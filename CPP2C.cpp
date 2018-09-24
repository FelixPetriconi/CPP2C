#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Execution.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Tooling/Refactoring/AtomicChange.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Signals.h"
#include "clang/Frontend/CompilerInstance.h"

#include "clang/Driver/Options.h"
#include <algorithm>
#include <map>
#include <set>
#include <sstream>
#include <vector>
#include <locale>


using namespace std;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace clang::ast_matchers;
using namespace llvm;


string toUpper(string strToConvert)
{
  std::transform(strToConvert.begin(), strToConvert.end(), strToConvert.begin(), ::toupper);
  return strToConvert;
}

template<class Container, class SourceContainer>
bool appendUniqueValues(Container& c, const SourceContainer& newValues)
{
  auto result = false;
  for (const auto& v : newValues)
  {
    result = appendUnique(c, v) || result;
  }
  return result;
}

template<class Container, typename T>
bool appendUnique(Container& c, const T& v)
{
  if (std::find(std::begin(c), std::end(c), v) == std::end(c))
  {
    c.push_back(v);
    return true;
  }
  return false;
}

/**
 * Appends element to the specified container if it not already available which is
 * checked by a predicate
 * @param c that supports a range specified by the begin() and end() ForwardIterators
 * @param value that will be append to the container
 * @param p UnaryPredicate that is used for equality check
 * @return true if it was appended, otherwise false
 */
template<class Container, typename T, class Predicate>
bool appendUnique(Container& c, T value, Predicate p)
{
  if (std::find_if(std::begin(c), std::end(c), p) == std::end(c))
  {
    c.push_back(std::move(value));
    return true;
  }
  return false;
}

string createNewClassName(string oldName)
{
  if (oldName[0] == 'I')
    oldName = oldName.substr(1);

  return "W" + oldName;
}

string currentFile;

/** Options **/
static cl::OptionCategory CPP2CCategory("CPP2C options");
static std::unique_ptr<opt::OptTable> Options(createDriverOptTable());
static cl::opt<std::string>
OutputFilename("o", cl::desc(Options->getOptionHelpText((options::OPT_o))));

/** Classes to be mapped to C **/
struct OutputStreams
{
  const string currentSourceFile;
  string headerFileBeforeIncludes;
  string headerFileAfterIncludes;
  string headerString;
  string bodyString;
  string destructorString;
  std::vector<string> includeFiles;

  llvm::raw_string_ostream HeaderOS;
  llvm::raw_string_ostream BodyOS;

  OutputStreams(string currentSourceFile)
    : currentSourceFile(std::move(currentSourceFile))
    , headerString("")
    , bodyString("")
    , HeaderOS(headerString)
    , BodyOS(bodyString)
  {
  };
};

vector<string> ClassList = {
  //"IAnalysesPerformed"
};

/** Matchers **/

/** Handlers **/
class classMatchHandler : public MatchFinder::MatchCallback
{
public:
  classMatchHandler(OutputStreams &os)
    : OS(os)
  {
  }

  struct CType
  {
    string mappedType;
    string declarationSourceFile;
    bool isPointer = false;
    bool isVector = false;
  };

  string stripPathFromFileName(string fileName) const
  {
    auto pos = fileName.find_last_of("\\/");
    if (pos != string::npos)
    {
      fileName = fileName.substr(pos+1, fileName.size() - pos - 1);
    }
    return fileName;
  }

  CType determineCType(const SourceManager& sourceManager, const QualType &qt)
  {
    // How to get full name with namespace 
    // QualType::getAsString(cl->getASTContext().getTypeDeclType(const_cast<CXXRecordDecl*>(cl)).split())
    CType result;
    // if it is build-in type use it as is
    if (qt->isBuiltinType() ||
        (qt->isPointerType() && qt->getPointeeType()->isBuiltinType()))
    {
      result.mappedType = qt.getAsString();
      //if (qt->isVoidType())
      //  result.shouldReturn = false;
      // if it is a CXXrecordDecl then return a pointer to WName*
    }
    else if (qt->isEnumeralType())
    {
      auto enumType = qt->getAs<EnumType>()->getDecl();
      result.declarationSourceFile = sourceManager.getFilename(enumType->getLocation()).str();
      result.mappedType = "W" + enumType->getNameAsString();
    }
    else if (qt->isRecordType() || (qt->isReferenceType() || qt->isPointerType()) &&
      qt->getPointeeType()->isRecordType()) // class or struct
    {
      const CXXRecordDecl *crd = 
        ((qt->isReferenceType() || qt->isPointerType()) && qt->getPointeeType()->isRecordType()) 
          ? qt->getPointeeType()->getAsCXXRecordDecl() : qt->getAsCXXRecordDecl();

      string recordName = crd->getNameAsString();
      result.declarationSourceFile = sourceManager.getFilename(crd->getLocation()).str();
      if (recordName == "basic_string")
      {
        result.mappedType = "char";
        result.isPointer = true;
      }
      else if (recordName == "vector")
      {
        string valueTypeName;
        auto tcrd = dyn_cast<ClassTemplateSpecializationDecl>(crd);
        const auto &templateArgument = tcrd->getTemplateArgs().asArray()[0];
        const auto &asType = templateArgument.getAsType();
        const auto &asTypePtr = asType.getTypePtr();
        if (asTypePtr->isPointerType())
        {
          const auto &baseType = asTypePtr->getPointeeType()->getAsCXXRecordDecl();
          valueTypeName = baseType->getName();
          result.declarationSourceFile = sourceManager.getFilename(baseType->getLocation()).str();
        }
        else
        {
          const auto &baseType = asTypePtr->getAsCXXRecordDecl();
          valueTypeName = baseType->getName();
          result.declarationSourceFile = sourceManager.getFilename(baseType->getLocation()).str();
        }

        result.mappedType = "vector_" + createNewClassName(valueTypeName);
        result.isPointer = true;
        result.isVector = true;
      }
      else
      {
        result.mappedType = createNewClassName(recordName);
        result.declarationSourceFile = sourceManager.getFilename(crd->getLocation()).str();
        result.isPointer = true;
      }
    }
    return result;
  }

  void run(const MatchFinder::MatchResult &Result) override
  {
    static bool passed = false;
    if (passed)
      return;

    const SourceManager &sourceManager = Result.Context->getSourceManager();

    if (const CXXRecordDecl *crd = Result.Nodes.getNodeAs<CXXRecordDecl>("classDecl"))
    {
      std::stringstream functionBody;
      std::stringstream destructorBody;
      std::stringstream constructorBody;
      std::stringstream functionSignature;

      const auto originalClassName = crd->getNameAsString();
      const auto newClassName = createNewClassName(originalClassName);
      
      stringstream headerPart;
      headerPart <<
        "struct __declspec(dllexport) " << newClassName << "\n"
        "{\n"
        "  static " << newClassName << "*(*constructor)(const void*);\n"
        "  static void(*destructor)(" << newClassName << "*);\n"
        "\n";

      if (crd->getNumBases() != 0)
      {
        auto bases = crd->bases();
        auto baseClass = *bases.begin();

        const auto originalBaseClassName = baseClass.getType()->getAsCXXRecordDecl()->getNameAsString();
        const auto newBaseClassName = createNewClassName(originalBaseClassName);

        headerPart <<
          "  " << newBaseClassName << "* base;\n";

        constructorBody <<
          "  const auto originalBase = reinterpret_cast<const " << originalClassName << "*>(origin);\n"
          "  result->base = " << newBaseClassName << "_create(dynamic_cast<const " << originalBaseClassName << "*>(originalBase));\n";

        destructorBody << "  " << newBaseClassName << "_destroy(val->base);\n";
      }

      OS.BodyOS <<
        newClassName << "*(*" << newClassName << "::constructor)(const void*) = &" << newClassName << "_create;\n"
        "void(*" << newClassName << "::destructor)(" << newClassName << "*) = &" << newClassName << "_destroy;\n"
        "\n" <<
        "DEFINE_VECTOR(" << newClassName << ")\n"
        "\n" <<
        newClassName << "* " << newClassName << "_create(const void* origin)\n"
        "{\n"
        "  auto result = WSCR::createWrappedObject<" << originalClassName << ", " << newClassName << ">(origin";

      // Loop over public functions
      for (const auto& method : crd->methods())
      {
        if (!method->isExternallyVisible())
          continue;

        string mappedFunctionName;

        // ignore operator overloadings
        if (method->isOverloadedOperator())
          continue;

        // constructor
        if (const CXXConstructorDecl *ccd = dyn_cast<CXXConstructorDecl>(method))
        {
          //if (ccd->isCopyConstructor() || ccd->isMoveConstructor())
          //  return;
          //mappedFunctionName = "_create";
          //returnType = "W" + className + "*";
          //self = "";
          //separator = "";
          //functionBody << "  return reinterpret_cast<" << returnType << ">( new " << className << "(";
          //bodyEnd += "))";
        }
        else if (isa<CXXDestructorDecl>(method))
        {
          //mappedFunctionName = "_destroy";
          //returnType = "void";
          //functionBody << "  delete reinterpret_cast<" << className << "*>(self)";
        }
        else
        {
          mappedFunctionName = method->getNameAsString();
          mappedFunctionName[0] = tolower(mappedFunctionName[0]);

          const QualType qt = method->getReturnType();
          auto cType = determineCType(sourceManager, qt);

          cType.declarationSourceFile = stripPathFromFileName(cType.declarationSourceFile);

          if (!cType.declarationSourceFile.empty() && cType.declarationSourceFile != OS.currentSourceFile)
          {
            if (cType.declarationSourceFile[0] == 'I')
            {
              cType.declarationSourceFile = cType.declarationSourceFile.substr(1, cType.declarationSourceFile.size() - 1);
            }
            appendUnique(OS.includeFiles, "W" + cType.declarationSourceFile);
          }

          if (cType.isPointer)
          {
            headerPart <<
              "  const " << cType.mappedType << "* " << mappedFunctionName << ";\n";
          }
          else
          {
            headerPart <<
              "  " << cType.mappedType << " " << mappedFunctionName << ";\n";
          }

          OS.BodyOS << ",\n"
            "    &" << originalClassName << "::" << method->getNameAsString() << ", &" << newClassName << "::" << mappedFunctionName;

          if (cType.isPointer)
          {
            if (cType.mappedType == "char")
            {
              destructorBody << "  delete [] val->" << mappedFunctionName << ";\n";
            }
            else
            {
              destructorBody << "  " << cType.mappedType << "_destroy(val->" << mappedFunctionName << ");\n";
            }
          }
        }

        if (method->getNumParams() > 1)
        {
          mappedFunctionName = method->getNameAsString();
          headerPart << "/* FIXME function with parameter " << mappedFunctionName << " */\n";
        }
      }

      headerPart <<
        "};\n"
        "\n"
        "" <<
        "__declspec(dllexport) " << newClassName << "* " << newClassName << "_create(const void* origin);\n"
        "__declspec(dllexport) void " << newClassName << "_destroy(" << newClassName << "* val);\n"
        "\n"
        "DECLARE_VECTOR(" << newClassName << ")\n";

      headerPart.flush();

      OS.headerFileAfterIncludes += headerPart.str();

      OS.BodyOS <<
        ");\n" <<
        constructorBody.str() << 
        "  return result;\n"
        "}\n"
        "\n"
        "void " << newClassName << "_destroy(" << newClassName << "* val)\n" <<
        "{\n" <<
        destructorBody.str() <<
        "  delete val;\n"
        "}\n";
      passed = true;
    }
  }

  virtual void onEndOfTranslationUnit()
  {
  }

private:
  OutputStreams &OS;
};


/****************** /Member Functions *******************************/
// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser. It registers a couple of matchers and runs them on
// the AST.
class MyASTConsumer : public ASTConsumer
{
public:
  MyASTConsumer(OutputStreams &os)
    : OS(os)
    , HandlerForClassMatcher(os)
  {
    // Add a simple matcher for finding 'if' statements.


    DeclarationMatcher classMatcher =
      cxxRecordDecl(hasName(ClassList[0])).bind("classDecl");


    Matcher.addMatcher(classMatcher, &HandlerForClassMatcher);
  }

  void HandleTranslationUnit(ASTContext &Context) override
  {
    // Run the matchers when we have the whole TU parsed.
    Matcher.matchAST(Context);
  }

private:
  OutputStreams &OS;
  classMatchHandler HandlerForClassMatcher;

  MatchFinder Matcher;
};

string guessOriginalClassNameFromFileName(string name)
{
  // strip off the tailing hpp
  auto dotIndex = name.find(".");
  if (dotIndex != string::npos)
    name = name.substr(0, dotIndex);

  return name;
}


// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction
{
public:
  MyFrontendAction()
    : OS(currentFile)
  {
    _originalIncludeFileName = currentFile;

    currentFile = guessOriginalClassNameFromFileName(currentFile);
    // strip off the leading I
    if (currentFile[0] == 'I')
      currentFile = currentFile.substr(1, currentFile.size() - 1);


    _className = "W" + currentFile;
    _headerFileName = _className + ".h";
    _bodyFileName = _className + ".cpp";
  }


  bool BeginSourceFileAction(CompilerInstance &CI) override
  {
    stringstream beforeIncludes;
    beforeIncludes <<
      "///////////////////////////////////////////////////////////////////\n"
      "// Copyright 2018 MeVis Medical Solutions AG  all rights reserved\n"
      "///////////////////////////////////////////////////////////////////\n"
      "#ifndef _" << toUpper(_className) << "_\n"
      "#define _" << toUpper(_className) << "_\n"
      "\n";
    beforeIncludes.flush();

    OS.headerFileBeforeIncludes = beforeIncludes.str();

    stringstream afterIncludes;
    afterIncludes <<
      "#include \"MacroHelper.h\"\n"
      "\n"
      "#ifdef __cplusplus\n"
      "extern \"C\"{\n"
      "#endif\n"
      "\n";
    afterIncludes.flush();
    OS.headerFileAfterIncludes = afterIncludes.str();

    OS.BodyOS <<
      "///////////////////////////////////////////////////////////////////\n"
      "// Copyright 2018 MeVis Medical Solutions AG  all rights reserved\n"
      "///////////////////////////////////////////////////////////////////\n"
      "\n"
      "#include \"" << _headerFileName << "\"\n"
      "#include \"TemplateHelper.h\"\n"
      "\n"
      "#include <R2MgCadSr/" << _originalIncludeFileName << ">\n"
      "\n"
      "using namespace R2::Citra::Mammo::Decoding;\n"
      "\n";

    return true;
  }

  void EndSourceFileAction() override
  {
    StringRef headerFile(_headerFileName);
    StringRef bodyFile(_bodyFileName);

    // Open the output file
    std::error_code EC;
    llvm::raw_fd_ostream HOS(headerFile, EC, llvm::sys::fs::F_None);
    if (EC)
    {
      llvm::errs() << "while opening '" << headerFile << "': " << EC.message()
        << '\n';
      exit(1);
    }
    llvm::raw_fd_ostream BOS(bodyFile, EC, llvm::sys::fs::F_None);
    if (EC)
    {
      llvm::errs() << "while opening '" << bodyFile << "': " << EC.message()
        << '\n';
      exit(1);
    }

    OS.HeaderOS <<
      OS.headerFileBeforeIncludes;

    for (const auto& fileName : OS.includeFiles)
    {
      OS.HeaderOS <<
        "#include \"" << fileName << "\"\n";
    }

    OS.HeaderOS <<
      OS.headerFileAfterIncludes <<
      "\n"
      "#ifdef __cplusplus\n"
      "}\n"
      "#endif\n"
      "\n"
      "#endif /* _" << toUpper(_className) << "_ */\n";

    //OS.BodyOS <<

    OS.HeaderOS.flush();
    OS.BodyOS.flush();
    HOS << OS.headerString << "\n";    
    BOS << OS.bodyString << "\n";
  }

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override
  {
    return llvm::make_unique<MyASTConsumer>(OS);
  }

private:
  OutputStreams OS;
  string _originalIncludeFileName;
  string _className;
  string _headerFileName;
  string _bodyFileName;
};

int main(int argc, const char **argv)
{
  // parse the command-line args passed to your code
  CommonOptionsParser op(argc, argv, CPP2CCategory);
  // create a new Clang Tool instance (a LibTooling environment)
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  auto sourcePathList = op.getSourcePathList();
  currentFile = sourcePathList[0];
  ClassList.push_back(guessOriginalClassNameFromFileName(sourcePathList[0]));

  // run the Clang Tool, creating a new FrontendAction
  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}
