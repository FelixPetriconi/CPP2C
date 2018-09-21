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
  string headerString;
  string bodyString;
  string destructorString;

  llvm::raw_string_ostream HeaderOS;
  llvm::raw_string_ostream BodyOS;

  OutputStreams()
    : headerString("")
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
    bool isPointer = false;
    bool isVector = false;
  };

  CType determineCType(const QualType &qt)
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
      result.mappedType = "W" + enumType->getNameAsString();
    }
    else if (qt->isRecordType() || (qt->isReferenceType() || qt->isPointerType()) &&
      qt->getPointeeType()->isRecordType()) // class or struct
    {
      const CXXRecordDecl *crd = 
        ((qt->isReferenceType() || qt->isPointerType()) && qt->getPointeeType()->isRecordType()) 
          ? qt->getPointeeType()->getAsCXXRecordDecl() : qt->getAsCXXRecordDecl();

      string recordName = crd->getNameAsString();
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
        }
        else
        {
          const auto &baseType = asTypePtr->getAsCXXRecordDecl();
          valueTypeName = baseType->getName();
        }

        result.mappedType = "vector_" + createNewClassName(valueTypeName);
        result.isPointer = true;
        result.isVector = true;
      }
      else
      {
        result.mappedType = createNewClassName(recordName);
        result.isPointer = true;
      }
    }
    //else if ((qt->isReferenceType() || qt->isPointerType()) &&
    //         qt->getPointeeType()->isRecordType())
    //{
    //  result.isPointer = true; // to properly differentiate among cast types
    //  const CXXRecordDecl *crd = qt->getPointeeType()->getAsCXXRecordDecl();
    //  string recordName = crd->getNameAsString();

    //  if (std::find(ClassList.begin(), ClassList.end(), recordName) !=
    //      ClassList.end())
    //  {
    //    result.mappedType = "W" + recordName + "*";
    //    result.castType = recordName + "*";
    //  }
    //  else
    //  {
    //    result.mappedType = recordName + "*";
    //  }
    //}
    return result;
  }

  void run(const MatchFinder::MatchResult &Result) override
  {
    if (const CXXRecordDecl *crd = Result.Nodes.getNodeAs<CXXRecordDecl>("derivedClassDecl"))
    {
      auto bases = crd->bases();
      auto baseClass = *bases.begin();

      string className = baseClass.getType()->getAsCXXRecordDecl()->getNameAsString();
    }
    else if (const CXXMethodDecl *cmd = Result.Nodes.getNodeAs<CXXMethodDecl>("publicMethodDecl"))
    {
      string mappedFunctionName;
      string className = cmd->getParent()->getDeclName().getAsString();
      string mappedClassName = createNewClassName(className);

      std::stringstream functionBody;
      std::stringstream destructorBody;
      std::stringstream constructorBody;
      std::stringstream functionSignature;

      // ignore operator overloadings
      if (cmd->isOverloadedOperator())
        return;

      // constructor
      if (const CXXConstructorDecl *ccd = dyn_cast<CXXConstructorDecl>(cmd))
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
      else if (isa<CXXDestructorDecl>(cmd))
      {
        //mappedFunctionName = "_destroy";
        //returnType = "void";
        //functionBody << "  delete reinterpret_cast<" << className << "*>(self)";
      }
      else
      {
        mappedFunctionName = cmd->getNameAsString();
        mappedFunctionName[0] = tolower(mappedFunctionName[0]);

        const QualType qt = cmd->getReturnType();
        auto cType = determineCType(qt);

        if (cType.isPointer)
        {
          functionSignature <<
            "  const " << cType.mappedType << "* " << mappedFunctionName << ";\n";
        }
        else
        {
          functionSignature <<
            "  " << cType.mappedType << " " << mappedFunctionName << ";\n";
        }

        constructorBody << ",\n"
          "    &" << className << "::" << cmd->getNameAsString() << ", &" << mappedClassName << "::" << mappedFunctionName;

        if (cType.isPointer)
        {
          if (cType.mappedType == "const char*")
          {
            destructorBody << "  delete [] " << mappedFunctionName << ";\n";
          }
          else if (cType.isVector)
          {
            destructorBody << "  " << cType.mappedType << "_destroy(val->" << mappedFunctionName << ");\n";
          }
          else
          {
            destructorBody << "  delete " << mappedFunctionName << ";\n";
          }
        }
      }

      if (cmd->getNumParams() > 1)
      {
        OS.HeaderOS << "/* FIXME function with parameter */" << mappedFunctionName << "\n";
      }

      OS.HeaderOS << functionSignature.str();
      OS.destructorString += destructorBody.str();

      OS.BodyOS << constructorBody.str();
    }
  }

  /*string createMappedParameterInvocation(const CXXMethodDecl* cmd)
  {
    stringstream result;
    string separator = ", ";
    for (unsigned int i = 0; i < cmd->getNumParams(); i++)
    {
      const QualType qt = cmd->parameters()[i]->getType();
      auto cType = determineCType(qt);

      if (i != 0)
        result << separator;

      if (cType.castType.empty())
        result << cmd->parameters()[i]->getQualifiedNameAsString();
      else
      {
        if (!cType.isPointer)
          result << "*";
        result << "reinterpret_cast<" << cType.castType << ">("
          << cmd->parameters()[i]->getQualifiedNameAsString()
          << ")";
      }
    }
    return result.str();
  }*/

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

    for (const auto &className : ClassList)
    {
      auto newClassName = createNewClassName(className);
      OS.HeaderOS <<
        "struct __declspec(dllexport) " << newClassName << "\n"
        "{\n"
        "  static " << newClassName << "*(*constructor)(const void*);\n"
        "  static void(*destructor)(" << newClassName << "*);\n"
        "\n";

        OS.BodyOS <<
          newClassName << "*(*" << newClassName << "::constructor)(const void*) = &" << newClassName << "_create;\n"
          "void(*" << newClassName << "::destructor)(" << newClassName << "*) = &" << newClassName << "_destroy;\n"
          "\n" <<
          "DEFINE_VECTOR(" << newClassName << ")\n"
          "\n" <<
          newClassName << "* " << newClassName << "_create(const void* origin)\n"
          "{\n"
          "  return WSCR::createWrappedObject<" << className << ", " << newClassName << ">(origin";


      //if (className.find("vector") != std::string::npos)
      //{
      //  auto openBrace = className.find("<");
      //  auto closeBrace = className.find(">");
      //  auto templateParam = className.substr(openBrace + 1, closeBrace - openBrace - 1);
      //  string vectorName = "vectorW" + templateParam;
      //  OS.HeaderOS << "struct __declspec(dllexport) " << vectorName <<
      //    "{\n" <<
      //    "  W" << templateParam << "* values;\n" <<
      //    "  unsigned int size;\n" <<
      //    "};\n\n" <<
      //    "__declspec(dllexport) " << vectorName << "* " << vectorName << "_create(); \n" <<
      //    "__declspec(dllexport) void " << vectorName << "_destroy(" << vectorName << "*val);\n\n";

      //  OS.BodyOS << vectorName << "* " << vectorName << "_create()\n" <<
      //    "{\n" <<
      //    "  " << vectorName << "* result = new " << vectorName << "();\n"
      //    "  result->values = nullptr;\n" <<
      //    "  result->size = 0;\n" <<
      //    "  return result; \n" <<
      //    "}\n\n" <<
      //    "void " << vectorName << "_destroy(" << vectorName << "* val)" <<
      //    "{\n" <<
      //    "  if (val) delete [] val->values;\n" << 
      //    "  delete val;\n" <<
      //    "}\n\n";
      //}
      //else if (className == "IPoint2D")
      //{
      //  OS.HeaderOS << "struct __declspec(dllexport) WIPoint2D" << 
      //    "{\n" <<
      //    "  int X;\n" <<
      //    "  int Y;\n" <<
      //    "};\n\n" <<
      //    "__declspec(dllexport) WIPoint2D* WIPoint2D_create();\n" <<
      //    "__declspec(dllexport) void WIPoint2D_destroy(WIPoint2D* val);\n\n";

      //  OS.BodyOS << "WIPoint2D * WIPoint2D_create()\n" <<
      //    "{\n" <<
      //    "  return new WIPoint2D();\n"
      //    "}\n\n" <<
      //    "void WIPoint2D_destroy(WIPoint2D* val)\n" <<
      //    "{\n" <<
      //    "  delete val;\n" <<
      //    "}\n\n";

      DeclarationMatcher classMatcher =
        cxxMethodDecl(isPublic(), ofClass(hasName(className)))
        .bind("publicMethodDecl");

      DeclarationMatcher derivedClassMatcher =
        cxxRecordDecl(isDerivedFrom(hasName("IFinding")/*anything()*/)).bind("derivedClassDecl");

      Matcher.addMatcher(classMatcher, &HandlerForClassMatcher);
      Matcher.addMatcher(derivedClassMatcher, &HandlerForClassMatcher);
    }
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
    OS.HeaderOS <<
      "///////////////////////////////////////////////////////////////////\n"
      "// Copyright 2018 MeVis Medical Solutions AG  all rights reserved\n"
      "///////////////////////////////////////////////////////////////////\n"
      "#ifndef _" << toUpper(_className) << "_\n"
      "#define _" << toUpper(_className) << "_\n"
      "\n"
      "/* FIXME Includes are missing */\n"
      "#include \"MacroHelper.h\"\n"
      "\n"
      "#ifdef __cplusplus\n"
      "extern \"C\"{\n"
      "#endif\n"
      "\n";

    OS.BodyOS <<
      "///////////////////////////////////////////////////////////////////\n"
      "// Copyright 2018 MeVis Medical Solutions AG  all rights reserved\n"
      "///////////////////////////////////////////////////////////////////\n"
      "\n"
      "#include \"" << _headerFileName << "\"\n"
      "\n"
      "#include <R2MgCadSr/" << _originalIncludeFileName << ">\n"
      "#include \"TemplateHelper.h\"\n"
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
      "};\n"
      "\n"
      "" << 
      "__declspec(dllexport) " << _className << "* " << _className << "_create(const void* origin);\n"
      "__declspec(dllexport) void " << _className << "_destroy(" << _className << "* va);\n"
      "\n"
      "DECLARE_VECTOR(" << _className << ")\n"
      "\n"
      "#ifdef __cplusplus\n"
      "}\n"
      "#endif\n"
      "\n"
      "#endif /* _" << toUpper(_className) << "_ */\n";

    OS.BodyOS <<
      ");\n"
      "}\n"
      "\n"
      "void " << _className << "_destroy(" << _className << "* val)\n" <<
      "{\n" << 
      OS.destructorString <<
      "  delete val;\n"
      "}\n";

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
