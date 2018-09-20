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

#include "clang/Driver/Options.h"
#include <map>
#include <set>
#include <sstream>
#include <tuple>
#include <vector>
#include "clang/Frontend/CompilerInstance.h"

using namespace std;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace clang::ast_matchers;
using namespace llvm;

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
  "ICalcification"
};

map<string, int> funcList;

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
    string castType; // whether this should be casted or not
    bool isPointer = false;
    bool shouldReturn = true;
    bool additionalParameter = false;
  };

  CType determineCType(const QualType &qt)
  {
    // How to get fuul name with namespace 
    // QualType::getAsString(cl->getASTContext().getTypeDeclType(const_cast<CXXRecordDecl*>(cl)).split())
    CType result;
    // if it is build-in type use it as is
    if (qt->isBuiltinType() ||
        (qt->isPointerType() && qt->getPointeeType()->isBuiltinType()))
    {
      result.mappedType = qt.getAsString();
      if (qt->isVoidType())
        result.shouldReturn = false;
      // if it is a CXXrecordDecl then return a pointer to WName*
    }
    else if (qt->isEnumeralType())
    {
      auto enumType = qt->getAs<EnumType>()->getDecl();
      result.mappedType = enumType->getNameAsString();
    }
    else if (qt->isRecordType()) // class or struct
    {
      const CXXRecordDecl *crd = qt->getAsCXXRecordDecl();
      string recordName = crd->getNameAsString();
      if (recordName == "basic_string")
      {
        result.mappedType = "const char*";
        result.castType = result.mappedType;
        result.isPointer = true;
      }
      else if (recordName == "vector")
      {
        result.mappedType = "vectorWIPoint2D";
        result.castType = result.mappedType;
        result.isPointer = true;
        result.additionalParameter = true;
        /*
        auto tcrd = dyn_cast<ClassTemplateSpecializationDecl>(crd);
        const auto &templateArgument = tcrd->getTemplateArgs().asArray()[0];
        const auto &baseType = templateArgument.getAsType().getTypePtr()->getAsCXXRecordDecl();
        const auto &name = baseType->getName();
        */
      }
      else if (recordName == "Point2D")
      {
        result.mappedType = "WIPoint2D";
        result.isPointer = true;
        result.castType = result.mappedType;
      }
      else
      {
        result.mappedType = "W" + recordName + "*";
        result.castType = recordName + "*";
        result.additionalParameter = true;
      }
    }
    else if ((qt->isReferenceType() || qt->isPointerType()) &&
             qt->getPointeeType()->isRecordType())
    {
      result.isPointer = true; // to properly differentiate among cast types
      const CXXRecordDecl *crd = qt->getPointeeType()->getAsCXXRecordDecl();
      string recordName = crd->getNameAsString();

      if (std::find(ClassList.begin(), ClassList.end(), recordName) !=
          ClassList.end())
      {
        result.mappedType = "W" + recordName + "*";
        result.castType = recordName + "*";
      }
      else
      {
        result.mappedType = recordName + "*";
      }
    }
    return result;
  }

  void run(const MatchFinder::MatchResult &Result) override
  {
    if (const CXXMethodDecl *cmd = Result.Nodes.getNodeAs<CXXMethodDecl>("publicMethodDecl"))
    {
      string mappedFunctionName;
      string className = cmd->getParent()->getDeclName().getAsString();
      string returnType;
      string returnCast;
      string self = "W" + className + "* self";
      string separator = ", ";
      string bodyEnd;
      string additionalParameter;

      std::stringstream functionBody;

      // ignore operator overloadings
      if (cmd->isOverloadedOperator())
        return;

      // constructor
      if (const CXXConstructorDecl *ccd = dyn_cast<CXXConstructorDecl>(cmd))
      {
        if (ccd->isCopyConstructor() || ccd->isMoveConstructor())
          return;
        mappedFunctionName = "_create";
        returnType = "W" + className + "*";
        self = "";
        separator = "";
        functionBody << "  return reinterpret_cast<" << returnType << ">( new " << className << "(";
        bodyEnd += "))";
      }
      else if (isa<CXXDestructorDecl>(cmd))
      {
        mappedFunctionName = "_destroy";
        returnType = "void";
        functionBody << "  delete reinterpret_cast<" << className << "*>(self)";
      }
      else
      {
        mappedFunctionName = "_" + cmd->getNameAsString();
        const QualType qt = cmd->getReturnType();
        
        auto cType = determineCType(qt);
        returnType = cType.mappedType;

        if (cType.mappedType.find("vector") != std::string::npos)
        {
          returnType = returnType +"*";
          additionalParameter = cType.castType;
          functionBody << "  const auto& elements = reinterpret_cast<" << className << "*>(self)->" << cmd->getNameAsString() << "(" << createMappedParameterInvocation(cmd) << ");\n";
          functionBody << "  result->values = new WIPoint2D[elements.size()];\n";
          functionBody << "  result->size = static_cast<unsigned int>(elements.size());\n";
          functionBody << "  std::transform(elements.cbegin(), elements.cend(), result->values, [](const IPoint2D& p) { return WIPoint2D{p.X, p.Y};};\n";
          functionBody << "  return result";
        }
        else
        {
          // should this function return?
          if (cType.shouldReturn)
            functionBody << "  return ";

          if (!cType.castType.empty())
          {
            // if not pointer and it needs to be casted, then return the pointer
            if (!cType.isPointer)
              functionBody << "&";

            functionBody << "reinterpret_cast<" << cType.mappedType << ">(";
            bodyEnd += ")";
          }

          // if Static call it properly
          if (cmd->isStatic())
            functionBody << className << "::" << cmd->getNameAsString() << "(";
          // if not  use the passed object to call the method
          else
            functionBody << "reinterpret_cast<" << className << "*>(self)->"
            << cmd->getNameAsString() << "(";

          bodyEnd += ")";
        }
      }

      std::stringstream functionSignature;
      functionSignature << returnType << " " << className << mappedFunctionName;

      auto it = funcList.find(functionSignature.str());

      if (it != funcList.end())
      {
        it->second++;
        functionSignature << "_" << it->second;
      }
      else
      {
        funcList[functionSignature.str()] = 0;
      }

     
      functionSignature << "(" << self;

      for (unsigned int i = 0; i < cmd->getNumParams(); i++)
      {
        const QualType qt = cmd->parameters()[i]->getType();
        auto cType = //std::tie(returnType, returnCast, isPointer, shouldReturn) =
          determineCType(qt);
        functionSignature << separator << cType.mappedType << " ";
        functionSignature << cmd->parameters()[i]->getQualifiedNameAsString() << "";

        separator = ", ";
      }
      if (!additionalParameter.empty())
        functionSignature << separator << additionalParameter << "* result";

      functionSignature << ")";

      string parameterInvocation = createMappedParameterInvocation(cmd);
      functionBody << parameterInvocation;

      OS.HeaderOS << "__declspec(dllexport) " << functionSignature.str() << ";\n\n";

      OS.BodyOS << functionSignature.str() << "{\n";
      OS.BodyOS << functionBody.str();
      OS.BodyOS << bodyEnd << "; \n}\n\n";
    }
  }

  string createMappedParameterInvocation(const CXXMethodDecl* cmd)
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

    for (const string &className : ClassList)
    {
      if (className.find("vector") != std::string::npos)
      {
        auto openBrace = className.find("<");
        auto closeBrace = className.find(">");
        auto templateParam = className.substr(openBrace + 1, closeBrace - openBrace - 1);
        string vectorName = "vectorW" + templateParam;
        OS.HeaderOS << "struct __declspec(dllexport) " << vectorName <<
          "{\n" <<
          "  W" << templateParam << "* values;\n" <<
          "  unsigned int size;\n" <<
          "};\n\n" <<
          "__declspec(dllexport) " << vectorName << "* " << vectorName << "_create(); \n" <<
          "__declspec(dllexport) void " << vectorName << "_destroy(" << vectorName << "*val);\n\n";

        OS.BodyOS << vectorName << "* " << vectorName << "_create()\n" <<
          "{\n" <<
          "  " << vectorName << "* result = new " << vectorName << "();\n"
          "  result->values = nullptr;\n" <<
          "  result->size = 0;\n" <<
          "  return result; \n" <<
          "}\n\n" <<
          "void " << vectorName << "_destroy(" << vectorName << "* val)" <<
          "{\n" <<
          "  if (val) delete [] val->values;\n" << 
          "  delete val;\n" <<
          "}\n\n";
      }
      else if (className == "IPoint2D")
      {
        OS.HeaderOS << "struct __declspec(dllexport) WIPoint2D" << 
          "{\n" <<
          "  int X;\n" <<
          "  int Y;\n" <<
          "};\n\n" <<
          "__declspec(dllexport) WIPoint2D* WIPoint2D_create();\n" <<
          "__declspec(dllexport) void WIPoint2D_destroy(WIPoint2D* val);\n\n";

        OS.BodyOS << "WIPoint2D * WIPoint2D_create()\n" <<
          "{\n" <<
          "  return new WIPoint2D();\n"
          "}\n\n" <<
          "void WIPoint2D_destroy(WIPoint2D* val)\n" <<
          "{\n" <<
          "  delete val;\n" <<
          "}\n\n";
      }
      else
      {
        OS.HeaderOS << "struct __declspec(dllexport) W" << className << ";\n";
      }

      DeclarationMatcher classMatcher =
        cxxMethodDecl(isPublic(), ofClass(hasName(className)))
        .bind("publicMethodDecl");
      Matcher.addMatcher(classMatcher, &HandlerForClassMatcher);
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

// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction
{
public:
  MyFrontendAction()
  {
    OS.HeaderOS << "#ifndef _WBREASTGEOMETRY_H_\n"
      "#define _WBREASTGEOMETRY_H_\n"
      "#include <stdbool.h>\n"
      "#include <Windows.h>\n"
      "#ifdef __cplusplus\n"
      "extern \"C\"{\n"
      "#endif\n"
      "\n"
      "__declspec(dllexport) BOOL WINAPI DllMain(HINSTANCE hinstDLL, DWORD fdwReason, LPVOID lpvReserved);\n"
      "\n";

    OS.BodyOS << "#include \"WBreastGeometryAlgo.h\"\n"
      "#include \"BreastGeometryAlgo.h\"\n"
      "#ifdef __cplusplus\n"
      "extern \"C\"{\n"
      "#endif\n"
      "\n"
      "BOOL WINAPI DllMain(HINSTANCE/*hinstDLL*/, DWORD fdwReason, LPVOID/*lpvReserved*/)\n"
      "{\n"
      "  if (fdwReason == DLL_PROCESS_ATTACH)\n"
      "  {\n"
      "  }\n"
      "  else if (fdwReason == DLL_PROCESS_DETACH) \n"
      "  {\n"
      "  }\n"
      "  return TRUE;\n"
      "}\n\n";
  }

  bool BeginSourceFileAction(CompilerInstance &CI) override
  {
    _headerFileName = "WBreastGeometryAlgo.h";
    _bodyFileName = "WBreastGeometryAlgo.cpp";
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

    OS.HeaderOS << "#ifdef __cplusplus\n"
      "}\n"
      "#endif\n"
      "#endif /* _WBREASTGEOMETRY_H_ */\n";

    OS.BodyOS << "#ifdef __cplusplus\n"
      "}\n"
      "#endif\n";

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
  string _headerFileName;
  string _bodyFileName;
};

int main(int argc, const char **argv)
{
  // parse the command-line args passed to your code
  CommonOptionsParser op(argc, argv, CPP2CCategory);
  // create a new Clang Tool instance (a LibTooling environment)
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  // run the Clang Tool, creating a new FrontendAction
  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}
