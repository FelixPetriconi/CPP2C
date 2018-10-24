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
#include <variant>
#include <sstream>
#include <vector>
#include <locale>


using namespace std;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace clang::ast_matchers;
using namespace llvm;

namespace
{
  const string ClassPrefix = "W2D";
  const string R2NameSpace = "R2::Citra::Mammo::Decoding";
  const string ThirdpartyInclude = "R2MgCadSr";

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

    if (oldName.find(ClassPrefix) == string::npos)
      return ClassPrefix + oldName;
    
    return oldName;
  }

  template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
  template<class... Ts> overloaded(Ts...)->overloaded<Ts...>;

  struct ContentPrinter
  {
    llvm::raw_string_ostream& _stream;
    ContentPrinter(llvm::raw_string_ostream& stream) : _stream(stream) {}

    void operator()(const string& s) { _stream << s << "\n"; }
    void operator()(const vector<string>& v) 
    {
      for (const auto& s : v)
        _stream << s << "\n";
    }
  };


  string stripPathFromFileName(string fileName)
  {
    auto pos = fileName.find_last_of("\\/");
    if (pos != string::npos)
    {
      fileName = fileName.substr(pos + 1, fileName.size() - pos - 1);
    }
    return fileName;
  }

  string guessOriginalClassNameFromFileName(string name)
  {
    // strip off the tailing hpp
    auto dotIndex = name.find(".");
    if (dotIndex != string::npos)
      name = name.substr(0, dotIndex);

    return stripPathFromFileName(name);
  }


  string currentFile;
  string originalSourceFile;

  /** Options **/
  cl::OptionCategory CPP2CCategory("CPP2C options");
  std::unique_ptr<opt::OptTable> Options(createDriverOptTable());
  cl::opt<std::string> OutputFilename("o", cl::desc(Options->getOptionHelpText((options::OPT_o))));

  enum class HeaderItems
  {
    CopyrightNotice,
    IncludeGuardTop,
    AdditionalIncludeFiles,
    CommonIncludeFiles,
    EnumDefinitions,
    StructBodyTop,
    Members,
    StructBodyBottom,
    ConstructorDeclaration,
    DestructorDeclaration,
    FreeFunctionDeclaration,
    AdditionalDeclarations,
    IncludeGuardBottom
  };

  enum class BodyItems
  {
    CopyrightNotice,
    StandardInclude,
    AdditionalIncludeFiles,
    CommonIncludeFiles,
    Usings,
    ConstructorDefinition,
    DestructorDefinition,
    MembersToCreate,
    MembersToDestruct,
    ConstructorImplementation,
    DestructorImplementation,
    FreeFunctionImplementation,
    AdditionalImplementations
  };

}
using Strings = vector<string>;

/** Classes to be mapped to C **/
struct OutputStreams
{
  map<HeaderItems, std::variant<string, Strings>> headerContent;
  map<BodyItems, variant<string, Strings>> bodyContent;

  const string currentSourceFile;
  string headerString;
  string bodyString;

  llvm::raw_string_ostream HeaderOS;
  llvm::raw_string_ostream BodyOS;

  OutputStreams(string currentSourceFile)
    : currentSourceFile(std::move(currentSourceFile))
    , headerString("")
    , bodyString("")
    , HeaderOS(headerString)
    , BodyOS(bodyString)
  {
    headerContent[HeaderItems::CopyrightNotice] = string{};
    headerContent[HeaderItems::IncludeGuardTop] = string{};
    headerContent[HeaderItems::AdditionalIncludeFiles] = vector<string>{};
    headerContent[HeaderItems::CommonIncludeFiles] = string{};
    headerContent[HeaderItems::EnumDefinitions] = vector<string>{};
    headerContent[HeaderItems::StructBodyTop] = string{};
    headerContent[HeaderItems::ConstructorDeclaration] = string{};
    headerContent[HeaderItems::DestructorDeclaration] = string{};
    headerContent[HeaderItems::Members] = vector<string>{};
    headerContent[HeaderItems::StructBodyBottom] = string{};
    headerContent[HeaderItems::FreeFunctionDeclaration] = vector<string>{};
    headerContent[HeaderItems::AdditionalDeclarations] = vector<string>{};
    headerContent[HeaderItems::IncludeGuardBottom] = string{};

    bodyContent[BodyItems::CopyrightNotice] = string{};
    bodyContent[BodyItems::StandardInclude] = string{};
    bodyContent[BodyItems::AdditionalIncludeFiles] = vector<string>{};
    bodyContent[BodyItems::CommonIncludeFiles] = vector<string>{};
    bodyContent[BodyItems::Usings] = vector<string>{};
    bodyContent[BodyItems::ConstructorDefinition] = string{};
    bodyContent[BodyItems::DestructorDefinition] = string{};
    bodyContent[BodyItems::MembersToCreate] = vector<string>{};
    bodyContent[BodyItems::MembersToDestruct] = vector<string>{};
    bodyContent[BodyItems::ConstructorImplementation] = string{};
    bodyContent[BodyItems::DestructorImplementation] = string{};
    bodyContent[BodyItems::FreeFunctionImplementation] = vector<string>{};
    bodyContent[BodyItems::AdditionalImplementations] = vector<string>{};
  }
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
    string originalType;
    string mappedType;
    string declarationSourceFile;
    string enumDefinition;
    bool static_cast_needed = false;
    bool isPointer = false;
    bool isVector = false;
    bool isVoid = false;
    bool isPOD = false;
    bool isLValueReference = false;
    bool explicitConstructionNecessary = false;
  };

  template <typename T>
  struct VisitValue
  {
    map<T, std::variant<string, Strings>>& _content;

    VisitValue(map<T, std::variant<string, Strings>>& content) : _content(content) {}

    void append(T key, string value)
    {
      if (_content[key].index() == 0)
        get<string>(_content[key]) = std::move(value);
      else
        get<Strings>(_content[key]).emplace_back(std::move(value));
    }
  };


  CType determineCType(const SourceManager& sourceManager, const QualType &qt)
  {
    // How to get full name with namespace 
    // QualType::getAsString(cl->getASTContext().getTypeDeclType(const_cast<CXXRecordDecl*>(cl)).split())
    CType result;
    // if it is build-in type use it as is
    if (qt->isBuiltinType() ||
        (qt->isPointerType() && qt->getPointeeType()->isBuiltinType()))
    {
      if (qt->isVoidType())
      {
        result.isVoid = true;
      }
      else
      {
        if (qt->isBooleanType())
        {
          result.mappedType = "int";
          result.originalType = "bool";
        }
        else
        {
          result.mappedType = qt.getAsString();
          result.originalType = qt.getAsString();
        }
      }

      result.isPOD = true;
    }
    else if (qt->isLValueReferenceType() && qt->getPointeeType()->isBuiltinType())
    {
      result.mappedType = qt.getAsString();
      result.originalType = qt.getAsString();
      result.isLValueReference = true;
      result.isPOD = true;
    }
    else if (qt->isEnumeralType())
    {
      auto enumType = qt->getAs<EnumType>()->getDecl();
      result.originalType = enumType->getNameAsString();
      result.declarationSourceFile = sourceManager.getFilename(enumType->getLocation()).str();
      result.mappedType = ClassPrefix + enumType->getNameAsString();
      result.static_cast_needed = true;

      if (stripPathFromFileName(result.declarationSourceFile) == originalSourceFile)
      {
        stringstream enumDefinition;
        enumDefinition <<
          "enum " << result.mappedType << "\n"
          "{ \n";

        std::vector<string> enumerations;
        std::transform(enumType->enumerator_begin(), enumType->enumerator_end(), back_inserter(enumerations), [](const auto& enumItem)
        {
          return string("  ") + enumItem->getNameAsString() + " = " + to_string(enumItem->getInitVal().getExtValue());
        });

        enumDefinition <<
          ::join(enumerations, ", \n") << "\n" <<
          "};\n";

        enumDefinition.flush();

        result.enumDefinition = enumDefinition.str();
      }
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
        result.originalType = "std::string";
        result.explicitConstructionNecessary = true;
        result.declarationSourceFile.clear();
      }
      else if (recordName == "vector")
      {
        string valueTypeName;
        auto tcrd = dyn_cast<ClassTemplateSpecializationDecl>(crd);
        const auto &templateArgument = tcrd->getTemplateArgs().asArray()[0];
        const auto &asType = templateArgument.getAsType();

        auto cType = determineCType(sourceManager, asType);

        if (cType.originalType == "std::string")
        {
          valueTypeName = "string";
          result.declarationSourceFile = "StringHelper.h";
        }
        else if (cType.originalType == "Point2D<int>" || cType.originalType == "Point2D<float>")
        {
          valueTypeName = cType.mappedType;
          result.declarationSourceFile = cType.declarationSourceFile;
        }
        else
        {
          valueTypeName = cType.mappedType;
          result.declarationSourceFile = cType.declarationSourceFile;
        }

        result.mappedType = "vector_" + createNewClassName(valueTypeName);
        result.isPointer = true;
        result.isVector = true;
        result.explicitConstructionNecessary = true;
      }
      else if (recordName == "Point2D")
      {
        auto tcrd = dyn_cast<ClassTemplateSpecializationDecl>(crd);
        const auto &templateArgument = tcrd->getTemplateArgs().asArray()[0];
        const auto &asType = templateArgument.getAsType();
        auto valueTypeName = asType.getAsString();;

        if (valueTypeName == "int")
        {
          result.mappedType = ClassPrefix + "Point2DInt";
          result.originalType = "Point2D<int>";
        }
        else
        {
          result.mappedType = ClassPrefix + "Point2DFloat";
          result.originalType = "Point2D<float>";
        }
        result.declarationSourceFile = "Point2D.h";
        result.explicitConstructionNecessary = true;
        result.isPointer = true;
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

  string generateMappedInclude(string originalInclude)
  {
    originalInclude = stripPathFromFileName(originalInclude);

    if (!originalInclude.empty() && originalInclude != OS.currentSourceFile)
    {
      if (originalInclude[0] == 'I')
      {
        originalInclude = originalInclude.substr(1, originalInclude.size() - 1);
      }
    }
    else
    {
      originalInclude.clear();
    }
    return originalInclude;
  }


  void run(const MatchFinder::MatchResult &Result) override
  {
    static bool passed = false;
    if (passed)
      return;

    const SourceManager &sourceManager = Result.Context->getSourceManager();

    if (const CXXRecordDecl *crd = Result.Nodes.getNodeAs<CXXRecordDecl>("classDecl"))
    {
      std::stringstream functionHeader;
      std::stringstream functionBody;
      vector<string> parameters;
      vector<string> parametersCall;
      std::stringstream destructorBody;
      std::stringstream constructorBody;
      std::stringstream constructorInitBody;
      std::stringstream functionSignature;

      const auto originalClassName = crd->getNameAsString();
      const auto newClassName = createNewClassName(originalClassName);

      stringstream freeFunctionsDeclarationPart;
      stringstream freeFunctionsImplementtaionPart;
      stringstream declarationPart;

      VisitValue{OS.headerContent}.append(HeaderItems::StructBodyTop,
        "struct __declspec(dllexport) " + newClassName + "\n"
        "{\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::StructBodyBottom,
        "};\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::Members,
        "  static " + newClassName + "*(*constructor)(const void*);\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::Members,
        "  static void(*destructor)(" + newClassName + "*);\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::Members,
        "  const void* origin;\n");


      VisitValue{ OS.headerContent }.append(HeaderItems::ConstructorDeclaration,
        "__declspec(dllexport) " + newClassName + "* " + newClassName + "_create(const void* origin);\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::DestructorDeclaration,
        "__declspec(dllexport) void " + newClassName + "_destroy(" + newClassName + "* val);\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::AdditionalDeclarations,
        "DECLARE_VECTOR(" + newClassName + ")\n");

      VisitValue{ OS.bodyContent }.append(BodyItems::ConstructorDefinition,
        newClassName + "*(*" + newClassName + "::constructor)(const void*) = &" + newClassName + "_create;\n");

      VisitValue{ OS.bodyContent }.append(BodyItems::DestructorDefinition,
        "void(*" + newClassName + "::destructor)(" + newClassName + "*) = &" + newClassName + "_destroy;\n");

      VisitValue{ OS.bodyContent }.append(BodyItems::AdditionalImplementations,
        "DEFINE_VECTOR(" + newClassName + ")\n");

      constructorBody << 
        newClassName << "* " << newClassName << "_create(const void* origin)\n"
        "{\n"
        "  auto result = " << ClassPrefix << "SCR::createWrappedObject<" << originalClassName << ", " << newClassName << ">(origin);\n";

      destructorBody <<
        "void " << newClassName << "_destroy(const " << newClassName << "* self) \n" <<
        "{\n";

      // Does this class has a base class? (Multiple base classes are currently not supported
      if (crd->getNumBases() != 0)
      {
        auto bases = crd->bases();
        auto baseClass = *bases.begin();

        const auto originalBaseClassName = baseClass.getType()->getAsCXXRecordDecl()->getNameAsString();
        const auto newBaseClassName = createNewClassName(originalBaseClassName);

        VisitValue{ OS.headerContent }.append(HeaderItems::Members,
          "  " + newBaseClassName + "* base;\n");

        constructorBody << 
          "  const auto originalBase = reinterpret_cast<const " << originalClassName << "*>(origin);\n" <<
          "  result->base = " << newBaseClassName << "_create(dynamic_cast<const " << originalBaseClassName << "*>(originalBase));\n";

        destructorBody << 
          "  " + newBaseClassName + "_destroy(self->base);\n";

        VisitValue{ OS.headerContent }.append(HeaderItems::AdditionalIncludeFiles, "#include \"" + newBaseClassName + ".h\"");

        // TODO allow call of base class functions
      }

      constructorBody <<
        "  result->origin = origin;\n"
        "  return result;\n"
        "};\n";

      constructorBody.flush();
      VisitValue{ OS.bodyContent }.append(BodyItems::ConstructorImplementation, constructorBody.str());

      destructorBody <<
        "  delete self;\n" << 
        "}\n";

      destructorBody.flush();
      VisitValue{ OS.bodyContent }.append(BodyItems::DestructorImplementation, destructorBody.str());

      // TODO Loop over members
      // Loop over public functions
      for (const auto& method : crd->methods())
      {
        if (method->getAccess() != AccessSpecifier::AS_public)
          continue;

        string mappedFunctionName;

        // ignore operator overloadings
        if (method->isOverloadedOperator())
          continue;

        // constructor
        if (const CXXConstructorDecl *ccd = dyn_cast<CXXConstructorDecl>(method))
        {
          //VisitValue{ OS.headerContent }.append(HeaderItems::FreeFunctionDeclaration,
          //  "  FIXME: ADDITIONAL CONSTRUCTOR NEEDED\n");

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
          const string originalFunctionName = method->getNameAsString();
          mappedFunctionName = originalFunctionName;
          mappedFunctionName[0] = tolower(mappedFunctionName[0]);
          mappedFunctionName = newClassName + "_" + mappedFunctionName;

          const QualType qt = method->getReturnType();
          auto cType = determineCType(sourceManager, qt);

          if (!cType.isVoid)
          {
            auto sourceFileName = generateMappedInclude(cType.declarationSourceFile);

            if (!sourceFileName.empty())
            {
              appendUnique(get<Strings>(OS.headerContent[HeaderItems::AdditionalIncludeFiles]), "#include \"" + ClassPrefix + sourceFileName + "\"");
            }

            if (!cType.enumDefinition.empty())
            {
              appendUnique(get<Strings>(OS.headerContent[HeaderItems::EnumDefinitions]), cType.enumDefinition);
            }
          }

          string returnType;
          if (cType.isPointer)
          {
            returnType = cType.mappedType + "* ";
            functionHeader << "__declspec(dllexport) const " << returnType << mappedFunctionName << "(";
            functionBody << "const " << cType.mappedType << "* " << mappedFunctionName << "(";
          }
          else
          {
            returnType = cType.mappedType.empty() ? string("void") : cType.mappedType;
            functionHeader << "__declspec(dllexport) " << returnType << " " << mappedFunctionName << "(";
            functionBody << returnType << " " << mappedFunctionName << "(";
          }

          if (!method->isStatic())
          {
            parameters.push_back("const " + newClassName + "* self");
          }

          for (const auto& parameter : method->parameters())
          {
            const QualType paramQt = parameter->getOriginalType();
            auto pType = determineCType(sourceManager, paramQt);
            const auto& parameterName = parameter->getNameAsString();

            if (!pType.isVoid)
            {
              auto sourceFileName = generateMappedInclude(cType.declarationSourceFile);

              if (!sourceFileName.empty())
              {
                appendUnique(get<Strings>(OS.headerContent[HeaderItems::AdditionalIncludeFiles]), "#include \"" + ClassPrefix + sourceFileName + "\"");
              }
            }

            if (pType.isPointer)
            {
              parameters.push_back("const " + pType.mappedType + "* " + parameterName);
            }
            else
            {
              if (!pType.isLValueReference)
                parameters.push_back("const " + pType.mappedType + "& " + parameterName);
              else
                parameters.push_back(pType.mappedType + " " + parameterName);
            }
            parametersCall.push_back(parameterName);
          }

          auto allParameters = ::join(parameters, ", ");
          functionHeader << allParameters << ");\n";
          functionHeader.flush();
          VisitValue{ OS.headerContent }.append(HeaderItems::FreeFunctionDeclaration, functionHeader.str());

          stringstream functionCall;

          functionBody << allParameters << ")\n"
            << "{\n";

          if (!cType.isVoid)
          {
            functionBody << "  const auto& value = ";
          }

          if (method->isStatic())
          {
            functionBody <<
              originalFunctionName << "(";
          }
          else
          {
            functionBody <<
              "  reinterpret_cast<const " << originalClassName << "*>(self->origin)->" << originalFunctionName << "(";
          }

          functionBody <<
            ::join(parametersCall, ", ") << ");\n"; 

          if (returnType != "void")
          {
            if (cType.static_cast_needed)
            {
              functionBody << "  return static_cast<" << cType.mappedType << ">(value);\n";
            }
            else if (cType.mappedType == "char")
            {
              functionBody << "  return value.c_str();\n";
            }
            else if (cType.isVector)
            {
              functionBody <<
                "  using OriginType = decltype(value);\n" <<
                "  using PureType = std::remove_reference_t<std::remove_const_t<OriginType>>;\n " <<
                "  return " << ClassPrefix << "SCR::createWrappedObjectArray<PureType, " << cType.mappedType << ">(value);\n";
            }
            else if (cType.isPOD)
            {
              functionBody << "  return value;\n";
            }
            else
            {
              functionBody <<
                "  using OriginType = decltype(value);\n" <<
                "  using PureType = std::remove_reference_t<std::remove_const_t<OriginType>>;\n " <<
                "  return " << ClassPrefix << "SCR::createWrappedObject<PureType, " << cType.mappedType << ">(&value);\n";
            }
          }
          functionBody <<
            "}\n";
          
          VisitValue{ OS.bodyContent }.append(BodyItems::FreeFunctionImplementation, functionBody.str());

          parameters.clear();
          parametersCall.clear();
          functionHeader.str(string());
          functionBody.str(string());
        }
      }

      for (const auto& item : OS.headerContent)
      {
        std::visit(ContentPrinter(OS.HeaderOS), item.second);
      }

      for (const auto& item : OS.bodyContent)
      {
        std::visit(ContentPrinter(OS.BodyOS), item.second);
      }

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



// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction
{
public:
  MyFrontendAction()
    : OS(currentFile)
  {
    _originalIncludeFileName = currentFile;

    originalSourceFile = stripPathFromFileName(currentFile);

    currentFile = guessOriginalClassNameFromFileName(currentFile);
    // strip off the leading I
    if (currentFile[0] == 'I')
      currentFile = currentFile.substr(1, currentFile.size() - 1);


    _className = ClassPrefix + currentFile;
    _headerFileName = _className + ".h";
    _bodyFileName = _className + ".cpp";
  }


  bool BeginSourceFileAction(CompilerInstance &CI) override
  {
    OS.headerContent[HeaderItems::CopyrightNotice] =
      "///////////////////////////////////////////////////////////////////\n"
      "// Copyright 2018 MeVis Medical Solutions AG  all rights reserved\n"
      "///////////////////////////////////////////////////////////////////\n";

    OS.headerContent[HeaderItems::IncludeGuardTop] =
      "#ifndef _" + toUpper(_className) + "_\n"
      "#define _" + toUpper(_className) + "_\n"
      "\n";

    OS.headerContent[HeaderItems::CommonIncludeFiles] = 
      "#include \"MacroHelper.h\"\n"
      "\n"
      "#ifdef __cplusplus\n"
      "extern \"C\"{\n"
      "#endif\n"
      "\n";

    OS.headerContent[HeaderItems::IncludeGuardBottom] =
      "\n"
      "#ifdef __cplusplus\n"
      "}\n"
      "#endif\n"
      "\n"
      "#endif /* _" + toUpper(_className) + "_ */\n";

    OS.bodyContent[BodyItems::CopyrightNotice] =
      "///////////////////////////////////////////////////////////////////\n"
      "// Copyright 2018 MeVis Medical Solutions AG  all rights reserved\n"
      "///////////////////////////////////////////////////////////////////\n"
      "\n";

    OS.bodyContent[BodyItems::StandardInclude] =
      "#include \"" + _headerFileName + "\"\n";

    OS.bodyContent[BodyItems::CommonIncludeFiles] =
      "#include \"TemplateHelper.h\"\n"
      "\n";

    OS.bodyContent[BodyItems::AdditionalIncludeFiles] =
      vector<string>{ "#include <"+ ThirdpartyInclude +"/" + stripPathFromFileName(_originalIncludeFileName) + ">\n" };

    OS.bodyContent[BodyItems::Usings] =
      vector<string>{ "using namespace " + R2NameSpace + ";\n" };

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
