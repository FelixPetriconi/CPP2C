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
#include <numeric>


using namespace std;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace clang::ast_matchers;
using namespace llvm;

namespace
{
  const string ClassPrefix = "R2M_";
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

    void operator()(const string& s) { _stream << s << "\r\n"; }
    void operator()(const vector<string>& v) 
    {
      for (const auto& s : v)
        _stream << s << "\r\n";
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

  string allUpperLetters(const string& camelCase)
  {
    return std::accumulate(camelCase.begin(), camelCase.end(), string(), 
      [](string val, char c)
    {
      if (isUppercase(c))
        return val + c;
      return val;
    });

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
    ExternCBegin,
    ConstructorDefinition,
    //DestructorDefinition,
    MembersToCreate,
    MembersToDestruct,
    ConstructorImplementation,
    DestructorImplementation,
    FreeFunctionImplementation,
    AdditionalImplementations,
    ExternCEnd
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
    bodyContent[BodyItems::ExternCBegin] = string{};
    bodyContent[BodyItems::ConstructorDefinition] = string{};
    //bodyContent[BodyItems::DestructorDefinition] = string{};
    bodyContent[BodyItems::MembersToCreate] = vector<string>{};
    bodyContent[BodyItems::MembersToDestruct] = vector<string>{};
    bodyContent[BodyItems::ConstructorImplementation] = string{};
    bodyContent[BodyItems::DestructorImplementation] = string{};
    bodyContent[BodyItems::FreeFunctionImplementation] = vector<string>{};
    bodyContent[BodyItems::AdditionalImplementations] = vector<string>{};
    bodyContent[BodyItems::ExternCEnd] = string{};
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
    bool isResultPointer = false;
    bool isOriginalPointer = false;
    bool isVector = false;
    bool isEnum = false;
    bool isVoid = false;
    bool isPOD = false;
    bool isReference = false;
    bool isLValueReference = false;
    bool isConstant = false;
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
    result.isReference = qt->isReferenceType();
    result.isConstant = qt.isConstQualified();

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
          result.static_cast_needed = true;
        }
        else
        {
          result.mappedType = qt.getAsString();
          result.originalType = qt.getAsString();
        }
      }
      result.isOriginalPointer = qt->isPointerType();
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
      result.isEnum = true;

      if (stripPathFromFileName(result.declarationSourceFile) == originalSourceFile)
      {
        stringstream enumDefinition;
        enumDefinition <<
          "enum " << result.mappedType << "\r\n"
          "{ \r\n";
        const auto uniqueId = ClassPrefix + allUpperLetters(result.originalType);
        std::vector<string> enumerations;
        std::transform(enumType->enumerator_begin(), enumType->enumerator_end(), back_inserter(enumerations), [uniqueId](const auto& enumItem)
        {
          return string("  ") + uniqueId + "_" + enumItem->getNameAsString() + " = " + to_string(enumItem->getInitVal().getExtValue());
        });

        enumDefinition <<
          ::join(enumerations, ", \r\n") << "\r\n" <<
          "};\r\n";

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
      result.isOriginalPointer = qt->isPointerType();

      if (recordName == "basic_string")
      {
        result.mappedType = "char";
        result.isResultPointer = true;
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
          result.originalType = "std::vector<std::string>";
        }
        else if (cType.originalType == "Point2D<int>" || cType.originalType == "Point2D<float>")
        {
          valueTypeName = cType.mappedType;
          result.declarationSourceFile = cType.declarationSourceFile;
          result.originalType = "std::vector<" + cType.originalType + ">";
        }
        else
        {
          valueTypeName = cType.mappedType;
          result.declarationSourceFile = cType.declarationSourceFile;
          auto valueType = (cType.isResultPointer ? "const " : "") + cType.originalType + (cType.isResultPointer ? "*" : "");
          result.originalType = "std::vector<" + valueType + ">";
        }

        result.mappedType = "vector_" + createNewClassName(valueTypeName);
        result.isResultPointer = true;
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
        result.isResultPointer = true;
      }
      else
      {
        result.originalType = recordName;
        result.mappedType = createNewClassName(recordName);
        result.declarationSourceFile = sourceManager.getFilename(crd->getLocation()).str();
        result.isResultPointer = true;
        result.isOriginalPointer = qt->isPointerType();
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
        "struct " + ClassPrefix + "DECLSPEC " + newClassName + "\r\n"
        "{\r\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::StructBodyBottom,
        "};\r\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::Members,
        "  typedef const " + newClassName + "*(*constructor_t)(const void*);\r\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::Members,
        "  static constructor_t constructor;\r\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::Members,
        "  typedef void(*destructor_t)(const " + newClassName + "*);\r\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::Members,
        "  destructor_t destructor;\r\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::Members,
        "  const void* origin;\r\n");


      VisitValue{ OS.headerContent }.append(HeaderItems::ConstructorDeclaration,
        ClassPrefix + "DECLSPEC const " + newClassName + "* " + newClassName + "_create(const void* origin);\r\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::DestructorDeclaration,
        ClassPrefix + "DECLSPEC void " + newClassName + "_destroy(const " + newClassName + "* val);\r\n");

      VisitValue{ OS.headerContent }.append(HeaderItems::AdditionalDeclarations,
        "DECLARE_VECTOR(" + newClassName + ")\r\n");

      VisitValue{ OS.bodyContent }.append(BodyItems::ConstructorDefinition,
        newClassName + "::constructor_t " + newClassName + "::constructor = &" + newClassName + "_create;\r\n");

      //VisitValue{ OS.bodyContent }.append(BodyItems::DestructorDefinition,
      //  "void ((*" + newClassName + "::destructor))(const " + newClassName + "*) = &" + newClassName + "_destroy;\r\n");

      VisitValue{ OS.bodyContent }.append(BodyItems::AdditionalImplementations,
        "DEFINE_VECTOR(" + newClassName + ")\r\n");

      constructorBody << 
        "const " << newClassName << "* " << newClassName << "_create(const void* origin)\r\n"
        "{\r\n"
        "  auto result = " << ClassPrefix << "SCR::createWrappedObject<" << originalClassName << ", " << newClassName << ">(origin);\r\n";

      destructorBody <<
        "void " << newClassName << "_destroy(const " << newClassName << "* self) \r\n" <<
        "{\r\n";

      // Does this class has a base class? (Multiple base classes are currently not supported
      if (crd->getNumBases() != 0)
      {
        auto bases = crd->bases();
        auto baseClass = *bases.begin();

        const auto originalBaseClassName = baseClass.getType()->getAsCXXRecordDecl()->getNameAsString();
        const auto newBaseClassName = createNewClassName(originalBaseClassName);

        VisitValue{ OS.headerContent }.append(HeaderItems::Members,
          "  const " + newBaseClassName + "* base;\r\n");

        constructorBody << 
          "  const auto originalBase = reinterpret_cast<const " << originalClassName << "*>(origin);\r\n" <<
          "  result->base = " << newBaseClassName << "_create(dynamic_cast<const " << originalBaseClassName << "*>(originalBase));\r\n";

        destructorBody << 
          "  " + newBaseClassName + "_destroy(self->base);\r\n";

        VisitValue{ OS.headerContent }.append(HeaderItems::AdditionalIncludeFiles, "#include \"" + newBaseClassName + ".h\"");

        // TODO allow call of base class functions
      }

      constructorBody <<
        "  result->destructor = &" + newClassName + "_destroy;\r\n"
        "  result->origin = origin;\r\n"
        "  return result;\r\n"
        "};\r\n";

      constructorBody.flush();
      VisitValue{ OS.bodyContent }.append(BodyItems::ConstructorImplementation, constructorBody.str());

      destructorBody <<
        "  delete self;\r\n" << 
        "}\r\n";

      destructorBody.flush();
      VisitValue{ OS.bodyContent }.append(BodyItems::DestructorImplementation, destructorBody.str());

      // TODO Loop over members
      // Loop over public functions
      std::unordered_map<string, int> functionList;
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
          //  "  FIXME: ADDITIONAL CONSTRUCTOR NEEDED\r\n");

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

          auto itFind = functionList.find(mappedFunctionName);
          if (itFind == functionList.end())
          {
            functionList.insert({ mappedFunctionName, 0 });
          }
          else
          {
            ++(itFind->second);
            mappedFunctionName += std::to_string(itFind->second);
          }

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
          if (cType.isResultPointer)
          {
            returnType = cType.mappedType + "* ";
            functionHeader << ClassPrefix << "DECLSPEC const " << returnType << mappedFunctionName << "(";
            functionBody << "const " << cType.mappedType << "* " << mappedFunctionName << "(";
          }
          else
          {
            returnType = cType.mappedType.empty() ? string("void") : cType.mappedType;
            functionHeader << ClassPrefix << "DECLSPEC " << returnType << " " << mappedFunctionName << "(";
            functionBody << returnType << " " << mappedFunctionName << "(";
          }

          auto constness = method->isConst() ? "const " : "";
          if (!method->isStatic())
          {
            parameters.push_back(constness + newClassName + "* self");
          }

          stringstream additionalVariables;
          stringstream returnByReference;
          int variableIndex = 0;
          for (const auto& parameter : method->parameters())
          {
            const QualType paramQt = parameter->getOriginalType();
            auto pType = determineCType(sourceManager, paramQt);
            const auto& parameterName = parameter->getNameAsString();

            auto sourceFileName = generateMappedInclude(pType.declarationSourceFile);
            if (!sourceFileName.empty())
            {
              appendUnique(get<Strings>(OS.headerContent[HeaderItems::AdditionalIncludeFiles]), "#include \"" + ClassPrefix + sourceFileName + "\"");
            }


            if (pType.isReference && !pType.isConstant && !pType.isPOD && pType.mappedType != "char")
            {
              parameters.push_back(pType.mappedType + "* " + parameterName);
              auto tempVariableName = " val" + to_string(variableIndex);
              parametersCall.push_back(tempVariableName);
              additionalVariables << 
                "  " << pType.originalType << tempVariableName << ";\r\n";
              returnByReference <<
                "  " << ClassPrefix << "SCR::copyArrayObjects(" << tempVariableName << ", " << parameterName << ");\r\n";
            }
            else if (pType.isReference && pType.isConstant)
            {
              parameters.push_back("const " + pType.mappedType + "& " + parameterName);
            }
            else if (pType.mappedType == "char" || (pType.isResultPointer && !pType.isReference && pType.isConstant))
            {
              parameters.push_back("const " + pType.mappedType + "* " + parameterName);
              parametersCall.push_back(parameterName);
            }
            else 
            {
              auto type = pType.mappedType;
              if (type.back() != '&' && pType.isReference)
              {
                type += "&";
              }
              if (type.find("const") == string::npos && pType.isConstant)
              {
                type = "const " + type;
              }
              parameters.push_back(type + " " + parameterName);
              if (pType.static_cast_needed)
              {
                parametersCall.push_back("static_cast<" + pType.originalType + ">(" + parameterName + ")");
              }
              else
              {
                parametersCall.push_back(parameterName);
              }
            }
            
            ++variableIndex;
          }

          auto allParameters = ::join(parameters, ", ");
          functionHeader << allParameters << ");\r\n";
          functionHeader.flush();
          VisitValue{ OS.headerContent }.append(HeaderItems::FreeFunctionDeclaration, functionHeader.str());

          stringstream functionCall;

          functionBody << allParameters << ")\r\n"
            << "{\r\n";

          additionalVariables.flush();
          functionBody << additionalVariables.str();

          if (!cType.isVoid)
          {
            functionBody << "  " << ((cType.isPOD || cType.isEnum) ? string() : constness) <<
              ((!cType.isReference || cType.isPOD || cType.isEnum)? "auto " : "auto& ") << "value = ";
          }

          if (method->isStatic())
          {
            functionBody <<
              "  " << originalClassName << "::" << originalFunctionName << "(";
          }
          else
          {
            if (method->isConst())
            {
              functionBody <<
                "  reinterpret_cast<const " << originalClassName << "*>(self->origin)->" << originalFunctionName << "(";
            }
            else
            {
              functionBody <<
                "  reinterpret_cast<" << originalClassName << "*>(const_cast<void*>(self->origin))->" << originalFunctionName << "(";
            }
          }

          functionBody <<
            ::join(parametersCall, ", ") << ");\r\n"; 

          if (returnType != "void")
          {
            if (cType.static_cast_needed)
            {
              functionBody << "  return static_cast<" << cType.mappedType << ">(value);\r\n";
            }
            else if (cType.mappedType == "char")
            {
              appendUnique(get<Strings>(OS.headerContent[HeaderItems::AdditionalIncludeFiles]), "#include \"" + ClassPrefix + "StringHelper.h" + "\"");
              functionBody << "  return " << ClassPrefix << "allocateAndCopyString(value.c_str());\r\n";
            }
            else if (cType.isVector)
            {
              functionBody <<
                "  using OriginType = decltype(value);\r\n" <<
                "  using PureType = std::remove_reference_t<std::remove_const_t<OriginType>>;\r\n " <<
                "  return " << ClassPrefix << "SCR::createWrappedObjectArray<PureType, " << cType.mappedType << ">(value);\r\n";
            }
            else if (cType.isPOD)
            {
              functionBody << "  return value;\r\n";
            }
            else
            {
              functionBody <<
                "  using OriginType = decltype(value);\r\n" <<
                "  using PureType = std::remove_reference_t<std::remove_const_t<OriginType>>;\r\n ";

              if (cType.isReference)
              {
                if (cType.mappedType == "R2M_Point2DInt" || cType.mappedType == "R2M_Point2DFloat")
                {
                  functionBody <<
                    "  auto result = " << ClassPrefix << "SCR::createWrappedObject<PureType, " << cType.mappedType << ">(&value);\r\n" <<
                    "  result->x = value.X;\r\n" <<
                    "  result->y = value.Y;\r\n";
                }
                else
                {
                  functionBody <<
                    "  auto result = " << ClassPrefix << "SCR::createWrappedObject<PureType, " << cType.mappedType << ">(&value);\r\n";
                }
              }
              else
              {
                if (cType.isOriginalPointer)
                {
                  functionBody <<
                    "  auto result = (value != nullptr)? " << ClassPrefix << "SCR::createWrappedObject<PureType, " << cType.mappedType << ">(value) : nullptr;\r\n";
                }
                else
                {
                  functionBody <<
                    "  auto result = (value != nullptr)? " << ClassPrefix << "SCR::createWrappedObject<PureType, " << cType.mappedType << ">(&value) : nullptr;\r\n";
                }
              }

              functionBody <<
                "  if (result)\r\n" <<
                "  {\r\n" <<
                "    const_cast<" << cType.mappedType << "*>(result)->destructor = &" + cType.mappedType + "_destroy;\r\n" <<
                "  }\r\n" << 
                "  return result;\r\n";
            }
          }
          else // isVoid
          {
            returnByReference.flush();
            functionBody <<
              returnByReference.str();
          }

          functionBody <<
            "}\r\n";
          
          VisitValue{ OS.bodyContent }.append(BodyItems::FreeFunctionImplementation, functionBody.str());

          parameters.clear();
          parametersCall.clear();
          functionHeader.str(string());
          functionBody.str(string());
          additionalVariables.str(string());
          returnByReference.str(string());
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
      "///////////////////////////////////////////////////////////////////\r\n"
      "// Copyright 2018 MeVis Medical Solutions AG  all rights reserved\r\n"
      "///////////////////////////////////////////////////////////////////\r\n";

    OS.headerContent[HeaderItems::IncludeGuardTop] =
      "#ifndef _" + toUpper(_className) + "_\r\n"
      "#define _" + toUpper(_className) + "_\r\n"
      "\r\n";

    OS.headerContent[HeaderItems::CommonIncludeFiles] = 
      "#include \"" + ClassPrefix + "Config.h\"\r\n"
      "#include \"" + ClassPrefix + "MacroHelper.h\"\r\n"
      "\r\n"
      "#ifdef __cplusplus\r\n"
      "extern \"C\"{\r\n"
      "#endif\r\n"
      "\r\n";

    OS.headerContent[HeaderItems::IncludeGuardBottom] =
      "\r\n"
      "#ifdef __cplusplus\r\n"
      "}\r\n"
      "#endif\r\n"
      "\r\n"
      "#endif /* _" + toUpper(_className) + "_ */\r\n";

    OS.bodyContent[BodyItems::CopyrightNotice] =
      "///////////////////////////////////////////////////////////////////\r\n"
      "// Copyright 2018 MeVis Medical Solutions AG  all rights reserved\r\n"
      "///////////////////////////////////////////////////////////////////\r\n"
      "\r\n"
      "#pragma warning(disable:4800)\r\n"
      "\r\n";

    OS.bodyContent[BodyItems::StandardInclude] =
      "#include \"" + _headerFileName + "\"\r\n";

    OS.bodyContent[BodyItems::CommonIncludeFiles] =
      "#include \"" + ClassPrefix + "TemplateHelper.h\"\r\n"
      "\r\n";

    OS.bodyContent[BodyItems::AdditionalIncludeFiles] =
      vector<string>{ "#include <"+ ThirdpartyInclude +"/" + stripPathFromFileName(_originalIncludeFileName) + ">\r\n" };

    OS.bodyContent[BodyItems::Usings] =
      vector<string>{ "using namespace " + R2NameSpace + ";\r\n" };

    OS.bodyContent[BodyItems::ExternCBegin] =
      "#ifdef __cplusplus \r\n"
      "extern \"C\" { \r\n"
      "#endif \r\n";

    OS.bodyContent[BodyItems::ExternCEnd] =
      "#ifdef __cplusplus \r\n"
      "} \r\n"
      "#endif \r\n";

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
        << '\r\n';
      exit(1);
    }
    llvm::raw_fd_ostream BOS(bodyFile, EC, llvm::sys::fs::F_None);
    if (EC)
    {
      llvm::errs() << "while opening '" << bodyFile << "': " << EC.message()
        << '\r\n';
      exit(1);
    }

    OS.HeaderOS.flush();
    OS.BodyOS.flush();
    HOS << OS.headerString << "\r\n";    
    BOS << OS.bodyString << "\r\n";
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
