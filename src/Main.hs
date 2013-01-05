{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main (main) where

import           Control.Applicative
import           Control.Monad.Error
import           Control.Monad.State
import           Language.Haskell.Exts
import           System.Environment
import           Text.Groom

data CompileState = CompileState
  { stateSearchString :: String
  , stateLoc :: [SrcLoc]
  , stateFinds :: [[SrcLoc]]
  } deriving (Show)

data CompileError
  = CompileError
  | UnsupportedDecl Decl
  | UnsupportedTyVarBind TyVarBind
  | UnsupportedQualConDecl QualConDecl
  | UnsupportedDeriving Deriving
  | UnsupportedExp Exp
  | UnsupportedRPat RPat
  | UnsupportedXName XName
  | UnsupportedPXAttr PXAttr
  deriving (Show)

instance Error CompileError

newtype Compile a = Compile { unCompile :: StateT CompileState (ErrorT CompileError IO) a }
  deriving
    ( MonadState CompileState
    , MonadError CompileError
    , MonadIO
    , Monad
    , Functor
    , Applicative
    )

runCompile :: CompileState -> Compile a -> IO (Either CompileError (a, CompileState))
runCompile state compiler = runErrorT (runStateT (unCompile compiler) state)

withLoc :: SrcLoc -> Compile a -> Compile a
withLoc loc m = do
  prevLoc <- gets stateLoc
  modify $ \s -> s { stateLoc = loc : stateLoc s }
  value <- m
  modify $ \s -> s { stateLoc = prevLoc }
  return value

main :: IO ()
main = do
  args             <- getArgs
  let searchString = args !! 0
  let filename     = args !! 1
  contents         <- readFile filename
  let ast          = parseModuleWithMode (defaultParseMode { parseFilename = filename, extensions = exts, ignoreLinePragmas = False }) contents
  res <- case ast of
    p@(ParseFailed _ _) -> error $ groom p
    ParseOk m -> runCompile (CompileState searchString [] []) (c_module m)
  putStrLn $ "Searched for " ++ searchString
  case res of
    Left e -> error $ groom e
    Right ((),res) ->
      case stateFinds res of
        [] -> putStrLn "No matches"
        fs -> forM_ fs $ \(SrcLoc fn l c:_) -> putStrLn $ fn ++ ":" ++ show l ++ ":" ++ show c
    where
      exts =
        [ OverlappingInstances
        , UndecidableInstances
        , IncoherentInstances
        , RecursiveDo
        , ParallelListComp
        , MultiParamTypeClasses
        , NoMonomorphismRestriction
        , FunctionalDependencies
        , ExplicitForAll
        , Rank2Types
        , RankNTypes
        , PolymorphicComponents
        , ExistentialQuantification
        , ScopedTypeVariables
        , ImplicitParams
        , FlexibleContexts
        , FlexibleInstances
        , EmptyDataDecls
        , CPP
        , KindSignatures
        , BangPatterns
        , TypeSynonymInstances
        , TemplateHaskell
        , ForeignFunctionInterface
        -- , Arrows
        , Generics
        , NoImplicitPrelude
        , NamedFieldPuns
        , PatternGuards
        , GeneralizedNewtypeDeriving
        , ExtensibleRecords
        , RestrictedTypeSynonyms
        , HereDocuments
        , MagicHash
        , TypeFamilies
        , StandaloneDeriving
        , UnicodeSyntax
        , PatternSignatures
        , UnliftedFFITypes
        , LiberalTypeSynonyms
        , TypeOperators
        , RecordWildCards
        , RecordPuns
        , DisambiguateRecordFields
        , OverloadedStrings
        , GADTs
        , MonoPatBinds
        , NoMonoPatBinds
        , RelaxedPolyRec
        , ExtendedDefaultRules
        , UnboxedTuples
        , DeriveDataTypeable
        , ConstrainedClassMethods
        , NPlusKPatterns
        , PackageImports
        , DoAndIfThenElse
        , ImpredicativeTypes
        , NewQualifiedOperators
        , PostfixOperators
        , QuasiQuotes
        , TransformListComp
        , ViewPatterns
        , XmlSyntax
        , RegularPatterns
        , TupleSections
        ]

match :: String -> Compile ()
match name = do
  s <- gets stateSearchString
  loc <- gets stateLoc
  when (name == s) $
    modify $ \s -> s { stateFinds = loc : stateFinds s }

mayb :: (a -> Compile ()) -> Maybe a -> Compile ()
mayb = maybe (return ())

list :: (a -> Compile ()) -> [a] -> Compile ()
list = mapM_

c_module :: Module -> Compile ()
c_module (Module loc mod _pragmas _wt expspec importdecls decls) = do
  withLoc loc $ do
    matchMod mod
    mayb (list c_exportSpec) expspec
    list c_importDecl importdecls
    list c_decl decls

-- WarningText

c_exportSpec :: ExportSpec -> Compile ()
c_exportSpec es = case es of
  EVar n -> matchQ n
  EAbs n -> matchQ n
  EThingAll n -> matchQ n
  EThingWith n cns -> matchQ n >> list matchC cns
  EModuleContents m -> matchMod m

c_importDecl :: ImportDecl -> Compile ()
c_importDecl (ImportDecl loc mod _qual _src pkg as specs) = do
  withLoc loc $ do
    matchMod mod
    mayb match pkg
    mayb matchMod as
    mayb (\(_,sps) -> list c_importSpec sps) specs

c_importSpec :: ImportSpec -> Compile ()
c_importSpec is = case is of
  IVar n -> matchN n
  IAbs n -> matchN n
  IThingAll n -> matchN n
  IThingWith n cns -> matchN n >> list matchC cns

-- Assoc

c_decl :: Decl -> Compile ()
c_decl decl = case decl of
  TypeDecl loc n binds typ -> throwError $ UnsupportedDecl decl
  TypeFamDecl loc n binds kind -> throwError $ UnsupportedDecl decl
  DataDecl loc _dataornew _ctx n binds qualcon der -> withLoc loc $ do
    matchN n
    list c_tyVarBind binds
    list c_qualConDecl qualcon
    list c_deriving der
  GDataDecl loc dataornew cxt n binds kind gadts der -> throwError $ UnsupportedDecl decl
  DataFamDecl loc ctx n binds kind -> throwError $ UnsupportedDecl decl
  TypeInsDecl loc typ1 typ2 -> throwError $ UnsupportedDecl decl
  DataInsDecl loc dataornew typ qualcon der -> throwError $ UnsupportedDecl decl
  GDataInsDecl loc dataornew typ kind gadt der -> throwError $ UnsupportedDecl decl
  ClassDecl loc _ctx n binds fundeps classs -> withLoc loc $ matchN n >> list c_tyVarBind binds >> list c_funDep fundeps >> list c_classDecl classs
  InstDecl loc ctx qn typs insts -> withLoc loc $ list c_type typs >> list c_instDecl insts
  DerivDecl loc ctx q typs -> throwError $ UnsupportedDecl decl
  InfixDecl loc assoc i ops -> throwError $ UnsupportedDecl decl
  DefaultDecl loc typ -> throwError $ UnsupportedDecl decl
  SpliceDecl loc exp -> throwError $ UnsupportedDecl decl
  TypeSig loc ns typ -> withLoc loc $ list matchN ns >> c_type typ
  FunBind matchs -> list c_match matchs
  PatBind loc pat typ rhs binds -> withLoc loc $ c_pat pat >> mayb c_type typ >> c_rhs rhs >> c_binds binds
  ForImp loc callconv safety str n typ -> throwError $ UnsupportedDecl decl
  ForExp loc callconv str n typ -> throwError $ UnsupportedDecl decl
  RulePragmaDecl loc rules -> throwError $ UnsupportedDecl decl
  DeprPragmaDecl loc nstrs -> throwError $ UnsupportedDecl decl
  WarnPragmaDecl loc nstrs -> throwError $ UnsupportedDecl decl
  InlineSig loc bool act qn -> throwError $ UnsupportedDecl decl
  InlineConlikeSig loc act qn -> throwError $ UnsupportedDecl decl
  SpecSig loc qn typs -> throwError $ UnsupportedDecl decl
  SpecInlineSig loc bool act qn typs -> throwError $ UnsupportedDecl decl
  InstSig loc ctx qn typs -> throwError $ UnsupportedDecl decl
  AnnPragma loc ann -> throwError $ UnsupportedDecl decl

c_binds binds = case binds of
  BDecls decls -> list c_decl decls
  IPBinds ipbs -> list c_ipBind ipbs

c_ipBind (IPBind loc ip e) = withLoc loc $ matchIP ip >> c_exp e

c_classDecl cdecl = case cdecl of
  ClsDecl d -> c_decl d
  ClsDataFam loc _ctx n tbs k -> withLoc loc $ matchN n >> list c_tyVarBind tbs >> mayb c_kind k
  ClsTyFam loc n tbs k -> withLoc loc $ matchN n >> list c_tyVarBind tbs >> mayb c_kind k
  ClsTyDef loc t1 t2 -> withLoc loc $ c_type t1 >> c_type t2

c_instDecl id = case id of
  InsDecl d -> c_decl d
  InsType loc t1 t2 -> withLoc loc $ c_type t1 >> c_type t2
  InsData loc _dn ty qcs ders -> withLoc loc $ c_type ty >> list c_qualConDecl qcs >> list c_deriving ders
  InsGData loc _dn t k gdecls der -> withLoc loc $ c_type t >> mayb c_kind k >> list c_gadtDecl gdecls >> list c_deriving der

c_deriving :: Deriving -> Compile ()
c_deriving (q, ts) = matchQ q >> list c_type ts

-- dataornew

c_conDecl cd = case cd of
  ConDecl n bt -> matchN n >> list c_bangType bt
  InfixConDecl bt1 n bt2 -> c_bangType bt1 >> matchN n >> c_bangType bt2
  RecDecl n nbts -> matchN n >> forM_ nbts (\(ns,bt) -> list matchN ns >> c_bangType bt)

c_qualConDecl (QualConDecl loc tyvarbinds _ctx condecl) = withLoc loc $ do
  list c_tyVarBind tyvarbinds
  c_conDecl condecl

c_gadtDecl (GadtDecl loc n t) = withLoc loc $ matchN n >> c_type t

c_bangType bt = case bt of
  BangedTy t -> c_type t
  UnBangedTy t -> c_type t
  UnpackedTy t -> c_type t

c_match (Match loc n pats typ rhs binds) = withLoc loc $ do
  matchN n
  list c_pat pats
  mayb c_type typ
  c_rhs rhs
  c_binds binds

c_rhs rhs = case rhs of
  UnGuardedRhs e -> c_exp e
  GuardedRhss rhss -> list c_guardedRhs rhss

c_guardedRhs (GuardedRhs loc stmts e) = withLoc loc $ list c_stmt stmts >> c_exp e


-- cantext

c_funDep (FunDep ns1 ns2) = list matchN ns1 >> list matchN ns2

-- asst

c_type typ = case typ of
  TyForall tyvar _ctx typ -> mayb (list c_tyVarBind) tyvar >> c_type typ
  TyFun t1 t2 -> c_type t1 >> c_type t2
  TyTuple _b ts -> list c_type ts
  TyList ty -> c_type ty
  TyApp t1 t2 -> c_type t1 >> c_type t2
  TyVar n -> matchN n
  TyCon qn -> matchQ qn
  TyParen t1 -> c_type t1
  TyInfix t1 q t2 -> c_type t1 >> matchQ q >> c_type t2
  TyKind t k -> c_type t >> c_kind k

-- boxed
c_kind kind = case kind of
  KindStar -> return ()
  KindBang -> return ()
  KindFn k1 k2 -> c_kind k1 >> c_kind k2
  KindParen k -> c_kind k
  KindVar n -> matchN n

c_tyVarBind :: TyVarBind -> Compile ()
c_tyVarBind tvb = case tvb of
  KindedVar n k -> matchN n >> c_kind k
  UnkindedVar n -> matchN n


c_exp exp = case exp of
  Var q                 -> matchQ q
  IPVar ip              -> matchIP ip
  Con q                 -> matchQ q
  Lit lit               -> c_literal lit
  InfixApp e1 qop e2 -> c_exp e1 >> c_qop qop >> c_exp e2
  App e1 e2 -> c_exp e1 >> c_exp e2
  NegApp e -> c_exp e
  Lambda loc pats e -> withLoc loc $ list c_pat pats >> c_exp e
  Let bs e -> c_binds bs >> c_exp e
  If e1 e2 e3 -> list c_exp [e1,e2,e3]
  Case e alts -> c_exp e >> list c_alt alts
  Do s -> list c_stmt s
  MDo s -> list c_stmt s
  Tuple es -> list c_exp es
  TupleSection e -> list (mayb c_exp) e
  List es -> list c_exp es
  Paren e -> c_exp e
  LeftSection e qop -> c_exp e >> c_qop qop
  RightSection qop e -> c_qop qop >> c_exp e
  RecConstr q fus -> matchQ q >> list c_fieldUpdate fus
  RecUpdate e fus -> c_exp e >> list c_fieldUpdate fus
  EnumFrom e -> c_exp e
  EnumFromTo e1 e2 -> c_exp e1 >> c_exp e2
  EnumFromThen e1 e2 -> c_exp e1 >> c_exp e2
  EnumFromThenTo e1 e2 e3 -> list c_exp [e1,e2,e3]
  ListComp e qs -> c_exp e >> list c_qualStmt qs
  ParComp  e qss -> c_exp e >> list (list c_qualStmt) qss
  ExpTypeSig loc e t -> withLoc loc $ c_exp e >> c_type t
  VarQuote q -> matchQ q
  TypQuote q -> matchQ q
  BracketExp b -> c_bracket b
  SpliceExp s -> c_splice s
  QuasiQuote _s1 _s2 -> return ()
  XTag loc x xas e es -> withLoc loc $ matchX x >> list c_xattr xas >> mayb c_exp e >> list c_exp es
  XETag loc x xas e -> withLoc loc $ matchX x >> list c_xattr xas >> mayb c_exp e
  XPcdata _s -> return ()
  XExpTag e -> c_exp e
  XChildTag loc es -> withLoc loc $ list c_exp es
  CorePragma _s e -> c_exp e
  SCCPragma _s e -> c_exp e
  GenPragma _s _is1 _is2 e -> c_exp e
  Proc loc p e -> withLoc loc $ c_pat p >> c_exp e
  LeftArrApp e1 e2 -> c_exp e1 >> c_exp e2
  RightArrApp e1 e2 -> c_exp e1 >> c_exp e2
  LeftArrHighApp e1 e2 -> c_exp e1 >> c_exp e2
  RightArrHighApp e1 e2 -> c_exp e1 >> c_exp e2

c_stmt stmt = case stmt of
  Generator loc p e -> withLoc loc $ c_pat p >> c_exp e
  Qualifier e -> c_exp e
  LetStmt bs -> c_binds bs
  RecStmt sts -> list c_stmt sts

c_qualStmt quals = case quals of
  QualStmt s -> c_stmt s
  ThenTrans e -> c_exp e
  ThenBy e1 e2 -> c_exp e1 >> c_exp e2
  GroupBy e -> c_exp e
  GroupUsing e -> c_exp e
  GroupByUsing e1 e2 -> c_exp e1 >> c_exp e2

c_fieldUpdate fu = case fu of
  FieldUpdate q e -> matchQ q >> c_exp e
  FieldPun n -> matchN n
  FieldWildcard -> return ()

c_alt (Alt loc p gas bs) = withLoc loc $ c_pat p >> c_guardedAlts gas >> c_binds bs

c_guardedAlts gas = case gas of
  UnGuardedAlt e -> c_exp e
  GuardedAlts gas -> list c_guardedAlt gas

c_guardedAlt (GuardedAlt loc ss e) = withLoc loc $ list c_stmt ss >> c_exp e

c_xattr (XAttr x e) = matchX x >> c_exp e

c_pat pat = case pat of
  PVar n -> matchN n
  PLit lit -> c_literal lit
  PNeg p -> c_pat p
  PNPlusK n _i -> matchN n
  PInfixApp p1 q p2 -> c_pat p1 >> matchQ q >> c_pat p2
  PApp q ps -> matchQ q >> list c_pat ps
  PTuple ps -> list c_pat ps
  PList ps -> list c_pat ps
  PParen p -> c_pat p
  PRec q pfs -> matchQ q >> list c_patField pfs
  PAsPat n p -> matchN n >> c_pat p
  PWildCard -> return ()
  PIrrPat p -> c_pat p
  PatTypeSig loc p t -> withLoc loc $ c_pat p >> c_type t
  PViewPat e p -> c_exp e >> c_pat p
  PRPat rpats -> list c_rpat rpats
  PXTag loc x pxats pat pats -> withLoc loc $ matchX x >> list c_pxAttr pxats >> mayb c_pat pat >> list c_pat pats
  PXETag loc x pxats pat -> withLoc loc $ matchX x >> list c_pxAttr pxats >> mayb c_pat pat
  PXPcdata _s -> return ()
  PXPatTag pat -> c_pat pat
  PXRPats rpats -> list c_rpat rpats
  PExplTypeArg q t -> matchQ q >> c_type t
  PQuasiQuote _s1 _s2 -> return ()
  PBangPat pat -> c_pat pat

c_patField pf = case pf of
  PFieldPat q p -> matchQ q >> c_pat p
  PFieldPun n -> matchN n
  PFieldWildcard -> return ()

c_pxAttr x = throwError $ UnsupportedPXAttr x

c_rpat e = throwError $ UnsupportedRPat e

-- rpatop


-- | Literals

c_literal :: Literal -> Compile ()
c_literal _ = return ()

-- Should split the name into a QName
matchMod :: ModuleName -> Compile ()
matchMod (ModuleName s) = match s

matchQ :: QName -> Compile ()
matchQ name = case name of
  Qual _ n -> matchN n
  UnQual n -> matchN n
  Special _sc -> return ()

matchN :: Name -> Compile ()
matchN name = case name of
  Ident n -> match n
  Symbol n -> match n

c_qop qop = case qop of
  QVarOp q -> matchQ q
  QConOp q -> matchQ q

-- op
-- specialcon

matchC :: CName -> Compile ()
matchC c = case c of
  VarName n -> matchN n
  ConName n -> matchN n

matchIP :: IPName -> Compile ()
matchIP ip = case ip of
  IPDup s -> match s
  IPLin s -> match s

matchX x = throwError $ UnsupportedXName x

c_bracket brack = case brack of
  ExpBracket e -> c_exp e
  PatBracket p -> c_pat p
  TypeBracket t -> c_type t
  DeclBracket ds -> list c_decl ds

c_splice sp = case sp of
  IdSplice s -> match s
  ParenSplice e -> c_exp e

-- safety
-- callconv
-- modulepragma
-- tool
-- rule
-- rulevar
-- activation
-- annotation
