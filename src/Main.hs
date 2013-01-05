{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import           Control.Applicative
import           Control.Monad.Error
import           Control.Monad.Identity (Identity)
import           Control.Monad.State
import           Data.String
import           Language.Haskell.Exts
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
  let ast          = parseModuleWithMode (defaultParseMode { parseFilename = filename }) contents
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

match :: String -> Compile ()
match name = do
  s <- gets stateSearchString
  loc <- gets stateLoc
  when (name == s) $
    modify $ \s -> s { stateFinds = loc : stateFinds s }

matchN :: Name -> Compile ()
matchN name = case name of
  Ident n -> match n
  Symbol n -> match n

matchQ :: QName -> Compile ()
matchQ name = case name of
  Qual _ n -> matchN n
  UnQual n -> matchN n

matchC :: CName -> Compile ()
matchC c = case c of
  VarName n -> matchN n
  ConName n -> matchN n

-- Should split the name into a QName
matchMod :: ModuleName -> Compile ()
matchMod (ModuleName s) = match s

c_module :: Module -> Compile ()
c_module (Module loc mod _pragmas _wt expspec importdecls decls) = do
  withLoc loc $ do
    matchMod mod
    maybe (return ()) (mapM_ c_exportSpec) expspec
    mapM_ c_importDecl importdecls
    mapM_ c_decl decls

c_exportSpec :: ExportSpec -> Compile ()
c_exportSpec es = case es of
  EVar n -> matchQ n
  EAbs n -> matchQ n
  EThingAll n -> matchQ n
  EThingWith n cns -> matchQ n >> mapM_ matchC cns
  EModuleContents m -> matchMod m

c_importDecl :: ImportDecl -> Compile ()
c_importDecl (ImportDecl loc mod _qual _src pkg as specs) = do
  withLoc loc $ do
    matchMod mod
    maybe (return ()) match pkg
    maybe (return ()) matchMod as
    maybe (return ()) (\(_,sps) -> mapM_ c_importSpec sps) specs

c_importSpec :: ImportSpec -> Compile ()
c_importSpec is = case is of
  IVar n -> matchN n
  IAbs n -> matchN n
  IThingAll n -> matchN n
  IThingWith n cns -> matchN n >> mapM_ matchC cns

c_decl :: Decl -> Compile ()
c_decl decl = case decl of
  TypeDecl loc n binds typ -> throwError $ UnsupportedDecl decl
  TypeFamDecl loc n binds kind -> throwError $ UnsupportedDecl decl
  DataDecl loc _dataornew _ctx n binds qualcon der -> withLoc loc $ do
    matchN n
    mapM_ c_tyVarBind binds
    mapM_ c_qualConDecl qualcon
    mapM_ c_deriving der
  GDataDecl loc dataornew cxt n binds kind gadts der -> throwError $ UnsupportedDecl decl
  DataFamDecl loc ctx n binds kind -> throwError $ UnsupportedDecl decl
  TypeInsDecl loc typ1 typ2 -> throwError $ UnsupportedDecl decl
  DataInsDecl loc dataornew typ qualcon der -> throwError $ UnsupportedDecl decl
  GDataInsDecl loc dataornew typ kind gadt der -> throwError $ UnsupportedDecl decl
  ClassDecl loc ctx n binds fundeps classs -> throwError $ UnsupportedDecl decl
  InstDecl loc ctx qn typs insts -> throwError $ UnsupportedDecl decl
  DefaultDecl loc typ -> throwError $ UnsupportedDecl decl
  SpliceDecl loc exp -> throwError $ UnsupportedDecl decl
  TypeSig loc ns typ -> throwError $ UnsupportedDecl decl
  FunBind matchs -> throwError $ UnsupportedDecl decl
  PatBind loc pat typ rhs binds -> throwError $ UnsupportedDecl decl
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

c_tyVarBind :: TyVarBind -> Compile ()
c_tyVarBind b = throwError $ UnsupportedTyVarBind b

c_qualConDecl (QualConDecl loc tyvarbinds _ctx condecl) = withLoc loc $ do
  mapM_ c_tyVarBind tyvarbinds
  c_conDecl condecl

c_deriving b = throwError $ UnsupportedDeriving b

c_conDecl cd = case cd of
  ConDecl n bt -> matchN n >> mapM_ c_bangType bt
  InfixConDecl bt1 n bt2 -> c_bangType bt1 >> matchN n >> c_bangType bt2
  RecDecl n nbts -> matchN n >> forM_ nbts (\(ns,bt) -> mapM_ matchN ns >> c_bangType bt)

c_bangType bt = case bt of
  BangedTy t -> c_type t
  UnBangedTy t -> c_type t
  UnpackedTy t -> c_type t

c_type typ = undefined
