{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import Language.Haskell.Exts
import System.Environment
import Text.Groom
import           Control.Applicative
import           Control.Monad.Error
import           Control.Monad.Identity (Identity)
import           Control.Monad.State
--import           Control.Monad.IO
import           Data.String
import           Language.Haskell.Exts

data CompileState = CompileState
  { searchString :: String
  , stateLoc :: [SrcLoc]
  , finds :: [[SrcLoc]]
  } deriving (Show)

data CompileError = CompileError
  deriving (Show)
instance Error CompileError

newtype Compile a = Compile { unCompile :: StateT CompileState (ErrorT CompileError IO) a }
  deriving (MonadState CompileState
           ,MonadError CompileError
           ,MonadIO
           ,Monad
           ,Functor
           ,Applicative)

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
      case finds res of
        [] -> putStrLn "No matches"
        fs -> forM_ fs $ \(SrcLoc fn l c:_) -> putStrLn $ fn ++ ":" ++ show l ++ ":" ++ show c

tryMatch :: String -> Compile ()
tryMatch name = do
  s <- gets searchString
  loc <- gets stateLoc
  when (name == s) $
    modify $ \s -> s { finds = loc : finds s }

tryMatchN :: Name -> Compile ()
tryMatchN name = case name of
  Ident n -> tryMatch n
  Symbol n -> tryMatch n

tryMatchQ :: QName -> Compile ()
tryMatchQ name = case name of
  Qual _ n -> tryMatchN n
  UnQual n -> tryMatchN n

tryMatchC :: CName -> Compile ()
tryMatchC c = case c of
  VarName n -> tryMatchN n
  ConName n -> tryMatchN n

c_module :: Module -> Compile ()
c_module (Module loc (ModuleName name) _pragmas _wt expspec importdecls decls) = do
  withLoc loc $ do
    tryMatch name
    maybe (return ()) (mapM_ c_exportSpec) expspec
    mapM_ c_importDecl importdecls
    mapM_ c_decl decls

c_exportSpec :: ExportSpec -> Compile ()
c_exportSpec es = case es of
  EVar n -> tryMatchQ n
  EAbs n -> tryMatchQ n
  EThingAll n -> tryMatchQ n
  EThingWith n cns -> tryMatchQ n >> mapM_ tryMatchC cns
  EModuleContents (ModuleName m) -> tryMatch m

c_importDecl :: ImportDecl -> Compile ()
c_importDecl _ = return ()

c_decl :: Decl -> Compile ()
c_decl _ = return ()
