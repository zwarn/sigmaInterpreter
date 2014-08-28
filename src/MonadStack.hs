module MonadStack where

import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe
import qualified Data.Map as Map

import Model

type StateType = Env
newState :: StateType
newState = Map.fromList [("a",example1), ("b",example2), ("c",example3)]
type ReaderType = Env
newReader :: ReaderType
newReader = Map.fromList [("a",example1), ("b",example2), ("c",example3)]
type ErrorType = String
newError :: ErrorType
newError = ""
type WriterType = [String]
newWriter :: WriterType
newWriter = []

type Eval a = ReaderT ReaderType 
              (ErrorT ErrorType
              (WriterT WriterType
              (StateT StateType Identity))) a
              
type Env = Map.Map Name Term

type ResultType a = ((Either ErrorType a, WriterType), StateType)

runEval :: ReaderType -> StateType -> Eval a -> ResultType a
runEval env st ev = runIdentity (runStateT (runWriterT (runErrorT (runReaderT ev env))) st)

example1 = Object [FuncDef ("s" , FuncBody "self" (Object []))]
example2 = Var "a"
example3 = Override (Object [FuncDef ("s" , FuncBody "self" (Object []))]) "s" (FuncBody "selfname" (Object[])) 
example4 = Invocation (Override (Object [FuncDef ("s" , FuncBody "self" (Object []))]) "s" (FuncBody "selfname" (Object[]))) "s" 
