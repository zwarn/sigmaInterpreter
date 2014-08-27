module Sigma where

import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe
import qualified Data.Map as Map

type Name = String
data Term = Object [FuncDef]
          | Var Name
          | Invocation Term Name
          | Override Term Name FuncBody
          deriving Show
          
data FuncDef = FuncDef (String, FuncBody)
             deriving Show   

--substituteDef :: FuncDef -> Name -> Term a -> FuncDef
--substituteDef FuncDef (name, funcBody) toReplace newTerm = FuncDef (name, substituteBody funcBody toReplace newTerm)

data FuncBody = FuncBody String Term
              deriving Show
              
--substituteBody :: FuncBody -> Name -> Term a -> FuncBody
--TODO if selfname==toReplace then substitute selfname
--substituteBody (FuncBody selfname term) toReplace newTerm = FuncBody selfname substitute term toReplace newTerm 
              
type Env = Map.Map Name Term
type StateType = Env
newState :: StateType
newState = getEnv
type ReaderType = Env
newReader :: ReaderType
newReader = getEnv
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

runEval :: Env -> StateType -> Eval a -> ((Either ErrorType a, WriterType), StateType)
runEval env st ev = runIdentity (runStateT (runWriterT (runErrorT (runReaderT ev env))) st)

eval :: Term -> Eval Term
eval (Object o) = do
                        tell ["Object!"]
                        return $ Object o
eval (Var n)    = do 
                        env <- ask
                        tell ["Var!"]
                        case Map.lookup n env of
                                Nothing -> throwError ("evaluating unbound variable " ++ n)
                                Just val -> return val
  
eval (Override term name funcBody) = do 
                                        tell ["Override!"]
                                        object <- eval term
                                        replaceFuncBody object name funcBody
eval (Invocation term name) = do 
                                 tell ["Invocation!"]
                                 object <- eval term
                                 let FuncBody selfname funcbody = getFuncBodyFromObject object name
                                 return $ substituteInTerm selfname term funcbody
                                                                           
substituteInFuncBody ::Name -> Term -> FuncBody -> FuncBody
substituteInFuncBody toBeReplaced replaceWith (FuncBody selfname body) = (FuncBody selfname newbody)
                                                                         -- TODO substitute selfname for unused variable  
                                                                         where newbody = substituteInTerm toBeReplaced replaceWith body
                                                                         
substituteInFuncDef ::Name -> Term -> FuncDef -> FuncDef
substituteInFuncDef toBeReplaced replaceWith (FuncDef (name, body)) = FuncDef (name, newBody)
                                                                      where newBody = substituteInFuncBody toBeReplaced replaceWith body

substituteInTerm :: Name -> Term -> Term ->Term
substituteInTerm toBeReplaced replaceWith (Object funcdefs) = Object (map (substituteInFuncDef toBeReplaced replaceWith) funcdefs)
substituteInTerm toBeReplaced replaceWith (Var n)  = if n == toBeReplaced
                                                     then replaceWith
                                                     else (Var n)
substituteInTerm toBeReplaced replaceWith (Invocation term name) = (Invocation newTerm name)
                                                                   where newTerm = substituteInTerm toBeReplaced replaceWith term
substituteInTerm toBeReplaced replaceWith (Override term name funcbody) = (Override newTerm name newFuncbody)
                                                                        where newTerm = substituteInTerm toBeReplaced replaceWith term
                                                                              newFuncbody = substituteInFuncBody toBeReplaced replaceWith funcbody                                                                      

replaceFuncBody :: Term -> Name -> FuncBody -> Eval Term
replaceFuncBody (Object funcBodys) funcName funcBody   = return $ Object (map (replaceFunction funcName funcBody) funcBodys) 

replaceFunction :: Name -> FuncBody -> FuncDef -> FuncDef
replaceFunction funcname funcBody (FuncDef (name, body)) = FuncDef (if funcname == name 
                                                                    then (name, funcBody)
                                                                    else (name, body))
                             
getFuncBodyFromObject :: Term -> Name -> FuncBody
getFuncBodyFromObject (Object (FuncDef (funcName, body):fds)) name = if (funcName == name)
                                                                     then body
                                                                     else getFuncBodyFromObject (Object fds) name
                                                                     
                                                


exampleTerm1 = Object [FuncDef ("s" , FuncBody "self" (Object []))]
exampleTerm2 = Var "a"
exampleTerm3 = Override (Object [FuncDef ("s" , FuncBody "self" (Object []))]) "s" (FuncBody "selfname" (Object[])) 
exampleTerm4 = Invocation (Override (Object [FuncDef ("s" , FuncBody "self" (Object []))]) "s" (FuncBody "selfname" (Object[]))) "s" 

execute t = runEval newReader newState (eval t)

getEnv :: Env
getEnv = Map.fromList [("a",exampleTerm1), ("b",exampleTerm2), ("c",exampleTerm3)]


