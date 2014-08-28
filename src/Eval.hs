module Eval where

import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe
import qualified Data.Map as Map

import Model
import MonadStack

eval :: Term -> Eval Term
eval (Object o) = do
                        tell [show (Object o)]
                        return $ Object o
eval (Var n)    = do 
                        env <- ask
                        tell [show (Var n)]
                        case Map.lookup n env of
                                Nothing -> throwError ("evaluating unbound variable " ++ n)
                                Just val -> return val
  
eval (Override term name funcBody) = do 
                                        tell [show (Override term name funcBody)]
                                        object <- eval term
                                        replaceFuncBody object name funcBody
eval (Invocation term name) = do 
                                 tell [show (Invocation term name)]
                                 object <- eval term
                                 let FuncBody selfname funcbody = getFuncBodyFromObject object name
                                 result <- eval ( substituteInTerm selfname term funcbody)
                                 return result
                                                                           
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
                                                                     
                                      
evaluate :: Term -> ResultType Term
evaluate t = runEval newReader newState (eval t)
