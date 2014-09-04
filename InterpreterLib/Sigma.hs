{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Sigma where

import Algebras
import Functors
import SubType
import Control.Monad
 
--type Value = ResultType Term
  
--instance Show Value where
--        show ((Left error, log), state) = show error
--        show ((Right term, log), state) = show term

type Name = String
data ExprSigma e = Object [FuncDef e]
                 | Var Name
                 | Invocation e Name
                 | Override e Name (FuncBody e)
                 
data FuncDef e = FuncDef (String, FuncBody e) 

data FuncBody e = FuncBody String e    

instance Functor ExprSigma where
    fmap f (Invocation term name) = (Invocation (f term) name)
    fmap f (Override term name funcbody) = (Override (f term) name funcbody)
    fmap f x = x
    
instance Algebra ExprSigma AlgSigma a where
    apply alg x@(Object _)              = (object alg x)
    apply alg x@(Var _)                 = (lookupVar alg x)
    apply alg x@(Invocation _ _)        = (invocation alg x)
    apply alg x@(Override _ _ _)        = (override alg x)
      
data AlgSigma t = AlgSigma     {object         :: (ExprSigma t) -> t,
                                lookupVar      :: (ExprSigma t) -> t,  
                                invocation     :: (ExprSigma t) -> t,  
                                override       :: (ExprSigma t) -> t}  
  
sright = S . Right

sleft = S . Left  