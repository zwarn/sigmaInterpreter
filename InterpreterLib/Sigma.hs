{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Sigma where

import Algebras
import Functors
import SubType
import Control.Monad
 
type Value = SigmaObject
  
--instance Show Value where
--        show ((Left error, log), state) = show error
--        show ((Right term, log), state) = show term

type Name = String

data SigmaObject        = Object [FuncDef]
                                  
data FuncDef            = FuncDef (String, FuncBody) 

data FuncBody           = FuncBody String SigmaObject

data SigmaExpr a        = SExpr (Term a)
data Term a             = SObj SigmaObject
                        | Invocation a Name
                        | Override a Name FuncDef

instance Functor SigmaExpr where
        fmap f (SExpr term) = (SExpr (fmap f term))
         
instance Functor Term where
        fmap f x@(SObj object)                  = (SObj object)
        fmap f (Invocation term name)           = (Invocation (f term) name)
        fmap f (Override term name funcdef)     = (Override (f term) name funcdef)       
    
instance Algebra SigmaExpr AlgSigma a where
         apply alg x@(SExpr expr)          = (sigma alg x)
      
data AlgSigma t = AlgSigma   {sigma :: (SigmaExpr t) -> t}  

phiSigma :: SigmaExpr t -> t
phiSigma (SExpr (Invocation term name)) = term
phiSigma (SExpr (Override term name funcdef)) = term
phiSigma (SExpr (SObj object)) = object
                                         
type TermType = (SigmaExpr)
type TermLang = Fix TermType                                      

termAlg = (AlgSigma phiSigma) 
                
eval = cata termAlg

mkEObject v = inn $ sleft $ SExpr v

term1 = mkEObject (SObj (Object []))
  
sright = S . Right

sleft = S . Left  