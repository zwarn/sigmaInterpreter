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

data ObjectExpr a       = ObjectExpr a

instance Functor ObjectExpr where
         fmap f (ObjectExpr o) = (ObjectExpr (f o))
    
instance Algebra ObjectExpr AlgObject a where
         apply alg x@(ObjectExpr _)          = (object alg x)
      
data AlgObject t = AlgObject   {object         :: (ObjectExpr t) -> t}  

phiObject :: ObjectExpr t -> t
phiObject (ObjectExpr o) = o

data FuncExpr a         = Invocation a Name
                        | Override a Name FuncBody
                        
instance Functor FuncExpr where
        fmap f (Invocation term name)           = (Invocation (f term) name)
        fmap f (Override term name funcbody)    = (Override (f term) name funcbody)
        
instance Algebra FuncExpr AlgFunc a where
        apply alg x@(Invocation _ _) = invocation alg x
        apply alg x@(Override _ _ _) = override alg x
        
data AlgFunc t = AlgFunc        {invocation :: (FuncExpr t) -> t,
                                 override   :: (FuncExpr t) -> t}
                                 
phiInvocation :: (FuncExpr t) -> t
phiInvocation (Invocation term name) = term

phiOverride :: (FuncExpr t) -> t
phiOverride (Override term name funcbody) = term

                                         
type TermType = (ObjectExpr :$: FuncExpr)
type TermLang = Fix TermType                                      

termAlg = (AlgObject phiObject) 
                @+@ (AlgFunc phiInvocation phiOverride)
                
eval = cata termAlg

mkEObject v = inn $ sleft $ ObjectExpr v

term1 = mkEObject (Object [])              
  
sright = S . Right

sleft = S . Left  