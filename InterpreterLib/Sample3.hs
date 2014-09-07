{-# LANGUAGE TypeOperators, FlexibleInstances, MultiParamTypeClasses, DeriveFunctor #-}

module Sample3 where

import Prelude hiding (div)
import qualified Prelude (div)

import Algebras
import Functors
import SubType
import Control.Monad
import Control.Monad.Reader

-- nicer aliases
type Any = TermLang
type AnESigma = TermLang

sright = S . Right
sleft  = S . Left

-- variables {{{

type EnvOf value = Reader [(String, value)] value

-- from Reader:
-- lookup :: Eq a => a -> [(a, b)] -> Maybe b

-- add extra binding while evaluating a (sub-)term
-- withExtraBinding :: MonadReader [binding] m => binding -> [binding] -> m a -> m a
withExtraBinding bind env = (local . const $ bind:env)

-- }}}

-- actual definitions {{{

type Name = String

data SigmaObject a       = Object [FuncDef a]
                          deriving (Show, Eq, Functor)
                                  
data FuncDef a           = FuncDef (String, FuncBody a)
                          deriving (Show, Eq, Functor) 

data FuncBody a          = FuncBody String a
                          deriving (Show, Eq, Functor)

data SigmaExpr a = SExpr (Term a)
                   deriving Functor
data Term a      = SObj (SigmaObject a)
                 | Invocation a Name
                 | Override a Name (FuncDef a)
                   deriving (Show, Eq, Functor)
    
data AlgSigma t = AlgSigma
                { object :: SigmaExpr t -> t
                , invocation :: SigmaExpr t -> t
                , override :: SigmaExpr t -> t
                }

instance Algebra SigmaExpr AlgSigma a where
    apply alg x = f alg x  where
     f = case x of
         SExpr (SObj _)               -> object
         SExpr (Invocation _ _)       -> invocation
         SExpr (Override _ _ _)       -> override

type TermType   =     (SigmaExpr :$: SigmaExpr)
type TermLang   = Fix TermType

type AtESigma f = Fix (    f   )
atESigma        = inn .  sleft

makeAlg (object, invocation, override)
        = (AlgSigma object invocation override)

type ValueMonad = EnvOf Value

data Value = SigmaObject
        deriving Show

evalVal = runReader . (cata termValAlg)

termValAlg = makeAlg (doObject, doInvocation, doOverride)
  where -- doFoos are defined as follows... {{{

    doObject :: Monad m => SigmaExpr t -> m Value
    doObject (SExpr (SObj object)) = return (object)
    
    doInvocation :: Monad m => SigmaExpr t -> m Value
    doInvocation (SExpr (Invocation term name)) = do object <- term
                                                     return (object)
    
    doOverride :: Monad m => SigmaExpr t -> m Value
    doOverride (SExpr (Override term name funcdef)) = return (term)
    
    
 