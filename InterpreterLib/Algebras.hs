{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Algebras where

import Functors
import Control.Monad(liftM, liftM2)
import SubType

infixr 5 @+@

type AlgSig f a = f a -> a

class Functor f => Algebra f alg a | alg -> f where
  apply :: alg a -> f a -> a

class Algebra f alg a => AlgebraBuilder f fType alg a | fType -> f, fType -> a, fType -> alg where
  mkAlgebra :: fType -> (alg a)

cata alg = (apply alg) . (fmap (cata alg)) . out

pairAlg a1 a2 = mkAlgebra pa
  where pa term = (((apply a1) . (fmap fst)) term, ((apply a2) . (fmap snd)) term)

sumAlg a1 a2 = SumAlgebra {left = sumAlg',
                           right = sumAlg'}
  where sumAlg' (S (Left x)) = apply a1 x
        sumAlg' (S (Right x)) = apply a2 x

(@+@) a b = sumAlg a b

data SumAlgebra f g a = SumAlgebra {left :: Sum f g a -> a,
                                    right :: Sum f g a -> a}


instance (Functor f, Functor g) => Algebra (Sum f g) (SumAlgebra f g) a where
  apply alg t@(S (Left _)) = left alg t
  apply alg t@(S (Right _)) = right alg t
  

instance (Functor f, Functor g) => 
  AlgebraBuilder (Sum f g) (Sum f g a -> a) (SumAlgebra f g) a where
  mkAlgebra f = SumAlgebra f f
