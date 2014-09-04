{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Functors where

infixr 5 :$:

newtype Fix f = In (f (Fix f))
inn = In
out (In x) = x

newtype Sum f g x = S (Either (f x) (g x))
unS (S x) = x
type x :$: y = Sum x y 

instance (Functor f, Functor g) => Functor (Sum f g) 
 where fmap h  (S (Left x))  = S (Left  $ fmap h x)
       fmap h  (S (Right x)) = S (Right $ fmap h x)

class SubFunctor f g where 
    injF :: f x -> g x
    prjF :: g x -> Maybe (f x)

instance SubFunctor f f where 
    injF f = f
    prjF = Just

instance SubFunctor f (Sum f x) where
    injF               = S . Left
    prjF (S (Left f))  = Just f
    prjF (S (Right x)) = Nothing

instance ( SubFunctor f g) => SubFunctor f (Sum x g) where
    injF               = S . Right . injF
    prjF (S (Left x))  = Nothing
    prjF (S (Right b)) = prjF b

toS :: (SubFunctor f g, Functor g) => f (Fix g) -> Fix g
toS x = inn $ injF x

--mkTerm0 = toS
mkTerm  f = toS . f
mkTerm2 f = curry $ toS . (uncurry f)
mkTerm3 f = curry $ curry $ toS . (uncurry (uncurry f))

class ZipFunctor f where
  zipFunctor :: Monad m => (a -> b -> c) -> f a -> f b -> m (f c)
