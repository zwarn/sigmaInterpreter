{-# LANGUAGE TypeOperators, FlexibleInstances, MultiParamTypeClasses, DeriveFunctor #-}

module Sample2 where

import Prelude hiding (div)
import qualified Prelude (div)

import Algebras
import Functors
import SubType
import Control.Monad
import Control.Monad.Reader

-- nicer aliases
type Any = TermLang
type AnEConst = TermLang
type AnEAdd = TermLang
type AnEMul = TermLang
type AnEFun = TermLang

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

data ExprConst e = EConst Int
                   deriving (Show, Eq, Functor)

data AlgConst t = AlgC ((ExprConst t) -> t)

instance Algebra ExprConst AlgConst a where
    apply (AlgC f) x = f x

mkEConst ::   Int
         -> --------
            AnEConst

mkEConst = atEConst . EConst



data ExprAdd e = EAdd e e
               | ESub e e
               deriving (Show, Eq, Functor)

data AlgAdd t = AlgAdd
                { add :: (ExprAdd t) -> t
                , sub :: (ExprAdd t) -> t
                }

instance Algebra ExprAdd AlgAdd a where
    apply alg x = f alg x  where
     f = case x of
         (EAdd _ _) -> add
         (ESub _ _) -> sub

mkEAdd, mkESub :: Any -> Any
               -> ----------
                    AnEAdd

mkEAdd x y = atEAdd $ EAdd x y
mkESub x y = atEAdd $ ESub x y



data ExprMul e = EMul e e
               | EDiv e e
               deriving (Show, Eq, Functor)

data AlgMul t = AlgMul
                { mul :: (ExprMul t) -> t
                , div :: (ExprMul t) -> t
                }

instance Algebra ExprMul AlgMul a where
    apply alg x = f alg x  where
     f = case x of
         (EMul _ _) -> mul
         (EDiv _ _) -> div

mkEMul, mkEDiv :: Any -> Any
               -> ----------
                    AnEMul

mkEMul x y = atEMul $ EMul x y
mkEDiv x y = atEMul $ EDiv x y




data ExprFun t = ELam String TyValue t
               | EApp t t
               | EVar String
               deriving (Show, Eq, Functor)

data AlgFun t = AlgFun
                { lam :: ExprFun t -> t
                , app :: ExprFun t -> t
                , var :: ExprFun t -> t
                }

instance Algebra ExprFun AlgFun a where
    apply alg x = f alg x  where
     f = case x of
         (EApp _ _)   -> app
         (ELam _ _ _) -> lam
         (EVar _)     -> var

mkEVar :: String
       -> ------
          AnEFun

mkEVar x = atEFun $ EVar x

mkELam :: String -> TyValue -> Any
       -> ------------------------
                  AnEFun

mkELam x ty y = atEFun $ ELam x ty y

mkEApp :: Any -> Any
       -> ----------
            AnEFun

mkEApp x y = atEFun $ EApp x y

-- }}}

-- Ikebana (mashing it all together into one big blob) {{{

--{- stupid-simple linked list arrangement (simple to extend) {{{

type TermType   =     (ExprConst :$:       (ExprAdd :$:       (ExprMul :$: ExprFun)))
type TermLang   = Fix TermType

type AtEConst f = Fix (    f     :$:       (ExprAdd :$:       (ExprMul :$: ExprFun)))
atEConst        = inn .  sleft

type AtEAdd f   = Fix (ExprConst :$:       (   f    :$:       (ExprMul :$: ExprFun)))
atEAdd          = inn             . sright . sleft

type AtEMul f   = Fix (ExprConst :$:       (ExprAdd :$:       (   f    :$: ExprFun)))
atEMul          = inn             . sright           . sright . sleft

type AtEFun f   = Fix (ExprConst :$:       (ExprAdd :$:       (ExprMul :$:    f   )))
atEFun          = inn             . sright           . sright           . sright

makeAlg :: (ExprConst t -> t)
        -> ((ExprAdd t -> t),(ExprAdd t -> t))
        -> ((ExprMul t -> t),(ExprMul t -> t))
        -> ((ExprFun t -> t),(ExprFun t -> t),(ExprFun t -> t))
        -> SumAlgebra ExprConst (Sum ExprAdd (Sum ExprMul ExprFun)) t
makeAlg const (add,sub) (mul,div) (lam,app,var)
        = (AlgC const)
      @+@ (AlgAdd add sub)
      @+@ (AlgMul mul div)
      @+@ (AlgFun lam app var)

--} -- }}}

{- example tree variant [ const | [ [+|*] | fun ] ] (could build optimal tree) {{{

type TermType   =     (ExprConst :$:       (       (ExprAdd :$: ExprMul) :$: ExprFun)  )
type TermLang   = Fix TermType

type AtEConst f = Fix (    f     :$:       (       (ExprAdd :$: ExprMul) :$: ExprFun)  )
atEConst        = inn .  sleft

type AtEAdd   f = Fix (ExprConst :$:       (       (   f    :$: ExprMul) :$: ExprFun)  )
atEAdd          = inn             . sright . sleft . sleft

type AtEMul   f = Fix (ExprConst :$:       (       (ExprAdd :$:    f   ) :$: ExprFun)  )
atEMul          = inn             . sright . sleft           .  sright

type AtEFun   f = Fix (ExprConst :$:       (       (ExprAdd :$: ExprMul) :$:    f   )  )
atEFun          = inn             . sright                                .  sright

makeAlg :: (ExprConst t -> t)
        -> ((ExprAdd t -> t),(ExprAdd t -> t))
        -> ((ExprMul t -> t),(ExprMul t -> t))
        -> ((ExprFun t -> t),(ExprFun t -> t),(ExprFun t -> t))
        -> SumAlgebra ExprConst (Sum (Sum ExprAdd ExprMul) ExprFun) t
makeAlg const (add,sub) (mul,div) (lam,app,var)
        = (AlgC const)
      @+@ ( (AlgAdd add sub) @+@ (AlgMul mul div) )
      @+@ (AlgFun lam app var)

--} -- }}}

-- }}}

-- first variant : "normal" value evaluation {{{

-- values {{{

type ValueMonad = EnvOf Value

data Value = ValNum Int
           | ValLam (ValueMonad -> ValueMonad)

instance Show Value where
    show (ValNum x) = show x
    show (ValLam _) = "<Function Value>"

valBinop :: (Int -> Int -> Int) -> (Value -> Value -> Value)
valBinop f (ValNum x) (ValNum y) = ValNum (f x y)

-- }}}

evalVal = runReader . (cata termValAlg)

termValAlg = makeAlg doConst (doAdd,doSub) (doMul,doDiv) (doLam,doApp,doVar)
  where -- doFoos are defined as follows... {{{

    doConst :: Monad m => ExprConst t -> m Value
    doConst (EConst x) = return (ValNum x)

    doAdd, doSub :: Monad m => ExprAdd (m Value) -> m Value
    doAdd (EAdd x1 x2) = liftM2 (valBinop (+)) x1 x2
    doSub (ESub x1 x2) = liftM2 (valBinop (-)) x1 x2

    doMul, doDiv :: Monad m => ExprMul (m Value) -> m Value
    doMul (EMul x1 x2) = liftM2 (valBinop (*))         x1 x2
    doDiv (EDiv x1 x2) = liftM2 (valBinop Prelude.div) x1 x2

    doLam (ELam s _ term) = do
        env <- ask
        return . ValLam $ \v -> do
            v' <- v
            withExtraBinding (s, v') env $ do
                term

    doApp (EApp f x) = do
        f' <- f
        case f' of
            (ValLam f) -> (f x)
            _             -> error "Cannot apply non-lambda value."

    doVar (EVar s) = do
        v <- asks (lookup s)
        case v of
            (Just x) -> return x
            Nothing  -> error "Variable not found."
    -- }}}

-- }}}

-- second variant : parity (odd/even) eval {{{

-- Parity(Odd,Even), ~+~, ~*~, alpha {{{

data Parity = Odd | Even deriving (Show,Eq)

(~+~) :: Parity -> Parity -> Parity
x ~+~ y | x == y    = Even
        | otherwise = Odd

(~*~) :: Parity -> Parity -> Parity
Odd ~*~ Odd = Odd
_   ~*~ _   = Even

alpha :: Int -> Parity
alpha x = if (odd x) then Odd else Even

-- }}}

-- values {{{

type ParValueMonad = EnvOf ParValue

data ParValue = ParNum Parity
              | ParLam (ParValueMonad -> ParValueMonad)

instance Show ParValue where
    show (ParNum v) = show v
    show (ParLam _) = "<Parity Function Value>"

instance Eq ParValue where
    (==) (ParNum x) (ParNum y) = (x == y)
    (==) (ParLam x) (ParLam y) = error "Cannot compare functions."

parBinop :: (Parity -> Parity -> Parity) -> (ParValue -> ParValue -> ParValue)
parBinop f (ParNum x) (ParNum y) = ParNum (f x y)

-- }}}

evalPar = runReader . (cata termParAlg)

termParAlg = makeAlg doConst (doAdd,doSub) (doMul,doDiv) (doLam,doApp,doVar)
  where -- doFoos are defined as follows... {{{

    doConst :: Monad m => ExprConst t -> m ParValue
    doConst (EConst x) = return . ParNum $ alpha x

    doAdd, doSub :: Monad m => ExprAdd (m ParValue) -> m ParValue
    doAdd (EAdd x1 x2) = liftM2 (parBinop (~+~)) x1 x2
    doSub (ESub x1 x2) = liftM2 (parBinop (~+~)) x1 x2

    doMul, doDiv :: Monad m => ExprMul (m ParValue) -> m ParValue
    doMul (EMul x1 x2) = liftM2 (parBinop (~*~)) x1 x2
    doDiv (EDiv x1 x2) = liftM2 (parBinop (~*~)) x1 x2

    doLam (ELam s _ term) = do
        env <- ask
        return . ParLam $ \v -> do
            v' <- v
            withExtraBinding (s, v') env $ do
                term

    doApp (EApp f x) = do
        f' <- f
        case f' of
            (ParLam f) -> (f x)
            _             -> error "Cannot apply non-lambda value."

    doVar (EVar s) = do
        v <- asks (lookup s)
        case v of
            (Just x) -> return x
            Nothing  -> error "Variable not found."
    -- }}}

-- }}}

-- third variant : type check {{{

-- values {{{

type TyMonad = EnvOf TyValue

data TyValue = TyInt
             | TyValue :->: TyValue
             deriving (Eq, Show)

tyBinop :: String -> (TyValue -> TyValue -> TyValue)
tyBinop mname = check
    where
        check TyInt      TyInt      = TyInt
        check (_ :->: _) _          = error message
        check _          (_ :->: _) = error message
        message = "Attempt to " ++ mname ++ " a function value."

-- }}}

typeof = runReader . (cata tyAlg)

tyAlg = makeAlg doConst (doAdd,doSub) (doMul,doDiv) (doLam,doApp,doVar)
  where -- doFoos are defined as follows... {{{

    doConst :: Monad m => ExprConst t -> m TyValue
    doConst (EConst x) = return TyInt

    doAdd, doSub :: Monad m => ExprAdd (m TyValue) -> m TyValue
    doAdd (EAdd x1 x2) = liftM2 (tyBinop "`add") x1 x2
    doSub (ESub x1 x2) = liftM2 (tyBinop "`sub") x1 x2

    doMul, doDiv :: Monad m => ExprMul (m TyValue) -> m TyValue
    doMul (EMul x1 x2) = liftM2 (tyBinop "`mul") x1 x2
    doDiv (EDiv x1 x2) = liftM2 (tyBinop "`div") x1 x2

    doLam (ELam s ty term) = do
        env <- ask
        ty' <- withExtraBinding (s, TyInt) env $ do
                term
        return $ ty :->: ty'

    doApp (EApp f x) = do
        tyf <- f
        tyx <- x
        case tyf of
            (ty :->: ty') | ty == tyx -> return ty'
                          | otherwise -> error "Ill-typed application."
            _            -> error "Cannot apply non-lambda value."

    doVar (EVar s) = do
        v <- asks (lookup s)
        case v of
            (Just x) -> return x
            Nothing  -> error "Variable not found."
    -- }}}

-- }}}

-- soundness check {{{

soundTest algA algB f term = do
    x  <- cata algA term
    x' <- cata algB term
    return $ alpha x == x'

sound term = let
    v = evalVal term []
    w = evalPar term []
  in case (v, w) of
    (ValNum a, ParNum b) -> alpha a == b
    (ValLam a, ParLam b) -> error "Cannot compare functions."
    _                    -> False

-- }}}

-- examples {{{

infixl 9 <:
infixr 0 -->
(<:) :: String            -> TyValue -> (String, TyValue)
(<:) = (,)
(-->) :: (String, TyValue) -> Any     -> Any
(-->) = uncurry mkELam
(@@) = mkEApp

ex_x = mkEVar "x"
ex_y = mkEVar "y"

ex_f = "x" <: TyInt --> mkEAdd ex_x ex_1
ex_g = "x" <: TyInt --> "y" <: TyInt --> mkEMul ex_x (mkEMul (mkEAdd ex_x ex_1) ex_y)

ex_1 = mkEConst 1
ex_2 = mkEAdd ex_1 ex_1
ex_3 = mkEAdd ex_1 ex_2
ex_4 = mkEMul ex_2 ex_2
ex_5 = mkESub ex_4 (mkEAdd ex_2 ex_2)
ex_6 = mkEDiv ex_4 ex_4
ex_7 = ex_f @@ ex_4
ex_8 = ex_g @@ ex_7 @@ ex_6

expected = [
  (ex_1, 1),
  (ex_2, 2),
  (ex_3, 3),
  (ex_4, 4),
  (ex_5, 0),
  (ex_6, 1),
  (ex_7, 5),
  (ex_8, 30)
  ]

doTest test = sequence_ $ map (putStrLn . test) expected
testVal = doTest vtest
testPar = doTest ptest
testTyp = doTest ttest

vtest (tm, r) = let
    result = evalVal tm []
  in case result of
    (ValNum r') | r == r' -> "OK"
    _ -> (show result) ++ " != " ++ show r

ptest (tm, r) = let
    result = evalPar tm []
  in case result of
    (ParNum r') | (alpha r) == r' -> "OK"
    _ -> (show result) ++ " != " ++ show (alpha r)

ttest (tm, _) = let
    result = typeof tm []
  in case result of
    TyInt -> "OK"
    _ -> (show result) ++ " != " ++ "TyInt"

-- }}}

-- old {{{
term1 = mkEConst 1
term2 = mkEAdd term1 term1
term3 = mkEMul term2 term2
term4 = mkESub term1 term1
term5 = mkEDiv term1 term1
term6 = mkEVar "x"
term7 = mkELam "x" TyInt term6
term8 = mkEApp term7 term1
term9 = mkELam "x" TyInt (mkEAdd term6 term6)
term10 = mkEApp term9 term1
term11 = mkELam "x" TyInt (mkELam "y" TyInt (mkEAdd term1 term1))
term12 = mkEApp (mkEApp term11 term1) term1
-- }}}