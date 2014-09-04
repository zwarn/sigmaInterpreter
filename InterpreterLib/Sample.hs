{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Sample where

  import Algebras
  import Functors
  import SubType
  import Control.Monad
  import Control.Monad.Reader

  data Value
      = ValNum Int
      | ValLambda (ValueMonad -> ValueMonad)
  
  instance Show Value where
      show (ValNum x) = show x
      show (ValLambda _) = "<Function Value>"

  data AlgConst t = AlgC ((ExprConst t) -> t)

  data ExprConst e = EConst Int
                     deriving (Show,Eq)

  instance Functor ExprConst where
      fmap f (EConst x) = EConst x

  instance Algebra ExprConst AlgConst a where
      apply (AlgC f) x@(EConst _) = (f x)

  mkEConst = inn . sleft . EConst

  data AlgAdd t = AlgAdd {add :: (ExprAdd t) -> t,
                          sub :: (ExprAdd t) -> t}

  data ExprAdd e = EAdd e e
                 | ESub e e
                   deriving (Show,Eq)
                               
  instance Functor ExprAdd where
      fmap f (EAdd x y) = (EAdd (f x) (f y))
      fmap f (ESub x y) = (ESub (f x) (f y))

  instance Algebra ExprAdd AlgAdd a where
      apply alg x@(EAdd _ _) = (add alg x)
      apply alg x@(ESub _ _) = (sub alg x)

  mkEAdd x y = inn $ sright $ sleft $ EAdd x y
  mkESub x y = inn $ sright $ sleft $ ESub x y 

  data AlgMult t = AlgMult {mult :: (ExprMult t) -> t,
                            divi :: (ExprMult t) -> t}

  data ExprMult e = EMult e e
                  | EDiv e e
                    deriving (Show,Eq)
                   
  instance Functor ExprMult where
      fmap f (EMult x y) = (EMult (f x) (f y))
      fmap f (EDiv x y) = (EDiv (f x) (f y))

  instance Algebra ExprMult AlgMult a where
      apply alg x@(EMult _ _) = (mult alg x)
      apply alg x@(EDiv _ _) = (divi alg x)

  mkEMult x y = inn $ sright $ sright $ sleft $ EMult x y
  mkEDiv x y = inn $ sright $ sright $ sleft $ EDiv x y

  data ExprFun t
      = ELambda String TyValue t
      | EApp t t
      | EVar String
        deriving (Show,Eq)

  data AlgFun t = AlgFun {lam :: ExprFun t -> t,
                          app :: ExprFun t -> t,
                          var :: ExprFun t -> t}

  instance Functor ExprFun where
      fmap f (ELambda s ty t) = ELambda s ty (f t)
      fmap f (EApp t1 t2) = EApp (f t1) (f t2)
      fmap f (EVar s) = (EVar s)
  
  instance Algebra ExprFun AlgFun a where
      apply alg x@(EApp _ _) = (app alg x)
      apply alg x@(ELambda _ _ _) = (lam alg x)
      apply alg x@(EVar _) = (var alg x)

  mkEVar x = inn $ sright $ sright $ sright $ EVar x
  mkELambda x ty y = inn $ sright $ sright $ sright $ ELambda x ty y
  mkEApp x y = inn $ sright $ sright $ sright $ EApp x y

  type TermType = (ExprConst :$: (ExprAdd :$: (ExprMult :$: ExprFun)))

  type TermLang = Fix TermType

  type ValueMonad = Reader Env Value

  data Env = Env {variables::[(String,Value)]}

  lookupVal name env = lookup name (variables env)

  addVal b env = Env {variables=b:(variables env)}

  phiConst (EConst x) = return (ValNum x)

  vPlus (ValNum x) (ValNum y) = ValNum (x + y)
  vSub (ValNum x) (ValNum y) = ValNum (x - y)

  phiAdd (EAdd x1 x2) = liftM2 vPlus x1 x2
  phiSub (ESub x1 x2) = liftM2 vSub x1 x2

  vMult (ValNum x) (ValNum y) = ValNum (x * y)
  vDiv (ValNum x) (ValNum y) = ValNum ((div) x y)

  phiMult (EMult x1 x2) = liftM2 vMult x1 x2
  phiDiv (EDiv x1 x2) = liftM2 vDiv x1 x2

  phiLambda (ELambda s _ t) =
      do { env <- ask
         ; return $ ValLambda (\v -> (do { v' <- v
                                         ; (local (const (addVal (s,v') env)) t)
                                         }))}
  phiApp (EApp x1 x2) =
      do { x1' <- x1
         ; case x1' of
           (ValLambda f) -> (f x2)
           _ -> error "Cannot apply non-lambda value"
         }
  phiVar (EVar s) = do { v <- asks (lookupVal s)
                       ; case v of
                         (Just x) -> return x
                         Nothing -> error "Variable not found"
                       }

  termAlg = (AlgC phiConst)
            @+@ (AlgAdd phiAdd phiSub)
            @+@ (AlgMult phiMult phiDiv)
            @+@ (AlgFun phiLambda phiApp phiVar)

  evalFun = runReader . (cata termAlg)

  data OE = Odd | Even deriving (Show,Eq)
 
  oePlus :: OE -> OE -> OE
  oePlus Odd Odd = Even
  oePlus Odd Even = Odd
  oePlus Even Odd = Odd
  oePlus Even Even = Even

  oeTimes :: OE -> OE -> OE
  oeTimes Odd Odd = Odd
  oeTimes Odd Even = Even
  oeTimes Even Odd = Even
  oeTimes Even Even =  Even

  data AbsValue
      = AbsValNum OE
      | AbsValLambda (AbsValueMonad -> AbsValueMonad)

  instance Show AbsValue where
      show (AbsValNum v) = show v
      show (AbsValLambda _) = "<Abstract Function Value>"

  instance Eq AbsValue where
      (==) (AbsValNum x) (AbsValNum y) = (x == y)
      (==) (AbsValLambda x) (AbsValLambda y) = error "Cannot compare functions."

  type AbsValueMonad = Reader AbsEnv AbsValue

  data AbsEnv = AbsEnv {absVariables::[(String,AbsValue)]}

  lookupAbsVal name env = lookup name (absVariables env)

  addAbsVal b env = AbsEnv {absVariables=b:(absVariables env)}

  alpha x = AbsValNum $ if (odd x) then Odd else Even

  phi1Const (EConst x) = return (alpha x)

  aPlus (AbsValNum x) (AbsValNum y) = AbsValNum (oePlus x y)
  phi1Add (EAdd x1 x2) = liftM2 aPlus x1 x2
  phi1Sub (ESub x1 x2) = liftM2 aPlus x1 x2

  aTimes (AbsValNum x) (AbsValNum y) = AbsValNum (oeTimes x y)
  phi1Mult (EMult x1 x2) = liftM2 aTimes x1 x2 
  phi1Div (EDiv x1 x2) = liftM2 aTimes x1 x2 

  phi1Lambda (ELambda s _ t) =
      do { env <- ask
         ; return $ AbsValLambda (\v -> (do { v' <- v
                                            ; (local (const (addAbsVal (s,v') env)) t)
                                            }))}

  phi1App (EApp x1 x2) =
      do { x1' <- x1
         ; case x1' of
           (AbsValLambda f) -> (f x2)
           _ -> error "Cannot apply non-lambda value"
         }

  phi1Var (EVar s) = do { v <- asks (lookupAbsVal s)
                       ; case v of
                         (Just x) -> return x
                         Nothing -> error "Variable not found"
                       }

  term1Alg = (AlgC phi1Const)
           @+@ (AlgAdd phi1Add phi1Sub)
           @+@ (AlgMult phi1Mult phi1Div)
           @+@ (AlgFun phi1Lambda phi1App phi1Var)

  evalPar = runReader . (cata term1Alg)

  data TyValue
      = TyInt
      | TyValue :->: TyValue
        deriving (Eq,Show)

  data Gamma = Gamma {gamma::[(String,TyValue)]}

  lookupTy name gam = lookup name (gamma gam)

  addBinding b gam = Gamma {gamma=b:(gamma gam)}

  type TyMonad = Reader Gamma TyValue

  tyConst (EConst x) = return TyInt

  tPlus TyInt TyInt = TyInt
  tPlus (_:->:_) _ = error "Cannot add function value"
  tPlus _ (_:->:_) = error "Cannot add function value"

  tSub TyInt TyInt = TyInt
  tSub (_:->:_) _ = error "Cannot subtract function value"
  tSub _ (_:->:_) = error "Cannot subtract function value"

  tyAdd (EAdd x1 x2) = liftM2 tPlus x1 x2
  tySub (ESub x1 x2) = liftM2 tSub x1 x2

  tMult TyInt TyInt = TyInt
  tMult (_:->:_) _ = error "Cannot multiply function value"
  tMult _ (_:->:_) = error "Cannot multiply function value"

  tDiv TyInt TyInt = TyInt
  tDiv (_:->:_) _ = error "Cannot divide function value"
  tDiv _ (_:->:_) = error "Cannot divide function value"

  tyMult (EMult x1 x2) = liftM2 tMult x1 x2
  tyDiv (EDiv x1 x2) = liftM2 tDiv x1 x2

  tyLambda (ELambda s ty t) =
      do { g <- ask
         ; t' <- (local (const (addBinding (s,TyInt) g)) t)
         ; return (ty :->: t')
         }

  tyApp (EApp x1 x2) =
      do { x1' <- x1
         ; x2' <- x2
         ; case x1' of
           (t1 :->: t2) -> if (t1 == x2')
                           then (return t2)
                           else (error "Input parameter of wrong type")
           _ -> error "Cannot apply non-lambda value"
         }

  tyVar (EVar s) = do { v <- asks (lookupTy s)
                        ; case v of
                        (Just x) -> return x
                        Nothing -> error "Variable not found"
                      }

  tyAlg = (AlgC tyConst)
            @+@ (AlgAdd tyAdd tySub)
            @+@ (AlgMult tyMult tyDiv)
            @+@ (AlgFun tyLambda tyApp tyVar)

  typeof = runReader . (cata tyAlg)

  soundTest c a alpha x = do { x' <- cata c x
                             ; x'' <- cata a x
                             ; return (x'' == (alpha x'))
                             }

  sound x = case v of
            (ValNum a)  -> case av of
                           c@(AbsValNum b) -> alpha a == c
                           _ -> False
            (ValLambda _) -> case av of
                             (AbsValLambda _) -> error "Cannot compare functions"
                             _ -> False
      where v=(evalFun x Env {variables=[]});
            av=(evalPar x AbsEnv {absVariables=[]})

  sright = S . Right

  sleft = S . Left

  term1 = mkEConst 1
  term2 = mkEAdd term1 term1
  term3 = mkEMult term2 term2
  term4 = mkESub term1 term1
  term5 = mkEDiv term1 term1
  term6 = mkEVar "x"
  term7 = mkELambda "x" TyInt term6
  term8 = mkEApp term7 term1
  term9 = mkELambda "x" TyInt (mkEAdd term6 term6)
  term10 = mkEApp term9 term1
  term11 = mkELambda "x" TyInt (mkELambda "y" TyInt (mkEAdd term1 term1))
  term12 = mkEApp (mkEApp term11 term1) term1

  emptyG = Gamma {gamma=[]}
  emptyE = Env {variables=[]}
  emptyAE = AbsEnv {absVariables=[]}