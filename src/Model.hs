module Model where

type Name = String
data Term = Object [FuncDef]
          | Var Name
          | Invocation Term Name
          | Override Term Name FuncBody
--        deriving Show
          
data FuncDef = FuncDef (String, FuncBody)
--        deriving Show

data FuncBody = FuncBody String Term
--         deriving Show

instance Show Term where
        show (Object funcs) = show funcs
        show (Var name) = name
        show (Invocation term name) = show term ++ "." ++ name
        show (Override term name funcbody) = show term ++ "." ++ name ++ "<=" ++ show funcbody
        
instance Show FuncDef where
        show (FuncDef (name, funcbody)) = name ++ "=" ++ show funcbody
        
instance Show FuncBody where
        show (FuncBody name term) = "@(" ++ name ++ ")" ++ show term
              