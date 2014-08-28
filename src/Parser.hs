module Parser where

import Control.Applicative((<*))
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as TokenParser
import Text.Parsec.Language

import Model
import MonadStack

def = emptyDef{ TokenParser.commentStart = "/*"
              , TokenParser.commentEnd = "*/"
              , TokenParser.identStart = letter
              , TokenParser.identLetter = alphaNum
              , TokenParser.opStart = oneOf "~=@."
              , TokenParser.opLetter = oneOf "=@."
              , TokenParser.reservedOpNames = ["@", ".", "=", "<=", "(", ")", "||"
                                            , ">>"]
              , TokenParser.reservedNames = ["true", "false", "nop",
                                 "if", "then", "else", "fi",
                                 "while", "do", "od", "$In", "$Out", "Signal"]
              }

lexer = TokenParser.makeTokenParser def
identifier = TokenParser.identifier lexer
reservedOp = TokenParser.reservedOp lexer
reserved = TokenParser.reserved lexer
semiSep1 = TokenParser.semiSep1 lexer
whiteSpace = TokenParser.whiteSpace lexer
parens = TokenParser.parens lexer
integer = TokenParser.integer lexer
brackets = TokenParser.brackets lexer
commaSep1 = TokenParser.commaSep1 lexer
           
parseTerm :: Parser Term
parseTerm = try parseOverride
            <|> try parseInvocation
            <|> try parseObject
            <|> try parseVariable          

parseVariable :: Parser Term
parseVariable = do { var <- identifier
                   ; return $ Var var
                   }

parseObject :: Parser Term
parseObject = do { funcDef <- brackets (commaSep1 parseFuncDef)
                 ; return $ Object funcDef
                 }

parseFuncDef :: Parser FuncDef
parseFuncDef = do { name <- identifier
                  ; reservedOp "="
                  ; body <- try parseFuncBody <|> parseMethodeBody
                  ; return $ FuncDef (name, body)
                  }

parseMethodeBody :: Parser FuncBody
parseMethodeBody = do { term <- parseTerm
                      ; return $ FuncBody "null" term
                      }

parseFuncBody :: Parser FuncBody
parseFuncBody = do { reservedOp "@"
                   ; name <- parens identifier
                   ; term <- parseTerm
                   ; return $ FuncBody name term
                   }
                   
parseInvocation :: Parser Term
parseInvocation = do { term <- parseIdentifierOrTerm
                     ; reservedOp "."
                     ; name <- identifier
                     ; return $ Invocation term name
                     }
                     
parseOverride :: Parser Term
parseOverride = do { term <- parseIdentifierOrTerm
                   ; reservedOp "."
                   ; name <- identifier
                   ; reservedOp "<="
                   ; func <- try parseFuncBody <|> parseMethodeBody
                   ; return $ Override term name func
                   }                 
                 
parseIdentifierOrTerm :: Parser Term
parseIdentifierOrTerm = parseVariable
                        <|> do { term <- parens parseTerm
                               ; return term
                               }


termparser :: Parser Term
termparser = whiteSpace >> parseTerm <* eof