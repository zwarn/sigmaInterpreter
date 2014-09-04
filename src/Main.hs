module Main where

import Text.Parsec
import System.IO
import Parser
import Eval
import MonadStack
import Model


--main::IO()
--main = print (execute example1)

main::IO()
main = runRepl

runRepl :: IO ()
runRepl = parseEvalLoop (readPrompt "Sigma>>> ") newReader newState

parseEvalLoop :: (IO String) -> ReaderType -> StateType -> IO()
parseEvalLoop promt log state = do
   codeLine <- promt
   if codeLine == "quit"
      then return ()
      else do
           let parsed = parseString codeLine
           case parsed of
           { Left err -> do print err
                            parseEvalLoop promt log state
           ; Right ans -> do 
                          let result = evaluate2 log state ans
                          let (newlog, newstate) = getNewStateFromResult log state result
                          parseEvalLoop promt newlog newstate            
           }
           
           
                

evaluate2 :: ReaderType -> StateType -> Term -> ResultType Term
evaluate2 log state term = runEval log state (eval term)
                
getNewStateFromResult :: ReaderType -> StateType -> ResultType Term -> (ReaderType, StateType)
getNewStateFromResult log state result = (log, state)               

parseString :: String -> Either ParseError Term
parseString string = parse termparser "" string
                   
evalAndPrint :: String -> IO ()
evalAndPrint expr =  parseInput expr

parseInput :: String -> IO ()
parseInput inp = case parse termparser "" inp of
             { Left err -> print err
             ; Right ans -> resultPrint (evaluate ans)
             }
             
justParseInput :: String -> IO ()
justParseInput inp = case parse termparser "" inp of
             { Left err -> print err
             ; Right ans -> print ans
             }
             
flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

resultPrint :: ResultType Term -> IO()
resultPrint ((Left err, log), state) = print err
resultPrint ((Right term, log), state) = do print term
                                            putStr (unlines log)