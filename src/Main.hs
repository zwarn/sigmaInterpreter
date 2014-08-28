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
runRepl = parseEvalLoop (readPrompt "Sigma>>> ")

parseEvalLoop :: (IO String) -> IO()
parseEvalLoop promt = do
   codeLine <- promt
   if codeLine == "quit"
      then return ()
      else let result = evalAndPrint codeLine in
                do result
                   parseEvalLoop promt
                   
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