module Main

import Data.String
import System
import System.File

import Common
import Context
import Surface.Parsing
import Surface.Presyntax
import Surface.Elaboration
import Surface.Unelaboration
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Typechecking
import Core.Definitions

Tc IO where
  tcError err = do
    putStrLn "Type error:"
    putStrLn $ "  " ++ show err
    exitWith (ExitFailure 1)

Elab IO where
  elabError err = do
    putStrLn "Elaboration error:"
    putStrLn $ "  " ++ show err
    exitWith (ExitFailure 1)

evalTerm : (bs : Names) => Context gs ns bs -> String -> IO ()
evalTerm ctx s = do
  Right parsed <- pure $ parse tm s
    | Left err => do
        putStrLn "Parse error:"
        putStrLn $ "  " ++ show err
        exitWith (ExitFailure 1)
  (core, ty) <- infer (elab Infer parsed) ctx
  let val = eval ctx.local.env core
  putStrLn $ "Type: " ++ show ty
  putStrLn $ "Value: " ++ show val

processTerm : String -> IO ()
processTerm input = evalTerm (MkContext [<] [<]) input

processFile : String -> IO ()
processFile filename = do
  Right content <- readFile filename
    | Left err => do
        putStrLn $ "Error reading file: " ++ show err
        exitWith (ExitFailure 1)
  processTerm content

showUsage : IO ()
showUsage = do
  putStrLn "Usage:"
  putStrLn "  compiler <filename>     Process a source file"
  putStrLn "  compiler -e <expr>      Evaluate an expression"
  putStrLn "  compiler -h             Show this help message"

partial
main : IO ()
main = do
  args <- getArgs
  case args of
    [_, "-h"] => showUsage
    [_, "-e", expr] => processTerm expr
    [_, filename] => processFile filename
    _ => do
      putStrLn "Invalid arguments"
      showUsage
      exitWith (ExitFailure 1)
