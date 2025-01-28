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

record CompilerState where
  constructor MkCompilerState
  sig : Sig Lin

Context' : Type
Context' = Context Lin Lin Lin

Context0 : Type
Context0 = Context Lin [<] [<]

initContext : Context0
initContext = MkContext Lin Lin

Show ElabError where
  show CannotInferLam = "Cannot infer type of lambda expression"

Tc IO where
  tcError err = do
    putStrLn "Type error:"
    putStrLn $ "  " ++ show err
    exitWith (ExitFailure 1)

Elab IO where
  errorElab = tcError

evalTerm : Context0 -> String -> IO ()
evalTerm ctx s = do
  Right parsed <- pure $ parse tm s
    | Left err => do
        putStrLn "Parse error:"
        putStrLn $ "  " ++ show err
        exitWith (ExitFailure 1)

  (core, ty) <- run (elab Infer) ctx InferInput
  let val = eval [<] core
  putStrLn $ "Type: " ++ show ty
  putStrLn $ "Value: " ++ show val

processTerm : String -> IO ()
processTerm input = evalTerm initContext input

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
