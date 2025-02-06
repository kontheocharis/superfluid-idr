module Main

import Data.String
import System
import System.File
import Data.DPair

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
import Control.Monad.State

%default covering

Tc (StateT Loc IO) where
  getLoc = get
  setLoc l u = put l >> u

  tcError err = do
    l <- get
    putStrLn "Type error:"
    putStrLn $ "  " ++ show err
    putStrLn $ "  at " ++ show l
    exitWith (ExitFailure 1)

Elab (StateT Loc IO) where
  elabError err = do
    l <- get
    putStrLn "Elaboration error:"
    putStrLn $ "  " ++ show err
    putStrLn $ "  at " ++ show l
    exitWith (ExitFailure 1)
    
processProgram : String -> IO ()
processProgram s = do
  Right parsed <- pure $ parse sig s
    | Left err => do
        putStrLn "Parse error:"
        putStrLn $ "  " ++ show err
        exitWith (ExitFailure 1)
  (Evidence _ sig) <- evalStateT dummyLoc $ elabSig parsed
  putStrLn $ "-- Raw program:\n" ++ show parsed
  putStrLn $ "-- Checked program:\n" ++ show sig

evalTerm : (bs : Names) => Context gs ns bs -> String -> IO ()
evalTerm ctx s = do
  Right parsed <- pure $ parse tm s
    | Left err => do
        putStrLn "Parse error:"
        putStrLn $ "  " ++ show err
        exitWith (ExitFailure 1)
  (tm, ty) <- evalStateT dummyLoc $ infer (elab Infer parsed) ctx
  let val = eval ctx.globEnv ctx.local.env tm
  putStrLn $ "Raw: " ++ show parsed
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
  processProgram content

showUsage : IO ()
showUsage = do
  putStrLn "Usage:"
  putStrLn "  compiler <filename>     Process a source file"
  putStrLn "  compiler -e <expr>      Evaluate an expression"
  putStrLn "  compiler -h             Show this help message"

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
