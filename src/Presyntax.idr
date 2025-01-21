module Presyntax

import Common

data PTm : Type

PTy : Type
PTy = PTm

data PTm : Type where
  PVar : Name -> PTm
  PLam : Name -> PTm -> PTm
  PApp : PTm -> PTm -> PTm
  PPi : Name -> PTy -> PTy -> PTy
  PLit : Lit -> PTm

Show PTm where
  show (PVar n) = n
  show (PLam n t) = "\\" ++ n ++ " => " ++ show t
  show (PApp f x) = "(" ++ show f ++ " " ++ show x ++ ")"
  show (PPi n a b) = "(" ++ n ++ " : " ++ show a ++ ") -> " ++ show b
  show (PLit l) = show l
