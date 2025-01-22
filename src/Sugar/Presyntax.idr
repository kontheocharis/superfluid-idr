module Sugar.Presyntax

import Common

public export
data PTm : Type

public export
PTy : Type
PTy = PTm

data PTm : Type where
  PVar : Name -> PTm
  PLam : Name -> Maybe PTy -> PTm -> PTm
  PApp : PTm -> PTm -> PTm
  PPi : Name -> PTy -> PTy -> PTy
  PU : PTm

public export
Show PTm where
  show (PVar n) = n
  show (PLam n Nothing t) = "\\" ++ n ++ " => " ++ show t
  show (PLam n (Just ty) t) = "\\(" ++ n ++ " : " ++ show ty ++ ") => " ++ show t
  show (PApp f x) = "(" ++ show f ++ " " ++ show x ++ ")"
  show (PPi n a b) = "(" ++ n ++ " : " ++ show a ++ ") -> " ++ show b
  show PU = "U"
