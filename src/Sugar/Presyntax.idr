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
  PLet : Name -> Maybe PTy -> PTm -> PTm -> PTm

public export
Show PTm where
  show (PVar n) = n.name
  show (PLam n Nothing t) = "\\" ++ n.name ++ " => " ++ show t
  show (PLam n (Just ty) t) = "\\(" ++ n.name ++ " : " ++ show ty ++ ") => " ++ show t
  show (PApp f x) = "(" ++ show f ++ " " ++ show x ++ ")"
  show (PPi n a b) = "(" ++ n.name ++ " : " ++ show a ++ ") -> " ++ show b
  show (PLet n Nothing v t) = "let " ++ n.name ++ " = " ++ show v ++ "; " ++ show t
  show (PLet n (Just ty) v t) = "let " ++ n.name ++ " : " ++ show ty ++ " = " ++ show v ++ "; " ++ show t
  show PU = "U"
