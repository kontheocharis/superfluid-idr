module Sugar.Presyntax

import Common

public export
data PTm : Type

public export
PTy : Type
PTy = PTm

data PTm : Type where
  PVar : String -> PTm
  PLam : String -> Maybe PTy -> PTm -> PTm
  PApp : PTm -> PTm -> PTm
  PPi : String -> PTy -> PTy -> PTy
  PU : PTm
  PLet : String -> Maybe PTy -> PTm -> PTm -> PTm

public export
pApps : PTm -> SnocList PTm -> PTm
pApps f [<] = f
pApps f (xs :< x) = PApp (pApps f xs) x

public export
Show PTm where
  show (PVar n) = n
  show (PLam n Nothing t) = "\\" ++ n ++ " => " ++ show t
  show (PLam n (Just ty) t) = "\\(" ++ n ++ " : " ++ show ty ++ ") => " ++ show t
  show (PApp f x) = "(" ++ show f ++ " " ++ show x ++ ")"
  show (PPi n a b) = "(" ++ n ++ " : " ++ show a ++ ") -> " ++ show b
  show (PLet n Nothing v t) = "let " ++ n ++ " = " ++ show v ++ "; " ++ show t
  show (PLet n (Just ty) v t) = "let " ++ n ++ " : " ++ show ty ++ " = " ++ show v ++ "; " ++ show t
  show PU = "U"
