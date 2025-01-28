module Surface.Presyntax

import Common
import Context

public export
data PTm : Type

public export
PTy : Type
PTy = PTm

public export
data PTm : Type where
  PName : Name -> PTm
  PLam : Name -> Maybe PTy -> PTm -> PTm
  PApp : PTm -> PTm -> PTm
  PPi : Name -> PTy -> PTy -> PTy
  PU : PTm
  PLet : Name -> Maybe PTy -> PTm -> PTm -> PTm

public export
pApps : PTm -> SnocList PTm -> PTm
pApps f [<] = f
pApps f (xs :< x) = PApp (pApps f xs) x

public export
Show PTm where
  show (PName n) = show n
  show (PLam n Nothing t) = "\\" ++ show n ++ " => " ++ show t
  show (PLam n (Just ty) t) = "\\(" ++ show n ++ " : " ++ show ty ++ ") => " ++ show t
  show (PApp f x) = "(" ++ show f ++ " " ++ show x ++ ")"
  show (PPi n a b) = "(" ++ show n ++ " : " ++ show a ++ ") -> " ++ show b
  show (PLet n Nothing v t) = "let " ++ show n ++ " = " ++ show v ++ "; " ++ show t
  show (PLet n (Just ty) v t) = "let " ++ show n ++ " : " ++ show ty ++ " = " ++ show v ++ "; " ++ show t
  show PU = "U"
