module Surface.Presyntax

import Common
import Context
import Data.String
import Data.SnocList
import Data.DPair

public export
data PTm : Type

public export
0 PTy : Type
PTy = PTm

public export
0 PPat : Type
PPat = PTm

public export
record PTel where
  constructor MkPTel
  actual : SnocList (Name, PTy)

public export
record PBranches where
  constructor MkPBranches
  actual : SnocList (PPat, PTm)

public export
data PTm : Type where
  PName : Name -> PTm
  PLam : Name -> Maybe PTy -> PTm -> PTm
  PApp : PTm -> PTm -> PTm
  PPi : Name -> PTy -> PTy -> PTy
  PU : PTm
  PLet : Name -> Maybe PTy -> PTm -> PTm -> PTm
  PCase : PTm -> PBranches -> PTm
  
public export
record PFields where
  constructor MkPFields
  actual : PTel

public export
0 PClauses : Type
PClauses = SnocList (SnocList PPat, PTm)

public export
data PItem : Type where
  PDef : Name -> PTel -> PTy -> PTm -> PItem
  PData : Name -> PTel -> PTy -> PFields -> PItem
  PPrim : Name -> PTel -> PTy -> PItem
  
public export
(.name) : PItem -> GlobName ps
(.name) (PDef n _ _ _) = MkGlobName n DefGlob
(.name) (PData n _ _ _) = MkGlobName n DataGlob
(.name) (PPrim n _ _) = MkGlobName n PrimGlob

public export
record PSig where
  constructor MkPSig
  actual : SnocList PItem

public export
pApps : PTm -> SnocList PTm -> PTm
pApps f [<] = f
pApps f (xs :< x) = PApp (pApps f xs) x

public export
pPis : PTel -> PTy -> PTy
pPis (MkPTel [<]) b = b
pPis (MkPTel (ts :< (n, a))) b = pPis (assert_smaller (MkPTel (ts :< (n, a))) (MkPTel ts)) (PPi n a b)

public export
Show PTm

indented : String -> String
indented s = lines s |> map (\l => "  " ++ l) |> joinBy "\n"

public export
covering
Show PTel where
  show (MkPTel [<]) = ""
  show (MkPTel ts) = " " ++ (map (\(n, t) => show n ++ " : " ++ show t) ts |> cast |> joinBy " ")

public export
covering
Show PBranches where
  show (MkPBranches bs) = map (\(p, t) => show p ++ " => " ++ show t) bs |> cast |> joinBy ",\n"
  
public export
covering
Show PFields where
  show (MkPFields cs) = map (\(n, t) => show n ++ " : " ++ show t) cs.actual |> cast |> joinBy ",\n" 

public export
covering
Show PItem where
  show (PDef n tel ty tm) = "def " ++ show n ++ show tel ++ " : " ++ show ty ++ " = " ++ show tm
  show (PData n tel ty cs) = "data " ++ show n ++ show tel ++ " : " ++ show ty ++ " {" ++ indented (show cs) ++ "}"
  show (PPrim n tel ty) = "prim " ++ show n ++ show tel ++ " : " ++ show ty
  
public export
covering
Show PSig where
  show (MkPSig [<]) = ""
  show (MkPSig [< it]) = show it
  show (MkPSig (sig :< it)) = show (MkPSig sig) ++ "\n\n" ++ show it
  
covering
Show PTm where
  show (PName n) = show n
  show (PLam n Nothing t) = "\\" ++ show n ++ " => " ++ show t
  show (PLam n (Just ty) t) = "\\(" ++ show n ++ " : " ++ show ty ++ ") => " ++ show t
  show (PApp f x) = "(" ++ show f ++ " " ++ show x ++ ")"
  show (PPi n a b) = "(" ++ show n ++ " : " ++ show a ++ ") -> (" ++ show b ++ ")"
  show (PLet n Nothing v t) = "let " ++ show n ++ " = " ++ show v ++ "; " ++ show t
  show (PLet n (Just ty) v t) = "let " ++ show n ++ " : " ++ show ty ++ " = " ++ show v ++ "; " ++ show t
  show (PCase t bs) = "case " ++ show t ++ " {" ++ indented (show bs) ++ "}"
  show PU = "U"
