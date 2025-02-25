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
  actual : SnocList (Loc, Name, PTy)

namespace PTel
  public export
  (.arity) : PTel -> Names
  (.arity) (MkPTel [<]) = [<]
  (.arity) (MkPTel (cs :< (l, n, t))) = (assert_smaller (MkPTel (cs :< (l, n, t))) (MkPTel cs)).arity :< n

public export
record PBranches where
  constructor MkPBranches
  actual : SnocList (Loc, PPat, PTm)

public export
data PTm : Type where
  PName : Name -> PTm
  PLam : Name -> Maybe PTy -> PTm -> PTm
  PApp : PTm -> PTm -> PTm
  PPi : Name -> PTy -> PTy -> PTy
  PU : PTm
  PLoc : Loc -> PTm -> PTm
  PLet : Name -> Maybe PTy -> PTm -> PTm -> PTm
  PCase : PTm -> PBranches -> PTm

public export
record PFields where
  constructor MkPFields
  actual : List (Loc, Name, PTel, PTy)

namespace PFields
  public export
  arity : Names -> PFields -> GlobNames
  arity ps (MkPFields []) = [<]
  arity ps (MkPFields ((l, n, pr, ret) :: cs)) =
      [< (ps ++ pr.arity ** MkGlobName n CtorGlob)] ++
        arity ps (assert_smaller (MkPFields ((l, n, pr, ret) :: cs)) (MkPFields cs))

public export
0 PClauses : Type
PClauses = SnocList (SnocList PPat, PTm)

public export
data PItem : Type where
  PDef : Name -> PTel -> PTy -> PTm -> PItem
  PData : Name -> PTel -> PTel -> PFields -> PItem
  PPrim : Name -> PTel -> PTy -> PItem

public export
(.name) : PItem -> GlobName ps
(.name) (PDef n _ _ _) = MkGlobName n DefGlob
(.name) (PData n _ _ _) = MkGlobName n DataGlob
(.name) (PPrim n _ _) = MkGlobName n PrimGlob

public export
record PSig where
  constructor MkPSig
  actual : SnocList (Loc, PItem)

public export
pApps : PTm -> SnocList PTm -> PTm
pApps f [<] = f
pApps f (xs :< x) = PApp (pApps f xs) x

public export
pGatherApps : PTm -> (PTm, SnocList PTm)
pGatherApps (PApp f x) = let (f', xs) = pGatherApps f in (f', xs :< x)
pGatherApps (PLoc _ t) = pGatherApps t
pGatherApps f = (f, [<])

public export
pGatherPis : PTy -> (PTel, PTy)
pGatherPis (PPi n a b) = let (MkPTel ts, ret) = pGatherPis b in (MkPTel ([< (dummyLoc, n, a)] ++ ts), ret)
pGatherPis t = (MkPTel [<], t)

public export
pGatherLams : PTm -> (List (Name, Maybe PTy), PTm)
pGatherLams (PLam n ty t) = let (ns, t') = pGatherLams t in ((n, ty) :: ns, t')
pGatherLams (PLoc _ t) = pGatherLams t
pGatherLams t = ([], t)

public export
pPis : PTel -> PTy -> PTy
pPis (MkPTel [<]) b = b
pPis (MkPTel (ts :< (l, n, a))) b = pPis (assert_smaller (MkPTel (ts :< (l, n, a))) (MkPTel ts)) (PPi n a b)

public export
Show PTm

indented : String -> String
indented s = lines s |> map (\l => "  " ++ l) |> joinBy "\n"

public export
covering
Show PTel where
  show (MkPTel [<]) = ""
  show (MkPTel ts) = " " ++ (map (\(_, n, t) => "(" ++ show n ++ " : " ++ show t ++ ")") ts |> cast |> joinBy " ")

public export
covering
Show PBranches where
  show (MkPBranches bs) = map (\(_, p, t) => show p ++ " => " ++ show t) bs |> cast |> joinBy ",\n"

public export
covering
Show PFields where
  show (MkPFields cs) = map (\(_, n, te, t) => show n ++ show te ++ " : " ++ show t) cs |> cast |> joinBy ",\n"

public export
covering
Show PItem where
  show (PDef n tel ty tm) = "def " ++ show n ++ show tel ++ " : " ++ show ty ++ " = " ++ show tm
  show (PData n tel (MkPTel [<]) cs) = "data " ++ show n ++ show tel ++ " {" ++ indented (show cs) ++ "}"
  show (PData n tel ind cs) = "data " ++ show n ++ show tel ++ " family" ++ show ind ++ " {" ++ indented (show cs) ++ "}"
  show (PPrim n tel ty) = "prim " ++ show n ++ show tel ++ " : " ++ show ty

public export
covering
Show PSig where
  show (MkPSig [<]) = ""
  show (MkPSig [< (_, it)]) = show it
  show (MkPSig (sig :< (_, it))) = show (MkPSig sig) ++ "\n\n" ++ show it

isAtomic : PTm -> Bool
isAtomic (PName _) = True
isAtomic PU = True
isAtomic (PLoc _ t) = isAtomic t
isAtomic _ = False

covering
showAtomic : PTm -> String

covering
Show PTm where
  show (PName n) = show n
  show t@(PLam _ _ _) = let (args, ret) = pGatherLams t in "\\" ++ joinBy " " (map (\(n, ty) => case ty of
        Nothing => show n
        Just ty => "(" ++ show n ++ " : " ++ show ty ++ ")"
      ) args) ++ " => " ++ show ret
  show t@(PApp _ _) = let (s, sp) = pGatherApps t in showAtomic s ++ " " ++ joinBy " " (cast $ map showAtomic sp)
  show (PPi (MkName "_") a b) = showAtomic a ++ " -> " ++ show b
  show (PPi n a b) = "(" ++ show n ++ " : " ++ show a ++ ") -> " ++ show b
  show (PLet n Nothing v t) = "let " ++ show n ++ " = " ++ show v ++ "; " ++ show t
  show (PLet n (Just ty) v t) = "let " ++ show n ++ " : " ++ show ty ++ " = " ++ show v ++ "; " ++ show t
  show (PCase t bs) = "case " ++ show t ++ " {" ++ indented (show bs) ++ "}"
  show (PLoc _ t) = show t
  show PU = "U"

showAtomic t = if isAtomic t then show t else "(" ++ show t ++ ")"
