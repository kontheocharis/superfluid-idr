module Sugar.Elaboration

import Common
import Context
import Sugar.Presyntax
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Typechecking

import Data.DPair
import Data.SnocList
import Data.SnocList.Elem

public export
data ElabError : Type where
  CannotInferLam : ElabError

public export
interface (Tc m) => Elab m where
  errorElab : {md : Mode} -> ElabError -> Typechecker m md gs ns bs

public export
elab : (Elab m) => (md : Mode) -> PTm -> Typechecker m md gs ns bs
elab Check (PLam n Nothing t) = lam (MkName n) (elab Check t)
elab md (PLet n Nothing a b) = letIn (MkName n) (elab Infer a) (elab md b)
elab md (PLet n (Just ty) a b) = typedLetIn (MkName n) (elab Check ty) (elab Check a) (elab md b)
elab Check u = switch (elab Infer u)
elab Infer (PLam n (Just ty) t) = typedLam (MkName n) (elab Check ty) (elab Infer t)
elab Infer (PLam n Nothing t) = errorElab CannotInferLam
elab Infer (PPi n a b) = pi (MkName n) (elab Check a) (elab Check b)
elab Infer (PApp f x) = app (elab Infer f) (elab Check x)
elab Infer (PVar n) = named (MkName n)
elab Infer PU = u

public export
unelab : (ns : Names) -> STm gs ns -> PTm

public export
unelabSpine : (ns : Names) -> Spine (STm gs) ps ns -> SnocList PTm
unelabSpine ns [<] = [<]
unelabSpine ns (xs :< x) = unelabSpine ns xs :< unelab ns x

unelab ns (SLam n t) = PLam n.name Nothing (unelab (ns :< n) t)
unelab ns (SPi n a b) = PPi n.name (unelab ns a) (unelab (ns :< n) b)
unelab ns (SApp f n x) = PApp (unelab ns f) (unelab ns x)
unelab ns (SVar i) = PVar (getName ns i).name
unelab ns (SLet n a b) = PLet n.name Nothing (unelab ns a) (unelab (ns :< n) b)
unelab ns (SGlob (Element n _) sp) = pApps (PVar n.name) (unelabSpine ns sp)
unelab ns SU = PU

public export
(ns : Names) => Show (STm gs ns) where
  show t = show (unelab ns t)
