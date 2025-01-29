module Surface.Unelaboration

import Core.Definitions
import Data.SnocList
import Data.Singleton
import Common
import Context
import Surface.Presyntax
import Surface.Elaboration
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Typechecking

public export
unelab : (ns : Names) -> STm gs ns -> PTm

public export
unelabSpine : (ns : Names) -> Spine (STm gs) ps ns -> SnocList PTm
unelabSpine ns [<] = [<]
unelabSpine ns (xs :< x) = unelabSpine ns xs :< unelab ns x

unelab ns (SLam n t) = PLam n Nothing (unelab (ns :< n) t)
unelab ns (SPi n a b) = PPi n (unelab ns a) (unelab (ns :< n) b)
unelab ns (SApp f n x) = PApp (unelab ns f) (unelab ns x)
unelab ns (SVar i) = PName (getName ns i)
unelab ns (SLet n a b) = PLet n Nothing (unelab ns a) (unelab (ns :< n) b)
unelab ns (SGlob (MkGlobNameIn n _) sp) = pApps (PName n.name) (unelabSpine ns sp)
unelab ns SU = PU

public export
partial covering
(ns : Names) => Show (STm gs ns) where
  show t = show (unelab ns t)

public export
partial covering
(ns : Names) => Show (VTm gs ns) where
  show t = show (quote ns.size t)

public export
partial covering
Show TcError where
  show ExpectedPi = "Expected function type"
  show (Mismatch (Val bs) a b) = "Mismatch: " ++ show a ++ " vs " ++ show b
  show (NameNotFound n) = "Name " ++ show n ++ " not found"

public export
Show ElabError where
  show CannotInferLam = "Cannot infer type of lambda"
