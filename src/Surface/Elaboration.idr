module Surface.Elaboration

import Core.Definitions
import Common
import Context
import Surface.Presyntax
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
  elabError : ElabError -> m a

errorElab : (Elab m) => {md : TcMode} -> ElabError -> Typechecker m md gs ns bs
errorElab {md = Infer} e = Inferer $ \_ => elabError e
errorElab {md = Check} e = Checker $ \_ => \_ => elabError e

public export
elab : (Elab m) => (md : TcMode) -> PTm -> Typechecker m md gs ns bs
elab Check (PLam n Nothing t) = lam n (elab Check t)
elab md (PLet n Nothing a b) = letIn n (elab Infer a) (elab md b)
elab md (PLet n (Just ty) a b) = typedLetIn n (elab Check ty) (elab Check a) (elab md b)
elab Check u = switch (elab Infer u)
elab Infer (PLam n (Just ty) t) = typedLam n (elab Check ty) (elab Infer t)
elab Infer (PLam n Nothing t) = errorElab CannotInferLam
elab Infer (PPi n a b) = pi n (elab Check a) (elab Check b)
elab Infer (PApp f x) = app (elab Infer f) (elab Check x)
elab Infer (PName n) = named n
elab Infer PU = u
