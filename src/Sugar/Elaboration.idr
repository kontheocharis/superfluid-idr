module Sugar.Elaboration

import Common
import Context
import Sugar.Presyntax
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Typechecking

data ElabError : Type where
  CannotInferLam : ElabError

interface (Tc m) => Elab m where
  errorElab : {md : Mode} -> ElabError -> Typechecker m md ns bs

elab : (Elab m) => (md : Mode) -> PTm -> Typechecker m md ns bs
elab Check (PLam n Nothing t) = lam n (elab Check t)
elab Infer (PLam n Nothing t) = errorElab CannotInferLam
elab Infer (PLam n (Just ty) t) = typedLam n (elab Check ty) (elab Infer t)
elab Check u = switch (elab Infer u)
elab Infer (PVar n) = named n
elab Infer (PApp f x) = app (elab Infer f) (elab Check x)
elab Infer (PPi n a b) = pi n (elab Check a) (elab Check b)
elab Infer PU = u
