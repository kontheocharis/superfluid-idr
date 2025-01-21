module Typecheck

import Common
import Context
import Syntax
import Values
import Evaluation

data Mode = Check | Infer

interface (Monad m) => Metas m where
  freshMeta : m (VTm ns)

data TcError = ExpectedPi

interface (Monad m, Metas m) => Tc m where
  tcError : TcError -> m a

data Context : Ctx -> Type where
  Empty : Context Lin
  Bind : Context ns -> (n : Name) -> (t : VTy ns) -> Context (ns :< n)
  Def : Context ns -> (n : Name) -> (t : VTy ns) -> (tm : VTm ns) -> Context (ns :< n)

(.size) : Context ns -> Size ns
(.size) Empty = SZ
(.size) (Bind s _ _) = SS s.size
(.size) (Def s _ _ _) = SS s.size

data Typechecker : (m : Type -> Type) -> Mode -> Ctx -> Type where
  Checker : (Tc m) => ((s : Context ns) -> VTy ns -> m (STm ns)) -> Typechecker m Check ns
  Inferer : (Tc m) => ((s : Context ns) -> m (STm ns, VTy ns)) -> Typechecker m Infer ns

lam : (n : Name) -> Typechecker m md (ns :< n) -> Typechecker m md ns
lam n (Checker f) = Checker $ \ctx => \ty => case ty of
  VPi n' a b => SLam n <$> f (Bind ctx n a) (applyRen ctx.size b)
  _ => tcError ExpectedPi
lam n (Inferer f) = Inferer $ \ctx => do
  a <- freshMeta
  (t, b) <- f (Bind ctx n a)
  pure ?h1

app : Typechecker m md ns -> Typechecker m md ns -> Typechecker m md ns

pi : (n : Name) -> Typechecker m md ns -> Typechecker m md (ns :< n) -> Typechecker m md ns

lit : Lit -> Typechecker m md ns


