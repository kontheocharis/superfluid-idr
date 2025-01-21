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

data Context : Ctx -> Ctx -> Type

data Context where
  Empty : Context Lin Lin
  Bind : (ctx : Context ns bs) -> (n : Name) -> (t : VTy bs) -> Context (ns :< n) (bs :< n)
  Def : (ctx : Context ns bs) -> (n : Name) -> (t : VTy bs) -> (tm : VTm bs) -> Context (ns :< n) bs

(.bindsSize) : Context ns bs -> Size bs
(.bindsSize) Empty = SZ
(.bindsSize) (Bind s _ _) = SS s.bindsSize
(.bindsSize) (Def s _ _ _) = s.bindsSize

(.size) : Context ns bs -> Size ns
(.size) Empty = SZ
(.size) (Bind s _ _) = SS s.size
(.size) (Def s _ _ _) = SS s.size

(.env) : Context ns bs -> Env bs ns
(.env) Empty = LinEnv
(.env) (Bind ctx _ _) = growEnv ctx.bindsSize ctx.env
(.env) (Def ctx _ _ tm) = ctx.env :< tm

data Typechecker : (m : Type -> Type) -> Mode -> Ctx -> Ctx -> Type where
  Checker : (Tc m) => (Context ns bs -> VTy bs -> m (STm ns)) -> Typechecker m Check ns bs
  Inferer : (Tc m) => (Context ns bs -> m (STm ns, VTy bs)) -> Typechecker m Infer ns bs

lam : (n : Name) -> Typechecker m md (ns :< n) (bs :< n) -> Typechecker m md ns bs
lam n (Checker f) = Checker $ \ctx => \ty => case ty of
  VPi n' a b => SLam n <$> f (Bind ctx n a) (applyRen ctx.bindsSize b)
  _ => tcError ExpectedPi
lam n (Inferer f) = Inferer $ \ctx => do
  a <- freshMeta
  (t, b) <- f (Bind ctx n a)
  pure (SLam n t, VPi n a (closeVal (idEnv ctx.bindsSize) b))

app : Typechecker m md ns bs -> Typechecker m md ns bs -> Typechecker m md ns bs

pi : (n : Name) -> Typechecker m md ns bs -> Typechecker m md (ns :< n) (bs :< n) -> Typechecker m md ns bs

lit : Lit -> Typechecker m md ns bs


