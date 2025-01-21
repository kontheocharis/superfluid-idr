module Core.Typechecking

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Evaluation

data Mode = Check | Infer

interface (Monad m) => Metas m where
  freshMeta : m (VTm ns)

data TcError = ExpectedPi

interface (Monad m, Metas m) => Tc m where
  tcError : TcError -> m a

data Context : Names -> Names -> Type

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

data Typechecker : (m : Type -> Type) -> (Tc m) => Mode -> Names -> Names -> Type where
  Checker : (Tc m) => (Context ns bs -> VTy bs -> m (STm ns)) -> Typechecker m Check ns bs
  Inferer : (Tc m) => (Context ns bs -> m (STm ns, VTy bs)) -> Typechecker m Infer ns bs

lam : (Tc m) => (n : Name) -> Typechecker m md (ns :< n) (bs :< n) -> Typechecker m md ns bs
lam n (Checker f) = Checker $ \ctx => \ty => case ty of
  VPi n' a b => do
    t <- f (Bind ctx n a) (applyRen ctx.bindsSize b)
    pure (SLam n t)
  _ => tcError ExpectedPi
lam n (Inferer f) = Inferer $ \ctx => do
  a <- freshMeta
  (t, b) <- f (Bind ctx n a)
  pure (SLam n t, VPi n a (closeVal (idEnv ctx.bindsSize) b))

app : (Tc m) => Typechecker m Infer ns bs -> Typechecker m Check ns bs -> Typechecker m Infer ns bs
app (Inferer f) (Checker g) = Inferer $ \ctx => do
  (f', a) <- f ctx
  case a of
    VPi n a b => do
      g' <- g ctx a
      pure (SApp f' g', b $$ eval ctx.env g')
    _ => tcError ExpectedPi

pi : (Tc m) => (n : Name) -> Typechecker m md ns bs -> Typechecker m md (ns :< n) (bs :< n) -> Typechecker m md ns bs

lit : (Tc m) => Lit -> Typechecker m md ns bs
