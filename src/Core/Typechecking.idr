module Core.Typechecking

import Data.DPair
import Decidable.Equality
import Data.SnocList.Elem
import Data.Singleton

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Conversion
import Core.Definitions

public export
data Mode = Check | Infer

public export
data TcError : Type where
  ExpectedPi : TcError
  Mismatch : Singleton bs -> VTm gs bs -> VTm gs bs -> TcError
  NameNotFound : (n : Name) -> TcError

public export
interface (Monad m) => Tc m where
  tcError : TcError -> m a

data ModeInput : (0 _ : Mode) -> GlobNamed (Named Type) where
  CheckInput : VTy gs bs -> ModeInput Check gs bs
  InferInput : ModeInput Infer gs bs

public export
data Typechecker : (0 m : Type -> Type) -> (Tc m) => (0 _ : Mode) -> GlobNamed (Named (Named Type)) where
  Checker : (Tc m) => (Context gs ns bs -> VTy gs bs -> m (STm gs ns)) -> Typechecker m Check gs ns bs
  Inferer : (Tc m) => (Context gs ns bs -> m (STm gs ns, VTy gs bs)) -> Typechecker m Infer gs ns bs

public export
convertOrError : (Tc m) => Context gs ns bs -> VTy gs bs -> VTy gs bs -> m ()
convertOrError ctx a b = if convert ctx.local.bindsSize a b then pure () else tcError (Mismatch ctx.local.binds a b)

public export
switch : (Tc m) => Typechecker m Infer gs ns bs -> Typechecker m Check gs ns bs
switch (Inferer f) = Checker $ \ctx => \ty => do
  (t, ty') <- f ctx
  convertOrError ctx ty ty'
  pure t

public export
check : (Tc m) => Typechecker m md gs ns bs -> Context gs ns bs -> VTy gs bs -> m (STm gs ns)
check (Checker f) ctx ty = f ctx ty
check (Inferer f) ctx ty = let Checker f' = switch (Inferer f) in f' ctx ty

public export
infer : (Tc m) => Typechecker m Infer gs ns bs -> Context gs ns bs -> m (STm gs ns, VTy gs bs)
infer (Inferer f) ctx = f ctx

public export
run : (Tc m) => Typechecker m md gs ns bs -> Context gs ns bs -> ModeInput md gs bs -> m (STm gs ns, VTy gs bs)
run (Checker f) ctx (CheckInput ty) = f ctx ty >>= \t => pure (t, ty)
run (Inferer f) ctx InferInput = f ctx

public export
mirror : (Tc m) => Typechecker m md gs ns bs -> (Context gs' ns' bs' -> ModeInput md gs' bs' -> m (STm gs' ns', VTy gs' bs')) -> Typechecker m md gs' ns' bs'
mirror (Checker _) k = Checker $ \ctx => \ty => do
  (a, _) <- k ctx (CheckInput ty)
  pure a
mirror (Inferer _) k = Inferer $ \ctx => k ctx InferInput

public export
var : (Tc m) => Idx ns -> Typechecker m Infer gs ns bs
var i = Inferer $ \ctx => case getIdx ctx.local i of
    MkVTerm ty _ => pure (SVar i, ty)

public export
named : (Tc m) => Name -> Typechecker m Infer gs ns bs
named n = Inferer $ \ctx => case lookupName ctx n of
    FoundLocal i (MkVTerm _ ty) _ => pure (SVar i, ty)
    FoundItem ps g ty => pure (sLams ps (SGlob g (sHeres ctx.local.size ps.size)), ty)
    NotFound => tcError (NameNotFound n)

public export
lam : (Tc m) => (n : Name) -> Typechecker m md gs (ns :< n) (bs :< n) -> Typechecker m Check gs ns bs
lam n f = Checker $ \ctx => \ty => case ty of
  VPi n' a b => do
    t <- check f (mapLocal (\l => Bind l n a) ctx) (applyRen ctx.local.bindsSize b)
    pure (SLam n t)
  _ => tcError ExpectedPi

public export
typedLam : (Tc m) => (n : Name) -> Typechecker m md gs ns bs -> Typechecker m Infer gs (ns :< n) (bs :< n) -> Typechecker m Infer gs ns bs
typedLam n a f = Inferer $ \ctx => do
    a' <- check a ctx VU
    let va = eval ctx.local.env a'
    (t, b) <- infer f (mapLocal (\l => Bind l n va) ctx)
    pure (SLam n t, VPi n va (closeVal (idEnv {s = ctx.local.bindsSize}) b))

public export
letIn : (Tc m) => (n : Name) -> Typechecker m Infer gs ns bs -> Typechecker m md gs (ns :< n) bs -> Typechecker m md gs ns bs
letIn n a b = mirror b $ \ctx => \ret => do
  (a', ty) <- infer a ctx
  let va = eval ctx.local.env a'
  (b', ret') <- run b (mapLocal (\l => Def l n ty va) ctx) ret
  pure (SLet n a' b', ret')

public export
typedLetIn : (Tc m) => (n : Name) -> Typechecker m Check gs ns bs -> Typechecker m Check gs ns bs -> Typechecker m md gs (ns :< n) bs -> Typechecker m md gs ns bs
typedLetIn n ty a b = mirror b $ \ctx => \ret => do
  ty' <- check ty ctx VU
  let vty = eval ctx.local.env ty'
  a' <- check a ctx vty
  let va = eval ctx.local.env a'
  (b', ret') <- run b (mapLocal (\l => Def l n vty va) ctx) ret
  pure (SLet n a' b', ret')

public export
app : (Tc m) => Typechecker m Infer gs ns bs -> Typechecker m md gs ns bs -> Typechecker m Infer gs ns bs
app f g = Inferer $ \ctx => do
  (f', a) <- infer f ctx
  case a of
    VPi n a b => do
      g' <- check g ctx a
      pure (SApp f' n g', b $$ eval ctx.local.env g')
    _ => tcError ExpectedPi

public export
pi : (Tc m) => (n : Name) -> Typechecker m md gs ns bs -> Typechecker m md' gs (ns :< n) (bs :< n) -> Typechecker m Infer gs ns bs
pi n a b = Inferer $ \ctx => do
  a' <- check a ctx VU
  b' <- check b (mapLocal (\l => Bind l n (eval l.env a')) ctx) VU
  pure (SPi n a' b', VU)

public export
u : (Tc m) => Typechecker m Infer gs ns bs
u = Inferer $ \ctx => pure (SU, VU)
