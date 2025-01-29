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
data TcMode = Check | Infer | Bind | Item

public export
data IsTmMode : TcMode -> Type where
  CheckIsTmMode : IsTmMode Check
  InferIsTmMode : IsTmMode Infer
  
public export
isTmMode : (m : TcMode) -> Dec (IsTmMode m)
isTmMode Check = Yes CheckIsTmMode
isTmMode Infer = Yes InferIsTmMode
isTmMode Bind = No (\case Refl impossible)
isTmMode Item = No (\case Refl impossible)

public export
data TcError : Type where
  ExpectedPi : TcError
  Mismatch : Singleton bs -> VTm gs bs -> VTm gs bs -> TcError
  NameNotFound : (n : Name) -> TcError

public export
interface (Monad m) => Tc m where
  tcError : TcError -> m a

public export
data TcModeInput : (0 _ : TcMode) -> GlobNamed (Named Type) where
  CheckInput : VTy gs bs -> TcModeInput Check gs bs
  InferInput : TcModeInput Infer gs bs

public export
0 ContextIndex : Type 
ContextIndex = (GlobNames, Names, Names)

public export
0 TypecheckerKind : Type
TypecheckerKind = (0 m : Type -> Type) -> (Tc m)
  => (0 _ : TcMode)
  -> ContextIndex
  -> ContextIndex
  -> Type

public export
data Typechecker : TypecheckerKind where
  InCheck : (Tc m)
    => (Context gs ns bs -> VTy gs bs -> m (STm gs ns))
    -> Typechecker m Check (gs, ns, bs) (gs, ns, bs)
  InInfer : (Tc m)
    => (Context gs ns bs -> m (STm gs ns, VTy gs bs))
    -> Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
  InBind : (Tc m)
    => (Context gs ns bs -> m (
          Context gs (ns ++ pns) (bs ++ pbs),
          SPat gs (ns ++ pns), VTy gs (bs ++ pbs)
        ))
    -> Typechecker m Bind (gs, ns, bs) (gs, ns ++ pns, bs ++ pbs)
  InItem : (Tc m)
    => (Context gs [<] [<] -> m (Context (gs :< g) [<] [<]))
    -> Typechecker m Item (gs, [<], [<]) (gs :< g, [<], [<])
  InError : (Tc m)
    => ({0 a : Type} -> m a)
    -> Typechecker m md i i'

public export
convertOrError : (Tc m) => Context gs ns bs -> VTy gs bs -> VTy gs bs -> m ()
convertOrError ctx a b =
  if convert ctx.local.bindsSize a b
    then pure ()
    else tcError (Mismatch ctx.local.binds a b)

public export
switch : (Tc m) => Typechecker m Infer i i' -> Typechecker m Check i i'
switch (InInfer f) = InCheck $ \ctx => \ty => do
  (t, ty') <- f ctx
  convertOrError ctx ty ty'
  pure t
switch (InError f) = InError f

public export
check : (Tc m) => {auto _ : IsTmMode md}
  -> Typechecker m md (gs, ns, bs) (gs', ns', bs')
  -> Context gs ns bs
  -> VTy gs bs
  -> m (STm gs ns)
check (InCheck f) ctx ty = f ctx ty
check (InInfer f) ctx ty = case switch (InInfer f) of
  InCheck f' => f' ctx ty
  InError f => f
check (InError f) ctx ty = f

public export
infer : (Tc m) => Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
  -> Context gs ns bs
  -> m (STm gs ns, VTy gs bs)
infer (InInfer f) ctx = f ctx
infer (InError f) ctx = f

public export
run : (Tc m) => Typechecker m md (gs, ns, bs) (gs, ns, bs)
  -> Context gs ns bs
  -> TcModeInput md gs bs
  -> m (STm gs ns, VTy gs bs)
run (InCheck f) ctx (CheckInput ty) = f ctx ty >>= \t => pure (t, ty)
run (InInfer f) ctx InferInput = f ctx
run (InError f) ctx _ = f

public export
mirror : (Tc m) => {auto _ : IsTmMode md}
  -> Typechecker m md (gs, ns, bs) (gs, ns, bs)
  -> (Context gs' ns' bs' -> TcModeInput md gs' bs' -> m (STm gs' ns', VTy gs' bs'))
  -> Typechecker m md (gs', ns', bs') (gs', ns', bs')
mirror (InCheck _) k = InCheck $ \ctx => \ty => do
  (a, _) <- k ctx (CheckInput ty)
  pure a
mirror (InInfer _) k = InInfer $ \ctx => k ctx InferInput
mirror (InError f) _ = InError f

public export
var : (Tc m) => Idx ns -> Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
var i = InInfer $ \ctx => case getIdx ctx.local i of
    MkVTerm ty _ => pure (SVar i, ty)

public export
named : (Tc m) => Name -> Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
named n = InInfer $ \ctx => case lookupName ctx n of
    FoundLocal i (MkVTerm ty _) _ => pure (SVar i, ty)
    FoundItem ps g ty => pure (sLams ps (SGlob g (sHeres ctx.local.size ps.size)), ty)
    NotFound => tcError (NameNotFound n)

public export
lam : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (body : Typechecker m md (gs, ns :< n, bs :< n) (gs, ns :< n, bs :< n))
  -> Typechecker m Check (gs, ns, bs) (gs, ns, bs)
lam n f = InCheck $ \ctx => \ty => case ty of
  VPi n' a b => do
    t <- check f (mapLocal (\l => Bind l n a) ctx) (applyRen ctx.local.bindsSize b)
    pure (SLam n t)
  _ => tcError ExpectedPi

public export
typedLam : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (argTy : Typechecker m md (gs, ns, bs) (gs, ns, bs))
  -> (body : Typechecker m Infer (gs, ns :< n, bs :< n) (gs, ns :< n, bs :< n))
  -> Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
typedLam n a f = InInfer $ \ctx => do
    a' <- check a ctx VU
    let va = eval ctx.local.env a'
    (t, b) <- infer f (mapLocal (\l => Bind l n va) ctx)
    pure (SLam n t, VPi n va (closeVal (idEnv {s = ctx.local.bindsSize}) b))

public export
letIn : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (rhs : Typechecker m Infer (gs, ns, bs) (gs, ns, bs))
  -> (rest : Typechecker m md (gs, ns :< n, bs) (gs, ns :< n, bs))
  -> Typechecker m md (gs, ns, bs) (gs, ns, bs)
letIn n a b = mirror b $ \ctx => \ret => do
  (a', ty) <- infer a ctx
  let va = eval ctx.local.env a'
  (b', ret') <- run b (mapLocal (\l => Def l n ty va) ctx) ret
  pure (SLet n a' b', ret')

public export
typedLetIn : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (rhsTy : Typechecker m Check (gs, ns, bs) (gs, ns, bs))
  -> (rhs : Typechecker m Check (gs, ns, bs) (gs, ns, bs))
  -> (rest : Typechecker m md (gs, ns :< n, bs) (gs, ns :< n, bs))
  -> Typechecker m md (gs, ns, bs) (gs, ns, bs)
typedLetIn n ty a b = mirror b $ \ctx => \ret => do
  ty' <- check ty ctx VU
  let vty = eval ctx.local.env ty'
  a' <- check a ctx vty
  let va = eval ctx.local.env a'
  (b', ret') <- run b (mapLocal (\l => Def l n vty va) ctx) ret
  pure (SLet n a' b', ret')

public export
app : (Tc m) => {auto _ : IsTmMode md}
  -> (fn : Typechecker m Infer (gs, ns, bs) (gs, ns, bs))
  -> (arg : Typechecker m md (gs, ns, bs) (gs, ns, bs))
  -> Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
app f g = InInfer $ \ctx => do
  (f', a) <- infer f ctx
  case a of
    VPi n a b => do
      g' <- check g ctx a
      pure (SApp f' n g', b $$ eval ctx.local.env g')
    _ => tcError ExpectedPi

public export
pi : (Tc m) => {auto _ : IsTmMode md} -> {auto _ : IsTmMode md'}
  -> (n : Name)
  -> (dom : Typechecker m md (gs, ns, bs) (gs, ns, bs))
  -> (cod : Typechecker m md' (gs, ns :< n, bs :< n) (gs, ns :< n, bs :< n))
  -> Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
pi n a b = InInfer $ \ctx => do
  a' <- check a ctx VU
  b' <- check b (mapLocal (\l => Bind l n (eval l.env a')) ctx) VU
  pure (SPi n a' b', VU)

public export
u : (Tc m) => Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
u = InInfer $ \ctx => pure (SU, VU)

public export
0 BranchTypechecker : (0 m : Type -> Type) -> (Tc m)
  => (0 _ : TcMode)
  -> ContextIndex
  -> Named (Named Type)
BranchTypechecker m md (gs, ns, bs) pns pbs = (
    Typechecker m Bind (gs, ns, bs) (gs, ns ++ pns, bs ++ pbs),
    Typechecker m md (gs, ns ++ pns, bs ++ pbs) (gs, ns ++ pns, bs ++ pbs)
  )

public export
caseOf : (Tc m)
  => (s : Typechecker m Infer (gs, ns, bs) (gs, ns, bs))
  -> IrrNameListN 2 (BranchTypechecker m md (gs, ns, bs))
  -> Typechecker m md (gs, ns, bs) (gs, ns, bs)
caseOf = todo