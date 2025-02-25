module Core.Typechecking

import Data.DPair
import Decidable.Equality
import Data.SnocList
import Data.SnocList.Elem
import Data.Singleton

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Conversion
import Core.Definitions
import Core.Weakening

public export
data TcMode = Check | Infer | Bind | Item | Trivial

public export
data IsTmMode : TcMode -> Type where
  CheckIsTmMode : IsTmMode Check
  InferIsTmMode : IsTmMode Infer

public export
isTmMode : (m : TcMode) -> Dec (IsTmMode m)
isTmMode Check = Yes CheckIsTmMode
isTmMode Infer = Yes InferIsTmMode
isTmMode Trivial = No (\case Refl impossible)
isTmMode Bind = No (\case Refl impossible)
isTmMode Item = No (\case Refl impossible)

public export
data TcError : Type where
  ExpectedPi : Singleton bs -> (original : VTm gs bs) -> (unfolded : VTm gs bs) -> TcError
  ExpectedFamily : Singleton bs -> (given : VTm gs bs) -> TcError
  ExpectedData : Singleton bs -> (given : VTm gs bs) -> (expected : GlobNameIn gs ps) -> TcError
  Mismatch : Singleton bs -> VTm gs bs -> VTm gs bs -> TcError
  NameNotFound : (n : Name) -> TcError

public export
interface (Monad m) => Tc m where
  setLoc : Loc -> m a -> m a
  getLoc : m Loc
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
  InTrivial : (Tc m) => Typechecker m Trivial i i
  InCheck : (Tc m)
    => (Context gs ns bs -> VTy gs bs -> m (STm gs ns))
    -> Typechecker m Check (gs, ns, bs) (gs, ns, bs)
  InInfer : (Tc m)
    => (Context gs ns bs -> m (STm gs ns, VTy gs bs))
    -> Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
  InLoc : (Tc m)
    => Loc
    -> Typechecker m md i i'
    -> Typechecker m md i i'
  InBind : (Tc m)
    => (Context gs ns bs -> m (
          Context gs (ns ++ pns) (bs ++ pbs),
          SPat gs (ns ++ pns), VTy gs (bs ++ pbs)
        ))
    -> Typechecker m Bind (gs, ns, bs) (gs, ns ++ pns, bs ++ pbs)
  InItem : (Tc m)
    => (Context gs [<] [<] -> m (Context gs' [<] [<]))
    -> Typechecker m Item (gs, [<], [<]) (gs', [<], [<])
  InError : (Tc m)
    => ({0 a : Type} -> m a)
    -> Typechecker m md i i'

public export
0 TmTypechecker : (0 m : Type -> Type) -> (Tc m) => (0 _ : TcMode) -> ContextIndex -> Type
TmTypechecker m md i = Typechecker m md i i

public export covering
convertOrError : (Tc m) => Context gs ns bs -> VTy gs bs -> VTy gs bs -> m ()
convertOrError ctx a b =
  if convert ctx.global ctx.local.bindsSize a b
    then pure ()
    else tcError (Mismatch ctx.local.binds a b)

public export covering
switch : (Tc m) => Typechecker m Infer i i' -> Typechecker m Check i i'
switch (InInfer f) = InCheck $ \ctx => \ty => do
  (t, ty') <- f ctx
  convertOrError ctx ty ty'
  pure t
switch (InError f) = InError f
switch InTrivial impossible
switch (InLoc l t) = InLoc l (switch t)

public export
run : (Tc m) => TmTypechecker m md (gs, ns, bs)
  -> Context gs ns bs
  -> TcModeInput md gs bs
  -> m (STm gs ns, VTy gs bs)
run (InCheck f) ctx (CheckInput ty) = f ctx ty >>= \t => pure (t, ty)
run (InInfer f) ctx InferInput = f ctx
run (InError f) ctx _ = f
run (InLoc l t) ctx i = setLoc l $ run t ctx i

public export covering
check : (Tc m) => {auto t : IsTmMode md}
  -> Typechecker m md (gs, ns, bs) (gs', ns', bs')
  -> Context gs ns bs
  -> VTy gs bs
  -> m (STm gs ns)
check (InCheck f) ctx ty = f ctx ty
check (InInfer f) ctx ty = case switch (InInfer f) of
  InCheck f' => f' ctx ty
  InError f => f
  InLoc l t => setLoc l $ check t ctx ty
check (InError f) ctx ty = f
check (InLoc l t) ctx ty = setLoc l $ check t ctx ty
check InTrivial impossible

public export
infer : (Tc m) => Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
  -> Context gs ns bs
  -> m (STm gs ns, VTy gs bs)
infer (InInfer f) ctx = f ctx
infer (InError f) ctx = f
infer (InLoc l t) ctx = setLoc l $ infer t ctx

public export
globally : (Tc m) => Typechecker m Item (gs, ns, bs) (gs', ns', bs') -> Context gs ns bs -> m (Context gs' ns' bs')
globally (InItem f) ctx = f ctx
globally (InError f) ctx = f
globally (InLoc l t) ctx = setLoc l $ globally t ctx

public export
mirror : (Tc m) => {auto _ : IsTmMode md}
  -> TmTypechecker m md (gs, ns, bs)
  -> (Context gs' ns' bs' -> TcModeInput md gs' bs' -> m (STm gs' ns', VTy gs' bs'))
  -> TmTypechecker m md (gs', ns', bs')
mirror (InCheck _) k = InCheck $ \ctx => \ty => do
  (a, _) <- k ctx (CheckInput ty)
  pure a
mirror (InInfer _) k = InInfer $ \ctx => k ctx InferInput
mirror (InError f) _ = InError f
mirror (InLoc l t) k = InLoc l (mirror t k)

public export
var : (Tc m) => Idx ns -> TmTypechecker m Infer (gs, ns, bs)
var i = InInfer $ \ctx => case getIdx ctx.local i of
    MkVTerm ty _ => pure (SVar i, ty)

public export covering
named : (Tc m) => Name -> TmTypechecker m Infer (gs, ns, bs)
named n = InInfer $ \ctx => case lookupName ctx n of
    FoundLocal i (MkVTerm ty _) _ => pure (SVar i, ty)
    FoundItem ps g ty => pure (sLams ps (SGlob g (sHeres ctx.local.size ps.size)), ty)
    NotFound => tcError (NameNotFound n)

public export covering
lam : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (body : TmTypechecker m md (gs, ns :< n, bs :< n))
  -> TmTypechecker m Check (gs, ns, bs)
lam n f = InCheck $ \ctx => \ty => case unfoldFully ctx.global ty of
  VPi n' a b => do
    t <- check f (mapLocal (\l => Bind l n a) ctx) (applyRen ctx.globEnv ctx.local.bindsSize b)
    pure (SLam n t)
  ty' => tcError $ ExpectedPi ctx.local.binds ty ty'

public export covering
typedLam : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (argTy : TmTypechecker m md (gs, ns, bs))
  -> (body : TmTypechecker m Infer (gs, ns :< n, bs :< n) )
  -> TmTypechecker m Infer (gs, ns, bs)
typedLam n a f = InInfer $ \ctx => do
    a' <- check a ctx VU
    let va = eval ctx.globEnv ctx.local.env a'
    (t, b) <- infer f (mapLocal (\l => Bind l n va) ctx)
    pure (SLam n t, VPi n va (closeVal (SS SZ) (idEnv {s = ctx.local.bindsSize}) b))

public export covering
letIn : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (rhs : TmTypechecker m Infer (gs, ns, bs))
  -> (rest : TmTypechecker m md (gs, ns :< n, bs))
  -> TmTypechecker m md (gs, ns, bs)
letIn n a b = mirror b $ \ctx => \ret => do
  (a', ty) <- infer a ctx
  let va = eval ctx.globEnv ctx.local.env a'
  (b', ret') <- run b (mapLocal (\l => Def l n ty va) ctx) ret
  pure (SLet n a' b', ret')

public export covering
typedLetIn : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (rhsTy : TmTypechecker m Check (gs, ns, bs))
  -> (rhs : TmTypechecker m Check (gs, ns, bs))
  -> (rest : TmTypechecker m md (gs, ns :< n, bs))
  -> TmTypechecker m md (gs, ns, bs)
typedLetIn n ty a b = mirror b $ \ctx => \ret => do
  ty' <- check ty ctx VU
  let vty = eval ctx.globEnv ctx.local.env ty'
  a' <- check a ctx vty
  let va = eval ctx.globEnv ctx.local.env a'
  (b', ret') <- run b (mapLocal (\l => Def l n vty va) ctx) ret
  pure (SLet n a' b', ret')

public export covering
app : (Tc m) => {auto _ : IsTmMode md}
  -> (fn : TmTypechecker m Infer (gs, ns, bs))
  -> (arg : TmTypechecker m md (gs, ns, bs))
  -> TmTypechecker m Infer (gs, ns, bs)
app f g = InInfer $ \ctx => do
  (f', s) <- infer f ctx
  case unfoldFully ctx.global s of
    VPi n a b => do
      g' <- check g ctx a
      pure (SApp f' n g', appClosure ctx.globEnv b [< eval ctx.globEnv ctx.local.env g'])
    s' => tcError $ ExpectedPi ctx.local.binds s s'

public export covering
pi : (Tc m) => {auto _ : IsTmMode md} -> {auto _ : IsTmMode md'}
  -> (n : Name)
  -> (dom : TmTypechecker m md (gs, ns, bs))
  -> (cod : TmTypechecker m md' (gs, ns :< n, bs :< n))
  -> TmTypechecker m Infer (gs, ns, bs)
pi n a b = InInfer $ \ctx => do
  a' <- check a ctx VU
  b' <- check b (mapLocal (\l => Bind l n (eval ctx.globEnv l.env a')) ctx) VU
  pure (SPi n a' b', VU)

public export
u : (Tc m) => TmTypechecker m Infer (gs, ns, bs)
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

namespace TelTypechecker
  public export
  data TelTypechecker : (0 m : Type -> Type) -> (Tc m)
    => ContextIndex
    -> Named Type
    where
    Lin : (Tc m) => TelTypechecker m (gs, ns, bs) [<]
    (:<) : (Tc m)
      => (c : TelTypechecker m (gs, ns, bs) ps)
      -> (p : (Name, Typechecker m Check (gs, ns ++ ps, bs ++ ps) (gs, ns ++ ps, bs ++ ps)))
      -> TelTypechecker m (gs, ns, bs) (ps :< fst p)

public export covering
tel : (Tc m)
  => TelTypechecker m (gs, ns, bs) ps
  -> Context gs ns bs
  -> m (Context gs (ns ++ ps) (bs ++ ps), VTel gs ps bs)
tel [<] ctx = pure (ctx, [<])
tel ((:<) ts (n, t)) ctx = do
  (ctx', ts') <- tel ts ctx
  t' <- check t ctx' VU
  let vty = eval ctx'.globEnv ctx'.local.env t'
  let cty = Cl ts'.size ctx.local.env t'
  pure (mapLocal (\l => Bind l n vty) ctx', ts' :< (n, cty))

public export covering
tel' : (Tc m)
  => TelTypechecker m (gs, [<], [<]) ps
  -> Context gs [<] [<]
  -> m (Context gs ps ps, VTel gs ps [<])
tel' ts ctx = do
  (ctx', te) <- tel ts ctx
  pure (apLeftMMRR {f = Context} ctx', te)

public export
caseOf : (Tc m)
  => (s : Typechecker m Infer (gs, ns, bs) (gs, ns, bs))
  -> IrrNameListN 2 (BranchTypechecker m md (gs, ns, bs))
  -> Typechecker m md (gs, ns, bs) (gs, ns, bs)
caseOf = ?caseOfImpl

public export covering
defItem : (Tc m)
  => (n : Name)
  -> (params : TelTypechecker m (gs, [<], [<]) ps)
  -> (ty : TmTypechecker m Check (gs, ps, ps))
  -> (tm : TmTypechecker m Check (gs :< (ps ** MkGlobName n DefGlob), ps, ps))
  -> Typechecker m Item (gs, [<], [<]) (gs :< (ps ** MkGlobName n DefGlob), [<], [<])
defItem n params ty tm = InItem $ \ctx => do
  (ctx', params') <- tel' params ctx
  ty' <- check ty ctx' VU
  let vty = eval ctx'.globEnv ctx'.local.env ty'
  let Val ps = ctx'.local.names
  tm' <- check tm (extendGlobal (\sig => sig :< Def (MkDefItem n params' vty Nothing)) ctx') (globWeaken vty)
  pure (extendGlobal (\sig => sig :< Def (MkDefItem n params' vty (Just tm'))) ctx)

public export covering
primItem : (Tc m)
  => (n : Name)
  -> (params : TelTypechecker m (gs, [<], [<]) ps)
  -> (ty : TmTypechecker m Check (gs, ps, ps))
  -> Typechecker m Item (gs, [<], [<]) (gs :< (ps ** MkGlobName n PrimGlob), [<], [<])
primItem n params ty = InItem $ \ctx => do
  (ctx', params') <- tel' params ctx
  ty' <- check ty ctx' VU
  let Val ps = ctx'.local.names
  let vty = eval ctx'.globEnv ctx'.local.env ty'
  pure (extendGlobal (\sig => sig :< Prim (MkPrimItem n params' vty)) ctx)

namespace CtorsTypechecker
  public export
  data CtorsTypechecker : (0 m : Type -> Type) -> (Tc m)
    => ContextIndex
    -> (ps : Names)
    -> GlobNamed Type
    where
    Lin : (Tc m)
      => CtorsTypechecker m (gs, ns, bs) ps [<]
    With : (Tc m)
      => CtorsTypechecker m (gs, ns, bs) ps gs'
      -> (n : Name)
      -> (args : TelTypechecker m (gs ++ gs', ns, bs) as)
      -> (ret : TmTypechecker m Check (gs ++ gs', ns ++ as, bs ++ as))
      -> CtorsTypechecker m (gs, ns, bs) ps (gs' :< (ps ++ as ** MkGlobName n CtorGlob))

covering
constructors : (Tc m)
  => (d : DataItem sig)
  -> {0 sig' : Sig gs}
  -> (di : ItemIn sig' (Data d))
  -> CtorsTypechecker m (gs :< (d.ps ++ d.is ** MkGlobName d.name DataGlob), d.ps, d.ps) d.ps cs
  -> Context (gs :< (d.ps ++ d.is ** MkGlobName d.name DataGlob)) d.ps d.ps
  -> m (Context (gs :< (d.ps ++ d.is ** MkGlobName d.name DataGlob) ++ cs) d.ps d.ps)
constructors _ _ Lin ctx = pure ctx
constructors d di (With cs n args ret) ctx = do
  ctx' <- constructors d di cs ctx
  (ctx'', args') <- tel args ctx'
  ret' <- check ret ctx'' VU
  let Val as = args'.names
  let vty = eval ctx''.globEnv ctx''.local.env ret'
  let gData = MkGlobNameIn ((Data d).globName) (globNameElem di)
  case unfoldFully ctx'.global vty of
    ty@(VGlob g rets [<] _) => case match g (globWeakenN _ (globWeaken gData)) of
      Just Refl => do
        let x  = ?fdsf
        let c : CtorItem di
            c = MkCtorItem {d = d} {di = di} n (globWeakenN {f = globWeakenForSpine} _ (globWeaken args')) (lastN _ rets)
        let ctx''' = MkContext (ctx'.global :< Ctor c) (globWeaken @{globWeakenCtx} ctx'.local)
        pure ctx'''
      Nothing => tcError $ ExpectedFamily ctx''.local.binds ty
    ty => tcError $ ExpectedFamily ctx''.local.binds ty
  -- case unfoldFully ctx'.global vty of
  --   VGlobal (MkGlobNameIn n' _) sp1 [<] _ => do
  --     convertOrError ctx'.global ctx'.local.binds a d
  --     constructors cs d ctx'
  --   ty => tcError $ ExpectedFamily ctx'.local.binds ty
  -- pure (extendGlobal (\sig => sig :< Ctor (MkCtorItem n args' vty)) ctx')

public export covering
dataItem : (Tc m)
  => (n : Name)
  -> (params : TelTypechecker m (gs, [<], [<]) ps)
  -> (indices : TelTypechecker m (gs, ps, ps) is)
  -> (ctors : CtorsTypechecker m (gs :< (ps ++ is ** MkGlobName n DataGlob), ps, ps) ps cs)
  -> Typechecker m Item (gs, [<], [<]) ((gs :< (ps ++ is ** MkGlobName n DataGlob)) ++ cs, [<], [<])
dataItem n params indices ctors = InItem $ \ctx => do
  (ctx', params') <- tel' params ctx
  (ctx'', ind') <- tel indices ctx'
  let Val ps = params'.names
  let Val is = ind'.names
  let d : DataItem ctx'.global
      d = MkDataItem n params' ind'
  let ctx'' = MkContext (ctx'.global :< Data d) (globWeaken @{globWeakenCtx} ctx'.local)
  ctx''' <- constructors d Here ctors ctx''
  pure $ MkContext ctx'''.global [<]
