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
  InTrivial : (Tc m) => Typechecker m Trivial i i
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
0 TmTypechecker : (0 m : Type -> Type) -> (Tc m) => (0 _ : TcMode) -> ContextIndex -> Type
TmTypechecker m md i = Typechecker m md i i

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
switch InTrivial impossible

public export
check : (Tc m) => {auto t : IsTmMode md}
  -> Typechecker m md (gs, ns, bs) (gs', ns', bs')
  -> Context gs ns bs
  -> VTy gs bs
  -> m (STm gs ns)
check (InCheck f) ctx ty = f ctx ty
check (InInfer f) ctx ty = case switch (InInfer f) of
  InCheck f' => f' ctx ty
  InError f => f
check (InError f) ctx ty = f
check InTrivial impossible

public export
infer : (Tc m) => Typechecker m Infer (gs, ns, bs) (gs, ns, bs)
  -> Context gs ns bs
  -> m (STm gs ns, VTy gs bs)
infer (InInfer f) ctx = f ctx
infer (InError f) ctx = f

public export
globally : (Tc m) => Typechecker m Item (gs, ns, bs) (gs', ns', bs') -> Context gs ns bs -> m (Context gs' ns' bs')
globally (InItem f) ctx = f ctx
globally (InError f) ctx = f

public export
run : (Tc m) => TmTypechecker m md (gs, ns, bs)
  -> Context gs ns bs
  -> TcModeInput md gs bs
  -> m (STm gs ns, VTy gs bs)
run (InCheck f) ctx (CheckInput ty) = f ctx ty >>= \t => pure (t, ty)
run (InInfer f) ctx InferInput = f ctx
run (InError f) ctx _ = f

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

public export
var : (Tc m) => Idx ns -> TmTypechecker m Infer (gs, ns, bs)
var i = InInfer $ \ctx => case getIdx ctx.local i of
    MkVTerm ty _ => pure (SVar i, ty)

public export
named : (Tc m) => Name -> TmTypechecker m Infer (gs, ns, bs)
named n = InInfer $ \ctx => case lookupName ctx n of
    FoundLocal i (MkVTerm ty _) _ => pure (SVar i, ty)
    FoundItem ps g ty => pure (sLams ps (SGlob g (sHeres ctx.local.size ps.size)), ty)
    NotFound => tcError (NameNotFound n)

public export
lam : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (body : TmTypechecker m md (gs, ns :< n, bs :< n))
  -> TmTypechecker m Check (gs, ns, bs)
lam n f = InCheck $ \ctx => \ty => case ty of
  VPi n' a b => do
    t <- check f (mapLocal (\l => Bind l n a) ctx) (applyRen ctx.local.bindsSize b)
    pure (SLam n t)
  _ => tcError ExpectedPi
  

public export
typedLam : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (argTy : TmTypechecker m md (gs, ns, bs))
  -> (body : TmTypechecker m Infer (gs, ns :< n, bs :< n) )
  -> TmTypechecker m Infer (gs, ns, bs) 
typedLam n a f = InInfer $ \ctx => do
    a' <- check a ctx VU
    let va = eval ctx.local.env a'
    (t, b) <- infer f (mapLocal (\l => Bind l n va) ctx)
    pure (SLam n t, VPi n va (closeVal (idEnv {s = ctx.local.bindsSize}) b))

public export
letIn : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (rhs : TmTypechecker m Infer (gs, ns, bs))
  -> (rest : TmTypechecker m md (gs, ns :< n, bs))
  -> TmTypechecker m md (gs, ns, bs) 
letIn n a b = mirror b $ \ctx => \ret => do
  (a', ty) <- infer a ctx
  let va = eval ctx.local.env a'
  (b', ret') <- run b (mapLocal (\l => Def l n ty va) ctx) ret
  pure (SLet n a' b', ret')

public export
typedLetIn : (Tc m) => {auto _ : IsTmMode md}
  -> (n : Name)
  -> (rhsTy : TmTypechecker m Check (gs, ns, bs))
  -> (rhs : TmTypechecker m Check (gs, ns, bs))
  -> (rest : TmTypechecker m md (gs, ns :< n, bs))
  -> TmTypechecker m md (gs, ns, bs) 
typedLetIn n ty a b = mirror b $ \ctx => \ret => do
  ty' <- check ty ctx VU
  let vty = eval ctx.local.env ty'
  a' <- check a ctx vty
  let va = eval ctx.local.env a'
  (b', ret') <- run b (mapLocal (\l => Def l n vty va) ctx) ret
  pure (SLet n a' b', ret')

public export
app : (Tc m) => {auto _ : IsTmMode md}
  -> (fn : TmTypechecker m Infer (gs, ns, bs))
  -> (arg : TmTypechecker m md (gs, ns, bs))
  -> TmTypechecker m Infer (gs, ns, bs) 
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
  -> (dom : TmTypechecker m md (gs, ns, bs))
  -> (cod : TmTypechecker m md' (gs, ns :< n, bs :< n))
  -> TmTypechecker m Infer (gs, ns, bs) 
pi n a b = InInfer $ \ctx => do
  a' <- check a ctx VU
  b' <- check b (mapLocal (\l => Bind l n (eval l.env a')) ctx) VU
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
    => (0 _ : TcMode)
    -> ContextIndex
    -> Named Type
    where
    Lin : (Tc m)
      => TelTypechecker m md (gs, ns, bs) [<]
    (:<) : (Tc m)
      => (c : TelTypechecker m md (gs, ns, bs) ps)
      -> (p : (Name, Typechecker m md (gs, ns ++ ps, bs ++ ps) (gs, ns ++ ps, bs ++ ps)))
      -> TelTypechecker m md (gs, ns, bs) (ps :< fst p)
      
tel : (Tc m) => {auto _ : IsTmMode md}
  -> TelTypechecker m md (gs, ns, bs) ps
  -> Context gs ns bs
  -> m (Context gs (ns ++ ps) (bs ++ ps), Tel (VTy gs) ps bs)
tel [<] ctx = pure (ctx, [<])
tel ((:<) ts (n, t)) ctx = do
  (ctx', ts') <- tel ts ctx
  t' <- check t ctx' VU
  let vty = eval ctx'.local.env t'
  pure (mapLocal (\l => Bind l n vty) ctx', ts' :< (n, vty))
  
tel' : (Tc m) => {auto _ : IsTmMode md}
  -> TelTypechecker m md (gs, [<], [<]) ps
  -> Context gs [<] [<]
  -> m (Context gs ps ps, Tel (VTy gs) ps [<])
tel' ts ctx = do
  (ctx', te) <- tel ts ctx
  pure (apLeftMMRR {f = Context} ctx', te)

public export
caseOf : (Tc m)
  => (s : Typechecker m Infer (gs, ns, bs) (gs, ns, bs))
  -> IrrNameListN 2 (BranchTypechecker m md (gs, ns, bs))
  -> Typechecker m md (gs, ns, bs) (gs, ns, bs)
caseOf = ?caseOfImpl

public export
defItem : (Tc m)
  => (n : Name)
  -> (params : TelTypechecker m Check (gs, [<], [<]) ps)
  -> (ty : TmTypechecker m Check (gs, ps, ps))
  -> (tm : TmTypechecker m Infer (gs :< (ps ** MkGlobName n DefGlob), ps, ps))
  -> Typechecker m Item (gs, [<], [<]) (gs :< (ps ** MkGlobName n DefGlob), [<], [<])
defItem n params ty tm = InItem $ \ctx => do
  (ctx', params') <- tel' params ctx
  ty' <- check ty ctx' VU
  let vty = eval ctx'.local.env ty'
  let Val ps = ctx'.local.names
  tm' <- check tm (extendGlobal (\sig => sig :< Def (MkDefItem n params' vty Nothing)) ctx') (globWeaken vty)
  pure (extendGlobal (\sig => sig :< Def (MkDefItem n params' vty (Just tm'))) ctx)

public export
primItem : (Tc m)
  => (n : Name)
  -> (params : TelTypechecker m Check (gs, [<], [<]) ps)
  -> (ty : TmTypechecker m Check (gs, ps, ps))
  -> Typechecker m Item (gs, [<], [<]) (gs :< (ps ** MkGlobName n PrimGlob), [<], [<])
primItem n params ty = InItem $ \ctx => do
  (ctx', params') <- tel' params ctx
  ty' <- check ty ctx' VU
  let Val ps = ctx'.local.names
  let vty = eval ctx'.local.env ty'
  pure (extendGlobal (\sig => sig :< Prim (MkPrimItem n params' vty)) ctx)
  