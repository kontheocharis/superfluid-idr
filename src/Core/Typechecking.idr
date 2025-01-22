module Core.Typechecking

import Data.DPair
import Decidable.Equality
import Data.SnocList.Elem

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Conversion

public export
data Mode = Check | Infer

public export
data Context : Names -> Names -> Type

public export
data TcError : Type where
  ExpectedPi : TcError
  Mismatch : VTm bs -> VTm bs -> TcError
  NameNotFound : (n : Name) -> TcError

public export
interface (Monad m) => Tc m where
  tcError : TcError -> m a

public export
data Context where
  Empty : Context Lin Lin
  Bind : (ctx : Context ns bs) -> (n : Name) -> (t : VTy bs) -> Context (ns :< n) (bs :< n)
  Def : (ctx : Context ns bs) -> (n : Name) -> (t : VTy bs) -> (tm : VTm bs) -> Context (ns :< n) bs

public export
(.bindsSize) : Context ns bs -> Size bs
(.bindsSize) Empty = SZ
(.bindsSize) (Bind s _ _) = SS s.bindsSize
(.bindsSize) (Def s _ _ _) = s.bindsSize

public export
(.size) : Context ns bs -> Size ns
(.size) Empty = SZ
(.size) (Bind s _ _) = SS s.size
(.size) (Def s _ _ _) = SS s.size

public export
(.env) : Context ns bs -> Env bs ns
(.env) Empty = LinEnv
(.env) (Bind ctx _ _) = growEnv ctx.bindsSize ctx.env
(.env) (Def ctx _ _ tm) = ctx.env :< tm

public export
thisTerm : Context (ns :< n) bs -> VTerm bs
thisTerm (Bind ctx _ ty) = MkVTerm (weaken ty) (VVar (lastLvl ctx.bindsSize))
thisTerm (Def ctx _ ty tm) = MkVTerm ty tm

public export
lookup : Context ns bs -> Idx ns -> VTerm bs
lookup (Bind ctx _ _) (IS i) = weaken (lookup ctx i)
lookup (Def ctx _ _ _) (IS i) = lookup ctx i
lookup ctx IZ = thisTerm ctx

public export
lookupName : Context ns bs -> (n : Name) -> Maybe (Idx ns, VTerm bs, Elem n ns)
lookupName Empty _ = Nothing
lookupName ctx@(Bind ctx' n ty) m = case decEq n m of
  Yes p => Just (IZ, thisTerm ctx, rewrite p in Here)
  No q => map (\(i, t, e) => (IS i, weaken t, There e)) (lookupName ctx' m)
lookupName ctx@(Def ctx' n ty tm) m = case decEq n m of
  Yes p => Just (IZ, thisTerm ctx, rewrite p in Here)
  No q => map (\(i, t, e) => (IS i, t, There e)) (lookupName ctx' m)

public export
data Typechecker : (m : Type -> Type) -> (Tc m) => Mode -> Names -> Names -> Type where
  Checker : (Tc m) => (Context ns bs -> VTy bs -> m (STm ns)) -> Typechecker m Check ns bs
  Inferer : (Tc m) => (Context ns bs -> m (STm ns, VTy bs)) -> Typechecker m Infer ns bs

public export
convertOrError : (Tc m) => Context ns bs -> VTy bs -> VTy bs -> m ()
convertOrError ctx a b = if convert ctx.bindsSize a b then pure () else tcError (Mismatch a b)

public export
switch : (Tc m) => Typechecker m Infer ns bs -> Typechecker m Check ns bs
switch (Inferer f) = Checker $ \ctx => \ty => do
  (t, ty') <- f ctx
  convertOrError ctx ty ty'
  pure t

public export
check : (Tc m) => Typechecker m md ns bs -> Context ns bs -> VTy bs -> m (STm ns)
check (Checker f) ctx ty = f ctx ty
check (Inferer f) ctx ty = let Checker f' = switch (Inferer f) in f' ctx ty

public export
infer : (Tc m) => Typechecker m Infer ns bs -> Context ns bs -> m (STm ns, VTy bs)
infer (Inferer f) ctx = f ctx

public export
var : (Tc m) => Idx ns -> Typechecker m Infer ns bs
var i = Inferer $ \ctx => case lookup ctx i of
    MkVTerm ty _ => pure (SVar i, ty)

public export
named : (Tc m) => Name -> Typechecker m Infer ns bs
named n = Inferer $ \ctx => case lookupName ctx n of
    Just (i, MkVTerm _ ty, _) => pure (SVar i, ty)
    Nothing => tcError (NameNotFound n)

public export
lam : (Tc m) => (n : Name) -> Typechecker m md (ns :< n) (bs :< n) -> Typechecker m Check ns bs
lam n f = Checker $ \ctx => \ty => case ty of
  VPi n' a b => do
    t <- check f (Bind ctx n a) (applyRen ctx.bindsSize b)
    pure (SLam n t)
  _ => tcError ExpectedPi

public export
typedLam : (Tc m) => (n : Name) -> Typechecker m md ns bs -> Typechecker m Infer (ns :< n) (bs :< n) -> Typechecker m Infer ns bs
typedLam n a (Inferer f) = Inferer $ \ctx => do
    a' <- check a ctx VU
    let va = eval ctx.env a'
    (t, b) <- f (Bind ctx n va)
    pure (SLam n t, VPi n va (closeVal (idEnv ctx.bindsSize) b))

public export
app : (Tc m) => Typechecker m Infer ns bs -> Typechecker m md ns bs -> Typechecker m Infer ns bs
app (Inferer f) g = Inferer $ \ctx => do
  (f', a) <- f ctx
  case a of
    VPi n a b => do
      g' <- check g ctx a
      pure (SApp f' g', b $$ eval ctx.env g')
    _ => tcError ExpectedPi

public export
pi : (Tc m) => (n : Name) -> Typechecker m md ns bs -> Typechecker m md' (ns :< n) (bs :< n) -> Typechecker m Infer ns bs
pi n a b = Inferer $ \ctx => do
  a' <- check a ctx VU
  b' <- check b (Bind ctx n (eval ctx.env a')) VU
  pure (SPi n a' b', VU)

public export
u : (Tc m) => Typechecker m Infer ns bs
u = Inferer $ \ctx => pure (SU, VU)
