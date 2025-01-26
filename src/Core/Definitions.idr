module Core.Definitions

import Data.DPair
import Decidable.Equality
import Data.SnocList.Elem
import Data.SnocList

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Conversion

namespace Sig
  public export
  data Sig : GlobNamed Type

namespace DefItem
  public export
  record DefItem (0 gs : GlobNames) where
    constructor MkDefItem
    name : Name
    ps : Names
    params : Tel (VTy gs) ps [<]
    ty : VTy gs ps
    tm : STm (gs :< (ps ** MkGlobName n DefGlob)) ps

namespace CtorItem
  public export
  record CtorItem (0 gs : GlobNames) (0 is : Names) (0 ns : Names) where
    constructor MkCtorItem
    name : Name
    ps : Names
    args : Tel (VTy gs) as ns
    rets : Spine (VTm gs) is (ns ++ as)

namespace DataItem
  public export
  record DataItem (0 gs : GlobNames) where
    constructor MkDataItem
    name : Name
    ps : Names
    params : Tel (VTy gs) ps [<]
    indices : Tel (VTy gs) is ps
    ctors : Tel (CtorItem gs is) cs ps

namespace PrimItem
  public export
  record PrimItem (0 gs : GlobNames) where
    constructor MkDataItem
    name : Name
    ps : Names
    params : Tel (VTy gs) ps [<]
    ty : VTy gs ps

namespace Item
  public export
  data Item : GlobName ps -> (0 ps : Names) -> GlobNamed Type where
    Def : (d : DefItem gs) -> Item (MkGlobName d.name DefGlob) d.ps gs
    Data : (d : DataItem gs) -> Item (MkGlobName d.name DataGlob) d.ps gs
    Prim : (p : PrimItem gs) -> Item (MkGlobName p.name PrimGlob) p.ps gs

(.name) : Item n ps gs -> Name
(.name) (Def d) = d.name
(.name) (Data d) = d.name
(.name) (Prim p) = p.name

(.params) : Item n ps gs -> Tel (VTy gs) ps [<]
(.params) (Def d) = d.params
(.params) (Data d) = d.params
(.params) (Prim p) = p.params

namespace Sig
  public export
  data Sig : GlobNamed Type where
    Lin : Sig Lin
    (:<) : Sig gs -> {ps : Names} -> {g : GlobName ps} -> Item g ps gs -> Sig (gs :< (ps ** g))

public export
data Ctx : GlobNamed (Named (Named Type)) where
  Lin : Ctx gs Lin Lin
  Bind : (ctx : Ctx gs ns bs) -> (n : Name) -> (t : VTy gs bs) -> Ctx gs (ns :< n) (bs :< n)
  Def : (ctx : Ctx gs ns bs) -> (n : Name) -> (t : VTy gs bs) -> (tm : VTm gs bs) -> Ctx gs (ns :< n) bs

public export
record Context (0 gs : GlobNames) (0 ns : Names) (0 bs : Names) where
  constructor MkContext
  global : Sig gs
  local : Ctx gs ns bs

public export
mapLocal : (Ctx gs ns bs -> Ctx gs ns' bs') -> Context gs ns bs -> Context gs ns' bs'
mapLocal f c = MkContext c.global (f c.local)

public export
(.bindsSize) : Ctx gs ns bs -> Size bs
(.bindsSize) [<] = SZ
(.bindsSize) (Bind s _ _) = SS s.bindsSize
(.bindsSize) (Def s _ _ _) = s.bindsSize

public export
(.size) : Ctx gs ns bs -> Size ns
(.size) [<] = SZ
(.size) (Bind s _ _) = SS s.size
(.size) (Def s _ _ _) = SS s.size

public export
(.env) : Ctx gs ns bs -> Env gs bs ns
(.env) [<] = [<]
(.env) (Bind ctx _ _) = growEnv ctx.bindsSize ctx.env
(.env) (Def ctx _ _ tm) = ctx.env :< tm

public export
thisTerm : Ctx gs (ns :< n) bs -> VTerm gs bs
thisTerm (Bind ctx _ ty) = MkVTerm (weaken ty) (VVar (lastLvl ctx.bindsSize))
thisTerm (Def ctx _ ty tm) = MkVTerm ty tm

public export
getIdx : Ctx gs ns bs -> Idx ns -> VTerm gs bs
getIdx (Bind ctx _ _) (IS i) = weaken (getIdx ctx i)
getIdx (Def ctx _ _ _) (IS i) = getIdx ctx i
getIdx ctx IZ = thisTerm ctx

public export
lookupLocal : Ctx gs ns bs -> (n : Name) -> Maybe (Idx ns, VTerm gs bs, Elem n ns)
lookupLocal [<] _ = Nothing
lookupLocal ctx@(Bind ctx' n ty) m = case decEq n m of
  Yes p => Just (IZ, thisTerm ctx, rewrite p in Here)
  No q => map (\(i, t, e) => (IS i, weaken t, There e)) (lookupLocal ctx' m)
lookupLocal ctx@(Def ctx' n ty tm) m = case decEq n m of
  Yes p => Just (IZ, thisTerm ctx, rewrite p in Here)
  No q => map (\(i, t, e) => (IS i, t, There e)) (lookupLocal ctx' m)

itemTy : Item n ps gs -> VTy gs [<]
itemTy (Def d) = vPis SZ d.params (rewrite appendLinLeftNeutral d.ps in d.ty)
itemTy (Data d) = vPis SZ d.params (rewrite appendLinLeftNeutral d.ps in vPis d.params.size d.indices VU)
itemTy (Prim p) = vPis SZ p.params (rewrite appendLinLeftNeutral p.ps in p.ty)

public export
lookupItem : Size bs -> Sig gs -> (n : Name) -> Maybe (DPair Names (\ps => (GlobNameIn gs ps, VTy gs bs)))
lookupItem s [<] _ = Nothing
lookupItem s sig@((:<) {ps = ps} {g = g} sig' it) m = case decEq it.name m of
  Yes p => Just (ps ** (MkGlobNameIn g Here, weakenTo s (globWeaken (itemTy it))))
  No q => map (\(ps ** (g, ty)) => (ps ** (MkGlobNameIn g.name (There g.contained), globWeaken ty))) (lookupItem s sig' m)

public export
data LookupResult : GlobNamed (Named (Named Type)) where
  FoundItem : (ps : Names) -> GlobNameIn gs ps -> VTy gs bs -> LookupResult gs ns bs
  FoundLocal : Idx ns -> VTerm gs bs -> Elem n ns -> LookupResult gs ns bs
  NotFound : LookupResult gs ns bs

public export
lookupName : Context gs ns bs -> (n : Name) -> LookupResult gs ns bs
lookupName (MkContext sig ctx) m = case lookupLocal ctx m of
    Just (i, t, e) => FoundLocal i t e
    Nothing => case lookupItem ctx.bindsSize sig m of
      Just (ps ** (g, t)) => FoundItem ps g t
      Nothing => NotFound
