module Core.Definitions

import Data.DPair
import Decidable.Equality
import Data.SnocList.Elem
import Data.SnocList
import Data.Singleton

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Conversion

namespace Sig
  public export
  data Sig : GlobNamed Type

namespace Item
  public export
  data Item : Sig gs -> Type

  public export
  data ItemIn : Sig gs' -> Item sig -> Type

namespace DefItem
  public export
  record DefItem (0 sig : Sig gs)

namespace DataItem
  public export
  record DataItem (0 sig : Sig gs)

Data' : (d : DataItem sig) -> Item sig

namespace CtorItem
  public export
  record CtorItem {0 sig : Sig gs} {d : DataItem sig'} (di : ItemIn sig (Data' d))

namespace PrimItem
  public export
  record PrimItem (0 sig : Sig gs)

namespace Item

  public export
  data Item : Sig gs -> Type where
    Def : DefItem sig -> Item sig
    Data : DataItem sig -> Item sig
    Prim : PrimItem sig -> Item sig
    Ctor : {0 d : DataItem sig'} -> {di : ItemIn sig (Data' d)} -> CtorItem {d = d} di -> Item sig

Data' d = Data d

namespace DefItem
  public export
  record DefItem (0 sig : Sig gs) where
    constructor MkDefItem
    name : Name
    {ps : Names}
    params : Tel (VTy gs) ps [<]
    ty : VTy gs ps
    tm : Maybe (STm (gs :< (ps ** MkGlobName name DefGlob)) ps)

namespace DataItem
  public export
  record DataItem (0 sig : Sig gs) where
    constructor MkDataItem
    name : Name
    {ps : Names}
    {is : Names}
    params : Tel (VTy gs) ps [<]
    indices : Tel (VTy gs) is ( ps)

namespace CtorItem
  public export
  record CtorItem {0 sig : Sig gs} {d : DataItem sig'} (di : ItemIn sig (Data' d)) where
    constructor MkCtorItem
    name : Name
    {as : Names}
    args : Tel (VTy gs) as d.ps
    rets : Spine (VTm gs) d.is (d.ps ++ as)

namespace PrimItem
  public export
  record PrimItem (0 sig : Sig gs) where
    constructor MkPrimItem
    name : Name
    {ps : Names}
    params : Tel (VTy gs) ps [<]
    ty : VTy gs ( ps)

public export
(.name) : Item sig -> Name
(.name) (Def d) = d.name
(.name) (Data d) = d.name
(.name) (Prim p) = p.name
(.name) (Ctor c) = c.name

public export
(.arity) : {sig : Sig gs} -> Item sig -> Names

public export
(.globName) : (i : Item sig) -> GlobName i.arity
(.globName) (Def d) = MkGlobName d.name DefGlob
(.globName) (Data d) = MkGlobName d.name DataGlob
(.globName) (Prim p) = MkGlobName p.name PrimGlob
(.globName) (Ctor c) = MkGlobName c.name CtorGlob

namespace Sig
  public export
  data Sig : GlobNamed Type where
    Lin : Sig Lin
    (:<) : (sig : Sig gs) -> (i : Item sig) -> Sig (gs :< (i.arity ** i.globName))
    
  public export
  (++) : Sig gs -> Sig gs' -> Sig (gs ++ gs')
  (++) sig [<] = sig
  (++) sig (sig' :< i) = sig ++ sig' :< i

namespace Item
  data ItemIn : (sig : Sig gs) -> Item sig' -> Type where
    Here : {0 i : Item sig} -> ItemIn (sig :< i) i
    There : {0 i : Item sig} -> {0 j : Item sig'} -> ItemIn sig j -> ItemIn (sig :< i) j

public export
globNameElem : {0 sig : Sig gs} -> {0 i : Item sig'} -> ItemIn sig i -> Elem (i.arity ** i.globName) gs
globNameElem Here = Here
globNameElem (There p) = There (globNameElem p)

public export
globWeakenByItem : GlobWeaken f => {0 sig : Sig gs} -> {0 sig' : Sig gs'} -> {0 i : Item sig'} -> ItemIn sig i -> f gs' ns -> f gs ns
globWeakenByItem = ?globWeakenByItemPrf

public export
getItem : {sig : Sig gs} -> {0 i : Item sig'} -> ItemIn sig i -> Singleton i
getItem {sig = (sig :< i)} p = case p of
  Here => Val i
  There p => getItem {sig = sig} p

public export
getDataItem : {sig : Sig gs} -> {0 d : DataItem sig'} -> ItemIn sig (Data d) -> Singleton d
getDataItem i = case getItem i of
  Val (Data d) => Val d

(.arity) (Def d) = d.ps
(.arity) (Data d) = d.ps ++ d.is
(.arity) (Prim p) = p.ps
(.arity) (Ctor {di = di} c) = let d = getDataItem di in d.value.ps ++ c.as

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
vGlob : {sig : Sig gs} -> {0 i : Item sig'} -> ItemIn sig i -> Spine (VTm gs) i.arity bs -> VTm gs bs
vGlob {sig = sig} {i = i} p sp = let it = getItem p in
  VGlob (MkGlobNameIn it.value.globName (rewrite it.identity in globNameElem p)) (rewrite it.identity in sp)

public export
mapLocal : (Ctx gs ns bs -> Ctx gs ns' bs') -> Context gs ns bs -> Context gs ns' bs'
mapLocal f c = MkContext c.global (f c.local)

public export
[globWeakenCtx] GlobWeaken (\gs => \ns => Ctx gs ns bs) where
  globWeaken Lin = Lin
  globWeaken (Bind ctx n ty) = Bind (globWeaken @{globWeakenCtx} ctx) n (globWeaken ty)
  globWeaken (Def ctx n ty tm) = Def (globWeaken @{globWeakenCtx} ctx) n (globWeaken ty) (globWeaken tm)

public export
extendGlobal : (Sig gs -> Sig (gs :< g)) -> Context gs ns bs -> Context (gs :< g) ns bs
extendGlobal f (MkContext sig ctx) = MkContext (f sig) (globWeaken @{globWeakenCtx} ctx)

public export
(.binds) : Ctx gs ns bs -> Singleton bs
(.binds) Lin = Val [<]
(.binds) (Bind ctx n _) = let Val bs = ctx.binds in Val $ bs :< n
(.binds) (Def ctx _ _ _) = ctx.binds

public export
(.names) : Ctx gs ns bs -> Singleton ns
(.names) Lin = Val [<]
(.names) (Bind ctx n _) = let Val ns = ctx.names in Val $ ns :< n
(.names) (Def ctx n _ _) = let Val ns = ctx.names in Val $ ns :< n

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
  Yes Refl => Just (IZ, thisTerm ctx, Here)
  No q => map (\(i, t, e) => (IS i, weaken t, There e)) (lookupLocal ctx' m)
lookupLocal ctx@(Def ctx' n ty tm) m = case decEq n m of
  Yes Refl => Just (IZ, thisTerm ctx, Here)
  No q => map (\(i, t, e) => (IS i, t, There e)) (lookupLocal ctx' m)

public export
itemTy : {sig : Sig us} -> Item sig -> VTy us [<]
itemTy (Def d) = vPis' d.params d.ty
itemTy (Data d) = vPis' d.params (vPis d.params.size d.indices VU)
itemTy (Prim p) = vPis' p.params p.ty
itemTy (Ctor {di = di} c) = case getDataItem di of
  Val d =>
    let binds = (globWeakenByItem @{globWeakenForTel} di d.params) ++. c.args in
    let paramSp = vHeres' d.params.size in
    let retSp = weakenN c.args.size paramSp ++ c.rets in
    let ret = vGlob di retSp in
    vPis' binds ret

public export
lookupItem : Size bs -> Sig gs -> (n : Name) -> Maybe (DPair Names (\ps => (GlobNameIn gs ps, VTy gs bs)))
lookupItem s [<] _ = Nothing
lookupItem s sig@((:<) sig' it) m = case decEq it.name m of
  Yes p => Just (it.arity ** (MkGlobNameIn it.globName Here, weakenTo s (globWeaken (itemTy it))))
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
