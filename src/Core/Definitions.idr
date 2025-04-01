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
import Core.Weakening

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

public export
Data' : (d : DataItem sig) -> Item sig

record DataGlobNameIn (0 gs : GlobNames) (0 ps : Names) (0 is : Names) where
  constructor MkDataGlobNameIn
  unwrap : GlobNameInFor DataGlob gs (ps ++ is)

record CtorGlobNameIn (0 gs : GlobNames) (0 ps : Names) (0 cs : Names) where
  constructor MkCtorGlobNameIn
  unwrap : GlobNameInFor CtorGlob gs (ps ++ cs)

public export
[globWeakenForDataGlobNameIn] GlobWeaken (\gs => \ns => DataGlobNameIn gs ps ns) where
  globWeaken (MkDataGlobNameIn u) = MkDataGlobNameIn (globWeaken @{globWeakenForGlobNameInFor} u)
  globReorder (MkDataGlobNameIn u) = MkDataGlobNameIn (globReorder @{globWeakenForGlobNameInFor} u)

globWeakenForDataGlobNameIn' : DataGlobNameIn gs ps is -> DataGlobNameIn (gs :< g) ps is
globWeakenForDataGlobNameIn' x = globWeaken @{globWeakenForDataGlobNameIn} x

namespace CtorItem
  public export
  record CtorItem (0 sig : Sig gs)

namespace PrimItem
  public export
  record PrimItem (0 sig : Sig gs)

namespace DataItem
    public export
    record DataItem (0 sig : Sig gs) where
        constructor MkDataItem
        name : Name
        {ps : Names}
        {is : Names}
        params : VTel gs ps [<]
        indices : VTel gs is ( ps)

public export
Ctor' : CtorItem sig -> Item sig

namespace CtorGlobNamesIn
  public export
  data CtorGlobNamesIn : (0 gs : GlobNames) -> (0 dg : DataGlobNameIn gs ps is) -> Type
    where
    Lin : CtorGlobNamesIn gs dg
    (:<) : {0 dg : DataGlobNameIn gs ps is} -> CtorGlobNamesIn gs dg
      -> {0 cs : Names}
      -> CtorGlobNameIn gs ps cs
      -> CtorGlobNamesIn gs dg

public export
record ElimItem (0 sig : Sig gs) where
  constructor MkElimItem
  name : Name
  {ps : Names}
  {is : Names}
  dg : DataGlobNameIn gs ps is
  csg : CtorGlobNamesIn gs dg

namespace Item
  public export
  data Item : Sig gs -> Type where
    Def : DefItem sig -> Item sig
    Data : DataItem sig -> Item sig
    Prim : PrimItem sig -> Item sig
    Ctor : CtorItem sig -> Item sig
    Elim : ElimItem sig -> Item sig

Data' d = Data d

Ctor' c = Ctor c

namespace DefItem
  public export
  record DefItem (0 sig : Sig gs) where
    constructor MkDefItem
    name : Name
    {ps : Names}
    params : VTel gs ps [<]
    ty : VTy gs ps
    tm : Maybe (STm (gs :< (ps ** MkGlobName name DefGlob)) ps)

namespace CtorItem
  public export
  record CtorItem (0 sig : Sig gs) where
    constructor MkCtorItem
    name : Name
    {as : Names}
    {ps : Names}
    dg : DataGlobNameIn gs ps is
    args : VTel gs as ps
    rets : Spine (VTm gs) is (ps ++ as)

namespace PrimItem
  public export
  record PrimItem (0 sig : Sig gs) where
    constructor MkPrimItem
    name : Name
    {ps : Names}
    params : VTel gs ps [<]
    ty : VTy gs ps

public export
(.name) : Item sig -> Name
(.name) (Def d) = d.name
(.name) (Data d) = d.name
(.name) (Prim p) = p.name
(.name) (Ctor c) = c.name
(.name) (Elim e) = e.name

public export
(.arityRel) : {sig : Sig gs} -> Item sig -> Names

public export
(.arity) : {sig : Sig gs} -> Item sig -> Names

public export
(.globName) : (i : Item sig) -> GlobName i.arity
(.globName) (Def d) = MkGlobName d.name DefGlob
(.globName) (Data d) = MkGlobName d.name DataGlob
(.globName) (Prim p) = MkGlobName p.name PrimGlob
(.globName) (Ctor c) = MkGlobName c.name CtorGlob
(.globName) (Elim e) = MkGlobName e.name ElimGlob

namespace Sig
  public export
  data Sig : GlobNamed Type where
    Lin : Sig Lin
    (:<) : (sig : Sig gs) -> (i : Item sig) -> Sig (gs :< (i.arity ** i.globName))

  (.size) : Sig gs -> Size gs

namespace Item
  public export
  data ItemIn : (sig : Sig gs) -> Item sig' -> Type where
    Here : {0 i : Item sig} -> ItemIn (sig :< i) i
    There : {0 i : Item sig} -> {0 j : Item sig'} -> ItemIn sig j -> ItemIn (sig :< i) j

public export
getItem : {sig : Sig gs} -> {0 i : Item sig'} -> ItemIn sig i -> Singleton i
getItem {sig = (sig :< i)} p = case p of
  Here => Val i
  There p => getItem {sig = sig} p

public export
getDataItem : {sig : Sig gs} -> {0 d : DataItem sig'} -> ItemIn sig (Data d) -> Singleton d
getDataItem i = case getItem i of
  Val (Data d) => Val d

namespace CtorGlobNamesIn
  public export
  (.arity) : CtorGlobNamesIn gs d -> Names
  (.arity) [<] = [<]
  (.arity) ((:<) csi {cs} ci) = csi.arity :< (fst ci.unwrap).name.name

  public export
  (.size) : (csi : CtorGlobNamesIn gs d) -> Size csi.arity
  (.size) [<] = SZ
  (.size) (cs :< _) = SS (cs.size)

(.arity) (Def d) = d.ps
(.arity) (Data d) = d.ps ++ d.is
(.arity) (Prim p) = p.ps
(.arity) (Ctor c) = c.ps ++ c.as
(.arity) (Elim t) = t.ps ++ [< MkName "E"] ++ t.csg.arity ++ t.is ++ [< MkName "s"]

public export
globWeakenDefItem : DefItem sig -> DefItem (sig :< i)
globWeakenDefItem (MkDefItem n params ty tm) = MkDefItem n (globWeakenVTel params) (globWeaken ty) (map (globReorder . globWeaken) tm)

public export
globWeakenDataItem : DataItem sig -> DataItem (sig :< i)
globWeakenDataItem (MkDataItem n params indices) = MkDataItem n (globWeakenVTel params) (globWeakenVTel indices)

public export
globWeakenPrimItem : PrimItem sig -> PrimItem (sig :< i)
globWeakenPrimItem (MkPrimItem n params ty) = MkPrimItem n (globWeakenVTel params) (globWeaken ty)

public export
globWeakenByItem : GlobWeaken f
  => {0 sig : Sig gs}
  -> {0 sig' : Sig gs'}
  -> {0 i : Item sig'}
  -> ItemIn sig i
  -> f gs' ns
  -> f gs ns
globWeakenByItem Here u = globWeaken u
globWeakenByItem (There p) u = globWeaken (globWeakenByItem p u)

public export
globWeakenDefItemTm : GlobWeaken f
  => {0 sig : Sig gs}
  -> {0 sig' : Sig gs'}
  -> {0 d : DefItem sig'}
  -> ItemIn sig (Def d)
  -> f (gs' :< (d.ps ** MkGlobName d.name DefGlob)) ns
  -> f gs ns
globWeakenDefItemTm Here y = y
globWeakenDefItemTm @{f} (There x) y = globWeaken $ globWeakenDefItemTm @{f} x y

public export
globWeakenCtorItem : CtorItem sig -> CtorItem (sig :< i)
globWeakenCtorItem (MkCtorItem n dg args rets) =
  MkCtorItem n (MkDataGlobNameIn (globWeaken (fst dg.unwrap) ** (let m = snd dg.unwrap in ?f))) (globWeakenVTel args) (globWeakenVTmSpine rets)

public export
globWeakenItem : Item sig -> Item (sig :< i)

public export
globWeakenElimItem : ElimItem sig -> ElimItem (sig :< i)

globWeakenItem (Def d) = Def (globWeakenDefItem d)
globWeakenItem (Data d) = Data (globWeakenDataItem d)
globWeakenItem (Prim p) = Prim (globWeakenPrimItem p)
globWeakenItem (Ctor c) = Ctor (globWeakenCtorItem c)
globWeakenItem (Elim t) = Elim (globWeakenElimItem t)

public export
globWeakenCtors : {0 dg : DataGlobNameIn gs ps is} -> CtorGlobNamesIn {ps} {is} gs dg
  -> CtorGlobNamesIn {ps} {is} (gs :< g) (globWeakenForDataGlobNameIn' dg)
globWeakenCtors [<] = [<]
globWeakenCtors ((:<) {cs = c} csg cg) = globWeakenCtors csg :< MkCtorGlobNameIn (globWeaken @{globWeakenForGlobNameInFor} cg.unwrap)

globWeakenElimItem (MkElimItem n dg csg) = MkElimItem n (globWeakenForDataGlobNameIn' dg) (globWeakenCtors csg)

public export
globNameElem : {0 sig : Sig gs} -> {0 i : Item sig'} -> ItemIn sig i -> Elem (i.arity ** i.globName) gs
globNameElem Here = Here
globNameElem (There p) = There (globNameElem p)

public export
globNameIn : {0 sig : Sig gs} -> {i : Item sig'} -> ItemIn sig i -> GlobNameIn gs i.arity
globNameIn {i} ii = MkGlobNameIn i.globName (globNameElem ii)

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
asGlobEnv : Sig gs -> GlobEnv gs

public export covering
vGlob : {sig : Sig gs} -> {0 i : Item sig'} -> Size bs -> ItemIn sig i -> Spine (VTm gs) i.arity bs -> VTm gs bs
vGlob {sig = sig} {i = i} sz p sp = let it = getItem p in
  eval (asGlobEnv sig)
    idEnv
    (SGlob
      (MkGlobNameIn it.value.globName (rewrite it.identity in globNameElem p))
      (rewrite it.identity in quoteSpine (asGlobEnv sig) sz sp))

public export
mapLocal : (Ctx gs ns bs -> Ctx gs ns' bs') -> Context gs ns bs -> Context gs ns' bs'
mapLocal f c = MkContext c.global (f c.local)

public export
[globWeakenCtx] GlobWeaken (\gs => \ns => Ctx gs ns bs) where
  globWeaken Lin = Lin
  globWeaken (Bind ctx n ty) = Bind (globWeaken @{globWeakenCtx} ctx) n (globWeaken ty)
  globWeaken (Def ctx n ty tm) = Def (globWeaken @{globWeakenCtx} ctx) n (globWeaken ty) (globWeaken tm)

  globReorder Lin = Lin
  globReorder (Bind ctx n ty) = Bind (globReorder @{globWeakenCtx} ctx) n (globReorder ty)
  globReorder (Def ctx n ty tm) = Def (globReorder @{globWeakenCtx} ctx) n (globReorder ty) (globReorder tm)

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
(.globEnv) : Context gs ns bs -> GlobEnv gs
(.globEnv) (MkContext sig ctx) = asGlobEnv sig

public export
thisTerm : Ctx gs (ns :< n) bs -> VTerm gs bs
thisTerm (Bind ctx _ ty) = MkVTerm (weaken ty) (VVar (lastLvl ctx.bindsSize))
thisTerm (Def ctx _ ty tm) = MkVTerm ty tm

public export
getIdx : Ctx gs ns bs -> Idx ns -> VTerm gs bs
getIdx (Bind ctx _ _) (IS i) = weaken (getIdx ctx i)
getIdx (Def ctx _ _ _) (IS i) = getIdx ctx i
getIdx ctx IZ = thisTerm ctx

record GetGlob (0 ps : Names) (0 sig : Sig gs) (0 k : GlobKind) where
  constructor MkGetGlob
  {0 gs' : GlobNames}
  {0 sig' : Sig gs'}
  item : Item sig'
  itemIn : ItemIn sig item
  sameArity : item.arity = ps
  sameKind : item.globName.kind = k

record GetDataGlob (0 ps : Names) (0 is : Names) (0 sig : Sig gs) where
  constructor MkGetDataGlob
  {0 gs' : GlobNames}
  {0 sig' : Sig gs'}
  item : DataItem sig'
  itemIn : ItemIn sig (Data item)
  sameParams : item.ps = ps
  sameIndices : item.is = is

record GetCtorGlob (0 ps : Names) (0 as : Names) (0 sig : Sig gs) where
  constructor MkGetCtorGlob
  {0 gs' : GlobNames}
  {0 sig' : Sig gs'}
  item : CtorItem sig'
  itemIn : ItemIn sig (Ctor item)
  sameParams : item.ps = ps
  sameArgs : item.as = as

public export
getGlob : (sig : Sig gs) -> GlobNameInFor k gs ps -> GetGlob ps sig k
getGlob [<] (MkGlobNameIn _ _) impossible
getGlob sig@(sig' :< i) (MkGlobNameIn _ Here ** q) = MkGetGlob i Here Refl q
getGlob sig@(sig' :< i) (MkGlobNameIn n (There p) ** Refl) = case getGlob sig' (MkGlobNameIn n p ** Refl) of
  MkGetGlob i' p' Refl q' => MkGetGlob i' (There p') Refl q'

public export
getDataGlob : (sig : Sig gs) -> DataGlobNameIn gs ps is -> GetDataGlob ps is sig
getDataGlob sig g = case getGlob sig g.unwrap of
  MkGetGlob (Data d) itemIn sameArity Refl => MkGetDataGlob d itemIn ?fp ?fi
  MkGetGlob (Ctor _) {} impossible
  MkGetGlob (Elim _) {} impossible
  MkGetGlob (Def _) {} impossible
  MkGetGlob (Prim _) {} impossible

public export
getCtorGlob : (sig : Sig gs) -> CtorGlobNameIn gs ps as -> GetCtorGlob ps as sig
getCtorGlob sig g = case getGlob sig g.unwrap of
  MkGetGlob (Ctor c) itemIn sameArity Refl => MkGetCtorGlob c itemIn ?fp' ?fi'
  MkGetGlob (Data _) {} impossible
  MkGetGlob (Elim _) {} impossible
  MkGetGlob (Def _) {} impossible
  MkGetGlob (Prim _) {} impossible


public export
lookupLocal : Ctx gs ns bs -> (n : Name) -> Maybe (Idx ns, VTerm gs bs, Elem n ns)
lookupLocal [<] _ = Nothing
lookupLocal ctx@(Bind ctx' n ty) m = case decEq n m of
  Yes Refl => Just (IZ, thisTerm ctx, Here)
  No q => map (\(i, t, e) => (IS i, weaken t, There e)) (lookupLocal ctx' m)
lookupLocal ctx@(Def ctx' n ty tm) m = case decEq n m of
  Yes Refl => Just (IZ, thisTerm ctx, Here)
  No q => map (\(i, t, e) => (IS i, t, There e)) (lookupLocal ctx' m)

public export covering
motiveTy : (sig : Sig gs) -> DataGlobNameIn gs ps is -> VTy gs ps
motiveTy sig dg with (getDataGlob sig dg)
  _ | MkGetDataGlob d di Refl Refl =
    let is = (globWeakenByItem @{globWeakenForVTel} di d.indices) in
    let psisSize = d.params.size + d.indices.size in
    let dat = vGlob psisSize di (vHeres' psisSize) in
    vPis d.params.size is (vPis psisSize (singleton (MkName "M") psisSize dat) VU)

public export covering
methodsTel : (sig : Sig gs)
  -> {0 dg : DataGlobNameIn gs ps is}
  -> (csg : CtorGlobNamesIn gs dg)
  -> VTel gs csg.arity (ps :< m)
methodsTel sig [<] = [<]
methodsTel sig (csg :< cg) with (getCtorGlob sig cg)
  _ | MkGetCtorGlob (MkCtorItem name dg' args' rets') ci Refl Refl
    with (getDataGlob sig (globWeakenByItem @{globWeakenForDataGlobNameIn} ci dg'))
    _ | MkGetDataGlob (MkDataItem dataName params' indices') di Refl Refl =
      let args = globWeakenByItem @{globWeakenForVTel} ci args' in
      let rets = globWeakenByItem @{globWeakenForSpine} ci rets' in
      let params = globWeakenByItem @{globWeakenForVTel} di params' in
      let binds = weakenVTel args in
      let paramSp = vHeres' params.size in
      let rets = subSpine (growEnvN (SS params.size) args.size (proj params.size)) rets in
      let datRetSp = weakenN args.size (weaken paramSp) ++ rets in
      let dat = vGlob ((SS paramSp.size) + args.size) di datRetSp in
      let motiveApplied = VRigid (weakenN args.size LZ) ((:<) {n = MkName "M"} rets dat) in
      let ms' = methodsTel sig csg in
      let method = vPis (SS paramSp.size) binds motiveApplied in
      (ms' :< ((fst cg.unwrap).name.name, closeVal csg.size (idEnv @{SS params.size}) (weakenN csg.size method)))

public export covering
sectionTy :  (sig : Sig gs)
  -> (dg : DataGlobNameIn gs ps is)
  -> (csg : CtorGlobNamesIn gs dg)
  -> VTy gs ((ps :< m) ++ csg.arity)
sectionTy sig dg csg with (getDataGlob sig dg)
  _ | MkGetDataGlob (MkDataItem _ params indices) di Refl Refl =
    let indices = (globWeakenByItem @{globWeakenForVTel} di indices) in
    let paramSp = weakenN @{weakenForSpine} indices.size (weakenSpine (vHeres' params.size)) in
    let indexSp = vHeres (SS params.size) indices.size in
    let subjectTy = vGlob (SS params.size + indices.size) di (paramSp ++ indexSp) in
    let motiveSec = weaken (VRigid (weakenN indices.size (lastLvl params.size)) indexSp) in
    weakenN csg.size $ vPis (SS params.size) (weakenVTel indices)
      (vPis (SS params.size + indices.size)
        (singleton (MkName "s") (SS params.size + indices.size) subjectTy) motiveSec)

public export covering
itemTy : {sig : Sig gs} -> Item sig -> VTy gs [<]
itemTy (Def d) = vPis' d.params d.ty
itemTy (Data d) = vPis' d.params (vPis d.params.size d.indices VU)
itemTy (Prim p) = vPis' p.params p.ty
itemTy {sig} (Ctor c) = case getDataGlob sig c.dg of
  MkGetDataGlob (MkDataItem _ params indices) di Refl Refl =>
    let binds = (globWeakenByItem @{globWeakenForVTel} di params) ++. c.args in
    let paramSp = vHeres' params.size in
    let retSp = weakenN c.args.size paramSp ++ c.rets in
    let ret = vGlob (paramSp.size + c.args.size) di retSp in
    vPis' binds ret
itemTy {gs} {sig} (Elim (MkElimItem _ dg csg)) with (getDataGlob {gs} sig dg)
 _ | MkGetDataGlob (MkDataItem _ {ps} params' _) di Refl Refl =
    let params = globWeakenByItem @{globWeakenForVTel} di params' in
    let motive = motiveTy sig dg in
    let methods = methodsTel sig csg in
    let section = sectionTy sig dg csg in
    vPis' params (vPis ps.size (singleton (MkName "E") ps.size motive) (vPis (SS ps.size) methods section))

public export covering
lookupItem : Size bs -> Sig gs -> (n : Name) -> Maybe (ps : Names ** (GlobNameIn gs ps, VTy gs bs))
lookupItem s [<] _ = Nothing
lookupItem s sig@(sig' :< it) m = case decEq it.name m of
  Yes p => Just (it.arity ** (MkGlobNameIn it.globName Here, weakenTo s (globWeaken (itemTy it))))
  No q => map (\(ps ** (g, ty)) => (ps ** (MkGlobNameIn g.name (There g.contained), globWeaken ty))) (lookupItem s sig' m)

public export
data LookupResult : GlobNamed (Named (Named Type)) where
  FoundItem : (ps : Names) -> GlobNameIn gs ps -> VTy gs bs -> LookupResult gs ns bs
  FoundLocal : Idx ns -> VTerm gs bs -> Elem n ns -> LookupResult gs ns bs
  NotFound : LookupResult gs ns bs

public export covering
lookupName : Context gs ns bs -> (n : Name) -> LookupResult gs ns bs
lookupName (MkContext sig ctx) m = case lookupLocal ctx m of
    Just (i, t, e) => FoundLocal i t e
    Nothing => case lookupItem ctx.bindsSize sig m of
      Just (ps ** (g, t)) => FoundItem ps g t
      Nothing => NotFound

public export
unfold : Sig gs -> GlobNameIn gs ps -> Maybe (STm gs ps)
unfold sig n = case getGlob sig n of
  MkGetGlob (Def (MkDefItem name params ty (Just tm))) i Refl => Just $ globWeakenDefItemTm i tm
  _ => Nothing

asGlobEnv sig = MkGlobEnv (\n => unfold sig n)

public export covering
unfoldFully : Sig gs -> VTm gs bs -> VTm gs bs
unfoldFully sig (VGlob n sp pp (Just t')) = t'
unfoldFully sig t = t
