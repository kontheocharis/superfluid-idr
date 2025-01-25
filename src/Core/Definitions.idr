module Core.Definitions

import Data.DPair
import Decidable.Equality
import Data.SnocList.Elem

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
  record DefItem (0 ctx : Sig gs) where
    constructor MkDefItem
    name : String
    params : Tel (VTy gs) ps [<]
    ty : VTy gs ps
    tm : STm (gs :< (ps ** MkGlobName n DefGlob)) ps

namespace CtorItem
  public export
  record CtorItem (0 gs : GlobNames) (0 is : Names) (0 ns : Names) where
    constructor MkCtorItem
    name : String
    args : Tel (VTy gs) as ns
    rets : Spine (VTm gs) is (ns ++ as)

namespace DataItem
  public export
  record DataItem (0 ctx : Sig gs) where
    constructor MkDataItem
    name : String
    params : Tel (VTy gs) ps [<]
    indices : Tel (VTy gs) is ps
    ctors : Tel (CtorItem gs is) cs ps

namespace PrimItem
  public export
  record PrimItem (0 ctx : Sig gs) where
    constructor MkDataItem
    name : String
    pp : Tel (VTy gs) ps [<]
    ty : VTy gs ps
    tm : VTm (gs :< (ps ** MkGlobName n DefGlob)) ps

namespace Sig
  public export
  data Sig : GlobNamed Type where
    Lin : Sig Lin
    Def : (ctx : Sig gs)
      -> DefItem ctx
      -> Sig (gs :< (ps ** MkGlobName n DefGlob))
    Data : (ctx : Sig gs)
      -> DataItem ctx
      -> Sig (gs :< (ps ** MkGlobName n DataGlob))
    Prim : (ctx : Sig gs)
      -> PrimItem ctx
      -> Sig (gs :< (ps ** MkGlobName n PrimGlob))

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
lookup : Ctx gs ns bs -> Idx ns -> VTerm gs bs
lookup (Bind ctx _ _) (IS i) = weaken (lookup ctx i)
lookup (Def ctx _ _ _) (IS i) = lookup ctx i
lookup ctx IZ = thisTerm ctx

public export
lookupName : Ctx gs ns bs -> (n : Name) -> Maybe (Idx ns, VTerm gs bs, Elem n ns)
lookupName [<] _ = Nothing
lookupName ctx@(Bind ctx' n ty) m = case decEq n m of
  Yes p => Just (IZ, thisTerm ctx, rewrite p in Here)
  No q => map (\(i, t, e) => (IS i, weaken t, There e)) (lookupName ctx' m)
lookupName ctx@(Def ctx' n ty tm) m = case decEq n m of
  Yes p => Just (IZ, thisTerm ctx, rewrite p in Here)
  No q => map (\(i, t, e) => (IS i, t, There e)) (lookupName ctx' m)
