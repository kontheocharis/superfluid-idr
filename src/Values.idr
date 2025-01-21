module Values

import Common
import Context
import Syntax

public export
0 VTy : Ctx -> Type

public export
0 Spine : Type -> Type

public export
data VTm : Ctx -> Type

public export
data Env : Ctx -> Ctx -> Type where
  LinEnv : Env n Lin
  (:<) : Env ns ms -> VTm ns -> Env ns (ms :< m)

public export
data Closure : Ctx -> Ctx -> Type where
  Cl : Env ns ks -> STm (ks ++ us) -> Closure us ns

data VTm where
  VLam : (n : Name) -> Closure (Lin :< n) ns -> VTm ns
  VRigid : Lvl n -> Spine (VTm n) -> VTm n
  VPi : (n : Name) -> VTy ns -> Closure (Lin :< n) ns -> VTm ns
  VLit : Lit -> VTm ns

VTy = VTm

Spine = SnocList

public export
VVar : Lvl n -> VTm n
VVar l = VRigid l Lin

public export
lookup : Env n m -> Idx m -> VTm n
lookup (xs :< x) IZ = x
lookup (xs :< x) (IS i) = lookup xs i
