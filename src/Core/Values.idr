module Core.Values

import Data.SnocList

import Common
import Context
import Core.Syntax

public export
VTy : Names -> Type

public export
Spine : Type -> Type

public export
SpineVec : Type -> Nat -> Type

public export
data VTm : Names -> Type

public export
data Env : Names -> Names -> Type where
  LinEnv : Env n Lin
  (:<) : Env ns ms -> VTm ns -> Env ns (ms :< m)

public export
(.size) : Env ns ms -> Size ms
(.size) LinEnv = SZ
(.size) (xs :< _) = SS (xs.size)

public export
record Closure (u : Name) (ns : Names) where
  constructor Cl
  {0 ks : Names}
  env : Env ns ks
  tm : STm (ks :< u)

data VTm where
  VLam : (n : Name) -> Closure n ns -> VTm ns
  VRigid : Lvl n -> Spine (VTm n) -> VTm n
  VPi : (n : Name) -> VTy ns -> Closure n ns -> VTm ns
  VU : VTm ns

VTy = VTm

Spine = SnocList

public export
VVar : Lvl n -> VTm n
VVar l = VRigid l Lin

public export
lookup : Env n m -> Idx m -> VTm n
lookup (xs :< x) IZ = x
lookup (xs :< x) (IS i) = lookup xs i

public export
idEnv : Size ns -> Env ns ns

public export
weakenEnv : Env ns ms -> Env (ns :< n) ms

public export
growEnv : (s : Size ns) -> Env ns ms -> Env (ns :< n) (ms :< m)
growEnv s env = weakenEnv env :< VVar (lastLvl s)

public export
(ms : Names) => Weaken (\ns => Env ns ms) where
  weaken = weakenEnv

public export
(n : Name) => Weaken (Closure n) where
  weaken (Cl env t) = Cl (weakenEnv env) t

public export
Weaken VTm where
  weaken (VLam n cl) = VLam n (weaken cl)
  weaken (VRigid i sp) = VRigid (weaken i) (map weaken sp)
  weaken (VPi n a cl) = VPi n (weaken a) (weaken cl)
  weaken VU = VU

idEnv SZ = LinEnv
idEnv (SS n) = growEnv n (idEnv n)

weakenEnv LinEnv = LinEnv
weakenEnv (xs :< x) = weakenEnv xs :< weaken x

public export
chainEnv : Env ns ms -> Env ms ks -> Env ns ks

public export
record VTerm (ns : Names) where
  constructor MkVTerm
  ty : VTy ns
  tm : VTm ns

public export
Weaken VTerm where
  weaken (MkVTerm tm ty) = MkVTerm (weaken tm) (weaken ty)
