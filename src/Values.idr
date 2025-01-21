module Values

import Data.SnocList

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
(.size) : Env ns ms -> Size ms
(.size) LinEnv = SZ
(.size) (xs :< _) = SS (xs.size)

public export
record Closure (u : Name) (ns : Ctx) where
  constructor Cl
  {0 ks : Ctx}
  env : Env ns ks
  tm : STm (ks :< u)

data VTm where
  VLam : (n : Name) -> Closure n ns -> VTm ns
  VRigid : Lvl n -> Spine (VTm n) -> VTm n
  VPi : (n : Name) -> VTy ns -> Closure n ns -> VTm ns
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

public export
idEnv : Size ns -> Env ns ns

public export
liftEnv : Env ns ms -> Env (ns :< n) ms

public export
growEnv : (s : Size ns) -> Env ns ms -> Env (ns :< n) (ms :< m)
growEnv s env = liftEnv env :< VVar (lastLvl s)

public export
(ms : Ctx) => Lift (\ns => Env ns ms) where
  lift = liftEnv

public export
(n : Name) => Lift (Closure n) where
  lift (Cl env t) = Cl (liftEnv env) t

public export
Lift VTm where
  lift (VLam n cl) = VLam n (lift cl)
  lift (VRigid i sp) = VRigid (lift i) (map lift sp)
  lift (VPi n a cl) = VPi n (lift a) (lift cl)
  lift (VLit l) = VLit l

idEnv SZ = LinEnv
idEnv (SS n) = growEnv n (idEnv n)

liftEnv LinEnv = LinEnv
liftEnv (xs :< x) = liftEnv xs :< lift x

public export
chainEnv : Env ns ms -> Env ms ks -> Env ns ks
