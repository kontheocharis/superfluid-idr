module Core.Values

import Data.SnocList

import Common
import Context
import Core.Syntax

public export
VTy : Names -> Type

public export
data VTm : Names -> Type

namespace Env
  public export
  data Env : Names -> Names -> Type where
    Lin : Env n [<]
    (:<) : Env ns ms -> VTm ns -> Env ns (ms :< m)

public export
(.size) : Env ns ms -> Size ms
(.size) [<] = SZ
(.size) (xs :< _) = SS (xs.size)

public export
record Closure (u : Name) (ns : Names) where
  constructor Cl
  {0 ks : Names}
  env : Env ns ks
  tm : STm (ks :< u)

data VTm where
  VLam : (n : Name) -> Closure n ns -> VTm ns
  VRigid : Lvl ns -> Spine VTm ps ns -> VTm ns
  VPi : (n : Name) -> VTy ns -> Closure n ns -> VTm ns
  VU : VTm ns

VTy = VTm

public export
VVar : Lvl n -> VTm n
VVar l = VRigid l [<]

public export
lookup : Env n m -> Idx m -> VTm n
lookup (xs :< x) IZ = x
lookup (xs :< x) (IS i) = lookup xs i

public export
idEnv : Size ns -> Env ns ns

public export
weakenEnv : Env ns ms -> Env (ns :< n) ms

public export
weakenSpine : Spine VTm ps ns -> Spine VTm ps (ns :< n)

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
  weaken (VRigid i sp) = VRigid (weaken i) (weakenSpine sp)
  weaken (VPi n a cl) = VPi n (weaken a) (weaken cl)
  weaken VU = VU

idEnv SZ = [<]
idEnv (SS n) = growEnv n (idEnv n)

weakenEnv [<] = [<]
weakenEnv (xs :< x) = weakenEnv xs :< weaken x

weakenSpine [<] = [<]
weakenSpine (xs :< x) = weakenSpine xs :< weaken x

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
