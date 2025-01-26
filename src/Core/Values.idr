module Core.Values

import Data.SnocList
import Data.DPair
import Data.SnocList.Elem

import Common
import Context
import Core.Syntax

public export
VTy : GlobNamed (Named Type)

public export
data VTm : GlobNamed (Named Type)

namespace Env
  public export
  data Env : GlobNamed (Named (Named Type)) where
    Lin : Env gs n [<]
    (:<) : Env gs ns ms -> VTm gs ns -> Env gs ns (ms :< m)

public export
(.size) : Env gs ns ms -> Size ms
(.size) [<] = SZ
(.size) (xs :< _) = SS (xs.size)

public export
record Closure (0 gs : GlobNames) (0 u : Name) (0 ns : Names) where
  constructor Cl
  {0 ks : Names}
  env : Env gs ns ks
  tm : STm gs (ks :< u)

data VTm where
  VLam : (n : Name) -> Closure gs n ns -> VTm gs ns
  VRigid : Lvl ns -> Spine (VTm gs) ps ns -> VTm gs ns
  VPi : (n : Name) -> VTy gs ns -> Closure gs n ns -> VTm gs ns
  VU : VTm gs ns
  VGlob : (n : GlobNameIn gs ps) -> Spine (VTm gs) ps ns -> VTm gs ns

VTy = VTm

public export
VVar : Lvl ns -> VTm gs ns
VVar l = VRigid l [<]

public export
lookup : Env gs ns ms -> Idx ms -> VTm gs ns
lookup (xs :< x) IZ = x
lookup (xs :< x) (IS i) = lookup xs i

public export
idEnv : {auto s : Size ns} -> Env gs ns ns

public export
growEnv : (s : Size ns) -> Env gs ns ms -> Env gs (ns :< n) (ms :< m)

idEnv {s = SZ} = [<]
idEnv {s = (SS n)} = growEnv n (idEnv {s = n})

public export
Weaken (VTm gs)

public export
GlobWeaken VTm

public export
weakenEnv : Env gs ns ms -> Env gs (ns :< n) ms
weakenEnv [<] = [<]
weakenEnv (xs :< x) = weakenEnv xs :< weaken x

public export
globWeakenEnv : Env gs ns ms -> Env (gs :< g) ns ms
globWeakenEnv [<] = [<]
globWeakenEnv (xs :< x) = globWeakenEnv xs :< globWeaken x

growEnv s env = weakenEnv env :< VVar (lastLvl s)

public export
growEnvN : (s : Size ns) -> Size ps -> Env gs ns ms -> Env gs (ns ++ ps) (ms ++ ps)
growEnvN s SZ env = env
growEnvN s (SS n) env = growEnv (s + n) (growEnvN s n env)

public export
weakenSpine : Spine (VTm gs) ps ns -> Spine (VTm gs) ps (ns :< n)
weakenSpine [<] = [<]
weakenSpine (xs :< x) = weakenSpine xs :< weaken x

public export
globWeakenSpine : Spine (VTm gs) ps ns -> Spine (VTm (gs :< g)) ps ns
globWeakenSpine Lin = Lin
globWeakenSpine (sp :< t) = globWeakenSpine sp :< globWeaken t

public export
Weaken (\ns => Env gs ns ms) where
  weaken = weakenEnv

public export
GlobWeaken (\gs => \ns => Env gs ns ms) where
  globWeaken = globWeakenEnv

public export
Weaken (\ns => Spine (VTm gs) ps ns) where
  weaken = weakenSpine

public export
GlobWeaken (\gs => \ns => Spine (VTm gs) ps ns) where
  globWeaken = globWeakenSpine

public export
Weaken (Closure gs n) where
  weaken (Cl env t) = Cl (weakenEnv env) t

globWeakenClosure : Closure gs n ns -> Closure (gs :< g) n ns
globWeakenClosure (Cl env t) = Cl (globWeakenEnv env) (globWeaken t)

public export
GlobWeaken (\gs => \ns => Closure gs n ns) where
  globWeaken = globWeakenClosure

public export
Weaken (VTm gs) where
  weaken (VLam n cl) = VLam n (weaken cl)
  weaken (VRigid i sp) = VRigid (weaken i) (weaken sp)
  weaken (VPi n a cl) = VPi n (weaken a) (weaken cl)
  weaken VU = VU
  weaken (VGlob n sp) = VGlob n (weaken sp)

public export
GlobWeaken VTm where
  globWeaken (VLam n cl) = VLam n (globWeakenClosure cl)
  globWeaken (VRigid i sp) = VRigid i (globWeakenSpine sp)
  globWeaken (VPi n a cl) = VPi n (globWeaken a) (globWeakenClosure cl)
  globWeaken VU = VU
  globWeaken (VGlob n sp) = VGlob (globWeaken n) (globWeakenSpine sp)

public export
record VTerm (0 gs : GlobNames) (0 bs : Names) where
  constructor MkVTerm
  ty : VTy gs bs
  tm : VTm gs bs

public export
Weaken (VTerm gs) where
  weaken v = MkVTerm (weaken v.ty) (weaken v.tm)

public export
GlobWeaken VTerm where
  globWeaken v = MkVTerm (globWeaken v.ty) (globWeaken v.tm)

public export
vHeres : Size ns -> Size ps -> Spine (VTm gs) ps (ns ++ ps)
vHeres n SZ = [<]
vHeres n (SS r) = weaken (vHeres n r) :< VVar (lastLvl (n + r))
