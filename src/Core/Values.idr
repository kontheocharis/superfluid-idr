module Core.Values

import Data.SnocList
import Data.DPair

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
weakenEnv : Env gs ns ms -> Env gs (ns :< n) ms

public export
weakenSpine : Spine (VTm gs) ps ns -> Spine (VTm gs) ps (ns :< n)

public export
growEnv : (s : Size ns) -> Env gs ns ms -> Env gs (ns :< n) (ms :< m)
growEnv s env = weakenEnv env :< VVar (lastLvl s)

public export
Weaken (\ns => Env gs ns ms) where
  weaken = weakenEnv

public export
Weaken (Closure gs n) where
  weaken (Cl env t) = Cl (weakenEnv env) t

public export
Weaken (VTm gs) where
  weaken (VLam n cl) = VLam n (weaken cl)
  weaken (VRigid i sp) = VRigid (weaken i) (weakenSpine sp)
  weaken (VPi n a cl) = VPi n (weaken a) (weaken cl)
  weaken VU = VU
  weaken (VGlob n sp) = VGlob n (weakenSpine sp)

idEnv {s = SZ} = [<]
idEnv {s = (SS n)} = growEnv n (idEnv {s = n})

weakenEnv [<] = [<]
weakenEnv (xs :< x) = weakenEnv xs :< ?h1

weakenSpine [<] = [<]
weakenSpine (xs :< x) = weakenSpine xs :< ?h2

public export
chainEnv : Env gs ns ms -> Env gs ms ks -> Env gs ns ks

public export
record VTerm (0 gs : GlobNames) (0 bs : Names) where
  constructor MkVTerm
  ty : VTy gs bs
  tm : VTm gs bs

public export
Weaken (VTerm gs) where
  weaken v = MkVTerm (weaken v.ty) (weaken v.tm)
