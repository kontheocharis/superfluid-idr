module Core.Values

import Data.SnocList
import Data.DPair
import Data.SnocList.Elem
import Data.SnocList

import Common
import Context
import Core.Syntax

public export
VTy : GlobNamed (Named Type)

public export
data VTm : GlobNamed (Named Type)

namespace Env
  public export
  0 Env : GlobNamed (Named (Named Type))
  Env gs ns ms = Spine (VTm gs) ms ns

public export
(.size) : Env gs ns ms -> Size ms
(.size) [<] = SZ
(.size) (xs :< _) = SS (xs.size)

public export
record Closure (0 gs : GlobNames) (0 us : Names) (0 ns : Names) where
  constructor Cl
  {0 ks : Names}
  vars : Size us
  env : Env gs ns ks
  tm : STm gs (ks ++ us)
  

data VTm where
  VLam : (n : Name) -> Closure gs [< n] ns -> VTm gs ns
  VRigid : Lvl ns -> Spine (VTm gs) ps ns -> VTm gs ns
  VPi : (n : Name) -> VTy gs ns -> Closure gs [< n] ns -> VTm gs ns
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
record VTerm (0 gs : GlobNames) (0 bs : Names) where
  constructor MkVTerm
  ty : VTy gs bs
  tm : VTm gs bs

public export
data VTel : GlobNamed (Named (Named Type)) where
  Lin : VTel gs [<] ns
  (:<) : VTel gs ps ns -> (p : (Name, Closure gs ps ns)) -> VTel gs (ps :< fst p) ns
  
