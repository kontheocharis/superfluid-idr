module Context

import Common
import Data.SnocList
import Data.Nat

public export
Ctx : Type
Ctx = SnocList Name

public export
data Size : Ctx -> Type where
  SZ : Size Lin
  SS : Size ns -> Size (ns :< n)

public export
data Idx : Ctx -> Type where
  IZ : Idx (ns :< n)
  IS : Idx ns -> Idx (ns :< n)

public export
data Lvl : Ctx -> Type where
  LZ : Lvl (ns :< n)
  LS : Lvl ns -> Lvl (ns :< n)

public export
interface Lift (f : Ctx -> Type) where
  lift : f ns -> f (ns :< n)

public export
Lift Lvl where
  lift LZ = LZ
  lift (LS i) = LS (lift i)

public export
Lift Idx where
  lift IZ = IZ
  lift (IS i) = IS (lift i)

public export
firstIdx : Size ns -> Idx (ns :< n)
firstIdx SZ = IZ
firstIdx (SS n) = IS (firstIdx n)

public export
lvlToIdx : Size ns -> Lvl ns -> Idx ns
lvlToIdx (SS n) LZ = firstIdx n
lvlToIdx (SS n) (LS l) = lift $ lvlToIdx n l

public export
lastLvl : Size ns -> Lvl (ns :< n)
lastLvl SZ = LZ
lastLvl (SS n) = LS (lastLvl n)

public export
idxToLvl : Size ns -> Idx ns -> Lvl ns
idxToLvl (SS n) IZ = lastLvl n
idxToLvl (SS n) (IS i) = lift $ idxToLvl n i
