module Context

import Common
import Data.SnocList
import Data.Nat

public export
data Idx : Named Type where
  IZ : Idx (ns :< n)
  IS : Idx ns -> Idx (ns :< n)

public export
data Lvl : Named Type where
  LZ : Lvl (ns :< n)
  LS : Lvl ns -> Lvl (ns :< n)

public export
Eq (Idx ns) where
  (==) IZ IZ = True
  (==) (IS i) (IS j) = i == j
  (==) _ _ = False

public export
Eq (Lvl ns) where
  (==) LZ LZ = True
  (==) (LS i) (LS j) = i == j
  (==) _ _ = False

public export
interface Weaken (f : Named Type) where
  weaken : f ns -> f (ns :< n)

public export
Weaken Lvl where
  weaken LZ = LZ
  weaken (LS i) = LS (weaken i)

public export
Weaken Idx where
  weaken IZ = IZ
  weaken (IS i) = IS (weaken i)

public export
getName : (ns : Names) -> Idx ns -> Name
getName (ns :< n) IZ = n
getName (ns :< n) (IS i) = getName ns i

public export
firstIdx : Size ns -> Idx (ns :< n)
firstIdx SZ = IZ
firstIdx (SS n) = IS (firstIdx n)

public export
lvlToIdx : Size ns -> Lvl ns -> Idx ns
lvlToIdx (SS n) LZ = firstIdx n
lvlToIdx (SS n) (LS l) = weaken $ lvlToIdx n l

public export
lastLvl : Size ns -> Lvl (ns :< n)
lastLvl SZ = LZ
lastLvl (SS n) = LS (lastLvl n)

public export
idxToLvl : Size ns -> Idx ns -> Lvl ns
idxToLvl (SS n) IZ = lastLvl n
idxToLvl (SS n) (IS i) = weaken $ idxToLvl n i
