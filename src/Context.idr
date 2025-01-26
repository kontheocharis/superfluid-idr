module Context

import Common
import Data.SnocList
import Data.Nat

import Decidable.Equality
import Control.Function
import Data.DPair
import Data.SnocList.Elem

public export
record Name where
  constructor MkName
  name : String

public export
Injective MkName where
  injective Refl = Refl

public export
DecEq Name where
  decEq (MkName n) (MkName n') = decEqCong $ decEq n n'

public export
0 Names : Type
Names = SnocList Name

public export
0 Named : Type -> Type
Named t = (0 _ : Names) -> t

public export
data Size : Named Type where
  SZ : Size Lin
  SS : Size ns -> Size (ns :< n)

public export
(.size) : (ns : Names) -> Size ns
(.size) [<] = SZ
(.size) (xs :< x) = SS xs.size

public export
data GlobKind : Type where
  CtorGlob : GlobKind
  DataGlob : GlobKind
  DefGlob : GlobKind
  PrimGlob : GlobKind

public export
record GlobName (0 ps : Names) where
  constructor MkGlobName
  name : Name
  kind : GlobKind

public export
DecEq GlobKind where
  decEq CtorGlob CtorGlob = Yes Refl
  decEq DataGlob DataGlob = Yes Refl
  decEq DefGlob DefGlob = Yes Refl
  decEq PrimGlob PrimGlob = Yes Refl
  decEq CtorGlob DataGlob = No (\p => case p of
      Refl impossible
    )
  decEq CtorGlob DefGlob = No (\p => case p of
      Refl impossible
    )
  decEq CtorGlob PrimGlob = No (\p => case p of
      Refl impossible
    )
  decEq DataGlob CtorGlob = No (\p => case p of
      Refl impossible
    )
  decEq DataGlob DefGlob = No (\p => case p of
      Refl impossible
    )
  decEq DataGlob PrimGlob = No (\p => case p of
      Refl impossible
    )
  decEq DefGlob CtorGlob = No (\p => case p of
      Refl impossible
    )
  decEq DefGlob DataGlob = No (\p => case p of
      Refl impossible
    )
  decEq DefGlob PrimGlob = No (\p => case p of
      Refl impossible
    )
  decEq PrimGlob CtorGlob = No (\p => case p of
      Refl impossible
    )
  decEq PrimGlob DataGlob = No (\p => case p of
      Refl impossible
    )
  decEq PrimGlob DefGlob = No (\p => case p of
      Refl impossible
    )

public export
Biinjective MkGlobName where
  biinjective Refl = (Refl, Refl)

public export
DecEq (GlobName ps) where
  decEq (MkGlobName n k) (MkGlobName n' k') = decEqCong2 (decEq n n') (decEq k k')

public export
0 GlobNames : Type
GlobNames = SnocList (DPair Names (\ps => GlobName ps))

public export
0 GlobNamed : Type -> Type
GlobNamed t = (0 _ : GlobNames) -> t

public export
record GlobNameIn (0 gs : GlobNames) (0 ps : Names) where
  constructor MkGlobNameIn
  name : GlobName ps
  0 contained : Elem (ps ** name) gs

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
interface GlobWeaken (f : GlobNamed (Named Type)) where
  globWeaken : f gs ns -> f (gs :< g) ns

public export
GlobWeaken GlobNameIn where
  globWeaken (MkGlobNameIn n e) = MkGlobNameIn n (There e)

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

public export
(+) : Size ns -> Size ms -> Size (ns ++ ms)
(+) m SZ = m
(+) m (SS n) = SS (m + n)
