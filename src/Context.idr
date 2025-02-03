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
Show Name where
  show (MkName n) = n

public export
Injective MkName where
  injective Refl = Refl

public export
DecEq Name where
  decEq (MkName n) (MkName n') = decEqCong $ decEq n n'
  
public export
Eq Name where
  (==) (MkName n) (MkName n') = n == n'

public export
0 Names : Type
Names = SnocList Name

public export
0 Named : Type -> Type
Named t = (0 _ : Names) -> t
  
public export
data Size : (0 _ : SnocList a) -> Type where
  SZ : Size Lin
  SS : Size us -> Size (us :< u)

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
  decEq CtorGlob DataGlob = No (\case Refl impossible)
  decEq CtorGlob DefGlob = No (\case Refl impossible)
  decEq CtorGlob PrimGlob = No (\case Refl impossible)
  decEq DataGlob CtorGlob = No (\case Refl impossible)
  decEq DataGlob DefGlob = No (\case Refl impossible)
  decEq DataGlob PrimGlob = No (\case Refl impossible)
  decEq DefGlob CtorGlob = No (\case Refl impossible)
  decEq DefGlob DataGlob = No (\case Refl impossible)
  decEq DefGlob PrimGlob = No (\case Refl impossible)
  decEq PrimGlob CtorGlob = No (\case Refl impossible)
  decEq PrimGlob DataGlob = No (\case Refl impossible)
  decEq PrimGlob DefGlob = No (\case Refl impossible)

public export
Biinjective MkGlobName where
  biinjective Refl = (Refl, Refl)

public export
DecEq (GlobName ps) where
  decEq (MkGlobName n k) (MkGlobName n' k') = decEqCong2 (decEq n n') (decEq k k')
  
public export
0 WithIrrNamesN : (n : Nat) -> composeN n Named Type -> Type
WithIrrNamesN 0 t = t
WithIrrNamesN (S n) t = Exists (\ns => WithIrrNamesN n (t ns))
  
public export
0 IrrNameListN : (n : Nat) -> composeN n Named Type -> Type
IrrNameListN n t = SnocList (WithIrrNamesN n t)
  
public export
0 NameList : Named Type -> Type
NameList t = SnocList (DPair Names (\ns => t ns))

public export
0 GlobNames : Type
GlobNames = NameList GlobName

public export
0 GlobNamed : Type -> Type
GlobNamed t = (0 _ : GlobNames) -> t

public export
record GlobNameIn (0 gs : GlobNames) (0 ps : Names) where
  constructor MkGlobNameIn
  name : GlobName ps
  0 contained : Elem (ps ** name) gs

public export
GlobKindNameIn : (kind : GlobKind) -> (0 gs : GlobNames) -> (0 ps : Names) -> Type
GlobKindNameIn kind gs ps = Subset (GlobNameIn gs ps) (\(MkGlobNameIn n e) => kind = n.kind)

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
interface Weaken (0 f : Named Type) where
  weaken : f ns -> f (ns :< n)

  weakenN : Size ms -> f ns -> f (ns ++ ms)
  weakenN SZ x = x
  weakenN (SS n) x = weaken (weakenN n x)

  weakenTo : Size ns -> f [<] -> f ns
  weakenTo SZ x = x
  weakenTo (SS n) x = weaken (weakenTo n x)

public export
interface GlobWeaken (0 f : GlobNamed (Named Type)) where
  globWeaken : f gs ns -> f (gs :< g) ns

  globReorder : f (gs :< g :< g') ns -> f (gs :< g' :< g) ns

  globWeakenN : Size gs' -> f gs ns -> f (gs ++ gs') ns
  globWeakenN SZ x = x
  globWeakenN (SS n) x = globWeaken (globWeakenN n x)

  globWeakenTo : Size gs -> f [<] ns -> f gs ns
  globWeakenTo SZ x = x
  globWeakenTo (SS n) x = globWeaken (globWeakenTo n x)

public export
GlobWeaken GlobNameIn where
  globWeaken (MkGlobNameIn n e) = MkGlobNameIn n (There e)

  globReorder (MkGlobNameIn n e) = MkGlobNameIn n (case e of
    There Here => Here
    There (There e) => There (There e)
    Here => There Here)

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
