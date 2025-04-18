module Core.Syntax

import Common
import Context
import Data.SnocList
import Data.DPair

public export
0 STy : GlobNamed (Named Type)

public export
data STm : GlobNamed (Named Type)

namespace Spine

data STm where
  SVar : Idx ns -> STm gs ns
  SLam : (n : Name) -> STm gs (ns :< n) -> STm gs ns
  SApp : STm gs ns -> (0 n : Name) -> STm gs ns -> STm gs ns
  SPi : (n : Name) -> STy gs ns -> STy gs (ns :< n) -> STm gs ns
  SU : STm gs ns
  SLet : (n : Name) -> STm gs ns -> STm gs (ns :< n) -> STm gs ns
  SGlob : (n : GlobNameIn gs ps) -> Spine (STm gs) ps ns -> STm gs ns

STy = STm

public export
data IsPat : STm gs ns -> Type where
  SVarIsPat : IsPat (SVar i)
  SGlobIsPat : IsPat (SGlob n sp)

public export
0 SPat : GlobNamed (Named Type)
SPat gs ns = Subset (STm gs ns) IsPat

isPat : (s : STm gs ns) -> Dec (IsPat s)
isPat (SVar i) = Yes SVarIsPat
isPat (SGlob n sp) = Yes SGlobIsPat
isPat (SLam n t) = No (\case Refl impossible)
isPat (SApp f n a) = No (\case Refl impossible)
isPat (SPi n a b) = No (\case Refl impossible)
isPat SU = No (\case Refl impossible)
isPat (SLet n a b) = No (\case Refl impossible)

public export
sPis : Tel (STy gs) ps ns -> STy gs (ns ++ ps) -> STy gs ns
sPis [<] b = b
sPis (as :< (n, a)) b = sPis as (SPi n a b)

public export
sLams : (ps : Names) -> STm gs (ns ++ ps) -> STm gs ns
sLams [<] b = b
sLams (as :< n) b = sLams as (SLam n b)
