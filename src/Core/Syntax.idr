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
  public export
  data Spine : (Named Type) -> Named (Named Type) where

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

namespace Tel
  public export
  data Tel : (Named Type) -> Named (Named Type) where
    Lin : Tel f [<] ns
    (:<) : (c : Tel f ps ns) -> (p : (Name, f (ns ++ ps))) -> Tel f (ps :< fst p) ns

  public export
  (++) : Tel f' ps' ns' -> Tel f' qs' (ns' ++ ps') -> Tel f' (ps' ++ qs') ns'
  (++) te [<] = te
  (++) te ((:<) {ps = ps} te' (n, t)) = (te ++ te') :< (n, rewrite appendAssociative ns' ps' ps in t)

  export infixr 5 ++.

  public export
  (++.) : Tel f ps [<] -> Tel f qs ps -> Tel f (ps ++ qs) [<]
  (++.) a b = a ++ (rewrite appendLinLeftNeutral ps in b)

namespace Spine
  data Spine where
    Lin : Spine f [<] ns
    (:<) : (c : Spine f ps ns) -> f ns -> Spine f (ps :< n) ns

  public export
  (++) : Spine f' ps' ns' -> Spine f' qs' ns' -> Spine f' (ps' ++ qs') ns'
  (++) te [<] = te
  (++) te ((:<) {ps = ps} te' t) = (te ++ te') :< t

  public export
  lastN : Size qs -> Spine f (ps ++ qs) ns -> Spine f qs ns
  lastN SZ p = [<]
  lastN (SS n) (te :< t) = lastN n te :< t

public export
Con : (Named Type) -> Named Type
Con f ps = Tel f ps [<]

public export
sPis : Tel (STy gs) ps ns -> STy gs (ns ++ ps) -> STy gs ns
sPis [<] b = b
sPis (as :< (n, a)) b = sPis as (SPi n a b)

public export
sLams : (ps : Names) -> STm gs (ns ++ ps) -> STm gs ns
sLams [<] b = b
sLams (as :< n) b = sLams as (SLam n b)

public export
(.size) : Tel f ps ns -> Size ps
(.size) [<] = SZ
(.size) (xs :< _) = SS (xs.size)
