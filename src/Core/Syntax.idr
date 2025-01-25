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

namespace Tel
  public export
  data Tel : (Named Type) -> Named (Named Type) where
    Lin : Tel f [<] ns
    (:<) : (c : Tel f ps ns) -> (p : (Name, f (ns ++ ps))) -> Tel f (ps :< fst p) ns

namespace Spine
  data Spine where
    Lin : Spine f [<] ns
    (:<) : (c : Spine f ps ns) -> f ns -> Spine f (ps :< n) ns

public export
Con : (Named Type) -> Named Type
Con f ps = Tel f ps [<]

public export
(++) : Tel f' ps' ns' -> Tel f' qs' (ns' ++ ps') -> Tel f' (ps' ++ qs') ns'
(++) te [<] = te
(++) te ((:<) {ps = ps} te' (n, t)) = (te ++ te') :< (n, rewrite appendAssociative ns' ps' ps in t)

public export
sPis : Tel (STy gs) ps ns -> STy gs (ns ++ ps) -> STy gs ns
sPis [<] b = b
sPis (as :< (n, a)) b = sPis as (SPi n a b)

-- public export
-- data Sig : GlobNamed Type

-- public export
-- data SigItem : (0 _ : GlobName) -> (0 _ : Sig gs) -> Type

-- data Sig where
--   Lin : Sig [<]
--   (:<) : (si : Sig gs) -> SigItem g si -> Sig (gs :< g)
