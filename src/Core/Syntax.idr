module Core.Syntax

import Common
import Context
import Data.SnocList

public export
0 STy : Names -> Type

public export
data STm : Names -> Type where
  SVar : Idx n -> STm n
  SLam : (n : Name) -> STm (ns :< n) -> STm ns
  SApp : STm ns -> (0 n : Name) -> STm ns -> STm ns
  SPi : (n : Name) -> STy ns -> STy (ns :< n) -> STm ns
  SU : STm ns
  SLet : (n : Name) -> STm ns -> STm (ns :< n) -> STm ns

STy = STm

namespace Tel
  public export
  data Tel : (Names -> Type) -> Names -> Names -> Type where
    Lin : Tel f [<] ns
    (:<) : (c : Tel f ps ns) -> (p : (Name, f (ns ++ ps))) -> Tel f (ps :< fst p) ns

namespace Spine
  public export
  data Spine : (Names -> Type) -> Names -> Names -> Type where
    Lin : Spine f [<] ns
    (:<) : (c : Spine f ps ns) -> f ns -> Spine f (ps :< n) ns

public export
Con : (Names -> Type) -> Names -> Type
Con f ps = Tel f ps [<]

public export
(++) : Tel f' ps' ns' -> Tel f' qs' (ns' ++ ps') -> Tel f' (ps' ++ qs') ns'
(++) te [<] = te
(++) te ((:<) {ps = ps} te' (n, t)) = (te ++ te') :< (n, rewrite appendAssociative ns' ps' ps in t)

public export
sPis : Tel STy ps ns -> STy (ns ++ ps) -> STy ns
sPis [<] b = b
sPis (as :< (n, a)) b = sPis as (SPi n a b)
