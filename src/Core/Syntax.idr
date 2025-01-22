module Core.Syntax

import Common
import Context

public export
0 STy : Names -> Type

public export
data STm : Names -> Type where
  SVar : Idx n -> STm n
  SLam : (n : Name) -> STm (ns :< n) -> STm ns
  SApp : STm ns -> STm ns -> STm ns
  SPi : (n : Name) -> STy ns -> STy (ns :< n) -> STm ns
  SU : STm ns

STy = STm

