module Syntax

import Common
import Context

public export
0 STy : Ctx -> Type

public export
data STm : Ctx -> Type where
  SVar : Idx n -> STm n
  SLam : (n : Name) -> STm (ns :< n) -> STm ns
  SApp : STm ns -> STm ns -> STm ns
  SPi : (n : Name) -> STy ns -> STy (ns :< n) -> STm ns
  SLit : Lit -> STm ns

STy = STm

