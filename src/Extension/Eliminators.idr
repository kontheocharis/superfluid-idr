module Extension.Eliminators

import Common
import Context
import Core.Syntax
import Core.Values
import Extension.Inductive
import Data.DPair

record Constraint (0 gs : GlobNames) (0 ns : Names) where
  constructor MkConstraint
  term : STm gs ns
  pat : SPat gs ns
  ty : VTy gs ns

data Elim : Names -> Type where
  ElimVar : Idx ns -> Elim ns

record PartialClause (0 gs : GlobNames) (0 ns : Names) where
  constructor MkPartialClause
  constraints : SnocList (Constraint gs ns)
  elims : SnocList (Elim ns)
  rhs : STm gs ns
