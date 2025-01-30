module Extension.Eliminators

import Common
import Context
import Core.Syntax
import Core.Values
import Extension.Inductive

IsCtor : Idx ns -> Names -> Type

data Ctor : Names -> Names -> Type where
  MkCtor : (i : Idx ns) -> IsCtor i ps -> Ctor ps ns

-- data Pat : Names -> Type where
--   PatVar : Idx ns -> Pat ns
--   PatCtor : Ctor ps ns -> Spine Pat ps ns -> Pat ns

-- data CoPat : Names -> Type where
--   CoPatVar : Idx ns -> CoPat ns

-- record Constraint (ns : Names) where
--   constructor MkConstraint
--   term : STm ns
--   pat : Pat ns
--   ty : VTy ns

-- record PartialClause (ns : Names) where
--   constructor MkPartialClause
--   constraints : SnocList (Constraint ns)
--   copats : SnocList (CoPat ns)
--   rhs : STm ns

