module Common

import Decidable.Equality
import Control.Function

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
record GlobName where
  constructor MkGlobName
  name : String

public export
Injective MkGlobName where
  injective Refl = Refl

public export
DecEq GlobName where
  decEq (MkGlobName n) (MkGlobName n') = decEqCong $ decEq n n'

public export
Names : Type
Names = SnocList Name

public export
Named : Type -> Type
Named t = (0 _ : Names) -> t

public export
GlobNames : Type
GlobNames = SnocList GlobName

public export
GlobNamed : Type -> Type
GlobNamed t = (0 _ : GlobNames) -> t

-- | A literal
public export
data Lit
  = StringLit String
  | CharLit Char
  | NatLit Nat

public export
Show Lit where
  show (StringLit s) = show s
  show (CharLit c) = show c
  show (NatLit n) = show n

public export
error : String -> a
error s = assert_total $ idris_crash s
