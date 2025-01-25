module Common

import Decidable.Equality
import Control.Function
import Data.DPair
import Data.SnocList.Elem

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
0 Names : Type
Names = SnocList Name

public export
0 Named : Type -> Type
Named t = (0 _ : Names) -> t

public export
data Size : Named Type where
  SZ : Size Lin
  SS : Size ns -> Size (ns :< n)

namespace GlobName
  public export
  data GlobName : Named Type where
    CtorGlob : String -> GlobName ps
    DataGlob : String -> GlobName ps
    DefGlob : String -> GlobName ps

  public export
  (.name) : GlobName ns -> String
  (.name) (CtorGlob n) = n
  (.name) (DataGlob n) = n
  (.name) (DefGlob n) = n


-- public export
-- Injective CtorGlob where
--   injective Refl = Refl

-- public export
-- Injective DataGlob where
--   injective Refl = Refl

-- public export
-- Injective DefGlob where
--   injective Refl = Refl

public export
DecEq (GlobName ps) where
  decEq a b = ?holeGlobNameDecEq
  -- decEq (DataGlob n) (DataGlob n') = decEqCong $ decEq n n'
  -- decEq (DefGlob n) (DefGlob n') = decEqCong $ decEq n n'
  -- decEq (CtorGlob _) (DataGlob _) = No (\p => case p of {
  --   Refl impossible
  -- })
  -- decEq (CtorGlob _) (DefGlob _) = No (\p => case p of {
  --   Refl impossible
  -- })
  -- decEq (DataGlob _) (CtorGlob _) = No (\p => case p of {
  --   Refl impossible
  -- })
  -- decEq (DataGlob _) (DefGlob _) = No (\p => case p of {
  --   Refl impossible
  -- })
  -- decEq (DefGlob _) (CtorGlob _) = No (\p => case p of {
  --   Refl impossible
  -- })
  -- decEq (DefGlob _) (DataGlob _) = No (\p => case p of {
  --   Refl impossible
  -- })


public export
0 GlobNames : Type
GlobNames = SnocList (Exists (\ps => GlobName ps))

public export
0 GlobNamed : Type -> Type
GlobNamed t = (0 _ : GlobNames) -> t

public export
0 GlobNameIn : (0 _ : GlobNames) -> (0 _ : Names) -> Type
GlobNameIn gs ps = Subset (GlobName ps) (\g => Elem (Evidence ps g) gs)

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
