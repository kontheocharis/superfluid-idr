module Common

public export
Name : Type
Name = String

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
