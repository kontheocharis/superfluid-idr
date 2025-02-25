module Common

import Data.Singleton
import Data.SnocList
import Data.String
import Data.List
import Data.Fin
import Data.Nat
import Data.List1

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

-- Source location
public export
record Loc where
  constructor MkLoc
  src : List Char
  pos : Fin (length src)

public export
linesBefore : Loc -> List String
linesBefore loc = lines (substr 0 (finToNat loc.pos) (pack loc.src))

public export
dummyLoc : Loc
dummyLoc = MkLoc [' '] (FZ)

public export
(.row) : Loc -> Nat
(.row) loc = length (linesBefore loc)

public export
(.col) : Loc -> Nat
(.col) loc = case linesBefore loc of
  [] => 1
  (x::xs) => length (last (x::xs)) + 1

export
Show Loc where
  show m = "line " ++ show m.row ++ ", column " ++ show m.col

public export
error : String -> a
error s = assert_total $ idris_crash s

public export
(.value) : {0 x : a} -> Singleton x -> a
(.value) (Val x) = x

public export
(.identity) : {0 x : a} -> (s : Singleton x) -> s.value = x
(.identity) (Val y) = Refl

public export
composeN : Nat -> (a -> a) -> a -> a
composeN Z f x = x
composeN (S k) f x = f (composeN k f x)

public export
apLeftR : {auto n : Nat} -> {f : (0 _ : a) -> (0 _ : SnocList b) -> Type} -> f p ([<] ++ q) -> f p q
apLeftR x = rewrite sym $ appendLinLeftNeutral q in x

public export
apLeftL : {f : (0 _ : SnocList a) -> (0 _ : b) -> Type} -> f ([<] ++ p) q -> f p q
apLeftL x = rewrite sym $ appendLinLeftNeutral p in x

public export
apLeftRL : {f : (0 _ : SnocList a) -> (0 _ : SnocList b) -> Type} -> f ([<] ++ p) ([<] ++ q) -> f p q
apLeftRL x = rewrite sym $ appendLinLeftNeutral q in rewrite sym $ appendLinLeftNeutral p in x

public export
apLeftMM : {f : a -> (0 _ : SnocList b) -> (0 _ : c) -> Type} -> f p ([<] ++ q) r -> f p q r
apLeftMM x = rewrite sym $ appendLinLeftNeutral q in x

public export
apLeftMMRR : {f : (0 _ : a) -> (0 _ : SnocList b) -> (0 _ : SnocList c) -> Type} -> f p ([<] ++ q) ([<] ++ r) -> f p q r
apLeftMMRR x = rewrite sym $ appendLinLeftNeutral q in rewrite sym $ appendLinLeftNeutral r in x

public export
apLeft : {f : (0 _ : SnocList a) -> Type} -> f ([<] ++ p) -> f p
apLeft x = rewrite sym $ appendLinLeftNeutral p in x
