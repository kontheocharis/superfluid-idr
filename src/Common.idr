module Common

import Data.Singleton
import Data.SnocList

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
apLeftR : {auto n : Nat} -> {f : SnocList a -> SnocList b -> Type} -> f p ([<] ++ q) -> f p q
apLeftR x = rewrite sym $ appendLinLeftNeutral q in x

public export
apLeftL : {f : (0 _ : SnocList a) -> (0 _ : SnocList b) -> Type} -> f ([<] ++ p) q -> f p q
apLeftL x = rewrite sym $ appendLinLeftNeutral p in x

public export
apLeftRL : {f : (0 _ : SnocList a) -> (0 _ : SnocList b) -> Type} -> f ([<] ++ p) ([<] ++ q) -> f p q
apLeftRL x = rewrite sym $ appendLinLeftNeutral q in rewrite sym $ appendLinLeftNeutral p in x

public export
apLeftMM : {f : (0 _ : SnocList a) -> (0 _ : SnocList b) -> (0 _ : SnocList c) -> Type} -> f p ([<] ++ q) r -> f p q r
apLeftMM x = rewrite sym $ appendLinLeftNeutral q in x

public export
apLeftMMRR : {f : (0 _ : SnocList a) -> (0 _ : SnocList b) -> (0 _ : SnocList c) -> Type} -> f p ([<] ++ q) ([<] ++ r) -> f p q r
apLeftMMRR x = rewrite sym $ appendLinLeftNeutral q in rewrite sym $ appendLinLeftNeutral r in x

public export
apLeft : {f : (0 _ : SnocList a) -> Type} -> f ([<] ++ p) -> f p
apLeft x = rewrite sym $ appendLinLeftNeutral p in x