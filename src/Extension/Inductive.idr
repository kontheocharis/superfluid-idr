module Extension.Inductive

import Data.SnocList

import Common
import Context
import Core.Syntax

record Inductive (sort : Names -> Type) (is : Names) (ss : Names) (ns : Names) where
  constructor MkInductive
  ind : Name
  indices : Tel STy is ns
  sig : Tel STy ss (ns :< ind)

elimName : Name -> Name
elimName n = "elim-" ++ n

inductiveCtors : (te : Inductive STy is ss ns) -> Tel STy ss (ns :< te.ind)
inductiveCtors te = te.sig

inductiveElim : (te : Inductive STy is ss ns) -> STy (ns ++ (([<] :< te.ind) ++ ss))
inductiveElim te = ?h2

inductiveTel : (te : Inductive STy is ss ns) -> Tel STy ((([<] :< te.ind) ++ ss) :< elimName te.ind) ns
inductiveTel te = (([<] :< (te.ind, sPis te.indices SU)) ++ inductiveCtors te) :< (elimName te.ind, inductiveElim te)



