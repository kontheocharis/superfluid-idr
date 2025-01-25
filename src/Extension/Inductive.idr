module Extension.Inductive

import Data.SnocList
import Data.DPair

import Common
import Context
import Core.Syntax

record Inductive (sort : Names -> Type) (is : Names) (ss : Names) (ns : Names) where
  constructor MkInductive
  ind : Name
  indices : Tel (STy gs) is ns
  sig : Tel (STy gs) ss (ns :< ind)

elimName : Name -> Name
elimName (MkName n) = MkName $ "elim-" ++ n

-- inductiveCtors : (te : Inductive (STy gs) is ss ns) -> Tel (STy gs) ss (ns :< te.ind)
-- inductiveCtors te = te.sig

-- inductiveElim : (te : Inductive (STy gs) is ss ns) -> STy gs (ns ++ (([<] :< te.ind) ++ ss))
-- inductiveElim te = ?h2

-- inductiveTel : (te : Inductive (STy gs) is ss ns) -> Tel STy gs ((([<] :< te.ind) ++ ss) :< elimName te.ind) ns
-- inductiveTel te = (([<] :< (te.ind, sPis te.indices SU)) ++ inductiveCtors te) :< (elimName te.ind, inductiveElim te)



