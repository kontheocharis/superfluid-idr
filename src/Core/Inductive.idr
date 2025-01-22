module Core.Inductive

import Data.SnocList

import Common
import Context
import Core.Syntax

data Tel : (Names -> Type) -> Names -> Names -> Type where
  Lin : Tel f [<] ns
  (:<) : (c : Tel f ps ns) -> (p : (Name, f (ns ++ ps))) -> Tel f (ps :< fst p) ns

Con : (Names -> Type) -> Names -> Type
Con f ps = Tel f ps [<]

(++) : Tel f' ps' ns' -> Tel f' qs' (ns' ++ ps') -> Tel f' (ps' ++ qs') ns'
(++) te [<] = te
(++) te ((:<) {ps = ps} te' (n, t)) = (te ++ te') :< (n, rewrite appendAssociative ns' ps' ps in t)

sPis : Tel STy ps ns -> STy (ns ++ ps) -> STy ns
sPis [<] b = b
sPis (as :< (n, a)) b = sPis as (SPi n a b)

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



