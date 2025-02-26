module Core.Algebras

import Data.DPair
import Decidable.Equality
import Data.SnocList.Elem
import Data.SnocList
import Data.Singleton

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Weakening
import Core.Definitions

-- (Exists (\c : CtorItem dataIn => ItemIn sig (Ctor c)))
--
-- 0 Carrier : {0 sig : Sig gs} -> (0 t : Theory sig) -> Type
-- Carrier {gs} t = Spine (STm gs) (Data t.d).arity [<] -> STy gs [<]

-- record Algebra {0 sig : Sig gs} (0 t : Theory sig) (0 x : Carrier t) where
--   constructor MkAlgebra
--   ops : ForList t.ctorsIn (\e => Spine (STm gs) (Ctor (fst e)).arity [<] -> STm gs [<])

-- 0 Alg : Theory sig -> Type
-- Alg t = (x : Carrier t ** Algebra t x)

-- termAlgebra : (t : Theory sig) -> Algebra t (SGlob (globNameIn t.dataIn))
-- termAlgebra t = MkAlgebra $ forList t.ctorsIn (\e => SGlob (globNameIn (snd e)))

-- 0 Motive : {0 sig : Sig gs} -> {0 t : Theory sig} -> Alg t -> Type
-- Motive a = (ts : Spine (STm gs) (Data t.d).arity [<]) -> STm gs [<] -> STy gs [<]

-- record Methods {0 sig : Sig gs} {0 t : Theory sig} {0 a : Alg t} (m : Motive a) where
--   constructor MkMethods
--   dispOps : ForList t.ctorsIn (\e => Spine (STm gs) (Ctor (fst e)).arity [<] -> STm gs [<])

-- 0 DispAlg : Alg t -> Type
-- DispAlg a = (e : Motive a ** Methods e)

-- 0 Section : DispAlg a -> Type
-- Section d = Spine (STm gs) (Data d).arity [<] -> STm gs [<] -> STm gs [<]
