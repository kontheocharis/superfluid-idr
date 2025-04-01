module Core.Conversion

import Data.DPair
import Decidable.Equality
import Data.SnocList.Elem
import Data.Fin
import Data.Nat

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Weakening
import Core.Evaluation
import Core.Definitions

orFalse : (b : Maybe a) -> (a -> Bool) -> Bool
orFalse (Just x) f = f x
orFalse Nothing _ = False

data SameSize : Names -> Names -> Type where
  BSZ : SameSize [<] [<]
  BSS : SameSize ns ns' -> SameSize (ns :< n) (ns' :< n')

sameSizeSym : SameSize ns ns' -> SameSize ns' ns
sameSizeSym BSZ = BSZ
sameSizeSym (BSS x) = BSS (sameSizeSym x)

data ConvertibleClosure : SameSize ns ns' -> Closure gs [< n] ns -> Closure gs [< n'] ns' -> Type

data ConvertibleSpine : SameSize ns ns' -> Spine (VTm gs) ns ps -> Spine (VTm gs) ns' ps' -> Type

convertibleSpineSameSize : (sp : Spine (VTm gs) ns ps) -> (sp' : Spine (VTm gs) ns' ps') -> ConvertibleSpine g sp sp' -> SameSize ps ps'

data Convertible : SameSize bs bs' -> VTm gs bs -> VTm gs bs' -> Type where
  CSym : Convertible g a b -> Convertible (sameSizeSym g) b a
  CRefl : Convertible g a a


  CU : Convertible g VU VU
  CPi : Convertible g a b -> ConvertibleClosure g c d -> Convertible g (VPi n a c) (VPi n' b d)
  VLam : ConvertibleClosure g a b -> Convertible g (VLam n a) (VLam n' b)
  VRigid : l = l' -> ConvertibleSpine g sp sp' -> Convertible g (VRigid l sp) (VRigid l' sp')


mutual
  public export covering
  convert : (sig : Sig gs) -> (s : Size bs) -> VTm gs bs -> VTm gs bs -> Bool
  convert sig _ VU VU = True
  convert sig s (VPi n a b) (VPi n' a' b') = convert sig s a a'
    && convert sig (SS s) (applyRen (asGlobEnv sig) s b) (apply (asGlobEnv sig) s b')
  convert sig s (VLam _ t) (VLam _ t') = convert sig (SS s) (applyRen (asGlobEnv sig) s t) (apply (asGlobEnv sig) s t')
  convert sig s (VLam n t) u = convert sig (SS s) (apply (asGlobEnv sig) s t) (app (asGlobEnv sig) (weaken u) n (VVar (lastLvl s)))
  convert sig s u (VLam n t) = convert sig (SS s) (app (asGlobEnv sig) (weaken u) n (VVar (lastLvl s))) (apply (asGlobEnv sig) s t)
  convert sig s (VRigid l sp) (VRigid l' sp') = l == l' && convertSpine sig s sp sp'
  convert sig s t@(VGlob g sp pp u) t'@(VGlob g' sp' pp' u') with (match g g')
    _ | Just _ = convertSpine sig s sp sp' && convertSpine sig s pp pp'
    _ | Nothing = case u of
        Just u => convert sig s (force u) t'
        Nothing => case u' of
          Just u' => convert sig s t (force u')
          Nothing => False
  convert sig s t (VGlob g' sp' pp' t') = case t' of
    Just t' => convert sig s t t'
    Nothing => False
  convert sig s (VGlob g sp pp t) t' = case t of
    Just t => convert sig s t t'
    Nothing => False
  convert sig s _ _ = False

  public export covering
  convertSpine : (sig : Sig gs) -> (s : Size bs) -> (xs : Spine (VTm gs) ps bs) -> (ys : Spine (VTm gs) ps' bs) -> Bool
  convertSpine sig s [<] [<] = True
  convertSpine sig s (sp :< t) (sp' :< t') = convertSpine sig s sp sp' && convert sig s t t'
  convertSpine sig s _ _ = False
