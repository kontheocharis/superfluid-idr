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

mutual
  public export covering
  convert : (sig : Sig gs) -> (s : Size bs) -> VTm gs bs -> VTm gs bs -> Bool
  convert sig _ VU VU = True
  convert sig s (VPi n a b) (VPi n' a' b') = convert sig s a a' && convert sig (SS s) (applyRen s b) (apply s b')
  convert sig s (VLam _ t) (VLam _ t') = convert sig (SS s) (applyRen s t) (apply s t')
  convert sig s (VLam n t) u = convert sig (SS s) (apply s t) (app (weaken u) n (VVar (lastLvl s)))
  convert sig s u (VLam n t) = convert sig (SS s) (app (weaken u) n (VVar (lastLvl s))) (apply s t)
  convert sig s (VRigid l sp) (VRigid l' sp') = l == l' && convertSpine sig s sp sp'
  convert sig s t@(VGlob g sp pp) t'@(VGlob g' sp' pp') with (match g g')
    _ | True = convertSpine sig s sp sp' && convertSpine sig s pp pp'
    _ | False = case unfold sig g' of
        Just g'' => convert sig s t (appSpine (eval sp' g'') pp')
        Nothing => case unfold sig g of
          Just g' => convert sig s (appSpine (eval sp g') pp) t'
          Nothing => False
  convert sig s t (VGlob g' sp' pp') = case unfold sig g' of
    Just g'' => convert sig s t (appSpine (eval sp' g'') pp')
    Nothing => False
  convert sig s (VGlob g sp pp) t' = case unfold sig g of
    Just g' => convert sig s (appSpine (eval sp g') pp) t' 
    Nothing => False
  convert sig s _ _ = False

  public export covering
  convertSpine : (sig : Sig gs) -> (s : Size bs) -> (xs : Spine (VTm gs) ps bs) -> (ys : Spine (VTm gs) ps' bs) -> Bool
  convertSpine sig s [<] [<] = True
  convertSpine sig s (sp :< t) (sp' :< t') = convertSpine sig s sp sp' && convert sig s t t'
  convertSpine sig s _ _ = False

