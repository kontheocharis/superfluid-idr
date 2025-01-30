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

mutual
  public export partial covering
  convert : (s : Size bs) -> VTm gs bs -> VTm gs bs -> Bool
  convert _ VU VU = True
  convert s (VPi _ a b) (VPi _ a' b') = convert s a a' && convert (SS s) (applyRen s b) (apply s b')
  convert s (VLam _ t) (VLam _ t') = convert (SS s) (applyRen s t) (apply s t')
  convert s (VLam n t) u = convert (SS s) (apply s t) (app (weaken u) n (VVar (lastLvl s)))
  convert s u (VLam n t) = convert (SS s) (app (weaken u) n (VVar (lastLvl s))) (apply s t)
  convert s (VRigid l sp) (VRigid l' sp') = l == l' && convertSpine s sp sp'
  convert s _ _ = False

  public export partial covering
  convertSpine : (s : Size bs) -> (xs : Spine (VTm gs) ps bs) -> (ys : Spine (VTm gs) ps' bs) -> Bool
  convertSpine s [<] [<] = True
  convertSpine s (sp :< t) (sp' :< t') = convertSpine s sp sp' && convert s t t'
  convertSpine s _ _ = False

