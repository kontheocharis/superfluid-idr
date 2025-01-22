module Core.Conversion

import Data.DPair
import Decidable.Equality
import Data.SnocList.Elem

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Evaluation

public export
convert : (s : Size bs) -> VTm bs -> VTm bs -> Bool

public export
convertSpine : (s : Size bs) -> (xs : Spine (VTm bs)) -> (ys : Spine (VTm bs)) -> Bool
convertSpine s [<] [<] = True
convertSpine s (sp :< t) (sp' :< t') = convertSpine s sp sp' && convert s t t'
convertSpine s _ _ = False

convert _ VU VU = True
convert s (VPi _ a b) (VPi _ a' b') = convert s a a' && convert (SS s) (applyRen s b) (apply s b')
convert s (VLam _ t) (VLam _ t') = convert (SS s) (applyRen s t) (apply s t')
convert s (VLam _ t) u = convert (SS s) (apply s t) (app (weaken u) (VVar (lastLvl s)))
convert s u (VLam _ t) = convert (SS s) (app (weaken u) (VVar (lastLvl s))) (apply s t)
convert s (VRigid l sp) (VRigid l' sp') = l == l' && convertSpine s sp sp'
convert s _ _ = False
