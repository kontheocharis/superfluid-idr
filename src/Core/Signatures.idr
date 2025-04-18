module Core.Signatures

import Common
import Context
import Data.SnocList
import Data.DPair
import Core.Substitution
import Core.Values
import Core.Weakening
import Core.Evaluation

import Data.Singleton

record Op (0 gs : GlobNames) (0 ps : Names) (0 ctx : Names) where
  constructor MkOp
  {0 as : Names}
  dom : VTel gs as ctx
  ret : Spine (VTm gs) ps (ctx ++ as)

0 Signature : (gs : GlobNames) -> (ps : Names) -> (ops : Names) -> (ctx : Names) -> Type
Signature gs ps ops ctx = Tel (\ctx' => Op gs ps ctx') ops ctx

-- plugIn : Subst (Env gs) (VTm gs) => Size ctx -> Size as -> VTy gs (ctx ++ ps) -> Spine (VTm gs) ps (ctx ++ as) -> VTm gs (ctx ++ as)
-- plugIn @{s} ctxSize asSize x [<] = res x (wkN @{s} ctxSize asSize)
-- plugIn ctxSize asSize x (ps :< p) = ?fa   -- let x' = plugIn asSize x ps in ?fa

covering
algebraForOp : Subst (Env gs) (VTm gs)
  => Size ctx
  -> Op gs ps ctx
  -> VTy gs (ctx ++ ps)
  -> VTy gs ctx
algebraForOp @{s} ctxSize (MkOp dom ret) x =
  vPis ctxSize dom
    -- (res x (join @{s} ret.size (wkN @{s} ctxSize dom.size) ret))
    (res (anyBaseN x) ?fa)

covering
0 algebra : Subst (Env gs) (VTm gs)
  => Size ctx
  -> Signature gs ps ops ctx
  -> (forall ctx' . VTy gs ((ctx ++ ctx') ++ ps))
  -> VTel gs ops ctx
algebra _ [<] x = [<]
algebra {ops = ops :< n} @{s} ctxSize (sig :< (n, op)) x =
  (algebra ctxSize sig x
  :< (n, closeVal sig.size (id @{s} ctxSize) (algebraForOp @{s} (ctxSize + sig.size) op x)))
