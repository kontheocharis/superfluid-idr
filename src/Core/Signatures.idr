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

record Op (0 gs : GlobNames) (0 ctx : Names) (0 ps : Names) where
  constructor MkOp
  {0 as : Names}
  dom : VTel gs as ctx
  ret : Spine (VTm gs) ps (ctx ++ as)

record Signature (0 gs : GlobNames) (0 ctx : Names) (0 ps : Names) (0 ops : Names) where
  constructor MkSignature
  inner : Tel (\ctx' => Op gs ctx' ps) ops ctx

public export
record Carrier (0 gs : GlobNames) (0 ctx : Names) (0 ps : Names) where
  constructor MkCarrier
  inner : VTy gs (ctx ++ ps)

public export
record AlgebraForOp (op : Op gs ctx ps) (x : Carrier gs ctx ps) where
  constructor MkAlgebraForOp
  inner : VTy gs ctx

public export covering
algebraForOp : Subst (Env gs) (VTm gs)
  => Size ctx
  -> (op : Op gs ctx ps)
  -> (x : Carrier gs ctx ps)
  -> AlgebraForOp op x
algebraForOp @{s} ctxSize (MkOp dom ret) (MkCarrier x) =
  MkAlgebraForOp $ vPis ctxSize dom -- domain of constructor
    (res x (join @{s} ret.size (wkN @{s} ctxSize dom.size) ret)) -- return algebra type

public export
record Algebra (sig : Signature gs ctx ps ops) (x : Carrier gs ctx ps) where
  constructor MkAlgebra
  inner : VTel gs ops ctx

public export covering
0 algebra : Subst (Env gs) (VTm gs)
  => Size ctx
  -> (sig : Signature gs ctx ps ops)
  -> (x : Carrier gs ctx ps)
  -> Algebra sig x
algebra _ (MkSignature [<]) (MkCarrier x) = MkAlgebra [<]
algebra {ops = ops :< n} @{s} ctxSize (MkSignature (sig :< op)) x =
  MkAlgebra $ ((algebra ctxSize (MkSignature sig) x).inner
  :< closeVal sig.size (id @{s} ctxSize) (algebraForOp @{s} (ctxSize + sig.size) op (?fx)).inner)

public export
record Motive (x : Carrier gs ctx ps) where
  constructor MkMotive
  {0 n : Name}
  inner : VTy gs ((ctx ++ ps) :< n)

public export
record AlgebraAtOp (op : Op gs ctx ps) (x : Carrier gs ctx ps) where
  constructor MkAlgebraAtOp
  inner : VTm gs (ctx ++ op.as)

public export
record DispAlgebraForOp (op : Op gs ctx ps) (ao : AlgebraAtOp op x) (y : Motive x) where
  constructor MkDispAlgebraForOp
  inner : VTy gs ctx

public export covering
0 dispAlgebraForOp : Subst (Env gs) (VTm gs)
  => Size ctx
  -> {0 x : Carrier gs ctx ps}
  -> (op : Op gs ctx ps)
  -> (ao : AlgebraAtOp op x)
  -> (y : Motive x)
  -> DispAlgebraForOp op ao y
dispAlgebraForOp @{s} ctxSize (MkOp dom ret) ao y =
  MkDispAlgebraForOp $ vPis ctxSize dom -- domain of eliminator method
    (res y.inner -- return motive type
      (ext @{s} (join @{s} ret.size (wkN @{s} ctxSize dom.size) ret) -- applied to indices
      ao.inner)) -- and constructor

public export
record DispAlgebra (sig : Signature gs ctx ps ops) (a : Algebra sig x) (y : Motive x) where
  constructor MkDispAlgebra
  inner : VTel gs ops ctx

public export covering
0 dispAlgebra : Subst (Env gs) (VTm gs)
  => Size ctx
  -> (sig : Signature gs ctx ps ops)
  -> (a : Algebra sig x)
  -> (y : Motive x) -- motive
  -> DispAlgebra sig a y
dispAlgebra _ (MkSignature [<]) a y = MkDispAlgebra [<]
dispAlgebra {ops = ops :< n} @{s} ctxSize (MkSignature (sig :< op)) (MkAlgebra (a :< ao)) y =
    MkDispAlgebra $ ((dispAlgebra ctxSize (MkSignature sig) (MkAlgebra a) y).inner
    :< closeVal sig.size (id @{s} ctxSize)
      (dispAlgebraForOp @{s} (ctxSize + sig.size) op -- displayed algebra for op
      (MkAlgebraAtOp $ appSpine noReplace (res ?ao (wkN2 @{s} ctxSize ops.size op.dom.size))
        (vHeres (ctxSize + ops.size) op.dom.size))  -- constructor in applied form
      ?y).inner) -- motive

-- public export covering
-- 0 section : Subst (Env gs) (VTm gs)
--   => Size ctx
--   -> Signature gs ps ops ctx
--   -> Spine (VTm gs) ops ctx -- algebra
--   -> (forall ctx' . VTy gs (((ctx ++ ctx') ++ ps) :< x)) -- motive
--   -> VTel gs ops ctx
-- dispAlgebra _ [<] a y = [<]
-- dispAlgebra {ops = ops :< n} @{s} ctxSize (sig :< (n, op)) (a :< ao) y =
--   (dispAlgebra ctxSize sig a y
--   :< (n, closeVal sig.size (id @{s} ctxSize)
--     (dispAlgebraForOp @{s} (ctxSize + sig.size) op -- displayed algebra for op
--     (appSpine noReplace (res ao (wkN2 @{s} ctxSize ops.size op.dom.size))
--       (vHeres (ctxSize + ops.size) op.dom.size))  -- constructor in applied form
--     y))) -- motive
