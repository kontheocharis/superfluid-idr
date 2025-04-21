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
  indices : VTel gs ps ctx
  inner : Tel (\ctx' => Op gs ctx' ps) ops ctx

record OpIn (sig : Signature gs ctx ps ops) where
  constructor MkOpIn
  index : Idx ops

public export
record Carrier (0 gs : GlobNames) (0 ctx : Names) (0 ps : Names) where
  constructor MkCarrier
  inner : Closure gs ps ctx

public export
record AlgebraTelForOp (op : Op gs ctx ps) (x : Carrier gs ctx ps) where
  constructor MkAlgebraForOp
  inner : VTy gs ctx

public export covering
algebraForOp : Subst (Env gs) (VTm gs)
  => (forall us . Subst (Env gs) (Closure gs us))
  => Size ctx
  -> (op : Op gs ctx ps)
  -> (x : Carrier gs ctx ps)
  -> AlgebraTelForOp op x
algebraForOp @{s} @{sc} ctxSize (MkOp dom ret) (MkCarrier x) =
  MkAlgebraForOp $ vPis ctxSize dom -- domain of constructor
    (appClosure noReplace (res x (wkN @{s} ctxSize dom.size)) ret)

public export
record AlgebraTel (sig : Signature gs ctx ps ops) (x : Carrier gs ctx ps) where
  constructor MkAlgebraTel
  inner : VTel gs ops ctx

public export covering
0 algebra : Subst (Env gs) (VTm gs)
  => (forall us . Subst (Env gs) (Closure gs us))
  => Size ctx
  -> (sig : Signature gs ctx ps ops)
  -> (x : Carrier gs ctx ps)
  -> AlgebraTel sig x
algebra _ (MkSignature _ [<]) (MkCarrier x) = MkAlgebraTel [<]
algebra {ops = ops :< n} @{s} ctxSize (MkSignature ind (sig :< op)) (MkCarrier x) =
  MkAlgebraTel $ ((algebra ctxSize (MkSignature ind sig) (MkCarrier x)).inner
  :< closeVal sig.size (id @{s} ctxSize)
    (algebraForOp @{s} (ctxSize + sig.size) op
      (MkCarrier (res x (wkN @{s} ctxSize sig.size)))).inner)

public export
record Motive (x : Carrier gs ctx ps) where
  constructor MkMotive
  {n : Name}
  inner : Closure gs (ps :< n) ctx

public export
record Algebra (op : Signature gs ctx ps ops) (x : Carrier gs ctx ps) where
  constructor MkAlgebra
  inner : Spine (VTm gs) ops ctx

public export
record AlgebraAtOp (op : Op gs ctx ps) (x : Carrier gs ctx ps) where
  constructor MkAlgebraAtOp
  inner : VTm gs (ctx ++ op.as)

public export
record DispAlgebraTelForOp (op : Op gs ctx ps) (ao : AlgebraAtOp op x) (y : Motive x) where
  constructor MkDispAlgebraTelForOp
  inner : VTy gs ctx

public export covering
dispAlgebraForOp : Subst (Env gs) (VTm gs)
  => (forall us . Subst (Env gs) (Closure gs us))
  => Size ctx
  -> {0 x : Carrier gs ctx ps}
  -> (op : Op gs ctx ps)
  -> (ao : AlgebraAtOp op x)
  -> (y : Motive x)
  -> DispAlgebraTelForOp op ao y
dispAlgebraForOp @{s} ctxSize (MkOp dom ret) ao (MkMotive y) =
  MkDispAlgebraTelForOp $ vPis ctxSize dom -- domain of eliminator method
    (appClosure noReplace
      (res y (wkN @{s} ctxSize dom.size))  -- motive type
      (ext @{s} ret ao.inner))  -- applied to indices and constructor

public export
record DispAlgebraTel (sig : Signature gs ctx ps ops) (a : Algebra sig x) (y : Motive x) where
  constructor MkDispAlgebraTel
  inner : VTel gs ops ctx

public export covering
dispAlgebra : Subst (Env gs) (VTm gs)
  => (forall us . Subst (Env gs) (Closure gs us))
  => Size ctx
  -> (sig : Signature gs ctx ps ops)
  -> (a : Algebra sig x)
  -> (y : Motive x) -- motive
  -> DispAlgebraTel sig a y
dispAlgebra _ (MkSignature _ [<]) a y = MkDispAlgebraTel [<]
dispAlgebra {ops = ops :< n} {x = MkCarrier x} @{s}
  ctxSize
  (MkSignature ind (sig :< op))
  (MkAlgebra (a :< ao)) (MkMotive {n = n'} y)
    = MkDispAlgebraTel $
      ((dispAlgebra {x = MkCarrier x} ctxSize (MkSignature ind sig) (MkAlgebra a) (MkMotive y)).inner -- rest of methods
        :< closeVal sig.size (id @{s} ctxSize)
          (dispAlgebraForOp @{s} (ctxSize + sig.size) op -- displayed algebra for op
            (MkAlgebraAtOp {x = MkCarrier (res x (wkN @{s} ctxSize sig.size))} $ appSpine noReplace   -- constructor in applied form
              (res ao (wkN2 @{s} ctxSize sig.size op.dom.size))
              (vHeres (ctxSize + sig.size) op.dom.size))
            (MkMotive {n = n'} (res y (wkN @{s} ctxSize sig.size)))).inner) -- motive

public export
record DispAlgebra (sig : Signature gs ctx ps ops) {x : Carrier gs ctx ps} (a : Algebra sig x) (y : Motive x) where
  constructor MkDispAlgebra
  inner : Spine (VTm gs) ops ctx

public export
record SectionTy (sig : Signature gs ctx ps ops) {x : Carrier gs ctx ps} (y : Motive x) where
  constructor MkSectionTy
  inner : VTy gs ctx

public export covering
section : Size ctx -> (sig : Signature gs ctx ps ops) -> {x : Carrier gs ctx ps} -> (y : Motive x) -> SectionTy sig y
section ctxSize (MkSignature ind sig) {x = MkCarrier x} (MkMotive y)
  = MkSectionTy $ vPis ctxSize (ind :< x) (apply' noReplace ctxSize y)

-- public export
-- record Section (sig : Signature gs ctx ps ops)
--   {x : Carrier gs ctx ps}
--   (y : Motive x) where
--   constructor MkSectionTy
--   inner : VTy gs ctx

-- section : (sig : Signature gs ctx ps ops) -> {x : Carrier gs ctx ps} -> (y : Motive x) -> Section sig y
-- section sig {x} y = MkSection $ MkVTy gs ctx

-- public export
-- record Section (sig : Signature gs ctx ps ops)
--   {x : Carrier gs ctx ps}
--   (y : Motive x) where
--   constructor MkSection
--   inner : VTm gs ctx


-- public export
-- record Section (sig : Signature gs ctx ps ops)
--   {x : Carrier gs ctx ps}
--   (y : Motive x) where
--   constructor MkSection
--   inner : VTm gs ctx


-- public export
-- record DispAlgebraAtOp (sig : Signature gs ctx ps ops) {x : Carrier gs ctx ps} (a : Algebra sig x) (y : Motive x) where
--   constructor MkAlgebraAtOp
--   inner : VTm gs (ctx ++ op.as)

-- public export covering
--   dispAlgebra : Subst (Env gs) (VTm gs)
--     => (forall us . Subst (Env gs) (Closure gs us))
--     => Size ctx
--     -> (sig : Signature gs ctx ps ops)
--     -> (a : Algebra sig x)
--     -> (y : Motive x) -- motive
--     -> DispAlgebraTel sig a y
