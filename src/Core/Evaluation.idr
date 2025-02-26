module Core.Evaluation

import Data.SnocList
import Data.Maybe

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Weakening

public export
record GlobEnv (0 gs : GlobNames) where
  constructor MkGlobEnv
  replace : {0 ps : Names} -> (n : GlobNameIn gs ps) -> Maybe (STm gs ps)

public export
noReplace : GlobEnv gs
noReplace = MkGlobEnv (\_ => Nothing)

public export covering
eval : GlobEnv gs -> Env gs ns ms -> STm gs ms -> VTm gs ns

export infixr 1 $$

public export covering
appClosure : GlobEnv gs -> Closure gs ps ms -> Spine (VTm gs) ps ms -> VTm gs ms
appClosure sig (Cl _ env t) x = eval sig (env ++ x) t

public export covering
apply : GlobEnv gs -> (s : Size ms) -> Closure gs ns ms -> VTm gs (ms ++ ns)
apply sig s (Cl vs env t) = eval sig (weakenN vs env ++ vHeres s vs) t

public export covering
applyRen : GlobEnv gs -> (s : Size ms) -> Closure gs [< n] ms -> VTm gs (ms :< n')
applyRen sig s (Cl vs env t) = eval sig (weaken env :< VVar (lastLvl s)) t

public export covering
app : GlobEnv gs -> VTm gs ns -> (0 n : Name) -> VTm gs ns -> VTm gs ns
app sig (VLam _ cl) _ x = appClosure sig cl [< x]
app sig (VRigid i sp) n x = VRigid i ((:<) {n = n} sp x)
app sig (VGlob g sp pp t) n x = VGlob g sp ((:<) {n = n} pp x) (case t of
  Just t => Just $ delay $ app sig (force t) n x
  Nothing => Nothing)
app sig (VPi _ a b) _ _ = error "impossible to apply VPi"
app sig VU _ _ = error "impossible to apply VU"

public export covering
appSpine : GlobEnv gs -> VTm gs ns -> Spine (VTm gs) ps ns -> VTm gs ns
appSpine sig f [<] = f
appSpine sig f ((:<) {n} xs x) = app sig (appSpine sig f xs) n x

public export covering
evalSpine : GlobEnv gs -> Env gs n m -> Spine (STm gs) ps m -> Spine (VTm gs) ps n
evalSpine sig env Lin = Lin
evalSpine sig env (xs :< x) = evalSpine sig env xs :< eval sig env x

eval sig env (SVar i) = lookup env i
eval sig env (SLam n t) = VLam n (Cl (SS SZ) env t)
eval sig env (SApp f n x) = app sig (eval sig env f) n (eval sig env x)
eval sig env (SPi n a b) = VPi n (eval sig env a) (Cl (SS SZ) env b)
eval sig env (SLet n a b) = eval sig (env :< eval sig env a) b
eval sig env SU = VU
eval sig env (SGlob n sp) = let sp' = evalSpine sig env sp in VGlob n sp' [<] (case sig.replace n of
  Just t => Just $ delay (eval sig sp' (force t))
  Nothing => Nothing)

public export covering
sAppSpine : STm gs ns -> Spine (STm gs) ps ns -> STm gs ns
sAppSpine f Lin = f
sAppSpine f ((:<) {n = n} xs x) = SApp (sAppSpine f xs) n x

public export covering
quote : GlobEnv gs -> Size ns -> VTm gs ns -> STm gs ns

public export covering
quoteSpine : GlobEnv gs -> Size ns -> Spine (VTm gs) ps ns -> Spine (STm gs) ps ns
quoteSpine sig s [<] = [<]
quoteSpine sig s (xs :< x) = quoteSpine sig s xs :< quote sig s x

quote sig s (VLam n (Cl _ env t)) = SLam n $ quote sig (SS s) (eval sig (weakenEnv env :< VVar (lastLvl s)) t)
quote sig s (VRigid l sp) = sAppSpine (SVar (lvlToIdx s l)) (quoteSpine sig s sp)
quote sig s (VPi n a (Cl _ env t)) = SPi n (quote sig s a) (quote sig (SS s) (eval sig (weakenEnv env :< VVar (lastLvl s)) t))
quote sig s VU = SU
quote sig s (VGlob n sp pp _) = sAppSpine (SGlob n (quoteSpine sig s sp)) (quoteSpine sig s pp)

public export covering
nf : Size ns -> STm gs ns -> STm gs ns
nf s t = quote noReplace s (eval noReplace idEnv t)

public export covering
sub : Env gs n m -> VTm gs m -> VTm gs n
sub env t = eval noReplace env (quote noReplace env.size t)

public export covering
closeVal : Size us -> Env gs ns ks -> VTm gs (ks ++ us) -> Closure gs us ns
closeVal vs env t = Cl vs env (quote noReplace (env.size + vs) t)

public export covering
sHeres : Size ns -> Size ps -> Spine (STm gs) ps (ns ++ ps)
sHeres nss pss = quoteSpine noReplace (nss + pss) (vHeres nss pss)

public export covering
vPis : Size ns -> VTel gs ps ns -> VTm gs (ns ++ ps) -> VTm gs ns
vPis nss [<] b = b
vPis nss (as :< (n, a)) b = vPis nss as (VPi n (apply noReplace nss a) (closeVal (SS SZ) (growEnvN nss as.size idEnv) b))

public export covering
vPis' : VTel gs ps [<] -> VTm gs ps -> VTm gs [<]
vPis' as b = vPis SZ as (rewrite appendLinLeftNeutral ps in b)

public export covering
vTelToTelVTm : Size ns -> VTel gs ps ns -> Tel (VTm gs) ps ns
vTelToTelVTm _ [<] = [<]
vTelToTelVTm s ((:<) {ps = ps} te' (n, t)) = (vTelToTelVTm s te') :< (n, apply noReplace s t)

public export covering
moveToBound : Size ns -> Size ps -> Size ls -> Closure gs ls (ns ++ ps) -> Closure gs (ps ++ ls) ns
moveToBound nss pss lss cl = closeVal (pss + lss) idEnv (rewrite appendAssociative ns ps ls in apply noReplace (nss + pss) cl)

public export covering
(++) : {auto ss : Size ns} -> VTel gs ps ns -> VTel gs qs (ns ++ ps) -> VTel gs (ps ++ qs) ns
(++) {ss} te [<] = te
(++) {ss} te ((:<) {ps = ls} te' (n, t)) = (te ++ te') :< (n, moveToBound ss te.size te'.size t)

public export covering
(++.) : VTel gs ps [<] -> VTel gs qs ps -> VTel gs (ps ++ qs) [<]
(++.) a b = a ++ (rewrite appendLinLeftNeutral ps in b)

public export covering
singleton : (n : Name) -> Size ns -> VTm gs ns -> VTel gs [< n] ns
singleton n sz t = [< (n, closeVal SZ idEnv t)]
