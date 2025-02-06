module Core.Evaluation

import Data.SnocList

import Common
import Context
import Core.Syntax
import Core.Values
import Core.Weakening

public export covering
eval : Env gs n m -> STm gs m -> VTm gs n

export infixr 1 $$

public export covering
($$) : Closure gs ps ms -> Spine (VTm gs) ps ms -> VTm gs ms
($$) (Cl _ env t) x = eval (env ++ x) t

public export covering
apply : (s : Size ms) -> Closure gs ns ms -> VTm gs (ms ++ ns)
apply s (Cl vs env t) = eval (weakenN vs env ++ vHeres s vs) t

public export covering
applyRen : (s : Size ms) -> Closure gs [< n] ms -> VTm gs (ms :< n')
applyRen s (Cl vs env t) = eval (weaken env :< VVar (lastLvl s)) t

public export covering
app : VTm gs ns -> (0 n : Name) -> VTm gs ns -> VTm gs ns
app (VLam _ cl) _ x = cl $$ [< x]
app (VRigid i sp) n x = VRigid i ((:<) {n = n} sp x)
app (VGlob g sp pp) n x = VGlob g sp ((:<) {n = n} pp x)
app (VPi _ a b) _ _ = error "impossible to apply VPi"
app VU _ _ = error "impossible to apply VU"

public export covering
appSpine : VTm gs ns -> Spine (VTm gs) ps ns -> VTm gs ns
appSpine f [<] = f
appSpine f ((:<) {n} xs x) = app (appSpine f xs) n x

public export covering
evalSpine : Env gs n m -> Spine (STm gs) ps m -> Spine (VTm gs) ps n
evalSpine env Lin = Lin
evalSpine env (xs :< x) = evalSpine env xs :< eval env x

eval env (SVar i) = lookup env i
eval env (SLam n t) = VLam n (Cl (SS SZ) env t)
eval env (SApp f n x) = app (eval env f) n (eval env x)
eval env (SPi n a b) = VPi n (eval env a) (Cl (SS SZ) env b)
eval env (SLet n a b) = eval (env :< eval env a) b
eval env SU = VU
eval env (SGlob n sp) = VGlob n (evalSpine env sp) [<]

public export covering
sAppSpine : STm gs ns -> Spine (STm gs) ps ns -> STm gs ns
sAppSpine f Lin = f
sAppSpine f ((:<) {n = n} xs x) = SApp (sAppSpine f xs) n x

public export covering
quote : Size ns -> VTm gs ns -> STm gs ns

public export covering
quoteSpine : Size ns -> Spine (VTm gs) ps ns -> Spine (STm gs) ps ns
quoteSpine s [<] = [<]
quoteSpine s (xs :< x) = quoteSpine s xs :< quote s x

quote s (VLam n (Cl _ env t)) = SLam n $ quote (SS s) (eval (weakenEnv env :< VVar (lastLvl s)) t)
quote s (VRigid l sp) = sAppSpine (SVar (lvlToIdx s l)) (quoteSpine s sp)
quote s (VPi n a (Cl _ env t)) = SPi n (quote s a) (quote (SS s) (eval (weakenEnv env :< VVar (lastLvl s)) t))
quote s VU = SU
quote s (VGlob n sp pp) = sAppSpine (SGlob n (quoteSpine s sp)) (quoteSpine s pp)

public export covering
nf : Size ns -> STm gs ns -> STm gs ns
nf s t = quote s (eval idEnv t)

public export covering
sub : Env gs n m -> VTm gs m -> VTm gs n
sub env t = eval env (quote (env.size) t)

public export covering
closeVal : Size us -> Env gs ns ks -> VTm gs (ks ++ us) -> Closure gs us ns
closeVal vs env t = Cl vs env (quote (env.size + vs) t)

public export covering
sHeres : Size ns -> Size ps -> Spine (STm gs) ps (ns ++ ps)
sHeres nss pss = quoteSpine (nss + pss) (vHeres nss pss)

public export covering
vPis : Size ns -> VTel gs ps ns -> VTm gs (ns ++ ps) -> VTm gs ns
vPis nss [<] b = b
vPis nss (as :< (n, a)) b = vPis nss as (VPi n (apply nss a) (closeVal (SS SZ) (growEnvN nss as.size idEnv) b))

public export covering
vPis' : VTel gs ps [<] -> VTm gs ps -> VTm gs [<]
vPis' as b = vPis SZ as (rewrite appendLinLeftNeutral ps in b)
  
public export covering
vTelToTelVTm : Size ns -> VTel gs ps ns -> Tel (VTm gs) ps ns
vTelToTelVTm _ [<] = [<]
vTelToTelVTm s ((:<) {ps = ps} te' (n, t)) = (vTelToTelVTm s te') :< (n, apply s t)

public export covering
moveToBound : Size ns -> Size ps -> Size ls -> Closure gs ls (ns ++ ps) -> Closure gs (ps ++ ls) ns
moveToBound nss pss lss cl = closeVal (pss + lss) idEnv (rewrite appendAssociative ns ps ls in apply (nss + pss) cl)

public export covering
(++) : {auto ss : Size ns} -> VTel gs ps ns -> VTel gs qs (ns ++ ps) -> VTel gs (ps ++ qs) ns
(++) {ss} te [<] = te
(++) {ss} te ((:<) {ps = ls} te' (n, t)) = (te ++ te') :< (n, moveToBound ss te.size te'.size t)

public export covering
(++.) : VTel gs ps [<] -> VTel gs qs ps -> VTel gs (ps ++ qs) [<]
(++.) a b = a ++ (rewrite appendLinLeftNeutral ps in b)