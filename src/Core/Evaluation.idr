module Core.Evaluation

import Data.SnocList

import Common
import Context
import Core.Syntax
import Core.Values

public export
eval : Env n m -> STm m -> VTm n

export infixr 1 $$

public export
($$) : Closure n ms -> VTm ms -> VTm ms
($$) (Cl env t) x = eval (env :< x) t

public export
apply : (s : Size ms) -> Closure n ms -> VTm (ms :< n)
apply s (Cl env t) = eval (weakenEnv env :< VVar (lastLvl s)) t

public export
applyRen : (s : Size ms) -> Closure n ms -> VTm (ms :< n')
applyRen s (Cl env t) = eval (weakenEnv env :< VVar (lastLvl s)) t

public export
app : VTm ns -> (0 n : Name) -> VTm ns -> VTm ns
app (VLam _ cl) _ x = cl $$ x
app (VRigid i sp) n x = VRigid i ((:<) {n = n} sp x)
app (VPi _ a b) _ x = error "impossible to apply VPi"
app VU _ _ = error "impossible to apply VU"

eval env (SVar i) = lookup env i
eval env (SLam n t) = VLam n (Cl env t)
eval env (SApp f n x) = app (eval env f) n (eval env x)
eval env (SPi n a b) = VPi n (eval env a) (Cl env b)
eval env (SLet n a b) = eval (env :< eval env a) b
eval env SU = VU

appSpine : STm ns -> Spine STm ps ns -> STm ns
appSpine f Lin = f
appSpine f ((:<) {n = n} xs x) = SApp (appSpine f xs) n x

public export
quote : Size ns -> VTm ns -> STm ns

quoteSpine : Size ns -> Spine VTm ps ns -> Spine STm ps ns
quoteSpine s [<] = [<]
quoteSpine s (xs :< x) = quoteSpine s xs :< quote s x

quote s (VLam n (Cl env t)) = SLam n $ quote (SS s) (eval (weakenEnv env :< VVar (lastLvl s)) t)
quote s (VRigid l sp) = appSpine (SVar (lvlToIdx s l)) (quoteSpine s sp)
quote s (VPi n a (Cl env t)) = SPi n (quote s a) (quote (SS s) (eval (weakenEnv env :< VVar (lastLvl s)) t))
quote s VU = SU

nf : Size ns -> STm ns -> STm ns
nf s t = quote s (eval (idEnv s) t)

public export
sub : Env n m -> VTm m -> VTm n
sub env t = eval env (quote (env.size) t)

public export
closeVal : Env ns ks -> VTm (ks :< u) -> Closure u ns
closeVal env t = Cl env (quote (SS env.size) t)
