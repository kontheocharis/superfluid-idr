module Core.Evaluation

import Data.SnocList

import Common
import Context
import Core.Syntax
import Core.Values

public export
eval : Env gs n m -> STm gs m -> VTm gs n

export infixr 1 $$

public export
($$) : Closure gs n ms -> VTm gs ms -> VTm gs ms
($$) (Cl env t) x = eval (env :< x) t

public export
apply : (s : Size ms) -> Closure gs n ms -> VTm gs (ms :< n)
apply s (Cl env t) = eval (weakenEnv env :< VVar (lastLvl s)) t

public export
applyRen : (s : Size ms) -> Closure gs n ms -> VTm gs (ms :< n')
applyRen s (Cl env t) = eval (weakenEnv env :< VVar (lastLvl s)) t

public export
app : VTm gs ns -> (0 n : Name) -> VTm gs ns -> VTm gs ns
app (VLam _ cl) _ x = cl $$ x
app (VRigid i sp) n x = VRigid i ((:<) {n = n} sp x)
app (VPi _ a b) _ _ = error "impossible to apply VPi"
app VU _ _ = error "impossible to apply VU"
app (VGlob n sp) _ _ = error "impossible to apply VGlob"

evalSpine : Env gs n m -> Spine (STm gs) ps m -> Spine (VTm gs) ps n
evalSpine env Lin = Lin
evalSpine env (xs :< x) = evalSpine env xs :< eval env x

eval env (SVar i) = lookup env i
eval env (SLam n t) = VLam n (Cl env t)
eval env (SApp f n x) = app (eval env f) n (eval env x)
eval env (SPi n a b) = VPi n (eval env a) (Cl env b)
eval env (SLet n a b) = eval (env :< eval env a) b
eval env SU = VU
eval env (SGlob n sp) = VGlob n (evalSpine env sp)

appSpine : STm gs ns -> Spine (STm gs) ps ns -> STm gs ns
appSpine f Lin = f
appSpine f ((:<) {n = n} xs x) = SApp (appSpine f xs) n x

public export
quote : Size ns -> VTm gs ns -> STm gs ns

quoteSpine : Size ns -> Spine (VTm gs) ps ns -> Spine (STm gs) ps ns
quoteSpine s [<] = [<]
quoteSpine s (xs :< x) = quoteSpine s xs :< quote s x

quote s (VLam n (Cl env t)) = SLam n $ quote (SS s) (eval (weakenEnv env :< VVar (lastLvl s)) t)
quote s (VRigid l sp) = appSpine (SVar (lvlToIdx s l)) (quoteSpine s sp)
quote s (VPi n a (Cl env t)) = SPi n (quote s a) (quote (SS s) (eval (weakenEnv env :< VVar (lastLvl s)) t))
quote s VU = SU
quote s (VGlob n sp) = SGlob n (quoteSpine s sp)

nf : Size ns -> STm gs ns -> STm gs ns
nf s t = quote s (eval idEnv t)

public export
sub : Env gs n m -> VTm gs m -> VTm gs n
sub env t = eval env (quote (env.size) t)

public export
closeVal : Env gs ns ks -> VTm gs (ks :< u) -> Closure gs u ns
closeVal env t = Cl env (quote (SS env.size) t)
