module Core.Weakening

import Common
import Context
import Core.Syntax
import Core.Values

mutual
  weakenClosure : Closure gs n ns -> Closure gs n (ns :< n')
  weakenClosure (Cl env t) = Cl (weakenEnv env) t

  weakenVTm : VTm gs ns -> VTm gs (ns :< n)
  weakenVTm (VLam n cl) = VLam n (weakenClosure cl)
  weakenVTm (VRigid i sp) = VRigid (weaken i) (weakenSpine sp)
  weakenVTm (VPi n a cl) = VPi n (weakenVTm a) (weakenClosure cl)
  weakenVTm VU = VU
  weakenVTm (VGlob n sp) = VGlob n (weakenSpine sp)

  weakenEnv : Env gs ns ms -> Env gs (ns :< n) ms
  weakenEnv [<] = [<]
  weakenEnv (xs :< x) = weakenEnv xs :< weakenVTm x

  weakenSpine : Spine (VTm gs) ps ns -> Spine (VTm gs) ps (ns :< n)
  weakenSpine [<] = [<]
  weakenSpine (xs :< x) = weakenSpine xs :< weakenVTm x

  weakenTel : Tel (VTm gs) ps ns -> Tel (VTm gs) ps (ns :< n)
  weakenTel [<] = [<]
  weakenTel (xs :< (m, x)) = weakenTel xs :< (m, ?weakenVTmx)

  globWeakenSTm : STm gs ns -> STm (gs :< g) ns
  globWeakenSTm (SVar i) = SVar i
  globWeakenSTm (SLam n t) = SLam n (globWeakenSTm t)
  globWeakenSTm (SApp f n a) = SApp (globWeakenSTm f) n (globWeakenSTm a)
  globWeakenSTm (SPi n a b) = SPi n (globWeakenSTm a) (globWeakenSTm b)
  globWeakenSTm SU = SU
  globWeakenSTm (SLet n a b) = SLet n (globWeakenSTm a) (globWeakenSTm b)
  globWeakenSTm (SGlob n sp) = SGlob (globWeaken n) (globWeakenSTmSpine sp)

  globWeakenSTmSpine : Spine (STm gs) ps ns -> Spine (STm (gs :< g)) ps ns
  globWeakenSTmSpine [<] = [<]
  globWeakenSTmSpine (sp :< t) = globWeakenSTmSpine sp :< globWeakenSTm t

  globWeakenVTmSpine : Spine (VTm gs) ps ns -> Spine (VTm (gs :< g)) ps ns
  globWeakenVTmSpine [<] = [<]
  globWeakenVTmSpine (sp :< t) = globWeakenVTmSpine sp :< globWeakenVTm t

  globWeakenSpine : {0 f : GlobNamed (Named Type)} -> (f gs ns -> f (gs :< g) ns) -> Spine (f gs) ps ns -> Spine (f (gs :< g)) ps ns
  globWeakenSpine n [<] = [<]
  globWeakenSpine {f} n (sp :< t) = globWeakenSpine {f} n sp :< n t

  globWeakenTel : (GlobWeaken f) => Tel (f gs) ps ns -> Tel (f (gs :< g)) ps ns
  globWeakenTel [<] = [<]
  globWeakenTel (sp :< (n, t)) = globWeakenTel sp :< (n, globWeaken t)

  globWeakenEnv : Env gs ns ms -> Env (gs :< g) ns ms
  globWeakenEnv [<] = [<]
  globWeakenEnv (xs :< x) = globWeakenEnv xs :< globWeakenVTm x

  globWeakenClosure : Closure gs n ns -> Closure (gs :< g) n ns
  globWeakenClosure (Cl env t) = Cl (globWeakenEnv env) (globWeakenSTm t)

  globWeakenVTm : VTm gs ns -> VTm (gs :< g) ns
  globWeakenVTm (VLam n cl) = VLam n (globWeakenClosure cl)
  globWeakenVTm (VRigid i sp) = VRigid i (globWeakenVTmSpine sp)
  globWeakenVTm (VPi n a cl) = VPi n (globWeakenVTm a) (globWeakenClosure cl)
  globWeakenVTm VU = VU
  globWeakenVTm (VGlob n sp) = VGlob (globWeaken n) (globWeakenVTmSpine sp)

  public export
  Weaken (\ns => Env gs ns ms) where
    weaken = weakenEnv

  public export
  GlobWeaken (\gs => \ns => Env gs ns ms) where
    globWeaken = globWeakenEnv

  public export
  Weaken (\ns => Spine (VTm gs) ps ns) where
    weaken = weakenSpine

  public export
  Weaken (\ns => Tel (VTm gs) ps ns) where
    weaken = weakenTel

  public export
  Weaken (Closure gs n) where
    weaken = weakenClosure

  public export
  GlobWeaken (\gs => \ns => Closure gs n ns) where
    globWeaken = globWeakenClosure

  public export
  Weaken (VTm gs) where
    weaken = weakenVTm

  public export
  GlobWeaken VTm where
    globWeaken = globWeakenVTm

  public export
  Weaken (VTerm gs) where
    weaken v = MkVTerm (weaken v.ty) (weaken v.tm)

  public export
  GlobWeaken VTerm where
    globWeaken v = MkVTerm (globWeaken v.ty) (globWeaken v.tm)

  public export
  GlobWeaken f => GlobWeaken (\gs => Spine (f gs) ps) where
    globWeaken = globWeakenSpine {f = f} globWeaken

  public export
  GlobWeaken f => GlobWeaken (\gs => Tel (f gs) ps) where
    globWeaken = globWeakenTel

  public export
  GlobWeaken STm where
    globWeaken = globWeakenSTm

  public export
  idEnv : {auto s : Size ns} -> Env gs ns ns
  idEnv {s = SZ} = [<]
  idEnv {s = (SS n)} = growEnv n (idEnv {s = n})

  public export
  growEnv : (s : Size ns) -> Env gs ns ms -> Env gs (ns :< n) (ms :< m)
  growEnv s env = weakenEnv env :< VVar (lastLvl s)

public export
growEnvN : (s : Size ns) -> Size ps -> Env gs ns ms -> Env gs (ns ++ ps) (ms ++ ps)
growEnvN s SZ env = env
growEnvN s (SS n) env = growEnv (s + n) (growEnvN s n env)

public export
vHeres : Size ns -> Size ps -> Spine (VTm gs) ps (ns ++ ps)
vHeres n SZ = [<]
vHeres n (SS r) = weaken (vHeres n r) :< VVar (lastLvl (n + r))

public export
vHeres' : Size ps -> Spine (VTm gs) ps ps
vHeres' SZ = [<]
vHeres' (SS r) = weaken (vHeres' r) :< VVar (lastLvl r)