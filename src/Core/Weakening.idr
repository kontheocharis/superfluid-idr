module Core.Weakening

import Common
import Context
import Core.Syntax
import Core.Values

import Data.SnocList

mutual
  public export
  weakenClosure : Closure gs n ns -> Closure gs n (ns :< n')
  weakenClosure (Cl vs env t) = Cl vs (weakenSpine env) t
  
  public export
  weakenMaybeLazyVTm : Maybe (Lazy (VTm gs ns)) -> Maybe (Lazy (VTm gs (ns :< n)))
  weakenMaybeLazyVTm (Just t) = Just $ delay (weakenVTm (assert_smaller (Just t) (force t)))
  weakenMaybeLazyVTm Nothing = Nothing

  public export
  weakenVTm : VTm gs ns -> VTm gs (ns :< n)
  weakenVTm (VLam n cl) = VLam n (weakenClosure cl)
  weakenVTm (VRigid i sp) = VRigid (weaken i) (weakenSpine sp)
  weakenVTm (VPi n a cl) = VPi n (weakenVTm a) (weakenClosure cl)
  weakenVTm VU = VU
  weakenVTm (VGlob n sp pp gl) = VGlob n (weakenSpine sp) (weakenSpine pp) (weakenMaybeLazyVTm gl)

  public export
  weakenSpine : Spine (VTm gs) ps ns -> Spine (VTm gs) ps (ns :< n)
  weakenSpine [<] = [<]
  weakenSpine (xs :< x) = weakenSpine xs :< weakenVTm x
  
  public export
  weakenVTel : VTel gs ps ns -> VTel gs ps (ns :< n)
  weakenVTel [<] = [<]
  weakenVTel (xs :< (m, cl)) = weakenVTel xs :< (m, weakenClosure cl)
  
  public export
  globWeakenVTel : VTel gs ps ns -> VTel (gs :< g) ps ns
  globWeakenVTel [<] = [<]
  globWeakenVTel (xs :< (m, cl)) = globWeakenVTel xs :< (m, globWeakenClosure cl)

  public export
  globReorderVTel : VTel (gs :< g :< g') ps ns -> VTel (gs :< g' :< g) ps ns
  globReorderVTel [<] = [<]
  globReorderVTel (xs :< (m, cl)) = globReorderVTel xs :< (m, globReorderClosure cl)

  public export
  globWeakenSTm : STm gs ns -> STm (gs :< g) ns
  globWeakenSTm (SVar i) = SVar i
  globWeakenSTm (SLam n t) = SLam n (globWeakenSTm t)
  globWeakenSTm (SApp f n a) = SApp (globWeakenSTm f) n (globWeakenSTm a)
  globWeakenSTm (SPi n a b) = SPi n (globWeakenSTm a) (globWeakenSTm b)
  globWeakenSTm SU = SU
  globWeakenSTm (SLet n a b) = SLet n (globWeakenSTm a) (globWeakenSTm b)
  globWeakenSTm (SGlob n sp) = SGlob (globWeaken n) (globWeakenSTmSpine sp)
  
  public export
  globReorderSTm : STm (gs :< g :< g') ns -> STm (gs :< g' :< g) ns
  globReorderSTm (SVar i) = SVar i
  globReorderSTm (SLam n t) = SLam n (globReorderSTm t)
  globReorderSTm (SApp f n a) = SApp (globReorderSTm f) n (globReorderSTm a)
  globReorderSTm (SPi n a b) = SPi n (globReorderSTm a) (globReorderSTm b)
  globReorderSTm SU = SU
  globReorderSTm (SLet n a b) = SLet n (globReorderSTm a) (globReorderSTm b)
  globReorderSTm (SGlob n sp) = SGlob (globReorder n) (globReorderSTmSpine sp)

  public export
  globWeakenSTmSpine : Spine (STm gs) ps ns -> Spine (STm (gs :< g)) ps ns
  globWeakenSTmSpine [<] = [<]
  globWeakenSTmSpine (sp :< t) = globWeakenSTmSpine sp :< globWeakenSTm t

  public export
  globReorderSTmSpine : Spine (STm (gs :< g :< g')) ps ns -> Spine (STm (gs :< g' :< g)) ps ns
  globReorderSTmSpine [<] = [<]
  globReorderSTmSpine (sp :< t) = globReorderSTmSpine sp :< globReorderSTm t

  public export
  globWeakenVTmSpine : Spine (VTm gs) ps ns -> Spine (VTm (gs :< g)) ps ns
  globWeakenVTmSpine [<] = [<]
  globWeakenVTmSpine (sp :< t) = globWeakenVTmSpine sp :< globWeakenVTm t

  public export
  globReorderVTmSpine : Spine (VTm (gs :< g :< g')) ps ns -> Spine (VTm (gs :< g' :< g)) ps ns
  globReorderVTmSpine [<] = [<]
  globReorderVTmSpine (sp :< t) = globReorderVTmSpine sp :< globReorderVTm t

  public export
  globWeakenSpine : {0 f : GlobNamed (Named Type)} -> (f gs ns -> f (gs :< g) ns) -> Spine (f gs) ps ns -> Spine (f (gs :< g)) ps ns
  globWeakenSpine n [<] = [<]
  globWeakenSpine {f} n (sp :< t) = globWeakenSpine {f} n sp :< n t
  
  public export
  globReorderSpine : {0 f : GlobNamed (Named Type)} -> (f (gs :< g :< g') ns -> f (gs :< g' :< g) ns) -> Spine (f (gs :< g :< g')) ps ns -> Spine (f (gs :< g' :< g)) ps ns
  globReorderSpine n [<] = [<]
  globReorderSpine {f} n (sp :< t) = globReorderSpine {f} n sp :< n t

  public export
  globWeakenTel : (GlobWeaken f) => Tel (f gs) ps ns -> Tel (f (gs :< g)) ps ns
  globWeakenTel [<] = [<]
  globWeakenTel (sp :< (n, t)) = globWeakenTel sp :< (n, globWeaken t)

  public export
  globReorderTel : (GlobWeaken f) => Tel (f (gs :< g :< g')) ps ns -> Tel (f (gs :< g' :< g)) ps ns
  globReorderTel [<] = [<]
  globReorderTel (sp :< (n, t)) = globReorderTel sp :< (n, globReorder t)

  public export
  globWeakenEnv : Env gs ns ms -> Env (gs :< g) ns ms
  globWeakenEnv [<] = [<]
  globWeakenEnv (xs :< x) = globWeakenEnv xs :< globWeakenVTm x

  public export
  globReorderEnv : Env (gs :< g :< g') ns ms -> Env (gs :< g' :< g) ns ms
  globReorderEnv [<] = [<]
  globReorderEnv (xs :< x) = globReorderEnv xs :< globReorderVTm x

  public export
  globWeakenClosure : Closure gs n ns -> Closure (gs :< g) n ns
  globWeakenClosure (Cl vs env t) = Cl vs (globWeakenEnv env) (globWeakenSTm t)

  public export
  globReorderClosure : Closure (gs :< g :< g') n ns -> Closure (gs :< g' :< g) n ns
  globReorderClosure (Cl vs env t) = Cl vs (globReorderEnv env) (globReorderSTm t)
  
  public export
  globWeakenMaybeLazyVTm : Maybe (Lazy (VTm gs ns)) -> Maybe (Lazy (VTm (gs :< g) ns))
  globWeakenMaybeLazyVTm (Just t) = Just $ delay (globWeakenVTm (assert_smaller (Just t) (force t)))
  globWeakenMaybeLazyVTm Nothing = Nothing

  public export
  globWeakenVTm : VTm gs ns -> VTm (gs :< g) ns
  globWeakenVTm (VLam n cl) = VLam n (globWeakenClosure cl)
  globWeakenVTm (VRigid i sp) = VRigid i (globWeakenVTmSpine sp)
  globWeakenVTm (VPi n a cl) = VPi n (globWeakenVTm a) (globWeakenClosure cl)
  globWeakenVTm VU = VU
  globWeakenVTm (VGlob n sp pp t) = VGlob (globWeaken n) (globWeakenVTmSpine sp) (globWeakenVTmSpine pp) (globWeakenMaybeLazyVTm t)

  public export
  globReorderMaybeLazyVTm : Maybe (Lazy (VTm (gs :< g :< g') ns)) -> Maybe (Lazy (VTm (gs :< g' :< g) ns))
  globReorderMaybeLazyVTm (Just t) = Just $ delay (assert_total (globReorderVTm (force t)))
  globReorderMaybeLazyVTm Nothing = Nothing

  public export
  globReorderVTm : VTm (gs :< g :< g') ns -> VTm (gs :< g' :< g) ns
  globReorderVTm (VLam n cl) = VLam n (globReorderClosure cl)
  globReorderVTm (VRigid i sp) = VRigid i (globReorderVTmSpine sp)
  globReorderVTm (VPi n a cl) = VPi n (globReorderVTm a) (globReorderClosure cl)
  globReorderVTm VU = VU
  globReorderVTm (VGlob n sp pp t) = VGlob (globReorder n) (globReorderVTmSpine sp) (globReorderVTmSpine pp) (globReorderMaybeLazyVTm t)

  public export
  idEnv : {auto s : Size ns} -> Env gs ns ns
  idEnv {s = SZ} = [<]
  idEnv {s = (SS n)} = growEnv n (idEnv {s = n})

  public export
  growEnv : (s : Size ns) -> Env gs ns ms -> Env gs (ns :< n) (ms :< m)
  growEnv s env = weakenSpine env :< VVar (lastLvl s)

public export
GlobWeaken (\gs => \ns => Env gs ns ms) where
  globWeaken = globWeakenEnv
  globReorder = globReorderEnv

public export
Weaken (\ns => Spine (VTm gs) ps ns) where
  weaken = weakenSpine

public export
Weaken (Closure gs n) where
  weaken = weakenClosure

public export
GlobWeaken (\gs => \ns => Closure gs n ns) where
  globWeaken = globWeakenClosure
  globReorder = globReorderClosure

public export
Weaken (VTm gs) where
  weaken = weakenVTm

public export
GlobWeaken VTm where
  globWeaken = globWeakenVTm
  globReorder = globReorderVTm

public export
Weaken (VTerm gs) where
  weaken v = MkVTerm (weaken v.ty) (weaken v.tm)

public export
GlobWeaken VTerm where
  globWeaken v = MkVTerm (globWeaken v.ty) (globWeaken v.tm)
  globReorder v = MkVTerm (globReorder v.ty) (globReorder v.tm)

public export
[globWeakenForSpine] GlobWeaken f => GlobWeaken (\gs => Spine (f gs) ps) where
  globWeaken = globWeakenSpine {f = f} globWeaken
  globReorder = globReorderSpine {f = f} globReorder

public export
[globWeakenForTel] GlobWeaken f => GlobWeaken (\gs => Tel (f gs) ps) where
  globWeaken = globWeakenTel
  globReorder = globReorderTel

public export
GlobWeaken (\gs => Tel (VTm gs) ps) where
  globWeaken = globWeakenTel
  globReorder = globReorderTel
  
Weaken (VTel gs ps) where
  weaken = weakenVTel

public export
[globWeakenForVTel] GlobWeaken (\gs => VTel gs ps) where
  globWeaken = globWeakenVTel
  globReorder = globReorderVTel

public export
GlobWeaken (\gs => Spine (VTm gs) ps) where
  globWeaken = globWeakenSpine {f = VTm} globWeaken
  globReorder = globReorderSpine {f = VTm} globReorder

public export
GlobWeaken STm where
  globWeaken = globWeakenSTm
  globReorder = globReorderSTm

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

public export
weakenEnv : Env gs ns ms -> Env gs (ns :< n) ms
weakenEnv = weakenSpine