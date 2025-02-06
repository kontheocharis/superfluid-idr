module Surface.Elaboration

import Core.Definitions
import Common
import Context
import Surface.Presyntax
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Weakening
import Core.Typechecking

import Data.DPair
import Data.SnocList
import Data.SnocList.Elem

public export
data ElabError : Type where
  CannotInferLam : ElabError

public export
interface (Tc m) => Elab m where
  elabError : ElabError -> m a
  
errorElab : (Elab m) => {md : TcMode} -> ElabError -> Typechecker m md i i'
errorElab e = InError $ elabError e

public export covering
elab : (Elab m) => (md : TcMode) -> {auto _ : IsTmMode md}
  -> PTm
  -> Typechecker m md (gs, ns, bs) (gs, ns, bs)

elabPat : (Elab m)
  => PPat
  -> WithIrrNamesN 2 (\pns => \pbs => Typechecker m Bind (gs, ns, bs) (gs, ns ++ pns, bs ++ pbs))

covering
elabBranch : (Elab m) => (md : TcMode) -> {auto _ : IsTmMode md}
  -> (Loc, PPat, PTm)
  -> WithIrrNamesN 2 (BranchTypechecker m md (gs, ns, bs))
elabBranch md (l, p, t) =
  let Evidence pns (Evidence pbs p') = elabPat p in
  let t' = elab md t in
  Evidence pns (Evidence pbs (p', t'))

covering
elabBranches : (Elab m) => (md : TcMode) -> {auto _ : IsTmMode md}
  -> PBranches
  -> IrrNameListN 2 (BranchTypechecker m md (gs, ns, bs))
elabBranches md (MkPBranches brs) =
  let brs' : SnocList _ = cast brs in
  map (elabBranch md) brs'

elab md (PLoc l t) = InLoc l (elab md t)
elab Check (PLam n Nothing t) = lam n (elab Check t)
elab md (PLet n Nothing a b) = letIn n (elab Infer a) (elab md b)
elab md (PLet n (Just ty) a b) = typedLetIn n (elab Check ty) (elab Check a) (elab md b)
elab md (PCase s bs) = caseOf (elab Infer s) (elabBranches md bs)
elab Check u = switch (elab Infer u)
elab Infer (PLam n (Just ty) t) = typedLam n (elab Check ty) (elab Infer t)
elab Infer (PLam n Nothing t) = errorElab CannotInferLam
elab Infer (PPi n a b) = pi n (elab Check a) (elab Check b)
elab Infer (PApp f x) = app (elab Infer f) (elab Check x)
elab Infer (PName n) = named n
elab Infer PU = u

covering
elabTel : (Elab m) => PTel -> Exists (\ps => TelTypechecker m (gs, ns, bs) ps)
elabTel (MkPTel [<]) = Evidence _ [<]
elabTel (MkPTel (ts :< (l, n, t))) = Evidence _ (snd (elabTel (MkPTel ts)) :< (n, InLoc l $ elab Check t))

covering
elabCtors : (Elab m) => PFields -> (Exists (\cs => CtorsTypechecker m (gs, ns, ns) cs))
elabCtors (MkPFields [<]) = Evidence _ [<]
elabCtors (MkPFields (cs :< (l, n, pr, ret))) =
  let Evidence _ cs' = elabCtors (MkPFields cs) in
  let t' = InLoc l $ elab Check ret in
  Evidence _ (With cs' n (snd (elabTel pr)) t')

covering
elabItem : (Elab m)
  => (i : PItem)
  -> Exists (\gs' => Typechecker m Item (gs, [<], [<]) (gs', [<], [<]))
elabItem (PDef n pr ty tm) = Evidence _ (defItem n (snd (elabTel pr)) (elab Check ty) (elab Check tm))
elabItem (PPrim n pr ty) = Evidence _ (primItem n (snd (elabTel pr)) (elab Check ty))
elabItem (PData n pr ind cs) = Evidence _ (dataItem n (snd (elabTel pr)) (snd (elabTel ind)) (snd (elabCtors cs)))

public export covering
elabSig : (Elab m) => PSig -> m (Exists (\gs => Sig gs))
elabSig (MkPSig [<]) = pure $ Evidence _ Lin
elabSig (MkPSig (sig :< (l, it))) = do 
  Evidence _ sig' <- elabSig (MkPSig sig)
  elabSig' l it sig'
  where
    elabSig' : Loc -> (i : PItem) -> Sig gs -> m (Exists (\gs' => Sig gs'))
    elabSig' l it sig = globally (InLoc l $ snd (elabItem it)) (MkContext sig [<]) >>= \g => pure $ Evidence _ g.global