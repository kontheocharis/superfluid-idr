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
  -> (PPat, PTm)
  -> WithIrrNamesN 2 (BranchTypechecker m md (gs, ns, bs))
elabBranch md (p, t) =
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
elabTel : (Elab m) => PTel -> Exists (\ps => TelTypechecker m Check (gs, ns, bs) ps)
elabTel (MkPTel [<]) = Evidence _ [<]
elabTel (MkPTel (ts :< (n, t))) = Evidence _ (snd (elabTel (MkPTel ts)) :< (n, elab Check t))

covering
elabItem : (Elab m)
  => (i : PItem)
  -> Exists (\ps => Typechecker m Item (gs, [<], [<]) (gs :< (ps ** i.name), [<], [<]))
elabItem (PDef n pr ty tm) = Evidence _ (defItem n (snd (elabTel pr)) (elab Check ty) (elab Infer tm))
elabItem (PPrim n pr ty) = Evidence _ (primItem n (snd (elabTel pr)) (elab Check ty))
elabItem (PData n pr ty cs) = ?elabPData

public export covering
elabSig : (Elab m) => PSig -> m (Exists (\gs => Sig gs))
elabSig (MkPSig [<]) = pure $ Evidence _ Lin
elabSig (MkPSig (sig :< it)) = do 
  Evidence _ sig' <- elabSig (MkPSig sig)
  Evidence _ it' <- elabSig' it sig'
  pure $ Evidence _ (sig' ++ it')
  where
    elabSig' : (i : PItem) -> Sig gs -> m (Exists (\ps => Sig (gs :< (ps ** i.name))))
    elabSig' it sig = globally (snd $ elabItem it) (MkContext sig [<]) >>= \g => pure $ Evidence _ g.global