module Surface.Unelaboration

import Core.Definitions
import Data.SnocList
import Data.Singleton
import Common
import Context
import Surface.Presyntax
import Surface.Elaboration
import Core.Syntax
import Core.Values
import Core.Evaluation
import Core.Typechecking
import Control.Monad.State
import Data.Maybe
import Data.List

public export
unelab : {ns : Names} -> STm gs ns -> PTm

covering
unelabVal : {ns : Names} -> VTm gs ns -> PTm
unelabVal v = unelab (quote noReplace ns.size v)

covering
unelabClosure : {ns : Names} -> {us : Names} -> Closure gs us ns -> PTm
unelabClosure {ns} cl = unelabVal $ apply noReplace ns.size cl

public export
unelabSpine : {ns : Names} -> Spine (STm gs) ps ns -> SnocList PTm
unelabSpine [<] = [<]
unelabSpine (xs :< x) = unelabSpine xs :< unelab x

covering
unelabSpineVTm : {ns : Names} -> Spine (VTm gs) ps ns -> SnocList PTm
unelabSpineVTm [<] = [<]
unelabSpineVTm (xs :< x) = unelabSpineVTm xs :< unelabVal x

unelab (SLam n t) = PLam n Nothing (unelab t)
unelab (SPi n a b) = PPi n (unelab a) (unelab b)
unelab (SApp f n x) = PApp (unelab f) (unelab x)
unelab {ns} (SVar i) = PName (getName ns i)
unelab (SLet n a b) = PLet n Nothing (unelab a) (unelab b)
unelab (SGlob (MkGlobNameIn n _) sp) = pApps (PName n.name) (unelabSpine sp)
unelab SU = PU

public export covering
unelabTel : {ns : Names} -> {ps : Names} -> VTel gs ps ns -> PTel
unelabTel Lin = MkPTel [<]
unelabTel (te :< (n, t)) = let MkPTel ts = unelabTel te in MkPTel (ts :< (dummyLoc, n, unelabClosure t))

public export covering
unelabItem : (sig : Sig gs) -> Item sig -> State (SnocList (Name, PFields)) PSig
unelabItem _ (Def (MkDefItem n pr ty tm)) = pure . MkPSig . cast $ [(dummyLoc, PDef n (unelabTel pr) (unelabVal ty) $ case tm of
  Just t => unelab t
  Nothing => PName (MkName "?"))]
unelabItem sig (Data (MkDataItem n pr ind)) = do 
  ctors <- lookup n . toList <$> get
  pure . MkPSig . cast $ [(dummyLoc, PData n (unelabTel pr) (unelabTel ind) (fromMaybe (MkPFields [<]) ctors))]
unelabItem _ (Prim (MkPrimItem n pr ty)) = pure . MkPSig . cast $ [(dummyLoc, PPrim n (unelabTel pr) (unelabVal ty))]
unelabItem sig it@(Ctor (MkCtorItem n args ret)) = do
  let ty = unelabVal (itemTy it)
  let (args, ret) = pGatherPis ty
  modify (modifyAt n (\(MkPFields ns) => MkPFields (ns :< (dummyLoc, n, args, ret))))
  pure $ MkPSig [<]
  where
    modifyAt : (Eq a) => a -> (b -> b) -> SnocList (a, b) -> SnocList (a, b)
    modifyAt _ _ [<] = [<]
    modifyAt a' f (xs :< (a, b)) = if a == a' then xs :< (a, f b) else modifyAt a' f xs :< (a, b)

public export covering
unelabSig : Sig gs -> PSig 
unelabSig s = evalState [<] (unelabSig' s)
  where 
    covering
    unelabSig' : Sig gs' -> State (SnocList (Name, PFields)) PSig
    unelabSig' [<] = pure . MkPSig $ [<]
    unelabSig' (sig :< it) = do
      MkPSig it' <- unelabItem sig it
      MkPSig rest <- unelabSig' sig
      pure . MkPSig $ rest ++ it'

public export
covering
(ns : Names) => Show (STm gs ns) where
  show t = show (unelab t)

public export
covering
(ns : Names) => Show (VTm gs ns) where
  show t = show (quote noReplace ns.size t)

public export
covering
Show (Sig gs) where
  show t = show (unelabSig t)

public export
covering
Show TcError where
  show (ExpectedPi (Val _) t t') = "Expected function type, got " ++ show t ++ " (expanded: " ++ show t' ++ ")"
  show (Mismatch (Val bs) a b) = "Mismatch: " ++ show a ++ " vs " ++ show b
  show (NameNotFound n) = "Name " ++ show n ++ " not found"
  show (ExpectedFamily (Val _) t) = "Expected family (type ending in U), but got " ++ show t
  show (ExpectedData (Val _) t n) = "Expected return type in data family " ++ show n.name.name ++ ", but got " ++ show t

public export
Show ElabError where
  show CannotInferLam = "Cannot infer type of lambda"
