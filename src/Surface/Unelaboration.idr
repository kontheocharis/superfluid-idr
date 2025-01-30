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

unelabVal : {ns : Names} -> VTm gs ns -> PTm
unelabVal v = unelab (quote ns.size v)

public export
unelabSpine : {ns : Names} -> Spine (STm gs) ps ns -> SnocList PTm
unelabSpine [<] = [<]
unelabSpine (xs :< x) = unelabSpine xs :< unelab x

unelab (SLam n t) = PLam n Nothing (unelab t)
unelab (SPi n a b) = PPi n (unelab a) (unelab b)
unelab (SApp f n x) = PApp (unelab f) (unelab x)
unelab {ns} (SVar i) = PName (getName ns i)
unelab (SLet n a b) = PLet n Nothing (unelab a) (unelab b)
unelab (SGlob (MkGlobNameIn n _) sp) = pApps (PName n.name) (unelabSpine sp)
unelab SU = PU

public export
unelabTel : {ns : Names} -> {ps : Names} -> Tel (VTy gs) ps ns -> PTel
unelabTel Lin = MkPTel [<]
unelabTel (te :< (n, t)) = let MkPTel ts = unelabTel te in MkPTel (ts :< (n, unelabVal t))

public export
unelabItem : (sig : Sig gs) -> Item sig -> State (SnocList (Name, PFields)) PSig
unelabItem _ (Def (MkDefItem n pr ty tm)) = pure . MkPSig . cast $ [PDef n (unelabTel pr) (unelabVal ty) $ case tm of
  Just t => unelab t
  Nothing => PName (MkName "?")]
unelabItem sig (Data (MkDataItem n pr ind)) = do 
  ctors <- lookup n . toList <$> get
  pure . MkPSig . cast $ [PData n (unelabTel pr) (pPis (unelabTel ind) PU) (fromMaybe (MkPFields (MkPTel [<])) ctors)]
unelabItem _ (Prim (MkPrimItem n pr ty)) = pure . MkPSig . cast $ [PPrim n (unelabTel pr) (unelabVal ty)]
unelabItem sig it@(Ctor (MkCtorItem n _ _)) = do
  let ty = unelabVal (itemTy it)
  modify (modifyAt n (\(MkPFields (MkPTel ns)) => MkPFields (MkPTel (ns :< (n, ty)))))
  pure $ MkPSig [<]
  where
    modifyAt : (Eq a) => a -> (b -> b) -> SnocList (a, b) -> SnocList (a, b)
    modifyAt _ _ [<] = [<]
    modifyAt a' f (xs :< (a, b)) = if a == a' then xs :< (a, f b) else modifyAt a' f xs :< (a, b)

public export
unelabSig : Sig gs -> PSig 
unelabSig s = evalState [<] (unelabSig' s)
  where 
    unelabSig' : Sig gs' -> State (SnocList (Name, PFields)) PSig
    unelabSig' [<] = pure . MkPSig $ [<]
    unelabSig' (sig :< it) = do
      MkPSig it' <- unelabItem sig it
      MkPSig rest <- unelabSig' sig
      pure . MkPSig $ rest ++ it'

public export
partial covering
(ns : Names) => Show (STm gs ns) where
  show t = show (unelab t)

public export
partial covering
(ns : Names) => Show (VTm gs ns) where
  show t = show (quote ns.size t)

public export
partial covering
Show (Sig gs) where
  show t = show (unelabSig t)

public export
partial covering
Show TcError where
  show ExpectedPi = "Expected function type"
  show (Mismatch (Val bs) a b) = "Mismatch: " ++ show a ++ " vs " ++ show b
  show (NameNotFound n) = "Name " ++ show n ++ " not found"

public export
Show ElabError where
  show CannotInferLam = "Cannot infer type of lambda"
