module Extension.Eliminators

import Common
import Context
import Core.Syntax

import Extension.Inductive

IsCtor : Idx ns -> Names -> Type

data Ctor : Names -> Names -> Type where
  MkCtor : (i : Idx ns) -> IsCtor i ps -> Ctor ps ns

data Pat : Names -> Type where
  PatVar : Idx ns -> Pat ns
  PatCtor : Ctor ps ns -> Spine Pat ps ns -> Pat ns
