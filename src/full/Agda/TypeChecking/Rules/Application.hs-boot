
module Agda.TypeChecking.Rules.Application where

import Data.List.NonEmpty (NonEmpty)

import Agda.Syntax.Common (NamedArg, ProjOrigin)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Debug (MonadDebug)
import Agda.TypeChecking.Monad.MetaVars (MonadMetaSolver)

checkArguments :: Comparison -> ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                  (ArgsCheckState CheckedTarget -> TCM Term) -> TCM Term

checkArguments_ :: Comparison -> ExpandHidden -> Range -> [NamedArg A.Expr] -> Telescope ->
                   TCM (Elims, Telescope)

checkApplication :: Comparison -> A.Expr -> A.Args -> A.Expr -> Type -> TCM Term

inferApplication :: ExpandHidden -> A.Expr -> A.Args -> A.Expr -> TCM (Term, Type)

checkProjAppToKnownPrincipalArg  :: Comparison -> A.Expr -> ProjOrigin -> NonEmpty QName -> A.Args -> Type -> Int -> Term -> Type -> PrincipalArgTypeMetas -> TCM Term

recordTypeInfo
  :: (MonadTCEnv m, ReadTCState m, MonadTCState m, HasRange marker, MonadDebug m, MonadMetaSolver m)
  => marker
  -> Type
  -> m ()
