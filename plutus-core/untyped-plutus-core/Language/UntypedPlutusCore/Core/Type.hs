{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.UntypedPlutusCore.Core.Type
    ( TPLC.UniOf
    , TPLC.StaticBuiltinName (..)
    , TPLC.DynamicBuiltinName (..)
    , TPLC.BuiltinName (..)
    , Term (..)
    , termAnn
    , erase
    ) where

import           PlutusPrelude

import qualified Language.PlutusCore.Constant                       as TPLC
import qualified Language.PlutusCore.Core                           as TPLC
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Universe

-- | The type of Untyped Plutus Core terms. Mirrors the type of Typed Plutus Core terms except
--
-- 1. all types are removed
-- 2. 'IWrap' and 'Unwrap' are removed
-- 3. type abstractions are replaced with 'Delay'
-- 4. type instantiations are replaced with 'Force'
--
-- The latter two are due to the fact that we don't have value restriction in Typed Plutus Core
-- and hence a computation can be stuck expecting only a single type argument for the computation
-- to become unstuck. Therefore we can't just silently remove type abstractions and instantions and
-- need to replace them with something else that also blocks evaluation (in order for the semantics
-- of an erased program to match with the semantics of the original typed one). 'Delay' and 'Force'
-- serve exactly this purpose.
data Term name uni fun ann
    = Constant ann (Some (ValueOf uni))
    | Builtin ann TPLC.BuiltinName
    | Var ann name
    | LamAbs ann name (Term name uni fun ann)
    | Apply ann (Term name uni fun ann) (Term name uni fun ann)
    | Delay ann (Term name uni fun ann)
    | Force ann (Term name uni fun ann)
    | Error ann
    deriving (Show, Functor, Generic)

type instance TPLC.UniOf (Term name uni fun ann) = uni

instance TPLC.AsConstant (Term name uni fun ann) where
    asConstant (Constant _ val) = Just val
    asConstant _                = Nothing

instance TPLC.FromConstant (Term name uni fun ()) where
    fromConstant = Constant ()

instance ToExMemory (Term name uni fun ()) where
    toExMemory _ = 0

instance ToExMemory (Term name uni fun ExMemory) where
    toExMemory = termAnn

deriving via GenericExMemoryUsage (Term name uni fun ann) instance
    ( ExMemoryUsage name, ExMemoryUsage ann
    , Closed uni, uni `Everywhere` ExMemoryUsage
    ) => ExMemoryUsage (Term name uni fun ann)

-- | Return the outermost annotation of a 'Term'.
termAnn :: Term name uni fun ann -> ann
termAnn (Constant ann _) = ann
termAnn (Builtin ann _)  = ann
termAnn (Var ann _)      = ann
termAnn (LamAbs ann _ _) = ann
termAnn (Apply ann _ _)  = ann
termAnn (Delay ann _)    = ann
termAnn (Force ann _)    = ann
termAnn (Error ann)      = ann

-- | Erase a Typed Plutus Core term to its untyped counterpart.
erase :: TPLC.Term tyname name uni fun ann -> Term name uni fun ann
erase (TPLC.Var ann name)           = Var ann name
erase (TPLC.TyAbs ann _ _ body)     = Delay ann (erase body)
erase (TPLC.LamAbs ann name _ body) = LamAbs ann name (erase body)
erase (TPLC.Apply ann fun arg)      = Apply ann (erase fun) (erase arg)
erase (TPLC.Constant ann con)       = Constant ann con
erase (TPLC.Builtin ann bn)         = Builtin ann bn
erase (TPLC.TyInst ann term _)      = Force ann (erase term)
erase (TPLC.Unwrap _ term)          = erase term
erase (TPLC.IWrap _ _ _ term)       = erase term
erase (TPLC.Error ann _)            = Error ann
