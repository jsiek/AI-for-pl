module LR-narrow.LRNarrowAll where

-- File Charter:
--   * Type-checking aggregate for the GTSFImp interpreter logical relation.
--   * Exposes paired worlds, computation observations, the core LR, and the
--     fundamental dynamic-payload constructors.

open import LR-narrow.World public
open import LR-narrow.Computation public
open import LR-narrow.TargetEvaluation public
open import LR-narrow.LogicalRelation public
open import LR-narrow.DynamicPayload public
open import LR-narrow.Closure public
open import LR-narrow.ClosingSubstitution public
open import LR-narrow.ClosingSubstitutionProperties public
open import LR-narrow.TermRelation public
open import LR-narrow.ImmediateReturn public
open import LR-narrow.Variable public
open import LR-narrow.Constant public
open import LR-narrow.Blame public
open import LR-narrow.Primitive public
open import LR-narrow.FunctionApplication public
open import LR-narrow.BetaExpansion public
open import LR-narrow.Lambda public
open import LR-narrow.Application public
open import LR-narrow.TypeBetaExpansion public
open import LR-narrow.Universal public
open import LR-narrow.UniversalInstantiation public
open import LR-narrow.TypeApplication public
open import LR-narrow.Cast public
open import LR-narrow.Fundamental public
open import LR-narrow.Insertion public

-- Assembly skeleton of the total theorem, parameterized by its remaining
-- obligations; imported so the aggregate check covers it.
import proof.LR-narrow.FundamentalAssembly
