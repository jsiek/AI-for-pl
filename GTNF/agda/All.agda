module All where

-- Aggregate driver for GTNF (GTNF/design.md): type-checking this module
-- type-checks the whole development.  The definitional layer is forked
-- from SystemF/agda/strong-rep-nu (System νF) and extended with ★,
-- coercions, casts and blame; the completed M1 type-safety proofs are
-- imported below.

open import Types
open import proof.Types
open import Ctx
open import proof.Ctx
open import Lookup
open import Boundary
open import Conversion
open import Coercion
open import Terms
open import TermSubst
open import Reduction

-- executable, derivation-producing type checking, and the step function
open import examples.TypeCheck
open import examples.Eval

-- design.md §8's examples, run by `refl`
open import examples.Examples

-- pairs of programs for designing the cast-term imprecision
-- type imprecision (GTSFImp's, design.md §12.1)
open import Imprecision

open import examples.ImprecisionExamples

-- cast-term imprecision (design.md §12.2-§12.3): worlds, the relation,
-- and sanity derivations on the pairs above
open import ImprecisionWorld
open import ConversionImprecision
open import TermImprecision
open import examples.TermImprecisionExamples

-- the term-imprecision examples of papers/cambridge26.lagda.md, run
open import examples.CambridgeExamples

-- term imprecision at the blocks where cambridge26 uses (split)/(extend)
open import examples.TermImprecisionRebaseExamples

-- de Bruijn → named rendering (scripts/render_gtnf.sh)
open import examples.Show

-- the statement of the dynamic gradual guarantee (proof/DGG/PLAN.md §2)
open import DynamicGradualGuarantee

-- the statements of progress, preservation, irreducibility, and determinism
open import TypeSafety

-- completed M1 proofs
open import proof.TypeSafety.Progress
open import proof.TypeSafety.Preservation
open import proof.TypeSafety.Irreducible
open import proof.TypeSafety.Determinism

-- world evolution along two runs, W ⟿[ ξs ∣ ξs′ ] W′ (proof/DGG/PLAN.md §3)
open import proof.DGG.Evolve

-- the statements of the DGG's major lemmas (proof/DGG/*Def.agda, PLAN.md §3)
open import proof.DGG.SimDef
open import proof.DGG.MultiSimDef
open import proof.DGG.SimBackDef
open import proof.DGG.MultiSimBackDef
open import proof.DGG.CatchupRightDef
open import proof.DGG.CatchupLeftDef
open import proof.DGG.CatchupBlameDef
open import proof.DGG.EvolveImpDef
open import proof.DGG.ImprecisionTypingDef

-- facts about runs and evolution, and typing along a run (helpers)
open import proof.DGG.EvolveLemmas
import proof.DGG.RunTyping

-- hole-free Proof modules, parameterized by the statements they use
import proof.DGG.DynamicGradualGuaranteeProof
import proof.DGG.MultiSimProof
import proof.DGG.MultiSimBackProof

-- finished DGG lemmas (Lemma modules)
open import proof.DGG.ImprecisionTyping
open import proof.DGG.CatchupBlame
