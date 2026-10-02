module T6D8a4PostMigrationCallerSupplyProbe where

-- File Charter:
--   * Re-runs the D8a2 caller-supplied boundary-environment refutation after
--     the D15 source-conceal migration.
--   * Uses a source-conceal boundary and handles the new
--     `conceal⊑²-source-ok` head explicitly.
--   * Contains only checked witnesses and exhaustive negative inversions; it
--     is not imported by the live DGG development.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)

open import Types using (★; ＇_; `ℕ; ‵_)
open import Consistency using (Env∼; X∼★; _⊢_∼_; id; _!)
open import Imprecision using (★⊑★)
open import CastTerms using (Term; Value; singleSub; $; _⟨_⟩)
import CastTerms as CT
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.CatchupToMorePreciseDef using
  (boundary-source-conceal)
open import T6D8a2RepairDraftProbe using
  ( BoundaryStackReachable
  ; TermSubstRelBoundary
  ; boundary-node
  ; reachable-boundary
  ; reachable-root
  )
import T6D8a2ClosedValueRebaseTransportProbe as P


source-env : Env∼ 1
source-env _ = X∼★

target-env : Env∼ 2
target-env _ = X∼★

source-X! : source-env ⊢ ＇ P.X ∼ ★
source-X! = id {μ = source-env} (＇ P.X) !

target-Y-old! : target-env ⊢ ＇ P.Y-old ∼ ★
target-Y-old! = id {μ = target-env} (＇ P.Y-old) !

source-argument : Term 1
source-argument = P.source-sealed ⟨ source-X! ⟩

target-argument : Term 2
target-argument = P.target-old-sealed ⟨ target-Y-old! ⟩

source-argument-value : Value source-argument
source-argument-value = P.source-sealed-value CT.《 CT.inj 》

target-argument-value : Value target-argument
target-argument-value = P.target-old-sealed-value CT.《 CT.inj 》

argument-at-W :
  P.W CTI2.∣ [] ⊢² source-argument ⊑ target-argument ∶ ★⊑★
argument-at-W =
  CTI2.cast⊑cast² source-X! target-Y-old! P.entangled-at-W ★⊑★

root-source-ctx : CTI2.CtxImp P.W
root-source-ctx = CTI2.ctx-imp ★ ★ ★⊑★ ∷ []

premise-source-ctx : CTI2.CtxImp P.Wᵖ
premise-source-ctx = CTI2.ctx-imp ★ ★ ★⊑★ ∷ []

root-node : T6D8a2RepairDraftProbe.BoundaryNode
root-node = boundary-node P.W root-source-ctx []

premise-node : T6D8a2RepairDraftProbe.BoundaryNode
premise-node = boundary-node P.Wᵖ premise-source-ctx []

premise-reachable : BoundaryStackReachable root-node premise-node
premise-reachable =
  reachable-boundary reachable-root
    (boundary-source-conceal P.mono-forward
      (CTI2.tag-rebase-varᴸ P.reversed-rebase))
    (CTI2.same-∷ CTI2.same-[])
    CTI2.same-[]

base-to-target-variable-empty : ∀ {W′ : CTI2.World 1 2 2}
  → (‵ `ℕ) CTI2.⊑ᵂ⟨ W′ ⟩ (＇ P.Y-old)
  → ⊥
base-to-target-variable-empty ()

constant-to-target-tag-empty : ∀ {W′ : CTI2.World 1 2 2}
    {p : (‵ `ℕ) CTI2.⊑ᵂ⟨ W′ ⟩ ★}
  → W′ CTI2.∣ [] ⊢² P.source-value ⊑ target-argument ∶ p
  → ⊥
constant-to-target-tag-empty {W′ = W′}
    (CTI2.⊑cast² {p = p} c′ rel q) =
  base-to-target-variable-empty {W′ = W′} p

source-seal-to-target-tag-empty :
  ∀ {p : (＇ P.X) CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ ★}
  → P.Wᵖ CTI2.∣ [] ⊢² P.source-sealed ⊑ target-argument ∶ p
  → ⊥
source-seal-to-target-tag-empty
    (CTI2.⊑cast² {p = p} c′ rel q) =
  P.pivot-old-at-Wᵖ-empty p
source-seal-to-target-tag-empty
    (CTI2.conceal⊑² ok mono rebase CTI2.same-[] c⊢ rel q) =
  constant-to-target-tag-empty rel
source-seal-to-target-tag-empty
    (CTI2.conceal⊑²-source-ok ok mono rebase CTI2.same-[] c⊢ rel q) =
  constant-to-target-tag-empty rel

argument-at-Wᵖ-empty :
  P.Wᵖ CTI2.∣ [] ⊢² source-argument ⊑ target-argument ∶ ★⊑★
  → ⊥
argument-at-Wᵖ-empty
    (CTI2.cast⊑cast² {p = p} c c′ rel .★⊑★) =
  P.pivot-old-at-Wᵖ-empty p
argument-at-Wᵖ-empty
    (CTI2.⊑cast² {p = p} c′ rel .★⊑★) with p
argument-at-Wᵖ-empty
    (CTI2.⊑cast² {p = p} c′ rel .★⊑★) | ()
argument-at-Wᵖ-empty
    (CTI2.cast⊑² c rel .★⊑★) =
  source-seal-to-target-tag-empty rel

caller-boundary-environment-empty :
  TermSubstRelBoundary root-node
    (singleSub source-argument) (singleSub target-argument)
  → ⊥
caller-boundary-environment-empty env =
  argument-at-Wᵖ-empty
    (T6D8a2RepairDraftProbe.TermSubstRelBoundary.lookup env
      premise-reachable CTI2.Zʷ)

CallerSupplyPostMigrationVerdict : Set₁
CallerSupplyPostMigrationVerdict =
  TermSubstRelBoundary root-node
    (singleSub source-argument) (singleSub target-argument)
  → ⊥

caller-supply-post-migration-verdict :
  CallerSupplyPostMigrationVerdict
caller-supply-post-migration-verdict = caller-boundary-environment-empty
