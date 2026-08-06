module InterpreterAdequacy.proof.DivergenceProof where

-- File Charter:
--   * Proves both directions of divergence adequacy for closed, typed direct-
--     interpreter source terms.
--   * Derives positive small-step divergence from timeout at every fuel and
--     derives timeout at every fuel from positive divergence.
--   * Reuses terminal adequacy, progress, preservation, and irreducibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Core.InterpreterOutcome using (timed≢blamed; timed≢returned)
open import Interpreter using (World; blamed; returned; run; timed)
open import InterpreterAdequacy.DivergenceRelation using (Diverges)
open import InterpreterAdequacy.RunBlameSoundness using
  (run-blame-soundᵢ)
open import InterpreterAdequacy.RunReturnSoundness using
  (run-return-soundᵢ)
open import InterpreterAdequacy.SmallStepBlameCompleteness using
  (small-step-blame-completeᵢ)
open import InterpreterAdequacy.SmallStepReturnCompleteness using
  (small-step-return-completeᵢ)
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import NuMetaTheory using
  (multi-preservation; multi-runtime-preservation; progress)
open import NuReduction using (_—↠[_]_)
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import Typing.InterpreterTypeSoundness using (interpreter-type-sound)
import NuTerms as N
open import proof.DGG.Core.NuDGGClosedWorld using (empty-store-wf)
open import proof.DGG.Core.NuProgress using (crash; done; step)
open import proof.DGG.Core.NuReductionDeterminism using
  (blame-irreducible; value-irreducible)

run-timeout-soundᵖ : ∀ {M A}
  → InterpreterTerm M
  → N._∣_∣_⊢_⦂_ zero [] [] M A
  → (∀ n → Σ[ W ∈ World ] run M n ≡ timed W)
  → Diverges M
run-timeout-soundᵖ {M} {A} image M⊢ all-timeout {χs} {P} M↠P
    with progress P-ok P⊢
  where
  runtime-ok : N.RuntimeOK M
  runtime-ok = N.ok-no (interpreter-term-no-bullet image)

  P-ok : N.RuntimeOK P
  P-ok =
    multi-runtime-preservation
      empty-store-wf runtime-ok M⊢ M↠P

  P⊢ : N._∣_∣_⊢_⦂_
    (NuReduction.applyTyCtxs χs zero)
    (NuReduction.applyStores χs []) [] P
    (NuReduction.applyTys χs A)
  P⊢ =
    multi-preservation empty-store-wf runtime-ok M⊢ M↠P
run-timeout-soundᵖ image M⊢ all-timeout M↠P | step P→Q =
  _ , _ , P→Q
run-timeout-soundᵖ image M⊢ all-timeout M↠P | done vP
    with small-step-return-completeᵢ image M⊢ M↠P vP
run-timeout-soundᵖ image M⊢ all-timeout M↠P | done vP
    | n , W , V , world-agreement , return-eq , V-agrees
    with all-timeout n
run-timeout-soundᵖ image M⊢ all-timeout M↠P | done vP
    | n , W , V , world-agreement , return-eq , V-agrees
    | U , timeout-eq =
  ⊥-elim (timed≢returned (trans (sym timeout-eq) return-eq))
run-timeout-soundᵖ image M⊢ all-timeout M↠P | crash refl
    with small-step-blame-completeᵢ image M⊢ M↠P
run-timeout-soundᵖ image M⊢ all-timeout M↠P | crash refl
    | n , W , blame-eq
    with all-timeout n
run-timeout-soundᵖ image M⊢ all-timeout M↠P | crash refl
    | n , W , blame-eq | U , timeout-eq =
  ⊥-elim (timed≢blamed (trans (sym timeout-eq) blame-eq))

small-step-divergence-completeᵖ : ∀ {M A}
  → InterpreterTerm M
  → N._∣_∣_⊢_⦂_ zero [] [] M A
  → Diverges M
  → ∀ n → Σ[ W ∈ World ] run M n ≡ timed W
small-step-divergence-completeᵖ image M⊢ diverges n
    with interpreter-type-sound n image M⊢
small-step-divergence-completeᵖ image M⊢ diverges n
    | inj₁ (W , timeout-eq) =
  W , timeout-eq
small-step-divergence-completeᵖ image M⊢ diverges n
    | inj₂ (inj₁ (W , blame-eq))
    with run-blame-soundᵢ n image M⊢ blame-eq
small-step-divergence-completeᵖ image M⊢ diverges n
    | inj₂ (inj₁ (W , blame-eq))
    | χs , world-agreement , M↠blame
    with diverges M↠blame
small-step-divergence-completeᵖ image M⊢ diverges n
    | inj₂ (inj₁ (W , blame-eq))
    | χs , world-agreement , M↠blame
    | χ , Q , blame→Q =
  ⊥-elim (blame-irreducible blame→Q)
small-step-divergence-completeᵖ image M⊢ diverges n
    | inj₂ (inj₂ (W , V , return-eq , W⊢ , V⊢))
    with run-return-soundᵢ n image M⊢ return-eq
small-step-divergence-completeᵖ image M⊢ diverges n
    | inj₂ (inj₂ (W , V , return-eq , W⊢ , V⊢))
    | χs , v , world-agreement , M↠v , vV , V-agrees
    with diverges M↠v
small-step-divergence-completeᵖ image M⊢ diverges n
    | inj₂ (inj₂ (W , V , return-eq , W⊢ , V⊢))
    | χs , v , world-agreement , M↠v , vV , V-agrees
    | χ , Q , v→Q =
  ⊥-elim (value-irreducible vV v→Q)
