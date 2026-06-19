module proof.CoercionProperties where

-- File Charter:
--   * Proof-only metatheory for the redesigned GTSF coercion typing judgment.
--   * Establishes endpoint well-formedness and source/target agreement for the
--     seal-mode-aware coercion typing rules.
--   * General coercion renaming is intentionally deferred: the mode environment
--     must be transported together with any seal renaming.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import Types
open import Coercions
open import proof.TypeProperties using (rename-id)

------------------------------------------------------------------------
-- Lookup helpers
------------------------------------------------------------------------

seal-lookup-var :
  ∀ {Γ α A} →
  Γ ∋α α ⦂ A →
  Γ ∋ˢ α
seal-lookup-var Zα = Zˢ
seal-lookup-var (Sα-ty h) = Sˢ-ty (seal-lookup-var h)
seal-lookup-var (Sα-seal h) = Sˢ-seal (seal-lookup-var h)
seal-lookup-var (Sα-term h) = Sˢ-term (seal-lookup-var h)

------------------------------------------------------------------------
-- Raw type-operation facts for coercion seal binders
------------------------------------------------------------------------

dropSeal-rename-suc :
  ∀ ρ A →
  dropSeal (rename ρ suc A) ≡ rename ρ idˢ A
dropSeal-rename-suc ρ (`X X) = refl
dropSeal-rename-suc ρ (`α α) = refl
dropSeal-rename-suc ρ (‵ ι) = refl
dropSeal-rename-suc ρ ★ = refl
dropSeal-rename-suc ρ (A ⇒ B) =
  cong₂ _⇒_ (dropSeal-rename-suc ρ A) (dropSeal-rename-suc ρ B)
dropSeal-rename-suc ρ (`∀ A) = cong `∀ (dropSeal-rename-suc (extᵗ ρ) A)

dropSeal-shiftˢ :
  ∀ A →
  dropSeal (⇑ˢ A) ≡ A
dropSeal-shiftˢ A = trans (dropSeal-rename-suc idᵗ A) (rename-id A)

postulate
  close-openTyWithSeal :
    ∀ A →
    closeSealWithTy (openTyWithSeal A) ≡ A

------------------------------------------------------------------------
-- Inert coercions
------------------------------------------------------------------------

renameᶜ-preserves-Inert :
  ∀ ρ σ {c} →
  Inert c →
  Inert (renameᶜ ρ σ c)
renameᶜ-preserves-Inert ρ σ (G !) = rename ρ σ G !
renameᶜ-preserves-Inert ρ σ (seal A α) = seal (rename ρ σ A) (σ α)
renameᶜ-preserves-Inert ρ σ (c ↦ d) =
  renameᶜ ρ σ c ↦ renameᶜ ρ σ d
renameᶜ-preserves-Inert ρ σ (`∀ c) = `∀ (renameᶜ (extᵗ ρ) σ c)
renameᶜ-preserves-Inert ρ σ (gen c) = gen (renameᶜ ρ (extˢ σ) c)

------------------------------------------------------------------------
-- Coercion endpoint well-formedness
------------------------------------------------------------------------

coercion-wf :
  ∀ {μ Γ c A B} →
  μ ∣ Γ ⊢ c ∶ A =⇒ B →
  WfTy Γ A × WfTy Γ B
coercion-wf (cast-id hA) = hA , hA
coercion-wf (cast-seal hA okα hα) =
  hA , wfα (seal-lookup-var hα)
coercion-wf (cast-unseal hA okα hα) =
  wfα (seal-lookup-var hα) , hA
coercion-wf (cast-seq c⊢ d⊢) with coercion-wf c⊢ | coercion-wf d⊢
coercion-wf (cast-seq c⊢ d⊢) | hA , hB | hB′ , hC = hA , hC
coercion-wf (cast-tag hG gG okG) = hG , wf★
coercion-wf (cast-untag hH gH okH) = wf★ , hH
coercion-wf (cast-fun c⊢ d⊢) with coercion-wf c⊢ | coercion-wf d⊢
coercion-wf (cast-fun c⊢ d⊢) | hA′ , hA | hB , hB′ =
  wf⇒ hA hB , wf⇒ hA′ hB′
coercion-wf (cast-all c⊢) with coercion-wf c⊢
coercion-wf (cast-all c⊢) | hA , hB = wf∀ hA , wf∀ hB
coercion-wf (cast-inst hA hB okA c⊢) = wf∀ hA , hB
coercion-wf (cast-gen hA hB okB c⊢) = hA , wf∀ hB

------------------------------------------------------------------------
-- Raw source/target functions agree with typed endpoints
------------------------------------------------------------------------

coercion-src-tgtᵐ :
  ∀ {μ Γ c A B} →
  μ ∣ Γ ⊢ c ∶ A =⇒ B →
  src c ≡ A × tgt c ≡ B
coercion-src-tgtᵐ (cast-id hA) = refl , refl
coercion-src-tgtᵐ (cast-seal hA okα hα) = refl , refl
coercion-src-tgtᵐ (cast-unseal hA okα hα) = refl , refl
coercion-src-tgtᵐ (cast-seq c⊢ d⊢)
  with coercion-src-tgtᵐ c⊢ | coercion-src-tgtᵐ d⊢
coercion-src-tgtᵐ (cast-seq c⊢ d⊢) | src-c , tgt-c | src-d , tgt-d
  rewrite src-c | tgt-d = refl , refl
coercion-src-tgtᵐ (cast-tag hG gG okG) = refl , refl
coercion-src-tgtᵐ (cast-untag hH gH okH) = refl , refl
coercion-src-tgtᵐ (cast-fun c⊢ d⊢)
  with coercion-src-tgtᵐ c⊢ | coercion-src-tgtᵐ d⊢
coercion-src-tgtᵐ (cast-fun c⊢ d⊢) | src-c , tgt-c | src-d , tgt-d
  rewrite src-c | tgt-c | src-d | tgt-d = refl , refl
coercion-src-tgtᵐ (cast-all c⊢) with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-all c⊢) | src-c , tgt-c
  rewrite src-c | tgt-c = refl , refl
coercion-src-tgtᵐ (cast-inst {A = A} {B = B} hA hB okA c⊢)
  with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-inst {A = A} {B = B} hA hB okA c⊢)
  | src-c , tgt-c rewrite src-c | tgt-c =
  cong `∀ (close-openTyWithSeal A) , dropSeal-shiftˢ B
coercion-src-tgtᵐ (cast-gen {A = A} {B = B} hA hB okB c⊢)
  with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-gen {A = A} {B = B} hA hB okB c⊢)
  | src-c , tgt-c rewrite src-c | tgt-c =
  dropSeal-shiftˢ A , cong `∀ (close-openTyWithSeal B)
