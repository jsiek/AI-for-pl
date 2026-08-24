open import proof.LR-narrow.RevealStatements

module proof.LR-narrow.RevealStructural (ob : RevealObligations) where

-- File Charter:
--   * The structural reveal and conceal compatibility at a paired
--     semantic slot, by strong induction on the step index, producing
--     the paired and the one-sided statements together.
--   * The function case decomposes the revealed function's application
--     into the argument conceal, the application, and the result reveal,
--     composed under the argument and reveal frames.
--   * The blocked universal imprecisions are delegated to the
--     obligations record; see FUNDAMENTAL-PROPERTY-PLAN.md, Finding C.

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using
  (n≤1+n; ≤-trans; ≤-refl; <-wellFounded; m∸n≤m)
open import Data.Nat.Induction using () renaming (<-wellFounded to wf)
open import Induction.WellFounded using (Acc; acc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)
open import Data.Fin.Properties using (_≟_)

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; unseal; seal; _↦↑_; _↦↓_; `∀↑_; `∀↓_; id↑; id↓;
   rename↑; rename↓; replaceTy; 〖_,_↑_〗; makeConceal)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective; renameᵗ-injective; ty-all-injective)
import proof.Imprecision as PI
open import proof.TypeSafety.Preservation using
  (structural-reveal-typing; structural-conceal-typing)
open import proof.TypeInTermSubst using (toRename-wk-eq; renameᵗ-id)
open import proof.LR-narrow.TypeRenamingComposition using
  (Packed↑; Packed↓; pack↑; pack↓; apply↑; apply↓)
open import proof.LR-narrow.TermRenamingComposition using
  (reveal-pointwise; conceal-pointwise)
open import proof.LR-narrow.TypeRenamingComposition using
  (pack-↦↑; pack-↦↓; pack-∀↑; pack-∀↓)
import Data.Fin as Fin
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return)
open import proof.LR-narrow.StepExpansion using
  (related-pure-step-expand)
open import proof.LR-narrow.CastComposition using
  (computations-related-future-compose)
open import proof.LR-narrow.FramePhases
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames
open import proof.LR-narrow.RevealSteps
open import proof.LR-narrow.SlotLifting
open import proof.LR-narrow.RevealLifting
open import proof.LR-narrow.ArgumentFrame using
  (related-application-computation)
open import proof.LR-narrow.StarNoOccurrence using
  (star-no-occurrence; replaceTy-absent; renameᵗ-reflects-∉ᵗ)
import proof.LR-narrow.PreciseReveal
open module PreciseRevealModule = proof.LR-narrow.PreciseReveal ob
  using (precise-reveal; precise-conceal)
open import proof.LR-narrow.KeepStepExpansion using
  (related-imprecise-keep-step-expand)
open import proof.LR-narrow.BindStepExpansion using
  (paired-bind-step; related-paired-bind-step-expand)
open import proof.LR-narrow.UniversalReveal using
  (reveal-type-app-step-question; conceal-type-app-step-question;
   fresh-slot; liftPreciseBody-replace; liftImpreciseBody-replace;
   universals-head; post-bind-weaken;
   embed-precise-bind-body; embed-imprecise-bind-body;
   embed-body-lift-precise; embed-body-lift-imprecise)
open import proof.LR-narrow.ReplaceImprecision using
  (replace-⊑; replace-zero-open; open-shifted-body)
open import proof.LR-narrow.ImprecisionSize using
  (sizeᵖ; lift-center-size)
import proof.LR-narrow.RevealAtomic as RA
import proof.LR-narrow.ConcealAtomic as CA

open RevealObligations ob using
  (blocked-reveal; blocked-conceal;
   blocked-dyn-reveal; blocked-dyn-conceal)
open RA using
  (AtomicReveal; atomic-★; atomic-ι; atomic-X; atomic-ι★; atomic-X★;
   rename-base-injective; rename-star-injective; rename-variable-inversion)

------------------------------------------------------------------------
-- Renamings preserve atomicity
------------------------------------------------------------------------

open import proof.ImprecisionConsistency using
  (rename-⊑; rename-star-map-ext; fin-suc-injective; ext-injective)

------------------------------------------------------------------------
-- No bottom-typed values
------------------------------------------------------------------------

open import proof.TypeSafety.Progress using (no-bot-value)

no-precise-bottom-value : ∀ {Δᴾ Δᴵ Δᶜ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ (`∀ (＇ Fin.zero)) ⊑ Aᴵ}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ⊥
no-precise-bottom-value {W = W} related =
  no-bot-value (precise-value endpoints) Vᴾ⊢bot
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  precise-type-eq : preciseType endpoints ≡ `∀ (＇ Fin.zero)
  precise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (preciseEmbedded endpoints)

  Vᴾ⊢bot = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    precise-type-eq (precise-typed endpoints)

------------------------------------------------------------------------
-- Typed endpoints of revealed and concealed values
------------------------------------------------------------------------

revealed-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → Value (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
  → Value (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
  → TypedEndpoints W q
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
revealed-endpoints W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} p sourceᴾ sourceᴵ q
    targetᴾ targetᴵ related vᴵ vᴾ =
  typed-endpoints _ _ targetᴵ targetᴾ vᴵ vᴾ
    (⊢reveal (structural-reveal-typing Bᴵ (impreciseBound (atom s)))
      Vᴵ⊢Bᴵ)
    (⊢reveal (structural-reveal-typing Bᴾ (preciseBound (atom s)))
      Vᴾ⊢Bᴾ)
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  Vᴾ⊢Bᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective (toRenameᵗ-injective (preciseEmbedding (core W)))
      (trans (preciseEmbedded endpoints) (sym sourceᴾ)))
    (precise-typed endpoints)

  Vᴵ⊢Bᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W)))
      (trans (impreciseEmbedded endpoints) (sym sourceᴵ)))
    (imprecise-typed endpoints)

concealed-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → Value (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
  → Value (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
  → TypedEndpoints W p
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
concealed-endpoints W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} p sourceᴾ sourceᴵ q
    targetᴾ targetᴵ related vᴵ vᴾ =
  typed-endpoints _ _ sourceᴵ sourceᴾ vᴵ vᴾ
    (⊢conceal (structural-conceal-typing Bᴵ (impreciseBound (atom s)))
      Vᴵ⊢Cᴵ)
    (⊢conceal (structural-conceal-typing Bᴾ (preciseBound (atom s)))
      Vᴾ⊢Cᴾ)
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  Vᴾ⊢Cᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective (toRenameᵗ-injective (preciseEmbedding (core W)))
      (trans (preciseEmbedded endpoints) (sym targetᴾ)))
    (precise-typed endpoints)

  Vᴵ⊢Cᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W)))
      (trans (impreciseEmbedded endpoints) (sym targetᴵ)))
    (imprecise-typed endpoints)
open Composition revealFrame revealFrame using ()
  renaming (frame-computations-related to reveal-computations-related;
            PlugValues to RevealPlugValues)
open Composition concealFrame concealFrame using ()
  renaming (frame-computations-related to conceal-computations-related;
            PlugValues to ConcealPlugValues)


revealed-computations : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {k n : ℕ} (size≤ : sizeᵖ p ≤ n)
      (below : ∀ j → j ≤ k → RevealAtSized j n)
      {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → ComputationsRelated W (FutureValueRelation p) k Mᴵ Mᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      (Mᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
      (Mᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
revealed-computations W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    p sourceᴾ sourceᴵ {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} q targetᴾ targetᴵ
    {k = k} size≤ below {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
  reveal-computations-related
    {R = FutureValueRelation p} {S = FutureValueRelation q}
    (reveal-frm 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
    (reveal-frm 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
    k Mᴵ Mᴾ plug-values related
  where
  plug-values : RevealPlugValues W (FutureValueRelation p)
      (FutureValueRelation q) k
      (reveal-frm 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
      (reveal-frm 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
  plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = j} j≤k {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
      value-related =
    computations-related-future-compose W≼W′ q
      (ClosureProof.computations-related-reindex
        (liftCenterImprecision W≼W′ q) (liftCenterImprecision W≼W′ q)
        refl refl
        (sym (transported-reveal-eq χsᴵ Mᴵ (slotXᴵ s) (slotRᴵ s) Bᴵ
          (trans (termsᴵ (Mᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗))
            (trans (lifted-reveal-imprecise s W≼W′ Mᴵ Bᴵ)
              (cong (λ M → M ↑ _) (sym (termsᴵ Mᴵ))))) Uᴵ))
        (sym (transported-reveal-eq χsᴾ Mᴾ (slotXᴾ s) (slotRᴾ s) Bᴾ
          (trans (termsᴾ (Mᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗))
            (trans (lifted-reveal-precise s W≼W′ Mᴾ Bᴾ)
              (cong (λ M → M ↑ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
        (below j j≤k W′ (slot-future s W≼W′)
          (liftCenterImprecision W≼W′ p)
          (subst≡ (_≤ _) (sym (lift-center-size W≼W′ p)) size≤)
          (trans (embedPrecise-lift W≼W′ Bᴾ)
            (cong (liftCenterTy W≼W′) sourceᴾ))
          (trans (embedImprecise-lift W≼W′ Bᴵ)
            (cong (liftCenterTy W≼W′) sourceᴵ))
          (liftCenterImprecision W≼W′ q)
          (trans (cong (embedPrecise (core W′))
            (replace-precise-lift s W≼W′ Bᴾ))
            (trans (embedPrecise-lift W≼W′ _)
              (cong (liftCenterTy W≼W′) targetᴾ)))
          (trans (cong (embedImprecise (core W′))
            (replace-imprecise-lift s W≼W′ Bᴵ))
            (trans (embedImprecise-lift W≼W′ _)
              (cong (liftCenterTy W≼W′) targetᴵ)))
          value-related))

concealed-computations : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {k n : ℕ} (size≤ : sizeᵖ p ≤ n)
      (below : ∀ j → j ≤ k → ConcealAtSized j n)
      {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → ComputationsRelated W (FutureValueRelation q) k Mᴵ Mᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Mᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
      (Mᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
concealed-computations W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    p sourceᴾ sourceᴵ {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} q targetᴾ targetᴵ
    {k = k} size≤ below {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
  conceal-computations-related
    {R = FutureValueRelation q} {S = FutureValueRelation p}
    (conceal-frm (makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ))
    (conceal-frm (makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ))
    k Mᴵ Mᴾ plug-values related
  where
  plug-values : ConcealPlugValues W (FutureValueRelation q)
      (FutureValueRelation p) k
      (conceal-frm (makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ))
      (conceal-frm (makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ))
  plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = j} j≤k {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
      value-related =
    computations-related-future-compose W≼W′ p
      (ClosureProof.computations-related-reindex
        (liftCenterImprecision W≼W′ p) (liftCenterImprecision W≼W′ p)
        refl refl
        (sym (transported-conceal-eq χsᴵ Mᴵ (slotXᴵ s) (slotRᴵ s) Bᴵ
          (trans (termsᴵ (Mᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ))
            (trans (lifted-conceal-imprecise s W≼W′ Mᴵ Bᴵ)
              (cong (λ M → M ↓ _) (sym (termsᴵ Mᴵ))))) Uᴵ))
        (sym (transported-conceal-eq χsᴾ Mᴾ (slotXᴾ s) (slotRᴾ s) Bᴾ
          (trans (termsᴾ (Mᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ))
            (trans (lifted-conceal-precise s W≼W′ Mᴾ Bᴾ)
              (cong (λ M → M ↓ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
        (below j j≤k W′ (slot-future s W≼W′)
          (liftCenterImprecision W≼W′ p)
          (subst≡ (_≤ _) (sym (lift-center-size W≼W′ p)) size≤)
          (trans (embedPrecise-lift W≼W′ Bᴾ)
            (cong (liftCenterTy W≼W′) sourceᴾ))
          (trans (embedImprecise-lift W≼W′ Bᴵ)
            (cong (liftCenterTy W≼W′) sourceᴵ))
          (liftCenterImprecision W≼W′ q)
          (trans (cong (embedPrecise (core W′))
            (replace-precise-lift s W≼W′ Bᴾ))
            (trans (embedPrecise-lift W≼W′ _)
              (cong (liftCenterTy W≼W′) targetᴾ)))
          (trans (cong (embedImprecise (core W′))
            (replace-imprecise-lift s W≼W′ Bᴵ))
            (trans (embedImprecise-lift W≼W′ _)
              (cong (liftCenterTy W≼W′) targetᴵ)))
          value-related))

------------------------------------------------------------------------
-- The function case
------------------------------------------------------------------------

-- One head of `FunctionsRelated` for a revealed function value: the
-- revealed application redistributes into a concealed argument, the
-- application, and a revealed result.

reveal-function-head : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Aᴾ₀ Bᴾ₀ : Ty Δᴾ} {Aᴵ₀ Bᴵ₀ : Ty Δᴵ}
    {Pᴾ Pᴵ Qᴾ Qᴵ : Ty Δᶜ}
    (p₁ : impEnv (core W) I.⊢ Pᴾ ⊑ Pᴵ)
    (p₂ : impEnv (core W) I.⊢ Qᴾ ⊑ Qᴵ)
  → (sourceᴾ₁ : embedPrecise (core W) Aᴾ₀ ≡ Pᴾ)
  → (sourceᴵ₁ : embedImprecise (core W) Aᴵ₀ ≡ Pᴵ)
  → (sourceᴾ₂ : embedPrecise (core W) Bᴾ₀ ≡ Qᴾ)
  → (sourceᴵ₂ : embedImprecise (core W) Bᴵ₀ ≡ Qᴵ)
  → ∀ {Cᴾ Cᴵ Dᴾ Dᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      (q₂ : impEnv (core W) I.⊢ Dᴾ ⊑ Dᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Aᴾ₀) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Aᴵ₀) ≡ Cᴵ
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ₀) ≡ Dᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ₀) ≡ Dᴵ
  → ∀ {k : ℕ}
      (revealBelow : ∀ j → j ≤ k → RevealAt j)
      (concealAt : ConcealAt k)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
  → ValueImprecision W′ (liftCenterImprecision W≼W′ q₁) (suc k) Uᴵ Uᴾ
  → ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc k)
      (liftImpreciseTerm W≼W′
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗) · Uᴵ)
      (liftPreciseTerm W≼W′
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗) · Uᴾ)
reveal-function-head W s {Aᴾ₀ = Aᴾ₀} {Bᴾ₀ = Bᴾ₀}
    {Aᴵ₀ = Aᴵ₀} {Bᴵ₀ = Bᴵ₀} {Pᴾ = Pᴾ} {Pᴵ = Pᴵ} {Qᴾ = Qᴾ} {Qᴵ = Qᴵ}
    p₁ p₂ sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Dᴾ = Dᴾ} {Dᴵ = Dᴵ} q₁ q₂
    targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    {k = k} revealBelow concealAt {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
    W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
  ClosureProof.computations-related-reindex
    (liftCenterImprecision W≼W′ q₂) (liftCenterImprecision W≼W′ q₂)
    refl refl (sym imprecise-redex-eq) (sym precise-redex-eq)
    expanded
  where
  s′ = slot-future s W≼W′
  Xᴾ′ = slotXᴾ s′
  Xᴵ′ = slotXᴵ s′
  Rᴾ′ = slotRᴾ s′
  Rᴵ′ = slotRᴵ s′

  Aᴾ′ = liftPreciseTy W≼W′ Aᴾ₀
  Bᴾ′ = liftPreciseTy W≼W′ Bᴾ₀
  Aᴵ′ = liftImpreciseTy W≼W′ Aᴵ₀
  Bᴵ′ = liftImpreciseTy W≼W′ Bᴵ₀

  cᴾ = makeConceal Xᴾ′ Rᴾ′ Aᴾ′
  dᴾ = 〖 Xᴾ′ , Rᴾ′ ↑ Bᴾ′ 〗
  cᴵ = makeConceal Xᴵ′ Rᴵ′ Aᴵ′
  dᴵ = 〖 Xᴵ′ , Rᴵ′ ↑ Bᴵ′ 〗

  Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
  Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

  -- The lifted revealed value is the revealed lifted value.

  precise-redex-eq :
      liftPreciseTerm W≼W′ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
        · Uᴾ
      ≡ (Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ
  precise-redex-eq
      rewrite lifted-reveal-precise s W≼W′ Vᴾ (Aᴾ₀ ⇒ Bᴾ₀)
            | liftPreciseTy-arrow W≼W′ Aᴾ₀ Bᴾ₀ = refl

  imprecise-redex-eq :
      liftImpreciseTerm W≼W′
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗) · Uᴵ
      ≡ (Vᴵ′ ↑ (cᴵ ↦↑ dᴵ)) · Uᴵ
  imprecise-redex-eq
      rewrite lifted-reveal-imprecise s W≼W′ Vᴵ (Aᴵ₀ ⇒ Bᴵ₀)
            | liftImpreciseTy-arrow W≼W′ Aᴵ₀ Bᴵ₀ = refl

  source-endpoints =
    ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑⇒ p₁ p₂} {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
      function-related
  argument-endpoints =
    ClosureProof.value-imprecision-endpoints argument-related

  -- The lifted source function relation, with an explicit arrow.

  lifted-function : ValueImprecision W′
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
        (liftCenterImprecision W≼W′ p₂)) k Vᴵ′ Vᴾ′
  lifted-function = ClosureProof.value-imprecision-reindex
    (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
      (liftCenterImprecision W≼W′ p₂))
    (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p₁ p₂))
    (sym (liftCenterTy-arrow W≼W′ Pᴾ Qᴾ))
    (sym (liftCenterTy-arrow W≼W′ Pᴵ Qᴵ))
    (ClosureProof.value-imprecision-future W≼W′
      (value-imprecision-downward-to (n≤1+n k) function-related))

  -- The concealed argument.

  concealed : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₁)) k
      (Uᴵ ↓ cᴵ) (Uᴾ ↓ cᴾ)
  concealed = concealAt W′ s′
    (liftCenterImprecision W≼W′ p₁) ≤-refl
    (trans (embedPrecise-lift W≼W′ Aᴾ₀)
      (cong (liftCenterTy W≼W′) sourceᴾ₁))
    (trans (embedImprecise-lift W≼W′ Aᴵ₀)
      (cong (liftCenterTy W≼W′) sourceᴵ₁))
    (liftCenterImprecision W≼W′ q₁)
    (trans (cong (embedPrecise (core W′))
      (replace-precise-lift s W≼W′ Aᴾ₀))
      (trans (embedPrecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴾ₁)))
    (trans (cong (embedImprecise (core W′))
      (replace-imprecise-lift s W≼W′ Aᴵ₀))
      (trans (embedImprecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴵ₁)))
    (value-imprecision-downward-to (n≤1+n k) argument-related)

  applied : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) k
      (Vᴵ′ · (Uᴵ ↓ cᴵ)) (Vᴾ′ · (Uᴾ ↓ cᴾ))
  applied = related-application-computation lifted-function concealed

  contracted : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) k
      ((Vᴵ′ · (Uᴵ ↓ cᴵ)) ↑ dᴵ) ((Vᴾ′ · (Uᴾ ↓ cᴾ)) ↑ dᴾ)
  contracted = revealed-computations W′ s′
    (liftCenterImprecision W≼W′ p₂)
    (trans (embedPrecise-lift W≼W′ Bᴾ₀)
      (cong (liftCenterTy W≼W′) sourceᴾ₂))
    (trans (embedImprecise-lift W≼W′ Bᴵ₀)
      (cong (liftCenterTy W≼W′) sourceᴵ₂))
    (liftCenterImprecision W≼W′ q₂)
    (trans (cong (embedPrecise (core W′))
      (replace-precise-lift s W≼W′ Bᴾ₀))
      (trans (embedPrecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴾ₂)))
    (trans (cong (embedImprecise (core W′))
      (replace-imprecise-lift s W≼W′ Bᴵ₀))
      (trans (embedImprecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴵ₂)))
    ≤-refl (λ j j≤k′ → revealBelow j j≤k′) applied

  expanded : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc k)
      ((Vᴵ′ ↑ (cᴵ ↦↑ dᴵ)) · Uᴵ) ((Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ)
  expanded
      with reveal-fun-app-step-question
             {Σ = impreciseStore (core W′)} cᴵ dᴵ
             (imprecise-value source-endpoints-lifted)
             (imprecise-value argument-endpoints)
         | reveal-fun-app-step-question
             {Σ = preciseStore (core W′)} cᴾ dᴾ
             (precise-value source-endpoints-lifted)
             (precise-value argument-endpoints)
    where
    source-endpoints-lifted =
      ClosureProof.value-imprecision-endpoints lifted-function
  expanded | vVᴵ , vUᴵ , step-eqᴵ | vVᴾ , vUᴾ , step-eqᴾ =
    related-pure-step-expand (λ ()) (λ ())
      (reveal-fun-app-value-none cᴵ dᴵ)
      (reveal-fun-app-value-none cᴾ dᴾ)
      (β-reveal-⇒ vVᴵ vUᴵ) (β-reveal-⇒ vVᴾ vUᴾ)
      step-eqᴵ step-eqᴾ contracted

reveal-function : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Aᴾ₀ Bᴾ₀ : Ty Δᴾ} {Aᴵ₀ Bᴵ₀ : Ty Δᴵ}
    {Pᴾ Pᴵ Qᴾ Qᴵ : Ty Δᶜ}
    (p₁ : impEnv (core W) I.⊢ Pᴾ ⊑ Pᴵ)
    (p₂ : impEnv (core W) I.⊢ Qᴾ ⊑ Qᴵ)
  → (sourceᴾ₁ : embedPrecise (core W) Aᴾ₀ ≡ Pᴾ)
  → (sourceᴵ₁ : embedImprecise (core W) Aᴵ₀ ≡ Pᴵ)
  → (sourceᴾ₂ : embedPrecise (core W) Bᴾ₀ ≡ Qᴾ)
  → (sourceᴵ₂ : embedImprecise (core W) Bᴵ₀ ≡ Qᴵ)
  → ∀ {Cᴾ Cᴵ Dᴾ Dᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      (q₂ : impEnv (core W) I.⊢ Dᴾ ⊑ Dᴵ)
  → (targetᴾ₁ :
      embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Aᴾ₀) ≡ Cᴾ)
  → (targetᴵ₁ :
      embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Aᴵ₀) ≡ Cᴵ)
  → (targetᴾ₂ :
      embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ₀) ≡ Dᴾ)
  → (targetᴵ₂ :
      embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ₀) ≡ Dᴵ)
  → ∀ {k : ℕ} (outer : OuterBelow k)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation (I.⇒⊑⇒ q₁ q₂)) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
reveal-function W s {Aᴾ₀ = Aᴾ₀} {Bᴾ₀ = Bᴾ₀} {Aᴵ₀ = Aᴵ₀} {Bᴵ₀ = Bᴵ₀}
    p₁ p₂ sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂
    q₁ q₂ targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    {k = k} outer {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  related-values-return
    (imprecise-value endpoints ↑ fun) (precise-value endpoints ↑ fun)
    at-every-index
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  reveal-endpoints : ∀ (j : ℕ)
    → TypedEndpoints W (I.⇒⊑⇒ q₁ q₂)
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗)
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
  reveal-endpoints j = revealed-endpoints W s (I.⇒⊑⇒ p₁ p₂)
    (cong₂ _⇒_ sourceᴾ₁ sourceᴾ₂) (cong₂ _⇒_ sourceᴵ₁ sourceᴵ₂)
    (I.⇒⊑⇒ q₁ q₂) (cong₂ _⇒_ targetᴾ₁ targetᴾ₂)
    (cong₂ _⇒_ targetᴵ₁ targetᴵ₂) related
    (imprecise-value endpoints ↑ fun) (precise-value endpoints ↑ fun)

  head-at : ∀ (j : ℕ) → suc j ≤ k
    → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) (suc j) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ (liftCenterImprecision W≼W′ q₁) (suc j) Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc j)
        (liftImpreciseTerm W≼W′
          (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗) · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗) · Uᴾ)
  head-at j sj≤k source-at = reveal-function-head W s p₁ p₂
    sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂ q₁ q₂
    targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    (λ i i≤j → full-revealAt (outer i (≤-trans (s≤s i≤j) sj≤k)))
    (full-concealAt (outer j sj≤k)) source-at

  functions-related : ∀ (j : ℕ) → suc j ≤ k
    → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) (suc j) Vᴵ Vᴾ
    → FunctionsRelated W q₁ q₂ (suc j)
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗)
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
  functions-related zero sj≤k source-at =
    head-at zero sj≤k source-at , tt
  functions-related (suc j) sj≤k source-at =
    head-at (suc j) sj≤k source-at ,
    functions-related j (≤-trans (n≤1+n (suc j)) sj≤k)
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ p₁ p₂} {j = suc j} {k = suc (suc j)}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n (suc j)) source-at)

  at-every-index : ∀ (j : ℕ) → j ≤ k
    → FutureValueRelation (I.⇒⊑⇒ q₁ q₂) W future-refl j
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗)
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
  at-every-index zero j≤k = reveal-endpoints zero
  at-every-index (suc j) sj≤k =
    reveal-endpoints (suc j) ,
    functions-related j sj≤k
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ p₁ p₂} {j = suc j} {k = k}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} sj≤k related)

------------------------------------------------------------------------
-- The conceal function case
------------------------------------------------------------------------

conceal-function-head : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Aᴾ₀ Bᴾ₀ : Ty Δᴾ} {Aᴵ₀ Bᴵ₀ : Ty Δᴵ}
    {Pᴾ Pᴵ Qᴾ Qᴵ : Ty Δᶜ}
    (p₁ : impEnv (core W) I.⊢ Pᴾ ⊑ Pᴵ)
    (p₂ : impEnv (core W) I.⊢ Qᴾ ⊑ Qᴵ)
  → (sourceᴾ₁ : embedPrecise (core W) Aᴾ₀ ≡ Pᴾ)
  → (sourceᴵ₁ : embedImprecise (core W) Aᴵ₀ ≡ Pᴵ)
  → (sourceᴾ₂ : embedPrecise (core W) Bᴾ₀ ≡ Qᴾ)
  → (sourceᴵ₂ : embedImprecise (core W) Bᴵ₀ ≡ Qᴵ)
  → ∀ {Cᴾ Cᴵ Dᴾ Dᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      (q₂ : impEnv (core W) I.⊢ Dᴾ ⊑ Dᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Aᴾ₀) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Aᴵ₀) ≡ Cᴵ
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ₀) ≡ Dᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ₀) ≡ Dᴵ
  → ∀ {k : ℕ}
      (revealAt : RevealAt k)
      (concealBelow : ∀ j → j ≤ k → ConcealAt j)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p₁) (suc k) Uᴵ Uᴾ
  → ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc k)
      (liftImpreciseTerm W≼W′
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀)) · Uᴵ)
      (liftPreciseTerm W≼W′
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀)) · Uᴾ)
conceal-function-head W s {Aᴾ₀ = Aᴾ₀} {Bᴾ₀ = Bᴾ₀}
    {Aᴵ₀ = Aᴵ₀} {Bᴵ₀ = Bᴵ₀} {Pᴾ = Pᴾ} {Pᴵ = Pᴵ} {Qᴾ = Qᴾ} {Qᴵ = Qᴵ}
    p₁ p₂ sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Dᴾ = Dᴾ} {Dᴵ = Dᴵ} q₁ q₂
    targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    {k = k} revealAt concealBelow {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
    W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
  ClosureProof.computations-related-reindex
    (liftCenterImprecision W≼W′ p₂) (liftCenterImprecision W≼W′ p₂)
    refl refl (sym imprecise-redex-eq) (sym precise-redex-eq)
    expanded
  where
  s′ = slot-future s W≼W′
  Xᴾ′ = slotXᴾ s′
  Xᴵ′ = slotXᴵ s′
  Rᴾ′ = slotRᴾ s′
  Rᴵ′ = slotRᴵ s′

  Aᴾ′ = liftPreciseTy W≼W′ Aᴾ₀
  Bᴾ′ = liftPreciseTy W≼W′ Bᴾ₀
  Aᴵ′ = liftImpreciseTy W≼W′ Aᴵ₀
  Bᴵ′ = liftImpreciseTy W≼W′ Bᴵ₀

  cᴾ = 〖 Xᴾ′ , Rᴾ′ ↑ Aᴾ′ 〗
  dᴾ = makeConceal Xᴾ′ Rᴾ′ Bᴾ′
  cᴵ = 〖 Xᴵ′ , Rᴵ′ ↑ Aᴵ′ 〗
  dᴵ = makeConceal Xᴵ′ Rᴵ′ Bᴵ′

  Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
  Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

  precise-redex-eq :
      liftPreciseTerm W≼W′
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀)) · Uᴾ
      ≡ (Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ
  precise-redex-eq
      rewrite lifted-conceal-precise s W≼W′ Vᴾ (Aᴾ₀ ⇒ Bᴾ₀)
            | liftPreciseTy-arrow W≼W′ Aᴾ₀ Bᴾ₀ = refl

  imprecise-redex-eq :
      liftImpreciseTerm W≼W′
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀)) · Uᴵ
      ≡ (Vᴵ′ ↓ (cᴵ ↦↓ dᴵ)) · Uᴵ
  imprecise-redex-eq
      rewrite lifted-conceal-imprecise s W≼W′ Vᴵ (Aᴵ₀ ⇒ Bᴵ₀)
            | liftImpreciseTy-arrow W≼W′ Aᴵ₀ Bᴵ₀ = refl

  argument-endpoints =
    ClosureProof.value-imprecision-endpoints argument-related

  lifted-function : ValueImprecision W′
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
        (liftCenterImprecision W≼W′ q₂)) k Vᴵ′ Vᴾ′
  lifted-function = ClosureProof.value-imprecision-reindex
    (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
      (liftCenterImprecision W≼W′ q₂))
    (liftCenterImprecision W≼W′ (I.⇒⊑⇒ q₁ q₂))
    (sym (liftCenterTy-arrow W≼W′ Cᴾ Dᴾ))
    (sym (liftCenterTy-arrow W≼W′ Cᴵ Dᴵ))
    (ClosureProof.value-imprecision-future W≼W′
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = k} {k = suc k}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n k) function-related))

  revealed : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₁)) k
      (Uᴵ ↑ cᴵ) (Uᴾ ↑ cᴾ)
  revealed = revealAt W′ s′
    (liftCenterImprecision W≼W′ p₁) ≤-refl
    (trans (embedPrecise-lift W≼W′ Aᴾ₀)
      (cong (liftCenterTy W≼W′) sourceᴾ₁))
    (trans (embedImprecise-lift W≼W′ Aᴵ₀)
      (cong (liftCenterTy W≼W′) sourceᴵ₁))
    (liftCenterImprecision W≼W′ q₁)
    (trans (cong (embedPrecise (core W′))
      (replace-precise-lift s W≼W′ Aᴾ₀))
      (trans (embedPrecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴾ₁)))
    (trans (cong (embedImprecise (core W′))
      (replace-imprecise-lift s W≼W′ Aᴵ₀))
      (trans (embedImprecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴵ₁)))
    (value-imprecision-downward-to
      {W = W′} {p = liftCenterImprecision W≼W′ p₁}
      {j = k} {k = suc k} {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
      (n≤1+n k) argument-related)

  applied : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) k
      (Vᴵ′ · (Uᴵ ↑ cᴵ)) (Vᴾ′ · (Uᴾ ↑ cᴾ))
  applied = related-application-computation lifted-function revealed

  contracted : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) k
      ((Vᴵ′ · (Uᴵ ↑ cᴵ)) ↓ dᴵ) ((Vᴾ′ · (Uᴾ ↑ cᴾ)) ↓ dᴾ)
  contracted = concealed-computations W′ s′
    (liftCenterImprecision W≼W′ p₂)
    (trans (embedPrecise-lift W≼W′ Bᴾ₀)
      (cong (liftCenterTy W≼W′) sourceᴾ₂))
    (trans (embedImprecise-lift W≼W′ Bᴵ₀)
      (cong (liftCenterTy W≼W′) sourceᴵ₂))
    (liftCenterImprecision W≼W′ q₂)
    (trans (cong (embedPrecise (core W′))
      (replace-precise-lift s W≼W′ Bᴾ₀))
      (trans (embedPrecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴾ₂)))
    (trans (cong (embedImprecise (core W′))
      (replace-imprecise-lift s W≼W′ Bᴵ₀))
      (trans (embedImprecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴵ₂)))
    ≤-refl (λ j j≤k′ → concealBelow j j≤k′) applied

  expanded : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc k)
      ((Vᴵ′ ↓ (cᴵ ↦↓ dᴵ)) · Uᴵ) ((Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ)
  expanded
      with conceal-fun-app-step-question
             {Σ = impreciseStore (core W′)} cᴵ dᴵ
             (imprecise-value function-endpoints)
             (imprecise-value argument-endpoints)
         | conceal-fun-app-step-question
             {Σ = preciseStore (core W′)} cᴾ dᴾ
             (precise-value function-endpoints)
             (precise-value argument-endpoints)
    where
    function-endpoints =
      ClosureProof.value-imprecision-endpoints lifted-function
  expanded | vVᴵ , vUᴵ , step-eqᴵ | vVᴾ , vUᴾ , step-eqᴾ =
    related-pure-step-expand (λ ()) (λ ())
      (conceal-fun-app-value-none cᴵ dᴵ)
      (conceal-fun-app-value-none cᴾ dᴾ)
      (β-conceal-⇒ vVᴵ vUᴵ) (β-conceal-⇒ vVᴾ vUᴾ)
      step-eqᴵ step-eqᴾ contracted

conceal-function : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Aᴾ₀ Bᴾ₀ : Ty Δᴾ} {Aᴵ₀ Bᴵ₀ : Ty Δᴵ}
    {Pᴾ Pᴵ Qᴾ Qᴵ : Ty Δᶜ}
    (p₁ : impEnv (core W) I.⊢ Pᴾ ⊑ Pᴵ)
    (p₂ : impEnv (core W) I.⊢ Qᴾ ⊑ Qᴵ)
  → (sourceᴾ₁ : embedPrecise (core W) Aᴾ₀ ≡ Pᴾ)
  → (sourceᴵ₁ : embedImprecise (core W) Aᴵ₀ ≡ Pᴵ)
  → (sourceᴾ₂ : embedPrecise (core W) Bᴾ₀ ≡ Qᴾ)
  → (sourceᴵ₂ : embedImprecise (core W) Bᴵ₀ ≡ Qᴵ)
  → ∀ {Cᴾ Cᴵ Dᴾ Dᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      (q₂ : impEnv (core W) I.⊢ Dᴾ ⊑ Dᴵ)
  → (targetᴾ₁ :
      embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Aᴾ₀) ≡ Cᴾ)
  → (targetᴵ₁ :
      embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Aᴵ₀) ≡ Cᴵ)
  → (targetᴾ₂ :
      embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ₀) ≡ Dᴾ)
  → (targetᴵ₂ :
      embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ₀) ≡ Dᴵ)
  → ∀ {k : ℕ} (outer : OuterBelow k)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation (I.⇒⊑⇒ p₁ p₂)) k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀))
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀))
conceal-function W s {Aᴾ₀ = Aᴾ₀} {Bᴾ₀ = Bᴾ₀} {Aᴵ₀ = Aᴵ₀} {Bᴵ₀ = Bᴵ₀}
    p₁ p₂ sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂
    q₁ q₂ targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    {k = k} outer {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  related-values-return
    (imprecise-value endpoints ↓ fun) (precise-value endpoints ↓ fun)
    at-every-index
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  conceal-endpoints : ∀ (j : ℕ)
    → TypedEndpoints W (I.⇒⊑⇒ p₁ p₂)
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀))
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀))
  conceal-endpoints j = concealed-endpoints W s (I.⇒⊑⇒ p₁ p₂)
    (cong₂ _⇒_ sourceᴾ₁ sourceᴾ₂) (cong₂ _⇒_ sourceᴵ₁ sourceᴵ₂)
    (I.⇒⊑⇒ q₁ q₂) (cong₂ _⇒_ targetᴾ₁ targetᴾ₂)
    (cong₂ _⇒_ targetᴵ₁ targetᴵ₂) related
    (imprecise-value endpoints ↓ fun) (precise-value endpoints ↓ fun)

  head-at : ∀ (j : ℕ) → suc j ≤ k
    → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc j) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ (liftCenterImprecision W≼W′ p₁) (suc j) Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc j)
        (liftImpreciseTerm W≼W′
          (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀)) · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀)) · Uᴾ)
  head-at j sj≤k source-at =
    conceal-function-head W s p₁ p₂
      sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂ q₁ q₂
      targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
      (full-revealAt (outer j sj≤k))
      (λ i i≤j → full-concealAt (outer i (≤-trans (s≤s i≤j) sj≤k)))
      source-at

  functions-related : ∀ (j : ℕ) → suc j ≤ k
    → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc j) Vᴵ Vᴾ
    → FunctionsRelated W p₁ p₂ (suc j)
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀))
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀))
  functions-related zero sj≤k source-at =
    head-at zero sj≤k source-at , tt
  functions-related (suc j) sj≤k source-at =
    head-at (suc j) sj≤k source-at ,
    functions-related j (≤-trans (n≤1+n (suc j)) sj≤k)
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = suc j} {k = suc (suc j)}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n (suc j)) source-at)

  at-every-index : ∀ (j : ℕ) → j ≤ k
    → FutureValueRelation (I.⇒⊑⇒ p₁ p₂) W future-refl j
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀))
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀))
  at-every-index zero j≤k = conceal-endpoints zero
  at-every-index (suc j) sj≤k =
    conceal-endpoints (suc j) ,
    functions-related j sj≤k
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = suc j} {k = k}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} sj≤k related)

------------------------------------------------------------------------
-- The paired universal case
------------------------------------------------------------------------

-- The residual of a revealed type application: the source universal is
-- instantiated at the freshly allocated paired name, and the result is
-- revealed twice — at the lifted old slot inside the body, then at the
-- fresh slot.

reveal-universal-inner : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {B₀ᴵ : Ty (suc Δᴵ)} {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    (p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Aᴾ)
  → (sourceᴵ : embedImprecise (core W) (`∀ B₀ᴵ) ≡ `∀ Aᴵ)
  → ∀ {k : ℕ} (below : OuterBelow (suc k))
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ p) (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Sᴾ : Ty Δᴾ′) (Sᴵ : Ty Δᴵ′) (r : Sᴾ ⊑ᵂ⟨ core W′ ⟩ Sᴵ)
      (t : liftPreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
            [ Sᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩
          liftImpreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
            [ Sᴵ ]ᵗ)
  → ComputationsRelated (pairedBindWorld W′ Sᴾ Sᴵ r)
      (FutureValueRelation
        (liftCenterImprecision (paired-bind-step W′ r) t)) k
      ((⇑ᵗᵐ (liftImpreciseTerm W≼W′ Vᴵ)
          ⦂∀ renameᵗ (extᵗ Fin.suc) (liftImpreciseBody W≼W′ B₀ᴵ)
            [ ＇ Fin.zero ])
        ↑ 〖 Fin.suc (slotXᴵ (slot-future s W≼W′)) ,
            ⇑ᵗ (slotRᴵ (slot-future s W≼W′))
            ↑ liftImpreciseBody W≼W′ B₀ᴵ 〗
        ↑ 〖 Fin.zero , ⇑ᵗ Sᴵ
          ↑ replaceTy (Fin.suc (slotXᴵ (slot-future s W≼W′)))
              (⇑ᵗ (slotRᴵ (slot-future s W≼W′)))
              (liftImpreciseBody W≼W′ B₀ᴵ) 〗)
      ((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ B₀ᴾ)
            [ ＇ Fin.zero ])
        ↑ 〖 Fin.suc (slotXᴾ (slot-future s W≼W′)) ,
            ⇑ᵗ (slotRᴾ (slot-future s W≼W′))
            ↑ liftPreciseBody W≼W′ B₀ᴾ 〗
        ↑ 〖 Fin.zero , ⇑ᵗ Sᴾ
          ↑ replaceTy (Fin.suc (slotXᴾ (slot-future s W≼W′)))
              (⇑ᵗ (slotRᴾ (slot-future s W≼W′)))
              (liftPreciseBody W≼W′ B₀ᴾ) 〗)
reveal-universal-inner W s p sourceᴾ sourceᴵ {k = zero} below
    related W′ W≼W′ Sᴾ Sᴵ r t =
  ClosureProof.computations-related-zero
reveal-universal-inner W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p sourceᴾ sourceᴵ {k = suc m} below
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related W′ W≼W′ Sᴾ Sᴵ r t
    with proj₂ related
reveal-universal-inner W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p sourceᴾ sourceᴵ {k = suc m} below
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related W′ W≼W′ Sᴾ Sᴵ r t
    | Bᴾ* , Bᴵ* , embP , embI , chain
    with ty-all-injective
           (renameᵗ-injective
             (toRenameᵗ-injective (preciseEmbedding (core W)))
             (trans embP (sym sourceᴾ)))
       | ty-all-injective
           (renameᵗ-injective
             (toRenameᵗ-injective (impreciseEmbedding (core W)))
             (trans embI (sym sourceᴵ)))
reveal-universal-inner W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p sourceᴾ sourceᴵ {k = suc m} below
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related W′ W≼W′ Sᴾ Sᴵ r t
    | .B₀ᴾ , .B₀ᴵ , embP , embI , chain
    | refl | refl = revealed₂
  where
  Wb = pairedBindWorld W′ Sᴾ Sᴵ r

  W≼Wb : Future W Wb
  W≼Wb = future-paired W≼W′ r

  s′ = slot-future s W≼W′
  s₁ = slot-future s′ (paired-bind-step W′ r)
  s₂ = fresh-slot W′ Sᴾ Sᴵ r
  Xᴾ′ = slotXᴾ s′
  Xᴵ′ = slotXᴵ s′
  Rᴾ′ = slotRᴾ s′
  Rᴵ′ = slotRᴵ s′
  B₀ᴾ′ = liftPreciseBody W≼W′ B₀ᴾ
  B₀ᴵ′ = liftImpreciseBody W≼W′ B₀ᴵ

  p′ : I.extᵐ (impEnv (core W′)) I.⊢
      liftCenterBody W≼W′ Aᴾ ⊑ liftCenterBody W≼W′ Aᴵ
  p′ = liftCenterBodyImprecision W≼W′ p

  Aᴾ-eq : Aᴾ
      ≡ renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W)))) B₀ᴾ
  Aᴾ-eq = ty-all-injective (sym sourceᴾ)

  Aᴵ-eq : Aᴵ
      ≡ renameᵗ (extᵗ (toRenameᵗ (impreciseEmbedding (core W)))) B₀ᴵ
  Aᴵ-eq = ty-all-injective (sym sourceᴵ)

  embed-eq-P : embedPrecise (core Wb) B₀ᴾ′ ≡ liftCenterBody W≼W′ Aᴾ
  embed-eq-P = trans (embed-precise-bind-body (core W′) Sᴾ Sᴵ B₀ᴾ′)
    (trans (embed-body-lift-precise W≼W′ B₀ᴾ)
      (cong (liftCenterBody W≼W′) (sym Aᴾ-eq)))

  embed-eq-I : embedImprecise (core Wb) B₀ᴵ′ ≡ liftCenterBody W≼W′ Aᴵ
  embed-eq-I = trans (embed-imprecise-bind-body (core W′) Sᴾ Sᴵ B₀ᴵ′)
    (trans (embed-body-lift-imprecise W≼W′ B₀ᴵ)
      (cong (liftCenterBody W≼W′) (sym Aᴵ-eq)))

  t₀ : impEnv (core Wb) I.⊢
      embedPrecise (core Wb) B₀ᴾ′ ⊑ embedImprecise (core Wb) B₀ᴵ′
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑ embedImprecise (core Wb) B₀ᴵ′)
    (sym embed-eq-P)
    (subst≡
      (λ R → impEnv (core Wb) I.⊢ liftCenterBody W≼W′ Aᴾ ⊑ R)
      (sym embed-eq-I) p′)

  open-P : renameᵗ (extᵗ Fin.suc) B₀ᴾ′ [ ＇ Fin.zero ]ᵗ ≡ B₀ᴾ′
  open-P = open-shifted-body B₀ᴾ′

  open-I : renameᵗ (extᵗ Fin.suc) B₀ᴵ′ [ ＇ Fin.zero ]ᵗ ≡ B₀ᴵ′
  open-I = open-shifted-body B₀ᴵ′

  s₀ : renameᵗ (extᵗ Fin.suc) B₀ᴾ′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ renameᵗ (extᵗ Fin.suc) B₀ᴵ′ [ ＇ Fin.zero ]ᵗ
  s₀ = subst≡
    (λ L → L ⊑ᵂ⟨ core Wb ⟩
      renameᵗ (extᵗ Fin.suc) B₀ᴵ′ [ ＇ Fin.zero ]ᵗ)
    (sym open-P)
    (subst≡ (λ R → B₀ᴾ′ ⊑ᵂ⟨ core Wb ⟩ R) (sym open-I) t₀)

  r₀ : (＇ Fin.zero) ⊑ᵂ⟨ core Wb ⟩ (＇ Fin.zero)
  r₀ = I.X⊑X

  core-related : ComputationsRelated Wb
      (PostBindValueRelation
        (future-paired (future-refl {W = Wb}) r₀) s₀) (suc m)
      (liftImpreciseTerm W≼Wb Vᴵ
        ⦂∀ liftImpreciseBody W≼Wb B₀ᴵ [ ＇ Fin.zero ])
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ liftPreciseBody W≼Wb B₀ᴾ [ ＇ Fin.zero ])
  core-related = universals-head {W = W} {p = p} {Bᴾ = B₀ᴾ}
    {Bᴵ = B₀ᴵ} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = suc (suc m)}
    m (s≤s (n≤1+n m)) chain
    Wb W≼Wb (＇ Fin.zero) (＇ Fin.zero) r₀ s₀

  weakened : ComputationsRelated Wb (FutureValueRelation s₀) (suc m)
      (liftImpreciseTerm W≼Wb Vᴵ
        ⦂∀ liftImpreciseBody W≼Wb B₀ᴵ [ ＇ Fin.zero ])
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ liftPreciseBody W≼Wb B₀ᴾ [ ＇ Fin.zero ])
  weakened = post-bind-weaken
    (future-paired (future-refl {W = Wb}) r₀) s₀ core-related

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀) (suc m)
      (liftImpreciseTerm W≼Wb Vᴵ
        ⦂∀ liftImpreciseBody W≼Wb B₀ᴵ [ ＇ Fin.zero ])
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ liftPreciseBody W≼Wb B₀ᴾ [ ＇ Fin.zero ])
  reindexed = ClosureProof.computations-related-reindex s₀ t₀
    (cong (embedPrecise (core Wb)) open-P)
    (cong (embedImprecise (core Wb)) open-I)
    refl refl weakened

  t₁ : impEnv (core Wb) I.⊢
      replaceTy (center s₁) (embedPrecise (core Wb) (slotRᴾ s₁))
        (embedPrecise (core Wb) B₀ᴾ′)
      ⊑ replaceTy (center s₁) (embedImprecise (core Wb) (slotRᴵ s₁))
          (embedImprecise (core Wb) B₀ᴵ′)
  t₁ = replace-⊑ (center s₁) (mode-eq s₁) (rep-related (atom s₁)) t₀

  target₁-P : embedPrecise (core Wb)
      (replaceTy (slotXᴾ s₁) (slotRᴾ s₁) B₀ᴾ′)
      ≡ replaceTy (center s₁) (embedPrecise (core Wb) (slotRᴾ s₁))
          (embedPrecise (core Wb) B₀ᴾ′)
  target₁-P = trans
    (renameᵗ-replaceTy (toRenameᵗ (preciseEmbedding (core Wb)))
      (toRenameᵗ-injective (preciseEmbedding (core Wb)))
      (slotXᴾ s₁) (slotRᴾ s₁) B₀ᴾ′)
    (cong
      (λ Z → replaceTy Z (embedPrecise (core Wb) (slotRᴾ s₁))
        (embedPrecise (core Wb) B₀ᴾ′))
      (preciseAligned (atom s₁)))

  target₁-I : embedImprecise (core Wb)
      (replaceTy (slotXᴵ s₁) (slotRᴵ s₁) B₀ᴵ′)
      ≡ replaceTy (center s₁) (embedImprecise (core Wb) (slotRᴵ s₁))
          (embedImprecise (core Wb) B₀ᴵ′)
  target₁-I = trans
    (renameᵗ-replaceTy (toRenameᵗ (impreciseEmbedding (core Wb)))
      (toRenameᵗ-injective (impreciseEmbedding (core Wb)))
      (slotXᴵ s₁) (slotRᴵ s₁) B₀ᴵ′)
    (cong
      (λ Z → replaceTy Z (embedImprecise (core Wb) (slotRᴵ s₁))
        (embedImprecise (core Wb) B₀ᴵ′))
      (impreciseAligned (atom s₁)))

  below≤ : ∀ j → j ≤ suc m → RevealAt j
  below≤ j j≤ = full-revealAt (below j (s≤s j≤))

  Nᴵ = ⇑ᵗᵐ (liftImpreciseTerm W≼W′ Vᴵ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) B₀ᴵ′ [ ＇ Fin.zero ]
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) B₀ᴾ′ [ ＇ Fin.zero ]

  revealed₁ : ComputationsRelated Wb (FutureValueRelation t₁) (suc m)
      (Nᴵ ↑ 〖 slotXᴵ s₁ , slotRᴵ s₁ ↑ B₀ᴵ′ 〗)
      (Nᴾ ↑ 〖 slotXᴾ s₁ , slotRᴾ s₁ ↑ B₀ᴾ′ 〗)
  revealed₁ = revealed-computations Wb s₁ t₀ refl refl t₁
    target₁-P target₁-I ≤-refl (λ j j≤ → below≤ j j≤) reindexed

  wrap-eq-I : (Nᴵ ↑ 〖 slotXᴵ s₁ , slotRᴵ s₁ ↑ B₀ᴵ′ 〗)
      ≡ (Nᴵ ↑ 〖 Fin.suc Xᴵ′ , ⇑ᵗ Rᴵ′ ↑ B₀ᴵ′ 〗)
  wrap-eq-I = cong₂ (λ X R → Nᴵ ↑ 〖 X , R ↑ B₀ᴵ′ 〗)
    (slot-imprecise-variable-lift s′ (paired-bind-step W′ r))
    (slot-imprecise-rep-lift s′ (paired-bind-step W′ r))

  wrap-eq-P : (Nᴾ ↑ 〖 slotXᴾ s₁ , slotRᴾ s₁ ↑ B₀ᴾ′ 〗)
      ≡ (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B₀ᴾ′ 〗)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↑ 〖 X , R ↑ B₀ᴾ′ 〗)
    (slot-precise-variable-lift s′ (paired-bind-step W′ r))
    (slot-precise-rep-lift s′ (paired-bind-step W′ r))

  revealed₁′ : ComputationsRelated Wb (FutureValueRelation t₁) (suc m)
      (Nᴵ ↑ 〖 Fin.suc Xᴵ′ , ⇑ᵗ Rᴵ′ ↑ B₀ᴵ′ 〗)
      (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B₀ᴾ′ 〗)
  revealed₁′ = ClosureProof.computations-related-reindex t₁ t₁
    refl refl wrap-eq-I wrap-eq-P revealed₁

  source₂-P : embedPrecise (core Wb)
      (replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
      ≡ replaceTy (center s₁) (embedPrecise (core Wb) (slotRᴾ s₁))
          (embedPrecise (core Wb) B₀ᴾ′)
  source₂-P = trans
    (cong₂ (λ X R → embedPrecise (core Wb) (replaceTy X R B₀ᴾ′))
      (sym (slot-precise-variable-lift s′ (paired-bind-step W′ r)))
      (sym (slot-precise-rep-lift s′ (paired-bind-step W′ r))))
    target₁-P

  source₂-I : embedImprecise (core Wb)
      (replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
      ≡ replaceTy (center s₁) (embedImprecise (core Wb) (slotRᴵ s₁))
          (embedImprecise (core Wb) B₀ᴵ′)
  source₂-I = trans
    (cong₂ (λ X R → embedImprecise (core Wb) (replaceTy X R B₀ᴵ′))
      (sym (slot-imprecise-variable-lift s′ (paired-bind-step W′ r)))
      (sym (slot-imprecise-rep-lift s′ (paired-bind-step W′ r))))
    target₁-I

  body-eq-P : liftPreciseBody W≼W′
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
      ≡ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′
  body-eq-P = trans
    (liftPreciseBody-replace W≼W′ (slotXᴾ s) (slotRᴾ s) B₀ᴾ)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B₀ᴾ′)
      (sym (slot-precise-variable-lift s W≼W′))
      (sym (slot-precise-rep-lift s W≼W′)))

  body-eq-I : liftImpreciseBody W≼W′
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
      ≡ replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′
  body-eq-I = trans
    (liftImpreciseBody-replace W≼W′ (slotXᴵ s) (slotRᴵ s) B₀ᴵ)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B₀ᴵ′)
      (sym (slot-imprecise-variable-lift s W≼W′))
      (sym (slot-imprecise-rep-lift s W≼W′)))

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Sᴾ)
        (replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′))
      ≡ ⇑ᵗ (embedPrecise (core W′)
          (liftPreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
            [ Sᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb))
      (replace-zero-open Sᴾ
        (replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)))
    (trans
      (embedPrecise-paired-shift (core W′) Sᴾ Sᴵ
        (replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′ [ Sᴾ ]ᵗ))
      (cong (λ T → ⇑ᵗ (embedPrecise (core W′) (T [ Sᴾ ]ᵗ)))
        (sym body-eq-P)))

  target₂-I : embedImprecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Sᴵ)
        (replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′))
      ≡ ⇑ᵗ (embedImprecise (core W′)
          (liftImpreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
            [ Sᴵ ]ᵗ))
  target₂-I = trans
    (cong (embedImprecise (core Wb))
      (replace-zero-open Sᴵ
        (replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)))
    (trans
      (embedImprecise-paired-shift (core W′) Sᴾ Sᴵ
        (replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′ [ Sᴵ ]ᵗ))
      (cong (λ T → ⇑ᵗ (embedImprecise (core W′) (T [ Sᴵ ]ᵗ)))
        (sym body-eq-I)))

  revealed₂ : ComputationsRelated Wb
      (FutureValueRelation
        (liftCenterImprecision (paired-bind-step W′ r) t)) (suc m)
      ((Nᴵ ↑ 〖 Fin.suc Xᴵ′ , ⇑ᵗ Rᴵ′ ↑ B₀ᴵ′ 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Sᴵ
          ↑ replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′ 〗)
      ((Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B₀ᴾ′ 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Sᴾ
          ↑ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′ 〗)
  revealed₂ = revealed-computations Wb s₂ t₁ source₂-P source₂-I
    (liftCenterImprecision (paired-bind-step W′ r) t)
    target₂-P target₂-I ≤-refl (λ j j≤ → below≤ j j≤) revealed₁′

-- One head of `UniversalsRelated` for a revealed universal value: the
-- type application allocates, the source universal is instantiated at
-- the freshly allocated name, and the result is revealed twice — at the
-- lifted old slot inside the body, then at the fresh slot.

reveal-universal-head : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {B₀ᴵ : Ty (suc Δᴵ)} {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    (p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Aᴾ)
  → (sourceᴵ : embedImprecise (core W) (`∀ B₀ᴵ) ≡ `∀ Aᴵ)
  → ∀ {k : ℕ} (below : OuterBelow (suc k))
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ p) (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Sᴾ : Ty Δᴾ′) (Sᴵ : Ty Δᴵ′) (r : Sᴾ ⊑ᵂ⟨ core W′ ⟩ Sᴵ)
      (t : liftPreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
            [ Sᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩
          liftImpreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
            [ Sᴵ ]ᵗ)
  → ComputationsRelated W′
      (PostBindValueRelation
        (future-paired (future-refl {W = W′}) r) t) (suc k)
      (liftImpreciseTerm W≼W′
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗)
        ⦂∀ liftImpreciseBody W≼W′
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ) [ Sᴵ ])
      (liftPreciseTerm W≼W′
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
        ⦂∀ liftPreciseBody W≼W′
          (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ) [ Sᴾ ])
reveal-universal-head W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ} p sourceᴾ sourceᴵ
    {k = k} below {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related W′ W≼W′ Sᴾ Sᴵ r t =
  ClosureProof.computations-related-post-bind-reindex t t
    refl refl (sym imprecise-redex-eq) (sym precise-redex-eq)
    stepped
  where
  s′ = slot-future s W≼W′
  Xᴾ′ = slotXᴾ s′
  Xᴵ′ = slotXᴵ s′
  Rᴾ′ = slotRᴾ s′
  Rᴵ′ = slotRᴵ s′
  B₀ᴾ′ = liftPreciseBody W≼W′ B₀ᴾ
  B₀ᴵ′ = liftImpreciseBody W≼W′ B₀ᴵ
  Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
  Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ
  cᴾ = 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B₀ᴾ′ 〗
  cᴵ = 〖 Fin.suc Xᴵ′ , ⇑ᵗ Rᴵ′ ↑ B₀ᴵ′ 〗

  precise-body-eq :
      liftPreciseBody W≼W′
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
      ≡ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′
  precise-body-eq = trans
    (liftPreciseBody-replace W≼W′ (slotXᴾ s) (slotRᴾ s) B₀ᴾ)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B₀ᴾ′)
      (sym (slot-precise-variable-lift s W≼W′))
      (sym (slot-precise-rep-lift s W≼W′)))

  imprecise-body-eq :
      liftImpreciseBody W≼W′
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
      ≡ replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′
  imprecise-body-eq = trans
    (liftImpreciseBody-replace W≼W′ (slotXᴵ s) (slotRᴵ s) B₀ᴵ)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B₀ᴵ′)
      (sym (slot-imprecise-variable-lift s W≼W′))
      (sym (slot-imprecise-rep-lift s W≼W′)))

  precise-redex-eq :
      liftPreciseTerm W≼W′ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
        ⦂∀ liftPreciseBody W≼W′
          (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ) [ Sᴾ ]
      ≡ (Vᴾ′ ↑ `∀↑ cᴾ) ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′ [ Sᴾ ]
  precise-redex-eq
      rewrite lifted-reveal-precise s W≼W′ Vᴾ (`∀ B₀ᴾ)
            | liftPreciseTy-universal W≼W′ B₀ᴾ
            | precise-body-eq = refl

  imprecise-redex-eq :
      liftImpreciseTerm W≼W′ (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗)
        ⦂∀ liftImpreciseBody W≼W′
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ) [ Sᴵ ]
      ≡ (Vᴵ′ ↑ `∀↑ cᴵ) ⦂∀ replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′ [ Sᴵ ]
  imprecise-redex-eq
      rewrite lifted-reveal-imprecise s W≼W′ Vᴵ (`∀ B₀ᴵ)
            | liftImpreciseTy-universal W≼W′ B₀ᴵ
            | imprecise-body-eq = refl

  stepped : ComputationsRelated W′
      (PostBindValueRelation
        (future-paired (future-refl {W = W′}) r) t) (suc k)
      ((Vᴵ′ ↑ `∀↑ cᴵ) ⦂∀ replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′ [ Sᴵ ])
      ((Vᴾ′ ↑ `∀↑ cᴾ) ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′ [ Sᴾ ])
  stepped
      with reveal-type-app-step-question
             {Σ = impreciseStore (core W′)} {A = Sᴵ} cᴵ vVᴵ′
         | reveal-type-app-step-question
             {Σ = preciseStore (core W′)} {A = Sᴾ} cᴾ vVᴾ′
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.∀⊑∀ p} {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    vVᴾ′ = ClosureProof.precise-value-future W≼W′
      (precise-value endpoints)
    vVᴵ′ = ClosureProof.imprecise-value-future W≼W′
      (imprecise-value endpoints)
  stepped | vVᴵ″ , step-eqᴵ | vVᴾ″ , step-eqᴾ =
    related-paired-bind-step-expand (λ ()) (λ ()) refl refl
      (β-reveal-∀ vVᴵ″) (β-reveal-∀ vVᴾ″) step-eqᴵ step-eqᴾ
      (reveal-universal-inner W s p sourceᴾ sourceᴵ below related
        W′ W≼W′ Sᴾ Sᴵ r t)

-- The residual of a concealed type application: the replaced source
-- universal is instantiated at the freshly allocated paired name, the
-- result is concealed at the lifted old slot inside the body, and
-- revealed at the fresh slot.

conceal-universal-inner : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {B₀ᴵ : Ty (suc Δᴵ)}
    {Aᴾ Aᴵ Aᴾʳ Aᴵʳ : Ty (suc Δᶜ)}
    (p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
    (q₀ : I.extᵐ (impEnv (core W)) I.⊢ Aᴾʳ ⊑ Aᴵʳ)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Aᴾ)
  → (sourceᴵ : embedImprecise (core W) (`∀ B₀ᴵ) ≡ `∀ Aᴵ)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ))
      ≡ `∀ Aᴾʳ)
  → (targetᴵ : embedImprecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ))
      ≡ `∀ Aᴵʳ)
  → ∀ {k : ℕ} (below : OuterBelow (suc k))
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ q₀) (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Sᴾ : Ty Δᴾ′) (Sᴵ : Ty Δᴵ′) (r : Sᴾ ⊑ᵂ⟨ core W′ ⟩ Sᴵ)
      (t : liftPreciseBody W≼W′ B₀ᴾ [ Sᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ B₀ᴵ [ Sᴵ ]ᵗ)
  → ComputationsRelated (pairedBindWorld W′ Sᴾ Sᴵ r)
      (FutureValueRelation
        (liftCenterImprecision (paired-bind-step W′ r) t)) k
      (((⇑ᵗᵐ (liftImpreciseTerm W≼W′ Vᴵ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
              (replaceTy (Fin.suc (slotXᴵ (slot-future s W≼W′)))
                (⇑ᵗ (slotRᴵ (slot-future s W≼W′)))
                (liftImpreciseBody W≼W′ B₀ᴵ))
            [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc (slotXᴵ (slot-future s W≼W′)))
            (⇑ᵗ (slotRᴵ (slot-future s W≼W′)))
            (liftImpreciseBody W≼W′ B₀ᴵ))
        ↑ 〖 Fin.zero , ⇑ᵗ Sᴵ ↑ liftImpreciseBody W≼W′ B₀ᴵ 〗)
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
              (replaceTy (Fin.suc (slotXᴾ (slot-future s W≼W′)))
                (⇑ᵗ (slotRᴾ (slot-future s W≼W′)))
                (liftPreciseBody W≼W′ B₀ᴾ))
            [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc (slotXᴾ (slot-future s W≼W′)))
            (⇑ᵗ (slotRᴾ (slot-future s W≼W′)))
            (liftPreciseBody W≼W′ B₀ᴾ))
        ↑ 〖 Fin.zero , ⇑ᵗ Sᴾ ↑ liftPreciseBody W≼W′ B₀ᴾ 〗)
conceal-universal-inner W s p q₀ sourceᴾ sourceᴵ targetᴾ targetᴵ
    {k = zero} below related W′ W≼W′ Sᴾ Sᴵ r t =
  ClosureProof.computations-related-zero
conceal-universal-inner W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {Aᴾʳ = Aᴾʳ} {Aᴵʳ = Aᴵʳ} p q₀
    sourceᴾ sourceᴵ targetᴾ targetᴵ {k = suc m} below
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related W′ W≼W′ Sᴾ Sᴵ r t
    with proj₂ related
conceal-universal-inner W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {Aᴾʳ = Aᴾʳ} {Aᴵʳ = Aᴵʳ} p q₀
    sourceᴾ sourceᴵ targetᴾ targetᴵ {k = suc m} below
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related W′ W≼W′ Sᴾ Sᴵ r t
    | Bᴾ* , Bᴵ* , embP , embI , chain
    with ty-all-injective
           (renameᵗ-injective
             (toRenameᵗ-injective (preciseEmbedding (core W)))
             (trans embP (sym targetᴾ)))
       | ty-all-injective
           (renameᵗ-injective
             (toRenameᵗ-injective (impreciseEmbedding (core W)))
             (trans embI (sym targetᴵ)))
conceal-universal-inner W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {Aᴾʳ = Aᴾʳ} {Aᴵʳ = Aᴵʳ} p q₀
    sourceᴾ sourceᴵ targetᴾ targetᴵ {k = suc m} below
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related W′ W≼W′ Sᴾ Sᴵ r t
    | .(replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
    , .(replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
    , embP , embI , chain
    | refl | refl = final
  where
  Wb = pairedBindWorld W′ Sᴾ Sᴵ r

  W≼Wb : Future W Wb
  W≼Wb = future-paired W≼W′ r

  s′ = slot-future s W≼W′
  s₁ = slot-future s′ (paired-bind-step W′ r)
  s₂ = fresh-slot W′ Sᴾ Sᴵ r
  Xᴾ′ = slotXᴾ s′
  Xᴵ′ = slotXᴵ s′
  Rᴾ′ = slotRᴾ s′
  Rᴵ′ = slotRᴵ s′
  B₀ᴾ′ = liftPreciseBody W≼W′ B₀ᴾ
  B₀ᴵ′ = liftImpreciseBody W≼W′ B₀ᴵ
  Lᴾ = liftPreciseBody W≼W′
    (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
  Lᴵ = liftImpreciseBody W≼W′
    (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)

  p′ : I.extᵐ (impEnv (core W′)) I.⊢
      liftCenterBody W≼W′ Aᴾ ⊑ liftCenterBody W≼W′ Aᴵ
  p′ = liftCenterBodyImprecision W≼W′ p

  q₀′ : I.extᵐ (impEnv (core W′)) I.⊢
      liftCenterBody W≼W′ Aᴾʳ ⊑ liftCenterBody W≼W′ Aᴵʳ
  q₀′ = liftCenterBodyImprecision W≼W′ q₀

  Aᴾ-eq : Aᴾ
      ≡ renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W)))) B₀ᴾ
  Aᴾ-eq = ty-all-injective (sym sourceᴾ)

  Aᴵ-eq : Aᴵ
      ≡ renameᵗ (extᵗ (toRenameᵗ (impreciseEmbedding (core W)))) B₀ᴵ
  Aᴵ-eq = ty-all-injective (sym sourceᴵ)

  Aᴾʳ-eq : Aᴾʳ
      ≡ renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W))))
          (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
  Aᴾʳ-eq = ty-all-injective (sym targetᴾ)

  Aᴵʳ-eq : Aᴵʳ
      ≡ renameᵗ (extᵗ (toRenameᵗ (impreciseEmbedding (core W))))
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
  Aᴵʳ-eq = ty-all-injective (sym targetᴵ)

  embed-eq-P : embedPrecise (core Wb) B₀ᴾ′ ≡ liftCenterBody W≼W′ Aᴾ
  embed-eq-P = trans (embed-precise-bind-body (core W′) Sᴾ Sᴵ B₀ᴾ′)
    (trans (embed-body-lift-precise W≼W′ B₀ᴾ)
      (cong (liftCenterBody W≼W′) (sym Aᴾ-eq)))

  embed-eq-I : embedImprecise (core Wb) B₀ᴵ′ ≡ liftCenterBody W≼W′ Aᴵ
  embed-eq-I = trans (embed-imprecise-bind-body (core W′) Sᴾ Sᴵ B₀ᴵ′)
    (trans (embed-body-lift-imprecise W≼W′ B₀ᴵ)
      (cong (liftCenterBody W≼W′) (sym Aᴵ-eq)))

  embed-eq-Pq : embedPrecise (core Wb) Lᴾ ≡ liftCenterBody W≼W′ Aᴾʳ
  embed-eq-Pq = trans (embed-precise-bind-body (core W′) Sᴾ Sᴵ Lᴾ)
    (trans
      (embed-body-lift-precise W≼W′
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ))
      (cong (liftCenterBody W≼W′) (sym Aᴾʳ-eq)))

  embed-eq-Iq : embedImprecise (core Wb) Lᴵ ≡ liftCenterBody W≼W′ Aᴵʳ
  embed-eq-Iq = trans (embed-imprecise-bind-body (core W′) Sᴾ Sᴵ Lᴵ)
    (trans
      (embed-body-lift-imprecise W≼W′
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ))
      (cong (liftCenterBody W≼W′) (sym Aᴵʳ-eq)))

  t₀ : impEnv (core Wb) I.⊢
      embedPrecise (core Wb) B₀ᴾ′ ⊑ embedImprecise (core Wb) B₀ᴵ′
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑ embedImprecise (core Wb) B₀ᴵ′)
    (sym embed-eq-P)
    (subst≡
      (λ R → impEnv (core Wb) I.⊢ liftCenterBody W≼W′ Aᴾ ⊑ R)
      (sym embed-eq-I) p′)

  t₀q : impEnv (core Wb) I.⊢
      embedPrecise (core Wb) Lᴾ ⊑ embedImprecise (core Wb) Lᴵ
  t₀q = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑ embedImprecise (core Wb) Lᴵ)
    (sym embed-eq-Pq)
    (subst≡
      (λ R → impEnv (core Wb) I.⊢ liftCenterBody W≼W′ Aᴾʳ ⊑ R)
      (sym embed-eq-Iq) q₀′)

  open-Pq : renameᵗ (extᵗ Fin.suc) Lᴾ [ ＇ Fin.zero ]ᵗ ≡ Lᴾ
  open-Pq = open-shifted-body Lᴾ

  open-Iq : renameᵗ (extᵗ Fin.suc) Lᴵ [ ＇ Fin.zero ]ᵗ ≡ Lᴵ
  open-Iq = open-shifted-body Lᴵ

  s₀ : renameᵗ (extᵗ Fin.suc) Lᴾ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ renameᵗ (extᵗ Fin.suc) Lᴵ [ ＇ Fin.zero ]ᵗ
  s₀ = subst≡
    (λ L → L ⊑ᵂ⟨ core Wb ⟩
      renameᵗ (extᵗ Fin.suc) Lᴵ [ ＇ Fin.zero ]ᵗ)
    (sym open-Pq)
    (subst≡ (λ R → Lᴾ ⊑ᵂ⟨ core Wb ⟩ R) (sym open-Iq) t₀q)

  r₀ : (＇ Fin.zero) ⊑ᵂ⟨ core Wb ⟩ (＇ Fin.zero)
  r₀ = I.X⊑X

  core-related : ComputationsRelated Wb
      (PostBindValueRelation
        (future-paired (future-refl {W = Wb}) r₀) s₀) (suc m)
      (liftImpreciseTerm W≼Wb Vᴵ
        ⦂∀ renameᵗ (extᵗ Fin.suc) Lᴵ [ ＇ Fin.zero ])
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ renameᵗ (extᵗ Fin.suc) Lᴾ [ ＇ Fin.zero ])
  core-related = universals-head {W = W} {p = q₀}
    {Bᴾ = replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ}
    {Bᴵ = replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = suc (suc m)}
    m (s≤s (n≤1+n m)) chain
    Wb W≼Wb (＇ Fin.zero) (＇ Fin.zero) r₀ s₀

  weakened : ComputationsRelated Wb (FutureValueRelation s₀) (suc m)
      (liftImpreciseTerm W≼Wb Vᴵ
        ⦂∀ renameᵗ (extᵗ Fin.suc) Lᴵ [ ＇ Fin.zero ])
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ renameᵗ (extᵗ Fin.suc) Lᴾ [ ＇ Fin.zero ])
  weakened = post-bind-weaken
    (future-paired (future-refl {W = Wb}) r₀) s₀ core-related

  body-eq-P : Lᴾ ≡ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′
  body-eq-P = trans
    (liftPreciseBody-replace W≼W′ (slotXᴾ s) (slotRᴾ s) B₀ᴾ)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B₀ᴾ′)
      (sym (slot-precise-variable-lift s W≼W′))
      (sym (slot-precise-rep-lift s W≼W′)))

  body-eq-I : Lᴵ ≡ replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′
  body-eq-I = trans
    (liftImpreciseBody-replace W≼W′ (slotXᴵ s) (slotRᴵ s) B₀ᴵ)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B₀ᴵ′)
      (sym (slot-imprecise-variable-lift s W≼W′))
      (sym (slot-imprecise-rep-lift s W≼W′)))

  Nᴵ = ⇑ᵗᵐ (liftImpreciseTerm W≼W′ Vᴵ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) Lᴵ [ ＇ Fin.zero ]
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) Lᴾ [ ＇ Fin.zero ]

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀q) (suc m)
      Nᴵ Nᴾ
  reindexed = ClosureProof.computations-related-reindex s₀ t₀q
    (cong (embedPrecise (core Wb)) open-Pq)
    (cong (embedImprecise (core Wb)) open-Iq)
    refl refl weakened

  target₁-P : embedPrecise (core Wb)
      (replaceTy (slotXᴾ s₁) (slotRᴾ s₁) B₀ᴾ′)
      ≡ embedPrecise (core Wb) Lᴾ
  target₁-P = trans
    (cong₂
      (λ X R → embedPrecise (core Wb) (replaceTy X R B₀ᴾ′))
      (slot-precise-variable-lift s′ (paired-bind-step W′ r))
      (slot-precise-rep-lift s′ (paired-bind-step W′ r)))
    (cong (embedPrecise (core Wb)) (sym body-eq-P))

  target₁-I : embedImprecise (core Wb)
      (replaceTy (slotXᴵ s₁) (slotRᴵ s₁) B₀ᴵ′)
      ≡ embedImprecise (core Wb) Lᴵ
  target₁-I = trans
    (cong₂
      (λ X R → embedImprecise (core Wb) (replaceTy X R B₀ᴵ′))
      (slot-imprecise-variable-lift s′ (paired-bind-step W′ r))
      (slot-imprecise-rep-lift s′ (paired-bind-step W′ r)))
    (cong (embedImprecise (core Wb)) (sym body-eq-I))

  belowC : ∀ j → j ≤ suc m → ConcealAt j
  belowC j j≤ = full-concealAt (below j (s≤s j≤))

  below≤ : ∀ j → j ≤ suc m → RevealAt j
  below≤ j j≤ = full-revealAt (below j (s≤s j≤))

  concealed₁ : ComputationsRelated Wb (FutureValueRelation t₀) (suc m)
      (Nᴵ ↓ makeConceal (slotXᴵ s₁) (slotRᴵ s₁) B₀ᴵ′)
      (Nᴾ ↓ makeConceal (slotXᴾ s₁) (slotRᴾ s₁) B₀ᴾ′)
  concealed₁ = concealed-computations Wb s₁ t₀ refl refl t₀q
    target₁-P target₁-I ≤-refl (λ j j≤ → belowC j j≤) reindexed

  wrap-eq-I : (Nᴵ ↓ makeConceal (slotXᴵ s₁) (slotRᴵ s₁) B₀ᴵ′)
      ≡ (Nᴵ ↓ makeConceal (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
  wrap-eq-I = cong₂ (λ X R → Nᴵ ↓ makeConceal X R B₀ᴵ′)
    (slot-imprecise-variable-lift s′ (paired-bind-step W′ r))
    (slot-imprecise-rep-lift s′ (paired-bind-step W′ r))

  wrap-eq-P : (Nᴾ ↓ makeConceal (slotXᴾ s₁) (slotRᴾ s₁) B₀ᴾ′)
      ≡ (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↓ makeConceal X R B₀ᴾ′)
    (slot-precise-variable-lift s′ (paired-bind-step W′ r))
    (slot-precise-rep-lift s′ (paired-bind-step W′ r))

  body-term-eq-I :
      (Nᴵ ↓ makeConceal (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
      ≡ ((⇑ᵗᵐ (liftImpreciseTerm W≼W′ Vᴵ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
              (replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
            [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
  body-term-eq-I = cong
    (λ T → (⇑ᵗᵐ (liftImpreciseTerm W≼W′ Vᴵ)
        ⦂∀ renameᵗ (extᵗ Fin.suc) T [ ＇ Fin.zero ])
      ↓ makeConceal (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
    body-eq-I

  body-term-eq-P :
      (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
      ≡ ((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
              (replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
            [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
  body-term-eq-P = cong
    (λ T → (⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
        ⦂∀ renameᵗ (extᵗ Fin.suc) T [ ＇ Fin.zero ])
      ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
    body-eq-P

  concealed₁′ : ComputationsRelated Wb (FutureValueRelation t₀)
      (suc m)
      ((⇑ᵗᵐ (liftImpreciseTerm W≼W′ Vᴵ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
              (replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
            [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
      ((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
              (replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
            [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
  concealed₁′ = ClosureProof.computations-related-reindex t₀ t₀
    refl refl
    (trans wrap-eq-I body-term-eq-I)
    (trans wrap-eq-P body-term-eq-P)
    concealed₁

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Sᴾ) B₀ᴾ′)
      ≡ ⇑ᵗ (embedPrecise (core W′) (B₀ᴾ′ [ Sᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb)) (replace-zero-open Sᴾ B₀ᴾ′))
    (embedPrecise-paired-shift (core W′) Sᴾ Sᴵ (B₀ᴾ′ [ Sᴾ ]ᵗ))

  target₂-I : embedImprecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Sᴵ) B₀ᴵ′)
      ≡ ⇑ᵗ (embedImprecise (core W′) (B₀ᴵ′ [ Sᴵ ]ᵗ))
  target₂-I = trans
    (cong (embedImprecise (core Wb)) (replace-zero-open Sᴵ B₀ᴵ′))
    (embedImprecise-paired-shift (core W′) Sᴾ Sᴵ (B₀ᴵ′ [ Sᴵ ]ᵗ))

  final : ComputationsRelated Wb
      (FutureValueRelation
        (liftCenterImprecision (paired-bind-step W′ r) t)) (suc m)
      (((⇑ᵗᵐ (liftImpreciseTerm W≼W′ Vᴵ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
              (replaceTy (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
            [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′)
        ↑ 〖 Fin.zero , ⇑ᵗ Sᴵ ↑ B₀ᴵ′ 〗)
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
              (replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
            [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
        ↑ 〖 Fin.zero , ⇑ᵗ Sᴾ ↑ B₀ᴾ′ 〗)
  final = revealed-computations Wb s₂ t₀ refl refl
    (liftCenterImprecision (paired-bind-step W′ r) t)
    target₂-P target₂-I ≤-refl (λ j j≤ → below≤ j j≤) concealed₁′

-- One head of `UniversalsRelated` for a concealed universal value.

conceal-universal-head : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {B₀ᴵ : Ty (suc Δᴵ)}
    {Aᴾ Aᴵ Aᴾʳ Aᴵʳ : Ty (suc Δᶜ)}
    (p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
    (q₀ : I.extᵐ (impEnv (core W)) I.⊢ Aᴾʳ ⊑ Aᴵʳ)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Aᴾ)
  → (sourceᴵ : embedImprecise (core W) (`∀ B₀ᴵ) ≡ `∀ Aᴵ)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ))
      ≡ `∀ Aᴾʳ)
  → (targetᴵ : embedImprecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ))
      ≡ `∀ Aᴵʳ)
  → ∀ {k : ℕ} (below : OuterBelow (suc k))
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ q₀) (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Sᴾ : Ty Δᴾ′) (Sᴵ : Ty Δᴵ′) (r : Sᴾ ⊑ᵂ⟨ core W′ ⟩ Sᴵ)
      (t : liftPreciseBody W≼W′ B₀ᴾ [ Sᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ B₀ᴵ [ Sᴵ ]ᵗ)
  → ComputationsRelated W′
      (PostBindValueRelation
        (future-paired (future-refl {W = W′}) r) t) (suc k)
      (liftImpreciseTerm W≼W′
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ))
        ⦂∀ liftImpreciseBody W≼W′ B₀ᴵ [ Sᴵ ])
      (liftPreciseTerm W≼W′
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
        ⦂∀ liftPreciseBody W≼W′ B₀ᴾ [ Sᴾ ])
conceal-universal-head W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ} p q₀
    sourceᴾ sourceᴵ targetᴾ targetᴵ
    {k = k} below {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related W′ W≼W′ Sᴾ Sᴵ r t =
  ClosureProof.computations-related-post-bind-reindex t t
    refl refl (sym imprecise-redex-eq) (sym precise-redex-eq)
    stepped
  where
  s′ = slot-future s W≼W′
  Xᴾ′ = slotXᴾ s′
  Xᴵ′ = slotXᴵ s′
  Rᴾ′ = slotRᴾ s′
  Rᴵ′ = slotRᴵ s′
  B₀ᴾ′ = liftPreciseBody W≼W′ B₀ᴾ
  B₀ᴵ′ = liftImpreciseBody W≼W′ B₀ᴵ
  Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
  Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ
  dᴾ = makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′
  dᴵ = makeConceal (Fin.suc Xᴵ′) (⇑ᵗ Rᴵ′) B₀ᴵ′

  precise-redex-eq :
      liftPreciseTerm W≼W′
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
        ⦂∀ liftPreciseBody W≼W′ B₀ᴾ [ Sᴾ ]
      ≡ (Vᴾ′ ↓ `∀↓ dᴾ) ⦂∀ B₀ᴾ′ [ Sᴾ ]
  precise-redex-eq
      rewrite lifted-conceal-precise s W≼W′ Vᴾ (`∀ B₀ᴾ)
            | liftPreciseTy-universal W≼W′ B₀ᴾ = refl

  imprecise-redex-eq :
      liftImpreciseTerm W≼W′
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ))
        ⦂∀ liftImpreciseBody W≼W′ B₀ᴵ [ Sᴵ ]
      ≡ (Vᴵ′ ↓ `∀↓ dᴵ) ⦂∀ B₀ᴵ′ [ Sᴵ ]
  imprecise-redex-eq
      rewrite lifted-conceal-imprecise s W≼W′ Vᴵ (`∀ B₀ᴵ)
            | liftImpreciseTy-universal W≼W′ B₀ᴵ = refl

  stepped : ComputationsRelated W′
      (PostBindValueRelation
        (future-paired (future-refl {W = W′}) r) t) (suc k)
      ((Vᴵ′ ↓ `∀↓ dᴵ) ⦂∀ B₀ᴵ′ [ Sᴵ ])
      ((Vᴾ′ ↓ `∀↓ dᴾ) ⦂∀ B₀ᴾ′ [ Sᴾ ])
  stepped
      with conceal-type-app-step-question
             {Σ = impreciseStore (core W′)} {A = Sᴵ} dᴵ vVᴵ′
         | conceal-type-app-step-question
             {Σ = preciseStore (core W′)} {A = Sᴾ} dᴾ vVᴾ′
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.∀⊑∀ q₀} {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    vVᴾ′ = ClosureProof.precise-value-future W≼W′
      (precise-value endpoints)
    vVᴵ′ = ClosureProof.imprecise-value-future W≼W′
      (imprecise-value endpoints)
  stepped | vVᴵ″ , step-eqᴵ | vVᴾ″ , step-eqᴾ =
    related-paired-bind-step-expand (λ ()) (λ ()) refl refl
      (β-conceal-∀ vVᴵ″) (β-conceal-∀ vVᴾ″) step-eqᴵ step-eqᴾ
      (conceal-universal-inner W s p q₀ sourceᴾ sourceᴵ
        targetᴾ targetᴵ below related W′ W≼W′ Sᴾ Sᴵ r t)

-- The value relation of a revealed universal value.

reveal-universal : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {B₀ᴵ : Ty (suc Δᴵ)}
    {Aᴾ Aᴵ Aᴾʳ Aᴵʳ : Ty (suc Δᶜ)}
    (p₀ : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
    (q₀ : I.extᵐ (impEnv (core W)) I.⊢ Aᴾʳ ⊑ Aᴵʳ)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Aᴾ)
  → (sourceᴵ : embedImprecise (core W) (`∀ B₀ᴵ) ≡ `∀ Aᴵ)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ))
      ≡ `∀ Aᴾʳ)
  → (targetᴵ : embedImprecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ))
      ≡ `∀ Aᴵʳ)
  → ∀ {k : ℕ} (below : OuterBelow k) {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ p₀) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation (I.∀⊑∀ q₀)) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
reveal-universal W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ} p₀ q₀
    sourceᴾ sourceᴵ targetᴾ targetᴵ
    {k = k} below {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  related-values-return
    (imprecise-value endpoints ↑ all) (precise-value endpoints ↑ all)
    at-every-index
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  reveal-endpoints : TypedEndpoints W (I.∀⊑∀ q₀)
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
  reveal-endpoints = revealed-endpoints W s (I.∀⊑∀ p₀)
    sourceᴾ sourceᴵ (I.∀⊑∀ q₀) targetᴾ targetᴵ related
    (imprecise-value endpoints ↑ all) (precise-value endpoints ↑ all)

  heads : ∀ (n : ℕ) → n ≤ k
    → ValueImprecision W (I.∀⊑∀ p₀) n Vᴵ Vᴾ
    → UniversalsRelated W q₀
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ) n
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗)
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
  heads zero n≤k source-at = tt
  heads (suc j) sj≤k source-at =
    (λ W′ W≼W′ Sᴾ Sᴵ r t →
      reveal-universal-head W s p₀ sourceᴾ sourceᴵ
        (outer-restrict sj≤k below) source-at W′ W≼W′ Sᴾ Sᴵ r t) ,
    heads j (≤-trans (n≤1+n j) sj≤k)
      (value-imprecision-downward-to
        {W = W} {p = I.∀⊑∀ p₀} {j = j} {k = suc j}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n j) source-at)

  at-every-index : ∀ (j : ℕ) → j ≤ k
    → FutureValueRelation (I.∀⊑∀ q₀) W future-refl j
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗)
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
  at-every-index zero j≤k = reveal-endpoints
  at-every-index (suc j) sj≤k =
    reveal-endpoints ,
    replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ ,
    replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ ,
    targetᴾ , targetᴵ ,
    heads (suc j) sj≤k
      (value-imprecision-downward-to
        {W = W} {p = I.∀⊑∀ p₀} {j = suc j} {k = k}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} sj≤k related)

-- The value relation of a concealed universal value.

conceal-universal : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {B₀ᴵ : Ty (suc Δᴵ)}
    {Aᴾ Aᴵ Aᴾʳ Aᴵʳ : Ty (suc Δᶜ)}
    (p₀ : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
    (q₀ : I.extᵐ (impEnv (core W)) I.⊢ Aᴾʳ ⊑ Aᴵʳ)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Aᴾ)
  → (sourceᴵ : embedImprecise (core W) (`∀ B₀ᴵ) ≡ `∀ Aᴵ)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ))
      ≡ `∀ Aᴾʳ)
  → (targetᴵ : embedImprecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ))
      ≡ `∀ Aᴵʳ)
  → ∀ {k : ℕ} (below : OuterBelow k) {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ q₀) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation (I.∀⊑∀ p₀)) k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ))
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
conceal-universal W s {B₀ᴾ = B₀ᴾ} {B₀ᴵ = B₀ᴵ} p₀ q₀
    sourceᴾ sourceᴵ targetᴾ targetᴵ
    {k = k} below {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  related-values-return
    (imprecise-value endpoints ↓ all) (precise-value endpoints ↓ all)
    at-every-index
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  conceal-endpoints : TypedEndpoints W (I.∀⊑∀ p₀)
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ))
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
  conceal-endpoints = concealed-endpoints W s (I.∀⊑∀ p₀)
    sourceᴾ sourceᴵ (I.∀⊑∀ q₀) targetᴾ targetᴵ related
    (imprecise-value endpoints ↓ all) (precise-value endpoints ↓ all)

  heads : ∀ (n : ℕ) → n ≤ k
    → ValueImprecision W (I.∀⊑∀ q₀) n Vᴵ Vᴾ
    → UniversalsRelated W p₀ B₀ᴾ B₀ᴵ n
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ))
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
  heads zero n≤k source-at = tt
  heads (suc j) sj≤k source-at =
    (λ W′ W≼W′ Sᴾ Sᴵ r t →
      conceal-universal-head W s p₀ q₀ sourceᴾ sourceᴵ
        targetᴾ targetᴵ (outer-restrict sj≤k below) source-at
        W′ W≼W′ Sᴾ Sᴵ r t) ,
    heads j (≤-trans (n≤1+n j) sj≤k)
      (value-imprecision-downward-to
        {W = W} {p = I.∀⊑∀ q₀} {j = j} {k = suc j}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n j) source-at)

  at-every-index : ∀ (j : ℕ) → j ≤ k
    → FutureValueRelation (I.∀⊑∀ p₀) W future-refl j
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ))
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
  at-every-index zero j≤k = conceal-endpoints
  at-every-index (suc j) sj≤k =
    conceal-endpoints ,
    B₀ᴾ , B₀ᴵ , sourceᴾ , sourceᴵ ,
    heads (suc j) sj≤k
      (value-imprecision-downward-to
        {W = W} {p = I.∀⊑∀ q₀} {j = suc j} {k = k}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} sj≤k related)

------------------------------------------------------------------------
-- Concealing to a bottom type is impossible
------------------------------------------------------------------------

-- The concealed precise value would be a value of the empty universal
-- type.

bottom-conceal-impossible : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴾ : Ty Δᴾ}
  → embedPrecise (core W) Bᴾ ≡ `∀ (＇ Fin.zero)
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → ⊥
bottom-conceal-impossible W s {Bᴾ = Bᴾ} sourceᴾ q targetᴾ related
    with rename-universal-inversion _ sourceᴾ
bottom-conceal-impossible W s sourceᴾ q targetᴾ related
    | Bᴾ₀ , refl , bodyᴾ
    with rename-variable-inversion _ bodyᴾ
bottom-conceal-impossible W s sourceᴾ q targetᴾ related
    | .(＇ Fin.zero) , refl , bodyᴾ | Fin.zero , refl , centerᴾ =
  no-bot-value (precise-value endpoints ↓ all)
    (⊢conceal
      (structural-conceal-typing (`∀ (＇ Fin.zero))
        (preciseBound (atom s)))
      Vᴾ⊢Cᴾ)
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  Vᴾ⊢Cᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective (toRenameᵗ-injective (preciseEmbedding (core W)))
      (trans (preciseEmbedded endpoints) (sym targetᴾ)))
    (precise-typed endpoints)
bottom-conceal-impossible W s sourceᴾ q targetᴾ related
    | .(＇ (Fin.suc _)) , refl , bodyᴾ | Fin.suc Y , refl , centerᴾ
    with centerᴾ
bottom-conceal-impossible W s sourceᴾ q targetᴾ related
    | .(＇ (Fin.suc _)) , refl , bodyᴾ | Fin.suc Y , refl , centerᴾ | ()

------------------------------------------------------------------------
-- The induction
------------------------------------------------------------------------

reveal-conceal-step : ∀ (k n : ℕ) → Below k n
  → RevealAtSized k n × ConcealAtSized k n
reveal-conceal-step k n below = reveal-at , conceal-at
  where
  reveal-at : RevealAtSized k n
  reveal-at W s I.★⊑★ size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    RA.AtSlot.reveal-atomic W (atom s) (entry-eq s) (mode-eq s)
      I.★⊑★ atomic-★ sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  reveal-at W s I.ι⊑ι size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    RA.AtSlot.reveal-atomic W (atom s) (entry-eq s) (mode-eq s)
      I.ι⊑ι atomic-ι sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  reveal-at W s I.X⊑X size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    RA.AtSlot.reveal-atomic W (atom s) (entry-eq s) (mode-eq s)
      I.X⊑X atomic-X sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  reveal-at W s I.ι⊑★ size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    RA.AtSlot.reveal-atomic W (atom s) (entry-eq s) (mode-eq s)
      I.ι⊑★ atomic-ι★ sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  reveal-at W s (I.X⊑★ eq) size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ
      related =
    RA.AtSlot.reveal-atomic W (atom s) (entry-eq s) (mode-eq s)
      (I.X⊑★ eq) (atomic-X★ eq) sourceᴾ sourceᴵ q targetᴾ targetᴵ
      related
  reveal-at W s (I.⇒⊑⇒ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      with rename-arrow-inversion _ sourceᴾ
         | rename-arrow-inversion _ sourceᴵ
  reveal-at W s (I.⇒⊑⇒ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      with targetᴾ | targetᴵ
  reveal-at W s (I.⇒⊑⇒ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      | refl | refl
      with arrow-imprecision-view q
  reveal-at W s (I.⇒⊑⇒ p₁ p₂) size≤
      sourceᴾ sourceᴵ .(I.⇒⊑⇒ q₁ q₂) targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      | refl | refl
      | arrow-imprecision q₁ q₂ =
    reveal-function W s p₁ p₂
      sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂ q₁ q₂
      refl refl refl refl (below-outer below) related
  reveal-at W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} (I.⇒⊑★ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      with rename-star-injective _ sourceᴵ
  reveal-at W s {Bᴾ = Bᴾ} (I.⇒⊑★ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related | refl
      with reveal-id-step-question {Σ = impreciseStore (core W)} ★
             (imprecise-value
               (ClosureProof.value-imprecision-endpoints related))
  reveal-at W s {Bᴾ = Bᴾ} (I.⇒⊑★ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related | refl
      | vVᴵ , step-eqᴵ =
    related-imprecise-keep-step-expand (λ ())
      (reveal-id-value-none ★ vVᴵ) (pure-step (id-reveal vVᴵ)) step-eqᴵ
      (ClosureProof.computations-related-reindex
        (I.⇒⊑★ p₁ p₂) q (trans (sym sourceᴾ) precise-target)
        (trans (sym sourceᴵ) targetᴵ) refl refl
        (precise-reveal below W s (I.⇒⊑★ p₁ p₂) slot-absent
          sourceᴾ related))
    where
    slot-absent : slotXᴾ s ∉ᵗ Bᴾ
    slot-absent = renameᵗ-reflects-∉ᵗ
      (toRenameᵗ (preciseEmbedding (core W))) Bᴾ
      (subst≡ (_∉ᵗ embedPrecise (core W) Bᴾ)
        (sym (preciseAligned (atom s)))
        (star-no-occurrence (center s) (mode-eq s)
          (subst≡ (λ A → impEnv (core W) I.⊢ A ⊑ ★) (sym sourceᴾ)
            (I.⇒⊑★ p₁ p₂))))

    precise-target : embedPrecise (core W) Bᴾ ≡ _
    precise-target = trans
      (cong (embedPrecise (core W))
        (sym (replaceTy-absent (slotXᴾ s) (slotRᴾ s) slot-absent)))
      targetᴾ
  reveal-at W s (I.∀⊑∀ p₀) size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ
      related
      with rename-universal-inversion _ sourceᴾ
         | rename-universal-inversion _ sourceᴵ
  reveal-at W s (I.∀⊑∀ p₀) size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ
      related
      | B₀ᴾ , refl , eqᴾ | B₀ᴵ , refl , eqᴵ
      with targetᴾ | targetᴵ
  reveal-at W s (I.∀⊑∀ {A = Aᴾc} {B = Aᴵc} p₀) size≤ sourceᴾ sourceᴵ
      q targetᴾ targetᴵ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | B₀ᴾ , refl , eqᴾ | B₀ᴵ , refl , eqᴵ
      | refl | refl =
    subst≡
      (λ q′ → ComputationsRelated W (FutureValueRelation q′) k
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗)
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗))
      (sym (PI.⊑-unique q (I.∀⊑∀ alt-body)))
      (reveal-universal W s p₀ alt-body sourceᴾ sourceᴵ refl refl
        (below-outer below) related)
    where
    ρᴾ = toRenameᵗ (preciseEmbedding (core W))
    ρᴵ = toRenameᵗ (impreciseEmbedding (core W))

    base : I.extᵐ (impEnv (core W)) I.⊢
        renameᵗ (extᵗ ρᴾ) B₀ᴾ ⊑ renameᵗ (extᵗ ρᴵ) B₀ᴵ
    base = subst≡
      (λ L → I.extᵐ (impEnv (core W)) I.⊢
        L ⊑ renameᵗ (extᵗ ρᴵ) B₀ᴵ)
      (sym eqᴾ)
      (subst≡
        (λ R → I.extᵐ (impEnv (core W)) I.⊢ Aᴾc ⊑ R)
        (sym eqᴵ) p₀)

    rep′ : I.extᵐ (impEnv (core W)) I.⊢
        ⇑ᵗ (embedPrecise (core W) (slotRᴾ s))
        ⊑ ⇑ᵗ (embedImprecise (core W) (slotRᴵ s))
    rep′ = shift-⊑ I.X⊑X (rep-related (atom s))

    commute-P : renameᵗ (extᵗ ρᴾ)
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
        ≡ replaceTy (Fin.suc (center s))
            (⇑ᵗ (embedPrecise (core W) (slotRᴾ s)))
            (renameᵗ (extᵗ ρᴾ) B₀ᴾ)
    commute-P = trans
      (renameᵗ-replaceTy (extᵗ ρᴾ)
        (ext-injective
          (toRenameᵗ-injective (preciseEmbedding (core W))))
        (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
      (cong₂ (λ Z R → replaceTy Z R (renameᵗ (extᵗ ρᴾ) B₀ᴾ))
        (cong Fin.suc (preciseAligned (atom s)))
        (renameᵗ-shift ρᴾ (slotRᴾ s)))

    commute-I : renameᵗ (extᵗ ρᴵ)
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
        ≡ replaceTy (Fin.suc (center s))
            (⇑ᵗ (embedImprecise (core W) (slotRᴵ s)))
            (renameᵗ (extᵗ ρᴵ) B₀ᴵ)
    commute-I = trans
      (renameᵗ-replaceTy (extᵗ ρᴵ)
        (ext-injective
          (toRenameᵗ-injective (impreciseEmbedding (core W))))
        (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
      (cong₂ (λ Z R → replaceTy Z R (renameᵗ (extᵗ ρᴵ) B₀ᴵ))
        (cong Fin.suc (impreciseAligned (atom s)))
        (renameᵗ-shift ρᴵ (slotRᴵ s)))

    raw : I.extᵐ (impEnv (core W)) I.⊢
        replaceTy (Fin.suc (center s))
          (⇑ᵗ (embedPrecise (core W) (slotRᴾ s)))
          (renameᵗ (extᵗ ρᴾ) B₀ᴾ)
        ⊑ replaceTy (Fin.suc (center s))
            (⇑ᵗ (embedImprecise (core W) (slotRᴵ s)))
            (renameᵗ (extᵗ ρᴵ) B₀ᴵ)
    raw = replace-⊑ (Fin.suc (center s)) (mode-eq s) rep′ base

    alt-body : I.extᵐ (impEnv (core W)) I.⊢
        renameᵗ (extᵗ ρᴾ)
          (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
        ⊑ renameᵗ (extᵗ ρᴵ)
            (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
    alt-body = subst≡
      (λ L → I.extᵐ (impEnv (core W)) I.⊢
        L ⊑ renameᵗ (extᵗ ρᴵ)
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ))
      (sym commute-P)
      (subst≡
        (λ R → I.extᵐ (impEnv (core W)) I.⊢
          replaceTy (Fin.suc (center s))
            (⇑ᵗ (embedPrecise (core W) (slotRᴾ s)))
            (renameᵗ (extᵗ ρᴾ) B₀ᴾ) ⊑ R)
        (sym commute-I) raw)

  reveal-at W s (I.∀⊑ nonvar occurs p₀) size≤ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    blocked-reveal below W s (I.∀⊑ nonvar occurs p₀) size≤
      blocked-∀⊑ sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  reveal-at W s I.∀★⊑★ size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    blocked-reveal below W s I.∀★⊑★ size≤ blocked-∀★⊑★
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  reveal-at W s (I.∀⊑★ nonstar p₀) size≤ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    blocked-reveal below W s (I.∀⊑★ nonstar p₀) size≤
      blocked-∀⊑★ sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  reveal-at W s I.bot-elim size≤ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    ⊥-elim (no-precise-bottom-value related)
  reveal-at W s I.bot⊑★ size≤ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    ⊥-elim (no-precise-bottom-value related)

  conceal-at : ConcealAtSized k n
  conceal-at W s I.★⊑★ size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    CA.AtSlot.conceal-atomic W (atom s) (entry-eq s) (mode-eq s)
      I.★⊑★ atomic-★ sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  conceal-at W s I.ι⊑ι size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    CA.AtSlot.conceal-atomic W (atom s) (entry-eq s) (mode-eq s)
      I.ι⊑ι atomic-ι sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  conceal-at W s I.X⊑X size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    CA.AtSlot.conceal-atomic W (atom s) (entry-eq s) (mode-eq s)
      I.X⊑X atomic-X sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  conceal-at W s I.ι⊑★ size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    CA.AtSlot.conceal-atomic W (atom s) (entry-eq s) (mode-eq s)
      I.ι⊑★ atomic-ι★ sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  conceal-at W s (I.X⊑★ eq) size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ
      related =
    CA.AtSlot.conceal-atomic W (atom s) (entry-eq s) (mode-eq s)
      (I.X⊑★ eq) (atomic-X★ eq) sourceᴾ sourceᴵ q targetᴾ targetᴵ
      related
  conceal-at W s (I.⇒⊑⇒ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      with rename-arrow-inversion _ sourceᴾ
         | rename-arrow-inversion _ sourceᴵ
  conceal-at W s (I.⇒⊑⇒ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      with targetᴾ | targetᴵ
  conceal-at W s (I.⇒⊑⇒ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      | refl | refl
      with arrow-imprecision-view q
  conceal-at W s (I.⇒⊑⇒ p₁ p₂) size≤
      sourceᴾ sourceᴵ .(I.⇒⊑⇒ q₁ q₂) targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      | refl | refl
      | arrow-imprecision q₁ q₂ =
    conceal-function W s p₁ p₂
      sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂ q₁ q₂
      refl refl refl refl (below-outer below) related
  conceal-at W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} (I.⇒⊑★ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      with rename-star-injective _ sourceᴵ
  conceal-at W s {Bᴾ = Bᴾ} (I.⇒⊑★ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related | refl
      with conceal-id-step-question {Σ = impreciseStore (core W)} ★
             (imprecise-value
               (ClosureProof.value-imprecision-endpoints related))
  conceal-at W s {Bᴾ = Bᴾ} (I.⇒⊑★ p₁ p₂) size≤
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related | refl
      | vVᴵ , step-eqᴵ =
    related-imprecise-keep-step-expand (λ ())
      (conceal-id-value-none ★ vVᴵ) (pure-step (id-conceal vVᴵ))
      step-eqᴵ
      (precise-conceal below W s (I.⇒⊑★ p₁ p₂) slot-absent
        sourceᴾ
        (ClosureProof.value-imprecision-reindex
          (I.⇒⊑★ p₁ p₂) q (trans (sym sourceᴾ) precise-target)
          (trans (sym sourceᴵ) targetᴵ) related))
    where
    slot-absent : slotXᴾ s ∉ᵗ Bᴾ
    slot-absent = renameᵗ-reflects-∉ᵗ
      (toRenameᵗ (preciseEmbedding (core W))) Bᴾ
      (subst≡ (_∉ᵗ embedPrecise (core W) Bᴾ)
        (sym (preciseAligned (atom s)))
        (star-no-occurrence (center s) (mode-eq s)
          (subst≡ (λ A → impEnv (core W) I.⊢ A ⊑ ★) (sym sourceᴾ)
            (I.⇒⊑★ p₁ p₂))))

    precise-target : embedPrecise (core W) Bᴾ ≡ _
    precise-target = trans
      (cong (embedPrecise (core W))
        (sym (replaceTy-absent (slotXᴾ s) (slotRᴾ s) slot-absent)))
      targetᴾ
  conceal-at W s (I.∀⊑∀ p₀) size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ
      related
      with rename-universal-inversion _ sourceᴾ
         | rename-universal-inversion _ sourceᴵ
  conceal-at W s (I.∀⊑∀ p₀) size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ
      related
      | B₀ᴾ , refl , eqᴾ | B₀ᴵ , refl , eqᴵ
      with targetᴾ | targetᴵ
  conceal-at W s (I.∀⊑∀ {A = Aᴾc} {B = Aᴵc} p₀) size≤ sourceᴾ sourceᴵ
      q targetᴾ targetᴵ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | B₀ᴾ , refl , eqᴾ | B₀ᴵ , refl , eqᴵ
      | refl | refl =
    conceal-universal W s p₀ alt-body sourceᴾ sourceᴵ refl refl
      (below-outer below)
      (subst≡ (λ q′ → ValueImprecision W q′ k Vᴵ Vᴾ)
        (PI.⊑-unique q (I.∀⊑∀ alt-body)) related)
    where
    ρᴾ = toRenameᵗ (preciseEmbedding (core W))
    ρᴵ = toRenameᵗ (impreciseEmbedding (core W))

    base : I.extᵐ (impEnv (core W)) I.⊢
        renameᵗ (extᵗ ρᴾ) B₀ᴾ ⊑ renameᵗ (extᵗ ρᴵ) B₀ᴵ
    base = subst≡
      (λ L → I.extᵐ (impEnv (core W)) I.⊢
        L ⊑ renameᵗ (extᵗ ρᴵ) B₀ᴵ)
      (sym eqᴾ)
      (subst≡
        (λ R → I.extᵐ (impEnv (core W)) I.⊢ Aᴾc ⊑ R)
        (sym eqᴵ) p₀)

    rep′ : I.extᵐ (impEnv (core W)) I.⊢
        ⇑ᵗ (embedPrecise (core W) (slotRᴾ s))
        ⊑ ⇑ᵗ (embedImprecise (core W) (slotRᴵ s))
    rep′ = shift-⊑ I.X⊑X (rep-related (atom s))

    commute-P : renameᵗ (extᵗ ρᴾ)
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
        ≡ replaceTy (Fin.suc (center s))
            (⇑ᵗ (embedPrecise (core W) (slotRᴾ s)))
            (renameᵗ (extᵗ ρᴾ) B₀ᴾ)
    commute-P = trans
      (renameᵗ-replaceTy (extᵗ ρᴾ)
        (ext-injective
          (toRenameᵗ-injective (preciseEmbedding (core W))))
        (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
      (cong₂ (λ Z R → replaceTy Z R (renameᵗ (extᵗ ρᴾ) B₀ᴾ))
        (cong Fin.suc (preciseAligned (atom s)))
        (renameᵗ-shift ρᴾ (slotRᴾ s)))

    commute-I : renameᵗ (extᵗ ρᴵ)
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
        ≡ replaceTy (Fin.suc (center s))
            (⇑ᵗ (embedImprecise (core W) (slotRᴵ s)))
            (renameᵗ (extᵗ ρᴵ) B₀ᴵ)
    commute-I = trans
      (renameᵗ-replaceTy (extᵗ ρᴵ)
        (ext-injective
          (toRenameᵗ-injective (impreciseEmbedding (core W))))
        (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
      (cong₂ (λ Z R → replaceTy Z R (renameᵗ (extᵗ ρᴵ) B₀ᴵ))
        (cong Fin.suc (impreciseAligned (atom s)))
        (renameᵗ-shift ρᴵ (slotRᴵ s)))

    raw : I.extᵐ (impEnv (core W)) I.⊢
        replaceTy (Fin.suc (center s))
          (⇑ᵗ (embedPrecise (core W) (slotRᴾ s)))
          (renameᵗ (extᵗ ρᴾ) B₀ᴾ)
        ⊑ replaceTy (Fin.suc (center s))
            (⇑ᵗ (embedImprecise (core W) (slotRᴵ s)))
            (renameᵗ (extᵗ ρᴵ) B₀ᴵ)
    raw = replace-⊑ (Fin.suc (center s)) (mode-eq s) rep′ base

    alt-body : I.extᵐ (impEnv (core W)) I.⊢
        renameᵗ (extᵗ ρᴾ)
          (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
        ⊑ renameᵗ (extᵗ ρᴵ)
            (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
    alt-body = subst≡
      (λ L → I.extᵐ (impEnv (core W)) I.⊢
        L ⊑ renameᵗ (extᵗ ρᴵ)
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ))
      (sym commute-P)
      (subst≡
        (λ R → I.extᵐ (impEnv (core W)) I.⊢
          replaceTy (Fin.suc (center s))
            (⇑ᵗ (embedPrecise (core W) (slotRᴾ s)))
            (renameᵗ (extᵗ ρᴾ) B₀ᴾ) ⊑ R)
        (sym commute-I) raw)

  conceal-at W s (I.∀⊑ nonvar occurs p₀) size≤ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    blocked-conceal below W s (I.∀⊑ nonvar occurs p₀) size≤
      blocked-∀⊑ sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  conceal-at W s I.∀★⊑★ size≤ sourceᴾ sourceᴵ q targetᴾ targetᴵ related =
    blocked-conceal below W s I.∀★⊑★ size≤ blocked-∀★⊑★
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  conceal-at W s (I.∀⊑★ nonstar p₀) size≤ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    blocked-conceal below W s (I.∀⊑★ nonstar p₀) size≤
      blocked-∀⊑★ sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  conceal-at W s I.bot-elim size≤ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    ⊥-elim (bottom-conceal-impossible W s sourceᴾ q targetᴾ related)
  conceal-at W s I.bot⊑★ size≤ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    ⊥-elim (bottom-conceal-impossible W s sourceᴾ q targetᴾ related)

-- Strong induction on the lexicographic (step index, derivation
-- size), producing the paired, one-sided, and dynamic statements
-- together.

statements-step : ∀ (k n : ℕ) → Below k n → Statements k n
statements-step k n below =
  proj₁ paired , proj₂ paired ,
  precise-reveal below , precise-conceal below ,
  blocked-dyn-reveal below , blocked-dyn-conceal below
  where
  paired = reveal-conceal-step k n below

statements-inner : ∀ (k : ℕ) → OuterBelow k
  → ∀ (n : ℕ) → Acc _<_ n → Statements k n
statements-inner k outer n (acc smaller-size) =
  statements-step k n below
  where
  below : Below k n
  below j m (lex-index j<k) = outer j j<k m
  below j m (lex-size refl m<n) =
    statements-inner j outer m (smaller-size m<n)

statements-acc : ∀ (k : ℕ) → Acc _<_ k → FullStatements k
statements-acc k (acc smaller) n =
  statements-inner k
    (λ j j<k m → statements-acc j (smaller j<k) m) n (wf n)

statements-all : ∀ (k n : ℕ) → Statements k n
statements-all k n = statements-acc k (wf k) n

------------------------------------------------------------------------
-- The structural reveal and conceal
------------------------------------------------------------------------

reveal-structural : ∀ {k} → RevealAt k
reveal-structural {k = k} {n = n} = revealAt (statements-all k n)

conceal-structural : ∀ {k} → ConcealAt k
conceal-structural {k = k} {n = n} = concealAt (statements-all k n)

precise-reveal-structural : ∀ {k} → PreciseRevealAt k
precise-reveal-structural {k = k} =
  preciseRevealAt (statements-all k 0)

precise-conceal-structural : ∀ {k} → PreciseConcealAt k
precise-conceal-structural {k = k} =
  preciseConcealAt (statements-all k 0)

dyn-reveal-structural : ∀ {k} → DynRevealAt k
dyn-reveal-structural {k = k} = dynRevealAt (statements-all k 0)

dyn-conceal-structural : ∀ {k} → DynConcealAt k
dyn-conceal-structural {k = k} = dynConcealAt (statements-all k 0)
