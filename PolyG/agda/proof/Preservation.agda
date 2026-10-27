module proof.Preservation where

-- File Charter:
--   * Preservation for closed PolyCν terms: a step from a well-typed
--     closed term under a closed store (StoreWf) yields a well-typed
--     term under the new store, and the new store is again closed.
--   * Reduction only extends the store, by one entry at β-inst
--     (`step-extends`), so typings of the surrounding frame survive by
--     store weakening.
--   * Uses the substitution lemmas of proof/TypingSubst.agda; consumed
--     by the top-level TypeSafety.agda.

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Types
open import Terms
open import Reduction
open import Typing
open import StoreWf
open import proof.TypeSubst
open import proof.TypingSubst
open import proof.Determinism using (Plug; plug-Plug; p-if; p-□·; p-app;
  p-letv; p-seal; p-unseal; p-is; p-inj; p-cast; p-inst)

------------------------------------------------------------------------
-- Reduction extends the store
------------------------------------------------------------------------

step-extends : ∀ {Σ Σ′ M N}
  → Σ ▷ M —→ Σ′ ▷ N
  → Σ′ ≡ Σ ⊎ ∃[ B ] (Σ′ ≡ Σ ++ (B ∷ []))
step-extends (ξξ F refl refl s) = step-extends s
step-extends (ξξ-℧ F refl) = inj₁ refl
step-extends (β-letv v) = inj₁ refl
step-extends (β-unseal v) = inj₁ refl
step-extends (β-is-yes v) = inj₁ refl
step-extends (β-is-no v G≢H) = inj₁ refl
step-extends β-if-true = inj₁ refl
step-extends β-if-false = inj₁ refl
step-extends (β-ƛ v) = inj₁ refl
step-extends (β-cast⇒ v w) = inj₁ refl
step-extends (β-inst {B = B}) = inj₂ (B , refl)
step-extends (β-id a v) = inj₁ refl
step-extends (β-tag-up v) = inj₁ refl
step-extends (β-tag-down v) = inj₁ refl
step-extends (β-tag-down-℧ v G≢H) = inj₁ refl
step-extends β-cast∀ = inj₁ refl

step-⊆ : ∀ {Σ Σ′ M N} → Σ ▷ M —→ Σ′ ▷ N → Σ ⊆ˢ Σ′
step-⊆ s with step-extends s
step-⊆ s | inj₁ refl = λ h → h
step-⊆ s | inj₂ (B , refl) = ∋ˢ-++ (B ∷ [])

------------------------------------------------------------------------
-- Casts that are the identity relate equal types
------------------------------------------------------------------------

atomic-≡ : ∀ {n p A B} → Atomic p → n ⊢ p ⦂ A ⊑ B → A ≡ B
atomic-≡ at★ ⊑★ = refl
atomic-≡ at𝔹 ⊑𝔹 = refl
atomic-≡ at‵ (⊑‵ wfα) = refl

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

preserve : ∀ {Σ Σ′ M N A}
  → StoreWf Σ
  → Σ ∣ [] ∣ [] ⊢ M ⦂ A
  → Σ ▷ M —→ Σ′ ▷ N
  → Σ′ ∣ [] ∣ [] ⊢ N ⦂ A × StoreWf Σ′

-- a step inside a frame
preserve-ξ : ∀ {Σ Σ′ F M N T A}
  → StoreWf Σ
  → Plug F M T
  → Σ ∣ [] ∣ [] ⊢ T ⦂ A
  → Σ ▷ M —→ Σ′ ▷ N
  → Σ′ ∣ [] ∣ [] ⊢ plug F N ⦂ A × StoreWf Σ′

preserve wfΣ ⊢M (ξξ F refl refl s) = preserve-ξ wfΣ (plug-Plug F _) ⊢M s
preserve wfΣ ⊢M (ξξ-℧ F refl) = ⊢℧ , wfΣ
preserve wfΣ (⊢letv ⊢V ⊢N) (β-letv v) = ⊢-[] wfΣ ⊢N ⊢V , wfΣ
preserve wfΣ (⊢unseal nt (⊢seal nt′ ⊢V)) (β-unseal v) =
  cong-⊢ refl refl (NameTy-unique (λ ()) nt′ nt) ⊢V , wfΣ
preserve wfΣ (⊢is wfG ⊢M) (β-is-yes v) = ⊢true , wfΣ
preserve wfΣ (⊢is wfG ⊢M) (β-is-no v G≢H) = ⊢false , wfΣ
preserve wfΣ (⊢if ⊢L ⊢M ⊢N) β-if-true = ⊢M , wfΣ
preserve wfΣ (⊢if ⊢L ⊢M ⊢N) β-if-false = ⊢N , wfΣ
preserve wfΣ (⊢· (⊢ƛ ⊢M) ⊢V) (β-ƛ v) = ⊢-[] wfΣ ⊢M ⊢V , wfΣ
preserve wfΣ (⊢· (⊢up (⊑⇒ p⊢ q⊢) ⊢V) ⊢W) (β-cast⇒ v w) =
  ⊢up q⊢ (⊢· ⊢V (⊢down p⊢ ⊢W)) , wfΣ
preserve wfΣ (⊢· (⊢down (⊑⇒ p⊢ q⊢) ⊢V) ⊢W) (β-cast⇒ v w) =
  ⊢down q⊢ (⊢· ⊢V (⊢up p⊢ ⊢W)) , wfΣ
preserve wfΣ (⊢inst (⊢Λν ⊢M) wfB ⊢N) β-inst =
  ⊢letv (⊢-inst-body wfΣ wfB ⊢M) (⊢-inst-cont wfΣ wfB ⊢N)
  , storeWf-snoc wfΣ wfB
preserve wfΣ (⊢up p⊢ ⊢V) (β-id a v) =
  cong-⊢ refl refl (atomic-≡ a p⊢) ⊢V , wfΣ
preserve wfΣ (⊢down p⊢ ⊢V) (β-id a v) =
  cong-⊢ refl refl (sym (atomic-≡ a p⊢)) ⊢V , wfΣ
preserve wfΣ (⊢up (⊑tag wfG p⊢) ⊢V) (β-tag-up v) =
  ⊢inj wfG (⊢up p⊢ ⊢V) , wfΣ
preserve wfΣ (⊢down (⊑tag wfG p⊢) (⊢inj wfG′ ⊢V)) (β-tag-down v) =
  ⊢down p⊢ ⊢V , wfΣ
preserve wfΣ (⊢down p⊢ ⊢V) (β-tag-down-℧ v G≢H) = ⊢℧ , wfΣ
preserve wfΣ (⊢up (⊑∀ p⊢) (⊢Λν ⊢M)) β-cast∀ = ⊢Λν (⊢up p⊢ ⊢M) , wfΣ
preserve wfΣ (⊢down (⊑∀ p⊢) (⊢Λν ⊢M)) β-cast∀ = ⊢Λν (⊢down p⊢ ⊢M) , wfΣ

preserve-ξ wfΣ p-if (⊢if ⊢L ⊢M ⊢N) s =
  let ⊢L′ , wfΣ′ = preserve wfΣ ⊢L s in
  ⊢if ⊢L′ (⊢-weaken-store (step-⊆ s) ⊢M) (⊢-weaken-store (step-⊆ s) ⊢N)
  , wfΣ′
preserve-ξ wfΣ p-□· (⊢· ⊢L ⊢M) s =
  let ⊢L′ , wfΣ′ = preserve wfΣ ⊢L s in
  ⊢· ⊢L′ (⊢-weaken-store (step-⊆ s) ⊢M) , wfΣ′
preserve-ξ wfΣ p-app (⊢· ⊢V ⊢M) s =
  let ⊢M′ , wfΣ′ = preserve wfΣ ⊢M s in
  ⊢· (⊢-weaken-store (step-⊆ s) ⊢V) ⊢M′ , wfΣ′
preserve-ξ wfΣ p-letv (⊢letv ⊢M ⊢N) s =
  let ⊢M′ , wfΣ′ = preserve wfΣ ⊢M s in
  ⊢letv ⊢M′ (⊢-weaken-store (step-⊆ s) ⊢N) , wfΣ′
preserve-ξ wfΣ p-seal (⊢seal nt ⊢M) s =
  let ⊢M′ , wfΣ′ = preserve wfΣ ⊢M s in
  ⊢seal (NameTy-weaken (step-⊆ s) nt) ⊢M′ , wfΣ′
preserve-ξ wfΣ p-unseal (⊢unseal nt ⊢M) s =
  let ⊢M′ , wfΣ′ = preserve wfΣ ⊢M s in
  ⊢unseal (NameTy-weaken (step-⊆ s) nt) ⊢M′ , wfΣ′
preserve-ξ wfΣ p-is (⊢is wfG ⊢M) s =
  let ⊢M′ , wfΣ′ = preserve wfΣ ⊢M s in
  ⊢is wfG ⊢M′ , wfΣ′
preserve-ξ wfΣ p-inj (⊢inj wfG ⊢M) s =
  let ⊢M′ , wfΣ′ = preserve wfΣ ⊢M s in
  ⊢inj wfG ⊢M′ , wfΣ′
preserve-ξ wfΣ p-cast (⊢up p⊢ ⊢M) s =
  let ⊢M′ , wfΣ′ = preserve wfΣ ⊢M s in
  ⊢up p⊢ ⊢M′ , wfΣ′
preserve-ξ wfΣ p-cast (⊢down p⊢ ⊢M) s =
  let ⊢M′ , wfΣ′ = preserve wfΣ ⊢M s in
  ⊢down p⊢ ⊢M′ , wfΣ′
preserve-ξ wfΣ p-inst (⊢inst ⊢M wfB ⊢N) s =
  let ⊢M′ , wfΣ′ = preserve wfΣ ⊢M s in
  ⊢inst ⊢M′ wfB (⊢-weaken-store (step-⊆ s) ⊢N) , wfΣ′
