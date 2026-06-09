module proof.CoercionProperties where

-- File Charter:
--   * Proof-only metatheory for GTSF coercion typing.
--   * Store membership transport, coercion weakening, and coercion type-renaming
--     lemmas used by term preservation.
--   * Term substitution/renaming lemmas belong in `proof.TermProperties`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; n≤1+n)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong₂; subst; sym; trans)

open import Types
open import Coercions
open import proof.TypeProperties

------------------------------------------------------------------------
-- Inert coercions
------------------------------------------------------------------------

renameᶜ-preserves-Inert :
  ∀ ρ {c} →
  Inert c →
  Inert (renameᶜ ρ c)
renameᶜ-preserves-Inert ρ (G !) = renameᵗ ρ G !
renameᶜ-preserves-Inert ρ (seal A α) = seal (renameᵗ ρ A) (ρ α)
renameᶜ-preserves-Inert ρ (c ↦ d) = renameᶜ ρ c ↦ renameᶜ ρ d
renameᶜ-preserves-Inert ρ (`∀ c) = `∀ (renameᶜ (extᵗ ρ) c)
renameᶜ-preserves-Inert ρ (gen A c) =
  gen (renameᵗ ρ A) (renameᶜ (extᵗ ρ) c)

------------------------------------------------------------------------
-- Store membership transport
------------------------------------------------------------------------

StoreIncl : Store → Store → Set
StoreIncl Σ Σ′ = ∀ {x} → x ∈ Σ → x ∈ Σ′

StoreIncl-refl :
  ∀ {Σ} →
  StoreIncl Σ Σ
StoreIncl-refl x∈ = x∈

StoreIncl-drop :
  ∀ {Σ α A} →
  StoreIncl Σ ((α , A) ∷ Σ)
StoreIncl-drop x∈ = there x∈

StoreIncl-cons :
  ∀ {Σ Σ′ x} →
  StoreIncl Σ Σ′ →
  StoreIncl (x ∷ Σ) (x ∷ Σ′)
StoreIncl-cons incl (here refl) = here refl
StoreIncl-cons incl (there x∈) = there (incl x∈)

∈-renameStoreᵗ :
  ∀ ρ {Σ α A} →
  (α , A) ∈ Σ →
  (ρ α , renameᵗ ρ A) ∈ renameStoreᵗ ρ Σ
∈-renameStoreᵗ ρ (here refl) = here refl
∈-renameStoreᵗ ρ (there x∈) = there (∈-renameStoreᵗ ρ x∈)

renameStoreᵗ-incl :
  ∀ ρ {Σ Σ′} →
  StoreIncl Σ Σ′ →
  StoreIncl (renameStoreᵗ ρ Σ) (renameStoreᵗ ρ Σ′)
renameStoreᵗ-incl ρ {Σ = []} incl ()
renameStoreᵗ-incl ρ {Σ = (α , A) ∷ Σ} incl (here refl) =
  ∈-renameStoreᵗ ρ (incl (here refl))
renameStoreᵗ-incl ρ {Σ = (α , A) ∷ Σ} incl (there x∈) =
  renameStoreᵗ-incl ρ (λ y∈ → incl (there y∈)) x∈

------------------------------------------------------------------------
-- Coercion typing under store/type-context weakening
------------------------------------------------------------------------

coercion-weaken :
  ∀ {Δ Δ′ Σ Σ′ c A B} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ′ ∣ Σ′ ⊢ c ∶ A =⇒ B
coercion-weaken Δ≤Δ′ incl (cast-id hA) =
  cast-id (WfTy-weakenᵗ hA Δ≤Δ′)
coercion-weaken Δ≤Δ′ incl (cast-seal hA α∈Σ) =
  cast-seal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
coercion-weaken Δ≤Δ′ incl (cast-unseal hA α∈Σ) =
  cast-unseal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
coercion-weaken Δ≤Δ′ incl (cast-seq c⊢ d⊢) =
  cast-seq (coercion-weaken Δ≤Δ′ incl c⊢)
           (coercion-weaken Δ≤Δ′ incl d⊢)
coercion-weaken Δ≤Δ′ incl (cast-tag hG gG) =
  cast-tag (WfTy-weakenᵗ hG Δ≤Δ′) gG
coercion-weaken Δ≤Δ′ incl (cast-untag hH gH) =
  cast-untag (WfTy-weakenᵗ hH Δ≤Δ′) gH
coercion-weaken Δ≤Δ′ incl (cast-fun c⊢ d⊢) =
  cast-fun (coercion-weaken Δ≤Δ′ incl c⊢)
           (coercion-weaken Δ≤Δ′ incl d⊢)
coercion-weaken Δ≤Δ′ incl (cast-all c⊢) =
  cast-all
    (coercion-weaken
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc incl)
      c⊢)
coercion-weaken Δ≤Δ′ incl (cast-inst hB c⊢) =
  cast-inst
    (WfTy-weakenᵗ hB Δ≤Δ′)
    (coercion-weaken
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl))
      c⊢)
coercion-weaken Δ≤Δ′ incl (cast-gen hA c⊢) =
  cast-gen
    (WfTy-weakenᵗ hA Δ≤Δ′)
    (coercion-weaken
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc incl)
      c⊢)

coercion-weaken-suc :
  ∀ {Δ Σ c A B α C} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , C) ∷ Σ ⊢ c ∶ A =⇒ B
coercion-weaken-suc {Δ = Δ} c⊢ =
  coercion-weaken (n≤1+n Δ) StoreIncl-drop c⊢

------------------------------------------------------------------------
-- Coercion typing under type renaming
------------------------------------------------------------------------

coercion-renameᵗ :
  ∀ {Δ Δ′ Σ c A B ρ} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ′ ∣ renameStoreᵗ ρ Σ ⊢ renameᶜ ρ c
    ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
coercion-renameᵗ hρ (cast-id hA) =
  cast-id (renameᵗ-preserves-WfTy hA hρ)
coercion-renameᵗ hρ (cast-seal hA α∈Σ) =
  cast-seal (renameᵗ-preserves-WfTy hA hρ)
            (∈-renameStoreᵗ _ α∈Σ)
coercion-renameᵗ hρ (cast-unseal hA α∈Σ) =
  cast-unseal (renameᵗ-preserves-WfTy hA hρ)
              (∈-renameStoreᵗ _ α∈Σ)
coercion-renameᵗ hρ (cast-seq c⊢ d⊢) =
  cast-seq (coercion-renameᵗ hρ c⊢)
           (coercion-renameᵗ hρ d⊢)
coercion-renameᵗ hρ (cast-tag hG gG) =
  cast-tag (renameᵗ-preserves-WfTy hG hρ) (renameᵗ-ground _ gG)
coercion-renameᵗ hρ (cast-untag hH gH) =
  cast-untag (renameᵗ-preserves-WfTy hH hρ) (renameᵗ-ground _ gH)
coercion-renameᵗ hρ (cast-fun c⊢ d⊢) =
  cast-fun (coercion-renameᵗ hρ c⊢)
           (coercion-renameᵗ hρ d⊢)
coercion-renameᵗ {ρ = ρ} hρ (cast-all c⊢) =
  cast-all
    (subst
      (λ Σ′ → _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
      (renameStoreᵗ-ext-suc-comm ρ _)
      (coercion-renameᵗ (TyRenameWf-ext hρ) c⊢))
coercion-renameᵗ {ρ = ρ} hρ (cast-inst {B = B} hB c⊢) =
  cast-inst
    (renameᵗ-preserves-WfTy hB hρ)
    (subst
      (λ T → _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ T)
      (renameᵗ-ext-suc-comm ρ B)
      (subst
        (λ Σ′ → _ ∣ (0 , ★) ∷ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗ (TyRenameWf-ext hρ) c⊢)))
coercion-renameᵗ {ρ = ρ} hρ (cast-gen {A = A} hA c⊢) =
  cast-gen
    (renameᵗ-preserves-WfTy hA hρ)
    (subst
      (λ T → _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _ ∶ T =⇒ _)
      (renameᵗ-ext-suc-comm ρ A)
      (subst
        (λ Σ′ → _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗ (TyRenameWf-ext hρ) c⊢)))

coercion-open :
  ∀ {Δ Σ c A B α C} →
  α < suc Δ →
  suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , C) ∷ Σ ⊢ c [ α ]ᶜ
    ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open {Σ = Σ} {α = α} α<sucΔ c⊢ =
  coercion-weaken ≤-refl StoreIncl-drop
    (subst
      (λ Σ′ → _ ∣ Σ′ ⊢ _ ∶ _ =⇒ _)
      (renameStoreᵗ-single-suc-cancel α Σ)
      (coercion-renameᵗ (singleRenameᵗ-Wf α<sucΔ) c⊢))

coercion-open-head :
  ∀ {Δ Σ c A B α C} →
  α < suc Δ →
  suc Δ ∣ (0 , C) ∷ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , renameᵗ (singleRenameᵗ α) C) ∷ Σ
    ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open-head
    {Δ = Δ} {Σ = Σ} {c = c} {A = A} {B = B} {α = α} α<sucΔ c⊢ =
  subst
    (λ Σ′ → suc Δ ∣ Σ′ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ)
    (cong₂ _∷_ refl (renameStoreᵗ-single-suc-cancel α Σ))
    (coercion-renameᵗ (singleRenameᵗ-Wf α<sucΔ) c⊢)

------------------------------------------------------------------------
-- Syntactic endpoints agree with typed endpoints
------------------------------------------------------------------------

coercion-src-tgt :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  src c ≡ A × tgt c ≡ B
coercion-src-tgt (cast-id hA) = refl , refl
coercion-src-tgt (cast-seal hA α∈Σ) = refl , refl
coercion-src-tgt (cast-unseal hA α∈Σ) = refl , refl
coercion-src-tgt (cast-seq c⊢ d⊢)
    with coercion-src-tgt c⊢ | coercion-src-tgt d⊢
coercion-src-tgt (cast-seq c⊢ d⊢)
    | src-c , tgt-c | src-d , tgt-d rewrite src-c | tgt-d =
  refl , refl
coercion-src-tgt (cast-tag hG gG) = refl , refl
coercion-src-tgt (cast-untag hH gH) = refl , refl
coercion-src-tgt (cast-fun c⊢ d⊢)
    with coercion-src-tgt c⊢ | coercion-src-tgt d⊢
coercion-src-tgt (cast-fun c⊢ d⊢)
    | src-c , tgt-c | src-d , tgt-d rewrite tgt-c | src-d | src-c | tgt-d =
  refl , refl
coercion-src-tgt (cast-all c⊢)
    with coercion-src-tgt c⊢
coercion-src-tgt (cast-all c⊢) | src-c , tgt-c rewrite src-c | tgt-c =
  refl , refl
coercion-src-tgt (cast-inst hB c⊢)
    with coercion-src-tgt c⊢
coercion-src-tgt (cast-inst hB c⊢) | src-c , tgt-c rewrite src-c =
  refl , refl
coercion-src-tgt (cast-gen hA c⊢)
    with coercion-src-tgt c⊢
coercion-src-tgt (cast-gen hA c⊢) | src-c , tgt-c rewrite tgt-c =
  refl , refl
