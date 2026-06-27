module proof.NuTermProperties where

-- File Charter:
--   * Proof-only metatheory for Nu GTSF terms.
--   * Context lookup through mapped contexts, value preservation, type-context
--     weakening, type renaming of typing derivations, and term substitution.
--   * Reduction-specific preservation cases belong in `proof.NuPreservation`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma as Sigma using (Σ; _,_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (zero; suc; _<_; _≤_; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; n≤1+n; <-≤-trans)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Ctx
open import Store
open import Coercions
open import Primitives
open import NuTerms
open import proof.TypeProperties
open import proof.StoreProperties
open import proof.CoercionProperties

------------------------------------------------------------------------
-- Context lookup under mapped contexts
------------------------------------------------------------------------

lookup-map-renameᵗ :
  ∀ {Γ x A ρ} →
  Γ ∋ x ⦂ A →
  map (renameᵗ ρ) Γ ∋ x ⦂ renameᵗ ρ A
lookup-map-renameᵗ Z = Z
lookup-map-renameᵗ (S h) = S (lookup-map-renameᵗ h)

lookup-map-inv :
  ∀ {Γ x} {B : Ty} {f : Ty → Ty} →
  map f Γ ∋ x ⦂ B →
  Sigma.Σ Ty (λ A → (Γ ∋ x ⦂ A) × (B ≡ f A))
lookup-map-inv {Γ = A ∷ Γ} {x = zero} Z = A , (Z , refl)
lookup-map-inv {Γ = A ∷ Γ} {x = suc x} (S h)
    with lookup-map-inv h
lookup-map-inv {Γ = A ∷ Γ} {x = suc x} (S h)
    | A′ , (hA′ , eq) = A′ , (S hA′ , eq)

lookup-⤊-elim :
  ∀ {Γ x B} {R : Set₁} →
  (∀ {A} → Γ ∋ x ⦂ A → B ≡ ⇑ᵗ A → R) →
  ⤊ᵗ Γ ∋ x ⦂ B →
  R
lookup-⤊-elim {Γ = []} k ()
lookup-⤊-elim {Γ = A ∷ Γ} {x = zero} k Z = k Z refl
lookup-⤊-elim {Γ = A ∷ Γ} {x = suc x} k (S h) =
  lookup-⤊-elim (λ hA eq → k (S hA) eq) h

lookup-⤊-elim₀ :
  ∀ {Γ x B} {R : Set} →
  (∀ {A} → Γ ∋ x ⦂ A → B ≡ ⇑ᵗ A → R) →
  ⤊ᵗ Γ ∋ x ⦂ B →
  R
lookup-⤊-elim₀ {Γ = []} k ()
lookup-⤊-elim₀ {Γ = A ∷ Γ} {x = zero} k Z = k Z refl
lookup-⤊-elim₀ {Γ = A ∷ Γ} {x = suc x} k (S h) =
  lookup-⤊-elim₀ (λ hA eq → k (S hA) eq) h

map-renameᵗ-⤊ :
  ∀ ρ Γ →
  map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ) ≡ ⤊ᵗ (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ ρ [] = refl
map-renameᵗ-⤊ ρ (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-ext-suc-comm ρ A) (map-renameᵗ-⤊ ρ Γ)

map-singleRenameᵗ-⤊-cancel :
  ∀ α Γ →
  map (renameᵗ (singleRenameᵗ α)) (⤊ᵗ Γ) ≡ Γ
map-singleRenameᵗ-⤊-cancel α [] = refl
map-singleRenameᵗ-⤊-cancel α (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-single-suc-cancel α A)
             (map-singleRenameᵗ-⤊-cancel α Γ)

renameStoreᵗ-ext-suc-cons-comm :
  ∀ ρ Σ A →
  renameStoreᵗ (extᵗ ρ) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ) ≡
  (zero , ⇑ᵗ (renameᵗ ρ A)) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
renameStoreᵗ-ext-suc-cons-comm ρ Σ A =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-ext-suc-comm ρ A))
    (renameStoreᵗ-ext-suc-comm ρ Σ)

renameStoreᵗ-single-suc-cons-cancel :
  ∀ α Σ A →
  renameStoreᵗ (singleRenameᵗ α) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ) ≡
  (α , A) ∷ Σ
renameStoreᵗ-single-suc-cons-cancel α Σ A =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-single-suc-cancel α A))
    (renameStoreᵗ-single-suc-cancel α Σ)

singleRenameᵗ-Wf-< :
  ∀ {Δ α} →
  α < Δ →
  TyRenameWf (suc Δ) Δ (singleRenameᵗ α)
singleRenameᵗ-Wf-< α<Δ {zero} z<s = α<Δ
singleRenameᵗ-Wf-< α<Δ {suc X} (s<s X<Δ) = X<Δ

rename-[]ᴿ-commute :
  ∀ ρ B α →
  renameᵗ ρ (B [ α ]ᴿ) ≡ renameᵗ (extᵗ ρ) B [ ρ α ]ᴿ
rename-[]ᴿ-commute ρ B α =
  trans (renameᵗ-compose (singleRenameᵗ α) ρ B)
    (trans
      (rename-cong env-eq B)
      (sym (renameᵗ-compose (extᵗ ρ) (singleRenameᵗ (ρ α)) B)))
  where
    env-eq :
      ∀ X →
      ρ (singleRenameᵗ α X) ≡ singleRenameᵗ (ρ α) (extᵗ ρ X)
    env-eq zero = refl
    env-eq (suc X) = refl

renameᵗᵐ-cong :
  ∀ {ρ ρ′} →
  (∀ X → ρ X ≡ ρ′ X) →
  ∀ M → renameᵗᵐ ρ M ≡ renameᵗᵐ ρ′ M
renameᵗᵐ-cong eq (` x) = refl
renameᵗᵐ-cong eq (ƛ M) = cong ƛ_ (renameᵗᵐ-cong eq M)
renameᵗᵐ-cong eq (L · M) =
  cong₂ _·_ (renameᵗᵐ-cong eq L) (renameᵗᵐ-cong eq M)
renameᵗᵐ-cong eq (Λ M) =
  cong Λ_ (renameᵗᵐ-cong ext-eq M)
  where
    ext-eq : ∀ X → extᵗ _ X ≡ extᵗ _ X
    ext-eq zero = refl
    ext-eq (suc X) = cong suc (eq X)
renameᵗᵐ-cong eq (M •) = cong _• (renameᵗᵐ-cong eq M)
renameᵗᵐ-cong {ρ = ρ} {ρ′ = ρ′} eq (ν A L c) =
  trans
    (cong₂ (λ A′ L′ → ν A′ L′ (renameᶜ (extᵗ ρ) c))
      (rename-cong eq A)
      (renameᵗᵐ-cong eq L))
    (cong (λ c′ → ν (renameᵗ ρ′ A) (renameᵗᵐ ρ′ L) c′)
      (renameᶜ-cong ext-eq c))
  where
    ext-eq : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
    ext-eq zero = refl
    ext-eq (suc X) = cong suc (eq X)
renameᵗᵐ-cong eq ($ κ) = refl
renameᵗᵐ-cong eq (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (renameᵗᵐ-cong eq L)
    (renameᵗᵐ-cong eq M)
renameᵗᵐ-cong {ρ = ρ} {ρ′ = ρ′} eq (M ⟨ c ⟩) =
  trans
    (cong (λ M′ → M′ ⟨ renameᶜ ρ c ⟩) (renameᵗᵐ-cong eq M))
    (cong (λ c′ → renameᵗᵐ ρ′ M ⟨ c′ ⟩) (renameᶜ-cong eq c))
renameᵗᵐ-cong eq blame = refl

renameᵗᵐ-compose :
  ∀ ρ τ M →
  renameᵗᵐ τ (renameᵗᵐ ρ M) ≡
    renameᵗᵐ (λ X → τ (ρ X)) M
renameᵗᵐ-compose ρ τ (` x) = refl
renameᵗᵐ-compose ρ τ (ƛ M) =
  cong ƛ_ (renameᵗᵐ-compose ρ τ M)
renameᵗᵐ-compose ρ τ (L · M) =
  cong₂ _·_ (renameᵗᵐ-compose ρ τ L) (renameᵗᵐ-compose ρ τ M)
renameᵗᵐ-compose ρ τ (Λ M) =
  cong Λ_
    (trans
      (renameᵗᵐ-compose (extᵗ ρ) (extᵗ τ) M)
      (renameᵗᵐ-cong (λ { zero → refl ; (suc X) → refl }) M))
renameᵗᵐ-compose ρ τ (M •) =
  cong _• (renameᵗᵐ-compose ρ τ M)
renameᵗᵐ-compose ρ τ (ν A L c) =
  trans
    (cong₂ (λ A′ L′ → ν A′ L′
      (renameᶜ (extᵗ τ) (renameᶜ (extᵗ ρ) c)))
      (renameᵗ-compose ρ τ A)
      (renameᵗᵐ-compose ρ τ L))
    (cong (λ c′ → ν (renameᵗ (λ X → τ (ρ X)) A)
      (renameᵗᵐ (λ X → τ (ρ X)) L) c′)
      (trans
        (renameᶜ-compose (extᵗ ρ) (extᵗ τ) c)
        (renameᶜ-cong (λ { zero → refl ; (suc X) → refl }) c)))
renameᵗᵐ-compose ρ τ ($ κ) = refl
renameᵗᵐ-compose ρ τ (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (renameᵗᵐ-compose ρ τ L)
    (renameᵗᵐ-compose ρ τ M)
renameᵗᵐ-compose ρ τ (M ⟨ c ⟩) =
  trans
    (cong (λ M′ → M′ ⟨ renameᶜ τ (renameᶜ ρ c) ⟩)
      (renameᵗᵐ-compose ρ τ M))
    (cong (λ c′ → renameᵗᵐ (λ X → τ (ρ X)) M ⟨ c′ ⟩)
      (renameᶜ-compose ρ τ c))
renameᵗᵐ-compose ρ τ blame = refl

renameᵗᵐ-left-inverse :
  ∀ {ρ ψ} →
  RenameLeftInverse ρ ψ →
  ∀ M →
  renameᵗᵐ ψ (renameᵗᵐ ρ M) ≡ M
renameᵗᵐ-left-inverse inv (` x) = refl
renameᵗᵐ-left-inverse inv (ƛ M) =
  cong ƛ_ (renameᵗᵐ-left-inverse inv M)
renameᵗᵐ-left-inverse inv (L · M) =
  cong₂ _·_ (renameᵗᵐ-left-inverse inv L)
             (renameᵗᵐ-left-inverse inv M)
renameᵗᵐ-left-inverse inv (Λ M) =
  cong Λ_ (renameᵗᵐ-left-inverse (RenameLeftInverse-ext inv) M)
renameᵗᵐ-left-inverse inv (M •) =
  cong _• (renameᵗᵐ-left-inverse inv M)
renameᵗᵐ-left-inverse inv (ν A L c) =
  trans
    (cong₂ (λ A′ L′ →
       ν A′ L′ (renameᶜ _ (renameᶜ _ c)))
      (renameᵗ-left-inverse inv A)
      (renameᵗᵐ-left-inverse inv L))
    (cong (ν A L) (renameᶜ-left-inverse (RenameLeftInverse-ext inv) c))
renameᵗᵐ-left-inverse inv ($ κ) = refl
renameᵗᵐ-left-inverse inv (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
        (renameᵗᵐ-left-inverse inv L)
        (renameᵗᵐ-left-inverse inv M)
renameᵗᵐ-left-inverse inv (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (renameᵗᵐ-left-inverse inv M)
              (renameᶜ-left-inverse inv c)
renameᵗᵐ-left-inverse inv blame = refl

open0-ext-suc-cancelᵐ :
  ∀ M →
  renameᵗᵐ (singleRenameᵗ zero) (renameᵗᵐ (extᵗ suc) M) ≡ M
open0-ext-suc-cancelᵐ = renameᵗᵐ-left-inverse open0-ext-suc-inv

renameᵗᵐ-pred-suc :
  ∀ M →
  renameᵗᵐ predᵗ (⇑ᵗᵐ M) ≡ M
renameᵗᵐ-pred-suc = renameᵗᵐ-left-inverse RenameLeftInverse-suc

renameᵗᵐ-pred-ext-suc :
  ∀ M →
  renameᵗᵐ predᵗ (renameᵗᵐ (extᵗ suc) M) ≡ M
renameᵗᵐ-pred-ext-suc =
  renameᵗᵐ-left-inverse RenameLeftInverse-ext-suc-pred

renameᵗᵐ-ext-suc-comm :
  ∀ ρ M →
  renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ M) ≡ ⇑ᵗᵐ (renameᵗᵐ ρ M)
renameᵗᵐ-ext-suc-comm ρ M =
  trans (renameᵗᵐ-compose suc (extᵗ ρ) M)
        (sym (renameᵗᵐ-compose ρ suc M))

renameᵗᵐ-open-commute :
  ∀ ρ M α →
  renameᵗᵐ ρ (M [ α ]ᵀ) ≡ renameᵗᵐ (extᵗ ρ) M [ ρ α ]ᵀ
renameᵗᵐ-open-commute ρ M α =
  trans (renameᵗᵐ-compose (singleRenameᵗ α) ρ M)
    (trans
      (renameᵗᵐ-cong env-eq M)
      (sym (renameᵗᵐ-compose (extᵗ ρ) (singleRenameᵗ (ρ α)) M)))
  where
    env-eq :
      ∀ X →
      ρ (singleRenameᵗ α X) ≡ singleRenameᵗ (ρ α) (extᵗ ρ X)
    env-eq zero = refl
    env-eq (suc X) = refl

WfTy-raise-inv :
  ∀ k {Δ A} →
  k ≤ Δ →
  WfTy (suc Δ) (renameᵗ (raiseVarFrom k) A) →
  WfTy Δ A
WfTy-raise-inv zero {A = ＇ X} k≤Δ (wfVar (s<s X<Δ)) = wfVar X<Δ
WfTy-raise-inv (suc k) {A = ＇ zero} (s≤s k≤Δ) (wfVar z<s) =
  wfVar z<s
WfTy-raise-inv (suc k) {A = ＇ suc X} (s≤s k≤Δ) (wfVar (s<s h))
    with WfTy-raise-inv k k≤Δ (wfVar h)
WfTy-raise-inv (suc k) {A = ＇ suc X} (s≤s k≤Δ) (wfVar (s<s h))
    | wfVar X<Δ =
  wfVar (s<s X<Δ)
WfTy-raise-inv k {A = ‵ ι} k≤Δ wfBase = wfBase
WfTy-raise-inv k {A = ★} k≤Δ wf★ = wf★
WfTy-raise-inv k {A = A ⇒ B} k≤Δ (wf⇒ hA hB) =
  wf⇒ (WfTy-raise-inv k k≤Δ hA) (WfTy-raise-inv k k≤Δ hB)
WfTy-raise-inv k {A = `∀ A} k≤Δ (wf∀ hA)
    rewrite rename-raise-ext k A =
  wf∀ (WfTy-raise-inv (suc k) (s≤s k≤Δ) hA)

------------------------------------------------------------------------
-- Context well-formedness
------------------------------------------------------------------------

CtxWf-weaken :
  ∀ {Δ Δ′ Γ} →
  CtxWf Δ Γ →
  Δ ≤ Δ′ →
  CtxWf Δ′ Γ
CtxWf-weaken hΓ Δ≤Δ′ h =
  WfTy-weakenᵗ (hΓ h) Δ≤Δ′

CtxWf-⤊ :
  ∀ {Δ Γ} →
  CtxWf Δ Γ →
  CtxWf (suc Δ) (⤊ᵗ Γ)
CtxWf-⤊ {Γ = []} hΓ ()
CtxWf-⤊ {Γ = A ∷ Γ} hΓ Z =
  renameᵗ-preserves-WfTy (hΓ Z) TyRenameWf-suc
CtxWf-⤊ {Γ = A ∷ Γ} hΓ (S h) =
  CtxWf-⤊ (λ hA → hΓ (S hA)) h

------------------------------------------------------------------------
-- Values under renaming and substitution
------------------------------------------------------------------------

renameᵗᵐ-preserves-Value :
  ∀ ρ {V} →
  Value V →
  Value (renameᵗᵐ ρ V)
renameᵗᵐ-preserves-Value ρ (ƛ N) = ƛ _
renameᵗᵐ-preserves-Value ρ (Λ vV) =
  Λ (renameᵗᵐ-preserves-Value (extᵗ ρ) vV)
renameᵗᵐ-preserves-Value ρ ($ κ) = $ κ
renameᵗᵐ-preserves-Value ρ (vV ⟨ i ⟩) =
  renameᵗᵐ-preserves-Value ρ vV ⟨ renameᶜ-preserves-Inert ρ i ⟩

renameˣᵐ-preserves-Value :
  ∀ ρ {V} →
  Value V →
  Value (renameˣᵐ ρ V)
renameˣᵐ-preserves-Value ρ (ƛ N) = ƛ _
renameˣᵐ-preserves-Value ρ (Λ vV) =
  Λ (renameˣᵐ-preserves-Value ρ vV)
renameˣᵐ-preserves-Value ρ ($ κ) = $ κ
renameˣᵐ-preserves-Value ρ (vV ⟨ i ⟩) =
  renameˣᵐ-preserves-Value ρ vV ⟨ i ⟩

substˣᵐ-preserves-Value :
  ∀ σ {V} →
  Value V →
  Value (substˣᵐ σ V)
substˣᵐ-preserves-Value σ (ƛ N) = ƛ _
substˣᵐ-preserves-Value σ (Λ vV) =
  Λ (substˣᵐ-preserves-Value (↑ᵗᵐ σ) vV)
substˣᵐ-preserves-Value σ ($ κ) = $ κ
substˣᵐ-preserves-Value σ (vV ⟨ i ⟩) =
  substˣᵐ-preserves-Value σ vV ⟨ i ⟩

renameˣ-renameᵗᵐ :
  ∀ ρ τ M →
  renameˣᵐ ρ (renameᵗᵐ τ M) ≡ renameᵗᵐ τ (renameˣᵐ ρ M)
renameˣ-renameᵗᵐ ρ τ (` x) = refl
renameˣ-renameᵗᵐ ρ τ (ƛ M) =
  cong ƛ_ (renameˣ-renameᵗᵐ (extʳ ρ) τ M)
renameˣ-renameᵗᵐ ρ τ (L · M) =
  cong₂ _·_ (renameˣ-renameᵗᵐ ρ τ L)
             (renameˣ-renameᵗᵐ ρ τ M)
renameˣ-renameᵗᵐ ρ τ (Λ M) =
  cong Λ_ (renameˣ-renameᵗᵐ ρ (extᵗ τ) M)
renameˣ-renameᵗᵐ ρ τ (M •) =
  cong _• (renameˣ-renameᵗᵐ ρ τ M)
renameˣ-renameᵗᵐ ρ τ (ν A L c) =
  cong (λ L′ → ν (renameᵗ τ A) L′ (renameᶜ (extᵗ τ) c))
       (renameˣ-renameᵗᵐ ρ τ L)
renameˣ-renameᵗᵐ ρ τ ($ κ) = refl
renameˣ-renameᵗᵐ ρ τ (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
        (renameˣ-renameᵗᵐ ρ τ L)
        (renameˣ-renameᵗᵐ ρ τ M)
renameˣ-renameᵗᵐ ρ τ (M ⟨ c ⟩) =
  cong (λ M′ → M′ ⟨ renameᶜ τ c ⟩) (renameˣ-renameᵗᵐ ρ τ M)
renameˣ-renameᵗᵐ ρ τ blame = refl

renameᵗᵐ-preserves-No• :
  ∀ ρ {M} →
  No• M →
  No• (renameᵗᵐ ρ M)
renameᵗᵐ-preserves-No• ρ no•-` = no•-`
renameᵗᵐ-preserves-No• ρ (no•-ƛ hM) =
  no•-ƛ (renameᵗᵐ-preserves-No• ρ hM)
renameᵗᵐ-preserves-No• ρ (no•-· hL hM) =
  no•-· (renameᵗᵐ-preserves-No• ρ hL)
        (renameᵗᵐ-preserves-No• ρ hM)
renameᵗᵐ-preserves-No• ρ (no•-Λ hM) =
  no•-Λ (renameᵗᵐ-preserves-No• (extᵗ ρ) hM)
renameᵗᵐ-preserves-No• ρ (no•-ν hL) =
  no•-ν (renameᵗᵐ-preserves-No• ρ hL)
renameᵗᵐ-preserves-No• ρ no•-$ = no•-$
renameᵗᵐ-preserves-No• ρ (no•-⊕ hL hM) =
  no•-⊕ (renameᵗᵐ-preserves-No• ρ hL)
         (renameᵗᵐ-preserves-No• ρ hM)
renameᵗᵐ-preserves-No• ρ (no•-⟨⟩ hM) =
  no•-⟨⟩ (renameᵗᵐ-preserves-No• ρ hM)
renameᵗᵐ-preserves-No• ρ no•-blame = no•-blame

renameˣᵐ-preserves-No• :
  ∀ ρ {M} →
  No• M →
  No• (renameˣᵐ ρ M)
renameˣᵐ-preserves-No• ρ no•-` = no•-`
renameˣᵐ-preserves-No• ρ (no•-ƛ hM) =
  no•-ƛ (renameˣᵐ-preserves-No• (extʳ ρ) hM)
renameˣᵐ-preserves-No• ρ (no•-· hL hM) =
  no•-· (renameˣᵐ-preserves-No• ρ hL)
        (renameˣᵐ-preserves-No• ρ hM)
renameˣᵐ-preserves-No• ρ (no•-Λ hM) =
  no•-Λ (renameˣᵐ-preserves-No• ρ hM)
renameˣᵐ-preserves-No• ρ (no•-ν hL) =
  no•-ν (renameˣᵐ-preserves-No• ρ hL)
renameˣᵐ-preserves-No• ρ no•-$ = no•-$
renameˣᵐ-preserves-No• ρ (no•-⊕ hL hM) =
  no•-⊕ (renameˣᵐ-preserves-No• ρ hL)
         (renameˣᵐ-preserves-No• ρ hM)
renameˣᵐ-preserves-No• ρ (no•-⟨⟩ hM) =
  no•-⟨⟩ (renameˣᵐ-preserves-No• ρ hM)
renameˣᵐ-preserves-No• ρ no•-blame = no•-blame

------------------------------------------------------------------------
-- Weakening over type-context and store growth
------------------------------------------------------------------------

term-weaken :
  ∀ {Δ Δ′ Σ Σ′ Γ M A} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Σ′ ∣ Γ ⊢ M ⦂ A
term-weaken Δ≤Δ′ incl no•-` (⊢` h) = ⊢` h
term-weaken Δ≤Δ′ incl (no•-ƛ noM) (⊢ƛ hA hM) =
  ⊢ƛ (WfTy-weakenᵗ hA Δ≤Δ′) (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-· noL noM) (⊢· hL hM) =
  ⊢· (term-weaken Δ≤Δ′ incl noL hL)
     (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-Λ noM) (⊢Λ vV hV) =
  ⊢Λ vV
    (term-weaken (s≤s Δ≤Δ′) (renameStoreᵗ-incl suc incl) noM hV)
term-weaken Δ≤Δ′ incl (no•-ν noL) (⊢ν hA hL c⊢) =
  ⊢ν
    (WfTy-weakenᵗ hA Δ≤Δ′)
    (term-weaken Δ≤Δ′ incl noL hL)
    (coercion-weakenᵐ
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl))
      c⊢)
term-weaken Δ≤Δ′ incl no•-$ (⊢$ κ) = ⊢$ κ
term-weaken Δ≤Δ′ incl (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  ⊢⊕ (term-weaken Δ≤Δ′ incl noL hL) op
      (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM) (⊢⟨⟩ c⊢ hM) =
  ⊢⟨⟩
    (coercion-weakenᵐ Δ≤Δ′ incl c⊢)
    (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl no•-blame (⊢blame hA) =
  ⊢blame (WfTy-weakenᵗ hA Δ≤Δ′)

term-weaken-suc :
  ∀ {Δ Σ Γ M A α C} →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  suc Δ ∣ (α , C) ∷ Σ ∣ Γ ⊢ M ⦂ A
term-weaken-suc {Δ = Δ} noM hM =
  term-weaken (n≤1+n Δ) StoreIncl-drop noM hM

------------------------------------------------------------------------
-- Renaming type variables in typing derivations
------------------------------------------------------------------------

modeRename-left-inverse :
  ∀ {ρ ψ μ} →
  RenameLeftInverse ρ ψ →
  ModeRename ρ μ (λ Y → μ (ψ Y))
modeRename-left-inverse {μ = μ} inv X rewrite inv X with μ X
modeRename-left-inverse inv X | id-only = refl
modeRename-left-inverse inv X | tag-or-id = refl
modeRename-left-inverse inv X | seal-or-id = refl

ModeRenamer : TyCtx → Renameᵗ → Set
ModeRenamer Δ ρ =
  ∀ μ → Sigma.Σ ModeEnv (λ target → ScopedModeRename Δ ρ μ target)

extModeᵈ : ModeEnv → ModeEnv → ModeEnv
extModeᵈ μ target zero = μ zero
extModeᵈ μ target (suc X) = target X

ModeRenamer-ext :
  ∀ {Δ ρ} →
  ModeRenamer Δ ρ →
  ModeRenamer (suc Δ) (extᵗ ρ)
ModeRenamer-ext {Δ = Δ} {ρ = ρ} η μ with η (λ X → μ (suc X))
ModeRenamer-ext {Δ = Δ} {ρ = ρ} η μ | target , rel =
  extModeᵈ μ target , rel′
  where
    rel′ : ScopedModeRename (suc Δ) (extᵗ ρ) μ (extModeᵈ μ target)
    rel′ {zero} z<s = modeIncl-refl {μ = μ} zero
    rel′ {suc X} (s<s X<Δ) = rel X<Δ

openModeRenamer :
  ∀ {Δ α} →
  Δ ≤ α →
  ModeRenamer (suc Δ) (singleRenameᵗ α)
openModeRenamer Δ≤α μ = openᵈ μ _ , openᵈ-scoped Δ≤α

typing-renameᵀ-scoped :
  ∀ {Δ Δ′ Σ Γ M A ρ} →
  StoreWfAt Δ Σ →
  CtxWf Δ Γ →
  TyRenameWf Δ Δ′ ρ →
  ModeRenamer Δ ρ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ renameStoreᵗ ρ Σ ∣ map (renameᵗ ρ) Γ
    ⊢ renameᵗᵐ ρ M ⦂ renameᵗ ρ A
typing-renameᵀ-scoped wfΣ hΓ hρ η no•-` (⊢` h) =
  ⊢` (lookup-map-renameᵗ h)
typing-renameᵀ-scoped wfΣ hΓ hρ η (no•-ƛ noM) (⊢ƛ hA hM) =
  ⊢ƛ (renameᵗ-preserves-WfTy hA hρ)
      (typing-renameᵀ-scoped
        wfΣ (ctxWf-∷ hA hΓ) hρ η noM hM)
typing-renameᵀ-scoped wfΣ hΓ hρ η (no•-· noL noM) (⊢· hL hM) =
  ⊢· (typing-renameᵀ-scoped wfΣ hΓ hρ η noL hL)
     (typing-renameᵀ-scoped wfΣ hΓ hρ η noM hM)
typing-renameᵀ-scoped {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    wfΣ hΓ hρ η (no•-Λ noM)
    (⊢Λ {M = M} {A = A} vM hM) =
  ⊢Λ
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vM)
    (subst
      (λ Γ′ → suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ) ∣ Γ′
        ⊢ renameᵗᵐ (extᵗ ρ) M ⦂ renameᵗ (extᵗ ρ) A)
      (map-renameᵗ-⤊ ρ Γ)
      (subst
        (λ Σ′ →
          suc Δ′ ∣ Σ′ ∣ map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ)
          ⊢ renameᵗᵐ (extᵗ ρ) M ⦂ renameᵗ (extᵗ ρ) A)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (typing-renameᵀ-scoped
          (StoreWfAt-⟰ᵗ wfΣ)
          (CtxWf-⤊ hΓ)
          (TyRenameWf-ext hρ)
          (ModeRenamer-ext η)
          noM
          hM)))
typing-renameᵀ-scoped {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    wfΣ hΓ hρ η
    (no•-ν noL)
    (⊢ν {L = L} {A = A} {B = B} {C = C} {c = c} {μ = μ}
      hA hL c⊢)
    with ModeRenamer-ext η μ
typing-renameᵀ-scoped {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    wfΣ hΓ hρ η
    (no•-ν noL)
    (⊢ν {L = L} {A = A} {B = B} {C = C} {c = c} {μ = μ}
      hA hL c⊢)
    | target , rel =
  ⊢ν {μ = target}
    (renameᵗ-preserves-WfTy hA hρ)
    (typing-renameᵀ-scoped wfΣ hΓ hρ η noL hL)
    (subst
      (λ T →
        target ∣ suc Δ′
          ∣ (zero , ⇑ᵗ (renameᵗ ρ A)) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) C =⇒ T)
      (renameᵗ-ext-suc-comm ρ B)
      (subst
        (λ Σ′ →
          target ∣ suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) c
            ∶ renameᵗ (extᵗ ρ) C =⇒ renameᵗ (extᵗ ρ) (⇑ᵗ B))
        (renameStoreᵗ-ext-suc-cons-comm ρ Σ A)
        (coercion-renameᵗᵐ-scoped
          (StoreWfAt-cons
            z<s
            (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
            (StoreWfAt-⟰ᵗ wfΣ))
          (TyRenameWf-ext hρ)
          rel
          c⊢)))
typing-renameᵀ-scoped {ρ = ρ} wfΣ hΓ hρ η no•-$ (⊢$ κ) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ $ κ ⦂ T)
        (constTy-renameᵗ ρ κ)
        (⊢$ κ)
typing-renameᵀ-scoped wfΣ hΓ hρ η (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  ⊢⊕ (typing-renameᵀ-scoped wfΣ hΓ hρ η noL hL) op
      (typing-renameᵀ-scoped wfΣ hΓ hρ η noM hM)
typing-renameᵀ-scoped {ρ = ρ} wfΣ hΓ hρ η
    (no•-⟨⟩ noM)
    (⊢⟨⟩ {μ = μ} c⊢ hM)
    with η μ
typing-renameᵀ-scoped {ρ = ρ} wfΣ hΓ hρ η
    (no•-⟨⟩ noM)
    (⊢⟨⟩ {μ = μ} c⊢ hM)
    | target , rel =
  ⊢⟨⟩ {μ = target}
    (coercion-renameᵗᵐ-scoped wfΣ hρ rel c⊢)
    (typing-renameᵀ-scoped wfΣ hΓ hρ η noM hM)
typing-renameᵀ-scoped wfΣ hΓ hρ η no•-blame (⊢blame hA) =
  ⊢blame (renameᵗ-preserves-WfTy hA hρ)

typing-open-freshᵀ :
  ∀ {Δ Δ′ Σ Γ M A α C} →
  StoreWfAt Δ Σ →
  CtxWf Δ Γ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  No• M →
  suc Δ ∣ ⟰ᵗ Σ ∣ ⤊ᵗ Γ ⊢ M ⦂ A →
  Δ′ ∣ (α , C) ∷ Σ ∣ Γ ⊢ M [ α ]ᵀ ⦂ A [ α ]ᴿ
typing-open-freshᵀ {Σ = Σ} {Γ = Γ} {M = M} {A = A} {α = α}
    {C = C} wfΣ hΓ Δ≤Δ′ Δ≤α α<Δ′ noM M⊢ =
  term-weaken ≤-refl StoreIncl-drop
    (renameᵗᵐ-preserves-No• (singleRenameᵗ α) noM)
    (subst
      (λ Γ′ → _ ∣ Σ ∣ Γ′ ⊢ M [ α ]ᵀ ⦂ A [ α ]ᴿ)
      (map-singleRenameᵗ-⤊-cancel α Γ)
      (subst
        (λ Σ′ → _ ∣ Σ′ ∣ map (renameᵗ (singleRenameᵗ α)) (⤊ᵗ Γ)
          ⊢ M [ α ]ᵀ ⦂ A [ α ]ᴿ)
        (renameStoreᵗ-single-suc-cancel α Σ)
        (typing-renameᵀ-scoped
          (StoreWfAt-⟰ᵗ wfΣ)
          (CtxWf-⤊ hΓ)
          (singleRenameᵗ-Wf≤ Δ≤Δ′ α<Δ′)
          (openModeRenamer Δ≤α)
          noM
          M⊢)))

typing-renameᵀ :
  ∀ {Δ Δ′ Σ Γ M A ρ ψ} →
  TyRenameWf Δ Δ′ ρ →
  RenameLeftInverse ρ ψ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ renameStoreᵗ ρ Σ ∣ map (renameᵗ ρ) Γ
    ⊢ renameᵗᵐ ρ M ⦂ renameᵗ ρ A
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv no•-` (⊢` h) =
  ⊢` (lookup-map-renameᵗ h)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv (no•-ƛ noM) (⊢ƛ hA hM) =
  ⊢ƛ (renameᵗ-preserves-WfTy hA hρ)
      (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv
    (no•-· noL noM) (⊢· hL hM) =
  ⊢· (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv noL hL)
     (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv noM hM)
typing-renameᵀ {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    {ψ = ψ} hρ inv (no•-Λ noM)
    (⊢Λ {M = M} {A = A} vM hM) =
  ⊢Λ
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vM)
    (subst
      (λ Γ′ → suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ) ∣ Γ′
        ⊢ renameᵗᵐ (extᵗ ρ) M ⦂ renameᵗ (extᵗ ρ) A)
      (map-renameᵗ-⤊ ρ Γ)
      (subst
        (λ Σ′ →
          suc Δ′ ∣ Σ′ ∣ map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ)
          ⊢ renameᵗᵐ (extᵗ ρ) M ⦂ renameᵗ (extᵗ ρ) A)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (typing-renameᵀ
          {ρ = extᵗ ρ} {ψ = extᵗ ψ}
          (TyRenameWf-ext hρ)
          (RenameLeftInverse-ext inv)
          noM
          hM)))
typing-renameᵀ {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    {ψ = ψ} hρ inv
    (no•-ν noL)
    (⊢ν {L = L} {A = A} {B = B} {C = C} {c = c} {μ = μ}
      hA hL c⊢) =
  ⊢ν {μ = λ Y → μ (extᵗ ψ Y)}
    (renameᵗ-preserves-WfTy hA hρ)
    (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv noL hL)
    (subst
      (λ T →
        (λ Y → μ (extᵗ ψ Y)) ∣ suc Δ′
          ∣ (zero , ⇑ᵗ (renameᵗ ρ A)) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) C =⇒ T)
      (renameᵗ-ext-suc-comm ρ B)
      (subst
        (λ Σ′ →
          (λ Y → μ (extᵗ ψ Y)) ∣ suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) c
            ∶ renameᵗ (extᵗ ρ) C =⇒ renameᵗ (extᵗ ρ) (⇑ᵗ B))
        (renameStoreᵗ-ext-suc-cons-comm ρ Σ A)
        (coercion-renameᵗᵐ (TyRenameWf-ext hρ)
          (modeRename-left-inverse
            {ρ = extᵗ ρ} {ψ = extᵗ ψ} (RenameLeftInverse-ext inv))
          c⊢)))
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv no•-$ (⊢$ κ) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ $ κ ⦂ T)
        (constTy-renameᵗ ρ κ)
        (⊢$ κ)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv
    (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  ⊢⊕ (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv noL hL) op
      (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv
    (no•-⟨⟩ noM) (⊢⟨⟩ {μ = μ} c⊢ hM) =
  ⊢⟨⟩ {μ = λ Y → μ (ψ Y)}
        (coercion-renameᵗᵐ hρ
          (modeRename-left-inverse {ρ = ρ} {ψ = ψ} inv) c⊢)
        (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv no•-blame (⊢blame hA) =
  ⊢blame (renameᵗ-preserves-WfTy hA hρ)

-- The old unrestricted opening lemmas used `singleRenameᵗ`, which is
-- non-injective.  They are intentionally on hold until the preservation proof
-- can pass the freshness invariant from `ν-step` into freshness-indexed
-- opening lemmas.

------------------------------------------------------------------------
-- Typing derivations produce well-formed result types
------------------------------------------------------------------------

constTy-wf :
  ∀ {Δ} κ →
  WfTy Δ (constTy κ)
constTy-wf (κℕ n) = wfBase

typing-wf :
  ∀ {Δ Σ Γ M A} →
  StoreWfAt Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  WfTy Δ A
typing-wf wfΣ hΓ (⊢` h) = hΓ h
typing-wf wfΣ hΓ (⊢ƛ hA hM) =
  wf⇒ hA (typing-wf wfΣ (ctxWf-∷ hA hΓ) hM)
typing-wf wfΣ hΓ (⊢· hL hM) with typing-wf wfΣ hΓ hL
typing-wf wfΣ hΓ (⊢· hL hM) | wf⇒ hA hB = hB
typing-wf wfΣ hΓ (⊢Λ vM hM) =
  wf∀ (typing-wf (StoreWfAt-⟰ᵗ wfΣ) (CtxWf-⤊ hΓ) hM)
typing-wf wfΣ hΓ (⊢• {C = C} refl refl hC vV noV hV) =
  hC
typing-wf wfΣ hΓ (⊢ν hA hL c⊢)
    with coercion-wfᵐ
      (StoreWfAt-cons
        z<s
        (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
        (StoreWfAt-⟰ᵗ wfΣ))
      c⊢
typing-wf wfΣ hΓ (⊢ν hA hL c⊢) | hC , hB =
  WfTy-raise-inv zero z≤n hB
typing-wf wfΣ hΓ (⊢$ κ) = constTy-wf κ
typing-wf wfΣ hΓ (⊢⊕ hL op hM) = wfBase
typing-wf wfΣ hΓ (⊢⟨⟩ c⊢ hM) with coercion-wfᵐ wfΣ c⊢
typing-wf wfΣ hΓ (⊢⟨⟩ c⊢ hM) | hA , hB = hB
typing-wf wfΣ hΓ (⊢blame hA) = hA

------------------------------------------------------------------------
-- Renaming and substituting term variables
------------------------------------------------------------------------

RenameWf : Ctx → Ctx → Renameˣ → Set₁
RenameWf Γ Γ′ ρ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A

SubstWf : TyCtx → Store → Ctx → Ctx → Substˣ → Set₁
SubstWf Δ Σ Γ Γ′ σ =
  ∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Σ ∣ Γ′ ⊢ σ x ⦂ A

SubstNo• : Ctx → Substˣ → Set₁
SubstNo• Γ σ = ∀ {x A} → Γ ∋ x ⦂ A → No• (σ x)

RenameWf-ext :
  ∀ {Γ Γ′ B ρ} →
  RenameWf Γ Γ′ ρ →
  RenameWf (B ∷ Γ) (B ∷ Γ′) (extʳ ρ)
RenameWf-ext hρ Z = Z
RenameWf-ext hρ (S h) = S (hρ h)

RenameWf-⤊ :
  ∀ {Γ Γ′ ρ} →
  RenameWf Γ Γ′ ρ →
  RenameWf (⤊ᵗ Γ) (⤊ᵗ Γ′) ρ
RenameWf-⤊ hρ h =
  lookup-⤊-elim
    (λ hA eq →
      subst (λ T → _ ∋ _ ⦂ T) (sym eq) (lookup-map-renameᵗ (hρ hA)))
    h

typing-renameˣ :
  ∀ {Δ Σ Γ Γ′ M A ρ} →
  RenameWf Γ Γ′ ρ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ Γ′ ⊢ renameˣᵐ ρ M ⦂ A
typing-renameˣ hρ (⊢` h) = ⊢` (hρ h)
typing-renameˣ hρ (⊢ƛ hA hM) =
  ⊢ƛ hA (typing-renameˣ (RenameWf-ext hρ) hM)
typing-renameˣ hρ (⊢· hL hM) =
  ⊢· (typing-renameˣ hρ hL) (typing-renameˣ hρ hM)
typing-renameˣ {Γ = Γ} {Γ′ = Γ′} {ρ = ρ} hρ
    (⊢Λ vM hM) =
  ⊢Λ (renameˣᵐ-preserves-Value ρ vM)
    (typing-renameˣ (RenameWf-⤊ hρ) hM)
typing-renameˣ {ρ = ρ} hρ (⊢• {V = V} eqΔ eqΣ hC vV noV hV) =
  subst
    (λ M → _ ∣ _ ∣ _ ⊢ M • ⦂ _)
    (sym (renameˣ-renameᵗᵐ ρ suc V))
    (⊢• eqΔ eqΣ hC
        (renameˣᵐ-preserves-Value ρ vV)
        (renameˣᵐ-preserves-No• ρ noV)
        (typing-renameˣ hρ hV))
typing-renameˣ hρ (⊢ν hA hL c⊢) =
  ⊢ν hA (typing-renameˣ hρ hL) c⊢
typing-renameˣ hρ (⊢$ κ) = ⊢$ κ
typing-renameˣ hρ (⊢⊕ hL op hM) =
  ⊢⊕ (typing-renameˣ hρ hL) op (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢⟨⟩ c⊢ hM) =
  ⊢⟨⟩ c⊢ (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢blame hA) = ⊢blame hA

typing-renameˣ-shift :
  ∀ {Δ Σ Γ M A B} →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ (B ∷ Γ) ⊢ renameˣᵐ suc M ⦂ A
typing-renameˣ-shift hM =
  typing-renameˣ (λ h → S h) hM

SubstWf-exts :
  ∀ {Δ Σ Γ Γ′ B σ} →
  SubstWf Δ Σ Γ Γ′ σ →
  SubstWf Δ Σ (B ∷ Γ) (B ∷ Γ′) (extˢˣ σ)
SubstWf-exts hσ Z = ⊢` Z
SubstWf-exts hσ (S h) = typing-renameˣ-shift (hσ h)

SubstNo•-exts :
  ∀ {Γ B σ} →
  SubstNo• Γ σ →
  SubstNo• (B ∷ Γ) (extˢˣ σ)
SubstNo•-exts hσ Z = no•-`
SubstNo•-exts hσ (S h) = renameˣᵐ-preserves-No• suc (hσ h)

SubstNo•-⇑ :
  ∀ {Γ σ} →
  SubstNo• Γ σ →
  SubstNo• (⤊ᵗ Γ) (↑ᵗᵐ σ)
SubstNo•-⇑ hσ h =
  lookup-⤊-elim₀
    (λ hA eq → renameᵗᵐ-preserves-No• suc (hσ hA))
    h

SubstWf-⇑ :
  ∀ {Δ Σ Γ Γ′ σ} →
  SubstWf Δ Σ Γ Γ′ σ →
  SubstNo• Γ σ →
  SubstWf (suc Δ) (⟰ᵗ Σ) (⤊ᵗ Γ) (⤊ᵗ Γ′) (↑ᵗᵐ σ)
SubstWf-⇑ hσ noσ h =
  lookup-⤊-elim
    (λ hA eq →
      subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
            (sym eq)
            (typing-renameᵀ {ρ = suc} {ψ = predᵗ}
              TyRenameWf-suc RenameLeftInverse-suc (noσ hA) (hσ hA)))
    h

SubstWf-⇑ν :
  ∀ {Δ Σ Γ Γ′ σ A} →
  SubstWf Δ Σ Γ Γ′ σ →
  SubstNo• Γ σ →
  SubstWf
    (suc Δ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
    (⤊ᵗ Γ)
    (⤊ᵗ Γ′)
    (↑ᵗᵐ σ)
SubstWf-⇑ν hσ noσ h =
  lookup-⤊-elim
    (λ hA eq →
      subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
            (sym eq)
            (term-weaken ≤-refl StoreIncl-drop
              (renameᵗᵐ-preserves-No• suc (noσ hA))
              (typing-renameᵀ {ρ = suc} {ψ = predᵗ}
                TyRenameWf-suc RenameLeftInverse-suc
                (noσ hA)
                (hσ hA))))
    h

substˣᵐ-preserves-No•-typed :
  ∀ {Δ Σ Γ M A σ} →
  SubstNo• Γ σ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  No• (substˣᵐ σ M)
substˣᵐ-preserves-No•-typed noσ no•-` (⊢` h) = noσ h
substˣᵐ-preserves-No•-typed noσ (no•-ƛ noM) (⊢ƛ hA hM) =
  no•-ƛ (substˣᵐ-preserves-No•-typed (SubstNo•-exts noσ) noM hM)
substˣᵐ-preserves-No•-typed noσ (no•-· noL noM) (⊢· hL hM) =
  no•-· (substˣᵐ-preserves-No•-typed noσ noL hL)
        (substˣᵐ-preserves-No•-typed noσ noM hM)
substˣᵐ-preserves-No•-typed noσ (no•-Λ noM) (⊢Λ vM hM) =
  no•-Λ
    (substˣᵐ-preserves-No•-typed (SubstNo•-⇑ noσ) noM hM)
substˣᵐ-preserves-No•-typed noσ (no•-ν noL) (⊢ν hA hL c⊢) =
  no•-ν (substˣᵐ-preserves-No•-typed noσ noL hL)
substˣᵐ-preserves-No•-typed noσ no•-$ (⊢$ κ) = no•-$
substˣᵐ-preserves-No•-typed noσ (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  no•-⊕ (substˣᵐ-preserves-No•-typed noσ noL hL)
         (substˣᵐ-preserves-No•-typed noσ noM hM)
substˣᵐ-preserves-No•-typed noσ (no•-⟨⟩ noM) (⊢⟨⟩ c⊢ hM) =
  no•-⟨⟩ (substˣᵐ-preserves-No•-typed noσ noM hM)
substˣᵐ-preserves-No•-typed noσ no•-blame (⊢blame hA) = no•-blame

typing-substˣ :
  ∀ {Δ Σ Γ Γ′ M A σ} →
  SubstWf Δ Σ Γ Γ′ σ →
  SubstNo• Γ σ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ Γ′ ⊢ substˣᵐ σ M ⦂ A
typing-substˣ hσ noσ no•-` (⊢` h) = hσ h
typing-substˣ hσ noσ (no•-ƛ noM) (⊢ƛ hA hM) =
  ⊢ƛ hA (typing-substˣ (SubstWf-exts hσ) (SubstNo•-exts noσ) noM hM)
typing-substˣ hσ noσ (no•-· noL noM) (⊢· hL hM) =
  ⊢· (typing-substˣ hσ noσ noL hL)
     (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-Λ noM) (⊢Λ vM hM) =
  ⊢Λ (substˣᵐ-preserves-Value _ vM)
    (typing-substˣ
      (SubstWf-⇑ hσ noσ)
      (SubstNo•-⇑ noσ)
      noM
      hM)
typing-substˣ hσ noσ (no•-ν noL) (⊢ν hA hL c⊢) =
  ⊢ν hA (typing-substˣ hσ noσ noL hL) c⊢
typing-substˣ hσ noσ no•-$ (⊢$ κ) = ⊢$ κ
typing-substˣ hσ noσ (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  ⊢⊕ (typing-substˣ hσ noσ noL hL) op
      (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-⟨⟩ noM) (⊢⟨⟩ c⊢ hM) =
  ⊢⟨⟩ c⊢ (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ no•-blame (⊢blame hA) = ⊢blame hA

singleSubstWf :
  ∀ {Δ Σ Γ A V} →
  Δ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  SubstWf Δ Σ (A ∷ Γ) Γ (singleEnv V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢` h

singleSubstNo• :
  ∀ {Γ A V} →
  No• V →
  SubstNo• (A ∷ Γ) (singleEnv V)
singleSubstNo• noV Z = noV
singleSubstNo• noV (S h) = no•-`

typing-single-subst :
  ∀ {Δ Σ Γ N V A B} →
  No• N →
  No• V →
  Δ ∣ Σ ∣ (A ∷ Γ) ⊢ N ⦂ B →
  Δ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  Δ ∣ Σ ∣ Γ ⊢ N [ V ] ⦂ B
typing-single-subst noN noV hN hV =
  typing-substˣ (singleSubstWf hV) (singleSubstNo• noV) noN hN
