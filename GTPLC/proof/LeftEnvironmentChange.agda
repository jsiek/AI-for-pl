module proof.LeftEnvironmentChange where

-- File Charter:
--   * Relates narrowing environments across source-side store changes.
--   * Proves left-only relocation and type-store shifting locally.
--   * Records the keep and dynamic-instantiation changes used by casts.

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat using (suc; zero; z<s; s≤s)
open import Data.Product using (_,_; proj₁; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)

open import Types
open import TyStore
open import Coercions
open import Terms using (Term; _⟨_⟩)
open import Reduction
open import TypeRelocate
open import NarrowWiden
open import EnvironmentNarrowing
open import proof.ImprecisionRenaming using (renameⁿ; renameʷ)
open import proof.ImprecisionComposition using
  (weaken-storeⁿ; weaken-storeʷ)
open import proof.TypeInCoercionSubst using
  (ModeRename; renameᶜ-preserves-Inert)
open import proof.TypeInTypeSubst using
  ( RenameLeftInverse
  ; RenameLeftInverse-ext
  ; RenameLeftInverse-suc
  ; TyRenameWf
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; renameᵗ-id
  ; renameᵗ-preserves-WfTy
  ; predᵗ
  )
open import proof.TyStore using (∈-renameTyStoreᵗ)

------------------------------------------------------------------------
-- Left-side store changes
------------------------------------------------------------------------

leftChangesᵢ : (χs : StoreChanges) → ∀ {Δᴸ Δᴿ}
  → ImpCtx Δᴸ Δᴿ
  → ImpCtx (χs ▶ᵈ Δᴸ) Δᴿ
leftChangesᵢ [] Φ = Φ
leftChangesᵢ (keep ∷ χs) Φ = leftChangesᵢ χs Φ
leftChangesᵢ (bind A ∷ χs) Φ = leftChangesᵢ χs (freshᴸ Φ)

syntax leftChangesᵢ χs Φ = χs ▶ᵢ Φ

leftChangesᶜ : StoreChanges → Coercion → Coercion
leftChangesᶜ [] c = c
leftChangesᶜ (χ ∷ χs) c = leftChangesᶜ χs (changeᶜ χ c)

syntax leftChangesᶜ χs c = χs ▶ᶜ c

cast-trace : ∀ {M N c χs}
  → M —↠[ χs ] N
  → M ⟨ c ⟩ —↠[ χs ] N ⟨ χs ▶ᶜ c ⟩
cast-trace ↠-refl = ↠-refl
cast-trace (↠-step M→N N—↠P) =
  ↠-step (ξ-⟨⟩ M→N) (cast-trace N—↠P)

leftChanges-preserves-Inert : ∀ χs {c}
  → Inert c
  → Inert (χs ▶ᶜ c)
leftChanges-preserves-Inert [] i = i
leftChanges-preserves-Inert (keep ∷ χs) i =
  leftChanges-preserves-Inert χs i
leftChanges-preserves-Inert (bind A ∷ χs) i =
  leftChanges-preserves-Inert χs (renameᶜ-preserves-Inert suc i)

------------------------------------------------------------------------
-- Relocation under a left-only shift
------------------------------------------------------------------------

private

  record RenameRelocation
      {Δᴸ Δᴿ Δᴸ′ Δᴿ′}
      (ρᴸ ρᴿ : Renameᵗ)
      (Φ : ImpCtx Δᴸ Δᴿ)
      (Ψ : ImpCtx Δᴸ′ Δᴿ′) : Set where
    constructor rename-relocation
    field
      left-wfᵣ : TyRenameWf Δᴸ Δᴸ′ ρᴸ
      right-wfᵣ : TyRenameWf Δᴿ Δᴿ′ ρᴿ
      pairedᵣ : ∀ {X Y}
        → Φ ⊢ X ≈ˣ Y
        → Ψ ⊢ ρᴸ X ≈ˣ ρᴿ Y

  open RenameRelocation

  bothᵣ : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameRelocation ρᴸ ρᴿ Φ Ψ
    → RenameRelocation (extᵗ ρᴸ) (extᵗ ρᴿ)
        (bothᵢ Φ) (bothᵢ Ψ)
  bothᵣ (rename-relocation hᴸ hᴿ paired) =
    rename-relocation (TyRenameWf-ext hᴸ) (TyRenameWf-ext hᴿ)
      both-paired
    where
    both-paired : ∀ {X Y}
      → bothᵢ _ ⊢ X ≈ˣ Y
      → bothᵢ _ ⊢ extᵗ _ X ≈ˣ extᵗ _ Y
    both-paired hereᵢ = hereᵢ
    both-paired (both-thereᵢ X≈Y) = both-thereᵢ (paired X≈Y)

  rename-relocation-type :
      ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ A B}
        {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameRelocation ρᴸ ρᴿ Φ Ψ
    → Φ ⊢ A ≈ B
    → Ψ ⊢ renameᵗ ρᴸ A ≈ renameᵗ ρᴿ B
  rename-relocation-type r
      (idᵃ (＇ X) (＇ Y) hX hY (varᵃ X≈Y)) =
    idᵃ (＇ _) (＇ _)
      (renameᵗ-preserves-WfTy hX (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hY (right-wfᵣ r))
      (varᵃ (pairedᵣ r X≈Y))
  rename-relocation-type r (idᵃ (‵ ι) (‵ .ι) hι hι′ baseᵃ) =
    idᵃ (‵ ι) (‵ ι)
      (renameᵗ-preserves-WfTy hι (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hι′ (right-wfᵣ r)) baseᵃ
  rename-relocation-type r (idᵃ ★ ★ h★ h★′ starᵃ) =
    idᵃ ★ ★
      (renameᵗ-preserves-WfTy h★ (left-wfᵣ r))
      (renameᵗ-preserves-WfTy h★′ (right-wfᵣ r)) starᵃ
  rename-relocation-type r (p ⇒ʳ q) =
    rename-relocation-type r p ⇒ʳ rename-relocation-type r q
  rename-relocation-type r (∀ʳ p) =
    ∀ʳ (rename-relocation-type (bothᵣ r) p)

  left-shiftᵣ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → RenameRelocation suc (λ X → X) Φ (freshᴸ Φ)
  left-shiftᵣ =
    rename-relocation TyRenameWf-suc (λ X<Δ → X<Δ)
      freshᴸ-thereᵢ

⇑ᴸʳ : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ≈ B
  → freshᴸ Φ ⊢ ⇑ᵗ A ≈ B
⇑ᴸʳ {A = A} {B = B} {Φ = Φ} p =
  subst (λ B′ → freshᴸ Φ ⊢ ⇑ᵗ A ≈ B′)
    (renameᵗ-id B) (rename-relocation-type left-shiftᵣ p)

------------------------------------------------------------------------
-- Type-store and environment extension on the left
------------------------------------------------------------------------

⇑ᴸˢ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
  → freshᴸ Φ ∣ suc Δᴸ ⊢ ⟰ᵗ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
⇑ᴸˢ []ˢ = []ˢ
⇑ᴸˢ (bothˢ X≈Y p σ) =
  bothˢ (freshᴸ-thereᵢ X≈Y) (⇑ᴸʳ p) (⇑ᴸˢ σ)
⇑ᴸˢ (leftˢ X<Δ σ) = leftˢ (s≤s X<Δ) (⇑ᴸˢ σ)
⇑ᴸˢ (rightˢ Yᴿ hB σ) =
  rightˢ (freshᴸ-thereᴿ Yᴿ) hB (⇑ᴸˢ σ)

bind-leftᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}
  → NarrowingEnv (freshᴸ Φ)
      {(zero , ★) ∷ ⟰ᵗ Σᴸ} {Σᴿ} {[]} {[]}
bind-leftᵉ (env μᴸ σ μᴿ []ᵍ) =
  env (instᵈ μᴸ) (leftˢ z<s (⇑ᴸˢ σ)) μᴿ []ᵍ

------------------------------------------------------------------------
-- Evidence for a sequence of left environment changes
------------------------------------------------------------------------

data LeftEnvChange
    {Δᴸ Δᴿ Σᴸ Σᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    (ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}) :
    (χs : StoreChanges)
    → NarrowingEnv (χs ▶ᵢ Φ)
        {χs ▶ˢ Σᴸ} {Σᴿ} {[]} {[]}
    → Set₁ where

  left-done : LeftEnvChange ρ [] ρ

  left-keep : ∀ {χs ρ′}
    → LeftEnvChange ρ χs ρ′
    → LeftEnvChange ρ (keep ∷ χs) ρ′

  left-bind : ∀ {χs ρ′}
    → LeftEnvChange (bind-leftᵉ ρ) χs ρ′
    → LeftEnvChange ρ (bind ★ ∷ χs) ρ′

------------------------------------------------------------------------
-- Narrowing and widening transport through the recorded changes
------------------------------------------------------------------------

left-shift-modeⁿ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
      ⊢ ⇑ᵗ A ⊒ ⇑ᵗ B
left-shift-modeⁿ (c , c⊒) =
  ⇑ᶜ c , weaken-storeⁿ add-head
    (renameⁿ suc predᵗ TyRenameWf-suc modeRename-suc-inst
      RenameLeftInverse-suc c⊒)
  where
  modeRename-suc-inst : ∀ {μ} → ModeRename suc μ (instᵈ μ)
  modeRename-suc-inst X = refl

  add-head : ∀ {Σ X A}
    → (X , A) ∈ Σ
    → (X , A) ∈ ((zero , ★) ∷ Σ)
  add-head X,A∈Σ = there X,A∈Σ

left-shift-modeʷ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
      ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
left-shift-modeʷ (c , c⊑) =
  ⇑ᶜ c , weaken-storeʷ add-head
    (renameʷ suc predᵗ TyRenameWf-suc modeRename-suc-inst
      RenameLeftInverse-suc c⊑)
  where
  modeRename-suc-inst : ∀ {μ} → ModeRename suc μ (instᵈ μ)
  modeRename-suc-inst X = refl

  add-head : ∀ {Σ X A}
    → (X , A) ∈ Σ
    → (X , A) ∈ ((zero , ★) ∷ Σ)
  add-head X,A∈Σ = there X,A∈Σ

bind-leftⁿ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
    (ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]})
  → ρ ⊢ᴸⁿ A ⊒ B
  → bind-leftᵉ ρ ⊢ᴸⁿ ⇑ᵗ A ⊒ ⇑ᵗ B
bind-leftⁿ (env μᴸ σ μᴿ []ᵍ) p = left-shift-modeⁿ p

bind-leftʷ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
    (ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]})
  → Σ[ c ∈ Coercion ] ρ ⊢ᴸʷ c ⦂ A ⊑ B
  → Σ[ c ∈ Coercion ]
      bind-leftᵉ ρ ⊢ᴸʷ c ⦂ ⇑ᵗ A ⊑ ⇑ᵗ B
bind-leftʷ (env μᴸ σ μᴿ []ᵍ) p = left-shift-modeʷ p

bind-left-rightⁿ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
    (ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]})
  → ρ ⊢ᴿⁿ A ⊒ B
  → bind-leftᵉ ρ ⊢ᴿⁿ A ⊒ B
bind-left-rightⁿ (env μᴸ σ μᴿ []ᵍ) p = p

left-changeⁿ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ A B χs}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}}
    {ρ′ : NarrowingEnv (χs ▶ᵢ Φ)
      {χs ▶ˢ Σᴸ} {Σᴿ} {[]} {[]}}
  → LeftEnvChange ρ χs ρ′
  → ρ ⊢ᴸⁿ A ⊒ B
  → ρ′ ⊢ᴸⁿ χs ▶ᵗ A ⊒ χs ▶ᵗ B
left-changeⁿ left-done p = p
left-changeⁿ (left-keep changes) p = left-changeⁿ changes p
left-changeⁿ {ρ = ρ} (left-bind changes) p =
  left-changeⁿ changes (bind-leftⁿ ρ p)

left-changeʷ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ A B χs}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}}
    {ρ′ : NarrowingEnv (χs ▶ᵢ Φ)
      {χs ▶ˢ Σᴸ} {Σᴿ} {[]} {[]}}
  → LeftEnvChange ρ χs ρ′
  → Σ[ c ∈ Coercion ] ρ ⊢ᴸʷ c ⦂ A ⊑ B
  → Σ[ c ∈ Coercion ]
      ρ′ ⊢ᴸʷ c ⦂ χs ▶ᵗ A ⊑ χs ▶ᵗ B
left-changeʷ left-done p = p
left-changeʷ (left-keep changes) p = left-changeʷ changes p
left-changeʷ {ρ = ρ} (left-bind changes) p =
  left-changeʷ changes (bind-leftʷ ρ p)

left-changeʳ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ A B χs}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}}
    {ρ′ : NarrowingEnv (χs ▶ᵢ Φ)
      {χs ▶ˢ Σᴸ} {Σᴿ} {[]} {[]}}
  → LeftEnvChange ρ χs ρ′
  → Φ ⊢ A ≈ B
  → (χs ▶ᵢ Φ) ⊢ χs ▶ᵗ A ≈ B
left-changeʳ left-done p = p
left-changeʳ (left-keep changes) p = left-changeʳ changes p
left-changeʳ (left-bind changes) p =
  left-changeʳ changes (⇑ᴸʳ p)

right-changeⁿ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ A B χs}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}}
    {ρ′ : NarrowingEnv (χs ▶ᵢ Φ)
      {χs ▶ˢ Σᴸ} {Σᴿ} {[]} {[]}}
  → LeftEnvChange ρ χs ρ′
  → ρ ⊢ᴿⁿ A ⊒ B
  → ρ′ ⊢ᴿⁿ A ⊒ B
right-changeⁿ left-done p = p
right-changeⁿ (left-keep changes) p = right-changeⁿ changes p
right-changeⁿ {ρ = ρ} (left-bind changes) p =
  right-changeⁿ changes (bind-left-rightⁿ ρ p)

left-changeⁿ-coercion : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ A B χs}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}}
    {ρ′ : NarrowingEnv (χs ▶ᵢ Φ)
      {χs ▶ˢ Σᴸ} {Σᴿ} {[]} {[]}}
    (changes : LeftEnvChange ρ χs ρ′)
    (p : ρ ⊢ᴸⁿ A ⊒ B)
  → proj₁ (left-changeⁿ changes p) ≡ χs ▶ᶜ proj₁ p
left-changeⁿ-coercion left-done p = refl
left-changeⁿ-coercion (left-keep changes) p =
  left-changeⁿ-coercion changes p
left-changeⁿ-coercion
    {ρ = env μᴸ σ μᴿ []ᵍ} (left-bind changes) (c , c⊒) =
  left-changeⁿ-coercion changes
    (bind-leftⁿ (env μᴸ σ μᴿ []ᵍ) (c , c⊒))

left-changeʷ-coercion : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ A B χs}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}}
    {ρ′ : NarrowingEnv (χs ▶ᵢ Φ)
      {χs ▶ˢ Σᴸ} {Σᴿ} {[]} {[]}}
    (changes : LeftEnvChange ρ χs ρ′)
    (p : Σ[ c ∈ Coercion ] ρ ⊢ᴸʷ c ⦂ A ⊑ B)
  → proj₁ (left-changeʷ changes p) ≡ χs ▶ᶜ proj₁ p
left-changeʷ-coercion left-done p = refl
left-changeʷ-coercion (left-keep changes) p =
  left-changeʷ-coercion changes p
left-changeʷ-coercion
    {ρ = env μᴸ σ μᴿ []ᵍ} (left-bind changes) (c , c⊑) =
  left-changeʷ-coercion changes
    (bind-leftʷ (env μᴸ σ μᴿ []ᵍ) (c , c⊑))
