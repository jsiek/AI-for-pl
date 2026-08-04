module EnvironmentNarrowing where

-- File Charter:
--   * Defines relocation between GTPLC type stores.
--   * Indexes term-context entries by factored type narrowing.
--   * Records paired and one-sided type-store entries.
--   * Provides lookup into term-context narrowing derivations.
--   * Bundles all environment narrowing evidence used by term narrowing.
--   * Computes ordinary, right-only, and smart environment shifts.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _<_; zero; suc; s≤s)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl)

open import Types hiding (_∋_⦂_)
open import TyStore
open import Ctx
open import Coercions
open import Terms
open import TypeRelocate
open import FactoredTypeNarrowing
open import NarrowWiden using
  ( _∣_∣_⊢_⦂_⊑_
  ; _∣_∣_⊢_⦂_⊒_
  ; _∣_∣_⊢_⊑_
  ; _∣_∣_⊢_⊒_
  )
open import proof.ImprecisionModeWeakening using
  ( ext-gen-incl
  ; weakenⁿ-bundle
  )
open import proof.TypeInTypeSubst using
  ( TyRenameWf-suc
  ; renameᵗ-preserves-WfTy
  )

------------------------------------------------------------------------
-- Type-store narrowing
------------------------------------------------------------------------

infix 4 _∣_⊢_⊒ˢ_⊣_

data _∣_⊢_⊒ˢ_⊣_ {Δᴸ Δᴿ} (Φ : ImpCtx Δᴸ Δᴿ) :
    TyCtx → TyStore → TyStore → TyCtx → Set where

  []ˢ :
      --------------------------------
      Φ ∣ Δᴸ ⊢ [] ⊒ˢ [] ⊣ Δᴿ

  bothˢ : ∀ {Σᴸ Σᴿ α β A B}
    → Φ ⊢ α ≈ˣ β
    → Φ ⊢ A ≈ B
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ
        ⊢ (α , A) ∷ Σᴸ ⊒ˢ (β , B) ∷ Σᴿ ⊣ Δᴿ

  leftˢ : ∀ {Σᴸ Σᴿ α}
    → α < Δᴸ
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ (α , ★) ∷ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ

  rightˢ : ∀ {Σᴸ Σᴿ β B}
    → Φ ⊢ β ˣᴿ
    → WfTy Δᴿ B
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ (β , B) ∷ Σᴿ ⊣ Δᴿ

------------------------------------------------------------------------
-- Term-context narrowing
------------------------------------------------------------------------

data CtxNarrowing {Δᴸ Δᴿ}
    (μᴸ : ModeEnv) (Σᴸ : TyStore) (Φ : ImpCtx Δᴸ Δᴿ)
    (μᴿ : ModeEnv) (Σᴿ : TyStore) : Ctx → Ctx → Set where

  []ᵍ :
      -------------------------------------
      CtxNarrowing μᴸ Σᴸ Φ μᴿ Σᴿ [] []

  bothᵍ : ∀ {Γᴸ Γᴿ A B}
    → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
    → CtxNarrowing μᴸ Σᴸ Φ μᴿ Σᴿ Γᴸ Γᴿ
      --------------------------------------------------
    → CtxNarrowing μᴸ Σᴸ Φ μᴿ Σᴿ (A ∷ Γᴸ) (B ∷ Γᴿ)

private

  ⇑ˢ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
    → bothᵢ Φ ∣ suc Δᴸ
        ⊢ ⟰ᵗ Σᴸ ⊒ˢ ⟰ᵗ Σᴿ ⊣ suc Δᴿ
  ⇑ˢ []ˢ = []ˢ
  ⇑ˢ (bothˢ X≈Y p σ) =
    bothˢ (both-thereᵢ X≈Y) (⇑ʳ p) (⇑ˢ σ)
  ⇑ˢ (leftˢ α<Δ σ) = leftˢ (s≤s α<Δ) (⇑ˢ σ)
  ⇑ˢ (rightˢ Yᴿ hB σ) =
    rightˢ (both-thereᴿ Yᴿ)
      (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
      (⇑ˢ σ)

  ⇑ᴿˢ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
    → freshᴿ Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ ⟰ᵗ Σᴿ ⊣ suc Δᴿ
  ⇑ᴿˢ []ˢ = []ˢ
  ⇑ᴿˢ (bothˢ X≈Y p σ) =
    bothˢ (freshᴿ-thereᵢ X≈Y) (⇑ᴿʳ p) (⇑ᴿˢ σ)
  ⇑ᴿˢ (leftˢ α<Δ σ) = leftˢ α<Δ (⇑ᴿˢ σ)
  ⇑ᴿˢ (rightˢ Yᴿ hB σ) =
    rightˢ (freshᴿ-thereᴿ Yᴿ)
      (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
      (⇑ᴿˢ σ)

  smart-⇑ᴿˢ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
    → SmartExtensionᵢ Φ Ψ
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
    → Ψ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ ⟰ᵗ Σᴿ ⊣ suc Δᴿ
  smart-⇑ᴿˢ freshᵢ σ = ⇑ᴿˢ σ
  smart-⇑ᴿˢ reuseᵢ []ˢ = []ˢ
  smart-⇑ᴿˢ reuseᵢ
      (bothˢ (freshᴸ-thereᵢ X≈Y) p σ) =
    bothˢ (both-thereᵢ X≈Y) (⇑ᴿ-reuseʳ p)
      (smart-⇑ᴿˢ reuseᵢ σ)
  smart-⇑ᴿˢ reuseᵢ (leftˢ α<Δ σ) =
    leftˢ α<Δ (smart-⇑ᴿˢ reuseᵢ σ)
  smart-⇑ᴿˢ reuseᵢ
      (rightˢ (freshᴸ-thereᴿ Yᴿ) hB σ) =
    rightˢ (both-thereᴿ Yᴿ)
      (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
      (smart-⇑ᴿˢ reuseᵢ σ)

  ⇑ᵍ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ}
    → CtxNarrowing μᴸ Σᴸ Φ μᴿ Σᴿ Γᴸ Γᴿ
    → CtxNarrowing (extᵈ μᴸ) (⟰ᵗ Σᴸ) (bothᵢ Φ)
        (extᵈ μᴿ) (⟰ᵗ Σᴿ) (⤊ᵗ Γᴸ) (⤊ᵗ Γᴿ)
  ⇑ᵍ []ᵍ = []ᵍ
  ⇑ᵍ (bothᵍ p γ) = bothᵍ (⇑ᶠ p) (⇑ᵍ γ)

  ⇑ᴿᵍ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ}
    → CtxNarrowing μᴸ Σᴸ Φ μᴿ Σᴿ Γᴸ Γᴿ
    → CtxNarrowing μᴸ Σᴸ (freshᴿ Φ)
        (genᵈ μᴿ) (⟰ᵗ Σᴿ) Γᴸ (⤊ᵗ Γᴿ)
  ⇑ᴿᵍ []ᵍ = []ᵍ
  ⇑ᴿᵍ (bothᵍ p γ) = bothᵍ (⇑ᴿᶠ p) (⇑ᴿᵍ γ)

  smart-⇑ᴿᵍ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
    → SmartExtensionᵢ Φ Ψ
    → CtxNarrowing μᴸ Σᴸ Φ μᴿ Σᴿ Γᴸ Γᴿ
    → CtxNarrowing μᴸ Σᴸ Ψ
        (genᵈ μᴿ) (⟰ᵗ Σᴿ) Γᴸ (⤊ᵗ Γᴿ)
  smart-⇑ᴿᵍ extension []ᵍ = []ᵍ
  smart-⇑ᴿᵍ extension (bothᵍ p γ) =
    bothᵍ (smart-⇑ᴿᶠ extension p) (smart-⇑ᴿᵍ extension γ)

------------------------------------------------------------------------
-- Term-context narrowing lookup
------------------------------------------------------------------------

infix 4 _∋_⦂_

data _∋_⦂_ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ} :
    ∀ {Γᴸ Γᴿ} → CtxNarrowing μᴸ Σᴸ Φ μᴿ Σᴿ Γᴸ Γᴿ
      → ℕ → {A B : Ty}
      → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
      → Set where

  Zⁿ : ∀ {Γᴸ Γᴿ A B}
      {p : μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B}
      {γ : CtxNarrowing μᴸ Σᴸ Φ μᴿ Σᴿ Γᴸ Γᴿ}
      --------------------------------
    → bothᵍ p γ ∋ zero ⦂ p

  Sⁿ : ∀ {Γᴸ Γᴿ A B C D x}
      {p : μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B}
      {q : μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ C ⊒ᶠ D}
      {γ : CtxNarrowing μᴸ Σᴸ Φ μᴿ Σᴿ Γᴸ Γᴿ}
    → γ ∋ x ⦂ p
      --------------------------------
    → bothᵍ q γ ∋ suc x ⦂ p

------------------------------------------------------------------------
-- Bundled narrowing environments
------------------------------------------------------------------------

record NarrowingEnv {Δᴸ Δᴿ} (Φ : ImpCtx Δᴸ Δᴿ)
    {Σᴸ Σᴿ : TyStore} {Γᴸ Γᴿ : Ctx} : Set where
  constructor env
  field
    modeᴸ : ModeEnv
    storeⁿ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
    modeᴿ : ModeEnv
    contextⁿ : CtxNarrowing modeᴸ Σᴸ Φ modeᴿ Σᴿ Γᴸ Γᴿ

open NarrowingEnv public

------------------------------------------------------------------------
-- Operators on bundled narrowing environments
------------------------------------------------------------------------

⇑ᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → NarrowingEnv (bothᵢ Φ)
      {⟰ᵗ Σᴸ} {⟰ᵗ Σᴿ} {⤊ᵗ Γᴸ} {⤊ᵗ Γᴿ}
⇑ᵉ (env μᴸ σ μᴿ γ) =
  env (extᵈ μᴸ) (⇑ˢ σ) (extᵈ μᴿ) (⇑ᵍ γ)

⇑ᴿᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → NarrowingEnv (freshᴿ Φ) {Σᴸ} {⟰ᵗ Σᴿ} {Γᴸ} {⤊ᵗ Γᴿ}
⇑ᴿᵉ (env μᴸ σ μᴿ γ) =
  env μᴸ (⇑ᴿˢ σ) (genᵈ μᴿ) (⇑ᴿᵍ γ)

smart-⇑ᴿᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
  → SmartExtensionᵢ Φ Ψ
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → NarrowingEnv Ψ {Σᴸ} {⟰ᵗ Σᴿ} {Γᴸ} {⤊ᵗ Γᴿ}
smart-⇑ᴿᵉ extension (env μᴸ σ μᴿ γ) =
  env μᴸ (smart-⇑ᴿˢ extension σ) (genᵈ μᴿ)
    (smart-⇑ᴿᵍ extension γ)

data SmartExtensionᵉ :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
    → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
    → NarrowingEnv Ψ {Σᴸ} {⟰ᵗ Σᴿ} {Γᴸ} {⤊ᵗ Γᴿ}
    → Set where

  freshᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
      -----------------------------------
    → SmartExtensionᵉ ρ (⇑ᴿᵉ ρ)

  reuseᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {ρ : NarrowingEnv (freshᴸ Φ) {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
      ------------------------------------------------------
    → SmartExtensionᵉ ρ (smart-⇑ᴿᵉ reuseᵢ ρ)

extensionᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
    {ρ′ : NarrowingEnv Ψ {Σᴸ} {⟰ᵗ Σᴿ} {Γᴸ} {⤊ᵗ Γᴿ}}
  → SmartExtensionᵉ ρ ρ′
  → SmartExtensionᵢ Φ Ψ
extensionᵉ freshᵉ = freshᵢ
extensionᵉ reuseᵉ = reuseᵢ

infix 4 _⊢ᵀ_⊒_
infix 4 _⊢ᴸ_ _⊢ᴿ_
infix 4 _⊢ᴸⁿ_⊒_ _⊢ᴿⁿ_⊒_
infix 4 _⊢ᴿ⁺[_]_⦂_⊒_
infix 4 _⊢ᴸⁿ_⦂_⊒_ _⊢ᴸʷ_⦂_⊑_
infix 4 _⊢ᴿⁿ_⦂_⊒_ _⊢ᴿʷ_⦂_⊑_
infix 4 _⊢ᴸ_⦂_ _⊢ᴿ_⦂_
infix 4 _∣_⊢ᴸ_⦂_⊑_ _∣_⊢ᴸ_⦂_⊒_
infix 4 _∣_⊢ᴿ_⦂_⊑_ _∣_⊢ᴿ_⦂_⊒_
infix 4 _∣_⊢ᴸ_∶_=⇒_ _∣_⊢ᴿ_∶_=⇒_
infix 4 _∋ᵉ_⦂_
infixl 5 _,ᵍ_

_⊢ᵀ_⊒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Ty → Ty → Set
_⊢ᵀ_⊒_ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} {Φ = Φ}
    (env μᴸ σ μᴿ γ) A B =
  μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B

_⊢ᴸⁿ_⊒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Ty → Ty → Set
_⊢ᴸⁿ_⊒_ {Δᴸ = Δᴸ} {Σᴸ = Σᴸ} (env μᴸ σ μᴿ γ) A B =
  μᴸ ∣ Δᴸ ∣ Σᴸ ⊢ A ⊒ B

_⊢ᴿⁿ_⊒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Ty → Ty → Set
_⊢ᴿⁿ_⊒_ {Δᴿ = Δᴿ} {Σᴿ = Σᴿ} (env μᴸ σ μᴿ γ) A B =
  μᴿ ∣ Δᴿ ∣ Σᴿ ⊢ A ⊒ B

_⊢ᴿ⁺[_]_⦂_⊒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Ty → Coercion → Ty → Ty → Set
_⊢ᴿ⁺[_]_⦂_⊒_ {Δᴿ = Δᴿ} {Σᴿ = Σᴿ}
    (env μᴸ σ μᴿ γ) R c A B =
  genᵈ μᴿ ∣ suc Δᴿ ∣ (zero , R) ∷ ⟰ᵗ Σᴿ
    ⊢ c ⦂ A ⊒ B

_⊢ᴸⁿ_⦂_⊒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_⊢ᴸⁿ_⦂_⊒_ {Δᴸ = Δᴸ} {Σᴸ = Σᴸ}
    (env μᴸ σ μᴿ γ) c A B =
  μᴸ ∣ Δᴸ ∣ Σᴸ ⊢ c ⦂ A ⊒ B

_⊢ᴸʷ_⦂_⊑_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_⊢ᴸʷ_⦂_⊑_ {Δᴸ = Δᴸ} {Σᴸ = Σᴸ}
    (env μᴸ σ μᴿ γ) c A B =
  μᴸ ∣ Δᴸ ∣ Σᴸ ⊢ c ⦂ A ⊑ B

_⊢ᴿⁿ_⦂_⊒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_⊢ᴿⁿ_⦂_⊒_ {Δᴿ = Δᴿ} {Σᴿ = Σᴿ}
    (env μᴸ σ μᴿ γ) c A B =
  μᴿ ∣ Δᴿ ∣ Σᴿ ⊢ c ⦂ A ⊒ B

_⊢ᴿʷ_⦂_⊑_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_⊢ᴿʷ_⦂_⊑_ {Δᴿ = Δᴿ} {Σᴿ = Σᴿ}
    (env μᴸ σ μᴿ γ) c A B =
  μᴿ ∣ Δᴿ ∣ Σᴿ ⊢ c ⦂ A ⊑ B

_⊢ᴸ_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Ty → Set
_⊢ᴸ_ {Δᴸ = Δᴸ} ρ A = WfTy Δᴸ A

_⊢ᴿ_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Ty → Set
_⊢ᴿ_ {Δᴿ = Δᴿ} ρ A = WfTy Δᴿ A

_⊢ᴸ_⦂_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Term → Ty → Set₁
_⊢ᴸ_⦂_ {Δᴸ = Δᴸ} {Σᴸ = Σᴸ} {Γᴸ = Γᴸ} ρ M A =
  ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊢ M ⦂ A

_⊢ᴿ_⦂_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Term → Ty → Set₁
_⊢ᴿ_⦂_ {Δᴿ = Δᴿ} {Σᴿ = Σᴿ} {Γᴿ = Γᴿ} ρ M A =
  ⟨ Δᴿ , Σᴿ , Γᴿ ⟩ ⊢ M ⦂ A

_∣_⊢ᴸ_⦂_⊑_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → ModeEnv
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_∣_⊢ᴸ_⦂_⊑_ {Δᴸ = Δᴸ} {Σᴸ = Σᴸ} μ ρ c A B =
  μ ∣ Δᴸ ∣ Σᴸ ⊢ c ⦂ A ⊑ B

_∣_⊢ᴸ_⦂_⊒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → ModeEnv
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_∣_⊢ᴸ_⦂_⊒_ {Δᴸ = Δᴸ} {Σᴸ = Σᴸ} μ ρ c A B =
  μ ∣ Δᴸ ∣ Σᴸ ⊢ c ⦂ A ⊒ B

_∣_⊢ᴿ_⦂_⊑_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → ModeEnv
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_∣_⊢ᴿ_⦂_⊑_ {Δᴿ = Δᴿ} {Σᴿ = Σᴿ} μ ρ c A B =
  μ ∣ Δᴿ ∣ Σᴿ ⊢ c ⦂ A ⊑ B

_∣_⊢ᴿ_⦂_⊒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → ModeEnv
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_∣_⊢ᴿ_⦂_⊒_ {Δᴿ = Δᴿ} {Σᴿ = Σᴿ} μ ρ c A B =
  μ ∣ Δᴿ ∣ Σᴿ ⊢ c ⦂ A ⊒ B

_∣_⊢ᴸ_∶_=⇒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → ModeEnv
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_∣_⊢ᴸ_∶_=⇒_ {Δᴸ = Δᴸ} {Σᴸ = Σᴸ} μ ρ c A B =
  μ ∣ Δᴸ ∣ Σᴸ ⊢ c ∶ A =⇒ B

_∣_⊢ᴿ_∶_=⇒_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → ModeEnv
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → Coercion → Ty → Ty → Set
_∣_⊢ᴿ_∶_=⇒_ {Δᴿ = Δᴿ} {Σᴿ = Σᴿ} μ ρ c A B =
  μ ∣ Δᴿ ∣ Σᴿ ⊢ c ∶ A =⇒ B

_∋ᵉ_⦂_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
    (ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ})
  → ℕ → {A B : Ty} → ρ ⊢ᵀ A ⊒ B → Set
env μᴸ σ μᴿ γ ∋ᵉ x ⦂ p = γ ∋ x ⦂ p

_,ᵍ_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
    (ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ})
  → ρ ⊢ᵀ A ⊒ B
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {A ∷ Γᴸ} {B ∷ Γᴿ}
_,ᵍ_ {Φ = Φ} (env μᴸ σ μᴿ γ) p =
  env μᴸ σ μᴿ (bothᵍ p γ)
