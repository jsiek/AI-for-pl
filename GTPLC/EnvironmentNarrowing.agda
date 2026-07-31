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
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl)

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
    → Φ ⊢★≈ β
    → WfTy Δᴿ B
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ (β , B) ∷ Σᴿ ⊣ Δᴿ

------------------------------------------------------------------------
-- Term-context narrowing
------------------------------------------------------------------------

data CtxNarrowing {Δᴸ Δᴿ} (Φ : ImpCtx Δᴸ Δᴿ) :
    Ctx → Ctx → Set where

  []ᵍ :
      ----------------
      CtxNarrowing Φ [] []

  bothᵍ : ∀ {Γᴸ Γᴿ A B}
    → Φ ⊢ A ⊒ᶠ B
    → CtxNarrowing Φ Γᴸ Γᴿ
      -----------------------------
    → CtxNarrowing Φ (A ∷ Γᴸ) (B ∷ Γᴿ)

private

  ⇑ˢ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
    → bothᵢ Φ ∣ suc Δᴸ ⊢ ⟰ᵗ Σᴸ ⊒ˢ ⟰ᵗ Σᴿ ⊣ suc Δᴿ
  ⇑ˢ []ˢ = []ˢ
  ⇑ˢ (bothˢ X≈Y p σ) =
    bothˢ (both-thereᵢ X≈Y) (⇑ʳ p) (⇑ˢ σ)
  ⇑ˢ (leftˢ α<Δ σ) = leftˢ (s≤s α<Δ) (⇑ˢ σ)
  ⇑ˢ (rightˢ ★≈Y hB σ) =
    rightˢ (both-thereᴿ ★≈Y)
      (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
      (⇑ˢ σ)

  ⇑ᴿˢ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
    → freshᴿ Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ ⟰ᵗ Σᴿ ⊣ suc Δᴿ
  ⇑ᴿˢ []ˢ = []ˢ
  ⇑ᴿˢ (bothˢ X≈Y p σ) =
    bothˢ (freshᴿ-thereᵢ X≈Y) (⇑ᴿʳ p) (⇑ᴿˢ σ)
  ⇑ᴿˢ (leftˢ α<Δ σ) = leftˢ α<Δ (⇑ᴿˢ σ)
  ⇑ᴿˢ (rightˢ ★≈Y hB σ) =
    rightˢ (freshᴿ-thereᴿ ★≈Y)
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
    {!!}
  smart-⇑ᴿˢ reuseᵢ (leftˢ α<Δ σ) =
    leftˢ α<Δ (smart-⇑ᴿˢ reuseᵢ σ)
  smart-⇑ᴿˢ reuseᵢ
      (rightˢ (freshᴸ-thereᴿ ★≈Y) hB σ) =
    rightˢ (both-thereᴿ ★≈Y)
      (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
      (smart-⇑ᴿˢ reuseᵢ σ)

  ⇑ᵍ : ∀ {Δᴸ Δᴿ Γᴸ Γᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → CtxNarrowing Φ Γᴸ Γᴿ
    → CtxNarrowing (bothᵢ Φ) (⤊ᵗ Γᴸ) (⤊ᵗ Γᴿ)
  ⇑ᵍ []ᵍ = []ᵍ
  ⇑ᵍ (bothᵍ p γ) = bothᵍ (⇑ᶠ p) (⇑ᵍ γ)

  ⇑ᴿᵍ : ∀ {Δᴸ Δᴿ Γᴸ Γᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → CtxNarrowing Φ Γᴸ Γᴿ
    → CtxNarrowing (freshᴿ Φ) Γᴸ (⤊ᵗ Γᴿ)
  ⇑ᴿᵍ []ᵍ = []ᵍ
  ⇑ᴿᵍ (bothᵍ p γ) = bothᵍ (⇑ᴿᶠ p) (⇑ᴿᵍ γ)

  smart-⇑ᴿᵍ : ∀ {Δᴸ Δᴿ Γᴸ Γᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
    → SmartExtensionᵢ Φ Ψ
    → CtxNarrowing Φ Γᴸ Γᴿ
    → CtxNarrowing Ψ Γᴸ (⤊ᵗ Γᴿ)
  smart-⇑ᴿᵍ freshᵢ γ = ⇑ᴿᵍ γ
  smart-⇑ᴿᵍ reuseᵢ []ᵍ = []ᵍ
  smart-⇑ᴿᵍ reuseᵢ (bothᵍ p γ) =
    bothᵍ (smart-⇑ᴿᶠ reuseᵢ p)
      (smart-⇑ᴿᵍ reuseᵢ γ)

------------------------------------------------------------------------
-- Term-context narrowing lookup
------------------------------------------------------------------------

infix 4 _∋_⦂_

data _∋_⦂_ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ} :
    ∀ {Γᴸ Γᴿ} → CtxNarrowing Φ Γᴸ Γᴿ
      → ℕ → {A B : Ty} → Φ ⊢ A ⊒ᶠ B → Set where

  Zⁿ : ∀ {Γᴸ Γᴿ A B}
      {p : Φ ⊢ A ⊒ᶠ B}
      {γ : CtxNarrowing Φ Γᴸ Γᴿ}
      --------------------------------
    → bothᵍ p γ ∋ zero ⦂ p

  Sⁿ : ∀ {Γᴸ Γᴿ A B C D x}
      {p : Φ ⊢ A ⊒ᶠ B}
      {q : Φ ⊢ C ⊒ᶠ D}
      {γ : CtxNarrowing Φ Γᴸ Γᴿ}
    → γ ∋ x ⦂ p
      --------------------------------
    → bothᵍ q γ ∋ suc x ⦂ p

------------------------------------------------------------------------
-- Bundled narrowing environments
------------------------------------------------------------------------

infix 3 _∣_∣_

record NarrowingEnv {Δᴸ Δᴿ} (Φ : ImpCtx Δᴸ Δᴿ)
    {Σᴸ Σᴿ : TyStore} {Γᴸ Γᴿ : Ctx} : Set where
  constructor env
  field
    storeⁿ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
    contextⁿ : CtxNarrowing Φ Γᴸ Γᴿ

_∣_∣_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    (Φ : ImpCtx Δᴸ Δᴿ)
  → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
  → CtxNarrowing Φ Γᴸ Γᴿ
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
Φ ∣ σ ∣ γ = env σ γ

------------------------------------------------------------------------
-- Operators on bundled narrowing environments
------------------------------------------------------------------------

⇑ᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → NarrowingEnv (bothᵢ Φ) {⟰ᵗ Σᴸ} {⟰ᵗ Σᴿ} {⤊ᵗ Γᴸ} {⤊ᵗ Γᴿ}
⇑ᵉ (env σ γ) = env (⇑ˢ σ) (⇑ᵍ γ)

⇑ᴿᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → NarrowingEnv (freshᴿ Φ) {Σᴸ} {⟰ᵗ Σᴿ} {Γᴸ} {⤊ᵗ Γᴿ}
⇑ᴿᵉ (env σ γ) = env (⇑ᴿˢ σ) (⇑ᴿᵍ γ)

smart-⇑ᴿᵉ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
  → SmartExtensionᵢ Φ Ψ
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}
  → NarrowingEnv Ψ {Σᴸ} {⟰ᵗ Σᴿ} {Γᴸ} {⤊ᵗ Γᴿ}
smart-⇑ᴿᵉ extension (env σ γ) =
  env (smart-⇑ᴿˢ extension σ) (smart-⇑ᴿᵍ extension γ)

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
_⊢ᵀ_⊒_ {Φ = Φ} ρ A B = Φ ⊢ A ⊒ᶠ B

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
env σ γ ∋ᵉ x ⦂ p = γ ∋ x ⦂ p

_,ᵍ_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
    (ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ})
  → ρ ⊢ᵀ A ⊒ B
  → NarrowingEnv Φ {Σᴸ} {Σᴿ} {A ∷ Γᴸ} {B ∷ Γᴿ}
_,ᵍ_ {Φ = Φ} (env σ γ) p = Φ ∣ σ ∣ bothᵍ p γ
