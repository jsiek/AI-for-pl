module EnvironmentNarrowing where

-- File Charter:
--   * Defines narrowing between GTPLC type stores and term contexts.
--   * Indexes environment entries by two-context type narrowing.
--   * Records paired and one-sided type-store entries.
--   * Provides lookup into term-context narrowing derivations.
--   * Bundles all environment narrowing evidence used by term narrowing.
--   * Computes ordinary, right-only, and smart environment shifts.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _<_; zero; suc; s≤s)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≢_; refl)
  renaming (subst to subst≡)

open import Types hiding (_∋_⦂_)
open import TyStore
open import Ctx
open import Coercions
open import Terms
open import TypeNarrow
open import NarrowWiden using
  ( _∣_∣_⊢_⦂_⊑_
  ; _∣_∣_⊢_⦂_⊒_
  )
open import proof.TypeInTypeSubst using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; renameᵗ-id
  ; renameᵗ-preserves-WfTy
  ; rename-preserves-tagged
  ; rename-ext-preserves-zero∈
  )

------------------------------------------------------------------------
-- Type narrowing under environment extension
------------------------------------------------------------------------

private

  record RenameNarrowing
      {Δᴸ Δᴿ Δᴸ′ Δᴿ′}
      (ρᴸ ρᴿ : Renameᵗ)
      (Φ : ImpCtx Δᴸ Δᴿ)
      (Ψ : ImpCtx Δᴸ′ Δᴿ′) : Set where
    constructor rename-narrowing
    field
      left-wfᵣ : TyRenameWf Δᴸ Δᴸ′ ρᴸ
      right-wfᵣ : TyRenameWf Δᴿ Δᴿ′ ρᴿ
      varᵣ : ∀ {X Y}
        → Φ ⊢ X ≈ˣ Y
        → Ψ ⊢ ρᴸ X ≈ˣ ρᴿ Y
      tagᵣ : ∀ {G}
        → Φ ⊢★ G
        → Ψ ⊢★ renameᵍ ρᴿ G

  open RenameNarrowing

  bothᵣ : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameNarrowing ρᴸ ρᴿ Φ Ψ
    → RenameNarrowing (extᵗ ρᴸ) (extᵗ ρᴿ) (bothᵢ Φ) (bothᵢ Ψ)
  bothᵣ (rename-narrowing hᴸ hᴿ var tag) =
    rename-narrowing
      (TyRenameWf-ext hᴸ)
      (TyRenameWf-ext hᴿ)
      both-var
      both-tag
    where
    both-var : ∀ {X Y}
      → bothᵢ _ ⊢ X ≈ˣ Y
      → bothᵢ _ ⊢ extᵗ _ X ≈ˣ extᵗ _ Y
    both-var hereᵢ = hereᵢ
    both-var (both-thereᵢ X≈Y) = both-thereᵢ (var X≈Y)

    both-tag : ∀ {G}
      → bothᵢ _ ⊢★ G
      → bothᵢ _ ⊢★ renameᵍ (extᵗ _) G
    both-tag (both-there★ G⊑★) = both-there★ (tag G⊑★)
    both-tag base★ = base★
    both-tag fun★ = fun★

  freshᴿᵣ : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameNarrowing ρᴸ ρᴿ Φ Ψ
    → RenameNarrowing ρᴸ (extᵗ ρᴿ) (freshᴿ Φ) (freshᴿ Ψ)
  freshᴿᵣ {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {Φ = Φ} {Ψ = Ψ}
      (rename-narrowing hᴸ hᴿ var tag) =
    rename-narrowing
      hᴸ
      (TyRenameWf-ext hᴿ)
      fresh-var
      fresh-tag
    where
    fresh-var : ∀ {X Y}
      → freshᴿ Φ ⊢ X ≈ˣ Y
      → freshᴿ Ψ ⊢ ρᴸ X ≈ˣ extᵗ ρᴿ Y
    fresh-var (freshᴿ-thereᵢ X≈Y) = freshᴿ-thereᵢ (var X≈Y)

    fresh-tag : ∀ {G}
      → freshᴿ Φ ⊢★ G
      → freshᴿ Ψ ⊢★ renameᵍ (extᵗ ρᴿ) G
    fresh-tag here★ = here★
    fresh-tag (freshᴿ-there★ G⊑★) = freshᴿ-there★ (tag G⊑★)
    fresh-tag base★ = base★
    fresh-tag fun★ = fun★

  rename-≢★ : ∀ ρ {A}
    → A ≢ ★
    → renameᵗ ρ A ≢ ★
  rename-≢★ ρ {＇ X} A≢ ()
  rename-≢★ ρ {‵ ι} A≢ ()
  rename-≢★ ρ {★} A≢ = A≢
  rename-≢★ ρ {A ⇒ B} A≢ ()
  rename-≢★ ρ {`∀ A} A≢ ()

  rename-⊒ : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ A B}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameNarrowing ρᴸ ρᴿ Φ Ψ
    → Φ ⊢ A ⊒ B
    → Ψ ⊢ renameᵗ ρᴸ A ⊒ renameᵗ ρᴿ B
  rename-⊒ r (idᵃ (＇ X) (＇ Y) hA hB X≈Y) =
    idᵃ (＇ _) (＇ _)
      (renameᵗ-preserves-WfTy hA (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hB (right-wfᵣ r))
      (varᵣ r X≈Y)
  rename-⊒ r (idᵃ (＇ X) (‵ ι) hA hB ())
  rename-⊒ r (idᵃ (＇ X) ★ hA hB ())
  rename-⊒ r (idᵃ (‵ ι) (＇ Y) hA hB ())
  rename-⊒ r (idᵃ (‵ ι) (‵ ι) hA hB refl) =
    idᵃ (‵ ι) (‵ ι)
      (renameᵗ-preserves-WfTy hA (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hB (right-wfᵣ r))
      refl
  rename-⊒ r (idᵃ (‵ ι) ★ hA hB ())
  rename-⊒ r (idᵃ ★ (＇ Y) hA hB ())
  rename-⊒ r (idᵃ ★ (‵ ι) hA hB ())
  rename-⊒ r (idᵃ ★ ★ hA hB tt) =
    idᵃ ★ ★
      (renameᵗ-preserves-WfTy hA (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hB (right-wfᵣ r))
      tt
  rename-⊒ r (p ↦ q) = rename-⊒ r p ↦ rename-⊒ r q
  rename-⊒ r (∀ⁿ p) = ∀ⁿ (rename-⊒ (bothᵣ r) p)
  rename-⊒ {ρᴿ = ρᴿ} r (untag G⊑★ G꞉A) =
    untag (tagᵣ r G⊑★) (rename-preserves-tagged ρᴿ G꞉A)
  rename-⊒ {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} r
      (gen nonvarA zero∈A p B≢★) =
    gen (renameNonVar (extᵗ ρᴿ) nonvarA)
        (rename-ext-preserves-zero∈ ρᴿ zero∈A)
        (rename-⊒ (freshᴿᵣ r) p)
        (rename-≢★ ρᴸ B≢★)

  shift-tagᵢ : ∀ {Δᴸ Δᴿ G} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢★ G
    → bothᵢ Φ ⊢★ renameᵍ suc G
  shift-tagᵢ {G = ＇ X} G⊑★ = both-there★ G⊑★
  shift-tagᵢ {G = ‵ ι} G⊑★ = base★
  shift-tagᵢ {G = ★⇒★} G⊑★ = fun★

  shiftᵣ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → RenameNarrowing suc suc Φ (bothᵢ Φ)
  shiftᵣ =
    rename-narrowing TyRenameWf-suc TyRenameWf-suc
      both-thereᵢ shift-tagᵢ

  right-shift-tagᵢ : ∀ {Δᴸ Δᴿ G} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢★ G
    → freshᴿ Φ ⊢★ renameᵍ suc G
  right-shift-tagᵢ {G = ＇ X} G⊑★ = freshᴿ-there★ G⊑★
  right-shift-tagᵢ {G = ‵ ι} G⊑★ = base★
  right-shift-tagᵢ {G = ★⇒★} G⊑★ = fun★

  right-shiftᵣ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → RenameNarrowing (λ X → X) suc Φ (freshᴿ Φ)
  right-shiftᵣ =
    rename-narrowing (λ X<Δ → X<Δ) TyRenameWf-suc
      freshᴿ-thereᵢ right-shift-tagᵢ

  reuse-shift-tagᵢ : ∀ {Δᴸ Δᴿ G} {Φ : ImpCtx Δᴸ Δᴿ}
    → freshᴸ Φ ⊢★ G
    → bothᵢ Φ ⊢★ renameᵍ suc G
  reuse-shift-tagᵢ (freshᴸ-there★ G⊑★) = both-there★ G⊑★
  reuse-shift-tagᵢ base★ = base★
  reuse-shift-tagᵢ fun★ = fun★

  reuse-shiftᵣ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → RenameNarrowing (λ X → X) suc (freshᴸ Φ) (bothᵢ Φ)
  reuse-shiftᵣ =
    rename-narrowing (λ X<Δ → X<Δ) TyRenameWf-suc
      reuse-var reuse-shift-tagᵢ
    where
    reuse-var : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
      → freshᴸ Φ ⊢ X ≈ˣ Y
      → bothᵢ Φ ⊢ X ≈ˣ suc Y
    reuse-var (freshᴸ-thereᵢ X≈Y) = both-thereᵢ X≈Y

⇑ᵀ : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ⊒ B
  → bothᵢ Φ ⊢ ⇑ᵗ A ⊒ ⇑ᵗ B
⇑ᵀ = rename-⊒ shiftᵣ

⇑ᴿᵀ : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ⊒ B
  → freshᴿ Φ ⊢ A ⊒ ⇑ᵗ B
⇑ᴿᵀ {A = A} {B = B} {Φ = Φ} p =
  subst≡ (λ A′ → freshᴿ Φ ⊢ A′ ⊒ ⇑ᵗ B)
    (renameᵗ-id A) (rename-⊒ right-shiftᵣ p)

smart-⇑ᴿᵀ : ∀ {Δᴸ Δᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
  → SmartExtensionᵢ Φ Ψ
  → Φ ⊢ A ⊒ B
  → Ψ ⊢ A ⊒ ⇑ᵗ B
smart-⇑ᴿᵀ freshᵢ p = ⇑ᴿᵀ p
smart-⇑ᴿᵀ {A = A} {B = B} {Ψ = Ψ} reuseᵢ p =
  subst≡ (λ A′ → Ψ ⊢ A′ ⊒ ⇑ᵗ B)
    (renameᵗ-id A) (rename-⊒ reuse-shiftᵣ p)

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
    → Φ ⊢ A ⊒ B
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
    → Φ ⊢★ ＇ β
    → WfTy Δᴿ B
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ (β , B) ∷ Σᴿ ⊣ Δᴿ

------------------------------------------------------------------------
-- Term-context narrowing
------------------------------------------------------------------------

infix 4 _∣_⊢_⊒ᵍ_⊣_

data _∣_⊢_⊒ᵍ_⊣_ {Δᴸ Δᴿ} (Φ : ImpCtx Δᴸ Δᴿ) :
    TyCtx → Ctx → Ctx → TyCtx → Set where

  []ᵍ :
      --------------------------------
      Φ ∣ Δᴸ ⊢ [] ⊒ᵍ [] ⊣ Δᴿ

  bothᵍ : ∀ {Γᴸ Γᴿ A B}
    → Φ ⊢ A ⊒ B
    → Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ A ∷ Γᴸ ⊒ᵍ B ∷ Γᴿ ⊣ Δᴿ

private

  ⇑ˢ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
    → bothᵢ Φ ∣ suc Δᴸ ⊢ ⟰ᵗ Σᴸ ⊒ˢ ⟰ᵗ Σᴿ ⊣ suc Δᴿ
  ⇑ˢ []ˢ = []ˢ
  ⇑ˢ (bothˢ X≈Y p σ) =
    bothˢ (both-thereᵢ X≈Y) (⇑ᵀ p) (⇑ˢ σ)
  ⇑ˢ (leftˢ α<Δ σ) = leftˢ (s≤s α<Δ) (⇑ˢ σ)
  ⇑ˢ (rightˢ G⊑★ hB σ) =
    rightˢ (shift-tagᵢ G⊑★)
      (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
      (⇑ˢ σ)

  ⇑ᴿˢ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
    → freshᴿ Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ ⟰ᵗ Σᴿ ⊣ suc Δᴿ
  ⇑ᴿˢ []ˢ = []ˢ
  ⇑ᴿˢ (bothˢ X≈Y p σ) =
    bothˢ (freshᴿ-thereᵢ X≈Y) (⇑ᴿᵀ p) (⇑ᴿˢ σ)
  ⇑ᴿˢ (leftˢ α<Δ σ) = leftˢ α<Δ (⇑ᴿˢ σ)
  ⇑ᴿˢ (rightˢ G⊑★ hB σ) =
    rightˢ (right-shift-tagᵢ G⊑★)
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
    bothˢ (both-thereᵢ X≈Y)
      (smart-⇑ᴿᵀ reuseᵢ p)
      (smart-⇑ᴿˢ reuseᵢ σ)
  smart-⇑ᴿˢ reuseᵢ (leftˢ α<Δ σ) =
    leftˢ α<Δ (smart-⇑ᴿˢ reuseᵢ σ)
  smart-⇑ᴿˢ reuseᵢ
      (rightˢ (freshᴸ-there★ G⊑★) hB σ) =
    rightˢ (both-there★ G⊑★)
      (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
      (smart-⇑ᴿˢ reuseᵢ σ)

  ⇑ᵍ : ∀ {Δᴸ Δᴿ Γᴸ Γᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ
    → bothᵢ Φ ∣ suc Δᴸ ⊢ ⤊ᵗ Γᴸ ⊒ᵍ ⤊ᵗ Γᴿ ⊣ suc Δᴿ
  ⇑ᵍ []ᵍ = []ᵍ
  ⇑ᵍ (bothᵍ p γ) = bothᵍ (⇑ᵀ p) (⇑ᵍ γ)

  ⇑ᴿᵍ : ∀ {Δᴸ Δᴿ Γᴸ Γᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ
    → freshᴿ Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ ⤊ᵗ Γᴿ ⊣ suc Δᴿ
  ⇑ᴿᵍ []ᵍ = []ᵍ
  ⇑ᴿᵍ (bothᵍ p γ) = bothᵍ (⇑ᴿᵀ p) (⇑ᴿᵍ γ)

  smart-⇑ᴿᵍ : ∀ {Δᴸ Δᴿ Γᴸ Γᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
    → SmartExtensionᵢ Φ Ψ
    → Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ
    → Ψ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ ⤊ᵗ Γᴿ ⊣ suc Δᴿ
  smart-⇑ᴿᵍ freshᵢ γ = ⇑ᴿᵍ γ
  smart-⇑ᴿᵍ reuseᵢ []ᵍ = []ᵍ
  smart-⇑ᴿᵍ reuseᵢ (bothᵍ p γ) =
    bothᵍ (smart-⇑ᴿᵀ reuseᵢ p)
      (smart-⇑ᴿᵍ reuseᵢ γ)

------------------------------------------------------------------------
-- Term-context narrowing lookup
------------------------------------------------------------------------

infix 4 _∋_⦂_

data _∋_⦂_ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ} :
    ∀ {Γᴸ Γᴿ} → Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ →
      ℕ → {A B : Ty} → Φ ⊢ A ⊒ B → Set where

  Zⁿ : ∀ {Γᴸ Γᴿ A B}
      {p : Φ ⊢ A ⊒ B}
      {γ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
      --------------------------------
    → bothᵍ p γ ∋ zero ⦂ p

  Sⁿ : ∀ {Γᴸ Γᴿ A B C D x}
      {p : Φ ⊢ A ⊒ B}
      {q : Φ ⊢ C ⊒ D}
      {γ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
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
    contextⁿ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ

_∣_∣_ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ}
    (Φ : ImpCtx Δᴸ Δᴿ)
  → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
  → Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ
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
_⊢ᵀ_⊒_ {Φ = Φ} ρ A B = Φ ⊢ A ⊒ B

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
