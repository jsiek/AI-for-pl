module EnvironmentNarrowing where

-- File Charter:
--   * Defines narrowing between GTPLC type stores and term contexts.
--   * Records paired and one-sided type-store entries.
--   * Relates term-context entries pointwise by bundled type narrowing.
--   * Provides lookup into term-context narrowing derivations.
--   * Supplies the environment indices used by term narrowing.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)

open import Types hiding (_∋_⦂_)
open import TyStore
open import Ctx
open import NarrowWiden

------------------------------------------------------------------------
-- Type-store narrowing
------------------------------------------------------------------------

infix 4 _∣_⊢_⊒ˢ_⊣_

data _∣_⊢_⊒ˢ_⊣_ (Φ : ImpCtx) (Δᴸ : TyCtx) :
    TyStore → TyStore → TyCtx → Set where

  []ˢ : ∀ {Δᴿ}
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ [] ⊒ˢ [] ⊣ Δᴿ

  bothˢ : ∀ {Σᴸ Σᴿ Δᴿ α β A B}
    → Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ (α , A) ∷ Σᴸ ⊒ˢ (β , B) ∷ Σᴿ ⊣ Δᴿ

  leftˢ : ∀ {Σᴸ Σᴿ Δᴿ α}
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ (α , ★) ∷ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ

  rightˢ : ∀ {Σᴸ Σᴿ Δᴿ β B}
    → WfTy Δᴿ B
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ (β , B) ∷ Σᴿ ⊣ Δᴿ

------------------------------------------------------------------------
-- Term-context narrowing
------------------------------------------------------------------------

infix 4 _∣_⊢_⊒ᵍ_⊣_

data _∣_⊢_⊒ᵍ_⊣_ (Φ : ImpCtx) (Δᴸ : TyCtx) :
    Ctx → Ctx → TyCtx → Set where

  []ᵍ : ∀ {Δᴿ}
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ [] ⊒ᵍ [] ⊣ Δᴿ

  bothᵍ : ∀ {Γᴸ Γᴿ Δᴿ A B}
    → Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ
    → Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ
      --------------------------------------------------
    → Φ ∣ Δᴸ ⊢ A ∷ Γᴸ ⊒ᵍ B ∷ Γᴿ ⊣ Δᴿ

------------------------------------------------------------------------
-- Term-context narrowing lookup
------------------------------------------------------------------------

infix 4 _∋_⦂_

data _∋_⦂_ {Φ Δᴸ Δᴿ} :
    ∀ {Γᴸ Γᴿ} → Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ → ℕ → {A B : Ty} →
      Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ → Set where

  Zⁿ : ∀ {Γᴸ Γᴿ A B}
      {pⁿ : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
      {γⁿ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
      --------------------------------------------------
    → bothᵍ pⁿ γⁿ ∋ zero ⦂ pⁿ

  Sⁿ : ∀ {Γᴸ Γᴿ A B C D x}
      {pⁿ : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
      {qⁿ : Φ ∣ Δᴸ ⊢ C ⊒ D ⊣ Δᴿ}
      {γⁿ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
    → γⁿ ∋ x ⦂ pⁿ
      --------------------------------------------------
    → bothᵍ qⁿ γⁿ ∋ suc x ⦂ pⁿ
