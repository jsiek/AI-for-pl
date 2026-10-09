{-# OPTIONS --safe #-}

module proof.DGG.Inversion.SpineValueDef where

-- File Charter:
--   * Defines the stable value-spine surface shared by DGG inversion proofs
--     and diagnostics.
--   * Provides target polymorphic value views for inst catch-up statements.
--   * Provides canonical target-variable/tag-boundary views used by the
--     right-injection inversion and seal transfer.
--   * Depends only on core cast-term imprecision typing projections and
--     the canonical complete-context world.

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

open import Types
open import TyStore using (TyStore; _∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _↪ᵗ_; _!;
  ∀ᶜ_; gen_; toRenameᵗ)
import Consistency as C
open import Conversion using (Conv↑; Conv↓; _↦↑_; _↦↓_;
  `∀↑_; `∀↓_; ⊢↓-seal)
open import Imprecision
open import Primitives using (Const; κℕ; κ𝔹)
open import CastTerms
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.CastTermImprecisionTyping as CTIT
open import proof.DGG.World
open CTIR using (_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Target polymorphic value views
------------------------------------------------------------------------

data AllValueView {Δ : TyCtx} (V : Term Δ) : Set where
  allv-Λ : ∀ {W}
    → Value W
    → V ≡ Λ W
    → AllValueView V

  allv-∀ : ∀ {μ : Env∼ Δ} {W} {A B : Ty (suc Δ)}
      {c : C.extᵐ μ ⊢ A ∼ B}
    → Value W
    → V ≡ W ⟨ ∀ᶜ c ⟩
    → AllValueView V

  allv-gen : ∀ {μ : Env∼ Δ} {W} {A : Ty Δ} {B : Ty (suc Δ)}
      {c : C.genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    → Value W
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → V ≡ W ⟨ (gen c) A≢★ ⟩
    → AllValueView V

  allv-reveal : ∀ {W} {A B : Ty (suc Δ)} {c : Conv↑ (suc Δ) A B}
    → Value W
    → V ≡ W ↑ `∀↑ c
    → AllValueView V

  allv-conceal : ∀ {W} {A B : Ty (suc Δ)} {c : Conv↓ (suc Δ) A B}
    → Value W
    → V ≡ W ↓ `∀↓ c
    → AllValueView V

------------------------------------------------------------------------
-- Source value spines
------------------------------------------------------------------------

data SpineValue {Δ : TyCtx} : Term Δ → Set where
  sv-ƛ : (N : Term Δ) → SpineValue (ƛ N)

  sv-Λ : ∀ {V} → SpineValue V → SpineValue (Λ V)

  sv-$ : (κ : Const) → SpineValue ($ κ)

  sv-cast : ∀ {V} {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → SpineValue V → Inert c → SpineValue (V ⟨ c ⟩)

  sv-seal : ∀ {V X R} → SpineValue V
    → SpineValue (V ↓ Conversion.seal X R)

  sv-reveal-fun : ∀ {V} {A A′ B B′ : Ty Δ}
      {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
    → SpineValue V → SpineValue (V ↑ (c ↦↑ d))

  sv-conceal-fun : ∀ {V} {A A′ B B′ : Ty Δ}
      {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
    → SpineValue V → SpineValue (V ↓ (c ↦↓ d))

  sv-reveal-all : ∀ {V} {A B : Ty (suc Δ)} {c : Conv↑ (suc Δ) A B}
    → SpineValue V → SpineValue (V ↑ `∀↑ c)

  sv-conceal-all : ∀ {V} {A B : Ty (suc Δ)} {c : Conv↓ (suc Δ) A B}
    → SpineValue V → SpineValue (V ↓ `∀↓ c)

------------------------------------------------------------------------
-- Canonical target values at an abstract variable
------------------------------------------------------------------------

data VarValueView {Δ : TyCtx} (Σ : TyStore Δ) (V : Term Δ)
    (X : TyVar Δ) : Set where
  varv-seal : ∀ {W R}
    → Value W
    → Σ ∋ X ⦂ R
    → V ≡ W ↓ Conversion.seal X R
    → VarValueView Σ V X

var-value-view : ∀ {Δ} {Σ : TyStore Δ} {Γ} {V : Term Δ} {X}
  → Value V
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ ＇ X
  → VarValueView Σ V X
var-value-view (ƛ N) ()
var-value-view (Λ vV) ()
var-value-view ($ (κℕ n)) ()
var-value-view ($ (κ𝔹 b)) ()
var-value-view (vV 《 inj 》) ()
var-value-view (vV 《 fun 》) ()
var-value-view (vV 《 all 》) ()
var-value-view (vV 《 genᵥ A≢★ safe 》) ()
var-value-view (vV ↑ fun) ()
var-value-view (vV ↑ all) ()
var-value-view (vV ↓ seal) (⊢conceal (⊢↓-seal X∈) V⊢) =
  varv-seal vV X∈ refl
var-value-view (vV ↓ fun) ()
var-value-view (vV ↓ all) ()

private
  tag-inner-typing : ∀ {Δ} {Σ : TyStore Δ} {Γ} {N : Term Δ}
      {H : Ty Δ} {ν : Env∼ Δ}
      {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
      {cH : ν ⊢ H ∼ H}
    → ⟨ Δ , Σ , Γ ⟩ ⊢
        N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ⦂ ★
    → ⟨ Δ , Σ , Γ ⟩ ⊢ N ⦂ H
  tag-inner-typing (⊢⟨⟩ N⊢ cH!) = N⊢

right-tag-variable-view : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {N : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {Y : TyVar (Δᵉ Γᴿ)}
    {ν : Env∼ (Δᵉ Γᴿ)}
    {H∼★ : ν ⊢ (＇ Y) ∼★} {Hns : NonStar (＇ Y)}
    {cH : ν ⊢ (＇ Y) ∼ (＇ Y)} {p : A ⊑ᵀ⟨ γ ⟩ ★}
  → Value N
  → γ ⊢² M
      ⊑ N ⟨ _! ⦃ ＇ Y ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → VarValueView (Σᵉ Γᴿ) N Y
right-tag-variable-view vN M⊑N! =
  var-value-view vN (tag-inner-typing (CTIT.target-typing M⊑N!))

private
  variable-imprecision-aligns : ∀ {Δ} {μ : ImpEnv Δ}
      {X Y : TyVar Δ}
    → μ ⊢ ＇ X ⊑ ＇ Y
    → X ≡ Y
  variable-imprecision-aligns X⊑X = refl

variable-obligation-aligns : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {X : TyVar (Δᵉ Γᴸ)} {Y : TyVar (Δᵉ Γᴿ)}
  → ＇ X ⊑ᵀ⟨ γ ⟩ ＇ Y
  → toRenameⁱ (ηᴸᶜ γ) X ≡ toRenameⁱ (ηᴿᶜ γ) Y
variable-obligation-aligns q = variable-imprecision-aligns q
