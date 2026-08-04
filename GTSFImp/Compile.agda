module Compile where

-- File Charter:
--   * Compiles gradual source terms to the explicit-cast calculus.
--   * Inserts consistency evidence directly as cast annotations.
--   * Proves that compilation preserves typing and source values.
--   * Is parametric in the target type store; type application allocates its
--     runtime representation later, according to the target semantics.

open import Data.Product using (Σ-syntax; _,_; proj₁)

open import Types
open import TyStore using (TyStore; store-lift)
open import TermCtx using (TermCtx)
open import Consistency

open import GradualTerms
  using (GTerm)
  renaming
    ( `_ to `ᴳ_
    ; ƛ_⇒_ to ƛᴳ_⇒_
    ; _·[_]_ to _·ᴳ[_]_
    ; Λ_ to Λᴳ_
    ; _`[_] to _`ᴳ[_]
    ; $ to $ᴳ
    ; _⊕[_at_]_ to _⊕ᴳ[_at_]_
    ; Value to Valueᴳ
    ; _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢` to ⊢ᴳ`
    ; ⊢ƛ to ⊢ᴳƛ
    ; ⊢· to ⊢ᴳ·
    ; ⊢·★ to ⊢ᴳ·★
    ; ⊢Λ to ⊢ᴳΛ
    ; ⊢• to ⊢ᴳ•
    ; ⊢$ to ⊢ᴳ$
    ; ⊢⊕ to ⊢ᴳ⊕
    )

open import CastTerms
  using (Term; ⟨_,_,_⟩)
  renaming
    ( `_ to `ᵀ_
    ; ƛ_ to ƛᵀ_
    ; _·_ to _·ᵀ_
    ; Λ_ to Λᵀ_
    ; _⦂∀_[_] to _⦂∀ᵀ_[_]
    ; $ to $ᵀ
    ; _⊕[_]_ to _⊕ᵀ[_]_
    ; _⟨_⟩ to _⟨ᵀ_⟩
    ; Value to Valueᵀ
    ; _⊢_⦂_ to _⊢ᵀ_⦂_
    ; ⊢` to ⊢ᵀ`
    ; ⊢ƛ to ⊢ᵀƛ
    ; ⊢· to ⊢ᵀ·
    ; ⊢Λ to ⊢ᵀΛ
    ; ⊢• to ⊢ᵀ•
    ; ⊢$ to ⊢ᵀ$
    ; ⊢⊕ to ⊢ᵀ⊕
    ; ⊢⟨⟩ to ⊢ᵀ⟨⟩
    )

------------------------------------------------------------------------
-- Compilation
------------------------------------------------------------------------

compile : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ} {M : GTerm Δ}
    {A : Ty Δ}
  → Δ ∣ Γ ⊢ᴳ M ⦂ A
  → Σ[ N ∈ Term Δ ] ⟨ Δ , Σ , Γ ⟩ ⊢ᵀ N ⦂ A

compile-value : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {M : GTerm Δ} {A : Ty Δ}
  → (vM : Valueᴳ M)
  → (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A)
  → Valueᵀ (proj₁ (compile {Σ = Σ} M⊢))

compile (⊢ᴳ` x∈) =
  `ᵀ _ , ⊢ᵀ` x∈
compile (⊢ᴳƛ M⊢) with compile M⊢
compile (⊢ᴳƛ M⊢) | N , N⊢ =
  ƛᵀ N , ⊢ᵀƛ N⊢
compile (⊢ᴳ· L⊢ M⊢ A∼A′) with compile L⊢ | compile M⊢
compile (⊢ᴳ· L⊢ M⊢ A∼A′) | L′ , L′⊢ | M′ , M′⊢ =
  L′ ·ᵀ (M′ ⟨ᵀ symᶜ A∼A′ ⟩) ,
  ⊢ᵀ· L′⊢ (⊢ᵀ⟨⟩ M′⊢ (symᶜ A∼A′))
compile (⊢ᴳ·★ L⊢ M⊢ A′∼★) with compile L⊢ | compile M⊢
compile (⊢ᴳ·★ L⊢ M⊢ A′∼★) | L′ , L′⊢ | M′ , M′⊢ =
  let c : ★ ∼ (★ ⇒ ★)
      c = (？ (id ★ ↦ id ★)) in
  L′ ⟨ᵀ c ⟩ ·ᵀ (M′ ⟨ᵀ A′∼★ ⟩) , ⊢ᵀ· (⊢ᵀ⟨⟩ L′⊢ c) (⊢ᵀ⟨⟩ M′⊢ A′∼★)
compile {Σ = Σ} (⊢ᴳΛ vM M⊢)
    with compile {Σ = store-lift Σ} M⊢
       | compile-value {Σ = store-lift Σ} vM M⊢
compile {Σ = Σ} (⊢ᴳΛ vM M⊢) | N , N⊢ | vN =
  Λᵀ N , ⊢ᵀΛ vN N⊢
compile (⊢ᴳ• {B = B} {A = A} M⊢) with compile M⊢
compile (⊢ᴳ• {B = B} {A = A} M⊢) | M′ , M′⊢ =
  M′ ⦂∀ᵀ B [ A ] , ⊢ᵀ• M′⊢
compile (⊢ᴳ$ κ) =
  $ᵀ κ , ⊢ᵀ$ κ
compile (⊢ᴳ⊕ op L⊢ A∼arg M⊢ B∼arg)
    with compile L⊢ | compile M⊢
compile (⊢ᴳ⊕ op L⊢ A∼arg M⊢ B∼arg)
    | L′ , L′⊢ | M′ , M′⊢ =
  (L′ ⟨ᵀ A∼arg ⟩) ⊕ᵀ[ op ] (M′ ⟨ᵀ B∼arg ⟩) ,
  ⊢ᵀ⊕ op (⊢ᵀ⟨⟩ L′⊢ A∼arg) (⊢ᵀ⟨⟩ M′⊢ B∼arg)

compile-value {Σ = Σ} (ƛᴳ A ⇒ M) (⊢ᴳƛ M⊢)
    with compile {Σ = Σ} M⊢
compile-value {Σ = Σ} (ƛᴳ A ⇒ M) (⊢ᴳƛ M⊢)
    | N , N⊢ =
  ƛᵀ N
compile-value ($ᴳ κ) (⊢ᴳ$ .κ) = $ᵀ κ
compile-value {Σ = Σ} (Λᴳ M) (⊢ᴳΛ vM M⊢)
    with compile {Σ = store-lift Σ} M⊢
       | compile-value {Σ = store-lift Σ} vM M⊢
compile-value {Σ = Σ} (Λᴳ M) (⊢ᴳΛ vM M⊢)
    | N , N⊢ | vN =
  Λᵀ vN
