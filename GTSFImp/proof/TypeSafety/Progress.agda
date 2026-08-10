module proof.TypeSafety.Progress where

-- File Charter:
--   * Proves progress for closed, well-typed GTSFImp terms.
--   * Supplies the canonical forms and cast classifications used by the proof.
--   * Depends on CastTerms typing and the store-changing Reduction relation.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool)
open import Data.List using ([])
open import Data.Nat using (zero; suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; refl; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import TermCtx using (TermCtx)
open import Consistency
open import Conversion
open import Primitives
open import CastTerms
open import Reduction
open import proof.Consistency using (gen-safe)

------------------------------------------------------------------------
-- Progress and canonical views
------------------------------------------------------------------------

data Progress {Δ : TyCtx} {Σ : TyStore Δ} (M : Term Δ) : Set where
  done : Value M → Progress {Σ = Σ} M
  step : ∀ {Δ′} {χ : StoreChange Δ Δ′} {N : Term Δ′}
    → M —→[ χ ] N
    → Progress {Σ = Σ} M
  crash : M ≡ blame → Progress {Σ = Σ} M

data FunView {Δ : TyCtx} (V : Term Δ) : Set where
  fv-ƛ : ∀ {N} → V ≡ ƛ N → FunView V
  fv-⇒ : ∀ {μ : Env∼ Δ} {W} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Value W
    → V ≡ W ⟨ c ↦ d ⟩
    → FunView V
  fv-reveal : ∀ {W A A′ B B′}
      {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
    → Value W → V ≡ W ↑ (c ↦↑ d) → FunView V
  fv-conceal : ∀ {W A A′ B B′}
      {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
    → Value W → V ≡ W ↓ (c ↦↓ d) → FunView V

data AllView {Δ : TyCtx} (C : Ty (suc Δ)) (V : Term Δ) : Set where
  av-Λ : ∀ {W} → Value W → V ≡ Λ W → AllView C V
  av-∀ : ∀ {μ : Env∼ Δ} {W} {A : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ C}
    → Value W → V ≡ W ⟨ ∀ᶜ c ⟩ → AllView C V
  av-gen : ∀ {μ : Env∼ Δ} {W} {A : Ty Δ}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ C}
      ⦃ Cnv : NonVar C ⦄ ⦃ z∈C : 0 ∈ᵗ C ⦄
    → Value W
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → V ≡ W ⟨ (gen c) A≢★ ⟩
    → AllView C V
  av-reveal : ∀ {W A} {c : Conv↑ (suc Δ) A C}
    → Value W
    → V ≡ W ↑ `∀↑ c
    → AllView C V
  av-conceal : ∀ {W A} {c : Conv↓ (suc Δ) A C}
    → Value W
    → V ≡ W ↓ `∀↓ c
    → AllView C V

data NatView {Δ : TyCtx} (V : Term Δ) : Set where
  nv-const : ∀ {n} → V ≡ $ (κℕ n) → NatView V

data BoolView {Δ : TyCtx} (V : Term Δ) : Set where
  bv-const : ∀ {b : Bool} → V ≡ $ (κ𝔹 b) → BoolView V

data StarView {Δ : TyCtx} (V : Term Δ) : Set where
  sv-tag : ∀ {μ : Env∼ Δ} {W G} {Gᵍ : Ground G}
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ Gns : NonStar G ⦄
    → Value W
    → V ≡ W ⟨ _! ⦃ Gᵍ ⦄ (idᵍ {μ = μ} Gᵍ) ⟩
    → StarView V

data SealView {Δ : TyCtx} (Σ : TyStore Δ) (X : TyVar Δ)
    (V : Term Δ) : Set where
  sv-conceal : ∀ {W R}
    → Σ ∋ X ⦂ R
    → Value W
    → V ≡ W ↓ seal X R
    → SealView Σ X V

lookup-unique : ∀ {Δ} {Σ : TyStore Δ} {X A B}
  → Σ ∋ X ⦂ A
  → Σ ∋ X ⦂ B
  → A ≡ B
lookup-unique (Z∋ eq) (Z∋ eq′) = trans eq (sym eq′)
lookup-unique (S-lift∋ X∈ eq) (S-lift∋ X∈′ eq′) =
  trans eq (trans (cong ⇑ᵗ (lookup-unique X∈ X∈′)) (sym eq′))
lookup-unique (S-bind∋ X∈ eq) (S-bind∋ X∈′ eq′) =
  trans eq (trans (cong ⇑ᵗ (lookup-unique X∈ X∈′)) (sym eq′))

------------------------------------------------------------------------
-- Canonical forms
------------------------------------------------------------------------

canonical-⇒ : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ} {A B : Ty Δ}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ (A ⇒ B)
  → FunView V
canonical-⇒ (ƛ N) (⊢ƛ V⊢) = fv-ƛ refl
canonical-⇒ (Λ vV) ()
canonical-⇒ ($ (κℕ n)) ()
canonical-⇒ ($ (κ𝔹 b)) ()
canonical-⇒ (vW 《 inj 》) ()
canonical-⇒ (vW 《 fun 》) (⊢⟨⟩ W⊢ c) = fv-⇒ vW refl
canonical-⇒ (vW 《 all 》) ()
canonical-⇒ (vW 《 genᵥ A≠★ safe 》) ()
canonical-⇒ (vW ↑ fun) (⊢reveal (⊢↑-⇒ c⊢ d⊢) W⊢) =
  fv-reveal vW refl
canonical-⇒ (vW ↑ all) ()
canonical-⇒ (vW ↓ seal) ()
canonical-⇒ (vW ↓ fun) (⊢conceal (⊢↓-⇒ c⊢ d⊢) W⊢) =
  fv-conceal vW refl
canonical-⇒ (vW ↓ all) ()

canonical-∀ : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {V : Term Δ} {A : Ty (suc Δ)}
  → Value V
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ `∀ A
  → AllView A V
canonical-∀ (ƛ N) ()
canonical-∀ (Λ vV) (⊢Λ _ V⊢) = av-Λ vV refl
canonical-∀ ($ (κℕ n)) ()
canonical-∀ ($ (κ𝔹 b)) ()
canonical-∀ (vW 《 inj 》) ()
canonical-∀ (vW 《 fun 》) ()
canonical-∀ (vW 《 all 》) (⊢⟨⟩ W⊢ c) = av-∀ vW refl
canonical-∀ (vW 《 genᵥ A≠★ safe 》) (⊢⟨⟩ W⊢ c) =
  av-gen vW A≠★ safe refl
canonical-∀ (vW ↑ fun) ()
canonical-∀ (vW ↑ all)
    (⊢reveal (⊢↑-∀ {A = A} c⊢) W⊢) =
  av-reveal vW refl
canonical-∀ (vW ↓ seal) ()
canonical-∀ (vW ↓ fun) ()
canonical-∀ (vW ↓ all)
    (⊢conceal (⊢↓-∀ {A = A} c⊢) W⊢) =
  av-conceal vW refl

canonical-ℕ : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ ‵ `ℕ
  → NatView V
canonical-ℕ (ƛ N) ()
canonical-ℕ (Λ vV) ()
canonical-ℕ ($ (κℕ n)) (⊢$ (κℕ .n)) = nv-const refl
canonical-ℕ ($ (κ𝔹 b)) ()
canonical-ℕ (vW 《 inj 》) ()
canonical-ℕ (vW 《 fun 》) ()
canonical-ℕ (vW 《 all 》) ()
canonical-ℕ (vW 《 genᵥ A≠★ safe 》) ()
canonical-ℕ (vW ↑ fun) ()
canonical-ℕ (vW ↑ all) ()
canonical-ℕ (vW ↓ seal) ()
canonical-ℕ (vW ↓ fun) ()
canonical-ℕ (vW ↓ all) ()

canonical-𝔹 : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ ‵ `𝔹
  → BoolView V
canonical-𝔹 (ƛ N) ()
canonical-𝔹 (Λ vV) ()
canonical-𝔹 ($ (κℕ n)) ()
canonical-𝔹 ($ (κ𝔹 b)) (⊢$ (κ𝔹 .b)) = bv-const refl
canonical-𝔹 (vW 《 inj 》) ()
canonical-𝔹 (vW 《 fun 》) ()
canonical-𝔹 (vW 《 all 》) ()
canonical-𝔹 (vW 《 genᵥ A≠★ safe 》) ()
canonical-𝔹 (vW ↑ fun) ()
canonical-𝔹 (vW ↑ all) ()
canonical-𝔹 (vW ↓ seal) ()
canonical-𝔹 (vW ↓ fun) ()
canonical-𝔹 (vW ↓ all) ()

canonical-★ : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ} {V : Term Δ}
  → Value V
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ ★
  → StarView V
canonical-★ (ƛ N) ()
canonical-★ (Λ vV) ()
canonical-★ ($ (κℕ n)) ()
canonical-★ ($ (κ𝔹 b)) ()
canonical-★ (vW 《 inj 》) (⊢⟨⟩ W⊢ c) =
  sv-tag vW refl
canonical-★ (vW 《 fun 》) ()
canonical-★ (vW 《 all 》) ()
canonical-★ (vW 《 genᵥ A≠★ safe 》) ()
canonical-★ (vW ↑ fun) ()
canonical-★ (vW ↑ all) ()
canonical-★ (vW ↓ seal) ()
canonical-★ (vW ↓ fun) ()
canonical-★ (vW ↓ all) ()

canonical-X : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ} {X : TyVar Δ}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ ＇ X
  → SealView Σ X V
canonical-X (ƛ N) ()
canonical-X (Λ vV) ()
canonical-X ($ (κℕ n)) ()
canonical-X ($ (κ𝔹 b)) ()
canonical-X (vW 《 inj 》) ()
canonical-X (vW 《 fun 》) ()
canonical-X (vW 《 all 》) ()
canonical-X (vW 《 genᵥ A≠★ safe 》) ()
canonical-X (vW ↑ fun) ()
canonical-X (vW ↑ all) ()
canonical-X (vW ↓ seal) (⊢conceal (⊢↓-seal X∈) W⊢) =
  sv-conceal X∈ vW refl
canonical-X (vW ↓ fun) ()
canonical-X (vW ↓ all) ()

------------------------------------------------------------------------
-- Fresh type-variable contradictions
------------------------------------------------------------------------

X∼★≢X∼X : X∼★ ≢ X∼X
X∼★≢X∼X ()

no-to-distinct-variable : ∀ {Δ} {μ : Env∼ Δ}
    {A : Ty Δ} {X Y : TyVar Δ}
  → μ Y ≡ X∼★
  → μ X ≡ X∼X
  → μ ⊢ A ∼ ＇ X
  → Y ∈ᵗ A
  → ⊥
no-to-distinct-variable Y★ XX (id (＇ X)) var-∈ =
  X∼★≢X∼X (trans (sym Y★) XX)
no-to-distinct-variable Y★ XX
    (？_ ⦃ g ⦄ c ⦃ Bns ⦄) ()
no-to-distinct-variable Y★ XX
    (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) (∈-all Y∈A) =
  no-to-distinct-variable Y★ XX c Y∈A

consistency-to-fresh : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)}
  → extᵐ μ ⊢ A ∼ ＇ Fin.zero
  → A ≡ ＇ Fin.zero
consistency-to-fresh (id (＇ Fin.zero)) = refl
consistency-to-fresh
    (？_ ⦃ Gᵍ = ★⇒★ ⦄ ())
consistency-to-fresh
    (？_ ⦃ Gᵍ = ‵ ι ⦄ ())
consistency-to-fresh
    (？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ () ⦄ c)
consistency-to-fresh
    (？_ ⦃ Gᵍ = ＇ Fin.suc X ⦄ ())
consistency-to-fresh
    (？_ ⦃ Gᵍ = ∀★ ⦄ (inst_ ⦃ Anv ⦄ ⦃ () ⦄ c B≢★))
consistency-to-fresh
    (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
  ⊥-elim (no-to-distinct-variable refl refl c z∈A)

no-zero-store-lift : ∀ {Δ} {Σ : TyStore Δ} {A : Ty (suc Δ)}
  → store-lift Σ ∋ Fin.zero ⦂ A
  → ⊥
no-zero-store-lift ()

fresh-not-shift : ∀ {Δ} (A : Ty Δ)
  → ＇ Fin.zero ≢ ⇑ᵗ A
fresh-not-shift (＇ X) ()
fresh-not-shift (‵ ι) ()
fresh-not-shift ★ ()
fresh-not-shift (A ⇒ B) ()
fresh-not-shift (`∀ A) ()

no-fresh-representation : ∀ {Δ} {Σ : TyStore Δ}
    {X : TyVar (suc Δ)}
  → store-lift Σ ∋ X ⦂ ＇ Fin.zero
  → ⊥
no-fresh-representation (S-lift∋ {A = A} X∈ eq) =
  fresh-not-shift A eq

reveal-to-fresh : ∀ {Δ} {Σ : TyStore Δ} {A : Ty (suc Δ)}
    {c : Conv↑ (suc Δ) A (＇ Fin.zero)}
  → store-lift Σ ⊢↑ c
  → A ≡ ＇ Fin.zero
reveal-to-fresh (⊢↑-unseal X∈) =
  ⊥-elim (no-fresh-representation X∈)
reveal-to-fresh ⊢↑-id = refl

conceal-to-fresh : ∀ {Δ} {Σ : TyStore Δ} {A : Ty (suc Δ)}
    {c : Conv↓ (suc Δ) A (＇ Fin.zero)}
  → store-lift Σ ⊢↓ c
  → A ≡ ＇ Fin.zero
conceal-to-fresh (⊢↓-seal X∈) =
  ⊥-elim (no-zero-store-lift X∈)
conceal-to-fresh ⊢↓-id = refl

no-fresh-value : ∀ {Δ} {Σ : TyStore Δ}
    {Γ : TermCtx (suc Δ)} {V : Term (suc Δ)}
  → Value V
  → ⟨ suc Δ , store-lift Σ , Γ ⟩ ⊢ V ⦂ ＇ Fin.zero
  → ⊥
no-fresh-value (ƛ N) ()
no-fresh-value (Λ vV) ()
no-fresh-value ($ (κℕ n)) ()
no-fresh-value ($ (κ𝔹 b)) ()
no-fresh-value (vW 《 inj 》) ()
no-fresh-value (vW 《 fun 》) ()
no-fresh-value (vW 《 all 》) ()
no-fresh-value (vW 《 genᵥ A≠★ safe 》) ()
no-fresh-value (vW ↑ fun) ()
no-fresh-value (vW ↑ all) ()
no-fresh-value (vW ↓ seal) (⊢conceal (⊢↓-seal X∈) W⊢) =
  no-zero-store-lift X∈
no-fresh-value (vW ↓ fun) ()
no-fresh-value (vW ↓ all) ()

no-bot-value : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {V : Term Δ}
  → Value V
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ `∀ (＇ Fin.zero)
  → ⊥
no-bot-value (Λ vV) (⊢Λ _ V⊢) = no-fresh-value vV V⊢
no-bot-value ($ (κℕ n)) ()
no-bot-value ($ (κ𝔹 b)) ()
no-bot-value (vW 《 all 》) (⊢⟨⟩ W⊢ (∀ᶜ c))
    with consistency-to-fresh c
no-bot-value (vW 《 all 》) (⊢⟨⟩ W⊢ (∀ᶜ c)) | refl =
  no-bot-value vW W⊢
no-bot-value (vW ↑ all) (⊢reveal (⊢↑-∀ c⊢) W⊢)
    with reveal-to-fresh c⊢
no-bot-value (vW ↑ all) (⊢reveal (⊢↑-∀ c⊢) W⊢) | refl =
  no-bot-value vW W⊢
no-bot-value (vW ↓ all) (⊢conceal (⊢↓-∀ c⊢) W⊢)
    with conceal-to-fresh c⊢
no-bot-value (vW ↓ all) (⊢conceal (⊢↓-∀ c⊢) W⊢) | refl =
  no-bot-value vW W⊢

------------------------------------------------------------------------
-- Ground-cast classification
------------------------------------------------------------------------

data ToStar {Δ : TyCtx} {μ : Env∼ Δ} : ∀ {A : Ty Δ}
    → (c : μ ⊢ A ∼ ★) → Set where
  same : ToStar (id ★)
  other : ∀ {A : Ty Δ} {c : μ ⊢ A ∼ ★}
    → A ≢ ★ → ToStar c

to-star : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
  → (c : μ ⊢ A ∼ ★) → ToStar c
to-star (id ★) = same
to-star (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (nonStar≢★ Ans)
to-star (？_ ⦃ g ⦄ c ⦃ () ⦄)
to-star (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) = other (λ ())

data FromStar {Δ : TyCtx} {μ : Env∼ Δ} : ∀ {B : Ty Δ}
    → (c : μ ⊢ ★ ∼ B) → Set where
  same : FromStar (id ★)
  other : ∀ {B : Ty Δ} {c : μ ⊢ ★ ∼ B}
    → B ≢ ★ → FromStar c

from-star : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ}
  → (c : μ ⊢ ★ ∼ B) → FromStar c
from-star (id ★) = same
from-star (_! ⦃ g ⦄ c ⦃ () ⦄)
from-star (？_ ⦃ g ⦄ c ⦃ Bns ⦄) =
  other (nonStar≢★ Bns)
from-star (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) = other (λ ())

data ToGround {Δ : TyCtx} {μ : Env∼ Δ} {G : Ty Δ}
    (Gᵍ : Ground G) :
    ∀ {A : Ty Δ} → μ ⊢ A ∼ G → Set where
  same : ToGround Gᵍ (idᵍ Gᵍ)
  other : ∀ {A : Ty Δ} {c : μ ⊢ A ∼ G}
    → A ≢ G → ToGround Gᵍ c

occurs-star-impossible : ∀ {Δ} {X : TyVar Δ} → X ∈ᵗ ★ → ⊥
occurs-star-impossible ()

to-ground : ∀ {Δ} {μ : Env∼ Δ} {A G : Ty Δ}
  → (Gᵍ : Ground G)
  → (c : μ ⊢ A ∼ G)
  → ToGround Gᵍ c
to-ground (‵ ι) (id (‵ ι)) = same
to-ground (‵ ι) (？_ ⦃ g ⦄ c ⦃ Bns ⦄) = other (λ ())
to-ground (‵ ι) (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) = other (λ ())
to-ground ★⇒★ (？_ ⦃ g ⦄ c ⦃ Bns ⦄) = other (λ ())
to-ground ★⇒★ (c ↦ d) with from-star c | to-star d
to-ground ★⇒★ (.(id ★) ↦ .(id ★)) | same | same = same
to-ground ★⇒★ (c ↦ d) | same | other B≠★ =
  other (λ { refl → B≠★ refl })
to-ground ★⇒★ (c ↦ d) | other A≠★ | same =
  other (λ { refl → A≠★ refl })
to-ground ★⇒★ (c ↦ d) | other A≠★ | other B≠★ =
  other (λ { refl → A≠★ refl })
to-ground ★⇒★ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) = other (λ ())
to-ground (＇ X) (id (＇ X)) = same
to-ground (＇ X) (？_ ⦃ g ⦄ c ⦃ Bns ⦄) = other (λ ())
to-ground (＇ X) (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) = other (λ ())
to-ground ∀★ (∀ᶜ c) with to-star c
to-ground ∀★ (∀ᶜ (id ★)) | same = same
to-ground ∀★ (∀ᶜ c) | other A≠★ =
  other (λ { refl → A≠★ refl })
to-ground ∀★ (？_ ⦃ g ⦄ c ⦃ Bns ⦄) = other (λ ())
to-ground ∀★ (gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c A≢★)
to-ground ∀★ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
  other (λ { refl → occurs-star-impossible z∈A })
to-ground ∀★ bot-elim = other (λ ())

data FromGround {Δ : TyCtx} {μ : Env∼ Δ} {G : Ty Δ}
    (Gᵍ : Ground G) :
    ∀ {B : Ty Δ} → μ ⊢ G ∼ B → Set where
  same : FromGround Gᵍ (idᵍ Gᵍ)
  other : ∀ {B : Ty Δ} {c : μ ⊢ G ∼ B}
    → B ≢ G → FromGround Gᵍ c

from-ground : ∀ {Δ} {μ : Env∼ Δ} {G B : Ty Δ}
  → (Gᵍ : Ground G)
  → (c : μ ⊢ G ∼ B)
  → FromGround Gᵍ c
from-ground (‵ ι) (id (‵ ι)) = same
from-ground (‵ ι) (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (λ ())
from-ground (‵ ι) (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) = other (λ ())
from-ground ★⇒★ (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (λ ())
from-ground ★⇒★ (c ↦ d) with to-star c | from-star d
from-ground ★⇒★ (.(id ★) ↦ .(id ★)) | same | same = same
from-ground ★⇒★ (c ↦ d) | same | other B≠★ =
  other (λ { refl → B≠★ refl })
from-ground ★⇒★ (c ↦ d) | other A≠★ | same =
  other (λ { refl → A≠★ refl })
from-ground ★⇒★ (c ↦ d) | other A≠★ | other B≠★ =
  other (λ { refl → A≠★ refl })
from-ground ★⇒★ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) = other (λ ())
from-ground (＇ X) (id (＇ X)) = same
from-ground (＇ X) (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (λ ())
from-ground (＇ X) (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) = other (λ ())
from-ground ∀★ (∀ᶜ c) with from-star c
from-ground ∀★ (∀ᶜ (id ★)) | same = same
from-ground ∀★ (∀ᶜ c) | other B≠★ =
  other (λ { refl → B≠★ refl })
from-ground ∀★ (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (λ ())
from-ground ∀★ (inst_ ⦃ Anv ⦄ ⦃ () ⦄ c B≢★)
from-ground ∀★ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) =
  other (λ { refl → occurs-star-impossible z∈B })
from-ground ∀★ bot-intro = other (λ ())

no-to-base : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {X : TyVar Δ} {ι}
  → μ ⊢ A ∼ ‵ ι
  → X ∈ᵗ A
  → ⊥
no-to-base (id (‵ ι)) ()
no-to-base (？_ ⦃ g ⦄ c ⦃ Bns ⦄) ()
no-to-base (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) (∈-all X∈A) =
  no-to-base c X∈A

no-from-base : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ} {X : TyVar Δ} {ι}
  → μ ⊢ ‵ ι ∼ B
  → X ∈ᵗ B
  → ⊥
no-from-base (id (‵ ι)) ()
no-from-base (_! ⦃ g ⦄ c ⦃ Ans ⦄) ()
no-from-base (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) (∈-all X∈B) =
  no-from-base c X∈B

occurrence-nonstar : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∈ᵗ A
  → NonStar A
occurrence-nonstar var-∈ = nonstar-X
occurrence-nonstar (∈-fun-left X∈A) = nonstar-⇒
occurrence-nonstar (∈-fun-right X∉A X∈B) = nonstar-⇒
occurrence-nonstar (∈-all X∈A) = nonstar-∀

------------------------------------------------------------------------
-- Progress for values under casts and conversions
------------------------------------------------------------------------

cast-value-progress : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    {A B : Ty Δ} {μ : Env∼ Δ}
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ A
  → Value V
  → (c : μ ⊢ A ∼ B)
  → Progress {Σ = Σ} (V ⟨ c ⟩)
cast-value-progress V⊢ vV (id a) = step (pure-step (β-id vV))
cast-value-progress V⊢ vV (c ↦ d) = done (vV 《 fun 》)
cast-value-progress V⊢ vV (∀ᶜ c) = done (vV 《 all 》)
cast-value-progress V⊢ vV
    (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄)
    with to-ground Gᵍ c
cast-value-progress V⊢ vV
    (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ .(idᵍ Gᵍ) ⦃ Ans ⦄)
    | same =
  done (vV 《 inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ ⦃ Gns = Ans ⦄ 》)
cast-value-progress V⊢ vV
    (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄)
    | other A≠G =
  step (pure-step
    (ground ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
      ⦃ Ans = Ans ⦄ ⦃ Gns = ground-nonstar Gᵍ ⦄ vV A≠G))
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄)
    with from-ground Gᵍ c
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄)
    | other B≠G =
  step (pure-step
    (expand ⦃ Gᵍ = Gᵍ ⦄ ⦃ ★∼G = ★∼G ⦄
      ⦃ Bns = Bns ⦄ ⦃ Gns = ground-nonstar Gᵍ ⦄
      vV (λ G≡B → B≠G (sym G≡B))))
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
    | same with canonical-★ vV V⊢
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
    | same | sv-tag {G = H} {Gᵍ = Hᵍ} ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns ⦄ vW refl
    with H ≟Ty G
cast-value-progress V⊢ vV
    (？_ {G = .H} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
    | same | sv-tag {G = H} {Gᵍ = Hᵍ} ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns ⦄ vW refl
    | yes refl rewrite nonStar-unique Bns Gns
                     | ground-unique Gᵍ Hᵍ =
  step (pure-step
    (tag-untag ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄
      ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = Gns ⦄ vW))
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
    | same | sv-tag {G = H} {Gᵍ = Hᵍ} ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns ⦄ vW refl
    | no H≠G =
  step (pure-step
    (tag-untag-bad ⦃ Gᵍ = Hᵍ ⦄ ⦃ Hᵍ = Gᵍ ⦄
      ⦃ G∼★ = H∼★ ⦄ ⦃ ★∼H = ★∼G ⦄
      ⦃ Gns = Gns ⦄ ⦃ Hns = Bns ⦄ vW H≠G))
cast-value-progress V⊢ vV
    (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
  step (β-inst vV B≢★)
cast-value-progress V⊢ vV
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) =
  done (vV 《 genᵥ A≢★ (gen-safe c A≢★ Bnv z∈B) 》)
cast-value-progress V⊢ vV bot-elim =
  ⊥-elim (no-bot-value vV V⊢)
cast-value-progress V⊢ vV bot-intro =
  step (pure-step (blame-bot-intro vV))

reveal-value-progress : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    {A B : Ty Δ} {c : Conv↑ Δ A B}
  → Σ ⊢↑ c
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ A
  → Value V
  → Progress {Σ = Σ} (V ↑ c)
reveal-value-progress (⊢↑-unseal X∈) V⊢ vV
    with canonical-X vV V⊢
reveal-value-progress (⊢↑-unseal X∈) V⊢ vV
    | sv-conceal X∈′ vW refl
    rewrite lookup-unique X∈′ X∈ =
  step (pure-step (conceal-reveal vW))
reveal-value-progress (⊢↑-⇒ c⊢ d⊢) V⊢ vV = done (vV ↑ fun)
reveal-value-progress (⊢↑-∀ c⊢) V⊢ vV = done (vV ↑ all)
reveal-value-progress ⊢↑-id V⊢ vV = step (pure-step (id-reveal vV))

conceal-value-progress : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    {A B : Ty Δ} {c : Conv↓ Δ A B}
  → Σ ⊢↓ c
  → Value V
  → Progress {Σ = Σ} (V ↓ c)
conceal-value-progress (⊢↓-seal X∈) vV = done (vV ↓ seal)
conceal-value-progress (⊢↓-⇒ c⊢ d⊢) vV = done (vV ↓ fun)
conceal-value-progress (⊢↓-∀ c⊢) vV = done (vV ↓ all)
conceal-value-progress ⊢↓-id vV = step (pure-step (id-conceal vV))

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ} {A : Ty Δ}
  → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ A
  → Progress {Σ = Σ} M
progress (⊢` ())
progress (⊢ƛ M⊢) = done (ƛ _)
progress (⊢· L⊢ M⊢) with progress L⊢
progress (⊢· L⊢ M⊢) | step L→L′ =
  step (ξ-·₁ L→L′ refl)
progress (⊢· L⊢ M⊢) | crash refl =
  step (pure-step blame-·₁)
progress (⊢· L⊢ M⊢) | done vL with progress M⊢
progress (⊢· L⊢ M⊢) | done vL | step M→M′ =
  step (ξ-·₂ vL M→M′ refl)
progress (⊢· L⊢ M⊢) | done vL | crash refl =
  step (pure-step (blame-·₂ vL))
progress (⊢· L⊢ M⊢) | done vL | done vM
    with canonical-⇒ vL L⊢
progress (⊢· L⊢ M⊢) | done vL | done vM | fv-ƛ refl =
  step (pure-step (β vM))
progress (⊢· L⊢ M⊢) | done vL | done vM
    | fv-⇒ vW refl =
  step (pure-step (β-⇒ vW vM))
progress (⊢· L⊢ M⊢) | done vL | done vM
    | fv-reveal vW refl =
  step (pure-step (β-reveal-⇒ vW vM))
progress (⊢· L⊢ M⊢) | done vL | done vM
    | fv-conceal vW refl =
  step (pure-step (β-conceal-⇒ vW vM))
progress (⊢Λ vM M⊢) = done (Λ vM)
progress (⊢• {C = C} L⊢) with progress L⊢
progress (⊢• {C = C} L⊢) | step L→L′ =
  step (ξ-• L→L′ refl refl)
progress (⊢• {C = C} L⊢) | crash refl =
  step (pure-step blame-•)
progress (⊢• {C = C} L⊢) | done vL
    with canonical-∀ vL L⊢
progress (⊢• {C = C} L⊢) | done vL | av-Λ vW refl =
  step (β-Λ {B = C} vW)
progress (⊢• {C = C} L⊢) | done vL | av-∀ vW refl =
  step (pure-step (β-∀ vW refl))
progress (⊢• {C = C} L⊢) | done vL
    | av-gen vW A≠★ safe refl =
  step (β-gen vW A≠★ safe)
progress (⊢• {C = C} L⊢) | done vL
    | av-reveal vW refl =
  step (β-reveal-∀ vW)
progress (⊢• {C = C} L⊢) | done vL
    | av-conceal vW refl =
  step (β-conceal-∀ vW)
progress (⊢$ κ) = done ($ κ)
progress (⊢⊕ addℕ L⊢ M⊢) with progress L⊢
progress (⊢⊕ addℕ L⊢ M⊢) | step L→L′ =
  step (ξ-⊕₁ L→L′ refl)
progress (⊢⊕ addℕ L⊢ M⊢) | crash refl =
  step (pure-step blame-⊕₁)
progress (⊢⊕ addℕ L⊢ M⊢) | done vL with progress M⊢
progress (⊢⊕ addℕ L⊢ M⊢) | done vL | step M→M′ =
  step (ξ-⊕₂ vL M→M′ refl)
progress (⊢⊕ addℕ L⊢ M⊢) | done vL | crash refl =
  step (pure-step (blame-⊕₂ vL))
progress (⊢⊕ addℕ L⊢ M⊢) | done vL | done vM
    with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
progress (⊢⊕ addℕ L⊢ M⊢) | done vL | done vM
    | nv-const refl | nv-const refl =
  step (pure-step (δ-⊕ δ-add))
progress (⊢⊕ and𝔹 L⊢ M⊢) with progress L⊢
progress (⊢⊕ and𝔹 L⊢ M⊢) | step L→L′ =
  step (ξ-⊕₁ L→L′ refl)
progress (⊢⊕ and𝔹 L⊢ M⊢) | crash refl =
  step (pure-step blame-⊕₁)
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL with progress M⊢
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL | step M→M′ =
  step (ξ-⊕₂ vL M→M′ refl)
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL | crash refl =
  step (pure-step (blame-⊕₂ vL))
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL | done vM
    with canonical-𝔹 vL L⊢ | canonical-𝔹 vM M⊢
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL | done vM
    | bv-const refl | bv-const refl =
  step (pure-step (δ-⊕ δ-and))
progress (⊢⟨⟩ M⊢ c) with progress M⊢
progress (⊢⟨⟩ M⊢ c) | step M→M′ =
  step (ξ-⟨⟩ M→M′ refl)
progress (⊢⟨⟩ M⊢ c) | crash refl =
  step (pure-step blame-⟨⟩)
progress (⊢⟨⟩ M⊢ c) | done vM = cast-value-progress M⊢ vM c
progress (⊢reveal c⊢ M⊢) with progress M⊢
progress (⊢reveal c⊢ M⊢) | step M→M′ =
  step (ξ-reveal M→M′ refl)
progress (⊢reveal c⊢ M⊢) | crash refl =
  step (pure-step blame-reveal)
progress (⊢reveal c⊢ M⊢) | done vM =
  reveal-value-progress c⊢ M⊢ vM
progress (⊢conceal c⊢ M⊢) with progress M⊢
progress (⊢conceal c⊢ M⊢) | step M→M′ =
  step (ξ-conceal M→M′ refl)
progress (⊢conceal c⊢ M⊢) | crash refl =
  step (pure-step blame-conceal)
progress (⊢conceal c⊢ M⊢) | done vM =
  conceal-value-progress c⊢ vM
progress ⊢blame = crash refl
