module Reduction where

-- File Charter:
--   * Pure and store-changing call-by-value reduction for CastTerms.
--   * Implements the ground-type cast rules of Figure 4 of "Refined
--     Criteria for Gradual Typing" and the polymorphic store action of
--     GTPLC.
--   * Provides intrinsically scoped traces and actions of store changes on
--     stores, types, consistency evidence, and terms.

open import Data.Nat as Nat using (ℕ; _+_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import TyStore
open import Consistency
open import Conversion
open import Primitives
open import CastTerms

------------------------------------------------------------------------
-- Store changes
------------------------------------------------------------------------

data StoreChange : TyCtx → TyCtx → Set where
  keep : ∀ {Δ} → StoreChange Δ Δ
  bind : ∀ {Δ} → Ty Δ → StoreChange Δ (Nat.suc Δ)

applyStore : ∀ {Δ Δ′}
  → StoreChange Δ Δ′
  → TyStore Δ
  → TyStore Δ′
applyStore keep Σ = Σ
applyStore (bind A) Σ = store-bind Σ A

applyTy : ∀ {Δ Δ′} → StoreChange Δ Δ′ → Ty Δ → Ty Δ′
applyTy keep A = A
applyTy (bind B) A = ⇑ᵗ A

applyTerm : ∀ {Δ Δ′} → StoreChange Δ Δ′ → Term Δ → Term Δ′
applyTerm keep M = M
applyTerm (bind A) M = ⇑ᵗᵐ M

applyConsistency : ∀ {Δ Δ′} {A B : Ty Δ}
  → (χ : StoreChange Δ Δ′)
  → A ∼ B
  → applyTy χ A ∼ applyTy χ B
applyConsistency keep c = c
applyConsistency (bind A) c = renameᶜ Fin.suc c

applyVar : ∀ {Δ Δ′}
  → StoreChange Δ Δ′
  → TyVar Δ
  → TyVar Δ′
applyVar keep X = X
applyVar (bind A) X = Fin.suc X

syntax applyStore χ Σ = χ ▷ˢ Σ
syntax applyTy χ A = χ ▷ᵗ A
syntax applyTerm χ M = χ ▷ᵀ M
syntax applyConsistency χ c = χ ▷ᶜ c

data StoreChanges : TyCtx → TyCtx → Set where
  [] : ∀ {Δ} → StoreChanges Δ Δ
  _∷_ : ∀ {Δ Δ′ Δ″}
    → StoreChange Δ Δ′
    → StoreChanges Δ′ Δ″
    → StoreChanges Δ Δ″

infixr 5 _∷_

applyStores : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → TyStore Δ
  → TyStore Δ′
applyStores [] Σ = Σ
applyStores (χ ∷ χs) Σ = applyStores χs (applyStore χ Σ)

applyTys : ∀ {Δ Δ′} → StoreChanges Δ Δ′ → Ty Δ → Ty Δ′
applyTys [] A = A
applyTys (χ ∷ χs) A = applyTys χs (applyTy χ A)

applyTerms : ∀ {Δ Δ′} → StoreChanges Δ Δ′ → Term Δ → Term Δ′
applyTerms [] M = M
applyTerms (χ ∷ χs) M = applyTerms χs (applyTerm χ M)

syntax applyStores χs Σ = χs ▶ˢ Σ
syntax applyTys χs A = χs ▶ᵗ A
syntax applyTerms χs M = χs ▶ᵀ M

------------------------------------------------------------------------
-- Interpreting consistency environments
------------------------------------------------------------------------

infix 4 _⟪_⟫_

data _⟪_⟫_ {Δ : TyCtx} (M : Term Δ) :
    ∀ {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B
    → Term Δ
    → Set where

  cast-id : ∀ {μ : Env∼ Δ} {A : Ty Δ} {a : Atom A}
      -----------------
    → M ⟪ id∼ {μ = μ} a ⟫ M

  cast-⇒ : ∀ {μ : Env∼ Δ} {A A′ B B′ : Ty Δ}
      {c : μ ⊢ A ∼ A′} {c′ : flipᵐ μ ⊢ A′ ∼ A}
      {d : μ ⊢ B ∼ B′} {P Q : Term Δ}
    → c′ ≡ sym∼ c
    → (` Nat.zero) ⟪ c′ ⟫ P
    → (rename Nat.suc M · P) ⟪ d ⟫ Q
      -----------------------------------
    → M ⟪ ⇒∼⇒ c d ⟫ ƛ Q

  cast-∀ : ∀ {μ : Env∼ Δ} {A B : Ty (Nat.suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B} {N : Term (Nat.suc Δ)}
    → ((⇑ᵗᵐ M) • ＇ Fin.zero) ⟪ c ⟫ N
      --------------------------
    → M ⟪ ∀∼∀ c ⟫ Λ N

  cast-tag : ∀ {μ : Env∼ Δ} {A G : Ty Δ}
      {g : Groundʳ G} {c : μ ⊢ A ∼ G} {N : Term Δ}
    → M ⟪ c ⟫ N
      ---------------------------------------------
    → M ⟪ tag g c ⟫ N ⟨ tag g (idᵍ g) ⟩

  cast-untag : ∀ {μ : Env∼ Δ} {G B : Ty Δ}
      {g : Groundʳ G} {c : μ ⊢ G ∼ B} {N : Term Δ}
    → M ⟨ untag g (idᵍ g) ⟩ ⟪ c ⟫ N
      ---------------------------------------------
    → M ⟪ untag g c ⟫ N

  cast-X∼★ : ∀ {μ : Env∼ Δ} {X : TyVar Δ}
      {eq : μ X ≡ X∼★}
      ---------------------------
    → M ⟪ X∼★ {μ = μ} {X = X} eq ⟫ reveal M (↑-unseal X)

  cast-★∼X : ∀ {μ : Env∼ Δ} {X : TyVar Δ}
      {eq : μ X ≡ ★∼X}
      ---------------------------
    → M ⟪ ★∼X {μ = μ} {X = X} eq ⟫ conceal M (↓-seal X)

  cast-gen : ∀ {μ : Env∼ Δ} {A : Ty Δ}
      {B : Ty (Nat.suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      {Bnv : NonVar B} {z∈B : Fin.zero ∈ᵗ B} {N : Term (Nat.suc Δ)}
    → ⇑ᵗᵐ M ⟪ c ⟫ N
      ---------------------------------
    → M ⟪ ∼∀ c Bnv z∈B ⟫ Λ N

------------------------------------------------------------------------
-- Factoring eager checks out of polymorphic casts
------------------------------------------------------------------------

data GroundGen : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {B : Ty Δ}
    → (c : μ ⊢ ★ ∼ B)
    → (c′ : μ ⊢ (★ ⇒ ★) ∼ B)
    → Set where

  ground-gen-⇒ : ∀ {Δ μ} {A B : Ty Δ}
      {c : μ ⊢ ★ ∼ A} {d : μ ⊢ ★ ∼ B}
    → GroundGen (untag g-⇒ (⇒∼⇒ c d)) (⇒∼⇒ c d)

  ground-gen-∀ : ∀ {Δ μ} {A : Ty Δ} {B : Ty (Nat.suc Δ)}
      {c : genᵐ μ ⊢ ★ ∼ B}
      {c′ : genᵐ μ ⊢ (★ ⇒ ★) ∼ B}
      {Bnv : NonVar B} {z∈B : Fin.zero ∈ᵗ B}
    → GroundGen c c′
    → GroundGen (∼∀ c Bnv z∈B) (∼∀ c′ Bnv z∈B)

groundGen-safe : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {B : Ty Δ}
    {c : μ ⊢ ★ ∼ B} {c′ : μ ⊢ (★ ⇒ ★) ∼ B}
  → GroundGen c c′
  → GenSafe c′
groundGen-safe ground-gen-⇒ = safe-⇒
groundGen-safe (ground-gen-∀ factor) = safe-gen (groundGen-safe factor)

data GroundInst : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A : Ty Δ}
    → (c : μ ⊢ A ∼ ★)
    → (c′ : μ ⊢ A ∼ (★ ⇒ ★))
    → Set where

  ground-inst-⇒ : ∀ {Δ μ} {A B : Ty Δ}
      {c : μ ⊢ A ∼ ★} {d : μ ⊢ B ∼ ★}
    → GroundInst (tag g-⇒ (⇒∼⇒ c d)) (⇒∼⇒ c d)

  ground-inst-∀ : ∀ {Δ μ} {A : Ty (Nat.suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ★}
      {c′ : instᵐ μ ⊢ A ∼ (★ ⇒ ★)}
      {Anv : NonVar A} {z∈A : Fin.zero ∈ᵗ A}
    → GroundInst c c′
    → GroundInst (∀∼ c Anv z∈A) (∀∼ c′ Anv z∈A)

------------------------------------------------------------------------
-- Pure one-step reduction
------------------------------------------------------------------------

infix 2 _—→_

data _—→_ {Δ : TyCtx} : Term Δ → Term Δ → Set where

  δ-⊕ : ∀ {m n : ℕ}
      -------------------------------------------------
    → $ (κℕ m) ⊕[ addℕ ] $ (κℕ n) —→ $ (κℕ (m + n))

  β : ∀ {N V : Term Δ}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  β-id : ∀ {V : Term Δ} {A : Ty Δ} {a : Atom A}
    → Value V
      -----------------
    → V ⟨ id∼ a ⟩ —→ V

  β-⇒ : ∀ {V W : Term Δ} {A A′ B B′ : Ty Δ}
      {c : A ∼ A′} {c′ : A′ ∼ A} {d : B ∼ B′}
    → Value V
    → Value W
    → c′ ≡ symᶜ c
      ------------------------------------------------
    → (V ⟨ ⇒∼⇒ c d ⟩) · W —→ (V · (W ⟨ c′ ⟩)) ⟨ d ⟩

  β-∀ : ∀ {V : Term Δ} {A B : Ty (Nat.suc Δ)} {C : Ty Δ}
      {c : extᵐ idᶜ ⊢ A ∼ B} {d : A [ C ]ᵗ ∼ B [ C ]ᵗ}
    → Value V
    → d ≡ c [ C ]ᶜ
      --------------------------------------------------------
    → (V ⟨ ∀∼∀ c ⟩) • C —→ (V • C) ⟨ d ⟩

  expand-∀ : ∀ {V : Term Δ} {B : Ty (Nat.suc Δ)}
      {c : genᵐ idᶜ ⊢ ★ ∼ B} {Bnv : NonVar B}
      {c′ : genᵐ idᶜ ⊢ (★ ⇒ ★) ∼ B}
      {z∈B : Fin.zero ∈ᵗ B}
    → Value V
    → GroundGen c c′
      -----------------------------------------------------------------------
    → V ⟨ ∼∀ c Bnv z∈B ⟩ —→
        V ⟨ untag g-⇒ (idᵍ g-⇒) ⟩ ⟨ ∼∀ c′ Bnv z∈B ⟩

  ground-∀ : ∀ {V : Term Δ} {A : Ty (Nat.suc Δ)}
      {c : instᵐ idᶜ ⊢ A ∼ ★} {Anv : NonVar A}
      {c′ : instᵐ idᶜ ⊢ A ∼ (★ ⇒ ★)}
      {z∈A : Fin.zero ∈ᵗ A}
    → Value V
    → GroundInst c c′
      ---------------------------------------------------------------------
    → V ⟨ ∀∼ c Anv z∈A ⟩ —→
        V ⟨ ∀∼ c′ Anv z∈A ⟩ ⟨ tag g-⇒ (idᵍ g-⇒) ⟩

  ground : ∀ {V : Term Δ} {A G : Ty Δ}
      {g : Groundʳ G} {c : A ∼ G}
    → Value V
    → A ≢ G
      ------------------------------------------------
    → V ⟨ tag g c ⟩ —→ V ⟨ c ⟩ ⟨ tag g (idᵍ g) ⟩

  expand : ∀ {V : Term Δ} {G B : Ty Δ}
      {g : Groundʳ G} {c : G ∼ B}
    → Value V
    → G ≢ B
      ----------------------------------------------------------
    → V ⟨ untag g c ⟩ —→ V ⟨ untag g (idᵍ g) ⟩ ⟨ c ⟩

  tag-untag : ∀ {V : Term Δ} {G : Ty Δ}
      {g : Groundʳ G}
    → Value V
      ------------------------------------------------------------
    → V ⟨ tag g (idᵍ g) ⟩ ⟨ untag g (idᵍ g) ⟩ —→ V

  tag-untag-bad : ∀ {V : Term Δ} {G H : Ty Δ}
      {g : Groundʳ G} {h : Groundʳ H}
    → Value V
    → G ≢ H
      ------------------------------------------------------------
    → V ⟨ tag g (idᵍ g) ⟩ ⟨ untag h (idᵍ h) ⟩ —→ blame

  β-reveal-⇒ : ∀ {V W : Term Δ} {c : Conv↓ Δ} {d : Conv↑ Δ}
    → Value V
    → Value W
      ---------------------------------------------------------
    → reveal V (↑-⇒ c d) · W —→ reveal (V · conceal W c) d

  β-conceal-⇒ : ∀ {V W : Term Δ} {c : Conv↑ Δ} {d : Conv↓ Δ}
    → Value V
    → Value W
      ---------------------------------------------------------
    → conceal V (↓-⇒ c d) · W —→ conceal (V · reveal W c) d

  id-reveal : ∀ {V : Term Δ} {A : Ty Δ}
    → Value V
      -------------------------
    → reveal V (↑-id A) —→ V

  id-conceal : ∀ {V : Term Δ} {A : Ty Δ}
    → Value V
      --------------------------
    → conceal V (↓-id A) —→ V

  conceal-reveal : ∀ {V : Term Δ} {X : TyVar Δ}
    → Value V
      --------------------------------------------------
    → reveal (conceal V (↓-seal X)) (↑-unseal X) —→ V

  blame-·₁ : ∀ {M : Term Δ}
      ------------------
    → blame · M —→ blame

  blame-·₂ : ∀ {V : Term Δ}
    → Value V
      ------------------
    → V · blame —→ blame

  blame-• : ∀ {A : Ty Δ}
      ------------------
    → blame • A —→ blame

  blame-⟨⟩ : ∀ {A B : Ty Δ} {c : A ∼ B}
      ------------------
    → blame ⟨ c ⟩ —→ blame

  blame-reveal : ∀ {c : Conv↑ Δ}
      -----------------------
    → reveal blame c —→ blame

  blame-conceal : ∀ {c : Conv↓ Δ}
      ------------------------
    → conceal blame c —→ blame

  blame-⊕₁ : ∀ {M : Term Δ} {op : Prim}
      ---------------------------
    → blame ⊕[ op ] M —→ blame

  blame-⊕₂ : ∀ {V : Term Δ} {op : Prim}
    → Value V
      ---------------------------
    → V ⊕[ op ] blame —→ blame

------------------------------------------------------------------------
-- Pure multi-step reduction
------------------------------------------------------------------------

infix 2 _—↠_
infixr 2 _—→⟨_⟩_
infix 3 _∎

data _—↠_ {Δ : TyCtx} : Term Δ → Term Δ → Set where
  _∎ : (M : Term Δ) → M —↠ M
  _—→⟨_⟩_ : (L : Term Δ) {M N : Term Δ}
    → L —→ M
    → M —↠ N
    → L —↠ N

------------------------------------------------------------------------
-- Store-changing one-step reduction and evaluation contexts
------------------------------------------------------------------------

infix 2 _—→[_]_

data _—→[_]_ : ∀ {Δ Δ′}
    → Term Δ → StoreChange Δ Δ′ → Term Δ′ → Set where

  pure-step : ∀ {Δ} {M M′ : Term Δ}
    → M —→ M′
      -----------------
    → M —→[ keep ] M′

  β-Λ : ∀ {Δ} {A : Ty Δ} {V : Term (Nat.suc Δ)}
    → Value V
      -----------------------
    → (Λ V) • A —→[ bind A ] V

  β-inst : ∀ {Δ} {V : Term Δ} {A : Ty (Nat.suc Δ)}
      {B : Ty Δ} {c : instᵐ idᶜ ⊢ A ∼ ⇑ᵗ B}
      {Anv : NonVar A} {z∈A : Fin.zero ∈ᵗ A}
      {N : Term (Nat.suc Δ)}
    → Value V
    → B ≢ ★
    → ((⇑ᵗᵐ V) • ＇ Fin.zero) ⟪ c ⟫ N
      -----------------------------------
    → V ⟨ ∀∼ c Anv z∈A ⟩ —→[ bind ★ ] N

  β-gen : ∀ {Δ} {V : Term Δ} {A C : Ty Δ}
      {B : Ty (Nat.suc Δ)} {c : genᵐ idᶜ ⊢ ⇑ᵗ A ∼ B}
      {Bnv : NonVar B} {z∈B : Fin.zero ∈ᵗ B}
      {N : Term (Nat.suc Δ)}
    → Value V
    → A ≢ ★
    → GenSafe c
    → ⇑ᵗᵐ V ⟪ c ⟫ N
      -------------------------------------
    → (V ⟨ ∼∀ c Bnv z∈B ⟩) • C —→[ bind C ] N

  β-reveal-∀ : ∀ {Δ} {V : Term Δ} {A : Ty Δ}
      {c : Conv↑ (Nat.suc Δ)}
    → Value V
      -------------------------------------------------
    → (reveal V (↑-∀ c)) • A —→[ bind A ]
        reveal ((⇑ᵗᵐ V) • ＇ Fin.zero) c

  β-conceal-∀ : ∀ {Δ} {V : Term Δ} {A : Ty Δ}
      {c : Conv↓ (Nat.suc Δ)}
    → Value V
      --------------------------------------------------
    → (conceal V (↓-∀ c)) • A —→[ bind A ]
        conceal ((⇑ᵗᵐ V) • ＇ Fin.zero) c

  ξ-·₁ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {L M : Term Δ} {L′ M′ : Term Δ′}
    → L —→[ χ ] L′
    → M′ ≡ applyTerm χ M
      ----------------------------------
    → L · M —→[ χ ] L′ · M′

  ξ-·₂ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {V M : Term Δ} {V′ M′ : Term Δ′}
    → Value V
    → M —→[ χ ] M′
    → V′ ≡ applyTerm χ V
      ----------------------------------
    → V · M —→[ χ ] V′ · M′

  ξ-• : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {A : Ty Δ} {A′ : Ty Δ′}
    → M —→[ χ ] M′
    → A′ ≡ applyTy χ A
      ----------------------------------
    → M • A —→[ χ ] M′ • A′

  ξ-⟨⟩ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {A B : Ty Δ} {c : A ∼ B}
      {c′ : applyTy χ A ∼ applyTy χ B}
    → M —→[ χ ] M′
    → c′ ≡ applyConsistency χ c
      ----------------------------------
    → M ⟨ c ⟩ —→[ χ ] M′ ⟨ c′ ⟩

  ξ-reveal : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {c : Conv↑ Δ}
      {c′ : Conv↑ Δ′}
    → M —→[ χ ] M′
    → c′ ≡ rename↑ (applyVar χ) c
      ----------------------------------
    → reveal M c —→[ χ ] reveal M′ c′

  ξ-conceal : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {c : Conv↓ Δ}
      {c′ : Conv↓ Δ′}
    → M —→[ χ ] M′
    → c′ ≡ rename↓ (applyVar χ) c
      ----------------------------------
    → conceal M c —→[ χ ] conceal M′ c′

  ξ-⊕₁ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {L M : Term Δ} {L′ M′ : Term Δ′} {op : Prim}
    → L —→[ χ ] L′
    → M′ ≡ applyTerm χ M
      ------------------------------------------------
    → L ⊕[ op ] M —→[ χ ] L′ ⊕[ op ] M′

  ξ-⊕₂ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {V M : Term Δ} {V′ M′ : Term Δ′} {op : Prim}
    → Value V
    → M —→[ χ ] M′
    → V′ ≡ applyTerm χ V
      ------------------------------------------------
    → V ⊕[ op ] M —→[ χ ] V′ ⊕[ op ] M′

------------------------------------------------------------------------
-- Store-changing multi-step reduction
------------------------------------------------------------------------

infix 2 _—↠[_]_

data _—↠[_]_ : ∀ {Δ Δ′}
    → Term Δ → StoreChanges Δ Δ′ → Term Δ′ → Set where

  ↠-refl : ∀ {Δ} {M : Term Δ}
      -------------
    → M —↠[ [] ] M

  ↠-step : ∀ {Δ Δ′ Δ″} {M : Term Δ} {N : Term Δ′}
      {P : Term Δ″} {χ : StoreChange Δ Δ′}
      {χs : StoreChanges Δ′ Δ″}
    → M —→[ χ ] N
    → N —↠[ χs ] P
      ---------------------
    → M —↠[ χ ∷ χs ] P

infix 3 _∎[]
pattern _∎[] M = ↠-refl {M = M}

infixr 2 _—→[_]⟨_⟩_
pattern _—→[_]⟨_⟩_ L χ L—→M M—↠N =
  ↠-step {M = L} {χ = χ} L—→M M—↠N
