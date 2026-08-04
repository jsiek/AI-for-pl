module Reduction where

-- File Charter:
--   * Pure and store-changing call-by-value reduction for CastTerms.
--   * Implements the ground-type cast rules of Figure 4 of "Refined
--     Criteria for Gradual Typing" and the polymorphic store action of
--     GTPLC.
--   * Eagerly blames casts that introduce the empty universal; eliminating
--     that type has no rule because no closed value can inhabit it.
--   * Provides intrinsically scoped traces and actions of store changes on
--     stores, types, consistency evidence, and terms.

import Data.Nat as Nat
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

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

-- A white triangle applies one store change; a black triangle below applies
-- a sequence. Superscripts identify the object being transported.
syntax applyStore χ Σ = χ ▷ˢ Σ

applyTy : ∀ {Δ Δ′} → StoreChange Δ Δ′ → Ty Δ → Ty Δ′
applyTy keep A = A
applyTy (bind B) A = ⇑ᵗ A

syntax applyTy χ A = χ ▷ᵗ A

applyBody : ∀ {Δ Δ′}
  → StoreChange Δ Δ′
  → Ty (Nat.suc Δ)
  → Ty (Nat.suc Δ′)
applyBody keep A = A
applyBody (bind B) A = renameᵗ (extᵗ Fin.suc) A

syntax applyBody χ A = χ ▷ᵇ A

applyTerm : ∀ {Δ Δ′} → StoreChange Δ Δ′ → Term Δ → Term Δ′
applyTerm keep M = M
applyTerm (bind A) M = ⇑ᵗᵐ M

syntax applyTerm χ M = χ ▷ᵀ M

applyEnv : ∀ {Δ Δ′}
  → StoreChange Δ Δ′
  → Env∼ Δ
  → Env∼ Δ′
applyEnv keep μ = μ
applyEnv (bind A) μ = extᵐ μ

syntax applyEnv χ μ = χ ▷ᵉ μ

applyConsistency : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (χ : StoreChange Δ Δ′)
  → μ ⊢ A ∼ B
  → χ ▷ᵉ μ ⊢ χ ▷ᵗ A ∼ χ ▷ᵗ B
applyConsistency keep c = c
applyConsistency (bind A) c = renameEnvᶜ Fin.suc (λ X → refl) c

syntax applyConsistency χ c = χ ▷ᶜ c

applyVar : ∀ {Δ Δ′}
  → StoreChange Δ Δ′
  → TyVar Δ
  → TyVar Δ′
applyVar keep X = X
applyVar (bind A) X = Fin.suc X

syntax applyVar χ X = χ ▷ᵛ X

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
syntax applyStores χs Σ = χs ▶ˢ Σ

applyStores [] Σ = Σ
applyStores (χ ∷ χs) Σ = χs ▶ˢ (χ ▷ˢ Σ)

applyTys : ∀ {Δ Δ′} → StoreChanges Δ Δ′ → Ty Δ → Ty Δ′
syntax applyTys χs A = χs ▶ᵗ A

applyTys [] A = A
applyTys (χ ∷ χs) A = χs ▶ᵗ (χ ▷ᵗ A)

applyTerms : ∀ {Δ Δ′} → StoreChanges Δ Δ′ → Term Δ → Term Δ′
syntax applyTerms χs M = χs ▶ᵀ M

applyTerms [] M = M
applyTerms (χ ∷ χs) M = χs ▶ᵀ (χ ▷ᵀ M)

------------------------------------------------------------------------
-- Pure one-step reduction
------------------------------------------------------------------------

infix 2 _—→_

data _—→_ {Δ : TyCtx} : Term Δ → Term Δ → Set where

  δ-⊕ : ∀ {op κ κ′ κ″}
    → δ op κ κ′ κ″
      ---------------------------------
    → $ κ ⊕[ op ] $ κ′ —→ $ κ″

  β : ∀ {N V : Term Δ}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  β-id : ∀ {V : Term Δ} {μ : Env∼ Δ} {A : Ty Δ} {a : Atom A}
    → Value V
      ------------------------
    → V ⟨ id {μ = μ} a ⟩ —→ V

  β-⇒ : ∀ {V W : Term Δ} {μ : Env∼ Δ}
      {A A′ B B′ : Ty Δ} {c : μ ⊢ A ∼ A′}
      {c′ : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Value V
    → Value W
    → c′ ≡ sym∼ c
      --------------------------------------------
    → (V ⟨ c ↦ d ⟩) · W —→ (V · (W ⟨ c′ ⟩)) ⟨ d ⟩

  β-∀ : ∀ {V : Term Δ} {μ : Env∼ Δ}
      {A B : Ty (Nat.suc Δ)} {C : Ty Δ}
      {c : extᵐ μ ⊢ A ∼ B} {d : μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ}
    → Value V
    → d ≡ c [ C ]ᶜ
      -----------------------------------------------
    → (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ C ] —→ (V ⦂∀ A [ C ]) ⟨ d ⟩

  ground : ∀ {V : Term Δ} {μ : Env∼ Δ} {A G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      {c : μ ⊢ A ∼ G}
      ⦃ Ans : NonStar A ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → A ≢ G
      ------------------------------------------------
    → V ⟨ c ! ⟩ —→ V ⟨ c ⟩ ⟨ (idᵍ Gᵍ) ! ⟩

  expand : ∀ {V : Term Δ} {μ : Env∼ Δ} {G B : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      {c : μ ⊢ G ∼ B}
      ⦃ Bns : NonStar B ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → G ≢ B
      ------------------------------------
    → V ⟨ ？ c ⟩ —→ V ⟨ ？ (idᵍ Gᵍ) ⟩ ⟨ c ⟩

  tag-untag : ∀ {V : Term Δ} {μ ν : Env∼ Δ}
      {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
      -----------------------------------
    → V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Gᵍ) ⟩ —→ V

  tag-untag-bad : ∀ {V : Term Δ} {μ ν : Env∼ Δ} {G H : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ Hᵍ : Ground H ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼H : ν ⊢★∼ H ⦄
      ⦃ Gns : NonStar G ⦄ ⦃ Hns : NonStar H ⦄
    → Value V
    → G ≢ H
      ------------------------------------------------------------
    → V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Hᵍ) ⟩ —→ blame

  blame-bot-intro : ∀ {V : Term Δ} {μ : Env∼ Δ}
    → Value V
      -------------------------
    → V ⟨ bot-intro {μ = μ} ⟩ —→ blame

  β-reveal-⇒ : ∀ {V W : Term Δ} {A A′ B B′}
      {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
    → Value V
    → Value W
      ---------------------------------------------------------
    → (V ↑ (c ↦↑ d)) · W —→ (V · (W ↓ c)) ↑ d

  β-conceal-⇒ : ∀ {V W : Term Δ} {A A′ B B′}
      {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
    → Value V
    → Value W
      ---------------------------------------------------------
    → (V ↓ (c ↦↓ d)) · W —→ (V · (W ↑ c)) ↓ d

  id-reveal : ∀ {V : Term Δ} {A : Ty Δ}
    → Value V
      -----------------------
    → V ↑ id↑ A —→ V

  id-conceal : ∀ {V : Term Δ} {A : Ty Δ}
    → Value V
      ------------------------
    → V ↓ id↓ A —→ V

  conceal-reveal : ∀ {V : Term Δ} {X : TyVar Δ} {R : Ty Δ}
    → Value V
      --------------------------------------------------
    → (V ↓ seal X R) ↑ unseal X R —→ V

  blame-·₁ : ∀ {M : Term Δ}
      ------------------
    → blame · M —→ blame

  blame-·₂ : ∀ {V : Term Δ}
    → Value V
      ------------------
    → V · blame —→ blame

  blame-• : ∀ {A : Ty Δ} {B : Ty (Nat.suc Δ)}
      --------------------------
    → blame ⦂∀ B [ A ] —→ blame

  blame-⟨⟩ : ∀ {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
      ---------------------
    → blame ⟨ c ⟩ —→ blame

  blame-reveal : ∀ {A B} {c : Conv↑ Δ A B}
      ------------------------
    → blame ↑ c —→ blame

  blame-conceal : ∀ {A B} {c : Conv↓ Δ A B}
      -------------------------
    → blame ↓ c —→ blame

  blame-⊕₁ : ∀ {M : Term Δ} {op : Prim}
      --------------------------
    → blame ⊕[ op ] M —→ blame

  blame-⊕₂ : ∀ {V : Term Δ} {op : Prim}
    → Value V
      -------------------------
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

  β-Λ : ∀ {Δ} {A : Ty Δ} {B : Ty (Nat.suc Δ)}
      {V : Term (Nat.suc Δ)}
    → Value V
      ---------------------------------------------
    → (Λ V) ⦂∀ B [ A ] —→[ bind A ] V ↑ 〖 0 , ⇑ᵗ A ↑ B 〗

  β-inst : ∀ {Δ} {V : Term Δ} {μ : Env∼ Δ}
      {A : Ty (Nat.suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : 0 ∈ᵗ A ⦄
    → Value V
    → (B≢★ : B ≢ ★)
      -----------------------------------------------------------------
    → V ⟨ (inst c) B≢★ ⟩ —→[ bind ★ ]
      ⇑ᵗᵐ V ⦂∀ (bind ★ ▷ᵇ A) [ ＇ 0 ] ↑ 〖 0 , ★ ↑ A 〗
        ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩

  β-gen : ∀ {Δ} {V : Term Δ} {μ : Env∼ Δ}
      {A C : Ty Δ} {B : Ty (Nat.suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : 0 ∈ᵗ B ⦄
    → Value V
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ---------------------------------------------------------------
    → (V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→[ bind C ]
      ⇑ᵗᵐ V ⟨ c ⟩ ↑ 〖 0 , ⇑ᵗ C ↑ B 〗

  β-reveal-∀ : ∀ {Δ} {V : Term Δ} {A : Ty Δ}
      {B C : Ty (Nat.suc Δ)}
      {c : Conv↑ (Nat.suc Δ) C B}
    → Value V
      -------------------------------------------------
    → (V ↑ `∀↑ c) ⦂∀ B [ A ] —→[ bind A ]
        ((⇑ᵗᵐ V ⦂∀ bind A ▷ᵇ C [ ＇ 0 ]) ↑ c
          ↑ 〖 0 , ⇑ᵗ A ↑ B 〗)

  β-conceal-∀ : ∀ {Δ} {V : Term Δ} {A : Ty Δ}
      {B C : Ty (Nat.suc Δ)}
      {c : Conv↓ (Nat.suc Δ) C B}
    → Value V
      --------------------------------------------------
    → (V ↓ `∀↓ c) ⦂∀ B [ A ] —→[ bind A ]
      (⇑ᵗᵐ V ⦂∀ bind A ▷ᵇ C [ ＇ 0 ] ↓ c
        ↑ 〖 0 , ⇑ᵗ A ↑ B 〗)

  ξ-·₁ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {L M : Term Δ} {L′ M′ : Term Δ′}
    → L —→[ χ ] L′
    → M′ ≡ χ ▷ᵀ M
      ----------------------------------
    → L · M —→[ χ ] L′ · M′

  ξ-·₂ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {V M : Term Δ} {V′ M′ : Term Δ′}
    → Value V
    → M —→[ χ ] M′
    → V′ ≡ χ ▷ᵀ V
      ----------------------------------
    → V · M —→[ χ ] V′ · M′

  ξ-• : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′}
      {A : Ty Δ} {A′ : Ty Δ′}
      {B : Ty (Nat.suc Δ)} {B′ : Ty (Nat.suc Δ′)}
    → M —→[ χ ] M′
    → B′ ≡ χ ▷ᵇ B
    → A′ ≡ χ ▷ᵗ A
      ----------------------------------
    → M ⦂∀ B [ A ] —→[ χ ] M′ ⦂∀ B′ [ A′ ]

  ξ-⟨⟩ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {μ : Env∼ Δ}
      {A B : Ty Δ} {c : μ ⊢ A ∼ B}
      {c′ : χ ▷ᵉ μ ⊢ χ ▷ᵗ A ∼ χ ▷ᵗ B}
    → M —→[ χ ] M′
    → c′ ≡ χ ▷ᶜ c
      --------------------------
    → M ⟨ c ⟩ —→[ χ ] M′ ⟨ c′ ⟩

  ξ-reveal : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {A B : Ty Δ}
      {c : Conv↑ Δ A B}
      {c′ : Conv↑ Δ′
        (renameᵗ (λ X → χ ▷ᵛ X) A)
        (renameᵗ (λ X → χ ▷ᵛ X) B)}
    → M —→[ χ ] M′
    → c′ ≡ rename↑ (λ X → χ ▷ᵛ X) c
      ------------------------------
    → M ↑ c —→[ χ ] M′ ↑ c′

  ξ-conceal : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {A B : Ty Δ}
      {c : Conv↓ Δ A B}
      {c′ : Conv↓ Δ′
        (renameᵗ (λ X → χ ▷ᵛ X) A)
        (renameᵗ (λ X → χ ▷ᵛ X) B)}
    → M —→[ χ ] M′
    → c′ ≡ rename↓ (λ X → χ ▷ᵛ X) c
      ----------------------------------
    → M ↓ c —→[ χ ] M′ ↓ c′

  ξ-⊕₁ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {L M : Term Δ} {L′ M′ : Term Δ′} {op : Prim}
    → L —→[ χ ] L′
    → M′ ≡ χ ▷ᵀ M
      ---------------------------------
    → L ⊕[ op ] M —→[ χ ] L′ ⊕[ op ] M′

  ξ-⊕₂ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {V M : Term Δ} {V′ M′ : Term Δ′} {op : Prim}
    → Value V
    → M —→[ χ ] M′
    → V′ ≡ χ ▷ᵀ V
      ---------------------------------
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

infixr 2 _—↠[_]⟨_⟩_
_—↠[_]⟨_⟩_ : ∀ {Δ Δ′} (M : Term Δ) {N : Term Δ′}
  → (χs : StoreChanges Δ Δ′)
  → M —↠[ χs ] N
  → N —↠[ [] ] N
  → M —↠[ χs ] N
M —↠[ χs ]⟨ M↠N ⟩ (_ ∎[]) = M↠N
