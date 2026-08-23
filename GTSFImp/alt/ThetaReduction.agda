module alt.ThetaReduction where

-- File Charter:
--   * Defines values, term-variable substitution, and pure one-step
--     reduction for the Θ-indexed alternative syntax.
--   * Regular-type weakening descends through every term form, including ν
--     and crossing interiors; term substitution stops at those boundaries
--     because their typing requires literal closed term contexts `[]`.
--   * This is the pure fragment only.  A ν is inert except for blame and
--     constant drops.  Floats, results, allocation, and ξ-ν belong to U4/U5.

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms

private
  variable
    Θ Θ′ : AnchorCtx
    Δ : TyCtx

------------------------------------------------------------------------
-- Term-variable renaming
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term Θ Δ → Term Θ Δ
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ A ˙ M) = ƛ A ˙ rename (ext ρ) M
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (Λ M) = Λ rename ρ M
rename ρ (L ⦂∀ C [ A ]) = rename ρ L ⦂∀ C [ A ]
rename ρ ($ κ) = $ κ
rename ρ (L ⊕[ op ] M) = rename ρ L ⊕[ op ] rename ρ M
rename ρ (M ⟨ c ⟩) = rename ρ M ⟨ c ⟩
rename ρ (M ↑[ Y ≔ α ] c) = M ↑[ Y ≔ α ] c
rename ρ (M ↓[ Y ≔ α ] c) = M ↓[ Y ≔ α ] c
rename ρ (ν[ A ] M) = ν[ A ] M
rename ρ blame = blame

------------------------------------------------------------------------
-- Regular-type weakening of terms
------------------------------------------------------------------------

-- This is the insertion instance of regular-type renaming needed beneath Λ.
-- Types and evidence follow the live renamings, slots follow the insertion,
-- and anchors and raw conversion shapes are unchanged.

insertEnv : ∀ {n} → TyVar (suc n) → Env∼ n → Env∼ (suc n)
insertEnv zero μ zero = X∼X
insertEnv zero μ (suc Y) = μ Y
insertEnv {n = suc n} (suc X) μ zero = μ zero
insertEnv {n = suc n} (suc X) μ (suc Y) =
  insertEnv X (λ Z → μ (suc Z)) Y

insertEnv-punchIn : ∀ {n} (X : TyVar (suc n)) (μ : Env∼ n) Y
  → insertEnv X μ (punchIn X Y) ≡ μ Y
insertEnv-punchIn zero μ Y = refl
insertEnv-punchIn {n = suc n} (suc X) μ zero = refl
insertEnv-punchIn {n = suc n} (suc X) μ (suc Y) =
  insertEnv-punchIn X (λ Z → μ (suc Z)) Y

weakenConsistency : ∀ {n} {μ : Env∼ n} {A B : Ty n}
  → (X : TyVar (suc n))
  → μ ⊢ A ∼ B
  → insertEnv X μ ⊢ wkᵗ X A ∼ wkᵗ X B
weakenConsistency {μ = μ} X c =
  rename∼ (punchIn X) (insertEnv-punchIn X μ) c

underReveal : ∀ {n} → Fin (suc n) → Fin (suc n) → Fin (suc (suc n))
underReveal zero zero = suc zero
underReveal zero (suc Y) = zero
underReveal (suc X) zero = suc (suc X)
underReveal {n = suc n} (suc X) (suc Y) = suc (underReveal X Y)

weakenRevealSlot : ∀ {n}
  → Fin (suc n)
  → Fin (suc n)
  → Fin (suc (suc n))
weakenRevealSlot zero zero = zero
weakenRevealSlot zero (suc Y) = suc (suc Y)
weakenRevealSlot (suc X) zero = zero
weakenRevealSlot {n = suc n} (suc X) (suc Y) =
  suc (weakenRevealSlot X Y)

outsideConceal : ∀ {n}
  → Fin (suc (suc n))
  → Fin (suc n)
  → Fin (suc n)
outsideConceal zero Y = zero
outsideConceal (suc X) zero = X
outsideConceal {n = suc n} (suc X) (suc Y) =
  suc (outsideConceal X Y)

weakenConcealSlot : ∀ {n}
  → Fin (suc (suc n))
  → Fin (suc n)
  → Fin (suc (suc n))
weakenConcealSlot zero Y = suc Y
weakenConcealSlot (suc X) zero = zero
weakenConcealSlot {n = suc n} (suc X) (suc Y) =
  suc (weakenConcealSlot X Y)

weakenᵗᵐ : ∀ {Θ n} (X : TyVar (suc n)) → Term Θ n → Term Θ (suc n)
weakenᵗᵐ X (` x) = ` x
weakenᵗᵐ X (ƛ A ˙ M) = ƛ wkᵗ X A ˙ weakenᵗᵐ X M
weakenᵗᵐ X (L · M) = weakenᵗᵐ X L · weakenᵗᵐ X M
weakenᵗᵐ X (Λ M) = Λ weakenᵗᵐ (suc X) M
weakenᵗᵐ X (L ⦂∀ C [ A ]) =
  weakenᵗᵐ X L ⦂∀ wkᵗ (suc X) C [ wkᵗ X A ]
weakenᵗᵐ X ($ κ) = $ κ
weakenᵗᵐ X (L ⊕[ op ] M) =
  weakenᵗᵐ X L ⊕[ op ] weakenᵗᵐ X M
weakenᵗᵐ X (M ⟨ c ⟩) = weakenᵗᵐ X M ⟨ weakenConsistency X c ⟩
weakenᵗᵐ X (M ↑[ Y ≔ α ] c) =
  weakenᵗᵐ (underReveal X Y) M ↑[ weakenRevealSlot X Y ≔ α ] c
weakenᵗᵐ X (M ↓[ Y ≔ α ] c) =
  weakenᵗᵐ (outsideConceal X Y) M ↓[ weakenConcealSlot X Y ≔ α ] c
weakenᵗᵐ X (ν[ A ] M) = ν[ wkᵗ X A ] weakenᵗᵐ X M
weakenᵗᵐ X blame = blame

removeVar : Var → Var → Var
removeVar zero zero = zero
removeVar zero (suc y) = y
removeVar (suc x) zero = zero
removeVar (suc x) (suc y) = suc (removeVar x y)

------------------------------------------------------------------------
-- Structural single substitution
------------------------------------------------------------------------

-- ν and crossing interiors are literally typed under `[]`; hence no outer
-- term variable can occur there, and substitution stops at each boundary.

substAt : Var → Term Θ Δ → Term Θ Δ → Term Θ Δ
substAt x V (` y) with Nat._≟_ x y
substAt x V (` .x) | yes refl = V
substAt x V (` y) | no x≠y = ` removeVar x y
substAt x V (ƛ A ˙ M) = ƛ A ˙ substAt (suc x) (rename suc V) M
substAt x V (L · M) = substAt x V L · substAt x V M
substAt x V (Λ M) = Λ substAt x (weakenᵗᵐ zero V) M
substAt x V (L ⦂∀ C [ A ]) = substAt x V L ⦂∀ C [ A ]
substAt x V ($ κ) = $ κ
substAt x V (L ⊕[ op ] M) = substAt x V L ⊕[ op ] substAt x V M
substAt x V (M ⟨ c ⟩) = substAt x V M ⟨ c ⟩
substAt x V (M ↑[ Y ≔ α ] c) = M ↑[ Y ≔ α ] c
substAt x V (M ↓[ Y ≔ α ] c) = M ↓[ Y ≔ α ] c
substAt x V (ν[ A ] M) = ν[ A ] M
substAt x V blame = blame

infixl 8 _[_]
_[_] : Term Θ Δ → Term Θ Δ → Term Θ Δ
M [ V ] = substAt zero V M

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data GenSafe : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  safe-⇒ : ∀ {Δ μ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
      ---------------------------------------------
    → GenSafe (c ↦ d)

  safe-∀ : ∀ {Δ μ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
      ----------------------
    → GenSafe (∀ᶜ c)

  safe-inst : ∀ {Δ μ} {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
    → (B≢★ : B ≢ ★)
      ---------------------------
    → GenSafe ((inst c) B≢★)

  safe-gen : ∀ {Δ μ} {A : Ty Δ} {B : Ty (suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
      --------------------------
    → GenSafe ((gen c) A≢★)

data Inert : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  inj : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      ⦃ Gns : NonStar G ⦄
      --------------------------------------
    → Inert {μ = μ} ((idᵍ {μ = μ} Gᵍ) !)

  fun : ∀ {Δ} {μ : Env∼ Δ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
      ---------------------------------------------
    → Inert (c ↦ d)

  all : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
      ----------------------
    → Inert (∀ᶜ c)

  genᵥ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
      {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ------------------------
    → Inert ((gen c) A≢★)

mutual
  data RevealValue {Θ : AnchorCtx} {Δ : TyCtx}
      (V : Term Θ Δ) : Reveal → Set where
    fun : ∀ {c d}
      ------------------------
      → RevealValue V (c ↦↑ d)

    all : ∀ {c}
      -----------------------
      → RevealValue V (`∀↑ c)

    delimiter :
      CanonicalInterior V
      ------------------------
      → RevealValue V id↑

  data ConcealValue {Θ : AnchorCtx} {Δ : TyCtx}
      (V : Term Θ Δ) : Conceal → Set where
    sealᵥ :
      -------------------------------
      ConcealValue V seal

    fun : ∀ {c d}
      -------------------------
      → ConcealValue V (c ↦↓ d)

    all : ∀ {c}
      ------------------------
      → ConcealValue V (`∀↓ c)

    delimiter :
      CanonicalInterior V
      -------------------------
      → ConcealValue V id↓

  data Value : ∀ {Θ : AnchorCtx} {Δ : TyCtx} → Term Θ Δ → Set where
    ƛ_˙_ : ∀ {Θ Δ} (A : Ty Δ) (N : Term Θ Δ)
      ------------------------------------------
      → Value (ƛ A ˙ N)

    Λ_ : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      → Value V
      ----------------
      → Value (Λ V)

    $ : ∀ {Θ Δ} (κ : Const)
      ---------------------------
      → Value {Θ = Θ} {Δ = Δ} ($ κ)

    _《_》 : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {A B : Ty Δ}
        {c : μ ⊢ A ∼ B}
      → Value V
      → Inert c
        ----------------
      → Value (V ⟨ c ⟩)

    _↑[_≔_]_ : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      → Value V
      → (X : TyVar (suc Δ))
      → (α : TyVar Θ)
      → {c : Reveal}
      → RevealValue V c
        --------------------------
      → Value (V ↑[ X ≔ α ] c)

    _↓[_≔_]_ : ∀ {Θ Δ} {V : Term Θ Δ}
      → Value V
      → (X : TyVar (suc Δ))
      → (α : TyVar Θ)
      → {c : Conceal}
      → ConcealValue V c
        --------------------------
      → Value (V ↓[ X ≔ α ] c)

  data CanonicalInterior : ∀ {Θ : AnchorCtx} {Δ : TyCtx}
      → Term Θ Δ → Set where
    tagged : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {G : Ty Δ}
        ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
        ⦃ Gns : NonStar G ⦄
      → Value V
        ------------------------------------------
      → CanonicalInterior (V ⟨ (idᵍ Gᵍ) ! ⟩)

    sealed : ∀ {Θ Δ} {V : Term Θ Δ}
      → Value V
      → (X : TyVar (suc Δ))
      → (α : TyVar Θ)
        --------------------------------------------------------
      → CanonicalInterior (V ↓[ X ≔ α ] seal)

    delimited : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      → CanonicalInterior V
      → (X : TyVar (suc Δ))
      → (α : TyVar Θ)
        ---------------------------------------------
      → CanonicalInterior (V ↑[ X ≔ α ] id↑)

canonical-value : ∀ {Θ Δ} {V : Term Θ Δ}
  → CanonicalInterior V
  → Value V
canonical-value (tagged Vᵥ) = Vᵥ 《 inj 》
canonical-value (sealed Vᵥ X α) = Vᵥ ↓[ X ≔ α ] sealᵥ
canonical-value (delimited Vᶜ X α) =
  canonical-value Vᶜ ↑[ X ≔ α ] delimiter Vᶜ

-- DEFERRED (U4): results/ν

------------------------------------------------------------------------
-- Pure one-step reduction
------------------------------------------------------------------------

infix 2 _—→_

data _—→_ : ∀ {Θ Δ} → Term Θ Δ → Term Θ Δ → Set where
  δ-⊕ : ∀ {Θ Δ} {op κ₁ κ₂ κ₃}
    → δ op κ₁ κ₂ κ₃
      -----------------------------------------
    → _—→_ {Θ = Θ} {Δ = Δ}
        ($ κ₁ ⊕[ op ] $ κ₂) ($ κ₃)

  β : ∀ {Θ Δ} {V N : Term Θ Δ} {A : Ty Δ}
    → Value V
      -----------------------------
    → (ƛ A ˙ N) · V —→ N [ V ]

  β-id : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {A : Ty Δ} {a : Atom A}
    → Value V
      ---------------------------------
    → V ⟨ id {μ = μ} a ⟩ —→ V

  β-⇒ : ∀ {Θ Δ} {V W : Term Θ Δ} {μ : Env∼ Δ}
      {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Value V
    → Value W
      ------------------------------------------------
    → (V ⟨ c ↦ d ⟩) · W —→ (V · (W ⟨ c ⟩)) ⟨ d ⟩

  β-∀ : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} {C : Ty Δ}
      {c : extᵐ μ ⊢ A ∼ B} {d : μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ}
    → Value V
    → d ≡ c [ C ]ᶜ
      -------------------------------------------------------
    → (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ C ] —→ (V ⦂∀ A [ C ]) ⟨ d ⟩

  ground : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {A G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      {c : μ ⊢ A ∼ G} ⦃ Ans : NonStar A ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → A ≢ G
      -------------------------------------------------
    → V ⟨ c ! ⟩ —→ V ⟨ c ⟩ ⟨ (idᵍ Gᵍ) ! ⟩

  expand : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {G B : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      {c : μ ⊢ G ∼ B} ⦃ Bns : NonStar B ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → G ≢ B
      -------------------------------------------------
    → V ⟨ ？ c ⟩ —→ V ⟨ ？ (idᵍ Gᵍ) ⟩ ⟨ c ⟩

  tag-untag : ∀ {Θ Δ} {V : Term Θ Δ} {μ ν : Env∼ Δ}
      {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
      -------------------------------------------------------
    → V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Gᵍ) ⟩ —→ V

  tag-untag-bad : ∀ {Θ Δ} {V : Term Θ Δ} {μ ν : Env∼ Δ}
      {G H : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ Hᵍ : Ground H ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼H : ν ⊢★∼ H ⦄
      ⦃ Gns : NonStar G ⦄ ⦃ Hns : NonStar H ⦄
    → Value V
    → G ≢ H
      ------------------------------------------------------------
    → V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Hᵍ) ⟩ —→ blame

  blame-bot-intro : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
    → Value V
      ------------------------------------------
    → V ⟨ bot-intro {μ = μ} ⟩ —→ blame

  β-reveal-⇒ : ∀ {Θ Δ}
      {V : Term Θ (suc Δ)} {W : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Conceal} {d : Reveal}
    → Value V
    → Value W
      ------------------------------------------------------------
    → (V ↑[ X ≔ α ] (c ↦↑ d)) · W —→
        (V · (W ↓[ X ≔ α ] c)) ↑[ X ≔ α ] d

  β-conceal-⇒ : ∀ {Θ Δ}
      {V : Term Θ Δ} {W : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Reveal} {d : Conceal}
    → Value V
    → Value W
      ------------------------------------------------------------
    → (V ↓[ X ≔ α ] (c ↦↓ d)) · W —→
        (V · (W ↑[ X ≔ α ] c)) ↓[ X ≔ α ] d

  id-cancel : ∀ {Θ Δ} {V : Term Θ Δ}
      {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
    → CanonicalInterior V
      -----------------------------------------------------
    → (V ↓[ X ≔ α ] id↓) ↑[ Y ≔ β ] id↑ —→ V

  id-reveal : ∀ {Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {κ}
      ---------------------------------------------
    → ($ κ) ↑[ X ≔ α ] id↑ —→ $ κ

  id-conceal : ∀ {Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {κ}
      ---------------------------------------------
    → ($ κ) ↓[ X ≔ α ] id↓ —→ $ κ

  conceal-reveal : ∀ {Θ Δ} {V : Term Θ Δ}
      {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
    → Value V
      ------------------------------------------------------------
    → (V ↓[ X ≔ α ] seal) ↑[ Y ≔ β ] unseal —→ V

  blame-·₁ : ∀ {Θ Δ} {M : Term Θ Δ}
      ------------------------
    → blame · M —→ blame

  blame-·₂ : ∀ {Θ Δ} {V : Term Θ Δ}
    → Value V
      ------------------------
    → V · blame —→ blame

  blame-• : ∀ {Θ : AnchorCtx} {Δ : TyCtx}
      {A : Ty Δ} {B : Ty (suc Δ)}
      ----------------------------------
    → _—→_ {Θ = Θ} (blame ⦂∀ B [ A ]) blame

  blame-⟨⟩ : ∀ {Θ Δ} {μ : Env∼ Δ} {A B : Ty Δ}
      {c : μ ⊢ A ∼ B}
      ------------------------
    → _—→_ {Θ = Θ} (blame ⟨ c ⟩) blame

  blame-reveal : ∀ {Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
      --------------------------------------
    → blame ↑[ X ≔ α ] c —→ blame

  blame-conceal : ∀ {Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
      --------------------------------------
    → blame ↓[ X ≔ α ] c —→ blame

  blame-⊕₁ : ∀ {Θ Δ} {M : Term Θ Δ} {op : Prim}
      --------------------------------
    → blame ⊕[ op ] M —→ blame

  blame-⊕₂ : ∀ {Θ Δ} {V : Term Θ Δ} {op : Prim}
    → Value V
      --------------------------------
    → V ⊕[ op ] blame —→ blame

  blame-ν : ∀ {Θ Δ} {A : Ty Δ}
      -------------------------
    → _—→_ {Θ = Θ} (ν[ A ] blame) blame

  const-ν : ∀ {Θ Δ} {A : Ty Δ} {κ : Const}
      ----------------------------
    → _—→_ {Θ = Θ} (ν[ A ] ($ κ)) ($ κ)

  ξ-·₁ : ∀ {Θ Δ} {L L′ M : Term Θ Δ}
    → L —→ L′
      --------------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Θ Δ} {V M M′ : Term Θ Δ}
    → Value V
    → M —→ M′
      --------------------
    → V · M —→ V · M′

  ξ-• : ∀ {Θ Δ} {M M′ : Term Θ Δ}
      {A : Ty Δ} {B : Ty (suc Δ)}
    → M —→ M′
      ------------------------------------
    → M ⦂∀ B [ A ] —→ M′ ⦂∀ B [ A ]

  ξ-⟨⟩ : ∀ {Θ Δ} {M M′ : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → M —→ M′
      ---------------------------
    → M ⟨ c ⟩ —→ M′ ⟨ c ⟩

  ξ-reveal : ∀ {Θ Δ} {M M′ : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → M —→ M′
      ------------------------------------------
    → M ↑[ X ≔ α ] c —→ M′ ↑[ X ≔ α ] c

  ξ-conceal : ∀ {Θ Δ} {M M′ : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → M —→ M′
      ------------------------------------------
    → M ↓[ X ≔ α ] c —→ M′ ↓[ X ≔ α ] c

  ξ-⊕₁ : ∀ {Θ Δ} {L L′ M : Term Θ Δ} {op : Prim}
    → L —→ L′
      --------------------------------
    → L ⊕[ op ] M —→ L′ ⊕[ op ] M

  ξ-⊕₂ : ∀ {Θ Δ} {V M M′ : Term Θ Δ} {op : Prim}
    → Value V
    → M —→ M′
      --------------------------------
    → V ⊕[ op ] M —→ V ⊕[ op ] M′

  -- DEFERRED (U4): ξ-ν
