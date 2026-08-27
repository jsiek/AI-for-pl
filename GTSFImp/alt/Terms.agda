module alt.Terms where

-- File Charter:
--   * Defines the shift-free term syntax with anchored reveal binders and
--     conceal anti-binders.
--   * Defines values, scoped-variable classifications, representation
--     transport, and typing against the global append-only store.
--   * Provides annotated lambdas and structural single substitution that
--     stops at closed crossing interiors.
--   * Keeps forall-bound scoped variables out of store representations.

open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import TermCtx
open import Primitives
open import Consistency
open import alt.Store
open import alt.Conversion

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_˙_
infixl 7 _·_
infix  5 Λ_
infixl 7 _⦂∀_[_]
infixl 7 _⟨_⟩
infixl 7 _↑[_≔_]_ _↓[_≔_]_
infixl 6 _⊕[_]_
infix  9 `_

Var : Set
Var = ℕ

private
  variable
    Δ : TyCtx

data Term : TyCtx → Set where
  `_      : Var → Term Δ
  ƛ_˙_    : Ty Δ → Term Δ → Term Δ
  _·_     : Term Δ → Term Δ → Term Δ
  Λ_      : Term (suc Δ) → Term Δ
  _⦂∀_[_] : Term Δ → Ty (suc Δ) → Ty Δ → Term Δ
  $       : Const → Term Δ
  _⊕[_]_  : Term Δ → Prim → Term Δ → Term Δ
  _⟨_⟩    : Term Δ → {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Term Δ

  _↑[_≔_]_ : Term (suc Δ)
    → TyVar (suc Δ) → Name → Reveal → Term Δ

  _↓[_≔_]_ : Term Δ
    → TyVar (suc Δ) → Name → Conceal → Term (suc Δ)

  blame   : Term Δ

------------------------------------------------------------------------
-- Term-variable renaming
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term Δ → Term Δ
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ A ˙ M) = ƛ A ˙ rename (ext ρ) M
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (Λ M) = Λ (rename ρ M)
rename ρ (L ⦂∀ C [ A ]) = rename ρ L ⦂∀ C [ A ]
rename ρ ($ κ) = $ κ
rename ρ (L ⊕[ op ] M) = rename ρ L ⊕[ op ] rename ρ M
rename ρ (M ⟨ c ⟩) = rename ρ M ⟨ c ⟩
rename ρ (M ↑[ X ≔ α ] c) = rename ρ M ↑[ X ≔ α ] c
rename ρ (M ↓[ X ≔ α ] c) = rename ρ M ↓[ X ≔ α ] c
rename ρ blame = blame

-- Type-context weakening used only beneath an existing `Λ`
------------------------------------------------------------------------

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

-- Commuting an ambient insertion inward across a reveal.  At equal type variables,
-- the reveal's own type variable comes first.
underReveal : ∀ {n} → Fin (suc n) → Fin (suc n) → Fin (suc (suc n))
underReveal zero zero = suc zero
underReveal zero (suc Y) = zero
underReveal (suc X) zero = suc (suc X)
underReveal {n = suc n} (suc X) (suc Y) = suc (underReveal X Y)

weakenRevealTyVar : ∀ {n}
  → Fin (suc n) → Fin (suc n) → Fin (suc (suc n))
weakenRevealTyVar zero zero = zero
weakenRevealTyVar zero (suc Y) = suc (suc Y)
weakenRevealTyVar (suc X) zero = zero
weakenRevealTyVar {n = suc n} (suc X) (suc Y) =
  suc (weakenRevealTyVar X Y)

-- Commuting an insertion outward across a conceal.  The inserted type variable is
-- placed before the conceal type variable when they meet at the same outer gap.
outsideConceal : ∀ {n}
  → Fin (suc (suc n)) → Fin (suc n) → Fin (suc n)
outsideConceal zero Y = zero
outsideConceal (suc X) zero = X
outsideConceal {n = suc n} (suc X) (suc Y) = suc (outsideConceal X Y)

weakenConcealTyVar : ∀ {n}
  → Fin (suc (suc n)) → Fin (suc n) → Fin (suc (suc n))
weakenConcealTyVar zero Y = suc Y
weakenConcealTyVar (suc X) zero = zero
weakenConcealTyVar {n = suc n} (suc X) (suc Y) =
  suc (weakenConcealTyVar X Y)

weakenᵗᵐ : ∀ {n} (X : TyVar (suc n)) → Term n → Term (suc n)
weakenᵗᵐ X (` x) = ` x
weakenᵗᵐ X (ƛ A ˙ M) = ƛ wkᵗ X A ˙ weakenᵗᵐ X M
weakenᵗᵐ X (L · M) = weakenᵗᵐ X L · weakenᵗᵐ X M
weakenᵗᵐ X (Λ M) = Λ (weakenᵗᵐ (suc X) M)
weakenᵗᵐ X (L ⦂∀ C [ A ]) =
  weakenᵗᵐ X L ⦂∀ wkᵗ (suc X) C [ wkᵗ X A ]
weakenᵗᵐ X ($ κ) = $ κ
weakenᵗᵐ X (L ⊕[ op ] M) = weakenᵗᵐ X L ⊕[ op ] weakenᵗᵐ X M
weakenᵗᵐ X (M ⟨ c ⟩) = weakenᵗᵐ X M ⟨ weakenConsistency X c ⟩
weakenᵗᵐ X (M ↑[ Y ≔ α ] c) =
  weakenᵗᵐ (underReveal X Y) M ↑[ weakenRevealTyVar X Y ≔ α ] c
weakenᵗᵐ X (M ↓[ Y ≔ α ] c) =
  weakenᵗᵐ (outsideConceal X Y) M ↓[ weakenConcealTyVar X Y ≔ α ] c
weakenᵗᵐ X blame = blame

removeVar : Var → Var → Var
removeVar zero zero = zero
removeVar zero (suc y) = y
removeVar (suc x) zero = zero
removeVar (suc x) (suc y) = suc (removeVar x y)

------------------------------------------------------------------------
-- Structural single substitution
------------------------------------------------------------------------

substAt : Var → Term Δ → Term Δ → Term Δ
substAt x V (` y) with Nat._≟_ x y
substAt x V (` .x) | yes refl = V
substAt x V (` y) | no x≠y = ` removeVar x y
substAt x V (ƛ A ˙ M) = ƛ A ˙ substAt (suc x) (rename suc V) M
substAt x V (L · M) = substAt x V L · substAt x V M
substAt x V (Λ M) = Λ (substAt x (weakenᵗᵐ zero V) M)
substAt x V (L ⦂∀ C [ A ]) = substAt x V L ⦂∀ C [ A ]
substAt x V ($ κ) = $ κ
substAt x V (L ⊕[ op ] M) = substAt x V L ⊕[ op ] substAt x V M
substAt x V (M ⟨ c ⟩) = substAt x V M ⟨ c ⟩
substAt x V (M ↑[ X ≔ α ] c) = M ↑[ X ≔ α ] c
substAt x V (M ↓[ X ≔ α ] c) = M ↓[ X ≔ α ] c
substAt x V blame = blame

infixl 8 _[_]
_[_] : Term Δ → Term Δ → Term Δ
M [ V ] = substAt zero V M

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data GenSafe : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  safe-⇒ : ∀ {Δ μ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → GenSafe (c ↦ d)

  safe-∀ : ∀ {Δ μ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
    → GenSafe (∀ᶜ c)

  safe-inst : ∀ {Δ μ} {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
    → (B≢★ : B ≢ ★)
    → GenSafe ((inst c) B≢★)

  safe-gen : ∀ {Δ μ} {A : Ty Δ} {B : Ty (suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → GenSafe ((gen c) A≢★)

data Inert : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  inj : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      ⦃ Gns : NonStar G ⦄
    → Inert {μ = μ} ((idᵍ {μ = μ} Gᵍ) !)

  fun : ∀ {Δ} {μ : Env∼ Δ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Inert (c ↦ d)

  all : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
    → Inert (∀ᶜ c)

  genᵥ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
      {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → Inert ((gen c) A≢★)

mutual
  data RevealValue {Δ : TyCtx} (V : Term Δ) : Reveal → Set where
    fun : ∀ {c d}
      → RevealValue V (c ↦↑ d)

    all : ∀ {c}
      → RevealValue V (`∀↑ c)

    delimiter : CanonicalInterior V
      → RevealValue V id↑

  data ConcealValue {Δ : TyCtx} (V : Term Δ) : Conceal → Set where
    seal : ConcealValue V alt.Conversion.seal

    fun : ∀ {c d}
      → ConcealValue V (c ↦↓ d)

    all : ∀ {c}
      → ConcealValue V (`∀↓ c)

    delimiter : CanonicalInterior V
      → ConcealValue V id↓

  data Value : ∀ {Δ : TyCtx} → Term Δ → Set where
    ƛ_˙_ : ∀ {Δ} (A : Ty Δ) (N : Term Δ) → Value (ƛ A ˙ N)
    Λ_ : ∀ {Δ} {V : Term (suc Δ)} → Value V → Value (Λ V)
    $ : ∀ {Δ} (κ : Const) → Value {Δ = Δ} ($ κ)

    _《_》 : ∀ {Δ} {V : Term Δ} {μ : Env∼ Δ} {A B : Ty Δ}
        {c : μ ⊢ A ∼ B}
      → Value V
      → Inert c
      → Value (V ⟨ c ⟩)

    _↑[_≔_]_ : ∀ {Δ} {V : Term (suc Δ)}
      → Value V
      → (X : TyVar (suc Δ))
      → (α : Name)
      → {c : Reveal}
      → RevealValue V c
      → Value (V ↑[ X ≔ α ] c)

    _↓[_≔_]_ : ∀ {Δ} {V : Term Δ}
      → Value V
      → (X : TyVar (suc Δ))
      → (α : Name)
      → {c : Conceal}
      → ConcealValue V c
      → Value (V ↓[ X ≔ α ] c)

  -- These are precisely the syntactic value shapes that can inhabit a
  -- non-base atomic region interior: a tag at ★, a seal at a scoped
  -- variable, or another identity reveal delimiter around either shape.
  data CanonicalInterior : ∀ {Δ : TyCtx} → Term Δ → Set where
    tagged : ∀ {Δ} {V : Term Δ} {μ : Env∼ Δ} {G : Ty Δ}
        ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
        ⦃ Gns : NonStar G ⦄
      → Value V
      → CanonicalInterior (V ⟨ (idᵍ Gᵍ) ! ⟩)

    sealed : ∀ {Δ} {V : Term Δ}
      → Value V
      → (X : TyVar (suc Δ))
      → (α : Name)
      → CanonicalInterior (V ↓[ X ≔ α ] alt.Conversion.seal)

    delimited : ∀ {Δ} {V : Term (suc Δ)}
      → CanonicalInterior V
      → (X : TyVar (suc Δ))
      → (α : Name)
      → CanonicalInterior (V ↑[ X ≔ α ] id↑)

canonical-value : ∀ {Δ} {V : Term Δ} → CanonicalInterior V → Value V
canonical-value (tagged Vᵥ) = Vᵥ 《 inj 》
canonical-value (sealed Vᵥ X α) = Vᵥ ↓[ X ≔ α ] seal
canonical-value (delimited Vᶜ X α) =
  canonical-value Vᶜ ↑[ X ≔ α ] delimiter Vᶜ

------------------------------------------------------------------------
-- Scoped-variable classifications and contexts
------------------------------------------------------------------------

data Binding (n : ℕ) : Set where
  ∀-bound : Binding n
  anchored : Fin n → Binding n

Bindings : TyCtx → ℕ → Set
Bindings Δ n = TyVar Δ → Binding n

insertBinding : ∀ {Δ n}
  → (X : TyVar (suc Δ))
  → Binding n
  → Bindings Δ n
  → Bindings (suc Δ) n
insertBinding zero b κ zero = b
insertBinding zero b κ (suc Y) = κ Y
insertBinding {Δ = suc Δ} (suc X) b κ zero = κ zero
insertBinding {Δ = suc Δ} (suc X) b κ (suc Y) =
  insertBinding X b (λ Z → κ (suc Z)) Y

wkᶜ : ∀ {Δ} → TyVar (suc Δ) → TermCtx Δ → TermCtx (suc Δ)
wkᶜ X = renameCtx (punchIn X)

------------------------------------------------------------------------
-- Relational transport from scoped variables to global names
------------------------------------------------------------------------

VarRel : TyCtx → ℕ → Set₁
VarRel Δ n = TyVar Δ → Ty n → Set

data BindingRel {Δ n} (κ : Bindings Δ n) : VarRel Δ n where
  map-anchor : ∀ {X α}
    → κ X ≡ anchored α
    → BindingRel κ X (＇ α)

data LiftRel {Δ n} (ρ : VarRel Δ n) : VarRel (suc Δ) (suc n) where
  map-zero : LiftRel ρ zero (＇ zero)

  map-suc : ∀ {X A B}
    → ρ X A
    → B ≡ ⇑ᵗ A
    → LiftRel ρ (suc X) B

data Transport {Δ n} (ρ : VarRel Δ n) : Ty Δ → Ty n → Set where
  transport-var : ∀ {X A}
    → ρ X A
    → Transport ρ (＇ X) A

  transport-base : ∀ {ι}
    → Transport ρ (‵ ι) (‵ ι)

  transport-star : Transport ρ ★ ★

  transport-fun : ∀ {A B A′ B′}
    → Transport ρ A A′
    → Transport ρ B B′
    → Transport ρ (A ⇒ B) (A′ ⇒ B′)

  transport-all : ∀ {A B}
    → Transport (LiftRel ρ) A B
    → Transport ρ (`∀ A) (`∀ B)

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

record Ctx : Set where
  constructor ⟨_,_,_,_,_⟩
  field
    Δᵉ : TyCtx
    sizeᵉ : ℕ
    κᵉ : Bindings Δᵉ sizeᵉ
    Σᵉ : Store sizeᵉ
    Γᵉ : TermCtx Δᵉ

open Ctx public

infixl 5 _,ᶜ_

_,ᶜ_ : (Γ : Ctx) → Ty (Δᵉ Γ) → Ctx
⟨ Δ , n , κ , Σ , Γ ⟩ ,ᶜ A =
  ⟨ Δ , n , κ , Σ , A ∷ Γ ⟩

∀-ctx : Ctx → Ctx
∀-ctx ⟨ Δ , n , κ , Σ , Γ ⟩ =
  ⟨ suc Δ , n , insertBinding zero ∀-bound κ , Σ , wkᶜ zero Γ ⟩

-- The classifier and store are extended beneath a crossing, but its interior
-- is always closed in the term context.
cross-ctx : (Γ : Ctx) (X : TyVar (suc (Δᵉ Γ))) {α : Name}
    {R : Ty (sizeᵉ Γ)}
  → α ⦂ R ∈ Σᵉ Γ
  → Ctx
cross-ctx ⟨ Δ , n , κ , Σ , Γ ⟩ X p =
  ⟨ suc Δ , n , insertBinding X (anchored (lookup-name p)) κ ,
    Σ , [] ⟩

infix 4 _∋ᵗ_⦂_
infix 4 _⊢_⦂_

_∋ᵗ_⦂_ : (Γ : Ctx) → Var → Ty (Δᵉ Γ) → Set
Γ ∋ᵗ x ⦂ A = TermCtx._∋_⦂_ (Γᵉ Γ) x A

data _⊢_⦂_ : (Γ : Ctx) → Term (Δᵉ Γ) → Ty (Δᵉ Γ) → Set where
  ⊢` : ∀ {Γ x A}
    → Γ ∋ᵗ x ⦂ A
    → Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {Γ A B M}
    → Γ ,ᶜ A ⊢ M ⦂ B
    → Γ ⊢ (ƛ A ˙ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {Γ A B L M}
    → Γ ⊢ L ⦂ (A ⇒ B)
    → Γ ⊢ M ⦂ A
    → Γ ⊢ (L · M) ⦂ B

  ⊢Λ : ∀ {Γ A M}
    → Value M
    → ∀-ctx Γ ⊢ M ⦂ A
    → Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {Γ C A L}
    → Γ ⊢ L ⦂ `∀ C
    → Γ ⊢ L ⦂∀ C [ A ] ⦂ C [ A ]ᵗ

  ⊢$ : ∀ {Γ} (κ : Const)
    → Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {Γ L M}
    → (op : Prim)
    → Γ ⊢ L ⦂ primArgTy op
    → Γ ⊢ M ⦂ primArgTy op
    → Γ ⊢ (L ⊕[ op ] M) ⦂ primResultTy op

  ⊢⟨⟩ : ∀ {Γ M A B μ}
    → Γ ⊢ M ⦂ A
    → (c : μ ⊢ A ∼ B)
    → Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢reveal : ∀ {Γ M A B X α R R′ c}
    → (p : α ⦂ R ∈ Σᵉ Γ)
    → Transport (BindingRel (κᵉ (cross-ctx Γ X p))) R′ R
    → ⊢↑[ X ⦂ R′ ] c ⦂ A ↝ wkᵗ X B
    → cross-ctx Γ X p ⊢ M ⦂ A
    → Γ ⊢ M ↑[ X ≔ α ] c ⦂ B

  ⊢conceal : ∀ {Γ} {Γ′ : TermCtx (suc (Δᵉ Γ))}
      {M A B X α R R′ c}
    → (p : α ⦂ R ∈ Σᵉ Γ)
    → Transport (BindingRel (κᵉ (cross-ctx Γ X p))) R′ R
    → ⊢↓[ X ⦂ R′ ] c ⦂ wkᵗ X A ↝ B
    → ⟨ Δᵉ Γ , sizeᵉ Γ , κᵉ Γ , Σᵉ Γ , [] ⟩ ⊢ M ⦂ A
    → ⟨ suc (Δᵉ Γ) , sizeᵉ Γ , κᵉ (cross-ctx Γ X p) ,
        Σᵉ Γ , Γ′ ⟩ ⊢ M ↓[ X ≔ α ] c ⦂ B

  ⊢blame : ∀ {Γ A}
    → Γ ⊢ blame ⦂ A
