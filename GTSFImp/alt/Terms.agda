module alt.Terms where

-- File Charter:
--   * Defines the shift-free term syntax with anchored reveal binders and
--     conceal anti-binders.
--   * Defines values, scoped-variable classifications, representation
--     transport, and typing against the global append-only store.
--   * Keeps forall-bound scoped variables out of store representations.

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TermCtx
open import Primitives
open import Consistency
open import alt.Store
open import alt.Conversion

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_
infixl 7 _·_
infix  5 Λ_
infixl 7 _⦂∀_[_]
infixl 7 _⟨_⟩
infixl 7 _↑⟨_≔_⟩_ _↓⟨_≔_⟩_
infixl 6 _⊕[_]_
infix  9 `_

Var : Set
Var = ℕ

private
  variable
    Δ : TyCtx

data Term : TyCtx → Set where
  `_      : Var → Term Δ
  ƛ_      : Term Δ → Term Δ
  _·_     : Term Δ → Term Δ → Term Δ
  Λ_      : Term (suc Δ) → Term Δ
  _⦂∀_[_] : Term Δ → Ty (suc Δ) → Ty Δ → Term Δ
  $       : Const → Term Δ
  _⊕[_]_  : Term Δ → Prim → Term Δ → Term Δ
  _⟨_⟩    : Term Δ → {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Term Δ

  _↑⟨_≔_⟩_ : ∀ {A : Ty (suc Δ)} {B : Ty Δ}
    → Term (suc Δ)
    → (X : TyVar (suc Δ))
    → Name
    → Conv↑ (suc Δ) A (wkᵗ X B)
    → Term Δ

  _↓⟨_≔_⟩_ : ∀ {A : Ty Δ} {B : Ty (suc Δ)}
    → Term Δ
    → (X : TyVar (suc Δ))
    → Name
    → Conv↓ (suc Δ) (wkᵗ X A) B
    → Term (suc Δ)

  blame   : Term Δ

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

data RevealValue : ∀ {Δ A B} → Conv↑ Δ A B → Set where
  fun : ∀ {Δ A A′ B B′}
      {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
    → RevealValue (c ↦↑ d)

  all : ∀ {Δ A B} {c : Conv↑ (suc Δ) A B}
    → RevealValue (`∀↑ c)

  delimiter-var : ∀ {Δ} {X : TyVar Δ}
    → RevealValue (id↑ (＇ X))

  delimiter-star : ∀ {Δ}
    → RevealValue (id↑ (★ {Δ}))

data ConcealValue : ∀ {Δ A B} → Conv↓ Δ A B → Set where
  seal : ∀ {Δ} {X : TyVar Δ} {R : Ty Δ}
    → ConcealValue (alt.Conversion.seal X R)

  fun : ∀ {Δ A A′ B B′}
      {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
    → ConcealValue (c ↦↓ d)

  all : ∀ {Δ A B} {c : Conv↓ (suc Δ) A B}
    → ConcealValue (`∀↓ c)

  delimiter-var : ∀ {Δ} {X : TyVar Δ}
    → ConcealValue (id↓ (＇ X))

  delimiter-star : ∀ {Δ}
    → ConcealValue (id↓ (★ {Δ}))

data Value : ∀ {Δ : TyCtx} → Term Δ → Set where
  ƛ_ : ∀ {Δ} (N : Term Δ) → Value (ƛ N)
  Λ_ : ∀ {Δ} {V : Term (suc Δ)} → Value V → Value (Λ V)
  $ : ∀ {Δ} (κ : Const) → Value {Δ = Δ} ($ κ)

  _《_》 : ∀ {Δ} {V : Term Δ} {μ : Env∼ Δ} {A B : Ty Δ}
      {c : μ ⊢ A ∼ B}
    → Value V
    → Inert c
    → Value (V ⟨ c ⟩)

  _↑⟨_≔_⟩_ : ∀ {Δ} {V : Term (suc Δ)} {A : Ty (suc Δ)}
      {B : Ty Δ}
    → Value V
    → (X : TyVar (suc Δ))
    → (α : Name)
    → {c : Conv↑ (suc Δ) A (wkᵗ X B)}
    → RevealValue c
    → Value (V ↑⟨ X ≔ α ⟩ c)

  _↓⟨_≔_⟩_ : ∀ {Δ′ : TyCtx} {V : Term Δ′} {A : Ty Δ′}
      {B : Ty (suc Δ′)}
    → Value V
    → (X : TyVar (suc Δ′))
    → (α : Name)
    → {c : Conv↓ (suc Δ′) (wkᵗ X A) B}
    → ConcealValue c
    → Value (V ↓⟨ X ≔ α ⟩ c)

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
-- Every recorded representation denotes the anchor's store entry
------------------------------------------------------------------------

mutual
  data Reps↑ {Δ n} (ρ : VarRel Δ n) (S : Ty n) :
      ∀ {A B} → Conv↑ Δ A B → Set where
    reps-unseal : ∀ {X R}
      → Transport ρ R S
      → Reps↑ ρ S (unseal X R)

    reps-↑⇒ : ∀ {A A′ B B′}
        {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
      → Reps↓ ρ S c
      → Reps↑ ρ S d
      → Reps↑ ρ S (c ↦↑ d)

    reps-↑∀ : ∀ {A B} {c : Conv↑ (suc Δ) A B}
      → Reps↑ (LiftRel ρ) (⇑ᵗ S) c
      → Reps↑ ρ S (`∀↑ c)

    reps-id↑ : ∀ {A} {a : Atom A}
      → Reps↑ ρ S (id↑ a)

  data Reps↓ {Δ n} (ρ : VarRel Δ n) (S : Ty n) :
      ∀ {A B} → Conv↓ Δ A B → Set where
    reps-seal : ∀ {X R}
      → Transport ρ R S
      → Reps↓ ρ S (alt.Conversion.seal X R)

    reps-↓⇒ : ∀ {A A′ B B′}
        {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
      → Reps↑ ρ S c
      → Reps↓ ρ S d
      → Reps↓ ρ S (c ↦↓ d)

    reps-↓∀ : ∀ {A B} {c : Conv↓ (suc Δ) A B}
      → Reps↓ (LiftRel ρ) (⇑ᵗ S) c
      → Reps↓ ρ S (`∀↓ c)

    reps-id↓ : ∀ {A} {a : Atom A}
      → Reps↓ ρ S (id↓ a)

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

cross-ctx : (Γ : Ctx) (X : TyVar (suc (Δᵉ Γ))) {α : Name}
    {R : Ty (sizeᵉ Γ)}
  → α ⦂ R ∈ Σᵉ Γ
  → Ctx
cross-ctx ⟨ Δ , n , κ , Σ , Γ ⟩ X p =
  ⟨ suc Δ , n , insertBinding X (anchored (lookup-name p)) κ ,
    Σ , wkᶜ X Γ ⟩

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
    → Γ ⊢ (ƛ M) ⦂ (A ⇒ B)

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

  ⊢reveal : ∀ {Γ M A B X α R}
      {c : Conv↑ (suc (Δᵉ Γ)) A (wkᵗ X B)}
    → (p : α ⦂ R ∈ Σᵉ Γ)
    → PivotStrict↑ X c
    → Reps↑ (BindingRel (κᵉ (cross-ctx Γ X p))) R c
    → cross-ctx Γ X p ⊢ M ⦂ A
    → Γ ⊢ M ↑⟨ X ≔ α ⟩ c ⦂ B

  ⊢conceal : ∀ {Γ M A B X α R}
      {c : Conv↓ (suc (Δᵉ Γ)) (wkᵗ X A) B}
    → (p : α ⦂ R ∈ Σᵉ Γ)
    → PivotStrict↓ X c
    → Reps↓ (BindingRel (κᵉ (cross-ctx Γ X p))) R c
    → Γ ⊢ M ⦂ A
    → cross-ctx Γ X p ⊢ M ↓⟨ X ≔ α ⟩ c ⦂ B

  ⊢blame : ∀ {Γ A}
    → Γ ⊢ blame ⦂ A
