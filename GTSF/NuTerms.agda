module NuTerms where

-- File Charter:
--   * Nu term syntax, values, renaming/substitution operations, and the
--     telescope-indexed typing judgment.
--   * Uses the redesigned `Types` telescope directly: ordinary type variables,
--     seals, and term variables all live in one de Bruijn context.
--   * Operational semantics and preservation/progress proofs live in
--     `NuReduction.agda` and `proof/Nu*.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (∃; ∃-syntax)

open import Types
open import Coercions
open import Primitives

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_
infix  5 Λ_
infixl 7 _·_
infixl 7 _•_
infixl 7 _⟨_⟩
infixl 6 _⊕[_]_
infix  9 `_

data Term : Set where
  `_      : Var → Term
  ƛ_      : Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _•_     : Term → SealVar → Term
  ν       : Ty → Term → Term
  $       : Const → Term
  _⊕[_]_  : Term → Prim → Term → Term
  _⟨_⟩    : Term → Coercion → Term
  blame   : Term

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : Term → Set where
  ƛ_ : (N : Term) → Value (ƛ N)
  Λ_ : {V : Term} → Value V → Value (Λ V)
  $ : (k : Const) → Value ($ k)
  _⟨_⟩ : {V : Term}{c : Coercion} → Value V → Inert c → Value (V ⟨ c ⟩)

------------------------------------------------------------------------
-- Type/seal renaming and type-variable substitution
------------------------------------------------------------------------

renameᵐ : Renameᵗ → Renameˢ → Term → Term
renameᵐ ρ σ (` x) = ` x
renameᵐ ρ σ (ƛ M) = ƛ renameᵐ ρ σ M
renameᵐ ρ σ (L · M) = renameᵐ ρ σ L · renameᵐ ρ σ M
renameᵐ ρ σ (Λ M) = Λ (renameᵐ (extᵗ ρ) σ M)
renameᵐ ρ σ (L • α) = renameᵐ ρ σ L • σ α
renameᵐ ρ σ (ν A N) = ν (rename ρ σ A) (renameᵐ ρ (extˢ σ) N)
renameᵐ ρ σ ($ κ) = $ κ
renameᵐ ρ σ (L ⊕[ op ] M) = renameᵐ ρ σ L ⊕[ op ] renameᵐ ρ σ M
renameᵐ ρ σ (M ⟨ c ⟩) = renameᵐ ρ σ M ⟨ renameᶜ ρ σ c ⟩
renameᵐ ρ σ blame = blame

renameᵗᵐ : Renameᵗ → Term → Term
renameᵗᵐ ρ = renameᵐ ρ idˢ

renameˢᵐ : Renameˢ → Term → Term
renameˢᵐ σ = renameᵐ idᵗ σ

⇑ᵗᵐ : Term → Term
⇑ᵗᵐ = renameᵗᵐ suc

⇑ˢᵐ : Term → Term
⇑ˢᵐ = renameˢᵐ suc

substᵗᵐ : Substᵗ → Term → Term
substᵗᵐ σ (` x) = ` x
substᵗᵐ σ (ƛ M) = ƛ substᵗᵐ σ M
substᵗᵐ σ (L · M) = substᵗᵐ σ L · substᵗᵐ σ M
substᵗᵐ σ (Λ M) = Λ (substᵗᵐ (extSubstᵗ σ) M)
substᵗᵐ σ (L • α) = substᵗᵐ σ L • α
substᵗᵐ σ (ν A N) = ν (substᵗ σ A) (substᵗᵐ (liftSubstᵗOverSeal σ) N)
substᵗᵐ σ ($ κ) = $ κ
substᵗᵐ σ (L ⊕[ op ] M) = substᵗᵐ σ L ⊕[ op ] substᵗᵐ σ M
substᵗᵐ σ (M ⟨ c ⟩) = substᵗᵐ σ M ⟨ substᵗᶜ σ c ⟩
substᵗᵐ σ blame = blame

infixl 8 _[_]ᵀ
_[_]ᵀ : Term → SealVar → Term
M [ α ]ᵀ = substᵗᵐ (singleTyEnv (`α α)) M

------------------------------------------------------------------------
-- Term-variable substitution
------------------------------------------------------------------------

Renameˣ : Set
Renameˣ = Var → Var

Substˣ : Set
Substˣ = Var → Term

extʳ : Renameˣ → Renameˣ
extʳ ρ zero = zero
extʳ ρ (suc x) = suc (ρ x)

renameˣᵐ : Renameˣ → Term → Term
renameˣᵐ ρ (` x) = ` (ρ x)
renameˣᵐ ρ (ƛ M) = ƛ renameˣᵐ (extʳ ρ) M
renameˣᵐ ρ (L · M) = renameˣᵐ ρ L · renameˣᵐ ρ M
renameˣᵐ ρ (Λ M) = Λ (renameˣᵐ ρ M)
renameˣᵐ ρ (L • α) = renameˣᵐ ρ L • α
renameˣᵐ ρ (ν A N) = ν A (renameˣᵐ ρ N)
renameˣᵐ ρ ($ κ) = $ κ
renameˣᵐ ρ (L ⊕[ op ] M) = renameˣᵐ ρ L ⊕[ op ] renameˣᵐ ρ M
renameˣᵐ ρ (M ⟨ c ⟩) = renameˣᵐ ρ M ⟨ c ⟩
renameˣᵐ ρ blame = blame

extˢˣ : Substˣ → Substˣ
extˢˣ σ zero = ` zero
extˢˣ σ (suc x) = renameˣᵐ suc (σ x)

↑ᵗᵐ : Substˣ → Substˣ
↑ᵗᵐ σ x = ⇑ᵗᵐ (σ x)

↑ˢᵐ : Substˣ → Substˣ
↑ˢᵐ σ x = ⇑ˢᵐ (σ x)

substˣᵐ : Substˣ → Term → Term
substˣᵐ σ (` x) = σ x
substˣᵐ σ (ƛ M) = ƛ substˣᵐ (extˢˣ σ) M
substˣᵐ σ (L · M) = substˣᵐ σ L · substˣᵐ σ M
substˣᵐ σ (Λ M) = Λ (substˣᵐ (↑ᵗᵐ σ) M)
substˣᵐ σ (L • α) = substˣᵐ σ L • α
substˣᵐ σ (ν A N) = ν A (substˣᵐ (↑ˢᵐ σ) N)
substˣᵐ σ ($ κ) = $ κ
substˣᵐ σ (L ⊕[ op ] M) = substˣᵐ σ L ⊕[ op ] substˣᵐ σ M
substˣᵐ σ (M ⟨ c ⟩) = substˣᵐ σ M ⟨ c ⟩
substˣᵐ σ blame = blame

singleEnv : Term → Substˣ
singleEnv N zero = N
singleEnv N (suc x) = ` x

infixl 8 _[_]
_[_] : Term → Term → Term
M [ N ] = substˣᵐ (singleEnv N) M

------------------------------------------------------------------------
-- Seal insertion
------------------------------------------------------------------------

-- `SealInsert Γ⁻ Γ⁺ α` says that `Γ⁺` is obtained from `Γ⁻` by inserting
-- one focused seal at de Bruijn index `α`.  The source telescope `Γ⁻` is the
-- scope used to type the head `L` of a type application, so `L` cannot mention
-- the focused seal: that seal simply is not in scope yet.  The target
-- telescope `Γ⁺` is the scope of the application `L • α`.
--
-- The `seal-above` constructor permits only seals to sit above the inserted
-- seal.  Its equality premise records the de Bruijn adjustment for those
-- intervening seals: a seal assignment `C` from the α-removed telescope becomes
-- `rename idᵗ (insertRenˢ i) C` after the focused seal is inserted below it.
-- Thus the seals above α are the same surrounding seals, with their assigned
-- types raised through the insertion rather than allowed to depend on α
-- directly.
mutual
  data SealInsert : Telescope → Telescope → SealVar → Set where
    here : ∀ {Γ A} →
      SealInsert Γ (sealᵉ A ∷ Γ) zero

    seal-above : ∀ {Γ⁻ Γ⁺ α C C↑}
      → (i : SealInsert Γ⁻ Γ⁺ α)
      → C↑ ≡ rename idᵗ (insertRenˢ i) C
       --------------------------------------------------------
      → SealInsert (sealᵉ C ∷ Γ⁻) (sealᵉ C↑ ∷ Γ⁺) (suc α)

  insertRenˢ :
    ∀ {Γ⁻ Γ⁺ α} →
    SealInsert Γ⁻ Γ⁺ α →
    Renameˢ
  insertRenˢ here β = suc β
  insertRenˢ (seal-above i eq) zero = zero
  insertRenˢ (seal-above i eq) (suc β) = suc (insertRenˢ i β)

openTyWithInsertedSeal :
  ∀ {Γ⁻ Γ⁺ α} →
  SealInsert Γ⁻ Γ⁺ α →
  Ty →
  Ty
openTyWithInsertedSeal here = openTyWithSeal
openTyWithInsertedSeal {α = α} i@(seal-above _ _) =
  subst (singleTyEnv (`α α)) (λ β → `α (insertRenˢ i β))

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

infix  4 _⊢_⦂_

data _⊢_⦂_ : Telescope → Term → Ty → Set₁ where

  ⊢` : ∀ {Γ x A}
     → Γ ∋ˣ x ⦂ A
      ----------------------
     → Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {Γ M A B}
     → WfTy Γ A
     → termᵉ A ∷ Γ ⊢ M ⦂ B
      ----------------------------
     → Γ ⊢ (ƛ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {Γ L M A B}
     → Γ ⊢ L ⦂ (A ⇒ B)
     → Γ ⊢ M ⦂ A
      -------------------------
     → Γ ⊢ (L · M) ⦂ B

  ⊢Λ : ∀ {Γ M A}
     → Value M
     → tyᵉ ∷ Γ ⊢ M ⦂ A
      ----------------------------
     → Γ ⊢ (Λ M) ⦂ (`∀ A)

  -- Type application is the de Bruijn/telescope version of the named rule
  --
  --   Γ ⊢ L : ∀X.B[X]
  --   --------------------
  --   Γ, α:=A ⊢ L α : B[α]
  --
  -- The premise types `L` in the α-removed telescope `Γ⁻`; the
  -- `SealInsert` witness inserts α into that telescope, possibly below a
  -- seal-only suffix.  This prevents `L` from referring to α by construction,
  -- while still letting the conclusion apply to an existing seal in `Γ⁺`.
  -- `L↑` and `T` remain bare metavariables in the conclusion so inversion does
  -- not have to unify through insertion/opening functions.
  ⊢• : ∀ {Γ⁻ Γ⁺ L B α L↑ T}
     → (i : SealInsert Γ⁻ Γ⁺ α)
     → Γ⁻ ⊢ L ⦂ (`∀ B)
     → WfTy (tyᵉ ∷ Γ⁻) B
     → L↑ ≡ renameᵐ idᵗ (insertRenˢ i) L
     → T ≡ openTyWithInsertedSeal i B
      ------------------------------------------------
     → Γ⁺ ⊢ L↑ • α ⦂ T

  ⊢ν : ∀ {Γ N A B}
     → WfTy Γ A
     → sealᵉ A ∷ Γ ⊢ N ⦂ ⇑ˢ B
      --------------------------------------------
     → Γ ⊢ (ν A N) ⦂ B

  ⊢$ : ∀ {Γ} (κ : Const)
      -------------------------------
     → Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {Γ L M}
     → Γ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Γ ⊢ M ⦂ (‵ `ℕ)
      -----------------------------------
     → Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢⟨⟩ : ∀ {Γ M A B c μ}
     → μ ∣ Γ ⊢ c ∶ A =⇒ B
     → Γ ⊢ M ⦂ A
      -------------------------
     → Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢blame : ∀ {Γ A}
     → WfTy Γ A
      ----------------------------
     → Γ ⊢ blame ⦂ A

⊢•-insert :
  ∀ {Γ L B A} →
  Γ ⊢ L ⦂ (`∀ B) →
  WfTy (tyᵉ ∷ Γ) B →
  WfTy Γ A →
  sealᵉ A ∷ Γ ⊢ ⇑ˢᵐ L • zero ⦂ openTyWithSeal B
⊢•-insert hL hB hA = ⊢• here hL hB refl refl
