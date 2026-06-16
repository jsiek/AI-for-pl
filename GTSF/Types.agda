module Types where

-- File Charter:
--   * Core syntax and primitive operations for extrinsic types, contexts, and stores.
--   * Definitions only (renaming/substitution/opening operators, lookup relations,
--   * well-formedness judgments, and top-level type algebra needed by definition
--     modules such as `Ctx` and `Store`).
--   * No proof-only metatheory or coercion-specific metatheory.
-- Note to self:
--   * Keep this file focused on syntax/judgments and definition-layer algebra;
--     place proof-only type lemmas in `proof/TypeProperties.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)

------------------------------------------------------------------------
-- Variables, contexts, base types
------------------------------------------------------------------------

Var : Set
Var = ℕ

TyVar : Set
TyVar = Var

TyCtx : Set
TyCtx = ℕ

data Base : Set where
  `ℕ : Base
  `𝔹 : Base

infixr 7 _⇒_
infix 6 `∀

-- Peter: Consider going intrinsically scoped
data Ty : Set where
  ＇_ : TyVar → Ty   -- both X's and α's
  ‵_ : Base → Ty
  ★ : Ty
  _⇒_ : Ty → Ty → Ty
  `∀ : Ty → Ty

occurs : TyVar → Ty → Bool
occurs X (＇ Y) with X ≟ Y
occurs X (＇ Y) | yes eq = true
occurs X (＇ Y) | no neq = false
occurs X (‵ ι) = false
occurs X ★ = false
occurs X (A ⇒ B) = occurs X A ∨ occurs X B
occurs X (`∀ A) = occurs (suc X) A

X₀ : Ty
X₀ = ＇ 0

data Ground : Ty → Set where
  ＇_ : (α : TyVar) → Ground (＇ α)
  ‵_ : (ι : Base) → Ground (‵ ι)
  ★⇒★ : Ground (★ ⇒ ★)

data Non∀ : Ty → Set where
  non∀-＇ : ∀ {X} → Non∀ (＇ X)
  non∀-‵ : ∀ {ι} → Non∀ (‵ ι)
  non∀-★ : Non∀ ★
  non∀-⇒ : ∀ {A B} → Non∀ (A ⇒ B)
  
data Atom : Ty → Set where
  ＇_ : (α : TyVar) → Atom (＇ α)
  ‵_ : (ι : Base) → Atom (‵ ι)
  ★ : Atom ★

infix 4 _≟Base_
_≟Base_ : (ι ι′ : Base) → Dec (ι ≡ ι′)
`ℕ ≟Base `ℕ = yes refl
`ℕ ≟Base `𝔹 = no (λ ())
`𝔹 ≟Base `ℕ = no (λ ())
`𝔹 ≟Base `𝔹 = yes refl

infix 4 _≟Ground_
_≟Ground_ :
  ∀ {G H : Ty} →
  Ground G →
  Ground H →
  Dec (G ≡ H)
(＇ α) ≟Ground (＇ β) with α ≟ β
... | yes eq = yes (cong ＇_ eq)
... | no neq = no (λ { refl → neq refl })
(＇ α) ≟Ground (‵ ι) = no (λ ())
(＇ α) ≟Ground ★⇒★ = no (λ ())
(‵ ι) ≟Ground (＇ α) = no (λ ())
(‵ ι) ≟Ground (‵ ι′) with ι ≟Base ι′
... | yes eq = yes (cong ‵_ eq)
... | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ground ★⇒★ = no (λ ())
★⇒★ ≟Ground (＇ α) = no (λ ())
★⇒★ ≟Ground (‵ ι) = no (λ ())
★⇒★ ≟Ground ★⇒★ = yes refl

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
＇ X ≟Ty ＇ Y with X ≟ Y
＇ X ≟Ty ＇ Y | yes X≡Y = yes (cong ＇_ X≡Y)
＇ X ≟Ty ＇ Y | no X≢Y = no (λ { refl → X≢Y refl })
＇ X ≟Ty ‵ ι = no (λ ())
＇ X ≟Ty ★ = no (λ ())
＇ X ≟Ty (A ⇒ B) = no (λ ())
＇ X ≟Ty `∀ B = no (λ ())
‵ ι ≟Ty ＇ Y = no (λ ())
‵ ι ≟Ty ‵ ι′ with ι ≟Base ι′
‵ ι ≟Ty ‵ ι′ | yes ι≡ι′ = yes (cong ‵_ ι≡ι′)
‵ ι ≟Ty ‵ ι′ | no ι≢ι′ = no (λ { refl → ι≢ι′ refl })
‵ ι ≟Ty ★ = no (λ ())
‵ ι ≟Ty (A ⇒ B) = no (λ ())
‵ ι ≟Ty `∀ B = no (λ ())
★ ≟Ty ＇ Y = no (λ ())
★ ≟Ty ‵ ι = no (λ ())
★ ≟Ty ★ = yes refl
★ ≟Ty (A ⇒ B) = no (λ ())
★ ≟Ty `∀ B = no (λ ())
(A ⇒ B) ≟Ty ＇ Y = no (λ ())
(A ⇒ B) ≟Ty ‵ ι = no (λ ())
(A ⇒ B) ≟Ty ★ = no (λ ())
(A ⇒ B) ≟Ty (A′ ⇒ B′) with A ≟Ty A′ | B ≟Ty B′
(A ⇒ B) ≟Ty (A′ ⇒ B′) | yes A≡A′ | yes B≡B′ =
  yes (cong₂ _⇒_ A≡A′ B≡B′)
(A ⇒ B) ≟Ty (A′ ⇒ B′) | no A≢A′ | _ =
  no (λ { refl → A≢A′ refl })
(A ⇒ B) ≟Ty (A′ ⇒ B′) | yes A≡A′ | no B≢B′ =
  no (λ { refl → B≢B′ refl })
(A ⇒ B) ≟Ty `∀ C = no (λ ())
`∀ A ≟Ty ＇ Y = no (λ ())
`∀ A ≟Ty ‵ ι = no (λ ())
`∀ A ≟Ty ★ = no (λ ())
`∀ A ≟Ty (B ⇒ C) = no (λ ())
`∀ A ≟Ty `∀ B with A ≟Ty B
`∀ A ≟Ty `∀ B | yes A≡B = yes (cong `∀ A≡B)
`∀ A ≟Ty `∀ B | no A≢B = no (λ { refl → A≢B refl })

Ctx : Set
Ctx = List Ty

Store : Set
Store = List (TyVar × Ty)

∅ˢ : Store
∅ˢ = []

extendˢ : Store → TyVar → Ty → Store
extendˢ Σ α A = (α , A) ∷ Σ

domˢ : Store → List TyVar
domˢ [] = []
domˢ ((X , A) ∷ Σ) = X ∷ domˢ Σ

------------------------------------------------------------------------
-- Type-variable substitution (de Bruijn X)
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = TyVar → TyVar

Substᵗ : Set
Substᵗ = TyVar → Ty

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero = zero
extᵗ ρ (suc X) = suc (ρ X)

raiseVarFrom : TyVar → TyVar → TyVar
raiseVarFrom zero X = suc X
raiseVarFrom (suc k) zero = zero
raiseVarFrom (suc k) (suc X) = suc (raiseVarFrom k X)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (＇ X) = ＇ (ρ X)
renameᵗ ρ (‵ ι) = ‵ ι
renameᵗ ρ ★ = ★
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A) = `∀ (renameᵗ (extᵗ ρ) A)

singleRenameᵗ : TyVar → Renameᵗ
singleRenameᵗ Y zero = Y
singleRenameᵗ Y (suc X) = X

⇑ᵗ : Ty → Ty
⇑ᵗ = renameᵗ suc

infixl 8 _[_]ᴿ
_[_]ᴿ : Ty → TyVar → Ty
A [ X ]ᴿ = renameᵗ (singleRenameᵗ X) A

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ zero = X₀
extsᵗ σ (suc X) = renameᵗ suc (σ X)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (＇ X) = σ X
substᵗ σ (‵ ι) = ‵ ι
substᵗ σ ★ = ★
substᵗ σ (A ⇒ B) = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A) = `∀ (substᵗ (extsᵗ σ) A)

singleTyEnv : Ty → Substᵗ
singleTyEnv B zero = B
singleTyEnv B (suc X) = ＇ X

substVarFrom : TyVar → Ty → Substᵗ
substVarFrom zero T = singleTyEnv T
substVarFrom (suc k) T = extsᵗ (substVarFrom k T)

infixl 8 _[_]ᵗ
_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

renameStoreᵗ : Renameᵗ → Store → Store
renameStoreᵗ ρ [] = []
renameStoreᵗ ρ ((α , A) ∷ Σ) = (ρ α , renameᵗ ρ A) ∷ renameStoreᵗ ρ Σ

⟰ᵗ : Store → Store
⟰ᵗ = renameStoreᵗ suc

------------------------------------------------------------------------
-- Well-formedness
------------------------------------------------------------------------

data WfTy : TyCtx → Ty → Set where
  wfVar : ∀ {Δ X} → X < Δ → WfTy Δ (＇ X)
  wfBase : ∀ {Δ ι} → WfTy Δ (‵ ι)
  wf★ : ∀ {Δ} → WfTy Δ ★
  wf⇒ : ∀ {Δ A B} → WfTy Δ A → WfTy Δ B → WfTy Δ (A ⇒ B)
  wf∀ : ∀ {Δ A} → WfTy (suc Δ) A → WfTy Δ (`∀ A)

------------------------------------------------------------------------
-- Lookup de Bruijn variable in a list
------------------------------------------------------------------------

infix 4 _∋_⦂_
data _∋_⦂_ : ∀{X : Set} → List X → Var → X → Set₁ where
  Z : ∀ {X}{Γ : List X}{A : X} →
      (A ∷ Γ) ∋ zero ⦂ A

  S : ∀{X}{Γ}{A B : X}{x} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A

------------------------------------------------------------------------
-- Lookup type variable in a store
------------------------------------------------------------------------

infix 4 _∋ˢ_⦂_
data _∋ˢ_⦂_ : Store → TyVar → Ty → Set where
  Z∋ˢ : ∀ {Σ A B α β}
       → α ≡ β
       → A ≡ B
       → ((β , B) ∷ Σ) ∋ˢ α ⦂ A

  S∋ˢ : ∀ {Σ α β A B}
       → Σ ∋ˢ α ⦂ A
       → ((β , B) ∷ Σ) ∋ˢ α ⦂ A
