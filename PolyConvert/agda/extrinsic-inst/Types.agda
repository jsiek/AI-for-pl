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
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

------------------------------------------------------------------------
-- Variables, contexts, base types
------------------------------------------------------------------------

Var : Set
Var = ℕ

TyVar : Set
TyVar = Var

Seal : Set
Seal = Var

TyCtx : Set
TyCtx = ℕ

SealCtx : Set
SealCtx = ℕ

data Base : Set where
  `ℕ : Base
  `𝔹 : Base

infixr 7 _⇒_
infix 6 `∀

data Ty : Set where
  ＇_ : TyVar → Ty
  ｀_ : Seal → Ty
  ‵_ : Base → Ty
  ★ : Ty
  _⇒_ : Ty → Ty → Ty
  `∀ : Ty → Ty

occurs : TyVar → Ty → Bool
occurs X (＇ Y) with X ≟ Y
occurs X (＇ Y) | yes eq = true
occurs X (＇ Y) | no neq = false
occurs X (｀ α) = false
occurs X (‵ ι) = false
occurs X ★ = false
occurs X (A ⇒ B) = occurs X A ∨ occurs X B
occurs X (`∀ A) = occurs (suc X) A

α₀ : Ty
α₀ = ｀ 0

X₀ : Ty
X₀ = ＇ 0

data Cross : Ty → Set where
  ＇_ : (X : TyVar) → Cross (＇ X)
  ｀_ : (α : Seal) → Cross (｀ α)
  ‵_ : (ι : Base) → Cross (‵ ι)
  _⇒_ : (A : Ty) → (B : Ty) → Cross (A ⇒ B)
  `∀ : (A : Ty) → Cross (`∀ A)

data Ground : Ty → Set where
  ｀_ : (α : Seal) → Ground (｀ α)
  ‵_ : (ι : Base) → Ground (‵ ι)
  ★⇒★ : Ground (★ ⇒ ★)

data Non★ : Ty → Set where
  non★-＇ : ∀ {X} → Non★ (＇ X)
  non★-｀ : ∀ {α} → Non★ (｀ α)
  non★-‵ : ∀ {ι} → Non★ (‵ ι)
  non★-⇒ : ∀ {A B} → Non★ (A ⇒ B)
  non★-∀ : ∀ {A} → Non★ (`∀ A)

data Non∀ : Ty → Set where
  non∀-＇ : ∀ {X} → Non∀ (＇ X)
  non∀-｀ : ∀ {α} → Non∀ (｀ α)
  non∀-‵ : ∀ {ι} → Non∀ (‵ ι)
  non∀-★ : Non∀ ★
  non∀-⇒ : ∀ {A B} → Non∀ (A ⇒ B)

infix 4 _≟Base_
_≟Base_ : (ι ι′ : Base) → Dec (ι ≡ ι′)
`ℕ ≟Base `ℕ = yes refl
`ℕ ≟Base `𝔹 = no (λ ())
`𝔹 ≟Base `ℕ = no (λ ())
`𝔹 ≟Base `𝔹 = yes refl

seal-≟ : (α β : Seal) → Dec (α ≡ β)
seal-≟ = _≟_

infix 4 _≟Ground_
_≟Ground_ :
  ∀ {G H : Ty} →
  Ground G →
  Ground H →
  Dec (G ≡ H)
(｀ α) ≟Ground (｀ β) with seal-≟ α β
... | yes eq = yes (cong ｀_ eq)
... | no neq = no (λ { refl → neq refl })
(｀ α) ≟Ground (‵ ι) = no (λ ())
(｀ α) ≟Ground ★⇒★ = no (λ ())
(‵ ι) ≟Ground (｀ α) = no (λ ())
(‵ ι) ≟Ground (‵ ι′) with ι ≟Base ι′
... | yes eq = yes (cong ‵_ eq)
... | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ground ★⇒★ = no (λ ())
★⇒★ ≟Ground (｀ α) = no (λ ())
★⇒★ ≟Ground (‵ ι) = no (λ ())
★⇒★ ≟Ground ★⇒★ = yes refl

Ctx : Set
Ctx = List Ty

Store : Set
Store = List (Seal × Ty)

∅ˢ : Store
∅ˢ = []

extendˢ : Store → Seal → Ty → Store
extendˢ Σ α A = (α , A) ∷ Σ

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
renameᵗ ρ (｀ α) = ｀ α
renameᵗ ρ (‵ ι) = ‵ ι
renameᵗ ρ ★ = ★
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A) = `∀ (renameᵗ (extᵗ ρ) A)

⇑ᵗ : Ty → Ty
⇑ᵗ = renameᵗ suc

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ zero = X₀
extsᵗ σ (suc X) = renameᵗ suc (σ X)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (＇ X) = σ X
substᵗ σ (｀ α) = ｀ α
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
renameStoreᵗ ρ ((α , A) ∷ Σ) = (α , renameᵗ ρ A) ∷ renameStoreᵗ ρ Σ

⟰ᵗ : Store → Store
⟰ᵗ = renameStoreᵗ suc

------------------------------------------------------------------------
-- Seal-variable renaming/opening (for ν binders over α)
------------------------------------------------------------------------

Renameˢ : Set
Renameˢ = Seal → Seal

Substˢᵗ : Set
Substˢᵗ = Seal → Ty

extˢ : Renameˢ → Renameˢ
extˢ ρ zero = zero
extˢ ρ (suc α) = suc (ρ α)

extsˢᵗ : Substˢᵗ → Substˢᵗ
extsˢᵗ τ α = renameᵗ suc (τ α)

singleSealEnv : Seal → Renameˢ
singleSealEnv α zero = α
singleSealEnv α (suc α′) = α′

renameˢ : Renameˢ → Ty → Ty
renameˢ ρ (＇ X) = ＇ X
renameˢ ρ (｀ α) = ｀ (ρ α)
renameˢ ρ (‵ ι) = ‵ ι
renameˢ ρ ★ = ★
renameˢ ρ (A ⇒ B) = renameˢ ρ A ⇒ renameˢ ρ B
renameˢ ρ (`∀ A) = `∀ (renameˢ ρ A)

substˢᵗ : Substˢᵗ → Ty → Ty
substˢᵗ τ (＇ X) = ＇ X
substˢᵗ τ (｀ α) = τ α
substˢᵗ τ (‵ ι) = ‵ ι
substˢᵗ τ ★ = ★
substˢᵗ τ (A ⇒ B) = substˢᵗ τ A ⇒ substˢᵗ τ B
substˢᵗ τ (`∀ A) = `∀ (substˢᵗ (extsˢᵗ τ) A)

singleSealTyEnv : Ty → Substˢᵗ
singleSealTyEnv B zero = B
singleSealTyEnv B (suc α) = ｀ α

infixl 8 _[_]ˢᵗ
_[_]ˢᵗ : Ty → Ty → Ty
A [ B ]ˢᵗ = substˢᵗ (singleSealTyEnv B) A

⇑ˢ : Ty → Ty
⇑ˢ = renameˢ suc

⤊ˢ : Ctx → Ctx
⤊ˢ Γ = map ⇑ˢ Γ

renameStoreˢ : Renameˢ → Store → Store
renameStoreˢ ρ [] = []
renameStoreˢ ρ ((α , A) ∷ Σ) =
  (ρ α , renameˢ ρ A) ∷ renameStoreˢ ρ Σ

⟰ˢ : Store → Store
⟰ˢ = renameStoreˢ suc

infixl 8 _[_]ˢ
_[_]ˢ : Ty → Seal → Ty
A [ α ]ˢ = renameˢ (singleSealEnv α) A

------------------------------------------------------------------------
-- Well-formedness
------------------------------------------------------------------------

data WfTy : TyCtx → SealCtx → Ty → Set where
  wfVar : ∀ {Δ Ψ X} → X < Δ → WfTy Δ Ψ (＇ X)
  wfSeal : ∀ {Δ Ψ α} → α < Ψ → WfTy Δ Ψ (｀ α)
  wfBase : ∀ {Δ Ψ ι} → WfTy Δ Ψ (‵ ι)
  wf★ : ∀ {Δ Ψ} → WfTy Δ Ψ ★
  wf⇒ : ∀ {Δ Ψ A B} → WfTy Δ Ψ A → WfTy Δ Ψ B → WfTy Δ Ψ (A ⇒ B)
  wf∀ : ∀ {Δ Ψ A} → {occ : occurs zero A ≡ true} →
    WfTy (suc Δ) Ψ A → WfTy Δ Ψ (`∀ A)

renameᵗ-cong-occ :
  ∀ {ρ ρ′ : Renameᵗ} →
  (∀ X → ρ X ≡ ρ′ X) →
  ∀ A → renameᵗ ρ A ≡ renameᵗ ρ′ A
renameᵗ-cong-occ h (＇ X) = cong ＇_ (h X)
renameᵗ-cong-occ h (｀ α) = refl
renameᵗ-cong-occ h (‵ ι) = refl
renameᵗ-cong-occ h ★ = refl
renameᵗ-cong-occ h (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-cong-occ h A) (renameᵗ-cong-occ h B)
renameᵗ-cong-occ {ρ = ρ} {ρ′ = ρ′} h (`∀ A) =
  cong `∀ (renameᵗ-cong-occ h-ext A)
  where
  h-ext : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
  h-ext zero = refl
  h-ext (suc X) = cong suc (h X)

raiseVarFrom-≢-occ :
  ∀ k X →
  raiseVarFrom k X ≡ k →
  ⊥
raiseVarFrom-≢-occ zero X ()
raiseVarFrom-≢-occ (suc k) zero ()
raiseVarFrom-≢-occ (suc k) (suc X) eq =
  raiseVarFrom-≢-occ k X (suc-injective eq)

raiseVarFrom-injective-occ :
  ∀ k {X Y} →
  raiseVarFrom k X ≡ raiseVarFrom k Y →
  X ≡ Y
raiseVarFrom-injective-occ zero eq = suc-injective eq
raiseVarFrom-injective-occ (suc k) {zero} {zero} eq = refl
raiseVarFrom-injective-occ (suc k) {zero} {suc Y} ()
raiseVarFrom-injective-occ (suc k) {suc X} {zero} ()
raiseVarFrom-injective-occ (suc k) {suc X} {suc Y} eq =
  cong suc (raiseVarFrom-injective-occ k (suc-injective eq))

raise-ext-occ :
  ∀ k X →
  extᵗ (raiseVarFrom k) X ≡ raiseVarFrom (suc k) X
raise-ext-occ k zero = refl
raise-ext-occ k (suc X) = refl

rename-raise-ext-occ :
  ∀ k A →
  renameᵗ (extᵗ (raiseVarFrom k)) A ≡
  renameᵗ (raiseVarFrom (suc k)) A
rename-raise-ext-occ k A = renameᵗ-cong-occ (raise-ext-occ k) A

occurs-raise-occ :
  ∀ k X A →
  occurs (raiseVarFrom k X) (renameᵗ (raiseVarFrom k) A) ≡
  occurs X A
occurs-raise-occ k X (＇ Y)
    with X ≟ Y | raiseVarFrom k X ≟ raiseVarFrom k Y
occurs-raise-occ k X (＇ .X) | yes refl | yes refl = refl
occurs-raise-occ k X (＇ .X) | yes refl | no neq = ⊥-elim (neq refl)
occurs-raise-occ k X (＇ Y) | no neq | yes eq =
  ⊥-elim (neq (raiseVarFrom-injective-occ k eq))
occurs-raise-occ k X (＇ Y) | no neq | no neq′ = refl
occurs-raise-occ k X (｀ α) = refl
occurs-raise-occ k X (‵ ι) = refl
occurs-raise-occ k X ★ = refl
occurs-raise-occ k X (A ⇒ B)
  rewrite occurs-raise-occ k X A
        | occurs-raise-occ k X B = refl
occurs-raise-occ k X (`∀ A)
  rewrite rename-raise-ext-occ k A =
  occurs-raise-occ (suc k) (suc X) A

occurs-raise-fresh-occ :
  ∀ k A →
  occurs k (renameᵗ (raiseVarFrom k) A) ≡ false
occurs-raise-fresh-occ k (＇ X) with k ≟ raiseVarFrom k X
occurs-raise-fresh-occ k (＇ X) | yes eq =
  ⊥-elim (raiseVarFrom-≢-occ k X (sym eq))
occurs-raise-fresh-occ k (＇ X) | no neq = refl
occurs-raise-fresh-occ k (｀ α) = refl
occurs-raise-fresh-occ k (‵ ι) = refl
occurs-raise-fresh-occ k ★ = refl
occurs-raise-fresh-occ k (A ⇒ B)
  rewrite occurs-raise-fresh-occ k A
        | occurs-raise-fresh-occ k B = refl
occurs-raise-fresh-occ k (`∀ A)
  rewrite rename-raise-ext-occ k A =
  occurs-raise-fresh-occ (suc k) A

extᵗFrom : ℕ → Renameᵗ → Renameᵗ
extᵗFrom zero ρ = ρ
extᵗFrom (suc k) ρ = extᵗ (extᵗFrom k ρ)

extᵗFrom-protect-var :
  ∀ k ρ X Y →
  X < k →
  occurs X (＇ extᵗFrom k ρ Y) ≡ occurs X (＇ Y)
extᵗFrom-protect-var zero ρ X Y ()
extᵗFrom-protect-var (suc k) ρ zero zero z<s = refl
extᵗFrom-protect-var (suc k) ρ zero (suc Y) z<s = refl
extᵗFrom-protect-var (suc k) ρ (suc X) zero (s<s X<k) = refl
extᵗFrom-protect-var (suc k) ρ (suc X) (suc Y) (s<s X<k) =
  trans
    (occurs-raise-occ zero X (＇ extᵗFrom k ρ Y))
    (trans
      (extᵗFrom-protect-var k ρ X Y X<k)
      (sym (occurs-raise-occ zero X (＇ Y))))

occurs-renameᵗ-protected :
  ∀ k ρ X A →
  X < k →
  occurs X (renameᵗ (extᵗFrom k ρ) A) ≡ occurs X A
occurs-renameᵗ-protected k ρ X (＇ Y) X<k =
  extᵗFrom-protect-var k ρ X Y X<k
occurs-renameᵗ-protected k ρ X (｀ α) X<k = refl
occurs-renameᵗ-protected k ρ X (‵ ι) X<k = refl
occurs-renameᵗ-protected k ρ X ★ X<k = refl
occurs-renameᵗ-protected k ρ X (A ⇒ B) X<k
  rewrite occurs-renameᵗ-protected k ρ X A X<k
        | occurs-renameᵗ-protected k ρ X B X<k = refl
occurs-renameᵗ-protected k ρ X (`∀ A) X<k =
  occurs-renameᵗ-protected (suc k) ρ (suc X) A (s<s X<k)

occurs-renameᵗ-ext-zero :
  ∀ ρ A →
  occurs zero (renameᵗ (extᵗ ρ) A) ≡ occurs zero A
occurs-renameᵗ-ext-zero ρ A =
  occurs-renameᵗ-protected (suc zero) ρ zero A z<s

occurs-renameˢ :
  ∀ X ρ A →
  occurs X (renameˢ ρ A) ≡ occurs X A
occurs-renameˢ X ρ (＇ Y) = refl
occurs-renameˢ X ρ (｀ α) = refl
occurs-renameˢ X ρ (‵ ι) = refl
occurs-renameˢ X ρ ★ = refl
occurs-renameˢ X ρ (A ⇒ B)
  rewrite occurs-renameˢ X ρ A
        | occurs-renameˢ X ρ B = refl
occurs-renameˢ X ρ (`∀ A) = occurs-renameˢ (suc X) ρ A

occurs-renameˢ-zero :
  ∀ ρ A →
  occurs zero (renameˢ ρ A) ≡ occurs zero A
occurs-renameˢ-zero ρ A = occurs-renameˢ zero ρ A

extsᵗFrom : ℕ → Substᵗ → Substᵗ
extsᵗFrom zero σ = σ
extsᵗFrom (suc k) σ = extsᵗ (extsᵗFrom k σ)

extsᵗFrom-protect-var :
  ∀ k σ X Y →
  X < k →
  occurs X (extsᵗFrom k σ Y) ≡ occurs X (＇ Y)
extsᵗFrom-protect-var zero σ X Y ()
extsᵗFrom-protect-var (suc k) σ X zero X<sk = refl
extsᵗFrom-protect-var (suc k) σ zero (suc Y) z<s =
  occurs-raise-fresh-occ zero (extsᵗFrom k σ Y)
extsᵗFrom-protect-var (suc k) σ (suc X) (suc Y) (s<s X<k) =
  trans
    (occurs-raise-occ zero X (extsᵗFrom k σ Y))
    (trans
      (extsᵗFrom-protect-var k σ X Y X<k)
      (sym (occurs-raise-occ zero X (＇ Y))))

occurs-substᵗ-protected :
  ∀ k σ X A →
  X < k →
  occurs X (substᵗ (extsᵗFrom k σ) A) ≡ occurs X A
occurs-substᵗ-protected k σ X (＇ Y) X<k =
  extsᵗFrom-protect-var k σ X Y X<k
occurs-substᵗ-protected k σ X (｀ α) X<k = refl
occurs-substᵗ-protected k σ X (‵ ι) X<k = refl
occurs-substᵗ-protected k σ X ★ X<k = refl
occurs-substᵗ-protected k σ X (A ⇒ B) X<k
  rewrite occurs-substᵗ-protected k σ X A X<k
        | occurs-substᵗ-protected k σ X B X<k = refl
occurs-substᵗ-protected k σ X (`∀ A) X<k =
  occurs-substᵗ-protected (suc k) σ (suc X) A (s<s X<k)

occurs-substᵗ-exts-zero :
  ∀ σ A →
  occurs zero (substᵗ (extsᵗ σ) A) ≡ occurs zero A
occurs-substᵗ-exts-zero σ A =
  occurs-substᵗ-protected (suc zero) σ zero A z<s

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
-- Lookup seal in a store
------------------------------------------------------------------------

infix 4 _∋ˢ_⦂_
data _∋ˢ_⦂_ : Store → Seal → Ty → Set where
  Z∋ˢ : ∀ {Σ A B α β}
       → α ≡ β
       → A ≡ B
       → ((β , B) ∷ Σ) ∋ˢ α ⦂ A

  S∋ˢ : ∀ {Σ α β A B}
       → Σ ∋ˢ α ⦂ A
       → ((β , B) ∷ Σ) ∋ˢ α ⦂ A

------------------------------------------------------------------------
-- Definition-layer type algebra
------------------------------------------------------------------------

renameLookupˢ :
  ∀  (ρ : Renameˢ) {Σ : Store} {α : Seal} {A : Ty} →
  Σ ∋ˢ α ⦂ A →
  renameStoreˢ ρ Σ ∋ˢ ρ α ⦂ renameˢ ρ A
renameLookupˢ ρ (Z∋ˢ α≡β A≡B) =
  Z∋ˢ (cong ρ α≡β) (cong (renameˢ ρ) A≡B)
renameLookupˢ ρ (S∋ˢ h) = S∋ˢ (renameLookupˢ ρ h)

liftSubstˢ :  Substᵗ → Substᵗ
liftSubstˢ σ X = ⇑ˢ (σ X)

TyRenameWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameWf Δ Δ′ ρ = ∀ {X} → X < Δ → ρ X < Δ′

TyRenameWf-ext :
  ∀ {Δ Δ′} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ′ ρ →
  TyRenameWf (suc Δ) (suc Δ′) (extᵗ ρ)
TyRenameWf-ext hρ {zero} z<s = z<s
TyRenameWf-ext hρ {suc X} (s<s X<Δ) = s<s (hρ X<Δ)

TyRenameWf-suc :
  ∀ {Δ} →
  TyRenameWf Δ (suc Δ) suc
TyRenameWf-suc {Δ} X<Δ = s<s X<Δ

SealRenameWf : SealCtx → SealCtx → Renameˢ → Set
SealRenameWf Ψ Ψ′ ρ = ∀ {α} → α < Ψ → ρ α < Ψ′

SealRenameWf-ext :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} →
  SealRenameWf Ψ Ψ′ ρ →
  SealRenameWf (suc Ψ) (suc Ψ′) (extˢ ρ)
SealRenameWf-ext hρ {zero} z<s = z<s
SealRenameWf-ext hρ {suc α} (s<s α<Ψ) = s<s (hρ α<Ψ)

SealRenameWf-suc :
  ∀ {Ψ} →
  SealRenameWf Ψ (suc Ψ) suc
SealRenameWf-suc α<Ψ = s<s α<Ψ

renameᵗ-preserves-WfTy :
  ∀ {Δ Δ′ Ψ} {ρ : Renameᵗ} {A : Ty} →
  WfTy Δ Ψ A →
  TyRenameWf Δ Δ′ ρ →
  WfTy Δ′ Ψ (renameᵗ ρ A)
renameᵗ-preserves-WfTy (wfVar X<Δ) hρ = wfVar (hρ X<Δ)
renameᵗ-preserves-WfTy (wfSeal α<Ψ) hρ = wfSeal α<Ψ
renameᵗ-preserves-WfTy wfBase hρ = wfBase
renameᵗ-preserves-WfTy wf★ hρ = wf★
renameᵗ-preserves-WfTy (wf⇒ hA hB) hρ =
  wf⇒ (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-preserves-WfTy hB hρ)
renameᵗ-preserves-WfTy (wf∀ {A = A} {occ = occ} hA) hρ =
  wf∀ {occ = trans (occurs-renameᵗ-ext-zero _ A) occ}
    (renameᵗ-preserves-WfTy hA (TyRenameWf-ext hρ))

renameˢ-preserves-WfTy :
  ∀ {Δ Ψ Ψ′} {ρ : Renameˢ} {A : Ty} →
  WfTy Δ Ψ A →
  SealRenameWf Ψ Ψ′ ρ →
  WfTy Δ Ψ′ (renameˢ ρ A)
renameˢ-preserves-WfTy (wfVar X<Δ) hρ = wfVar X<Δ
renameˢ-preserves-WfTy (wfSeal α<Ψ) hρ = wfSeal (hρ α<Ψ)
renameˢ-preserves-WfTy wfBase hρ = wfBase
renameˢ-preserves-WfTy wf★ hρ = wf★
renameˢ-preserves-WfTy (wf⇒ hA hB) hρ =
  wf⇒ (renameˢ-preserves-WfTy hA hρ) (renameˢ-preserves-WfTy hB hρ)
renameˢ-preserves-WfTy (wf∀ {A = A} {occ = occ} hA) hρ =
  wf∀ {occ = trans (occurs-renameˢ-zero _ A) occ}
    (renameˢ-preserves-WfTy hA hρ)

rename-cong :
  ∀{ρ ρ′ : Renameᵗ} →
  ((X : TyVar) → ρ X ≡ ρ′ X) →
  (A : Ty) →
  renameᵗ ρ A ≡ renameᵗ ρ′ A
rename-cong h (＇ X) = cong ＇_ (h X)
rename-cong h (｀ α) = refl
rename-cong h (‵ ι) = refl
rename-cong h ★ = refl
rename-cong h (A ⇒ B) = cong₂ _⇒_ (rename-cong h A) (rename-cong h B)
rename-cong {ρ = ρ} {ρ′ = ρ′} h (`∀ A) = cong `∀ (rename-cong h-ext A)
  where
    h-ext : (X : TyVar) → extᵗ ρ X ≡ extᵗ ρ′ X
    h-ext zero = refl
    h-ext (suc X) = cong suc (h X)

substᵗ-cong :
  ∀
  {σ τ : Substᵗ} →
  ((X : TyVar) → σ X ≡ τ X) →
  (A : Ty) →
  substᵗ σ A ≡ substᵗ τ A
substᵗ-cong h (＇ X) = h X
substᵗ-cong h (｀ α) = refl
substᵗ-cong h (‵ ι) = refl
substᵗ-cong h ★ = refl
substᵗ-cong h (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-cong h A) (substᵗ-cong h B)
substᵗ-cong {σ = σ} {τ = τ} h (`∀ A) =
  cong `∀ (substᵗ-cong h-ext A)
  where
    h-ext : (X : TyVar) → extsᵗ σ X ≡ extsᵗ τ X
    h-ext zero = refl
    h-ext (suc X) = cong (renameᵗ suc) (h X)

substᵗ-id :
  ∀ (A : Ty) →
  substᵗ (λ X → ＇ X) A ≡ A
substᵗ-id (＇ X) = refl
substᵗ-id (｀ α) = refl
substᵗ-id (‵ ι) = refl
substᵗ-id ★ = refl
substᵗ-id (A ⇒ B) = cong₂ _⇒_ (substᵗ-id A) (substᵗ-id B)
substᵗ-id (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong env-eq A)
      (substᵗ-id A))
  where
    env-eq : (X : TyVar) → extsᵗ (λ Y → ＇ Y) X ≡ ＇ X
    env-eq zero = refl
    env-eq (suc X) = refl

renameᵗ-compose :
  ∀
  (ρ₁ : Renameᵗ) (ρ₂ : Renameᵗ) (A : Ty) →
  renameᵗ ρ₂ (renameᵗ ρ₁ A) ≡ renameᵗ (λ X → ρ₂ (ρ₁ X)) A
renameᵗ-compose ρ₁ ρ₂ (＇ X) = refl
renameᵗ-compose ρ₁ ρ₂ (｀ α) = refl
renameᵗ-compose ρ₁ ρ₂ (‵ ι) = refl
renameᵗ-compose ρ₁ ρ₂ ★ = refl
renameᵗ-compose ρ₁ ρ₂ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-compose ρ₁ ρ₂ A) (renameᵗ-compose ρ₁ ρ₂ B)
renameᵗ-compose ρ₁ ρ₂ (`∀ A) =
  trans
    (cong `∀ (renameᵗ-compose (extᵗ ρ₁) (extᵗ ρ₂) A))
    (cong `∀ (rename-cong ext-comp A))
  where
    ext-comp :
      (X : TyVar) →
      extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ X′ → ρ₂ (ρ₁ X′)) X
    ext-comp zero = refl
    ext-comp (suc X) = refl

renameᵗ-suc-comm :
  ∀
  (ρ : Renameᵗ) (A : Ty) →
  renameᵗ suc (renameᵗ ρ A) ≡
  renameᵗ (extᵗ ρ) (renameᵗ suc A)
renameᵗ-suc-comm ρ A =
  trans
    (renameᵗ-compose ρ suc A)
    (sym (renameᵗ-compose suc (extᵗ ρ) A))

substᵗ-renameᵗ :
  ∀
  (ρ : Renameᵗ) (σ : Substᵗ) (A : Ty) →
  substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
substᵗ-renameᵗ ρ σ (＇ X) = refl
substᵗ-renameᵗ ρ σ (｀ α) = refl
substᵗ-renameᵗ ρ σ (‵ ι) = refl
substᵗ-renameᵗ ρ σ ★ = refl
substᵗ-renameᵗ ρ σ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-renameᵗ ρ σ A) (substᵗ-renameᵗ ρ σ B)
substᵗ-renameᵗ ρ σ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-renameᵗ (extᵗ ρ) (extsᵗ σ) A)
      (substᵗ-cong env-eq A))
  where
    env-eq :
      (X : TyVar) →
      extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
    env-eq zero = refl
    env-eq (suc X) = refl

renameᵗ-substᵗ :
  ∀
  (ρ : Renameᵗ) (σ : Substᵗ) (A : Ty) →
  renameᵗ ρ (substᵗ σ A) ≡ substᵗ (λ X → renameᵗ ρ (σ X)) A
renameᵗ-substᵗ ρ σ (＇ X) = refl
renameᵗ-substᵗ ρ σ (｀ α) = refl
renameᵗ-substᵗ ρ σ (‵ ι) = refl
renameᵗ-substᵗ ρ σ ★ = refl
renameᵗ-substᵗ ρ σ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-substᵗ ρ σ A) (renameᵗ-substᵗ ρ σ B)
renameᵗ-substᵗ ρ σ (`∀ A) =
  cong `∀
    (trans
      (renameᵗ-substᵗ (extᵗ ρ) (extsᵗ σ) A)
      (substᵗ-cong env-eq A))
  where
    env-eq :
      (X : TyVar) →
      renameᵗ (extᵗ ρ) (extsᵗ σ X) ≡ extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
    env-eq zero = refl
    env-eq (suc X) = sym (renameᵗ-suc-comm ρ (σ X))

substᵗ-suc-renameᵗ-suc :
  ∀
  (σ : Substᵗ) (A : Ty) →
  substᵗ (extsᵗ σ) (renameᵗ suc A) ≡
  renameᵗ suc (substᵗ σ A)
substᵗ-suc-renameᵗ-suc σ A =
  trans
    (substᵗ-renameᵗ suc (extsᵗ σ) A)
    (sym (renameᵗ-substᵗ suc σ A))

renameˢ-renameᵗ :
  ∀
  (ρᵗ : Renameᵗ) (ρˢ : Renameˢ) (A : Ty) →
  renameˢ ρˢ (renameᵗ ρᵗ A) ≡
  renameᵗ ρᵗ (renameˢ ρˢ A)
renameˢ-renameᵗ ρᵗ ρˢ (＇ X) = refl
renameˢ-renameᵗ ρᵗ ρˢ (｀ α) = refl
renameˢ-renameᵗ ρᵗ ρˢ (‵ ι) = refl
renameˢ-renameᵗ ρᵗ ρˢ ★ = refl
renameˢ-renameᵗ ρᵗ ρˢ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-renameᵗ ρᵗ ρˢ A) (renameˢ-renameᵗ ρᵗ ρˢ B)
renameˢ-renameᵗ ρᵗ ρˢ (`∀ A) =
  cong `∀ (renameˢ-renameᵗ (extᵗ ρᵗ) ρˢ A)

renameᵗ-⇑ˢ :
  ∀  (ρ : Renameᵗ) (B : Ty) →
  renameᵗ ρ (⇑ˢ B) ≡ ⇑ˢ (renameᵗ ρ B)
renameᵗ-⇑ˢ ρ (＇ X) = refl
renameᵗ-⇑ˢ ρ (｀ α) = refl
renameᵗ-⇑ˢ ρ (‵ ι) = refl
renameᵗ-⇑ˢ ρ ★ = refl
renameᵗ-⇑ˢ ρ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-⇑ˢ ρ A) (renameᵗ-⇑ˢ ρ B)
renameᵗ-⇑ˢ ρ (`∀ A) =
  cong `∀ (renameᵗ-⇑ˢ (extᵗ ρ) A)

private
  exts-liftSubstˢ :
    ∀
    (σ : Substᵗ) (X : TyVar) →
    extsᵗ (liftSubstˢ σ) X ≡ liftSubstˢ (extsᵗ σ) X
  exts-liftSubstˢ σ zero = refl
  exts-liftSubstˢ σ (suc X) = renameᵗ-⇑ˢ suc (σ X)

substᵗ-⇑ˢ :
  ∀  (σ : Substᵗ) (B : Ty) →
  substᵗ (liftSubstˢ σ) (⇑ˢ B) ≡ ⇑ˢ (substᵗ σ B)
substᵗ-⇑ˢ σ (＇ X) = refl
substᵗ-⇑ˢ σ (｀ α) = refl
substᵗ-⇑ˢ σ (‵ ι) = refl
substᵗ-⇑ˢ σ ★ = refl
substᵗ-⇑ˢ σ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-⇑ˢ σ A) (substᵗ-⇑ˢ σ B)
substᵗ-⇑ˢ σ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong (exts-liftSubstˢ σ) (⇑ˢ A))
      (substᵗ-⇑ˢ (extsᵗ σ) A))

open-renᵗ-suc :
  (A : Ty) →
  (T : Ty) →
  (renameᵗ suc A) [ T ]ᵗ ≡ A
open-renᵗ-suc A T =
  trans
    (substᵗ-renameᵗ suc (singleTyEnv T) A)
    (trans
      (substᵗ-cong (λ X → refl) A)
      (substᵗ-id A))

renameˢ-ext-⇑ˢ :
  ∀
  (ρ : Renameˢ) (A : Ty) →
  renameˢ (extˢ ρ) (⇑ˢ A) ≡ ⇑ˢ (renameˢ ρ A)
renameˢ-ext-⇑ˢ ρ (＇ X) = refl
renameˢ-ext-⇑ˢ ρ (｀ α) = refl
renameˢ-ext-⇑ˢ ρ (‵ ι) = refl
renameˢ-ext-⇑ˢ ρ ★ = refl
renameˢ-ext-⇑ˢ ρ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-ext-⇑ˢ ρ A) (renameˢ-ext-⇑ˢ ρ B)
renameˢ-ext-⇑ˢ ρ (`∀ A) =
  cong `∀ (renameˢ-ext-⇑ˢ ρ A)

renameˢ-single-⇑ˢ-id :
  (α : Seal) →
  (A : Ty) →
  renameˢ (singleSealEnv α) (⇑ˢ A) ≡ A
renameˢ-single-⇑ˢ-id α (＇ X) = refl
renameˢ-single-⇑ˢ-id α (｀ β) = refl
renameˢ-single-⇑ˢ-id α (‵ ι) = refl
renameˢ-single-⇑ˢ-id α ★ = refl
renameˢ-single-⇑ˢ-id α (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-single-⇑ˢ-id α A) (renameˢ-single-⇑ˢ-id α B)
renameˢ-single-⇑ˢ-id α (`∀ A) =
  cong `∀ (renameˢ-single-⇑ˢ-id α A)

dropVarFrom : TyVar → TyVar → TyVar
dropVarFrom zero zero = zero
dropVarFrom zero (suc X) = X
dropVarFrom (suc n) zero = zero
dropVarFrom (suc n) (suc X) = suc (dropVarFrom n X)

dropTyFrom : TyVar → Ty → Ty
dropTyFrom n (＇ X) = ＇ (dropVarFrom n X)
dropTyFrom n (｀ α) = ｀ α
dropTyFrom n (‵ ι) = ‵ ι
dropTyFrom n ★ = ★
dropTyFrom n (A ⇒ B) = dropTyFrom n A ⇒ dropTyFrom n B
dropTyFrom n (`∀ A) = `∀ (dropTyFrom (suc n) A)
