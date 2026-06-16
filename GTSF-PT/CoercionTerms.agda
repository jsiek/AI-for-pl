-- File Charter:
--   * Core syntax, values, and primitive operations for coercion terms.
--   * Primary exports are intrinsically typed target terms plus term/type
--     renaming and substitution operations.
--   * Depends on labels, types, consistency, coercion typing, and source
--     expression contexts.

module CoercionTerms where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (Bool)
open import Data.Fin.Subset using (Subset; Side; inside; outside; _∈_)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂)
open import Data.Vec using ([] ; _∷_; here; there)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; sym; trans)
  renaming (subst to substEq)

open import Label
open import Types
open import Consistency
open import Coercions
open import Terms using (ExCtx; ∅; _▷_; renameᵉ; ExVar; Zᵉ; Sᵉ)

-- data ExCtx : TyCtx → Set where

--   ∅ : ∀{Δ} → ExCtx Δ

--   _▷_ : ∀{Δ} → ExCtx Δ → Ty Δ → ExCtx Δ

-- renameᵉ : ∀ {Δ}{Δ′} → Renameᵗ Δ Δ′ → ExCtx Δ → ExCtx Δ′
-- renameᵉ ρ ∅ = ∅
-- renameᵉ ρ (Γ ▷ T) = renameᵉ ρ Γ ▷ renameᵗ ρ T

-- data ExVar {Δ : TyCtx} : ExCtx Δ → Ty Δ → Set where

--   Zᵉ : ∀ {Γ}{T} → ExVar (Γ ▷ T) T

--   Sᵉ : ∀ {Γ} {T T′ : Ty Δ} → ExVar Γ T → ExVar (Γ ▷ T′) T

data Ex {Δ : TyCtx} {Ψ : Subset Δ} : ExCtx Δ → Ty Δ → Set where

  `_ : ∀ {Γ} {T}
    → ExVar Γ T → Ex Γ T

  cst : ∀ {Γ}
    → (b : Σ Base base-type)
    → Ex Γ (‵ b .proj₁)

  λx:_⇒ : ∀ {Γ} {U}
    → ∀ T
    → Ex {Ψ = Ψ} (Γ ▷ T) U
    → Ex Γ (T ⇒ U)

  app : ∀ {Γ} {T U}
      → Ex {Ψ = Ψ} Γ (T ⇒ U)
      → Ex {Ψ = Ψ} Γ T
      → Ex Γ U

  ΛX : ∀ {Γ} {T}
    → Ex {Ψ = outside ∷ Ψ}  (renameᵉ Sᵗ Γ) T
    → Ex Γ (`∀ T)

  tapp : ∀ {Γ} {T : Ty (ℕ.suc Δ)}
       → Ex {Ψ = Ψ} Γ (`∀ T)
       → (U : Ty Δ)
       → Ex Γ (T [ U ]ᵗ)

  capp : ∀ {Γ}{S T : Ty Δ}{s : Coercion Δ}
    → Ex {Ψ = Ψ} Γ S
    → Δ ∣ Ψ ⊢ s ∶ S =⇒ T
    → Ex Γ T

  blame : ∀ {Γ}{A} (ℓ : Label)
    → Ex Γ A

syntax app x y = x · y
syntax capp x y = x ⟨ y ⟩

data Value {Δ : TyCtx} {Ψ : Subset Δ} {Γ : ExCtx Δ} : ∀  {T : Ty Δ} → Ex {Ψ = Ψ} Γ T → Set where

  v-cst : ∀ (b : Σ Base base-type) → Value (cst b)

  v-λx:_⇒  : ∀ (A : Ty Δ) {B : Ty Δ} → (M : Ex (Γ ▷ A) B) → Value (λx: A ⇒ M)

  v-ΛX : ∀ {A} (N : Ex {Ψ = outside ∷ Ψ} (renameᵉ Sᵗ Γ) A) → Value (ΛX N)

  v-capp-seal :  ∀{α : TyVar Δ}{A : Ty Δ}{V : Ex Γ A}
    → (α∈Ψ : tyVarToFin α ∈ Ψ)
    → Value V
    → Value (capp V (cast-seal α∈Ψ))

  v-capp-tag : ∀ {T} {V : Ex {Ψ = Ψ} Γ T}
    → (gT : Ground T)
    → Value V
    → Value (capp V (cast-tag gT))

  v-capp-fun : ∀ {A}{B}{A′}{B′} {V : Ex {Ψ = Ψ} Γ (A ⇒ B)} {s}{t}
    → {s⊢ : Δ ∣ Ψ ⊢ s ∶ A′ =⇒ A}
    → {t⊢ : Δ ∣ Ψ ⊢ t ∶ B =⇒ B′}
    → Value V
    → Value (capp V (cast-fun s⊢ t⊢))

  v-capp-gen :  ∀{A : Ty Δ}{B : Ty (suc Δ)}{V : Ex Γ A}{s : Coercion (suc Δ)}
    → {s⊢ : suc Δ ∣ inside ∷ Ψ ⊢ s ∶ wkTy A =⇒ B}
    → Value V
    → Value (capp V (cast-gen s⊢))

------------------------------------------------------------
-- expression renaming
------------------------------------------------------------

Renameᶜᵗ : ∀ {Δ} → ExCtx Δ → ExCtx Δ → Set
Renameᶜᵗ Γ Γ′ = ∀ {T} → ExVar Γ T → ExVar Γ′ T

extᶜᵗ : ∀ {Δ}{Γ Γ′ : ExCtx Δ}{T : Ty Δ} →
  Renameᶜᵗ Γ Γ′ →
  Renameᶜᵗ (Γ ▷ T) (Γ′ ▷ T)
extᶜᵗ ρ Zᵉ = Zᵉ
extᶜᵗ ρ (Sᵉ x) = Sᵉ (ρ x)

rename-varᵗ :
  ∀ {Δ Δ′}{Γ : ExCtx Δ}{T : Ty Δ} →
  (ρ : Renameᵗ Δ Δ′) →
  ExVar Γ T →
  ExVar (renameᵉ ρ Γ) (renameᵗ ρ T)
rename-varᵗ ρ Zᵉ = Zᵉ
rename-varᵗ ρ (Sᵉ x) = Sᵉ (rename-varᵗ ρ x)

renameᵉ-Renameᶜᵗ :
  ∀ {Δ Δ′}{Γ Γ′ : ExCtx Δ} →
  (ρᵗ : Renameᵗ Δ Δ′) →
  Renameᶜᵗ Γ Γ′ →
  Renameᶜᵗ (renameᵉ ρᵗ Γ) (renameᵉ ρᵗ Γ′)
renameᵉ-Renameᶜᵗ {Γ = ∅} ρᵗ ρ ()
renameᵉ-Renameᶜᵗ {Γ = Γ ▷ T} ρᵗ ρ Zᵉ = rename-varᵗ ρᵗ (ρ Zᵉ)
renameᵉ-Renameᶜᵗ {Γ = Γ ▷ T} ρᵗ ρ (Sᵉ x) =
  renameᵉ-Renameᶜᵗ ρᵗ (λ y → ρ (Sᵉ y)) x

renameᶜᵗ :
  ∀ {Δ} {Ψ : Subset Δ} {Γ Γ′ : ExCtx Δ}{T : Ty Δ} →
  Renameᶜᵗ Γ Γ′ →
  Ex {Ψ = Ψ} Γ T →
  Ex {Ψ = Ψ} Γ′ T
renameᶜᵗ ρ (` x) = ` (ρ x)
renameᶜᵗ ρ (cst b) = cst b
renameᶜᵗ ρ (λx: T ⇒ M) = λx: T ⇒ (renameᶜᵗ (extᶜᵗ ρ) M)
renameᶜᵗ ρ (app M N) = app (renameᶜᵗ ρ M) (renameᶜᵗ ρ N)
renameᶜᵗ ρ (ΛX M) = ΛX (renameᶜᵗ (renameᵉ-Renameᶜᵗ Sᵗ ρ) M)
renameᶜᵗ ρ (tapp M U) = tapp (renameᶜᵗ ρ M) U
renameᶜᵗ ρ (capp M s⊢) = capp (renameᶜᵗ ρ M) s⊢
renameᶜᵗ ρ (blame ℓ) = blame ℓ

RenamesSubset : ∀ {Δ Δ′} → Renameᵗ Δ Δ′ → Subset Δ → Subset Δ′ → Set
RenamesSubset ρ Ψ Ψ′ =
  ∀ {X} → tyVarToFin X ∈ Ψ → tyVarToFin (ρ X) ∈ Ψ′

renames-outside :
  ∀ {Δ Δ′}{ρ : Renameᵗ Δ Δ′}{Ψ : Subset Δ}{Ψ′ : Subset Δ′} →
  RenamesSubset ρ Ψ Ψ′ →
  RenamesSubset (extᵗ ρ) (outside ∷ Ψ) (outside ∷ Ψ′)
renames-outside ρ⊆ {Zᵗ} ()
renames-outside ρ⊆ {Sᵗ X} (there X∈Ψ) = there (ρ⊆ X∈Ψ)

renames-inside :
  ∀ {Δ Δ′}{ρ : Renameᵗ Δ Δ′}{Ψ : Subset Δ}{Ψ′ : Subset Δ′} →
  RenamesSubset ρ Ψ Ψ′ →
  RenamesSubset (extᵗ ρ) (inside ∷ Ψ) (inside ∷ Ψ′)
renames-inside ρ⊆ {Zᵗ} here = here
renames-inside ρ⊆ {Sᵗ X} (there X∈Ψ) = there (ρ⊆ X∈Ψ)

renames-wk : ∀ {Δ}{Ψ : Subset Δ} → RenamesSubset Sᵗ Ψ (outside ∷ Ψ)
renames-wk X∈Ψ = there X∈Ψ

rename-Ground :
  ∀ {Δ Δ′}{G : Ty Δ} →
  (ρ : Renameᵗ Δ Δ′) →
  Ground G →
  Ground (renameᵗ ρ G)
rename-Ground ρ (‵ ι) = ‵ ι
rename-Ground ρ ★⇒★ = ★⇒★

rename-wkTy :
  ∀ {Δ Δ′}(ρ : Renameᵗ Δ Δ′) (A : Ty Δ) →
  renameᵗ (extᵗ ρ) (wkTy A) ≡ wkTy (renameᵗ ρ A)
rename-wkTy ρ A =
  trans (renameᵗ-comp (extᵗ ρ) Sᵗ A)
        (sym (renameᵗ-comp Sᵗ ρ A))

rename-cast :
  ∀ {Δ Δ′}{Ψ : Subset Δ}{Ψ′ : Subset Δ′}
    {A B : Ty Δ}{s : Coercion Δ} →
  (ρ : Renameᵗ Δ Δ′) →
  RenamesSubset ρ Ψ Ψ′ →
  Δ ∣ Ψ ⊢ s ∶ A =⇒ B →
  Δ′ ∣ Ψ′ ⊢ renameᶜ ρ s ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
rename-cast ρ ρ⊆ cast-id = cast-id
rename-cast ρ ρ⊆ (cast-seal α∈Ψ) = cast-seal (ρ⊆ α∈Ψ)
rename-cast ρ ρ⊆ (cast-unseal α∈Ψ) = cast-unseal (ρ⊆ α∈Ψ)
rename-cast ρ ρ⊆ (cast-seq s⊢ t⊢) =
  cast-seq (rename-cast ρ ρ⊆ s⊢) (rename-cast ρ ρ⊆ t⊢)
rename-cast ρ ρ⊆ (cast-tag G) = cast-tag (rename-Ground ρ G)
rename-cast ρ ρ⊆ (cast-untag H) = cast-untag (rename-Ground ρ H)
rename-cast ρ ρ⊆ (cast-fun s⊢ t⊢) =
  cast-fun (rename-cast ρ ρ⊆ s⊢) (rename-cast ρ ρ⊆ t⊢)
rename-cast ρ ρ⊆ (cast-all s⊢) =
  cast-all (rename-cast (extᵗ ρ) (renames-outside ρ⊆) s⊢)
rename-cast ρ ρ⊆ (cast-inst {A = A} {B = B} {s = s} s⊢) =
  cast-inst
    (substEq
      (λ C → _ ∣ _ ⊢ renameᶜ (extᵗ ρ) s ∶ renameᵗ (extᵗ ρ) A =⇒ C)
      (rename-wkTy ρ B)
      (rename-cast (extᵗ ρ) (renames-inside ρ⊆) s⊢))
rename-cast ρ ρ⊆ (cast-gen {A = A} {B = B} {s = s} s⊢) =
  cast-gen
    (substEq
      (λ C → _ ∣ _ ⊢ renameᶜ (extᵗ ρ) s ∶ C =⇒ renameᵗ (extᵗ ρ) B)
      (rename-wkTy ρ A)
      (rename-cast (extᵗ ρ) (renames-inside ρ⊆) s⊢))

singleTyEnv-rename :
  ∀ {Δ Δ′}(ρ : Renameᵗ Δ Δ′)(U : Ty Δ)(X : TyVar (suc Δ)) →
  renameᵗ ρ (singleTyEnv U X) ≡
  singleTyEnv (renameᵗ ρ U) (extᵗ ρ X)
singleTyEnv-rename ρ U Zᵗ = refl
singleTyEnv-rename ρ U (Sᵗ X) = refl

rename-[]ᵗ :
  ∀ {Δ Δ′}(ρ : Renameᵗ Δ Δ′)(T : Ty (suc Δ))(U : Ty Δ) →
  renameᵗ ρ (T [ U ]ᵗ) ≡ (renameᵗ (extᵗ ρ) T) [ renameᵗ ρ U ]ᵗ
rename-[]ᵗ ρ T U =
  trans (renameᵗ-subst ρ (singleTyEnv U) T)
        (trans (substᵗ-cong-env (singleTyEnv-rename ρ U) T)
               (sym (substᵗ-rename (extᵗ ρ)
                                    (singleTyEnv (renameᵗ ρ U)) T)))

renameᵉ-wk :
  ∀ {Δ Δ′}(ρ : Renameᵗ Δ Δ′)(Γ : ExCtx Δ) →
  renameᵉ (extᵗ ρ) (renameᵉ Sᵗ Γ) ≡ renameᵉ Sᵗ (renameᵉ ρ Γ)
renameᵉ-wk ρ ∅ = refl
renameᵉ-wk ρ (Γ ▷ T) =
  cong₂ _▷_ (renameᵉ-wk ρ Γ) (rename-wkTy ρ T)

renameᵗᶜᵗ :
  ∀ {Δ Δ′}{Ψ : Subset Δ}{Ψ′ : Subset Δ′}
    {Γ : ExCtx Δ}{T : Ty Δ} →
  (ρ : Renameᵗ Δ Δ′) →
  RenamesSubset ρ Ψ Ψ′ →
  Ex {Ψ = Ψ} Γ T →
  Ex {Ψ = Ψ′} (renameᵉ ρ Γ) (renameᵗ ρ T)
renameᵗᶜᵗ ρ ρ⊆ (` x) = ` (rename-varᵗ ρ x)
renameᵗᶜᵗ ρ ρ⊆ (cst b) = cst b
renameᵗᶜᵗ ρ ρ⊆ (λx: T ⇒ M) =
  λx: renameᵗ ρ T ⇒ (renameᵗᶜᵗ ρ ρ⊆ M)
renameᵗᶜᵗ ρ ρ⊆ (app M N) = app (renameᵗᶜᵗ ρ ρ⊆ M) (renameᵗᶜᵗ ρ ρ⊆ N)
renameᵗᶜᵗ {Ψ′ = Ψ′} {Γ = Γ} ρ ρ⊆ (ΛX {T = T} M) =
  ΛX
    (substEq
      (λ Γ₀ → Ex {Ψ = outside ∷ Ψ′} Γ₀ (renameᵗ (extᵗ ρ) T))
      (renameᵉ-wk ρ Γ)
      (renameᵗᶜᵗ (extᵗ ρ) (renames-outside ρ⊆) M))
renameᵗᶜᵗ {Ψ′ = Ψ′} {Γ = Γ} ρ ρ⊆ (tapp {T = T} M U) =
  substEq (Ex {Ψ = Ψ′} (renameᵉ ρ Γ)) (sym (rename-[]ᵗ ρ T U))
          (tapp (renameᵗᶜᵗ ρ ρ⊆ M) (renameᵗ ρ U))
renameᵗᶜᵗ ρ ρ⊆ (capp M s⊢) =
  capp (renameᵗᶜᵗ ρ ρ⊆ M) (rename-cast ρ ρ⊆ s⊢)
renameᵗᶜᵗ ρ ρ⊆ (blame ℓ) = blame ℓ

Substᶜᵗ : ∀ {Δ} {Ψ : Subset Δ} → ExCtx Δ → ExCtx Δ → Set
Substᶜᵗ {Ψ = Ψ} Γ Γ′ = ∀ {T} → ExVar Γ T → Ex {Ψ = Ψ} Γ′ T

extsᶜᵗ :
  ∀ {Δ}{Ψ : Subset Δ}{Γ Γ′ : ExCtx Δ}{T : Ty Δ} →
  Substᶜᵗ {Ψ = Ψ} Γ Γ′ →
  Substᶜᵗ {Ψ = Ψ} (Γ ▷ T) (Γ′ ▷ T)
extsᶜᵗ σ Zᵉ = ` Zᵉ
extsᶜᵗ σ (Sᵉ x) = renameᶜᵗ Sᵉ (σ x)

wk-substᶜᵗ :
  ∀ {Δ}{Ψ : Subset Δ}{Γ Γ′ : ExCtx Δ} →
  Substᶜᵗ {Ψ = Ψ} Γ Γ′ →
  Substᶜᵗ {Ψ = outside ∷ Ψ} (renameᵉ Sᵗ Γ) (renameᵉ Sᵗ Γ′)
wk-substᶜᵗ {Γ = ∅} σ ()
wk-substᶜᵗ {Γ = Γ ▷ T} σ Zᵉ = renameᵗᶜᵗ Sᵗ renames-wk (σ Zᵉ)
wk-substᶜᵗ {Γ = Γ ▷ T} σ (Sᵉ x) =
  wk-substᶜᵗ (λ y → σ (Sᵉ y)) x

substᶜᵗ :
  ∀ {Δ}{Ψ : Subset Δ}{Γ Γ′ : ExCtx Δ}{T : Ty Δ} →
  Substᶜᵗ {Ψ = Ψ} Γ Γ′ →
  Ex {Ψ = Ψ} Γ T →
  Ex {Ψ = Ψ} Γ′ T
substᶜᵗ σ (` x) = σ x
substᶜᵗ σ (cst b) = cst b
substᶜᵗ σ (λx: T ⇒ M) = λx: T ⇒ (substᶜᵗ (extsᶜᵗ σ) M)
substᶜᵗ σ (app M N) = app (substᶜᵗ σ M) (substᶜᵗ σ N)
substᶜᵗ σ (ΛX M) = ΛX (substᶜᵗ (wk-substᶜᵗ σ) M)
substᶜᵗ σ (tapp M U) = tapp (substᶜᵗ σ M) U
substᶜᵗ σ (capp M s⊢) = capp (substᶜᵗ σ M) s⊢
substᶜᵗ σ (blame ℓ) = blame ℓ

singleᶜᵗ :
  ∀ {Δ}{Ψ : Subset Δ}{Γ : ExCtx Δ}{T : Ty Δ} →
  Ex {Ψ = Ψ} Γ T →
  Substᶜᵗ {Ψ = Ψ} (Γ ▷ T) Γ
singleᶜᵗ N Zᵉ = N
singleᶜᵗ N (Sᵉ x) = ` x

infixl 8 _[_]
_[_] :
  ∀ {Δ}{Ψ : Subset Δ}{Γ : ExCtx Δ}{S T : Ty Δ} →
  Ex {Ψ = Ψ} (Γ ▷ S) T →
  Ex {Ψ = Ψ} Γ S →
  Ex {Ψ = Ψ} Γ T
M [ N ] = substᶜᵗ (singleᶜᵗ N) M
