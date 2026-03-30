module TermSubst where

-- File Charter:
--   * Term-level substitution interfaces used by reduction.
--   * This module is the home for term-substitution definitions/lemmas.
--   * Keep operational semantics in `Reduction.agda`.
-- Note to self:
--   * If a proof is primarily about term substitution behavior, put it here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (map; []; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)

open import Types
open import Store
open import Ctx
open import Imprecision
open import PolyImp

------------------------------------------------------------------------
-- Term-variable renaming and substitution
------------------------------------------------------------------------

Renameˣ :
  (Δ : TyCtx) (Ψ : SealCtx) →
  Ctx Δ Ψ → Ctx Δ Ψ → Set
Renameˣ Δ Ψ Γ Γ′ =
  ∀ {A : Ty Δ Ψ} {x : Var} →
  Γ ∋ x ⦂ A →
  Σ[ y ∈ Var ] (Γ′ ∋ y ⦂ A)

Substˣ :
  (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ) →
  Ctx Δ Ψ → Ctx Δ Ψ → Set
Substˣ Δ Ψ Σ Γ Γ′ =
  ∀ {A : Ty Δ Ψ}{x : Var} →
  Γ ∋ x ⦂ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ A

extʳ :
  ∀{Δ}{Ψ}{Γ Γ′ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Renameˣ Δ Ψ Γ Γ′ →
  Renameˣ Δ Ψ (A ∷ Γ) (A ∷ Γ′)
extʳ ρ Z = _ , Z
extʳ ρ (S h) with ρ h
... | y , h′ = suc y , S h′

wkʳ :
  ∀{Δ}{Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Renameˣ Δ Ψ Γ (A ∷ Γ)
wkʳ {x = x} h = suc x , S h

map∋ :
  ∀{Δ}{Ψ}{Δ′}{Ψ′}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty Δ Ψ} →
  (f : Ty Δ Ψ → Ty Δ′ Ψ′) →
  Γ ∋ x ⦂ A →
  map f Γ ∋ x ⦂ f A
map∋ f Z = Z
map∋ f (S h) = S (map∋ f h)

unmap∋-⤊ᵗ :
  ∀{Δ}{Ψ}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty (suc Δ) Ψ} →
  ⤊ᵗ Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty Δ Ψ ] Σ[ _ ∈ (A ≡ renameᵗ Sᵗ B) ] (Γ ∋ x ⦂ B)
unmap∋-⤊ᵗ {Γ = B ∷ Γ} Z = B , refl , Z
unmap∋-⤊ᵗ {Γ = B ∷ Γ} (S h) with unmap∋-⤊ᵗ {Γ = Γ} h
... | C , eq , h′ = C , eq , S h′

liftᵗʳ :
  ∀{Δ}{Ψ}{Γ Γ′ : Ctx Δ Ψ} →
  Renameˣ Δ Ψ Γ Γ′ →
  Renameˣ (suc Δ) Ψ (⤊ᵗ Γ) (⤊ᵗ Γ′)
liftᵗʳ {Γ′ = Γ′} ρ h with unmap∋-⤊ᵗ h
... | B , eq , h₀ with ρ h₀
... | y , h₁ =
  y ,
  subst
    (λ T → ⤊ᵗ Γ′ ∋ y ⦂ T)
    (sym eq)
    (map∋ (renameᵗ Sᵗ) h₁)

unmap∋-⤊ˢ :
  ∀{Δ}{Ψ}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty Δ (suc Ψ)} →
  ⤊ˢ Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty Δ Ψ ] Σ[ _ ∈ (A ≡ ⇑ˢ B) ] (Γ ∋ x ⦂ B)
unmap∋-⤊ˢ {Γ = B ∷ Γ} Z = B , refl , Z
unmap∋-⤊ˢ {Γ = B ∷ Γ} (S h) with unmap∋-⤊ˢ {Γ = Γ} h
... | C , eq , h′ = C , eq , S h′

liftˢʳ :
  ∀{Δ}{Ψ}{Γ Γ′ : Ctx Δ Ψ} →
  Renameˣ Δ Ψ Γ Γ′ →
  Renameˣ Δ (suc Ψ) (⤊ˢ Γ) (⤊ˢ Γ′)
liftˢʳ {Γ′ = Γ′} ρ h with unmap∋-⤊ˢ h
... | B , eq , h₀ with ρ h₀
... | y , h₁ =
  y ,
  subst
    (λ T → ⤊ˢ Γ′ ∋ y ⦂ T)
    (sym eq)
    (map∋ ⇑ˢ h₁)

------------------------------------------------------------------------
-- Store weakening for imprecision witnesses, casts, and terms
------------------------------------------------------------------------

mutual
  wkΣᵖᵃ :
    ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    Σ ⊢ A ⊑ᵃ B →
    Σ′ ⊢ A ⊑ᵃ B
  wkΣᵖᵃ w (tag g ℓ) = tag g ℓ
  wkΣᵖᵃ w (`⊥ ℓ) = `⊥ ℓ
  wkΣᵖᵃ w (seal h) = seal (wkLookupˢ w h)
  wkΣᵖᵃ w (p ↦ q) = wkΣᵖ w p ↦ wkΣᵖ w q
  wkΣᵖᵃ w (∀ᵖ p) = ∀ᵖ (wkΣᵖ w p)
  wkΣᵖᵃ w (ν i) = ν (wkΣᵖ (ν-⊆ˢ `★ w) i)

  wkΣᵖ :
    ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    Σ ⊢ A ⊑ B →
    Σ′ ⊢ A ⊑ B
  wkΣᵖ w id = id
  wkΣᵖ w (p ； a) = wkΣᵖ w p ； wkΣᵖᵃ w a

wkΣ-term :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Σ ⊆ˢ Σ′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ ⊢ A
wkΣ-term w (` h) = ` h
wkΣ-term w (ƛ A ⇒ M) = ƛ A ⇒ wkΣ-term w M
wkΣ-term w (L · M) = wkΣ-term w L · wkΣ-term w M
wkΣ-term w (Λ M) = Λ (wkΣ-term w M)
wkΣ-term w ((M • α [ h ]) eq) =
  cast⊢
    refl
    refl
    (sym eq)
    ((wkΣ-term w M • α [ wkLookupˢ w h ]) refl)
wkΣ-term w (ν:= A ∙ M) = ν:= A ∙ wkΣ-term (ν-⊆ˢ A w) M
wkΣ-term w ($ κ eq) = $ κ eq
wkΣ-term w (L ⊕[ op ] M) = wkΣ-term w L ⊕[ op ] wkΣ-term w M
wkΣ-term w (M at[ up ] p) = wkΣ-term w M at[ up ] wkΣᵖ w p
wkΣ-term w (M at[ down ] p) = wkΣ-term w M at[ down ] wkΣᵖ w p
wkΣ-term w (blame ℓ) = blame ℓ

------------------------------------------------------------------------
-- Renaming and substitution actions on terms
------------------------------------------------------------------------

renameˣ-term :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameˣ Δ Ψ Γ Γ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ A
renameˣ-term ρ (` h) with ρ h
... | y , h′ = ` h′
renameˣ-term ρ (ƛ A ⇒ M) = ƛ A ⇒ renameˣ-term (extʳ ρ) M
renameˣ-term ρ (L · M) = renameˣ-term ρ L · renameˣ-term ρ M
renameˣ-term ρ (Λ M) = Λ (renameˣ-term (liftᵗʳ ρ) M)
renameˣ-term ρ ((M • α [ h ]) eq) =
  cast⊢
    refl
    refl
    (sym eq)
    ((renameˣ-term ρ M • α [ h ]) refl)
renameˣ-term ρ (ν:= A ∙ M) = ν:= A ∙ renameˣ-term (liftˢʳ ρ) M
renameˣ-term ρ ($ κ eq) = $ κ eq
renameˣ-term ρ (L ⊕[ op ] M) = renameˣ-term ρ L ⊕[ op ] renameˣ-term ρ M
renameˣ-term ρ (M at[ up ] p) = renameˣ-term ρ M at[ up ] p
renameˣ-term ρ (M at[ down ] p) = renameˣ-term ρ M at[ down ] p
renameˣ-term ρ (blame ℓ) = blame ℓ

↑ˢ :
  ∀{Ψ}{Σ : Store Ψ} →
  (A : Ty 0 Ψ) →
  ⟰ˢ Σ ⊆ˢ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ)
↑ˢ A = drop ⊆ˢ-refl

liftᵗˣ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ} →
  Substˣ Δ Ψ Σ Γ Γ′ →
  Substˣ (suc Δ) Ψ Σ (⤊ᵗ Γ) (⤊ᵗ Γ′)
liftᵗˣ {Γ′ = Γ′} σ h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  cast⊢
    refl
    refl
    (sym eq)
    (renameᵗ-term Sᵗ (σ h₀))

liftˢˣ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ} →
  (A : Ty 0 Ψ) →
  Substˣ Δ Ψ Σ Γ Γ′ →
  Substˣ Δ (suc Ψ) ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) (⤊ˢ Γ) (⤊ˢ Γ′)
liftˢˣ {Σ = Σ} A σ h with unmap∋-⤊ˢ h
... | B , eq , h₀ =
  cast⊢
    refl
    refl
    (sym eq)
    (wkΣ-term (↑ˢ A) (renameˢ-term Sˢ (σ h₀)))

extˣ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Substˣ Δ Ψ Σ Γ Γ′ →
  Substˣ Δ Ψ Σ (A ∷ Γ) (A ∷ Γ′)
extˣ σ Z = ` Z
extˣ σ (S h) = renameˣ-term wkʳ (σ h)

substˣ-term :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (σ : Substˣ Δ Ψ Σ Γ Γ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ A
substˣ-term σ (` h) = σ h
substˣ-term σ (ƛ A ⇒ M) = ƛ A ⇒ substˣ-term (extˣ σ) M
substˣ-term σ (L · M) = substˣ-term σ L · substˣ-term σ M
substˣ-term σ (Λ M) = Λ (substˣ-term (liftᵗˣ σ) M)
substˣ-term σ ((M • α [ h ]) eq) =
  cast⊢
    refl
    refl
    (sym eq)
    ((substˣ-term σ M • α [ h ]) refl)
substˣ-term σ (ν:= A ∙ M) = ν:= A ∙ substˣ-term (liftˢˣ A σ) M
substˣ-term σ ($ κ eq) = $ κ eq
substˣ-term σ (L ⊕[ op ] M) = substˣ-term σ L ⊕[ op ] substˣ-term σ M
substˣ-term σ (M at[ up ] p) = substˣ-term σ M at[ up ] p
substˣ-term σ (M at[ down ] p) = substˣ-term σ M at[ down ] p
substˣ-term σ (blame ℓ) = blame ℓ

------------------------------------------------------------------------
-- Single-variable and single-type substitution APIs
------------------------------------------------------------------------

infixl 8 _[_]
infixl 8 _[_]ᵀ

singleVarEnv :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Substˣ Δ Ψ Σ (A ∷ Γ) Γ
singleVarEnv V Z = V
singleVarEnv V (S h) = ` h

_[_] :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B
N [ V ] = substˣ-term (singleVarEnv V) N

map-singleTyEnv-⤊ᵗ :
  ∀ {Δ}{Ψ}
  (T : Ty Δ Ψ) (Γ : Ctx Δ Ψ) →
  map (substᵗ (singleTyEnv T)) (⤊ᵗ Γ) ≡ Γ
map-singleTyEnv-⤊ᵗ T [] = refl
map-singleTyEnv-⤊ᵗ T (A ∷ Γ) =
  cong₂ _∷_
    (open-renᵗ-suc A T)
    (map-singleTyEnv-⤊ᵗ T Γ)

_[_]ᵀ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty (suc Δ) Ψ} →
  (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ A →
  (T : Ty Δ Ψ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A [ T ]ᵗ)
_[_]ᵀ {Γ = Γ} N T =
  cast⊢
    refl
    (map-singleTyEnv-⤊ᵗ T Γ)
    refl
    (substᵗ-term (singleTyEnv T) N)
