module TermProperties where

-- File Charter:
--   * Term-variable metatheory for extrinsic terms.
--   * Renaming/substitution environments for term variables, with lifting through
--   * type/seal binders and typing-preservation theorems.
--   * Single-variable and single-type substitution APIs used by reduction.
-- Note to self:
--   * Keep raw term syntax and type/seal structural actions in `Terms.agda`;
--   * this file owns term-variable substitution infrastructure.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (map; []; _∷_)
open import Data.Nat using (suc; zero; z<s; s<s)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)

open import Types
open import TypeProperties
open import Store
open import Ctx using (⤊ᵗ)
open import UpDown
open import Terms hiding (_[_]ᵀ)

------------------------------------------------------------------------
-- Term-variable renaming and substitution environments
------------------------------------------------------------------------

Renameˣ : Set
Renameˣ = Var → Var

Renameˣ-wt : (Γ Γ′ : Ctx) (ρ : Renameˣ) → Set
Renameˣ-wt Γ Γ′ ρ = ∀ {A : Ty}{x : Var} → (h : Γ ∋ x ⦂ A) → Γ′ ∋ ρ x ⦂ A

Substˣ : Set
Substˣ = Var → Term

Substˣ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx} → (σ : Substˣ) → Set
Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ =
  ∀ {A : Ty}{x : Var} → (h : Γ ∋ x ⦂ A) → Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ σ x ⦂ A

extʳ : Renameˣ → Renameˣ
extʳ ρ zero = zero
extʳ ρ (suc x) = suc (ρ x)

extʳ-wt : ∀ {Γ Γ′ : Ctx}{A : Ty} → (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Renameˣ-wt (A ∷ Γ) (A ∷ Γ′) (extʳ ρ)
extʳ-wt ρ hρ Z = Z
extʳ-wt ρ hρ (S h) = S (hρ h)

wkʳ : Renameˣ
wkʳ x = suc x

wkʳ-wt : ∀ {Γ : Ctx}{A B : Ty}{x : Var} →
  (h : Γ ∋ x ⦂ A) →
  (B ∷ Γ) ∋ wkʳ x ⦂ A
wkʳ-wt h = S h

map∋ : ∀ {Γ : Ctx}{x : Var}{A : Ty} → (f : Ty → Ty) →
  Γ ∋ x ⦂ A →
  map f Γ ∋ x ⦂ f A
map∋ f Z = Z
map∋ f (S h) = S (map∋ f h)

unmap∋-⤊ᵗ : ∀ {Γ : Ctx}{x : Var}{A : Ty} →
  ⤊ᵗ Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty ] Σ[ _ ∈ (A ≡ renameᵗ suc B) ] (Γ ∋ x ⦂ B)
unmap∋-⤊ᵗ {Γ = B ∷ Γ} Z = B , refl , Z
unmap∋-⤊ᵗ {Γ = B ∷ Γ} (S h) with unmap∋-⤊ᵗ {Γ = Γ} h
... | C , eq , h′ = C , eq , S h′

liftᵗʳ : Renameˣ → Renameˣ
liftᵗʳ ρ x = ρ x

liftᵗʳ-wt : ∀ {Γ Γ′ : Ctx} → (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Renameˣ-wt (⤊ᵗ Γ) (⤊ᵗ Γ′) (liftᵗʳ ρ)
liftᵗʳ-wt {Γ′ = Γ′} ρ hρ {x = x} h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  subst
    (λ T → ⤊ᵗ Γ′ ∋ ρ x ⦂ T)
    (sym eq)
    (map∋ (renameᵗ suc) (hρ h₀))

unmap∋-⤊ˢ : ∀ {Γ : Ctx}{x : Var}{A : Ty} →
  ⤊ˢ Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty ] Σ[ _ ∈ (A ≡ ⇑ˢ B) ] (Γ ∋ x ⦂ B)
unmap∋-⤊ˢ {Γ = B ∷ Γ} Z = B , refl , Z
unmap∋-⤊ˢ {Γ = B ∷ Γ} (S h) with unmap∋-⤊ˢ {Γ = Γ} h
... | C , eq , h′ = C , eq , S h′

liftˢʳ-wt : ∀ {Γ Γ′ : Ctx} → (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Renameˣ-wt (⤊ˢ Γ) (⤊ˢ Γ′) ρ
liftˢʳ-wt {Γ′ = Γ′} ρ hρ {x = x} h with unmap∋-⤊ˢ h
... | B , eq , h₀ =
  subst
    (λ T → ⤊ˢ Γ′ ∋ ρ x ⦂ T)
    (sym eq)
    (map∋ ⇑ˢ (hρ h₀))

------------------------------------------------------------------------
-- Renaming and substitution actions on terms (term variables)
------------------------------------------------------------------------

renameˣᵐ : Renameˣ → Term → Term
renameˣᵐ ρ (` x) = ` (ρ x)
renameˣᵐ ρ (ƛ A ⇒ M) = ƛ A ⇒ renameˣᵐ (extʳ ρ) M
renameˣᵐ ρ (L · M) = renameˣᵐ ρ L · renameˣᵐ ρ M
renameˣᵐ ρ (Λ M) = Λ (renameˣᵐ (liftᵗʳ ρ) M)
renameˣᵐ ρ (M • α) = renameˣᵐ ρ M • α
renameˣᵐ ρ (ν:= A ∙ M) = ν:= A ∙ renameˣᵐ ρ M
renameˣᵐ ρ ($ κ) = $ κ
renameˣᵐ ρ (L ⊕[ op ] M) = renameˣᵐ ρ L ⊕[ op ] renameˣᵐ ρ M
renameˣᵐ ρ (at M d c) = at (renameˣᵐ ρ M) d c
renameˣᵐ ρ (blame ℓ) = blame ℓ

renameˣ-term-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{M : Term}{A : Ty} →
  (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  (M⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ renameˣᵐ ρ M ⦂ A
renameˣ-term-wt ρ hρ (⊢` h) = ⊢` (hρ h)
renameˣ-term-wt ρ hρ (⊢ƛ {A = A} wfA M) =
  ⊢ƛ wfA (renameˣ-term-wt (extʳ ρ) (extʳ-wt ρ hρ) M)
renameˣ-term-wt ρ hρ (⊢· L M) =
  ⊢· (renameˣ-term-wt ρ hρ L) (renameˣ-term-wt ρ hρ M)
renameˣ-term-wt ρ hρ (⊢Λ M) =
  ⊢Λ (renameˣ-term-wt (liftᵗʳ ρ) (liftᵗʳ-wt ρ hρ) M)
renameˣ-term-wt ρ hρ (⊢• {α = α} M α∈ h) =
  ⊢• (renameˣ-term-wt ρ hρ M) α∈ h
renameˣ-term-wt ρ hρ (⊢ν {A = A} wfA M) =
  ⊢ν wfA (renameˣ-term-wt ρ (liftˢʳ-wt ρ hρ) M)
renameˣ-term-wt ρ hρ (⊢$ κ) = ⊢$ κ
renameˣ-term-wt ρ hρ (⊢⊕ L op M) =
  ⊢⊕ (renameˣ-term-wt ρ hρ L) op (renameˣ-term-wt ρ hρ M)
renameˣ-term-wt ρ hρ (⊢at {d = d} {c = c} M hp) =
  ⊢at {c = c} (renameˣ-term-wt ρ hρ M) hp
renameˣ-term-wt ρ hρ (⊢blame ℓ) = ⊢blame ℓ

↑ˢ : ∀ {Σ : Store} → (A : Ty) →
  ⟰ˢ Σ ⊆ˢ ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ)
↑ˢ A = drop ⊆ˢ-refl

↑ᵗᵐ : Substˣ → Substˣ
↑ᵗᵐ σ x = renameᵗᵐ suc (σ x)

↑ᵗᵐ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx} →
  (σ : Substˣ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ →
  Substˣ-wt {suc Δ} {Ψ} {⟰ᵗ Σ} {⤊ᵗ Γ} {⤊ᵗ Γ′} (↑ᵗᵐ σ)
↑ᵗᵐ-wt σ hσ {x = x} h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  cong-⊢⦂
    refl
    refl
    refl
    (sym eq)
    (renameᵗ-term suc TyRenameWf-suc (hσ {x = x} h₀))

↑ˢᵐ : Substˣ → Substˣ
↑ˢᵐ σ x = renameˢᵐ suc (σ x)

↑ˢᵐ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx} →
  (A : Ty) →
  (σ : Substˣ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ →
  Substˣ-wt {Δ} {suc Ψ} {((zero , ⇑ˢ A) ∷ ⟰ˢ Σ)} {⤊ˢ Γ} {⤊ˢ Γ′}
    (↑ˢᵐ σ)
↑ˢᵐ-wt A σ hσ {x = x} h with unmap∋-⤊ˢ h
... | B , eq , h₀ =
  cong-⊢⦂ refl refl refl (sym eq)
    (wkΣ-term (↑ˢ A) (⇑ˢᵐ (hσ {x = x} h₀)))

extˣ : Substˣ → Substˣ
extˣ σ zero = ` zero
extˣ σ (suc x) = renameˣᵐ wkʳ (σ x)

extˣ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{A : Ty} →
  (σ : Substˣ) →
  (hσ : Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {A ∷ Γ} {A ∷ Γ′} (extˣ σ)
extˣ-wt σ hσ Z = ⊢` Z
extˣ-wt σ hσ (S h) = renameˣ-term-wt wkʳ wkʳ-wt (hσ h)

substˣ-term : Substˣ → Term → Term
substˣ-term σ (` x) = σ x
substˣ-term σ (ƛ A ⇒ M) = ƛ A ⇒ substˣ-term (extˣ σ) M
substˣ-term σ (L · M) = substˣ-term σ L · substˣ-term σ M
substˣ-term σ (Λ M) = Λ (substˣ-term (↑ᵗᵐ σ) M)
substˣ-term σ (M • α) = substˣ-term σ M • α
substˣ-term σ (ν:= A ∙ M) = ν:= A ∙ substˣ-term (↑ˢᵐ σ) M
substˣ-term σ ($ κ) = $ κ
substˣ-term σ (L ⊕[ op ] M) = substˣ-term σ L ⊕[ op ] substˣ-term σ M
substˣ-term σ (at M d c) = at (substˣ-term σ M) d c
substˣ-term σ (blame ℓ) = blame ℓ

substˣ-term-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{M : Term}{A : Ty} →
  (σ : Substˣ) →
  (hσ : Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ) →
  (M⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ substˣ-term σ M ⦂ A
substˣ-term-wt σ hσ (⊢` h) = hσ h
substˣ-term-wt σ hσ (⊢ƛ {A = A} wfA M) =
  ⊢ƛ wfA (substˣ-term-wt (extˣ σ) (extˣ-wt {A = A} σ hσ) M)
substˣ-term-wt σ hσ (⊢· L M) =
  ⊢· (substˣ-term-wt σ hσ L) (substˣ-term-wt σ hσ M)
substˣ-term-wt σ hσ (⊢Λ M) =
  ⊢Λ (substˣ-term-wt (↑ᵗᵐ σ) (↑ᵗᵐ-wt σ hσ) M)
substˣ-term-wt σ hσ (⊢• {α = α} M α∈ h) =
  ⊢• (substˣ-term-wt σ hσ M) α∈ h
substˣ-term-wt σ hσ (⊢ν {A = A} wfA M) =
  ⊢ν wfA (substˣ-term-wt (↑ˢᵐ σ) (↑ˢᵐ-wt A σ hσ) M)
substˣ-term-wt σ hσ (⊢$ κ) = ⊢$ κ
substˣ-term-wt σ hσ (⊢⊕ L op M) =
  ⊢⊕ (substˣ-term-wt σ hσ L) op (substˣ-term-wt σ hσ M)
substˣ-term-wt σ hσ (⊢at {d = d} {c = c} M hp) =
  ⊢at {c = c} (substˣ-term-wt σ hσ M) hp
substˣ-term-wt σ hσ (⊢blame ℓ) = ⊢blame ℓ

------------------------------------------------------------------------
-- Single-variable and single-type substitution APIs
------------------------------------------------------------------------

infixl 8 _[_]
infixl 8 _[_]ᵀ

singleVarEnv : Term → Substˣ
singleVarEnv V zero = V
singleVarEnv V (suc x) = ` x

singleVarEnv-wt : ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  Substˣ-wt {Δ} {Ψ} {Σ} {A ∷ Γ} {Γ} (singleVarEnv V)
singleVarEnv-wt {V = V} V⊢ Z = V⊢
singleVarEnv-wt V⊢ (S h) = ⊢` h

_[_] : Term → Term → Term
N [ V ] = substˣ-term (singleVarEnv V) N

[]-wt : ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{N V : Term}{A B : Ty} →
  (N⊢ : Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ N ⦂ B) →
  (V⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (N [ V ]) ⦂ B
[]-wt {V = V} N⊢ V⊢ =
  substˣ-term-wt (singleVarEnv V) (singleVarEnv-wt V⊢) N⊢

map-singleTyEnv-⤊ᵗ : (T : Ty) (Γ : Ctx) →
  map (substᵗ (singleTyEnv T)) (⤊ᵗ Γ) ≡ Γ
map-singleTyEnv-⤊ᵗ T [] = refl
map-singleTyEnv-⤊ᵗ T (A ∷ Γ) =
  cong₂ _∷_
    (open-renᵗ-suc A T)
    (map-singleTyEnv-⤊ᵗ T Γ)

substStoreᵗ-singleTyEnv-⟰ᵗ :
  (T : Ty) (Σ : Store) →
  substStoreᵗ (singleTyEnv T) (⟰ᵗ Σ) ≡ Σ
substStoreᵗ-singleTyEnv-⟰ᵗ T [] = refl
substStoreᵗ-singleTyEnv-⟰ᵗ T ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (open-renᵗ-suc A T))
    (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ)

singleTyEnv-Wf : ∀ {Δ Ψ} (T : Ty) →
  WfTy Δ Ψ T →
  TySubstWf (suc Δ) Δ Ψ (singleTyEnv T)
singleTyEnv-Wf T wfT {zero} z<s = wfT
singleTyEnv-Wf T wfT {suc X} (s<s X<Δ) = wfVar X<Δ

_[_]ᵀ : Term → Ty → Term
M [ T ]ᵀ = substᵗᵐ (singleTyEnv T) M

[]ᵀ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  (M⊢ : (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ M ⦂ A) →
  (T : Ty) →
  (wfT : WfTy Δ Ψ T) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M [ T ]ᵀ) ⦂ (A [ T ]ᵗ)
[]ᵀ-wt {Σ = Σ} {Γ = Γ} {M = M} {A = A} M⊢ T wfT =
  cong-⊢⦂
    (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ)
    (map-singleTyEnv-⤊ᵗ T Γ)
    refl
    refl
    (substᵗ-term (singleTyEnv T) (singleTyEnv-Wf T wfT) M⊢)
