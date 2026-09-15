module strong.proof.ScratchAlloc where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.proof.Flat

-- The ambient context assigns the name 0 to the level 0, which the
-- empty store does NOT contain.
Δ₀ : Ctxᵗ
Δ₀ = asgn (lvl zero) ∷ [] ∥ []

flat-Δ₀ : Flat Δ₀
flat-Δ₀ = flat (fu-asgn fu-[]) refl

sok-[] : StoreOk []
sok-[] ()

-- the ν body's context
Δ₁ : Ctxᵗ
Δ₁ = asgn (lvl zero) ∷ [] ∥ nuBind `ℕᴿ ∷ []

Δ₂ : Ctxᵗ
Δ₂ = [] ∥ nuBind `ℕᴿ ∷ []

Δ₃ : Ctxᵗ
Δ₃ = asgn (bse zero) ∷ [] ∥ nuBind `ℕᴿ ∷ []

c₀ : Conv
c₀ = show zero (bse zero) ∷ᶜ hide zero (lvl zero) ∷ᶜ id `ℕ

⊢c₀ : [] ∣ Δ₃ ⊢ c₀ ∶ `ℕ ⇝ `ℕ ⊣ Δ₁
⊢c₀ = conv-cons (conv-show wf-ℕ pop-here (λ ()))
        (conv-cons (conv-hide wf-ℕ pop-here (λ ())) (conv-id wf-ℕ))

nf-c₀ : NF c₀
nf-c₀ = nf-cons nf-show (nf-cons nf-hide nf-id irr-id) (irr-cons refl)

M₀ : Term
M₀ = ($ zero) ⟨ c₀ ⟩

⊢M₀ : [] ∣ Δ₁ ∣ [] ⊢ M₀ ⦂ `ℕ
⊢M₀ = ⊢⟨⟩ nf-c₀ ⊢$ ⊢c₀

⊢νM₀ : [] ∣ Δ₀ ∣ [] ⊢ ν `ℕᴿ ∙ M₀ ⦂ `ℕ
⊢νM₀ = ⊢ν wfᴿ-ℕ ⊢M₀

-- After the substitution the two crossings FUSE, so the conversion is
-- no longer a normal form and the contractum is not typable.
¬⊢subst : ¬ (([] ∷ʳ `ℕᴿ) ∣ Δ₀ ∣ [] ⊢ M₀ [ lvl (length {A = RepTy} []) ]ᵃᴹ ⦂ `ℕ)
¬⊢subst (⊢⟨⟩ (nf-cons hd tl (irr-cons ())) m c)

Alloc-Claim : Set
Alloc-Claim = ∀ {Sg Δ Γ R M A}
  → StoreOk Sg → Flat Δ
  → Sg ∣ Δ ∣ Γ ⊢ ν R ∙ M ⦂ A
  → (Sg ∷ʳ R) ∣ Δ ∣ Γ ⊢ M [ lvl (length Sg) ]ᵃᴹ ⦂ A

refuted : ¬ Alloc-Claim
refuted f = ¬⊢subst (f sok-[] flat-Δ₀ ⊢νM₀)
