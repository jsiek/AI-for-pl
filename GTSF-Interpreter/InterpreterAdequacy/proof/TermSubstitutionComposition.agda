module InterpreterAdequacy.proof.TermSubstitutionComposition where

-- File Charter:
--   * Supplies the missing parallel term-substitution fusion laws needed by
--     beta reification.
--   * Proves renaming/substitution commutation in both directions and then
--     substitution composition for all Nu term forms.
--   * Is syntax-only and independent of interpreter or reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

import NuTerms as N
open import InterpreterAdequacy.proof.SyntaxReification using
  (substˣᵐ-cong)
open import proof.Core.Properties.NuTermProperties using
  ( renameˣᵐ-compose
  ; renameˣᵐ-cong
  ; renameˣ-renameᵗᵐ
  )
open import proof.Substitution.Term.TermSubstitutionSyntax using
  (substˣᵐ-renameᵗᵐ)

infixr 9 _⨟ˢ_
_⨟ˢ_ : N.Substˣ → N.Substˣ → N.Substˣ
(σ ⨟ˢ τ) x = N.substˣᵐ τ (σ x)

subst-after-rename :
  ∀ σ ρ M →
  N.substˣᵐ σ (N.renameˣᵐ ρ M) ≡
    N.substˣᵐ (λ x → σ (ρ x)) M
subst-after-rename σ ρ (N.` x) = refl
subst-after-rename σ ρ (N.ƛ M) =
  cong N.ƛ_
    (trans
      (subst-after-rename (N.extˢˣ σ) (N.extʳ ρ) M)
      (substˣᵐ-cong ext-compose M))
  where
  ext-compose :
    ∀ x → N.extˢˣ σ (N.extʳ ρ x) ≡ N.extˢˣ (λ y → σ (ρ y)) x
  ext-compose zero = refl
  ext-compose (suc x) = refl
subst-after-rename σ ρ (L N.· M) =
  cong₂ N._·_ (subst-after-rename σ ρ L)
    (subst-after-rename σ ρ M)
subst-after-rename σ ρ (N.Λ M) =
  cong N.Λ_
    (trans
      (subst-after-rename (N.↑ᵗᵐ σ) ρ M)
      (substˣᵐ-cong lift-compose M))
  where
  lift-compose :
    ∀ x → N.↑ᵗᵐ σ (ρ x) ≡ N.↑ᵗᵐ (λ y → σ (ρ y)) x
  lift-compose x = refl
subst-after-rename σ ρ (M N.•) =
  cong N._• (subst-after-rename σ ρ M)
subst-after-rename σ ρ (N.ν A L c) =
  cong (λ L′ → N.ν A L′ c) (subst-after-rename σ ρ L)
subst-after-rename σ ρ (N.$ κ) = refl
subst-after-rename σ ρ (L N.⊕[ op ] M) =
  cong₂ N._⊕[ op ]_ (subst-after-rename σ ρ L)
    (subst-after-rename σ ρ M)
subst-after-rename σ ρ (M N.⟨ c ⟩) =
  cong (λ M′ → M′ N.⟨ c ⟩) (subst-after-rename σ ρ M)
subst-after-rename σ ρ N.blame = refl

rename-after-subst :
  ∀ ρ σ M →
  N.renameˣᵐ ρ (N.substˣᵐ σ M) ≡
    N.substˣᵐ (λ x → N.renameˣᵐ ρ (σ x)) M
rename-after-subst ρ σ (N.` x) = refl
rename-after-subst ρ σ (N.ƛ M) =
  cong N.ƛ_
    (trans
      (rename-after-subst (N.extʳ ρ) (N.extˢˣ σ) M)
      (substˣᵐ-cong ext-compose M))
  where
  ext-compose :
    ∀ x →
    N.renameˣᵐ (N.extʳ ρ) (N.extˢˣ σ x) ≡
      N.extˢˣ (λ y → N.renameˣᵐ ρ (σ y)) x
  ext-compose zero = refl
  ext-compose (suc x) =
    trans
      (renameˣᵐ-compose suc (N.extʳ ρ) (σ x))
      (trans
        (renameˣᵐ-cong (λ y → refl) (σ x))
        (sym (renameˣᵐ-compose ρ suc (σ x))))
rename-after-subst ρ σ (L N.· M) =
  cong₂ N._·_ (rename-after-subst ρ σ L)
    (rename-after-subst ρ σ M)
rename-after-subst ρ σ (N.Λ M) =
  cong N.Λ_
    (trans
      (rename-after-subst ρ (N.↑ᵗᵐ σ) M)
      (substˣᵐ-cong lift-compose M))
  where
  lift-compose :
    ∀ x →
    N.renameˣᵐ ρ (N.↑ᵗᵐ σ x) ≡
      N.↑ᵗᵐ (λ y → N.renameˣᵐ ρ (σ y)) x
  lift-compose x = renameˣ-renameᵗᵐ ρ suc (σ x)
rename-after-subst ρ σ (M N.•) =
  cong N._• (rename-after-subst ρ σ M)
rename-after-subst ρ σ (N.ν A L c) =
  cong (λ L′ → N.ν A L′ c) (rename-after-subst ρ σ L)
rename-after-subst ρ σ (N.$ κ) = refl
rename-after-subst ρ σ (L N.⊕[ op ] M) =
  cong₂ N._⊕[ op ]_ (rename-after-subst ρ σ L)
    (rename-after-subst ρ σ M)
rename-after-subst ρ σ (M N.⟨ c ⟩) =
  cong (λ M′ → M′ N.⟨ c ⟩) (rename-after-subst ρ σ M)
rename-after-subst ρ σ N.blame = refl

substˣᵐ-compose :
  ∀ σ τ M →
  N.substˣᵐ τ (N.substˣᵐ σ M) ≡
    N.substˣᵐ (σ ⨟ˢ τ) M
substˣᵐ-compose σ τ (N.` x) = refl
substˣᵐ-compose σ τ (N.ƛ M) =
  cong N.ƛ_
    (trans
      (substˣᵐ-compose (N.extˢˣ σ) (N.extˢˣ τ) M)
      (substˣᵐ-cong ext-compose M))
  where
  ext-compose :
    ∀ x →
    ((N.extˢˣ σ) ⨟ˢ (N.extˢˣ τ)) x ≡
      N.extˢˣ (σ ⨟ˢ τ) x
  ext-compose zero = refl
  ext-compose (suc x) =
    trans
      (subst-after-rename (N.extˢˣ τ) suc (σ x))
      (trans
        (substˣᵐ-cong (λ y → refl) (σ x))
        (sym (rename-after-subst suc τ (σ x))))
substˣᵐ-compose σ τ (L N.· M) =
  cong₂ N._·_ (substˣᵐ-compose σ τ L)
    (substˣᵐ-compose σ τ M)
substˣᵐ-compose σ τ (N.Λ M) =
  cong N.Λ_
    (trans
      (substˣᵐ-compose (N.↑ᵗᵐ σ) (N.↑ᵗᵐ τ) M)
      (substˣᵐ-cong lift-compose M))
  where
  lift-compose :
    ∀ x →
    ((N.↑ᵗᵐ σ) ⨟ˢ (N.↑ᵗᵐ τ)) x ≡
      N.↑ᵗᵐ (σ ⨟ˢ τ) x
  lift-compose x =
    trans
      (substˣᵐ-renameᵗᵐ
        suc (N.↑ᵗᵐ τ) τ (σ x) (λ y → refl))
      refl
substˣᵐ-compose σ τ (M N.•) =
  cong N._• (substˣᵐ-compose σ τ M)
substˣᵐ-compose σ τ (N.ν A L c) =
  cong (λ L′ → N.ν A L′ c) (substˣᵐ-compose σ τ L)
substˣᵐ-compose σ τ (N.$ κ) = refl
substˣᵐ-compose σ τ (L N.⊕[ op ] M) =
  cong₂ N._⊕[ op ]_ (substˣᵐ-compose σ τ L)
    (substˣᵐ-compose σ τ M)
substˣᵐ-compose σ τ (M N.⟨ c ⟩) =
  cong (λ M′ → M′ N.⟨ c ⟩) (substˣᵐ-compose σ τ M)
substˣᵐ-compose σ τ N.blame = refl

substˣᵐ-identity :
  ∀ M → N.substˣᵐ N.`_ M ≡ M
substˣᵐ-identity (N.` x) = refl
substˣᵐ-identity (N.ƛ M) =
  cong N.ƛ_
    (trans
      (substˣᵐ-cong (λ { zero → refl ; (suc x) → refl }) M)
      (substˣᵐ-identity M))
substˣᵐ-identity (L N.· M) =
  cong₂ N._·_ (substˣᵐ-identity L) (substˣᵐ-identity M)
substˣᵐ-identity (N.Λ M) =
  cong N.Λ_
    (trans
      (substˣᵐ-cong (λ x → refl) M)
      (substˣᵐ-identity M))
substˣᵐ-identity (M N.•) =
  cong N._• (substˣᵐ-identity M)
substˣᵐ-identity (N.ν A L c) =
  cong (λ L′ → N.ν A L′ c) (substˣᵐ-identity L)
substˣᵐ-identity (N.$ κ) = refl
substˣᵐ-identity (L N.⊕[ op ] M) =
  cong₂ N._⊕[ op ]_
    (substˣᵐ-identity L) (substˣᵐ-identity M)
substˣᵐ-identity (M N.⟨ c ⟩) =
  cong (λ M′ → M′ N.⟨ c ⟩) (substˣᵐ-identity M)
substˣᵐ-identity N.blame = refl
