module proof.NuTermProperties where

-- File Charter:
--   * Proof-only metatheory for Nu GTSF terms after the telescope redesign.
--   * Collects value preservation, telescope-step weakening, result-type
--     well-formedness, and the substitution/weakening obligations needed by
--     progress and preservation.
--   * The old split `Ctx`/`Store` infrastructure is intentionally absent:
--     ordinary type variables, seals, and term variables all live in `Telescope`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; ∃)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction
open import proof.CoercionProperties using (coercion-wf; renameᶜ-preserves-Inert)
open import proof.TypeProperties
  using (rename-cong; rename-compose; rename-shiftᵗ-comm;
         rename-shiftˢ-comm; subst-cong)

------------------------------------------------------------------------
-- Values under renaming and term substitution
------------------------------------------------------------------------

renameᵐ-preserves-Value :
  ∀ ρ σ {V} →
  Value V →
  Value (renameᵐ ρ σ V)
renameᵐ-preserves-Value ρ σ (ƛ N) = ƛ _
renameᵐ-preserves-Value ρ σ (Λ vV) =
  Λ (renameᵐ-preserves-Value (extᵗ ρ) σ vV)
renameᵐ-preserves-Value ρ σ ($ κ) = $ κ
renameᵐ-preserves-Value ρ σ (vV ⟨ i ⟩) =
  renameᵐ-preserves-Value ρ σ vV ⟨ renameᶜ-preserves-Inert ρ σ i ⟩

renameˢᵐ-preserves-Value :
  ∀ σ {V} →
  Value V →
  Value (renameˢᵐ σ V)
renameˢᵐ-preserves-Value σ = renameᵐ-preserves-Value idᵗ σ

renameˣᵐ-preserves-Value :
  ∀ ρ {V} →
  Value V →
  Value (renameˣᵐ ρ V)
renameˣᵐ-preserves-Value ρ (ƛ N) = ƛ _
renameˣᵐ-preserves-Value ρ (Λ vV) =
  Λ (renameˣᵐ-preserves-Value ρ vV)
renameˣᵐ-preserves-Value ρ ($ κ) = $ κ
renameˣᵐ-preserves-Value ρ (vV ⟨ i ⟩) =
  renameˣᵐ-preserves-Value ρ vV ⟨ i ⟩

substˣᵐ-preserves-Value :
  ∀ σ {V} →
  Value V →
  Value (substˣᵐ σ V)
substˣᵐ-preserves-Value σ (ƛ N) = ƛ _
substˣᵐ-preserves-Value σ (Λ vV) =
  Λ (substˣᵐ-preserves-Value (↑ᵗᵐ σ) vV)
substˣᵐ-preserves-Value σ ($ κ) = $ κ
substˣᵐ-preserves-Value σ (vV ⟨ i ⟩) =
  substˣᵐ-preserves-Value σ vV ⟨ i ⟩

------------------------------------------------------------------------
-- Raw renaming/substitution algebra
------------------------------------------------------------------------

extᵗ-cong :
  ∀ {ρ ρ′ : Renameᵗ} →
  (∀ X → ρ X ≡ ρ′ X) →
  ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
extᵗ-cong eq zero = refl
extᵗ-cong eq (suc X) = cong suc (eq X)

extˢ-cong :
  ∀ {σ σ′ : Renameˢ} →
  (∀ α → σ α ≡ σ′ α) →
  ∀ α → extˢ σ α ≡ extˢ σ′ α
extˢ-cong eq zero = refl
extˢ-cong eq (suc α) = cong suc (eq α)

renameᶜ-cong :
  ∀ {ρ ρ′ : Renameᵗ} {σ σ′ : Renameˢ} →
  (∀ X → ρ X ≡ ρ′ X) →
  (∀ α → σ α ≡ σ′ α) →
  (c : Coercion) →
  renameᶜ ρ σ c ≡ renameᶜ ρ′ σ′ c
renameᶜ-cong eqᵗ eqˢ (id A) =
  cong id (rename-cong eqᵗ eqˢ A)
renameᶜ-cong eqᵗ eqˢ (p ︔ q) =
  cong₂ _︔_ (renameᶜ-cong eqᵗ eqˢ p) (renameᶜ-cong eqᵗ eqˢ q)
renameᶜ-cong eqᵗ eqˢ (A !) =
  cong _! (rename-cong eqᵗ eqˢ A)
renameᶜ-cong eqᵗ eqˢ (A ？) =
  cong _？ (rename-cong eqᵗ eqˢ A)
renameᶜ-cong eqᵗ eqˢ (unseal α A) =
  cong₂ unseal (eqˢ α) (rename-cong eqᵗ eqˢ A)
renameᶜ-cong eqᵗ eqˢ (seal A α) =
  cong₂ seal (rename-cong eqᵗ eqˢ A) (eqˢ α)
renameᶜ-cong eqᵗ eqˢ (p ↦ q) =
  cong₂ _↦_ (renameᶜ-cong eqᵗ eqˢ p) (renameᶜ-cong eqᵗ eqˢ q)
renameᶜ-cong eqᵗ eqˢ (`∀ p) =
  cong `∀ (renameᶜ-cong (extᵗ-cong eqᵗ) eqˢ p)
renameᶜ-cong eqᵗ eqˢ (gen p) =
  cong gen (renameᶜ-cong eqᵗ (extˢ-cong eqˢ) p)
renameᶜ-cong eqᵗ eqˢ (inst p) =
  cong inst (renameᶜ-cong eqᵗ (extˢ-cong eqˢ) p)

renameᵐ-cong :
  ∀ {ρ ρ′ : Renameᵗ} {σ σ′ : Renameˢ} →
  (∀ X → ρ X ≡ ρ′ X) →
  (∀ α → σ α ≡ σ′ α) →
  (M : Term) →
  renameᵐ ρ σ M ≡ renameᵐ ρ′ σ′ M
renameᵐ-cong eqᵗ eqˢ (` x) = refl
renameᵐ-cong eqᵗ eqˢ (ƛ M) =
  cong ƛ_ (renameᵐ-cong eqᵗ eqˢ M)
renameᵐ-cong eqᵗ eqˢ (L · M) =
  cong₂ _·_ (renameᵐ-cong eqᵗ eqˢ L) (renameᵐ-cong eqᵗ eqˢ M)
renameᵐ-cong eqᵗ eqˢ (Λ M) =
  cong Λ_ (renameᵐ-cong (extᵗ-cong eqᵗ) eqˢ M)
renameᵐ-cong eqᵗ eqˢ (L • α) =
  cong₂ _•_ (renameᵐ-cong eqᵗ eqˢ L) (eqˢ α)
renameᵐ-cong eqᵗ eqˢ (ν A N) =
  cong₂ ν (rename-cong eqᵗ eqˢ A)
    (renameᵐ-cong eqᵗ (extˢ-cong eqˢ) N)
renameᵐ-cong eqᵗ eqˢ ($ κ) = refl
renameᵐ-cong eqᵗ eqˢ (L ⊕[ op ] M) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (renameᵐ-cong eqᵗ eqˢ L)
    (renameᵐ-cong eqᵗ eqˢ M)
renameᵐ-cong eqᵗ eqˢ (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (renameᵐ-cong eqᵗ eqˢ M) (renameᶜ-cong eqᵗ eqˢ c)
renameᵐ-cong eqᵗ eqˢ blame = refl

renameᶜ-reflects-Inert :
  ∀ ρ σ {c} →
  Inert (renameᶜ ρ σ c) →
  Inert c
renameᶜ-reflects-Inert ρ σ {id A} ()
renameᶜ-reflects-Inert ρ σ {p ︔ q} ()
renameᶜ-reflects-Inert ρ σ {p ↦ q} (._ ↦ ._) = p ↦ q
renameᶜ-reflects-Inert ρ σ {`∀ c} (`∀ ._) = `∀ c
renameᶜ-reflects-Inert ρ σ {G !} (._ !) = G !
renameᶜ-reflects-Inert ρ σ {G ？} ()
renameᶜ-reflects-Inert ρ σ {seal A α} (seal ._ ._) = seal A α
renameᶜ-reflects-Inert ρ σ {unseal α A} ()
renameᶜ-reflects-Inert ρ σ {gen c} (gen ._) = gen c
renameᶜ-reflects-Inert ρ σ {inst c} ()

renameᵐ-reflects-Value :
  ∀ ρ σ {V} →
  Value (renameᵐ ρ σ V) →
  Value V
renameᵐ-reflects-Value ρ σ {` x} ()
renameᵐ-reflects-Value ρ σ {ƛ M} (ƛ ._) = ƛ M
renameᵐ-reflects-Value ρ σ {L · M} ()
renameᵐ-reflects-Value ρ σ {Λ V} (Λ vV) =
  Λ (renameᵐ-reflects-Value (extᵗ ρ) σ vV)
renameᵐ-reflects-Value ρ σ {L • α} ()
renameᵐ-reflects-Value ρ σ {ν A N} ()
renameᵐ-reflects-Value ρ σ {$ κ} ($ ._) = $ κ
renameᵐ-reflects-Value ρ σ {L ⊕[ op ] M} ()
renameᵐ-reflects-Value ρ σ {M ⟨ c ⟩} (vM ⟨ i ⟩) =
  renameᵐ-reflects-Value ρ σ vM ⟨ renameᶜ-reflects-Inert ρ σ i ⟩
renameᵐ-reflects-Value ρ σ {blame} ()

substˣᵐ-cong :
  ∀ {σ τ : Substˣ} →
  (∀ x → σ x ≡ τ x) →
  (M : Term) →
  substˣᵐ σ M ≡ substˣᵐ τ M
substˣᵐ-cong eq (` x) = eq x
substˣᵐ-cong eq (ƛ M) =
  cong ƛ_ (substˣᵐ-cong eq↑ M)
  where
    eq↑ : ∀ x → extˢˣ _ x ≡ extˢˣ _ x
    eq↑ zero = refl
    eq↑ (suc x) = cong (renameˣᵐ suc) (eq x)
substˣᵐ-cong eq (L · M) =
  cong₂ _·_ (substˣᵐ-cong eq L) (substˣᵐ-cong eq M)
substˣᵐ-cong eq (Λ M) =
  cong Λ_ (substˣᵐ-cong (λ x → cong ⇑ᵗᵐ (eq x)) M)
substˣᵐ-cong eq (L • α) = cong (_• α) (substˣᵐ-cong eq L)
substˣᵐ-cong eq (ν A N) =
  cong (ν A) (substˣᵐ-cong (λ x → cong ⇑ˢᵐ (eq x)) N)
substˣᵐ-cong eq ($ κ) = refl
substˣᵐ-cong eq (L ⊕[ op ] M) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (substˣᵐ-cong eq L)
    (substˣᵐ-cong eq M)
substˣᵐ-cong eq (M ⟨ c ⟩) = cong _⟨ c ⟩ (substˣᵐ-cong eq M)
substˣᵐ-cong eq blame = refl

substᵗᶜ-cong :
  ∀ {σ τ : Substᵗ} →
  (∀ X → σ X ≡ τ X) →
  (c : Coercion) →
  substᵗᶜ σ c ≡ substᵗᶜ τ c
substᵗᶜ-cong eq (id A) =
  cong id (subst-cong eq (λ α → refl) A)
substᵗᶜ-cong eq (p ︔ q) =
  cong₂ _︔_ (substᵗᶜ-cong eq p) (substᵗᶜ-cong eq q)
substᵗᶜ-cong eq (p ↦ q) =
  cong₂ _↦_ (substᵗᶜ-cong eq p) (substᵗᶜ-cong eq q)
substᵗᶜ-cong eq (`∀ p) =
  cong `∀ (substᵗᶜ-cong eq↑ p)
  where
    eq↑ : ∀ X → extSubstᵗ _ X ≡ extSubstᵗ _ X
    eq↑ zero = refl
    eq↑ (suc X) = cong ⇑ᵗ (eq X)
substᵗᶜ-cong eq (A !) =
  cong _! (subst-cong eq (λ α → refl) A)
substᵗᶜ-cong eq (A ？) =
  cong _？ (subst-cong eq (λ α → refl) A)
substᵗᶜ-cong eq (seal A α) =
  cong (λ A′ → seal A′ α) (subst-cong eq (λ β → refl) A)
substᵗᶜ-cong eq (unseal α A) =
  cong (unseal α) (subst-cong eq (λ β → refl) A)
substᵗᶜ-cong eq (gen p) =
  cong gen (substᵗᶜ-cong (λ X → cong ⇑ˢ (eq X)) p)
substᵗᶜ-cong eq (inst p) =
  cong inst (substᵗᶜ-cong (λ X → cong ⇑ˢ (eq X)) p)

substᵗᵐ-cong :
  ∀ {σ τ : Substᵗ} →
  (∀ X → σ X ≡ τ X) →
  (M : Term) →
  substᵗᵐ σ M ≡ substᵗᵐ τ M
substᵗᵐ-cong eq (` x) = refl
substᵗᵐ-cong eq (ƛ M) = cong ƛ_ (substᵗᵐ-cong eq M)
substᵗᵐ-cong eq (L · M) =
  cong₂ _·_ (substᵗᵐ-cong eq L) (substᵗᵐ-cong eq M)
substᵗᵐ-cong eq (Λ M) =
  cong Λ_ (substᵗᵐ-cong eq↑ M)
  where
    eq↑ : ∀ X → extSubstᵗ _ X ≡ extSubstᵗ _ X
    eq↑ zero = refl
    eq↑ (suc X) = cong ⇑ᵗ (eq X)
substᵗᵐ-cong eq (L • α) = cong (_• α) (substᵗᵐ-cong eq L)
substᵗᵐ-cong eq (ν A N) =
  cong₂ ν (subst-cong eq (λ α → refl) A)
    (substᵗᵐ-cong (λ X → cong ⇑ˢ (eq X)) N)
substᵗᵐ-cong eq ($ κ) = refl
substᵗᵐ-cong eq (L ⊕[ op ] M) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (substᵗᵐ-cong eq L)
    (substᵗᵐ-cong eq M)
substᵗᵐ-cong eq (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (substᵗᵐ-cong eq M) (substᵗᶜ-cong eq c)
substᵗᵐ-cong eq blame = refl

renameᶜ-compose :
  ∀ ρ ρ′ σ σ′ c →
  renameᶜ ρ′ σ′ (renameᶜ ρ σ c) ≡
  renameᶜ (λ X → ρ′ (ρ X)) (λ α → σ′ (σ α)) c
renameᶜ-compose ρ ρ′ σ σ′ (id A) =
  cong id (rename-compose ρ ρ′ σ σ′ A)
renameᶜ-compose ρ ρ′ σ σ′ (p ︔ q) =
  cong₂ _︔_ (renameᶜ-compose ρ ρ′ σ σ′ p)
             (renameᶜ-compose ρ ρ′ σ σ′ q)
renameᶜ-compose ρ ρ′ σ σ′ (p ↦ q) =
  cong₂ _↦_ (renameᶜ-compose ρ ρ′ σ σ′ p)
             (renameᶜ-compose ρ ρ′ σ σ′ q)
renameᶜ-compose ρ ρ′ σ σ′ (`∀ p) =
  cong `∀
    (trans
      (renameᶜ-compose (extᵗ ρ) (extᵗ ρ′) σ σ′ p)
      (renameᶜ-cong
        (λ { zero → refl ; (suc X) → refl})
        (λ α → refl)
        p))
renameᶜ-compose ρ ρ′ σ σ′ (A !) =
  cong _! (rename-compose ρ ρ′ σ σ′ A)
renameᶜ-compose ρ ρ′ σ σ′ (A ？) =
  cong _？ (rename-compose ρ ρ′ σ σ′ A)
renameᶜ-compose ρ ρ′ σ σ′ (seal A α) =
  cong₂ seal (rename-compose ρ ρ′ σ σ′ A) refl
renameᶜ-compose ρ ρ′ σ σ′ (unseal α A) =
  cong₂ unseal refl (rename-compose ρ ρ′ σ σ′ A)
renameᶜ-compose ρ ρ′ σ σ′ (gen p) =
  cong gen
    (trans
      (renameᶜ-compose ρ ρ′ (extˢ σ) (extˢ σ′) p)
      (renameᶜ-cong
        (λ X → refl)
        (λ { zero → refl ; (suc α) → refl})
        p))
renameᶜ-compose ρ ρ′ σ σ′ (inst p) =
  cong inst
    (trans
      (renameᶜ-compose ρ ρ′ (extˢ σ) (extˢ σ′) p)
      (renameᶜ-cong
        (λ X → refl)
        (λ { zero → refl ; (suc α) → refl})
        p))

renameᵐ-compose :
  ∀ ρ ρ′ σ σ′ M →
  renameᵐ ρ′ σ′ (renameᵐ ρ σ M) ≡
  renameᵐ (λ X → ρ′ (ρ X)) (λ α → σ′ (σ α)) M
renameᵐ-compose ρ ρ′ σ σ′ (` x) = refl
renameᵐ-compose ρ ρ′ σ σ′ (ƛ M) =
  cong ƛ_ (renameᵐ-compose ρ ρ′ σ σ′ M)
renameᵐ-compose ρ ρ′ σ σ′ (L · M) =
  cong₂ _·_ (renameᵐ-compose ρ ρ′ σ σ′ L)
             (renameᵐ-compose ρ ρ′ σ σ′ M)
renameᵐ-compose ρ ρ′ σ σ′ (Λ M) =
  cong Λ_
    (trans
      (renameᵐ-compose (extᵗ ρ) (extᵗ ρ′) σ σ′ M)
      (renameᵐ-cong
        (λ { zero → refl ; (suc X) → refl})
        (λ α → refl)
        M))
renameᵐ-compose ρ ρ′ σ σ′ (L • α) =
  cong₂ _•_ (renameᵐ-compose ρ ρ′ σ σ′ L) refl
renameᵐ-compose ρ ρ′ σ σ′ (ν A N) =
  cong₂ ν (rename-compose ρ ρ′ σ σ′ A)
    (trans
      (renameᵐ-compose ρ ρ′ (extˢ σ) (extˢ σ′) N)
      (renameᵐ-cong
        (λ X → refl)
        (λ { zero → refl ; (suc α) → refl})
        N))
renameᵐ-compose ρ ρ′ σ σ′ ($ κ) = refl
renameᵐ-compose ρ ρ′ σ σ′ (L ⊕[ op ] M) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (renameᵐ-compose ρ ρ′ σ σ′ L)
    (renameᵐ-compose ρ ρ′ σ σ′ M)
renameᵐ-compose ρ ρ′ σ σ′ (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (renameᵐ-compose ρ ρ′ σ σ′ M)
    (renameᶜ-compose ρ ρ′ σ σ′ c)
renameᵐ-compose ρ ρ′ σ σ′ blame = refl

renameᵐ-shiftᵗ-comm :
  ∀ ρ σ M →
  ⇑ᵗᵐ (renameᵐ ρ σ M) ≡ renameᵐ (extᵗ ρ) σ (⇑ᵗᵐ M)
renameᵐ-shiftᵗ-comm ρ σ M =
  trans
    (renameᵐ-compose ρ suc σ idˢ M)
    (trans
      (renameᵐ-cong (λ X → refl) (λ α → refl) M)
      (sym (renameᵐ-compose suc (extᵗ ρ) idˢ σ M)))

renameᵐ-shiftˢ-commᵍ :
  ∀ ρ σ M →
  ⇑ˢᵐ (renameᵐ ρ σ M) ≡ renameᵐ ρ (extˢ σ) (⇑ˢᵐ M)
renameᵐ-shiftˢ-commᵍ ρ σ M =
  trans
    (renameᵐ-compose ρ idᵗ σ suc M)
    (trans
      (renameᵐ-cong (λ X → refl) (λ α → refl) M)
      (sym (renameᵐ-compose idᵗ ρ suc (extˢ σ) M)))

renameᵐ-shiftˢ-comm :
  ∀ σ M →
  ⇑ˢᵐ (renameᵐ idᵗ σ M) ≡ renameᵐ idᵗ (extˢ σ) (⇑ˢᵐ M)
renameᵐ-shiftˢ-comm = renameᵐ-shiftˢ-commᵍ idᵗ

renameᶜ-shiftˢ-commᵍ :
  ∀ ρ σ c →
  ⇑ˢᶜ (renameᶜ ρ σ c) ≡ renameᶜ ρ (extˢ σ) (⇑ˢᶜ c)
renameᶜ-shiftˢ-commᵍ ρ σ c =
  trans
    (renameᶜ-compose ρ idᵗ σ suc c)
    (trans
      (renameᶜ-cong (λ X → refl) (λ α → refl) c)
      (sym (renameᶜ-compose idᵗ ρ suc (extˢ σ) c)))

renameᶜ-shiftˢ-comm :
  ∀ σ c →
  ⇑ˢᶜ (renameᶜ idᵗ σ c) ≡ renameᶜ idᵗ (extˢ σ) (⇑ˢᶜ c)
renameᶜ-shiftˢ-comm = renameᶜ-shiftˢ-commᵍ idᵗ

renameᵐ-renameˣᵐ :
  ∀ ρ σ τ M →
  renameᵐ ρ σ (renameˣᵐ τ M) ≡ renameˣᵐ τ (renameᵐ ρ σ M)
renameᵐ-renameˣᵐ ρ σ τ (` x) = refl
renameᵐ-renameˣᵐ ρ σ τ (ƛ M) =
  cong ƛ_ (renameᵐ-renameˣᵐ ρ σ (extʳ τ) M)
renameᵐ-renameˣᵐ ρ σ τ (L · M) =
  cong₂ _·_ (renameᵐ-renameˣᵐ ρ σ τ L)
             (renameᵐ-renameˣᵐ ρ σ τ M)
renameᵐ-renameˣᵐ ρ σ τ (Λ M) =
  cong Λ_ (renameᵐ-renameˣᵐ (extᵗ ρ) σ τ M)
renameᵐ-renameˣᵐ ρ σ τ (L • α) =
  cong (_• σ α) (renameᵐ-renameˣᵐ ρ σ τ L)
renameᵐ-renameˣᵐ ρ σ τ (ν A N) =
  cong (ν (rename ρ σ A)) (renameᵐ-renameˣᵐ ρ (extˢ σ) τ N)
renameᵐ-renameˣᵐ ρ σ τ ($ κ) = refl
renameᵐ-renameˣᵐ ρ σ τ (L ⊕[ op ] M) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (renameᵐ-renameˣᵐ ρ σ τ L)
    (renameᵐ-renameˣᵐ ρ σ τ M)
renameᵐ-renameˣᵐ ρ σ τ (M ⟨ c ⟩) =
  cong _⟨ renameᶜ ρ σ c ⟩ (renameᵐ-renameˣᵐ ρ σ τ M)
renameᵐ-renameˣᵐ ρ σ τ blame = refl

renameᵐ-substˣᵐ :
  ∀ ρ σ τ M →
  substˣᵐ (λ x → renameᵐ ρ σ (τ x)) (renameᵐ ρ σ M) ≡
  renameᵐ ρ σ (substˣᵐ τ M)
renameᵐ-substˣᵐ ρ σ τ (` x) = refl
renameᵐ-substˣᵐ ρ σ τ (ƛ M) =
  cong ƛ_
    (trans
      (substˣᵐ-cong env-eq (renameᵐ ρ σ M))
      (renameᵐ-substˣᵐ ρ σ (extˢˣ τ) M))
  where
    env-eq : ∀ x →
      extˢˣ (λ y → renameᵐ ρ σ (τ y)) x ≡
      renameᵐ ρ σ (extˢˣ τ x)
    env-eq zero = refl
    env-eq (suc x) = sym (renameᵐ-renameˣᵐ ρ σ suc (τ x))
renameᵐ-substˣᵐ ρ σ τ (L · M) =
  cong₂ _·_ (renameᵐ-substˣᵐ ρ σ τ L)
             (renameᵐ-substˣᵐ ρ σ τ M)
renameᵐ-substˣᵐ ρ σ τ (Λ M) =
  cong Λ_
    (trans
      (substˣᵐ-cong env-eq (renameᵐ (extᵗ ρ) σ M))
      (renameᵐ-substˣᵐ (extᵗ ρ) σ (↑ᵗᵐ τ) M))
  where
    env-eq : ∀ x →
      ↑ᵗᵐ (λ y → renameᵐ ρ σ (τ y)) x ≡
      renameᵐ (extᵗ ρ) σ (↑ᵗᵐ τ x)
    env-eq x = renameᵐ-shiftᵗ-comm ρ σ (τ x)
renameᵐ-substˣᵐ ρ σ τ (L • α) =
  cong (_• σ α) (renameᵐ-substˣᵐ ρ σ τ L)
renameᵐ-substˣᵐ ρ σ τ (ν A N) =
  cong (ν (rename ρ σ A))
    (trans
      (substˣᵐ-cong env-eq (renameᵐ ρ (extˢ σ) N))
      (renameᵐ-substˣᵐ ρ (extˢ σ) (↑ˢᵐ τ) N))
  where
    env-eq : ∀ x →
      ↑ˢᵐ (λ y → renameᵐ ρ σ (τ y)) x ≡
      renameᵐ ρ (extˢ σ) (↑ˢᵐ τ x)
    env-eq x = renameᵐ-shiftˢ-commᵍ ρ σ (τ x)
renameᵐ-substˣᵐ ρ σ τ ($ κ) = refl
renameᵐ-substˣᵐ ρ σ τ (L ⊕[ op ] M) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (renameᵐ-substˣᵐ ρ σ τ L)
    (renameᵐ-substˣᵐ ρ σ τ M)
renameᵐ-substˣᵐ ρ σ τ (M ⟨ c ⟩) =
  cong _⟨ renameᶜ ρ σ c ⟩ (renameᵐ-substˣᵐ ρ σ τ M)
renameᵐ-substˣᵐ ρ σ τ blame = refl

IdLikeᵗ : Renameᵗ → Set
IdLikeᵗ ρ = ∀ X → ρ X ≡ X

idᵗ-like : IdLikeᵗ idᵗ
idᵗ-like X = refl

extᵗ-idlike :
  ∀ {ρ} →
  IdLikeᵗ ρ →
  IdLikeᵗ (extᵗ ρ)
extᵗ-idlike ρ-id zero = refl
extᵗ-idlike ρ-id (suc X) = cong suc (ρ-id X)

rename-substᵗ :
  ∀ ρ →
  IdLikeᵗ ρ →
  ∀ σ τ A →
  substᵗ (λ X → rename ρ σ (τ X)) (rename ρ σ A) ≡
  rename ρ σ (substᵗ τ A)
rename-substᵗ ρ ρ-id σ τ (`X X) =
  cong (λ Y → rename ρ σ (τ Y)) (ρ-id X)
rename-substᵗ ρ ρ-id σ τ (`α α) = refl
rename-substᵗ ρ ρ-id σ τ (‵ ι) = refl
rename-substᵗ ρ ρ-id σ τ ★ = refl
rename-substᵗ ρ ρ-id σ τ (A ⇒ B) =
  cong₂ _⇒_ (rename-substᵗ ρ ρ-id σ τ A)
             (rename-substᵗ ρ ρ-id σ τ B)
rename-substᵗ ρ ρ-id σ τ (`∀ A) =
  cong `∀
    (trans
      (subst-cong env-eq (λ α → refl) (rename (extᵗ ρ) σ A))
      (rename-substᵗ (extᵗ ρ) (extᵗ-idlike ρ-id)
        σ (extSubstᵗ τ) A))
  where
    env-eq : ∀ X →
      extSubstᵗ (λ Y → rename ρ σ (τ Y)) X ≡
      rename (extᵗ ρ) σ (extSubstᵗ τ X)
    env-eq zero = refl
    env-eq (suc X) = rename-shiftᵗ-comm ρ σ (τ X)

renameᶜ-substᵗᶜ :
  ∀ ρ →
  IdLikeᵗ ρ →
  ∀ σ τ c →
  substᵗᶜ (λ X → rename ρ σ (τ X)) (renameᶜ ρ σ c) ≡
  renameᶜ ρ σ (substᵗᶜ τ c)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (id A) =
  cong id (rename-substᵗ ρ ρ-id σ τ A)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (p ︔ q) =
  cong₂ _︔_ (renameᶜ-substᵗᶜ ρ ρ-id σ τ p)
             (renameᶜ-substᵗᶜ ρ ρ-id σ τ q)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (p ↦ q) =
  cong₂ _↦_ (renameᶜ-substᵗᶜ ρ ρ-id σ τ p)
             (renameᶜ-substᵗᶜ ρ ρ-id σ τ q)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (`∀ p) =
  cong `∀
    (trans
      (substᵗᶜ-cong env-eq (renameᶜ (extᵗ ρ) σ p))
      (renameᶜ-substᵗᶜ (extᵗ ρ) (extᵗ-idlike ρ-id)
        σ (extSubstᵗ τ) p))
  where
    env-eq : ∀ X →
      extSubstᵗ (λ Y → rename ρ σ (τ Y)) X ≡
      rename (extᵗ ρ) σ (extSubstᵗ τ X)
    env-eq zero = refl
    env-eq (suc X) = rename-shiftᵗ-comm ρ σ (τ X)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (A !) =
  cong _! (rename-substᵗ ρ ρ-id σ τ A)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (A ？) =
  cong _？ (rename-substᵗ ρ ρ-id σ τ A)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (seal A α) =
  cong (λ A′ → seal A′ (σ α)) (rename-substᵗ ρ ρ-id σ τ A)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (unseal α A) =
  cong (unseal (σ α)) (rename-substᵗ ρ ρ-id σ τ A)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (gen p) =
  cong gen
    (trans
      (substᵗᶜ-cong env-eq (renameᶜ ρ (extˢ σ) p))
      (renameᶜ-substᵗᶜ ρ ρ-id (extˢ σ) (liftSubstᵗOverSeal τ) p))
  where
    env-eq : ∀ X →
      liftSubstᵗOverSeal (λ Y → rename ρ σ (τ Y)) X ≡
      rename ρ (extˢ σ) (liftSubstᵗOverSeal τ X)
    env-eq X = rename-shiftˢ-comm ρ σ (τ X)
renameᶜ-substᵗᶜ ρ ρ-id σ τ (inst p) =
  cong inst
    (trans
      (substᵗᶜ-cong env-eq (renameᶜ ρ (extˢ σ) p))
      (renameᶜ-substᵗᶜ ρ ρ-id (extˢ σ) (liftSubstᵗOverSeal τ) p))
  where
    env-eq : ∀ X →
      liftSubstᵗOverSeal (λ Y → rename ρ σ (τ Y)) X ≡
      rename ρ (extˢ σ) (liftSubstᵗOverSeal τ X)
    env-eq X = rename-shiftˢ-comm ρ σ (τ X)

renameᵐ-substᵗᵐ :
  ∀ ρ →
  IdLikeᵗ ρ →
  ∀ σ τ M →
  substᵗᵐ (λ X → rename ρ σ (τ X)) (renameᵐ ρ σ M) ≡
  renameᵐ ρ σ (substᵗᵐ τ M)
renameᵐ-substᵗᵐ ρ ρ-id σ τ (` x) = refl
renameᵐ-substᵗᵐ ρ ρ-id σ τ (ƛ M) =
  cong ƛ_ (renameᵐ-substᵗᵐ ρ ρ-id σ τ M)
renameᵐ-substᵗᵐ ρ ρ-id σ τ (L · M) =
  cong₂ _·_ (renameᵐ-substᵗᵐ ρ ρ-id σ τ L)
             (renameᵐ-substᵗᵐ ρ ρ-id σ τ M)
renameᵐ-substᵗᵐ ρ ρ-id σ τ (Λ M) =
  cong Λ_
    (trans
      (substᵗᵐ-cong env-eq (renameᵐ (extᵗ ρ) σ M))
      (renameᵐ-substᵗᵐ (extᵗ ρ) (extᵗ-idlike ρ-id)
        σ (extSubstᵗ τ) M))
  where
    env-eq : ∀ X →
      extSubstᵗ (λ Y → rename ρ σ (τ Y)) X ≡
      rename (extᵗ ρ) σ (extSubstᵗ τ X)
    env-eq zero = refl
    env-eq (suc X) = rename-shiftᵗ-comm ρ σ (τ X)
renameᵐ-substᵗᵐ ρ ρ-id σ τ (L • α) =
  cong (_• σ α) (renameᵐ-substᵗᵐ ρ ρ-id σ τ L)
renameᵐ-substᵗᵐ ρ ρ-id σ τ (ν A N) =
  cong₂ ν (rename-substᵗ ρ ρ-id σ τ A)
    (trans
      (substᵗᵐ-cong env-eq (renameᵐ ρ (extˢ σ) N))
      (renameᵐ-substᵗᵐ ρ ρ-id (extˢ σ) (liftSubstᵗOverSeal τ) N))
  where
    env-eq : ∀ X →
      liftSubstᵗOverSeal (λ Y → rename ρ σ (τ Y)) X ≡
      rename ρ (extˢ σ) (liftSubstᵗOverSeal τ X)
    env-eq X = rename-shiftˢ-comm ρ σ (τ X)
renameᵐ-substᵗᵐ ρ ρ-id σ τ ($ κ) = refl
renameᵐ-substᵗᵐ ρ ρ-id σ τ (L ⊕[ op ] M) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (renameᵐ-substᵗᵐ ρ ρ-id σ τ L)
    (renameᵐ-substᵗᵐ ρ ρ-id σ τ M)
renameᵐ-substᵗᵐ ρ ρ-id σ τ (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (renameᵐ-substᵗᵐ ρ ρ-id σ τ M)
    (renameᶜ-substᵗᶜ ρ ρ-id σ τ c)
renameᵐ-substᵗᵐ ρ ρ-id σ τ blame = refl

renameᵐ-substˣ-single :
  ∀ σ N V →
  substˣᵐ (singleEnv (renameᵐ idᵗ σ V)) (renameᵐ idᵗ σ N) ≡
  renameᵐ idᵗ σ (substˣᵐ (singleEnv V) N)
renameᵐ-substˣ-single σ N V =
  trans
    (substˣᵐ-cong env-eq (renameᵐ idᵗ σ N))
    (renameᵐ-substˣᵐ idᵗ σ (singleEnv V) N)
  where
    env-eq : ∀ x →
      singleEnv (renameᵐ idᵗ σ V) x ≡
      renameᵐ idᵗ σ (singleEnv V x)
    env-eq zero = refl
    env-eq (suc x) = refl

renameᵐ-openᵀ-seal :
  ∀ σ V α →
  substᵗᵐ (singleTyEnv (`α (σ α))) (renameᵐ (extᵗ idᵗ) σ V) ≡
  renameᵐ idᵗ σ (substᵗᵐ (singleTyEnv (`α α)) V)
renameᵐ-openᵀ-seal σ V α =
  trans
    (substᵗᵐ-cong env-eq (renameᵐ (extᵗ idᵗ) σ V))
    (trans
      (renameᵐ-substᵗᵐ (extᵗ idᵗ) (extᵗ-idlike idᵗ-like)
        σ (singleTyEnv (`α α)) V)
      (renameᵐ-cong
        (extᵗ-idlike idᵗ-like)
        (λ β → refl)
        (substᵗᵐ (singleTyEnv (`α α)) V)))
  where
    env-eq : ∀ X →
      singleTyEnv (`α (σ α)) X ≡
      rename (extᵗ idᵗ) σ (singleTyEnv (`α α) X)
    env-eq zero = refl
    env-eq (suc X) = cong `X_ (sym (extᵗ-idlike idᵗ-like X))

renameᶜ-open∀-seal :
  ∀ σ c α →
  (renameᶜ (extᵗ idᵗ) σ c) [ σ α ]ᵀᶜ ≡
  renameᶜ idᵗ σ (c [ α ]ᵀᶜ)
renameᶜ-open∀-seal σ c α =
  trans
    (substᵗᶜ-cong env-eq (renameᶜ (extᵗ idᵗ) σ c))
    (trans
      (renameᶜ-substᵗᶜ (extᵗ idᵗ) (extᵗ-idlike idᵗ-like)
        σ (singleTyEnv (`α α)) c)
      (renameᶜ-cong
        (extᵗ-idlike idᵗ-like)
        (λ β → refl)
        (substᵗᶜ (singleTyEnv (`α α)) c)))
  where
    env-eq : ∀ X →
      singleTyEnv (`α (σ α)) X ≡
      rename (extᵗ idᵗ) σ (singleTyEnv (`α α) X)
    env-eq zero = refl
    env-eq (suc X) = cong `X_ (sym (extᵗ-idlike idᵗ-like X))

renameᶜ-openν-seal :
  ∀ σ c α →
  (renameᶜ idᵗ (extˢ σ) c) [ σ α ]ᶜ ≡
  renameᶜ idᵗ σ (c [ α ]ᶜ)
renameᶜ-openν-seal σ c α =
  trans
    (renameᶜ-compose idᵗ idᵗ (extˢ σ) (singleRenameˢ (σ α)) c)
    (trans
      (renameᶜ-cong
        (λ X → refl)
        (λ { zero → refl ; (suc b) → refl})
        c)
      (sym (renameᶜ-compose idᵗ idᵗ (singleRenameˢ α) σ c)))

------------------------------------------------------------------------
-- Telescope lookup uniqueness
------------------------------------------------------------------------

seal-lookup-unique :
  ∀ {Γ α A B} →
  Γ ∋α α ⦂ A →
  Γ ∋α α ⦂ B →
  A ≡ B
seal-lookup-unique Zα Zα = refl
seal-lookup-unique (Sα-ty hA) (Sα-ty hB) =
  cong ⇑ᵗ (seal-lookup-unique hA hB)
seal-lookup-unique (Sα-seal hA) (Sα-seal hB) =
  cong ⇑ˢ (seal-lookup-unique hA hB)
seal-lookup-unique (Sα-term hA) (Sα-term hB) =
  seal-lookup-unique hA hB

------------------------------------------------------------------------
-- Telescope-step weakening
------------------------------------------------------------------------

weakenTy :
  ∀ {Γ Γ′} →
  StepExt Γ Γ′ →
  Ty →
  Ty
weakenTy ext-refl A = A
weakenTy ext-seal A = ⇑ˢ A

stepExt-unique :
  ∀ {Γ Γ′} →
  (ext ext′ : StepExt Γ Γ′) →
  ext ≡ ext′
stepExt-unique ext-refl ext-refl = refl
stepExt-unique ext-seal ext-seal = refl

typing-stepExt-cong :
  ∀ {Γ Γ′ M A} {ext ext′ : StepExt Γ Γ′} →
  ext ≡ ext′ →
  Γ′ ⊢ M ⦂ weakenTy ext A →
  Γ′ ⊢ M ⦂ weakenTy ext′ A
typing-stepExt-cong refl M⊢ = M⊢

postulate
  typing-insert-seal :
    ∀ {Γ⁻ Γ⁺ α M A} →
    (i : SealInsert Γ⁻ Γ⁺ α) →
    Γ⁻ ⊢ M ⦂ A →
    Γ⁺ ⊢ renameᵐ idᵗ (insertRenˢ i) M
      ⦂ rename idᵗ (insertRenˢ i) A

typing-weaken-seal :
  ∀ {Γ M A B} →
  Γ ⊢ M ⦂ A →
  sealᵉ B ∷ Γ ⊢ ⇑ˢᵐ M ⦂ ⇑ˢ A
typing-weaken-seal M⊢ = typing-insert-seal here M⊢

typing-weaken-step :
  ∀ {Γ Γ′ M A} →
  (ext : StepExt Γ Γ′) →
  Γ ⊢ M ⦂ A →
  Γ′ ⊢ weakenTerm ext M ⦂ weakenTy ext A
typing-weaken-step ext-refl M⊢ = M⊢
typing-weaken-step ext-seal M⊢ = typing-weaken-seal M⊢

postulate
  coercion-weaken-step :
    ∀ {Γ Γ′ c A B μ} →
    (ext : StepExt Γ Γ′) →
    μ ∣ Γ ⊢ c ∶ A =⇒ B →
    ∃ λ μ′ →
      μ′ ∣ Γ′ ⊢ weakenCoercion ext c ∶ weakenTy ext A =⇒ weakenTy ext B

------------------------------------------------------------------------
-- Typing derivations produce well-formed result types
------------------------------------------------------------------------

constTy-wf :
  ∀ {Γ} κ →
  WfTy Γ (constTy κ)
constTy-wf (κℕ n) = wfBase

postulate
  typing-wf :
    ∀ {Γ M A} →
    Γ ⊢ M ⦂ A →
    WfTy Γ A

------------------------------------------------------------------------
-- Term-variable substitution
------------------------------------------------------------------------

postulate
  typing-single-subst :
    ∀ {Γ N V A B} →
    termᵉ A ∷ Γ ⊢ N ⦂ B →
    Γ ⊢ V ⦂ A →
    Γ ⊢ N [ V ] ⦂ B
