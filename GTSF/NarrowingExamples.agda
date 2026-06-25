{-
  Term-narrowing examples for the Nu syntax.

  This file mechanizes the `⊒` examples from cambridge23.lagda.md that are
  expressible with the current TermNarrowing rules.  The examples focus on
  the K/id-style polymorphic narrowing derivations around `⊒Λ`; casted
  continuations are added as the coercion-equivalence side conditions mature.
-}

module NarrowingExamples where

open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; cong; cong₂)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (z<s)
open import Data.Product using (_,_)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import TermNarrowing
open import proof.TermNarrowingProperties

------------------------------------------------------------------------
-- Shared syntax from cambridge23 Examples 1 and 6
------------------------------------------------------------------------

c★ : Term
c★ = $ (κℕ 0) ⟨ id (‵ `ℕ) ︔ ((‵ `ℕ) !) ⟩

------------------------------------------------------------------------
-- Example 1
------------------------------------------------------------------------

-- cambridge23 line 266 / line 406.
ex1-⊒Λ :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0) ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex1-⊒Λ = ⊒Λ (ƛ⊒ƛ (x⊒x Z))

-- cambridge23 line 272 side condition (i), at the raw-composition level.
ex1-line272-⨟ :
  gen (★ ⇒ ★)
    ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
    ⨟ `∀ (id (＇ 0) ↦ id (＇ 0))
    ≡ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex1-line272-⨟ =
  trans
    (⨟-gen-∀ (★ ⇒ ★)
      ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
      (id (＇ 0) ↦ id (＇ 0)))
    (cong (gen (★ ⇒ ★))
      (trans
        (⨟-↦ (id (＇ 0) ︔ ((＇ 0) !))
          (((＇ 0) ？) ︔ id (＇ 0)) (id (＇ 0)) (id (＇ 0)))
        (cong₂ _↦_
          (trans (⨟-tagʳ (id (＇ 0)) (id (＇ 0)) (＇ 0)) refl)
          refl)))

ex1-line272-≈ :
  0 ∣ [] ⊢
    gen (★ ⇒ ★)
      ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
      ≈ gen (★ ⇒ ★)
          ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
          ⨟ `∀ (id (＇ 0) ↦ id (＇ 0))
      ∶ (★ ⇒ ★) ⊒ `∀ (＇ 0 ⇒ ＇ 0)
ex1-line272-≈ rewrite ex1-line272-⨟ =
  ν≈νⁿ (wf⇒ wf★ wf★)
    (↦≈↦ⁿ
      (!≈! {G = ＇ 0} (wfVar z<s) (＇ 0)
        (id≈id {A = ＇ 0} {aA = ＇ 0} (wfVar z<s)))
      (?≈?ⁿ {G = ＇ 0} (wfVar z<s) (＇ 0)
        (id≈idⁿ {A = ＇ 0} {aA = ＇ 0} (wfVar z<s))))

ex1-cast- :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ gen (★ ⇒ ★)
          ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))) ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ `∀ (id (＇ 0) ↦ id (＇ 0))
ex1-cast- = cast-⊒ (≈ᵗ-oldⁿ ex1-line272-≈) ex1-⊒Λ

ex1-initial :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ gen (★ ⇒ ★)
          ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))) ⟩
        ⟨ inst (★ ⇒ ★)
          ((seal ★ 0 ︔ id (＇ 0)) ↦ (id (＇ 0) ︔ unseal 0 ★)) ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex1-initial =
  cast+⊒
    {p = `∀ (id (＇ 0) ↦ id (＇ 0))}
    {r = gen (★ ⇒ ★)
      ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))}
    {t = gen (★ ⇒ ★)
      ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))}
    (≈ᵗ-oldⁿ ex1-line272-≈) ex1-cast-

-- cambridge23 line 293 side condition (iii), at the raw-composition level.
ex1-line293-⨟ :
  ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
    ⨟ (id (＇ 0) ↦ id (＇ 0))
    ≡ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex1-line293-⨟ =
  trans
    (⨟-↦ (id (＇ 0) ︔ ((＇ 0) !)) (((＇ 0) ？) ︔ id (＇ 0))
      (id (＇ 0)) (id (＇ 0)))
    (cong₂ _↦_ (trans (⨟-tagʳ (id (＇ 0)) (id (＇ 0)) (＇ 0)) refl) refl)

ex1-line293-≈ :
  1 ∣ (0 ꞉ id ★) ∷ [] ⊢
    (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
      ≈ ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
          ⨟ (id (＇ 0) ↦ id (＇ 0))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex1-line293-≈ rewrite ex1-line293-⨟ =
  ↦≈↦ⁿ
    (!≈! {G = ＇ 0} (wfVar z<s) (＇ 0)
      (id≈id {A = ＇ 0} {aA = ＇ 0} (wfVar z<s)))
    (?≈?ⁿ {G = ＇ 0} (wfVar z<s) (＇ 0)
      (id≈idⁿ {A = ＇ 0} {aA = ＇ 0} (wfVar z<s)))

ex1-line294-⨟ :
  ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0))
    ⨟ (id (＇ 0) ↦ id (＇ 0))
    ≡ (unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)
ex1-line294-⨟ =
  trans
    (⨟-↦ (unseal 0 ★ ︔ id ★) (id ★ ︔ seal ★ 0)
      (id (＇ 0)) (id (＇ 0)))
    refl

ex1-line294-≈ :
  1 ∣ (0 ꞉ id ★) ∷ [] ⊢
    (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
      ≈ ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0))
          ⨟ (id (＇ 0) ↦ id (＇ 0))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex1-line294-≈ rewrite ex1-line294-⨟ =
  ↦≈↦ⁿ
    (!≈unseal★ (here refl))
    (?≈seal★ⁿ (here refl))

ex1-inner-⊒Λ-premise :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex1-inner-⊒Λ-premise = ƛ⊒ƛ (x⊒x Z)

ex1-inner-cast- :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
      ⊒ ƛ (` 0)
    ∶ id (＇ 0) ↦ id (＇ 0)
ex1-inner-cast- =
  cast-⊒ (≈ᵗ-oldⁿ ex1-line293-≈) ex1-inner-⊒Λ-premise

ex1-inner-cast+ :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
        ⟨ - ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)) ⟩
      ⊒ ƛ (` 0)
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex1-inner-cast+ =
  cast+⊒
    {p = id (＇ 0) ↦ id (＇ 0)}
    {r = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
    {t = (unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)}
    (≈ᵗ-oldⁿ ex1-line294-≈) ex1-inner-cast-

ex1-split :
  1 ∣ (0 ꞉= ★ ⊑) ∷ (⊑ 1 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ (id (＇ 1) ︔ ((＇ 1) !)) ↦ (((＇ 1) ？) ︔ id (＇ 1)) ⟩
        ⟨ - ((unseal 1 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 1)) ⟩
      ⊒ ƛ (` 0)
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex1-split =
  split
    {N =
      (ƛ (` 0))
        ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
        ⟨ - ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)) ⟩}
    {N′ = ƛ (` 0)}
    {p = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
    {q = id ★}
    {A = ★}
    {α = 0}
    {αᵢ = 1}
    {Σ = []}
    (id-onlyᵈ , (cast-id wf★ refl , id★))
    ex1-inner-cast+

-- cambridge23 line 291: this is after three reduction steps from
-- `ex1-initial`, not after the first reduction step.
ex1-after-reduction :
  0 ∣ (⊑ 0 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
        ⟨ - ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)) ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex1-after-reduction = ⊒Λ ex1-split

------------------------------------------------------------------------
-- Example 2
------------------------------------------------------------------------

ex2-id :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ id ★ ↦ id ★
ex2-id = ƛ⊒ƛ (x⊒x Z)

-- cambridge23 line 307, left-hand raw composition.
ex2-line307-left-⨟ :
  (id ★ ↦ id ★)
    ⨟ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
    ≡ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex2-line307-left-⨟ =
  trans
    (⨟-genʳ (id ★ ↦ id ★) (★ ⇒ ★)
      ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))))
    (cong (gen (★ ⇒ ★))
      (trans
        (⨟-↦ (id ★) (id ★) (id (＇ 0) ︔ ((＇ 0) !))
          (((＇ 0) ？) ︔ id (＇ 0)))
        (cong₂ _↦_ (⨟-idʳ (id (＇ 0) ︔ ((＇ 0) !)) {A = ★}) refl)))

ex2-line307-≈ :
  0 ∣ [] ⊢
    (id ★ ↦ id ★)
      ⨟ gen (★ ⇒ ★)
          ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
      ≈ gen (★ ⇒ ★)
          ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
          ⨟ `∀ (id (＇ 0) ↦ id (＇ 0))
      ∶ (★ ⇒ ★) ⊒ `∀ (＇ 0 ⇒ ＇ 0)
ex2-line307-≈ rewrite ex2-line307-left-⨟ | ex1-line272-⨟ =
  ν≈νⁿ (wf⇒ wf★ wf★)
    (↦≈↦ⁿ
      (!≈! {G = ＇ 0} (wfVar z<s) (＇ 0)
        (id≈id {A = ＇ 0} {aA = ＇ 0} (wfVar z<s)))
      (?≈?ⁿ {G = ＇ 0} (wfVar z<s) (＇ 0)
        (id≈idⁿ {A = ＇ 0} {aA = ＇ 0} (wfVar z<s))))

ex2-line303-right-≈ :
  0 ∣ [] ⊢
    (id ★ ↦ id ★)
      ⨟ gen (★ ⇒ ★)
          ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
      ≈ gen (★ ⇒ ★)
          ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
      ∶ (★ ⇒ ★) ⊒ `∀ (＇ 0 ⇒ ＇ 0)
ex2-line303-right-≈ rewrite ex2-line307-left-⨟ =
  ν≈νⁿ (wf⇒ wf★ wf★)
    (↦≈↦ⁿ
      (!≈! {G = ＇ 0} (wfVar z<s) (＇ 0)
        (id≈id {A = ＇ 0} {aA = ＇ 0} (wfVar z<s)))
      (?≈?ⁿ {G = ＇ 0} (wfVar z<s) (＇ 0)
        (id≈idⁿ {A = ＇ 0} {aA = ＇ 0} (wfVar z<s))))

ex2-right-cast :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ (ƛ (` 0))
          ⟨ gen (★ ⇒ ★)
            ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))) ⟩
    ∶ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex2-right-cast = ⊒cast- (≈ᵗ-oldⁿ ex2-line303-right-≈) ex2-id

ex2-line303 :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ gen (★ ⇒ ★)
          ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))) ⟩
      ⊒ (ƛ (` 0))
          ⟨ gen (★ ⇒ ★)
            ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))) ⟩
    ∶ `∀ (id (＇ 0) ↦ id (＇ 0))
ex2-line303 = cast-⊒ (≈ᵗ-oldⁿ ex1-line272-≈) ex2-right-cast

ex2-initial :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ gen (★ ⇒ ★)
          ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))) ⟩
        ⟨ inst (★ ⇒ ★)
          ((seal ★ 0 ︔ id (＇ 0)) ↦ (id (＇ 0) ︔ unseal 0 ★)) ⟩
      ⊒ (ƛ (` 0))
          ⟨ gen (★ ⇒ ★)
            ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))) ⟩
    ∶ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex2-initial =
  cast+⊒
    {p = `∀ (id (＇ 0) ↦ id (＇ 0))}
    {r = gen (★ ⇒ ★)
      ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))}
    {t = gen (★ ⇒ ★)
      ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))}
    (≈ᵗ-oldⁿ ex1-line272-≈) ex2-line303

ex2-inner-id :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ id ★ ↦ id ★
ex2-inner-id = ƛ⊒ƛ (x⊒x Z)

ex2-line316-left-⨟ :
  (id ★ ↦ id ★)
    ⨟ ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
    ≡ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex2-line316-left-⨟ =
  trans
    (⨟-↦ (id ★) (id ★) (id (＇ 0) ︔ ((＇ 0) !))
      (((＇ 0) ？) ︔ id (＇ 0)))
    (cong₂ _↦_ (⨟-idʳ (id (＇ 0) ︔ ((＇ 0) !)) {A = ★}) refl)

ex2-line316-right-≈ :
  1 ∣ (0 ꞉ id ★) ∷ [] ⊢
    (id ★ ↦ id ★)
      ⨟ ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
      ≈ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex2-line316-right-≈ rewrite ex2-line316-left-⨟ =
  ↦≈↦ⁿ
    (!≈! {G = ＇ 0} (wfVar z<s) (＇ 0)
      (id≈id {A = ＇ 0} {aA = ＇ 0} (wfVar z<s)))
    (?≈?ⁿ {G = ＇ 0} (wfVar z<s) (＇ 0)
      (id≈idⁿ {A = ＇ 0} {aA = ＇ 0} (wfVar z<s)))

ex2-inner-right-cast :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ (ƛ (` 0))
          ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex2-inner-right-cast =
  ⊒cast- (≈ᵗ-oldⁿ ex2-line316-right-≈) ex2-inner-id

ex2-line316 :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
      ⊒ (ƛ (` 0))
          ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
    ∶ id (＇ 0) ↦ id (＇ 0)
ex2-line316 = cast-⊒ (≈ᵗ-oldⁿ ex1-line293-≈) ex2-inner-right-cast

ex2-line318 :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
        ⟨ - ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)) ⟩
      ⊒ (ƛ (` 0))
          ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex2-line318 =
  cast+⊒
    {p = id (＇ 0) ↦ id (＇ 0)}
    {r = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
    {t = (unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)}
    (≈ᵗ-oldⁿ ex1-line294-≈) ex2-line316

ex2-split :
  1 ∣ (0 ꞉= ★ ⊑) ∷ (⊑ 1 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ (id (＇ 1) ︔ ((＇ 1) !)) ↦ (((＇ 1) ？) ︔ id (＇ 1)) ⟩
        ⟨ - ((unseal 1 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 1)) ⟩
      ⊒ (ƛ (` 0))
          ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex2-split =
  split
    {N =
      (ƛ (` 0))
        ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
        ⟨ - ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)) ⟩}
    {N′ =
      (ƛ (` 0))
        ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩}
    {p = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
    {q = id ★}
    {A = ★}
    {α = 0}
    {αᵢ = 1}
    {Σ = []}
    (id-onlyᵈ , (cast-id wf★ refl , id★))
    ex2-line318

-- cambridge23 line 320: as with Example 1, this is after the catch-up
-- reductions, not after the first reduction step.
ex2-after-reduction :
  0 ∣ (⊑ 0 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)) ⟩
        ⟨ - ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)) ⟩
      ⊒ (ƛ (` 0))
          ⟨ gen (★ ⇒ ★)
            ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))) ⟩
    ∶ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex2-after-reduction = ⊒⟨ν⟩ ex2-split

------------------------------------------------------------------------
-- Example 3
------------------------------------------------------------------------

ex3-line329 :
  0 ∣ (0 ꞉= ‵ `ℕ ⊑) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ (Λ (ƛ (` 0))) • 0
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex3-line329 =
  ⊒α {A = ‵ `ℕ} {α = 0}
    (⊒Λ
      {A = ‵ `ℕ}
      {N = ƛ (` 0)}
      {V′ = ƛ (` 0)}
      {p = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
      (ƛ⊒ƛ (x⊒x Z)))

ex3-line329-extend :
  0 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ (Λ (ƛ (` 0))) • 0
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex3-line329-extend =
  extend
    {M = ƛ (` 0)}
    {N′ = (Λ (ƛ (` 0))) • 0}
    {p = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
    {q = id (‵ `ℕ)}
    {A = ‵ `ℕ}
    {B = ‵ `ℕ}
    {α = 0}
    {Σ = []}
    (id-onlyᵈ , (cast-id wfBase refl , cross id-‵))
    ex3-line329

ex3-line331-⨟ :
  ((id (‵ `ℕ) ︔ ((‵ `ℕ) !)) ↦ (((‵ `ℕ) ？) ︔ id (‵ `ℕ)))
    ⨟ ((unseal 0 (‵ `ℕ) ︔ id (‵ `ℕ))
         ↦ (id (‵ `ℕ) ︔ seal (‵ `ℕ) 0))
    ≡ (((unseal 0 (‵ `ℕ) ︔ id (‵ `ℕ)) ︔ ((‵ `ℕ) !))
        ↦ ((((‵ `ℕ) ？) ︔ id (‵ `ℕ)) ︔ seal (‵ `ℕ) 0))
ex3-line331-⨟ =
  trans
    (⨟-↦ (id (‵ `ℕ) ︔ ((‵ `ℕ) !))
      (((‵ `ℕ) ？) ︔ id (‵ `ℕ))
      (unseal 0 (‵ `ℕ) ︔ id (‵ `ℕ))
      (id (‵ `ℕ) ︔ seal (‵ `ℕ) 0))
    (cong₂ _↦_
      (trans
        (⨟-tagʳ (unseal 0 (‵ `ℕ) ︔ id (‵ `ℕ))
          (id (‵ `ℕ)) (‵ `ℕ))
        refl)
      (trans
        (⨟-sealʳ (((‵ `ℕ) ？) ︔ id (‵ `ℕ))
          (id (‵ `ℕ)) (‵ `ℕ) 0)
        refl))

ex3-line331-≈ :
  0 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ⊢
    ((id (‵ `ℕ) ︔ ((‵ `ℕ) !)) ↦ (((‵ `ℕ) ？) ︔ id (‵ `ℕ)))
      ⨟ ((unseal 0 (‵ `ℕ) ︔ id (‵ `ℕ))
           ↦ (id (‵ `ℕ) ︔ seal (‵ `ℕ) 0))
      ≈ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex3-line331-≈ rewrite ex3-line331-⨟ =
  ↦≈↦ⁿ
    (unsealG≈! {G = ‵ `ℕ} {aG = ‵ `ℕ} wfBase (‵ `ℕ)
      (here refl))
    (sealG≈?ⁿ {G = ‵ `ℕ} {aG = ‵ `ℕ} wfBase (‵ `ℕ)
      (here refl))

ex3-line331 :
  0 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ ((Λ (ƛ (` 0))) • 0)
          ⟨ -
            ((unseal 0 (‵ `ℕ) ︔ id (‵ `ℕ))
              ↦ (id (‵ `ℕ) ︔ seal (‵ `ℕ) 0)) ⟩
    ∶ (id (‵ `ℕ) ︔ ((‵ `ℕ) !)) ↦ (((‵ `ℕ) ？) ︔ id (‵ `ℕ))
ex3-line331 =
  ⊒cast+
    {q = (id (‵ `ℕ) ︔ ((‵ `ℕ) !))
      ↦ (((‵ `ℕ) ？) ︔ id (‵ `ℕ))}
    {r = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
    {s =
      (unseal 0 (‵ `ℕ) ︔ id (‵ `ℕ))
        ↦ (id (‵ `ℕ) ︔ seal (‵ `ℕ) 0)}
    (≈ᵗ-oldⁿ ex3-line331-≈)
    ex3-line329-extend

------------------------------------------------------------------------
-- Example 4
------------------------------------------------------------------------

ex4-poly-id :
  0 ∣ [] ∣ []
    ⊢ Λ (ƛ (` 0)) ⊒ Λ (ƛ (` 0))
    ∶ `∀ (id (＇ 0) ↦ id (＇ 0))
ex4-poly-id = Λ⊒Λ (ƛ⊒ƛ (x⊒x Z))

ex4-initial :
  0 ∣ [] ∣ []
    ⊢ (Λ (ƛ (` 0)))
        ⟨ inst (★ ⇒ ★)
          ((seal ★ 0 ︔ id (＇ 0)) ↦ (id (＇ 0) ︔ unseal 0 ★)) ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex4-initial =
  cast+⊒
    {p = `∀ (id (＇ 0) ↦ id (＇ 0))}
    {r = gen (★ ⇒ ★)
      ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))}
    {t = gen (★ ⇒ ★)
      ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))}
    (≈ᵗ-oldⁿ ex1-line272-≈) ex4-poly-id

ex4-line352 :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ id (＇ 0) ↦ id (＇ 0)
ex4-line352 = ƛ⊒ƛ (x⊒x Z)

ex4-line353 :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ - ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)) ⟩
      ⊒ ƛ (` 0)
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex4-line353 =
  cast+⊒
    {p = id (＇ 0) ↦ id (＇ 0)}
    {r = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
    {t = (unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)}
    (≈ᵗ-oldⁿ ex1-line294-≈) ex4-line352

ex4-split :
  1 ∣ (0 ꞉= ★ ⊑) ∷ (⊑ 1 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ - ((unseal 1 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 1)) ⟩
      ⊒ ƛ (` 0)
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex4-split =
  split
    {N =
      (ƛ (` 0))
        ⟨ - ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)) ⟩}
    {N′ = ƛ (` 0)}
    {p = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
    {q = id ★}
    {A = ★}
    {α = 0}
    {αᵢ = 1}
    {Σ = []}
    (id-onlyᵈ , (cast-id wf★ refl , id★))
    ex4-line353

-- cambridge23 Example 4, final displayed derivation after the ν̅ reduction
-- exposes the fresh seal variable.
ex4-after-reduction :
  0 ∣ (⊑ 0 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ - ((unseal 0 ★ ︔ id ★) ↦ (id ★ ︔ seal ★ 0)) ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★)
        ((id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0)))
ex4-after-reduction = ⊒Λ ex4-split

------------------------------------------------------------------------
-- Example 5
------------------------------------------------------------------------

-- cambridge23 Example 5 uses a tagged value at one ground type as the
-- argument to a function expecting another ground type.  Here `c★` is tagged
-- at ℕ, so the function side below uses 𝔹 for the mismatching ground type.
ex5-line380-⨟ :
  (id ★ ↦ id ★)
    ⨟ ((id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹)))
    ≡ (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))
ex5-line380-⨟ =
  trans
    (⨟-↦ (id ★) (id ★)
      (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      (((‵ `𝔹) ？) ︔ id (‵ `𝔹)))
    (cong₂ _↦_
      (⨟-idʳ (id (‵ `𝔹) ︔ ((‵ `𝔹) !)) {A = ★})
      refl)

ex5-line380-≈ :
  0 ∣ [] ⊢
    (id ★ ↦ id ★)
      ⨟ ((id (‵ `𝔹) ︔ ((‵ `𝔹) !))
        ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹)))
      ≈ (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
        ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))
      ∶ (★ ⇒ ★) ⊒ (‵ `𝔹 ⇒ ‵ `𝔹)
ex5-line380-≈ rewrite ex5-line380-⨟ =
  ↦≈↦ⁿ
    (!≈! {G = ‵ `𝔹} wfBase (‵ `𝔹)
      (id≈id {A = ‵ `𝔹} {aA = ‵ `𝔹} wfBase))
    (?≈?ⁿ {G = ‵ `𝔹} wfBase (‵ `𝔹)
      (id≈idⁿ {A = ‵ `𝔹} {aA = ‵ `𝔹} wfBase))

ex5-function-base :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))
ex5-function-base = ƛ⊒ƛ (x⊒x Z)

-- cambridge23 Example 5, line 379, function-side premise.
ex5-function-cast :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ (ƛ (` 0))
          ⟨ -
            ((id (‵ `𝔹) ︔ ((‵ `𝔹) !))
              ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))) ⟩
    ∶ id ★ ↦ id ★
ex5-function-cast =
  ⊒cast+
    {q = id ★ ↦ id ★}
    {r = (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))}
    {s = (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))}
    {A = ★ ⇒ ★}
    {B = ‵ `𝔹 ⇒ ‵ `𝔹}
    (≈ᵗ-oldⁿ ex5-line380-≈) ex5-function-base

-- cambridge23 Example 5, argument-side premise, using the barred two-sided
-- cast rule with `ℕ!` as the dual of `ℕ?;idℕ`.
ex5-c★ :
  0 ∣ [] ∣ []
    ⊢ c★ ⊒ c★ ∶ id ★
ex5-c★ =
  cast+⊒cast+
    {p = id (‵ `ℕ)}
    {q = id ★}
    {r = ((‵ `ℕ) ？) ︔ id (‵ `ℕ)}
    {s = ((‵ `ℕ) ？) ︔ id (‵ `ℕ)}
    {t = ((‵ `ℕ) ？) ︔ id (‵ `ℕ)}
    (≈ᵗ-oldⁿ
      (?≈?ⁿ {G = ‵ `ℕ} wfBase (‵ `ℕ)
        (id≈idⁿ {A = ‵ `ℕ} {aA = ‵ `ℕ} wfBase)))
    (≈ᵗ-oldⁿ
      (?≈?ⁿ {G = ‵ `ℕ} wfBase (‵ `ℕ)
        (id≈idⁿ {A = ‵ `ℕ} {aA = ‵ `ℕ} wfBase)))
    (κ⊒κ (κℕ 0))

-- cambridge23 Example 5, initial displayed derivation.
ex5-initial :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0)) · c★
      ⊒ ((ƛ (` 0))
          ⟨ -
            ((id (‵ `𝔹) ︔ ((‵ `𝔹) !))
              ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))) ⟩)
        · c★
    ∶ id ★
ex5-initial = ·⊒· ex5-function-cast ex5-c★

-- cambridge23 Example 5, after the reductions to blame.
ex5-after-reduction :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0)) · c★ ⊒ blame ∶ id ★
ex5-after-reduction = ⊒blame

------------------------------------------------------------------------
-- Example 6
------------------------------------------------------------------------

-- cambridge23 Example 6, line 403.
ex6-open-ν𝔹 :
  1 ∣ (0 ꞉= ‵ `𝔹 ⊑) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ (Λ (ƛ (` 0))) • 0
    ∶ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
ex6-open-ν𝔹 =
  ⊒α {A = ‵ `𝔹} {α = 0}
    (⊒Λ
      {A = ‵ `𝔹}
      {N = ƛ (` 0)}
      {V′ = ƛ (` 0)}
      {p = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
      (ƛ⊒ƛ (x⊒x Z)))

ex6-line405-⨟ :
  ((id (‵ `𝔹) ︔ ((‵ `𝔹) !)) ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹)))
    ⨟ ((unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹))
         ↦ (id (‵ `𝔹) ︔ seal (‵ `𝔹) 0))
    ≡ (((unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹)) ︔ ((‵ `𝔹) !))
        ↦ ((((‵ `𝔹) ？) ︔ id (‵ `𝔹)) ︔ seal (‵ `𝔹) 0))
ex6-line405-⨟ =
  trans
    (⨟-↦ (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      (((‵ `𝔹) ？) ︔ id (‵ `𝔹))
      (unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹))
      (id (‵ `𝔹) ︔ seal (‵ `𝔹) 0))
    (cong₂ _↦_
      (trans
        (⨟-tagʳ (unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹))
          (id (‵ `𝔹)) (‵ `𝔹))
        refl)
      (trans
        (⨟-sealʳ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))
          (id (‵ `𝔹)) (‵ `𝔹) 0)
        refl))

-- cambridge23 Example 6, line 405 side condition (i), with the corrected
-- result `ι!→ι?`.  This uses the term-cast side-condition relation so the
-- seal/tag bridge can read identity-like evidence from the exact `α:=ι`
-- assumption without changing the sound coercion-equivalence relation.
ex6-line405-≈ :
  1 ∣ (0 ꞉= ‵ `𝔹 ⊑) ∷ [] ⊢
    ((id (‵ `𝔹) ︔ ((‵ `𝔹) !)) ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹)))
      ⨟ ((unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹))
           ↦ (id (‵ `𝔹) ︔ seal (‵ `𝔹) 0))
      ≈ᵗ (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex6-line405-≈ rewrite ex6-line405-⨟ =
  ↦≈↦ᵗⁿ
    (unsealG≈!ᵗ wfBase (‵ `𝔹) (≈id-exact (here refl)))
    (sealG≈?ᵗⁿ wfBase (‵ `𝔹) (≈id-exact (here refl)))

-- cambridge23 Example 6, line 405.
ex6-line405 :
  1 ∣ (0 ꞉= ‵ `𝔹 ⊑) ∷ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ ((Λ (ƛ (` 0))) • 0)
          ⟨ -
            ((unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹))
              ↦ (id (‵ `𝔹) ︔ seal (‵ `𝔹) 0)) ⟩
    ∶ (id (‵ `𝔹) ︔ ((‵ `𝔹) !)) ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))
ex6-line405 =
  ⊒cast+
    {q = (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))}
    {r = (id (＇ 0) ︔ ((＇ 0) !)) ↦ (((＇ 0) ？) ︔ id (＇ 0))}
    {s =
      (unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹))
        ↦ (id (‵ `𝔹) ︔ seal (‵ `𝔹) 0)}
    ex6-line405-≈
    ex6-open-ν𝔹

ex6-line407-ν :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ ν (‵ `𝔹)
          (((Λ (ƛ (` 0))) • 0)
            ⟨ -
              ((unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹))
                ↦ (id (‵ `𝔹) ︔ seal (‵ `𝔹) 0)) ⟩)
          (⇑ᶜ ((id (‵ `𝔹) ︔ ((‵ `𝔹) !))
            ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))))
    ∶ (id (‵ `𝔹) ︔ ((‵ `𝔹) !)) ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))
ex6-line407-ν = ⊒ν ex6-line405

-- cambridge23 Example 6, line 407 side condition (ii).
ex6-line407 :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ (ν (‵ `𝔹)
          (((Λ (ƛ (` 0))) • 0)
            ⟨ -
              ((unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹))
                ↦ (id (‵ `𝔹) ︔ seal (‵ `𝔹) 0)) ⟩)
          (⇑ᶜ ((id (‵ `𝔹) ︔ ((‵ `𝔹) !))
            ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹)))))
          ⟨ -
            ((id (‵ `𝔹) ︔ ((‵ `𝔹) !))
              ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))) ⟩
    ∶ id ★ ↦ id ★
ex6-line407 =
  ⊒cast+
    {q = id ★ ↦ id ★}
    {r = (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))}
    {s = (id (‵ `𝔹) ︔ ((‵ `𝔹) !))
      ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))}
    {A = ★ ⇒ ★}
    {B = ‵ `𝔹 ⇒ ‵ `𝔹}
    (≈ᵗ-oldⁿ ex5-line380-≈)
    ex6-line407-ν

ex6-initial :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0)) · c★
      ⊒ ((ν (‵ `𝔹)
          (((Λ (ƛ (` 0))) • 0)
            ⟨ -
              ((unseal 0 (‵ `𝔹) ︔ id (‵ `𝔹))
                ↦ (id (‵ `𝔹) ︔ seal (‵ `𝔹) 0)) ⟩)
          (⇑ᶜ ((id (‵ `𝔹) ︔ ((‵ `𝔹) !))
            ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹)))))
          ⟨ -
            ((id (‵ `𝔹) ︔ ((‵ `𝔹) !))
              ↦ (((‵ `𝔹) ？) ︔ id (‵ `𝔹))) ⟩)
        · c★
    ∶ id ★
ex6-initial = ·⊒· ex6-line407 ex5-c★

-- cambridge23 line 473.  This endpoint is independent of the casted
-- derivation above it because `⊒blame` relates any left term to blame.
ex6-blame :
  0 ∣ (0 ꞉= ‵ `ℕ ⊑) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) · c★ ⊒ blame ∶ id ★
ex6-blame = ⊒blame
