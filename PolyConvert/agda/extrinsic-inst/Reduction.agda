module Reduction where

-- File Charter:
--   * Raw, store-threaded one-step, and store-threaded multi-step reduction
--     for PolyConvert terms.
--   * Adapts the non-store-threaded PolyUpDown reduction rules to raw
--     imprecision and conversion evidence.

open import Data.List using (length; _∷_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import Imprecision
open import Conversion
open import Primitives
open import Terms public

--------------------------------------------------------------------------------
-- One-step reduction
--------------------------------------------------------------------------------

infix 2 _—→_
data _—→_ : Term → Term → Set where

  β : ∀ {B : Ty} {N V : Term} →
    Value V →
    ----------------------------
    ((ƛ B ⇒ N) · V) —→ (N [ V ])

  β-up-∀ : ∀ {B A V p} →
    Value V →
    --------------------------------------------------------------------
    (V ⇑ (‵∀ p)) ⦂∀ B [ A ]  —→  (V ⦂∀ (src⊑ p) [ A ]) ⇑ (p [ A ]⊑)

  β-up-↦ : ∀ {V W p q} →
    Value V → Value W →
    --------------------------------------------------
    (V ⇑ (p ↦ q)) · W  —→  (V · (W ⇓ p)) ⇑ q

  β-down-↦ : ∀ {V W p q} →
    Value V → Value W →
    --------------------------------------------------
    (V ⇓ (p ↦ q)) · W  —→  (V · (W ⇑ p)) ⇓ q

  β-reveal-↦ : ∀ {V W p q} →
    Value V → Value W →
    --------------------------------------------
    (V ↑ (↑-⇒ p q)) · W  —→  (V · (W ↓ p)) ↑ q

  β-conceal-↦ : ∀ {V W p q} →
    Value V → Value W →
    --------------------------------------------
    (V ↓ (↓-⇒ p q)) · W  —→  (V · (W ↑ p)) ↓ q

  id-up-★ : ∀ {V} →
    Value V →
    ----------------
    V ⇑ id★  —→  V

  id-up-＇ : ∀ {X V} →
    Value V →
    --------------------
    V ⇑ (idₓ X)  —→  V

  id-up-｀ : ∀ {α V} →
    Value V →
    --------------------
    V ⇑ (idₛ α)  —→  V

  id-up-‵ : ∀ {ι V} →
    Value V →
    --------------------
    V ⇑ (idι ι)  —→  V

  id-down-★ : ∀ {V} →
    Value V →
    ----------------
    V ⇓ id★  —→  V

  id-down-＇ : ∀ {X V} →
    Value V →
    --------------------
    V ⇓ (idₓ X ) —→  V

  id-down-｀ : ∀ {α V} →
    Value V →
    --------------------
    V ⇓ (idₛ α)  —→  V

  id-down-‵ : ∀ {ι V} →
    Value V →
    --------------------
    V ⇓ (idι ι)  —→  V

  id-reveal : ∀ {A V} →
    Value V →
    -------------------
    V ↑ (↑-id A)  —→  V

  id-conceal : ∀ {A V} →
    Value V →
    -------------------    
    V ↓ (↓-id A)  —→  V

  seal-unseal : ∀ {α V} →
    Value V →
    --------------------------------------
    (V ↓ (↓-seal α)) ↑ (↑-unseal α)  —→  V

  tag-untag-ok : ∀ {V p q} →
    Value V → tgt⊑ p ≡ tgt⊑ q →
    --------------------------------------------
    (V ⇑ (p !)) ⇓ (q !)  —→  (V ⇑ p) ⇓ q

  tag-untag-bad : ∀ {V p q} {ℓ : Label} →
    Value V → tgt⊑ p ≢ tgt⊑ q →
    ----------------------------------------
    (V ⇑ (p !)) ⇓ (q !)  —→  blame ℓ

  δ-⊕ : ∀ {m n : ℕ} →
    -----------------------------------------------
    $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)  —→  $ (κℕ (m + n))

  blame-·₁ : ∀ {ℓ : Label} {M : Term} →
    (blame ℓ · M) —→ blame ℓ

  blame-·₂ : ∀ {ℓ : Label} {V : Term} →
    Value V →
    (V · blame ℓ) —→ blame ℓ

  blame-·α : ∀ {ℓ : Label} {B T : Ty} →
    (blame ℓ ⦂∀ B [ T ]) —→ blame ℓ

  blame-up : ∀ {p : Imp} {ℓ : Label} →
    ((blame ℓ) ⇑ p) —→ blame ℓ

  blame-down : ∀ {p : Imp} {ℓ : Label} →
    ((blame ℓ) ⇓ p) —→ blame ℓ

  blame-reveal : ∀ {c : Conv↑} {ℓ : Label} →
    ((blame ℓ) ↑ c) —→ blame ℓ

  blame-conceal : ∀ {c : Conv↓} {ℓ : Label} →
    ((blame ℓ) ↓ c) —→ blame ℓ

  blame-⊕₁ : ∀ {ℓ : Label} {M : Term} {op : Prim} →
    (blame ℓ ⊕[ op ] M) —→ blame ℓ

  blame-⊕₂ : ∀ {ℓ : Label} {L : Term} {op : Prim} →
    Value L →
    (L ⊕[ op ] blame ℓ) —→ blame ℓ

--------------------------------------------------------------------------------
-- Store-threaded one-step reduction
--------------------------------------------------------------------------------

infix 2 _∣_—→_∣_
data _∣_—→_∣_ : Store → Term → Store → Term → Set where

  pure-step : ∀ {Σ : Store} {M M′ : Term} →
    M —→ M′ →
    ---------------
    Σ ∣ M —→ Σ ∣ M′

  β-Λ : ∀ {Σ : Store} {A B : Ty} {V : Term} →
    ---------------------------------------------------------------------------
    let α = length Σ in
    Σ ∣ (Λ V) ⦂∀ B [ A ]  —→  (α , A) ∷ Σ ∣ V [ ｀ α ]ᵀ ↑ (convert↑ B α)

  β-down-∀ : ∀ {Σ : Store} {A B V p} →
    Value V →
    ---------------------------------------------------------------------------
    let α = length Σ in
    Σ ∣ V ⇓ (‵∀ p) ⦂∀ B [ A ] —→
      (α , A) ∷ Σ ∣ V ⦂∀ (tgt⊑ p) [ ｀ α ] ⇓ (p [ ｀ α ]⊑) ↑ convert↑ (src⊑ p) α

  β-down-ν : ∀ {Σ : Store} {A C V p} →
    Value V →
    -------------------------------------------------------
    let α = length Σ in
    Σ ∣ V ⇓ (ν p) ⦂∀ C [ A ] —→
      (α , A) ∷ Σ ∣ V ⇓ (p [ ｀ α ]⊑) ↑ convert↑ (src⊑ p) α

  β-up-ν : ∀ {Σ : Store} {V p} →
    Value V →
    ---------------------------------------------------------------------------
    let α = length Σ in
    Σ ∣ V ⇑ (ν p)  —→  (α , ★) ∷ Σ ∣ V ⦂∀ (src⊑ p) [ ｀ α ] ⇑ p [ ｀ α ]⊑

  β-reveal-∀ : ∀ {Σ : Store} {B T V c} →
    Value V →
    Σ ∣ ((V ↑ (↑-∀ c)) ⦂∀ B [ T ]) —→ Σ ∣
      ((V ⦂∀ (src↑ (⟰ᵗ Σ) c) [ T ]) ↑
        (subst↑ (singleTyEnv T) c))

  β-conceal-∀ : ∀ {Σ : Store} {B T V c} →
    Value V →
    Σ ∣ ((V ↓ (↓-∀ c)) ⦂∀ B [ T ]) —→ Σ ∣
      ((V ⦂∀ (src↓ (⟰ᵗ Σ) c) [ T ]) ↓
        (subst↓ (singleTyEnv T) c))

  ξ-·₁ : ∀ {Σ Σ′ : Store} {L M L′ : Term} →
    Σ ∣ L —→ Σ′ ∣ L′ →
    Σ ∣ (L · M) —→ Σ′ ∣ (L′ · M)

  ξ-·₂ : ∀ {Σ Σ′ : Store} {V M M′ : Term} →
    Value V →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (V · M) —→ Σ′ ∣ (V · M′)

  ξ-·α : ∀ {Σ Σ′ : Store} {M M′ : Term} {B T : Ty} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M ⦂∀ B [ T ]) —→ Σ′ ∣ (M′ ⦂∀ B [ T ])

  ξ-⇑ : ∀ {Σ Σ′ : Store} {p : Imp} {M M′ : Term} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M ⇑ p) —→ Σ′ ∣ (M′ ⇑ p)

  ξ-⇓ : ∀ {Σ Σ′ : Store} {p : Imp} {M M′ : Term} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M ⇓ p) —→ Σ′ ∣ (M′ ⇓ p)

  ξ-↑ : ∀ {Σ Σ′ : Store} {c : Conv↑} {M M′ : Term} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M ↑ c) —→ Σ′ ∣ (M′ ↑ c)

  ξ-↓ : ∀ {Σ Σ′ : Store} {c : Conv↓} {M M′ : Term} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M ↓ c) —→ Σ′ ∣ (M′ ↓ c)

  ξ-⊕₁ : ∀ {Σ Σ′ : Store} {L M L′ : Term} {op : Prim} →
    Σ ∣ L —→ Σ′ ∣ L′ →
    Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L′ ⊕[ op ] M)

  ξ-⊕₂ : ∀ {Σ Σ′ : Store} {L M M′ : Term} {op : Prim} →
    Value L →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L ⊕[ op ] M′)

------------------------------------------------------------------------
-- Store-threaded multi-step reduction
------------------------------------------------------------------------

infix 2 _∣_—↠_∣_
infix 3 _∎
infixr 2 _—→⟨_⟩_

data _∣_—↠_∣_ : Store → Term → Store → Term → Set where
  _∎ : ∀ {Σ : Store} →
    (M : Term) →
    Σ ∣ M —↠ Σ ∣ M

  _—→⟨_⟩_ :
    ∀ {Σ Σ′ Σ″ : Store} {N K : Term} →
    (M : Term) →
    Σ ∣ M —→ Σ′ ∣ N →
    Σ′ ∣ N —↠ Σ″ ∣ K →
    Σ ∣ M —↠ Σ″ ∣ K

------------------------------------------------------------------------
-- Convergence and blame observations
------------------------------------------------------------------------

Blame : Term → Set
Blame M = ∃[ ℓ ] (M ≡ blame ℓ)

Blames : Store → Term → Set
Blames Σ M = ∃[ Σ′ ] ∃[ ℓ ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ)

Converges : Store → Term → Set
Converges Σ M =
  ∃[ Σ′ ] ∃[ W ] ((Σ ∣ M —↠ Σ′ ∣ W) × (Value W ⊎ Blame W))

Diverges : Store → Term → Set
Diverges Σ M = ¬ Converges Σ M

DivergeOrBlame : Store → Term → Set
DivergeOrBlame Σ M =
  ∀ Σ′ N →
  Σ ∣ M —↠ Σ′ ∣ N →
  Blame N ⊎ (∃[ Σ″ ] ∃[ N″ ] (Σ′ ∣ N —→ Σ″ ∣ N″))
