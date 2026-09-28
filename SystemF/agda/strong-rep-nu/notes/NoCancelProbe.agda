module strong-rep-nu.notes.NoCancelProbe where

-- File Charter:
--   * JUSTIFIES THE PAPER'S FORMULATION of the chain rules (paper/main.tex,
--     the Conversions figure).  The paper states the side conditions of
--     `conv-seal-seq` and `conv-unseal-seq` as "the smart constructor
--     leaves the chain unchanged",
--         t ;ˢ seal X = t ; seal X        and     unseal X ;ˢ c = unseal X ; c,
--     where the mechanization has `¬ IsIdᵀ t` and `¬ IsIdᶜ c × NoCancel X c`.
--     `seal-tight→/←` and `unseal-tight→/←` below prove the two
--     formulations equivalent, so the paper's rules and Conversion.agda's
--     define the same judgement.
--   * The key lemma: on a tail, `NoCancelᵀ X t` holds exactly when
--     cancelling finds nothing, `cancelᵀ X t ≡ unseal X ⨾ tail t`
--     (`nocancel→cancel`, `cancel→nocancel`, via `cancel-shape`).

open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong-rep-nu.Conversion

-- NoCancel on a tail is exactly "cancelling finds nothing to cancel".
nocancel→cancel : ∀ X t → NoCancelᵀ X t → cancelᵀ X t ≡ unseal X ⨾ tail t
nocancel→cancel X (mid g) _ = refl
nocancel→cancel X (seal Y) ne with X ≟ Y
... | yes eq = ⊥-elim (ne eq)
... | no  _  = refl
nocancel→cancel X (t ⨾seal Y) nc with cancelᵀ X t | nocancel→cancel X t nc
... | unseal .X ⨾ .(tail t) | refl = refl

-- cancelling either cancels (a tail) or finds nothing (unseal X ; t)
cancel-shape : ∀ X t → (Σ[ t′ ∈ Tail ] cancelᵀ X t ≡ tail t′)
                     ⊎ (cancelᵀ X t ≡ unseal X ⨾ tail t)
cancel-shape X (mid g) = inj₂ refl
cancel-shape X (seal Y) with X ≟ Y
... | yes _ = inj₁ (_ , refl)
... | no  _ = inj₂ refl
cancel-shape X (t ⨾seal Y) with cancelᵀ X t | cancel-shape X t
... | tail t′     | _ = inj₁ (_ , refl)
... | unseal Z     | inj₁ (_ , ())
... | unseal Z     | inj₂ ()
... | unseal Z ⨾ c | inj₁ (_ , ())
... | unseal Z ⨾ c | inj₂ refl = inj₂ refl

cancel→nocancel : ∀ X t → cancelᵀ X t ≡ unseal X ⨾ tail t → NoCancelᵀ X t
cancel→nocancel X (mid g) _ = _
cancel→nocancel X (seal Y) eq with X ≟ Y
cancel→nocancel X (seal Y) () | yes _
cancel→nocancel X (seal Y) eq | no ne = ne
cancel→nocancel X (t ⨾seal Y) eq with cancel-shape X t
... | inj₂ e = cancel→nocancel X t e
... | inj₁ (t′ , e) rewrite e with eq
...   | ()

------------------------------------------------------------------------
-- The chain side conditions are "the smart constructor changes nothing"
------------------------------------------------------------------------

seal-tight→ : ∀ {t X} → ¬ IsIdᵀ t → t ⨾sealˢ X ≡ t ⨾seal X
seal-tight→ {t} ¬id with isIdᵀ? t
... | yes p = ⊥-elim (¬id p)
... | no  _ = refl

seal-tight← : ∀ {t X} → t ⨾sealˢ X ≡ t ⨾seal X → ¬ IsIdᵀ t
seal-tight← {t} eq p with isIdᵀ? t
seal-tight← {t} () p | yes _
seal-tight← {t} eq p | no ¬p = ¬p p

unseal-tight→ : ∀ {X c} → ¬ IsIdᶜ c → NoCancel X c
  → unseal X ⨾ˢ c ≡ unseal X ⨾ c
unseal-tight→ {X} {tail t} ¬id nc with isIdᵀ? t
... | yes p = ⊥-elim (¬id p)
... | no  _ = nocancel→cancel X t nc
unseal-tight→ {c = unseal Y}     _ _ = refl
unseal-tight→ {c = unseal Y ⨾ c} _ _ = refl

unseal-tight← : ∀ {X c} → unseal X ⨾ˢ c ≡ unseal X ⨾ c
  → ¬ IsIdᶜ c × NoCancel X c
unseal-tight← {X} {tail t} eq with isIdᵀ? t
unseal-tight← {X} {tail t} () | yes _
unseal-tight← {X} {tail t} eq | no ¬p = ¬p , cancel→nocancel X t eq
unseal-tight← {c = unseal Y}     _ = (λ ()) , _
unseal-tight← {c = unseal Y ⨾ c} _ = (λ ()) , _
