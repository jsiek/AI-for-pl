module proof.CoreLemmas where

-- File Charter:
--   * Small private helper lemmas used by multiple proof modules.
--   * Currently includes `_≟Ty_` and multi-step transitivity.

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import STLC

multi-trans : {M N L : Term} -> M —↠ N -> N —↠ L -> M —↠ L
multi-trans (_ ∎) ms2 = ms2
multi-trans (_ —→⟨ s ⟩ ms1') ms2 = _ —→⟨ s ⟩ (multi-trans ms1' ms2)

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
nat ≟Ty nat = yes refl
nat ≟Ty (B ⇒ B₁) = no λ ()
(A ⇒ A₁) ≟Ty nat = no (λ ())
(A₁ ⇒ A₂) ≟Ty (B₁ ⇒ B₂)
    with A₁ ≟Ty B₁ | A₂ ≟Ty B₂
... | yes refl | yes refl = yes refl
... | no neq | _ = no λ { refl → neq refl }
... | _ | no neq = no λ { refl → neq refl }
