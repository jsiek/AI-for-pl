module proof.LR.PrecisionUnique where

-- File Charter:
--   * Two-context precision derivations are unique (notes/logrel-dgg.md,
--     Section 6.9, item 4).  The rules `•⊑•` and `•⊑` of
--     `LR.CastPrecision` carry a derivation of the substituted types as
--     a premise; the substitution lemma produces a particular one, and
--     uniqueness says it is the premise.
--   * The proof is by induction on both derivations.  Two pairs of rules
--     can derive the same types: `∀⊑∀` and `∀⊑` (when the right type is
--     a `∀`), and `∀⊑` and `∀⊑★` (when it is `★`).  Those cases are
--     refuted by `forget`: their images in `Imprecision` start with
--     different rules, and `Imprecision`'s derivations are unique.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Types
open import LR.Precision
open import proof.LR.Precision using (forget)
import proof.Imprecision as PI

↔-unique : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X Y} (x y : Φ ∋ X ↔ Y) → x ≡ y
↔-unique ↔-here ↔-here = refl
↔-unique (↔-pair x) (↔-pair y) = cong ↔-pair (↔-unique x y)
↔-unique (↔-only x) (↔-only y) = cong ↔-only (↔-unique x y)
↔-unique (↔-dead x) (↔-dead y) = cong ↔-dead (↔-unique x y)

only-unique : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X} (x y : Φ ∋ X only) → x ≡ y
only-unique only-here only-here = refl
only-unique (only-pair x) (only-pair y) = cong only-pair (only-unique x y)
only-unique (only-only x) (only-only y) = cong only-only (only-unique x y)
only-unique (only-dead x) (only-dead y) = cong only-dead (only-unique x y)

⊑-unique : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p q : Φ ⊢ A ⊑ B) → p ≡ q
⊑-unique ★⊑★ ★⊑★ = refl
⊑-unique ι⊑ι ι⊑ι = refl
⊑-unique (X⊑Y x) (X⊑Y y) = cong X⊑Y (↔-unique x y)
⊑-unique (⇒⊑⇒ p q) (⇒⊑⇒ p′ q′)
    rewrite ⊑-unique p p′
          | ⊑-unique q q′ =
  refl
⊑-unique (∀⊑∀ p) (∀⊑∀ p′) = cong ∀⊑∀ (⊑-unique p p′)
⊑-unique (∀⊑∀ p) (∀⊑ a z q)
    with PI.⊑-unique (forget (∀⊑∀ p)) (forget (∀⊑ a z q))
⊑-unique (∀⊑∀ p) (∀⊑ a z q) | ()
⊑-unique (∀⊑∀ (X⊑★ ())) bot-elim
⊑-unique (⇒⊑★ p q) (⇒⊑★ p′ q′)
    rewrite ⊑-unique p p′
          | ⊑-unique q q′ =
  refl
⊑-unique ι⊑★ ι⊑★ = refl
⊑-unique (X⊑★ x) (X⊑★ y) = cong X⊑★ (only-unique x y)
⊑-unique (∀⊑ a z p) (∀⊑∀ q)
    with PI.⊑-unique (forget (∀⊑ a z p)) (forget (∀⊑∀ q))
⊑-unique (∀⊑ a z p) (∀⊑∀ q) | ()
⊑-unique (∀⊑ a z p) (∀⊑ a′ z′ p′)
    rewrite nonVar-unique a a′
          | PI.∈ᵗ-unique z z′
          | ⊑-unique p p′ =
  refl
⊑-unique (∀⊑ a () p) ∀★⊑★
⊑-unique (∀⊑ a z p) (∀⊑★ ns q)
    with PI.⊑-unique (forget (∀⊑ a z p)) (forget (∀⊑★ ns q))
⊑-unique (∀⊑ a z p) (∀⊑★ ns q) | ()
⊑-unique (∀⊑ () z p) bot-elim
⊑-unique (∀⊑ () z p) bot⊑★
⊑-unique ∀★⊑★ (∀⊑ a () q)
⊑-unique ∀★⊑★ ∀★⊑★ = refl
⊑-unique ∀★⊑★ (∀⊑★ () q)
⊑-unique (∀⊑★ ns p) (∀⊑ a z q)
    with PI.⊑-unique (forget (∀⊑★ ns p)) (forget (∀⊑ a z q))
⊑-unique (∀⊑★ ns p) (∀⊑ a z q) | ()
⊑-unique (∀⊑★ () p) ∀★⊑★
⊑-unique (∀⊑★ ns p) (∀⊑★ ns′ p′)
    rewrite nonStar-unique ns ns′
          | ⊑-unique p p′ =
  refl
⊑-unique (∀⊑★ ns (X⊑★ ())) bot⊑★
⊑-unique bot-elim (∀⊑∀ (X⊑★ ()))
⊑-unique bot-elim (∀⊑ () z q)
⊑-unique bot-elim bot-elim = refl
⊑-unique bot⊑★ (∀⊑ () z q)
⊑-unique bot⊑★ (∀⊑★ ns (X⊑★ ()))
⊑-unique bot⊑★ bot⊑★ = refl
