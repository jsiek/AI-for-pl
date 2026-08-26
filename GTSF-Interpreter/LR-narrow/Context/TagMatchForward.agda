module LR-narrow.Context.TagMatchForward where

-- File Charter:
--   * Proves forward coherence of corresponding interpreter tag checks.
--   * Equal left tags force equal right tags through paired-seal functionality.
--   * Contains exactly one exported theorem.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter using (Tag; seal-name; variable-tag)
open import LR-narrow.Context.PairedBindingFunctional
open import LR-narrow.Dynamic
open import LR-narrow.World
open import Types using (Ty; TyCtx)

tag-match-forward : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {current : World}
    {I : Interpretation {Φ} {Δᴾ} {Δᴵ} current}
    {Gᴾ Gᴵ Hᴾ Hᴵ : Ty}
    {p : Φ ∣ Δᴾ ⊢ Gᴾ ⊑ Gᴵ ⊣ Δᴵ}
    {q : Φ ∣ Δᴾ ⊢ Hᴾ ⊑ Hᴵ ⊣ Δᴵ}
    {left-expected right-expected left-actual right-actual : Tag}
  → TagEqualityAt I p left-expected right-expected
  → TagEqualityAt I q left-actual right-actual
  → left-expected ≡ left-actual
  → right-expected ≡ right-actual
tag-match-forward {current = current}
    (variable-tags-equal right-name left-name binding)
    (variable-tags-equal other-right-name other-left-name other-binding)
    refl =
  cong (λ α → variable-tag (seal-name α))
    (paired-binding-functional {w = current} binding other-binding)
tag-match-forward base-tags-equal base-tags-equal refl = refl
tag-match-forward function-tags-equal function-tags-equal refl = refl
