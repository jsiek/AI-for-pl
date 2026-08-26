module LR-narrow.Context.TagEqualityFuture where

-- File Charter:
--   * Preserves observable dynamic-tag equality in a future interpretation.
--   * Uses preservation of both interpretation type environments and bindings.
--   * Contains exactly one exported theorem.

open import Agda.Builtin.Equality using (refl)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter using (Tag)
open import LR-narrow.Dynamic
open import LR-narrow.World
open import Types using (Ty; TyCtx)

tag-equality-future : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {Gᴾ Gᴵ : Ty} {current future : World}
    {I : Interpretation {Φ} {Δᴾ} {Δᴵ} current}
    {J : Interpretation {Φ} {Δᴾ} {Δᴵ} future}
    {q : Φ ∣ Δᴾ ⊢ Gᴾ ⊑ Gᴵ ⊣ Δᴵ}
    {left-tag right-tag : Tag}
  → J ⊒ⁱ I
  → TagEqualityAt I q left-tag right-tag
  → TagEqualityAt J q left-tag right-tag
tag-equality-future
    (future-interpretation growth refl refl refl)
    (variable-tags-equal right-name left-name binding) =
  variable-tags-equal right-name left-name
    (paired-binding-weaken (bindings-future growth) binding)
tag-equality-future J⊒I base-tags-equal = base-tags-equal
tag-equality-future J⊒I function-tags-equal = function-tags-equal
