module LR-narrow.Context.GroundTagAgreementFuture where

-- File Charter:
--   * Preserves dynamic ground-tag agreement in a future interpretation.
--   * Keeps the observed runtime tags and their `tagOf` equations unchanged.
--   * Contains exactly one exported theorem.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter using (TypeEnvironment)
open import LR-narrow.Context.TagEqualityFuture
open import LR-narrow.Dynamic
open import LR-narrow.World using (Interpretation; World; _⊒ⁱ_)
open import Types using (Ground; Ty; TyCtx)

ground-tag-agreement-future : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {Gᴾ Gᴵ : Ty} {current future : World}
    {I : Interpretation {Φ} {Δᴾ} {Δᴵ} current}
    {J : Interpretation {Φ} {Δᴾ} {Δᴵ} future}
    {q : Φ ∣ Δᴾ ⊢ Gᴾ ⊑ Gᴵ ⊣ Δᴵ}
    {gᴵ : Ground Gᴵ} {gᴾ : Ground Gᴾ}
    {θᴵ θᴾ : TypeEnvironment}
  → J ⊒ⁱ I
  → GroundTagAgreement I q gᴵ gᴾ θᴵ θᴾ
  → GroundTagAgreement J q gᴵ gᴾ θᴵ θᴾ
ground-tag-agreement-future J⊒I
    (ground-tag-agreement left-tag right-tag
      left-result right-result tags-equal) =
  ground-tag-agreement left-tag right-tag left-result right-result
    (tag-equality-future J⊒I tags-equal)
