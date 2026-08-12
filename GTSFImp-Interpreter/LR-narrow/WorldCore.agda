module LR-narrow.WorldCore where

-- File Charter:
--   * Defines the three-context core used by the intrinsic LR world.
--   * Embeds precise and imprecise runtime types into one center context.
--   * Provides paired fresh binding while keeping endpoint stores distinct.

open import Data.Nat using (suc)

open import Types
open import TyStore
open import Consistency using (_↪ᵗ_; keep; toRenameᵗ)
import Imprecision as I

record CoreWorld (Δᴾ Δᴵ Δᶜ : TyCtx) : Set where
  constructor core-world
  field
    preciseEmbedding : Δᴾ ↪ᵗ Δᶜ
    impreciseEmbedding : Δᴵ ↪ᵗ Δᶜ
    impEnv : I.ImpEnv Δᶜ
    preciseStore : TyStore Δᴾ
    impreciseStore : TyStore Δᴵ

open CoreWorld public

embedPrecise : ∀ {Δᴾ Δᴵ Δᶜ}
  → CoreWorld Δᴾ Δᴵ Δᶜ
  → Ty Δᴾ
  → Ty Δᶜ
embedPrecise W = renameᵗ (toRenameᵗ (preciseEmbedding W))

embedImprecise : ∀ {Δᴾ Δᴵ Δᶜ}
  → CoreWorld Δᴾ Δᴵ Δᶜ
  → Ty Δᴵ
  → Ty Δᶜ
embedImprecise W = renameᵗ (toRenameᵗ (impreciseEmbedding W))

infix 4 _⊑ᵂ⟨_⟩_

_⊑ᵂ⟨_⟩_ : ∀ {Δᴾ Δᴵ Δᶜ}
  → Ty Δᴾ
  → CoreWorld Δᴾ Δᴵ Δᶜ
  → Ty Δᴵ
  → Set
Aᴾ ⊑ᵂ⟨ W ⟩ Aᴵ =
  impEnv W I.⊢ embedPrecise W Aᴾ ⊑ embedImprecise W Aᴵ

pairedBindCore : ∀ {Δᴾ Δᴵ Δᶜ}
  → CoreWorld Δᴾ Δᴵ Δᶜ
  → Ty Δᴾ
  → Ty Δᴵ
  → CoreWorld (suc Δᴾ) (suc Δᴵ) (suc Δᶜ)
pairedBindCore W Aᴾ Aᴵ =
  core-world (keep (preciseEmbedding W)) (keep (impreciseEmbedding W))
    (I.extᵐ (impEnv W)) (store-bind (preciseStore W) Aᴾ)
    (store-bind (impreciseStore W) Aᴵ)
