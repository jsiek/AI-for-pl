module proof.RightTagInversion where

-- File Charter:
--   * Structural inversion lemmas for term narrowing whose target is a raw
--     right tag `V ⟨ G ! ⟩`.
--   * Proves `right-tag-inversion₁` used by the dynamic gradual guarantee.
--   * Depends only on term narrowing, coercion grammar, and narrowing
--     composition side conditions; it does not depend on catchup.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_)

open import Types
open import Coercions
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing

------------------------------------------------------------------------
-- Proof-strategy log
------------------------------------------------------------------------

-- 1. Direct inversion on `⊒cast+` first looked promising: a target
--    `V ⟨ G ! ⟩` would have to come from `- s`, so `s` must be raw
--    `G ？`.  This fails as a productive branch because raw `G ？` is not
--    a narrowing grammar form; only `(G ？) ︔ g` is.
-- 2. The symmetric `⊒cast-` branch would need raw `G !` as a narrowing.
--    That fails for the same reason: tags live in the widening grammar, not
--    as bare narrowing spines.
-- 3. Left-cast and store-prefix constructors do not introduce the right tag;
--    they only preserve the target shape, so recurse through them.
--
-- The resulting proof is vacuous: no valid term-narrowing derivation can have
-- a raw right target tag `G !`.

raw-untag-narrowing⊥ :
  ∀ {μ Δ Σ A B G} →
  μ ∣ Δ ∣ Σ ⊢ G ？ ∶ A ⊒ B →
  ⊥
raw-untag-narrowing⊥ (_ , cross ())

raw-tag-narrowing⊥ :
  ∀ {μ Δ Σ A B G} →
  μ ∣ Δ ∣ Σ ⊢ G ! ∶ A ⊒ B →
  ⊥
raw-tag-narrowing⊥ (_ , cross ())

compose-raw-untag-right⊥ :
  ∀ {Δ σ q r A B G} →
  Δ ∣ σ ⊢ q ⨾ⁿ G ？ ≈ r ∶ A ⊒ B →
  ⊥
compose-raw-untag-right⊥ (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  raw-untag-narrowing⊥ s⊒

compose-raw-tag-right⊥ :
  ∀ {Δ σ q r A B G} →
  Δ ∣ σ ⊢ q ⨾ⁿ G ! ≈ r ∶ A ⊒ B →
  ⊥
compose-raw-tag-right⊥ (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  raw-tag-narrowing⊥ s⊒

data RawRightTag : Term → Set where
  raw-right-tag : ∀ {V G} → RawRightTag (V ⟨ G ! ⟩)

raw-right-tag-cast+⊥ :
  ∀ {Δ σ q r A B M s} →
  RawRightTag (M ⟨ - s ⟩) →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  ⊥
raw-right-tag-cast+⊥ {s = id A} () q⨟s≈r
raw-right-tag-cast+⊥ {s = s ︔ t} () q⨟s≈r
raw-right-tag-cast+⊥ {s = s ↦ t} () q⨟s≈r
raw-right-tag-cast+⊥ {s = `∀ s} () q⨟s≈r
raw-right-tag-cast+⊥ {s = (＇ α) !} () q⨟s≈r
raw-right-tag-cast+⊥ {s = (‵ ι) !} () q⨟s≈r
raw-right-tag-cast+⊥ {s = ★ !} () q⨟s≈r
raw-right-tag-cast+⊥ {s = (A ⇒ B) !} () q⨟s≈r
raw-right-tag-cast+⊥ {s = (`∀ A) !} () q⨟s≈r
raw-right-tag-cast+⊥ {s = (＇ α) ？} raw-right-tag q⨟s≈r =
  compose-raw-untag-right⊥ q⨟s≈r
raw-right-tag-cast+⊥ {s = (‵ ι) ？} raw-right-tag q⨟s≈r =
  compose-raw-untag-right⊥ q⨟s≈r
raw-right-tag-cast+⊥ {s = ★ ？} raw-right-tag q⨟s≈r =
  compose-raw-untag-right⊥ q⨟s≈r
raw-right-tag-cast+⊥ {s = (A ⇒ B) ？} raw-right-tag q⨟s≈r =
  compose-raw-untag-right⊥ q⨟s≈r
raw-right-tag-cast+⊥ {s = (`∀ A) ？} raw-right-tag q⨟s≈r =
  compose-raw-untag-right⊥ q⨟s≈r
raw-right-tag-cast+⊥ {s = seal A α} () q⨟s≈r
raw-right-tag-cast+⊥ {s = unseal α A} () q⨟s≈r
raw-right-tag-cast+⊥ {s = gen A s} () q⨟s≈r
raw-right-tag-cast+⊥ {s = inst B s} () q⨟s≈r

raw-right-tag-cast-⊥ :
  ∀ {Δ σ q r A B M s} →
  RawRightTag (M ⟨ s ⟩) →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  ⊥
raw-right-tag-cast-⊥ {s = id A} () q⨟s≈r
raw-right-tag-cast-⊥ {s = s ︔ t} () q⨟s≈r
raw-right-tag-cast-⊥ {s = s ↦ t} () q⨟s≈r
raw-right-tag-cast-⊥ {s = `∀ s} () q⨟s≈r
raw-right-tag-cast-⊥ {s = G !} raw-right-tag q⨟s≈r =
  compose-raw-tag-right⊥ q⨟s≈r
raw-right-tag-cast-⊥ {s = G ？} () q⨟s≈r
raw-right-tag-cast-⊥ {s = seal A α} () q⨟s≈r
raw-right-tag-cast-⊥ {s = unseal α A} () q⨟s≈r
raw-right-tag-cast-⊥ {s = gen A s} () q⨟s≈r
raw-right-tag-cast-⊥ {s = inst B s} () q⨟s≈r

raw-right-tag-⇑ᵗᵐ :
  ∀ {N} →
  RawRightTag N →
  RawRightTag (⇑ᵗᵐ N)
raw-right-tag-⇑ᵗᵐ raw-right-tag = raw-right-tag

raw-right-tag-target⊥ :
  ∀ {Δ σ γ M N q} →
  RawRightTag N →
  Δ ∣ σ ∣ γ ⊢ M ⊒ N ∶ q →
  ⊥
raw-right-tag-target⊥ tag (extend qᶜ pαᶜ M⊒N) =
  raw-right-tag-target⊥ tag M⊒N
raw-right-tag-target⊥ tag (split qᶜ pαᶜ M⊒N) =
  raw-right-tag-target⊥ tag M⊒N
raw-right-tag-target⊥ tag (⊒cast+ qᶜ q⨟s≈r M⊒V) =
  raw-right-tag-cast+⊥ tag q⨟s≈r
raw-right-tag-target⊥ tag (⊒cast- qᶜ q⨟s≈r M⊒V) =
  raw-right-tag-cast-⊥ tag q⨟s≈r
raw-right-tag-target⊥ tag (ν⊒ pᶜ N⊒N′) =
  raw-right-tag-target⊥ (raw-right-tag-⇑ᵗᵐ tag) N⊒N′
raw-right-tag-target⊥ tag (cast+⊒ pᶜ r≈t⨾p M⊒N) =
  raw-right-tag-target⊥ tag M⊒N
raw-right-tag-target⊥ tag (cast-⊒ pᶜ r≈t⨾p M⊒N) =
  raw-right-tag-target⊥ tag M⊒N

right-tag-target⊥ :
  ∀ {Δ σ γ M V q G} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ G ! ⟩ ∶ q →
  ⊥
right-tag-target⊥ M⊒V! =
  raw-right-tag-target⊥ raw-right-tag M⊒V!

right-tag-inversion₁ :
  ∀ {Δ σ γ M V q G} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ G ! ⟩ ∶ q →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ G ？
right-tag-inversion₁ M⊒V! =
  ⊥-elim (right-tag-target⊥ M⊒V!)
