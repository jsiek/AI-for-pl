module proof.RightTagSealInversion where

-- File Charter:
--   * Right-hand inversion lemmas for raw tag and seal casts in term
--     narrowing.
--   * Exports the four lemmas used by `proof.DynamicGradualGuarantee`.
--   * The proof factors through equality-indexed target-shape contradiction
--     lemmas so store-opening constructors (`extend`, `split`, and `ν⊒`) can
--     be handled before Agda has to invert type-variable opening.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Types
open import Coercions renaming
  ( gen to genᶜ
  ; _! to _!ᶜ
  ; _？ to _？ᶜ
  ; seal to sealᶜ
  ; unseal to unsealᶜ
  )
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing

------------------------------------------------------------------------
-- Raw coercion-shape exclusions
------------------------------------------------------------------------

rawTag : Ty → Coercion
rawTag G = G !ᶜ

rawUntag : Ty → Coercion
rawUntag G = G ？ᶜ

rawSeal : Ty → TyVar → Coercion
rawSeal A α = sealᶜ A α

rawUnseal : TyVar → Ty → Coercion
rawUnseal α A = unsealᶜ α A

rawGen : Ty → Coercion → Coercion
rawGen A s = genᶜ A s

cast-coercion-injective :
  ∀ {M N : Term} {c d : Coercion} →
  M ⟨ c ⟩ ≡ N ⟨ d ⟩ →
  c ≡ d
cast-coercion-injective refl = refl

narrowing-not-tag! :
  ∀ {s : Coercion} {G : Ty} →
  Narrowing s →
  s ≡ rawTag G →
  ⊥
narrowing-not-tag! (cross (id-＇ α)) ()
narrowing-not-tag! (cross (id-‵ ι)) ()
narrowing-not-tag! (cross (sʷ ↦ tⁿ)) ()
narrowing-not-tag! (cross (`∀ sⁿ)) ()
narrowing-not-tag! id★ ()
narrowing-not-tag! (gen sⁿ) ()
narrowing-not-tag! (gG ？︔ sⁿ) ()
narrowing-not-tag! (sⁿ ︔seal α) ()

narrowing-not-untag? :
  ∀ {s : Coercion} {G : Ty} →
  Narrowing s →
  s ≡ rawUntag G →
  ⊥
narrowing-not-untag? (cross (id-＇ α)) ()
narrowing-not-untag? (cross (id-‵ ι)) ()
narrowing-not-untag? (cross (sʷ ↦ tⁿ)) ()
narrowing-not-untag? (cross (`∀ sⁿ)) ()
narrowing-not-untag? id★ ()
narrowing-not-untag? (gen sⁿ) ()
narrowing-not-untag? (gG ？︔ sⁿ) ()
narrowing-not-untag? (sⁿ ︔seal α) ()

narrowing-not-seal :
  ∀ {s : Coercion} {A : Ty} {α : TyVar} →
  Narrowing s →
  s ≡ rawSeal A α →
  ⊥
narrowing-not-seal (cross (id-＇ α)) ()
narrowing-not-seal (cross (id-‵ ι)) ()
narrowing-not-seal (cross (sʷ ↦ tⁿ)) ()
narrowing-not-seal (cross (`∀ sⁿ)) ()
narrowing-not-seal id★ ()
narrowing-not-seal (gen sⁿ) ()
narrowing-not-seal (gG ？︔ sⁿ) ()
narrowing-not-seal (sⁿ ︔seal α) ()

narrowing-not-unseal :
  ∀ {s : Coercion} {A : Ty} {α : TyVar} →
  Narrowing s →
  s ≡ rawUnseal α A →
  ⊥
narrowing-not-unseal (cross (id-＇ α)) ()
narrowing-not-unseal (cross (id-‵ ι)) ()
narrowing-not-unseal (cross (sʷ ↦ tⁿ)) ()
narrowing-not-unseal (cross (`∀ sⁿ)) ()
narrowing-not-unseal id★ ()
narrowing-not-unseal (gen sⁿ) ()
narrowing-not-unseal (gG ？︔ sⁿ) ()
narrowing-not-unseal (sⁿ ︔seal α) ()

narrowing-dual-not-tag! :
  ∀ {s : Coercion} {G : Ty} →
  Narrowing s →
  - s ≡ rawTag G →
  ⊥
narrowing-dual-not-tag! (cross (id-＇ α)) ()
narrowing-dual-not-tag! (cross (id-‵ ι)) ()
narrowing-dual-not-tag! (cross (sʷ ↦ tⁿ)) ()
narrowing-dual-not-tag! (cross (`∀ sⁿ)) ()
narrowing-dual-not-tag! id★ ()
narrowing-dual-not-tag! (gen sⁿ) ()
narrowing-dual-not-tag! (gG ？︔ sⁿ) ()
narrowing-dual-not-tag! (sⁿ ︔seal α) ()

narrowing-dual-not-untag? :
  ∀ {s : Coercion} {G : Ty} →
  Narrowing s →
  - s ≡ rawUntag G →
  ⊥
narrowing-dual-not-untag? (cross (id-＇ α)) ()
narrowing-dual-not-untag? (cross (id-‵ ι)) ()
narrowing-dual-not-untag? (cross (sʷ ↦ tⁿ)) ()
narrowing-dual-not-untag? (cross (`∀ sⁿ)) ()
narrowing-dual-not-untag? id★ ()
narrowing-dual-not-untag? (gen sⁿ) ()
narrowing-dual-not-untag? (gG ？︔ sⁿ) ()
narrowing-dual-not-untag? (sⁿ ︔seal α) ()

narrowing-dual-not-seal :
  ∀ {s : Coercion} {A : Ty} {α : TyVar} →
  Narrowing s →
  - s ≡ rawSeal A α →
  ⊥
narrowing-dual-not-seal (cross (id-＇ α)) ()
narrowing-dual-not-seal (cross (id-‵ ι)) ()
narrowing-dual-not-seal (cross (sʷ ↦ tⁿ)) ()
narrowing-dual-not-seal (cross (`∀ sⁿ)) ()
narrowing-dual-not-seal id★ ()
narrowing-dual-not-seal (gen sⁿ) ()
narrowing-dual-not-seal (gG ？︔ sⁿ) ()
narrowing-dual-not-seal (sⁿ ︔seal α) ()

narrowing-dual-not-unseal :
  ∀ {s : Coercion} {A : Ty} {α : TyVar} →
  Narrowing s →
  - s ≡ rawUnseal α A →
  ⊥
narrowing-dual-not-unseal (cross (id-＇ α)) ()
narrowing-dual-not-unseal (cross (id-‵ ι)) ()
narrowing-dual-not-unseal (cross (sʷ ↦ tⁿ)) ()
narrowing-dual-not-unseal (cross (`∀ sⁿ)) ()
narrowing-dual-not-unseal id★ ()
narrowing-dual-not-unseal (gen sⁿ) ()
narrowing-dual-not-unseal (gG ？︔ sⁿ) ()
narrowing-dual-not-unseal (sⁿ ︔seal α) ()

gen-not-tag! :
  ∀ {A G : Ty} {s : Coercion} →
  rawGen A s ≡ rawTag G →
  ⊥
gen-not-tag! {A = A} {G = G} {s = s} ()

gen-not-untag? :
  ∀ {A G : Ty} {s : Coercion} →
  rawGen A s ≡ rawUntag G →
  ⊥
gen-not-untag? {A = A} {G = G} {s = s} ()

gen-not-seal :
  ∀ {A B : Ty} {s : Coercion} {α : TyVar} →
  rawGen A s ≡ rawSeal B α →
  ⊥
gen-not-seal {A = A} {B = B} {s = s} {α = α} ()

gen-not-unseal :
  ∀ {A B : Ty} {s : Coercion} {α : TyVar} →
  rawGen A s ≡ rawUnseal α B →
  ⊥
gen-not-unseal {A = A} {B = B} {s = s} {α = α} ()

------------------------------------------------------------------------
-- Equality-indexed right target exclusions
------------------------------------------------------------------------

mutual
  right-tag-target₁⊥ :
    ∀ {Δ σ γ M T q V G} →
    T ≡ V ⟨ G !ᶜ ⟩ →
    Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ q →
    ⊥
  right-tag-target₁⊥ eq (extend qᶜ pαᶜ M⊒T) =
    right-tag-target₁⊥ eq M⊒T
  right-tag-target₁⊥ eq (split qᶜ pαᶜ M⊒T) =
    right-tag-target₁⊥ eq M⊒T
  right-tag-target₁⊥ () (⊒blame pᶜ)
  right-tag-target₁⊥ () (x⊒x pᶜ x∋p)
  right-tag-target₁⊥ () (ƛ⊒ƛ p↦qᶜ N⊒N′)
  right-tag-target₁⊥ () (·⊒· qᶜ L⊒L′ M⊒M′)
  right-tag-target₁⊥ () (Λ⊒Λ allᶜ vV V⊒V′)
  right-tag-target₁⊥ () (⊒Λ pᶜ N⊒V′)
  right-tag-target₁⊥ eq
      (⊒⟨ν⟩ pᶜ i N⊒V′) =
    gen-not-tag! (cast-coercion-injective eq)
  right-tag-target₁⊥ () (α⊒α qᶜ pαᶜ L⊒L′)
  right-tag-target₁⊥ () (⊒α pαᶜ L⊒L′)
  right-tag-target₁⊥ () (ν⊒ν pᶜ qᶜ N⊒N′)
  right-tag-target₁⊥ () (⊒ν pᶜ N⊒N′)
  right-tag-target₁⊥ eq (ν⊒ pᶜ N⊒N′) =
    right-tag-target₁⊥ (cong ⇑ᵗᵐ eq) N⊒N′
  right-tag-target₁⊥ () (κ⊒κ κ)
  right-tag-target₁⊥ () (⊕⊒⊕ M⊒M′ N⊒N′)
  right-tag-target₁⊥ eq
      (⊒cast+ qᶜ
        (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r)
        M⊒M′) =
    narrowing-dual-not-tag!
      (proj₂ s⊒) (cast-coercion-injective eq)
  right-tag-target₁⊥ eq
      (⊒cast- qᶜ
        (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r)
        M⊒M′) =
    narrowing-not-tag!
      (proj₂ s⊒) (cast-coercion-injective eq)
  right-tag-target₁⊥ eq (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
    right-tag-target₁⊥ eq M⊒M′
  right-tag-target₁⊥ eq (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
    right-tag-target₁⊥ eq M⊒M′

  right-tag-target₂⊥ :
    ∀ {Δ σ γ M T r V G} →
    T ≡ V ⟨ G ？ᶜ ⟩ →
    Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ r →
    ⊥
  right-tag-target₂⊥ eq (extend qᶜ pαᶜ M⊒T) =
    right-tag-target₂⊥ eq M⊒T
  right-tag-target₂⊥ eq (split qᶜ pαᶜ M⊒T) =
    right-tag-target₂⊥ eq M⊒T
  right-tag-target₂⊥ () (⊒blame pᶜ)
  right-tag-target₂⊥ () (x⊒x pᶜ x∋p)
  right-tag-target₂⊥ () (ƛ⊒ƛ p↦qᶜ N⊒N′)
  right-tag-target₂⊥ () (·⊒· qᶜ L⊒L′ M⊒M′)
  right-tag-target₂⊥ () (Λ⊒Λ allᶜ vV V⊒V′)
  right-tag-target₂⊥ () (⊒Λ pᶜ N⊒V′)
  right-tag-target₂⊥ eq
      (⊒⟨ν⟩ pᶜ i N⊒V′) =
    gen-not-untag? (cast-coercion-injective eq)
  right-tag-target₂⊥ () (α⊒α qᶜ pαᶜ L⊒L′)
  right-tag-target₂⊥ () (⊒α pαᶜ L⊒L′)
  right-tag-target₂⊥ () (ν⊒ν pᶜ qᶜ N⊒N′)
  right-tag-target₂⊥ () (⊒ν pᶜ N⊒N′)
  right-tag-target₂⊥ eq (ν⊒ pᶜ N⊒N′) =
    right-tag-target₂⊥ (cong ⇑ᵗᵐ eq) N⊒N′
  right-tag-target₂⊥ () (κ⊒κ κ)
  right-tag-target₂⊥ () (⊕⊒⊕ M⊒M′ N⊒N′)
  right-tag-target₂⊥ eq
      (⊒cast+ qᶜ
        (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r)
        M⊒M′) =
    narrowing-dual-not-untag?
      (proj₂ s⊒) (cast-coercion-injective eq)
  right-tag-target₂⊥ eq
      (⊒cast- qᶜ
        (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r)
        M⊒M′) =
    narrowing-not-untag?
      (proj₂ s⊒) (cast-coercion-injective eq)
  right-tag-target₂⊥ eq (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
    right-tag-target₂⊥ eq M⊒M′
  right-tag-target₂⊥ eq (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
    right-tag-target₂⊥ eq M⊒M′

  right-seal-target₁⊥ :
    ∀ {Δ σ γ M T r V A α} →
    T ≡ V ⟨ sealᶜ A α ⟩ →
    Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ r →
    ⊥
  right-seal-target₁⊥ eq (extend qᶜ pαᶜ M⊒T) =
    right-seal-target₁⊥ eq M⊒T
  right-seal-target₁⊥ eq (split qᶜ pαᶜ M⊒T) =
    right-seal-target₁⊥ eq M⊒T
  right-seal-target₁⊥ () (⊒blame pᶜ)
  right-seal-target₁⊥ () (x⊒x pᶜ x∋p)
  right-seal-target₁⊥ () (ƛ⊒ƛ p↦qᶜ N⊒N′)
  right-seal-target₁⊥ () (·⊒· qᶜ L⊒L′ M⊒M′)
  right-seal-target₁⊥ () (Λ⊒Λ allᶜ vV V⊒V′)
  right-seal-target₁⊥ () (⊒Λ pᶜ N⊒V′)
  right-seal-target₁⊥ eq
      (⊒⟨ν⟩ pᶜ i N⊒V′) =
    gen-not-seal (cast-coercion-injective eq)
  right-seal-target₁⊥ () (α⊒α qᶜ pαᶜ L⊒L′)
  right-seal-target₁⊥ () (⊒α pαᶜ L⊒L′)
  right-seal-target₁⊥ () (ν⊒ν pᶜ qᶜ N⊒N′)
  right-seal-target₁⊥ () (⊒ν pᶜ N⊒N′)
  right-seal-target₁⊥ eq (ν⊒ pᶜ N⊒N′) =
    right-seal-target₁⊥ (cong ⇑ᵗᵐ eq) N⊒N′
  right-seal-target₁⊥ () (κ⊒κ κ)
  right-seal-target₁⊥ () (⊕⊒⊕ M⊒M′ N⊒N′)
  right-seal-target₁⊥ eq
      (⊒cast+ qᶜ
        (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r)
        M⊒M′) =
    narrowing-dual-not-seal
      (proj₂ s⊒) (cast-coercion-injective eq)
  right-seal-target₁⊥ eq
      (⊒cast- qᶜ
        (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r)
        M⊒M′) =
    narrowing-not-seal
      (proj₂ s⊒) (cast-coercion-injective eq)
  right-seal-target₁⊥ eq (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
    right-seal-target₁⊥ eq M⊒M′
  right-seal-target₁⊥ eq (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
    right-seal-target₁⊥ eq M⊒M′

  right-seal-target₂⊥ :
    ∀ {Δ σ γ M T q V A α} →
    T ≡ V ⟨ unsealᶜ α A ⟩ →
    Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ q →
    ⊥
  right-seal-target₂⊥ eq (extend qᶜ pαᶜ M⊒T) =
    right-seal-target₂⊥ eq M⊒T
  right-seal-target₂⊥ eq (split qᶜ pαᶜ M⊒T) =
    right-seal-target₂⊥ eq M⊒T
  right-seal-target₂⊥ () (⊒blame pᶜ)
  right-seal-target₂⊥ () (x⊒x pᶜ x∋p)
  right-seal-target₂⊥ () (ƛ⊒ƛ p↦qᶜ N⊒N′)
  right-seal-target₂⊥ () (·⊒· qᶜ L⊒L′ M⊒M′)
  right-seal-target₂⊥ () (Λ⊒Λ allᶜ vV V⊒V′)
  right-seal-target₂⊥ () (⊒Λ pᶜ N⊒V′)
  right-seal-target₂⊥ eq
      (⊒⟨ν⟩ pᶜ i N⊒V′) =
    gen-not-unseal (cast-coercion-injective eq)
  right-seal-target₂⊥ () (α⊒α qᶜ pαᶜ L⊒L′)
  right-seal-target₂⊥ () (⊒α pαᶜ L⊒L′)
  right-seal-target₂⊥ () (ν⊒ν pᶜ qᶜ N⊒N′)
  right-seal-target₂⊥ () (⊒ν pᶜ N⊒N′)
  right-seal-target₂⊥ eq (ν⊒ pᶜ N⊒N′) =
    right-seal-target₂⊥ (cong ⇑ᵗᵐ eq) N⊒N′
  right-seal-target₂⊥ () (κ⊒κ κ)
  right-seal-target₂⊥ () (⊕⊒⊕ M⊒M′ N⊒N′)
  right-seal-target₂⊥ eq
      (⊒cast+ qᶜ
        (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r)
        M⊒M′) =
    narrowing-dual-not-unseal
      (proj₂ s⊒) (cast-coercion-injective eq)
  right-seal-target₂⊥ eq
      (⊒cast- qᶜ
        (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r)
        M⊒M′) =
    narrowing-not-unseal
      (proj₂ s⊒) (cast-coercion-injective eq)
  right-seal-target₂⊥ eq (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
    right-seal-target₂⊥ eq M⊒M′
  right-seal-target₂⊥ eq (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
    right-seal-target₂⊥ eq M⊒M′

------------------------------------------------------------------------
-- Public inversions
------------------------------------------------------------------------

right-tag-inversion₁ :
  ∀ {Δ σ γ M V q G} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ G !ᶜ ⟩ ∶ q →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ G ？ᶜ
right-tag-inversion₁ M⊒V! =
  ⊥-elim (right-tag-target₁⊥ refl M⊒V!)

right-tag-inversion₂ :
  ∀ {Δ σ γ M V r G} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ G ？ᶜ ⟩ ∶ r →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ id ★
right-tag-inversion₂ M⊒V? =
  ⊥-elim (right-tag-target₂⊥ refl M⊒V?)

right-seal-inversion₁ :
  ∀ {Δ σ γ M V r A α} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ sealᶜ A α ⟩ ∶ r →
  ∃[ q ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ q
right-seal-inversion₁ M⊒Vseal =
  ⊥-elim (right-seal-target₁⊥ refl M⊒Vseal)

right-seal-inversion₂ :
  ∀ {Δ σ γ M V q A α} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ unsealᶜ α A ⟩ ∶ q →
  ∃[ r ] Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ r
right-seal-inversion₂ M⊒Vunseal =
  ⊥-elim (right-seal-target₂⊥ refl M⊒Vunseal)
