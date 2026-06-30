{-# OPTIONS --allow-unsolved-metas #-}

module proof.RightSealInversion2 where

-- File Charter:
--   * Attempts to prove the cambridge25 Right Seal Inversion 2 lemma.
--   * The theorem keeps the composition equation in the conclusion: stripping
--     a right `unseal α A` produces both a witness coercion and evidence that
--     the original index composes with `seal A α`.
--   * The direct `⊒cast+` seal case is immediate.  The remaining holes record
--     the proof obligations that arise from store-shaping and left-cast cases.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)

open import Types
open import Coercions
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import proof.CoercionProperties using (coercion-src-tgtᵐ)

RightSealInversion2 : Set₁
RightSealInversion2 =
  ∀ {Δ σ γ M V q A α} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ⟨ unseal α A ⟩ ∶ q →
  ∃[ r ]
    (Δ ∣ σ ⊢ q ⨾ⁿ seal A α ≈ r ∶ src q ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ r

right-seal-compose-endpoints :
  ∀ {Δ σ q r A B A₀ α} →
  Δ ∣ σ ⊢ q ⨾ⁿ seal A₀ α ≈ r ∶ A ⊒ B →
  Δ ∣ σ ⊢ q ⨾ⁿ seal A₀ α ≈ r ∶ src q ⊒ ＇ α
right-seal-compose-endpoints
    (compose-leftⁿ wfΣ q⊒ seal⊒
      (endpointsⁿ src-u tgt-u src-r tgt-r σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒))
    rewrite proj₁ (coercion-src-tgtᵐ (proj₁ q⊒))
          | proj₂ (coercion-src-tgtᵐ (proj₁ seal⊒)) =
  compose-leftⁿ wfΣ q⊒ seal⊒
    (endpointsⁿ src-u tgt-u src-r tgt-r σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒)

rightSealInversion2-cast+ :
  ∀ {Δ σ γ M M′ V q r s A B C D A₀ α} →
  M′ ⟨ - s ⟩ ≡ V ⟨ unseal α A₀ ⟩ →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r →
  ∃[ u ]
    (Δ ∣ σ ⊢ q ⨾ⁿ seal A₀ α ≈ u ∶ src q ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ u
rightSealInversion2-cast+ {s = id A} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = c ︔ d} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = c ↦ d} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = `∀ c} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = G !} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = G ？} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = seal A α} refl
    qᶜ q⨟seal≈r M⊒V =
  _ , right-seal-compose-endpoints q⨟seal≈r , M⊒V
rightSealInversion2-cast+ {s = unseal α A} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = gen A c} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast+ {s = inst B c} ()
    qᶜ q⨟s≈r M⊒M′

rightSealInversion2-cast- :
  ∀ {Δ σ γ M M′ V q r s A B C D A₀ α} →
  M′ ⟨ s ⟩ ≡ V ⟨ unseal α A₀ ⟩ →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q →
  ∃[ u ]
    (Δ ∣ σ ⊢ r ⨾ⁿ seal A₀ α ≈ u ∶ src r ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ u
rightSealInversion2-cast- {s = id A} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = c ︔ d} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = c ↦ d} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = `∀ c} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = G !} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = G ？} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = seal A α} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = unseal α A} refl
    qᶜ
    (compose-leftⁿ wfΣ q⊒ (cast-unseal hA α∈Σ ok , cross ())
      q⨟s≈r)
    M⊒M′
rightSealInversion2-cast- {s = gen A c} ()
    qᶜ q⨟s≈r M⊒M′
rightSealInversion2-cast- {s = inst B c} ()
    qᶜ q⨟s≈r M⊒M′

rightSealInversion2-aux :
  ∀ {Δ σ γ M T V q A α} →
  T ≡ V ⟨ unseal α A ⟩ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ q →
  ∃[ r ]
    (Δ ∣ σ ⊢ q ⨾ⁿ seal A α ≈ r ∶ src q ⊒ ＇ α) ×
    Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ r
-- Store/context-shaping cases: the right term is exposed only after
-- type-variable substitution.  The proof should recurse below the store
-- transformation and then transport both the composition equation and the term
-- narrowing witness back through the same substitution.
rightSealInversion2-aux eq (extend qᶜ pαᶜ M⊒T) = {!!}
rightSealInversion2-aux eq (split qᶜ pαᶜ M⊒T) = {!!}
rightSealInversion2-aux () (⊒blame pᶜ)
rightSealInversion2-aux () (x⊒x pᶜ x∋p)
rightSealInversion2-aux () (ƛ⊒ƛ p↦qᶜ N⊒N′)
rightSealInversion2-aux () (·⊒· qᶜ L⊒L′ M⊒M′)
rightSealInversion2-aux () (Λ⊒Λ allᶜ vV V⊒V′)
rightSealInversion2-aux () (⊒Λ pᶜ N⊒V′)
rightSealInversion2-aux () (⊒⟨ν⟩ pᶜ sᵢ N⊒V′)
rightSealInversion2-aux () (α⊒α qᶜ pαᶜ L⊒L′)
rightSealInversion2-aux () (⊒α pαᶜ L⊒L′)
rightSealInversion2-aux () (ν⊒ν pᶜ qᶜ N⊒N′)
rightSealInversion2-aux () (⊒ν pᶜ N⊒N′)
-- The `ν⊒` case is a left wrapper: the right term is unconstrained, so
-- the proof should recurse under `⇑ᵗᵐ` and then rebuild `ν⊒`.  The attempted
-- recursive call produces a shifted composition
-- `⇑ᶜ p ⨾ⁿ seal (⇑ᵗ A) (suc α) ≈ r`; rebuilding needs an unshifting
-- lemma that factors this through a witness for `p ⨾ⁿ seal A α`.
rightSealInversion2-aux eq (ν⊒ pᶜ N⊒N′) = {!!}
rightSealInversion2-aux () (κ⊒κ κ)
rightSealInversion2-aux () (⊕⊒⊕ M⊒M′ N⊒N′)
-- Direct right-positive seal cast.  Here the syntax of `- (seal A α)` is
-- exactly `unseal α A`, so the constructor already carries the desired
-- composition evidence and the stripped premise.
-- Other right-positive casts can only reach `V ⟨ unseal α A ⟩` when the
-- dual of their cast is definitionally an unseal.  The non-seal cases are
-- expected to be syntactically impossible; they are left split out while the
-- exact dual-action refinements are worked through.
rightSealInversion2-aux eq (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  rightSealInversion2-cast+ eq qᶜ q⨟s≈r M⊒M′
-- Right-negative casts would require the cast itself to be `unseal α A`, but
-- the composition side condition classifies that cast as a narrowing.  Since
-- `unseal` is a widening constructor, the main branch should close by the
-- impossible narrowing evidence.
rightSealInversion2-aux eq (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  rightSealInversion2-cast- eq qᶜ q⨟s≈r M⊒M′
-- Left cast cases recurse on the premise.  After the recursive inversion, the
-- first missing algebra is an associativity/factoring lemma for narrowing
-- composition:
--
--   r ≈ t ⨾ⁿ p
--   r ⨾ⁿ seal A α ≈ u
--   --------------------
--   ∃[ v ] p ⨾ⁿ seal A α ≈ v × u ≈ t ⨾ⁿ v
--
-- The direct rebuild attempt then hits a second obligation: `cast+⊒` and
-- `cast-⊒` require the premise index to be cast-like (`∶ᶜ`), but the
-- recursive inversion only returns a term relation at the composed witness.
-- A complete proof needs either a strengthened IH that also returns enough
-- typing for the witness, or a derived left-cast transport lemma that produces
-- the stripped term relation without exposing that `∶ᶜ` requirement at the
-- call site.
rightSealInversion2-aux eq (cast+⊒ pᶜ r≈t⨟p M⊒M′) = {!!}
rightSealInversion2-aux eq (cast-⊒ pᶜ r≈t⨟p M⊒M′) = {!!}

rightSealInversion2 : RightSealInversion2
rightSealInversion2 M⊒Vunseal =
  rightSealInversion2-aux refl M⊒Vunseal

right-seal-inversion₂ : RightSealInversion2
right-seal-inversion₂ = rightSealInversion2
