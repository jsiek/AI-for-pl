{-# OPTIONS --safe #-}

module proof.DGG.SourceRebaseRequest where

-- File Charter:
--   * Defines the operational request carried by source reveal/conceal
--     boundaries in the two-context design.
--   * Separates no-pivot identity, a genuinely unmatched source pivot, and
--     a paired pivot whose structural move carries SourceRebasePlan.
--   * Interprets every request as a world and derives center/mark laws.
--     Paired soundness uses the request's direct store-entry relation, never
--     resolveVar or an invariant-derived representation.
--   * Primary exports are SourceRebaseRequest, sourceRebaseRequestWorld, and
--     sourceRebaseRequest-sound; SourceRebasePlan supplies paired movement.

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using (TyVar; ★)
open import TyStore using (lookupStore)
open import Consistency using (toRenameᵗ)
open import Imprecision using (X⊑X; X⊑★; extendᵐ)
open import CastTerms using (Ctx; Δᵉ; Σᵉ)
open import proof.DGG.World
open import proof.DGG.WorldInvariants
open import proof.DGG.SourceRebasePlan


private
  subst-Fin-suc-sym : ∀ {m n} (eq : m ≡ n) (X : Fin.Fin n)
    → subst Fin.Fin (sym (cong suc eq)) (Fin.suc X)
      ≡ Fin.suc (subst Fin.Fin (sym eq) X)
  subst-Fin-suc-sym refl X = refl

  subst-Fin-zero-sym : ∀ {m n} (eq : m ≡ n)
    → subst Fin.Fin (sym (cong suc eq)) Fin.zero ≡ Fin.zero
  subst-Fin-zero-sym refl = refl


rebaseSource-marks :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
    (Z : TyVar (centerᶜ W))
  → marksᶜ (rebaseSource plan)
      (subst Fin.Fin (sym (rebaseSource-center plan)) Z)
    ≡ marksᶜ W Z
rebaseSource-marks (source-rebase-id aligned) Z = refl
rebaseSource-marks
    (source-to-target Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★) Z =
  refl
rebaseSource-marks (source-rebase-skip plan) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-center plan) = refl
rebaseSource-marks (source-rebase-skip plan) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSource plan)))
      (subst-Fin-suc-sym (rebaseSource-center plan) Z))
    (rebaseSource-marks plan Z)
rebaseSource-marks
    (source-rebase-target plan fresh′ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-center plan) = refl
rebaseSource-marks
    (source-rebase-target plan fresh′ Γᴿ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSource plan)))
      (subst-Fin-suc-sym (rebaseSource-center plan) Z))
    (rebaseSource-marks plan Z)
rebaseSource-marks
    (source-rebase-lift-both {v = v} plan Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-center plan) = refl
rebaseSource-marks
    (source-rebase-lift-both {v = v} plan Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc Z) =
  trans
    (cong (extendᵐ v (marksᶜ (rebaseSource plan)))
      (subst-Fin-suc-sym (rebaseSource-center plan) Z))
    (rebaseSource-marks plan Z)
rebaseSource-marks
    (source-rebase-lift-left plan Γᴸ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-center plan) = refl
rebaseSource-marks
    (source-rebase-lift-left plan Γᴸ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSource plan)))
      (subst-Fin-suc-sym (rebaseSource-center plan) Z))
    (rebaseSource-marks plan Z)
rebaseSource-marks
    (source-rebase-bind-left plan Γᴸ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-center plan) = refl
rebaseSource-marks
    (source-rebase-bind-left plan Γᴸ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSource plan)))
      (subst-Fin-suc-sym (rebaseSource-center plan) Z))
    (rebaseSource-marks plan Z)
rebaseSource-marks
    (source-rebase-bind-term plan represented′) Z =
  rebaseSource-marks plan Z
rebaseSource-marks
    (source-rebase-bind-both
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-center plan) = refl
rebaseSource-marks
    (source-rebase-bind-both
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑X (marksᶜ (rebaseSource plan)))
      (subst-Fin-suc-sym (rebaseSource-center plan) Z))
    (rebaseSource-marks plan Z)
rebaseSource-marks
    (source-rebase-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-center plan) = refl
rebaseSource-marks
    (source-rebase-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSource plan)))
      (subst-Fin-suc-sym (rebaseSource-center plan) Z))
    (rebaseSource-marks plan Z)


data SourceRebaseRequest {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ) :
    Maybe (TyVar (Δᵉ Cᴸ)) → Maybe (TyVar (Δᵉ Cᴿ)) → Set where

  source-request-id :
      SourceRebaseRequest W nothing nothing

  source-request-only : ∀ {Xᴸ}
    → marksᶜ W (toRenameᵗ (ηᴸᶜ W) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ
        → toRenameᵗ (ηᴿᶜ W) Xᴿ
          ≢ toRenameᵗ (ηᴸᶜ W) Xᴸ)
    → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ⟨ W ⟩ ★
    → SourceRebaseRequest W (just Xᴸ) nothing

  source-request-paired : ∀ {Xᴸ Xᴿ}
    → (plan : SourceRebasePlan W Xᴸ Xᴿ)
    → lookupStore (Σᵉ Cᴸ) Xᴸ
        ⊑ᵀ⟨ rebaseSource plan ⟩
      lookupStore (Σᵉ Cᴿ) Xᴿ
    → SourceRebaseRequest W (just Xᴸ) (just Xᴿ)


sourceRebaseRequestWorld : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ? Xᴿ?}
  → SourceRebaseRequest W Xᴸ? Xᴿ?
  → Cᴸ ⊑ᶜ Cᴿ
sourceRebaseRequestWorld {W = W} source-request-id = W
sourceRebaseRequestWorld {W = W}
    (source-request-only mark disaligned represented) = W
sourceRebaseRequestWorld
    (source-request-paired plan represented) =
  rebaseSource plan


sourceRebaseRequest-center : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ? Xᴿ?}
    (request : SourceRebaseRequest W Xᴸ? Xᴿ?)
  → centerᶜ (sourceRebaseRequestWorld request) ≡ centerᶜ W
sourceRebaseRequest-center source-request-id = refl
sourceRebaseRequest-center
    (source-request-only mark disaligned represented) = refl
sourceRebaseRequest-center
    (source-request-paired plan represented) =
  rebaseSource-center plan


sourceRebaseRequest-marks : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ? Xᴿ?}
    (request : SourceRebaseRequest W Xᴸ? Xᴿ?)
    (Z : TyVar (centerᶜ W))
  → marksᶜ (sourceRebaseRequestWorld request)
      (subst Fin.Fin (sym (sourceRebaseRequest-center request)) Z)
    ≡ marksᶜ W Z
sourceRebaseRequest-marks source-request-id Z = refl
sourceRebaseRequest-marks
    (source-request-only mark disaligned represented) Z = refl
sourceRebaseRequest-marks
    (source-request-paired plan represented) Z =
  rebaseSource-marks plan Z


sourceRebaseRequestPlan : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
  → SourceRebaseRequest W (just Xᴸ) (just Xᴿ)
  → SourceRebasePlan W Xᴸ Xᴿ
sourceRebaseRequestPlan
    (source-request-paired plan represented) = plan


sourceRebaseRequest-sound : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (request : SourceRebaseRequest W (just Xᴸ) (just Xᴿ))
  → RebaseSourceᶜ W (sourceRebaseRequestWorld request) Xᴸ Xᴿ
sourceRebaseRequest-sound
    (source-request-paired plan represented) =
  rebase-sourceᶜ
    (rebaseSource-center plan)
    (rebaseSource-ηᴸ-off plan)
    (rebaseSource-ηᴿ-frozen plan)
    (rebaseSource-pivot-aligned plan)
    represented
