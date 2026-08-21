{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxSourceRebaseProducerProbe where

-- File Charter:
--   * Checks the operational request carried by source reveal/conceal
--     boundaries in the two-Ctx design.
--   * Separates no-pivot identity, a genuinely unmatched source pivot, and
--     a paired pivot whose structural move carries SourceRebasePlanᶜ₀.
--   * Interprets every request into a world and derives center/mark laws.
--     Paired soundness uses the request's direct store-entry relation, never
--     resolveVar or an invariant-derived representation.

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; zero)
open import Data.Sum using (inj₁)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using (TyVar; ★; ‵_; `ℕ)
open import TyStore using (lookupStore; store-empty)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open I using (X⊑X; X⊑★; extendᵐ)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; _,ˢ_)
open import proof.DGG.TwoCtxWorld
open import proof.DGG.TwoCtxWorldInvariants
open import proof.DGG.notes.probes.TwoCtxSourceRebasePlanProbe


private
  subst-Fin-suc-sym : ∀ {m n} (eq : m ≡ n) (X : Fin.Fin n)
    → subst Fin.Fin (sym (cong suc eq)) (Fin.suc X)
      ≡ Fin.suc (subst Fin.Fin (sym eq) X)
  subst-Fin-suc-sym refl X = refl

  subst-Fin-zero-sym : ∀ {m n} (eq : m ≡ n)
    → subst Fin.Fin (sym (cong suc eq)) Fin.zero ≡ Fin.zero
  subst-Fin-zero-sym refl = refl


rebaseSource-marksᶜ₀ :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlanᶜ₀ W Xᴸ Xᴿ)
    (Z : TyVar (centerᶜ W))
  → marksᶜ (rebaseSourceᶜ₀ plan)
      (subst Fin.Fin (sym (rebaseSource-centerᶜ₀ plan)) Z)
    ≡ marksᶜ W Z
rebaseSource-marksᶜ₀ (source-rebase-idᶜ₀ aligned) Z = refl
rebaseSource-marksᶜ₀
    (source-to-targetᶜ₀ Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★) Z =
  refl
rebaseSource-marksᶜ₀ (source-rebase-skipᶜ₀ plan) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-centerᶜ₀ plan) = refl
rebaseSource-marksᶜ₀ (source-rebase-skipᶜ₀ plan) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSourceᶜ₀ plan)))
      (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan) Z))
    (rebaseSource-marksᶜ₀ plan Z)
rebaseSource-marksᶜ₀
    (source-rebase-targetᶜ₀ plan fresh′ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-centerᶜ₀ plan) = refl
rebaseSource-marksᶜ₀
    (source-rebase-targetᶜ₀ plan fresh′ Γᴿ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSourceᶜ₀ plan)))
      (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan) Z))
    (rebaseSource-marksᶜ₀ plan Z)
rebaseSource-marksᶜ₀
    (source-rebase-lift-bothᶜ₀ {v = v} plan Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-centerᶜ₀ plan) = refl
rebaseSource-marksᶜ₀
    (source-rebase-lift-bothᶜ₀ {v = v} plan Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc Z) =
  trans
    (cong (extendᵐ v (marksᶜ (rebaseSourceᶜ₀ plan)))
      (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan) Z))
    (rebaseSource-marksᶜ₀ plan Z)
rebaseSource-marksᶜ₀
    (source-rebase-lift-leftᶜ₀ plan Γᴸ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-centerᶜ₀ plan) = refl
rebaseSource-marksᶜ₀
    (source-rebase-lift-leftᶜ₀ plan Γᴸ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSourceᶜ₀ plan)))
      (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan) Z))
    (rebaseSource-marksᶜ₀ plan Z)
rebaseSource-marksᶜ₀
    (source-rebase-bind-leftᶜ₀ plan Γᴸ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-centerᶜ₀ plan) = refl
rebaseSource-marksᶜ₀
    (source-rebase-bind-leftᶜ₀ plan Γᴸ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSourceᶜ₀ plan)))
      (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan) Z))
    (rebaseSource-marksᶜ₀ plan Z)
rebaseSource-marksᶜ₀
    (source-rebase-bind-termᶜ₀ plan represented′) Z =
  rebaseSource-marksᶜ₀ plan Z
rebaseSource-marksᶜ₀
    (source-rebase-bind-bothᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-centerᶜ₀ plan) = refl
rebaseSource-marksᶜ₀
    (source-rebase-bind-bothᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑X (marksᶜ (rebaseSourceᶜ₀ plan)))
      (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan) Z))
    (rebaseSource-marksᶜ₀ plan Z)
rebaseSource-marksᶜ₀
    (source-rebase-bind-both-starᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero-sym (rebaseSource-centerᶜ₀ plan) = refl
rebaseSource-marksᶜ₀
    (source-rebase-bind-both-starᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (rebaseSourceᶜ₀ plan)))
      (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan) Z))
    (rebaseSource-marksᶜ₀ plan Z)


data SourceRebaseRequestᶜ₀ {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ) :
    Maybe (TyVar (Δᵉ Cᴸ)) → Maybe (TyVar (Δᵉ Cᴿ)) → Set where

  source-request-idᶜ₀ :
      SourceRebaseRequestᶜ₀ W nothing nothing

  source-request-onlyᶜ₀ : ∀ {Xᴸ}
    → marksᶜ W (toRenameᵗ (ηᴸᶜ W) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ
        → toRenameᵗ (ηᴿᶜ W) Xᴿ
          ≢ toRenameᵗ (ηᴸᶜ W) Xᴸ)
    → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ⟨ W ⟩ ★
    → SourceRebaseRequestᶜ₀ W (just Xᴸ) nothing

  source-request-pairedᶜ₀ : ∀ {Xᴸ Xᴿ}
    → (plan : SourceRebasePlanᶜ₀ W Xᴸ Xᴿ)
    → lookupStore (Σᵉ Cᴸ) Xᴸ
        ⊑ᵀ⟨ rebaseSourceᶜ₀ plan ⟩
      lookupStore (Σᵉ Cᴿ) Xᴿ
    → SourceRebaseRequestᶜ₀ W (just Xᴸ) (just Xᴿ)


sourceRebaseRequestWorldᶜ₀ : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ? Xᴿ?}
  → SourceRebaseRequestᶜ₀ W Xᴸ? Xᴿ?
  → Cᴸ ⊑ᶜ Cᴿ
sourceRebaseRequestWorldᶜ₀ {W = W} source-request-idᶜ₀ = W
sourceRebaseRequestWorldᶜ₀ {W = W}
    (source-request-onlyᶜ₀ mark disaligned represented) = W
sourceRebaseRequestWorldᶜ₀
    (source-request-pairedᶜ₀ plan represented) =
  rebaseSourceᶜ₀ plan


sourceRebaseRequest-centerᶜ₀ : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ? Xᴿ?}
    (request : SourceRebaseRequestᶜ₀ W Xᴸ? Xᴿ?)
  → centerᶜ (sourceRebaseRequestWorldᶜ₀ request) ≡ centerᶜ W
sourceRebaseRequest-centerᶜ₀ source-request-idᶜ₀ = refl
sourceRebaseRequest-centerᶜ₀
    (source-request-onlyᶜ₀ mark disaligned represented) = refl
sourceRebaseRequest-centerᶜ₀
    (source-request-pairedᶜ₀ plan represented) =
  rebaseSource-centerᶜ₀ plan


sourceRebaseRequest-marksᶜ₀ : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ? Xᴿ?}
    (request : SourceRebaseRequestᶜ₀ W Xᴸ? Xᴿ?)
    (Z : TyVar (centerᶜ W))
  → marksᶜ (sourceRebaseRequestWorldᶜ₀ request)
      (subst Fin.Fin (sym (sourceRebaseRequest-centerᶜ₀ request)) Z)
    ≡ marksᶜ W Z
sourceRebaseRequest-marksᶜ₀ source-request-idᶜ₀ Z = refl
sourceRebaseRequest-marksᶜ₀
    (source-request-onlyᶜ₀ mark disaligned represented) Z = refl
sourceRebaseRequest-marksᶜ₀
    (source-request-pairedᶜ₀ plan represented) Z =
  rebaseSource-marksᶜ₀ plan Z


sourceRebaseRequestPlanᶜ₀ : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
  → SourceRebaseRequestᶜ₀ W (just Xᴸ) (just Xᴿ)
  → SourceRebasePlanᶜ₀ W Xᴸ Xᴿ
sourceRebaseRequestPlanᶜ₀
    (source-request-pairedᶜ₀ plan represented) = plan


sourceRebaseRequest-soundᶜ₀ : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (request : SourceRebaseRequestᶜ₀ W (just Xᴸ) (just Xᴿ))
  → RebaseSourceᶜ W (sourceRebaseRequestWorldᶜ₀ request) Xᴸ Xᴿ
sourceRebaseRequest-soundᶜ₀
    (source-request-pairedᶜ₀ plan represented) =
  rebase-sourceᶜ
    (rebaseSource-centerᶜ₀ plan)
    (rebaseSource-ηᴸ-offᶜ₀ plan)
    (rebaseSource-ηᴿ-frozenᶜ₀ plan)
    (rebaseSource-pivot-alignedᶜ₀ plan)
    represented


-- Concrete operational requests.

empty-context : Ctx
empty-context = ⟨ zero , store-empty , [] ⟩

identity-request :
    SourceRebaseRequestᶜ₀ emptyᶜ nothing nothing
identity-request = source-request-idᶜ₀

unmatched-source-world :
    (empty-context ,ˢ (‵ `ℕ)) ⊑ᶜ empty-context
unmatched-source-world = bindLeftᶜ emptyᶜ (‵ `ℕ)

unmatched-source-request :
    SourceRebaseRequestᶜ₀ unmatched-source-world
      (just Fin.zero) nothing
unmatched-source-request =
  source-request-onlyᶜ₀ refl (λ ()) I.ι⊑★

separated-pivots-world :
    (empty-context ,ˢ (‵ `ℕ)) ⊑ᶜ (empty-context ,ˢ ★)
separated-pivots-world =
  bindRightᶜ unmatched-source-world ★ (inj₁ refl)

paired-move-plan :
    SourceRebasePlanᶜ₀ separated-pivots-world Fin.zero Fin.zero
paired-move-plan =
  source-to-targetᶜ₀ refl refl (inj₁ refl) I.ι⊑★ (λ ())

paired-move-request :
    SourceRebaseRequestᶜ₀ separated-pivots-world
      (just Fin.zero) (just Fin.zero)
paired-move-request =
  source-request-pairedᶜ₀ paired-move-plan I.ι⊑★


-- The live optional boundary supplies the three-way pivot classification.
-- Its unmatched and paired cases currently relate `resolveVar` results, not
-- the direct lookup entries required here.  A direct-entry premise must
-- therefore be produced at the boundary; it cannot be recovered without the
-- forbidden resolver or an invariant injection.  After that repair, a genuine
-- paired move additionally needs `SourceRebasePlanᶜ₀ W Xᴸ Xᴿ`.  This raw
-- history is not recoverable from RebaseAt's extensional equalities either, so
-- it too must be carried when a moving paired boundary is created.
