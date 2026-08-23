module proof.LR-narrow.Universal where

-- File Charter:
--   * Constructs related universal values from their elimination obligations.
--   * Constructs those obligations from a binder-specific body relation.
--   * Reconstructs one-sided universal types from left-lifted body types.
--   * Converts ordinary related universal computations to target phases.
--   * Derives endpoint typing from symmetric universal term imprecision.
--   * Keeps evaluator and endpoint proof details out of the public module.

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import CastTerms
open import proof.LR-narrow.TermSubstitution using (subst-cong)
open import proof.TypeInTermSubst using (rename-occurs; toRename-keep-eq)
import Consistency
import Imprecision as I
import proof.Imprecision as PI
import proof.ImprecisionConsistency as IC
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
import proof.DGG.CastTermImprecision2Typing as CTIT
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
open import LR-narrow.ImmediateReturn
open import LR-narrow.TargetEvaluation
open import LR-narrow.TypeBetaExpansion using
  (paired-step; precise-step; related-type-beta-expand;
   related-precise-type-beta-expand)
import proof.LR-narrow.Closure as ClosureProof
import proof.LR-narrow.ClosingSubstitution as ClosingProof

universal-body-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty (suc Δᴵ)}
  → Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldBoth I.X⊑X (forgetWorld W) ⟩ Aᴵ
  → I.extᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W)))) Aᴾ
      ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W)))) Aᴵ
universal-body-imprecision {W = W} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p =
  subst≡ (λ L → I.extᵐ (impEnv (core W)) I.⊢ L ⊑ right)
    precise-eq
    (subst≡
      (λ R → I.extᵐ (impEnv (core W)) I.⊢
        CTI.embedᴸ (CTI.liftWorldBoth I.X⊑X (forgetWorld W)) Aᴾ ⊑ R)
      imprecise-eq p)
  where
  right = renameᵗ (extᵗ (Consistency.toRenameᵗ
    (impreciseEmbedding (core W)))) Aᴵ

  precise-eq : CTI.embedᴸ
      (CTI.liftWorldBoth I.X⊑X (forgetWorld W)) Aᴾ
      ≡ renameᵗ (extᵗ (Consistency.toRenameᵗ
          (preciseEmbedding (core W)))) Aᴾ
  precise-eq = renameᵗ-cong Aᴾ
    (toRename-keep-eq (preciseEmbedding (core W)))

  imprecise-eq : CTI.embedᴿ
      (CTI.liftWorldBoth I.X⊑X (forgetWorld W)) Aᴵ ≡ right
  imprecise-eq = renameᵗ-cong Aᴵ
    (toRename-keep-eq (impreciseEmbedding (core W)))

right-universal-body-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty Δᴵ}
  → Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Aᴵ
  → I.instᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W)))) Aᴾ
      ⊑ ⇑ᵗ (embedImprecise (core W) Aᴵ)
right-universal-body-imprecision {W = W} {Aᴾ = Aᴾ}
    {Aᴵ = Aᴵ} p =
  subst≡ (λ L → I.instᵐ (impEnv (core W)) I.⊢ L ⊑ right)
    precise-eq
    (subst≡
      (λ R → I.instᵐ (impEnv (core W)) I.⊢
        CTI.embedᴸ (CTI.liftWorldLeft I.X⊑★ (forgetWorld W)) Aᴾ ⊑ R)
      imprecise-eq p)
  where
  right = ⇑ᵗ (embedImprecise (core W) Aᴵ)

  precise-eq : CTI.embedᴸ
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W)) Aᴾ
      ≡ renameᵗ (extᵗ (Consistency.toRenameᵗ
          (preciseEmbedding (core W)))) Aᴾ
  precise-eq = renameᵗ-cong Aᴾ
    (toRename-keep-eq (preciseEmbedding (core W)))

  imprecise-eq : CTI.embedᴿ
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W)) Aᴵ ≡ right
  imprecise-eq = renameᵗ-skip-eq
    (impreciseEmbedding (core W)) Aᴵ

right-universal-type-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty Δᴵ}
  → NonVar Aᴾ
  → Fin.zero ∈ᵗ Aᴾ
  → Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Aᴵ
  → `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
right-universal-type-from-body {W = W} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    nonvar occurs body-related =
  subst≡
    (λ L → impEnv (core W) I.⊢ `∀ L ⊑ embedImprecise (core W) Aᴵ)
    (renameᵗ-cong Aᴾ
      (toRename-keep-eq (preciseEmbedding (core W))))
    (I.∀⊑
      (renameNonVar
        (Consistency.toRenameᵗ
          (Consistency.keep (preciseEmbedding (core W)))) nonvar)
      (rename-occurs
        (Consistency.toRenameᵗ
          (Consistency.keep (preciseEmbedding (core W)))) occurs)
      (subst≡
        (λ R → I.instᵐ (impEnv (core W)) I.⊢
          renameᵗ
            (Consistency.toRenameᵗ
              (Consistency.keep (preciseEmbedding (core W)))) Aᴾ
            ⊑ R)
        (renameᵗ-skip-eq (impreciseEmbedding (core W)) Aᴵ)
        body-related))

universals-related-from-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Nᴾ : Term (suc Δᴾ)} {Nᴵ : Term (suc Δᴵ)}
  → Value Nᴾ
  → Value Nᴵ
  → (∀ i → i ≤ k →
      CompiledUniversalBodyRelation p Bᴾ Bᴵ i Γ Nᴾ Nᴵ)
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′ (compiledContext W Γ)))
      (j : ℕ)
  → j ≤ k
  → UniversalsRelated W′ (liftCenterBodyImprecision W≼W′ p)
      (liftPreciseBody W≼W′ Bᴾ) (liftImpreciseBody W≼W′ Bᴵ) j
      (close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ (Λ Nᴵ)))
      (close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (Λ Nᴾ)))
universals-related-from-body vNᴾ vNᴵ body-related W≼W′ γ zero
    j≤k = tt
universals-related-from-body {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {W = W} {k} {Γ} {p} {Bᴾ} {Bᴵ} {Nᴾ} {Nᴵ}
    vNᴾ vNᴵ body-related
    {W′ = W′} W≼W′ γ (suc j) sj≤k = head , tail
  where
  j≤k = ≤-trans (n≤1+n j) sj≤k

  tail = universals-related-from-body {p = p} vNᴾ vNᴵ body-related
    W≼W′ γ j j≤k

  head : ∀ {Δᴾ″ Δᴵ″ Δᶜ″}
      (W″ : World Δᴾ″ Δᴵ″ Δᶜ″)
      (W′≼W″ : Future W′ W″)
      (Rᴾ : Ty Δᴾ″) (Rᴵ : Ty Δᴵ″)
      (r : Rᴾ ⊑ᵂ⟨ core W″ ⟩ Rᴵ)
      (s : liftPreciseBody W′≼W″
            (liftPreciseBody W≼W′ Bᴾ) [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W″ ⟩
          liftImpreciseBody W′≼W″
            (liftImpreciseBody W≼W′ Bᴵ) [ Rᴵ ]ᵗ)
    → let tested = pairedBindWorld W″ Rᴾ Rᴵ r
          test-step = future-paired (future-refl {W = W″}) r
      in ComputationsRelated W″
          (PostBindValueRelation test-step s) (suc j)
          (liftImpreciseTerm W′≼W″
            (close (impreciseClosingSubstitution γ)
              (liftImpreciseTerm W≼W′ (Λ Nᴵ)))
            ⦂∀ liftImpreciseBody W′≼W″
              (liftImpreciseBody W≼W′ Bᴵ) [ Rᴵ ])
          (liftPreciseTerm W′≼W″
            (close (preciseClosingSubstitution γ)
              (liftPreciseTerm W≼W′ (Λ Nᴾ)))
            ⦂∀ liftPreciseBody W′≼W″
              (liftPreciseBody W≼W′ Bᴾ) [ Rᴾ ])
  head W″ W′≼W″ Rᴾ Rᴵ r s =
    ClosureProof.computations-related-post-bind-reindex
      s-composite s
      (cong (embedPrecise (core W″)) precise-result-trans)
      (cong (embedImprecise (core W″)) imprecise-result-trans)
      imprecise-redex-eq precise-redex-eq canonical
    where
    test-step = paired-step W″ r
    tested = pairedBindWorld W″ Rᴾ Rᴵ r
    W≼W″ = future-trans W≼W′ W′≼W″

    precise-result-trans = cong (λ C → C [ Rᴾ ]ᵗ)
      (liftPreciseBody-trans W≼W′ W′≼W″ Bᴾ)
    imprecise-result-trans = cong (λ C → C [ Rᴵ ]ᵗ)
      (liftImpreciseBody-trans W≼W′ W′≼W″ Bᴵ)

    s-composite = subst≡
      (λ L → L ⊑ᵂ⟨ core W″ ⟩
        liftImpreciseBody W≼W″ Bᴵ [ Rᴵ ]ᵗ)
      (sym precise-result-trans)
      (subst≡
        (λ R → liftPreciseBody W′≼W″
          (liftPreciseBody W≼W′ Bᴾ) [ Rᴾ ]ᵗ
          ⊑ᵂ⟨ core W″ ⟩ R)
        (sym imprecise-result-trans) s)
    γ-down = related-closing-downward j≤k γ
    γ-future = related-closing-future W′≼W″ γ-down
    γ-tail = related-closing-trans W≼W′ W′≼W″ γ-future

    γᴵ-tail = impreciseClosingSubstitution γ-tail
    γᴾ-tail = preciseClosingSubstitution γ-tail

    bodyᴵ = closeTypeBody γᴵ-tail
      (liftImpreciseBodyTerm W≼W″ Nᴵ)
    bodyᴾ = closeTypeBody γᴾ-tail
      (liftPreciseBodyTerm W≼W″ Nᴾ)

    vBodyᴵ = close-type-body-preserves-value γᴵ-tail
      (liftImpreciseBodyTerm-value W≼W″ vNᴵ)
    vBodyᴾ = close-type-body-preserves-value γᴾ-tail
      (liftPreciseBodyTerm-value W≼W″ vNᴾ)

    contract-related = body-related j j≤k W″ W≼W″ γ-tail
      Rᴾ Rᴵ r s-composite

    canonical = related-type-beta-expand
      {W = W″} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
      {r = r} {p = s-composite}
      {Bᴾ = liftPreciseBody W≼W″ Bᴾ}
      {Bᴵ = liftImpreciseBody W≼W″ Bᴵ}
      {Vᴾ = bodyᴾ} {Vᴵ = bodyᴵ}
      vBodyᴵ vBodyᴾ contract-related

    imprecise-tail-env-eq : ∀ x →
        closingSubstitution (imprecise-closing-future W′≼W″
          (impreciseClosingSubstitution γ)) x
        ≡ closingSubstitution γᴵ-tail x
    imprecise-tail-env-eq x =
      trans
        (ClosingProof.imprecise-closing-future-lookup W′≼W″
          (impreciseClosingSubstitution γ) x)
        (sym (trans
          (ClosingProof.imprecise-related-trans-lookup
            W≼W′ W′≼W″ γ-future x)
          (trans
            (ClosingProof.imprecise-related-future-lookup
              W′≼W″ γ-down x)
            (cong (liftImpreciseTerm W′≼W″)
              (ClosingProof.imprecise-related-downward-lookup
                j≤k γ x)))))

    precise-tail-env-eq : ∀ x →
        closingSubstitution (precise-closing-future W′≼W″
          (preciseClosingSubstitution γ)) x
        ≡ closingSubstitution γᴾ-tail x
    precise-tail-env-eq x =
      trans
        (ClosingProof.precise-closing-future-lookup W′≼W″
          (preciseClosingSubstitution γ) x)
        (sym (trans
          (ClosingProof.precise-related-trans-lookup
            W≼W′ W′≼W″ γ-future x)
          (trans
            (ClosingProof.precise-related-future-lookup
              W′≼W″ γ-down x)
            (cong (liftPreciseTerm W′≼W″)
              (ClosingProof.precise-related-downward-lookup
                j≤k γ x)))))

    imprecise-universal-eq : liftImpreciseTerm W′≼W″
        (close (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W≼W′ (Λ Nᴵ))) ≡ Λ bodyᴵ
    imprecise-universal-eq =
      trans
        (imprecise-close-future W′≼W″
          (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W≼W′ (Λ Nᴵ)))
        (trans
          (cong (close (imprecise-closing-future W′≼W″
            (impreciseClosingSubstitution γ)))
            (sym (liftImpreciseTerm-trans W≼W′ W′≼W″ (Λ Nᴵ))))
          (trans
            (subst-cong imprecise-tail-env-eq
              (liftImpreciseTerm W≼W″ (Λ Nᴵ)))
            (trans
              (cong (close γᴵ-tail)
                (liftImpreciseTerm-universal W≼W″ Nᴵ))
              (close-universal γᴵ-tail
                (liftImpreciseBodyTerm W≼W″ Nᴵ)))))

    precise-universal-eq : liftPreciseTerm W′≼W″
        (close (preciseClosingSubstitution γ)
          (liftPreciseTerm W≼W′ (Λ Nᴾ))) ≡ Λ bodyᴾ
    precise-universal-eq =
      trans
        (precise-close-future W′≼W″
          (preciseClosingSubstitution γ)
          (liftPreciseTerm W≼W′ (Λ Nᴾ)))
        (trans
          (cong (close (precise-closing-future W′≼W″
            (preciseClosingSubstitution γ)))
            (sym (liftPreciseTerm-trans W≼W′ W′≼W″ (Λ Nᴾ))))
          (trans
            (subst-cong precise-tail-env-eq
              (liftPreciseTerm W≼W″ (Λ Nᴾ)))
            (trans
              (cong (close γᴾ-tail)
                (liftPreciseTerm-universal W≼W″ Nᴾ))
              (close-universal γᴾ-tail
                (liftPreciseBodyTerm W≼W″ Nᴾ)))))

    imprecise-redex-eq = cong₂
      (λ F B → F ⦂∀ B [ Rᴵ ])
      (sym imprecise-universal-eq)
      (liftImpreciseBody-trans W≼W′ W′≼W″ Bᴵ)

    precise-redex-eq = cong₂
      (λ F B → F ⦂∀ B [ Rᴾ ])
      (sym precise-universal-eq)
      (liftPreciseBody-trans W≼W′ W′≼W″ Bᴾ)

right-universal-test-from-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k j : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Nᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → Value Nᴾ
  → CompiledRightUniversalTestRelation p Bᴾ Bᴵ j Γ Nᴾ Mᴵ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′ (compiledContext W Γ)))
  → j ≤ k
  → ∀ {Δᴾ″ Δᴵ″ Δᶜ″}
      (W″ : World Δᴾ″ Δᴵ″ Δᶜ″)
      (W′≼W″ : Future W′ W″)
      (Rᴾ : Ty Δᴾ″)
      (r★ : impEnv (core W″) I.⊢ embedPrecise (core W″) Rᴾ ⊑ ★)
      (s : liftPreciseBody W′≼W″
            (liftPreciseBody W≼W′ Bᴾ) [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W″ ⟩
          liftImpreciseTy W′≼W″
            (liftImpreciseTy W≼W′ Bᴵ))
  → ComputationsRelated W″
      (PostBindValueRelation (precise-step W″ r★) s) j
      (liftImpreciseTerm W′≼W″
        (close (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W≼W′ Mᴵ)))
      (liftPreciseTerm W′≼W″
        (close (preciseClosingSubstitution γ)
          (liftPreciseTerm W≼W′ (Λ Nᴾ)))
        ⦂∀ liftPreciseBody W′≼W″
          (liftPreciseBody W≼W′ Bᴾ) [ Rᴾ ])
right-universal-test-from-body {W = W} {k = k} {j = j}
    {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Nᴾ = Nᴾ} {Mᴵ = Mᴵ}
    vNᴾ body-related {W′ = W′} W≼W′ γ j≤k
    W″ W′≼W″ Rᴾ r★ s =
  ClosureProof.computations-related-post-bind-reindex
    s-composite s
    (cong (embedPrecise (core W″)) precise-result-trans)
    (cong (embedImprecise (core W″)) imprecise-result-trans)
    (sym imprecise-term-eq) precise-redex-eq canonical
  where
  W≼W″ = future-trans W≼W′ W′≼W″

  precise-result-trans = cong (λ C → C [ Rᴾ ]ᵗ)
    (liftPreciseBody-trans W≼W′ W′≼W″ Bᴾ)
  imprecise-result-trans =
    liftImpreciseTy-trans W≼W′ W′≼W″ Bᴵ

  s-composite = subst≡
    (λ L → L ⊑ᵂ⟨ core W″ ⟩ liftImpreciseTy W≼W″ Bᴵ)
    (sym precise-result-trans)
    (subst≡
      (λ R → liftPreciseBody W′≼W″
        (liftPreciseBody W≼W′ Bᴾ) [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W″ ⟩ R)
      (sym imprecise-result-trans) s)

  γ-down = related-closing-downward j≤k γ
  γ-future = related-closing-future W′≼W″ γ-down
  γ-tail = related-closing-trans W≼W′ W′≼W″ γ-future
  γᴵ-tail = impreciseClosingSubstitution γ-tail
  γᴾ-tail = preciseClosingSubstitution γ-tail

  bodyᴾ = closeTypeBody γᴾ-tail
    (liftPreciseBodyTerm W≼W″ Nᴾ)
  vBodyᴾ = close-type-body-preserves-value γᴾ-tail
    (liftPreciseBodyTerm-value W≼W″ vNᴾ)

  contract-related = body-related W″ W≼W″ γ-tail
    Rᴾ r★ s-composite

  canonical = related-precise-type-beta-expand
    {W = W″} {Rᴾ = Rᴾ} {p = s-composite}
    {Bᴾ = liftPreciseBody W≼W″ Bᴾ} {Vᴾ = bodyᴾ}
    vBodyᴾ contract-related

  imprecise-tail-env-eq : ∀ x →
      closingSubstitution (imprecise-closing-future W′≼W″
        (impreciseClosingSubstitution γ)) x
      ≡ closingSubstitution γᴵ-tail x
  imprecise-tail-env-eq x =
    trans
      (ClosingProof.imprecise-closing-future-lookup W′≼W″
        (impreciseClosingSubstitution γ) x)
      (sym (trans
        (ClosingProof.imprecise-related-trans-lookup
          W≼W′ W′≼W″ γ-future x)
        (trans
          (ClosingProof.imprecise-related-future-lookup
            W′≼W″ γ-down x)
          (cong (liftImpreciseTerm W′≼W″)
            (ClosingProof.imprecise-related-downward-lookup
              j≤k γ x)))))

  precise-tail-env-eq : ∀ x →
      closingSubstitution (precise-closing-future W′≼W″
        (preciseClosingSubstitution γ)) x
      ≡ closingSubstitution γᴾ-tail x
  precise-tail-env-eq x =
    trans
      (ClosingProof.precise-closing-future-lookup W′≼W″
        (preciseClosingSubstitution γ) x)
      (sym (trans
        (ClosingProof.precise-related-trans-lookup
          W≼W′ W′≼W″ γ-future x)
        (trans
          (ClosingProof.precise-related-future-lookup
            W′≼W″ γ-down x)
          (cong (liftPreciseTerm W′≼W″)
            (ClosingProof.precise-related-downward-lookup j≤k γ x)))))

  imprecise-term-eq : liftImpreciseTerm W′≼W″
      (close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ Mᴵ))
      ≡ close γᴵ-tail (liftImpreciseTerm W≼W″ Mᴵ)
  imprecise-term-eq =
    trans
      (imprecise-close-future W′≼W″
        (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ Mᴵ))
      (trans
        (cong (close (imprecise-closing-future W′≼W″
          (impreciseClosingSubstitution γ)))
          (sym (liftImpreciseTerm-trans W≼W′ W′≼W″ Mᴵ)))
        (subst-cong imprecise-tail-env-eq
          (liftImpreciseTerm W≼W″ Mᴵ)))

  precise-universal-eq : liftPreciseTerm W′≼W″
      (close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (Λ Nᴾ))) ≡ Λ bodyᴾ
  precise-universal-eq =
    trans
      (precise-close-future W′≼W″
        (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (Λ Nᴾ)))
      (trans
        (cong (close (precise-closing-future W′≼W″
          (preciseClosingSubstitution γ)))
          (sym (liftPreciseTerm-trans W≼W′ W′≼W″ (Λ Nᴾ))))
        (trans
          (subst-cong precise-tail-env-eq
            (liftPreciseTerm W≼W″ (Λ Nᴾ)))
          (trans
            (cong (close γᴾ-tail)
              (liftPreciseTerm-universal W≼W″ Nᴾ))
            (close-universal γᴾ-tail
              (liftPreciseBodyTerm W≼W″ Nᴾ)))))

  precise-redex-eq = cong₂
    (λ F B → F ⦂∀ B [ Rᴾ ])
    (sym precise-universal-eq)
    (liftPreciseBody-trans W≼W′ W′≼W″ Bᴾ)

right-universals-related-from-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Nᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → Value Nᴾ
  → (∀ i → i ≤ k →
      CompiledRightUniversalTestRelation {W = W}
        p Bᴾ Bᴵ i Γ Nᴾ Mᴵ)
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′ (compiledContext W Γ)))
      (j : ℕ)
  → j ≤ k
  → RightUniversalsRelated W′
      (liftCenterDynamicBodyImprecision W≼W′ p)
      (liftPreciseBody W≼W′ Bᴾ) (liftImpreciseTy W≼W′ Bᴵ) j
      (close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ Mᴵ))
      (close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (Λ Nᴾ)))
right-universals-related-from-body {W = W} {k = k} {p = p}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Nᴾ = Nᴾ} {Mᴵ = Mᴵ}
    vNᴾ body-related W≼W′ γ zero z≤k =
  right-universal-test-from-body
    {W = W} {k = k} {j = zero} {p = p}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Nᴾ = Nᴾ} {Mᴵ = Mᴵ}
    vNᴾ (body-related zero z≤k) W≼W′ γ z≤k
right-universals-related-from-body {W = W} {k = k} {p = p}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Nᴾ = Nᴾ} {Mᴵ = Mᴵ}
    vNᴾ body-related W≼W′ γ (suc j) sj≤k = head , tail
  where
  head = right-universal-test-from-body
    {W = W} {k = k} {j = suc j} {p = p}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Nᴾ = Nᴾ} {Mᴵ = Mᴵ}
    vNᴾ (body-related (suc j) sj≤k) W≼W′ γ sj≤k
  j≤k = ≤-trans (n≤1+n j) sj≤k
  tail = right-universals-related-from-body {W = W} {p = p}
    vNᴾ body-related W≼W′ γ j j≤k

right-universals-related-result-transport : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Aᴵ′}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {k Vᴵ Vᴾ}
    (eq : Aᴵ ≡ Aᴵ′)
    (p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
  → RightUniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W
      (subst≡ (λ R → I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ R)
        eq p)
      Bᴾ Bᴵ k Vᴵ Vᴾ
right-universals-related-result-transport refl p related = related

right-universal-body-phase-from-relation : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → Value Vᴾ
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Mᴵ
  → CompiledRightUniversalBodyRelation q k Γ Vᴾ Mᴵ
right-universal-body-phase-from-relation vVᴾ q term-related
    W′ W≼W′ γ =
  future-value-computations-target-phase precise-closed-value
    (term-related W′ W≼W′ γ)
  where
  precise-closed-value = close-preserves-value
    (preciseClosingSubstitution γ)
    (ClosureProof.precise-value-future W≼W′ (Λ vVᴾ))

right-universal-phase-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → Value Vᴾ
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → CompiledRightUniversalBodyRelation q k Γ Vᴾ Mᴵ
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Mᴵ
right-universal-phase-compatible vVᴾ q body-phase W′ W≼W′ γ =
  target-phase-computations-related precise-closed-value
    (body-phase W′ W≼W′ γ)
  where
  precise-closed-value = close-preserves-value
    (preciseClosingSubstitution γ)
    (ClosureProof.precise-value-future W≼W′ (Λ vVᴾ))

right-universal-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Mᴵ ⦂ Bᴵ
  → CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Mᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → CompiledRightUniversalBodyRelation q k Γ Vᴾ Mᴵ
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Mᴵ
right-universal-compatible-from-body {W = W} nonvar occurs liftΓ
    vVᴾ target⊢ body q body-phase =
  right-universal-phase-compatible vVᴾ q body-phase

right-universal-smart-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ Δᵐ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Wᵐ : CTI.World (suc Δᴾ) Δᴵ Δᵐ}
    {Γᵐ : CTI.CtxImp Wᵐ}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨ Wᵐ ⟩ Bᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (smart : CTI.SmartCommaLiftᴸ (forgetWorld W) Wᵐ)
  → (liftΓ : CTI.SmartLiftCtxᴸ Γ Γᵐ)
  → (vVᴾ : Value Vᴾ)
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Mᴵ ⦂ Bᴵ
  → Wᵐ ∣ Γᵐ ⊢² Vᴾ ⊑ Mᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → CompiledRightUniversalBodyRelation q k Γ Vᴾ Mᴵ
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Mᴵ
right-universal-smart-compatible-from-body nonvar occurs smart liftΓ
    vVᴾ target⊢ body q body-phase =
  right-universal-phase-compatible vVᴾ q body-phase

right-universal-value-related-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term Δᴵ}
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Vᴵ ⦂ Bᴵ
  → CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → (∀ i → i ≤ k → CompiledRightUniversalTestRelation {W = W}
      (right-universal-body-imprecision {W = W} p)
      Aᴾ Bᴵ i Γ Vᴾ Vᴵ)
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′ (compiledContext W Γ)))
      (j : ℕ)
  → j ≤ k
  → FutureValueRelation (liftCenterImprecision W≼W′ q)
      W′ future-refl j
      (close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ Vᴵ))
      (close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (Λ Vᴾ)))
right-universal-value-related-from-body {W = W} {k = k} {Γ = Γ}
    {Aᴾ = Aᴾ} {Bᴵ = Bᴵ} {p = p} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ}
    nonvar occurs liftΓ vVᴾ vVᴵ target⊢ body q body-related
    W′ W≼W′ γ j j≤k =
  related j j≤k
  where
  precise-γ = preciseClosingSubstitution γ
  imprecise-γ = impreciseClosingSubstitution γ

  precise-body-base =
    renameᵗ (extᵗ (Consistency.toRenameᵗ
      (preciseEmbedding (core W)))) Aᴾ

  imprecise-base = embedImprecise (core W) Bᴵ

  p-body : I.instᵐ (impEnv (core W)) I.⊢
      precise-body-base ⊑ ⇑ᵗ imprecise-base
  p-body = right-universal-body-imprecision {W = W} p

  embedded-nonvar : NonVar precise-body-base
  embedded-nonvar = renameNonVar
    (extᵗ (Consistency.toRenameᵗ (preciseEmbedding (core W))))
    nonvar

  embedded-occurs : Fin.zero ∈ᵗ precise-body-base
  embedded-occurs = rename-occurs
    (extᵗ (Consistency.toRenameᵗ (preciseEmbedding (core W))))
    occurs

  structural-base = I.∀⊑ embedded-nonvar embedded-occurs p-body

  universal-imprecision =
    CTIR.Λ⊑² nonvar occurs liftΓ vVᴾ target⊢ body q

  precise-universal-typing = precise-open-typing-future W≼W′
    (CTIT.source-typing² universal-imprecision)

  precise-universal-typing′ =
    subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
      (sym (compiled-precise-context-future W≼W′ Γ))
      precise-universal-typing

  imprecise-universal-typing = imprecise-open-typing-future W≼W′
    (CTIT.target-typing² universal-imprecision)

  imprecise-universal-typing′ =
    subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
      (sym (compiled-imprecise-context-future W≼W′ Γ))
      imprecise-universal-typing

  endpoints : TypedEndpoints W′ (liftCenterImprecision W≼W′ q)
      (close imprecise-γ (liftImpreciseTerm W≼W′ Vᴵ))
      (close precise-γ (liftPreciseTerm W≼W′ (Λ Vᴾ)))
  endpoints = typed-endpoints
    (liftImpreciseTy W≼W′ Bᴵ)
    (liftPreciseTy W≼W′ (`∀ Aᴾ))
    (embedImprecise-lift W≼W′ Bᴵ)
    (embedPrecise-lift W≼W′ (`∀ Aᴾ))
    (close-preserves-value imprecise-γ
      (ClosureProof.imprecise-value-future W≼W′ vVᴵ))
    (close-preserves-value precise-γ
      (ClosureProof.precise-value-future W≼W′ (Λ vVᴾ)))
    (close-preserves-typing imprecise-γ imprecise-universal-typing′)
    (close-preserves-typing precise-γ precise-universal-typing′)

  p-lifted = liftCenterDynamicBodyImprecision W≼W′ p-body

  p-structural = subst≡
    (λ R → I.instᵐ (impEnv (core W′)) I.⊢
      liftCenterBody W≼W′ precise-body-base ⊑ R)
    (liftCenterBody-shift W≼W′ imprecise-base) p-lifted

  structural = I.∀⊑
    (liftCenterBody-nonvar W≼W′ embedded-nonvar)
    (liftCenterBody-occurs W≼W′ embedded-occurs)
    p-structural

  precise-body-eq = trans
    (cong (embedPrecise (core W′))
      (sym (liftPreciseTy-universal W≼W′ Aᴾ)))
    (trans (embedPrecise-lift W≼W′ (`∀ Aᴾ))
      (liftCenterTy-universal W≼W′ precise-body-base))

  imprecise-body-eq = embedImprecise-lift W≼W′ Bᴵ

  explicit-endpoints : TypedEndpoints W′ structural
      (close imprecise-γ (liftImpreciseTerm W≼W′ Vᴵ))
      (close precise-γ (liftPreciseTerm W≼W′ (Λ Vᴾ)))
  explicit-endpoints = typed-endpoints
    (impreciseType endpoints) (preciseType endpoints)
    (impreciseEmbedded endpoints)
    (trans (preciseEmbedded endpoints)
      (liftCenterTy-universal W≼W′ precise-body-base))
    (imprecise-value endpoints) (precise-value endpoints)
    (imprecise-typed endpoints) (precise-typed endpoints)

  related : ∀ j → j ≤ k →
      FutureValueRelation (liftCenterImprecision W≼W′ q)
        W′ future-refl j
        (close imprecise-γ (liftImpreciseTerm W≼W′ Vᴵ))
        (close precise-γ (liftPreciseTerm W≼W′ (Λ Vᴾ)))
  related zero j≤k = ClosureProof.value-imprecision-reindex
    (liftCenterImprecision W≼W′ q) structural
    (liftCenterTy-universal W≼W′ precise-body-base) refl
    (explicit-endpoints ,
      liftPreciseBody W≼W′ Aᴾ , liftImpreciseTy W≼W′ Bᴵ ,
      precise-body-eq , imprecise-body-eq ,
      (λ {Δᴾ′} {Δᴵ′} {Δᶜ′} K W′≼K Rᴾ r★ s →
        right-universals-related-result-transport
          (liftCenterBody-shift W≼W′ imprecise-base) p-lifted
          (λ {Δᴾ″} {Δᴵ″} {Δᶜ″} J W′≼J Sᴾ r★′ t →
            right-universals-related-from-body
              {W = W} {k = k} {p = p-body}
              {Bᴾ = Aᴾ} {Bᴵ = Bᴵ} {Nᴾ = Vᴾ} {Mᴵ = Vᴵ}
              vVᴾ body-related {W′ = W′} W≼W′ γ zero j≤k
              {Δᴾ″} {Δᴵ″} {Δᶜ″} J W′≼J Sᴾ r★′ t)
          {Δᴾ′} {Δᴵ′} {Δᶜ′} K W′≼K Rᴾ r★ s))
  related (suc j) sj≤k = ClosureProof.value-imprecision-reindex
    (liftCenterImprecision W≼W′ q) structural
    (liftCenterTy-universal W≼W′ precise-body-base) refl
    (explicit-endpoints ,
      liftPreciseBody W≼W′ Aᴾ , liftImpreciseTy W≼W′ Bᴵ ,
      precise-body-eq , imprecise-body-eq ,
      right-universals-related-result-transport
        (liftCenterBody-shift W≼W′ imprecise-base) p-lifted
        (right-universals-related-from-body
          {W = W} {k = k} {p = p-body}
          {Bᴾ = Aᴾ} {Bᴵ = Bᴵ} {Nᴾ = Vᴾ} {Mᴵ = Vᴵ}
          vVᴾ body-related {W′ = W′} W≼W′ γ (suc j) sj≤k))

right-universal-value-phase-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term Δᴵ}
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Vᴵ ⦂ Bᴵ
  → CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → (∀ i → i ≤ k → CompiledRightUniversalTestRelation {W = W}
      (right-universal-body-imprecision {W = W} p)
      Aᴾ Bᴵ i Γ Vᴾ Vᴵ)
  → CompiledRightUniversalBodyRelation
      {W = W} {Bᴾ = Aᴾ} {Bᴵ = Bᴵ} q k Γ Vᴾ Vᴵ
right-universal-value-phase-from-body {W = W} {k = k} {Γ = Γ}
    {Vᴵ = Vᴵ} nonvar occurs liftΓ vVᴾ vVᴵ target⊢ body q
    body-related W′ W≼W′ γ =
  related-target-value-phase imprecise-closed-value
    (λ j j≤k → right-universal-value-related-from-body
      {W = W} nonvar occurs liftΓ vVᴾ vVᴵ target⊢ body q body-related
      W′ W≼W′ γ j j≤k)
  where
  imprecise-closed-value = close-preserves-value
    (impreciseClosingSubstitution γ)
    (ClosureProof.imprecise-value-future W≼W′ vVᴵ)

right-universal-value-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term Δᴵ}
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Vᴵ ⦂ Bᴵ
  → CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → (∀ i → i ≤ k → CompiledRightUniversalTestRelation {W = W}
      (right-universal-body-imprecision {W = W} p)
      Aᴾ Bᴵ i Γ Vᴾ Vᴵ)
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Vᴵ
right-universal-value-compatible-from-body {W = W} nonvar occurs liftΓ
    vVᴾ vVᴵ target⊢ body q body-related =
  right-universal-phase-compatible {W = W} vVᴾ q
    (right-universal-value-phase-from-body {W = W} nonvar occurs liftΓ
      vVᴾ vVᴵ target⊢ body q body-related)

universal-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty (suc Δᴵ)}
    {p : Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldBoth I.X⊑X (forgetWorld W) ⟩ Aᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldBoth I.X⊑X (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
  → (liftΓ : CTI.LiftCtx I.X⊑X Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → CTI.liftWorldBoth I.X⊑X (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ `∀ Aᴵ)
  → (∀
      (q-body : I.extᵐ (impEnv (core W)) I.⊢
        renameᵗ (extᵗ (Consistency.toRenameᵗ
          (preciseEmbedding (core W)))) Aᴾ
        ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
          (impreciseEmbedding (core W)))) Aᴵ)
      → q ≡ I.∀⊑∀ q-body
      → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
          (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
          (W≼W′ : Future W W′)
          (γ : RelatedClosingSubstitutions W′ k
            (liftContextImprecision W≼W′ (compiledContext W Γ)))
          (j : ℕ)
      → j ≤ k
      → UniversalsRelated W′
          (liftCenterBodyImprecision W≼W′ q-body)
          (liftPreciseBody W≼W′ Aᴾ)
          (liftImpreciseBody W≼W′ Aᴵ) j
          (close (impreciseClosingSubstitution γ)
            (liftImpreciseTerm W≼W′ (Λ Vᴵ)))
          (close (preciseClosingSubstitution γ)
            (liftPreciseTerm W≼W′ (Λ Vᴾ))))
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) (Λ Vᴵ)
universal-compatible {W = W} {k = k} {Γ = Γ}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {p = p}
    {Vᴾ = Vᴾ} {Vᴵ = Vᴵ}
    liftΓ vVᴾ vVᴵ body q universals W′ W≼W′ γ =
  related-values-return (imprecise-value endpoints)
    (precise-value endpoints) related
  where
  precise-γ = preciseClosingSubstitution γ
  imprecise-γ = impreciseClosingSubstitution γ

  precise-body-base =
    renameᵗ (extᵗ (Consistency.toRenameᵗ
      (preciseEmbedding (core W)))) Aᴾ

  imprecise-body-base =
    renameᵗ (extᵗ (Consistency.toRenameᵗ
      (impreciseEmbedding (core W)))) Aᴵ

  p-body : I.extᵐ (impEnv (core W)) I.⊢
      precise-body-base ⊑ imprecise-body-base
  p-body = universal-body-imprecision {W = W} p

  universal-imprecision =
    CTIR.Λ⊑Λ² liftΓ vVᴾ vVᴵ body q

  precise-universal-typing = precise-open-typing-future W≼W′
    (CTIT.source-typing² universal-imprecision)

  precise-universal-typing′ =
    subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
      (sym (compiled-precise-context-future W≼W′ Γ))
      precise-universal-typing

  imprecise-universal-typing = imprecise-open-typing-future W≼W′
    (CTIT.target-typing² universal-imprecision)

  imprecise-universal-typing′ =
    subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
      (sym (compiled-imprecise-context-future W≼W′ Γ))
      imprecise-universal-typing

  endpoints : TypedEndpoints W′ (liftCenterImprecision W≼W′ q)
      (close imprecise-γ (liftImpreciseTerm W≼W′ (Λ Vᴵ)))
      (close precise-γ (liftPreciseTerm W≼W′ (Λ Vᴾ)))
  endpoints = typed-endpoints
    (liftImpreciseTy W≼W′ (`∀ Aᴵ))
    (liftPreciseTy W≼W′ (`∀ Aᴾ))
    (embedImprecise-lift W≼W′ (`∀ Aᴵ))
    (embedPrecise-lift W≼W′ (`∀ Aᴾ))
    (close-preserves-value imprecise-γ
      (ClosureProof.imprecise-value-future W≼W′ (Λ vVᴵ)))
    (close-preserves-value precise-γ
      (ClosureProof.precise-value-future W≼W′ (Λ vVᴾ)))
    (close-preserves-typing imprecise-γ imprecise-universal-typing′)
    (close-preserves-typing precise-γ precise-universal-typing′)

  explicit-universal = I.∀⊑∀
    (liftCenterBodyImprecision W≼W′ p-body)

  precise-body-eq = trans
    (cong (embedPrecise (core W′))
      (sym (liftPreciseTy-universal W≼W′ Aᴾ)))
    (trans (embedPrecise-lift W≼W′ (`∀ Aᴾ))
      (liftCenterTy-universal W≼W′
        (renameᵗ (extᵗ (Consistency.toRenameᵗ
          (preciseEmbedding (core W)))) Aᴾ)))

  imprecise-body-eq = trans
    (cong (embedImprecise (core W′))
      (sym (liftImpreciseTy-universal W≼W′ Aᴵ)))
    (trans (embedImprecise-lift W≼W′ (`∀ Aᴵ))
      (liftCenterTy-universal W≼W′
        (renameᵗ (extᵗ (Consistency.toRenameᵗ
          (impreciseEmbedding (core W)))) Aᴵ)))

  explicit-endpoints : TypedEndpoints W′ explicit-universal
      (close imprecise-γ (liftImpreciseTerm W≼W′ (Λ Vᴵ)))
      (close precise-γ (liftPreciseTerm W≼W′ (Λ Vᴾ)))
  explicit-endpoints = typed-endpoints
    (impreciseType endpoints) (preciseType endpoints)
    (trans (impreciseEmbedded endpoints)
      (liftCenterTy-universal W≼W′ imprecise-body-base))
    (trans (preciseEmbedded endpoints)
      (liftCenterTy-universal W≼W′ precise-body-base))
    (imprecise-value endpoints) (precise-value endpoints)
    (imprecise-typed endpoints) (precise-typed endpoints)

  q-zero : ValueImprecision W′ (liftCenterImprecision W≼W′ q) zero
      (close imprecise-γ (liftImpreciseTerm W≼W′ (Λ Vᴵ)))
      (close precise-γ (liftPreciseTerm W≼W′ (Λ Vᴾ)))
  q-zero = ClosureProof.value-imprecision-reindex
    (liftCenterImprecision W≼W′ q) explicit-universal {k = zero}
    (liftCenterTy-universal W≼W′ precise-body-base)
    (liftCenterTy-universal W≼W′ imprecise-body-base)
    explicit-endpoints

  related : ∀ j → j ≤ k →
      FutureValueRelation (liftCenterImprecision W≼W′ q)
        W′ future-refl j
        (close imprecise-γ (liftImpreciseTerm W≼W′ (Λ Vᴵ)))
        (close precise-γ (liftPreciseTerm W≼W′ (Λ Vᴾ)))
  related zero j≤k = q-zero
  related (suc j) j≤k =
    ClosureProof.value-imprecision-reindex
      (liftCenterImprecision W≼W′ q) explicit-universal
      (liftCenterTy-universal W≼W′ precise-body-base)
      (liftCenterTy-universal W≼W′ imprecise-body-base)
      (explicit-endpoints ,
        liftPreciseBody W≼W′ Aᴾ , liftImpreciseBody W≼W′ Aᴵ ,
        precise-body-eq , imprecise-body-eq ,
        universals p-body (PI.⊑-unique q (I.∀⊑∀ p-body))
          W′ W≼W′ γ (suc j) j≤k)

universal-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty (suc Δᴵ)}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldBoth I.X⊑X (forgetWorld W) ⟩ Aᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldBoth I.X⊑X (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
  → (liftΓ : CTI.LiftCtx I.X⊑X Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → CTI.liftWorldBoth I.X⊑X (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ `∀ Aᴵ)
  → (∀ i → i ≤ k → CompiledUniversalBodyRelation
      (universal-body-imprecision {W = W} p) Aᴾ Aᴵ i Γ Vᴾ Vᴵ)
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) (Λ Vᴵ)
universal-compatible-from-body {W = W} {p = p}
    liftΓ vVᴾ vVᴵ body q body-related =
  universal-compatible liftΓ vVᴾ vVᴵ body q
    (λ q-body q-eq W′ W≼W′ γ j j≤k →
      subst≡
        (λ r → UniversalsRelated W′
          (liftCenterBodyImprecision W≼W′ r)
          (liftPreciseBody W≼W′ _)
          (liftImpreciseBody W≼W′ _) j
          (close (impreciseClosingSubstitution γ)
            (liftImpreciseTerm W≼W′ (Λ _)))
          (close (preciseClosingSubstitution γ)
            (liftPreciseTerm W≼W′ (Λ _))))
        (PI.⊑-unique p-body q-body)
        (universals-related-from-body {p = p-body}
          vVᴾ vVᴵ body-related
          W≼W′ γ j j≤k))
  where
  p-body = universal-body-imprecision {W = W} p
