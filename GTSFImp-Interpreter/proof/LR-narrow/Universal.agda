module proof.LR-narrow.Universal where

-- File Charter:
--   * Constructs related universal values from their elimination obligations.
--   * Constructs those obligations from a binder-specific body relation.
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
open import proof.TermInTermSubst using (subst-cong)
open import proof.TypeInTermSubst using (toRename-keep-eq)
import Consistency
import Imprecision as I
import proof.Imprecision as PI
import proof.DGG.CastTermImprecision2 as CTI
open CTI using (_∣_⊢²_⊑_∶_)
import proof.DGG.CastTermImprecision2Typing as CTIT
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
open import LR-narrow.ImmediateReturn
open import LR-narrow.TypeBetaExpansion using
  (paired-step; related-type-beta-expand)
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
      (fresh : SemanticAtom
        (pairedBindCore (core W″) Rᴾ Rᴵ) Fin.zero)
      (s : liftPreciseBody W′≼W″
            (liftPreciseBody W≼W′ Bᴾ) [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W″ ⟩
          liftImpreciseBody W′≼W″
            (liftImpreciseBody W≼W′ Bᴵ) [ Rᴵ ]ᵗ)
    → let tested = pairedBindWorld W″ Rᴾ Rᴵ fresh
          test-step = future-paired (future-refl {W = W″}) r fresh
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
  head W″ W′≼W″ Rᴾ Rᴵ r fresh s =
    ClosureProof.computations-related-post-bind-reindex
      s-composite s
      (cong (embedPrecise (core W″)) precise-result-trans)
      (cong (embedImprecise (core W″)) imprecise-result-trans)
      imprecise-redex-eq precise-redex-eq canonical
    where
    test-step = paired-step W″ r fresh
    tested = pairedBindWorld W″ Rᴾ Rᴵ fresh
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
      Rᴾ Rᴵ r fresh s-composite

    canonical = related-type-beta-expand
      {W = W″} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
      {r = r} {fresh = fresh} {p = s-composite}
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
    CTI.Λ⊑Λ² liftΓ vVᴾ vVᴵ body q

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
