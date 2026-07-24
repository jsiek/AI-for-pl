module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsUnsealAssemblyAccProof
  where

-- File Charter:
--   * Closes the ranked pending-cast SCC from the sole semantic
--     instantiation/allocation residual.
--   * Owns successful unseal and both eager fused-plan expansions, with every
--     recursive call visibly consuming the current `Acc` predecessor.
--   * Reuses the same completed worker for all target administration.
--   * Contains no result/view/outcome carrier, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (_︔_; unseal)
open import Data.List using ([]; _∷_)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (<-trans; n<1+n)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionWf using
  (∀ⁱ_; ν; _∣_⊢_⊑_⊣_)
open import Induction.WellFounded using (acc)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import NuReduction using
  (β-id; β-seq; pure-step; seal-unseal; tag-untag-ok)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ƛ_
  ; Λ_
  ; $
  ; no•-⟨⟩
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import TermTyping using (forget)
open import Types using
  (★; ★⇒★; _⇒_; `∀; ＇_)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)
open import proof.DGG.Core.NuProgress using
  (canonical-★; canonical-＇; sv-seal; sv-tag)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureDef
  using
  ( targetPendingAdministrationRank
  ; valueAdministrationWeight
  )
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureLemma
  using
  ( target-inert-value-administration-increaseᵀ
  ; target-pending-administration-tail-decreaseᵀ
  )
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureProof
  using
  (target-inert-rank-decreases; target-sequence-rank-decreases)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using
  ( plan-fun-untag-gen
  ; plan-id
  ; plan-inert
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-seq
  ; plan-unseal
  ; plan-untag
  )
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( applyTargetPendingCasts
  ; pending-cons
  ; pending-empty
  )
open import
  proof.Target.Administration.NuImprecisionTargetPendingSequenceExpansion
  using (target-administration-sequence-spine-expansionᵀ)
open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationLemma
  using (target-tag-cancellationᵀ)
open import
  proof.Target.SealTag.NuImprecisionTargetSealCancellationLemma
  using (target-seal-cancellationᵀ)
open import
  proof.Target.SealTag.NuImprecisionTargetGroundUniqueness
  using (universal-star-to-function)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextLemma
  using
  (world-coherent-right-target-pending-cast-prepend-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsAccDef
  using (WorldCoherentRightTargetPendingCastsAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsInstResidualAccDef
  using (WorldCoherentRightTargetPendingCastsInstResidualAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsUnsealAssemblyAccDef
  using (WorldCoherentRightTargetPendingCastsUnsealAssemblyAccᵀ)
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextLemma
  using (world-coherent-right-value-terminal-contextᵀ)


private
  value-administration-weight-proof-irrelevant :
    ∀ {V : Term} (vV vV′ : Value V) →
    valueAdministrationWeight vV ≡
      valueAdministrationWeight vV′
  value-administration-weight-proof-irrelevant
      (ƛ N) (ƛ .N) =
    refl
  value-administration-weight-proof-irrelevant
      (Λ vV) (Λ vV′)
      rewrite
        value-administration-weight-proof-irrelevant vV vV′ =
    refl
  value-administration-weight-proof-irrelevant
      ($ k) ($ .k) =
    refl
  value-administration-weight-proof-irrelevant
      (vV ⟨ inert-c ⟩) (vV′ ⟨ inert-c′ ⟩)
      rewrite
        value-administration-weight-proof-irrelevant vV vV′ =
    refl

  target-pending-rank-value-proof-irrelevant :
    ∀ {V : Term} (vV vV′ : Value V) cs →
    targetPendingAdministrationRank vV cs ≡
      targetPendingAdministrationRank vV′ cs
  target-pending-rank-value-proof-irrelevant vV vV′ cs
      rewrite
        value-administration-weight-proof-irrelevant vV vV′ =
    refl

  seal-no•⁻¹ :
    ∀ {V A α} →
    No• (V ⟨ C.seal A α ⟩) →
    No• V
  seal-no•⁻¹ (no•-⟨⟩ noV) = noV

  pending-casts-runtime⁻¹ :
    ∀ cs {M : Term} →
    RuntimeOK (applyTargetPendingCasts M cs) →
    RuntimeOK M
  pending-casts-runtime⁻¹ [] okM = okM
  pending-casts-runtime⁻¹ (c ∷ cs) okM =
    runtime-⟨⟩ (pending-casts-runtime⁻¹ cs okM)

  pending-casts-runtime :
    ∀ cs {M : Term} →
    RuntimeOK M →
    RuntimeOK (applyTargetPendingCasts M cs)
  pending-casts-runtime [] okM = okM
  pending-casts-runtime (c ∷ cs) okM =
    pending-casts-runtime cs (ok-⟨⟩ okM)

  successor-rank-decrease :
    ∀ {inner outer} →
    outer ≡ suc inner →
    inner < outer
  successor-rank-decrease {inner} equality =
    subst (inner <_) (sym equality) (n<1+n inner)

  eager-function-from-star :
    ∀ {Φ Δᴸ Δᴿ A C} →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
    Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
  eager-function-from-star p (∀ⁱ q) =
    universal-star-to-function p
  eager-function-from-star p (ν safe occ q) =
    universal-star-to-function p

  eager-function-to-star :
    ∀ {Φ Δᴸ Δᴿ A C} →
    Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ →
    (q : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
    Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
  eager-function-to-star (∀ⁱ p) q =
    universal-star-to-function q
  eager-function-to-star (ν safe occ p) q =
    universal-star-to-function q

  tag-no-bullet :
    ∀ {V G} →
    No• (V ⟨ G C.! ⟩) →
    No• V
  tag-no-bullet (no•-⟨⟩ noV) = noV

  tag-value-evidence⁻¹ :
    ∀ {V G} →
    (vTag : Value (V ⟨ G C.! ⟩)) →
    Σ[ vV ∈ Value V ] vTag ≡ (vV ⟨ G C.! ⟩)
  tag-value-evidence⁻¹ (vV ⟨ G C.! ⟩) = vV , refl

  module PendingWorker
      (inst : WorldCoherentRightTargetPendingCastsInstResidualAccᵀ) where

    pending-worker :
      WorldCoherentRightTargetPendingCastsAccᵀ
    pending-worker
        vW access pending-empty coherent exclusive unique wfR
        runtime vV noV noW relation =
      world-coherent-right-value-terminal-contextᵀ
        prefix-reflⁱ coherent exclusive unique wfR
        vV noV vW noW relation
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-inert inert-c)
          (inj₁ (μ′ , β , X′ , reveal)) tail)
        coherent exclusive unique wfR runtime vV noV noW relation =
      pending-worker
        (vW ⟨ inert-c ⟩)
        (smaller
          (successor-rank-decrease
            (target-inert-rank-decreases vW inert-c cs)))
        tail coherent exclusive unique wfR runtime
        vV noV (no•-⟨⟩ noW)
        (⊑conv↑ᵀ reveal relation r)
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-inert inert-c)
          (inj₂ (inj₁ (μ′ , β , X′ , conceal))) tail)
        coherent exclusive unique wfR runtime vV noV noW relation =
      pending-worker
        (vW ⟨ inert-c ⟩)
        (smaller
          (successor-rank-decrease
            (target-inert-rank-decreases vW inert-c cs)))
        tail coherent exclusive unique wfR runtime
        vV noV (no•-⟨⟩ noW)
        (⊑conv↓ᵀ conceal relation r)
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-inert inert-c)
          (inj₂ (inj₂ (inj₁
            (μ′ , mode , seal★ , narrowing)))) tail)
        coherent exclusive unique wfR runtime vV noV noW relation =
      pending-worker
        (vW ⟨ inert-c ⟩)
        (smaller
          (successor-rank-decrease
            (target-inert-rank-decreases vW inert-c cs)))
        tail coherent exclusive unique wfR runtime
        vV noV (no•-⟨⟩ noW)
        (⊑cast⊒ᵀ mode seal★ narrowing relation r)
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-inert inert-c)
          (inj₂ (inj₂ (inj₂ (inj₁
            (μ′ , mode , seal★ , widening))))) tail)
        coherent exclusive unique wfR runtime vV noV noW relation =
      pending-worker
        (vW ⟨ inert-c ⟩)
        (smaller
          (successor-rank-decrease
            (target-inert-rank-decreases vW inert-c cs)))
        tail coherent exclusive unique wfR runtime
        vV noV (no•-⟨⟩ noW)
        (⊑cast⊑ᵀ mode seal★ widening relation r)
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-inert inert-c)
          (inj₂ (inj₂ (inj₂ (inj₂
            (seal★ , widening))))) tail)
        coherent exclusive unique wfR runtime vV noV noW relation =
      pending-worker
        (vW ⟨ inert-c ⟩)
        (smaller
          (successor-rank-decrease
            (target-inert-rank-decreases vW inert-c cs)))
        tail coherent exclusive unique wfR runtime
        vV noV (no•-⟨⟩ noW)
        (⊑cast⊑idᵀ seal★ widening relation r)
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {p = p} {r = r} plan-id evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        with assumption-membership-unique→precision-index-unique unique p r
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {p = p} {r = .p} plan-id evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        | refl
        with pending-worker
          vW
          (smaller
            (target-pending-administration-tail-decreaseᵀ vW c cs))
          tail coherent exclusive unique wfR
          (pending-casts-runtime cs (ok-no noW))
          vV noV noW relation
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {p = p} {r = .p} plan-id evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        | refl
        | caught , context-eq , right-prefix =
      world-coherent-right-target-pending-cast-prepend-contextᵀ
        {cs = cs}
        (pure-step (β-id vW))
        caught context-eq right-prefix
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-untag {gH = gH})
          evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        with canonical-★ vW
          (forget (nu-term-imprecision-target-typing relation))
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-untag {gH = gH})
          evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        | sv-tag {W = U} {G = G} canonical-vU refl
        with tag-value-evidence⁻¹ vW
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-untag {gH = gH})
          evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        | sv-tag {W = U} {G = G} canonical-vU refl
        | vU , refl
        with target-tag-cancellationᵀ
          exclusive unique gH vV noV vU relation r
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-untag {gH = gH})
          evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        | sv-tag {W = U} {G = G} canonical-vU refl
        | vU , refl
        | refl , canceled
        with pending-worker
          vU
          (smaller
            (<-trans
              (target-inert-value-administration-increaseᵀ
                vU (G C.!) cs)
              (target-pending-administration-tail-decreaseᵀ vW c cs)))
          tail coherent exclusive unique wfR
          (pending-casts-runtime cs
            (ok-no (tag-no-bullet noW)))
          vV noV (tag-no-bullet noW) canceled
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons {r = r} (plan-untag {gH = gH})
          evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        | sv-tag {W = U} {G = G} canonical-vU refl
        | vU , refl
        | refl , canceled
        | caught , context-eq , right-prefix =
      world-coherent-right-target-pending-cast-prepend-contextᵀ
        {cs = cs}
        (pure-step (tag-untag-ok vU))
        caught context-eq right-prefix
    pending-worker
        {B = ＇ α} {cs = unseal α B ∷ cs}
        vW (acc recurse)
        (pending-cons {r = r}
          (plan-unseal {αB∈Σ = αB∈Σ})
          evidence tail-spine)
        coherent exclusive unique wfR ok-pending
        vV noV noW relation
        with canonical-＇ vW
          (forget (nu-term-imprecision-target-typing relation))
    pending-worker
        {B = ＇ α} {cs = unseal α B ∷ cs}
        vW (acc recurse)
        (pending-cons {r = r}
          (plan-unseal {αB∈Σ = αB∈Σ})
          evidence tail-spine)
        coherent exclusive unique wfR ok-pending
        vV noV noW relation
        | sv-seal {W = U} {A = Y} vU refl =
      world-coherent-right-target-pending-cast-prepend-contextᵀ
        {cs = cs}
        (pure-step (seal-unseal vU))
        caught context-eq right-prefix
      where
      noU = seal-no•⁻¹ noW

      canceled =
        target-seal-cancellationᵀ
          coherent wfR vV noV vU αB∈Σ relation r

      smaller =
        <-trans
          (target-inert-value-administration-increaseᵀ
            vU (C.seal Y α) cs)
          (subst
            (λ n →
              n <
              targetPendingAdministrationRank
                vW (unseal α B ∷ cs))
            (sym
              (target-pending-rank-value-proof-irrelevant
                (vU ⟨ C.seal Y α ⟩) vW cs))
            (target-pending-administration-tail-decreaseᵀ
              vW (unseal α B) cs))

      ok-root =
        pending-casts-runtime⁻¹ cs ok-pending

      okU =
        runtime-⟨⟩ (runtime-⟨⟩ ok-root)

      continued =
        pending-worker
          vU (recurse smaller) tail-spine coherent
          exclusive unique wfR (pending-casts-runtime cs okU)
          vV noV noU canceled

      caught = continued .Data.Product.proj₁
      context-eq =
        continued .Data.Product.proj₂ .Data.Product.proj₁
      right-prefix =
        continued .Data.Product.proj₂ .Data.Product.proj₂
    pending-worker
        {cs = c ∷ cs}
        vW access
        (pending-cons
          (plan-inst
            {hB = hB} {occ = occ} {s⊢ = s⊢}
            {p = p} {q = r})
          evidence tail)
        coherent exclusive unique wfR ok-pending
        vV noV noW relation =
      inst
        {hB = hB} {occ = occ} {s⊢ = s⊢}
        {p = p} {r = r}
        vW access evidence tail coherent exclusive unique wfR
        ok-pending vV noV noW relation
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons
          (plan-fun-untag-gen
            {μ = μ} {s = s}
            {hG = hG} {gG = gG} {tag-ok = tag-ok}
            {hFun = hFun} {occ = occ} {s⊢ = s⊢}
            {p = p} {q = r})
          evidence tail)
        coherent exclusive unique wfR ok-pending
        vV noV noW relation
        with pending-worker
          vW
          (smaller
            (successor-rank-decrease
              (target-sequence-rank-decreases
                vW ((★ ⇒ ★) C.？) (C.gen (★ ⇒ ★) s) cs)))
          (target-administration-sequence-spine-expansionᵀ
            {s⊢ = C.cast-untag hG gG tag-ok}
            {t⊢ = C.cast-gen hFun occ s⊢}
            (plan-untag
              {μ = μ} {hH = hG} {gH = gG} {ok = tag-ok}
              {p = p} {q = eager-function-from-star p r})
            (plan-inert
              {p = eager-function-from-star p r} {q = r}
              (C.gen (★ ⇒ ★) s))
            evidence tail)
          coherent exclusive unique wfR
          (pending-casts-runtime
            ((★ ⇒ ★) C.？ ∷ C.gen (★ ⇒ ★) s ∷ cs)
            (ok-no noW))
          vV noV noW relation
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons
          (plan-fun-untag-gen
            {μ = μ} {s = s}
            {hG = hG} {gG = gG} {tag-ok = tag-ok}
            {hFun = hFun} {occ = occ} {s⊢ = s⊢}
            {p = p} {q = r})
          evidence tail)
        coherent exclusive unique wfR ok-pending
        vV noV noW relation
        | caught , context-eq , right-prefix =
      world-coherent-right-target-pending-cast-prepend-contextᵀ
        {cs = cs}
        (pure-step (β-seq vW))
        caught context-eq right-prefix
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons
          (plan-inst-fun-tag
            {μ = μ} {s = s}
            {hFun = hFun} {occ = occ} {s⊢ = s⊢}
            {hG = hG} {gG = gG} {tag-ok = tag-ok}
            {p = p} {q = r})
          evidence tail)
        coherent exclusive unique wfR ok-pending
        vV noV noW relation
        with pending-worker
          vW
          (smaller
            (successor-rank-decrease
              (target-sequence-rank-decreases
                vW (C.inst (★ ⇒ ★) s) ((★ ⇒ ★) C.!) cs)))
          (target-administration-sequence-spine-expansionᵀ
            {s⊢ = C.cast-inst hFun occ s⊢}
            {t⊢ = C.cast-tag hG gG tag-ok}
            (plan-inst
              {p = p} {q = eager-function-to-star p r})
            (plan-inert
              {p = eager-function-to-star p r} {q = r}
              ((★ ⇒ ★) C.!))
            evidence tail)
          coherent exclusive unique wfR
          (pending-casts-runtime
            (C.inst (★ ⇒ ★) s ∷ (★ ⇒ ★) C.! ∷ cs)
            (ok-no noW))
          vV noV noW relation
    pending-worker
        {cs = c ∷ cs}
        vW (acc smaller)
        (pending-cons
          (plan-inst-fun-tag
            {μ = μ} {s = s}
            {hFun = hFun} {occ = occ} {s⊢ = s⊢}
            {hG = hG} {gG = gG} {tag-ok = tag-ok}
            {p = p} {q = r})
          evidence tail)
        coherent exclusive unique wfR ok-pending
        vV noV noW relation
        | caught , context-eq , right-prefix =
      world-coherent-right-target-pending-cast-prepend-contextᵀ
        {cs = cs}
        (pure-step (β-seq vW))
        caught context-eq right-prefix
    pending-worker
        {cs = (s ︔ t) ∷ cs}
        vW (acc smaller)
        (pending-cons
          (plan-seq s-plan t-plan) evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        with pending-worker
          vW
          (smaller
            (successor-rank-decrease
              (target-sequence-rank-decreases vW s t cs)))
          (target-administration-sequence-spine-expansionᵀ
            s-plan t-plan evidence tail)
          coherent exclusive unique wfR
          (pending-casts-runtime (s ∷ t ∷ cs) (ok-no noW))
          vV noV noW relation
    pending-worker
        {cs = (s ︔ t) ∷ cs}
        vW (acc smaller)
        (pending-cons
          (plan-seq s-plan t-plan) evidence tail)
        coherent exclusive unique wfR runtime vV noV noW relation
        | caught , context-eq , right-prefix =
      world-coherent-right-target-pending-cast-prepend-contextᵀ
        {cs = cs}
        (pure-step (β-seq vW))
        caught context-eq right-prefix


world-coherent-right-target-pending-casts-unseal-assembly-acc-proofᵀ :
  WorldCoherentRightTargetPendingCastsUnsealAssemblyAccᵀ
world-coherent-right-target-pending-casts-unseal-assembly-acc-proofᵀ inst =
  PendingWorker.pending-worker
    (λ {Φ} {Δᴸ} {Δᴿ} {ρ}
      {V} {W} {A} {B} {C} {D} {s} {cs} {μ}
      {hB} {occ} {s⊢} {p} {r} {q}
      vW access evidence tail coherent exclusive unique wfR
      runtime vV noV noW relation →
      inst
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
        {V = V} {W = W}
        {A = A} {B = B} {C = C} {D = D}
        {s = s} {cs = cs} {μ = μ}
        {hB = hB} {occ = occ} {s⊢ = s⊢}
        {p = p} {r = r} {q = q}
        vW access evidence tail coherent exclusive unique wfR
        runtime vV noV noW relation)
