module proof.DGG.LambdaImpProbe where

-- File Charter:
--   * Probes the Λ⊑² rule with the smallest ∀ ⊑ non-∀ pair: the source
--     instantiates a type abstraction at ℕ while the target is a
--     monomorphic lambda at ★ ⇒ ★ and never allocates a type variable.
--   * Checkpoint 0 exercises Λ⊑², whose premise compares the target
--     term unweakened in a left-only lifted world.
--   * After the source's β-Λ step the world evolves by leftOnlyWorld.
--     The old direct sealed-argument checkpoint is now recorded
--     negatively: the source seal has representation ℕ and its target
--     partner is the bare `ℕ!` tag, so source-side conceal formation is
--     rejected.  The final payload comparison remains derivable.
--   * An earlier revision of this probe proved the negative results
--     that forced this design: with the ⇑ᵗᵐ-weakened Λ⊑² premise and
--     only two-sided pivots, checkpoint 1 was impossible in any world.
--     The two-sided impossibility is kept below as
--     no-rebase-empty-target; the rest became derivable and was
--     replaced by the positive checkpoints.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
import Data.Fin as Fin
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using (TyStore; store-empty; store-bind)
open import TermCtx using (Z)
open import Consistency using (_↪ᵗ_; empty; id↪ᵗ)
open import Imprecision
open import Primitives using (Const; κℕ)
open import CastTerms
open import Reduction
open import Eval using (step?; value?)
import proof.DGG.ExampleTerms as Ex
import proof.DGG.OneStep as Step
open Step using (Δ′; change; next; reduction)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.Example12Worlds as Ex12
open CTX using (_⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.Examples2 as Ex2

------------------------------------------------------------------------
-- The probe pair
------------------------------------------------------------------------

-- Source: ((Λ (ƛ x)) ⦂∀ (X ⇒ X) [ ℕ ]) · 7, Example 12's direct
-- program.  Target: (ƛ x) · (7 ⟨ ℕ! ⟩) at type ★, with the type
-- abstraction erased entirely, so ∀ X. X ⇒ X ⊑ ★ ⇒ ★ crosses the
-- ∀ ⊑ non-∀ boundary and the pair needs Λ⊑².

probe-source : Term 0
probe-source = Ex.example12-left

probe-target : Term 0
probe-target = (ƛ (` 0)) · (Ex.c ⟨ Ex12.example12-ℕ! ⟩)

probe-target-lambda-⊢ : Ex.∅ ⊢ ƛ (` 0) ⦂ ★ ⇒ ★
probe-target-lambda-⊢ = ⊢ƛ (⊢` Z)

probe-target-⊢ : Ex.∅ ⊢ probe-target ⦂ ★
probe-target-⊢ =
  ⊢· probe-target-lambda-⊢ (⊢⟨⟩ Ex.c-⊢ Ex12.example12-ℕ!)

------------------------------------------------------------------------
-- Reduction traces
------------------------------------------------------------------------

-- The source allocates one type variable (β-Λ) and then runs the
-- revealed function; this is Example 12's left trace, reused.

probe-source-reduction :
  probe-source —↠[ Ex.left-changes ] Ex.left-final
probe-source-reduction = Ex.example12-left-reduction

-- The target never allocates: its argument 7 ⟨ ℕ! ⟩ is already a
-- value, so the only step is the β for the monomorphic lambda.

probe-target-step₀ : Step.OneStep store-empty probe-target
probe-target-step₀ =
  Step.from-just-step (step? store-empty probe-target) refl

probe-target₁ : Term (Δ′ probe-target-step₀)
probe-target₁ = next probe-target-step₀

probe-target₁-value : Value probe-target₁
probe-target₁-value = Step.from-just-value (value? probe-target₁) refl

probe-target-changes : StoreChanges 0 (Δ′ probe-target-step₀)
probe-target-changes = change probe-target-step₀ ∷ []

probe-target-reduction :
  probe-target —↠[ probe-target-changes ] probe-target₁
probe-target-reduction =
  probe-target
  —→[ change probe-target-step₀ ]⟨ reduction probe-target-step₀ ⟩
  probe-target₁ ∎[]

------------------------------------------------------------------------
-- Checkpoint 0: Λ⊑² with an unweakened target premise
------------------------------------------------------------------------

probe-world₀ : CTX.World 0 0 0
probe-world₀ = Ex2.reflWorld store-empty

probe-∀⊑⇒★ : `∀ Ex.X⇒X ⊑ᵂ⟨ probe-world₀ ⟩ (★ ⇒ ★)
probe-∀⊑⇒★ = Ex2.∀X⇒X⊑★⇒★² {W = probe-world₀}

probe-body⊑ :
  Ex.X⇒X ⊑ᵂ⟨ CTX.liftWorldLeft probe-world₀ ⟩ (★ ⇒ ★)
probe-body⊑ = ⇒⊑⇒ (X⊑★ refl) (X⊑★ refl)

probe-Λ-premise :
  CTX.liftWorldLeft probe-world₀ ∣ [] ⊢²
    ƛ (` 0) ⊑ ƛ (` 0) ∶ probe-body⊑
probe-Λ-premise =
  CTI2.ƛ⊑ƛ²
    {A = ＇ Fin.zero} {A′ = ★}
    {pA = X⊑★ refl} {pB = X⊑★ refl}
    (CTI2.x⊑x² {p = X⊑★ refl} CTX.Zʷ)

probe-Λ⊑ :
  probe-world₀ ∣ [] ⊢² Λ (ƛ (` 0)) ⊑ ƛ (` 0) ∶ probe-∀⊑⇒★
probe-Λ⊑ =
  CTI2.Λ⊑² nonvar-fun (∈-fun-left var-∈)
    CTX.liftᴸ-[] (ƛ (` 0)) probe-target-lambda-⊢
    probe-Λ-premise probe-∀⊑⇒★

probe-function₀ :
  probe-world₀ ∣ [] ⊢²
    (Λ (ƛ (` 0))) ⦂∀ Ex.X⇒X [ Ex.ℕᵗ ] ⊑ ƛ (` 0) ∶
      Ex2.ℕ⇒ℕ⊑★⇒★² {W = probe-world₀}
probe-function₀ =
  CTI2.•⊑²
    {C = Ex.X⇒X} {A = Ex.ℕᵗ} {B = ★ ⇒ ★}
    probe-∀⊑⇒★ probe-Λ⊑
    (Ex2.ℕ⊑★² {W = probe-world₀})
    (Ex2.ℕ⇒ℕ⊑★⇒★² {W = probe-world₀})

probe-checkpoint₀ :
  probe-world₀ ∣ [] ⊢² Ex.left₀ ⊑ probe-target ∶
    Ex2.left-path-ℕ⊑★₀
probe-checkpoint₀ =
  CTI2.·⊑·² probe-function₀ Ex2.left-path-argument₀

------------------------------------------------------------------------
-- Two-sided pivots still need a target variable
------------------------------------------------------------------------

-- With an empty target type context there is no pivot pair at all;
-- this is the impossibility that motivates rebase-onlyᴸ.

no-rebase-empty-target : ∀ {Δᴸ Δ} {W W′ : CTX.World Δᴸ 0 Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar 0}
  → ¬ CTX.RebaseAt W W′ Xᴸ Xᴿ
no-rebase-empty-target {Xᴿ = ()} _

------------------------------------------------------------------------
-- After β-Λ: the left-only world and its left-only pivot
------------------------------------------------------------------------

-- The source allocates Xᴸ ↦ ℕ, so the world evolves by leftOnlyWorld:
-- the source store binds ℕ while the target side is untouched.

probe-world₁ : CTX.World 1 0 1
probe-world₁ = CTX.leftOnlyWorld probe-world₀ Ex.ℕᵗ

probe-rebase-X : CTX.RebaseAtᴸ probe-world₁ probe-world₁
    (just Fin.zero)
probe-rebase-X = CTX.rebase-onlyᴸ refl (λ ()) ι⊑★

probe-X⊑★₁ : (＇ Fin.zero) ⊑ᵂ⟨ probe-world₁ ⟩ ★
probe-X⊑★₁ = X⊑★ refl

probe-fn⊑₁ :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ probe-world₁ ⟩ (★ ⇒ ★)
probe-fn⊑₁ = ⇒⊑⇒ probe-X⊑★₁ probe-X⊑★₁

------------------------------------------------------------------------
-- Checkpoints 1-4: the simulation completes
------------------------------------------------------------------------

probe-lambda₁ :
  probe-world₁ ∣ [] ⊢² ƛ (` 0) ⊑ ƛ (` 0) ∶ probe-fn⊑₁
probe-lambda₁ =
  CTI2.ƛ⊑ƛ²
    {A = ＇ Fin.zero} {A′ = ★}
    {pA = probe-X⊑★₁} {pB = probe-X⊑★₁}
    (CTI2.x⊑x² {p = probe-X⊑★₁} CTX.Zʷ)

probe-function₁ :
  probe-world₁ ∣ [] ⊢²
    (ƛ (` 0)) ↑ Ex2.example12-source-X-reveal ⊑ ƛ (` 0) ∶
      Ex2.ℕ⇒ℕ⊑★⇒★² {W = probe-world₁}
probe-function₁ =
  CTI2.reveal⊑² CTX.impEnvMono-refl probe-rebase-X CTX.same-[]
    Ex2.example12-source-X-reveal-⊢ˣ probe-lambda₁
    (Ex2.ℕ⇒ℕ⊑★⇒★² {W = probe-world₁})

probe-argument₁ :
  probe-world₁ ∣ [] ⊢²
    $ (κℕ 7) ⊑ Ex.c ⟨ Ex12.example12-ℕ! ⟩ ∶
      Ex2.ℕ⊑★² {W = probe-world₁}
probe-argument₁ =
  CTI2.⊑cast² Ex12.example12-ℕ!
    (CTI2.κ⊑κ² (κℕ 7) (Ex2.ℕ⊑ℕ² {W = probe-world₁}))
    (Ex2.ℕ⊑★² {W = probe-world₁})

probe-checkpoint₁ :
  probe-world₁ ∣ [] ⊢² Ex.left₁ ⊑ probe-target ∶
    Ex2.ℕ⊑★² {W = probe-world₁}
probe-checkpoint₁ = CTI2.·⊑·² probe-function₁ probe-argument₁


{-
The following positive checkpoints used the removed direct
source-seal/bare-target-tag admission.  Their semantic payload survives as
`probe-argument₁` and `probe-checkpoint₄`.

probe-app₂ :
  probe-world₁ ∣ [] ⊢²
    (ƛ (` 0)) · (($ (κℕ 7)) ↓ Ex2.example12-source-X-seal)
    ⊑ (ƛ (` 0)) · (Ex.c ⟨ Ex12.example12-ℕ! ⟩) ∶ probe-X⊑★₁
probe-app₂ = CTI2.·⊑·² probe-lambda₁ probe-sealed-arg

probe-checkpoint₂ :
  probe-world₁ ∣ [] ⊢² Ex.left₂ ⊑ probe-target ∶
    Ex2.ℕ⊑★² {W = probe-world₁}
probe-checkpoint₂ =
  CTI2.reveal⊑² CTX.impEnvMono-refl probe-rebase-X CTX.same-[]
    Ex2.example12-source-X-unseal-⊢ˣ probe-app₂
    (Ex2.ℕ⊑★² {W = probe-world₁})

-- The source's β under the reveal is matched by the target's β, so
-- checkpoint 3 pairs the source with the stepped target.

probe-checkpoint₃ :
  probe-world₁ ∣ [] ⊢² Ex.left₃ ⊑ probe-target₁ ∶
    Ex2.ℕ⊑★² {W = probe-world₁}
probe-checkpoint₃ =
  CTI2.reveal⊑² CTX.impEnvMono-refl probe-rebase-X CTX.same-[]
    Ex2.example12-source-X-unseal-⊢ˣ probe-sealed-arg
    (Ex2.ℕ⊑★² {W = probe-world₁})
-}

probe-checkpoint₄ :
  probe-world₁ ∣ [] ⊢² Ex.left-final ⊑ probe-target₁ ∶
    Ex2.ℕ⊑★² {W = probe-world₁}
probe-checkpoint₄ = probe-argument₁
