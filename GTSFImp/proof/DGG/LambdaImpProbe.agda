module proof.DGG.LambdaImpProbe where

-- File Charter:
--   * Probes the Λ⊑² rule with the smallest ∀ ⊑ non-∀ pair: the source
--     instantiates a type abstraction at ℕ while the target is a
--     monomorphic lambda at ★ ⇒ ★ and never allocates a type variable.
--   * Checkpoint 0 is the first use of Λ⊑² in the development, showing
--     the rule is derivable where intended.
--   * After the source's β-Λ step, no checkpoint exists at all: the
--     one-sided reveal rules demand a target pivot variable, and the
--     target type context is empty.  This is recorded as negative
--     theorems that hold for every world, not just one alignment.
--   * Separately, the Λ⊑² premise cannot serve as the induction
--     hypothesis for the missing checkpoint even once left-only pivots
--     exist: it weakens the target term with ⇑ᵗᵐ and lifts the target
--     store, so it lives at target type context 1 while the machine's
--     target store stays at context 0, and SameRuntime is homogeneous.

open import Data.Empty using (⊥-elim)
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
import proof.DGG.Examples as Ex
open Ex.OneStep using (Δ′; change; next; reduction)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (_⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)
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
probe-target = (ƛ (` 0)) · (Ex.c ⟨ CTI2.example12-ℕ! ⟩)

probe-target-lambda-⊢ : Ex.∅ ⊢ ƛ (` 0) ⦂ ★ ⇒ ★
probe-target-lambda-⊢ = ⊢ƛ (⊢` Z)

probe-target-⊢ : Ex.∅ ⊢ probe-target ⦂ ★
probe-target-⊢ =
  ⊢· probe-target-lambda-⊢ (⊢⟨⟩ Ex.c-⊢ CTI2.example12-ℕ!)

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

probe-target-step₀ : Ex.OneStep store-empty probe-target
probe-target-step₀ =
  Ex.from-just-step (step? store-empty probe-target) refl

probe-target₁ : Term (Δ′ probe-target-step₀)
probe-target₁ = next probe-target-step₀

probe-target₁-value : Value probe-target₁
probe-target₁-value = Ex.from-just-value (value? probe-target₁) refl

probe-target-changes : StoreChanges 0 (Δ′ probe-target-step₀)
probe-target-changes = change probe-target-step₀ ∷ []

probe-target-reduction :
  probe-target —↠[ probe-target-changes ] probe-target₁
probe-target-reduction =
  probe-target
  —→[ change probe-target-step₀ ]⟨ reduction probe-target-step₀ ⟩
  probe-target₁ ∎[]

------------------------------------------------------------------------
-- Checkpoint 0: the first use of Λ⊑²
------------------------------------------------------------------------

probe-world₀ : CTI2.World 0 0 0
probe-world₀ = Ex2.reflWorld store-empty

probe-∀⊑⇒★ : `∀ Ex.X⇒X ⊑ᵂ⟨ probe-world₀ ⟩ (★ ⇒ ★)
probe-∀⊑⇒★ = Ex2.∀X⇒X⊑★⇒★² {W = probe-world₀}

probe-body⊑ :
  Ex.X⇒X ⊑ᵂ⟨ CTI2.liftWorldBoth X⊑★ probe-world₀ ⟩ ⇑ᵗ (★ ⇒ ★)
probe-body⊑ = ⇒⊑⇒ (X⊑★ refl) (X⊑★ refl)

-- The Λ⊑² premise as the rule demands it: the target lambda is
-- weakened with ⇑ᵗᵐ into the extended target context, and the world
-- lifts both stores.

probe-Λ-premise :
  CTI2.liftWorldBoth X⊑★ probe-world₀ ∣ [] ⊢²
    ƛ (` 0) ⊑ ⇑ᵗᵐ (ƛ (` 0)) ∶ probe-body⊑
probe-Λ-premise =
  CTI2.ƛ⊑ƛ²
    {A = ＇ Fin.zero} {A′ = ★}
    {pA = X⊑★ refl} {pB = X⊑★ refl}
    (CTI2.x⊑x² {p = X⊑★ refl} CTI2.Zʷ)

probe-Λ⊑ :
  probe-world₀ ∣ [] ⊢² Λ (ƛ (` 0)) ⊑ ƛ (` 0) ∶ probe-∀⊑⇒★
probe-Λ⊑ =
  CTI2.Λ⊑² CTI2.lift-[] (ƛ (` 0)) probe-target-lambda-⊢
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
-- After β-Λ there is no checkpoint, in any world
------------------------------------------------------------------------

-- The source steps to
--   ((ƛ x) ↑ (seal Xᴸ ℕ ↦↑ unseal Xᴸ ℕ)) · 7
-- with source store Xᴸ ↦ ℕ, while the target's type context stays
-- empty.  Peeling the source-only reveal needs reveal⊑², whose
-- rebasing premise demands a target pivot: rebase-varᴸ wraps a
-- RebaseAt whose Xᴿ inhabits TyVar 0, and rebase-idᴸ demands the
-- conversion have no pivot, but seal/unseal pin the pivot to Xᴸ.

no-rebase-empty-target : ∀ {Δᴸ Δ} {W W′ : CTI2.World Δᴸ 0 Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar 0}
  → ¬ CTI2.RebaseAt W W′ Xᴸ Xᴿ
no-rebase-empty-target {Xᴿ = ()} _

probe-function₁-unrelatable : ∀ {Δc} {W : CTI2.World 1 0 Δc}
    {γ : CTI2.CtxImp W} {A B} {q : A ⊑ᵂ⟨ W ⟩ B}
  → ¬ (W ∣ γ ⊢²
        (ƛ (` 0)) ↑ Ex2.example12-source-X-reveal ⊑ ƛ (` 0) ∶ q)
probe-function₁-unrelatable
  (CTI2.reveal⊑² CTI2.rebase-idᴸ _
    (CTI2.⊢↑-⇒ˣ CTI2.join-none () _) _ _)
probe-function₁-unrelatable
  (CTI2.reveal⊑² (CTI2.rebase-varᴸ ra) _ _ _ _) =
  ⊥-elim (no-rebase-empty-target ra)

-- No relation rule matches an application against a constant, so once
-- the target has finished reducing there is nothing left to peel.

probe-app⊑const-unrelatable : ∀ {Δᴸ Δc} {W : CTI2.World Δᴸ 0 Δc}
    {γ : CTI2.CtxImp W} {L M : Term Δᴸ} {κ : Const}
    {A B} {q : A ⊑ᵂ⟨ W ⟩ B}
  → ¬ (W ∣ γ ⊢² L · M ⊑ $ κ ∶ q)
probe-app⊑const-unrelatable ()

-- Checkpoint 1 is impossible against the unstepped target...

probe-checkpoint₁-unrelatable : ∀ {Δc} {W : CTI2.World 1 0 Δc}
    {γ : CTI2.CtxImp W} {A B} {q : A ⊑ᵂ⟨ W ⟩ B}
  → ¬ (W ∣ γ ⊢² Ex.left₁ ⊑ probe-target ∶ q)
probe-checkpoint₁-unrelatable (CTI2.·⊑·² fn arg) =
  probe-function₁-unrelatable fn

-- ...and against the target's only other reduct, the final value.

probe-checkpoint₁-stepped-unrelatable : ∀ {Δc} {W : CTI2.World 1 0 Δc}
    {γ : CTI2.CtxImp W} {A B} {q : A ⊑ᵂ⟨ W ⟩ B}
  → ¬ (W ∣ γ ⊢² Ex.left₁ ⊑ probe-target₁ ∶ q)
probe-checkpoint₁-stepped-unrelatable (CTI2.⊑cast² _ prem _) =
  probe-app⊑const-unrelatable prem

-- Every world relating Term 1 to Term 0 has the shape World 1 0 Δc,
-- because SameRuntime pins the world's stores to the machine's stores
-- and the target store still has type TyStore 0.  So the two lemmas
-- above close off every candidate checkpoint for the β-Λ square: the
-- simulation cannot be completed with the current rules.
--
-- Note the Λ⊑² premise proved in probe-Λ-premise is of no help: it
-- lives in liftWorldBoth X⊑★ probe-world₀ : World 1 1 1, whose target
-- store is store-lift store-empty : TyStore 1 and whose target term is
-- the weakened ⇑ᵗᵐ (ƛ (` 0)).  A usable induction hypothesis needs the
-- unweakened target ƛ (` 0) over target store store-empty : TyStore 0,
-- which is not even the same World index, so no SameRuntime or
-- RebaseAt can connect them.  Restating Λ⊑² with a left-only world
-- lift (keep ηᴸ, skip ηᴿ, store-lift only the source store) and an
-- unweakened premise V ⊑ M removes both obstacles at this rule, and
-- the missing left-only pivot form of RebaseAtᴸ is what reveal⊑² and
-- conceal⊑² additionally need to peel the source-only wrappers.
