M5 instantiation inversion blocker: a hereditary smart child plan does not
provide the reverse type-imprecision bridge needed by the parent Λ rewrap

Date: 2026-08-13

Scoped target:

  Define the statement-first derivation-recursive producer

    rel : W ∣ γ ⊢² M ⊑ Λ V′ ∶ p
    plan : ΛTwoInsertPostPlan W
    ----------------------------------------------------------
    ΛPostPrefixPackageAtBase rel (postExtend plan) c′ B′≢★

  with recursive clauses for `Λ⊑Λ²`, `Λ⊑²`,
  `Λ⊑²-smart-comma`, and the source-only cast/reveal/conceal wrappers.

Checked progress before this stop:

  `Λ-two-insert-rebase-child` transports an arbitrary finite two-insert plan
  through `RebaseAtᴸ` by applying `TargetExtend.insertRebaseAtᴸ` twice.  It
  reconstructs both target-store-follow equations, both target windows, the
  route-one facts and post geometry, and returns the post `ImpEnvMono` and
  `RebaseAtᴸ` witnesses needed by the reveal wrapper.

  `Λ-two-insert-tag-rebase-child` does the analogous construction through
  `TagRebaseAtᴸ`, using `TargetExtend.reverseTagRebaseAtᴸ` twice.  It returns
  the post monotonicity and tag-rebase witness needed by the conceal wrapper.

  The focused no-metas gate passes:

    agda -v0 --no-allow-unsolved-metas \
      proof/DGG/Catchup/InstInversionProof.agda

First non-composing obligation:

  Suppose the current smart-comma constructor has premise world `Wᵐ`, and
  `Λ-two-insert-smart-child plan liftW` supplies its hereditary child plan.
  Recursive production gives the child prefix type

    A ⊑ᵂ⟨ Wᵐ₂ ⟩ ΛResidualSource₂ B

  where `Wᵐ₂` is the child's post world.  Re-emitting the parent constructor
  with `Λ⊑²-smart-recursive-prefix-at-base` requires instead

    `∀ A ⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B.

  The usual `∀⊑` construction first requires the premise relation

    A ⊑ᵂ⟨ liftWorldLeft X⊑★ W₂ ⟩ ΛResidualSource₂ B.

  The child plan exposes

    postLift : SmartCommaLiftᴸ W₂ Wᵐ₂

  but `smartCommaLift-transport⊑ᵂ postLift` only maps in the forward
  direction:

    A ⊑ᵂ⟨ liftWorldLeft X⊑★ W₂ ⟩ C
      → A ⊑ᵂ⟨ Wᵐ₂ ⟩ C.

  It cannot map the recursive result back to the left-lifted parent world.

Machine-checked mismatch:

  A temporary notes probe stated the required reverse bridge and tried the
  only existing smart transport:

    post-smart-untransport-needed :
      SmartCommaLiftᴸ W₂ Wᵐ₂
      → A ⊑ᵂ⟨ Wᵐ₂ ⟩ B
      → A ⊑ᵂ⟨ liftWorldLeft X⊑★ W₂ ⟩ B
    post-smart-untransport-needed liftW p =
      smartCommaLift-transport⊑ᵂ liftW p

  Agda rejected `p` at the application site with:

    Δᵐ₂ != (suc Δ₂) of type Data.Nat.ℕ
    when checking that the expression p has type
    A ⊑ᵂ⟨ liftWorldLeft X⊑★ W₂ ⟩ B

  The temporary probe was removed after recording the error.

Why existing lemmas do not close it:

  `ΛPostWindowGeometry.finalBody⊑ᵂ` starts from a shared
  `liftWorldBoth X⊑X` body.  It does not invert a smart-comma relation.

  `Λ-post-outer-obligation` is specialized to the canonical twice-right-only
  post world.  Its `∀⊑` branch recursively uses
  `Λ⊑²-smart-fresh-top`, whose untransport proof is likewise specialized to
  the canonical front/fresh layout.

  In the hereditary worker the post guard may be either alias or fresh and,
  in the fresh case, may use a nontrivial pushout center context.  Those worlds
  are not definitionally equal to the canonical right-only world.

Required next statement surface:

  Either strengthen the smart child-plan result with a checked post-top
  eliminator

    (NonVar A)
    → (zero ∈ᵗ A)
    → A ⊑ᵂ⟨ Wᵐ₂ ⟩ C
    → `∀ A ⊑ᵂ⟨ W₂ ⟩ C

  and construct it exhaustively for both `SmartAliasMergeGuard` and
  `SmartFreshBehindGuard`, or prove the corresponding reusable guarded
  untransport theorem first.  Merely storing the existing forward
  `SmartCommaLiftᴸ` witness in the child plan is insufficient.

  The theorem must be justified by the guard fields for both cases; it must
  not be postulated or obtained by changing the live term-imprecision
  relation.  Once live, the recursive `Λ⊑²` and `Λ⊑²-smart-comma` clauses can
  use it for their top `p₂`, after which the already-checked source plan
  transformers can close reveal and conceal.

Recommended re-evaluation before strengthening every smart guard:

  The failed probe tried to build the parent's top `p₂` from the recursive
  child's `p₂`.  A narrower route may instead generalize
  `Λ-post-outer-obligation` from the canonical twice-right-only world to a
  `ΛTwoInsertPostPlan`, and build the parent top obligation directly from the
  parent's original type relation.  Its `∀⊑∀` case can consume
  `ΛPostWindowGeometry.finalBody⊑ᵂ`.  Its one-sided `∀⊑` recursion would
  still need a post-top bridge, but only for the controlled front-fresh child
  plan used by that structural recursion, rather than for an arbitrary alias
  or fresh smart-comma premise.  This route is not yet machine-checked; it is
  the first alternative to test at the next statement-first pass.

No relation change, postulate, hole, catch-all clause, or weakened statement
was added.
