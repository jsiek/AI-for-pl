# `shifted-source-catchup-Λ-inversion` proof attempts

This note records the proof search for replacing the
`shifted-source-catchup-Λ-inversion` postulate in `proof.Catchup`.

## Attempt 1: plain shifted reduction inversion

Rejected as too weak.  The tempting lemma says that if
`⇑ᵗᵐ N —↠[ χs ] W`, then there are `χs′` and `W′` such that
`N —↠[ χs′ ] W′` and `W = ⇑ᵗᵐ W′`.  This fails for a pure `β-Λ•`
step:

`(⇑ᵗᵐ (Λ V •)) —→ (renameᵗᵐ (extᵗ suc) V) [ zero ]ᵀ`,

which simplifies to `V`, not to `⇑ᵗᵐ (V [ zero ]ᵀ)`.

The final catchup goal is shaped to account for this: it asks for a relation
on `⇑ᵗᵐ W′` after moving the enclosing `⊒Λ` binder back outside the emitted
store prefix.

## Attempt 2: apply `predᵗ` to the shifted reduction

Promising but not a stand-alone simulation theorem.  Setting
`W′ = renameᵗᵐ predᵗ W` handles the `β-Λ•` example, and a shifted bind
change can be pulled back to `bind (renameᵗ predᵗ A)`.

The obstacle is that `predᵗ` is not injective.  A shifted `tag-untag-bad`
step can compare `＇ zero` and `＇ suc zero`, but after applying `predᵗ` both
ground tags collapse to `＇ zero`.  Such a bad step should not occur on a path
that catches up to a value, because it produces `blame`, but proving that
requires an additional invariant such as "a reduction sequence that reaches a
value never takes a blame-producing bad tag/unseal branch".

## Attempt 3: store-prefix commutation only

Rejected as incomplete.  The store-shape equation needed by `⊒Λ` is not merely
`combineStoreNrw-⇑ˢ`.  The recursive catchup premise has emitted source-only
entries in front of the fresh `zero ꞉= ★ ⊒` entry:

`combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)`.

The conclusion needs that fresh entry outside the emitted prefix:

`(zero ꞉= ★ ⊒) ∷ ⇑ˢ (combineStoreNrw π′ σ)`.

So the proof needs a term-narrowing transport that commutes the emitted
source-only prefix under the enclosing type binder while simultaneously
rewriting the target term and coercion with `applyTermsUnderTyBinders` and
`applyCoercionUnderTyBinders`.

## Attempt 4: inline the recursive catchup under the outer `⊒Λ`

Potentially viable, but too large for a local replacement of the postulate.
Instead of accepting the abstract recursive result
`⇑ᵗᵐ N —↠[ χs ] W`, one can define a specialized catchup theorem for the
premise

`suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ [] ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p`

that directly returns the outer conclusion for
`Δ ∣ σ ∣ [] ⊢ N ⊒ Λ V′ ∶ gen A p`.

This avoids a general inverse theorem for arbitrary reductions, because each
case knows which term-imprecision constructor produced the recursive catchup.
However, the proof duplicates almost the entire `catchup-lemma` case structure
under an outer `⊒Λ` wrapper.  The `extend`, `split`, `cast+⊒`, `cast-⊒`, and
`ν⊒` cases still need the same emitted-prefix transports or the other
catchup-case postulates, just at the wrapped store shape.  So this is a
possible refactor, not a small proof of the existing postulate.

## Attempt 5: unshift every reduction step with `predᵗ`

Rejected as a direct one-step lemma, but still a useful decomposition if a
finality invariant is added.  Define the unshifted result as
`renameᵗᵐ predᵗ W` and try to prove

`renameᵗᵐ predᵗ M —→[ unshift χ ] renameᵗᵐ predᵗ M′`

from `M —→[ χ ] M′`.  This works for the ordinary β/cast/ν/context cases,
including `β-Λ•`: the `open0-ext-suc-cancelᵐ` and
`renameᵗᵐ-pred-ext-suc` lemmas account for the type binder.

The one-step theorem is false for `tag-untag-bad`.  A shifted reduction may
compare `＇ zero` with `＇ suc zero`; after `predᵗ` both become `＇ zero`, so the
unshifted source has an ok tag/untag redex while the shifted target is `blame`.
The actual catchup path ends in a `Value W`, so such a branch should be
unreachable in this theorem, but that requires a separate finality lemma:
after a blame-producing step, the deterministic evaluation context can never
reach a value.  The current reduction library has `value-no-step` and runtime
preservation, but no "bad/blame branch cannot later become a value" or
determinism lemma strong enough to discharge this branch.

Checked sub-obligation: `proof.ReductionProperties` now contains the bare
`blame` base facts `blame-not-value`, `blame-no-pure-step`, `blame-no-step`,
and `blame-no-↠-value`.  These are not enough for the full bad-branch case,
because a bad step may first produce `blame` inside an evaluation context
before the existing blame-propagation rules reduce the whole term to bare
`blame`.

The same file also now has first-order propagation finality for
`blame · M`, `blame ⟨ c ⟩`, `ν A blame c`, and `blame ⊕[ op ] M`.  The
right-argument forms `V · blame` and `V ⊕[ op ] blame` still require a local
value-finality lemma to rule out simultaneous stepping of the value side.

Follow-up: `proof.ReductionProperties` now also has the reduction-local
`value-no-pure-step` and `value-no-step` lemmas, plus finality for the
right-argument forms `V · blame` and `V ⊕[ op ] blame`.  This still does not
prove the full bad-branch exclusion for arbitrary nested evaluation contexts,
but the one-frame cases needed by the reduction constructors are now available.

Stronger checked sub-obligation: the same file now defines
`NoValueReachable M` and proves closure through the evaluation-context forms
`L · M`, `V · M`, `M ⟨ c ⟩`, `ν A M c`, `L ⊕[ op ] M`, and
`V ⊕[ op ] M`.  This is the reusable shape needed to rule out
`tag-untag-bad` after applying `predᵗ`: if the shifted bad step produces a
doomed term, the rest of the catchup reduction cannot end in `Value W`.

The exact redex lemma `tag-untag-bad-noValue` is also checked: for
`G ≢ H`, no reduction from `V ⟨ G ! ⟩ ⟨ H ？ ⟩` can end in a value.  Combined
with the `NoValueReachable` context-closure lemmas, this should discharge the
bad-tag branch of a future value-final shifted-reduction inversion.

## Attempt 6: general one-step `predᵗ` simulation

Rejected as too broad.  After adding the checked
`renameᵗᵐ-subst` lemma in `proof.NuTermProperties`, the β cases have the
right algebra: type renaming commutes with term substitution, and
`renameᵗᵐ-open-commute` handles type application.

The obstacle is `ν-step`.  For an arbitrary term
`ν A V c —→[ bind A ] ((⇑ᵗᵐ V) •) ⟨ c ⟩`, reducing
`renameᵗᵐ predᵗ (ν A V c)` produces the cast
`renameᶜ (extᵗ predᵗ) c`, while `renameᵗᵐ predᵗ` of the target contains
`renameᶜ predᵗ c`.  These are not equal in general.  The equality holds when
the `ν` redex itself is known to come from a shifted source, because then
`c = renameᶜ (extᵗ suc) c₀` and `renameᶜ-pred-ext-suc` cancels it.

So the next reduction inversion should not be stated for arbitrary one-step
reduction.  It needs an explicit "reachable from a shifted source" invariant
or should be proved directly by induction on the particular reduction sequence
from `⇑ᵗᵐ N`.

## Useful invariant: emitted binds are star binds

The store evidence is stronger than it first appears.  In both the `⊒Λ` and
`⊒⟨ν⟩` shifted-source obligations, the recursive catchup gives
`Π′ ≡ []` and `Δ′ ⊢ π ꞉ Π ⊒ˢ Π′`.  Therefore every nonempty constructor of
`π` must be `⊒ˢ-left`; `⊒ˢ-right` and `⊒ˢ-both` are impossible because they
would make the target store nonempty.

Since each `⊒ˢ-left` entry contributes `(X , ★)` to the source store, any
matching emitted `bind A` in the history equation `Π ≡ applyStores χs []`
must contribute a store head equal to ★.  In other words, the emitted bind
history relevant to this theorem is star-only.  This means the proof should
not need a general "unshift arbitrary bind type" operation for `χs`; the hard
parts are instead:

1. value-final reduction inversion/simulation for the source term, and
2. term-imprecision transport that moves source-only star entries across the
   fresh target-only `zero ꞉= ★ ⊒` binder while rewriting target terms and
   coercions with the under-binder actions.

The prose notes describe this situation as catchup under `σ, α:=★`, but the
Agda `⊒Λ` constructor is more precise about polarity: the fresh entry is
target-only, `(zero ꞉= ★ ⊒)`, while the emitted prefix from `π⊒ : Π ⊒ˢ []`
is source-only.  Treating the fresh entry as source-only leads to the wrong
transport problem.

## Attempt 7: generic source-side `⇑ᵗᵐ ∘ predᵗ` transport

Rejected as too broad.  A tempting transport is:

`Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ c`
implies
`Δ ∣ σ ∣ γ ⊢ ⇑ᵗᵐ (renameᵗᵐ predᵗ M) ⊒ T ∶ c`.

The simple constructors rebuild, but the `split` constructor already fails.
Its conclusion source has shape `N [ αᵢ ]ᵀ`; after the proposed transform the
source is `⇑ᵗᵐ (renameᵗᵐ predᵗ (N [ αᵢ ]ᵀ))`, which is not the source shape
produced by `split`.  This confirms that the needed transport must be indexed
by the emitted store history and must rebuild the specific split/exchange
shape; it cannot be a standalone source-renaming admissibility lemma.

## Attempt 8: value-only `⇑ᵗᵐ ∘ predᵗ` transport

Rejected as still too broad.  I probed the apparently weaker theorem that, if
both endpoints are values and

`suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ [] ⊢ W ⊒ T ∶ p`,

then the source may be replaced by `⇑ᵗᵐ (renameᵗᵐ predᵗ W)`.
The value restriction removes some top-level cases, but value constructors
still recurse into arbitrary non-value subderivations.  In the `ƛ⊒ƛ` case,
for example, rebuilding the outer value immediately requires the body
transport

`N ⊒ N′` implies `⇑ᵗᵐ (renameᵗᵐ predᵗ N) ⊒ N′`.

That is exactly the generic transport from Attempt 7, now under a lambda body.
Similarly, a casted value can change a source tag from `＇ zero` to
`＇ suc zero` while the coercion index is fixed, so casts need a genuine
binder-exchange/coercion-index transport rather than a value-final shortcut.

Conclusion: the shifted-source inversion needs a history-indexed
binder-exchange theorem that commutes emitted source-only star binders past
the fresh target-only binder and simultaneously transforms source terms,
target terms, and coercion indices.  Restricting to final values does not avoid
that structural work.

## Attempt 9: checked zero-emission beta probe

This found a concrete obstruction to the current standalone statement of
`shifted-source-catchup-Λ-inversion`.

The checked probe in `proof/TraceProbe.agda` uses

`probe-body = (ƛ (` 0)) ⟨ id (＇ 0) ↦ id (＇ 0) ⟩`

and

`probe-N = (Λ probe-body) •`.

Under the right-only fresh binder `(0 ꞉= ★ ⊒) ∷ []`, the probe constructs

`1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ [] ⊢ probe-body ⊒ ƛ (` 0) ∶ probe-c`

where `probe-c = id (＇ 0) ↦ id (＇ 0)`, and also constructs the shifted beta
reduction

`⇑ᵗᵐ probe-N —↠[ keep ∷ [] ] (renameᵗᵐ (extᵗ suc) probe-body) [ zero ]ᵀ`.

The beta target is definitionally the original `probe-body`, so these are the
premises expected by the broad inversion lemma with zero emitted binds.  But
the conclusion would need to relate

`⇑ᵗᵐ (probe-body [ zero ]ᵀ)`

to `ƛ (` 0)` at the same coercion index `probe-c`.  The source cast in this
term is shifted to `id (＇ 1) ↦ id (＇ 1)`, while the context is still only
`1`.  The probe checks the key obstruction:

`1 ∣ (0 ꞉= ★ ⊒) ∷ [] ⊢ r ≈ ⇑ᶜ probe-c ⨾ⁿ p ∶ A ⊒ B → ⊥`.

The contradiction is that typing `⇑ᶜ probe-c` requires typing
`id (＇ 1)` in type context `1`, which would require `WfTy 1 (＇ 1)`.

This does not yet refute the actual `catchup-lemma` case, because the probe
does not provide the original premise

`suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ [] ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p`.

It does show that the standalone postulate is too broad: it accepts final
catchup states that cannot arise from the original `⊒Λ` premise.  The next
alternative proof should therefore keep the original term-narrowing premise in
the shifted inversion statement, or prove the `⊒Λ` catchup case directly by
induction on that premise.  A reduction-only inversion cannot be correct at
this level of generality.

## Attempt 10: direct `⊒Λ` cases by source value shape

Promising, partially checked.  Instead of matching on the constructor that
derives the inner premise

`suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ [] ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p`,

match on the original source `N`.  If `N` is already a syntactic value,
detected with `TypeCheck.value?`, the outer `⊒Λ` catchup can use zero source
steps and rebuild with the original premise unchanged.

The general source-value branch now checks in `proof/Catchup.agda`.  It covers
lambdas, constants, polymorphic values whose bodies are values, and inert
casted values:

`catchup-lemma (Λ vV′) (⊒Λ {N = N} pᶜ N⊒V′) with value? N`.

The first failed version matched specifically on an inner `ƛ⊒ƛ` derivation.
Agda correctly rejected that coverage split because the same shifted lambda
source can also be produced by `split`.  Matching on source valuehood instead
avoids that false distinction and preserves split/extend/cast derivations
unchanged inside the rebuilt `⊒Λ`.

This does not solve the non-value source cases.  In particular, it does not yet
handle sources that become values only after left-cast reduction, `ν` opening,
or nested polymorphic catchup.  It is still useful evidence that the
premise-aware route should be organized around source shape plus the original
term-narrowing derivation, not around final reduction alone.

## Attempt 11: full contradiction from the beta probe

Incomplete.  I tried to strengthen `proof/TraceProbe.agda` from the checked
composition obstruction to a full inversion lemma:

`1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ [] ⊢
  ⇑ᵗᵐ (probe-body [ zero ]ᵀ) ⊒ probe-V′ ∶ probe-c → ⊥`.

The `cast-⊒` branch reduces to the checked `no-probe-compose` fact.  The
`cast+⊒` branch is morally the same, because the source cast coercion is
self-dual, but Agda will not accept the case split without an explicit
injectivity/inversion lemma for the dual operation `-_`:

`M ⟨ - t ⟩ ≟ (ƛ (` 0)) ⟨ - ⇑ᶜ probe-c ⟩`.

An equality-indexed auxiliary with an explicit premise
`c ≡ - ⇑ᶜ probe-c` was tried too; it exposes the source as
`(ƛ (` 0)) ⟨ - ⇑ᶜ probe-c ⟩`, but the `cast+⊒` coverage split still gets
stuck on the same hidden `- t` unification.

I also tried a local recursive lemma saying that if `- t ≡ - ⇑ᶜ probe-c`,
then `t` cannot be typed as a narrowing in context `1`.  The first component
of a function coercion does reduce to the impossible `id (＇ 1)` case, but Agda
still needs a principled injectivity theorem for dual on function coercions to
extract that component equality from `- (t₁ ↦ t₂) ≡ - ⇑ᶜ probe-c`.

Do not repeat this pattern-match-only attempt.  To complete the formal
counterexample, first prove a small dual-inversion lemma for this exact
function coercion shape, or prove a more general source-cast inversion theorem
for term narrowing that exposes the composition side condition together with
the source-cast equality.

## Attempt 12: checked counterexample to the standalone postulate

Succeeded.  `proof/TraceProbe.agda` now proves

`shifted-source-catchup-Λ-inversion-counterexample : ⊥`

by importing `shifted-source-catchup-Λ-inversion` and instantiating it with the
beta probe from Attempt 9:

`probe-N = (Λ probe-body) •`

where

`probe-body = (ƛ (` 0)) ⟨ id (＇ 0) ↦ id (＇ 0) ⟩`.

The postulate accepts the shifted reduction

`⇑ᵗᵐ probe-N —↠[ keep ∷ [] ] probe-W`

and the checked final relation

`1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ [] ⊢ probe-W ⊒ ƛ (` 0) ∶ probe-c`.

Its conclusion then produces an unshifted value reachable from `probe-N`.
The only such value is `probe-W`: the first step is forced to be `β-Λ•`, and
any further step from `probe-W` contradicts `value-no-step`.  The conclusion is
therefore forced to contain

`1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ [] ⊢ (ƛ (` 0)) ⟨ ⇑ᶜ probe-c ⟩ ⊒ ƛ (` 0) ∶ probe-c`,

which `no-probe-conclusion` refutes.

The source-cast inversion obstacle from Attempt 11 was solved without a new
postulate by using an equality-indexed auxiliary over the source cast coercion
and a small projection

`fun-left : Coercion → Coercion`.

Applying `cong fun-left` to `- t ≡ ⇑ᶜ probe-c` extracts the impossible left
component `- t₁ ≡ id (＇ 1)` from function coercions without requiring a global
dual-injectivity theorem.

This is a counterexample to the standalone
`shifted-source-catchup-Λ-inversion` statement, not to the original
`catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)` case.  The probe still does not provide the
original premise

`suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ [] ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p`.

Future proof work should replace the postulate with a premise-aware inversion
or prove the `⊒Λ` branch directly by induction on that premise.  A
reduction-only shifted-source inversion is now formally ruled out.

## Attempt 13: check whether the beta probe satisfies the real inner premise

Succeeded, and it explains why Attempt 12 is only a counterexample to the
standalone helper.  `proof/TraceProbe.agda` now checks

`no-probe-inner-premise :
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ ⇑ᵗᵐ probe-N ⊒ probe-V′ ∶ probe-c → ⊥`.

So the original beta probe cannot inhabit the actual premise carried by

`catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)`.

The reason is structural, not just an artifact of the chosen coercion:
`⇑ᵗᵐ probe-N` is a runtime type application at the source.  I moved the
general exclusion to `proof.TermNarrowingProperties`:

`type-app-source-no-value-target :
  Value V → Δ ∣ σ ∣ γ ⊢ L • ⊒ V ∶ p → ⊥`.

Using this lemma, the `catchup-lemma` `⊒Λ` branch now discharges the
`N = L •` and `value? N = nothing` subcase by contradiction before it can call
the false shifted-source helper.

This confirms the current proof search should keep using the real inner
term-narrowing premise.  It also rules out reusing the Attempt 12 probe as a
counterexample to the full catchup lemma.

## Attempt 14: exclude neutral non-values from the live `⊒Λ` branch

Succeeded.  I added another reusable source-shape lemma to
`proof.TermNarrowingProperties`:

`neutral-source-no-value-target :
  NeutralSource M →
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p → ⊥`,

where `NeutralSource` covers variables, applications, primitive additions, and
`blame`.  The proof is by induction on the term-narrowing derivation.  The
interesting cases are `extend`, `split`, `⊒Λ`, `⊒⟨ν⟩`, and target-cast
wrappers; the source shape is preserved through type opening/renaming, and
the target value is peeled when the target is an inert cast.

`proof/Catchup.agda` now uses the lemma to close these additional
`value? N = nothing` cases:

the variable case, `N = L · M`, `N = L ⊕[ op ] M`, and `N = blame`.

This is still not a full proof of the `⊒Λ` catchup case.  After these checked
exclusions, the remaining non-value source shapes that can plausibly satisfy
the real inner premise are:

- `N = Λ M` where `M` is not syntactically a value,
- `N = ν A L c`,
- `N = M ⟨ c ⟩` where the cast is not already an inert value.

The likely next route is a premise-aware helper by induction on the inner
term-narrowing derivation.  The cast cases probably need generated-coercion
composition lemmas, because an inner source cast
`⇑ᵗᵐ M ⟨ ⇑ᶜ t ⟩ ⊒ V′` must be converted into an outer catchup source
`M ⟨ t ⟩ ⊒ Λ V′` at a `gen` coercion.  I did not find an actual catchup-lemma
counterexample among these remaining shapes.

## Attempt 15: exclude non-value source lambdas

Succeeded.  The `N = Λ M` and `value? N = nothing` subcase is now closed in
`proof/Catchup.agda`.

The first direct lemma,

`Value V → Δ ∣ σ ∣ γ ⊢ Λ M ⊒ V ∶ p → Value M`,

ran into Agda's usual open-term unification problem in the `split` case:
from a conclusion source `N [ αᵢ ]ᵀ` Agda would not infer that `N` must be a
lambda just because the expected source was `Λ M`.

The checked version uses explicit source-shape witnesses instead:

- `LambdaSource M` records that the source has the form `Λ _`.
- `LambdaBodyValue M` records that the source is `Λ M₀` and `M₀` is a value.
- `lambda-source-value-target-body-value` proves that a lambda source related
  to any value target has a value body, preserving the source-shape witness
  through `extend`, `split`, `⊒Λ`, `⊒⟨ν⟩`, and target-cast wrappers.

This required small value-reflection helpers:

- `value?-none-no-value` turns a `value? M ≡ nothing` result into negative
  value evidence.
- `renameᵗᵐ-reflects-Value` and `renameᵗᵐ-reflects-LambdaBodyValue` invert
  type renaming for value shape.

In `Catchup.agda`, the branch for `N = Λ M` splits once more on `value? M`.
The `just` subcase returns the ordinary zero-step catchup witness.  The
`nothing` subcase reflects the value body out of the shifted inner premise and
contradicts `value? M ≡ nothing`.

After Attempts 13-15, the generic non-value fallback in the `⊒Λ` catchup
branch should only be reachable for source terms of these forms:

- `N = ν A L c`;
- `N = M ⟨ c ⟩` where the cast is not an inert value.

These are the real operational cases.  A full replacement for
`shifted-source-catchup-Λ-inversion` should focus there rather than on neutral
or syntactic-value shapes.

## Attempt 16: classify value-target `ν` sources

Partially succeeded as an exploratory Agda probe, then the temporary probe file
was deleted.  The reusable source-shape witness and preservation helpers are
now kept in `proof.TermNarrowingProperties`:

`NuSource M`

and checked a coverage proof for

`NuSource M → Value V → Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p → Set`.

The purpose was not the trivial `Set` conclusion; it was to ask Agda which
term-narrowing constructors can actually match a `ν` source with a value
target once the same explicit-source-witness style from Attempts 14-15 is used.

The checked classification was:

- `extend` and `split` preserve the `ν` source witness and recurse.
- `⊒Λ`, `⊒⟨ν⟩`, `⊒cast+`, and `⊒cast-` peel target value wrappers and recurse.
- `ν⊒` is the genuine base case.
- `α⊒α` can have a `ν`-shaped source, because `L • α` is encoded as
  `ν (＇ α) L (id (＇ zero))`, but it is impossible in the value-target setting
  because its target is also a non-value type-application encoding.
- `ν⊒ν` and `⊒ν` are impossible here because their targets are `ν` terms, not
  values.

So the remaining `N = ν A L c` branch is not blocked on constructor coverage:
the inner premise should eventually expose a `ν⊒` base.  The real obstruction
is later.  `catchup-ν⊒-catchup` produces a source reduction and relation for
the opened target body, while the outer `⊒Λ` catchup conclusion needs a final
relation to `Λ V′` at a generated coercion.  Bridging those requires the same
under-binder shifted-source relation that the false standalone inversion tried
to provide.

Do not repeat a blind reduction-only inversion here.  A useful next lemma would
either:

- strengthen the `ν` classification to return the `ν⊒` base plus enough
  wrapper history to rebuild the outer `⊒Λ` result, or
- prove a focused premise-aware shifted-source inversion only for sources that
  have already been classified down to `ν⊒`.

No counterexample to the full `catchup-lemma` was found in the `ν` source
classification.

## Attempt 17: inspect the non-inert cast source route

Partially explored, then strengthened by a checked constructor-coverage probe
in Attempt 18.  The surrounding catchup proof already handles top-level
source casts with the pattern:

1. recursively catch the cast body up to a source value;
2. lift the reduction through the cast;
3. invoke `left-widening-lemma` or `left-narrowing-lemma`;
4. compose emitted store prefixes.

For the `⊒Λ` branch, however, the cast appears inside the inner shifted premise:

`suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ []
  ⊢ ⇑ᵗᵐ (M ⟨ c ⟩) ⊒ V′ ∶ p`.

To reuse the existing cast catchup skeleton, the proof first needs inversion of
that inner term-narrowing derivation to expose a `cast+⊒` or `cast-⊒` source
cast premise, including its composition side condition.  This is the same kind
of missing infrastructure called out in `proof.LeftSealNarrowingInversion`:
that experiment gets stuck needing a transport principle like

`termNarrowing-resp-≈`.

So the next cast-focused step should not start by moving reductions around.
It should first prove a small source-cast inversion lemma, using an explicit
`CastSource` witness to get through `extend` and `split`, and decide whether
the required coercion transport can be proved from the existing endpoint
equivalence machinery.

## Attempt 18: classify value-target cast sources

Succeeded as a temporary Agda probe, then the probe file was deleted.  The
reusable source-shape witness and preservation helpers are now kept in
`proof.TermNarrowingProperties`.  I used the explicit-source-witness pattern
again:

`CastSource M`

with preservation lemmas for type renaming and opening.  The checked probe had
the shape

`CastSource M → Value V → Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p → Set`.

The useful fact is the accepted coverage split:

- `extend` and `split` preserve the cast-source witness and recurse.
- `⊒Λ` and `⊒⟨ν⟩` preserve the cast-source witness under `⇑ᵗᵐ` and recurse
  into the inner premise.
- `⊒cast+` and `⊒cast-` peel target inert casts and recurse.
- the genuine source-cast bases are exactly `cast+⊒` and `cast-⊒`.
- neutral, lambda, type-application, `ν`, primitive, and right-`ν` constructors
  are ruled out by the cast-source witness or the value-target proof.

This confirms the cast branch is not a constructor-search problem.  A useful
next lemma should package the same coverage split with a nontrivial result,
for example a `CastSourceValueTarget` datatype whose base constructors carry
the exposed `cast+⊒`/`cast-⊒` premise and whose recursive constructors record
the wrapper history.  That wrapper history is needed to rebuild the final
outer `⊒Λ` catchup result after applying the existing left widening/narrowing
catchup skeleton.

Do not try to prove the cast branch by starting from the reduction
`⇑ᵗᵐ (M ⟨ c ⟩) —↠ W`; that repeats the false standalone-inversion pattern.
The checked direction is to invert the inner term-narrowing premise first.

## Attempt 19: package cast-source inversion with wrapper history

Succeeded after making the constructor indices explicit.  I first tried to make
the cast-source classification return a fully dependent witness indexed by the
exact term-narrowing derivation:

`CastSource M → Value V → Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p → Set₁`.

The intended base constructors carried the exposed `cast+⊒` or `cast-⊒`
premise, while recursive constructors recorded `extend`, `split`, `⊒Λ`,
`⊒⟨ν⟩`, `⊒cast+`, and `⊒cast-` wrappers.  Agda rejected the first version with
many unsolved metas.  The failures were not from a single bad branch; the
datatype constructors themselves left hidden stores, endpoints, and coercion
indices underdetermined.  In particular, `extend`, `split`, `⊒Λ`, and
cast-wrapper constructors all forced Agda to infer the source/target coercion
endpoints of their premises from an indexed witness argument, which it would
not solve.

The checked version in `proof.TermNarrowingProperties` fixes that by spelling
out the hidden endpoints and premise derivations in each constructor.  One
minor wrinkle was the `⊒⟨ν⟩` value proof: the target term is indexed by
`gen A s`, but the caller's `Value` proof may contain any proof of
`Inert (gen A s)`, so the constructor must preserve that inert proof instead
of choosing the canonical `gen A s` proof.

This is now a real wrapper-history artifact, not just a coverage probe:

`cast-source-value-target-inversion :
  CastSource M → Value V → Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  CastSourceValueTarget src vV M⊒V`.

It exposes that cast sources with value targets bottom out only at `cast+⊒` or
`cast-⊒`, with the intervening wrappers recorded in the witness.  It still does
not by itself rebuild the `⊒Λ` catchup branch; the next step is to consume this
history and transport the exposed cast-base catchup result back through the
recorded wrappers.

## Attempt 20: split the exact inner `⊒Λ` premise by remaining source shape

Failed for the same constructor-form-index reason as earlier broad premise
splits.  I tried a temporary probe over the exact inner premise shape

`suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ []
  ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p`

and then specialized it to the remaining source forms

`N = ν A L c`

and

`N = M ⟨ c ⟩`.

Even in those specialized probes, Agda got stuck deciding whether the `split`
constructor should be a case, because it had to solve equations of the form

`N₀ [ αᵢ ]ᵀ ≟ ⇑ᵗᵐ (ν A L c)`

or

`N₀ [ αᵢ ]ᵀ ≟ ⇑ᵗᵐ (M ⟨ c ⟩)`.

So specializing the outer source shape is not enough.  The next viable route
still needs an explicit source-shape witness threaded through `split`, or a
split-specific transport that carries the opening evidence needed to rebuild
the catchup result.

## Attempt 21: package `ν`-source inversion with wrapper history

Succeeded.  To match the checked cast-source wrapper history from Attempt 19,
I added a dependent `ν`-source witness in `proof.TermNarrowingProperties`:

`nu-source-value-target-inversion :
  NuSource M → Value V → Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  NuSourceValueTarget src vV M⊒V`.

The witness records the same wrapper constructors that can preserve a
value-target source shape:

- `extend` and `split`;
- `⊒Λ` and `⊒⟨ν⟩`;
- `⊒cast+` and `⊒cast-`.

Its only genuine base constructor is `ν⊒`.  The other `ν`-shaped term
constructors do not produce value targets here:

- `ν⊒ν` and `⊒ν` have `ν` targets, so their value target is impossible;
- `α⊒α` can have a syntactically `ν` source because `L • α` expands to a
  `ν`, but its target is also a type-application encoding and hence not a
  value.

This closes the constructor-coverage gap for the remaining non-value source
shapes in the live `⊒Λ` branch: `ν` sources now expose a `ν⊒` base and cast
sources expose `cast+⊒`/`cast-⊒` bases.  It still does not finish the branch.
The next proof obligation is a consumer for these histories: run the appropriate
base catchup (`catchup-ν⊒-catchup`, `left-widening-lemma`, or
`left-narrowing-lemma`) and replay the recorded wrappers while transporting the
emitted store prefix and opening evidence back to the outer `⊒Λ` conclusion.

## Attempt 22: classify the live non-value `⊒Λ` fallback

Succeeded.  I packaged the hand-written source exclusions from Attempts 13-16
into a reusable checked classifier:

`shifted-source-remainder :
  value? N ≡ nothing →
  Value V →
  Δ ∣ σ ∣ γ ⊢ ⇑ᵗᵐ N ⊒ V ∶ p →
  ShiftedSourceRemainder vV N⊒V`.

The classifier pattern matches on the original, unshifted `N`:

- values are impossible from `value? N ≡ nothing`;
- lambda sources use `lambda-source-value-target-source-value` to contradict
  non-value bodies;
- runtime type applications use `type-app-source-no-value-target`;
- neutral sources use `neutral-source-no-value-target`;
- `ν` sources return the `NuSourceValueTarget` history from Attempt 21;
- cast sources return the `CastSourceValueTarget` history from Attempt 19.

I then threaded this classifier into the actual `catchup-lemma` `⊒Λ` fallback.
The branch still calls `catchup-⊒Λ-catchup`, so this is not the final proof, but
the live code now exposes exactly two checked subgoals:

- `remainder-nu hist`;
- `remainder-cast hist`.

This avoids repeating the source-shape exclusions and gives the next proof
attempt a concrete entry point: replace the call to `catchup-⊒Λ-catchup` in
each classified branch by a consumer for the corresponding history.

## Attempt 23: expose the real base premises in the live fallback

Succeeded.  The wrapper-history witnesses from Attempts 19 and 21 still left
the live `⊒Λ` fallback one step away from the usable premises.  I added base
views in `proof.TermNarrowingProperties`:

`nu-source-value-target-base :
  NuSourceValueTarget src vV M⊒V → NuSourceBase`

and

`cast-source-value-target-base :
  CastSourceValueTarget src vV M⊒V → CastSourceBase`.

These functions recurse through the recorded wrapper history and expose the
genuine base constructor:

- `nu-base`, carrying the `ν⊒` premise;
- `cast-base+`, carrying the `cast+⊒` premise;
- `cast-base-`, carrying the `cast-⊒` premise.

I then threaded the base views into the actual `catchup-lemma` `⊒Λ` fallback.
The branch still delegates to `catchup-⊒Λ-catchup`, so this is not a proof of
the case yet, but the live code now presents the final missing work in three
checked base cases:

- `remainder-nu hist | nu-base vBase pBaseᶜ bodyBase`;
- `remainder-cast hist | cast-base+ vBase pBaseᶜ base≈ bodyBase`;
- `remainder-cast hist | cast-base- vBase pBaseᶜ base≈ bodyBase`.

The next attempt should use these base premises directly:

- for `nu-base`, apply `catchup-ν⊒-catchup` at the base and then replay the
  recorded wrappers;
- for `cast-base+` and `cast-base-`, use the existing left
  widening/narrowing skeleton and then replay wrappers.

The remaining hard part is still wrapper replay: the base catchup result must be
transported back through the `extend`, `split`, `⊒Λ`, `⊒⟨ν⟩`, and target-cast
history while preserving the emitted store-prefix and opening evidence.

## Attempt 24: expose empty-context bases and try direct base recursion

Partly succeeded, but the direct proof route failed termination.

The base views from Attempt 23 were too lossy for an actual base consumer: they
hide the term context `γ`.  In the live `catchup-lemma` branch the relevant
context is definitionally `[]`, but after erasing the wrapper path Agda sees the
exposed `ν⊒` body under an arbitrary-looking context such as
`Data.List.map ⇑ᶜ γ`, so a direct call to `catchup-lemma` does not type-check.

I added checked empty-context variants:

`nu-source-value-target-base-empty :
  NuSourceValueTarget {γ = []} src vV M⊒V → NuSourceBaseEmpty`

and

`cast-source-value-target-base-empty :
  CastSourceValueTarget {γ = []} src vV M⊒V → CastSourceBaseEmpty`.

These variants recurse through `extend`, `split`, `⊒Λ`, `⊒⟨ν⟩`, `⊒cast+`,
and `⊒cast-`, but keep the fact that all exposed base premises have context
`[]`.  The live fallback now uses these empty-context views, so the remaining
three base cases expose:

- `nu-base-empty vBase pBaseᶜ bodyBase`;
- `cast-base-empty+ vBase pBaseᶜ base≈ bodyBase`;
- `cast-base-empty- vBase pBaseᶜ base≈ bodyBase`.

I then probed the obvious next step in the `nu-base-empty` case:

`catchup-lemma (renameᵗᵐ-preserves-Value suc vBase) bodyBase`.

This type-checks far enough to show the empty-context view fixed the context
problem and that Agda has refined the outer source to a syntactic `ν A L c`.
However, the termination checker rejects the recursive call because `bodyBase`
comes from the inversion/base-view computation on `hist`, not from a direct
structural pattern match on the current `⊒Λ` premise.  So the base consumer
cannot simply call `catchup-lemma` again on the exposed base body inside the
same definition.

Conclusion: the next viable route still needs a history-indexed replay or
continuation that consumes the already-available recursive catchup result for
`N⊒V′`, or a refactoring of `catchup-lemma` into a mutually recursive
specialized helper whose recursive calls are structurally visible to Agda.  Do
not repeat the direct base-recursive call unless the recursion structure has
first been changed.

## Attempt 25: direct inner-constructor clauses in `catchup-lemma`

Failed.  I tried to avoid the indirect inversion/base-view termination problem
by adding temporary direct clauses for the outer case

`catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)`.

The idea was to pattern match on the actual inner `N⊒V′` derivation, so a
recursive call on a premise such as a `ν⊒`, `cast+⊒`, or `cast-⊒` body would be
structurally visible to Agda.

The unrestricted `ν⊒` clause failed because Agda could not decide whether the
constructor should apply through the shifted-source index:

`ν ★ N (⇑ᶜ p) ≟ ⇑ᵗᵐ N₁`.

Specializing the outer source to a syntactic `ν ★ L c` did not help; the stuck
equation became

`ν ★ N (⇑ᶜ p) ≟ ⇑ᵗᵐ (ν ★ L c)`.

The cast-source probes had the same shape.  A temporary `cast+⊒` clause for
`N = M ⟨ c ⟩` got stuck on

`M ⟨ - t ⟩ ≟ ⇑ᵗᵐ (M₁ ⟨ c ⟩)`,

and a temporary `cast-⊒` clause caused coverage to get stuck on a possible
`split` overlap:

`N [ αᵢ ]ᵀ ≟ ⇑ᵗᵐ (M ⟨ x ⟩)`.

So direct inner-constructor clauses do not make the recursive structure visible
enough.  The source-shape histories from Attempts 21-24 are still needed to
cross `split` and shifted coercion indices.  A viable structural refactor would
need to recurse on those histories themselves, or define a separate
well-founded measure for extracted premises; simply adding more direct
`catchup-lemma` clauses repeats the same unification failure.

## Attempt 26: restore value-final no-value-reachable infrastructure

Succeeded.  The earlier notes from Attempt 5 referred to checked
`NoValueReachable` helpers, but the current branch only had the smaller
`value-no-step` facts in `proof.ReductionProperties`.  I restored the reusable
finality toolbox needed by the value-final `predᵗ` simulation route:

- `blame-not-value`, `blame-no-pure-step`, `blame-no-step`, and
  `blame-no-↠-value`;
- `NoValueReachable`;
- closure through evaluation-context forms `noValue-·₁`, `noValue-·₂`,
  `noValue-cast`, `noValue-ν`, `noValue-⊕₁`, and `noValue-⊕₂`;
- the exact bad tag/untag lemma
  `tag-untag-bad-noValue`.

This does not by itself prove the shifted-source inversion.  Its purpose is to
make the non-injective `predᵗ` branch usable: if a shifted bad tag/untag step
would become an ok tag/untag step after applying `predᵗ`, the original shifted
step produces a term from which no value is reachable, contradicting the
catchup premise's final `Value W`.

The next reduction-inversion attempt can now cite `tag-untag-bad-noValue`
lifted through the context-closure lemmas instead of re-proving bad-branch
finality locally.

## Attempt 27: β algebra for the value-final `predᵗ` simulation

Succeeded.  The next one-step `predᵗ` simulation needs to rewrite β targets
after applying a type-variable predecessor.  I added checked substitution
algebra in `proof.NuTermProperties`:

- `substˣᵐ-cong`;
- `renameᵗᵐ-substˣᵐ`;
- `renameᵗᵐ-single-subst`.

Then I added checked redex-specific lemmas in `proof.ReductionProperties`:

- `pred-β-step`;
- `pred-β-Λ•-step`;
- `pred-β-∀•-step`;
- `pred-β-gen•-step`.

These lemmas do not yet give the full shifted-source inversion.  They verify
that the β and type-application redexes of a future value-final `predᵗ`
one-step simulation have the right target equalities.  The remaining hard
branch for that simulation is still the bad tag/untag collapse, now supported
by Attempt 26's no-value-reachable lemmas.

## Attempt 28: pure-step `predᵗ` simulation with a doomed branch

Succeeded as a checked local reduction fact.  I added

`PredPureStepView M N`

to `proof.ReductionProperties`, with two outcomes for a pure step `M —→ N`:

- `renameᵗᵐ predᵗ M —→ renameᵗᵐ predᵗ N`;
- `NoValueReachable (renameᵗᵐ predᵗ N)`.

The corresponding theorem

`pure-pred-step-view : M —→ N → PredPureStepView M N`

uses the beta algebra from Attempt 27 for the β and runtime type-application
redexes.  All ordinary cast/blame redexes simulate directly after applying
`predᵗ`.  The `tag-untag-bad` case takes the doomed branch by returning
`blame-no-↠-value`, avoiding the false injectivity assumption for `predᵗ`.

This is deliberately weaker than the rejected reduction-only inversion.  It
does not handle `ν-step`, whose binder/coercion target is not a direct generic
`predᵗ` image, and it does not replay the term-narrowing wrapper history needed
by the live `⊒Λ` fallback.  The useful next reduction fact would have to be
shift-aware or premise-aware: a generic store-change `predᵗ` simulation is still
too broad, but a step literally arising under the original shifted source may be
invertible after using `renameᵗᵐ-pred-suc` and
`renameᶜ-pred-ext-suc`.

## Attempt 29: value-final `predᵗ` simulation for all-`keep` traces

Succeeded.  The first version of the trace lemma assumed that every `keep`
step was literally a `pure-step`, but Agda correctly rejected the coverage:
`ξ-·₁`, `ξ-·₂`, `ξ-⟨⟩`, `ξ-ν`, `blame-ν`, `ξ-⊕₁`, and `ξ-⊕₂` can also emit
`keep`.

I generalized the one-step view to

`PredKeepStepView M N`

and proved

`keep-pred-step-view : M —→[ keep ] N → PredKeepStepView M N`.

The contextual cases recurse on the inner `keep` step.  If the inner step
simulates, the proof rebuilds the same evaluation-context step after applying
`predᵗ`; if it is doomed, the proof lifts `NoValueReachable` through the
corresponding context using `noValue-·₁`, `noValue-·₂`, `noValue-cast`,
`noValue-ν`, `noValue-⊕₁`, or `noValue-⊕₂`.

With that view, the all-`keep` multi-step theorem checks:

`pure-pred-↠-value :
  AllKeep χs →
  M —↠[ χs ] V →
  Value V →
  renameᵗᵐ predᵗ M —↠[ χs ] renameᵗᵐ predᵗ V`.

This closes the pure/contextual part of the value-final `predᵗ` route.  It
still does not solve the live `⊒Λ` case, because the emitted catchup trace can
contain `bind` entries from `ν-step`.  A generic `predᵗ` simulation for `bind`
steps is not true without extra shifted-source invariants: the coercion under a
`ν` binder uses `extᵗ`, while the cast left after the step is not a generic
`predᵗ` image.  The next proof step must therefore either be a shift-aware
`bind` inversion or a term-narrowing-history replay, not a generic extension of
`keep-pred-step-view`.

## Attempt 30: all-`keep` traces from `ν` cannot end in a value

Succeeded.  I added

`allKeep-ν-no-value :
  AllKeep χs →
  ν A M c —↠[ χs ] V →
  Value V →
  ⊥`

to `proof.ReductionProperties`.

The proof is by induction on the all-`keep` trace.  A `ν` source has only two
possible `keep` steps: reducing under the `ν` with `ξ-ν`, or propagating
`ν A blame c` to `blame`.  The `ξ-ν` case recurses on the tail; the
`blame-ν` case uses `blame-no-↠-value`.

This is useful for the live `remainder-nu` branch: if
`⇑ᵗᵐ N` is a shifted `ν` source and the recursive catchup trace reaches a
value, the emitted store-change list cannot be all `keep`.  Therefore the
remaining `ν` case genuinely requires a `bind`-aware inversion/replay argument;
it cannot be discharged by the all-`keep` `predᵗ` simulation from Attempt 29.

## Attempt 31: integrate the all-`keep` exclusion into `remainder-nu`

Succeeded.  The live `catchup-lemma` `⊒Λ` fallback now splits the
`remainder-nu` branch with `storeChangesLastBind χs`.

The `no-bind keeps` subcase is discharged by

`allKeep-ν-no-value keeps ⇑N↠W vW`.

This works because the `remainder-nu` constructor preserves enough index
information for Agda to know that the shifted source reduction really starts
from a syntactic `ν` term.  The branch therefore cannot reach the recursive
catchup value `W` without emitting a `bind`.

The remaining live `remainder-nu` branch is now explicitly the

`last-bind χs₀ Aχ keeps keeps-ok`

subcase.  It still delegates to `catchup-⊒Λ-catchup`, so this is not the final
proof, but the impossible no-bind path has been removed from the hard case.

## Attempt 32: package the all-`keep` unshifted reduction

Succeeded for the reduction half.  I added

`pure-pred-↠-shifted-value :
  AllKeep χs →
  ⇑ᵗᵐ M —↠[ χs ] V →
  Value V →
  M —↠[ χs ] renameᵗᵐ predᵗ V`.

This is just `pure-pred-↠-value` specialized to a shifted source, followed by
`renameᵗᵐ-pred-suc` to rewrite the source back to `M`.

This is useful but not a proof of any remaining `⊒Λ` fallback branch.  To
rebuild the final `⊒Λ` relation, one needs an inner source relation for
`⇑ᵗᵐ (renameᵗᵐ predᵗ V)`, while the recursive catchup result provides a
relation for `V`.  Turning the latter into the former is exactly the
source-relation part of the false standalone shifted-source inversion.  The
all-`keep` reduction lemma is safe; a corresponding relation lemma must remain
premise-aware or it will repeat the `TraceProbe` counterexample.

## Attempt 33: mechanize the star-bind invariant for empty targets

Succeeded.  I added two small store-shape lemmas in `proof.Catchup`:

`⊒ˢ-empty-source-head-star :
  Δ ⊢ π ꞉ (α , A) ∷ Σ ⊒ˢ [] →
  A ≡ ★`

and

`last-bind-empty-target-star :
  AllKeep keeps →
  Π ≡ applyStores (χs ++ bind A ∷ keeps) [] →
  Δ ⊢ π ꞉ Π ⊒ˢ [] →
  A ≡ ★`.

The first lemma is just inversion on store narrowing to the empty target store:
the only possible nonempty constructor is `⊒ˢ-left`, whose source head is
`★`.  The second combines that inversion with `applyStores-last-bind` and
`⇑ᵗ-★-inv`.

The live `remainder-nu`/`last-bind` branch now calls
`last-bind-empty-target-star` and carries the local fact

`Aχ≡★ : Aχ ≡ ★`.

Trying to pattern-refine the branch directly with `refl` got stuck in Agda's
nested `with` abstraction, so the checked version keeps the equality as an
explicit local witness.  This still does not prove the branch, but it makes the
remaining replay obligation match the paper intuition: the final emitted bind
is source-only star.

## Attempt 34: split the reduction trace at the final bind

Succeeded.  I added two multi-step decomposition lemmas in
`proof.ReductionProperties`:

`↠-split-++ :
  M —↠[ χs ++ χs′ ] W →
  ∃[ P ] ((M —↠[ χs ] P) × (P —↠[ χs′ ] W))`

and

`↠-split-last-bind :
  M —↠[ χs ++ bind A ∷ keeps ] W →
  ∃[ P ] ∃[ Q ]
    ((M —↠[ χs ] P) × (P —→[ bind A ] Q) × (Q —↠[ keeps ] W))`.

The live `remainder-nu`/`last-bind` branch now applies
`↠-split-last-bind` to the recursive catchup trace, so the remaining delegated
case has explicit local evidence

`⇑N↠P : ⇑ᵗᵐ N —↠[ χs₀ ] P`,
`P→Q : P —→[ bind Aχ ] Q`, and
`Q↠W : Q —↠[ keeps ] W`.

Together with Attempt 33, the same branch also has `Aχ≡★ : Aχ ≡ ★` and
`AllKeep keeps`.  This still does not identify `P→Q` with the specific
outer/base `ν-step`; a bind step can be nested under contexts after earlier
emitted binds.  The next replay lemma needs to connect this isolated final
star bind to the `nu-base-empty` history rather than analyzing the raw
reduction trace alone.

## Attempt 35: invert a top-level `ν` final bind

Succeeded as a checked local step-inversion lemma.  I added

`ν-bind-step-value-tail-inv :
  ν A L c —→[ bind B ] Q →
  AllKeep keeps →
  Q —↠[ keeps ] W →
  Value W →
  Value L × No• L × B ≡ A`

to `proof.ReductionProperties`.

The direct `ν-step` case returns the value and `No•` evidence.  The only other
possible `bind` step from a top-level `ν` is `ξ-ν`; after that step the result
is still a top-level `ν`, so an all-`keep` tail cannot reach a value by
`allKeep-ν-no-value`.

This is not yet enough to replace the `catchup-⊒Λ-catchup` call.  The live
trace splitter exposes a generic

`P→Q : P —→[ bind Aχ ] Q`.

To use `ν-bind-step-value-tail-inv`, the replay proof still has to show that
the particular `P` obtained from the prefix reduction is a top-level `ν`.
That fact should come from combining the prefix trace with the `nu-base-empty`
history, not from raw reduction inversion alone.

## Attempt 36: expose no-bind and last-bind structure in `remainder-cast`

Succeeded as live scaffolding.  The `remainder-cast` branch of the actual
`catchup-lemma` `⊒Λ` fallback now splits on `storeChangesLastBind χs`.

In the `no-bind keeps` subcase, the branch calls

`pure-pred-↠-shifted-value keeps ⇑N↠W vW`

and therefore has the unshifted reduction half

`N↠predW : N —↠[ χs ] renameᵗᵐ predᵗ W`

available before exposing the cast base (`cast-base-empty+` or
`cast-base-empty-`).  This still does not rebuild the relation half for
`⊒Λ`; Attempt 32 explains why a generic relation transport would be too broad.

In the `last-bind` subcase, the branch now mirrors the `remainder-nu` setup:
it obtains

`Aχ≡★ : Aχ ≡ ★`

from `last-bind-empty-target-star`, and then splits the trace with
`↠-split-last-bind`, exposing

`⇑N↠P : ⇑ᵗᵐ N —↠[ χs₀ ] P`,
`P→Q : P —→[ bind Aχ ] Q`, and
`Q↠W : Q —↠[ keeps ] W`.

Both subcases still delegate to `catchup-⊒Λ-catchup`, so this is not a proof
of the cast branch.  It does make the live proof state match the two remaining
proof obligations: all-`keep` relation replay for casts, and final star-bind
replay for casts.

## Attempt 37: collapse all-`keep` empty store narrowing to `[]`

Succeeded as checked bookkeeping.  I added

`⊒ˢ-empty-empty-nil :
  Δ ⊢ π ꞉ [] ⊒ˢ [] →
  π ≡ []`

and the all-`keep` specialization

`allKeep-empty-target-nil :
  AllKeep χs →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ ⊢ π ꞉ Π ⊒ˢ Π′ →
  π ≡ []`.

The live `remainder-cast` / `no-bind` branches now carry

`π≡[] : π ≡ []`.

This removes one false degree of freedom: with only `keep` changes and empty
target store, the emitted store-narrowing proof cannot hide a source prefix.
It still does not rebuild the final `⊒Λ` relation.  The remaining obstruction
is the one from Attempt 32: the recursive result gives an inner relation for
`W`, while the unshifted reduction endpoint is `renameᵗᵐ predᵗ W`, and `W`
need not be definitionally equal to `⇑ᵗᵐ (renameᵗᵐ predᵗ W)`.

## Attempt 38: factor the all-`keep` no-bind `⊒Λ` bookkeeping

Succeeded as a checked reduction of the no-bind administrative burden.  I added
all-`keep` identities for the under-binder actions:

`allKeep-applyTermsUnderTyBinders-id :
  AllKeep χs →
  applyTermsUnderTyBinders χs M ≡ M`

and

`allKeep-applyCoercionUnderTyBinders-id :
  AllKeep χs →
  applyCoercionUnderTyBinders χs p ≡ p`.

The live `remainder-cast` / `no-bind` branches now also expose

`targetUnder≡ : applyTermsUnderTyBinders χs V′ ≡ V′`

and

`coercionUnder≡ : applyCoercionUnderTyBinders χs p ≡ p`,

with the hidden target body inferred from `vV′` and the hidden inner coercion
inferred from the typed `gen A p` premise.

I also added a checked finisher:

`catchup-⊒Λ-no-bind-finish`.

It proves the entire no-bind `⊒Λ` conclusion from:

- `AllKeep χs`;
- a value endpoint `W′`;
- a reduction `N —↠[ χs ] W′`;
- the original `gen A p` typing premise; and
- the single missing body relation
  `suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ []
     ⊢ ⇑ᵗᵐ W′ ⊒ V′ ∶ p`.

Thus the no-bind cast path is now isolated to one real mathematical gap.  For
the live branch, `W′` would be `renameᵗᵐ predᵗ W`, and the missing premise is
exactly the premise-aware source bridge from Attempt 32.  The new finisher
shows that no store, target, or coercion bookkeeping remains hidden in that
subcase.

## Attempt 39: reduce no-bind replay to a shifted-image equality

Succeeded as another checked factoring step.  I added

`catchup-⊒Λ-no-bind-shift-image`.

This helper consumes the actual recursive catchup relation

`Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
  ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p`

and produces the full outer no-bind `⊒Λ` catchup conclusion, assuming:

- `AllKeep χs`;
- the unshifted reduction endpoint `W′`;
- `N —↠[ χs ] W′`;
- the context equality `Δ′ ≡ applyTyCtxs χs (suc Δ)`;
- `π ≡ []`; and
- the shifted-image equality `W ≡ ⇑ᵗᵐ W′`.

The proof transports the recursive relation through:

- `allKeep-applyTyCtxs-id`;
- `combineStoreNrw [] σ ≡ σ`;
- `allKeep-applyTerms-id`;
- `allKeep-applyCoercions-id`; and
- the source equality `W ≡ ⇑ᵗᵐ W′`,

then calls `catchup-⊒Λ-no-bind-finish`.

For the live no-bind cast branch, `W′` is already available as
`renameᵗᵐ predᵗ W` via `pure-pred-↠-shifted-value`, so the branch is now
isolated to proving

`W ≡ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)`.

That equality is false in general, as the `proof.TraceProbe` counterexample to
the standalone inversion shows.  A valid proof must derive it from the actual
`⊒Λ` premise and cast-source history, or avoid it by producing the body relation
directly.  Do not try to use this helper with a generic shifted-trace equality.

## Attempt 40: derive a no-active-type-application source invariant

Succeeded as a checked premise invariant.  I added a new predicate

`NoActiveTypeApp M`

in `proof.TermNarrowingProperties`.  It rules out runtime type applications in
reducible positions, but deliberately permits bullets under lambda and type
lambda values, since reduction does not inspect those bodies.

The main checked lemma is

`value-target-source-no-active :
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  NoActiveTypeApp M`.

The proof follows the term-narrowing derivation:

- value constructors such as `ƛ⊒ƛ`, `Λ⊒Λ`, and `κ⊒κ` close directly;
- `⊒Λ`, `⊒⟨ν⟩`, and `ν⊒` recurse through their shifted premises;
- source and target cast wrappers recurse to their bodies;
- `extend` and `split` preserve the invariant through type-variable opening;
- non-value target constructors are impossible by the supplied `Value` proof.

The live `remainder-cast` / `no-bind` branches now expose

`noActive⇑N : NoActiveTypeApp (⇑ᵗᵐ N)`.

This is the first checked fact that distinguishes the real `⊒Λ` premise from
the `proof.TraceProbe` counterexample: the counterexample's shifted source is
a runtime type application, while the actual branch now carries evidence that
the shifted source has no active runtime type application.  The next reduction
lemma should use `NoActiveTypeApp (⇑ᵗᵐ N)`, `AllKeep χs`, and
`⇑ᵗᵐ N —↠[ χs ] W` to prove that the value endpoint is still in the image of
`⇑ᵗᵐ`, or produce the needed body relation directly.

## Attempt 41: recurse on the extracted cast-base premise

Failed by Agda termination checking.  I temporarily added

`with catchup-lemma vBase bodyBase`

to the `remainder-cast` / `no-bind` / `cast-base-empty+` branch, while still
returning the old postulate-backed RHS.  Agda rejected `catchup-lemma` because
the call

`catchup-lemma vBase bodyBase`

is not structurally visible as a subcall of the original

`catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)`.

This confirms an earlier suspicion: although the history inversion exposes a
logically smaller value-target premise, that premise is obtained through a
classifier after the recursive call on `N⊒V′`, so Agda cannot use it directly
for structural recursion.  Reusing the ordinary cast catchup proof shape inside
this branch would require a larger refactor to an explicit measure or a
separate non-recursive lemma; it is not available as a local direct recursive
call.

## Attempt 42: factor a catchup-safe reducible-spine invariant

Partly succeeded.  I added the checked syntactic predicate

`CatchupSafe M`

in `proof.ReductionProperties`.  It describes sources whose reducible spine can
catch up to a value: values are leaves, and the only non-value spine forms are
`ν A L c` and `M ⟨ c ⟩`.

I then proved in `proof.TermNarrowingProperties`:

`value-target-source-safe :
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  CatchupSafe M`.

The proof mirrors `value-target-source-no-active`: value constructors close
with `safe-value`, source `ν` and source cast constructors recurse under
`safe-ν`/`safe-cast`, and the `⊒Λ`/`⊒⟨ν⟩` cases reflect the invariant through
the shifted premise.  The live `remainder-cast` / `no-bind` branch now exposes

`safe⇑N : CatchupSafe (⇑ᵗᵐ N)`.

The next intended step was a reduction lemma saying that an all-keep reduction
from a shifted `CatchupSafe` source to a value either remains in the image of
`⇑ᵗᵐ` or reaches a doomed term.  That proof ran into the repo's
"constructor form indices" pitfall.  In the `tag-untag-ok` and `seal-unseal`
cases, Agda must match redexes such as

`renameᵗᵐ suc M ⟨ renameᵗ suc H ？ ⟩`

against constructors whose indices require the same tag on both casts.  The
needed equality follows from injectivity of `renameᵗ suc`, but Agda's unifier
does not use that injectivity when deciding whether the reduction constructor
case is possible.  Splitting on the outer coercion, splitting on the inner
preterm, and adding cast-constructor injectivity helpers still left Agda stuck
on matching `tag-untag-ok`.

So `CatchupSafe` is useful checked evidence, but the attempted shifted-image
reduction proof should not be repeated in this direct pattern-matching form.
Any future version needs a reduction view whose indices avoid defined
functions, or a separate normalized redex view that carries the tag equality as
an explicit proof rather than asking Agda's unifier to infer it.

## Attempt 43: prove the no-bind shifted-image equality from `CatchupSafe`

Succeeded for the live no-bind cast branches.  I avoided the failed direct
pattern match on shifted reduction indices by carrying explicit image evidence:

`TermShiftImage M = ∃[ N ] (M ≡ ⇑ᵗᵐ N)`.

The checked helper decomposes shifted images of casts, `ν`, sequences, and
instantiations by first inspecting the preimage syntax and then using ordinary
constructor injectivity.  On top of that, `proof.ReductionProperties` now has:

`safe-allKeep-value-image :
  CatchupSafe M →
  TermShiftImage M →
  AllKeep χs →
  M —↠[ χs ] W →
  Value W →
  W ≡ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)`.

The one-step view says a keep step from a shifted `CatchupSafe` source either
remains safe and shifted or reaches a `NoValueReachable` term.  The bad tag
case goes to the doomed branch; the final `Value W` eliminates it.

The two live `remainder-cast` / `no-bind` branches now call
`catchup-⊒Λ-no-bind-shift-image` with this checked equality instead of
delegating to `catchup-⊒Λ-catchup`.  This does not solve the last-bind
branches: there the final star bind still has to be replayed or erased, and
the all-keep shifted-image invariant applies only after the last bind.

## Attempt 44: expose the store-tail shape of the final star bind

Succeeded as checked last-bind scaffolding.  I added:

`last-bind-empty-target-left-tail :
  AllKeep keeps →
  Π ≡ applyStores (χs ++ bind A ∷ keeps) [] →
  Δ ⊢ π ꞉ Π ⊒ˢ [] →
  ∃[ X ] ∃[ π₀ ] (π ≡ (⊒ X ꞉=☆) ∷ π₀) ×
    (X ≡ zero) ×
    Δ ⊢ π₀ ꞉ ⟰ᵗ (applyStores χs []) ⊒ˢ []`.

This strengthens the earlier `last-bind-empty-target-star` fact.  The final
emitted bind does not merely have type `★`; the empty-target store narrowing
proof must begin with a source-only star at de Bruijn zero, and its tail is a
proof for the shifted prefix source store.

I also added the small context-index lemma

`applyTyCtxs-last-bind-suc :
  applyTyCtxs (χs ++ bind A ∷ keeps) (suc Δ) ≡
    suc (suc (applyTyCtxs χs Δ))`.

These facts are the store and context bookkeeping needed by the remaining
binder-exchange replay: move the source-only star produced by the final bind
under the fresh target-only `⊒Λ` binder while lowering the shifted prefix tail.
They do not yet identify the pre-bind term `P` or transport the term relation,
so the three live last-bind branches still delegate to `catchup-⊒Λ-catchup`.

## Attempt 45: reuse `ExtendReplaceRel` for the final binder exchange

Rejected after inspecting the checked replacement machinery.  `ExtendReplaceRel`
is the right abstraction for the `extend` case: it changes one target-only
entry

`(α ꞉= A ⊒) ∷ σ`

into a both-side coercion entry

`(α ꞉ q) ∷ σ`

and then recurses structurally under right, left, or both entries.  Its
source-store inclusion goes in the corresponding weakening direction.

The last-bind `⊒Λ` replay needs a different operation.  After Attempt 44, the
store has the shape

`(⊒ zero ꞉=☆) ∷ π₀`

in front of the shifted fresh target-only binder.  The desired body store has
the fresh target-only binder first, with the emitted source-only star moved
under it and the prefix tail lowered.  That is an exchange/drop operation, not
an endpoint replacement.  Forcing it through `ExtendReplaceRel` would lose the
needed reindexing of terms/coercions under the binder and repeat the broad
transport failures from Attempts 7 and 8.

Next useful target: define a narrow exchange relation for this exact pair of
store shapes, then prove only the term-imprecision clauses reachable from the
last-bind replay instead of a generic source-transport theorem.

## Attempt 46: lower the shifted prefix tail after the final star bind

Succeeded as checked store algebra.  The earlier last-bind fact exposed

`π = (⊒ zero ꞉=☆) ∷ πtail`

with

`πtail : ⟰ᵗ (applyStores χs []) ⊒ˢ []`.

I added a small inversion for empty-target shifted stores:

`⊒ˢ-empty-shift-inv :
  Δ ⊢ π ꞉ ⟰ᵗ Σ ⊒ˢ [] →
  ∃[ π′ ] (π ≡ ⇑ˢ π′) × Δ ⊢ π′ ꞉ Σ ⊒ˢ []`.

Combining it with Attempt 44 gives the sharper checked form

`last-bind-empty-target-lowered-tail :
  ∃[ π₀ ] (π ≡ (⊒ zero ꞉=☆) ∷ ⇑ˢ π₀) ×
    Δ ⊢ π₀ ꞉ applyStores χs [] ⊒ˢ []`.

I also added the corresponding append algebra:

`combineStoreNrw-source-star-shifted-tail :
  combineStoreNrw ((⊒ zero ꞉=☆) ∷ ⇑ˢ π) σ ≡
    (⊒ zero ꞉=☆) ∷ ⇑ˢ (combineStoreNrw π σ)`.

This is useful but not sufficient.  After substituting this shape, the live
last-bind relation is under the store

`(⊒ zero ꞉=☆) ∷ ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`.

The body required to rebuild `⊒Λ` wants the adjacent binders in the opposite
order:

`(zero ꞉= ★ ⊒) ∷ ⇑ˢ ((⊒ zero ꞉=☆) ∷ combineStoreNrw π₀ σ)`.

So the remaining issue is not more tail inversion; it is an adjacent
source-only/target-only binder exchange with the corresponding de Bruijn
renaming of the term, target, and coercion indices.

## Attempt 47: use a `CatchupSafe` bind-step view instead of exchange

Rejected as a way around exchange.  The no-bind proof succeeded because an
all-keep trace from a shifted `CatchupSafe` source to a value stays in the
image of `⇑ᵗᵐ`.  I considered extending that view to classify one final
`bind` step:

`⇑ᵗᵐ N —↠[ χs ++ bind ★ ∷ keeps ] W`.

The root `ν-step` case is easy to identify locally, and contextual bind steps
through casts/`ν` could be described recursively.  However, even a perfect
bind-step view only explains the source reduction.  It still leaves the final
term relation under the source-first store

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ...`

while rebuilding `⊒Λ` needs the body under the target-first store

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ...`.

This is not just an equality of store append expressions: the source term that
mentions the emitted source seal must be renamed from variable `zero` to
`suc zero`, while the target-side binder moves to `zero`.  Thus a bind-step
view would still have to call the same adjacent source-only/target-only binder
exchange theorem.  It is not a separate escape hatch.

The useful next theorem should therefore be the exchange itself, probably
specialized to empty target store prefixes and to the stores generated by
`combineStoreNrw`, rather than a generic store permutation theorem.

## Attempt 48: replay the branch-specific `ν⊒` base instead of exchanging

Rejected.  I temporarily replaced the remaining `remainder-nu` last-bind call
to `catchup-⊒Λ-catchup` with a hole and then with `bodyBase` /
`ν⊒ pBaseᶜ bodyBase` to inspect the branch-specific evidence.

The `nu-source-value-target-base-empty` witness really is the base premise of
the original `ν⊒` derivation:

`suc Δ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ ∣ []
  ⊢ N ⊒ ⇑ᵗᵐ N′ ∶ ⇑ᶜ p`.

Using `ν⊒ pBaseᶜ bodyBase` only reconstructs a term-imprecision judgment of
shape

`Δ ∣ σ ∣ [] ⊢ ν ★ N (⇑ᶜ p) ⊒ N′ ∶ p`.

That is the pre-catchup source relation, not the Σ-shaped catchup conclusion
needed by the branch.  It also does not mention the emitted prefix, the final
value `W`, or the keep-tail reductions after the final `bind`.  So the base
witness is useful evidence about the derivation history, but it cannot replace
the false shifted-source inversion by itself.

## Attempt 49: use the examples' `split` shape directly

Rejected as a direct transport, but it clarifies the next real theorem.  The
post-reduction examples (`ex1-split`, `ex4-split`) confirm that the intended
local move is:

1. build a relation under a both-side store such as `(zero ꞉ id ★) ∷ σ`;
2. apply `split` to obtain the target-first/source-only store
   `(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ σ`;
3. rebuild the outer `⊒Λ`.

The recursive catchup result in the live branch has already performed the
source reduction and keep-tail catchup under the source-first store

`(⊒ zero ꞉=☆) ∷ ⇑ˢ (combineStoreNrw π₀
  ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`.

That is not a `split` premise, and the `NuSourceValueTarget` /
`CastSourceValueTarget` base witness alone does not reconstruct the caught-up
post-tail term under the both-side store.  A direct call to `split` would need
either:

- a history-preserving catchup theorem that replays the source-shape history
  through the final `bind` and the keep tail, producing the both-side premise
  before applying `split`; or
- a genuine binder-exchange theorem transporting the already caught-up
  relation from source-first order to target-first order, with the corresponding
  de Bruijn renaming of the source term, target term, and coercion.

The existing insertion/gap lemmas in `proof.NarrowWidenProperties` are aimed at
coercion overlap/determinacy, not whole `TermNarrowing` transport, so they do
not provide this exchange directly.

## Attempt 50: lift the `TraceProbe` counterexample through the real `gen` premise

Rejected as a counterexample to `catchup-⊒Λ-catchup`, but now checked as a
diagnostic boundary.  I tried to reuse the standalone
`shifted-source-catchup-Λ-inversion` counterexample to refute the helper that
the `⊒Λ` branches currently call.

The first observation is useful: after the shifted beta step, the proposed
outer conclusion is also impossible if the helper ignored its `gen` premise:

`no-probe-outer-conclusion :
  0 ∣ [] ∣ []
    ⊢ probe-W ⊒ Λ probe-V′ ∶ gen (★ ⇒ ★) probe-c →
  ⊥`.

However, the actual helper has the premise

`Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B`.

The old probe uses `probe-c = id (＇ 0) ↦ id (＇ 0)`, and this cannot be the
body of such an empty-context `gen` coercion.  I added the checked lemma

`no-probe-gen-premise :
  0 ∣ [] ⊢ gen A probe-c ∶ᶜ A ⊒ `∀ B →
  ⊥`.

Mechanically, the body of a `gen` coercion is typed with source endpoint
`⇑ᵗ A`, but `probe-c` has source endpoint headed by `＇ 0`; no shifted type can
have `＇ 0` at the head.  This explains the earlier failed attempt to pass
`poly-fun-cast`: that theorem types `gen (★ ⇒ ★) var0-fun`, not
`gen (★ ⇒ ★) probe-c`.

Conclusion: this does not refute `catchup-⊒Λ-catchup` or the main
`catchup-lemma`.  The extra `gen` premise is doing real work, and any
counterexample must use a legal `gen` body such as `var0-fun`.  With legal
example bodies, the desired post-bind shape is exactly the `split` shape already
visible in `NarrowingExamples`, so the remaining proof path is still either a
history-preserving replay through the final `bind` or a structural adjacent
source-only/target-only binder exchange theorem.

## Attempt 51: normalize the last-bind body into source-first form

Partial progress.  I added the checked transport lemma

`last-bind-source-first-body :
  AllKeep keeps →
  π ≡ (⊒ zero ꞉=☆) ∷ ⇑ˢ π₀ →
  Δ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms (χs ++ bind A ∷ keeps) V
      ∶ applyCoercions (χs ++ bind A ∷ keeps) p →
  Δ ∣ (⊒ zero ꞉=☆) ∷
      ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)) ∣ []
    ⊢ W ⊒ ⇑ᵗᵐ (applyTerms χs V) ∶ ⇑ᶜ (applyCoercions χs p)`.

This combines the lowered-tail store inversion from Attempt 46 with
`applyTerms-last-bind` and `applyCoercions-last-bind`.  It removes some
transport noise from the live last-bind branches: after the final `bind`, the
caught-up body is explicitly under the source-first store

`(⊒ zero ꞉=☆) ∷
  ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`

and its target/coercion are explicitly shifted.

This still does not rebuild `⊒Λ`.  The desired `⊒Λ` premise would need the
target-first/source-only order

`(zero ꞉= ★ ⊒) ∷
  ⇑ˢ ((⊒ zero ꞉=☆) ∷ combineStoreNrw π₀ σ)`.

So the remaining missing theorem is now isolated more cleanly: either transport
this normalized source-first body across the adjacent binder exchange, or replay
the source history up to a both-side premise and then use `split`.

## Attempt 52: invert one shifted `bind` step with `predᵗ`

Partial progress.  I added checked structural reflection lemmas:

- `renameᶜ-reflects-Inert` in `proof.CoercionProperties`;
- `renameᵗᵐ-reflects-Value` and `renameᵗᵐ-reflects-No•` in
  `proof.NuTermProperties`.

Then I proved the local reduction inverse:

`type-rename-bind-step-pred :
  ⇑ᵗᵐ M —→[ bind A ] N →
  M —→[ bind (renameᵗ predᵗ A) ] renameᵗᵐ predᵗ N`.

The proof needed explicit transports for the root `ν-step`, contextual `ν`,
cast, application, and primitive-op contexts.  In particular, the root step
normalizes

`pred ((⇑ (⇑ L)) • ⟨ renameᶜ (extᵗ suc) c ⟩)`

to

`(⇑ L) • ⟨ c ⟩`,

and the contextual `ν` case needs the under-binder cancellation

`renameᶜ (extᵗ predᵗ) (renameᶜ (extᵗ suc) c) ≡ c`.

This is a real replacement ingredient for replaying shifted reductions, but it
does not by itself prove the last-bind `⊒Λ` branch.  The lemma applies only
when the source of the `bind` step is visibly `⇑ᵗᵐ M`.  In the live last-bind
branches, the prefix before the final `bind` can contain earlier nested binds
inside the top-level `ν` or cast source, so the intermediate term before the
final bind need not be a global type-shift image.  This confirms that the
remaining proof still needs either a recursive replay theorem that performs the
same binder exchange at each nested bind, or the adjacent source-only/target-only
exchange theorem isolated in Attempts 47, 49, and 51.

## Attempt 53: build the split coercion premises from the `gen` premise

Partial progress.  The examples suggest that the post-bind `⊒Λ` body should
eventually be rebuilt by a `split`: the target-only binder sits at `zero`, and
the emitted source-only star sits at `suc zero`.  I therefore isolated the
coercion premises needed by that future `split`.

I added the checked helpers:

`id★-coercionᶜ :
  Δ ∣ Σ ⊢ id ★ ∶ᶜ ★ ⊒ ★`

and

`gen-body-open-split-coercion :
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc Δ ∣
    srcStoreⁿ ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ)
    ⊢ (⇑ᶜ p) [ zero ]ᶜ ∶ᶜ ⇑ᵗ A ⊒ B`.

The second helper inverts the `cast-gen` premise, relaxes the body mode from
`genᵈ tag-or-idᵈ` back to `tag-or-idᵈ`, weakens the source store by the emitted
star, and rewrites `(⇑ᶜ p) [ zero ]ᶜ` back to `p`.

I also lifted it through emitted catchup prefixes:

`catchup-gen-body-open-split-coercion :
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  suc Δ′ ∣
    srcStoreⁿ
      ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷
        ⇑ˢ (combineStoreNrw π σ))
    ⊢ (⇑ᶜ (applyCoercionUnderTyBinders χs p)) [ zero ]ᶜ
      ∶ᶜ ⇑ᵗ (applyTys χs A) ⊒ applyTysUnderTyBinders χs B`.

This removes one uncertainty from the split-rebuild path: the required
coercion premises can be derived from the real `gen` premise even after an
emitted prefix.  It still does not move the caught-up term relation from the
source-first store to the target-first/source-only store, so the remaining
obligation is still the term-level exchange/replay theorem.

## Attempt 54: normalize under-binder targets at the last bind

Partial progress.  While inspecting the last-bind exchange shape, I noticed
that the target-first result should be stated with the under-binder actions
rather than ordinary `applyTerms`/`applyCoercions`.  I added two checked
normal forms:

`applyTermsUnderTyBinders-last-bind :
  AllKeep keeps →
  applyTermsUnderTyBinders (χs ++ bind A ∷ keeps) M ≡
    renameᵗᵐ (extᵗ suc) (applyTermsUnderTyBinders χs M)`

and

`applyCoercionUnderTyBinders-last-bind :
  AllKeep keeps →
  applyCoercionUnderTyBinders (χs ++ bind A ∷ keeps) p ≡
    renameᶜ (extᵗ suc) (applyCoercionUnderTyBinders χs p)`.

Both are immediate consequences of the existing append lemmas plus the
all-keep identity lemmas for the tail after the last bind.  They are useful
because the future exchange/replay theorem can now target the exact
under-binder syntax expected by `applyTerms-Λ` and `applyCoercions-gen`.

This does not solve the branch.  The recursive catchup body normalized in
Attempt 51 is still phrased with ordinary shifted target/coercion syntax under
the source-first store.  Attempt 54 only identifies the target-first side; a
term-level exchange/replay theorem must still move the derivation itself and
account for the ordinary-vs-under-binder index change.

## Attempt 55: isolate the source-side `raise0ᵗ` algebra

Partial progress.  I added the checked renaming

`raise0ᵗ : Renameᵗ`

with

`raise0ᵗ X = suc (predᵗ X)`.

This renaming maps the emitted source-only star at type variable `zero` to
`suc zero`, while leaving positive variables fixed: `0 ↦ 1`, `1 ↦ 1`,
`2 ↦ 2`, and so on.  I also added checked syntax equalities for types,
coercions, and terms:

`renameᵗ raise0ᵗ A ≡ ⇑ᵗ (renameᵗ predᵗ A)`,

`renameᶜ raise0ᵗ c ≡ ⇑ᶜ (renameᶜ predᵗ c)`,

and

`renameᵗᵐ raise0ᵗ M ≡ ⇑ᵗᵐ (renameᵗᵐ predᵗ M)`.

This packages one syntactic component of the source-first/target-first
exchange.  Source-first catchup evidence talks about the final emitted
source-only star at `zero`, but the target-first `⊒Λ` body needs the final
source term under `⇑ᵗᵐ`, so that star must appear at `suc zero`.

This is not enough to prove the branch.  The renaming is not injective: it
merges `zero` and `suc zero`.  A direct structural transport of the term
narrowing relation would therefore need mode-renaming or typing side
conditions showing that the target-only variable being merged with the emitted
source star is not used in the wrong place.  The existing relation-preservation
lemmas such as `coercion-renameᵗᵐ` and `narrow-renameᵗ` require a
`ModeRename`, so this non-injective raw renaming cannot be threaded through
them directly.  The remaining theorem still needs a constrained exchange/replay
argument, not just syntax renaming.

## Attempt 56: make `raise0ᵗ` mode-valid in the two-binder context

Partial progress, and a correction to the pessimistic part of Attempt 55.
Although `raise0ᵗ` is non-injective, the public coercion premises used by
term narrowing are in `tag-or-idᵈ`, and `ModeRename` only asks for a
mode-inclusion into the renamed target environment.  For `tag-or-idᵈ`, the
merged variable is still accepted.

I added the checked facts:

`TyRenameWf-raise0 :
  TyRenameWf (suc (suc Δ)) (suc (suc Δ)) raise0ᵗ`

and

`modeRename-raise0-tag-or-id :
  ModeRename raise0ᵗ tag-or-idᵈ tag-or-idᵈ`.

So the raw renaming can be used with existing coercion-level lemmas such as
`narrow-renameᵗ`, at least for `∶ᶜ` coercions in the live two-binder context.
This is useful, but it still does not prove the branch.  Coercion renaming
acts on ordinary source stores via `renameStoreᵗ`; the missing theorem is a
whole `TermNarrowing` transport across the adjacent source-only/target-only
store exchange.  Such a transport would need to rename source terms, target
terms, coercion indices, `CtxNrw`, and the `StoreNrw` structure itself, with
special handling for constructors such as `extend`, `split`, `⊒Λ`, `⊒⟨ν⟩`,
`ν⊒ν`, `⊒ν`, and `ν⊒`.

The next non-redundant proof target is therefore either a structural
term-narrowing renaming/exchange lemma specialized to this two-binder
`tag-or-idᵈ` situation, or a replay theorem that rebuilds the post-bind
`split` premise before the final exchange is needed.

## Attempt 57: extend the `raise0ᵗ` algebra to `StoreNrw` and `CtxNrw`

Partial progress.  I started the structural exchange route by adding the
syntax/index operations that a term-narrowing transport would need:

`renameStNrw : Renameᵗ → StNrw → StNrw`,

`renameStoreNrw : Renameᵗ → StoreNrw → StoreNrw`,

and

`renameCtxNrw : Renameᵗ → CtxNrw → CtxNrw`.

The checked source-store commutation lemma is:

`srcStoreⁿ-renameStoreNrw :
  srcStoreⁿ (renameStoreNrw ρ σ) ≡ renameStoreᵗ ρ (srcStoreⁿ σ)`.

I also added the checked shift commutation lemmas:

`renameStoreNrw-⇑ˢ :
  renameStoreNrw (extᵗ ρ) (⇑ˢ σ) ≡ ⇑ˢ (renameStoreNrw ρ σ)`

and

`renameCtxNrw-⇑ᵍ :
  renameCtxNrw (extᵗ ρ) (⇑ᵍ γ) ≡ ⇑ᵍ (renameCtxNrw ρ γ)`.

Finally, I lifted the `raise0ᵗ = suc ∘ predᵗ` syntax equations to stores and
contexts:

`renameStoreNrw-raise0-pred :
  renameStoreNrw raise0ᵗ σ ≡ ⇑ˢ (renameStoreNrw predᵗ σ)`

and

`renameCtxNrw-raise0-pred :
  renameCtxNrw raise0ᵗ γ ≡ ⇑ᵍ (renameCtxNrw predᵗ γ)`.

These are the right index-level ingredients for a future structural
`TermNarrowing` renaming/exchange theorem: they show how the source term,
coercion index, store-narrowing context, and variable context should all move
together under `raise0ᵗ`.

This still does not close the `⊒Λ` branch.  Inspecting
`NarrowWidenComposition` showed that the cast endpoint constructors in
`TermNarrowing` depend on side conditions

`Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B`

and

`Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B`.

There is no existing type-renaming theorem for these composition relations.
A full structural term-renaming theorem would need that layer too, including
transport through `EndpointWf`, `StoreDetWf`, and the endpoint equality
proofs.  So the next useful proof target is either composition-side-condition
renaming, or a narrower exchange theorem that avoids the cast endpoint
constructors by using the `NuSourceValueTarget`/`CastSourceValueTarget`
history more directly.

## Attempt 58: inspect main's substitution-narrowing proof and isolate the
`gen` body invariant

Main added `proof.TermSubstitutionNarrowing`, which is useful as a structural
recursion template over `TermNarrowing`: it shows how to recurse through every
term-narrowing constructor while threading a framed environment through
binders.  It does not directly solve the `⊒Λ` obstruction, because the theorem
keeps the `StoreNrw` fixed.  The stuck branch needs to change the store shape
from source-first

`(⊒ zero ꞉=☆) ∷ ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`

to the target-first/source-only shape needed by the final `⊒Λ` body.  So the
new substitution theorem cannot be applied as a black box.

I also checked whether Attempt 57's "composition-side-condition renaming"
could be proved generically.  For injective renamings this looks plausible,
but the intended `raise0ᵗ` map is non-injective: it merges `zero` and
`suc zero`.  A generic composition-renaming theorem would have to rename the
`StoreDetWf` witness in `compose-leftⁿ`/`compose-rightⁿ`, and `StoreDetWf` is
not preserved by arbitrary non-injective renaming.  This explains why the
plain `raise0ᵗ` structural-renaming route keeps getting stuck.

The useful checked progress from this attempt is the small invariant that the
TraceProbe counterexample lacks:

`gen-body-coercionᶜ :
  Δ ∣ Σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  genᵈ tag-or-idᵈ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ p ∶ ⇑ᵗ A ⊒ B`

and its catchup-transported form

`catchup-gen-body-coercionᶜ :
  genᵈ tag-or-idᵈ ∣ suc Δ′ ∣
    ⟰ᵗ (srcStoreⁿ (combineStoreNrw π σ))
    ⊢ applyCoercionUnderTyBinders χs p
      ∶ ⇑ᵗ (applyTys χs A) ⊒ applyTysUnderTyBinders χs B`.

This pins down the sound side condition that distinguishes the real `⊒Λ`
branch from the false standalone inversion: the body coercion of a valid
`gen` has a shifted source endpoint.  The next non-redundant route is therefore
not bare store renaming; it is a history-preserving replay or exchange theorem
that uses this shifted-source endpoint invariant to move the source-only star
under the target-only binder.

## Attempt 59: reuse split catchup or a post-bind image view as a shortcut

Rejected as a shortcut, but it narrows the remaining shared obligation.

First, I rechecked whether the existing `catchup-split-catchup` postulate could
be instantiated to finish the `⊒Λ` last-bind branches.  The shapes are close:
the desired `⊒Λ` body needs the same target-first/source-only store order that
`split` concludes with,

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ ...`.

However, `catchup-split-catchup` transports an opening

`N [ α ]ᵀ —↠[ χs ] W`

to another opening

`N [ αᵢ ]ᵀ —↠[ χs′ ] W′`.

The live `⊒Λ` branch instead starts from a global shift:

`⇑ᵗᵐ N —↠[ χs ] W`

and must produce an unshifted run

`N —↠[ χs′ ] W′`.

Opening a uniformly shifted term cancels the shift for every choice of
variable, so there is no direct instantiation that makes one side `⇑ᵗᵐ N` and
the other side `N`.

Second, I revisited the all-keep shifted-image route.  It succeeds in the
no-bind branch because `safe-allKeep-value-image` only has to preserve a
`TermShiftImage` invariant through keep steps after the source is already known
to be in the image of `⇑ᵗᵐ`.  In a last-bind branch, splitting the reduction
gives

`⇑ᵗᵐ N —↠[ χs₀ ] P`, `P —→[ bind Aχ ] Q`, and
`Q —↠[ keeps ] W`.

Even if a local bind-step view proves that `Q` is safe and shifted-image, the
final term-imprecision evidence remains under the source-first store

`(⊒ zero ꞉=☆) ∷
  ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`.

Rebuilding `⊒Λ` still needs the target-first/source-only order

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷
  ⇑ˢ (combineStoreNrw π₀ σ)`.

So the image view cannot avoid the adjacent exchange.  The split case and the
`⊒Λ` last-bind case appear to need a common source-variable opening/exchange
transport: one version changes `N [ α ]ᵀ` to `N [ αᵢ ]ᵀ`, while the `⊒Λ`
version changes the source-first body to the target-first/source-only body and
uses the checked `gen` body invariant for the split coercion premise.

## Attempt 60: factor the injective variable swap inside the exchange

Checked progress.  Attempts 57 and 58 framed the exchange in terms of
`raise0ᵗ`, but `raise0ᵗ` is non-injective and therefore a poor fit for a
generic structural transport through coercion-composition side conditions.
The adjacent source-only/target-only exchange itself is better described in two
steps:

1. swap the two newest type variables with an injective renaming; then
2. reorder the two corresponding `StoreNrw` entries.

I added the checked renaming component:

`swap01ᵗ zero = suc zero`

`swap01ᵗ (suc zero) = zero`

`swap01ᵗ (suc (suc X)) = suc (suc X)`.

The following facts now type-check in `proof.Catchup`:

`TyRenameWf-swap01 :
  TyRenameWf (suc (suc Δ)) (suc (suc Δ)) swap01ᵗ`

`modeRename-swap01-tag-or-id :
  ModeRename swap01ᵗ tag-or-idᵈ tag-or-idᵈ`

`renameᵗ-swap01-⇑ :
  renameᵗ swap01ᵗ (⇑ᵗ A) ≡ renameᵗ (extᵗ suc) A`

`renameᶜ-swap01-⇑ :
  renameᶜ swap01ᵗ (⇑ᶜ c) ≡ renameᶜ (extᵗ suc) c`

`renameᵗᵐ-swap01-⇑ :
  renameᵗᵐ swap01ᵗ (⇑ᵗᵐ M) ≡ renameᵗᵐ (extᵗ suc) M`.

This does not finish the `⊒Λ` branch because renaming alone does not reorder
the `StoreNrw` list.  In particular, it changes the variables inside the
source-first store but leaves the source-only entry syntactically before the
target-only entry.  The remaining theorem is therefore not "rename by
`raise0ᵗ`"; it is a list-level adjacent exchange whose renaming component is
`swap01ᵗ`.  This looks more plausible than the earlier generic `raise0ᵗ`
renaming route because the syntax renaming is injective; the hard part is now
isolated to the `StoreNrw` permutation and the term-narrowing constructors
that expose store entries (`extend`, `split`, `⊒Λ`, `⊒ν`, `ν⊒`, and the cast
composition side conditions).

## Attempt 61: check `swap01ᵗ` injectivity and inspect the store-prefix
obstruction

Checked progress plus a sharper obstruction.  I added:

`swap01ᵗ-involutive :
  swap01ᵗ (swap01ᵗ X) ≡ X`

and

`swap01ᵗ-injective :
  RenameInjective swap01ᵗ`.

This confirms the variable-swap part of the future exchange can use
injective-renaming infrastructure; it should not have the `StoreDetWf`
preservation problem that blocked the generic `raise0ᵗ` route.

However, inspecting the store shapes shows that the remaining exchange is not
just "rename by `swap01ᵗ` and swap two list heads".  The source-first body from
Attempt 51 has the final source-only binder in front of

`⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`.

The emitted prefix `π₀` was produced while the original `⊒Λ` target binder was
already in scope.  After rebuilding the outer `⊒Λ`, the corresponding emitted
prefix must live under both the target binder and the final source-only binder.
So the exchange theorem must also transport/lower the prefix itself; it cannot
be stated as a bare adjacent permutation of two fixed store entries.

This makes the likely next theorem a prefix-aware exchange/replay:

if the recursive body is under

`(⊒ zero ꞉=☆) ∷
  ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`,

then construct an emitted prefix for the unshifted source run and transport the
body to the `⊒Λ` premise store

`(zero ꞉= ★ ⊒) ∷ ⇑ˢ (combineStoreNrw π′ σ)`.

The checked `swap01ᵗ` facts should handle the target/coercion syntax during
this transport, but the theorem still has to describe how `π₀`, reductions,
and the term-narrowing derivation move together.

## Attempt 62: revisit composition-side-condition renaming with an injective
renaming

Rejected as a small next step.  With `swap01ᵗ-injective` available, I checked
whether the composition side conditions could now be renamed directly.  The
first tempting target is a lemma of the form:

`Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
 Δ′ ∣ renameStoreNrw ρ σ
   ⊢ renameᶜ ρ q ⨾ⁿ renameᶜ ρ s ≈ renameᶜ ρ r
     ∶ renameᵗ ρ A ⊒ renameᵗ ρ B`.

The existing infrastructure already gives most of the constructor payload:
`narrow-renameᵗ` renames the two coercion premises, and `WfTyˢ-rename`
renames endpoint well-formedness.  The remaining problem is the recursive
composition result itself.  A `compose-leftⁿ` side condition does not relate
`q` and `s` to `r` directly; it relates

`proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒)`

to `r`.

After renaming the premises, the new constructor wants a side condition about

`proj₁ (_⨟ⁿ_ {wfΣ = wfΣ′} (rename q⊒) (rename s⊒))`.

So the renaming lemma for side conditions also needs a mutual theorem saying
that the narrowing and widening composition functions commute with the same
renaming, including their `StoreDetWf` arguments and all recursive gen/inst
cases.  That is a legitimate theorem, and `swap01ᵗ-injective` avoids the
non-injective `StoreDetWf` problem noted in Attempt 58, but it is not a small
local proof.

Conclusion: composition-side-condition renaming remains a possible component
of a full structural exchange theorem, but the next proof should either state
the whole exchange/replay theorem directly or first prove a dedicated
composition-commutes-with-`swap01ᵗ` theorem, not just a shallow renaming lemma
for `compose-leftⁿ`/`compose-rightⁿ`.

## Attempt 63: extend the checked `swap01ᵗ` algebra to stores and contexts

Partially accepted.  The term/type/coercion facts from Attempt 60 were not
enough for a future exchange proof, because the body precision judgment also
carries a `StoreNrw` and `CtxNrw`.  I added and checked:

`renameStoreNrw-swap01-⇑ˢ :
 renameStoreNrw swap01ᵗ (⇑ˢ σ) ≡ renameStoreNrw (extᵗ suc) σ`

and

`renameCtxNrw-swap01-⇑ᵍ :
 renameCtxNrw swap01ᵗ (⇑ᵍ γ) ≡ renameCtxNrw (extᵗ suc) γ`.

This closes the purely syntactic part of moving a shifted object under the
adjacent swap.  It still does not solve the `⊒Λ` branch: after the last emitted
`bind`, the proof needs to exchange/replay the emitted prefix so that the
source-only star generated by the reduction moves behind the target-only star
required by the `⊒Λ` body.  That movement is not a pointwise rename of
`StoreNrw`; it changes the list structure and the way the earlier prefix is
threaded through `combineStoreNrw`.

I also revisited the existing split at the last bind.  The helper
`type-rename-bind-step-pred` can lower a single `bind` step whose source is a
plain `⇑ᵗᵐ` image, and the `keeps` tail can then be lowered by
`pure-pred-↠-shifted-value`.  However, the prefix before the last bind may
itself contain earlier `bind`s, so the intermediate term before the final bind
is not guaranteed to be a plain `⇑ᵗᵐ` image.  It may be an under-binder image
created by prior `ν`/cast reductions.  Thus the last-bind split is useful
evidence for a prefix-aware exchange/replay theorem, but it is not by itself a
local proof of `catchup-⊒Λ-catchup`.

## Attempt 64: transport non-mode endpoints across `swap01ᵗ`

Partially accepted.  I extended the checked swap algebra from syntax to the
existential, non-mode endpoint relation:

`⊒ˢ-rename-swap01ᵗ :
 suc (suc Δ) ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
 suc (suc Δ) ⊢ renameStoreNrw swap01ᵗ σ ꞉
   renameStoreᵗ swap01ᵗ Σ ⊒ˢ renameStoreᵗ swap01ᵗ Σ′`

and

`≈ⁿ-rename-swap01ᵗ :
 suc (suc Δ) ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
 suc (suc Δ) ∣ renameStoreNrw swap01ᵗ σ
   ⊢ renameᶜ swap01ᵗ s ≈ renameᶜ swap01ᵗ t
     ∶ renameᵗ swap01ᵗ A ⊒ renameᵗ swap01ᵗ B`.

The only non-obvious part was the mode environment inside the existential
narrowing witnesses.  Defining `swap01ᵗMode μ X = μ (swap01ᵗ X)` and using
`swap01ᵗ-involutive` gives a small checked `ModeRename` witness, so this route
does not need a global mode convention.

I then tested the more ambitious next shortcut: use narrowing determinacy to
show that `_⨟ⁿ_` commutes with `swap01ᵗ`, avoiding a full structural replay of
composition.  That needs a `StoreDetWf` witness for the swapped store.  The
generic lemma

`StoreDetWf (suc (suc Δ)) Σ →
 StoreDetWf (suc (suc Δ)) (renameStoreᵗ swap01ᵗ Σ)`

is false.  A store entry at index `suc zero` may contain a type mentioning
variable `zero`; after the swap the entry is at index `zero` while the renamed
type may mention `suc zero`, violating `wfOlder`.  This is not a counterexample
to the catchup lemma, but it rules out using unconstrained store renaming as the
composition-side-condition proof.

I also checked the obstruction directly in Agda:

`StoreDetWf-swap01-generic⊥ :
 StoreDetWf (suc (suc zero))
   (renameStoreᵗ swap01ᵗ ((suc zero , ＇ zero) ∷ [])) →
 ⊥`.

The impossible `wfOlder` obligation for the swapped singleton is
`WfTy zero (＇ (suc zero))`.

The remaining promising variant is shape-specific rather than generic:
transport `StoreDetWf` only for stores of the form `(zero , ★) ∷ ⟰ᵗ Σ` or the
corresponding shifted source store produced by the `⊒Λ` branch.  That shape may
make the swap safe because the head moved from `zero` to `suc zero` stores only
`★`, and the tail is already under a binder.

## Attempt 65: split the missing theorem into reduction image and body exchange

Rejected as two independent small lemmas; accepted as the next theorem shape.
I rechecked the live `remainder-nu` and `remainder-cast` last-bind branches.
They expose:

1. `↠-split-last-bind`, giving
   `⇑ᵗᵐ N —↠[ χs₀ ] P`,
   `P —→[ bind ★ ] Q`, and `Q —↠[ keeps ] W`;
2. `last-bind-source-first-body`, giving the caught-up body under

   `(⊒ zero ꞉=☆) ∷
     ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`.

The tempting reduction-only move is to apply `type-rename-bind-step-pred` to
the final `P —→[ bind ★ ] Q`.  That still fails for the same reason as Attempt
63: `P` is not known to be syntactically `⇑ᵗᵐ P₀`.  Earlier `bind` steps in
`χs₀` may have already put the source into an under-binder image.  So the
source-reduction side needs a prefix-indexed image invariant, not a last-step
inversion.

The tempting body-only move is to rename the source-first body by `swap01ᵗ`.
Attempt 64 gives endpoint transport for this, but a full `TermNarrowing`
renaming/exchange theorem is still missing.  There is no existing whole-term
`TermNarrowing` type-renaming theorem in the repo, and the needed store change
is not just renaming: the target-only `(zero ꞉= ★ ⊒)` entry has to move across
the whole emitted source-only prefix, yielding the target-first shape

`(zero ꞉= ★ ⊒) ∷
  ⇑ˢ ((⊒ zero ꞉=☆) ∷ combineStoreNrw π₀ σ)`.

Conclusion: the next useful statement should combine both sides as a
prefix-aware replay/exchange theorem.  Proving only a store permutation, only a
composition-renaming lemma, or only final-bind lowering repeats earlier dead
ends.

## Attempt 66: use the strict-narrowing merge to recover swapped-store
determinacy

Partially accepted.  After pulling the strict narrowing/widening work from
`main`, I checked whether the new determinacy lemmas changed the obstruction
from Attempt 64.  They do not remove the need for a well-formed deterministic
store after the adjacent `swap01ᵗ`; the generic store-renaming theorem is still
false for the same reason as before.

However, the shape-specific variant suggested in Attempt 64 is true for the
instantiation store shape used by the `⊒Λ` branch.  I added checked helpers in
`proof.Catchup`:

`∈-renameStoreᵗ-inv`

`StoreUnique-renameᵗ`

`StoreDetWf-rename-ext-suc`

`StoreDetWf-swap01-inst :
  StoreDetWf Δ Σ →
  StoreDetWf (suc (suc Δ))
    (renameStoreᵗ swap01ᵗ ((zero , ★) ∷ ⟰ᵗ Σ))`

The key point is that swapping `(zero , ★) ∷ ⟰ᵗ Σ` produces

`(suc zero , ★) ∷ renameStoreᵗ (extᵗ suc) Σ`.

The shifted tail under `extᵗ suc` never contains index `suc zero`, so the new
head cannot collide with the tail.  The `wfOlder` field is also preserved:
for each original entry `(α , A)`, the renamed entry needs
`WfTy (extᵗ suc α) (renameᵗ (extᵗ suc) A)`, which follows from a
bound-indexed `TyRenameWf` for `extᵗ suc`.

This is useful for a future composition/exchange theorem: determinacy can now
be applied to the swapped instantiation-store shape, instead of requiring the
false generic `StoreDetWf` renaming from Attempt 64.  It still does not prove
the `⊒Λ` branch by itself, because the branch needs whole `TermNarrowing`
replay across the emitted prefix, not just endpoint/coercion determinacy.

## Attempt 67: avoid recursive composition-commutation with determinacy

Accepted as a checked proof component.  Attempt 62 rejected a direct
structural proof that `_⨟ⁿ_` commutes with renaming because it would require a
mutual recursion through all narrowing/widening composition cases.  After
Attempt 66 supplied the safe renamed-store determinant shape, I revisited this
using determinacy instead of structural recursion.

I added a generic checked lemma in `proof.Catchup`:

`⨟ⁿ-renameᵗ-determined :
  ...
  proj₁ (_⨟ⁿ_ {wfΣ = wfΣ′}
    (narrow-renameᵗ hρ hμ s⊒)
    (narrow-renameᵗ hρ hμ t⊒))
  ≡ renameᶜ ρ (proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} s⊒ t⊒))`

The proof is one use of `narrowing-determinedᵐ`: both sides are typed
narrowings between the same renamed endpoints under the same renamed store.
So no case split over `_⨟ⁿ_` is needed.

I then added the swap-specific component lemmas for composition side
conditions:

`compose-leftⁿ-rename-swap01ᵗ-components`

`compose-rightⁿ-rename-swap01ᵗ-components`

These take the original `StoreDetWf` witness, the renamed-store `StoreDetWf`
witness, the two composition premises, and the endpoint equality premise, then
rebuild the corresponding `compose-leftⁿ`/`compose-rightⁿ` side condition
under `renameStoreNrw swap01ᵗ`.

This directly addresses the composition-side-condition problem from Attempt
62.  It still does not prove the `⊒Λ` branch by itself: a full exchange/replay
proof must still provide the right renamed-store determinant witness at each
side-condition site and, more importantly, recurse through the entire
`TermNarrowing` derivation while changing the surrounding `StoreNrw` prefix.

## Attempt 68: make composition transport symmetric and determinant-parametric

Accepted as checked support, not as the final `⊒Λ` proof.  After confirming
the branch already contained the latest `main` tip, I added the widening twin
of the narrowing composition-renaming lemma:

`⨟ʷ-renameᵗ-determined :
  ...
  proj₁ (_⨟ʷ_ {wfΣ = wfΣ′}
    (widen-renameᵗ hρ hμ s⊑)
    (widen-renameᵗ hρ hμ t⊑))
  ≡ renameᶜ ρ (proj₁ (_⨟ʷ_ {wfΣ = wfΣ} s⊑ t⊑))`

The proof is the same determinacy move as Attempt 67, using
`widening-determinedᵐ`.  This rules out an asymmetry in the composition
algebra: both `_⨟ⁿ_` and `_⨟ʷ_` commute with type renaming up to the existing
determinacy theorems, provided the renamed store has a `StoreDetWf` witness.

I then wrapped the component lemmas from Attempt 67 in checked side-condition
transport rules:

`compose-leftⁿ-rename-swap01ᵗ`

`compose-rightⁿ-rename-swap01ᵗ`

Both wrappers take an explicit argument

`∀ {Σ} →
  StoreDetWf (suc (suc Δ)) Σ →
  StoreDetWf (suc (suc Δ)) (renameStoreᵗ swap01ᵗ Σ)`

and then pattern-match on `compose-leftⁿ` or `compose-rightⁿ` to supply the
hidden store determinant to the component lemma.

This is intentionally not instantiated generically.  Attempt 64 and the
checked `StoreDetWf-swap01-generic⊥` counterexample show that the generic
determinant mapper is false.  The wrapper is still useful because it isolates
the exact side-condition needed by a future whole-term replay/exchange theorem:
the replay must provide a shape-specific determinant mapper at every
composition side-condition site.  For the instantiation-store shape,
Attempt 66 already proves the relevant shape-specific determinant.  For an
arbitrary `TermNarrowing` derivation under an emitted prefix, the remaining
work is still to thread those shape facts through the changing `StoreNrw`
prefix while replaying the term derivation.

## Attempt 69: isolate the local source/target list exchange

Accepted as checked support, not as the prefix-aware exchange theorem.  After
re-reading Attempts 60-65, I confirmed that the `⊒Λ` last-bind branch still
needs two separate movements:

1. rename the two newest type variables with `swap01ᵗ`; and
2. actually reorder a source-only store entry past a target-only store entry in
   the `StoreNrw` list.

Attempt 68 addressed the first movement through composition side conditions
under `renameStoreNrw swap01ᵗ`.  It did not perform the list reordering.  I
therefore added the local list-exchange primitive:

`⊒ˢ-source-target-swap :
  Δ ⊢ (⊒ X ꞉=☆) ∷ (Y ꞉= A ⊒) ∷ σ ꞉ Σ ⊒ˢ Σ′ →
  Δ ⊢ (Y ꞉= A ⊒) ∷ (⊒ X ꞉=☆) ∷ σ ꞉ Σ ⊒ˢ Σ′`

The proof is just the commutation of `⊒ˢ-left` and `⊒ˢ-right`:
`⊒ˢ-left (⊒ˢ-right hA σ⊒)` becomes
`⊒ˢ-right hA (⊒ˢ-left σ⊒)`.

I lifted that through endpoint equivalence and the two composition
side-condition forms:

`≈ⁿ-source-target-swap`

`compose-leftⁿ-source-target-swap`

`compose-rightⁿ-source-target-swap`

This gives the missing local list permutation for cast side conditions.  It is
still only an adjacent exchange.  The live `⊒Λ` last-bind branch exposes a
source-first body under

`(⊒ zero ꞉=☆) ∷
  ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`,

where the target-only entry is buried below the emitted prefix `π₀`.  So a full
solution must recursively bubble that target-only entry through the prefix,
using this local exchange at each adjacent source/target crossing and the
checked composition transport from Attempt 68 for cast side conditions.

## Attempt 70: close adjacent source/target swaps under prefixes

Accepted as checked support.  Attempt 69 only gave the head exchange

`(⊒ X ꞉=☆) ∷ (Y ꞉= A ⊒) ∷ σ`

to

`(Y ꞉= A ⊒) ∷ (⊒ X ꞉=☆) ∷ σ`.

The full emitted prefix needs the same adjacent crossing below arbitrary
store-narrowing prefixes, and eventually a sequence of such crossings.  I
added a checked relation:

`SourceTargetSwapRel Δ σ σ′`

with constructors for:

`swap-here`

`swap-right`

`swap-left`

`swap-both`

This represents one adjacent source/target swap, possibly below a target-only,
source-only, or both-entry prefix.  I also added:

`SourceTargetSwapRel-⇑ˢ`

`SourceTargetSwapRel-src≡`

`SourceTargetSwapRel-coercionᶜ`

`SourceTargetSwapRel-⊒ˢ`

`SourceTargetSwapRel-≈ⁿ`

`SourceTargetSwapRel-compose-left`

`SourceTargetSwapRel-compose-right`

The important invariant is `SourceTargetSwapRel-src≡`: this exchange preserves
the source store exactly, so coercion-typing side conditions can be transported
by equality rather than weakened.

I then added the reflexive/transitive closure:

`SourceTargetSwapRels Δ σ σ′`

and lifted the same operations through the closure.  This is the right
endpoint/composition-level infrastructure for "bubble this target-only entry
through a source-only prefix" as a sequence of adjacent exchanges.

This still does not prove the `⊒Λ` branch.  The closure preserves the source
and target stores, so it cannot by itself account for the de Bruijn lowering
that happens when a target-only entry is moved out from under a source-only
binder.  The full replay theorem must combine each list exchange with the
`swap01ᵗ` renaming support from Attempts 66-68.  I did not try to prove a
generic term-level transport for `SourceTargetSwapRel`: in split-shaped
derivations, swapping the distinguished source-only entry introduced by
`split` past a following target-only entry would destroy the syntactic store
shape required to rebuild `split`.  So a future term replay theorem should be
more constrained than arbitrary source/target swapping.

## Attempt 71: classify empty-target emitted prefixes

Accepted as checked support.  I added a small source-prefix classifier:

`SourceStarOnly`

and proved:

`⊒ˢ-empty-source-star-only :
  Δ ⊢ π ꞉ Σ ⊒ˢ [] →
  SourceStarOnly π`

The live last-bind `⊒Λ` branches always have target store `[]`, so the emitted
prefix contains only source-star entries.  This rules out a target-side case
split as the missing ingredient: the remaining job is to move the outer
target-only `⊒Λ` binder through a source-star prefix, not to discover hidden
target entries in that prefix.

## Attempt 72: test whether source-target swaps alone can bubble the prefix

Rejected as insufficient.  For the empty prefix, renaming with `swap01ᵗ`
makes the final source-only binder and target-only binder adjacent.  I added
checked normalizations:

`swap01ᵗ-after-suc-suc`

`renameᵗ-swap01-⇑⇑`

`renameᶜ-swap01-⇑⇑`

`renameᵗᵐ-swap01-⇑⇑`

`renameStoreNrw-swap01-⇑ˢ⇑ˢ`

But for a nonempty emitted source prefix, a single closure of
`SourceTargetSwapRel` is not enough.  Each crossing needs a local
`swap01ᵗ` renaming before the adjacent list exchange.  A plain swap closure
keeps the wrong de Bruijn levels.

## Attempt 73: add the empty bubble base and term-renaming support

Accepted as checked support.  I added:

`source-target-bubble-empty`

which proves the empty-prefix exchange:

`SourceTargetSwapRels Δ
  (renameStoreNrw swap01ᵗ
    ((⊒ zero ꞉=☆) ∷ ⇑ˢ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)))
  ((zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ))`

I also added term-renaming bookkeeping that a future replay theorem will need:

`lookup-renameCtxNrw`

`renameCtxNrw-dual-cons`

`renameStoreNrw-coercionᶜ`

The useful bubble step must first rename a body derivation by `swap01ᵗ` and
then perform adjacent source/target swaps.  The remaining obstacle is not the
nonrecursive lookup/store bookkeeping; it is replaying every `TermNarrowing`
constructor through the combined rename-and-swap step.

## Attempt 74: reject arbitrary term transport across swaps

Rejected.  I tried to revive a structural term transport for arbitrary
`SourceTargetSwapRel`, using the renaming support from Attempt 73 and the
composition-side lemmas from Attempts 67-70.  The proof gets stuck at:

`SourceTargetSwapRel-term (swap-right swap-here) (split ...)`

This is not just an Agda annoyance.  The step moves the distinguished
source-only marker of `split` past a following target-only entry.  After that
movement the store no longer has the syntactic
`target-only, source-only` shape required by the `split` constructor.  A sound
term replay theorem must be split-aware.

## Attempt 75: classify split-shaped single swaps

Accepted as checked support.  I added:

`SplitSourceTargetSwapView`

and:

`split-source-target-swap-view`

For a store of the form:

`(α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ`

the first swap is either:

`split-swap-safe`, which happens below the split marker and can be replayed
structurally, or

`split-swap-unsafe`, the exact `swap-right swap-here` case from Attempt 74.

This makes the split obstruction explicit instead of rediscovering it during
whole-term replay.

## Attempt 76: lift the split classification to swap closures

Accepted as checked support.  I added:

`SplitSourceTargetSwapsView`

and:

`split-source-target-swaps-view`

The closure view has three cases:

`split-swaps-refl`

`split-swaps-safe-step`

`split-swaps-unsafe-step`

This is the right shape for a future replay theorem.  It can consume zero
swaps, continue below the split marker for a safe first step, or stop at the
unsafe first step and hand that case to split/opening catchup machinery.

## Attempt 77: recheck after pulling `main` and revisit reduction-only unshift

Rejected as a standalone path.  On 2026-06-29 I fetched `origin/main`; this
branch was already up to date.  I reran:

`agda -v0 proof/Catchup.agda`

and the file still type-checks.

I then revisited the reduction-only idea: invert the prefix reduction

`⇑ᵗᵐ N —↠[ χs₀ ] P`

and the final bind step from `P` by repeatedly applying `predᵗ`.
The existing library has useful pieces:

`keep-pred-step-view`

`pure-pred-↠-shifted-value`

`type-rename-bind-step-pred`

However, this does not scale through earlier `bind` steps in `χs₀`.  A
general bind step is not stable under plain `predᵗ`: the coercion under a
runtime `ν` binder uses `extᵗ`, while the surrounding term shift uses `suc`.
The one-step lemma `type-rename-bind-step-pred` works only when the source is
known to be a global shift image.  After an earlier bind, the target may no
longer be a global shift image, even though the later value-reaching trace is
sound.

So the remaining proof cannot be a reduction-only unshift.  It must keep the
source/target binder-exchange invariant from Attempts 71-76 and replay the
term-narrowing history while performing the local `swap01ᵗ` crossing at each
emitted source-star binder.  The promising next target is a split-aware replay
theorem that consumes `SplitSourceTargetSwapsView`; the unsafe branch should
delegate to the same split/opening machinery needed by `catchup-split-catchup`.

## Attempt 78: turn the safe split view into a rebuild operation

Accepted as checked support.  Attempt 76 classified swap closures at a split
marker, but did not yet provide a way to use the safe case.  I added closure
prefix lifts:

`SourceTargetSwapRels-right`

`SourceTargetSwapRels-left`

`SourceTargetSwapRels-both`

These are the closure-level counterparts of `swap-right`, `swap-left`, and
`swap-both`.  They let a replay theorem keep a swap sequence aligned when it
passes under a target-only entry, a source-only entry, or a both-side
coercion entry.

I then added:

`split-source-target-safe-rebuild`

This lemma rebuilds a `split` after a whole swap closure that stays below the
split marker.  Its premise is the recursively transported body under
`(α ꞉ q) ∷ σ′`; the lemma transports the two split side conditions through the
lifted closure

`SourceTargetSwapRels-right (SourceTargetSwapRels-left rels)`

and reconstructs the outer split under

`(α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ′`.

Finally I added:

`split-source-target-swaps-safe-view`

which proves that every closure produced by `right (left rels)` is classified
by `SplitSourceTargetSwapsView` as zero or safe-first-step, never as the
unsafe split-marker crossing.

This still does not prove the `⊒Λ` branch.  It discharges the safe branch of
the split-aware replay once a recursive transport of the split premise has
already been obtained.  The remaining hard case is exactly the unsafe
`swap-right swap-here` crossing, which must use split/opening catchup rather
than structural reconstruction.

## Attempt 79: package the normalized source-first body as `ν⊒`

Accepted as checked support, but not a complete proof path.  The last-bind
branches already expose a normalized body of the shape:

`(⊒ zero ꞉=☆) ∷ ⇑ˢ (combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ))`

This is exactly the premise store shape of `ν⊒`.  To make that observation
usable, I added:

`gen-body-coercionᶜ-tag`

which relaxes the body of a `gen` coercion from `genᵈ tag-or-idᵈ` mode to
ordinary `∶ᶜ` mode, and:

`catchup-gen-body-ordinary-coercionᶜ`

which transports that ordinary body coercion through the recursive emitted
prefix under the outer `⊒Λ` target-only binder.

With those side conditions available, I added:

`source-first-body-ν⊒`

This packages a normalized source-first body as:

`ν ★ W (⇑ᶜ (applyCoercions χs p)) ⊒ applyTerms χs V′`

under the store:

`combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)`

The limitation is important.  This bridge re-expresses the *already caught-up*
body `W` as the premise of a new `ν⊒` derivation.  It does not prove that the
original source `N` reduces to this newly packaged `ν ★ W ...` term.  Calling
`catchup-ν⊒-catchup` on the packaged relation would therefore prove catchup for
the wrong source unless it is paired with a separate history-preserving replay
that connects the original `χs₀` prefix and final bind step to this `ν⊒`
source.

## Attempt 80: lower the final-bind tail context for the `ν⊒` bridge

Accepted as checked support.  Attempt 79 packaged a normalized source-first
body, but the live last-bind branches expose the tail narrowing `π₀` in the
full post-bind type context:

`Δ′ ⊢ π₀ ꞉ applyStores χs₀ [] ⊒ˢ []`

where:

`Δ′ ≡ applyTyCtxs (χs₀ ++ bind Aχ ∷ keeps) (suc Δ)`

The `ν⊒` bridge needs `π₀` in the lowered tail context:

`applyTyCtxs χs₀ (suc Δ)`

This is valid because the target store is empty, so `π₀` contains only
source-star entries and its typing is independent of the type context.  Rather
than adding a new lowering lemma, I reused the existing:

`⊒ˢ-empty-anyᵗ`

I added:

`last-bind-source-first-ν⊒`

This consumes the actual branch facts:

`π ≡ (⊒ zero ꞉=☆) ∷ ⇑ˢ π₀`

`Δ′ ≡ applyTyCtxs (χs₀ ++ bind Aχ ∷ keeps) (suc Δ)`

the original outer `gen` coercion typing, the full-context `π₀⊒`, and the
caught-up body `W⊒V′`.  It uses `last-bind-source-first-body` plus
`applyTyCtxs-last-bind` to transport the body to
`suc (applyTyCtxs χs₀ (suc Δ))`, lowers `π₀⊒` with `⊒ˢ-empty-anyᵗ`, and then
calls `source-first-body-ν⊒`.

This is the first checked lemma that directly matches the live last-bind branch
facts.  It still packages a new source `ν ★ W ...`; it does not yet replay the
original source `N` to that package, so it cannot replace the remaining
`catchup-⊒Λ-catchup` calls by itself.

## Attempt 81: add the split marker to an inner `⊒Λ` body

Accepted as checked support.  The final bind creates a source-star marker that
the existing `split` machinery knows how to reason about, but the original
inner `⊒Λ` body has only the target-only binder:

`(zero ꞉= ★ ⊒) ∷ ⇑ˢ σ`

I added:

`⊒Λ-body-add-split-marker`

This proves that an inner body:

`⇑ᵗᵐ N ⊒ V′ ∶ p`

under the target-only store can be transported to the split-shaped store:

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ`

without changing the visible source, target, or coercion.

The proof first uses `extend-replace-here-current` with `id ★` to move the body
from the target-only entry to a both-side entry.  Then it applies `split` to the
double-shifted source/target/coercion:

`⇑ᵗᵐ (⇑ᵗᵐ N)`

`⇑ᵗᵐ V′`

`⇑ᶜ p`

and uses `open-shiftᵐ` / `open-shiftᶜ` to rewrite both openings back to the
original body shape.

This gives a checked bridge from the `⊒Λ` premise to the split/opening
machinery needed for the unsafe marker crossing.  It does not by itself prove
the live last-bind branch: instantiated at the inner `suc Δ` context, the
result still reduces the shifted source `⇑ᵗᵐ N`, not the unshifted source `N`.
So the remaining missing piece is still the history-preserving replay that
moves the emitted source-star marker outward while lowering the source term.

## Attempt 82: add the split marker to caught-up body evidence

Accepted as checked support.  Attempt 81 changes a direct body relation, but
the live `catchup-lemma` branch has the stronger package produced by the
recursive call:

`⇑ᵗᵐ N —↠[ χs ] W`

`W ⊒ applyTerms χs V′ ∶ applyCoercions χs p`

I added:

`⊒Λ-body-split-marker-catchup`

This factors the same split-marker move through `catchup-split-catchup`.  The
proof opens the shifted source as:

`(⇑ᵗᵐ (⇑ᵗᵐ N)) [ zero ]ᵀ`

and uses `catchup-extend-transport` to move the final body relation from the
target-only entry to the temporary `(zero ꞉ id ★)` entry expected by
`catchup-split-catchup`.  The opened `gen` body coercion is weakened under that
temporary source-store entry with `StoreIncl-drop`, matching the shape already
used by `gen-body-open-split-coercion`.

The result is a catchup package for the split-shaped store:

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ`

It still reduces the shifted source:

`⇑ᵗᵐ N —↠[ χs′ ] W′`

rather than the original unshifted source `N`.  So this isolates the remaining
gap more sharply: after the recursive catchup evidence has been replayed through
the split marker, the proof still needs a history-lowering/replay lemma that
connects the shifted-source catchup package back to the original source term.

## Attempt 83: use the packaged `ν⊒` relation as the branch result

Rejected by a focused Agda probe.  I temporarily replaced the live
`remainder-nu` / last-bind / `nu-base-empty` branch result with:

`last-bind-source-first-ν⊒ keeps-ok π≡ Δ′≡ pᶜ π₀⊒ W⊒V′`

Agda inferred exactly the expected package from Attempts 79 and 80:

`ν ★ W (⇑ᶜ (applyCoercions χs₀ p)) ⊒ applyTerms χs₀ V′`

under:

`combineStoreNrw π₀ ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)`

The branch goal, however, is a full catchup package whose reduction component
starts from the original source:

`ν A L c —↠[ χs₁ ] W₁`

and whose final relation targets:

`applyTerms χs₁ (Λ V′) ∶ applyCoercions χs₁ (gen A p)`.

So the `ν⊒` package is still the wrong source term.  It may be a useful
intermediate once a replay theorem connects the original prefix/final bind to
that packaged `ν` source, but by itself it cannot replace the remaining
`catchup-⊒Λ-catchup` call.

## Attempt 84: repair the `TraceProbe` counterexample with legal `var0-fun`

Rejected as a counterexample family.  The old `TraceProbe` counterexample uses
the illegal body coercion `probe-c`; Attempt 50 showed that it cannot satisfy a
real empty-context `gen` premise.  I tested the obvious legal replacement:

`p = var0-fun`

and tried to build the shifted final-body premise:

`1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
  ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩ ⊒ ƛ (` 0) ∶ var0-fun`

The nearby checked example witness `ex1-inner-cast+` does not fit this store;
Agda reports the head entry mismatch:

`0 ꞉ id ★ != 0 ꞉= ★ ⊒`

This blocks the direct lift of the checked example witness.  The legal
`var0-fun` examples in `NarrowingExamples` use a source-side marker/both-side
`id ★` store before the final cast is typed, and that marker is exactly what
the last-bind/split path creates.  So the standalone `TraceProbe`
counterexample still cannot be lifted to a legal `catchup-⊒Λ-catchup`
counterexample by simply replacing `probe-c` with `var0-fun`; a stronger
counterexample would need a different final-body derivation, not just this
nearby example.

## Attempt 85: make the legal helper counterexample use a casted body

Rejected, and the failure points to a possible invariant.  I tried to build the
legal analogue of `TraceProbe` directly under the target-only store:

`1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
  ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩ ⊒ ƛ (` 0) ∶ var0-fun`

The first repair was to use the target-only store narrowing in the endpoint
equivalence but keep the composition determinant over the source store `[]`.
That part is consistent.  The proof then fails at the `cast-⊒` constructor:
the outer cast is `var0-fun`, but the easy composition side condition gives a
result coercion `id (＇ 0) ↦ id (＇ 0)`, not `var0-fun`.

The existing way to recover result coercion `var0-fun` is the
`ex1-inner-cast+` shape, which adds a second cast by `- star-seal-fun`.
That requires a source-side marker/both-side `id ★` store; it is not available
under `(0 ꞉= ★ ⊒) ∷ []`.

So the legal `gen` premise is doing more than excluding the old `probe-c`.
It also seems to block the non-shift-image casted final value under the
target-only store.  A promising next invariant is:

if `gen A p` is well typed and a value `W` is related to `V′` by `p` under the
target-only `⊒Λ` store, then `W` is a type-shift image (or can be caught up to
one through the emitted source-star prefix).

## Attempt 86: prove the legal target-only casted body impossible

Accepted as checked diagnostic support in `proof.TraceProbe`.  After pulling
the newer `main`, I reused the counterexample style from
`proof.RightSealInversionCounterexample`: avoid coverage getting stuck on the
defined dual operation by proving an equality-indexed auxiliary.

The checked theorem is:

`no-legal-target-cast-body :
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩ ⊒ ƛ (` 0) ∶ var0-fun →
  ⊥`

There are two possible left-cast shapes.

In the `cast+⊒` case, the visible cast requires `- t ≡ var0-fun`.  The helper
`no-dual-var0-fun-narrow` shows this impossible: the domain component would
make `(＇ 0) ？` a widening, but the widening grammar has no such case.

In the `cast-⊒` case, the composition side condition would have to type:

`r ≈ var0-fun ⨾ⁿ var0-fun`

The helper `no-var0-fun-self-compose` extracts endpoints from the two
`var0-fun` typings with `coercion-src-tgtᵐ`, forcing the shared middle type to
be both `★ ⇒ ★` and `＇ 0 ⇒ ＇ 0`.

This rules out the direct legal replacement for the old `probe-c`
counterexample under the target-only `⊒Λ` body store.  It still does not prove
the live last-bind branch: the real branch may create the source-side marker
through the emitted bind/split path, and the remaining theorem still needs a
replay/lowering argument for that emitted source-star prefix.

## Attempt 87: inspect the live `remainder-nu` last-bind goal

I added a temporary hole in the live

`remainder-nu / last-bind / nu-base-empty`

branch after splitting the final bind.  Agda's expected type refined the source
of the outer catchup goal to the original `ν` source:

`ν A L c —↠[ χs₁ ] W₁`

and the final relation still targets the outer lambda:

`W₁ ⊒ applyTerms χs₁ (Λ V) ∶ applyCoercions χs₁ (gen A₁ p)`.

So the rich `NuSourceValueTarget` history has not lost the fact that the source
is a `ν`; the erasure only happens when the branch immediately collapses the
history with `nu-source-value-target-base-empty`.

I then checked whether this suggests a direct use of the existing
`catchup-ν⊒-catchup` postulate.  It does not directly fit.  That postulate
catches up a `ν ★ N (⇑ᶜ p)` source to the body target `V`, whereas this branch
must catch up the original `ν A L c` source to `Λ V` under `gen A₁ p`.  A
separate rebuild would still be needed to turn a body-target catchup into the
outer `⊒Λ` conclusion.  The no-bind helper can do such a rebuild only when the
final value is known to be a type-shift image; the last-bind path is precisely
where that image invariant can fail because the emitted source-star marker may
be introduced by the final `ν-step`.

This rules out the naive "use the rich history, then call `catchup-ν⊒-catchup`"
route.  The useful fact retained from the probe is narrower: branch-specific
helpers can assume the concrete original source shape (`ν A L c` or a cast),
but they still need the same prefix replay/lowering argument to rebuild the
outer lambda target.

## Attempt 88: recursively catch up the extracted `ν` base body

Rejected by Agda's termination checker.  Since Attempt 87 showed that the live
`remainder-nu` branch refines the original source to `ν A L c`, I tested
whether we could use the base body exposed by
`nu-source-value-target-base-empty hist`:

`bodyBase :
  suc Δ₀ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ₀ ∣ []
    ⊢ N₀ ⊒ ⇑ᵗᵐ V₀ ∶ ⇑ᶜ p₀`

and make a second recursive call:

`catchup-lemma (renameᵗᵐ-preserves-Value suc vBase) bodyBase`.

Agda rejects the resulting definition for `catchup-lemma` termination.  The
problem is expected: `bodyBase` is extracted through the computed
`ShiftedSourceRemainder`/`NuSourceValueTarget` history, so the termination
checker no longer recognizes it as a syntactic subderivation of the original
`N⊒V′` argument.  This rules out the simple base-recursion strategy unless the
whole proof is refactored into an explicitly structural recursion over the
history, which would be a much larger change and would still have to replay all
wrappers (`extend`, `split`, `⊒Λ`, casts) back to the outer target.

So the live branch should continue to use the already accepted recursive call
on the immediate subderivation `N⊒V′`; any additional reasoning must transform
that catchup package rather than making a hidden second recursive call on the
erased base.

## Attempt 89: prove reduction lowering for an all-keep prefix plus one bind

Accepted as checked reduction infrastructure in `proof.ReductionProperties`.
The remaining last-bind branches split the recursive reduction as:

`⇑ᵗᵐ N —↠[ χs₀ ] P`

`P —→[ bind Aχ ] Q`

`Q —↠[ keeps ] W`

where `keeps` is all `keep`.  If `χs₀` is also all `keep`, then the reduction
part can be lowered without using the false shifted-source inversion.  I added:

`shift-image-bind-step-pred`

This lowers a single `bind` step out of a known type-shift image:

`M —→[ bind A ] N`

to:

`renameᵗᵐ predᵗ M —→[ bind (renameᵗ predᵗ A) ] renameᵗᵐ predᵗ N`.

The proof uses the existing `type-rename-bind-step-pred` after exposing the
`TermShiftImage M` witness.

I then added:

`safe-allKeep-bind-pred-↠`

This lowers an all-keep prefix followed by one `bind` and an all-keep tail:

`M —↠[ χs ] P`

`P —→[ bind A ] Q`

`Q —↠[ keeps ] W`

to:

`renameᵗᵐ predᵗ M
  —↠[ χs ++ bind (renameᵗ predᵗ A) ∷ keeps ]
  renameᵗᵐ predᵗ W`

provided `M` is both `CatchupSafe` and a `TermShiftImage`, and both `χs` and
`keeps` are all `keep`.  The proof uses `safe-keep-step-image-view` to keep
each intermediate prefix term in the shift-image fragment.  If a prefix step
falls into the doomed branch, its continuation through the remaining prefix,
the `bind`, and the tail reaches the value `W`, contradiction.

Finally I added the exact corollary needed at shifted sources:

`safe-allKeep-bind-pred-↠-shifted`

which starts from `⇑ᵗᵐ M` and returns a reduction from the original `M`.

This is genuine progress on the last-bind case, but it does not by itself
replace `catchup-⊒Λ-catchup`.  Even in the no-earlier-bind subcase, the final
body relation produced by the recursive call lives under the source-first store:

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ...`

whereas rebuilding the outer `⊒Λ` needs the target-first split-marker store:

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ...`

The missing piece is therefore now isolated on the term-narrowing side: a
split-aware source/target marker replay or store-swap transport for the final
body relation.  The reduction component for the single-bind/no-earlier-bind
case no longer requires the false shifted-source inversion.

## Attempt 90: instantiate the single-bind lowering in the live `ν` branch

Accepted as a diagnostic probe, then reverted.  I temporarily split `χs₀` in
the live

`remainder-nu / last-bind / nu-base-empty`

branch and considered the subcase:

`storeChangesLastBind χs₀ = no-bind keeps₀`.

Using Attempt 89, Agda accepted the reduction component of the natural
candidate package:

`χs′ = χs₀ ++ bind (renameᵗ predᵗ Aχ) ∷ keeps`

`W′ = renameᵗᵐ predᵗ W`

`N —↠[ χs′ ] W′`

where the reduction proof was:

`safe-allKeep-bind-pred-↠-shifted
  (value-target-source-safe vV′ N⊒V′)
  keeps₀ keeps-ok ⇑N↠P P→Q Q↠W vW`.

After also choosing the emitted store narrowing:

`π′ = (⊒ zero ꞉=☆) ∷ []`

Agda reduced the remaining obligation to the final term relation:

`Δ′′ ∣ combineStoreNrw ((⊒ zero ꞉=☆) ∷ []) σ ∣ []
  ⊢ renameᵗᵐ predᵗ W
    ⊒ applyTerms (χs₀ ++ bind (renameᵗ predᵗ Aχ) ∷ keeps) (Λ V)
    ∶ applyCoercions (χs₀ ++ bind (renameᵗ predᵗ Aχ) ∷ keeps)
        (gen A p)`.

Trying to rebuild that relation with `⊒Λ` first exposed only the expected
normalization mismatch:

`Λ _` versus

`applyTerms (χs₀ ++ bind (renameᵗ predᵗ Aχ) ∷ keeps) (Λ V)`.

The existing all-keep/last-bind normalization lemmas should rewrite this target
to:

`Λ (renameᵗᵐ (extᵗ suc) V)`,

and similarly rewrite the coercion to:

`gen (⇑ᵗ A) (renameᶜ (extᵗ suc) p)`.

The body relation that would remain is the real blocker:

`⇑ᵗᵐ (renameᵗᵐ predᵗ W)
  ⊒ renameᵗᵐ (extᵗ suc) V
  ∶ renameᶜ (extᵗ suc) p`

under the target-first split-marker store

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)`.

The recursive catchup body instead gives:

`W ⊒ ⇑ᵗᵐ V ∶ ⇑ᶜ p`

under the source-first store

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`.

So the reduction lowering from Attempt 89 is usable in the live branch.  The
remaining no-earlier-bind obstruction is specifically a term-narrowing replay:
rename the source-first body relation by `swap01ᵗ`, rewrite
`renameᵗᵐ swap01ᵗ (⇑ᵗᵐ V)` to `renameᵗᵐ (extᵗ suc) V` and
`renameᶜ swap01ᵗ (⇑ᶜ p)` to `renameᶜ (extᵗ suc) p`, then perform the adjacent
source/target store swap.  This is the term-level counterpart of the
store/coercion/equivalence swap lemmas already present from Attempts 72-78.

## Attempt 91: factor the single-bind `⊒Λ` packaging

Accepted as checked support in `proof.Catchup`.

I added:

`catchup-⊒Λ-single-bind-finish`

The lemma packages the no-earlier-bind candidate once the remaining target-first
body relation is available.  Its inputs are:

`AllKeep χs`

`AllKeep keeps`

`N —↠[ χs ++ bind ★ ∷ keeps ] W′`

and the body relation

`suc (suc Δ) ∣
  (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
  ⊢ ⇑ᵗᵐ W′ ⊒ renameᵗᵐ (extᵗ suc) V′
    ∶ renameᶜ (extᵗ suc) p`.

It returns the full catchup existential for

`Δ ∣ σ ∣ [] ⊢ N ⊒ Λ V′ ∶ gen A p`

with witnesses

`χs′ = χs ++ bind ★ ∷ keeps`

`Δ″ = suc Δ`

`Π″ = (zero , ★) ∷ []`

`Π″′ = []`

`π′ = (⊒ zero ꞉=☆) ∷ []`.

The proof discharges the previously noisy target/coercion normalization:

`applyTerms χs′ (Λ V′)
  = Λ (renameᵗᵐ (extᵗ suc) V′)`

and

`applyCoercions χs′ (gen A p)
  = gen (⇑ᵗ A) (renameᶜ (extᵗ suc) p)`.

This confirms that the final packaging is not another hidden blocker.  After
Attempt 89 supplies the lowered reduction, the only missing proof obligation in
the no-earlier-bind last-bind branch is still the target-first body replay:

`W ⊒ ⇑ᵗᵐ V ∶ ⇑ᶜ p`

under

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`

must be transported to

`⇑ᵗᵐ (renameᵗᵐ predᵗ W)
  ⊒ renameᵗᵐ (extᵗ suc) V
  ∶ renameᶜ (extᵗ suc) p`

under

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)`.

This replay likely needs a split-aware term-renaming theorem for the safe store
shape, plus the invariant that source terms under the source-first store cannot
mention the target-only variable `suc zero`.  A generic `swap01ᵗ` term-renaming
theorem remains suspect because arbitrary determinant stores are not preserved
by the swap (`StoreDetWf-swap01-generic⊥`).

## Attempt 92: refine the replay target to an asymmetric transport

Reasoning step, not yet checked as code.

Attempt 91 originally described the missing body replay as a symmetric
`swap01ᵗ` transport plus a separate invariant saying that the source term cannot
mention the target-only variable `suc zero`.  That invariant is too naive:
source-side casts can mention target-only type variables through the coercions
used by cast rules, as in the old `TraceProbe` examples.  So a proof should not
try to show:

`renameᵗᵐ swap01ᵗ W = ⇑ᵗᵐ (renameᵗᵐ predᵗ W)`

by syntactic absence of variable `suc zero`.

The exact source term required by Attempt 91 is instead already represented by
the existing `raise0ᵗ` helpers:

`raise0ᵗ X = suc (predᵗ X)`

and

`renameᵗᵐ-raise0-pred :
  renameᵗᵐ raise0ᵗ W ≡ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)`.

So the next replay theorem should be asymmetric:

source side:

`W ↦ renameᵗᵐ raise0ᵗ W`

target/coercion side:

`⇑ᵗᵐ V ↦ renameᵗᵐ swap01ᵗ (⇑ᵗᵐ V)
        = renameᵗᵐ (extᵗ suc) V`

`⇑ᶜ p ↦ renameᶜ swap01ᵗ (⇑ᶜ p)
      = renameᶜ (extᵗ suc) p`.

Store side:

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`

should map to

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)`.

This is not an ordinary type-variable renaming theorem.  It collapses the
source marker `zero` to source marker `suc zero` on the left, while moving the
target marker `suc zero` to target marker `zero` on the right.  That shape looks
closer to a split-aware source/target retagging theorem than to the symmetric
`SourceTargetSwapRels` replay from Attempts 72-78.

This also explains why a generic `swap01ᵗ` term transport is the wrong target
for the single-bind branch: it produces `renameᵗᵐ swap01ᵗ W`, but the lowered
reduction from Attempt 89 produces `renameᵗᵐ predᵗ W`, and the outer `⊒Λ`
requires `⇑ᵗᵐ (renameᵗᵐ predᵗ W)`, i.e. `renameᵗᵐ raise0ᵗ W`.

## Attempt 93: factor checked retagging infrastructure

Accepted as checked support in `proof.Catchup`.

I added the first reusable pieces for the asymmetric replay target from
Attempt 92:

`source-target-bubble-empty-coercionᶜ`

`source-target-bubble-empty-≈ⁿ`

These show that ordinary coercion typing and plain coercion equivalence can be
renamed by `swap01ᵗ` and then moved from the source-first store

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`

to the target-first store

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)`.

I also added the `raise0ᵗ` double-shift stability lemmas and

`source-target-raise0-coercionᶜ`.

This proves the source-side half needed by source casts: if a coercion is typed
against the source-first source store, then renaming it by `raise0ᵗ` is typed
against the target-first source store.

This narrows the unsolved part.  The missing theorem is not basic coercion
typing or plain equivalence transport.  It is the mixed composition transport
needed by source-side cast constructors in the asymmetric term replay.  In a
`cast-⊒` branch, the desired output has the shape

`renameᶜ swap01ᵗ r ≈ renameᶜ raise0ᵗ t ⨾ⁿ renameᶜ swap01ᵗ p`.

The existing symmetric composition transport gives

`renameᶜ swap01ᵗ r ≈ renameᶜ swap01ᵗ t ⨾ⁿ renameᶜ swap01ᵗ p`

when the determinant-store side condition is available.  That is not enough:
the source term produced by the lowered reduction contains
`renameᶜ raise0ᵗ t`, not `renameᶜ swap01ᵗ t`.  Proving, refuting, or avoiding
that mixed composition statement is now the concrete next obstruction.

## Attempt 94: checked counterprobe for generic mixed composition

Accepted as checked support in `proof.TraceProbe`.

I added a small no-postulate probe around the mixed composition target from
Attempt 93.  In the source-first store

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ []`

the identity coercion on type variable `1`,

`id (＇ 1) ↦ id (＇ 1)`,

can compose with itself on the right:

`id-var1-fun ≈ id-var1-fun ⨾ⁿ id-var1-fun`.

But after moving to the target-first store

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ []`

the analogous mixed target

`probe-c ≈ id-var1-fun ⨾ⁿ probe-c`

is impossible, because the left component of the composition would need source
type `＇ 0 ⇒ ＇ 0`, while `id-var1-fun` has source type `＇ 1 ⇒ ＇ 1`.

So the fully generic mixed-composition replay is false.  This does not yet
refute the actual `catchup-lemma`, because the probe is still not known to arise
from the real `⊒Λ`/`gen` premise.  It does rule out the tempting theorem that
would replay arbitrary source-first `compose-rightⁿ` derivations by changing
only the first source-side coercion to `renameᶜ raise0ᵗ`.

Next restriction to investigate: prove or refute the mixed-composition replay
under the additional invariant supplied by the real `gen` premise, or avoid
that replay entirely by deriving the single-bind body relation through
catchup/left-narrowing rather than by structural retagging of every constructor.

## Attempt 95: check whether the mixed counterprobe can be a `gen` body

Accepted as checked support in `proof.TraceProbe`, and rejected as a
counterexample to the live `⊒Λ` case.

The Attempt 94 mixed-composition counterprobe uses

`id-var1-fun = id (＇ 1) ↦ id (＇ 1)`.

Trying to make this the body coercion of a legal `gen` premise runs into the
side condition of `cast-gen`:

`occurs zero B ≡ true`.

For the probe target `B = ＇ 1 ⇒ ＇ 1`, this side condition reduces to `false ≡
true`, so no such `gen` premise can be constructed.  The new checked lemma is:

`no-id-var1-fun-gen-target :
  Δ ∣ Σ ⊢ gen A id-var1-fun ∶ᶜ A ⊒ `∀ (＇ 1 ⇒ ＇ 1) → ⊥`

This explains why the generic replay theorem is false while the actual
`catchup-lemma` branch may still be sound: the real premise deliberately
inserts a target occurrence of the freshly bound variable.  The relevant
existing infrastructure is `narrowing-all-gen-overlap⊥`, which packages this
occurrence gap as an impossible overlap between an ordinary shifted `∀` body
and a legal `gen` body.

Next step: use the `cast-gen` occurrence invariant, or
`narrowing-all-gen-overlap⊥` directly, to rule out the bad source-cast replay
branches instead of proving a free-standing mixed-composition theorem.

## Attempt 96: check whether `Value W` rules out the bad mixed replay

Accepted as checked support in `proof.TraceProbe`, and rejected as a sufficient
invariant.

I lifted the Attempt 94 coercion-level obstruction to a term-level source that
is already a value.  The new checked relation is:

`source-first-id-var1-cast⊒ :
  2 ∣ (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ id-var1-fun ⟩ ⊒ ƛ (` 0) ∶ id-var1-fun`

with the separate checked value witness:

`source-first-id-var1-cast-value :
  Value ((ƛ (` 0)) ⟨ id-var1-fun ⟩)`.

So the source-first body relation can have a value source and still use the
bad `cast-⊒` shape.  Replaying that branch asymmetrically would need the
target-first mixed composition

`r ≈ id-var1-fun ⨾ⁿ probe-c`

under

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ []`,

and the new checked lemma

`target-first-id-var1-probe-compose⊥`

rules that out by comparing the target endpoint of `id-var1-fun` with the
source endpoint of `probe-c`.

Conclusion: the no-earlier-bind body replay cannot be justified merely by the
fact that the caught-up source `W` is a `Value`.  The next restriction really
must use the provenance of the body relation from the legal `gen` premise
(`occurs zero B ≡ true`), or avoid replaying source-side cast constructors
altogether.

## Attempt 97: expose the legal `gen` occurrence invariant in `Catchup`

Accepted as checked support in `proof.Catchup`.

I added the direct inversion helper:

`gen-target-occursᶜ :
  Δ ∣ Σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  occurs zero B ≡ true`

and its catchup-transported form:

`catchup-gen-target-occursᶜ :
  ...
  occurs zero (applyTysUnderTyBinders χs B) ≡ true`.

These make the side condition from `cast-gen` available without redoing the
coercion inversion at each later proof site.

I also wrapped the existing determinacy overlap lemma in the surface shape
needed when a legal `gen` source is itself a forall:

`gen-source-all-overlap⊥ :
  StoreDetWf Δ Σ →
  Δ ∣ Σ ⊢ gen (`∀ A) p ∶ᶜ `∀ A ⊒ `∀ B →
  extᵈ tag-or-idᵈ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊒ B →
  ⊥`.

This packages `narrowing-all-gen-overlap⊥` using the occurrence proof from the
real `gen` premise and the `genᵈ` body typing from `gen-body-coercionᶜ`.

Limitation: this proves exactly the all/gen overlap exclusion used by
coercion determinacy.  It does not by itself solve the arbitrary source-side
cast replay from Attempt 96, because a casted source value can still use a
non-forall function coercion.  The next proof attempt has to either:

1. show that the live last-bind source-cast replay only needs the all/gen
   overlap case once the legal `gen` body is tracked with its mode, or
2. avoid structural replay of source-side casts and instead use the
   value-level left-widening/left-narrowing route on the smaller base witness.

## Attempt 98: isolate the double-shift endpoint where `raise0ᵗ` and `swap01ᵗ` agree

Accepted as checked support in `proof.Catchup`.

The generic mixed-composition replay from Attempts 94 and 96 is false because
the right component can have an arbitrary source endpoint.  Rechecking the live
last-bind `⊒Λ` branch shows an extra invariant: the body coercion supplied by
the real `gen` premise is opened under two type binders, so the relevant source
endpoint has shape `⇑ᵗ (⇑ᵗ A)`.

On that restricted syntax, the two renamings used by the desired replay agree.
I added the direct equalities:

`renameᵗ-raise0-swap01-⇑⇑`,
`renameᶜ-raise0-swap01-⇑⇑`, and
`renameᵗᵐ-raise0-swap01-⇑⇑`.

These are immediate consequences of the existing `rename*-raise0-⇑⇑` and
`rename*-swap01-⇑⇑` lemmas, but naming the bridge makes the next proof target
more explicit.

Limitation: this is still algebra on syntax, not the mixed-composition replay
itself.  It does not move a `compose-rightⁿ` proof across the source/target
binder swap.  The next target is a restricted replay theorem for
`compose-rightⁿ` whose right component has a double-shifted source endpoint,
rather than the false arbitrary theorem refuted by the earlier probes.

## Attempt 99: split off the last-bind reduction inversion

Accepted as checked support in `proof.Catchup`.

The broad shifted-source postulate bundles two different jobs:

1. invert the reduction from `⇑ᵗᵐ N` so the unshifted source `N` reaches
   `renameᵗᵐ predᵗ W`, and
2. replay the final body relation under the target-first store prefix.

The first job is already supported by `safe-allKeep-bind-pred-↠-shifted` from
`proof.ReductionProperties`.  I added the small local wrapper
`last-bind-pred-reduction`, specialized to the `bind ★` shape forced by
`last-bind-empty-target-star`:

`N —↠[ χs ++ bind ★ ∷ keeps ] renameᵗᵐ predᵗ W`.

This uses `value-target-source-safe` as the intended source of the
`CatchupSafe (⇑ᵗᵐ N)` premise in the live `⊒Λ` last-bind branch.

Limitation: this does not construct the body relation required by
`catchup-⊒Λ-single-bind-finish`.  The remaining obligation is now isolated as
the mixed target-first replay:

`⇑ᵗᵐ (renameᵗᵐ predᵗ W) ⊒ renameᵗᵐ (extᵗ suc) V′
  ∶ renameᶜ (extᵗ suc) p`.

The source-first relation from `last-bind-source-first-body` is still

`W ⊒ ⇑ᵗᵐ (...) ∶ ⇑ᶜ (...)`,

so source-side cast branches still need the mixed `raise0ᵗ`/`swap01ᵗ`
composition argument or a different value-level route.

## Attempt 100: reject a generic `raise0ᵗ` mode-renaming transport

Rejected as too broad.

A tempting way to prove the source-side cast replay is to reuse
`narrow-renameᵗ` with `raise0ᵗ` for the left component `t` and the source-side
composition result.  This would require a generic target mode environment `ν`
such that

`ModeRename raise0ᵗ μ ν`.

But `raise0ᵗ zero = suc zero` and `raise0ᵗ (suc zero) = suc zero`.  Therefore
`ν (suc zero)` would have to admit both `μ zero` and `μ (suc zero)`.
The mode lattice has no common top for `tag-or-id` and `seal-or-id`, so this is
impossible for arbitrary `μ`.

This matters because the hidden mode in

`Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B`

is existential inside `compose-rightⁿ`; the term-level source-cast constructor
does not expose a `tag-or-idᵈ`-only mode for `t`.

Conclusion: the mixed replay cannot be a plain renaming theorem over arbitrary
composition derivations.  It must either recover a mode restriction from the
legal `gen` body and occurrence invariant, or avoid renaming arbitrary `t`
components by using the value-level left-widening/left-narrowing route.

## Attempt 101: erase the lowered tail in the last-bind source body

Accepted as checked support in `proof.Catchup`.

In the live last-bind branch, the prefix before the final `bind` is all `keep`
and the target store for that prefix is empty.  Therefore the lowered source
tail `π₀` in

`Δ ⊢ π₀ ꞉ applyStores χs [] ⊒ˢ []`

must itself be `[]`.  I added `source-first-body-empty-tail` and
`last-bind-source-first-body-empty-tail` to turn the source-first body from
Attempt 99 into the exact two-entry store

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`.

This removes the remaining `combineStoreNrw π₀ ...` noise from the body replay
target.

Limitation: the body is still source-first.  The desired `⊒Λ` finisher needs
the target-first store

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)`

and source term `renameᵗᵐ raise0ᵗ W`.  Attempts 94-100 show why this cannot be
obtained by a generic mixed composition renaming theorem.  The next replay
target should be split-aware and should use the legal `gen` occurrence
invariant, or else rebuild the body through the existing split-marker
machinery.

## Attempt 102: lower source-first side conditions to the split premise store

Accepted as checked support in `proof.Catchup`.

After Attempt 101, the remaining source-first body has the exact store

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`.

I added the lowering/collapse bookkeeping for the split route:

`TyRenameWf-pred-lower`

`renameStoreNrw-pred-⇑ˢ⇑ˢ`

`source-first-pred-both-srcStore`

`source-first-pred-both-coercionᶜ`

The key fact is that renaming this source-first store by `predᵗ` has the same
source store as the single both-side entry used by the `split` premise:

`srcStoreⁿ (renameStoreNrw predᵗ ((⊒ zero ꞉=☆) ∷
  (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)))
  ≡ srcStoreⁿ ((zero ꞉ id ★) ∷ ⇑ˢ σ)`.

This gives a reusable way to transport ordinary `∶ᶜ` side conditions from the
source-first body down to the `(zero ꞉ id ★) ∷ ⇑ˢ σ` context that
`split`/`⊒Λ-body-add-split-marker` use internally.

Limitation: I intentionally did not generalize this to a term-imprecision
renaming theorem.  A generic term theorem would again need a non-injective
mode rename for hidden composition witnesses.  The next proof step must use
this side-condition transport only inside a split-aware replay, where the bad
source-cast composition branches are rebuilt through `split` or ruled out with
the legal `gen` occurrence invariant.

## Attempt 103: probe the legal-gen body replay and keep pred-collapse facts

Accepted as checked support in `proof.Catchup`; the larger replay theorem is
still open.

I temporarily stated the core no-earlier-bind body replay:

`W ⊒ ⇑ᵗᵐ V′ ∶ ⇑ᶜ p`

under the source-first store

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`

should imply

`⇑ᵗᵐ (renameᵗᵐ predᵗ W) ⊒ renameᵗᵐ (extᵗ suc) V′
  ∶ renameᶜ (extᵗ suc) p`

under the target-first store

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)`,

with the real `gen A p` premise in scope.

This is not refuted by the existing `TraceProbe` counterexample, because that
counterexample still fails the legal `gen` premise (`no-probe-gen-premise` /
`no-id-var1-fun-gen-target`).  However, the replay theorem is too large to add
as an unchecked hole: the difficult source-side cast cases still need to carry
the `cast-gen` occurrence invariant through the hidden composition mode, or be
rebuilt by a value-level left-narrowing/widening route.

I removed the temporary hole and kept the checked algebra that the replay will
need:

`renameStoreNrw-pred-source-first`

`renameCtxNrw-pred-⇑ᵍ⇑ᵍ`

`renameᵗᵐ-pred-⇑ᵗᵐ⇑ᵗᵐ`

The first records the exact full-store collapse:

`renameStoreNrw predᵗ ((⊒ zero ꞉=☆) ∷
  (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))
  ≡ (⊒ zero ꞉=☆) ∷ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ`.

The second and third remove the corresponding double-shift noise from term
contexts and terms.  They do not prove the replay, but they make the pred-lower
half of a future split-aware replay theorem explicit and reusable.

## Attempt 104: rule out the active type-application `RuntimeOK` source

Accepted as checked support in `proof.Catchup`.

The RuntimeOK merge gives the outer `catchup-lemma` branch an extra source
invariant.  I used the existing no-value-target theorem for runtime type
applications to split off the `ok-•` case:

`catchup-lemma (ok-• vV noV) (Λ vV′) (⊒Λ pᶜ N⊒V′)`.

In that case the recursive premise source is definitionally still a type
application after `⇑ᵗᵐ`, so `type-app-source-no-value-target` contradicts the
fact that the target is the value `V′`.  I also added the reusable bridge
`shifted-runtime-type-app-source-no-value-target`, which packages the same
argument for any source with `RuntimeTypeApp N`.

This explains why the old `TraceProbe` witness is not a counterexample to the
real `catchup-lemma`: it uses an active type application source, but such a
source cannot satisfy the real inner `⊒Λ` premise against a value target.

Limitation: this only removes the active bullet shape.  The general
`catchup-lemma okM (Λ vV′) (⊒Λ pᶜ N⊒V′)` clause still delegates to
`catchup-⊒Λ-catchup`, which still depends on the too-broad
`shifted-source-catchup-Λ-inversion` postulate for the remaining RuntimeOK
forms.

## Attempt 105: prove the all-keep `catchup-⊒Λ-catchup` branch

Accepted as checked support in `proof.Catchup`.

I threaded the original source-shape evidence from the real inner `⊒Λ` premise
into `catchup-⊒Λ-catchup`:

`value-target-source-safe vV′ N⊒V′ : CatchupSafe (⇑ᵗᵐ N)`.

That is enough to prove the `storeChangesLastBind χs = no-bind keeps` branch
without the false shifted-source inversion postulate.  The proof uses:

`pure-pred-↠-shifted-value keeps ⇑N↠W vW`

to turn the all-keep shifted reduction

`⇑ᵗᵐ N —↠[ χs ] W`

into the unshifted reduction

`N —↠[ χs ] renameᵗᵐ predᵗ W`,

and uses

`safe-allKeep-value-image (value-target-source-safe vV′ N⊒V′) (_ , refl)
  keeps ⇑N↠W vW`

to recover the equation

`W = ⇑ᵗᵐ (renameᵗᵐ predᵗ W)`.

The emitted store narrowing collapses with
`allKeep-empty-target-nil keeps Π≡ Π′≡ π⊒`, so the existing
`catchup-⊒Λ-no-bind-shift-image` finisher rebuilds the final `⊒Λ` result.

Limitation: the `last-bind` branch still falls back to
`shifted-source-catchup-Λ-inversion`.  The remaining work is exactly the
source-first to target-first replay from Attempts 101-103, or a way to show
that the live branch cannot have an earlier non-keep prefix before the final
source-only bind.

## Attempt 106: short-circuit value sources in the outer `⊒Λ` case

Accepted as checked support in `proof.Catchup`.

Before making the recursive call on the shifted source, the outer
`catchup-lemma` now checks `value? N`.  If `N` is already a value, the original
constructor

`⊒Λ pᶜ N⊒V′`

is already the desired final relation, so the proof returns `χs = []`,
`W = N`, `π = []`, and `↠-refl`.  The `No• N` witness comes from
`value-runtime-No• vN okM`.

This is not the missing inversion, but it removes a non-problematic source
shape from the recursive path.  The remaining non-value path is exactly where
`shifted-source-remainder` reduces the source to ν/cast histories and where the
last-bind replay problem still lives.

## Attempt 107: recheck the remaining last-bind replay after RuntimeOK

Inspection only; no Agda code kept.

After Attempts 104-106, the only live use of
`shifted-source-catchup-Λ-inversion` in `catchup-⊒Λ-catchup` is the
`storeChangesLastBind χs = last-bind χs₀ Aχ keeps keeps-ok` branch.

I rechecked the tempting replay route:

1. split the final bind with `↠-split-last-bind`;
2. use `last-bind-empty-target-star` to get `Aχ = ★`;
3. use `last-bind-source-first-body-empty-tail` to obtain the exact
   source-first body

   `(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`;

4. replay that body to the target-first store

   `(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)`.

The replay still wants `raise0ᵗ`, because the desired source term is

`⇑ᵗᵐ (renameᵗᵐ predᵗ W)`,

and `renameᵗᵐ-raise0-pred` gives exactly

`renameᵗᵐ raise0ᵗ W = ⇑ᵗᵐ (renameᵗᵐ predᵗ W)`.

The existing code has `source-target-raise0-coercionᶜ`, which is enough for
ordinary `∶ᶜ` side conditions over `srcStoreⁿ`, but there is no corresponding
`≈ⁿ`/composition transport for `raise0ᵗ`.  That absence is not accidental:
`raise0ᵗ` is non-injective and collapses the source-only variable, so generic
cast-composition replay repeats the failure from Attempts 94-100.

I also rechecked `last-bind-source-first-ν⊒`.  It can wrap a source-first body
back into a `ν⊒` relation at the prefix level, but it wraps the final caught-up
term `W`; it does not by itself produce a reachable source value for the
original `N`.  Using it directly would repeat the old base-history recursion
problem from Attempts 21-25.

Conclusion: the remaining branch still needs a split-aware replay that uses the
legal `gen A p` occurrence invariant to handle cast composition cases, or a
structural refactor that recurses on the ν/cast source-history witnesses
without hiding the recursive call from Agda's termination checker.

## Attempt 108: package the no-earlier-bind source-first residue

Accepted as checked support in `proof.Catchup`.

I added:

`catchup-⊒Λ-no-earlier-bind-source-first`

This helper handles the subcase where the prefix before the final `bind` is
also all `keep`.  From the live last-bind data it now packages two checked
facts:

1. the lowered source reduction

   `N —↠[ χs ++ bind ★ ∷ keeps ] renameᵗᵐ predᵗ W`;

2. the exact source-first body relation

   `suc (suc Δ) ∣
      (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
      ⊢ W ⊒ ⇑ᵗᵐ V′ ∶ ⇑ᶜ p`.

The proof combines existing pieces:

- `↠-split-last-bind`;
- `last-bind-empty-target-star`;
- `last-bind-pred-reduction`;
- `last-bind-empty-target-lowered-tail`;
- `last-bind-source-first-body-empty-tail`;
- all-keep normalization for the prefix.

This is useful because the remaining no-earlier-bind problem is now precisely a
single replay theorem from the source-first body above to the target-first body
needed by `catchup-⊒Λ-single-bind-finish`:

`suc (suc Δ) ∣
  (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
  ⊢ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)
    ⊒ renameᵗᵐ (extᵗ suc) V′
    ∶ renameᶜ (extᵗ suc) p`.

Limitation: this still does not prove the replay itself.  It deliberately
keeps the source-first body as the output so the remaining obligation cannot
silently re-expand into the false generic `raise0ᵗ`/composition transport.

## Attempt 109: package the no-earlier-bind final finisher

Accepted as checked support in `proof.Catchup`.

I added:

`catchup-⊒Λ-no-earlier-bind-catchup`

This wraps Attempt 108 with the existing `catchup-⊒Λ-single-bind-finish`.
Its only extra input is exactly the missing target-first replay body:

`suc (suc Δ) ∣
  (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
  ⊢ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)
    ⊒ renameᵗᵐ (extᵗ suc) V′
    ∶ renameᶜ (extᵗ suc) p`.

Given that replay body, the helper now constructs the full catchup existential
for the outer `⊒Λ` case, using Attempt 108 to get the lowered reduction and
then `catchup-⊒Λ-single-bind-finish` to normalize the lambda target and
`gen` coercion.

So the no-earlier-bind last-bind subcase is now factored into a single
remaining proof obligation: source-first body replay to the target-first body
above.  There is no remaining reduction or existential-packaging work in that
subcase.

## Attempt 110: test the legal `var0-fun` replay with the old `id-var1` cast

Rejected as a counterexample, with a checked endpoint obstruction in
`proof.TraceProbe`.

After Attempts 94-96, the most attractive remaining counterexample shape was:

1. keep the outer `gen (★ ⇒ ★) var0-fun` premise legal;
2. use a source-first body cast by `id (＇ 1) ↦ id (＇ 1)`;
3. hope the target-first replay would fail in the same way as the old illegal
   `probe-c` counterexample.

I added the checked lemma:

`no-id-var1-shifted-var0-compose`

which proves that even the source-first cast side condition cannot be formed:

`2 ∣ (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ [] ⊢
  r ≈ id-var1-fun ⨾ⁿ ⇑ᶜ var0-fun ∶ A ⊒ B → ⊥`.

The reason is simple but important: the left cast `id-var1-fun` targets
`＇ 1 ⇒ ＇ 1`, while the shifted legal body coercion `⇑ᶜ var0-fun` has source
`★ ⇒ ★`.  Composition would force `＇ 1 ⇒ ＇ 1 ≡ ★ ⇒ ★`.

Conclusion: the legal `var0-fun` repair of the old `id-var1` counterexample
does not produce a source-first body at all.  This supports the idea that the
real `gen` premise is enforcing the relevant endpoint freshness/occurrence
invariant.  The remaining replay proof still needs to exploit that invariant in
the cast-composition cases, rather than replaying a generic mixed
`raise0ᵗ`/`swap01ᵗ` composition theorem.

## Attempt 111: probe direct value replay and the split-shaped target

Rejected as a direct small proof; useful as a shape check.

After pulling `origin/main` again, Git reported that this branch was already up
to date with `origin/main`.  I then tried a temporary scratch lemma with the
exact remaining no-earlier-bind replay statement:

`W ⊒ ⇑ᵗᵐ V′ ∶ ⇑ᶜ p`

under

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`

should imply

`⇑ᵗᵐ (renameᵗᵐ predᵗ W) ⊒ renameᵗᵐ (extᵗ suc) V′
  ∶ renameᶜ (extᵗ suc) p`

under

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ)`.

The target store is exactly split-shaped, with `α = zero` and
`αᵢ = suc zero`.  That confirms the earlier split-marker intuition: the final
body should be obtainable by crossing the source-only star past the target-only
star and rebuilding a split-shaped target-first body.

However, direct structural recursion over the value-target relation is not a
small proof.  In Agda, even the first constructor probes require exposing the
hidden shapes of the defined indices `⇑ᶜ p` and `⇑ᵗᵐ V′`; otherwise Agda gets
stuck deciding whether constructors such as `ƛ⊒ƛ`, `κ⊒κ`, and cast rules can
apply.  Exposing those shapes just brings the proof back to the existing
split-aware replay problem: recursive `⊒Λ`/`⊒⟨ν⟩` branches can put a
`swap-right swap-here` exchange underneath a split marker, which is the unsafe
case already isolated by Attempts 74-78.

Conclusion: the value assumption removes many impossible top-level shapes, but
it does not eliminate the split-aware transport requirement.  The temporary
scratch file was deleted.  The next viable direct route is still a
split-aware source/target replay theorem that handles the unsafe split step
with real opening/catchup reasoning, not an arbitrary value-only structural
renaming theorem.

## Attempt 112: move the checked `gen` open-id exclusion out of the holey file

Accepted as checked support in `proof.TermNarrowingProperties`.

The new `main` branch contains useful lemmas near the top of
`proof.LeftSealNarrowingInversion`, but that file has
`--allow-unsolved-metas` for later unfinished inversion work.  Importing it
directly would be the wrong dependency for the catchup proof.

I ported only the completed exclusion prefix into the fully checked
`proof.TermNarrowingProperties` module:

`⇑ᵗ≢＇0`

`narrowing-open-id-var-endpoints⊥`

`gen-body-open-id-var⊥`

`gen-open-id-var⊥`

`gen-open-id-var∃⊥`

`castLike-gen-open-id-var⊥`

`narrowing-gen-open-id-var∃-eq⊥`

`termNarrowing-gen-open-id-var⊥`

The key reusable fact is:

`Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ gen A p →
 p [ β ]ᶜ ≡ id (＇ α) → ⊥`.

This is not the lambda replay proof, but it gives the remaining proof search a
checked way to use the real `cast-gen` occurrence premise without depending on
the unfinished left-seal inversion file.  It should be useful for ruling out
source-side cast branches that would force the legal `gen` body to open to an
identity variable.

## Attempt 113: add value evidence to the replay scratch goal

Rejected as a direct proof, but it sharpened the remaining obstruction.

I temporarily tested the exact no-earlier-bind replay statement with the extra
facts that the real caller knows:

`Value W`

`Value V′`

`No• W`

from

`suc (suc Δ) ∣
  (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
  ⊢ W ⊒ ⇑ᵗᵐ V′ ∶ ⇑ᶜ p`

to

`suc (suc Δ) ∣
  (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ (⇑ˢ σ) ∣ []
  ⊢ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)
    ⊒ renameᵗᵐ (extᵗ suc) V′
    ∶ renameᶜ (extᵗ suc) p`.

The goal is well-formed, but the value evidence does not collapse the proof to
simple constructor replay.  The surviving top-level shapes still include the
same hard cases:

- `split`;
- source-side casts, where composition needs mixed `raise0ᵗ`/`extᵗ suc`;
- target-side casts;
- recursive `⊒Λ` and `⊒⟨ν⟩` wrappers.

So carrying `Value V′` into `catchup-⊒Λ-catchup` may still be useful, but it is
not a standalone shortcut.  The temporary scratch module was deleted.

## Attempt 114: wrap the source-first body through `ν⊒`

Rejected as a postulate-trading route.

The source-first body has exactly the premise shape of `ν⊒`.  Instantiating
`ν⊒` with

`σ₀ = (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ`

would turn the source-first body

`suc (suc Δ) ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ₀ ∣ []
  ⊢ W ⊒ ⇑ᵗᵐ V′ ∶ ⇑ᶜ p`

into a relation under the target-only store

`suc Δ ∣ σ₀ ∣ [] ⊢ ν ★ W (⇑ᶜ p) ⊒ V′ ∶ p`.

This explains the operational intuition: the source-only binder in the replay
is the binder that a `ν ★ _` source would emit.  However, using this to finish
the body would require catching up that `ν` source to the lowered value.  The
available lemma for that is currently `catchup-ν⊒-catchup`, which is another
existing postulate.  Relying on it would remove the false
`shifted-source-catchup-Λ-inversion` call only by moving trust to a different
unfinished catchup case.

Conclusion: the `ν⊒` wrapping is useful explanatory structure, but it should
not be the final proof unless `catchup-ν⊒-catchup` is proved first or the proof
is refactored into a mutual recursion accepted by Agda.

## Attempt 115: use `⊒Λ-body-split-marker-catchup` as the last-bind shortcut

Rejected as insufficient.

`⊒Λ-body-split-marker-catchup` is tempting because it already invokes the
split-catchup machinery and returns a body under

`(zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ ⇑ˢ σ`.

But its source reduction conclusion is still rooted at the shifted source:

`⇑ᵗᵐ N —↠[ χs′ ] W′`.

The final `⊒Λ` catchup result needs a reduction from `N`, not from `⇑ᵗᵐ N`.
Thus the helper can add the split marker to a shifted-source catchup result, but
it does not solve the hard lowering step.  Applying it in the live last-bind
branch would simply recreate the need for a shifted-source inversion after the
split-marker work.

Conclusion: this helper is not an alternative to the false inversion postulate.
It may become useful after the shifted-source lowering is proved, but it cannot
replace that proof.

## Attempt 116: endpoint freshness by occurrence contraposition

Accepted as checked support, but not a complete replay proof.

Added two lemmas to `proof.NarrowWidenProperties`:

- `narrowing-target-fresh-source-fresh`;
- `widening-source-fresh-target-fresh`.

They are boolean contrapositives of the existing occurrence-preservation
lemmas in `NarrowWiden`.  The immediate motivation is the remaining `⊒Λ`
last-bind replay obligation: the target-only variable `suc zero` is absent
from the source store

`srcStoreⁿ ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ))`.

For source-side composition branches, if the right endpoint of the source-side
narrowing piece is known fresh for `suc zero`, the new lemma pushes that
freshness backward to the source endpoint.  This is a useful bridge toward
showing that the source term cannot depend on the target-only variable and may
therefore be replayed through the same store swap as the target/coercion side.

Limitation: this only gives type-endpoint freshness.  It does not yet prove
term-level freshness for `W`, nor does it convert the source renaming from
`raise0ᵗ` to `swap01ᵗ` in the live body relation.

## Attempt 117: legal `gen` source-endpoint freshness for source casts

Accepted as checked support, but still not a replay proof.

Added the following checked helpers:

- `occurs-one-⇑⇑-false`;
- `StoreNoOccurs-one-⟰ᵗ⟰ᵗ`;
- `srcStoreⁿ-source-first-one-fresh`;
- `gen-shifted-body-source-one-fresh`;
- `compose-right-gen-shift-left-source-fresh`.

The key fact is that if `p` is the body coercion of a legal

`gen A p : A ⊒ `∀ B`,

then the source endpoint of `⇑ᶜ p` is `⇑ᵗ (⇑ᵗ A)`, so it is fresh for the
target-only variable `suc zero`.  For a source-side cast branch

`r ≈ t ⨾ⁿ q`

whose result `r` is `⇑ᶜ p`, the new composition lemma propagates that
freshness to the source endpoint of `t`.  This rules out the old bad
`id-var1`-style left cast as a possible decomposition of a legal shifted
`gen` body.

Limitation: for narrowing, source-endpoint freshness does not imply
target-endpoint freshness.  A narrowing can introduce a store variable on the
target side, for example through a seal.  So this prunes the old counterexample
shape but does not yet prove that the whole source-side cast branch replays
through the `source-first` to `target-first` store exchange.

## Attempt 118: distinguish seal from untag with source-store no-key

Accepted as checked support, but still not the replay proof.

Added `StoreNoKey` support in `proof.NarrowWidenProperties`, including:

- `StoreNoKey-⟰ᵗ`;
- `StoreNoKey-zero-⟰ᵗ`;
- `StoreNoKey-one-⟰ᵗ⟰ᵗ`;
- `srcStoreⁿ-source-first-one-no-key`.

The point is sharper than occurrence freshness.  In the source-first body store

`(⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ ⇑ˢ (⇑ˢ σ)`,

the source store has no key for the target-only variable `suc zero`.  That
means a narrowing step cannot introduce target variable `suc zero` through a
`seal` case on the source side, since `seal` needs an actual source-store key.

Limitation: this does not eliminate `untag (＇ suc zero)`, which can introduce a
target ground variable without a store key.  Thus the no-key fact separates the
old seal-shaped obstruction from the remaining tag-shaped branch, but it still
does not supply the source-side replay through the swapped store.

## Attempt 119: exact no-key seal exclusions and the uniform-renaming detour

Accepted as small checked support, but not a complete replay proof.

I first considered factoring the replay through a uniform term-narrowing
renaming lemma:

`Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p`

to

`Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
  ⊢ renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ p`.

This is plausible for a fixed renaming such as `swap01ᵗ`, but the arbitrary
version is not a lightweight shortcut: the composition constructors expose
mode-indexed coercion derivations, so generic composition transport must carry
an explicit `ModeRename ρ μ ν` target mode environment.  The existing
`swap01ᵗ` transport works because `swap01ᵗ` is invertible and has a bespoke
mode map; a general lemma would be a real proof project, not bookkeeping.

Instead I added checked no-key exclusions for the syntactically exposed seal
cases:

- `narrowing-seal-no-key`;
- `narrowing-seq-seal-no-key`.

These close exact `seal A α` and `s ︔ seal A α` narrowing derivations whenever
`StoreNoKey α Σ` is available.  For the lambda replay, this supports the
current split of the source-side cast obstruction: source-side seal cases for
the target-only variable `suc zero` are impossible in the source-first source
store, while tag/untag cases still remain and must be replayed rather than
discarded.
