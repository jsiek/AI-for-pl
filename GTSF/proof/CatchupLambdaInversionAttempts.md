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
