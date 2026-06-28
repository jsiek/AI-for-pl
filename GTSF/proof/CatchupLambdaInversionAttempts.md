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
