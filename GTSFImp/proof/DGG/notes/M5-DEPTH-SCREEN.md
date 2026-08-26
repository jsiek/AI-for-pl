# M5 Depth Screen: nested one-sided `Λ` at an inst site

Investigation only.  This note records a cheap reachability screen in the
same style as the M3/QHUNT scratches: compile a small source suite, scan the
right target trace/prefix for generated `inst` casts, and inspect the source
imprecision derivation shape.

Checked scratch: `M5DepthScreenScratch.agda`.

## Syntactic characterization

The relevant source-side shape is a consecutive prefix of one-sided universal
imprecision clauses:

```agda
Λ⊑ᴳ (... Λ⊑ᴳ (... D ...))
```

Each `Λ⊑ᴳ` erases one precise/source `∀` binder against a target term that
does not bind that `∀`.  Thus depth at least two requires the source type to
bind two universals that the imprecise side lacks before any matching target
`Λ` appears.  A representative type shape is:

```text
∀X. ∀Y. ∀Z. X -> Y -> Z -> Z
  ⊑
∀Z. ★ -> ★ -> Z -> Z
```

The first two binders are erased by consecutive `Λ⊑ᴳ` clauses; the `Z`
binder is then matched by `Λ⊑Λᴳ`.

Compilation emits the target-side `inst` cast when a polymorphic value is used
where the expected type is not `∀`.  In the positive candidate below the
application expects:

```text
★³ = ★ -> ★ -> ★ -> ★
```

but the right operand has type:

```text
∀Z. ★ -> ★ -> Z -> Z
```

The source typing consistency is `★³ ∼ ∀Z. ★ -> ★ -> Z -> Z`; the compiler
wraps the right operand with `sym-screen`, which is an `inst` consistency cast.

By inspection of `CompilePreservesImprecision2.agda`, source `Λ⊑ᴳ` clauses are
compiled to target `Λ⊑²` clauses.  The screen does not build a per-step `⊢²`
derivation for the Eval trace; it uses that compile-preservation shape plus the
compiled target term/trace locator.

## Candidate Verdicts

### Candidate A. Catalog `left-only-inst-path`

Source pair from `ReachabilityCatalog.agda`:

```text
((ΛX. λx:X. x)[ℕ]) 5
  ⊑
(λx:★. x) 5
```

Verdict: derivable, but no depth-2 source stack and no right-side inst cast in
the checked trace.  Scratch gates:

```agda
left-only-inst-source-no-depth2 = refl
left-only-inst-right-no-inst-cast = refl
```

### Candidate B. Catalog `left-only-gen-path`

Source pair from `ReachabilityCatalog.agda`:

```text
((λf:(∀X. X -> X). f) (λx:★. x))[ℕ] 5
  ⊑
((λf:★ -> ★. f) (λx:★. x)) 5
```

Verdict: derivable, but no depth-2 source stack and no right-side inst cast in
the checked trace.  Scratch gates:

```agda
left-only-gen-source-no-depth2 = refl
left-only-gen-right-no-inst-cast = refl
```

### Candidate C. Nested `Λ`s under a matched `λ`

Source pair:

```text
λw:★. ΛX. ΛY. ΛZ. λx:X. λy:Y. λz:Z. z
  ⊑
λw:★. ΛZ. λu:★. λv:★. λz:Z. z
```

Verdict: derivable and the source derivation contains the desired consecutive
`Λ⊑ᴳ`/`Λ⊑ᴳ` stack, but the compiled right program is just a lambda value and
the prefix scanner reaches no inst cast.  Scratch gates:

```agda
under-lambda-source-nested-left-Λ = refl
under-lambda-right-no-inst-cast = refl
```

### Candidate D. Source-cast variant

Verdict: not a source candidate.  `GradualTerms.agda` explicitly has no source
cast syntax; casts are target constructs introduced by compilation.  The
source-valid proxy for this shape is Candidate E, where the compiled right
operand is directly under a generated `inst` cast.

### Candidate E. REACHED: nested erased binders at a compiled inst site

Definitions in `M5DepthScreenScratch.agda`:

```text
source-triple =
  ΛX. ΛY. ΛZ. λx:X. λy:Y. λz:Z. z

target-one =
  ΛZ. λu:★. λv:★. λz:Z. z

use-dyn =
  λf:(★ -> ★ -> ★ -> ★). f
```

Source pair:

```text
use-dyn source-triple
  ⊑
use-dyn target-one
```

The argument relation has the exact source prefix:

```text
Λ⊑ᴳ  -- erase X
  Λ⊑ᴳ  -- erase Y
    Λ⊑Λᴳ  -- match Z
```

The compiled right operand is:

```text
(Λ (λu:★. λv:★. λz:Z. z))
  ⟨ sym-screen ★³∼target-∀Z ⟩
```

and `sym-screen ★³∼target-∀Z` is an `inst` cast.  Since the cast input is a
closed `Λ` value, this is the target-side `β-inst` catch-up site.

Verdict: REACHED.  Scratch gates:

```agda
reached-source-nested-left-Λ = refl
reached-right-initial-inst-cast = refl
```

## Locator Sanity Check

`ReachabilityScreen.example12-entry` is retained as a target-only sanity check
for the inst-cast locator:

```agda
example12-right-inst-cast = refl
```

This is not counted as a source-pair candidate for the depth question.

## Overall Verdict

Yes: the compile image of gradual source programs can produce the depth-≥1
geometry in question, and the checked Candidate E reaches depth 2.  The
relevant site relates the source value under two consecutive one-sided
universal abstractions against the polymorphic target value that is being
instantiated.

Strongest caveat: this is still a screen, not a full reachability theorem.  The
positive result is strong because the inst cast is in the initial compiled
right operand and the source derivation shape is checked by Agda.  The exact
target `⊢²` stack at the catch-up site is inferred from the compile-preservation
clauses (`Λ⊑ᴳ` compiles to `Λ⊑²`), not reconstructed as a per-step target DGG
derivation in this scratch.

## Checks

Commands run with a repo-local Agda cache because the global stdlib interface
cache is not writable in this environment:

```sh
env AGDA_DIR=/home/runner/AI-for-pl/.agda-cache agda -l standard-library \
  -i GTSFImp -i GTSFImp/proof/DGG/notes -v0 \
  GTSFImp/proof/DGG/notes/M5DepthScreenScratch.agda

env AGDA_DIR=/home/runner/AI-for-pl/.agda-cache agda -l standard-library \
  -i GTSFImp -i GTSFImp/proof/DGG/notes -v0 \
  GTSFImp/proof/DGG/ReachabilityCatalog.agda

env AGDA_DIR=/home/runner/AI-for-pl/.agda-cache agda -l standard-library \
  -i GTSFImp -i GTSFImp/proof/DGG/notes -v0 \
  GTSFImp/proof/DGG/ReachabilityScreen.agda

env AGDA_DIR=/home/runner/AI-for-pl/.agda-cache agda -l standard-library \
  -i GTSFImp -i GTSFImp/proof/DGG/notes -v0 \
  GTSFImp/proof/DGG/CompileImageShape.agda
```
