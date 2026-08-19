Extra-cast dispatcher extractor obstruction after D15+D17
==========================================================

Date: 2026-08-19

Status: proposal note only.  No relation definition was changed.


D17 prerequisite audit
----------------------

The attempted direct use of D17's shape-only classifier does not inhabit
`OccupiedNonStarSourceSealResidual`.  That residual starts with:

```agda
prem : W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y S ∶ p₂
```

and asks for a source conceal while keeping that already concealed target:

```agda
W ∣ γ ⊢² V ↓ seal Xᴸ (＇ X₂) ⊑ U ↓ seal Y S ∶ q
```

Using `conceal⊑conceal² (matched-seal-nonstar nonstar-X)` would add a
second target conceal and therefore requires its premise target to be `U`,
not `U ↓ seal Y S`.  The source-only D17 name-protected classifier instead
requires a target tag outside the conceal, which is also absent here.  The
focused full legacy check reports the resulting mismatch as
`(＇ Y) != S` when the paired rule is attempted.

Therefore `RightInjInversion2Lemma.right-inj-inversion²` correctly remains
conditional on `OccupiedNonStarSourceSealResidual`; target projection still
cannot consume it as a total theorem.


The live residual surface is broader than an active target head
------------------------------------------------------------

The two fields in `StructuralExtraCastResiduals` consume a whole relation:

```agda
W ∣ γ ⊢² M ⊑ N ⟨ cᴿ ⟩ ∶ q
```

They do not require that the relation is headed by `⊑cast²` or
`cast⊑cast²`.  Consequently a legal input may still be headed by any
source-only wrapper whose target premise happens to be `N ⟨ cᴿ ⟩`.
In particular, `Λ⊑²` and `Λ⊑²-smart-comma` are possible heads.  Solving
either case requires precisely the strict-cells source-Λ replay wave that this
task explicitly leaves residual.  The extra-cast dispatcher receives neither
that residual nor a current-fuel value worker, so it cannot discharge those
heads independently.

The assembled value dispatcher calls the extra worker only after recursively
solving the child and explicitly rebuilding one of these exposed heads:

```agda
⊑cast² cᴿ child q
cast⊑cast² cᴸ cᴿ child q
```

That call-site invariant is not represented by the current
`StructuralExtraCastRightAt` type.


Exposed paired endpoint gap
---------------------------

Even after narrowing to the two exposed heads, the target-only case is the
only immediately complete route.  For injection, `to-ground` classifies the
identity tag versus the strict ground step and
`structural-ground-extra-cast-right-at` consumes the peeled `⊑cast²`
premise.  For projection, `canonical-★`, a supplied `RightInjInversion²`,
and the checked project-same/project-expand rows provide the corresponding
target-only route.  The inversion's occupied residual remains an additional
prerequisite for a concrete factory.

The general paired injection head instead supplies:

```agda
cast⊑cast² cᴸ (_! cᴿ) prem q★

prem : C ⊑ B
cᴸ   : C ∼ A
cᴿ   : B ∼ G
q★   : A ⊑ ★
```

The checked stuttering row requires the re-attachment endpoint `A ⊑ G`.
That endpoint is not a constructor field.  The paired projection head has the
dual problem: its checked tag replacement needs a supplied `C ⊑ G`; the
constructor gives `C ⊑ ★` and the post-source endpoint `A ⊑ B`.
`RightInjInversion²` removes a matching tag only after the caller supplies the
ground endpoint, so supplying its occupied premise would not manufacture
either witness.

The premise-first midpoint repair is not available: the repository's checked
`LG3EndpointTransportCounterexampleScratch.agda` inhabits the paired
function/expand cell while refuting that midpoint.  The live row combinators
therefore correctly use stuttering re-attachment, but their factory still
needs an endpoint-producing extractor.


Proposed surface decision
-------------------------

Represent the actual call-site invariant by splitting
`StructuralExtraCastRightAt` into exposed target-only and exposed paired
entries, with the paired entry carrying the appropriate re-attachment
endpoint/core package.  The value dispatcher already has exactly these two
heads after child catch-up and can supply the package when a future approved
paired endpoint inversion exists.  Source wrappers, especially source Λ,
should remain the value dispatcher's responsibility rather than being hidden
inside the extra-cast factory.

Alternatively, approve a new whole-relation, wrapper-aware active-cast
extractor.  Such a theorem necessarily includes the deferred source-Λ wave
and a new paired endpoint inversion, so it is larger than the decided LG-3
tag machinery.

Without one of those decisions, changing the residual fields or introducing
the endpoint extractor would be a genuinely new major lemma/surface.  The
target injection and target projection residuals therefore remain live in
this pass.
