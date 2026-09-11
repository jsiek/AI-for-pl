# Contextual backward simulation and source catch-up

## Scope

This packet covers only the backward half of the contextual migration.  It
does not change CTI, `SimBackᵀ`, or `CatchupToLessPrecise`.  The concrete local
allocation geometry is checked by
`notes/probes/SimBackContextualCatchupProbe.agda`.

The current broad transport is unsound for an evolution containing
`evolution-bind-left-aligned`.  The backward callers cannot be narrowed to
target-only evolution: both `CatchupToLessPrecise` and recursive `sim-back`
return arbitrary source evolution.  The repair therefore has to keep the
whole CTI evaluation context during the induction.

## Strict source `β-inst` pin

`SimBackContextualCatchupProbe.agda` places the explicit `β-inst` reduction
from `TrustedLambdaCatchupProbe.target-inst-step` on the source endpoint:

```agda
TLC.target-inst-redex —→[ bind ★ ] TLC.target-after-inst
```

The target endpoint has already allocated a dynamic cell.  The same checked
theorem pairs that reduction with:

```agda
MultiWorldEvolution
  {W = source-β-inst-start-world}
  {W′ = source-β-inst-aligned-world}
  (bind ★ ∷ []) []
```

The world step is `evolution-bind-left-aligned`.  Its boundary is justified by
the two structural reveals `〖 zero , ★ ↑ target-body 〗`; the new source pivot
and the existing target pivot both represent `★`.  The rebase role is
`alignment-onlyᶜ`, and the probe checks
`openFramesᶜ source-β-inst-start-world ≡ []` and
`openFramesᶜ source-β-inst-aligned-world ≡ []`.

This is the local path that invalidates any backward design which catches up a
focus and then transports an unrelated outer sibling through the returned
world evolution.

## The fifteen unsafe backward transports

The inventory below is exhaustive for the current backward stack.  Line
numbers name the present branch; the semantic branch description is the stable
identifier.

| Module and line | Evolution provenance | Relation transported | Contextual replacement |
| --- | --- | --- | --- |
| `SimBackProof.agda:122` | function catch-up in application right-blame | argument | catch up the function under application-left; keep the rebuilt application root for argument blame catch-up |
| `SimBackProof.agda:181` | recursive simulation of application-left target step | dormant argument | recursive contextual `SimBack` returns the rebuilt application relation directly |
| `SimBackProof.agda:210` | function catch-up before application-right target step | argument | shift the returned application path from the now-ready function to the argument, then recurse contextually |
| `SimBackProof.agda:240` | recursive simulation of the application argument | ready function | recursive contextual `SimBack` returns the rebuilt application relation directly |
| `SimBackProof.agda:1184` | left-operand catch-up in primitive right-blame | right operand | catch up under primitive-left and retain the rebuilt primitive root |
| `SimBackProof.agda:1248` | recursive simulation of primitive-left target step | dormant right operand | recursive contextual `SimBack` returns the rebuilt primitive relation directly |
| `SimBackProof.agda:1315` | left-operand catch-up before primitive-right target step | right operand | shift the returned primitive path to the right operand, then recurse contextually |
| `SimBackProof.agda:1343` | recursive simulation of the primitive right operand | ready left operand | recursive contextual `SimBack` returns the rebuilt primitive relation directly |
| `SimBackPairedFunClosingProof.agda:97` | function catch-up | application argument | the first contextual catch-up returns the whole application relation and a path to its argument |
| `SimBackPairedFunClosingProof.agda:135` | subsequent argument catch-up | ready function | the second contextual catch-up returns the whole application relation used by value closing |
| `SimBackPairedFunValuesProof.agda:459` | casted argument catch-up | source function body under `cast⊑²` | catch up in the post-`β-⇒` term, through result cast then application-right |
| `SimBackPairedFunValuesProof.agda:627` | concealed argument catch-up | source function body under `reveal⊑-identity` | catch up in the post-`β-reveal-⇒` term, through result reveal then application-right |
| `SimBackPairedFunValuesProof.agda:810` | concealed argument catch-up | source function body under `reveal⊑-only²` | same contextual post-beta path, retaining the one-sided reveal evidence in the root CTI |
| `SimBackPairedFunValuesProof.agda:999` | revealed argument catch-up | source function body under `conceal⊑-identity` | catch up in the post-`β-conceal-⇒` term, through result conceal then application-right |
| `SimBackPairedFunValuesProof.agda:1182` | revealed argument catch-up | source function body under `conceal⊑-only²` | same contextual post-beta path, retaining the one-sided conceal evidence in the root CTI |

The five `SimBackPairedFunValuesProof` calls are decisive.  They occur after a
source function root step has exposed an administrative application under a
result cast/reveal/conceal.  They are not recursive calls to the public
`SimBackᵀ`, so a contextual `SimBack` worker alone cannot remove their sibling
transport without absorbing the whole value-closing proof.

## Decision: contextual catch-up is a separate theorem

The smallest reusable boundary is a separate
`ContextualCatchupToLessPreciseᵀ`, used by the contextual `SimBack` worker and
by paired-function closing/value proofs.  Folding catch-up into `SimBack` would
either leave the five value-level transports untouched or duplicate their
cast/reveal/conceal induction inside `SimBack`.

The contextual catch-up proof cannot be an adapter around the current
`LeftValueCatchupAt`.  Such an adapter would first obtain a focused source
evolution and would then need the same false sibling transport to rebuild the
outer relation.  Instead, the existing lower catch-up lemmas should be reused
branch by branch inside an induction that retains the root-to-focus path.

## Shared zipper surface

The nineteen `_↘ᶜ_` edges in
`SimTargetRevealRebaseContextDef.agda` already cover the required syntax:
application left/right, primitive left/right, the two type-application forms,
three cast forms, four identity conversions, two source-only conversions, two
paired conversions, and target reveal/conceal rebase.

After the forward contextual work stabilizes, move the neutral pieces into one
canonical `CastTermImprecisionContextDef.agda` rather than creating a backward
copy:

- `RelatedConfiguration`, `world`, `sourceTerm`, and `targetTerm`;
- `_↘ᶜ_`, `_↘ᶜ*_`, `focus-here`, `focus-there`, and `extend-focus`;
- the current source-frame and `RebuildSource` definitions;
- a direct dual `TargetFrame` and `RebuildTarget` for lifting a focused target
  step to the root;
- `TargetPathEvolution`, which the forward proof already uses;
- a direct dual `SourcePathEvolution` whose edge evidence preserves the target
  frame while the source endpoint and source readiness evolve.

`SourcePathEvolution` is not a wrapper around an unfinished obligation.  It is
the exact correspondence needed to move from an application/primitive left
focus to the right focus after source catch-up, and to retain the result
conversion/application path in the five paired-function value cases.

No separate world-frame stack is needed.  The nested world remains in the CTI
node that owns each reveal/conceal rebase.

## Direct contextual catch-up interface

The production Def should state the following structure directly.  The code
below uses the shared zipper projections named above; all existential result
components remain inline.

```agda
ContextualCatchupToLessPreciseᵀ : Set₁
ContextualCatchupToLessPreciseᵀ = ∀
    {Δᴸ Δᴿ : TyCtx} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {root focus : RelatedConfiguration
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩}
  → openFramesᶜ (world root) ≡ []
  → (path : root ↘ᶜ* focus)
  → Value (targetTerm focus)
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ root′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ focus′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ path′ ∈ root′ ↘ᶜ* focus′ ]
        (sourceTerm root —↠[ χsᴸ ] sourceTerm root′)
        × Value (sourceTerm focus′)
        × targetTerm root′ ≡ targetTerm root
        × targetTerm focus′ ≡ targetTerm focus
        × SourcePathEvolution path path′
        × MultiWorldEvolution
            {W = world root} {W′ = world root′} χsᴸ [])
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (sourceTerm root —↠[ χsᴸ ] blame)
        × MultiWorldEvolution
            {W = world root} {W′ = γ′} χsᴸ [])
```

Only the root world requires `openFramesᶜ ... ≡ []`.  Requiring it at the
focus would reject precisely the nested reveal/rebase contexts the zipper is
meant to preserve.

The existing public `CatchupToLessPrecise` is recovered with `root = focus`,
`path = focus-here`, followed by pattern matching on `root′`.  That adapter is
the final migration step, not part of the initial Def introduction.

## Direct contextual `SimBack` worker

The worker takes a focused target step and an explicit `RebuildTarget` witness
for the whole target reduct.  Its success branch returns the rebuilt root CTI,
so a recursive caller never transports a sibling relation:

```agda
ContextualSimBackᵀ : Set₁
ContextualSimBackᵀ = ∀
    {Δᴸ Δᴿ Δᴿ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {root focus : RelatedConfiguration
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
    {P′ : Term Δᴿ′} {N′ : Term Δᴿ′}
  → openFramesᶜ (world root) ≡ []
  → (path : root ↘ᶜ* focus)
  → targetTerm focus —→[ χᴿ ] P′
  → RebuildTarget path χᴿ P′ N′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ root′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩
        ⟨ Δᴿ′ , applyStore χᴿ Σᴿ , [] ⟩ ]
        (sourceTerm root —↠[ χsᴸ ] sourceTerm root′)
        × targetTerm root′ ≡ N′
        × MultiWorldEvolution
            {W = world root} {W′ = world root′}
            χsᴸ (χᴿ ∷ []))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        sourceTerm root —↠[ χsᴸ ] blame)
```

The public `SimBackᵀ` is the `focus-here`/identity-`RebuildTarget` adapter.
The application-right and primitive-right branches first invoke contextual
catch-up on the left edge, use its returned `SourcePathEvolution` to construct
the now-ready right edge, and recurse with that right focus.

## Dependency and migration order

1. Finish the forward owner's current zipper work.  Extract the neutral zipper
   and rebuild definitions into `CastTermImprecisionContextDef.agda`; migrate
   the forward imports in the same closed-world change.
2. Add the dual target rebuild and source path-evolution definitions.  Strictly
   probe application left-to-right focus shifting, primitive left-to-right
   focus shifting, and a result-conversion/application-right path.
3. Add `ContextualCatchupToLessPreciseDef.agda`.  Implement its proof by
   generalizing the live left-value catch-up induction, retaining the root and
   path at every recursive call.  Reuse the existing lower catch-up interfaces;
   do not call broad `transport-CTI` after the focused result returns.
4. Migrate the five `SimBackPairedFunValuesProof` calls first.  They exercise
   cast, identity conversion, one-sided conversion, post-beta application, and
   aligned source evolution independently of the main simulation worker.
5. Migrate the two `SimBackPairedFunClosingProof` calls.  The first catch-up
   returns a whole application plus a right-focus path; the second returns the
   whole value-ready application.
6. Add `ContextualSimBackDef.agda` and its parameterized Proof, depending on
   `ContextualCatchupToLessPreciseᵀ` and the existing root-closing Defs.
   Replace the eight application/primitive transports in `SimBackProof` with
   contextual recursion.
7. Instantiate `SimBackᵀ` with the `focus-here` adapter.  Instantiate the
   unchanged `CatchupToLessPrecise` similarly.  Only after all fifteen sites
   are gone should `TransportTermImprecisionᵀ` be removed from the backward
   module parameters.

At no stage is an aligned source evolution narrowed away.  The context owns
the sibling, and the contextual theorem reconstructs the whole relation.
