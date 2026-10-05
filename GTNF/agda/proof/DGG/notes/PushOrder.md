# H1 made concrete: two right instantiations, and the fixes

Status: 2026-10-05.  Agda: `PushOrder.agda` (this directory).  From
`GTNF/agda` it checks with

```
agda --safe -v0 proof/DGG/notes/PushOrder.agda
```

It takes about 15 s once the base modules are cached.  It has no holes,
no postulates and no pragmas.  It is not a Def module, All.agda does
not import it, and no other file was edited.  LEFT is the more precise
side.

**Base.**  The real `ImprecisionWorld`, `ConversionImprecision` and
`TermImprecision` are being edited for D28.  So §0 of the file is a
verbatim snapshot of those three files at git 888407ff (charters
dropped).  §1 is HEAD's 15-rule relation, `Rel ClaimR PushR`, with
`Λ⊑`'s `Claim` and `⊑⟪⟫`'s `Push` turned into module parameters.
`Rel Claim Push` (`D27`) is HEAD's relation, rule for rule.  Every
term below is a `scripts/render_gtnf.sh` render.

## Verdict

| question | answer | Agda |
|---|---|---|
| a concrete H1 pair from related sources | **yes, H1′.**  The right instantiates `∀X.∀Y.X→Y→X` with two casts, `⇒ ∀Y.★→Y→★ ⇒ ★→★→★`.  Its final value is a nested pair of boundaries with a cast between them, so it never Merges | `Ex.*` |
| initial pair related | yes, at `∅ʷ` | `PosD27.init` |
| state 2 (after the first Inst, TyBeta) | related: P3's push and pop | `PosD27.st2` |
| **state 4 (the right's final value)** | **not related by D27, in any world over the final contexts with no pending name, at any index.**  So the DGG, part 1, fails for this pair | `NoD27.unrelated` |
| is it the push ORDER? | **no.**  The proof never reads the push relation.  It holds for every `PushR` | `NoRel` (generic in `PushR`) |
| (a) push order `new ++ π′` | **does not fix it** | `NoFixA.unrelated` |
| (b) the order stated at the pop (pop any pending name) | **does not fix it** | `NoFixB.unrelated` |
| (c1) any interleaving of carried and new (a stack is the case (a)) | **does not fix it** | `NoFixS.unrelated` |
| (c2) `claim-rep`: with nothing pending, a left binder may pair itself lexically with an unnamed right ★ rep. var; the boundary that later names it rejoins by `Interior.join-fresh` (D25) | **fixes it**, with HEAD's `Push` and index unchanged.  It even needs no push here | `FinalR.final`, `FinalR.final-no-push` |
| (c2) at HEAD's marks | **revives C4** (the right blames, the left reaches 5) | `C4Revived.c4-related`, `R₀c-blame`, `L₀c-5` |
| (c2) under D28 | C4 stays dead (the rejoined name's mark is derived, X⊑X unless permitted); H1′ derives (argued, §4) | — |
| corpus (K, P3, Cg X0, C2 X0) | unchanged under every fix.  (b), (c1), (c2) contain HEAD (`map⊑`).  (a) agrees with HEAD at every corpus push (each has nothing carried or nothing new, `toA`) | `ToS`, `ToB`, `ToR`, `toA` |
| D28 | H1′ breaks D28 too: the proof reads no mark.  D28 is what makes (c2) safe | argued, §4 |
| **recommendation** | **(c2) in the D28 world** | §5 |

Mechanized: everything in the Agda column.  Argued: the D28 transfer,
(c2)'s safety under D28, the corpus inspection behind `toA`, and the
statement impact.

## 1. The example H1′

### Sources

```
L:  (ΛX.ΛY.λx:X.λy:Y.x  : ∀X.∀Y.X→Y→X)
R:  ((ΛX.ΛY.λx:X.λy:Y.x : ∀Y.★→Y→★) : ★→★→★)
```

**The sources are related.**  The terms are the same, and the
ascriptions are related:

```
∀X.∀Y.X→Y→X  ⊑  ∀Y.★→Y→★      (Ex.src-1: ∀⊑ then ∀⊑∀)
∀Y.★→Y→★     ⊑  ★→★→★         (Ex.src-2: ∀⊑)
```

### Initial cast terms

An ascription at the term's own type inserts no cast.

```
L₀ = (ΛX. (ΛY. (λx:X. (λy:Y. x))))
R₀ = (ΛX. (ΛY. (λx:X. (λy:Y. x))))⟨inst Z. (∀X′. (Z?ℓ0 → (id(X′) → Z!)))⟩^[]⟨inst Y′. (id(★) → (Y′?ℓ0 → id(★)))⟩^[]
```

**The initial cast terms are related** at `∅ʷ`, at the index
`∀X.∀Y.X→Y→X ⊑ ★→★→★` (`PosD27.init`):

```
⊑cast (inst Y′. …)
  ⊑cast (inst Z. ∀X′. …)
    Λ⊑Λ, Λ⊑Λ, ƛ⊑ƛ, ƛ⊑ƛ, x⊑x
```

### Runs

The left is a value: its run (`showRun 30 Ex.L₀-⊢`) is the single state

```
  (ΛX. (ΛY. (λx:X. (λy:Y. x))))
```

The right's run (`showRun 30 Ex.R₀-⊢`):

```
  (ΛX. (ΛY. (λx:X. (λy:Y. x))))⟨inst Z. (∀X′. (Z?ℓ0 → (id(X′) → Z!)))⟩^[]⟨inst Y′. (id(★) → (Y′?ℓ0 → id(★)))⟩^[]
⟶ (Inst)
  (ν X:=★. ((ΛY. (ΛZ. (λx:Y. (λy:Z. x)))) X) ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨∀X′. (id(★) → (id(X′) → id(★)))⟩^[]⟨inst Y′. (id(★) → (Y′?ℓ0 → id(★)))⟩^[]
⟶ (TyBeta, ⊣ α:=★)
R₂ = ([+X^α] (ΛY. (λx:X. (λy:Y. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨∀Z. (id(★) → (id(Z) → id(★)))⟩^[]⟨inst X′. (id(★) → (X′?ℓ0 → id(★)))⟩^[]
⟶ (Inst)
  (ν Y:=★. (([+X^α] (ΛZ. (λx:X. (λy:Z. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨∀X′. (id(★) → (id(X′) → id(★)))⟩^[] Y) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
⟶ (TyBeta, ⊣ β:=★)
R₄ = ([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩)⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X] ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
```

The second Inst runs `InstX` through the `∀ᵖ` cast and into the
∀-boundary.  So the new boundary `+Y^β` lands OUTSIDE `+X^α`, with
the cast `⟨id(★) → (id(Y) → id(★))⟩` between them.  No Merge applies.
`R₄` is a value (`Ex.vR₄`) and the run stops there
(`Ex.R₄-final`).  `Ex.R₂-state` and `Ex.R₄-state` pin the states to
`evalTerms`.

### The state pairs

| left | right | D27 | Agda |
|---|---|---|---|
| L₀ | R₀ | related | `PosD27.init` |
| L₀ | state 1 (ν) | no rule: no rule relates a right ν to a left non-ν.  The same transient state occurs in P3 and K, and SimBack's right continuation `r″` steps past it | — |
| L₀ | R₂ | related: `+X^α` pushes X and the left's ΛX pops it (P3), then `Λ⊑Λ` for Y | `PosD27.st2` |
| L₀ | state 3 (ν) | as state 1 | — |
| **L₀** | **R₄** | **not related** | `NoD27.unrelated` |

**This is a DGG counterexample.**  DGG part 1, with `r` the empty run
of the left, needs some world `W` over `(empty, ΔT2)` with
`πʷ W ≡ []` that relates L₀ to a value of the right's run.  The
right's only value is R₄:

- `R₀-nv` and `R₂-nv` show that R₀ and R₂ are not values;
- states 1 and 3 are ν-terms, and `Value` has no ν case;
- the run is deterministic.

`NoD27.unrelated` quantifies over every such W (well formed or not)
and every index.

**Why the pair should be related.**  The left is the same term, kept
polymorphic.  The right only instantiated it at ★, twice, through
casts the left lacks.  The intended derivation pairs the left's X with
the right's X and the left's Y with the right's Y.  `FinalR.final`
is that derivation in fix (c2).

## 2. Why D27 cannot relate (L₀, R₄)

```
L₀ = ΛX. ΛY. λx:X. λy:Y. x
R₄ = [+Y^β] ( ([+X^α] (λx:X. λy:Y. x) ⟨…⟩) ⟨id(★) → id(Y) → id(★)⟩ ) ⟨…⟩ ⟨…⟩
```

The left's binders are peeled outer first (X, then Y).  The right's
boundaries are entered outer first (`+Y^β`, then `+X^α`).  The bodies
`λx:X ⊑ λx:X` need the left X JOINED with the right X (`ƛ⊑ƛ`'s domain
index is a variable against a variable, `var⊑var`).  There are two
cases.

**(i) The left's ΛX is peeled outside `+Y^β`.**  Nothing is pending
at the top, so the claim is fresh, and the binder's rep. var is
unpaired (`ClaimOK.unpaired0`).  The right's X is fresh in `+X^α`.
So it joins the left X only if their rep. vars are paired
(`join-fresh`), and they are not.  This case is the walk `rfL`, `byL`,
`ciL`, `bxL` (and the `N` variants after the left's ΛY), ending in
`nl-nl`.

**(ii) The left's ΛX is peeled inside `+Y^β`.**  Then `+Y^β`'s premise
relates all of L₀ to the interior, at the index

```
∀X.∀Y.X→Y→X  ⊑ᵂ⟨Wᵢ⟩  ★ → Y → ★
```

Inside `+Y^β` the right has one name, Y, so at most one name is
pending (`piY`: `PendingOK` and `wf-distinct` of the premise's
`WfWorld`).  The index is empty in both cases (`noIdx`):

```
πʷ = []  :  ∀X.∀Y′. X → Y′ → X  ⊑  ★ → Y → ★     needs  Y′ ⊑ Y
πʷ = [Y] :  ∀Y′. Y → Y′ → Y     ⊑  ★ → Y → ★     needs  Y′ ⊑ Y
```

Here `Y′` is the left's bound Y, and the right's Y is free, so no
mark can help.  This is `noKCI`, with `ltyK-CI` and `rty-KL` pinning
the two types.

Neither case reads the push relation.  So the theorem is
`NoRel ClaimR PushR ok` for **every** `PushR`, given only that the
claim relation `ClaimR` satisfies `ClaimOK`: a binder claimed with
nothing pending is unpaired, and a claim only renumbers older pairs
and joins.  HEAD's `Claim` and fix (b)'s `ClaimAny` satisfy it
(`claimOK`, `claimAnyOK`).

**Diagnosis.**  H1 is not about the push order.  At `+Y^β` the only
right name in scope is Y, and Y belongs to the left's SECOND binder.
The left's FIRST binder has nothing to be matched with until `+X^α`.
A pending list of right NAMES, in any order, makes the index at
`+Y^β` open the left's first binder at Y, or at nothing.

**The one-cast variant** (PushTypePremise's H1) is weaker.  The
right is `KL⟨inst X. inst Y. (X?→Y?→X!)⟩` (`showRun 30 Ex.R₀m-⊢`).
Its state 4 has the same nesting, but there the boundaries are
adjacent and the right Merges next:

```
⟶ (TyBeta, ⊣ β:=★)
  ([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
⟶ (Merge)
  ([+Y^β, +X^α] (λx:X. (λy:Y. x)) ⟨−X → (−Y → +X)⟩)⟨id(★) → (id(★) → id(★))⟩^[]
```

The merged boundary may push `[X, Y]` in either order, and the natural
order passes (PushTypePremise `H1.merged-natural`).  So that variant
only breaks a lemma (`PushInstR` must include the Merge).  H1′'s `∀ᵖ`
cast blocks the Merge, which is what makes it a DGG counterexample.

## 3. The fixes

| fix | definition (instance of `Rel`) | (L₀, R₄) | corpus pushes |
|---|---|---|---|
| (a) | `PushA`: `Push` with `new ++ π′` | not related, `NoFixA.unrelated` | same lists: each corpus push has `π′ = []` or `new = []` (`toA`) |
| (b) | `ClaimAny`: `claim-fresh`, or `open-any`, which pops `k` from any position `π₁ ++ k ∷ π₂` | not related, `NoFixB.unrelated` | contains HEAD (`ToB.map⊑`, the pop at `π₁ = []`) |
| (c1) | `PushS`: any `Shuffle π′ new πᵢ` | not related, `NoFixS.unrelated` | contains HEAD (`ToS.map⊑`, `shuffle-++`) |
| (c2) | `ClaimRep`: HEAD's `Claim`, plus `claim-rep` | **related**, `FinalR.final`, `final-no-push` | contains HEAD (`ToR.map⊑`) |
| (c3) | pending REP. VARS instead of names; the index opens an unnamed one left-only | argued: works | changes `πʷ`, `OpenImp`, `Carried`, `Push` |

The corpus column is argued from PushTypePremise §2's table.  P3,
Cg X0, C2 X0, C12 X0, L3c/L3d, R2c and K's `VL⊑RF` each push with
nothing pending.  K's `lk₁⊑rk₃` inner boundary only carries.  The
corpus derivations live in `examples/`, which is being edited, so they
are not re-imported.  The example's own state 2 carries over
mechanically (`st2-S`, `st2-B`, `st2-R`).

### (c2) `claim-rep`

```agda
claim-rep : ∀ {Ω ϱᵍ ϱˡ β} {ηᴸ : names Δ ↪ Ω} {ηᴿ : names Δ′ ↪ Ω}
  → let W = world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
    Δ′ ∋rep β := ★              -- a ★ rep. var
  → ¬ (names Δ′ ∋ᵅ β)           -- with no right name in scope
  → NoNamedPartner W β          -- and no named left partner
  → ClaimRep W (world (X⊑★ ∷ Ω) (keep (relabel suc ηᴸ)) (skip ηᴿ)
                  (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) [])
```

The claimed binder is `claim-fresh`'s left-only binder plus one
lexical pair `(0, β)`.  When a right boundary later names β (`+X^β`),
its fresh name joins the binder by `Interior.join-fresh`.  This is
D25's rejoin, already in the design.  `final` on H1′:

```
Λ⊑ claim-rep (X ↦ α)                      KL ⊑ R₄            ∀X.∀Y.X→Y→X ⊑ ★→★→★
  ⊑cast                                   ΛY… ⊑ R₄           ∀Y.X→Y→X ⊑ ★→★→★      (X⊑★)
    ⊑⟪⟫ +Y^β, push Y                      ΛY… ⊑ (…)⟨…⟩
      ⊑cast                               index opened at Y: X→Y→X ⊑ ★→Y→★
        ⊑⟪⟫ +X^α, carry Y, X REJOINS      ΛY… ⊑ λx:X.λy:Y.x
          Λ⊑ pop Y                        X→Y→X ⊑ X→Y→X
            ƛ⊑ƛ, ƛ⊑ƛ, x⊑x
```

`final-no-push` claims both binders at the top (X ↦ α, Y ↦ β).  Both
boundaries then use `push-none` and rejoin.  So in H1′ the pending
names are not needed at all.

**At HEAD's marks (c2) revives C4.**  The claimed binder is X⊑★, and
`Interior.mark-left` keeps that mark through the rejoin.  So the
right's `x⟨X!⟩` passes at `X ⊑ ★`.  C4's pair is the one of
PushTypePremise §3, with the left's initial program against the
right's state 2 (`C4Revived.R₂c-state`):

```
Λ⊑ claim-rep (X ↦ αᴿ)
  ⊑⟪⟫ +X^α, push-none, X rejoins at X⊑★
    ƛ⊑ƛ at X→X ⊑ X→★
      ⊑cast x⟨X!⟩ at X ⊑ ★
```

That is `C4Revived.c4-related`.  The right blames (`R₀c-blame`) and
the left reaches 5 (`L₀c-5`).  Under D27's marks, (c2) would need a
premise at the rejoin, like `PushTy`, that re-reads the boundary's
index with the rejoined names at X⊑X.

## 4. Interaction with D28 (PermissionsR)

- **H1′ breaks D28 as well (argued).**  The proof uses only these
  facts: `Claim`'s two cases, `Open1`'s pair `(0, β)`, `Interior`'s
  `same-ϱ` and `join-fresh`, `PendingOK`'s `Δ′ ∋ᵗ k := β`,
  `wf-distinct`, and type imprecision between variables (`X⊑X`
  without marks).  PermissionsR's relation has the same fields
  (`Claim`, `Open1`, `Interior.join-fresh`, `PendingOK`,
  `wf-distinct`).  Its extra premises (R1 on `⟪⟫⊑`, R2 on the ★
  conversion clauses) only remove derivations.  This matches
  PermissionsR §6 ("H1 untouched").
- **(c2) is safe under D28 (argued).**  Marks are derived
  (`marksʷ W = dmarks (ηᴿʷ W) (κʷ W)`):
  - Before the rejoin, the claimed binder is skipped by `ηᴿ`, so it
    is X⊑★, as `claim-fresh` makes it.
  - After the rejoin, its center is kept by `ηᴿ` with rep. var β, so
    its mark is `permit β κ`.  That is X⊑X unless β is permitted.
  - C4's `X ⊑ ★` step then has no X⊑★ to use: no right check of αᴿ
    grants it.  So C4 stays dead, for the same reason PermissionsR §6
    finds the push premise redundant.
  - In H1′ the claimed X is read at `X ⊑ ★` only BEFORE the rejoin
    (left-only, X⊑★).  After the rejoin it is read at `X ⊑ X`, which
    needs no mark.  So `final` goes through.
- **No new D28 condition.**  `claim-rep` leaves `κʷ` unchanged.  R1
  concerns left unbinds and R2 concerns the ★ conversion clauses;
  neither meets a claim.
- **Summary.**  D28 does not fix H1, and neither does any push order.
  D28 is what lets (c2) fix it without another premise.

## 5. Recommendation

**Adopt (c2), `claim-rep`, in the D28 world.**

- It is one new `Claim` constructor.  `Push`, `πʷ` and the index are
  unchanged, and every existing derivation stays (`ToR.map⊑`).
- H1′'s final pair derives (`final`, and `final-no-push`).
- C4 stays dead by D28's derived marks (argued, §4).  Under D27's marks
  it does not (`c4-related`).
- (a), (b) and (c1) are refuted by `NoFixA`, `NoFixB` and `NoFixS`.
  (c3) is the same idea at a higher cost: it changes the world field
  and the index.

**Statement impact (argued).**

- `PushInstR` for a SECOND Inst on a ∀-boundary value cannot keep the
  first Inst's push and pop.  It must turn the pop of `+X^α`'s name
  into `claim-rep α` above the new boundary.  α has no right name
  outside `+X^α`, so `claim-rep` applies.  This is a re-association
  lemma: a push of an Inst boundary's name followed by its pop equals
  `claim-rep` outside followed by `push-none` and the rejoin.
- SimBack's case for the right's Inst then has no Merge to wait for.

**Open question.**  With (c2), H1′ and P3 derive without any push.
Pushes might be removable altogether.  The cases to check are K's
`VL⊑RF` (a merged boundary) and C2 X0's `cc-gen` pop.

## 6. Names

- **Base**: §0 snapshot modules `IW`, `CI`, `TI`; the relation `Rel`;
  the instances `D27`, `FixA`, `FixS`, `FixB`, `FixR`.
- **Fixes**: `PushA`, `pushA`; `Shuffle`, `PushS`, `pushS`;
  `OpenAny`, `ClaimAny`; `ClaimRep`, `claim-old`, `claim-rep`.
- **Example**: `Ex.{K2, KY, src-1, src-2, KL, L1, NL, instX∀, instY,
  L₀, R₀, R₂, R₄, R₂-state, R₄-state, R₄-final, R₀-nv, R₂-nv, vR₄,
  R₀m, R₀m-steps}`, plus the typing bundles `Ex.{instX∀-ty, …, bX}`.
- **Positive**: `Pos.{init, st2}` (instances `PosD27`, `PosFixR`);
  `FinalR.{final, final-no-push, W₄-wf, intY, intX, wfY, wfX, …}`.
- **Negative**: `ClaimOK`, `claimOK`, `claimAnyOK`;
  `NoRel.{unrelated, topBY, noKCI, noIdx, piY, rty-KL, ltyK-CI,
  rfL, byL, ciL, bxL, bxN, nl-nl, l1-nl}`; the instances `NoD27`,
  `NoFixA`, `NoFixS`, `NoFixB`.
- **C4**: `C4Revived.{c4-related, R₂c-state, L₀c-5, R₀c-blame}`.
- **Carry-over**: `Map.map⊑`; `ToR`, `ToS`, `ToB`; `toA`;
  `st2-S`, `st2-B`, `st2-R`.
