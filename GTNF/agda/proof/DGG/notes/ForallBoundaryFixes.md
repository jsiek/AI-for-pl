# Fixes for the open `∀⊑⟪+⟫` items (R3, R2)

> **Revised under design.md D25 (2026-10-03); see `D25.md`.**  The R3
> proposal `⊕⁺ˢ` below is withdrawn: under D25 the plain `⊕⁺` premise
> world is well formed (`post-premise-wf`), and under D23 `⊕⁺ˢ` can
> break agreement (`⊕⁺ˢ-breaks-agreement`).  L3d/R3d now goes through
> (`l3d-evolve`, `l3d-after`).  The Agda file has been updated to match;
> the R3 sections of this note describe the earlier, D13 state.  The
> R2 sections still hold, with `⊕⁺` in place of `⊕⁺ˢ`.

Status: 2026-10-03.  Agda: `ForallBoundaryFixes.agda` (this directory).
It checks with `agda --safe -v0` against the working tree at 0f83de9f
(D22: `∀⊑⟪+⟫` has `NonVar A` and `0 ∈ᵗ A`).  It has no holes and no
postulates.  It is not a Def module, and All.agda does not import it.
States are verbatim `scripts/render_gtnf.sh` output, and each state is
pinned to `evalTerms` by `refl` (`*-state`).

The file contains a local copy of the relation (§4) with the same
constructor names.  It differs from TermImprecision in two ways:
`∀⊑⟪+⟫` reads `W ⊕⁺ˢ m ^ β`, and there is one extra constructor,
`∀⊑⟪+⟫ᵃ` (candidate B of R2).

## Summary

| item | proposal | checked |
|---|---|---|
| R3 | `_⊕⁺ˢ_^_`: drop every pair whose right member is β (from ϱᵍ **and** ϱˡ), then add the lexical (0, β) | (a) `wf-⊕⁺ˢ` / `wf-premise`, in general; (b) all five existing derivations, verbatim; (c) the L3c/R3c pair after the left's TyBeta, with a well-formed premise world |
| R3, new | both copies instantiated on the left (L3d/R3d) | **open**: the second catch-up gives αᴿ a second left partner.  `⊕⁺ˢ` does not address this; D13 itself is in question |
| R2 | keep `∀⊑⟪+⟫` (candidate A), and add the child `SimBackInstX` (backward simulation inside the premise, left unmoved) | on L2c/R2c, the post-Merge pair derives with the **unchanged** rule (`r2c-post-A`).  Candidate B also derives it (`r2c-post-B`), and is admissible from A + `InstExpand` (`B-admissible`) |

## R3: the shadowing premise world

### Proposal

```agda
dropᴿ : RVar → RepRel → RepRel          -- drop the pairs (_, β)

_⊕⁺ˢ_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
world μ η η′ ϱᵍ ϱˡ ⊕⁺ˢ m ^ β =
  world (m ∷ μ) (keep (relabel suc η)) (keep η′)
        (dropᴿ β (shiftᴸ ϱᵍ)) ((zero , β) ∷ dropᴿ β (shiftᴸ ϱˡ))
```

The rule is the same, except that its premise world is
`W ⊕⁺ˢ m ^ β`.  The pairs are dropped from ϱˡ as well as ϱᵍ.  The
reason is that `∀⊑⟪+⟫` matches any single-`bind` right boundary, and
an enclosing `underν²` or `∀⊑⟪+⟫` can leave a lexical pair of β behind
(for example, inside a right `[−X^β]`).

### (a) The premise world is well formed

```agda
wf-⊕⁺ˢ : WfWorld W → names Δ′ ∌ʳ β → Δ′ ∋rep β := ★
  → WfWorld (W ⊕⁺ˢ m ^ β)

wf-premise : WfWorld W → Δ′ ∋rep β := ★
  → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
  → WfWorld (W ⊕⁺ˢ m ^ β)
```

Both hypotheses are premises of `∀⊑⟪+⟫`.  The freshness
`names Δ′ ∌ʳ β` is the `step-bind` premise inside the `BdyTy`
(`bdy-fresh`).  `wf-premise` fills SimBackProof's
`{! WfWorld (W ⊕⁺ m ^ β) !}` once the rule uses `⊕⁺ˢ`.  The proof
covers each field of `WfWorld`:

- **Joint.** The head is `both (inj₂ here⇔)`.  For the tail, every
  `both` entry of W has a right member that is named in Δ′.  By
  freshness that member is not β, so its pair survives the drop
  (`joint-⊕⁺ˢ`, `paired-⊕⁺ˢ`).
- **Agree.** The pair (0, β) is `abst-★`.  A surviving pair keeps its
  agreement (`agree-⊕⁺ˢ`).  In the `rep-rep` case this needs two
  renaming lemmas, proved in §2:
  - `same-pos`: the reading `_⊢_~_` along a renaming of name positions;
  - `⊑-ren`: type imprecision along a renaming that keeps every X⊑★
    mark.
- **D13 right-uniqueness.** By `paired-⊕⁺ˢ⁻`, every pair is either
  (0, β) or a surviving pair of W whose right member is not β.  Two
  pairs with the same right member are therefore both (0, β), or both
  come from W, where `wf-right-unique` applies.

### (b) The five existing derivations

Their premise worlds are all `W₃ ⊕⁺ m ^ 0` with `ϱᵍ = ϱˡ = []`, so
nothing is dropped.  `W₃-same : W₃ ⊕⁺ˢ m ^ 0 ≡ W₃ ⊕⁺ m ^ 0` holds by
`refl`.  p3-inst (= ch-x0), cg-x0, c2-x0 and c12-x0 are copied
verbatim into the local relation (§5) and check.  The only edit is
that p3-inst uses the Rebase file's `∀id⊑★ W₃`.  They reuse the
example worlds (`Wg⁻-int : Interior Wg⁺ …`, `W2⁻-int`, …) unchanged.

### (c) L3c/R3c at the left's TyBeta

```
L  (λf:∀X.X→X. (λy:ℕ. f) (f[ℕ] 5)) (ΛX.λx:X.x)
R  (λf:★→★.    (λy:★. f) (f 5))    (ΛX.λx:X.x)
```

Before the TyBeta, the left is in state 1 (`L3c₁`), the right in
state 3 (`R3c₃`), and the world is W₃:

```
  ((λx:ℕ. (ΛX. (λy:X. y))) ((ν Y:=ℕ. ((ΛZ. (λx:Z. x)) Y) ⟨−Y → +Y⟩) 5))
  ((λx:★. ([+X^α] (λy:X. y) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[]) (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[]))
```

After it, the left is in state 2 (`L3c₂`), against the same right:

```
⟶ (TyBeta, ⊣ α:=ℕ)
  ((λx:ℕ. (ΛY. (λy:Y. y))) (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5))
```

The following are checked:

- `l3c-pre : W₃ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ ∀id⊑★ W₃`.  Both copies go by
  `∀⊑⟪+⟫` (`copy2`, and `p3-inst` for the argument).
- `l3c-evolve : W₃ ⟿[ new ℕ ∷ [] ∣ [] ] W₁`, by `ev-L⇔`.  Also
  `W₁-wf`.
- `l3c-post : W₁ ∣ [] ⊢ L3c₂ ⊑ R3c₃ ∶ ∀id⊑★ W₁`.  Copy 1 goes by
  `⟪⟫⊑⟪⟫` through the global pair (αᴸ, αᴿ), which is ch-b1.  Copy 2
  goes by `∀⊑⟪+⟫` in W₁.
- `post-premise : W₁ ⊕⁺ˢ X⊑X ^ 0 ≡ world (X⊑X ∷ []) (keep []↪)
  (keep []↪) [] ((0 , 0) ∷ [])`.  The global (αᴸ+1, αᴿ) is dropped.
- `post-premise-wf : WfWorld (W₁ ⊕⁺ˢ X⊑X ^ 0)`, by `wf-premise`.
- `old-premise-¬wf : ¬ WfWorld (W₁ ⊕⁺ X⊑X ^ 0)`.  Under the old
  operation, αᴿ has the two left partners αᴸ+1 and 0.

So the Sim step at the left's TyBeta is related, with W′ = W₁, and
every world involved is well formed.

### The case where V mentions β's left partner

Say the left partner of β is αᴸ.  Inside the premise there are two
situations.

- **The right still names β.**  The right's continuing name for β
  (position 0) is joined with the left's lexical Y.  A left boundary
  `[+X^αᴸ]` inside N introduces a fresh left name.  Under `⊕⁺`,
  `join-fresh` would force that name to join β's right name as well.
  The embeddings are order-preserving and injective, so no `Interior`
  exists, and the derivation is impossible.  Under `⊕⁺ˢ` the pair is
  dropped, so the fresh name is left-only (at X⊑★).
- **The right rebinds β inside its own `[−X^β] … [+X^β]`.**  Then the
  fresh right name joins the left Y, never `[+X^αᴸ]`.

So **no formulation** lets the premise use (αᴸ, β) while β is named
inside.  `⊕⁺ˢ` makes the answer explicit and well formed.

**Why the case is not reachable (informal).**  The pair (αᴸ, β) is
created only by `ev-L⇔`, the left TyBeta that catches up with a copy
of this boundary.  The left value V of every ∀⊑⟪+⟫ pair on this
boundary was fixed before that allocation.  It is the value the right's
Inst was related to, or a Beta-copy of it.  V is a value, so it never
steps, and no term is ever substituted into a boundary interior
(TermSubst law 1).  Hence V cannot mention αᴸ.  If V mentions an
αᴸ′ whose partner is a different β′, nothing is dropped, because only
pairs with right member β are dropped.

### Remains

- To adopt the proposal: replace `_⊕⁺_^_` in ImprecisionWorld with
  `⊕⁺ˢ` (it can keep its name), and move §1–§3 into proof/.
- The non-reachability argument above is informal.
- **New issue, related to R3 (§7, L3d/R3d): both copies instantiated
  on the left.**

  ```
  L  (λf:∀X.X→X. (λy:ℕ. f[ℕ] 5) (f[ℕ] 5)) (ΛX.λx:X.x)
  R  (λf:★→★.    (λy:★. f 5)    (f 5))    (ΛX.λx:X.x)
  ```

  The left instantiates copy 1, which is consumed (Merge, Id).  Then it
  instantiates copy 2.  At copy 2's TyBeta the pair is P3's
  `(L1, R3′)` again, now in W₁ (`L3d₇-state`, `R3d₁₂-state`), and it
  derives (`l3d-before`):

  ```
    ((ν Y:=ℕ. ((ΛZ. (λx:Z. x)) Y) ⟨−Y → +Y⟩) 5)
  ⟶ (TyBeta, ⊣ β:=ℕ)
    (([+Y^β] (λx:Y. x) ⟨−Y → +Y⟩) 5)
  ```

  After that TyBeta (`L3d₈-state`), nothing works.  The right copy is
  still `[+X^αᴿ] …`, and αᴿ still has copy 1's left partner (pairs are
  never removed).  So:

  - `ev-L⇔` is unavailable (`no-second-catchup`);
  - `ev-L` leaves the new rep. var unpaired (`second-unpaired`), so
    `⟪⟫⊑⟪⟫` cannot join X with X′;
  - pairing it anyway breaks D13 (`second-paired-¬wf`).

  Each `ν` instantiation of the duplicated ∀ allocates its own left
  rep. var, while the right has a single β.  If two such left
  boundaries are alive at once, they genuinely need two left partners
  for β.  This is a question for D13, not for `⊕⁺ˢ`.  `⊕⁺ˢ` drops
  every pair of β, so it would survive relaxing D13 for ★-bound β with
  pairwise-disjoint scopes.  I have not checked such a relaxation.

## R2: SimBackFrame-∀⊑⟪+⟫

The IH on the premise `N ⊑ V′` (N = inst_X V) is SimBack, and SimBack
may answer with **any** left run.  The left value V cannot run, so
the frame child needs an answer in which the left does not move.

### The example: L2c/R2c at the right's Merge

```
L  (λh:∀X.X→X. h) ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
R  (λh:★→★. h)    ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
```

The left is in state 2 (`L2c₂`).  The right is in states 4 and 5
(`R2c₄`, `R2c₅`):

```
  ((λx:(∀X. X→X). x) ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨gen Y. (Y! → Y?ℓ0)⟩^[])

  ((λx:★→★. x) ([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩) ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[])
⟶ (Merge)
  ((λx:★→★. x) ([+Y^β] ([−Y^β, +X^α] (λx:X. x) ⟨−X → +X⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[])
```

`N = inst_Y(V2)` (`instV2 = inst-gen vBα`) is literally the right's
interior.  The left's Λ rep. var is at 0 where the right has β, and
αᴸ is at 1 where the right has αᴿ:

```
N  = ([−Y^0] ([+X^1] (λx:X. x) ⟨−X → +X⟩) ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩
N₀ = ([−Y^0, +X^1] (λx:X. x) ⟨−X → +X⟩)⟨Y! → Y?ℓ0⟩        (N's own Merge)
```

The world is `W4 = world [] []↪ []↪ ((0 , 1) ∷ []) []`.  It is reached
by ev-2 for the matched αᴸ/αᴿ, then ev-R for β.  The premise world is
`Pw = W4 ⊕⁺ˢ X⊑X ^ 0`, with ϱᵍ = {(1, 1)} and ϱˡ = {(0, 0)}.

Checked:

- `r2c-pre : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₄ ∶ ∀id⊑★ W4`.  Its premise `N⊑N`
  is `cast⊑cast`, then `⟪⟫⊑⟪⟫` for `[−Y] ∥ [−Y]` through the lexical
  pair, then `⟪⟫⊑⟪⟫` for `[+X] ∥ [+X]` through the global pair.
- **Candidate A** (rule unchanged, left unmoved): `r2c-post-A : W4 ∣
  [] ⊢ L2c₂ ⊑ R2c₅`.  Its premise `N⊑N₀` is `cast⊑cast`, then `⟪⟫⊑`
  for the left-only `[−Y]`, then `⟪⟫⊑⟪⟫` for `[+X^1] ∥ [−Y^β, +X^αᴿ]`.
  - The `⟪⟫⊑` makes Y right-only and keeps its X⊑X (`Pu′`,
    `right-only`).
  - The merged conversion is literally `revX`, because the outer
    conversion was the identity `Id(A)` of `inst-gen`.  So the
    conversion premise is `revX⊑revX`.
  - The world is unchanged: `W4-same : W4 ⟿[ [] ∣ none ∷ [] ] W4`.
- **Candidate B** (premise after an administrative run):
  `r2c-post-B : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₅`, by

  ```agda
  ∀⊑⟪+⟫ᵃ : … → InstX V N → (ρ : underΛ Δ ⊢ N -→* N₀) → Admin ρ
         → W ⊕⁺ˢ m ^ β ∣ [] ⊢ N₀ ⊑ V′ ∶ r → …
  ```

  The run is `N-merge = eval-sound 1 N-⊢`, with `Admin N-merge = tt`.
  The premise is `N₀⊑N₀`, which goes by `⟪⟫⊑⟪⟫` for `Θm ∥ Θm`.

So L2c/R2c does not separate the two candidates.  The left-expansion
that A needs holds here.

### The statements (§9)

```agda
-- the right's allocations inside the boundary commute with ⊕⁺ˢ (PROVED)
allocᴿ-⊕⁺ˢ : allocᴿ R′ (W ⊕⁺ˢ m ^ β) ≡ allocᴿ R′ W ⊕⁺ˢ m ^ suc β

-- candidate A's lemma: left-expansion along an administrative run
InstExpand = Value V → InstX V N → (ρ : underΛ Δ ⊢ N -→* N₂) → Admin ρ
  → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ N₂ ⊑ M′ ∶ r → Wᵢ ∣ [] ⊢ N ⊑ M′ ∶ r

-- B is admissible from A given InstExpand (PROVED)
B-admissible : InstExpand → (∀⊑⟪+⟫ᵃ's premises) → W ∣ γ ⊢ V ⊑ V′ ⟪…⟫ ∶ q

-- THE CHILD the frame needs (statement only): left UNMOVED
SimBackInstX = WfCtx Δ → WfCtx Δ′ → WfWorld W
  → NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ [] ⊢ V ⦂ `∀ A → InstX V N
  → Δ′ ∋rep β := ★ → W ⊕⁺ˢ m ^ β ∣ [] ⊢ N ⊑ M′ ∶ r
  → (st′ : reps Δ′ ∣ (β ∷ names Δ′) ⊢ M′ -→ M₁′ ∣ δ′)
  → ∃ M₂′, r″, W′. W ⟿[ [] ∣ allocs (st′ then r″) ] W′ × WfWorld W′
      × W′ ⊕⁺ˢ m ^ shiftβ (allocs (st′ then r″)) β ∣ [] ⊢ N ⊑ M₂′ ∶ r′
```

Given `SimBackInstX`, SimBackFrame-∀⊑⟪+⟫ re-applies `∀⊑⟪+⟫` to
`N ⊑ M₂′`.  That also needs the BdyTy of the shifted boundary
`↑ᴮ[δ′] (bind 0 β ∷ [])` at the new context.

### Comparison

- **Syntax-directedness.**
  - A keeps the rule syntax-directed.  The premise term `N` is fixed
    by V through `InstX`, and inversion gives back `N ⊑ V′`.
  - B is not syntax-directed.  `N₀` ranges over the administrative
    reducts of `inst_X V`, so one conclusion has derivations through
    different `N₀`, and inversion yields an existential run.
- **Which one the DGG proof can use.**
  - A can be used, through `SimBackInstX`.  That child is proved by
    induction on the premise derivation and always answers with the
    left unmoved.
    - A right Merge/Id on a redex that N shares is answered by an
      expansion-shaped derivation, as `N⊑N₀` is here.
    - A right Inst+TyBeta is answered by a nested `∀⊑⟪+⟫`, again
      without moving the left.
    - Right allocations are read back through `allocᴿ-⊕⁺ˢ`.
    - Blame is excluded by D22 (InstNoBlame, ForallBoundaryRisks.md).
  - B does not remove the obligation; it moves it.
    - The SimBack frame child can compose the IH's left run with ρ only
      if that run is administrative.  SimBack does not promise that: it
      may answer a right Inst with a left Inst+TyBeta, which allocates,
      and no `ρ` can hold such a run.  So B still needs a
      `SimBackInstX`-like strengthening.
    - Sim's left TyBeta on `ν T · V ⟨c⟩` against a `∀⊑⟪+⟫ᵃ` pair
      produces `inst_X(V)` against a premise about `N₀`.  That is
      `InstExpand`, unless Sim's left is allowed extra administrative
      steps, which changes SimDef/MultiSimDef.
    - With `InstExpand`, B adds no derivable pair (`B-admissible`).

**Recommendation:** keep `∀⊑⟪+⟫` as it is (A), and add `SimBackInstX`
as the child of SimBackFrame-∀⊑⟪+⟫.

### Remains

- `SimBackInstX` is a statement only.  The Merge case generalizes `N⊑N₀`.
  - That case needs the outer boundary of an inst_X image to be
    `inst-gen`'s single `[−X^0]` with an identity conversion.  Then
    the merged conversion relates to the left's inner one.
  - A general Merge expansion can fail.  A left `bind` in the outer
    boundary would create a fresh left name, and `join-fresh` would
    force it to join a right name that is already joined.
- `InstExpand` is stated only.  B needs it, and A needs it only in this
  restricted form.
- The SimBackFrame-∀⊑⟪+⟫ skeleton in M2ChildStatements/SimBackProof
  still uses `⊕⁺` and lacks D22's `NonVar`/`0 ∈ᵗ` arguments.  I left
  those files alone.
