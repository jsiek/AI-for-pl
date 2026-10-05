# Sided marks: a name's mark determined by its sidedness

Status: 2026-10-05.  Agda: `SidedMarks.agda` (this directory).  It
checks with `agda --safe -v0` from `GTNF/agda`, with no holes, no
postulates and no pragmas.  It is not a Def module, and All.agda does
not import it.  No other file was edited.  LEFT is the more precise
side.  Type imprecision `_⊢_⊑_` (Imprecision.agda) is unchanged.

The world layer, ConversionImprecision and TermImprecision are local
copies of git HEAD 46f04f4f, because the real files are being edited.
The copy is parameterized by a `Policy`:

- `d11` is HEAD's relation: `Interior` has its mark fields, and
  `WfWorld` checks `Joint`.
- `sided` is the proposal.

## Verdict

| question | answer | Agda |
|---|---|---|
| encoding | **marks derived from the embeddings.** `Sidedᵐ ηᴸ ηᴿ`: a name in the right image is X⊑X, a left-only name is X⊑★.  "X⊑★ iff no right preimage."  Required in `WfWorld` and in every conversion world.  `Interior`/`ConversionInterior` lose their mark fields. | `Sidedᵐ`, `right-mark`, `left-mark`, `sided` |
| the key fact | under sided marks, **`⊑cast` of a right name tag `X!`, name check `X?`, or an arrow containing one, is never derivable** | `clash`, `bad-cast` |
| P4 blocks 2, 3, 4 (= Cf B1, B2, B3) | **not derivable**, in any sided world | `p4-B2`, `p4-B3`, `p4-B4` |
| P4 simulation | **fails**: initial pair related, the left's Beta, TyBeta state is unrelated to **every** state the right can reach | `p4-init`, `p4-multisim-fails` |
| Cg (right-led X0 and B1) | **not derivable**; the multi-step backward simulation fails at the right's Inst, TyBeta | `cg-b0`, `cg-multisimback-fails` |
| C12 B1, C13 B1, C14 B1 (the gen layer) | **not derivable** | `c12-B1`, `c13-B1`, `c14-B1` |
| C12 simulation | **fails** at the left's TyBeta | `c12-b0`, `c12-multisim-fails` |
| C18b B1–B7 | not derivable (argued): same gen-wrapper `⊑cast` | — |
| C2 X0 (gen on both sides), C12 X0, Ch | derive (C2 X0 mechanized) | `C2.c2-x0` |
| K | **derives**: every opening pair, joined names at X⊑X | `K.lk₁⊑rk₃`, `K.lk₁⊑rk₄`, `K.VL⊑RF` |
| SimBackBlame cex `L₆ ⊑ R₇` | in `d11`: derivable **with no ★ conversion clause** (one-sided boundaries).  In `sided`: **not derivable** in any sided world | `Cex.InD11.L₆⊑R₇`, `Cex.cex-unrelated` |
| new cex hunt | none found.  Probe H1 (hide, rebind, escape): right blames, left gives 5, **unrelated** | `Cex.h1-unrelated` |
| pending openings | a popped binder joined to a right ★-bound name is X⊑X.  K is fine.  `PendingOK`'s X⊑★ contradicts sidedness, which breaks the pending derivation of C2 | §5 |
| proposal as stated | **cannot be adopted**: it removes the cex, but also every pair where a right-only `gen` wrapper meets a both-sided name (P4/Cf, Cg, C12–C14, C18b) | — |

What is mechanized and what is argued:

- *Mechanized*: everything in the verdict's Agda column.  The
  simulation failures quantify over **all** states the other side can
  reach (`in-trace`: by determinism, they are the states of the
  `evalTerms` run), and over every sided world.
- *Argued*: C18b, C2 B6/B7, C12 X0, Ch, the pending-openings
  consequences (§5), the lemma impact and the "hidden names" repair
  candidate (§6), and that no other counterexample exists under sided
  marks.

## 1. The encoding

```agda
data Sidedᵐ : η ↪ Ω → η′ ↪ Ω → Set where
  s[]     : Sidedᵐ []↪ []↪
  s-both  : Sidedᵐ ι ι′ → Sidedᵐ (keep {m = X⊑X} ι) (keep {m = X⊑X} ι′)
  s-left  : Sidedᵐ ι ι′ → Sidedᵐ (keep {m = X⊑★} ι) (skip {m = X⊑★} ι′)
  s-right : Sidedᵐ ι ι′ → Sidedᵐ (skip {m = X⊑X} ι) (keep {m = X⊑X} ι′)
  s-none  : Sidedᵐ ι ι′ → Sidedᵐ (skip {m = m} ι) (skip {m = m} ι′)
```

- Given the keep/skip pattern, exactly one mark list satisfies
  `Sidedᵐ`.  So μ is derived data:
  - `right-mark`: a right-image name is X⊑X;
  - `left-mark`: a name with no right preimage is X⊑★.
- The policy:

  ```agda
  sided = record { IMarks = ⊤ ; CMarks = ⊤
                 ; JointP = λ W → Joint (Paired W) ηᴸ ηᴿ × Sid W
                 ; CJointP = Sid }
  ```

- Every world a derivation reaches is sided:
  - the boundary rules and openings check `WfWorld`;
  - `⊕ X⊑X` and `⊕ᴸ` preserve sidedness (`sid-⊕ᴸ`);
  - `Λ⊑Λ` only ever uses `⊕ X⊑X`.
- The conversion premises check `Sid` of their conversion world.
- ConversionImprecision's ★ clauses need no edit.  They read
  `μ(X) = X⊑★` of a LEFT name, which under sidedness already means
  the name is left-only.  So `conv-unseal⊑id★`, `conv-seal⊑id★`,
  `conv-⨾seal⊑` and `conv-unseal⨾⊑` apply to left-only names only.
  They are still needed (C23a B3 compares a left-only `−X`/`+X` with
  `id(★)`).

## 2. The key lemma

`⊑cast`'s premise index and conclusion index share the left type:

```
p : A ⊑ B′        (B′ = source of the right cast)
q : A ⊑ A′        (A′ = its target)
```

A name tag `X! : X ⟹ ★` has `B′ = X` and `A′ = ★`; a name check
`X? : ★ ⟹ X` the reverse.

- `⊑var`: only a variable is below a variable.  So A is the variable.
- `var⊑★`: a variable below ★ is marked X⊑★.

The general form is `clash`: if B′ and A′ have ★ and the variable k
at the same position (`Clash k B′ A′`, through arrows), then
`μ ∋ k := X⊑★`.  A left ∀ goes through `∀⊑` on both sides, and the
clash moves under `instᵐ`.  k is a right-image name, so `right-mark`
refutes it:

```agda
bad-cast : Sid V → CastTy Δ′ μ′ c′ B′ A′ → BadCo c′
  → A ⊑ᵂ⟨ V ⟩ B′ → A ⊑ᵂ⟨ V ⟩ A′ → ⊥
```

`BadCo` is `X!`, `X?`, or `p ↦ q` with a bad side.  This covers every
gen wrapper `X! → X?`.

`no-rel` lifts this to whole terms:

```agda
no-rel : LftA M → RBad R → Sid V → ¬ (V ∣ γ ⊢ M ⊑ R ∶ q)
```

- `LftA` covers left λ, literals, applications (by their function),
  boundaries, Λ, ν, and good casts (`id(★)`, `ℕ!`, `ℕ?`).
- `RBad` covers right terms whose head path (through casts,
  boundaries and functions of applications) reaches a bad cast.
- Every path down ends at one of two refutations:
  - `⊑cast` of the bad cast, refuted by `bad-cast`;
  - `cast⊑cast` against a good left cast, refuted by `cc-bad`, because
    atomic types cannot clash.
- Openings keep `LftA` (`instx-lft`).

## 3. Example P4 (= cambridge Cf from its second block)

The right's run, rendered:

```
  ((λx:(∀X. X→X). ((ν X:=ℕ. (x X) ⟨−X → +X⟩) 5)) (λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[])
⟶ (Beta)
  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
⟶ (TyBeta, ⊣ α:=ℕ)
  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5)
⟶ (Wrap)
  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
⟶ (CastFun)
  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (Wrap)
⟶ (Beta)
  ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (Merge) ⟶ (IdDyn) ⟶ (Merge)
⟶ (TagUntag)
  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨+X⟩)
⟶ (Merge) ⟶ (Id)
  5
```

**Block 1 (initial pair): related.**  `p4-init`:

```
·⊑·
  ƛ⊑ƛ, ·⊑·, ν⊑ν (ν-bound rep. vars paired in the conversion world Wν), κ⊑κ
  ⊑cast (gen) at ∀X.X→X ⊑ ∀X.X→X
    Λ⊑ (Y left-only, X⊑★ — what sidedness gives)
      ƛ⊑ƛ at Y→Y ⊑ ★→★
```

**Blocks 2, 3, 4: not derivable.**

- `p4-B2`: left `([+X^α] (λx:X. x) ⟨−X → +X⟩) 5` against the right's
  TyBeta state.
  - The two `+X^α` name rep. vars paired by the matched TyBeta, so X is
    both-sided in every order of the boundary rules (`join-fresh`).
  - The right's `⟨X! → X?⟩` must go by `⊑cast` at `X→X ⊑ ★→★`, and X is
    X⊑X.
- `p4-B3`: left `[+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩`.
  - The right's outer `⟨X?⟩` needs `⊑cast` at `X ⊑ ★`.
  - The right's `X!` sits outside its `[−X^α]`, not inside it, so
    there is no left-only interval in which to read `X ⊑ ★`.
- `p4-B4`: left `[+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩`.
  - The outer `⟨X?⟩` blocks first.
  - Even below it, the right's rebind `+X^α` (the "delicate step")
    makes X both-sided again, at X⊑X, and the `⊑cast (X!)` needs X⊑★.
  - Entering the left's `[−X^α]` first leaves the index `ℕ ⊑ X`,
    which is empty.
- These are general facts (`no-rel`), not a failed search: every
  interleaving of `⟪⟫⊑⟪⟫`, `⟪⟫⊑`, `⊑⟪⟫`, `⊑cast` and the openings
  is covered.

**The pairs are wrongly unrelated.**  `p4-multisim-fails`:

```agda
(∅ʷ ∣ [] ⊢ L4 ⊑ R4 ∶ ι⊑ι base-ℕ)
× (empty ⊢ L4 -→* L1′)
× (∀ {R′} → empty ⊢ R4 -→* R′ → Unrel L1′ R′)
```

- `L1′ = ([+X^α] (λx:X. x) ⟨−X → +X⟩) 5` is the left's state after
  Beta, TyBeta.
- `Unrel L R` means that no sided world relates L to R.
- How the 13 right states are refuted:
  - states 2–9 by `no-rel`;
  - state 0 by `no-ƛapp`;
  - state 1 by `no-νapp`;
  - states 10–12 by `no-app-lit`.
- Both sides reach 5, so the DGG itself holds.  What fails is every
  simulation-based proof of it with this relation (Sim / MultiSim).
- Blocks 5 and 6 (`[−X^α]` against `[−X^α, +X^α, −X^α]`, then `5 ⊑ 5`)
  read no X⊑★ and derive (argued).

## 4. The corpus, K, and the counterexample

**The gen layer.**  Every block below relates a left name X (joined)
to the right's `[+X^β] ([−X^β] M ⟨…⟩)⟨X! → X?⟩ ⟨…⟩`.  It is
dead by `bad-cast`.

| block | right term (rendered) | verdict |
|---|---|---|
| Cg B1/X0 | `(([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])` | not derivable: `cg-multisimback-fails` (every left state, X0 = `cg-x0` and B1 included) |
| C12 B1 | `(([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩) 5)` | not derivable: `c12-B1`; simulation fails, `c12-multisim-fails` |
| C13 B1 | the same layer under `⟨id(★) → id(★)⟩`, then `5⟨ℕ!⟩` | not derivable: `c13-B1` |
| C14 B1 | two layers, the outer at `Z` | not derivable: `c14-B1` |
| C18b B1–B7 | `⟨gen Z. (X! → (Z! → X?))⟩`, then `⟨X! → (Y! → X?)⟩` at two both-sided names | not derivable (argued: the arrow clash covers B2–B7; B1's gen cast is the ∀ form of the same clash) |
| C2 B6/B7 | both sides tag (`cast⊑cast`), X⊑X | derive (argued: HEAD's derivation reads no X⊑★) |
| C2 X0 | both sides gen-wrapped, opening at X⊑X | **derives**: `C2.c2-x0` |
| C12 X0, Ch X0/B1 | opening at X⊑X, no right name tag | derive (argued: HEAD's derivations are at X⊑X) |

The pattern: a right-only `gen` (implicit generalization on the right
only) against a left Λ.  The right's wrapper is the only thing that
casts `★→★` up to `X→X`, and relating it needs `X ⊑ ★` at a name both
sides see.  This is what D11 and D15 were introduced for (§12.4 P4:
"a both-sided name at X⊑★").

**K.**  Every opening pair derives under sided marks (`lk₁⊑rk₃`,
`lk₁⊑rk₄`).  HEAD already chose X⊑X for both joined names: the opened
Y against `β:=★`, and the rejoined X.  The initial pairs `lk⊑rk` and
`lk₁⊑rk₁` use X⊑X only and carry over (argued).

**The SimBackBlame counterexample** (PendingOpenings §5d):

```
L₆ = ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[]⟨ℕ?ℓ0⟩^[]         ⟶* 5
R₇ = ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩^[]  ⟶ blame ℓ0
```

In HEAD's relation it has a second derivation, which compares no
`+X` conversion (`Cex.InD11.L₆⊑R₇`):

```
cast⊑cast (ℕ?)
  cast⊑ (id(★))
    ⟪⟫⊑ the left's +X^α: X left-only, X⊑★
      ⊑⟪⟫ the right's +X^α: X rejoins by (α, α), KEEPS X⊑★ (D15)
        ⊑cast (X!) at X ⊑ ★
          ⟪⟫⊑⟪⟫ the two −X^α (seal X ⊑ seal X), ⊑cast 5⟨ℕ!⟩
```

- So **restricting `conv-unseal⊑id★` to left-only names (the second
  repair candidate of PendingOpenings) does not remove the
  counterexample.**
- Sided marks remove it: after the rejoin X is X⊑X
  (`cex-unrelated`).
- `L₆-never-blames` and `R₇-blames` are re-proved here.

**The "J" pair.**  Under D11, P4's block 4 and this one-sided
derivation pass through the same inner pair, in the same world shape
(X left-only at X⊑★, one global pair):

```
[−X^α] V ⟨−X⟩   ⊑   [+X^α] (([−X^α] V ⟨−X⟩)⟨X!⟩) ⟨id(★)⟩
```

- P4 has `V = 5`, α:=ℕ; the counterexample has `V = 5⟨ℕ!⟩`, α:=★.
- In P4 the left-only interval comes from the right's `−X` of a
  both-sided name, and the escaped X-tag is re-checked by the right's
  `X?`.
- In the counterexample it comes from the left's fresh `+X`, and the
  tag escapes to `ℕ?`.
- So any compositional repair that keeps P4 and kills the
  counterexample must store this difference in the world.  See §6.

**Hunt (sided).**  `h1-unrelated` refutes the "hide, rebind, escape"
probe:

```
LH = ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨+X⟩)⟨ℕ?ℓ0⟩^[]                                   ⟶* 5
RH = ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩) ⟨id(★)⟩) ⟨id(★)⟩)⟨ℕ?ℓ0⟩^[]
   ⟶ (Merge) ⟶ (IdDyn) ⟶ (Merge) ⟶ (TagUntagBad-⟪⟫)  blame ℓ0
```

Other candidates, argued:

- A right blame comes from a right check that fails.
  - A right name check `X?` cannot be related by `⊑cast` (`bad-cast`).
  - A matched `X? ⊑ X?` checks on both sides.
  - A ground check `G?` forces the left type to be G (`⊑var`-like
    inversion: A ⊑ G and A ⊑ ★ give A = G).  The right value is then
    the G-tagged image of the left's.
- The only X⊑★ facts left are left-only names.  Through `⟪⟫⊑` they
  relate a left X-sealed value to the right's **payload** view
  (P5, C19, C23a), never to a right X-tagged value: a right tag needs
  a joined name, which is X⊑X.
- Probes H2 (left-only seal of `true⟨𝔹!⟩`, then `ℕ?`: both blame)
  and H3 (left `−X → +X` against right `id(★) → id(★)`, X left-only:
  both return `5⟨ℕ!⟩`) were checked by hand, not run: both sides
  agree.
- M26 `CastRedexNoBlame`: under sided marks its X-check case is
  vacuous (`bad-cast`); its ground case is the canonical-forms
  argument above.  The PendingOpenings counterexample does not touch
  M26 (its left is not a value).

## 5. Pending openings (D27) and marks after a pop

1. **D26 encoding (Open1).**
   - `Open1` does not change μ, so the right-only name must already be
     X⊑X (`W ⊕ʳ X⊑X ^ β`).  This is also what sidedness asks of a
     right-only name.
   - After the join it is both-sided, at X⊑X.
   - K's final pair derives so (`VL⊑RF`; the index is `Y→Y ⊑ Y→Y`, and
     no `Y ⊑ ★` is read).
   - X⊑X is the right mark there.  The left Y is abstract and the
     right Y is `β:=★`.  The name relation is between two sealed
     sides, and the payloads are compared by ϱ.  After the left's
     catch-up TyBeta, `(αᴸ, β)` is global, with `T ⊑ ★` by
     `RepImp.α⊑★`/`ι⊑★`.
   - `Y ⊑ ★` would be needed only if the right had already tagged or
     unsealed its Y-values: the gen wrapper, i.e. Cg (`Wg⁺ = W₃ ⊕⁺ X⊑★`,
     now dead).
2. **Pending encoding (PendingOpenings).**
   - `PendingOK` requires X⊑★ on the pending right-only name.
     `right-mark` contradicts that, so a pending name must be X⊑X.
   - Effect on K: none.  PendingOpenings' K derivation reads only the
     joins (`Y→Y ⊑ Y→Y`) and `∀⊑` (which uses `instᵐ`, not the world).
   - Effect on C2: PendingOpenings derives C2's X0 by `⊑cast` **before**
     the gen pop, reading `Y ⊑ ★` off the pending name's X⊑★.  With
     X⊑X that index is empty.  The two-sided `cast⊑cast` that the D26
     encoding uses (`C2.c2-x0`, mechanized here) is not allowed under
     a pending name.
   - So sidedness plus pending needs either `cast⊑cast` with a gen pop
     (a new claim form), or C2 is lost.
   - A popped binder joined to a ★-bound right name gets X⊑X in both
     encodings.
   - In the pending encoding, "while pending" is the one place where
     the left's ∀-bound variable reads a right name's mark, and
     sidedness fixes that mark at X⊑X.

## 6. Lemma impact (STATEMENTS-CORE, argued)

| statement | change |
|---|---|
| M1 MorSide, M2 MorImp (`WorldMor.mor-μ`: marks may rise) | marks are a function of the embeddings, which `mor-ηᴸ`/`mor-ηᴿ` keep, so `mor-μ` becomes an equality.  "Raised marks" (A27 MarkMono) leaves MorImp.  MorSide (b) loses the mark fields, and `Sid` of the image world follows from the kept embeddings. |
| M13 InstXImpL (second outcome `W ⊕ᴸ⇔ β`) | its MarkMono step is gone.  The opened (joined, X⊑X) name becomes left-only (X⊑★).  That is a change of side, not a morphism, and not monotone: right uses of the name lose their partner.  Needs a new side-change lemma, unproven. |
| M3 EvolveMor | unchanged (allocations move no name); `mor-μ` trivial. |
| M4 EvolveInterior, M6 InteriorMerge | simpler: no mark fields to compose; sidedness is `WfWorld` of the final world. |
| M5 WfWorld-bind | true only for `W ⊕ X⊑X` (statement: drop the free m); `W ⊕ᴸ` as before. |
| M7 MergeConvWorld | **at risk**.  A name left-only in the inner conversion world can become joined in the merged one, when the outer boundary binds its partner.  A `conv-unseal⊑id★` fact of the inner pair then does not transport. |
| M8 PayloadImp, D23 `RepImp.α⊑★` | unchanged.  The "X⊑★ name against ★ gives α⊑★" case now arises only for left-only names; `α⊑★` stays unconditional. |
| M22 SimBackBlame, M26 CastRedexNoBlame | the known counterexample is gone (`cex-unrelated`); no new one found (§4). |
| Sim, SimBack (and their multi-step forms; M16–M21 are their frames) | **false on P4, C12 (Sim) and Cg (SimBack)** under sided marks (§3, §4): single-step Sim composes to MultiSim, which is refuted.  The relation is too small. |

**Next candidate (unchecked): hidden names.**

- Keep D11's chosen mark at a matched fresh pair and at an opening.
  Cf B1 and Cg need this.
- Keep D15's kept mark only for a name the RIGHT hid with its own
  `−X` and then rebinds (P4/Cf B3, C12–C14, C18b).
- A name born left-only that a fresh right `+X` later joins gets
  X⊑X (sided).
- Restrict `conv-unseal⊑id★` to left-only names.
- Together these kill both derivations of `L₆ ⊑ R₇`:
  - the `⟪⟫⊑⟪⟫` one, by the conversion restriction;
  - the one-sided one, because its X is born left-only.
- The world needs a fifth `Joint` case, "hidden": left keep, right
  skip, mark kept, distinct from left-only.
- This is the J distinction of §4, stored in the world.
