# Hidden names: a world records how a name became one-sided

Status: 2026-10-05.  Agda: `HiddenNames.agda` (this directory).  It
checks with `agda --safe -v0 proof/DGG/notes/HiddenNames.agda` from
`GTNF/agda`, with no holes, no postulates and no pragmas.  It is not a
Def module, and All.agda does not import it.  No other file was
edited.  LEFT is the more precise side.  `_⊢_⊑_` is unchanged.

**Base.**  The local copy is git HEAD ce2da4b6+ (D27: `πʷ` is a field
of `World`), not the pre-D27 copies of SidedMarks/ModeCondition.  The
reason: HEAD's three example files (P1/P2/P3/P6; C12–C14, Cg, C2, Ch;
K) port almost verbatim.  Only the `Interior` records need two new
fields, and the worlds that a right `−X` produces need `hide`.
ModeCondition's P4 blocks port with three edits: `push-none`,
`claim-fresh`, and an extra `[]` for `πʷ`.  The side-premise bundles
and the pending-name side relations are world-free, so they are
imported from HEAD's TermImprecision.

## Verdict

| question | answer | Agda |
|---|---|---|
| encoding | a fourth embedding constructor `hide`; statuses `joined/plain/hidden` read off the embeddings; `markStep`; `LeftOnly` on the four ★ clauses (§1) | `_↪_.hide`, `statusAt`, `markStep`, `StOK`, `NotHid`, `LeftOnly` |
| must the rule be symmetric? | **yes**.  HEAD relates C1 by a right-first route.  The right's `+X` is born right-only at a chosen X⊑★, then the left's `+X` rejoins it and `mark-right` keeps X⊑★.  This route uses no ★ clause and no left-only rejoin, so the asymmetric repair keeps it. | `C1.InHEAD.L₆⊑R₇`, `C1.right-first-rejected` |
| P4, all blocks (incl. B4's J pair) | **derive** | `P4.p4-B1`, `p4-B1′`, `p4-B2` … `p4-B6`, `P4.S⊑J` |
| Cg X0/B0, C12 B0/X0/B1, C13 B1, C14 B1, C2 B0/X0/B6/B7, Ch B0/X0/B1, P1/P2/P3/P6 | **derive** (HEAD's derivations, ported) | `Rebase.*`, `TIE.*` |
| Cg B1 | **derives** (new; not mechanized under D11 before) | `CgB1.cg-b1` |
| C18b | B7 (the two-name hide/rejoin block) **derives**.  B0–B6, B8, B9: argued, same rule shapes. | `C18bB7.c18b-b7` |
| K | **derives**: `lk⊑rk`, `lk₁⊑rk₁`, `VL⊑idX`, `VL⊑RF`, `lk₁⊑rk₃`, `lk₁⊑rk₄` | `K.*` |
| C1 `L₆ ⊑ R₇` (incl. its one-sided variant) | **not derivable** in any world over its typing contexts, at any index | `C1.c1-unrelated` |
| C2 (late, `LE₃ ⊑ RE₅`) | **not derivable**, same quantifiers | `C2.c2-unrelated` |
| C3 (early, `LE₁ ⊑ RE₁`) | **not derivable**, same quantifiers | `C3.c3-unrelated` |
| ModeOK still needed? | **not for C1–C3** (the relation here has no ModeOK).  It would kill C4 but not C4g. | — |
| **new counterexamples** | **yes: C4 and C4g.**  A *popped* pending name is joined at X⊑★ (`PendingOK`).  The push is one-sided, so no conversion is compared.  C4 holds in HEAD too. | `C4.c4-cex`, `C4InHEAD.C4-HEAD`, `C4g.c4g-cex` |
| reduction closure | P4: every right state of its Merge, IdDyn, Merge, TagUntag steps is related to the left at B4.  Two status steps compose at a Merge whenever the final world is well formed. | `P4c.p4-R7` … `p4-R10`, `st-compose` |
| InteriorMerge (M6) | **false as stated**: a name fresh in the merged boundary can be hidden in the nested world | `MergeCex.InteriorMerge-cex` |

Mechanized: everything in the Agda column.  Argued: C18b's other
blocks, the hunt items of §6, the absence of a Merge-closure failure
on related pairs (§7), and the lemma impact (§8).

## 1. The encoding

A center name that the left sees and the right does not see is passed
by the right embedding either by `skip` (the name was born left-only)
or by `hide` (the right hid a both-sided name with its own `−X`).  The
left embedding is symmetric.

```agda
data _↪_ : TyCtx → ImpEnv → Set where
  []↪  : [] ↪ []
  keep : Δ ↪ Ω → (α ∷ Δ) ↪ (m ∷ Ω)
  skip : Δ ↪ Ω → Δ ↪ (m ∷ Ω)
  hide : Δ ↪ Ω → Δ ↪ (m ∷ Ω)      -- NEW: emb, relabel treat it as skip

data St : Set where joined plain hidden : St
statusAt : η ↪ Ω → ℕ → St          -- keep ↦ joined, skip ↦ plain, hide ↦ hidden
stᴿ W X  = statusAt (ηᴿʷ W) (emb (ηᴸʷ W) X)   -- the right's view of left name X
stᴸ W X′ = statusAt (ηᴸʷ W) (emb (ηᴿʷ W) X′)  -- the left's view of right name X′

markStep : St → St → VarImp → VarImp
markStep plain joined m = X⊑X     -- a plain one-sided name rejoined
markStep _     _      m = m       -- everything else keeps its mark (D15)

StOK : St → St → Set              -- the allowed steps of a continuing name
--   joined → joined | hidden      hidden → hidden | joined
--   plain  → plain  | joined      (nothing → plain from joined/hidden;
--                                  a plain name is never hidden)
```

**The world data.**  The `World` record is unchanged.  The new
information is in its two embeddings, so every world operation (`⊕`,
`⊕ᴸ`, `⊕⁺`, `⊕ʳ`, allocations, `Open1`) is unchanged and produces no
`hide`.  `WfWorld`'s `Joint` gets two cases:

```agda
hidden-r : Joint P ι ι′ → Joint P (keep {α} {X⊑★} ι) (hide {X⊑★} ι′)   -- as left-only
hidden-l : Joint P ι ι′ → Joint P (hide {m} ι) (keep {β} {m} ι′)       -- as right-only
```

**Interior.**  `mark-left` and `mark-right` now return the status step
and the stepped mark.  Two new fields say that a fresh name is never
hidden.

```agda
mark-left : Δᵢ ∋tv X → toExt Θ X ≡ just Xₑ → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
  → StOK (stᴿ W Xₑ) (stᴿ Wᵢ X)
    × (μʷ Wᵢ ∋ˡ emb (ηᴸʷ Wᵢ) X := markStep (stᴿ W Xₑ) (stᴿ Wᵢ X) m)
mark-right : …  (the same with stᴸ, for right names)
fresh-left  : Δᵢ ∋tv X → Fresh Θ X → NotHid (stᴿ Wᵢ X)
fresh-right : Δ′ᵢ ∋tv X′ → Fresh Θ′ X′ → NotHid (stᴸ Wᵢ X′)
```

What `Interior` does at each entry kind follows from these fields
together with HEAD's `join-cont` and `join-fresh`:

| entry | the name | status step | mark |
|---|---|---|---|
| right `−X` of a both-sided X | left X continues | joined → hidden | kept |
| right `+X^β`, β paired with a hidden left X | left X continues | hidden → joined | **kept** (P4, C12–C14, C18b) |
| right `+X^β`, β paired with a plain left X | left X continues | plain → joined | **X⊑X** (C1, C2) |
| left `+X^α` against a plain right-only name of a paired rep. var | right name continues | plain → joined | **X⊑X** (C1's right-first route) |
| left `−X` of a both-sided X, then left `+X` | right name continues | joined → hidden → joined | kept (symmetric) |
| fresh name on both sides, paired (matched `⟪⟫⊑⟪⟫`) | — | fresh, joined | chosen (D11, unchanged) |
| fresh name with no partner | — | fresh, plain | free (left-only must be X⊑★) |
| unbind then bind within ONE boundary (Merge's `[−X,+X]`) | continuing (`toExt`'s `seekUnbind`) | joined → joined | kept (`P4c.IntRR`) |
| Merge | composition of the two steps (§7) | `st-compose` | `st-compose` |

`ConversionInterior` steps its marks by `markStep` too (it has no
status fields, since a conversion context never removes a name).

**The ★ clauses** read LEFT-ONLY in the conversion world:

```agda
LeftOnly W X = ∀ {X′} → Δ′ ∋tv X′ → ¬ Joins W X X′

conv-seal⊑id★   : μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★ → LeftOnly W X → TailImp W (seal X) (mid (id ★))
conv-⨾seal⊑     : TailImp W t t′ → … X⊑★ → LeftOnly W X → TailImp W (t ⨾seal X) t′
conv-unseal⊑id★ : … X⊑★ → LeftOnly W X → ConvImp W (unseal X) ⌞ id ★ ⌟
conv-unseal⨾⊑   : … X⊑★ → LeftOnly W X → ConvImp W c c′ → ConvImp W (unseal X ⨾ c) c′
```

D11's chosen marks at matched fresh pairs are kept.  No ModeOK.

## 2. Why symmetric (C1, mechanized)

C1 (PendingOpenings §5d) is the following pair:

```
L₆ = ([+X^α] ([−X^α] 5⟨ℕ!⟩ ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩⟨ℕ?ℓ0⟩      ⟶* 5
R₇ = ([+X^α] ([−X^α] 5⟨ℕ!⟩ ⟨−X⟩)⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩  ⟶ blame ℓ0
```

HEAD has three derivations of it:

- matched `⟪⟫⊑⟪⟫` with `+X ⊑ id(★)` by `conv-unseal⊑id★` on the
  joined X;
- left-first (`Cex.InD11`): the left's `+X` makes X left-only, then
  the right's `+X` rejoins it and keeps X⊑★;
- **right-first** (`C1.InHEAD.L₆⊑R₇`, new):

```
cast⊑cast (ℕ?), cast⊑ (id(★))
  ⊑⟪⟫  right +X^α: X right-only, mark X⊑★ (chosen; fresh marks are free)
    ⟪⟫⊑  left +X^α: X joins (α, α); mark-right keeps X⊑★
      ⊑cast (X!) at X ⊑ ★
        S ⊑ S
```

The right-first derivation compares no conversion with a ★ clause and
rejoins no left-only name.  So the repair as first stated (only left
names, only right `+X`) keeps it.  The repair rejects the two one-sided
steps (`left-first-rejected`, `right-first-rejected`: `markStep` gives
X⊑X where the world says X⊑★), and the restricted clause rejects the
matched one.

## 3. The corpus

Every derivation below checks against the repaired relation.

| item | derivation | the hidden information it reads |
|---|---|---|
| P4 B1, Cf B0, B2, B3 | `P4.p4-B1`, `p4-B1′`, `p4-B2`, `p4-B3` | matched X⊑★ (D11) |
| P4 B4, the J pair | `P4.p4-B4`, `P4.S⊑J` | right `−X` hides X (`Wc-unbindᴿ`), right `+X` rejoins it (`Wc-bindᴿ`): hidden → joined, X⊑★ kept |
| P4 B5, B6 | `P4.p4-B5`, `p4-B6` | none |
| P4 right states 7–10 against B4's left | `P4c.p4-R7` … `p4-R10` | merged `[−X,+X]` is continuing; IdDyn's tag outside at the same joined X⊑★ |
| C12 B1, C13 B1, C14 B1 | `Rebase.c12-b1`, `c13-b1`, `c14-b1` | each gen layer: hide, then rejoin (`Wcᴸ` is now `keep/hide`) |
| Cg X0, Ch X0, P3 | `Rebase.cg-x0`, `ch-x0`, `TIE.p3-inst` | push, pop at X⊑★; Cg also hides under the pop (`Wg⁻` is `keep/hide`) |
| Cg B1 | `CgB1.cg-b1` | matched X⊑★, the right's `−X` hides |
| C2 X0, B0, B6, B7; Ch B0, B1; C12 B0, X0; Cg B0 | `Rebase.*` | none new |
| C18b B7 | `C18bB7.c18b-b7` | `(−Y,−X)` hides two names (hidden-r twice), `(+X,+Y)` rejoins both, marks kept |
| P1, P2, P6 | `TIE.p1-init`, `p1-tybeta`, `p2-tybeta`, `p6-init-ν`, `p6-tybeta` | P2's X is plain left-only |
| K | `K.lk⊑rk`, `lk₁⊑rk₁`, `VL⊑idX`, `VL⊑RF`, `lk₁⊑rk₃`, `lk₁⊑rk₄` | `IntX★`: a left fresh X rejoins a plain right X: X⊑X, which it already was |

Not ported: K's Evolve-based obligations (`sim-K`, `simBack-K-merge`,
`dgg1-K`), which read HEAD's world, and C18b's other blocks.

## 4. C1, C2, C3 are unrelated (mechanized)

Each result quantifies over every world over the pair's own typing
contexts (`ΔR` for C1, `ΔL` for C2/C3), every term context, and every
index.

**C3 (`c3-unrelated`)** needs only indices and one conversion fact.

- The function pair `[+X^α] (λx:X.x) ⟨−X → +X⟩` against
  `[+X^α] (λx:★.x)⟨X! → id(★)⟩ ⟨−X → id(★)⟩` sits at domain ℕ on both
  sides (read off the argument 5).
- Left first: `X ⊑ ℕ` in the premise index (`lty-ƛ`).
- Right first: `ℕ ⊑ X` (`rty-cast` of the gen body).
- Matched: `−X ⊑ −X` needs X joined in the conversion world, and
  `+X ⊑ id(★)` needs X left-only there (`C3.matched-conv`).  This holds
  in any world.

**C1 (`c1-unrelated`) and C2 (`c2-unrelated`)** need the world history.

- The decisive step is `⊑cast` of a right name tag `X!` facing the
  left's sealed literal (the only left term of variable type).
- That step needs `Joins V 0 k` and `μ ∋ X⊑★` at the left name
  (`var⊑var`, `var⊑★`).
- The invariant (§16):

  ```agda
  Good V = μʷ V ∋ˡ emb (ηᴸʷ V) 0 := X⊑★ → stᴿ V 0 ≡ plain
  ```

  It holds when the left's `+X` is entered:
  - after a one-sided left bind, every right name in scope is plain,
    so a rejoin is X⊑X (`good-fresh`);
  - at a matched pair whose rep. vars are not paired, X is not joined
    (`good-matched`).
- Every one-sided right boundary keeps it (`good-step`, from `StOK`
  and `markStep` alone).
- So `no-S` refutes every right spine that reaches a tag (`Reach`).
- Matched `+X ∥ +X` boundaries with `+X ⊑ id(★)` force the rep. vars
  unpaired (`matched-conv`, `matched-conv★`).
- The proofs walk the two spines.  For C2 that is `LO` (the left's
  boundary under its ground casts) against the right's six stages
  `o-RE₅`, `o-RB₅`, `o-RI`, `o-RU`, `o-J`, `o-RX`.  They read typing
  side premises (`lty-cast`, `lty-bdy`, `lty-$`, `bdy-LB`, `bdy-LB₄`).

C1's one-sided variant (`Cex.InD11`) and the matched variant are
instances of this argument.

## 5. NEW COUNTEREXAMPLES: a popped name at X⊑★ (mechanized)

The repair leaves pending names alone.  `PendingOK` makes a pushed name
X⊑★, and `Open1` keeps the mark when a left `Λ` pops it.  So a popped
name is **joined at X⊑★** without any conversion comparison, because
the push is one-sided.

**C4.**  The pair is C1's own run, one block earlier on the right (the
right has run Inst and TyBeta, the left has not):

```
L₀ = ((ΛX. (λx:X. x))⟨inst Y. (Y?ℓ0 → Y!)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]                     ⟶* 5
R₂ = (([+X^α] (λx:X. x⟨X!⟩^[X:★∼X∼★]) ⟨−X → id(★)⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
   ⟶ (CastFun) ⟶ (CastId) ⟶ (Wrap) ⟶ (Beta) ⟶ (CastId)
     ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩^[]
   ⟶ (TagUntagBad-⟪⟫)  blame ℓ0
```

The derivation is `C4.C4`, and `C4InHEAD.C4-HEAD` in HEAD's relation:

```
cast⊑cast (ℕ?), ·⊑·, cast⊑cast (inst ∥ id(★) → id(★))
  ⊑⟪⟫ PUSHES X (int-ro₃, Wi₃-wf: right-only, X⊑★, β:=★)
    Λ⊑ POPS it (open-⊕): X joined, X⊑★
      ƛ⊑ƛ, ⊑cast (x⟨X!⟩) at X ⊑ ★
```

**C4g** (`C4g.c4g-cex`) uses a gen-mode tag instead.  The mode
condition (ModeOK) permits `★∼X`, so it does not reject this one:

```
R0g = ((λx:★. x)⟨gen X. (X! → id(★))⟩^[]⟨inst Y. (Y?ℓ0 → id(★))⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
R2g = (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → id(★)⟩^[X:★∼X] ⟨−X → id(★)⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
   ⟶* ([+X^α] ([−X^α, +X^α, −X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩^[]
   ⟶ (TagUntagBad-⟪⟫)  blame ℓ0
```

C4g's derivation is Cg X0's (`Rebase.cg-body`), with the codomain
`id(★)`.  It pops at X⊑★, the gen body reads `X ⊑ ★` at the joined X,
then the right's `−X` hides it.

Scope:

- As for C1, the source pair `(L₀, R₀)` is unrelated, so these refute
  M22 SimBackBlame, not the DGG.
- M26 is not refuted, because the left is not a value at the failing
  cast.

**What kills them (argued; one fact mechanized).**

- *ModeOK*: kills C4, not C4g.  Insufficient.
- *A push conversion premise* (candidate): compare the pushed
  boundary's conversion `c′` with the conversion the left's own
  instantiation would produce, the reveal of the left ∀ type (here
  `−X → +X`), in a world where the pending name is joined.
  - `C4g.revX⋢cE`: no conversion world relates `−X → +X` to
    `−X → id(★)` once the right's X is a name, because the seal needs
    X joined and the unseal needs it left-only.  This kills C4 and
    C4g.
  - Every corpus push (P3, Cg X0, C2 X0, K, Ch X0) has `c′ = −X → +X`
    against a left `∀X.X→X`, so they pass.
  - C2 X0 pops by `cc-gen`, which never joins the name.  So the
    premise must be read through the pending opening (an `OpenImp`
    analogue for conversions), not at the popped world.  This is a
    design step.
- *Pop at X⊑X*: kills C4/C4g, but also Cg X0 (its hidden interval
  needs X⊑★).

## 6. Hunt (argued unless named)

- **Left value vs right blame.**  A joined X⊑★ name can come only from
  (i) a matched fresh pair (D11 choice), (ii) a pop (`PendingOK`), or
  (iii) a hide/rejoin of (i)/(ii).
  - (i) compares conversions, so an escaping `id(★)` meets a restricted
    ★ clause (C1, C2, C3).
  - (ii) is C4/C4g.
  - (iii) adds no X⊑★ that was not there before the hiding.
- **Right value vs left diverge.**  None found.  GTNF has no fixpoint,
  and the repair only removes derivations.
- **Tags escaping a boundary.**  C2 (unrelated), C4g (related, §5).
  IdDyn re-spells an escaped tag at its exterior name.  A tag related
  inside at a rejoined hidden name keeps the same mark outside
  (`P4c.p4-R8`).
- **Names hidden on the LEFT and rebound** (`hidden-l`, joined →
  hidden → joined).  The mark is the one the name had while joined, so
  no new X⊑★ arises.  SidedMarks' probe H1 (the right hides, rebinds
  and lets the tag escape) has the shape of C2.  Every route gives X⊑X
  or meets the restricted clause.  Not mechanized.
- **Pending names popping into a hidden name.**  This is impossible.
  `Join↪` pops only into a center the left `skip`s, and a pending name
  is right-only and plain (`PendingOK`'s `RightOnly`), and `StOK`
  forbids plain → hidden.
- **Merge reordering.**  See §7.

## 7. Reduction closure

- **Merge composes statuses** (`st-compose`, mechanized).  Two
  successive steps of a continuing name compose, with the composed
  mark, whenever the final world is well formed.  The one excluded path
  is plain → joined → hidden: its mark is X⊑X at a hidden name, which
  `hidden-r` forbids.
- **But a fresh name can end hidden** (`MergeCex.InteriorMerge-cex`).
  - Matched `+X ∥ +X` followed by the right's `−X` composes to
    `+X ∥ (+X, −X)`.
  - In the merged boundary the left X is fresh.
  - `fresh-left` makes it plain, while the nested world has it hidden.
  - So InteriorMerge (M6) is false as stated.
- **Does a related pair lose its relation at such a Merge?**  Argued:
  no.
  - Hidden-keep matters only if a later right `+X` rejoin is followed
    by a one-sided right tag or check reading X ⊑ ★.
  - For the right's `[+X]` and `[−X]` to be adjacent (mergeable),
    the outer `+X` boundary's interior is the exterior of a `−X`
    boundary, which does not mention X.  So the right's outer
    conversion is X-free (`id(★)`).
  - Then the matched left conversion is either X-free too (the left
    must tag X itself, and `cast⊑cast X! ⊑ X!` needs only X⊑X), or
    `+X ⊑ id(★)` (restricted clause: dead).
  - Probe (run, not mechanized): left `[+X^α] ((λx:X. 7) S) ⟨id(ℕ)⟩`,
    right `[+X^α] ([−X^α] ((λx:★. 7) J) ⟨id(ℕ)⟩) ⟨id(ℕ)⟩`.  The Beta
    fires before any Merge, and the boundaries leave by Id.
- **P4's right Merge/IdDyn steps** keep the relation with the left
  fixed (`P4c.p4-R7` … `p4-R10`).
  - Right state 11 (the final Merge) needs the left's own Merge: B5,
    `(5, 11)`.
  - TyBeta and Wrap appear between P4's mechanized blocks (B1′ → B2,
    B2 → B3, B3 → B4).

## 8. Lemma impact (STATEMENTS-CORE, argued)

| statement | change |
|---|---|
| all statements with `Interior` | its record has the stepped `mark-left`/`mark-right` and `fresh-left`/`fresh-right` |
| M1 MorSide, M2 MorImp (`WorldMor`, "marks may rise") | `WorldMor` must preserve each center's pass kind (`skip` vs `hide`), since `markStep` reads it.  Raising a mark is harmless at plain → joined (`markStep` ignores m) and kept at the others.  MorSide (b) then works field by field.  A27 MarkMono at a joined name is the C4 route (§5). |
| M3 EvolveMor, M4 EvolveInterior | unchanged: allocations `relabel` the embeddings, which keeps `hide`. |
| M5 WfWorld-bind | unchanged statement; `Joint` gains `hidden-r`/`hidden-l`, carried by `relabel`. |
| M6 InteriorMerge | **false as stated** (§7).  It needs `WfWorld` of the final world (for `st-compose`), and either a second composite world with a hidden → plain lowering plus a MergeImp transport along it, or a `fresh-left` clause that allows "hidden" when the other side binds and unbinds a paired rep. var within its entries. |
| M7 MergeConvWorld | as before, at risk.  A name left-only in an inner conversion world can be joined in the merged one, so a restricted ★ fact need not transport.  The statuses do not add risk: `LeftOnly` reads only `Joins`. |
| M8 PayloadImp | unchanged: a hidden name is a left-visible X⊑★ name (`α⊑★`). |
| M13 InstXImpL | its second outcome (an opening with a raised mark, `W ⊕ᴸ⇔ β`) is the pop route of C4.  Under the push conversion premise this outcome needs that premise too. |
| M22 SimBackBlame | still **false** (C4, C4g; C4 also for HEAD).  C1–C3 are removed. |
| M26 CastRedexNoBlame | not refuted by C4/C4g.  Its X-check case is unchanged. |

## 9. Names

- **Encoding**: `hide`, `St`, `statusAt`, `stᴿ`, `stᴸ`, `markStep`,
  `StOK`, `NotHid`, `keepMark`, `hidden-r`, `hidden-l`, `LeftOnly`,
  `Interior.fresh-left`/`fresh-right`.
- **Negative proofs**:
  - facts: `plain-idx`, `π[]`, `lty-cast`, `lty-bdy`, `lty-$`,
    `lty-ƛ`, `rty-cast`, `st-emb`, `st-inv`, `st-[]`, `rejoin`;
  - the invariant: `Good`, `good-step`, `good-fresh`, `good-matched`,
    `Reach`, `no-S`, `no-$`, `matched-conv★`;
  - per pair: `C1.c1-unrelated`, `C2.c2-unrelated`,
    `C3.c3-unrelated`.
- **Counterexamples**: `C1.InHEAD.L₆⊑R₇` (HEAD, right-first),
  `C4.c4-cex`, `C4InHEAD.C4-HEAD`, `C4g.c4g-cex`, `C4g.revX⋢cE`,
  `MergeCex.InteriorMerge-cex`.
- **Corpus**: `TIE.*`, `Rebase.*`, `K.*`, `P4.*`, `P4c.*`,
  `CgB1.cg-b1`, `C18bB7.c18b-b7`.
