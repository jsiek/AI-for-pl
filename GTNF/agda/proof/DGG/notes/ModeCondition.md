# Mode condition: restricting the cast rules by the right cast's modes

Status: 2026-10-05.  Agda: `ModeCondition.agda` (this directory).  It
checks with `agda --safe -v0` from `GTNF/agda`.  It has no holes, no
postulates and no pragmas.  It is not a Def module, and All.agda does
not import it.  No other file was edited.  LEFT is the more precise
side.

The proposal is option 2 of SidedMarks.md:

- keep D11's marks (chosen at the binder) and D15 (a rejoined name
  keeps its mark);
- restrict the cast rules by the mode environment that the right cast
  carries.

Type imprecision `_⊢_⊑_`, the world layer and ConversionImprecision
are **unchanged**.  The condition lives only in the term relation.

## Verdict

**The condition removes the known counterexample, but not the class.**
A new SimBackBlame counterexample exists under `modes` (§5).  Its
decisive inner pair is P4 B4's own J pair: the same world, the same
terms, the same modes, the same index.  The Agda reuses `P4.S⊑J`
verbatim.  So no condition on casts can keep P4 and kill it.  The
difference is how the left-only interval was created, and that is
world information (SidedMarks.md §6, "hidden names").

| question | answer | Agda |
|---|---|---|
| the condition | `ModeOK`, below: a right cast may not read `X ⊑ ★` at the image of a right name whose mode is `★∼X∼★`.  It is a premise of `⊑cast` **and** `cast⊑cast`. | `ModeOK`, `ReadsStar`, `modes` |
| purely in the term relation? | yes.  `_⊢_⊑_`, worlds and `ConvImp` are unchanged.  The condition reads the world's right embedding `ηᴿʷ`, but changes nothing in it. | `Rel`, `CastPolicy` |
| where it bites | only on right casts whose environment contains `★∼X∼★`.  Every right state of every Cambridge run, of P4 and of K is free of it.  So on the whole corpus, H-derivable ⟺ M-derivable. | `NoX`, `lift`, `forget`, `CorpusModes.noX-*`, `reach-lift` |
| P4, all blocks | **derive**: B1 (0,0), Cf-B0 (1,1), B2 (2,2), B3 (3,4), B4 (4,6), B5 (5,11), B6 (6,12) | `P4.p4-B1ᴹ` … `p4-B6ᴹ` |
| Cg X0, C12 X0/B1, C13 B1, C14 B1, C2 X0/B6/B7, Ch B0/X0/B1, P1/P2/P3/P6 | **derive**: HEAD's derivations ported verbatim into H, then lifted | `TIE`, `Rebase`, `HeadInM.*ᴹ` |
| Cg B1, C18b B1–B7, K | **derive** (argued): their right runs are cross-free (mechanized: `noX-Cg`, `noX-C18b`, `noX-K`), so any D11 derivation lifts.  HEAD's K derivation (Regression, pre-D27) was not ported, because it imports `proof.DGG.Evolve`.  Cg B1 and C18b are not mechanized under D11 anywhere. | `reach-lift` |
| `L₆ ⊑ R₇` | **not derivable** in any world.  HEAD's one-sided derivation is ported (`Cex.InH.L₆⊑R₇`), and its `⊑cast (X!)` step is rejected (`cex-step-rejected`).  Probe H1 is also unrelated. | `Cex.cex-unrelatedᴹ`, `Cex.h1-unrelatedᴹ` |
| tag-only reading (as literally proposed: `⊑cast` only, by the coercion's tags) | **not closed under reduction**: a related pair whose left TagUntag step leaves the left state unrelated to every right state | `AsStated.asStated-sim-fails` |
| new counterexample under `modes` | **yes**, at two points of one run (late and early) | `Esc.esc-cex`, `Esc.esc-cex-early` |
| modes changed by reduction? | no.  The mode a cast records for a name is invariant (§4). | argued, plus the P4 and Esc runs |

What is mechanized and what is argued:

- *Mechanized*: everything in the verdict's Agda column.
- *Argued*: Cg B1, C18b, K (by `lift` plus HEAD's or paper
  derivations), the mode-invariance of reduction, and the lemma impact
  (§6).

## 1. The condition

```agda
-- the free center names at which an imprecision derivation reads X ⊑ ★
data ReadsStar : ∀ {μ A B} → μ ⊢ A ⊑ B → ℕ → Set where
  rs-var : ReadsStar (X⊑★ h) X
  -- … congruence through ⇒⊑⇒, ⇒⊑★, and (shifting) ∀⊑∀, ∀⊑, ∀⊑★

ModeOK : (W : World Δ Δ′) → ModeEnv → ∀ {A A′} → A ⊑ᵂ⟨ W ⟩ A′ → Set
ModeOK W μ′ d = ∀ {j k} → ReadsStar d j
  → emb (ηᴿʷ W) k ≡ j → μ′ ∋ˡ k := ★∼X∼★ → ⊥
```

The two cast rules take it as an instance-argument premise.  It
applies to both the source index p and the target index q of the
right cast:

```agda
⊑cast     : … → (q : A ⊑ᵂ⟨ W ⟩ A′) → ⦃ ModeOK W μ′ p × ModeOK W μ′ q ⦄
          → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q
cast⊑cast : … → (q : A ⊑ᵂ⟨ W ⟩ A′) → ⦃ ModeOK W μ′ p × ModeOK W μ′ q ⦄
          → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q
```

Precisely:

- **Which modes permit.**  `X∼X`, `X∼★` and `★∼X` permit; `★∼X∼★`
  forbids.
  - `★∼X` is gen's binder (Reduction `inst-gen`).
  - `X∼★` is its flip, which CastFun puts on the argument cast.
  - `X∼X` permits nothing anyway, since it allows no tag.
  - `★∼X∼★` is the source-scope mode that compilation writes
    (`Coercion.cross`).  It means "the right program had a real
    variable here".
- **How names are indexed.**  μ′ is parallel to the right cast's
  `names Δ′`.  Right name k sits at center `emb (ηᴿʷ W) k`.
  - A read at a left-only center has no right preimage, so it is
    always allowed.
  - A read at a joined center is checked against that name's mode.
- **Why the index, not the coercion.**  The read must be checked on the
  index, not on the coercion's own tags, and `cast⊑cast` must carry it
  too.  §3 shows that the tag-only version is not closed under
  reduction.
- **Mechanized.**  The proposal is policy `modes` (module `M`).  HEAD
  is policy `head⁰` (module `H`), and the tag-only reading is
  `asStated` (module `A`).

## 2. Corpus and P4

**`lift` (mechanized).**  If no cast of R carries `★∼X∼★` (`NoX R`),
every H-derivation of `L ⊑ R` is an M-derivation.  This holds because
the premises' right terms are subterms of R.  `forget` gives the
converse.

- `CorpusModes` checks with `noX?` every right state of the Cambridge
  runs: Cf, Cg, Ch, C2, C5, C10, C12, C13, C14, C17, C18, C18b, C19,
  C23a, C23b, CJ, C8, C22.  It also checks P4 and K.
- **All are cross-free.**  Corpus casts are compiled at top level
  (`^[]`), and the Λ bodies (I, K) contain no casts.  At run time, the
  only modes are gen's `★∼X` and its flip `X∼★`.
- Only the counterexample's `R₀` has `★∼X∼★` (`cex-R₀-cross`).
- So on the corpus, `modes` relates **exactly** what D11 relates.

**HEAD's derivations.**  TermImprecisionExamples and
TermImprecisionRebaseExamples (46f04f4f) are pasted in verbatim; only
their imports were replaced.  They check against H, which is evidence
that H is HEAD's relation.  `HeadInM` lifts them all.

**P4, every block (new, mechanized in H and lifted).**  The worlds are
the following:

- W₄ pairs αᴸ:=ℕ with αᴿ:=ℕ globally.
- The boundary name is X⊑★, both-sided (`W₄²`).
- After the right's −X it is left-only (`W₄ᴸ`).
- At the right's rebind it rejoins and keeps X⊑★ (D15).

```
B2  ([+X^α] (λx:X. x) ⟨−X → +X⟩) 5
  ⊑ ([+X^α] ([−X^α] (λx:★. x) ⟨…⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5
      ⊑cast of the gen wrapper at X→X ⊑ ★→★            (★∼X: allowed)
B3  [+X^α] ((λx:X. x) S) ⟨+X⟩
  ⊑ [+X^α] ((…) S⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩
      ⊑cast X? reading X ⊑ ★ (★∼X), ⊑cast X! reading X ⊑ ★ (X∼★)
B4  [+X^α] S ⟨+X⟩
  ⊑ [+X^α] ([−X^α] J ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩
      where J = [+X^α] S⟨X!⟩^[X:X∼★] ⟨id(★)⟩, and the J pair
      S⊑J : W₄ᴸ ∣ [] ⊢ S ⊑ J ∶ X⊑★ here   (⊑⟪⟫ rejoin, ⊑cast X!)
B5  [+X^α, −X^α] 5 ⟨id(ℕ)⟩ ⊑ [+X^α, −X^α, +X^α, −X^α] 5 ⟨id(ℕ)⟩
B6  5 ⊑ 5
```

Here `S = [−X^α] 5 ⟨−X⟩`.  These derivations were not mechanized
under D11 before; they confirm design.md's claim that P4 needs a
both-sided X at X⊑★.

## 3. The counterexample `L₆ ⊑ R₇`, and why the index (not the tag)

```
L₆ = ([+X^α] ([−X^α] 5⟨ℕ!⟩ ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩⟨ℕ?ℓ0⟩
R₇ = ([+X^α] ([−X^α] 5⟨ℕ!⟩ ⟨−X⟩)⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩
```

`Cex.cex-unrelatedᴹ`: no M-derivation exists in any world.

- R₇'s `X!` is related either by `⊑cast` or by `cast⊑cast`.
- `⊑cast`: `⊑var` forces the left type to be the name's image.  Then q
  reads X ⊑ ★ there (`star-at`), and its mode is `★∼X∼★`.
- `cast⊑cast`: the left casts are `id(★)`, `ℕ!` and `ℕ?`, which are
  atomic (`cc-bad`).
- This covers HEAD's one-sided derivation (ported as
  `Cex.InH.L₆⊑R₇`, with the rejected step `cex-step-rejected`), the
  `⟪⟫⊑⟪⟫` derivation through `conv-unseal⊑id★`, and every other
  derivation (`no-relᴹ`).

**The tag-only reading fails** (`AsStated.asStated-sim-fails`).  Take
the joined X at X⊑★, with every cast at `★∼X∼★`:

```
Lp = [−X^α] 5⟨ℕ!⟩ ⟨−X⟩ ⟨X!⟩⟨X?ℓ0⟩    ⊑   Rp = [−X^α] 5⟨ℕ!⟩ ⟨−X⟩ ⟨X!⟩⟨id(★)⟩
```

- The pair is related by two `cast⊑cast`.
- The left steps by TagUntag.  Neither right state (`Rp`, `…⟨X!⟩`) is
  related to the left's state in any world.  The right's source-scope
  `X!` is now exposed to `⊑cast`.
- Under `modes`, the pre-state's outer `cast⊑cast` is already rejected
  (`pre-rejectedᴹ`): the right's `id(★)` reads X ⊑ ★ at a `★∼X∼★`
  name.

## 4. Does reduction change the modes the condition reads?  No (argued)

Names never change spelling.  `crossΛᴹ` wraps a value in the binder's
dual instead of renaming it (TermSubst §5).  So a cast's environment
only changes where a rule writes one:

| rule | environment written | effect on a name's mode |
|---|---|---|
| compilation | `cross` | `★∼X∼★` |
| `inst-gen` | `★∼X ∷ μ` | the freed name gets `★∼X`; the rest are kept |
| `inst-∀` | `X∼X ∷ μ` | strict |
| CastFun | argument: `flipEnv μ` | `★∼X ↔ X∼★`; `★∼X∼★` is fixed |
| CastSeq, CastSeq? | μ, μ | kept |
| Inst | μ for `closeᵖ 0 p` | kept (the closed binder's tags become `id(★)`) |
| IdDyn-var | `exitEnv Θ μ n` | the moved tag's exterior name gets its interior name's mode, and a continuing name is the same binder; unseen names get `X∼X` |

- So "cross" and "gen-born" are stable properties of a (name, cast)
  pair.
- The P4 and Esc runs show the IdDyn case: `X!^[X:X∼★]` leaves
  `[−X^α, +X^α]` as `X!^[X:X∼★]`.
- The index-based condition is preserved by the cast redexes on the
  right: CastFun, CastSeq, CastId and IdDyn produce casts whose indices
  are sub-derivations of the old ones, with flip-invariant modes.
- The failure is not here: it is §5.

## 5. NEW COUNTEREXAMPLE under `modes` (mechanized: `Esc`)

```
LE = ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)⟨ℕ!⟩^[]⟨ℕ?ℓ0⟩^[]      ⟶* 5
RE = ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → id(★))⟩^[] X) ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩^[]
```

The right's gen does not re-check on the way out (codomain `id(★)`).
Its run:

```
⟶ (TyBeta)  (([+X^α] ([−X^α] (λx:★. x) ⟨…⟩)⟨X! → id(★)⟩^[X:★∼X] ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩
⟶ (Wrap) ⟶ (CastFun) ⟶ (Wrap) ⟶ (Beta)
  RE₅ = ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨id(★)⟩^[X:★∼X] ⟨id(★)⟩)⟨ℕ?ℓ0⟩
⟶ (Merge) ⟶ (IdDyn) ⟶ (Merge) ⟶ (CastId)
  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩
⟶ (TagUntagBad-⟪⟫)  blame ℓ0
```

**Late pair** (`esc-cex`): LE₃ ⊑ RE₅ holds in M; RE₅ blames; LE₃ never
blames.

```
LE₃ = ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)⟨ℕ!⟩⟨ℕ?ℓ0⟩

cast⊑cast (ℕ?)
  cast⊑ (ℕ!)
    ⟪⟫⊑ the left's +X^α          X left-only, X⊑★          (IntLE)
      ⊑⟪⟫ the right's +X^α       X rejoins (α, α), keeps X⊑★ (D15)
        ⊑cast id(★)^[X:★∼X]       reads X ⊑ ★: allowed
          ⊑⟪⟫ the right's −X^α   X left-only
            S⊑J                   ← P4 B4's J pair, verbatim
```

**Early pair** (`esc-cex-early`): both after TyBeta.  Matched boundaries
with `conv-↦⊑↦ (seal ⊑ seal) (conv-unseal⊑id★ here)`: D11 lets the
**joined** X be X⊑★, so `+X ⊑ id(★)` applies.  The gen body `X! → id(★)`
at `★∼X` is related by `⊑cast` at X→X ⊑ X→★.

**Why no cast condition can help.**

- `esc-inner≡p4-inner`: the premise under the right's `−X^α` is
  `P4.S⊑J` itself, in the same world `W₄ᴸ`.
- Both modes on the way are gen modes (`X∼★` on the tag, `★∼X` on the
  `id(★)`), as in P4.
- The difference is outside the J pair:
  - In P4 the left-only interval was opened by the **right's** −X.
    The boundaries are matched, `+X ⊑ +X`, and the tag is re-checked by
    `X?`.
  - Here it was opened by the **left's** own +X (one-sided `⟪⟫⊑`), and
    the right's +X^α has `id(★)`.
- That is exactly the "J" distinction of SidedMarks.md §4.  Removing
  it needs **both** of the following:
  - the hidden-names world case (a name born left-only that a right
    fresh `+X` joins gets X⊑X), which kills the late pair;
  - `conv-unseal⊑id★` / `conv-seal⊑id★` / `conv-⨾seal⊑` /
    `conv-unseal⨾⊑` restricted to left-only names, which kills the
    early pair.
- The mode condition is then redundant for the known examples: the
  hidden-names repair already kills `L₆ ⊑ R₇`, whose X is born
  left-only (SidedMarks.md §6).

**Scope.**  The source programs are not related.  `∀X.X→X ⋢ ∀X.X→★`
(`esc-source-unrelated`), as for `L₀`/`R₀`.  So this refutes M22
SimBackBlame (stated for all related pairs), not the DGG.

## 6. Lemma impact (STATEMENTS-CORE, argued)

| statement | change under `modes` |
|---|---|
| M1 MorSide, M2 MorImp | new obligation: `ModeOK` transports along a world morphism (its `ReadsStar` centers rename; it needs `mor-ηᴿ` and no new joins of a right name with a cross cast).  Raising a mark (A27) can create a read: a cross cast related at a raised X⊑★ becomes ill-formed.  **At risk wherever MorImp raises a mark under a right source-scope cast.** |
| M11 SubstImp | unchanged in shape.  Right casts and their μ′ are untouched; the condition rides on the indices, except through MorImp (row above). |
| M12 InstXImp2 | fine.  `inst-gen` gives the freed name `★∼X` (allowed); `inst-∀` gives `X∼X`.  Choosing m′ = X⊑★ over a Λ body with `★∼X∼★` casts reads nothing new, since the body was related at X⊑X. |
| M13 InstXImpL | **at risk**.  The second outcome joins the left binder to a right ★ name with a raised mark.  If the right's scope holds `★∼X∼★` casts on that name, they may now read X ⊑ ★.  Not hit by the corpus (the Inst'd Λ bodies have no casts). |
| M17 SimCast, M20 SimBackCast, M24 CatchupCast | each rebuilt cast's indices are sub-derivations of the old one's.  Its modes are the old ones, flipped (CastFun), kept (CastSeq), or read back (IdDyn).  Preserved. |
| M14–M15, M18, M21, M23, M25 (merge, boundaries) | no cast premise is created; carried derivations keep their ModeOK provided the interior world's right embedding of the cast's names is unchanged (Merge does not change which names a cast sees). |
| M22 SimBackBlame | **still FALSE** (`Esc.esc-cex`, `Esc.esc-cex-early`). |
| M26 CastRedexNoBlame | its X-check case loses the `★∼X∼★` instances; the gen-mode case is unchanged.  Nothing gained for M22. |
| top-level DGG | unchanged (no source pair changes status: `lift` / `forget` on the corpus). |

## Files and names

- Condition: `NonCross`, `ReadsStar`, `ModeOK`, `CrossFree`
  (tag-only), `CastPolicy`, `head⁰`, `modes`, `asStated`, `Rel`, `H`,
  `M`, `A`.
- Transfer: `NoX`, `noX?`, `noX-sound`, `lift`, `forget`,
  `CorpusModes.reach-lift`, `CorpusModes.noX-*`.
- HEAD ports: `TIE`, `Rebase`, `HeadInM`.
- P4: `P4.p4-B1 … p4-B6`, `P4.p4-B1′`, and their `ᴹ` versions;
  `P4.S⊑J`.
- Counterexample: `Cex.InH.L₆⊑R₇`, `Cex.cex-step-rejected`,
  `Cex.cex-unrelatedᴹ`, `Cex.h1-unrelatedᴹ`, `no-relᴹ`, `star-at`.
- Tag-only: `no-relᴬ`, `AsStated.asStated-sim-fails`,
  `AsStated.pre-rejectedᴹ`.
- New counterexample: `Esc.esc-late(ᴹ)`, `Esc.esc-early(ᴹ)`,
  `Esc.esc-cex`, `Esc.esc-cex-early`, `Esc.esc-inner≡p4-inner`,
  `Esc.esc-source-unrelated`.
