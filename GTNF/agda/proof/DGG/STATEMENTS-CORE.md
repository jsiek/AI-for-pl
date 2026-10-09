# DGG: the MAJOR statements, consolidated

Status: 2026-10-04, for review.  None of these statements is approved.
The Agda text is `proof/DGG/drafts/StatementsCore.agda`, which checks
with `agda --safe -v0` (from `GTNF/agda`).  Each block below is copied
from that file by a script.  It replaces, for review,
`STATEMENTS-REVIEW.md` (108 statements).  The INLINE statements stay
in `drafts/Statements.agda` as text: nobody reviews them, and each is
proved in its consumer.  LEFT is the more precise side.

**D31 note (2026-10-09; supersedes the D27 and D28 notes below where
they differ).**  design.md D31 (adopted) replaced the pending list
`πʷ` by SLOTS of the index (`A ⊑ᵂ⟨ W ⟩[ O ] A′`, `OpenO`; judgment
`W ∣ γ ⊢ M ⊑ M′ ∶[ O ] p`) and D28's grants by permissions chosen at
joining boundaries (`JoinRep`, `Wᵢ +κ K`, "the join pays").  The
statements below still mention `πʷ` and grants and are NOT yet
rewritten; the changes (D28pD30.md §8) are:

- `Pre W` (all statements) loses `πʷ W ≡ []`; it keeps `κʷ W ≡ []`
  and `WfWorld W`.  Every statement is at `O = []`.
- `CatchupRightπ` becomes `CatchupRightO` (CatchupRight with slots,
  the left a VALUE) and gains `CatchupRightκ` (at a world with
  permissions, the premise of a permitting boundary).
- M1 MorSide, M2 MorImp, M3 EvolveMor: the `PendingMor` parts go
  (openings are right positions in the index, renamed with the right
  side).  "κ may grow" remains, now only at boundaries.
- `PushInstR`, `RightMergePending`, `PushCompose`, `WfPop`,
  `PopInstX`: their π bookkeeping becomes slot bookkeeping (`Carried`,
  `Fill`, `NewSlot`); `WfPop` becomes the `SlotOK` premise of `⊑⟪⟫`.
- M19 SimBackApp, M24 CatchupCast (CastFun): no grant moves, so
  `castfun-grant` and R12 go.  M20 SimBackCast (TagUntag): the drop
  lemma goes.
- NEW: a κ-weakening at Wrap into a permitting boundary (M16, M19), and
  the permission of a merged rejoin (M14, M6, M15); both argued, open.
- M22 SimBackBlame, M26 CastRedexNoBlame: C1-C5, C4g and the hunt's
  gen-valued C4 stay dead (examples/TermImprecisionPermissionExamples).

**D27 note (2026-10-05).**  design.md D27 replaced D26's `Opens` by
pending names in the world (the field `πʷ` of `ImprecisionWorld.World`;
TermImprecision §2).  The statements below still mention `Opens` and are NOT yet
rewritten; that is the next review.  Per
`notes/PendingOpenings.md` §6 the changes are:

- M23 CatchupRightᴳ becomes `CatchupRightπ`: CatchupRight at any
  pending names, with the left a VALUE (no Opens image).
- M1 MorSide loses (e) (the `Opens` transport, `instX-ren`): pending
  names are name positions (`PendingMor`, trivial).
- M2 MorImp becomes `MorImpπ` (the pending names ride along).
- M15 RightMergeOpens becomes `RightMergePending`, with the INLINE
  `PushCompose`.
- NEW MAJOR `PopInstX` (popping is instantiating; the `⊑⟪⟫` case of
  M13 InstXImpL) and `PushInstR` (the right's Inst + TyBeta against a
  left ∀-value; replaces B7, B9 and the INLINE B13 InstSyncᴳ).
- INLINE A25 WfOpens becomes `WfPop` (`wf-⊕⁺` generalized); A26
  OpensEvolveᴿ goes.
- M12 InstXImp2: its `open-∀` "MISSING FORM" becomes the `⊑⟪⟫`-push
  case.
- M22 SimBackBlame and M26 CastRedexNoBlame are false as stated for
  the current relation (PendingOpenings.md §5d; independent of D27).

Net: 26 → 28 MAJOR.  The top-level DGG statement is unchanged
(top-level worlds have no pending name: `πʷ W ≡ []`).

**D28 note (2026-10-05).**  design.md D28 adopted permissions: the
world field `κʷ` (permitted right rep. vars), marks COMPUTED from it
(`marksʷ`), grants on right checks (`⊑cast` with `CastGrant`), R1 on
`⟪⟫⊑` (`All (UnbindOK W) Θ`) and R2 on the four ★ conversion clauses
(`LeftUnpermitted`).  The statements below are NOT yet rewritten.
Affected (`notes/PermissionsR.md` §7, `notes/Permissions.md` §7):

- `Pre W` (all statements) gains `κʷ W ≡ []` beside `πʷ W ≡ []`, and
  `WfWorld W` (the check fact of PermissionsR §5 needs `wf-joint`).
  In Agda the Def statements already take `κʷ W ≡ []` (EvolveLemmas
  `⟿-κʷ` carries it along an evolution); `CatchupBlame` does not need
  it and is unchanged.
- M1 MorSide, M2 MorImp: "marks may rise" (A27 MarkMono) becomes
  "κ may grow", now `κ-weaken` WITH the side condition `R12` (R1/R2 are
  anti-monotone in κ); `WorldMor` renames κ by the right rep. var
  renaming.
- M3 EvolveMor: κ shifts with the right side (`map suc`).
- M7 MergeConvWorld and M14 MergeImp must PRESERVE R2: free when an
  input ★ clause supplies it; a MIXED case that creates a ★ clause
  needs `LeftUnpermitted` as a new hypothesis.
- M13 InstXImpL: no mark to raise; an X⊑★ at a joined name needs a
  grant above.
- M15 RightMergeOpens/RightMergePending and M18 SimBdy: turning a
  matched left boundary into a one-sided one (`⟪⟫⊑⟪⟫` → `⟪⟫⊑`) now
  needs R1 for its unbind entries (fails for P4-B3-like matched seals
  under a grant).
- M19 SimBackApp (CastFun) and M24 CatchupCast: `R12 (β ∷ κ)` of the
  argument (`castfun-grant`).
- M20 SimBackCast (TagUntag): the drop lemma (PermissionsR §4.3;
  pieces mechanized, a re-ordering walk missing).
- M22 SimBackBlame and M26 CastRedexNoBlame: C1–C4g and C5 are no
  longer counterexamples (`examples/TermImprecisionPermissionExamples`:
  `C1.c1-unrelated`, `C3.c3-unrelated`, `C5Dead.c5-unrelated`,
  `C5Dead.c5-redex-unrelated`); no new counterexample is known.
- The Sim, SimBack and CatchupRight skeletons have a new hole each,
  the granting `⊑cast` (its premise is at a world with a permission):
  `SimFrame-⊑castκ`, `SimBackFrame-⊑castκ`, `CatchupRightκ`.
- Not adopted: the push type premise (redundant under permissions).
  Open: H1, the push ORDER (`notes/PushTypePremise.md` §7); fixed by
  D29 below.

**D29 note (2026-10-06).**  design.md D29 added `claim-rep` to `Λ⊑`'s
`Claim`.  With nothing pending, the binder pairs its abstract rep. var
lexically with an unnamed right `★` rep. var `β` (`W ⊕ᴸ⇔ β`).  The
right boundary that later names `β` rejoins it (`Interior.join-fresh`).
It fixes H1 (`notes/PushOrder.md`, `examples/TermImprecisionH1Examples`).
The statements below are NOT yet rewritten.  Affected:

- Every lemma by induction on `⊑` gets a `claim-rep` case of `Λ⊑`, like
  `claim-fresh`'s at the world `W ⊕ᴸ⇔ β`.  The skeletons have one new
  hole each: `CatchupRight-claim-rep` (CatchupRightProof) and
  `SimBackFrame-Λ⊑⇔` (SimBackProof).  CatchupBlame has the case and
  stays finished.
- INLINE: `WfWorld (W ⊕ᴸ⇔ β)` from `WfWorld W` and the claim's premises
  (`(0, β)` agrees by `abst-★`; `β` unnamed, so named uniqueness is
  unaffected).
- M1 MorSide, M2 MorImp, M3 EvolveMor and AllocImp: `β` is renumbered
  with the right side, like `κ`.
- M13 InstXImpL: when the left's `TyBeta` catches up with a claimed
  binder, the lexical pair `(0, β)` becomes global (`allocᴸ⇔`), as for
  a pop.
- `PushInstR`: a SECOND Inst on a ∀-boundary value cannot keep the
  first Inst's push and pop.  It turns that pop into `claim-rep α`
  above the new boundary, followed by `push-none` and the rejoin
  (`notes/PushOrder.md` §5).  SimBack's case for the right's Inst then
  has no Merge to wait for.
- If pushes were removed as well (`notes/NoPush.md`; NOT adopted),
  then `PushInstR` (Λ case), `RightMergePending`, `PushCompose`,
  `WfPop`, `PendingMor`, `PopInstX` and `CatchupRightπ` would lose
  their pending-name parts.  But the gen-value case (C2 X0, G1) would
  then be unrelated, which refutes DGG part 1.

## 0. Overview

**Count.**  26 MAJOR statements.

| group | MAJOR |
|---|---|
| transports and worlds (§2) | 10 |
| substitution, instantiation, merge (§3) | 5 |
| redex lemmas of Sim and SimBack (§4) | 7 |
| CatchupRight (§5) | 4 |

Of the 108 old statements, 54 are folded into these 26, 11 are
corollaries of the generic transports or are no longer needed, and 43
are INLINE (§7).

**The rule.**  A statement is MAJOR when it does real work (an
induction, or a non-trivial case analysis) and either has at least two
consumers or is the induction behind one skeleton hole.  Everything
else is INLINE.

**The generic transports.**  One world morphism, `WorldMor ρ ρ′ W W₁`,
covers three things:

- a rep. var renaming on either side (`RepMor.rm-ren`: an allocation or
  a binder insertion);
- a representation in place (`rm-refine`: `abstR → bindR R`);
- raised marks (`mor-μ`: X⊑X to X⊑★).

Three statements are stated over it:

- `MorSide` moves the world-level side premises: `⊑ᵂ`, `Interior`, the
  two conversion premises and `Opens`;
- `MorImp` moves the relation;
- `EvolveMor` says that an evolution *is* a world morphism.

Together they replace eleven transports (A6–A9, A12–A19), three
inductions on `⊑` (A1, B8, A27) and the four allocation corollaries
(A2–A5).

- EvolveImp, which is approved, becomes `EvolveMor` followed by
  `MorImp`.
- The typing side premises move by the existing lemmas, used on each
  side of the morphism: `coercion-renᴿ`/`coercion-refine`,
  `⊢renᴿ`/`⊢refine`, `interior-ren`, `conversion-ren` and `wfctx-ren`.
  No substitution or renaming lemma is restated.

**Shared forms between Sim and SimBack.**

- *What is shared.*  Everything at the world level is shared: the
  transports, `EvolveReplay` (A29 and A30 merged into one two-sided
  statement), `PayloadImp` (A31 and A32 merged), `TyBetaSync2` (an
  INLINE helper used by both TyBeta holes), and the merge lemmas.
- *What is not shared.*  The redex lemmas themselves are not merged
  into one statement parameterized by direction.  The relation has no
  flip: `ν⊑` has no `⊑ν`, and `⊑⟪⟫` has openings that `⟪⟫⊑` lacks.
  The two conclusions also differ.  SimConcl is one left step against a
  right run; SimBackConcl is one right step against a left run or
  blame.  So a statement indexed by direction would just be the pair
  of the two.
- *What was merged instead.*  Each side's redex lemmas are merged by
  redex kind, which takes 24 statements down to 6: `SimApp`, `SimCast`
  and `SimBdy`, with their mirrors.

**Dependency tree.**  `→` means "its proof uses".  Approved or proved
statements are in brackets, and INLINE glue is in parentheses.  `↺`
marks a recursive call on a derivation that is not a subderivation.

```
[DGG] → [Sim*] → [Sim] → SimApp, SimCast, SimBdy, [CatchupRight]
                         (SimTyBeta, SimCast-ToBlame, frames)
        [SimBack*] → [SimBack] → SimBackApp, SimBackCast, SimBackBdy,
                                 SimBackBlame, WfWorld-bind,
                                 [CatchupLeft], [CatchupBlame]
                                 (SimBackTyBeta, frames,
                                  SimBackValue → [CatchupRight])

SimApp, SimBackApp → SubstImp, [CatchupRight] / [CatchupLeft]
SimCast, SimBackCast → [CatchupRight] / [CatchupLeft], (InstSyncᴳ)
SimBdy, SimBackBdy → InteriorMerge, MergeConvWorld, MergeImp,
                     RightMergeOpens (SimBackBdy)
SimBackBlame → [CatchupBlame], [CatchupLeft], CastRedexNoBlame
(SimTyBeta, SimBackTyBeta) → InstXImp2, InstXImpL, MorImp, PayloadImp
(frames) → EvolveMor, MorSide, EvolveInterior, [EvolveImp];
           ·₂ also RunReplay, EvolveReplay, MorImp

[EvolveImp] → EvolveMor, MorImp
MorImp → MorSide, WfWorld-bind
SubstImp → MorImp, WfWorld-bind, [ImprecisionTyping]
InstXImp2, InstXImpL → MorImp, WfWorld-bind
MergeImp → WfWorld-bind          RightMergeOpens → InteriorMerge

[CatchupRight] = CatchupRightᴳ at zero openings
CatchupRightᴳ → CatchupCast, CatchupBdy, WfWorld-bind, EvolveMor,
                MorSide, EvolveInterior, [EvolveImp]   (frames E2–E8)
CatchupCast → CastRedexNoBlame, ↺CatchupCast, CatchupBdy,
              (InstSyncᴳ: InstXImp2, MorImp) then ↺CatchupRightᴳ
CatchupBdy → MergeImp, InteriorMerge, MergeConvWorld,
             RightMergeOpens, ↺CatchupBdy
```

**The catch-up cycle.**  It is unchanged in substance.

```
CatchupRightᴳ → (cast frames) → CatchupCast →(Inst, InstSyncᴳ) CatchupRightᴳ on a derivation InstSyncᴳ creates
```

There are also the self-loops `CatchupCast ↺` and `CatchupBdy ↺`.
There is no other cycle: Sim and SimBack call CatchupRight (SimBack
through SimBackValue), and nothing calls back.

A measure that would break the cycle is defined on the RIGHT term
only.  Its components are compared lexicographically, and then the
derivation:

1. `ι`, the number of `instᵖ` nodes in the right term's coercions.
   Inst consumes one, and no administrative step creates one.
2. `κ`, the total size of the right term's coercions, counting the `︔`
   node.  CastId, CastSeq, CastSeq? and TagUntag decrease it.
3. `β`, the number of boundaries, plus, for each tag cast, the number
   of boundaries around it.  Merge, Id and IdDyn decrease it.
4. The size of the derivation, for the structural calls.

A catch-up runs only administrative steps.  The only TyBeta follows an
Inst, and each re-entry is compared with the term before that Inst,
where `ι` has already dropped.  I have not checked this in Agda.

## 1. Fit check

The method: for each skeleton, I made a temporary copy and took the
MAJOR statements (from StatementsCore) and the INLINE statements (from
drafts/Statements) as module parameters.  Then I replaced every hole.
Each old redex child became a one-line adapter over its MAJOR
statement, for example:

```agda
simWrap pre d u w ci ri rd sc =
  simApp pre d (V-⟪⟫ u I-fun) w (Wrap u w ci ri rd sc)
```

So the adapters also check that the old statements are instances.
Each copy was checked with `agda --safe -v0`, and all the copies are
deleted.

| file | holes | MAJOR | INLINE | not covered |
|---|---|---|---|---|
| SimProof | 47 | 21 (SimApp 3, SimCast 10, SimBdy 8) | 26 (ToBlame 14, frames 10, SimTyBeta 2) | 0 |
| SimBackProof | 46 | 32 (SimBackApp 3, SimBackCast 10, SimBackBdy 8, SimBackBlame 10, WfWorld-bind 1) | 14 (frames 11, SimBackTyBeta 1, SimBackValue 2) | 0 |
| CatchupRightProof | 7 | 1 (WfWorld-bind) + CatchupRightᴳ as the argument of one | 6 (E2, E3, E6, E7, E8 ×2) | 0 |

- **SimBackProof clause changes.**  The two clause changes of
  STATEMENTS-REVIEW.md §1 are still needed: the `⊑⟪⟫ (open-∀ …)` ×
  `ξ-⟪⟫` and × `Blame-⟪⟫` clauses become `inj₁` through SimBackValue,
  because the left is a value.  With them, the copy checks with no
  holes left.
- **Corollaries.**  A second temporary module derives A12–A15, A18,
  A19 and EvolveImp from `MorSide`, `MorImp` and `EvolveMor`.  It also
  uses four INLINE helpers: `fusionᴹ`, `wfctx-mor`, `castTy-mor` and
  `nuTy-mor`.  That module checks too.  A16 and A17 are the same
  pattern, plus `fusionᴮ` and `interior-functional`; I did not check
  them in Agda.
- **Not re-run: the draft proofs of MAJOR statements**
  (drafts/{AllocImp,SubstImp,InstXImp,MergeImp}Proof).
  - The holes they left uncovered are unchanged: InstXImpProof has 14
    (Q3) and MergeImpProof has 10 (B15's generalization).
  - AllocImpProof becomes MorImp's proof.  Its 3 routine `BdyTy`
    holes are `bdyTy-mor`.
  - EvolveImpProof is replaced by the corollary above.

## 2. Transports and worlds

### M1 `MorSide`
```agda
MorSide : Set
MorSide = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
  → WorldMor ρ ρ′ W W₁
    -- (a) type imprecision
  → (∀ {A A′} → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W₁ ⟩ A′)
    -- (b) interior worlds (the boundary rules)
    × (∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
         → WfWorld W₁
         → Interior W Θ Θ′ Wᵢ
         → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ] Σ[ Wᵢ₁ ∈ World Δᵢ₁ Δ′ᵢ₁ ]
             Interior W₁ (renᴮᴿ ρ Θ) (renᴮᴿ ρ′ Θ′) Wᵢ₁
             × WorldMor ρ ρ′ Wᵢ Wᵢ₁ × AllAgree Wᵢ₁
             × (WfWorld Wᵢ → WfWorld Wᵢ₁))
    -- (c) the conversion premise of ⟪⟫⊑⟪⟫
    × (∀ {Δᵢ Δ′ᵢ Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
         (b : BdyTy Δ Θ Δᵢ Aᵢ c A) (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
         → BdyConversionImp W b b′
         → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ]
           Σ[ b₁ ∈ BdyTy Δ₁ (renᴮᴿ ρ Θ) Δᵢ₁ Aᵢ c A ]
           Σ[ b₁′ ∈ BdyTy Δ′₁ (renᴮᴿ ρ′ Θ′) Δ′ᵢ₁ A′ᵢ c′ A′ ]
             BdyConversionImp W₁ b₁ b₁′)
    -- (d) the conversion premise of ν⊑ν
    × (∀ {A A′ C C′ c c′ B B′}
         (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
         → NuConversionImp W n n′
         → Σ[ n₁ ∈ NuTy Δ₁ A C c B ] Σ[ n₁′ ∈ NuTy Δ′₁ A′ C′ c′ B′ ]
             NuConversionImp W₁ n₁ n₁′)
    -- (e) the openings of ⊑⟪⟫ (W read as an interior world); under
    -- each opening the left is renamed by one more `extᵗ`
    × (∀ {Δ⁺} {W⁺ : World Δ⁺ Δ′} {Θ′ M A M₀ A₀}
         → AllAgree W₁
         → Opens Θ′ W M A W⁺ M₀ A₀
         → WfWorld W⁺
         → Σ[ ρ⁺ ∈ Renameᵗ ] Σ[ Δ₁⁺ ∈ Ctxᵗ ] Σ[ W₁⁺ ∈ World Δ₁⁺ Δ′₁ ]
             Opens (renᴮᴿ ρ′ Θ′) W₁ (renᴹᴿ ρ M) A W₁⁺ (renᴹᴿ ρ⁺ M₀) A₀
             × WorldMor ρ⁺ ρ′ W⁺ W₁⁺ × WfWorld W₁⁺)
```
- **Intent.**  The world-level side premises move along any world
  morphism.  These are `⊑ᵂ`, the interior world, the conversion
  premises of `⟪⟫⊑⟪⟫` and `ν⊑ν`, and the openings.  Under each opening
  the left is renamed by one more `extᵗ` (ρ⁺).
- **Consumers.**  MorImp (every rule with a side premise).  Through
  EvolveMor, every frame of Sim, SimBack and CatchupRight.
- **Plan.**  The parts in order:
  - (a) is `renameᵗ-cong` on `mor-ηᴸ`/`mor-ηᴿ`, with monotonicity of
    `_⊢_⊑_` in the marks.
  - (b) works field by field, with `toExt-renᴮᴿ` for continuation and
    `mor-paired` for `join-fresh`.
  - (c) and (d) use `ConvImp`, which reads only `μ`/`emb`, so it moves
    unchanged.
  - (e) is an induction on `Opens`, with `instX-ren`.

### M2 `MorImp`
```agda
MorImp : Set
MorImp = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WorldMor ρ ρ′ W W₁
  → WfWorld W₁
  → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ renᴹᴿ ρ M ⊑ renᴹᴿ ρ′ M′ ∶ q)
```
- **Intent.**  `⊑` moves along a world morphism.
  - At an allocation it is A1 (AllocImp).
  - At `rm-refine` it is B8 (RefineImp: an InstX result moved into the
    represented interior of `inst []`).
  - At raised marks it is A27 (MarkMono).
- **Consumers.**  EvolveImp (now a corollary).  SubstImp's `lift-env`
  (`crossΛᴹ`).  InstXImp2 and InstXImpL (`inst-gen`, raised marks).
  The INLINE TyBeta helpers (refinement).  The `·₂` frames (the
  argument under the function's allocations).
- **Plan.**  Induction on `⊑`.  Binders use `extᵗ ρ` and WfWorld-bind,
  side premises use MorSide and the existing typing lemmas, and
  `blame⊑` uses `⊢renᴿ`/`⊢refine`.

### M3 `EvolveMor`
```agda
EvolveMor : Set
EvolveMor = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → WorldMor (nnew ξs +_) (nnew ξs′ +_) W W′ × (WfWorld W → WfWorld W′)
```
- **Intent.**  An evolution is a world morphism, `(nnew ξs +_)` on the
  left and `(nnew ξs′ +_)` on the right, and it keeps `WfWorld`.  The
  new pairs of `ev-2` and `ev-L⇔` are off the image.
- **Consumers.**  EvolveImp.  Every frame (A13–A19 are corollaries:
  §1).  CatchupRightᴳ.
- **Plan.**  Induction on `⟿`.  Each step is a morphism (`repwk-alloc`
  with the recorded payload premise), and morphisms compose.
  `WfWorld` uses the recorded `Agree`, moved by `⊑ᴿ-ren`.

### M4 `EvolveInterior`
```agda
EvolveInterior : Set
EvolveInterior = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {ξs ξs′ : List Alloc}
    {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Wᵢ′ : World (applyˢ ξs Δᵢ) (applyˢ ξs′ Δ′ᵢ)} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ
  → Wᵢ ⟿[ ξs ∣ ξs′ ] Wᵢ′
  → Σ[ W′ ∈ World (applyˢ ξs Δ) (applyˢ ξs′ Δ′) ]
      (W ⟿[ ξs ∣ ξs′ ] W′) × Interior W′ (↑ᴮ*[ ξs ] Θ) (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′
```
- **Intent.**  The IH's evolution of an interior world lifts to the
  outer world, with the boundary renumbered as `ξ-⟪⟫*` renumbers it.
- **Consumers.**  The boundary frames of Sim (3), SimBack (3) and
  CatchupRight (3).
- **Plan.**  Induction on `⟿`, with InteriorAlloc (A20) at each step.
  The interior reps are the exterior reps.

### M5 `WfWorld-bind`
```agda
WfWorld-bind : Set
WfWorld-bind = ∀ {Δ Δ′} {W : World Δ Δ′} {m : VarImp}
  → WfWorld W → WfWorld (W ⊕ m) × WfWorld (W ⊕ᴸ)
```
- **Intent.**  The premise worlds of `Λ⊑Λ` and `Λ⊑` are well formed.
- **Consumers.**  The `Λ⊑` holes of CatchupRightProof and SimBackProof.
  Also MorImp, SubstImp, InstXImp2, InstXImpL and MergeImp.
- **Plan.**  As the existing `wf-⊕⁺`.  `⊕ m` adds the lexical pair
  `(0, 0)` (`abst-abst`), and `⊕ᴸ` is `left-only` at X⊑★.  Old pairs
  shift by `⊑ᴿ-ren`.

### M6 `InteriorMerge`
```agda
InteriorMerge : Set
InteriorMerge = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δᵢᵢ Δ′ᵢᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Wᵢᵢ : World Δᵢᵢ Δ′ᵢᵢ} {Θ₁ Θ₂ Θ₁′ Θ₂′}
  → Interior W Θ₂ Θ₂′ Wᵢ
  → Interior Wᵢ Θ₁ Θ₁′ Wᵢᵢ
  → Interior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) Wᵢᵢ
```
- **Intent.**  Interior worlds compose across a Merge.
- **Consumers.**  SimBdy, SimBackBdy, CatchupBdy, RightMergeOpens.
- **Plan.**  `toExt (Θ₁ ++ Θ₂)` composes.  A name fresh in the
  composite is fresh in Θ₁, or fresh in Θ₂ and continuing through Θ₁.

### M7 `MergeConvWorld`
```agda
MergeConvWorld : Set
MergeConvWorld = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δ₂ᶜ Δ′₂ᶜ Δ⋉ᶜ Δ′⋉ᶜ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {W₂ᶜ : World Δ₂ᶜ Δ′₂ᶜ} {Θ₁ Θ₂ Θ₁′ Θ₂′}
  → WfWorld W
  → Interior W Θ₂ Θ₂′ Wᵢ
  → ConversionInterior W Θ₂ Θ₂′ W₂ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ → Δ′ ⊢ᶜ Θ₁′ ++ Θ₂′ ⇒ Δ′⋉ᶜ
  → Σ[ W⋉ᶜ ∈ World Δ⋉ᶜ Δ′⋉ᶜ ]
      ConversionInterior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) W⋉ᶜ × WfWorld W⋉ᶜ
      -- the outer pair's conversions
      × (∀ {s s′ r r′}
           → SameConv Δ⋉ᶜ r Δ₂ᶜ s → SameConv Δ′⋉ᶜ r′ Δ′₂ᶜ s′
           → ConvImp W₂ᶜ s s′ → ConvImp W⋉ᶜ r r′)
      -- the inner pair's conversions
      × (∀ {Δ₁ᶜ Δ′₁ᶜ} {W₁ᶜ : World Δ₁ᶜ Δ′₁ᶜ}
           → ConversionInterior Wᵢ Θ₁ Θ₁′ W₁ᶜ
           → ∀ {s s′ r r′}
           → SameConv Δ⋉ᶜ r Δ₁ᶜ s → SameConv Δ′⋉ᶜ r′ Δ′₁ᶜ s′
           → ConvImp W₁ᶜ s s′ → ConvImp W⋉ᶜ r r′)
```
- **Intent.**  This gives the merged pair's conversion world, and
  carries conversion imprecision along Merge's `SameConv` respellings.
- **Consumers.**  SimBdy, SimBackBdy, CatchupBdy.
- **Plan.**  Build `W⋉ᶜ` from W and the conversion names of `Θ₁ ++ Θ₂`.
  Then induct on the shared spelling.

### M8 `PayloadImp`
```agda
PayloadImp : Set
PayloadImp = ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ R R′}
  → WfWorld W
  → A ⊑ᵂ⟨ W ⟩ A′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → [] ⊢ R ⊑ᴿ⟨ W ⟩ R′
```
- **Intent.**  Imprecise type arguments have imprecise payloads.  The
  `Agree` premise of `ev-2` is `rep-rep` of PayloadImp.  The premise of
  `ev-L⇔` is its instance at `A′ = ★` (`same-★`), which also gives
  "★ is top" for these payloads.
- **Consumers.**  The matched TyBeta (TyBetaSync2: SimTyBeta,
  SimBackTyBeta) and the left TyBeta (TyBetaCatchUpᴸ: SimTyBeta).
- **Plan.**  Induction on `A ⊑ᵂ A′` with `A ~ R`.  A joined name's rep.
  vars are paired (`Joint`), which gives `α⊑β`.  An X⊑★ name against ★
  gives `α⊑★`.

### M9 `RunReplay`
```agda
RunReplay : Set
RunReplay = ∀ {Δ : Ctxᵗ} {M N : Term} (xs : List Alloc)
  → (r : Δ ⊢ M -→* N)
  → Σ[ r₁ ∈ applyˢ xs Δ ⊢ ↑ᴹ*[ xs ] M
              -→* renᴹᴿ (extN (nnew (allocs r)) (nnew xs +_)) N ]
      (allocs r₁ ≡ replayAllocs (nnew xs) zero (allocs r))
```
- **Intent.**  A run replays when extra rep. vars are allocated below
  it.
- **Consumers.**  The `·₂` frames of Sim and SimBack.
- **Plan.**  Induction on the run, with a one-step lemma: every rule
  commutes with a rep. var renaming (`renᴹᴿ`, `renᴮᴿ`, TyBeta's `~`).
  It may need `WfCtx`.

### M10 `EvolveReplay`
```agda
EvolveReplay : Set
EvolveReplay = ∀ {Δ Δ′} {W : World Δ Δ′} {xs xs′ ys ys′ : List Alloc}
    {W₁ : World (applyˢ xs Δ) (applyˢ xs′ Δ′)}
    {W₂ : World (applyˢ ys Δ) (applyˢ ys′ Δ′)}
  → W ⟿[ xs ∣ xs′ ] W₁
  → W ⟿[ ys ∣ ys′ ] W₂
  → Σ[ W₃ ∈ World (applyˢ (replayAllocs (nnew xs) zero ys) (applyˢ xs Δ))
                  (applyˢ (replayAllocs (nnew xs′) zero ys′)
                          (applyˢ xs′ Δ′)) ]
      (W₁ ⟿[ replayAllocs (nnew xs) zero ys
           ∣ replayAllocs (nnew xs′) zero ys′ ] W₃)
      × WorldMor (extN (nnew ys) (nnew xs +_))
                 (extN (nnew ys′) (nnew xs′ +_)) W₂ W₃
```
- **Intent.**  Two evolutions from one world commute.  The second
  replays after the first, and its world embeds by a morphism.  A29 is
  the instance `xs = []`, and A30 the instance `xs′ = []`.
- **Consumers.**  The `·₂` frames of Sim (A29) and SimBack (A30).
- **Plan.**  Induction on the second evolution.  Each recorded payload
  and `Agree` shifts by `⊑ᴿ-ren`.

## 3. Substitution, instantiation, merge

### M11 `SubstImp`
```agda
SubstImp : Set
SubstImp = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {γ γ₁ : CtxImp W}
    {σ σ′ : Var → Img} {N N′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → (∀ {x e} → γ ∋ʷ x ⦂ e → ImgImp γ₁ (σ x) (σ′ x) e)
  → W ∣ γ ⊢ N ⊑ N′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ γ₁ ⊢ substᵐ σ N ⊑ substᵐ σ′ N′ ∶ q)
```
- **Intent.**  Related images substituted into related terms stay
  related.
- **Consumers.**  Through SubstImpBeta: SimApp and SimBackApp (Beta).
  It is a real induction (drafts/SubstImpProof).
- **Plan.**  Induction on `⊑`.  It uses MorImp for `crossΛᴹ`, and
  WeakenClosedImp and ClosedSubstFixed as private helpers.

### M12 `InstXImp2`
```agda
InstXImp2 : Set
InstXImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V V′ N N′ : Term}
    {C C′ : Ty} {m : VarImp} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → C ⊑ᵂ⟨ W ⊕ m ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m′ ] Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ m′ ⟩ C′ ] (W ⊕ m′ ∣ [] ⊢ N ⊑ N′ ∶ q)
```
- **Intent.**  When the binders correspond, both InstX images are
  related at the `Λ⊑Λ` world.
- **Consumers.**  The matched TyBeta (SimTyBeta, SimBackTyBeta).  Inst
  (InstSyncᴳ: CatchupCast, SimBackCast).
- **Plan.**  Induction on `⊑`, with `InstX` inverted
  (drafts/InstXImpProof).  14 holes are open (Q3).

### M13 `InstXImpL`
```agda
InstXImpL : Set
InstXImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V N M′ : Term}
    {C B′ : Ty} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
  → WfWorld W
  → C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′
  → Value V → InstX V N
  → W ∣ [] ⊢ V ⊑ M′ ∶ r
  → (Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′ ] (W ⊕ᴸ ∣ [] ⊢ N ⊑ M′ ∶ q))
    ⊎ (∃[ β ] (Δ′ ∋rep β := ★) × (names Δ′ ∌ʳ β)
        × Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ᴸ⇔ β ⟩ B′ ] (W ⊕ᴸ⇔ β ∣ [] ⊢ N ⊑ M′ ∶ q))
```
- **Intent.**  The left alone instantiates.  The second outcome,
  `W ⊕ᴸ⇔ β`, comes from an opening found under the right spine.
- **Consumers.**  The left TyBeta (SimTyBeta at `ν⊑`).  It is a real
  induction.
- **Plan.**  Induction on `⊑`.  An opened `⊑⟪⟫` gives the second
  outcome, with its mark raised by MorImp.  `Λ⊑Λ` is still open
  (`MISFIT`).

### M14 `MergeImp`
```agda
MergeImp : Set
MergeImp =
  -- both sides compose
  (∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
      {c₁ c₂ c₁′ c₂′ : Conv} {A B C A′ B′ C′ : Ty}
    → WfWorld W
    → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
    → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₁ c₁′ → ConvImp W c₂ c₂′
    → ConvImp W (Δ ⊢ c₁ ⨟ c₂) (Δ′ ⊢ c₁′ ⨟ c₂′))
  -- the left alone composes
  × (∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
      {c₁ c₂ c₂′ : Conv} {A B C A′ C′ : Ty}
    → WfWorld W
    → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ′ ⊢ c₂′ ∶ A′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → B ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₂ c₂′
    → ConvImp W (Δ ⊢ c₁ ⨟ c₂) c₂′)
  -- the right alone composes
  × (∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
      {c₂ c₁′ c₂′ : Conv} {A C A′ B′ C′ : Ty}
    → WfWorld W
    → Δ ⊢ c₂ ∶ A ⇝ C → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W ⟩ B′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₂ c₂′
    → ConvImp W c₂ (Δ′ ⊢ c₁′ ⨟ c₂′))
```
- **Intent.**  `⨟` preserves conversion imprecision when both sides
  merge, the left alone merges, or the right alone merges.  The three
  are one mutual induction, so they are one statement.
- **Consumers.**  SimBdy (both, left), SimBackBdy (both, right),
  CatchupBdy (right).
- **Plan.**  Mutual induction following `⨟` (drafts/MergeImpProof).
  6 `MIXED` cases are open, and the left-only conjunct needs
  `rep(X) ⊑ A′`.

### M15 `RightMergeOpens`
```agda
RightMergeOpens : Set
RightMergeOpens = ∀ {Δ Δ′ Δ′ᵢ Δ⁺} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {Θ₁′ Θ₂′ M M₀ U′ t₁′ A A₀ A′ᵢ}
    {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′ᵢ}
  → WfWorld W
  → Interior W [] Θ₂′ Wᵢ
  → Opens Θ₂′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ⁺
  → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ U′ ⟪ Θ₁′ , t₁′ ⟫ ∶ r
  → ∃[ Δ″ ] Σ[ Wₘ ∈ World Δ Δ″ ] Σ[ Wₘ⁺ ∈ World Δ⁺ Δ″ ]
      Interior W [] (Θ₁′ ++ Θ₂′) Wₘ
      × Opens (Θ₁′ ++ Θ₂′) Wₘ M A Wₘ⁺ M₀ A₀ × WfWorld Wₘ⁺
      × ∃[ A″ ] Σ[ r′ ∈ A₀ ⊑ᵂ⟨ Wₘ⁺ ⟩ A″ ] (Wₘ⁺ ∣ [] ⊢ M₀ ⊑ U′ ∶ r′)
```
- **Intent.**  The right merges under a right-only outer boundary, and
  the openings stay.
- **Consumers.**  SimBackBdy and CatchupBdy (`⊑⟪⟫` × Merge).
- **Plan.**  InteriorMerge for the merged interior, and an induction on
  `Opens` through Θ₁′.  An inner `⟪⟫⊑⟪⟫` becomes `⟪⟫⊑`, and an inner
  `⊑⟪⟫` is unwrapped.

## 4. Redex lemmas of Sim and SimBack

A redex lemma takes the whole derivation and a head step: the step's
immediate subterms are values.  This excludes the congruences and the
blame propagations, which are the IH and INLINE glue.

### M16 `SimApp`
```agda
SimApp : Set
SimApp = ∀ {Δ Δ′} {W : World Δ Δ′} {L M M′ N A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ L · M ⊑ M′ ∶ p
  → Value L → Value M
  → Δ ⊢ L · M -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N
```
- **Intent.**  The left's Beta, Wrap or CastFun is simulated.
- **Consumers.**  `·⊑·` × Beta, Wrap, CastFun (3 holes).  Each case
  needs an induction on the right function value's wrappers.
- **Plan.**  CatchupRight brings the function and the argument to
  values.  Induct on the right function's casts and boundaries, which
  the right peels by CastFun and Wrap, with the argument caught up each
  time.  At the λ, SubstImpBeta.

### M17 `SimCast`
```agda
SimCast : Set
SimCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ N μ c A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ c ⟩ ⊑ M′ ∶ p
  → Value V
  → Δ ⊢ V ⟨ μ ∣ c ⟩ -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N
```
- **Intent.**  The left's cast redex is simulated: CastId, CastSeq,
  CastSeq?, Inst and TagUntag, and also the blaming ones.
- **Consumers.**  `cast⊑cast` and `cast⊑` × 5 steps (10 holes).
- **Plan.**  For `cast⊑`, the right stays and the left wrapper is
  rebuilt.  For `cast⊑cast`, CatchupRight on the premise, then the
  right's matching step.  Inst rebuilds `ν⊑ν` or `ν⊑` at ★.

### M18 `SimBdy`
```agda
SimBdy : Set
SimBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ N Θ c A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ p
  → Value M
  → Δ ⊢ M ⟪ Θ , c ⟫ -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N
```
- **Intent.**  The left's boundary redex is simulated: Merge, Id, IdDyn
  and IdDyn-var.
- **Consumers.**  `⟪⟫⊑⟪⟫` and `⟪⟫⊑` × 4 steps (8 holes).
- **Plan.**  CatchupRight inside, then the right's matching step, or
  `⟪⟫⊑` is peeled.  Merge uses InteriorMerge, MergeConvWorld and
  MergeImp.

### M19 `SimBackApp`
```agda
SimBackApp : Set
SimBackApp = ∀ {Δ Δ′} {W : World Δ Δ′} {M L′ M′ N′ A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ L′ · M′ ∶ p
  → Value L′ → Value M′
  → Δ′ ⊢ L′ · M′ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′
```
- **Intent.**  The right's Beta, Wrap or CastFun is matched.
- **Consumers.**  `·⊑·` × 3 steps (3 holes).  It is the mirror of
  SimApp, with the left peeling its wrappers, or blame.
- **Plan.**  CatchupLeft on both parts.  Induct on the left function's
  wrappers, which the left steps away.  At the λ, SubstImpBeta.

### M20 `SimBackCast`
```agda
SimBackCast : Set
SimBackCast = ∀ {Δ Δ′} {W : World Δ Δ′} {M V′ N′ μ c A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V′ ⟨ μ ∣ c ⟩ ∶ p
  → Value V′
  → Δ′ ⊢ V′ ⟨ μ ∣ c ⟩ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′
```
- **Intent.**  The right's cast redex is matched.
- **Consumers.**  `cast⊑cast` and `⊑cast` × 5 steps (10 holes).
- **Plan.**  CatchupLeft on the premise.  Under `⊑cast` the left is
  then a value, and SimBackValue applies.  Under `cast⊑cast` the left
  cast is matched or administrative.  Inst uses InstSyncᴳ.

### M21 `SimBackBdy`
```agda
SimBackBdy : Set
SimBackBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ N′ Θ c A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ⟪ Θ , c ⟫ ∶ p
  → Value M′
  → Δ′ ⊢ M′ ⟪ Θ , c ⟫ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′
```
- **Intent.**  The right's boundary redex is matched, under `⊑⟪⟫` with
  any number of openings.
- **Consumers.**  `⟪⟫⊑⟪⟫` and `⊑⟪⟫` × 4 steps (8 holes).
- **Plan.**  For `⊑⟪⟫`, RightMergeOpens, or the right's step alone.
  For `⟪⟫⊑⟪⟫`, CatchupLeft, then InteriorMerge, MergeConvWorld and
  MergeImp.

### M22 `SimBackBlame`
```agda
SimBackBlame : Set
SimBackBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ blame ℓ ∣ none
  → ∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)
```
- **Intent.**  A right step to blame is matched by a left run to blame.
- **Consumers.**  Every right blame step that the skeleton does not
  close with `catchupBlame` (10 holes).
- **Plan.**  Induction on `⊑`.  Propagations use CatchupBlame on the
  blamed premise (after CatchupLeft on the siblings).  Failing cast
  redexes use the left's catch-up, where CastRedexNoBlame excludes a
  left value.

## 5. CatchupRight

### M23 `CatchupRightᴳ`
```agda
CatchupRightᴳ : Set
CatchupRightᴳ = ∀ {Δ Δ⁺ Δ′ Θ′} {W₀ : World Δ Δ′} {W : World Δ⁺ Δ′}
    {V M M′ A₀ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ⁺ → WfCtx Δ′ → WfWorld W
  → Value V → Opens Θ′ W₀ V A₀ W M A
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → CatchupRightConcl W M M′ A A′
```
- **Intent.**  CatchupRight with the left an Opens image of a value.
  CatchupRight is its zero-opening instance.
- **Consumers.**  CatchupRightProof's `⊑⟪⟫`-with-opening hole, and
  CatchupCast's Inst case (`↺`).
- **Plan.**  The skeleton's cases, by induction, with the measure of
  §0.

### M24 `CatchupCast`
```agda
CatchupCast : Set
CatchupCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → CatchupRightConcl W V (V′ ⟨ μ′ ∣ c′ ⟩) A A′
```
- **Intent.**  The right's outer cast fires against a left value.
- **Consumers.**  The cast frames E2 and E3 (INLINE in CatchupRightᴳ).
- **Plan.**  The measure of §0:
  - inert: `done`;
  - CastId, CastSeq, CastSeq?, TagUntag: `↺`;
  - blame: CastRedexNoBlame;
  - Inst + TyBeta: InstSyncᴳ, then `↺`CatchupRightᴳ, then CatchupBdy,
    then `↺` on `closeᵖ 0 p`.

### M25 `CatchupBdy`
```agda
CatchupBdy : Set
CatchupBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ Θ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟪ Θ′ , c′ ⟫ ∶ p
  → CatchupRightConcl W V (V′ ⟪ Θ′ , c′ ⟫) A A′
```
- **Intent.**  The right's outer boundary fires against a left value.
- **Consumers.**  The boundary frames E6, E7 and E8.
- **Plan.**
  - Merge: MergeImp with InteriorMerge and MergeConvWorld, or
    RightMergeOpens; then `↺`.
  - Id: the left is the same literal.
  - IdDyn: `exitEnv`.

### M26 `CastRedexNoBlame`
```agda
CastRedexNoBlame : Set
CastRedexNoBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′ ℓ}
    {ξ′ : Alloc} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → ¬ (Δ′ ⊢ V′ ⟨ μ′ ∣ c′ ⟩ -→ blame ℓ ∣ ξ′)
```
- **Intent.**  Against a left value, the right's cast redex does not
  blame.
- **Consumers.**  CatchupCast and SimBackBlame.
- **Plan.**  By types: the two grounds agree, and no value has type
  `∀X.X` (NoBotValue).

## 6. INLINE

Old statements now INLINE, and new helpers.  A "consumer" in
parentheses is itself INLINE.

| name | consumer | one-line proof idea |
|---|---|---|
| `castTy-mor`, `nuTy-mor`, `bdyTy-mor`, `wfctx-mor`, `⊢-mor` (new) | MorImp, frames | existing: `coercion-renᴿ`/`coercion-refine`, `⊢renᴿ`'s ν and boundary cases (`ν-boundary-ren`, `interior-ren`, `conversion-ren`), `wfctx-ren`, `⊢refine`, by the `RepMor` constructor |
| `fusionᴹ`, `fusionᴮ` (new) | EvolveImp, frames | `↑ᴹ*[ ξs ] M ≡ renᴹᴿ (nnew ξs +_) M` (and the same for `↑ᴮ*`): induction on ξs with `renᴹᴿ`/`renᴮᴿ` composition, which is missing from proof/TermSubst (routine) |
| `renᴹᴿ-id` (new) | MorImp at `rm-refine` | `renᴹᴿ ρ M ≡ M` for ρ pointwise the identity; induction on M, `extᵗ` congruence |
| `instX-ren` (new) | MorSide (e) | induction on `InstX`; `crossΛᴹ` commutes with `renᴹᴿ` (needs composition) |
| `step-mor`, `mor-∘` (new) | EvolveMor | each evolution step is a morphism (definitional and `repwk-alloc`); morphisms compose |
| A20 InteriorAlloc | EvolveInterior | its step: `toExt (↑ᴮ[ new R ] Θ) = toExt Θ`, `Paired` shifts |
| A22 InteriorLift | InstXImp2, InstXImpL (one module) | field by field; `toExt (liftᴮ Θ) (suc X)` |
| A25 WfOpens | (InstSyncᴳ) | one opening only: the existing `wf-⊕⁺`; `NoNamedPartner` of the fresh rep. var 0 of `allocᴿ ★ W` is vacuous |
| A26 OpensEvolveᴿ | (CatchupFrame-⊑⟪⟫) | induction on `Opens`; allocations renumber rep. vars, not names |
| A29, A30 | (·₂ frames) | EvolveReplay at `xs = []` / `xs′ = []`; `replayAllocs 0 0 ys ≡ ys` by `renameᵗ-cong`, `renameᵗ-id` |
| B2 SubstImpBeta | SimApp, SimBackApp | SubstImp at the one-image environment (complete in the draft) |
| B3 WeakenClosedImp | SubstImp | routine induction on `⊑`; `blame⊑` by `⊢weakenⁿ` |
| B4 ClosedSubstFixed | SubstImp | induction on the typing; `substᵐ` stops at boundaries |
| B7 InstXImpOpenR | InstXImp2 (`Λ⊑`) | induction on the right's `InstX` |
| B9 InstXImp⁺ | (InstSyncᴳ) | InstXImp2, then MorImp at `rm-refine` on the right |
| B10 NuBdyConvImp | (TyBetaSync2) | `underν²`'s conversion world is `alloc²`'s at `inst []`: the same names, conversions untouched |
| B11 TyBetaSync2 | (SimTyBeta), (SimBackTyBeta) | InstXImp2; MorImp (refine into `alloc²`'s interior); B10; rebuild `⟪⟫⊑⟪⟫`; `ev-2` with PayloadImp |
| B12 TyBetaCatchUpᴸ | (SimTyBeta) | the premise from `r`; InstXImpL; MorImp (refine); rebuild `⟪⟫⊑`; `ev-L` or `ev-L⇔` with PayloadImp |
| B13 InstSyncᴳ | CatchupCast, SimBackCast | B9, `open-⊕`, `wf-⊕⁺`, rebuild `⊑⟪⟫` |
| C3 SimTyBeta | Sim (2 holes) | `ν⊑ν`: CatchupRight, the right's TyBeta, B11; `ν⊑`: B12 |
| C14 SimCast-ToBlame | Sim (14 holes) | `blame⊑` with the right typing from ImprecisionTyping, `r′ = done` |
| C15–C24 Sim frames | Sim (1 hole each) | lift the IH's run (RunFrames; `ξ-·₁*`, `ξ-·₂*` to add); side premises by EvolveMor, MorSide and the `*-mor` helpers; interiors by EvolveInterior; ·₁ moves the sibling by EvolveImp; ·₂ uses RunReplay, EvolveReplay, MorImp |
| D3 SimBackTyBeta | SimBack (1 hole) | CatchupLeft (or blame), the left's TyBeta, B11 |
| D15–D25 SimBack frames | SimBack (1 hole each) | as C15–C24; D22 is `unliftᴸ` and EvolveImp, as in CatchupRightProof's `Λ⊑` |
| D26 SimBackValue | SimBack (2 clauses) | proved (notes/M2ChildStatements): CatchupRight, Determinism, Irreducible |
| E2, E3 CatchupFrame-cast, -⊑cast | CatchupRightᴳ | rebuild at the IH's world (EvolveMor, MorSide (a), `castTy-mor`), then CatchupCast; concatenate the runs |
| E6, E7 CatchupFrame-⟪⟫, -⟪⟫⊑ | CatchupRightᴳ | EvolveInterior, MorSide (c) or `bdyTy-mor`, rebuild, then CatchupBdy |
| E8 CatchupFrame-⊑⟪⟫ | CatchupRightᴳ (2 holes) | A26, EvolveInterior, rebuild `⊑⟪⟫`, then CatchupBdy |

## 7. Fate of the 108

| old | fate |
|---|---|
| A1 AllocImp | MAJOR MorImp (`rm-ren`) |
| A2–A5 AllocImpL, R, 2, L⇔ | dropped: EvolveImp is EvolveMor + MorImp (checked); each is MorImp at a one-step EvolveMor if wanted |
| A6 InteriorRen | MorSide (b) |
| A7 OpensRen | MorSide (e) |
| A8 NuConvImpRen | MorSide (d) |
| A9 BdyConvImpRen | MorSide (c) |
| A10 WfWorld-⊕, A11 WfWorld-⊕ᴸ | MAJOR WfWorld-bind |
| A12 WfWorld-evolve | EvolveMor, second conjunct (checked) |
| A13 ⊑ᵂ-evolve | corollary: MorSide (a) ∘ EvolveMor (checked) |
| A14 CastTy-evolve | corollary: `castTy-mor` at EvolveMor's sides (checked) |
| A15 NuTy-evolve | corollary: `nuTy-mor` (checked) |
| A16 BdyTy-evolve | corollary: `bdyTy-mor`, `fusionᴮ`, `interior-functional` |
| A17 BdyConversionImp-evolve | corollary: MorSide (c), `fusionᴮ` |
| A18 NuConversionImp-evolve | corollary: MorSide (d) (checked) |
| A19 WfCtx-evolve | corollary: `wfctx-mor` (checked) |
| A20 InteriorAlloc | INLINE (EvolveInterior) |
| A21 EvolveInterior | MAJOR EvolveInterior |
| A22 InteriorLift | INLINE (InstX module) |
| A23 InteriorMerge | MAJOR InteriorMerge |
| A24 MergeConvWorld | MAJOR MergeConvWorld |
| A25 WfOpens | INLINE (`wf-⊕⁺`) |
| A26 OpensEvolveᴿ | INLINE (E8) |
| A27 MarkMono | MorImp (`mor-μ`) |
| A28 RunReplay | MAJOR RunReplay |
| A29 EvolveReplayᴿ, A30 EvolveReplayᴸ | MAJOR EvolveReplay (two-sided) |
| A31 PayloadAgree2, A32 PayloadAgreeᴸ⇔ | MAJOR PayloadImp |
| B1 SubstImp | MAJOR SubstImp |
| B2 SubstImpBeta | INLINE |
| B3 WeakenClosedImp, B4 ClosedSubstFixed | INLINE (SubstImp) |
| B5 InstXImp2 | MAJOR InstXImp2 |
| B6 InstXImpL | MAJOR InstXImpL |
| B7 InstXImpOpenR | INLINE (InstXImp2) |
| B8 RefineImp | MorImp (`rm-refine`) |
| B9 InstXImp⁺, B10 NuBdyConvImp, B11 TyBetaSync2, B12 TyBetaCatchUpᴸ, B13 InstSyncᴳ | INLINE |
| B14 MergeImp2, B15 MergeImpL, B16 MergeImpR | MAJOR MergeImp |
| B17 RightMergeOpens | MAJOR RightMergeOpens |
| C1 SimBeta-Beta, C2 SimBeta-Wrap, C11 SimCast-CastFun | MAJOR SimApp (checked adapters) |
| C3 SimTyBeta | INLINE |
| C4 SimBoundary-Merge, C5 -Id, C6 -IdDyn, C7 -IdDynVar | MAJOR SimBdy (checked adapters) |
| C8 SimCast-CastId, C9 -CastSeq, C10 -CastSeq?, C12 -Inst, C13 -TagUntag | MAJOR SimCast (checked adapters) |
| C14 SimCast-ToBlame | INLINE |
| C15–C24 SimFrame-* | INLINE |
| D1 SimBackBeta-Beta, D2 SimBackBeta-Wrap, D11 SimBackCast-CastFun | MAJOR SimBackApp (checked adapters) |
| D3 SimBackTyBeta | INLINE |
| D4 SimBackBoundary-Merge, D5 -Id, D6 -IdDyn, D7 -IdDynVar | MAJOR SimBackBdy (checked adapters) |
| D8 SimBackCast-CastId, D9 -CastSeq, D10 -CastSeq?, D12 -Inst, D13 -TagUntag | MAJOR SimBackCast (checked adapters) |
| D14 SimBackCast-ToBlame | MAJOR SimBackBlame |
| D15–D25 SimBackFrame-* | INLINE |
| D26 SimBackValue | INLINE (proved) |
| E1 CatchupRightᴳ | MAJOR CatchupRightᴳ |
| E2, E3, E6, E7, E8 CatchupFrame-* | INLINE |
| E4 CatchupCast | MAJOR CatchupCast |
| E5 CastRedexNoBlame | MAJOR CastRedexNoBlame |
| E9 CatchupBdy | MAJOR CatchupBdy |

## 8. Questions for the reviewer

1. **SimBack with a left value.**  Do you approve SimBackValue (D26,
   INLINE, proved) for the two `⊑⟪⟫`-with-opening clauses?  Each needs
   a clause change in SimBackProof (§1).  It adds the edge
   SimBack → CatchupRight.  Should `Λ⊑` also go through it?  That would
   drop SimBackFrame-Λ⊑ and that use of WfWorld-bind.
2. **CatchupRight's induction.**  Should CatchupRightᴳ become the Def
   that is proved, with CatchupRight as its zero-opening corollary?
3. **Binder correspondence for InstX.**  InstXImp2 and InstXImpL take
   it as a type premise.  It is not inherited under a cast or a
   one-sided boundary (5 holes), and mixed layers need forms that are
   not stated (5 holes).  Should we keep the premises and add the
   missing forms, or carry the correspondence in the relation?
4. **The left's TyBeta against an opening.**  Do you accept
   InstXImpL's second outcome `W ⊕ᴸ⇔ β`, with its mark raised by
   MorImp (formerly MarkMono), in place of OpenCatchUp?
5. **The catch-up measure.**  Do you accept the lexicographic measure
   of §0 for CatchupRightᴳ, CatchupCast and CatchupBdy as one
   well-founded induction?
6. **(new) One world morphism.**  APPROVED by Jeremy, 2026-10-04.  Do you accept `WorldMor` as the
   single transport, in place of `WorldRen`, `WorldRefine` and
   `MarksRaised`?  It covers renaming, refinement and raised marks.
   Do you also accept the merge of the redex children by redex kind
   (SimApp, SimCast, SimBdy and their mirrors)?
