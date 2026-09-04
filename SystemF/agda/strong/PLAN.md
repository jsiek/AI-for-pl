# Strong System F — handoff plan (finishing preservation & progress)

Status as of the `strong-preservation` branch (PR #189), **2026-09-04, evening (x-license
install IN FLIGHT)**. This document is the authoritative handoff. The DESIGN LOG lives in
`notes/DECISIONS.md` (decisions as definitions, examples, probe verdicts) and
`notes/DualLicenseDesign.md` (the dual-conceal license, fully ruled); this file carries the
state, the settled design, and the roadmap (§9).

**Landed 2026-09-04**: grounded knowledge interiors `⟦A⟧`; the rep-less abstract reveal
`rvl⋆`; the reversal-form conceal premise; Γ-indexed reduction with the ambient dual
`dualᴳ`; the telescopic reveal block was landed and then REVERTED the same day
(simultaneity ruling — reveal reps are read in the PLAIN exterior). `make -C strong check`
is green; the residue is three `DualDef` parameters plus the four `ProgressDef` ones,
both targeted by the in-flight install (§9 step 0).

## 0. What "Strong System F" is

System F with **reveal/conceal boundary wrappers** giving tight control over where
type variables appear. A term `M ⟪ Θ , B₀ ⟫` wraps `M` in a boundary `Θ` (a list
of reveals/conceals) recording a single **boundary type** `B₀`; the internal and
external types are its two projections. The type system must **accept every System
F source term** (source has no wrappers — wrappers only arise from reduction), so
no change may reject valid source.

Design invariant (user's dual semantics):
- **reveal `X:=A`**: `X` is a fresh **internal** abstract var; rep `A` is **external** to the whole boundary.
- **conceal `Y:=A`**: `Y` is an **external** var; rep `A` is **internal** to the whole boundary.

## 1. Current state (files under `SystemF/agda/strong/`)

**Method (the rhythm of this development).** Reduction rules are added ONE AT A
TIME. For each rule: (i) add the constructor to `_-→_`; (ii) a worked example — a
well-typed redex, the step, and the well-typed contractum at the same type;
(iii) its `preservation` case; (iv) its `progress` case. The goal is a rule set
rich enough that `progress` goes through (§5). The old design's `Reduction.agda`
rule shapes are guidance only and may change considerably.

| file | role | status |
|---|---|---|
| `Boundary.agda` | boundary syntax, projections, scope machinery, typing (`_∣_⊢_⦂_`, `env`) | ✅ 0 holes |
| `BReduction.agda` | values, `_⊢_-→_` (TyBeta, Beta, TyWrap, Wrap, ξ-·-l, ξ-·-r, ξ-·[], ξ-Λ, ξ-⟪⟫), `dualᴳ`, type-var renaming through boundaries, `⊢renameᵀ`, the ⟦·⟧-transport chain, shift/dual boundary lemmas, `_≼_`/`⊢retag` | ✅ 0 holes |
| `ScopeBridge.agda` | `⊢ty-wf`, `wf→Scoped`, `env-ext-wf`, `scB-bridge` (§3b) | ✅ 0 holes |
| `TermSubst.agda` | `⊢renameᵀᵐ`, `⊢substᵀᵐ`, `⊢[]ᵐ`, `preserve-Beta` (§3c) | ✅ 0 holes |
| `BPreservation.agda` | `module Impl (dual-rep dual-cnc dual-int)`: `preservation : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A`, all current rules | ✅ 0 holes |
| `Canonical.agda` | canonical forms `canon-ℕ/⇒/∀`, `canon-var`, `Value-renameᵀ` (§5; 5 of 6 ground by REALLMS) | ✅ 0 holes |
| `DualDef.agda` | the ambient dual's well-formedness: `repOf-wf`, `dual-rep-conc`, `bwf-dualᴳ` PROVEN; `DualRep`, `DualCnc`, `DualInt` stated (the (R2) residue) | ✅ 0 holes |
| `ProgressDef.agda`, `Progress.agda` | `progress` for all rules over `Δ ⊢ M -→ M′`; module `Impl` is parameterised over the four cases stated in `ProgressDef` (`RevealVarApp`, `RevealVarTApp`, `NestedApp`, `NestedTApp`), to be instantiated once Merge lands | ✅ 0 holes |
| `All.agda` | aggregate driver — now points at the NEW design | ✅ |
| `notes/BoundaryRules.md`, `notes/DECISIONS.md` | §4 rule design memo; the decision record (1–4) with the (R1)/(R2) residues | ✅ |
| `notes/old/*Probe.agda`, `notes/old/Example8Trace.agda` | the design-path probes (Grounded, Reversal, Merge, AmbientDual, BoundaryRules, Example 8). **Superseded 2026-09-04; they do NOT compile against the current core** and are kept only as a record — their surviving content is now in `Boundary.agda`/`BReduction.agda` | 📄 record |
| `ScratchGamma.agda`, `ScratchBlocked.agda` | evidence for the two design findings (§2) | ✅ |
| `notes/old/Scratch7/8/9.agda` | machine-checked unsoundness of the OLD design (Example 8) | ✅ keep |

**Preservation is closed** for the current relation modulo the three `DualDef`
parameters, and **`make check` passes** (2026-09-04, post-install): the old design and the
design-path probes live under `notes/old/`, and the open cases are module parameters
(`DualDef`, `ProgressDef`) — no holes, no postulates anywhere under `strong/`.

## 1b. OLD design (DISCARDED) vs NEW design — read this first

Two designs coexist in this directory. **Do not build new work on the old one.**

### NEW design (boundary wrapper `M ⟪ Θ , B₀ ⟫`) — the one to finish
- `Boundary.agda` — redefines `Term`, values, typing (`_∣_⊢_⦂_`, `env`), boundary syntax, projections, scope machinery.
- `BReduction.agda` — reduction `_-→_`, renaming/subst through boundaries, `⊢renameᵀ`, `preservation`.
- `ScratchGamma.agda`, `ScratchBlocked.agda` — evidence for the two new-design findings (§2).

### SHARED substrate (keep — imported by BOTH designs)
- `Types.agda` (type syntax), `TypeSubst.agda` (type subst/renaming, `subst-cong`, …),
  `Context.agda` (`TCtx`, wf `_⊢_`, `_∋tv_`, `_↓_`, `abst`/`rvld`), `Weakening.agda`
  (`wf-rename-fv`, `fv-scope`).

### OLD design (per-variable `↑`/`↓` wrappers) — DISCARDED, do not extend
- `notes/old/Terms.agda` — old term syntax with **separate** reveal `_↑[_,_]` and conceal `_↓[_,_,_]` constructors (one wrapper per single reveal/conceal).
- `notes/old/Typing.agda` — old typing (`TyWrapRevl`/`TyWrapCncl`, the tightened-conceal-marker rules).
- `notes/old/Reduction.agda` — old reduction: `β-↑` (WrapReveal), `β-↓·` (WrapConceal), `β-cancel`, `β-drop`, `β-↑[]` (TyWrapRevl), `β-↓[]` (TyWrapCncl), `ξ-*`.
- old `Examples.agda`, `Preservation.agda` — DELETED (2026-09-04; unreferenced, the latter had 8 holes).
- `All.agda` — drives the NEW design.
- `notes/old/Scratch7/8/9.agda` — keep, but note they **import the old `Terms`/`Typing`/`Reduction` (also under `notes/old/`)**: they are the machine-checked proof that the old design is unsound. This is the *only* reason the old files are retained.

### Why the old design was discarded (Example 8)
The old design made each reveal/conceal a **separate per-variable wrapper**, with
`TyWrapCncl` pushing a conceal inward under a `Λ` (conceal-of-a-value is a value).
This is **unsound**: a conceal `↓[X:=A]` whose body, once the context is tightened
to `X`'s existential scope, references a **shallower** type variable that thereby
falls out of scope. `notes/old/Scratch7/8/9.agda` exhibit a closed, well-typed source program
`P : ∀(Z→Z)` that reduces in 4 steps (via `β-↓[]`) to an **ill-typed** term — a
direct counterexample to preservation.

The fix is structural, not a patch: replace the separate `↑`/`↓` wrappers with a
**single combined boundary** `⟪ Θ , B₀ ⟫` in which multiple reveals and conceals
coexist simultaneously, so a reveal's fresh variable stays visible to a conceal's
body instead of being blocked — while genuinely-inaccessible variables are blocked
(and forbidden in `B₀` by the scope premise, §2). Because reveals and conceals live
on one boundary, **no `Commute` rule is needed**. The old `Reduction.agda` rule
shapes (WrapReveal/WrapConceal/Cancel/Drop) remain a useful *reference* for the
boundary-manipulation rules to add in §4, but must be reformulated for the combined
boundary — do not copy them verbatim.

## 2. Settled design (do not relitigate)

- **Delta-indexed boundary.** `BEntry = rvl (A : Ty) | rvl⋆ | cnc (X : ℕ) (A : Ty)`; `BCtx = List BEntry`. Reveal rep `A` over the **plain exterior `Γ`** — SIMULTANEOUS, no interference from sibling entries (the telescopic reading was tried and reverted); `rvl⋆` is the rep-less abstract reveal; the in-flight install adds `cnc⋆` (rep-less conceal) and the context entry `X:=ˣA`; conceal index `X` a whole-`Γ` de Bruijn index, rep `A` over the interior.
- **B₀ typing (`env`), not a consistency premise.** Record one boundary type `B₀`; derive both faces: internal `= substᵗ (γᵇ Θ) B₀`, external `= substᵗ (ρᵇ Θ) B₀`. No `τ(A)=σ(B)` premise.
- **Whole-`Γ` tight interior, with KNOWLEDGE.** `intOf Γ Θ = revEnts Θ 0 Θ ++ dropN (cmax Θ) Γ` — the reveal block's entries prepended over "everything deeper than the deepest conceal" (`cmax = 1 + max conceal index`). This is the **Example-8 soundness fix**: variables shallower than the deepest conceal are intentionally **blocked** (inaccessible in the interior). Conceal indices are whole-`Γ`-relative → renaming is uniform.
- **Projections.** `ρᵇ` (reveal-resolve): reveal var ↦ its rep AS STORED (a lookup — parallel/simultaneous), `rvl⋆` ↦ a dummy (never nameable, its slot is `blk`), others pass through. `γᵇ Θ = prepId (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ)`: reveal var passes through, concealed index ↦ its rep (**unshifted** — reps live over the whole interior and may mention reveal vars), kept index ↦ its interior slot `` ` (revs + (i ∸ cmax)) ``.
- **Scope premise on `env`.** `Scoped (baseS Θ Δ) B₀` forbids `B₀` from naming a **blocked** slot. `baseS` marks each bframe slot `ok`/`blk`; `Scoped`/`_∋ok_` is a wf judgment that only accepts `ok` slots (binders push `ok`). `subst-cong-sc` is the scope-restricted `subst-cong` — it needs the pointwise equality only at `ok` slots, which is what makes `γcnc-comm`'s failure at blocked indices irrelevant.

### Settled 2026-09-04 (notes/DECISIONS.md, Decisions 1, 3, 4) — INSTALLED, do not relitigate

- **Grounded knowledge interiors (Decision 1, refined).** A reveal contributes the knowledge
  entry `X:=⟦A⟧`, the interior reading of its rep, read as a TELESCOPE entry. Two total
  guards fall back to `abst`: `bfree` (the rep names a BLOCKED slot) and `dfree` (the reading
  names a reveal slot at or above this one, so it is not a legal telescope entry — this guard
  is what makes the entries stable under renaming, i.e. what makes `⊢renameᵀ` provable).
- **Reversal-form (bwf-↓) (Decision 3's ruling).** `Γ ∋ Y:=A₀`, `Reversal Θ Y A A₀` (the
  conceal's rep read BACK OUT through the whole boundary equals the exterior's knowledge),
  `Ψ ⊢ A`. Comparing on the outside unfolds the boundary's own reveals — Zdancewic's (trans)
  — which is what Merge needs; it also transports under any monotone renaming with no scope
  restriction. `bad`/`bad₂` are refuted in `Boundary.agda`. Boundary well-formedness carries
  the whole `Θ` as a parameter and recurses on a suffix.
- **Parallel (simultaneous) reveal block — the telescope is REVERTED.** `(bwf-↑)` is plain
  `Γ ⊢ A`; `TyWrap` records the type argument UNLIFTED. Design law (Jeremy): "the
  representation type of a reveal entry is well-formed in the external context, without any
  interference from the other entries in the boundary."
- **Design laws (standing, do not relitigate):** grounded invariants (in the relation, no
  companion predicates); TIGHTNESS (tight interiors wanted for their own sake); NO TERM
  SHIFTS (shift types, never terms); SIMULTANEITY (both directions: a conceal's rep may use
  the boundary's reveal variables; a reveal's rep reads in the plain exterior); CLOSURE
  UNDER DUALIZATION (every entry form has a dual image — rvl↔cnc, rvl⋆↔cnc⋆).
- **Γ-indexed reduction and the ambient dual (Decision 4).** `_⊢_-→_ : TCtx → Term → Term →
  Set`; `ξ-⟪⟫` extends by `intOf Δ Θ`, `ξ-Λ` by `abst`, the rest pass Δ through. `Wrap` uses
  `dualᴳ Δ Θ`, which at a slot the boundary drops without concealing COPIES Δ's own entry
  (`rvld B` ⇒ a reveal at B, `abst` ⇒ `rvl⋆`) instead of inventing one. Both of Wrap's face
  laws (`ρᵇ-dual-ty`, `γᵇ-dual-ty`) are theorems; the reps are transported into the dual's
  telescope (`renameᵗ (k +_)` for a conceal rep, `upFrom k (revs Θ)` for a copied one) and the
  dual's conceal block carries the reveal's EXTERNAL FACE, not its raw rep.
- **Typing reads the marker, so `⊢retag` is along `_≼_`.** `abst ≼ anything`, `X:=A ≼ X:=A`;
  the old equal-length retagging is unsound now that a conceal is licensed by knowledge.

### Being installed now (probed, ruled, IN FLIGHT — notes/DualLicenseDesign.md)

- **The unfolding congruence `≈Δ̄`** (`unfoldᵉ` through the context's knowledge; equality of
  unfoldings). Used at exactly the knowledge-COMPARING sites: `(bwf-↓)`'s Reversal becomes
  `Reversal≈`; the new `(bwf-↓x)` compares up to `≈Δ̄` (ruling (ii), for duality); `≼`/⊢retag
  becomes `≼≈`. Reveal reps, conceal reps, faces, terms: never unfolded — nothing is erased.
- **Hybrid interior entries**: raw where expressible → retry at the unfolding → for a
  rep-carrying reveal the EXTERIOR-READ entry `X:=ˣA` (consumed only by `(bwf-↓x)`) → abst.
- **`cnc⋆`** (rep-less conceal, dual image of `rvl⋆`) and the entry-independent dual conceal
  block. **`(bwf-↓x)`** licenses a dual's conceal of an unknowable reveal: `Γ ∋ X:=ˣA`, rep
  equal up to `≈Δ̄`, and the LOAD-BEARING "claims nothing" premise (the rep names only
  abstract interior variables — this is what refutes the ⊢3n-adv adversary).
- Gauntlet: Pn, Pc, E★, E★′ end-to-end; bad/bad₂/far-bad refuted, near-bad admitted;
  ⊢3n-adv under ≈; dual-of-dual round trip. Goal: discharge all three `DualDef` parameters
  (preservation unconditional).

### Two findings that produced the current design (see scratch files)
1. **FIXED** — old `γᵇ = extsⁿ(revs)(γᶜ)` shifted conceal reps by `sucᵛ`, disagreeing with `bwf↓`/`renᴮ` when a rep mentions a reveal var. Now `prepId`/`γcnc`, no shift.
2. **Blocked-var aliasing** — `γᵇ` aliased a blocked var onto a kept var (both → same slot). Resolved by the scope premise (user chose this over a `delAt`-style interior, which would reopen Example 8).

## 3. PRESERVATION — DONE (kept as a record of the lemma architecture)

3a `⊢renameᵀ`'s `env` case: closed. The lemma chain is in `BReduction.agda`:
`Mono→inj`, `Mono-intRen`, `revs-ren`, `⊔-mono-comm`, `cmax-ren` (a `CmaxV` view),
`liftⁿ-lo/hi`, `prepId-lo/hi`, `split`, the `baseS`/`slotAt` accessibility bridge
(both directions), `γcnc-comm` / `γᵇ-comm-ok` / `C-int` (via `subst-cong-sc`),
`h-int` (`dropN-↓` is NOT definitional for abstract Δ), `bwf-ren`, `sc-ren`.
Two corrections to the original plan: conceal reps rename by `intRen ρ Θ`, not
`deepRen`; the concealed case of `γcnc-comm` needs `Mono→inj`.

3b `scB`: closed by `ScopeBridge.scB-bridge` (`⊢ty-wf` needs `Δ ⊢* Γₜ`, discharged
by `⊢[]` since the Λ body is at `⤊ [] = []`). `env`'s `Scoped` premise is what
makes the external face's well-formedness derivable (`env-ext-wf`).

3c `Beta`: closed by `TermSubst.preserve-Beta` (`⊢substᵀᵐ`'s Λ case is `⊢renameᵀ`
at `suc` with `Mono-suc`; `⤊ Γ = map ⇑ᵗ Γ` is definitional).

## 4. Complete the REDUCTION relation (one rule at a time — see §1 Method)

Done: `TyBeta`, `Beta`, and the congruences `ξ-·-l`, `ξ-·-r` (CBV, left to right),
`ξ-·[]`, `ξ-Λ` (Λ V is a value only when V is), `ξ-⟪⟫` (reduce under a boundary;
its preservation case is why `preservation` is generalised over Δ).

Boundary-manipulation rules — proposed in `notes/BoundaryRules.md` (all typing
machine-checked in `notes/BoundaryRulesProbe.agda`), in order of adoption:

- **`TyWrap`** (landed; REVISED 2026-09-04 to the direct-combine form — Decision 2):
  `((Λ V) ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ] -→ V ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫`.
  Consumes the Λ (its binder slot IS the new reveal slot), so NO ⇑ᵀ on the
  term — the no-term-shift principle; conceal reps still shift (types).
  Face laws: `γᵇ-shift` (every slot), `ρᵇ-shift-ty`, `bwf-shift`, `baseS-shift`.
  Never pushes `A` inward — Example 8 avoided by construction.  A wrapper-
  bodied wrapper at a ∀ face waits for Merge (ProgressDef.NestedTApp).
- **`Wrap`** (R2, landed; REVISED 2026-09-04 to push-through + the AMBIENT dual — Decision 4):
  `Δ ⊢ ((ƛ A′ ∙ N) ⟪ Θ , B₁ ⇒ B₂ ⟫) · W -→ (N [ W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ]ᵐ) ⟪ Θ , B₂ ⟫`
  — consumes the ƛ and β-substitutes the dual-wrapped argument in one step.
  A wrapper-bodied wrapper at a ⇒ face waits for Merge (ProgressDef.NestedApp).
  The dual now COPIES the ambient context's entry at every dropped-but-unconcealed
  slot, so no knowledge is lost and no term traversal is needed (Decision 4's
  programs P and E, notes.md Examples 9 and 10); a Λ-bound slot comes back via the
  rep-less `rvl⋆`. Blocked slots still make the two faces differ, so R2's
  preservation still goes through `subst-cong-sc`.
  **Outstanding:** the dual's well-formedness and its rebuild law — `DualRep`,
  `DualCnc`, `DualInt` in `DualDef.agda`. `bwf-dualᴳ` proves everything else, and
  the concealed / Λ-bound slots of the reveal block are proven outright.
- **Merge is now load-bearing** (Decision 3, notes/DECISIONS.md): the revised
  TyWrap/Wrap are partial on wrapper-bodied wrappers, and notes.md Examples 1/3
  hit that mid-trace.  Progress carries four ProgressDef parameters until the
  reversal-form rework and Merge land.  `Canonical.Value-renameᵀ` is currently
  unused (its consumer was the old TyWrap's ⇑ᵀ) — keep until Merge/W3 decide.

**Decision 1 is CLOSED** (2026-09-04): `bad` and `bad₂` are now ill typed —
the reversal-form `(bwf-↓)` against the interior's knowledge entry refutes both,
machine-checked in `Boundary.agda` (`¬⊢bad`, `¬Reversal-bad₂`). No companion
predicate; the invariant lives in the relation, as the grounded-invariants law
demands.

**The one design question still open — [R2].** A reveal whose representation names
a slot its OWN boundary blocks (Example 8's run-time `↑Z:=Y , ↓X:=ℕ` with `Y`
Λ-bound) gets an ABSTRACT interior entry, so the dual's conceal of `Z` has nothing
to meet. Neither the ambient dual nor W3 dissolves it; it is structural — "Z is Y"
is not expressible in a context that dropped Y. Candidate resolutions recorded in
notes/DECISIONS.md: (a) Γ-aware knowledge closure in `⟦·⟧`; (b) a conceal premise
licensed by the boundary's own reveal rep; (c) Merge-first normalisation; (d)
forbid such reveal reps in `(bwf-↑)`, which would reject Example 8's T4/T5.
Isolated as `DualDef.DualCnc` (with `DualRep` and `DualInt` alongside).

## 5. PROGRESS (in flight, incremental)

`progress : Δ ∣ [] ⊢ M ⦂ A → Value M ⊎ (Σ Term λ M′ → Δ ⊢ M -→ M′)` — generalised
over Δ (ξ-⟪⟫ recurses into `intOf Δ Θ`, ξ-Λ into `abst ∷ Δ`, and the reduction
relation now carries the same index), term context always `[]`.
- `Canonical.agda`: `canon-ℕ/⇒/∀` (value = numeral/ƛ/Λ or a wrapper),
  `canon-var` (a value of variable type is a wrapper with a variable boundary
  type — a chain ending in a conceal of that variable), `Value-renameᵀ`.
- `cf-∀-B₀` / `cf-⇒-B₀`: a wrapper's `B₀` is `∀`/`⇒`-shaped (R1/R2 fire) or a
  reveal variable.
- **Four parameters remain** (`ProgressDef`), all waiting on Merge (Decision 3):
  `RevealVarApp`/`RevealVarTApp` (the boundary type is a reveal variable — a
  Merge/Cancel against the enclosing boundary) and `NestedApp`/`NestedTApp` (a
  wrapper-bodied wrapper at a ⇒/∀ face). Merge in turn needs "retyping along
  unfolding" (Zdancewic's Δ̄), which under the in-flight
  install collapses into `≼≈` (UpToProbe, both directions). **See the roadmap, §9.**

## 9. ROADMAP — what comes after the in-flight install

0. **[IN FLIGHT] The x-license install** (notes/DualLicenseDesign.md; all rulings taken):
   `≈Δ̄`, hybrid `⟦·⟧` with `X:=ˣA`, `cnc⋆`, `(bwf-↓x)` under (ii), the dual's unfolded
   second-chance copy, `≼≈`; the full gauntlet incl. E★′ and ⊢3n-adv-under-≈; attempt to
   discharge `DualRep`/`DualCnc`/`DualInt` → **preservation unconditional** if all three go.
1. **Merge + Drop∅ in one landing** (Decisions 3 + addendum; both ruled). Port `⊕` from
   notes/old/MergeProbe to the new core; the cancel clause's soundness is the restored
   invariant (`cancel-agree` — an x-conceal cancels the very reveal it was born from);
   retyping-along-unfolding = `≼≈`. Per the §1 Method: rule → example (the cancel pair,
   Example 3's tower, E★′'s continuation) → preservation case → progress case. OPEN
   sub-decision for Jeremy at landing time: the merged wrapper's boundary type (the probe's
   `B₁`-pushed-out form vs the alternative).
2. **Depth-1 values** (Decision 3: a wrapper's body is never a wrapper; Zdancewic's value
   grammar) + the strengthened canonical form `canon-var-conceal` (a value at variable type:
   the variable is revealed — `:=` or `:=ˣ` — and the chain ends in a licensed conceal) +
   `no-abstract-value` where still load-bearing. Then **instantiate `Progress.Impl`**: Merge
   discharges `NestedApp`/`NestedTApp`; Merge-against-the-enclosing-boundary plus the
   canonical form discharge `RevealVarApp`/`RevealVarTApp`. **PROGRESS COMPLETE.**
3. **Top-level `TypeSafety.agda`** per the AGENTS.md maximal-join checklist: `progress` and
   `preservation` stated explicitly at the language's top level as thin wrappers (plus
   multi-step safety), `All.agda`, `make check`.
4. **Deferred general lemmas** (tracked, not blocking): dual-of-dual is the identity on
   x-licensed boundaries (checked on shapes, wants the general theorem); the copied-rep
   fv-lemma (`renameᵗ (n +_)` never hits the dual's own ⋆-slots); `DualRep`'s `⊢ Δ`
   question if any residue survives step 0.
5. **Join-checklist round-out** once safety is closed: `Eval.agda` (step function/fuel
   evaluator over `Δ ⊢ M -→ M′`), a fresh `Examples.agda` for the new calculus (notes.md
   Examples 1–8 mechanized end-to-end, incl. the towers collapsing through Merge/Drop∅),
   README/Design notes; optional cheap win: revive `Cancel` as an optimisation (its side
   condition is exactly what `Reversal` now guarantees).
6. **Research directions after safety** (Jeremy's call, unscheduled): the abstraction
   theorems the calculus was built for (the `barrier-*` bit-identity results are the seed),
   and the Zdancewic correspondence written up properly (notes/Zdancewic-embeddings.md).

## 6. Conventions / gotchas (learned)

- **Constructor names match the rule names in notes.md** (Beta, TyBeta, TyWrap, Wrap, ξ-…); keep notes.md in sync with the Agda (named variables there, de Bruijn here).

- **No `postulate`** — leave `{!!}` holes; `make postulate-check` fails on `postulate`.
- **No `cd`** in Bash — use `agda -v0 strong/File.agda` from `SystemF/agda`, or `make -C`.
- Constructor-form indices, named `with`-cases (not `...`), no catch-all cases in proofs.
- `subst-cong` (in `TypeSubst.agda`) needs **all** indices — that's why `subst-cong-sc` (scope-restricted) exists; use it wherever a per-index equality only holds on accessible slots.
- `prepId`/`slotAt` use `_<?_`/`_≤?_`; these reduce definitionally on closed indices (examples type by `refl`) but need `prepId-lo/hi` lemmas for abstract indices.
- Build each reduction rule → typed example → preservation case, in that order.

## 7. Build

From `SystemF/agda/`: `agda --safe -v0 strong/All.agda` (or `make -C strong agda`)
checks the whole NEW design; `make -C strong check` adds `postulate-check`
(no `postulate`/holes/unsafe pragmas anywhere under `strong/`, `notes/old/`
included). `All.agda` drives Types, TypeSubst, Context, Weakening, Boundary,
BReduction, ScopeBridge, TermSubst, **DualDef**, BPreservation, Canonical,
ProgressDef, Progress.

`notes/old/` holds everything that is a RECORD rather than live code: the old
per-variable design (Terms/Typing/Reduction + Scratch7/8/9, the Example-8
unsoundness evidence) and, since 2026-09-04, the six design-path probes
(GroundedProbe, ReversalProbe, MergeProbe, AmbientDualProbe, BoundaryRulesProbe,
Example8Trace). **The probes do not compile against the current core and are not
meant to** — they are the record of how Decisions 1/3/4 were reached; their
surviving content now lives in `Boundary.agda` and `BReduction.agda`. They are
free of `postulate`/holes, so `postulate-check` still passes over them.

## 8. Tooling (2026-09-03)

Opus subagents do the Agda loop; REALLMS (free; `scripts/REALLMS.md`,
`scripts/reallms_holes.py`) grinds lemma-sized holes; the supervisor verifies
every landing with `agda --safe`. Dependents of a holed module: put
`{-# OPTIONS --allow-unsolved-metas #-}` in the IMPORTED module only, or better,
use the repo's `...Def` convention (statement in a `FooDef` module, importer
parameterised over it, instantiated when the proof lands).
