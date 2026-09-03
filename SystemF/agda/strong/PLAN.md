# Strong System F — handoff plan (finishing preservation & progress)

Status as of the `strong-preservation` branch (PR #189), 2026-09-03. This document is the
authoritative handoff: it captures the design that is now settled, exactly what
compiles, and the ordered chain of work to close **preservation** and then
**progress**.

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
| `BReduction.agda` | values, `_-→_` (TyBeta, Beta, TyWrap, Wrap, ξ-·-l, ξ-·-r, ξ-·[], ξ-Λ, ξ-⟪⟫), type-var renaming through boundaries, `⊢renameᵀ`, shift/dual boundary lemmas, `⊢retag` | ✅ 0 holes |
| `ScopeBridge.agda` | `⊢ty-wf`, `wf→Scoped`, `env-ext-wf`, `scB-bridge` (§3b) | ✅ 0 holes |
| `TermSubst.agda` | `⊢renameᵀᵐ`, `⊢substᵀᵐ`, `⊢[]ᵐ`, `preserve-Beta` (§3c) | ✅ 0 holes |
| `BPreservation.agda` | `preservation : Δ ∣ [] ⊢ M ⦂ A → M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A`, all current rules | ✅ 0 holes |
| `Canonical.agda` | canonical-form statements `canon-ℕ/⇒/∀`, `canon-var`, `Value-renameᵀ` (§5) | ⚠️ holes (REALLMS) |
| `Progress.agda` | `progress`, all rules; 2 holes = the reveal-variable boundary-type cases (Decision 1) | ⚠️ 2 holes |
| `All.agda` | aggregate driver — now points at the NEW design | ✅ |
| `notes/BoundaryRules.md`, `notes/BoundaryRulesProbe.agda` | §4 rule design memo + machine-checked probe (R1/R2, dual, `bad`) | ✅ probe checks |
| `ScratchGamma.agda`, `ScratchBlocked.agda` | evidence for the two design findings (§2) | ✅ |
| `notes/Scratch7/8/9.agda` | machine-checked unsoundness of the OLD design (Example 8) | ✅ keep |

**Preservation is closed** for the current relation (`make agda` passes under
`--safe`). `make check` still fails at `postulate-check` only because the OLD
design's `Preservation.agda` has holes — pending the cleanup decision in §7.

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
- `Terms.agda` — old term syntax with **separate** reveal `_↑[_,_]` and conceal `_↓[_,_,_]` constructors (one wrapper per single reveal/conceal).
- `Typing.agda` — old typing (`TyWrapRevl`/`TyWrapCncl`, the tightened-conceal-marker rules).
- `Reduction.agda` — old reduction: `β-↑` (WrapReveal), `β-↓·` (WrapConceal), `β-cancel`, `β-drop`, `β-↑[]` (TyWrapRevl), `β-↓[]` (TyWrapCncl), `ξ-*`.
- `Examples.agda`, `Preservation.agda` — examples/preservation for the old system.
- `All.agda` — the aggregate driver **still points at the old system** (Terms/Typing/Reduction/Examples). Repoint it to the new design once §3's holes close.
- `notes/Scratch7/8/9.agda` — keep, but note they **import the old `Terms`/`Typing`/`Reduction`**: they are the machine-checked proof that the old design is unsound. This is the *only* reason the old files are retained.

### Why the old design was discarded (Example 8)
The old design made each reveal/conceal a **separate per-variable wrapper**, with
`TyWrapCncl` pushing a conceal inward under a `Λ` (conceal-of-a-value is a value).
This is **unsound**: a conceal `↓[X:=A]` whose body, once the context is tightened
to `X`'s existential scope, references a **shallower** type variable that thereby
falls out of scope. `notes/Scratch7/8/9.agda` exhibit a closed, well-typed source program
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

- **Delta-indexed boundary.** `BEntry = rvl (A : Ty) | cnc (X : ℕ) (A : Ty)`; `BCtx = List BEntry`. Reveal rep `A` over the exterior `Γ`; conceal index `X` a whole-`Γ` de Bruijn index, rep `A` over the interior.
- **B₀ typing (`env`), not a consistency premise.** Record one boundary type `B₀`; derive both faces: internal `= substᵗ (γᵇ Θ) B₀`, external `= substᵗ (ρᵇ Θ) B₀`. No `τ(A)=σ(B)` premise.
- **Whole-`Γ` tight interior.** `intOf Γ Θ = prepAbst (revs Θ) (dropN (cmax Θ) Γ)` — reveals prepended over "everything deeper than the deepest conceal" (`cmax = 1 + max conceal index`). This is the **Example-8 soundness fix**: variables shallower than the deepest conceal are intentionally **blocked** (inaccessible in the interior). Conceal indices are whole-`Γ`-relative → renaming is uniform.
- **Projections.** `ρᵇ` (reveal-resolve): reveal var ↦ rep, others pass through. `γᵇ Θ = prepId (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ)`: reveal var passes through, concealed index ↦ its rep (**unshifted** — reps live over the whole interior and may mention reveal vars), kept index ↦ its interior slot `` ` (revs + (i ∸ cmax)) ``.
- **Scope premise on `env`.** `Scoped (baseS Θ Δ) B₀` forbids `B₀` from naming a **blocked** slot. `baseS` marks each bframe slot `ok`/`blk`; `Scoped`/`_∋ok_` is a wf judgment that only accepts `ok` slots (binders push `ok`). `subst-cong-sc` is the scope-restricted `subst-cong` — it needs the pointwise equality only at `ok` slots, which is what makes `γcnc-comm`'s failure at blocked indices irrelevant.

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

- **`TyWrap`** (R1, landed): a wrapped value meets a type application. Float
  the `·[]` inside and RECORD the argument as a new reveal, shifting conceal reps
  (`shiftReps`, reps live over the whole interior which grows by one `abst`):
  `(V ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ] -→ ((⇑ᵀ V) ·[ B′ , ` 0 ]) ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫`.
  Face laws: `γᵇ-shift` (every slot), `ρᵇ-shift-ty`, `bwf-shift`, `baseS-shift`.
  Never pushes `A` inward — this is how Example 8 is avoided by construction.
  The direct-combine variant R1′ `(Λ V) ⟪ Θ , `∀ B₀ ⟫ ·[ B , A ] -→ V ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫`
  is tighter but partial (stuck on nested wrappers) and would force a merge rule.
- **`Wrap`** (R2, landed — preservation keeps its statement via `⊢retag`: typing reads Δ only through its length; see notes/DECISIONS.md for why Option 1a would change that): a wrapped value meets an application; the argument moves
  inside through the DUAL boundary: `(V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W -→ (V · (W ⟪ dualᵇ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫`.
  An exact dual exists over all-`abst` exteriors (everything reachable from a
  closed program); over `rvld` exteriors it does not (`no-dual-Γ₃`). Blocked slots
  get a dummy rep, sound by the scope premise — R2's preservation needs
  `subst-cong-sc`.
- Drop / Cancel / merge: NOT needed for progress with R1/R2 in float-inside form;
  Cancel is sound exactly when the conceal rep equals the enclosing reveal's rep.

**Open design decisions — see `notes/DECISIONS.md` (alternatives as definitions).** Summary of Decision 1: `env` cannot relate a `cnc X A` rep
to the rep of the enclosing reveal of `X`, so
`bad = (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ rvl (`∀ (` 0 ⇒ ` 0)) ∷ [] , ` 0 ⟫`
is a closed well-typed value of type `∀(Z→Z)` that no type-preserving rule can
eliminate. Routes: (1) a reachability companion predicate — against the
grounded-invariants law; (2) ground it: a reveal puts `rvld A` (not `abst`) in
`intOf` and `bwf↓` demands `Δ ∋ X := A` — touches §2's `intOf`, with a wrinkle
when the reveal rep names a dropped slot; (3) prove progress only for the image
of source programs. `Progress.agda` keeps this obstruction as a labelled hole.

## 5. PROGRESS (in flight, incremental)

`progress : Δ ∣ [] ⊢ M ⦂ A → Value M ⊎ (Σ Term λ M′ → M -→ M′)` — generalised over
Δ (ξ-⟪⟫ recurses into `intOf Δ Θ`), term context always `[]`.
- `Canonical.agda`: `canon-ℕ/⇒/∀` (value = numeral/ƛ/Λ or a wrapper),
  `canon-var` (a value of variable type is a wrapper with a variable boundary
  type — a chain ending in a conceal of that variable), `Value-renameᵀ`.
- `cf-∀-B₀` / `cf-⇒-B₀` (probe §6): a wrapper's `B₀` is `∀`/`⇒`-shaped (R1/R2
  fire) or a reveal variable (the `bad` case above).
- Each `_-→_` rule gets a `progress` case as it lands; holes are labelled with the
  rule (or decision) they wait for.

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
checks the whole NEW design. `make -C strong check` additionally runs
`postulate-check`, which currently fails only on the OLD design's
`Preservation.agda` (8 holes). Proposed cleanup (needs Jeremy's OK): delete old
`Preservation.agda` and `Examples.agda` (unreferenced), move old `Terms`/`Typing`/
`Reduction` and `notes/Scratch7/8/9` under `notes/old/` (the scratches import
them; adjust their module headers).

## 8. Tooling (2026-09-03)

Opus subagents do the Agda loop; REALLMS (free; `scripts/REALLMS.md`,
`scripts/reallms_holes.py`) grinds lemma-sized holes; the supervisor verifies
every landing with `agda --safe`. Dependents of a holed module: put
`{-# OPTIONS --allow-unsolved-metas #-}` in the IMPORTED module only, or better,
use the repo's `...Def` convention (statement in a `FooDef` module, importer
parameterised over it, instantiated when the proof lands).
