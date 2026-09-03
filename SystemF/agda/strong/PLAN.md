# Strong System F — handoff plan (finishing preservation & progress)

Status as of the `strong-tightened-conceal-marker` branch. This document is the
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

| file | role | status |
|---|---|---|
| `Boundary.agda` | boundary syntax, projections, scope machinery, typing (`_∣_⊢_⦂_`, `env`) | ✅ compiles, 0 holes |
| `BReduction.agda` | reduction `_-→_`, values, type-var renaming/subst through boundaries, `⊢renameᵀ`, `preservation` | ⚠️ 3 holes |
| `ScratchGamma.agda` | evidence: the fixed conceal-rep-references-reveal bug | ✅ |
| `ScratchBlocked.agda` | evidence: the blocked-var aliasing that motivates the scope premise | ✅ |
| `Scratch7/8/9.agda` | machine-checked proof that the OLD (non-boundary) tightened design was unsound (Example 8) | ✅ keep as evidence |
| `Types/Context/Typing/Reduction/Weakening/Examples.agda` | the older non-boundary development | pre-existing |

`BReduction.agda` holes (all in the renaming/substitution path):
1. `scB` (line ~306) — `β-Λ`'s new `Scoped` obligation.
2. `⊢renameᵀ … (env …)` (line ~279) — the `env` case of type-variable renaming.
3. `preservation … (β-ƛ …)` (line ~313) — needs `⊢substᵀᵐ`.

`β-Λ` preservation is otherwise proven; `β-ƛ` and `⊢renameᵀ` are the open work.

## 2. Settled design (do not relitigate)

- **Delta-indexed boundary.** `BEntry = rvl (A : Ty) | cnc (X : ℕ) (A : Ty)`; `BCtx = List BEntry`. Reveal rep `A` over the exterior `Γ`; conceal index `X` a whole-`Γ` de Bruijn index, rep `A` over the interior.
- **B₀ typing (`env`), not a consistency premise.** Record one boundary type `B₀`; derive both faces: internal `= substᵗ (γᵇ Θ) B₀`, external `= substᵗ (ρᵇ Θ) B₀`. No `τ(A)=σ(B)` premise.
- **Whole-`Γ` tight interior.** `intOf Γ Θ = prepAbst (revs Θ) (dropN (cmax Θ) Γ)` — reveals prepended over "everything deeper than the deepest conceal" (`cmax = 1 + max conceal index`). This is the **Example-8 soundness fix**: variables shallower than the deepest conceal are intentionally **blocked** (inaccessible in the interior). Conceal indices are whole-`Γ`-relative → renaming is uniform.
- **Projections.** `ρᵇ` (reveal-resolve): reveal var ↦ rep, others pass through. `γᵇ Θ = prepId (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ)`: reveal var passes through, concealed index ↦ its rep (**unshifted** — reps live over the whole interior and may mention reveal vars), kept index ↦ its interior slot `` ` (revs + (i ∸ cmax)) ``.
- **Scope premise on `env`.** `Scoped (baseS Θ Δ) B₀` forbids `B₀` from naming a **blocked** slot. `baseS` marks each bframe slot `ok`/`blk`; `Scoped`/`_∋ok_` is a wf judgment that only accepts `ok` slots (binders push `ok`). `subst-cong-sc` is the scope-restricted `subst-cong` — it needs the pointwise equality only at `ok` slots, which is what makes `γcnc-comm`'s failure at blocked indices irrelevant.

### Two findings that produced the current design (see scratch files)
1. **FIXED** — old `γᵇ = extsⁿ(revs)(γᶜ)` shifted conceal reps by `sucᵛ`, disagreeing with `bwf↓`/`renᴮ` when a rep mentions a reveal var. Now `prepId`/`γcnc`, no shift.
2. **Blocked-var aliasing** — `γᵇ` aliased a blocked var onto a kept var (both → same slot). Resolved by the scope premise (user chose this over a `delAt`-style interior, which would reopen Example 8).

## 3. Finish PRESERVATION (ordered)

### 3a. Close `⊢renameᵀ`'s `env` case (the crux)
`⊢renameᵀ : (∀{X} → Δ ∋tv X → Δ' ∋tv ρ X) → Δ ∣ Γₜ ⊢ M ⦂ A → Δ' ∣ map (renameᵗ ρ) Γₜ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A`.
The `env` case mirrors the already-proven `C-ext`. Needed lemmas (all in `BReduction.agda`; `C-ext`, `ρᵇ-comm`, `h-restrict`, `↓-∋`/`↓-∋⁻`, `∸-strict`, `Mono` already exist):

1. `revs-ren`: `revs (renᴮ ρ ir Θ) ≡ revs Θ` (trivial, `renᴮ` preserves reveal count).
2. `⊔`-monotone-commute (`ρ (a ⊔ b) ≡ ρ a ⊔ ρ b` for `Mono ρ`) → `cmax-ren`: `cmax (renᴮ ρ ir Θ)` relates to `ρ (cmax Θ ∸ 1)` — needed so the interior drop-count aligns under renaming.
3. `liftⁿ-lo` (`X < r → liftⁿ r ρ X ≡ X`) and `liftⁿ-hi` (`liftⁿ r ρ (r + i) ≡ r + ρ i`).
4. `prepId-lo` (`X < r → prepId r σ X ≡ ` X`) and `prepId-hi` (`prepId r σ (r + i) ≡ σ i`), via `m+n∸m≡n` / `m+n≮m`. These encapsulate the `<?` reasoning once.
5. `split : ∀ r X → (X < r) ⊎ (∃ i, X ≡ r + i)` — a view to case on reveal-prefix vs deep.
6. `γcnc-comm` (base content): `∀ i → γcnc r m' Θ' (ρ i) ≡ renameᵗ (deepRen m ρ) (γcnc r m Θ i)` — **holds at concealed and kept `i`** (fails at blocked, which is fine — see next). By induction on `Θ`; concealed `i` gives the (renamed) rep on both sides, kept `i` uses `cmax-ren` + `restrictRen`.
7. `γᵇ-comm-ok`: `∀ X → baseS Θ Δ ∋ok X → γᵇ Θ' (liftⁿ (revs Θ) ρ X) ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ X)`. Assemble from 3–6 via `split`. Needs a bridge: `baseS Θ Δ ∋ok X` (with `X = revs + i`) implies `i` is concealed or kept — i.e. `γcnc-comm` applies. Prove `slotAt`/`baseS` bridge lemmas (`∋ok` at a `Γ` slot ⇒ `cmax ≤ i ∨ isConc i Θ`).
8. `C-int` (mirror `C-ext`, but use `subst-cong-sc sc (γᵇ-comm-ok …)` in the middle step so only `ok` slots are needed):
   `substᵗ (γᵇ Θ') (renameᵗ (liftⁿ (revs Θ) ρ) B₀) ≡ renameᵗ (intRen ρ Θ) (substᵗ (γᵇ Θ) B₀)`, given `Scoped (baseS Θ Δ) B₀`.
9. `bwf-ren`: `Δ ∣ intOf Δ Θ ⊢ᵇ Θ → Δ' ∣ intOf Δ' (renᴮ …) ⊢ᵇ (renᴮ …)` (uses `h`, `h-int` = the interior-lookup lemma built from `h-restrict` + `cmax-ren`, and `wf-ren`).
10. `sc-ren`: `Scoped (baseS Θ Δ) B₀ → Scoped (baseS (renᴮ …) Δ') (renameᵗ (liftⁿ …) B₀)` — the scope premise transports under renaming (renaming is index-preserving on `ok` slots).
11. Wire the `env` case: `env (bwf-ren …) (sc-ren …) (⊢renameᵀ h-int ⊢M …)`, retyping the two faces by `C-int`/`C-ext`.

Note: the interior renaming is now uniform — `intRen ρ Θ = liftⁿ (revs Θ) (deepRen (cmax Θ) ρ)` with a **single** restriction (`deepRen`), not the old progressive per-conceal `restrictRen`.

### 3b. Close `β-Λ`'s `scB`
Needs a **context-wf ⇒ typing ⇒ `Scoped`** bridge, specialised to the all-`ok` case (`β-Λ`'s boundary `rvl A ∷ []` has `cmax = 0`, so `baseS` is all `ok`). Concretely:
- `wf→Scoped-allOk : (Δ' ⊢ B) → (baseS Θ Δ is all ok, length = length Δ') → Scoped (baseS Θ Δ) B` via `∋tv → ∋ok`.
- a **context-wf ⇒ typing ⇒ type-wf** lemma `⊢ty-wf : CtxWf Γₜ Δ → Δ ∣ Γₜ ⊢ M ⦂ A → Δ ⊢ A` (needs a `CtxWf` invariant because `⊢`\` pulls a type from the term context). `β-Λ` uses it at the empty term context `⤊[] = []`. The `env` case of `⊢ty-wf` needs `substᵗ (ρᵇ Θ) B₀` wf — build a `subst-preserves-wf` for `ρᵇ`.

### 3c. `⊢substᵀᵐ` → `β-ƛ`
`⊢substᵀᵐ : (∀ {x A} → Γₜ ∋ x ⦂ A → Δ ∣ Γₜ' ⊢ σ x ⦂ A) → Δ ∣ Γₜ ⊢ N ⦂ B → Δ ∣ Γₜ' ⊢ substᵀᵐ σ N ⦂ B`. `substᵀᵐ` is the identity on wrappers, so the only nontrivial cases are `ƛ`/`·`/`Λ`; the `Λ` case uses `⊢renameᵀ` (3a) to push `σ` under the type binder. Then `β-ƛ` preservation is `⊢substᵀᵐ (σ from ⊢W) ⊢N`.

## 4. Complete the REDUCTION relation

`_-→_` currently has only `β-Λ` and `β-ƛ`. Add, **one rule at a time**, each with a
typed redex≈contractum example then its preservation case (the established rhythm):

- **ξ (congruence)** rules: `ξ-·-l`, `ξ-·-r`, `ξ-·[]`, `ξ-⟪⟫` (reduce under a boundary), `ξ-Λ`. Preservation cases are routine once 3a–3c land.
- **Boundary-manipulation** (the interesting rules — combined/simultaneous boundary):
  - a wrapped value meeting a **type application** combines into one boundary — the motivating `(ΛZ.V) ↓[X:=A] [B] --> V ⟪ ↑Z:=B , ↓X:=A ⟫` (reveal + conceal coexist on one boundary; NO separate `Commute` rule).
  - a wrapped value meeting an **application** / **another boundary**: push/merge (`Cancel` a reveal against a matching conceal; `Drop` an empty boundary).
  - the dual builder `dualᵇ` for reveal↔conceal was sketched in earlier notes.
  These need the boundary-combination semantics finalised; keep them consistent with the `intOf`/`γᵇ`/`ρᵇ` projections and the scope premise.

## 5. PROGRESS

Not started. Standard shape:
- `Progress : [] ∣ [] ⊢ M ⦂ A → Value M ⊎ ∃ M′, M -→ M′`.
- **Canonical forms** over `Value` including `V-⟪⟫` (a wrapped value): a value of `∀`-type is `Λ`; of `⇒`-type is `ƛ`; and characterise wrapped values so the boundary-manipulation rules fire. The `env` typing rule plus the `Value` grammar (`V-$`, `V-G`, `V-⟪⟫`) drive the case analysis.
- Each `_-→_` rule must have a matching progress case; boundary-manipulation rules ensure wrapped values at elimination positions always step.

## 6. Conventions / gotchas (learned)

- **No `postulate`** — leave `{!!}` holes; `make postulate-check` fails on `postulate`.
- **No `cd`** in Bash — use `agda -v0 strong/File.agda` from `SystemF/agda`, or `make -C`.
- Constructor-form indices, named `with`-cases (not `...`), no catch-all cases in proofs.
- `subst-cong` (in `TypeSubst.agda`) needs **all** indices — that's why `subst-cong-sc` (scope-restricted) exists; use it wherever a per-index equality only holds on accessible slots.
- `prepId`/`slotAt` use `_<?_`/`_≤?_`; these reduce definitionally on closed indices (examples type by `refl`) but need `prepId-lo/hi` lemmas for abstract indices.
- Build each reduction rule → typed example → preservation case, in that order.

## 7. Build

From `SystemF/agda/`:
```
agda -v0 strong/Boundary.agda
agda -v0 strong/BReduction.agda      # 3 holes until §3 lands
```
The strong development is not yet wired into `All.agda`; add it once the holes are
closed and `make check` is clean.
