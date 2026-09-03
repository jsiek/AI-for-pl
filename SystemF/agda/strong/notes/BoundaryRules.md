# Boundary-manipulation rules — decision memo

For Jeremy. Everything asserted here is machine-checked in
`notes/BoundaryRulesProbe.agda` (`agda --safe -v0` clean, no holes, no
postulates); section numbers below point at that file. Nothing in
`BReduction.agda` is imported or changed.

Notation is Boundary.agda's throughout: `M ⟪ Θ , B₀ ⟫`, `rvl A`, `cnc X A`,
`revs Θ` (= *r*), `cmax Θ` (= *c*), `intOf Δ Θ = prepAbst r (dropN c Δ)`,
faces `γᵇ` (internal) / `ρᵇ` (external), scope stack `baseS Θ Δ`, rule `env`.

## 1. Proposed minimal rule set

Two new computation rules and the five `ξ` congruences suffice for progress.
Both new rules are **total in the wrapped term** — they do not require the
body to be syntactically `Λ`/`ƛ` — which is what removes the need for a merge
rule (§2).

```agda
  -- R1  a boundary meets a type application: float the ·[] inside and
  --     RECORD the type argument as a new reveal (never push A inward)
  β-⟪⟫·[] : Value V
    → (V ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
      -→ ((⇑ᵀ V) ·[ renameᵗ (extᵗ suc) (substᵗ (extsᵗ (γᵇ Θ)) B₀) , ` 0 ])
           ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫

  -- R2  a boundary meets an application: move the argument inside through
  --     the DUAL boundary
  β-⟪⟫· : Value V → Value W
    → (V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W
      -→ (V · (W ⟪ dualᵇ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫
```

`shiftReps` (probe §1) shifts the **conceal reps only** (`renameᵗ suc`): reps
live over the *whole* interior, which R1 grows by one `abst`. Reveal reps are
exterior and are untouched. The `B` index of `·[ B , A ]` is forced —
`tapp-B-forced : substᵗ (ρᵇ Θ) (`∀ B₀) ≡ `∀ B → B ≡ substᵗ (extsᵗ (ρᵇ Θ)) B₀`.

Proved face laws (probe §1), i.e. exactly the retypings preservation needs:

* `γᵇ-shift : γᵇ (rvl A ∷ shiftReps Θ) X ≡ extsᵗ (γᵇ Θ) X` — **at every slot**,
  blocked ones included, so R1 carries no scope side-condition;
* `ρᵇ-shift-ty : substᵗ (ρᵇ (rvl A ∷ shiftReps Θ)) B ≡ (substᵗ (extsᵗ (ρᵇ Θ)) B) [ A ]ᵗ`;
* `bwf-shift`, `baseS-shift : baseS (rvl A ∷ shiftReps Θ) Γ ≡ ok ∷ baseS Θ Γ`
  (so R1's `Scoped` obligation *is* the `sc-∀` inversion of the redex's);
* `ext-suc-[]0 : (renameᵗ (extᵗ suc) T) [ ` 0 ]ᵗ ≡ T` for the floated `·[]`
  (its index is the ∀-body of `⇑ᵀ V`'s type, hence the `renameᵗ (extᵗ suc)`;
  landed as `β-⟪⟫·[]` in BReduction.agda, preservation case in BPreservation.agda).

`dualᵇ` / `swapᵇ` (probe §3): every **reveal** of `Θ` becomes a **conceal** of
`dualᵇ Θ` at its interior index, keeping its rep (a reveal rep is read in `Δ`,
which is the dual's interior — exactly a conceal rep's home); every Δ-slot
`0 … c-1` that `Θ` dropped becomes a **reveal** of `dualᵇ Θ` whose rep is `Θ`'s
conceal rep for that slot (read in `intOf Δ Θ` — exactly a reveal rep's home).
So `revs (dualᵇ Θ) = cmax Θ`, `cmax (dualᵇ Θ) = revs Θ`, and the boundary frame
is permuted by the block swap `swapᵇ`. A dropped slot that is *not* concealed
is **blocked**; it gets an arbitrary rep (`ℕ`), which is sound precisely because
`env`'s `Scoped` premise forbids `B₁` from naming it — the one slot where the
exterior face law genuinely fails is kept as a checked witness
(`blocked-slot-differs`, probe §3a), so R2's preservation must use
`subst-cong-sc`, not a pointwise identity.

Checked typed redex/contractum pairs, all at the same type:

| rule | example | probe |
|---|---|---|
| R1 / R1′ | Example 8's own redex, at `Δ8 = [Y , X]` | §2 `⊢redex-R1`, `⊢contractum-R1`, `⊢contractum-R1′` |
| R1 on a **nested** wrapper | `nest ·[ Z→Z , 𝔹 ]` | §4c `⊢nest-redex`, `⊢nest-R1` |
| R2, reveal-only `Θ` | Example 8's step 2 at `Δ = []` | §4a `⊢redex-R2`, `⊢contractum-R2` |
| R2, **mixed** `Θ` (`rvl` *and* `cnc`) | `((λz:Z.z) ⟪ ↑Z:=ℕ,↓X:=ℕ ⟫) · 3` | §4b `⊢redex-R2m`, `⊢contractum-R2m` |
| R3 Drop `V ⟪ [] , B₀ ⟫ -→ V` | both faces are `B₀` — **confirmed** (`γᵇ-[]`, `ρᵇ-[]`) | §5 |
| R4 Cancel (reps agree) | `($7 ⟪ ↓X:=ℕ ⟫) ⟪ ↑X:=ℕ ⟫ -→ $7` | §5 |

## 2. Open decisions

**(a) The ƛ-application rule — does an exact dual exist?** Yes, and more often
than the sketch feared, but *not* always.

* Over an **all-`abst`** exterior the dual is exact:
  `intOf (intOf Δ Θ) (dualᵇ Θ) ≡ Δ`, checked for reveal-only, conceal-only and
  mixed `Θ` (probe §3a, incl. `intOf (intOf Δm Θm) (dualᵇ Θm) ≡ Δm`). Every
  context reachable from a closed program is `prepAbst n []` (only `⊢Λ` and
  `intOf` create entries, both `abst`), so this covers all of runtime.
* Over a context with `rvld` entries in the dropped prefix it does **not**
  exist: `intOf` can only prepend `abst` and drop a prefix, so `Γ₃` can never
  be rebuilt — `no-dual-Γ₃ : ¬ (Σ BCtx λ Θᵈ → intOf (intOf Γ₃ Θ₃) Θᵈ ≡ Γ₃)`
  (probe §3b). `Γ₃`-style contexts are hand-written examples only.
* The prompt's worry — "conceals of `Θ` would need to become reveals whose
  fresh variable stands for an *existing* Δ variable" — dissolves because the
  dual's interior is *rebuilt* by `prepAbst c`, and `abst` entries are
  interchangeable; the fresh reveal variables land at exactly the indices the
  dropped Δ-slots had. Blocked slots are covered by the scope premise.
* **Recommendation: R2 as stated**, with `dualᵇ` total (dummy rep for blocked
  slots). Restricting to `cmax Θ = 0` is *not* enough: a mixed boundary at an
  application is reachable — it is precisely the shape R1 produces (probe §2 →
  §4b). Alternative (c) of the prompt (an inverse wrapper only for the
  reveal-only case) is subsumed: `dualᵇ` on a reveal-only `Θ` *is* that inverse
  (`swapᵇ` is then the identity), and `dualᵇ (dualᵇ Θr) ≡ Θr`.

**(b) Merge / Cancel / Drop — needed for progress?** **No** — tidiness only,
*given* R1/R2 in the float-inside form. The alternative "direct combine" rules
(R1′ `(Λ V) ⟪ Θ , `∀ B₀ ⟫ ·[ B , A ] -→ V ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫`, checked
in probe §2, and the corresponding ƛ rule) produce *tighter* terms — one
boundary instead of two, no `⇑ᵀ` — but they are **partial**: R2 wraps the
argument, so nested wrappers are reachable, and R1′ is stuck on them
(`⊢nest-redex`, probe §4c). Choosing R1′/β-ƛ⟪⟫ therefore forces a merge rule.
Merge is also delicate: a composite of two boundaries is expressible in general
(the contexts line up), but reconciling a rep the inner boundary blocks needs
its own scope premises — and in the inconsistent case of §4 below no merge can
be type-preserving at all. **Recommendation: adopt R1/R2 now; keep R1′ and
Cancel as optional space-optimisations** (Cancel is sound exactly when the
conceal rep equals the enclosing reveal's rep, cf. probe §5 vs §5a). Drop is
type-preserving but unreachable: no rule mints `Θ = []`.

## 3. Canonical forms (PLAN §5)

With `Value = V-$ | V-G (ƛ/Λ) | V-⟪⟫` the shape analysis needed is the *boundary
type*, because that is what selects the rule. Proved in probe §6:

```agda
  cf-∀-B₀ : ∀ Θ B₀ → substᵗ (ρᵇ Θ) B₀ ≡ `∀ B
    → (Σ Ty λ B₀′ → B₀ ≡ `∀ B₀′)                    -- R1 fires
    ⊎ (Σ ℕ λ X → (B₀ ≡ ` X) × (X < revs Θ))         -- see §4
  cf-⇒-B₀ : ∀ Θ B₀ → substᵗ (ρᵇ Θ) B₀ ≡ (A ⇒ B)
    → (Σ Ty λ B₁ → Σ Ty λ B₂ → B₀ ≡ (B₁ ⇒ B₂))      -- R2 fires
    ⊎ (Σ ℕ λ X → (B₀ ≡ ` X) × (X < revs Θ))
```

(A `` ` X `` with `X ≥ revs Θ` is impossible: `ρᵇ-hi` makes the external face a
variable, and no elimination types a variable.) The statements progress then
uses, all restricted to the runtime term context `[]`:

```agda
  canon-ℕ : Value V → [] ∣ [] ⊢ V ⦂ `ℕ
          → (Σ ℕ λ n → V ≡ $ n)
          ⊎ (Σ Term λ V′ → Σ BCtx λ Θ → Σ Ty λ B₀ → V ≡ V′ ⟪ Θ , B₀ ⟫)
  canon-⇒ : Value V → [] ∣ [] ⊢ V ⦂ (A ⇒ B)
          → (Σ Ty λ A′ → Σ Term λ N → V ≡ ƛ A′ ∙ N) ⊎ (… wrapper …)
  canon-∀ : Value V → [] ∣ [] ⊢ V ⦂ `∀ B
          → (Σ Term λ V′ → V ≡ Λ V′) ⊎ (… wrapper …)
  canon-var : Value V → Δ ∣ [] ⊢ V ⦂ ` X
          → Σ Term λ V′ → Σ BCtx λ Θ → Σ ℕ λ Y → V ≡ V′ ⟪ Θ , ` Y ⟫
```

`canon-var` is the nested-wrapper question of the prompt: if `B₀` is a reveal
variable then the interior type is the *abstract* variable `` ` X ``
(`γᵇ-lo : X < revs Θ → γᵇ Θ X ≡ ` X`), and no `$`/`ƛ`/`Λ` has a variable type,
so the body must itself be a wrapper with a variable boundary type. The chain
can only terminate at a **conceal of that same variable** (a conceal rep is
`γᵇ`'s only non-variable output) — i.e. at a Cancel pair.

Rules needed so that every elimination of a closed value steps: `β-Λ`, `β-ƛ`,
`β-⟪⟫·[]` (R1), `β-⟪⟫·` (R2), and `ξ-·-l`, `ξ-·-r`, `ξ-·[]`, `ξ-⟪⟫`, `ξ-Λ`.
R1 additionally needs `Value V → Value (renameᵀ ρ V)` (structural).

## 4. Risks

**Example 8 is avoided by construction.** The old `β-↓[]` transported the type
argument *into* the interior (`downTyEnv X A`), where a shallower variable is
out of scope. R1 never transports `A`: it records it as `rvl A`, read in the
exterior, and applies the interior term to the *fresh reveal variable* `` ` 0 ``.
Machine-checked on Example 8's own redex, at `Δ8 = [Y , X]` with `Y` **blocked**
(`baseS Θ8 Δ8 ≡ blk ∷ ok ∷ []`):

```
        (polyid ⟪ ↓X:=ℕ , ∀(Z→Z) ⟫) ·[ Z→Z , Y ]      : Y→Y      ⊢redex-R1
  R1 ↓
        (polyid ·[ Z→Z , ` 0 ]) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→Z ⟫ : Y→Y    ⊢contractum-R1
  β-Λ ↓
        (λz:Z. z) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→Z ⟫              : Y→Y     ⊢contractum-R1′
```
`Y` stays blocked in the interior and `B₀ = Z→Z` never names it, so `Scoped`
holds; the old design's ill-typed term is unreachable. R2 likewise never moves
a type *into* the interior — `dualᵇ` only re-reads reps that already live on
the right side of the boundary.

**The one real risk is not Example 8 but rep inconsistency.** `env` records one
`B₀` and derives both faces (§2, settled), and there is no premise relating a
`cnc X A`'s rep to the rep of the reveal whose variable it conceals — the
reveal lives on an *enclosing* wrapper, so no local premise could. Hence
(probe §5a) the closed, well-typed **value**

```agda
  bad = (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ rvl (`∀ (` 0 ⇒ ` 0)) ∷ [] , ` 0 ⟫
  ⊢bad : [] ∣ [] ⊢ bad ⦂ `∀ (` 0 ⇒ ` 0)
```
whose whole content is `$ 7`. `bad ·[ Z→Z , ℕ ] : ℕ→ℕ` is well typed, is not a
`Λ`, has a *variable* `B₀` (so neither R1 nor R1′ applies), and Cancel would be
unsound (`bad-cancel-ill-typed : ¬ ([] ∣ [] ⊢ $ 7 ⦂ `∀ (` 0 ⇒ ` 0))`). No merge
can help: the composite of those two boundaries would have to be a `Θ₂` over
`[]` with `intOf [] Θ₂ ≡ []`, whose two faces then coincide — but they must be
`ℕ` and `∀(Z→Z)`. **So progress cannot be proved from `env` alone**; the term is
unreachable (R2's conceals come from `dualᵇ`, which copies the reveal's own
rep), so the options are:

1. state progress for the reachable class (an invariant "every `cnc` matches its
   enclosing `rvl`"), which is a *companion* predicate — against the standing
   design law;
2. ground the invariant in the relation: let a reveal put `rvld A` (not `abst`)
   into `intOf`, and let `bwf↓` demand `Δ ∋ X := A` (`Context.agda` already has
   `_∋_:=_`). This kills `bad` and legitimises `dualᵇ`'s conceals. **Wrinkle**:
   a reveal rep is read in `Δ`, and when `cmax Θ > 0` it may name a slot the
   interior drops (in the diagram above `rvl A` has `A = Y`, blocked) — so the
   entry can only be `rvld` when the rep survives, `abst` otherwise, and the
   pathology returns exactly on those slots. Touches §2's `intOf` — flagged, not
   relitigated;
3. accept it and prove progress only for the image of a source program.

My recommendation: adopt R1/R2 (they are orthogonal to this), and take route 3
for now, with route 2 recorded as the principled fix if progress is to be stated
unconditionally. Nothing above conflicts with §2 otherwise: `B₀`-typing, the
whole-`Γ` interior, the unshifted conceal reps and the scope premise are all
*used* by these rules — R2 in particular is only sound because of `Scoped`.
