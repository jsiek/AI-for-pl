# Is the `CancelR` defect REACHABLE?  Yes — the hunt, 2026-09-19

Jeremy's question, verbatim: *"For the CancelR problem and repair, do you
have an example source program that reduces to the problematic
configuration?"*

**VERDICT: YES.** The witness is machine-checked in
`notes/CancelRReachabilityWitness.agda` and is the FIRST candidate the
search built. Two controls confirm that it is the CONJUNCTION of the two
conjuncts that breaks preservation, not either one alone.

That settles the repair question in favour of **path (a)** — carry the
re-spelling premise against the inner boundary's own conversion context —
because there is no invariant `numBinds Θ₁ ≡ 0` to prove: it is false on a
reachable redex. §6 of the witness module also checks, on this very
contractum, that the shifted spelling repair (a) would supply retypes it.

---

## 1. The source program

```
Inner = ΛX. λf:(∀Z. Z ⇒ X). (f [ℕ]) · 7        : ∀X. (∀Z. Z⇒X) ⇒ X
Outer = ΛP. λp:P. (Inner [P]) · (ΛZ. λz:Z. p)  : ∀P. P ⇒ P
Src   = (Outer [ℕ]) · 7                        : ℕ
```

Closed, plain System F: no boundary, no morphism, no conversion anywhere in
the source. It is nine steps from the `CancelR` redex; the tenth step is
the `CancelR`, and `eval` records it as `broke` — the contractum has no
typing derivation, and the witness module proves that with an explicit `¬`,
not only with the checker's refusal.

Intended reading: `Inner` takes a polymorphic function that RETURNS the
abstracted type, instantiates it at `ℕ`, and applies it to `7`; `Outer`
runs `Inner` at its OWN type variable `P`, supplying `ΛZ. λz:Z. p` for the
argument. Both facts are load-bearing, one per conjunct (§3).

## 2. The run

`scripts/render_term.sh 'showRun 0 12 Src-⊢' 'open import
strong-rep-var.notes.CancelRReachabilityWitness'` (α, β, γ are representation
variables; `↑β:=α` is a bind whose payload is the representation VARIABLE
α; `↥` an unlock, `↓` a lock):

```
((ΛX. (λx:X. ((ΛY. (λy:(∀Z. (Z⇒Y)). (y [ℕ] · 7))) [X] · (ΛZ. (λy:Z. x))))) [ℕ] · 7)
  --[TyBeta]-->
(((λx:X. …) ⟪ ↑α:=ℕ , ↥X , (seal X ↦ unseal X) ⟫) · 7)
  --[Peel]-->
(((λx:X. …) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫)
  --[Beta]-->
(((ΛY. (λx:(∀Z. (Z⇒Y)). (x [ℕ] · 7))) [X]
    · (ΛZ. (λx:Z. ((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Z , id X ⟫)))) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫)
  --[TyBeta]-->            ← mints ((∀Z. (id Z ↦ seal Y)) ↦ unseal Y) on ↑β:=α
((((λx:(∀Z. (Z⇒Y)). (x [ℕ] · 7))
     ⟪ ↑β:=α , ↥Y , ((∀Z. (id Z ↦ seal Y)) ↦ unseal Y) ⟫) · (ΛZ. …))
   ⟪ ↑α:=ℕ , ↥X , unseal X ⟫)
  --[Peel]-->              ← the ∀-conversion goes to the ARGUMENT, dual frame
  --[Beta]-->
(((((ΛZ. (λx:Z. …)) ⟪ ↓Y , (∀Z. (id Z ↦ seal Y)) ⟫) [ℕ] · 7)
    ⟪ ↑β:=α , ↥Y , unseal Y ⟫) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫)
  --[TyPeelR-Λ]-->         ← THE SEAL LEAF LANDS ON A FRAME THAT BINDS
(((((λx:Z. …) ⟪ ↑γ:=ℕ , ↥Z , ↓Y , (seal Z ↦ seal Y) ⟫) · 7)
    ⟪ ↑β:=α , ↥Y , unseal Y ⟫) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫)
  --[Peel]-->              ← the CODOMAIN `seal Y` stays on THAT frame
  --[Beta]-->
(((((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Z , id X ⟫)
     ⟪ ↑γ:=ℕ , ↥Z , ↓Y , seal Y ⟫)          ← Θ₁: numBinds ≡ 1
    ⟪ ↑β:=α , ↥Y , unseal Y ⟫)              ← Θ₂: payload α, OPEN
   ⟪ ↑α:=ℕ , ↥X , unseal X ⟫)
  --[CancelR]-->  -- TYPE LOST
```

In de Bruijn, with `Δ₉ = (bindR ℕ ∷ []) ∣ (0 ∷ [])` the ambient of the
`CancelR`:

```
Θ₁ = morph (ℕ ∷ [])   (lock 1 1 ∷ unlock 0 0 ∷ [])   numBinds Θ₁ ≡ 1
Θ₂ = morph (` 0 ∷ []) (unlock 0 0 ∷ [])              payload ` 0 — a rep VARIABLE
Δᶜ = conv Θ₂ Δ₉ = (bindR (` 0) ∷ bindR ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
```

`Δᶜ` is `notes/CancelRShiftWall.agda`'s hand-built `Δ*` **on the nose**, and
`Δᶜ ∋ 0 := ` 1` with `` ` 1 `` denoting the representation VARIABLE
`` ` 1 ``. The wall's configuration is not merely reachable in spirit; it
is reachable literally.

## 3. Why the search found it on the first try

The wall module's reason for believing the configuration might be
unreachable is:

> A bare `seal X` conversion is minted by exactly one rule — `Peel`, on the
> crossing argument — whose frame is `dualMorph Θ`, and
> `binds (dualMorph Θ) ≡ []`.

`Peel` mints **two** boundaries, and only the argument's carries the dual:

```
Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
  -→ (V · (… ⟪ dualMorph Θ , s′ ⟫)) ⟪ Θ , t ⟫
            ^^^^^^^^^^^^^ binds nothing     ^^^ the ORIGINAL frame
```

So a bare `seal` sits on a multi-bind frame as soon as the CODOMAIN of a
`↦` conversion is a `seal` and the boundary's own frame binds. The frame
binds when the boundary was minted by `TyPeelR` (`instantiate R Θ₀`), and
`instReveal X (seal Y) ≡ seal Y` carries the leaf across untouched. All
four identities are checked in §0 of the witness module.

What remained was to produce a `↦` whose codomain is a bare `seal`, i.e. a
`conceal` landing on the abstracted variable to the RIGHT of an `⇒` and
UNDER a `∀`:

```
conceal 0 (∀Z. Z ⇒ X) ≡ `∀ (id (` 0) ↦ seal 1)
```

which is `TyBeta`'s mint at an argument of type `∀Z. Z ⇒ X`. **No program
in the twelve-run suite or in `Examples.agda` passes an argument whose
polymorphic type RETURNS the abstracted variable** — examples 8 and 9 come
closest (`∀Z. Z⇒Z` and `∀Z. Z⇒X`), but 9's `∀Z. Z ⇒ X` is the payload of a
type APPLICATION, not the argument type of the function that abstracts `X`,
so its seal leaf never meets a `TyPeelR`. That is the gap the suite had.

Then `[P]` instead of `[ℕ]` for the instantiation that mints the cancelled
binder, exactly as `Examples.agda` §2c (`R`) already does for `IdPush`,
makes the payload a representation variable.

## 4. The candidate table

| # | program shape | (i) `numBinds Θ₁ > 0` | (ii) rep open | outcome |
|---|---|---|---|---|
| 1 | `((ΛP. λp:P. ((ΛX. λf:(∀Z. Z⇒X). f[ℕ]·7) [P]) · (ΛZ. λz:Z. p)) [ℕ]) · 7` | YES, `Θ₁ = ↑γ:=ℕ,↥Z,↓Y` | YES, `Θ₂ = ↑β:=α` | **BREAKS** at step 10 (`CancelR`); `eval` records `broke` |
| A | control: candidate 1 with the inner instantiation at `ℕ`, i.e. `(ΛX. λf:(∀Z. Z⇒X). f[ℕ]·7) [ℕ] · (ΛZ. λz:Z. 5)` | YES, `Θ₁ = ↑β:=ℕ,↥Y,↓X` | no — payload `ℕ` | runs, 9 steps to `5` |
| B | control: candidate 1 with a FIRST-ORDER crossing argument, `((ΛP. λp:P. ((ΛX. λf:ℕ⇒X. f·7) [P]) · (λn:ℕ. p)) [ℕ]) · 7` | no — `Θ₁ = ↓Y`, the `Peel` dual | YES, `Θ₂ = ↑β:=α` | runs, 17 steps to `7` |

Both controls are in §7 of the witness module, as ordinary `Reaches` runs,
so they are regressions and not just prose. They are the machine-checked
form of the wall's remark that each conjunct alone is harmless.

## 5. What the witness module checks

* `Src-⊢ : empty ∣ [] ⊢ Src ⦂ ℕ` — the source is a closed, plain program.
* `src-→*-redex : empty ⊢ Src -→* Redex` and
  `src-→*-contractum : empty ⊢ Src -→* Contractum` — reachability in the
  object language's own relation, via `eval-run`, with the two states
  pinned to hand-written terms by `refl`.
* `eval-broke-at-step-10 :
   report (eval 10 Src Src-⊢) ≡ reported Contractum 10 false` — `eval`
  records the break, so no `Reaches` for this run can assert `true`.
* `conjunct-i : numBinds Θ₁ ≡ 1` and, for (ii), `lookup-A : Δᶜ ∋ 0 := ` 1`
  with `conjunct-ii-rep : Δᶜ ⊢ᶜ ` 1 ~ ` 1` and
  `conjunct-ii-open : shiftRep 1 (` 1) ≢ ` 1`.
* `cancel-step` — the `CancelR` derivation itself, every premise supplied
  by the checker at the contexts the run built, and `redex-step` the same
  step under the outermost boundary where the run takes it.
* `no-contractum : ¬ (empty ∣ [] ⊢ Contractum ⦂ ℕ)`, through
  `no-cancel-pair`, which refutes the two minted layers for an ARBITRARY
  exterior type. The argument is the wall's: the outer `mkId (` 1)` pins
  the inner boundary's exterior reading to `` ` 1 ``, the inner
  `SameTyExt 1` then demands `shiftRep 1 (` 1) ≡ ` 2`, and at `Δ⋉ᶜ` the
  name `` ` 1 `` denotes `` ` 1 ``. A representation reading is unique.
* `repaired-⊢` — the same contractum with `mkId (` 2)` on the inner layer
  IS well typed, and `seal-source : Δ₁ᶜ ∋ 1 := ` 2` shows that `` ` 2 ``
  is exactly what repair (a)'s premise
  `Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ` delivers,
  with `Δ₁ᶜ = conv Θ₁ (int Θ₂ Δ₉)`.

Nothing is installed: `strong-rep-var.Reduction` is untouched, and
`strong-rep-var.proof.Preserve` keeps `CancelRCase` as the open parameter it was.

## 6. Consequence for the repair decision

Path (b) — prove and carry the invariant `numBinds Θ₁ ≡ 0` — is CLOSED.
The invariant is false at a `CancelR` redex reachable from a closed, plain
source program, so there is nothing to prove and no premise of that shape
can be discharged.

Path (a) stands, and on this example it is confirmed: with the premise
read against `Δ₁ᶜ` (and the new premise `Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ` that makes `Δ₁ᶜ`
available), the rule mints `mkId (` 2)` where it now mints `mkId (` 1)`,
and the contractum types. Whether that premise is always satisfiable —
the analogue of `peel-premises` for `CancelR` — is the next question, and
it is not answered here.

## Postscript, 2026-09-19 — repair (a) approved and installed

Jeremy approved repair (a) the same day this hunt log was written, and it
is installed on `codex/strong-system-f-representation-vars`.

`strong-rep-var.Reduction`'s `CancelR` now carries the three readings the old rule
lacked and re-spells at the inner boundary's own conversion context:

    CancelR : … → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → Δ₁ᶜ ∋ X := Aᵢ
      → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
      → Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ
      → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ → Δᶜ ∋ Y := A → …

which is `IdPush`'s premise block with `Aᵢ` in place of `` ` X ``.

What changed for `Src`. The first nine steps are untouched; step 10 now
mints `mkId (` 2)` on the inner layer where it minted `mkId (` 1)`, and
the run COMPLETES — `Reaches 19 19 Src-⊢ ($ 7)`, every state type checked
(`notes/CancelRReachabilityWitness.Src-eval`). The raw machine, which
carries no typing and used to stick at 16 steps on a non-value identity
tower, now agrees exactly: `rawLen 100 Src ≡ 19`, ending at `$ 7`
(`notes/RawRunProbe.agda`). The two controls keep their counts, 9 and 17.

And the question section 5 left open — whether the repaired premise is
always satisfiable, and whether the preservation case it generates is
provable — is answered for preservation:
`strong-rep-var.proof.MoveScope.preserve-CancelR` proves `CancelRCase` outright,
by `preserve-IdPush`'s argument. `strong-rep-var.Preservation.Stage1` and
`strong-rep-var.TypeSafety.Stage1` no longer take a `cancel` parameter. The
satisfiability half for progress is still carried by the pending-review
`MergedReading`.
