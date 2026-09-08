# The shift audit — every place a rule moves a subterm

**Jeremy, 2026-09-08.**  "Frame exactness is the main point of Strong
System F!"  (PR #199: `Beta` now wraps every value crossing a `Λ` in that
binder's dual, `crossΛ`.)  Request: *audit all places that shift a term to
see if we have forgotten to mask type variables in other places.*

**VERDICT: one leak, and it is INSTALLED-FIXED.**  The audit found exactly
one — the single `TyPeelR` moved its value under a **new unmasked bind
slot** — and the repair `(b)+(b′)` is now in the live calculus: the rule
is the two clauses `TyPeelR-Λ` and `TyPeelR-⟪⟫` (`Reduction.agda`, and
`Design.md` §6.4).  **Every rule that moves a subterm masks what it
introduces, and the table below has no exceptions.**

Machine-checked companion: `proof/ShiftAudit.agda` (in `All.agda`; the
gate `make -C strong check` is green).  The frame-identity table it feeds
is `Design.md` §7; the per-rule tightness tests are `Examples` §15 —
§15b for the two `TyPeelR` clauses — and `proof/DualTightness`.

## The criterion

Whenever a rule **moves a subterm** to a new position, the subterm's type
context at the new position must be **exactly** its context at the old
position, up to

1. the **index shift** past the binders it crossed, and
2. **refinement** `abst → bind` of a slot it **could already name**
   (TyBeta's reveal; `instReveal`'s slot).

Any slot the subterm **could not name before and can name after** is a
**frame leak** — even when the subterm's shifted indices cannot reach it.
The frame must *say the truth* about what the subterm may name.

## The table

| site | what shifts | frame before | frame after | verdict |
|------|-------------|--------------|-------------|---------|
| **Peel** | `wkᴹ (numBinds Θ) W` under `dual Θ` | `Δ` | `map maskEnt (pushBinds (binds Θ) []) ++ Δ` — (†) `proof/PeelDual.interior-dual` | **exact**.  Every new slot is `masked` (`Peel-slot0-locked`), and `wkᴹ (numBinds Θ)` lands past exactly them.  Criterion 1 alone. |
| **Peel** (`V`) | nothing | `interior Θ Δ` | `interior Θ Δ` | **exact** — identical context, no shift. |
| **TyPeelR** (`V`), the SINGLE rule — *replaced* | `wkᴹ 1 V` | `interior Θ Δ` | `unmasked (bind (shiftBy (numBinds Θ) A)) ∷ interior Θ Δ` — `interior-TyPeelR` | ****LEAK****.  The new slot 0 was offered **unmasked**; `V` neither had it nor uses it.  This is the rule the split replaced; the record of the leak is `proof/ShiftAudit` §3/§3a. |
| **TyPeelR-Λ** (`N`) | nothing | `unmasked abst ∷ interior Θ Δ` | `interior (morph (A ∷ binds Θ) (changes Θ)) Δ` — `interior-TyPeelR` | **exact up to refinement**.  The `Λ`'s abst slot BECOMES the boundary's bind slot: `la-uu le-ab` at a slot `N` could already name, criterion 2, `⊑ᵃ`-legal (`TyPeelR-Λ-refinement`).  **No shift at all** — no `wkᴹ`, no `⊢rename`. |
| **TyPeelR-⟪⟫** (the moved boundary) | `wkᴹ 1`, plus `lock 0` appended to its own change list | `interior Θ′ (interior Θ Δ)` | `pushBinds (map ⇑ᵗ (binds Θ′)) (masked (bind (shiftBy (numBinds Θ) A)) ∷ scope Θ′ (interior Θ Δ))` — `TyPeelR-⟪⟫-frame`, from `strong.TermSubst.interior-addLock0-cross` | **exact**.  The moved boundary's BIRTH frame with the new binder inserted **masked** below its bind prefix — the shape (†) gives Peel and `interior-Beta-Λ` gives Beta.  Criterion 1 alone; the new slot is unnameable there (`TyPeelR-⟪⟫-slot-locked`), and it crosses by `⊢rename` at `Ren-addLock0` **alone**. |
| **TyBeta** | nothing (`N` stays) | `unmasked abst ∷ Δ` (`⊢Λ`) | `unmasked (bind A) ∷ Δ` — `interior-TyBeta` | **exact up to refinement**.  `la-uu le-ab` at a slot `N` could already name: criterion 2, `⊑ᵃ`-legal. |
| **TyBeta** (the type `B`) | nothing | `unmasked abst ∷ Δ` | `convCtx (morph (A ∷ []) []) Δ ≡ unmasked (bind A) ∷ Δ` | **exact up to refinement** — same step. |
| **Beta**, no binder crossed | `substᵐ` | `Δ` | `Δ` | **exact**.  (The one recorded exception is **erasure** — a dropped argument crosses nowhere; `Examples` §15d.) |
| **Beta**, crossing a `Λ` | `crossΛ W A = ⇑ᴹ W ⟪ morph [] (lock 0 ∷ []) , mkId (⇑ᵗ A) ⟫` | `Δ` | `interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ` — `interior-Beta-Λ` | **exact** (PR #199).  Slot 0 is refused (`Beta-Λ-slot0-locked`). |
| **Beta**, crossing a `ƛ` | `shiftᴵ` | `Δ` | `Δ` | **exact, vacuous**.  A `ƛ` binds a *term* variable; `shiftᴵ` is the identity on a value image because the image is **term-closed**, and it stays term-closed after #199 (`crossΛ W A` is a boundary, and `env` types its interior at `Γ = []`).  The two crossings commute on the nose (`⇑ᴵ-shiftᴵ-comm`) — the no-interference law. |
| **CancelR / IdPush** (`V`) | nothing | `interior Θ₁ (interior Θ₂ Δ)` | `interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ)` — `proof/MoveScope.interior-⋉-rewind` | **exact** — an *equality*, which is why neither case needs `⊢retag`. |
| **CancelR / IdPush** (outer) | nothing | `interior Θ₂ Δ` | `interior (rewind Θ₂) Δ ≡ pushBinds (binds Θ₂) Δ` | **exact**.  Only the inner boundary node sits there, and `_⋉_` **reapplies** Θ₂'s whole change list at the tail, where `applyChanges` runs it first.  Both conversions are **re-minted** (`mkId`/`unseal`), not transported.  `numBinds` is unchanged on both sides (`refl`). |
| **Drop$** | the numeral leaves its frame | `interior Θ Δ` | `Δ` | **vacuous**.  This is a frame change in the *other* direction — the bind prefix disappears and Θ's locks lift, so the new frame is strictly *more* nameable — but a numeral names no type variable: `⊢$` types it at every type context (`Drop$-vacuous`).  No other term can take the step: the rule's LHS interior is the **numeral itself** (`Drop$-only-numerals`), and progress needs no more because a closed value at a base type *is* a numeral (`canon-base`). |
| **ξ-Λ / ξ-⟪⟫ / ξ-·-l / ξ-·-r / ξ-·[]** | nothing | — | — | **exact**.  Each reduces a subterm *in place*, at the very context the corresponding typing rule reads it on: `unmasked abst ∷ Δ` is `⊢Λ`'s premise context, `interior Θ Δ` is `env`'s.  Both `refl`. |

Not rules, and therefore not sites: `⊢rename`, `⊢retag`, `Ren-wk`,
`Ren-addLock0`, `renᴹ`, `renⁿ`, `⊢renⁿ`, `⊢weakenⁿ`,
`canon-renᴹ`/`canon-renⁿ`.  These are transports the cases above are
*proved with*; each one's `Ren`/`⊑ᵃ` argument is supplied at the site.
`Eval` constructs no terms (`step` is `progress`), and `Show` is a
printer.

**Dead machinery.**  `shiftᵐ = renⁿ suc` (`TermSubst` §5) and
`canon-shiftᵐ` (`proof/Canonicity`) have **no consumers** after #199:
frame-exact substitution weakens an image with `shiftᴵ`, which is `there`
on a variable image and the identity on a value image, so the
term-variable shift is never applied to a term.  `renⁿ` itself is live —
`⊢renⁿ` at the identity renaming is what proves `⊢weakenⁿ`.  *Recorded,
not deleted; an audit proposes.*

## The TyPeelR leak, in detail — what was there before the split

The rule, as it stood:

    TyPeelR : Value V
      → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

`V` moved from `interior Θ Δ` to
`interior (morph (A ∷ binds Θ) (changes Θ)) Δ`, which `interior-TyPeelR`
says is that same context with **one new entry at slot 0** — and the entry
was `unmasked (bind (shiftBy (numBinds Θ) A))`.

Four machine-checked facts pinned the verdict, and all four still stand as
statements about frames:

* `TyPeelR-slot0-nameable` — the new frame **has** the slot, nameably
  (`∋tv 0`), so `TyPeelR-slot0-typeable` gives `⊢ᵗ ` 0` at V's position.
* `TyPeelR-V-tight` — **V did not need it.**  The old proof's own
  `⊢wkV = ⊢rename Ren-wk Inj-suc ⊢V` goes through **verbatim** with the
  head entry `masked (bind C)`, because `Ren-wk : Ren suc Δ (E ∷ Δ)` holds
  for *every* entry `E`.  So the `unmasked` was strictly more than V uses.
* `TyPeelR-node-needs-slot0` — **the instantiation node did.**  With the
  slot masked, `·[ … , ` 0 ]`'s `⊢·[]` premise `⊢ᵗ ` 0` is refused.  V and
  the node shared one frame, so *no repair was possible without changing
  the contractum's shape* — which is why the fix is a split and not a
  side condition.
* `TyPeelR-leak-⊑` / `TyPeelR-leak-¬⊑ᵃ` — the sharpest form.  The tight
  frame and the offered frame differ by exactly one **`le-mu`**, the
  re-exposure clause, which is precisely the step `_⊑ᵃ_` — the refinement
  a **term** may travel along — refuses.  The single rule moved V along a
  frame change that is `⊑` but not `⊑ᵃ`.

**The witness** (`§3a`, Examples-style, at `Δᵃ = unmasked (bind ℕ) ∷ []`,
`Θᵃ = morph [] (lock 0 ∷ [])`).  V's frames were

    Ξold   = masked (bind ℕ) ∷ []
    Ξnew   = unmasked (bind ℕ) ∷ masked (bind ℕ) ∷ []      (the single rule)
    Ξtight = masked   (bind ℕ) ∷ masked (bind ℕ) ∷ []      (what V needs)

and `nmᵃ = ƛ X. x` at `X = ` 0` **types at `Ξnew`** (`⊢nmᵃ`) and is
**refused at `Ξtight`** for the one localized `wf-var` reason (`¬⊢nmᵃ`) —
Jeremy's tightness test, run on the *frame* instead of the rule.  And
`wkᴹ1-misses-nmᵃ : ∀ V → wkᴹ 1 V ≢ nmᵃ`: **no moved value could be it.**
So the extra nameability the frame granted was nameability that nothing at
that position could use.  The frame did not say the truth.

Note this was **not** a scope gain for the relation: an ill-typed V stayed
ill-typed, because `wkᴹ 1` sent the fault from slot 0 to slot 1.  The leak
was about **what the frame authorizes**, which is what Jeremy asked for.

The single `TyPeelR` was the **only** rule that put a moved subterm under
an *unmasked* new binder.  Peel masks its whole bind prefix ((†));
frame-exact Beta masks the crossed `Λ` (`interior-Beta-Λ`); TyBeta
introduces no new slot at all.

## The candidate fixes

### (a) Wrap V in the new binder's dual — **REFUTED, it loops**

    (wkᴹ 1 V ⟪ morph [] (lock 0 ∷ []) , mkId (`∀ Bᵢ↑) ⟫) ·[ Bᵢ↑ , ` 0 ]

The frame identity would be exact (`morph [] (lock 0 ∷ [])` *is*
`dual (morph (A ∷ []) [])`, the shape `crossΛ` mints), and the node keeps
its nameable slot.

**The hazard is structural.**  An identity conversion at a `∀` type is
*necessarily* a `` `∀ `` conversion: `conv-id` wants a base type and
`conv-idv` a variable, so `mkId (`∀ B) ≡ `∀ (mkId B)` (`mkId-∀`) is the
only spelling.  Hence the inserted layer is inert `I-all`
(`mkId-∀-inert`), hence the wrapped value under `·[ … ]` **is itself a
TyPeelR redex**.

Machine-checked in `§4`/`§4a` on the prototype relation `_⊢_-→ᵃ_`, which
is **kept** in `proof/ShiftAudit.agda` as a refutation record:

* `fixA-loop-step` — **in general**, a `loopShape` term steps to a
  `loopShape` term under one more boundary.  Both premises regenerate:
  `Value (wkᴹ 1 V)` is `value-wkᴹ`, and the conversion typing is `mkId-⊢`
  from the type's well-formedness alone.  **So the answer to "does TyPeelR
  require anything of `s` that `mkId` fails?" is NO** — `mkId` is exactly
  what the wrapper carries, and `mkId-⊢` types it wherever the type is well
  formed, which the wrapper's own `env` premise guarantees.
* `T₀ -→ᵃ T₁ -→ᵃ T₂` on the closed instance
  `((ΛY. 3) ⟪ · , (∀Y. id ℕ) ⟫) [ℕ]`: the `Λ` is still buried under a
  fresh `morph [] (lock 0 ∷ [])` layer at `T₂`, so `TyBeta` never fires
  and the term grows by one boundary per step.

Excluding identity conversions from TyPeelR is not an option: the
classification is by **conversion constructor** and inspects no type
(`Design.md` §5), and progress needs *some* rule for an `I-all` layer under
`·[]`.

### (b) Split on the interior — **the Λ half, INSTALLED as `TyPeelR-Λ`**

`proof/Canonical.canon-∀` says a closed value at a `∀` type is a `Λ` over
a value **or** a wrapper with a `∀` conversion, nothing else.  So TyPeelR
splits, and the `Λ` half is now the live rule:

    TyPeelR-Λ  : Value N
      → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ N ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

**Frame verdict: exact up to refinement — TyBeta's own step.**  `N`
already lives one `abst` binder in (`⊢Λ`), so the new `bind` slot is a slot
`N` **could already name**: the move is
`TyPeelR-Λ-refinement : (unmasked abst ∷ interior Θ Δ) ⊑ᵃ interior (morph (A ∷ binds Θ) (changes Θ)) Δ`
— `la-uu le-ab`, **`⊑ᵃ`-legal**, in flat contrast to the old rule's
`le-mu`.  And **there is no shift at all**: no `wkᴹ`, no `⊢rename`, no
`ren-suc-[0]`.

* **Preservation** (`proof/Preserve.preserve-TyPeelR-Λ`).  It is the old
  proof with `int` replaced by `⊢retag (refine …) ⊢N`; the frame,
  conversion and exterior premises are the old proof **verbatim**.  The
  repair costs nothing.
* **Determinism** (`Reduction.det`).  The two clauses' patterns are
  disjoint (a `Λ` is not a boundary).  Bonus: `TyPeelR-Λ`'s contractum
  does not mention `Bᵢ`, so it is determined by the redex **without**
  `conv-src-unique`.
* **Progress** (`proof/Progress.progress-·[]-∀conv`).  `canon-∀` hands the
  split exactly its two patterns; the premises come off the redex's own
  derivation (`canon-∀` for the value, `conv-all-inv` for the conversion
  typing), in one inversion.
* **Value/ξ overlap: unchanged.**  `(Λ N) ⟪ Θ , `∀ s ⟫` is a value iff
  `Value N`, and the rule carries `Value N` — the same guard `TyBeta`
  carries.

**(b) alone would be partial.**  In the wrapper case the moved subterm is
the boundary `W ⟪ Θ′ , `∀ s′ ⟫`, and the leak above applies to it
verbatim: it too would be put under the unmasked new bind.  The tower is
finite and bottoms out at the `Λ`, so the leak would recur at most
`height` times — it would not grow, but it would still be there.  (b′)
closes that half, so the pair is a complete repair.

### (b′) The wrapper half, closed the same way — **INSTALLED as `TyPeelR-⟪⟫`**

`canon-∀` says the thing being moved in the wrapper case **is a boundary**,
and a boundary carries its own change list.  So mask the new binder in the
moved boundary's **own** frame — no second wrapper (which loops), nothing
resolved (which is (c)'s price):

    addLock0 Θ = morph (binds Θ) (changes Θ ++ (lock 0 ∷ []))

appended at the **tail**, where `applyChanges` runs it **first** — exactly
the position the scope move `_⋉_` puts its travelling changes in.  It
lives in `strong.CtxMorph` §5, with its induced-context identities:
`interior (addLock0 Θ) Δ ≡ interior Θ (mask 0 Δ)` and
`convCtx (addLock0 Θ) Δ ≡ convCtx Θ Δ` (the lock is **lifted** on the
conversion context, which is what makes the repair free).  At the shift
the rule performs (`strong.TermSubst.interior-addLock0-cross`):

    interior (addLock0 (renᴮ suc Θ′)) (unmasked (bind C) ∷ Δ)
      ≡ pushBinds (map ⇑ᵗ (binds Θ′)) (masked (bind C) ∷ scope Θ′ Δ)

i.e. the moved boundary's frame is its **birth frame** with the new binder
inserted below the bind prefix and **masked** — the shape (†) gives Peel
and `interior-Beta-Λ` gives Beta.  And it crosses by `⊢rename` **alone**:

    Ren-addLock0 : Ren (extN (numBinds Θ′) suc) (interior Θ′ Δ)
                       (pushBinds (map ⇑ᵗ (binds Θ′)) (E ∷ scope Θ′ Δ))

which is exactly the renaming `wkᴹ 1` performs on a boundary
(`renᴹ`'s wrapper clause).  The appended `lock 0` is legal where it acts
because slot 0 of the new frame is nameable (`addLock0-sw-l`) — *the
leak's own slot is what authorizes the lock that closes it*.

#### The rule, as installed (`Reduction.agda`)

    TyPeelR-⟪⟫ : Value W
      → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ ((renᴹ (extN (numBinds Θ′) suc) W
                 ⟪ addLock0 (renᴮ suc Θ′)
                 , `∀ (renᶜ (extᵗ (extN (numBinds Θ′) suc)) s′) ⟫)
                ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

**No extra premise.**  `Value W` and the conversion typing are the old
rule's own two premises, and `Value W` is what `canon-∀` hands progress.

**It is `wkᴹ 1` plus one lock, on the nose.**  With `addLock0ᵛ` the
change-list append lifted to a term (`addLock0ᵛ (M ⟪ Θ , c ⟫) = M ⟪ addLock0 Θ , c ⟫`),

    TyPeelR-⟪⟫-wkᴹ : addLock0ᵛ (wkᴹ 1 (W ⟪ Θ′ , `∀ s′ ⟫))
                       ≡ renᴹ (extN (numBinds Θ′) suc) W
                           ⟪ addLock0 (renᴮ suc Θ′)
                           , `∀ (renᶜ (extᵗ (extN (numBinds Θ′) suc)) s′) ⟫

is `refl`, and `TyPeelR-⟪⟫-outer-unchanged` says the whole contractum is
the old contractum with `addLock0ᵛ` applied to the moved value: same outer
frame `morph (A ∷ binds Θ) (changes Θ)`, same minted conversion
`instReveal 0 s`, same pushed-in annotation `renameᵗ (extᵗ suc) Bᵢ`, same
type argument `` ` 0 ``.

#### The two clauses on an example

The tightness redex of `Examples` §15b (`Δᵇ = X := ℕ`; the outer frame
locks `X`, the inner frame is trivial), machine-rendered:

    showTmIn 1 Rᵇ′
      = (((λx:ℕ. (ΛY. 3) [X]) ⟪ (∀Y. id ℕ) ⟫) ⟪ ↓X , (∀Y. id ℕ) ⟫) [ℕ]

    showTmIn 1 Cᵇ′                                  -- TyPeelR-⟪⟫
      = (((λx:ℕ. (ΛZ. 3) [X]) ⟪ ↓Y , (∀Z. id ℕ) ⟫) [Y] ⟪ ↑Y:=ℕ , ↓X , id ℕ ⟫)

Against the old rule's contractum at that redex the entire repair is the
`↓Y` on the moved boundary, and it is the difference between a frame that
lies and one that does not:

    showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξᵇ-single
      =  Y := ℕ , ⌷[X := ℕ]           ← the LEAK: Y is offered
    showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξᵇ-split
      =  ⌷[Y := ℕ] , ⌷[X := ℕ]        ← TyPeelR-⟪⟫: Y is masked

`⊢prb0-single` types a value that **names** the new slot `Y` at the old
frame; `¬⊢prb0-split` refuses the same value at the split's.  That is
§3a's `nmᵃ` test, run at the position the moved boundary's interior
actually occupies.  And the tightness test itself passes: `¬⊢Rᵇ′` and
`¬⊢Cᵇ′` refuse the redex and the contractum for the **same** localized
reason (`wf-var` at a masked slot), one index apart.  The `Λ` clause gets
the same treatment at `Rᵇ`/`Cᵇ` (`¬⊢Rᵇ`, `¬⊢Cᵇ`), where no index moves at
all.

#### What is proven, and where it lives

| lemma | where | claim |
|-------|-------|-------|
| `addLock0`, `interior-addLock0`, `unlockedScope-addLock0`, `convCtx-addLock0`, `numBinds-addLock0` | `strong.CtxMorph` §5 | the appended lock is `mask 0` on the interior and **invisible** on the conversion context |
| `Ren-addLock0`, `interior-addLock0-cross`, `map-renᶠ-shiftScope` | `strong.TermSubst` | the crossing renaming and the frame identity at the shift the rule performs |
| `⊢addLock0-cross` | `strong.TermSubst` §6 | **the crossing lemma** — a boundary crosses one new bind slot, masking it in its own frame.  Reps by `⊢ʳ-ren`, changes by `⊢ˢ-++` (`⊢ˢ-ren` over the frame the lock leaves, `sw-l` for the lock), interior by `⊢rename` at `Ren-addLock0` **alone**, conversion by `conv-ren` at `ren-convCtx`.  The (b′) analogue of `⊢crossΛ` |
| `preserve-TyPeelR-Λ`, `preserve-TyPeelR-⟪⟫` | `proof/Preserve` §3 | **preservation** for the two clauses — the Λ clause is the old proof with `⊢retag` for `int`, the wrapper clause is the old proof with `⊢addLock0-cross` for `⊢wkV`; the outer `env` is verbatim in both |
| `preservation-TyPeelR-Λ`, `preservation-TyPeelR-⟪⟫` | `strong.Preservation` | the public per-rule statements |
| `det` | `strong.Reduction` | **determinism** over the whole rule set.  The two `TyPeelR` patterns are disjoint (a `Λ` is not a boundary); the wrapper case needs `conv-src-unique`, exactly as the old rule did, and the Λ case needs nothing |
| `progress-·[]-∀conv` | `proof/Progress` | **progress** — `canon-∀` hands the split exactly its two patterns, so the pair is TOTAL over canonical `∀`-values: the old rule is **replaced**, not supplemented |
| `TyPeelR-Λ-refinement`, `TyPeelR-Λ-no-shift`, `TyPeelR-Λ-slot0-old` | `proof/ShiftAudit` §5 | **frame exactness** of the Λ clause: criterion 2 alone, criterion 1 vacuous |
| `TyPeelR-⟪⟫-frame`, `TyPeelR-⟪⟫-birth`, `TyPeelR-⟪⟫-slot-locked` | `proof/ShiftAudit` §5c₁ | **frame exactness** of the wrapper clause, and that the new slot is **unnameable** there (`∋lk-¬∋tv`, `pushBinds-∋lk0`) |
| `TyPeelR-⟪⟫-wkᴹ`, `TyPeelR-⟪⟫-outer-unchanged` | `proof/ShiftAudit` §5c/§5c₁ | the contractum is the old one with `addLock0ᵛ` on the moved value and nothing else changed |
| `towerHeight`, `towerHeight-renᴹ`, `TyPeelR-⟪⟫-height`, `fixA-height-stalls`, `canon-∀-height`, `progress-Λ-at-0` | `proof/ShiftAudit` §5c₂ | **termination** (below) |
| `U₀ -→ U₁ -→ U₂`, `⊢U₀`/`⊢U₁`/`⊢U₂` | `proof/ShiftAudit` §5c₃ | the closed two-deep run, every state typed |
| `Rᵇ`/`Cᵇ`, `Rᵇ′`/`Cᵇ′` and their refutations | `Examples` §15b | the tightness tests for both clauses |

#### Termination — it is not (a)'s regress

The wrapper clause's contractum contains

    (… ⟪ addLock0 … , `∀ s″ ⟫) ·[ … , ` 0 ]

which *is* again a redex.  The measure that separates it from fix (a) is
the `∀`-value's **tower height** — the number of nested boundaries above
the `Λ`:

    towerHeight (M ⟪ Θ , c ⟫) = suc (towerHeight M)      towerHeight _ = 0

`towerHeight-renᴹ` says the shift does not change it (both candidates
shift), and then

    TyPeelR-⟪⟫-height : towerHeight (contractum's inner ∀-value)
                          ≡ towerHeight (redex's ∀-value) ∸ 1
    fixA-height-stalls : towerHeight (fix (a)'s inner ∀-value)
                          ≡ towerHeight (redex's ∀-value)

`TyPeelR-⟪⟫` **consumes** a boundary that was already there; (a) **mints**
a new one, so its measure stalls — and §4a's `T₀ -→ᵃ T₁ -→ᵃ T₂` is that
stall, twice.  So a redex of tower height `h` takes `h − 1`
`TyPeelR-⟪⟫` steps and then exactly one `TyPeelR-Λ` step
(`canon-∀-height`: a `∀`-value of height 0 is a `Λ`, `canon-∀` has no
third shape), and `TyPeelR-Λ` neither shifts nor locks anything.

#### The closed run (§5c₃)

The outer frame binds `X := ℕ` and the inner frame locks it, so the moved
boundary really does carry a change list for the appended lock to join:

    Θᵈ  = morph (`ℕ ∷ []) []        the OUTER frame
    Θᵈ′ = morph [] (lock 0 ∷ [])    the INNER frame

Machine-rendered:

    showTmIn 0 U₀
      = (((ΛY. 3) ⟪ ↓X , (∀Y. id ℕ) ⟫) ⟪ ↑X:=ℕ , (∀Y. id ℕ) ⟫) [ℕ]
                      │ TyPeelR-⟪⟫          tower height 2 → 1
                      ▼
    showTmIn 0 U₁
      = (((ΛZ. 3) ⟪ ↓X , ↓Y , (∀Z. id ℕ) ⟫) [Y] ⟪ ↑Y:=ℕ , ↑X:=ℕ , id ℕ ⟫)
                      │ ξ-⟪⟫ (TyPeelR-Λ)    tower exhausted
                      ▼
    showTmIn 0 U₂
      = ((3 ⟪ ↑Z:=Y , ↓X , ↓Y , id ℕ ⟫) ⟪ ↑Y:=ℕ , ↑X:=ℕ , id ℕ ⟫)

Read the moved boundary's change list across step 1: `↓X` becomes
`↓X , ↓Y` — the **shifted** original lock and the **new** lock, appended
at the tail.  Nothing else about the boundary changes and no wrapper
appears.  The frames:

    showTCtxAt 9 0 (λ _ → "X") Ξᵈ₁                    =  ⌷[X := ℕ]
    showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξᵈ₃
      =  ⌷[Y := ℕ] , ⌷[X := ℕ]

`Ξᵈ₁` is `W`'s birth frame and `Ξᵈ₃` its frame in the contractum: the same
frame with the new binder `Y` inserted **masked**.  Exact.

### (c) The resolve variant — exact for V, but it spells a representation inside

`Design.md` §9 / `Examples` §13c, options (v)/(vi) — already weighed and
recorded when the polarity index still stood:

    (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]  →  (V ·[ Bᵢ , A ]) ⟪ Θ , conceal/reveal … ⟫

No new bind, no shift, so **V's frame is unchanged: exact**.  It **types**
(`⊢Cb`, `⊢CbH` in `Examples` §13c are machine-checked).  The price is the
one §13c already names: it **resolves the binder**, writing the exterior's
representation `A` into the interior, which the interior may not see.  That
trades a *scope* leak for a *knowledge* leak — and knowledge is the thing
the binder-syntactic design (`Design.md` §3, Q1) exists to keep out.  The
grounded-invariants law says representations live only at their binder;
(c) copies one inward.  **Worse than the leak it fixes.**

## What landed

1. **(b), the `Λ` split** — `TyPeelR-Λ`.  It costs nothing (the old
   preservation proof minus the `⊢rename`), it removes the shift entirely
   from the case where the instantiation actually happens, and it makes
   TyPeelR's `Λ` case *the same step as TyBeta* — which is what §6.4's own
   commentary always said it morally was ("TyPeelR's reveal case really is
   TyBeta's mint, one `∀` inside").
2. **(b′), the wrapper split** — `TyPeelR-⟪⟫`.  With (b) and (b′)
   together, **every rule that moves a subterm masks what it introduces**,
   and the §7 table has no exceptions.
3. **(a) was not taken** — machine-refuted, it loops; the refutation
   (`_⊢_-→ᵃ_`, `fixA-loop-step`, `T₀ -→ᵃ T₁ -→ᵃ T₂`) is kept in
   `proof/ShiftAudit` §4/§4a.  **(c) was not taken** — it converts a scope
   leak into a knowledge leak, which the design forbids.
4. Optionally delete `shiftᵐ`/`canon-shiftᵐ` (dead after #199).  Not done.

**One side effect worth recording.**  The `Λ` clause performs the
instantiation itself, so no `(Λ …) ·[ … , ` 0 ]` is left behind for
`TyBeta` to consume: one type instantiation now mints **one** binder where
the old rule pair minted two.  Runs therefore get shorter — `Examples`
§13a's `J` is eleven steps rather than fourteen, §14's `E` five rather
than six, and §3's birth story is one step, landing on `T₈′` (T₈ with the
fused layer gone) instead of on `T₈`.
