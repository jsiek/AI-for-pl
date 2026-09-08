# The shift audit — every place a rule moves a subterm

**Jeremy, 2026-09-08.**  "Frame exactness is the main point of Strong
System F!"  (PR #199: `Beta` now wraps every value crossing a `Λ` in that
binder's dual, `crossΛ`.)  Request: *audit all places that shift a term to
see if we have forgotten to mask type variables in other places.*

Machine-checked companion: `proof/ShiftAudit.agda` (in `All.agda`; the
gate `make -C strong check` is green).  The frame-identity table it feeds
is `Design.md` §7; the per-rule tightness tests are `Examples` §15 and
`proof/DualTightness`.

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
| **TyPeelR** (`V`) | `wkᴹ 1 V` | `interior Θ Δ` | `unmasked (bind (shiftBy (numBinds Θ) A)) ∷ interior Θ Δ` — `interior-TyPeelR` | ****LEAK****.  The new slot 0 is offered **unmasked**; `V` neither had it nor uses it.  *Repaired on the probe branch — (b)+(b′) below, `proof/ShiftAudit` §5c.* |
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
`renᴹ`, `renⁿ`, `⊢renⁿ`, `⊢weakenⁿ`, `canon-renᴹ`/`canon-renⁿ`.  These are
transports the cases above are *proved with*; each one's `Ren`/`⊑ᵃ`
argument is supplied at the site.  `Eval` constructs no terms (`step` is
`progress`), and `Show` is a printer.

**Dead machinery.**  `shiftᵐ = renⁿ suc` (`TermSubst` §5) and
`canon-shiftᵐ` (`proof/Canonicity`) have **no consumers** after #199:
frame-exact substitution weakens an image with `shiftᴵ`, which is `there`
on a variable image and the identity on a value image, so the
term-variable shift is never applied to a term.  `renⁿ` itself is live —
`⊢renⁿ` at the identity renaming is what proves `⊢weakenⁿ`.  *Recorded,
not deleted; an audit proposes.*

## The TyPeelR leak, in detail

The rule:

    TyPeelR : Value V
      → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

`V` moves from `interior Θ Δ` to
`interior (morph (A ∷ binds Θ) (changes Θ)) Δ`, which `interior-TyPeelR`
says is that same context with **one new entry at slot 0** — and the entry
is `unmasked (bind (shiftBy (numBinds Θ) A))`.

Four machine-checked facts pin the verdict:

* `TyPeelR-slot0-nameable` — the new frame **has** the slot, nameably
  (`∋tv 0`), so `TyPeelR-slot0-typeable` gives `⊢ᵗ ` 0` at V's position.
* `TyPeelR-V-tight` — **V does not need it.**  The live proof's own
  `⊢wkV = ⊢rename Ren-wk Inj-suc ⊢V` goes through **verbatim** with the
  head entry `masked (bind C)`, because `Ren-wk : Ren suc Δ (E ∷ Δ)` holds
  for *every* entry `E`.  So the `unmasked` is strictly more than V uses.
* `TyPeelR-node-needs-slot0` — **the instantiation node does.**  With the
  slot masked, `·[ … , ` 0 ]`'s `⊢·[]` premise `⊢ᵗ ` 0` is refused.  V and
  the node share one frame, so *no repair is possible without changing the
  contractum's shape*.
* `TyPeelR-leak-⊑` / `TyPeelR-leak-¬⊑ᵃ` — the sharpest form.  The tight
  frame and the live frame differ by exactly one **`le-mu`**, the
  re-exposure clause, which is precisely the step `_⊑ᵃ_` — the refinement
  a **term** may travel along — refuses.  TyPeelR moves V along a frame
  change that is `⊑` but not `⊑ᵃ`.

**The witness** (`§3a`, Examples-style, at `Δᵃ = unmasked (bind ℕ) ∷ []`,
`Θᵃ = morph [] (lock 0 ∷ [])`).  V's frames are

    Ξold   = masked (bind ℕ) ∷ []
    Ξnew   = unmasked (bind ℕ) ∷ masked (bind ℕ) ∷ []      (the live rule)
    Ξtight = masked   (bind ℕ) ∷ masked (bind ℕ) ∷ []      (what V needs)

and `nmᵃ = ƛ X. x` at `X = ` 0` **types at `Ξnew`** (`⊢nmᵃ`) and is
**refused at `Ξtight`** for the one localized `wf-var` reason (`¬⊢nmᵃ`) —
Jeremy's tightness test, run on the *frame* instead of the rule.  And
`wkᴹ1-misses-nmᵃ : ∀ V → wkᴹ 1 V ≢ nmᵃ`: **no moved value can be it.**  So
the extra nameability the frame grants is nameability that nothing at that
position can use.  The frame does not say the truth.

Note this is **not** a scope gain for the relation: `Examples` §15b already
checks that an ill-typed V stays ill-typed, because `wkᴹ 1` sends the fault
from slot 0 to slot 1.  The leak is about **what the frame authorizes**,
which is what Jeremy asked for.

TyPeelR is the **only** rule that puts a moved subterm under an *unmasked*
new binder.  Peel masks its whole bind prefix ((†)); frame-exact Beta masks
the crossed `Λ` (`interior-Beta-Λ`); TyBeta introduces no new slot at all.

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

Machine-checked in `§4`/`§4a` on the prototype relation `_⊢_-→ᵃ_`:

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

### (b) Split on the interior — **the Λ half is exact, and proven**

`proof/Canonical.canon-∀` says a closed value at a `∀` type is a `Λ` over
a value **or** a wrapper with a `∀` conversion, nothing else.  So TyPeelR
can split (prototype `_⊢_-→ᵇ_`, `§5`):

    TyPeelR-Λ  : Value N
      → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ᵇ N ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

**Frame verdict: exact up to refinement — TyBeta's own step.**  `N`
already lives one `abst` binder in (`⊢Λ`), so the new `bind` slot is a slot
`N` **could already name**: the move is
`TyPeelR-Λ-refinement : (unmasked abst ∷ interior Θ Δ) ⊑ᵃ interior (morph (A ∷ binds Θ) (changes Θ)) Δ`
— `la-uu le-ab`, **`⊑ᵃ`-legal**, in flat contrast to the live rule's
`le-mu`.  And **there is no shift at all**: no `wkᴹ`, no `⊢rename`, no
`ren-suc-[0]`.

* **Preservation: PROVEN** (`preserve-TyPeelR-Λ`).  It is the live proof
  with `int` replaced by `⊢retag (TyPeelR-Λ-refinement …) ⊢N`; the frame,
  conversion and exterior premises are the live proof **verbatim**.  The
  repair costs nothing.
* **Determinism: PROVEN** (`detᵇ`).  The two patterns are disjoint (a `Λ`
  is not a boundary).  Bonus: `TyPeelR-Λ`'s contractum does not mention
  `Bᵢ`, so it is determined by the redex **without** `conv-src-unique` —
  the live rule needs that lemma only because its pushed-in annotation is
  premise-determined.
* **Progress: PROVEN** (`progressᵇ-·[]`).  `canon-∀` hands the split
  exactly its two patterns; the premises come off the redex's own
  derivation (`canon-∀` for the value, `conv-all-inv` for the conversion
  typing), as `proof/Progress.∀-conv-premise` already does.
* **Value/ξ overlap: unchanged.**  `(Λ N) ⟪ Θ , `∀ s ⟫` is a value iff
  `Value N`, and the rule carries `Value N` — the same guard the live rule
  and `TyBeta` carry.

**(b) alone would be partial.**  In the wrapper case the moved subterm is
the boundary `W ⟪ Θ′ , `∀ s′ ⟫`, and §3 applies to it verbatim: it too is
put under the unmasked new bind.  The tower is finite and bottoms out at
the `Λ`, so the leak would recur at most `height` times — it would not
grow, but it would still be there.  (b′) below closes that half, so the
pair is a complete repair.

### (b′) The wrapper half, closed the same way — **PROVEN, and it WORKS**

`canon-∀` says the thing being moved in the wrapper case **is a boundary**,
and a boundary carries its own change list.  So mask the new binder in the
moved boundary's **own** frame — no second wrapper (which loops), nothing
resolved (which is (c)'s price):

    addLock0 Θ = morph (binds Θ) (changes Θ ++ (lock 0 ∷ []))

appended at the **tail**, where `applyChanges` runs it **first** — exactly
the position the scope move `_⋉_` puts its travelling changes in.  Then
(`§5b`):

    interior-addLock0 :
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

#### The rule, as it type-checked (`proof/ShiftAudit` §5, `_⊢_-→ᵇ_`)

    TyPeelR-⟪⟫ : Value W
      → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ᵇ ((renᴹ (extN (numBinds Θ′) suc) W
                  ⟪ addLock0 (renᴮ suc Θ′)
                  , `∀ (renᶜ (extᵗ (extN (numBinds Θ′) suc)) s′) ⟫)
                 ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
                ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

**No extra premise.**  `Value W` and the conversion typing are the live
rule's own two premises, and `Value W` is what `canon-∀` hands progress.

**It is `wkᴹ 1` plus one lock, on the nose.**  With `addLock0ᵛ` the
change-list append lifted to a term (`addLock0ᵛ (M ⟪ Θ , c ⟫) = M ⟪ addLock0 Θ , c ⟫`),

    TyPeelR-⟪⟫-wkᴹ : addLock0ᵛ (wkᴹ 1 (W ⟪ Θ′ , `∀ s′ ⟫))
                       ≡ renᴹ (extN (numBinds Θ′) suc) W
                           ⟪ addLock0 (renᴮ suc Θ′)
                           , `∀ (renᶜ (extᵗ (extN (numBinds Θ′) suc)) s′) ⟫

is `refl`, and

    TyPeelR-⟪⟫-outer-unchanged

says the whole contractum is the **live** contractum with `addLock0ᵛ`
applied to the moved value: same outer frame `morph (A ∷ binds Θ) (changes Θ)`,
same minted conversion `instReveal 0 s`, same pushed-in annotation
`renameᵗ (extᵗ suc) Bᵢ`, same type argument `` ` 0 ``.

#### The rule on an example

The tightness redex of §5c₄ (`Δᵛ = X := ℕ`; the outer frame locks `X`, the
inner frame is trivial), machine-rendered:

    showTmIn 1 Rᵛ
      = (((λx:ℕ. (ΛY. 3) [X]) ⟪ (∀Y. id ℕ) ⟫) ⟪ ↓X , (∀Y. id ℕ) ⟫) [ℕ]

    showTmIn 1 Cᵛ-live                              -- the LIVE rule
      = (((λx:ℕ. (ΛZ. 3) [X]) ⟪ (∀Z. id ℕ) ⟫) [Y] ⟪ ↑Y:=ℕ , ↓X , id ℕ ⟫)

    showTmIn 1 Cᵛ                                   -- fix (b′)
      = (((λx:ℕ. (ΛZ. 3) [X]) ⟪ ↓Y , (∀Z. id ℕ) ⟫) [Y] ⟪ ↑Y:=ℕ , ↓X , id ℕ ⟫)

The entire repair is the `↓Y` on the moved boundary, and it is the
difference between a frame that lies and one that does not:

    showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξᵛ-live
      =  Y := ℕ , ⌷[X := ℕ]           ← the LEAK: Y is offered
    showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξᵛ-new
      =  ⌷[Y := ℕ] , ⌷[X := ℕ]        ← (b′): Y is masked

`⊢prb0-live` types a value that **names** the new slot `Y` at the live
frame; `¬⊢prb0-new` refuses the same value at (b′)'s.  That is §3a's
`nmᵃ` test, run at the position the moved boundary's interior actually
occupies.  And the §15b test itself passes: `¬⊢Rᵛ` and `¬⊢Cᵛ` refuse the
redex and the contractum for the **same** localized reason (`wf-var` at a
masked slot), one index apart.

#### What is proven

| lemma | claim |
|-------|-------|
| `TyPeelR-⟪⟫-wkᴹ` | the contractum's inner value is `addLock0ᵛ (wkᴹ 1 …)`, `refl` |
| `applyUnlocks-++`, `unlockedScope-addLock0`, `convCtx-addLock0` | the appended lock is **lifted**: the conversion context is the plainly renamed one |
| `⊢addLock0-cross` | **the crossing lemma** — a boundary crosses one new bind slot, masking it in its own frame.  Reps by `⊢ʳ-ren`, changes by `⊢ˢ-++` (`⊢ˢ-ren` over the frame the lock leaves, `sw-l` for the lock), interior by `⊢rename` at `Ren-addLock0` **alone**, conversion by `conv-ren` at `ren-convCtx`.  The (b′) analogue of `⊢crossΛ` |
| `preserve-TyPeelR-⟪⟫` | **preservation** — the live proof with `⊢wkV = ⊢rename Ren-wk Inj-suc` replaced by `⊢addLock0-cross`; the outer `env` is verbatim |
| `preserveᵇ` | preservation for the whole prototype, both clauses and `ξᵇ-⟪⟫` |
| `detᵇ` | **determinism** over all three clauses.  The two `TyPeelR` patterns are disjoint (a `Λ` is not a boundary); the wrapper case needs `conv-src-unique`, exactly as the live rule does |
| `progressᵇ-·[]` | **progress** — `canon-∀` hands the split exactly its two patterns, so the pair is TOTAL over canonical `∀`-values: the live rule is **replaced**, not supplemented |
| `TyPeelR-⟪⟫-frame`, `TyPeelR-⟪⟫-birth` | **frame exactness** — the moved boundary's interior is its birth frame `pushBinds (binds Θ′) (scope Θ′ (interior Θ Δ))` with the reps lifted (`map ⇑ᵗ`) and the new slot inserted **masked** below the bind prefix |
| `TyPeelR-⟪⟫-slot-locked` | the new slot is **unnameable** there (`∋lk-¬∋tv`, `pushBinds-∋lk0`) |
| `TyPeelR-⟪⟫-outer-unchanged` | the outer boundary is the live rule's, untouched |
| `towerHeight`, `towerHeight-renᴹ`, `TyPeelR-⟪⟫-height` | **termination** (below) |
| `canon-∀-height`, `progressᵇ-Λ-at-0` | at tower height 0 the interior is a `Λ`, so `TyPeelR-Λ` fires |
| `U₀ -→ᵇ U₁ -→ᵇ U₂`, `⊢U₀`/`⊢U₁`/`⊢U₂` | the closed two-deep run, every state typed |

#### Termination — it is not (a)'s regress

The contractum's inner application

    (… ⟪ addLock0 … , `∀ s″ ⟫) ·[ … , ` 0 ]

*is* again a `-→ᵇ` redex.  The measure that separates it from fix (a) is
the `∀`-value's **tower height** — the number of nested boundaries above
the `Λ`:

    towerHeight (M ⟪ Θ , c ⟫) = suc (towerHeight M)      towerHeight _ = 0

`towerHeight-renᴹ` says the shift does not change it (both candidates
shift), and then

    TyPeelR-⟪⟫-height : towerHeight (contractum's inner ∀-value)
                          ≡ towerHeight (redex's ∀-value) ∸ 1
    fixA-height-stalls : towerHeight (fix (a)'s inner ∀-value)
                          ≡ towerHeight (redex's ∀-value)

(b′) **consumes** a boundary that was already there; (a) **mints** a new
one, so its measure stalls — and §4a's `T₀ -→ᵃ T₁ -→ᵃ T₂` is that stall,
twice.  So a redex of tower height `h` takes `h − 1` `TyPeelR-⟪⟫` steps
and then exactly one `TyPeelR-Λ` step (`canon-∀-height`: a `∀`-value of
height 0 is a `Λ`, `canon-∀` has no third shape), and `TyPeelR-Λ` neither
shifts nor locks anything.

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
                      │ ξᵇ-⟪⟫ (TyPeelR-Λ)   tower exhausted
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

#### Verdict

**(b) + (b′) WORKS.**  Preservation, determinism and progress all hold for
the pair; the two clauses are total over canonical `∀`-values, so the live
`TyPeelR` is *replaced*, not supplemented; both new frames are exact (the
`Λ` case up to `TyBeta`'s own refinement, the wrapper case up to the index
shift alone); the descent terminates on a strictly decreasing measure that
fix (a) leaves fixed; and tightness holds for both clauses.  No premise
had to be added, and nothing in `Reduction.agda`, `Preservation.agda`,
`Progress.agda` or `TypeSafety.agda` was touched — the probe lives
entirely in `proof/ShiftAudit.agda` §5/§5b/§5c.

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

## Recommendation

1. **Land (b) — the `Λ` split.**  It is written and proven in
   `proof/ShiftAudit.agda` (`TyPeelR-Λ`, `preserve-TyPeelR-Λ`, `detᵇ`,
   `progressᵇ-·[]`), it costs nothing (the live preservation proof minus
   the `⊢rename`), it removes the shift entirely from the case where the
   instantiation actually happens, and it makes TyPeelR's `Λ` case *the
   same step as TyBeta* — which is what §6.4's own commentary says it
   morally is ("TyPeelR's reveal case really is TyBeta's mint, one `∀`
   inside").
2. **Then land (b′) — the wrapper split.  It is now PROVEN too** (`§5c`):
   `preserve-TyPeelR-⟪⟫`, `detᵇ`, `progressᵇ-·[]`, the frame identity
   (`TyPeelR-⟪⟫-frame`, `TyPeelR-⟪⟫-slot-locked`), the terminating measure
   (`TyPeelR-⟪⟫-height` against `fixA-height-stalls`) and a closed
   two-deep run with every state typed.  With (b) and (b′) together,
   **every rule that moves a subterm masks what it introduces**, and the
   §7 table has no exceptions.
3. **Do not take (a)** — machine-refuted, it loops — and **do not take
   (c)** — it converts a scope leak into a knowledge leak, which the
   design forbids.
4. Optionally delete `shiftᵐ`/`canon-shiftᵐ` (dead after #199).

Until (b)/(b′) land in `Reduction.agda`, `Design.md` §7 carries the
**TyPeelR (V's frame)** row as the open item — the repair is proven on the
probe relation `_⊢_-→ᵇ_`, not installed in the live rules.
