# PR body draft — the context morphism becomes a PAIR

Branch `morph-pair`, on top of `main` @ `2c092f1e`.
Gate: `make -C SystemF/agda/strong check` passes, cold, exit 0
(`--safe`, no postulates/holes/pragmas).

## What changed

Jeremy's ruling (2026-09-06): the boundary's context morphism is not one
interleaved list.  Its two halves are different kinds of thing —
**binds are PARALLEL** (a block of binders whose representations are read
outside all of them) and **lock/unlock are SEQUENTIAL** — so the type
now says so.

```agda
data Change : Set where
  lock unlock : ℕ → Change          -- EXTERIOR indices, name only

record CtxMorph : Set where
  constructor morph
  field
    binds   : List Ty               -- PARALLEL block of binders
    changes : List Change           -- SEQUENTIAL, applied head-LAST
```

Field names are Jeremy's (`binds` / `changes`); the constructor is
`morph`.  The two *induced contexts* keep their old names because
`Design.md` and the lemma names use them:

```agda
applyChanges : List Change → Ctxᵗ → Ctxᵗ    -- locks AND unlocks, head-last
applyUnlocks : List Change → Ctxᵗ → Ctxᵗ    -- unlocks only (locks skipped)

scope         Θ Δ = applyChanges (changes Θ) Δ
unlockedScope Θ Δ = applyUnlocks (changes Θ) Δ
interior      Θ Δ = pushBinds (binds Θ) (scope Θ Δ)
convCtx       Θ Δ = pushBinds (binds Θ) (unlockedScope Θ Δ)
```

`repsOf` is gone — it *is* the field `binds`.  `scopeOf` became
`shiftScope`.  The derived morphisms are re-expressed at the pair:

```agda
dual   Θ = morph [] (hideBinds (numBinds Θ)
                       ++ dualScope (numBinds Θ) (changes Θ))
rewind Θ = morph (binds Θ) (dualScope 0 (changes Θ) ++ changes Θ)
Θ₁ ⋉ Θ₂  = morph (binds Θ₁)
                 (changes Θ₁ ++ shiftScope (numBinds Θ₂) (changes Θ₂))
```

and the two minting rules: `TyBeta` mints `morph (A ∷ []) []`, `TyPeelR`
mints `morph (A ∷ binds Θ) (changes Θ)` (change indices are exterior and
stay unshifted by the morphism's own binds — unchanged).

`Δ ⊢ᵐ Θ` is a **pair of judgements**, one per half:

```agda
data _⊢ʳ_ : Ctxᵗ → List Ty → Set where        -- the PARALLEL reps
  rw[] : Δ ⊢ʳ []
  rw-b : Δ ⊢ᵗ A → Δ ⊢ʳ Bs → Δ ⊢ʳ (A ∷ Bs)

data _⊢ˢ_ : Ctxᵗ → List Change → Set where    -- the SEQUENTIAL changes
  sw[] : Δ ⊢ˢ []
  sw-l : applyChanges S Δ ∋tv X → Δ ⊢ˢ S → Δ ⊢ˢ (lock X ∷ S)
  sw-u : applyChanges S Δ ∋lk X → Δ ⊢ˢ S → Δ ⊢ˢ (unlock X ∷ S)

record _⊢ᵐ_ (Δ : Ctxᵗ) (Θ : CtxMorph) : Set where
  constructor mw
  field
    mw-reps    : unlockedScope Θ Δ ⊢ʳ binds Θ
    mw-changes : Δ ⊢ˢ changes Θ
```

## The one semantic change

The interleaved list read a bind's representation past **its own tail's**
unlocks (`mw-b : unlockedScope Θ′ Δ ⊢ᵗ A → … → Δ ⊢ᵐ (bind A ∷ Θ′)`).  The
pair reads **every** representation past the **whole** change list.  This
is the one thing the refactor changes about what is derivable, and it is
strictly **more permissive** — a rep may now name a slot that an unlock
*to its left in the old list* re-exposed.  It is also the point: a
parallel block has no left and no right.

Consequences observed, in full:

* **No `⊢ᵐ` derivation in the development needed the tighter reading, and
  none needed the looser one.**  Exactly one morphism in the whole tree
  had a change to the left of a bind under the old order —
  `rewind Θ₆ = lock 0 ∷ bind (` 0) ∷ unlock 0 ∷ []` in
  `proof/MwUObstruct` §4 — and there the two readings *coincide*, because
  the entry to the left is a `lock` and `applyUnlocks` skips locks.
  Every other morphism has all its binds before all its changes, where
  the two readings are the same.  So: no example was refused, and none
  needed the extra permissiveness.
* **One lemma pays for it:** `proof/MoveScope.⊢ᵐ-rewind`.  A rewound
  frame's change list is `dualScope 0 (changes Θ) ++ changes Θ`, and the
  inverse half turns `Θ`'s *locks* into *unlocks* — so under the pair the
  reps of `rewind Θ` are read on a context with those extra unmasks
  applied.  That is more nameable, so the proof gains one `⊢ʳ-⊑` step
  (with a `subst` along `applyUnlocks-++`).  Under the interleaved list
  the reps sat inside the appended `Θ` tail and were read unchanged.
* **No theorem is weakened.**  `_⊢ᵐ_` is a premise of `env`, so a more
  permissive `_⊢ᵐ_` admits a (very slightly) larger set of typed terms;
  `preservation`, `progress`, `det`, `value-¬step`, tightness and
  canonicity are all reproved over the new judgement with their
  statements unchanged.

## Lemma-count deltas

Genuinely **deleted** (8), all of them projection/filtering lemmas about
`repsOf` that the record field makes definitional:

| module | deleted |
|--------|---------|
| `proof/PeelDual` | `repsOf-hideBinds`, `repsOf-++`, `repsOf-dualScope`, `repsOf-dual` |
| `proof/MoveScope` | `repsOf-scopeOf`, `repsOf-⋉`, `repsOf-rewind` |
| `TermSubst` | `repsOf-ren` |

Became `refl` (3), and their uses (three `rewrite`s, one `subst`) were
deleted with them:

    numBinds-dual   Θ     : numBinds (dual Θ)    ≡ 0            -- refl
    numBinds-⋉      Θ₁ Θ₂ : numBinds (Θ₁ ⋉ Θ₂)  ≡ numBinds Θ₁  -- refl
    numBinds-rewind Θ     : numBinds (rewind Θ)  ≡ numBinds Θ   -- refl

`numBinds-ren` is now `map-length` directly (it was `trans (cong length
repsOf-ren) map-length`).  `wf-convCtx-rewind` lost its `subst`;
`interior-rewind` lost a `rewrite`; `preserve-Peel`'s `⊢s-tr` lost its
`rewrite numBinds-dual`; `preserve-IdPush`/`preserve-CancelR` lost their
`rewrite numBinds-⋉`; `MoveScope.moved-conv` lost its
`rewrite numBinds-rewind`.

**Dead cases removed.**  Every induction over the change list lost its
`bind` case (26 functions/lemmas: `applyChanges`, `applyUnlocks`,
`applyChanges⊑applyUnlocks`, `Δ⊑applyUnlocks`, `⊑-applyChanges`,
`⊑-applyUnlocks`, `⊑ᵃ-applyChanges`, `dualScope`, `shiftScope`,
`ren-applyChanges`, `ren-applyUnlocks`, `⊢ˢ-⊑ᵃ`, `⊢ˢ-ren`,
`applyChanges-++`, `applyUnlocks-++`, `applyChanges-dualScope`,
`⊢ˢ-dualScope`, `dualScope-unmask-comm`, `applyUnlocks-dualScope`,
`⊢ˢ-++`, `applyChanges-shiftScope`, `applyUnlocks-shiftScope`,
`⊢ˢ-shiftScope`, `applyUnlocks-∋bind`, `locksOnly`, `dropL`), and every
induction over the reps lost its `lock`/`unlock` cases (`⊢ʳ-⊑`,
`⊢ʳ-ren`).

**Split, not added.**  `⊢ᵐ-⊑ᵃ` and `⊢ᵐ-ren` survive with their statements
unchanged and now delegate to `⊢ʳ-⊑`/`⊢ˢ-⊑ᵃ` and `⊢ʳ-ren`/`⊢ˢ-ren`.
`⊢ᵐ-++` is gone; the *append* lemma is now the rep-free `⊢ˢ-++`, which is
where the simplification shows: the old `⊢ᵐ-++` had a `bind` case that
had to move a rep from `scope Ψ Δ` to `unlockedScope Ψ Δ` along `⊑-wf`,
and the new one has no rep in it at all.  `⊢ᵐ-hideBinds`/`⊢ᵐ-dualScope`/
`⊢ᵐ-scopeOf` became `⊢ˢ-hideBinds`/`⊢ˢ-dualScope`/`⊢ˢ-shiftScope` and
likewise lost their `bind` cases.

Per-module declaration counts (old → new): `CtxMorph` 23 → 30 (five of
the seven additions are one-line morphism-level wrappers kept so
`scope Θ Δ`/`unlockedScope Θ Δ` and their transports keep their names),
`proof/PeelDual` 33 → 29, `proof/MoveScope` 34 → 32, `TermSubst` 35 → 39
(the four additions are the two `renᶠ`-level list functions and the two
halves of `⊢ᵐ-ren`).

**Was `⊢ᵐ-⋉` easier, as predicted?**  Half of it.  Its two obligations
now split cleanly and each is one step: the changes are `⊢ˢ-++` at the
move (nothing to carry), and the reps are `⊢ʳ-⊑` along
`⊑-applyUnlocks (changes Θ₁) (⊑-pushBinds (binds Θ₂)
(applyChanges⊑applyUnlocks (changes Θ₂) Δ))`.  Net length is about the
same as before: the `⊑-wf` step that used to hide inside `⊢ᵐ-++` is now
visible at the one place that needs it, which is the honest form.

**Which lemma got harder:** `⊢ᵐ-rewind` (above) — four lines instead of
one.  Nothing else.

## Rendering deltas

None.  `Show.agda` renders the pair in its own order — all binds, then
all changes, then the conversion: `⟪ ↑X:=A , ↓Y , ↥Z , c ⟫`.  Every one
of `Examples`' 26 pinned rendering traces is byte-identical (they are
`refl` proofs and the module type-checks unchanged); the diff touches no
`showTmIn` line.  The only morphism in the tree whose old list order
differed from binds-then-changes is `rewind Θ₆` in `proof/MwUObstruct`,
which is never rendered.

`scripts/render_term.sh` still works unchanged, e.g.

    scripts/render_term.sh \
      'showBndIn 1 (morph (`ℕ ∷ []) (lock 0 ∷ unlock 0 ∷ [])) (id `ℕ)' \
      'open import strong.Types' 'open import strong.Conversion' \
      'open import strong.CtxMorph' 'open import Data.List using ([]; _∷_)'
    ⟪ ↑Y:=ℕ , ↓X , ↥X , id ℕ ⟫

## What was re-proved

Everything, with statements unchanged: `proof/PeelDual`
(`interior-dual` (†), `convCtx-dual`, `⊢ᵐ-dual`, `preserve-Peel`),
`proof/MoveScope` (the frame equalities, `⊢ᵐ-⋉`, `⊢ᵐ-rewind`,
`preserve-IdPush`, `preserve-CancelR`, and the lock-only refutation
`¬frame-locksOnly` on the pair witness
`Θ✗ = morph [] (unlock 0 ∷ lock 0 ∷ [])`), `proof/Preserve`,
`strong.Preservation`, `strong.Progress`, `det`, `value-¬step`,
`proof/Canonicity`, `proof/Adversary`, `proof/IdLayer`,
`proof/MaskFacts`, `proof/DualTightness`, `proof/MwUObstruct` (its
`dropLocks`/`bindsOnly` witnesses translated to the pair),
`proof/PreserveObstruct`, the 7 `evalTerms` regressions, and `Examples`
§1–§15.

## Docs

`Design.md` §2 (the record, the two halves, the rendering order), §3
(`applyChanges`/`applyUnlocks` under `scope`/`unlockedScope`), §4.2 (the
paired judgement, verbatim, and the one semantic move), §4.3 (what
`env`'s first premise checks), §6.3/§6.7 (`dual`, `rewind`, `⋉`,
`shiftScope`), §8 law 4 (simultaneity, now stated exactly), §9 (a new
bullet, *The pair*), Appendix A (names).  `README.md`: the module map
lines for `CtxMorph.agda`, `MoveScope.agda`, `MwUObstruct.agda`.
