# Proposed rule repairs: TyPeelR and CancelR (2026-09-05)

Status: PROPOSALS awaiting Jeremy's ruling.  Context: the v2 preservation
verdict (DECISIONS "v2 PRESERVATION VERDICT") refuted four rules; Peel is
fixed and proven (proof/PeelDual.agda); IdPush is right as formulated
and discharges over the RepWf invariant (proof/WallReach.agda,
`idPush-RepWf`); TyPeelR and CancelR remain.  Each proposal below is
shown before → after and run on the concrete example that broke it.

## 1. TyPeelR

### Current (Reduction.agda), with its two defects marked

```agda
TyPeelR : ∀ {Δ V Θ s B A} → Value V
  → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
      -→ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) B , ` 0 ])   -- (a) B is the EXTERIOR ∀-body;
                                                      --     the inner ·[] is typed INSIDE
           ⟪ bind A ∷ renᴮ suc Θ , s ⟫                -- (b) renᴮ suc double-counts:
                                                      --     prep already lifts past bind A
```

### Defect (b) — mechanical fix, refuted from closed source

Replace `renᴮ suc Θ` by plain `Θ`.  Witness (Examples §11c): the closed
program

    G₀ = ((ΛX. λx:X. ((ΛY. ΛZ. x)·[ℕ])·[ℕ])·[ℕ]) · 7

reaches `G₄ = ((ΛZ. 7⟪↓X, seal X⟫) ⟪ ↑Y:=ℕ , ∀Z. id X ⟫) [ℕ]` (typed) and
TyPeelR steps it to `G₅`, whose interior mentions `` ` 3 `` while the
pushed annotation says `` ` 2 `` — `¬⊢G₅` (untypeable).  The face here is
an identity, so the annotation defect (a) is NOT what fires: the
double-count alone kills it.  The frame identity that makes plain `Θ`
right is definitional:

    intC (bind A ∷ Θ) Δ ≡ bind (liftN (nbind Θ) A) ∷ intC Θ Δ     (= Ren-wk)

and `K₀ -→ K₁` (Examples §11c) shows the multi-bind frame TYPES once the
shift is removed.

### Defect (a) — the interior ∀-body is not syntactic: make it premise-determined

The inner `·[ Bᵢ , ` 0 ]` must carry the SOURCE face of `s` — what the
interior's own `⊢·[]` demands — not the exterior body `B`.  For `↑ˢ`
(reveal) faces `Bᵢ` is reconstructible syntactically (`unseal X ↦ ` X`,
`id A ↦ A`, `↦`/`∀` structural), but for a `↓ˢ` ∀-face — a POLYMORPHIC
ARGUMENT that crossed a Peel, reachable — a `seal`'s source is an owner's
REP, which the rep-free conversion does not carry.  It is, however,
DETERMINED by the conversion typing.  Proposal — the same move already
ruled for the `idc` faces (owner-lookup premises):

```agda
TyPeelR : ∀ {Δ V Θ s A Bᵢ Bₑ p} → Value V
  → (abst ∷ fceC Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ ∙ p            -- NEW: the face typing, read at the
                                                    --   ∀-body (under one abst) — gives
                                                    --   the INTERIOR body Bᵢ
  → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ ⟨exterior body⟩ , A ]
      -→ (wkᴹ 1 V ·[ Bᵢ′ , ` 0 ]) ⟪ bind A ∷ Θ , s ⟫  -- Bᵢ′ = Bᵢ re-based to the interior
                                                    --   frame with bind A at slot 0
```

Determinism: faces are functions of (type context, conversion) — `id A`
carries its face, `unseal X`/`seal X` faces come from the owner lookup
(`∋:=`-det), `↦`/`∀` are structural — so a `conv-faces-unique` lemma
(to prove alongside) closes the TyPeelR-vs-TyPeelR det case.  Progress
derives the premise for free by inverting the redex's `env` (its
conversion typing IS this fact, one `∀` inside), exactly as it recovers
the lookup premises today.  The `↑ˢ` special case (syntactic `srcOf`)
becomes a corollary, not a restriction.

## 2. CancelR

### Current, with the defect marked

```agda
CancelR : ∀ {Δ V Θ₁ Θ₂ X Y A} → Value V → fceC Θ₂ Δ ∋ Y := A
  → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
      -→ V ⟪ reps→bind (reps Θ₂) , idc A ⟫          -- drops Θ₁'s ENTIRE frame and
                                                    --   Θ₂'s unlocks; V was typed in
                                                    --   intC Θ₁ (intC Θ₂ Δ)
```

### Proposal — keep both frames, neutralize both faces

Composition happens only on the FACES, where `unseal ∘ seal = id` is the
algebra we already trust; the context morphisms stay put, so no `⊕`
returns:

```agda
CancelR : ∀ {Δ V Θ₁ Θ₂ X Y A} → Value V → fceC Θ₂ Δ ∋ Y := A
  → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
      -→ (V ⟪ Θ₁ , idc (liftN (nbind Θ₁) A) ⟫) ⟪ Θ₂ , idc A ⟫
```

On Q's cancel step (Examples §11, `Q₅ → Q₆`; Θ₁ = `↓X`, Θ₂ = `↑Y:=ℕ`):
today `7 ⟪ ↑Y:=ℕ , id ℕ ⟫`; proposed `(7 ⟪ ↓X , id ℕ ⟫) ⟪ ↑Y:=ℕ , id ℕ ⟫`
— one extra `Drop$` to reach `7`, and nothing dropped that `V` might
need.  On the §1 obstruction witness (`nbind Θ₁ = 1`, `V` naming Θ₁'s own
binder; proof/PreserveObstruct.agda) the old residue is untypeable and
the new one types — `V` retypes exactly where it was.  The active/inert
story is intact: `idc A` at a base type is ACTIVE (`Drop$` finishes it),
at a variable INERT (a legitimate transparent layer).

## The shared caveat, and why it is already covered

Both new contracta make an inner wrapper PRESENT A REP (`A`, resp. `Bᵢ`)
inside Θ₂'s interior — the common wall (DECISIONS "Peel FIXED and
PROVEN; CancelR/TyPeelR/IdPush share ONE wall").  proof/WallReach.agda
covers it: `unseal-scoped`/`cancelR-scoped` derive the needed
`intC Θ₂ Δ ⊢ᵗ A` from `RepWf` + `MaskOnly`, and `RepWf-dual` shows every
reachable Θ₂ satisfies `RepWf` (a Peel's locks never block a rep, no
side condition).  So these cases discharge OVER THE INVARIANT — not over
a rule premise Progress would have to supply — and the remaining debt
for that route is the Θ₂-`RepWf` term-level induction (its mint
obligations are already discharged).

## Validation plan

Land both as one rule-repair pass; each is validated by instantiating
the corresponding parameter of `strong.Preservation.Conditional`
(`TyPeelRCase`, `CancelRCase`), with `det`/`value-¬step` re-proven
against the new contracta and Examples' pinned traces (Q/D/R/K, run-P₀)
updated where a contractum shape changed.
