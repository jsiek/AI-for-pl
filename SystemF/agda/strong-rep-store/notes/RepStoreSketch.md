# Experiment 2 — a GLOBAL REPRESENTATION STORE instead of `binds`

Sketch, 2026-09-22 (revised the same day after Jeremy's remark that
addresses need not be a separate sort: "the addresses can just be
larger de Bruijn indices").  Jeremy: "removing the binds field from
Boundary and instead make that a global representation type store.  For
example, TyBeta would add the representation R to the type store."

Nothing here is implemented.  Every `Agda` block is the intended
statement, written against the current strong-rep-store names so that
the diff is readable rule by rule.  Decision points are marked **ASK**.

## 0. What moves where — one sentence

Today a boundary `M ⟪ boundary Rs χ , c ⟫` carries its own bind block
`Rs`, pushed as `bindR` entries onto the FRONT of the representation
context on the way in (`extendReps`), so every representation variable
is a de Bruijn index RELATIVE to the boundaries that enclose it, and
every rule that moves a subterm across a boundary re-indexes it
(`renᴹ²`, `renᴹᴿ`, `underRepBinds`, `SameConv`, `SameTyExt`).  The
experiment appends the bound representations at the END of the
representation context instead — the store is the `bindR` suffix of
`Ξ`, an address is just an index beyond the abstract prefix — so a
moved subterm is moved VERBATIM and a representation is written exactly
once, by the `TyBeta` that mints it.

The NAME MAP `names Δ : List RVar` (ordinary `X` ↦ its representation
variable) and the `lock`/`unlock` changes on it are UNCHANGED.  This is
the answer to the 2026-09-05 objection recorded at `DesignSpace.md` D33 →
D34 ("a global Σ-store, NOT taken — lexical scope is needed for lock
blocking"): that proposal stored the whole context; this one stores
only what `bindR` held.  The store says WHAT a representation is; `Δ`
says WHETHER this position may name it.  Lock blocking is still lexical.

**Why experiment 1 had to come first.**  With `ξ-Λ`, a `TyBeta` under a
`Λ` would append a payload mentioning the `Λ`'s own abstract variable,
and a later instantiation of that `Λ` would leave the cell pointing at a
binder that no longer exists.  With the value restriction nothing
reduces under `Λ`, so at every redex the abstract prefix of `Ξ` is the
AMBIENT one, fixed for the run — which is exactly what makes an
appended address stable.

## 1. Definitions

### 1.1 One sort of representation variable; the store is a suffix

`RVar = ℕ`, `Rep = Ty`, `RepCtx = List RepBinding` with `abstR`/`bindR`
— ALL AS TODAY.  What changes is the discipline on `Ξ`:

```agda
-- abstract binders are pushed at the FRONT (typing, under Λ);
-- cells are appended at the END (reduction, TyBeta):
--
--   Ξ = abstR ∷ … ∷ abstR ∷ bindR R₀ ∷ bindR R₁ ∷ … ∷ bindR Rₖ₋₁
--       └── n ambient Λ ──┘ └────────── the store ──────────┘
--                            address of cell j  =  n + j

allocate : RepCtx → Ty → RepCtx
allocate Ξ R = Ξ ∷ʳ bindR R        -- the fresh address is length Ξ
```

Nothing in the TYPE of `Ξ` enforces the shape; it holds because
`underΛ` is the only producer of `abstR` and `allocate` the only
producer of `bindR` (today `extendReps` was the other one).

**Payloads are spelled at the front.**  Today `_∋ʳ_:=_` shifts the
payload it finds on the way out (`r-here : (b ∷ Ξ) ∋ʳ zero :=
renRepBinding suc b`, one `suc` per `r-there`): each entry is spelled in
its own TAIL, the standard right-referring telescope.  A cell refers the
other way — to the ambient abstract prefix and to EARLIER cells, all to
its LEFT — so the lazy shift must go.  Every payload is spelled in the
whole `Ξ` it lives in, lookup returns it unchanged, and the one
operation that re-indexes `Ξ` — pushing a binder at the front — shifts
the stored payloads eagerly:

```agda
_∋ʳ_:=_ : RepCtx → RVar → RepBinding → Set
Ξ ∋ʳ α := b  =  Ξ ∋ˡ α := b                         -- no renRepBinding

underΛ : Ctxᵗ → Ctxᵗ
underΛ (Ξ ∣ Δ) = (abstR ∷ map (renRepBinding suc) Ξ) ∣ (zero ∷ shiftNames Δ)
```

`underΛ` is applied only by `⊢Λ` and by `conv-all`, i.e. in typing;
a run never shifts its store.  `crossΛᴹ`'s `renᴹ² (ren² idᵗ suc)` stays
exactly as it is: a value moving under a `Λ` shifts every representation
index by one, cells included, matching the eager shift of `Ξ`.

```agda
-- acyclic by construction: a cell may cite only what is to its left
WfRepCtx : RepCtx → Set
WfRepCtx Ξ = ∀ {i R} → Ξ ∋ˡ i := bindR R → take i Ξ ⊢ᴿ R
-- (abstR entries carry nothing; ValidNames and Unique are unchanged)

_⊑_ : RepCtx → RepCtx → Set            -- store extension, cells only
Ξ ⊑ Ξ′ = ∃[ Rs ] Ξ′ ≡ Ξ ++ map bindR Rs
```

`Ctxᵗ = Ξ ∣ Δ`, `empty`, `_⊢ᵗ_`, `_⊢ᴿ[_]_`, `_⊢_~_`, `_∋_:=_` all keep
their statements.  `pushRepBinds`, `extendReps`, `shiftRVars`, `_⊢ᴮ_`,
`RepRefines` are gone.

### 1.2 Boundaries: changes only

```agda
data Change : Set where
  lock   : ℕ → RVar → Change
  unlock : ℕ → RVar → Change

Boundary : Set
Boundary = List Change

dualBoundary Θ  = map dualChange (reverse Θ)             -- as today
rewind Θ        = dualBoundary Θ ++ Θ                     -- as today
Θ₁ ⋉ Θ₂         = Θ₁ ++ Θ₂           -- no underRepBinds: nothing shifts
addLock0 ℓ Θ    = Θ ++ (lock 0 ℓ ∷ [])         -- was lock 0 (numBinds Θ)
instantiate ℓ Θ = map shiftX Θ ++ (unlock 0 ℓ ∷ [])
                  -- shiftX bumps the ORDINARY index only; the new name 0
                  -- names the cell ℓ, not a bind slot
```

`numBinds`, `renᴮ²`, `renᴮᴿ` are gone.  The two readings lose their
`extendReps` prefix and become plain name-map transformers:

```agda
Δ ⊢ⁱ Θ ⇒ Δᵢ     -- every change applied     (interior)
Δ ⊢ᶜ Θ ⇒ Δᶜ     -- locks skipped            (conversion context)
-- step-unlock : reps Δ ∋ʳ α → names Δ ∌ʳ α → α ⊢+ names Δ at X ⇒ Δ′ → …
-- and  reps Δᵢ ≡ reps Δ ≡ reps Δᶜ : a boundary changes NAMES only
```

Consequently

```agda
Δ ⊢ A ≈ B ⊣ Δ′  =  ∃[ R ] (Δ ⊢ᶜ A ~ R × Δ′ ⊢ᶜ B ~ R)
```

is the ONLY cross-context type comparison: `SameTyExt (numBinds Θ) …`
collapses into it, because there is no bind prefix to cross.

### 1.3 Conversions cite representation variables  — **ASK (R2)**

```agda
data Conv : Set where          -- the DATATYPE is unchanged …
  id     : Ty → Conv           -- … but id's payload is a Rep (` α, or a base)
  seal   : RVar → Conv         -- … and seal/unseal cite the CELL, not the name
  unseal : RVar → Conv
  _↦_    : Conv → Conv → Conv
  `∀     : Conv → Conv
```

Today `seal X`, `unseal X`, `id (` X)` cite ORDINARY names, which is why
a conversion read in another name map must be RE-SPELLED (`SameConv`,
`respell`, the `s′`/`s″` premises of `Peel` and `TyPeelR-⟪⟫`, the
`≈`-premises of `CancelR`/`IdPush`).  With the payload in the
representation universe a conversion means the same thing in every name
map, and all of that respelling machinery is deleted.  This is GTSF's
`Conversion.agda` shape (`unseal α A` with `(α , A) ∈ Σ`), as
`RedesignAdvice.md` Q3 already noted.  `mkId : Ty → Conv` is UNCHANGED
as a function; the rules simply hand it the representation `R` instead
of the ordinary `A`.

The fallback R2-b keeps ordinary names and `SameConv`; the store still
removes every SHIFT, but not the respelling.

```agda
Δ ⊢ c ∶ A ⇝ B                       -- Δ = Ξ ∣ names, as today

conv-id     : Base A                → Δ ⊢ id A ∶ A ⇝ A
conv-idv    : Δ ∋ᵗ X := α           → Δ ⊢ id (` α) ∶ ` X ⇝ ` X
conv-seal   : Δ ∋ᵗ X := α → Δ ∋rep α := R → Δ ⊢ᶜ A ~ R
                                    → Δ ⊢ seal α ∶ A ⇝ ` X
conv-unseal : Δ ∋ᵗ X := α → Δ ∋rep α := R → Δ ⊢ᶜ A ~ R
                                    → Δ ⊢ unseal α ∶ ` X ⇝ A
conv-fun, conv-all : as today
```

`conv-seal`/`conv-unseal` still demand `Δ ∋ᵗ X := α`: the cell must be
NAMED in the conversion context.  A boundary whose changes lock `X`
cannot unseal `α` however many cells exist — abstraction is enforced by
the name map; the store only stores.  (Compare today's `Δ ∋ X := A`,
which bundles the same three facts keyed by `X`.)

Helpers: `reveal ℓ : Ty → Conv` (the body type read as a `Rep`, with
`unseal ℓ`/`seal ℓ` by polarity at the leaves that are `` ` ℓ ``, `id`
elsewhere), `instReveal ℓ` likewise composed with `s`.

## 2. Typing

The judgement keeps its shape, `Δ ∣ Γ ⊢ M ⦂ A` with `Δ = Ξ ∣ names`;
the store is `reps Δ`'s suffix.

```agda
⊢Λ   : Value N → underΛ Δ ∣ ⤊ Γ ⊢ N ⦂ C → Δ ∣ Γ ⊢ Λ N ⦂ `∀ C      -- as today
⊢·[] : as today

env : Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
    → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
    → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
    → Δ  ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ          -- was SameTyExt (numBinds Θ) Δ Bₑ Δᶜ Cₑ
    → Δ ⊢ᵗ Bₑ
    → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ
```

`BoundaryWf Δ Θ Δᵢ Δᶜ` shrinks to `WfCtx Δ` plus the two readings (its
`bw-binds` field has nothing to say).

Two lemma families replace `RepWeaken`/`RepRefines`:

```agda
⊢-⊑  : reps Δ ⊑ Ξ′ → Δ ∣ Γ ⊢ M ⦂ A → (Ξ′ ∣ names Δ) ∣ Γ ⊢ M ⦂ A
      -- and for ∶⇝, ⊢ⁱ/⊢ᶜ, ~, WfCtx: every judgement is monotone in the
      -- store, because nothing is ever read by "the last address".
      -- underΛ commutes with ⊑ (eager shift of the appended cells).

_[_]ᴿ : Term → RVar → Term
-- N [ ℓ ]ᴿ : representation index 0 ↦ ℓ, suc i ↦ i, in every
-- lock/unlock and every id/seal/unseal inside N.  Ordinary types in N
-- are untouched.  (It is renᴹ² (ren² idᵗ σ) for the non-injective
-- σ 0 = ℓ, σ (suc i) = i — the represent half of the paired renaming,
-- now a substitution.)
⊢[]ᴿ : Ξ′ ≡ Ξ ∷ʳ bindR R                -- ℓ = length Ξ
     → underΛ (Ξ ∣ Δ) ∣ ⤊ Γ ⊢ N ⦂ C
     → (Ξ′ ∣ (ℓ ∷ Δ)) ∣ ⤊ Γ ⊢ N [ ℓ ]ᴿ ⦂ C
```

`⊢[]ᴿ` is today's `⊢refine (rr-represent …)`: the abstract binder at
index 0 is REPLACED by the cell at the top index instead of being
re-tagged in place.  **ASK (R3):** this makes `TyBeta` substitute — in
the REPRESENTATION universe only.  The design law "TyBeta does not
substitute" (Design.md §6.1) survives as "does not substitute TYPES":
`N` keeps running at the ordinary `X`; only its pointers learn `ℓ`.
Since `N` is a value (experiment 1) the substitution never walks a
redex.

## 3. Reduction — the store is the context's suffix

```agda
Δ ⊢ M -→ M′ ∣ Ξ′        -- Ξ′ : the representation context AFTER the step;
                        -- Ξ′ = reps Δ except in the three ∀-eliminations
```

Below, `ℓ = length (reps Δ)` is the fresh address and
`Δ⁺ = allocate (reps Δ) R ∣ names Δ`.

```agda
TyBeta : Value N → Δ ⊢ᶜ A ~ R → underΛ Δ ⊢ᶜ B ~ Rᴮ
  → Δ ⊢ (Λ N) ·[ B , A ]
      -→ N [ ℓ ]ᴿ ⟪ unlock 0 ℓ ∷ [] , reveal ℓ (Rᴮ [ ℓ ]ᴿ) ⟫
      ∣ allocate (reps Δ) R
```

(today: `N ⟪ instantiate R (boundary [] []) , reveal 0 B ⟫`, the bind
`R` riding on the boundary.)

```agda
Beta : Value W → Δ ⊢ᶜ A ~ R
  → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ R ]ᵐ ∣ reps Δ
-- crossΛᴹ W R = renᴹ² (ren² idᵗ suc) W ⟪ lock 0 0 ∷ [] , mkId (⇑ᵗ R) ⟫
-- unchanged in shape; the wrapper's identity is built from the REP
```

`Beta` gains the reading premise because `mkId` needs the argument type
as a representation (under R2).  Under R2-b it stays exactly as today.

```agda
Peel : Value V → Value W
  → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
      -→ (V · (W ⟪ dualBoundary Θ , s ⟫)) ⟪ Θ , t ⟫ ∣ reps Δ
```

(today: `renᴹ² (ren² idᵗ (wkN (numBinds Θ))) W`, `s′` with
`SameConv Δᵈ s′ Δᶜ s`, and the three context-reading premises.  All
gone: `W` moves verbatim and `s` means the same thing in `Δᵈ`.)

```agda
TyPeelR-Λ : Value N → Δ ⊢ᶜ A ~ R
  → Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
      -→ N [ ℓ ]ᴿ ⟪ instantiate ℓ Θ , instReveal ℓ (s [ ℓ ]ᶜ) ⟫
      ∣ allocate (reps Δ) R

TyPeelR-⟪⟫ : Value W → Δ ⊢ᶜ A ~ R → (the Bᵢ′ reading, as today)
  → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
      -→ ((W ⟪ addLock0 ℓ (map shiftX Θ′) , `∀ s′ ⟫)
            ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
           ⟪ instantiate ℓ Θ , instReveal ℓ (s [ ℓ ]ᶜ) ⟫
      ∣ allocate (reps Δ) R
```

`s [ ℓ ]ᶜ` is `_[_]ᴿ` on a conversion.  In `TyPeelR-⟪⟫` the inner
boundary is moved WITHOUT `renᴹ²`, without `renᴮ² (ren² idᵗ suc)`, and
with `s′` unchanged — the `s″`/`SameConv`/`renNameCtx` premise cluster,
which is where the 2026-09-20 wall (`notes/AddLock0Wall.agda`) lived,
has nothing left to misspell.  `addLock0 ℓ` locks the NEW name `0`
(which names the cell `ℓ`) out of the moved interior, as today.

```agda
CancelR : Value V → Δ ∋rep α := R
  → Δ ⊢ (V ⟪ Θ₁ , seal α ⟫) ⟪ Θ₂ , unseal α ⟫
      -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId R ⟫) ⟪ rewind Θ₂ , mkId R ⟫ ∣ reps Δ

IdPush : Value V → Δ ∋rep β := R
  → Δ ⊢ (V ⟪ Θ₁ , id (` α) ⟫) ⟪ Θ₂ , unseal β ⟫
      -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal β ⟫) ⟪ rewind Θ₂ , mkId R ⟫ ∣ reps Δ
```

Today `CancelR` has eight premises (`seal X` at `Δ₁ᶜ`, `unseal Y` at
`Δᶜ`, two lookups, the `⋉`-reading, `Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ`) because the
two conversions spell one fact in two name maps.  Under R2 typing forces
the SAME `α` on both sides (`Δᵢ ⊢ ` X ≈ ` Y ⊣ Δᶜ` is `α ≡ β`), and the
minted identities are read off the store.  `IdPush` loses its
`` Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ `` re-spelling for the same reason.

`Drop$`/`Drop-true`/`Drop-false` and the four congruences are unchanged
(they pass the store through; `ξ-⟪⟫` runs the interior at the SAME
`reps`).  `value-¬step` is unchanged.  `det` gains the conclusion
`Ξ′ ≡ Ξ″`; it holds because the only allocation is at `length Ξ` and
`_~_` readings are functional.

## 4. The same programs, on the store

`P₀ = (ΛX. λx:X. x) [ℕ] · 7` — today's 6-step run
(`Examples` §1a; frames render binds as `↑α:=ℕ`):

```
((ΛX. λx:X. x) [ℕ] · 7)
 --TyBeta-->  ((λx:X. x) ⟪ ↑α:=ℕ , ↥X , seal X ↦ unseal X ⟫) · 7
 --Peel---->  ((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫
 --Beta---->  (7 ⟪ ↓X , seal X ⟫) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫
 --CancelR->  (7 ⟪ ↥X , ↓X , id ℕ ⟫) ⟪ ↑α:=ℕ , ↥X , ↓X , id ℕ ⟫
 --Drop$-->   7 ⟪ ↑α:=ℕ , ↥X , ↓X , id ℕ ⟫
 --Drop$-->   7
```

With the store (`Ξ` on the left, `α` = cell 0; `↥X:=α` is `unlock 0 α`):

```
Ξ = []            ((ΛX. λx:X. x) [ℕ] · 7)
 --TyBeta-->
Ξ = [α:=ℕ]        ((λx:X. x) ⟪ ↥X:=α , seal α ↦ unseal α ⟫) · 7
 --Peel---->      ((λx:X. x) · (7 ⟪ ↓X , seal α ⟫)) ⟪ ↥X:=α , unseal α ⟫
 --Beta---->      (7 ⟪ ↓X , seal α ⟫) ⟪ ↥X:=α , unseal α ⟫
 --CancelR->      (7 ⟪ ↓X , ↥X:=α , id ℕ ⟫) ⟪ ↥X:=α , ↓X , id ℕ ⟫
 --Drop$-->       7 ⟪ ↥X:=α , ↓X , id ℕ ⟫
 --Drop$-->       7
```

Same six rules, same shape.  What changed is invisible in the trace and
visible in the rule: `Peel` moved `7` without `renᴹ²` and reused `seal α`
without `SameConv`; `CancelR` fired on `Ξ ∋ α := ℕ` alone; the bind `ℕ`
was written once, in `Ξ`, instead of being carried by every frame the
value later passes through.

`Q₀` (`Examples` §2, the id-layer program) — the first `IdPush` step,
today:

```
(((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Y , id X ⟫) ⟪ ↑β:=ℕ , ↥Y , unseal X ⟫) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫
 --IdPush-->
(((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Y , id X ⟫) ⟪ ↑β:=ℕ , ↥X , ↥Y , unseal X ⟫) ⟪ ↑α:=ℕ , ↥X , ↓X , id ℕ ⟫
```

and with the store, `Ξ = [α:=ℕ , β:=ℕ]`:

```
(((7 ⟪ ↓X , seal α ⟫) ⟪ ↓Y , id α ⟫) ⟪ ↥Y:=β , unseal α ⟫) ⟪ ↥X:=α , unseal α ⟫
 --IdPush-->
(((7 ⟪ ↓X , seal α ⟫) ⟪ ↓Y , id α ⟫) ⟪ ↥Y:=β , ↥X:=α , unseal α ⟫) ⟪ ↓X , ↥X:=α , id ℕ ⟫
```

Note `id α`: today's `id X` had to be re-spelled as `id X′` when pushed
into the merged frame (the `` ` X′ ≈ ` X `` premise); the cell needs no
spelling.  The `↑β:=ℕ` bind that today rides on the middle frame is the
cell `β`, allocated by the inner `TyBeta`, and is never mentioned again
— the `↥Y:=β` unlock is the only trace of it, exactly as `↑β` today is
only ever reached through `↥Y`.

## 5. What the metatheory loses and gains

Retired outright: `RepWeaken.agda` (`renᴹᴿ`, `RepWk`, `⊢renᴿ`,
`cross-Λ-⊢`), `RepRefines`/`⊢refine` (47 uses in `proof/Preserve.agda`),
`SameConv`/`respell`/`SameTyExt`, `pushRepBinds`/`extendReps`/`numBinds`
arithmetic, `underRepBinds`, `renᴮ²`/`renᴮᴿ`, the lazy shift in
`_∋ʳ_:=_` (56 uses of `renRepBinding`/`r-there` in `proof/Ctx.agda`
become plain `∋ˡ` facts), and the `ShiftAudit` frame-exactness
obligations of `Peel`/`TyPeelR-⟪⟫` (no representation is ever moved).
`MoveScope.agda`'s `preserve-CancelR`/`preserve-IdPush` reduce to the
store lookup.

New: `allocate`, `_⊑_` and the monotonicity family `⊢-⊑` (the STLCRef
store-typing pattern, already in this repo), the leftward `WfRepCtx`,
`_[_]ᴿ` with `⊢[]ᴿ` (the represent half of `renᴹ²` at a non-injective
map), the eager shift in `underΛ`, `reveal ℓ`.

The theorem statements:

```agda
Preservation = ∀ {Δ Ξ′ M M′ A} → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ ∣ Ξ′
  → (reps Δ ⊑ Ξ′) × WfCtx (Ξ′ ∣ names Δ) × ((Ξ′ ∣ names Δ) ∣ [] ⊢ M′ ⦂ A)

Progress      = ∀ {Δ M A} → Δ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ ∃[ M′ ] ∃[ Ξ′ ] (Δ ⊢ M -→ M′ ∣ Ξ′)

det : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ ∣ Ξ′ → Δ ⊢ M -→ M″ ∣ Ξ″
  → M′ ≡ M″ × Ξ′ ≡ Ξ″
```

Color/scope-map preservation: the residual renaming `ρ` a move delivers
becomes the identity, so `ScopeMapPreservation` should become
`names Δ₂ ≡ names Δ₁` up to the unlock the boundary itself performs —
worth re-stating once the core is in.

## 6. Decision points, collected

- ~~R1~~ dissolved (2026-09-22): `RVar = ℕ`, `Rep = Ty`, `RepCtx`
  unchanged; cells are the indices beyond the abstract prefix.  The
  price is the spelling convention of §1.1 — payloads at the front,
  eager shift in `underΛ`, no lazy shift in lookup.
- **R2** conversions cite `RVar` (recommended; deletes all respelling)
  vs keep ordinary names and `SameConv` (R2-b; deletes only the shifts).
- **R3** `TyBeta`/`TyPeelR` perform `N [ ℓ ]ᴿ` — pointer substitution in
  the body.  The alternative, keeping the `Λ`'s slot as a lexical
  `abstR` and refining it in place, is today's design and is what the
  store is replacing; I see no third option.
- **R4** append at the END (`Ξ ∷ʳ bindR R`), so addresses are stable
  under allocation.  Pushing at the front would re-index every address
  on every allocation — the shift we are trying to eliminate.
- **R5** the ambient abstract prefix stays (needed to type `Λ` bodies
  and to state reduction at the probes' `underΛ empty`).

## 7. Suggested order of work

1. `Ctx.agda`: `_∋ʳ_:=_` without the lazy shift, eager `underΛ`,
   leftward `WfRepCtx`, `allocate`, `_⊑_`; `Boundary.agda` as
   `List Change` with the two readings; `Conversion.agda` on `RVar`
   (R2).  Statements only, then `Terms.agda`'s `env`.
2. `Reduction.agda` with the `∣ Ξ′` index, `_[_]ᴿ` in `TermSubst.agda`.
   `det` and `value-¬step`.
3. `TypeCheck.agda`/`Eval.agda`: `step` returns `Ξ′`; `eval` threads
   it; `Reaches` records the final store.  Rerun the 23 runs — their
   step counts should be UNCHANGED (no rule was added or split).
4. `proof/Preserve.agda`: the `⊢-⊑` family first, then rule by rule;
   `TyPeelR-⟪⟫` should be the big win.
5. Progress, type safety, then the color theorem's restatement.
