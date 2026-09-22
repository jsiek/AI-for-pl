# Experiment 2 — a GLOBAL REPRESENTATION STORE instead of `binds`

Sketch, 2026-09-22, fourth revision.  Jeremy: "removing the binds field
from Boundary and instead make that a global representation type store.
For example, TyBeta would add the representation R to the type store."
Then: addresses need not be a separate sort ("larger de Bruijn
indices"), and — the version this revision adopts — "use zero for the
fresh address and push all the existing addresses up by one.  That
means the ξ reduction rules all need to shift the rep vars in the
sibling terms, but that's just one easy lemma used in many places."
And: "have reduction return the change to the environment instead of
the new environment.  Then you don't need to deal with subtraction."

Nothing here is implemented.  Every `Agda` block is the intended
statement, written against the current strong-rep-store names so that
the diff is readable rule by rule.  Decision points are marked **ASK**.

## 0. What moves where — one sentence

Today a boundary `M ⟪ boundary Rs χ , c ⟫` carries its own bind block
`Rs`, pushed as `bindR` entries onto the representation context ON THE
WAY INTO THAT BOUNDARY (`extendReps`), so a representation variable is
an index relative to the boundaries that enclose it and every rule that
moves a subterm across a boundary re-indexes it (`renᴹ²`, `renᴹᴿ`,
`underRepBinds`, `SameConv`, `SameTyExt`).  The experiment pushes the
bind onto the AMBIENT representation context instead, at index 0, when
`TyBeta` mints it: the whole program then lives under one more binder,
so the redex's SIBLINGS are shifted by one (`renᴹᴿ suc`, one lemma,
`⊢renᴿ`, which already exists), and nothing is ever shifted again —
crossing a boundary no longer changes the representation context at
all.

The NAME MAP `names Δ : List RVar` (ordinary `X` ↦ its representation
variable) and the `lock`/`unlock` changes on it are UNCHANGED.  This is
the answer to the 2026-09-05 objection recorded at `DesignSpace.md` D33 →
D34 ("a global Σ-store, NOT taken — lexical scope is needed for lock
blocking"): that proposal stored the whole context; this one stores
only what `bindR` held.  `reps Δ` says WHAT a representation is;
`names Δ` says WHETHER this position may name it.  Lock blocking is
still lexical.

**Why experiment 1 had to come first.**  With `ξ-Λ`, a `TyBeta` under a
`Λ` would push a cell whose payload mentions the `Λ`'s own abstract
variable onto a context the `Λ`'s siblings do not share; the value
restriction makes every redex's context the AMBIENT one, so "push at 0
and shift everyone else" is meaningful.

**Why fresh = 0 rather than append at the end.**  Under `Λ N` the body
is typed with the binder at index 0.  If the cell `TyBeta` mints is
ALSO index 0, the body's indices already line up with the new context:
`N` moves into the contractum VERBATIM, and its retyping is today's
`⊢refine (rr-represent …)` — `abstR` refined to `bindR R` in place.
Appending at the end would instead need a pointer substitution
`N [ ℓ ]ᴿ` in the body and a left-referring store spelled at the front
(second revision of this note, retired).  Fresh = 0 keeps the standard
right-referring telescope, so `_∋ʳ_:=_`, `WfRepCtx`, `RepWk`,
`_⊢ᴿ[_]_` and the 56 uses of the lazy shift in `proof/Ctx.agda` are
untouched.  The price is that a step GROWS THE CONTEXT and the
congruences shift siblings — §3, where a step returns the growth `δ`
and the new context is `apply δ Δ`.

## 1. Definitions

### 1.1 Contexts: unchanged; allocation is `bindR R ∷_`

`RVar = ℕ`, `Rep = Ty`, `RepCtx = List RepBinding`, `Ctxᵗ = Ξ ∣ Δ`,
`underΛ`, `_∋ʳ_:=_` (lazy shift), `_⊢ᴿ[_]_`, `WfRepCtx`, `WfCtx`,
`RepWk` — ALL AS TODAY.  The store is `reps Δ` itself, now containing
every bind the run has minted, interleaved with the ambient `abstR`s in
allocation order (newest at 0):

```agda
allocate : Ty → Ctxᵗ → Ctxᵗ
allocate R (Ξ ∣ Δ) = (bindR R ∷ Ξ) ∣ shiftNames Δ
-- fresh address 0; every existing representation variable, and every
-- entry of the name map, moves up by one.  wf: WfCtx Δ → Ξ ⊢ᴿ R →
-- WfCtx (allocate R Δ)   (today's `represented-wf`, at the ambient)

↑ᴿ : Term → Term          -- the sibling shift
↑ᴿ = renᴹᴿ suc            -- representation universe only; ordinary
                          -- types and term variables untouched
```

`pushRepBinds`, `extendReps`, `shiftRVars`, `_⊢ᴮ_` are gone (their only
callers were the two boundary readings).  `RepRefines`/`⊢refine` stay,
used by `TyBeta` exactly as today.

### 1.2 Boundaries: changes only

```agda
data Change : Set where
  lock   : ℕ → RVar → Change
  unlock : ℕ → RVar → Change

Boundary : Set
Boundary = List Change

dualBoundary Θ = map dualChange (reverse Θ)             -- as today
rewind Θ       = dualBoundary Θ ++ Θ                     -- as today
Θ₁ ⋉ Θ₂        = Θ₁ ++ Θ₂           -- no underRepBinds: nothing shifts
addLock0 Θ     = Θ ++ (lock 0 0 ∷ [])          -- was lock 0 (numBinds Θ)
instantiate Θ  = map shiftX Θ ++ (unlock 0 0 ∷ [])
                 -- shiftX bumps the ORDINARY index only; the new name 0
                 -- names cell 0, which allocate has just pushed
renᴮᴿ ρ Θ      = map (renᶠᴿ ρ) Θ                         -- no extN offset
```

`numBinds`, `renᴮ²` are gone.  The two readings lose their `extendReps`
prefix and become plain name-map transformers:

```agda
Δ ⊢ⁱ Θ ⇒ Δᵢ     -- every change applied     (interior)
Δ ⊢ᶜ Θ ⇒ Δᶜ     -- locks skipped            (conversion context)
-- reps Δᵢ ≡ reps Δ ≡ reps Δᶜ : a boundary changes NAMES only
```

Consequently

```agda
Δ ⊢ A ≈ B ⊣ Δ′  =  ∃[ R ] (Δ ⊢ᶜ A ~ R × Δ′ ⊢ᶜ B ~ R)
```

is the ONLY cross-context type comparison: `SameTyExt (numBinds Θ) …`
collapses into it, because there is no bind prefix to cross.
`interior-ren`/`conversion-ren` (Boundary.agda §3d) survive as the
readings' half of the sibling-shift lemma.

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
map, and all of that respelling machinery is deleted; the sibling shift
`renᶜ suc` is exact, not a respelling.  This is GTSF's
`Conversion.agda` shape (`unseal α A` with `(α , A) ∈ Σ`), as
`RedesignAdvice.md` Q3 already noted.  `mkId : Ty → Conv` is UNCHANGED
as a function; the rules hand it the representation `R` instead of the
ordinary `A`.

The fallback R2-b keeps ordinary names and `SameConv`; the store still
removes every cross-boundary shift, but not the respelling.

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
the name map; the store only stores.  (Today's `Δ ∋ X := A` bundles
the same three facts keyed by `X`.)

`reveal 0 B` / `instReveal 0 s` are built as today; under R2 the `0`
they write into `seal`/`unseal` is CELL 0 (= the binder's slot), under
R2-b it is ordinary slot 0.  Same number either way, which is the
fresh-at-0 coincidence again.

## 2. Typing

`Δ ∣ Γ ⊢ M ⦂ A` keeps its shape and all of its rules except `env`:

```agda
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

THE ONE LEMMA.  It is today's `proof/RepWeaken.agda`, at `ρ = suc`:

```agda
repwk-alloc : Ξ ⊢ᴿ R → RepWk suc Ξ (bindR R ∷ Ξ)     -- repwk-wkN at [R]

⊢renᴿ : RepWk ρ Ξ Ξ′ → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A
      → (Ξ′ ∣ map ρ η) ∣ Γ ⊢ renᴹᴿ ρ M ⦂ A            -- exists today

⊢↑ᴿ : Ξ ⊢ᴿ R → Δ ∣ Γ ⊢ M ⦂ A → allocate R Δ ∣ Γ ⊢ ↑ᴿ M ⦂ A
⊢↑ᴿ wR = ⊢renᴿ (repwk-alloc wR)
```

and its companions `interior-ren`/`conversion-ren` (readings),
`conv-ren` (conversions), `value-renᴹᴿ` (values, added in experiment
1), `wf-ren-rep` (types).  All exist.  What is NEW is only where they
are applied: in every congruence, to the redex's siblings.

## 3. Reduction — a step returns the CHANGE to the store

```agda
data Alloc : Set where        -- what a step did to the store: nothing,
  none : Alloc                -- or exactly one cell (Jeremy: a step
  new  : Ty → Alloc           -- allocates 0 or 1 addresses, never more)

apply : Alloc → Ctxᵗ → Ctxᵗ
apply none    Δ = Δ
apply (new R) Δ = allocate R Δ

↑[_] : Alloc → Term → Term    -- the sibling shift
↑[ none  ] = id
↑[ new R ] = renᴹᴿ suc        -- likewise renᴮᴿ suc / renᶜ suc on Θ and c

_⊢_-→_∣_ : Ctxᵗ → Term → Term → Alloc → Set
-- Δ ⊢ M -→ M′ ∣ δ : the contractum M′ lives at apply δ Δ
```

No context is ever subtracted from another, and no counting: every
lemma is stated once at `none` (identity) and once at `new R` (`suc`).

```agda
TyBeta : Value N → Δ ⊢ᶜ A ~ R
  → Δ ⊢ (Λ N) ·[ B , A ]
      -→ N ⟪ unlock 0 0 ∷ [] , reveal 0 B ⟫ ∣ new R
```

(today: `N ⟪ instantiate R (boundary [] []) , reveal 0 B ⟫` — the
SAME contractum with the bind moved from the boundary to the context.
`N` is verbatim: it was typed at `underΛ Δ = abstR ∷ Ξ ∣ 0 ∷ shiftNames
Δ`, and the interior of the contractum reads `unlock 0 0` at
`allocate R Δ` as `bindR R ∷ Ξ ∣ 0 ∷ shiftNames Δ` — `⊢refine
(rr-represent rr-refl)`, today's proof.)

```agda
Beta : Value W → Δ ⊢ᶜ A ~ R
  → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ R ]ᵐ ∣ none
-- crossΛᴹ unchanged in shape: renᴹ² (ren² idᵗ suc) W ⟪ lock 0 0 ∷ [] , mkId (⇑ᵗ R) ⟫
```

(`Beta` gains the reading premise only under R2, because `mkId` needs
the argument type as a representation; under R2-b it is today's rule.)

```agda
Peel : Value V → Value W
  → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
      -→ (V · (W ⟪ dualBoundary Θ , s ⟫)) ⟪ Θ , t ⟫ ∣ none
```

(today: `renᴹ² (ren² idᵗ (wkN (numBinds Θ))) W`, `s′` with
`SameConv Δᵈ s′ Δᶜ s`, and three context-reading premises.  All gone:
`W` moves verbatim — the boundary has no binds to move it past — and
under R2 `s` means the same thing in `Δᵈ`.)

```agda
TyPeelR-Λ : Value N → Δ ⊢ᶜ A ~ R
  → Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
      -→ N ⟪ instantiate Θ , instReveal 0 s ⟫ ∣ new R

TyPeelR-⟪⟫ : Value W → Δ ⊢ᶜ A ~ R → (the Bᵢ′ reading, as today)
  → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
      -→ ((↑ᴿ W ⟪ addLock0 (renᴮᴿ suc (map shiftX Θ′)) , `∀ (renᶜ suc s′) ⟫)
            ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
           ⟪ instantiate Θ , instReveal 0 s ⟫
      ∣ new R
```

In `TyPeelR-⟪⟫` the inner boundary is a SIBLING of the redex's `Λ`
binder, so it gets exactly the sibling shift and nothing else: today's
`renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc)) W` becomes `↑ᴿ W`, `renᴮ²
(ren² idᵗ suc) Θ′` becomes `renᴮᴿ suc`, and `s″` with its `SameConv`/
`renNameCtx` premise — where the 2026-09-20 wall lived — becomes the
exact `renᶜ suc s′`.

```agda
CancelR : Value V → Δ ∋rep α := R
  → Δ ⊢ (V ⟪ Θ₁ , seal α ⟫) ⟪ Θ₂ , unseal α ⟫
      -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId R ⟫) ⟪ rewind Θ₂ , mkId R ⟫ ∣ none

IdPush : Value V → Δ ∋rep β := R
  → Δ ⊢ (V ⟪ Θ₁ , id (` α) ⟫) ⟪ Θ₂ , unseal β ⟫
      -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal β ⟫) ⟪ rewind Θ₂ , mkId R ⟫ ∣ none
```

Today `CancelR` has eight premises (`seal X` at `Δ₁ᶜ`, `unseal Y` at
`Δᶜ`, two lookups, the `⋉`-reading, `Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ`) because the
two conversions spell one fact in two name maps.  Under R2 typing forces
the SAME `α` on both sides (`Δᵢ ⊢ ` X ≈ ` Y ⊣ Δᶜ` is `α ≡ β`) and the
minted identities are read off the context.  `IdPush` loses its
`` Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ `` re-spelling for the same reason.  `Drop$`,
`Drop-true`, `Drop-false` return `none`.

THE CONGRUENCES pass the change up and shift the siblings by it:

```agda
ξ-·-l  : Δ ⊢ L -→ L′ ∣ δ → Δ ⊢ L · M -→ L′ · ↑[ δ ] M ∣ δ
ξ-·-r  : Value V → Δ ⊢ M -→ M′ ∣ δ → Δ ⊢ V · M -→ ↑[ δ ] V · M′ ∣ δ
ξ-·[]  : Δ ⊢ L -→ L′ ∣ δ → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ] ∣ δ
ξ-⟪⟫   : Δ ⊢ⁱ Θ ⇒ Δᵢ → Δᵢ ⊢ M -→ M′ ∣ δ
       → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ ↑[ δ ] Θ , ↑[ δ ] c ⟫ ∣ δ
```

`ξ-·[]`'s type annotations are ordinary and do not shift.  In `ξ-⟪⟫`
the interior's contractum lives at `apply δ Δᵢ`, and `interior-ren` at
`suc` says that is exactly what `apply (new R) Δ ⊢ⁱ ↑[ new R ] Θ ⇒ _`
reads — the fact `preserve`'s `ξ-⟪⟫` case needs.  The rules never
mention `apply`; only the theorems do.

The multi-step relation needs no store index: each step's change is
applied to the context the tail runs at, and the endpoint's context is
whatever the last step left.

```agda
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : Δ ⊢ M -→* M
  _then_ : Δ ⊢ L -→ M ∣ δ → apply δ Δ ⊢ M -→* N → Δ ⊢ L -→* N
-- the run's final context is read off the derivation (`runCtx`);
-- `Reaches` states it alongside the endpoint
```

`value-¬step` is unchanged.  `det` concludes `M′ ≡ M″ × δ′ ≡ δ″`.

## 4. The same programs, on the store

`P₀ = (ΛX. λx:X. x) [ℕ] · 7` — today (`Examples` §1a; frames render
binds as `↑α:=ℕ`):

```
((ΛX. λx:X. x) [ℕ] · 7)
 --TyBeta-->  ((λx:X. x) ⟪ ↑α:=ℕ , ↥X , seal X ↦ unseal X ⟫) · 7
 --Peel---->  ((λx:X. x) · (7 ⟪ ↓X , seal X ⟫)) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫
 --Beta---->  (7 ⟪ ↓X , seal X ⟫) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫
 --CancelR->  (7 ⟪ ↥X , ↓X , id ℕ ⟫) ⟪ ↑α:=ℕ , ↥X , ↓X , id ℕ ⟫
 --Drop$-->   7 ⟪ ↑α:=ℕ , ↥X , ↓X , id ℕ ⟫
 --Drop$-->   7
```

With the store (`Ξ` on the left; `↥X:=α` is `unlock 0 α`; the sibling
`7` of the first step has no representation variables, so `↑ᴿ 7 = 7`):

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

Same six rules, same shape; `Peel` moved `7` without `renᴹ²` and reused
`seal α` without `SameConv`; `CancelR` fired on `Ξ ∋ α := ℕ` alone.

`Q₀` (`Examples` §2) is where the sibling shift shows.  Today's fourth
step is the inner `TyBeta`, INSIDE the outer boundary:

```
(((ΛY. λx:ℕ. (7 ⟪ ↓X , seal X ⟫) ⟪ ↓Y , id X ⟫) [ℕ] · 0) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫
 --ξ-⟪⟫ ⨟ ξ-·-l ⨟ TyBeta-->
((((λx:ℕ. …) ⟪ ↑β:=ℕ , ↥Y , id ℕ ↦ id X ⟫) · 0) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫
```

With the store, in INDICES so the shift is visible (`α` was cell 0
before the step and is cell 1 after it):

```
Ξ = [ℕ]         (((ΛY. λx:ℕ. (7 ⟪ ↓X , seal 0 ⟫) ⟪ ↓Y , id 0 ⟫) [ℕ] · 0) ⟪ ↥X:=0 , unseal 0 ⟫
 --ξ-⟪⟫ ⨟ ξ-·-l ⨟ TyBeta-->
Ξ = [ℕ , ℕ]     ((((λx:ℕ. (7 ⟪ ↓X , seal 1 ⟫) ⟪ ↓Y , id 1 ⟫) ⟪ ↥Y:=0 , id ℕ ↦ id 1 ⟫) · 0) ⟪ ↥X:=1 , unseal 1 ⟫
```

Three things moved by one: the body `N` did NOT (it was under the `ΛY`,
its `seal 0`/`id 0` for `X` were already `1` there — hence `seal 1`,
`id 1` verbatim in the contractum); the sibling argument `0` has no
representation variables; the enclosing boundary's `↥X:=0 , unseal 0`
became `↥X:=1 , unseal 1` through `ξ-⟪⟫`'s `renᴮᴿ`/`renᶜ`; and the
ambient name map went from `[0]` to `[1]`.  The renderer (`Show.agda`)
names cells by identity, so with names the trace reads exactly like
today's minus the `↑β:=ℕ` on the frame.

## 5. What the metatheory loses and gains

Retired: `binds`/`numBinds`/`extendReps`/`pushRepBinds`/`_⊢ᴮ_`,
`underRepBinds`, `renᴮ²` and the represent-half of `ren²` on boundaries,
`SameTyExt`, and under R2 `SameConv`/`respell` and the re-spelling
premises of `Peel`/`TyPeelR-⟪⟫`/`CancelR`/`IdPush`; the `ShiftAudit`
frame-exactness obligations for moves across binds (there are no binds
to move across).  `MoveScope.agda`'s `preserve-CancelR`/`preserve-IdPush`
reduce to the store lookup.

Kept and PROMOTED: `proof/RepWeaken.agda` (`RepWk`, `⊢renᴿ`,
`repwk-wkN`, `interior-ren`, `conversion-ren`, `conv-ren`,
`value-renᴹᴿ`) is the sibling-shift lemma, applied in the four
congruences and in `TyPeelR-⟪⟫`; `RepRefines`/`⊢refine` is `TyBeta`'s
retyping, as today.  `Ctx.agda` and `proof/Ctx.agda` are untouched.

New: `allocate` and its `WfCtx` lemma (today's `represented-wf` at the
ambient), `↑ᴿ`/`↑[_,_]`, the context-returning step relation, and the
`ξ-⟪⟫` bookkeeping (`interior-ren` at `ρ = suc`).

The theorem statements:

```agda
Preservation = ∀ {Δ δ M M′ A} → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ ∣ δ
  → WfCtx (apply δ Δ) × (apply δ Δ ∣ [] ⊢ M′ ⦂ A)

Preservation* : … → Δ ⊢ M -→* M′ → WfCtx (runCtx r) × (runCtx r ∣ [] ⊢ M′ ⦂ A)

Progress      = ∀ {Δ M A} → Δ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ ∃[ M′ ] ∃[ δ ] (Δ ⊢ M -→ M′ ∣ δ)

det : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ ∣ δ′ → Δ ⊢ M -→ M″ ∣ δ″
  → M′ ≡ M″ × δ′ ≡ δ″
```

`Preservation` needs no `⊑` and no subtraction: the new context is
`apply δ Δ`, and `⊢↑ᴿ` is stated at `none` (nothing to do) and at
`new R` (`⊢renᴿ (repwk-alloc wR)`).  Its congruence cases are `⊢↑ᴿ` on
the sibling plus the IH.

Color/scope-map preservation: the residual renaming `ρ` a step delivers
is now `id` or `suc` by `δ`, uniformly for every position — the
theorem's shape (`names Δ₂ ≡ map ρ (names Δ₁)`) is unchanged and `ρ`
is read off `δ`.

## 6. Decision points, collected

- ~~R1~~ dissolved (2026-09-22): `RVar = ℕ`, `Rep = Ty`, contexts as
  today.
- **R2** conversions cite `RVar` (recommended; deletes all respelling,
  and makes the sibling shift on conversions exact) vs keep ordinary
  names and `SameConv` (R2-b).
- ~~R3~~ dissolved by fresh = 0: `TyBeta`'s body is verbatim and its
  retyping is today's `⊢refine`.
- **R4** RULED (Jeremy): fresh address 0, siblings shift by one, one
  lemma (`⊢renᴿ`) in many places.  Append-at-end retired.
- **R5** the ambient abstract entries stay in `Ξ` (needed to type `Λ`
  bodies and to state reduction at the probes' `underΛ empty`).
- ~~R6~~ RULED (Jeremy): a step returns the CHANGE `δ : Alloc`, not the
  new context, and `Alloc` is `none | new R` — a step allocates 0 or 1
  addresses, never more.  The shift is `id`/`suc`, the new context is
  `apply δ Δ`.  No subtraction, no counting.

## 7. Suggested order of work

1. `Boundary.agda`: `Boundary = List Change`, the two readings without
   `extendReps`, `instantiate`/`addLock0`/`_⋉_`/`renᴮᴿ` as in §1.2;
   `Conversion.agda` on `RVar` (R2).  Statements only, then `Terms.agda`'s
   `env` and `allocate` in `Ctx.agda`.
2. `Reduction.agda` with the `∣ δ` index and `↑[ δ ]` in the
   congruences; `_-→*_` applying each step's `δ` to the tail's context;
   `det` and `value-¬step`.
3. `TypeCheck.agda`/`Eval.agda`: `step` returns `δ` and applies the
   sibling shift; `eval` threads `apply δ`; `Reaches` records the
   final context.  Rerun the 23 runs — their step counts should be
   UNCHANGED (no rule was added or split).
4. `proof/Preserve.agda`: congruences by `⊢↑ᴿ`, `TyBeta` by today's
   `⊢refine`, then rule by rule; `TyPeelR-⟪⟫` should be the big win.
5. Progress, type safety, then the color theorem's restatement.
