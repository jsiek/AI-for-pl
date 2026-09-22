# Experiment 2 — a GLOBAL REPRESENTATION STORE instead of `binds`

Sketch, 2026-09-22.  Jeremy: "removing the binds field from Boundary and
instead make that a global representation type store.  For example,
TyBeta would add the representation R to the type store."

Nothing here is implemented.  Every `Agda` block is the intended
statement, written against the current strong-rep-store names so that
the diff is readable rule by rule.  Decision points are marked **ASK**.

## 0. What moves where — one sentence

Today a boundary `M ⟪ boundary Rs χ , c ⟫` carries its own bind block
`Rs`, pushed as `bindR` entries onto the representation context on the
way in (`extendReps`), so every representation variable is a de Bruijn
index RELATIVE to the boundaries and `Λ`s that enclose it, and every
rule that moves a subterm across a boundary re-indexes it (`renᴹ²`,
`renᴹᴿ`, `underRepBinds`, `SameConv`, `SameTyExt`).  The experiment
puts the bound representations in ONE append-only store `Σ`, addressed
globally, so that a moved subterm is moved VERBATIM and a representation
is written exactly once, by the `TyBeta` that mints it.

The NAME MAP `names Δ : List RVar` (ordinary `X` ↦ its representation
variable) and the `lock`/`unlock` changes on it are UNCHANGED.  This is
the answer to the 2026-09-05 objection recorded at `DesignSpace.md` D33 →
D34 ("a global Σ-store, NOT taken — lexical scope is needed for lock
blocking"): that proposal stored the whole context; this one stores
only what `bindR` held.  `Σ` says WHAT a representation is; `Δ` says
WHETHER this position may name it.  Lock blocking is still lexical.

**Why experiment 1 had to come first.**  With `ξ-Λ`, a `TyBeta` under a
`Λ` would append to `Σ` a payload mentioning the `Λ`'s own abstract
variable, and a later instantiation of that `Λ` would leave the store
entry pointing at a binder that no longer exists.  With the value
restriction nothing reduces under `Λ`, so at every redex the abstract
variables in scope are exactly the AMBIENT ones, fixed for the run.

## 1. Definitions

### 1.1 Representation variables are two-sorted

```agda
data RVar : Set where
  var : ℕ → RVar   -- de Bruijn: a payload's own ∀ binders, then the
                   --   ambient Λ binders (today's abstR entries)
  loc : ℕ → RVar   -- an ADDRESS in the global store Σ (today's bindR)

Rep : Set          -- representation payloads: types over RVar
Rep = Ty RVar      -- Types.agda parameterised by the variable sort;
                   -- the ordinary Ty is Ty ℕ

Store : Set
Store = List Rep   -- Σ.  Address ℓ = position ℓ.  Only ever EXTENDED
                   -- at the end (Σ ∷ʳ R), so addresses never move.

Σ ∋ loc ℓ := R  iff  Σ ∋ˡ ℓ := R     -- var i has NO representation
                                       -- (abstract), exactly as abstR
```

`shiftVar (var i) = var (suc i)`, `shiftVar (loc ℓ) = loc ℓ`: crossing a
`Λ` moves abstract indices and leaves addresses alone.  **ASK (R1):**
`Rep = Ty RVar` by parameterising `Types.agda`, or a separate `Rep`
datatype mirroring `Ty`?  Parameterising is one mechanical refactor and
keeps `renameᵗ`/`_[_]ᵗ` shared; a separate type keeps `Ty` untouched.

### 1.2 Type contexts

```agda
record Ctxᵗ : Set where
  constructor _∣_
  field
    abst  : ℕ           -- the number of enclosing Λ binders
    names : List RVar   -- the name map, unchanged in role

underΛ (n ∣ Δ) = suc n ∣ (var 0 ∷ map shiftVar Δ)
empty          = 0 ∣ []
```

`RepCtx`, `RepBinding`, `pushRepBinds`, `extendReps`, `shiftRVars`,
`_⊢ᴮ_` are gone.  `WfCtx` becomes store-relative:

```agda
record WfCtx (Σ : Store) (Γ : Ctxᵗ) : Set where
  field
    wf-names : ∀ {X α} → names Γ ∋ˡ X := α → Σ ∣ abst Γ ⊢ʳ α
               -- var i : i < abst Γ ;  loc ℓ : ℓ < length Σ
    name-fn  : Unique (names Γ)

data _⊢Σ_ : ℕ → Store → Set where          -- the store is a TELESCOPE
  wfΣ[]  : n ⊢Σ []
  wfΣ∷ʳ  : n ⊢Σ Σ → (Σ ∣ n) ⊢ᴿ R → n ⊢Σ Σ ∷ʳ R
             -- R's loc's are EARLIER addresses, its var's are ambient
```

### 1.3 Boundaries: changes only

```agda
data Change : Set where
  lock   : ℕ → RVar → Change
  unlock : ℕ → RVar → Change

Boundary : Set
Boundary = List Change

dualBoundary Θ  = map dualChange (reverse Θ)             -- as today
rewind Θ        = dualBoundary Θ ++ Θ                     -- as today
Θ₁ ⋉ Θ₂         = Θ₁ ++ Θ₂           -- no underRepBinds: nothing shifts
addLock0 ℓ Θ    = Θ ++ (lock 0 (loc ℓ) ∷ [])   -- was lock 0 (numBinds Θ)
instantiate ℓ Θ = map shiftX Θ ++ (unlock 0 (loc ℓ) ∷ [])
                  -- shiftX bumps the ORDINARY index only; the new name 0
                  -- names the store cell, not a bind slot
```

`numBinds` is gone.  The two readings lose their `extendReps` prefix and
become plain name-map transformers:

```agda
Σ ∣ Δ ⊢ⁱ Θ ⇒ Δᵢ     -- every change applied     (interior)
Σ ∣ Δ ⊢ᶜ Θ ⇒ Δᶜ     -- locks skipped            (conversion context)
-- step-unlock : Σ ∣ n ⊢ʳ α → Δ ∌ʳ α → α ⊢+ Δ at X ⇒ Δ′ → …
```

The interior and the exterior now share the same `abst`; the only
thing a boundary changes is `names`.  Consequently

```agda
Δ ⊢ A ≈ B ⊣ Δ′  =  ∃[ R ] (Δ ⊢ A ~ R × Δ′ ⊢ B ~ R)
```

is the ONLY cross-context type comparison: `SameTyExt (numBinds Θ) …`
collapses into it, because there is no bind prefix to cross.

### 1.4 Conversions cite representation variables  — **ASK (R2)**

```agda
data Conv : Set where
  id     : Rep → Conv          -- ACTIVE at a base, INERT at ` α
  seal   : RVar → Conv         -- INERT
  unseal : RVar → Conv         -- ACTIVE
  _↦_    : Conv → Conv → Conv
  `∀     : Conv → Conv
```

Today `seal X`, `unseal X`, `id (` X)` cite ORDINARY names, which is why
a conversion read in another name map must be RE-SPELLED (`SameConv`,
`respell`, the `s′`/`s″` premises of `Peel` and `TyPeelR-⟪⟫`, the
`≈`-premises of `CancelR`/`IdPush`).  With the payload in the
representation universe, a conversion means the same thing in every
name map, and all of that respelling machinery is deleted.  This is
GTSF's `Conversion.agda` shape (`unseal α A` with `(α , A) ∈ Σ`), as
`RedesignAdvice.md` Q3 already noted.

The fallback R2-b keeps `seal X`/`unseal X` and keeps `SameConv`; the
store still removes every SHIFT, but not the respelling.

```agda
Σ ; Δ ⊢ c ∶ A ⇝ B

conv-id     : Base R                → Σ ; Δ ⊢ id R ∶ ⌜R⌝ ⇝ ⌜R⌝
conv-idv    : Δ ∋ᵗ X := α           → Σ ; Δ ⊢ id (` α) ∶ ` X ⇝ ` X
conv-seal   : Δ ∋ᵗ X := α → Σ ∋ α := R → Δ ⊢ A ~ R
                                    → Σ ; Δ ⊢ seal α ∶ A ⇝ ` X
conv-unseal : Δ ∋ᵗ X := α → Σ ∋ α := R → Δ ⊢ A ~ R
                                    → Σ ; Δ ⊢ unseal α ∶ ` X ⇝ A
conv-fun, conv-all : as today
```

`conv-seal`/`conv-unseal` still demand `Δ ∋ᵗ X := α`: the address must
be NAMED in the conversion context.  A boundary whose changes lock `X`
cannot unseal `α` however many store cells exist — abstraction is
enforced by the name map, the store only stores.

Helpers: `mkIdᴿ : Rep → Conv` (structural, `mkIdᴿ (` α) = id (` α)`),
`reveal ℓ : Rep → Conv` (the body type read as a `Rep` with `loc ℓ` at
the instantiated leaves; `unseal (loc ℓ)`/`seal (loc ℓ)` by polarity,
`id` elsewhere), `instReveal ℓ` likewise composed with `s`.

## 2. Typing

```agda
Σ ; Δ ∣ Γ ⊢ M ⦂ A

⊢Λ   : Value N → Σ ; underΛ Δ ∣ ⤊ Γ ⊢ N ⦂ C → Σ ; Δ ∣ Γ ⊢ Λ N ⦂ `∀ C
⊢·[] : Σ ; Δ ∣ Γ ⊢ L ⦂ `∀ B → Δ ⊢ᵗ A → Σ ; Δ ∣ Γ ⊢ L ·[ B , A ] ⦂ B [ A ]ᵗ

env : Σ ∣ Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Σ ∣ Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Σ ; Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
    → Σ ; Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
    → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
    → Δ  ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ          -- was SameTyExt (numBinds Θ) Δ Bₑ Δᶜ Cₑ
    → Δ ⊢ᵗ Bₑ
    → Σ ; Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ
```

`BoundaryWf Δ Θ Δᵢ Δᶜ` shrinks to the two readings (its `bw-binds` field
has nothing to say).  Ordinary type formation `Δ ⊢ᵗ A` is unchanged.

Two lemma families replace `RepWeaken`/`RepRefines`:

```agda
_⊑_ : Store → Store → Set          -- prefix: Σ ⊑ Σ ∷ʳ R

⊢-⊑  : Σ ⊑ Σ′ → Σ ; Δ ∣ Γ ⊢ M ⦂ A → Σ′ ; Δ ∣ Γ ⊢ M ⦂ A   -- and for
      -- ∶⇝, ⊢ⁱ/⊢ᶜ, WfCtx: every judgement is monotone in Σ, because
      -- nothing is ever read by "the last address"

_[_]ᴿ : Term → ℕ → Term
-- N [ ℓ ]ᴿ : var 0 ↦ loc ℓ, var (suc i) ↦ var i, in every lock/unlock
-- and every id/seal/unseal inside N.  Ordinary types in N are untouched.
⊢[]ᴿ : Σ ∋ loc ℓ := R
     → Σ ; (suc n ∣ var 0 ∷ map shiftVar Δ) ∣ ⤊ Γ ⊢ N ⦂ C
     → Σ ; (n ∣ loc ℓ ∷ Δ) ∣ ⤊ Γ ⊢ N [ ℓ ]ᴿ ⦂ C
```

`⊢[]ᴿ` is today's `⊢refine (rr-represent …)`: the abstract binder is
REPLACED by the cell instead of being re-tagged in place.  **ASK (R3):**
this makes `TyBeta` substitute — in the REPRESENTATION universe only.
The design law "TyBeta does not substitute" (Design.md §6.1) survives as
"does not substitute TYPES": `N` keeps running at the ordinary `X`;
only its pointers learn `ℓ`.  Since `N` is a value (experiment 1), the
substitution never walks a redex.

## 3. Reduction — store-passing

```agda
Σ ∣ Δ ⊢ M -→ M′ ∣ Σ′        -- Σ′ = Σ except in the three ∀-eliminations
```

Below, `ℓ = length Σ` is the fresh address.

```agda
TyBeta : Value N → Δ ⊢ᶜ A ~ R → underΛ Δ ⊢ᶜ B ~ Rᴮ
  → Σ ∣ Δ ⊢ (Λ N) ·[ B , A ]
      -→ N [ ℓ ]ᴿ ⟪ unlock 0 (loc ℓ) ∷ [] , reveal ℓ (Rᴮ [ ℓ ]ᴿ) ⟫
      ∣ Σ ∷ʳ R
```

(today: `N ⟪ instantiate R (boundary [] []) , reveal 0 B ⟫`, the bind
`R` living in the boundary.)

```agda
Beta : Value W → Δ ⊢ᶜ A ~ R
  → Σ ∣ Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ R ]ᵐ ∣ Σ
-- crossΛᴹ W R = shiftVarᴹ W ⟪ lock 0 (var 0) ∷ [] , mkIdᴿ (shiftVar R) ⟫
-- the only surviving representation renaming: abstract indices move
-- past the new Λ; addresses do not
```

`Beta` gains the reading premise because `mkIdᴿ` needs the argument
type as a `Rep` (under R2).  Under R2-b it stays exactly as today.

```agda
Peel : Value V → Value W
  → Σ ∣ Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
      -→ (V · (W ⟪ dualBoundary Θ , s ⟫)) ⟪ Θ , t ⟫ ∣ Σ
```

(today: `renᴹ² (ren² idᵗ (wkN (numBinds Θ))) W`, `s′` with
`SameConv Δᵈ s′ Δᶜ s`, and the three context-reading premises.  All
gone: `W` moves verbatim and `s` means the same thing in `Δᵈ`.)

```agda
TyPeelR-Λ : Value N → Δ ⊢ᶜ A ~ R
  → Σ ∣ Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
      -→ N [ ℓ ]ᴿ ⟪ instantiate ℓ Θ , instReveal ℓ (s [ ℓ ]ᶜ) ⟫
      ∣ Σ ∷ʳ R

TyPeelR-⟪⟫ : Value W → Δ ⊢ᶜ A ~ R → Δᶜ-reading of Bᵢ′ as today
  → Σ ∣ Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
      -→ ((W ⟪ addLock0 ℓ (map shiftX Θ′) , `∀ s′ ⟫)
            ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
           ⟪ instantiate ℓ Θ , instReveal ℓ (s [ ℓ ]ᶜ) ⟫
      ∣ Σ ∷ʳ R
```

`s [ ℓ ]ᶜ` is `_[_]ᴿ` on a conversion.  In `TyPeelR-⟪⟫` the inner
boundary is moved WITHOUT `renᴹ²`, without `renᴮ² (ren² idᵗ suc)`, and
with `s′` unchanged — the `s″`/`SameConv`/`renNameCtx` premise cluster,
which is where the 2026-09-20 wall (`notes/AddLock0Wall.agda`) lived,
has nothing left to misspell.  `addLock0 ℓ` locks the NEW name `0`
(which names the cell `ℓ`) out of the moved interior, as today.

```agda
CancelR : Value V → Σ ∋ α := R
  → Σ ∣ Δ ⊢ (V ⟪ Θ₁ , seal α ⟫) ⟪ Θ₂ , unseal α ⟫
      -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkIdᴿ R ⟫) ⟪ rewind Θ₂ , mkIdᴿ R ⟫ ∣ Σ

IdPush : Value V → Σ ∋ β := R
  → Σ ∣ Δ ⊢ (V ⟪ Θ₁ , id (` α) ⟫) ⟪ Θ₂ , unseal β ⟫
      -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal β ⟫) ⟪ rewind Θ₂ , mkIdᴿ R ⟫ ∣ Σ
```

Today `CancelR` has eight premises (`seal X` at `Δ₁ᶜ`, `unseal Y` at
`Δᶜ`, two lookups, the `⋉`-reading, `Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ`) because the
two conversions spell one fact in two name maps.  Under R2 typing forces
the SAME `α` on both sides (`Δᵢ ⊢ ` X ≈ ` Y ⊣ Δᶜ` is `α ≡ β`), and the
minted identities are read off the store.  `IdPush` loses its
`` Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ `` re-spelling for the same reason.

`Drop$`/`Drop-true`/`Drop-false` and the four congruences are unchanged
(they pass `Σ` through).  `value-¬step` is unchanged.  `det` gains the
conclusion `Σ′ ≡ Σ″`; it holds because the only allocation is at
`length Σ` and `_~_` readings are functional.

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

With the store (`Σ` on the left; `↥X:=ℓ₀` is `unlock 0 (loc ℓ₀)`):

```
Σ = []          ((ΛX. λx:X. x) [ℕ] · 7)
 --TyBeta-->
Σ = [ℓ₀ ↦ ℕ]    ((λx:X. x) ⟪ ↥X:=ℓ₀ , seal ℓ₀ ↦ unseal ℓ₀ ⟫) · 7
 --Peel---->    ((λx:X. x) · (7 ⟪ ↓X , seal ℓ₀ ⟫)) ⟪ ↥X:=ℓ₀ , unseal ℓ₀ ⟫
 --Beta---->    (7 ⟪ ↓X , seal ℓ₀ ⟫) ⟪ ↥X:=ℓ₀ , unseal ℓ₀ ⟫
 --CancelR->    (7 ⟪ ↓X , ↥X:=ℓ₀ , id ℕ ⟫) ⟪ ↥X:=ℓ₀ , ↓X , id ℕ ⟫
 --Drop$-->     7 ⟪ ↥X:=ℓ₀ , ↓X , id ℕ ⟫
 --Drop$-->     7
```

Same six rules, same shape.  What changed is invisible in the trace and
visible in the rule: `Peel` moved `7` without `renᴹ²` and reused `seal ℓ₀`
without `SameConv`; `CancelR` fired on `Σ ∋ ℓ₀ := ℕ` alone; the bind
`ℕ` was written once, in `Σ`, instead of being carried by every frame
the value later passes through.

`Q₀` (`Examples` §2, the id-layer program) — the two `IdPush` steps,
today:

```
(((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Y , id X ⟫) ⟪ ↑β:=ℕ , ↥Y , unseal X ⟫) ⟪ ↑α:=ℕ , ↥X , unseal X ⟫
 --IdPush-->
(((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Y , id X ⟫) ⟪ ↑β:=ℕ , ↥X , ↥Y , unseal X ⟫) ⟪ ↑α:=ℕ , ↥X , ↓X , id ℕ ⟫
```

and with the store, `Σ = [ℓ₀ ↦ ℕ , ℓ₁ ↦ ℕ]`:

```
(((7 ⟪ ↓X , seal ℓ₀ ⟫) ⟪ ↓Y , id ℓ₀ ⟫) ⟪ ↥Y:=ℓ₁ , unseal ℓ₀ ⟫) ⟪ ↥X:=ℓ₀ , unseal ℓ₀ ⟫
 --IdPush-->
(((7 ⟪ ↓X , seal ℓ₀ ⟫) ⟪ ↓Y , id ℓ₀ ⟫) ⟪ ↥Y:=ℓ₁ , ↥X:=ℓ₀ , unseal ℓ₀ ⟫) ⟪ ↓X , ↥X:=ℓ₀ , id ℕ ⟫
```

Note `id ℓ₀`: today's `id X` had to be re-spelled as `id X′` when pushed
into the merged frame (the `` ` X′ ≈ ` X `` premise); the address needs
no spelling.  The `↑β:=ℕ` bind that today rides on the middle frame is
the store cell `ℓ₁`, allocated by the inner `TyBeta`, and is never
mentioned again — the `↥Y:=ℓ₁` unlock is the only trace of it, exactly
as `↑β` today is only ever reached through `↥Y`.

## 5. What the metatheory loses and gains

Retired outright: `RepWeaken.agda` (`renᴹᴿ`, `RepWk`, `⊢renᴿ`,
`cross-Λ-⊢`), `RepRefines`/`⊢refine`, `SameConv`/`respell`/`SameTyExt`,
`pushRepBinds`/`extendReps`/`numBinds` arithmetic, `underRepBinds`,
`renᴮ²`, the represent-half of `ren²` except `shiftVar`, and the
`ShiftAudit` frame-exactness obligations of `Peel`/`TyPeelR-⟪⟫` (no
representation is ever moved).  `MoveScope.agda`'s
`preserve-CancelR`/`preserve-IdPush` reduce to the store lookup.

New: `Store`, `_⊑_` and the monotonicity family `⊢-⊑` (the STLCRef
store-typing pattern, already in this repo), the telescope `_⊢Σ_`,
`_[_]ᴿ` with `⊢[]ᴿ` (a positional substitution on pointers — the same
shape as today's `renᴹ²` on the represent side), `reveal ℓ`, `mkIdᴿ`.

The theorem statements:

```agda
Preservation = ∀ {Σ Σ′ Δ M M′ A} → n ⊢Σ Σ → WfCtx Σ Δ
  → Σ ; Δ ∣ [] ⊢ M ⦂ A → Σ ∣ Δ ⊢ M -→ M′ ∣ Σ′
  → (Σ ⊑ Σ′) × (n ⊢Σ Σ′) × (Σ′ ; Δ ∣ [] ⊢ M′ ⦂ A)

Progress      = ∀ {Σ Δ M A} → Σ ; Δ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ ∃[ M′ ] ∃[ Σ′ ] (Σ ∣ Δ ⊢ M -→ M′ ∣ Σ′)

det : Σ ; Δ ∣ [] ⊢ M ⦂ A → Σ ∣ Δ ⊢ M -→ M′ ∣ Σ′ → Σ ∣ Δ ⊢ M -→ M″ ∣ Σ″
  → M′ ≡ M″ × Σ′ ≡ Σ″
```

Color/scope-map preservation: the residual renaming `ρ` a move delivers
becomes the identity on `loc` and `shiftVar` on `var`, so
`ScopeMapPreservation` should become `names Δ₂ ≡ names Δ₁` up to the
unlock the boundary itself performs — worth re-stating once the core is
in.

## 6. Decision points, collected

- **R1** `Rep = Ty RVar` (parameterise `Types.agda`) vs a separate `Rep`
  datatype.  Recommendation: parameterise.
- **R2** conversions cite `RVar` (recommended; deletes all respelling)
  vs keep ordinary names and `SameConv` (R2-b; deletes only the shifts).
- **R3** `TyBeta`/`TyPeelR` perform `N [ ℓ ]ᴿ` — pointer substitution in
  the body.  The alternative, keeping the `Λ`'s slot as a lexical
  `abstR` and refining it in place, is today's design and is what the
  store is replacing; I see no third option.
- **R4** `Σ ∷ʳ R` (addresses are levels, stable under extension).  With
  `R ∷ Σ` every extension would re-index every address — the shift we
  are trying to eliminate.
- **R5** keep `abst : ℕ` in `Ctxᵗ` (needed to type `Λ` bodies and to
  state reduction at the probes' `underΛ empty`), or fix reduction at
  `abst = 0`.  Recommendation: keep; it costs one field.

## 7. Suggested order of work

1. `Types.agda` parameterised; `Ctx.agda` with `RVar`, `Store`,
   `_⊢Σ_`, `WfCtx Σ`; `Boundary.agda` as `List Change` with the two
   readings; `Conversion.agda` on `RVar` (R2).  Statements only, then
   `Terms.agda`'s `env`.
2. `Reduction.agda` store-passing, with `_[_]ᴿ` in `TermSubst.agda`.
   `det` and `value-¬step`.
3. `TypeCheck.agda`/`Eval.agda`: `infer` takes `Σ`; `step` returns
   `Σ′`; `Reaches` records the final store.  Rerun the 23 runs — their
   step counts should be UNCHANGED (no rule was added or split).
4. `proof/Preserve.agda`: the `⊢-⊑` family first, then rule by rule;
   `TyPeelR-⟪⟫` should be the big win.
5. Progress, type safety, then the color theorem's restatement.
