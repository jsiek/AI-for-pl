# Subst: renaming and substitution by kits

A library for parallel renaming and substitution of de Bruijn syntax, after
McBride's "Type-preserving renaming and substitution" and the framework in the
`denotational_semantics` repository (`Framework/Syntax/{Kit,TypedSubst}.agda`).
The language writes **one traversal** of its terms. Renaming and substitution
are that traversal with two different **kits**. The library derives the
standard API and its laws from **two inductions** that the language proves.

No function extensionality is used anywhere: substitutions are always
compared pointwise (`∀ x → σ x ≡ τ x`). Everything checks with `agda --safe`.

## What you get, and what it costs

### What the language writes (one-level)

| piece | size | what it is |
|---|---|---|
| `trav` | one clause per term constructor | the traversal; under a binder it calls `exts 𝒦 σ` |
| `trav-var` | usually `λ _ _ _ → refl` | `trav 𝒦 σ (` x) ≡ Kit.tm 𝒦 (σ x)` |
| `fuse : Fuse` | one clause per constructor, each a `cong` of the induction hypothesis | two traversals fuse into one (statement below) |
| `sub-id : SubId` | one clause per constructor | substituting variables for themselves is the identity |

For STLC (6 constructors), that is the 6-clause `trav` in
`STLC/agda-subst/STLC.agda` and the 58-line `STLC/agda-subst/proof/Subst.agda`.
That file replaces the 280 lines of hand-written substitution algebra in
`STLC/agda`. In return, one line gives every theorem in the next section:

    open Lemmas fuse sub-id public

The two statements the language proves are:

    Fuse  = ∀ 𝒦₁ 𝒦₂ 𝒦₃ (R : relation on σ₁ σ₂ σ₃)
            → (R σ₁ σ₂ σ₃ → R (exts 𝒦₁ σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
            → (R σ₁ σ₂ σ₃ → ∀ x → trav 𝒦₂ σ₂ (tm₁ (σ₁ x)) ≡ tm₃ (σ₃ x))
            → R σ₁ σ₂ σ₃ → ∀ M → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M

    SubId = (∀ x → σ x ≡ ` x) → ∀ M → sub σ M ≡ M

### Notation

The statements below leave implicit arguments out, as the Agda does. All
hypotheses are pointwise, over every variable `x`, and `≡` is propositional
equality.

    r, s        : ∀ {A} → Var Γ A → Var Δ A      -- renamings
    σ, τ, ρ     : ∀ {A} → Var Γ A → Tm Δ A       -- substitutions (Sub tmK Γ Δ)
    ren r M     = trav varK r M                  -- renaming
    sub σ M     = trav tmK σ M                   -- substitution
    ⇑ M         = ren there M                    -- weaken past one binder
    ids         = `_                             -- identity substitution
    W • σ       : here ↦ W,  there x ↦ σ x
    exts 𝒦 σ    : here ↦ vr here,  there x ↦ wk (σ x)   -- lift under a binder
    N [ M ]     = sub (M • ids) N                -- single substitution
    σ ⨟ τ       = λ x → sub τ (σ x)              -- composition

### Theorems (one-level, `proof/Kit.agda`)

**Composition.** Two traversals in a row are one traversal. Each lemma takes
the composite on variables as a hypothesis, so it holds for any third
substitution that agrees with the composite. The hypothesis is usually
`λ _ → refl`.

    ren-ren : (∀ x → r₂ (r₁ x) ≡ r₃ x)  → ren r₂ (ren r₁ M) ≡ ren r₃ M
    ren-sub : (∀ x → σ (r x) ≡ τ x)     → sub σ (ren r M) ≡ sub τ M
    sub-ren : (∀ x → ren r (σ x) ≡ τ x) → ren r (sub σ M) ≡ sub τ M
    sub-sub : (∀ x → sub τ (σ x) ≡ ρ x) → sub τ (sub σ M) ≡ sub ρ M

For example, `sub-sub (λ _ → refl) M : sub τ (sub σ M) ≡ sub (σ ⨟ τ) M`.
The same composition holds for any kits:

    ren-trav  : (∀ x → σ (r x) ≡ τ x)
              → trav 𝒦 σ (ren r M) ≡ trav 𝒦 τ M
    trav-trav : Laws 𝒦₁ → Laws 𝒦₂ → Laws 𝒦₃
              → (∀ x → trav 𝒦₂ σ₂ (tm₁ (σ₁ x)) ≡ tm₃ (σ₃ x))
              → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M

`Laws 𝒦` collects `tm (vr x) ≡ ` x`, `tm (wk k) ≡ ⇑ (tm k)`, and
`trav 𝒦 (exts 𝒦 τ) (⇑ M) ≡ ⇑ (trav 𝒦 τ M)`. The library proves it for both
kits (`varL`, `tmL`).

**Identity and congruence.** Pointwise-equal substitutions give equal
results, so you never need extensionality.

    sub-id     : (∀ x → σ x ≡ ` x)  → sub σ M ≡ M       -- proved by the language
    ren-id     : (∀ x → r x ≡ x)    → ren r M ≡ M
    trav-id    : Laws 𝒦 → (∀ x → tm (σ x) ≡ ` x) → trav 𝒦 σ M ≡ M
    trav-cong  : (∀ x → σ x ≡ τ x)  → trav 𝒦 σ M ≡ trav 𝒦 τ M
    ren-cong   : (∀ x → r x ≡ s x)  → ren r M ≡ ren s M
    sub-cong   : (∀ x → σ x ≡ τ x)  → sub σ M ≡ sub τ M
    ren-as-sub : ren r M ≡ sub (λ x → ` (r x)) M

**Single substitution.** These are the lemmas that type-safety and
logical-relations proofs use.

    sub-⇑-• : sub (W • σ) (⇑ M) ≡ sub σ M
    ⇑-[]    : ⇑ M [ W ] ≡ M
    exts-[] : sub (exts tmK σ) N [ W ] ≡ sub (W • σ) N
    sub-[]  : sub σ (N [ M ]) ≡ sub (exts tmK σ) N [ sub σ M ]
    ren-[]  : ren r (N [ M ]) ≡ ren (exts varK r) N [ ren r M ]
    trav-[] : Laws 𝒦 → trav 𝒦 σ (N [ M ]) ≡ trav 𝒦 (exts 𝒦 σ) N [ trav 𝒦 σ M ]

What each is for:
- `⇑-[]` and `sub-⇑-•`: a substitution cancels a weakening.
- `exts-[]`: the λ case of a logical relation. Substituting the environment
  under the binder and then the argument is one substitution. STLC's
  termination proof uses it in exactly this way.
- `sub-[]`, `ren-[]`, `trav-[]`: substitution and renaming commute with
  β-reduction.

**Building blocks.** These are also exported, for proofs that go below the
API:
- `cons-here`, `cons-there`, `exts-here`, `exts-there`: the computation laws
  of `•` and `exts`. They are `refl` in every instance.
- `exts-cong`.
- `sub-id-exts`, `trav-id-exts`, `trav-trav-exts`: the binder closures of the
  identity and fusion hypotheses.

### What it does not give

- **Typing preservation** for an extrinsically typed language. Write one
  lemma for the traversal over both kits, as `typing_trav` in
  `STLC/agda-subst/proof/TypeSafety.agda` does in about 25 lines. `typing_rename`
  and `typing_subst` are its two instances.
- **Named lemmas** for associativity of `⨟`, or for the double-substitution
  law `N [ M ] [ L ] ≡ …`. Each follows from `sub-sub` and `sub-cong` in a
  few lines.
- **Lifting under several binders at once** (`exts*`), sorts with no
  variables (kinds as a separate sort), and automation. Every traversal and
  induction is written by hand.

## Example: STLC (`STLC/agda-subst`)

The language gives the traversal, one clause per constructor. Under a binder
it uses the library's `exts`:

    trav : (𝒦 : Kit) → ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A
    trav 𝒦 σ (` i)     = Kit.tm 𝒦 (σ i)
    trav 𝒦 σ (ƛ A ⇒ N) = ƛ A ⇒ trav 𝒦 (exts 𝒦 σ) N
    trav 𝒦 σ (L · M)   = trav 𝒦 σ L · trav 𝒦 σ M
    ...
    open Substitution trav public   -- ren, sub, ⇑, _[_], ...

A kit says what a variable maps to (`K`), how a variable becomes one (`vr`),
how one becomes a term (`tm`), and how one moves under a binder (`wk`):

| kit    | `K`         | `vr` | `tm`  | `wk`        | traversal = |
|--------|-------------|------|-------|-------------|-------------|
| `varK` | variables   | id   | `` ` ``   | `there`     | `ren`       |
| `tmK`  | terms       | `` ` ``  | id    | `ren there` | `sub`       |

## Variables are abstract (`Scope.agda`)

The library only needs a *scope structure*: scopes, sorts, variables, the
extension `Γ ▷ A`, `here`, `there`, and induction on the variables of
`Γ ▷ A`. The provided instances are:

- `ℕScope`: raw de Bruijn numbers, one scope, one sort (`⊤`). This is how STLC
  keeps its extrinsic `Term` with `ℕ` variables and `Subst = ℕ → Term`.
- `ctxScope T`: typed indices `Γ ∋ A` into `Ctx T` (`∅`, `Γ , A`, `Z`, `S x`).
- System F builds its own `tyScope` for `TyVar Δ` (8 lines).

Every operation still computes after instantiation. For example, in STLC,
`exts varK ρ (suc i)` reduces to `suc (ρ i)`, and the `Examples` reduction
traces check by `refl`.

## Several sorts of variables in one scope (`examples/MultiSortedF.agda`)

If a language is extrinsically typed and has several sorts of variables,
then the one-level library already handles it, with no change. This is the
multi-sorted design of Saffrich, "Abstractions for Multi-Sorted
Substitutions" (ITP 2024). Use `ctxScope Sort` with a data type of sorts,
write one syntax `S ⊢ s` and one traversal, and prove `fuse` and `sub-id`.

For example, in an extrinsic System F with sorts `𝕖` (expressions) and `𝕥`
(types), take the body of `Λα. λ(f : ∀β. β ⇒ β). f ∙ α`. Its scope is
`∅ , 𝕥 , 𝕖`, so `f` is `Z` and `α` is `S Z`:

    body = ƛ `∀ (` Z ⇒ ` Z) ˙ (` Z ∙ ` (S Z))

    inst : body [ `Nat ] ≡ ƛ `∀ (` Z ⇒ ` Z) ˙ (` Z ∙ `Nat)
    inst = refl

Here type instantiation is the same single substitution `_[_]` as β for λ,
and the library's `sub-[]` serves both sorts. This does not work for
*intrinsically* typed System F: its terms are indexed by types, so terms
and their types cannot share one scope. That case is `Poly.agda`. The
comparison with the paper is in `notes/ITP2024-comparison.md`.

## Polymorphic languages (`Poly.agda`)

In intrinsically typed System F, a type abstraction moves terms *across* a
type binder. Its body lives in a weakened context:

    Λ_ : Δ ,α ∣ ⇑ᶜ Γ ⊢ A → Δ ∣ Γ ⊢ `∀ A

so one level of kits is not enough. `Poly` is built on a one-level instance
for the types and has **two traversals** of terms, both written by the
language:

- `travᵀ 𝒯 θ ρ` renames or substitutes the **type variables** of a term. It
  takes a type-level kit `𝒯`, a map of types `θ`, and a map of term variables
  along `θ`, `ρ : ∀ {A} → Γ ∋ A → Γ' ∋ act 𝒯 θ A`. It gives `renᵀ`, `subᵀ`,
  `⇑ᵀ` (weakening past a type variable), and `N [ B ]ᵀ`.
- `trav 𝒦 σ` renames or substitutes the **term variables** of a term. It goes
  under `Λ` with `⇑s`, which needs the kit to move a thing past a type
  variable (`wkα`); for the kit of terms that is `⇑ᵀ`. It gives `ren`, `sub`,
  `⇑`, and `N [ M ]`, and it keeps the type of the term exactly.

Here is why the two are separate. With one traversal indexed by a type map,
the term substitution `N [ W ]` would have type `sub ids B` rather than `B`,
so even β-reduction would need a cast.

Casts on terms appear only where the language needs a type equation, which
in System F is the `_∙_` clause of `travᵀ`:

    travᵀ 𝒯 θ ρ (M ∙ B) =
      convᵀ (sym (act-[] 𝒯 θ A B)) (travᵀ 𝒯 θ ρ M ∙ act 𝒯 θ B)

The other casts are on *variables*, at a type binder (`⇑ρ`, `instᵛ`). For
closed types the casts compute away. `intrinsic-subst/Examples.agda` checks
`(Λα. λ(f : ∀β. β→β). f [α]) [ℕ] id 1 —↠ 1` step by step.

### What the language writes (two-level)

The numbers below are for intrinsic System F, which has 5 type constructors
and 11 term constructors (`SystemF/agda/intrinsic-subst`).

| piece | System F | what it is |
|---|---|---|
| `travᵗ`, `fuseᵗ`, `sub-idᵗ` | 5 clauses each | the one-level library for types (`proof/TypeSubst.agda`, 40 lines) |
| `travᵀ` | 11 clauses, 1 cast | type variables in terms |
| `trav` | 11 clauses | term variables in terms |
| `fuseᵀ`, `idᵀ` | 11 clauses each, with `_≅_` | fusion and identity of `travᵀ` |
| `commute` | 11 clauses | `trav` after `travᵀ` is `travᵀ` after `trav` |
| `fuse`, `sub-id` | 11 clauses each | as in the one-level library |
| congruences | 10 one-line lemmas | `ƛ-≅`, `·-≅`, `Λ-≅`, ...: each constructor respects `_≅_` given equal indices |

`SystemF/agda/intrinsic-subst/proof/TermSubst.agda`, which has all the
term-level pieces, is 263 lines.

### Theorems (two-level, `proof/Poly.agda`)

**Term variables.** You get every one-level theorem above, with the same
names and statements, for the term-level `ren`, `sub`, `exts`, `_•_` and
`_[_]`. All of them are homogeneous (`≡`), because term substitution keeps
types:
- `ren-ren`, `ren-sub`, `sub-ren`, `sub-sub`, `ren-trav`, `trav-trav`;
- `trav-cong`, `ren-cong`, `sub-cong`, `ren-id`, `ren-as-sub`;
- `sub-⇑-•`, `⇑-[]`, `exts-[]`, `sub-[]`, `ren-[]`, `trav-[]`.

**Term variables and type variables.** These are also homogeneous. They say
that a substitution of term variables commutes with a map of type
variables:

    trav-travᵀ : KitLaws 𝒦
               → (∀ x → tm (σ' (ρ x)) ≡ travᵀ 𝒯 θ ρ₁ (tm (σ x)))
               → trav 𝒦 σ' (travᵀ 𝒯 θ ρ M) ≡ travᵀ 𝒯 θ ρ₁ (trav 𝒦 σ M)
    ren-travᵀ  : (∀ x → r' (ρ x) ≡ ρ₁ (r x))
               → ren r' (travᵀ 𝒯 θ ρ M) ≡ travᵀ 𝒯 θ ρ₁ (ren r M)
    sub-⇑ᵀ     : sub (⇑s tmK σ) (⇑ᵀ M) ≡ ⇑ᵀ (sub σ M)
    travᵀ-[]   : travᵀ 𝒯 θ ρ (N [ M ]) ≡ travᵀ 𝒯 θ (extρ 𝒯 θ ρ) N [ travᵀ 𝒯 θ ρ M ]

In words:
- `sub-⇑ᵀ`: substitution commutes with weakening past a type variable. This
  is what term substitution under `Λ` needs. `⇑s-⇑ᵀ` is the same for any
  kit.
- `travᵀ-[]`: a type substitution commutes with β for λ.

**Type variables in terms.** These are heterogeneous (`_≅_`), because two
type maps in a row give a type that equals the composite only
propositionally:

    fuseᵀ  : FuseHypᵀ 𝒯₁ 𝒯₂ 𝒯₃ θ₁ θ₂ θ₃ ρ₁ ρ₂ ρ₃
           → travᵀ 𝒯₂ θ₂ ρ₂ (travᵀ 𝒯₁ θ₁ ρ₁ M) ≅ travᵀ 𝒯₃ θ₃ ρ₃ M
    idᵀ    : IdHypᵀ 𝒯 θ ρ → travᵀ 𝒯 θ ρ M ≅ M
    ⇑ᵀ-[]ᵀ : ⇑ᵀ M [ B ]ᵀ ≅ M

`FuseHypᵀ` asks for three facts:
- the type maps fuse on type variables:
  `travᵗ θ₂ (tm (θ₁ α)) ≡ tm (θ₃ α)`;
- the target contexts are equal: `Γ'' ≡ Γ'''`;
- the term-variable maps fuse: `ρ₂ (ρ₁ x) ≅ ρ₃ x`.

`IdHypᵀ` asks for the identity on type variables, equal contexts, and
`ρ x ≅ x`. The library closes both hypotheses under a term binder and a
type binder (`fuseᵀ-ext`, `fuseᵀ-⇑`, `idᵀ-ext`, `idᵀ-⇑`). It also gives
`fuseᵀ-ty` (the types fuse on every type) and `idᵀ-ty`. When the two sides
have the same type, `≅-to-≡` turns a result into `≡`.

**What it does not give.**
- **A named lemma** for term substitution commuting with type
  instantiation, `sub σ (N [ B ]ᵀ)` against `sub (⇑s σ) N [ B ]ᵀ`. The
  type-abstraction case of the parametricity proof derives a variant from
  `trav-travᵀ` and `fuseᵀ` in about 30 lines (`Λ-close` in
  `SystemF/agda/intrinsic-subst/proof/Parametricity.agda`).
- **Fusion of `renᵀ`/`subᵀ` into their canonical contexts `mapᶜ 𝒯 θ Γ`.**
  Use `fuseᵀ` with `mapᵛ` as the term-variable maps.

## Files

- `Scope.agda`: scope structures and the `ℕScope` / `ctxScope` instances.
- `Kit.agda`: one-level kits, `Sub`, `exts`, `varK`, `_•_`, `ids`, and,
  given `trav`, `ren`, `tmK`, `sub`, `↑`, `⇑`, `_⨟_`, `_[_]`, and the
  *statements* of the laws, `Fuse`, `SubId`, and `Laws`.
- `Poly.agda`: the two-level extension for polymorphic languages. It takes
  the laws of the type-level kits that its casts need as parameters, so it
  imports no proofs.
- `proof/Kit.agda`: one-level laws (`Fuse`, `SubId` → `Lemmas`).
- `proof/Poly.agda`: two-level laws.
- `examples/MultiSortedF.agda`: multi-sorted extrinsic System F on the
  one-level library.
- `notes/ITP2024-comparison.md`: comparison with Saffrich (ITP 2024).
- `All.agda`: aggregate driver.

The top-level files import nothing from `proof/`, apart from the `All`
driver. So a client can keep the repository's audit rule: its definitions
use only statements, and the proofs come in through thin top-level
wrappers.

## Checking

The module names are `Subst.*`, so the repository root is the include root:

    make            # agda --safe -i .. All.agda, plus the postulate grep

A client adds the repository root as an include path, for example
`agda -i . -i ../.. All.agda` from `STLC/agda-subst`.
