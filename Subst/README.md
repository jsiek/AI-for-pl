# Subst: renaming and substitution by kits

A library for parallel renaming and substitution of de Bruijn syntax, after
McBride's "Type-preserving renaming and substitution" and the framework in the
`denotational_semantics` repository (`Framework/Syntax/{Kit,TypedSubst}.agda`).
The language writes **one traversal** of its terms. Renaming and substitution
are that traversal with two different **kits**. The library derives the
standard API and its laws from **two inductions** that the language proves.

No function extensionality is used anywhere: substitutions are always
compared pointwise (`∀ x → σ x ≡ τ x`).

## Example: STLC (`STLC/agda-subst`)

The language gives the traversal, one clause per constructor. Under a binder
it uses the library's `exts`:

    trav : (𝒦 : Kit) → ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A
    trav 𝒦 σ (` i)     = Kit.tm 𝒦 (σ i)
    trav 𝒦 σ (ƛ A ⇒ N) = ƛ A ⇒ trav 𝒦 (exts 𝒦 σ) N
    trav 𝒦 σ (L · M)   = trav 𝒦 σ L · trav 𝒦 σ M
    ...
    open Substitution trav public   -- ren, sub, ⇑, _[_], ...

The proofs need two inductions, one clause per constructor: `fuse` (two
traversals fuse into one) and `sub-id`. Everything else comes from the
library, for example `ren-ren`, `ren-sub`, `sub-ren`, `sub-sub`, `trav-cong`,
`ren-id`, `⇑-[]`, `exts-[]`, and `sub-[]`:

    open Lemmas fuse sub-id public

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

The proofs need five inductions on terms (`proof/Poly.agda` states them):

- `Fuseᵀ`, `Idᵀ`: fusion and identity of `travᵀ`. These change the types of
  terms by equations that hold only propositionally, so they are stated with
  heterogeneous equality, under the hypotheses `FuseHypᵀ` and `IdHypᵀ`. The
  library closes those hypotheses under both binders (`fuseᵀ-ext`, `fuseᵀ-⇑`,
  `idᵀ-ext`, `idᵀ-⇑`).
- `Commute`: `trav` after `travᵀ` is `travᵀ` after `trav`.
- `Fuse`, `SubId`: as in the one-level library, now also closed under `⇑s`.

The library derives the term-level API from these: `ren-trav`, `sub-ren`,
`trav-trav`, `ren-ren`, `ren-sub`, `sub-sub`, `trav-cong`, `ren-id`,
`ren-as-sub`, `⇑-[]`, `exts-[]`, `trav-[]`, `sub-[]`, `sub-⇑ᵀ` (substitution
commutes with type weakening), `trav-travᵀ`, `travᵀ-[]`, and `⇑ᵀ-[]ᵀ`.

## Files

- `Scope.agda`: scope structures and the `ℕScope` / `ctxScope` instances.
- `Kit.agda`: one-level kits, `Sub`, `exts`, `varK`, `_•_`, `ids`, and,
  given `trav`, `ren`, `tmK`, `sub`, `↑`, `⇑`, `_⨟_`, `_[_]`, and the
  *statements* of the laws, `Fuse`, `SubId`, and `Laws`.
- `Poly.agda`: the two-level extension for polymorphic languages. It takes
  the laws of the type-level kits that its casts need as parameters, so it
  imports no proofs.

The top-level files import nothing from `proof/`, apart from the `All`
driver. So a client can keep the repository's audit rule: its definitions
use only statements, and the proofs come in through thin top-level
wrappers.
- `proof/Kit.agda`: one-level laws (`Fuse`, `SubId` → `Lemmas`).
- `proof/Poly.agda`: two-level laws.
- `examples/MultiSortedF.agda`: multi-sorted extrinsic System F on the
  one-level library.
- `notes/ITP2024-comparison.md`: comparison with Saffrich (ITP 2024).
- `All.agda`: aggregate driver.

## Checking

The module names are `Subst.*`, so the repository root is the include root:

    make            # agda --safe -i .. All.agda, plus the postulate grep

A client adds the repository root as an include path, for example
`agda -i . -i ../.. All.agda` from `STLC/agda-subst`.
