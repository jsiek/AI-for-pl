# `Subst` and "Abstractions for Multi-Sorted Substitutions" (ITP 2024)

The paper is by **Hannes Saffrich** alone (University of Freiburg),
LIPIcs ITP 2024, article 32, doi 10.4230/LIPIcs.ITP.2024.32. The
supplement is <https://github.com/m0rphism/kitty-supplement> (a
simplified framework, `Simple/Kits.agda`, and System F,
`Simple/SystemF.agda`). The full framework, which adds reflection, is
<https://github.com/m0rphism/kitty>. I read the paper, both System F
files, and the parts of the full framework that cover map equality and
traversal (`KitHomotopy`, `MultiTraversal`, `MultiSub`, `Examples/SystemF`).

## Recommendation in brief

- **Keep `Poly` as it is.** The paper's main idea, multi-sorted syntax,
  works only for extrinsic typing. Section 2.2 says so directly: an
  intrinsically typed multi-sorted syntax would have to index `_⊢_` by
  itself. So the paper has nothing that would remove our casts or our
  heterogeneous equality from intrinsic System F.
- **Our one-level library already supports multi-sorted syntax.** If a
  language is extrinsically typed, then `Subst.Kit (ctxScope Sort)` with one
  traversal, `fuse`, and `sub-id` gives the paper's design with no change
  to `Subst/`. I checked this with `agda --safe` on a System F with term and
  type variables in one scope (Section 1c).
- **Adopt later, when an extrinsic polymorphic client needs it:** the
  paper's *typing kit*, which gives one type-preservation lemma for both
  renaming and substitution. STLC already has a local version of it
  (`typing_trav` in `STLC/agda-subst/proof/TypeSafety.agda`).
- **Do not adopt** reflection, instance-argument kits, or the `CKit`
  composition abstraction. Section 6 gives the reasons.

## 1. The running example

Take the first step of `intrinsic-subst/Examples.agda`. It instantiates a
type abstraction:

    (Λα. λ(f : ∀β. β ⇒ β). f [α]) [ℕ]   —→   λ(f : ∀β. β ⇒ β). f [ℕ]

The interesting subterm is the type application `f [α]`, written `f ∙ α`
in our Agda. Below we follow `f ∙ α` through each design, and then through
the proof that two substitutions fuse on `M ∙ B`.

### 1a. Our design (`Subst/Poly.agda`, intrinsic System F)

Scopes. There are two separate index spaces.

    Δ = ∅ ,α                       α = Z : TyVar Δ
    Γ = ∅ , `∀ (` Z ⇒ ` Z)         f = Z : Γ ∋ `∀ (` Z ⇒ ` Z)

    N : ∅ ,α ∣ ∅ , `∀ (` Z ⇒ ` Z) ⊢ (` Z ⇒ ` Z) [ ` Z ]ᵗ
    N = ` Z ∙ ` Z                  -- term variable f, type variable α

The step is `N [ `ℕ ]ᵀ = travᵀ subKᵗ θ (instᵛ `ℕ) N` with
`θ = `ℕ TK.• TK.ids`. The `_∙_` clause of `travᵀ` (in `Terms.agda`) is the
only clause that casts a term:

    travᵀ 𝒯 θ ρ (_∙_ {A = A} M B) =
      convᵀ (sym (act-[] 𝒯 θ A B)) (travᵀ 𝒯 θ ρ M ∙ act 𝒯 θ B)

So the step produces

    convᵀ p (` Z ∙ `ℕ)
      where p : act θ ((` Z ⇒ ` Z) [ ` Z ]ᵗ)
                ≡ act (exts θ) (` Z ⇒ ` Z) [ `ℕ ]ᵗ

The variable `f` also passes through `instᵛ`, which casts it by `⇑-[]`. In
this closed example both sides of `p` are `ℕ ⇒ ℕ`, so `p` reduces to
`refl` and the cast goes away. That is why `Examples.agda` checks by
`refl`. For an open `M ∙ B` the cast stays.

The proof. `Fuseᵀ` is stated with `_≅_`. Its `_∙_` clause in
`proof/TermSubst.agda` is 15 lines and chains four heterogeneous steps:

    travᵀ θ₂ (travᵀ θ₁ (M ∙ B))
      ≅ travᵀ θ₂ (travᵀ θ₁ M ∙ θ₁B)      -- travᵀ-conv: drop the inner cast
      ≅ travᵀ θ₂ (travᵀ θ₁ M) ∙ θ₂θ₁B    -- convᵀ-≅: drop the outer cast
      ≅ travᵀ θ₃ M ∙ θ₃B                 -- ∙-≅ with the induction hypothesis
      ≅ travᵀ θ₃ (M ∙ B)                 -- convᵀ-≅ backwards

Every other clause of `Fuseᵀ` and `Idᵀ` also needs a heterogeneous
congruence (`ƛ-≅`, `·-≅`, `Λ-≅`, ...). The reason is that the result types
`act θ₂ (act θ₁ A)` and `act θ₃ A`, and the contexts, are equal only
propositionally.

### 1b. The paper's design (multi-sorted, extrinsic)

Scopes. There is one index space, a list of sorts. Variables of all sorts
are interleaved in binding order:

    data Sort : SortTy → Set where 𝕖 𝕥 : Sort Var ; 𝕜 : Sort NoVar

    scope of the body:  𝕖 ∷ 𝕥 ∷ []      f = zero : 𝕖,  α = suc zero : 𝕥

    Λα (λx (` zero ∙ ` suc zero))   : [] ⊢ 𝕖

(The paper's λ has no type annotation. The supplement has no `ℕ`, so take
`ℕ` to be some closed type.) A map acts on every sort at once,
`S₁ →ₖ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢ s`. Type instantiation is the same
singleton map `⦅_⦆` that β for λ uses:

    β-Λ : (Λα e₁) ∙ t₂ ↪ e₁ ⋯ ⦅ t₂ ⦆

    (λx (` zero ∙ ` suc zero)) ⋯ ⦅ ℕ ⦆
      = λx (((` zero) ⋯ (⦅ ℕ ⦆ ↑ 𝕖)) ∙ ((` suc zero) ⋯ (⦅ ℕ ⦆ ↑ 𝕖)))
      = λx (` zero ∙ wk 𝕖 ℕ)
      = λx (` zero ∙ ℕ)

There is no cast, because terms are indexed by their scope but not by
their types. The `_∙_` clauses of the traversal and of fusion are each one
line:

    (t₁ ∙ t₂) ⋯ ϕ = (t₁ ⋯ ϕ) ∙ (t₂ ⋯ ϕ)
    fusion (t₁ ∙ t₂) ϕ₁ ϕ₂ = cong₂ _∙_ (fusion t₁ ϕ₁ ϕ₂) (fusion t₂ ϕ₁ ϕ₂)

The type equation does not go away. It moves to the typing derivation, in
the `⊢∙` clause of the one type-preservation lemma `_⊢⋯_`:

    ⊢∙ ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ =
      subst (λ t → _ ⊢ _ ∶ t) (sym (dist-↑-⦅⦆-⋯ t₁ t₂ _))
            (⊢∙ (⊢t₁ ⊢⋯ (⊢ϕ ⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))

`dist-↑-⦅⦆-⋯` says `t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ s) ⋯ ⦅ x/t &/⋯ ϕ ⦆`. This
equation is between types of the same sort `S ⊢ 𝕥`, so it is homogeneous.

### 1c. The paper's idea on our library (experiment)

The whole file is in the Appendix (93 lines). It was checked outside the
repository with `agda --safe -i /Users/jsiek/AI-for-pl`, Agda 2.8.0.2. The sorts are `𝕖 𝕥`, the scope
structure is `ctxScope Sort`, and there is one syntax `_⊢_ : Ctx Sort →
Sort → Set` with 8 constructors. It writes one `trav` (8 clauses), `fuse`
(8 clauses) and `sub-id` (8 clauses). Then it opens `Lemmas fuse sub-id`
with no change to `Subst/`.

    body : ∅ , 𝕥 ⊢ 𝕖
    body = ƛ `∀ (` Z ⇒ ` Z) ˙ (` Z ∙ ` (S Z))     -- Z = f : 𝕖, S Z = α : 𝕥

    trav 𝒦 σ (M ∙ B) = trav 𝒦 σ M ∙ trav 𝒦 σ B
    go r (M ∙ B) = cong₂ _∙_ (go r M) (go r B)         -- the fuse clause

    inst : body [ `Nat ] ≡ ƛ `∀ (` Z ⇒ ` Z) ˙ (` Z ∙ `Nat)
    inst = refl

    -- one library lemma, used at sort 𝕥 (β for Λ) and at sort 𝕖 (β for λ)
    sub-[]ᵗ : sub σ (N [ B ]) ≡ sub (exts tmK σ) N [ sub σ B ]   -- N : Γ , 𝕥 ⊢ 𝕖
    sub-[]ᵉ : sub σ (N [ M ]) ≡ sub (exts tmK σ) N [ sub σ M ]   -- N : Γ , 𝕖 ⊢ 𝕖

So, if a language is extrinsically typed, then our `Subst.Kit` already
handles a single parallel substitution over all variable sorts. There is
one restriction: `Kit` indexes terms by the sorts of variables
(`Tm : Sc → Sort → Set`), so it has no counterpart of the paper's `NoVar`
sort for kinds. System F needs only one kind, so dropping `𝕜` is harmless.
The experiment does not cover typing (Section 6, item 2).

## 2. How each design represents sorts, scopes and kits

| | `Subst` (ours) | Saffrich (ITP 2024) |
|---|---|---|
| scopes | abstract `Scope` record: `Sc`, `Sort`, `Var`, `_▷_`, `here`, `there`, `var-ind`; instances `ℕScope`, `ctxScope T`, System F's `tyScope` | concrete `List (Sort Var)`, variables `S ∋ s` |
| sorts | the sorts of the variables, a field of `Scope` (`⊤` for STLC and for System F types) | `Sort : SortTy → Set`, with `Var`/`NoVar` sorts; kinds are `NoVar` |
| syntax | `Tm : Sc → Sort → Set`; for System F, types `Type Δ` and intrinsically typed terms `Δ ∣ Γ ⊢ A` are separate families | one family `S ⊢ s` for expressions, types and kinds |
| kit | `K`, `vr`, `tm`, `wk` (and `wkα` in `Poly`); laws in a separate `Laws` record | `id/``, ``/id``, `wk` and four laws (`` `/`-is-` ``, two injectivities, `wk-id/``); `WkKit` adds `wk-`/id` |
| kit selection | explicit argument, `trav 𝒦 σ` | instance arguments, `t ⋯ ϕ` |
| maps | `Sub 𝒦 Γ Δ = ∀ {A} → Var Γ A → K Δ A` | `S₁ →ₖ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢ s` |
| multi-sorted System F | two levels: kit `TK` on types; `travᵀ 𝒯 θ ρ` for type variables in terms; `trav 𝒦 σ` for term variables, crossing `Λ` by `⇑s`/`wkα` | one traversal `_⋯_`; a map covers term and type variables at once |
| typing | intrinsic, so type preservation is free | extrinsic `Γ ⊢ e ∶ t`, with dependent contexts `Ctx S` (`lookup` weakens) and typing kits `TKit` |

Our `Sub` also maps all sorts at once: the sort is the implicit `{A}`.
The difference for System F is that our terms are intrinsically typed,
and a type-indexed term family cannot share one scope with its own types.

## 3. What the language author proves by hand (System F)

Our System F has 11 term constructors and 5 type constructors. The paper's
has 8 constructors in one syntax and 6 typing rules.

| | ours, `intrinsic-subst` | paper, simplified supplement | paper, full framework (reflection) | experiment, our library (1c) |
|---|---|---|---|---|
| traversals written | `travᵗ` 5, `travᵀ` 11 (1 cast), `trav` 11: **27 clauses** | `_⋯_` 8 | 0 (`unquoteDecl D = derive Sort _⊢_ D`) | `trav` 8 |
| inductions on types | `fuseᵗ` 5, `sub-idᵗ` 5 | (types are terms) | (types are terms) | (types are terms) |
| inductions on terms | `fuseᵀ` 11 (`≅`), `idᵀ` 11 (`≅`), `commute` 11, `fuse` 11, `sub-id` 11: **55 clauses** | `⋯-id` 8, `fusion` 8 | 0 | `fuse` 8, `sub-id` 8 |
| helper lemmas | 10 heterogeneous congruences (`true-≅` … `∙-≅`), `travᵀ-conv`, `trav-conv`, `cong₃` | none | none | none |
| type preservation | free (intrinsic) | `_⊢⋯_`: 6 clauses, 2 `subst` | `_⊢⋯_`: 6 clauses, 2 `subst` | not done |
| total by hand | 7 inductions, 65 proof clauses + 27 definition clauses + 13 helpers; `proof/TermSubst.agda` is 263 lines, `proof/TypeSubst.agda` is 40 | 3 inductions, 22 clauses + 8 definition clauses | **1 induction, 6 clauses** | 2 inductions, 16 clauses + 8 definition clauses |

The paper reports the supplement's System F as 212 lines, of which 79
can be derived by the full framework.

For a fair comparison, note that the paper's `_⊢⋯_` is the work we avoid
by intrinsic typing. Our 55 term clauses buy terms that carry their types.
Most of the cost is the two-level split: `Commute` exists only because
there are two traversals, and `Fuseᵀ`/`Idᵀ` need `_≅_` only because
`travᵀ` changes the type index.

## 4. Casts and heterogeneous equality

For System F, the equation that matters is

    act θ (A [ B ]ᵗ) ≡ act (exts θ) A [ act θ B ]ᵗ          (our `act-[]`)
    t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ (ϕ ↑ s) ⋯ ⦅ x/t &/⋯ ϕ ⦆          (paper `dist-↑-⦅⦆-⋯`)

Both designs need it. The difference is where it appears.

- **Ours.** It is an index of the term (`_∙_ : … → Δ ∣ Γ ⊢ A [ B ]ᵗ`), so
  `travᵀ` casts the term (`convᵀ`). At a type binder, the context
  `⇑ᶜ Γ` changes too, so `⇑ρ` and `instᵛ` cast variables (`conv∋`).
  Because the results of two traversals have types that are only
  propositionally equal, the laws `Fuseᵀ` and `Idᵀ` are stated with `_≅_`.
- **Paper.** Terms are not indexed by types, so `_⋯_` never casts. The
  equation appears as `subst` on *typing derivations*, in two clauses of
  `_⊢⋯_` (`⊢λ` by `⋯-↑-wk`, `⊢∙` by `dist-↑-⦅⦆-⋯`) and in the library's
  `⊢↑` and `⊢⦅_⦆`. Every equation is between terms of the same scope and
  sort, so there is no `_≅_`. When the paper lists "heterogeneous equality
  between renamings and substitutions" as a contribution, it means
  comparing a renaming with a substitution pointwise (`~` across two kits,
  `⋯-ι-→` in `KitHomotopy`). It does not mean `_≅_` on terms.
- The full framework still uses `subst`, but only on scope equations: the
  `++-assoc` casts in `⋯-↑*-▷▷` and `MultiSub`, for lifting under several
  binders at once.

So the paper avoids our casts by giving up intrinsic typing. Nothing in it
removes the casts at `_∙_` or at type binders while terms stay
intrinsically typed. Section 2.2 of the paper says such a syntax is not
straightforward to construct.

## 5. Extensionality, `--safe`, and automation

| | `Subst` | paper supplement (`Simple/`) | full `kitty` |
|---|---|---|---|
| function extensionality | none; all map equalities are pointwise | `postulate ~-ext` in `Simple/Kits.agda` | README: "does not rely on" it. It proves that operations preserve `~` (`KitHomotopy.~-cong-⋯`, `MultiTraversal.⋯-↑`) |
| `--safe` | yes (`make` runs `agda --safe` and greps for postulates) | no (it has a postulate) | not declared in any file; I did not build it. `ReflectionLib/Standard/SyntaxCopy.agda` contains postulates; I did not check whether the derivation imports it |
| Agda / stdlib | 2.8.0.2 / 2.4 | tested on Agda 2.6.2–2.6.5, any stdlib | Agda 2.6.4–2.6.5, stdlib 2.0 |
| automation | none; each traversal and induction is written | none | reflection derives `_⋯_`, `⋯-id`, fusion and congruence. The user writes the syntax, the typing relation, and `_⊢⋯_` |

Two points of contact are worth noting.

- Paper footnote 2 says that avoiding funext costs "boilerplate": a
  `~`-congruence for every operation on maps. We avoid this boilerplate
  differently. `Fuse` is stated for any relation `R` that is closed under
  `exts`, and `trav-cong` is derived from `ren-trav` with `r = id`.
- The full framework's `MultiTraversal.⋯-↑` is a generalization of our
  `Fuse`. Take two *lists* of maps of any kits. If they agree on every
  variable under any number of lifts, then they agree on every term. That
  one induction gives fusion (`[ϕ₁, ϕ₂]` against `[ϕ₁ ·ₖ ϕ₂]`), identity
  (`[id]` against `[]`) and congruence (`[f]` against `[g]`). With it, our
  one-level language author would prove one induction instead of two
  (`fuse` and `sub-id`).

## 6. Recommendation

Each item says what to do, what it costs, and what changes in `Subst/`,
in `STLC/agda-subst`, and in `SystemF/agda/intrinsic-subst`.

1. **Document multi-sorted scopes for extrinsic languages (adopt; cheap).**
   Add the experiment of 1c as an example, for instance
   `Subst/examples/MultiSortedF.agda` checked by `Subst/Makefile`, and add
   a README paragraph: if a language is extrinsically typed and has
   several sorts of variables, then use `ctxScope Sort` with one
   traversal. Cost: about 95 lines and no change to the library. Clients:
   no change. If kinds or other `NoVar` sorts are ever needed, then `Kit`
   must index terms by a larger sort type than the variables'. That is a
   small change to `Kit.agda` and `proof/Kit.agda`, but every client
   signature would mention it, so do it only when a client needs it.

2. **Typing kits (adopt when an extrinsic polymorphic client uses
   `Subst`).** STLC already has the idea locally: the module of
   `typing_trav` in `proof/TypeSafety.agda` takes `_⊢K_⦂_`, `⊢vr`, `⊢wk`,
   `⊢tm`, and gives `typing_rename` and `typing_subst` from one induction.
   Moving that module into `Subst/` (say `Subst/Typing.agda`) saves STLC
   about 25 lines, so it is not worth doing for STLC alone. It becomes
   worth doing for a multi-sorted extrinsic System F. That needs the
   paper's dependent contexts, `Ctx S` with a weakening `lookup`, and its
   `TKit`/`⊢↑`/`⊢⦅_⦆`. The equations they need are already exported by
   `Subst.proof.Kit`:

   | paper | ours |
   |---|---|
   | `⋯-↑-wk : t ⋯ ϕ ⋯ weaken s ≡ t ⋯ weaken s ⋯ (ϕ ↑ s)` | `Laws.exts-ren` (symmetric form) |
   | `wk-cancels-⦅⦆-⋯ : t ⋯ weaken s ⋯ ⦅ x/t ⦆ ≡ t` | `⇑-[]` (for the term kit) |
   | `dist-↑-⦅⦆-⋯` | `trav-[]` |

   The cost is about 120–150 lines of library. The typing part of the
   paper's simplified framework is about 130 lines. Clients: STLC
   optionally switches to it; `intrinsic-subst` does not change.

3. **Multi-sorted syntax for intrinsic System F (do not adopt).** Section 4
   explains why it does not apply. `Poly`, its two traversals, and its
   heterogeneous laws stay. `intrinsic-subst` does not change.

4. **Reflection (do not adopt).** It would tie `Subst` to a reflection
   library and to particular Agda versions. It derives only the
   scoped-untyped part, which for a one-level language is two short
   inductions. It also cannot derive `Poly`'s laws, which involve casts and
   `_≅_`. Our audit rule (read the top level, trust `--safe` for `proof/`)
   is easier to keep without it.

5. **`CKit` and instance-argument kits (do not adopt).** Our `Fuse`, with
   three kits and a relation `R`, already covers all four compositions of
   renaming and substitution. `trav-trav` with `Laws` is the counterpart
   of the paper's `fusion` for any `CKit`. Instance arguments would hide
   which kit a lemma uses, at the call site of a theorem.

6. **List-of-maps fusion, after `kitty`'s `⋯-↑` (maybe later).** It would
   merge `Fuse` and `SubId` into one induction, saving one induction per
   language (6 clauses for STLC, 5 for System F types). The library would
   need lists of maps of different kits, and lifting by several binders.
   `kitty` needed `++-assoc` casts for that lifting. It does not help
   `Poly`'s `Commute`, which mixes two traversals.

Under this recommendation:

- `Subst/`: an example file, a README paragraph, and later a typing module.
- `STLC/agda-subst`: no change now. If item 2 is done, then switch to the
  library's typing kit.
- `SystemF/agda/intrinsic-subst`: no change.

**Where the paper's idea would pay off most** is outside the two current
clients. `SystemF/agda/extrinsic` defines three separate substitutions,
in `TypeSubst.agda` (241 lines), `TermSubst.agda` (343) and
`TypeTermSubst.agda` (548). This is the "triplication" that the paper's
introduction describes. If that development moved to multi-sorted syntax
on `Subst`, then those files would shrink to one traversal and two
inductions, plus the typing kit of item 2. The cost is large: term
variable indices would also count type binders, so every downstream proof
(`Preservation`, `LogicalRelation`, `Parametricity`, `FreeTheorems`) would
change. I have not read those files. Treat this as a separate decision,
not part of this comparison.

## Appendix: `MultiSortedF.agda`

Checked with `agda --safe -i /Users/jsiek/AI-for-pl -i <dir> MultiSortedF.agda`
(Agda 2.8.0.2, stdlib 2.4), against `Subst/` as of 2026-11-11.

```agda
module MultiSortedF where

-- Experiment: the multi-sorted syntax of Saffrich (ITP 2024) for System F,
-- written against the existing one-level library Subst.Kit, with the
-- scope structure `ctxScope Sort` (scopes are lists of sorts).

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Subst.Scope using (ctxScope; Ctx; ∅; _,_; _∋_; Z; S_)

data Sort : Set where
  𝕖 𝕥 : Sort

infix  4 _⊢_
infixr 7 _⇒_
infixl 7 _·_ _∙_
infix  9 `_

data _⊢_ (S : Ctx Sort) : Sort → Set where
  `_   : ∀ {s} → S ∋ s → S ⊢ s
  ƛ_˙_ : S ⊢ 𝕥 → S , 𝕖 ⊢ 𝕖 → S ⊢ 𝕖
  _·_  : S ⊢ 𝕖 → S ⊢ 𝕖 → S ⊢ 𝕖
  Λ_   : S , 𝕥 ⊢ 𝕖 → S ⊢ 𝕖
  _∙_  : S ⊢ 𝕖 → S ⊢ 𝕥 → S ⊢ 𝕖
  `Nat : S ⊢ 𝕥
  _⇒_  : S ⊢ 𝕥 → S ⊢ 𝕥 → S ⊢ 𝕥
  `∀_  : S , 𝕥 ⊢ 𝕥 → S ⊢ 𝕥

open import Subst.Kit (ctxScope Sort) _⊢_ `_ public

-- One traversal for expressions and types, and for both sorts of variable.
trav : (𝒦 : Kit) → ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Γ ⊢ A → Δ ⊢ A
trav 𝒦 σ (` x) = Kit.tm 𝒦 (σ x)
trav 𝒦 σ (ƛ A ˙ N) = ƛ trav 𝒦 σ A ˙ trav 𝒦 (exts 𝒦 σ) N
trav 𝒦 σ (L · M) = trav 𝒦 σ L · trav 𝒦 σ M
trav 𝒦 σ (Λ N) = Λ trav 𝒦 (exts 𝒦 σ) N
trav 𝒦 σ (M ∙ B) = trav 𝒦 σ M ∙ trav 𝒦 σ B
trav 𝒦 σ `Nat = `Nat
trav 𝒦 σ (A ⇒ B) = trav 𝒦 σ A ⇒ trav 𝒦 σ B
trav 𝒦 σ (`∀ A) = `∀ trav 𝒦 (exts 𝒦 σ) A

open Substitution trav public

open import Subst.proof.Kit (ctxScope Sort) _⊢_ `_ using (module Traversal)
open Traversal trav (λ _ _ _ → refl) using (Fuse; SubId; sub-id-exts; module Lemmas)

fuse : Fuse
fuse 𝒦₁ 𝒦₂ 𝒦₃ R R-exts R-var = go
  where
  go : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
    → R σ₁ σ₂ σ₃ → ∀ {A} (M : Γ ⊢ A)
    → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
  go r (` x) = R-var r x
  go r (ƛ A ˙ N) = cong₂ ƛ_˙_ (go r A) (go (R-exts r) N)
  go r (L · M) = cong₂ _·_ (go r L) (go r M)
  go r (Λ N) = cong Λ_ (go (R-exts r) N)
  go r (M ∙ B) = cong₂ _∙_ (go r M) (go r B)
  go r `Nat = refl
  go r (A ⇒ B) = cong₂ _⇒_ (go r A) (go r B)
  go r (`∀ A) = cong `∀_ (go (R-exts r) A)

sub-id : SubId
sub-id h (` x) = h x
sub-id h (ƛ A ˙ N) = cong₂ ƛ_˙_ (sub-id h A) (sub-id (sub-id-exts h) N)
sub-id h (L · M) = cong₂ _·_ (sub-id h L) (sub-id h M)
sub-id h (Λ N) = cong Λ_ (sub-id (sub-id-exts h) N)
sub-id h (M ∙ B) = cong₂ _∙_ (sub-id h M) (sub-id h B)
sub-id h `Nat = refl
sub-id h (A ⇒ B) = cong₂ _⇒_ (sub-id h A) (sub-id h B)
sub-id h (`∀ A) = cong `∀_ (sub-id (sub-id-exts h) A)

open Lemmas fuse sub-id public

-- The running example: Λα. λ(f : ∀β. β ⇒ β). f ∙ α
-- In the body, scope ∅ , 𝕥 , 𝕖: `Z` is f (sort 𝕖), `S Z` is α (sort 𝕥).
body : ∅ , 𝕥 ⊢ 𝕖
body = ƛ `∀ (` Z ⇒ ` Z) ˙ (` Z ∙ ` (S Z))

poly : ∅ ⊢ 𝕖
poly = Λ body

-- β for type application is the same single substitution `_[_]` as β for
-- term application, at the sort 𝕥, and it computes with no cast.
inst : body [ `Nat ] ≡ ƛ `∀ (` Z ⇒ ` Z) ˙ (` Z ∙ `Nat)
inst = refl

-- The substitution lemma, used at both sorts: one lemma, no casts.
sub-[]ᵗ : ∀ {Γ Δ} (σ : Sub tmK Γ Δ) (N : Γ , 𝕥 ⊢ 𝕖) (B : Γ ⊢ 𝕥)
  → sub σ (N [ B ]) ≡ sub (exts tmK σ) N [ sub σ B ]
sub-[]ᵗ = sub-[]

sub-[]ᵉ : ∀ {Γ Δ} (σ : Sub tmK Γ Δ) (N : Γ , 𝕖 ⊢ 𝕖) (M : Γ ⊢ 𝕖)
  → sub σ (N [ M ]) ≡ sub (exts tmK σ) N [ sub σ M ]
sub-[]ᵉ = sub-[]
```
