# Strong System F vs. Syntactic Type Abstraction

An in-depth comparison of the FINAL Strong System F design (`Design.md`,
`notes/DECISIONS.md`, `Examples.agda`, `proof/`) with the treatment of
**polymorphism** in

> Dan Grossman, Greg Morrisett and Steve Zdancewic, *Syntactic Type
> Abstraction*, TOPLAS 22(6), November 2000, pp. 1037–1080.
> In tree as `p1037-grossman.pdf` (printed page = PDF page + 1036).
> The ICFP'99 precursor is `p197-zdancewic.pdf`.

Below, **STA** means that paper.  Page numbers are printed pages.

**What this note is not.**  `notes/Zdancewic-embeddings.md` transcribes the
ICFP'99 calculus and `notes/SyntacticTypeAbstraction.md` transcribes what
the journal version adds.  Both are **v1-era**: they were written to
adjudicate v1 choices (Merge, `Drop∅`, depth-1 values, the conceal
licence, the ambient dual `dualᴳ`) and every one of those was later
refuted or deleted.  This note does not repeat their transcriptions and
does not reuse their verdicts.  It answers one question Jeremy asked:

> add an in-depth comparison … Especially compare our notion of
> TIGHTNESS (which type variables are in scope), to see if there is
> anything analogous in that paper.

The short answer is at the end of §2 and in §11.  The one-line version:
**STA has no notion of a type variable being out of scope.**  It has
`Θ`, a set of "type variables currently in scope" (p.1072), but the
paper says in the same paragraph that "Θ is unused by the new version of
the old rules", and no rule anywhere has a premise of the form
`FTV(τ) ⊆ Θ`.  Their type abstraction is entirely by **opacity** — a
variable an agent cannot *refine* — never by **unnameability**.  Ours is
both, and the second is what "tight" means.

The structural reason is the one §8 ends on.  STA's type variables are
**global allocated names** in a monotone knowledge base `{Δ}` —
freshness is meta-level α-conversion, and `{Δ}` is only ever extended
(Def. 5.4, p.1073) — so there is no *position* at which a name stops
being nameable and "out of scope" has nothing to mean.  Ours are
lexically scoped binders in a type context.  That is the `D33` fork
(`notes/DesignSpace.md`, edge `D33→D34`), and it is what makes
tightness vacuous for them; it is **not** bought by their evaluation
order.


## 0. The two vocabularies, side by side

| STA | Strong System F |
|-----|-----------------|
| agent / principal / colour `i` (p.1039 fn.1) | interior / exterior (two sides of one boundary) |
| embedding `⌈eⱼ⌉^τ_ℓ` | boundary `M ⟪ Θ , c ⟫` |
| agent list `ℓ`, appended by `[8]` | the tower of boundaries; never merged (law 6) |
| annotation `τ` (one type per embedding) | conversion `c`, leaf by leaf |
| `δᵢ : TyVar ⇀ Ty`, per agent, **global** | `bind A` entry in the type context `Δ` |
| `Δᵢ`, the total extension of `δᵢ` | binder lookup `Δ ∋ X := A` |
| `{Δ} = {Δ₁,…,Δₙ}`, ambient, monotone | the exterior `Δ`, fixed along `Δ ⊢ M -→ M′` |
| `t ∉ Dom(δᵢ)` — `t` is *opaque* to `i` | `masked E` — the slot is *unnameable* |
| — (no counterpart) | `lock X` / `unlock X`, rendered `↓X` / `↥X` |
| — (no counterpart) | `interior Θ Δ`, `convCtx Θ Δ` |
| `⊢ τ ≲_ℓ τ′` (Fig. 13, p.1051) | `Δ ⊢ c ∶ A ⇝ B` (`Conversion.agda`) |
| oblivious (Def. 3.10, p.1054) | `Nameable` / `wf-var` (`Ctx.agda`) |

Ours in Jeremy's words: a boundary `M ⟪ Θ , c ⟫` carries a **context
morphism** `Θ = morph binds changes` with **parallel binds** `↑X:=A` and
**sequential changes** `↓X` (lock) and `↥X` (unlock), and a
**conversion** `c` whose **source type** is the interior type and whose
**target type** is the exterior type read inside.  The morphism induces
`interior Θ Δ` (where `M` is typed) and `convCtx Θ Δ` (where `c` is
typed); `Δ` itself is the **exterior**.  A `bind` entry names the
variable's **binder**, which stores its **representation** once.


## 1. STA's calculus, in the shape our vocabulary makes visible

Multiagent syntax (Fig. 9, p.1046), transcribed:

    (agents) i, j ∈ {1,…,n}
    (lists)  ℓ    ::= i | i ℓ
    (types)  τ    ::= t | b | τ → τ′
    (i-terms) eᵢ  ::= xᵢ | bᵢ | λxᵢ:τ. eᵢ | eᵢ eᵢ′
                    | fix fᵢ(xᵢ:τ). eᵢ | ⌈eⱼ⌉^τ_ℓ
    (i-primvals) v̂ᵢ ::= bᵢ | λxᵢ:τ. eᵢ
    (i-values)   vᵢ ::= v̂ᵢ | ⌈v̂ⱼ⌉^t_ℓ        (t ∉ Dom(δᵢ))

Knowledge (Def. 3.1, p.1047).  A set `{δ₁,…,δₙ}` of finite partial maps
from type variables to types is **compatible** if

* for every `i, j`, if `t ∈ Dom(δᵢ) ∩ Dom(δⱼ)` then `δᵢ(t) = δⱼ(t)`;
* the type variables can be totally ordered so that for every agent `i`
  and variable `t`, all variables in `δᵢ(t)` precede `t`.

Each `δᵢ` extends to a total `Δᵢ` with `Δᵢ(t) = t` when `t ∉ Dom(δᵢ)`,
and `Δ̄ᵢ` is its fixpoint — "the most concrete view of `τ` that agent `i`
is able to determine from its knowledge" (p.1047).

Typing (Fig. 12, p.1051).  The only nonstandard rule is

    Γ ⊢ eⱼ : τ′     ⊢ τ′ ≲_{jℓi} τ
    ───────────────────────────────  [embed]
    Γ ⊢ ⌈eⱼ⌉^τ_{jℓ} : Δ̄ᵢ(τ)

with the chain relation (Fig. 13, p.1051)

    Δ̄ᵢ(τ) = Δ̄ᵢ(τ′)                ⊢ τ ≲_ℓ τ″   ⊢ τ″ ≲_ℓ′ τ′
    ────────────────── [eq]        ───────────────────────── [trans]
      ⊢ τ ≲_i τ′                        ⊢ τ ≲_{ℓℓ′} τ′

Reduction (Fig. 10, p.1049), the four rules that are about embeddings:

    [6] ⌈bⱼ⌉^b_ℓ ↦→ bᵢ
    [7] ⌈v̂ⱼ⌉^τ_ℓ ↦→ ⌈v̂ⱼ⌉^{Δ̄ᵢ(τ)}_ℓ                    (τ ≠ Δ̄ᵢ(τ))
    [8] ⌈⌈v̂ⱼ⌉^u_ℓ⌉^τ_{kℓ′} ↦→ ⌈v̂ⱼ⌉^τ_{ℓkℓ′}
                                    (u ∉ Dom(δₖ), τ = Δ̄ᵢ(τ))
    [9] ⌈λxⱼ:τ. eⱼ⌉^{τ′→τ″}_{jℓ}
          ↦→ λxᵢ:τ′. ⌈{⌈xᵢ⌉^τ_{i rev(ℓ)} / xⱼ} eⱼ⌉^{τ″}_{jℓ}
                              (xᵢ fresh, τ′→τ″ = Δ̄ᵢ(τ′→τ″))

Three observations that set up everything below.

1. **An embedding carries no context.**  `⌈eⱼ⌉^τ_ℓ` is a term former
   with one type annotation and one agent list.  There is nothing in it
   that says which type variables `eⱼ` may mention, because in STA the
   answer is always "all of them".
2. **`[9]` is our `Peel`, but eager.**  It fires on the embedding alone,
   not on an application; it has to, because `⌈v̂ⱼ⌉^{τ′→τ″}_ℓ` is not an
   `i`-value (Fig. 9 admits an embedding as a value only at a type
   *variable* `t` with `t ∉ Dom(δᵢ)`).  Ours is by need: `s ↦ t` is
   `Inert`, the boundary is a value, and `Peel` fires at the
   application.  Both rules do the same bookkeeping — the domain
   component crosses inward under the reversed frame.  Theirs reverses
   the *agent list*, `rev(ℓ)`; ours reverses the *morphism*, `dual Θ`.
3. **`[9]`'s side condition `τ′→τ″ = Δ̄ᵢ(τ′→τ″)`** is exactly our
   determinism discipline (law 5): it exists "to preserve the
   determinism of the semantics" (p.1049), not for soundness — the
   paper says so of `[7]` in the same breath (p.1048).


## 2. (1) Out of scope, or merely opaque?

**STA: opaque only.**  Types are `τ ::= t | b | τ → τ′` over one global
namespace of type variables.  There is no type well-formedness
judgement.  Every agent may *name* every `t`; what differs is whether
`t ∈ Dom(δᵢ)`, i.e. whether `i` can *refine* it.  Abstraction is
Def. 3.10 (p.1054):

> A set of agents, `S`, is **oblivious** to type `t` if for all `i ∈ S`,
> `t ∉ Dom(δᵢ)`.

Obliviousness is *absence from a partial map*.  It is never absence from
a context, because there is no context.

**Ours: both.**  `Ctx.agda` (`Design.md` §3):

    E ::= abst | bind A | masked E
    Δ ::= · | E , Δ

    Nameable abst        Nameable (bind A)     -- and never `masked E`
    Δ ∋tv X = ∃ E. (Δ ∋e X , E) × Nameable E
    wf-var : Δ ∋tv X → Δ ⊢ᵗ ` X

`Ctx.agda`'s own comment states the law: *"A slot may be NAMED iff its
entry is not masked.  This is the whole of the tightness discipline:
`masked` is unnameable in types and in terms."*  So we have two
independent axes where STA has one:

| | may *name* `X` | may *see* `X`'s representation |
|-|----------------|-------------------------------|
| STA | always | iff `X ∈ Dom(δᵢ)` |
| ours | iff `Δ ∋tv X` | iff `Δ ∋ X := A` |

A `lock X` moves a slot down the first axis without touching the second:
the entry is retained, so `unlock X` can put it back, and the
representation is still stored at the binder for the *conversion* to
cite in `convCtx Θ Δ`.  STA has no move of that kind.

**The one nameability restriction STA does have**, and it points the
other way.  In the two-agent calculus (Fig. 7, p.1043) the host-function
rule is

    Γ[xₕ:τ′] ⊢ H : τ
    ─────────────────────────  [Hfn]        (t ∉ τ′)
    Γ ⊢ λxₕ:τ′. H : τ′ → τ

so the **host** — the agent that *knows* `t = τₕ` — may not write `t` in
a function-argument annotation.  The paper states the restriction in
prose as "`t` is not allowed to appear in the annotation for the
argument to a function" (p.1043), which is what fixes it to the domain.

The paper's justification is
presentational: "Because the host knows that `t = τₕ`, this restriction
does not limit expressiveness.  The convenient effect of this side
condition and rule `[CinH]` is that types of host terms never contain
`t`" (p.1043).  It is a convenience for the *knowing* side, not
abstraction for the *ignorant* side, and it does not survive into the
multiagent calculus.  It is the closest thing in the paper to `wf-var`
refusing a masked slot, and it is not close.

**And `Θ`.**  §5.2 adds a third judgement parameter:

> We also need to track the lexical scoping of `Λ`-bound type variables.
> We do so by adding a set, `Θ`, of type variables currently in scope.
> The new form of typing judgments is therefore `Θ; {Δ}; Γ ⊢ e : τ`
> (p.1072).

`Θ` is used in exactly one place (Fig. 20, p.1071):

    Θ,α; {Δ}; Γ ⊢ eᵢ : τ
    ─────────────────────────  [∀intro]    (α ∉ Θ ∪ Dom{Δ})
    Θ; {Δ}; Γ ⊢ Λα. eᵢ : ∀α.τ

— as a **freshness** side condition, never as a visibility premise.  The
paper is explicit: "(Θ is unused by the new version of the old rules.)"
(p.1072).  `[∀elim]` does not require `FTV(τ′) ⊆ Θ`:

    Θ; {Δ}; Γ ⊢ eᵢ : ∀α.τ     Δᵢ(τ′) = τ′
    ───────────────────────────────────────  [∀elim]  (α ∉ Dom{Δ})
    Θ; {Δ}; Γ ⊢ eᵢ[τ′] : {τ′/α}τ

So `Θ` is write-only.  There is no `Θ ⊢ τ` judgement to refuse anything.
Compare `Design.md` §4.1, where `wf-var` is the *only* interesting
clause of `Δ ⊢ᵗ A` and is the premise every tightness refutation lands
on.

The paper knows it is leaning on α-conversion rather than on scope, and
says so in the conclusions (p.1078):

> There is also a similarity between our use (in Section 5.2) of global
> alpha conversion and the restriction operator, `ν`, of the pi calculus
> to generate a "fresh" type variable at runtime.


## 3. (2) What an embedding tracks about the variables inside it

Nothing.  Systematically, against our three devices:

**Masks.**  No counterpart.  `[embed]` (p.1051) relates the inside type
`τ′` to the annotation `τ` by the chain `≲_{jℓi}` and says nothing about
which variables `eⱼ` may write.  Our `env` (`Terms.agda`) says both:

    env : Δ ⊢ᵐ Θ
        → interior Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
        → convCtx Θ Δ ⊢ c ∶ Bᵢ ⇝ shiftBy (numBinds Θ) Bₑ
        → Δ ⊢ᵗ Bₑ
          ------------------------------------
        → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ

Premise 2 is where the masks bite: if `Θ` locks `X`, then `Bᵢ` — and
every type inside `M` — cannot name `X`.  STA's `[embed]` has no premise
that could be weakened this way, because it types `eⱼ` at the same `Γ`
and the same global type namespace as its context.

**`unlock` (re-exposure when a value crosses back).**  No counterpart,
and there cannot be one: a variable is never hidden, so nothing needs
re-exposing.  The nearest structural relative is `[9]`'s `rev(ℓ)`, which
re-orders the *agent list* on the argument's embedding.  The paper's
reason for reversing is worth quoting next to our `dualScope`
(p.1049–1050):

> Because the "inside type" and "outside type" have reversed roles, the
> agent list must be in reverse order.  Intuitively, the agents that
> successively provided the function-argument type to `i` must undo
> their work in the body of the function.

That is exactly the argument in `CtxMorph.agda` for reversing
`dualScope` — *"an inverse runs backwards"* — except that ours is
reversing a list of **frame changes** and theirs a list of **agents**:

    dualScope n (unlock X ∷ S) = dualScope n S ++ (lock   (n + X) ∷ [])
    dualScope n (lock   X ∷ S) = dualScope n S ++ (unlock (n + X) ∷ [])
    dual Θ = morph [] (hideBinds (numBinds Θ) ++ dualScope (numBinds Θ)
                                                           (changes Θ))

**Bind block (fresh binders introduced by a boundary).**  No
counterpart.  Their `[9]` and `[8]` introduce no type variables at all.
The only rule that introduces knowledge is `[∀1]`, which extends the
*global* `δᵢ` rather than a boundary (§4).  Our `hideBinds` half — a
boundary's own binders are masked for the crossing argument — has
nothing to correspond to.


## 4. (3) Polymorphism: their `[∀1]`/`[∀2]` against our `TyBeta`/`TyPeelR`

STA, Fig. 20 (p.1071), transcribed in full:

    (types)      τ  ::= … | ∀α.τ
    (i-terms)    eᵢ ::= … | Λα. eᵢ | eᵢ[τ]
    (i-primvals) v̂ᵢ ::= … | Λα. eᵢ
                                     Dom{Δ} = ⋃ᵢ Dom(δᵢ)

    [∀1] ⟨{Δ}, (Λα. eᵢ)[τ]⟩ ↦→ ⟨{Δ} ⊎ᵢ {α = τ}, {τ/α}ᵢ eᵢ⟩
    [∀2] ⟨{Δ}, ⌈Λα. eⱼ⌉^{∀α.τ}_ℓ⟩ ↦→ ⟨{Δ}, Λα. ⌈eⱼ⌉^τ_ℓ⟩

with `{τ/α}ᵢ` "a special substitution operator … to perform the
substitution of `τ` for `α` only in terms colored `i`, including
`i`-subterms of any `j`-colored subexpressions" (p.1072).

Ours (`Reduction.agda`):

    TyBeta : Value N
      → Δ ⊢ (Λ N) ·[ B , A ] -→ N ⟪ morph (A ∷ []) [] , reveal 0 B ⟫

    TyPeelR : Value V
      → (abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

Named: `(ΛX. N) [B, A] → N ⟪ ↑X:=A , reveal X B ⟫`, and
`(V ⟪ Θ , ∀X. s ⟫) [B, A] → (V [Bᵢ, X]) ⟪ ↑X:=A , Θ , instReveal X s ⟫`.

**Where the instantiation event is recorded.**  This is the deepest
difference and it explains all the others.

* STA records it in the **ambient knowledge base**: `{Δ} ⊎ᵢ {α = τ}`.
  The registry is global, flat, keyed by agent, and **monotone** —
  Def. 5.4 (p.1073) defines `{Δ} ≤ {Δ′}` as one such extension and
  `≤*` as its closure, and Lemma 5.5 must carry the extra conclusion
  "`{Δ′}` is compatible and **refines** `{Δ}`".
* We record it in the **term**, as a `bind` entry on a boundary.  The
  ambient `Δ` never changes: our relation is `Δ ⊢ M -→ M′` with the
  *same* `Δ` on both sides (`Reduction.agda`), and `preservation` is

      preservation : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A

  with no monotonicity clause, because there is no ambient thing to be
  monotone.  Our `Δ` is indexed only so that `ξ-Λ` can push `abst` and
  `ξ-⟪⟫` can push `interior Θ Δ`.

So: **STA's `⟨{Δ}, e⟩` configuration is a store, and our type context is
a lexical scope.**  `notes/DesignSpace.md` records that the global-store
realization was considered and *not* taken (edge `D33→D34`: "a global
Σ-store, **NOT taken** — lexical scope is needed for lock blocking"),
and `notes/DesignPoints.md` `D33` has Jeremy's ruling in full: "once
type variables are in a global store, it becomes more difficult to talk
about their lexical scope relationships, which we are currently using in
conceal blocking" (see also `Design.md` §9 and `notes/RedesignAdvice.md`
Q1, which sets out realizations (i) store-passing and (ii)
owner-syntactic).  This note supplies the missing citation for that
edge: STA is the design that took (i), and §5.2 is what it looks like.
§8 draws the consequence — the fork, not the evaluation order, is why
tightness has nothing to say there.

**The type argument.**  Jeremy's lesson from the pre-boundary
counterexample is *never push a type argument into a concealed body*
(`Design.md` §1, `notes/DesignPoints.md` D05).  STA's `[∀1]` **does**
push — but only into `i`-coloured subterms.  The `j`-coloured interior
of an embedding is untouched, and `δⱼ` is not extended: "Most
importantly, no other agent knows `α`" (p.1072).  So on the
configuration that matters — a `Λ` whose body is an embedding —

    (Λα. ⌈eⱼ⌉^τ_ℓ)[τ′]  ↦→  ⟨{Δ} ⊎ᵢ {α = τ′}, ⌈eⱼ⌉^{{τ′/α}τ}_ℓ⟩

the interior `eⱼ` keeps running at the abstract name `α` while the
exterior learns `α = τ′`.  That is precisely `TyBeta`.  The colour
index does structurally what our boundary does syntactically.

Two consequences, one in each direction.

* **In STA's favour**: their push is safe wherever the colouring is
  right, and it needs no boundary at the type application at all.
* **Against it**: the abstraction is only as strong as the colouring the
  programmer (or the translation of §5.3) chose.  With the naive
  one-colour translation, "the operational semantics degenerates to
  those of the regular polymorphic lambda calculus; in particular, type
  application still substitutes a type for a type variable" and "our
  system will provide no more opportunity to use syntactic proofs of
  type abstraction than before" (p.1074).  Ours is unconditional:
  `TyBeta` installs a boundary at *every* type application, and
  `Design.md` §1 opens on exactly that point — "**Strong** System F
  enforces it at *run time*".

We also cannot adopt `{τ/α}ᵢ`: it rewrites type annotations inside
terms, which design law 3 (*no term type-shifts*) forbids outright.

**The mint site.**  Their boundary is minted at the `Λ`; ours at the
type application.  Fig. 22's `[Ttypeabs]` (p.1075) spawns a fresh agent
for the body of every type abstraction:

    C[[Γ ⊢ e : τ]]ⱼ γ = eⱼ
    ─────────────────────────────────────────────  [Ttypeabs] (j fresh)
    C[[Γ ⊢ Λα. e : ∀α.τ]]ᵢ γ = Λα. ⌈eⱼ⌉^τ_j

    C[[Γ ⊢ e : ∀α.τ]]ᵢ γ = eᵢ
    ─────────────────────────────────────────  [Ttypeapp]
    C[[Γ ⊢ (e[τ′]) : {τ′/α}τ]]ᵢ γ = (eᵢ[τ′])

Note `[Ttypeapp]`: **no boundary at the type application**.  The paper
therefore needs a source-to-source translation to get abstraction, and
Lemma 5.7 (p.1075) has to set `Θ = FTV(Γ)` and `{Δ} = {Δₖ | δₖ = ∅}` by
hand.  We need neither, because `TyBeta` is a reduction rule.

**`[∀2]` is where a boundary drifts under a binder.**  It is the only
STA rule that moves a boundary under a `Λ`, and it is the structural
analogue of our `↓X` coming to sit under a later `ΛY`.  Its preservation
case (p.1073) is discharged by α-freshness alone — the side conditions
give `α ∉ Dom{Δ}`, hence `Δ̄ᵢ(∀α.τ) = ∀α.Δ̄ᵢ(τ)`, and Lemma 5.3 (∀ Type
Relations) splits the chain.  Nothing about scope is checked, because
nothing about scope is tracked.  §8 runs the program.

**A note on where STA *does* impose a scope-like condition.**  For
recursive types (§5.1) the paper writes: "To avoid problems with
capture, we prohibit free occurrences of `α` in the range of `δᵢ`"
(p.1069) — a restriction on what the knowledge base may *name*.  It is
not an oversight that §5.2 imposes no such restriction on `∀`-bound
variables.  §5.1's `μ`-bound variables are a **separate syntactic
class**: "because the `μ`-bound type variables are syntactically
distinct from the abstraction type variables, it makes no sense for `α`
to be in the domain of `δᵢ`" (p.1069).  §5.2 by contrast has "only one
form of type variable" (p.1071), and its `∀`-bound variables are
exactly the ones the registry exists to define — so there the freshness
discipline is global α-conversion **by design**, and the two sections
are consistent.  That design choice is what §8 turns on.


## 5. (4) Merge `[8]`, the three-agent counterexample, and towers

STA's `[8]` merges a nested embedding into one, appending the lists.
The paper's justification for having it at all (p.1048):

> Because an embedding is not an `i`-primval, a nested embedding (for
> example `⌈⌈λxⱼ:τ. xⱼ⌉^t_j⌉^s_i`) is never an `i`-value.  We could have
> made such terms values, but the result would significantly complicate
> the dynamic semantics: if our example nested embedding were passed to
> an agent that was able to refine `s` to an arrow type, then we would
> need to cross two embedding boundaries to find the function that the
> agent expects.

And the counterexample that forces the *list* (p.1048), transcribed:

> consider three agents, `i`, `j`, and `k`, such that `δᵢ(t) = int`,
> `δⱼ(s) = t`, and `δₖ = ∅`.  Then collapsing the `k`-term
> `⌈⌈3ᵢ⌉^t_i⌉^s_j` to either `⌈3ᵢ⌉^s_i` or `⌈3ⱼ⌉^s_j` violates the
> type-abstraction properties because neither `i` nor `j` knows that `s`
> abstracts an `int`. … If we use sets of agents instead of (ordered)
> lists, the reasonable rules become too permissive because we lose the
> information that agent `i` must have exported the integer at type `t`
> before `j` could export it at type `s`.

The right answer is `⌈3ᵢ⌉^s_{ij}`: the merged embedding is sound only
because the ordered list `ij` **is** the flattened tower.

Ours (`Design.md` §8, law 6):

> **Towers, not merges.**  Boundaries pile up; they are never merged.
> … Instead, an inert `↦` or `∀` conversion is **eliminated at its use**
> (`Peel`, `TyPeelR`), and a transparent layer is dissolved by pushing
> the active conversion inward (`IdPush`) until it meets its seal
> (`CancelR`) or a numeral (`Drop$`).  The towers stay bounded because
> every such step moves the active conversion strictly inward.

So we made the choice the paper explicitly rejected, and we answer its
objection with the two rules it did not have.  The "cross two boundaries
to find the function" worry costs us exactly one canonical-forms lemma:
`canon-var` says a value at a variable type is a `seal`- or
`id (` Y)`-converted boundary, so the two-layer case is one two-way
split (`Design.md` §7, `progress`).

The deeper point is that **both designs found the same fact by different
routes: the accumulated crossing history must be an ordered list, and
forgetting the order is unsound.**  Theirs is a three-agent knowledge
counterexample; ours is a frame counterexample in `proof/MoveScope` §4b,
where moving only the *locks* out of `Θ₂` past a same-slot `unlock`
corrupts the value's frame:

    Θ✗ = morph [] (unlock 0 ∷ lock 0 ∷ [])   over   Δ✗ = bind ℕ ∷ []
    interior Θ✗ Δ✗ ≡ bind ℕ ∷ []
    lock-only contractum's interior ≡ masked (bind ℕ) ∷ []   -- corrupted

Their answer is `rev(ℓ)` and list append; ours is the scope move

    Θ₁ ⋉ Θ₂ = morph (binds Θ₁)
                    (changes Θ₁ ++ shiftScope (numBinds Θ₂) (changes Θ₂))
    rewind Θ = morph (binds Θ) (dualScope 0 (changes Θ) ++ changes Θ)

with the frame preserved on the nose,
`interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ≡ interior Θ₁ (interior Θ₂ Δ)`
given `Δ ⊢ᵐ Θ₂` (`proof/MoveScope.interior-⋉-rewind`).

Our `CancelR` and `IdPush` are not merges.  Both keep **both** frames:

    CancelR : Value V → convCtx Θ₂ Δ ∋ Y := A
      → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
          -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId (shiftBy (numBinds Θ₁) A) ⟫)
               ⟪ rewind Θ₂ , mkId A ⟫

    IdPush : Value V → convCtx Θ₂ Δ ∋ Y := A
      → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
          -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal X ⟫) ⟪ rewind Θ₂ , mkId A ⟫

Nothing is stripped, so the STA worry about "naively stripping away
embeddings [losing] information about which agents could have
contributed information about the type of a term" (p.1049) cannot arise
for us at all.  §9 runs their counterexample on these rules.


## 6. (5) The `Value` judgement

STA's is **dynamic**, and the paper flags it (the sentence starts at the
foot of p.1073; the definition is on **p.1074**):

> Because the `{Δ}` context changes during evaluation, and the
> definition of when `⌈v̂ⱼ⌉^t_{jℓ}` is an `i`-value depends on whether
> `Δ̄ᵢ(t) = t`, the notion of value is also dynamic.  We write
> `{Δ} ⊢ eᵢ : Value` when either `eᵢ` is an `i`-primval or
> `eᵢ = ⌈v̂ⱼ⌉^t_ℓ` and `t ∉ Dom{Δ}`.

**The condition must be read per observing agent**, i.e. the rule is

    {Δ} ⊢ eᵢ : Value   iff   eᵢ is an i-primval, or
                             eᵢ = ⌈v̂ⱼ⌉^t_ℓ  and  t ∉ Dom(δᵢ)

equivalently `Δ̄ᵢ(t) = t` — which is what the same sentence's prose says
and what Fig. 9's `i`-value grammar says (`t ∉ Dom(δᵢ)`, p.1046, §1).
`Dom{Δ}` as printed is the **union** `⋃ᵢ Dom(δᵢ)` (§4), and the union
form cannot be meant, because it makes Lemma 5.6 (Progress) false: once
`[∀1]` has fired for agent `1`, `α ∈ Dom{Δ}` while `α ∉ Dom(δ₂)`, so a
`2`-term `⌈v̂ⱼ⌉^α_ℓ` would be neither a value nor a redex — `[6]` wants
a base type, `[7]` wants `α ≠ Δ̄₂(α)`, `[8]` wants a nested embedding,
`[9]` wants an arrow, and none applies.  The union would strand agent
`2`'s value on knowledge only agent `1` has.  (The quote is faithful to
the page; the per-agent reading is mine — §12.)

So value-hood is a *knowledge-relative* predicate — relative to the
observer's `δᵢ` inside the ambient `{Δ}` — and Progress (Lemma 5.6,
p.1074) is stated against it.  Ours is syntactic (`Terms.agda`):

    V-$  : Value ($ n)
    V-ƛ  : Value (ƛ A ∙ N)
    V-Λ  : Value N → Value (Λ N)
    V-⟪⟫ : Value M → Inert c → Value (M ⟪ Θ , c ⟫)

    Inert  = { id (` X) , seal X , s ↦ t , ∀X. s }
    Active = { id A with Base A , unseal X }

with the classification "by the **conversion constructor** alone — no
type is inspected and no slot arithmetic occurs" (`Design.md` §5).  The
split is Siek and Chen's (`notes/ParameterizedCastCalculi.md`), and its
whole point is to buy back exactly the staticness STA gives up:
`Inert (seal X)` is a claim the value keeps carrying, whereas STA has to
consult the observer's `δᵢ` in the ambient `{Δ}` to decide whether the
same embedding is a value.

Two knock-on differences.

* `V-Λ` carries `Value N` because **we reduce under `Λ`** (`ξ-Λ`).  STA
  does not: "Polymorphic expressions are values" (p.1072) and
  `Λα. eᵢ` is an `i`-primval for *arbitrary* `eᵢ` (Fig. 20).  This is
  the single most consequential difference in the whole comparison and
  §8 is about it.
* STA's canonical-forms lemma (Lemma 3.2, p.1051) has the clause "if
  `τ = t`, then `t ∉ Dom(δᵢ)` and `vᵢ = ⌈v̂ⱼ⌉^t_{jℓ}" — one shape.  Ours
  (`canon-var`) has two, `seal X` and `id (` X)`, which is why we need
  `IdPush` and they do not.


## 7. (6) What each design has that the other lacks

**STA has, and we do not.**

* **n agents with an arbitrary knowledge assignment**, plus a
  *compatibility* condition (Def. 3.1) that lets agents share
  knowledge.  We are two-sided per boundary: interior and exterior.
  Sharing, for us, is not a separate notion — a `bind` entry lives in
  one type context and everyone reading that context sees it.
* **The abstraction theorems, which are the paper's actual payoff.**
  Theorem 3.11 (Independence of Evaluation, p.1055), Lemma 3.12 (Value
  Abstraction, p.1055), Theorem 3.13 (Host-Provided Values, p.1056).
  We have type safety, determinism and tightness; we have proved no
  parametricity-flavoured theorem.
* **Erasure to the plain calculus** (Lemma 3.8 p.1054, Lemma 5.8
  p.1075, Theorem 5.10 p.1076), which is what licenses calling the
  boundaries "only a proof technique" (p.1054).  We have `Eval`'s
  `Trace` and seven pinned runs, but no erasure theorem.
* **State and recursive types** (§4, §5.1).

**We have, and STA does not.**

* **An explicit type context on each boundary** — `interior Θ Δ` and
  `convCtx Θ Δ` — and therefore masking, `unlock`, and tightness.
* **Strong (under-`Λ`) reduction.**
* **A leaf-by-leaf conversion `c` instead of one annotation `τ`**, with
  `conv-seal` as the soundness gate: a conceal must cite a live binder,
  `Δ ∋ X := A`, and lookup is a partial *function* (`∋:=-det`).  STA's
  `[embed]` instead relates the two types by the chain `≲_ℓ`, which is
  a relation with a nondeterministic `[trans]` (their footnote 3,
  p.1051).
* **An exact dual.**  Their Reversal (Lemma 3.4, p.1052) is
  unconditional because there is no context to invert.  Ours is the
  frame identity `(†)`,

      interior (dual Θ) (interior Θ Δ)
        ≡ map masked (pushBinds (binds Θ) []) ++ Δ    given  Δ ⊢ᵐ Θ

  (`proof/PeelDual.interior-dual`) — *the crossing frame IS the
  exterior*, one masked bind prefix in.
* **Determinism as a theorem** (`det`), where STA treats it as a
  convenience ("probably not necessary", p.1042).
* **A machine-checked development**, `--safe`, postulate-free.

**A methodological difference worth naming.**  STA's abstraction
theorems are proved with **external companion predicates**: Fig. 15
(p.1057) defines two relations `φ(e)` and `Ψ(e)` by inference rules
outside the type system, and Lemma 3.15 (Host-Provided Preservation,
p.1058) is a *second* subject-reduction argument showing `φ` is
preserved.  Lemma 3.12's `φ` has five clauses, of which (4) and (5) —

> (4) If `⌈v̂ⱼ⌉^τ_{jℓ}` is a `k`-term in `eᵢ`, then `⊢ t ≲_{ℓk} τ`.
> (5) `j` never appears in an embedding list within `eᵢ` except as the
> first element.

— are per-boundary shape invariants maintained by hand.  Our design law
1 forbids exactly this:

> **Grounded invariants.**  No external companion predicate.  Every
> invariant lives *in the relation*, is minted by the rules and
> preserved by reduction.

Their `φ` is what a design pays when the type system does not carry the
invariant; our `env` premises are what it costs to carry it.  Whether
our abstraction theorems, when we state them, will avoid a `φ` of their
own is an open question this note does not settle.


## 8. Program (a): the pre-boundary counterexample, run in STA

The source (`Design.md` §1, `Examples` §14, `E₀`), machine-rendered:

    ((ΛX. (λx:(∀Y. (Y⇒Y)). (ΛY. x [Y]))) [ℕ] · (ΛZ. (λx:Z. x)))

In our design this runs to a value in five steps and `E₃ → E₄` is
`TyPeelR` — "the line the pre-boundary design died on".  At that redex,
the crossed value's frame is the single lock `↓X` and its two contexts
are (`Examples` §14, `E-int` / `E-ext`, rendered by
`scripts/render_term.sh`):

    interior (↓X) Δ    Y Λ-bound , ⌷[X := ℕ]
    convCtx  (↓X) Δ    Y Λ-bound ,   X := ℕ

where the pre-boundary design had `∅`.  `E-Y-inside` and `E-X-hidden`
pin both halves.

**Now translate and run it in STA.**  Apply Fig. 22 with `i = 1` and
fresh agents `2, 3, 4`.  Writing `ID = ∀Z. Z→Z`:

    e = ((ΛX. ⌈λf₂:ID. ΛY. ⌈(⌈f₂⌉^{ID}_2)[Y]⌉^{Y→Y}_3⌉^{ID→∀Y.Y→Y}_2)[ℕ])
          (ΛZ. ⌈λz₄:Z. z₄⌉^{Z→Z}_4)

The two embeddings come from `[Ttypeabs]` (one per `Λ`) and the
`⌈f₂⌉^{ID}_2` from `[Tvar]`, where the variable's colour differs from
the desired colour.  All `δₖ = ∅` initially (Lemma 5.7).

Diagram:

    S₀  ((ΛX. ⌈λf₂:ID. ΛY. ⌈(⌈f₂⌉^{ID}_2)[Y]⌉^{Y→Y}_3⌉^{ID→∀Y.Y→Y}_2)[ℕ])
          (ΛZ. ⌈λz₄:Z. z₄⌉^{Z→Z}_4)
        |
        |  [∀1]: δ₁ := {X = ℕ}.  {ℕ/X}₁ touches nothing —
        |  X occurs in no 1-coloured annotation.  NO BOUNDARY IS MINTED:
        |  the boundary was already there, put by the translation.
        v
    S₁  (⌈λf₂:ID. ΛY. ⌈(⌈f₂⌉^{ID}_2)[Y]⌉^{Y→Y}_3⌉^{ID→∀Y.Y→Y}_2)
          (ΛZ. ⌈λz₄:Z. z₄⌉^{Z→Z}_4)
        |
        |  [9]: the embedded function is lifted out.  ℓ = ε, so the
        |  argument re-embeds at agent list `1 rev(ε)` = `1`.
        v
    S₂  (λx₁:ID. ⌈ΛY. ⌈(⌈⌈x₁⌉^{ID}_1⌉^{ID}_2)[Y]⌉^{Y→Y}_3⌉^{∀Y.Y→Y}_2)
          (ΛZ. ⌈λz₄:Z. z₄⌉^{Z→Z}_4)
        |
        |  [5]: β, with W = ΛZ. ⌈λz₄:Z. z₄⌉^{Z→Z}_4
        v
    S₃  ⌈ΛY. ⌈(⌈⌈W⌉^{ID}_1⌉^{ID}_2)[Y]⌉^{Y→Y}_3⌉^{∀Y.Y→Y}_2
        |
        |  [∀2]: the embedding moves INSIDE the Λ.  {Δ} unchanged.
        |  THIS IS THE DRIFT — the analogue of ↓X coming to sit
        |  under a later ΛY.
        v
    S₄  ΛY. ⌈⌈(⌈⌈W⌉^{ID}_1⌉^{ID}_2)[Y]⌉^{Y→Y}_3⌉^{Y→Y}_2      a VALUE

**And there it stops.**  `Λα. eᵢ` is an `i`-primval (Fig. 20, p.1071),
so `S₄` is a value and the type application `(…)[Y]` sitting under the
`ΛY` is **never reached**.  Our `E₃ → E₄` is a step STA cannot take.

So the direct answer to "what plays the role of the drifted `↓X`" is:
**the embedding `⌈·⌉^{Y→Y}_2` at `S₄` is the drifted boundary, and
nothing goes wrong for two independent reasons.**

1. Their boundary carries no context, so there is nothing for `[∀2]` to
   drop.  Our pre-boundary design died because a conceal's interior was
   the exterior *truncated* at the concealed variable, and at
   `Γ = Y , X:=ℕ` that prefix is `∅`.  STA never had the prefix, so it
   never truncated it.  Lesson 1 (*mask, don't drop*) has no STA
   counterpart because STA has nothing to drop.
2. Evaluation is **weak**, so the rule that killed the pre-boundary
   design — the one that eliminates a *concealed polymorphic value* —
   is unreachable.  That is a statement about *reachability* only; it
   is (1), and the fork below, that make the drift harmless.

**A hypothetical, flagged as mine.**  Suppose one made STA strong, i.e.
allowed reduction under `Λ`, and ran `S₄` further.  The inner
`⌈W⌉^{ID}_1` is an embedding at a `∀` type, so `[∀2]` fires again —
twice, once per layer — and then `[∀1]` fires at `(ΛZ. …)[Y]`, a
`3`-coloured type application, giving `{Δ} ⊎₃ {Z = Y}`, i.e.
`δ₃(Z) = Y`, while the enclosing `ΛY` is still there.

**And nothing dangles.**  `Y` is not a name that can go out of scope in
STA.  It is a **globally allocated name**, and the knowledge base is
**monotone**: Def. 5.4 (p.1073) makes `{Δ} ≤ {Δ′}` a single extension
`{Δ} ⊎ᵢ {α = τ}`, and Lemma 5.5 (Preservation, p.1073) carries the
extra conclusion "`{Δ′}` is compatible and **refines** `{Δ}`".  If a
later step eliminates the enclosing `ΛY`, it does so by `[∀1]` at some
`(ΛY. …)[T]` of some colour `k`, and *that step records* `Y = T` in the
same registry **before** the binder is gone.  Either way `Y` remains a
legal type — STA has no type well-formedness judgement that could
refuse it (§2) — and it remains a legal *view*: `Δ̄₃(Z) = Y` if
`k ≠ 3`, and `Δ̄₃(Z) = T` if `k = 3`, compatibility's total order being
`FTV(T) ≺ Y ≺ Z` in the second case.  The registry resolves `Z`
through `Y` exactly as it was built to.  (An earlier draft of this note
claimed `δ₃(Z) = Y` would be left dangling; that was wrong, and the
trace above does not show it.  `[∀1]` records before it removes.)

**What the trace does show is the fork.**  STA's freshness is entirely
meta-level — "we can always satisfy this condition by suitable alpha
conversion" (p.1072), "always possible via alpha-conversion of `∀α.τ`"
(p.1071) — and the paper names the discipline itself: the semantics is
"similar to the allocation-based, explicit type-passing semantics for
polymorphism found in the dissertation of Morrisett [1995]" (p.1071),
its preservation is proved "as usual for an allocation-style semantics"
(p.1073), and the conclusions liken the arrangement to "the restriction
operator, `ν`, of the pi calculus to generate a 'fresh' type variable at
runtime" (p.1078).  Under allocation there is no *position* at which a
name stops being nameable, so "out of scope" cannot arise and
tightness is **vacuous — independently of whether evaluation is weak or
strong** (§11).  Making STA strong would not create a scope problem; it
would only make more of the same registry reachable.

The real contrast with Strong System F is therefore **lexical scope
versus a global registry**.  Our binders live *in contexts*; `lock X`
masks a slot **in place** (`D34`); a boundary's two contexts are
*computed at its current position*, `interior Θ Δ` and `convCtx Θ Δ`;
and those frames are preserved by reduction under `Λ`, because `ξ-Λ`
pushes `abst` onto `Δ` and every rule re-derives the frame at the new
position.  That is precisely the `D33` fork, and we took the other
branch on purpose: "realization (i), a global `Σ`-store, **NOT taken** —
lexical scope is needed for lock blocking"
(`notes/DesignSpace.md`, edge `D33→D34`; `Design.md` §9;
`notes/RedesignAdvice.md` Q1, realizations (i) and (ii)).  **STA is the
design that took (i).**  So STA's theorems being *silent* on tightness
(§11) follows from the fork, not from weak evaluation; and `E₃ → E₄`
being a step STA cannot take is a separate fact, about which
configurations its evaluation order makes reachable.


## 9. Program (b): STA's three-agent counterexample, run in ours

Their configuration (p.1048): `δᵢ(t) = int`, `δⱼ(s) = t`, `δₖ = ∅`, and
the `k`-term `⌈⌈3ᵢ⌉^t_i⌉^s_j`.

Ours is `Examples` §12b / `proof/PreserveObstruct`, and the
correspondence is exact.  Take the exterior

    scripts/render_term.sh 'showTCtx Δi'    =    X := Y , Y := ℕ

so `X` is their `s` (representation `Y`) and `Y` is their `t`
(representation `ℕ`).  Then

    scripts/render_term.sh 'showTmIn 2 Vi'
      =  ((7 ⟪ seal Y ⟫) ⟪ ↥Y , seal X ⟫)

**is their nested embedding**, with `7` for `3`: the inner boundary
conceals the numeral at `Y` (that is `⌈3ᵢ⌉^t_i`) and the outer conceals
the result at `X` (that is `⌈·⌉^s_j`).  The `↥Y` is there because `Vi`
sits inside a boundary that locks `Y`:

    scripts/render_term.sh 'showTCtx (interior Θi Δi)'
      =  X := Y , ⌷[Y := ℕ]

Now put it under an eliminator — an `id X` layer under a reveal — and
take the two steps:

Diagram:

    R₀   ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , seal X ⟫) ⟪ id X ⟫)
            ⟪ ↓Y , unseal X ⟫)
      |
      |  IdPush   (Θ₁ = [] , Θ₂ = ↓Y ;
      |            Θ₁ ⋉ Θ₂ = ↓Y , rewind Θ₂ = ↥Y , ↓Y)
      v
    R₁′  ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , seal X ⟫) ⟪ ↓Y , unseal X ⟫)
            ⟪ ↥Y , ↓Y , id Y ⟫)
      |
      |  CancelR, lifted through the outer boundary by ξ-⟪⟫
      v
    R₂   ((((7 ⟪ seal Y ⟫) ⟪ ↥Y , ↓Y , id Y ⟫) ⟪ ↥Y , ↓Y , id Y ⟫)
            ⟪ ↥Y , ↓Y , id Y ⟫)                            a VALUE

(`R₁′` and `R₂` are `wallR₁` and `wallR₂`, rendered here by
`scripts/render_term.sh 'showTmIn 2 wallR₁'` and `… wallR₂`; the step
`wallstep₁` and the typing `⊢wallR₁ = preservation ⊢Ri wallstep₁` are in
`Examples` §12b.)

**What CancelR and IdPush do with their counterexample.**

* The **two-layer tower is never touched**.  `⟪ seal Y ⟫` and
  `⟪ ↥Y , seal X ⟫` stay two boundaries throughout.  Their `[8]` would
  merge them into one and record the history in the list `ij`; we
  record it as the nesting, which no rule collapses.
* `CancelR` cancels only the **outer** conceal `seal X` against the
  reveal `unseal X` that meets it, neutralising *both conversions to
  identities* while **keeping both frames**.  The inner `seal Y` is
  untouched.  So "the middle type's abstractness to the middle agent" —
  the thing their `[trans]`+Idempotence argument has to establish — is
  never at issue: nothing about the inner layer is consulted.
* Their unsound collapses are not merely too permissive for us, they
  are **untypeable**.  `conv-seal` requires `Δ ∋ X := A`, and lookup is
  a function (`∋:=-det`): `X`'s representation is `Y`, once and for
  all.  There is no derivation of `seal X : ℕ ⇝ X`, which is what
  `⌈3ᵢ⌉^s_i` would need.  Where STA's soundness rests on the *label
  list*, ours rests on *representations being stored once at the
  binder* — `notes/DesignSpace.md`'s `D33`.
* `IdPush` is the rule with no STA counterpart at all.  It exists
  because our `canon-var` has two shapes where their Lemma 3.2 has one
  (§6), and its content is the **scope move**: `Θ₂`'s whole scope —
  locks *and* unlocks, in order — travels into the inner frame, and
  what stays outside is `rewind Θ₂`, whose net effect on the type
  context is nothing (`scope (rewind Θ₂) Δ ≡ Δ`).  The representation
  `Y` that the reveal hands back is thereby presented *outside* the
  lock, where it is nameable.  STA has no such problem because its
  `δᵢ` is global: a representation is never "inside" anything.

That last bullet is the whole comparison in miniature.  **A global
knowledge base cannot have the wall, and cannot have tightness either.**


## 10. Table

| aspect | STA | Strong System F |
|--------|-----|-----------------|
| boundary syntax | `⌈eⱼ⌉^τ_ℓ` — one annotation, one agent list | `M ⟪ Θ , c ⟫` — a context morphism and a conversion tree |
| what the boundary knows about scope | nothing | `interior Θ Δ` and `convCtx Θ Δ`, both computed from the ambient `Δ` |
| where an instantiation is recorded | ambient `{Δ} ⊎ᵢ {α = τ}`, global and monotone (Def. 5.4, p.1073) | a `bind A` entry on a boundary in the term |
| reduction judgement | `⟨{Δ}, eᵢ⟩ ↦→ ⟨{Δ′}, e′ᵢ⟩`, `{Δ}` may grow | `Δ ⊢ M -→ M′`, same `Δ` throughout |
| abstraction mechanism | opacity: `t ∉ Dom(δᵢ)` | opacity (`Δ ∋ X := A`) **and** unnameability (`Nameable`) |
| out-of-scope variable | does not exist; `Θ` is freshness-only (p.1072) | `masked E`, refused by `wf-var` |
| re-exposure | — | `unlock X` (`↥X`), with `sw-u` refusing vacuous unlocks |
| type abstraction intro | `[Ttypeabs]` at the `Λ`, by translation (p.1075) | `TyBeta` at the type application, by reduction |
| type application through a boundary | `[∀2]` pushes the embedding inside the `Λ`; `[∀1]` extends `δᵢ` and substitutes `{τ/α}ᵢ` | `TyPeelR`: one bind prepended, interior instantiated at the fresh **name** `` ` 0 ``, conversion re-minted as `instReveal 0 s` |
| pushing the type argument in | into `i`-coloured subterms only | never — law 3 forbids term type-shifts |
| function crossing | `[9]`, eager, reverses the agent list | `Peel`, at the application, under `dual Θ` |
| nested boundaries | merged by `[8]`; ordered list `ℓ` is the residue | towers; eliminated at the use (law 6) |
| why order matters | three-agent counterexample, p.1048 | `¬frame-locksOnly`, `proof/MoveScope` §4b |
| cancel | `[8]` + `[6]` (multiagent), `[H4]` (two-agent) | `CancelR` — both frames kept, both conversions neutralised |
| `Value` | dynamic: depends on the observer's `δᵢ` in the ambient `{Δ}` (p.1074) | syntactic; `Inert`/`Active` by conversion constructor |
| reduction under `Λ` | no — `Λα. eᵢ` is an `i`-primval | yes — `ξ-Λ`, and `V-Λ` carries `Value N` |
| determinism | a convenience (p.1042) | design law 5, theorem `det` |
| principals | `n` agents, compatible knowledge (Def. 3.1) | two sides per boundary |
| main theorems | type safety; erasure; Independence of Evaluation (3.11); Value Abstraction (3.12); Host-Provided Values (3.13) | `progress`, `preservation`, `type-safety`, `det`, `value-¬step`, plus tightness as a tested property |
| invariants | external companion predicates `φ`, `Ψ` (Fig. 15, p.1057) | grounded in `env`'s premises (law 1) |
| mechanized | no | yes, `--safe`, postulate-free |


## 11. What "tightness" would mean in STA, and whether the paper settles it

Our statement (`Design.md` §8, law 2 and §7):

> A masked slot may not be named in any type; `Nameable` and `wf-var`
> are the whole enforcement. … Build an ill-typed redex whose fault is
> one localized `wf-var` premise: a subterm names a type variable the
> frame at its position masks, or has no entry for at all.  Take the
> step.  The rule moves that subterm into a new frame.  The rule is
> **tight** iff the contractum is refused for the same reason.

Transplanting the *definition* to STA gives: *reduction never lets a
subterm name a type variable it could not name in the redex.*  In STA
that predicate is **vacuously true and vacuously empty**, because
"could name" is total: every type variable is a legal type for every
agent everywhere, there is no type well-formedness judgement, and `Θ`
is consulted by no rule — type variables are **allocated names**, not
scoped binders (§8).  There is no ill-typed-for-a-scope-reason redex
to build, so the test cannot even be run.  The paper's theorems
therefore neither imply nor contradict tightness; they are **silent**,
and silent for a structural reason rather than an oversight — the
reason being the `D33` fork of §8, allocated names versus lexical
binders, and not the paper's evaluation order.

The non-vacuous shadow of tightness in STA is its **abstraction**
theorems, and they are a different kind of statement:

* Def. 3.10 (obliviousness) and Theorem 3.11 (Independence of
  Evaluation, p.1055) say an agent that does not *know* `t` cannot
  behave differently on two values of type `t`.  That is
  indistinguishability — semantic, about *observations*.
* Ours is scope preservation — syntactic, about *derivations*.
  `notes/DECISIONS.md` (line 217ff.) is blunt about that: "Terms cannot
  mention later variables anyway (they predate them), so **tightness
  restricts derivations, not terms**; but it is the design intent behind
  'strong'."

The closest STA gets to our machinery is Lemma 3.12's `φ`, whose clauses
(4) and (5) are per-boundary shape invariants preserved by reduction —
structurally our `env` premises, but living outside the type system,
which our design law 1 forbids.  And their `[9]`'s `rev(ℓ)` argument
(p.1050) is, word for word, our argument for reversing `dualScope`.

So the honest summary is: **STA and Strong System F agree on the
list-order fact and on the "interior keeps the abstract name" fact, and
diverge on scope entirely.**  STA does not need tightness because its
type variables are **global allocated names in a monotone knowledge
base** — freshness by meta-level α-conversion, `{Δ}` only ever extended
(Def. 5.4, p.1073) — and *not* because it never reduces under a `Λ`: a
name that is never scoped cannot leave a scope, whatever the evaluation
order (§8).  That is the `D33` fork, and STA is the design that took
the global-store branch we did not
(`notes/DesignSpace.md`, edge `D33→D34`).

Strong reduction is a **second, independent** difference, and it is the
one that decides how much a boundary must carry *once lexical scope has
been chosen*: it makes the drifted boundary of §8 reachable, so a
boundary must carry a context, and every question this development spent
a week on — mask vs. drop, push vs. bind, merge vs. tower, drop vs. move
the locks — appears at once.  The through line of `DesignSpace.md`,
*nothing may be dropped*, is the answer to a question that arises only
on the lexical branch.


## 12. Flags — what I could not confirm

* The PDF has no ToUnicode maps; I extracted its text layer with a
  hand-written decoder over the TeX base encodings (OT1 / CMMI / CMSY).
  Displayed formulas came out reliably, but **superscript and subscript
  placement on the embedding notation `⌈·⌉^τ_ℓ` had to be
  reconstructed** from the surrounding prose.  Every rule transcribed
  above was cross-checked against the paper's own prose description of
  it; where the prose did not pin a detail I say so.  The transcriptions
  of `[7]`, `[8]`, `[9]`, `[∀1]`, `[∀2]`, `[∀intro]`, `[∀elim]`,
  `[embed]`, `[eq]`, `[trans]`, `[Hfn]`, `[Ttypeabs]` and `[Ttypeapp]`
  are the ones I rely on.
* **Fig. 7's metavariables** (p.1043) came out of the extraction with
  `[Cfn]` and `[Hfn]` interleaved; I fixed the domain/codomain naming
  from the paper's prose sentence about the argument annotation, quoted
  in §2.  The side condition itself, `t ∉ τ′`, is unambiguous in the
  extraction; only which type `τ′` names was reconstructed.
* **Fig. 15's `Ψ` relation** (p.1057) renders in the extraction as a
  blank; I read it as an auxiliary relation named alongside `φ` from the
  prose ("Figure 15 presents two relations, `φ(e)` and `Ψ(e)`").  Its
  exact name is not load-bearing here.
* The claim that **no rule has a premise `FTV(τ) ⊆ Θ`** rests on
  (i) reading Fig. 20 and Fig. 12, (ii) the paper's own sentence "(Θ is
  unused by the new version of the old rules.)" (p.1072), and (iii) a
  text search for `FTV`, `in scope` and `well-formed` over the whole
  extraction, whose only hits are Fig. 21 (the *source* polymorphic
  lambda calculus, p.1074), Lemma 5.7's `Θ = FTV(Γ)` (p.1075) and §4's
  store well-formedness.  I am confident, but this is a negative claim
  about a 44-page paper.
* §8's strong-reduction hypothetical is **my analysis, not the paper's**.
  STA never considers reduction under `Λ`, and nothing in it is wrong
  because of this.  Its verdict — that nothing dangles, because `{Δ}`
  is monotone and `[∀1]` records `Y = T` *before* the binder is removed
  — rests on Def. 5.4 and Lemma 5.5 (p.1073), which I read directly.
  The paper never runs the configuration, so it neither confirms nor
  denies the reading.  (Review round 1 withdrew an earlier draft's
  opposite claim, that the registry entry would be left dangling and
  that weak evaluation is therefore what buys STA its freedom from
  tightness.  Both are retracted; §8 and §11 now say what the trace
  actually shows.)
* **The `Value` rule of §5.2 as printed reads `t ∉ Dom{Δ}`** — the
  union.  The quote in §6 is faithful: I verified the glyphs, `Dom` in
  CMTI10 then CMSY10 `{`, CMR10 `0x01` = `Δ`, CMSY10 `}`, the same byte
  pattern as the `{Δ}` of `{Δ} ⊢ eᵢ : Value` two lines earlier.  The
  **per-agent reading** `t ∉ Dom(δᵢ)` given in §6 is therefore *mine*;
  the paper states no correction.  My grounds are the same sentence's
  own prose (`Δ̄ᵢ(t) = t`), Fig. 9's `i`-value grammar (`t ∉ Dom(δᵢ)`,
  p.1046) and the Progress counterexample in §6.  The other five
  occurrences of `Dom{Δ}` in the paper — the definition
  `Dom{Δ} = ⋃ᵢ Dom(δᵢ)` and the side conditions of `[∀intro]`,
  `[∀elim]`, `[∀1]` and Def. 5.4 (all p.1071–1073) — are the union and
  are transcribed as such.
* The three-agent counterexample's term is given in the paper as
  `⌈⌈v̂ᵢ⌉^t_i⌉^s_j` with the value written `3ᵢ` in the following
  sentence's collapsed forms; I have used `3ᵢ` throughout for
  readability and `7` on our side, matching `Examples` §12b.
