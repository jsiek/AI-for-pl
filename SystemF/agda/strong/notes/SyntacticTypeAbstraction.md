# Grossman, Morrisett & Zdancewic, *Syntactic Type Abstraction* (TOPLAS 22(6), pp. 1037–1080)

Digest of what the JOURNAL version adds over ICFP'99 (notes/Zdancewic-embeddings.md — read that
first; nothing there is repeated). Printed page = PDF page + 1036. Notation normalised to the
earlier digest: `⌈e_j⌉^τ_ℓ` for the embedding, `≲_ℓ` for the chain relation, `∀` for the paper's
∀-quantifier glyph. Transcriptions are read off the PDF **text layer** (`pdftoppm` is not installed
in this container, so figures could not be re-rendered); two spots where the layer was ambiguous
are flagged inline.

## 0. LEAD — verdicts on our in-flight choices

* **VALIDATES the ambient dual / Γ-indexed reduction.** §5.2, p. 1071: to get polymorphism they
  must change `e_i -i→ e_i'` into `⟨{Δ}; e_i⟩ -i→ ⟨{Δ'}; e_i'⟩` — an ambient knowledge base
  threaded through reduction, "similar to the allocation-based, explicit type-passing semantics of
  Morrisett [1995]". Our `_⊢_-→_ : TCtx → Term → Term → Set` is the same move, for the same reason.
* **VALIDATES depth-1 values and `canon-var-conceal`.** Canonical Forms, Lemma 3.2, p. 1051, third
  clause: *if τ = t then t ∉ Dom(δ_i) and v_i = ⌈v̂_j⌉^t_{jℓ}* — a **primval** inside, i.e. depth 1,
  and the annotation is the bare variable. Under polymorphism the notion of value becomes
  *dynamic* (p. 1074): `{Δ} ⊢_i e_i : Value` iff `e_i` is an i-primval, or `e_i = ⌈v̂_j⌉^t_ℓ` with
  `t` not in the relevant domain (the text layer drops the subscript here; the preceding sentence
  says the test is `Δ_i(t) = t`, so read `t ∉ Dom(δ_i)` *in the current* `{Δ}`). Roadmap step 2 is
  their design exactly.
* **ANSWERS the open B₂′ sub-decision: keep the OUTER boundary type.** Merge [8], p. 1049, is
  `⌈⌈v̂_j⌉^u_ℓ⌉^τ_{kℓ'} -i→ ⌈v̂_j⌉^τ_{ℓkℓ'}` — annotation = the **outer** `τ`; the middle type `u`
  is discarded and reconstructed by the chain; labels append inner ++ outer, middle agent kept.
* **WARNS about Merge's cancel clause (the one thing here that could bite us).** p. 1048 gives a
  three-agent counterexample: `δ_i(t)=int`, `δ_j(s)=t`, `δ_k=⊥`; collapsing the k-term
  `⌈⌈3_i⌉^t_i⌉^s_j` to *either* `⌈3⌉^s_i` or `⌈3⌉^s_j` "violates the type-abstraction properties
  because neither i nor j knows that s abstracts an int". The type system admits the nested term
  and `⌈3⌉^s_{ij}` **and nothing else**. p. 1049 repeats it: "naively stripping away embeddings
  loses information about which agents could have contributed information about the type of a
  term." Their [8] therefore **never deletes** — it only appends; erasure happens solely at [6]
  (annotation = base type `b`), and Fig. 11's evaluation ends `[8]` then `[6]`. Our `Θ₁ ⊕ Θ₂`
  cancel clause (a `↓X:=A` of Θ₁ against the `↑X:=A` of Θ₂ — *both entries vanish*) is precisely
  a deletion inside a still-abstract composite. It is plausibly safe (a matched reveal/conceal pair
  is an identity, not a chain link, and `Drop∅` is the analogue of their [6]) but it is the one
  place where our Merge diverges from the rule they proved sound, so it deserves its own
  adversary in the Merge gauntlet.
* **Nothing in the paper refutes the x-license install.** See §2: their treatment of an
  unknowable realization is an *ordinary* δ entry whose value is a globally-abstract variable, and
  the condition that makes it harmless is literally our "claims nothing".

## 1. What the journal adds — the System F treatment (§5.2, Figs. 20–22, pp. 1070–1076)

New syntax (Fig. 20, p. 1071): `τ ::= … | ∀α.τ`; `e_i ::= … | Λα.e_i | e_i[τ]`; and crucially
**`v̂_i ::= … | Λα.e_i`** — a Λ is an i-**primval**, matching our `ΛX.V` value. `Δ_i(∀α.τ) =
∀α.Δ_i(τ)` (α-convert so α ∉ Dom δ_i).

Typing adds a *static* scope set Θ of Λ-bound variables, so judgments become `Θ;{Δ};Γ ⊢_i e_i : τ`:

```
  [∀intro]  Θ,α;{Δ};Γ ⊢_i e_i : τ        (α ∉ Θ ∪ Dom{Δ})
            ---------------------------------------------
            Θ;{Δ};Γ ⊢_i Λα.e_i : ∀α.τ

  [∀elim]   Θ;{Δ};Γ ⊢_i e_i : ∀α.τ     Δ_i(τ′) = τ′     (α ∉ Dom{Δ})
            ---------------------------------------------------------
            Θ;{Δ};Γ ⊢_i e_i[τ′] : {τ′/α}τ
```

Note `α ∉ Dom{Δ}` where `Dom{Δ} = ⋃_i Dom(δ_i)`: a Λ-bound variable is in **nobody's** knowledge
map, so `Δ_i(α) = α` for every agent i, and τ may mention α. The old rules are unchanged; Θ is
unused by them.

Reduction (Fig. 20):

```
  [∀1]  ⟨{Δ}; (Λα.e_i)[τ]⟩       -i→  ⟨{Δ} ⊎_i {α = τ};  {τ/α}_i e_i⟩
  [∀2]  ⟨{Δ}; ⌈Λα.e_j⌉^{∀α.τ}_ℓ⟩ -i→  ⟨{Δ};              Λα.⌈e_j⌉^τ_ℓ⟩
```

* **[∀1] does BOTH**: it extends `δ_i` with `α = τ` *and* substitutes τ into the i-coloured parts
  of the body via a **colour-indexed substitution** `{τ/α}_i` ("substitution of τ for α only in
  terms coloured i, including i-subterms of any j-coloured subexpressions", p. 1072; extended
  pointwise to Γ). Why both: recording feeds the boundaries; substituting restores the invariant
  `Γ ⊢_i e : τ ⟹ Δ_i(τ) = τ`, which p. 1072 says **polymorphism otherwise breaks** — "this
  invariant is harder to maintain now that an agent may *learn* information about a type variable
  at runtime."
* **[∀2] is our TyWrap — minus the entry.** The boundary is simply pushed inside the Λ; the label
  ℓ is unchanged, `{Δ}` is unchanged, **no new entry and no dual is minted**. It works because α is
  a global name that both the inner and the outer agent see as abstract, so the same annotation τ
  is legal on both sides. (As printed there is no most-concrete side condition on [∀2], unlike [9];
  none is needed for typing because `Δ̄_i` commutes with ∀, though it overlaps retag [7].)
* `{Δ}` **never shrinks**: Definition 5.4, p. 1073, defines `{Δ} ≤ {Δ}⊎_i{α=τ}` and its reflexive
  transitive closure "refines"; Λ-scoping is handled *statically* by Θ only. There is no analogue of
  discarding an entry when leaving a Λ's scope.

### Does a type application at an ABSTRACT variable arise? **No — the configuration is unreachable.**

Three facts conspire. (a) The invariant `Γ ⊢_i e : τ ⟹ Δ_i(τ) = τ` (p. 1051), so a ∀-type is
syntactically a ∀. (b) An embedding *value* is annotated only at a variable `t ∉ Dom(δ_i)`, so its
type is that **variable**, never a ∀ — hence no value of ∀-type is an embedding, and by canonical
forms every value at a ∀-type is a Λ-primval. (c) Progress (Lemma 5.6, p. 1074, with the sketch at
p. 1053/1054) dispatches on `⌈v_j⌉^τ_ℓ` in a fixed order: `Δ̄_i(τ) ≠ τ` → **retag [7]**; `v_j` an
embedding → **merge [8]**; then by the shape of τ: `b` → [6], `τ′→τ″` → [9], `∀α.τ′` → [∀2],
otherwise (τ a variable) **it is a value**. So an eliminator never meets a boundary at an abstract
annotation: retag [7] fires first on the knowing side, or the term is inert.

**Our E★′ in their language.** Reconstructing E★′ under their own translation (Fig. 22): ΛX spawns
agent j, ΛY spawns agent k, and `f` is used across the boundary as `⌈f⌉^{∀Z.(Z→ℕ)→(Z→ℕ)}_j` inside
k — p. 1074 flags exactly this: "[Tvar] … Because the type Γ(x) may mention type variables that are
currently in scope, the embedding may be abstract." k type-applies it: [∀2] pushes the boundary
inside the Λ, then [∀1] fires with `τ = Y`, giving `δ_k(Z) = Y` where **Y is a Λ-bound variable in
no agent's δ**. So: *the case where the realization is unknowable is, for them, a perfectly
ordinary knowledge entry whose value happens to be globally abstract.* Compatibility (Def. 3.1,
p. 1046) survives because Y is nobody's key, and the well-founded total order ("all variables in
δ_i(t) precede t") is satisfied because Y is not in any domain.

## 2. Their analogue of our dual's licensing (↑⋆ / ↓⋆ / `:=ˣ` / "claims nothing")

* **No rep-less entry form.** "Abstract" is *absence* from the partial map: `t ∉ Dom(δ_i)` (Fig. 9,
  p. 1046). `rvl⋆`/`cnc⋆` exist for us only because a de Bruijn context is total, so we must carry
  a marker where they carry a hole.
* **No exterior-read entry.** The nearest thing is `{τ/α}_i`, which pushes a realization into the
  i-coloured *term annotations* while leaving j-coloured subterms (and hence j's view) untouched —
  Lemma 5.2, p. 1072, is the two-part simultaneous induction that makes this precise: for `i = j`
  the type is substituted too, for `i ≠ j` the type is unchanged. That is the same
  "knowledge visible on one side of the boundary only" phenomenon our `X:=ˣA` encodes, obtained by
  a substitution instead of a marked entry.
* **"Claims nothing" is theirs, but as an invariant, not a premise.** Definition 3.10, p. 1054: "a
  set of agents S is *oblivious* to type t if for all i ∈ S, t ∉ Dom(δ_i)"; obliviousness is the
  hypothesis of every abstraction theorem (Thm. 3.11 Independence of Evaluation, p. 1055; Lemma
  3.12 clause (2)). Combined with the §1 observation — a Λ-bound rep is in nobody's domain — this
  is independent support for the *shape* of `(bwf-↓x)`'s load-bearing premise (the rep names only
  abstract variables of Ψ): that is exactly the situation in which their δ entry `Z ↦ Y` is
  compatible and information-free.
* **Divergence to keep in view.** For them `Z ↦ Y` is *usable* knowledge (`Δ̄_k(Z) = Y`, retag [7]
  will use it). Our `X:=ˣA` is deliberately invisible to `∋:=` to dodge the `¬hk-int` renaming
  trap. They have no such trap because type variables are global names and `{Δ}` is never renamed —
  so our restriction, and ruling (ii) (compare up to `≈Δ̄`), is the de Bruijn price for their global
  namespace, not a departure from their design.
* **Re-hiding itself** is rule [9] (p. 1049) and needs no knowledge lookup at all: the formal
  argument is re-embedded as `⌈x_i⌉^{τ⁰}_{i rev(ℓ)}` at the *inner* agent's type τ⁰, licensed by
  **Reversal**, now a bullet of Lemma 3.4, p. 1052. Our `dualᵇ`/`swapᵇ` obligation is discharged for
  them by the chain relation, never by an entry.

## 3. Δ̄ / (eq) / retag in journal form — the (a′)-vs-(a″) fork

* Fig. 13, p. 1051 is still just two rules: `[eq] Δ̄_i(τ) = Δ̄_i(τ′) ⟹ ⊢ τ ≲_i τ′` and `[trans]`.
  So **they take BOTH**: eager retag [7] *and* comparison-at-Δ̄. Our (a″) is (eq) without (7).
* **They comment directly on the fork**, p. 1049: they chose "to maintain the invariants that the
  static semantics always derives the most concrete type for any term, and that types explicitly
  mentioned in the lambda-abstraction syntax are most concrete… It would be possible to reformulate
  the calculus so that these conditions are relaxed (by allowing a nondeterministic type-refinement
  rule in the static semantics), but doing so would require additional **proof-normalization
  arguments**." That is a fair description of the price we accepted with (a″): the `≈Δ̄` congruence
  threaded through `(bwf-↓)`/`(bwf-↓x)`/`≼≈`. Note also that even *with* eager retag their **Arrow
  Lemma** (Lemma 3.4, p. 1052) needs "a tedious normalization argument" that deletes type variables
  from a chain — so a variant of that work is unavoidable on either side of the fork; (a″) does not
  add a new *kind* of obligation.
* **Determinism, not soundness, is what [7]'s side condition buys** (p. 1048): "This determinism of
  the type-refinement rules is not critical to the system, but it makes many of the proofs easier
  because there is only one applicable rule for each evaluation step."
* **Renaming/substitution stability of the comparison (our §5(i)/(ii) fork):** there is no separate
  transport hypothesis anywhere. The only stability statement is Lemma 5.2 (p. 1072), about the
  *whole judgment* under `{τ/α}_i`; the chain relation is stated over a global `{Δ}` and needs no
  renaming lemma. Consistent with ruling (ii) (state the comparison so it is stable) rather than
  (i) (add a transport hypothesis).
* Footnote 3, p. 1051, is a small Agda hint: `[trans]` is deliberately **nondeterministic**
  ("we are not concerned with an algorithmic presentation… This formulation lets us slightly
  simplify the proofs of the Type-Relations Properties"). Do not make `⊕`/`Reversal≈` algorithmic
  for its own sake.

## 4. Merge / cancel in journal form, and the F-fragment safety proof

* **[8] is ICFP (8) verbatim**, modulo how the label is written (`ℓ k ℓ′` for inner ++ middle ++
  outer, vs ICFP's `ℓ_j : ℓ_k`). Side conditions unchanged: `u ∉ Dom(δ_k)` (the inner embedding
  really is a k-value) and `τ = Δ̄_i(τ)`. Two-agent `[H4]` (Fig. 4) is unchanged and p. 1049 says
  explicitly that [8] *replaces* it in the symmetric setting, for the "no lost authority" reason
  quoted in §0.
* **The preservation case (p. 1052–1053) is one line of chain algebra**: from `⊢ τ″ ≲_{jℓ} u` and
  `⊢ Δ̄_k(u) ≲_{kℓ′} τ′`, use `u ∉ Dom(δ_k) ⟹ Δ̄_k(u) = u` to join them with `[trans]`, then
  **Idempotence** (`⊢ τ ≲_{ℓ i i ℓ′} τ′ iff ⊢ τ ≲_{ℓ i ℓ′} τ′`) collapses the duplicated k. So the
  thing that makes the two chains composable is precisely **the middle type's abstractness to the
  middle agent** — the role our `cancel-agree` plays, and one more reason to state our `⊕`
  obligation as "middle type" rather than as an equality of reps.
* **F-fragment safety structure.** Preservation is Lemma 5.5, p. 1073, and it carries an extra
  clause we do not currently state: *"Furthermore {Δ′} is compatible and refines {Δ}"* (with
  refinement from Def. 5.4). Its two new cases are [∀1] (discharged entirely by Lemma 5.2) and
  [∀2] (discharged by Lemma 5.3, `∀ Type Relations`: `{Δ} ⊢ ∀α.τ¹ ≲_ℓ ∀α.τ ⟹ {Δ} ⊢ τ¹ ≲_ℓ τ`).
  Progress is Lemma 5.6, p. 1074, over the dynamic `Value`; the variable-type case is "else e_i is
  a value", i.e. it is *canonical forms* (Lemma 3.2) that carries the weight, exactly as our
  `canon-var-conceal` must.
* **The recipe for a new type constructor** is stated twice (§5.1 for μ, §5.2 for ∀) and is worth
  copying as a checklist: **one push-the-boundary-through-the-constructor rule** with a
  most-concrete side condition for determinism ([μ4], Fig. 19 p. 1068; [∀2]) + **one Type-Relations
  inversion lemma** (Lemma 5.1 for μ, 5.3 for ∀, Arrow for →) + **one clause of Δ̄** + **one clause
  of canonical forms**. Our `cf-⇒-B₀`/`cf-∀-B₀` inversions *are* the Type-Relations lemmas.
* **Where the boundaries sit in their System F translation** (Fig. 22, p. 1075) is the mirror image
  of ours: `[Ttypeabs] C[[Γ ⊢ Λα.e : ∀α.τ]] i γ = Λα.⌈e_j⌉^τ_j` (j fresh — the boundary is minted
  at the **Λ**, with a singleton label), while `[Ttypeapp]` is completely transparent,
  `(e_i[τ′])`. We mint at the **elimination** (TyWrap). Their Theorem 5.10 (p. 1076) is the
  correctness of that translation (erase ∘ C = id up to evaluation), i.e. the source-language
  faithfulness result our compile/DGG-style story would want.

## 5. Mapping table (journal-only rows; ICFP rows are in notes/Zdancewic-embeddings.md §3)

| paper (journal) | ours | mismatch / note |
|---|---|---|
| `⟨{Δ}; e_i⟩ -i→ ⟨{Δ′}; e_i′⟩` (p. 1071) | `Δ ⊢ M -→ M′` | **match** (ambient knowledge threaded through reduction) |
| `{Δ} ≤ {Δ}⊎_i{α=τ}`, "refines" (Def. 5.4) | — | **gap**: our preservation says nothing about how Δ may change. Add it. |
| Θ (static set of Λ-bound vars), unused by old rules | the Λ-bound slots of Γ | ours is the same context as the term vars; theirs is a separate set |
| `[∀1]`: extend δ_i **and** `{τ/α}_i` (p. 1072) | `TyWrap` records `↑Y:=A`, no substitution | **the third option in our (a′)/(a″) fork** — rewrite the annotations rather than record-and-compare |
| `[∀2]`: push boundary inside Λ, label unchanged, no dual | `TyWrap` + reveal entry + (later) dual | ours must mint an entry because interior/exterior contexts differ; theirs shares one global α |
| `Λα.e_i` is an i-**primval** (Fig. 20) | `ΛX.V` is a value | **match** |
| `δ_k(Z) = Y` with Y Λ-bound (no one's key) | `Z :=ˣ Y` + `(bwf-↓x)` + absOnly | same situation; theirs is plain usable knowledge, ours is exterior-read-only (renaming) |
| `t ∉ Dom(δ_i)` = abstract | `rvl⋆` / `cnc⋆` | marker vs. hole; forced by de Bruijn totality |
| Def. 3.10 obliviousness | `(bwf-↓x)`'s "claims nothing" | theirs is a hypothesis of the abstraction theorems, ours a premise of a licensing rule |
| `[8]` merge: outer annotation, append labels, keep middle agent | `Merge`, `Θ₁ ⊕ Θ₂` with **cancel** | **flagged**: theirs never deletes (see §0); ours does |
| `[6]` strip at `b` | `Drop∅` (and the "both faces agree" generalisation) | ours strictly weaker; theirs is what terminates evaluations |
| Lemma 3.4 Idempotence / Reversal / Arrow | `⊕ᵇ` collapse / `dualᵇ` face law / `cf-⇒` | **match** — the three lemmas we need are exactly their three |
| Lemma 5.2 (colour-indexed subst, 2-part induction) | `⊢renameᵀ` / substitution lemmas | closest thing to a stability statement; no transport hypothesis anywhere |
| Fig. 22 boundary at the **Λ**, transparent type application | boundary at the type **application** | mirror image; theirs gives one boundary per Λ, ours one per use |
| `ref τ` must be exported at `ref τ` or fully abstractly; Δ̄ does not descend under `ref` (p. 1063) | — | a *tightness* restriction on the comparison; no refs in our calculus, but the pattern (a constructor the comparison may not enter) is worth remembering |

## 6. Concrete take-aways

1. **Adopt the refinement clause in preservation** (Def. 5.4 / Lemma 5.5, p. 1073): our
   Γ-indexed preservation should also conclude that the *outgoing* Δ is well-formed and extends the
   incoming one monotonically. Today the ambient Δ is an input only; the paper needed this clause to
   close the F fragment, and it is the statement that stops a reduction from silently inventing
   knowledge — a grounded-invariants-law obligation we have not written down.
2. **Give Merge's cancel clause its own adversary, modelled on p. 1048.** Their [8] appends and
   never deletes, and the reason is a concrete three-agent counterexample. Before landing `⊕`,
   build the analogue (three nested boundaries, only the middle one knowing the middle type) and
   check that our cancel does not collapse it to something both faces accept. If it does not
   survive, the fallback is theirs: merge by appending only, and let `Drop∅` (their [6]) do all the
   erasing.
3. **Keep the outer boundary type `B₂` for the merged wrapper** (the [8] shape, p. 1049), and state
   the `⊕` obligation as *"the middle type is abstract to the middle boundary"* rather than as an
   equality of stored reps — that is what discharges their case, via `[trans]` + Idempotence.
4. Cheaper, already flagged in the ICFP digest and re-confirmed by Fig. 11: **generalise `Drop∅`**
   to "both faces agree" (their [6] at base type). Fig. 11's evaluation only terminates because
   [8] is followed by [6].
5. Worth *considering, not adopting*: the colour-indexed type substitution `{τ/α}_i` of [∀1]
   (p. 1072). It is the only mechanism in the literature that restores the eager-most-concrete
   invariant in the presence of polymorphism, and it is a third point on our (a′)/(a″) fork. Cost:
   it rewrites type annotations inside terms (Lemma 5.2's two-part simultaneous induction is the
   price), which is at best in tension with our no-term-shift law; and our whole `≈Δ̄` apparatus
   exists to avoid it. Recorded for completeness.
6. **Copy their per-constructor checklist** (§4 above) when we round out the calculus: push-through
   rule + Type-Relations inversion + Δ̄ clause + canonical-forms clause. It predicts precisely the
   lemma set we already have, which is a good sign.

## 7. Where our design goes beyond theirs

* **The combined multi-entry boundary.** Their embedding is a colour change carrying *one*
  annotation and a list of *principals*; ours carries a list of *entries with representations* in
  two directions at once. Their knowledge lives in a global, compatible, well-founded registry
  `{Δ}`; ours lives in the boundary and the context, which is what the grounded-invariants law
  demands and what makes our merge harder than their `[trans]`.
* **Tightness and blocking.** `intOf`, `cmax`, `Scoped (baseS Θ Δ) B₀` — the Example-8 fix — has no
  counterpart. Their types are closed over a global variable namespace; nothing can be *blocked*,
  and Example 8 cannot arise for them. Conversely, blocking is the sole reason we need `X:=ˣA`
  at all.
* **The x-license.** Because their reps are global names, "unknowable here but readable one level
  out" is not a distinct state for them — it is either in `δ_i` or it is not. `(bwf-↓x)` is our
  reconstruction of the same situation inside a de Bruijn context, and the paper's obliviousness
  invariant is the closest thing to an independent justification of its "claims nothing" premise.
* **The dual.** They have no `dualᴳ`: [9]/[∀2] re-embed the argument at the *inner* type and appeal
  to Reversal. Our ambient dual (copy Δ's own entry, `abst ⇒ rvl⋆`) does the work their global
  namespace does for free.
