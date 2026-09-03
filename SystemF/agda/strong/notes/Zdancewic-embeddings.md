# Zdancewic, Grossman & Morrisett, *Principals in Programming Languages* (ICFP'99, pp. 197–207) — what it says about our boundaries

Digest for Jeremy + supervisor. Only the parts bearing on `notes/BoundaryRules.md` §1–§2 (R1/R1′/R2, merge)
and PLAN.md §4. Page numbers are the printed pages (197–207); PDF page = printed − 196.
Transcriptions below are read off the rendered figures, not the OCR layer.

## 1. The embedding construct

### 1a. Two-agent calculus (§2, pp. 198–200)

One global abstract type `t`, one global realization `τ_h`. Two colours: agent `a` (does **not** know `t = τ_h`),
host `h` (does). Syntax, **Figure 4, p. 198**:

```
  τ  ::= t | b | τ -> τ'
  A  ::= x_a | c | λx_a:τ. A | A A' | ⌈H⌉^τ_h            -- agent terms
  Â  ::= c   | λx_a:τ. A | ⌈Ĥ⌉^t_h                       -- agent VALUES
  H  ::= x_h | c | λx_h:τ. H | H H' | ⌈A⌉^τ_a            -- host terms
  Ĥ  ::= c   | λx_h:τ. H                                 -- host VALUES (no embedding!)
```

`⌈e_j⌉^τ_c` = "code of colour `c` exported to the enclosing colour at type `τ`". Note the asymmetry: an agent
value may be an embedded host value **only at annotation `t`** (i.e. only when the agent learns nothing), and
only when the body is a host *value*; a host value is never an embedding.

Typing, **Figure 7, p. 200** (`{τ_h/t}τ` = the host's view of `τ`):

```
  (HinA)   Γ ⊢ H : {τ_h/t}τ                (AinH)   Γ ⊢ A : τ
         ------------------------                 ---------------------------
           Γ ⊢ ⌈H⌉^τ_h : τ                          Γ ⊢ ⌈A⌉^τ_a : {τ_h/t}τ

  (Hfn)   Γ[x_h : τ'] ⊢ H : τ   (t ∉ τ')    -- host binders may not mention t
        ------------------------------
         Γ ⊢ λx_h:τ'. H : τ' -> τ
```

Reduction, **Figure 5, p. 199** (`e`/`ê` polychromatic term/value):

```
  (P1) e e'          ↦ e'' e'     if e ↦ e''
  (P2) ê e'          ↦ ê e''      if e' ↦ e''
  (P3) (λx:τ. e) ê   ↦ {ê/x}e

  (A1) ⌈H⌉^τ_h                 ↦ ⌈H'⌉^τ_h     if H ↦ H'          -- congruence, colour switch
  (A2) ⌈c⌉^b_h                 ↦ c                               -- strip at base type
  (A3) ⌈λx_h:τ. H⌉^(τ'->τ'')_h ↦ λx_a:τ'. ⌈{⌈x_a⌉^τ_a / x_h} H⌉^τ''_h

  (H1) ⌈A⌉^τ_a                 ↦ ⌈A'⌉^τ_a     if A ↦ A'
  (H2) ⌈c⌉^b_a                 ↦ c
  (H3) ⌈λx_a:τ. A⌉^(τ'->τ'')_a ↦ λx_h:{τ_h/t}τ'. ⌈{⌈x_h⌉^τ_h / x_a} A⌉^τ''_a
  (H4) ⌈⌈Ĥ⌉^t_h⌉^(τ_h)_a       ↦ Ĥ                               -- CANCEL of nested embeddings
```

### 1b. Multiagent calculus (§3, pp. 201–204)

`n` agents; each agent `i` has a finite partial map `δ_i` from type variables to types. **Global consistency is
assumed** (p. 202): if `t ∈ Dom(δ_i) ∩ Dom(δ_j)` then `δ_i(t) = δ_j(t)`; and the type variables are globally
well-founded ("all variables in `δ_i(t)` precede `t`"). `Δ̄_i(τ)` = the limit of iterating `δ_i` = agent `i`'s
most concrete view of `τ`.

Syntax, **Figure 11, p. 202** — the embedding is labelled by a *non-empty list of agents* `ℓ_j` starting at `j`:

```
  (labels)      ℓ_i ::= i | ℓ_i : ℓ_j
  (i-terms)     e_i ::= x_i | c | λx_i:τ. e_i | e_i e_i' | fix f_i(x_i:τ).e_i | ⌈e_j⌉^τ_{ℓ_j}
  (i-primvals)  v̂_i ::= c | λx_i:τ. e_i
  (i-values)    v_i ::= v̂_i | ⌈v̂_j⌉^t_{ℓ_j}        (t ∉ Dom(δ_i))
```

**A nested embedding is *never* a value** — the body of a value-embedding must be a *primval*.

Reduction, **Figure 12, p. 203** (the novel rules):

```
  (3)  e_j -j-> e_j'  ⟹  ⌈e_j⌉^τ_{ℓ_j} -i-> ⌈e_j'⌉^τ_{ℓ_j}
  (6)  ⌈c⌉^b_{ℓ_j}                     -i-> c
  (7)  ⌈v̂_j⌉^τ_{ℓ_j}                   -i-> ⌈v̂_j⌉^(Δ̄_i(τ))_{ℓ_j}          (τ ≠ Δ̄_i(τ))
  (8)  ⌈⌈v̂_j⌉^u_{ℓ_j}⌉^τ_{ℓ_k}         -i-> ⌈v̂_j⌉^τ_{ℓ_j : ℓ_k}           (u ∉ Dom(δ_k), τ = Δ̄_i(τ))
  (9)  ⌈λx_j:τ. e_j⌉^(τ'->τ'')_{ℓ_j}   -i-> λx_i:τ'. ⌈{⌈x_i⌉^τ_{i:rev(ℓ_j)} / x_j} e_j⌉^τ''_{ℓ_j}
                                            (x_i fresh, τ' -> τ'' = Δ̄_i(τ' -> τ''))
```

Typing, **Figure 14, p. 204**, with the chain relation `{Δ} ⊢ τ ≲_ℓ τ'` of **Figure 15, p. 204**:

```
  (embed)  {Δ}; Γ ⊢_j e_j : τ'    {Δ} ⊢ τ' ≲_{ℓ_j : i} τ
          ---------------------------------------------
                {Δ}; Γ ⊢_i ⌈e_j⌉^τ_{ℓ_j} : Δ̄_i(τ)

  (eq)     Δ̄_i(τ) = Δ̄_i(τ')            (trans)  {Δ} ⊢ τ ≲_{ℓ_i} τ''   {Δ} ⊢ τ'' ≲_{ℓ_j} τ'
          --------------------                          -------------------------------------
           {Δ} ⊢ τ ≲_i τ'                                    {Δ} ⊢ τ ≲_{ℓ_i : ℓ_j} τ'
```

So: **one** annotation type + a list of principals; the *inner* type is not stored, it is whatever the chain
`≲_{ℓ_j:i}` can justify. This is structurally our `⟪ Θ , B₀ ⟫`: one type, one list.

## 2. Nested embeddings — merge, cancel, push-in

* **Merge: YES, rule (8), p. 203.** Two adjacent embeddings collapse into one and the **labels are appended**
  (`ℓ_j : ℓ_k`). Side conditions: the inner annotation `u` is abstract to the *middle* agent `k`
  (`u ∉ Dom(δ_k)` — i.e. the inner embedding really is a `k`-value), and the outer annotation is already
  fully refined (`τ = Δ̄_i(τ)`). The preservation case (Appendix, **p. 207**) is: chain
  `τ' ≲_{ℓ_j:k} u` with `u = Δ̄_k(u) ≲_{ℓ_k:i} τ` by **(trans)**, then drop the duplicated `k` by
  **Lemma A.1 (Idempotency)**. Merge is *soundness by transitivity of the chain relation.*
* **Cancel: YES in the two-agent system, (H4), p. 199** — `⌈⌈Ĥ⌉^t_h⌉^{τ_h}_a ↦ Ĥ`: an embedding meeting its
  inverse annihilates. It is legitimate there precisely because there is exactly one `t` with exactly one
  realization `τ_h`, so the inner annotation and the outer one are forced to agree. In the multiagent system
  (H4) is *replaced* by (8)+(6) (stated explicitly on p. 203, §3.3).
* **Needed for progress, not an optimisation.** p. 204, after Lemma 3.2: "rules (6) through (9) guarantee that
  `⌈v_j⌉^τ_{ℓ_j}` is not stuck unless it is a value", and the value grammar (Fig. 11) admits only a *primval*
  inside. Likewise Lemma 2.1 (Canonical Forms, p. 200): a value at type `t` is `⌈Ĥ⌉^t_h` with `Ĥ` a host value.
  So the depth-1 value invariant is load-bearing.
* **They explicitly considered and rejected our option (b)** (p. 203, right column): "We could have chosen to
  allow nested embeddings to be values, so long as each inner embedding is a value with respect to the
  enclosing agent … This allows embeddings to pile up in a way that is difficult to deal with syntactically
  and that complicates the dynamic semantics. Instead, we allow rule (8) to collapse two embeddings and push
  the work of ensuring compatibility onto the `≲_ℓ` relation."
* **Application: dual/swap, (A3)/(H3)/(9).** The embedded λ is *pulled out* as an outer λ; the bound variable
  is replaced by an embedding of the **new outer variable in the opposite direction**, and in the multiagent
  case the label is **reversed**: `⌈x_i⌉^τ_{i:rev(ℓ_j)}`. Justified by **Lemma A.2 (Reversal), p. 207**:
  `⊢ τ ≲_{ℓ_i} τ'` implies `⊢ τ' ≲_{rev(ℓ_i)} τ`. This is exactly our `dualᵇ` / `swapᵇ`, and Reversal is
  exactly our missing-in-general dual-face law. **Lemma A.3 (Arrow Type)** is the `cf-⇒` inversion.
  Note the direction: they pull the *function* out; we (R2) push the *argument* in. Same content.
* **Type application: absent.** No polymorphism in the calculus. But §4.1, **p. 205**, sketches it and picks
  *our R1*: "represent the body of a polymorphic function `Λα.e_i` as an agent with no information about `α`.
  When such a function is applied to a type `τ`, a new agent `j` that knows `α = τ` is spawned with the body
  `e_i` embedded inside it." Spawning an agent that knows `α = τ` **is** `rvl τ`; recording rather than
  substituting is their choice too. (They also note the other option — plain System F with agent type
  variables kept disjoint — as "straightforward".)
* **Rule (7)** (retag the annotation to `Δ̄_i(τ)`) has no analogue in ours: our `env` derives both faces from
  `B₀`, so there is nothing to refine. It is (7) that makes (8) and (9)'s side conditions satisfiable, i.e.
  it plays the role our `cf-∀-B₀`/`cf-⇒-B₀` inversions play.

## 3. Mapping table

| paper | ours | mismatch |
|---|---|---|
| embedding `⌈e_j⌉^τ_{ℓ_j}` | `M ⟪ Θ , B₀ ⟫` | theirs is one-sided (a colour change); ours combines many reveals/conceals at once |
| annotation `τ` (single type) | `B₀` (single boundary type) | **match** — both store one type and derive/justify the other side |
| label list `ℓ_j` | `Θ : BCtx` | theirs is a list of *principals*; ours a list of *entries with reps*. Ours carries the knowledge; theirs looks it up in the global `δ_i` |
| `δ_i` / `Δ̄_i`, globally consistent | — (nothing) | **biggest mismatch.** They have a global, consistent, well-founded registry of realizations. We have none; that is exactly the hole `bad` exploits (memo §4) |
| `t ∉ Dom(δ_i)`, `i` cannot see `t` | `rvl A` — fresh internal abstract var, rep `A` external | match in spirit; theirs is a global name, ours a de Bruijn slot |
| host refines `t` to `τ_h` (`{τ_h/t}` in (AinH)/(H3)) | `cnc X A` — external var `X`, internal rep `A` | ours is *indexed by an external variable* and additionally **blocks** slots shallower than `cmax Θ`; theirs has no indices, no shifting, no blocking |
| `τ' ≲_{ℓ_j : i} τ` (chain relation) | `substᵗ (γᵇ Θ) B₀` / `substᵗ (ρᵇ Θ) B₀` | ours is a *function* on both faces; theirs a *relation*. A relation composes (trans); our two projections do not obviously compose — that is why merge is hard for us |
| scope premise | `Scoped (baseS Θ Δ) B₀` | **no analogue.** Their types are closed over global variables; the only ordering condition is the well-foundedness of `δ` (p. 202). Example 8 cannot arise for them |
| (H4) cancel / (8) merge | *not adopted* | see §4 |
| (A2)/(H2)/(6) strip at base type `b` | `Drop` (only at `Θ ≡ []`) | theirs strips whenever the annotation carries no abstraction; ours is strictly weaker and unreachable |
| Lemma A.2 Reversal | `dualᵇ` / `swapᵇ` face law | **match**; ours fails on `rvld` exteriors (`no-dual-Γ₃`), theirs is unconditional because there is no context |
| Lemma A.1 Idempotency | — | needed for merge; would be `Θ ⊕ᵇ Θ` collapsing a repeated frame |

## 4. Recommendation

**Not (a) and not (b) as stated — (c): keep R1/R2 (float-inside), and add merge, but only after grounding.**

Reasons, in order of weight:

1. **The paper's evidence is against (b).** Our current situation — `canon-var`'s "chain of wrappers ending at a
   conceal" — *is* the "embeddings pile up" design they considered and rejected on p. 203. Their reason is
   exactly our symptom: with piles you can no longer relate the innermost term's type to the outermost
   annotation, and `bad` (memo §4) is precisely a two-deep pile whose two annotations cannot be reconciled.
   Depth-1 values (Fig. 11) are what makes their progress proof go through.
2. **But (a) is the wrong half to adopt first.** R1′ is their rule (9) shape (fire on a syntactic λ/Λ); it is
   partial and *forces* merge. R1 is their §4.1 p. 205 sketch (spawn a principal that knows `α = τ`) and is
   total. Given merge, R1′ is a space optimisation, not a necessity. So: **R1 + R2 + merge**, with R1′ kept as
   an optimisation exactly as memo §2(b) recommends.
3. **Merge is only sound over a consistent knowledge base.** Their (8) is justified by (trans) + Idempotency
   over `≲_ℓ`, and `≲_ℓ` is sound only because `{δ}` is *globally consistent* (p. 202: `δ_i(t) = δ_j(t)`).
   We have no such registry, and memo §4 already proves that no merge can be type-preserving on `bad`. So
   merge **requires route 2 of memo §4** (a reveal puts `rvld A` into `intOf`; `bwf↓` demands `Δ ∋ X := A`).
   That is not an extra companion predicate — it is the grounded, in-the-relation form of the paper's `δ`
   consistency requirement, and it satisfies the standing grounded-invariants design law.

Proposed rule, in `BReduction.agda` style:

```agda
  -- MERGE (after Zdancewic et al. rule (8), p. 203).
  -- Θ₁ lives over the interior of Θ₂; the composite lives over the exterior of Θ₂.
  β-⟪⟫⟪⟫ : Value V
    → (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫  -→  V ⟪ Θ₁ ⊕ᵇ Θ₂ , B₂ ⟫

  -- Θ₁ ⊕ᵇ Θ₂ (the analogue of their label append ℓ_j : ℓ_k):
  --   * every `rvl A` of Θ₁ stays a reveal, its rep pushed out: `rvl (substᵗ (ρᵇ Θ₂) A)`;
  --   * every `rvl A` of Θ₂ that Θ₁ did NOT conceal stays a reveal, rep unchanged;
  --   * every `cnc X A` of Θ₁ with `X ≥ revs Θ₂` (a slot inherited from the exterior)
  --     becomes `cnc (X ∸ revs Θ₂ + cmax Θ₂) A`;
  --   * every `cnc X A` of Θ₂ stays a conceal, rep unchanged;
  --   * every `cnc X A` of Θ₁ with `X < revs Θ₂` is a CANCEL pair: it and the reveal it
  --     names both disappear.
```

**Invariant it relies on — and yes, it is exactly the open "rep inconsistency" issue.** The cancel clause is
well-typed only if `A` (the conceal's internal rep) equals the rep of the enclosing reveal it names. Under
today's `env` that is unprovable (memo §4, `bad`, `bad-cancel-ill-typed`), so **do not land merge on the
current relation.** Under route 2 the reveal contributes `rvld A` to `intOf` and `bwf↓` on `cnc X A` demands
`Δ ∋ X := A`, which *forces* the agreement — the merge clause then discharges by inversion, and `bad` ceases
to typecheck at all. This is the same move the paper makes: `≲_ℓ` is only transitive because the `δ_i` agree.

Two obligations to state before writing any proof:

```agda
  ⊕ᵇ-int : intOf Δ (Θ₁ ⊕ᵇ Θ₂) ≡ intOf (intOf Δ Θ₂) Θ₁                     -- contexts compose
  ⊕ᵇ-γ   : substᵗ (γᵇ (Θ₁ ⊕ᵇ Θ₂)) B₂ ≡ substᵗ (γᵇ Θ₁) B₁                   -- their (trans)+Lemma A.1
             -- given the env premise substᵗ (ρᵇ Θ₁) B₁ ≡ substᵗ (γᵇ Θ₂) B₂ (the "middle type")
  ⊕ᵇ-ρ   : substᵗ (ρᵇ (Θ₁ ⊕ᵇ Θ₂)) B₂ ≡ substᵗ (ρᵇ Θ₂) B₂
```

`⊕ᵇ-γ` is the whole content; it is the Agda form of their Appendix p. 207 case (8), and it is the statement
that will fail unless route 2 lands first. Suggested order: **route 2 → `⊕ᵇ` + `⊕ᵇ-int` probe → `β-⟪⟫⟪⟫`
→ tighten `canon-var` to depth-1 → progress.**

One further thing the paper does that we have not considered: **their strip rule (6)/(A2)/(H2) fires at any
annotation with no abstraction content (`b`), not only at an empty boundary.** Our `Drop` demands `Θ ≡ []`
and is therefore unreachable. An analogue — `V ⟪ Θ , B₀ ⟫ -→ V` whenever `substᵗ (γᵇ Θ) B₀ ≡ substᵗ (ρᵇ Θ) B₀`
(both faces agree, e.g. `B₀ = ℕ`) — is cheap, is what actually terminates their evaluations (Figure 13,
p. 203 ends `(8)` then `(6)`), and would give us a reachable termination for merged chains.
