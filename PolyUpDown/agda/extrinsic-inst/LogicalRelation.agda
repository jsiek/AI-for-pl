{-

File Charter (planned):
  * Define the step-indexed logical relation for `PolyUpDown` (extrinsic-inst).
  * Use one framework to derive both:
      1) relational parametricity
      2) dynamic gradual guarantee
  * Keep this file focused on the relation definitions and their proof skeleton.
    Put reduction/type-preservation details in their owner modules.

------------------------------------------------------------------------------
Resources and design commitments
------------------------------------------------------------------------------

We will explicitly follow three resources already cited in this file:

1. Max New dissertation (`/Users/jsiek/bib/dissertation-new.pdf`), especially
   the step-indexed + Kripke world structure for graduality/parametricity
   together (Chapter 10 logical relation section).

2. GTLC/Peter logical relation
   (`/Users/jsiek/gradual-typing-in-agda/LogRel/PeterLogRel.lagda`):
   two-direction expression relation (`≼`/`≽`) with timeout on one side and
   “more-precise side may blame”.

3. Existing System F logical relation in this repo
   (`SystemF/agda/extrinsic/LogicalRelation.agda`):
   naming/style (`𝒱`, `ℰ`, relation environments, open-term interpretation),
   substitution/renaming closure lemmas, and fundamental-theorem structure.

Additional local assumption (from current discussion):
  * `PolyUpDown/agda/extrinsic-inst` reduction rules will match
    `PolyUpDown/agda/extrinsic/Reduction.agda` up to module-path differences.

We will therefore use explicit step indexing (not SIL) and keep the relation
shape close to New/Peter, with System F-style environment plumbing.

------------------------------------------------------------------------------
Detailed plan: exact relation shape
------------------------------------------------------------------------------

Design decision (recommended split):
  * Do not use `_∣_⊢_⦂_⊑_` directly as the primary LR index.
  * Define a separate, store-free imprecision relation (in
    `Imprecision.agda`) and index the logical relation by that evidence.
  * Treat `_∣_⊢_⦂_⊑_` / `_∣_⊢_⦂_⊒_` as cast realizers used by compatibility lemmas.

Why this split:
  * Keeps LR indices clean (avoids threading `Σ`/`Φ` through every relation).
  * Matches New-style architecture: LR indexed by precision derivations,
    with parametricity from reflexive precision.
  * Avoids entangling Kripke/world-extension proofs with cast-typing bookkeeping.
  * Still reuses the existing `UpDown` cast metatheory where it is strongest.

Concrete split plan:
  Status (2026-04-13):
    [x] 1. Add `Imprecision.agda` with store-free imprecision evidence
     (and whichever directional decomposition is most convenient).
    [~] 2. Prove bridge lemmas:
       imprecision evidence -> well-typed `Up`/`Down` casts in
       `_∣_⊢_⦂_⊑_` / `_∣_⊢_⦂_⊒_` under suitable `Σ` and `Φ`.
       Structural fragment implemented in `ImprecisionBridge.agda`;
       remaining work is discharging/providing the `★` endpoint realizers.
    [ ] 3. Define `𝒱`/`ℰ` indexed by precision evidence (not by cast syntax).
    [ ] 4. For cast compatibility cases in the fundamental theorem, invoke
     bridge lemmas + existing `UpDown`/`Terms` infrastructure.

Term precision plan (add explicitly; currently only sketched):
  * We need an explicit syntactic term-precision judgement, not just the
    theorem statement. Follow the architecture in:
      - `PeterPrecision.lagda` (`Γ ⊩ M ⊑ M′ ⦂ c`)
      - New Ch.10 (`Γv ⊢ Ml v Mr : Av`, plus cast-side rules).

Planned artifacts:
  1. `TermPrecision.agda`:
     define a judgement of the form
       `Γv ⊢ M ⊑ M′ ⦂ Av`
     where `Γv` maps variables to type-imprecision evidence.

  2. Structural term-precision rules:
     variable, constants/primitives, lambda/application, type abstraction and
     instantiation, ν binder, and congruence through term constructors.
     (This is the analogue of the structural rules in New’s PolyCν figures.)

  3. Cast-specific precision rules:
     include rules that relate adding casts on either side, analogous to New’s
     cast-bridge rules (the “important four” in Ch.10), but expressed using
     PolyUpDown syntax (`up`/`down`) and our bridge lemmas from precision
     evidence to well-typed `Up`/`Down`.

  4. Blame precision rule:
     include the asymmetric blame clause (as in Peter/New): the more-precise
     side may blame while preserving graduality obligations.

  5. Metatheory for term precision:
     reflexivity and transitivity (if needed for proof scripts), context
     weakening/substitution, and compatibility with type precision transport.

How this plugs into the LR:
  * Fundamental theorem should explicitly quantify over this judgement:
      if `Γv ⊢ M ⊑ M′ ⦂ Av` then `Γv ⊨ M ≈ M′ ⦂ Av`.
  * Parametricity is recovered via reflexive precision witnesses.
  * Dynamic gradual guarantee is recovered from closed-term instances plus
    the two-direction (`≼`/`≽`) expression relation.

0) Preliminaries imported/assumed in this folder
   * `Types`, `TypeProperties`, `Store`, `Ctx`, `Terms`, `UpDown`.
   * Reduction/multi-step from `extrinsic-inst` (mirroring `extrinsic`).
   * Typing preservation/progress lemmas used only as prerequisites for
     soundness lemmas, not as part of the relation definition itself.

1) Direction and indexing
   Define exactly:

     data Dir : Set where
       ≼ : Dir    -- count steps on the left
       ≽ : Dir    -- count steps on the right

   and mutually define value/expression relations indexed by:
   * step index `n : ℕ`
   * direction `dir : Dir`
   * world `w`
   * relational type index `Av` (type-imprecision evidence)
   * closed terms/values on left and right.

   Timeout convention:
   * `ℰ 0 dir w Av Mˡ Mʳ = ⊤` (no obligations at 0).

2) World structure (Kripke + store growth)
   Use a world carrying:
   * `Σˡ`, `Σʳ` : left/right runtime stores.
   * a finite association `η` between seals in `Σˡ` and `Σʳ`.
   * each association stores a relation payload used to interpret abstract/sealed
     values (this is the PolyUpDown analogue of the dissertation’s case-map).
   * partial-bijection side conditions on `η` (a seal on each side maps to at
     most one counterpart).

   Define world extension `w′ ⪰ w`:
   * step index decreases (or stays for non-strict extension; strict extension
     used for “later”/guarded recursion).
   * stores grow monotonically on each side.
   * old `η` entries are preserved; new entries may be appended.

   Define `Later`/clamping operations on relations by decrementing index and
   requiring the relation in all strict future worlds.

3) Type relational index `Av`
   The logical relation will be indexed by a type-imprecision witness `Av`,
   not raw type pairs. This matches the dissertation design and gives:
   * graduality directly (heterogeneous case),
   * parametricity by reflexive instances (`A ⊑ A`).

   Concretely, `Av` should cover:
   * base/base,
   * function,
   * polymorphic `∀`,
   * dynamic cases (`★` vs `★`, and dynamic-vs-static),
   * seal/abstract-name cases tied to world `η`.

   Cast-level link:
   * keep explicit lemmas translating `Av` to well-typed `Up`/`Down` evidence
     (or vice versa where needed) so compatibility lemmas for `up/down` reuse
     existing `UpDown`/`Terms` infrastructure.

4) Value relation `𝒱`
   Define:

     𝒱 : (n : ℕ) → Dir → World → Av → Term → Term → Set

   with these clauses:

   * Base case:
     related iff constants are identical.

   * Function case (`A₁⇒B₁` vs `A₂⇒B₂` with precision witness):
     both values must be lambdas; for all related arguments, bodies are related
     at expression level.
     Use a guarded condition (`m < n` or explicit `Later`) to satisfy Agda
     termination.

   * Polymorphic case:
     both values must be type abstractions.
     For every future world `w′`, every choice of instantiation types, and every
     admissible relation `R` for the new type variable, instantiate both terms
     and require expression-relatedness in the extended world.
     This is the key parametricity clause.

   * Dynamic/unknown case:
     follow New/Peter: values at `★` are related by matching runtime tags/seals,
     then payloads are related at a later index via world interpretation.
     Direction-sensitive decrementing is used exactly where open-sum/tag
     inspection consumes one observed step.

   * Seal case (`｀ α`):
     lookup `(αˡ, αʳ, R)` in world association `η`; require payload relation `R`.
     This is where freshness/ν-allocation interacts with parametricity.

5) Expression relation `ℰ`
   Define:

     ℰ : (n : ℕ) → Dir → World → Av → Term → Term → Set

   For `suc n`, copy the GTLC/Peter two-direction structure:

   * Direction `≼`:
     1. left takes one step and relation continues at `n`, or
     2. right may reduce to blame, or
     3. left is already a value and right multi-steps to a related value.

   * Direction `≽`:
     1. right takes one step and relation continues at `n`, or
     2. right may reduce to blame, or
     3. right is already a value and left multi-steps to a related value.

   Important:
   * Use store-aware one-step/multi-step configurations, threading each side’s
     store and transporting worlds through store growth.
   * Use the same convention as `extrinsic/Reduction.agda` for ν-steps and
     congruence renamings.

6) Environment interpretation for open terms
   Mirror System F structure, but world-aware and heterogeneous:
   * relational type-variable environment (maps type vars to type pairs +
     relation payload),
   * relational term environment (maps term vars to related closed values).

   Define `𝒢 Γ ρ γ` pointwise:
   * each variable maps to expressions/values related at the corresponding
     precision witness.

   Define open-term logical relation:

     Γ ⊨ M ≈ M′ ⦂ Av

   meaning: for all admissible `(w, ρ, γ)` satisfying `𝒢`, substituted/instantiated
   terms are in `ℰ`.

7) Core closure lemmas required immediately after definitions
   (same proof engineering pattern as System F file)
   * Monotonicity in step index (`n′ ≤ n`).
   * Monotonicity in world extension (`w′ ⪰ w`).
   * Renaming/substitution closure for `𝒱`, `ℰ`, and `𝒢`.
   * `𝒱 ⇒ ℰ` (related values are related expressions).
   * Compatibility with multi-step on either side.
   * Fundamental cast-compatibility lemmas for `up/down` using `UpDown`
     typing/equational lemmas.

8) Fundamental theorem plan (single theorem powering both goals)
   Prove by induction on term-precision derivation:

     If `Γ ⊢ M ⊑ M′ : Av` then `Γ ⊨ M ≈ M′ ⦂ Av`.

   Compatibility cases needed:
   * var, λ, app, Λ, type-app, ν binder, constants/prims.
   * `up` and `down` cast introduction.
   * blame and congruence/administrative forms.

9) Corollaries
   * Dynamic gradual guarantee:
     instantiate fundamental theorem at closed terms and both directions.
     Extract operational statement:
       - simulation up to blame on the more-precise side,
       - matching termination/divergence behavior otherwise.

   * Relational parametricity:
     specialize to reflexive precision witness (`A ⊑ A`) and `∀` case.
     Obtain standard free-theorem shape:
       if inputs are related under arbitrary relation `R`, outputs are related.

10) Suggested implementation order in this file
   1. Datatypes for `Dir`, world records, world extension.
   2. Relation interfaces (`𝒱`, `ℰ`, environment records).
   3. Concrete clauses for `𝒱`/`ℰ`.
   4. Monotonicity + transport lemmas.
   5. Open-term relation + substitution machinery.
   6. Fundamental theorem skeleton in `Parametricity.agda`.
   7. Exported corollaries (parametricity + graduality).

------------------------------------------------------------------------------
Practical proof guidance for this codebase
------------------------------------------------------------------------------

* Follow the existing Agda style notes in `AGENTS.md`:
  explicit `with` clause names (no `...` shorthand in multi-case/nested `with`),
  avoid local `where` under `rewrite`,
  and use explicit transport bridges when dependent equalities appear.

* Keep de Bruijn/store-transport details localized:
  use `Store`, `Ctx`, and `TypeProperties` lemmas instead of re-proving
  renaming/substitution boilerplate in this file.

* For ν/fresh-seal cases, prove small world-extension helper lemmas first
  (extend left/right store, preserve bijection invariants, and extend `η`)
  and reuse them in both `𝒱`/`ℰ` and the fundamental theorem.

-}
