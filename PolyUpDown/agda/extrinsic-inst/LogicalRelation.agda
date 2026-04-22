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

We will therefore use explicit step indexing (not SIL) and keep the relation
shape close to New/Peter, with System F-style environment plumbing.

Operational convention for this file:
  * The logical relation is meant to follow `ReductionFresh.agda`, using the
    fresh-store one-step relation `_∣_—→_∣_` and its multi-step closure.
  * Fresh seals are allocated at the back of the store, so the freshly created
    seal is `length Σ`, not `zero` plus a global shift of older seals.
  * Consequently, ν/fresh-seal observations in `𝒱`/`ℰ` should be phrased in
    the "fresh-at-the-end" style rather than the older shifted-store style of
    `_∣_—→[_]_∣_`.

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
    [x] 2. Prove bridge lemmas:
       imprecision evidence -> well-typed `Up`/`Down` casts in
       `_∣_⊢_⦂_⊑_` / `_∣_⊢_⦂_⊒_` under suitable `Σ` and `Φ`.
       Structural fragment implemented in `ImprecisionBridge.agda`;
       remaining work is discharging/providing the `★` endpoint realizers.
    [x] 3. Define `𝒱`/`ℰ` indexed by precision evidence (not by cast syntax).
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
      if `Γv ⊢ M ⊑ M′ ⦂ Av` then `Γv ⊨ M ⊑ M′ ⦂ Av`.
  * Parametricity is recovered via reflexive precision witnesses.
  * Dynamic gradual guarantee is recovered from closed-term instances plus
    the two-direction (`≼`/`≽`) expression relation.

0) Preliminaries imported/assumed in this folder
   * `Types`, `TypeProperties`, `Store`, `Ctx`, `Terms`, `UpDown`.
   * Reduction/multi-step from `ReductionFresh.agda` in `extrinsic-inst`.
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
     use elimination-oriented observation: for all related arguments, the
     applications of the observed values are related at expression level.
     Use a guarded condition (`m < n` or explicit `Later`) to satisfy Agda
     termination.

   * Polymorphic case:
     use elimination-oriented observation rather than matching only `Λ`-forms.
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
   * For ν-steps, follow `ReductionFresh.agda`: fresh allocation appends at the
     end of the store and the fresh seal is `length Σ`.
   * Do not rely on the older shifted-store convention of
     `_∣_—→[_]_∣_` when formulating ν/fresh-seal clauses.

6) Environment interpretation for open terms
   Mirror System F structure, but world-aware and heterogeneous:
   * relational type-variable environment (maps type vars to type pairs +
     relation payload),
   * relational term environment (maps term vars to related closed values).
   * As in `PeterLogRel`, the environment/substitution interpretation should be
     indexed by a single direction `dir : Dir`, not by both directions at once.
     Intuitively, a pointwise environment relation should say that each pair of
     substituted variables is related by `𝒱` in the chosen direction.

   Define the directional environment interpretation, something like
   `𝒢 Γ dir w ρ γ`, pointwise:
   * each variable maps to closed values related by `𝒱` at the corresponding
     precision witness and the chosen `dir`.
   * do not package both directions into `𝒢` itself; keep the directional split
     explicit so it matches the directional definitions of `𝒱` and `ℰ`.

   Define the directional open-term logical relation:

     Γ ∣ dir ⊨ M ⊑ M′ ⦂ Av

   meaning: for all admissible `(w, ρ, γ)` satisfying the directional `𝒢`,
   the instantiated terms are in `ℰ` at the same `dir`.

   Then define the user-facing open-term relation as the conjunction of both
   directions, again following `PeterLogRel`:

     Γ ⊨ M ⊑ M′ ⦂ Av = (Γ ∣ ≼ ⊨ M ⊑ M′ ⦂ Av) × (Γ ∣ ≽ ⊨ M ⊑ M′ ⦂ Av)

   and provide a projection helper to recover either direction when needed.

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

     If `Γ ⊢ M ⊑ M′ : Av` then `Γ ⊨ M ⊑ M′ ⦂ Av`.

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

module LogicalRelation where

-- File Charter:
--   * Defines the step-indexed logical relation core for extrinsic-inst
--   * `PolyUpDown`.
--   * Introduces direction/index/world/precision indices and concrete
--   * `𝒱`/`ℰ` clauses.
--   * Keeps closure/fundamental-theorem proofs for follow-up files.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; z<s)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; 0ℓ) renaming (suc to lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Types
open import Store using (_⊆ˢ_; done; keep; drop; ⊆ˢ-refl)
open import Imprecision
open import TypeProperties
  using (liftSubstˢ; substᵗ-ν-src; substᵗ-⇑ˢ; substᵗ-id; renameᵗ-substᵗ;
         substᵗ-ground; renameᵗ-preserves-WfTy; renameˢ-preserves-WfTy;
         TyRenameWf-suc; SealRenameWf-suc)
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermPrecision using (Prec; PCtx)
open import TermProperties using (Substˣ; substˣ-term; _[_]; _[_]ᵀ)
open import ReductionFresh using (Value; _∣_—→_∣_; _∣_—↠_∣_)

------------------------------------------------------------------------
-- Direction, world, and precision index
------------------------------------------------------------------------

data Dir : Set where
  ≼ : Dir
  ≽ : Dir

Rel : Set₁
Rel = ℕ → Dir → Term → Term → Set

record SealRel : Set₁ where
  constructor ηentry
  field
    αˡ : Seal
    αʳ : Seal
    Rη : Rel
open SealRel public

infix 4 _∋η_↔_∶_

data _∋η_↔_∶_ : List SealRel → Seal → Seal → Rel → Set₁ where
  hereη :
    ∀ {η αˡ αʳ R} →
    (ηentry αˡ αʳ R ∷ η) ∋η αˡ ↔ αʳ ∶ R

  thereη :
    ∀ {η αˡ αʳ R βˡ βʳ R′} →
    η ∋η αˡ ↔ αʳ ∶ R →
    (ηentry βˡ βʳ R′ ∷ η) ∋η αˡ ↔ αʳ ∶ R

infix 4 _⊆η_

data _⊆η_ : List SealRel → List SealRel → Set₁ where
  η-done : ∀ {η} → [] ⊆η η
  η-keep : ∀ {η η′ e} → η ⊆η η′ → (e ∷ η) ⊆η (e ∷ η′)
  η-drop : ∀ {η η′ e} → η ⊆η η′ → η ⊆η (e ∷ η′)

⊆η-refl : ∀ {η} → η ⊆η η
⊆η-refl {η = []} = η-done
⊆η-refl {η = e ∷ η} = η-keep ⊆η-refl

-- Should this also record the Δ : TyCtx and Ψ : SealCtx?
record World : Set₁ where
  constructor mkWorld
  field
    Σˡ : Store
    Σʳ : Store
    η : List SealRel
open World public

record _⪰_ (w′ w : World) : Set₁ where
  field
    growˡ : Σˡ w ⊆ˢ Σˡ w′
    growʳ : Σʳ w ⊆ˢ Σʳ w′
    growη : η w ⊆η η w′

extendWorld : World → Rel → World
extendWorld w R =
  mkWorld (Σˡ w) (Σʳ w) (ηentry (length (Σˡ w)) (length (Σʳ w)) R ∷ η w)

extendWorld-⪰ : ∀ {w} (R : Rel) → extendWorld w R ⪰ w
extendWorld-⪰ {w} R ._⪰_.growˡ = ⊆ˢ-refl
extendWorld-⪰ {w} R ._⪰_.growʳ = ⊆ˢ-refl
extendWorld-⪰ {w} R ._⪰_.growη = η-drop ⊆η-refl

--------------------------------------------------------------------------------
-- Logical relation core
--------------------------------------------------------------------------------

mutual
  -- Intended invariant:
  --   `𝒱` is meant to be used only on closed values under an empty
  --   type context. Under that intended use, the lack of a `⊑-＇` clause is
  --   deliberate. 
  𝒱 : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱 p n dir w V W = Value V × Value W × 𝒱′ p n dir w V W

  𝒱′ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱′ p zero dir w V W = Lift (lsuc 0ℓ) ⊤
  
  𝒱′ ⊑-‵ (suc n) dir w ($ (κℕ m)) ($ (κℕ m′)) = Lift (lsuc 0ℓ) (m ≡ m′)
  
  𝒱′ (⊑-⇒ pA pB) (suc n) dir w V W =
    ∀ {V′ W′} →
    𝒱 pA (suc n) dir w V′ W′ →
    ℰ pB (suc n) dir w (V · V′) (W · W′)

  𝒱′ {A = `∀ A} {B = `∀ B} (⊑-∀ p) (suc n) dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (T U : Ty) →
    ℰ p (suc n) dir (extendWorld w′ R) (V ⦂∀ A [ T ]) (W ⦂∀ B [ U ])

  𝒱′ {A = `∀ A} {B = B} (⊑-ν p) (suc n) dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) →
    ℰ p (suc n) dir (extendWorld w′ R) (V ⦂∀ A [ ｀ length (Σˡ w′) ]) W
    
  𝒱′ ⊑-★★ (suc n) dir w (V up tag G) (W up tag H) =
    Lift (lsuc 0ℓ) (G ≡ H) ×
    𝒱 (⊑-refl {A = G}) n dir w V W
    
  𝒱′ ⊑-★★ (suc n) dir w (V down seal αˡ) (W down seal αʳ) =
    Σ[ R ∈ Rel ] (η w ∋η αˡ ↔ αʳ ∶ R) × R n dir V W
    
  𝒱′ (⊑-★ {G = G} g p) (suc n) ≼ w V (W up tag H) =
    Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 p n ≼ w V W

  𝒱′ (⊑-★ {G = G} g p) (suc n) ≽ w V (W up tag H) =
    Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 p (suc n) ≽ w V W
    
  𝒱′ (⊑-｀ {α = α}) (suc n) dir w (V down seal βˡ) (W down seal βʳ) =
    Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
      (η w ∋η α ↔ α ∶ R) ×
      R (suc n) dir V W
      
  𝒱′ p (suc n) dir w V W = Lift (lsuc 0ℓ) ⊥


  -- This follows PeterLogRel.
  ℰ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  ℰ p zero dir w Mˡ Mʳ = Lift (lsuc 0ℓ) ⊤
  
  ℰ p (suc n) ≼ w Mˡ Mʳ =
    (Σ[ Σˡ′ ∈ Store ] Σ[ Mˡ′ ∈ Term ]
      (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) ×
      ℰ p n ≼ (mkWorld Σˡ′ (Σʳ w) (η w)) Mˡ′ Mʳ)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mˡ × Σ[ Σʳ′ ∈ Store ] Σ[ Wʳ ∈ Term ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) ×
      𝒱 p n ≼ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Wʳ)
      
  ℰ p (suc n) ≽ w Mˡ Mʳ =
    (Σ[ Σʳ′ ∈ Store ] Σ[ Mʳ′ ∈ Term ]
      (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) ×
      ℰ p n ≽ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Mʳ′)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mʳ × Σ[ Σˡ′ ∈ Store ] Σ[ Wˡ ∈ Term ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) ×
      𝒱 p n ≽ (mkWorld Σˡ′ (Σʳ w) (η w)) Wˡ Mʳ)

------------------------------------------------------------------------
-- Environment interpretation for open terms
------------------------------------------------------------------------

WfTyClosedᵗ : TyCtx → Ty → Set
WfTyClosedᵗ Δ A = Σ[ Ψ ∈ SealCtx ] WfTy Δ Ψ A

record RelSub (Δ : TyCtx) : Set₁ where
  field
    leftᵗ : Substᵗ
    rightᵗ : Substᵗ
    left-closed : (X : TyVar) → WfTyClosedᵗ Δ (leftᵗ X)
    right-closed : (X : TyVar) → WfTyClosedᵗ Δ (rightᵗ X)
    precᵗ : (X : TyVar) → leftᵗ X ⊑ rightᵗ X
open RelSub public

∅ρ : RelSub 0
(∅ρ .leftᵗ) = λ _ → ‵ `ℕ
(∅ρ .rightᵗ) = λ _ → ‵ `ℕ
(∅ρ .left-closed) = λ _ → 0 , wfBase
(∅ρ .right-closed) = λ _ → 0 , wfBase
(∅ρ .precᵗ) = λ _ → ⊑-‵

shift-substᵗ : (A : Ty) → substᵗ (λ X → ＇ suc X) A ≡ renameᵗ suc A
shift-substᵗ A = trans (sym (renameᵗ-substᵗ suc (λ X → ＇ X) A))
                        (cong (renameᵗ suc) (substᵗ-id A))

⇑ᵗρ : ∀ {Δ} → RelSub Δ → RelSub (suc Δ)
(⇑ᵗρ ρ .leftᵗ) = extsᵗ (leftᵗ ρ)
(⇑ᵗρ ρ .rightᵗ) = extsᵗ (rightᵗ ρ)
(⇑ᵗρ ρ .left-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .left-closed) (suc X) =
  let Ψ , wfA = left-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .right-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .right-closed) (suc X) =
  let Ψ , wfA = right-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .precᵗ) zero = ⊑-＇
(⇑ᵗρ ρ .precᵗ) (suc X) =
  cast-⊑ (shift-substᵗ (leftᵗ ρ X))
          (shift-substᵗ (rightᵗ ρ X))
          (Imprecision.substᵗ-⊑ (λ Y → ＇ suc Y) (precᵗ ρ X))

⇑ˢρ : ∀ {Δ} → RelSub Δ → RelSub Δ
(⇑ˢρ ρ .leftᵗ) = liftSubstˢ (leftᵗ ρ)
(⇑ˢρ ρ .rightᵗ) = liftSubstˢ (rightᵗ ρ)
(⇑ˢρ ρ .left-closed) X =
  let Ψ , wfA = left-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .right-closed) X =
  let Ψ , wfA = right-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .precᵗ) X = renameˢ-⊑ suc (precᵗ ρ X)

substᴿ-⊑ : ∀ {Δ} → (ρ : RelSub Δ) → ∀ {A B} → A ⊑ B → substᵗ (leftᵗ ρ) A ⊑ substᵗ (rightᵗ ρ) B
substᴿ-⊑ ρ ⊑-★★ = ⊑-★★
substᴿ-⊑ ρ (⊑-★ g p) = ⊑-★ (substᵗ-ground (rightᵗ ρ) g) (substᴿ-⊑ ρ p)
substᴿ-⊑ ρ (⊑-＇ {X}) = precᵗ ρ X
substᴿ-⊑ ρ ⊑-｀ = ⊑-｀
substᴿ-⊑ ρ ⊑-‵ = ⊑-‵
substᴿ-⊑ ρ (⊑-⇒ p q) = ⊑-⇒ (substᴿ-⊑ ρ p) (substᴿ-⊑ ρ q)
substᴿ-⊑ ρ (⊑-∀ p) = ⊑-∀ (substᴿ-⊑ (⇑ᵗρ ρ) p)
substᴿ-⊑ ρ (⊑-ν {A = A} {B = B} p) =
  ⊑-ν (cast-⊑ (substᵗ-ν-src (leftᵗ ρ) A)
               (substᵗ-⇑ˢ (rightᵗ ρ) B)
               (substᴿ-⊑ (⇑ˢρ ρ) p))

record RelEnv : Set where
  field
    leftˣ : Substˣ
    rightˣ : Substˣ
open RelEnv public

∅γ : RelEnv
(∅γ .leftˣ) x = ` x
(∅γ .rightˣ) x = ` x

⇓γ : RelEnv → RelEnv
(⇓γ γ .leftˣ) x = leftˣ γ (suc x)
(⇓γ γ .rightˣ) x = rightˣ γ (suc x)

𝒢 : PCtx → ℕ → Dir → World → RelSub 0 → RelEnv → Set₁
𝒢 [] n dir w ρ γ = Lift (lsuc 0ℓ) ⊤
𝒢 ((A , B , p) ∷ Γ) n dir w ρ γ =
  Value (leftˣ γ zero) ×
  Value (rightˣ γ zero) ×
  𝒱 (substᴿ-⊑ ρ p) n dir w (leftˣ γ zero) (rightˣ γ zero) ×
  𝒢 Γ n dir w ρ (⇓γ γ)

_∣_⊨_⊑_⦂_ : PCtx → Dir → Term → Term → ∀ {A B} → A ⊑ B → Set₁
Γ ∣ dir ⊨ M ⊑ M′ ⦂ p =
  ∀ (n : ℕ) (w : World) (ρ : RelSub 0) (γ : RelEnv) →
  𝒢 Γ n dir w ρ γ →
  ℰ (substᴿ-⊑ ρ p) n dir w
    (substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M))
    (substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′))

_⊨_⊑_⦂_ : PCtx → Term → Term → ∀ {A B} → A ⊑ B → Set₁
Γ ⊨ M ⊑ M′ ⦂ p = (Γ ∣ ≼ ⊨ M ⊑ M′ ⦂ p) × (Γ ∣ ≽ ⊨ M ⊑ M′ ⦂ p)

proj⊨ :
  ∀ {Γ M M′ A B} {p : A ⊑ B} →
  (dir : Dir) →
  Γ ⊨ M ⊑ M′ ⦂ p →
  Γ ∣ dir ⊨ M ⊑ M′ ⦂ p
proj⊨ ≼ rel = proj₁ rel
proj⊨ ≽ rel = proj₂ rel
