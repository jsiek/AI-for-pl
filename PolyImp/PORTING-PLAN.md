# PolyImp Port Plan (PolyCast style + Imprecision)

This task has been completed.

## Goal
Port the PolyCast development shape into `PolyImp`, but completely replace coercions with imprecision.

There is already a development with imprecision in PolyBlameI, but
that had subtle problems that prevented us from proving type safety.
We were able to prove type safety in PolyCast, so we want to stay
close to that design.

## What is Imprecision

Imprecision can be viewed as a subset of coercion. 
Imprecision only allows casts up to `★` whereas coercions allow casts both up to `★` and down to `★`.

To enable casts down to `★`, cast `__⊢_↣_` has a down constructor that says to interpret
the imprecision in reverse.
Instead of the term cast constructor `_⟨_⟩`, cast through `_at_` with two parameters, the subterm
and the cast  `_⊢_↣_`.

## Constraints from design
1. No coercion judgment (`_⊢_⇨_`) in PolyImp.
2. No term cast constructor `_⟨_⟩`.
3. Terms cast through `_at_` and cast  `_⊢_↣_`.
4. `_⊢_↣_` has exactly two constructors: `up` and `down`, each carrying an imprecision witness `_⊢_⊑_`.
5. Imprecision has a single tag constructor to `★` (`tag`) that takes a ground type and a blame label, 
   with no project/inject pair.
6. No separate coercion-reduction relation is needed for term reduction.

## Execution plan
1. To obtain the implementation of imprecision in Imprecision.agda, take the _⊢_⇨_ of PolyCast/Coercions.agda
   and remove projection _`?_ and generalization 𝒢. Rename injection _! to tag that takes a ground type and a blame label.
   Rename ℐ to ν_. 
2. Create a correspondence between coercions and imprecision constructors to help you with the porting process.
   Write down this correspondence in the Development Notes section below.
3. Port over the the renaming and substitution operations on coercions (from Coercions.agda) to imprecision.
   You do not need to port over coercion reduction, as we do not need imprecision reduction.
   This should be straightforward because imprecision is a subset of coercion.
4. Port over the term definitions, renaming, and substitution from PolyCast.agda over to create PolyImp.agda,
   replacing the term cast constructor `_⟨_⟩` with cast through `_at_` with two parameters, the subterm
   and the cast  `_⊢_↣_`.
5. Port the file from PolyCast/TermSubst.agda to a new file PolyImp/TermSubst.agda, using the
   correspondence below to adapt each reduction rule involving coercions to up/down imprecision.
6. Port the file from PolyCast/Reduction.agda to a new file PolyImp/Reduction.agda, using the
   correspondence below to adapt each reduction rule involving coercions to up/down imprecision.
7. Port the file from PolyCast/Progress.agda to a new file PolyImp/Progress.agda, updating to replace
   any coercion-related things with imprecision.
8. Port the file from PolyCast/Eval.agda to a new file PolyImp/Eval.agda, updating to replace
   any coercion-related things with imprecision.
9. Port the file from PolyCast/Examples.agda to a new file PolyImp/Examples.agda, updating to replace
   any coercion-related things with imprecision using the
   correspondence below to adapt coercions to up/down imprecision.

## Implemented
- Step 1 complete:
  - Added `Imprecision.agda` with intrinsically typed imprecision witnesses (`_⊢_⊑_`, `_⊢_⊑ᵃ_`) in the PolyCast shape.
  - Removed projection (`_`?`) and generalization (`𝒢`) from the ported structure.
  - Replaced injection (`_!`) with `tag : Ground G → Label → _⊢ G ⊑ᵃ ★`.
  - Renamed polymorphic instantiation constructor from `ℐ` to `ν_`.
  - Kept this step scoped to syntax/composition (`id`, `_；_`, `_⨟_`) and transport helper (`castᵖ`), deferring renaming/substitution to step 3.
- Step 2 complete:
  - Added a coercion→imprecision constructor correspondence in Development Notes.
- Step 3 complete:
  - Ported coercion renaming/substitution operations into `Imprecision.agda` for imprecision witnesses:
    - Type-variable renaming/substitution: `renameAtomᵖᵗ`, `renameᵖᵗ`, `substAtomᵖᵗ`, `substᵖᵗ`, `_[_]ᵖᵗ`.
    - Seal renaming: `renameAtomᵖˢ`, `renameᵖˢ`.
  - Adapted all cases to the imprecision constructor set (`tag`, `` `⊥ ``, `seal`, `_↦_`, `∀ᵖ`, `ν_`), with no projection/generalization cases.
  - Kept the port scoped to renaming/substitution only; no coercion/imprecision reduction relation was added.
- Step 4 complete:
  - Added `PolyImp.agda` by porting term syntax and term renaming/substitution from `PolyCast/PolyCast.agda`.
  - Replaced term cast constructor `_⟨_⟩` with `_at_`, using cast judgment `_∣_∣_⊢_↣_`.
  - Added cast constructors `up_` and `down_`, each carrying an imprecision witness (`_⊢_⊑_`), matching the PolyImp design constraints.
  - Ported cast renaming/substitution transport (`renameᵗ↣`, `substᵗ↣`, `renameˢ↣`) and updated term traversals (`renameᵗ-term`, `substᵗ-term`, `renameˢ-term`) to use imprecision operations (`renameᵖᵗ`, `substᵖᵗ`, `renameᵖˢ`).
- Step 5 complete:
  - Added `TermSubst.agda` by porting `PolyCast/TermSubst.agda` into PolyImp style.
  - Replaced coercion weakening with imprecision/cast weakening:
    - `wkΣᶜᵃ`/`wkΣᶜ` ↦ `wkΣᵖᵃ`/`wkΣᵖ`.
    - Added `wkΣ↣` for up/down casts.
  - Updated all term cases from `_⟨_⟩` to `_at_` and removed coercion imports.
- Step 6 complete:
  - Added `Reduction.agda` by porting dynamic semantics from `PolyCast/Reduction.agda` to PolyImp.
  - Replaced coercion-based value/reduction forms with up/down imprecision forms:
    - Value constructors for `tag`, `seal`, `↦`, `∀ᵖ`, and `ν` through `up`/`down`.
    - Cast reduction rules for `id`, `⊥`, composition (`_；_`), and compatibility (`ξ-at`).
    - Adapted function/polymorphic cast β-rules to up/down forms (`β-at-up-↦`, `β-at-down-↦`, `β-at-up-∀`, `β-at-down-∀`, `β-at-up-ν`, `β-at-down-ν`).
  - Kept multi-step reduction and store-growth/uniqueness lemmas in PolyCast structure.
- Step 7 complete:
  - Added `Progress.agda` by porting `PolyCast/Progress.agda`.
  - Reworked canonical forms and progress analysis for up/down casts:
    - Function, polymorphic, star, and seal canonical views now use PolyImp value constructors.
    - Cast progress case now branches on `up`/`down` and imprecision constructors instead of coercions.
- Step 8 complete:
  - Added `Eval.agda` by porting `PolyCast/Eval.agda` with PolyImp imports.
  - Fuel-bounded evaluator remains unchanged in structure, now driving PolyImp reduction/progress.
- Step 9 complete:
  - Added `Examples.agda` by porting `PolyCast/Examples.agda` to PolyImp cast forms.
  - Replaced coercion casts with `_at_` + `up/down` over `tag`/`id`.
  - Kept the example suite shape and test style; adapted the old `ℐ`-specific example to a PolyImp-valid equivalent.


## Agda check
Run:
- `for f in PolyImp/*.agda; do agda -i PolyImp "$f"; done`

Result:
- All files in `PolyImp/*.agda` typecheck.

## Difficulties and postulates

- In `Reduction.agda`, opening a down-`ν` cast at term-level type application required a bridge from
  `((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ)`-indexed witness to a `Σ`-indexed witness:
  `Σ ⊢ (A [ ｀ α ]ᵗ) ⊑ B`.
- This is now resolved without postulates:
  - `openν` is implemented constructively in `Reduction.agda` via:
    - seal-renaming with `singleSealEnv` (PolyCast-style opening step), and
    - a structural strengthening pass that removes exactly the extra `★` store entry while preserving typing.


## Development Notes

### Coercion to imprecision correspondence

Judgment correspondence:
- `_⊢_⇨_` (coercions) ↦ `_⊢_⊑_` (imprecision).
- `_⊢_⇨ᵃ_` (atomic coercions) ↦ `_⊢_⊑ᵃ_` (atomic imprecision).

These two tables record how `PolyCast/Coercions.agda` constructors map
to `PolyImp/Imprecision.agda` depending on whether the imprecision
is inside the up or down constructor of cast `_⊢_↣_`.

#### Up correspondence

| PolyCast coercion constructor | PolyImp imprecision constructor | Status/notes |
| --- | --- | --- |
| `id` (in `_⊢_⇨_`) | `id` (in `_⊢_⊑_`) | unchanged shape |
| `_；_` (in `_⊢_⇨_`) | `_；_` (in `_⊢_⊑_`) | unchanged shape |
| `_⨟_` | `_⨟_` | unchanged definition pattern |
| `_!` | `tag` | renamed and now explicitly takes a `Label` (`Ground G → Label → _⊢ G ⊑ᵃ ★`) |
| `` `⊥ `` | `` `⊥ `` | unchanged (blame/failed cast ) |
| `_⁺` | `seal` | renamed (`seal : Σ ∋ˢ α ⦂ A → Σ ⊢ ｀ α ⊑ᵃ wkTy0 A`) |
| `_↦_` | `_↦_` | unchanged variance/shape |
| `∀ᶜ` | `∀ᵖ` | same role, renamed to fit imprecision naming |
| `ℐ` | `ν_` | renamed per plan |
| `_`?` | (none) | removed (no projection in imprecision) |
| `𝒢` | (none) | removed (no generalization constructor in imprecision) |
| `_⁻` | (none) | removed from imprecision; recovered via down interpretation of `seal` |


#### Down correspondence (Imprecision in reverse)

This table records how coercions correspond when the imprecision witness
is interpreted as a down cast. Note that imprecision source and target
types are reversed for the down interpretation.

| PolyCast coercion constructor | PolyImp imprecision constructor | Status/notes |
| --- | --- | --- |
| `id` (in `_⊢_⇨_`) | `id` (in `_⊢_⊑_`) | unchanged shape |
| `_；_` (in `_⊢_⇨_`) | `_；_` (in `_⊢_⊑_`) | unchanged shape |
| `_⨟_` | `_⨟_` | unchanged definition pattern |
| `_`?` | `tag` | projection corresponds to `tag` under down interpretation |
| `` `⊥ `` | `` `⊥ `` | unchanged (blame/failed cast) |
| `_⁻` | `seal` | unsealing corresponds to `seal` under down interpretation |
| `_↦_` | `_↦_` | unchanged variance/shape |
| `∀ᶜ` | `∀ᵖ` | same role, renamed to fit imprecision naming |
| `𝒢` | `ν_` | `ν_` corresponds to coercion generalization in the down interpretation |
| `_!` | (none) | up-only correspondence (captured in the first table) |
| `ℐ` | (none) | up-only correspondence (captured in the first table) |
