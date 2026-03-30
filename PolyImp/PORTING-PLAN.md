# PolyImp Port Plan (PolyCast style + Imprecision)

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
5. Stop and report what was implemented and what blockers were encountered if any.
   After that we'll formulate a plan for porting the rest of PolyCast.

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


## Agda check
Run:
- `for f in PolyImp/*.agda; do agda -i PolyImp "$f"; done`

Result:
- All files in `PolyImp/*.agda` typecheck.

## Difficulties and postulates



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
