# The dynamic gradual guarantee for GTSFImp by a logical relation

Status: started.  The syntactic layer is carried over and checked; the
relation is not yet designed in detail.

## 1. Goal and route

* **Goal.**  The dynamic gradual guarantee for GTSFImp's cast calculus.
  If closed programs `M ⊑ M′` (`M` more precise), then:
  * if `M` reduces to a value, `M′` reduces to a less precise value;
  * if `M` diverges, `M′` diverges;
  * if `M′` reduces to a value, `M` reduces to a more precise value or
    to `blame`;
  * if `M′` diverges, `M` diverges or reduces to `blame`.
* **Route: option (B)** of `notes/denotational-dgg.md`, Section 8c.
  * A binary, step-indexed, Kripke logical relation on the reduction
    semantics, in the style of New, Jamner and Ahmed's proof of
    graduality and parametricity for PolyGν
    (`papers/new2020-graduality-and-parametricity.pdf`).
  * The guarantee is the relation's fundamental lemma, read at closed
    programs.
* **Why not the denotational route.**  `notes/denotational-dgg.md`,
  Sections 8c–8f, on branch `gtsfimp-denotational` (PR #215):
  * soundness as subject expansion fails for `β-∀` (exact seal counts,
    then identity casts at `∀` types);
  * the repair, option (A), needs two term–denotation relations, one of
    them step-indexed, on top of the denotational guarantee relation;
  * (B) needs one relation.

## 2. Carried over from the denotational branch

The syntactic layer (step 1 of the old plan) is independent of the
denotation.  It moved from `Denot/` to `LR/`, unchanged except for
module names and charters.

| file | content |
|---|---|
| `LR/Precision.agda`, `proof/LR/Precision.agda` | two-context type precision `Φ ⊢ A ⊑ B`, contained in `Imprecision` |
| `LR/EagerCast.agda`, `proof/LR/EagerCast.agda`, `proof/LR/SwapRename.agda` | the eager normal form of casts and `eager` |
| `LR/CastPrecision.agda` | cast-calculus term precision, the relation of the fundamental lemma |
| `LR/Elaborate.agda`, `proof/LR/Elaboration.agda` | eager elaboration, and the theorem that it preserves precision |
| `LR/Meta.agda` | the public statements |

`notes/denotational-dgg.md` is copied unchanged as the record of the
design work.  Its section numbers are cited here and in the charters.

* **Two-context precision.**  The single-context `Imprecision` relates
  `X ⊑ X` for every variable, which admits the `Catchup` counterexample
  (`notes/denotational-dgg.md`, Section 8, risk 4).  The same problem
  would affect any relation that pairs left and right variables.
* **The eager normal form.**  Without it the left program can
  instantiate a paired variable before the right one does
  (`notes/denotational-dgg.md`, Section 8a, case 8).  This is about
  reduction, not about the denotation, so (B) needs it too.

## 3. What transfers from the denotational design

* **Which side creates seals** (Section 3).
  * Shared type applications create a store variable on both sides.
  * A left-only `Λ` or a left `inst` creates a left-only one.
  * A right `inst` while the left stays `∀` creates a right-only one,
    which never reaches the boundary.
* **Leaf relations and tag relations** (Section 4).
  * The relation for a variable's contents belongs in a Reynolds
    environment.
  * The relation for values *tagged* with a variable at `★` belongs in
    the world.
  * Section 8b shows that keeping the contents relation in the world
    makes the world-change lemma false.
* **The `∀` clauses** (Section 5): `∀⊑∀`, `∀⊑` and `∀⊑★`, each choosing
  a tag relation existentially.
* **Paper checks of the new cases** (Section 6): left-only `Λ`, `gen`
  under a left-only type application, and a right `inst` while the left
  stays `∀`.
* **Cast monotonicity** (Section 8a): related values cast at related
  types are related.  In (B) this is the compatibility lemma for casts.
* **The world-change lemma** (Section 8b).

The step-indexed setting changes how the relations are *defined*:

* by the step index and the type, not by recursion on denotational
  values;
* with a later modality wherever a value is used after a step.

It does not change which seals are paired or which relation each one
carries.

## 4. Plan

1. **Design on paper.**
   * Worlds: the step index, the two store sizes, and the variable
     correspondences with their tag relations.
   * The value and expression relations.  As in New–Jamner–Ahmed,
     there are two expression relations, one counting steps on each
     side, because the guarantee is asymmetric in blame and divergence.
   * Check them against the cases of Section 3 above.
2. **Mechanize the worlds and the relations**, with monotonicity
   (Kripke and downward closure in the index).
3. **Compatibility lemmas:**
   * application, type application, primitives;
   * conversions (reveals and conceals);
   * casts (cast monotonicity, Section 8a);
   * the world-change lemma (Section 8b).
4. **The fundamental lemma** for `LR.CastPrecision`.
5. **The dynamic gradual guarantee**, via `elaboration-preserves-precision`
   (`LR/Meta.agda`).

## 5. Open points

* **The `inst` variable.**  It is read as `★`: reduction substitutes
  `★` for it in the cast.  Does it need a world entry at all, or only
  a leaf relation?
* **Blame on the left.**  The left may blame where the right does not.
  This is the asymmetry the two expression relations encode.
* **Mixed indexing.**  Section 8a's monotonicity argument was by
  induction on the cast.  In the step-indexed setting the induction is
  on the cast, nested inside the step index.
