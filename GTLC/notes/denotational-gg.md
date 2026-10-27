# A Denotational Proof of the Dynamic Gradual Guarantee for GTLC

Status: design on paper, not mechanized.  The graph model with errors is
that of `denotational_semantics` (`Framework/GraphModel/`,
`Semantics/GraphErr/`); the cast calculus, coercions and precision are
those of `GTLC/agda/` (`CastCalculus.agda`, `Coercions.agda`).

Conventions, as in the rest of GTLC: in `A ⊑ A′` and `M ⊑ M′` the left
side is the less precise one (`★ ⊑ A`).  The relations below always
have the less precise program on the left and the more precise one on
the right.

## 1. Summary

* There is no split into a value relation and a computation relation.
  Blame is the element `ω`, and divergence is the empty set, so blame
  and convergence are cases of an element.
* There are two relations, one per direction of the guarantee, and
  each relates a whole set on one side to a single element on the
  other:

  * `d ◃ D′`: the left element `d` is justified by the right set `D′`
    (preservation: what the less precise program does, the more
    precise one does too, or it blames);
  * `D ▹ d′`: the right element `d′` is justified by the left set `D`
    (reflection: what the more precise program does, the less precise
    one does too).

  Each is defined by recursion on its element, so on the element's
  depth, as for the delay relation; the set side is quantified over
  whole sets, as `app-obs` of `ApproxLRLayer` does.
* The two directions do not refer to each other: the function clause of
  each mentions only the same direction on arguments.  So the
  fundamental lemma is two independent inductions.
* All the coercion-precision rules (`⊑ᶜ`) are sound for both relations,
  and `⊑castL` and `⊑castR` are instances of `⊑cast`, because `id`
  denotes the identity.
* The four clauses of the dynamic gradual guarantee follow from the two
  relations at the top level, with soundness and adequacy of the graph
  model for the cast calculus.  Determinacy is not needed.  The clause
  about syntactic value precision `V ⊑ᶜᵀ V′` does not come out
  directly (Section 9).

## 2. Values

The domain is the graph model's `Value` with errors:

    d ::= n | V ↦ w | ν | ω | tag G d        (V a finite list of values)

where `tag G d` is the injection of `d` into `★` at ground type `G`
(`G ::= ℕ | ★ ⇒ ★`); with the existing constructors, `tag ℕ d = left d`
and `tag (★ ⇒ ★) d = right d`.  `ν` is the empty function, which every
`Λ` contains.  A set is *a value set* when it does not contain `ω`.

Notation, for sets `D`, `E` of values:

* `⌊D⌋ = D ∖ {ω}`; `Conv D` when `⌊D⌋` is nonempty;
* `untag_G D = { d | tag G d ∈ D }`;
* `D ● E = { w | V ↦ w ∈ D, mem V ⊆ E, V ≠ [] }`  (the kernel `⋆`);
* `D ≫= F`: `ω` when `ω ∈ D`, and `F ⌊D⌋` when `Conv D`
  (`Framework/GraphModel/ErrorMonad.agda`);
* `guard X D = D` when `Conv X`, and `∅` otherwise;
* `Con D`: the elements of `D` are pairwise consistent (`~`).

## 3. Semantics of the cast calculus

Terms (`ρ` maps variables to value sets):

    ⟦ x ⟧ρ          = ρ x
    ⟦ $ n ⟧ρ        = { n }
    ⟦ ƛ A ⇒ N ⟧ρ    = Λᵐ (Y ↦ ⟦ N ⟧ρ[x ↦ Y])
    ⟦ L · M ⟧ρ      = ⟦ L ⟧ρ ≫= λ F. ⟦ M ⟧ρ ≫= λ X. F ● X
    ⟦ cast M [ c ] ⟧ρ = ⟦ M ⟧ρ ≫= ⟦ c ⟧
    ⟦ blame ⟧ρ      = { ω }

There is no check of the operator in the application, because the cast
calculus is typed; the only checks are those of projections.

Coercions, as functions on value sets `X`:

    ⟦ id A ⟧X            = X
    ⟦ G ! ⟧X             = { tag G v | v ∈ X }
    ⟦ G ?ℓ ⟧X            = untag_G X ∪ { ω | tag H v ∈ X, H ≠ G }
    ⟦ c ↦ d ⟧X           = guard X (Λᵐ (Y ↦ ⟦ c ⟧Y ≫= λ Y₁. (X ● Y₁) ≫= ⟦ d ⟧))
    ⟦ c ⨟ d ⟧X           = ⟦ c ⟧X ≫= ⟦ d ⟧
    ⟦ ⊥ A ⇨ B at ℓ ⟧X    = guard X { ω }

Recall `⊢ c ↦ d ⦂ (A ⇒ B) ⇨ (C ⇒ D)` when `⊢ c ⦂ C ⇨ A` and
`⊢ d ⦂ B ⇨ D`.  Every `⟦ c ⟧` is strict (`⟦ c ⟧∅ = ∅`), monotone,
continuous, and preserves consistency (on a consistent `X` all tags
agree, since `left x ~ right y` is false, so `⟦ G ?ℓ ⟧X` either
untags or errs, never both).

Each cast reduction holds as an equation.  For example, by `Λ-β`
(Section 6),

    ⟦ cast V [ c ↦ d ] · W ⟧ = ⟦ c ⟧⟦W⟧ ≫= λ Y₁. (⟦V⟧ ● Y₁) ≫= ⟦ d ⟧
                              = ⟦ cast (V · cast W [ c ]) [ d ] ⟧.

## 4. The relations

Both relations are indexed by a type precision `A ⊑ A′`.  Write
`G ⊑ A′` with `A′ ≠ ★` for the unique ground type below `A′`
(`ℕ ⊑ ℕ`, `★ ⇒ ★ ⊑ A₁ ⇒ A₂`).

### 4.1 Preservation, `d ◃ D′ : A ⊑ A′`, by recursion on `d`

    ω ◃ D′                 iff  ω ∈ D′
    d ◃ D′    (d ≠ ω)      iff  ω ∈ D′  or  d ◃ᵛ D′

    n ◃ᵛ D′ : ℕ ⊑ ℕ                     iff  n ∈ D′
    tag G u ◃ᵛ D′ : ★ ⊑ ★               iff  u ◃ᵛ untag_G D′ : G ⊑ G
    tag G u ◃ᵛ D′ : ★ ⊑ A′   (A′ ≠ ★)   iff  G ⊑ A′  and  u ◃ᵛ D′ : G ⊑ A′
    ν ◃ᵛ D′ : A ⇒ B ⊑ A′ ⇒ B′           iff  ν ∈ D′
    (U ↦ w) ◃ᵛ D′ : A ⇒ B ⊑ A′ ⇒ B′     iff  ν ∈ D′  and
        for every consistent value set E′,
          if  u ◃ E′ : A ⊑ A′  for every u ∈ U
          then  w ◃ (⌊D′⌋ ● E′) : B ⊑ B′
    otherwise                            false

### 4.2 Reflection, `D ▹ d′ : A ⊑ A′`, by recursion on `d′`

    D ▹ ω                  always
    D ▹ d′    (d′ ≠ ω)     iff  D ▹ᵛ d′

    D ▹ᵛ n : ℕ ⊑ ℕ                       iff  n ∈ D
    D ▹ᵛ tag G u′ : ★ ⊑ ★                iff  untag_G D ▹ᵛ u′ : G ⊑ G
    D ▹ᵛ d′ : ★ ⊑ A′        (A′ ≠ ★)     iff  untag_G D ▹ᵛ d′ : G ⊑ A′
                                              where G ⊑ A′
    D ▹ᵛ ν : A ⇒ B ⊑ A′ ⇒ B′             iff  ν ∈ D
    D ▹ᵛ (V′ ↦ w′) : A ⇒ B ⊑ A′ ⇒ B′     iff  ν ∈ D  and
        for every consistent value set E,
          if  E ▹ v′ : A ⊑ A′  for every v′ ∈ V′
          then  (⌊D⌋ ● E) ▹ w′ : B ⊑ B′
    otherwise                             false

### 4.3 Sets and environments

    D ◃ D′ : A ⊑ A′   iff  d ◃ D′ : A ⊑ A′  for every d ∈ D
    D ▹ D′ : A ⊑ A′   iff  D ▹ d′ : A ⊑ A′  for every d′ ∈ D′
    ρ ◃ ρ′ : Γ ⊑ Γ′   iff  ρ x ◃ ρ′ x : Γ(x) ⊑ Γ′(x)  for every x  (likewise ▹)

### 4.4 How the clauses carry the guarantee

* Blame only on the right: `D ▹ ω` always holds, and `d ◃ D′` holds
  for every `d` when `ω ∈ D′`.
* Blame on the left forces blame on the right: `ω ◃ D′` iff `ω ∈ D′`.
* A right value needs a left value: `D ▹ᵛ d′` asks for a membership
  in `D` (or a `ν` in `D`), never for `ω`.
* A function is related by what it does to related arguments (`●`),
  never entry by entry.  The `ν` conjunct records that the other side
  converges to a function.

## 5. Why these choices

### 5.1 Why a set on one side

Relating single elements to single elements fails at application,
because application selects an entry by its argument list.  Suppose
`a ≼ a′` and `a ≼ a″` (with `a = [1] ↦ 2`, `a′ = [1] ↦ 2`,
`a″ = [1] ↦ ω`, say), and

    D = { [a] ↦ 5 },  D′ = { [a″] ↦ 5 },  E = { a },  E′ = { a′ }.

Every element has a related partner, yet `D ● E = { 5 }` and
`D′ ● E′ = ∅`.  The relation must look at what `D′` does on the
arguments that are actually there, which needs `D′` as a set.

### 5.2 Why the set side quantifies over sets, not lists

In the application case of reflection, a right result
`w′ ∈ X′ ● Y′` comes from one entry `V′ ↦ w′ ∈ X′` with
`mem V′ ⊆ Y′`.  The function clause of `X ▹ (V′ ↦ w′)` is then used
with `E = ⌊Y⌋`, the whole left argument set; nothing finite on the left
has to be found.  Dually for preservation with `E′ = ⌊Y′⌋`.  This is
what `app-obs` of the delay relation does (`∀ E → … → Q (D ● E) W`),
and it removes the finite-approximation problem: no left list has to be
grown to match a right list.

### 5.3 Why the two directions are independent

The function clause of `◃` asks for `u ◃ E′` on the arguments, the same
direction; that of `▹` asks for `E ▹ v′`.  Precision is covariant in
the domain (`A ⇒ B ⊑ A′ ⇒ B′` needs `A ⊑ A′`), and the left and right
sides never swap, so no clause needs the other direction.  In the
`λ` case of either direction, the body is used with the bound variable
related in the same direction (Section 7), which is all that returning
the variable needs.

### 5.4 Termination

The measure is the depth of the element (`depth` in
`proof/Framework/GraphModel/DomainUtilBase.agda`):

* in `◃`, every call is on `u` (in `tag G u`), on an element of `U`, or
  on `w`, all of smaller depth;
* in `▹`, every call is on `u′`, an element of `V′`, or `w′`, of
  smaller depth, except the clause `★ ⊑ A′`, which keeps `d′` and
  moves to `G ⊑ A′`.  Unfolding that clause into its three instances
  (`d′ = n`, `ν`, `V′ ↦ w′`, with `untag_G D` inlined) removes the
  exception.

So the recursion is in fact structural.  The delay relation needed
fuel because a call of a Clos4ᵀ closure combines several pairs
(`Calls`), whose results are not sub-elements of any one pair; here
`●` uses a single entry.  In Agda the quantification "for every
`v′ ∈ V′`" goes through a mutual list relation (as `_≈_` does for
`_~_` in `Domain.agda`); if the termination checker does not accept
that, the fallback is the `ApproxLR≤` pattern: fuel, bounded by depth,
with a lemma that any bound gives the same relation.  Both relations
quantify over sets, so they live in `Set₁`.

## 6. Supporting lemmas

* *Convergence transfer.*  If `d ≠ ω` and `d ◃ᵛ D′`, then `Conv D′`.
  If `d′ ≠ ω` and `D ▹ᵛ d′`, then `Conv D`.
* *Monotonicity.*  If `d ◃ D′` and `D′ ⊆ D″`, then `d ◃ D″`.  If
  `D ▹ d′` and `D ⊆ D″`, then `D″ ▹ d′`.  Also `D ▹ᵛ d′` iff
  `⌊D⌋ ▹ᵛ d′`.
* *Λ-β.*  If `E` is a nonempty consistent value set and `F` is monotone
  and continuous, then `Λᵐ F ● E = F E`.
* *Consistency.*  If `ρ` is consistent, then `⟦ M ⟧ρ` is consistent,
  and each `⟦ c ⟧` preserves consistency.
* *Bind.*  If `D ◃ D′`, and `F X ◃ F′ X′` whenever `X ◃ X′` are
  consistent value sets, then `(D ≫= F) ◃ (D′ ≫= F′)`.  Likewise
  for `▹`.
* *Application.*  If `X ◃ X′ : A ⇒ B ⊑ A′ ⇒ B′` and `Y ◃ Y′ : A ⊑ A′`,
  with `Y′` consistent, then `(X ● Y) ◃ (X′ ● Y′) : B ⊑ B′`.  Likewise
  for `▹`.

Proof of *Application* for `◃`.  Let `w ∈ X ● Y` by `U ↦ w ∈ X`,
`mem U ⊆ Y`.  Then `(U ↦ w) ◃ X′`.  If `ω ∈ X′` this is impossible,
because `X′` is a value set.  Otherwise its function clause applies
with `E′ = Y′`, since `u ◃ Y′` for each `u ∈ U`, and gives
`w ◃ X′ ● Y′`.

Proof of *Application* for `▹`.  Let `w′ ∈ X′ ● Y′` by
`V′ ↦ w′ ∈ X′`, `mem V′ ⊆ Y′`.  Then `X ▹ (V′ ↦ w′)`, and its
function clause applies with `E = Y`, since `Y ▹ v′` for each
`v′ ∈ V′`, and gives `(X ● Y) ▹ w′`.

Proof of *Bind* for `◃`.  Let `w ∈ D ≫= F`.  If `w = ω` with
`ω ∈ D`, then `ω ∈ D′` and so `ω ∈ D′ ≫= F′`.  Otherwise `Conv D`
and `w ∈ F ⌊D⌋`.  If `ω ∈ D′`, then `ω ∈ D′ ≫= F′`.  Otherwise
`⌊D⌋ ◃ D′`, `Conv D′` by convergence transfer, and
`w ◃ F′ D′ ⊆ D′ ≫= F′`.

## 7. Fundamental lemma

**Lemma.**  If `ρ ⊑ᵉ ρ′ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′` and `ρ ◃ ρ′`
(consistent value sets), then `⟦ M ⟧ρ ◃ ⟦ M′ ⟧ρ′ : A ⊑ A′`.  Likewise
for `▹`.

By induction on the precision derivation.

### Case `x ⊑ᶜᵀ x`

By the environment relation.

### Case `$ n ⊑ᶜᵀ $ n`

`n ◃ { n }` and `{ n } ▹ n`.

### Case `ƛ A ⇒ N ⊑ᶜᵀ ƛ A′ ⇒ N′`

For `◃`: `ν` is in both.  Let `(U ↦ w) ∈ ⟦ ƛ A ⇒ N ⟧ρ`, so
`w ∈ ⟦ N ⟧ρ[x ↦ mem U]` and `U` is a nonempty list of values.  Let `E′`
be a consistent value set with `u ◃ E′` for each `u ∈ U`.  `E′` is
nonempty by convergence transfer, so by `Λ-β`

    ⟦ ƛ A′ ⇒ N′ ⟧ρ′ ● E′ = ⟦ N′ ⟧ρ′[x ↦ E′].

The environments `ρ[x ↦ mem U] ◃ ρ′[x ↦ E′]` are related, so by the
induction hypothesis `w ◃ ⟦ N′ ⟧ρ′[x ↦ E′]`.

For `▹`: dually, with `w′ ∈ ⟦ N′ ⟧ρ′[x ↦ mem V′]`, an arbitrary `E`
with `E ▹ v′` for each `v′ ∈ V′`, and `ρ[x ↦ E] ▹ ρ′[x ↦ mem V′]`.

### Case `L · M ⊑ᶜᵀ L′ · M′`

By *Bind* twice and *Application*.

### Case `cast M [ c ] ⊑ᶜᵀ cast M′ [ c′ ]`

By *Bind* and the coercion lemma (Section 8), using `⊑ᶜ→⊑` for the
precision of the target types.

### Case `cast M [ c ] ⊑ᶜᵀ M′`  (`c ⊑ᶜ id A′`)

`⟦ M′ ⟧ρ′ = ⟦ M′ ⟧ρ′ ≫= ⟦ id A′ ⟧`, so this is the previous case.

### Case `M ⊑ᶜᵀ cast M′ [ c′ ]`  (`id A ⊑ᶜ c′`)

Likewise.

### Case `M ⊑ᶜᵀ blame`

The right side is `{ ω }`: `d ◃ { ω }` for every `d`, and
`D ▹ ω` always.

## 8. Coercion lemma

Say `c ◃ c′` (at `⊢ c ⦂ A ⇨ B`, `⊢ c′ ⦂ A′ ⇨ B′`, `A ⊑ A′`,
`B ⊑ B′`) when, for all consistent value sets `X`, `X′`, if
`X ◃ X′ : A ⊑ A′` then `⟦ c ⟧X ◃ ⟦ c′ ⟧X′ : B ⊑ B′`; likewise
`c ▹ c′`.

**Lemma.**  If `c ⊑ᶜ c′`, `⊢ c ⦂ A ⇨ B` and `⊢ c′ ⦂ A′ ⇨ B′`, then
`c ◃ c′` and `c ▹ c′`.

By induction on `c ⊑ᶜ c′`.  The endpoint precisions come from `⊑ᶜ→⊑`.
In the cases below `X ◃ X′` (or `X ▹ X′`) at the source types.

### Case `id A ⊑ᶜ id A′`

Immediate.

### Case `G ! ⊑ᶜ G ! ` and case `G ?ℓ ⊑ᶜ G ?ℓ`

Both grounds are equal (`G ⊑ G′` between grounds).  For `!`, by the
clause `★ ⊑ ★`, since `untag_G (tag_G X′) = X′`.  For `?` and `◃`, a
left `v` with `tag G v ∈ X` gives `v ◃ᵛ untag_G X′ ⊆ ⟦ G ?ℓ ⟧X′`.  A
left `ω`, from `tag H v ∈ X` with `H ≠ G`, gives
`v ◃ᵛ untag_H X′`, so `untag_H X′` is nonempty by convergence transfer,
so `ω ∈ ⟦ G ?ℓ ⟧X′`.  For `?` and `▹`, a right `v′` with
`tag G v′ ∈ X′` gives `untag_G X ▹ᵛ v′`.

### Case `c ↦ d ⊑ᶜ c′ ↦ d′`

For `◃`: `ν` by convergence transfer from `X ◃ X′`.  For an entry
`(U ↦ w)`, `w ∈ ⟦ c ⟧(mem U) ≫= λ Y₁. (X ● Y₁) ≫= ⟦ d ⟧`.  Given
`E′` with `mem U ◃ E′`, by `Λ-β` the right side applied to `E′` is
`⟦ c′ ⟧E′ ≫= λ Y₁′. (X′ ● Y₁′) ≫= ⟦ d′ ⟧`.  Conclude by *Bind*, the
induction hypotheses for `c` and `d`, and *Application*.  For `▹`,
dually.

### Case `c ⨟ d ⊑ᶜ c′ ⨟ d′`

By *Bind* and the induction hypotheses (the middle types are related by
`⊑ᶜ→⊑`).

### Case `id A ⊑ᶜ c′` with `c′` one of `id B`, `G !`, `G ?ℓ`

* `c′ = G !`: then `A = ★`.  For `◃`, a left `tag H u ∈ X` has
  `tag H u ◃ X′ : ★ ⊑ G`, so `H = G` and `u ◃ᵛ X′ : G ⊑ G`, which is
  `tag G u ◃ᵛ tag_G X′ : ★ ⊑ ★`.  For `▹`, a right `tag G v′` with
  `v′ ∈ X′` has `untag_G X ▹ᵛ v′ : G ⊑ G` from `X ▹ v′ : ★ ⊑ G`.
* `c′ = G ?ℓ`: then `A = ★`.  For `◃`, a left `tag H u ∈ X` has
  `u ◃ᵛ untag_H X′`.  If `H = G`, then `u ◃ᵛ ⟦ G ?ℓ ⟧X′`.  If `H ≠ G`,
  then `untag_H X′` is nonempty, so `ω ∈ ⟦ G ?ℓ ⟧X′`: the more precise
  side blames.  For `▹`, a right `v′` with `tag G v′ ∈ X′` gives
  `untag_G X ▹ᵛ v′ : G ⊑ G`, which is `X ▹ v′ : ★ ⊑ G`.

### Case `id ★ ⊑ᶜ c′ ↦ d′` and case `id (A ⇒ B) ⊑ᶜ c′ ↦ d′`

As the case `c ↦ d ⊑ᶜ c′ ↦ d′`, with `⟦ id ⟧` on the left.  For `id ★`,
a left `tag G u` must have `G = ★ ⇒ ★` and `u ◃ᵛ X′ : ★ ⇒ ★ ⊑ A′ ⇒ B′`.

### Case `id A ⊑ᶜ c′ ⨟ d′`

`X ◃ ⟦ c′ ⟧X′`, then `X ◃ ⟦ c′ ⟧X′ ≫= ⟦ d′ ⟧`, by *Bind* with
`X = X ≫= ⟦ id A ⟧` on the left.

### Case `c ⊑ᶜ id A′` with `c` one of `id B`, `G !`, `G ?ℓ`

* `c = G !`: then `G ⊑ A′` and `A′ ≠ ★`.  For `◃`, `tag G u` with
  `u ◃ X′ : G ⊑ A′` is `tag G u ◃ X′ : ★ ⊑ A′`.  For `▹`,
  `untag_G (tag_G X) = X`.
* `c = G ?ℓ`: then `G ⊑ A′` and `A′ ≠ ★`.  For `◃`, a left `v` with
  `tag G v ∈ X` gives `v ◃ X′ : G ⊑ A′`.  A left `ω`, from
  `tag H v ∈ X` with `H ≠ G`, cannot occur: `tag H v ◃ X′ : ★ ⊑ A′`
  with `X′` a value set gives `H ⊑ A′`, and the ground below `A′` is
  unique, so `H = G`.  For `▹`, `X ▹ v′ : ★ ⊑ A′` is
  `untag_G X ▹ᵛ v′ ⊆ ⟦ G ?ℓ ⟧X`.

### Case `c ↦ d ⊑ᶜ id (A′ ⇒ B′)` and case `c ⨟ d ⊑ᶜ id A′`

Mirror images of the `id`-on-the-left cases.

### Case `(★ ⇒ ★) ?ℓ ⨟ c ⊑ᶜ c′`  and case `c ⨟ (★ ⇒ ★) ! ⊑ᶜ c′`

`⟦ c′ ⟧ = ⟦ id ⨟ c′ ⟧`, so these are `⨟` with
`(★ ⇒ ★) ?ℓ ⊑ᶜ id A′` (resp. `(★ ⇒ ★) ! ⊑ᶜ id`), which are cases
above.

### Case `c ⊑ᶜ ⊥ A′ ⇨ B′ at ℓ`

For `◃`: if `X` is empty, `⟦ c ⟧X = ∅` by strictness.  Otherwise
`Conv X′` by convergence transfer, so `ω ∈ ⟦ ⊥ ⟧X′`, and every left
element is justified.  For `▹`: the only right element is `ω`.

## 9. The dynamic gradual guarantee

Let `M ⊑ᵀ M′` be closed GTLC programs, and let `D` and `D′` be the
denotations of their compilations.  `compile` preserves precision
(`proof/CompileMeta.agda`), so the fundamental lemma gives `D ◃ D′` and
`D ▹ D′`.  Soundness of the denotation for reduction gives

* if `compile M —↠ V`, then `⌊D⌋` is nonempty;
* if `compile M —↠ blame`, then `ω ∈ D`;

and adequacy gives the converses.  With type safety:

1. If `M′ ⇓ V′`, then `D′` has a value `d′`; `D ▹ᵛ d′` gives `Conv D`,
   so `M ⇓ V`.
2. If `M′` diverges, then `D′` is empty.  A value `d ∈ D` would give
   `ω ∈ D′` or `Conv D′`; `ω ∈ D` would give `ω ∈ D′`.  So `D` is
   empty and `M` diverges.
3. If `M ⇓ V`, then `D` has a value `d`, and `d ◃ D′` gives `ω ∈ D′`
   (`M′` blames) or `Conv D′` (`M′ ⇓ V′`).
4. If `M` diverges, then `D` is empty.  If `M′ ⇓ V′`, clause 1 would
   make `D` nonempty.  So `M′` diverges or blames.

Determinacy (that no denotation holds both `ω` and a value) is never
used.

**What changes in the statement.**  Clauses 1 and 3 of
`dynamic-gradual-guarantee` also promise syntactic precision
`[]⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′` between the final values.  The denotational
proof gives instead that the denotations of `V` and `V′` are related,
and, at type `ℕ`, that they are the same numeral.  Keeping the
syntactic clause would need an operational argument, which defeats the
purpose.

Decision: the theorem is restated in observational form.  The
observation of a value forgets injections and function wrappers:

    observe ($ n)            = nat n
    observe (ƛ A ⇒ N)        = fun
    observe (cast V [ G ! ]) = observe V
    observe (cast V [ c ↦ d ]) = fun

and clauses 1 and 3 promise `observe V ≡ observe V′` in place of
`V ⊑ᶜᵀ V′`.  This follows from the relations: on elements, `obs n =
nat n`, `obs (tag G u) = obs u`, `obs ν = obs (U ↦ w) = fun`; a match
under `◃ᵛ` or `▹ᵛ` has the same `obs`; and adequacy produces a value
`V` whose `observe` is the `obs` of the element it was produced from.

## 10. Example

Less precise and more precise programs (`ℓ` the blame label of the
inner application):

    M  = (λx:★. (λy:★. y) x) 5
    M′ = (λx:★. (λy:ℕ ⇒ ℕ. y) x) 5

`M ⊑ᵀ M′` because `★ ⊑ ℕ ⇒ ℕ`.  Compiling the inner applications:

    left:   (λy:★. y) · cast x [ id ★ ]
    right:  (λy:ℕ ⇒ ℕ. y) · cast x [ (★ ⇒ ★) ?ℓ ⨟ (ℕ ! ↦ ℕ ?ℓ) ]

and the coercions are related by
`id ★ ⊑ᶜ (★ ⇒ ★) ?ℓ ⨟ (ℕ ! ↦ ℕ ?ℓ)` (`id` on the left of `⨟`, of a
projection, and of `↦`).  With `x` bound to `{ tag ℕ 5 }` on both sides:

    ⟦ (★ ⇒ ★) ?ℓ ⟧{ tag ℕ 5 } = { ω }

so `D = { tag ℕ 5 }` and `D′ = { ω }`.  `tag ℕ 5 ◃ { ω } : ★ ⊑ ℕ ⇒ ℕ`
holds by `ω ∈ D′`, which is the case `id ★ ⊑ᶜ G ?ℓ` with `H ≠ G`.
`D ▹ D′` holds because `D′` has only `ω`.  So `M` returns and `M′`
blames, as clause 3 allows.

Replacing `5` by `λz:★. z` (tagged into `★`) makes the projection
succeed.  The right result is then a function at `ℕ ⇒ ℕ` with entries
`[n] ↦ n`, and `D ▹ ([n] ↦ n) : ★ ⊑ ℕ ⇒ ℕ` unfolds to: for every
consistent `E` with `tag ℕ n ∈ E`,
`(untag_{★⇒★} D ● E) ▹ n : ★ ⊑ ℕ`, that is,
`tag ℕ n ∈ untag_{★⇒★} D ● E`, which holds because the left function
is the identity.

## 11. What remains, and what goes away

To build:

1. the semantics of Section 3, with strictness, monotonicity,
   continuity and consistency;
2. the relations and the lemmas of Section 6;
3. the coercion lemma (15 rules, two directions);
4. the fundamental lemma (8 rules, two directions);
5. soundness and adequacy of the semantics for the cast calculus's
   reduction (`CastCalculus.agda`); this is the largest new piece, by
   analogy with the adequacy proofs of `denotational_semantics`;
6. the final assembly of Section 9.

What has no counterpart: the simulation (`sim*`), the catch-up lemmas
(`cast-value-catchup`, `blame-right-catchup`), and the separate
arguments for the divergence clauses in
`proof/DynamicGradualGuarantee.agda` and
`proof/DynamicGradualGuaranteeCore.agda`.

## 12. Open questions

* Decided: the value clauses are observational (Section 9).
* Decided: the mechanization lives under `GTLC/agda/`, with the parts
  of the graph model it needs (the domain, sets as predicates, the
  error monad, `Λ`, `⋆`) copied from `denotational_semantics` and
  specialized to GTLC's values.
* Transitivity of `◃` and `▹` along a chain of three programs is not
  needed for the guarantee and is not obvious: the function clause does
  not name an intermediate argument set.
