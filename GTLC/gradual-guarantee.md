# Dynamic Gradual Guarantee for GTLC, informally

## Conventions

Diagrams use:

  * vertical edges   = reduction
  * horizontal edges = precision
  * left             = less precise
  * right            = more precise

So the basic square always looks like:

          M  <=  M'
          |      |
          v      v
          N  <=  N'


This file translates the proof into a readable proof sketch.

  * lemmas are named explicitly
  * minor lemmas are left unnamed
  * rule names / constructor names are omitted


## Precision Relations

### 1. Type precision

      ★ ⊑ A
    
      ℕ ⊑ ℕ
    
      A ⊑ A'      B ⊑ B'
      -------------------
      A ⇒ B ⊑ A' ⇒ B'



### 2. Surface-term precision

      x ⊑ᵀ x
    
      $ n ⊑ᵀ $ n
    
      A ⊑ A'      N ⊑ᵀ N'
      ---------------------
      (ƛ x:A. N) ⊑ᵀ (ƛ x:A'. N')
    
      L ⊑ᵀ L'      M ⊑ᵀ M'
      ----------------------
      L ·[ℓ] M ⊑ᵀ L' ·[ℓ] M'



### 3. Coercion precision

Coercion precision compares explicit casts after compilation.

      id A  <=  id A'
      G !   <=  G' !
      G ?ℓ  <=  G' ?ℓ
      c ↦ d <=  c' ↦ d'
      c ; d <=  c' ; d'


plus the important cases where identity can stand in for less dynamic behavior:

      Atomic c
      ⊢ c : B ⇨ C
      A ⊑ B
      A ⊑ C
      ----------------
      id A <= c
    
      id A <= c      id B <= d
      -------------------------
      id (A ⇒ B) <= c ↦ d
    
      id ★ <= c      id ★ <= d
      -------------------------
      id ★ <= c ↦ d
    
      id A <= c      id A <= d
      -------------------------
      id A <= c ; d


and the corresponding cases on the right:

      Atomic c
      ⊢ c : B ⇨ C
      B ⊑ A
      C ⊑ A
      ----------------
      c <= id A
    
      c <= id A      d <= id B
      -------------------------
      c ↦ d <= id (A ⇒ B)
    
      c <= id A      d <= id A
      -------------------------
      c ; d <= id A


plus the two "drop function tag boundary" cases:

      c' <= c
      -------------------------
      ((★⇒★ ?ℓ) ; c') <= c
    
      c' <= c
      -------------------------
      (c' ; (★⇒★ !)) <= c


The point of these extra cases is that precision is not just shape-by-shape.
It also records that a more precise term may avoid some dynamic checks or tags.


### 4. Cast-term precision

This is the precision relation used by simulation.

      x <= x
    
      $ n <= $ n
    
      A ⊑ A'      N <= N'
      ---------------------
      ƛ x:A. N <= ƛ x:A'. N'
    
      L <= L'      M <= M'
      ----------------------
      L · M <= L' · M'
    
      M <= M'      c <= c'
      ----------------------
      cast M [ c ] <= cast M' [ c' ]
    
      M <= M'      c <= id
      ---------------------
      cast M [ c ] <= M'
    
      M <= M'      id <= c'
      ----------------------
      M <= cast M' [ c' ]
    
      M : A        A ⊑ A'
      --------------------
      M <= blame



### 5. Compilation preserves precision

Lemma: `compile-precision`

  If `M ⊑ᵀ M'`, then `compile M <= compile M'`.

Proof shape:

  induction on the source precision derivation


## Substitution / beta infrastructure

### 6. Precision is preserved by substitution

Lemma: `substᶜ-⊑`

  if related substitutions are plugged into related terms,
  the results stay related.

Closed corollary used in beta steps:

Lemma: `[]ᶜ-⊑`

          body[V/x]   <=   body'[V'/x]


Proof shape:

  induction on the precision derivation for the body


## Cast-moving lemmas used by simulation

### 7. Casting on the left against an identity target

Lemma: `cast-left-id-val`

  If `V <= V'` and `c <= id`, 
  then `cast V [ c ] -->* V2` and `V2 <= V'`.

Diagram:

          cast V[c]   <=   V'
             |
             | *
             v
             V2       <=   V'


Proof shape:

  induction on the derivation of `c <= id`

### Case 1. `id A0 <= id A'`

The left cast reduces by `β-id`.

Diagram:

          cast V[id A0]   <=   V'
             |
             | 1
             v
             V            <=   V'


### Case 2. `G ! <= id`

Diagram:

          cast V[G!]   <=   V'
             |
             | 0
             v
          cast V[G!]   <=   V'


### Case 3. `G ?ℓ <= id`

By inversion of `V <= cast V' [ G ! ]`, choose `W` such that

  `V = cast W [ G ! ]`
  `W <= V'`

Diagram:

          cast (cast W[G!]) [G ?ℓ]
                    |
                    | 1
                    v
                    W        <=   V'


### Case 4. `c1 ↦ d1 <= id`

Diagram:

          cast V[c1↦d1]   <=   V'
               |
               | 0
               v
          cast V[c1↦d1]   <=   V'


### Case 5. `c1 ; d1 <= id`

Use the induction hypothesis on `c1`, then again on `d1`, and connect the two
reduction sequences with `cast-seq-lift`.

Diagram:

          cast V[c1;d1]   <=   V'
               |
               | *
               |   induction hypothesis on c1,
               |   lifted through d1
               v
          cast V1[d1]     <=   V'
               |
               | *
               |   induction hypothesis on d1
               v
               V2         <=   V'


### Case 6. `(★⇒★ ?ℓ) ; d1 <= id`

First apply `proj-?-less-ground`, then continue with the induction hypothesis
on `d1`.

Diagram:

          cast V[(★⇒★ ?ℓ);d1]   <=   V'
                  |
                  | *
                  |   proj-?-less-ground on V <= V',
                  |   lifted through d1
                  v
          cast W[d1]            <=   V'
                  |
                  | *
                  |   induction hypothesis on d1
                  v
                  V2            <=   V'


### Case 7. `d1 ; (★⇒★ !) <= id`

Use the induction hypothesis on `d1`, then rebuild the outer injection.

Diagram:

          cast V[d1;(★⇒★ !)]   <=   V'
                 |
                 | *
                 |   induction hypothesis on d1, lifted through (★⇒★ !)
                 v
          cast V1[(★⇒★ !)]     <=   V'



### 8. Casting on the left against a function-cast target

Lemma: `cast-left-↦-val`

  If `V <= V'` and `c <= (c1 ↦ c2)`, 
  then `cast V [ c ] -->* V2` and `V2 <= cast V' [ c1 ↦ c2 ]`.

Diagram:

          cast V[c]   <=   cast V'[c1 ↦ c2]
             |
             | *
             v
             V2       <=   cast V'[c1 ↦ c2]


Proof shape:

  induction on the derivation of `c <= (c1 ↦ c2)`

### Case 1. `d1 ↦ d2 <= c1 ↦ c2`

Both sides already have function casts, so no reduction is needed.

Diagram:

          cast V[d1↦d2]   <=   cast V'[c1↦c2]
               |
               | 0
               v
          cast V[d1↦d2]   <=   cast V'[c1↦c2]


### Case 2. `id A0 <= c1 ↦ c2`

The left cast reduces by `β-id`.

Diagram:

          cast V[id A0]    <=   cast V'[c1↦c2]
               |
               | 1
               v
               V           <=   cast V'[c1↦c2]


### Case 3. `(★⇒★ ?ℓ) ; d <= c1 ↦ c2`

First apply `proj-?-less-ground`, then continue by induction on `d`.

Diagram:

          cast V[(★⇒★ ?ℓ);d]   <=   cast V'[c1↦c2]
                  |
                  | *
                  |   proj-?-less-ground on V <= V',
                  |   lifted through d
                  v
          cast W[d]            <=   cast V'[c1↦c2]
                  |
                  | *
                  |   induction hypothesis on d <= c1↦c2
                  v
                  V2           <=   cast V'[c1↦c2]


### Case 4. `d ; (★⇒★ !) <= c1 ↦ c2`

Use the induction hypothesis on `d`, then rebuild the outer injection.

Diagram:

          cast V[d;(★⇒★ !)]   <=   cast V'[c1↦c2]
                 |
                 | *
                 |   induction hypothesis on d <= c1↦c2,
                 |   lifted through (★⇒★ !)
                 v
          cast V1[(★⇒★ !)]    <=   cast V'[c1↦c2]



### 9. Casting on the left against a sequence target

Lemma: `cast-left-⨟-val`

  If `V <= V'` and `d <= c' ; d'`, 
  then `cast V [ d ] -->* N2` and `N2 <= cast (cast V' [ c' ]) [ d' ]`.

Diagram:

          cast V[d]   <=   cast (cast V'[c']) [d']
             |
             | *
             v
             N2       <=   cast (cast V'[c']) [d']


Proof shape:

  induction on the derivation of `d <= c' ; d'`

### Case 1. `d <= c' ; d'`

If the precision proof already gives `d <= c' ; d'` without exposing internal
structure, then we keep the left cast as-is and conclude directly.

Diagram:

          cast V[d]   <=   cast (cast V'[c']) [d']
             |
             | 0
             v
          cast V[d]   <=   cast (cast V'[c']) [d']


### Case 2. `d1 ; d2 <= c' ; d'`

Expose the sequence on the left with one reduction step, then apply precision
componentwise.

Diagram:

          cast V[d1;d2]   <=   cast (cast V'[c']) [d']
               |
               | 1
               v
          cast (cast V[d1]) [d2]   <=   cast (cast V'[c']) [d']


### Case 3. `(★⇒★ ?ℓ) ; d1 <= c' ; d'`

First use `cast-left-id-val` to justify the projection to a function, then use
the induction hypothesis on `d1`.

Diagram:

          cast V[(★⇒★ ?ℓ);d1]   <=   cast (cast V'[c']) [d']
                  |
                  | *
                  |   cast-left-id-val on V <= V',
                  |   lifted through d1
                  v
          cast V2[d1]           <=   cast (cast V'[c']) [d']
                  |
                  | *
                  |   induction hypothesis on d1 <= c' ; d'
                  v
                  N2            <=   cast (cast V'[c']) [d']


### Case 4. `d1 ; (★⇒★ !) <= c' ; d'`

Use the induction hypothesis on `d1`, then rebuild the final injection.

Diagram:

          cast V[d1;(★⇒★ !)]   <=   cast (cast V'[c']) [d']
                 |
                 | *
                 |   induction hypothesis on d1 <= c' ; d',
                 |   lifted through (★⇒★ !)
                 v
          cast N2[(★⇒★ !)]     <=   cast (cast V'[c']) [d']



### 10. Casting on the left against a projection target (Crux!)

Lemma: `cast-left-?-val`

  If `V <= cast V' [ A' ! ]` and `c <= A' ?ℓ`
  then `cast V [ c ] -->* N` and `N <= V'`.

Diagram:

          cast V[c]                  <=  cast (cast V'[A'!]) [A'?]
          |                              |
          | *                            | 1
          v                              v
          N                          <=  V'


Proof shape:

  induction on the derivation of `c <= A' ?ℓ`

### Case 1. `A' ?ℓ <= A' ?ℓ`

By inversion of `V <= cast V' [ A' ! ]`, choose `W` such that

  `V = cast W [ A' ! ]`
  `W <= V'`

Diagram:

          cast (cast W[A'!]) [A' ?ℓ]   <=   cast (cast V'[A'!]) [A' ?ℓ]
                      |                                  |
                      | 1                                | 1
                      v                                  v
                      W                              <=  V'


The crucial step uses the dynamic-shape inversion lemmas for injections.

### Case 2. `id <= A' ?ℓ`

By inversion of `V <= cast V' [ A' ! ]`, choose `W` such that

  `V = cast W [ A' ! ]`
  `W <= V'`

Diagram:

          cast (cast W[A'!]) [id]
                    |
                    | 1
                    v
              cast W[A'!]        <=   V'


### Case 3. `d ; (★⇒★ !) <= A' ?ℓ`

Use the induction hypothesis on `d`, then rebuild the final injection.

Diagram:

          cast V[d;(★⇒★ !)]   <=   V'
                 |
                 | *
                 |   induction hypothesis on d <= A' ?ℓ,
                 |   lifted through (★⇒★ !)
                 v
          cast N[(★⇒★ !)]     <=   V'



### 11. Casting on the left against an injection target

Lemma: `cast-left-!-val`

  If `V <= V'` and `c <= G !`, 
  then `cast V [ c ] -->* N` and `N <= cast V' [ G ! ]`.

Diagram:

          cast V[c]   <=   cast V'[G!]
             |
             | *
             v
             N        <=   cast V'[G!]


Proof shape:

  induction on the derivation of `c <= G !`

### Case 1. `G ! <= G !`

Diagram:

          cast V[G!]   <=   cast V'[G!]
             |
             | 0
             v
          cast V[G!]   <=   cast V'[G!]


### Case 2. `id A0 <= G !`

The left cast reduces by `β-id`, and then `star-to-inj` gives the bottom
precision step.

Diagram:

          cast V[id A0]   <=   cast V'[G!]
             |
             | 1
             v
             V        <=   cast V'[G!]


### Case 3. `(★⇒★ ?ℓ) ; d <= ★⇒★ !`

From `(★⇒★ ?ℓ) ; d <= G !` we have `★⇒★ <= G` so `G = ★⇒★`.

Diagram:

          cast V[(★⇒★ ?ℓ);d]             <=  cast V'[★⇒★!]
                  |
                  | 1
                  v
          cast (cast V[★⇒★ ?ℓ]) [d]      <=  cast V'[★⇒★!]
                  |
                  | *
                  |   cast-left-?-val on V <= cast V'[★⇒★!]
                  |   and (★⇒★ ?ℓ) <= (★⇒★ ?ℓ),
                  |   lifted through d
                  v
          cast W[d]                        <=  cast V'[★⇒★!]
                  |
                  | *
                  |   catchup on W <= V',
                  |   lifted through d
                  v
          cast W1[d]                       <=  cast V'[★⇒★!]
                  |
                  | *
                  |   induction hypothesis on d <= ★⇒★ !
                  v
                  N                          <=  cast V'[★⇒★!]


### Case 4. `d ; (★⇒★ !) <= G !`

Use the induction hypothesis on `d`, then rebuild the final injection.

Diagram:

          cast V[d;(★⇒★ !)]   <=   cast V'[G!]
                 |
                 | *
                 |   induction hypothesis on d <= G!,
                 |   lifted through (★⇒★ !)
                 v
          cast N[(★⇒★ !)]     <=   cast V'[G!]



## Forward simulation core

### 12. Catchup

Lemma: `catchup`

  If `N <= V'` and `V'` is a value, 
  then there exists `V` such that `N -->* V`, `V` is a value, and `V <= V'`.

Diagram:

          N    <=    V'
          |
          | *
          v
          V    <=    V'


Proof shape:

  induction on the precision derivation `N <= V'`

This is the main engine that turns a precision proof whose right side is a
value into an actual reduction sequence on the left.

### Case 1. `N <= V'` with `V'` a base value or lambda

Diagram:

          N    <=    V'
          |
          | 0
          v
          N    <=    V'


### Case 2. `N <= cast V1 [ G ! ]`

First recurse on the inner precision proof to reach a value on the left, then
use `cast-left-!-val`.

Diagram:

          N                  <=   cast V1[G!]
          |
          | *
          |   induction hypothesis
          v
          V                  <=   V1
          |
          | *
          |   cast-left-!-val on V <= V1
          v
          V2                 <=   cast V1[G!]


### Case 3. `N <= cast V1 [ c1 ↦ d1 ]`

Again recurse first to reach a left value, then analyze how the left coercion
sits below the function cast. The main subcases use either
`catchup-cast-idL↦` or `cast-left-↦-val`.

Diagram:

          N                  <=   cast V1[c1↦d1]
          |
          | *
          |   induction hypothesis
          v
          V                  <=   V1
          |
          | *
          |   catchup-cast-idL↦ on V <= cast V1[c1↦d1]
          |   or cast-left-↦-val on V <= V1
          v
          V2                 <=   cast V1[c1↦d1]


### Case 4. `cast N[c] <= V'`

First recurse on the inner precision proof, then use `cast-left-id-val`.

Diagram:

          cast N[c]   <=   V'
               |
               | *
               |   induction hypothesis on N <= V'
               v
               V      <=   V'
               |
               | *
               |   cast-left-id-val on N <= V'
               v
               V2     <=   V'


### Case 5. `N <= cast V' [ c' ]`

Recurse on the inner precision proof. No extra left reduction is needed after
the recursive call.

Diagram:

          N    <=   cast V'[c']
          |
          | *
          |   induction hypothesis
          v
          V    <=   cast V'[c']


### Case 6. `blame <= V'`

This case is impossible because the right side is a value.


### 13. Beta simulation against a lambda

Lemma: `sim-beta`

  If `V <= λx. N'` and `W <= W'`, then there exists `N` such that
  `V · W -->* N` and `N <= N'[W'/x]`.

Diagram:

          V · W        <=  (λx. N') · W'
          |                |
          | *              | 1
          v                v
          N            <=  N'[W'/x]


Proof shape:

  induction on the precision proof `V <= λx. N'`

### Case 1. `λx. N <= λx. N'`

So both sides beta-reduce immediately:

Diagram:

          (λx. N) · W   <=  (λx. N') · W'
          |                 |
          | 1               | 1
          v                 v
          N[W/x]        <=  N'[W'/x]


The bottom precision step is obtained by applying the lemma `[]ᶜ-⊑` to the
body precision `N <= N'` and the argument precision `W <= W'`.

So this case finishes in one beta step on the left.


### Case 2. `cast U [ c1 ↦ d1 ] <= λx. N'`

Side information:

  `c1 <= id`
  `d1 <= id`

Diagram:

          cast U[c1↦d1] · W                          <=   (λx. N') · W'
                  |                                          |
                  | 1                                        | 1
                  v                                          |
          cast (U · cast W[c1]) [d1]                         |
                  |                                          |
                  | *    cast-left-id-val on W <= W',        |
                  |      lifted through U · □ and [d1]       |
                  v                                          |
          cast (U · W1) [d1]                                 |
                  |                                          |
                  | *    induction hypothesis                |
                  |      on U <= λx. N' and W1 <= W',        |
                  |      lifted through [d1]                 |
                  v                                          v
              cast N [d1]                              <=   N'[W'/x]


The bottom precision step uses the lemma `cast-left-id-val` with `d1 <= id`
and the induction-hypothesis conclusion `N <= N'[W'/x]`.


### 14. Beta simulation against a function cast

Lemma: `sim-beta-cast`

  If `V <= cast V' [ c' ↦ d' ]` and `W <= W'`, then there exists `N` such
  that `V · W -->* N` and `N <= cast (V' · cast W' [ c' ]) [ d' ]`.

Diagram:

          V · W        <=  cast V'[c'↦d'] · W'
          |                |
          | *              | 1
          v                v
          N            <=  cast (V' · cast W'[c']) [d']


Proof shape:

  induction on the precision proof `V <= cast V' [ c' ↦ d' ]`

### Case 1. `cast V1 [ c ↦ d ] <= cast V' [ c' ↦ d' ]`

Here both sides already have explicit function casts.

Diagram:

          cast V1[c↦d] · W              <=  cast V'[c'↦d'] · W'
          |                                 |
          | 1                               | 1
          v                                 v
          cast (V1 · cast W[c]) [d]     <=  cast (V' · cast W'[c']) [d']


The bottom precision step is obtained directly from:

  `V1 <= V'`
  `W <= W'`
  `c <= c'`
  `d <= d'`

So this case finishes in one beta step on the left.


### Case 2. `cast U [ c1 ↦ d1 ] <= cast V' [ c' ↦ d' ]`

Side information:

  `c1 <= id`
  `d1 <= id`

Diagram:

          cast U[c1↦d1] · W                            <=  cast V'[c'↦d'] · W'
          |                                                |
          | 1                                              | 1
          v                                                v
          cast (U · cast W[c1]) [d1]                  <=  cast (V' · cast W'[c']) [d']
          |                                                |
          | *    cast-left-id-val on W <= W',              |
          |      lifted through U · □ and [d1]             | 0
          v                                                v
          cast (U · W1) [d1]                          <=  cast (V' · cast W'[c']) [d']
          |                                                |
          | *    induction hypothesis                      |
          |      on U <= cast V' [ c' ↦ d' ]               |
          |      and W1 <= W', lifted through [d1]         | 0
          v                                                v
          cast N [d1]                                 <=  cast (V' · cast W'[c']) [d']


The bottom precision step uses `⊑castL` with the side condition `d1 <= id`
applied to the induction-hypothesis conclusion

  `N <= cast (V' · cast W'[c']) [d']`.


### Case 3. `V1 <= cast V' [ c' ↦ d' ]`

Side information:

  `id <= c' ↦ d'`

In this case the left side does not need to reduce at all.

Diagram:

          V1 · W                         <=  cast V'[c'↦d'] · W'
          |                                  |
          | 0                                | 1
          v                                  v
          V1 · W                         <=  cast (V' · cast W'[c']) [d']


The bottom precision step is obtained directly from:

  `V1 <= V'`
  `W <= W'`
  `id <= c'`
  `id <= d'`


### 15. One-step forward simulation

Lemma: `sim`

  If `M <= M'` and `M' --> N'`, then there exists `N` such that
  `M -->* N` and `N <= N'`.

Diagram:

          M      <=  M'
          |          |
          | *        | 1
          v          v
          N      <=  N'


Proof shape:

  induction on the right-hand one-step reduction.

### Case 1. The right step happens inside a subterm

Apply the induction hypothesis to that inner step, then rebuild the same outer
context.

Diagram:

          L · W        <=  L' · W'
          |                |
          | *  induction   | 1
          v                v
          N · W        <=  N' · W'


This covers the application and cast contexts. When the left term is wrapped in
an extra left cast, apply the induction hypothesis to the inner term and then
rebuild that left cast.

### Case 2. The right step is a beta step against a lambda

Use the lemma `catchup` on the function position and on the argument position,
then use the lemma `sim-beta`.

Diagram:

          L · M                                      <=  (λx. N') · M'
          |                                              |
          | *  catchup on L <= λx. N' and M <= M'        | 1
          v                                              v
          V · W                                          N'[M'/x]
          |
          | *  sim-beta on V <= λx. N' and W <= W'
          v
          N                                          <=  N'[M'/x]


### Case 3. The right step is a beta step against a function cast

Again use `catchup` to reach a left function value and a left argument value,
then use the lemma `sim-beta-cast`.

Diagram:

          L · M                                              <=  cast V'[c'↦d'] · W'
          |                                                      |
          | *  catchup on L <= cast V'[c'↦d'] and M <= W'        | 1
          v                                                      v
          V · W                                                  cast (V' · cast W'[c']) [d']
          |
          | *  sim-beta-cast on V <= cast V'[c'↦d'] and W <= W'
          v
          N                                                  <=  cast (V' · cast W'[c']) [d']


### Case 4. The right step removes an identity cast

No new reduction is needed on the left.

Diagram:

          M                    <=  cast M'[id]
          |                        |
          | 0                      | 1
          v                        v
          M                    <=  M'


### Case 5. The right step splits a sequence cast

Use `catchup` to reach a left value below the right value, then use the lemma
`cast-left-⨟-val`.

Diagram:

          cast M[c]                                  <=  cast V'[c'⨟d']
          |                                              |
          | *  catchup on M <= V',                       | 1
          |    lifted through [c]                        |
          v                                              v
          cast V[c]                                  <=  cast (cast V'[c']) [d']
          |
          | *  cast-left-⨟-val on V <= V' and c <= c'⨟d'
          v
          N                                          <=  cast (cast V'[c']) [d']


### Case 6. The right step projects a matching injection

Use `catchup` to expose a left value below the injected right value, then use
the lemma `cast-left-?-val`.

Diagram:

          cast M[c]                                      <=  cast (cast V'[A'!]) [A'?]
          |                                                  |
          | *  catchup on M <= cast V'[A'!],                 | 1
          |    lifted through [c]                            |
          v                                                  v
          cast V[c]                                          V'
          |
          | *  cast-left-?-val on V <= cast V'[A'!]
          v
          N                                              <=  V'


### Case 7. The right step reaches `blame`

Take `N = M`.

Diagram:

          M        <=  M'
          |            |
          | 0          | 1
          v            v
          M        <=  blame



### 16. Multi-step forward simulation

Lemma: `sim*`

  If `M <= M'` and `M' -->* N'`, then there exists `N` such that
  `M -->* N` and `N <= N'`.

Diagram:

          M      <=  M'
          |          |
          | *        | *
          v          v
          N      <=  N'


Proof shape:

  induction on the right-hand reduction sequence.

### Case 1. Zero steps on the right

Take `N = M`.

### Case 2. One more step on the right

First use the lemma `sim` for the first right-hand step. Then use the
induction hypothesis for the remaining right-hand sequence, and compose the two
left-hand reduction sequences.

Diagram:

          M                          <=  M'
          |                              |
          | *  sim on M <= M'            | 1
          |    and M' --> N1'            |
          v                              v
          N1                         <=  N1'
          |                              |
          | *  induction                 | *
          v                              v
          N                          <=  N'



### 17. Termination transfer from right to left

Lemma: `gg`

  If `M' <= M` and `M -->* V` and `V` is a value, then there exists `V'`
  such that `M' -->* V'`, `V'` is a value, and `V' <= V`.

Diagram:

          M'     <=  M
          |          |
          | *        | *
          v          v
          V'     <=  V


Proof shape:

  first use the lemma `sim*` to move the whole right-hand reduction sequence to
  the left.

Diagram:

          M'                     <=  M
          |                         |
          | *  sim* on M' <= M      | *
          |    and M -->* V         |
          v                         v
          N'                     <= V
          |
          | *  catchup on N' <= V
          v
          V'                     <= V


Composing the two left-hand sequences gives the result.


## Backward simulation core

### 18. Values on the left force catchup on the right

Lemma: `value-right-catchup`

  If `V` is a value and `V <= M'`, then there exists `N` such that
  `M' -->* N` and either (`N` is a value and `V <= N`) or (`N = blame`).

Diagram:

          V      <=  M'
          |          |
          | 0        | *
          v          v
          V      <=  N    or    blame


Proof shape:

  induction on the precision derivation `V <= M'`.

### Case 1. `V <= M'` with `M'` a base value or a lambda

Take `N = M'`. No right reduction is needed.

### Case 2. `V <= cast M' [ c' ]`

First apply the induction hypothesis to the inner precision proof, so the right
side reduces to either a value or blame. If it reaches a value `W'`, apply
`cast-value-catchup` to `cast W' [ c' ]`. If it reaches blame, the outer cast
also reduces to blame.

Diagram:

          V                    <=  cast M'[c']
                                    |
                                    | *  induction on V <= M',
                                    |   lifted through [c']
                                    v
          V                    <=  cast W'[c']
                                    |
                                    | *  cast-value-catchup
                                    |   on cast W'[c']
                                    v
          V                    <=   N


When the precision proof is a left-cast case around a casted injection or
function value, the induction hypothesis already gives the needed right-hand
value or blame, so no extra right reduction is needed.

### Case 3. `V <= blame`

Take `N = blame`.


### 19. Beta backward simulation against a lambda

Lemma: `sim-back-beta`

  If `λx. N <= F'` and `V <= M'`, then there exists `N'` such that
  `F' · M' -->* N'` and `N[V/x] <= N'`.

Diagram:

          (λx. N) · V   <=  F' · M'
          |                 |
          | 1               | *
          v                 v
          N[V/x]        <=  N'


Proof shape:

  induction on the precision proof `λx. N <= F'`.

### Case 1. `λx. N <= λx. N'`

Use the lemma `value-right-catchup` on the argument precision `V <= M'`.

Diagram:

          (λx. N) · V                <=  (λx. N') · M'
                                           |
                                           | *  value-right-catchup on V <= M'
                                           v
                                       (λx. N') · W'
                                           |
                                           | 1
                                           v
                                       N'[W'/x]


If the right argument catches up to a value `W'`, the final horizontal step is
obtained by the lemma `[]ᶜ-⊑`.

Diagram:

          (λx. N) · V                <=  (λx. N') · M'
          |                                |
          | 1                              | *
          v                                v
          N[V/x]                       <=  N'[W'/x]


If the right argument catches up to blame instead, the right application
reaches blame.

Diagram:

          (λx. N) · V                <=  (λx. N') · M'
          |                                |
          | 1                              | *
          v                                v
          N[V/x]                       <=  blame


### Case 2. `λx. N <= cast F'[c↦d]`

Use `value-right-catchup` on the argument again. If the right argument reaches
blame, the whole right application reaches blame. If it reaches a value `W'`,
apply the induction hypothesis to the smaller function precision with
`V <= cast W'[c]`, then rebuild the output cast on the right.

Diagram:

          (λx. N) · V                    <=  cast F'[c↦d] · M'
                                               |
                                               | *  value-right-catchup on V <= M'
                                               v
                                           cast F'[c↦d] · W'
                                               |
                                               | 1
                                               v
                                           cast (F' · cast W'[c]) [d]
          |                                    |
          | 1                                  | *  induction
          v                                    v
          N[V/x]                           <=  cast N' [d]


The final horizontal step is obtained by rebuilding the right output cast
around the induction-hypothesis conclusion.


### 20. Beta backward simulation against a function cast

Lemma: `sim-back-beta-cast`

  If `cast V [ c ↦ d ] <= F'` and `W <= M'`, then there exists `N'` such that
  `F' · M' -->* N'` and `cast (V · cast W [ c ]) [ d ] <= N'`.

Diagram:

          cast V[c↦d] · W   <=             F' · M'
          |                                |
          | 1                              | *
          v                                v
          cast (V · cast W[c]) [d]  <=     N'


Proof shape:

  induction on the precision proof `cast V [ c ↦ d ] <= F'`.

### Case 1. `cast V[c↦d] <= cast V'[c'↦d']`

Use `value-right-catchup` on the argument precision `W <= M'`. If the right
argument reaches blame, the right application reaches blame. If it reaches a
value `W'`, the right side takes one function-cast beta step, and the final
precision fact is obtained directly from the function, argument, and coercion
precision facts.

Diagram:

          cast V[c↦d] · W                    <=  cast V'[c'↦d'] · M'
          |                                         |
          | 1                                       | *  value-right-catchup on W <= M'
          v                                         v
          cast (V · cast W[c]) [d]               cast V'[c'↦d'] · W'
                                                    |
                                                    | 1
                                                    v
          cast (V · cast W[c]) [d]           <=  cast (V' · cast W'[c']) [d']


The bottom horizontal step is obtained directly from the function, argument,
and coercion precision facts.

### Case 2. `cast V[c↦d] <= F'`

Here the precision proof is already a left-cast case into `F'`, so no right
reduction is needed.

Diagram:

          cast V[c↦d] · W                <=  F' · M'
          |                                  |
          | 1                                | 0
          v                                  v
          cast (V · cast W[c]) [d]      <=  F' · M'


### Case 3. `cast V[c↦d] <= cast F'[c'↦d']`

Use `value-right-catchup` on the argument precision. If the right argument
reaches a value `W'`, apply the induction hypothesis to the smaller function
precision with `W <= cast W'[c']`, then rebuild the outer right output cast.

Diagram:

          cast V[c↦d] · W                    <=  cast F'[c'↦d'] · M'
          |                                         |
          | 1                                       | *  value-right-catchup on W <= M'
          v                                         v
          cast (V · cast W[c]) [d]              cast F'[c'↦d'] · W'
                                                    |
                                                    | 1
                                                    v
          cast (V · cast W[c]) [d]              cast (F' · cast W'[c']) [d']
                                                    |
                                                    | *  induction
                                                    v
          cast (V · cast W[c]) [d]           <=  cast N' [d']


The final horizontal step is obtained by rebuilding the outer right output cast
around the induction-hypothesis conclusion.


### 21. One-step backward simulation

Lemma: `sim-back`

  If `M <= M'` and `M --> N`, then there exists `N'` such that
  `M' -->* N'` and `N <= N'`.

Diagram:

          M      <=  M'
          |          |
          | 1        | *
          v          v
          N      <=  N'


Proof shape:

  induction on the left-hand one-step reduction.

### Case 1. The left step happens inside a subterm

Apply the induction hypothesis to that inner step, then rebuild the same outer
context on the right.

Diagram:

          M            <=  M'
          |                |
          | 1              | *  induction
          v                v
          N            <=  N'


If the left step is in the argument of an application, first use the lemma
`value-right-catchup` to make the right function catch up to a value or blame,
then rebuild the application context.

### Case 2. The left step propagates blame out of a context

Make the corresponding right subterm catch up to blame, then the whole right
context also reduces to blame.

Diagram:

          M            <=  M'
          |                |
          | 1              | *
          v                v
          blame        <=  blame


### Case 3. The left step is a beta step against a lambda

First use `value-right-catchup` on the right function. If it reaches blame, the
right application reaches blame. If it reaches a function value `F'`, use the
lemma `sim-back-beta`.

Diagram:

          (λx. N) · V                                      <=  L' · M'
          |                                                    |
          | 1                                                  | *  value-right-catchup on λx. N <= L'
          v                                                    v
          N[V/x]                                               F' · M'
                                                               |
                                                               | *  sim-back-beta on λx. N <= F' and V <= M'
                                                               v
                                                               N'
          N[V/x]                                           <=  N'


### Case 4. The left step is a beta step against a function cast

Use `value-right-catchup` on the right function and on the right argument. If
either side catches up to blame, the right application reaches blame. If both
reach values, use the lemma `sim-back-beta-cast`.

Diagram:

          cast V[c↦d] · W                                    <=  L' · M'
          |                                                      |
          | 1                                                    | *  value-right-catchup on cast V[c↦d] <= L' and W <= M'
          v                                                      v
          cast (V · cast W[c]) [d]                               F' · W'
                                                                 |
                                                                 | *  sim-back-beta-cast on cast V[c↦d] <= F' and W <= W'
                                                                 v
                                                                 N'
          cast (V · cast W[c]) [d]                           <=  N'


### Case 5. The left step removes an identity cast

Use `value-right-catchup` on the value precision under the cast. If the right
side reaches blame, we are done. If it reaches a value, let the outer right
cast finish reducing, and keep the resulting precision fact.

Diagram:

          cast V[id]                  <=  cast M'[c']
          |                               |
          | 1                             | *
          v                               v
          V                           <=  N'


### Case 6. The left step splits a sequence cast

If the right precision is only by left casts, then no right reduction is
needed. Otherwise use `value-right-catchup` to expose a right value, inspect
how the left sequence sits below the right coercion, and either let the right
perform the matching sequence step or observe that the right side is already in
the weaker target form.

Diagram:

          cast V[c⨟d]                  <=  cast M'[c']
          |                               |
          | 1                             | *
          v                               v
          cast (cast V[c]) [d]        <=  N'


### Case 7. The left step projects a matching injection

Use `value-right-catchup` to expose a right injected value or blame. If the
right side reaches blame, we are done. If it reaches an injected value, either
its outer cast already yields the needed value, or we use the lemma `sim*`
followed by the lemma `catchup` to continue the right cast until a value is
reached.

Diagram:

          cast (cast V[G!]) [G?]                               <=  cast M'[c']
          |                                                        |
          | 1                                                      | *  value-right-catchup on cast V[G!] <= M'
          v                                                        v
          V                                                        cast W'[c']
                                                                   |
                                                                   | *  sim* on cast (cast V[G!]) [G?] <= cast W'[c']
                                                                   v
                                                                   N1
                                                                   |
                                                                   | *  catchup on N1 <= N'
                                                                   v
                                                                   N'
          V                                                    <=  N'


### Case 8. The left step projects a mismatching injection

The start is the same as in the successful-projection case, but once the right
injected value is exposed, the mismatch forces the right side to reach blame.

Diagram:

          cast (cast V[G!]) [H?]                               <=  cast M'[c']
          |                                                        |
          | 1                                                      | *  value-right-catchup on cast V[G!] <= M'
          v                                                        v
          blame                                                <=  cast W'[c']
                                                                   |
                                                                   | *
                                                                   v
                                                                   blame


### Case 9. The right side is already below `blame`

Take `N' = blame`. This also covers the impossible cases where a variable,
constant, or lambda on the left would have to step.


### 22. Multi-step backward simulation

Lemma: `sim-back*`

  If `M <= M'` and `M -->* N`, then there exist `N'` and `N2` such that
  `M' -->* N'`, `N -->* N2`, and `N2 <= N'`.

Diagram:

          M      <=  M'
          |          |
          | *        | *
          v          v
          N          N'
          |
          | *
          v
          N2     <=  N'


Proof shape:

  induction on the left-hand reduction sequence.

### Case 1. Zero steps on the left

Take `N' = M'` and `N2 = M`.

### Case 2. One more step on the left

First use the lemma `sim-back` for the first left-hand step. Then use the
induction hypothesis for the remaining left-hand sequence.

Diagram:

          M                 <=  M'
          |                     |
          | 1                   | *  sim-back on M <= M' and M --> N1
          v                     v
          N1                <=  N1'
          |                     |
          | *  induction        | *
          v                     v
          N2                <=  N'


The left residual sequence `N -->* N2` comes from the induction hypothesis.


## Dynamic Gradual Guarantee

### Statement

Assume:

  `M ⊑ᵀ M'`
  `[] ⊢ M : A`
  `[] ⊢ M' : A'`

By `compile-precision` we get:

  `[[M]] <= [[M']]`


### Part 1. If the more precise program produces a value,
the less precise program also produces a related value.

Wanted:

  If `[[M']] -->* V'` and `V'` is a value, then there exists `V` such that
  `[[M]] -->* V`, `V` is a value, and `V <= V'`.

Diagram:

          [[M]]     <=  [[M']]
          |             |
          | *           | *
          v             v
          V         <=  V'


Proof:

  use `compile-precision`
  then use `gg`


### Part 2. If the more precise program diverges,
the less precise program also diverges.

Diagram:

          [[M]]   <=   [[M']]
            ?              |
            ?              | diverges
            ?              v
            ?           no value / no blame


Contrapositive diagram:

          [[M]]     <=  [[M']]
          |             |
          | *           | *
          v             v
          V         <=  V'


Proof:

  use `compile-precision`
  then use `gg-diverge`
  which is obtained from Part 1 by contraposition


### Part 3. If the less precise program produces a value,
the more precise program either produces a related value or blames.

Wanted:

  If `[[M]] -->* V` and `V` is a value, then either there exists `V'` such
  that `[[M']] -->* V'`, `V'` is a value, and `V <= V'`, or `[[M']] -->* blame`.

Main diagram:

          [[M]]     <=  [[M']]
          |             |
          | *           | *
          v             v
          V         <=  N'


Then use `value-right-catchup` on the bottom line:

      N2 = V    <=  N'
                   |
                   | *
                   v
                   V'  or  blame

Final diagram:

          [[M]]     <=  [[M']]
          |             |
          | *           | *
          v             v
          V         <=  V'


or

      [[M]]     <=  [[M']]
      |             |
      | *           | *
      v             v
      V             blame

Proof:

  use `compile-precision`
  then use `sim-back*`
  then use `value-right-catchup`


### Part 4. If the less precise program diverges,
the more precise program either diverges or reaches blame.

Wanted:

  If `[[M]]` diverges, then for every `N'` with `[[M']] -->* N'`, either
  `N' = blame` or `N' --> N''`.

Diagram at an arbitrary right-hand prefix:

      [[M]]     <=  [[M']]
                     |
                     | *
                     v
                     N'
      |
      | sim*
      v
      N         <=  N'

If `N'` is a value, `catchup` would give:

      N      <=  N'
      |
      | *
      v
      V      <=  N'

which would make `[[M]]` converge, contradiction.

So every reachable `N'` on the right is either:

  * already blame
  * or can still step

Diagram:

          [[M]]     <=  [[M']]
          |             |
          | diverges    | *
          |             v
          |             N'
          |
          +---- impossible if N' is a value


Proof:

  use `compile-precision`
  then use `sim*`
  then use `catchup`


## Whole theorem at a glance

Forward value transfer:

      [[M]]     <=  [[M']]
      |             |
      | *           | *
      v             v
      V         <=  V'

Backward value-or-blame transfer:

      [[M]]     <=  [[M']]
      |             |
      | *           | *
      v             v
      V         <=  V'

or

      [[M]]     <=  [[M']]
      |             |
      | *           | *
      v             v
      V             blame

Divergence transfer:

      [[M]]   <=   [[M']]
                        |
                        | diverges
                        v
                     diverges

or, in the other direction:

      [[M]] diverges
      [[M']] can only:

        |
        | 1
        v
      blame

      or

        |
        | 1
        v
        N'
        |
        | ...
        v
        ...

but never get stuck at a value.
