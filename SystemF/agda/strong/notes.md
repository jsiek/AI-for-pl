Strong System F

This version of System F keep tight control over where type variables
can appear and where they cannot. The name "strong" alludes to the
fact that weakening with respect to type variables is not used.

# TODO

* finish removing Commute
* FIX TyWrapCncl soundness bug: (tapp) on a concealed ∀ may instantiate at a type
  variable outside X's existential scope, and TyWrapCncl then leaks it into the
  sealed body — preservation fails (see Example 8).  Confine the type argument to Γ↓X.

# Types (with variables as names)

  X,Y,Z ∈ TyVar
  A,B,C ::= X | ℕ | 𝔹 | A → B | ∀X.A

# Source Terms (with variables as names)

  n ∈ ℕ
  b ∈ 𝔹
  x ∈ Var
  k ::= n | b
  ⊕ ::= + | ×
  L,M,N ::= x | k | M ⊕ N | λx:A. N | L · M | ΛX.N | L @B[A]

# Runtime Terms (with variables as names)

  L,M,N ::= ... | M ↑[X:=A]@B | M ↓[X:=A]@B

# Contexts

  Γ ::= ∅ | Γ, x:A | Γ, X | Γ, X:=A

  There is NO conceal marker.  A conceal ↓[X:=A] does not extend the context; instead its
  body is typed in the *prefix* Γ ↓ X (below) — the part of Γ deeper than X, its existential
  scope.  (An earlier design used a marker ↓X; see the cautionary note near the end.)

# Context Prefix     Γ ↓ X

  The part of Γ deeper than X: everything bound BEFORE X's binder, dropping X itself and
  everything shallower (bound after X).  This is X's existential scope — a value sealed on X
  may depend only on it.  Used by the (conceal) rule.

  Γ, X ↓ X     = Γ
  Γ, Y ↓ X     = Γ ↓ X    (Y ≠ X)
  Γ, X:=A ↓ X  = Γ
  Γ, Y:=A ↓ X  = Γ ↓ X    (Y ≠ X)
  Γ, x:A ↓ X   = Γ ↓ X

  Because the kept part Γ₁ = Γ↓X is bound before X, nothing in it mentions X — so Γ↓X is
  well-formed on its own, with no dangling reference to the sealed variable.  (This is exactly
  what the failed conceal-b design got wrong: it kept the SHALLOWER part too, where entries
  like Y:=(X→X) do mention X.)

# Type-variable lookup   Γ ∋ X   /   Γ ∋ X:=A     (Q ranges over the query, X or X:=A)

  Ordinary lookup — there is no marker to skip past, since contexts have none.

  (∋-tvar)   Γ, X    ∋ X
  (∋-var1)   Γ ∋ X           ⟹  Γ, x:A ∋ X
  (∋-tskip1) Γ ∋ X           ⟹  Γ, Y   ∋ X          (Y ≠ X)
  (∋-rskip1) Γ ∋ X           ⟹  Γ, Y:=A ∋ X         (Y ≠ X)
  
  (∋-rvar)   Γ, X:=A ∋ X:=A
  (∋-var2)   Γ ∋ X:=A        ⟹  Γ, x:A ∋ X:=A
  (∋-tskip2) Γ ∋ X:=A        ⟹  Γ, Y   ∋ X:=A       (Y ≠ X)
  (∋-rskip2) Γ ∋ X:=A        ⟹  Γ, Y:=A ∋ X:=A      (Y ≠ X)


# Term-variable lookup   x:A ∈ Γ

  (∈-here)   x:A ∈ Γ, x:A
  (∈-var)    x:A ∈ Γ  ⟹  x:A ∈ Γ, y:B       (y ≠ x)
  (∈-tvar)   x:A ∈ Γ  ⟹  x:A ∈ Γ, Y
  (∈-rvar)   x:A ∈ Γ  ⟹  x:A ∈ Γ, Y:=B

  Note: a conceal body uses no term variables.  A conceal appears only at runtime, where Γ is
  term-variable-free (no reduction fires under a λ), and the body is typed in the prefix Γ↓X,
  which drops every term variable anyway.  So substitution never reaches into a conceal (see
  Term-variable substitution below).  Source programs have no conceals, so this is ordinary
  lookup there.

# Well-formed Types   Γ ⊢ A

  (wf-ℕ)                        ⟹  Γ ⊢ ℕ
  (wf-𝔹)                        ⟹  Γ ⊢ 𝔹
  (wf-tvar)   Γ ∋ X             ⟹  Γ ⊢ X
  (wf-rvar)   Γ ∋ X:=A          ⟹  Γ ⊢ X
  (wf-fun)    Γ ⊢ A    Γ ⊢ B    ⟹  Γ ⊢ A → B
  (wf-all)    Γ, X ⊢ A          ⟹  Γ ⊢ ∀X.A

# Well-formed Contexts   ⊢ Γ

  (ctx-empty)  ⊢ ∅
  (ctx-var)    ⊢ Γ   Γ ⊢ A       ⇒ ⊢ Γ, x:A
  (ctx-tvar)   ⊢ Γ               ⇒ ⊢ Γ, X
  (ctx-rvl)    ⊢ Γ   Γ ⊢ A       ⇒ ⊢ Γ, X:=A

# Type System

  (cnst-n)  ---------
            Γ ⊢ n : ℕ
            
  (cnst-b)  ---------
            Γ ⊢ b : 𝔹
  
  (arith)   Γ ⊢ L : ℕ   Γ ⊢ M : ℕ
            ---------------------
            Γ ⊢ L ⊕ M : ℕ
            
  (var)     x:A ∈ Γ
            ---------
            Γ ⊢ x : A
            
  (lam)     Γ, x:A ⊢ N : B   Γ ⊢ A
            -----------------------
            Γ ⊢ λx:A.N : A→B
            
  (app)     Γ ⊢ L : A→B   Γ ⊢ M : A
            -----------------------
            Γ ⊢ L·M : B
  
  (tlam)    Γ, X ⊢ N : C
            ---------------
            Γ ⊢ ΛX.N : ∀X.C
            
  (tapp)    Γ ⊢ L : ∀X.B   Γ ⊢ A
            --------------------
            Γ ⊢ L@B[A] : B[X:=A]

  (reveal)  Γ, X:=A ⊢ M : B   Γ ⊢ A
            -------------------------
            Γ ⊢ M ↑[X:=A]@B : B[X:=A]

  (conceal) Γ ∋ X:=A   Γ ⊢ B   Γ ↓ X ⊢ M : B[X:=A]
            --------------------------------------
            Γ ⊢ M↓[X:=A]@B : B

    The body M is typed in the prefix Γ↓X (X's existential scope), not in Γ.  So M — and,
    since B[X:=A] must be well-formed there, the annotation B — may mention only X-and-deeper
    variables; there is no marker and no side condition.  In de Bruijn, Γ↓X drops the indices
    ≤ X, so M's and B[X:=A]'s indices are already prefix-relative: nothing is incremented and
    nothing has to be shifted back down.

# Values

  G ::= λx:A. N | ΛX.V | G ↑[X:=A]@B
  F ::= G | F ↓[X:=A]@B
  V,W ::= k | F | V ↓[X:=A]@B

# Frames

  R ::= □ ⊕ M | V ⊕ □ | □ · M | V · □ | □ ↑[X:=A]@B | □ ↓[X:=A]@B | □ @B[A] | Λ □

# Term-variable substitution   N[x := V]     (V a value)

  Capture-avoiding, by recursion on N.  Types carry no term variables, so every type
  annotation (the A of λx:A, and each X:=A, @B, @B[A]) is untouched.  By the Barendregt
  convention the bound variables — the y of λy, the X of ΛX and of a reveal ↑[X:=A] — are
  kept distinct from the free variables of V; at runtime V is term-closed, so no term binder
  ever needs renaming and only type binders can interact with V's free type variables.

  x[x:=V]             = V
  y[x:=V]             = y                             (y ≠ x)
  k[x:=V]             = k
  (M₁ ⊕ M₂)[x:=V]     = M₁[x:=V] ⊕ M₂[x:=V]
  (L · M)[x:=V]       = L[x:=V] · M[x:=V]
  (λx:A. N)[x:=V]     = λx:A. N                       (bound x shadows the substituted x)
  (λy:A. N)[x:=V]     = λy:A. N[x:=V]                 (y ≠ x)
  (Λ X. N)[x:=V]      = Λ X. N[x:=V]
  (L @B[A])[x:=V]     = L[x:=V] @B[A]
  (M ↑[X:=A]@B)[x:=V] = M[x:=V] ↑[X:=A]@B             -- reveal passes term vars: recurse
  (M ↓[X:=A]@B)[x:=V] = M ↓[X:=A]@B                   -- conceal blocks term vars: identity

  The reveal/conceal asymmetry mirrors the type system: a reveal ↑[X:=A] leaves term variables
  visible, so substitution descends into its body; a conceal ↓[X:=A] types its body in the
  prefix Γ↓X, which excludes the substituted (shallower) term variable, so a well-typed conceal
  body cannot mention it and substitution is the identity on it.  Taking that as the defining
  clause (rather than recursing, which would give the same result) makes seals inert by
  construction and matches the de Bruijn port, where the body's variable scope is the prefix.

# Reduction rules

  (δ)           n₁ ⊕ n₂               -→ n           if n = n₁ ⟦⊕⟧ n₂
  (Beta)        (λx:A. N) · V         -→ N[x:=V]
  (TyBeta)      (Λ X. V) @B[A]        -→ V ↑[X:=A]@B
  (WrapReveal)  F ↑[X:=A]@(B₁→B₂) · W -→ (F · W↓[X:=A]@B₁) ↑[X:=A]@B₂
  (WrapConceal) F ↓[X:=A]@(B₁→B₂) · W -→ (F · W↑[X:=A]@B₁) ↓[X:=A]@B₂
  (TyWrapRevl)  F ↑[X:=A]@∀Y.B [C]    -→ F [C] ↑[X:=A]@B
  (TyWrapCncl)  F ↓[X:=A]@∀Y.B [C]    -→ F [C[X:=A]] ↓[X:=A]@B
  (Cancel)      V ↓[X:=A]@B ↑[X:=A]@B -→ V
  (Drop)        V ↓[Y:=B]@C ↑[X:=A]@D -→ V ↓[Y:=B]@C  if X ≠ Y and X ∉ V↓[Y:=B]
  (RevealCnst)  k ↑[X:=A]@B           -→ k
  (ξ)           R[M]                  -→ R[M′]      if M -→ M′

  There is no Commute rule.  Its precondition (X ≠ Y and X ∈ V↓[Y:=B]) cannot hold for a
  well-typed reveal-on-conceal: the conceal on Y is typed in a prefix that excludes the
  freshly-revealed X, so the sealed value cannot mention X.  Hence a reveal-over-conceal on a
  different variable is always Drop (the X ∉ V↓[Y:=B] side condition holds automatically).


# Examples

## Example 1

  (Λ Y. λy:Y. (ΛX.λx:X.y) [Y] ) [ℕ] · 7 · 3
  → TyBeta      (λy:Y. (ΛX.λx:X.y) [Y] ) ↑[Y:=ℕ] · 7 · 3
  → WrapReveal  ((λy:Y. (ΛX.λx:X.y) [Y] ) · 7↓[Y:=ℕ]) ↑[Y:=ℕ] · 3
  → Beta        (ΛX. λx:X. 7↓[Y:=ℕ]) [Y] ↑[Y:=ℕ] · 3
  → TyBeta      (λx:X. 7↓[Y:=ℕ]) ↑[X:=Y] ↑[Y:=ℕ] · 3
  → WrapReveal  ((λx:X. 7↓[Y:=ℕ]) ↑[X:=Y] · 3↓[Y:=ℕ]) ↑[Y:=ℕ]
  → WrapReveal  ((λx:X. 7↓[Y:=ℕ]) · 3↓[Y:=ℕ]↓[X:=Y]) ↑[X:=Y] ↑[Y:=ℕ]
  → Beta        7↓[Y:=ℕ] ↑[X:=Y] ↑[Y:=ℕ]
  → Drop        7↓[Y:=ℕ] ↑[Y:=ℕ]
  → Cancel      7

## Example 2

  (ΛX. λf:X→X. λy:X. f·y) [ℕ] · (λn:ℕ.n+1) · 7
  → TyBeta      (λf. λy. f·y) ↑[X:=ℕ] · (λn.n+1) · 7
  → WrapReveal  ((λf. λy. f·y) · (λn.n+1)↓[X:=ℕ]) ↑[X:=ℕ] · 7
  → Beta        (λy. (λn.n+1)↓[X:=ℕ] · y) ↑[X:=ℕ] · 7
  → WrapReveal  ((λy. (λn.n+1)↓[X:=ℕ] · y) · 7↓[X:=ℕ]) ↑[X:=ℕ]
  → Beta        ((λn.n+1)↓[X:=ℕ] · 7↓[X:=ℕ]) ↑[X:=ℕ]        -- sealed fn in head position
  → WrapConceal ((λn.n+1) · (7↓[X:=ℕ]↑[X:=ℕ])) ↓[X:=ℕ] ↑[X:=ℕ]
  → Cancel      ((λn.n+1) · 7) ↓[X:=ℕ] ↑[X:=ℕ]
  → Beta        8 ↓[X:=ℕ] ↑[X:=ℕ]
  → Cancel      8

## Example 3   (type application to wrapped polymorphic values)

  (ΛX. λf:(∀Z.Z→Z). f [X]) [𝔹] · ((ΛY. ΛZ. λz:Z. z) [ℕ])
  → TyBeta      (λf:(∀Z.Z→Z). f [X]) ↑[X:=𝔹] · ((ΛY. ΛZ. λz:Z. z) [ℕ])
  → TyBeta      (λf:(∀Z.Z→Z). f [X]) ↑[X:=𝔹] · (ΛZ. λz:Z. z) ↑[Y:=ℕ]
  → WrapReveal  ((λf. f [X]) · (ΛZ. λz:Z. z) ↑[Y:=ℕ] ↓[X:=𝔹]) ↑[X:=𝔹]
  → Beta        ((ΛZ. λz:Z. z) ↑[Y:=ℕ] ↓[X:=𝔹] [X]) ↑[X:=𝔹]
  → TyWrapCncl  ((ΛZ. λz:Z. z) ↑[Y:=ℕ] [𝔹]) ↓[X:=𝔹] ↑[X:=𝔹]        -- X[X:=𝔹] = 𝔹
  → TyWrapRevl  ((ΛZ. λz:Z. z) [𝔹]) ↑[Y:=ℕ] ↓[X:=𝔹] ↑[X:=𝔹]
  → TyBeta      (λz:Z. z) ↑[Z:=𝔹] ↑[Y:=ℕ] ↓[X:=𝔹] ↑[X:=𝔹]
  → Cancel      (λz:Z. z) ↑[Z:=𝔹] ↑[Y:=ℕ]


## Example 4   (a constant escaping a reveal)

  (ΛX. λx:X. 7) [ℕ] · 5
  → TyBeta      (λx:X. 7) ↑[X:=ℕ] · 5
  → WrapReveal  ((λx:X. 7) · 5↓[X:=ℕ]) ↑[X:=ℕ]
  → Beta        7 ↑[X:=ℕ]
  → RevealCnst  7

## Example 5

  (ΛX. λf:(X→X)→X. f · (λx:X. x)) [ℕ] · (λg:ℕ→ℕ. g · 42)
  --> TyBeta
  (λf:(X→X)→X. f · (λx:X. x))↑[X:=ℕ] · (λg:ℕ→ℕ. g · 42)
  --> WrapReveal
  ((λf:(X→X)→X. f · (λx:X. x)) · (λg:ℕ→ℕ. g · 42)↓[X:=ℕ])↑[X:=ℕ]
  --> Beta
  ((λg:ℕ→ℕ. g · 42)↓[X:=ℕ] · (λx:X. x))↑[X:=ℕ]
  --> WrapConceal
  ((λg:ℕ→ℕ. g · 42) · (λx:X. x)↑[X:=ℕ]) ↓[X:=ℕ] ↑[X:=ℕ]
  --> Beta
  ((λx:X. x)↑[X:=ℕ] · 42) ↓[X:=ℕ] ↑[X:=ℕ]
  --> WrapReveal
  ((λx:X. x) · 42↓[X:=ℕ]) ↑[X:=ℕ] ↓[X:=ℕ] ↑[X:=ℕ]
  --> Beta
  42↓[X:=ℕ] ↑[X:=ℕ] ↓[X:=ℕ] ↑[X:=ℕ]
  --> Cancel
  42↓[X:=ℕ] ↑[X:=ℕ]
  --> Cancel
  42

## Example 6

  (ΛX. λw:ℕ. (ΛY. w) [X→X]) [ℕ] · 5
  → TyBeta      (λw:ℕ. (ΛY. w) [X→X]) ↑[X:=ℕ] · 5
  → WrapReveal  ((λw:ℕ. (ΛY. w) [X→X]) · 5↓[X:=ℕ]) ↑[X:=ℕ]
  → Beta        ((ΛY. 5↓[X:=ℕ]) [X→X]) ↑[X:=ℕ]
  → TyBeta      (5↓[X:=ℕ] ↑[Y:=X→X]) ↑[X:=ℕ]
  → Drop        5↓[X:=ℕ] ↑[X:=ℕ]
  → Cancel      5

## Example 7

  (ΛX. λw:X. (ΛY. λy:X → Y. y · w) [X] · (λz:X.z)) [ℕ] · 5
  --> TyBeta
  (λw:X. (ΛY. λy:X → Y. y · w) [X] · (λz:X.z)) ↑[X:=ℕ] · 5
  --> WrapReveal
  ((λw:X. (ΛY. λy:X → Y. y · w) [X] · (λz:X.z)) · 5↓[X:=ℕ]) ↑[X:=ℕ] 
  --> Beta
  ((ΛY. λy:X → Y. y · (5↓[X:=ℕ])) [X] · (λz:X.z)) ↑[X:=ℕ] 
  --> TyBeta
  ((λy:X → Y. y · (5↓[X:=ℕ])) ↑[Y:=X] · (λz:X.z)) ↑[X:=ℕ] 
  --> WrapReveal
  ((λy:X → Y. y · (5↓[X:=ℕ])) · ((λz:X.z)↓[Y:=X])) ↑[Y:=X] ↑[X:=ℕ]
  --> Beta
  (((λz:X.z)↓[Y:=X]) · (5↓[X:=ℕ])) ↑[Y:=X] ↑[X:=ℕ]
  --> WrapConceal
  ((λz:X.z) · (5↓[X:=ℕ]↑[Y:=X])) ↓[Y:=X] ↑[Y:=X] ↑[X:=ℕ]
  --> Drop
  ((λz:X.z) · (5↓[X:=ℕ])) ↓[Y:=X] ↑[Y:=X] ↑[X:=ℕ]
  --> Beta
  5 ↓[X:=ℕ] ↓[Y:=X] ↑[Y:=X] ↑[X:=ℕ]
  --> Cancel
  5 ↓[X:=ℕ] ↑[X:=ℕ]
  --> Cancel
  5

## Example 8   (TyWrapCncl leaks a shallower variable — a PRESERVATION COUNTEREXAMPLE)

  A closed, well-typed program that reduces to an ILL-TYPED term.  The key ingredient is
  `λf. ΛY. f [Y]`: the polymorphic argument f is applied to a type variable Y introduced
  AFTER f is bound.  (Machine-checked in de Bruijn form as strong/Scratch8.agda.)

  (ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]) [ℕ] · (ΛZ. λz:Z. z)              : ∀Y. Y→Y
  → TyBeta      (λf:(∀Z.Z→Z). ΛY. f [Y]) ↑[X:=ℕ] · (ΛZ. λz:Z. z)
  → WrapReveal  ((λf. ΛY. f [Y]) · (ΛZ. λz:Z. z)↓[X:=ℕ]) ↑[X:=ℕ]
  → Beta        (ΛY. (ΛZ. λz:Z. z)↓[X:=ℕ] [Y]) ↑[X:=ℕ]
  → TyWrapCncl  (ΛY. ((ΛZ. λz:Z. z) [Y]) ↓[X:=ℕ]) ↑[X:=ℕ]              ← ILL-TYPED

  Every line down to the redex is well-typed; the redex (ΛY. (ΛZ.λz.z)↓[X:=ℕ] [Y]) ↑[X:=ℕ]
  has type ∀Y.Y→Y.  The last term does NOT.

  Does the ill-typed term fail under the informal rules here too?  YES — for the same reason
  as the de Bruijn version.  Its conceal is  ((ΛZ.λz.z) [Y]) ↓[X:=ℕ]@(Y→Y)  at context
  X:=ℕ, Y.  The (conceal) rule types the body in the PREFIX (X:=ℕ, Y)↓X = ∅ — Y is shallower
  than X, so it is dropped from X's existential scope.  But the body (ΛZ.λz.z) [Y] mentions Y,
  so (tapp) demands ∅ ⊢ Y, which fails.  The reduct is untypable.

  What went wrong.  TyWrapCncl pushes the type argument into the sealed body:
  F [C[X:=A]] = (ΛZ.λz.z) [ Y[X:=ℕ] ] = (ΛZ.λz.z) [Y], and Y[X:=ℕ] = Y is still shallower
  than X.  So the invariant "a conceal body mentions only X-and-deeper variables" is BROKEN by
  TyWrapCncl.  The tightening that confines the sealed VALUE to X's existential scope does not
  confine the TYPE ARGUMENT at which the sealed value's ∀ is instantiated: (tapp) admits any
  well-formed C, including a variable Y outside the scope.  A sound system must also require
  the type argument of a concealed polymorphic value to lie in X's existential scope Γ↓X.

# Metatheory  (proof sketches)

Runtime contexts.
  The frames R enter reveal, conceal, and Λ bodies (□↑, □↓, Λ□) but never a λ-body, so no
  term binder is descended into.  Every context that arises therefore has only type-variable
  entries:   Δ ::= ∅ | Δ, X | Δ, X:=A   (term variables occur only when checking source terms,
  or transiently under a λ when inverting (lam)).  Contexts are marker-free.  Progress and
  preservation are stated at such runtime contexts Δ.

The prefix at work.
  A conceal body lives in the prefix Δ↓X — the variables deeper than X.  Adding or removing a
  SHALLOW entry (a reveal's X:=A, a Λ's X, or dropping the fresh variable of a reveal) leaves
  Δ↓Y unchanged for every Y deeper than that entry.  So a conceal body does not move when the
  context is extended or trimmed at the shallow end — which is why the cases below re-type
  conceal bodies almost never.  The identity used throughout is  (Δ, X:=A) ↓ X = Δ.

Supporting lemmas.
  (L1) Term substitution.  If  Γ, x:A, Θ ⊢ N : B  and  Γ ⊢ V : A  (V a value), then
       Γ, Θ ⊢ N[x:=V] : B.  The conceal case is the identity: a conceal in N on Y is typed in
       the prefix (Γ,x:A,Θ)↓Y, which drops the shallower term variable x, so x∉M and there is
       nothing to substitute.  Other cases homomorphic.  Beta uses Θ=∅.
  (L2) Revelation.  Γ,X ⊢ M:C  ⟹  Γ,X:=A ⊢ M:C  (given Γ⊢A).  Revealing an abstract X only
       widens lookup; conceals in M are on variables deeper than X (X is the freshly-bound,
       shallowest, abstract variable — nothing conceals it), and their prefixes exclude X.
  (L3) Commutation.  For X≠Z, Z∉A:  C[Z:=B][X:=A] = C[X:=A][Z:=B[X:=A]].  (Type level; used by
       the TyWrap rules.)
  (L-str) Strengthening.  Γ, X:=A ⊢ M:C  with X∉M, X∉C  ⟹  Γ ⊢ M:C  — and more generally,
       drop a whole SHALLOW suffix that M and C avoid.
  (L-scope) Value scoping.  If  Δ ⊢ V:T  (V a value) and T mentions only X-and-deeper
       variables, then V mentions only X-and-deeper variables.  (A value of a sealed-scope
       type is itself in that scope.  Needed to move a redex argument into the prefix in
       WrapConceal.  TO VERIFY.)
  (L-mark, L-exch′, and the Commute substitution lemma are gone — there is no marker, and
   Commute is gone.)

  Inversion of (conceal):  from  Γ ⊢ M↓[X:=A]@B : B  we get  Γ ∋ X:=A,  Γ ⊢ B,  and
  (Γ↓X) ⊢ M : B[X:=A].  The body is already in the prefix; there is no marker to strip.

## Preservation

Δ ⊢ M : A  (Δ runtime)  and  M -→ M′   ⟹   Δ ⊢ M′ : A.

By cases on the reduction rule.  Contexts stay marker-free runtime contexts; the only term
variable is the transient x:A from inverting (lam) in Beta, inside L1.

  δ, Beta.    Beta by L1 (Θ=∅).
  TyBeta.     Inv(tapp,tlam): Δ,X⊢V:C, Δ⊢A; result C[X:=A].  (L2) Δ,X:=A⊢V:C;
              (reveal) V↑[X:=A]@C : C[X:=A].
  WrapReveal. Inv(app,reveal): Δ,X:=A⊢F:B₁→B₂, Δ⊢W:B₁[X:=A]; result B₂[X:=A].
              The seal W↓[X:=A]@B₁ is built at Δ,X:=A; its body sits at (Δ,X:=A)↓X = Δ, where
              the expected type B₁[X:=A] is EXACTLY W's type.  So the body is W UNCHANGED — no
              shift, no weakening:  Δ,X:=A ⊢ W↓[X:=A]@B₁ : B₁;  (app) F·W↓… : B₂;
              (reveal) : B₂[X:=A].
  WrapConceal. Inv(app): Δ⊢F↓[X:=A]@(B₁→B₂):B₁→B₂, Δ⊢W:B₁; result B₂.
              Inv(conceal): Δ∋X:=A, (Δ↓X) ⊢ F : (B₁→B₂)[X:=A].
              The reduct's outer conceal is on X, body at Δ↓X; its inner reveal W↑[X:=A]@B₁
              needs (Δ↓X),X:=A ⊢ W : B₁.  B₁ (from the tightened conceal type) uses only
              X-and-deeper, and by (L-scope) so does W; so strengthen Δ⊢W:B₁ down to
              (Δ↓X),X:=A ⊢ W:B₁ (drop the part of Δ shallower than X).  Then
              (reveal) Δ↓X ⊢ W↑[X:=A]@B₁ : B₁[X:=A];  (app) with F;  (conceal) : B₂.
              [The one case that trims the argument into the prefix; L-scope licenses it.  It
               replaces the old L-mark step.]
  TyWrapRevl. Inv(tapp,reveal): Δ,X:=A⊢F:∀Y.B, Δ⊢C (X∉C).  (tapp) F[C]:B[Y:=C];
              (reveal) : (B[Y:=C])[X:=A] =(L3)= (B[X:=A])[Y:=C].  (Annotation reads B[Y:=C].)
  TyWrapCncl. Inv(tapp): Δ⊢F↓[X:=A]@(∀Y.B):∀Y.B, Δ⊢C; result B[Y:=C].
              Inv(conceal): Δ∋X:=A, (Δ↓X) ⊢ F : ∀Y.(B[X:=A]).
              (Δ↓X) ⊢ C[X:=A] (X-free);  (tapp) F[C[X:=A]] : (B[X:=A])[Y:=C[X:=A]] =(L3)=
              (B[Y:=C])[X:=A];  (conceal) Δ ⊢ …↓[X:=A]@(B[Y:=C]) : B[Y:=C].
              *** THIS CASE IS WRONG.  The step "(Δ↓X) ⊢ C[X:=A]" is UNJUSTIFIED: (tapp) only
              gives Δ⊢C, and when C mentions a variable SHALLOWER than X (revealed after X),
              C[X:=A] is not well-formed in the prefix Δ↓X.  Example 8 exhibits a closed,
              well-typed program whose TyWrapCncl step produces an untypable term.  Fixing this
              requires (tapp) on a conceal to confine C to X's existential scope.  See Ex. 8. ***
  Cancel.     Inv(reveal): Δ,X:=A⊢V↓[X:=A]@B:B; result B[X:=A].
              Inv(conceal): the body V sits at (Δ,X:=A)↓X = Δ, typed B[X:=A].  So Δ⊢V:B[X:=A]
              = result, DIRECTLY — no strengthening, no shift; the body already lives in the
              post-Cancel context.
  Drop (X≠Y, X∉V↓[Y:=B]@C).  Inv(reveal): Δ,X:=A⊢V↓[Y:=B]@C:C; result C[X:=A].
              Y is deeper than the fresh X, so the conceal body sits at (Δ,X:=A)↓Y = Δ↓Y,
              untouched by dropping the reveal; and X∉C ⟹ C[X:=A]=C.  So Δ⊢V↓[Y:=B]@C:C =
              result — V and C unchanged.
  RevealCnst. k↑[X:=A]@B → k.
  ξ.          M→M′ ⟹ R[M′] by IH on M at the frame's context (□↑ adds X:=A; □↓ takes the
              prefix Δ↓X; Λ□ adds abstract X; the rest keep Δ), then re-apply the frame.

## Progress.

Δ ⊢ M : A  (Δ runtime)   ⟹   M is a value  or  M -→ M′.

  Induction on the typing derivation.  Canonical forms of values at elimination types:
       A→B :  λx:_.N  |  G↑[…]  |  V↓[…]
       ∀X.C:  ΛX.V    |  G↑[…]  |  V↓[…]
  Cases on M:
    k, λ           : values.    x : impossible (no term variables in Δ).
    M ⊕ N          : reduce a non-value operand by ξ; if both are values they are
                     numerals n₁,n₂ reduce via δ-rule.
    L · M          : reduce a non-value part by ξ; both values ⟹ L is λ (Beta) /
                     G↑ (WrapReveal) / V↓ (WrapConceal).
    L [A]          : likewise; L value ⟹ Λ (TyBeta) / G↑ (TyWrapRevl) / V↓ (TyWrapCncl).
    M ↑[X:=A]      : M not a value ⟹ ξ.  M = V value:
                       V=k → RevealCnst;  V=G → G↑[X:=A] is a value;
                       V=V′↓[Y:=B] → Y=X ⟹ Cancel (consistency forces B=A);
                       X≠Y ⟹ Drop.  Here X∉V′↓[Y:=B] is AUTOMATIC: the conceal on Y is typed
                       in a prefix that excludes the freshly-revealed X (X is shallowest, Y is
                       deeper), so nothing under the seal can mention X.  So reveal-on-conceal
                       is always Cancel or Drop — never stuck, and Commute never arises.
    M ↓[X:=A]      : M not a value ⟹ ξ (body at Δ↓X).  M a value ⟹ M↓[X:=A] is a value.
    Λ X. N         : N not a value ⟹ ξ.  N is a value ⟹ ΛX.N is a value.

# Why the earlier conceal-b design failed  (kept as a cautionary record)

  An earlier (conceal) — call it conceal-b — typed the body without X by *deleting* the
  binding rather than blocking it:

     (conceal-b) Γ₁, Γ₂ ⊢ M : B[X:=A]     X ∉ Γ₂
                 -------------------------------
                 Γ₁, X:=A, Γ₂ ⊢ M↓[X:=A]@B : B

  Example 6 breaks it.  The reduction is exactly as above:

     (ΛX. λw:ℕ. (ΛY. w) [X→X]) [ℕ] · 5
     → TyBeta      (λw:ℕ. (ΛY. w) [X→X]) ↑[X:=ℕ] · 5
     → WrapReveal  ((λw:ℕ. (ΛY. w) [X→X]) · 5↓[X:=ℕ]) ↑[X:=ℕ]
     → Beta        ((ΛY. 5↓[X:=ℕ]) [X→X]) ↑[X:=ℕ]
     → TyBeta      (5↓[X:=ℕ] ↑[Y:=X→X]) ↑[X:=ℕ]        ← ill-typed under conceal-b

  At the last line the seal 5↓[X:=ℕ] sits at context X:=ℕ, Y:=(X→X).  conceal-b must type
  its body by deleting X, at Γ₁,Γ₂ = ∅, {Y:=(X→X)} — but that context is ill-formed: Y's
  representation X→X now dangles.  Equivalently the side condition X ∉ Γ₂ fails, since
  X ∈ (Y:=(X→X)).  So conceal-b rejects this term even though it runs fine (Drop, Cancel → 5).

  The failure was traced to TyBeta: revealing Y:=(X→X) injects X into the seal's Γ₂, and the
  supposed lemma "revealing a variable preserves typing" (L2) is false under conceal-b.

  The end marker fixes it: (conceal) blocks X for the body but keeps X:=ℕ in the context, so
  Y:=(X→X) stays well-formed and the body 5 (which never mentions X) type-checks.




# De Bruijn formalization and the tightened conceal marker  (what we learned)

  NOTE: this section records an INTERMEDIATE design — a non-counting conceal marker
  whose lookup was tightened to  n < X.  It is SUPERSEDED by the prefix approach above
  (no marker; the conceal body is typed in Δ↓X).  The prefix approach is the tightened
  marker "compiled away": the same variables are in scope, but the body is stored over
  the prefix so nothing needs blocking, shifting, or subtracting.  Kept here because the
  reasoning that led to the tightening (below) is what justifies discarding the shallower
  context in the prefix rule.

  We mechanized this calculus in Agda under SystemF/agda/strong/ using de Bruijn
  indices: Types / TypeSubst (types and their substitution), Context (the two
  contexts and their lookups), Weakening (well-formedness / weakening lemmas),
  Terms, Typing (Δ ∣ Γ ⊢ M ⦂ A), Reduction (values, the rules, and -↠), and
  Examples (Examples 1–6 as machine-checked typing derivations and reduction
  sequences).  Two design points sharpened along the way.

## Representation well-formedness at a conceal

  The (conceal) rule types its body at Γ,↓X against B[X:=A], so to prove
  regularity/preservation we need the representation A — recovered by the lookup
  Γ ∋ X:=A — to be well-formed in the current context.  Lookup alone did NOT
  guarantee this originally: a marker ↓Y could sit between a use and a revealed
  variable whose representation mentions a *concealed* variable (the "dangerous
  shape": Y:=(X→X) with X concealed, so looking up Y returns X→X while X is
  blocked).  We first fixed this with an inductive predicate, ConcealCtx Δ X,
  generated from the context shape when a conceal is born (WrapReveal) plus one
  constructor for each way that context changes under reduction, and proved it
  implies Δ ⊢ A.

## The insight: a sealed value lives in its existential scope

  We then asked whether a value that uses X can be sealed on a *different*
  variable Y — the shape that would trigger Commute (V↓[Y:=B]↑[X:=A] with X ∈ V).
  No closed program produces it.  The reason is an invariant: a sealed value can
  only depend on type variables revealed BEFORE the sealed one — it can never
  reference a variable revealed later.  (WrapReveal seals a value on the very
  variable it just revealed; pushing a conceal under Λ can only involve the
  freshly-bound variable, which the sealed value cannot mention.)  Equivalently,
  at a conceal on X the body and annotation mention only X and variables deeper
  than X.

## The tightened marker

  This invariant is captured by ONE change to type-variable lookup: a marker ↓X
  blocks not just X but every variable revealed after X.  With de Bruijn indices
  (index 0 = most-recently-revealed), the marker-skip rules become

      skip-cncl : n < X → Δ ∋tv   X       → (cncl n ∷ Δ) ∋tv   X          (was n ≢ X)
      skip-cncl : n < X → Δ ∋ X := A      → (cncl n ∷ Δ) ∋ X := A         (was n ≢ X)

  so a conceal body sees exactly the variables in its existential scope.  (The
  condition is natural with de Bruijn indices, which record the reveal order; a
  name-based presentation would have to track that order explicitly.)

  Consequences, all machine-checked:

  - Representation lookup now yields a well-formed type directly:
        ⊢ Δ  and  Δ ∋ X := A   give   Δ ⊢ A        (Agda: ∋:=-⊢).
    Any marker skipped en route to X conceals something shallower than X, while A
    mentions only variables deeper than X, so no marker can block A.  This
    SUBSUMES ConcealCtx, which we deleted (along with its premise on (conceal)).

  - The "dangerous shape" is now impossible to even state: looking up a variable
    past a marker that conceals a deeper variable no longer type-checks.

  - The Commute redex is rejected statically:
        (λx:X.x)↓[Y:=ℕ]@(X→X) ↑[X:=ℕ]
    no longer type-checks, because the body λx:X.x would have to reference X,
    which is shallower than the sealed Y and thus blocked by ↓Y.  So the Commute
    reduction rule is dead code — no well-typed term takes that branch — pending
    its removal once Preservation confirms this.
