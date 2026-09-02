Strong System F

This version of System F keep tight control over where type variables
can appear and where they cannot. The name "strong" alludes to the
fact that weakening with respect to type variables is not used.

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

  Γ ::= ∅ | Γ, x:A | Γ, X | Γ, X:=A | Γ, ↓X

    ↓X   end marker: "X is sealed off here".  It blocks lookup of X past it, but leaves
         X's binding (and anything in Γ depending on X) in place.

# Type-variable lookup   Γ ∋ X   /   Γ ∋ X:=A     (Q ranges over the query, X or X:=A)

  (∋-tvar)   Γ, X    ∋ X
  (∋-rvar)   Γ, X:=A ∋ X:=A
  (∋-var)    Γ ∋ Q     ⟹  Γ, x:A ∋ Q
  (∋-tskip1) Γ ∋ X     ⟹  Γ, Y   ∋ X          (Y ≠ X)
  (∋-tskip2) Γ ∋ X:=A  ⟹  Γ, Y   ∋ X:=A       (Y ≠ X)
  (∋-rskip1) Γ ∋ X     ⟹  Γ, Y:=A ∋ X         (Y ≠ X)
  (∋-rskip2) Γ ∋ X:=A  ⟹  Γ, Y:=A ∋ X:=A      (Y ≠ X)
  (∋-mskip1) Γ ∋ X     ⟹  Γ, ↓Y ∋ X           (Y ≠ X)
  (∋-mskip2) Γ ∋ X:=A  ⟹  Γ, ↓Y ∋ X:=A        (Y ≠ X)
  
  Note: There is no rule for  Γ, ↓X ∋ X  or  Γ, ↓X ∋ X:=A 
  because the marker ↓X blocks X

# Term-variable lookup   x:A ∈ Γ

  (∈-here)   x:A ∈ Γ, x:A
  (∈-var)    x:A ∈ Γ  ⟹  x:A ∈ Γ, y:B       (y ≠ x)
  (∈-tvar)   x:A ∈ Γ  ⟹  x:A ∈ Γ, Y
  (∈-rvar)   x:A ∈ Γ  ⟹  x:A ∈ Γ, Y:=B

  Note: There is deliberately no rule for  Γ, ↓Y : every marker ↓Y blocks *every* term
  variable to its left.  So a term variable is visible iff no ↓ marker sits between its
  binder and its use.  (Contrast type-variable lookup, where ↓Y blocks only Y and other
  type variables skip past via ∋-mskip.)  A marker seals the term level entirely — the
  conceal body typed at Γ,↓X is a self-contained value, using only the type variables of Γ
  and the term variables it binds itself.  Source programs have no markers, so this is
  ordinary lookup there; the blocking bites only at runtime.

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
  (ctx-cncl)   ⊢ Γ               ⇒ ⊢ Γ, ↓X

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

  (conceal) Γ ∋ X:=A   Γ ⊢ B   Γ, ↓X ⊢ M : B[X:=A]
            --------------------------------------
            Γ ⊢ M↓[X:=A]@B : B

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

  The reveal/conceal asymmetry mirrors lookup: a reveal ↑[X:=A] leaves term variables
  visible, so substitution descends into its body; a conceal ↓[X:=A] sits under a marker ↓X
  that blocks every term variable, so a well-typed conceal body is term-closed and
  substitution is the identity on it.  Taking that as the defining clause (rather than
  recursing, which would give the same result) makes seals inert by construction and matches
  the de Bruijn port, where a substitution for an outer term variable does not reach past the
  marker into the body's own variable scope.

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
  (Commute)     V ↓[Y:=B]@C ↑[X:=A]@D -→ (V ↑[X:=A[Y:=B]]@C[Y:=B]) ↓[Y:=B]@C[X:=A]  if X ≠ Y and X ∈ V↓[Y:=B]
  (RevealCnst)  k ↑[X:=A]@B           -→ k
  (ξ)           R[M]                  -→ R[M′]      if M -→ M′


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


# Metatheory  (proof sketches)

Runtime contexts.
  The frames R enter reveal, conceal, and Λ bodies (□↑, □↓, Λ□) but never a λ-body, so no
  term binder is descended into.  Every context that arises therefore has only type-variable
  entries:   Δ ::= ∅ | Δ, X | Δ, X:=A | Δ, ↓X   (term variables occur only when checking
  source terms, or transiently under a λ when inverting (lam)).  Both progress and
  preservation are stated at such runtime contexts Δ: since no reduction fires under a λ,
  the redex always sits at a term-variable-free Δ.  (This matters now that a marker blocks
  every term variable: a "preservation for any Γ" claim would fail — e.g. WrapConceal on a
  W that uses a term variable of Γ — but that configuration is never reachable.)

Supporting lemmas.
  (L1) Term substitution.  Let Θ be *marker-free* (contains no ↓Z entry).  If
       Γ, x:A, Θ ⊢ N : B  and  Γ ⊢ V : A  (V a value), then  Γ, Θ ⊢ N[x:=V] : B.
       The two-sided context is needed for the induction (descending a binder grows Θ), and
       Θ marker-free is the invariant the induction maintains: substitution follows only the
       term-visible spine of N — under λ, Λ, reveal (these keep term variables in scope,
       growing Θ by y:B′, X, X:=A′) — and stops at every conceal (the ↓ clause is identity).
       Hence x is never separated from a use by a marker, and V weakens through Θ by L4
       (no marker to block it).
       • var x:  returns V; weaken Γ⊢V:A to Γ,Θ⊢V:A (L4).
       • conceal N=M↓[Y:=D]@E:  identity.  Its body sits at Γ,x:A,Θ,↓Y, where ↓Y blocks x,
         so x∉M; strengthen x:A away to get Γ,Θ,↓Y ⊢ M and reapply (conceal) at Γ,Θ.
         (Γ∋Y:=D survives dropping the term variable x, since ∋ skips term variables.)
       • other cases: homomorphic; Θ stays marker-free.
       Beta uses the Θ=∅ instance:  Δ,x:A ⊢ N:B  and  Δ ⊢ V:A  ⟹  Δ ⊢ N[x:=V]:B.
  (L2) Revelation.  Γ,X ⊢ M:C  ⟹  Γ,X:=A ⊢ M:C   (given Γ ⊢ A).  Robust now: a conceal
       inside M *blocks* (does not delete) its variable, so revealing X cannot strand it.
  (L3) Commutation.  For X≠Z with Z ∉ A:  C[Z:=B][X:=A] = C[X:=A][Z:=B[X:=A]].
  (L-sub) Substitution lemma.  For X≠Y with X ∉ B:
       C[Y:=B][X:=A[Y:=B]] = C[X:=A][Y:=B].   (No X∉A condition — the rep A[Y:=B] on
       the left absorbs it; checked variable-by-variable.  Used by Commute.)
  (L4) Weakening (extend the context on the right).
  (L-mark) Weaken-through-marker.  For term-closed M:  Γ ⊢ M:C  ⟹  Γ, ↓X, X:=A ⊢ M:C.  Net
       X-accessibility is unchanged (the trailing X:=A re-opens X past ↓X) and no type
       variable is affected; term-closedness is required because ↓X blocks every term
       variable of Γ.  Only ever applied to a redex argument W, which is term-closed.
  (L-str) Strengthening.  Γ, X:=A ⊢ M:C  with X ∉ M, X ∉ C  ⟹  Γ ⊢ M:C.  A body typed
       under a marker ↓X has X ∉ M for free (any use of X would be blocked), so this also
       covers removing an X:=A adjacent to a ↓X.
  (L-exch′) Exchange-with-reduction.  Γ, X:=A, ↓Y ⊢ V : T   with Γ ∋ Y:=B, X≠Y, X∉B  ⟹
       Γ, ↓Y, X:=A[Y:=B] ⊢ V : T.   Move X:=A rightward past ↓Y, reducing its
       representation by Y:=B.  Sound because: (i) Y ∉ A[Y:=B], so Γ,↓Y ⊢ A[Y:=B] and the
       reordered context is well-formed; (ii) X, Y and every other type variable have the
       same accessibility on both sides (Y blocked by ↓Y, X reachable); (iii) the
       representation A is opaque to V's derivation — V queries only variable accessibility
       and the annotation types it itself carries — so replacing A by A[Y:=B] leaves it
       unchanged.
  (L5 is gone.)

  Inversion of (conceal):  Γ ∋ X:=A  and  Γ, ↓X ⊢ M : B[X:=A].  No context split, no
  side-condition — the marker keeps all of Γ in scope for well-formedness while blocking
  X for the body M.

## Preservation

Δ ⊢ M : A  (Δ runtime)  and  M -→ M′   ⟹   Δ ⊢ M′ : A.

By cases on the reduction rule.  Every displayed context is a runtime context (Δ extended
only by X, X:=A, ↓X); the sole term variable to appear is the transient x:A introduced by
inverting (lam) in the Beta case, which lives inside L1.

  δ, Beta.    As before (Beta by L1, at the Θ=∅ instance: Δ,x:A ⊢ N:B and Δ⊢V:A ⟹ Δ⊢N[x:=V]:B).
  TyBeta.     Inv(tapp,tlam): Δ,X⊢V:C, Δ⊢A; result C[X:=A].  (L2) Δ,X:=A⊢V:C;
              (reveal) V↑[X:=A]@C : C[X:=A].   [L2 holds even when V contains conceals.]
  WrapReveal. Inv(app,reveal): Δ,X:=A⊢F:B₁→B₂, Δ⊢W:B₁[X:=A]; result B₂[X:=A].
              (conceal) Δ,X:=A ∋ X:=A ✓; body W at Δ,X:=A,↓X (Δ⊢W:B₁[X:=A] weakens there,
              X∉W).  So Δ,X:=A⊢W↓[X:=A]@B₁:B₁; (app) F·W↓…:B₂; (reveal) : B₂[X:=A].
  WrapConceal. Inv(app): Δ⊢F↓[X:=A]@(B₁→B₂):B₁→B₂, Δ⊢W:B₁; result B₂.
              Inv(conceal): Δ∋X:=A, Δ,↓X ⊢ F : B₁[X:=A]→B₂[X:=A].
              (L-mark) Δ,↓X,X:=A ⊢ W:B₁  (W term-closed, as Δ has no term variables);
              (reveal) Δ,↓X ⊢ W↑[X:=A]@B₁ : B₁[X:=A];
              (app) Δ,↓X ⊢ F·W↑[X:=A]@B₁ : B₂[X:=A];  (conceal) Δ ⊢ (…)↓[X:=A]@B₂ : B₂.  ✓
              [↓X bars F from X; the inner reveal re-opens X for W past the marker.  No
               strengthening, no L-exch, no side-condition — this is what fixes the case.]
  TyWrapRevl. (no conceal) Inv(tapp,reveal): Δ,X:=A⊢F:∀Y.B, Δ⊢C (X∉C).  (tapp) F[C]:B[Y:=C];
              (reveal) : (B[Y:=C])[X:=A] =(L3,X∉C)= (B[X:=A])[Y:=C] = result.
              (Result annotation should read B[Y:=C].)
  TyWrapCncl. Inv(tapp): Δ⊢F↓[X:=A]@(∀Y.B):∀Y.B, Δ⊢C; result B[Y:=C].
              Inv(conceal): Δ∋X:=A, Δ,↓X ⊢ F : ∀Y.(B[X:=A]).
              Δ,↓X ⊢ C[X:=A] (X-free);  (tapp) F[C[X:=A]] : (B[X:=A])[Y:=C[X:=A]] =(L3)= (B[Y:=C])[X:=A];
              (conceal) Δ ⊢ F[C[X:=A]]↓[X:=A]@(B[Y:=C]) : B[Y:=C] = result.
              (Conceal annotation should read B[Y:=C].)
  Cancel.     Inv(reveal): Δ,X:=A⊢V↓[X:=A]@B:B; result B[X:=A].
              Inv(conceal): Δ,X:=A ∋ X:=A;  Δ,X:=A,↓X ⊢ V : B[X:=A].  Under ↓X, X∉V, and
              B[X:=A] is X-free, so (L-str) Δ ⊢ V : B[X:=A] = result.
  Drop (X≠Y, X∉V↓[Y:=B]@C).  Inv(reveal): Δ,X:=A⊢V↓[Y:=B]@C:C; result C[X:=A].
              X ∉ the conceal value ⟹ X∉C ⟹ C[X:=A]=C, and (L-str) Δ⊢V↓[Y:=B]@C:C = result.
  Commute (X≠Y, X∈V↓[Y:=B]).  Redex V↓[Y:=B]@C ↑[X:=A]@D; well-typed ⟹ D=C (the reveal's
              annotation is the type of its body, and the conceal body has type C).
              Inv(reveal): Δ,X:=A ⊢ V↓[Y:=B]@C : C,  Δ⊢A;  result C[X:=A].
              Inv(conceal): Δ,X:=A ∋ Y:=B  (so Δ∋Y:=B; X≠Y ⟹ Y:=B sits left of X:=A in Δ,
              hence X∉B);  Δ,X:=A,↓Y ⊢ V : C[Y:=B].
              Reduct (V↑[X:=A′]@C[Y:=B]) ↓[Y:=B]@C[X:=A],  where A′ = A[Y:=B] (so Y∉A′).
              (L-exch′) from Δ,X:=A,↓Y ⊢ V : C[Y:=B] and Δ∋Y:=B, X∉B:
                        Δ,↓Y,X:=A′ ⊢ V : C[Y:=B]   (Y∉A′ makes Δ,↓Y⊢A′, so the exchange —
                        which previously stuck when A mentioned Y — now always goes through).
              (reveal) Δ,↓Y ⊢ V↑[X:=A′]@C[Y:=B] : (C[Y:=B])[X:=A′].
              (L-sub, X≠Y, X∉B):  (C[Y:=B])[X:=A[Y:=B]] = (C[X:=A])[Y:=B].
              (conceal) Δ∋Y:=B, body type (C[X:=A])[Y:=B] = ann[Y:=B] with ann=C[X:=A]:
                        Δ ⊢ (…)↓[Y:=B]@C[X:=A] : C[X:=A] = result.  ✓
              [RESOLVED: floating A′=A[Y:=B] (not A) under ↓Y removes Y from the rep, so the
               exchange and the type match hold with no A-mentions-Y side condition.  When
               Y∉A this is A′=A and the old reduct.]
  RevealCnst. k↑[X:=A]@B → k.
  ξ.          M→M′ ⟹ R[M′] by IH on M at the frame's context (□↑ adds X:=A; □↓ adds ↓X;
              Λ□ adds abstract X; the rest keep Δ — each is again a runtime context), then
              re-apply the frame.

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
                       X≠Y ⟹ Drop (if X∉V′↓[Y:=B]) or Commute (if X∈V′↓[Y:=B]).
                       These three cover reveal-on-conceal, so it never sticks.
    M ↓[X:=A]      : M not a value ⟹ ξ (body at Γ,↓X).  M a value ⟹ M↓[X:=A] is a value.
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


