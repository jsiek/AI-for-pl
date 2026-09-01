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

  (conceal) Γ ∋ X:=A     Γ, ↓X ⊢ M : B[X:=A]
            ---------------------------------
            Γ ⊢ M↓[X:=A]@B : B

# Values

  F ::= G | F ↓[X:=A]@B
  G ::= λx:A. N | ΛX.V | G ↑[X:=A]@B
  V,W ::= k | F | V ↓[X:=A]@B

# Frames

  R ::= □ ⊕ M | V ⊕ □ | □ · M | V · □ | □ ↑[X:=A]@B | □ ↓[X:=A]@B | □ @B[A] | Λ □

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
  (L1) Term substitution.  Γ,x:A ⊢ N:B and Γ ⊢ V:A  ⟹  Γ ⊢ N[x:=V]:B.  The conceal case is
       trivial: a conceal body of N is typed under a ↓Y that blocks x, so x∉body, the
       substitution skips it (seals are inert), and the blocked x:A strengthens away.
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

Γ ⊢ M : A  and  M -→ M′   ⟹   Γ ⊢ M′ : A.

By cases on the reduction rule.

  δ, Beta.    As before (Beta by L1).
  TyBeta.     Inv(tapp,tlam): Γ,X⊢V:C, Γ⊢A; result C[X:=A].  (L2) Γ,X:=A⊢V:C;
              (reveal) V↑[X:=A]@C : C[X:=A].   [L2 holds even when V contains conceals.]
  WrapReveal. Inv(app,reveal): Γ,X:=A⊢F:B₁→B₂, Γ⊢W:B₁[X:=A]; result B₂[X:=A].
              (conceal) Γ,X:=A ∋ X:=A ✓; body W at Γ,X:=A,↓X (Γ⊢W:B₁[X:=A] weakens there,
              X∉W).  So Γ,X:=A⊢W↓[X:=A]@B₁:B₁; (app) F·W↓…:B₂; (reveal) : B₂[X:=A].
  WrapConceal. Inv(app): Γ⊢F↓[X:=A]@(B₁→B₂):B₁→B₂, Γ⊢W:B₁; result B₂.
              Inv(conceal): Γ∋X:=A, Γ,↓X ⊢ F : B₁[X:=A]→B₂[X:=A].
              (L-mark) Γ,↓X,X:=A ⊢ W:B₁;  (reveal) Γ,↓X ⊢ W↑[X:=A]@B₁ : B₁[X:=A];
              (app) Γ,↓X ⊢ F·W↑[X:=A]@B₁ : B₂[X:=A];  (conceal) Γ ⊢ (…)↓[X:=A]@B₂ : B₂.  ✓
              [↓X bars F from X; the inner reveal re-opens X for W past the marker.  No
               strengthening, no L-exch, no side-condition — this is what fixes the case.]
  TyWrapRevl. (no conceal) Inv(tapp,reveal): Γ,X:=A⊢F:∀Y.B, Γ⊢C (X∉C).  (tapp) F[C]:B[Y:=C];
              (reveal) : (B[Y:=C])[X:=A] =(L3,X∉C)= (B[X:=A])[Y:=C] = result.
              (Result annotation should read B[Y:=C].)
  TyWrapCncl. Inv(tapp): Γ⊢F↓[X:=A]@(∀Y.B):∀Y.B, Γ⊢C; result B[Y:=C].
              Inv(conceal): Γ∋X:=A, Γ,↓X ⊢ F : ∀Y.(B[X:=A]).
              Γ,↓X ⊢ C[X:=A] (X-free);  (tapp) F[C[X:=A]] : (B[X:=A])[Y:=C[X:=A]] =(L3)= (B[Y:=C])[X:=A];
              (conceal) Γ ⊢ F[C[X:=A]]↓[X:=A]@(B[Y:=C]) : B[Y:=C] = result.
              (Conceal annotation should read B[Y:=C].)
  Cancel.     Inv(reveal): Γ,X:=A⊢V↓[X:=A]@B:B; result B[X:=A].
              Inv(conceal): Γ,X:=A ∋ X:=A;  Γ,X:=A,↓X ⊢ V : B[X:=A].  Under ↓X, X∉V, and
              B[X:=A] is X-free, so (L-str) Γ ⊢ V : B[X:=A] = result.
  Drop (X≠Y, X∉V↓[Y:=B]@C).  Inv(reveal): Γ,X:=A⊢V↓[Y:=B]@C:C; result C[X:=A].
              X ∉ the conceal value ⟹ X∉C ⟹ C[X:=A]=C, and (L-str) Γ⊢V↓[Y:=B]@C:C = result.
  Commute (X≠Y, X∈V↓[Y:=B]).  Redex V↓[Y:=B]@C ↑[X:=A]@D; well-typed ⟹ D=C (the reveal's
              annotation is the type of its body, and the conceal body has type C).
              Inv(reveal): Γ,X:=A ⊢ V↓[Y:=B]@C : C,  Γ⊢A;  result C[X:=A].
              Inv(conceal): Γ,X:=A ∋ Y:=B  (so Γ∋Y:=B; X≠Y ⟹ Y:=B sits left of X:=A in Γ,
              hence X∉B);  Γ,X:=A,↓Y ⊢ V : C[Y:=B].
              Reduct (V↑[X:=A′]@C[Y:=B]) ↓[Y:=B]@C[X:=A],  where A′ = A[Y:=B] (so Y∉A′).
              (L-exch′) from Γ,X:=A,↓Y ⊢ V : C[Y:=B] and Γ∋Y:=B, X∉B:
                        Γ,↓Y,X:=A′ ⊢ V : C[Y:=B]   (Y∉A′ makes Γ,↓Y⊢A′, so the exchange —
                        which previously stuck when A mentioned Y — now always goes through).
              (reveal) Γ,↓Y ⊢ V↑[X:=A′]@C[Y:=B] : (C[Y:=B])[X:=A′].
              (L-sub, X≠Y, X∉B):  (C[Y:=B])[X:=A[Y:=B]] = (C[X:=A])[Y:=B].
              (conceal) Γ∋Y:=B, body type (C[X:=A])[Y:=B] = ann[Y:=B] with ann=C[X:=A]:
                        Γ ⊢ (…)↓[Y:=B]@C[X:=A] : C[X:=A] = result.  ✓
              [RESOLVED: floating A′=A[Y:=B] (not A) under ↓Y removes Y from the rep, so the
               exchange and the type match hold with no A-mentions-Y side condition.  When
               Y∉A this is A′=A and the old reduct.]
  RevealCnst. k↑[X:=A]@B → k.
  ξ.          M→M′ ⟹ R[M′] by IH on M at the frame's context (□↑ adds X:=A; □↓ adds ↓X;
              Λ□ adds abstract X; the rest keep Γ), then re-apply the frame.

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


