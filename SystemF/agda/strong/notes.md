Strong System F

This version of System F keeps tight control over where type variables
can appear and where they cannot. The name "strong" alludes to the
fact that weakening with respect to type variables is not used.

The runtime device is a single **combined boundary** `M ⟪ Θ , B₀ ⟫`: one wrapper carrying a
list Θ of reveals and conceals together with one boundary type B₀.  (An earlier design used a
separate wrapper per revealed/concealed variable, `↑[X:=A]@B` / `↓[X:=A]@B`; it is unsound —
see "Old per-variable design" and the historical Example 8 below.)

# TODO

* land `Wrap` (the application rule, R2 of notes/BoundaryRules.md) in the Agda; it is the
  only rule of the table below that is still only proposed.
* close progress.  The one open obstruction is rep inconsistency (`bad`, Metatheory §Progress):
  (env) cannot relate a conceal's rep to the rep of the reveal that binds the same variable.
* rename the Agda constructors to the names used here (Beta, TyBeta, TyWrap, Wrap, ξ).

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

  Source terms carry NO boundaries.  Boundaries arise only from reduction, so the source
  typing rules below are exactly System F's and are unchanged by this design.

# Runtime Terms (with variables as names)

  L,M,N ::= ... | M ⟪ Θ , B₀ ⟫

  Θ ::= ∅ | ↑X:=A , Θ | ↓Y:=A , Θ        (a boundary: a list of reveals and conceals)

  * a reveal   ↑X:=A :  X is a fresh **internal** abstract type variable; its representation
                        A is read in the **exterior** of the whole boundary.
  * a conceal  ↓Y:=A :  Y is an **exterior** type variable; its representation A is read in
                        the **interior** of the whole boundary.

  Reads left to right as "most recently added first": the leftmost entry is the one a
  reduction step just pushed on, and the reveal variables are listed in that order.

  B₀ is the **boundary type**.  It is written over the *boundary frame* — the reveal variables
  of Θ together with the exterior context — and the internal and external types of the wrapper
  are its two projections (below).  There is no consistency premise relating two annotations:
  there is only one B₀.

# Contexts

  Γ ::= ∅ | Γ, x:A | Γ, X | Γ, X:=A

  As before, `X` is an abstract type variable and `X:=A` a revealed one.  There is no conceal
  marker: a conceal restricts the *interior context* (below) instead of extending Γ.
  (The Agda splits Γ into a type context Δ and a term context Γₜ, judgment `Δ ∣ Γₜ ⊢ M ⦂ A`;
  runtime contexts are term-variable-free anyway, so the merged Γ used here loses nothing.)

# Context Prefix     Γ ↓ X

  The part of Γ deeper than X: everything bound BEFORE X's binder, dropping X itself and
  everything shallower (bound after X).  This is X's existential scope.  Used to build the
  interior context of a boundary that conceals X.

  Γ, X ↓ X     = Γ
  Γ, Y ↓ X     = Γ ↓ X    (Y ≠ X)
  Γ, X:=A ↓ X  = Γ
  Γ, Y:=A ↓ X  = Γ ↓ X    (Y ≠ X)
  Γ, x:A ↓ X   = Γ ↓ X

  Because the kept part Γ↓X is bound before X, nothing in it mentions X — so Γ↓X is
  well-formed on its own, with no dangling reference to the concealed variable.  (This is
  exactly what the failed conceal-b design got wrong: it kept the SHALLOWER part too, where
  entries like Y:=(X→X) do mention X.)

# The interior context     Γ ⇈ Θ

  A boundary's body is typed in the *interior* context.  ONE restriction is taken, at the
  DEEPEST concealed variable, and the reveal variables are added on top:

     Γ ⇈ Θ  =  (Γ ↓ Y★) , X₁ , … , X_r        where  Y★ = the deepest variable concealed
                                                     by Θ (if Θ conceals nothing, Γ↓Y★ = Γ)
                                                     X₁ … X_r = the reveal variables of Θ,
                                                     fresh and abstract

  In words: everything from the shallowest end of Γ down to and including Y★ is dropped —
  those variables are **blocked**, they have no interior image — and the reveal variables are
  appended (so they are the shallowest interior variables, in Θ's order).

  Taking a SINGLE restriction at the deepest conceal (rather than one restriction per conceal,
  progressively) is what keeps a conceal of a shallow variable from over-dropping a deeper
  one; see the multiple-conceal example at the end of Boundary.agda.

  Blocked ≠ concealed.  A variable that Θ drops but does NOT conceal is blocked: it has no
  interior image at all, and B₀ may not name it (the scope premise of (env)).  A concealed
  variable is also absent from the interior, but B₀ *may* name it, because the internal face
  replaces it by its representation.

# The two faces of B₀

  external face   B₀[ρΘ]     read in the exterior Γ:
                             each reveal variable X ↦ its representation A;
                             every exterior variable (concealed or not) passes through.

  internal face   B₀[γΘ]     read in the interior Γ ⇈ Θ:
                             each reveal variable passes through (it IS an interior variable);
                             each concealed variable Y ↦ its representation A (read in the
                             interior, so it may itself mention reveal variables);
                             each kept exterior variable ↦ itself.

  Both faces come from one B₀, which is why (env) needs no consistency premise.

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

  Note: a boundary body uses no term variables.  Boundaries appear only at runtime, where Γ is
  term-variable-free (no reduction fires under a λ), and (env) types the body with an EMPTY
  term context.  So substitution never reaches into a boundary (see Term-variable substitution
  below).  Source programs have no boundaries, so this is ordinary lookup there.

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

# Well-formed Boundaries   Γ ∣ Ψ ⊢ Θ        (Γ the exterior, Ψ = Γ ⇈ Θ the interior)

  Each representation is read on the side it belongs to: a reveal's outside, a conceal's
  inside.

  (bwf-∅)                                                   ⟹  Γ ∣ Ψ ⊢ ∅
  (bwf-↑)   Γ ⊢ A      Γ ∣ Ψ ⊢ Θ                            ⟹  Γ ∣ Ψ ⊢ ↑X:=A , Θ
  (bwf-↓)   Γ ∋ Y      Ψ ⊢ A      Γ ∣ Ψ ⊢ Θ                 ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

# Boundary-type scope   Θ ; Γ ⊢ᵒᵏ B₀

  B₀ is well-scoped over the boundary frame when it names no BLOCKED variable: reveal
  variables are fine, kept exterior variables are fine, concealed exterior variables are fine
  (the internal face resolves them), and a dropped-but-not-concealed variable is not.
  Structural, with ∀-bound variables always accessible:

  (sc-var)  X is a reveal variable, a kept variable, or a concealed variable  ⟹ Θ;Γ ⊢ᵒᵏ X
  (sc-ℕ) (sc-𝔹)                                                              ⟹ Θ;Γ ⊢ᵒᵏ ℕ , 𝔹
  (sc-fun)  Θ;Γ ⊢ᵒᵏ A    Θ;Γ ⊢ᵒᵏ B                                           ⟹ Θ;Γ ⊢ᵒᵏ A→B
  (sc-all)  Θ;(Γ,Z) ⊢ᵒᵏ A                                                    ⟹ Θ;Γ ⊢ᵒᵏ ∀Z.A

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

  (env)     Γ ∣ (Γ⇈Θ) ⊢ Θ      Θ;Γ ⊢ᵒᵏ B₀      Γ⇈Θ ⊢ M : B₀[γΘ]
            ---------------------------------------------------
            Γ ⊢ M ⟪ Θ , B₀ ⟫ : B₀[ρΘ]

    Three premises: the boundary is well-formed (each rep on its own side); B₀ names no
    blocked variable; and the body is typed IN THE INTERIOR at the internal face.  The
    conclusion is at the external face.  The body's term context is empty.

    (env) subsumes the old (reveal) and (conceal) rules: a reveal-only Θ = ↑X:=A gives
    interior Γ,X, internal face B₀ and external face B₀[X:=A] — the old (reveal); a
    conceal-only Θ = ↓X:=A gives interior Γ↓X, internal face B₀[X:=A] and external face B₀ —
    the old (conceal).  The point of combining them is that a conceal's body can still see a
    reveal's fresh variable, which is exactly what the old design could not express.

# Values

  G     ::= λx:A. N | ΛX.V
  V,W   ::= k | G | V ⟪ Θ , B₀ ⟫

  A wrapped value is a value, whatever Θ is — including a wrapped constant.  (The old
  RevealCnst rule, which unwrapped a constant, is gone.)

# Frames

  R ::= □ ⊕ M | V ⊕ □ | □ · M | V · □ | □ @B[A] | Λ □ | □ ⟪ Θ , B₀ ⟫

# Term-variable substitution   N[x := V]     (V a value)

  Capture-avoiding, by recursion on N.  Types carry no term variables, so every type
  annotation (the A of λx:A, each rep of Θ, B₀, @B[A]) is untouched.  By the Barendregt
  convention the bound variables — the y of λy, the X of ΛX and each reveal variable of Θ —
  are kept distinct from the free variables of V.

  x[x:=V]               = V
  y[x:=V]               = y                             (y ≠ x)
  k[x:=V]               = k
  (M₁ ⊕ M₂)[x:=V]       = M₁[x:=V] ⊕ M₂[x:=V]
  (L · M)[x:=V]         = L[x:=V] · M[x:=V]
  (λx:A. N)[x:=V]       = λx:A. N                       (bound x shadows the substituted x)
  (λy:A. N)[x:=V]       = λy:A. N[x:=V]                 (y ≠ x)
  (Λ X. N)[x:=V]        = Λ X. N[x:=V]
  (L @B[A])[x:=V]       = L[x:=V] @B[A]
  (M ⟪ Θ , B₀ ⟫)[x:=V]  = M ⟪ Θ , B₀ ⟫                  -- a boundary blocks term vars

  The last clause is not an approximation: (env) types the body with an EMPTY term context, so
  a well-typed boundary body is term-closed and there is nothing to substitute.

# Reduction rules

  V, W range over values; TyWrap's wrapped term is ΛY.V with V a value, and Wrap's is a λ.

  (δ)       n₁ ⊕ n₂                       -→ n                if n = n₁ ⟦⊕⟧ n₂
  (Beta)    (λx:A. N) · W                 -→ N[x:=W]
  (TyBeta)  (ΛX. V) @B[A]                 -→ V ⟪ ↑X:=A , B ⟫
  (TyWrap)  ((ΛY.V) ⟪ Θ , ∀Y.B₀ ⟫) @B[A]  -→ V ⟪ ↑Y:=A , Θ , B₀ ⟫
  (Wrap)    ((λx:B₁[γΘ]. N) ⟪ Θ , B₁→B₂ ⟫) · W
                                          -→ N[x := W ⟪ Θᵈ , B₁ ⟫] ⟪ Θ , B₂ ⟫
  (ξ)       R[M]                          -→ R[M′]            if M -→ M′
  (Cancel)  (V ⟪ ↓X:=A , B₀ ⟫) ⟪ ↑X:=A′ , B₀′ ⟫  -→ V         if A = A′    [OPTIONAL]
  (Drop)    V ⟪ ↑X:=A , Θ , B₀ ⟫          -→ V ⟪ Θ , B₀ ⟫     if X ∉ B₀, X ∉ V,
                                                              X ∉ the reps of Θ  [OPTIONAL]
  (Drop∅)   V ⟪ ∅ , B₀ ⟫                  -→ V                             [OPTIONAL]

## TyBeta — a boundary is BORN

  The ∀-body B of the eliminated type is recorded as the boundary type; the type argument A
  becomes the representation of the reveal.  Internal face = B[γ] = B (the reveal variable
  passes through), external face = B[ρ] = B[X:=A] — which is exactly (tapp)'s result type.
  This is the ONLY rule that creates a boundary out of nothing.

## TyWrap — a boundary meets a type application (R1)

  The DIRECT-COMBINE form (Decision 2 as revised, notes/DECISIONS.md).  The elimination
  CONSUMES the Λ: the Λ-binder Y and the reveal variable are the SAME slot, so the wrapped
  value's body V needs no relocation at all, and the type argument A is RECORDED as Y's
  representation, read in the EXTERIOR.  The redex's own annotation B is forced: (env) gives
  it as the ∀-body of the external face.  Faces: internal B₀[γ], and external
  B₀[ρ] = B[Y:=A] — the redex's type.

  Never pushing A inward is precisely what makes this rule sound where the old TyWrapCncl was
  not: A may name a variable the interior blocks (Example 8), and here it never has to be read
  there.

  Partial, by design: the wrapped value must be a Λ.  A WRAPPER-bodied wrapper at a ∀ face is
  a Merge redex (Decision 3), not a TyWrap redex — after merging, canonical forms give the
  single boundary a Λ body.  This is the price of the tighter contractum, and it buys the
  no-term-shift principle: no rule performs a type shift on a TERM (a shift forgets which
  type variables a term is not allowed to mention).

  De Bruijn remark.  The interior grows by one abstract variable, so the CONCEAL reps — which
  live over the whole interior — shift by one (`shiftReps`); reveal reps are exterior and are
  untouched.  Those are TYPES; the term is untouched.  In named notation nothing moves.

## Wrap — a boundary meets an application (R2)

  Symmetric to TyWrap: the elimination CONSUMES the λ and β-substitutes in one step.  The
  argument lives in the EXTERIOR, so it is first moved inside through the DUAL boundary Θᵈ;
  N[x := …] is TERM-variable substitution only, so, as in TyWrap, no term is type-shifted.
  The λ's annotation is forced by (env) to be the internal face B₁[γΘ].  Partial in the same
  way: a WRAPPER-bodied wrapper at a ⇒ face waits for Merge (Decision 3).

  Θᵈ is the DUAL boundary: it is read from the interior's point of view, so every arrow flips.

     each  ↑X:=A  of Θ  becomes  ↓X:=A  of Θᵈ      (X was interior to Θ, so it is exterior to
                                                    Θᵈ; A was exterior to Θ, i.e. interior to
                                                    Θᵈ — exactly a conceal rep's home)
     each  ↓Y:=A  of Θ  becomes  ↑Y:=A  of Θᵈ      (Y's slot is rebuilt as a fresh interior
                                                    variable of Θᵈ; A was interior to Θ, i.e.
                                                    exterior to Θᵈ — a reveal rep's home)

  A variable that Θ drops but does not conceal is blocked; it becomes a reveal of Θᵈ with an
  arbitrary rep (ℕ).  That is sound because (env)'s scope premise forbids B₁ from naming it —
  so Wrap's preservation must go through the scope-restricted congruence (`subst-cong-sc`),
  not a pointwise identity of the two faces.

  Wrap is exact over exteriors built only from abstract variables, which is everything
  reachable from a closed program; over a hand-written exterior containing revealed variables
  the dual may not exist (`no-dual-Γ₃`).

  De Bruijn remark.  The boundary frame of Θᵈ is Θ's frame with the reveal block and the
  dropped block interchanged, so B₁ is renamed by that block swap (`swapᵇ`).  Named notation
  hides this: B₁ is the same type, read on the other side.  The substitution N[x := …] is
  `_[_]ᵐ`, which is the identity on wrappers (a boundary body is term-closed), so the
  argument's own boundaries are never descended into.

## ξ — congruences

  Call-by-value, left to right; also under a Λ and under a boundary.  The last two are not
  bookkeeping: `ΛX.N` is a value only when N is, and `M ⟪ Θ , B₀ ⟫` only when M is, so both
  bodies must be reduced in place.  In the Agda these are five constructors ξ-·-l, ξ-·-r,
  ξ-·[], ξ-Λ, ξ-⟪⟫; ξ-⟪⟫ recurses at the INTERIOR context, which is why preservation and
  progress are generalised over Γ rather than fixed at ∅.

## Cancel / Drop — optional, NOT in the Agda

  None of these is needed for progress; they are space optimisations that collapse the towers
  of boundaries the examples below accumulate.  (Merge, Decision 3, is a different matter: it
  IS needed, because TyWrap and Wrap consume the Λ / λ they eliminate and so do not fire on a
  wrapper-bodied wrapper.)

  Cancel is sound ONLY when the conceal's rep equals the enclosing reveal's rep.  Nothing in
  (env) enforces that (see the `bad` term in Metatheory §Progress), so Cancel must carry the
  side condition explicitly.  Drop∅ is type-preserving but unreachable — no rule mints an
  empty boundary.

## Old per-variable design — superseded; see Example 8

  Kept because notes/old/Scratch7-9.agda and the historical Example 8 below refer to it.  Runtime
  terms were `M ↑[X:=A]@B` and `M ↓[X:=A]@B`, one wrapper per variable, with (reveal) and
  (conceal) as separate typing rules.

  (δ)           n₁ ⊕ n₂               -→ n           if n = n₁ ⟦⊕⟧ n₂
  (Beta)        (λx:A. N) · V         -→ N[x:=V]
  (TyBeta)      (Λ X. V) @B[A]        -→ V ↑[X:=A]@B
  (WrapReveal)  F ↑[X:=A]@(B₁→B₂) · W -→ (F · W↓[X:=A]@B₁) ↑[X:=A]@B₂
  (WrapConceal) F ↓[X:=A]@(B₁→B₂) · W -→ (F · W↑[X:=A]@B₁) ↓[X:=A]@B₂
  (TyWrapRevl)  F ↑[X:=A]@∀Y.B [C]    -→ F [C] ↑[X:=A]@B
  (TyWrapCncl)  F ↓[X:=A]@∀Y.B [C]    -→ F [C[X:=A]] ↓[X:=A]@B         ← UNSOUND (Example 8)
  (Cancel)      V ↓[X:=A]@B ↑[X:=A]@B -→ V
  (Drop)        V ↓[Y:=B]@C ↑[X:=A]@D -→ V ↓[Y:=B]@C  if X ≠ Y and X ∉ V↓[Y:=B]
  (RevealCnst)  k ↑[X:=A]@B           -→ k
  (ξ)           R[M]                  -→ R[M′]      if M -→ M′

  How the new rules replace the old ones:

     TyWrap        replaces  TyWrapRevl + TyWrapCncl   (one rule; the type argument is never
                                                        pushed inward, which is the fix)
     Wrap          replaces  WrapReveal + WrapConceal  (one rule; Θᵈ flips both directions)
     TyBeta, Beta  unchanged in spirit; TyBeta now mints a one-entry boundary
     RevealCnst    gone — a wrapped constant is simply a value
     Commute       never existed and is not needed: reveals and conceals now live on ONE
                   boundary, so there is no reveal-over-conceal shape to commute
     Cancel, Drop  survive only as optional tidying rules (above)

# Examples

Traces are in named notation with the new rules; each line is annotated with the rule that
fires (ξ steps that merely locate the redex are left implicit).  Steps marked [opt] use the
optional Cancel/Drop rules; without them the trace stops at a value that is a tower of
boundaries around the answer.  Steps marked [D3] use Merge, which is settled but not yet a
rule (Decision 3): since TyWrap and Wrap consume the Λ / λ they eliminate, a WRAPPER-bodied
wrapper at an elimination is a Merge redex.  The merged boundary is written Θ₁ ⊕ Θ₂ — its
entry-level definition is Decision 3's (notes/MergeProbe.agda), not fixed here.

## Example 1

  (Λ Y. λy:Y. (ΛX.λx:X.y) [Y] ) [ℕ] · 7 · 3                                      : ℕ
  → TyBeta      ((λy:Y. (ΛX.λx:X.y) [Y]) ⟪ ↑Y:=ℕ , Y→Y→Y ⟫) · 7 · 3
  → Wrap        (((ΛX. λx:X. 7⟪↓Y:=ℕ,Y⟫) [Y]) ⟪ ↑Y:=ℕ , Y→Y ⟫) · 3
  → TyBeta      (((λx:X. 7⟪↓Y:=ℕ,Y⟫) ⟪ ↑X:=Y , X→Y ⟫) ⟪ ↑Y:=ℕ , Y→Y ⟫) · 3
  → Merge [D3]  ((λx:X. 7⟪↓Y:=ℕ,Y⟫) ⟪ (↑X:=Y) ⊕ (↑Y:=ℕ) , X→Y ⟫) · 3
  → Wrap        (7⟪↓Y:=ℕ,Y⟫) ⟪ (↑X:=Y) ⊕ (↑Y:=ℕ) , Y ⟫                  -- a VALUE
  → [opt]       7

  The head of the fourth line is a wrapper wrapped in a wrapper: Wrap consumes the λ, and
  there is no λ until the two boundaries merge.  The λ's body does not use x, so the Wrap step
  discards the dual-wrapped 3 outright.

  The inner boundary ⟪↑X:=Y , X→Y⟫ sits over the outer one's interior (which contains Y), and
  its external face X→Y[ρ] = Y→Y is exactly the outer boundary's internal type.

## Example 2

  (ΛX. λf:X→X. λy:X. f·y) [ℕ] · (λn:ℕ.n+1) · 7                                   : ℕ
  → TyBeta      ((λf:X→X. λy:X. f·y) ⟪ ↑X:=ℕ , (X→X)→(X→X) ⟫) · (λn:ℕ.n+1) · 7
  → Wrap        ((λy:X. (λn:ℕ.n+1)⟪↓X:=ℕ,X→X⟫ · y) ⟪ ↑X:=ℕ , X→X ⟫) · 7
  → Wrap        ((λn:ℕ.n+1)⟪↓X:=ℕ,X→X⟫ · (7⟪↓X:=ℕ,X⟫)) ⟪ ↑X:=ℕ , X ⟫  -- sealed fn in head pos
  → Wrap        ((((7⟪↓X:=ℕ,X⟫) ⟪ ↑X:=ℕ , X ⟫)+1) ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫
  → Cancel[opt] ((7+1) ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫
  → δ           (8 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫
  → Cancel[opt] 8

  Note how Wrap on a conceal-only boundary reproduces the old WrapConceal: the dual of ↓X:=ℕ
  is ↑X:=ℕ, so the argument is revealed on its way in.

## Example 3   (type application to wrapped polymorphic values)

  (ΛX. λf:(∀Z.Z→Z). f [X]) [𝔹] · ((ΛY. ΛZ. λz:Z. z) [ℕ])                         : 𝔹→𝔹
  → TyBeta      ((λf:(∀Z.Z→Z). f [X]) ⟪ ↑X:=𝔹 , (∀Z.Z→Z)→(X→X) ⟫) · ((ΛY.ΛZ.λz:Z.z) [ℕ])
  → TyBeta      (…) · ((ΛZ.λz:Z.z) ⟪ ↑Y:=ℕ , ∀Z.Z→Z ⟫)                   -- call it W
  → Wrap        ((W ⟪ ↓X:=𝔹 , ∀Z.Z→Z ⟫) [X]) ⟪ ↑X:=𝔹 , X→X ⟫
  → Merge [D3]  ((ΛZ.λz:Z.z) ⟪ (↑Y:=ℕ) ⊕ (↓X:=𝔹) , ∀Z.Z→Z ⟫ [X]) ⟪ ↑X:=𝔹 , X→X ⟫
  → TyWrap      ((λz:Z₁.z) ⟪ ↑Z₁:=X , (↑Y:=ℕ) ⊕ (↓X:=𝔹) , Z₁→Z₁ ⟫) ⟪ ↑X:=𝔹 , X→X ⟫

  A value: the polymorphic identity behind two boundaries, external type 𝔹→𝔹.  Note that the
  type argument X of TyWrap is recorded as the rep of the reveal Z₁ — the slot the consumed
  ΛZ used to bind, read in the exterior, where X is in scope — and the concealed X is never
  used to instantiate anything.  This is the step where the old design applied TyWrapCncl and
  substituted into the sealed body.  The type application meets a WRAPPER-bodied wrapper, so
  Merge has to fire first; the old float-inside TyWrap fired directly here but left one extra
  boundary per use, and a further TyBeta to run.

## Example 4   (a constant escaping a boundary)

  (ΛX. λx:X. 7) [ℕ] · 5                                                          : ℕ
  → TyBeta      ((λx:X. 7) ⟪ ↑X:=ℕ , X→ℕ ⟫) · 5
  → Wrap        7 ⟪ ↑X:=ℕ , ℕ ⟫                              -- a VALUE (no RevealCnst)
  → Drop [opt]  7

  The λ's body ignores x, so the dual-wrapped 5 is discarded by the Wrap step itself.

## Example 5

  (ΛX. λf:(X→X)→X. f · (λx:X. x)) [ℕ] · (λg:ℕ→ℕ. g · 42)                         : ℕ
  → TyBeta      ((λf. f · (λx:X.x)) ⟪ ↑X:=ℕ , ((X→X)→X)→X ⟫) · (λg:ℕ→ℕ. g·42)
  → Wrap        ((λg:ℕ→ℕ.g·42)⟪↓X:=ℕ,(X→X)→X⟫ · (λx:X.x)) ⟪ ↑X:=ℕ , X ⟫
  → Wrap        ((((λx:X.x)⟪↑X:=ℕ,X→X⟫) · 42) ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫
  → Wrap        (((42⟪↓X:=ℕ,X⟫) ⟪↑X:=ℕ,X⟫) ⟪↓X:=ℕ,X⟫) ⟪↑X:=ℕ,X⟫
  → Cancel[opt] (42 ⟪↓X:=ℕ,X⟫) ⟪↑X:=ℕ,X⟫
  → Cancel[opt] 42

## Example 6   (the trace that killed the conceal-b design)

  (ΛX. λw:ℕ. (ΛY. w) [X→X]) [ℕ] · 5                                              : ℕ
  → TyBeta      ((λw:ℕ. (ΛY. w) [X→X]) ⟪ ↑X:=ℕ , ℕ→ℕ ⟫) · 5
  → Wrap        ((ΛY. 5⟪↓X:=ℕ,ℕ⟫) [X→X]) ⟪ ↑X:=ℕ , ℕ ⟫
  → TyBeta      ((5⟪↓X:=ℕ,ℕ⟫) ⟪ ↑Y:=X→X , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫
  → Drop [opt]  (5⟪↓X:=ℕ,ℕ⟫) ⟪ ↑X:=ℕ , ℕ ⟫
  → Cancel[opt] 5

  At the fourth line the conceal of X sits under the reveal of Y whose rep X→X mentions X.
  Under (env) this is unproblematic: the reveal's rep is read in the EXTERIOR, where X is in
  scope, and the conceal's interior (which blocks Y and X) never has to read it.

## Example 7

  (ΛX. λw:X. (ΛY. λy:X → Y. y · w) [X] · (λz:X.z)) [ℕ] · 5                       : ℕ
  → TyBeta      ((λw:X. (ΛY. λy:X→Y. y·w) [X] · (λz:X.z)) ⟪ ↑X:=ℕ , X→X ⟫) · 5
  → Wrap        ((ΛY. λy:X→Y. y·(5⟪↓X:=ℕ,X⟫)) [X] · (λz:X.z)) ⟪ ↑X:=ℕ , X ⟫
  → TyBeta      (((λy:X→Y. y·5⟪…⟫) ⟪ ↑Y:=X , (X→Y)→Y ⟫) · (λz:X.z)) ⟪ ↑X:=ℕ , X ⟫
  → Wrap        ((((λz:X.z)⟪↓Y:=X,X→Y⟫) · (5⟪↓X:=ℕ,X⟫)) ⟪ ↑Y:=X , Y ⟫) ⟪ ↑X:=ℕ , X ⟫
  → Wrap        ((((5⟪↓X:=ℕ,X⟫) ⟪↑Y:=X , X⟫) ⟪↓Y:=X , Y⟫) ⟪↑Y:=X,Y⟫) ⟪↑X:=ℕ,X⟫
  → Drop [opt]  (((5⟪↓X:=ℕ,X⟫) ⟪↓Y:=X , Y⟫) ⟪↑Y:=X,Y⟫) ⟪↑X:=ℕ,X⟫
  → Cancel[opt] (5⟪↓X:=ℕ,X⟫) ⟪↑X:=ℕ,X⟫
  → Cancel[opt] 5

## Example 8   (the OLD design's preservation counterexample — now well typed)

  This is the program of the historical failure below.  Every term is typed, at ∀Y.Y→Y, in
  notes/Example8Trace.agda; the labels T0…T5, T4′ are that file's (a historical record of the
  two candidate TyWrap forms, so it still carries the float-inside T4 and T5).  With the rules
  as they now stand the trace goes T0 → T1 → T3 → T4′ and stops: T2 and T4/T5 do not occur.

  T0  (ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]) [ℕ] · (ΛZ. λz:Z. z)                       : ∀Y.Y→Y
  → TyBeta
  T1  ((λf:(∀Z.Z→Z). ΛY. f [Y]) ⟪ ↑X:=ℕ , (∀Z.Z→Z)→(∀Y.Y→Y) ⟫) · (ΛZ. λz:Z. z)
  → Wrap        (the λ is consumed; T2, the float-form's intermediate, is skipped)
  T3  (ΛY. ((ΛZ.λz:Z.z) ⟪ ↓X:=ℕ , ∀Z.Z→Z ⟫) [Y]) ⟪ ↑X:=ℕ , ∀Y.Y→Y ⟫
  → TyWrap      (the ΛZ is consumed; T4's floated application and T5 are skipped)
  T4′ (ΛY. ((λz:Z.z) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→Z ⟫)) ⟪ ↑X:=ℕ , ∀Y.Y→Y ⟫            -- a VALUE

  Why the old failure does not recur.  At T3 the redex is a value concealed on X, type-applied
  to the Λ-bound Y — and Y is SHALLOWER than X, hence blocked in the boundary's interior (in
  the exterior Γ = Y , X:=ℕ the interior of ↓X:=ℕ is Γ↓X = ∅).  The old TyWrapCncl pushed the
  type argument INTO the sealed body, producing `(ΛZ.λz.z) [Y]` at a context without Y:
  untypable.  TyWrap instead RECORDS Y as the representation of the reveal Z — the slot the
  consumed ΛZ used to bind, read in the exterior Γ, where Y is perfectly in scope.  The
  boundary of T4′ is ↑Z:=Y , ↓X:=ℕ with interior Z (Y still blocked) and B₀ = Z→Z, which names
  no blocked variable; both faces compute to Y→Y externally and Z→Z internally.

  The trace is two steps shorter than the float-inside form's and ends in a SINGLE boundary
  where that form ended in the nested T5.  What is given up is totality: the T3 redex fires
  only because the wrapped value is syntactically a Λ.  Example 3 shows the other case, where
  it is a wrapper and Merge must fire first.

## Example 8, historical   (why the OLD per-variable design was discarded)

  A closed, well-typed program that reduced to an ILL-TYPED term under the old rules.  The key
  ingredient is `λf. ΛY. f [Y]`: the polymorphic argument f is applied to a type variable Y
  introduced AFTER f is bound.  (Machine-checked in de Bruijn form as notes/old/Scratch8.agda.)

  (ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]) [ℕ] · (ΛZ. λz:Z. z)              : ∀Y. Y→Y
  → TyBeta      (λf:(∀Z.Z→Z). ΛY. f [Y]) ↑[X:=ℕ] · (ΛZ. λz:Z. z)
  → WrapReveal  ((λf. ΛY. f [Y]) · (ΛZ. λz:Z. z)↓[X:=ℕ]) ↑[X:=ℕ]
  → Beta        (ΛY. (ΛZ. λz:Z. z)↓[X:=ℕ] [Y]) ↑[X:=ℕ]
  → TyWrapCncl  (ΛY. ((ΛZ. λz:Z. z) [Y]) ↓[X:=ℕ]) ↑[X:=ℕ]              ← ILL-TYPED

  Every line down to the redex is well-typed; the redex (ΛY. (ΛZ.λz.z)↓[X:=ℕ] [Y]) ↑[X:=ℕ]
  has type ∀Y.Y→Y.  The last term does NOT: its conceal is ((ΛZ.λz.z) [Y]) ↓[X:=ℕ]@(Y→Y) at
  context X:=ℕ, Y, and the old (conceal) rule typed the body in the PREFIX (X:=ℕ, Y)↓X = ∅ —
  Y is shallower than X, so it is dropped from X's existential scope.  But the body mentions
  Y, so (tapp) demanded ∅ ⊢ Y, which fails.

  What went wrong.  TyWrapCncl pushed the type argument into the sealed body:
  F [C[X:=A]] = (ΛZ.λz.z) [ Y[X:=ℕ] ] = (ΛZ.λz.z) [Y], and Y[X:=ℕ] = Y is still shallower than
  X.  So the invariant "a conceal body mentions only X-and-deeper variables" was BROKEN by
  TyWrapCncl.  The fix is structural, not a side condition: put reveals and conceals on ONE
  boundary, so a conceal's interior can still see the reveals, and never transport a type
  argument inward — record it as a reveal rep instead.  That is TyWrap.

# Metatheory  (proof sketches)

Runtime contexts.
  The frames R enter Λ bodies and boundary interiors but never a λ-body, so no term binder is
  descended into.  Every context that arises therefore has only type-variable entries:
  Γ ::= ∅ | Γ, X | Γ, X:=A  (term variables occur only when checking source terms, or
  transiently under a λ when inverting (lam)).  Progress and preservation are stated at such
  runtime contexts, with an EMPTY term context.

The interior at work.
  Only two operations touch the interior: TyWrap grows it by one fresh abstract variable — the
  slot the consumed Λ used to bind — so conceal reps, which live over the whole interior,
  shift, while reveal reps do not; and moving a wrapper under a Λ grows the EXTERIOR by one
  (so conceal indices shift; in named notation, nothing).  Everything else leaves Γ⇈Θ alone;
  in particular (env)'s premises mention only Θ and B₀, so ξ-⟪⟫ carries them across unchanged.
  Note that no rule shifts a TERM: TyWrap's contractum is the Λ-body exactly as it stood, and
  Wrap's is a term-variable substitution.  Only TYPES (the conceal reps) move.

Supporting lemmas.
  (L1) Term substitution.  If Γ, x:A, Θ ⊢ N : B and Γ ⊢ V : A (V a value), then
       Γ, Θ ⊢ N[x:=V] : B.  The boundary case is the identity: a boundary body is typed with
       an empty term context, so x ∉ M.  The Λ case needs type-variable renaming (below) at
       the weakening ρ = suc.  Beta uses Θ = ∅.
  (L2) Type-variable renaming.  If Γ ⊢ M : A and ρ : Γ → Γ′ preserves lookup AND IS MONOTONE,
       then Γ′ ⊢ ρM : ρA.  Monotonicity is not a convenience: the interior of a boundary is
       determined by the ORDER of the indices (a single restriction at the deepest conceal),
       so a renaming that permuted indices could shrink a conceal's interior and strand a
       variable.  In the Agda (`⊢renameᵀ`) the boundary case renames the conceal indices and
       B₀ by ρ (lifted past the reveal variables) and the body and the conceal reps by the
       INDUCED interior renaming; the concealed case of the commutation between renaming and
       the internal face needs ρ injective, which monotonicity supplies, and the shape of the
       renamed interior needs ρ to send the deepest conceal to the deepest.
  (L3) Commutation.  For X≠Z, Z∉A:  C[Z:=B][X:=A] = C[X:=A][Z:=B[X:=A]].  (Type level.)
  (L-sc) Scope-restricted congruence.  Two substitutions that agree on the ACCESSIBLE slots
       act the same on a B₀ that is well-scoped (Θ;Γ ⊢ᵒᵏ B₀).  This is what makes the blocked
       slots harmless: the faces need only agree where B₀ can look.
  (L-wf) Typing ⇒ well-formedness ⇒ scope.  A derivable Γ ⊢ M : A has Γ ⊢ A, and a
       well-formed type over the boundary frame is well-scoped — this is how the (env) premise
       Θ;Γ ⊢ᵒᵏ B₀ is discharged in the cases where no reduction rule supplies it.

  Inversion of (env): from Γ ⊢ M ⟪ Θ , B₀ ⟫ : C we get Γ ∣ (Γ⇈Θ) ⊢ Θ, Θ;Γ ⊢ᵒᵏ B₀,
  Γ⇈Θ ⊢ M : B₀[γΘ], and C = B₀[ρΘ].

## Preservation

Γ ⊢ M : A  (Γ runtime)  and  M -→ M′   ⟹   Γ ⊢ M′ : A.

Proved in the Agda (BPreservation.agda) for every rule: Beta, TyBeta, TyWrap, Wrap and the
five ξ congruences.

  Beta.       (L1).  Substitution is the identity on boundaries (their bodies are term-closed),
              and the Λ case of the substitution lemma is (L2) at ρ = suc, whose monotonicity
              premise is immediate.  This is the only case where a term variable appears.
  TyBeta.     Inversion of (tapp) and (tlam): Γ, X ⊢ V : B and Γ ⊢ A, result B[X:=A].  The
              new boundary is ↑X:=A: (bwf-↑) from Γ ⊢ A; the interior is Γ,X, where V is
              already typed; the internal face of B is B itself (a reveal variable passes
              through γ) and the external face is B[X:=A] — the two face equations.  The scope
              premise Θ;Γ ⊢ᵒᵏ B is not supplied by the rule and is discharged by (L-wf) from
              the typing of V.  This is the case that makes preservation need the wf/scope
              bridge at all.
  TyWrap.     Inversion of (tapp) and (env): the wrapper's external face is ∀-shaped, so
              B₀ = ∀Y.B₀′ and the redex's annotation B is FORCED to be the ∀-body of the
              external face.  Inverting (tlam) on the (env) body premise — whose type is the
              internal face ∀Y.(B₀′[γΘ]) — gives the Λ-body typed at Γ⇈Θ, Y with the internal
              face of B₀′.  That is ALREADY the contractum's interior and interior face, so
              the body is transported by two equations and nothing renames it.  Four face
              laws do the work, all machine-checked: (i) the internal face of the SHIFTED
              boundary equals the extension of the old internal face — AT EVERY SLOT, blocked
              ones included, so the rule needs no scope side condition; (ii) the external face
              of the shifted boundary is the old external face's ∀-body instantiated at A,
              i.e. exactly the redex's type; (iii) boundary well-formedness survives the shift
              (reveal reps are exterior and untouched, conceal reps are weakened by one);
              (iv) the scope stack of the shifted boundary is the old one with one accessible
              slot pushed, so the new Scoped obligation IS the sc-all inversion of the redex's.
  Wrap.       Inversion of (app) and (env): B₀ = B₁→B₂, the argument W has the external face
              B₁[ρΘ], and inverting (lam) on the body premise — whose type is the internal
              face B₁[γΘ] → B₂[γΘ] — forces the λ's annotation to B₁[γΘ] and gives its body
              at the term context x:B₁[γΘ].  The dual boundary Θᵈ has the wrapper's interior
              as its exterior and (over an all-abstract exterior) the original Γ as its
              interior, so W ⟪ Θᵈ , B₁ ⟫ types at the interior with internal face B₁[γΘ] —
              exactly the annotation.  The two faces of B₁ under Θᵈ are the two faces under Θ
              with the sides exchanged, EXCEPT at blocked slots, where the dummy rep makes
              them differ; (L-sc) with the scope premise on B₁ makes that difference
              irrelevant.  Then (L1) at that argument, and (env) at B₂.
  ξ.          One induction hypothesis under the corresponding typing rule.  Two change
              context: under Λ the IH is at Γ,X (the term context stays empty), and under a
              boundary the IH is at the INTERIOR Γ⇈Θ — a different context, which is why the
              statement must be generalised over Γ.  The (env) premises mention only Θ and B₀
              and are carried across intact.
  Cancel/Drop.  Not in the Agda.  Drop∅ is immediate (both faces of an empty boundary are B₀);
              Cancel needs the two reps to agree, and is unsound otherwise (next section).

## Progress

Γ ⊢ M : A  (Γ runtime, empty term context)   ⟹   M is a value  or  M -→ M′.

  Canonical forms.  A value of type ℕ is a numeral or a wrapper; of type A→B a λ or a wrapper;
  of type ∀X.C a Λ or a wrapper; of a VARIABLE type it must be a wrapper whose B₀ is a
  variable (no constant, λ or Λ has a variable type).  So at an elimination position the first
  analysis is the shape of B₀, not of the value:

     B₀ = ∀Y.B₀′        ⟹  TyWrap fires, IF the wrapped value is a Λ
     B₀ = B₁→B₂         ⟹  Wrap fires,   IF the wrapped value is a λ
     B₀ = a reveal variable  ⟹  see the obstruction below
     B₀ = a kept/concealed variable  is impossible at an elimination: the external face would
                                     then be a variable, and no elimination types a variable.

  In the first two cases the wrapped value's own type is the internal face of B₀, which is
  ∀- resp. ⇒-shaped, so it is the matching binder or a WRAPPER; the wrapper subcase is a Merge
  redex (Decision 3), which is why the two rules being partial costs no progress once Merge
  lands.  In the Agda those two subcases are the module parameters NestedTApp / NestedApp of
  strong.ProgressDef, alongside the two reveal-variable ones.

  Cases on M: constants and λ are values; a variable is impossible (empty term context); an
  application or type application reduces a non-value part by ξ, and with both parts values
  steps by Beta / TyBeta (unwrapped head) or Wrap / TyWrap / Merge (wrapped head); Λ N and
  M ⟪ Θ , B₀ ⟫ reduce their body by ξ, and are values once the body is.

  THE OPEN OBSTRUCTION — rep inconsistency (notes/BoundaryRules.md §4).  (env) records one B₀
  per wrapper and derives both faces, but it cannot relate a conceal ↓X:=A to the rep of the
  REVEAL that binds X — that reveal lives on an ENCLOSING wrapper, so no local premise could
  see it.  Hence the closed, well-typed value

     bad  =  (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=(∀Z.Z→Z) , X ⟫        :  ∀Z.Z→Z

  whose entire content is the numeral 7.  The outer boundary reveals X with rep ∀Z.Z→Z, so its
  external face is ∀Z.Z→Z; the inner boundary conceals that same X with the INCONSISTENT rep
  ℕ, so its internal face is ℕ and 7 type-checks.  Now bad @(Z→Z)[ℕ] : ℕ→ℕ is well typed, is
  not a Λ, and its B₀ is a variable — so TyWrap does not apply (and neither did the old
  float-inside form);
  Cancel would produce 7 : ∀Z.Z→Z, which is false; and no merge rule can help, since the
  composite of the two boundaries would have to have two coinciding faces that must be ℕ and
  ∀Z.Z→Z.  So progress is NOT provable from (env) alone.  bad is unreachable (Wrap's conceals
  come from the dual, which copies the reveal's own rep), leaving three routes:

    1. state progress for a reachable class — a companion predicate "every conceal matches its
       enclosing reveal", which is against the standing grounded-invariants design law;
    2. ground the invariant in the relation: let a reveal put a REVEALED entry X:=A (not an
       abstract X) into the interior, and let (bwf-↓) demand Γ ∋ Y:=A.  This kills bad and
       legitimises the dual's conceals.  Wrinkle: a reveal rep is read in the exterior and may
       name a blocked variable, in which case the entry can only be abstract — and the
       pathology returns exactly there;
    3. accept it and prove progress only for the image of a source program.

  The Agda keeps this as a labelled hole in Progress.agda.

# Correspondence with the Agda   (SystemF/agda/strong/)

  Jeremy's rule: the Agda constructor names follow the names in these notes.

  notes                      Agda                                       file
  -------------------------  -----------------------------------------  --------------
  M ⟪ Θ , B₀ ⟫               _⟪_,_⟫                                     Boundary.agda
  ↑X:=A                      rvl A                                      Boundary.agda
  ↓Y:=A                      cnc Y A                                    Boundary.agda
  Θ                          BCtx = List BEntry                         Boundary.agda
  Γ ⇈ Θ  (interior)          intOf Δ Θ = prepAbst (revs Θ) (dropN (cmax Θ) Δ)
  Γ ↓ X  (prefix)            _↓_                                        Context.agda
  B₀[γΘ] (internal face)     substᵗ (γᵇ Θ) B₀                           Boundary.agda
  B₀[ρΘ] (external face)     substᵗ (ρᵇ Θ) B₀                           Boundary.agda
  Θ;Γ ⊢ᵒᵏ B₀ (scoped)        Scoped (baseS Θ Δ) B₀                      Boundary.agda
  Γ ∣ Ψ ⊢ Θ                  _∣_⊢ᵇ_  (bwf[], bwf↑, bwf↓)                Boundary.agda
  (env)                      env                                        Boundary.agda
  L @B[A]                    L ·[ B , A ]        (⊢·[])                 Boundary.agda
  Beta                       Beta                                        BReduction.agda
  TyBeta                     TyBeta                                        BReduction.agda
  TyWrap                     TyWrap   (R1)                             BReduction.agda
  Wrap                       Wrap     (R2)                             BReduction.agda
  Merge                      — not yet a rule; the four open progress  ProgressDef.agda
                               cases are its module parameters
  ξ                          ξ-·-l, ξ-·-r, ξ-·[], ξ-Λ, ξ-⟪⟫            BReduction.agda
  Cancel / Drop              — not in the Agda (optional; see above)
  Θᵈ (dual)                  dualᵇ Θ / swapᵇ Θ                          notes/BoundaryRulesProbe
  L2 (monotone renaming)     ⊢renameᵀ (premise `Mono ρ`)                BReduction.agda
  L-sc                       subst-cong-sc                              Boundary.agda
  L-wf                       ⊢ty-wf, wf→Scoped, scB-bridge              ScopeBridge.agda
  L1                         ⊢substᵀᵐ, ⊢[]ᵐ, preserve-Beta               TermSubst.agda
  Example 8 trace (T0…T5)    notes/Example8Trace.agda
  old design (historical)    Terms/Typing/Reduction, notes/old/Scratch7-9.agda

  Named vs de Bruijn.  The Agda differences that named notation hides:

  * conceal indices are WHOLE-Γ de Bruijn indices (not progressive), which is what makes
    renaming through a boundary uniform;
  * conceal reps live over the WHOLE interior and are NOT shifted past the reveal variables —
    so a conceal rep may mention a reveal variable — but they DO shift when the interior grows
    (TyWrap's `shiftReps`) or when the wrapper moves under a Λ (`⇑ᵀ`);
  * reveal reps are exterior and never shift with the interior;
  * B₀ lives over the boundary frame (reveal variables ++ Γ), so it renames by a lift past the
    reveal block, and Θᵈ permutes that frame by a block swap (`swapᵇ`);
  * the Agda's `Term` has no arithmetic `_⊕_` and no boolean constants, so it has no (δ) and
    no (arith)/(cnst-b) — the type 𝔹 exists but no term inhabits it.  The (δ)/(arith)/(cnst-b)
    lines above are part of the informal language only.

# Why the earlier conceal-b design failed  (kept as a cautionary record)

  An earlier (conceal) — call it conceal-b — typed the body without X by *deleting* the
  binding rather than blocking it:

     (conceal-b) Γ₁, Γ₂ ⊢ M : B[X:=A]     X ∉ Γ₂
                 -------------------------------
                 Γ₁, X:=A, Γ₂ ⊢ M↓[X:=A]@B : B

  Example 6 breaks it.  The reduction is (in the old per-variable notation):

     (ΛX. λw:ℕ. (ΛY. w) [X→X]) [ℕ] · 5
     → TyBeta      (λw:ℕ. (ΛY. w) [X→X]) ↑[X:=ℕ] · 5
     → WrapReveal  ((λw:ℕ. (ΛY. w) [X→X]) · 5↓[X:=ℕ]) ↑[X:=ℕ]
     → Beta        ((ΛY. 5↓[X:=ℕ]) [X→X]) ↑[X:=ℕ]
     → TyBeta      (5↓[X:=ℕ] ↑[Y:=X→X]) ↑[X:=ℕ]        ← ill-typed under conceal-b

  At the last line the seal 5↓[X:=ℕ] sits at context X:=ℕ, Y:=(X→X).  conceal-b must type
  its body by deleting X, at Γ₁,Γ₂ = ∅, {Y:=(X→X)} — but that context is ill-formed: Y's
  representation X→X now dangles.  Equivalently the side condition X ∉ Γ₂ fails, since
  X ∈ (Y:=(X→X)).  So conceal-b rejects this term even though it runs fine.

  The failure was traced to TyBeta: revealing Y:=(X→X) injects X into the seal's Γ₂, and the
  supposed lemma "revealing a variable preserves typing" is false under conceal-b.

  Under the combined boundary the question does not arise at all: a reveal's representation is
  read in the EXTERIOR, so it never has to be well-formed in an interior that blocks X (see
  the new Example 6).

# De Bruijn formalization and the tightened conceal marker  (what we learned)

  NOTE: this section records an INTERMEDIATE design of the OLD per-variable calculus — a
  non-counting conceal marker whose lookup was tightened to n < X.  It was superseded first by
  the prefix approach (no marker; the conceal body typed in Γ↓X) and then, after Example 8,
  by the combined boundary of this document.  It is kept because the reasoning that led to the
  tightening is what justifies the single restriction at the deepest conceal in Γ⇈Θ.

  We mechanized the old calculus in Agda under SystemF/agda/strong/ using de Bruijn indices:
  Types / TypeSubst, Context, Weakening, Terms, Typing, Reduction, Examples.  Two design
  points sharpened along the way.

## Representation well-formedness at a conceal

  The old (conceal) rule typed its body at Γ↓X against B[X:=A], so to prove
  regularity/preservation we needed the representation A — recovered by the lookup Γ ∋ X:=A —
  to be well-formed in the current context.  Lookup alone did NOT guarantee this originally: a
  marker ↓Y could sit between a use and a revealed variable whose representation mentions a
  *concealed* variable (the "dangerous shape": Y:=(X→X) with X concealed).  We first fixed
  this with an inductive predicate, ConcealCtx Δ X, and proved it implies Δ ⊢ A.

## The insight: a sealed value lives in its existential scope

  We then asked whether a value that uses X can be sealed on a *different* variable Y.  No
  closed program produces it: a sealed value can only depend on type variables revealed BEFORE
  the sealed one.  Equivalently, at a conceal on X the body and annotation mention only X and
  variables deeper than X.

## The tightened marker

  This invariant is captured by ONE change to type-variable lookup: a marker ↓X blocks not
  just X but every variable revealed after X.  With de Bruijn indices (index 0 = most-recently
  revealed), the marker-skip rules become

      skip-cncl : n < X → Δ ∋tv   X       → (cncl n ∷ Δ) ∋tv   X          (was n ≢ X)
      skip-cncl : n < X → Δ ∋ X := A      → (cncl n ∷ Δ) ∋ X := A         (was n ≢ X)

  so a conceal body sees exactly the variables in its existential scope.  Consequences, all
  machine-checked at the time: representation lookup yields a well-formed type directly
  (subsuming ConcealCtx); the "dangerous shape" becomes unstateable; and the Commute redex is
  rejected statically.

  This is the ancestor of the current interior Γ⇈Θ, which drops the whole shallow block at the
  DEEPEST conceal — the same idea, "compiled away": the same variables are in scope, but the
  body is stored over the restricted context so nothing needs blocking, shifting, or
  subtracting at lookup time.  What the old design still got wrong, and the combined boundary
  fixes, is that the shallow block was dropped for the sealed body while a type ARGUMENT could
  still be pushed into it (TyWrapCncl, Example 8).
