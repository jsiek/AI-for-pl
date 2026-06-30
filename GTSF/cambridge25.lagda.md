TODO:
  Clean up definitions of typing and narrowing to conform to result of
    meeting of Thu 25 Jun
  Change ≈ to put same endpoints first and alternative defintion last


Graduality, Parametricity, Interoperability:
Together Again for the First Time
(version 25)

25 June 2026

Jeremy Siek, Indiana University
Peter Thiemann, University of Freiburg
Philip Wadler, Input Output

------------------------------------------------------------------------
New in this version:
cambridge20 casts relate terms, *except* upcasts and downcasts use full imprecision.
cambridge21 has full draft proof, including ν upcast lemma.
cambridge22 based on arbitrary casts (not up or down), plus widening and narrowing
------------------------------------------------------------------------
[Key changes in the syntax]

                      L,M,N      ::=  ... | V α | ...
                      E          ::=  ... | να:=A. E α ⟨ c[α] ⟩ | ...


## Reduction with invariant, variation a: one big-step rule [Obsolete]

    F  ::=  □ | F ⟨ c ⟩

  Replace the rules marked (*) above by the following rules.

  Type application reduction (F / V / α —→ N)

    F / (ΛX.V[X]) / α        —→  F[V[α]]
    F / (V ⟨ να.c[α] ⟩) / α  —→  F[V ⟨ c[α] ⟩]

    F[□ ⟨ c[α] ⟩] / V —→ N
    ------------------------
    F / (V ⟨ ∀X.c[X] ⟩) —→ N

    (□ ⟨ c[α] ⟩) / V / α —→ N
    -------------------------
    E[V α ⟨ c[α] ⟩] —→_∅ E[N]

    -----------------------------------------------
    E[να:=A.L α ⟨ c[α] ⟩] —→_{α:=A} E[L α ⟨ c[α] ⟩]

    L —→_Σ L′
    -------------------------------------
    E[L α ⟨ c[α] ⟩] —→_Σ E[L′ α ⟨ c[α] ⟩]


## Reduction with invariant, variation b: alter the grammar [Obsolete]

Redefine the grammar of term by adding

    L,M,N ::=  ... | να. L α ⟨ c[α] ⟩ | ⌈ P[α] ⌉ 
    P[α]  ::=  L α | P[α] ⟨ c[α] ⟩

and in the definition of term replace L α by P[α].
Write ⌈P⌉ to indicate that a subterm is a P rather than an M.

Replace the rules marked (*) above by the following rules.

Add a type application reduction rule, of type M ——→ M′
    
    F ::= □ | F ⟨ c ⟩

    ⌈ F[(ΛX.V[X]) α] ⌉ ——→ F[V[α]]

    ⌈ F[(V ⟨ να.c[α] ⟩) α] ⌉ ——→ F[V ⟨ c[α] ⟩]

    ⌈ F[(V ⟨ ∀X.c[X] ⟩) α] ⌉ ——→ ⌈ F[V α ⟨ c[α] ⟩] ⌉

    ⌈ P[α] ⌉ ——→ M
    ---------------------
    E[⌈ P[α] ⌉] —→_∅ E[M]

    L —→_Σ L′
    -----------------------------
    E[⌈F[L α]⌉] —→_Σ E[⌈F[L′ α]⌉]

    -------------------------------------
    E[να:=A.F[L α]] —→_{α:=A} E[⌈F[L α]⌉]
------------------------------------------------------------------------
Jeremy and Peter,

Jeremy's counterexample had me stumped for a while. But in fact,
it is illegal by the type rules in cambridge22:

    Γ ⊢ L : ∀X.B[X]
    --------------------
    Γ, α:=A ⊢ L α : B[α]

By these rules, in a type application (L α), the seal α cannot appear
free in L. So we rule out the possibility that subsituting α into L
can lead to a conflict.

In particular, in Jeremy's counterexample, the subterm

  (((λx:★. x) ⟨ νβ. (-seal_α → -tag_β) ⟩) α)

isn't permitted, because α occurs free in L, and that indeed is the
source of the problem.

The rule as written is quite restrictive---no binding form can intercede
between the binding (να. ...) and the application (L α). But that's
adequate for our purposes, since the translation from the surface
language

  L A  ~~>  να:=A. L α ⟨ p̅ ⟩   where  L : ∀X.B[X] and p̅ : B[α] ⊑_{α:=A} B[A]

obeys the restriction.

Note that restricting α to not appear in L only saves our bacon because
of the innovation we introduced yesterday, that id_α doesn't conflict with
any of α!, α?, α♯, α♭, since otherwise a reduction (ΛX.V[X]) α —→ V[α]
could get us into trouble. This latter distinction also shows why it is
crucial to distinguish X's from α's, and permit X in id_X but not in
tags or seals.

Restricting the α:=A binding to the end of the type context is important,
because it guarantees that when we drop the binding there is no later
binding that refers to α and becomes undefined. Further, the restriction
corresponds to our formulation of the term narrowing rules:

    (α⊒α)
      γ ⊢ L ⊒ L′ : ∀X.p[X]
      ---------------------------
      γ, α:=q ⊢ L α ⊒ L′ α : p[α]

    (⊒α)
      γ ⊢ L ⊒ L′ : να.p[α]
      -------------------------
      γ, α:=A ⊢ L ⊒ L′ α : p[α]

The restricted form corresponds neatly to the desired property that if
γ ⊢ M ⊒ M′ : p then γ : Γ ⊒ Γ′, Γ ⊢ M : A, Γ′ ⊢ M′ : A′ and p : A ⊒ A′.

I can't fault Jeremy for not spotting the importance of this formulation of
the rule, because I forgot about it myself! In cambridge23, I rewrote it
to a more familiar form:

    Γ ⊢ L : ∀X.B[X]
    --------------- α ∈ dom(Γ)
    Γ ⊢ L α : B[α]

But that form is problematic.

Whew! Go well, -- P
------------------------------------------------------------------------
False trail:

    Γ,Π ⊢ L : ∀X.B[X]    
    --------------------- α ∉ fv(Π)
    Γ,α:=A,Π ⊢ L α : B[α]

------------------------------------------------------------------------
A simple problematic example:

Jeremy's problematic example

    (ΛX.ΛY.N[X,Y]) A B
  ~>
    νβ:=B. (να:=A. (ΛX.ΛY.N[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) β ⟨ q̅ ⟩

Let's check the typing derivation and reductions.

    X, Y ⊢ V[X,Y] : C[X,Y]
    -------------------------
    X ⊢ ΛY.V[X,Y] : ∀Y.C[X,Y]
    -------------------------------
    ∅ ⊢ ΛX.ΛY.V[X,Y] : ∀X.∀Y.C[X,Y]
    -----------------------------------
    α:=A ⊢ (ΛX.ΛY.V[X,Y]) α : ∀Y.C[α,Y]     ∀Y.p̅[id_Y] : ∀Y.C[α,Y] ⊑_{α:=A} ∀Y.C[A,Y]
    ---------------------------------------------------------------------------------
    α:=A ⊢ (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩ : ∀Y.C[A,Y]
    --------------------------------------------------
    ∅ ⊢ (να:=A. (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) : ∀Y.C[A,Y]
    --------------------------------------------------------
    β:=B ⊢ (να:=A. (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) β : C[A,β]    q̅ : C[A,β] ⊑_{β:=B} C[A,B]
    ----------------------------------------------------------------------------------------
    β:=B ⊢ (να:=A. (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) β ⟨ q̅ ⟩ : C[A,B]
    ----------------------------------------------------------------------
    ∅ ⊢ (νβ:=B. (να:=A. (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) β ⟨ q̅ ⟩) : C[A,B]

  —→_{β:=B}

    X, Y ⊢ V[X,Y] : C[X,Y]
    -------------------------
    X ⊢ ΛY.V[X,Y] : ∀Y.C[X,Y]
    -------------------------------
    ∅ ⊢ ΛX.ΛY.V[X,Y] : ∀X.∀Y.C[X,Y]
    -----------------------------------
    α:=A ⊢ (ΛX.ΛY.V[X,Y]) α : ∀Y.C[α,Y]     ∀Y.p̅[id_Y] : ∀Y.C[α,Y] ⊑_{α:=A} ∀Y.C[A,Y]
    ---------------------------------------------------------------------------------
    α:=A ⊢ (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩ : ∀Y.C[A,Y]
    --------------------------------------------------
    ∅ ⊢ (να:=A. (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) : ∀Y.C[A,Y]
    --------------------------------------------------------
    β:=B ⊢ (να:=A. (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) β : C[A,β]    q̅ : C[A,β] ⊑_{β:=B} C[A,B]
    ----------------------------------------------------------------------------------------
    β:=B ⊢ (να:=A. (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) β ⟨ q̅ ⟩ : C[A,B]

  —→_{α:=A}

    X, Y ⊢ V[X,Y] : C[X,Y]
    -------------------------
    X ⊢ ΛY.V[X,Y] : ∀Y.C[X,Y]
    -------------------------------
    ∅ ⊢ ΛX.ΛY.V[X,Y] : ∀X.∀Y.C[X,Y]
    -----------------------------------
    α:=A ⊢ (ΛX.ΛY.V[X,Y]) α : ∀Y.C[α,Y]     ∀Y.p̅[id_Y] : ∀Y.C[α,Y] ⊑_{α:=A} ∀Y.C[A,Y]
    ---------------------------------------------------------------------------------
    α:=A ⊢ (ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩ : ∀Y.C[A,Y]
    --------------------------------------------------
    α:=A ⊢ ((ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) : ∀Y.C[A,Y]
    ---------------------------------------------------------
    α:=A, β:=B ⊢ ((ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) β : C[A,β]
    ---------------------------------------------------------
    β:=B, α:=A ⊢ ((ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) β : C[A,β]    q̅ : C[A,β] ⊑_{β:=B} C[A,B]
    ----------------------------------------------------------------------------------------
    β:=B, α:=A ⊢ ((ΛX.ΛY.V[X,Y]) α ⟨ ∀Y.p̅[id_Y] ⟩) β ⟨ q̅ ⟩ : C[A,B]

  Yes, a swap is required!    
------------------------------------------------------------------------
More on Jeremy's counterexample

  να:=ι.(λf:(∀X.X→X).(f α ⟨ α♯→α♭ ⟩)) (ΛX.νβ:=X.λx:β.x ⟨ β! ⟩ ⟨ α? ⟩)

This is ruled out if no binding form can interpose between the introduction
of α at να:=ι and it's use at (f α).

------------------------------------------------------------------------
TODO:
Explain c[α!,α?] as a context with two holes. Give example.
In description of Figure 5, note Σ ⊆ Γ preserves order (to preserve wf)
Make sure to mention System F embedding in text
------------------------------------------------------------------------
Max,

I'm an admirer of your work on gradual typing!

I've been studying the system PolyCν from your dissertation, and
have a question about its formulation.

You extend values of universal type to include a sequence of casts,
stating "the polymorphic function proxy Λν{X.([\overbar{B⊑↕}],M)} is
essentially equivalent to a sequence of casts applied to a polymorphic
function ΛνX.M", and similarly for existentials. Here is a relevant
fragment of the grammar:

  M ::= ... | Λ{X.([\overbar{B⊑↕}], M)} | let x = M{X≅A}; N
            | pack(X≅A, [\overbar{B⊑↕}], M) | unpack (X,x) = M; N
  V ::= ... | Λ{X.([\overbar{B⊑↕}], M)}
            | pack(X≅A, [\overbar{B⊑↕}], M)

And here are the relevant reductions:

  (1)  Σ ▷ E[let x = (Λ{X.([\overbar{B⊑↕}], M)}){Y≅A}; N]
    —→ Σ, σ≅A ▷ E[let y = \overbar{⟨B⊑↕[σ/X]⟩}M[σ/X]; N[σ/Y]]
  (2)  Σ ▷ E[unpack (Y,x) = pack(X≅A, [\overbar{B⊑↕}], M); N]
    —→ Σ, σ≅A ▷ E[let x = \overbar{⟨B⊑[σ/X]⟩↕}M[σ/X]; N[σ/Y]]
  (3)  E[⟨∀X.A⊑⟩↕ Λ{Y.([\overbar{B⊑↕}], M)}]
    —→ E[Λ{Y.([A⊑[Y/X]↕, \overbar{B⊑↕}], M)}]
  (4)  E[⟨∃X.A⊑⟩↕ pack(Y≅A′, [\overbar{B⊑↕}], M)]
    —→ E[pack(Y≅A′, [A⊑[Y/X]↕, \overbar{B⊑↕}], M)

(By the way, rule (2) is not quite as in your paper; I think
your rule has a typo; I've replaced y on the rhs by x.)

If I understand correctly, an alternative formulation is possible.
Analogous to the value form ⟨A⊑→B⊑⟩↕V, one could introduce value forms
⟨∀X.A⊑⟩↕V and ⟨∃X.A⊑⟩↕V. The relevant fragment of the grammar becomes:

  M ::= ... | ΛX.M | let x=M{X≅A}; N
            | pack(X≅A, M) | unpack (X,x) = M; N
  V ::= ... | ΛX.M | ⟨∀X.A⊑⟩↕V
            | pack(X≅A, M) | ⟨∃X.A⊑⟩↕V

And the relevant reductions become:

  (1′)  Σ ▷ E[let x = (ΛX.M){Y≅A}; N]
     —→ Σ, σ≅A ▷ E[let y = M[σ/X] in N[σ/Y]]
  (2′)  Σ ▷ E[unpack (Y,x) = pack(X≅A, M); N]
     —→ Σ, σ≅A ▷ E[let x = M[σ/X]; N[σ/Y]]
  (3′)  E[let x = (⟨∀νX.A⊑⟩↕V){Y≅A}; N]
     —→ E[let y = V{Y≅A}; let x = ⟨A⊑[Y/X]⟩↕y; N]
  (4′)  E[unpack (Y,x) = ⟨∃X.A⊑⟩↕V; N]
     —→ E[unpack (Y,y) = V; let x = ⟨A⊑[Y/X]⟩↕y; N]

Indeed, your version of PolyCν in the POPL paper seems to take a
similar approach for universals (but not for existentials).

Have I understood correctly, and is this alternative version
equally valid? Did you consider it when writing your dissertation,
and if so why did you choose the form you used instead?

Thank you for your help. Go well, -- P

Hi Phil,

Thank you for your email. It's been a while, but reviewing the paper
and the dissertation, the major change I made was in eliminating an
explicit form "hide X =~ A" which was actually performing the name
generation for universal quantifiers.

It seems correct to me that your formulation is equivalent to the one
in my dissertation. As to why I made a new form of stacked proxies
rather than using the casts themselves, I'm not sure offhand. My main
goal was developing a system for which I could prove the simulation
theorem with the code in CBPV_OSum, so it may have just been more
convenient for me in that proof to distinguish between the general
cast case and the stacked proxies syntactically.

Jeremy,

Here's my summary of how to adapt Max's syntax.

E[να:=A. let x = (ΛX.V[X])α in N[x,α]]
     —→_{α:=A} E[let x = V[α] in N[x,α]]
E[να:=A. let x = (V ⟨ να.s[α] ⟩)α in N[x,α]]
     —→_{α:=A} E[let x = V ⟨ s[α] ⟩ in N[x,α]]
E[να:=A. let x = (V ⟨ ∀X.s[X] ⟩)α in N[x,α]]
     —→_{α:=A} E[να:=A. let y = V α in let x = y ⟨ s[α] ⟩ in N[x,α]]


L,M,N ::= ...
        | να:=A.let x = L α in N[x,α]
        | let x = V α in N[x,α]
        | let x = M in N[x]

(1)   E[να:=A.let x = L α in N[x,α]] —→_{α:=A} E[let x = L α in N[x,α]]

(2)   let x = (ΛX.V[X]) α in N[x,α] ⊢→ N[V[α],α]
(3)   let x = (V ⟨ νβ.s[β] ⟩) α in N[x,α] ⊢→ let x = V ⟨ s[α] ⟩ in N[x,α]
(4)   let x = (V ⟨ ∀X.s[X] ⟩) α in N[x,α] ⊢→ let y = V α in let x = y ⟨ s[α] ⟩ in N[x,α]


A different idea. Let's get rid of all the constraints on casts,
and see if anything goes wrong.

    νβ.(α♯→β?) : α→⋆ =⇒ ∀X.(⋆→X)


    ∅ ⊢ να:=⋆. (((λx:α.(κ′⟨ι!⟩) ⟨νβ.(α♯→β?)⟩) α ⟨α♯→α♭⟩) (κ ⟨ι!⟩) : ι
    (yes, this works)

    ∅ ⊢ να:=⋆. (((λx:α.(κ′⟨ι!⟩) ⟨νβ.(β♭→β?)⟩) α ⟨α♯→α♭⟩) (κ ⟨ι!⟩) : ι
    (yes, this works)

    

------------------------------------------------------------------------
Igarashi et al's F_G and F_C

Reduction rules.

               (ΛX.V[X]) A  ⊢→  V[A]
    (V : ∀X.A[X] ⇒ B[X]) C  ⊢→  V C : A[C] ⇒ B[C]
         (V : ∀X.A[X] ⇒ B)  ⊢→  V ★ : A[★] ⇒ B

           Σ ⊢ (Λα.V[α]) A  —→  Σ, α:=A ⊢ V[α]
   Σ ⊢ (V : A ⇒ ∀X.B[X]) C  —→  Σ, α:=C ⊢ V : A ⇒ B[α]

In their work, unlike in ours, one can have two kinds of variables in Λ,
and Γ, X ⊑ Γ′, α:=A with X on the left related to α on the right.

Imprecision between terms (selected special cases). Note the additional
binding χ. Note binding of χ in Λ⊑ here corresponds to idea that we have
X binding in hypothesis for term Λ, but α binding in hypothesis for term
imprecision rule Λ⊑.

  GType(Γ,A)  =  α ∉ A
  QPoly(A)    =  A ≠ ∀X.A′[X] and ★ ∈ A

  Γ ⊢ f : ∀X.B[X] ⊑_Χ Γ′ ⊢ f′ : B′
  Γ ⊢ A    GType(χ,A)    QPoly(B′)    X ∉ fv(B′)
  -----------------------------------------------
  Γ ⊢ f A : B[X:=Γ(A)] ⊑_χ Γ′ ⊢ f′ : B′

  Γ, X::L ⊢ w[X] : A[X] ⊑_{χ,X::𝒮} Γ′ ⊢ w′ : A′
  QPoly(A′)    X ∉ fv(A′)
  ---------------------------------------------
  Γ ⊢ (ΛX::L.w[X]) : (∀X.A[X]) ⊑_χ Γ′ ⊢ w′ : A′

  Γ ⊢ f : Γ(A₁) ⊑_χ Γ′ ⊢ f′ : A′
  Γ ⊢ A₁ ~ A₂    χ ⊢ A₁ ⊑ A′    χ ⊢ χ ⊢ A₂ ⊑ A′
  ---------------------------------------------
  Γ ⊢ (f : A₁ ⇒ A₂) : Γ(A₂) ⊑ Γ′ ⊢ f′ : A′

  Γ ⊢ f : A ⊑_χ Γ′ ⊢ f′ : Γ(A₁′)
  Γ′ ⊢ A₁′ ⊑ A₂′    χ ⊢ A ⊑ A₁′    χ ⊢ A ⊑ A₂′
  --------------------------------------------
  Γ ⊢ f : A ⊑ Γ ⊢ (f′ : A₁′ ⇒ A₂′) : Γ′(A₂′)

They conjecture the gradual guarantee holds for their system,
but that seems clearly false. In particular, they don't allow
an α on the right with no corresponding α on the left, so they
can't do the standard up/down examples.

  ∅ ⊢ (ΛX.λx:X.x) : (∀X.X→X) ⊑ ∅ ⊢ ((ΛX.λx:X.x) : (∀X.X→X) ⇒ (★→★)) : (★→★)

    ∅ ⊢ (ΛX.λx:X.x) : (∀X.X→X) ⇒ (★→★)
  —→
    ∅ ⊢ (ΛX.λx:X.x) ★ : (★→★) ⇒ (★→★)
  —→
    α₀:=★ ⊢ (λx:α₀.x) : (★→★) ⇒ (★→★)

But we don't have

  ∅ ⊢ (ΛX.λx:X.x) : (∀X.X→X) ⊑ α₀:=★ ⊢ ((λx:α₀.x) : (★→★) ⇒ (★→★)) : (★→★)

because it's not permitted to have a type variable on the right that
does not correspond to one on the left.
------------------------------------------------------------------------
Hi Phil, Peter,

In the notes we have:

      (1) a ∉ dom(Σ) guarantees we don't have both id_α and (α♯;p)
          in the same imprecision judgement.

      (2) G ∉ dom(Σ) guarantees we don't have both (id_α;α!) and
          (α♯;p) in the same imprecision judgement.

But I’m having trouble seeing how these invariants are maintained by
type variable substitution.

Suppose we are substituting X for α in an imprecision (e.g., triggered
by the application of a type abstraction), but the imprecision already
has α♯ inside. The substitution will turn id_X into id_α and then
the above invariant will be violated.

Here’s a small albeit contrived example:

να:=ℕ. (((ΛX. (λx:X. 0) ⟨ \dual{id_X → α♯} ⟩) α) ⟨ α♯ → α♯ ⟩)
-->
να:=ℕ. (((λx:α. 0) ⟨ \dual{id_α → α♯} ⟩) ⟨ α♯ → α♯ ⟩)


Best regards,
Jeremy
========================================================================
ABSTRACT AND INTRODUCTION
========================================================================
Abstract

There has long been a tension between achieving three key properties
of gradual typing typing. Graduality: as we upcast parts of a program
it retains its semantics. Parametricity: polymorphic terms
instantiated at related types have related semantics.
Interoperability: functions at polymorphic type may upcast to dynamic
type, and downcast vice-versa. We present the first system that
satisfies all three. Interoperability is obvious from its formulation;
we provide a direct proof of graduality; and we show parametricity by
reduction to the systems of Ahmed et al (2017) and New et al
(2020). We also introduce a number of technical innovations; in
particular, we merge the casts and conversions of Ahmed et al (2017)
into a single construct, eliminating annoying redundancies.

Traditionally, the tension between graduality and parametricity arises
because graduality demands we can upcast (∀X.X→X) to, say, (∀X.X→★),
and its semantics must not change. Conversely, parametricity demands
that (∀X.X→X) must be either the identity function or the function
that never returns, while (∀X.X→★) must be a constant function. (Here
★ is the dynamic type, also written ? in some work.) We resolve the
problem by restricting casts, so that (∀X.X→X) may be cast to itself,
satisfying reflexivity, or to (★→★) or ★, satisfying interoperability,
but not to (∀X.X→★).  Throwing out the latter loses little: the cast
adds nothing to graduality precisely because it violates
parametricity.
------------------------------------------------------------------------
Longer Abstract

There has long been a tension between achieving three key properties
of gradual typing typing. Graduality: as we upcast parts of a program
it retains its semantics. Parametricity: polymorphic terms
instantiated at related types have related semantics.
Interoperability: functions at polymorphic type may upcast to dynamic
type, and downcast vice-versa. We present the first system that
satisfies all three.

Traditionally, the tension between graduality and parametricity arises
because graduality demands we can upcast (∀X.X→X) to (∀X.X→★) or
(∀X.★→X) and its semantics should not change, where ★ is the dynamic
type, while parametricity demands (∀X.X→X) must be the identity
function or the function that never terminates, and (∀X.X→★) must be a
constant function, and (∀X.★→X) must be the function that never
terminates. We resolve the problem by restricting casts, so that
(∀X.X→X) may be cast to (★→★) or ★, but not to (∀X.X→★) or (∀X.★→X).
Throwing out the latter cast loses little: it adds nothing useful to
graduality precisely because it violates parametricity.

Traditionally, interoperability required compromises. In the presence
of interoperability, compatibility between types becomes asymmetric
and overly permissive: (∀X.X→X) casts to (A→B), for any types A and B,
while only (★→★) casts to (∀X.X→X).  Here, by restricting type
imprecision we have (∀X.X→X) casts to (★→★) but not (A→B), and vice
versa, restoring symmetry and eliminating over permissiveness. The key
to achieving this is to introduce two distinct type variables, written
X and α, that behave differently with regard to type imprecision.

Our new system satisfies graduality, parametricity, and
interoperability. Interoperability is obvious from its formulation; we
provide a direct proof of graduality; and we show parametricity by
reduction to the systems of Ahmed et al (2017) and New et al
(2020). We also introduce a number of technical innovations. We
combine casts and conversions as in Ahmed et al (2017), and tagging
and sealing as in New et al (2020), into a single construct,
eliminating annoying redundancies. We are simpler than Ahmed et al
(2017), though similar to New et al (2020), in that we replace five
relations (≺, <:, <:⁺, <:⁻, <:ₙ) by a single relation (⊑, similar to
the previous <:ₙ). The system of New et al (2020) has been criticised
because it is not obvious how to embed System F into it; we show there
is a straightforward embedding of F into their system (and ours) that
is fully abstract. Finally, Devriese et al (2018) point out that the
parametricity satisfied by gradual type systems must be weaker than
that originally defined by Reynolds (1983), because they have
non-trivial instantiations of the universal type, (∃X.∀Y.(Y→X)×(X→Y)),
obtained by instantiating X to the dynamic type ★. In our system,
instantiating X to ★ results in a trivial type, suggesting that we may
satisfy a form of parametricity stronger than previous work.
------------------------------------------------------------------------
Introduction

The quest to reconcile gradual typing with parametricity is nearing
the end of its second decade.  Siek and Taha (2006) introduced gradual
typing. Guha et al (2007) described how runtime seals could be used to
convert dynamically-typed terms to polymorphic type while ensuring
parametricity.

...

A key property of Amal et al (2011, 2017) is that a polymorphic
function with universal type is cast to a dynamically typed function
that can be applied directly. Technically, the trick is that, for
instance, we may cast ∀X.X→X to ★→★ and thence to ★. In other systems
[CITE], we cast ∀X.X→X to ∀X.★, and thence to ★, meaning that rather
than apply the polymorphic function we must first instantiate it. We
refer to the former sort of system as _adaptable_ and the latter sort
as _rigid_. Devriese et al [CITE plausible paper] refer to the former
sort as supporting _implicit_ polymorphism and the latter as
_explicit_ polymorphism, but we prefer _adaptable_ and _rigid_ as less
likely to be confused with other concepts. [Actually, Labrada et al (2022)
use the term "interoperable" instead of "adaptable", and that's just as
good-s̅̅o perhaps stick with that!]

Labrada et al (2022) refer to "harmless imprecise ascriptions":
given a term t : A and A ⊑ B, then t :: B :: A is equivalent to t
(where :: is type ascription). This is strictly weaker than the
dynamic gradual guarantee.

...

Calling a dynamically typed function from within a Λ can be tricky.
The easy way to do it is to cast the dynamically typed function
to a polymorphic type:

    id★  =  λx:★.x
    id   =  ΛX.λx:X.x
    id′  =  ΛX.λx:X.(id★ ⟨ \dual{να.α♯→α♯} ⟩) X x
         =  ΛX.λx:X.να:=X. ((id★ ⟨ \dual{να.α♯→α♯} ⟩) α ⟨ α♯→α♯ ⟩) x

But it can also be done with explicit tagging and sealing:

    id″ = ΛX.λx:X.να:=X. (id★ ⟨ \dual{α!→α!} ⟩ ⟨ α♯→α♯ ⟩)

This is actually just one reduction step applied to the previous,
so I guess that the previous is better style and easier to use.

========================================================================
EXAMPLES
========================================================================

[K example shows why we need α]

Example 1.

       ----------------------- x⊒x
       α:=★, x:α? ⊢ x ⊒ x : α?
       ------------------------------------ λ⊒λ
       α:=★ ⊢ (λx:★.x) ⊒ (λx:α.x) : (α!→α?)
       ------------------------------------- ⊒Λ
       ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) : (να.α!→α?)
       ------------------------------------------------------ -⊒ (i)
       ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⊒ (ΛX.λx:X.x) : (∀X.id_X→id_X)
       --------------------------------------------------------------- +⊒ (ii)
       ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)

       (i)     (να.α!→α?) = (να.α!→α?) ⨾ (∀X.id_X→id_X)
       (ii)    (να.α!→α?) = \dual{ν̅α.α♯→α♭} ⨾ (∀X.id_X→id_X)  

               where  \dual{ν̅α.α♯→α♭} = (να.α!→α?)

     —→
       ⊢ να:=★. (λx:★.x) ⟨ να.α!→α? ⟩ α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)
     —→
       α:=☆ ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)
     —→
       -------------------------- x⊒x
       α:=id_★, x:α? ⊢ x ⊒ x : α?
       ---------------------------------------  λ⊒λ
       α:=id_★ ⊢ (λx:★.x) ⊒ (λx:α.x) : (α!→α?)    
       ----------------------------------------------------- -⊒ (iii)
       α:=id_★ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⊒ (λx:α.x) : (id_α→id_α)    
       -----------------------------------------------------------  +⊒ (iv)
       α:=id_★ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (λx:α.x) : (α!→α?)    
       -------------------------------------------------------------- ⊒Λ
       α:=☆ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)

       (iii)   (α!→α?) = (α!→α?) ⨾ (id_α→id_α)
       (iv)    (α!→α?) = \dual{α♯→α♭} ⨾ (id_α→id_α)

               where \dual{α♯→α♭} = (α!→α?)


Example 2.

      ⊢ (λx:★.x) ⊒ (λx:★.x) : (id_★→id_★)
      ---------------------------------------------------------------- (i)
      ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (∀X.id_X→id_X)
      ------------------------------------------------------------------------- (ii)
      ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)

      (i)   (id_★→id_★) ⨾ (να.α!→α?) ≈ (να.α!→α?) ⨾ (∀X.id_X→id_X)
      (ii)  (να.α!→α?) ≈ (να.α!→α?) ⨾ (∀X.id_X→id_X)


    —↠
      ⊢ να:=★. (λx:★.x) ⟨ να.α!→α? ⟩ α ⟨ α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)
    —↠
      α:=☆ ⊢ ((λx:★.x) ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)
    —↠
      α:=id_★ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⊒ (λx:★.x) ⟨ α!→α? ⟩ : (id_α→id_α)
      ----------------------------------------------------------------------------------- (iii)
      α:=id_★ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ α!→α? ⟩ : (α!→α?)
      -------------------------------------------------------------------------------------- ⊒Λ generalised
      α:=☆ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)

      (iii)  (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)


Example 3.

      ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) : (να.α!→α?)
      --------------------------------------- ⊒α
      α:=ι ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) α : α!→α?
      ------------------------------------------------- ⊒+ (i)
      α:=ι ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ : ι!→ι?

      (i)  (ι!→ι?) ⨾ (α!→α?) ≈ α!→α?


Example 4.

      ∅ ⊢ (ΛX.λx:X.x) ⟨ ν̅α.α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)
    —→
      ∅ ⊢ να:=★.(ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)
    —→
      α:=☆ ⊢ (ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)
    —→
      α:=☆ ⊢ (λx:α.x) ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)


      ---------------------------------------------------------
      α:=☆ ⊢ (ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)


      α:=id_★ ⊢ (λx:α.x) ⊒ (λx:α.x) : id_α→id_α
      ----------------------------------------------- +⊒  (i)
      α:=id_★ ⊢ (λx:α.x) ⟨ α♯→α♭ ⟩ ⊒ (λx:α.x) : α!→α?
      ------------------------------------------------------ split
      α:=★, α₀:=☆ ⊢ (λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⊒ (λx:α.x) : α!→α?
      -------------------------------------------------------- ⊒Λ
      α₀:=☆ ⊢ (λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)


      (i)  (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)


Example 5. Example where the term on the left fails.

  c : ι′
  c★ : ★ = c ⟨ ι′! ⟩

    ∅ ⊢ (λx:★.x) c★ ⊒ ((λx:ι.x) ⟨ ι?→ι! ⟩) c★ : id_★
  —→
    ∅ ⊢ (λx:★.x) c★ ⊒ ((λx:ι.x) (c★ ⟨ ι? ⟩)) ⟨ ι! ⟩ : id_★
  —→
    ∅ ⊢ (λx:★.x) c★ ⊒ blame : id_★

    ∅ ⊢ (λx:★.x) ⊒ (λx:ι.x) : ι!→ι?
    --------------------------------------------- (i)
    ∅ ⊢ (λx:★.x) ⊒ (λx:ι.x) ⟨ ι?→ι! ⟩ : id_★→id_★        ∅ ⊢ c★ ⊒ c★ : id_★
    -----------------------------------------------------------------------
    ∅ ⊢ (λx:★.x) c★ ⊒ ((λx:ι.x) ⟨ ι?→ι! ⟩) c★ : id_★

    (i)  (id_★→id_★) ⨾ (ι!→ι?) ≈ (ι!→ι?)


Example 6. Example where the term on the left fails, with abstraction. [UPDATED]

   Assume c★ = c ⟨ ι′! ⟩ where ι ≠ ι′

    ∅ ⊢ (λx:★.x) c★ ⊒ ((να:=ι.(ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩) ⟨ ι?→ι! ⟩) c★ : id_★
  —→
    α:=ι ⊢ (λx:★.x) c★ ⊒ ((ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ ⟨ ι?→ι! ⟩) c★ : id_★
  —→
    α:=ι ⊢ (λx:★.x) c★ ⊒ ((λx:α.x) ⟨ α♯→α♭ ⟩ ⟨ ι?→ι! ⟩) c★ : id_★
  —↠
    α:=ι ⊢ (λx:★.x) c★ ⊒ (((λx:α.x) ⟨ α♯→α♭ ⟩) (c★ ⟨ ι? ⟩)) ⟨ ι! ⟩ : id_★
  —→
    α:=ι ⊢ (λx:★.x) c★ ⊒ blame

    α:=★, x:α? ⊢ x ⊒ x : α?
    ----------------------------------
    α:=★ ⊢ (λx:★.x) ⊒ (λx:α.x) : α!→α?
    -------------------------------------
    ∅ ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) : να.α!→α?
    ---------------------------------------
    α:=ι ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) α : α!→α?
    ------------------------------------------------- (i)
    α:=ι ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ : ι?→ι!
    --------------------------------------------------------------- (ii)
    α:=ι ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ ⟨ ι?→ι! ⟩ : id_★→id_★
    --------------------------------------------------------------------
    ∅ ⊢ (λx:★.x) ⊒ (να:=ι.(ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩) ⟨ ι?→ι! ⟩ : id_★→id_★    ∅ ⊢ c★ ⊒ c★ : id_★
    ------------------------------------------------------------------------------------------
    ∅ ⊢  (λx:★.x) c★⊒ ((να:=ι.(ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩) ⟨ ι?→ι! ⟩) c★ : id_★


         (i)
                       ι?→ι!
                         ∅
                    ι→ι ————→ ★→★
                     ↑      ↗
                     |     /
               α♯→α♭ |    /   α?→α!
               α:=ι  |   /      ∅
                     |  /
                    α→α  
                          

         (ii)
                          id_★→id_★
                              ∅
                    ★→★ ————————————→ ★→★
                     ↑                 ↑
                     |                 |
               ι!→ι! |        ≈        |  id_★→id_★
                 ∅   |                 |      ∅
                     |                 |
                    ι→ι ————————————→ ★→★
                            ι!→ι!
                              ∅


Example 7. Downcast preserves imprecision.

    ∅ ⊢ να:=ι.((λx:★.x) ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩ ⊒ να:=ι.(ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ : id_ι→id_ι
  —→
    α:=ι ⊢ ((λx:★.x) ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ : id_ι→id_ι
  —→
    α:=ι ⊢ ((λx:★.x) ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩ ⊒ (λx:α.x) ⟨ α♯→α♭ ⟩ : id_ι→id_ι
  —→
    α:=ι ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (λx:α.x) ⟨ α♯→α♭ ⟩ : id_ι→id_ι

      
      ∅ ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) : (να.α!→α?)
      ---------------------------------------------------------------  (να.α!→α?) ≈ (να.α!→α?) ⨾ (∀X.id_X→id_X)
      ∅ ⊢ ((λx:★.x) ⟨ να.α!→α? ⟩) ⊒ (ΛX.λx:X.x) : ∀X.id_X→id_X
      ----------------------------------------------------------------------
      α:=id_ι ⊢ ((λx:★.x) ⟨ να.α!→α? ⟩) α ⊒ (ΛX.λx:X.x) α : id_α→id_α
      ------------------------------------------------------------------------------------------
      α:=id_ι ⊢ ((λx:★.x) ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ : id_ι→id_ι
      ------------------------------------------------------------------------------------------------     
      ∅ ⊢ να:=ι.((λx:★.x) ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩ ⊒ να:=ι.(ΛX.λx:X.x) α ⟨ α♯→α♭ ⟩ : id_ι→id_ι


      α:=id_ι ⊢ (λx:★.x) ⊒ (λx:α.x) : α!→α?
      ---------------------------------------------------------- (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)
      α:=id_ι ⊢ ((λx:★.x) ⟨ α!→α? ⟩) ⊒ (λx:α.x) : id_α→id_α
      ------------------------------------------------------------------------------
      α:=id_ι ⊢ ((λx:★.x) ⟨ α!→α? ⟩) ⟨ α♯→α♭ ⟩ ⊒ (λx:α.x) ⟨ α♯→α♭ ⟩ : id_ι→id_ι


Example 8. Instantiate id at different types.

  id   = ΛX.λx:X.x
  idα  = λx:α.x
  id★  = λx:★.x
  c★   = c ⟨ ι! ⟩

    ∅ ⊢ id ★ c★ ⊒ id ι c : ι?
  ~>
    ∅ ⊢ (να:=★. id α ⟨ α♯→α♭ ⟩) c★
      ⊒ (να:=ι. id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι? ⊢ (idα ⟨ α♯→α♭ ⟩) c★
             ⊒ (idα ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι? ⊢ (idα (c★ ⟨ α♯ ⟩)) ⟨ α♭ ⟩
             ⊒ (idα (c ⟨ α♯ ⟩)) ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι? ⊢ c★ ⟨ α♯ ⟩ ⟨ α♭ ⟩
             ⊒ c ⟨ α♯ ⟩ ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι? ⊢ c★ ⊒_∅ c : ι?


    ---------------------------- (x⊒x)
    α:=ι?, x:id_α ⊢ x ⊒ x : id_α
    ----------------------------- (λ⊒λ)
    α:=ι? ⊢ idα ⊒ idα : id_α→id_α
    ----------------------------------- (derived)    (i)
    α:=ι? ⊢ (idα ⟨ α♯→α♭ ⟩)
             ⊒ (idα ⟨ α♯→α♭ ⟩) : ι!→ι?    α:=ι? ⊢ c★ ⊒ c : ι?   
    --------------------------------------------------------- (·⊒·)
    α:=ι? ⊢ (idα ⟨ α♯→α♭ ⟩) c★
             ⊒ (idα ⟨ α♯→α♭ ⟩) c : ι?

    (i)  (id_α→id_α) ⨾ (α!→α?) ≈ (α!→α?) ⨾ (ι!→ι?)


                            ι!→ι?
                                 ∅
                         ι→ι --------→ ★→★
                          ↑             ↑
                          |             |
            α♯→α♭ |      ≈      | α♯→α♭    (i)
                 α:=ι     |             |      α:=★
                          |             |
                         α→α --------→ α→α
                             id_α→id_α
                                 ∅

  How does this example look in Igarashi et al (2017)?
  Their rules are formulated for the gradual surface language, F_G.

      γ, X, x:id_X ⊢ x ⊑ x : id_X
      --------------------------------------
      γ, X ⊢ (λx:X.x) ⊑ (λx:X.x) : id_X→id_X
      ----------------------------------------------
      γ ⊢ (ΛX.λx:X.x) ⊑ (ΛX.λx:X.x) : ∀X.(id_X→id_X)    γ ⊢ ι ⊑ ★
      -----------------------------------------------------------
      γ ⊢ (ΛX.λx:X.x) ι ⊑ (ΛX.λx:X.x) ★ : ι!→ι!                      γ ⊢ c ⊑ c★ : ι!
      ------------------------------------------------------------------------------
      γ ⊢ (ΛX.λx:X.x) ι c ⊑ (ΛX.λx:X.x) ★ c★ : ι!

Example 9. Polymorphic id is less imprecise than monomorphic id.

    ∅ ⊢ id★ c★ ⊒_∅ id ι c : ι?
  ~>
    ∅ ⊢ id★ c★ ⊒_∅ (να:=ι. id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι ⊢ id★ c★ ⊒_∅ (idα ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι ⊢ id★ c★ ⊒_∅ idα (c ⟨ α♯ ⟩) ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι ⊢ c★ ⊒_∅ c ⟨ α♯ ⟩ ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι ⊢ c★ ⊒_∅ c : ι?


    -------------------------------- (x⊒x)
    α:=ι, α′:=★, x:α′? ⊢ x ⊒ x : α′?
    -------------------------------------------- (λ⊒λ)
    α:=ι, α′:=★ ⊢ (λx:★.x) ⊒ (λx:α′.x) : α′!→α′?
    -------------------------------------------- (⊒Λ)
    α:=ι ⊢ id★ ⊒ (ΛX.λx:X.x) : να.(α!→α?)
    ------------------------------------- (⊒α)
    α:=ι ⊢ id★ ⊒ id α : α!→α?
    ------------------------------------- (⊒+)  (i)
    α:=ι ⊢ id★ ⊒_∅ id α ⟨ α♯→α♭ ⟩ : ι!→ι?
    ------------------------------------------- (⊒ν)
    ∅ ⊢ id★ ⊒_∅ (να:=ι. id α ⟨ α♯→α♭ ⟩) : ι!→ι?         ∅ ⊢ c★ ⊒_∅ c : ι?
    --------------------------------------------------------------------- (·⊒·)
    ∅ ⊢ id★ c★ ⊒_∅ (να:=ι. id α ⟨ α♯→α♭ ⟩) c : ι?


    (i)  (ι!→ι?) ⨾ (α!→α?) ≈ (α!→α?)


    ----------------------- (x⊒x)
    α:=ι, x:α? ⊢ x ⊒ x : α?
    ------------------------ (λ⊒λ)
    α:=ι ⊢ id★ ⊒ idα : α!→α?
    ---------------------------------- (⊒+)
    α:=ι ⊢ id★ ⊒ idα ⟨ α♯→α♭ ⟩ : ι!→ι?         α:=ι ⊢ c★ ⊒ c : ι?
    ------------------------------------------------------------- (·⊒·)
    α:=ι ⊢ id★ c★ ⊒ (idα ⟨ α♯→α♭ ⟩) c : ι?


Example 10. Up on the right.

    ∅ ⊢ id★ c★ ⊒_∅ (id ⟨ ν̅α.α♯→α♭ ⟩) c★ : id_★
  ~>
    ∅ ⊢ id★ c★ ⊒_∅ (να:=★. id α ⟨ α♯→α♭ ⟩) c★ : id_★
  —↠
    α:=★ ⊢ id★ c★ ⊒_∅ (idα ⟨ α♯→α♭ ⟩) c★ : id_★
  —↠
    α:=★ ⊢ id★ c★ ⊒_∅ idα (c★ ⟨ α♯ ⟩) ⟨ α♭ ⟩ : id_★
  —↠
    α:=★ ⊢ c★ ⊒_∅ c★ ⟨ α♯ ⟩ ⟨ α♭ ⟩ : id_★
  —↠
    α:=★ ⊢ c★ ⊒_∅ c★ : id_★
         

    ----------------------- (x⊒x)
    α:=★, x:α? ⊢ x ⊒ x : α?
    ------------------------------------ (λ⊒λ)
    α:=★ ⊢ (λx:★.x) ⊒ (λx:α.x) : (α!→α?)
    --------------------------------------- (⊒Λ)
    ∅ ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) : (να.α!→α?)
    --------------------------------------------------- (⊒+)
    ∅ ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) ⟨ ν̅α.α♯→α♭ ⟩ : id_★→id_★

    (i)  (id_★→id_★) ⨾ (να.α!→α?) ≈ (να.α!→α?)


Example 11. Up on the left.

    ∅ ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩) c★ ⊒_∅ id ι c : ι?
  ~>
    ∅ ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩) c★ ⊒_∅ (να:=ι. id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    ∅ ⊢ (να₀:=★. id α₀ ⟨ α₀♯→α₀♭ ⟩) c★ ⊒_∅ (να:=ι. id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι, α₀:=☆ ⊢ (id α₀ ⟨ α₀♯→α₀♭ ⟩) c★ ⊒_∅ (id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι, α₀:=☆ ⊢ idα₀ (c★ ⟨ α₀♯ ⟩) ⟨ α₀♭ ⟩ ⊒_∅ idα (c ⟨ α♯ ⟩) ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι, α₀:=☆ ⊢ c★ ⟨ α₀♯ ⟩ ⟨ α₀♭ ⟩ ⊒_∅ c ⟨ α♯ ⟩ ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι, α₀:=☆ ⊢ c★ ⊒_∅ c : ι?

    ------------------------------ (x⊒x)
    α:=ι, X, x:id_X ⊢ x ⊒ x : id_X
    ------------------------------------- (λ⊒λ)
    α:=ι, X ⊢ λx:X.x ⊒ λx:X.x : id_X→id_X
    ------------------------------------- (Λ⊒Λ)
    α:=ι ⊢ id ⊒ id : ∀X.id_X→id_X
    ------------------------------------------------ (+⊒)    (i)
    α:=ι ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩) ⊒ id : (να.α!→α?)
    ------------------------------------------------ (⊒α)
    α:=ι ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩) ⊒ id α : α!→α?
    ------------------------------------------------------- (⊒+)  (ii)
    α:=ι ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩) ⊒ id α ⟨ α♯→α♭ ⟩ : ι!→ι?
    ------------------------------------------------------- (⊒ν)
    ∅ ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩) ⊒ (να:=ι. id α ⟨ α♯→α♭ ⟩) : ι!→ι?

    (i)   (να.α!→α?) ≈ (να.α!→α?) ⨾ (∀X.id_X→id_X)
    (ii)  (ι!→ι?) ⨾ (α!→α?) ≈ α!→α?


Example 12. Up and then down.

    ∅ ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩) ι c ⊒ id ι c : id_ι
  ~>
    ∅ ⊢ (να:=ι. (id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ (να:=ι. id α ⟨ α♯→α♭ ⟩) c : id_ι
  —↠
    α:=id_ι
      ⊢ ((id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : id_ι
  —↠
    α:=id_ι
      ⊢ (να₀:=★. (id α₀ ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : id_ι
  —↠
    α:=id_ι,α₀:=☆
      ⊢ (((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : id_ι
  —↠
    α:=id_ι,α₀:=☆
      ⊢ ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩) c
      ⊒ ((ƛx:α.x) ⟨ α♯→α♭ ⟩) c : id_ι
  —↠
    α:=id_ι,α₀:=☆
      ⊢ ((ƛx:α₀.x) (c ⟨ α♯ ⟩ ⟨ α! ⟩ ⟨ α₀♯ ⟩)) ⟨ α₀♭ ⟩ ⟨ α? ⟩ ⟨ α♭ ⟩
      ⊒ ((ƛx:α.x) (c ⟨ α♯ ⟩)) ⟨ α♭ ⟩ : id_ι
  —↠
    α:=id_ι,α₀:=☆
      ⊢ c ⟨ α♯ ⟩ ⟨ α! ⟩ ⟨ α₀♯ ⟩ ⟨ α₀♭ ⟩ ⟨ α? ⟩ ⟨ α♭ ⟩
      ⊒ c ⟨ α♯ ⟩ ⟨ α♭ ⟩ : id_ι
  —↠
    α:=id_ι,α₀:=☆ ⊢ c ⊒_∅ c : id_ι

   This example makes clear why we need αᵢ:=☆ bindings.
    
    --------------------------------- (x⊒x)
    α′:=id_★, x:id_α′ ⊢ x ⊒ x : id_α′
    ---------------------------------------------- (λ⊒λ)
    α′:=id_★ ⊢ (ƛx:α₀.x) ⊒ (ƛx:α₀.x) : id_α′→id_α′
    ------------------------------------------------------ (+⊒)  (i)
    α′:=id_★ ⊢ (ƛx:α′.x) ⟨ α′♯→α′♭ ⟩ ⊒ (ƛx:α′.x) : α′!→α′?   
    ---------------------------------------------------------- split
    α′:=★, α₀:=☆ ⊢ (ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⊒ (ƛx:α′.x) : α′!→α′?
    ---------------------------------------------------------- (⊒Λ)
    α₀:=☆ ⊢ (ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⊒ (ΛX.ƛx:X.x) : να.α!→α?
    ------------------------------------------------------------------------------ (-⊒)
    α₀:=☆ ⊢ (ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩ ⊒ (ΛX.ƛx:X.x) : ∀X.id_X→id_X
    ------------------------------------------------------------------------------------------ (α⊒α)
    α:=id_ι, α₀:=☆ ⊢ ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩) α ⊒ (ΛX.ƛx:X.x) α : id_α→id_α
    -------------------------------------------------------------------------------------------------------------- (derived)
    α:=id_ι, α₀:=☆ ⊢ ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.ƛx:X.x) α ⟨ α♯→α♭ ⟩ : id_ι→id_ι

    (i)   (α′!→α′?) ≈ (α′!→α′?) ⨾ (id_α′→id_α′)

    ---------------------------- (x⊒x)
    α:=ι?, x:id_α ⊢ x ⊒ x : id_α
    --------------------------------------- (λ⊒λ)
    α:=ι? ⊢ (ƛx:α.x) ⊒ (ƛx:α.x) : id_α→id_α
    --------------------------------------------- (+⊒) (i)
    α:=ι? ⊢ (ƛx:α.x) ⟨ α♯→α♭ ⟩ ⊒ (ƛx:α.x) : α!→α?
    ------------------------------------------------------ (split)
    α:=ι, α₀:=☆ ⊢ (ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⊒ (ƛx:α.x) : α!→α?
    ------------------------------------------------------------------------------ (-⊒) (ii)
    α:=id_ι, α₀:=☆ ⊢ (ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α!→α? ⟩ ⊒ (ƛx:α.x) : id_α→id_α
    -------------------------------------------------------------------------------------------------- (derived)
    α:=id_ι, α₀:=☆ ⊢ (ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (ƛx:α.x) ⟨ α♯→α♭ ⟩ : id_ι→id_ι

         (i)
                          α!→α?
                            ∅
                  α→α ————————————→ ★→★
                   ↑                 ↑
                   |                 |
         id_α→id_α |        ≈        | α♯→α♭
             ∅     |                 | α:=★
                   |                 |
                  α→α ————————————→ α→α
                        id_α→id_α
                            ∅

         (ii)
                       α!→α?
                            ∅
                  α→α ————————————→ ★→★
                   ↑                 ↑
                   |                 |
         id_α→id_α |        ≈        |  α!→α?
             ∅     |                 |    ∅
                   |                 |
                  α→α ————————————→ α→α
                        id_α→id_α
                            ∅

Example 13. Up and then down and then up. The binding list is getting longer.

    ∅ ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩) c★
      ⊒ id ι c : ι?
  ~>
    ∅ ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩) c★
      ⊒ (να:=ι. id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι
      ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩) c★
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι
      ⊢ (να₀:=★. id α₀ ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩) c★
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι, α₀:=☆
      ⊢ ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩) c★
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι, α₀:=☆
      ⊢ (να₁:=★. ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩) α₁ ⟨ α₁♯→α₁♭ ⟩) c★
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ (((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩) α₁ ⟨ α₁♯→α₁♭ ⟩) c★
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : ι?
  —↠  
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α₁!→α₁? ⟩ ⟨ α₁♯→α₁♭ ⟩) c★
      ⊒ ((ƛx:α.x) ⟨ α♯→α♭ ⟩) c : ι?
  —↠  
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ ((ƛx:α₀.x) (c★ ⟨ α₁♯ ⟩ ⟨ α₁! ⟩ ⟨ α₀♯ ⟩)) ⟨ α₀♭ ⟩ ⟨ α₁? ⟩ ⟨ α₁♭ ⟩
      ⊒ ((ƛx:α.x) (c ⟨ α♯ ⟩)) ⟨ α♭ ⟩ : ι?
  —↠  
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ c★ ⟨ α₁♯ ⟩ ⟨ α₁! ⟩ ⟨ α₀♯ ⟩ ⟨ α₀♭ ⟩ ⟨ α₁? ⟩ ⟨ α₁♭ ⟩
      ⊒ c ⟨ α♯ ⟩ ⟨ α♭ ⟩ : ι?
  —↠  
    α:=ι, α₀:=☆, α₁:=☆ ⊢ c★ ⊒ c : ι?


    α:=ι ⊢ id ⊒ id : (∀X.id_X→id_X)
    ---------------------------------------- +⊒ (i)
    α:=ι ⊢ id ⟨ ν̅α.α♯→α♭ ⟩ ⊒ id : (να.α!→α?)
    ---------------------------------------------------------------- -⊒ (i)
    α:=ι ⊢ id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⊒ id : (∀X.id_X→id_X)
    -------------------------------------------------------------------- +⊒ (i)
    α:=ι ⊢ id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩
         ⊒ id : (να.α!→α?)
    -------------------------------------------------------------------- ⊒α
    α:=ι ⊢ id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩
         ⊒ id α : (α!→α?)
    ----------------------------------------------------------------- ⊒+ (ii)
    α:=ι ⊢ id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩
         ⊒ id α ⟨ α♯→α♭ ⟩ : (ι!→ι?)

    (i)   (να.α!→α?) ≈ (να.α!→α?) ⨾ (∀X.id_X→id_X)
    (ii)  (ι!→ι?) ⨾ (α!→α?) ≈ (α!→α?)


    α:=ι? ⊢ (λx:α.x) ⊒ (λx:α.x) : (id_α→id_α)
    ----------------------------------------------- +⊒  (i)
    α:=ι? ⊢ (λx:α.x) ⟨ α♯→α♭ ⟩ ⊒ (λx:α.x) : (α!→α?)
    ----------------------------------------------- ⊒Λ
    α:=ι? ⊢ (λx:α.x) ⟨ α♯→α♭ ⟩ ⊒ id : (να.α!→α?)
    -------------------------------------------------------------------- -⊒ (ii)
    α:=ι? ⊢ (λx:α.x) ⟨ α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⊒ id : (∀X.id_X→id_X)
    -------------------------------------------------------------------- +⊒ (ii)
    α:=ι? ⊢ (λx:α.x) ⟨ α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩
      ⊒ id : (να.α!→α?)
    -------------------------------------------------------------------- ⊒α
    α:=ι? ⊢ (λx:α.x) ⟨ α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩
      ⊒ id α : α!→α?
    --------------------------------------------------------------- ⊒+ (iii)
    α:=ι? ⊢ (λx:α.x) ⟨ α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩
      ⊒ id α ⟨ α♯→α♭ ⟩ : ι!→ι?

    (i)    (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)
    (ii)   (να.α!→α?) ≈ (να.α!→α?) ⨾ (∀X.id_X→id_X)
    (iii)  (ι!→ι?) ⨾ (α!→α?) ≈ (α!→α?)


    α:=ι? ⊢ (ƛx:α.x) ⊒ (ƛx:α.x) : id_α→id_α
    --------------------------------------- +⊒  (i)
    α:=ι? ⊢ (ƛx:α.x) ⟨ α♯→α♭ ⟩
      ⊒ (ƛx:α.x) : α!→α?
    --------------------------------------------- -⊒  (ii)
    α:=ι?, α₀:=☆ ⊢ (ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α!→α? ⟩
      ⊒ (ƛx:α.x) : id_α→id_α
    -------------------------------------------------------------- +⊒ (iii)
    α:=ι?, α₀:=☆ ⊢ ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩)
      ⊒ (ƛx:α.x) : α!→α?
    -------------------------------------------------------------- ⊒+ (iv)
    α:=ι?, α₀:=☆ ⊢ ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩)
      ⊒ ((ƛx:α.x) ⟨ α♯→α♭ ⟩) : ι!→ι?

    (i)    (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)
    (ii)   (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)
    (iii)  (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)
    (iv)   (ι!→ι?) ⨾ (α!→α?) ≈ (α!→α?)


Example 14. Up and then down and then up and then down.

    ∅ ⊢ (id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩) ι c
      ⊒ id ι c : id_ι
  ~>
    ∅ ⊢ (να:=ι. (id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ (να:=ι. id α ⟨ α♯→α♭ ⟩) c : id_ι
  —→
    α:=id_ι
      ⊢ ((id ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : id_ι
  —→
    α:=id_ι
      ⊢ ((να₀:=★. id α₀ ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : id_ι
  —→
    α:=id_ι, α₀:=☆
      ⊢ ((id α₀ ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ (id α ⟨ α♯→α♭ ⟩) c : id_ι
  —→
    α:=id_ι, α₀:=☆
      ⊢ ((λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ ((λx:α.x) ⟨ α♯→α♭ ⟩) c : id_ι
  —→
    α:=id_ι, α₀:=☆
      ⊢ (να₁:=★. (((λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩) α₁ ⟨ α₁♯→α₁♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ ((λx:α.x) ⟨ α♯→α♭ ⟩) c : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ ((((λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩) α₁ ⟨ α₁♯→α₁♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ ((λx:α.x) ⟨ α♯→α♭ ⟩) c : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ (((λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α₁!→α₁? ⟩ ⟨ α₁♯→α₁♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ ((λx:α.x) ⟨ α♯→α♭ ⟩) c : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ ((λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α₁!→α₁? ⟩ ⟨ α₁♯→α₁♭ ⟩ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩) c
      ⊒ ((λx:α.x) ⟨ α♯→α♭ ⟩) c : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ ((λx:α₀.x) (c ⟨ α♯ ⟩ ⟨ α! ⟩ ⟨ α₁♯ ⟩ ⟨ α₁! ⟩ ⟨ α₀♯ ⟩)) ⟨ α₀♭ ⟩ ⟨ α₁? ⟩ ⟨ α₁♭ ⟩ ⟨ α? ⟩ ⟨ α♭ ⟩
      ⊒ ((λx:α.x) (c ⟨ α♯ ⟩)) ⟨ α♭ ⟩ : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ c ⟨ α♯ ⟩ ⟨ α! ⟩ ⟨ α₁♯ ⟩ ⟨ α₁! ⟩ ⟨ α₀♯ ⟩ ⟨ α₀♭ ⟩ ⟨ α₁? ⟩ ⟨ α₁♭ ⟩ ⟨ α? ⟩ ⟨ α♭ ⟩
      ⊒ c ⟨ α♯ ⟩ ⟨ α♭ ⟩ : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ c ⊒ c : id_ι


    α:=ι?
      ⊢ (λx:α.x)
      ⊒ (λx:α.x) : id_α→id_α
    -------------------------
    α:=ι, α₀:=☆
      ⊢ (λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩
      ⊒ (λx:α.x) : α!→α?
    ------------------------------------------------- (i)
    α:=ι?, α₀:=☆
      ⊢ (λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α!→α? ⟩
      ⊒ (λx:α.x) : id_α→id_α
    ---------------------------------------------------------------- (ii)
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ (λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α₁!→α₁? ⟩ ⟨ α₁♯→α₁♭ ⟩
      ⊒ (λx:α.x) : α!→α?
    --------------------------------------------------------------------------------------
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ (λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α₁!→α₁? ⟩ ⟨ α₁♯→α₁♭ ⟩ ⟨ α!→α? ⟩
      ⊒ (λx:α.x) : id_α→id_α
    ------------------------------------------------------------------------------------------------
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ (λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α₁!→α₁? ⟩ ⟨ α₁♯→α₁♭ ⟩ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩
      ⊒ (λx:α.x) ⟨ α♯→α♭ ⟩ : id_ι→id_ι

      (i)
                        α!→α?
                          ∅
                  α→α --------> ★→★ 
                   ↑             ↑
         id_α→id_α |      ≈      | α♯→α♭
             ∅     |             | α:=★
                  α→α --------> α→α
                      id_α→id_α
                          ∅

      (ii)
                        α!→α?
                          ∅
                  α→α --------> ★→★ 
                   ↑             ↑
         id_α→id_α |      ≈      | α!→α?
             ∅     |             |   ∅
                  α→α --------> α→α
                      id_α→id_α
                          ∅

Example 15. Down on the left.

    ∅ ⊢ (id★ ⟨ να.α!→α? ⟩) ι c ⊒_∅ id ι c : id_ι
  ~>
    ∅ ⊢ (να:=ι. (id★ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
      ⊒ (να:=ι. id α ⟨ α♯→α♭ ⟩) c : id_ι
  —↠
    α:=id_ι ⊢ ((id★ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
            ⊒ (idα ⟨ α♯→α♭ ⟩) c : id_ι
  —↠
    α:=id_ι ⊢   ((id★ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c
            ⊒_∅ (idα ⟨ α♯→α♭ ⟩) c : id_ι
  —↠
    α:=id_ι ⊢   (id★ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩) c
            ⊒_∅ (idα ⟨ α♯→α♭ ⟩) c : id_ι
  —↠
    α:=id_ι ⊢   (id★ (c ⟨ α♯ ⟩ ⟨ α! ⟩)) ⟨ α? ⟩ ⟨ α♭ ⟩
            ⊒_∅ (idα (c ⟨ α♯ ⟩)) ⟨ α♭ ⟩ : id_ι
  —↠
    α:=id_ι ⊢   c ⟨ α♯ ⟩ ⟨ α! ⟩ ⟨ α? ⟩ ⟨ α♭ ⟩
            ⊒_∅ c ⟨ α♯ ⟩ ⟨ α♭ ⟩ : id_ι
  —↠
    α:=id_ι ⊢ c ⊒_∅ c : id_ι
  

Example 16. Down on the right

    ∅ ⊢ id★ c★ ⊒ (id★ ⟨ να.α!→α? ⟩) ι c : ι?
  ~>
    ∅ ⊢ id★ c★ ⊒ να:=ι.((id★ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c : ι?
  —→
    α:=ι ⊢ id★ c★ ⊒ ((id★ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩) c : ι?
  —→
    α:=ι ⊢ id★ c★ ⊒ (id★ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι ⊢ id★ c★ ⊒ (id★ (c ⟨ α♯ ⟩ ⟨ α! ⟩)) ⟨ α? ⟩ ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι ⊢ c★ ⊒ c ⟨ α♯ ⟩ ⟨ α! ⟩ ⟨ α? ⟩ ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι ⊢ c★ ⊒ c : ι?

    α:=ι ⊢ id★ ⊒  id★ : id_★→id_★
    ------------------------------------------ (ii)
    α:=ι ⊢ id★ ⊒ id★ ⟨ α!→α? ⟩ : α!→α?
    ---------------------------------------------------- (i)
    α:=ι ⊢ id★ ⊒ id★ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ : ι!→ι?        α:=ι ⊢ c★ ⊒ c : ι?
    ------------------------------------------------------------------------------
    α:=ι ⊢ id★ c★ ⊒ (id★ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩) c : ι?

    (i)   (ι!→ι?)⨾(α!→α?) = α!→α?
    (ii)  (id_★→id_★)⨾(α!→α?) ≈ (α!→α?)


Example 17. Constant function. Polymorphic less imprecise then monomorphic.

    K    = ΛX.ΛY.λx:X.λy:Y.x
    Kα   = ΛY.λx:α.λy:Y.x
    Kαβ  = λx:α.λy:β.x
    K★   = λx:★.λy:★.x

    ∅ ⊢ K★ 42★ ⊒ K ι ι 42 : ι?
  ~>
    ∅ ⊢ K★ 42★
      ⊒ (νβ:=ι.(να:=ι.K α ⟨ ∀Y.α♯→id_Y→α♭ ⟩) β ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι ⊢ K★ 42★ 69★
         ⊒ (νβ:=ι.(Kα ⟨ ∀Y.α♯→id_Y→α♭ ⟩) β ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι, β:=ι ⊢ K★ 42★ 69★
               ⊒ (Kαβ ⟨ α♯→id_β→α♭ ⟩ ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι, β:=ι ⊢ K★ 42★ 69★
               ⊒ (Kαβ ⟨ α♯→id_β→α♭ ⟩ ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι, β:=ι ⊢ K★ 42★ 69★
               ⊒ Kαβ (42 ⟨ id_ι ⟩ ⟨ α♯ ⟩) (69 ⟨ β♯ ⟩ ⟨ id_β ⟩) ⟨ α♭ ⟩ ⟨ id_ι ⟩ : ι?
  —↠
    α:=ι, β:=ι ⊢ K★ 42★ 69★
               ⊒ Kαβ (42 ⟨ α♯ ⟩) (69 ⟨ β♯ ⟩) ⟨ α♭ ⟩ ⟨ id_ι ⟩ : ι?
  —↠
    α:=ι, β:=ι ⊢ 42★ ⊒ 42 ⟨ α♯ ⟩ ⟨ α♭ ⟩ ⟨ id_ι ⟩ : ι?
  —↠
    α:=ι, β:=ι ⊢ 42★ ⊒ 42 : ι?


  α:=★, β:=★, x:α?, y:β? ⊢ x ⊒ x : α?
  ----------------------------------------------
  α:=★, β:=★, x:α? ⊢ (λy:★.x) ⊒ (λy:β.x) : β!→α?
  -----------------------------------------------------
  α:=★, β:=★ ⊢ (λx:★.λy:★.x) ⊒ (λx:α.λy:β.x) : α!→β!→α?
  -----------------------------------------------------
  α:=★ ⊢ (λx:★.λy:★.x) ⊒ (ΛY.λx:α.λy:Y.x) : νβ.α!→β♯→α?
  ------------------------------------------------------
  ⊢ (λx:★.λy:★.x) ⊒ (ΛX.ΛY.λx:X.λy:Y.x) : να.νβ.α♯→β♯→α♭


  α:=ι, β:=ι, x:α?, y:β? ⊢ x ⊒ x : α?
  ------------------------------------------
  α:=ι, β:=ι, x:α? ⊢ λy:★.x ⊒ λy:β.x : β!→α?
  ------------------------------------------
  α:=ι, β:=ι ⊢ K★ ⊒ Kαβ : α!→β!→α?
  ----------------------------------------------- ⊒+ (i)
  α:=ι, β:=ι ⊢ K★ ⊒ Kαβ ⟨ α♯→id_β→α♭ ⟩ : ι!→β!→ι?
  ---------------------------------------------------------------- ⊒+ (ii)
  α:=ι, β:=ι ⊢ K★ ⊒ Kαβ ⟨ α♯→id_β→α♭ ⟩ ⟨ id_ι→β♯→id_ι ⟩ : ι!→ι!→ι?


  (i)  (ι!→β!→ι?) ⨾ (α♯→id_β→α♭) ≈ α!→β!→α?
  (ii) (ι!→ι!→ι?) ⨾ (id_ι→β♯→id_ι) ≈ ι!→β!→ι?


Example 18. Constant function, up on the right.

    ∅ ⊢ (K ⟨ ν̅α.ν̅β.α♯→β♯→α♭ ⟩) 42★ ⊒ K ι ι 42 : ι?
  ~>
    ∅ ⊢   (K ⟨ ν̅α.ν̅β.α♯→β♯→α♭ ⟩) 42★ 69★
      ⊒_∅ (νβ:=ι.(να:=ι.K α ⟨ ∀Y.α♯→id_Y→α♭ ⟩) β ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι ⊢   (K ⟨ ν̅α.ν̅β.α♯→β♯→α♭ ⟩) 42★ 69★
         ⊒_∅ (νβ:=ι.(Kα ⟨ ∀Y.α♯→id_Y→α♭ ⟩) β ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι, β:=ι ⊢   (K ⟨ ν̅α.ν̅β.α♯→β♯→α♭ ⟩) 42★ 69★
               ⊒_∅ (Kαβ ⟨ α♯→id_β→α♭ ⟩ ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  ~>
    α:=ι, β:=ι
      ⊢ (να₀:=★. K α₀ ⟨ ν̅β.α♯→β♯→α♭ ⟩) 42★ 69★
      ⊒ (K α β ⟨ α♯→id_β→α♭ ⟩ ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι, β:=ι, α₀:=☆
      ⊢ (K α₀ ⟨ ν̅β.α₀♯→β♯→α₀♭ ⟩) 42★ 69★
      ⊒ (K α β ⟨ α♯→id_β→α♭ ⟩ ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι, β:=ι, α₀:=☆
      ⊢ (νβ₀:=★. K α₀ β₀ ⟨ α₀♯→β₀♯→α₀♭ ⟩) 42★ 69★
      ⊒ (K α β ⟨ α♯→id_β→α♭ ⟩ ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆
      ⊢ (K α₀ β₀ ⟨ α₀♯→β₀♯→α₀♭ ⟩) 42★ 69★
      ⊒ (K α β ⟨ α♯→id_β→α♭ ⟩ ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆
      ⊢ ((λx:α₀.λy:β₀.x) ⟨ α₀♯→β₀♯→α₀♭ ⟩) 42★ 69★
      ⊒ ((λx:α.λy:β.x) ⟨ α♯→id_β→α♭ ⟩ ⟨ id_ι→β♯→id_ι ⟩) 42 69 : ι?
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆
      ⊢ ((λx:α₀.λy:β₀.x) (42★ ⟨ α₀♯ ⟩) (69★ ⟨ β₀♯ ⟩)) ⟨ α₀♭ ⟩
      ⊒ ((λx:α.λy:β.x) (42 ⟨ id_ι ⟩ ⟨ α♯ ⟩) (69 ⟨ β♯ ⟩ ⟨ id_β ⟩)) ⟨ α♭ ⟩ ⟨ id_ι ⟩ : ι?
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆
      ⊢ 42★ ⟨ α₀♯ ⟩ ⟨ α₀♭ ⟩
      ⊒ 42 ⟨ id_ι ⟩ ⟨ α♯ ⟩ ⟨ α♭ ⟩ ⟨ id_ι ⟩ : ι?
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆ ⊢ 42★ ⊒ 42 : ι?


Example 19. An example to demonstrate rebinding

    ∅ ⊢ (λx:★.(λy:★.y)x)c★ ⊒ (ΛX.λx:X.(ΛY.λy:Y.y)Xx)ιc : ι?
  ~>
    ∅ ⊢ (λx:★.(λy:★.y)x)c★ ⊒ (να:=ι.(ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x)α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι ⊢ (λx:★.(λy:★.y)x)c★ ⊒ ((ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x)α ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι ⊢ (λx:★.(λy:★.y)x)c★ ⊒ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x) ⟨ α♯→α♭ ⟩) c : ι?
  —↠
    α:=ι ⊢ (λx:★.(λy:★.y)x)c★ ⊒ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x) (c ⟨ α♯ ⟩) ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι ⊢ (λy:★.y)c★ ⊒ ((νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)(c ⟨ α♯ ⟩)) ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι, β:=α ⊢ (λy:★.y)c★ ⊒ ((ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)(c ⟨ α♯ ⟩)) ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι, β:=α ⊢ (λy:★.y)c★ ⊒ ((λy:β.y) ⟨ β♯→β♭ ⟩)(c ⟨ α♯ ⟩)) ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι, β:=α ⊢ (λy:★.y)c★ ⊒ ((λy:β.y) (c ⟨ α♯ ⟩ ⟨ β♯ ⟩)) ⟨ β♭ ⟩ ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι, β:=α ⊢ c★ ⊒ c ⟨ α♯ ⟩ ⟨ β♯ ⟩ ⟨ β♭ ⟩ ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι, β:=α ⊢ c★ ⊒ c ⟨ α♯ ⟩ ⟨ α♭ ⟩ : ι?
  —↠
    α:=ι, β:=α ⊢ c★ ⊒ c : ι?



    -----------------------------------
    α:=★, x:α?, β:=α, y:β? ⊢ y ⊒ y : β?
    ----------------------------------------------
    α:=★, x:α?, β:=α ⊢ (λy:★.y) ⊒ (λy:β.y) : β!→β?
    ------------------------------------------------------
    α:=★, x:α?, β:=α ⊢ (λy:★.y) ⊒ (ΛY.λy:Y.y) : (νβ.β!→β?)
    ------------------------------------------------------
    α:=★, x:α?, β:=α ⊢ (λy:★.y) ⊒ (ΛY.λy:Y.y)β : β!→β?
    ------------------------------------------------------------ (i)
    α:=★, x:α?, β:=α ⊢ (λy:★.y) ⊒ (ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩ : α!→α?
    ------------------------------------------------------------
    α:=★, x:α? ⊢ (λy:★.y) ⊒ νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩ : α!→α?    α:=★, α? ⊢ x ⊒ x : α?
    -------------------------------------------------------------------------------------
    α:=★, x:α? ⊢ (λy:★.y)x ⊒ (νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x : α?
    ------------------------------------------------------------------------
    α:=★ ⊢ (λx:★.(λy:★.y)x) ⊒ (λx:α.(νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x) : α!→α?
    -----------------------------------------------------------------------------
    ∅ ⊢ (λx:★.(λy:★.y)x) ⊒ (ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x) : (να.α!→α?)
    -----------------------------------------------------------------------------
    α:=ι ⊢ (λx:★.(λy:★.y)x) ⊒ (ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x)α : α!→α?
    -------------------------------------------------------------------------------------- (ii)
    α:=ι ⊢ (λx:★.(λy:★.y)x) ⊒ (ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x)α ⟨ α♯→α♭ ⟩ : ι!→ι?
    -------------------------------------------------------------------------------------------
    ∅ ⊢ (λx:★.(λy:★.y)x) ⊒ (να:=ι.(ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x)α ⟨ α♯→α♭ ⟩) : ι!→ι?    ∅ ⊢ c★ ⊒ c : ι?
    --------------------------------------------------------------------------------------------------------------
    ∅ ⊢ (λx:★.(λy:★.y)x)c★ ⊒ (να:=ι.(ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x)α ⟨ α♯→α♭ ⟩) c : ι?

    (i)  (α!→α?) ⨾ (β♯→β♭) ≈ β!→β?
    (ii) (ι!→ι?) ⨾ (α♯→α♭) ≈ α!→α?

    α:=ι, x:α?, β:=α, y:β? ⊢ y ⊒ y : β?
    ----------------------------------------------
    α:=ι, x:α?, β:=α ⊢ (λy:★.y) ⊒ (λy:β.y) : β!→β?
    ------------------------------------------------------
    α:=ι, x:α?, β:=α ⊢ (λy:★.y) ⊒ (ΛY.λy:Y.y) : (νβ.β!→β?)
    ------------------------------------------------------
    α:=ι, x:α?, β:=α ⊢ (λy:★.y) ⊒ (ΛY.λy:Y.y)β : β!→β?
    ------------------------------------------------------------
    α:=ι, x:α?, β:=α ⊢ (λy:★.y) ⊒ (ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩ : α!→α?
    --------------------------------------------------------------
    α:=ι, x:α? ⊢ (λy:★.y) ⊒ (νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩) : α!→α?    α:=ι, x:α? ⊢ x ⊒ x : α?
    -----------------------------------------------------------------------------------------
    α:=ι, x:α? ⊢ (λy:★.y)x ⊒ (νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x : α?
    ------------------------------------------------------------------------
    α:=ι ⊢ (λx:★.(λy:★.y)x) ⊒ (λx:α.(νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x) : α!→α?
    ------------------------------------------------------------------------------------
    α:=ι ⊢ (λx:★.(λy:★.y)x) ⊒ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x) ⟨ α♯→α♭ ⟩) : ι!→ι?    α:=ι ⊢ c★ ⊒ c : ι?
    ----------------------------------------------------------------------------------------------------------
    α:=ι ⊢ (λx:★.(λy:★.y)x)c★ ⊒ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β ⟨ β♯→β♭ ⟩)x) ⟨ α♯→α♭ ⟩) c : ι?


Example 20. Example of final case of ν upcast lemma

    ∅ ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)
  —→
    ∅ ⊢ να:=★. (λx:★.x) ⟨ να.α!→α? ⟩ α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)
  —→
    α:=☆ ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ α ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)
  —→
    α:=☆ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)

    ----------------------- x⊒x
    α:=★, x:α? ⊢ x ⊒ x : α?
    ------------------------------------ λ⊒λ
    α:=★ ⊢ (λx:★.x) ⊒ (λx:α.x) : (α!→α?)
    --------------------------------------- ⊒Λ
    ∅ ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) : (να.α!→α?)
    --------------------------------------------------------------- -⊒  (i)
    ∅ ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⊒ (ΛX.λx:X.x) : (∀X.id_X→id_X)
    ------------------------------------------------------------------------ +⊒  (i)
    ∅ ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)

    (i)   (να.α!→α?) ≈ (να.α!→α?) ⨾ (∀X.id_X→id_X)

    ----------------------- x⊒x
    α:=★, x:α? ⊢ x ⊒ x : α?
    --------------------------------------- λ⊒λ
    α:=id_★ ⊢ (λx:★.x) ⊒ (λx:α.x) : (α!→α?)
    ------------------------------------------------------------ -⊒  (i)
    α:=id_★ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⊒ (λx:α.x) : (id_α→id_α)
    ------------------------------------------------------------------ +⊒  (i)
    α:=id_★ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (λx:α.x) : (α!→α?)
    --------------------------------------------------------------------- ⊒Λ
    α:=☆ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)

    (i)   (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)


Example 21. Double ν downcast (demonstrates need for ⊒⟨ν⟩)

    ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)
  —→
    ⊢ να:=★. (λx:★.x) ⟨ να.α!→α? ⟩ α ⟨ α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)
  —→
    α:=☆ ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ α ⟨ α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)
  —→
    α:=☆ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)


    ⊢ (λx:★.x) ⊒ (λx:★.x) : (id_★→id_★)
    ---------------------------------------------------------------- -⊒- (i)
    ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (∀X.id_X→id_X)
    ------------------------------------------------------------------------- +⊒ (ii)
    ⊢ (λx:★.x) ⟨ να.α!→α? ⟩ ⟨ ν̅α.α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)

    (i)    (id_★→id_★) ⨾ (να.α!→α?) ≈ (να.α!→α?) ⨾ (∀X.id_X→id_X)
    (ii)   (να.α!→α?) ≈ (να.α!→α?) ⨾ (∀X.id_X→id_X)

    α:=id_★ ⊢ (λx:★.x) ⊒ (λx:★.x) : (id_★→id_★)
    --------------------------------------------------------------- -⊒- (iii)
    α:=id_★ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⊒ (λx:★.x) ⟨ α!→α? ⟩ : (id_α→id_α)
    --------------------------------------------------------------------- +⊒ (iv)
    α:=id_★ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (λx:★.x) ⟨ α!→α? ⟩ : (α!→α?)
    ----------------------------------------------------------------------------- split
    α₀:=☆, α:=⋆ ⊢ (λx:★.x) ⟨ α₀!→α₀? ⟩ ⟨ α₀♯→α₀♭ ⟩ ⊒ (λx:★.x) ⟨ α!→α? ⟩ : (α!→α?)    
    ----------------------------------------------------------------------------- ⊒⟨ν⟩
    α₀:=☆ ⊢ (λx:★.x) ⟨ α₀!→α₀? ⟩ ⟨ α₀♯→α₀♭ ⟩ ⊒ (λx:★.x) ⟨ να.α!→α? ⟩ : (να.α!→α?)

    (iii) (id_★→id_★) ⨾ (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)
    (iv)  (α!→α?) ≈ (α!→α?) ⨾ (id_α→id_α)

  
Example 22. Power of imprecision.

  Consider the following two imprecision relations:

    (να.∀Y.α!→id_Y→α?)    :  (∀Y.★→Y→ ★) ⊒ (∀X.∀Y.X→Y→X)
    (∀X.νβ.id_X→β?→id_X)  :  (∀X.X→★→ X) ⊒ (∀X.∀Y.X→Y→X)

  In the system of Amahl et al 2017 or Igarashi et al 2017, the first is
  permitted but the second is not.  Ours permits both.


================================================================================
THE DEVELOPMENT
================================================================================

## Syntax

  Type                A,B,C      ::=  α | X | ι | ★ | A→B | ∀X.B[X]
  Ground type         G,H        ::=  α | ι | ★→★
  Imprecision         c,d        ::=  id_A | c;d | c→d | ∀X.c[X] | να.c[α] | ν̅α.c[α]
                                    | G! | G?^ℓ | α♯ | α♭
  Term                L,M,N      ::=  x | κ | M ⊕ N | λx.N[x] | L M | ΛX.V[X]
                                    | να:=A. L α ⟨ c[α] ⟩ | V α | M ⟨ c ⟩ | blame ℓ
  Value               V,W        ::=  λx.N[x] | ΛX.V[X] | κ | V ⟨ c→d ⟩ | V ⟨ ∀X.c[X] ⟩
                                    | V ⟨ να.c[α] ⟩ | V ⟨ G! ⟩ | V ⟨ α♯ ⟩
  Type context        Γ,Δ        ::=  ∅ | Γ, α:=A | Γ, X | Γ, x:A
  Store               Σ,Π        ::=  ∅ | Σ, α:=A
  Evaluation context  E          ::=  □ | E ⊕ M | V ⊕ E | E M | V E | E ⟨ c ⟩ | να.E α ⟨ c ⟩


## Embedding System F

  We have the following embedding of System F into our system.
     Assume Γ ⊢ L : ∀X.B[X].
     (L A) ~> (να:=A. L α ⟨ B[α♯] ⟩
  where B[α♯] : B[α] ⊑_{α:=A} B[A].


## Coercions (c : A =⇒_Σ B)

    ----------------
    id_A : A ==>_Σ A

    c : A =⇒_Σ B    d : B =⇒_Σ C
    ----------------------------
    (c ; d) : A =⇒_Σ C

    c : A′ =⇒_Σ A    d : B =⇒_Σ B′
    ------------------------------
    (c→d) : (A→B) =⇒_Σ (A′→B′)

    c[X] : A[X] =⇒_Σ B[X]
    ------------------------------------
    (∀X.c[X]) : (∀X.A[X]) =⇒_Σ (∀X.B[X])

    c[α] : A =⇒_Σ B[α]
    ---------------------------- α ∉ fv(A), α ∈ fv(B[α])
    (να.c[α]) : A =⇒_Σ (∀X.B[X])

    c[α] : B[α] =⇒_{Σ,α:=★} A
    ---------------------------- α ∉ fv(A), α ∈ fv(B[α])
    (ν̅α.c[α]) : (∀X.B[X]) =⇒_Σ A

    ------------- if G=α then α ∉ dom(Σ)  (i)
    G! : G =⇒_Σ ★

    --------------- if G=α then α ∉ dom(Σ)  (i)
    G?^ℓ : ★ =⇒_Σ G

    ------------- (α:=A) ∈ Σ
    α♯ : A =⇒_Σ α

    ------------- (α:=A) ∈ Σ
    α♭ : α =⇒_Σ A

    (i)  guarantees we don't have both α! and α♯
         in the same imprecision judgement.

  Lemma.  Derivation determines types and store.
    if c : A =⇒_Σ B and c : A′ =⇒_Σ′ B′ then
    types and stores agree: A = A′ and B = B′ and Σ = Σ′.

## Discussion

An example of a term that breaks the invariant on coercions if the body
of ν bindings is not sufficiently restricted.

    (να:=ι.(λz:(∀X.α→X). z α ⟨ α♯→α♭ ⟩) ((λx:α.κ ⟨ ι! ⟩) ⟨ νβ.(α♭→β?) ⟩)) κ
  —→
    α:=ι ⊢ ((λz:(∀X.α→X). z α ⟨ α♯→α♭ ⟩)((λx:α.κ ⟨ ι! ⟩) ⟨ νβ.(α♭→β?) ⟩)) κ
  —→
    α:=ι ⊢ (((λx:α.κ ⟨ ι! ⟩) ⟨ νβ.(α♭→β?) ⟩) α ⟨ α♯→α♭ ⟩) κ
  —→
    α:=ι ⊢ ((λx:α.κ ⟨ ι! ⟩) ⟨ (α♭→α?) ⟩ ⟨ α♯→α♭ ⟩) κ
  —→
    α:=ι ⊢ ((λx:α.κ ⟨ ι! ⟩) ⟨ (α♭→α?) ⟩) (κ ⟨ α♯ ⟩) ⟨ α♭ ⟩
  —→
    α:=ι ⊢ ((λx:α.κ ⟨ ι! ⟩) (κ ⟨ α♯ ⟩ ⟨ α♭ ⟩) ⟨ α? ⟩ ⟨ α♭ ⟩
  —→
    α:=ι ⊢ (λx:α.κ ⟨ ι! ⟩) κ  ⟨ α? ⟩ ⟨ α♭ ⟩
  —→
    α:=ι ⊢ κ ⟨ ι! ⟩ ⟨ α? ⟩ ⟨ α♭ ⟩
  —→
    α:=ι ⊢ blame

The invariant gets broken but nothing else goes wrong. Do we
need the invariant?


## Free type and store variables

  Free type variables of a type

    fv(α)        =  {α}
    fv(X)        =  {X}
    fv(ι)        =  ∅
    fv(★)        =  ∅
    fv(A→B)      =  fv(A) ∪ fv(B)
    fv(∀X.A[X])  =  fv(A[X]) / {X}

  Free type variables of a coercion

    ftv(id_A)     =  fv(A)
    ftv(c;d)      =  ftv(c) ∪ ftv(d)
    ftv(c→d)      =  ftv(c) ∪ ftv(d)
    ftv(∀X.c[X])  =  ftv(c[X]) / {X}
    ftv(να.c[α])  =  ftv(c[α])
    ftv(ν̅α.c[α])  =  ftv(c[α])
    ftv(G!)       =  ftv(G)
    ftv(G?)       =  ftv(G)
    ftv(α♯)       =  ∅
    ftv(α♭)       =  ∅

  Free store variables of a coercion

    fsv(id_A)     =  ∅
    fsv(c;d)      =  fsv(c) ∪ fsv(d)
    fsv(c→d)      =  fsv(c) ∪ fsv(d)
    fsv(∀X.c[X])  =  fsv(c[X])
    fsv(να.c[α])  =  fsv(c[α]) / {α}
    fsv(ν̅α.c[α])  =  fsv(c[α]) / {α}    
    fsv(G!)       =  ∅
    fsv(G?)       =  ∅
    fsv(α♯)       =  {α}
    fsv(α♭)       =  {α}

  Free variables of a coercion

    fv(c)  =  ftv(c) ∪ fsv(c)


## Types (Γ ⊢ A)

   Γ ⊢ ι

   Γ ⊢ ★

   ----- X ∈ Γ
   Γ ⊢ X

   ----- (α:=A) ∈ Γ
   Γ ⊢ α

   Γ ⊢ A    Γ ⊢ B
   --------------
   Γ ⊢ A → B

   Γ, X ⊢ B[X]
   -------------
   Γ ⊢ (∀X.B[X])


## Type contexts (Γ wf)

    ∅ wf

    Γ wf   Γ ⊢ A
    ------------ (α ∉ dom(Γ))
    Γ, α:=A wf

    Γ wf
    ------- (X ∉ dom(Γ))
    Γ, X wf

    Γ wf    Γ ⊢ A
    ------------- (x ∉ dom(Γ))
    Γ, x:A wf

    Lemma (Well-formed contexts are closed under prefix).
      If (Γ, Δ) wf then Γ wf.


## Terms (Γ ⊢ M : A)

    --------- (x:A) ∈ Γ
    Γ ⊢ x : A

    --------- tp(κ) = ι
    Γ ⊢ κ : ι

    Γ ⊢ M : ι    Γ ⊢ N : ι′
    ----------------------- tp(⊕) = ι → ι′ → ι″
    Γ ⊢ M ⊕ N : ι″

    Γ, x : A ⊢ N[x] : B
    -------------------
    Γ ⊢ λx.N[x] : A → B

    Γ ⊢ L : A → B    Γ ⊢ M : A
    --------------------------
    Γ ⊢ L M : B

    Γ, X ⊢ V[X] : B[X]
    ---------------------
    Γ ⊢ ΛX.V[X] : ∀X.B[X]

    Γ, α:=A ⊢ N[α] : B
    ------------------ α ∉ fv(B)
    Γ ⊢ να:=A.N[α] : B

    Γ ⊢ M : A    Γ ⊢ c : A =⇒_Σ B
    ----------------------------- Σ ⊆ Γ
    Γ ⊢ M ⟨ c ⟩ : B

    ---------------
    Γ ⊢ blame ℓ : A

    Γ ⊢ L : (∀X.A[X])    Γ, α:=C ⊢ c[α] : A[α] ==>_Σ B
    -------------------------------------------------- Σ ⊆ (Γ, α:=C)
    Γ ⊢ να:=C. L α ⟨ c[α] ⟩ : B

    Γ ⊢ V : ∀X.B[X]
    --------------------
    Γ, α:=A ⊢ V α : B[α]


    Lemma (Substitution).
      If Γ, x:A, Δ ⊢ N[x] : B
      and Γ, Δ ⊢ M : A
      then Γ, Δ ⊢ N[M] : B

    Lemma (Weakening).
      If Γ ⊢ M : A and Γ, Δ wf then Γ, Δ ⊢ M : A


## Canonical forms

  If Γ ⊢ V : A then V : A matches one of the following
    κ              : ι
    λx:A.N[x]      : A→B        where  Γ, x:A ⊢ N[x] : B
    W ⟨ c→d ⟩      : A→B        where  Γ ⊢ W : A′→B′ and c : A′ =⇒_Σ A and d : B =⇒_Σ B′
    ΛX.V[X]        : ∀X.B[X]    where  Γ, X ⊢ V[X] : B[X]
    W ⟨ ∀X.c[X] ⟩  : ∀X.B[X]    where  Γ ⊢ W : ∀X.A[X] and c[X] : A[X] =⇒_Σ B[X]
    W ⟨ να.c[α] ⟩  : ∀X.B[X]    where  Γ ⊢ W : A and c[α] : A =⇒_Σ B[α]
    W ⟨ α♯ ⟩       : α          where  Γ ⊢ W : A  and α:=A ∈ Γ
    W ⟨ G! ⟩       : ★          where  Γ ⊢ W : G


## Evaluation contexts (Γ ⊢ E : A ~~> B)

    E ::= □ | E ⊕ M | V ⊕ E | E M | V E | E α | E ⟨ c ⟩

    Γ ⊢ C
    ---------------
    Γ ⊢ □ : C ~~> C

    Γ ⊢ E : C ~~> A → B    Γ ⊢ M : A
    --------------------------------
    Γ ⊢ E M : C ~~> B

    Γ ⊢ V : A → B    Γ ⊢ E : C ~~> A
    --------------------------------
    Γ ⊢ V E : Γ ⊢ C ~~> B

    Γ ⊢ E : C ~~> ∀X.B[X]
    --------------------- α ∈ dom(Γ)
    Γ ⊢ E α : C ~~> B[α]

    Γ ⊢ E : C ~~> ι    Γ ⊢ M : ι′
    ----------------------------- tp(⊕) = ι → ι′ → ι″
    Γ ⊢ E ⊕ M : C ~~> ι″

    Γ ⊢ V : ι    Γ ⊢ E : C ~~> ι′
    ----------------------------- tp(⊕) = ι → ι′ → ι″
    Γ ⊢ V ⊕ E : C ~~> ι″

    Γ ⊢ E : C ~~> A    c : A =⇒_Σ B
    ------------------------------- Σ ⊆ Γ
    Γ ⊢ E ⟨ c ⟩ : C ~~> B

    Lemma (Sanity). If Γ ⊢ E : A ~~> B
      then Γ wf and Γ ⊢ A and Γ ⊢ B

    Lemma (Plug).
      If  Γ ⊢ E : A ~~> B
      and Γ ⊢ M : A
      then Γ ⊢ E[M] : B.


## Reduction

  Reduction (M ⊢→ N)

    κ ⊕ κ′             ⊢→  δ(⊕)(κ,κ′)
    (λx.N[x]) V        ⊢→  N[V]
    (ΛX.V[X]) α        ⊢→  V[α]
    V ⟨ id_A ⟩         ⊢→  V
    V ⟨ c;d ⟩          ⊢→  V ⟨ c ⟩ ⟨ d ⟩
    (V ⟨ c→d ⟩) W      ⊢→  V (W ⟨ c ⟩) ⟨ d ⟩
    (V ⟨ ∀X.c[X] ⟩) α  ⊢→  V α ⟨ c[α] ⟩
    (V ⟨ να.c[α] ⟩) α  ⊢→  V ⟨ c[α] ⟩
    V ⟨ ν̅α.c[α] ⟩      ⊢→  να:=★.(V α ⟨ c[α] ⟩)
    V ⟨ G! ⟩ ⟨ G? ⟩    ⊢→  V
    V ⟨ G! ⟩ ⟨ H?^ℓ ⟩  ⊢→  blame ℓ   if G ≠ H
    V ⟨ α♯ ⟩ ⟨ α♭ ⟩    ⊢→  V

  Reduction with store (M —→_Σ N)

    M ⊢→ N
    --------------
    E[M] —→_∅ E[N]

    -----------------------------------------------
    E[να:=A.V α ⟨ c[α] ⟩] —→_{α:=A} E[V α ⟨ c[α] ⟩]

    -------------------
    E[blame] —→_∅ blame


  Reflexive transitive closure (M —↠_Σ N)

    --------
    M —↠_∅ M

    M —→_Σ N    N —↠_Π P
    --------------------
    M —↠_{Σ,Π} P


## Thunking

  Let unit:Unit be the unit value of unit type.

  We convert arbitrary terms under Λ to values under Λ by a translation:
    ⟦ ΛX.N[X] ⟧  =  ΛX.λx:Unit.⟦ N[X] ⟧
    ⟦ L α ⟧      =  L α unit

  If we apply the translation uniformly to the reduction rules, something goes wrong. What?

        ⟦ (ΛX.N[X]) α ⟧
    ~>  (ΛX.λx:Unit.⟦ N[X] ⟧) α unit
    —↠  ⟦ N[α] ⟧
    
        ⟦ L ⟨ να.c[α] ⟩ α ⟧
    ~>  (⟦ L ⟧ ⟨ να.id_Unit→c[α] ⟩ α unit
    —↠  να:=★. ⟦ L ⟧ α ⟨ id_Unit→c[α] ⟩ unit
    —↠  να:=★. ⟦ L ⟧ α unit ⟨ c[α] ⟩
    <~  ⟦ να:=★. L α ⟨ c[α] ⟩ ⟧

        ⟦ (L ⟨ ν̅α.c[α] ⟩ ⟧
    ~>  να:=★. ⟦ L ⟧ α ⟨ id_Unit→c[α] ⟩
        Not in the image of the translation, because missing application to unit.
        This is why we can't apply the transformation uniformly to the reduction rules!
      
        In particular, the problematic example behaves as follows.
        ⟦ ((ΛX.blame) ⟨ ν̅α.α♯ ⟩ ⟨ να.α! ⟩ ⟧
    ~>  ((ΛX.λx:Unit.blame) ⟨ ν̅α.id_Unit→α♯ ⟩ ⟨ να.id_Unit→α! ⟩
    —↠  να:=★. (ΛX.λx:Unit.blame) α ⟨ id_Unit→α♯ ⟩ ⟨ να.id_Unit→α♯ ⟩
    —↠  να:=★. (λx:Unit.blame) ⟨ id_Unit→α♯ ⟩ ⟨ να.id_Unit→α♯ ⟩
        Not in the image of the translation.

        If all polymorphic terms are applied, we stay in the image of the translation.
        ⟦ ((ΛX.blame) ⟨ ν̅α.α♭ ⟩ ⟨ να.α? ⟩) α ⟧
    ~>  (ΛX.λx:Unit.blame) ⟨ ν̅α.id_Unit→α♭ ⟩ ⟨ να.id_Unit→α! ⟩ α unit
    —↠  (να₀:=★. (ΛX.λx:Unit.blame) α₀ ⟨ id_Unit→α₀♭ ⟩) ⟨ να.id_Unit→α? ⟩ α unit
    —↠  (να₀:=★. (λx:Unit.blame) ⟨ id_Unit→α₀♭ ⟩) ⟨ να.id_Unit→α? ⟩ α unit
    —↠  (να₀:=★. (λx:Unit.blame) ⟨ id_Unit→α₀♭ ⟩) ⟨ id_Unit→α? ⟩ unit
    —↠  (να:=★. (λx:Unit.blame) unit ⟨ α₀♭ ⟩ ⟨ α? ⟩
    —↠  να:=★. blame ⟨ α♭ ⟩ ⟨ α? ⟩
    —↠  blame


## Progress

  Progress 1.  If Σ ⊢ M : A then either:
  * M = V, where V is a value
  * M = E[P] where either P = blame or P = να:=A.N or P ⊢→ N

  Proof by induction on Σ ⊢ M : A.

    ---------
    Σ ⊢ x : A

      cannot occur

    Σ ⊢ A    Σ, x : A ⊢ N[x] : B
    ----------------------------
    Σ ⊢ (λx.N[x]) : A → B

      (λx.N[x]) is a value

    Σ ⊢ L : A → B    Σ ⊢ M : A
    --------------------------
    Σ ⊢ L M : B

      By progress on L either:
      * L = E[P] in which case L M = (E M)[P]
      * L is a value V, in which case by progress on M either:
        - M = E[P] in which case L M = (V E)[P]
        - M is a value W, in which case
          by canonical forms we have either
          + V = λx.N[x], in which case
            (λx.N[x]) W ⊢→ N[W]
          + V = V′ ⟨ c→d ⟩ in which case
            (V′ ⟨ c→d ⟩) W ⊢→ V′ (W ⟨ c ⟩) ⟨ d ⟩

    Σ, X ⊢ V[X] : B[X]
    ---------------------
    Σ ⊢ ΛX.V[X] : ∀X.B[X]

      (ΛX.V[X]) is a value

    Σ ⊢ L : ∀X.B[X]
    --------------- (α:=A ∈ Σ, α ∉ fv(L))
    Σ ⊢ L α : B[α]

      By progress on L either:
      * L = E[P] in which case L α = (E α)[P]
      * L is a value V, in which case
        by canonical forms we have either
        - V = ΛX.N[X] and
          (ΛX.N[X]) α ⊢→ N[α]
        - V = W ⟨ ∀X.c[X] ⟩ and
          (W ⟨ ∀X.c[X] ⟩) α ⊢→ W α ⟨ c[α] ⟩
        - V = W ⟨ να.c[α] ⟩ and
          (W ⟨ να.c[α] ⟩) α ⊢→ W ⟨ c[α] ⟩

    Σ, α:=A ⊢ N[α] : B
    ------------------
    Σ ⊢ να:=A.N[α] : B

      να:=A.N[α] = □(να:=A.N[α])

    Σ wf
    --------- tp(κ) = ι
    Σ ⊢ κ : ι

      κ is a value

    Σ ⊢ M : ι    Σ ⊢ N : ι′
    ----------------------- tp(⊕) = ι → ι′ → ι″
    Σ ⊢ M ⊕ N : ι″

      By progress on M either:
      * M = E[P] in which case M ⊕ N = (E ⊕ N)[P]
      * M is a value V, in which case by progress on N either:
        - N = E[P] in which case M ⊕ N = (V ⊕ E)[P]
        - N is a value W, in which case
          by canonical forms we have V = κ and W = κ′ and
          κ ⊕ κ′ ⊢→ δ(⊕)(κ,κ′)

    Σ ⊢ M : A    c : A =⇒_Π B
    ------------------------- Π ⊆ Σ
    Σ ⊢ M ⟨ c ⟩ : B

      By progress on M either:
      ● M = E[P] in which case M ⟨ c ⟩ = (E ⟨ c ⟩)[P]
      ● M is a value V, in which case c is either:
        * id_a, in which case
          V ⟨ id_a ⟩ ⊢→ V
        * (c;d), in which case
          V ⟨ c;d ⟩ ⊢→ V ⟨ c ⟩ ⟨ d ⟩
        * (c→d), in which case
          (V ⟨ c→d ⟩) is a value
        * (∀X.c[X]), in which case
          (V ⟨ ∀X.c[X] ⟩) is a value
        * να.c[α], in which case
          (V ⟨ να.c[α] ⟩) is a value
        * ν̅α.c[α], in which case
          V ⟨ ν̅α.c[α] ⟩ ⊢→ να:=★.(V α ⟨ c[α] ⟩)
        * G!, in which case
          (V ⟨ G! ⟩) is a value
        * H?, in which case
          by canonical forms V has the form (W ⟨ G! ⟩) and either
          ● G = H, in which case
            W ⟨ G! ⟩ ⟨ G? ⟩ ⊢→ W
          ● G ≠ H, in which case
            W ⟨ G! ⟩ ⟨ H? ⟩ ⊢→ blame
        * α♯, in which case
          (V ⟨ α♯ ⟩) is a value
        * α♭, in which case
          by canonical forms V = (W ⟨ α♯ ⟩) and
          W ⟨ α♯ ⟩ ⟨ α♭ ⟩ ⊢→ W
          

    Γ ⊢ A
    -------------
    Γ ⊢ blame : A

      blame = □[blame]

    QED


  Progress 2.  If Σ ⊢ M : A then either:
  * M = V, where V is a value.
  * M —→_Π N, for some Π and N.
  * M —→_Π blame.

  By Progress 1, either
  * M = V, where V is a value.
  * M = E[P], where either:
    - P ⊢→ N, in which case
      Σ ⊢ E[P] —→ Σ ⊢ E[N]
    - P = (να:=A.N[α]), in which case
      Σ ⊢ E[να:=A.N[α]] —→ Σ, α:=A ⊢ N[α]
    - P = blame, in which case
      Σ ⊢ E[blame] —→ blame


## Preservation

  Preservation 1. If Σ ⊢ M : A and M ⊢→ N then Σ ⊢ N : A.

  Proof. By case analysis of the reduction rules.

    κ ⊕ κ′  ⊢→  δ(⊕)(κ,κ′)

        Σ ⊢ κ : ι    Σ ⊢ κ′ : ι′
        ------------------------
        Σ ⊢ κ ⊕ κ′ : ι″
      ⊢→
        -------------------
        Σ ⊢ δ(⊕)(κ,κ′) : ι″

    (λx.N[x]) V  ⊢→  N[V]

        Σ, x:A ⊢ N[x] : B
        -------------------
        Σ ⊢ λx.N[x] : A → B    Σ ⊢ V : A
        --------------------------------
        Σ ⊢ (λx.N[x]) V : B
      ⊢→
        Σ, x : A ⊢ N[x] : B    Σ ⊢ V : A
        -------------------------------- (subs't lemma)
        Σ ⊢ N[V] : B

    (ΛX.V[X]) α  ⊢→  V[α]

        Σ, X ⊢ N[X] : B[X]
        ---------------------
        Σ ⊢ ΛX.N[X] : ∀X.B[X]
        ---------------------- α:=A ∈ Σ
        Σ ⊢ (ΛX.N[X]) α : B[α]
      ⊢→
        Σ, X ⊢ N[X] : B[X]
        ------------------ (subs't lemma)
        Σ ⊢ N[α] : B[α]

    V ⟨ id_A ⟩  ⊢→  V

        Σ ⊢ V : A    Σ ⊢ id_A : A ⇒ A
        -----------------------------
        Σ ⊢ V ⟨ id_A ⟩ : A
      ⊢→
        Σ ⊢ V : A

    V ⟨ c;d ⟩  ⊢→  V ⟨ c ⟩ ⟨ d ⟩

                     Σ ⊢ c : A =⇒_Σ B    Σ ⊢ d : B =⇒_Π C
                     ------------------------------------
        Σ ⊢ V : A    Σ ⊢ (c;d) : A =⇒_{Σ,Π} C
        -------------------------------------
        Σ ⊢ V ⟨ c;d ⟩ : C
      ⊢→
        Σ ⊢ V : A    Σ ⊢ c : A =⇒_Σ B
        -----------------------------
        Σ ⊢ V ⟨ c ⟩ : B                  Σ ⊢ d : B =⇒_Π C
        -------------------------------------------------
        Σ ⊢ V ⟨ c ⟩ ⟨ d ⟩ : C

    (V ⟨ c→d ⟩) W  ⊢→  V (W ⟨ c ⟩) ⟨ d ⟩

                       Σ ⊢ c : A′ =⇒_Σ A    Σ ⊢ d : B =⇒_Σ B′
                       --------------------------------------
        Σ ⊢ V : A→B    Σ ⊢ c→d : A→B =⇒_Σ A′→B′
        ---------------------------------------
        Σ ⊢ V ⟨ c→d ⟩ : A′ → B′                   Σ ⊢ W : A′
        -----------------------------------------------------
        Σ ⊢ (V ⟨ c→d ⟩) W : B′
      ⊢→
                       Σ ⊢ W : A′    Σ ⊢ c : A′ =⇒_Σ A
                       -------------------------------
        Σ ⊢ V : A→B    Σ ⊢ W ⟨ c ⟩ : A
        ------------------------------
        Σ ⊢ V (W ⟨ c ⟩) : B               Σ ⊢ d : B =⇒_Σ B′
        ---------------------------------------------------
        Σ ⊢ V (W ⟨ c ⟩) ⟨ d ⟩ : B′

    (V ⟨ ∀X.c[X] ⟩) α  ⊢→  V α ⟨ c[α] ⟩

                           Σ, X ⊢ c[X] : A[X] =⇒_Σ B[X]
                           ----------------------------------
        Σ ⊢ V : ∀X.A[X]    Σ ⊢ ∀X.c[X] : ∀X.A[X] =⇒_Σ ∀X.B[X]
        -----------------------------------------------------
        Σ ⊢ V ⟨ ∀X.c[X] ⟩ : ∀X.B[X]
        ---------------------------- α:=C ∈ Σ
        Σ ⊢ (V ⟨ ∀X.c[X] ⟩) α : B[α]
      ⊢→
        Σ ⊢ V : ∀X.A[X]
        --------------- α:=C ∈ Σ
        Σ ⊢ V α : A[α]              Σ ⊢ c[α] : A[α] =⇒_Σ B[α]
        -----------------------------------------------------
        Σ ⊢ V α ⟨ c[α] ⟩ : B[α]

    V ⟨ ν̅α.c[α] ⟩  ⊢→  να:=★. V α ⟨ c[α] ⟩

                           c[α] : A[α] =⇒_{Π,α:=★} B
                           -------------------------
        Σ ⊢ V : ∀X.A[X]    ν̅α.c[α] : ∀X.A[X] =⇒_Π B
        -------------------------------------------
        Σ ⊢ V ⟨ ν̅α.c[α] ⟩ : B
      ⊢→
        Σ, α:=★ ⊢ V : ∀X.A[X]
        ---------------------
        Σ, α:=★ ⊢ V α : A[α]     c[α] : A[α] =⇒_{Π,α:=★} B
        --------------------------------------------------
        Σ, α:=★ ⊢ (V α ⟨ c[α] ⟩) : B
         ---------------------------------
        Σ ⊢ (να:=★. V α ⟨ c[α] ⟩) : B

    (V ⟨ να.c[α] ⟩) α  ⊢→  V ⟨ c[α] ⟩

                     c[α] : A[α] =⇒_Π B
                     ------------------------
        Σ ⊢ V : B    να.c[α] : ∀X.A[X] =⇒_Π B
        -------------------------------------
        Σ ⊢ V ⟨ να.c[α] ⟩ : ∀X.A[X]
        ---------------------------- α:=C ∈ Σ
        Σ ⊢ (V ⟨ να.c[α] ⟩) α : A[α]
      ⊢→
        Σ ⊢ V : B    c[α] : A[α] =⇒_Π B
        ------------------------------- α:=C ∈ Σ
        Σ ⊢ V ⟨ c[α] ⟩ : A[α]

    V ⟨ G! ⟩ ⟨ G? ⟩  ⊢→  V
                 
        Σ ⊢ V : G    G! : G =⇒ ★
        ------------------------
        Σ ⊢ V ⟨ G! ⟩ : ★            G? : ★ =⇒ G
        ---------------------------------------
        Σ ⊢ V ⟨ G! ⟩ ⟨ G? ⟩ : G
      ⊢→
        Σ ⊢ V : G

    V ⟨ G! ⟩ ⟨ H? ⟩  ⊢→  blame,  if G ≠ H

        Σ ⊢ V : G    G! : G =⇒ ★
        ------------------------
        Σ ⊢ V ⟨ G! ⟩ : ★                H? : ★ =⇒ H
        -------------------------------------------
        Σ ⊢ V ⟨ G! ⟩ ⟨ H? ⟩ : H
      ⊢→
        Σ ⊢ blame : H

    V ⟨ α♯ ⟩ ⟨ α♭ ⟩  ⊢→  V

        Σ ⊢ V : A    α♯ : A =⇒_Π α
        -------------------------- α:=A ∈ Π
        Σ ⊢ V ⟨ α♯ ⟩ : α                       α♭ : α =⇒_Π A
        ---------------------------------------------------- α:=A ∈ Π
        Σ ⊢ V ⟨ α♯ ⟩ ⟨ α♭ ⟩ : A
      ⊢→
        Σ ⊢ V : A


  Preservation 2. If Σ ⊢ M : A and M —→_Π N then Σ, Π ⊢ N : A.

  Proof. By case analysis of the reduction rules.

    M ⊢→ N
    ----------------------
    Σ ⊢ E[M] —→_∅ Σ ⊢ E[N]

        Σ ⊢ M : A    Σ ⊢ E : A ~~> B
        ----------------------------
        Σ ⊢ E[M] : B
      —→
        Σ ⊢ N : A    Σ ⊢ E : A ~~> B
        ----------------------------
        Σ ⊢ E[N] : B

    Σ ⊢ E[να:=A.N[α]]  —→_{α:=A}  Σ, α:=A ⊢ E[N[α]]

        Σ, α:=A ⊢ N[α] : B
        ------------------
        Σ ⊢ να:=A.N[α] : B    Σ ⊢ E : B ~~> C
        -------------------------------------
        Σ ⊢ E[να:=A.N[α]] : C
      —→
        Σ, α:=A ⊢ N[α] : B    Σ, α:=A ⊢ E : B ~~> C
        -------------------------------------------
        Σ, α:=A ⊢ E[N[α]] : C

        [Needs weakening lemma for contexts]

    Σ ⊢ E[blame]  —→_∅  blame

        Σ ⊢ blame : A    Σ ⊢ E : A ~~> B
        --------------------------------
        Σ ⊢ E[blame] : B
      —→
        blame : B


## Translation: ν∀ into ν∀

  Types (⟦A⟧=B)

  ⟦ι⟧           =  ι
  ⟦★⟧           =  ★
  ⟦α⟧           =  α
  ⟦X⟧           =  X
  ⟦A→B⟧         =  ⟦A⟧ → ⟦B⟧
  ⟦∀X.A[X]⟧     =  ∀X.(Unit → ⟦A[X]⟧)

  Coercions (⟦c⟧=N)

  ⟦id_A⟧        =  λf.f
  ⟦c→d⟧         =  λf.λx.⟦d⟧(f(⟦c⟧x))
  ⟦∀X.c[X]⟧     =  λf.ΛX.λ_:Unit.(να:=X. ⟦c[α]⟧ (f α unit))
  ⟦να.c[α]⟧     =  λf.ΛX.λ_:Unit.(να:=X. ⟦c[α]⟧ f)
  ⟦ν̅α.c[α]⟧     =  λf.(να:=★. ⟦c[α]⟧ (f α unit))
  ⟦c;d⟧         =  λf.⟦d⟧(⟦c⟧f)
  ⟦G!⟧          =  λf.f ⟨ G! ⟩
  ⟦G?⟧          =  λf.f ⟨ G? ⟩
  ⟦α♯⟧          =  λf.f ⟨ α♯ ⟩
  ⟦α♭⟧          =  λf.f ⟨ α♭ ⟩

  Terms (⟦M⟧=N)

  ⟦x⟧           =  x
  ⟦κ⟧           =  κ
  ⟦M ⊕ N⟧       =  ⟦M⟧ ⊕ ⟦N⟧
  ⟦λx:A.N[x]⟧   =  λx:⟦A⟧.⟦N[x]⟧
  ⟦L M⟧         =  ⟦L⟧ ⟦M⟧
  ⟦ΛX.N[X]⟧     =  ΛX.λ_:Unit.⟦N[X]⟧
  ⟦L A⟧         =  ⟦L⟧ ⟦A⟧ unit
  ⟦να:=A.N[α]⟧  =  να:=⟦A⟧.⟦N[α]⟧
  ⟦M ⟨ c ⟩⟧     =  ⟦c⟧ ⟦M⟧


Proposition. The translation is a simulation

Proof. The main cases are as follows.

  (V ⟨ c→d ⟩) W  ⊢→  V (W ⟨ c ⟩) ⟨ d ⟩
    (λf.λx.⟦d⟧(f(⟦c⟧x))) ⟦V⟧ ⟦W⟧  —↠  ⟦d⟧ (⟦V⟧ (⟦c⟧ ⟦W⟧))

  V ⟨ id_A ⟩ ⊢→  V
    (λf.f)⟦V⟧  —→  ⟦V⟧

  V ⟨ ∀X.c[X] ⟩ α  ⊢→  V α ⟨ c[α] ⟩
    (λf.ΛX.λ_:Unit.(να:=X. ⟦c[α]⟧ (f α unit))) ⟦V⟧ α unit  —↠_{α:=α}  ⟦ c[α] ⟧ (⟦V⟧ α unit)

  V ⟨ να.c[α] ⟩ α  ⊢→  V ⟨ c[α] ⟩
    (λf.ΛX.λ_:Unit.να:=X. ⟦c[α]⟧ f) ⟦V⟧ α unit  —↠_{α:=α}  ⟦c[α]⟧ ⟦V⟧

  V ⟨ ν̅α.c[α] ⟩  ⊢→  να:=★.((V α) ⟨ c[α] ⟩)
    (λf.να:=★. ⟦c[α]⟧ (f α unit)) ⟦V⟧  —↠  να:=★. ⟦c[α]⟧ (⟦V⟧ α unit)

  V ⟨ c;d ⟩  ⊢→  V ⟨ c ⟩ ⟨ d ⟩
    (λf.⟦d⟧(⟦c⟧f)) ⟦V⟧  —→  ⟦d⟧ (⟦c⟧ ⟦V⟧)



## Translation: ν∀ into Ahmed et al 2017

  ⟦id_A⟧_Σ     =  λf.f
  ⟦c→d⟧_Σ      =  λf.λx.⟦d⟧_Σ(f(⟦c⟧_Σx))
  ⟦∀X.c[X]⟧_Σ  =  λf.ΛX.λ().⟦c[X]⟧_Σ(f X ())
  ⟦να.c[α]⟧_Σ  =  λf.ΛX.λ().⟦c[α]⟧_{Σ,α:=X}(f)
  ⟦ν̅α.c[α]⟧_Σ  =  λf.⟦c[α]⟧_{Σ,α:=★}(f ★ ())
  ⟦c;d⟧_Σ      =  λf.⟦d⟧_Σ(⟦c⟧_Σf)
  ⟦G!⟧_Σ       =  λf.(f : G =⇒ ★)
  ⟦G?⟧_Σ       =  λf.(f : ★ =⇒ G)
  ⟦α♯⟧_Σ       =  λf.(f : α =⇒^α A)   if (α:=A) ∈ Σ
  ⟦α♭⟧_Σ       =  λf.(f : A =⇒^α̅ α)   if (α:=A) ∈ Σ

## Translation:  ν∀ into New et al 2019.

  ⟦id_A⟧     =  λf.f
  ⟦c→d⟧      =  λf.λx.⟦d⟧(f(⟦c⟧x))
  ⟦∀X.c[X]⟧  =  λf.ΛX.λ().(let x = f {α≅X} in ⟦c[α]⟧ (x ()) ())
  ⟦να.c[α]⟧  =  λf.ΛX.λ().(⟦c[X]⟧ (x ()))
  ⟦ν̅α.c[α]⟧  =  λf.(let x = f {α≅★} in ⟦c[α]⟧ (x ()))
  ⟦c;d⟧      =  λf.⟦d⟧(⟦c⟧f)
  ⟦G!⟧       =  λf.inj_G(f)
  ⟦G?⟧       =  λf.⟨tag_G(G)⟩↓(f)
  ⟦α♯⟧       =  λf.seal_α(f)
  ⟦α♭⟧       =  λf.unseal_α(f)


  
  
## Duality

We ignore labels on ? for duality.

Note that in να.c[α] all occurrences of α must be of the form α! or α?.
and in ν̅α.c[α] all occurrences of α must be of the form α♯ or α♭.  We
occasionally indicate this by writing να.c[α!] or ν̅α.c[α♯].  Further,
if c[α!,α?] : A =⇒_Σ B is in scope, we write c̅[α♯,α♭] : A =⇒_{Σ,α:=★} B
to indicate the former with all occurrences of α! replaced by α♭ and
all occurrences of α? replaced by α♯ and taking the dual of all other
constructs. Similarly to go the other way.

Dual. Given c : A =⇒_Σ B it's dual is c̅ : B =⇒_Σ A.

    \dual{id_A}         =  id_A
    \dual{c;d}          =  (d̅);(c̅)
    \dual{c→d}          =  (c̅)→(d̅)
    \dual{∀X.c[X]}      =  ∀X.(c̅[X])
    \dual{να.c[α!,α?]}  =  ν̅α.(c̅[α♭,α♯])    \dual{ν̅α.c[α♭,α♯]}  =  να.(c̅[α!,α?])
    \dual{G!}           =  G?               \dual{G?}           =  G!
    \dual{α♯}           =  α♭               \dual{α♭}           =  α♯


Duality is an involution. For any c : A =⇒_Σ B, we have c̅̅ = c.
    

## Underlying types

  Every type other than ★ has a unique underlying type.

  |α|        =  α
  |X|        =  X
  |ι|        =  ι
  |A→B|      =  ★→★
  |∀X.A[X]|  =  ∀X.★


## Narrowing and Widening

  cross narrowing   g,h  ::=  id_α | id_X | id_ι | s̅→t | ∀X.s[X]
  narrowing         s,t  ::=  g | id_★ | να.s[α] | G?;g | s;α♯
  cross widening    g̅,h̅  ::=  id_α | id_X | id_ι | s→t̅ | ∀X.s̅[X]
  widening          s̅,t̅  ::=  g̅ | id_★ | ν̅α.s̅[α] | g̅;G! | α♭;s̅


  We define narrowing and widening as follows.

  Assume s, s̅ : A =⇒_Σ B.
  Then we write s : A ⊒_Σ B and s̅ : A ⊑_Σ B
  if they satisfy the following grammar.

     g,h  ::=  id_α | id_X | id_ι | s̅→t | ∀X.s[X]
     s,t  ::=  g | id_★ | να.s[α] | G?;g | s;α♯
     g̅,h̅  ::=  id_α | id_X | id_ι | s→t̅ | ∀X.s̅[X]
     s̅,t̅  ::=  g̅ | id_★ | ν̅α.s̅[α] | g̅;G! | α♭;s̅

  Cross coercions.
    If g : A =⇒_Σ B or g̅ : A =⇒_Σ B then |A| = |B|.

  Narrowing and Widening are dual.
    If s : A ⊒_Σ B then s̅ : B ⊑_Σ A and
    if s̅ : A ⊑_Σ B then s : B ⊒_Σ A.

  Widening and narrowing are determined by types and store.
    If s : A ⊒_Σ B and t : A ⊒_Σ B then s = t.
    If v : A ⊑_Σ B and w : A ⊑_Σ B then v = w.


## Composition for narrowing.

  s : A ⊒_Σ B    t : B ⊒_Σ C
  --------------------------
  (s ⨾ t) : A ⊒_Σ C

  s ⨾ t = r  (by cases on t)

      s ⨾ id_★       =  s
      id_★ ⨾ (G?;g)  =  (G?;g)
      s ⨾ (t;α♯)     =  (s ⨾ t);α♯
      s ⨾ (να.t[α])  =  να.(s ⨾ t[α])

  s ⨾ g = r  (by cases on s)

      id_★ ⨾ id_★            =  id_★
      (G?;g) ⨾ h             =  G?;(g ⨾ h)
      (s;α♯) ⨾ id_α          =  s;α♯
      (να.s[α]) ⨾ (∀X.t[X])  =  να.(s[α] ⨾ t[α])

  g ⨾ h = f  (by cases on g or h)

      id_ι ⨾ id_ι            =  id_ι
      id_α ⨾ id_α            =  id_α
      id_X ⨾ id_X            =  id_X
      (v→s) ⨾ (w→t)          =  (w ⨾ v)→(s ⨾ t)
      (∀X.s[X]) ⨾ (∀X.t[X])  =  ∀X.(s[X] ⨾ t[X])

  (Composition for widening is the dual.)

  Conjecture. The following holds, where ≅ is observational equivalence.

    M ⟨ s ⨾ t ⟩  ≅  M ⟨ s ⟩ ⟨ t ⟩
    M ⟨ s̅ ⨾ t̅ ⟩  ≅  M ⟨ s̅ ⟩ ⟨ t̅ ⟩


## Factoring

    We can factor narrowing into casts and conversions.

    A cast is an narrowing with tags but no free seals.
    A conversion is a narrrowing with seals but no tags and no ν.

    Casts            p, q   fsv(p) = ∅
    Abstraction      φ, ψ   ::=  id_a | φ→ψ | ∀X.ϕ[X] | φ;α♯

    Claim. For every s there exist p and φ such that s = p ⨾ φ

    Abstraction Factoring Lemma.
      Let φ : A ⊑_{Σ,α:=★} B be an abstraction.
      Then there exists φ₁ and φ₂ such that:
        (i)   fsv(φ₁) ⊆ dom(Σ)
        (ii)  fsv(ϕ₂) ⊆ {α}
        (iii) φ = φ₁ ⨾ φ₂.

    Proof.

      Cases for id_a, φ→ψ, ∀X.φ[X] as for proper factoring lemma, below.

      In the case for α♯, with α:=★,
      take φ₁ = id_★ and φ₂ = α♯.

      In the case for φ;β♯ with β ≠ α and β:=A.
      By induction, φ = φ₁′⨾φ₂′ with fsv(φ₂′) = {a}.
      take φ₁ = (β♯;φ₁′) and φ₂ = φ₂′.

    Imprecision Factoring Lemma.
      Every imprecision factors into a cast and and a conversion:
      For every s there exist φ and p such that s = φ ⨾ p.

    Proof.
        id_a
      =⟨def'n ⨾⟩
        id_a⨾id_a

        s;G!
      =⟨induction⟩
        (φ⨾s);G!
      =⟨def'n ⨾⟩
        φ⨾(s;G!)

        α♯;s
      =⟨induction⟩
        α♯;(φ⨾p)
      =⟨def'n ⨾⟩
        (α♯;φ)⨾p

        s→t
      =⟨induction⟩
        (φ⨾p)→(ψ⨾q)
      =⟨def'n ⨾⟩
        (φ→ψ)⨾(p→q)

        ∀X.s[X]
      =⟨induction⟩
        ∀X.(φ[X]⨾p[X])
      =⟨def'n ⨾⟩
        (∀X.φ[X])⨾(∀X.p[X])
        
        να.s[α]
      =⟨induction⟩
        να.(φ[α]⨾p[α])
      =⟨conversion factoring, where α ∉ fsv(φ₁[α]), {α} = fsv(φ₂)⟩
        να.(φ₁[α]⨾φ₂[α]⨾p[α])
      =⟨def'n ⨾⟩
        (∀X.φ₁[X])⨾(να.φ₂[α]⨾p[α])


## Discussion: a corner case

Consider the reduction:

    (V ⟨ \dual{να.s[α♯]} ⟩) α ⊢→ V ⟨ s̅[α!] ⟩

Observe that (V ⟨ \dual{να.s[α♯]} ⟩) is a value. The redex,
V ⟨ s̅[α!] ⟩, is very nearly a value, with one exceptional
corner case.

Consider the possibilities for s̅[α!]. It will be one of

   (s₀→t₀)
   (∀X.s₀[id_X])
   (νa.s₀[α♯])
   α!

It cannot be id_a or α♯, because s̅[α!] must contain α!.
For all of these, V ⟨ s̅[α!] ⟩ is itself a value, with the sole
exception being the case α!. This can arise only from:

    (V ⟨ \dual{να.α♯} ⟩) α ⊢→ V ⟨ α? ⟩

Here V : ★ and (να.α♯) : (∀X.X) ⊑ ★. The right-hand side
V ⟨ α? ⟩ must (by parametricity) reduce to blame. (The other
possibility, that it loops forever, cannot occur becase V is
a value.)

In what follows, it will be convenient to rule out this corner
case, to ensure that the right-hand side of

    (V ⟨ \dual{να.s[α♯]} ⟩) α ⊢→ V ⟨ s̅[α!] ⟩

is always a value. Therefore, we modify the formation rule for
ν to rule out this corner case.

    Γ, α:=★ | Φ, α ⊢ s[α] : A[α] ⊑ B
    -------------------------------- α ∈ fv(A[α]), α ∉ fv(B), A[α] ≠ α.
    Γ | Φ ⊢ (να.s[α]) : ∀X.A[X] ⊑ B


## Environment imprecision (γ : Γ ⊒ Γ′, σ : Σ ⊒ Σ′)

    γ    ::=  ∅ | γ, α:=p | γ, α:=A | γ, α:=☆ | γ, X | γ, x:p
    σ,π  ::=  ∅ | σ, α:=p | σ, α:=A | σ, α:=☆

    ---------
    ∅ : ∅ ⊒ ∅

    γ : Γ ⊒ Γ′    Γ ⊢ A
    ---------------------- α ∉ dom(γ)
    γ, α:=A : Γ ⊒ Γ′, α:=A

    γ : Γ ⊒ Γ′    Γ ⊢ p : A ⊒ A′    Γ′ ⊢ A′
    --------------------------------------- α ∉ dom(γ)
    γ, α:=p : Γ, α:=A ⊒ Γ′, α:=A′

    γ : Γ ⊒ Γ′
    ---------------------- α ∉ dom(γ)
    γ, α:=☆ : Γ, α:=★ ⊒ Γ′

    γ : Γ ⊒ Γ′
    ------------------- X ∉ dom(γ)
    γ, X : Γ, X ⊒ Γ′, X

    γ : Γ ⊒ Γ′    Γ ⊢ p : A ⊒ A′    Γ′ ⊢ A′
    --------------------------------------- x ∉ dom(γ)
    γ, x:p : Γ, x:A ⊒ Γ′, x:A′

    Lemma (Sanity). If γ : Γ ⊒ Γ′ then Γ wf and Γ′ wf.

    Lemma. If σ : Γ ⊒ Γ′ then Γ = Σ and Γ′ = Σ′ for some Σ, Σ′.

    Lemma. If γ : Σ ⊒ Γ′ then γ = σ and Γ′ = Σ′ for some σ, Σ′.

    Lemma. If γ : Γ ⊒ Σ′ then γ = σ and Γ = Σ for some σ, Σ.


## Relating imprecisions: (γ ⊢ p ≈ q)

    If γ | σ ⊢ p ≈ q holds iff
      γ ⊇ σ
      γ : Γ ⊒ Γ′
      σ : Σ ⊒ Σ′
      Γ | Σ ⊢ p : A ⊒ B
      Γ′ | Σ′ ⊢ q : A ⊒ B
      
## Relating imprecisions [alternate definition] (γ ⊢ p ≈ q)

    X ∈ γ
    ---------------
    γ ⊢ id_X ≈ id_X

    α:=p ∈ γ
    ---------------
    γ ⊢ id_α ≈ id_α

    γ ⊢ g ≈ g′
    --------------------
    γ ⊢ (g;G!) ≈ (g′;G!)

    ----------- (α:=id_★ ∈ γ)
    γ ⊢ α! ≈ α♯

    ----------- (α:=id_★ ∈ γ)
    γ ⊢ α♯ ≈ α!

    γ ⊢ r ≈ p ⨾ q
    ------------------- (α:=p ∈ γ)
    γ ⊢ α♯ ; r ≈ α♯ ; q

    γ ⊢  s ≈ s′    γ ⊢ t ≈ t′
    ------------------------
    γ ⊢ (s→t) ≈ (s′→t′)

    γ, X ⊢ p[id_X] ≈ p′[id_X]
    --------------------------------
    γ ⊢ (∀X.p[id_X]) ≈ (∀X.p′[id_X])

    γ, α:=id_★ ⊢ p[α♯] ≈ p′[α♯]
    ----------------------------
    γ ⊢ (να.p[α♯]) ≈ (να.p′[α♯])

  (More general rules. But perhaps I don't need these.)

    γ ⊢ r ≈ p ⨾ q
    --------------- (α:=p ∈ γ), γ : Γ ⊑ Γ′, Γ | ∅ ⊢ r : A ⊑ ★
    γ ⊢ α! ≈ α♯ ; q

    γ ⊢ r ≈ p ⨾ q
    --------------- (α:=p ∈ γ), γ : Γ ⊑ Γ′, Γ | ∅ ⊢ r : A ⊑ ★
    γ ⊢ α♯ ; q ≈ α!

  (I believe the more general rules are equivalent to the
  "same endpoints" definitions.)
  

## Term narrowing (γ ⊢ M ⊒ M′ : r)

    Assume
      γ : Γ ⊒ Γ′
      Γ ⊢ M : A
      Γ′ ⊢ M′ : A′
      Γ | ∅ ⊢ p, q : A ⊒ A′
      Γ | Φ ⊢ r, s, t : A ⊒ A′

    N.B. Use of ∅ for p, q but arbitary Φ for r, s, t.


    (extend)
      γ, α:=A ⊢ M ⊒ M′[α] : p[α]
      -------------------------- α ∉ fv(M) and q : B ⊒ A
      γ, α:=q ⊢ M ⊒ M′[α] : p[α]

    (split)
      γ, α:=q ⊢ M[α] ⊒ M′[α] : p[α]
      ------------------------------------- α ∉ fv(M[αᵢ]) and q : ★ ⊒ A
      γ, α:=A, αᵢ:=☆ ⊢ M[αᵢ] ⊒ M′[α] : p[α]

    (⊒blame)
      -----------------
      γ ⊢ M ⊒ blame : p
      
    (x⊒x)
      ------------- x:p ∈ γ
      γ ⊢ x ⊒ x : p

    (λ⊒λ)
      γ, x:=p ⊢ N[x] ⊒ N′[x] : q
      ---------------------------------
      γ ⊢ λx:A.N[x] ⊒ λx:A′.N′[x] : p̅→q

    (·⊒·)
      γ ⊢ L ⊒ L′ : p̅→q    γ ⊢ M ⊒ M′ : p
      ----------------------------------
      γ ⊢ L M ⊒ L′ M′ : q

    (Λ⊒Λ)
      γ, X ⊢ V[X] ⊒ V′[X] : p[X]
      --------------------------------
      γ ⊢ ΛX.V[X] ⊒ ΛX.V′[X] : ∀X.p[X]

    (⊒Λ)
      γ, α:=★ ⊢ N ⊒ V′[α] : p[α]
      --------------------------
      γ ⊢ N ⊒ ΛX.V′[X] : να.p[α]

    (⊒⟨ν⟩)
      γ, α:=★ ⊢ N ⊒ V ⟨ s[α] ⟩ : p[α]
      --------------------------------
      γ ⊢ N ⊒ V′ ⟨ να.s[α] ⟩ : να.p[α]

    (α⊒α)
      γ ⊢ L ⊒ L′ : ∀X.p[X]
      ---------------------------
      γ, α:=q ⊢ L α ⊒ L′ α : p[α]

    (⊒α)
      γ ⊢ L ⊒ L′ : να.p[α]
      -------------------------
      γ, α:=A ⊢ L ⊒ L′ α : p[α]

    (ν⊒ν)
      γ, α:=q ⊢ N[α] ⊒ N′[α] : p    q : A ⊒ A′
      ---------------------------------------- α ∉ fv(p)
      γ ⊢ να:=A.N[α] ⊒ να:=A′.N′[α] : p

    (⊒ν)
      γ, α:=A ⊢ N ⊒ N′[α] : p
      ----------------------- α ∉ fv(p)
      γ ⊢ N ⊒ να:=A.N′[α] : p

    (κ⊒κ)
      ---------------- tp(κ) = ι
      γ ⊢ κ ⊒ κ : id_ι

    (⊕⊒⊕)
      γ ⊢ M ⊒ M′ : id_ι    γ ⊢ N ⊒ N′ : id_ι′
      --------------------------------------- tp(⊕) = ι → ι′ → ι″
      γ ⊢ M ⊕ N ⊒ M′ ⊕ N′ : id_ι″

    (-⊒)
      γ ⊢ M ⊒ M′ : r
      -------------------- (s ⨾ q ≈ r)
      γ ⊢ M ⟨ s ⟩ ⊒ M′ : q

    (+⊒)
      γ ⊢ M ⊒ M′ : q
      -------------------- (s ⨾ q ≈ r)
      γ ⊢ M ⟨ s̅ ⟩ ⊒ M′ : r

    (⊒-)
      γ ⊢ M ⊒ M′ : p
      -------------------- (r ≈ p ⨾ t)
      γ ⊢ M ⊒ M′ ⟨ t ⟩ : r

    (⊒+)
      γ ⊢ M ⊒ M′ : r
      -------------------- (r ≈ p ⨾ t)
      γ ⊢ M ⊒ M′ ⟨ t̅ ⟩ : p


## Discussion

On might wonder whether we need the following rules

    (α⊒)
      γ ⊢ L ⊒ L′ : να.p[α]
      -------------------- (α:=☆) ∈ γ, α ∉ fv(L)
      γ ⊢ L α ⊒ L′ : p[α]

    (ν⊒)
      γ, α:=☆ ⊢ N[α] ⊒ N′ : p
      ----------------------- α ∉ fv(p)
      γ ⊢ να:=★.N[α] ⊒ N′ : p

They would be required to type the rhs of the reductions

    (V ⟨ ∀X.c[X] ⟩) α  ⊢→  V α ⟨ c[α] ⟩
    V ⟨ ν̅α.c[α] ⟩      ⊢→  να:=★.(V α ⟨ c[α] ⟩)

if applied to the left of a term narrowing.  However, we are allowed
multiple reductions left of a term narrowing, and so both vanish.


## Derived rules

             p
        A ——————> A′
        | \       |
        |  \   ≈  |
        |   \     |
      s |    \ r  | t
        |     \   |
        |  ≈   \  |
        ↓       ↘ ↓
        B ——————> B′
             q

  The following two rules are derivable.

      γ ⊢ M ⊒ M′ : p
      --------------------------  s ⨾ q ≈ p ⨾ t
      γ ⊢ M ⟨ s ⟩ ⊒ M′ ⟨ t ⟩ : q

      γ ⊢ M ⊒ M′ : q
      --------------------------  s ⨾ q ≈ p ⨾ t
      γ ⊢ M ⟨ s̅ ⟩ ⊒ M′ ⟨ t̅ ⟩ : p

  Derivation of the first rule:
  
      γ ⊢ M ⊒ M′ : p
      --------------------  r ≈ p ⨾ t
      γ ⊢ M ⊒ M′ ⟨ t ⟩ : r     
      --------------------------  s ⨾ q ≈ r
      γ ⊢ M ⟨ s ⟩ ⊒ M′ ⟨ t ⟩ : q

  Derivation of the second rule:
  
      γ ⊢ M ⊒ M′ : q
      --------------------  s ⨾ q ≈ r
      γ ⊢ M ⟨ s̅ ⟩ ⊒ M′ : r  
      --------------------------  r ≈ p ⨾ t
      γ ⊢ M ⟨ s̅ ⟩ ⊒ M′ ⟨ t̅ ⟩ : p



## Reflexivity

   Define id_Γ : Γ ⊒ Γ.
   If Γ ⊢ M : A then id_Γ ⊢ M ⊒ M : id_A.



## Cast Inversion

   We might derive a term narrowing in more than one way:

   σ ⊢ M ⊒ M′ : p
   ------------------- r ≈ p ⨾ t
   σ ⊢ M ⊒ M′ ⟨ t ⟩ : r
   -------------------------- s ⨾ q ≈ r
   σ ⊢ M ⟨ s ⟩ ⊒ M′ ⟨ t ⟩ : q

   σ ⊢ M ⊒ M′ : p
   -------------------- s ⨾ r′ ≈ p
   σ ⊢ M ⟨ s ⟩ ⊒ M′ : r′
   --------------------------  q ≈ r′ ⨾ t
   σ ⊢ M ⟨ s ⟩ ⊒ M′ ⟨ t ⟩ : q

             p
        A ——————> A′
        | \     ↗ |
        |  \ ≈ /  |
        | r \ / r′|
      s |    \    | t
        |   / \   |
        |  / ≈ \  |
        ↓ /     ↘ ↓
        B ——————> B′
             q

    If both derivations are possible, they give the same result.
    From either derivation, we get s ⨾ q ≈ p ⨾ t.
    With r:

       s ⨾ q ≈ r ≈ p ⨾ t

    With r′:

       s ⨾ q ≈ s ⨾ r′ ⨾ t ≈ p ⨾ t

    Further, if the r′ derivation exists, then so does the r
    derivation (take r ≈ s ⨾ p ≈ q ⨾ t).

    However, the r derivation may exist when r′ does not:

           id_⋆
        ⋆ ——————> ⋆
        | \       |
        |  \ ≈    |
        |   \     |
     α? | α? \    | α?
        |     \   |
        |    ≈ \  |
        ↓       ↘ ↓
        α ——————> α
           id_α

     There is no possible narrowing from α (lower left)
     to ⋆ (upper right).


## Simulation notation

Let ~↝,~↝′ range over =, ⊢→, ⊢↠, —→_Π, or —↠_Π.

We write

    σ ⊢ M ⊒ M′ : r
  ~↝_Π/~↝′_Π′
    σ, π ⊢ N ⊒ N′ : r

to stand for the following implication: if
  σ ⊢ M ⊒ M′ : r
  M′ ~↝′_Π′ N′
then
  M ~↝_Π N
  π : Π ⊒ Π′
  σ, π ⊢ N ⊑ N′ : r
for some N, Π, π.

Write Σ^★ for Σ when all α bindings are to ★.
Write Σ^☆ for σ where σ : Σ^★ ⊒ ∅.


## Left Seal Narrowing Inversion

If
  σ ⊢ V ⟨ α♯ ⟩ ⊒ V′ : id_α
then
  σ ⊢ V ⊒ V′ : α♯

Proof. By case analysis on the derivation of p.

  Case -⊒

    σ ⊢ V ⊑ V′ : α♯
    ------------------------ -⊒  α♯ ⨾ id_α ≈ α♯
    σ ⊢ V ⟨ α♯ ⟩ ⊑ V′ : id_α
    Immediate.

  Case ⊒-

    σ ⊢ V ⟨ α♯ ⟩ ⊒ V′ : p
    --------------------------------- ⊒- p ⨾ t ≈ id_α
    σ ⊢ V ⟨ α♯ ⟩ ⊒ V′ ⟨ t ⟩ : id_α
    Can only happen if p = t = id_α, in which case recurse.

  Case ⊒+

    σ ⊢ V ⟨ α♯ ⟩ ⊒ V′ : r
    ------------------------------ ⊒+  r ≈ id_α ⨾ t
    σ ⊢ V ⟨ α♯ ⟩ ⊒ V′ ⟨ t̅ ⟩ : id_α
    Can only happen if t = r₀ = id_α, in which case recurse.

  Cases for ⊑Λ and ⊒⟨ν⟩ can't occur because να.p[α♯] ≠ id_α.

  [NEW] Case ⊒α

    The last rule would have to look like

      σ ⊢ L ⊒ L′ : νβ.p[β!]
      ------------------------- ⊒α
      σ, β:=A ⊢ L ⊒ L′ β : p[β?]

    so the conclusion index id_α would force p[β?] = id_α. But in a
    well-typed ν narrowing, the body p has shifted source endpoint:

      p : C↑ ⊒ D[β]

    No shifted source type is the newly bound variable β; and if p is 
    an identity on a shifted variable, its target does not contain β,
    contradicting the occurrence side condition for ν. So this case is
    impossible.

## Tag Factoring

Lemma. Tag Factoring.
If r ⨾ s ≈ G? ⨾ t and r ≠ id_★ then there exists p such that
r ≈ G? ⨾ p and p ⨾ s ≈ t.


## Left Widening Tag Inversion

Lemma. Left Widening Tag Inversion.
If
  σ ⊢ V ⟨ G! ⟩ ⊒ V′ : r
then there exists a p such that
  r ≈ G? ⨾ p
and
  σ ⊢ V ⊒ V′ : p

Proof. By case analysis on the derivation of p.

  Case +⊒

      σ ⊢ V ⊒ V′ : p
      --------------------- +⊒  G? ⨾ p ≈ r
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ : r

    Immediate.

  Case ⊒+, t = id

      σ ⊢ V ⟨ G! ⟩ ⊒ V′ : r
      ------------------------------ ⊒+  r ≈ r ⨾ id_G
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ ⟨ id_G ⟩ : r

    By induction.

  Case ⊒+, t ≠ id

      σ ⊢ V ⊒ V′ : r₁
      ---------------------- +⊒  G? ⨾ r₁ ≈ r₀
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ : r₀
      --------------------------- ⊒+  r₀ ≈ r ⨾ t
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ ⟨ t̅ ⟩ : r

    By Tag Factoring, r ≈ G? ⨾ p and p ⨾ t ≈ r₁. Hence,

      σ ⊢ V ⊒ V′ : r₁
      -------------------- ⊒+  r₁ ≈ p ⨾ t
      σ ⊢ V ⊒ V′ ⟨ t̅ ⟩ : p
      --------------------------- +⊒  r ≈ G? ⨾ p
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ ⟨ t̅ ⟩ : r

  Case ⊒-, t = id
  
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ : r
      ------------------------------ ⊒-  r ≈ r ⨾ id_G
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ ⟨ id_G ⟩ : r

    By induction.

  Case ⊒-, t ≠ id

      σ ⊢ V ⊒ V′ : r₁
      ---------------------- +⊒  G? ⨾ r₁ ≈ r₀
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ : r₀
      --------------------------- ⊒-  r ≈ r₀ ⨾ t
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ ⟨ t ⟩ : r

    By Tag Factoring, r ≈ G? ⨾ p and r₁ ⨾ t ≈ p. Hence,

      σ ⊢ V ⊒ V′ : r₁
      -------------------- ⊒-  p ≈ r₁ ⨾ t
      σ ⊢ V ⊒ V′ ⟨ t ⟩ : p
      --------------------------- +⊒  r ≈ G? ⨾ p
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ ⟨ t ⟩ : r

  Case ⊒Λ

      σ, α:=★ ⊢ V ⟨ G! ⟩ ⊒ V′[α] : p₀[α]
      ----------------------------------- ⊒Λ
      σ ⊢ V ⟨ G! ⟩ ⊒ ΛX.V′[X] : να.p₀[α]

    where r = να.p₀[α]
    By induction, p₀[α] ≈ G? ⨾ p₁[α] and

      σ, α:=★ ⊢ V ⊒ V′[α] : p₁[α]
      ---------------------------- ⊒Λ
      σ ⊢ V ⊒ ΛX.V′[X] : να.p₁[α]
      ----------------------------------- +⊒
      σ ⊢ V ⟨ G! ⟩ ⊒ ΛX.V′[X] : να.p₀[α]

      (i) να.p₀[α] ≈ G? ⨾ να.p₁[α]

  Case ⊒⟨ν⟩

      σ, α:=★ ⊢ V ⟨ G! ⟩ ⊒ V′ ⟨ s[α] ⟩ : p₀[α]
      ----------------------------------------- ⊒⟨ν⟩
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ ⟨ να.s[α] ⟩ : να.p₀[α]

    where r = να.p₀[α]
    By induction, p₀[α] ≈ G? ⨾ p₁[α] and

      σ, α:=★ ⊢ V ⊒ V′ ⟨ s[α] ⟩ : p₁[α]
      ---------------------------------- ⊒⟨ν⟩
      σ ⊢ V ⊒ V′ ⟨ να.s[α] ⟩ : να.p₁[α]
      ----------------------------------------- +⊒
      σ ⊢ V ⟨ G! ⟩ ⊒ V′ ⟨ να.s[α] ⟩ : να.p₀[α]

      (i) να.p₀[α] ≈ G? ⨾ να.p₁[α]



## Right Tag Inversion

  σ ⊢ M ⊒ V : G?
  ------------------------ ⊒+  G? ≈ id_★ ⨾ G?
  σ ⊢ M ⊒ V ⟨ G! ⟩ : id_★
  ----------------------------- ⊒-  G? ≈ id_★ ⨾ G?
  σ ⊢ M ⊒ V ⟨ G! ⟩ ⟨ G? ⟩ : G?


Right Tag Inversion 1.

If σ ⊢ M ⊒ V ⟨ G! ⟩ : q
then q = id_★ and σ ⊢ M ⊒ V : G?.

Proof. By induction on the derivation.

  Case ⊒+

      σ ⊢ M ⊒ V : r
      --------------------- ⊒+  r ≈ q ⨾ G?
      σ ⊢ M ⊒ V ⟨ G! ⟩ : q

    The only solution is q = id_★, r = G?.

  Case +⊒

      σ ⊢ M₀ ⊒ V ⟨ G! ⟩ : p₀
      ----------------------------- +⊒  s ⨾ p₀ ≈ r₀
      σ ⊢ M₀ ⟨ s̅ ⟩ ⊒ V ⟨ G! ⟩ : r₀

    By induction

      σ ⊢ M₀ ⊒ V : G?
      ------------------------- ⊒+
      σ ⊢ M₀ ⊒ V ⟨ G! ⟩ : id_★

    Taking p₀ = id_★, the only solution is r₀ = id_★, s = id_★.
    So we have

      σ ⊢ M₀ ⊒ V : G?
      ------------------------- +⊒
      σ ⊢ M₀ ⟨ id_★ ⟩ ⊒ V : G?      
      ---------------------------------- ⊒+
      σ ⊢ M₀ ⟨ id_★ ⟩ ⊒ V ⟨ G! ⟩ : id_★


  Case -⊒

      σ ⊢ M₀ ⊒ V ⟨ G! ⟩ : r₀
      ----------------------------- -⊒  s ⨾ p₀ ≈ r₀
      σ ⊢ M₀ ⟨ s ⟩ ⊒ V ⟨ G! ⟩ : p₀

    By induction

      σ ⊢ M₀ ⊒ V : G?
      ------------------------- ⊒+
      σ ⊢ M₀ ⊒ V ⟨ G! ⟩ : id_★

    Taking r₀ = id_★, the only solution is p₀ = id_★, s = id_★.
    So we have

      σ ⊢ M₀ ⊒ V : G?
      ------------------------- -⊒
      σ ⊢ M₀ ⟨ id_★ ⟩ ⊒ V : G?      
      ---------------------------------- ⊒+
      σ ⊢ M₀ ⟨ id_★ ⟩ ⊒ V ⟨ G! ⟩ : id_★


Right Tag Inversion 2.

If σ ⊢ M ⊒ V ⟨ G? ⟩ : r
then r = G? and σ ⊢ M ⊒ V : id_★.

Proof. By induction on the derivation.

  Case ⊒-

      σ ⊢ M ⊒ V : q      
      --------------------- ⊒-  r ≈ q ⨾ G?
      σ ⊢ M ⊒ V ⟨ G? ⟩ : r

    The only solution is q = id_★, r = G?.

  Case +⊒

      σ ⊢ M₀ ⊒ V ⟨ G? ⟩ : p₀
      ----------------------------- +⊒  s ⨾ p₀ ≈ r₀
      σ ⊢ M₀ ⟨ s̅ ⟩ ⊒ V ⟨ G? ⟩ : r₀

    By induction

      σ ⊢ M₀ ⊒ V :  id_★
      ----------------------- ⊒-
      σ ⊢ M₀ ⊒ V ⟨ G? ⟩ : G?

    Taking p₀ = G?, the only solution is r₀ = G?, s = id_★.
    So we have

      σ ⊢ M₀ ⊒ V : id_★
      -------------------------- +⊒
      σ ⊢ M₀ ⟨ id_★ ⟩ ⊒ V : id_★
      -------------------------------- ⊒-
      σ ⊢ M₀ ⟨ id_★ ⟩ ⊒ V ⟨ G? ⟩ : G?

  Case -⊒

      σ ⊢ M₀ ⊒ V ⟨ G? ⟩ : r₀
      ----------------------------- -⊒  s ⨾ p₀ ≈ r₀
      σ ⊢ M₀ ⟨ s ⟩ ⊒ V ⟨ G? ⟩ : p₀

    By induction

      σ ⊢ M₀ ⊒ V :  id_★
      ----------------------- ⊒-
      σ ⊢ M₀ ⊒ V ⟨ G? ⟩ : G?

    Taking r₀ = G?, the only solution is p₀ = G?, s = id_★.
    So we have

      σ ⊢ M₀ ⊒ V : id_★
      -------------------------- -⊒
      σ ⊢ M₀ ⟨ id_★ ⟩ ⊒ V : id_★
      -------------------------------- ⊒-
      σ ⊢ M₀ ⟨ id_★ ⟩ ⊒ V ⟨ G? ⟩ : G?


## Right Seal Inversion

  σ ⊢ M ⊒ V : q
  -------------------- ⊒-  r ≈ q ⨾ α♯
  σ ⊢ M ⊒ V ⟨ α♯ ⟩ : r
  --------------------------- ⊒+  r ≈ q ⨾ α♯
  σ ⊢ M ⊒ V ⟨ α♯ ⟩ ⟨ α♭ ⟩ : q

Right Seal Inversion 1.

If σ ⊢ M ⊒ V ⟨ α♯ ⟩ : r
then there exists a q such that
q ⨾ α♯ ≈ r and σ ⊢ M ⊒ V : q.

Proof by induction on the derivation.

  Case ⊒-

      σ ⊢ M ⊒ V : q
      -------------------- ⊒-  r ≈ q ⨾ α♯
      σ ⊢ M ⊒ V ⟨ α♯ ⟩ : r

    Immediate.

  Case +⊒

      σ ⊢ M ⊒ V ⟨ α♯ ⟩ : r₀
      --------------------------- +⊒  s ⨾ r₀ ≈ r
      σ ⊢ M ⟨ s̅ ⟩ ⊒ V ⟨ α♯ ⟩ : r

    By induction

      σ ⊢ M ⊒ V : q₀
      -------------------- ⊒-  r₀ ≈ q₀ ⨾ α♯
      σ ⊢ M ⊒ V ⟨ α♯ ⟩ : r₀

    So we have

      σ ⊢ M ⊒ V : q₀
      ------------------- +⊒  s ⨾ q₀ ≈ q
      σ ⊢ M ⟨ s̅ ⟩ ⊒ V : q
      -------------------------- ⊒-  r ≈ q ⨾ α♯
      σ ⊢ M ⟨ s̅ ⟩ ⊒ V ⟨ α♯ ⟩ : r

    by taking q = s ⨾ q₀, in which case
    q ⨾ α♯ ≈ s ⨾ q₀ ⨾ α♯ ≈ s ⨾ r₀ ≈ r.

  Case -⊒

      σ ⊢ M ⊒ V ⟨ α♯ ⟩ : r₀
      --------------------------- -⊒  s ⨾ r ≈ r₀
      σ ⊢ M ⟨ s ⟩ ⊒ V ⟨ α♯ ⟩ : r

    By induction

      σ ⊢ M ⊒ V : q₀
      -------------------- ⊒-  r₀ ≈ q₀ ⨾ α♯
      σ ⊢ M ⊒ V ⟨ α♯ ⟩ : r₀

    So we have

      σ ⊢ M ⊒ V : q₀
      ------------------- -⊒  s ⨾ q ≈ q₀
      σ ⊢ M ⟨ s ⟩ ⊒ V : q
      -------------------------- ⊒-  r ≈ q ⨾ α♯
      σ ⊢ M ⟨ s ⟩ ⊒ V ⟨ α♯ ⟩ : r

    How do we know such a q exists?
    Either r = q′ ⨾ α♯, in which case we can take q = q′.
    Or r = α?, in which case α:=A and q : ★ ⊒ A exists.
    (Because A is typed under σ, it has no X's.)

    Erratum.  This last case analysis is incomplete.  It assumes a
    cancellation/decomposition property for

        s ⨾ r ≈ q₀ ⨾ α♯

    that fails when the left cast itself is the seal α♯.

    Counterexample.  Let ι = ℕ, let 0 : ι, and let

        σ = α:=id_ι.

    Then the following derivation is valid:

        σ ⊢ 0 ⊒ 0 : id_ι
        ------------------------------ ⊒-    id_ι ⨾ α♯ ≈ α♯
        σ ⊢ 0 ⊒ 0⟨α♯⟩ : α♯
        ------------------------------ -⊒    α♯ ⨾ id_α ≈ α♯
        σ ⊢ 0⟨α♯⟩ ⊒ 0⟨α♯⟩ : id_α

    Thus Right Seal Inversion 1 would have to produce some q such that

        σ ⊢ 0⟨α♯⟩ ⊒ 0 : q

    and, in the stated strengthened form,

        q ⨾ α♯ ≈ id_α.

    No such q exists.  To derive the stripped judgment, the last rule would
    have to introduce the visible left seal.

    In the +⊒ case, matching 0⟨s̅⟩ with 0⟨α♯⟩ forces s̅ = α♯, hence
    s = α♭.  But s must be a narrowing, and α♭ is a widening.

    In the -⊒ case, the premise relates bare constants, so its index is
    id_ι.  The side condition therefore requires

        α♯ ⨾ q ≈ id_ι,

    so q would have to be a narrowing q : α ⊒ ι.  The only coercion that
    goes from α back to ι is α♭, which is again a widening, not a narrowing.

    The missing case in the proof is r = id_α with s = α♯.  It is neither
    r = q′ ⨾ α♯ for any narrowing q′, nor r = α?.


Right Seal Inversion 2.

If

    σ ⊢ M ⊒ V ⟨ α♯ ⟩ : r
    --------------------------- ⊒+  r ≈ q ⨾ α♯
    σ ⊢ M ⊒ V ⟨ α♯ ⟩ ⟨ α♭ ⟩ : q

then there exists a u such that
q ⨾ α♯ ≈ u and σ ⊢ M ⊒ V ⟨ α♯ ⟩ : u.

Proof.  Immediate, taking u = r.

The corresponding `⊒-` case with a right α♭ cast is impossible, since
composition on the right side of a narrowing judgment requires the composed
coercion to be a narrowing, but α♭ is a widening.



## Left ν Widening Lemma

    σ ⊢ V ⊒ V′ : ∀X.p[id_X]
    ------------------------------------ +⊒ (i)
    σ ⊢ V ⟨ ν̅α.t[α♯] ⟩ ⊒ V′ : (να.r[α!])

    (i) (να.r[α!]) ≈ (να.t[α!]) ⨾ (∀X.p[id_X])

  —↠_{Π^★}/=

    σ, α:=☆, Π^☆ ⊢ W ⊒ V′ : να.r[α!]

Proof by mutual induction with the widening and narrowing lemmas,
on the derivation of ⟨ ν̅α.t[α♯] ⟩ and the derivation of V ⊒ V′.

  Case Λ⊒Λ

      σ, X ⊢ V[X] ⊒ V′[X] : p[id_X]
      --------------------------------------- Λ⊒Λ
      σ ⊢ (ΛX.V[X]) ⊒ (ΛX.V′[X]) : ∀X.p[id_X]
      ---------------------------------------------------- +⊒ (i)
      σ ⊢ (ΛX.V[X]) ⟨ ν̅α.t[α♯] ⟩ ⊒ (ΛX.V′[X]) : (να.r[α!])

      (i)  (να.r[α!]) ≈ (να.t[α!]) ⨾ (∀X.p[id_X])

    —↠_{α:=★}/=   

      σ, α:=id_★ ⊢ V[α] ⊒ V′[α] : p[id_α]
      ------------------------------------------- +⊒ (ii)
      σ, α:=id_★ ⊢ V[α] ⟨ t[α♯] ⟩ ⊒ V′[α] : r[α?]
      --------------------------------------------------- ⊒Λ
      σ, α:=☆ ⊢ V[α] ⟨ t[α♯] ⟩ ⊒ (ΛX.V′[X]) : (να.r[α!])

      (ii)  r[α?] ≈ t[α?] ⨾ p[id_α]

    —↠_{Π^★}/=  (widening lemma, on a smaller cast)    

      σ, α:=id_★, Π^☆ ⊢ W ⊒ V′[α] : r[α?]    
      ------------------------------------------ ⊒Λ
      σ, α:=☆, Π^☆ ⊢ W ⊒ (ΛX.V′[X]) : (να.r[α!])

    (see Example 14)

  Case ⊒+

      σ ⊢ V ⊒ V′ : ∀X.p₀[id_X]
      --------------------------------------- ⊒+  (i)
      σ ⊢ V ⊒ V′ ⟨ ∀X.s[id_X] ⟩ : ∀X.p₁[id_X]
      ---------------------------------------------------- +⊒ (ii)
      σ ⊢ V ⟨ ν̅α.t[α♯] ⟩ ⊒ V′ ⟨ ∀X.s[id_X] ⟩ : (να.p₂[α!])

      (i)   (∀X.p₁[id_X]) ⨾ (∀X.s̄[id_X]) ≈ (∀X.p₀[id_X])
      (ii)  (να.p₂[α!]) ≈ (να.t[α!]) ⨾ (∀X.p₁[id_X])

    =/=

      σ ⊢ V ⊒ V′ : ∀X.p₀[id_X]
      ------------------------------------- +⊒ (iii)
      σ ⊢ V ⟨ ν̅α.t[α♯] ⟩ ⊒ V′ : (να.p₃[α!])
      ---------------------------------------------------- ⊒+ (iv)  
      σ ⊢ V ⟨ ν̅α.t[α♯] ⟩ ⊒ V′ ⟨ ∀X.s[id_X] ⟩ : (να.p₂[α!])

      (iii)  (να.p₃[α!]) ≈ (να.t[α!]) ⨾ (∀X.p₀[id_X])
      (iv)   (να.p₂[α!]) ⨾ (∀X.s̄[id_X]) ≈ (να.p₃[α!])

    —↠_{Π^★}/=  (by induction, V ⟨ ν̅α.t[α♯] ⟩ —↠_{Π^★} W)

      σ, Π^☆ ⊢ W ⊒ V′ : (να.p₃[α!])
      -------------------------------------------- ⊒+ (iv) 
      σ, Π^☆ ⊢ W ⊒ V′ ⟨ ∀X.s[id_X] ⟩ : (να.p₂[α!])

    We define p₃ by (iii), and (iv) follows because
      (να.p₂[α!]) ⨾ (∀X.s̄[id_X]) ≈(ii)
      (να.t[α!]) ⨾ (∀X.p₁[id_X]) ⨾ (∀X.s̄[id_X]) ≈(i)
      (να.t[α!]) ⨾ (∀X.p₀[id_X]) ≈(iii)
      (να.p₃[α!])        

  Case +⊒

      σ ⊢ V ⊒ V′ : ∀X.p₀[id_X]
      ---------------------------------------- ⊒+ (i)
      σ ⊢ V ⊒ V′ ⟨ \dual{∀X.s[id_X]} ⟩ : ∀X.p₁[id_X]
      ----------------------------------------------------------- +⊒ (ii)
      σ ⊢ V ⟨ ν̅α.t[α♯] ⟩ ⊒ V′ ⟨ \dual{∀X.s[id_X]} ⟩ : (να.p₂[α!])
      (i)   (∀X.p₀[id_X]) ⨾ (∀X.s[id_X]) ≈ (∀X.p₁[id_X])
      (ii)  (να.p₂[α!]) ≈ (να.t[α!]) ⨾ (∀X.p₁[id_X])

    =/=

      σ ⊢ V ⊒ V′ : ∀X.p₀[id_X]
      ------------------------------------- +⊒ (iii)
      σ ⊢ V ⟨ ν̅α.t[α♯] ⟩ ⊒ V′ : (να.p₃[α!])
      ------------------------------------------------ ⊒+ (iv)
      σ, Π^☆ ⊢ W ⊒ V′ ⟨ \dual{∀X.s[id_X]} ⟩ : (να.p₂[α!])
      (iii)  (να.p₃[α!]) ≈ (να.t[α!]) ⨾ (∀X.p₀[id_X])
      (iv)   (να.p₃[α!]) ⨾ (∀X.s[id_X]) ≈ (να.p₂[α!])

    —↠_{Π^★}/=  (by induction, V ⟨ ν̅α.t[α♯] ⟩ —↠_{Π^★} W)

      σ, Π^☆ ⊢ W ⊒ V′ : (να.p₃[α!])
      ------------------------------------------------ ⊒+ (iv)
      σ, Π^☆ ⊢ W ⊒ V′ ⟨ \dual{∀X.s[id_X]} ⟩ : (να.p₂[α!])

      We define p₃ by (iii), and (iv) follows because
        (να.p₃[α!]) ⨾ (∀X.s[id_X]) ≈(iii) 
        (να.t[α!]) ⨾ (∀X.p₀[id_X]) ⨾ (∀X.s[id_X]) ≈(i)
        (να.t[α!]) ⨾ (∀X.p₁[id_X]) ≈(ii)
        (να.p₂[α!])        

  Case ⊒Λ/-⊒

      σ, α:=★ ⊢ V ⊒ V′[α] : p₀[α?]
      ------------------------------ ⊒Λ
      σ ⊢ V ⊒ ΛX.V′[X] : (να.p₀[α!])
      -------------------------------------------------- -⊒ (i)
      σ ⊢ V ⟨ \dual{να.s[α♯]} ⟩ ⊒ ΛX.V′[X] : (∀X.p₁[id_X])
      --------------------------------------------------------------- +⊒ (ii)
      σ ⊢ V ⟨ ν̅α.t[α♯] ⟩ ⟨ \dual{να.s[α♯]} ⟩ ⊒ ΛX.V′[X] : (να.p₂[α!])

      (i)   (να.p₀[α!]) ≈ (να.s[α!]) ⨾ (∀X.p₁[id_X])
      (ii)  (να.p₂[α!]) ≈ (να.t[α!]) ⨾ (∀X.p₁[id_X])

    —↠_{α:=★}/=

      σ, α:=★ ⊢ V ⊒ V′[α] : p₀[α?]
      ------------------------------------------- -⊒ (iii)
      σ, α:=id_★ ⊢ V ⟨ s[α?] ⟩ ⊒ V′[α] : p₁[id_α]
      ------------------------------------------------------ +⊒ (iv)
      σ, α:=id_★ ⊢ V ⟨ t[α♯] ⟩ ⟨ s[α?] ⟩ ⊒ ΛX.V′[X] : p₂[α?]
      -------------------------------------------------------- ⊒Λ
      σ, α:=☆ ⊢ V ⟨ t[α♯] ⟩ ⟨ s[α?] ⟩ ⊒ ΛX.V′[X] : (να.p₂[α!])

      (iii)  p₀[α?] ≈ s[α?] ⨾ p₁[id_α]
      (iv)   p₂[α?] ≈ t[α?] ⨾ p₁[id_α]

    Then V ⟨ s[α?] ⟩ is a value, and we invoke Left Widening on smaller casts t[α♯].

    (see Example 20)

  Case -⊒-

      σ ⊢ V ⊒ V′ : p₀
      ------------------------------------------------------------- -⊒- (i)
      σ ⊢ V ⟨ \dual{να.s₀[α♯]} ⟩ ⊒ V ⟨ \dual{να.t₀[α♯]} ⟩ : ∀X.p₁[id_X]
      ---------------------------------------------------------------------------- +⊒ (ii)
      σ ⊢ V ⟨ \dual{να.s₀[α♯]} ⟩ ⟨ ν̅α.t[α♯] ⟩ ⊒ V ⟨ \dual{να.t₀[α♯]} ⟩ : να.p₂[α!]

      (i)   p₀ ⨾ (να.s₀[α!]) ≈ (να.t₀[α!]) ⨾ (∀X.p₁[id_X])
      (ii)  (να.p₂[α!]) ≈ (να.t[α!]) ⨾ (∀X.p₁[id_X])

    ⊢→/=
      σ ⊢ (να:=★. (V ⟨ \dual{να.t₀[α♯]} ⟩) α) ⟨ t[α♯] ⟩ ⊒ V ⟨ \dual{να.s₀[α♯]} ⟩ : να.p₂[α!]
    —→_{α:=★}/=
      σ, α:=☆ ⊢ (V ⟨ \dual{να.t₀[α♯]} ⟩) α ⟨ t[α♯] ⟩ ⊒ V ⟨ \dual{να.s₀[α♯]} ⟩ : να.p₂[α!]
    ⊢→/=

      σ ⊢ V ⊒ V′ : p₀      
      ------------------------------------------------ -⊒- (iii)
      σ, α:=☆ ⊢ V ⟨ t̅₀[α!] ⟩ ⊒ V ⟨ s̅₀[α!] ⟩ : p₁[id_α]
      -------------------------------------------------------- +⊒ (iv)
      σ, α:=☆ ⊢ V ⟨ t̅₀[α!] ⟩ ⟨ t[α♯] ⟩ ⊒ V ⟨ s̅₀[α!] ⟩ : p₂[α?]            
      --------------------------------------------------------------------- ⊒⟨ν⟩
      σ, α:=☆ ⊢ V ⟨ t̅₀[α!] ⟩ ⟨ t[α♯] ⟩ ⊒ V ⟨ \dual{να.s₀[α♯]} ⟩ : να.p₂[α!]      

      (iii)  p₀ ⨾ s₀[α!] ≈ t₀[α!] ⨾ p₁[id_α] 
      (iv)   p₂[α?] ≈ t[α?] ⨾ p₁[id_α]

    (see Example 21)


## Left Widening Lemma

    σ ⊢ V ⊒ V′ : p
    ------------------- +⊒  t ⨾ p ≈ r
    σ ⊢ V ⟨ t̅ ⟩ ⊒ V′ : r
  —↠_{Σ^★}/=
    σ, Σ^☆ ⊢ W ⊒ V′ : r

Proof. By mutual induction with the Left ν Widening and Narrowing Lemmas,
on the derivations of t̅ and V ⊒ V′.
  
  Case id_a

      σ ⊢ V ⟨ id_a ⟩ ⊒ V′ : r
    —→/=
      σ ⊢ V ⊒ V′ : r

  Case (s→t)

      σ ⊢ V ⟨ s→t̅ ⟩ ⊒ V′ : r
      lhs is a value

  Case (∀X.s[id_X])

      σ ⊢ V ⟨ ∀X.s̅[X] ⟩ ⊒ V′ : r
      lhs is a value

  Case (ν̅α.s[α♯])

      σ ⊢ V ⟨ ν̅α.s[α♯] ⟩ ⊒ V′ : r
      by ν Left Widening Lemma

  Case (s;t)

      σ ⊢ V ⟨ \dual{s;t} ⟩ ⊒ V′ : r
    —→/=
      σ ⊢ V ⟨ t̅ ⟩ ⟨ s̅ ⟩ ⊒ V′ : r
    —↠_{Σ^★}/= (induction)
      σ, Σ^☆ ⊢ W ⟨ s̅ ⟩ ⊒ V′ : r
    —↠_{Π^★}/= (induction)      
      σ, Σ^☆, Π^☆ ⊢ W″ ⊒ V′ : r

   Case G!

      σ ⊢ V ⟨ G! ⟩ ⊒ V′ : r
      lhs is a value

   Case α♭   

      σ ⊢ V ⊒ V′ : id_α
      ----------------------------- +⊒  α♯ ⨾ id_α ≈ α♯
      σ ⊢ V ⟨ α♭ ⟩ ⊒ V′ : α♯
      by canonical values, V = V″ ⟨ α♯ ⟩ and by Right Seal Inversion
    =/=
      σ ⊢ V″ ⊒ V′ : α♯
      ------------------------ -⊒  α♯ ⨾ id_α ≈ α♯
      σ ⊢ V″ ⟨ α♯ ⟩ ⊒ V′ : id_α
      ----------------------------- +⊒  α♯ ⨾ id_α ≈ α♯
      σ ⊢ V″ ⟨ α♯ ⟩ ⟨ α♭ ⟩ ⊒ V′ : α♯
    ⊢→/=
      σ ⊢ V″ ⊒ V′ : r


## Left Narrowing Lemma

    σ ⊢ V ⊒ V′ : r
    ------------------- -⊒  t̅ ⨾ p ≈ r
    σ ⊢ V ⟨ t̅ ⟩ ⊒ V′ : p
  —↠_{Σ^★}/=
    σ, Σ^☆ ⊢ W ⊒ V′ : p

Proof. By mutual induction with the Left ν Widening and Widening Lemmas,
on the derivations of t̅ and V ⊒ V′.
  
  Case id_a

      σ ⊢ V ⟨ id_a ⟩ ⊒ V′ : p
    —→/=
      σ ⊢ V ⊒ V′ : r

  Case (s→t)

      σ ⊢ V ⟨ \dual{s→t} ⟩ ⊒ V′ : p
      lhs is a value

  Case (∀X.s[id_X])

      σ ⊢ V ⟨ \dual{∀X.s[X]} ⟩ ⊒ V′ : p
      lhs is a value

  Case (να.s̅[α!])

      σ ⊢ V ⟨ να.s̅[α!] ⟩ ⊒ V′ : p
      lhs is a value

  Case (s;t)

      σ ⊢ V ⟨ \dual{s;t} ⟩ ⊒ V′ : p
    —→/=
      σ ⊢ V ⟨ t̅ ⟩ ⟨ s̅ ⟩ ⊒ V′ : p
    —↠_{Σ^★}/= (induction)
      σ, Σ^☆ ⊢ W ⟨ s̅ ⟩ ⊒ V′ : p
    —↠_{Π^★}/= (induction)      
      σ, Σ^☆, Π^☆ ⊢ W″ ⊒ V′ : p

  Case G?
   
      σ ⊢ V ⊒ V′ : r
      ----------------------- -⊒  G? ⨾ p ≈ r
      σ ⊢ V ⟨ G? ⟩ ⊒ V′ : p
      by canonical values, V = V″ ⟨ G! ⟩ and Left Widening Tag Inversion
      σ ⊢ V″ ⊒ V′ : p
      ----------------------- +⊒  G? ⨾ p ≈ r
      σ ⊢ V″ ⟨ G! ⟩ ⊒ V′ : r
      ----------------------- -⊒  G? ⨾ p ≈ r
      σ ⊢ V″ ⟨ G! ⟩ ⟨ G? ⟩ ⊒ V′ : p
    —→/=
      σ ⊢ V″ ⊒ V′ : p

  Case α♯

      σ ⊢ V ⟨ α♯ ⟩ ⊒ V′ : p
      lhs is a value


## Catchup Lemma

    V value    σ ⊢ M ⊒ V : p
  —↠_{Π^★}/=
    W value    σ, Π^☆ ⊢ W ⊒ V : p

  In the Agda de Bruijn mechanization, the unchanged target value and coercion
  index are weakened by the emitted store changes, so the conclusion uses
  `applyTerms Π` on `V` and `applyCoercions Π` on `p`.

Lemma. Shifted-source Catchup Inversion. [New]
If catchup is applied to a premise under `σ, α:=★`, then the emitted store
changes may be pulled back under the enclosing type binder:

    σ, α:=★ ⊢ M[α] ⊒ U[α] : p[α]
  —↠_{Π^★}/=
    σ, α:=★, Π^☆ ⊢ W ⊒ U[α] : p[α]
  implies
    σ, Π^☆ ⊢ W₀ ⊒ ΛX.U[X] : να.p[α]

and similarly, if the right-hand side is `U ⟨ s[α] ⟩`, then

    σ, α:=★, Π^☆ ⊢ W ⊒ U ⟨ s[α] ⟩ : p[α]
  implies
    σ, Π^☆ ⊢ W₀ ⊒ U ⟨ να.s[α] ⟩ : να.p[α].

Proof.  Invert the de Bruijn shift on the source reduction sequence and on the
emitted store-change prefix.  The shifted target term and coercion are rewritten
with the usual under-binder action lemmas, then the result is rebuilt with
`⊒Λ` or `⊒⟨ν⟩`.

Lemma. Split Catchup Case. [New]
If the induction hypothesis catches up the split premise

    σ, α:q ⊢ N[α] ⊒ N′[α] : p[α]
  —↠_{Π^★}/=
    σ, α:q, Π^☆ ⊢ W ⊒ N′[α] : p[α],

then the split conclusion catches up as

    σ, α:=A⊒, αᵢ:=★ ⊢ N[αᵢ] ⊒ N′[α] : p[α]
  —↠_{Π′^★}/=
    σ, α:=A⊒, αᵢ:=★, Π′^☆ ⊢ W′ ⊒ N′[α] : p[α].

Proof.  Transport the source-opening reduction from `α` to the source-only
`αᵢ` introduced by `split`, transport the emitted store changes through the
two fresh entries, and rebuild the final narrowing derivation with `split`.

Lemma. Extend Prefix Transport. [New]
If the induction hypothesis catches up the premise of `extend`

    σ, α:=A⊒ ⊢ M ⊒ N′[α] : p[α]
  —↠_{Π^★}/=
    σ, α:=A⊒, Π^☆ ⊢ W ⊒ N′[α] : p[α],

and `q : B ⊒ A` and `p[α] : C ⊒ D` are well typed under the corresponding
source stores, then

    σ, α:q ⊢ M ⊒ N′[α] : p[α]
  —↠_{Π^★}/=
    σ, α:q, Π^☆ ⊢ W ⊒ N′[α] : p[α].

Proof.  By induction on the emitted store-change prefix.  If the prefix emits
no type variable, rewrite away the empty store changes and rebuild `extend`
directly.  If the prefix ends in a fresh source-only star entry, peel that
entry, shift `q` and `p[α]` under the fresh binder, apply the induction
hypothesis to the tail, and rewrite the opened target term and coercion with
the usual under-binder action lemmas.  The right-only and both-side emitted
entries are impossible when the emitted target store is empty.

Counterexample screen. [New]  Do not generalize this lemma to an arbitrary
store-narrowing prefix at a single final type context `Δ`.  Take the prefix to
be one source-only star entry followed by the `extend` store entry.  The old
side can type the tail as `α:=A⊒`, but the transported side needs the shifted
coercion `q` under the fresh star binder.  If `q` mentions the top variable of
the incoming context, that shifted coercion is only well typed with the extra
binder evidence.  Thus the induction must remember the emitted store changes
and shift `q` and `p[α]` in the recursive call.

Counterexample screen. [New]  Do not generalize emitted-prefix transport to
an arbitrary right-hand target `V`.  In the `⊒α` case, the old conclusion has
target `L′ • α`.  Rebuilding by `extend` would require that target to be an
opening `N′[α]`, which in turn would require the body `L′` itself to be an
opened term.  The rule gives no such fact.  Thus the transport statement must
keep the actual catchup/`extend` target shape, or else split out the right-α
case with a separate invariant.

Lemma. Emitted Prefix Transport. [New]
If an emitted store-change prefix `ρ` is kept as structured syntax, then the
`extend` transport is stable under that prefix for the opened target produced
by the `extend` rule:

    ρ, σ, α:=A⊒ ⊢ W ⊒ N′[α] : p[α]
  implies
    ρ, σ, α:q ⊢ W ⊒ N′[α] : p[α].

The same statement holds when `ρ` is followed by a source-only emitted star
entry before the old store tail.

[New] In the mechanized statement, if `ρ` contains entries generated by
`combineStoreNrw`, the induction must also carry the shifted well-typing
premises for `q` and `p[α]` at every suffix of `ρ`.  These shifted premises are
not consequences of source-store inclusion alone; they come from the same
emitted type-context history that produced `ρ`.

Proof.  By induction on the narrowing derivation.  Ordinary term constructors
weaken their coercion typings along source-store inclusion and use the
induction hypotheses on subterms.  Binder constructors shift the whole emitted
prefix `ρ`, as well as `q`, `p[α]`, and the old store tail, before applying the
induction hypothesis.  If the leading entry of `ρ` is consumed by `extend`,
`α⊒α`, or `⊒α`, the recursive call is made on the remaining emitted prefix
with the corresponding right-only or tail shape.

Lemma. Right ν Catchup Case. [New]
If the induction hypothesis catches up the shifted premise of `ν⊒`

    σ, α:=★ ⊢ N ⊒ V[α] : p[α]
  —↠_{Π^★}/=
    σ, α:=★, Π^☆ ⊢ W ⊒ V[α] : p[α],

then

    σ ⊢ ν★.N ⊒ V : να.p[α]
  —↠_{Π′^★}/=
    σ, Π′^☆ ⊢ W′ ⊒ V : να.p[α].

Proof.  Lift the reduction through the `ν` wrapper, use the canonical runtime
shape of the caught-up polymorphic value to take the `ν` store-opening step,
then transport the emitted store prefix back through the source-only star
entry and rebuild the `ν⊒` conclusion.

Proof. By induction on the proof of the hypothesis.

  Case extend [New]

      σ, α:=A⊒ ⊢ M ⊒ V : p[α]
      -------------------------------- extend
      σ, α:q ⊢ M ⊒ V : p[α]

    Apply induction to the premise, then rebuild the `extend` rule after
    transporting the emitted store narrowing through the fresh `α` entry.

  Case split [New]

      σ, α:q ⊢ M ⊒ V : p[α]
      -------------------------------- split
      σ, α:=A⊒, αᵢ:=★ ⊢ M ⊒ V : p[α]

    Apply induction to the premise, then rebuild the `split` rule after
    transporting the emitted store narrowing through the two fresh entries.
    The recursive premise consumes the source-only `αᵢ:=★` entry, so the
    mechanized proof transports that premise under the remaining both-side
    `α:q` entry while the split side conditions are transported under the full
    `α:=A⊒, αᵢ:=★` prefix.

  Case ⊒blame, x⊒x, ·⊒·, α⊒α, ⊒α, ν⊒ν, ⊒ν, and ⊕⊒⊕ [New]

    These cases are impossible because the right-hand term is not a value of
    the required syntactic form.

  Case λ⊒λ [New]

      σ, x:p ⊢ N[x] ⊒ N′[x] : q
      ---------------------------- λ⊒λ
      σ ⊢ λx.N[x] ⊒ λx.N′[x] : p̅→q

    Take zero steps.  The source value is `λx.N[x]`, and the original
    narrowing derivation is the final witness.

  Case Λ⊒Λ [New]

      σ, X ⊢ M[X] ⊒ V[X] : p
      ------------------------ Λ⊒Λ
      σ ⊢ ΛX.M[X] ⊒ ΛX.V[X] : ∀X.p

    In the paper value grammar this case is immediate because the source body
    is already a value.  The Agda `Λ⊒Λ` rule carries that source-body value
    premise explicitly, so take zero steps and reuse the original derivation.

  Case κ⊒κ [New]

      ---------------- κ⊒κ
      σ ⊢ κ ⊒ κ : id

    Take zero steps.  The source value is `κ`, and the original narrowing
    derivation is the final witness.

  Case ⊒+

      σ ⊢ M ⊒ V : r
      ------------------ ⊒+  r ≈ q ⨾ t 
      σ ⊢ M ⊒ V ⟨ t̅ ⟩ : q
    —↠_{Π^★}/=
      σ, Π^☆ ⊢ W ⊒ V : r
      ------------------- ⊒+  r ≈ q ⨾ t 
      σ, Π^☆ ⊢ W ⊒ V ⟨ t̅ ⟩ : q

  Case ⊒-

      σ ⊢ M ⊒ V : q
      ------------------ ⊒-  r ≈ q ⨾ t
      σ ⊢ M ⊒ V ⟨ t ⟩ : r
    —↠_{Π^★}/=
      σ, Π^☆ ⊢ W ⊒ V : q
      ------------------- ⊒-  r ≈ q ⨾ t 
      σ, Π^☆ ⊢ W ⊒ V ⟨ t ⟩ : r

  Case ⊒Λ

    σ, α:=★ ⊢ M ⊒ V[α] : p[α]
    ----------------------------- ⊒Λ
    σ ⊢ M ⊒ (ΛX.V[X]) : να.p[α]
  —↠_{Π^★}/= (induction)
    σ, α:=★, Π^☆ ⊢ W ⊒ V[α] : p[α]
    --------------------------------- ⊒Λ
    σ, Π^☆ ⊢ W ⊒ (ΛX.V[X]) : να.p[α]

  Case ⊒⟨ν⟩

    σ, α:=★ ⊢ M ⊒ V ⟨ s[α] ⟩ : p[α]
    s[α] inert
    ----------------------------------------- ⊒⟨ν⟩
    σ ⊢ M ⊒ V ⟨ να.s[α] ⟩ : να.p[α]
  —↠_{Π^★}/= (induction)
    σ, α:=★, Π^☆ ⊢ W ⊒ V ⟨ s[α] ⟩ : p[α]
    --------------------------------------------- ⊒⟨ν⟩
    σ, Π^☆ ⊢ W ⊒ V ⟨ να.s[α] ⟩ : να.p[α]

    Note that V ⟨ s[α] ⟩ is itself a value, so induction applies.  The
    mechanized rule records this as an explicit `s[α] inert` premise.

  Case ν⊒ [New]

      σ, α:=★ ⊢ N ⊒ V : p
      --------------------- ν⊒
      σ ⊢ ν★.N ⊒ V : p

    Apply induction to the shifted premise.  Then wrap the caught-up source
    through the `ν` store-opening rule, use the canonical shape of the caught-up
    polymorphic value, and transport the emitted store narrowing back through
    the type-variable shift.

  Case +⊒

    σ ⊢ M ⊒ V : p
    ------------------- +⊒  s ⨾ p ≈ r
    σ ⊢ M ⟨ s̅ ⟩ ⊒ V : r
  —↠_{Σ^★}/= (induction)
    σ, Σ^☆ ⊢ V′ ⊒ V : p
    ------------------------ +⊒  s ⨾ p ≈ r
    σ, Σ^☆ ⊢ V′ ⟨ s̅ ⟩ ⊒ V : r
  —↠_{Π^★}/= (Left Widening Lemma)
    σ, Σ^☆, Π^☆ ⊢ W ⊒ V : r

  Case -⊒

    σ ⊢ M ⊒ V : r
    ------------------- -⊒  s ⨾ p ≈ r
    σ ⊢ M ⟨ s ⟩ ⊒ V : p
  —↠_{Σ^★}/= (induction)
    σ, Σ^☆ ⊢ V′ ⊒ V : r
    ------------------------ -⊒  s ⨾ p ≈ r
    σ, Σ^☆ ⊢ V′ ⟨ s ⟩ ⊒ V : p
  —↠_{Π^★}/= (Left Narrowing Lemma)
    σ, Σ^☆, Π^☆ ⊢ W ⊒ V : p


## Wrap Narrowing Lemma

    σ ⊢ V′ ⊒ V ⟨ \dual{s→t} ⟩ : p̅→q    σ ⊢ W′ ⊒ W : p
    -------------------------------------------
    σ ⊢ V′ W′ ⊒ (V ⟨ \dual{s→t} ⟩) W : q
  —↠_{Π^★}/⊢→
    σ, Π^☆ ⊢ N′ ⊒ V (W ⟨ s ⟩) ⟨ t̅ ⟩ : p

Proof. By induction on the derivation of σ ⊢ V′ ⊒ V ⟨ \dual{s→t} ⟩ : p̅→q.

  Case ⊒-

      σ ⊢ V′ ⊒ V : s₁→t₁
      ----------------------------- ⊒- (i)
      σ ⊢ V′ ⊒ (V ⟨ \dual{s→t} ⟩) : s₂→t₂           σ ⊢ W′ ⊒ W ⊢ s₂
      ------------------------------------------------------- ·⊒·
      σ ⊢ V′ W′ ⊒ (V ⟨ \dual{s→t} ⟩) W : t₂
      (i) (s₂→t₂) ≈ (s₁→t₁)⨾(s→t)
    ⊢→
                            W′ ⊒ W : s₂
                            ----------- ⊒+  s₂ ≈ s₁⨾s
      σ ⊢ V′ ⊒ V : s₁→t₁    W′ ⊒ W ⟨ s ⟩ : s₁
      -------------------------------------- ·⊒·
      σ ⊢ V′ W′ ⊒ (V (W ⟨ s ⟩)) : t₁
      ---------------------------------- ⊒+  t₂ ≈ t₁⨾t
      σ ⊢ V′ W′ ⊒ (V (W ⟨ s ⟩)) ⟨ t̅ ⟩ : t₂

  Case +⊒
         
    We are given
    
      σ ⊢ V′ ⊒ (V ⟨ \dual{s→t} ⟩) : s₄→t₄
      ------------------------------------------ +⊒ (i)
      σ ⊢ (V′ ⟨ s₃→t₃ ⟩) ⊒ (V ⟨ \dual{s→t} ⟩) : s₂→t₂           σ ⊢ W′ ⊒ W : s₂
      -------------------------------------------------------------------- ·⊒·
      σ ⊢ (V′ ⟨ s₃→t₃ ⟩) W′ ⊒ (V ⟨ \dual{s→t} ⟩) W : t₂
      (i)  (s₂→t₂) ≈ (s₃→t₃)⨾(s₄→t₄)   

    From this we derive
    
      σ ⊢ W′ ⊒ W : s₂
      --------------------- ⊒-  s₂ ≈ s₃⨾s₄
      σ ⊢ W′ ⊒ W ⟨ s̅₃ ⟩ : s₄
    —↠_{Π₁^★}/=
      σ, Π₁^☆ ⊢ W″ ⊒ W : s₄

    Now apply induction hypothesis where W′ = W″, p = s₄, q = t₄.
    We know V′ W″ —↠_{Π₂^★} N′ and σ ⊢ N′ ⊒ V (W ⟨ s ⟩) ⟨ t̅ ⟩ : t₄.
    Hence

                 (V′ ⟨ s₃→t₃ ⟩) W′
      ⊢→         V′ (W′ ⟨ s̅₃ ⟩) ⟨ t₃ ⟩
      —↠_{Π₁^★}  V′ W″ ⟨ t₃ ⟩
      —↠_{Π₂^★}  N′ ⟨ t₃ ⟩

    and 

      σ, Π₁^☆, Π₂^☆ ⊢ N′ ⊒ V (W ⟨ s ⟩) ⟨ t̅ ⟩ : t₄        
      ----------------------------------------------- +⊒  t₂ ≈ t₃⨾t₄
      σ, Π₁^☆, Π₂^☆ ⊢ N′ ⟨ t₃ ⟩ ⊒ V (W ⟨ s ⟩) ⟨ t̅ ⟩ : t₂

  Case -⊒

    We are given
    
      σ ⊢ V′ ⊒ (V ⟨ \dual{s→t} ⟩) : s₂→t₂
      ------------------------------------------ -⊒ (i)
      σ ⊢ (V′ ⟨ \dual{s₃→t₃} ⟩) ⊒ (V ⟨ \dual{s→t} ⟩) : s₄→t₄           σ ⊢ W′ ⊒ W : s₄
      -------------------------------------------------------------------- ·⊒·
      σ ⊢ (V′ ⟨ \dual{s₃→t₃} ⟩) W′ ⊒ (V ⟨ \dual{s→t} ⟩) W : t₄
      (i)  (s₂→t₂) ≈ (s₃→t₃)⨾(s₄→t₄)

    From this we derive
    
      σ ⊢ W′ ⊒ W : s₄
      --------------------- +⊒  s₂ ≈ s₃⨾s₄
      σ ⊢ W′ ⟨ s₃ ⟩ ⊒ W : s₂
    —↠_{Π₁^★}/=
      σ, Π₁^☆ ⊢ W″ ⊒ W : s₂

    Now apply induction hypothesis where W′ = W″, p = s₂, q = t₂.
    We know V′ W″ —↠ N′ and σ ⊢ N′ ⊒ V (W ⟨ s ⟩) ⟨ t̅ ⟩ : t₂.

    Hence

                 (V′ ⟨ \dual{s₃→t₃} ⟩) W′
      ⊢→         V′ (W′ ⟨ s₃ ⟩) ⟨ t̅₃ ⟩
      —↠_{Π₁^★}  V′ W″ ⟨ t̅₃ ⟩
      —↠_{Π₂^★}  N′ ⟨ t̅₃ ⟩

    and 

        σ, Π₁^☆, Π₂^☆ ⊢ N′ ⊒ V (W ⟨ s ⟩) ⟨ t̅ ⟩ : t₂        
        ----------------------------------------------- +⊒  t₂ ≈ t₃⨾t₄
        σ, Π₁^☆, Π₂^☆ ⊢ N′ ⟨ t̅₃ ⟩ ⊒ V (W ⟨ s ⟩) ⟨ t̅ ⟩ : t₄


## Wrap Widening Lemma

  Similar to Wrap Narrowing.


## Gradual Guarantee

    σ ⊢ M ⊒ M′ : p
  —↠_Π/—→_Π′    π : Π ⊒ Π′
    σ, π ⊢ N ⊒ N′ : p

Proof: By induction on the derivations of σ ⊢ M ⊒ M′ : p and M′ —→_Π′ N′.

    κ₁ ⊕ κ₂  ⊢→  δ(⊕)(κ₁,κ₂)

      (⊕⊒⊕)
      
        σ ⊢ κ₁ ⊒ κ₁ : id_ι₁    σ ⊢ κ₂ ⊒ κ₂ : id_ι₂
        ------------------------------------------ ⊕⊒⊕
        σ ⊢ κ₁ ⊕ κ₂ ⊒ κ₁ ⊕ κ₂ : id_ι₃
      ⊢→/⊢→
        σ ⊢ δ(⊕)(κ₁,κ₂) ⊒ δ(⊕)(κ₁,κ₂) : id_ι₃

    (λx.N′[x]) W′  ⊢→  N′[W′]

      Induct on the derivation of σ ⊢ N ⊒ λx.N′[x] : p̅→q and use catchup.

      (λ⊒λ)

          σ, x:p ⊢ N[x] ⊒ N′[x] : q
          ---------------------------- λ⊒λ
          σ ⊢ λx.N[x] ⊒ λx.N′[x] : p̅→q        σ ⊢ W ⊒ W′ : p
          -------------------------------------------------- ·⊒·
          σ ⊢ (λx.N[x]) W ⊒ (λx.N′[x]) W′ : q
        ⊢→/⊢→
          σ ⊢ N[W] ⊒ N′[W′] : q

          (assumes a suitable substitution lemma)

      → widening (+⊒)

         Let V′ = λx.N′[x]. (This means +⊒ must be used, so we don't need inversion.)

          σ ⊢ V ⊒ V′ : p′→q′
          ------------------------- +⊒  (s→t)⨾(p′→q′) ≈ p̅→q
          σ ⊢ V ⟨ s→t ⟩ ⊒ V′ : p̅→q                            σ ⊢ W ⊒ W′ : p
          ------------------------------------------------------------------ ·⊒·
          σ ⊢ (V ⟨ s→t ⟩) W ⊒ V′ W′ : q
        ⊢→/=
                                σ ⊢ W ⊒ W′ : p
                                -------------- +⊒  s̅⨾p ≈ p′ 
          σ ⊢ V ⊒ V′ : p′→q′    σ ⊢ W ⟨ s̅ ⟩ ⊒ W′ : p′
          ------------------------------------------ ·⊒·
          σ ⊢ V (W ⟨ s̅ ⟩) ⊒ V′ W′ : q′                   
          -------------------------------- +⊒  t⨾q ≈ q′
          σ ⊢ (V (W ⟨ s̅ ⟩)) ⟨ t ⟩ ⊒ V′ W′ : q

          (and then induction) [TODO: Check]

      → narrowing (-⊒)

          Let V′ = λx.N′[x].

          σ ⊢ V ⊒ V′ : p̅→q
          --------------------------- -⊒  (s→t)⨾(p′→q′) ≈ p̅→q
          σ ⊢ V ⟨ \dual{s→t} ⟩ ⊒ V′ : p′→q′                            σ ⊢ W ⊒ W′ : p′
          --------------------------------------------------------------------- ·⊒·
          σ ⊢ (V ⟨ \dual{s→t} ⟩) W ⊒ V′ W′ : q′
        ⊢→/=
                              σ ⊢ W ⊒ W′ : p′
                              --------------- -⊒  s⨾p ≈ p′ 
          σ ⊢ V ⊒ V′ : p̅→q    σ ⊢ W ⟨ s ⟩ ⊒ W′ : p
          ---------------------------------------- ·⊒·
          σ ⊢ V (W ⟨ s ⟩) ⊒ V′ W′ : q                   
          -------------------------------- -⊒  t⨾q ≈ q′
          σ ⊢ (V (W ⟨ s ⟩)) ⟨ t̅ ⟩ ⊒ V′ W′ : q′

          (and then induction) [TODO: Check]

    (ΛX.V′[X]) α  ⊢→  V′[α]

      Induct on the derivation of σ ⊢ N ⊒ ΛX.V′[X] : q.

      (⊒Λ)

        σ, α:=★ ⊢ N ⊒ V′[α] : q[α?]
        --------------------------- ⊒Λ
        σ ⊢ N ⊒ ΛX.V′[X] : να.q[α!]
        ---------------------------------- ⊒α
        σ, α:=A ⊢ N ⊒ (ΛX.V′[X]) α : q[α?]
      =/⊢→
        σ, α:=A ⊢ N ⊒ V′[α] : q[α?]

      (Λ⊒Λ)

        σ, X ⊢ V[X] ⊒ V′[X] : q[id_X]
        ----------------------------------- Λ⊒Λ
        σ ⊢ ΛX.V[X] ⊒ ΛX.V′[X] : ∀X.q[id_X]        
        ---------------------------------------- α⊒α where α:=p ∈ σ
        σ ⊢ (ΛX.V[X]) α ⊒ (ΛX.V′[X]) α : q[id_α]
      ⊢→/⊢→
        σ ⊢ V[α] ⊒ V′[α] : q[id_α]

      ∀ widening (+⊒)

        σ ⊢ V ⊒ V′ : ∀X.q[id_X]
        -------------------------------------- +⊒  (∀X.p[id_X])⨾(∀X.q[id_X]) ≈ ∀X.r[id_X]
        σ ⊢ V ⟨ ∀X.p[id_X] ⟩ ⊒ V′ : ∀X.r[id_X]
        -------------------------------------- α⊒α  α:=s ∈ σ
        σ ⊢ (V ⟨ ∀X.p[X] ⟩) α ⊒ V′ α : r[id_α]
      ⊢→/=
        σ ⊢ V ⊒ V′ : ∀X.q[id_X]    
        ------------------------ α⊒α  α:=s ∈ σ
        σ ⊢ V α ⊒ V′ α : q[id_α]
        ----------------------------------- +⊒    p[id_α]⨾q[id_α] ≈ r[id_α]
        σ ⊢ V α ⟨ p[id_α] ⟩ ⊒ V′ α : r[id_α]

      ∀ narrowing (-⊒)

        σ ⊢ V ⊒ V′ : ∀X.r[id_X]
        --------------------------------------- -⊒  (∀X.p[id_X])⨾(∀X.q[id_X]) ≈ ∀X.r[id_X]
        σ ⊢ V ⟨ \dual{∀X.p[id_X]} ⟩ ⊒ V′ : ∀X.q[id_X]
        --------------------------------------- α⊒α  α:=s ∈ σ
        σ ⊢ (V ⟨ \dual{∀X.p[id_X]} ⟩) α ⊒ V′ α : q[α]
      ⊢→/=
        σ ⊢ V ⊒ V′ : ∀X.r[id_X]    
        ------------------------ α⊒α  α:=s ∈ σ
        σ ⊢ V α ⊒ V′ α : r[id_α]
        ----------------------------------- -⊒    p[id_α]⨾q[id_α] ≈ r[id_α]
        σ ⊢ V α ⟨ p̅[id_α] ⟩ ⊒ V′ α : q[id_α]

      ν Narrowing (-⊒)

        σ, α:=★ ⊢ N ⊒ V′[α] : r[α?]
        ----------------------------- ⊒Λ
        σ ⊢ N ⊒ (ΛX.V′[X]) : να.r[α!]
        ------------------------------------------------- -⊒ (i)
        σ ⊢ N ⟨ \dual{να.q[α♯]} ⟩ ⊒ (ΛX.V′[X]) : ∀X.p[id_X]
        ---------------------------------------------------------- α⊒α
        σ, α:=s ⊢ (N ⟨ \dual{να.q[α♯]} ⟩) α ⊒ (ΛX.V′[X]) α : p[id_α]
        (i)  (∀X.p[id_X])⨾(να.q[α!]) ≈ να.r[α!]
      =/⊢→
        σ, α:=s ⊢ (N ⟨ \dual{να.q[α♯]} ⟩) α ⊒ V′[α] : p[id_α]
      —↠_{Π^★}/=  (Catchup Lemma)
        σ, α:=s, Π^☆ ⊢ (V ⟨ \dual{να.q[α♯]} ⟩) α ⊒ V′[α] : p[id_α]
      —→_{α:=★}/=
        σ, α:=★ ⊢ V ⊒ V′[α] : r[α?]
        --------------------------------------- -⊒ (ii)
        σ, α:=s ⊢ V ⟨ q̅[α!] ⟩ ⊒ V′[α] : p[id_α]
        (ii)  p[id_α]⨾q[α!] ≈ r[α!]

        [See Example 0]

    V′ ⟨ id_a ⟩  ⊢→  V′

        σ ⊢ M ⊒ V′ : p    id_a : a ⊒ a
        -----------------------------
        σ ⊢ M ⊒ V′ ⟨ id_a ⟩ : p
      =/⊢→
        σ ⊢ M ⊒ V′ : p

    (V′ ⟨ s→t̅ ⟩) W′  ⊢→  V′ (W′ ⟨ s ⟩) ⟨ t̅ ⟩

        σ ⊢ L ⊒ V′ : s̅₂→t₂
        --------------------------- ⊒+  (s̅₂→t₂) ≈ (s̅₁→t₁)⨾(s→t̅)
        σ ⊢ L ⊒ (V′ ⟨ s→t̅ ⟩) : s̅₁→t₁                                σ ⊢ M ⊒ W′ : s₁
        ------------------------------------------------------------------------- ·⊒·
        σ ⊢ L M ⊒ (V′ ⟨ s→t̅ ⟩) W′ : t₁
      =/⊢→
                             M ⊒ W′ : s₁
                             ---------------- ⊒-  s₂ ≈ s₁⨾s  (follows from  s̅₁⨾s̅ ⊒ s̅₂)
        σ ⊢ L ⊒ V′ : s̅₂→t₂    M ⊒ W′ ⟨ s ⟩ : s₂              
        ------------------------------------- ·⊒·
        σ ⊢ L M ⊒ (V′ (W′ ⟨ s ⟩)) : t₂
        -------------------------------- ⊒+  t₂ ≈ t₁⨾t
        σ ⊢ L M ⊒ (V′ (W′ ⟨ s ⟩)) ⟨ t̅ ⟩ : t₁

       [TODO: Do I need Wrap Widening Lemma?]

    (V′ ⟨ s̅→t ⟩) W′  ⊢→  V′ (W′ ⟨ s̅ ⟩) ⟨ t ⟩

        Wrap narrowing lemma.

    (V′ ⟨ ∀X.p[X] ⟩) α  ⊢→  V′ α ⟨ p[α] ⟩

        There are three possible derivations.

      (i)
        σ ⊢ L ⊒ V′ : να.r[α]
        --------------------------------- ⊒+    να.r[α] ≈ (να.q[α])⨾(∀X.p[X])
        σ ⊢ L ⊒ (V′ ⟨ ∀X.p[X] ⟩) : να.q[α]
        --------------------------------- ⊒α    α:=A ∈ σ
        σ ⊢ L ⊒ (V′ ⟨ ∀X.p[X] ⟩) α : q[α]
      =/⊢→
        σ ⊢ L ⊒ V′ : να.r[α]
        ------------------- ⊒α    α:=A ∈ σ
        σ ⊢ L ⊒ V′ α : r[α]
        -------------------------- ⊒+    r[α] ≈ q[α]⨾p[α]
        σ ⊢ L ⊒ V′ α ⟨ p[α] ⟩ : q[α]

      (ii)
        ρ ⊢ L ⊒ V′ : ∀X.r[X]
        --------------------------------- ⊒+    ∀X.r[X] ≈ (∀X.q[X])⨾(∀X.p[X])
        ρ ⊢ L ⊒ (V′ ⟨ ∀X.p[X] ⟩) : ∀X.q[X]
        ---------------------------------- α⊒α    α:=s ∈ ρ
        ρ ⊢ L α ⊒ (V′ ⟨ ∀X.p[X] ⟩) α : q[α]
      =/⊢→
        ρ ⊢ L ⊒ V′ : ∀X.r[X]
        -------------------- α⊒α    α:=s ∈ ρ
        ρ ⊢ L α ⊒ V′ α : r[α]
        ----------------------------- ⊒+    r[α] ≈ q[α]⨾p[α]
        ρ ⊢ L α ⊒ V′ α ⟨ p[α] ⟩ : q[α]

        (or handle widening or narrowing on left)

    (V′ ⟨ \dual{∀X.p[X]} ⟩) α  ⊢→  V′ α ⟨ p̅[α] ⟩

        similar to previous case

    V′ ⟨ ν̅α.p[α♯] ⟩  ⊢→  να:=★.(V′ α ⟨ p[α♯] ⟩)

                                       p[α♯] : B =⇒ A[α]
                                       ----------------
         σ ⊢ L ⊒ V′ : (να.r[α!])    ν̅α.p[α♯] : B =⇒ ∀X.A[X]
         ------------------------------------------------ ⊒+ (i)
         σ ⊢ L ⊒ V′ ⟨ ν̅α.p[α♯] ⟩ : q
         (i)  q⨾(να.p[α!]) ≈ (να.r[α!])
       ⊢→
         σ, α:=★ ⊢ L ⊒ V′ : (να.r[α!])       
         -------------------------------- ⊒α    
         σ, α:=★ ⊢ L ⊒ V′ α : r[α?]          p[α♯] : B =⇒ A[α]
         --------------------------------------------------- ⊒+ (ii)
         σ, α:=★ ⊢ L ⊒ (V′ α ⟨ p[α♯] ⟩) : q
         --------------------------------- ⊒ν
         σ ⊢ L ⊒ να:=★.(V′ α ⟨ p[α♯] ⟩) : q
         (ii)  q⨾p[α!] ≈ r[α?]

    (V′ ⟨ \dual{να.p[α♯]} ⟩) α  ⊢→  V′ ⟨ p̅[α!] ⟩

         σ ⊢ L ⊒ V′ : q
         ------------------------------------------ +⊒ (i)
         σ ⊢ L ⟨ \dual{να.p[α♯]} ⟩ ⊒ V′ : (να.r[α!])
         ------------------------------------------ ⊒α    α:=A ∈ σ
         σ ⊢ (L ⟨ \dual{να.p[α♯]} ⟩) α ⊒ V′ : r[α?]
         (i)  (να.p[α!])⨾q ≈ να.r[α!]
       =/⊢→
         σ ⊢ L ⊒ V′ : q
         --------------------------- +⊒ (ii)
         σ ⊢ L ⟨ p̅[α!] ⟩ ⊒ V′ : r[α?]
         (ii)  p[α!]⨾q ≈ r[α?]

         (There could be left widening or narrowing between ⊒α and +⊒.
         In that case, we can push it underneath the ⊒α.)

    V′ ⟨ s;t ⟩  ⊢→  V′ ⟨ s ⟩ ⟨ t ⟩

         σ ⊢ M ⊒ V′ ⟨ s;t ⟩ : p
       =/⊢→
         σ ⊢ M ⊒ V′ ⟨ s ⟩ ⟨ t ⟩ : p

         Easy to show σ ⊢ M ⊒ V′ ⟨ s;t ⟩ : p
         implies σ ⊢ M ⊒ V′ ⟨ s ⟩ ⟨ t ⟩ : p.

    V′ ⟨ G! ⟩ ⟨ G? ⟩  ⊢→  V′

         σ ⊢ M ⊒ V′ ⟨ G! ⟩ ⟨ G? ⟩ : G?
       =/⊢→
         σ ⊢ M ⊒ V′ : G?

       By Right Tag Inversion 1 and 2.

    V′ ⟨ G! ⟩ ⟨ H? ⟩  ⊢→  blame,  G ≠ H

         σ ⊢ M ⊒ V′ ⟨ G! ⟩ ⟨ H? ⟩ : p
       =/⊢→
         σ ⊢ M ⊒ blame : p

         Immediate.

    V′ ⟨ α♯ ⟩ ⟨ α♭ ⟩  ⊢→  V′

        σ ⊢ M ⊒ V′ ⟨ α♯ ⟩ ⟨ α♭ ⟩ : p
      =/⊢→
        σ ⊢ M ⊒ V′ : p

         Easy to show σ ⊢ M ⊒ V′ ⟨ α♯ ⟩ ⟨ α♭ ⟩ : p
         implies σ ⊢ M ⊒ V′ : p.

    (να:=A.N′[α]) —→_{α:=A} N′[α]

        σ, α:=p ⊢ N[α] ⊒ N′[α]
        --------------------------------- ν⊒ν
        σ ⊢ (να:=A.N[α]) ⊒ (να:=A′.N′[α])
      —→_{α:=A}/—→_{α:=A′}
        σ, α:=p ⊢ N[α] ⊒ N′[α]
      
        σ, α:=☆ ⊢ N[α] ⊒ N′ : p
        ----------------------- ν⊒  α ∉ fv(p)
        σ ⊢ να:=★.N[α] ⊒ N′ : p
      =/—→_{α:=A}
        σ, α:=☆ ⊢ N[α] ⊒ N′ : p

------------------------------------------------------------------------
RELATED WORK
------------------------------------------------------------------------

* Ahmed, Jamner, Siek, and Wadler (ICFP 2017)
  Theorems for free for free: parametricity, with and without types.
  supports using casts to instantiate and generalise
  uses compatibility

* Igarashi, Sekiyama & Igarashi (ICFP 2017)
  On Polymorphic Gradual Typing.
  supports using casts to instantiate and generalise
  uses compatibility
  two kinds of type variable (but also two types of quantification)

* Castagna, Lanvin, Petrucciani, and Siek (POPL 2019)
  Gradual Typing: A New Perspective.
  show that we can get rid of ~ ≤ ≤⁺ ≤⁻, and just keep ⊑
  replaces compatibility by imprecision

* New, Jamner & Ahmed (POPL 2020)
  Graduality and Parametricity: Together Again for the First Time.
  source of our title
  odd syntax with user-written seals: "throws the baby out with the bathwater"
  doesn't support using casts to instantiate and generalise
  replaces compatibility by imprecision
  has ∀X.★ as a ground type

* Toro, Labrada & Tanter (POPL 2019) Gradual Parametricity, Revisited;
  Labrada, Toro & Tanter (JACM 2022) Gradual System F.
  introduces "strict" imprecision, but mixes it with ordinary imprecision.
  doesn't support using casts to instantiate and generalise
  uses compatibility
  has ∀X.★ as a ground type

* Devriese, Patrignani & Piessens (POPL 2018, TOPLAS 2022)
  Two Parametricities Versus Three Universal Types.
  Consider the type,
    ∃X.∀Y.(Y→X, X→Y)
  which makes X a Universal Type.

  Observe that System F lacks a universal type but that Ahmed, Jamner,
  Siek & Wadler (ICFP 2017) permit a universal type, and hence full
  abstraction cannot hold when mapping System F to λB.  Make similar
  observations for mapping System F into the cryptographic lambda calculus
  of Pierce and Sumii (2000), or into System G of Neis, Dreyer, and Rossberg
  (ICFP 2009). They also note that System F is modeled with a Reynolds
  Logical Relation (RLR), whereas the other systems are modeled with a
  Type World Logical Relation (TWLR).  However, in our system the
  universal type *is* empty, meaning (a) perhaps full abstraction
  holds, (b) perhaps we can use a Kripke Logical Relation rather than
  a Type World Logical Relation.
  
* Arjun Guha, Jacob Matthews, Robert Bruce Findler, and Shriram
  Krishnamurthi. Relationally-parametric polymorphic contracts.
  In Dynamic Languages Symposium (DLS), pages 29–40, 2007.

* Jeremy G. Siek and Walid Taha. Gradual typing for functional
  languages. In Scheme and Functional Programming Workshop
  (Scheme), pages 81–92, September 2006.

------------------------------------------------------------------------


APPENDIX: EXTRA MATERIAL
~~~~~~~~~~~~~~~~~~~~~~~~

The following appear not to be needed-t̅̅he simulation proof does not
reference them, even though similar results appear in Siek et al
(2015).


Left upcast inversion
~~~~~~~~~~~~~~~~~~~~~

(Convention. p, q, r range over casts, s, t over imprecisions.)


If γ ⊢ M ⟨ s ⟩ ⊑ N : q and s ⨾ q ≈ r then γ ⊢ M ⊑ N : r.

Proof by induction on the derivation of σ ⊢ M ⟨ s ⟩ ⊑ N : q.

  (+⊑)
      γ ⊢ M ⊑ N : r
      ------------------ +⊑    s ⨾ q ≈ r
      γ ⊢ M ⟨ s ⟩ ⊑ N : q

      (trivial)

  (⊑+)  N = N′ ⟨ t ⟩

      γ ⊢ M ⊑ N′ : p
      -------------------- +⊑        s ⨾ r′ ≈ p  (i)  (induction -- see below)
      γ ⊢ M ⟨ s ⟩ ⊑ N′ : r′
      ------------------------ ⊑+    q ≈ r′ ⨾ t  (ii)
      γ ⊢ M ⟨ s ⟩ ⊑ N′ ⟨ t ⟩ : q
    =>
      γ ⊢ M ⊑ M′ : p    
      ------------------- ⊑+         r ≈ p ⨾ t   (iii)
      γ ⊢ M ⊑ M′ ⟨ t ⟩ : r
      ------------------------ +⊑    s ⨾ q ≈ r   (iv)
      γ ⊢ M ⟨ s ⟩ ⊑ M′ ⟨ t ⟩ : q

    Then (iv) is given and (iii) holds because:

        r
      ≈ {(iv)}
        s ⨾ q
      ≈ {(ii)}
        s ⨾ r′ ⨾ t
      ≈ {(i)}
        p ⨾ t

    TODO: For the induction step, we need to show there is a p such
    that s ⨾ r′ ≈ p.  Possibly we need a lemma: if s ⨾ q ≈ r and
    q ≈ r′ ⨾ t then there is a p such that s ⨾ r′ ≈ p.

  (⊑-)  N = N′ ⟨ t̅ ⟩
  
      γ ⊢ M ⊑ N′ : p
      -------------------- +⊑        s ⨾ r′ ≈ p  (i)  (induction -- see below)
      γ ⊢ M ⟨ s ⟩ ⊑ N′ : r′
      ------------------------ ⊑-    r′ ≈ q ⨾ t  (ii)
      γ ⊢ M ⟨ s ⟩ ⊑ N′ ⟨ t̅ ⟩ : q
    =>
      γ ⊢ M ⊑ N′ : p    
      ------------------- ⊑-         p ≈ r ⨾ t   (iii)
      γ ⊢ M ⊑ N′ ⟨ t̅ ⟩ : r
      ------------------------ +⊑    s ⨾ q ≈ r   (iv)
      γ ⊢ M ⟨ s ⟩ ⊑ N′ ⟨ t̅ ⟩ : q

    Then (iv) is given, and (iii) holds because

        p
      ≈ (i)
        s ⨾ r′
      ≈ (ii)
        s ⨾ q ⨾ t
      ≈ (iv)
        r ⨾ t

    TODO: For the induction step, we need to show there is a p such
    that s ⨾ r′ ≈ p.  Possibly we need a lemma: if s ⨾ q ≈ r and
    r′ ≈ q ⨾ t then there is a p such that s ⨾ r′ ≈ p.


Left downcast inversion
~~~~~~~~~~~~~~~~~~~~~~~

If γ ⊢ M ⟨ s̅ ⟩ ⊑ N : r and s ⨾ q = r then γ ⊢ M ⊑ N : q.

Proof by induction on the derivation of γ ⊢ M ⟨ s̅ ⟩ ⊑ N : r.

  (-⊑)
      γ ⊢ M ⊑ N : q
      ------------------- -⊑    s ⨾ q = r
      γ ⊢ M ⟨ s̅ ⟩ ⊑ N : r

      (trivial)

  (⊑-)   N = N′ ⟨ t̅ ⟩

      γ ⊢ M ⊑ N′ : p
      -------------------- -⊑        s ⨾ p ≈ q′  (i)  (induction -- see below)
      γ ⊢ M ⟨ s̅ ⟩ ⊑ N′ : q′
      ------------------------ ⊑-    q′ ≈ r ⨾ t  (ii)
      γ ⊢ M ⟨ s̅ ⟩ ⊑ N′ ⟨ t̅ ⟩ : r
    =>
      γ ⊢ M ⊑ M′ : p    
      ------------------- ⊑-         p ≈ q ⨾ t   (iii)
      γ ⊢ M ⊑ M′ ⟨ t̅ ⟩ : q
      ------------------------ -⊑    s ⨾ q ≈ r   (iv)
      γ ⊢ M ⟨ s̅ ⟩ ⊑ M′ ⟨ t̅ ⟩ : r

    Then (iv) is given and (iii) holds because

      s ⨾ p
    ≈ (i)
      q′
    ≈ (ii)
      r ⨾ t
    ≈ (iv)
      s ⨾ q ⨾ t

    From which we can conclude p ≈ q ⨾ t.

    TODO: For the induction step we need to show there is a p such
    that s ⨾ p ≈ q′. Possibly we need a lemma: if s ⨾ q ≈ r and
    q′ ≈ r ⨾ t then there is a p such that s ⨾ p ≈ q′.

  (⊑+)  N = N′ ⟨ t ⟩
    
      γ ⊢ M ⊑ N′ : p
      -------------------- -⊑        s ⨾ p ≈ q′  (i)  (induction -- see below)
      γ ⊢ M ⟨ s̅ ⟩ ⊑ N′ : q′
      ------------------------ ⊑+    r ≈ q′ ⨾ t  (ii)
      γ ⊢ M ⟨ s̅ ⟩ ⊑ N′ ⟨ t ⟩ : r
    =>
      γ ⊢ M ⊑ M′ : p    
      ------------------- ⊑+         q ≈ p ⨾ t   (iii)
      γ ⊢ M ⊑ M′ ⟨ t ⟩ : q
      ------------------------ -⊑    s ⨾ q ≈ r   (iv)
      γ ⊢ M ⟨ s̅ ⟩ ⊑ M′ ⟨ t ⟩ : r

    Then (iv) is given and (iii) holds because

      s ⨾ q
    ≈ (iv)
      r
    ≈ (ii)
      q′ ⨾ t
    ≈ (i)
      s ⨾ p ⨾ t

    From which we can conclude q ≈ p ⨾ t.

    TODO: For the induction step we need to show there is a p such
    that s ⨾ p ≈ q′. Possibly we need a lemma: if s ⨾ q ≈ r and
    r ≈ q′ ⨾ t then there is a p such that s ⨾ p ≈ q′.


Right Upcast Inversion
~~~~~~~~~~~~~~~~~~~~~~

If σ ⊢ V ⊑ V′ ⟨ q ⟩ : (p ⨾ q) then σ ⊢ V ⊑ V′ : p.

Proof by induction on the derivation of σ ⊢ V ⊑ V′ ⟨ q ⟩ : (p ⨾ q).

  (⊑+)
      σ ⊢ V ⊑ V′ : p    q : A ⊑ B
      --------------------------- ⊑+
      σ ⊢ V ⊑ V′ ⟨ q ⟩ : (p ⨾ q)

      Immediate.

  (+⊑)
      σ ⊢ V ⊑ V′ : (s ⨾ t)
      ----------------------------- ⊑+
      σ ⊢ V ⊑ V′ ⟨ q ⟩ : (s ⨾ t ⨾ q)
      ------------------------------ +⊑
      σ ⊢ V ⟨ s ⟩ ⊑ V′ ⟨ q ⟩ : (t ⨾ q)
    =>
      σ ⊢ V ⊑ V′ : (s ⨾ t)
      -------------------- +⊑
      σ ⊢ V ⟨ s ⟩ ⊑ V′ : t
      ------------------------------ ⊑+
      σ ⊢ V ⟨ s ⟩ ⊑ V′ ⟨ q ⟩ : (t ⨾ q)

  (-⊑)
      σ ⊢ V ⊑ V′ : t
      ------------------------- ⊑+
      σ ⊢ V ⊑ V′ ⟨ q ⟩ : (t ⨾ q)
      ---------------------------------- -⊑
      σ ⊢ V ⟨ s̅ ⟩ ⊑ V′ ⟨ q ⟩ : (s ⨾ t ⨾ q)
    =>
      σ ⊢ V ⊑ V′ : t
      ------------------------- -⊑
      σ ⊢ V ⟨ s̅ ⟩ ⊑ V′ : (s ⨾ t)
      ---------------------------------- ⊑+
      σ ⊢ V ⟨ s̅ ⟩ ⊑ V′ ⟨ q ⟩ : (s ⨾ t ⨾ q)

  (Λ⊑)
      σ, α:=★ ⊢ V[α] ⊑ V′ : p[α]
      ------------------------------------- ⊑+
      σ, α:=★ ⊢ V[α] ⊑ V′ ⟨ q ⟩ : (p[α] ⨾ q)
      ------------------------------------- Λ⊑
      σ ⊢ ΛX.V[X] ⊑ V′ ⟨ q ⟩ : να.(p[α] ⨾ q)
    =>
      σ, α:=★ ⊢ V[α] ⊑ V′ : p[α]
      -------------------------- Λ⊑
      σ ⊢ ΛX.V[α] ⊑ V′ : να.p[α]
      ------------------------------------- ⊑+
      σ ⊢ ΛX.V[X] ⊑ V′ ⟨ q ⟩ : να.(p[α] ⨾ q)

  [TODO: Check]


## Simulation of function application

  (Lemma 10 of Refined Criteria)
  If σ ⊢ (λx.N[x]) ⊑ V′ : p→q and σ ⊢ W ⊑ W′ : p and σ : Σ ⊑ Σ′
  then Σ′ ⊢ V′ W′ ⊢↠ Π′ ⊢ N′ and π ⊢ N[W] ⊑ N′: q and π : Σ ⊑ Π′.

  Proof by induction on the derivation of σ ⊢ (λx.N[x]) ⊑ V′ : p→q.
  The only possibility for V′ is that it is a lambda term or a function
  cast.

    Lambda term

          σ, x:p ⊢ N[x] ⊑ N′[x] : q
          ----------------------------
          σ ⊢ λx.N[x] ⊑ λx.N′[x] : p→q    σ ⊢ W ⊑ W′ : p
          ----------------------------------------------
          σ ⊢ (λx.N[x]) W ⊑ (λx.N′[x]) W′ : q
        —→
          σ ⊢ N[W] ⊑ N′[W′] : q

          (assumes a suitable substitution lemma)

     Function upcast

          σ ⊢ V ⊑ V′ : p′→q′
          ------------------------- ⊑+    (s→t)⨾(p→q) = p′→q′
          σ ⊢ V ⊑ V′ ⟨ s→t ⟩ : p→q                              σ ⊢ W ⊑ W′ : p
          -------------------------------------------------------------------- ·⊑·
          σ ⊢ V W ⊑ (V′ ⟨ s→t ⟩) W′ : q
        —→
                                σ ⊢ W ⊑ W′ : p
                                -------------- ⊑-    s⨾p = p′
          σ ⊢ V ⊑ V′ : p′→q′    σ ⊢ W ⊑ W′ ⟨ s̅ ⟩ : p′
          ------------------------------------------ ·⊑·
          σ ⊢ V W ⊑ V′ (W′ ⟨ s̅ ⟩) : q′                   
          -------------------------------- ⊑+    t⨾q = q′
          σ ⊢ V W ⊑ V′ (W′ ⟨ s̅ ⟩) ⟨ t ⟩ : q

        By induction, we then have V = λx.N[x], V′ (W′ ⟨ s̅ ⟩) ⊢↠ N′ and σ ⊢ N[V] ⊑ N′ : q′,
        whence σ ⊢ N[V] ⊑ N′ ⟨ t ⟩ : q

      Function downcast. (Similar.)


Simulation of type application (∀)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If σ : Σ ⊑ Σ′ and σ ⊢ (ΛX.V[X]) ⊑ V′ : ∀X.p[X]
then Σ′ ⊢ V′ α —↠ Π′ ⊢ N′ and π : Σ ⊑ Π′ and π ⊢ V[α] ⊑ N′: p[α].

Proof by induction on the derivation of σ ⊢ (ΛX.V[X]) ⊑ V′ : ∀X.p[X].

The only possibility for V′ is that it is a big lambda term or a
∀ or ν̅ cast.


  Big Lambda


  ∀ Upcast
                            
        σ ⊢ V ⊑ V′ : ∀X.r[X]
        -------------------------------- ⊑+    (∀X.p[X])⨾(∀X.q[X]) = ∀X.r[X]
        σ ⊢ V ⊑ V′ ⟨ ∀X.p[X] ⟩ : ∀X.q[X]
        ----------------------------------- α⊑α    α:=s ∈ σ
        σ ⊢ V α ⊑ (V′ ⟨ ∀X.p[X] ⟩) α : q[α]
      ⊢→
        σ ⊢ V ⊑ V′ : ∀X.r[X]    
        --------------------- α⊑α    α:=s ∈ σ
        σ ⊢ V α ⊑ V′ α : r[α]
        ----------------------------- ⊑+    p[X]⨾q[X] = r[X]
        σ ⊢ V α ⊑ V′ α ⟨ p[α] ⟩ : q[α]

  ∀ Downcast (similar)

  ν Downcast

        σ, α:=★ ⊢ V[α] ⊑ V′ : r[α]
        ---------------------------- Λ⊑
        σ ⊢ (ΛX.V[X]) ⊑ V′ : να.r[α]
        ----------------------------------------- ⊑-    (∀X.p[X])⨾(να.q[α]) = να.r[α]
        σ ⊢ (ΛX.V[X]) ⊑ V′ ⟨ \dual{να.q[α]} ⟩ : ∀X.p[X]
        -------------------------------------------------- α⊑α
        σ, α:=s ⊢ (ΛX.V[X]) α ⊑ (V′ ⟨ \dual{να.q[α]} ⟩) α : p[α]
      ⊢→
        σ, α:=★ ⊢ V[α] ⊑ V′ : r[α]
        ---------------------------------------- ⊑-    p[α]; q[α♯:=α!] = r[α]
        σ, α:=s ⊢ V[α] ⊑ V′ ⟨ q̅[α♯:=α!] ⟩ : p[α]


Simulation of unwrap
~~~~~~~~~~~~~~~~~~~~

(Lemma 11 of Refined Criteria)
If σ ⊢ V @ (p̅→q) ⊑ V′ : s̅→t and σ ⊢ W ⊑ W′ : s
then V′ W′ ⊢↠ N′ and σ ⊢ V (W ⟨ p̅ ⟩) ⟨ q ⟩ ⊑ N′: t.

Proof.  See the cases

    (V ⟨ s̅→t ⟩) W  ⊢→  V (W ⟨ s̅ ⟩) ⟨ t ⟩
    (V ⟨ s→t̅ ⟩) W  ⊢→  V (W ⟨ s ⟩) ⟨ t̅ ⟩

in the proof of the Gradual Guarantee above.

========================================================================
Notes on Siek and Chen (2021) and Siek et al (2015)

Simulation.

    σ ⊢ M ⊑ M′ : p
  —→/—↠
    π ⊢ N ⊑ N′ : p

Cast Catchup.

    σ ⊢ V ⊑ V′ : p
    ------------------- ⊑+  r ≈ p ⨾ t
    σ ⊢ V ⊑ V′ ⟨ t ⟩ : r
  =/—↠
    π ⊢ V ⊑ W : r

    σ ⊢ V ⊑ V′ : r
    ------------------- ⊑-  r ≈ p ⨾ t
    σ ⊢ V ⊑ V′ ⟨ t̅ ⟩ : p
  =/—↠
    π ⊢ V ⊑ W : p

Catchup.

    σ ⊢ V ⊑ M : p
  =/—↠
    π ⊢ V ⊑ W : p

Sim-cast.

    σ ⊢ V ⊑ V′ : p
    ------------------------ +⊑  s ⨾ q ≈ p ⨾ t
    σ ⊢ V ⟨ s ⟩ ⊑ V′ ⟨ t ⟩ : q
  —→/—↠
    σ ⊢ M ⊑ M′ : r

    σ ⊢ V ⊑ V′ : q
    ------------------------ +⊑  s ⨾ q ≈ p ⨾ t
    σ ⊢ V ⟨ s̅ ⟩ ⊑ V′ ⟨ t̅ ⟩ : p
  —→/—↠
    σ ⊢ M ⊑ M′ : r

Simulation of Function Application (Siek et al 2015, Lemma 10).

    σ ⊢ (λx.N[x]) ⊑ V′ : p→q    σ : W ⊑ W′ : p
    ------------------------------------------ ·⊑·
    σ ⊢ (λx.N[x]) W ⊑ V′ W′ : q
  —→/—↠
    π ⊢ N[W] ⊑ N′ : q

Simulation of Unwrapping (Siek et al 2015, Lemma 11).

    (p→q) ≈ (s→t) ⨾ (p′→q′)

    σ ⊢ V ⊑ V′ : p→q
    --------------------------- +⊑
    σ ⊢ V ⟨ s→t ⟩ ⊑ V′ : p′→q′       σ ⊢ W ⊑ W′ : p′
    ------------------------------------------------ ·⊑·
    σ ⊢ (V ⟨ s→t ⟩) W ⊑ V′ W′ : q′
  —→/—↠
    π ⊢ V (W ⟨ s̅ ⟩) ⟨ t ⟩ ⊑ N : q′
