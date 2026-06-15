Graduality, Parametricity, Interoperability:
Together Again for the First Time
(version 22)

8 June 2026

Jeremy Siek, Indiana University
Peter Thiemann, University of Freiburg
Philip Wadler, Input Output

------------------------------------------------------------------------
New in this version:
cambridge20 casts relate terms, *except* upcasts and downcasts use full imprecision.
cambridge21 has full draft proof, including ν upcast lemma.
cambridge22 based on arbitrary casts (not up or down), plus widening and narrowing
------------------------------------------------------------------------
TODO: All instances of seals should be erasable at runtime.
How do the imprecision rules look under the influence of erasure?
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
  Γ ⊢ A    GType(χ,A)    QPoly(B′)    X ∉ ftv(B′)
  -----------------------------------------------
  Γ ⊢ f A : B[X:=Γ(A)] ⊑_χ Γ′ ⊢ f′ : B′

  Γ, X::L ⊢ w[X] : A[X] ⊑_{χ,X::𝒮} Γ′ ⊢ w′ : A′
  QPoly(A′)    X ∉ fvt(A′)
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

      (1) a ∉ dom(Σ) guarantees we don't have both id_α and (seal_α;p)
          in the same imprecision judgement.

      (2) G ∉ dom(Σ) guarantees we don't have both (id_α;tag_α) and
          (seal_α;p) in the same imprecision judgement.

But I’m having trouble seeing how these invariants are maintained by
type variable substitution.

Suppose we are substituting X for α in an imprecision (e.g., triggered
by the application of a type abstraction), but the imprecision already
has seal_α inside. The substitution will turn id_X into id_α and then
the above invariant will be violated.

Here’s a small albeit contrived example:

να:=ℕ. (((ΛX. (λx:X. 0) @ −(id_X → seal_α)) α) @ +(seal_α → seal_α))
-->
να:=ℕ. (((λx:α. 0) @ −(id_α → seal_α)) @ +(seal_α → seal_α))


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
good---so perhaps stick with that!]

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
    id′  =  ΛX.λx:X.(id★ @ -(να.seal_α→seal_α)) X x
         =  ΛX.λx:X.να:=X. ((id★ @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) x

But it can also be done with explicit tagging and sealing:

    id″ = ΛX.λx:X.να:=X. (id★ @ -(tag_α→tag_α) @ +(seal_α→seal_α))

This is actually just one reduction step applied to the previous,
so I guess that the previous is better style and easier to use.

========================================================================
EXAMPLES
========================================================================

[K example shows why we need α]

Example 1.

       ------------------------------- x⊒x
       α:=★, x:-tag_α ⊢ x ⊒ x : -tag_α
       ------------------------------------------- λ⊒λ
       α:=★ ⊢ (λx:★.x) ⊒ (λx:α.x) : (tag_α→-tag_α)
       --------------------------------------------- Λ⊒
       ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) : (να.tag_α→-tag_α)
       ------------------------------------------------------------- -⊒ (i)
       ⊢ (λx:★.x) ⟨ να.tag_α→-tag_α ⟩ ⊒ (ΛX.λx:X.x) : (∀X.id_X→id_X)
       -------------------------------------------------------------------------------------- +⊒ (ii)
       ⊢ (λx:★.x) ⟨ να.tag_α→-tag_α ⟩ ⟨ -να.seal_α→-seal_α ⟩ ⊒ (ΛX.λx:X.x) : (να.tag_α→tag_α)

       (i)     (να.tag_α→-tag_α) = (να.tag_α→-tag_α) ⨾ (∀X.id_X→id_X)
       (ii)    (να.tag_α→-tag_α) = -(-να.seal_α→-seal_α) ⨾ (∀X.id_X→id_X)  

               where  -(-να.seal_α→-seal_α) = (να.tag_α→-tag_α)

     —→
       ⊢ να:=★. (λx:★.x) ⟨ να.tag_α→-tag_α ⟩ α ⟨ seal_α→-seal_α ⟩ ⊒ (ΛX.λx:X.x) : (να.tag_α→-tag_α)
     —→
       α:=☆ ⊢ (λx:★.x) ⟨ να.tag_α→-tag_α ⟩ α ⟨ seal_α→-seal_α ⟩ ⊒ (ΛX.λx:X.x) : (να.tag_α→-tag_α)
     —→
       ---------------------------------- x⊒x
       α:=id_★, x:-tag_α ⊢ x ⊒ x : -tag_α
       ----------------------------------------------  λ⊒λ
       α:=id_★ ⊢ (λx:★.x) ⊒ (λx:α.x) : (tag_α→-tag_α)    
       ---------------------------------------------------------------- -⊒ (iii)
       α:=id_★ ⊢ (λx:★.x) ⟨ tag_α→-tag_α ⟩ ⊒ (λx:α.x) : (id_α→id_α)    
       ----------------------------------------------------------------------------------  +⊒ (iv)
       α:=id_★ ⊢ (λx:★.x) ⟨ tag_α→-tag_α ⟩ ⟨ seal_α→-seal_α ⟩ ⊒ (λx:α.x) : (tag_α→-tag_α)    
       -------------------------------------------------------------------------------------- ⊒Λ
       α:=☆ ⊢ (λx:★.x) ⟨ tag_α→-tag_α ⟩ ⟨ seal_α→-seal_α ⟩ ⊒ (ΛX.λx:X.x) : (να.tag_α→-tag_α)

       (iii)   (tag_α→-tag_α) = (tag_α→-tag_α) ⨾ (id_α→id_α)
       (iv)    (tag_α→-tag_α) = -(seal_α→seal_α) ⨾ (id_α→id_α)

               where -(seal_α→seal_α) = (tag_α→-tag_α)


Example 2.

      ⊢ (λx:★.x) ⊑ (λx:★.x) : (id_★→id_★)
      ---------------------------------------------------------------------------------- -⊑- (ii)
      ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (λx:★.x) @ -(να.seal_α→seal_α) : (∀X.id_X→id_X)
      ------------------------------------------------------------------------------------------------------------ ⊑+ (i)
      ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (λx:★.x) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)

      (i)    (να.seal_α→seal_α) ≈ (∀X.id_X→id_X) ⨾ (να.seal_α→seal_α)
      (ii)   (να.seal_α→seal_α) ⨾ (id_★→id_★) ≈ (∀X.id_X→id_X) ⨾ (να.seal_α→seal_α)

    —↠
      ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (να:=★. (λx:★.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : (να.seal_α→seal_α)
    —↠
      α:=☆ ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ ((λx:★.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : (να.seal_α→seal_α)
    —↠
      α:=id_★ ⊢ (λx:★.x) @ -(tag_α→tag_α) ⊑ (λx:★.x) @ -(tag_α→tag_α) : (id_α→id_α)
      ---------------------------------------------------------------------------------------------------- ⊑+  (iii)
      α:=id_★ ⊢ (λx:★.x) @ -(tag_α→tag_α) ⊑ (λx:★.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : (tag_α→tag_α)
      ---------------------------------------------------------------------------------------------------------- Λ⊑ generalised
      α:=☆ ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (λx:★.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : (να.seal_α→seal_α)

      (iii)  (tag_α→tag_α) ≈ (id_α→id_α) ⨾ (seal_α→seal_α)


Example 3.

      ⊢ (ΛX.λx:X.x) ⊑ (λx:⋆.x) : (να.seal_α→seal_α)
      -------------------------------------------------- α⊑
      α:=ι ⊢ (ΛX.λx:X.x) α ⊑ (λx:⋆.x) : tag_α→tag_α
      ---------------------------------------------------------------- +⊑ (i)
      α:=ι ⊢ (ΛX.λx:X.x) α @ +(seal_α→seal_α) ⊑ (λx:⋆.x) : tag_ι→tag_ι

      (i)  (seal_α→seal_α) ⨾ (tag_ι→tag_ι) ≈ tag_α→tag_α


Example 4.

      ∅ ⊢ (ΛX.λx:X.x) ⊑ (ΛX.λx:X.x) @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)
    —→
      ∅ ⊢ (ΛX.λx:X.x) ⊑ να:=★.(ΛX.λx:X.x) α @ +(seal_α→seal_α) : (να.seal_α→seal_α)
    —→
      α:=☆ ⊢ (ΛX.λx:X.x) ⊑ (ΛX.λx:X.x) α @ +(seal_α→seal_α) : (να.seal_α→seal_α)
    —→
      α:=☆ ⊢ (ΛX.λx:X.x) ⊑ (λx:α.x) @ +(seal_α→seal_α) : (να.seal_α→seal_α)


      --------------------------------------------------------------------------
      α:=☆ ⊢ (ΛX.λx:X.x) ⊑ (ΛX.λx:X.x) α @ +(seal_α→seal_α) : (να.seal_α→seal_α)


      α:=id_★ ⊢ (λx:α.x) ⊑ (λx:α.x) : id_α→id_α
      ---------------------------------------------------------------- ⊑+  (i)
      α:=id_★ ⊢ (λx:α.x) ⊑ (λx:α.x) @ +(seal_α→seal_α) : tag_α→tag_α
      --------------------------------------------------------------------- merge
      α:=★, α₀:=☆ ⊢ (λx:α.x) ⊑ (λx:α₀.x) @ +(seal_α₀→seal_α₀) : tag_α→tag_α
      -------------------------------------------------------------------------- Λ⊑
      α₀:=☆ ⊢ (ΛX.λx:X.x) ⊑ (λx:α₀.x) @ +(seal_α₀→seal_α₀) : (να.seal_α→seal_α)


      (i)  (tag_α→tag_α) ≈ (id_α→id_α) ⨾ (seal_α→seal_α)


Example 5. Example where the term on the left fails.

  c : ι′
  c★ : ★ = c @ +tag_ι′

    ∅ ⊢ ((λx:ι.x) @ +(tag_ι→tag_ι)) c★ ⊑ (λx:★.x) c★
  —→
    ∅ ⊢ ((λx:ι.x) (c★ @ -tag_ι)) @ +tag_ι ⊑ (λx:★.x) c★
  —→
    ∅ ⊢ blame ⊑ (λx:★.x) c★

    ∅ ⊢ (λx:ι.x) ⊑ (λx:★.x) : tag_ι→tag_ι
    ----------------------------------------------------
    ∅ ⊢ (λx:ι.x) @ +(tag_ι→tag_ι) ⊑ (λx:★.x) : id_★→id_★    ∅ ⊢ c★ ⊑ c★ : id_★
    --------------------------------------------------------------------------
    ∅ ⊢ ((λx:ι.x) @ +(tag_ι→tag_ι)) c★ ⊑ (λx:★.x) c★ : id_★


Example 6. Example where the term on the left fails, with abstraction. [UPDATED]

   Assume c⋆ = c ⟨ tag_ι′ ⟩ where ι ≠ ι′

    ∅ ⊢ (λx:★.x) c★ ⊒ ((να:=ι.(ΛX.λx:X.x) α ⟨ seal_α→-seal_α ⟩) ⟨ -tag_ι→tag_ι ⟩) c★ : id_⋆
  —→
    α:=ι ⊢ (λx:★.x) c★ ⊒ ((ΛX.λx:X.x) α ⟨ seal_α→-seal_α ⟩ ⟨ -tag_ι→tag_ι ⟩) c★ : id_⋆
  —→
    α:=ι ⊢ (λx:★.x) c★ ⊒ ((λx:α.x) ⟨ seal_α→-seal_α ⟩ ⟨ -tag_ι→tag_ι ⟩) c★ : id_⋆
  —↠
    α:=ι ⊢ (λx:★.x) c★ ⊒ (((λx:α.x) ⟨ seal_α→-seal_α ⟩) (c★ ⟨ -tag_ι ⟩)) ⟨ tag_ι ⟩ : id_⋆
  —→
    α:=ι ⊢ (λx:★.x) c★ ⊒ blame

    α:=✯; x:-tag_α ⊢ x ⊒ x : -tag_α
    ------------------------------------------
    α:=✯ ⊢ (λx:★.x) ⊒ (λx:α.x) : tag_α→-tag_α
    ---------------------------------------------
    ∅ ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) : να.tag_α→-tag_α
    ----------------------------------------------
    α:=ι ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) α : -tag_α→tag_α
    ----------------------------------------------------------------- (i)
    α:=ι ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) α ⟨ seal_α→-seal_α ⟩ : -tag_ι→tag_ι
    ------------------------------------------------------------------------------- (ii)
    α:=ι ⊢ (λx:★.x) ⊒ (ΛX.λx:X.x) α ⟨ seal_α→-seal_α ⟩ ⟨ -tag_ι→tag_ι ⟩ : id_★→id_★
    ------------------------------------------------------------------------------------
    ∅ ⊢ (να:=ι.(ΛX.λx:X.x) α ⟨ seal_α→-seal_α ⟩) ⟨ -tag_ι→tag_ι ⟩ ⊒ (λx:★.x) : id_★→id_★    ∅ ⊢ c★ ⊒ c★ : id_★
    ----------------------------------------------------------------------------------------------------------
    ∅ ⊢ ((να:=ι.(ΛX.λx:X.x) α ⟨ seal_α→seal_α ⟩) ⟨ -tag_ι→tag_ι ⟩) c★ ⊒ (λx:★.x) c★ : id_★


    CONTINUE FROM HERE

         (i)
                    -tag_ι→tag_ι
                         ∅
                    ι→ι ————→ ★→★
                     ↑      ↗
                     |     /
      seal_α→-seal_α |    /   -tag_α→tag_α
           α:=ι      |   /          ∅
                    α→α  
                          

         (ii)
                          id_★→id_★
                              ∅
                    ★→★ ————————————→ ★→★
                     ↑                 ↑
                     |                 |
         tag_ι→tag_ι |        ≈        |  id_★→id_★
               ∅     |                 |      ∅
                     |                 |
                    ι→ι ————————————→ ★→★
                         tag_ι→tag_ι
                              ∅


Example 7. Downcast preserves imprecision.

    ∅ ⊢ να:=ι.(ΛX.λx:X.x) α @ +(seal_α→seal_α) ⊑ να:=ι.((λx:★.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : id_ι→id_ι
  —→
    α:=ι ⊢ (ΛX.λx:X.x) α @ +(seal_α→seal_α) ⊑ α:=ι ⊢ ((λx:★.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : id_ι→id_ι
  —→
    α:=ι ⊢ (λx:α.x) @ +(seal_α→seal_α) ⊑ α:=ι ⊢ ((λx:★.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : id_ι→id_ι
  —→
    α:=ι ⊢ (λx:α.x) @ +(seal_α→seal_α) ⊑ α:=ι ⊢ (λx:★.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : id_ι→id_ι

      
      ∅ ⊢ (ΛX.λx:X.x) ⊑ (λx:★.x) : (να.seal_α→seal_α)
      -----------------------------------------------------------------  (να.seal_α→seal_α) ≈ (∀X.id_X→id_X)⨾(να.seal_α→seal_α)
      ∅ ⊢ (ΛX.λx:X.x) ⊑ ((λx:★.x) @ -(να.seal_α→seal_α)) : ∀X.id_X→id_X
      ------------------------------------------------------------------------
      α:=id_ι ⊢ (ΛX.λx:X.x) α ⊑ ((λx:★.x) @ -(να.seal_α→seal_α)) α : id_α→id_α
      --------------------------------------------------------------------------------------------------------------
      α:=id_ι ⊢ (ΛX.λx:X.x) α @ +(seal_α→seal_α) ⊑ ((λx:★.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : id_ι→id_ι
      --------------------------------------------------------------------------------------------------------------------     
      ∅ ⊢ να:=ι.(ΛX.λx:X.x) α @ +(seal_α→seal_α) ⊑ να:=ι.((λx:★.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : id_ι→id_ι


      α:=id_ι ⊢ (λx:α.x) ⊑ (λx:★.x) : tag_α→tag_α
      ---------------------------------------------------------- (tag_α→tag_α) ≈ (id_α→id_α)⨾(tag_α→tag_α)
      α:=id_ι ⊢ (λx:α.x) ⊑ (λx:★.x) @ -(tag_α→tag_α) : id_α→id_α
      ------------------------------------------------------------------------------------------------
      α:=id_ι ⊢ (λx:α.x) @ +(seal_α→seal_α) ⊑ (λx:★.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : id_ι→id_ι


Example 8. Instantiate id at different types.

  id  = ΛX.λx:X.x
  idα = λx:α.x
  id★ = λx:★.x
  c★  = c @ +tag_ι

    ∅ ⊢ id ι c ⊑ id ★ c★ : tag_ι
  ~>
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c
      ⊑ (να:=★. id α @ +(seal_α→seal_α)) c★ : tag_ι
  —↠
    α:=tag_ι ⊢ (idα @ +(seal_α→seal_α)) c
             ⊑ (idα @ +(seal_α→seal_α)) c★ : tag_ι
  —↠
    α:=tag_ι ⊢ (idα @ (c @ -seal_α)) @ +seal_α
             ⊑ (idα @ (c★ @ -seal_α)) @ +seal_α : tag_ι
  —↠
    α:=tag_ι ⊢ c @ -seal_α @ +seal_α
             ⊑ c★ @ -seal_α @ +seal_α : tag_ι
  —↠
    α:=tag_ι ⊢ c ⊑_∅ c★ : tag_ι


    ------------------------------- (x⊑x)
    α:=tag_ι, x:id_α ⊢ x ⊑ x : id_α
    -------------------------------- (λ⊑λ)
    α:=tag_ι ⊢ idα ⊑ idα : id_α→id_α
    ----------------------------------- (+⊑+)    (i)
    α:=tag_ι ⊢ (idα @ +(seal_α→seal_α))
             ⊑ (idα @ +(seal_α→seal_α)) : tag_ι→tag_ι    α:=tag_ι ⊢ c ⊑ c★ : tag_ι   
    ------------------------------------------------------------------------------ (·⊑·)
    α:=tag_ι ⊢ (idα @ +(seal_α→seal_α)) c
             ⊑ (idα @ +(seal_α→seal_α)) c★ : tag_ι


                            tag_ι→tag_ι
                                 ∅
                         ι→ι --------→ ★→★
                          ↑             ↑
                          |             |
            seal_α→seal_α |      ⊑      | seal_α→seal_α    (i)
                 α:=ι     |             |      α:=✯
                          |             |
                         α→α --------→ α→α
                             id_α→id_α
                                 ∅

            top:        ∅ | ∅ ⊢ tag_ι→tag_ι : ι→ι ⊑ ★→★
            left:       ∅ | α:=ι ⊢ seal_α→seal_α : α→α ⊑ ι→ι
            right:      ∅ | α:=★ ⊢ seal_α→seal_α : α→α ⊑ ★→★
            bottom:     α:=tag_ι | ∅ ⊢ id_α→id_α : α→α ⊑ α→α

  How does this example look in Igarashi et al (2017)?
  Their rules are formulated for the gradual surface language, F_G.

      γ, X, x:id_X ⊢ x ⊑ x : id_X
      --------------------------------------
      γ, X ⊢ (λx:X.x) ⊑ (λx:X.x) : id_X→id_X
      ----------------------------------------------
      γ ⊢ (ΛX.λx:X.x) ⊑ (ΛX.λx:X.x) : ∀X.(id_X→id_X)    γ ⊢ ι ⊑ ✯
      -----------------------------------------------------------
      γ ⊢ (ΛX.λx:X.x) ι ⊑ (ΛX.λx:X.x) ✯ : tag_ι→tag_ι                γ ⊢ c ⊑ c✯ : tag_ι
      ---------------------------------------------------------------------------------
      γ ⊢ (ΛX.λx:X.x) ι c ⊑ (ΛX.λx:X.x) ✯ c✯ : tag_ι

Example 9. Polymorphic id is less imprecise than monomorphic id.

    ∅ ⊢ id ι c ⊑_∅ id★ c★ : tag_ι
  ~>
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c ⊑_∅ id★ c★ : tag_ι
  —↠
    α:=ι ⊢ (idα @ +(seal_α→seal_α)) c ⊑_∅ id★ c★ : tag_ι
  —↠
    α:=ι ⊢ idα (c @ -seal_α) @ +seal_α ⊑_∅ id★ c★ : tag_ι
  —↠
    α:=ι ⊢ c @ -seal_α @ +seal_α ⊑_∅ c★ : tag_ι
  —↠
    α:=ι ⊢ c ⊑_∅ c★ : tag_ι


    -------------------------------------- (x⊑x)
    α:=ι, α′:=★, x:tag_α′ ⊢ x ⊑ x : tag_α′
    -------------------------------------------------- (λ⊑λ)
    α:=ι, α′:=★ ⊢ (λx:α′.x) ⊑ (λx:★.x) : tag_α′→tag_α′
    -------------------------------------------------- (Λ⊑)
    α:=ι ⊢ (ΛX.λx:X.x) ⊑ id★ : να.(seal_α→seal_α)
    --------------------------------------------- (α⊑)
    α:=ι ⊢ id α ⊑ id★ : tag_α→tag_α
    ---------------------------------------------------- (+⊑)  (i)
    α:=ι ⊢ id α @ +(seal_α→seal_α) ⊑_∅ id★ : tag_ι→tag_ι
    ---------------------------------------------------------- (ν⊑)
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) ⊑_∅ id★ : tag_ι→tag_ι         ∅ ⊢ c ⊑_∅ c★ : tag_ι
    --------------------------------------------------------------------------------------- (·⊑·)
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c ⊑_∅ id★ c★ : tag_ι


    (i)  (seal_α→seal_α) ⨾ (tag_ι→tag_ι) ⊑ (tag_α→tag_α)


    ------------------------------ (x⊑x)
    α:=ι, x:tag_α ⊢ x ⊑ x : tag_α
    ------------------------------- (λ⊑λ)
    α:=ι ⊢ idα ⊑ id★ : tag_α→tag_α
    ------------------------------------------------- (+⊑)
    α:=ι ⊢ idα @ +(seal_α→seal_α) ⊑ id★ : tag_ι→tag_ι         α:=ι ⊢ c ⊑ c★ : tag_ι
    ------------------------------------------------------------------------------- (·⊑·)
    α:=ι ⊢ (idα @ +(seal_α→seal_α)) c ⊑ id★ c★ : tag_ι


Example 10. Up on the left.

    ∅ ⊢ (id @ +(να.seal_α→seal_α)) c★ ⊑_∅ id★ c★ : id_★
  —↠
    ∅ ⊢ id ★ c★ ⊑_∅ id★ c★ : id_★
  ~>
    ∅ ⊢ (να:=★. id α @ +(seal_α→seal_α)) c★ ⊑_∅ id★ c★ : id_★
  —↠
    α:=★ ⊢ idα (c★ @ -seal_α) @ +seal_α ⊑_∅ id★ c★ : id_★
  —↠
    α:=★ ⊢ c★ @ -seal_α @ +seal_α ⊑_∅ c★ : id_★
  —↠
    α:=★ ⊢ c★ ⊑_∅ c★ : id_★
         

    -------------------------------- (x⊑x)
    α:=★, x:tag_α ⊢ x ⊑ x : tag_α
    -------------------------------------------- (λ⊑λ)
    α:=★ ⊢ (λx:α.x) ⊑ (λx:★.x) : (tag_α→tag_α)
    ----------------------------------------------- (Λ⊑)
    ∅ ⊢ (ΛX.λx:X.x) ⊑ (λx:★.x) : (να.seal_α→seal_α)
    ------------------------------------------------------------ (+⊑)
    ∅ ⊢ (ΛX.λx:X.x) @ +(να.seal_α→seal_α) ⊑ (λx:★.x) : id_★→id_★


Example 11. Up on the right.

    ∅ ⊢ id ι c ⊑_∅ (id @ +(να.seal_α→seal_α)) c★ : tag_ι
  ~>
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c ⊑_∅ (id @ +(να.seal_α→seal_α)) c★ : tag_ι
  —↠
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c ⊑_∅ (να₀:=★. id α₀ @ +(seal_α₀→seal_α₀)) c★ : tag_ι
  —↠
    α:=ι, α₀:=☆ ⊢ (id α @ +(seal_α→seal_α)) c ⊑_∅ (id α₀ @ +(seal_α₀→seal_α₀)) c★ : tag_ι
  —↠
    α:=ι, α₀:=☆ ⊢ idα (c @ -seal_α) @ +seal_α ⊑_∅ idα₀ (c★ @ -seal_α₀) @ +seal_α₀ : tag_ι
  —↠
    α:=ι, α₀:=☆ ⊢ c @ -seal_α @ +seal_α ⊑_∅ c★ @ -seal_α₀ @ +seal_α₀ : tag_ι
  —↠
    α:=ι, α₀:=☆ ⊢ c ⊑_∅ c★ : tag_ι

    ------------------------------ (x⊑x)
    α:=ι, X, x:id_X ⊢ x ⊑ x : id_X       
    ------------------------------------- (λ⊑λ)
    α:=ι, X ⊢ λx:X.x ⊑ λx:X.x : id_X→id_X    
    ------------------------------------- (Λ⊑Λ)
    α:=ι ⊢ id ⊑ id : ∀X.id_X→id_X
    ----------------------------------------------------------- (⊑+)    (i)
    α:=ι ⊢ id ⊑ (id @ +(να.seal_α→seal_α)) : (να.seal_α→seal_α)
    ------------------------------------------------------------------------ (α⊑)
    α:=ι ⊢ id α ⊑ (id @ +(να.seal_α→seal_α)) : tag_α→tag_α
    ------------------------------------------------------------------------- (+⊑)  (ii)
    α:=ι ⊢ id α @ +(seal_α→seal_α) ⊑ (id @ +(να.seal_α→seal_α)) : tag_ι→tag_ι    
    ------------------------------------------------------------------------------- (ν⊑)
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) ⊑ (id @ +(να.seal_α→seal_α)) : tag_ι→tag_ι

    (i)   (να.seal_α→seal_α) ≈ (∀X.id_X→id_X) ; (να.seal_α→seal_α)
    (ii)  (seal_α→seal_α) ; (tag_ι→tag_ι) ≈ tag_α→tag_α


Example 12. Up and then down.

    ∅ ⊢ id ι c ⊑ (id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α)) ι c : id_ι
  ~>
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c
      ⊑ (να:=ι. (id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —↠
    α:=id_ι
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ ((id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —↠
    α:=id_ι
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ (να₀:=★. (id α₀ @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —↠
    α:=id_ι,α₀:=☆
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ (((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —↠
    α:=id_ι,α₀:=☆
      ⊢ ((ƛx:α.x) @ +(seal_α→seal_α)) c
      ⊑ ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α→tag_α) @ +(seal_α→seal_α)) c : id_ι
  —↠
    α:=id_ι,α₀:=☆
      ⊢ ((ƛx:α.x) (c @ -seal_α)) @ +seal_α
      ⊑ ((ƛx:α₀.x) (c @ -seal_α @ +tag_α @ -seal_α₀)) @ +seal_α₀ @ -tag_α @ +seal_α : id_ι
  —↠
    α:=id_ι,α₀:=☆
      ⊢ c @ -seal_α @ +seal_α
      ⊑ c @ -seal_α @ +tag_α @ -seal_α₀ @ +seal_α₀ @ -tag_α @ +seal_α : id_ι
  —↠
    α:=id_ι,α₀:=☆ ⊢ c ⊑_∅ c : id_ι

   This example makes clear why we need αᵢ:=☆ bindings.
    
    --------------------------------- (x⊑x)
    α′:=id_★, x:id_α′ ⊢ x ⊑ x : id_α′
    ---------------------------------------------- (λ⊑λ)
    α′:=id_★ ⊢ (ƛx:α₀.x) ⊑ (ƛx:α₀.x) : id_α′→id_α′
    --------------------------------------------------------------------------- (⊑+)  (i)
    α′:=id_★ ⊢ (ƛx:α′.x) ⊑ (ƛx:α′.x) @ +(seal_α′→seal_α′) : tag_α′→tag_α′   
    --------------------------------------------------------------------------- merge
    α′:=★, α₀:=☆ ⊢ (ƛx:α′.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) : tag_α′→tag_α′
    ---------------------------------------------------------------------------- (Λ⊑)
    α₀:=☆ ⊢ (ΛX.ƛx:X.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) : να.seal_α→seal_α
    ------------------------------------------------------------------------------------------ (⊑-)
    α₀:=☆ ⊢ (ΛX.ƛx:X.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α) : ∀X.id_X→id_X
    ---------------------------------------------------------------------------------------------------- (α⊑α)
    α:=id_ι, α₀:=☆ ⊢ (ΛX.ƛx:X.x) α ⊑ ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α : id_α→id_α
    ---------------------------------------------------------------------------------------------------------------------------------------------- (+⊑+)
    α:=id_ι, α₀:=☆ ⊢ (ΛX.ƛx:X.x) α @ +(seal_α→seal_α) ⊑ ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : id_ι→id_ι

    (i)   (tag_α′→tag_α′) ≈  (id_α′→id_α′) ; (seal_α′→seal_α′)

    ------------------------------------------ (x⊑x)
    α:=id_ι, α′:=id_★, x:id_α′ ⊢ x ⊑ x : id_α′
    ------------------------------------------ (λ⊑λ)
    α:=tag_ι ⊢ (ƛx:α.x) ⊑ (ƛx:α.x) : id_α→id_α
    ---------------------------------------------------------------------- (⊑+) (i)
    α:=tag_ι ⊢ (ƛx:α.x) ⊑ (ƛx:α.x) @ +(seal_α→seal_α) : tag_α→tag_α
    ---------------------------------------------------------------------- (merge)
    α:=ι, α₀:=☆ ⊢ (ƛx:α.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) : tag_α→tag_α
    ---------------------------------------------------------------------------------------- (⊑-) (ii)
    α:=id_ι, α₀:=☆ ⊢ (ƛx:α.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α→tag_α) : id_α→id_α
    ----------------------------------------------------------------------------------------------------------------------------- (+⊑+)
    α:=id_ι, α₀:=☆ ⊢ (ƛx:α.x) @ +(seal_α→seal_α) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : id_ι→id_ι

         (i)
                       tag_α→tag_α
                            ∅
                  α→α ————————————→ ★→★
                   ↑                 ↑
                   |                 |
         id_α→id_α |        ≈        | seal_α→seal_α
             ∅     |                 |      α:=★
                   |                 |
                  α→α ————————————→ α→α
                        id_α→id_α
                            ∅

         (ii)
                       tag_α→tag_α
                            ∅
                  α→α ————————————→ ★→★
                   ↑                 ↑
                   |                 |
         id_α→id_α |        ≈        |  tag_α→tag_α
             ∅     |                 |       ∅
                   |                 |
                  α→α ————————————→ α→α
                        id_α→id_α
                            ∅

Example 13. Up and then down and then up. The binding list is getting longer.

    ∅ ⊢ id ι c
      ⊑ (id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α)) c★ : tag_ι
  ~>
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c
      ⊑ (id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α)) c★ : tag_ι
  —↠
    α:=ι
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ (id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α)) c★ : tag_ι
  —↠
    α:=ι
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ (να:=★. id α @ +(seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α)) c★ : tag_ι
  —↠
    α:=ι, α₀:=☆
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α)) c★ : tag_ι
  —↠
    α:=ι, α₀:=☆
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ (να₁:=★. ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α₁ @ +(seal_α₁→seal_α₁)) c★ : tag_ι
  —↠
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ (((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α₁ @ +(seal_α₁→seal_α₁)) c★ : tag_ι
  —↠  
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ ((ƛx:α.x) @ +(seal_α→seal_α)) c
      ⊑ ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α₁→tag_α₁) @ +(seal_α₁→seal_α₁)) c★ : tag_ι
  —↠  
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ (λx:α.x) (c @ -seal_α) @ +seal_α
      ⊑ ((λx:α₀.x) (c★ @ -seal_α₁ @ +tag_α₁ @ -seal_α₀)) @ +seal_α₀ @ -tag_α₁ @ +seal_α₁ : tag_ι
  —↠  
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ c @ -seal_α @ +seal_α
      ⊑ c★ @ -seal_α₁ @ +tag_α₁ @ -seal_α₀ @ +seal_α₀ @ -tag_α₁ @ +seal_α₁ : tag_ι
  —↠  
    α:=ι, α₀:=☆, α₁:=☆ ⊢ c ⊑ c★ : tag_ι


    α:=ι ⊢ id ⊑ id : (∀X.id_X→id_X)
    ------------------------------------------------------------ ⊑+ (i)
    α:=ι ⊢ id ⊑ id @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)
    --------------------------------------------------------------------------- ⊑- (i)
    α:=ι ⊢ id ⊑ id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) : (∀X.id_X→id_X)
    ------------------------------------------------------------------------------------------------ ⊑+ (i)
    α:=ι ⊢ id
         ⊑ id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)
    ------------------------------------------------------------------------------------------------ α⊑
    α:=ι ⊢ id α
         ⊑ id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : (tag_α→tag_α)
    ------------------------------------------------------------------------------------------- +⊑ (ii)
    α:=ι ⊢ id α @ +(seal_α→seal_α)
         ⊑ id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : (tag_ι→tag_ι)

    (i)   (να.seal_α→seal_α) ≈ (∀X.id_X→id_X) ⨾ (να.seal_α→seal_α)
    (ii)  (seal_α→seal_α) ⨾ (tag_ι→tag_ι) ≈ (tag_α→tag_α)


    α:=tag_ι ⊢ (λx:α.x) ⊑ (λx:α.x) : (id_α→id_α)
    ----------------------------------------------------------------- ⊑+  (i)
    α:=tag_ι ⊢ (λx:α.x) ⊑ (λx:α.x) @ +(seal_α→seal_α) : (tag_α→tag_α)
    ----------------------------------------------------------------- Λ⊑
    α:=tag_ι ⊢ id ⊑ (λx:α.x) @ +(seal_α→seal_α) : (να.seal_α→seal_α)
    ------------------------------------------------------------------------------ ⊑- (ii)
    α:=tag_ι ⊢ id ⊑ (λx:α.x) @ +(seal_α→seal_α) @ -(να.seal_α→seal_α) : (∀X.id_X→id_X)
    -------------------------------------------------------------------------------------------- ⊑+ (ii)
    α:=tag_ι ⊢ id
      ⊑ (λx:α.x) @ +(seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)
    -------------------------------------------------------------------------------------------- α⊑
    α:=tag_ι ⊢ id α
      ⊑ (λx:α.x) @ +(seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : tag_α→tag_α
    ------------------------------------------------------------------------------------- +⊑ (iii)    
    α:=tag_ι ⊢ id α @ +(seal_α→seal_α)
      ⊑ (λx:α.x) @ +(seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : tag_ι→tag_ι

    (i)    (tag_α→tag_α) ≈ (id_α→id_α) ⨾ (seal_α→seal_α)
    (ii)   (να.seal_α→seal_α) ≈ (∀X.id_X→id_X) ⨾ (να.seal_α→seal_α)
    (iii)  (seal_α→seal_α) ⨾ (tag_ι→tag_ι) ≈ (tag_α→tag_α)


    α:=tag_ι ⊢ (ƛx:α.x) ⊑ (ƛx:α.x) : id_α→id_α
    ------------------------------------------- ⊑+  (i)
    α:=tag_ι ⊢ (ƛx:α.x)
      ⊑ (ƛx:α.x) @ +(seal_α→seal_α) : tag_α→tag_α
    --------------------------------------------- ⊑-  (ii)
    α:=tag_ι, α₀:=☆ ⊢ (ƛx:α.x)
      ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α→tag_α) : id_α→id_α
    ----------------------------------------------------------------- ⊑+ (iii)
    α:=tag_ι, α₀:=☆ ⊢ (ƛx:α.x)
      ⊑ ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α→tag_α) @ +(seal_α→seal_α)) : tag_α→tag_α
    --------------------------------------------------------------------------------------- +⊑ (iv)
    α:=tag_ι, α₀:=☆ ⊢ ((ƛx:α.x) @ +(seal_α→seal_α))
      ⊑ ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α→tag_α) @ +(seal_α→seal_α)) : tag_ι→tag_ι

    (i)    (tag_α→tag_α) ≈ (id_α→id_α) ⨾ (seal_α→seal_α)
    (ii)   (tag_α→tag_α) ≈ (id_α→id_α) ⨾ (tag_α→tag_α)
    (iii)  (tag_α→tag_α) ≈ (id_α→id_α) ⨾ (seal_α→seal_α)
    (iv)   (seal_α→seal_α) ⨾ (tag_ι→tag_ι) ≈ (tag_α→tag_α)


Example 14. Up and then down and then up and then down.

    ∅ ⊢ id ι c
      ⊑ (id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α)) ι c : id_ι
  ~>
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c
      ⊑ (να:=ι. (id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —→
    α:=id_ι
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ ((id @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —→
    α:=id_ι
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ ((να₀:=★. id α₀ @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —→
    α:=id_ι, α₀:=☆
      ⊢ (id α @ +(seal_α→seal_α)) c
      ⊑ (id α₀ @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —→
    α:=id_ι, α₀:=☆
      ⊢ ((λx:α.x) @ +(seal_α→seal_α)) c
      ⊑ ((λx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —→
    α:=id_ι, α₀:=☆
      ⊢ ((λx:α.x) @ +(seal_α→seal_α)) c
      ⊑ (να₁:=★. (((λx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α₁ @ +(seal_α₁→seal_α₁) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ ((λx:α.x) @ +(seal_α→seal_α)) c
      ⊑ ((((λx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α₁ @ +(seal_α₁→seal_α₁) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ ((λx:α.x) @ +(seal_α→seal_α)) c
      ⊑ (((λx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α₁→tag_α₁) @ +(seal_α₁→seal_α₁) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ ((λx:α.x) @ +(seal_α→seal_α)) c
      ⊑ ((λx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α₁→tag_α₁) @ +(seal_α₁→seal_α₁) @ -(tag_α→tag_α) @ +(seal_α→seal_α)) c : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ ((λx:α.x) (c @ -seal_α)) @ +seal_α
      ⊑ ((λx:α₀.x) (c @ -seal_α @ +tag_α @ -seal_α₁ @ +tag_α₁ @ -seal_α₀)) @ +seal_α₀ @ -tag_α₁ @ +seal_α₁ @ -tag_α @ +seal_α : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ c @ -seal_α @ +seal_α
      ⊑ c @ -seal_α @ +tag_α @ -seal_α₁ @ +tag_α₁ @ -seal_α₀ @ +seal_α₀ @ -tag_α₁ @ +seal_α₁ @ -tag_α @ +seal_α : id_ι
  —→
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ c ⊑ c : id_ι


    α:=tag_ι
      ⊢ (λx:α.x)
      ⊑ ((λx:α.x) : id_α→id_α
    -------------------------
    α:=ι, α₀:=☆
      ⊢ (λx:α.x)
      ⊑ ((λx:α₀.x) @ +(seal_α₀→seal_α₀) : tag_α→tag_α
    ------------------------------------------------- (i)
    α:=tag_ι, α₀:=☆
      ⊢ (λx:α.x)
      ⊑ ((λx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α→tag_α) : id_α→id_α
    ---------------------------------------------------------------- (ii)
    α:=ι, α₀:=☆, α₁:=☆
      ⊢ (λx:α.x)
      ⊑ ((λx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α₁→tag_α₁) @ +(seal_α₁→seal_α₁) : tag_α→tag_α
    -----------------------------------------------------------------------------------------
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ (λx:α.x)
      ⊑ ((λx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α₁→tag_α₁) @ +(seal_α₁→seal_α₁) @ -(tag_α→tag_α) : id_α→id_α
    --------------------------------------------------------------------------------------------------------
    α:=id_ι, α₀:=☆, α₁:=☆
      ⊢ (λx:α.x) @ +(seal_α→seal_α)
      ⊑ ((λx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α₁→tag_α₁) @ +(seal_α₁→seal_α₁) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : id_ι→id_ι

      (i)
                     tag_α→tag_α
                          ∅
                  α→α --------> ★→✯ 
                   ↑             ↑
         id_α→id_α |      ⊑      | seal_α→seal_α
             ∅     |             |      α:=✯
                  α→α --------> α→α
                      id_α→id_α
                          ∅

      (ii)
                     tag_α→tag_α
                          ∅
                  α→α --------> ★→✯ 
                   ↑             ↑
         id_α→id_α |      ⊑      | tag_α→tag_α
             ∅     |             |      ∅
                  α→α --------> α→α
                      id_α→id_α
                          ∅

Example 15. Down on the right.

    ∅ ⊢ id ι c ⊑_∅ (id★ @ -(να.seal_α→seal_α)) ι c : id_ι
  ~>
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c
      ⊑ (να:=ι. (id★ @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —↠
    α:=id_ι ⊢ (idα @ +(seal_α→seal_α)) c
            ⊑ ((id★ @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —↠
    α:=id_ι ⊢   (idα @ +(seal_α→seal_α)) c
            ⊑_∅ ((id★ @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c : id_ι
  —↠
    α:=id_ι ⊢   (idα @ +(seal_α→seal_α)) c
            ⊑_∅ (id★ @ -(tag_α→tag_α) @ +(seal_α→seal_α)) c : id_ι
  —↠
    α:=id_ι ⊢   (idα (c @ -seal_α) @ +seal_α
            ⊑_∅ (id★ (c @ -seal_α @ +tag_α) @ -tag_α @ +seal_α : id_ι
  —↠
    α:=id_ι ⊢   c @ -seal_α @ +seal_α
            ⊑_∅ c @ -seal_α @ +tag_α @ -tag_α @ +seal_α : id_ι
  —↠
    α:=id_ι ⊢ c ⊑_∅ c : id_ι
  

Example 16. Down on the left

    ∅ ⊢ (id★ @ -(να.seal_α→seal_α)) ι c ⊑  id★ c★ : tag_ι
  ~>
    ∅ ⊢ να:=ι.((id★ @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c ⊑  id★ c★ : tag_ι
  —→
    α:=ι ⊢ ((id★ @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) c ⊑  id★ c★ : tag_ι
  —→
    α:=ι ⊢ (id★ @ -(tag_α→tag_α) @ +(seal_α→seal_α)) c ⊑  id★ c★ : tag_ι
  —↠
    α:=ι ⊢ (id★ (c @ -seal_α @ +tag_α) @ -tag_α @ +seal_α ⊑  id★ c★ : tag_ι
  —↠
    α:=ι ⊢ c @ -seal_α @ +tag_α @ -tag_α @ +seal_α ⊑  c★ : tag_ι
  —↠  
    α:=ι ⊢ c ⊑  c★ : tag_ι

    α:=ι ⊢ id★ ⊑  id★ : id_★→id_★
    ------------------------------------------------------------------- (ii)
    α:=ι ⊢ id★ @ -(tag_α→tag_α) ⊑  id★ : tag_α→tag_α
    ------------------------------------------------------------------- (i)
    α:=ι ⊢ id★ @ -(tag_α→tag_α) @ +(seal_α→seal_α) ⊑  id★ : tag_ι→tag_ι        α:=ι ⊢ c ⊑ c★ : tag_ι
    ------------------------------------------------------------------------------------------------
    α:=ι ⊢ (id★ @ -(tag_α→tag_α) @ +(seal_α→seal_α)) c ⊑  id★ c★ : tag_ι

    (i)   (seal_α→seal_α)⨾(tag_ι→tag_ι) = tag_α→tag_α
    (ii)  (tag_α→tag_α)⨾(id_★→id_★) ⊑ (tag_α→tag_α)


Example 17. Constant function. Polymorphic less imprecise then monomorphic.

    K   = ΛX.ΛY.λx:X.λy:Y.x
    Kα  = ΛY.λx:α.λy:Y.x
    Kαβ = λx:α.λy:β.x
    K★  = λx:★.λy:★.x

    ∅ ⊢ K ι ι 42 ⊑ K★ 42★ : tag_ι
  ~>
    ∅ ⊢ (νβ:=ι.(να:=ι.K α @ +(∀Y.seal_α→id_Y→seal_α)) β @ +(id_ι→seal_β→id_ι)) 42 69
      ⊑ K★ 42★ : tag_ι
  —↠
    α:=ι ⊢ (νβ:=ι.(Kα @ +(∀Y.seal_α→id_Y→seal_α)) β @ +(id_ι→seal_β→id_ι)) 42 69
         ⊑ K★ 42★ 69★ : tag_ι
  —↠
    α:=ι, β:=ι ⊢ (Kαβ @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι)) 42 69
               ⊑ K★ 42★ 69★ : tag_ι
  —↠
    α:=ι, β:=ι ⊢ (Kαβ @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι)) 42 69
               ⊑ K★ 42★ 69★ : tag_ι
  —↠
    α:=ι, β:=ι ⊢ Kαβ (42 @ -id_ι @ -seal_α) (69 @ -seal_β @ -id_β) @ +seal_α @ +id_ι
               ⊑ K★ 42★ 69★ : tag_ι
  —↠
    α:=ι, β:=ι ⊢ Kαβ (42 @ -seal_α) (69 @ -seal_β) @ +seal_α @ +id_ι
               ⊑ K★ 42★ 69★ : tag_ι
  —↠
    α:=ι, β:=ι ⊢ 42 @ -seal_α @ +seal_α @ +id_ι ⊑ 42★ : tag_ι
  —↠
    α:=ι, β:=ι ⊢ 42 ⊑ 42★ : tag_ι


  α:=★, β:=★, x:tag_α, y:tag_β ⊢ x ⊢ x : tag_α
  -------------------------------------------------------
  α:=★, β:=★, x:tag_α ⊢ (λy:β.x) ⊢ (λy:★.x) : tag_β→tag_α
  ---------------------------------------------------------------
  α:=★, β:=★ ⊢ (λx:α.λy:β.x) ⊢ (λx:★.λy:★.x) : tag_α→tag_β→tag_α
  ---------------------------------------------------------------
  α:=★ ⊢ (ΛY.λx:α.λy:Y.x) ⊢ (λx:★.λy:★.x) : νβ.tag_α→seal_β→tag_α
  ------------------------------------------------------------------
  ⊢ (ΛX.ΛY.λx:X.λy:Y.x) ⊢ (λx:★.λy:★.x) : να.νβ.seal_α→seal_β→seal_α


  α:=ι, β:=ι, x:tag_α, y:tag_β ⊢ x ⊑ x : tag_α
  ---------------------------------------------------
  α:=ι, β:=ι, x:tag_α ⊢ λy:β.x ⊑ λy:★.x : tag_β→tag_α
  ---------------------------------------------------
  α:=ι, β:=ι ⊢ Kαβ ⊑ K★ : tag_α→tag_β→tag_α
  ----------------------------------------------------------------- +⊑ (i)
  α:=ι, β:=ι ⊢ Kαβ @ +(seal_α→id_β→seal_α) ⊑ K★ : tag_ι→tag_β→tag_ι
  --------------------------------------------------------------------------------------- +⊑ (ii)
  α:=ι, β:=ι ⊢ Kαβ @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι) ⊑ K★ : tag_ι→tag_ι→tag_ι


  (i)  (seal_α→id_β→seal_α) ⨾ (tag_ι→tag_β→tag_ι) ≈ tag_α→tag_β→tag_α
  (ii) (id_ι→seal_β→id_ι) ⨾ (tag_ι→tag_ι→tag_ι) ≈ tag_ι→tag_β→tag_ι


Example 18. Constant function, up on the right.

    ∅ ⊢ K ι ι 42 ⊑ (K @ +(να.νβ.tag_α→tag_β→tag_α)) 42★ : tag_ι
  ~>
    ∅ ⊢   (νβ:=ι.(να:=ι.K α @ +(∀Y.seal_α→id_Y→seal_α)) β @ +(id_ι→seal_β→id_ι)) 42 69
      ⊑_∅ (K @ +(να.νβ.seal_α→seal_β→seal_α)) 42★ 69★ : tag_ι
  —↠
    α:=ι ⊢   (νβ:=ι.(Kα @ +(∀Y.seal_α→id_Y→seal_α)) β @ +(id_ι→seal_β→id_ι)) 42 69
         ⊑_∅ (K @ +(να.νβ.seal_α→seal_β→seal_α)) 42★ 69★ : tag_ι
  —↠
    α:=ι, β:=ι ⊢   (Kαβ @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι)) 42 69
               ⊑_∅ (K @ +(να.νβ.seal_α→seal_β→seal_α)) 42★ 69★ : tag_ι
  ~>
    α:=ι, β:=ι
      ⊢ (K α β @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι)) 42 69
      ⊑ (να₀:=★. K α₀ @ +(νβ.seal_α→seal_β→seal_α)) 42★ 69★ : tag_ι
  —↠
    α:=ι, β:=ι, α₀:=☆
      ⊢ (K α β @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι)) 42 69
      ⊑ (K α₀ @ +(νβ.seal_α₀→seal_β→seal_α₀)) 42★ 69★ : tag_ι 
  —↠
    α:=ι, β:=ι, α₀:=☆
      ⊢ (K α β @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι)) 42 69
      ⊑ (νβ₀:=★. K α₀ β₀ @ +(seal_α₀→seal_β₀→seal_α₀)) 42★ 69★ : tag_ι 
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆
      ⊢ (K α β @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι)) 42 69
      ⊑ (K α₀ β₀ @ +(seal_α₀→seal_β₀→seal_α₀)) 42★ 69★ : tag_ι 
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆
      ⊢ ((λx:α.λy:β.x) @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι)) 42 69
      ⊑ ((λx:α₀.λy:β₀.x) @ +(seal_α₀→seal_β₀→seal_α₀)) 42★ 69★ : tag_ι 
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆
      ⊢ ((λx:α.λy:β.x) (42 @ -id_ι @ -seal_α) (69 @ -seal_β @ -id_β)) @ +seal_α @ +id_ι
      ⊑ ((λx:α₀.λy:β₀.x) (42★ @ -seal_α₀) (69★ @ -seal_β₀) @ +seal_α₀ : tag_ι 
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆
      ⊢ 42 @ -id_ι @ -seal_α @ +seal_α @ +id_ι
      ⊑ 42★ @ -seal_α₀ @ +seal_α₀ : tag_ι 
  —↠
    α:=ι, β:=ι, α₀:=☆, β₀:=☆ ⊢ 42 ⊑ 42★ : tag_ι


Example 19. An example to demonstrate rebinding

    ∅ ⊢ (ΛX.λx:X.(ΛY.λy:Y.y)Xx)ιc ⊑ (λx:★.(λy:★.y)x)c★ : tag_ι
  ~>
    ∅ ⊢ (να:=ι.(ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α)) c ⊑ (λx:★.(λy:★.y)x)c★ : tag_ι
  —↠
    α:=ι ⊢ ((ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α)) c ⊑ (λx:★.(λy:★.y)x)c★ : tag_ι
  —↠
    α:=ι ⊢ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) @ +(seal_α→seal_α)) c ⊑ (λx:★.(λy:★.y)x)c★ : tag_ι
  —↠
    α:=ι ⊢ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) (c @ -seal_α) @ +seal_α ⊑ (λx:★.(λy:★.y)x)c★ : tag_ι
  —↠
    α:=ι ⊢ ((νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))(c @ -seal_α)) @ +seal_α ⊑ (λy:★.y)c★ : tag_ι
  —↠
    α:=ι, β:=α ⊢ ((ΛY.λy:Y.y)β @ +(seal_β→seal_β))(c @ -seal_α)) @ +seal_α ⊑ (λy:★.y)c★ : tag_ι
  —↠
    α:=ι, β:=α ⊢ ((λy:β.y) @ +(seal_β→seal_β))(c @ -seal_α)) @ +seal_α ⊑ (λy:★.y)c★ : tag_ι
  —↠
    α:=ι, β:=α ⊢ ((λy:β.y) (c @ -seal_α @ -seal_β)) @ +seal_β @ +seal_α ⊑ (λy:★.y)c★ : tag_ι
  —↠
    α:=ι, β:=α ⊢ c @ -seal_α @ -seal_β @ +seal_β @ +seal_α ⊑ c★ : tag_ι
  —↠
    α:=ι, β:=α ⊢ c @ -seal_α @ +seal_α ⊑ c★ : tag_ι
  —↠
    α:=ι, β:=α ⊢ c ⊑ c★ : tag_ι



    -----------------------------------------------------------------
    α:=★, x:tag_α, β:=α, y:tag_β ⊢ y ⊑ y : tag_β
    ----------------------------------------------------------------------------
    α:=★, x:tag_α, β:=α ⊢ (λy:β.y) ⊑ (λy:★.y) : tag_β→tag_β
    ------------------------------------------------------------------------------------
    α:=★, x:tag_α, β:=α ⊢ (ΛY.λy:Y.y) ⊑ (λy:★.y) : (νβ.seal_β→seal_β)
    ------------------------------------------------------------------------------------
    α:=★, x:tag_α, β:=α ⊢ (ΛY.λy:Y.y)β ⊑ (λy:★.y) : tag_β→tag_β
    --------------------------------------------------------------------------------- (i)
    α:=★, x:tag_α, β:=α ⊢ (ΛY.λy:Y.y)β @ +(seal_β→seal_β) ⊑ (λy:★.y) : tag_α→tag_α
    ---------------------------------------------------------------------------------
    α:=★, x:tag_α ⊢ νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β) ⊑ (λy:★.y) : tag_α→tag_α    α:=★, tag_α ⊢ x ⊑ x : tag_α
    --------------------------------------------------------------------------------------------------------------------
    α:=★, x:tag_α ⊢ (νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x ⊑ (λy:★.y)x : tag_α
    -----------------------------------------------------------------------------------------
    α:=★ ⊢ (λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) ⊑ (λx:★.(λy:★.y)x) : tag_α→tag_α
    ----------------------------------------------------------------------------------------------
    ∅ ⊢ (ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) ⊑ (λx:★.(λy:★.y)x) : (να.seal_α→seal_α)
    -------------------------------------------------------------------------------------------------------------
    α:=ι ⊢ (ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α ⊑ (λx:★.(λy:★.y)x) : tag_α→tag_α
    -------------------------------------------------------------------------------------------------------------- (ii)
    α:=ι ⊢ (ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α) ⊑ (λx:★.(λy:★.y)x) : tag_ι→tag_ι
    -------------------------------------------------------------------------------------------------------------------
    ∅ ⊢ (να:=ι.(ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α)) ⊑ (λx:★.(λy:★.y)x) : tag_ι→tag_ι    ∅ ⊢ c ⊑ c★ : tag_ι
    -----------------------------------------------------------------------------------------------------------------------------------------
    ∅ ⊢ (να:=ι.(ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α)) c ⊑ (λx:★.(λy:★.y)x)c★ : tag_ι

    (i)  (seal_β→seal_β) ⨾ (tag_α→tag_α) ≈ tag_β→tag_β
    (ii) (seal_α→seal_α) ⨾ (tag_ι→tag_ι) ≈ tag_α→tag_α

    α:=ι, x:tag_α, β:=α, y:tag_β ⊢ y ⊑ y : tag_β
    ----------------------------------------------------------------------------
    α:=ι, x:tag_α, β:=α ⊢ (λy:β.y) ⊑ (λy:★.y) : tag_β→tag_β
    ------------------------------------------------------------------------------------
    α:=ι, x:tag_α, β:=α ⊢ (ΛY.λy:Y.y) ⊑ (λy:★.y) : (νβ.seal_β→seal_β)
    ------------------------------------------------------------------------------------
    α:=ι, x:tag_α, β:=α ⊢ (ΛY.λy:Y.y)β ⊑ (λy:★.y) : tag_β→tag_β
    ---------------------------------------------------------------------------------
    α:=ι, x:tag_α, β:=α ⊢ (ΛY.λy:Y.y)β @ +(seal_β→seal_β) ⊑ (λy:★.y) : tag_α→tag_α
    -----------------------------------------------------------------------------------
    α:=ι, x:tag_α ⊢ (νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β)) ⊑ (λy:★.y) : tag_α→tag_α    α:=ι, x:tag_α ⊢ x ⊑ x : tag_α
    -----------------------------------------------------------------------------------------------------------------------
    α:=ι, x:tag_α ⊢ (νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x ⊑ (λy:★.y)x : tag_α
    -----------------------------------------------------------------------------------------
    α:=ι ⊢ (λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) ⊑ (λx:★.(λy:★.y)x) : tag_α→tag_α
    ------------------------------------------------------------------------------------------------------------
    α:=ι ⊢ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) @ +(seal_α→seal_α)) ⊑ (λx:★.(λy:★.y)x) : tag_ι→tag_ι    α:=ι ⊢ c ⊑ c★ : tag_ι
    -------------------------------------------------------------------------------------------------------------------------------------
    α:=ι ⊢ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) @ +(seal_α→seal_α)) c ⊑ (λx:★.(λy:★.y)x)c★ : tag_ι


Example 20. Example of final case of ν upcast lemma

    ∅ ⊢ (ΛX.λx:X.x) ⊑ (λx:⋆.x) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)
  —→
    ∅ ⊢ (ΛX.λx:X.x) ⊑ (να:=★.((λx:⋆.x) @ -(να.seal_α→seal_α)) α) @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)
  —→
    α:=☆ ⊢ (ΛX.λx:X.x) ⊑ ((λx:⋆.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : (να.seal_α→seal_α)
  —→
    α:=☆ ⊢ (ΛX.λx:X.x) ⊑ (λx:⋆.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : (να.seal_α→seal_α)

    ----------------------------- x⊑x
    α:=★, x:tag_α ⊢ x ⊑ x : tag_α
    ------------------------------------------ λ⊑λ
    α:=★ ⊢ (λx:α.x) ⊑ (λx:⋆.x) : (tag_α→tag_α)
    ----------------------------------------------- Λ⊑
    ∅ ⊢ (ΛX.λx:X.x) ⊑ (λx:⋆.x) : (να.seal_α→seal_α)
    ----------------------------------------------------------------- ⊑-  (i)
    ∅ ⊢ (ΛX.λx:X.x) ⊑ (λx:⋆.x) @ -(να.seal_α→seal_α) : (∀X.id_X→id_X)
    ------------------------------------------------------------------------------------------- ⊑+  (i)
    ∅ ⊢ (ΛX.λx:X.x) ⊑ (λx:⋆.x) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)

    (i)   (να.seal_α→seal_α) ≈ (∀X.id_X→id_X) ⨾ (να.seal_α→seal_α)

    ----------------------------- x⊑x
    α:=★, x:tag_α ⊢ x ⊑ x : tag_α
    --------------------------------------------- λ⊑λ
    α:=id_★ ⊢ (λx:α.x) ⊑ (λx:⋆.x) : (tag_α→tag_α)
    ------------------------------------------------------------ ⊑-  (i)
    α:=id_★ ⊢ (λx:α.x) ⊑ (λx:⋆.x) @ -(tag_α→tag_α) : (id_α→id_α)
    --------------------------------------------------------------------------------- ⊑+  (i)
    α:=id_★ ⊢ (λx:α.x) ⊑ (λx:⋆.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : (tag_α→tag_α)
    -------------------------------------------------------------------------------------- Λ⊑
    α:=☆ ⊢ (ΛX.λx:X.x) ⊑ (λx:⋆.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : (να.seal_α→seal_α)

    (i)   (tag_α→tag_α) ≈ (id_α→id_α) ⨾ (seal_α→seal_α)

Example 21. Double ν downcast (demonstrates need for -ν⊑)

    ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (λx:★.x) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)
  —→
    ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (να:=★. (λx:★.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : (να.seal_α→seal_α)
  —→
    α:=☆ ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ ((λx:★.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : (να.seal_α→seal_α)
  —→
    α:=☆ ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (λx:★.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : (να.seal_α→seal_α)


    ⊢ (λx:★.x) ⊑ (λx:★.x) : (id_★→id_★)
    ---------------------------------------------------------------------------------- -⊑- (i)
    ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (λx:★.x) @ -(να.seal_α→seal_α) : (∀X.id_X→id_X)
    ------------------------------------------------------------------------------------------------------------ ⊑+ (ii)
    ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (λx:★.x) @ -(να.seal_α→seal_α) @ +(να.seal_α→seal_α) : (να.seal_α→seal_α)

    (i)    (να.seal_α→seal_α) ⨾ (id_★→id_★) ≈ (∀X.id_X→id_X) ⨾ (να.seal_α→seal_α)
    (ii)   (να.seal_α→seal_α) ≈ (∀X.id_X→id_X) ⨾ (να.seal_α→seal_α)

    α:=id_★ ⊢ (λx:★.x) ⊑ (λx:★.x) : (id_★→id_★)
    ----------------------------------------------------------------------------- -⊑- (iii)
    α:=id_★ ⊢ (λx:★.x) @ -(tag_α→tag_α) ⊑ (λx:★.x) @ -(tag_α→tag_α) : (id_α→id_α)
    ---------------------------------------------------------------------------------------------------- ⊑+ (iv)
    α:=id_★ ⊢ (λx:★.x) @ -(tag_α→tag_α) ⊑ (λx:★.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : (tag_α→tag_α)
    ---------------------------------------------------------------------------------------------------------- -ν⊑
    α:=☆ ⊢ (λx:★.x) @ -(να.seal_α→seal_α) ⊑ (λx:★.x) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : (να.seal_α→seal_α)

    (iii) (tag_α→tag_α) ⨾ (id_★→id_★) ≈ (id_α→id_α) ⨾ (tag_α→tag_α)
    (iv)  (tag_α→tag_α) ≈ (id_α→id_α) ⨾ (seal_α→seal_α)

Example 22. Power of imprecision.

  Consider the following two imprecision relations:

    (να.∀Y.seal_α→id_Y→seal_α) : (∀X.∀Y.X→Y→X) ⊑ (∀Y.⋆→Y→ ⋆)
    (∀X.νβ.id_X→seal_β→id_X)   : (∀X.∀Y.X→Y→X) ⊑ (∀X.X→⋆→ X)

  In the system of Amahl et al 2017 or Igarashi et al 2017, the first is
  permitted but the second is not.  Ours permits both.


================================================================================
THE DEVELOPMENT
================================================================================

## Syntax

  Type         A,B,C      ::=  α | X | ι | ★ | A→B | ∀X.B[X]
  Ground type  G,H        ::=  α | ι | ★→★
  Imprecision  c,d        ::=  id_A | c;d | c→d | ∀X.c[X]
                             | tag_G | -tag_G^ℓ | seal_α | -seal_α
                             | να.c[α] | -να.c[α]
  Term         L,M,N      ::=  x | λx.N[x] | L M | ΛX.V[X] | L α
                             | να:=A.N[α] | κ | M ⊕ N | M ⟨ c ⟩ | blame ℓ
  Value        V,W        ::=  λx.N[x] | ΛX.V[X] | κ
                             | V ⟨ tag_G ⟩ | V ⟨ seal_α ⟩
                             | V ⟨ c→d ⟩ | V ⟨ ∀X.c[X] ⟩ | V ⟨ να.c[α] ⟩
  Environment  Γ,Δ        ::=  ∅ | Γ, α:=A | Γ, X | Γ, x:A
  Store        Σ,Π        ::=  ∅ | Σ, α:=A

  We have the following embedding of System F into our system.
     Assume Γ ⊢ L : ∀X.B[X].
     (L A) ~> (να:=A. L α ⟨ B[seal_α] ⟩
  where B[seal_α] : B[α] ⊑_{α:=A} B[A].

## Coercions (c : A =⇒_Σ B)

    ---------------- (ftv(A) ∩ dom(Σ) = ∅)  (i)
    id_A : A ==>_Σ A

    c : A =⇒_Σ B    d : B =⇒_Π C
    ---------------------------- (if α:=A ∈ Σ and α:=B ∈ Π then A = B)
    (c ; d) : A =⇒_{Σ,Π} C

    c : A′ =⇒_Σ A    d : B =⇒_Σ B′
    ------------------------------
    (c→d) : (A→B) =⇒_Σ (A′→B′)

    c[X] : A[X] =⇒_Σ B[X]
    ------------------------------------
    (∀X.c[X]) : (∀X.A[X]) =⇒_Σ (∀X.B[X])

    c[α] : A =⇒_Σ B[α]
    ---------------------------- α ∉ fv(A), α ∈ fv(B[α])
    (να.c[α]) : A =⇒_Σ (∀X.B[X])

    c[α] : A[α] =⇒_{Σ,α:=⋆} B
    ----------------------------- α ∈ fv(A[α]), α ∉ fv(B)
    (-να.c[α]) : (∀X.A[X]) =⇒_Σ B

    ---------------- (if G=α then α ∉ dom(Σ))  (ii)
    tag_G : G =⇒_Σ ★

    ------------------- (if G=α then α ∉ dom(Σ))  (ii)
    -tag_G^ℓ : ★ =⇒_Σ G

    ----------------- (α:=A) ∈ Σ
    seal_α : A =⇒_Σ α

    ------------------ (α:=A) ∈ Σ
    -seal_α : α =⇒_Σ A

    (i)  guarantees we don't have both id_α and seal_α
         in the same imprecision judgement.

    (ii) guarantees we don't have both tag_α and seal_α
         in the same imprecision judgement.

  Lemma.  Derivation determines types and store.
    if c : A =⇒_Σ B and c : A′ =⇒_Σ′ B′ then
    types and stores agree: A = A′ and B = B′ and Σ = Σ′.


## Free type and store variables

  Free type variables of a type

    ftv(α)         =  {α}
    ftv(X)         =  {X}
    ftv(ι)         =  ∅
    ftv(⋆)         =  ∅
    ftv(A→B)       =  ftv(A) ∪ ftv(B)
    ftv(∀X.A[X])   =  ftv(A[X]) / {X}

  Free type variables of a coercion

    ftv(id_A)      =  ftv(A)
    ftv(c;d)       =  ftv(c) ∪ ftv(d)
    ftv(c→d)       =  ftv(c) ∪ ftv(d)
    ftv(∀X.c[X])   =  ftv(c[X]) / {X}
    ftv(να.c[α])   =  ftv(c[α])
    ftv(-να.c[α])  =  ftv(c[α])
    ftv(tag_G)     =  ftv(G)
    ftv(-tag_G)    =  ftv(G)
    ftv(seal_α)    =  ∅
    ftv(-seal_α)   =  ∅

  Free store variables of a coercion

    fsv(id_A)      =  ∅
    fsv(c;d)       =  fsv(c) ∪ fsv(d)
    fsv(c→d)       =  fsv(c) ∪ fsv(d)
    fsv(∀X.c[X])   =  fsv(c[X])
    fsv(να.c[α])   =  fsv(c[α]) / {α}
    fsv(-να.c[α])  =  fsv(c[α]) / {α}    
    fsv(tag_G)     =  ∅
    fsv(-tag_G)    =  ∅
    fsv(seal_α)    =  {α}
    fsv(-seal_α)   =  {α}


## Duality

We ignore labels on untags for duality.

Note that in να.c[α] all occurrences of α must be of the form tag_α or -tag_α.
and in -να.c[α] all occurrences of α must be of the form seal_α or -seal_α.
We occasionally indicate this by writing να.c[tag_α] or -να.c[seal_α].
Further, if c[tag_α] : A =⇒_Σ B is in scope,
we write c[seal_α] : A =⇒_{Σ,α:=⋆} B to indicate the former with all occurrences
of tag_α replaced by -seal_α, and all occurrences of -tag_α replaced by seal_α;
and vice-versa.

Dual. Given c : A =⇒_Σ B it's dual is -c : B =⇒_Σ A.

    -(id_A)         =  id_A
    -(c→d)          =  (-c)→(-d)
    -(∀X.c[X])      =  ∀X.(-c[X])
    -(c;d)          =  (-d);(-c)
    -(tag_G)        =  -tag_G              -(-tag_G)        =  tag_G
    -(seal_α)       =  -seal_α             -(-seal_α)       =  seal_α
    -(να.c[tag_α])  =  -να.(-c[seal_α])    -(-να.c[tag_α])  =  να.(-c[seal_α])

Duality is an involution. For any c : A =⇒_Σ B, we have --c = c.
    

## Environments (Γ wf)

    ∅ wf

    Γ wf   ftv(A) ⊆ dom(Γ)
    ---------------------- (α ∉ dom(Γ))
    Γ, α:=A wf

    Γ wf
    ------- (X ∉ dom(Γ))
    Γ, X wf

    Γ wf    ftv(A) ⊆ dom(Γ)
    ----------------------- (x ∉ dom(Γ))
    Γ, x:A wf

    Lemma (Well-formed contexts are closed under prefix).
      If (Γ, Δ) wf then Γ wf.


## Terms (Γ ⊢ M : A)

    Γ wf
    --------- (x:A) ∈ Γ
    Γ ⊢ x : A

    Γ ⊢ A    Γ, x : A ⊢ N[x] : B
    ---------------------------- x ∉ dom(Γ)
    Γ ⊢ λx.N[x] : A → B

    Γ ⊢ L : A → B    Γ ⊢ M : A
    --------------------------
    Γ ⊢ L M : B

    Γ, X ⊢ V[X] : B[X]
    --------------------- X ∉ dom(Γ)
    Γ ⊢ ΛX.V[X] : ∀X.B[X]

    Γ ⊢ L : ∀X.B[X]
    --------------------
    Γ, α:=A ⊢ L α : B[α]

    Γ ⊢ A   Γ, α:=A ⊢ N[α] : B
    -------------------------- α ∉ dom(Γ), α ∉ fv(B)
    Γ ⊢ να:=A.N[α] : B

    Γ wf
    --------- tp(κ) = ι
    Γ ⊢ κ : ι

    Γ ⊢ M : ι    Γ ⊢ N : ι′
    ----------------------- tp(⊕) = ι → ι′ → ι″
    Γ ⊢ M ⊕ N : ι″

    Γ ⊢ M : A    c : A =⇒_Σ B
    ------------------------- Σ ⊆ Γ
    Γ ⊢ M ⟨ c ⟩ : B

    Γ ⊢ A
    -------------
    Γ ⊢ blame : A

    Lemma (Sanity).
      If Γ ⊢ M : A then Γ wf and ftv(A) ⊆ dom(Γ).

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
    W ⟨ seal_α ⟩   : α          where  Γ ⊢ W : A  and α:=A ∈ Γ
    W ⟨ tag_G ⟩    : ★          where  Γ ⊢ W : G


## Evaluation contexts (Γ ⊢ E : A ~~> B)

    E ::= □ | E M | V E | E α | E ⊕ M | V ⊕ E | E ⟨ c ⟩

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


## Reduction rules (M ⊢→ N, M —→_Π N)

    κ ⊕ κ′                         ⊢→  δ(⊕)(κ,κ′)
    (λx.N[x]) V                    ⊢→  N[V]
    (ΛX.V[X]) α                    ⊢→  V[α]
    V ⟨ id_a ⟩                     ⊢→  V
    V ⟨ c;d ⟩                      ⊢→  V ⟨ c ⟩ ⟨ d ⟩
    (V ⟨ c→d ⟩) W                  ⊢→  V (W ⟨ c ⟩) ⟨ d ⟩
    (V ⟨ ∀X.c[X] ⟩) α              ⊢→  V α ⟨ c[α] ⟩
    (V ⟨ να.c[α] ⟩) α              ⊢→  V ⟨ c[α] ⟩
    V ⟨ -να.c[α] ⟩                 ⊢→  να:=★.(V α ⟨ c[α] ⟩)
    V ⟨ tag_G ⟩ ⟨ -tag_G ⟩         ⊢→  V
    V ⟨ tag_G ⟩ ⟨ -tag_H ⟩         ⊢→  blame,   G ≠ H
    V ⟨ seal_α ⟩ ⟨ -seal_α ⟩       ⊢→  V


    M ⊢→ N
    --------------
    E[M] —→_∅ E[N]

    ------------------------------- α ∉ fv(να:=A.N[α])
    E[να:=A.N[α]] —→_{α:=A} E[N[α]]

    -------------------
    E[blame] —→_∅ blame


    --------
    M —↠_∅ M

    M —→_Σ N    N —↠_Π P
    --------------------
    M —↠_{Σ,Π} P


## Thunking

  Let tt:⊤ be the unit value of unit type.

  We convert arbitrary terms under Λ to values under Λ by a translation:
    ⟦ ΛX.N[X] ⟧  =  ΛX.λx:⊤.⟦ N[X] ⟧
    ⟦ L α ⟧      =  L α tt

  If we apply the translation uniformly to the reduction rules, something goes wrong. What?

        ⟦ (ΛX.N[X]) α ⟧
    ~>  (ΛX.λx:⊤.⟦ N[X] ⟧) α tt
    —↠  ⟦ N[α] ⟧
    
        ⟦ L ⟨ να.c[α] ⟩ α ⟧
    ~>  (⟦ L ⟧ ⟨ να.id_⊤→c[α] ⟩ α tt
    —↠  να:=★. ⟦ L ⟧ α ⟨ id_⊤→c[α] ⟩ tt
    —↠  να:=★. ⟦ L ⟧ α tt ⟨ c[α] ⟩
    <~  ⟦ να:=★. L α ⟨ c[α] ⟩ ⟧

        ⟦ (L ⟨ -να.c[α] ⟩ ⟧
    ~>  να:=★. ⟦ L ⟧ α ⟨ id_⊤→c[α] ⟩
        Not in the image of the translation, because missing application to tt.
        This is why we can't apply the transformation uniformly to the reduction rules!
      
        In particular, the problematic example behaves as follows.
        ⟦ ((ΛX.blame) ⟨ -να.seal_α ⟩ ⟨ να.tag_α ⟩ ⟧
    ~>  ((ΛX.λx:⊤.blame) ⟨ -να.id_⊤→seal_α ⟩ ⟨ να.id_⊤→tag_α ⟩
    —↠  να:=★. (ΛX.λx:⊤.blame) α ⟨ id_⊤→seal_α ⟩ ⟨ να.id_⊤→seal_α ⟩
    —↠  να:=★. (λx:⊤.blame) ⟨ id_⊤→seal_α ⟩ ⟨ να.id_⊤→seal_α ⟩
        Not in the image of the translation.

        If all polymorphic terms are applied, we stay in the image of the translation.
        ⟦ ((ΛX.blame) ⟨ -να.unseal_α ⟩ ⟨ να.untag_α ⟩) α ⟧
    ~>  (ΛX.λx:⊤.blame) ⟨ -να.id_⊤→unseal_α ⟩ ⟨ να.id_⊤→tag_α ⟩ α tt
    —↠  (να₀:=★. (ΛX.λx:⊤.blame) α₀ ⟨ id_⊤→unseal_α₀ ⟩) ⟨ να.id_⊤→untag_α ⟩ α tt
    —↠  (να₀:=★. (λx:⊤.blame) ⟨ id_⊤→unseal_α₀ ⟩) ⟨ να.id_⊤→untag_α ⟩ α tt
    —↠  (να₀:=★. (λx:⊤.blame) ⟨ id_⊤→unseal_α₀ ⟩) ⟨ id_⊤→untag_α ⟩ tt
    —↠  (να:=★. (λx:⊤.blame) tt ⟨ unseal_α₀ ⟩ ⟨ untag_α ⟩
    —↠  να:=★. blame ⟨ unseal_α ⟩ ⟨ untag_α ⟩
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
    --------------- (α:=A ∈ Σ)
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
    ----------------------
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
        * -να.c[α], in which case
          V ⟨ -να.c[α] ⟩ ⊢→ να:=★.(V α ⟨ c[α] ⟩)
        * tag_G, in which case
          (V ⟨ tag_G ⟩) is a value
        * -tag_H, in which case
          by canonical forms V has the form (W ⟨ tag_G ⟩) and either
          ● G = H, in which case
            W ⟨ tag_G ⟩ ⟨ —tag_G ⟩ ⊢→ W
          ● G ≠ H, in which case
            W ⟨ tag_G ⟩ ⟨ —tag_H ⟩ ⊢→ blame
        * seal_α, in which case
          (V ⟨ seal_α ⟩) is a value
        * -seal_α, in which case
          by canonical forms V = (W ⟨ seal_α ⟩) and
          W ⟨ seal_α ⟩ ⟨ -seal_α ⟩ ⊢→ W
          

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

    V @ ±id_a  ⊢→  V

        Σ ⊢ V : a    Σ ⊢ ±id_a : a ⇒ a
        ------------------------------
        Σ ⊢ V @ ±id_a : a
      ⊢→
        Σ ⊢ V : a

    V @ +(c;d)  ⊢→  V @ +c @ +d

                     Σ ⊢ c : A ⊑ B    Σ ⊢ d : B ⊑ C
                     ------------------------------
        Σ ⊢ V : A    Σ ⊢ (c;d) : A ⊑ C
        ------------------------------
        Σ ⊢ V @ +(c;d) : C
      ⊢→
        Σ ⊢ V : A    Σ ⊢ c : A ⊑ B
        ---------------------------
        Σ ⊢ V @ +c : B                 Σ ⊢ d : B ⊑ C
        --------------------------------------------
        Σ ⊢ V @ +c @ +d : C

    V @ -(c;d)  ⊢→  V @ -d @ -c

                     Σ ⊢ c : A ⊑ B    Σ ⊢ d : B ⊑ C
                     ------------------------------
        Σ ⊢ V : C    Σ ⊢ (c;d) : A ⊑ C
        ------------------------------
        Σ ⊢ V @ -(c;d) : A
      ⊢→
        Σ ⊢ V : C    Σ ⊢ d : B ⊑ C
        ---------------------------
        Σ ⊢ V @ -d : B                 Σ ⊢ c : A ⊑ B
        --------------------------------------------
        Σ ⊢ V @ -d @ -c : A

    (V @ ±(c→d)) W  ⊢→  V (W @ ∓c) @ ±d

                       Σ ⊢ ∓c : A′ ⇒ A    Σ ⊢ ±d : B ⇒ B′
                       ----------------------------------
        Σ ⊢ V : A→B    Σ ⊢ ±(c→d) : A→B ⇒ A′→B′
        ---------------------------------------
        Σ ⊢ V @ ±(c→d) : A′ → B′                   Π ⊢ W : A′
        -----------------------------------------------------
        Σ ⊢ (V @ ±(c→d)) W : B′
      ⊢→
                       Σ ⊢ W : A′    Σ ⊢ ∓c : A′ ⇒ A
                       -----------------------------
        Σ ⊢ V : A→B    Σ ⊢ W @ ∓c : A
        -----------------------------
        Σ ⊢ V (W @ ∓c) : B               Σ ⊢ ±d : B ⇒ B′
        ------------------------------------------------
        Σ ⊢ V (W @ ∓c) @ ±d : B′

    (V @ ±(∀X.c[X])) α  ⊢→  V α @ ±c[α]

                           Σ, X ⊢ ±c[X] : A[X] ⇒ B[X]
                           ----------------------------------
        Σ ⊢ V : ∀X.A[X]    Σ ⊢ ±(∀X.c[X]) : ∀X.A[X] ⇒ ∀X.B[X]
        -----------------------------------------------------
        Σ ⊢ V @ ±(∀X.c[X]) : ∀X.B[X]
        ----------------------------- α:=C ∈ Σ
        Σ ⊢ (V @ ±(∀X.c[X])) α : B[α]
      ⊢→
        Σ ⊢ V : ∀X.A[X]
        --------------- α:=C ∈ Σ
        Σ ⊢ V α : A[α]              Σ ⊢ ±c[α] : A[α] ⇒ B[α]
        ---------------------------------------------------
        Σ ⊢ V α @ ±c[α] : B[α]

    V @ +(να.c[seal_α])  ⊢→  να:=★. V α @ + c[seal_α]

                           Σ, α:=★ ⊢ c[seal_α] : A[α] ⊑ B
                           ------------------------------
        Σ ⊢ V : ∀X.A[X]    Σ ⊢ να.c[seal_α] : ∀X.A[X] ⊑ B
        -------------------------------------------------
        Σ ⊢ V @ +(να.c[seal_α]) : B
      ⊢→
        Σ, α:=★ ⊢ V : ∀X.A[X]
        ---------------------
        Σ, α:=★ ⊢ V α : A[α]     Σ, α:=★ ⊢ c[seal_α] : A[α] ⊑ B
        -------------------------------------------------------
        Σ, α:=★ ⊢ (V α @ +c[seal_α]) : B
         ---------------------------------
        Σ ⊢ (να:=★. V α @ + c[seal_α]) : B

    (V @ —(να.c[seal_α])) α  ⊢→  V @ -c[tag_α]

                     Σ, α:=★ ⊢ c[seal_α] : A[α] ⊑ B
                     ------------------------------
        Σ ⊢ V : B    Σ ⊢ να.c[seal_α] : ∀X.A[X] ⊑ B
        -------------------------------------------
        Σ ⊢ V @ —(να.c[seal_α]) : ∀X.A[X]
        ---------------------------------- α:=C ∈ Σ
        Σ ⊢ (V @ —(να.c[seal_α])) α : A[α]
      ⊢→
        Σ ⊢ V : B    Σ ⊢ c[tag_α] : A[α] ⊑ B
        ------------------------------------ α:=C ∈ Σ
        Σ ⊢ V @ -c[tag_α] : A[α]

    V @ +tag_G @ —tag_G  ⊢→  V
                 
        Σ ⊢ V : G    Σ ⊢ tag_G : G ⊑ ★
        ------------------------------
        Σ ⊢ V @ +tag_G : ✯                Σ ⊢ tag_G : G ⊑ ★
        ---------------------------------------------------
        Σ ⊢ V @ +tag_G @ —tag_G : G
      ⊢→
        Σ ⊢ V : G

    V @ +tag_G @ —tag_H  ⊢→  blame,  if G ≠ H

        Σ ⊢ V : G    Σ ⊢ tag_G : G ⊑ ★
        ------------------------------
        Σ ⊢ V @ +tag_G : ✯                Σ ⊢ tag_H : H ⊑ ★
        ---------------------------------------------------
        Σ ⊢ V @ +tag_G @ —tag_H : H
      ⊢→
        Σ ⊢ blame : H

    V @ -seal_α @ +seal_α  ⊢→  V

        Σ ⊢ V : A    Σ ⊢ seal_α : α ⊑ A
        -------------------------------
        Σ ⊢ V @ -seal_α : α                Σ ⊢ seal_α : α ⊑ A
        -----------------------------------------------------
        Σ ⊢ V @ -seal_α @ +seal_α : A
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

    -----------------------------------------------
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

    -------------------------
    Σ ⊢ E[blame]  —→_∅  blame

        Σ ⊢ blame : A    Σ ⊢ E : A ~~> B
        --------------------------------
        Σ ⊢ E[blame] : B
      —→
        blame : B


## Underlying types

  Every type other than ⋆ has a unique underlying type.

  |α|        =  α
  |X|        =  X
  |ι|        =  ι
  |A→B|      =  ⋆→⋆
  |∀X.A[X]|  =  ∀X.⋆


## Narrowing and Widening

  We define narrowing and widening as follows.

  Assume s, s̅ : A =⇒_Σ B.
  Then we write s : A ⊒_Σ B and s̅ : A ⊑_Σ B
  if they satisfy the following grammar.

     g,h  ::=  id_α | id_X | id_ι | s̅→t | ∀X.s[X]
     s,t  ::=  g | id_⋆ | να.s[α] | -tag_G;g | s;seal_α
     g̅,h̅  ::=  id_α | id_X | id_ι | s→t̅ | ∀X.s̅[X]
     s̅,t̅  ::=  g̅ | id_⋆ | -να.s̅[α] | g̅;tag_G | -seal_α;s̅

  Cross coercions.
    If g : A =⇒_Σ B or g̅ : A =⇒_Σ B then |A| = |B|.

  Narrowing and Widening are dual.
    If s : A ⊒_Σ B then s̅ : B ⊑_Σ A and
    if s̅ : A ⊑_Σ B then s : B ⊒_Σ A.

  Widening and narrowing are determined by types and store.
    If s : A ⊒_Σ B and t : A ⊒_Σ B then s = t.
    If v : A ⊑_Σ B and w : A ⊑_Σ B then v = w.


## Composition for narrowing.

  Composition of narrowing is defined as follows.

  s : A ⊒_Σ B    t : B ⊒_Π C
  --------------------------
  (s ⨾ t) : A ⊒_{Σ,Π} C

  s ⨾ t = r  (by cases on t)

      s ⨾ id_★               =  s
      id_⋆ ⨾ (-tag_G;g)      =  (-tag_G;g)
      s ⨾ (t;seal_α)         =  (s ⨾ t);seal_α
      s ⨾ (να.t[α])          =  να.(s ⨾ t[α])

  s ⨾ g = r  (by cases on s)

      id_⋆ ⨾ id_⋆            =  id_⋆
      (-tag_G;g) ⨾ h         =  -tag_G;(g ⨾ h)
      (s;seal_α) ⨾ id_α      =  s;seal_α
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
    M ⟨ v ⨾ w ⟩  ≅  M ⟨ v ⟩ ⟨ w ⟩


## Factoring

    We can factor narrowing into casts and conversions.

    A cast is an narrowing with tags but no free seals.
    A conversion is a narrrowing with seals but no tags and no ν.

    Casts            p, q   fsv(p) = ∅
    Abstraction      φ, ψ   ::=  id_a | φ→ψ | ∀X.ϕ[X] | φ;seal_α

    Claim. For every s there exist p and φ such that s = p ⨾ φ

    Abstraction Factoring Lemma.
      Let φ : A ⊑_{Σ,α:=⋆} B be an abstraction.
      Then there exists φ₁ and φ₂ such that:
        (i)   fsv(φ₁) ⊆ dom(Σ)
        (ii)  fsv(ϕ₂) ⊆ {α}
        (iii) φ = φ₁ ⨾ φ₂.

    Proof.

      Cases for id_a, φ→ψ, ∀X.φ[X] as for proper factoring lemma, below.

      In the case for seal_α, with α:=★,
      take φ₁ = id_★ and φ₂ = seal_α.

      In the case for φ;seal_β with β ≠ α and β:=A.
      By induction, φ = φ₁′⨾φ₂′ with fsv(φ₂′) = {a}.
      take φ₁ = (seal_β;φ₁′) and φ₂ = φ₂′.

    Imprecision Factoring Lemma.
      Every imprecision factors into a cast and and a conversion:
      For every s there exist φ and p such that s = φ ⨾ p.

    Proof.
        id_a
      =⟨def'n ⨾⟩
        id_a⨾id_a

        s;tag_G
      =⟨induction⟩
        (φ⨾s);tag_G
      =⟨def'n ⨾⟩
        φ⨾(s;tag_G)

        seal_α;s
      =⟨induction⟩
        seal_α;(φ⨾p)
      =⟨def'n ⨾⟩
        (seal_α;φ)⨾p

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

    (V @ -(να.s[seal_α])) α ⊢→ V @ -s[tag_α]

Observe that (V @ -(να.s[seal_α])) is a value. The redex,
V @ -s[tag_α], is very nearly a value, with one exceptional
corner case.

Consider the possibilities for -s[tag_α]. It will be one of

   (s₀→t₀)
   (∀X.s₀[id_X])
   (νa.s₀[seal_α])
   tag_α

It cannot be id_a or seal_α, because -s[tag_α] must contain tag_α.
For all of these, V @ -s[tag_α] is itself a value, with the sole
exception being the case tag_α. This can arise only from:

    (V @ -(να.seal_α)) α ⊢→ V @ -tag_α

Here V : ★ and (να.seal_α) : (∀X.X) ⊑ ★. The right-hand side
V @ -tag_α must (by parametricity) reduce to blame. (The other
possibility, that it loops forever, cannot occur becase V is
a value.)

In what follows, it will be convenient to rule out this corner
case, to ensure that the right-hand side of

    (V @ -(να.s[seal_α])) α ⊢→ V @ -s[tag_α]

is always a value. Therefore, we modify the formation rule for
ν to rule out this corner case.

    Γ, α:=✯ | Φ, α ⊢ s[α] : A[α] ⊑ B
    -------------------------------- α ∈ fv(A[α]), α ∉ fv(B), A[α] ≠ α.
    Γ | Φ ⊢ (να.s[α]) : ∀X.A[X] ⊑ B


## Environment imprecision (γ : Γ ⊑ Γ′, σ : Σ ⊑ Σ′)

    γ    ::=  ∅ | γ, α:=p | γ, α:=A | γ, α:=☆ | γ, X | γ, x:p
    σ,π  ::=  ∅ | σ, α:=p | σ, α:=A | σ, α:=☆

    ---------
    ∅ : ∅ ⊑ ∅

    γ : Γ ⊑ Γ′    Γ ⊢ A
    -------------------------- α ∉ dom(γ)
    (γ, α:=A) : (Γ, α:=A) ⊑ Γ′

    γ : Γ ⊑ Γ′    Γ ⊢ p : A ⊑ A′    Γ′ ⊢ A′
    --------------------------------------- α ∉ dom(γ)
    (γ, α:=p) : (Γ, α:=A) ⊑ (Γ′, α:=A′)

    γ : Γ ⊑ Γ′
    -------------------------- α ∉ dom(γ)
    (γ, α:=☆) : Γ ⊑ (Γ′, α:=★)

    γ : Γ ⊑ Γ′
    ------------------------- X ∉ dom(γ)
    (γ, X) : (Γ, X) ⊑ (Γ′, X)

    γ : Γ ⊑ Γ′    Γ ⊢ p : A ⊑ A′    Γ′ ⊢ A′
    --------------------------------------- x ∉ dom(γ)
    (γ, x:p) : (Γ, x:A) ⊑ (Γ′, x:A′)

    Lemma (Sanity). If γ : Γ ⊑ Γ′ then Γ wf and Γ′ wf.

    Lemma. If σ : Γ ⊑ Γ′ then Γ = Σ and Γ′ = Σ′ for some Σ, Σ′.

    Lemma. If γ : Σ ⊑ Γ′ then γ = σ and Γ′ = Σ′ for some σ, Σ′.

    Lemma. If γ : Γ ⊑ Σ′ then γ = σ and Γ = Σ for some σ, Σ.


## Relating imprecisions: (γ ⊢ p ≈ q)

    X ∈ γ
    ---------------
    γ ⊢ id_X ≈ id_X

    α:=p ∈ γ
    ---------------
    γ ⊢ id_α ≈ id_α

    γ ⊢ g ≈ g′
    --------------------------
    γ ⊢ (g;tag_G) ≈ (g′;tag_G)

    ------------------ (α:=id_★ ∈ γ)
    γ ⊢ tag_α ≈ seal_α

    ------------------ (α:=id_★ ∈ γ)
    γ ⊢ seal_α ≈ tag_α

    γ ⊢ r ≈ p ⨾ q
    --------------------------- (α:=p ∈ γ)
    γ ⊢ seal_α ; r ≈ seal_α ; q

    γ ⊢  s ≈ s′    γ ⊢ t ≈ t′
    ------------------------
    γ ⊢ (s→t) ≈ (s′→t′)

    γ, X ⊢ p[id_X] ≈ p′[id_X]
    ------------------------------------
    γ ⊢ (∀X.p[id_X]) ≈ (∀X.p′[id_X])

    γ, α:=id_★ ⊢ p[seal_α] ≈ p′[seal_α]
    ------------------------------------
    γ ⊢ (να.p[seal_α]) ≈ (να.p′[seal_α])


    Lemma (Sanity). If
      γ ⊢ p ≈ q
    then
      γ : Γ ⊑ Δ
      Γ | Φ ⊢ p : A ⊑ B
      Δ | Ψ ⊢ q : A ⊑ B
      for some Γ, Δ, Φ, Ψ A, B

  (More general rules. But perhaps I don't need these.)

    γ ⊢ r ≈ p ⨾ q
    ---------------------- (α:=p ∈ γ), γ : Γ ⊑ Γ′, Γ | ∅ ⊢ r : A ⊑ ★
    γ ⊢ tag_α ≈ seal_α ; q

    γ ⊢ r ≈ p ⨾ q
    ---------------------- (α:=p ∈ γ), γ : Γ ⊑ Γ′, Γ | ∅ ⊢ r : A ⊑ ★
    γ ⊢ seal_α ; q ≈ tag_α

  (With the more general rules, the implication in the Sanity Lemma
  becomes a bi-implication.)


## Term imprecision (γ ⊢ M ⊒ M′ : r)

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
      ------------------------------------- α ∉ fv(M[αᵢ]) and q : ⋆ ⊒ A
      γ, α:=A, αᵢ:=☆ ⊢ M[αᵢ] ⊒ M′[α] : p[α]

    (⊒blame)
      -----------------
      γ ⊢ M ⊒ blame : p
      
    (x⊒x)
      ------------- x:p ∈ γ
      γ ⊢ x ⊒ x : p

    (λ⊒λ)
      γ, x:=-p ⊢ N[x] ⊒ N′[x] : q
      ---------------------------------
      γ ⊢ λx:A.N[x] ⊒ λx:A′.N′[x] : p→q

    (·⊒·)
      γ ⊢ L ⊒ L′ : p→q    γ ⊢ M ⊒ M′ : -p
      -----------------------------------
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
      γ, α:=p ⊢ N[α] ⊒ N′[α] : p
      --------------------------------- α ∉ ftv(p)
      γ ⊢ να:=A.N[α] ⊒ να:=A′.N′[α] : p

    (⊒ν)
      γ, α:=A ⊢ N ⊒ N′[α] : p
      ----------------------- α ∉ fv(p)
      γ ⊢ N ⊒ να:=A.N′[α] : p

    (⊒ν)
      γ, α:=☆ ⊢ N[α] ⊒ N′ : p
      ----------------------- α ∉ fv(p)
      γ ⊢ να:=★.N[α] ⊒ N′ : p

    (κ⊒κ)
      ---------------- tp(κ) = ι
      γ ⊢ κ ⊒ κ : id_ι

    (⊕⊒⊕)
      γ ⊢ M ⊒ M′ : id_ι    γ ⊢ N ⊒ N′ : id_ι′
      --------------------------------------- tp(⊕) = ι → ι′ → ι″
      γ ⊢ M ⊕ N ⊒ M′ ⊕ N′ : id_ι″

    (⊒+)
      γ ⊢ M ⊒ M′ : r
      --------------------- (q ⨾ s ≈ r)
      γ ⊢ M ⊒ M′ ⟨ -s ⟩ : q

    (⊒-)
      γ ⊢ M ⊒ M′ : q
      -------------------- (q ⨾ s ≈ r)
      γ ⊢ M ⊒ M′ ⟨ s ⟩ : r

    (+⊒)
      γ ⊢ M ⊒ M′ : p
      --------------------- (r ≈ t ⨾ p)
      γ ⊢ M ⟨ -t ⟩ ⊒ M′ : r

    (-⊒)
      γ ⊢ M ⊒ M′ : r
      -------------------- (r ≈ t ⨾ p)
      γ ⊢ M ⟨ t ⟩ ⊒ M′ : p

             q
        B ------> B′
        ↑       ↗ ↑
        |  ≈   /  |
        |     /   |
      s |    / r  | t    (DIAGRAM)
        |   /     |
        |  /   ≈  |
        | /       |
        A ------> A′
             p

  The following two rules are derivable.

    (+⊒+)
      γ ⊢ M ⊒ M′ : p
      ---------------------------- (q ⨾ s ≈ t ⨾ p)
      γ ⊢ M ⟨ -t ⟩ ⊒ M′ ⟨ -s ⟩ : q

    (-⊒-)
      γ ⊢ M ⊒ M′ : q
      -------------------------- (q ⨾ s ≈ t ⨾ p)
      γ ⊢ M ⟨ t ⟩ ⊒ M′ ⟨ s ⟩ : p



## Reflexivity
~~~~~~~~~~~~~~

   Define id_Γ : Γ ⊑ Γ.
   If Γ ⊢ M : A then id_Γ ⊢ M ⊑ M : id_A.



## Cast Inversion
~~~~~~~~~~~~~~~~~

   We might derive a term imprecision in more than one way:

   σ ⊢ M ⊑ M′ : p
   ------------------- r ≈ p ⨾ t
   σ ⊢ M ⊑ M′ @ +t : r
   ------------------------ s ⨾ q ≈ r
   σ ⊢ M @ +s ⊑ M′ @ +t : q

   σ ⊢ M ⊑ M′ : p
   -------------------- s ⨾ r′ ≈ p
   σ ⊢ M @ +s ⊑ M′ : r′
   ------------------------  q ≈ r′ ⨾ t
   σ ⊢ M @ +s ⊑ M′ @ +t : q

                        q
                   B ------> B′
                   ↑ \     ↗ ↑
                   |  \   /  |
                   |   \ / r |
                 s |    /    | t
                   |   / \ r′|
                   |  /   \  |
                   | /     ↘ |
                   A ------> A′
                        p

    If both derivations are possible, they give the same result.
    From either derivation, we get s ⨾ q ≈ p ⨾ t.
    With r:

       s ⨾ q ≈ r ≈ p ⨾ t

    With r′:

       s ⨾ q ≈ s ⨾ r′ ⨾ t ≈ p ⨾ t

    Further, if the r′ derivation exists, then so does the r
    derivation (take r ≈ s ⨾ q ≈ p ⨾ t).

    However, the r derivation may exist when r′ does not:

                       id_★
                   ★ ------> ★
                   ↑       ↗ ↑
                   |      /  |
                   |tag_α/   |
             tag_α |    /    | tag_α
                   |   /     |
                   |  /      |
                   | /       |
                   α ------> α
                       id_α


## Simulation notation
~~~~~~~~~~~~~~~~~~~~~~

Let ~↝,~↝′ range over =, ⊢→, ⊢↠, —→_Π, or —↠_Π.

We write

    σ ⊢ M ⊑ M′ : r
  ~↝_Π/~↝′_Π′
    σ, π ⊢ N ⊑ N′ : r

to stand for the following implication: if
  σ ⊢ M ⊑ M′ : r
  M ~↝_Π N
then there exist Π′, N′, π such that
  M′ ~↝′_Π′ N′
  π : Π ⊑ Π′
  σ, π ⊢ N ⊑ N′ : r

Write Σ^⋆ for a Σ where all α bindings are to ⋆.
Write Σ^☆ for σ where σ : ∅ ⊑ Σ^★.


Right Seal Downcast Inversion
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If
  σ ⊢ V ⊑ V′ @ -seal_α : id_α
then
  σ ⊢ V ⊑ V′ : seal_α

Proof. By case analysis on the derivation of p.

  Case ⊑-

    σ ⊢ V ⊑ V′ : seal_α
    ---------------------------- ⊑-  seal_α ≈ id_α ⨾ seal_α
    σ ⊢ V ⊑ V′ @ -seal_α : id_α
    Immediate.

  Case -⊑

    σ ⊢ V₀ ⊑ V′ @ -seal_α : q₀
    --------------------------------- -⊑  s ⨾ q₀ ≈ id_α
    σ ⊢ V₀ @ -s ⊑ V′ @ -seal_α : id_α
    Can only happen if s = q₀ = id_α, in which case recurse.

  Case +⊑

    σ ⊢ V₀ ⊑ V′ @ -seal_α : q₀
    --------------------------------- +⊑  s ⨾ id_α ≈ q₀
    σ ⊢ V₀ @ +s ⊑ V′ @ -seal_α : id_α
    Can only happen if s = q₀ = id_α, in which case recurse.

  Cases for Λ⊑ and -ν⊑ can't occur because να.p[seal_α] ≠ id_α.


Tag Factoring
~~~~~~~~~~~~~

Lemma. Tag Factoring.
If s ⨾ r ≈ t ⨾ tag_G and r ≠ id_⋆ then there exists p such that
r ≈ p ⨾ tag_G and s ⨾ p ≈ t.


Right Upcast Tag Inversion
~~~~~~~~~~~~~~~~~~~~~~~~~~
Lemma. Right Upcast Tag Inversion.
If
  σ ⊢ V ⊑ V′ @ +tag_G : r
then there exists a p such that
  r ≈ p ⨾ tag_G
and
  σ ⊢ V ⊑ V′ : p

Proof. By case analysis on the derivation of p.

  Case ⊑+

      σ ⊢ V ⊑ V′ : p
      ----------------------- ⊑+  r ≈ p ⨾ tag_G
      σ ⊢ V ⊑ V′ @ +tag_G : r

    Immediate.

  Case +s⊑, s = id

      σ ⊢ V ⊑ V′ : r
      ------------------------------- +⊑  id ⨾ r ≈ r
      σ ⊢ V @ +id_G ⊑ V′ @ +tag_G : r

    By induction.

  Case +s⊑, s ≠ id

      σ ⊢ V ⊑ V′ : r₁
      ------------------------ ⊑+  r₀ ≈ r₁ ⨾ tag_G
      σ ⊢ V ⊑ V′ @ +tag_G : r₀
      ---------------------------- +⊑  s ⨾ r ≈ r₀
      σ ⊢ V @ +s ⊑ V′ @ +tag_G : r

    By Tag Factoring, r ≈ p ⨾ tag_G and s ⨾ p ≈ r₁. Hence,

      σ ⊢ V ⊑ V′ : r₁
      -------------------- +⊑  r₁ ≈ s ⨾ p
      σ ⊢ V @ +s ⊑ V′ : p
      ---------------------------- ⊑+  r ≈ p ⨾ tag_G
      σ ⊢ V @ +s ⊑ V′ @ +tag_G : r

  Case -s⊑, s = id
  
      σ ⊢ V ⊑ V′ : r
      ------------------------------- +⊑  id ⨾ r ≈ r
      σ ⊢ V @ -id_G ⊑ V′ @ +tag_G : r

    By induction.

  Case -s⊑, s ≠ id

      σ ⊢ V ⊑ V′ : r₁
      ------------------------ ⊑+  r₀ ≈ r₁ ⨾ tag_G
      σ ⊢ V ⊑ V′ @ +tag_G : r₀
      ---------------------------- -⊑  s ⨾ r₀ ≈ r
      σ ⊢ V @ -s ⊑ V′ @ +tag_G : r

    By Tag Factoring, r ≈ p ⨾ tag_G and s ⨾ r₁ ≈ p. Hence,

      σ ⊢ V ⊑ V′ : r₁
      -------------------- -⊑  s ⨾ r₁ ≈ p
      σ ⊢ V @ -s ⊑ V′ : p
      ---------------------------- ⊑+  r ≈ p ⨾ tag_G
      σ ⊢ V @ -s ⊑ V′ @ +tag_G : r

  Case Λ⊑

      σ, α:=★ ⊢ V[α] ⊑ V′ @ +tag_G : p₀[tag_α]
      ----------------------------------------- Λ⊑
      σ ⊢ ΛX.V[X] ⊑ V′ @ +tag_G : να.p₀[seal_α]

    where r = να.p₀[seal_α]
    By induction, p₀[tag_α] ≈ p₁[tag_α] ⨾ tag_G and

      σ, α:=★ ⊢ V[α] ⊑ V′ : p₁[tag_α]
      -------------------------------------- Λ⊑
      σ ⊢ ΛX.V[X] ⊑ V′ : να.p₁[seal_α]
      ----------------------------------------------- +⊑
      σ ⊢ ΛX.V[X] ⊑ V′ @ +tag_G : να.p₀[seal_α]

      (i) να.p₀[seal_α] ≈ να.p₁[seal_α] ⨾ tag_G

  Case -ν⊑

      σ, α:=★ ⊢ V @ -s[seal_α] ⊑ V′ @ +tag_G : p₀[tag_α]
      ----------------------------------------------------- -ν⊑
      σ ⊢ V @ -(να.s[seal_α]) ⊑ V′ @ +tag_G : να.p₀[seal_α]

    where r = να.p₀[seal_α]
    By induction, p₀[tag_α] ≈ p₁[tag_α] ⨾ tag_G and

      σ, α:=★ ⊢ V @ -s[seal_α] ⊑ V′ : p₁[tag_α]
      -------------------------------------------- -ν⊑
      σ ⊢ V @ -(να.s[seal_α]) ⊑ V′ : να.p₁[seal_α]
      ----------------------------------------------------- +⊑
      σ ⊢ V @ -(να.s[seal_α]) ⊑ V′ @ +tag_G : να.p₀[seal_α]

      (i) να.p₀[seal_α] ≈ να.p₁[seal_α] ⨾ tag_G



Left Tag Inversion
~~~~~~~~~~~~~~~~~~

  σ ⊢ V ⊑ M′ : tag_G
  -------------------------- +⊑  tag_G ⨾ id_⋆ ≈ r
  σ ⊢ V @ +tag_G ⊑ M′ : id_⋆
  ------------------------------------ -⊑  tag_G ⨾ id_⋆ ≈ r
  σ ⊢ V @ +tag_G @ -tag_G ⊑ M′ : tag_G


Left Tag Inversion 1.

If σ ⊢ V @ +tag_G ⊑ M′ : q
then q = id_⋆ and σ ⊢ V ⊑ M′ : tag_G.

Proof. By induction on the derivation.

  Case +⊑

      σ ⊢ V ⊑ M′ : r
      ----------------------- +⊑  tag_G ⨾ q ≈ r
      σ ⊢ V @ +tag_G ⊑ M′ : q

    The only solution is q = id_⋆, r = tag_G.

  Case ⊑+

      σ ⊢ V @ +tag_G ⊑ M₀′ : p₀
      ------------------------------ ⊑+  r₀ ≈ p₀ ⨾ t
      σ ⊢ V @ +tag_G ⊑ M₀′ @ +t : r₀

    By induction

      σ ⊢ V ⊑ M₀′ : tag_G
      --------------------------- +⊑
      σ ⊢ V @ +tag_G ⊑ M₀′ : id_⋆

    Taking p₀ = id_⋆, the only solution is r₀ = id_⋆, t = id_⋆.
    So we have

      σ ⊢ V ⊑ M₀′ : tag_G
      --------------------------- ⊑+
      σ ⊢ V ⊑ M₀′ @ +id_⋆ : tag_G      
      ----------------------------------- +⊑
      σ ⊢ V @ +tag_G ⊑ M₀′ @ +id_⋆ : id_⋆


  Case ⊑-

      σ ⊢ V @ +tag_G ⊑ M₀′ : r₀
      ------------------------------ ⊑-  r₀ ≈ p₀ ⨾ t
      σ ⊢ V @ +tag_G ⊑ M₀′ @ -t : p₀

    By induction

      σ ⊢ V ⊑ M₀′ : tag_G
      --------------------------- +⊑
      σ ⊢ V @ +tag_G ⊑ M₀′ : id_⋆

    Taking r₀ = id_⋆, the only solution is p₀ = id_⋆, t = id_⋆.
    So we have

      σ ⊢ V ⊑ M₀′ : tag_G
      --------------------------- ⊑-
      σ ⊢ V ⊑ M₀′ @ -id_⋆ : tag_G      
      ----------------------------------- +⊑
      σ ⊢ V @ +tag_G ⊑ M₀′ @ +id_⋆ : id_⋆


Left Tag Inversion 2.

If σ ⊢ V @ -tag_G ⊑ M′ : r
then r = tag_G and σ ⊢ V ⊑ M′ : id_⋆.

Proof. By induction on the derivation.

  Case -⊑

      σ ⊢ V ⊑ M′ : q      
      ----------------------- -⊑  tag_G ⨾ q ≈ r
      σ ⊢ V @ -tag_G ⊑ M′ : r

    The only solution is q = id_⋆, r = tag_G.

  Case ⊑+

      σ ⊢ V @ -tag_G ⊑ M₀′ : p₀
      ------------------------------ ⊑+  r₀ ≈ p₀ ⨾ t
      σ ⊢ V @ -tag_G ⊑ M₀′ @ +t : r₀

    By induction

      σ ⊢ V ⊑ M₀′ :  id_⋆
      ---------------------------- -⊑
      σ ⊢ V @ -tag_G ⊑ M₀′ : tag_G

    Taking p₀ = tag_G the only solution is r₀ = tag_G, t = id_⋆.
    So we have

      σ ⊢ V ⊑ M₀′ : id_⋆
      -------------------------- ⊑+
      σ ⊢ V ⊑ M₀′ @ +id_⋆ : id_⋆
      ------------------------------------ -⊑
      σ ⊢ V @ -tag_G ⊑ M₀′ @ +id_⋆ : tag_G

  Case ⊑-

      σ ⊢ V @ -tag_G ⊑ M₀′ : r₀
      ------------------------------ ⊑-  r₀ ≈ p₀ ⨾ t
      σ ⊢ V @ -tag_G ⊑ M₀′ @ -t : p₀

    By induction

      σ ⊢ V ⊑ M₀′ :  id_⋆
      ---------------------------- -⊑
      σ ⊢ V @ -tag_G ⊑ M₀′ : tag_G

    Taking p₀ = tag_G the only solution is r₀ = tag_G, t = id_⋆.
    So we have

      σ ⊢ V ⊑ M₀′ : id_⋆
      -------------------------- ⊑-
      σ ⊢ V ⊑ M₀′ @ -id_⋆ : id_⋆
      ------------------------------------ -⊑
      σ ⊢ V @ -tag_G ⊑ M₀′ @ -id_⋆ : tag_G


Left Seal Inversion
~~~~~~~~~~~~~~~~~~~

  σ ⊢ V ⊑ M : q
  ----------------------- -⊑  seal_α ⨾ q ≈ r
  σ ⊢ V @ -seal_α ⊑ M : r
  --------------------------------- +⊑  seal_α ⨾ q ≈ r
  σ ⊢ V @ -seal_α @ +seal_α ⊑ M : q

Left Seal Inversion 1.

If σ ⊢ V @ -seal_α ⊑ M : r
then there exists a q such that
seal_α ⨾ q ≈ r and σ ⊢ V ⊑ M : q.

Proof by induction on the derivation.

  Case -⊑

      σ ⊢ V ⊑ M : q
      ----------------------- -⊑  seal_α ⨾ q ≈ r
      σ ⊢ V @ -seal_α ⊑ M : r

    Immediate.

  Case ⊑+

      σ ⊢ V @ -seal_α ⊑ M : r₀
      ----------------------------- ⊑+  r ≈ r₀ ⨾ t
      σ ⊢ V @ -seal_α ⊑ M @ +t : r

    By induction

      σ ⊢ V ⊑ M : q₀
      ------------------------ -⊑  seal_α ⨾ q₀ ≈ r₀
      σ ⊢ V @ -seal_α ⊑ M : r₀

    So we have

      σ ⊢ V ⊑ M : q₀
      ------------------- ⊑+  q ≈ q₀ ⨾ t
      σ ⊢ V ⊑ M @ +t : q
      -------------------------- -⊑  seal_α ⨾ q ≈ r
      σ ⊢ V -seal_α ⊑ M @ +t : r

    by taking q = q₀ ⨾ t, in which case
    seal_α ⨾ q ≈ seal_α ⨾ q₀ ⨾ t ≈ r₀ ⨾ t ≈ r.

  Case ⊑-

      σ ⊢ V @ -seal_α ⊑ M : r₀
      ----------------------------- ⊑-  r₀ ≈ r ⨾ t
      σ ⊢ V @ -seal_α ⊑ M @ -t : r

    By induction

      σ ⊢ V ⊑ M : q₀
      ------------------------ -⊑  seal_α ⨾ q₀ ≈ r₀
      σ ⊢ V @ -seal_α ⊑ M : r₀

    So we have

      σ ⊢ V ⊑ M : q₀
      ------------------- ⊑-  q₀ ≈ q ⨾ t
      σ ⊢ V ⊑ M @ -t : q
      ---------------------------- -⊑  seal_α ⨾ q ≈ r
      σ ⊢ V @ -seal_α ⊑ M @ -t : r

    How do we know such a q exists?
    Either r = seal_α ⨾ q′, in which case we can take q = q′.
    Or r = tag_α, in which case α:=A and q : A ⊑ ⋆ exists.
    (Because A is typed under σ, it has no X's.)


Left Seal Inversion 2.

If σ ⊢ V @ +seal_α ⊑ M : q
then there exists a r such that
seal_α ⨾ q ≈ r and σ ⊢ V ⊑ M : r.

Proof by induction on the derivation.

  Case +⊑

      σ ⊢ V ⊑ M : r
      ----------------------- -⊑  seal_α ⨾ q ≈ r
      σ ⊢ V @ +seal_α ⊑ M : q

    Immediate.

  Case ⊑+

      σ ⊢ V @ +seal_α ⊑ M : q₀
      ----------------------------- ⊑+  q ≈ q₀ ⨾ t
      σ ⊢ V @ +seal_α ⊑ M @ +t : q

    By induction

      σ ⊢ V ⊑ M : r₀
      ------------------------ -⊑  seal_α ⨾ q₀ ≈ r₀
      σ ⊢ V @ +seal_α ⊑ M : q₀

    So we have

      σ ⊢ V ⊑ M : r₀
      ------------------- ⊑+  r ≈ r₀ ⨾ t
      σ ⊢ V ⊑ M @ +t : r
      ---------------------------- -⊑  seal_α ⨾ q ≈ r
      σ ⊢ V @ +seal_α ⊑ M @ +t : q

    (We know r exists because we can take r = seal_α ⨾ q.
    Then r₀ ⨾ t ≈ seal_α ⨾ q₀ ⨾ t ≈ seal_α ⨾ q = r.)


  Case ⊑-

      σ ⊢ V @ +seal_α ⊑ M : q₀
      ----------------------------- ⊑-  q₀ ≈ q ⨾ t
      σ ⊢ V @ +seal_α ⊑ M @ -t : q

    By induction

      σ ⊢ V ⊑ M : r₀
      ------------------------ -⊑  seal_α ⨾ q₀ ≈ r₀
      σ ⊢ V @ +seal_α ⊑ M : q₀

    So we have

      σ ⊢ V ⊑ M : r₀
      ------------------- ⊑-  r₀ ≈ r ⨾ t
      σ ⊢ V ⊑ M @ -t : r
      ---------------------------- -⊑  seal_α ⨾ q ≈ r
      σ ⊢ V @ +seal_α ⊑ M @ -t : q

    (We know r exists because we can take r = seal_α ⨾ q.
    Then r₀ ≈ seal_α ⨾ q₀ ≈ seal_α ⨾ q ⨾ t = r ⨾ t.)



Right ν Upcast Lemma
~~~~~~~~~~~~~~~~~~~~

    σ ⊢ V ⊑ V′ : ∀X.p[id_X]
    --------------------------------------------- ⊑+ (i)
    σ ⊢ V ⊑ V′ @ +(να.t[seal_α]) : (να.r[seal_α])

    (i) (να.r[seal_α]) ≈ (∀X.p[id_X]) ⨾ (να.t[seal_α])

  =/—↠_{Π^★}

    σ, α:=☆, Π^☆ ⊢ V ⊑ W′ : να.r[seal_α]

Proof by mutual induction with the upcast and downcast lemmas,
on the derivation of +(να.t[seal_α]) and the derivation of V ⊑ V′.

  Case Λ⊑Λ

      σ, X ⊢ V[X] ⊑ V′[X] : p[id_X]
      --------------------------------------- Λ⊑Λ
      σ ⊢ (ΛX.V[X]) ⊑ (ΛX.V′[X]) : ∀X.p[id_X]
      ------------------------------------------------------------- ⊑+ (i)
      σ ⊢ (ΛX.V[X]) ⊑ (ΛX.V′[X]) @ +(να.t[seal_α]) : (να.r[seal_α])

      (i)  (να.r[seal_α]) ≈ (∀X.p[id_X]) ⨾ (να.t[seal_α])

    =/—↠_{α:=★}   

      σ, α:=id_⋆ ⊢ V[α] ⊑ V′[α] : p[id_α]
      ------------------------------------------------- ⊑+ (ii)
      σ, α:=id_⋆ ⊢ V[α] ⊑ V′[α] @ +t[seal_α] : r[tag_α]
      --------------------------------------------------------------- Λ⊑
      σ, α:=☆ ⊢ (ΛX.V[X]) ⊑  V′[α] @ +t[seal_α] : (να.r[seal_α])

      (ii)  r[tag_α] ≈ p[id_α] ⨾ t[seal_α]

    =/—↠_{Π^★}  (upcast lemma, on a smaller cast)    

      σ, α:=id_⋆, Π^☆ ⊢ V[α] ⊑ W′ : r[tag_α]    
      ---------------------------------------------- Λ⊑
      σ, α:=☆, Π^☆ ⊢ (ΛX.V[X]) ⊑ W′ : (να.r[seal_α])

    (see Example 14)

  Case +⊑

      σ ⊢ V ⊑ V′ : ∀X.p₀[id_X]
      ---------------------------------------- +⊑  (i)
      σ ⊢ V @ +(∀X.s[id_X]) ⊑ V′ : ∀X.p₁[id_X]
      -------------------------------------------------------------- ⊑+ (ii)
      σ ⊢ V @ +(∀X.s[id_X]) ⊑ V′ @ +(να.t[seal_α]) : (να.p₂[seal_α])

      (i)   (∀X.s[id_X]) ⨾ (∀X.p₁[id_X]) ≈ (∀X.p₀[id_X])
      (ii)  (να.p₂[seal_α]) ≈ (∀X.p₁[id_X]) ⨾ (να.t[seal_α])

    =/=

      σ ⊢ V ⊑ V′ : ∀X.p₀[id_X]
      ----------------------------------------------  ⊑+ (iii)
      σ ⊢ V ⊑ V′ @ +(να.t[seal_α]) : (να.p₃[seal_α])
      -------------------------------------------------------------- +⊑ (iv)  
      σ ⊢ V @ +(∀X.s[id_X]) ⊑ V′ @ +(να.t[seal_α]) : (να.p₃[seal_α])

      (iii)  (να.p₃[seal_α]) ≈ (∀X.p₀[id_X]) ⨾ (να.t[seal_α])
      (iv)   (∀X.s[id_X]) ⨾ (να.p₂[seal_α]) ≈ (να.p₃[seal_α])

    =/—↠_{Π^★}  (by induction, V′ @ +(να.t[seal_α]) —↠_{Π^★} W′)

      σ, Π^☆ ⊢ V ⊑ W′ : (να.p₃[seal_α])
      ------------------------------------------------- +⊑ (iv) 
      σ, Π^☆ ⊢ V @ +(∀X.s[id_X]) ⊑ W′ : (να.p₂[seal_α])

    We define p₃ by (iii), and (iv) follows because
      (∀X.s[id_X]) ⨾ (να.p₂[seal_α]) ≈(ii)
      (∀X.s[id_X]) ⨾ (∀X.p₁[id_X]) ⨾ (να.t[seal_α]) ≈(i)
      (∀X.p₀[id_X]) ⨾ (να.t[seal_α]) ≈(iii)
      (να.p₃[seal_α])        

  Case -⊑

      σ ⊢ V ⊑ V′ : ∀X.p₀[id_X]
      ---------------------------------------- +⊑ (i)
      σ ⊢ V @ -(∀X.s[id_X]) ⊑ V′ : ∀X.p₁[id_X]
      -------------------------------------------------------------- ⊑+ (ii)
      σ ⊢ V @ -(∀X.s[id_X]) ⊑ V′ @ +(να.t[seal_α]) : (να.p₂[seal_α])
      (i)   (∀X.s[id_X]) ⨾ (∀X.p₀[id_X]) ≈ (∀X.p₁[id_X])
      (ii)  (να.p₂[seal_α]) ≈ (∀X.p₁[id_X]) ⨾ (να.t[seal_α])

    =/=

      σ ⊢ V ⊑ V′ : ∀X.p₀[id_X]
      ----------------------------------------------  ⊑+ (iii)
      σ ⊢ V ⊑ V′ @ +(να.t[seal_α]) : (να.p₃[seal_α])
      ------------------------------------------------ +⊑ (iv)
      σ, Π^☆ ⊢ V @ -(∀X.s[id_X]) ⊑ W′ : (να.p₂[seal_α])
      (iii)  (να.p₃[seal_α]) ≈ (∀X.p₀[id_X]) ⨾ (να.t[seal_α])
      (iv)   (∀X.s[id_X]) ⨾ (να.p₃[seal_α]) ≈ (να.p₂[seal_α])

    =/—↠_{Π^★}  (by induction, V′ @ +(να.t[seal_α]) —↠_{Π^★} W′)

      σ, Π^☆ ⊢ V ⊑ W′ : (να.p₃[seal_α])
      ------------------------------------------------ +⊑ (iv)
      σ, Π^☆ ⊢ V @ -(∀X.s[id_X]) ⊑ W′ : (να.p₂[seal_α])

      We define p₃ by (iii), and (iv) follows because
        (∀X.s[id_X]) ⨾ (να.p₃[seal_α]) ≈(iii) 
        (∀X.s[id_X]) ⨾ (∀X.p₀[id_X]) ⨾ (να.t[seal_α]) ≈(i)
        (∀X.p₁[id_X]) ⨾ (να.t[seal_α]) ≈(ii)
        (να.p₂[seal_α])        

  Case Λ⊑/⊑-

      σ, α:=★ ⊢ V[α] ⊑ V′ : p₀[tag_α]
      ---------------------------------- Λ⊑
      σ ⊢ ΛX.V[X] ⊑ V′ : (να.p₀[seal_α])
      -------------------------------------------------- ⊑- (i)
      σ ⊢ ΛX.V[X] ⊑ V′ @ -(να.s[seal_α]) : (∀X.p₁[id_X])
      ---------------------------------------------------------------------- ⊑+ (ii)
      σ ⊢ ΛX.V[X] ⊑ V′ @ -(να.s[seal_α]) @ +(να.t[seal_α]) : (να.p₂[seal_α])

      (i)   (να.p₀[seal_α]) ≈ (∀X.p₁[id_X]) ⨾ (να.s[seal_α])
      (ii)  (να.p₂[seal_α]) ≈ (∀X.p₁[id_X]) ⨾ (να.t[seal_α])

    =/—↠_{α:=★}

      σ, α:=★ ⊢ V[α] ⊑ V′ : p₀[tag_α]
      ---------------------------------------------- ⊑- (iii)
      σ, α:=id_★ ⊢ V[α] ⊑ V′ @ -s[tag_α] : p₁[id_α]
      -------------------------------------------------------------- ⊑+ (iv)
      σ, α:=id_★ ⊢ ΛX.V[X] ⊑ V′ @ -s[tag_α] @ +t[seal_α] : p₂[tag_α]
      ----------------------------------------------------------------- Λ⊑
      σ, α:=☆ ⊢ ΛX.V[X] ⊑ V′ @ -s[tag_α] @ +t[seal_α] : (να.p₂[seal_α])

      (iii)  p₀[tag_α] ≈ p₁[id_α] ⨾ s[tag_α]
      (iv)   p₂[tag_α] ≈ p₁[id_α] ⨾ t[seal_α]

    Then V′ @ -s[tag_α] is a value, and we invoke Right Upcast on smaller casts t[seal_α].

    (see Example 20)

  Case -⊑-

      σ ⊢ V ⊑ V′ : p₀
      ------------------------------------------------------------- -⊑- (i)
      σ ⊢ V @ -(να.s₀[seal_α]) ⊑ V @ -(να.t₀[seal_α]) : ∀X.p₁[id_X]
      --------------------------------------------------------------------------------- ⊑+ (ii)
      σ ⊢ V @ -(να.s₀[seal_α]) ⊑ V @ -(να.t₀[seal_α]) @ +(να.t[seal_α]) : να.p₂[seal_α]

      (i)   (να.s₀[seal_α]) ⨾ p₀ ≈ (∀X.p₁[id_X]) ⨾ (να.t₀[seal_α])
      (ii)  (να.p₂[seal_α]) ≈ (∀X.p₁[id_X]) ⨾ (να.t[seal_α])

    =/⊢→
      σ ⊢ V @ -(να.s₀[seal_α]) ⊑ (να:=⋆. (V @ -(να.t₀[seal_α])) α) @ +t[seal_α] : να.p₂[seal_α]
    =/—→_{α:=★}
      σ, α:=☆ ⊢ V @ -(να.s₀[seal_α]) ⊑ (V @ -(να.t₀[seal_α])) α @ +t[seal_α] : να.p₂[seal_α]
    =/⊢→

      σ ⊢ V ⊑ V′ : p₀      
      ---------------------------------------------------- -⊑- (iii)
      σ, α:=☆ ⊢ V @ -s₀[tag_α] ⊑ V @ -t₀[tag_α] : p₁[id_α]
      ------------------------------------------------------------------ ⊑+ (iv)
      σ, α:=☆ ⊢ V @ -s₀[tag_α] ⊑ V @ -t₀[tag_α] @ +t[seal_α] : p₂[tag_α]            
      ---------------------------------------------------------------------------- -ν⊑
      σ, α:=☆ ⊢ V @ -(να.s₀[seal_α]) ⊑ V @ -t₀[tag_α] @ +t[seal_α] : να.p₂[seal_α]      

      (iii)  s₀[tag_α] ⨾ p₀ ≈ p₁[id_α] ⨾ t₀[tag_α] 
      (iv)   p₂[tag_α] ≈ p₁[id_α] ⨾ t[seal_α]

    (see Example 21)



Right Upcast Lemma
~~~~~~~~~~~~~~~~~~

    σ ⊢ V ⊑ V′ : p
    ------------------- ⊑+  r ≈ p ⨾ t
    σ ⊢ V ⊑ V′ @ +t : r
  =/—↠_{Σ^★}
    σ, Σ^☆ ⊢ V ⊑ W′ : r

Proof. By mutual induction with the Right Upcast ν and Downcast Lemmas,
on the derivations of t and V ⊑ V′.
  
  Case id_a

      σ ⊢ V ⊑ V′ @ +id_a : r
    =/—→
      σ ⊢ V ⊑ V′ : r

  Case (s→t)

      σ ⊢ V ⊑ V′ @ +(s→t) : r
      rhs is a value

  Case (∀X.s[id_X])

      σ ⊢ V ⊑ V′ @ +(∀X.s[X]) : r
      rhs is a value

  Case (να.s[seal_α])

      σ ⊢ V ⊑ V′ @ +(να.s[seal_α]) : r
      by ν Right Upcast Lemma

  Case (s;t)

      σ ⊢ V ⊑ V′ @ +(s;t) : r
    =/—→
      σ ⊢ V ⊑ V′ @ +s @ +t : r
    =/—↠_{Σ^★} (induction)
      σ, Σ^☆ ⊢ V ⊑ W′ @ +t : r
    =/—↠_{Π^★} (induction)      
      σ, Σ^☆, Π^☆ ⊢ V ⊑ W″ : r

   Case tag_G

      σ ⊢ V ⊑ V′ @ +tag_G : r
      rhs is a value

   Case seal_α   

      σ ⊢ V ⊑ V′ : id_α
      ----------------------------- ⊑+  seal_α ≈ id_α ⨾ seal_α
      σ ⊢ V ⊑ V′ @ +seal_α : seal_α
      by canonical values, V′ = V″ @ -seal_α and by Right Seal Inversion
    =/=
      σ ⊢ V ⊑ V″ : seal_α
      --------------------------- ⊑-  seal_α ≈ id_α ⨾ seal_α
      σ ⊢ V ⊑ V″ @ -seal_α : id_α
      --------------------------------------- ⊑+  seal_α ≈ id_α ⨾ seal_α
      σ ⊢ V ⊑ V″ @ -seal_α @ +seal_α : seal_α
    =/⊢→
      σ ⊢ V ⊑ V″ : r


Right Downcast Lemma
~~~~~~~~~~--~~~~~~~~

    σ ⊢ V ⊑ V′ : r
    ------------------- ⊑-  r ≈ p ⨾ t
    σ ⊢ V ⊑ V′ @ -t : p
  =/—↠_{Σ^★}
    σ, Σ^☆ ⊢ V ⊑ W′ : p

Proof. By mutual induction with the Right Upcast ν and Upcast Lemmas,
on the derivations of t and V ⊑ V′.
  
  Case id_a

      σ ⊢ V ⊑ V′ @ -id_a : p
    =/—→
      σ ⊢ V ⊑ V′ : r

  Case (s→t)

      σ ⊢ V ⊑ V′ @ -(s→t) : p
      rhs is a value

  Case (∀X.s[id_X])

      σ ⊢ V ⊑ V′ @ -(∀X.s[X]) : p
      rhs is a value

  Case (να.s[seal_α])

      σ ⊢ V ⊑ V′ @ -(να.s[seal_α]) : p
      rhs is a value

  Case (s;t)

      σ ⊢ V ⊑ V′ @ -(s;t) : p
    =/—→
      σ ⊢ V ⊑ V′ @ -t @ -s : p
    =/—↠_{Σ^★} (induction)
      σ, Σ^☆ ⊢ V ⊑ W′ @ -s : p
    =/—↠_{Π^★} (induction)      
      σ, Σ^☆, Π^☆ ⊢ V ⊑ W″ : p

  Case tag_G
   
      σ ⊢ V ⊑ V′ : r
      ----------------------- ⊑-  r ≈ p ⨾ tag_G
      σ ⊢ V ⊑ V′ @ -tag_G : p
      by canonical values, V′ = V″ @ +tag_G and Right Tag Upcast Inversion
      σ ⊢ V ⊑ V″ : p
      ----------------------- ⊑-  r ≈ p ⨾ tag_G
      σ ⊢ V ⊑ V″ @ +tag_G : r
      -------------------------------- ⊑-  r ≈ p ⨾ tag_G
      σ ⊢ V ⊑ V″ @ +tag_G @ -tag_G : p
    =/—→
      σ ⊢ V ⊑ V″ : p

  Case seal_α

      σ ⊢ V ⊑ V′ @ -seal_α : p
      rhs is a value


Catchup Lemma
~~~~~~~~~~~~~

    σ ⊢ V ⊑ M : p
  =/—↠_{Π^★}
    σ, Π^☆ ⊢ V ⊑ W : p

Proof. By induction on the proof of the hypothesis.

  Case +⊑

      σ ⊢ V ⊑ M : r
      ------------------ +⊑  s ⨾ q ≈ r 
      σ ⊢ V @ +s ⊑ M : q
    =/—↠_{Π^★}
      σ, Π^☆ ⊢ V ⊑ W′ : r
      ------------------- +⊑  s ⨾ q ≈ r 
      σ, Π^☆ ⊢ V @ +s ⊑ W′ : q

  Case -⊑

      σ ⊢ V ⊑ M : q
      ------------------ -⊑  s ⨾ q ≈ r
      σ ⊢ V @ -s ⊑ M : r
    =/—↠_{Π^★}
      σ, Π^☆ ⊢ V ⊑ W′ : q
      ------------------- -⊑  s ⨾ q ≈ r 
      σ, Π^☆ ⊢ V @ -s ⊑ W′ : r

  Case Λ⊑

    σ, α:=★ ⊢ V[α] ⊑ N′ : p[tag_α]
    --------------------------------------- Λ⊑
    σ ⊢ (ΛX.V[X]) ⊑ N′ : να.p[seal_α]
  =/—↠_{Π^★} (induction)
    σ, α:=★, Π^☆ ⊢ V[α] ⊑ V′ : p[tag_α]
    ------------------------------------- Λ⊑
    σ, Π^☆ ⊢ (ΛX.V[X]) ⊑ M : να.p[seal_α]

  Case -ν⊑

    σ, α:=★ ⊢ V @ -s[tag_α] ⊑ N′ : p[tag_α]
    ------------------------------------------- -ν⊑
    σ ⊢ V @ -(να.s[seal_α]) ⊑ N′ : να.p[seal_α]
  =/—↠_{Π^★} (induction)
    σ, α:=★, Π^☆ ⊢ V @ -s[tag_α] ⊑ V′ : p[tag_α]
    ----------------------------------------------- -ν⊑
    σ, Π^☆ ⊢ V @ -(να.s[seal_α]) ⊑ M : να.p[seal_α]

    Note that V @ -s[tag_α] is itself a value, so induction applies.

  Case ⊑+

    σ ⊢ V ⊑ M′ : p
    ------------------- ⊑+  r ≈ p ⨾ t
    σ ⊢ V ⊑ M′ @ +t : r
  =/—↠_{Σ^★} (induction)
    σ, Σ^☆ ⊢ V ⊑ V′ : p
    ------------------------ ⊑+  r ≈ p ⨾ t
    σ, Σ^☆ ⊢ V ⊑ V′ @ +t : r
  =/—↠_{Π^★} (Right Upcast Lemma)
    σ, Σ^☆, Π^☆ ⊢ V ⊑ W′ : r

  Case ⊑-

    σ ⊢ V ⊑ M′ : r
    ------------------- ⊑-  r ≈ p ⨾ t
    σ ⊢ V ⊑ M′ @ -t : p
  =/—↠_{Σ^★} (induction)
    σ, Σ^☆ ⊢ V ⊑ V′ : r
    ------------------------ ⊑-  r ≈ p ⨾ t
    σ, Σ^☆ ⊢ V ⊑ V′ @ -t : p
  =/—↠_{Π^★} (Right Downcast Lemma)
    σ, Σ^☆, Π^☆ ⊢ V ⊑ W′ : p


Wrap Downcast Lemma
~~~~~~~~~~~~~~~~~~~

    σ ⊢ V @ -(s→t) ⊑ V′ : p→q    σ ⊢ W ⊑ W′ : p
    -------------------------------------------
    σ ⊢ (V @ -(s→t)) W ⊑ V′ W′ : q
  ⊢→/—↠_{Π^★}
    σ, Π^☆ ⊢ V (W @ +s) @ -t ⊑ N′ : p

Proof. By induction on the derivation of σ ⊢ V @ -(s→t) ⊑ V′ : p→q.

  Case -⊑

      σ ⊢ V ⊑ V′ : s₁→t₁
      ----------------------------- -⊑ (i)
      σ ⊢ (V @ -(s→t)) ⊑ V′ : s₂→t₂           σ ⊢ W ⊑ W′ ⊢ s₂
      ------------------------------------------------------- ·⊑·
      σ ⊢ (V @ -(s→t)) W ⊑ V′ W′ : t₂
      (i) (s→t)⨾(s₁→t₁) ⊑ (s₂→t₂)
    ⊢→
                            W ⊑ W′ : s₂
                            --------------- +⊑  s⨾s₁ ⊑ s₂
      σ ⊢ V ⊑ V′ : s₁→t₁    W @ +s ⊑ W′ : s₁
      -------------------------------------- ·⊑·
      σ ⊢ (V (W @ +s)) ⊑ V′ W′ : t₁
      ---------------------------------- -⊑  t⨾t₁ ⊑ t₂
      σ ⊢ (V (W @ +s)) @ -t ⊑ V′ W′ : t₂

  Case ⊑+
         
    We are given
    
      σ ⊢ (V @ -(s→t)) ⊑ V′ : s₄→t₄
      ------------------------------------------ ⊑+ (i)
      σ ⊢ (V @ -(s→t)) ⊑ (V′ @ +(s₃→t₃)) : s₂→t₂           σ ⊢ W ⊑ W′ : s₂
      -------------------------------------------------------------------- ·⊑·
      σ ⊢ (V @ -(s→t)) W ⊑ (V′ @ +(s₃→t₃)) W′ : t₂
      (i)  s₂→t₂ ⊑ (s₄→t₄)⨾(s₃→t₃)   

    From this we derive
    
      σ ⊢ W ⊑ W′ : s₂
      --------------------- ⊑-  s₂ ⊑ s₄⨾s₃
      σ ⊢ W ⊑ W′ @ -s₃ : s₄
    =/—↠_{Π₁^★}
      σ, Π₁^☆ ⊢ W ⊑ W″ : s₄

    Now apply induction hypothesis where W′ = W″, p = s₄, q = t₄.
    We know V′ W″ —↠_{Π₂^★} N′ and σ ⊢ V (W @ +s) @ -t ⊑ N′ : t₄.
    Hence

                 (V′ @ +(s₃→t₃)) W′
      ⊢→         V′ (W′ @ -s₃) @ +t₃
      —↠_{Π₁^★}  V′ W″ @ +t₃
      —↠_{Π₂^★}  N′ @ +t₃

    and 

      σ, Π₁^☆, Π₂^☆ ⊢ V (W @ +s) @ -t ⊑ N′ : t₄        
      ----------------------------------------------- ⊑+  t₂ ⊑ t₄⨾t₃
      σ, Π₁^☆, Π₂^☆ ⊢ V (W @ +s) @ -t ⊑ N′ @ +t₃ : t₂

  Case ⊑-

    We are given
    
      σ ⊢ (V @ -(s→t)) ⊑ V′ : s₂→t₂
      ------------------------------------------ ⊑- (i)
      σ ⊢ (V @ -(s→t)) ⊑ (V′ @ -(s₃→t₃)) : s₄→t₄           σ ⊢ W ⊑ W′ : s₄
      -------------------------------------------------------------------- ·⊑·
      σ ⊢ (V @ -(s→t)) W ⊑ (V′ @ -(s₃→t₃)) W′ : t₄
      (i)  s₂→t₂ ⊑ (s₄→t₄)⨾(s₃→t₃)

    From this we derive
    
      σ ⊢ W ⊑ W′ : s₄
      --------------------- ⊑+  s₂ ⊑ s₄⨾s₃
      σ ⊢ W ⊑ W′ @ +s₃ : s₂
    =/—↠_{Π₁^★}
      σ, Π₁^☆ ⊢ W ⊑ W″ : s₂

    Now apply induction hypothesis where W′ = W″, p = s₂, q = t₂.
    We know V′ W″ —↠ N′ and σ ⊢ V (W @ +s) @ -t ⊑ N′ : t₂.

    Hence

                 (V′ @ -(s₃→t₃)) W′
      ⊢→         V′ (W′ @ +s₃) @ -t₃
      —↠_{Π₁^★}  V′ W″ @ -t₃
      —↠_{Π₂^★}  N′ @ -t₃

    and 

        σ, Π₁^☆, Π₂^☆ ⊢ V (W @ +s) @ -t ⊑ N′ : t₂        
        ----------------------------------------------- ⊑+  t₂ ⊑ t₄⨾t₃
        σ, Π₁^☆, Π₂^☆ ⊢ V (W @ +s) @ -t ⊑ N′ @ -t₃ : t₄


Wrap Upcast Lemma
~~~~~~~~~~~~~~~~~

  Similar to Wrap Downcast.


Gradual Guarantee
~~~~~~~~~~~~~~~~~

    σ ⊢ M ⊑ M′ : p
  —→_Π/—↠_Π′    π : Π ⊑ Π′
    σ, π ⊢ N ⊑ N′ : p

Proof: By induction on the derivations of σ ⊢ M ⊑ M′ : p and M —→_Π N.

    κ₁ ⊕ κ₂  ⊢→  δ(⊕)(κ₁,κ₂)

      (⊕⊑⊕)
      
        σ ⊢ κ₁ ⊑ κ₁ : id_ι₁    σ ⊢ κ₂ ⊑ κ₂ : id_ι₂
        ------------------------------------------ ⊕⊑⊕
        σ ⊢ κ₁ ⊕ κ₂ ⊑ κ₁ ⊕ κ₂ : id_ι₃
      ⊢→/⊢→
        σ ⊢ δ(⊕)(κ₁,κ₂) ⊑ δ(⊕)(κ₁,κ₂) : id_ι₃

    (λx.N[x]) W  ⊢→  N[W]

      Induct on the derivation of σ ⊢ λx.N[x] ⊑ N′ : p→q and use catchup.

      (λ⊑λ)

          σ, x:p ⊢ N[x] ⊑ N′[x] : q
          ---------------------------- λ⊑λ
          σ ⊢ λx.N[x] ⊑ λx.N′[x] : p→q        σ ⊢ W ⊑ W′ : p
          -------------------------------------------------- ·⊑·
          σ ⊢ (λx.N[x]) W ⊑ (λx.N′[x]) W′ : q
        ⊢→/⊢→
          σ ⊢ N[W] ⊑ N′[W′] : q

          (assumes a suitable substitution lemma)

      → upcast (⊑+)

         Let V = λx.N[x]. (This means ⊑+ must be used, so we don't need inversion.)

          σ ⊢ V ⊑ V′ : p′→q′
          ------------------------- ⊑+  p→q ≈ (p′→q′)⨾(s→t)
          σ ⊢ V ⊑ V′ @ +(s→t) : p→q                            σ ⊢ W ⊑ W′ : p
          ------------------------------------------------------------------- ·⊑·
          σ ⊢ V W ⊑ (V′ @ +(s→t)) W′ : q
        =/⊢→
                                σ ⊢ W ⊑ W′ : p
                                -------------------- ⊑-  p ≈ p′⨾t 
          σ ⊢ V ⊑ V′ : p′→q′    σ ⊢ W ⊑ W′ @ -s : p′
          ------------------------------------------ ·⊑·
          σ ⊢ V W ⊑ V′ (W′ @ -s) : q′                   
          -------------------------------- ⊑+  q ≈ q′⨾t
          σ ⊢ V W ⊑ V′ (W′ @ -s) @ +t : q

          (and then induction) [TODO: Check]

      → downcast (⊑-)

          Let V = λx.N[x].

          σ ⊢ V ⊑ V′ : p→q
          --------------------------- ⊑-  p→q ≈ (p′→q′)⨾(s→t)
          σ ⊢ V ⊑ V′ @ -(s→t) : p′→q′                            σ ⊢ W ⊑ W′ : p′
          --------------------------------------------------------------------- ·⊑·
          σ ⊢ V W ⊑ (V′ @ -(s→t)) W′ : q′
        =/⊢→
                              σ ⊢ W ⊑ W′ : p′
                              ------------------- ⊑+  p ≈ p′⨾t 
          σ ⊢ V ⊑ V′ : p→q    σ ⊢ W ⊑ W′ @ +s : p
          ------------------------------------------ ·⊑·
          σ ⊢ V W ⊑ V′ (W′ @ +s) : q                   
          -------------------------------- ⊑-  q ≈ q′⨾t
          σ ⊢ V W ⊑ V′ (W′ @ +s) @ -t : q′

          (and then induction) [TODO: Check]

    (ΛX.V[X]) α  ⊢→  V[α]

      Induct on the derivation of σ ⊢ ΛX.V[X] ⊑ N′ : q.

      (Λ⊑)

        σ, α:=✯ ⊢ V[α] ⊑ N′ : q[tag_α]
        ------------------------------- Λ⊑
        σ ⊢ ΛX.V[X] ⊑ N′ : να.q[seal_α]
        ------------------------------------- α⊑
        σ, α:=A ⊢ (ΛX.V[X]) α ⊑ N′ : q[tag_α]
      ⊢→/=
        σ, α:=A ⊢ V[α] ⊑ N′ : q[tag_α]

      (Λ⊑Λ)

        σ, X ⊢ V[X] ⊑ V′[X] : q[id_X]
        ----------------------------------- Λ⊑Λ
        σ ⊢ ΛX.V[X] ⊑ ΛX.V′[X] : ∀X.q[id_X]        
        ---------------------------------------- α⊑α where α:=p ∈ σ
        σ ⊢ (ΛX.V[X]) α ⊑ (ΛX.V′[X]) α : q[id_α]
      ⊢→/⊢→
        σ ⊢ V[α] ⊑ V′[α] : q[id_α]

      ∀ upcast (⊑+)

        σ ⊢ V ⊑ V′ : ∀X.q[id_X]
        --------------------------------------- ⊑+  ∀X.r[id_X] ⊑ (∀X.p[id_X])⨾(∀X.q[id_X])
        σ ⊢ V ⊑ V′ @ +(∀X.p[id_X]) : ∀X.r[id_X]
        --------------------------------------- α⊑α  α:=s ∈ σ
        σ ⊢ V α ⊑ (V′ @ +(∀X.p[X])) α : r[id_α]
      =/⊢→
        σ ⊢ V ⊑ V′ : ∀X.q[id_X]    
        ------------------------ α⊑α  α:=s ∈ σ
        σ ⊢ V α ⊑ V′ α : q[id_α]
        ----------------------------------- ⊑+    r[id_α] ⊑ p[id_α]⨾q[id_α]
        σ ⊢ V α ⊑ V′ α @ +p[id_α] : r[id_α]

      ∀ downcast (⊑-)

        σ ⊢ V ⊑ V′ : ∀X.r[id_X]
        --------------------------------------- ⊑+  ∀X.r[id_X] ⊑ (∀X.p[id_X])⨾(∀X.q[id_X])
        σ ⊢ V ⊑ V′ @ -(∀X.p[id_X]) : ∀X.q[id_X]
        --------------------------------------- α⊑α  α:=s ∈ σ
        σ ⊢ V α ⊑ (V′ @ -(∀X.p[id_X])) α : q[α]
      =/⊢→
        σ ⊢ V ⊑ V′ : ∀X.r[id_X]    
        ------------------------ α⊑α  α:=s ∈ σ
        σ ⊢ V α ⊑ V′ α : r[id_α]
        ----------------------------------- ⊑+    r[id_α] ⊑ p[id_α]⨾q[id_α]
        σ ⊢ V α ⊑ V′ α @ -p[id_α] : q[id_α]

      ν Downcast (⊑-)

        σ, α:=✯ ⊢ V[α] ⊑ N′ : r[tag_α]
        --------------------------------- Λ⊑
        σ ⊢ (ΛX.V[X]) ⊑ N′ : να.r[seal_α]
        ------------------------------------------------- ⊑- (i)
        σ ⊢ (ΛX.V[X]) ⊑ N′ @ -(να.q[seal_α]) : ∀X.p[id_X]
        ---------------------------------------------------------- α⊑α
        σ, α:=s ⊢ (ΛX.V[X]) α ⊑ (N′ @ -(να.q[seal_α])) α : p[id_α]
        (i)  να.r[seal_α] ⊑ (∀X.p[id_X])⨾(να.q[seal_α])
      ⊢→/=
        σ, α:=s ⊢ V[α] ⊑ (N′ @ -(να.q[seal_α])) α : p[id_α]
      =/—↠_{Π^⋆}  (Catchup Lemma)
        σ, α:=s, Π^☆ ⊢ V[α] ⊑ (V′ @ -(να.q[seal_α])) α : p[id_α]
      =/—→_{α:=⋆}
        σ, α:=✯ ⊢ V[α] ⊑ V′ : r[tag_α]
        ----------------------------------------- ⊑- (ii)
        σ, α:=s ⊢ V[α] ⊑ V′ @ -q[tag_α] : p[id_α]
        (ii)  r[tag_α] ⊑ p[id_α]⨾q[tag_α]

        [See Example 0]

    V @ ±id_a  ⊢→  V

        σ ⊢ V ⊑ M : p    id_a : a ⊑ a
        -----------------------------
        σ ⊢ V @ ±id_a ⊑ M : p
      ⊢→/=
        σ ⊢ V ⊑ M : p

    (V @ +(s→t)) W  ⊢→  V (W @ -s) @ +t

        σ ⊢ V ⊑ L : s₂→t₂
        ---------------------------- +⊑  (s→t)⨾(s₁→t₁) ⊑ (s₂→t₂)
        σ ⊢ (V @ +(s→t)) ⊑ L : s₁→t₁                                σ ⊢ W ⊑ M ⊢ s₁
        -------------------------------------------------------------------------- ·⊑·
        σ ⊢ (V @ +(s→t)) W ⊑ L M : t₁
      ⊢→/=
                             W ⊑ M : s₁
                             --------------- -⊑  s⨾s₁ ⊑ s₂
        σ ⊢ V ⊑ L : s₂→t₂    W @ -s ⊑ M : s₂
        ------------------------------------ ·⊑·
        σ ⊢ (V (W @ -s)) ⊑ L M : t₂
        -------------------------------- +⊑  t⨾t₁ ⊑ t₂
        σ ⊢ (V (W @ -s)) @ +t ⊑ L M : t₁

        (or handle upcast or downcast on right in usual way)

    (V @ -(s→t)) W  ⊢→  V (W @ +s) @ -t

        Wrap downcast lemma.

    (V @ +(∀X.p[X])) α  ⊢→  V α @ +p[α]

        There are three possible derivations.

      (i)
        σ ⊢ V ⊑ L : να.r[α]
        ------------------------------------ +⊑    (∀X.p[X])⨾(να.q[α]) ⊑ να.r[α]
        σ ⊢ (V @ +(∀X.p[X])) ⊑ L : να.q[α]
        ------------------------------------ α⊑    α:=A ∈ σ
        σ ⊢ (V @ +(∀X.p[X])) α ⊑ L : q[α]
      ⊢→/=
        σ ⊢ V ⊑ L : να.r[α]
        ------------------- α⊑    α:=A ∈ σ
        σ ⊢ V α ⊑ L : r[α]
        -------------------------- +⊑    p[α]⨾q[α] ⊑ r[α]
        σ ⊢ V α @ +p[α] ⊑ L : q[α]

      (ii)
        ρ ⊢ V ⊑ L : ∀X.r[X]
        ---------------------------------- +⊑    (∀X.p[X])⨾(∀X.q[X]) ⊑ ∀X.r[X]
        ρ ⊢ (V @ +(∀X.p[X])) ⊑ L : ∀X.q[X]
        ------------------------------------- α⊑α    α:=s ∈ ρ
        ρ ⊢ (V @ +(∀X.p[X])) α ⊑ L α : q[α]
      ⊢→/=
        ρ ⊢ V ⊑ L : ∀X.r[X]
        -------------------- α⊑α    α:=s ∈ ρ
        ρ ⊢ V α ⊑ L α : r[α]
        ------------------------------ +⊑    p[α]⨾q[α] ⊑ r[α]
        ρ ⊢ V α @ +p[α] ⊑ L α : q[α]

        (or handle upcast or downcast on right)

    (V @ -(∀X.p[X])) α  ⊢→  V α @ -p[α]

        similar to previous case

    V @ +(να.p[seal_α])  ⊢→  να:=★.(V α @ +p[seal_α])

                                       p[seal_α] : A[α] ⊑ B
                                       --------------------------
         σ ⊢ V ⊑ L : (να.r[seal_α])    να.p[seal_α] : ∀X.A[X] ⊑ B
         -------------------------------------------------------- +⊑ (i)
         σ ⊢ V @ +(να.p[seal_α]) ⊑ L : q
         (i)  (να.p[seal_α])⨾q ⊑ (να.r[seal_α])
       ⊢→
         σ, α:=★ ⊢ V ⊑ L : (να.r[seal_α])       
         -------------------------------- α⊑    
         σ, α:=★ ⊢ V α ⊑ L : r[seal_α]          p[seal_α] : A[α] ⊑ B
         ----------------------------------------------------------- +⊑ (ii)
         σ, α:=★ ⊢ (V α @ +p[seal_α]) ⊑ L : q
         ------------------------------------ ν⊑
         σ ⊢ να:=★.(V α @ +p[seal_α]) ⊑ L : q
         (ii)  p[seal_α]⨾q ⊑ r[seal_α]

    (V @ —(να.p[seal_α])) α  ⊢→  V @ -p[tag_α]

         σ ⊢ V ⊑ L : q
         -------------------------------------------- -⊑ (i)
         σ ⊢ V @ —(να.p[seal_α]) ⊑ L : (να.r[seal_α])
         -------------------------------------------- α⊑    α:=A ∈ σ
         σ ⊢ (V @ —(να.p[seal_α])) α ⊑ L : r[tag_α]
         (i)  (να.p[seal_α])⨾q ⊑ να.r[seal_α]
       ⊢→/=
         σ ⊢ V ⊑ L : q
         ------------------------------------ -⊑ (ii)
         σ ⊢ V @ -p[tag_α] ⊑ L : r[tag_α]
         (ii)  p[tag_α]⨾q ⊑ r[tag_α]

         (There could be right upcast or downcast between α⊑ and -⊑.
         In that case, we can push it underneath the α⊑.)

    V @ +(s;t)  ⊢→  V @ +s @ +t

         σ ⊢ V @ +(s;t) ⊑ M′ : p
       ⊢→/=
         σ ⊢ V @ +s @ +t ⊑ M′ : p

         Easy to show σ ⊢ V @ +(s;t) ⊑ M′ : p
         implies σ ⊢ V @ +s @ +t ⊑ M′ : p.

    V @ +tag_G @ -tag_G  ⊢→  V

         σ ⊢ V @ +tag_G @ -tag_G ⊑ M : tag_G
       ⊢→/=
         σ ⊢ V ⊑ M : tag_G

       By Left Tag Inversion 1 and 2.

    V @ +tag_G @ -tag_H  ⊢→  blame,  G ≠ H

         σ ⊢ V @ +tag_G @ -tag_H ⊑ M : p
       ⊢→
         σ ⊢ blame ⊑ M : p

         Immediate.

    V @ -seal_α @ +seal_α  ⊢→  V

        σ ⊢ V @ -seal_α @ +seal_α ⊑ M : p
      ⊢→
        σ ⊢ V ⊑ M : p

         Easy to show σ ⊢ V @ -seal_α @ +seal_α ⊑ M : p
         implies σ ⊢ V ⊑ M : p.

    (να:=A.N[α]) —→_{α:=A} N[α]

        σ, α:=p ⊢ N[α] ⊑ N′[α]
        --------------------------------- ν⊑ν
        σ ⊢ (να:=A.N[α]) ⊑ (να:=A′.N′[α])
      —→_{α:=A}/—→_{α:=A′}
        σ, α:=p ⊢ N[α] ⊑ N′[α]
      
        σ, α:=A ⊢ N[α] ⊑ N′ : p
        ----------------------- ν⊑  α ∉ fv(p)
        σ ⊢ να:=A.N[α] ⊑ N′ : p
      —→_{α:=A}/=
        σ, α:=A ⊢ N[α] ⊑ N′ : p

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

The following appear not to be needed---the simulation proof does not
reference them, even though similar results appear in Siek et al
(2015).


Left upcast inversion
~~~~~~~~~~~~~~~~~~~~~

(Convention. p, q, r range over casts, s, t over imprecisions.)


If γ ⊢ M @ +s ⊑ N : q and s ⨾ q ≈ r then γ ⊢ M ⊑ N : r.

Proof by induction on the derivation of σ ⊢ M @ +s ⊑ N : q.

  (+⊑)
      γ ⊢ M ⊑ N : r
      ------------------ +⊑    s ⨾ q ≈ r
      γ ⊢ M @ +s ⊑ N : q

      (trivial)

  (⊑+)  N = N′ @ +t

      γ ⊢ M ⊑ N′ : p
      -------------------- +⊑        s ⨾ r′ ≈ p  (i)  (induction -- see below)
      γ ⊢ M @ +s ⊑ N′ : r′
      ------------------------ ⊑+    q ≈ r′ ⨾ t  (ii)
      γ ⊢ M @ +s ⊑ N′ @ +t : q
    =>
      γ ⊢ M ⊑ M′ : p    
      ------------------- ⊑+         r ≈ p ⨾ t   (iii)
      γ ⊢ M ⊑ M′ @ +t : r
      ------------------------ +⊑    s ⨾ q ≈ r   (iv)
      γ ⊢ M @ +s ⊑ M′ @ +t : q

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

  (⊑-)  N = N′ @ -t
  
      γ ⊢ M ⊑ N′ : p
      -------------------- +⊑        s ⨾ r′ ≈ p  (i)  (induction -- see below)
      γ ⊢ M @ +s ⊑ N′ : r′
      ------------------------ ⊑-    r′ ≈ q ⨾ t  (ii)
      γ ⊢ M @ +s ⊑ N′ @ -t : q
    =>
      γ ⊢ M ⊑ N′ : p    
      ------------------- ⊑-         p ≈ r ⨾ t   (iii)
      γ ⊢ M ⊑ N′ @ -t : r
      ------------------------ +⊑    s ⨾ q ≈ r   (iv)
      γ ⊢ M @ +s ⊑ N′ @ -t : q

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

If γ ⊢ M @ -s ⊑ N : r and s ⨾ q = r then γ ⊢ M ⊑ N : q.

Proof by induction on the derivation of γ ⊢ M @ -s ⊑ N : r.

  (-⊑)
      γ ⊢ M ⊑ N : q
      ------------------- -⊑    s ⨾ q = r
      γ ⊢ M @ -s ⊑ N : r

      (trivial)

  (⊑-)   N = N′ @ -t

      γ ⊢ M ⊑ N′ : p
      -------------------- -⊑        s ⨾ p ≈ q′  (i)  (induction -- see below)
      γ ⊢ M @ -s ⊑ N′ : q′
      ------------------------ ⊑-    q′ ≈ r ⨾ t  (ii)
      γ ⊢ M @ -s ⊑ N′ @ -t : r
    =>
      γ ⊢ M ⊑ M′ : p    
      ------------------- ⊑-         p ≈ q ⨾ t   (iii)
      γ ⊢ M ⊑ M′ @ -t : q
      ------------------------ -⊑    s ⨾ q ≈ r   (iv)
      γ ⊢ M @ -s ⊑ M′ @ -t : r

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

  (⊑+)  N = N′ @ +t
    
      γ ⊢ M ⊑ N′ : p
      -------------------- -⊑        s ⨾ p ≈ q′  (i)  (induction -- see below)
      γ ⊢ M @ -s ⊑ N′ : q′
      ------------------------ ⊑+    r ≈ q′ ⨾ t  (ii)
      γ ⊢ M @ -s ⊑ N′ @ +t : r
    =>
      γ ⊢ M ⊑ M′ : p    
      ------------------- ⊑+         q ≈ p ⨾ t   (iii)
      γ ⊢ M ⊑ M′ @ +t : q
      ------------------------ -⊑    s ⨾ q ≈ r   (iv)
      γ ⊢ M @ -s ⊑ M′ @ +t : r

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

If σ ⊢ V ⊑ V′ @ +q : (p ⨾ q) then σ ⊢ V ⊑ V′ : p.

Proof by induction on the derivation of σ ⊢ V ⊑ V′ @ +q : (p ⨾ q).

  (⊑+)
      σ ⊢ V ⊑ V′ : p    q : A ⊑ B
      --------------------------- ⊑+
      σ ⊢ V ⊑ V′ @ +q : (p ⨾ q)

      Immediate.

  (+⊑)
      σ ⊢ V ⊑ V′ : (s ⨾ t)
      ----------------------------- ⊑+
      σ ⊢ V ⊑ V′ @ +q : (s ⨾ t ⨾ q)
      ------------------------------ +⊑
      σ ⊢ V @ +s ⊑ V′ @ +q : (t ⨾ q)
    =>
      σ ⊢ V ⊑ V′ : (s ⨾ t)
      -------------------- +⊑
      σ ⊢ V @ +s ⊑ V′ : t
      ------------------------------ ⊑+
      σ ⊢ V @ +s ⊑ V′ @ +q : (t ⨾ q)

  (-⊑)
      σ ⊢ V ⊑ V′ : t
      ------------------------- ⊑+
      σ ⊢ V ⊑ V′ @ +q : (t ⨾ q)
      ---------------------------------- -⊑
      σ ⊢ V @ -s ⊑ V′ @ +q : (s ⨾ t ⨾ q)
    =>
      σ ⊢ V ⊑ V′ : t
      ------------------------- -⊑
      σ ⊢ V @ -s ⊑ V′ : (s ⨾ t)
      ---------------------------------- ⊑+
      σ ⊢ V @ -s ⊑ V′ @ +q : (s ⨾ t ⨾ q)

  (Λ⊑)
      σ, α:=★ ⊢ V[α] ⊑ V′ : p[α]
      ------------------------------------- ⊑+
      σ, α:=★ ⊢ V[α] ⊑ V′ @ +q : (p[α] ⨾ q)
      ------------------------------------- Λ⊑
      σ ⊢ ΛX.V[X] ⊑ V′ @ +q : να.(p[α] ⨾ q)
    =>
      σ, α:=★ ⊢ V[α] ⊑ V′ : p[α]
      -------------------------- Λ⊑
      σ ⊢ ΛX.V[α] ⊑ V′ : να.p[α]
      ------------------------------------- ⊑+
      σ ⊢ ΛX.V[X] ⊑ V′ @ +q : να.(p[α] ⨾ q)

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
          σ ⊢ V ⊑ V′ @ +(s→t) : p→q                              σ ⊢ W ⊑ W′ : p
          --------------------------------------------------------------------- ·⊑·
          σ ⊢ V W ⊑ (V′ @ +(s→t)) W′ : q
        —→
                                σ ⊢ W ⊑ W′ : p
                                -------------------- ⊑-    s⨾p = p′
          σ ⊢ V ⊑ V′ : p′→q′    σ ⊢ W ⊑ W′ @ -s : p′
          ------------------------------------------ ·⊑·
          σ ⊢ V W ⊑ V′ (W′ @ -s) : q′                   
          -------------------------------- ⊑+    t⨾q = q′
          σ ⊢ V W ⊑ V′ (W′ @ -s) @ +t : q

        By induction, we then have V = λx.N[x], V′ (W′ @ -s) ⊢↠ N′ and σ ⊢ N[V] ⊑ N′ : q′,
        whence σ ⊢ N[V] ⊑ N′ @ +t : q

      Function downcast. (Similar.)


Simulation of type application (∀)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If σ : Σ ⊑ Σ′ and σ ⊢ (ΛX.V[X]) ⊑ V′ : ∀X.p[X]
then Σ′ ⊢ V′ α —↠ Π′ ⊢ N′ and π : Σ ⊑ Π′ and π ⊢ V[α] ⊑ N′: p[α].

Proof by induction on the derivation of σ ⊢ (ΛX.V[X]) ⊑ V′ : ∀X.p[X].

The only possibility for V′ is that it is a big lambda term or a
±∀ or -ν cast.


  Big Lambda


  ∀ Upcast
                            
        σ ⊢ V ⊑ V′ : ∀X.r[X]
        --------------------------------- ⊑+    (∀X.p[X])⨾(∀X.q[X]) = ∀X.r[X]
        σ ⊢ V ⊑ V′ @ +(∀X.p[X]) : ∀X.q[X]
        ------------------------------------ α⊑α    α:=s ∈ σ
        σ ⊢ V α ⊑ (V′ @ +(∀X.p[X])) α : q[α]
      ⊢→
        σ ⊢ V ⊑ V′ : ∀X.r[X]    
        --------------------- α⊑α    α:=s ∈ σ
        σ ⊢ V α ⊑ V′ α : r[α]
        ----------------------------- ⊑+    p[X]⨾q[X] = r[X]
        σ ⊢ V α ⊑ V′ α @ +p[α] : q[α]

  ∀ Downcast (similar)

  ν Downcast

        σ, α:=✯ ⊢ V[α] ⊑ V′ : r[α]
        ---------------------------- Λ⊑
        σ ⊢ (ΛX.V[X]) ⊑ V′ : να.r[α]
        ----------------------------------------- ⊑-    (∀X.p[X])⨾(να.q[α]) = να.r[α]
        σ ⊢ (ΛX.V[X]) ⊑ V′ @ -(να.q[α]) : ∀X.p[X]
        -------------------------------------------------- α⊑α
        σ, α:=s ⊢ (ΛX.V[X]) α ⊑ (V′ @ -(να.q[α])) α : p[α]
      ⊢→
        σ, α:=✯ ⊢ V[α] ⊑ V′ : r[α]
        ---------------------------------------------- ⊑-    p[α]; q[seal_α:=tag_α] = r[α]
        σ, α:=s ⊢ V[α] ⊑ V′ @ -q[seal_α:=tag_α] : p[α]


Simulation of unwrap
~~~~~~~~~~~~~~~~~~~~

(Lemma 11 of Refined Criteria)
If σ ⊢ V @ ±(p→q) ⊑ V′ : s→t and σ ⊢ W ⊑ W′ : s
then V′ W′ ⊢↠ N′ and σ ⊢ V (W @ ∓p) @ ±q ⊑ N′: t.

Proof.  See the cases

    (V @ +(s→t)) W  ⊢→  V (W @ -s) @ +t
    (V @ -(s→t)) W  ⊢→  V (W @ +s) @ -t

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
    σ ⊢ V ⊑ V′ @ +t : r
  =/—↠
    π ⊢ V ⊑ W : r

    σ ⊢ V ⊑ V′ : r
    ------------------- ⊑-  r ≈ p ⨾ t
    σ ⊢ V ⊑ V′ @ -t : p
  =/—↠
    π ⊢ V ⊑ W : p

Catchup.

    σ ⊢ V ⊑ M : p
  =/—↠
    π ⊢ V ⊑ W : p

Sim-cast.

    σ ⊢ V ⊑ V′ : p
    ------------------------ +⊑  s ⨾ q ≈ p ⨾ t
    σ ⊢ V @ +s ⊑ V′ @ +t : q
  —→/—↠
    σ ⊢ M ⊑ M′ : r

    σ ⊢ V ⊑ V′ : q
    ------------------------ +⊑  s ⨾ q ≈ p ⨾ t
    σ ⊢ V @ -s ⊑ V′ @ -t : p
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
    σ ⊢ V @ +(s→t) ⊑ V′ : p′→q′       σ ⊢ W ⊑ W′ : p′
    ------------------------------------------------- ·⊑·
    σ ⊢ (V @ +(s→t)) W ⊑ V′ W′ : q′
  —→/—↠
    π ⊢ V (W @ -s) @ +t ⊑ N : q′
