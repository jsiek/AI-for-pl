Graduality, Parametricity, Interoperability: Together Again for the First Time
(version 16)

25 January 2026

Jeremy Siek
Indiana University

Peter Thiemann
University of Freiburg

Philip Wadler
University of Edinburgh

------------------------------------------------------------------------
New in this version:
Deleted superfluous material. See cambridge15.lagda.md for previous.
------------------------------------------------------------------------

There has long been a tension between achieving three key properties
of gradual typing typing. Graduality: as we upcast parts of a program
it retains its semantics. Parametricity: polymorphic terms
instantiated at related types have related semantics.
Interoperability: functions at polymorphic type may upcast to dynamic
type, and downcast vice-versa. We present the first system that
satisfies all three. Interoperability is obvious from its formulation;
we provide a direct proof of graduality; and we show parametricity by
reduction to the systems of Ahmed et al (2017) and New et al
(2019). We also introduce a number of technical innovations; in
particular, we merge the casts and conversions of Ahmed et al (2017)
into a single construct, eliminating annoying redundancies.

Traditionally, the tension between graduality and parametricity arises
because graduality demands we can upcast (∀X.X→X) to, say, (∀X.X→⋆),
and its semantics must not change. Conversely, parametricity demands
that (∀X.X→X) must be either the identity function or the function
that never returns, while (∀X.X→⋆) must be a constant function. (Here
⋆ is the dynamic type, also written ? in some work.) We resolve the
problem by restricting casts, so that (∀X.X→X) may be cast to (⋆→⋆) or
to ⋆, as required by interoperability, but not to (∀X.X→⋆).  Throwing
out the latter loses little: the cast adds nothing to graduality
precisely because it violates parametricity.

------------------------------------------------------------------------
Longer abstract

There has long been a tension between achieving three key properties
of gradual typing typing. Graduality: as we upcast parts of a program
it retains its semantics. Parametricity: polymorphic terms
instantiated at related types have related semantics.
Interoperability: functions at polymorphic type may upcast to dynamic
type, and downcast vice-versa. We present the first system that
satisfies all three.

Traditionally, the tension between graduality and parametricity arises
because graduality demands we can upcast (∀X.X→X) to (∀X.X→⋆) or
(∀X.⋆→X) and its semantics should not change, where ⋆ is the dynamic
type, while parametricity demands (∀X.X→X) must be the identity
function or the function that never terminates, and (∀X.X→⋆) must be a
constant function, and (∀X.⋆→X) must be the function that never
terminates. We resolve the problem by restricting casts, so that
(∀X.X→X) may be cast to (⋆→⋆) or ⋆, but not to (∀X.X→⋆) or (∀X.⋆→X).
Throwing out the latter cast loses little: it adds nothing useful to
graduality precisely because it violates parametricity.

Traditionally, interoperability required compromises. In the presence
of interoperability, compatibility between types becomes asymmetric
and overly permissive: (∀X.X→X) casts to (A→B), for any types A and B,
while only (⋆→⋆) casts to (∀X.X→X).  Here, by restricting type
imprecision we have (∀X.X→X) casts to (⋆→⋆) but not (A→B), and vice
versa, restoring symmetry and eliminating over permissiveness. The key
to achieving this is to introduce two distinct type variables, written
X and α, that behave differently with regard to type imprecision.

Our new system satisfies graduality, parametricity, and
interoperability. Interoperability is obvious from its formulation; we
provide a direct proof of graduality; and we show parametricity by
reduction to the systems of Ahmed et al (2017) and New et al
(2019). We also introduce a number of technical innovations. We
combine casts and conversions as in Ahmed et al (2017), and tagging
and sealing as in New et al (2019), into a single construct,
eliminating annoying redundancies. We are simpler than Ahmed et al
(2017), though similar to New et al (2019), in that we replace five
relations (≺, <:, <:⁺, <:⁻, <:ₙ) by a single relation (⊑, similar to
the previous <:ₙ). The system of New et al (2019) has been criticised
because it is not obvious how to embed System F into it; we show there
is a straightforward embedding of F into their system (and ours) that
is fully abstract. Finally, Devriese et al (2017) point out that the
parametricity satisfied by gradual type systems must be weaker than
that originally defined by Reynolds (1983), because they have
non-trivial instantiations of the universal type, (∃X.∀Y.(X→Y)×(Y→X)),
obtained by instantiating X to the dynamic type ⋆. In our system,
instantiating X to ⋆ results in a trivial type, suggesting that we may
satisfy a form of parametricity stronger than previous work.
------------------------------------------------------------------------

Key related works.

Castagna, Lanvin, Petrucciani, and Siek (POPL 2019).
  Gradual Typing: A New Perspective.
New, Jamner & Ahmed (POPL 2019).
  Graduality and Parametricity: Together Again for the First Time.
Igarashi, Sekiyama & Igarashi (ICFP 2017).
  On Polymorphic Gradual Typing.
Ahmed, Jamner, Siek, and Wadler (POPL 2017).
  Theorems for free for free: parametricity, with and without types.
Toro, Labrada & Tanter (POPL 2019, JACM 2022).
  Gradual System F.
Devriese, Patrigani & Piessens (POPL 2017, TOPLAS 2022).
  Two Parametricities Versus Three Universal Types.

Other related works.

Guha, Matthews, Findler & Krishnamurthi (DLS 2007).
  Relationally-parametric polymorphic contracts.
Siek & Taha (Scheme 2006).
  Gradual typing for functional programming.
Wadler & Findler (ESOP 2009).
  Well-typed programs can't be blamed.

------------------------------------------------------------------------

Draft for slides.

1. Title
2. First apology: <: <:⁺ <:⁻ <:ₙ ≺ vs ⊑ (Castagna et al 2019)
3. Second apology: ∀X.X→X ≺ A→B vs ∀X.X→X ⊑ ⋆→⋆ (Igarashi et al 2017)
4. Third apology: casts and conversions (Ahmed et al 2017), tags and seals (New et al 2019)
5. Why we need G
6. Don't throw the baby out with the bathwater: from F to G. (Siek and Wadler 2015)
7. How New et al (2019) reconcile graduality and parametricity
8. How we fix imprecision.
9. Devriese et al (2017, 2022): trivial vs non-trivial Universal type
10. Summary
11. Formal development: types
12. Formal development: imprecision, grammar
13. Formal development: imprecision, rules
14. Formal development: imprecision, casts isomorphic to derivations
15. Formal development: imprecision, composition
16. Formal development: term grammar, selected rules
17. Formal development: term imprecision, equations and inequations
18. Reduction to Ahmed et al (2017)
19. Reduction to New et al (2019)
20. Example: Identity function
21. Example: upcast
22. Example: downcast
23. Example: upcast and downcast, multiple times
24. Summary
25. More titles

------------------------------------------------------------------------
Can I build a table to show how these relate?


                        Par  Gra  Int  1/5  F→G  C&C  RLR
Ahmed et al (2017)       ✓    ✗    ✓    ✗    ✗    ✗    ✗    
Igarashi et al (2017)    c    c    ✓    ✗    ✗    ✗    ✗
Toro et al (2019)        ✓    ✓    ✗    ✗    ✗    ✗    ✗
New et al (2019)         ✓    ✓    ✗    ✓    ✗    ✗    ✗
this work                ✓    ✓    ✓    ✓    ✓    ✓    c

Par = Parametricity
Gra = Graduality
Int = Interoperability
1/5 = one relation instead of five
F→G = F embeds in G fully abstractly
C&C = Casts & Conversions
RLR = Reynolds Logical Relation



------------------------------------------------------------------------

(a) A New Perspective. Castagna, Lanvin, Petrucciani, and Siek (POPL 2019).

    Replace five relations (~ <: <:⁺ <:⁻ ⊑) by one (⊑).

(b) A New Perspective on Interoperability.

    Replace

               C ≺ A   B ≺ D    A[⋆] ≺ B       A ≺ B[X]
      -----    -------------    -----------    -----------    -----    -----    -----
      ι ≺ ι    A→B ≺ C→D        ∀X.B[X] ≺ B    A ≺ ∀X.B[X]    A ≺ ⋆    ⋆ ≺ A    X ≺ X
     
    by

               A ⊑ C   B ⊑ D    A[X] ⊑ B[X]          A[α] ⊑ B       A ⊑ G
      -----    -------------    -----------------    -----------    -----    -----    -----    -----
      ι ⊑ ι    A→B ⊑ C→D        ∀X.A[X] ⊑ ∀X.B[X]    ∀X.A[X] ⊑ B    A ⊑ ⋆    X ⊑ X    α ⊑ α    ⋆ ⊑ ⋆

      G ::= α | ι | ⋆→⋆

    This has huge advantages!

    We are symmetric again. A ~ B iff ∃C.(C ⊑ A & C ⊑ B).

    The old version allows ∀X.X→X ≺ ⋆→⋆, but also ∀X.X→X ≺ ι→ι (bad: we don't want it).
    The old version allows ⋆→⋆ ≺ ∀X.X→X, but not ι→ι ≺ ∀X.X→X (good: we don't want it).
    The new version allows only ∀X.A[X] ⊑ ⋆→⋆.

(c) From System F to System G.

    LA ~~> να:=A.Lα @ +B[seal_α]  where  L : ∀X.B[X]

    We can show full abstraction for translations from F to G.

(d) Interoperability and gradual guarantee.

    Key examples:
      (ΛX.λx:X.x) ι κ ~~> (να:=ι.(ΛX.λx:X.x) α @ +(seal_α→seal_α)) κ ⊑ ((ΛX.λx:X.x) @ +(να.seal_α→seal_α)) (κ @ +tag_ι)
      ((λx:⋆.x) @ -(να.seal_α→seal_α)) ι κ ~~> (να:=ι. ((λx:⋆.x) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) κ ⊑ (λx:⋆.x) (κ @ +tag_ι)
      

(e) Strict graduality

    Disallow X ⊑ ⋆ but allow α ⊑ ⋆.
    Similar to Toro, Labrada & Tanter (POPL 2019), Labrada, Toro & Tanter (JACM 2022),
      but without the shame.

(f) Better parametricity.

    Devriese, Patrigani & Piessens (POPL 2017, TOPLAS 2022) point out the special
    role of the universal type: ∃Y.∀X.(X → Y) × (Y → X).
    This is empty for System F (no such Y), but not for gradual calculi (choose Y = ⋆).
    In our system, there is also no such Y, so we may have stronger parametricity.
    
(g) Casts and conversions, together again for the first time.

    Casts and conversions are merged. Much more compact.

(h) Graduality and parametricity: Together again for the first time, again.

    Stresses we have both (e) and (f).


Trying to understand New.

In New, upcasting (∀X.X→X) to (∀X.X→⋆) should leave behaviour unchanged.
How does this occur?

    να:=ι. ((ΛX.λx:X.x) α @ +(seal_α→seal_α)) κ  —↠  κ

(just as in our system), but

    να:=ι. ((ΛX.λx:X.x) :: ∀X.X→⋆) α @ +(seal_α→seal_α)) κ  —↠  κ

(unlike in our system). Let me work out the second in detail.
The key point is that attribution ∀X.X→⋆ adds an upcast +tag_X,
while the mismatch between α→⋆ and α→α adds a downcast -tag_α.
After disambiguating, we have

    να:=ι. ((ΛX.λx:X.x) @ +(∀X.id_X→tag_X)) α @ -(id_X→tag_α) @ +(seal_α→seal_α)) κ  —↠  κ

as expected. Basically the upcast to ⋆ is immediately undone, in order
to match the type α→α required of the input to the conversion.



Introduction.

The quest to reconcile gradual typing with parametricity is nearing
the end of its second decade.  Siek and Taha (2006) introduced gradual
typing. Guha et al (2007) described how runtime seals could be used to
convert dynamically-typed terms to polymorphic type while ensuring
parametricity.

...

A key property of Amal et al (2011, 2017) is that a polymorphic
function with universal type is cast to a dynamically typed function
that can be applied directly. Technically, the trick is that, for
instance, we may cast ∀X.X→X to ⋆→⋆ and thence to ⋆. In other systems
[CITE], we cast ∀X.X→X to ∀X.⋆, and thence to ⋆, meaning that rather
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

    id⋆  =  λx:⋆.x
    id   =  ΛX.λx:X.x
    id′  =  ΛX.λx:X.(id⋆ @ -(να.seal_α→seal_α)) X x
         =  ΛX.λx:X.να:=X. ((id⋆ @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α)) x

But it can also be done with explicit tagging and sealing:

    id″ = ΛX.λx:X.να:=X. (id⋆ @ -(tag_α→tag_α) @ +(seal_α→seal_α))

This is actually just one reduction step applied to the previous,
so I guess that the previous is better style and easier to use.

========================================================================
EXAMPLES
========================================================================

[Add an example showing why we need α]

Example 1. Instantiate id at different types.

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


Example 2. Polymorphic id is less imprecise than monomorphic id.

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


    --------------------------------------- (x⊑x)
    α:=ι, α′:=★, x:seal_α′ ⊢ x ⊑ x : seal_α
    ---------------------------------------------------- (λ⊑λ)
    α:=ι, α′:=★ ⊢ (λx:α′.x) ⊑ (λx:★.x) : seal_α′→seal_α′
    ---------------------------------------------------- (Λ⊑)
    α:=ι ⊢ (ΛX.λx:X.x) ⊑ id★ : να.(seal_α→seal_α)
    ------------------------------------------------- (α⊑)
    α:=ι ⊢ id α ⊑ id★ : (seal_α;tag_ι)→(seal_α;tag_ι)
    ---------------------------------------------------- (+⊑)
    α:=ι ⊢ id α @ +(seal_α→seal_α) ⊑_∅ id★ : tag_ι→tag_ι
    ---------------------------------------------------------- (ν⊑)
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) ⊑_∅ id★ : tag_ι→tag_ι         ∅ ⊢ c ⊑_∅ c★ : tag_ι
    --------------------------------------------------------------------------------------- (·⊑·)
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c ⊑_∅ id★ c★ : tag_ι


    ----------------------------------------------- (x⊑x)
    α:=ι, x:(seal_α;tag_ι) ⊢ x ⊑ x : (seal_α;tag_ι)
    ---------------------------------------------------- (λ⊑λ)
    α:=ι ⊢ idα ⊑ id★ : (seal_α;tag_ι)→(seal_α;tag_ι)
    ----------------------------------------------------- (+⊑)
    α:=ι ⊢ idα @ +(seal_α→seal_α) ⊑ id★ : tag_ι→tag_ι             α:=ι ⊢ c ⊑ c★ : tag_ι
    ----------------------------------------------------------------------------------- (·⊑·)
    α:=ι ⊢ (idα @ +(seal_α→seal_α)) c ⊑ id★ c★ : tag_ι


Example 3. Up on the left.

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
    α:=★, x:seal_α ⊢ x ⊑ x : seal_α
    -------------------------------------------- (λ⊑λ)
    α:=★ ⊢ (λx:α.x) ⊑ (λx:★.x) : (seal_α→seal_α)
    ----------------------------------------------- (Λ⊑)
    ∅ ⊢ (ΛX.λx:X.x) ⊑ (λx:★.x) : (να.seal_α→seal_α)
    ------------------------------------------------------------ (+⊑)
    ∅ ⊢ (ΛX.λx:X.x) @ +(να.seal_α→seal_α) ⊑ (λx:★.x) : id_★→id_★


Example 4. Up on the right.

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
    ----------------------------------------------------------- (⊑+)
    α:=ι ⊢ id ⊑ (id @ +(να.seal_α→seal_α)) : (να.seal_α→seal_α)
    ------------------------------------------------------------------------ (α⊑)
    α:=ι ⊢ id α ⊑ (id @ +(να.seal_α→seal_α)) : (seal_α;tag_ι)→(seal_α;tag_ι)
    ------------------------------------------------------------------------- (+⊑)
    α:=ι ⊢ id α @ +(seal_α→seal_α) ⊑ (id @ +(να.seal_α→seal_α)) : tag_ι→tag_ι    
    ------------------------------------------------------------------------------- (ν⊑)
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) ⊑ (id @ +(να.seal_α→seal_α)) : tag_ι→tag_ι

  There is an alternative approach, below, but later examples show it does not generalise.

    ∅ ⊢ id ι c ⊑_∅ (id @ +(να.seal_α→seal_α)) c★ : tag_ι
  ~>
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c ⊑ (id @ +(να.seal_α→seal_α)) c★ : tag_ι
  —↠
    ∅ ⊢ (να:=ι. id α @ +(seal_α→seal_α)) c ⊑ (να:=★. id α @ +(seal_α→seal_α)) c★ : tag_ι
  —↠
    α:=tag_ι ⊢ (id α @ +(seal_α→seal_α)) c ⊑ (id α @ +(seal_α→seal_α)) c★ : tag_ι
  —↠
    α:=tag_ι ⊢ idα (c @ -seal_α) @ +seal_α ⊑ idα (c★ @ -seal_α) @ +seal_α : tag_ι
  —↠
    α:=tag_ι ⊢ c @ -seal_α @ +seal_α ⊑ c★ @ -seal_α @ +seal_α : tag_ι
  —↠
    α:=tag_ι ⊢ c ⊑ c★ : tag_ι
                  
              
Example 5. Up and then down.

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
    
    ------------------------------------------ (x⊑x)
    α:=id_ι, α′:=id_⋆, x:id_α′ ⊢ x ⊑ x : id_α′
    ------------------------------------------------------- (λ⊑λ)
    α:=id_ι, α′:=id_⋆ ⊢ (ƛx:α₀.x) ⊑ (ƛx:α₀.x) : id_α′→id_α′
    ------------------------------------------------------------------------------------ (⊑+), rename
    α:=id_ι, α′:=⋆, α′:=☆ ⊢ (ƛx:α′.x) ⊑ (ƛx:α′.x) @ +(seal_α′→seal_α′) : seal_α′→seal_α′   
    ------------------------------------------------------------------------------------ (⊑α)
    α:=id_ι, α′:=⋆, α₀:=☆ ⊢ (ƛx:α′.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) : seal_α′→seal_α′
    ------------------------------------------------------------------------------------- (Λ⊑)
    α:=id_ι, α₀:=☆ ⊢ (ΛX.ƛx:X.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) : να.seal_α→seal_α
    --------------------------------------------------------------------------------------------------- (⊑-)
    α:=id_ι, α₀:=☆ ⊢ (ΛX.ƛx:X.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α) : ∀X.id_X→id_X
    ---------------------------------------------------------------------------------------------------- (α⊑α)
    α:=id_ι, α₀:=☆ ⊢ (ΛX.ƛx:X.x) α ⊑ ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α : id_α→id_α
    ---------------------------------------------------------------------------------------------------------------------------------------------- (+⊑+)
    α:=id_ι, α₀:=☆ ⊢ (ΛX.ƛx:X.x) α @ +(seal_α→seal_α) ⊑ ((ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(να.seal_α→seal_α)) α @ +(seal_α→seal_α) : id_ι→id_ι

    ------------------------------------------ (x⊑x)
    α:=id_ι, α′:=id_⋆, x:id_α′ ⊢ x ⊑ x : id_α′
    ------------------------------------------ (λ⊑λ)
    α:=tag_ι ⊢ (ƛx:α.x) ⊑ (ƛx:α.x) : id_α→id_α
    ---------------------------------------------------------------------- (⊑+) (i)
    α:=ι, α₀:=☆ ⊢ (ƛx:α.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) : tag_α→tag_α
    ---------------------------------------------------------------------------------------- (⊑-) (ii)
    α:=id_ι, α₀:=☆ ⊢ (ƛx:α.x) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α→tag_α) : id_α→id_α
    ----------------------------------------------------------------------------------------------------------------------------- (+⊑+)
    α:=id_ι, α₀:=☆ ⊢ (ƛx:α.x) @ +(seal_α→seal_α) ⊑ (ƛx:α₀.x) @ +(seal_α₀→seal_α₀) @ -(tag_α→tag_α) @ +(seal_α→seal_α) : id_ι→id_ι


         (i)
                       tag_α→tag_α
                            ∅
                  α→α ————————————→ *→*
                   ↑                 ↑
                   |                 |
         id_α→id_α |        ⊑        | seal_α→seal_α
             ∅     |                 |      α:=⋆
                   |                 |
                  α→α ————————————→ α→α
                        id_α→id_α
                            ∅

         (ii)
                       tag_α→tag_α
                            ∅
                  α→α ————————————→ *→*
                   ↑                 ↑
                   |                 |
         id_α→id_α |        ⊑        |  tag_α→tag_α
             ∅     |                 |      α:=⋆
                   |                 |
                  α→α ————————————→ α→α
                        id_α→id_α
                            ∅

Example 6. Up and then down and then up. The binding list is getting longer.

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


Example 7. Up and then down and then up and then down.

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
                  α→α --------> ⋆→✯ 
                   ↑             ↑
         id_α→id_α |      ⊑      | seal_α→seal_α
             ∅     |             |      α:=✯
                  α→α --------> α→α
                      id_α→id_α
                          ∅

      (ii)
                     tag_α→tag_α
                          ∅
                  α→α --------> ⋆→✯ 
                   ↑             ↑
         id_α→id_α |      ⊑      | tag_α→tag_α
             ∅     |             |      ∅
                  α→α --------> α→α
                      id_α→id_α
                          ∅

Example 8. Down on the right.

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
  
Example 9. Constant function. Polymorphic less imprecise then monomorphic.

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


  α:=ι, β:=ι, x:(seal_α;tag_ι), y:(seal_β;tag_ι) ⊢ x ⊑ x : (seal_α;tag_ι)
  ------------------------------------------------------------------------------
  α:=ι, β:=ι, x:(seal_α;tag_ι) ⊢ λy:β.x ⊑ λy:★.x : (seal_β;tag_ι)→(seal_α;tag_ι)
  ------------------------------------------------------------------------------
  α:=ι, β:=ι ⊢ Kαβ ⊑ K★ : (seal_α;tag_ι)→(seal_β;tag_ι)→(seal_α;tag_ι)
  -------------------------------------------------------------------------- +⊑
  α:=ι, β:=ι ⊢ Kαβ @ +(seal_α→id_β→seal_α) ⊑ K★ : tag_ι→(seal_β;tag_ι)→tag_ι
  --------------------------------------------------------------------------------------- +⊑
  α:=ι, β:=ι ⊢ Kαβ @ +(seal_α→id_β→seal_α) @ +(id_ι→seal_β→id_ι) ⊑ K★ : tag_ι→tag_ι→tag_ι


Example 10. Constant function, up on the right.

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


Example 11. An example to demonstrate rebinding

    ∅ ⊢ (ΛX.λx:X.(ΛY.λy:Y.y)Xx)ιc ⊑ (λx:⋆.(λy:⋆.y)x)c⋆ : tag_ι
  ~>
    ∅ ⊢ (να:=ι.(ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α)) c ⊑ (λx:⋆.(λy:⋆.y)x)c⋆ : tag_ι
  —↠
    α:=ι ⊢ ((ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α)) c ⊑ (λx:⋆.(λy:⋆.y)x)c⋆ : tag_ι
  —↠
    α:=ι ⊢ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) @ +(seal_α→seal_α)) c ⊑ (λx:⋆.(λy:⋆.y)x)c⋆ : tag_ι
  —↠
    α:=ι ⊢ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) (c @ -seal_α) @ +seal_α ⊑ (λx:⋆.(λy:⋆.y)x)c⋆ : tag_ι
  —↠
    α:=ι ⊢ ((νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))(c @ -seal_α)) @ +seal_α ⊑ (λy:⋆.y)c⋆ : tag_ι
  —↠
    α:=ι, β:=α ⊢ ((ΛY.λy:Y.y)β @ +(seal_β→seal_β))(c @ -seal_α)) @ +seal_α ⊑ (λy:⋆.y)c⋆ : tag_ι
  —↠
    α:=ι, β:=α ⊢ ((λy:β.y) @ +(seal_β→seal_β))(c @ -seal_α)) @ +seal_α ⊑ (λy:⋆.y)c⋆ : tag_ι
  —↠
    α:=ι, β:=α ⊢ ((λy:β.y) (c @ -seal_α @ -seal_β)) @ +seal_β @ +seal_α ⊑ (λy:⋆.y)c⋆ : tag_ι
  —↠
    α:=ι, β:=α ⊢ c @ -seal_α @ -seal_β @ +seal_β @ +seal_α ⊑ c⋆ : tag_ι
  —↠
    α:=ι, β:=α ⊢ c @ -seal_α @ +seal_α ⊑ c⋆ : tag_ι
  —↠
    α:=ι, β:=α ⊢ c ⊑ c⋆ : tag_ι


                   seal_α→seal_α
                        α:=⋆
                  α→α ------> ⋆→⋆
                   ↑           ↑
     seal_β→seal_β |     ⊑     | id_⋆→id_⋆    (i)
         β:=α      |           |     ∅
                  β→β ------> ⋆→⋆
          (seal_β;seal_α)→(seal_β;seal_α)
                     α:=⋆,β:=α 

    -----------------------------------------------------------------
    α:=⋆, x:seal_α, β:=α, y:(seal_β;seal_α) ⊢ y ⊑ y : (seal_β;seal_α)
    ----------------------------------------------------------------------------
    α:=⋆, x:seal_α, β:=α ⊢ (λy:β.y) ⊑ (λy:⋆.y) : (seal_β;seal_α)→(seal_β;seal_α)
    ------------------------------------------------------------------------------------
    α:=⋆, x:seal_α, β:=α ⊢ (ΛY.λy:Y.y) ⊑ (λy:⋆.y) : (νβ.(seal_β;seal_α)→(seal_β;seal_α))
    ------------------------------------------------------------------------------------
    α:=⋆, x:seal_α, β:=α ⊢ (ΛY.λy:Y.y)β ⊑ (λy:⋆.y) : (seal_β;seal_α)→(seal_β;seal_α)
    --------------------------------------------------------------------------------- (i)
    α:=⋆, x:seal_α, β:=α ⊢ (ΛY.λy:Y.y)β @ +(seal_β→seal_β) ⊑ (λy:⋆.y) : seal_α→seal_α
    ---------------------------------------------------------------------------------
    α:=⋆, x:seal_α ⊢ νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β) ⊑ (λy:⋆.y) : seal_α→seal_α    α:=⋆, x:seal_α ⊢ x ⊑ x : seal_α
    --------------------------------------------------------------------------------------------------------------------
    α:=⋆, x:seal_α ⊢ (νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x ⊑ (λy:⋆.y)x : seal_α
    -----------------------------------------------------------------------------------------
    α:=⋆ ⊢ (λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) ⊑ (λx:⋆.(λy:⋆.y)x) : seal_α→seal_α
    ----------------------------------------------------------------------------------------------
    ∅ ⊢ (ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) ⊑ (λx:⋆.(λy:⋆.y)x) : (να.seal_α→seal_α)    (NB: can't be tag_α because of way ν is defined!!!)
    -------------------------------------------------------------------------------------------------------------
    α:=ι ⊢ (ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α ⊑ (λx:⋆.(λy:⋆.y)x) : (seal_α;tag_ι)→(seal_α;tag_ι)
    --------------------------------------------------------------------------------------------------------------
    α:=ι ⊢ (ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α) ⊑ (λx:⋆.(λy:⋆.y)x) : tag_ι→tag_ι
    -------------------------------------------------------------------------------------------------------------------
    ∅ ⊢ (να:=ι.(ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α)) ⊑ (λx:⋆.(λy:⋆.y)x) : tag_ι→tag_ι    ∅ ⊢ c ⊑ c⋆ : tag_ι
    -----------------------------------------------------------------------------------------------------------------------------------------
    ∅ ⊢ (να:=ι.(ΛX.λx:X.(νβ:=X.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x)α @ +(seal_α→seal_α)) c ⊑ (λx:⋆.(λy:⋆.y)x)c⋆ : tag_ι


    α:=ι, x:seal_α, β:=α, y:(seal_β;seal_α) ⊢ y ⊑ y : (seal_β;seal_α)
    ----------------------------------------------------------------------------
    α:=ι, x:seal_α, β:=α ⊢ (λy:β.y) ⊑ (λy:⋆.y) : (seal_β;seal_α)→(seal_β;seal_α)
    ------------------------------------------------------------------------------------
    α:=ι, x:seal_α, β:=α ⊢ (ΛY.λy:Y.y) ⊑ (λy:⋆.y) : (νβ.(seal_β;seal_α)→(seal_β;seal_α))
    ------------------------------------------------------------------------------------
    α:=ι, x:seal_α, β:=α ⊢ (ΛY.λy:Y.y)β ⊑ (λy:⋆.y) : (seal_β;seal_α)→(seal_β;seal_α)
    ---------------------------------------------------------------------------------
    α:=ι, x:seal_α, β:=α ⊢ (ΛY.λy:Y.y)β @ +(seal_β→seal_β) ⊑ (λy:⋆.y) : seal_α→seal_α
    -----------------------------------------------------------------------------------
    α:=ι, x:seal_α ⊢ (νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β)) ⊑ (λy:⋆.y) : seal_α→seal_α    α:=ι, x:seal_α ⊢ x ⊑ x : seal_α
    -----------------------------------------------------------------------------------------------------------------------
    α:=ι, x:seal_α ⊢ (νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x ⊑ (λy:⋆.y)x : seal_α
    -----------------------------------------------------------------------------------------
    α:=ι ⊢ (λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) ⊑ (λx:⋆.(λy:⋆.y)x) : seal_α→seal_α
    ------------------------------------------------------------------------------------------------------------
    α:=ι ⊢ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) @ +(seal_α→seal_α)) ⊑ (λx:⋆.(λy:⋆.y)x) : tag_ι→tag_ι    α:=ι ⊢ c ⊑ c⋆ : tag_ι
    -------------------------------------------------------------------------------------------------------------------------------------
    α:=ι ⊢ ((λx:α.(νβ:=α.(ΛY.λy:Y.y)β @ +(seal_β→seal_β))x) @ +(seal_α→seal_α)) c ⊑ (λx:⋆.(λy:⋆.y)x)c⋆ : tag_ι


========================================================================
THE DEVELOPMENT
========================================================================

## Syntax

    Types                 A,B,C      ::=  α | X | ι | ★ | A→B | ∀X.B[X]
    Atomic types          a          ::=  α | X | ι | ★
    Ground types          G,H        ::=  α | ι | ★→★
    Terms                 L,M,N      ::=  x | λx.N[x] | L M | ΛX.V[X] | L α
                                        | να:=A.N[α] | κ | M ⊕ N | M @ ±p | blame
    Imprecision           p,q,r,s,t  ::=  g | id_⋆ | g;tag_G | seal_α;p | να.p[α]
    Cross imprecision     f,g,h      ::=  id_α | id_X | id_ι | p→q | ∀X.p[X]
    Values                V,W        ::=  λx.N[x] | ΛX.V[X] | κ
                                        | V @ +(g;tag_G) | V @ -(seal_α;p)
                                        | V @ ±(s→t) | V @ ±(∀X.p[X]) | V @ —(να.p[α])
    Environments          Γ,Δ        ::=  ∅ | Γ, α:=A | Γ, X | Γ, x:A
    Stores                Σ,Π        ::=  ∅ | Σ, α:=A


    The formal system only defines id_a for atomic a. But we define
    id_A as an abbreviation, where:
      id_{A→B} = id_A → id_B
      id_{∀X.B[X]} = ∀X.id_{B[X]}
    
    tag_G abbreviates (id_G;tag_G)
    seal_α abbreviates (seal_α;id_A) when α:=A ∈ Σ

    We have the following embedding of System F into our system.
       Assume L : ∀X.B[X].
       (L A) ~> (να:=A. L α @ +id_{B[X]}[id_X:=seal_α])
    where id_{B[X]}[id_X:=seal_α] stands for id_{B[X]} with each occurrence of id_X replaced by seal_α.

## Imprecision (Γ | Σ ⊢ p : A ⊑ B) (Γ ⊢ p : A ⊑ B)

    Assume Γ, Σ ⊢ A and Γ ⊢ B

    -------------------- (a ∉ dom(Σ))  (1)
    Γ | Σ ⊢ id_a : a ⊑ a

    Γ | Σ ⊢ g : A ⊑ G
    ------------------------- (G ∉ dom(Σ))  (2)
    Γ | Σ ⊢ (g;tag_G) : A ⊑ ★

    Γ | Σ ⊢ p : A ⊑ B
    -------------------------- (α:=A) ∈ Σ
    Γ | Σ ⊢ (seal_α;p) : α ⊑ B

    Γ | Σ ⊢ s : A ⊑ A′    Γ | Σ ⊢ t : B ⊑ B′
    ----------------------------------------
    Γ | Σ ⊢ (s→t) : A→B ⊑ A′→B′

    Γ, X | Σ ⊢ p[X] : A[X] ⊑ B[X]
    -------------------------------------
    Γ | Σ ⊢ (∀X.p[X]) : ∀X.A[X] ⊑ ∀X.B[X]

    Γ | Σ, α:=★ ⊢ p[α] : A[α] ⊑ B
    ------------------------------- α ∈ fv(A[α]), α ∉ fv(B)
    Γ | Σ ⊢ (να.p[α]) : ∀X.A[X] ⊑ B

      (1) a ∉ dom(Σ) guarantees we don't have both id_α and (seal_α;p)
          in the same imprecision judgement.

      (2) G ∉ dom(Σ) guarantees we don't have both (id_α;tag_α) and (seal_α;p)
          in the same imprecision judgement.

    Free type variables

    ftv(id_⋆)      =  ∅
    ftv(id_α)      =  {α}
    ftv(id_X)      =  {X}
    ftv(id_ι)      =  ∅
    ftv(s→t)       =  ftv(s) ∪ ftv(t)
    ftv(g;tag_G)   =  ftv(g) ∪ {α | G = α}
    ftv(seal_α;p)  =  ftv(p)
    ftv(∀X.p[X])   =  ftv(p[X]) / {X}
    ftv(να.p[α])   =  ftv(p[α])

    Free store variables

    fsv(id_⋆)      =  ∅
    fsv(id_α)      =  ∅
    fsv(id_X)      =  ∅
    fsv(id_ι)      =  ∅
    fsv(s→t)       =  fsv(s) ∪ fsv(t)
    fsv(g;tag_G)   =  fsv(g)
    fsv(seal_α;p)  =  {α} ∪ fsv(p)
    fsv(∀X.p[X])   =  fsv(p[X])
    fsv(να.p[α])   =  fsv(p[α]) / {α}

    Environment and types determine derivation.
      if Γ | Σ ⊢ p : A ⊑ B and Γ | Σ ⊢ p′ : A ⊑ B then p = p′

    Derivation determines environment and types.
      if Γ | Σ ⊢ p : A ⊑ B and Γ′ | Σ′ ⊢ p : A′ ⊑ B′ then
        (i)   types agree: A = A′ and B = B′
        (ii)  Γ and Γ′ agree on ftv(p): ftv(p) ⊆ dom(Γ) ∩ dom(Γ′)
        (iii) Σ and Σ′ agree on fsv(p): for each α in fsv(p), α:=A ∈ Σ ∩ Σ′ for some A.

    Write Γ ⊢ p : A ⊑ B if Γ = Δ, Σ and Δ | Σ ⊢ p : A ⊑ B for some Δ and Σ.


## Composition

    Γ, Σ | Π ⊢ p : A ⊑ B    Γ | Σ ⊢ q : B ⊑ C
    -----------------------------------------
    Γ | Σ, Π ⊢ (p ⨾ q) : A ⊑ C

    s ⨾ t = r   (by cases on s)

        id_★ ⨾ t                 =  t
        (g ; tag_G) ⨾ id_★       =  (g ; tag_G)
        (seal_α ; s) ⨾ t         =  seal_α ; (s ⨾ t)
        (να. s[α]) ⨾ t           =  να.(s[α] ⨾ t)

    g ⨾ t = r  (by cases on t)

        g ⨾ (h ; tag_G)          =  (g ⨾ h) ; tag_G
        id_α ⨾ (seal_α; s)       =  seal_α; s
        (∀X. s[X]) ⨾ (να. t[α])  =  να.(s[α] ⨾ t[α])

    g ⨾ h = f  (by cases on g)

        id_ι ⨾ id_ι              =  id_ι
        id_α ⨾ id_α              =  id_α
        (p -> q) ⨾ (r -> s)      =  (p ⨾ r) -> (q ⨾ s)
        (∀X. p[X]) ⨾ (∀X. q[X])  =  ∀X.(p[X] ⨾ q[X])


## Factoring

    We can factor imprecision into casts and conversions.

    Casts           c, d       ::=  id_a | c;tag_G | c→d | ∀X.c[X] | να.c[α]
    Conversions     φ, ψ       ::=  id_a | φ→ψ | ∀X.φ[X] | seal_α;φ

    Claim. For every p there exist c and φ such that p = φ ⨾ c.

    Proof.
      id_a = id_a⨾id_a
      p;tag_G =(induction) (φ⨾c);tag_G = φ⨾(c;tag_G)
      p→q =(induction) (φ⨾c)→(ψ⨾d) = (φ→ψ)⨾(c→d)
      ∀X.p[X] =(induction) ∀X.(φ[X]⨾c[X]) = (∀X.φ[X])⨾(∀X.c[X])
      να.p[α] =(induction) να.(φ[α]⨾c[α]) = (∀X.φ[X])⨾(να.c[α])
      seal_α;p =(induction) seal_α;(φ⨾c) = (seal_α;φ)⨾c
      

## Types (Γ ⊢ A)

    ----- α ∈ dom(Γ)
    Γ ⊢ α

    ----- X ∈ dom(Γ)
    Γ ⊢ X

    -----
    Γ ⊢ ι

    Γ ⊢ A    Γ ⊢ B
    --------------
    Γ ⊢ A→B

    Γ, X ⊢ B[X]
    -----------
    Γ ⊢ ∀X.B[X]

    -----
    Γ ⊢ ★


## Environments (Γ wf)

    ∅ wf

    Γ wf    Γ ⊢ A
    ------------- (α ∉ dom(Γ))
    Γ, α:=A wf

    Γ wf
    ------- (X ∉ dom(Γ))
    Γ, X wf

    Γ wf    Γ ⊢ A
    ------------- (x ∉ dom(Γ))
    Γ, x:A wf

    Lemma (Well-formed contexts are closed under prefix).
      If Γ, Δ wf then Γ wf.


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

    Γ ⊢ M : A    Γ ⊢ p : A ⊑ B
    -------------------------- (Upcast/Concretion)
    Γ ⊢ M @ +p : B

    Γ ⊢ M : B    Γ ⊢ p : A ⊑ B
    -------------------------- (Downcast/Abstraction)
    Γ ⊢ M @ —p : A

    Γ ⊢ A
    -------------
    Γ ⊢ blame : A

    Lemma (Sanity). If Γ ⊢ M : A then Γ wf and Γ ⊢ A.

    Lemma (Substitution).
      If Γ, x:A, Δ ⊢ N[x] : B
      and Γ, Δ ⊢ M : A
      then Γ, Δ ⊢ N[M] : B

    Abbreviation.  L A ~~> να:=A.(L α : @ +B[seal_α])
      where L : ∀X.B[X]


## Weakening

  If Γ ⊢ M : A then Γ, Δ ⊢ M : A


## Canonical forms

  If Γ ⊢ V : A then V : A matches one of the following
    κ              : ι
    λx:A.N[x]      : A → B
    W @ ±(s→t)     : A → B
    ΛX.V[X]        : ∀X.A[X]
    W @ ±(∀X.p[X]) : ∀X.A[X]
    W @ -(να.p[α]) : ∀X.A[X]
    W @ -seal_α(p) : α
    W @ +tag_G(p)  : ★


## Evaluation contexts (Γ ⊢ E : A ~~> B)

    E ::= □ | E M | V E | E α | E ⊕ M | V ⊕ E | E @ +p | E @ -p

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

    Γ ⊢ E C ~~> A    Γ ⊢ p : A ⊑ B
    ------------------------------
    Γ ⊢ E @ +p : C ~~> B

    Γ ⊢ E C ~~> B    Γ ⊢ p : A ⊑ B
    ------------------------------
    Γ ⊢ E @ -p : C ~~> A

    Lemma (Sanity). If Γ ⊢ E : A ~~> B
      then Γ wf and Γ ⊢ A and Γ ⊢ B

    Lemma (Plug).
      If  Γ ⊢ E : A ~~> B
      and Γ ⊢ M : A
      then Γ ⊢ E[M] : B.


## Reduction rules (M ⊢→ N, Σ ⊢ M —→ Π ⊢ N, Σ ⊢ M —→ blame)

  If Γ | Σ, α:=★ ⊢ r[α] : A[α] ⊑ B
  then Γ | Σ ⊢ r[seal_α:=tag_α] : A[α] ⊑ B
  stands for r[α] with each instance of (seal_α;id_⋆) replaced by (id_α;tag_α).

    κ ⊕ κ′                         ⊢→  δ(⊕)(κ,κ′)
    (λx.N[x]) V                    ⊢→  N[V]
    (ΛX.V[X]) α                    ⊢→  V[α]
    V @ ±id_a                      ⊢→  V
    (V @ ±(s→t)) W                 ⊢→  V (W @ ∓s) @ ±t
    (V @ ±(∀X.p[X])) α             ⊢→  V α @ ±p[α]
    V @ +(να.p[α])                 ⊢→  να:=★.(V α @ +p[α])
    (V @ —(να.p[α])) β             ⊢→  V @ -p[seal_α:=tag_β]
    V @ +(g;tag_G) @ —(h;tag_G)    ⊢→  V @ +g @ —h
    V @ +(g;tag_G) @ —(h;tag_H)    ⊢→  blame,   G ≠ H
    V @ -(seal_α;p) @ +(q;seal_α)  ⊢→  V @ -p @ +q

    M ⊢→ N
    ----------------------
    Σ ⊢ E[M]  —→  Σ ⊢ E[N]

    ---------------------------------------- α ∉ dom(Σ)
    Σ ⊢ E[να:=A.N[α]]  —→  Σ, α:=A ⊢ E[N[α]]

    -----------------------
    Σ ⊢ E[blame]  —→  blame


## Composition of upcasts and downcasts

  Lemma. The following hold, where ≅ is observational equivalence.

    M @ +(p ⨾ q) ≅ M @ +p @ +q
    M @ —(p ⨾ q) ≅ M @ —q @ —p


## Thunking

  Let tt:⊤ be the unit value of unit type.

  We convert arbitrary terms under Λ to values under Λ by a translation:
    ⟦ ΛX.N[X] ⟧  =  ΛX.λx:⊤.⟦ N[X] ⟧
    ⟦ L α ⟧      =  L α tt

  If we apply the translation uniformly to the reduction rules, something goes wrong. What?

        ⟦ (ΛX.N[X]) α ⟧
    ~>  (ΛX.λx:⊤.⟦ N[X] ⟧) α tt
    —↠  ⟦ N[α] ⟧
    
        ⟦ (L @ -να.p[α]) α ⟧
    ~>  (⟦ L ⟧ @ -(να.id_⊤→p[α])) α tt
    —↠  να:=★. (⟦ L ⟧ α @ -(id_⊤→p[seal_α:=tag_α])) tt
    —↠  να:=★. (⟦ L ⟧ α tt @ -(p[seal_α:=tag_α]))
    <~  ⟦ να:=★. (L α @ -(p[seal_α:=tag_α])) ⟧

        ⟦ (L @ +να.p[α]) ⟧
    ~>  (να:=★. ⟦ L ⟧ α @ +(id_⊤→p[α]))
        Not in the image of the translation, because missing application to tt.
        This is why we can't apply the transformation uniformly to the reduction rules!
      
        In particular, the problematic example behaves as follows.
        ⟦ ((ΛX.blame) @ +(να.seal_α) @ -(να.seal_α)) ⟧
    ~>  ((ΛX.λx:⊤.blame) @ +(να.id_⊤→seal_α) @ -(να.id_⊤→seal_α))
    —↠  (να:=★. (ΛX.λx:⊤.blame) α @ +(id_⊤→seal_α) @ -(να.id_⊤→seal_α))
    —↠  (να:=★. (λx:⊤.blame) @ +(id_⊤→seal_α) @ -(να.id_⊤→seal_α))
        Not in the image of the translation.

        If all polymorphic terms are applied, we stay in the image of the translation.
        ⟦ ((ΛX.blame) @ +(να.seal_α) @ -(να.seal_α)) α ⟧
    ~>  ((ΛX.λx:⊤.blame) @ +(να.id_⊤→seal_α) @ -(να.id_⊤→seal_α)) α tt
    —↠  (να:=★. (ΛX.λx:⊤.blame) α @ +(id_⊤→seal_α) @ -(να.id_⊤→seal_α)) α tt
    —↠  (να:=★. (λx:⊤.blame) @ +(id_⊤→seal_α) @ -(να.id_⊤→seal_α)) α tt
    —↠  (να:=★. (λx:⊤.blame) @ +(id_⊤→seal_α) @ -(id_⊤→tag_α)) tt
    —↠  να:=★. (λx:⊤.blame) tt @ +(seal_α) @ -(tag_α)
    —↠  να:=★. blame @ +(seal_α) @ -(tag_α)
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
          + V = V′ @ ±(s→t) in which case
            (V′ @ ±(s→t)) W ⊢→ V′ (W @ ∓s) @ ±t

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
        - V = W @ ±(∀X.p[X]) and
          (W @ ±(∀X.p[X])) α ⊢→ W α @ ±p[α]
        - V = W @ -(να.p[α]) and
          (W @ -(να.p[α])) α ⊢→ W @ -p[seal_α:=tag_α]

    Σ, α:=A ⊢ N[α] : B
    ----------------------
    Σ ⊢ να:=A.N[α] : B

      να:=A.N[α] = □(να:=A.N[α])

    Σ wf
    --------- tp(κ) = ι
    Σ ⊢ κ : ι

      κ is a value

    Γ ⊢ M : ι    Γ | Σ ⊢ N : ι′
    ---------------------------- tp(⊕) = ι → ι′ → ι″
    Γ ⊢ M ⊕ N : ι″

      By progress on M either:
      * M = E[P] in which case M ⊕ N = (E ⊕ N)[P]
      * M is a value V, in which case by progress on N either:
        - N = E[P] in which case M ⊕ N = (V ⊕ E)[P]
        - N is a value W, in which case
          by canonical forms we have V = κ and W = κ′ and
          κ ⊕ κ′ ⊢→ δ(⊕)(κ,κ′)

    Σ ⊢ M : A    Σ ⊢ p : A ⊑ B
    --------------------------
    Σ ⊢ M @ +p : B

      By progress on M either:
      * M = E[P] in which case M @ +p = (E @ +p)[P]
      * M is a value V, in which case p is either:
        - id_a, in which case
          V @ +id_a ⊢→ V
        - g;tag_G, in which case
          (V @ +(g;tag_G)) is a value
        - s→t, in which case
          (V @ +(s→t)) is a value
        - ∀X.p[X], in which case
          (V @ +(∀X.p[X])) is a value
        - να.p[α], in which case
          V @ +(να.p[α]) ⊢→ να:=⋆.(V α @ + p[α])
        - seal_α;q, in which case
          by canonical forms V = (W @ -(seal_α;p)) and
          W @ -(seal_α;p) @ +(seal_α;q) ⊢→ W @ -p @ +q

    Σ ⊢ M : B    Σ ⊢ p : A ⊑ B
    --------------------------
    Σ ⊢ M @ —p : A

      By progress on M either:
      * M = E[P] in which case M @ -p = (E @ -p)[P]
      * M is a value V, in which case p is either:
        - id_a, in which case
          V @ -id_a ⊢→ V
        - h;tag_H, in which case
          by canonical forms V has the form (W @ +(g;tag_G)) and either
          + G = H, in which case
            V @ +(g;tag_G) @ —(h;tag_G) ⊢→ V @ +g @ —h
          + G ≠ H, in which case
            V @ +tag_G(p) @ —tag_H(q) ⊢→ blame
        - s→t, in which case
          (V @ -(s→t)) is a value
        - ∀X.p[X], in which case
          (V @ -(∀X.p[X])) is a value
        - να.p[α], in which case
          (V @ -(να.p[α])) is a value
        - seal_α;p, in which case
          (V @ -(seal_α;p)) is a value

    Γ ⊢ A
    -------------
    Γ ⊢ blame : A

      blame = □[blame]

    QED

  Progress 2.  If Σ ⊢ M : A then either:
  * M = V, where V is a value.
  * Σ ⊢ M —→ Π ⊢ N, for some Π and N.
  * Σ ⊢ M —→ blame.

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

  Preservation 1. If Σ ⊢ M : A and M ⊢→ N  then Σ ⊢ N : A.

  By case analysis of the reduction rules.

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

        Σ ⊢ V : a    Σ ⊢ id_a : a ⊑ a
        -----------------------------
        Σ ⊢ V @ ±id_a : a
      ⊢→
        Σ ⊢ V : a

    (V @ +(s→t)) W  ⊢→  V (W @ -s) @ +t

                       Σ ⊢ s : A ⊑ A′    Σ ⊢ t : B ⊑ B′
                       --------------------------------
        Σ ⊢ V : A→B    Σ ⊢ s→t : A→B ⊑ A′→B′
        ------------------------------------
        Σ ⊢ V @ +(s→t) : A′ → B′                Π ⊢ W : A′
        --------------------------------------------------
        Σ ⊢ (V @ +(s→t)) W : B′
      ⊢→
                       Σ ⊢ W : A′    Σ ⊢ s : A ⊑ A′
                       ----------------------------
        Σ ⊢ V : A→B    Σ ⊢ W @ -s : A
        -----------------------------
        Σ ⊢ V (W @ -s) : B               Σ ⊢ t : B ⊑ B′
        -----------------------------------------------
        Σ ⊢ V (W @ -s) @ +t : B′

    (V @ -(s→t)) W  ⊢→  V (W @ +s) @ -t

                         Σ ⊢ s : A ⊑ A′    Σ ⊢ t : B ⊑ B′
                         --------------------------------
        Σ ⊢ V : A′→B′    Σ ⊢ s→t : A→B ⊑ A′→B′
        --------------------------------------
        Σ ⊢ V @ -(s→t) : A → B                    Σ ⊢ W : A
        ---------------------------------------------------
        Σ ⊢ (V @ -(s→t)) W : B
      ⊢→
                         Σ ⊢ W : A    Σ ⊢ s : A ⊑ A′
                         ---------------------------
        Σ ⊢ V : A′→B′    Σ ⊢ W @ +s : A′
        --------------------------------
        Σ ⊢ V (W @ +s) : B′                 Σ ⊢ t : B ⊑ B′
        --------------------------------------------------
        Σ ⊢ V (W @ +s) @ -t : B

    (V @ ±(∀X.p[X])) α  ⊢→  V α @ ±p[α]

                           Σ, X ⊢ p[X] : A[X] ⊑ B[X]
                           -------------------------------
        Σ ⊢ V : ∀X.A[X]    Σ ⊢ ∀X.p[X] : ∀X.A[X] ⊑ ∀X.B[X]
        --------------------------------------------------
        Σ ⊢ V @ +(∀X.p[X]) : ∀X.B[X]
        ----------------------------- α:=C ∈ Σ
        Σ ⊢ (V @ +(∀X.p[X])) α : B[α]
      ⊢→
        Σ ⊢ V : ∀X.A[X]
        --------------- α:=C ∈ Σ
        Σ ⊢ V α : A[α]              Σ ⊢ p[α] : A[α] ⊑ B[α]
        --------------------------------------------------
        Σ ⊢ V α @ +p[α] : B[α]

        (and similarly for swapped signs)

    V @ +(να.p[α])  ⊢→  να:=⋆. V α @ + p[α]

                           Σ, α:=⋆ ⊢ p[α] : A[α] ⊑ B
                           -------------------------
        Σ ⊢ V : ∀X.A[X]    Σ ⊢ να.p[α] : ∀X.A[X] ⊑ B
        --------------------------------------------
        Σ ⊢ V @ +(να.p[α]) : B
      ⊢→
        Σ, α:=⋆ ⊢ V : ∀X.A[X]
        ---------------------
        Σ, α:=⋆ ⊢ V α : A[α]     Σ, α:=⋆ ⊢ p[α] : A[α] ⊑ B
        --------------------------------------------------
        Σ, α:=⋆ ⊢ (V α @ +p[α]) : B
         ----------------------------
        Σ ⊢ (να:=⋆. V α @ + p[α]) : B

    (V @ —(να.p[α])) α  ⊢→  V @ -p[seal_α:=tag_α]

                     Σ, α:=⋆ ⊢ p[α] : A[α] ⊑ B
                     -------------------------
        Σ ⊢ V : B    Σ ⊢ να.p[α] : ∀X.A[X] ⊑ B
        --------------------------------------
        Σ ⊢ V @ —(να.p[α]) : ∀X.A[X]
        ------------------------------------ α:=C ∈ Σ
        Σ ⊢ (V @ —(να.p[α])) α : A[β]
      ⊢→
        Σ ⊢ V : B    Σ ⊢ p[seal_α:=tag_β] : A[β] ⊑ B
        -------------------------------------------- β:=C ∈ Σ
        Σ ⊢ V @ -p[seal_α:=tag_β] : A[β]

    V @ +(g;tag_G) @ —(h;tag_G)  ⊢→  V @ +g @ —h

                     Σ ⊢ g : A ⊑ G
                     -------------------
        Σ ⊢ V : A    Σ ⊢ g;tag_G : A ⊑ ★    Σ ⊢ h : B ⊑ G      
        --------------------------------    -------------------
        Σ ⊢ V @ +(g;tag_G) : ★              Σ ⊢ h;tag_G : B ⊑ ★     
        -------------------------------------------------------
        Σ ⊢ V @ +(g;tag_G) @ —(h;tag_G) : B
      ⊢→
        Σ ⊢ V : A    Σ ⊢ g : A ⊑ G
        --------------------------
        Σ ⊢ V @ +g : G                Σ ⊢ h : B ⊑ G
        -------------------------------------------
        Σ ⊢ V @ +p @ —q : B

    V @ +tag_G(p) @ —tag_H(q)  ⊢→  blame,  if G ≠ H

        (similar to above)

    V @ -(seal_α;p) @ +(seal_α;q)  ⊢→  V @ -p @ +q

                     Σ ⊢ p : C ⊑ A
                     --------------------
        Σ ⊢ V : A    Σ ⊢ seal_α;p : α ⊑ A    Σ ⊢ q : C ⊑ B
        ---------------------------------    --------------------
        Σ ⊢ V @ -(seal_α;p) : α              Σ ⊢ seal_α;q : α ⊑ B
        ---------------------------------------------------------
        Σ ⊢ V @ -(seal_α;p) @ +(seal_α;q) : B
      ⊢→
                              
        Σ ⊢ V : A    Σ ⊢ p : C ⊑ A
        --------------------------
        Σ ⊢ V @ -p : C                Σ ⊢ q : C ⊑ B
        -------------------------------------------
        Σ ⊢ V @ -p @ +q : B


    Preservation 2. If Σ ⊢ M : A and Σ ⊢ M —→ Π ⊢ N then Π ⊢ N : A.
                    If Σ ⊢ M : A and Σ ⊢ M —→ blame then ∅ ⊢ blame : A.

    M ⊢→ N
    --------------------
    Σ ⊢ E[M] —→ Σ ⊢ E[N]

        Σ ⊢ M : A    Σ ⊢ E : A ~~> B
        ----------------------------
        Σ ⊢ E[M] : B
     —→
        Σ ⊢ N : A    Σ ⊢ E : A ~~> B
        ----------------------------
        Σ ⊢ E[N] : B

    ----------------------------------------
    Σ ⊢ E[να:=A.N[α]]  —→  Σ, α:=C ⊢ E[N[α]]

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

    -----------------------
    Σ ⊢ E[blame]  —→  blame

        Σ ⊢ blame : A    Σ ⊢ E : A ~~> B
        --------------------------------
        Σ ⊢ E[blame] : B
      —→
        ∅ ⊢ blame : B


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


## Imprecision between imprecisions (γ ⊢ p ⊑ q, γ ⊩ p ⊑ q)

    Assume
      γ : Γ ⊑ Γ′
      σ : Σ ⊑ Σ′
      Γ, Σ ⊢ A
      Γ′, Σ′ ⊢ A
      Γ ⊢ B
      Γ′ ⊢ B
      Γ | Σ ⊢ p : A ⊑ B
      Γ′ | Σ′ ⊢ q : A ⊑ B


### Syntactic definition (γ | σ ⊢ p : A ⊑ B)

    X ∈ γ
    -------------------
    γ | σ ⊢ id_X ⊑ id_X

    α:=p ∈ γ
    -------------------
    γ | σ ⊢ id_α ⊑ id_α

    γ | σ ⊢ g ⊑ g′
    ------------------------------ (G ∉ dom(σ))
    γ | σ ⊢ (g;tag_G) ⊑ (g′;tag_G)

    γ | σ ⊢ q ⊑ p ⨾ q′
    -------------------------------- (α:=p) ∈ σ
    γ | σ ⊢ (seal_α;q) ⊑ (seal_α;q′)

    ------------------------------------ (α:=A) ∈ γ, (α:=☆) ∈ σ
    γ | σ ⊢ (id_α;tag_α) ⊑ (seal_α;id_⋆)

    γ | σ ⊢ s ⊑ s′    γ | σ ⊢ t ⊑ t′
    --------------------------------
    γ | σ ⊢ (s→t) ⊑ (s′→t′)

    γ, X | σ ⊢ p[X] ⊑ p′[X]
    ------------------------------
    γ | σ ⊢ (∀X.p[X]) ⊑ (∀X.p′[X])

    γ | σ, α:=★ ⊢ p[α] ⊑ p′[α]
    -----------------------------
    γ | σ ⊢ (να.p[α]) ⊑ (να.p[α])
    

    Write γ ⊢ p ⊑ p′ iff γ = δ, π and δ | π ⊢ p ⊑ p′


### Semantic definition (γ | σ ⊩ p ⊑ p′)

    Def'n. 
    Assume p : A ⊑ B, q : A ⊑ B, γ : Γ ⊑ Γ′, σ : Σ ⊑ Σ′
    γ | σ ⊩ p ⊑ q holds iff
    for every Γ ⊢ E : B ~> ι and Γ, Σ ⊢ V : A, we have E[V @ +p]⇓ implies E[V @ +q]⇓ and
    for every Γ, Σ ⊢ E : A ~> ι and Γ ⊢ V : B, we have E[V @ -p]⇓ implies E[V @ -q]⇓ 

    Equivalent Def'n.
    Assume γ | σ ⊩ p ⊑ q if p : A ⊑ B, q : A ⊑ B, γ : Γ ⊑ Γ′, σ : Σ ⊑ Σ′
    γ | σ ⊩ p ⊑ q holds iff
    for every 𝒞 : Γ ⊢ B ~> ∅ ⊢ ι and Γ, Σ ⊢ M : A, we have 𝒞[M @ +p]⇓ implies 𝒞[M @ +q]⇓ and
    for every 𝒞 : Γ, Σ ⊢ A ~> ∅ ⊢ ι and Γ ⊢ M : B, we have 𝒞[M @ -p]⇓ implies 𝒞[M @ -q]⇓ 

    Proof sketch. If 𝒞[M @ +p] —↠ W then it factors into 𝒞[M @ +p] —↠ E[V @ +p] —↠ W.

    (Can we show that semantic for upcasts implies semantic for downcasts, or vice versa?)
      
      
### Sound and complete

      γ | σ ⊢ p ⊑ p′ iff γ | σ ⊩ p ⊑ p′

      Sound is probably easy to prove, but I'm not sure about complete.


## Term imprecision (γ ⊢ M ⊑ M′ : p)

    Assume γ : Γ ⊑ Γ′, Γ ⊢ M : A, Γ′ ⊢ M′ : A′, Γ ⊢ p : A ⊑ A′.

    (drop)
      γ, α:=A ⊢ M[α] ⊑ M′ : p[α]
      -------------------------- α ∉ fv(M′) and q : A ⊑ B
      γ, α:=q ⊢ M[α] ⊑ M′ : p[α]

    (merge)
      γ, α:=q ⊢ M[α] ⊑ M′[α] : p[α]
      ------------------------------------- α ∉ fv(M′[αᵢ]) and q : A ⊑ ⋆
      γ, α:=A, αᵢ:=☆ ⊢ M[α] ⊑ M′[αᵢ] : p[α]
      
    (x⊑x)
      γ : Γ ⊑ Γ′
      ------------- x:p ∈ γ
      γ ⊢ x ⊑ x : p

    (λ⊑λ)
      γ ⊢ Γ ⊑ Γ′    Γ ⊢ p : A ⊑ A′    γ, x:=p ⊢ N[x] ⊑ N′[x] : q
      ----------------------------------------------------------
      γ ⊢ λx:A.N[x] ⊑ λx:A′.N′[x] : p→q

    (·⊑·)
      γ ⊢ L ⊑ L′ : p→q    γ ⊢ M ⊑ M′ : p
      ----------------------------------
      γ ⊢ L M ⊑ L′ M′ : q

    (Λ⊑)
      γ ⊢ Γ ⊑ Γ′    γ, α:=★ ⊢ V[α] ⊑ N : q[α]
      --------------------------------------- seal_α, tag_α ∉ V[α]
      γ ⊢ ΛX.V[X] ⊑ N : να.q[α]

    (Λ⊑Λ)
      γ, X ⊢ V[X] ⊑ V′[X] : q[X]
      --------------------------------
      γ ⊢ ΛX.V[X] ⊑ ΛX.V′[X] : ∀X.q[X]

    (α⊑α)
      γ ⊢ L ⊑ L′ : ∀X.p[X]
      ---------------------------
      γ, α:=q ⊢ L α ⊑ L′ α : p[α]

    (α⊑)
      γ ⊢ L ⊑ L′ : να.p[α]
      ------------------------------------------ (*) 
      γ, α:=A ⊢ L α ⊑ L′ : p[seal_α:=(seal_α;r)]

      (*) γ : Γ ⊑ Γ′ and Γ = Δ, Π and Δ | Π ⊢ να.p[α] : ∀X.B[X] ⊑ C and Δ | Π ⊢ r : A ⊑ ⋆
      (which guarantees r is unique)

    (ν⊑ν)
      γ, α:=p ⊢ N[α] ⊑ N′[α] : q
      --------------------------------- α ∉ fv(q)
      γ ⊢ να:=A.N[α] ⊑ να:=A′.N′[α] : q

    (ν⊑)
      γ, α:=A ⊢ N[α] ⊑ N′ : q
      ----------------------- α ∉ fv(q)
      γ ⊢ να:=A.N[α] ⊑ N′ : q

    (⊑ν)
      γ, α:=☆ ⊢ N ⊑ N′[α] : q
      ----------------------- α ∉ fv(q)
      γ ⊢ N ⊑ να:=★.N′[α] : q

    (κ⊑κ)
      ---------------- tp(κ) = ι
      γ ⊢ κ ⊑ κ : id_ι

    (⊕⊑⊕)
      γ ⊢ M ⊑ M′ : id_ι    γ ⊢ N ⊑ N′ : id_ι′
      --------------------------------------- tp(⊕) = ι → ι′ → ι″
      γ ⊢ M ⊕ N ⊑ M′ ⊕ N′ : id_ι″

    (+⊑)
      γ ⊢ M ⊑ M′ : r
      ------------------- (s ⨾ q = r)
      γ ⊢ M @ +s ⊑ M′ : q

    (⊑+)
      γ ⊢ M ⊑ M′ : p
      ------------------- (r ⊑ p ⨾ t)
      γ ⊢ M ⊑ M′ @ +t : r

    (+⊑+)
      γ ⊢ M ⊑ M′ : p
      ------------------------ (s ⨾ q ⊑ p ⨾ t)
      γ ⊢ M @ +s ⊑ M′ @ +t : q

                        q
                   B ------> B′
                   ↑       ↗ ↑
                   |  =   /  |
                   |     /   |
                 s |    / r  | t    (DIAGRAM)
                   |   /     |
                   |  /   ⊑  |
                   | /       |
                   A ------> A′
                        p

    (-⊑)
      γ ⊢ M ⊑ M′ : q
      ------------------- (s ⨾ q = r)
      γ ⊢ M @ -s ⊑ M′ : r

    (⊑-)
      γ ⊢ M ⊑ M′ : r
      ------------------- (r ⊑ p ⨾ t)
      γ ⊢ M ⊑ M′ @ -t : p

    (-⊑-)
      γ ⊢ M ⊑ M′ : q
      ------------------------ (s ⨾ q ⊑ p ⨾ t)
      γ ⊢ M @ -s ⊑ M′ @ -t : p

    The +⊑+ rule can be derived from +⊑ and ⊑+ and similarly for -⊑-.


## Reflexivity

   Define id_Γ : Γ ⊑ Γ.
   If Γ ⊢ M : A then id_Γ ⊢ M ⊑ M : id_A.


Left upcast inversion
~~~~~~~~~~~~~~~~~~~~~

If γ ⊢ M @ +s ⊑ M′ : q then γ ⊢ M ⊑ M′ : r where s ⨾ q = r

Proof by induction on the derivation of σ ⊢ M @ +s ⊑ M : q.

  (+⊑)
      γ ⊢ M ⊑ M′ : r
      ------------------- +⊑    s ⨾ q = r
      γ ⊢ M @ +s ⊑ M′ : q

      (trivial)

  (⊑+)

      γ ⊢ M ⊑ M′ : p
      -------------------- +⊑        s ⨾ r′ = p  (i)
      γ ⊢ M @ +s ⊑ M′ : r′
      ------------------------ ⊑+    q ⊑ r′ ⨾ t  (ii)
      γ ⊢ M @ +s ⊑ M′ @ +t : q
    =>
      γ ⊢ M ⊑ M′ : p    
      ------------------- ⊑+         r ⊑ p ⨾ t   (iii)
      γ ⊢ M ⊑ M′ @ +t : r
      ------------------------ +⊑    s ⨾ q = r   (iv)
      γ ⊢ M @ +s ⊑ M′ @ +t : q

   By (iv), define r = s ⨾ q. Then (iii) holds because:

        r
      = {(iv)}
        s ⨾ q
      ⊑ {(ii)}
        s ⨾ r′ ⨾ t
      = {(i)}
        p ⨾ t

  (⊑-)
      γ ⊢ M ⊑ M′ : p
      -------------------- +⊑        s ⨾ r′ = p  (i)
      γ ⊢ M @ +s ⊑ M′ : r′
      ------------------------ ⊑-    r′ ⊑ q ⨾ t  (ii)
      γ ⊢ M @ +s ⊑ M′ @ -t : q
    =>
      γ ⊢ M ⊑ M′ : p    
      ------------------- ⊑-         p ⊑ r ⨾ t   (iii)
      γ ⊢ M ⊑ M′ @ -t : r
      ------------------------ +⊑    s ⨾ q = r   (iv)
      γ ⊢ M @ +s ⊑ M′ @ -t : q

   By (iv), define r = s ⨾ q. Then (iii) holds because:

       p
     = {(i)}
       s ⨾ r′
     ⊑ {(ii)}
       s ⨾ q ⨾ t
     = {(iv)}
       r ⨾ t


Left downcast inversion (doesn't hold)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If γ ⊢ M @ -s ⊑ M′ : r then γ ⊢ M ⊑ M′ : q where s ⨾ q = r.

Proof by induction on the derivation of γ ⊢ M @ -s ⊑ M : q.

  (-⊑)
      γ ⊢ V ⊑ M′ : q
      ------------------- +⊑    s ⨾ q = r
      γ ⊢ V @ -s ⊑ M′ : r

      (trivial)

  (⊑-)

      γ ⊢ V ⊑ M′ : q
      -------------------- -⊑        s ⨾ q = r′  (i)
      γ ⊢ V @ -s ⊑ M′ : r′
      ------------------------ ⊑-    r′ ⊑ p ⨾ t  (ii)
      γ ⊢ V @ -s ⊑ M′ @ -t : p
    =>
      γ ⊢ V ⊑ M′ : q    
      ------------------- ⊑-         q ⊑ r ⨾ t   (iii)
      γ ⊢ V ⊑ M′ @ -t : r
      ------------------------ -⊑    s ⨾ r = p   (iv)
      γ ⊢ V @ -s ⊑ M′ @ -t : p

   Then it is not clear how to define r so that (iv) holds.
   And, indeed, there may be no such r, because even if
   the first derivation is possible the second may not be.
   We may need to go down on the left first to make room
   to go down on the right!

Right downcast inversion may hold. But isn't required below.


Upcast Lemma
~~~~~~~~~~~~

If σ : Σ ⊑ Σ′ and σ ⊢ V ⊑ V′ : p
then Σ′ ⊢ V′ @ +t —↠ Π′ ⊢ W′ and π : Σ ⊑ Π′ and π ⊢ V ⊑ W′ : r where r ⊑ p ⨾ t.

Proof by induction on t.

    V′ @ +id_a        ⊢→  V′
    V′ @ +(s→t)       is a value
    V′ @ +(∀X.s[X])   is a value
    V′ @ +(να.s[α])   ⊢→  να:=★.(V′ α @ +s[α])
      then apply reduction, substitution, and induction.
    V′ @ +(g;tag_G)   is a value
    V′ @ +(seal_α;t)
      then by canonical forms V′ = V″ @ -seal_α(s)
      and V″ @ -(seal_α;s) @ +(seal_α;t) —↠ V″ @ -s @ +t
      and apply induction twice (mutual induction with downcast lemma)


Downcast Lemma
~~~~~~~~~~~~~~

If σ : Σ ⊑ Σ′ and σ ⊢ V ⊑ V′ : r
then Σ′ ⊢ V′ @ -t —↠ Π′ ⊢ W′ and π : Σ ⊑ Π′ and π ⊢ V ⊑ W′ : p where r ⊑ p ⨾ t.

Proof by induction on q.

    V′ @ -id_a        ⊢↠  V′
    V′ @ -(s→t)       is a value
    V′ @ -(∀X.p[X])   is a value
    V′ @ -(να.p[α])   is a value
    V′ @ -(q;tag_G)
      then by canonical forms V′ = V″ @ +(g;tag_G)
      (it must be G and not H because σ ⊢ V ⊑ V″ : s for some s by Inversion Lemma)
      and V″ @ +(g;tag_G) @ -(h;tag_G) ⊢↠ V″ @ +g @ -h
      and apply induction twice (mutual induction with upcast lemma).
      [This is the one place Inversion Lemma is used.]
    V′ @ -(seal_α;q)  is a value


Catchup Lemma
~~~~~~~~~~~~~

If σ : Σ ⊑ Σ′ and σ ⊢ V ⊑ M′ : p
then Σ′ ⊢ M′ —↠ Π′ ⊢ W′ and π : Σ ⊑ Π′ and π ⊢ V ⊑ W′ : p.

If M′ = V′ then the result is trivial.  If M′ ≠ V′ then the only
possibility for M is that it is an upcast or downcast---and hence
result follows from upcast and downcast lemmas---or one of the
following. 

    (Λ⊑)
      σ ⊢ Σ ⊑ Σ′    Σ, X ⊢ V[X] : B[X]    σ, α:=★ ⊢ V[α] ⊑ N : q[α]
      -------------------------------------------------------------
      σ ⊢ ΛX.V[X] ⊑ N : να.q[α]

    By induction on the last premise.

    (⊑ν)
      σ, α:=☆ ⊢ N ⊑ N′[α] : q
      ----------------------- α ∉ fv(q)
      σ ⊢ N ⊑ να:=★.N′[α] : q
    ⊢→
      σ, α:=☆ ⊢ N ⊑ N′[α] : q

    And then apply induction on the premise.


Wrap downcast lemma
~~~~~~~~~~~~~~~~~~~

If σ ⊢ V @ -(s→t) ⊑ V′ : p→q and σ ⊢ W ⊑ W′ : p and σ : Σ ⊑ Σ′
then Σ′ ⊢ V′ W′ —↠ Π′ ⊢ N′ and π ⊢ V (W @ +s) @ -t ⊑ N′ : p and π : Π ⊑ Π′ for some Π′, N′, π.

Proof. By induction on the derivation of σ ⊢ V @ -(s→t) ⊑ V′ : p→q.

  Case 1.

        σ ⊢ V ⊑ V′ : s₁→t₁
        ----------------------------- -⊑  (s→t)⨾(s₁→t₁) ⊑ (s₂→t₂)
        σ ⊢ (V @ -(s→t)) ⊑ V′ : s₂→t₂                                σ ⊢ W ⊑ W′ ⊢ s₂
        ---------------------------------------------------------------------------- ·⊑·
        σ ⊢ (V @ -(s→t)) W ⊑ V′ W′ : t₂
      ⊢→
                              W ⊑ W′ : s₂
                              --------------- +⊑  s⨾s₁ ⊑ s₂
        σ ⊢ V ⊑ V′ : s₁→t₁    W @ +s ⊑ W′ : s₁
        -------------------------------------- ·⊑·
        σ ⊢ (V (W @ +s)) ⊑ V′ W′ : t₁
        ---------------------------------- -⊑  t⨾t₁ ⊑ t₂
        σ ⊢ (V (W @ +s)) @ -t ⊑ V′ W′ : t₂

  Case 2.
         
      We are given
     
        σ ⊢ (V @ -(s→t)) ⊑ V′ : s₄→t₄
        ------------------------------------------ ⊑+  s₂→t₂ ⊑ (s₄→t₄)⨾(s₃→t₃)   
        σ ⊢ (V @ -(s→t)) ⊑ (V′ @ +(s₃→t₃)) : s₂→t₂                                σ ⊢ W ⊑ W′ : s₂
        ----------------------------------------------------------------------------------------- ·⊑·
        σ ⊢ (V @ -(s→t)) W ⊑ (V′ @ +(s₃→t₃)) W′ : t₂

      From this we derive
     
        σ ⊢ W ⊑ W′ : s₂
        --------------------- ⊑-  s₂ ⊑ s₄⨾s₃
        σ ⊢ W ⊑ W′ @ -s₃ : s₄

      By catchup, W′ @ -s₃ —↠ W″ and σ ⊢ W ⊑ W″ : s₄.
      Now apply induction hypothesis where W′ = W″, p = s₄, q = t₄.
      We know V′ W″ —↠ N′ and σ ⊢ V (W @ +s) @ -t ⊑ N′ : t₄.

      Hence

           (V′ @ +(s₃→t₃)) W′
        —→ V′ (W′ @ -s₃) @ +t₃
        —↠ V′ W″ @ +t₃
        —↠ N′ @ +t₃

      and 

        σ ⊢ V (W @ +s) @ -t ⊑ N′ : t₄        
        ----------------------------------- ⊑+  t₂ ⊑ t₄⨾t₃
        σ ⊢ V (W @ +s) @ -t ⊑ N′ @ +t₃ : t₂


  Case 3.

      We are given
     
        σ ⊢ (V @ -(s→t)) ⊑ V′ : s₂→t₂
        ------------------------------------------ ⊑-  s₂→t₂ ⊑ (s₄→t₄)⨾(s₃→t₃)
        σ ⊢ (V @ -(s→t)) ⊑ (V′ @ -(s₃→t₃)) : s₄→t₄                                σ ⊢ W ⊑ W′ : s₄
        ----------------------------------------------------------------------------------------- ·⊑·
        σ ⊢ (V @ -(s→t)) W ⊑ (V′ @ -(s₃→t₃)) W′ : t₂

     From this we derive
     
        σ ⊢ W ⊑ W′ : s₄
        --------------------- ⊑+  s₂ ⊑ s₄⨾s₃
        σ ⊢ W ⊑ W′ @ +s₃ : s₂

      By catchup, W′ @ +s₃ —↠ W″ and σ ⊢ W ⊑ W″ : s₂.
      Now apply induction hypothesis where W′ = W″, p = s₂, q = t₂.
      We know V′ W″ —↠ N′ and σ ⊢ V (W @ +s) @ -t ⊑ N′ : t₂.

      Hence

           (V′ @ -(s₃→t₃)) W′
        —→ V′ (W′ @ +s₃) @ -t₃
        —↠ V′ W″ @ -t₃
        —↠ N′ @ -t₃

      and 

        σ ⊢ V (W @ +s) @ -t ⊑ N′ : t₂        
        ----------------------------------- ⊑-  t₂ ⊑ t₄⨾t₃
        σ ⊢ V (W @ +s) @ -t ⊑ N′ @ -t₃ : t₄




Gradual Guarantee
~~~~~~~~~~~~~~~~~

If σ ⊢ M ⊑ M′ : p and σ : Σ ⊑ Σ′ and Σ ⊢ M —→ Π ⊢ N
then Σ′ ⊢ M′ —↠ Π′ ⊢ N′ and π ⊢ N ⊑ N′ : p and π : Π ⊑ Π′ for some Π′, N′, π.

    κ₁ ⊕ κ₂  ⊢→  δ(⊕)(κ₁,κ₂)

      (⊕⊑⊕)
      
        σ ⊢ κ₁ ⊑ κ₁ : id_ι₁    σ ⊢ κ₂ ⊑ κ₂ : id_ι₂
        ------------------------------------------ ⊕⊑⊕
        σ ⊢ κ₁ ⊕ κ₂ ⊑ κ₁ ⊕ κ₂ : id_ι₃
      ⊢→
        σ ⊢ δ(⊕)(κ₁,κ₂) ⊑ δ(⊕)(κ₁,κ₂) : id_ι₃

    (λx.N[x]) W  ⊢→  N[W]

      Induct on the derivation of σ ⊢ λx.N[x] ⊑ N′ : p→q and use catchup.

      (λ⊑λ)

          σ, x:p ⊢ N[x] ⊑ N′[x] : q
          ---------------------------- λ⊑λ
          σ ⊢ λx.N[x] ⊑ λx.N′[x] : p→q        σ ⊢ W ⊑ W′ : p
          -------------------------------------------------- ·⊑·
          σ ⊢ (λx.N[x]) W ⊑ (λx.N′[x]) W′ : q
        ⊢→
          σ ⊢ N[W] ⊑ N′[W′] : q

          (assumes a suitable substitution lemma)

      → upcast (⊑+)

         Let V = λx.N[x]. (This means ⊑+ must be used, so we don't need inversion.)

          σ ⊢ V ⊑ V′ : p′→q′
          ------------------------- ⊑+  p→q ⊑ (p′→q′)⨾(s→t)
          σ ⊢ V ⊑ V′ @ +(s→t) : p→q                            σ ⊢ W ⊑ W′ : p
          ------------------------------------------------------------------- ·⊑·
          σ ⊢ V W ⊑ (V′ @ +(s→t)) W′ : q
        ⊢→
                                σ ⊢ W ⊑ W′ : p
                                -------------------- ⊑-  p ⊑ p′⨾t 
          σ ⊢ V ⊑ V′ : p′→q′    σ ⊢ W ⊑ W′ @ -s : p′
          ------------------------------------------ ·⊑·
          σ ⊢ V W ⊑ V′ (W′ @ -s) : q′                   
          -------------------------------- ⊑+  q ⊑ q′⨾t
          σ ⊢ V W ⊑ V′ (W′ @ -s) @ +t : q

          (and then induction)

      → downcast (⊑-)

          Let V = λx.N[x].

          σ ⊢ V ⊑ V′ : p→q
          --------------------------- ⊑-  p→q ⊑ (p′→q′)⨾(s→t)
          σ ⊢ V ⊑ V′ @ -(s→t) : p′→q′                            σ ⊢ W ⊑ W′ : p′
          ------------------------------------------------------------------- ·⊑·
          σ ⊢ V W ⊑ (V′ @ -(s→t)) W′ : q′
        ⊢→
                              σ ⊢ W ⊑ W′ : p′
                              ------------------- ⊑+  p ⊑ p′⨾t 
          σ ⊢ V ⊑ V′ : p→q    σ ⊢ W ⊑ W′ @ +s : p
          ------------------------------------------ ·⊑·
          σ ⊢ V W ⊑ V′ (W′ @ +s) : q                   
          -------------------------------- ⊑-  q ⊑ q′⨾t
          σ ⊢ V W ⊑ V′ (W′ @ +s) @ -t : q′

          (and then induction)

    (ΛX.V[X]) α  ⊢→  V[α]

      Induct on the derivation of σ ⊢ ΛX.V[X] ⊑ N′ : q.

      (Λ⊑)

        σ, α:=✯ ⊢ V[α] ⊑ N′ : q[α]
        -------------------------- Λ⊑
        σ ⊢ ΛX.V[X] ⊑ N′ : να.q[α]
        -------------------------------------------------- α⊑ where r : A ⊑ ⋆
        σ, α:=A ⊢ (ΛX.V[X]) α ⊑ N′ : q[seal_α:=(seal_α;r)]
      ⊢→
        σ, α:=A ⊢ V[α] ⊑ N′ : q[seal_α:=(seal_α;r)]

      (Λ⊑Λ)

        σ, X ⊢ V[X] ⊑ V′[X] : q[X]
        -------------------------------- Λ⊑Λ
        σ ⊢ ΛX.V[X] ⊑ ΛX.V′[X] : ∀X.q[X]        
        ------------------------------------- α⊑α where α:=p ∈ σ
        σ ⊢ (ΛX.V[X]) α ⊑ (ΛX.V′[X]) α : q[α]
      ⊢→
        σ ⊢ V[α] ⊑ V′[α] : q[α]

      ∀ upcast (⊑+)

        σ ⊢ V ⊑ V′ : ∀X.q[X]
        --------------------------------- ⊑+  ∀X.r[X] ⊑ (∀X.p[X])⨾(∀X.q[X])
        σ ⊢ V ⊑ V′ @ +(∀X.p[X]) : ∀X.r[X]
        ------------------------------------ α⊑α  α:=s ∈ σ
        σ ⊢ V α ⊑ (V′ @ +(∀X.p[X])) α : r[α]
      ⊢→
        σ ⊢ V ⊑ V′ : ∀X.q[X]    
        --------------------- α⊑α  α:=s ∈ σ
        σ ⊢ V α ⊑ V′ α : q[α]
        ----------------------------- ⊑+    r[X] ⊑ p[X]⨾q[X]
        σ ⊢ V α ⊑ V′ α @ +p[α] : r[α]

        (and then induction)

      ∀ downcast (⊑-)

        σ ⊢ V ⊑ V′ : ∀X.r[X]
        --------------------------------- ⊑+  ∀X.r[X] ⊑ (∀X.p[X])⨾(∀X.q[X])
        σ ⊢ V ⊑ V′ @ -(∀X.p[X]) : ∀X.q[X]
        ------------------------------------ α⊑α  α:=s ∈ σ
        σ ⊢ V α ⊑ (V′ @ -(∀X.p[X])) α : q[α]
      ⊢→
        σ ⊢ V ⊑ V′ : ∀X.r[X]    
        --------------------- α⊑α  α:=s ∈ σ
        σ ⊢ V α ⊑ V′ α : r[α]
        ----------------------------- ⊑+    r[X] ⊑ p[X]⨾q[X]
        σ ⊢ V α ⊑ V′ α @ -p[α] : q[α]

        (and then induction)
        
      ν Downcast (⊑-)

        σ, α:=✯ ⊢ V[α] ⊑ V′ : r[α]
        ---------------------------- Λ⊑
        σ ⊢ (ΛX.V[X]) ⊑ V′ : να.r[α]
        ----------------------------------------- ⊑-  να.r[α] ⊑ (∀X.p[X])⨾(να.q[α])
        σ ⊢ (ΛX.V[X]) ⊑ V′ @ -(να.q[α]) : ∀X.p[X]
        -------------------------------------------------- α⊑α
        σ, α:=s ⊢ (ΛX.V[X]) α ⊑ (V′ @ -(να.q[α])) α : p[α]
      ⊢→
        σ, α:=✯ ⊢ V[α] ⊑ V′ : r[α]
        ---------------------------------------------- ⊑-  r[α] ⊑ p[α]; q[seal_α:=tag_α]
        σ, α:=s ⊢ V[α] ⊑ V′ @ -q[seal_α:=tag_α] : p[α]

    V @ ±id_a  ⊢→  V

        σ ⊢ V ⊑ M : p    id_a : a ⊑ a
        -----------------------------
        σ ⊢ V @ ±id_a ⊑ M : p
      ⊢→
        σ ⊢ V ⊑ M : p

    (V @ +(s→t)) W  ⊢→  V (W @ -s) @ +t

      By left upcast inversion we have:

        σ ⊢ V ⊑ L : s₂→t₂
        ---------------------------- +⊑  (s→t)⨾(s₁→t₁) ⊑ (s₂→t₂)
        σ ⊢ (V @ +(s→t)) ⊑ L : s₁→t₁                                σ ⊢ W ⊑ M ⊢ s₁
        -------------------------------------------------------------------------- ·⊑·
        σ ⊢ (V @ +(s→t)) W ⊑ L M : t₁
      ⊢→
                             W ⊑ M : s₁
                             --------------- -⊑  s⨾s₁ ⊑ s₂
        σ ⊢ V ⊑ L : s₂→t₂    W @ -s ⊑ M : s₂
        ------------------------------------ ·⊑·
        σ ⊢ (V (W @ -s)) ⊑ L M : t₂
        -------------------------------- +⊑  t⨾t₁ ⊑ t₂
        σ ⊢ (V (W @ -s)) @ +t ⊑ L M : t₁

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
      ⊢→
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
      ⊢→
        ρ ⊢ V ⊑ L : ∀X.r[X]
        -------------------- α⊑α    α:=s ∈ ρ
        ρ ⊢ V α ⊑ L α : r[α]
        ------------------------------ +⊑    p[α]⨾q[α] ⊑ r[α]
        ρ ⊢ V α @ +p[α] ⊑ L α : q[α]

      (iii)
        (and similarly for -(∀X.p[X]))

    V @ +(να.p[α])  ⊢→  να:=★.(V α @ +p[α])

                                  p[α] : A[α] ⊑ B
                                  ---------------------
         σ ⊢ V ⊑ L : (να.r[α])    να.p[α] : ∀X.A[X] ⊑ B
         ---------------------------------------------- +⊑   (να.p[α])⨾q ⊑ (να.r[α])
         σ ⊢ V @ +(να.p[α]) ⊑ L : q
       ⊢→
         σ, α:=★ ⊢ V ⊑ L : (να.r[α])       
         --------------------------- α⊑    
         σ, α:=★ ⊢ V α ⊑ L : r[α]          p[α] : A[α] ⊑ B
         ------------------------------------------------- +⊑    p[α]⨾q ⊑ r[α]
         σ, α:=★ ⊢ (V α @ +p[α]) ⊑ L : q
         ------------------------------- ν⊑
         σ ⊢ να:=★.(V α @ +p[α]) ⊑ L : q

    (V @ —(να.p[α])) α  ⊢→  V @ -p[seal_α:=tag_α]

         σ ⊢ V ⊑ L : q
         ---------------------------------- -⊑    (να.p[α])⨾q ⊑ να.r[α]
         σ ⊢ V @ —(να.p[α]) ⊑ L : (να.r[α])
         ---------------------------------- α⊑    α:=A ∈ σ
         σ ⊢ (V @ —(να.p[α])) α ⊑ L : r[α]
       ⊢→
         σ ⊢ V ⊑ L : q
         ------------------------------------ -⊑    p[seal_α:=tag_α]⨾q ⊑ p[α]⨾q ⊑ r[α]
         σ ⊢ V @ -p[seal_α:=tag_α] ⊑ L : r[α]

         [Here is where we use tag_α ⊑ seal_α.]

    V @ +(p;tag_G) @ —(q;tag_G)  ⊢→  V @ +p @ —q

       There are two possible derivations.

         σ ⊢ V ⊑ M : (p;tag_G)
         ----------------------------- +⊑    (p;tag_G)⨾id_★ ⊑ p;tag_G
         σ ⊢ V @ +(p;tag_G) ⊑ M : id_★
         ----------------------------------------------- -⊑    (q;tag_G)⨾id_★ ⊑ q;tag_G
         σ ⊢ V @ +(p;tag_G) @ -(q;tag_G) ⊑ M : (q;tag_G)
       ⊢→
         σ ⊢ V ⊑ M : (p;tag_G)
         ----------------------------- +⊑    p⨾(id_G;tag_G) ⊑ p;tag_G
         σ ⊢ V @ +p ⊑ M : (id_G;tag_G)
         ------------------------------- -⊑    q⨾(id_G;tag_G) ⊑ q;tag_G
         σ ⊢ V @ +p @ -q ⊑ M : (q;tag_G)

         [TODO: Appears to implicitly use inversion.]

         σ ⊢ V ⊑ M : seal_α
         ------------------------- +⊑    tag_α⨾id_★ ⊑ seal_α
         σ ⊢ V @ +tag_α ⊑ M : id_★
         ------------------------------------ -⊑    tag_α⨾id_★ ⊑ seal_α
         σ ⊢ V @ +tag_α @ -tag_α ⊑ M : seal_α
       ⊢→
         σ ⊢ V ⊑ M : seal_α
         ----------------------------- +⊑    id_α⨾seal_α ⊑ seal_α
         σ ⊢ V @ +id_α ⊑ M : seal_α
         ---------------------------------- -⊑    id_α⨾seal_α ⊑ seal_α
         σ ⊢ V @ +id_α @ -id_α ⊑ M : seal_α

    V @ +(p;tag_G) @ —(q;tag_H)  ⊢→  blame

         σ ⊢ V ⊑ M : (p;tag_G)
         ----------------------------- +⊑    (p;tag_G)⨾id_★ ⊑ p;tag_G
         σ ⊢ V @ +(p;tag_G) ⊑ M : id_★
         ----------------------------------------------- -⊑    (q;tag_H)⨾id_★ ⊑ q;tag_H
         σ ⊢ V @ +(p;tag_G) @ -(q;tag_H) ⊑ M : (q;tag_H)
       —→
         σ ⊢ blame ⊑ M : (q;tag_H)

    V @ -(seal_α;p) @ +(seal_α;q)  ⊢→  V @ -p @ +q
                         
         σ ⊢ V ⊑ M : s
         ------------------------------------ -⊑    (seal_α;p)⨾s ⊑ seal_α;t
         σ ⊢ V @ -(seal_α;p) ⊑ M : (seal_α;t)
         --------------------------------------- +⊑    (seal_α;q)⨾r ⊑ seal_α;t
         σ ⊢ V @ -seal_α(p) @ +seal_α(q) ⊑ M : r
       —→
         σ ⊢ V ⊑ M : s
         ------------------ -⊑    p⨾s ⊑ t
         σ ⊢ V @ -p ⊑ M : t
         ----------------------- +⊑    q⨾r ⊑ t
         σ ⊢ V @ -p @ +q ⊑ M : r

------------------------------------------------------------------------
RELATED WORK
------------------------------------------------------------------------

* Ahmed, Jamner, Siek, and Wadler (POPL 2017)
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

* New, Jamner & Ahmed (POPL 2019)
  Graduality and Parametricity: Together Again for the First Time.
  source of our title
  odd syntax with user-written seals: "throws the baby out with the bathwater"
  doesn't support using casts to instantiate and generalise
  replaces compatibility by imprecision
  has ∀X.★ as a ground type

* Toro, Labrada & Tanter (POPL 2019), Labrada, Toro & Tanter (JACM 2022)
  Gradual System F.
  introduces "strict" imprecision, but mixes it with ordinary imprecision.
  doesn't support using casts to instantiate and generalise
  uses compatibility
  has ∀X.★ as a ground type

* Devriese, Patrigani & Piessens (POPL 2017, TOPLAS 2022)
  Two Parametricities Versus Three Universal Types.
  Consider the type,
    ∃X.∀Y.(Y→X, X→Y)
  which makes X a Universal Type.

  Observe that System F lacks a universal type but that Ahmed, Jamner,
  Siek & Wadler (POPL 2017) permit a universal type, and hence full
  abstraction cannot hold when mapping System F to λB.  Make similar
  observations for mapping System F into cryptographic lambda calculus
  of Peirce and Sumii, or into System G of Neiss, Dreyer, and Rossberg
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




APPENDIX: EXTRA MATERIAL
~~~~~~~~~~~~~~~~~~~~~~~~

The following appear not to be needed---the simulation proof does not
reference them, even though similar results appear in Siek et al
(2015).


## Left inversion

### Left upcast inversion

If σ ⊢ V @ +s ⊑ M : r then σ ⊢ V ⊑ M : p where r ⊑ p ⨾ t

Proof by induction on the derivation of σ ⊢ V @ +s ⊑ M : r.

  (+⊑)
      σ ⊢ V ⊑ M′ : r
      ------------------- +⊑    s ⨾ q ⊑ r
      σ ⊢ V @ +s ⊑ M′ : q

      (trivial)

  (⊑+)

      σ ⊢ V ⊑ M′ : p
      -------------------- +⊑        s ⨾ r′ ⊑ p
      σ ⊢ V @ +s ⊑ M′ : r′
      ------------------------ ⊑+    q ⊑ r′ ⨾ t
      σ ⊢ V @ +s ⊑ M′ @ +t : q
    =>
      σ ⊢ V ⊑ M′ : p    
      ------------------- ⊑+         r ⊑ p ⨾ t
      σ ⊢ V ⊑ M′ @ +t : r
      ------------------------ +⊑    s ⨾ q ⊑ r
      σ ⊢ V @ +s ⊑ M′ @ +t : q

   First implies second because

      s ⨾ q ⊑ s ⨾ r′ ⨾ t ⊑ p ⨾ t

      (can take r = s ⨾ q or r = p ⨾ t)

  (⊑-)
      σ ⊢ V ⊑ M′ : p
      -------------------- +⊑        s ⨾ r′ ⊑ p
      σ ⊢ V @ +s ⊑ M′ : r′
      ------------------------ ⊑-    r′ ⊑ q ⨾ t
      σ ⊢ V @ +s ⊑ M′ @ -t : q
    =>
      σ ⊢ V ⊑ M′ : p    
      ------------------- ⊑-         p ⊑ r ⨾ t
      σ ⊢ V ⊑ M′ @ -t : r
      ------------------------ +⊑    s ⨾ q ⊑ r
      σ ⊢ V @ +s ⊑ M′ @ -t : q

    Cannot be shown in general, because p has
    a lower bound in the hypothesis and an
    upper bound in the conclusion. (Does follow
    if the inequalities are equalities.)

   


## Right Inversion

### Right Downcast Inversion

If σ ⊢ V ⊑ V′ @ -t : p then σ ⊢ V ⊑ V′ : r where r ⊑ p ⨾ t.

Proof by induction on the derivation of σ ⊢ V ⊑ V′ @ -t : p.

  (⊑-)
      σ ⊢ V ⊑ V′ : r    σ ⊢ t
      ----------------------- ⊑- (r ⊑ p ⨾ t)
      σ ⊢ V ⊑ V′ @ —t : p

      Immediate.

  (+⊑)
      σ ⊢ V ⊑ V′ : p
      ------------------------ ⊑- (p ⊑ q ⨾ t)  (induction)
      σ ⊢ V ⊑ V′ @ -t : q
      ------------------------ +⊑ (s ⨾ r ⊑ q)
      σ ⊢ V @ +s ⊑ V′ @ -t : r
    =>
      σ ⊢ V ⊑ V′ : p
      ------------------------ +⊑ (s ⨾ q′ ⊑ p)
      σ ⊢ V @ +s ⊑ V′ : q′
      ------------------------ ⊑- (q′ ⊑ r ⨾ t)
      σ ⊢ V @ +s ⊑ V′ @ -t : r

      If the inequations were equations this would follow trivially by
      setting q′ = r ⨾ t. But because we have inequations there is no
      way to guarantee this works. We can see this trivially because
      the hypothesis sets an upper bound on p but the conclusion
      requires a lower bound on p.




      Let's try a specific example.

                       tag_α→tag_α
                            ∅
                  α→α ————————————→ *→*
                   ↑                 ↑
                   |                 |
         id_α→id_α |        ⊑        | seal_α→seal_α
             ∅     |                 |      α:=⋆
                   |                 |
                  α→α ————————————→ α→α
                        id_α→id_α


         ⊢ idα ⊑ id⋆ : tag_α→tag_α
         ------------------------------------------
         ⊢ idα ⊑ id⋆ @ -(seal_α→seal_α) : id_α→id_α


  (-⊑)
      σ ⊢ V ⊑ V′ : p
      ------------------- ⊑- (p ⊑ q ⨾ t) (induction)
      σ ⊢ V ⊑ V′ @ -t : q
      ------------------------ -⊑ (s ⨾ q ⊑ r)
      σ ⊢ V @ -s ⊑ V′ @ -t : r
    =>
      σ ⊢ V ⊑ V′ : p
      -------------------- -⊑ (s ⨾ p ⊑ q′)
      σ ⊢ V @ -s ⊑ V′ : q′
      ------------------------ ⊑- (q′ ⊑ r ⨾ t)
      σ ⊢ V @ -s ⊑ V′ @ -t : r

  (Λ⊑)
      σ, α:=★ ⊢ V[α] ⊑ V′ : (p[α] ⨾ q)
      -------------------------------- ⊑- (induction)
      σ, α:=★ ⊢ V[α] ⊑ V′ @ -q : p[α]
      ------------------------------- Λ⊑
      σ ⊢ ΛX.V[X] ⊑ V′ @ -q : να.p[α]
    =>
      σ, α:=★ ⊢ V[α] ⊑ V′ : (p[α] ⨾ q)
      ------------------------------------- Λ⊑
      σ ⊢ ΛX.V[X] ⊑ V′ @ -q : να.(p[α] ⨾ q)
      ------------------------------------- ⊑-
      σ ⊢ ΛX.V[X] ⊑ V′ @ -q : να.p[α]


### Right Upcast Inversion

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


Simulation of type application (ν)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If σ : Σ ⊑ Σ′ and σ ⊢ (ΛX.V[X]) ⊑ V′ : να.q[α]
then Σ′ ⊢ V′ α —↠ Π′ ⊢ N′ and π : Σ ⊑ Π′ and π ⊢ V[α] ⊑ N′: q′ for some q′.

Proof by induction on the derivation of σ ⊢ (ΛX.V[X]) ⊑ V′ : να.q[α].




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

in the proof of the Gradual Guarantee below.


Upcast Lemma
~~~~~~~~~~~~

If σ : Σ ⊑ Σ′ and σ ⊢ V ⊑ V′ : p
then Σ′ ⊢ V′ @ +q —↠ Π′ ⊢ W′ and π : Σ ⊑ Π′ and π ⊢ V ⊑ W′ : (p⨾q).

Proof by induction on q.

    V′ @ +id_a        ⊢→  V′
    V′ @ +(s→t)       is a value
    V′ @ +(∀X.s[X])   is a value
    V′ @ +(να.s[α])   ⊢→  να:=★.(V′ α @ +s[α])
      then apply reduction, catchup lemma, and induction.
      (This implies upcast, downcast, and catchup lemmas are proved
      by mutual induction.)
    V′ @ +(g;tag_G)   is a value
    V′ @ +(seal_α;t)
      then by canonical forms V′ = V″ @ -seal_α(s)
      and V″ @ -(seal_α;s) @ +(seal_α;t) —↠ V″ @ -s @ +t
      and apply induction twice (mutual induction with downcast lemma)


Downcast Lemma
~~~~~~~~~~~~~~

If σ : Σ ⊑ Σ′ and σ ⊢ V ⊑ V′ : (p⨾q)
then Σ′ ⊢ V′ @ +q —↠ Π′ ⊢ W′ and π : Σ ⊑ Π′ and π ⊢ V ⊑ W′ : p.

Proof by induction on q.

    V′ @ -id_a        ⊢↠  V′
    V′ @ -(s→t)       is a value
    V′ @ -(∀X.p[X])   is a value
    V′ @ -(να.p[α])   is a value
    V′ @ -(q;tag_G)
      then by canonical forms V′ = V″ @ +(p;tag_G)
      (it must be G and not H because σ ⊢ V ⊑ V″ : s for some s by Inversion Lemmas)
      and V″ @ +(p;tag_G) @ -(q;tag_G) ⊢↠ V″ @ +p @ -q
      and apply induction twice (mutual induction with downcast lemma)
    V′ @ -(seal_α;q)  is a value


Catchup Lemma
~~~~~~~~~~~~~

If σ : Σ ⊑ Σ′ and σ ⊢ V ⊑ M′ : p
then Σ′ ⊢ M′ —↠ Π′ ⊢ W′ and π : Σ ⊑ Π′ and π ⊢ V ⊑ W′ : p.

If M′ = V′ then the result is trivial.  If M′ ≠ V′ then the only
possibility for M is that it is an upcast or downcast, and hence
result follows from upcast and downcast lemmas, or one of the
following. 

    (Λ⊑)
      γ ⊢ Γ ⊑ Γ′    Γ, X ⊢ V[X] : B[X]    γ, α:=★ ⊢ V[α] ⊑ N : q[α]
      -------------------------------------------------------------
      γ ⊢ ΛX.V[X] ⊑ N : να.q[α]

    (⊑ν)
      γ, α:=☆ ⊢ N ⊑ N′[α] : q
      --------------------------- α ∉ fv(q)
      γ ⊢ N ⊑ να:=★.N′[α] : q

Induct over the derivation σ ⊢ V ⊑ M′ : p.  The first case follows by
induction. The second follows by applying the reduction Σ′ ⊢
να:=⋆.N′[α] —→ Σ′, α:=⋆ ⊢ N′[α] and then using induction.


