# Strong System F — v5: LOCALLY NAMELESS TYPE VARIABLES

STATUS: design draft, 2026-09-11.  Nothing mechanized.  WRITTEN TO BE
EVALUATED, not adopted — Jeremy is sceptical of locally nameless and
suspects most of the benefit is reachable in de Bruijn with anchors used
in fewer places; [C9] states that hypothesis against this draft.

v5 is v4's [O6] taken seriously.  Read v4 first: v5 changes only HOW a
variable is identified.  The layering [v4 C7], the conceal spine
[v4 C15], the representation discipline and the boundary forms are all
inherited unchanged.

Part I is the calculus; Part II the commentary [C1]…[C9]; Part III open.


                        =====================
                        PART I — THE CALCULUS
                        =====================

# The single change                                                  [C1]

A type variable is identified by its NAME, never by its position.

  FREE type variables are NAMES.  They are the anchors: permanent, and
  carrying representations.
  ∀-BOUND type variables are DE BRUIJN indices.

Term variables stay de Bruijn throughout, as v3 and v4.

# Types

  v ::= ⌜n⌝ | X                      bound index | free name
  A,B,C ::= v | ℕ | 𝔹 | A → B | ∀A

  A^B     OPEN: replace the outermost bound index of A by B          [C2]

Locally closed: no dangling ⌜n⌝.  `B[A]ᵗ` of v3/v4 IS `B^A`.

# Contexts                                                           [C3]

  Σ ::= ∅ | Σ, X | Σ, X:=R           PERMANENT, append-only, X distinct
                                     `Σ, X` abstract (Λ-bound, no rep)
                                     `Σ, X:=R` carries representation R
  Δ ⊆ dom Σ                          the names IN SCOPE — a finite SET

  Σ;Δ ⊢ A    every free name of A is in Δ, and A is locally closed

A REPRESENTATION IS JUST A TYPE.  `R` is stored with `FV(R) ⊆ dom Σ`; it
is READ only where `FV(R) ⊆ Δ`.  v4's two sublanguages, `⌊·⌋` and `⌈·⌉`
all disappear into that one condition.                               [C4]

# Conversions

  c,d   ::= id | c → d | ∀c | +v | -v
  cⁱ,dⁱ ::= c → d | ∀c | -v          (inert)
  cᵃ,dᵃ ::= id | +v                  (active)

  X ∈ Δ   Σ ∋ X:=R   FV(R) ⊆ Δ       X ∈ Δ   Σ ∋ X:=R   FV(R) ⊆ Δ
  ----------------------------       ----------------------------
  Σ;Δ ⊢ +X : X ⇒ R          [C4]     Σ;Δ ⊢ -X : R ⇒ X

  ------------------  ------------------
  Σ;Δ ⊢ id : ι ⇒ ι    Σ;Δ ⊢ id : X ⇒ X

  Σ;Δ ⊢ c : C ⇒ A   Σ;Δ ⊢ d : B ⇒ D      Σ,Y ; Δ∪{Y} ⊢ c^Y : A^Y ⇒ B^Y
  --------------------------------       ------------------------------ Y ∉ Σ
  Σ;Δ ⊢ c → d : (A → B) ⇒ (C → D)        Σ;Δ ⊢ ∀c : ∀A ⇒ ∀B

THE MINT, with NO INDEX ARITHMETIC:                                  [C5]

  +X(X) = +X        -X(X) = -X
  +X(v) = id        -X(v) = id       (v ≠ X, INCLUDING every ⌜n⌝)
  +X(ι) = id        -X(ι) = id
  +X(A → B) = -X(A) → +X(B)          -X(A → B) = +X(A) → -X(B)
  +X(∀A)    = ∀ (+X(A))              -X(∀A)    = ∀ (-X(A))

Compare v3's `revTy (suc X) A` under a ∀.  A name is not shifted by a
binder it does not belong to.

# Runtime Terms

  b ::= new X:=R | +v | -v
  L,M,N ::= ... | ν b [ M ] | M⟨c⟩

  ν new X:=R [ M ]   INTRO.  Allocates X with representation R and brings
                     it into scope.  The only form that extends Σ.
  ν +X [ M ]         REVEAL.  X is in scope inside, not outside.
  ν -X [ M ]         CONCEAL.  X is in scope outside, not inside.

  TAGS RANGE OVER `v`, NOT JUST NAMES — a tag under an UNOPENED Λ names
  that Λ's bound index.  Opening reaches into tags.                  [C6]

  DERIVED FORM — THE CONCEAL SPINE (as v4 [C15]):

    δ ::= ∅ | -v , δ      ⁻∅[M] = M      ⁻(-v,δ)[M] = ν -v [ ⁻ᵟ[M] ]

  -----------
  | -b = b′ |
  -----------

  -(new X:=R) = -X       -(+v) = -v       -(-v) = +v

# Term Typing                                                        [C3]

  Σ ⊢ R   X ∉ dom Σ                      X ∈ dom Σ   X ∉ Δ
  Σ,X:=R ; Δ∪{X} ⊢ M : C                 Σ ; Δ∪{X} ⊢ M : C
  X ∉ FV(C)                              X ∉ FV(C)
  -------------------------- (intro)     -------------------- (reveal)
  Σ;Δ ⊢ ν new X:=R [ M ] : C             Σ;Δ ⊢ ν +X [ M ] : C

  X ∈ Δ                                  Σ;Δ ⊢ M : A   Σ;Δ ⊢ c : A ↝ B
  Σ ; Δ∖{X} ⊢ M : C                      ------------------------------
  -------------------- (conceal)         Σ;Δ ⊢ M⟨c⟩ : B          (conv)
  Σ;Δ ⊢ ν -X [ M ] : C

  Σ,Y ; Δ∪{Y} | ⤊Γ ⊢ N^Y : C^Y     Y ∉ Σ
  --------------------------------------- (Λ)
  Σ;Δ | Γ ⊢ Λ N : ∀C

v3's ⊢reveal/⊢conceal REPAIR (`Δ ∋lks χ` / `Δ ∋tvs χ`, 2026-09-11) is here
`X ∉ Δ` and `X ∈ Δ`.  Its two round-trip lemmas — v3's `lock-unlock` and
`unlock-lock`, built on the whole `updateAt` algebra — become

  (Δ∖{X}) ∪ {X} = Δ   given X ∈ Δ        (Δ∪{X}) ∖ {X} = Δ   given X ∉ Δ

# Values                                                    [v4 C7] [v4 C8]

  Vˢ,Wˢ ::= λx:A. N | Λ V
  V⁻,W⁻ ::= ⁻ᵟ[Vˢ]
  Vᶜ,Wᶜ ::= V⁻ | Vᶜ⟨cⁱ⟩
  V⁺,W⁺ ::= Vᶜ | ᵖ[ V⁺ ]                (ᵖ ::= new X:=R | +v)
  V,W   ::= k | V⁺

Unchanged from v4.  Valuehood is purely syntactic, so `Λ V` reads its
body unopened.

# Substitution

  crossΛ W  =  ν -⌜0⌝ [ W ]        NO SHIFT, unconditionally    [C6] [C7]

# Reduction Rules

  (Beta)       Δ ⊢ (λx:A. N) · W   -→ N[x:=W : A]
  (AppConv)    Δ ⊢ V⟨c → d⟩ · W    -→ (V (W⟨c⟩))⟨d⟩
  (AppBnd)     Δ ⊢ ᵇ[V⁺] · W       -→ ᵇ[V⁺ ⁻ᵇ[W]]   if ᵇ[V⁺] is a value
  (Cancel)     Δ ⊢ V⟨-X⟩⟨+X⟩      -→ V
  (DropId)     Δ ⊢ V⟨id⟩          -→ V
  (DropConst)  Δ ⊢ ᵇ[k]           -→ k
  (PrimBeta)   Δ ⊢ n₁ ⊕ n₂        -→ n₁ ⟦⊕⟧ n₂

  (TyBeta)     Δ ⊢ ⁻ᵟ[Λ V] •B[A]  -→ ν new Y:=A [ (⁻ᵟ[V^Y])⟨+Y(B^Y)⟩ ]
                                      Y ∉ Σ; δ possibly EMPTY; subsumes
                                      v3's TyConceal                 [C8]

  (TyConv)     Δ ⊢ V⟨∀c⟩ •B[A]    -→ (V A)⟨c^A⟩

  (TyPos)      Δ ⊢ ᵖ[V⁺] •B[A]    -→ ᵖ[ ν new Y:=A [ (ν -Y [V⁺]) •B[Y]
                                                      ⟨+Y(B^Y)⟩ ] ]

  (PushConv)   Δ ⊢ ν -X [Vᶜ⟨cⁱ⟩]  -→ (ν -X [Vᶜ])⟨cⁱ⟩
  (PushPos)    Δ ⊢ ν -X [ᵖ[V⁺]]   -→ ᵖ[ν -X [V⁺]]      if X ∉ names(ᵖ)
  (CancelBnd)  Δ ⊢ ν -X [ν +X [M]] -→ M
               Δ ⊢ ν +X [ν -X [M]] -→ M

  (ξ-Λ)        Σ,Y ; Δ∪{Y} ⊢ N^Y -→ N′    Y ∉ Σ
               -------------------------------------
               Σ;Δ ⊢ Λ N -→ Λ (close Y N′)                           [C6]

  (ξ)          otherwise as v3.

EVERY PRIMED METAVARIABLE OF v4 IS GONE: PushPos has no ᵖ′/X′, PushConv no
cⁱ′, TyBeta no δ′, crossΛ no shift.  That is the whole point.        [C7]


                        ======================
                        PART II — COMMENTARY
                        ======================

[C1] THE TRICHOTOMY.  There are three ways to handle a variable leaving
     scope, and v5 is the third corner:
       v3  positional + MARK    the slot stays, masked.  No renumbering,
                                at the cost of masks, ∋lks/∋tvs, and the
                                VarSet machinery.
       v4  positional + DELETE  the slot goes.  No masks, at the cost of
                                four renumbering sites [v4 O4].
       v5  NOMINAL              there are no positions, so neither cost
                                arises — at the cost of naming machinery.
     v4 pays renumbering to buy a property (slots that genuinely leave
     scope) that naming gives away, and buys back a second type
     sublanguage and a partial read-back to compensate for something that
     was never a problem nominally.

[C2] WHY LOCALLY NAMELESS AND NOT FULLY NOMINAL.  Fully nominal types
     would need α-equivalence and capture-avoiding substitution.  Locally
     nameless needs neither: ∀-binding stays de Bruijn, so ∀A is a closed
     form, and NO RULE EVER SUBSTITUTES FOR A FREE NAME — `B[A]ᵗ` is
     ∀-opening, and revealing is a CONVERSION, not a substitution.  What
     is actually needed is opening, a freshness condition, and local
     closure.  That is the whole of the machinery.

[C3] TWO CONTEXTS OVER ONE FAMILY.  v4's "anchor α" and "scoped variable
     X@α" collapse: a scoped variable IS its anchor.  What remains is two
     CONTEXTS — Σ permanent and carrying representations, Δ the subset
     currently in scope.  Jeremy's constraint ("anchors should appear only
     in reveal/conceal") is not so much satisfied as dissolved: there is
     no second sort to confine.

[C4] TIGHTNESS IS ONE SIDE CONDITION.  v4 needed representations to be
     ANCHOR-CLOSED, a second type sublanguage, `⌊·⌋` total, and `⌈·⌉`
     partial — all so that a representation could outlive the scope of
     what it mentions.  Nominally a representation is just a type; it is
     STORED with `FV(R) ⊆ dom Σ` and READ with `FV(R) ⊆ Δ`.  v4's [C3]
     forced case evaporates: an intro planted inside a conceal writes the
     same R either way, because names do not care where they are written.
     v3's regularity gap (`conv-unseal` with no well-formedness premise on
     the rep it returns) is still closed, by `FV(R) ⊆ Δ`.

[C5] THE MINT LOSES ITS ARITHMETIC.  v3 is `revTy (suc X) A` under a ∀ —
     the name is shifted because it is an index.  A name is not shifted by
     a binder it does not belong to, so v5's clause is `+X(∀A) = ∀(+X(A))`
     and every bound index falls in the `v ≠ X` case.  This also removes
     `instConvσ`/`_[_]ᶜ`'s variable action (v3 Reduction §0).

[C6] THE ONE PLACE LOCALLY NAMELESS COSTS SOMETHING.  `crossΛ` conceals
     the Λ's OWN type variable from a substituted image — and at
     substitution time that variable is still a BOUND INDEX, not a name.
     So tags must range over `v`, not just names, and opening must reach
     into them.  This is standard locally-nameless practice, but it means:
       * a tag may transiently name `⌜0⌝`, under an unopened Λ;
       * ξ-Λ must OPEN and then CLOSE (`close Y N′`), where v3's ξ-Λ just
         pushes a binder on the context;
       * `Cancel` and `CancelBnd` match on `v`, so a bound-index pair can
         cancel under an unopened Λ.
     THIS IS THE THING TO WEIGH.  It is the only new machinery v5 adds,
     and it is exactly the part Jeremy is sceptical of.

[C7] WHAT GOES AWAY.  All four of v4's renumbering sites [v4 O4] —
     PushPos's X′/ᵖ′, PushConv's cⁱ′, TyBeta's δ′, crossΛ's shift.  Also
     v4's [O1] and [O2] (two scoped variables at one anchor is not
     expressible when Δ is a set) and [O3] (nothing renumbers).
       AND COLOUR PRESERVATION BECOMES LITERAL.  v3's annotation is a set
     of INDICES, transported by `renᴹ`, needing `scopeᵇ`, `mergeᵒ`,
     `insertᵒ`, and a proof at every shifting rule — and the TyPos defect
     of 2026-09-11 was exactly a positional disagreement between a
     renaming and its partner conceal.  A v5 annotation is a set of NAMES
     and reduction never renames a name, so "invariant under reduction" is
     invariance, with no transport at all.  That whole class of defect
     stops existing.

[C8] WHAT DOES NOT CHANGE.  The layering and PushConv/PushPos [v4 C7], the
     conceal spine and its canonical-forms lemma [v4 C15], the
     representation-not-term-type discipline [v4 C5], the TyBeta/TyConceal
     unification [v4 C8], and the whole Progress-gap argument.  v5 is a
     change of IDENTITY, not of structure.

[C9] JEREMY'S HYPOTHESIS, AGAINST THIS DRAFT.  "Most of these benefits
     while staying with de Bruijn, reducing the places anchors can be
     used."  The honest test is which of [C7]'s four renumbering sites a
     de Bruijn variant can kill, and the four are not alike:
       crossΛ, PushConv, TyBeta's δ′  arise because a CONCEAL DELETES a
            slot and everything above it moves.  A de Bruijn variant kills
            these only by not deleting — i.e. by marking, which is v3.
       PushPos's X′/ᵖ′               arises because two slot-changing tags
            swap.  Same source.
     So the hypothesis is really: is there a de Bruijn representation in
     which a slot can LEAVE SCOPE without the slots above it moving?  v3's
     answer is the mask.  If there is a third answer, it is worth more
     than either draft — and it is the question I would put first.


                        ================
                        PART III — OPEN
                        ================

[O1] The name supply.  ξ-Λ, ⊢Λ, TyBeta and TyPos all need a fresh name.
     Cofinite quantification (`∀ Y ∉ L`) is the standard Agda idiom and
     avoids threading a counter; whether the reduction RELATION can use it
     as comfortably as the typing judgment needs checking.

[O2] `close` in ξ-Λ.  v3's ξ-Λ pushes a binder on the context and is done.
     v5's opens, steps, and closes.  Whether `close Y (·)` is well behaved
     on the boundary tags of [C6] — in particular whether closing can
     capture a tag that names a DIFFERENT free variable — needs checking.
     This is the sharpest technical risk in the draft.

[O3] Determinism, over `v`-ranging tags.  Cancel/CancelBnd match on `v`,
     so a bound-index pair may cancel under an unopened Λ while the same
     pair, opened, cancels as names.  Confluence of those two paths is not
     obvious and is not argued here.

[O4] Colour preservation, properly stated.  [C7] claims the annotation
     becomes a set of names with no transport.  That should be written out
     and checked against AppBnd, which in v3 must REBUILD its application
     node's annotation (`scopeᵇ b κ`) — nominally that becomes `Δ` for the
     interior, which is not the node's old set either.  So AppBnd may
     still rebuild; the claim in [C7] is about TRANSPORT, not about
     rebuilding.
