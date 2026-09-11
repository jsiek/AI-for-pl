# Strong System F — v6: FUSED BOUNDARIES, PREFIX INTERIORS

STATUS: design draft, 2026-09-11.  Nothing mechanized.  Supersedes the
earlier v6 sketch: representations live on Θ, contexts are BARE, and
ANCHORS ARE GONE — see [C6] for the retraction.

v6 combines two of Jeremy's ideas, which turn out to be one [C2]:

  FUSED BOUNDARY         one node carries the scope change AND the
                         conversion, so the interior is TRUNCATE-then-
                         APPEND and the prefix design works         [C1]
  TWO-CONTEXT CONVERSION is what fusion IS, formally                [C2]


                        =====================
                        PART I — THE CALCULUS
                        =====================

# Criteria, source terms, types

As v3, unchanged.

  A,B,C ::= X | ℕ | 𝔹 | A → B | ∀X.A

# Contexts                                                           [C3]

  Γ ::= ∅ | Γ, X              a list of DISTINCT variables.  NO
                              representations, no marks, no locks.
  Γ ↓ X                       the part of Γ strictly BEFORE X
  Γ ⊢ A                       every free variable of A is in Γ

ALL KNOWLEDGE LIVES ON Θ.  A context says only what is in scope.

# Boundary morphisms

  θ ::= ↑X:=A | ↑X:⋆ | ↓Y:=B | ↓Y:⋆
  Θ ::= ∅ | θ, Θ              AT MOST ONE conceal, and it comes FIRST
                              (v1's "one restriction at the deepest
                              conceal")                             [C5]

  L,M,N ::= ... | M ⟪ Θ , c ⟫

  ------------------------------
  | Γ ⇈ Θ = Γ′   the INTERIOR  |
  ------------------------------

  Γ ⇈ ∅        = Γ
  Γ ⇈ (↓Y, Θ)  = (Γ ↓ Y) ⇈ Θ
  Γ ⇈ (↑X, Θ)  = (Γ , X) ⇈ Θ

  ------------------------------------
  | Γ ⊢ Θ ⊣ Γ′   WELL-FORMED MORPHISM |
  ------------------------------------

                        Γ ⊢ Θ ⊣ Γ′    Y ∈ Γ    Γ′ ⊢ B
  ------------------    -------------------------------
  Γ ⊢ ∅ ⊣ Γ             Γ ⊢ (↓Y:=B), Θ ⊣ Γ′

  Γ ⊢ Θ ⊣ Γ′    Y ∈ Γ               Γ ⊢ Θ ⊣ Γ′    X ∉ Γ    Γ ⊢ A
  -----------------------           --------------------------------
  Γ ⊢ (↓Y:⋆), Θ ⊣ Γ′                Γ ⊢ (↑X:=A), Θ ⊣ Γ′

  Γ ⊢ Θ ⊣ Γ′    X ∉ Γ
  -----------------------
  Γ ⊢ (↑X:⋆), Θ ⊣ Γ′

THE REPRESENTATION CONDITIONS ARE CHECKED AT THE TWO ENDPOINTS, NOT AT
INTERMEDIATE STAGES — simultaneity, in v1's sense:                   [C4]

    A REVEAL's representation is a type over the EXTERIOR.
    A CONCEAL's representation is a type over the INTERIOR.

# The dual                                                       [C7] [C8]

  ------------------
  | Θᵈ_Γ  the DUAL |
  ------------------

  (↑X:=A)ᵈ = ↓X:=A            (↓Y:=B)ᵈ = ↑Y:=B
  (↑X:⋆)ᵈ  = ↓X:⋆             (↓Y:⋆)ᵈ  = ↑Y:⋆

  (θ₁,…,θₙ)ᵈ = θₙᵈ, …, θ₁ᵈ

  Θᵈ_Γ = (Θ)ᵈ ++ [ ↑W:⋆ | W ∈ Γ₁, in Γ's order ]
         where Γ = Γ₀ , Y , Γ₁  and Y is Θ's truncation point
         (Γ₁ = ∅, and the second component empty, if Θ does not truncate)

REPRESENTATIONS ARE CARRIED ACROSS VERBATIM — no re-scoping, no reading,
no fallback.  Dualising swaps exterior and interior, and the endpoint
convention above swaps with it.                                      [C7]

  Γ ⇈ Θ ⇈ Θᵈ_Γ = Γ            EXACTLY, in order                      [C8]

# Conversions

  c,d ::= id | c ↦ d | ∀X.c | +X | -X

  Γₛ ; Γₜ ; Θ ⊢ c : A ⇒ B          A over Γₛ,  B over Γₜ

`+` always goes NAME → REPRESENTATION; `-` always REPRESENTATION → NAME.
A reveal's name lives inside and its representation outside; a conceal's
name lives outside and its representation inside.  The four leaf rules are
that sentence:

  (↑X:=A) ∈ Θ                        (↑X:=A) ∈ Θ
  ---------------------------------  ---------------------------------
  Γ⇈Θ ; Γ ; Θ ⊢ +X : X ⇒ A           Γ ; Γ⇈Θ ; Θ ⊢ -X : A ⇒ X

  (↓Y:=B) ∈ Θ                        (↓Y:=B) ∈ Θ
  ---------------------------------  ---------------------------------
  Γ⇈Θ ; Γ ; Θ ⊢ -Y : B ⇒ Y           Γ ; Γ⇈Θ ; Θ ⊢ +Y : Y ⇒ B

  Γₛ ⊢ A    Γₜ ⊢ A                   Γₜ ; Γₛ ; Θ ⊢ c : C ⇒ A
  ------------------------           Γₛ ; Γₜ ; Θ ⊢ d : B ⇒ D
  Γₛ ; Γₜ ; Θ ⊢ id : A ⇒ A           ----------------------------------
                                     Γₛ ; Γₜ ; Θ ⊢ c ↦ d : (A→B)⇒(C→D)

  Γₛ,X ; Γₜ,X ; Θ ⊢ c : A ⇒ B
  ---------------------------------------
  Γₛ ; Γₜ ; Θ ⊢ ∀X.c : ∀X.A ⇒ ∀X.B

THE ARROW RULE SWAPS the two contexts; `∀` extends both.  `id` is
available exactly for a type that SURVIVES the crossing.        [C2] [C9]

# Term Typing

  Γ ⊢ Θ ⊣ Γ′    Γ′ ⊢ M : A    Γ′ ; Γ ; Θ ⊢ c : A ⇒ B    Γ ⊢ B
  -------------------------------------------------------------
  Γ ⊢ M ⟪ Θ , c ⟫ : B

NO `names(Θ) ∩ FV(B) = ∅` SIDE CONDITION: B is a type over Γ, and the
interior-only variables are simply not in Γ.

Source rules (`⊢λ`, `⊢·`, `⊢Λ`, `⊢•[]`, constants, `⊕`) as v3.

# Values                                                          [v4 C7]

  Vˢ,Wˢ ::= λx:A. N | ΛX.V
  V,W   ::= k | Vˢ | V ⟪ Θ , c ⟫                                     [O3]

# Substitution

  crossΛ W = W ⟪ ↓Z:⋆ , id ⟫        Z the Λ's own variable            [C10]

No shift: the interior is `(Γ,Z)↓Z = Γ`, exactly where W was typed.

# Reduction Rules

  (Beta, DropId, DropConst, PrimBeta, ξ)   as v3.

  (TyBeta)   Γ ⊢ ((Λ V) ⟪ Θ , c ⟫) • B [ A ]
               -→ V ⟪ Θ , (↑Y:=A) , c′ ⟫
             Y is the Λ's OWN variable — the binder's slot IS the reveal's
             slot.  A is a type over Γ, which is EXACTLY the reveal
             convention, so it is stored verbatim.  c′ = c ⨟ +Y(B). [O1]

  (AppBnd)   Γ ⊢ (V ⟪ Θ , c₁ ↦ c₂ ⟫) · W
               -→ (V · (W ⟪ Θᵈ_Γ , c₁ ⟫)) ⟪ Θ , c₂ ⟫

             THE CONVERSION SPLITS: the domain half c₁ rides the
             argument's crossing, the codomain half c₂ stays on the
             result.  And c₁'s contexts — `Γ ; Γ⇈Θ` by the arrow rule's
             swap — are EXACTLY the dual boundary's.                [C9]

  (Cancel)   a matched pair spanning two adjacent boundaries needs Θ
             COMPOSITION                                             [O2]


                        ======================
                        PART II — COMMENTARY
                        ======================

[C1] WHY FUSION RESCUES THE PREFIX DESIGN.  The obstruction (notes-v4
     [C16]) was that a freshly introduced Y ends up in scope while OLDER
     variables are concealed — a shape `Γ↓X` cannot denote.  It arose ONLY
     because the intro and the conceal were SEPARATE NODES that had to be
     ordered.  Fused, `Γ ⇈ (↓Y, ρ) = (Γ↓Y), ρ` truncates and THEN appends:
     the new entries land shallowest, so the truncation is a prefix by
     construction and there is no ordering question.

[C2] A TWO-CONTEXT CONVERSION IS A FUSED BOUNDARY.  `Γₛ ; Γₜ ⊢ c : A ⇒ B`
     says something only if the node CHANGES the context.  THE TEST that
     it is the right reading: contravariance becomes LITERAL CONTEXT
     SWAPPING.  In v3 that asymmetry in `conv-fun` is unexplained ("the
     only trace the retired polarity index leaves"); here it falls out.

[C3] CONTEXTS ARE BARE.  v3 carries `bind A` in the context; v1 carried
     `X:=⟦A⟧` in the interior and needed the READING.  v6 carries nothing:
     every representation sits on a Θ.  This is what makes [C7] a verbatim
     copy and [C6] a retraction.

[C4] SIMULTANEITY IS LOAD-BEARING.  Checking a conceal's representation at
     the INTERMEDIATE context fails — see [C8]'s worked dual, where
     `↓Y:=Z` would need Z at `Y↓Y = ∅`.  Checked at the ENDPOINT it holds.
     This is v1's Q2 ruling ("simultaneity KEEP") arriving for a reason
     v1 did not state.

[C5] AT MOST ONE CONCEAL.  A prefix truncation at the deepest concealed
     variable subsumes any shallower one, and two conceal entries would
     make the dual re-append the same block twice.  v1's "one restriction
     at the deepest conceal", now forced by the dual rather than chosen.

[C6] ANCHORS ARE RETRACTED.  Earlier drafts (notes-v4 [C3], notes-v6 v1)
     argued representations must be ANCHOR-CLOSED, on the grounds that a
     conceal REMOVES an entry and a later reveal must restore it, so the
     representation must live somewhere permanent.  THAT IS CONDITIONAL ON
     REPRESENTATIONS LIVING IN CONTEXTS.  They do not here: they live on
     Θ, the dual carries them verbatim [C7], and contexts are bare [C3].
     No anchor appears anywhere in Part I.
       What the anchor idea DID contribute is the diagnosis — that the
     rep-copy is the disease (2026-09-05, "every failure is a failed rep
     copy") — and v6 cures it a different way: not by making the rep
     context-independent, but by never moving it between contexts.

[C7] THE DUAL CARRIES REPRESENTATIONS VERBATIM, and the endpoint
     convention [C4] is why.  Dualising swaps exterior and interior; "a
     reveal's rep is over the exterior" therefore BECOMES "a conceal's rep
     is over the interior", which is exactly the other rule.  So
     `(↑X:=A)ᵈ = ↓X:=A` with A untouched, and `Θᵈᵈ = Θ` on the nose.
       That asymmetry looked arbitrary when it was written down.  It is
     the reason the dual is free.

[C8] THE ROUND TRIP IS EXACT — a correction to the earlier [O1], which
     predicted `Γ` only UP TO REORDERING (v2's ≼≈).  It is exact, in
     order, PROVIDED Θᵈ is taken relative to Γ: prefix truncation has
     COLLATERAL (`Γ↓Y` drops Y AND everything after), which Θ does not
     name, so the dual must re-append it.  Re-appended ABSTRACTLY, losing
     nothing, since contexts are bare [C3].  Worked: Γ = Z,W with
     Θ = ↓Z:⋆, ↑Y:=Z gives interior Y, Θᵈ = ↓Y:=Z, ↑Z:⋆, ↑W:⋆, and the
     round trip is ∅,Z,W = Γ.
       WHAT REMAINS OF THE COST: Θᵈ is a function of Θ AND Γ, not of Θ
     alone, and its size is O(|Γ₁|) where v3 restores in O(1).  A rule can
     just compute it.  The `≼≈` half of the risk is gone.

[C9] AppBnd SPLITS THE CONVERSION, and the split is forced.  With
     `c = c₁ ↦ c₂`, the arrow rule types c₁ at the SWAPPED contexts
     `Γ ; Γ⇈Θ` — which are precisely the dual boundary's own.  So c₁ is
     the argument's crossing conversion and c₂ the result's, with no
     re-typing.  (Minor: `id` at an arrow must expand to `id ↦ id`, as
     v3's `mkId` does.)

[C10] crossΛ LOSES ITS SHIFT AND ITS CONVERSION.  v3 has
     `ν conceal (0∷[]) [ ⇑ᴹ W ]`, shifted because the Λ's slot is
     present-but-masked.  Here the interior is `(Γ,Z)↓Z = Γ`, exactly
     where W was typed, so nothing shifts and the conversion is `id` —
     available by [C2]'s rule precisely because W's type survives.


                        ================
                        PART III — OPEN
                        ================

[O1] CONVERSION COMPOSITION `c ⨟ d`, needed by TyBeta.  Two conversions in
     sequence cross two boundaries; composing them into one requires the
     middle context to disappear.  NOT WORKED.

[O2] Θ COMPOSITION, needed by Cancel across adjacent boundaries.  This is
     the last place v2's `≼≈` might still live, now that [C8] has removed
     it from the dual.  NOT WORKED, and it is the headline risk.

[O3] VALUES AND PROGRESS.  With one boundary form there is nothing to
     order, so v3/v4's layering and its administrative rules may all go —
     but the layering was carrying the termination argument for the
     boundary-elimination family (v4 [C7]).  What replaces it is not
     sketched.

[O4] COLOUR PRESERVATION.  The annotation is "the scoped context", and a
     fused boundary changes it in one step.  [C8] means the dual no longer
     reorders, which removes the worry that an index-list annotation could
     not survive the round trip.

[O5] THE COMPARISON THAT MATTERS.  v3 buys a cheap interior (masks) with
     no morphism algebra.  v6 buys a cheap interior (prefix) and pays one
     — but the algebra is now smaller than v2's: the dual is free [C7] and
     exact [C8], leaving only [O2].  Re-reading v2's Boundary.agda for
     what composition actually cost is the next measurement.
