# Strong System F — v6: FUSED BOUNDARIES, PREFIX INTERIORS, ANCHORED ENTRIES

STATUS: design draft, 2026-09-11.  Nothing mechanized.  More tentative
than v4 or v5 — the two places v2 actually bled (THE DUAL and BOUNDARY
COMPOSITION) are worked below rather than waved at, and both come out
costly.  Read [O1] and [O2] before believing the rest.

v6 combines three of Jeremy's ideas, each of which covers a DIFFERENT one
of the three historical failures:

  FUSED BOUNDARY        makes the interior "truncate then append", so the
                        prefix design works                          [C1]
  TWO-CONTEXT CONVERSION  is what fusion IS, formally                 [C2]
  ANCHORED ENTRIES      remove the rep copy that killed v1's fused+prefix
                        design                                       [C3]

That they line up this well is either a good sign or a reason to be
suspicious; [C7] says which parts I would actually bet on.


                        =====================
                        PART I — THE CALCULUS
                        =====================

# Anchors and contexts

  Σ ::= ∅ | Σ, α | Σ, α:=R      PERMANENT, append-only.  R anchor-closed.
  Γ ::= ∅ | Γ, X@α              scoped variables; NEWEST on the right

  Γ ↓ X     the part of Γ strictly DEEPER than X — dropping X and
            everything bound after it.  X's EXISTENTIAL SCOPE.

No masks, no locks, no deletion-at-a-position.  The only context surgery
is TRUNCATE and APPEND.                                              [C1]

# Types

  A,B,C ::= X | ℕ | 𝔹 | A → B | ∀X.A        term types, over some Γ
  R,S   ::= α | X | ℕ | 𝔹 | R → S | ∀X.R    representations; every FREE
                                            variable an ANCHOR

  ⌊A⌋Γ = R    read out — total, every scoped variable is anchored
  ⌈R⌉Γ = A    read back — PARTIAL, defined when every anchor of R has a
              scoped variable in Γ                                   [C3]

As v4.  No type that any term has ever mentions an anchor.

# The boundary

ONE runtime form does all four jobs.

  e ::= X@α           APPEND a scoped variable for an existing anchor
      | X@(α:=R)      ALLOCATE α with representation R, and append X for it
  ρ ::= ∅ | ρ , e     appended entries, shallowest last
  Θ ::= ↓Y ; ρ        TRUNCATE at Y, then append ρ
      |      ρ        append only

  L,M,N ::= ... | M ⟪ Θ , c ⟫

  ------------------------------
  | Γ ⇈ Θ  = Γ′   the INTERIOR |
  ------------------------------

  Γ ⇈ (↓Y ; ρ) = (Γ ↓ Y) , ρ
  Γ ⇈ ρ        = Γ , ρ

ONE truncation, then append.  The truncation is a PREFIX by construction,
and the appended entries record ANCHORS — never a type read into the
interior, which is what killed v1 [C3].

  Σ ⊕ Θ    Σ extended by Θ's allocations (the `X@(α:=R)` entries)

# Conversions, in TWO contexts                                       [C2]

  c,d ::= id | c → d | ∀X.c | +X | -X

  Σ ; Γᵢ ; Γₑ ⊢ c : A ⇒ B        A over Γᵢ (INTERIOR), B over Γₑ (EXTERIOR)

  REVEAL — interior sees the name, exterior sees the representation:

    Γᵢ ∋ X@α     Σ ∋ α:=R     ⌈R⌉Γₑ defined
    ----------------------------------------
    Σ ; Γᵢ ; Γₑ ⊢ +X : X ⇒ ⌈R⌉Γₑ

  CONCEAL — interior sees the representation, exterior sees the name:

    Γₑ ∋ Y@α     Σ ∋ α:=R     ⌈R⌉Γᵢ defined
    ----------------------------------------
    Σ ; Γᵢ ; Γₑ ⊢ -Y : ⌈R⌉Γᵢ ⇒ Y

  THE ARROW RULE SWAPS THE CONTEXTS in its domain — contravariance
  becomes literal:                                                   [C2]

    Σ ; Γₑ ; Γᵢ ⊢ c : C ⇒ A       Σ ; Γᵢ ; Γₑ ⊢ d : B ⇒ D
    ------------------------------------------------------
    Σ ; Γᵢ ; Γₑ ⊢ c → d : (A → B) ⇒ (C → D)

    Σ ; Γᵢ,X@α ; Γₑ,X@α ⊢ c : A ⇒ B          Σ;Γᵢ ⊢ A   Σ;Γₑ ⊢ A
    -----------------------------------      --------------------
    Σ ; Γᵢ ; Γₑ ⊢ ∀X.c : ∀X.A ⇒ ∀X.B         Σ;Γᵢ;Γₑ ⊢ id : A ⇒ A

`id` is available only for a type well formed on BOTH sides — i.e. one
that SURVIVES the crossing.  In v3 that is a side condition; here it is
the rule.                                                            [C4]

# Term Typing

  Σ ⊢ Θ ok      Σ⊕Θ ; Γ⇈Θ ⊢ M : A
  Σ⊕Θ ; Γ⇈Θ ; Γ ⊢ c : A ⇒ B       Σ;Γ ⊢ B
  ----------------------------------------- (bnd)
  Σ ; Γ ⊢ M ⟪ Θ , c ⟫ : B

NO `names(b) ∩ FV(B) = ∅` SIDE CONDITION.  B is a type over Γ, and the
interior-only variables are simply not in Γ.  (Same win as v4 [v4 C6];
here it is even cleaner, since there is only one rule.)

  Σ ⊢ Θ ok    the truncation point is in Γ; every `X@α` names an
              α ∈ dom Σ; every `X@(α:=R)` has α ∉ dom Σ and Σ ⊢ R;
              the X's are distinct                                   [O3]

Λ, λ, application, ⊕, constants: as v3.

# Values                                                             [O4]

  Vˢ,Wˢ ::= λx:A. N | ΛX.V
  V,W   ::= k | Vˢ | V ⟪ Θ , c ⟫                               SKETCH

v3/v4's four-layer stratification existed because conceals, conversions
and positives were SEPARATE nodes that had to be ordered.  Fused, there is
nothing to order, so the layering — and PushConv, PushPos, MergeConceal,
the two Drops — may all go.  BUT the Progress argument that the layering
was carrying [v4 C7] then needs a replacement.  This is [O4], and it is
not sketched further here.

# Reduction Rules                                                    SKETCH

  (Beta, AppConv, DropId, DropConst, PrimBeta, ξ)   as v3.

  (TyBeta)   Γ ⊢ (Λ V) ⟪ Θ , c ⟫ • B[A]
               -→ V ⟪ Θ ⊹ (Y@(β:=⌊A⌋Γ)) , c ⨟ +Y(B) ⟫                [C5]

             ONE boundary.  Θ's truncation is unchanged; Y is APPENDED,
             so it lands SHALLOWEST and the truncation stays a prefix.
             This is the rule the whole design exists for.

  (AppBnd)   Γ ⊢ (V ⟪ Θ , c ⟫) · W  -→ (V · (W ⟪ Θᵈ , cᵈ ⟫)) ⟪ Θ , c′ ⟫
                                                                [O1] [C6]

  (Cancel)   a matched -X/+X pair spanning TWO adjacent boundaries
             requires Θ COMPOSITION                              [O2] [C6]


                        ======================
                        PART II — COMMENTARY
                        ======================

[C1] WHY FUSION RESCUES THE PREFIX DESIGN.  The obstruction (notes-v4
     [C16], notes/PrefixDesignProbe.agda) was that a freshly introduced Y
     ends up in scope while OLDER variables are concealed — a shape `Γ↓X`
     cannot denote, since it drops a SUFFIX.  That shape arose ONLY
     because the intro and the conceal were SEPARATE NODES that had to be
     ordered.  Fused, `Γ ⇈ (↓Y ; ρ) = (Γ↓Y) , ρ` truncates and THEN
     appends: the new entries land shallowest, so the truncation is a
     prefix by construction and there is no ordering question.
       MY EARLIER CLAIM that the prefix design is dead for a
     representation-independent reason was WRONG in its strong form.  It
     is independent of how CONTEXTS are represented, but not of the
     boundary being SPLIT.  notes-v4 [C16] and PrefixDesignProbe overclaim
     and should be corrected.

[C2] A TWO-CONTEXT CONVERSION IS A FUSED BOUNDARY.  `Γᵢ ; Γₑ ⊢ c : A ⇒ B`
     says something only if the node CHANGES the context — otherwise
     Γᵢ = Γₑ.  So the two ideas coincide: Θ supplies the two contexts and
     c mediates.
       THE TEST THAT IT IS THE RIGHT READING: contravariance becomes
     LITERAL CONTEXT SWAPPING.  `c → d` types its domain conversion with
     Γᵢ and Γₑ exchanged, because the domain crosses the boundary the
     other way.  In v3 that is an unexplained asymmetry in conv-fun ("the
     only trace the retired polarity index leaves"); here it falls out.

[C3] ANCHORS REMOVE WHAT KILLED v1's FUSED+PREFIX DESIGN.  v1 had exactly
     this shape — `Γ ⇈ Θ = (Γ↓Y★) , X₁:=⟦A₁⟧ , …` (notes/old/notes-v1.md
     §"The interior context") — and paid for it with `⟦A⟧`, the INTERIOR
     READING of an exterior representation, and its three-case fallback
     chain (knowledge / exterior-read / abstract).  The 2026-09-05 survey
     verdict was "every failure is a failed rep copy" (DECISIONS.md:1878).
       With anchors there is nothing to re-express.  An appended entry is
     `X@α`; the representation lives at α in Σ, which no truncation
     touches.  No reading, no fallback, no copy.
       AND THE PREFIX IS EXACTLY THE RIGHT SCOPE.  A conceal at Y types
     its interior at `Γ↓Y` — Y's existential scope — and Y's
     representation was recorded over the context BEFORE Y, i.e. over
     `Γ↓Y`.  So `⌈R⌉` on the interior side of a `-Y` is automatically
     defined.  v1 needed the fallback because the reading could reach a
     BLOCKED variable; anchored entries cannot.

[C4] `id` STOPS BEING A SIDE CONDITION.  Two-context typing makes
     `id : A ⇒ A` require A well formed on BOTH sides, i.e. a type that
     SURVIVES the crossing.  v3 has to say this separately (the boundary's
     `names(b) ∩ FV(B) = ∅`); here the conversion rule says it.

[C5] TyBeta, THE RULE THE DESIGN EXISTS FOR.  Split-boundary designs must
     put the new Y OUTSIDE the conceal, because the conversion needs the
     representation readable and must sit under Y's binder (notes-v4
     [C16]).  Fused, the conversion is the boundary's own payload, so
     "under" is not a question: Y is APPENDED to the same Θ, the
     truncation is untouched, and the interior stays `(Γ↓Y★) , ρ , Y@β`.
     `⌊A⌋Γ` is computed at the redex's context and stored at β, which is
     permanent [C3].

[C6] WHERE v2 BLED, AND WHETHER ANCHORS HELP.  Two places, and they are
     the honest risk of this design; see [O1] and [O2].  Anchors help with
     one and not obviously with the other:
       THE DUAL ([O1]) needs Θᵈ to RESTORE a truncated block — and the
     block is gone, so Θᵈ must re-append an entry for every dropped
     variable.  Anchors make each entry cheap (`X@α`, no rep to
     re-derive), and identity-by-anchor would make the resulting REORDERING
     immaterial.  But Θᵈ's size is the size of the dropped block, where
     v3/v4 restore in place at O(1).
       COMPOSITION ([O2]) is needed because Cancel matches a -X/+X pair
     that may span two adjacent boundaries.  Anchors give the pair a
     stable identity, which is the matching half; they say nothing about
     composing two truncate-then-append morphisms, which is the hard half
     and is where v2's `≼≈` came from.

[C7] WHAT I WOULD BET ON.  [C1]–[C5] I believe: they are short arguments
     about scope, and [C2]'s contravariance test is the kind of
     coincidence that indicates a right reading.  [C6] I do not: the dual
     and composition are exactly what made v2 expensive, and v6 does not
     obviously make them cheaper — it makes the INTERIOR cheaper and
     leaves the MORPHISM ALGEBRA where it was.  The question v6 has to
     answer is whether a prefix interior plus anchored entries is worth
     paying the morphism algebra for, when v3's masks buy the same
     interior with no algebra at all.


[C8] DO REPRESENTATIONS STILL NEED ANCHORS?  Jeremy: with two contexts,
     perhaps R is well formed in the exterior (for a reveal) or the
     interior (for a conceal), so the R,S sublanguage could go.  BOTH
     IMMEDIATE CASES WORK:
       REVEAL  `+X : X ⇒ R` needs R in the EXTERIOR, and the boundary's
               own field supplies it as a type over the exterior.
       CONCEAL `-Y : R ⇒ Y` needs R in the INTERIOR, which is `Γ↓Y` —
               EXACTLY the context Y's telescope entry was written over.
               The prefix truncation is what makes this automatic; it is
               Y's existential scope [C3].
     So a plain term type suffices AT THE BOUNDARY ITSELF.

     BUT THE RESIDUE IS REAL AND REACHED.  A boundary that BOTH truncates
     at Z AND appends Y:=A with A mentioning Z cannot store Y's
     representation in its interior telescope: Y's prefix there is Γ↓Z,
     which lacks Z.  An ABSTRACT entry would do unless something INSIDE
     needs Y's representation — and something does.  AppBnd's DUAL sends
     the argument back out through a conceal of Y, carrying `-Y`, whose
     INTERIOR side needs exactly that representation.

     notes/DeeperConcealProbe.agda REACHES THE SHAPE in three steps from

       (λg:(∀Y. ℕ→ℕ). ΛZ. (g •(ℕ→ℕ)[Z]) · 5) · (ΛY. λw:ℕ. w)

     — Beta sends g across the ΛZ (crossΛ conceals Z), TyConceal
     instantiates AT the concealed Z so the minted intro's representation
     IS Z, and AppBnd then drags a conceal of that fresh Y down INSIDE the
     intro.  Checked in the live v3 calculus, where the node is
     `ν conceal (0 ∷ []) [ … ]` inside `ν intro (` 0) [ … ]`; v3 survives
     it only because masking RETAINS the binding (`v3-retains`).
     A prefix interior does not retain.

     SO v6 KEEPS ANCHORED ENTRIES.  The R,S sublanguage could go if the
     entries were anchored some other way, but the entries themselves
     cannot be plain telescope types.

                        ================
                        PART III — OPEN
                        ================

[O1] THE DUAL, and the headline risk.  AppBnd sends the argument across
     `Θᵈ`, which must undo `Γ ⇈ Θ`.  Undoing an APPEND is a truncation;
     undoing a TRUNCATION is an append of the whole dropped block, in some
     order.  So:
       * Θᵈ's size is the size of the dropped block, not O(1);
       * the restored context is Γ UP TO REORDERING, not on the nose —
         v2's `≼≈` (notes/old/notes-v1.md:845) in a new place;
       * v3 and v4 do this in O(1) (unmask, or insert at a position) and
         land on Γ exactly.
     Identity-by-anchor would make the reordering immaterial.  Whether it
     makes the SIZE immaterial is a separate question and I do not think
     it does.

[O2] Θ COMPOSITION.  Cancel matches a -X/+X pair that may span two
     adjacent boundaries, so `Θ₁ ⊕ Θ₂` is needed.  With prefix interiors
     that is composing two truncate-then-append morphisms; the deeper
     truncation dominates, and the appends must be merged and re-indexed.
     v2's composition held only up to `≼≈`.  NOT WORKED HERE.

[O3] Could Θ be RESTRICTED so that no single boundary both truncates and
     appends a variable whose representation mentions the truncated block?
     That would remove [C8]'s residue by construction.  TyBeta as written
     violates it in exactly the motivating case, so the restriction would
     have to be bought with a different TyBeta — two boundaries instead of
     one, which is the split design again.  NOT WORKED.

[O4] `Σ ⊢ Θ ok` is stated loosely.  In particular whether an appended
     `X@α` may name an anchor that ALREADY has a scoped variable in Γ
     (v4's [O1]) — if it may, `⌈α⌉` is not deterministic.

[O5] VALUES AND PROGRESS.  Fusion may delete the whole layering and its
     administrative rules, since there is nothing left to order.  But the
     layering was carrying the termination argument for the
     boundary-elimination family (v4 [C7]): the administrative rules push
     positives out of a freshly minted conceal, exposing a tag to peel.
     With one boundary form that argument has no obvious analogue.  THIS
     IS THE SECOND-BIGGEST RISK after [O1].

[O6] COLOUR PRESERVATION.  The annotation would be "the scoped context",
     and a fused boundary changes it in one step, so the per-node
     bookkeeping should be simpler than v3's.  But a prefix interior
     REORDERS on the way back through the dual [O1], and an annotation
     that is a list of indices does not survive reordering.  This may be
     a third place identity-by-anchor is load-bearing.

[O7] THE COMPARISON THAT MATTERS.  v3 buys a cheap interior (masks) with
     no morphism algebra.  v6 buys a cheap interior (prefix + anchors)
     and pays a morphism algebra.  v4/v5 buy a cheap interior (deletion /
     names) with no algebra but a renumbering discipline.  The three are
     not obviously ordered, and the deciding measurements are [O1]'s dual
     and [O2]'s composition — both of which are v2 questions we already
     have data on.  Re-reading v2's Boundary.agda for what those actually
     cost is probably worth more than more design.
