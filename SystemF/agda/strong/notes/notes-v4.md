# Strong System F — v4: ANCHOR VARIABLES

STATUS: design draft, 2026-09-11.  Nothing mechanized.  Part I is the
definitions and rules; Part II is the commentary, cited as [C1]…[C12];
Part III the open questions [O1]…[O7]; Part IV what to check first.

Prior art: `GTSFImp/alt/Design.md` on branch `claude/gtsfimp-alt-semantics`
(PR #185).  v4 differs there in one respect: anchors are LEXICAL binders,
not a global store [C1].


                        =====================
                        PART I — THE CALCULUS
                        =====================

# Criteria   (unchanged from v3)

Color Preservation: the set of type variables in scope at every subterm
from the source program is invariant under reduction.
Progress, Preservation, Determinism: as v3.

# The two variable families                                          [C1]

  α,β,γ ∈ Anchor        permanent; allocated by Λ and by intro
  X,Y,Z ∈ TyVar         scoped; inserted by reveal, deleted by conceal

Every scoped variable is anchored.  A Λ allocates a REP-LESS anchor.  [C2]

# Types                                                           [C3]

  TERM TYPES        A,B,C ::= X | ℕ | 𝔹 | A → B | ∀X.A
  REPRESENTATIONS   R,S   ::= α | X | ℕ | 𝔹 | R → S | ∀X.R
                              every FREE variable an anchor

No type that any term has ever mentions an anchor.

  ----------------------------------------------
  | ⌊A⌋ = R   term type  ⟶  representation     |    TOTAL         [C2]
  ----------------------------------------------

  ⌊X⌋ = α  where X@α       ⌊ι⌋ = ι
  ⌊A → B⌋ = ⌊A⌋ → ⌊B⌋      ⌊∀X.A⌋ = ∀X.⌊A⌋

  ----------------------------------------------
  | ⌈R⌉ = A   representation  ⟶  term type     |    PARTIAL       [C4]
  ----------------------------------------------

  ⌈α⌉ = X  where X@α, IF ONE IS IN SCOPE; otherwise UNDEFINED
  ⌈ι⌉ = ι    ⌈R → S⌉ = ⌈R⌉ → ⌈S⌉    ⌈∀X.R⌉ = ∀X.⌈R⌉

# Contexts

  Σ ::= ∅ | Σ, α | Σ, α:=R      anchors; R anchor-closed over earlier Σ
  Δ ::= ∅ | Δ, X@α              scoped variables, each naming its anchor

  Δ ∖ X        Δ with the slot X DELETED
  Δ ⊕ (X@α)    Δ with a slot for α INSERTED at position X

Σ is APPEND-ONLY.  There is no lock, no mask, no Nameable/Locked.

# Conversions

  c,d   ::= id | c → d | ∀X.c | +X | -X
  cⁱ,dⁱ ::= c → d | ∀X.c | -X           (inert)
  cᵃ,dᵃ ::= id | +X                     (active)

Conversions name SCOPED VARIABLES, as in v3; the anchor is reached by
LOOKUP.                                                             [C13]

  Δ ∋ X@α   Σ ∋ α:=R   ⌈R⌉ defined      Δ ∋ X@α   Σ ∋ α:=R   ⌈R⌉ defined
  --------------------------------      --------------------------------
  Σ;Δ ⊢ +X : X ⇒ ⌈R⌉          [C4]      Σ;Δ ⊢ -X : ⌈R⌉ ⇒ X

  ------------------  ------------------
  Σ;Δ ⊢ id : ι ⇒ ι    Σ;Δ ⊢ id : X ⇒ X

  Σ;Δ ⊢ c : C ⇒ A    Σ;Δ ⊢ d : B ⇒ D        Σ;Δ,X@α ⊢ c : A ⇒ B   (α fresh,
  ----------------------------------        ----------------------  rep-less)
  Σ;Δ ⊢ c → d : (A → B) ⇒ (C → D)           Σ;Δ ⊢ ∀X.c : ∀X.A ⇒ ∀X.B

SYNTACTIC — a pure function of the type, no Δ:                       [C13]

  +X(X) = +X                       -X(X) = -X
  +X(Y) = id        (X ≠ Y)        -X(Y) = id        (X ≠ Y)
  +X(ι) = id                       -X(ι) = id
  +X(A → B) = -X(A) → +X(B)        -X(A → B) = +X(A) → -X(B)
  +X(∀Y.A) = ∀Y.+X(A)              -X(∀Y.A) = ∀Y.-X(A)

# Runtime Terms

  b ::= new X:α:=R | +X:α | -X:α        (R a REPRESENTATION)      [C5] [O5]
  L,M,N ::= ... | ν b [ M ] | M⟨c⟩

  ν new X:α:=R [ M ] INTRO.  Allocates the anchor α with representation R,
                     AND binds the slot X@α over the interior.  The only
                     form that extends Σ.  Its scoped half is exactly a
                     reveal: `Δ ⊕ (X@α)`.                           [C14]
  ν +X:α [ M ]       REVEAL, A BINDER.  The interior has a slot X@α that
                     the exterior does not.
  ν -X:α [ M ]       CONCEAL, AN ANTI-BINDER.  The exterior has a slot X@α
                     that the interior does not.

  ᵖ ::= new X:α:=R | +X:α               the POSITIVE tags               [C14]

  DERIVED FORM — THE CONCEAL SPINE.  A tag conceals ONE slot, so a run of
  conceals is ITERATION of the single form, not a new one:

    δ ::= ∅ | -X:α , δ
    ⁻∅[M]        = M
    ⁻(-X:α,δ)[M] = ν -X:α [ ⁻ᵟ[M] ]

  §Values and TyBeta both match a whole spine; nothing else does.    [C15]

  -----------
  | -b = b′ |
  -----------

  -(new X:α:=R) = -X:α
  -(+X:α)       = -X:α
  -(-X:α)       = +X:α

# Term Typing                                                        [C6]

  Σ ⊢ R      α ∉ Σ                       Σ ; Δ ⊕ (X@α) ⊢ M : C
  Σ,α:=R ; Δ ⊕ (X@α) ⊢ M : C             X ∉ FV(C)                  [O2]
  X ∉ FV(C)                              --------------------------
  -------------------------- (intro)     Σ;Δ ⊢ ν +X:α [ M ] : C  (reveal)
  Σ;Δ ⊢ ν new X:α:=R [ M ] : C

  (intro) IS (reveal) PLUS THE Σ EXTENSION — same scoped premise.    [C14]

  Σ ; Δ ∖ X ⊢ M : C                    Σ;Δ ⊢ M : A   Σ;Δ ⊢ c : A ↝ B
  ------------------------- (conceal)  ----------------------------- (conv)
  Σ;Δ ⊢ ν -X:α [ M ] : C               Σ;Δ ⊢ M⟨c⟩ : B

# Values                                                        [C7] [C8]

  Vˢ,Wˢ ::= λx:A. N | ΛX.V
  V⁻,W⁻ ::= ⁻ᵟ[Vˢ]                             (the spine, §Runtime Terms)
  Vᶜ,Wᶜ ::= V⁻ | Vᶜ⟨cⁱ⟩
  V⁺,W⁺ ::= Vᶜ | ᵖ[ V⁺ ]                       (ᵖ a POSITIVE tag)
  V,W   ::= k | V⁺

LAYERED, inside out: simple, conceals, conversions, positives — as v3.

# Substitution

As v3: a boundary is TERM-CLOSED so substitution stops at it; a conversion
is descended into.  Crossing a Λ wraps a value image:

  crossΛ W  =  ν -X:α [ W ]        (X, α the Λ's own slot and anchor)  [C9]

# Reduction Rules

  (Beta)       Δ ⊢ (λx:A. N) · W   -→ N[x:=W : A]
  (AppConv)    Δ ⊢ V⟨c → d⟩ · W    -→ (V (W⟨c⟩))⟨d⟩
  (AppBnd)     Δ ⊢ ᵇ[V⁺] · W       -→ ᵇ[V⁺ ⁻ᵇ[W]]   if ᵇ[V⁺] is a value
  (Cancel)     Δ ⊢ V⟨-X⟩⟨+X⟩      -→ V
  (DropId)     Δ ⊢ V⟨id⟩          -→ V
  (DropConst)  Δ ⊢ ᵇ[k]           -→ k
  (PrimBeta)   Δ ⊢ n₁ ⊕ n₂        -→ n₁ ⟦⊕⟧ n₂

  (TyBeta)     Δ ⊢ ⁻ᵟ[ΛY.V] •B[A] -→ ν new Y:β:=⌊A⌋ [ (⁻ᵟ′[V])⟨+Y(B)⟩ ]
                                      δ possibly EMPTY; subsumes v3's
                                      TyConceal      [C8] [C11] [C15] [C16]
                                      Y is OUTSIDE the spine — forced by
                                      the conversion                 [C16]
                                      δ′ re-indexed: the new slot Y is
                                      inserted OUTSIDE the spine     [O4]

  (TyConv)     Δ ⊢ V⟨∀X.c⟩ •B[A]  -→ (V A)⟨c⟩

  (TyPos)      Δ ⊢ ᵖ[V⁺] •B[A]    -→ ᵖ[ ν new Y:β:=⌊A⌋ [ (ν -Y:β [V⁺]) •B[Y]
                                                          ⟨+Y(B[Y])⟩ ] ]
                                                                     [C10]

  (PushConv)   Δ ⊢ ν -X:α [Vᶜ⟨cⁱ⟩]  -→ (ν -X:α [Vᶜ])⟨cⁱ′⟩            [C13]
  (PushPos)    Δ ⊢ ν -X:α [ᵖ[V⁺]]   -→ ᵖ′[ν -X′:α [V⁺]]
                                      if not a matched pair    [C14] [O4]
  (CancelBnd)  Δ ⊢ ν -X:α [ν +X:α [M]] -→ M   ← ANCHOR IDENTITY
               Δ ⊢ ν +X:α [ν -X:α [M]] -→ M

  (ξ)          as v3, with `ᵇ[M]` stepping at the interior context.

NO MergeConceal, NO DropReveal, NO DropConceal — see [C8].
PushIntro and Commute have MERGED into PushPos — see [C14].


                        ======================
                        PART II — COMMENTARY
                        ======================

[C1] WHY SPLIT THE VARIABLE.  v3 uses ONE variable for two jobs: type
     abstraction, and linking a conceal/reveal back to the intro that owns
     the representation.  Because the same slot does both, a conceal
     cannot hide the abstraction without breaking the link — so v3 keeps
     the slot and MASKS it (`masked b` retains `b`).  v4 splits them: the
     ANCHOR carries the representation and stays; the SCOPED VARIABLE does
     the abstraction and comes and goes.  Conceal then removes the slot
     OUTRIGHT and reveal is an ordinary binder.
       Anchors are LEXICAL, not a store, per the Q1 ruling (DECISIONS.md,
     2026-09-05): "once type variables are in a global store, it becomes
     more difficult to talk about their lexical scope relationships, which
     we are currently using in conceal blocking."

[C2] WHY Λ ALLOCATES AN ANCHOR.  Representations must be anchor-closed
     [C3], so `⌊·⌋` must be TOTAL, so every scoped variable must be
     anchored — including Λ-bound ones, whose anchor is REP-LESS.  This is
     where the GTSFImp alt stops: its `Transport` has NO clause for a
     `∀-bound` entry, so allocating at a Λ-bound variable is not
     expressible there.  `strong` cannot inherit that, since TyBeta's
     whole job is instantiating at whatever the exterior supplies.
       (v1 had rep-less entries for a related reason: `↑X:⋆`, `↓Y:⋆`.)

[C3] WHY REPRESENTATIONS MAY NAME ANCHORS.  TWICE RETRACTED AND FINALLY
     ARGUED (2026-09-11).  The forcing is NOT about where a node sits, and
     not about Σ's existence; it is about what a CONCEAL DOES TO THE ENTRY.

       THE ARGUMENT.  A v4 conceal DELETES X's entry from the interior.  A
     later reveal must RESTORE it — with its representation.  So the
     representation must live somewhere the deletion did not touch, i.e.
     somewhere PERMANENT; and a permanent store cannot hold a type scoped
     at a transient context, so its entries must be context-independent,
     i.e. anchor-closed.
       v3 ESCAPES THIS ENTIRELY, and that is the whole point of masking:
     `masked b` RETAINS b, so the rep never leaves the context and v3 can
     keep it as an ordinary telescope type.  v6's prefix truncation does
     NOT escape it — see notes-v6 §"Do representations still need
     anchors?" and notes/DeeperConcealProbe.agda.

       TWO EARLIER ARGUMENTS, BOTH WRONG, kept because they were believed:
       (a) "TyConceal plants an intro INSIDE a conceal."  Superseded: since
           the TyBeta/TyConceal unification the intro is always OUTSIDE
           [C16], where its field is a type over the node's own exterior.
       (b) "Σ is permanent, so its entries cannot be scoped at a transient
           Δ" — circular, since Σ exists only to hold representations; and
           "crossΛ/AppBnd wrap a value that may contain an intro naming the
           concealed variable" — REFUTED by the premises: crossΛ conceals
           the Λ's FRESH slot, which the wrapped value predates and cannot
           name, and AppBnd at a reveal conceals slots that ⊢reveal
           requires be LOCKED in Δ, which the argument therefore cannot
           name either.

       WHAT ANCHORS ARE ACTUALLY FOR, then: (1) surviving a conceal that
     REMOVES an entry, above; (2) IDENTITY — Cancel matching across a
     crossing, and [O6]-style position-independence.  Not representations
     in general.

[C4] READ-BACK IS PARTIAL, AND THAT IS THE TIGHTNESS DISCIPLINE.  A
     representation may always be LOOKED UP — the anchor is always there —
     but may only be USED where every anchor it mentions currently has a
     scoped variable.  Concealing does not delete knowledge; it makes it
     unreadable.
       This also closes a gap v3 has TODAY: `conv-unseal` carries no
     well-formedness premise on the rep it returns, so at a concealing
     frame `unseal X` is derivable with a target naming a masked slot, and
     regularity — `Γ ⊢ M : A ⟹ Γ ⊢ A` — is FALSE.  v4 closes it by
     construction.

[C5] AN INTRO'S FIELD IS A REPRESENTATION, NOT A TERM TYPE.  `Σ ⊢ R`
     mentions no Δ, so the field is independent of the scoped context and
     the node may be planted at any depth.  A term-type field would be
     scoped at the node's own exterior, and every rule that moves an intro
     inward would have to re-scope it — impossible for TyBeta at a conceal
     stack, since the type argument may name the very variable concealed
     [C3].

[C6] WHAT DISAPPEARED FROM THE TYPING RULES.  v3's
     `names(b) ∩ FV(B) = ∅` becomes `X ∉ FV(C)` on the two rules that ADD
     a slot to the interior, and on (conceal) it is not needed at all — C
     is already a type over the smaller context.  v3's `Δ ∋lks χ` /
     `Δ ∋tvs χ` premises (the 2026-09-11 repair) vanish: there is no "was
     it locked?" question when the slot is simply absent.

[C7] WHY THE LAYERING IS KEPT  (RULED, Jeremy, 2026-09-11).  A FLAT value
     grammar — any value under any boundary — would delete PushConv,
     PushIntro and Commute, and would make "substituting a value into a
     value yields a value" TRUE (in v3 it is false,
     notes/AppBndExample.agda §5).  It also opens a PROGRESS GAP: at a ∀
     type it admits a value whose body is not a Λ,

       (ν -X:α [ ν new β:=R [ Λ V ] ]) • B [ A ]

     and no rule applies — TyPos wants a POSITIVE tag, TyBeta wants a Λ
     under the conceal stack.  Layered, this is not a value: PushIntro
     fires, and TyPos then peels the positive tag.
       THE NATURAL REPAIR REGRESSES.  Generalising to
     `ᵇ[V] •B[A] -→ ᵇ[ν new β [(ν -Y:β [V]) •B[Y] ⟨…⟩]]` makes the inner
     redex an instance of the same rule, forever.  The layering is what
     terminates it: the administrative rules push positives OUT of the
     freshly minted conceal, exposing a positive tag to peel — the tower
     measure, TyBeta consuming a Λ at height zero.  Dropping the inner
     conceal would terminate but is unsound: V came from inside b and must
     not learn A.
       KEEPING IT COSTS v4 NOTHING.  With no masks, PushIntro hoisting an
     intro out of a conceal is a pure re-association: intro-outside and
     intro-inside denote the SAME context.  What v4 buys was never the
     placement, it is that the representation can be RECORDED AT ALL.

[C8] THE CONCEAL LAYER IS A STACK, NOT A SET.  v3's layer is ONE node
     carrying a SET (`⁻χ[Vˢ]`); v4's tags carry one slot, so the layer is
     a stack.  Two consequences:
       * MergeConceal HAS NO ANALOGUE.  It fused two set-tags into one; a
         stack is already normal, and two single-slot conceals cannot fuse.
       * Anything that matched v3's single conceal node must now match a
         STACK — which is why v3's TyBeta and TyConceal UNIFY: TyBeta over
         `⁻ᵟ[ΛY.V]` with δ possibly empty IS v3's TyBeta at δ = ∅ and v3's
         TyConceal at δ ≠ ∅.
     DropReveal/DropConceal also have no analogue: they dropped EMPTY
     tags, and a single-slot tag is never empty.

[C9] crossΛ'S SHIFT DISAPPEARS.  v3 has
     `crossΛ W = ν conceal (0∷[]) [ ⇑ᴹ W ]` — the `⇑ᴹ` because the Λ's slot
     is present-but-masked in the interior, so W's indices move.  In v4 the
     slot is ABSENT, so W's context is the one it was already typed in.
     Subject to [O3].

[C10] ⌊A⌋ IS NEVER SHIFTED.  v3's TyPos had to lift A into b's interior
      (`shiftBy (numBindsᵇ b) A`) because the rep was a term type and the
      interior had more binders.  An anchor-closed rep is
      position-independent, so it is planted verbatim at any depth.  This
      is the same property as [C3] and [C5], doing a third job.

[C11] THE MOTIVATING CASE, WORKED.  v3, at Γ, Z:

        ⁻{Z}[ΛY.V] •(Y→Y)[Z]  -→  ⁺ʸ⁼ᶻ[ (⁻{Z}[V])⟨+Y(Y→Y)⟩ ]

      with the conceal's body at `Γ, locked(Z), Y=Z` — Y newer and
      visible, Z older and hidden (notes/TyConcealExample.agda).  v4:

        ⁻ᵟ[ΛY.V] •(Y→Y)[Z]  -→  ν new β:=⌊Z⌋ [ (⁻ᵟ[V])⟨+β(Y→Y)⟩ ]

      δ = -Z:α, so ⌊Z⌋ = α.  The body's context is `Δ ∖ Z` — Z is simply
      not there, no mask.  The body may name Y; it may not read β's
      representation, because `⌈α⌉` is undefined once Z's slot is gone.
      Tightness as a SCOPE condition rather than a mask.

[C12] THE LEDGER.  v4 COSTS two binder families, two renamings, two
      transport lemmas, and a partial read-back every conversion rule must
      discharge.  It DELETES masks and the whole `unmasked`/`masked` entry
      layer, `∋lks`/`∋tvs` and their round-trip lemmas, the VarSet
      machinery (`lockχ`, `unlockχ`, `_∖_`, `_∪_`, `scopeᵇ`, `mergeᵒ`),
      `MergeConceal`, `DropReveal`, `DropConceal`, the non-empty-set side
      conditions, `shiftBy` on representations, one of v3's two
      type-application-at-a-Λ rules, and one of PushIntro/Commute [C14].


[C13] WHY CONVERSIONS NAME SCOPED VARIABLES, NOT ANCHORS  (RULED, Jeremy,
      2026-09-11).  Both work — `+α`'s typing rule already demands
      `Δ ∋ X@α`, so the two are inter-derivable given Δ.  The deciding
      difference is the MINT: `+α(A)` needs Δ to decide whether X is
      anchored at α, whereas `+X(A)` is a pure function of the type.  v3's
      revTy/concTy port over unchanged, and anchors stay confined to
      boundaries, context entries and representations.
        THE COST is one renumbering, in one rule.  PushConv is the ONLY
      rule that moves a conversion between contexts — out of a conceal,
      from `Δ ∖ X` to `Δ` — so `cⁱ` needs a single-insertion renaming on
      the way (`cⁱ′` above).  Everywhere else is free: AppBnd sends W
      across the DUAL, and `(Δ ⊕ X) ∖ X`, `(Δ ∖ X) ⊕ X` and
      `(Δ, X@α) ∖ X` all return Δ — v4's analogue of v3's
      `lock-unlock`/`unlock-lock` — so conversions inside a crossed
      argument never change context at all.
        THE RISK, stated plainly: Cancel matches `V⟨-X⟩⟨+X⟩` BY NAME, so
      two conversions separated by a crossing and reunited by PushConv
      match only if that renumbering is exactly right.  That is the class
      of bug TyPos had (a renaming and its partner conceal disagreeing by
      one, 2026-09-11).  Anchor naming would make it unfalsifiable; this
      makes it a proof obligation — for which the colour annotations are
      exactly the tripwire.  Free if [O6].

[C14] THE INTRO NAMES ITS SLOT  (Jeremy, 2026-09-11): `new X:α:=R`, not
      `new α:=R`.  Three things follow.
        * (intro) IS (reveal) PLUS THE Σ EXTENSION.  Both have the scoped
          premise `Σ ; Δ ⊕ (X@α) ⊢ M : C` with `X ∉ FV(C)`; the intro adds
          `Σ ⊢ R`, `α ∉ Σ`, and the Σ entry.  The two-jobs split [C1] is
          now visible in the syntax: `new` does the anchor job AND the
          scoped job, `+`/`-` do only the scoped one.
        * THE POSITIVE TAGS BECOME A CLASS, `ᵖ ::= new X:α:=R | +X:α`,
          which is what §Values' top layer and TyPos both range over.
        * PushIntro AND Commute MERGE.  Both were "swap a conceal past a
          slot-introducing tag"; with the intro's slot explicit they are
          one rule, PushPos.  The side condition (not a matched pair, vs
          CancelBnd) is vacuous in the intro case, since an intro
          allocates a FRESH anchor.

[C15] WHY A SPINE RATHER THAN A LIST-CARRYING TAG.  v3's conceal layer is
      ONE node carrying a SET, which is why v3's TyConceal can match it
      with a single pattern.  v4's tags carry one slot, so the layer is a
      RUN of nodes, and anything matching the layer — §Values' V⁻ and
      TyBeta — must match a SPINE.  The two options:

        (a) TAGS CARRY A LIST, `-χ` with χ a list of (X:α).  The layer is
            one node again and no spine notation is needed.  But
            MergeConceal returns (two adjacent tags must fuse), so does
            DropConceal (the empty list), and Cancel/PushPos need
            MEMBERSHIP in χ — i.e. v3's VarSet machinery, which [C12]
            counts as deleted.
        (b) TAGS STAY SINGLE-SLOT, and the spine is a DERIVED FORM
            (§Runtime Terms).  No MergeConceal, no set machinery, no
            non-empty side conditions.  Cost: TyBeta matches an unbounded
            spine, so mechanically it is a pattern over a derived function
            plus a canonical-forms lemma ("a value at a ∀ type is
            `⁻ᵟ[ΛY.V]` for some δ") — which Progress needs anyway.

      TAKEN (b).  The spine is notation over the single form, not a second
      form, and §Runtime Terms is where it is introduced.  Note the
      contractum re-indexes it: TyBeta inserts the new slot Y OUTSIDE the
      spine, so δ′ is δ shifted past one insertion — another [O4] site.

[C16] WHY TyBeta'S NEW Y IS OUTSIDE THE CONCEAL SPINE.  Forced by the
      CONVERSION, not chosen for tidiness.  `+Y(B)` types only where β's
      representation is READABLE — `⌈R⌉` defined, i.e. every variable of A
      still in scope — and inside the spine that can fail, in exactly the
      motivating case (A = Z, δ concealing Z).  So the conversion must sit
      OUTSIDE the spine; and it needs Y in scope, so the intro must
      ENCLOSE it.  The three candidates:

        intro + conversion inside ⁻ᵟ   ⌈⌊A⌋⌉ undefined
        intro inside, conversion out   conversion at Δ, where Y is absent
        BOTH OUTSIDE                   types

      It also agrees with the layering (positives outside conceals), so
      PushPos has nothing to do — but agreement is not the reason; the
      placement would be forced without the layering.
        NOTE this is the SAME placement v3's TyConceal uses.  What v4
      changed here was never the placement [C7]: it is that the resulting
      frame `(Δ ⊕ Y) ∖ δ` needs no mask.
        AND THIS IS WHY THE Γ↓X PREFIX DESIGN IS DEAD FOR SPLIT
      BOUNDARIES.  The contractum has Y (newest) in scope while δ's slots
      (older) are gone — the non-prefix shape.  Read the forcing again:
      the representation must be READABLE where the conversion is, and the
      conversion must sit UNDER the binder it converts.  Neither step
      mentions masks, deletion, positions or names, so the ordering is
      forced under v3's masks, under v4's deletion and under v5's names
      alike, and `Γ↓X` — which drops a SUFFIX — cannot express it in any
      of them.
        CORRECTED 2026-09-11.  I first wrote that this survives EVERY
      design change.  It does not: the second premise assumes the boundary
      and the conversion are SEPARATE NODES.  FUSE them (v2-style, one
      node carrying the scope change AND the conversion) and "under" is
      not a question — the interior becomes `(Γ↓Y) , ρ`, truncate THEN
      append, and the prefix survives.  See notes-v6.md.  So the claim is
      representation-independent but NOT boundary-shape-independent.
        notes/PrefixDesignProbe.agda reached the same verdict framed as
      "two rules force non-prefix MASKS", which reads as a fact about
      masks.  It is a fact about CONVERSIONS AT SPLIT BOUNDARIES.

                        ========================
                        PART III — OPEN
                        ========================

[O1] May two scoped variables be anchored at one α at a time?  Everything
     above assumes NO, so that `⌈α⌉` is deterministic.  A reveal under a
     reveal at the same anchor would violate it; whether any rule produces
     that needs checking.

[O2] Does (reveal) need `Σ ∋ α` plus a freshness condition saying no
     scoped variable for α is already in Δ?  See [O1].

[O3] Does `Δ ∖ X` RENUMBER?  If deletion is positional then indices above
     X move, and [C9]'s claim that crossΛ loses its shift is wrong.  Free
     if identity is by anchor rather than position [O6].

[O4] RENUMBERING, the one obligation v4 adds.  FOUR sites, all the same
     kind:
       * PushPos's X′ and ᵖ′ — the swap reaches the same interior only if
         both are adjusted for whether the other happened first;
       * PushConv's cⁱ′                                            [C13]
       * TyBeta's δ′ — the new slot Y is inserted outside the spine [C15]
       * crossΛ                                              [C9] [O3]
     This is the v4 analogue of v3's set difference (χ₂∖χ₁, χ₁∖χ₂) —
     simpler, but not free.  ALL FOUR go away under [O6].

[O5] The intro is spelled `new` where v3 wrote it `+X=A`, a positive tag
     alongside the reveal.  Naming, not design.

[O6] IDENTITY BY ANCHOR RATHER THAN SLOT.  If a revealed variable is "the
     variable of α" rather than "slot n", re-inserting it at a different
     position is harmless, and v1's order-sensitivity (monotone renamings;
     boundary composition only up to `≼≈`, notes/old/notes-v1.md:845) may
     go away.  Would also settle [O3] and [O4].  Not attempted.

[O7] COLOUR PRESERVATION.  v3's annotation `κ ≡ scopeᵗ Δ` becomes just
     "the scoped context", and `scopeᵇ` should collapse to insert/delete.
     Does AppBnd still have to rebuild its application node's annotation?


                        ========================
                        PART IV — WHAT TO CHECK
                        ========================

 1. [O3] and [O4] together: does deletion renumber, and if so what do
    the four renumbering sites actually cost?  These gate the claim that
    v4 is cheaper than masking.
 2. Does AppBnd at a `+` tag stay well behaved?  v3 needed `lock-unlock`
    for the dual round trip; here it should be a DELETE-then-INSERT
    identity, which is either free or false depending on [O3].
 3. [O1]: does any rule produce two scoped variables at one anchor?
 4. Determinism, pairwise, over the restored administrative rules —
    PushPos against CancelBnd in particular, which is why PushPos carries
    its side condition.
 5. [O7].
