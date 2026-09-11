# Strong System F — v4 design: ANCHOR VARIABLES

STATUS: design draft, 2026-09-11.  Nothing is mechanized yet.  Open
questions are marked **OPEN**.

Prior art: `GTSFImp/alt/Design.md` on branch `claude/gtsfimp-alt-semantics`
(PR #185), §"Two classes of type variable" and §"Reveal is a binder,
conceal is an anti-binder".  v4 adapts that to `strong`, with one
deliberate difference: anchors here are LEXICAL binders, not a global
store — per the Q1 ruling (DECISIONS.md, 2026-09-05), "once type variables
are in a global store, it becomes more difficult to talk about their
lexical scope relationships, which we are currently using in conceal
blocking."

# Why v4

v3 uses ONE variable for two jobs: type abstraction, and linking a
conceal/reveal back to the intro that owns the representation.  Because
the same slot does both, a conceal cannot hide the abstraction without
also breaking the link — so v3 keeps the slot and MASKS it
(`masked b` retains `b`).  Masking works, but it is why the context can
never be truncated, and truncation is what the `Γ↓X` design needed.

v4 splits the two jobs:

  * an ANCHOR α carries the representation and STAYS IN SCOPE;
  * a SCOPED TYPE VARIABLE X does the abstraction and COMES AND GOES.

A conceal then removes X from scope OUTRIGHT — no mask, no mark, the slot
is simply not there — and a reveal is an ordinary BINDER that brings one
back.  Both name the anchor, so they can still find the representation and
still know which crossing cancels which.

Three consequences, in decreasing order of confidence:

  1. Representations survive concealment without being copied.  v1's
     `Γ⇈Θ` had to COPY the rep inward (`⟦A⟧`, a three-case fallback chain,
     notes/old/notes-v1.md §"The interior context") because truncation
     destroyed the binder the name pointed at.  An anchor is not destroyed,
     so the representation stays a POINTER — the Q1 discipline, now
     compatible with truncation.
  2. An intro's two halves may straddle a boundary.  In v3 `⁺ʸ⁼ᶻ` must sit
     OUTSIDE `⁻{Z}`, because Z must be visible when the rep is recorded;
     that is exactly what strands a newer visible slot above an older
     hidden one (notes/TyConcealExample.agda).  In v4 the rep is `⌊A⌋`,
     anchor-closed, which the conceal does not touch — so the intro can
     sit INSIDE.  See §"What this buys".
  3. **OPEN** Identity may become the anchor rather than the slot.  If a
     revealed variable is "the variable of α" rather than "slot n", then
     re-inserting it at a different position is harmless, and v1's
     order-sensitivity (monotone renamings; boundary composition only up to
     `≼≈`, notes/old/notes-v1.md:845) may go away.  Not attempted below.

# Criteria  (unchanged from v3)

Color Preservation: the set of type variables in scope at every subterm
from the source program is invariant under reduction.

Progress, Preservation, Determinism: as in v3.

# The two variable families

  α,β,γ ∈ Anchor        permanent; introduced by Λ and by intro
  X,Y,Z ∈ TyVar         scoped; inserted by reveal, deleted by conceal

EVERY scoped variable is anchored.  In particular a Λ ALSO allocates an
anchor — a REP-LESS one.  This is not decoration: it is what makes
representations anchor-closed (below), and it is what lets a Λ-bound
variable be concealed and revealed like any other.  (v1 had the same
four-way split for a related reason: `Θ ::= … | ↑X:⋆ | ↓Y:⋆ | …`.)

# Types

TWO SUBLANGUAGES.  **No type that any term has ever mentions an anchor.**

  TERM TYPES        A,B,C ::= X | ℕ | 𝔹 | A → B | ∀X.A
  REPRESENTATIONS   R,S   ::= α | X | ℕ | 𝔹 | R → S | ∀X.R
                              with every FREE variable an anchor
                              (a bound X, as in ∀X. X → α, is ordinary)

Term types are v3's types, unchanged.  Only an ANCHOR'S STORED
REPRESENTATION may name anchors, and it MUST be able to:

  THE FORCED CASE.  TyConceal's contractum puts an intro INSIDE a conceal:

      ν -Z:α [ΛY.V] •B[A] -→ ν -Z:α [ ν new β:=⌊A⌋ [ V⟨+β(B)⟩ ] ]

  ⌊A⌋ is computed at the REDEX's context, where A is well formed — but it
  is PLANTED inside the conceal, where A's own variables need not be.  Take
  the instance A = Z, the concealed variable itself: ⌊A⌋ = α, and inside
  the conceal Z's slot is GONE, so the field could not have been a term
  type.  Nor can β alias some representation of α's own: α is Λ-bound,
  hence REP-LESS.  "Whatever α stands for" is the only thing there is to
  say, and saying it names the anchor.  It is not special to a bare
  variable either — A may be `ℕ → Z`, so anchors must sit INSIDE compound
  representations.

  REJECTED ALTERNATIVE: keep representations as term types, scoped at the
  ENCLOSING conceal's exterior (where Z is still in scope).  Then a node's
  rep field is scoped at a context determined by some OTHER node, which
  breaks as soon as ξ moves either of them — and it puts the intro back
  outside the conceal, which is the thing v4 exists to avoid.

Anchors therefore appear in exactly four places: reveal/conceal tags,
conversions (+α / -α), context entries (X@α), and representations.

  ----------------------------------------------
  | ⌊A⌋ = R   term type  ⟶  representation     |
  ----------------------------------------------

  ⌊X⌋ = α        where X is anchored at α
  ⌊ι⌋ = ι
  ⌊A → B⌋ = ⌊A⌋ → ⌊B⌋
  ⌊∀X.A⌋ = ∀X.⌊A⌋            (X is bound inside; it stays a scoped variable)

`⌊·⌋` is TOTAL, because every scoped variable is anchored.  That totality
is the reason Λ must allocate an anchor.  (Contrast the GTSFImp alt, whose
`Transport` has no clause for a `∀-bound` entry — there, allocating at a
Λ-bound variable is not expressible.)

  ----------------------------------------------
  | ⌈R⌉ = A   representation  ⟶  term type     |
  ----------------------------------------------

  ⌈α⌉ = X        where X is THE scoped variable anchored at α, IF ONE IS IN
                 SCOPE; otherwise ⌈R⌉ is UNDEFINED
  ⌈ι⌉ = ι ,  ⌈R → S⌉ = ⌈R⌉ → ⌈S⌉ ,  ⌈∀X.R⌉ = ∀X.⌈R⌉

READ-BACK IS PARTIAL, AND THAT PARTIALITY IS THE TIGHTNESS DISCIPLINE.
A representation may be looked up from anywhere — the anchor is always
there — but it may only be USED where every anchor it mentions currently
has a scoped variable.  Concealing X does not delete the knowledge; it
makes the knowledge unreadable.

**OPEN** Whether at most one scoped variable may be anchored at a given α
at a time.  Everything below assumes YES (so `⌈α⌉` is deterministic).  A
reveal under a reveal at the same anchor would violate it; whether any
rule can produce that needs checking.

# Contexts

  Σ ::= ∅ | Σ, α | Σ, α:=R          anchors; R anchor-closed over earlier Σ
  Δ ::= ∅ | Δ, X@α                  scoped variables, each naming its anchor

Σ is APPEND-ONLY: no rule removes an anchor.  Δ is manipulated by
reveal/conceal, which INSERT and DELETE a slot at a named position.

  Δ ∖ X        Δ with the slot X deleted
  Δ ⊕ (X@α)    Δ with a slot for α inserted at position X

There is no lock, no mask, and no `Nameable`/`Locked` discrimination.  The
whole of v3's §"Locking and Unlocking" and `Ent = unmasked | masked`
disappears.

# Conversions

  c,d   ::= id | c → d | ∀X.c | +α | -α
  cⁱ,dⁱ ::= c → d | ∀X.c | -α           (inert)
  cᵃ,dᵃ ::= id | +α                     (active)

CONVERSIONS NAME ANCHORS, NOT SCOPED VARIABLES.  That is what makes a
conversion stable across a crossing that changes Δ.

  Δ ∋ X@α      Σ ∋ α:=R      ⌈R⌉ defined
  ---------------------------------------
  Σ;Δ ⊢ +α : X ⇒ ⌈R⌉                        (reveal the representation)

  Δ ∋ X@α      Σ ∋ α:=R      ⌈R⌉ defined
  ---------------------------------------
  Σ;Δ ⊢ -α : ⌈R⌉ ⇒ X                        (conceal it)

  ------------------  ------------------
  Σ;Δ ⊢ id : ι ⇒ ι    Σ;Δ ⊢ id : X ⇒ X

  Σ;Δ ⊢ c : C ⇒ A    Σ;Δ ⊢ d : B ⇒ D
  ----------------------------------
  Σ;Δ ⊢ c → d : (A → B) ⇒ (C → D)

  Σ;Δ,X@α ⊢ c : A ⇒ B         (α fresh, rep-less)
  -----------------------------------------------
  Σ;Δ ⊢ ∀X.c : ∀X.A ⇒ ∀X.B

NOTE the `⌈R⌉ defined` premise.  In v3 the corresponding gate is that the
slot be `unmasked`.  Here it is stronger and more informative: it is not
enough that X be in scope, the REPRESENTATION must be readable too.  (v3
lacks this: `conv-unseal` has no well-formedness premise on the rep it
returns, so at a concealing frame `unseal X` is derivable with a target
type naming a masked slot, and regularity — `Γ ⊢ M : A ⟹ Γ ⊢ A` — is
false.  v4 closes that by construction.)

  +α(A) and -α(A) are as in v3, with the CONTRAVARIANT arrow clause:

  +α(X) = +α  if X@α, else id      -α(X) = -α  if X@α, else id
  +α(ι) = id                       -α(ι) = id
  +α(A → B) = -α(A) → +α(B)        -α(A → B) = +α(A) → -α(B)
  +α(∀X.A) = ∀X.+α(A)              -α(∀X.A) = ∀X.-α(A)

# Runtime Terms

  b ::= new α:=R | +X:α | -X:α          (R a REPRESENTATION)

  **OPEN** the intro is still spelled `new`.  v3 wrote it `+X=A`, i.e. as
  a positive tag alongside the reveal.  Whether v4 should follow suit
  (`+X:α:=R`?) is a naming call, not a design one.
  L,M,N ::= ... | ν b [ M ] | M⟨c⟩

  ν new α:=R [ M ]   INTRO.  Allocates the anchor α with representation R,
                     and brings a scoped variable for it into the
                     interior.  Both at once — this is the only form that
                     extends Σ.
                     THE FIELD IS A REPRESENTATION, NOT A TERM TYPE.  That
                     is what lets an intro be PLANTED anywhere: R is
                     anchor-closed, so it needs nothing of Δ in scope.  A
                     term-type field would be scoped at the node's own
                     exterior, and every rule that moves an intro inward
                     (TyConceal, TyPos) would then have to re-scope it —
                     which for TyConceal is impossible, since the type
                     argument may name the very variable being concealed.
  ν +X:α [ M ]     REVEAL, A BINDER.  The interior has a slot X@α that
                     the exterior does not.
  ν -X:α [ M ]     CONCEAL, AN ANTI-BINDER.  The exterior has a slot X@α
                     that the interior does not.

  -----------
  | -b = b′ |
  -----------

  -(new α:=R) = -X:α       (X the slot the intro introduced)
  -(+X:α)     = -X:α
  -(-X:α)     = +X:α

The dual is now an involution on (+, -), with intro's dual the conceal of
the slot it introduced — the same story as v3, one line shorter.

# Term Typing

  Σ ⊢ R            α ∉ Σ
  Σ,α:=R ; Δ,X@α ⊢ M : C            X ∉ FV(C)
  --------------------------------------------------  (intro)
  Σ;Δ ⊢ ν new α:=R [ M ] : C

  NOTE `Σ ⊢ R` mentions NO Δ.  An intro's field is independent of the
  scoped context, which is exactly why it may be planted inside a conceal.

  Σ ; Δ ⊕ (X@α) ⊢ M : C             X ∉ FV(C)
  --------------------------------------------------  (reveal)
  Σ;Δ ⊢ ν +X:α [ M ] : C

  Σ ; Δ ∖ X ⊢ M : C
  --------------------------------------------------  (conceal)
  Σ ; Δ ⊢ ν -X:α [ M ] : C

  Σ;Δ ⊢ M : A     Σ;Δ ⊢ c : A ↝ B
  --------------------------------
  Σ;Δ ⊢ M⟨c⟩ : B

WHAT DISAPPEARED.  v3's `names(b) ∩ FV(B) = ∅` is now `X ∉ FV(C)` on the
two rules that ADD a slot to the interior — and on (conceal) it is not
needed at all, because C is already a type over the smaller context.  v3's
`Δ ∋lks χ` / `Δ ∋tvs χ` premises (the 2026-09-11 repair) vanish: there is
no "was it locked?" question when the slot is simply absent.

**OPEN** Whether (reveal) needs `Σ ∋ α` plus a freshness condition saying
no scoped variable for α is already in Δ (see the OPEN in §Types).

# Values

THE GRAMMAR IS FLAT.  Any value under any boundary; any value under any
inert conversion.

  V⁺,W⁺ ::= λx:A. N | ΛX.V | ν b [ V⁺ ] | V⁺⟨cⁱ⟩
  V,W   ::= k | V⁺

ONE stratification survives: a constant under a boundary must not be a
value, or it overlaps DropConst.

WHY v3 WAS LAYERED, AND WHY v4 NEED NOT BE.  v3's grammar is layered
inside out — simple, conceal, conversions, positives —

  Vˢ ::= λx:A. N | ΛX.V
  V⁻ ::= Vˢ | ⁻ᴸ[Vˢ]
  Vᶜ ::= V⁻ | Vᶜ⟨c→d⟩ | Vᶜ⟨∀X.c⟩ | Vᶜ⟨-X⟩
  V⁺ ::= Vᶜ | [V⁺]⁺ˣ⁼ᴬ | [V⁺]⁺ᴸ

and EVERY administrative rule is generated by exactly one out-of-order
pair of it:

  conceal inside conceal      MergeConceal
  conversion inside conceal   PushConv
  intro inside conceal        PushIntro
  reveal inside conceal       Commute

So PushIntro was never an independent rule — it is the price of putting
positives outside conceals.  Those out-of-order shapes are produced by
`crossΛ` and `AppBnd`-at-an-intro, both of which wrap an ARBITRARY value
in a conceal; which is why, in v3, "substituting a value into a value
yields a value" is FALSE (notes/AppBndExample.agda §5).  Flat, it is true.

  DELETES  PushConv, PushIntro, Commute, MergeConceal, DropReveal,
           DropConceal — six rules, all bookkeeping.
  COSTS    canonical forms stop being UNIQUE.  Progress needs COVERAGE,
           not uniqueness — but see the gap below.

## **OPEN — A PROGRESS GAP THE FLAT GRAMMAR OPENS**

Found while making this change.  At a ∀ type the flat grammar admits a
value `ν -X:α [ V ]` whose body is NOT a Λ, e.g.

    (ν -X:α [ ν new β:=R [ Λ V ] ]) • B [ A ]

Under v3's layering this is not a value — PushIntro fires, hoisting the
intro out, and TyPos then peels the positive tag.  FLAT, IT IS A VALUE,
and no rule applies: TyPos wants a POSITIVE tag, and TyConceal wants a Λ
directly under the conceal.

THE NATURAL FIX REGRESSES.  Generalising TyConceal to TyPos's shape,

    ᵇ[V] •B[A] -→ ᵇ[ ν new β:=⌊A⌋ [ (ν -Y:β [V]) •B[Y] ⟨+β(B[Y])⟩ ] ]

makes the inner redex `(ν -Y:β [V]) •B[Y]` an instance of the same rule,
forever.  v3 terminates precisely BECAUSE the administrative rules push
positives out of the freshly minted conceal, exposing a positive tag for
TyPos to peel — the tower measure, with TyConceal consuming a Λ at height
zero.  Dropping the inner conceal would terminate but is unsound: V came
from inside b and must not learn A.

SO THE LAYERING AND THE BOUNDARY-ELIMINATION FAMILY ARE COUPLED, and the
choice is not the free one I claimed:

  (A) KEEP THE LAYERING.  v3's four administrative rules return, and
      PushIntro hoists TyConceal's intro back outside the conceal.  NOTE
      THIS IS HARMLESS IN v4 — with no masks, intro-outside-conceal and
      intro-inside-conceal express the same context, so nothing is lost.
      The v4 gains (no masks, single-slot tags, anchors for identity, an
      anchor-closed rep that never needs shifting) all survive.
  (B) GO FLAT.  Needs a non-regressing rule for `ᵇ[V] •B[A]` at a conceal
      tag.  I do not have one.

Recorded as written because Jeremy asked for the flat grammar; the gap is
the thing to rule on.

# Substitution

As v3.  A boundary is TERM-CLOSED, so substitution stops at it; a
conversion is descended into.  Crossing a Λ still wraps a value image:

  crossΛ W  =  ν -X:α [ W ]        (X, α the Λ's own slot and anchor)

NOTE the shift disappears.  In v3 `crossΛ W = ν conceal (0∷[]) [ ⇑ᴹ W ]` —
the `⇑ᴹ` is there because the Λ's slot is present-but-masked in the
interior, so W's indices move.  In v4 the slot is ABSENT from the
interior, so W's context is the one it was already typed in and nothing
shifts.  **OPEN** whether that is exactly right depends on how `Δ ∖ X`
renumbers; if deletion is positional then W's indices above X do move.

# Reduction Rules

  (Beta)      Δ ⊢ (λx:A. N) · W  -→ N[x:=W : A]
  (AppConv)   Δ ⊢ V⟨c → d⟩ · W   -→ (V (W⟨c⟩))⟨d⟩
  (AppBnd)    Δ ⊢ ᵇ[V⁺] · W      -→ ᵇ[V⁺ ⁻ᵇ[W]]     if ᵇ[V⁺] is a value
  (Cancel)    Δ ⊢ V⟨-α⟩⟨+α⟩     -→ V                ← MATCHED BY ANCHOR
  (DropId)    Δ ⊢ V⟨id⟩         -→ V
  (DropConst) Δ ⊢ ᵇ[k]          -→ k
  (PrimBeta)  Δ ⊢ n₁ ⊕ n₂       -→ n₁ ⟦⊕⟧ n₂

  (TyBeta)    Δ ⊢ (ΛX.V) •B[A]  -→ ν new α:=⌊A⌋ [ V⟨+α(B)⟩ ]

  (TyConv)    Δ ⊢ V⟨∀X.c⟩ •B[A] -→ (V A)⟨c⟩

  (TyPos)     Δ ⊢ ᵖ[V⁺] •B[A]   -→ ᵖ[ ν new β:=⌊A⌋ [ (ν -Y:β [V⁺]) •B[Y]
                                                       ⟨+β(B[Y])⟩ ] ]
                                    for ᵖ ∈ { new, + }

              ← NOTE ⌊A⌋ IS NOT SHIFTED.  v3's TyPos had to lift A into
                b's interior (`shiftBy (numBindsᵇ b) A`) because the rep
                was a term type and the interior had more binders.  An
                anchor-closed rep is position-independent, so it is
                planted verbatim, at any depth.

  (TyConceal) Δ ⊢ (ν -Z:α [ΛY.V]) •B[A]
                -→ ν -Z:α [ ν new β:=⌊A⌋ [ V⟨+β(B)⟩ ] ]

              ← THE POINT OF v4, FOR ARBITRARY A.  ⌊A⌋ is computed at the
                REDEX's context, where A is well formed; it is
                anchor-closed, so planting it inside the conceal requires
                NOTHING of A's own variables to be in scope there.  The
                intro therefore sits INSIDE the conceal, where v3 forced
                it outside.  The motivating case A = Z is just the
                instance where ⌊A⌋ = α, the conceal's own anchor — and it
                is the instance that shows a term-type field could not
                work, since Z is precisely what the conceal removes.

  (CancelBnd)   Δ ⊢ ν +X:α [ν -X:α [M]] -→ M
                Δ ⊢ ν -X:α [ν +X:α [M]] -→ M     ← MATCHED BY ANCHOR

  (ξ)          as v3, with `ᵇ[M]` stepping at the interior context.

THAT IS THE WHOLE RELATION.  v3's PushConv, PushIntro, Commute,
MergeConceal, DropReveal and DropConceal are GONE — the first four exist
only to normalize a layered value grammar (§Values), and the two Drops had
empty tags to drop, which single-slot tags do not have.  `CancelBnd`
replaces nothing: it is new, and it is the one place adjacent crossings
interact, by ANCHOR IDENTITY.

SUBJECT TO §Values' OPEN GAP: if the layering is kept after all, the first
four come back.

# What this buys, and what to check first

THE TyConceal CASE, worked.  v3, at Γ, Z:

  ⁻{Z}[ΛY.V] •(Y→Y)[Z]  -→  ⁺ʸ⁼ᶻ[ (⁻{Z}[V])⟨+Y(Y→Y)⟩ ]

with the conceal's body at `Γ, locked(Z), Y=Z` — Y newer and visible, Z
older and hidden, which no prefix truncation denotes
(notes/TyConcealExample.agda).  v4:

  ν -Z:α [ΛY.V] •(Y→Y)[Z]  -→  ν -Z:α [ ν new β:=⌊Z⌋ [ V⟨+β(Y→Y)⟩ ] ]

(the instance A = Z, so ⌊A⌋ = α; the rule itself is general in A)

and the body's context is `(Δ ∖ Z), Y@β` — a DELETION followed by a PUSH.
Y is the newest scoped variable; Z is simply not there.  The body may name
Y; it may not read β's representation, because `⌈α⌉` is undefined once
Z's slot is gone — tightness, as a scope condition rather than a mask.

CHECKS, IN THE ORDER I WOULD DO THEM:

 1. RULE ON §Values' PROGRESS GAP.  Everything else depends on it: either
    a non-regressing rule for `ᵇ[V] •B[A]` at a conceal tag, or the
    layering comes back with its four administrative rules.
 2. Does `AppBnd` at a `+` tag stay well behaved?  The dual round trip
    that v3 needed `lock-unlock` for should become a DELETE-then-INSERT
    identity, which is either free or false depending on how positions
    are renumbered.
 3. Does any rule produce two scoped variables at one anchor?
 4. Does `Δ ∖ X` renumber, and if so does `crossΛ` regain a shift?
 5. Colour preservation: the annotation `κ ≡ scopeᵗ Δ` becomes just "the
    scoped context", and `scopeᵇ` should collapse to insert/delete.  Does
    `AppBnd` still have to rebuild its application node's annotation?

WHAT v4 COSTS.  Two binder families, two renamings, two transport lemmas,
and a partial read-back that every conversion rule must discharge.
Against that, it deletes: masks and the whole `unmasked`/`masked` entry
layer, the `∋lks`/`∋tvs` premises and their round-trip lemmas, the
VarSet machinery (`lockχ`, `unlockχ`, `_∖_`, `_∪_`, `scopeᵇ`, `mergeᵒ`),
`PushConv`, `PushIntro`, `Commute`, `MergeConceal`, `DropReveal`,
`DropConceal`, and the non-empty-set side conditions — the last six
CONDITIONAL on §Values' open gap.
