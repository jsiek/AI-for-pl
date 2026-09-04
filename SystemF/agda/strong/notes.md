Strong System F

This version of System F keeps tight control over where type variables
can appear and where they cannot. The name "strong" alludes to the
fact that weakening with respect to type variables is not used.

The runtime device is a single **combined boundary** `M ⟪ Θ , B₀ ⟫`: one wrapper carrying a
list Θ of reveals and conceals together with one boundary type B₀.  (An earlier design used a
separate wrapper per revealed/concealed variable, `↑[X:=A]@B` / `↓[X:=A]@B`; it is unsound —
see "Old per-variable design" and the historical Example 8 below.)

# TODO

* land **Merge** (Decision 3) and **Drop∅**; Merge discharges the two `Nested…` progress
  parameters and enables depth-1 values.
* close progress's two `RevealVar…` parameters.
* shrink what is left of `DualDef.agda`'s three parameters.  Two of the four components they
  used to bundle are now theorems (the ⋆ half of the conceal block, and the copied reps'
  well-formedness); the licensing residue is precisely a reveal whose representation names a
  blocked slot that the dual re-reveals AT KNOWLEDGE — the Pn shape, i.e. Example 8's
  run-time boundary `↑Z:=Y , ↓X:=ℕ` over an exterior that KNOWS Y.  That case was closed
  in the probes by the ambient unfold retry, which this install had to drop (§The interior
  context); recovering it means finding a retry that is stable under renaming and retagging.
* the *ambient dual* (Decision 4), the *grounded knowledge interiors + reversal-form conceal*
  (Decisions 1, 3), the *up-to-unfolding comparisons* ((a″)), the *rep-less conceal* `↓Y:⋆`
  and the *exterior-read entry* `X:=ˣA` with its licence (bwf-↓x) are SETTLED and INSTALLED —
  the notes below describe the installed semantics, not a proposal.  The design document is
  notes/DualLicenseDesign.md; the evidence is notes/InstallGauntlet.agda.

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

  Γ ::= ∅ | Γ, x:A | Γ, X | Γ, X:=A | Γ, X:=ˣA

  As before, `X` is an abstract type variable and `X:=A` a revealed one.  There is no conceal
  marker: a conceal restricts the *interior context* (below) instead of extending Γ.

  **ENTRY FORMS — the whole table.**  Four boundary entries and three context entries, and
  the two columns line up: each boundary entry says what the interior gets.

     boundary entry     read as                        interior entry it contributes
     ---------------------------------------------------------------------------------
     ↑X:=A              reveal X, external rep A       X:=⟦A⟧ if expressible, else X:=ˣA
     ↑X:⋆               reveal X, NO rep               X            (abstract)
     ↓Y:=A              conceal Y, internal rep A      — (Y is dropped)
     ↓Y:⋆               conceal Y, NO rep              — (Y is dropped, and BLOCKED)

     context entry      read as
     ---------------------------------------------------------------------------------
     X                  abstract (from ∀ / Λ)
     X:=A               revealed, A a TELESCOPE type — over the entries below X's own slot
     X:=ˣA              exterior-read: "revealed; A readable ONE LEVEL OUT; asserts nothing
                        HERE".  NOT a telescope entry — A is a type over THIS context's
                        exterior.  Minted only by the interior computation (below) and
                        consumed only by (bwf-↓x).  Ordinary knowledge lookup `Γ ∋ X:=A`
                        does NOT see it; that separation is what keeps it off the telescope
                        and out of the renaming trap.

  Both new forms are the design of notes/DualLicenseDesign.md: `↓Y:⋆` is the mirror of the
  rep-less reveal, and `X:=ˣA` is what lets a dual TRANSLATE a type mentioning a variable it
  knows nothing about — the thing E★′ (Examples) needs and `↓Y:⋆` cannot give.
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
  DEEPEST concealed variable, and the reveal variables are added on top — each carrying the
  KNOWLEDGE its representation gives:

     Γ ⇈ Θ  =  (Γ ↓ Y★) , X₁:=⟦A₁⟧ , … , X_r:=⟦A_r⟧
                                              where  Y★ = the deepest variable concealed
                                                     by Θ (if Θ conceals nothing, Γ↓Y★ = Γ)
                                                     X₁ … X_r = the reveal variables of Θ

  In words: everything from the shallowest end of Γ down to and including Y★ is dropped —
  those variables are **blocked**, they have no interior image — and the reveal variables are
  appended (so they are the shallowest interior variables, in Θ's order).

  **Knowledge entries** (Decision 1's refinement).  A reveal is NOT abstract inside: the
  interior records what the boundary knows about it.  ⟦A⟧ is the INTERIOR READING of the
  reveal's representation A — and A is a type over the PLAIN exterior (simultaneity, below),
  so the reading touches only exterior variables: concealed ones ↦ their conceal
  representations, kept ones ↦ their interior slot.  The RESULT is stored as a TELESCOPE
  entry, i.e. over the entries below X's own slot (the convention of `Γ, X:=A` everywhere
  else in these notes: A is a type over the part of the context that precedes X).  Two cases
  fall back to an ABSTRACT entry, with no knowledge:

     * A names a BLOCKED variable — its reading is not a type of the interior at all;
     * the reading names a reveal slot at or above X's own — it is then not a legal telescope
       entry (this is what makes the entry stable under renaming).  A representation cannot
       name a sibling reveal, but its READING can reach one, since a conceal's
       representation may.

  **THE FALLBACK CHAIN, exactly.**  For a REP-CARRYING reveal ↑X:=A at interior slot j:

     1.  the reading ⟦A⟧ is a legal telescope entry  ⟹  X:=⟦A⟧      (knowledge)
     2.  otherwise                                   ⟹  X:=ˣA       (exterior-read)

  and a REP-LESS reveal ↑X:⋆ contributes the abstract X.  Step 2 replaces what used to be an
  abstract entry, and that is the whole difference the licence design makes: the interior
  still learns nothing about X, but the rep is RECORDED, so a later dual can conceal X at it.

  **What is deliberately NOT here** (flagged in strong/Boundary.agda).  The probes had a
  middle step: retry the reading at the AMBIENT unfolding of A, which closes Pn (Example 11).
  It makes the interior a function of the ambient as well as the boundary, and then neither
  transport the metatheory runs on survives — renaming (the interior's entries must move with
  ρ, and unfolding does not commute with ρ) nor retagging (the interior must be MONOTONE in
  the ambient's knowledge, and it is not: a further-resolved rep may name a slot the boundary
  blocks).  Both are knowledge-WEAKENING steps the design cannot do without, since TyBeta
  turns a Λ-binder's abstract slot into a reveal's knowledge slot.  Price: Pn's dual conceal
  is unlicensed, and that case sits in DualCnc≈.

  **Rep-less reveal ↑X:⋆ and rep-less conceal ↓Y:⋆.**  Four boundary entries in all:

     Θ  ::=  ∅ | ↑X:=A , Θ | ↑X:⋆ , Θ | ↓Y:=A , Θ | ↓Y:⋆ , Θ

  `↑X:⋆` contributes an ABSTRACT interior entry, has no (bwf-↑) premise, and its slot is
  BLOCKED in the boundary-type scope (below), so no B₀ can name it — its external face is an
  arbitrary dummy that is therefore never consulted.  It is minted only by the DUAL, at a slot
  the boundary drops without concealing and which the ambient context binds ABSTRACTLY (a
  Λ-bound variable) or exterior-reads.  Under the old design that slot got a reveal at a
  fabricated representation, i.e. invented knowledge; `↑X:⋆` is the exact re-introduction.

  `↓Y:⋆` is its exact mirror: it COUNTS as a conceal (Y is dropped, so it counts in the
  interior restriction and the frame keeps its width), has NO internal image at all, and its
  slot is BLOCKED — a dummy image would be a dangling index, which is how a rep-less conceal
  differs from a rep-less reveal.  Its only premise is that the slot exists (bwf-⋆↓ below).
  It is minted only by the DUAL, for the dual of a REP-LESS reveal, where there is no rep to
  keep; the old dual invented `↓Y:=ℕ` there, which nothing licenses.

  Why knowledge, and not abstraction?  Because a conceal is licensed by the exterior's
  knowledge ((bwf-↓) below), a nested boundary inside the interior must be able to see it.
  This is the in-the-relation form of Zdancewic's global δ-consistency; without it the closed
  well-typed value `bad` (Metatheory §Progress) is stuck.

  Taking a SINGLE restriction at the deepest conceal (rather than one restriction per conceal,
  progressively) is what keeps a conceal of a shallow variable from over-dropping a deeper
  one; see the multiple-conceal example at the end of Boundary.agda.

  Blocked ≠ concealed.  A variable that Θ drops but does NOT conceal is blocked: it has no
  interior image at all, and B₀ may not name it (the scope premise of (env)).  A concealed
  variable is also absent from the interior, but B₀ *may* name it, because the internal face
  replaces it by its representation.

# The two faces of B₀

  external face   B₀[ρΘ]     read in the exterior Γ:
                             each reveal variable X ↦ its representation A **as stored** (ρ
                             is a LOOKUP, not a fold: the reveal block is read
                             SIMULTANEOUSLY, so the rep of ↑Y:=Y′ in ↑Y:=Y′ , ↑Y′:=𝔹 has
                             external face the EXTERIOR Y′, not 𝔹);
                             a rep-less reveal ↑X ↦ a dummy (never consulted);
                             every exterior variable (concealed or not) passes through.

  internal face   B₀[γΘ]     read in the interior Γ ⇈ Θ:
                             each reveal variable passes through (it IS an interior variable);
                             each concealed variable Y ↦ its representation A (read in the
                             interior, so it may itself mention reveal variables);
                             each kept exterior variable ↦ itself.

  Both faces come from one B₀, which is why (env) needs no consistency premise.

  **SIMULTANEITY** (Jeremy's ruling, notes/DECISIONS.md "RULING — telescopic (bwf-↑)
  REVERTED"), a design principle alongside tightness and no-term-shifts.  A boundary's
  entries are read all at once, each on its own side:

     (i)  a CONCEAL's representation may mention the boundary's REVEAL variables — it is an
          interior type, and the reveal variables are interior variables (this is the
          original Example-8 fix);
     (ii) a REVEAL's representation is read in the PLAIN exterior, with no interference from
          the boundary's other entries — in particular not over its siblings.

  So neither block is a telescope in the other's variables, and (ii) makes ρ a lookup.

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
  inside.  Since a conceal's premise reads back out through the WHOLE boundary, the judgement
  carries Θ as a parameter and the rules recurse on a suffix; Θ is left implicit below.

  (bwf-∅)                                                   ⟹  Γ ∣ Ψ ⊢ ∅
  (bwf-↑)   Γ ⊢ A                         Γ ∣ Ψ ⊢ Θ         ⟹  Γ ∣ Ψ ⊢ ↑X_i:=A , Θ
  (bwf-⋆)                                 Γ ∣ Ψ ⊢ Θ         ⟹  Γ ∣ Ψ ⊢ ↑X:⋆ , Θ
  (bwf-↓)   Γ ∋ Y:=A₀     A[ρΘ] ≈Δ̄⟨Γ⟩ A₀    Ψ ⊢ A
                                          Γ ∣ Ψ ⊢ Θ         ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ
  (bwf-↓x)  Γ ∋ Y:=ˣA′    A claims nothing in Θ    Ψ ⊢ A
                                          Γ ∣ Ψ ⊢ Θ         ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ
  (bwf-⋆↓)  Γ ∋ Y                         Γ ∣ Ψ ⊢ Θ         ⟹  Γ ∣ Ψ ⊢ ↓Y:⋆ , Θ

  THREE conceal-facing clauses, one per way a conceal can be licensed.

  **(bwf-↓x) — the exterior-read licence** (notes/DualLicenseDesign.md).  Y is x-revealed —
  revealed, but asserting nothing HERE — and the rep A CLAIMS NOTHING: every free variable of
  A names a REP-LESS reveal slot of Θ itself.  A rep-less reveal contributes an abstract
  entry and a blocked slot, so the interior has no knowledge about it and no boundary type can
  name it: the conceal aliases Y to a genuinely fresh abstract slot.  This is `↓Y:⋆`'s
  "claims nothing" WITH a rep attached, so the boundary type can still be TRANSLATED — which
  is exactly what E★′ needs and exactly what `↓Y:⋆` cannot give.

  The claims-nothing premise is LOAD-BEARING, not hygiene: dropping it admits an adversary
  that types `7 : ℕ` at an abstract Z, by pairing the x-entry with a NON-dual boundary
  ↑W:=ℕ , ↓Z:=W whose rep smuggles interior content in.  Machine-checked both ways in
  strong/Boundary.agda (¬starOnly-adv, ¬⊢adv) and in notes/InstallGauntlet.agda §6.

  Two deviations from notes/DualLicenseDesign.md, both flagged in the Agda:

    * the premise is stated on the BOUNDARY ("A names only rep-less reveals of Θ"), not on
      the interior ("A names only abstract variables of Ψ").  The interior form is
      ANTI-MONOTONE in knowledge, so it does not survive the retag TyBeta and TyWrap perform
      (`abst ↦ rvld` at the Λ-binder's slot).  The boundary form mentions no context at all,
      so it is retag-stable outright and renaming-stable through renᴮ; on the whole gauntlet
      it decides identically.
    * there is NO rep comparison ("A is, up to ≈Δ̄, the recorded rep A′").  §5's warning is
      real and the congruence does NOT repair it: under a weakening the x-rep moves by the
      OUTER ρ while renᴮ freezes the conceal's rep, and in the renamed interior the two are a
      genuinely abstract slot apart — so the ≈ form fails exactly where the ≡ form does
      (notes/InstallGauntlet.agda §7b).  The x-LOOKUP still does the discriminating work: a
      conceal of a plain Λ-bound abstract variable stays unlicensed.

  **(bwf-⋆↓)** asks only that the slot exist.  A rep-less conceal asserts nothing, so it
  needs nothing; that its slot is blocked is what keeps it honest.

  **(bwf-↑) is PARALLEL** (Jeremy's ruling; the earlier telescopic (bwf-↑) of Decision 4's
  residue (R1) is reverted): a reveal's representation is well formed in the PLAIN exterior Γ,
  with no interference from the boundary's other entries — simultaneity (ii) above.  Price: a
  CHAIN of knowledge (Γ = Y:=Y′ , Y′:=𝔹 , X:=ℕ dropped by ↓X:=ℕ) is no longer expressible as
  a raw copy in the dual's reveal block — but the dual's SECOND-CHANCE copy (below) unfolds
  the representation in its own tail, which collapses the chain and recovers it; the rebuild
  is then one unfolding away from Γ, which ≼≈ absorbs (Example 12).

  **(bwf-↓) is in REVERSAL FORM, UP TO ≈Δ̄** (Decision 3's ruling, relaxed by candidate
  (a″)): a conceal's representation A, READ BACK OUT through the boundary (reveal variables ↦
  their external faces, kept interior variables ↦ their exterior index), must be the
  exterior's own knowledge about Y — up to the unfolding congruence (below).
  Comparing on the OUTSIDE, rather than transporting the knowledge inwards, is what lets the
  boundary's own reveals be UNFOLDED — which is Zdancewic's (trans) / Δ̄ and is what Merge
  needs.  It also transports under any monotone renaming with no scope restriction, unlike
  the interior comparison.

  Consequences.  `bad` and `bad₂` (Metatheory §Progress) are ill typed; a conceal is
  licensed only against real knowledge, so a Λ-bound variable can never be concealed.

# The unfolding congruence   A ≈Δ̄⟨Γ⟩ B

  Knowledge entries are kept RAW — a reveal's representation is stored as written, so the
  external face and the interior entry agree — and instead every KNOWLEDGE COMPARISON is
  taken up to unfolding.  This is candidate (a″); it is what makes the dual's rebuild
  usable, since the rebuild differs from the original context by exactly an unfolding.

     Δ̄(Γ) A          Zdancewic's Δ̄ applied to A: every revealed variable of Γ replaced by
                     its (recursively unfolded) representation.  The recursion is on the
                     CONTEXT — `X:=B` stores B over its own TAIL — so it is well founded for
                     free.  ABSTRACT and EXTERIOR-READ slots are left alone: an x-entry's rep
                     lives one level out, so it is not a type this context can resolve.

     A ≈Δ̄⟨Γ⟩ B      Δ̄(Γ) A = Δ̄(Γ) B, i.e. the two types have the same unfolding in Γ.

  It is the PROPOSITIONAL EQUALITY of unfoldings, not an inductive congruence: equivalence
  and the ⇒ / ∀ congruence rules are then theorems rather than constructors, every witness is
  refl-checkable, and every refutation is a one-line absurd pattern on two closed normal
  forms.

  Two properties carry the metatheory:

    * MONOTONICITY.  If Γ′ resolves at least what Γ resolves, the same way, then every ≈ at
      Γ is an ≈ at Γ′.  The retag ordering (below) supplies exactly that.
    * RENAMING.  The OPERATOR Δ̄ does NOT commute with renaming under the hypotheses the
      renaming lemma carries — an abstract slot may land on a revealed one, and unfolding
      notices.  The CONGRUENCE transports with strictly less, in ABSORBED form, and THAT
      follows from the knowledge-transport hypothesis the renaming lemma already has:
      every slot either unfolds to itself (abstract, exterior-read, out of range), making
      the equation an identity, or is knowledge, and then its renamed representation is read
      in the slot's own PREFIX.  So the congruence needs NO new top-level hypothesis, which
      is what ruling (ii) of notes/DualLicenseDesign.md §5 hoped for.

  Three comparisons are taken up to ≈Δ̄: (bwf-↓)'s reversal premise, the retag ordering
  Γ ≼≈ Γ′, and the dual's three laws (DualRep≈ / DualCnc≈ / DualInt≈).

# Retagging   Γ ≼≈ Γ′

  Typing READS the entry flavour, so a derivation transports along an ORDERING of contexts,
  not along equal length.  Entrywise:

     X       ≼≈  anything          (a Λ-binder's slot becoming a reveal's knowledge slot is
                                    exactly this step — TyBeta, TyWrap)
     X:=ˣA   ≼≈  X:=ˣA             the mark is PRESERVED: its whole content is "revealed, but
                                    I know nothing here", which a richer context does not
                                    satisfy, so it may not be traded for knowledge.  That is
                                    what keeps (bwf-↓x) transportable — and what keeps `bad`
                                    refuted, since a conceal of a KNOWN slot must not become
                                    x-licensable.
     X:=A    ≼≈  X:=B              when A ≈Δ̄⟨Γ′↓X⟩ B — knowledge up to unfolding, which is
                                    what the dual's rebuild delivers when it collapses a
                                    chain (Example 12)

  Syntactic equality of entries orders the chained context and its rebuild in NEITHER
  direction; ≼≈ orders them both ways.  That is the whole content of the relaxation.

# Boundary-type scope   Θ ; Γ ⊢ᵒᵏ B₀

  B₀ is well-scoped over the boundary frame when it names no BLOCKED variable: reveal
  variables WITH a representation are fine, kept exterior variables are fine, concealed
  exterior variables are fine (the internal face resolves them), and a
  dropped-but-not-concealed variable is not — nor is a REP-LESS reveal ↑X:⋆, whose external
  face is a dummy, nor a REP-LESSLY concealed variable ↓Y:⋆, which has no internal image.
  Structural, with ∀-bound variables always accessible:

  (sc-var)  X is a reveal variable with a rep, a kept variable, or a concealed variable
                                                                             ⟹ Θ;Γ ⊢ᵒᵏ X
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

  Reduction is **knowledge-indexed**: the judgement is `Γ ⊢ M -→ M′`, where Γ is the type
  context in which the redex sits — the very Γ that types it.  Only Wrap consults it, to
  build the dual; the ξ rules carry it into the sub-term's own context.  V, W range over
  values; TyWrap's wrapped term is ΛY.V with V a value, and Wrap's is a λ.

  (δ)       Γ ⊢ n₁ ⊕ n₂                   -→ n                if n = n₁ ⟦⊕⟧ n₂
  (Beta)    Γ ⊢ (λx:A. N) · W             -→ N[x:=W]
  (TyBeta)  Γ ⊢ (ΛX. V) @B[A]             -→ V ⟪ ↑X:=A , B ⟫
  (TyWrap)  Γ ⊢ ((ΛY.V) ⟪ Θ , ∀Y.B₀ ⟫) @B[A]
                                          -→ V ⟪ ↑Y:=A , Θ , B₀ ⟫
  (Wrap)    Γ ⊢ ((λx:B₁[γΘ]. N) ⟪ Θ , B₁→B₂ ⟫) · W
                                          -→ N[x := W ⟪ Θᵈ(Γ) , B₁ ⟫] ⟪ Θ , B₂ ⟫
  (ξ-·-l)   Γ ⊢ L -→ L′                   ⟹  Γ ⊢ L · M   -→ L′ · M
  (ξ-·-r)   Γ ⊢ M -→ M′                   ⟹  Γ ⊢ V · M   -→ V · M′
  (ξ-@)     Γ ⊢ L -→ L′                   ⟹  Γ ⊢ L @B[A] -→ L′ @B[A]
  (ξ-Λ)     Γ, X ⊢ N -→ N′                ⟹  Γ ⊢ ΛX.N    -→ ΛX.N′
  (ξ-⟪⟫)    Γ⇈Θ ⊢ M -→ M′                 ⟹  Γ ⊢ M ⟪ Θ , B₀ ⟫ -→ M′ ⟪ Θ , B₀ ⟫
  (Cancel)  Γ ⊢ (V ⟪ ↓X:=A , B₀ ⟫) ⟪ ↑X:=A′ , B₀′ ⟫  -→ V     if A = A′    [OPTIONAL]
  (Drop)    Γ ⊢ V ⟪ ↑X:=A , Θ , B₀ ⟫      -→ V ⟪ Θ , B₀ ⟫     if X ∉ B₀, X ∉ V,
                                                              X ∉ the reps of Θ  [OPTIONAL]
  (Drop∅)   Γ ⊢ V ⟪ ∅ , B₀ ⟫              -→ V                             [OPTIONAL]

  In TyWrap the type argument A is recorded VERBATIM as the new reveal's representation: a
  reveal's rep is read in the plain exterior (simultaneity (ii)), where A already lives, so
  its external face is A and the rule's result type is unchanged.  There is no rep lift —
  the earlier `A↑` (A shifted past Θ's existing reveal slots) was forced only by the
  reverted telescopic (bwf-↑).  In Θᵈ(Γ) the ambient Γ is the dual's second argument
  (below).

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

  Θᵈ(Γ) is the AMBIENT DUAL boundary (Decision 4): it is read from the interior's point of
  view, so every arrow flips, and it takes the ambient context Γ as a second argument.

     each  ↑X:=A  of Θ  becomes  ↓X:=A  of Θᵈ      (X was interior to Θ, so it is exterior to
                                                    Θᵈ; the rep is X's EXTERNAL FACE, which
                                                    under the parallel reading IS A — a
                                                    Γ-type, i.e. a Θᵈ-interior type, exactly
                                                    a conceal rep's home)
     each  ↑X:⋆   of Θ  becomes  ↓X:⋆   of Θᵈ      (there is no rep to keep; the old dual
                                                    invented ↓X:=ℕ here, which nothing
                                                    licenses)
     each  ↓Y:=A  of Θ  becomes  ↑Y:=A  of Θᵈ      (Y's slot is rebuilt as a fresh interior
                                                    variable of Θᵈ; A was interior to Θ, i.e.
                                                    exterior to Θᵈ — a reveal rep's home)
     each BLOCKED slot i    becomes  Γ's OWN ENTRY at i:
                                     Γ has i:=B  ⟹  ↑i:=B  of Θᵈ if B names no other dropped
                                                    slot; ELSE ↑i:=Δ̄(Γ↓i) B if THAT names
                                                    none — the SECOND-CHANCE copy, which
                                                    collapses a CHAIN; else ↑i:⋆
                                     Γ has i     ⟹  ↑i:⋆   of Θᵈ  (rep-less)
                                     Γ has i:=ˣB ⟹  ↑i:⋆   of Θᵈ  (B lives one level further
                                                    out than the dual's exterior)

  The CONCEAL block is ENTRY-INDEPENDENT: every rep-carrying reveal is concealed at its
  stored rep, and the licence comes from whichever clause the interior supports — (bwf-↓)
  when it has ordinary knowledge of the slot, (bwf-↓x) when it only x-knows it.  Only a
  rep-LESS reveal is treated differently, and that is forced: there is nothing to conceal at.

  The SECOND-CHANCE copy is what recovers Pc's chained knowledge (Example 12): the raw copy's
  guard refuses a rep naming another dropped slot, and unfolding the rep in its own tail
  collapses the chain to something the dual's plain exterior can express.  The rebuild is
  then one unfolding away from Γ — which is exactly what ≼≈ absorbs.

  The third clause is the point of the ambient dual.  A variable that Θ drops but does not
  conceal is blocked, and the OLD dual gave it a fabricated representation (ℕ) — which loses
  the knowledge Γ held about it and breaks preservation as soon as the argument W uses that
  knowledge (Decision 4's programs P and E, Examples 9 and 10 below).  Copying Γ's entry
  loses nothing and invents nothing: a Λ-bound slot comes back ABSTRACT, via the rep-less
  reveal.  No term traversal, no insertion, and every step stays local — which is why
  reduction is indexed by Γ at all.

  The fabricated rep is still what a blocked slot's EXTERNAL face would need, so Wrap's
  preservation still goes through the scope-restricted congruence (`subst-cong-sc`) with
  (env)'s scope premise for B₁, not a pointwise identity of the two faces.

  Still open at Wrap, and now precisely: the dual's conceal of a rep-carrying reveal needs
  ONE of the two licences, and neither is available when the reveal's rep names a blocked
  slot that the dual re-reveals AT KNOWLEDGE (the Pn shape: the interior x-knows Z, but the
  rep names ↑Y:=ℕ, which claims something).  The ⋆ half of the conceal block is a THEOREM
  (every reveal slot exists in the interior, whatever entry it carries), the copied reps'
  well-formedness is a theorem given the rebuild law, and the rebuild law's own residue is a
  slot whose copy BOTH guards refuse plus an exterior-read slot, which the dual re-reveals
  rep-lessly.  See `DualDef.agda` for the three statements and exactly what is proven.

  De Bruijn remark.  The boundary frame of Θᵈ is Θ's frame with the reveal block and the
  dropped block interchanged, so B₁ is renamed by that block swap (`swapᵇ`).  Named notation
  hides this: B₁ is the same type, read on the other side.  The substitution N[x := …] is
  `_[_]ᵐ`, which is the identity on wrappers (a boundary body is term-closed), so the
  argument's own boundaries are never descended into.

## ξ — congruences

  Call-by-value, left to right; also under a Λ and under a boundary.  The last two are not
  bookkeeping: `ΛX.N` is a value only when N is, and `M ⟪ Θ , B₀ ⟫` only when M is, so both
  bodies must be reduced in place.  In the Agda these are five constructors ξ-·-l, ξ-·-r,
  ξ-·[], ξ-Λ, ξ-⟪⟫; ξ-⟪⟫ recurses at the INTERIOR context and ξ-Λ at `Γ, X`, which is why
  preservation and progress are generalised over Γ rather than fixed at ∅ — and, now that
  reduction itself is Γ-indexed, those two rules EXTEND the index by exactly the context the
  corresponding typing rule extends by, so the two judgements stay in step.

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
entry-level definition is Decision 3's (notes/old/MergeProbe.agda), not fixed here.

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
  notes/old/Example8Trace.agda; the labels T0…T5, T4′ are that file's (a historical record of the
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

  **[R2]** T4′'s boundary ↑Z:=Y , ↓X:=ℕ is exactly the still-open residue: Z's representation
  Y names a slot the SAME boundary blocks, so Z's interior entry is ABSTRACT, and if that
  wrapper is ever the function of an application its dual's conceal ↓Z:=Y has no knowledge to
  meet.  Here it never is (T4′ is a value of ∀-type whose next elimination is a type
  application, which TyWrap handles), but nothing rules the shape out in general.

## Example 9   (blocked KNOWLEDGE — what forced the ambient dual)

  Decision 4's program.  Two Λ-bound variables become REVEALED while a sealed value sits
  under them, so the sealed boundary blocks slots that carry knowledge.

  P = (ΛX. λf:(X→X). ΛY. λw:X. f w) [ℕ] · (λn:ℕ. n) [𝔹] · 3                          : ℕ

  → TyBeta   ((λf. ΛY. λw. f w) ⟪ ↑X:=ℕ , (X→X)→∀Y.X→X ⟫) · (λn.n) [𝔹] · 3
  → Wrap     ((ΛY. λw. f′ w) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫) [𝔹] · 3      f′ = (λn:ℕ.n)⟪↓X:=ℕ,X→X⟫
  → TyWrap   ((λw:X. f′ w) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X→X ⟫) · 3      interior Y′:=𝔹 , X:=ℕ
  → Wrap     (f′ · W₁) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X ⟫                 W₁ = 3 ⟪ ↓Y′:=𝔹 , ↓X:=ℕ , X ⟫
  → Wrap     ((λn:ℕ.n) · (W₁ ⟪ Θᵈ , X ⟫)) ⟪ ↓X:=ℕ , X ⟫ ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X ⟫

  At the last step the sealed f′ meets an argument, at ambient Γ = Y′:=𝔹 , X:=ℕ.  Its
  boundary ↓X:=ℕ BLOCKS Y′, and W₁ uses Y′'s knowledge (its outer conceal is ↓Y′:=𝔹).  The
  old dual re-introduced Y′ at the fabricated ℕ, so W₁ did not retype and preservation broke.
  The ambient dual copies Γ's entry — Θᵈ = ↑Y′:=𝔹 , ↑X:=ℕ, interior Y′:=𝔹 , X:=ℕ = Γ on the
  nose — and W₁ retypes unchanged.

## Example 10   (why a term traversal will not do)

  Decision 4's forcing example: a type abstraction sits BETWEEN the ΛY and the sealed value,
  and is evaluated under the Λ before Y's TyWrap can fire.  A "push the knowledge down into
  the term" repair (option W3) would have to CROSS it, and iterating the gadget makes the
  crossing depth unbounded.

  E = (ΛX. λf:(X→X). ΛY. (ΛZ. λz:X. f z) [ℕ]) [ℕ] · (λn:ℕ. n) [𝔹] · 3               : ℕ

  → TyBeta ; Wrap ; ξ-Λ TyBeta
             ((ΛY. ((λz:X. f′ z) ⟪ ↑Z:=ℕ , X→X ⟫)) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫) [𝔹] · 3
                                                            f′ = (λn:ℕ.n)⟪↓X:=ℕ,X→X⟫
  → TyWrap   ((λz:X. f′ z) ⟪ ↑Z:=ℕ , X→X ⟫) ⟪ ↑Y:=𝔹 , ↑X:=ℕ , X→X ⟫ · 3
  → Merge [D3] ; Wrap  …                                     ambient Γ = Z:=ℕ , Y:=𝔹 , X:=ℕ
  → Wrap     the sealed f′ (boundary still the PLAIN ↓X:=ℕ) meets its argument at that Γ,
             blocking BOTH Z and Y, both of which carry knowledge

  With the ambient dual the sealed boundary is never touched — it stays ↓X:=ℕ for its whole
  life — and both knowledge entries are copied at the moment of use.  Zero traversal.

## Example 11   (E★′ — the counterexample the LICENCE design closes)

  The supervisor's E★′.  The Pn shape (Example 8's run-time boundary ↑Z:=Y , ↓X:=ℕ) with ONE
  change: the instantiated ∀-body MENTIONS its own variable, so the failing Wrap must move a
  value whose type NAMES the reveal Z.  A rep-less conceal cannot do that (a re-hidden slot
  is blocked, so the dual cannot even carry the boundary type), and a rep-keeping conceal was
  unlicensed — which is what forced the exterior-read entry.

  E★′ = (ΛX. λf:(∀Z.(Z→ℕ)→(Z→ℕ)). ΛY. (f [Y]) (λy:Y. 5)) [ℕ]
          · (ΛZ. λg:(Z→ℕ). λz:Z. g z)                          : ∀Y. Y→ℕ

  → TyBeta   (λf. ΛY. …) ⟪ ↑X:=ℕ , (∀Z.(Z→ℕ)→(Z→ℕ)) → ∀Y.Y→ℕ ⟫ · (ΛZ. …)
  → Wrap     (ΛY. ((g′ [Y]) (λy:Y. 5))) ⟪ ↑X:=ℕ , ∀Y.Y→ℕ ⟫
                                       g′ = (ΛZ. …) ⟪ ↓X:=ℕ , ∀Z.(Z→ℕ)→(Z→ℕ) ⟫
  → ξ⟪⟫ ξΛ TyWrap                                        ambient Γ★ = Y , X:=ℕ
             (ΛY. ((λg. λz. g z) ⟪ ↑Z:=Y , ↓X:=ℕ , (Z→ℕ)→(Z→ℕ) ⟫) (λy:Y. 5))
             ⟪ ↑X:=ℕ , ∀Y.Y→ℕ ⟫
  → ξ⟪⟫ ξΛ Wrap
             (ΛY. (λz:Z. W′ z) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→ℕ ⟫) ⟪ ↑X:=ℕ , ∀Y.Y→ℕ ⟫
                                       W′ = (λy:Y. 5) ⟪ ↑Y:⋆ , ↑X:=ℕ , ↓Z:=Y , Z→ℕ ⟫

  At the TyWrap step the knowledge "Z is Y" is inexpressible in the interior (Y is blocked by
  ↓X) and un-unfoldable (Y is Λ-bound), so Z's entry is the EXTERIOR-READ  Z:=ˣY  — the
  interior learns nothing, but the rep is recorded.  The final Wrap's dual is

     ↑Y:⋆ , ↑X:=ℕ , ↓Z:=Y

  and its conceal of Z is licensed by (bwf-↓x): Z is x-revealed, and the rep Y names the
  dual's OWN rep-less reveal ↑Y:⋆, so it claims nothing.  Both faces were already exactly
  right; only the licence was missing.  The dual's interior rebuilds Γ★ on the nose, and
  dualising the dual round-trips exactly (with ↓Y:⋆ where the rep-less reveal has to be
  re-hidden — the one place ↓·:⋆ is indispensable).

  Machine-checked end to end, against the live rules, in notes/InstallGauntlet.agda §1.

## Example 12   (Pc — the chained dual, recovered by the second-chance copy)

  Γq = W:=Y , Y:=ℕ , X:=ℕ is reachable (TyBeta turns a Λ-bound Y into W:=Y without renaming)
  and the seal ↓X:=ℕ drops all three.  W's entry is the CHAIN "W is Y", and the seal drops Y
  too, so the dual's RAW copy of W is refused: its rep names another dropped slot, which the
  dual's plain exterior cannot express.  That knowledge used to be LOST to ↑W:⋆.

  The dual now retries at Δ̄(Γq↓W) Y = ℕ, which the exterior CAN express, so all three slots
  come back with knowledge and the rebuild is  W:=ℕ , Y:=ℕ , X:=ℕ  — Γq up to exactly one
  unfolding.  Syntactic equality of entries orders the two contexts in neither direction; ≼≈
  orders them, and the argument's own ↓W:=Y conceal — whose read-back is the raw variable Y
  while the rebuilt knowledge is ℕ — retypes because (bwf-↓) is up to ≈Δ̄.  That single site
  is what the whole congruence exists for (notes/InstallGauntlet.agda §5).

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
  Only two operations touch the interior: TyWrap grows it by one variable — the slot the
  consumed Λ used to bind, which becomes the new reveal's KNOWLEDGE slot — so conceal reps,
  which live over the whole interior, shift, while reveal reps do not; and moving a wrapper
  under a Λ grows the EXTERIOR by one (so conceal indices shift; in named notation, nothing).
  Everything else leaves Γ⇈Θ alone; in particular (env)'s premises mention only Θ and B₀, so
  ξ-⟪⟫ carries them across unchanged.
  Note that no rule shifts a TERM: TyWrap's contractum is the Λ-body exactly as it stood, and
  Wrap's is a term-variable substitution.  The only TYPES that move are the conceal reps
  (`shiftReps`); with the parallel (bwf-↑) even TyWrap's type argument is recorded
  unshifted.

Supporting lemmas.
  (L1) Term substitution.  If Γ, x:A, Θ ⊢ N : B and Γ ⊢ V : A (V a value), then
       Γ, Θ ⊢ N[x:=V] : B.  The boundary case is the identity: a boundary body is typed with
       an empty term context, so x ∉ M.  The Λ case needs type-variable renaming (below) at
       the weakening ρ = suc.  Beta uses Θ = ∅.
  (L2) Type-variable renaming.  If Γ ⊢ M : A and ρ : Γ → Γ′ preserves lookup, IS MONOTONE,
       and TRANSPORTS KNOWLEDGE (Γ ∋ X:=A₀ ⟹ Γ′ ∋ ρX:=ρ↓A₀, where ρ↓ is the renaming ρ
       induces on X's prefix), then Γ′ ⊢ ρM : ρA.  The third premise is new with the
       reversal-form (bwf-↓), which reads the exterior's knowledge; it holds at the weakening
       ρ = suc (the induced prefix renaming is the identity) and extends under a Λ.  The
       boundary case must then also show that the INTERIOR's knowledge entries ⟦A⟧ transport,
       which is where the two guards on ⟦·⟧ earn their keep.
       Monotonicity is not a convenience: the interior of a boundary is
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
       Θ;Γ ⊢ᵒᵏ B₀ is discharged in the cases where no reduction rule supplies it.  With the
       parallel (bwf-↑) the "external face is well formed" step is a plain LOOKUP into
       (bwf-↑)'s own premise (it was a substitution lemma while the face was a fold).
  (L-≼≈) Retagging along KNOWLEDGE GROWTH, up to unfolding.  Γ ≼≈ Γ′ is the ordering of
       §Retagging above; then Γ ⊢ M : A ⟹ Γ′ ⊢ M : A.  Typing READS the entry flavour (a
       conceal is licensed by knowledge, or by the exterior-read mark), so it no longer
       transports along a context of the same LENGTH — ≼≈ is the replacement.  Used three
       times: TyBeta and TyWrap turn the consumed Λ's ABSTRACT slot into the new reveal's
       entry, and Wrap retypes the argument in the dual's rebuild of Γ.  Its two interesting
       clauses: (bwf-↓)'s reversal premise moves by MONOTONICITY of ≈Δ̄ composed with the
       target's own knowledge witness, and (bwf-↓x) moves because its two premises are the
       x-LOOKUP (which ≼≈ preserves by construction) and a claims-nothing condition that
       mentions no context at all.  The interior's monotonicity —
       Γ ≼≈ Γ′ ⟹ Γ⇈Θ ≼≈ Γ′⇈Θ — holds ON THE NOSE, because the interior computation consults
       the BOUNDARY alone; that is why the ambient unfold retry had to go, not this lemma.

  Inversion of (env): from Γ ⊢ M ⟪ Θ , B₀ ⟫ : C we get Γ ∣ (Γ⇈Θ) ⊢ Θ, Θ;Γ ⊢ᵒᵏ B₀,
  Γ⇈Θ ⊢ M : B₀[γΘ], and C = B₀[ρΘ].

## Preservation

Γ ⊢ M : A  (Γ runtime)  and  Γ ⊢ M -→ M′   ⟹   Γ ⊢ M′ : A.

The SAME Γ indexes both judgements — which is exactly why ξ-Λ and ξ-⟪⟫ had to extend the
reduction's index by the context the corresponding typing rule extends by.

Proved in the Agda (BPreservation.agda) for every rule: Beta, TyBeta, TyWrap, Wrap and the
five ξ congruences.  Wrap's case is proved MODULO three statements about the ambient dual
(DualDef.agda); everything else — including both of Wrap's face laws, the renaming lemma with
its exterior-read transport, and the retagging lemma — is unconditional.

  What the licence install changed in the three dual statements.  Their SHAPES are now up to
  ≈Δ̄ (DualRep≈ / DualCnc≈ / DualInt≈), and two of their four former components became
  theorems: the ⋆ half of the conceal block (every reveal slot exists in the interior,
  whatever entry it carries) and the copied reps' well-formedness in the dual's interior
  (which follows from the rebuild law).  DualCnc≈ is now a per-reveal DISJUNCTION — ordinary
  knowledge with the read-back up to ≈, or the exterior-read mark with the claims-nothing
  premise — and the residue is exactly where neither disjunct holds: a reveal whose rep names
  a blocked slot that the dual re-reveals AT KNOWLEDGE (the Pn shape).  Wrap's INTERNAL face
  law also became scope-restricted, like the external one, because a rep-lessly concealed slot
  has no internal image; (L-sc) with (env)'s premise on B₁ covers exactly the difference.

  Beta.       (L1).  Substitution is the identity on boundaries (their bodies are term-closed),
              and the Λ case of the substitution lemma is (L2) at ρ = suc, whose monotonicity
              premise is immediate.  This is the only case where a term variable appears.
  TyBeta.     Inversion of (tapp) and (tlam): Γ, X ⊢ V : B and Γ ⊢ A, result B[X:=A].  The
              new boundary is ↑X:=A: (bwf-↑) from Γ ⊢ A; the interior is Γ, X:=⟦A⟧, where V
              is typed by (L-≼) from Γ, X (abstract ≼ knowledge — the ONLY thing that
              changes with the knowledge interiors); the internal face of B is B itself
              (a reveal variable passes
              through γ) and the external face is B[X:=A] — the two face equations.  The scope
              premise Θ;Γ ⊢ᵒᵏ B is not supplied by the rule and is discharged by (L-wf) from
              the typing of V.  This is the case that makes preservation need the wf/scope
              bridge at all.
  TyWrap.     Inversion of (tapp) and (env): the wrapper's external face is ∀-shaped, so
              B₀ = ∀Y.B₀′ and the redex's annotation B is FORCED to be the ∀-body of the
              external face.  Inverting (tlam) on the (env) body premise — whose type is the
              internal face ∀Y.(B₀′[γΘ]) — gives the Λ-body typed at Γ⇈Θ, Y with the internal
              face of B₀′.  That is ALREADY the contractum's interior (up to (L-≼): the Λ's
              abstract slot becomes the new reveal's knowledge slot) and interior face, so
              the body is transported by (L-≼) and two equations and nothing renames it.
              The type argument is recorded UNCHANGED as the new reveal's rep, licensed
              directly by the redex's Γ ⊢ A (no lift, hence no weakening).  Four face
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
              at the term context x:B₁[γΘ].  The ambient dual Θᵈ(Γ) has the wrapper's
              interior as its exterior and rebuilds Γ as its interior, so W ⟪ Θᵈ , B₁ ⟫ types
              at the interior with internal face B₁[γΘ] — exactly the annotation.  The two
              faces of B₁ under Θᵈ are the two faces under Θ with the sides exchanged, EXCEPT
              at blocked slots, where the re-introduced entry makes them differ; (L-sc) with
              the scope premise on B₁ makes that difference irrelevant.  BOTH face laws are
              theorems.  Then (L1) at that argument, and (env) at B₂.

              THREE facts about the dual are NOT proved and are the module parameters of
              `DualDef.agda` (the repo's `…Def` convention):

                DualRep — every re-introduced KNOWLEDGE rep is well formed in the dual's
                          EXTERIOR.  This is a fact about the well-formedness of Γ itself,
                          which the preservation statement does not carry; the CONCEALED and
                          the Λ-BOUND slots of the reveal block ARE proved (dual-rep-conc and
                          the rep-less reveal's absent premise), and `bwf-dualᴳ` assembles
                          the whole reveal block from this one gap.  With the parallel
                          (bwf-↑) the copy is GUARDED: a CHAINED rep (one naming another slot
                          the boundary drops) is not expressible in the plain exterior, so
                          the dual emits ↑Y there instead — DualRep assumes the guard, and
                          the knowledge the guard drops surfaces in DualInt.
                DualCnc — the dual's CONCEAL block: Θ's interior knows each reveal variable,
                          and Θ's external face for it reads back to that knowledge.  This is
                          the [R2] residue: false exactly when a reveal's rep names a slot
                          the same boundary blocks (Example 8's T4′).
                DualInt — the rebuild law, Γ ≼ (Γ⇈Θ)⇈Θᵈ.  Its Λ-bound and abstract slots are
                          exact by construction; the others need the same round trip as
                          DualCnc, one level out — plus, since the parallel revert, the
                          chained slots the copy guard refuses (BReduction's Γp).  One
                          knowledge-closure operator — candidate (a) — would serve both the
                          interior entries ⟦·⟧ and the dual's copied reps.
  ξ.          One induction hypothesis under the corresponding typing rule.  Two change
              context: under Λ the IH is at Γ,X (the term context stays empty), and under a
              boundary the IH is at the INTERIOR Γ⇈Θ — a different context, which is why the
              statement must be generalised over Γ.  The (env) premises mention only Θ and B₀
              and are carried across intact.
  Cancel/Drop.  Not in the Agda.  Drop∅ is immediate (both faces of an empty boundary are B₀);
              Cancel needs the two reps to agree, and is unsound otherwise (next section).

## Progress

Γ ⊢ M : A  (Γ runtime, empty term context)   ⟹   M is a value  or  Γ ⊢ M -→ M′.

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

  THE OBSTRUCTION THAT WAS — rep inconsistency (notes/BoundaryRules.md §4), now CLOSED.
  The old (env) recorded one B₀ per wrapper and derived both faces, but could not relate a
  conceal ↓X:=A to the rep of the REVEAL that binds X — that reveal lives on an ENCLOSING
  wrapper, so no local premise saw it.  Hence the closed, well-typed value

     bad  =  (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=(∀Z.Z→Z) , X ⟫        :  ∀Z.Z→Z

  whose entire content is the numeral 7: the outer boundary revealed X at ∀Z.Z→Z while the
  inner concealed it at the INCONSISTENT ℕ, and `bad @(Z→Z)[ℕ] : ℕ→ℕ` was well typed, not a
  Λ, with a variable B₀ — stuck.

  This is what the KNOWLEDGE INTERIORS plus the REVERSAL-FORM (bwf-↓) fix, in the relation
  and not by a companion predicate: the outer reveal puts X:=⟦∀Z.Z→Z⟧ into the interior, and
  the inner conceal must read its rep BACK OUT to exactly that.  ℕ does not, so `bad` is
  ill typed — machine-checked in Boundary.agda (`¬⊢bad`), together with the subtler `bad₂`,
  which the untransported comparison still admitted.  A conceal is now licensed only against
  real knowledge, so a Λ-bound variable can never be concealed at all.

  WHAT REMAINS OPEN in progress.  Four cases, all module parameters of ProgressDef.agda,
  none of them the old inconsistency:

    RevealVarApp / RevealVarTApp — the wrapper's B₀ is a REVEAL VARIABLE.  Its external face
      is that reveal's rep, which can be ⇒- or ∀-shaped, so the term IS at an elimination;
      what fires is a Merge or a Cancel against the enclosing boundary.
    NestedApp / NestedTApp — a WRAPPER-bodied wrapper at a ⇒ / ∀ face.  Merge (Decision 3)
      discharges both uniformly.

  So progress reduces to Merge, and Merge to "retyping along unfolding" (Zdancewic's Δ̄) —
  which the reversal form was chosen to make possible.

# Correspondence with the Agda   (SystemF/agda/strong/)

  Jeremy's rule: the Agda constructor names follow the names in these notes.

  notes                      Agda                                       file
  -------------------------  -----------------------------------------  --------------
  M ⟪ Θ , B₀ ⟫               _⟪_,_⟫                                     Boundary.agda
  ↑X:=A                      rvl A                                      Boundary.agda
  ↑X:⋆     (rep-less)        rvl⋆                                       Boundary.agda
  ↓Y:=A                      cnc Y A                                    Boundary.agda
  ↓Y:⋆     (rep-less)        cnc⋆ Y                                     Boundary.agda
  X  (abstract entry)        abst                                       Context.agda
  X:=A  (knowledge entry)    rvld A                                     Context.agda
  X:=ˣA (exterior-read)      xrvld A                                    Context.agda
  Γ ∋ X:=ˣA                  _∋_:=x_  (herex, skipx)                    Context.agda
  Θ                          BCtx = List BEntry                         Boundary.agda
  Γ ⇈ Θ  (interior)          intOf Δ Θ = revEnts Θ 0 Θ ++ dropN (cmax Θ) Δ
  the fallback chain         ⟦_⟧ᴴ  (raw ⇒ rvld, else xrvld; guards       Boundary.agda
                               bfree / dfree via expr; rawRead, dnT)
  Δ̄(Γ) A  (unfolding)        unfoldᵉ Γ A  (unfSub, context-recursive)    Unfold.agda
  A ≈Δ̄⟨Γ⟩ B                  _≈Δ̄⟨_⟩_  (≈unf; ≈-refl/sym/trans, ≈-⇒/∀)   Unfold.agda
  ≈ monotone / renaming      ≈-mono (Absorbs), ≈-ren (UnfRen≈)          Unfold.agda
  Γ ↓ X  (prefix)            _↓_                                        Context.agda
  B₀[γΘ] (internal face)     substᵗ (γᵇ Θ) B₀                           Boundary.agda
  B₀[ρΘ] (external face)     substᵗ (ρᵇ Θ) B₀   (a LOOKUP: parallel)    Boundary.agda
  A[ρΘ] ≈Δ̄⟨Γ⟩ A₀ (reversal)  Reversal≈ Γ Θ X A A₀
                               = outRead Θ A ≈Δ̄⟨ Γ ⟩ upRep X A₀         Boundary.agda
  A claims nothing in Θ      starOnly Θ 0 A ≡ true  (revStar)           Boundary.agda
  Θ;Γ ⊢ᵒᵏ B₀ (scoped)        Scoped (baseS Θ Δ) B₀                      Boundary.agda
  Γ ∣ Ψ ⊢ Θ                  _∣_⊢ᵇ_  (bwf[], bwf↑, bwf⋆, bwf↓,          Boundary.agda
                               bwf↓x, bwf⋆↓)
  (env)                      env                                        Boundary.agda
  L @B[A]                    L ·[ B , A ]        (⊢·[])                 Boundary.agda
  Γ ⊢ M -→ M′                _⊢_-→_                                     BReduction.agda
  Beta                       Beta                                       BReduction.agda
  TyBeta                     TyBeta                                     BReduction.agda
  TyWrap  (A unlifted)       TyWrap   (R1)                              BReduction.agda
  Wrap                       Wrap     (R2)                              BReduction.agda
  Merge                      — not yet a rule; the four open progress   ProgressDef.agda
                               cases are its module parameters
  ξ                          ξ-·-l, ξ-·-r, ξ-·[], ξ-Λ, ξ-⟪⟫             BReduction.agda
  Cancel / Drop              — not in the Agda (optional; see above)
  Θᵈ(Γ)  (ambient dual)      dualᴳ Δ Θ / entᴳ / swapᵇ Θ                 BReduction.agda
  second-chance copy         entᴳ's `unfEnt Γ i B` retry                BReduction.agda
  entry-independent conceal  cncOfRevs (rvl ↦ cnc, rvl⋆ ↦ cnc⋆)         BReduction.agda
  dual face laws             ρᵇ-dual-ty, γᵇ-dual-ty (both now           BReduction.agda
                               scope-restricted), sc-dual
  dual well-formedness       bwf-dualᴳ / bwf-dual + DualRep≈,           DualDef.agda
                               DualCnc≈ (CncLic), DualInt≈; the proven
                               parts: cnc⋆-licensed, revE-lo:=x,
                               dual-rep-ok
  L2 (monotone renaming)     ⊢renameᵀ (premises `Mono ρ`, ∋:= and the   BReduction.agda
                               exterior-read ∋:=x; hk-suc / hx-suc)
  ≈ transport from ∋:=       UnfRen≈-hk (unfSub-dich, unf-up, unf-self) BReduction.agda
  L-sc                       subst-cong-sc                              Boundary.agda
  L-≼≈ (retagging)           _≼≈_, ⊢retag≈, bwf-retag≈, ≼≈-intOf,       BReduction.agda
                               ≼≈→Absorbs
  L-wf                       ⊢ty-wf, wf→Scoped, scB-bridge              ScopeBridge.agda
  L1                         ⊢substᵀᵐ, ⊢[]ᵐ, preserve-Beta              TermSubst.agda
  bad / bad₂ refuted         ¬⊢bad, ¬Reversal≈-bad₂                     Boundary.agda
  near-bad / far-bad         Reversal≈-near-bad, ¬Reversal≈-far-bad     Boundary.agda
  the x-licence adversary    ¬⊢adv, ¬starOnly-adv, adv-rep-match≈       Boundary.agda
  Example 8's T4′ boundary   Θ₈  (the [R2] shape)                       Boundary.agda
  Examples 9, 10  (P, E)     Γp/Γp′/Θp (chained dual), Δm/Θm            BReduction.agda
  Examples 11, 12 (E★′, Pc)  notes/InstallGauntlet.agda §1, §5  — NOT in All.agda
  the install gauntlet       notes/InstallGauntlet.agda  (E★′, E★, Pn,
                               dual-of-dual, Pc, soundness, renaming)
  design-path probes         notes/old/*Probe.agda — do NOT compile
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
