# Redesign advice from the Boundary Survey
# (2026-09-05; data = notes/BoundarySurvey.md, corpus = SurveyCorpus.agda;
#  answers to Jeremy's four questions + the open one)

## Q1 — Store the rep ONCE (at the outermost reveal / a store), look it
## up from inner boundaries?  YES — the strongest-supported change.

What the data says about per-boundary rep spelling (the current design):
- Every preservation failure is a failed attempt to COPY or RE-SPELL a
  rep across a boundary: F4 (x-copies die unconditionally), F5 (chained
  copies die at Λ-bound targets), R2′ (the discriminator is the entry at
  the named slot), and D1's two-copies drift was the same disease at the
  renaming level.
- F8/F9: every cancel that ever fires is a lineage pair — the conceal
  and the reveal are about ONE instantiation event.  Two spellings of
  one fact, plus machinery (Reversal≈, SkelEq, xrep-stored, MergeOK's
  faces) to argue they agree.
- R1: the requirement is to carry knowledge forward or refuse; a
  SPELLING sometimes cannot be carried (no rep is writable — §3.3), but
  a NAME always can.

The ownership design: the reveal that instantiates a variable OWNS its
rep for the variable's whole scope; every inner boundary mentioning that
variable stores only the NAME (slot).  Faces and licenses are defined by
owner lookup.  Two realizations:
  (i) STORE-PASSING (GTSF's Σ): reps in a store, `(α , A) ∈ Σ`;
      GTSF/Conversion.agda + proof/Core StoreProperties already carry
      the renaming/extension transport lemmas — the exact lemmas whose
      absence killed strong/'s ambient-dependent readings.
  (ii) OWNER-SYNTACTIC: the outermost reveal wrapper IS the store entry;
      lookup walks the enclosing type context.  Store-free (grounded), but
      faces become context-dependent — the transport risk is real and
      must be probed FIRST (the mitigation: lookup is by slot identity
      along the enclosing type context, which renamings move coherently —
      unlike spelled copies, which is exactly what D1 refuted).
Key structural fact favoring both: the owner's wrapper syntactically
ENCLOSES every inner user (a variable's scope is inside its reveal), so
inner crossings can never drop the owner — the pointer is stable where
the copy was not.  The demotion CONCEPT disappears: a dual re-points
slots; it never re-spells knowledge, so it has nothing to destroy.

## Q2 — Simultaneity: KEEP IT.  The data does not implicate it.

No finding involves sibling-entry interference inside one boundary; all
failures are CROSS-boundary propagation.  The one sequential-ish reading
in the system — the second-chance copy — exists only to patch copy
propagation (F5 shows it saving exactly the knowledge-target chains) and
retires under Q1, where there are no copies to patch.  Telescoping would
re-couple siblings without touching the actual failure surface, and it
was reverted once already for principled reasons.  Under ownership the
question mostly dissolves: entries carry names, not reps, so there is
little left for siblings to interfere over.

## Q3 — Conversion for the faces: YES, as HALF the boundary.

GTSF/Conversion.agda: `unseal α A ∶ ＇α ↑ˢ A` and `seal A α ∶ A ↓ˢ ＇α`
(both with `(α , A) ∈ Σ`), `s ↦ t` contravariant on domains, `∀ s`
under binders with store shift.  Mapping onto the survey:
- The four obligation shapes (§3.1) are exactly conversion forms:
  I = id, II = seal, III = unseal (+ ↦/∀ composites), IV = compositions
  of seal and unseal at different names.  The vocabulary fits the
  observed requirements precisely.
- R3's gap (61/195 rows with no term-determined face) is closed by
  making the conversion a WITNESS ON THE WRAPPER: M ⟪ Θˢ , c ⟫ with
  c : int-face ⇝ ext-face — every obligation row becomes self-checking,
  Oblig/Eval simpler, preservation transports subst-free.
- Jeremy's caveat is correct and load-bearing: Conversion does NOT do
  scoping.  THE SPLIT: a boundary = the SCOPE SKELETON (which slots
  exist inside — strong/'s tight-interior discipline, kept, rep-free)
  + the FACE CONVERSION (GTSF-style, store/owner-backed).  strong/
  contributes what GTSF lacks and vice versa.

## Q4 — The load-bearing cancel: becomes DEFINITIONAL.

Under ownership, `seal α` and `unseal α` both cite the ONE stored rep,
so interior/exterior face agreement at a cancel is by construction:
`unseal α ∘ seal α = id` is a one-time algebra lemma, replacing
cancel-agree + Reversal≈ + SkelEq + xrep-stored + MergeOK's two face
equations.  F8/F9 say the algebra only ever needs the same-name case on
reachable traces.  §9m's ≡/≈ gap cannot arise: there is no second
spelling to disagree with the first.

## Q5 — Other changes the data recommends

(a) MERGE → CANCEL.  F8/F9: six of six firing merges are lineage
    cancels to the empty composite; ⊕'s re-indexing generality is
    unused.  Retire ⊕/mrgB/MergeOK; the rule is the face-anchored
    Cancel (CancelProbe's 2-equation form, now definitional per Q4).
(b) NO ≈ IN THE RULES.  §9m/F2 is a pure ≡-vs-≈ disease; under
    ownership every license compares against the stored rep, ≡ by
    construction.  Unfold/≈Δ̄ leaves the trusted core.
(c) RETIRE the x-machinery (xrvld, ∋:=x, bwf↓x, starOnly, SkelEq/SkelX).
    F4: an x-license never survives a crossing; it was a birth-time
    patch over copied reps.  Ownership removes its reason to exist.
    (Check: E★′ — the one x-survivor — retypes via a Λ-bound owner-less
    name, the `abst`-pointer case.)
(d) THE DUAL SHRINKS to slot re-pointing: no entᴳ guards, no copies, no
    second chance, no rvl⋆-fallback-at-knowledge — F3/F4/F5's entire
    failure surface is deleted, not repaired.
(e) KEEP (the data actively endorses these): the active/inert value
    discipline (F11 — perfect separation), inward-only readings (F10 —
    23/23 Peels), det + values-don't-step, tightness FOR TERMS AND
    SCOPE.  FLAG for Jeremy: owner lookup reads a rep from an enclosing
    frame — I argue this is name RESOLUTION (the interior still cannot
    NAME the variable; only faces/metatheory resolve it, as ρᵇ already
    reads the exterior), not a tightness violation, but it is his law
    and his call.
(f) SOUNDNESS GATE for the whole direction: ⊢3n-adv must stay out.
    Under ownership a conceal must cite a live owner; the adversary's
    conceal has none — expected UNMINTABLE, to be machine-checked
    before anything lands.

## Next step

A design probe (ConversionBoundaryProbe): a mini-core with the split
boundary (scope skeleton + owner/store-backed conversion faces), the
Cancel rule, and Peel-as-repointing; run the 16-program corpus
end-to-end + the adversary suite.  Kill criteria: any corpus program
that stops typing/running, ⊢3n-adv minting, or a transport lemma
(⊢renameᵀ/⊢retag analog) that fails on the owner lookup — probe the
transport FIRST, it is the one open risk (mitigated by GTSF's proven
store lemmas if the store-passing realization is chosen).
