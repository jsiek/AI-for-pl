# Open design decisions (2026-09-03) — alternatives as definitions

Notation as in notes.md.  Each decision lists the alternatives as definitions
and the one consequence that matters.  Status: awaiting Jeremy's choice.

## Decision 1 — what licenses a conceal's representation?

Today:

    Γ ⇈ Θ    =  (Γ ↓ Y★) , X₁ , … , X_r            reveal variables enter as ABSTRACT
    (bwf-↓)  Γ ∋ Y      Ψ ⊢ A      Γ ∣ Ψ ⊢ Θ   ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

Consequence — a closed well-typed value that no type-preserving rule can
eliminate (machine-checked, notes/old/BoundaryRulesProbe.agda §5a):

    bad  =  (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=∀Z.Z→Z , X ⟫   :  ∀Z.Z→Z
    bad @(Z→Z)[ℕ]  :  ℕ→ℕ          stuck: B₀ is the variable X, not a ∀

Option 1a — record the knowledge in the interior context:

    Γ ⇈ Θ    =  (Γ ↓ Y★) , X₁:=A₁ , … , X_r:=A_r
    (bwf-↓)  Γ ∋ Y:=A      Γ ∣ Ψ ⊢ Θ            ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

  No typing rule converts through X:=A, so abstraction is unchanged.  `bad`
  is ill-typed (↓X:=ℕ against X:=∀Z.Z→Z).  This is the in-the-relation form
  of Zdancewic's global δ-consistency and is what Merge (Decision 3) needs.
  Cost: A₁ is read in the exterior Γ but the entry sits in the interior,
  whose tail may lack variables A₁ names (Example 8: ↑Z:=Y , ↓X:=ℕ over
  Y, X has interior ∅ , Z:=Y with Y blocked).  So the entry is a knowledge
  entry read in Γ, not a telescope entry; in Agda ⊢renameᵀ renames it by
  the exterior renaming.
  Second cost (found while landing Wrap): today typing reads Γ only through
  ∋ and ⊢, so it transports along any context of the same LENGTH
  (BReduction.⊢retag), and Wrap's preservation uses that to retype the
  argument in the dual's interior (Γ ↓ Y★ rebuilt with abstract entries),
  which equals Γ only when Γ's dropped prefix is all abstract.  Under 1a the
  entries X:=A become typing-relevant, ⊢retag fails, and the dual's interior
  must equal Γ exactly — which fails at BLOCKED slots (their dual reveal has
  a dummy rep, Γ's entry may carry knowledge).  1a therefore needs either a
  Wrap restricted to boundaries whose exterior is all-abstract-below-Y★
  (true at run time: only Λ and reveals create entries — a probe should
  confirm), or a dual that copies Γ's knowledge for blocked slots.

Option 1b — keep (env); progress for reachable terms via a predicate

    Consistent M  ⟺  every ↓Y:=A in M whose enclosing boundary has ↑Y:=A′
                     satisfies A = A′

  preserved by reduction, true of source programs.  A companion predicate
  (against the grounded-invariants design law).

Option 1c — accept the gap: progress for source images only; no Merge/Cancel.

### Decision 1 — resolution (2026-09-03, after Jeremy's clarification and the probe)

Jeremy: the old design's (conceal) rule had the premise `Γ ∋ X:=A` and the
invariant "a conceal's representation is the one the matching reveal
recorded" was never meant to be dropped.  Decision 1 is therefore settled
on restoring it (Option 1a); 1b/1c are withdrawn.  The probe
notes/old/GroundedProbe.agda (agda --safe clean) fixes the exact form:

    Γ ⇈ Θ    =  (Γ ↓ Y★) , X₁:=A₁ , … , X_r:=A_r       knowledge entries (Aᵢ read in Γ)
    (bwf-↓)  Γ ∋ Y:=A₀      A = A₀[γΘ]      Γ ∣ Ψ ⊢ Θ   ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

  i.e. the conceal's rep A is the INTERIOR reading of the knowledge Γ holds
  about Y.  The transport A = A₀[γΘ] is NOT optional: comparing A₀ and A
  syntactically (the naive 1a) still admits a stuck closed value `bad₂`
  (probe §5), because ` 0 read in Γ↓Y (= P) and ` 0 read in the interior
  (= the fresh reveal Z) are different variables.  In de Bruijn A₀ is first
  shifted past the r reveals and Y (`liftRep`), then γΘ is applied.
  Since the premise mentions γΘ of the WHOLE boundary, boundary
  well-formedness takes Θ as a parameter instead of recursing on the list.

  Checked in the probe: `bad` and `bad₂` are untypable; Example 8 T0…T5 all
  type and every step is a real -→ (TyWrap/Wrap included); Merge's cancel
  clause is sound by inversion (`cancel-agree`: a ↓X:=A inside a boundary
  whose reveal is ↑X:=A′ has A = A′) — the payoff.

  Consequences for Wrap (also machine-checked):
  * typing no longer transports along equal-length contexts (`¬⊢retag-len`);
    it transports along `Δ ≼ Δ′` (entrywise: abstract ≼ anything, X:=A ≼
    X:=A) — `⊢retag′`.
  * the dual rebuilds Γ's entry exactly at CONCEALED slots (the conceal rep
    is Γ's knowledge), but at BLOCKED slots it yields a dummy `↑Y:=ℕ`, i.e.
    interior entry Y:=ℕ, which can differ from Γ's entry for Y.  Wrap's
    argument retypes only if blocked slots are ABSTRACT in Γ (`BlkAbst`),
    and that property is not preserved unless the dual marks blocked slots
    specially.  Hence one more syntax change:

    Θ  ::=  …  |  ↑Y:⋆ , Θ      blocked reveal: interior entry abstract, no
                                 knowledge; external face a dummy (never named,
                                 by the scope premise); produced only by the
                                 dual at dropped-but-unconcealed slots

  Open (small): whether `BlkAbst` then holds for every run-time boundary (only
  Λ, reveals and ↑Y:⋆ create context entries) or must be a premise of (env).

### Decision 1 — refinement forced by the implementation (2026-09-04)

The rework (worktree, not merged; 2 labelled holes) machine-checked that the
form above is not yet right: storing a reveal's rep "as written, read in the
exterior" as the interior entry X:=A is inconsistent with renaming, because
every other use of an entry (∋ X:=A, the shift liftRep, ⊢renameᵀ) reads it as
a TELESCOPE entry, over the entries below it.  Witness (`¬hk-int`):

    Γ = X:=ℕ , W        Θ = ↑Z:=W , ↓X:=ℕ        weaken by a new abstract V
    Γ ⇈ Θ = ∅ , Z:=W    but after weakening the entry reads Z:=(the slot W moved to)
    while the interior renaming (identity here) demands the entry be unchanged.

Fix (worked out, to implement): the interior entry is the INTERIOR READING of
the reveal's rep — concealed variables replaced by their reps, kept variables
re-indexed — and a reveal whose rep names a BLOCKED variable contributes an
abstract entry (no knowledge):

    Γ ⇈ Θ    =  (Γ ↓ Y★) , X₁:⟦A₁⟧ , … , X_r:⟦A_r⟧
       ⟦A⟧    =  A[γΘ]  if A names no blocked variable,   X:⟦A⟧ = X abstract otherwise
    (bwf-↓)  Γ ∋ Y:=A₀     ⟦A₀⟧ scoped (names no blocked var)     A = ⟦A₀⟧
             Ψ ⊢ A     Γ ∣ Ψ ⊢ Θ                             ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

  Under the grounded premise a conceal rep never names a reveal variable (it
  is the reading of exterior knowledge, which bottoms out in kept variables),
  so ⟦A⟧ is a legitimate telescope entry.  `bad`/`bad₂` stay refuted.

### Decision 4 — Wrap and a blocked slot that carries knowledge (needs a ruling)

  P  =  (ΛX. λf:(X→X). ΛY. λw:X. f w) [ℕ] (λn:ℕ. n) [𝔹] 3      : ℕ

  → TyBeta   (λf. ΛY. λw. f w) ⟪ ↑X:=ℕ , (X→X)→∀Y.X→X ⟫ · (λn.n) [𝔹] 3
  → Wrap     ((λf. ΛY. λw. f w) · f′) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫ [𝔹] 3          f′ = (λn:ℕ.n) ⟪ ↓X:=ℕ , X→X ⟫
  → Beta     (ΛY. λw:X. f′ w) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫ [𝔹] 3
  → TyWrap   ((ΛY. λw. f′ w) [Y′]) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X→X ⟫ 3            interior Y′:=𝔹 , X:=ℕ
  → TyBeta   ((λw:X. f′ w) ⟪ ↑Y:=Y′ , X→X ⟫) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X→X ⟫ 3
  → Wrap     (((λw. f′ w) ⟪ ↑Y:=Y′ , X→X ⟫) · W₁) ⟪ … , X ⟫                W₁ = 3 ⟪ ↓Y′:=𝔹 , ↓X:=ℕ , X ⟫
  → Wrap     ((λw. f′ w) · W₂) ⟪ ↑Y:=Y′ , X ⟫ ⟪ … ⟫                       W₂ = W₁ ⟪ ↓Y:=Y′ , X ⟫
  → Beta     ((λn:ℕ.n) ⟪ ↓X:=ℕ , X→X ⟫ · W₂) ⟪ ↑Y:=Y′ , X ⟫ ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X ⟫
  → Wrap     ((λn:ℕ.n) · (W₂ ⟪ ↑Y:⋆,↑Y′:⋆, ↑X:=ℕ , X ⟫)) 
                 ⟪ ↓X:=ℕ , X ⟫ ⟪ ↑Y:=Y′ , X ⟫ ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X ⟫

The example.  Exterior Γ = Y:=𝔹 , X:=ℕ (both revealed; Y shallower).  A sealed
identity on X, and an argument of type X that USES Y's knowledge:

    h  =  (λx:ℕ. x) ⟪ ↓X:=ℕ , X→X ⟫              : X→X      Γ ⇈ (↓X:=ℕ) = ∅ ; Y is BLOCKED
    W  =  (3 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↓Y:=𝔹 , X ⟫         : X        the outer conceal reads Γ ∋ Y:=𝔹
    R  =  h · W                                   : X        well typed, a Wrap redex

    (Wrap)  R  -→  ((λx:ℕ. x) · (W ⟪ Θᵈ , X ⟫)) ⟪ ↓X:=ℕ , X ⟫

Θᵈ, the dual of ↓X:=ℕ over Γ, has exterior ∅ and must rebuild Γ as its
interior.  It can rebuild X (concealed: its rep ℕ is Γ's knowledge), but for
the BLOCKED slot Y it has nothing to copy — the dual is syntactic and cannot
see Γ — so it emits a blocked reveal ↑Y:⋆, whose interior entry is Y abstract:

    Γ ⇈ (↓X:=ℕ) ⇈ Θᵈ  =  Y , X:=ℕ        ≠   Y:=𝔹 , X:=ℕ  =  Γ

W must now be retyped there, and its outer conceal ↓Y:=𝔹 needs Y:=𝔹 — FAILS.
The contractum is ill typed: preservation breaks on R.  (Nothing here is
exotic: Γ is the interior of two reveals; h is a sealed value weakened by a
later reveal Y — exactly what TyWrap does to the boundaries inside V; W's
conceal of Y is what the dual of a boundary revealing Y produces.)

A closed System F program that reaches this configuration (two blocked
knowledge slots instead of one):

    P  =  (ΛX. λf:(X→X). ΛY. λw:X. f w) [ℕ] (λn:ℕ. n) [𝔹] 3      : ℕ

    TyBeta   (λf. ΛY. λw. f w) ⟪ ↑X:=ℕ , (X→X)→∀Y.X→X ⟫ · (λn.n) [𝔹] 3
    Wrap     ((λf. ΛY. λw. f w) · f′) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫ [𝔹] 3        f′ = (λn:ℕ.n) ⟪ ↓X:=ℕ , X→X ⟫
    Beta     (ΛY. λw:X. f′ w) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫ [𝔹] 3
    TyWrap   ((ΛY. λw. f′ w) [Y′]) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X→X ⟫ 3          interior Y′:=𝔹 , X:=ℕ
    TyBeta   ((λw:X. f′ w) ⟪ ↑Y:=Y′ , X→X ⟫) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X→X ⟫ 3
    Wrap     (((λw. f′ w) ⟪ ↑Y:=Y′ , X→X ⟫) · W₁) ⟪ … , X ⟫              W₁ = 3 ⟪ ↓Y′:=𝔹 , ↓X:=ℕ , X ⟫
    Wrap     ((λw. f′ w) · W₂) ⟪ ↑Y:=Y′ , X ⟫ ⟪ … ⟫                     W₂ = W₁ ⟪ ↓Y:=Y′ , X ⟫
    Beta     (f′ · W₂) ⟪ ↑Y:=Y′ , X ⟫ ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X ⟫

  The last line is a Wrap redex at exterior Γ = Y:=Y′ , Y′:=𝔹 , X:=ℕ; f′'s
  boundary ↓X:=ℕ blocks Y and Y′ (both revealed), W₂ conceals both; the dual
  of ↓X:=ℕ is ↑Y:⋆ , ↑Y′:⋆ , ↑X:=ℕ with interior Y , Y′ , X:=ℕ ≠ Γ, and W₂'s
  two conceals fail to retype.  Note that BOTH TyWrap and TyBeta introduce a
  revealed variable above f′ (TyBeta turns the Λ-bound Y into Y:=Y′ without
  renaming), so W3 has to act in both rules.

The alternatives, on this example:

  (W1)  Add a premise to preservation, RunOK Γ M: "at every boundary in M the
        dual rebuilds the exterior" (here: false, so R is simply excluded).
        Works (the rework closed Wrap with it) but it is a companion predicate
        on terms — against the grounded-invariants law.

  (W2)  Make it an (env) premise: "every slot the boundary drops without
        concealing is ABSTRACT".  h is then ill typed (Y:=𝔹 is dropped and not
        concealed).  Grounded — but TyWrap creates h-like terms by weakening a
        sealed value under a new reveal, so TyWrap would fail preservation.

  (W3)  Never let a revealed slot be blocked: when a boundary with conceals is
        weakened by a NEW REVEALED variable, conceal that variable in it too,
        with the interior reading of its knowledge.  In the example h becomes

            h′ = (λx:ℕ. x) ⟪ ↓Y:=𝔹 , ↓X:=ℕ , X→X ⟫         Y concealed, not blocked

        the body is unchanged (interior still ∅, X→X[γ] = ℕ→ℕ), and the dual
        is ↑Y:=𝔹 , ↑X:=ℕ with interior Y:=𝔹 , X:=ℕ = Γ, so W retypes and
        Wrap preserves types.  Blocked slots are then always ABSTRACT
        (Λ-bound), (W2)'s condition holds by construction, and no premise is
        needed anywhere.  Cost: type-variable weakening through a boundary
        becomes knowledge-aware.  Only TyWrap introduces a revealed variable
        above existing boundaries, so the cleanest place is TyWrap's
        contractum: instead of a plain ⇑ᵀ V, weaken V by "↑Z:=A, concealing Z
        in every boundary of V that has a conceal" (named notation: nothing
        moves, the conceal ↓Z:=⟦A⟧ is inserted).

  (W4)  Stop dropping: Γ ⇈ Θ = Γ , X₁:⟦A₁⟧ , … , X_r:⟦A_r⟧ — concealed variables
        stay in scope (γ still resolves them to their reps) and no slot is ever
        blocked.  Then the dual has nothing to rebuild (its interior is a
        weakening of Γ by the reveal slots, which ⊢renameᵀ supplies), the
        scope premise of (env) becomes vacuous, Merge's context law is trivial,
        and the counterexample below (a reveal rep naming a blocked slot)
        cannot arise.  Cost: it gives up the TIGHT interior of §2 — the
        property that a sealed value's context contains only variables that
        existed when the seal was made.  Terms cannot mention later variables
        anyway (they predate them), so tightness restricts derivations, not
        terms; but it is the design intent behind "strong", so this is
        Jeremy's call, not a technicality.  (Under W4 the old design's Example
        8 reduct would even be well typed: the type argument Y is in scope.)

  Recommendation was W4; OVERRULED (Jeremy, 2026-09-04): tightness is wanted
  for its own sake — W4 withdrawn.  Design principle made explicit: almost no
  rule performs a type shift on a TERM, and that is the point — a shift
  forgets which type variables a term is not allowed to mention.  The only
  exception is TyWrap's ⇑ᵀ V, which Jeremy would also like to eliminate
  (open; candidate: introduce the new reveal at the DEEP end of the interior
  instead of the shallow end, so existing term indices are untouched and the
  shift lands on the boundary type B₀ instead of on V — to be probed).
  So Decision 4 is resolved by W3 (knowledge-preserving weakening), with the
  reveal-rep-names-a-blocked-variable case (¬⊢dualΘnʳ, e.g. TyWrap's own
  ↑Z:=Y with Y Λ-bound and blocked) still open under tightness.

  Would Merge help instead? (Jeremy's question, 2026-09-04.)  No — checked on
  P: after the second TyBeta the two nested reveal boundaries DO merge
  (Θ₁ = ↑Y:=Y′ against Θ₂ = ↑Y′:=𝔹,↑X:=ℕ; nothing cancels; Y's rep unfolds
  to 𝔹), and the trace gets nicer — the argument then carries ONE dual
  boundary ↓Y:=𝔹,↓Y′:=𝔹,↓X:=ℕ with fully unfolded reps instead of the nested
  W₂ — but the failing step is unchanged: f′ = (λn:ℕ.n) ⟪ ↓X:=ℕ , X→X ⟫ sits
  UNDER the λ in λw:X. f′ w, so no wrapper-on-wrapper Merge ever reaches it,
  and its dual still rebuilds Y, Y′ as ⋆ where Γ has knowledge.  The blocked-
  knowledge configuration is created by TyBeta/TyWrap weakening boundaries
  INSIDE the body; only those rules are positioned to fix it, which is W3 —
  indeed W3's inserted ↓Z:=⟦A⟧ is exactly the entry a merge with the new
  reveal's dual would deliver if the λ were not in the way.

### Decision 4, continued — W3's traversal, the forcing example E, and the ambient dual (2026-09-04)

Jeremy: W3's ⇓ ("pass Y:=A down into V") is a term traversal — wants a
localized/incremental mechanism.  Forcing example (closed source; the gadget
is a TYPE abstraction between ΛY and the sealed value, evaluated under the Λ
by ξ-Λ before Y's TyWrap can fire):

    E  =  (ΛX. λf:(X→X). ΛY. (ΛZ. λz:X. f z) [ℕ]) [ℕ] · (λn:ℕ. n) · [𝔹] · 3

    TyBeta(X); Wrap; ξ TyBeta(Z)  [TyBeta needs W3 too: ↓X blocks Z ⇒ insert ↓Z:=ℕ]
      ⇒ ((ΛY. ((λz:X. ((λn:ℕ.n) ⟪ ↓Z:=ℕ , ↓X:=ℕ ⟫) z) ⟪ ↑Z:=ℕ ⟫)) ⟪ ↑X:=ℕ ⟫) [𝔹] · 3
    TyWrap(Y)+W3: the Λ-body is the REVEAL-ONLY wrapper ⟪↑Z:=ℕ⟫, which does not
    block Y ⇒ ⇓ must CROSS it (and λz, and an application) to insert ↓Y:=𝔹 at
    the sealed boundary.  Merge cannot pre-flatten (the ΛY sits between the two
    boundaries); iterating the (ΛZ.…)[ℕ] gadget makes the crossing depth
    unbounded; P already made the binder depth unbounded.

Where the knowledge is CONSUMED: only when the sealed boundary's own
Wrap/TyWrap builds its dual — and that redex sits under the ξ-⟪⟫ frames of
the boundaries that revealed Y, whose interiors are exactly the redex's
typing context.  Hence the incremental candidate:

  (A) AMBIENT DUAL / knowledge-indexed reduction:  Γ ⊢ M -→ M′  (mirroring
      the Δ-indexed typing);  ξ-⟪⟫ extends Γ with the boundary's interior,
      ξ-Λ with an abstract entry;  Wrap's dual is  dualᵇ Γ Θ  — for each slot
      Θ drops without concealing, copy Γ's OWN entry (knowledge if revealed,
      abstract if Λ-bound).  No ⇓, no insertion, no ⋆-with-lost-knowledge;
      every step local; grounded (it is the reduction judgment itself).
      By typing, Γ always suffices.

Star nuance: W3/(A) eliminate the HARMFUL stars (knowledge existed and was
lost).  A genuinely Λ-bound blocked slot still gets an abstract
re-introduction under either scheme — exact, since Γ's entry is abstract too;
write it as a rep-less reveal ↑Y rather than ↑Y:⋆.

Status: probe launched (contextual dual on E and P, compatibility with the
reversal-form premise).  W3-as-traversal kept as the fallback.

### Decision 4 — ambient dual probe verdict and the overnight install (2026-09-04, Jeremy asleep)

notes/old/AmbientDualProbe.agda (agda --safe clean).  Verdict: POSITIVE on the
candidate itself —
  ✓ P repaired with NO insertion anywhere (dualᴳ copies Y:=𝔹; rebuild = Γ on
    the nose; dualᵇ version refuted);
  ✓ E handled with ZERO traversal (both blocked knowledge entries copied at
    the moment of use; the sealed boundary stays the plain ↓X:=ℕ for its
    whole life);
  ✓ Λ-bound blocked slot: rep-less abstract reveal, exact rebuild (dualᵇ
    rebuilt bogus knowledge Y:=ℕ there — an exactness leak now fixed);
  ✓ reversal-premise compatibility reproduced in general.

Two residues, and the overnight scoping calls made under the mandate ("if
the probe comes back positive, install"):

  (R1) CHAINED KNOWLEDGE (probe §6b, reachable): Γ = Y:=Y′ , Y′:=𝔹 , X:=ℕ,
    Θ = ↓X:=ℕ — the copied entry for Y names Y′, which Θ also blocks, so the
    dual's reveal rep ` 0 is ill-formed under the PARALLEL reading of a
    boundary's reveal block.  Probe: it is exactly the right TELESCOPIC
    entry.  CALL: adopt the telescopic reading of the reveal block
    ((bwf-↑) reads each reveal rep over Γ extended by the DEEPER reveals of
    the same boundary; ρ becomes the corresponding fold) — this matches the
    repo's existing telescope convention for revealed entries
    (Context.agda: "the rep stored in rvld A is a type over its tail").
    Flagged for Jeremy's review; revertible.  [REVERTED 2026-09-04, see RULING below — landed on the branch.]

  (R2) A REVEAL REP NAMING A SLOT ITS OWN BOUNDARY BLOCKS (¬⊢dualᴳΘn;
    Θn = ↑Z:=Y , ↓X:=ℕ with Y Λ-bound and blocked — minted by TyWrap itself
    whenever a sealed polymorphic value is instantiated at an abstract
    variable, e.g. Example 8's f [Y]).  "Z is Y" is not expressible in an
    interior that dropped Y: Z's knowledge entry is abstract, so the dual's
    conceal of Z is unlicensed and Wrap's contractum does not type.  NOT
    resolved by the ambient dual (nor by W3).  CALL: do not invent a fix
    overnight; the Wrap preservation case for such boundaries is isolated
    as a `...Def` statement parameter with the obligation stated precisely,
    and the candidate resolutions recorded: (a) Γ-aware knowledge closure in
    ⟦·⟧ (resolve blocked variables of a reveal rep through Γ's knowledge
    when it exists — helps the revealed case, not the Λ-bound one);
    (b) a conceal premise licensed by the boundary's own reveal rep rather
    than the interior entry; (c) Merge-first normalization.  Jeremy rules.

Install scope (Track L/M): knowledge interiors ⟦A⟧ + reversal-form (bwf-↓)
+ rep-less abstract reveal entry + telescopic reveal block + Γ-indexed
reduction with dualᴳ; preservation and progress updated; Merge still NOT
landed (unfolding-transport open); ProgressDef keeps its parameters.

### Decision 3 — tension with Decision 1 found by the Merge probe (needs a ruling)

notes/old/MergeProbe.agda (agda --safe clean) defines Θ₁ ⊕ Θ₂ and proves the
face laws in general, but exhibits a Merge redex with NO well-typed
contractum under the grounded premise as stated:

    Γ  =  X:=ℕ→ℕ
    inner  (λw:W. w) ⟪ ↑W:=ℕ , W→W ⟫            : ℕ→ℕ    in the interior of the outer boundary
    outer  ( … ) ⟪ ↓X:=ℕ→ℕ , X ⟫                : X       internal face of X is ℕ→ℕ  ✓

A merged single boundary must have external face X and internal face W→W:

    (λw:W. w) ⟪ ↑W:=ℕ , ↓X:=(W→W) , X ⟫

i.e. the conceal of X must carry the rep W→W — "X is W→W", true because W is
ℕ — but the grounded premise as written pins X's rep to the interior
READING of Γ's knowledge, ℕ→ℕ, syntactically.  So Decisions 1 and 3a
conflict: the premise compares knowledge without UNFOLDING the boundary's
own reveals, which is exactly what Zdancewic's Δ̄ (transitive closure) and
their (trans) rule allow.

Candidate fix — compare in the EXTERIOR instead of the interior (the
"reversal" form):

    (bwf-↓)  Γ ∋ Y:=A₀     A[ρΘ] = A₀     Ψ ⊢ A     Γ ∣ Ψ ⊢ Θ   ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

  the conceal's rep A, read back out through the boundary (reveal variables
  ↦ their reps), must equal the exterior's knowledge.  On the examples:
  merged boundary above: (W→W)[W↦ℕ] = ℕ→ℕ = Γ's knowledge  ✓ accepted;
  bad: ℕ ≠ ∀Z.Z→Z  ✓ rejected;  bad₂: ` 0[Z↦ℕ] = ℕ ≠ P  ✓ rejected;
  dual conceal of a reveal Z:=A: A read back = A = the entry  ✓.
  Bonus: the external face commutes with renaming WITHOUT a scope restriction
  (BReduction.ρᵇ-comm / C-ext), unlike γ, so this premise should transport
  under ⊢renameᵀ more easily than the interior form.  Interior knowledge
  entries stay as in the Decision-1 refinement (X:⟦A⟧).
  Still open even with the fix: Merge's contractum interior differs from the
  nested one by UNFOLDING (probe: nested W:=Z vs merged W:=ℕ when Z:=ℕ), so
  Merge's preservation needs "retyping along unfolding", Zdancewic's Δ̄.

  Probe verdict (notes/old/ReversalProbe.agda, agda --safe clean, 2026-09-04):
  ADOPT.  Verbatim premise (over Δ; A₀ lifted from Δ ↓ X):

      Reversal Θ X A A₀ = outRead Θ A ≡ upRep X A₀
      bwf↓ʳ : Δ ∋ X := A₀ → Reversal Θ X A A₀ → Ψ ⊢ A → … → ⊢ᵇʳ (cnc X A ∷ Ξ)

  ✓ bad, bad₂ refuted;  ✓ the no-merge redex AND its merged boundary type;
  ✓ MergeProbe's ¬⊕-bwf pair now composes;  ✓ Example 8 T0…T5 with all steps;
  ✓ Wrap's dual conceals satisfy the premise (dual-read-back, general, for
  reps naming no blocked slot);  ✓ transports under ANY monotone renaming
  with no scope restriction (Reversal-ren) — the interior form's failure
  point;  ✓ W3's h′ types, its dual interior is Γ on the nose, W retypes.

  NEW COUNTEREXAMPLE (¬⊢dualΘnʳ): a reveal whose rep names a BLOCKED slot —
  Example 8's own run-time boundary ↑Z:=Y , ↓X:=ℕ over Y , X (Y blocked) —
  gets an abstract interior entry for Z under the Decision-1 refinement, so
  the dual's conceal ↓Z:=Y has no knowledge to match: Wrap is stuck on the
  T5 boundary.  W3 does not help (Y is Λ-bound, so nothing conceals it); W4
  removes the problem (Y is not dropped, Z:=Y is a legal entry).  Otherwise:
  forbid reveal reps that name blocked slots in (bwf-↑), which would reject
  T4/T5.
  Still open: Merge's contractum interior differs from the nested one by one
  UNFOLDING (probe: ⊕ pushes Θ₂'s conceal rep in as ℕ→ℕ, Merge needs W→W);
  preservation of Merge needs retyping along unfolding (Zdancewic's Δ̄).

## MORNING AGENDA (2026-09-04, after the overnight install — commit acebd7f5)

The ambient dual is INSTALLED and `make check` is green.  Preservation lives
in `BPreservation.Impl (dual-rep) (dual-cnc) (dual-int)`; progress in
`Progress.Impl (rv-app) (rv-tapp) (nt-app) (nt-tapp)` (statements in
DualDef.agda / ProgressDef.agda).  Rulings wanted, in rough priority:

1. R2 (`DualCnc`): a reveal whose rep names a slot its own boundary blocks
   (Example 8's ↑Z:=Y , ↓X:=ℕ with Y Λ-bound).  Candidates: (a) Γ-aware
   knowledge closure in ⟦·⟧; (b) license the dual's conceal by the reveal's
   own rep; (c) Merge-first normalisation (may subsume R2 — see 6).
2. `DualRep` vs a `⊢ Δ` premise on preservation: the copied-knowledge rep's
   well-formedness is provable if preservation carries well-formedness of
   the ambient context (needs an intOf-closure lemma).  Accept parameter or
   add the premise?
3. Confirm/revert the telescopic reveal block (R1 call, provisional).
4. Confirm the `dfree` guard on ⟦·⟧ (a reveal whose interior reading is not
   a legal telescope entry contributes an abstract entry — some knowledge
   silently dropped; without the guard ⊢renameᵀ is false).
5. TyWrap's rep lift `renameᵗ (revs Θ +_) A` (type shift only) — forced by
   the telescope; confirm the rule as landed.
6. Next big piece order: Merge (discharges the four ProgressDef parameters;
   needs retyping-along-unfolding) vs resolving R2 first — note candidate
   (c) would make Merge subsume R2.
7. Cheap win, if wanted: revive Cancel — its old side condition ("conceal
   rep equals the enclosing reveal's rep") is now exactly what Reversal
   guarantees.

## RULING (Jeremy, 2026-09-04 morning) — telescopic (bwf-↑) REVERTED

"The representation type of a reveal entry is well-formed in the EXTERNAL
context, without any interference from the other entries in the boundary.
This is an important part of the simultaneous nature of the boundaries."

The R1 overnight call (telescopic reveal block) is therefore a mistake and
is reverted: (bwf-↑) reads each reveal rep over the plain exterior Γ, in
parallel; ρ returns to the parallel form (rep substituted as-is, not folded
through the other reveals).  Recorded as a design principle alongside
tightness and no-term-shifts: SIMULTANEITY = (i) a conceal's rep may mention
the boundary's reveal variables (the original Example-8 fix), and (ii) a
reveal's rep is read in the plain exterior, independent of its siblings.

Consequences (worked out before reverting):
  * TyWrap's rep lift `renameᵗ (revs Θ +_) A` was forced ONLY by the
    telescope — it disappears; the rule returns to
    `((Λ V) ⟪ Θ , ∀·B₀ ⟫)·[B,A] -→ V ⟪ ↑?:=A , shiftReps Θ , B₀ ⟫` with A
    unlifted.  Agenda items 3 and 5 are hereby closed.
  * ρᵇ-comm / C-ext revert to their simpler pre-fold proofs; the Reversal
    premise's read-back returns to the ReversalProbe-verified parallel form.
  * The one thing the telescope was buying — AmbientDualProbe §6b (chained
    knowledge: the dual's copied rep for Y is Y′, itself blocked) — is no
    longer expressible as a raw copy.  Under the parallel reading the dual's
    copied rep must be UNFOLDED through Γ's knowledge until it mentions only
    surviving variables (well-founded: Γ's entries are a telescope), which is
    the SAME knowledge-closure operator as candidate (a) for R2.  Until (a)
    is ruled on, §6b's obligation simply lives inside the DualRep parameter.
    One operator would then serve both: interior entries ⟦·⟧ and the dual's
    copied reps.

## CANDIDATE (a) SHARPENED TO (a′) — unfold AT ENTRY BIRTH (2026-09-04)

Worked example Pc (colored trace: the "Scope Trace of Pc" artifact) — the
smallest closed program minting CHAINED knowledge above a seal:

    Pc = (ΛX. λg:(X→X). ΛY. λx:X. ((ΛW. λu:X. g u) [Y]) x) [ℕ] · (λn:ℕ. n) · [𝔹] · 3

  By T5 the ambient context is  W:=Y , Y:=𝔹 , X:=ℕ  and the seal ↓X:=ℕ (in
  application position — Merge can never reach it) must eventually dualise,
  copying knowledge for W.  Raw copy of W:=Y is inexpressible under the
  parallel reveal reading (Y is itself dropped) → ↑W:⋆ → the argument's
  ↓W conceal is unlicensed → ✗.

  Fix, sharpened by the trace: unfold WHEN THE ENTRY IS BORN — ⟦·⟧ stores
  knowledge fully resolved through the ambient context (Zdancewic's Δ̄), so
  T5's entry is W:=𝔹, T6's dual conceal is minted as ↓W:=𝔹, and T7's copy
  is a plain closed type.  Unfolding lazily in the DUAL instead is wrong:
  the rebuilt entry (W:=𝔹) would mismatch conceals minted at the raw
  knowledge (↓W:=Y), forcing "retyping along unfolding" — Merge's open
  obligation — into Wrap.  At-birth unfolding keeps every conceal and copy
  in agreement by construction.

  (a′) preserves the rulings: simultaneity — the boundary SYNTAX ↑W:=Y is
  untouched, reps still read in the plain exterior; tightness — nothing new
  enters an interior, entries only become more resolved.  It is the same
  operator that fixes R2's Pn (there the BLOCKED Y unfolds; here the
  CHAINED Y does), so one mechanism closes both Pn and Pc, with the
  Λ-bound case abstract-as-today plus the no-abstract-value vacuity lemma.

  RULING (Jeremy, 2026-09-04): conditional go-ahead — "If the probe finds no
  mismatches, go ahead with (a′)."

  PROBE VERDICT (notes/UnfoldProbe.agda, agda --safe clean): MISMATCH FOUND
  — (a′) NOT INSTALLED, per the ruling.  Jeremy's worry is real, structural,
  and lands at exactly one consumer: THE DUAL'S CONCEAL-OF-A-REVEAL.

  The witness (¬DualCnc-a′), on Pc's own next step, exterior Y:=ℕ , X:=ℕ,
  boundary ΘW = ↑W:=Y:

      (a′) entry for W:  W:=ℕ  (unfolded)
      the dual's conceal is FORCED to carry the raw stored rep:  ↓W:=Y
        (simultaneity: cncOfRevs reads the reveal's stored rep, which stays
         raw — the same ruling that reverted the telescope)
      read-back Y  ≠  knowledge ℕ   →  the Wrap contractum does not type.

  All three placements of eager unfolding fail, each refl-checked:
    entry only          → ¬DualCnc-a′   (above)
    + dual's conceal    → ¬face-unfolded, ¬argY-retype (internal face and
                          the argument's retype break)
    + the stored rep    → ¬TyBeta-unfold-rep (TyBeta breaks; also rewrites
                          the TERM, against the no-term-shift spirit)
  and each is repaired by the same missing ingredient: EQUALITY UP TO
  UNFOLDING.  So (a′) does not eliminate retyping-along-unfolding — it
  relocates it from Merge into Wrap — and it additionally needs a
  strengthened ⊢renameᵀ hypothesis (¬UnfRen-hk).

  Provably impossible under uniform (a′) (the sites that are SAFE):
  route divergence (routes-agree — and note ¬cnc-W-raw: in the RAW regime
  chained knowledge can never be concealed at all), Merge's middle-type
  mismatch (⊕-int-a′ on the nose), ≼-retag (⊕-retag-a′ via idempotence),
  faces/scope/blocked slots bit-identical (barrier-* — the abstraction
  barrier is untouched by either regime).  Bonus: under normal-form
  knowledge the dfree guard is vacuous (rd-dfree).

  RECOMMENDATION → (a″): keep RAW entries (no information erased anywhere),
  and make the KNOWLEDGE COMPARISONS up-to-unfolding: bwf↓'s licensing
  compares Δ̄(read-back) with Δ̄(knowledge); the dual's copy is the one-step
  unfold of Γ's entry (differing from it by exactly unf-eq-entries); ≼ and
  the Merge middle type compare up to Δ̄.  This is Zdancewic's (eq) rule
  (compare at Δ̄) WITHOUT their eager retag (7).  On the probe's witnesses
  (a″) needs nothing at site 3 (DualCnc-raw is refl today), dissolves the
  ⊢renameᵀ strengthening, and repairs site 1 by unfolding only the copy.
  Cost: the licensing premise becomes 'up to Δ̄' — one congruence threaded
  through bwf↓/dual/retag — instead of syntactic equality.  Awaiting ruling.

## Would Merge solve Pc instead of (a′)?  (Jeremy's question, 2026-09-04)

No — checked on Pc's T6 argument (3 ⟪ ↓Y:=𝔹 , ↓X:=ℕ ⟫) ⟪ ↓W:=Y ⟫, which IS a
Merge redex.  ⊕ pushes the outer conceal's rep through the inner γ, so the
merge UNFOLDS correctly: 3 ⟪ ↓W:=𝔹 , ↓Y:=𝔹 , ↓X:=ℕ ⟫.  But:
  (1) the merge step itself is ill typed in the raw-knowledge world — the
      merged ↓W:=𝔹 is licensed against the ambient entry, which is still the
      raw W:=Y from T5 (read-back 𝔹 ≠ Y) — MergeProbe's retyping-along-
      unfolding gap, live on this trace;
  (2) even granting it, T7 still fails: the seal's dual copies the AMBIENT
      entry (raw W:=Y → ↑W:⋆), which no restructuring of the argument can
      reach.
Under (a′) both vanish: entries are born unfolded (W:=𝔹 from T5′), the
argument's conceal is minted unfolded, Merge's output agrees with the
context and becomes type-preserving.  Conclusion: MERGE PRESUPPOSES (a′),
not the reverse — Zdancewic's structure exactly (their merge (8) is sound
only over Δ̄-resolved annotations, maintained eagerly by retag (7); (a′) is
our rule (7)).  Order of work: (a′) → Merge.

## (a″) PROBE VERDICT — SURVIVED (notes/UpToProbe.agda, 2026-09-04)

All seven sites SAFE, with one requirement and one residual:
  ✓ the (a′) killer reversed (DualCnc≈-Pc: raw conceal licenses by refl);
  ✓ Pc end-to-end (the chained copy unfolds, the argument retypes: ≼≈);
  ✓ Pn/R2 — pure (a″) is NOT enough (¬DualCnc≈-Pn-raw: bwf↓'s ∋:= lookup
    is a lookup, no congruence relaxes it); the HYBRID entry ⟦·⟧ᴴ is
    REQUIRED and fixes it (raw entry where expressible, retried at
    unfoldᵉ Γ A where not, abstract only when both fail).  Bonus finding:
    with the hybrid, the dual's read-back at Pn resolves through the dual's
    own copied reveal and the licensing premise holds SYNTACTICALLY;
  ✓ bad/bad₂ stay refuted under ≈; near-bad-by-a-different-route rightly
    admitted; genuinely different knowledge rejected;
  ✓ renaming: better than (a′) — the entrywise strengthening dissolves
    (UnfRen≈-abst is refl).  RESIDUAL: the hybrid entry commutes with
    renaming only up to ≼≈ (¬⟦⟧ᴴ-ren / ⟦⟧ᴴ-ren≼≈) — one ⊢retag≈ inside
    ⊢renameᵀ's (env) case;
  ✓ Merge's retyping-along-unfolding collapses into ≼≈ (both directions);
  ✓ the raw/unfolded mixture is coherent (mix-≼≈, idempotence, two-routes,
    abstraction barrier bit-identical).
  Λ-bound blocked case still stuck as expected → the no-abstract-value
  vacuity lemma is still the closing piece (bases proven, chain step a
  commented conjecture).

Design summary (before/after, home relations) presented to Jeremy for
sign-off; install pending his approval.
## E★ — the vacuity lemma is insufficient; the rep-less conceal ↓·:⋆ (2026-09-04)

    E★ = (ΛX. λf:(∀Z. ℕ→ℕ). ΛY. (f [Y]) 5) [ℕ] · (ΛZ. λn:ℕ. n)   : ∀Y. ℕ

    TyBeta(X); Wrap  ⇒  (ΛY. (((ΛZ. λn:ℕ. n) ⟪ ↓X:=ℕ ⟫) [Y]) 5) ⟪ ↑X:=ℕ ⟫
    ξ TyWrap(Z)      ⇒  (ΛY. ((λn:ℕ. n) ⟪ ↑Z:=Y , ↓X:=ℕ ⟫) 5) ⟪ ↑X:=ℕ ⟫
      Y is Λ-bound AND blocked: Z's entry is abstract under raw, hybrid, and
      unfolding alike — nothing to unfold.
    ξ Wrap on (…) · 5  ⇒  STUCK: the dual must conceal Z, no knowledge exists,
      and the argument is 5 : ℕ — so no-abstract-value says NOTHING here
      (the boundary's type ℕ→ℕ never mentions Z).

  Fix proposed to Jeremy (trace artifact "Scope Trace of E★"): the REP-LESS
  CONCEAL ↓Z:⋆, mirror of ↑Y:⋆ — re-hide the variable claiming nothing,
  licensed by nothing, slot blocked in baseS so no boundary type may depend
  on it; the dual emits it exactly when a reveal's knowledge is
  inexpressible and un-unfoldable.  Completed case split for the dual's
  conceal-of-a-reveal:
    knowledge expressible raw        → as today
    expressible after unfolding      → the (a″) copy
    inexpressible, named by the type → vacuous (no-abstract-value: no redex)
    inexpressible, not named         → ↓·:⋆
  Probe in flight (notes/StarConcealProbe.agda): E★ end-to-end before/after,
  bad-via-⋆ refutation, whether no-abstract-value stays load-bearing, dual-of-
  dual/renaming/retag behaviour of cnc⋆.

  RULING (Jeremy, 2026-09-04): conditional — "if the probe passes, install
  a″ with the star conceal."  His observation, recorded as the design's
  symmetry principle: "I suppose we should have expected to need a rep-less
  conceal because we already have a rep-less reveal."  Formal version: the
  entry syntax must be CLOSED UNDER DUALIZATION — the dual maps reveals to
  conceals and back, ↑Y:⋆ was forced by the dual re-introducing Λ-bound
  slots, so its dual image ↓Y:⋆ was inevitable; E★ is merely the program
  that makes the missing image observable.

## STAR-CONCEAL PROBE VERDICT — sound and required, NOT sufficient (2026-09-04)

notes/StarConcealProbe.agda (agda --safe clean, 1531 lines).  Per the
conditional mandate, (a″)+↓·:⋆ is NOT installed: a new counterexample.

What PASSED:
  ✓ E★ verified end-to-end (two index corrections: the dual's conceal is
    cnc 1 under the ΛY, and the dual's entry order is ↑Y:⋆ , ↑X:=ℕ , ↓Z);
    the fix types E★'s contractum, exact rebuild, final value at ∀Y.ℕ;
  ✓ cnc⋆ soundness clean: bad-via-⋆ refuted (the scope premise forbids a
    boundary type naming a ⋆-slot), no new route to variable-typed values,
    faces unchanged, renaming/retag trivial;
  ✓ closure under dualization confirmed (dual-of-dual round-trips; a
    cnc⋆-dropped slot duals to rvl⋆ when abstract, to the exterior's own
    knowledge when revealed);
  ✓ cnc⋆ is REQUIRED regardless of E★: today's dual of a boundary containing
    rvl⋆ mints cnc j ℕ, which is ALREADY unlicensable (¬DualCnc-rvl⋆) and
    reachable — E★'s own dual contains a rvl⋆;
  ✓ the DualCnc case split: raw and unfoldable knowledge are the standing
    (a″) obligations; the inexpressible-and-unneeded case is now a THEOREM
    (cnc⋆-licensed); no-abstract-value is no longer needed for DualCnc.

What FAILED — the new counterexample E★′ (both regimes), full trace:

    E★′ = (ΛX. λf:(∀Z.(Z→ℕ)→(Z→ℕ)). ΛY. (f [Y]) (λy:Y. 5)) [ℕ]
            · (ΛZ. λg:(Z→ℕ). λz:Z. g z)      : ∀Y. Y→ℕ

    TyBeta(X)  ((λf:(∀Z.(Z→ℕ)→(Z→ℕ)). ΛY. (f [Y]) (λy:Y. 5)) ⟪ ↑X:=ℕ ⟫)
                 · (ΛZ. λg:(Z→ℕ). λz:Z. g z)
    Wrap       (ΛY. (((ΛZ. λg:(Z→ℕ). λz:Z. g z) ⟪ ↓X:=ℕ ⟫) [Y]) (λy:Y. 5))
                 ⟪ ↑X:=ℕ ⟫
    ξ TyWrap(Z)  (ΛY. ((λg:(Z→ℕ). λz:Z. g z) ⟪ ↑Z:=Y , ↓X:=ℕ ⟫) (λy:Y. 5))
                 ⟪ ↑X:=ℕ ⟫
       — Y Λ-bound AND blocked: Z's entry abstract, nothing to unfold; the
         boundary's type (Z→ℕ)→(Z→ℕ) NAMES Z.
    ξ Wrap     STUCK.  The argument λy:Y.5 is a VALUE at the arrow type Y→ℕ
       (the external face of the domain Z→ℕ), so no-abstract-value is silent.
       Attempt 1, rep-keeping dual  ↓Z:=Y , ↑Y:⋆ , ↑X:=ℕ : both faces are
       exactly right (face-int-E★′, face-ext-E★′, sc-live-E★′) — only
       bwf↓'s knowledge lookup fails (¬⊢T4′).
       Attempt 2, star dual  ↓Z:⋆ , ↑Y:⋆ , ↑X:=ℕ : licensed by nothing, but
       the re-hidden slot is blk and the dual cannot express its own
       boundary type Z→ℕ (¬Scoped-⋆-E★′, ¬⊢T4′⋆).

  Same shape as E★, but B₁ = Z→ℕ NAMES Z, and the argument λy:Y.5 is a
  VALUE at the arrow type Y→ℕ — reachable, and vacuity is silent.  At the
  Wrap: if the dual conceals with the rep kept (↓Z:=Y), then both faces are
  already EXACTLY right (face-int-E★′, face-ext-E★′, sc-live-E★′) and the
  ONLY defect is bwf↓'s knowledge lookup (Z's entry is abstract); if the
  dual conceals with ↓Z:⋆ instead, then the re-hidden slot is blk and the
  dual cannot express its own boundary type Z→ℕ (¬Scoped-⋆-E★′).  So cnc⋆
  trades a boundary failure for a scope failure exactly when the type
  mentions the unknowable reveal.

Probe's recommendation: candidate (b) for rep-carrying reveals — a
DUAL-ONLY conceal that KEEPS the rep and is licensed by the reveal it
cancels (Zdancewic Lemma A.2, Reversal) rather than by interior knowledge —
with cnc⋆ retained for duals of rvl⋆.

RULING (Jeremy, 2026-09-04): probe the candidate premises for (b); a full
design description of (b) to follow the probe.

(b)-PROBE VERDICT (notes/DualLicenseProbe.agda, agda --safe clean):
(b3)-SOUND WINS; (b1) and (b2) refuted; the NAIVE (b3) was itself unsound
(an adversary reuses a planted x-entry in a non-dual boundary, ⊢3n-adv) and
is repaired by the load-bearing "claims nothing" premise.  Full design
description with example, before/after rules and homes, the soundness
story, the uncovered obligations, and the one open renaming lemma:
notes/DualLicenseDesign.md.  Awaiting Jeremy's sign-off on that design
(and on §5's choice (i) vs (ii)) before the combined install.  In flight
(notes/DualLicenseProbe.agda), three candidates against the E★′/E★/Pn/bad/
bad₂/near-bad gauntlet:
  (b1) read-back identity (concealing-then-revealing is the identity on the
       slot's face) — expected to produce garbage past rep-less reveals;
  (b2) the face laws themselves as the bwf↓ premise — expected to be
       whole-boundary, not per-entry, and possibly circular;
  (b3) an exterior-read knowledge entry `xrvld A` in the interior (minted by
       ⟦·⟧ when a rep-carrying reveal's knowledge is neither expressible nor
       unfoldable; consumed ONLY by a new bwf↓ clause with syntactic rep
       equality — the homes align: the x-entry's rep and a dual conceal's
       rep both live over the same context).  Also probed: whether (b3)
       subsumes the (a″) hybrid at Pn, and the structural argument ruling
       out (b4) (a co-boundary-parameterized judgment: the contractum must
       be typed by plain env).
## D1 PROBE VERDICT — root cause pinned; A SOUNDNESS HOLE in the landed license; the SkelEq repair (2026-09-04)

notes/D1Probe.agda (agda --safe clean).  Answers to Jeremy's two questions:

ROOT CAUSE — CONFIRMED, one line: x-entry reps rename by the EXTERIOR ρ
(entRen₂), conceal reps by the induced INTERIOR renaming (renᴮ).  The
divergence class is exactly "ρ differs from the induced interior renaming
on the rep's support" — and it contains EVERY weakening, because an x-entry
forces a conceal, and a conceal absorbs suc outright.  A renaming inserting
deeper than cmax leaves the comparison intact, so the class is proper.
CORRECTION: DualLicenseDesign §2's "the homes align" was false — the two
reps are identified only through the rebuild.  The rebuild-relative
comparison (Jeremy's re-alignment instinct) HOLDS AT BIRTH — xrep-stored is
the x-analogue of cancel-agree, the two reps are syntactically equal at
every dual's birth — but is NOT renaming-stable, fatally: after an absorbed
weakening the rebuild has fewer slots than the ambient context (¬rebuild-ren
— ≼≈ is FALSE, not unproven).

PROPAGATION — WORSE THAN FEARED.  CORRECTION to this file's earlier claim
"the comparison never was the load-bearing part": REFUTED.  starOnly is
vacuously true of CLOSED types (starOnly Θ d ℕ = true), so the landed
(bwf-↓x) licenses  ↓Z:=ℕ  at an x-slot — asserting "Z is ℕ" with no
justification.  Machine-checked: ⊢Tg exports 7 at the Λ-bound Y through
E★′'s own x-slot; ⊢Tbad is bad's configuration one indirection away,
reached via the ⊢retag≈ transport TyBeta performs.  The dropped comparison
is exactly what refuses it (would-refute-≡/-≈).  The same hole was in the
original absOnly form.  Once depth-1 values land, ⊢Tg's term becomes a
stuck Merge redex — a progress failure.

THE REPAIR — SkelEq (found by the probe): compare the conceal's rep with
the recorded one by SKELETON (constructor tree with variable positions
identified) — stable under arbitrary independent renamings with NO
hypotheses (skel-ren), so it survives exactly the drift that killed ≡ and
≈Δ̄, while still refusing ↓Z:=ℕ against a recorded variable (closing the
hole) and the ⊢3n-adv adversary, and admitting the whole gauntlet.

    (bwf-↓x)   Γ ∋ X:=ˣA′     starOnly Θ 0 A ≡ true     SkelEq A A′
               Ψ ⊢ A
               ──────────────────────────────────────────────────
               Γ ∣ Ψ ⊢ ↓X:=A , Θ

Cost: ⊢renameᵀ's hx hypothesis strengthens to SkelX (weaker than the
rejected XRen; both live call sites already satisfy it — SkelX-suc,
SkelX-mv).  Bonus: SkelEq + xrep-stored discharge MERGE'S cancel-agree for
x-pairs, so the deleting cancel keeps its justification.

MERGE VERDICTS: the TOPLAS three-agent adversary CLEARS our deleting cancel
(their term is conceal-of-conceal — our cancel never fires; the appended
merge types, the middle authority discharging Reversal through ≈Δ̄; the
variant where cancel DOES fire survives via the agreed rep).  APPEND-ONLY
IS REFUTED FOR US (¬bwf-append: exterior-relative conceal indices make the
appended boundary inadmissible — theirs works only over a global
namespace); the faces-agree strip is unsound except at Θ = ∅ (= Drop∅).
Towers collapse via DELETING merge + strip at a closed B₀ — which needs
cancel-agree anyway.  So the ranked recommendation is unambiguous:

  (i) REPAIR (bwf-↓x) WITH SkelEq — RULED BY JEREMY AND LANDED (commit
      "the SkelEq repair").  ⊢Tg/⊢Tbad are now permanent refutations in
      Boundary.agda; ¬⊢adv reconfirmed; CncLic's x-disjunct carries the
      SkelEq conjunct at zero residual cost (dual-cnc-skel discharges it
      at every dual's birth via xrep-stored); D1 is CLOSED — the landed
      license now reads: x-lookup + starOnly + SkelEq + Ψ ⊢ A.
  (ii)/(iii) accepting D1, with either cancel flavor: refuted or dominated.

## DESIGN LAW, restated by Jeremy via the trace coloring (2026-09-04)

"Another way to think about the tightness property that I'm going for is
that THE COLOR OF A NON-BOUNDARY TERM SHOULD NEVER CHANGE DURING REDUCTION."

I.e. reduction never changes which type variables a non-boundary subterm
can see — scope regions are preserved; only boundary syntax moves.  Two
instances already in the calculus: TyWrap consumes a Λ but its body keeps
its color (the binder's slot becomes the boundary's reveal slot — same
scope, new binder site); Wrap moves an argument inside a dual whose
interior REBUILDS exactly the context the argument was colored by — the
argument keeps its color, which is the DualInt law stated visually.  A
candidate rule that recolors a non-boundary term is thereby suspect on
sight.  Recorded next to tightness / no-term-shifts / simultaneity /
closure-under-dualization.

## THE X-LICENSE INSTALL — LANDED (e07e8863), WITH THREE DEVIATIONS (2026-09-04 night)

Gates green (cold make check + notes/InstallGauntlet.agda, worktree and main
tree).  E★′ closed through (bwf-↓x); E★ needs no cnc⋆ under the x-license;
bad/bad₂/far-bad refuted, near-bad admitted, dual-of-dual exact.  Honest
scorecard: preservation did NOT become unconditional — three parameters
remain, materially smaller (DualRep≈ wants ⊢ Δ; DualCnc≈ is a per-reveal
disjunction whose residue is exactly the Pn shape; DualInt≈ the rebuild law).

Deviations from the ruled design, all machine-checked, FOR JEREMY'S REVIEW:

  (D1) (bwf-↓x) carries NO rep comparison — neither ≡ nor ≈.  Ruling (ii)
       does not survive ⊢renameᵀ at this clause: under a weakening the
       x-entry's rep moves by the exterior renaming while renᴮ freezes the
       conceal's stored rep, and the two end a genuinely-abstract slot
       apart even up to unfolding (¬x-rep-match-ren≈, InstallGauntlet §7b).
       The license is: the x-LOOKUP (the slot is x-marked) + the
       claims-nothing premise + Ψ ⊢ A.  The whole soundness gauntlet turns
       on claims-nothing (the ⊢3n-adv rep MATCHES on both sides — the
       comparison never was the load-bearing part, confirming (ii)'s
       orthogonality expectation from the wrong direction).
  (D2) Claims-nothing is the BOUNDARY-relative `starOnly Θ` ("the rep names
       only rep-less reveal slots of Θ"), not the interior-relative absOnly:
       the interior form is anti-monotone in knowledge and dies at the
       abst↦rvld retag TyBeta/TyWrap perform.  Same verdicts on the whole
       gauntlet.
  (D3) The ambient unfold retry in ⟦·⟧ is NOT installed: an ambient-
       dependent interior breaks both required transports (renaming:
       ¬UnfRen-hk; knowledge-monotonicity: a further-resolved rep may name
       a blocked slot).  Price: Pn's dual conceal is unlicensed again and
       is now EXACTLY the DualCnc≈ residue.  The congruence ≈Δ̄ itself,
       Reversal≈, ≼≈, and the dual's second-chance unfolded copy ARE
       installed and carry Pc.

Open questions this leaves (beyond the roadmap): whether to accept (D1)'s
comparison-free license as final (the rep is still constrained by starOnly
+ Ψ ⊢ A, and the faces use it; but "the conceal repeats the recorded rep"
is now unchecked — is that acceptable, or should the x-entry itself be
REDEFINED to be renaming-stable so a comparison can return?), and whether
Pn's residue is acceptable pending Merge (Merge-first unfolds Pn's chain in
the cases that reach eliminations — to check at the Merge landing).

## THE TOPLAS FOLLOW-ON (notes/SyntacticTypeAbstraction.md, 2026-09-04)

Jeremy pushed p1037-grossman.pdf ("Syntactic Type Abstraction", the journal
version, WITH a System F treatment).  Digest highlights, as they bear on our
open items:

  * OUR E★′-CLASS CONFIGURATIONS ARE UNREACHABLE FOR THEM — dissolved
    upstream by a global type-variable namespace plus eager retag, not
    solved.  Reconstructing E★′ inside their own encoding yields exactly an
    ordinary δ-entry `Z=Y` with Y Λ-bound and in nobody's domain — i.e. our
    `Z:=ˣY` — compatible precisely because Y is nobody's key.  Independent
    support for (bwf-↓x) + the "claims nothing" premise; ruling (ii) intact
    (the paper has no transport hypotheses anywhere — substitution is a
    judgment-level lemma).
  * (a″) VALIDATED WITH A WARNING: they keep eager retag [7] AND (eq)-at-Δ̄;
    p. 1049 notes relaxing eagerness needs "additional proof-normalization
    arguments" — our ≈Δ̄ congruence is exactly that normalization.
  * MERGE: their [8] APPENDS AND NEVER DELETES; a three-agent counterexample
    (p. 1048–49: δ_i(t)=int, δ_j(s)=t, δ_k=⊥) shows dropping authority
    breaks abstraction.  Our ⊕ deletes matched ↑X/↓X pairs (cancel).  Before
    Merge lands: build the cancel adversary on their example; if cancel
    fails, fall back to append-only merge + Drop∅ (which we adopted anyway).
  * B₂′ ANSWERED: keep the OUTER boundary type; the ⊕ obligation is "the
    middle type is abstract to the middle boundary" ([trans] + Idempotence
    is their entire preservation case for merge).
  * PRESERVATION STRENGTHENING to adopt: the outgoing context REFINES the
    incoming one (their Def. 5.4 / Lemma 5.5) — a grounded invariant our
    statement does not yet carry.
  * Depth-1 values + canon-var-conceal are literally their Lemma 3.2 third
    clause; under polymorphism their VALUE-HOOD IS DYNAMIC (p. 1074) —
    expect our Value to become Δ-indexed at the depth-1 step.

## AGENDA ITEM 1 IN DETAIL — R2 / DualCnc, by example (2026-09-04)

The program (ordinary System F; the essential move is instantiating an
imported polymorphic value AT AN ABSTRACT VARIABLE, f [Y] — Example 8's core):

    Pn = (ΛX. λf:(∀Z.Z→Z). ΛY. λy:Y. f [Y] y) [ℕ] · (ΛZ. λz:Z. z) · [𝔹] · true   : 𝔹

    TyBeta(X)  ((λf:(∀Z.Z→Z). ΛY. λy:Y. f [Y] y) ⟪ ↑X:=ℕ ⟫) · (ΛZ. λz:Z. z)  [𝔹] · true
    Wrap       ((ΛY. λy:Y. (((ΛZ. λz:Z. z) ⟪ ↓X:=ℕ ⟫) [Y]) y) ⟪ ↑X:=ℕ ⟫)  [𝔹] · true
    TyWrap(Y)  ((λy:Y. (((ΛZ. λz:Z. z) ⟪ ↓X:=ℕ ⟫) [Y]) y) ⟪ ↑Y:=𝔹 , ↑X:=ℕ ⟫) · true
    Wrap       ((((ΛZ. λz:Z. z) ⟪ ↓X:=ℕ ⟫) [Y]) · (true ⟪ ↓Y:=𝔹 , ↓X:=ℕ ⟫)) ⟪ ↑Y:=𝔹 , ↑X:=ℕ ⟫
    ξ TyWrap   (((λz:Z. z) ⟪ ↑Z:=Y , ↓X:=ℕ ⟫) · (true ⟪ ↓Y:=𝔹 , ↓X:=ℕ ⟫)) ⟪ ↑Y:=𝔹 , ↑X:=ℕ ⟫

  All well typed so far.  The inner TyWrap minted, at exterior Γn = Y:=𝔹 , X:=ℕ:

    Θn = ↑Z:=Y , ↓X:=ℕ          interior:  Z ABSTRACT

  Z's entry should be the knowledge "Z is Y", but ⟦·⟧ reads Θn ALONE, and in
  Θn's interior Y is BLOCKED (↓X drops everything up to X, including the
  shallower Y): no interior reading exists, so the entry falls back to
  abstract.  "Z is Y" — and via Γn, "Z is 𝔹" — is known ambiently, recorded
  nowhere in Θn.

  The failing step: the last Wrap's dual must CONCEAL Z (duals turn reveals
  into conceals), and a conceal ↓Z:=A₀ is licensed only by interior knowledge
  Ψn ∋ Z := A₀ — which does not exist.  Contractum untypable.  That is
  DualCnc's counterexample; the dual's REVEAL block is fine (↑Y:=𝔹 copied
  from Γn, ↑X:=ℕ from the conceal) — only the conceal-of-a-reveal side is
  stuck.

  Candidates, on Pn:

  (a) KNOWLEDGE CLOSURE IN ⟦·⟧ — compute the entry with the ambient Γ: when
      a reveal's rep names a blocked variable, resolve it through Γ's
      knowledge first.  At the ξ TyWrap step, ⟦Y⟧ under Γn unfolds Y:=𝔹, so
      Z's entry is Z:=𝔹; the dual's ↓Z:=𝔹 is licensed and the rebuild is
      exact.  FIXES Pn.  The residual case — same shape with Y still
      Λ-bound — is conjectured VACUOUS: the failing Wrap needs a VALUE of
      type Y, and no value inhabits an abstract variable's type (a value at
      variable type is a wrapper chain that can only terminate in a conceal,
      and a conceal of an abstract variable is unlicensed by the restored
      invariant).  New lemma to prove: no-abstract-value.  If it holds, (a)
      closes DualCnc completely.  Cost: intOf consults Γ's entries (it
      already takes Γ; renaming transport rides ⊢renameᵀ's ∋:= hypothesis).
      bad/bad₂ unaffected (their failure is the conceal check).

  (b) SELF-JUSTIFYING DUAL CONCEALS — a marked entry ↓Z:≈A minted only by
      dualᴳ, licensed by the read-back law against the reveal it cancels
      (A = the reveal's own rep; Zdancewic's Reversal lemma made syntactic).
      On Pn: ↓Z:≈Y, Y in scope in the dual's interior (= Γn).  Spot-checks:
      read-back alone still refutes bad (ℕ ≠ ∀Z.Z→Z) and bad₂.  Cost: a
      fourth entry form whose typing reaches across to ANOTHER boundary —
      the kind of non-local premise the design has avoided.  Probe first.

  (c) MERGE-FIRST — REFUTED AS A COMPLETE SOLUTION BY Pn.  Merge fuses only
      adjacent wrappers.  In the E8-shape (sealed value = the Λ-body) TyWrap
      creates the adjacency and Merge dissolves Θn (the cancel unfolds
      ↑Z:=Y against ↑Y:=𝔹 into ↑Z:=𝔹).  In Pn the sealed value sits in
      APPLICATION position inside the boundary — never wrapper-on-wrapper —
      and Merge cannot reach it before the failing Wrap.  Shape-dependent;
      not an R2 fix on its own.

  RECOMMENDATION: (a) + the no-abstract-value lemma, probed before install.
  (b) is the fallback if the vacuity lemma fails; (c) stays desirable for
  Decision 3 but does not resolve R2.

## Decision 2 — a boundary meets a type application

Both well typed on every step of Example 8 (notes/old/Example8Trace.agda).

    (TyWrap)   (V ⟪ Θ , ∀Z.B₀ ⟫) @B[A]        -→  (V @(B₀[γΘ])[Z]) ⟪ ↑Z:=A , Θ , B₀ ⟫
    (TyWrap′)  ((ΛZ.V) ⟪ Θ , ∀Z.B₀ ⟫) @B[A]   -→  V ⟪ ↑Z:=A , Θ , B₀ ⟫

  TyWrap: total in V (Zdancewic §4.1's sketch); leaves a nested boundary per
  use.  TyWrap′: one boundary, but stuck when the body is a boundary (which
  Wrap produces) — needs Merge.  TyWrap is what the Agda has (constructor TyWrap).

### Decision 2 — resolution (2026-09-03)

Jeremy: TyWrap.  "It would yield a more consistent calculus … because that
mirrors the way Wrap works for function typed values" — both rules float the
elimination inside the boundary and are total in the wrapped value.  TyWrap′
is at most a later optimisation (and would need Merge).  No change to the Agda.

## Decision 3 — nested boundaries: merge, or let them pile up?

Option 3a — depth-1 values (Zdancewic rule (8), p. 203):

    (Merge)   (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫   -→  V ⟪ Θ₁ ⊕ Θ₂ , B₂ ⟫
    values:   c | λx:A.N | ΛX.V | V ⟪ Θ , B₀ ⟫   with V not itself a boundary

  Θ₁ ⊕ Θ₂ keeps all entries of both, except a conceal ↓X:=A in Θ₁ of a
  variable revealed ↑X:=A by Θ₂ cancels against it — sound only under 1a.
  Obligations: contexts compose, internal face composes (their (trans)),
  external face unchanged (notes/Zdancewic-embeddings.md §4).

### Decision 2 — REVISED to TyWrap′ (Jeremy, 2026-09-04)

The 2026-09-03 objection to TyWrap′ (partial: the body must be syntactically
Λ) dissolves under Decision 3: with depth-1 values a wrapper-bodied wrapper is
a Merge redex, and after merging, a value wrapped at a ∀-shaped B₀ has a Λ
body by canonical forms.  And TyWrap′ has NO ⇑ᵀ on the term — the shift in
TyWrap existed only because it declined to consume the Λ (the Λ-binder's slot
IS the new reveal slot) — so the switch also discharges the no-term-shift
principle's one exception.  Ruling: switch to TyWrap′; the notes.md rule name
stays TyWrap (its definition changes to the direct-combine shape):

    (TyWrap)  ((ΛY.V) ⟪ Θ , ∀Y.B₀ ⟫) @B[A]   -→   V ⟪ ↑Y:=A , Θ , B₀ ⟫

  (conceal reps still shift — types, not terms).  Progress at a ∀-faced
  wrapper: Λ body → TyWrap; wrapper body → Merge (a ProgressDef parameter
  until Merge lands).  W3 is still needed and now acts in TyBeta and TyWrap
  (both upgrade a Λ-bound slot above inner boundaries to revealed).
  Follow-up ruling (Jeremy, 2026-09-04, same day): switch Wrap too, from the
  lazy/float form to PUSH-THROUGH-THE-LAMBDA, symmetric to TyWrap′ — consume
  the ƛ and β-substitute the dual-wrapped argument in one step:

    (Wrap)  ((λx:B₁′. N) ⟪ Θ , B₁→B₂ ⟫) · W  -→  N[x := W ⟪ Θᵈ , B₁ ⟫] ⟪ Θ , B₂ ⟫

  (this is PLAN §4's original sketch, before the memo generalised it to the
  total float form).  The dual Θᵈ and its face laws are unchanged, so
  Decision 4 / W3 is unaffected.  Totality: a wrapper-bodied wrapper at a
  ⇒ face waits for Merge, exactly as at a ∀ face — progress carries two
  further ProgressDef parameters (NestedApp, NestedTApp) until Merge lands.
  No term shift anywhere: _[_]ᵐ substitutes term variables only.

### Decision 3, addendum (Jeremy, 2026-09-04): Drop∅ ships WITH Merge

    (Drop∅)   V ⟪ ∅ , B₀ ⟫   -→   V          both faces are B₀; long proven safe

Merge's cancel clause empties matched boundaries (e.g. the cancel pair
(7 ⟪ ↓X:=ℕ ⟫) ⟪ ↑X:=ℕ ⟫ merges to 7 ⟪ ∅ ⟫), so without Drop∅ towers
collapse to a vacuous wrapper rather than the bare value.  Adopt both in
one landing: rule + example + preservation + progress cases each, per the
§1 Method.  Note Drop∅ finally becomes REACHABLE at that point (today no
rule mints an empty boundary).

### Decision 3 — resolution (2026-09-03)

Jeremy leans to 3a (Merge, depth-1 values).  Plan: after the Decision-1
rework lands, (i) define Θ₁ ⊕ Θ₂ and probe the three obligations (contexts
compose; internal face composes given the middle type; external face
unchanged — notes/Zdancewic-embeddings.md §4); (ii) add `Merge` with its
example and preservation case (cancel clause discharged by `cancel-agree`);
(iii) restrict `Value` so a wrapper's body is not itself a wrapper, and
adjust `Wrap`/`TyWrap`'s progress cases and canonical forms accordingly.

Option 3b — towers as values, no Merge (current, to be replaced).  Canonical form at a
  variable type = a chain of boundaries ending in a conceal; Examples
  1,2,5,6,7 end at towers; progress still needs Decision 1.

## Recommendation

Settled: TyWrap′ and push-through Wrap (both revised 2026-09-04); Merge (3a).  Decision 1: restore the invariant in the REVERSAL
form (probe-verified).  Awaiting Jeremy: W3 vs W4 (Decision 4).  Then: Boundary.agda
rework (reversal premise + W3/W4) and re-run of every preservation case → Merge with
retyping-along-unfolding → depth-1 values → progress.

## THE MERGE + DROP∅ LANDING — LANDED, ONE OPEN RULING (2026-09-04 night)

Gates green cold (`make -C strong check` + InstallGauntlet `--safe`). The rules as landed
(`BReduction.agda`):

```agda
Merge : Value V
      → MergeOK Δ Θ₁ Θ₂ B₁ B₂
      → Δ ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ -→ V ⟪ Θ₁ ⊕ Θ₂ , mrgB Θ₁ Θ₂ B₁ ⟫

Drop∅ : Value V
      → Δ ⊢ V ⟪ [] , B₀ ⟫ -→ V
```

`Θ₁ ⊕ Θ₂ = mapL Θ₂ Θ₁ ++ mapR Θ₁ 0 Θ₂`: Θ₁'s reveals stay, reps pushed out through Θ₂;
a Θ₁-conceal (or `cnc⋆`) of a Θ₂-reveal slot CANCELS both (the clause is on the index, not
the flavour — sound because only a `rvl`/`cnc` pair transports a rep, and that pair is
`cancel-agree`); surviving conceals re-index. Both preservation cases are FULLY PROVEN, no
new parameters: `⊕-γ` (the internal face composes on the nose), `cancel-agree` re-derived
as a theorem on the live core (ordinary pairs; x-pairs are `xrep-stored`/`dual-cnc-skel`),
body transport = `⊢retag≈` along `≼≈` — so "retyping-along-unfolding = ≼≈" is now USED,
not just probed. Worked examples in gauntlet §9: the cancel pair
`(7 ⟪ ↓X:=ℕ ⟫) ⟪ ↑X:=ℕ ⟫ → 7 ⟪ ∅ ⟫ → 7`, E★′'s continuation tower (the reachable x-pair
cancel — exact, `⊢merged-★`), Example 3's tower merged twice, and the TOPLAS three-agent
shape (`⊢merged-ag` — types with both authorities kept, NO abstraction breach).

DEVIATION (grounded, not a parameter): `Merge` carries `MergeOK` as a rule premise —
`cmax Θ₁ ≤ revs Θ₂`, bwf + Scoped + `≼≈` for the composite, and the external-face
equation `substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≡ substᵗ (ρᵇ Θ₂) B₂`. A `MergeDef`
parameter was NOT used because the residues are FALSE as universal statements (below).

PROGRESS SCORECARD: `RevealVarApp`/`RevealVarTApp` DIED — theorems inside
`Progress.Impl`, no new hypothesis: at a reveal-variable face `γᵇ Θ X = \` X` (`γᵇ-lo`),
so the wrapper's body is a value of variable type, hence itself a wrapper by `canon-var` —
the redex was a wrapper-bodied wrapper all along, and `ξ-·-l (Merge v ok)` steps it.
`NestedApp`/`NestedTApp` remain, reduced to exactly "supply `MergeOK`".

### Decision 5 — ⊕ must keep the abstract witness (NEEDS A RULING)

Why progress did not close: `MergeOK` is falsifiable. The example (gauntlet §9d(i),
`⊢redex-cx`/`¬ext-cx`/`¬⊢merged-cx`):

```
Δ = X:=ℕ  ⊢  ((ƛ y:W. 3) ⟪ ↑W:=ℕ , W⇒ℕ ⟫) ⟪ ↓X:=ℕ , X⇒ℕ ⟫  :  X⇒ℕ
```

(No cancel fires here — W's reveal and X's conceal sit at different slots; the cancel
variant of the same failure is §9d(ii).)  If Merge fires with the current ⊕, then the
result is (`Θcx1 ⊕ Θcx2 ≡ rvl ℕ ∷ cnc 0 ℕ` and `mrgB Θcx1 Θcx2 (W⇒ℕ) ≡ W⇒ℕ`, both
by `refl` in the gauntlet):

```
(ƛ y:W. 3) ⟪ ↑W:=ℕ , ↓X:=ℕ , W⇒ℕ ⟫

  internal face:  (γᵇ) W⇒ℕ = ℕ⇒ℕ   ✓ matches the body
  external face:  (ρᵇ) W⇒ℕ = ℕ⇒ℕ   ✗ the redex has X⇒ℕ   (¬ext-cx)
```

The flattening lost the outer boundary's re-abstraction step: in the nested redex the
inner wrapper exports ℕ⇒ℕ into the middle region and the outer conceal re-abstracts
that to X⇒ℕ; in the composite, ρᵇ reads ↑W's rep — kept as the RESOLVED ℕ by mapL's
push-out — directly in the exterior, so the wrapper exports ℕ⇒ℕ and X's abstraction
is dropped (exactly TOPLAS's authority warning, reachable at an ⇒ face; `¬⊢merged-cx`
— the merged wrapper is not typable at X⇒ℕ).  This bad term is never actually
produced: MergeOK's external-face premise refuses it, so Merge does not fire — which
is precisely why `NestedApp` is unprovable and progress stalls on this redex.  But a
CORRECT merged boundary exists and types (`⊢repair-cx`):

```
(ƛ y:W. 3) ⟪ ↑W:=X , ↓X:=ℕ , X⇒ℕ ⟫        -- re-abstract W AT X, not at ℕ
```

— the reveal is kept, re-abstracted at the OUTER conceal's variable (the abstract
witness) instead of its resolved rep; both faces are then exact and the interior is
identical. Same story for the alias/x-pair shape (§9d(ii), `⊢repair-al`: keep Θ₂'s reveal
rather than the alias's ⋆-slot). And B₂′ is NOT a mrg₁-vs-mrg₂ coin flip — both are
machine-refuted in opposite directions (`¬γ-mrg₂-tower`: TOPLAS's keep-the-outer fails on
Example 3's tower; `¬ρ-mrgB-ag`: the landed pushed-out form fails on the three-agent
shape). The pattern in all four verdicts: the transport is wrong exactly when it
RESOLVES a cancelled reveal's rep through an enclosing conceal instead of naming that
conceal's variable.

THE PROPOSAL: change `mapL` so a Θ₁-reveal whose rep crosses a Θ₂-conceal is re-abstracted
at that conceal's variable (⊕ consults Θ₂'s conceals, not only its reveal count). If this
holds up, both `MergeOK` faces plausibly become theorems, `MergeOK` shrinks or vanishes,
and `NestedApp`/`NestedTApp` — the last two progress parameters — close.

Also flagged for later: `cmax Θ₁ ≤ revs Θ₂` (⊕-γ's side condition) is sufficient, not
necessary — it over-refuses conceal-of-conceal, the very TOPLAS-adversary shape whose
merge IS sound (`⊢merged-ag`); Merge simply doesn't fire there (no stuckness: such
towers are values pending depth-1).

### Decision 5, addendum (Jeremy's question, 2026-09-04 night): why ↑W:=ℕ
### and not ↑W:=X — the redex is REACHABLE, and the machine is STUCK there

Jeremy asked why the counterexample's inner boundary carries `↑W:=ℕ` rather
than the witness form `↑W:=X`.  The answer upgraded Decision 5's severity,
so it is recorded in full (machine-checked: gauntlet §9f).

WHERE A REVEAL'S REP COMES FROM.  A rep is minted by `TyBeta` as the
LITERAL type argument at the application site:

```agda
TyBeta : Value V → Δ ⊢ (Λ V) ·[ B , A ] -→ V ⟪ rvl A ∷ [] , B ⟫
```

So the question "ℕ or X?" is "what did the source program write at
`·[_]`?" — and that depends on whether X is NAMEABLE at that site.  Inside
`↑X:=ℕ`'s interior it is (`rvld` slot), and there the source writes `·[X]`
and the landed ⊕ is exact.  But in the PLAIN EXTERIOR — after the `ΛX` was
eliminated — X does not exist, and `ℕ` is the only spelling of that type;
inside `↓X:=ℕ` likewise (`intOf` DROPS the concealed slot: tightness).
The counterexample's form is therefore not exotic; it is what any client
that instantiates its own `ΛW` OUTSIDE the package produces.

THE WHOLE TRACE (gauntlet §9f: `cxP₀ … cxP₄`, `cx-step₁ … cx-step₄`,
`⊢cxP₀`, `⊢cxP₄`, all live inhabitants).  A closed plain System F source:

```
P = ((ΛX. λx:X. λf:X⇒ℕ. f·x) ·[X⇒(X⇒ℕ)⇒ℕ, ℕ] · 5) · ((ΛW. λy:W. 3) ·[W⇒ℕ, ℕ])

T1 TyBeta(X):  the package opens
    → ((λx:X. λf:X⇒ℕ. f·x) ⟪ ↑X:=ℕ , X⇒(X⇒ℕ)⇒ℕ ⟫ · 5) · ((ΛW. λy:W. 3) ·[W⇒ℕ, ℕ])
T2 Wrap(5):    5 crosses in as the abstract x; dualᴳ mints ↓X:=ℕ
    → (λf:X⇒ℕ. f · (5 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , (X⇒ℕ)⇒ℕ ⟫
        · ((ΛW. λy:W. 3) ·[W⇒ℕ, ℕ])
T3 TyBeta(W):  the client's Λ opens IN THE EXTERIOR — ↑W:=ℕ is FORCED,
               X is not a name here
    → (λf:X⇒ℕ. f · (5 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , (X⇒ℕ)⇒ℕ ⟫
        · ((λy:W. 3) ⟪ ↑W:=ℕ , W⇒ℕ ⟫)
T4 Wrap:       the client's function crosses in — the §9d(i) nesting
    → ( ((λy:W. 3) ⟪ ↑W:=ℕ , W⇒ℕ ⟫ ⟪ ↓X:=ℕ , X⇒ℕ ⟫)
          · (5 ⟪ ↓X:=ℕ , X ⟫) ) ⟪ ↑X:=ℕ , ℕ ⟫
```

STUCK — MACHINE-CHECKED (`stuck-cx`, `stuck-cxP₄`): the post-T4 term is
well-typed at ℕ (`⊢cxP₄`), is not a value, and NO rule fires on it: the
only candidate on the active redex is `Merge` via ξ-·-l, and `MergeOK`'s
external-face component is exactly `¬ext-cx`.  So this is no longer just
"NestedApp is unprovable": `cxP₄` is a reachable counterexample to TYPE
SAFETY of the calculus as it stands.  Decision 5 (or a change to `Value`)
is REQUIRED, not optional.

THE CROSSING IS THE GAP.  T4's dual re-expresses the crossing term's
boundary TYPE from interior to exterior coordinates (X⇒ℕ), but the reps of
boundaries ALREADY INSIDE the crossing term keep their exterior spelling
(↑W:=ℕ).  The re-abstraction ℕ↦X is exactly what Decision 5 asks ⊕ to
perform at merge time — and it is the INVERSE of the conceal's interior
reading γᵇ, which is relational in general (which ℕs become X?  In
`⊢repair-cx` the whole rep; for a rep like ℕ⇒ℕ under ↓X:=ℕ the candidates
X⇒ℕ / ℕ⇒X / X⇒X differ).  The external-face equation (B₂'s positional
alignment) is what selects the right one — so the repaired ⊕ must consult
Θ₂'s conceals AND B₂, or equivalently Zdancewic's Δ̄ backward reading.

CONTRAST, machine-checked (`run-repair-cx`): with the repaired boundary
`Θcx′ = ↑W:=X , ↓X:=ℕ` in place of the un-mergeable nesting, `Wrap` fires
and the program runs on to 3.

AND THE REPAIRED RUN FINISHES (`run-repair-tail`, fully-discharged
`MergeOK`): `(3 ⟪ ↑W:=X , ↓X:=ℕ , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫` merges — the ↓X/↑X
pair CANCELS and W's rep resolves to ℕ legitimately, the outward crossing
passing the reveal that publishes X:=ℕ.  Final value: `3 ⟪ ↑W:=ℕ , ℕ ⟫`.
The resolved spelling ℕ is CORRECT in the plain exterior; it was wrong
only across ↓X:=ℕ — Decision 5 in one example.

### Decision 5, REFRAMED by Jeremy at the §9f review (2026-09-04 night):
### the linkage lives in the FACE TYPES — and Merge cannot be the whole story

Jeremy, reading the §9f trace: "W and X are not really tied to each other,
they just both happen to have the same rep type, and that means a revealed
W can line up with a concealed X" — and then: "the merge operator needs to
know the face types, because it's the face types that cause W and X to be
linked."  Both confirmed, machine-checked (gauntlet §9g); the second has a
machine-checked LIMIT.

(i) CONFIRMED: the W/X alignment is a COINCIDENCE OF REPS stipulated
positionally by B₂ — not a lineage.  (The x-pair cancels ARE lineage:
`xrep-stored` ties the dual's conceal to the reveal it was born from.
The §9f pair has no common birth.)  Consequence: a correct ⊕ cannot be
face-blind.  The landed `⊕ : BCtx → BCtx → BCtx` never consults B₁/B₂ —
which is exactly why the external-face equation had to be carried as a
MergeOK premise.  Any repaired merge is at least `⊕ Θ₁ Θ₂ B₁ B₂`.

(ii) THE LIMIT (gauntlet §9g): if the linkage is coincidence, one revealed
W can coincide with TWO different conceals at once.  The double package —
the §9f construction with two abstractions, client's Λ still opened
outside:

```
(ΛX. ΛZ. λx:X. λg:X⇒Z. g·x) ·[ℕ] ·[ℕ] · 5 · ((ΛW. λy:W. y) ·[ℕ])
```

The client `(λy:W. y) ⟪ ↑W:=ℕ , W⇒W ⟫` crosses the double reveal; the
dual mints `↓X:=ℕ , ↓Z:=ℕ` at boundary type `X⇒Z`.  The nesting types
(`⊢redex-d`).  But the external face needs W ↦ X at the domain and W ↦ Z
at the codomain, and:
- a single rep cannot carry both (`¬ext-dX`, `¬ext-dZ` — the two
  face-directed candidates each fix one position and break the other);
- rewriting B₀ to spell X⇒Z breaks the INTERNAL face against the body's
  type W⇒W (`¬γ-dXZ`, `¬γ-dWZ`) — terms are never rewritten, so the body
  stays typed at W⇒W;
- splitting the reveal in two (↑W₁:=X, ↑W₂:=Z with B₀ = W₁⇒W₂) is barred
  by the same internal-face pinning.

So on this shape FLATTENING IS IMPOSSIBLE — not underdetermined,
impossible, under ANY ⊕.  If this nesting is reachable (the construction
is the §9f trace with one more TyBeta; full mechanization of the trace is
queued), then `NestedApp` cannot be discharged by Merge at all, and the
abstract-witness ⊕ repair — even face-directed — is NOT sufficient for
progress/safety.

THE FORK THIS LEAVES (for Jeremy):
(a) FACE-DIRECTED ⊕ (`⊕ Θ₁ Θ₂ B₁ B₂`, keep the abstract witness where B₂
    stipulates one).  Fixes §9f's single-coincidence; machine-refuted on
    §9g's double coincidence — Merge stays partial, so progress
    additionally needs un-mergeable nestings to be handled some other way
    (values? a peel rule?).
(b) PEEL instead of flatten — generalize Wrap (and TyWrap) from ƛ-bodied
    (Λ-bodied) wrappers to VALUE-bodied wrappers:
      (V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W -→
        (V · (W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫
    (today's Wrap = peel + Beta when V is a ƛ; a TyWrap analog would have
    the inner type application instantiate at the new reveal's own
    abstract variable).  The application unwinds ONE boundary per step —
    all readings are INWARD (γ-direction, functional); the outward
    (relational, Δ̄) re-abstraction is never needed.  On §9f's stuck term:
    peel crosses the argument through ↓X:=ℕ (its dual re-reveals X:=ℕ),
    the inner Wrap then fires — runs, no merge.  On §9g's double
    coincidence: same, runs.  Merge + Drop∅ remain as MergeOK-guarded
    GARBAGE COLLECTION (they are sound as landed — preservation is
    proven), no longer load-bearing for progress; depth-1 values would be
    dropped (towers stay values).  Needs its own probe: preservation of
    peel = the Wrap case minus the β-substitution, plus the ∀-face analog.

Status: NO RULING YET.  §9g evidence is in; the fork is Jeremy's call.

### Decision 5 — RULING (Jeremy, 2026-09-04 night): PEEL (fork (b))

"Let's go with the Peel design."  Install in flight.  The finding that
led here, in full, since it reshapes the calculus:

THE CHAIN.  (1) The Merge landing left `MergeOK`'s external-face equation
as a rule premise, and §9f showed a reachable well-typed term stuck on it
(`cxP₄`) — the flatten-first design had a type-safety hole.  (2) Jeremy,
reading the §9f trace: W and X are NOT tied to each other — they merely
happen to share a rep type; the linkage that lets a revealed W line up
with a concealed X lives in the FACE TYPES, stipulated positionally by
B₂, not in the entries.  So any correct flattening ⊕ must consult the
faces.  (3) The limit (§9g, machine-checked): because the linkage is
coincidence rather than lineage, one revealed W can coincide with TWO
equal-rep conceals at once (`⊢redex-d`, face X⇒Z over ↑W:=ℕ against
↓X:=ℕ,↓Z:=ℕ), and then NO flat boundary exists under ANY ⊕ — the
external face needs W↦X and W↦Z simultaneously (`¬ext-dX`, `¬ext-dZ`),
rewriting B₀ breaks the internal face against the body's type
(`¬γ-dXZ`, `¬γ-dWZ`), and splitting the reveal is barred the same way.
Flattening is not underdetermined but IMPOSSIBLE.  (4) The root cause,
stated once: flattening must move an inner boundary OUTWARD across a
conceal, and the outward re-expression is the inverse of the conceal's
interior reading — relational (Zdancewic's Δ̄), with no syntactic home.

THE DESIGN.  Peel moves the ARGUMENT INWARD instead — the inward
re-expression is dualᴳ, a function, already live:

    Peel : Value V → Value W
         → Δ ⊢ (V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W
           -→ (V · (W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫

(generalizing Wrap from ƛ-bodied to any value body; old Wrap = Peel
followed by Beta; a TyPeel analog replaces/extends TyWrap at ∀ faces —
form to be fixed by probe at install, flagged for review).  The pairs
Peel creates are LINEAGE pairs — `dualᴳ Δcx Θcx2 ≡ Θcx1` by refl (§9h
`dual-cx`): the minted reveal comes from the very conceal it faces — and
those are exactly the cancels `cancel-agree`/`xrep-stored` justify.  On
§9f's stuck term: Peel, then the LANDED Merge cancels the argument's
↓X/↑X pair with a fully discharged MergeOK (`peel-cancel`), Drop∅, the
ordinary ƛ-crossing — a value.  §9g's double coincidence runs the same
way.  Each boundary is consumed by its own crossing, in its own
coordinates; the coincidence linkage is never needed.

CONSEQUENCES:
- Merge + Drop∅ STAY AS LANDED (preservation proven), demoted from
  load-bearing to lineage-pair GARBAGE COLLECTION behind MergeOK.
- Decision 3's depth-1 value grammar (option (iii)) is SUPERSEDED:
  towers remain values; no Value change needed.
- Progress: at a ⇒/∀ face Peel/TyPeel fires on ANY value body —
  NestedApp/NestedTApp become theorems; with the rv-* discharges kept,
  `progress` should become a top-level unconditional theorem at this
  install.
- §9f's stuck-cx/stuck-cxP₄ change meaning: cxP₄ now steps; the gauntlet
  keeps ¬ext-cx/§9g as the permanent record of why flattening was
  abandoned, and replaces the stuckness lemmas with the live Peel run.

### Decision 5 — refinement rulings (Jeremy, 2026-09-04 night)

(1) EITHER TOWERS OR MERGE/DROP∅, NOT BOTH.  Since Peel forces towers
(§9g killed collapse-by-flattening, so depth-1 + Merge was never
available), Merge/Drop∅ must be DELETED unless some progress case has no
Merge-free route — the known hinge is the RevealVarApp/RevealVarTApp
discharges (a variable-faced wrapper whose external rep is an arrow does
not match Peel's syntactic ⇒ face).  The install agent is determining
the dependency on the machine; if a case genuinely needs Merge, it stops
and reports rather than keeping Merge silently.  On deletion, the
flatten-first record (⊕, MergeOK, the §9 refutations) freezes into
notes/old per repo convention.

(2) DESIGN LAW — DETERMINISM: "I do indeed want determinism for this
language."  This independently evicts Merge/Drop∅: they are the only
rules whose LHS is a VALUE, so with them a tower in argument position
steps by ξ-·-r + Merge or is consumed by Peel — two different reducts.
Deliverables at the install: values-don't-step
(`Value V → ¬ (Δ ⊢ V -→ M′)`) and the determinism statement

    det : Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂

(proof included if it doesn't balloon the install, else queued NEXT —
never postulated).  Rule-pair disjointness to preserve: Peel vs Beta
(wrapper vs ƛ function), TyPeel vs TyBeta (wrapper vs bare Λ), ξ frames
directed left-to-right with Value premises.

## Decision 6 — PROGRESS NEEDS MERGE; THE DETERMINISM LAW FORBIDS IT
## (2026-09-04 night, at the Peel install — NEEDS A RULING)

The Peel install landed green (Peel replaces Wrap; TyPeel added for
wrapper-bodied ∀ faces, form (β) — TyWrap kept for Λ bodies;
NestedApp/NestedTApp DISCHARGED and deleted).  But the install surfaced a
genuine conflict between two rulings, both sides machine-checked:

(1) PROGRESS NEEDS MERGE (gauntlet §9i).  At a reveal-variable face the
interior type is `γᵇ Θ X = ` X` — abstract — so Peel/TyPeel, which push
the elimination INWARD, cannot type there; re-spelling B₀ as the rep
breaks the internal face by §9g's own ¬γ argument.  The nesting must
collapse: Merge is the ONLY rule that fires.  Reachable BY PEEL STEPS
ALONE from a closed plain source (`⊢rvQ₀`, `rv-step₁…₅` live):

    Q = ((ΛX. λf:(ℕ⇒X). f · 3) ·[ (ℕ⇒X)⇒X , ℕ⇒ℕ ] · (λn.λm.7)) · 5
      →TyBeta →Peel →Beta →Peel →Beta
      (((λm.7) ⟪ ↓X:=ℕ⇒ℕ , X ⟫) ⟪ ↑X:=ℕ⇒ℕ , X ⟫) · 5      : ℕ

`rv-only-merge` (coverage-complete): every step from this term is a
Merge; `rv-merge`: the Merge fires with MergeOK FULLY discharged (a
lineage pair, composite ∅); `rv-finish` runs on to 7.  So Merge was NOT
deleted.  RevealVarApp/RevealVarTApp are again Progress.Impl parameters,
now TIGHTENED to exactly this nested variable-face shape (strictly
weaker than before).

(2) DETERMINISM FAILS WITH MERGE (gauntlet §9j).  Merge/Drop∅ are the
only rules whose LHS is a VALUE.  Machine-checked counterexample
`nd-peel`/`nd-merge`/`nd-≢`: at

    (Vcx ⟪ ↑X:=ℕ , X⇒ℕ ⟫) · ((($5) ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫)

both Peel (consuming the tower argument as a value) and ξ-·-r + Merge
(stepping it) fire, with provably distinct contracta.  So as landed:
values-don't-step is FALSE and `det` is FALSE (both left as a NEXT
comment, not postulated).  No other rule pair overlaps — deleting
Merge/Drop∅ would give determinism immediately, and by (1) lose progress.

### The option space (no ruling taken)

(A) FOLD THE MERGE INTO THE ELIMINATION — front-runner.  Delete
    standalone Merge/Drop∅ (restoring values-don't-step + det) and add
    variable-face ELIMINATION rules whose LHS is the APPLICATION, e.g.

      MergeApp : … ((V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫) · W -→
                   (V ⟪ Θ₁ ⊕ Θ₂ , mrgB Θ₁ Θ₂ (` Y) ⟫) · W   (+ ∀ analog)

    An application never IS a value, so determinism survives; the
    collapse happens exactly where progress needs it.  OPEN QUESTION
    (the crux): the rv parameters demand a step for EVERY well-typed
    variable-face nesting — is the needed MergeOK derivable there in
    general (§9i's instance is a fully-discharged lineage pair), or does
    typing/bwf need a grounded strengthening so that only
    MergeOK-satisfying nestings type?  If some well-typed instance lacks
    MergeOK, this option needs the invariant minted at birth (the
    grounded-invariants law) — or the shape shown unreachable-and-
    untypeable.
(B) KEEP MERGE, SHRINK VALUE: a tower whose adjacent pair cancels is not
    a value (conditional, knowledge-relative value-hood — TOPLAS p.1074
    style).  Restores values-don't-step by construction; costs the
    simple value grammar and reintroduces a Decision-3-flavor depth
    restriction, now semantic.
(C) KEEP MERGE, WEAKEN THE LAW to determinism-up-to-GC (Merge/Drop∅
    confluent with everything).  Conflicts with the law as stated.

### Also flagged at this install (law-touching deviation)

TyPeel WEAKENS THE TERM: its contractum is `⇑ᵀ (V ⟪ Θ₁ , B₁ ⟫) ·[ … ]`
— the one rule that moves a term, against the no-term-shift law.  The
agent's case: it is a pure weakening (⊢renameᵀ at suc, a landed
theorem), not the forbidden push-a-type-inward (that is TyWrapCncl,
refuted by Example 8), and it is confined to the wrapper-bodied case
(TyWrap for Λ bodies stays shift-free — that is why form (β) was
chosen over (α), which also recreates the Ξalias residue and breaks the
E★′ trace).  Jeremy to confirm or overrule.

### Decision 6 — Jeremy's direction (2026-09-04 night): CANCEL, not Merge

"That example looks like it needs a Cancel reduction, not Merge."
Confirmed by §9i's own numbers: the firing Merge computes `Θrᵈ ⊕ Θr ≡ []`
— nothing is re-indexed; it is the CANCEL CLAUSE alone.  Precedent: the
old design's Cancel rule; the standing roadmap note "revive Cancel — its
side condition is exactly what Reversal now guarantees."  The option
space accordingly REPLACES (A)/(B):

  Cancel : Value V → (side condition)
         → Δ ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ -→ V

(A′) FOLDED: CancelApp/CancelTApp with the APPLICATION as LHS, restricted
     to variable-faced outer boundaries (where Peel/TyPeel cannot fire) —
     Value grammar untouched, towers at rest stay values, determinism by
     disjointness.
(B′) STANDALONE Cancel + Value restriction: a cancellable tower is NOT a
     value (decidable side condition required) — towers GC eagerly;
     Peel's Value premise and ξ-·-r become disjoint by construction.

Probe in flight (notes/CancelProbe.agda — now notes/old/CancelProbe.agda, pinned to the pre-Decision-6 relation): the side condition (syntactic
inverse vs Reversal≈ agreement vs lineage/dualᴳ form — the ≈ form is
suspected necessary, since a conceal rep spelled `X` under a reveal rep
spelled `ℕ⇒ℕ` may type via Reversal≈ unfolding while failing the
syntactic check); the (A′)/(B′) determinism tables; THE CRUX — whether
Cancel discharges the tightened rv parameters for EVERY well-typed
variable-face nesting (adversaries: the alias-reveal tower ↑Y:=X over a
conceal bottom; extra-entry Θ₁), or whether typing must mint
cancellability at birth (grounded-invariants law) / an extra rule is
needed; and the deletion inventory (Merge/Drop∅/⊕/MergeOK all die if
Cancel suffices — "either towers or merge/drop" resolved as towers +
Cancel).

Jeremy's refinement (same night): "cancel is a special form of merge +
drop — the special case where the inner value has type X, concealed by
the inner boundary and revealed by the outer boundary."  So Cancel's LHS
is FACE-ANCHORED:

    Cancel : Value V → (side condition)
           → Δ ⊢ (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫ -→ V

with ` Y a conceal of Θ₁ (V's interior type = the conceal's rep,
concrete) and ` X the matching reveal of Θ₂ — exactly the tightened
RevealVarApp/RevealVarTApp shape, so Cancel targets precisely the
progress residue.  The probe additionally verifies the identity
cancel ≡ merge-then-drop∅ on the shapes where both fire (§9i: Merge
gives V ⟪ ∅ , mrgB ⟫, Drop∅ gives V), and derives the preservation
equation for the face-anchored form (what the OTHER entries of Θ₁/Θ₂
must satisfy — or be absent — for bare V to be typed in Δ at
ρᵇ Θ₂ (` X)).

### Decision 6 — CANCEL PROBE VERDICT (notes/CancelProbe.agda — now notes/old/, 2026-09-04)

Jeremy's identity CONFIRMED as a machine fact, and the side condition is
DERIVED, not chosen — but Cancel cannot carry progress alone.

(1) THE SOUND CANCEL.  Inverting (env) twice forces the side condition:

    CancelOK Δ Θ₁ Θ₂ B₁ B₂ =
        (intOf (intOf Δ Θ₂) Θ₁ ≡ Δ)                 -- contexts undo
      × (substᵗ (γᵇ Θ₁) B₁ ≡ substᵗ (ρᵇ Θ₂) B₂)     -- faces agree, ON THE NOSE

`cancel-pres` proves preservation for -→ V IN GENERAL from just these
two equations (no bwf, no Reversal, no MergeOK); `cancelOK?` decides it.
SURPRISE: the CONTEXT conjunct is the load-bearing one, not the face
pair — `Θe` (an extra reveal beside the conceal) has all four
face-anchored conjuncts yet its interior term can be ill-typed at Δ
(`¬⊢Ve`); a face-only Cancel is UNSOUND.  The ≈ form is also UNSOUND
(`¬a-inner-pres`: contexts undo, faces agree up to ≈Δ̄, contractum has
no type) — this CLOSES the old note "Cancel's side condition is exactly
what Reversal now guarantees": only ≡ works.

(2) CANCEL = MERGE + DROP∅, exactly: `cancel-≡-merge+drop` +
`merge+drop-general` — Cancel is Merge's `Θ₁ ⊕ Θ₂ ≡ []` case with Drop∅
fused; its only gain is 2 equations instead of MergeOK's 5 components.

(3) THE CRUX — Cancel does NOT discharge the rv parameters; progress
FAILS under both placements.  The well-typed variable-face nestings
`(V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫` classify into THREE families (typing
forces ρᵇ Θ₁ (` Y) ≡ ` X):
    α  alias-reveal: Y < revs Θ₁, rep ` X — NO conceal anywhere
       (¬a-CancelFace holds for every Y,X); typed: ⊢Ma.
    β1 the cancel case: Y = revs Θ₁ + X, X concealed — Cancel fires
       iff contexts undo; typed: ⊢rvQ₅ (§9i).
    β2 transparent layer: X kept and unconcealed — Cancel refuted
       (¬p-CancelOK); typed: ⊢Mtp; REACHABLE IN ONE LIVE TyBeta STEP
       from plain source (⊢p-src/p-birth/p-reaches — a ∀-body returning
       an OUTER type variable mints it: (ΛW. e) ·[ ` X-spelling , ℕ ]).
`progress-failsᴬ/ᴮ`: Ma · 5 and Mtp · 5 are closed, well-typed at ℕ, not
values, and take NO step in either Cancel placement (coverage-complete).
Merge fires on ALL THREE families with MergeOK FULLY DISCHARGED
(a-MergeOK, p-MergeOK, e-MergeOK).

(4) PRACTICAL CONCLUSION.  Piecemeal rules for α and β2 re-derive Merge
(β2 = the [] ⊕ Θ₂ case, α = the reveal-over-reveal case).  The design
that works is option (A) FOLDED MERGE: MergeApp/MergeTApp with the
APPLICATION as LHS, restricted to variable-faced outer boundaries
(disjoint from Peel/TyPeel by the face constructor — Progress's own
cf-⇒-B₀/cf-∀-B₀ split); standalone Merge/Drop∅ (the value-LHS rules)
DELETED → values-don't-step and det restored.  Cancel remains a
noteworthy special case (the 2-equation form), not a rule.  The three
fully-discharged MergeOK instances are positive evidence for (A)'s
remaining crux: the general lemma "MergeOK is derivable at every
well-typed variable-face nesting" (needed to discharge rv-app/rv-tapp;
if it resists, the rv parameters carry exactly it).

Placement detail from the probe (§4 disjointness tables): under (A′/A)
the §9j tower simply does not step at rest (nd-arg-stuckᴬ) and Peel is
the unique step at the application (nd-onlyᴬ); the Value grammar stays
untouched.  AWAITING JEREMY'S RULING on installing (A).

### Decision 6 — Jeremy's face-type restriction, checked (gauntlet §9k)

Proposal: "restrict Merge to function and universal face types" (keep it
standalone; the elimination position is maybe not the point).  Verdict:
the face types ARE the right discriminator, but the restriction alone
does not restore determinism — §9k, machine-checked.  §9j's clash does
vanish (that tower's external face is base ℕ).  But §9i's own tower has
EXTERNAL face ℕ⇒ℕ — a function face, so the restricted Merge still fires
on it — and in ARGUMENT position it clashes: `nd-beta` (Beta consumes
the tower as a value) and `nd-mergeArg` (ξ-·-r merges it) are both live
steps with distinct contracta (`nd-fnface-≢`).  A merge-redex that IS a
value clashes somewhere, whatever the face restriction.  The two exits:
  (i) exclude ⇒/∀-faced merge-redexes from Value — but ⊢redex-cx (§9d)
      is a ⇒-faced nesting with MergeOK FALSE: at rest it would be
      neither a value nor able to step, reviving the §9f hole — unless
      value-hood is conditioned on MergeOK itself (knowledge-relative
      values + a MergeOK decidability burden);
  (ii) put the merge at the elimination (MergeApp/MergeTApp) — the LHS
      is an application, never a value, so Value stays untouched and
      determinism is free.  Note the face types remain the point there
      too: at an elimination the merge fires exactly when the outer face
      is a VARIABLE (the complement of Peel/TyPeel's syntactic ⇒/∀)
      whose external reading is the function/universal type — the merge
      exists to EXPOSE the face Peel needs.

### Decision 6 — RULING (Jeremy, 2026-09-04 night): ACTIVE/INERT, inert/inert

Jeremy pushed the Siek–Chen JFP'21 parameterized-cast-calculi paper
(digest: notes/ParameterizedCastCalculi.md): reveals/conceals are casts;
casts classify as ACTIVE (reduce on values; not values themselves) or
INERT (value-forming; eliminated at use sites), with coherence fields
(ActiveOrInert totality, InertCross→, baseNotInert, applyCast totality)
that name exactly our failure modes — §9j/§9k were an active rule
(Merge) on inert-classified values; pre-Peel §9f was an inert shape
with no elimination.  RULED: **inert for function faces, inert for
universal faces** (Peel/TyWrap/TyPeel are the eliminations — active-⇒
would eta-expand and hide the boundary; active-∀ needs a type shift on
the term, barred by the no-term-shift law).  The classification table
(notes/ParameterizedCastCalculi.md): reveal-var faces and base faces
are ACTIVE (collapse via ⊕ / drop), conceal-var and ambient-var faces
INERT (the sealed values; no elimination exists at abstract type).
V-⟪⟫ gains the Inert premise (the Vcast discipline).  Install in
flight: Value restriction, active rules replacing standalone
Merge/Drop∅, canonical forms (canon-ℕ = numerals, canon-var-conceal),
applyCast-totality lemma (discharges rv-app/rv-tapp → progress
unconditional), values-don't-step + det.

### Decision 6 — INSTALLED (2026-09-04 night); Decision 7 opened

The active/inert install is LANDED, gates green cold.  As landed:

- `Inert`/`Active` classifiers (I-⇒ / I-∀ / I-var (revs Θ ≤ X);
  A-var (X < revs Θ) / A-ℕ / A-𝔹), `ActiveOrInert` total,
  `active-not-inert`; `V-⟪⟫ : Value V → Inert Θ B₀ → Value (V ⟪ Θ , B₀ ⟫)`.
- Active rules: `Merge` (kept name; now carries `Inert Θ₁ B₁`,
  `Active Θ₂ B₂`, and MergeOK — its LHS is no longer a value) and
  `Drop$ : Δ ⊢ ($ n) ⟪ Θ , `ℕ ⟫ -→ $ n`.  The base-face action set is a
  THEOREM, not a choice: `inert-ext` (InertCross→ + baseNotInert in one)
  gives the sharpened `canon-ℕ` (a value of type ℕ IS a numeral) and
  `canon-𝔹` (no 𝔹 values exist), so a numeral is the only possible body
  — CancelProbe's context conjunct is free (`⊢$` types anywhere).
  `Drop∅` DELETED (subsumed: at ∅ every var face is inert, every base
  face is Drop$'s redex).
- `TyPeel` gained `Inert Θ₁ B₁` (required for det — otherwise an active
  body stepping under ξ-·[] clashes with TyPeel).
- **DESIGN LAW SATISFIED — DETERMINISM IS PROVEN**:
  `V-¬-→ : Value V → ¬ (Δ ⊢ V -→ M′)` and
  `det : Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂`, both in BReduction.agda,
  no parameters — the whole proof runs off `active-not-inert` + the
  Value premises on the ξ frames.
- Canonical forms sharpened across the board; `canon-var-conceal`
  landed (a value at variable type is an INERT — conceal/ambient-faced
  — wrapper).
- `rv-app`/`rv-tapp` DISSOLVED (the reveal-var branch of the arrow/∀
  canonical-form analysis is refuted by `active-not-inert`).
- CancelProbe.agda retired to notes/old (pinned to the pre-Decision-6
  relation; its verdict lives here and in gauntlet §9a–§9l).

### Decision 7 — MergeOK's component (1) is the LAST obstruction to
### unconditional progress (gauntlet §9l — NEEDS A RULING)

Progress now carries exactly ONE parameter:

    MergeDerivable = ∀ {Δ V Θ₁ Θ₂ X Y}
      → Value V → revs Θ₁ ≤ Y → X < revs Θ₂
      → Δ ∣ [] ⊢ (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫ ⦂ substᵗ (ρᵇ Θ₂) (` X)
      → MergeOK Δ Θ₁ Θ₂ (` Y) (` X)

and it is FALSE as stated — machine-checked (§9l).  With Δ = W:=𝔹,
Θ₂ = ↑X:=ℕ, Θ₁ = ↓X:=ℕ , ↓W:=𝔹:

    (3 ⟪ ↓X:=ℕ , ↓W:=𝔹 , X ⟫) ⟪ ↑X:=ℕ , X ⟫   :  ℕ     (⊢p)

is well typed, NOT a value (outer face active, ¬val-p), and takes NO
step: MergeOK's component (1) — `cmax Θ₁ ≤ revs Θ₂` — is 2 ≤ 1 (¬mok-p).
The inner boundary conceals an AMBIENT slot (W) the outer does not
reveal.  THE DIAGNOSIS IS SHARP: components (2)–(5) all hold on the nose
(bwf-p, sc-p, int⊕-p, ext-p), the contractum types at the redex's type
(⊢merged-p), and the INTERNAL-FACE EQUATION — the very thing component
(1) exists to buy via ⊕-γ — ALSO holds (int-p = refl).  Component (1)
is ⊕-γ's sufficient side condition, mistaken for a necessary one.

THE INDICATED REPAIR: replace MergeOK's component (1) by the
internal-face equation itself

    substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≡ substᵗ (γᵇ Θ₁) B₁

keeping `⊕-γ` as the theorem that discharges it whenever
`cmax Θ₁ ≤ revs Θ₂` (every existing Merge witness still builds).  §9l's
counterexample then steps, and `MergeDerivable` plausibly becomes a
theorem — PROGRESS UNCONDITIONAL.  This edits `MergeOK`, a Decision-3
object in the reduction relation: Jeremy's ruling required.

### Decision 7 — RULING (Jeremy, 2026-09-05): repair MergeOK

"Go ahead with the MergeOK repair."  Install in flight: MergeOK's
component (1) `cmax Θ₁ ≤ revs Θ₂` becomes the internal-face equation
`substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≡ substᵗ (γᵇ Θ₁) B₁`, with ⊕-γ
demoted to the theorem discharging it under cmax≤revs (existing
witnesses rebuild); §9l's counterexample steps; the target is
MergeDerivable proven → Progress.Impl instantiated → progress TOP-LEVEL
UNCONDITIONAL, with det/V-¬-→ kept.

## THE PRESERVATION ENDGAME (2026-09-05) — plan + three parallel tracks

Jeremy: "speed up the push to finish preservation; plan DualCnc≈ now,
launch subagents for DualRep≈ and DualInt≈."  Done — the full plan is
notes/PreservationEndgame.md.  Key points: all three residues are
PROBE-FIRST (each has a suspected-false corner: DualRep≈ lacks ⊢ᶜ Δ —
the store-typing pattern, a preservation-STATEMENT change to confirm;
DualInt≈'s ≼≈ has no clause for the rebuild's abst at xrvld /
double-refusal slots; DualCnc≈'s starOnly is caught in the Pc-copy vs
Pn-license tension INSIDE dualᴳ).  The DualCnc crux = whether the
copy-needing and license-needing demands can hit the SAME slot (probe
Q2); if not, the repair is per-slot copy suppression in dualᴳ
(decidable, birth-time, grounded); else starOnly′ "claims nothing new"
(renaming-stable form only — D1 lesson; must re-refute ⊢3n-adv) or a
birth-time minting.  Rulings will be asked with the probes' examples on
the table.

## DECISION 7 LANDED; TWO REFUTATIONS OPEN DECISION 8 (2026-09-05)

The MergeOK repair is in (component (1) = the internal-face equation,
⊕-γ demoted to its discharge; every witness rebuilt; preservation's
Merge case simpler; det/V-¬-→ untouched).  `merge-derivable :
MergeRest → MergeDerivable` is PROVEN — Decision 7 closed component (1)
for good (`mid-var` pins Y ≡ revs Θ₁ + X, `⊕-γ-var` discharges (1) with
no side condition).  Progress's parameter shrank to `MergeRest`
(components (2)–(5)).

BUT two refutations landed the same hour, and they share a root cause.

(1) `¬MergeRest` and `¬progress` (gauntlet §9m).  Δq = X:=ℕ,
Θq2 = ↑X:=ℕ, Θq1 = ↓X:=(` 0) — the conceal's rep is spelled `X`, the
ABSTRACT witness, licensed by bwf↓'s Reversal≈ THROUGH THE UNFOLDING
(rev-q = ≈unf refl; the syntactic form is refuted, ¬rev-q-≡).  The pair
cancels, and MergeOK's external-face component — stated with ≡ because
preservation transports by subst — fails: mrgB = ` 0 vs ℕ (¬ext-q).
The same tower with the lineage rep ℕ steps (merge-q′).  Half is
settled: ⊕-ρ-var-kept proves the external face free in the KEPT branch;
the CANCELLED branch is the refuted half.  So the unconditional
progress statement is FALSE as things stand (¬progress, machine).

(2) `¬DualCnc≈` and — the sharp one — `¬DualCnc≈-soundness :
DualRep≈ → DualInt≈ → ¬ DualCnc≈` (notes/probes/DualCncProbe.agda).
Pn refutes DualCnc≈ with the hypothesis discharged; per-slot copy
suppression is IMPOSSIBLE as a theorem (`no-per-slot-suppression`:
every rep-carryingly-copied slot is non-abst in Δ and ≼≈ has no
knowledge-below-abst clause — the copy the license wants gone is the
copy the rebuild law requires, ALWAYS the same slot); the
claims-nothing-NEW weakening re-admits ⊢3n-adv via the same
constructor, and the machine shows WHY nothing can work at that site:
`Ψn≡Γz` — Pn's dual conceal and the ⊢3n-adv adversary are THE SAME
(bwf-↓x) INSTANCE (same Γ, Ψ, Θ, X, A, A′).  The three preservation
parameters are mutually INCONSISTENT: BPreservation.Impl as
parameterized can never be instantiated.  The residue must not be
attacked at DualCnc≈.

THE SHARED ROOT CAUSE: reps spelled through knowledge CHAINS rather
than resolved.  §9m's conceal rep is the abstract spelling `X` whose
license is ≈-through-unfolding while the merge's faces demand ≡; Pn's
reveal rep is the chained spelling `Y` whose dual re-reveals the
knowledge rep-carryingly.  In both, the ≡/≈ gap between what bwf
licenses (≈Δ̄, Decision 1's (a″)) and what the metatheory transports
(subst over ≡) is the obstruction.

DECISION 8 — the option space (probing before the ask is complete;
DualRep≈/DualInt≈ agents still out, their verdicts fold in):
(α) FACES UP TO ≈: state MergeOK's two face components (and possibly
    the middle-type equation) with ≈Δ̄ instead of ≡, and transport
    preservation's Merge case by a retag≈-style lemma.  Obstacle: ⊢retag≈
    moves CONTEXTS; a type-side ≈ in the typing judgment has no
    transport today — this road may lead to a conversion-style typing
    rule or ≈-stated (env) faces, a deep change to Boundary.agda.
(β) BORN-RESOLVED REPS: normalize reps THROUGH THE AMBIENT AT MINT TIME
    (in the RULES — TyBeta/TyWrap/dualᴳ — not in the entry maps, so the
    transports that killed (a′)-at-entry-birth are untouched).  Kills
    §9m (conceal born ↓X:=ℕ — merge-q′ steps) and Pn (reveal born
    ↑Z:=ℕ — raw-readable, ordinary license) and collapses Pc's chain
    (second-chance copy retired).  KNOWN OBSTACLE, stated honestly: the
    ≡-rigidity relocates — e.g. TyBeta's contractum must be typed at
    B [ A ]ᵗ with the SYNTACTIC A, so normalizing a reveal rep changes
    the external face away from the redex's type unless the face
    equations/typing absorb ≈ somewhere.  Needs a probe (distinct from
    the refuted (a′): UnfoldProbe's ¬DualCnc-a′ was about the ENTRY
    map).
(γ) UPSTREAM DISSOLUTION: make the chained/abstract-rep shapes
    unmintable or non-values (classification/typing strengthening), or
    dissolve Pn-shaped boundaries by an eager collapse before any dual
    is taken.  Shape unclear; the probes' reachability analysis
    matters (is §9m's ↓X:=(` 0) conceal MINTABLE by the current rules?
    — dualᴳ mints conceal reps as the STORED reveal reps, and TyBeta
    mints reveals from literal type arguments; a ↓X:=X-spelled conceal
    may only arise from a source-written abstract-witness spelling —
    check).
NO RULING YET.  The ask will be assembled with the DualRep≈/DualInt≈
verdicts and reachability probes, on concrete examples.

## THE PRESERVATION VERDICT (2026-09-05) — SUBJECT REDUCTION IS FALSE;
## the endgame probes converge on the REP DISCIPLINE (Decision 8, full ask)

All four endgame tracks are in.  The headline, machine-checked
(notes/probes/DualIntProbe.agda §3.3 + §5):

    ⊢Redex     : Δd ∣ [] ⊢ (Vtm ⟪ Θ2 , (` 0 ⇒ ` 0) ⇒ `ℕ ⟫) · Wtm ⦂ `ℕ
    peel-step  : a live Peel step on it
    ¬⊢contractum : the contractum has NO typing at ℕ

with Δd = rvld (` 0) ∷ abst ∷ rvld `ℕ (a chained-knowledge ambient),
Θ2 = ↑?:=(` 0) , ↓·:=ℕ (a reveal whose REP names the chained slot), and
Wtm a value sealed by ORDINARY knowledge of that same slot
(↓0:=(` 0), bwf↓ at Δd ∋ 0 := ` 0).  The Peel's dual DEMOTES slot 0
(both copy guards refuse → rvl⋆ → the rebuild has abst), and Wtm's own
conceal license — which consults slot 0 — dies inside the dual
(¬⊢W-rebuild).  So the loss is not in the proofs: the CALCULUS loses
subject reduction at this Peel.  Combined with §9m's ¬progress, both
halves of type safety are false as things stand; the DualDef
parameterization was covering a false theorem (and ¬DualCnc≈-soundness
had already shown the three parameters mutually inconsistent).

WHAT IS CLOSED, in the same sweep:
- DualRep≈: FALSE as stated, REPAIRED AND FULLY PROVEN
  (strong/DualRepProof.agda): BlkRepWf (the index relation
  cmax Θ ≤ suc (i + k) the emitter guarantees) + the EXISTING ⊢_ context
  judgment; threading lemmas ⊢-[], ⊢-abst, ⊢-intOf, ⊢-intOf-dual all
  proven — preservation's statement gains a ⊢ Δ premise (store-typing
  pattern; every ξ case covered).  bwf-dual-wf drops the parameter: the
  residue set shrinks by one.
- DualInt≈: FALSE (two corners, xrvld and double-refusal — both the
  rvl⋆→abst demotion); the ≼≈-weakening repair REFUTED at the live Peel
  above; strongest-true version delivered (strong/DualIntProof.agda):
  dual-int≈ reduces it to DualIntHead, a per-slot residue on the cmax Θ
  dropped slots, and head-⋆-abst shows the residue at an rvl⋆ slot IS
  "Δ was abstract there" — dual-int-nodrop / dual-int-abst are the
  closed sub-cases.
- DualCnc≈: FALSE; unfixable at its own site (no-per-slot-suppression;
  CNN re-admits ⊢3n-adv; Pn's dual IS the adversary's (bwf-↓x) instance).
- Decision 7's component (1): closed for good (merge-derivable).
- det / values-don't-step: STAND (they are about the rules, not the
  typing).

THE CONVERGENT DIAGNOSIS.  Every counterexample of the sweep — Pn
(DualCnc), §9m (progress), the two DualInt corners, and the live
preservation break — threads through the same gap: THE SCOPE DISCIPLINE
POLICES B₀ BUT NOT THE REPS.  `Scoped (baseS Θ Δ) B₀` forbids the
boundary type from naming a blocked slot, but bwf↑ licenses a reveal
rep to be ANY Δ-type — chained spellings (` Y with Y:=ℕ), abstract
witnesses (` X licensed only ≈-through-unfolding), and demotable slots
included — and bwf↓/bwf↓x's licenses are NOT stable under the demotion
the dual performs (≼≈ has no knowledge-below-abst clause, correctly:
¬⊢W-rebuild is exactly a license dying under demotion).  The ≡/≈ gap
(§9m) is the same phenomenon one level up.

DECISION 8 — the ask (rulings on direction, then probes before install):
(A) A REP DISCIPLINE in bwf: reps must be Scoped like B₀ (no blocked
    slots) AND resolved (no spelling through rvld-chained slots — the
    resolved spelling exists and is what the license compares against
    anyway).  Kills Pn and §9m at birth (their boundaries become
    unmintable as written; TyBeta/source can still write ·[Y] — the
    RULE would mint the resolved rep, which is where the known
    obstacle lives: TyBeta's contractum must still be typed at
    B [ A ]ᵗ with the syntactic A — needs a probe).  ASSESSMENT, not
    machine-checked: this alone does NOT close the live preservation
    break — §3.3's resolved rep lands on an abst (Λ-bound) slot and
    the demotion problem remains.
(B) DEMOTION-COMPATIBLE CROSSINGS: Peel (the only rule reading Δ)
    gains a grounded premise in the MergeOK style — the crossing value
    W must be typeable against the dual's rebuild ("PeelOK"), with
    progress then obligated to derive it at well-typed redexes or the
    redex classified a value/stuck-by-design.  §3.3's redex would fail
    PeelOK; the question becomes whether every SOURCE-reachable
    crossing satisfies it (reachability probe) — if yes, this is the
    grounded-invariants answer; if no, the calculus needs (C).
(C) RETHINK THE DEMOTION: the dual's rvl⋆ fallback is the only
    knowledge-destroying step in the system; alternatives (keep an
    x-marked copy instead of rvl⋆ so licenses survive demotion as
    x-licenses; or forbid boundaries whose reps/licences depend on
    demotable slots — a transitive rep discipline) need design work
    with the five counterexamples (Pn, §9m, DualInt ×2, §3.3-peel,
    plus ⊢3n-adv as the soundness gate) as the fixed test suite.
Recommendation: (A)+(B) probed together first — (A) shrinks the shapes
to Λ-bound-only demotions, (B) polices exactly those; (C) only if the
reachability probe under (B) finds a source-reachable failing crossing.

## REDESIGN SURVEY ORDERED (Jeremy, 2026-09-05)

"I'm worried that our current boundary bookkeeping is rather broken...
time for a fresh look at all the critical examples and perhaps more, now
that trace generation is easy, and use the data to inform a redesign."
This SUPERSEDES Decision 8's install track: no repair is installed until
the survey data is in.  In flight: EvalLog.agda (an event annotator over
stepΣ's derivations — boundary mints with rep classification, crossings
with per-slot dual outcomes incl. DEMOTION markers, merges/cancels),
notes/probes/SurveyCorpus.agda (the critical examples + new families:
depth-2 chains, double crossings, returned sealed values, x-entries
under a second dual, Λ-bound reps crossed twice), and
notes/BoundarySurvey.md (the master table + machine-backed findings).
The corpus doubles as the regression suite / kill criterion for any
redesign candidate.
