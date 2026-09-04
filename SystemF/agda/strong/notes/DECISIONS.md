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
    Flagged for Jeremy's review; revertible.

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
