* COLOR PRESERVATION — the proof, once Jeremy has reviewed the statement
  (PR #207).

  DONE 2026-09-21 (PR #207), alongside the CtxMorph → Boundary rename:

    `Residual.agda`           one-hole contexts `TermCtx`/`plug`; the type
                              context at the hole `Δ ⊢C C ⊣ Δ′`, whose
                              `names` is the hole's SCOPE MAP; renaming and
                              Beta-substitution through a context
                              (`renCtx²`/`holeRen²`, `substCtx`/`holeEnv`);
                              `Residual r C M ρ D N` and `Residuals`,
                              indexed by the representation renaming ρ the
                              move delivers to the hole.
    `ColorPreservation.agda`  the STATEMENT `ColorPreservation : Set` —
                              at a residual position the scope map is the
                              old one under ρ:
                              `names Δ₂ ≡ map ρ (names Δ₁)`.  Unproved.
    `notes/ColorPreservationProbe.agda`
                              the statement on one run (TyBeta, Peel, Beta
                              under a Λ), every object checked, the final
                              equation by `refl`.
    `proof/Residual.agda`     soundness of the layer: `plug C M` is the
                              step's source and `plug D N` its contractum
                              (`residual-source`, `residual-sound`,
                              `residuals-sound`), via `plug-renCtx²` and
                              `plug-substCtx`.

  NEXT, after the review: `proof/ColorPreservation.agda`, by induction on
  `Residuals`, one lemma per `Residual` constructor:

    * frames: `⊢C` through `renCtx² (moveᴿ ρ) C` reads the hole at the
      renamed context — the name-map half is `map (holeᴿ ρ C)`, by
      `renNameCtx`/`RepWk` (proof/Ctx §8, proof/RepWeaken);
    * per site, the frame facts proof/ShiftAudit already records: Peel
      `dual-interior` (names shift by `wkN (numBinds Θ)`), TyBeta /
      TyPeelR-Λ `instantiate` restores name 0
      (`TyBeta-restores-name-0`), TyPeelR-⟪⟫ `addLock0` after
      `renᴮ² (moveᴿ suc)`, CancelR / IdPush `rewind-interior` /
      `merged-interior`, Beta's body `substCtx` keeps the binder
      structure, Beta's argument crosses each `Λ` inside `crossΛᴹ`'s
      dual, whose lock deletes exactly the name the `Λ` added;
    * `Residuals` composes the per-step equations along `ρ′ ∘ ρ`.

  THE V7 ORIGINAL (strong-v3-design, commit 31fa0918, "proof of color
  preservation"; retired 2026-09-15 by the v8 sweep 309ad95a; last fully
  alive at db3d7fb8: `strong/ColorPreservation.agda`,
  `strong/proof/ColorPreservation.agda`, `strong/Residual.agda`) said
  `scopeᵗ Δ₁ ≡ scopeᵗ Δ₂` and factored through a push/pop BALANCE for
  one-hole contexts.  Here the balance is replaced by the observation
  proof/ShiftAudit §3 records: every move but TyBeta's refinement is
  REPRESENTATION-ONLY, so the scope map is transported by a renaming ρ
  rather than counted.

  DECISIONS EMBEDDED IN THE STATEMENT, for Jeremy to veto (also on the
  PR):

    1. color = `names Δ` at the hole (which ordinary names are live, and
       which α each denotes), transported along ρ.  The representation
       STORE (`reps Δ`: insertion, and the `abstR → bindR R` refinement)
       is deliberately NOT in the statement; a second theorem could pin it.
    2. ρ is an INDEX of `Residuals`, pinned per rule by the derivation —
       not an existential.
    3. which nodes have residuals: redex nodes are consumed;
       `Drop$`/`Drop-true`/`Drop-false` consume their literal; a
       substituted variable's position becomes the argument copy's
       (`CopyResidual`, one residual per receiving occurrence), and
       `Stable` excludes it from the body residuals.
    4. the typing premise `Δ ∣ [] ⊢ L ⦂ A` is kept, as in v7; the proof
       may turn out not to need it.
    5. stated over any `Δ`, not just `empty`, since ξ-Λ reduces under Λ.
