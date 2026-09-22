module strong-rep-store.Reduction where

-- File Charter:
--   * THE RULE SET, AND THE TWO FACTS THAT NEED NO TYPING.  §1 is
--     `_⊢_-→_` with FOURTEEN rules — TyBeta, Beta, Peel, TyPeelR-Λ,
--     TyPeelR-⟪⟫, CancelR, Drop$, Drop-true, Drop-false, IdPush, and
--     the four congruences ξ-·-l, ξ-·-r, ξ-·[], ξ-⟪⟫ (NO ξ-Λ: this is
--     the strong-rep-store experiment, see `⊢Λ` in Terms) — plus the
--     multi-step `_⊢_-→*_` (`done`/`_then_`) and the concrete check
--     `TyBeta-ℕ`.  §2 is `value-¬step`.  §3 is `det`, which takes the
--     redex's TYPING DERIVATION (notes/DECISIONS.md, 2026-09-18:
--     uniqueness comes from typing, not reduction) and reads the
--     name-map `Unique`ness off it through `bw-exterior`,
--     `bw-interior-wf` and `bw-conversion-wf`; NO rule carries a
--     `Unique` premise any more.
--   * NOT HERE.  The typing judgement is strong-rep-store.Terms; the decision
--     procedures that DISCHARGE these rules' side conditions are
--     strong-rep-store.TypeCheck, and the redex search that assembles them is
--     strong-rep-store.Eval.  Preservation, progress and canonical forms live
--     under strong-rep-store.proof with their public statements in
--     strong-rep-store.Preservation, strong-rep-store.Progress and
-- strong-rep-store.TypeSafety.  The
--     design record — what a rule said before a repair, and the
--     machine-checked refutation of it — belongs in
--     notes/DECISIONS.md and the wall modules, never in a rule comment
--     that claims to describe the live rule.
--   * THE CROSSING-SPELLING LAW.  When a rule MOVES a subterm between
--     two name maps, the moved spelling is CARRIED by the rule as a
--     named premise and PINNED by a `Same…` relation — `SameConv`
--     (strong-rep-store.Conversion) for a conversion, `_⊢_≈_⊣_`
-- (strong-rep-store.Ctx §5)
--     for a type or a bare name — and is NEVER computed by a fixed
--     renaming.  The crossing is by the REPRESENTATION a name denotes,
--     never by arithmetic on its position, because the two contexts can
--     reorder relative to each other.  Five such spellings are carried
--     today, and each was installed only after a defect:
--
--       Peel        `s′`, `SameConv Δᵈ s′ Δᶜ s`        2026-09-18
--                     notes/CrossingAudit, notes/PeelPremise
--       TyPeelR-⟪⟫  `Bᵢ′`, `≈` at the interior          2026-09-18
--                     notes/ForallPayloadWall
--       IdPush      `X′`, `≈` at the merged frame       2026-09-18
--                     notes/ForallPayloadWall
--       CancelR     `A′`, `≈` at Θ₁'s OWN conv. ctx     2026-09-19
--                     notes/CancelRShiftWall,
--                     notes/CancelRReachabilityWitness
--       TyPeelR-⟪⟫  `s″`, `SameConv` at `underΛ Δ″ᶜ`    2026-09-20
--                     notes/AddLock0Wall
--
--     A sixth defect of the same reading discipline hit the CONVERSION
--     CONTEXT itself rather than a spelling: the re-unlock clause
--     `conv-unlock-live` (2026-09-17, notes/ReUnlockWall,
--     strong-rep-store.Boundary §3).  Determinism for the carried premises is
--     `sameConv-src-unique`, `sameTy-src-unique`, `conv-src-unique` and
--     `same-rep-unique`; for the lookup-carrying rules it is
--     `∋:=-det`.
--
-- The rule set of the conversion-boundary design, with the repairs ruled in
-- notes/DECISIONS.md ("Id-layer RULING", 2026-09-05) applied:
--
--   (1) V-Λ carries `Value N` (in strong-rep-store.Terms).  In
--       strong-rep-var this was because reduction went under Λ; here
--       `⊢Λ` itself demands `Value N` and ξ-Λ is gone.
--   (2) TyPeelR shifts its type annotation.  It is also SPLIT IN TWO —
--       `TyPeelR-Λ` and `TyPeelR-⟪⟫` — by the shift audit
--       (notes/ShiftAudit.md, 2026-09-08), so that no moved subterm is
--       offered a slot it could not name before.
--   (3) CancelR drops the `hideBinds` residue, carries the BINDER-LOOKUP
--       premise that determines its `mkId` conversion, and names its two
--       conversions separately (the single-name presumption, examined
--       below).
--   (4) IdPush replaces IdAbsorb: the two conversions are SWAPPED
--       instead of the two frames being merged, so no boundary scope
--       arithmetic (`⊳`) is needed and the no-⊕ test is passed by
--       construction.
--   (5) TyBeta carries `Value N` — see the note on the rule.  (In
--       strong-rep-var it closed the TyBeta / ξ-·[] ⨟ ξ-Λ overlap; here
--       it is implied by `⊢Λ`.)
--
-- The principle behind (3)/(4): EVERY rule that mints an identity
-- conversion at a looked-up rep carries the binder-lookup premise, and
-- determinism for those rules is exactly `∋:=-det`.
--
-- TWO-UNIVERSE PORT. A type application carries an ordinary type `A`, but a
-- ∀-elimination mints a representation payload `R`. `TyBeta` and both
-- TyPeelR rules therefore carry `Δ ⊢ᶜ A ~ R`, return the store change
-- `new R` — the cell is pushed onto the AMBIENT representation context at
-- index 0 (`allocate`, experiment 2, notes/RepStoreSketch.md) — and build
-- `instantiate Θ`, which unlocks ordinary name 0 for that cell and shifts
-- the old changes in both universes. Congruence rules carry the relational
-- interior/conversion-context witnesses rather than computing those
-- contexts, and shift the redex's SIBLINGS by the store change.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ;
         _[_]ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst

------------------------------------------------------------------------
-- 1.  The rules
------------------------------------------------------------------------

-- A step returns the CHANGE it made to the store (experiment 2): `none`,
-- or `new R` when a ∀-elimination allocated the cell for R.  The
-- contractum lives at `apply δ Δ`; the congruences shift the redex's
-- siblings by `↑ᴹ[ δ ]`/`↑ᴮ[ δ ]` (strong-rep-store.TermSubst §2).
infix 2 _⊢_-→_∣_
data _⊢_-→_∣_ : Ctxᵗ → Term → Term → Alloc → Set where

  -- A boundary is BORN: the ∀-elimination mints THE BINDER of the event.
  --
  -- THE VALUE PREMISE (repair (5) in strong-rep-var, where reduction went
  -- under Λ and the premise kept TyBeta from overlapping ξ-·[] ⨟ ξ-Λ).
  -- strong-rep-store has no ξ-Λ, and `⊢Λ` demands `Value N`, so on a
  -- well-typed redex the premise is supplied by the typing derivation.
  -- It is kept verbatim so that the untyped relation is unchanged.
  TyBeta : ∀ {Δ B A R N} → Value N
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ (Λ N) ·[ B , A ] -→ N ⟪ instantiate (boundary [])
                                      , reveal 0 B ⟫ ∣ new R

  -- BETA, FRAME-EXACT (2026-09-08).  The substitution CARRIES THE
  -- ARGUMENT'S TYPE — the ƛ's own annotation A — because every image that
  -- crosses a `Λ` in the body is wrapped in that binder's DUAL with an
  -- IDENTITY conversion at the argument's type (`crossΛᴹ`,
  -- strong-rep-store.TermSubst §5).
  -- Shifting alone (the old `N [ W ]ᵐ`) was sound but not frame-exact: the
  -- argument's frame silently gained the Λ's slot.  Determinism is
  -- unaffected — A is read off the redex, so the contractum is still a
  -- function of the redex alone.
  Beta : ∀ {Δ A N W} → Value W
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ ∣ none

  -- PEEL — the crossing.  The application is pushed in one layer and the
  -- argument acquires the DUAL.  `s`/`t` are ↦'s components: the crossing
  -- argument's conversion is RE-BASED by the repointing.
  --
  -- IT CARRIES THE DUAL'S SPELLING (2026-09-18, the crossing audit).  `s`
  -- is read at Θ's conversion context and is used at the DUAL's, which is
  -- taken at the interior — a different name map, and not merely a
  -- renumbering of the same one: the invariant that would have made the
  -- two agree, `conv(dual Θ, int(Θ,Δ)) ≡ conv(Θ,Δ)`, is FALSE here, and
  -- `_⋉_` is what breaks it (notes/CrossingAudit §§4–6).  So the rule
  -- NAMES the dual's spelling `s′` and carries a `SameConv` relating it to
  -- `s`, exactly as `TyPeelR-⟪⟫`, `IdPush` and `CancelR` carry
  -- `_⊢_≈_⊣_`.
  --
  -- The premise never blocks a reduction.  The two contexts name the same
  -- representation variables — that is (Q), notes/PeelPremise §5 — and a
  -- well-typed conversion always has a reading to transport, so a witness
  -- always exists (`peel-premises-env`, strong-rep-store.Conversion §2c).  `t`
  -- needs no premise: it
  -- stays on the same boundary, at Δᶜ, where it was read.
  Peel : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Value V → Value W
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ dualBoundary Θ ⇒ Δᵈ
    → SameConv Δᵈ s′ Δᶜ s
    → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
        -→ (V · (W ⟪ dualBoundary Θ , s′ ⟫)) ⟪ Θ , t ⟫ ∣ none

  -- TYPEEL — the ∀-conversion analogue; the new binder is prepended and the
  -- elimination instantiates at the new binder's bind name.  IT IS TWO
  -- CLAUSES, split on the crossed boundary's INTERIOR (2026-09-08, the
  -- shift audit; notes/ShiftAudit.md).
  --
  -- WHAT EACH CLAUSE DOES.  `canon-∀` (proof/Canonical) says a closed
  -- value at a `∀` type is a `Λ` over a value or a WRAPPER with a `∀`
  -- conversion, and nothing else.  So:
  --
  --   TyPeelR-Λ    the interior is `Λ N`: INSTANTIATE AT ONCE.  N moves
  --                nowhere, gains no shift, and the boundary is born on
  --                the spot.
  --   TyPeelR-⟪⟫   the interior is a boundary: PUSH THE TYPE APPLICATION
  --                INWARD one layer, exactly as the single rule did, and
  --                mask the new binder in the MOVED BOUNDARY'S OWN change
  --                list (`addLock0`, strong-rep-store.Boundary §3).
  --
  -- Together they are TOTAL over canonical `∀`-values, so the split
  -- REPLACES the single rule (`progress`, proof/Progress) rather than
  -- supplementing it.
  --
  -- WHY V'S FRAME MUST NOT GAIN THE UNMASKED BIND SLOT.  The single rule
  -- moved its value V by `wkᴹ 1` into
  -- `unmasked (bind (shiftBy (numBinds Θ) A)) ∷ interior Θ Δ` — V's old
  -- frame with ONE NEW SLOT, offered UNMASKED.  V neither had that slot
  -- nor could use it (`wkᴹ 1` sends every index to ≥ 1), so the frame
  -- said more than the truth: the tight frame and the live one differed
  -- by exactly one `le-mu`, the RE-EXPOSURE clause — the one step `_⊑ᵃ_`,
  -- the refinement a TERM may travel along, REFUSES (`TyPeelR-leak-⊑` /
  -- `TyPeelR-leak-¬⊑ᵃ`, notes/ShiftAudit.md "The TyPeelR leak"; the
  -- surviving Agda half is proof/ShiftAudit §3).  Every other rule masks what
  -- it introduces (Peel by (†), Beta by `crossΛ`), so this was the one
  -- exception, and the audit closed it.
  --
  -- WHY THE Λ CLAUSE NEEDS NO SHIFT.  The `Λ`'s abst slot BECOMES the
  -- boundary's bind slot: N already lives one `abst` binder in (`⊢Λ`), so
  -- the frame move is `unmasked abst → unmasked (bind …)` at a slot N
  -- COULD ALREADY NAME — `la-uu le-ab`, `⊑ᵃ`-legal, which is TyBeta's own
  -- refinement, one `∀` inside.  Hence no `wkᴹ`, no `⊢rename`, and the
  -- contractum does not mention `Bᵢ` at all.
  --
  -- WHY THE WRAPPER CLAUSE TERMINATES.  Its contractum's inner
  -- application is again a redex, but the `∀`-value's TOWER HEIGHT — the
  -- number of nested boundaries above the `Λ` — strictly DECREASES
  -- (`TyPeelR-⟪⟫-height`, proof/ShiftAudit §4), because the clause
  -- CONSUMES a boundary that was already there.  The rejected repair
  -- (wrap the moved value in the new binder's dual) MINTS one instead, so
  -- its measure stalls and it loops: an identity conversion at a `∀` is
  -- necessarily a `` `∀ `` conversion, hence inert, hence the wrapped
  -- value under `·[ … ]` is itself a redex (`fixA-height-stalls`,
  -- proof/ShiftAudit §4; the looping run is written out in
  -- notes/ShiftAudit.md, candidate fix (a)). A tower
  -- height
  -- `h` therefore takes `h − 1` `TyPeelR-⟪⟫` steps and then exactly one
  -- `TyPeelR-Λ` step.
  --
  -- THE ANNOTATION PREMISE (2a).  The pushed-in `·[ _ , ` 0 ]` must carry
  -- the INTERIOR ∀-body — what the interior's own `⊢·[]` demands — not
  -- the
  -- exterior body `B`, from which it differs at every non-identity leaf.
  -- The interior body is not syntactic (a `seal`'s source is a binder's
  -- rep, which the rep-free conversion does not carry) but it IS
  -- DETERMINED by the conversion typing, so both clauses carry that
  -- typing as a PREMISE — the same move already ruled for the `mkId`
  -- conversions.  It is read at the ∀-body, i.e. under one `abst`, and
  -- Progress derives it for free by inverting the redex's own `env`
  -- (`conv-all-inv`).  Determinism is `conv-src-unique`
  -- (strong-rep-store.Conversion) for the wrapper clause, exactly as it is
  -- `∋:=-det`
  -- for the lookup-carrying rules; the Λ clause needs neither.
  --
  -- THE SHIFT (2b).  `renᴮ suc Θ` would double-count: `interior` already
  -- lifts Θ's reps past the binder A prepended here
  -- (`interior (boundary (A ∷ binds Θ) (changes Θ)) Δ
  --   ≡ bind (shiftBy (numBinds Θ) A) ∷ interior Θ Δ`), so the CHANGES
  -- are
  -- plain `changes Θ` — a change names an EXTERIOR slot and is unshifted
  -- by the boundary scope's own binds.
  --
  -- THE CONVERSION (2c).  Slot 0 of the conversion's body was ABSTRACT
  -- and is now the BINDER this rule introduces, so every leaf of `s` that
  -- reads it must become the instantiation step: `instReveal 0 s`.
  -- Keeping `s` itself is ill-typed — its TARGET body still mentions
  -- `` ` 0 `` where `env` demands the instantiated
  -- `shiftBy (numBinds Θ + 1) (Bₑ [ A ])`.
  TyPeelR-Λ : ∀ {Δ Δᶜ N Θ s B A R Bᵢ Bₑ} → Value N
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ N ⟪ instantiate Θ , instReveal 0 s ⟫ ∣ new R

  -- The moved boundary crosses a binder that its appended `lock 0` removes
  -- from the INTERIOR reading.  Its ordinary term indices therefore retain
  -- their positions after deletion; only representation occurrences move past
  -- the new representation binder.  Thus the interior term and frame use
  -- paired, representation-only renamings, and the pushed-in annotation is
  -- re-spelled separately at the outer frame's interior.
  --
  -- THE CONVERSION WALL AND REPAIR (2026-09-20).  The conversion reading
  -- SKIPS locks.  Hence the new ordinary name survives there while every
  -- `unlock X α` in Θ′ inserts around it; where that name ends up depends on
  -- Θ′.  In the closed witness of notes/AddLock0Wall, one `unlock 0 0`
  -- displaces it to position one, so the old fixed
  -- `renᶜ (extᵗ suc) s′` points at the wrong representation and the third
  -- state loses its type.  No fixed renaming can be right for all Θ′.
  --
  -- The rule therefore NAMES the carried spelling `s″`, carries both the old
  -- and moved conversion readings, and pins the spellings with `SameConv`, in
  -- the same pattern as `Peel`.  The old context is viewed through the
  -- representation renaming made by the insertion: without that view, §6b
  -- of strong-rep-store.Examples loses its type at step 8 because
  -- a free representation index is compared to the newly inserted binder.
  -- The contractum is otherwise unchanged: same `addLock0` frame, outer
  -- frame, minted `instReveal 0 s`, pushed-in annotation and type argument
  -- `` ` 0 ``.
  -- THE RE-BASED ANNOTATION (2026-09-18).  `Bᵢ` is read at the CONVERSION
  -- context, because that is where the crossed boundary's conversion is
  -- typed; the pushed-in `·[ _ , ` 0 ]` is read by `⊢·[]` at the INTERIOR.
  -- Those are two different name maps, and they can even reorder relative
  -- to each other (notes/ForallPayloadWall §3), so the rule carries the
  -- interior spelling `Bᵢ′` and a `_⊢_≈_⊣_` relating the two — the
  -- crossing is by the REPRESENTATION a name denotes, never by
  -- arithmetic on its position.  Determinism for it is
  -- `sameTy-src-unique`; `det` reads the interior's `Unique` name map from
  -- the redex typing derivation.
  TyPeelR-⟪⟫ : ∀ {Δ Δᵢ Δᵢ⁺ Δᶜ Δ′ᶜ Δ″ᶜ W Θ′ s′ s″ Θ s B A R
                    Bᵢ Bᵢ′ Bₑ} → Value W
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
    → allocate R Δ ⊢ⁱ instantiate Θ ⇒ Δᵢ⁺
    → Δᵢ⁺ ⊢ᶜ addLock0 (renᴮᴿ suc Θ′) ⇒ Δ″ᶜ
    → SameConv (underΛ Δ″ᶜ) s″ (underΛ (renNameCtx suc Δ″ᶜ Δ′ᶜ)) s′
    → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
    → underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ ((renᴹᴿ suc W ⟪ addLock0 (renᴮᴿ suc Θ′) , `∀ s″ ⟫)
              ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
             ⟪ instantiate Θ , instReveal 0 s ⟫ ∣ new R

  -- CANCEL — a conceal directly under the binder it names.  The
  -- conversion match is DEFINITIONAL: `seal X` and `unseal Y` cite the
  -- SAME entry, so there is no second spelling to disagree with the
  -- first.
  --
  -- THE RESIDUE REPAIR (3a), AS RE-RULED (2026-09-05).  The mini-core
  -- appended `hideBinds (numBinds Θ₂)`, which masks EXTERIOR slots that need
  -- not exist (refuted by the retired `¬⊢ᵐ-cancel-residue`, whose module
  -- proof/MaskFacts.agda went with the masked-entry design); dropping the
  -- residue was not enough either, because `repsOf→bind (binds Θ₂)`
  -- DISCARDS
  -- Θ₁'s whole frame, and a `V` that names one of Θ₁'s own binders loses
  -- it (the old proof/PreserveObstruct §1 witness).  The honest form keeps
  -- BOTH FRAMES and neutralises BOTH CONVERSIONS: composition happens
  -- only on the conversions, where `unseal ∘ seal = id` is the algebra we
  -- already trust, so no boundary-scope arithmetic (`⊕`, `⊳`)
  -- returns.  `V` retypes exactly where it was, and the two `mkId` layers
  -- are transparent at a variable and finished by `Drop$` at a base type.
  --
  -- THE SINGLE-NAME PRESUMPTION, EXAMINED (3b).  The mini-core wrote ONE
  -- name X on both conversions.  That presumes `numBinds Θ₁ ≡ 0`: the
  -- inner conversion is checked on `convCtx Θ₁ (interior Θ₂ Δ)`, which
  -- is
  -- `numBinds Θ₁` binders INSIDE the conversion context `convCtx Θ₂ Δ`
  -- the outer conversion is checked on.  The honest general form carries
  -- TWO names — and needs no extra premise to relate them, because typing
  -- already FORCES `X ≡ numBinds Θ₁ + Y` (proof/IdLayer.agda,
  -- `cancel-name`), exactly as it does for IdPush (`idpush-name`).
  --
  -- THE LOOKUP PREMISE (3c).  `mkId A` is an identity conversion minted
  -- at a looked-up rep, so the rule carries the binder lookup; determinism
  -- for it is `∋:=-det`.
  --
  -- THE SCOPE MOVE (3d, 2026-09-06).  The residue's INNER boundary now
  -- presents the rep `shiftBy (numBinds Θ₁) A` where it presented the
  -- abstract
  -- name, so Θ₂'s LOCKS travel into the inner frame (§2b) — otherwise
  -- `env`'s last premise reads that rep INSIDE Θ₂'s masking.  The lift is
  -- unchanged, because `numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁`.
  --
  -- THE RE-BASED IDENTITY (2026-09-18), REPAIRED (2026-09-19, repair (a),
  -- approved by Jeremy).  `A` is the looked-up type at the OUTER
  -- conversion context `Δᶜ`, which is where the outer layer's `mkId A` is
  -- checked; that half was always right.  The INNER layer is checked at
  -- the merged frame's conversion context `Δ⋉ᶜ`, which lies `numBinds Θ₁`
  -- representation binders inside `Δᶜ` — so re-spelling `A` FROM `Δᶜ`
  -- asserted that `A′` denotes the same representation as `A`, while the
  -- inner `env`'s `SameTyExt (numBinds Θ₁)` demands `shiftBy (numBinds
  -- Θ₁)` of it.  The two agree only when Θ₁ binds nothing or the
  -- representation is closed, and NEITHER holds at a reachable redex.
  --
  -- The premise is therefore read where the shift already lives: at Θ₁'s
  -- OWN conversion context `Δ₁ᶜ`, on the cancelled `seal X`'s own source
  -- `Aᵢ`.  That makes this premise block premise-isomorphic to `IdPush`'s
  -- below — the same interior reading, the same inner conversion reading,
  -- the same lookup, the same re-spelling target.
  --
  -- The wall is `notes/CancelRShiftWall.agda` (the shift incompatibility,
  -- and the OLD statement refuted against a local copy); the reachable
  -- closed witness and the measured before/after run are
  -- `notes/CancelRReachabilityWitness.agda`.  See notes/DECISIONS.md,
  -- 2026-09-19.
  CancelR : ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X Y A A′ Aᵢ}
    → Value V
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → Δ₁ᶜ ∋ X := Aᵢ
    → Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
    → Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
    → Δᶜ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫)
             ⟪ rewind Θ₂ , mkId A ⟫ ∣ none

  -- DROP$ — an identity boundary at a base type, over a numeral (`⊢$`
  -- types it anywhere).
  Drop$ : ∀ {Δ n Θ A} → Base A
    → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ -→ $ n ∣ none

  Drop-true : ∀ {Δ Θ}
    → Δ ⊢ `true ⟪ Θ , id `𝔹 ⟫ -→ `true ∣ none

  Drop-false : ∀ {Δ Θ}
    → Δ ⊢ `false ⟪ Θ , id `𝔹 ⟫ -→ `false ∣ none

  -- IDPUSH (repair (4)) — the transparent-layer rule, as ruled.  An inert
  -- `id (` X)` layer under an ACTIVE conversion is not a value and no
  -- other rule fires; instead of merging the two frames (IdAbsorb's `⊳`,
  -- retired for failing the no-⊕ test) the two CONVERSIONS are swapped:
  -- the transparent layer becomes the revealing one and the outer becomes
  -- transparent.  BOTH FRAMES ARE UNTOUCHED.  `unseal` is the only active
  -- conversion this LHS can meet (proof/IdLayer.agda,
  -- `outer-id-base-untypeable`), and the pushed name is already written in
  -- the identity conversion (`idpush-name`).
  --
  -- THE SCOPE MOVE (2026-09-06).  The swap makes the INNER boundary the
  -- revealing one, so its exterior type becomes Y's rep `A`.  Θ₂'s LOCKS
  -- travel into the inner frame (§2b) so that the rep is presented
  -- OUTSIDE them, where it is nameable: `interior (rewind Θ₂) Δ` IS
  -- `pushBinds (binds Θ₂) Δ`, and
  -- `A ≡ shiftBy (numBinds Θ₂) C` for the redex's own
  -- exterior type C.  That is what retires the wall — the case needs no
  -- scoping invariant at all (proof/MoveScope.preserve-IdPush).
  -- THE RE-BASED NAME (2026-09-18).  `X` is read at the INNER frame's
  -- conversion context; the swap moves it into the MERGED frame's, which
  -- is a different name map.  So the rule carries the merged spelling
  -- `X′` and a `_⊢_≈_⊣_` relating the two, exactly as `TyPeelR-⟪⟫`
  -- does
  -- for its annotation.
  IdPush : ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X X′ Y A} → Value V
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
    → Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
    → Δᶜ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal X′ ⟫)
             ⟪ rewind Θ₂ , mkId A ⟫ ∣ none

  -- THE CONGRUENCES pass the store change up and shift the SIBLINGS by
  -- it: after an allocation the whole program lives under one more
  -- representation binder.  Type annotations are ordinary and do not
  -- move; neither does a boundary's conversion (`renᴹᴿ` leaves it alone).
  ξ-·-l : ∀ {Δ L L′ M δ} → Δ ⊢ L -→ L′ ∣ δ
    → Δ ⊢ L · M -→ L′ · ↑ᴹ[ δ ] M ∣ δ
  ξ-·-r : ∀ {Δ V M M′ δ} → Value V → Δ ⊢ M -→ M′ ∣ δ
    → Δ ⊢ V · M -→ ↑ᴹ[ δ ] V · M′ ∣ δ
  ξ-·[] : ∀ {Δ L L′ B A δ} → Δ ⊢ L -→ L′ ∣ δ
    → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ] ∣ δ
  -- (NO ξ-Λ.)  strong-rep-store does not reduce under a type binder:
  -- `⊢Λ` (strong-rep-store.Terms) requires the body to be a value, so a
  -- well-typed `Λ N` is already a value (V-Λ) and there is nothing for a
  -- congruence to do.  strong-rep-var had `ξ-Λ` here.
  ξ-⟪⟫  : ∀ {Δ Δᵢ M M′ Θ c δ} → Δ ⊢ⁱ Θ ⇒ Δᵢ
        → Δᵢ ⊢ M -→ M′ ∣ δ
        → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ ↑ᴮ[ δ ] Θ , c ⟫ ∣ δ

-- Concrete instantiation check: the ordinary argument `ℕ` translates to
-- representation payload `ℕ`, and `instantiate` produces TyBetaBoundary.
TyBeta-ℕ : empty ⊢ (Λ ($ 7)) ·[ `ℕ , `ℕ ]
  -→ ($ 7) ⟪ TyBetaBoundary , id `ℕ ⟫ ∣ new `ℕ
TyBeta-ℕ = TyBeta V-$ same-ℕ

-- A run needs no store index: each step's change is applied to the
-- context the tail runs at.
infix 2 _⊢_-→*_
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : ∀ {Δ M} → Δ ⊢ M -→* M
  _then_ : ∀ {Δ L M N δ} → Δ ⊢ L -→ M ∣ δ → apply δ Δ ⊢ M -→* N
    → Δ ⊢ L -→* N

infixr 2 _then_

------------------------------------------------------------------------
-- 2.  VALUES DON'T STEP
------------------------------------------------------------------------

-- Nothing reduces under Λ (there is no ξ-Λ), so the `V-Λ` case is
-- absurd outright; the boundary case recurses through ξ-⟪⟫.
value-¬step : ∀ {Δ M M′ δ} → Value M → Δ ⊢ M -→ M′ ∣ δ → ⊥
value-¬step (V-⟪⟫ v I-idv) (Drop$ ())
value-¬step (V-⟪⟫ v ic)    (ξ-⟪⟫ rel st) = value-¬step v st
value-¬step (V-Λ v)        ()

------------------------------------------------------------------------
-- 3.  DETERMINISM
------------------------------------------------------------------------

det : ∀ {Δ Γ M M₁ M₂ A δ₁ δ₂}
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ⊢ M -→ M₁ ∣ δ₁
  → Δ ⊢ M -→ M₂ ∣ δ₂
  → M₁ ≡ M₂ × δ₁ ≡ δ₂

-- TyBeta
det _ (TyBeta v same) (TyBeta v′ same′)
  with same-rep-unique same same′
det _ (TyBeta v same) (TyBeta v′ same′) | refl = refl , refl
det _ (TyBeta v same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-Λ v) st)
det _ (ξ-·[] st) (TyBeta v same) =
  ⊥-elim (value-¬step (V-Λ v) st)

-- Beta
det _ (Beta w)     (Beta w′)    = refl , refl
det _ (Beta w)     (ξ-·-l st)   = ⊥-elim (value-¬step V-ƛ st)
det _ (Beta w)     (ξ-·-r v st) = ⊥-elim (value-¬step w st)
det _ (ξ-·-l st)   (Beta w)     = ⊥-elim (value-¬step V-ƛ st)
det _ (ξ-·-r v st) (Beta w)     = ⊥-elim (value-¬step w st)

-- Peel
-- the dual's spelling is pinned by `sameConv-src-unique`, once the three
-- readings have been identified.
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  with conversion-functional rc rc′ | interior-functional ri ri′
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl with conversion-functional rd rd′
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl | refl
  with sameConv-src-unique
         (dual-unique (name-fn (bw-exterior mwΘ)) ri rd) sc sc′
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl | refl | refl = refl , refl
det _ (Peel v w rc ri rd sc) (ξ-·-l st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det _ (Peel v w rc ri rd sc) (ξ-·-r u′ st) =
  ⊥-elim (value-¬step w st)
det _ (ξ-·-l st) (Peel v w rc ri rd sc) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det _ (ξ-·-r u′ st) (Peel v w rc ri rd sc) =
  ⊥-elim (value-¬step w st)

-- TyPeelR — the two clauses' patterns are DISJOINT (a `Λ` is not a
-- boundary), so no cross case arises.
--
-- The Λ clause is determined by the redex OUTRIGHT: its contractum does
-- not mention `Bᵢ`, so `conv-src-unique` is not needed at all.
det _ (TyPeelR-Λ v rel ⊢s same)
    (TyPeelR-Λ v′ rel′ ⊢s′ same′)
  with same-rep-unique same same′
det _ (TyPeelR-Λ v rel ⊢s same)
    (TyPeelR-Λ v′ rel′ ⊢s′ same′) | refl = refl , refl
det _ (TyPeelR-Λ v rel ⊢s same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-Λ v) I-all) st)
det _ (ξ-·[] st) (TyPeelR-Λ v rel ⊢s same) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-Λ v) I-all) st)

-- The wrapper clause's two contracta agree after all five carried readings
-- have been identified.  The SOURCE type determines the pushed-in annotation;
-- the type argument determines the instantiated frame; and the moved
-- conversion spelling is pinned by `sameConv-src-unique`.  Its `Unique` map is
-- recovered from the redex typing's exterior and the carried instantiated
-- interior/moved-conversion readings, just as `Peel` recovers the dual map.
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
  with interior-functional ri ri′ | conversion-functional rc rc′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl
  with interior-functional ri (bw-interior mwΘ)
     | conversion-functional rc (bw-conversion mwΘ)
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl
  with conversion-functional r′ r′′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl
  with conv-src-unique
         (unique-underΛ {Γ = Δᶜ} (name-fn (bw-conversion-wf mwΘ))) ⊢s ⊢s′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl
  with sameTy-src-unique
         (unique-underΛ {Γ = Δᵢ} (name-fn (bw-interior-wf mwΘ))) sm sm′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl
  with same-rep-unique same same′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl
  with interior-functional ri⁺ ri⁺′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δ″ᶜ = Δ″ᶜ} v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl
  with conversion-functional r″ r″′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δ″ᶜ = Δ″ᶜ} v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl
  with sameConv-src-unique
         (unique-underΛ {Γ = Δ″ᶜ}
           (conversion-unique
             (interior-unique (unique-shift (name-fn (bw-exterior mwΘ)))
                              ri⁺) r″))
         sc sc′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl
    | refl = refl , refl
det _ (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-⟪⟫ v I-all) I-all) st)
det _ (ξ-·[] st) (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm same) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-⟪⟫ v I-all) I-all) st)

-- CancelR — both looked-up types and the re-spelling are functional.  The
-- repaired rule reads its inner lookup at Θ₁'s own conversion context, so
-- determinism inverts the redex typing to BOTH boundaries' `BoundaryWf`s.
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
  with interior-functional ri ri′ | conversion-functional r₂ r₂′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl
  with conversion-functional r₁ r₁′ | conversion-functional r⋉ r⋉′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl
  with interior-functional ri (bw-interior mwΘ₂)
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl
  with conversion-functional r₁ (bw-conversion mwΘ₁)
     | conversion-functional r₂ (bw-conversion mwΘ₂)
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl | refl | refl
  with ∋:=-det (name-fn (bw-conversion-wf mwΘ₁)) d₁ d₁′
     | ∋:=-det (name-fn (bw-conversion-wf mwΘ₂)) d₂ d₂′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl
  with sameTy-src-unique
         (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sm sm′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl =
  refl , refl
det _ (CancelR v ri r₁ d₁ r⋉ sm r₂ d₂) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)
det _ (ξ-⟪⟫ frame st) (CancelR v ri r₁ d₁ r⋉ sm r₂ d₂) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)

-- Drop$
det _ (Drop$ b)    (Drop$ b′)   = refl , refl
det _ (Drop$ b) (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-$ st)
det _ (ξ-⟪⟫ frame st) (Drop$ b) = ⊥-elim (value-¬step V-$ st)

-- Drop-true / Drop-false
det _ Drop-true Drop-true = refl , refl
det _ Drop-true (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-true st)
det _ (ξ-⟪⟫ frame st) Drop-true = ⊥-elim (value-¬step V-true st)
det _ Drop-false Drop-false = refl , refl
det _ Drop-false (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-false st)
det _ (ξ-⟪⟫ frame st) Drop-false = ⊥-elim (value-¬step V-false st)

-- IdPush — likewise determined by the lookup.
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
  with interior-functional ri ri′ | conversion-functional rel rel′
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′) | refl | refl
  with conversion-functional r₁ r₁′ | conversion-functional r⋉ r⋉′
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
    | refl | refl | refl | refl
  with conversion-functional rel (bw-conversion mwΘ₂)
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
    | refl | refl | refl | refl | refl
  with sameTy-src-unique
         (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sm sm′
     | ∋:=-det (name-fn (bw-conversion-wf mwΘ₂)) d d′
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
    | refl | refl | refl | refl | refl | refl | refl = refl , refl
det _ (IdPush v ri r₁ r⋉ sm rel d) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)
det _ (ξ-⟪⟫ frame st) (IdPush v ri r₁ r⋉ sm rel d) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)

-- the congruences: the sibling shift is a function of the store change,
-- so once the two steps agree on the contractum AND the change, the two
-- shifted siblings agree too.
det (⊢· ⊢L ⊢M) (ξ-·-l st) (ξ-·-l st′) with det ⊢L st st′
det (⊢· ⊢L ⊢M) (ξ-·-l st) (ξ-·-l st′) | refl , refl = refl , refl
det _ (ξ-·-l st) (ξ-·-r v st′) = ⊥-elim (value-¬step v st)
det _ (ξ-·-r v st) (ξ-·-l st′) = ⊥-elim (value-¬step v st′)
det (⊢· ⊢L ⊢M) (ξ-·-r v st) (ξ-·-r u st′) with det ⊢M st st′
det (⊢· ⊢L ⊢M) (ξ-·-r v st) (ξ-·-r u st′) | refl , refl = refl , refl
det (⊢·[] ⊢L ⊢A) (ξ-·[] st) (ξ-·[] st′) with det ⊢L st st′
det (⊢·[] ⊢L ⊢A) (ξ-·[] st) (ξ-·[] st′) | refl , refl = refl , refl
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  with interior-functional rel rel′
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl with interior-functional rel (bw-interior mwΘ)
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl with det ⊢M st st′
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl | refl , refl = refl , refl
