module strong.Reduction where

-- Strong System F — REDUCTION.
--
-- The rule set of the conversion-boundary design, with the repairs ruled in
-- notes/DECISIONS.md ("Id-layer RULING", 2026-09-05) applied:
--
--   (1) V-Λ carries `Value N` (in strong.Terms) — reduction goes under Λ.
--   (2) TyPeelR shifts its type annotation.  It is also SPLIT IN TWO —
--       `TyPeelR-Λ` and `TyPeelR-⟪⟫` — by the shift audit
--       (notes/ShiftAudit.md, 2026-09-08), so that no moved subterm is
--       offered a slot it could not name before.
--   (3) CancelR drops the `hideBinds` residue, carries the BINDER-LOOKUP
--       premise that determines its `mkId` conversion, and names its two
--       conversions separately (the single-name presumption, examined
--       below).
--   (4) IdPush replaces IdAbsorb: the two conversions are SWAPPED
--       instead of the two frames being merged, so no context morphism
--       arithmetic (`⊳`) is needed and the no-⊕ test is passed by
--       construction.
--   (5) TyBeta carries `Value N` — see the note on the rule.  Without it
--       TyBeta and ξ-·[] ⨟ ξ-Λ are a genuine overlap (repair (1) alone
--       does
--       not close it), so determinism would still be false.
--
-- The principle behind (3)/(4): EVERY rule that mints an identity
-- conversion at a looked-up rep carries the binder-lookup premise, and
-- determinism for those rules is exactly `∋:=-det`.
--
-- TWO-UNIVERSE PORT. A type application carries an ordinary type `A`, but a
-- morphism binds a representation payload `R`. `TyBeta` and both TyPeelR
-- rules therefore carry `Δ ⊢ᶜ A ~ R` and build `instantiate R Θ`. This
-- operation prepends `bindR R`, explicitly unlocks ordinary name 0 for it,
-- and shifts the old changes in both universes. Congruence rules carry the
-- relational interior/conversion-context witnesses rather than computing
-- those contexts with the retired `interior` and `convCtx` functions.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ;
         _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.TermSubst

------------------------------------------------------------------------
-- 1.  The rules
------------------------------------------------------------------------

infix 2 _⊢_-→_
data _⊢_-→_ : Ctxᵗ → Term → Term → Set where

  -- A boundary is BORN: the ∀-elimination mints THE BINDER of the event.
  --
  -- THE VALUE PREMISE (repair (5)).  This calculus reduces under Λ (ξ-Λ),
  -- so `Λ N` is a value only when N is one (V-Λ).  Without `Value N` here,
  -- `(Λ N) ·[ B , A ]` with N a redex has TWO distinct steps — this one and
  -- ξ-·[] ⨟ ξ-Λ — and determinism fails.  The premise mirrors Beta's.
  TyBeta : ∀ {Δ B A R N} → Value N
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ (Λ N) ·[ B , A ] -→ N ⟪ instantiate R (morph [] [])
                                      , reveal 0 B ⟫

  -- BETA, FRAME-EXACT (2026-09-08).  The substitution CARRIES THE
  -- ARGUMENT'S TYPE — the ƛ's own annotation A — because every image that
  -- crosses a `Λ` in the body is wrapped in that binder's DUAL with an
  -- IDENTITY conversion at the argument's type (strong.TermSubst §5b).
  -- Shifting alone (the old `N [ W ]ᵐ`) was sound but not frame-exact: the
  -- argument's frame silently gained the Λ's slot.  Determinism is
  -- unaffected — A is read off the redex, so the contractum is still a
  -- function of the redex alone.
  Beta : ∀ {Δ A N W} → Value W
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ

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
  -- `s`, exactly as `TyPeelR-⟪⟫`, `IdPush` and `CancelR` carry `SameTy`.
  --
  -- The premise never blocks a reduction.  The two contexts name the same
  -- representation variables — that is (Q), notes/PeelPremise §5 — and a
  -- well-typed conversion always has a reading to transport, so a witness
  -- always exists (`peel-premises-env`, §8).  `t` needs no premise: it
  -- stays on the same boundary, at Δᶜ, where it was read.
  Peel : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Value V → Value W
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ dualMorph Θ ⇒ Δᵈ
    → Unique (names Δᵈ)
    → SameConv Δᵈ s′ Δᶜ s
    → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
        -→ (V · (renᴹ² (ren² idᵗ (wkN (numBinds Θ))) W
                    ⟪ dualMorph Θ , s′ ⟫)) ⟪ Θ , t ⟫

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
  --                list (`addLock0`, strong.CtxMorph §5).
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
  -- the refinement a TERM may travel along, REFUSES (proof/ShiftAudit §3,
  -- `TyPeelR-leak-⊑` / `TyPeelR-leak-¬⊑ᵃ`).  Every other rule masks what
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
  -- (`TyPeelR-⟪⟫-height`, proof/ShiftAudit §5c₂), because the clause
  -- CONSUMES a boundary that was already there.  The rejected repair
  -- (wrap the moved value in the new binder's dual) MINTS one instead, so
  -- its measure stalls and it loops: an identity conversion at a `∀` is
  -- necessarily a `` `∀ `` conversion, hence inert, hence the wrapped
  -- value under `·[ … ]` is itself a redex (`fixA-height-stalls` and the
  -- run `T₀ -→ᵃ T₁ -→ᵃ T₂`, proof/ShiftAudit §4/§4a). A tower
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
  -- (strong.Conversion) for the wrapper clause, exactly as it is `∋:=-det`
  -- for the lookup-carrying rules; the Λ clause needs neither.
  --
  -- THE SHIFT (2b).  `renᴮ suc Θ` would double-count: `interior` already
  -- lifts Θ's reps past the binder A prepended here
  -- (`interior (morph (A ∷ binds Θ) (changes Θ)) Δ
  --   ≡ bind (shiftBy (numBinds Θ) A) ∷ interior Θ Δ`), so the CHANGES
  -- are
  -- plain `changes Θ` — a change names an EXTERIOR slot and is unshifted
  -- by the morphism's own binds.
  --
  -- THE CONVERSION (2c).  Slot 0 of the conversion's body was ABSTRACT
  -- and is now the BINDER this rule introduces, so every leaf of `s` that
  -- reads it must become the instantiation step: `instReveal 0 s`.
  -- Keeping `s` itself is ill-typed — its TARGET body still mentions
  -- `` ` 0 `` where `env` demands the instantiated
  -- `shiftBy (numBinds Θ + 1) (Bₑ [ A ])`.
  TyPeelR-Λ : ∀ {Δ Δᶜ N Θ s B A R Bᵢ Bₑ} → Value N
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Unique (names (underΛ Δᶜ))
    → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ N ⟪ instantiate R Θ , instReveal 0 s ⟫

  -- The moved boundary crosses a binder that its appended `lock 0` removes.
  -- Its ordinary indices therefore retain their positions after deletion;
  -- only representation occurrences move past the new representation binder.
  -- Thus the interior and frame use paired, rep-only renamings, while the
  -- conversion and annotation (which can see the new ordinary binder) retain
  -- their ordinary weakening.
  -- `renᶜ (extᵗ (extN (numBinds Θ′) suc))` on its `∀`-conversion
  -- body —
  -- and then `lock 0` is APPENDED to its own (shifted) change list.  So
  -- the contractum is the single rule's, with `addLock0` on the moved
  -- boundary and nothing else changed: same outer frame, same minted
  -- conversion `instReveal 0 s`, same pushed-in annotation, same type
  -- argument `` ` 0 `` (`TyPeelR-⟪⟫-wkᴹ`,
  -- `TyPeelR-⟪⟫-outer-unchanged`, proof/ShiftAudit §5c).
  -- THE RE-BASED ANNOTATION (2026-09-18).  `Bᵢ` is read at the CONVERSION
  -- context, because that is where the crossed boundary's conversion is
  -- typed; the pushed-in `·[ _ , ` 0 ]` is read by `⊢·[]` at the INTERIOR.
  -- Those are two different name maps, and they can even reorder relative
  -- to each other (notes/ForallPayloadWall §3), so the rule carries the
  -- interior spelling `Bᵢ′` and a `SameTy` relating the two — the
  -- crossing is by the REPRESENTATION a name denotes, never by
  -- arithmetic on its position.  Determinism for it is
  -- `sameTy-src-unique`, which is why the interior's name map is carried
  -- with its own `Unique`.
  TyPeelR-⟪⟫ : ∀ {Δ Δᵢ Δᶜ W Θ′ s′ Θ s B A R Bᵢ Bᵢ′ Bₑ} → Value W
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Unique (names (underΛ Δᵢ))
    → Unique (names (underΛ Δᶜ))
    → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
    → SameTy (underΛ Δᵢ) Bᵢ′ (underΛ Δᶜ) Bᵢ
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ ((renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc)) W
               ⟪ addLock0 (renᴮ² (ren² idᵗ suc) Θ′)
               , `∀ (renᶜ (extᵗ suc) s′) ⟫)
              ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
             ⟪ instantiate R Θ , instReveal 0 s ⟫

  -- CANCEL — a conceal directly under the binder it names.  The
  -- conversion match is DEFINITIONAL: `seal X` and `unseal Y` cite the
  -- SAME entry, so there is no second spelling to disagree with the
  -- first.
  --
  -- THE RESIDUE REPAIR (3a), AS RE-RULED (2026-09-05).  The mini-core
  -- appended `hideBinds (numBinds Θ₂)`, which masks EXTERIOR slots that need
  -- not exist (proof/MaskFacts.agda, `¬⊢ᵐ-cancel-residue`); dropping the
  -- residue was not enough either, because `repsOf→bind (binds Θ₂)`
  -- DISCARDS
  -- Θ₁'s whole frame, and a `V` that names one of Θ₁'s own binders loses
  -- it (the old proof/PreserveObstruct §1 witness).  The honest form keeps
  -- BOTH FRAMES and neutralises BOTH CONVERSIONS: composition happens
  -- only on the conversions, where `unseal ∘ seal = id` is the algebra we
  -- already trust, so no context-morphism arithmetic (`⊕`, `⊳`)
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
  -- THE RE-BASED IDENTITY (2026-09-18).  `A` is the looked-up type at the
  -- OUTER conversion context, which is where the outer layer's `mkId A`
  -- is checked.  The INNER layer is checked at the merged frame's, a
  -- different name map, so it carries its own spelling `A′` and a
  -- `SameTy` relating the two — the same crossing `TyPeelR-⟪⟫` and
  -- `IdPush` carry, repaired here before any example reached a
  -- configuration where the two disagree.
  CancelR : ∀ {Δ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X Y A A′} → Value V
    → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
    → Unique (names Δ⋉ᶜ)
    → SameTy Δ⋉ᶜ A′ Δᶜ A
    → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
    → Unique (names Δᶜ)
    → Δᶜ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫)
             ⟪ rewind Θ₂ , mkId A ⟫

  -- DROP$ — an identity boundary at a base type, over a numeral (`⊢$`
  -- types it anywhere).
  Drop$ : ∀ {Δ n Θ A} → Base A
    → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ -→ $ n

  Drop-true : ∀ {Δ Θ}
    → Δ ⊢ `true ⟪ Θ , id `𝔹 ⟫ -→ `true

  Drop-false : ∀ {Δ Θ}
    → Δ ⊢ `false ⟪ Θ , id `𝔹 ⟫ -→ `false

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
  -- `X′` and a `SameTy` relating the two, exactly as `TyPeelR-⟪⟫` does
  -- for its annotation.
  IdPush : ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X X′ Y A} → Value V
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
    → Unique (names Δ⋉ᶜ)
    → SameTy Δ⋉ᶜ (` X′) Δ₁ᶜ (` X)
    → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
    → Unique (names Δᶜ)
    → Δᶜ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal X′ ⟫)
             ⟪ rewind Θ₂ , mkId A ⟫

  ξ-·-l : ∀ {Δ L L′ M} → Δ ⊢ L -→ L′
    → Δ ⊢ L · M -→ L′ · M
  ξ-·-r : ∀ {Δ V M M′} → Value V → Δ ⊢ M -→ M′
    → Δ ⊢ V · M -→ V · M′
  ξ-·[] : ∀ {Δ L L′ B A} → Δ ⊢ L -→ L′
    → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ]
  ξ-Λ   : ∀ {Δ N N′} → underΛ Δ ⊢ N -→ N′
    → Δ ⊢ Λ N -→ Λ N′
  ξ-⟪⟫  : ∀ {Δ Δᵢ M M′ Θ c} → Δ ⊢ⁱ Θ ⇒ Δᵢ
        → Δᵢ ⊢ M -→ M′
        → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ Θ , c ⟫

-- Concrete instantiation check: the ordinary argument `ℕ` translates to
-- representation payload `ℕ`, and `instantiate` produces TyBetaMorph.
TyBeta-ℕ : empty ⊢ (Λ ($ 7)) ·[ `ℕ , `ℕ ]
  -→ ($ 7) ⟪ TyBetaMorph , id `ℕ ⟫
TyBeta-ℕ = TyBeta V-$ same-ℕ

infix 2 _⊢_-→*_
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : ∀ {Δ M} → Δ ⊢ M -→* M
  _then_ : ∀ {Δ L M N} → Δ ⊢ L -→ M → Δ ⊢ M -→* N
    → Δ ⊢ L -→* N

infixr 2 _then_

------------------------------------------------------------------------
-- 2.  VALUES DON'T STEP
------------------------------------------------------------------------

-- With V-Λ's `Value N` premise this holds on the nose.  (In the mini-core it
-- was false: `Λ N` was a value for every N while ξ-Λ reduced under it.)
value-¬step : ∀ {Δ M M′} → Value M → Δ ⊢ M -→ M′ → ⊥
value-¬step (V-⟪⟫ v I-idv) (Drop$ ())
value-¬step (V-⟪⟫ v ic)    (ξ-⟪⟫ rel st) = value-¬step v st
value-¬step (V-Λ v)        (ξ-Λ st)  = value-¬step v st

------------------------------------------------------------------------
-- 3.  DETERMINISM
------------------------------------------------------------------------

det : ∀ {Δ M M₁ M₂}
  → Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂

-- TyBeta
det (TyBeta v same) (TyBeta v′ same′)
  with same-rep-unique same same′
det (TyBeta v same) (TyBeta v′ same′) | refl = refl
det (TyBeta v same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-Λ v) st)
det (ξ-·[] st) (TyBeta v same) =
  ⊥-elim (value-¬step (V-Λ v) st)

-- Beta
det (Beta w)     (Beta w′)    = refl
det (Beta w)     (ξ-·-l st)   = ⊥-elim (value-¬step V-ƛ st)
det (Beta w)     (ξ-·-r v st) = ⊥-elim (value-¬step w st)
det (ξ-·-l st)   (Beta w)     = ⊥-elim (value-¬step V-ƛ st)
det (ξ-·-r v st) (Beta w)     = ⊥-elim (value-¬step w st)

-- Peel
-- the dual's spelling is pinned by `sameConv-src-unique`, once the three
-- readings have been identified.
det (Peel v w rc ri rd u sc) (Peel v′ w′ rc′ ri′ rd′ u′ sc′)
  with conversion-functional rc rc′ | interior-functional ri ri′
det (Peel v w rc ri rd u sc) (Peel v′ w′ rc′ ri′ rd′ u′ sc′)
  | refl | refl with conversion-functional rd rd′
det (Peel v w rc ri rd u sc) (Peel v′ w′ rc′ ri′ rd′ u′ sc′)
  | refl | refl | refl
  with sameConv-src-unique u sc sc′
det (Peel v w rc ri rd u sc) (Peel v′ w′ rc′ ri′ rd′ u′ sc′)
  | refl | refl | refl | refl = refl
det (Peel v w rc ri rd u sc) (ξ-·-l st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det (Peel v w rc ri rd u sc) (ξ-·-r u′ st) = ⊥-elim (value-¬step w st)
det (ξ-·-l st)   (Peel v w rc ri rd u sc) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det (ξ-·-r u′ st) (Peel v w rc ri rd u sc) = ⊥-elim (value-¬step w st)

-- TyPeelR — the two clauses' patterns are DISJOINT (a `Λ` is not a
-- boundary), so no cross case arises.
--
-- The Λ clause is determined by the redex OUTRIGHT: its contractum does
-- not mention `Bᵢ`, so `conv-src-unique` is not needed at all.
det (TyPeelR-Λ v rel unique ⊢s same)
    (TyPeelR-Λ v′ rel′ unique′ ⊢s′ same′)
  with same-rep-unique same same′
det (TyPeelR-Λ v rel unique ⊢s same)
    (TyPeelR-Λ v′ rel′ unique′ ⊢s′ same′) | refl = refl
det (TyPeelR-Λ v rel unique ⊢s same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-Λ v) I-all) st)
det (ξ-·[] st) (TyPeelR-Λ v rel unique ⊢s same) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-Λ v) I-all) st)

-- The wrapper clause's two contracta agree because the SOURCE type is a
-- function of the conversion and the type context (`conv-src-unique`), so
-- the two premises determine the SAME pushed-in annotation.
det (TyPeelR-⟪⟫ v ri rc uᵢ u ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ uᵢ′ u′ ⊢s′ sm′ same′)
  with interior-functional ri ri′ | conversion-functional rc rc′
det (TyPeelR-⟪⟫ v ri rc uᵢ u ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ uᵢ′ u′ ⊢s′ sm′ same′) | refl | refl
  with conv-src-unique u ⊢s ⊢s′
det (TyPeelR-⟪⟫ v ri rc uᵢ u ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ uᵢ′ u′ ⊢s′ sm′ same′) | refl | refl | refl
  with sameTy-src-unique uᵢ sm sm′
det (TyPeelR-⟪⟫ v ri rc uᵢ u ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ uᵢ′ u′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl
  with same-rep-unique same same′
det (TyPeelR-⟪⟫ v ri rc uᵢ u ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ uᵢ′ u′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl = refl
det (TyPeelR-⟪⟫ v ri rc uᵢ u ⊢s sm same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-⟪⟫ v I-all) I-all) st)
det (ξ-·[] st) (TyPeelR-⟪⟫ v ri rc uᵢ u ⊢s sm same) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-⟪⟫ v I-all) I-all) st)

-- CancelR — the two contracta agree because the lookup is a function.
det (CancelR v r⋉ u⋉ sm rel unique d)
    (CancelR v′ r⋉′ u⋉′ sm′ rel′ unique′ d′)
  with conversion-functional rel rel′ | conversion-functional r⋉ r⋉′
det (CancelR v r⋉ u⋉ sm rel unique d)
    (CancelR v′ r⋉′ u⋉′ sm′ rel′ unique′ d′) | refl | refl
  with ∋:=-det unique d d′
det (CancelR v r⋉ u⋉ sm rel unique d)
    (CancelR v′ r⋉′ u⋉′ sm′ rel′ unique′ d′) | refl | refl | refl
  with sameTy-src-unique u⋉ sm sm′
det (CancelR v r⋉ u⋉ sm rel unique d)
    (CancelR v′ r⋉′ u⋉′ sm′ rel′ unique′ d′)
    | refl | refl | refl | refl = refl
det (CancelR v r⋉ u⋉ sm rel unique d) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)
det (ξ-⟪⟫ frame st) (CancelR v r⋉ u⋉ sm rel unique d) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)

-- Drop$
det (Drop$ b)    (Drop$ b′)   = refl
det (Drop$ b) (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-$ st)
det (ξ-⟪⟫ frame st) (Drop$ b) = ⊥-elim (value-¬step V-$ st)

-- Drop-true / Drop-false
det Drop-true Drop-true = refl
det Drop-true (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-true st)
det (ξ-⟪⟫ frame st) Drop-true = ⊥-elim (value-¬step V-true st)
det Drop-false Drop-false = refl
det Drop-false (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-false st)
det (ξ-⟪⟫ frame st) Drop-false = ⊥-elim (value-¬step V-false st)

-- IdPush — likewise determined by the lookup.
det (IdPush v ri r₁ r⋉ u⋉ sm rel unique d)
    (IdPush v′ ri′ r₁′ r⋉′ u⋉′ sm′ rel′ unique′ d′)
  with interior-functional ri ri′ | conversion-functional rel rel′
det (IdPush v ri r₁ r⋉ u⋉ sm rel unique d)
    (IdPush v′ ri′ r₁′ r⋉′ u⋉′ sm′ rel′ unique′ d′) | refl | refl
  with conversion-functional r₁ r₁′ | conversion-functional r⋉ r⋉′
det (IdPush v ri r₁ r⋉ u⋉ sm rel unique d)
    (IdPush v′ ri′ r₁′ r⋉′ u⋉′ sm′ rel′ unique′ d′)
    | refl | refl | refl | refl
  with sameTy-src-unique u⋉ sm sm′ | ∋:=-det unique d d′
det (IdPush v ri r₁ r⋉ u⋉ sm rel unique d)
    (IdPush v′ ri′ r₁′ r⋉′ u⋉′ sm′ rel′ unique′ d′)
    | refl | refl | refl | refl | refl | refl = refl
det (IdPush v ri r₁ r⋉ u⋉ sm rel unique d) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)
det (ξ-⟪⟫ frame st) (IdPush v ri r₁ r⋉ u⋉ sm rel unique d) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)

-- the congruences
det (ξ-·-l st)   (ξ-·-l st′)  = cong (_· _) (det st st′)
det (ξ-·-l st)   (ξ-·-r v st′) = ⊥-elim (value-¬step v st)
det (ξ-·-r v st) (ξ-·-l st′)  = ⊥-elim (value-¬step v st′)
det (ξ-·-r v st) (ξ-·-r u st′) = cong (_ ·_) (det st st′)
det (ξ-·[] st) (ξ-·[] st′) =
  cong (λ L → L ·[ _ , _ ]) (det st st′)
det (ξ-Λ st)     (ξ-Λ st′)    = cong Λ_ (det st st′)
det (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  with interior-functional rel rel′
det (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′) | refl =
  cong (λ M → M ⟪ _ , _ ⟫) (det st st′)
