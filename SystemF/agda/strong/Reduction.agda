module strong.Reduction where

-- Strong System F — REDUCTION.
--
-- The rule set of the conversion-boundary design, with the repairs ruled in
-- notes/DECISIONS.md ("Id-layer RULING", 2026-09-05) applied:
--
--   (1) V-Λ carries `Value N` (in strong.Terms) — reduction goes under Λ.
--   (2) TyPeelR shifts its type annotation.
--   (3) CancelR drops the `hideBinds` residue, carries the BINDER-LOOKUP
--       premise that determines its `mkId` conversion, and names its two
--       conversions separately (the single-name presumption, examined
--       below).
--   (4) IdPush replaces IdAbsorb: the two conversions are SWAPPED
--       instead of the two frames being merged, so no context morphism
--       arithmetic (`⊳`) is needed and the no-⊕ test is passed by
--       construction.
--   (5) TyBeta carries `Value N` — see the note on the rule.  Without it
--       TyBeta and ξ-·[] ⨟ ξ-Λ are a genuine overlap (repair (1) alone does
--       not close it), so determinism would still be false.
--
-- The principle behind (3)/(4): EVERY rule that mints an identity
-- conversion at a looked-up rep carries the binder-lookup premise, and
-- determinism for those rules is exactly `∋:=-det`.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
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
  TyBeta : ∀ {Δ B A N} → Value N
    → Δ ⊢ (Λ N) ·[ B , A ] -→ N ⟪ bind A ∷ [] , reveal 0 B ⟫

  Beta : ∀ {Δ A N W} → Value W
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ]ᵐ

  -- PEEL — the crossing.  The application is pushed in one layer and the
  -- argument acquires the DUAL.  `s`/`t` are literally ↦'s components: the
  -- crossing argument's conversion is RE-BASED by the repointing.
  Peel : ∀ {Δ V W Θ s t} → Value V → Value W
    → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
        -→ (V · (wkᴹ (numBinds Θ) W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫

  -- TYPEEL — the ∀-conversion analogue; the new binder is prepended and the
  -- elimination instantiates at the new binder's bind name.
  --
  -- THE ANNOTATION REPAIR (2a).  The pushed-in `·[ _ , ` 0 ]` must carry
  -- the INTERIOR ∀-body — what the interior's own `⊢·[]` demands — not the
  -- exterior body `B`, from which it differs at every non-identity leaf.
  -- The interior body is not syntactic (a `seal`'s source is a binder's
  -- rep, which the rep-free conversion does not carry) but it IS
  -- DETERMINED by the conversion typing, so the rule carries that typing
  -- as a PREMISE — the same move already ruled for the `mkId`
  -- conversions.  It is read at the ∀-body, i.e. under one `abst`, and
  -- Progress derives it for free by inverting the redex's own `env`
  -- (`conv-all-inv`).  Determinism is `conv-types-unique`
  -- (strong.Conversion), exactly as it is `∋:=-det` for the lookup-carrying
  -- rules.
  --
  -- THE SHIFT REPAIR (2b).  `renᴮ suc Θ` double-counts: `interior` already
  -- lifts Θ's reps past the binder `bind A` prepended here
  -- (`interior (bind A ∷ Θ) Δ ≡ bind (shiftBy (numBinds Θ) A) ∷
  -- interior Θ Δ`), so the frame is plain `Θ`.
  --
  -- THE CONVERSION (2c).  Slot 0 of the conversion's body was ABSTRACT
  -- and is now the BINDER this rule introduces, so every leaf of `s` that
  -- reads it must become the instantiation step: `instReveal 0 s`.
  -- Keeping `s` itself is ill-typed — its TARGET body still mentions
  -- `` ` 0 `` where `env` demands the instantiated
  -- `shiftBy (numBinds Θ + 1) (Bₑ [ A ])`.
  TyPeelR : ∀ {Δ V Θ s B A Bᵢ Bₑ} → Value V
    → (abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
    → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
             ⟪ bind A ∷ Θ , instReveal 0 s ⟫

  -- CANCEL — a conceal directly under the binder it names.  The
  -- conversion match is DEFINITIONAL: `seal X` and `unseal Y` cite the
  -- SAME entry, so there is no second spelling to disagree with the
  -- first.
  --
  -- THE RESIDUE REPAIR (3a), AS RE-RULED (2026-09-05).  The mini-core
  -- appended `hideBinds (numBinds Θ₂)`, which masks EXTERIOR slots that need
  -- not exist (proof/MaskFacts.agda, `¬⊢ᵐ-cancel-residue`); dropping the
  -- residue was not enough either, because `repsOf→bind (repsOf Θ₂)` DISCARDS
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
  -- inner conversion is checked on `convCtx Θ₁ (interior Θ₂ Δ)`, which is
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
  -- presents the rep `shiftBy (numBinds Θ₁) A` where it presented the abstract
  -- name, so Θ₂'s LOCKS travel into the inner frame (§2b) — otherwise
  -- `env`'s last premise reads that rep INSIDE Θ₂'s masking.  The lift is
  -- unchanged, because `numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁`.
  CancelR : ∀ {Δ V Θ₁ Θ₂ X Y A} → Value V → convCtx Θ₂ Δ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId (shiftBy (numBinds Θ₁) A) ⟫)
             ⟪ rewind Θ₂ , mkId A ⟫

  -- DROP$ — an identity boundary at a base type, over a numeral (`⊢$`
  -- types it anywhere).
  Drop$ : ∀ {Δ n Θ A} → Base A
    → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ -→ $ n

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
  -- `pushBinds (repsOf Θ₂) Δ`, and `A ≡ shiftBy (numBinds Θ₂) C` for the redex's own
  -- exterior type C.  That is what retires the wall — the case needs no
  -- scoping invariant at all (proof/MoveScope.preserve-IdPush).
  IdPush : ∀ {Δ V Θ₁ Θ₂ X Y A} → Value V → convCtx Θ₂ Δ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal X ⟫) ⟪ rewind Θ₂ , mkId A ⟫

  ξ-·-l : ∀ {Δ L L′ M} → Δ ⊢ L -→ L′ → Δ ⊢ L · M -→ L′ · M
  ξ-·-r : ∀ {Δ V M M′} → Value V → Δ ⊢ M -→ M′ → Δ ⊢ V · M -→ V · M′
  ξ-·[] : ∀ {Δ L L′ B A} → Δ ⊢ L -→ L′ → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ]
  ξ-Λ   : ∀ {Δ N N′} → (abst ∷ Δ) ⊢ N -→ N′ → Δ ⊢ Λ N -→ Λ N′
  ξ-⟪⟫  : ∀ {Δ M M′ Θ c} → interior Θ Δ ⊢ M -→ M′
        → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ Θ , c ⟫

infix 2 _⊢_-→*_
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : ∀ {Δ M} → Δ ⊢ M -→* M
  _then_ : ∀ {Δ L M N} → Δ ⊢ L -→ M → Δ ⊢ M -→* N → Δ ⊢ L -→* N

infixr 2 _then_

------------------------------------------------------------------------
-- 2.  VALUES DON'T STEP
------------------------------------------------------------------------

-- With V-Λ's `Value N` premise this holds on the nose.  (In the mini-core it
-- was false: `Λ N` was a value for every N while ξ-Λ reduced under it.)
value-¬step : ∀ {Δ M M′} → Value M → Δ ⊢ M -→ M′ → ⊥
value-¬step (V-⟪⟫ v I-idv) (Drop$ ())
value-¬step (V-⟪⟫ v ic)    (ξ-⟪⟫ st) = value-¬step v st
value-¬step (V-Λ v)        (ξ-Λ st)  = value-¬step v st

------------------------------------------------------------------------
-- 3.  DETERMINISM
------------------------------------------------------------------------

det : ∀ {Δ M M₁ M₂} → Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂

-- TyBeta
det (TyBeta v)   (TyBeta v′)  = refl
det (TyBeta v)   (ξ-·[] st)   = ⊥-elim (value-¬step (V-Λ v) st)
det (ξ-·[] st)   (TyBeta v)   = ⊥-elim (value-¬step (V-Λ v) st)

-- Beta
det (Beta w)     (Beta w′)    = refl
det (Beta w)     (ξ-·-l st)   = ⊥-elim (value-¬step V-ƛ st)
det (Beta w)     (ξ-·-r v st) = ⊥-elim (value-¬step w st)
det (ξ-·-l st)   (Beta w)     = ⊥-elim (value-¬step V-ƛ st)
det (ξ-·-r v st) (Beta w)     = ⊥-elim (value-¬step w st)

-- Peel
det (Peel v w)   (Peel v′ w′) = refl
det (Peel v w)   (ξ-·-l st)   = ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det (Peel v w)   (ξ-·-r u st) = ⊥-elim (value-¬step w st)
det (ξ-·-l st)   (Peel v w)   = ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det (ξ-·-r u st) (Peel v w)   = ⊥-elim (value-¬step w st)

-- TyPeelR — the two contracta agree because the SOURCE AND TARGET TYPES
-- are a function of the conversion and the type context
-- (`conv-types-unique`), so the two premises determine the SAME pushed-in
-- annotation.
det (TyPeelR {V = V} {Θ = Θ} {s = s} {A = A} v ⊢s) (TyPeelR v′ ⊢s′) =
  cong (λ T → (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) T , ` 0 ])
                ⟪ bind A ∷ Θ , instReveal 0 s ⟫)
       (conv-src-unique ⊢s ⊢s′)
det (TyPeelR v ⊢s) (ξ-·[] st)     = ⊥-elim (value-¬step (V-⟪⟫ v I-all) st)
det (ξ-·[] st)     (TyPeelR v ⊢s) = ⊥-elim (value-¬step (V-⟪⟫ v I-all) st)

-- CancelR — the two contracta agree because the lookup is a function.
det (CancelR {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} v d) (CancelR v′ d′) =
  cong (λ T → (V ⟪ Θ₁ ⋉ Θ₂ , mkId (shiftBy (numBinds Θ₁) T) ⟫)
                ⟪ rewind Θ₂ , mkId T ⟫)
       (∋:=-det d d′)
det (CancelR v d) (ξ-⟪⟫ st) = ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)
det (ξ-⟪⟫ st) (CancelR v d) = ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)

-- Drop$
det (Drop$ b)    (Drop$ b′)   = refl
det (Drop$ b)    (ξ-⟪⟫ st)    = ⊥-elim (value-¬step V-$ st)
det (ξ-⟪⟫ st)    (Drop$ b)    = ⊥-elim (value-¬step V-$ st)

-- IdPush — likewise determined by the lookup.
det (IdPush v d) (IdPush v′ d′) = cong (λ A → _ ⟪ _ , mkId A ⟫) (∋:=-det d d′)
det (IdPush v d) (ξ-⟪⟫ st) = ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)
det (ξ-⟪⟫ st) (IdPush v d) = ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)

-- the congruences
det (ξ-·-l st)   (ξ-·-l st′)  = cong (_· _) (det st st′)
det (ξ-·-l st)   (ξ-·-r v st′) = ⊥-elim (value-¬step v st)
det (ξ-·-r v st) (ξ-·-l st′)  = ⊥-elim (value-¬step v st′)
det (ξ-·-r v st) (ξ-·-r u st′) = cong (_ ·_) (det st st′)
det (ξ-·[] st)   (ξ-·[] st′)  = cong (λ L → L ·[ _ , _ ]) (det st st′)
det (ξ-Λ st)     (ξ-Λ st′)    = cong Λ_ (det st st′)
det (ξ-⟪⟫ st)    (ξ-⟪⟫ st′)   = cong (λ M → M ⟪ _ , _ ⟫) (det st st′)
