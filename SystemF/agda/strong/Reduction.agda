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
-- 1.  The canonical conversion at a slot
------------------------------------------------------------------------

-- Unseal every occurrence of X where the conversion runs covariantly /
-- seal it back where it runs contravariantly.  These are what the
-- boundary rules mint at a fresh binder; they are DERIVED FROM THE TYPE,
-- not from stored knowledge, and they carry only the NAME X.
mutual
  reveal : ℕ → Ty → Conv
  reveal X (` Y) with X ≟ℕ Y
  ... | yes _ = unseal X
  ... | no  _ = id (` Y)
  reveal X `ℕ      = id `ℕ
  reveal X `𝔹      = id `𝔹
  reveal X (A ⇒ B) = conceal X A ↦ reveal X B
  reveal X (`∀ A)  = `∀ (reveal (suc X) A)

  conceal : ℕ → Ty → Conv
  conceal X (` Y) with X ≟ℕ Y
  ... | yes _ = seal X
  ... | no  _ = id (` Y)
  conceal X `ℕ      = id `ℕ
  conceal X `𝔹      = id `𝔹
  conceal X (A ⇒ B) = reveal X A ↦ conceal X B
  conceal X (`∀ A)  = `∀ (conceal (suc X) A)

-- THE SAME MINT, APPLIED TO A CONVERSION (the TyPeelR repair,
-- notes/RuleRepairs-TyPeelR-CancelR.md §1).  When a boundary whose
-- conversion is a `` `∀ `` is instantiated, the boundary's frame gains
-- a BINDER at slot 0 — the slot the conversion's `` `∀ `` had left
-- ABSTRACT.  Every leaf of the conversion that reads that slot is an
-- identity (`id (` 0)`, because an abstract slot has no binder to seal or
-- unseal at), and each such leaf must become the instantiation step:
-- `unseal 0` where the conversion runs covariantly, `seal 0` where it
-- runs contravariantly.  That is exactly `reveal`/`conceal`, pushed
-- through a CONVERSION instead of through a type — and on an identity
-- conversion the two agree (`instReveal-mkId` below).
mutual
  instReveal : ℕ → Conv → Conv
  instReveal X (id A)     = reveal X A
  instReveal X (seal Y)   = seal Y
  instReveal X (unseal Y) = unseal Y
  instReveal X (s ↦ t)    = instConceal X s ↦ instReveal X t
  instReveal X (`∀ s)     = `∀ (instReveal (suc X) s)

  instConceal : ℕ → Conv → Conv
  instConceal X (id A)     = conceal X A
  instConceal X (seal Y)   = seal Y
  instConceal X (unseal Y) = unseal Y
  instConceal X (s ↦ t)    = instReveal X s ↦ instConceal X t
  instConceal X (`∀ s)     = `∀ (instConceal (suc X) s)

-- TyBeta's minted conversion IS this operation at an identity
-- conversion: the type version is the conversion version on `mkId`.  (So
-- TyPeelR's reveal case really is TyBeta's mint, one ∀ inside.)
mutual
  instReveal-mkId : (X : ℕ) (B : Ty) → instReveal X (mkId B) ≡ reveal X B
  instReveal-mkId X (` Y)   = refl
  instReveal-mkId X `ℕ      = refl
  instReveal-mkId X `𝔹      = refl
  instReveal-mkId X (A ⇒ B) =
    cong₂ _↦_ (instConceal-mkId X A) (instReveal-mkId X B)
  instReveal-mkId X (`∀ A)  = cong `∀ (instReveal-mkId (suc X) A)

  instConceal-mkId : (X : ℕ) (B : Ty) → instConceal X (mkId B) ≡ conceal X B
  instConceal-mkId X (` Y)   = refl
  instConceal-mkId X `ℕ      = refl
  instConceal-mkId X `𝔹      = refl
  instConceal-mkId X (A ⇒ B) =
    cong₂ _↦_ (instReveal-mkId X A) (instConceal-mkId X B)
  instConceal-mkId X (`∀ A)  = cong `∀ (instConceal-mkId (suc X) A)

------------------------------------------------------------------------
-- 2.  The dual of a crossed boundary
------------------------------------------------------------------------

-- THE DUAL, in full.  It mints ONLY name-carrying entries: a `lock` for each
-- of the crossed boundary's binders (the argument may not see them) and an
-- `unlock` for each of its conceals (the argument came from outside, where they
-- were nameable).  Nothing is copied, nothing is guarded, nothing is
-- demoted; the old design's `entᴳ` has no analogue.
hideBinds : ℕ → CtxMorph
hideBinds zero    = []
hideBinds (suc k) = lock k ∷ hideBinds k

-- THE DUAL IS AN INVERSE, AND AN INVERSE RUNS BACKWARDS (2026-09-06).
--
-- The mini-core DROPPED the `unlock` case, on the reading that an
-- `unlock` "claims nothing".  It claims plenty: it UNMASKS, and a dual
-- that does not re-mask hands the crossing argument a frame STRICTLY MORE
-- NAMEABLE than the exterior — `Peel` GAINS SCOPE, machine-checked in
-- proof/DualTightness.agda.  So `unlock X ↦ lock (n + X)`, and the
-- restoring `lock` is sound exactly because `mw-u` (strong.Terms) refuses
-- a VACUOUS unlock: `mask ∘ unmask` is the identity at a LOCKED slot
-- (`mask-unmask`, strong.Ctx) and nowhere else.
--
-- AND THE LIST IS REVERSED.  `scope` applies its list HEAD-LAST, so
-- undoing it runs the entries BACK TO FRONT; a same-order dual is not an
-- inverse at a frame that toggles one slot twice (`Θ = ↥X ∷ ↧X ∷ []`,
-- which the judgement admits).  With both repairs the frame identity is
-- EXACT (proof/PeelDual, `interior-dual`): the crossing argument's frame
-- is the exterior itself, one bind prefix in, and it crosses by
-- `⊢rename` alone — no `⊢retag`, no `le-mu`.
dualScope : ℕ → CtxMorph → CtxMorph
dualScope n []             = []
dualScope n (bind A ∷ Θ)   = dualScope n Θ
dualScope n (unlock X ∷ Θ) = dualScope n Θ ++ (lock   (n + X) ∷ [])
dualScope n (lock X ∷ Θ)   = dualScope n Θ ++ (unlock (n + X) ∷ [])

dual : CtxMorph → CtxMorph
dual Θ = hideBinds (numBinds Θ) ++ dualScope (numBinds Θ) Θ

-- (The old Cancel residue `repsOf→bind` — a frame that rebinds Θ₂'s binders
-- and nothing else — is GONE with the rule that wrote it: the repaired
-- CancelR keeps both frames and mints none.)

------------------------------------------------------------------------
-- 2b.  THE SCOPE MOVE — the outer frame's locks go INTO the inner one
------------------------------------------------------------------------

-- JEREMY'S MOVE (2026-09-06).  CancelR and IdPush both SWAP the two
-- conversions: the inner boundary stops presenting the abstract name
-- `` ` Y `` and starts presenting Y's REP.  A rep is read on the outer
-- boundary's CONVERSION CONTEXT (its locks lifted), so it is nameable
-- there and NOT, in general, inside the outer boundary's own locks — that
-- was the wall (the old proof/PreserveObstruct §4).
--
-- The repair is not a side condition but a FRAME MOVE: the outer frame's
-- whole SCOPE travels into the inner frame's TAIL, where `scope` applies
-- it FIRST — exactly where it applied before — and what stays outside is
-- the frame with its own scope REWOUND (`rewind Θ₂`), whose net effect on
-- the exterior is its BIND PREFIX alone.  The rep is then presented
-- OUTSIDE the locks, where it is nameable, and the locks still stand
-- between the value and the world.
--
-- WHY THE UNLOCKS TRAVEL TOO.  `scope` applies its list HEAD-LAST, so
-- moving only the LOCKS past a same-slot `unlock` reorders a mask/unmask
-- pair, and the value's frame is then not refined but CORRUPTED — a slot
-- it may name is masked in the contractum and was not in the redex
-- (`¬frame-locksOnly`, proof/MoveScope §4b, at the ⊢ᵐ-legal
-- `Θ₂ = unlock 0 ∷ lock 0 ∷ []`).  Moving the WHOLE scope keeps the
-- order, and then the value's frame is preserved ON THE NOSE: the two
-- frame lemmas are EQUALITIES, no `⊢retag` appears in either case, and
-- there is no premise about Θ₂'s shape for Progress to supply.

-- The outer frame's scope entries, lifted past its own binders.
scopeOf : ℕ → CtxMorph → CtxMorph
scopeOf n []             = []
scopeOf n (bind A ∷ Θ)   = scopeOf n Θ
scopeOf n (unlock X ∷ Θ) = unlock (n + X) ∷ scopeOf n Θ
scopeOf n (lock X ∷ Θ)   = lock (n + X) ∷ scopeOf n Θ

-- WHAT IS LEFT OF THE OUTER FRAME: the frame with its OWN SCOPE REWOUND.
--
-- `rewind Θ` is Θ with its inverse scope run on top, so its net effect on
-- the exterior is the BIND PREFIX ALONE:
--
--     scope    (rewind Θ) Δ ≡ Δ                       (given Δ ⊢ᵐ Θ)
--     interior (rewind Θ) Δ ≡ pushBinds (repsOf Θ) Δ
--
-- which is what makes the moved scope reproduce the redex's frame ON THE
-- NOSE (`interior-⋉-rewind`, proof/MoveScope) — no `⊢retag` and no
-- `le-mu` anywhere in the two cases.
--
-- IT IS NOT `bindsOnly Θ`, AND THAT IS THE POINT.  Simply DELETING Θ's
-- scope has the same effect on the type context but loses the frame's own
-- `⊢ᵐ`: Θ's bind reps are read on `unlockedScope Θ′ Δ` (strong.Terms,
-- `mw-b`) and a rep naming a slot Θ's tail UNLOCKED is not well formed on
-- the plain Δ.  Keeping the entries and rewinding them keeps every rep
-- exactly where it was read.
rewind : CtxMorph → CtxMorph
rewind Θ = dualScope 0 Θ ++ Θ

-- The inner frame, with the outer frame's scope moved in at its TAIL.
-- `numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁`: the move carries no binder.
infixl 5 _⋉_
_⋉_ : CtxMorph → CtxMorph → CtxMorph
Θ₁ ⋉ Θ₂ = Θ₁ ++ scopeOf (numBinds Θ₂) Θ₂

------------------------------------------------------------------------
-- 3.  The rules
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
-- 4.  VALUES DON'T STEP
------------------------------------------------------------------------

-- With V-Λ's `Value N` premise this holds on the nose.  (In the mini-core it
-- was false: `Λ N` was a value for every N while ξ-Λ reduced under it.)
value-¬step : ∀ {Δ M M′} → Value M → Δ ⊢ M -→ M′ → ⊥
value-¬step (V-⟪⟫ v I-idv) (Drop$ ())
value-¬step (V-⟪⟫ v ic)    (ξ-⟪⟫ st) = value-¬step v st
value-¬step (V-Λ v)        (ξ-Λ st)  = value-¬step v st

------------------------------------------------------------------------
-- 5.  DETERMINISM
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
