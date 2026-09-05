module strong.Reduction where

-- Strong System F — REDUCTION.
--
-- The rule set of the conversion-boundary design, with the repairs ruled in
-- notes/DECISIONS.md ("Id-layer RULING", 2026-09-05) applied:
--
--   (1) V-Λ carries `Value N` (in strong.Terms) — reduction goes under Λ.
--   (2) TyPeelR shifts its type annotation.
--   (3) CancelR drops the `lockBinds` residue, carries the OWNER-LOOKUP
--       premise that determines its `idc` face, and names its two faces
--       separately (the single-name presumption, examined below).
--   (4) IdPush replaces IdAbsorb: the two faces are SWAPPED instead of the
--       two frames being merged, so no context morphism arithmetic (`⊳`) is needed
--       and the no-⊕ test is passed by construction.
--   (5) TyBeta carries `Value N` — see the note on the rule.  Without it
--       TyBeta and ξ-·[] ⨟ ξ-Λ are a genuine overlap (repair (1) alone does
--       not close it), so determinism would still be false.
--
-- The principle behind (3)/(4): EVERY rule that mints an identity face at a
-- looked-up rep carries the owner-lookup premise, and determinism for those
-- rules is exactly `∋:=-det`.

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

-- Unseal every occurrence of X (read in the ↑ polarity) / seal it back (in
-- the ↓ polarity).  These are what the reveal rules mint; they are DERIVED
-- from the face type, not from stored knowledge, and they carry only the
-- NAME X.
mutual
  unsealAt : ℕ → Ty → Conv
  unsealAt X (` Y) with X ≟ℕ Y
  ... | yes _ = unseal X
  ... | no  _ = id (` Y)
  unsealAt X `ℕ      = id `ℕ
  unsealAt X `𝔹      = id `𝔹
  unsealAt X (A ⇒ B) = sealAt X A ↦ unsealAt X B
  unsealAt X (`∀ A)  = `∀ (unsealAt (suc X) A)

  sealAt : ℕ → Ty → Conv
  sealAt X (` Y) with X ≟ℕ Y
  ... | yes _ = seal X
  ... | no  _ = id (` Y)
  sealAt X `ℕ      = id `ℕ
  sealAt X `𝔹      = id `𝔹
  sealAt X (A ⇒ B) = unsealAt X A ↦ sealAt X B
  sealAt X (`∀ A)  = `∀ (sealAt (suc X) A)

------------------------------------------------------------------------
-- 2.  The dual of a crossed boundary
------------------------------------------------------------------------

-- THE DUAL, in full.  It mints ONLY name-carrying entries: a `lock` for each
-- of the crossed boundary's owners (the argument may not see them) and an
-- `unlock` for each of its conceals (the argument came from outside, where they
-- were nameable).  Nothing is copied, nothing is guarded, nothing is
-- demoted; the old design's `entᴳ` has no analogue.
lockBinds : ℕ → CtxMorph
lockBinds zero    = []
lockBinds (suc k) = lock k ∷ lockBinds k

dualS : ℕ → CtxMorph → CtxMorph
dualS n []          = []
dualS n (bind A ∷ Θ) = dualS n Θ
dualS n (unlock X ∷ Θ) = lock (n + X) ∷ dualS n Θ
dualS n (lock X ∷ Θ) = unlock (n + X) ∷ dualS n Θ

dual : CtxMorph → CtxMorph
dual Θ = lockBinds (nrev Θ) ++ dualS (nrev Θ) Θ

-- A context morphism that binds Θ's owners and nothing else (Cancel's residue).
reps→bind : List Ty → CtxMorph
reps→bind []       = []
reps→bind (A ∷ As) = bind A ∷ reps→bind As

reps-reps→bind : (As : List Ty) → reps (reps→bind As) ≡ As
reps-reps→bind []       = refl
reps-reps→bind (A ∷ As) = cong (A ∷_) (reps-reps→bind As)

nrev-reps→bind : (As : List Ty) → nrev (reps→bind As) ≡ length As
nrev-reps→bind As = cong length (reps-reps→bind As)

------------------------------------------------------------------------
-- 3.  The rules
------------------------------------------------------------------------

infix 2 _⊢_-→_
data _⊢_-→_ : Ctxᵗ → Term → Term → Set where

  -- A boundary is BORN: the ∀-elimination mints THE OWNER of the event.
  --
  -- THE VALUE PREMISE (repair (5)).  This calculus reduces under Λ (ξ-Λ),
  -- so `Λ N` is a value only when N is one (V-Λ).  Without `Value N` here,
  -- `(Λ N) ·[ B , A ]` with N a redex has TWO distinct steps — this one and
  -- ξ-·[] ⨟ ξ-Λ — and determinism fails.  The premise mirrors Beta's.
  TyBeta : ∀ {Δ B A N} → Value N
    → Δ ⊢ (Λ N) ·[ B , A ] -→ N ⟪ bind A ∷ [] , unsealAt 0 B ⟫

  Beta : ∀ {Δ A N W} → Value W
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ]ᵐ

  -- PEEL — the crossing.  The application is pushed in one layer and the
  -- argument acquires the DUAL.  `s`/`t` are literally ↦'s components: the
  -- crossing argument's conversion is RE-BASED by the repointing.
  Peel : ∀ {Δ V W Θ s t} → Value V → Value W
    → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
        -→ (V · (wkᴹ (nrev Θ) W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫

  -- TYPEEL — the ∀-face analogue; the new owner is prepended and the
  -- elimination instantiates at the new owner's bind name.
  --
  -- THE ANNOTATION REPAIR (2).  `B` is read over `abst ∷ Δ`; the contractum
  -- reads it over `abst ∷ bind A ∷ Δ`, so it must be shifted past the new
  -- owner: `renameᵗ (extᵗ suc) B`.
  TyPeelR : ∀ {Δ V Θ s B A} → Value V
    → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) B , ` 0 ])
             ⟪ bind A ∷ renᴮ suc Θ , s ⟫

  -- CANCEL — a conceal directly under the owner it names.  The face match is
  -- DEFINITIONAL: `seal X` and `unseal Y` cite the SAME entry, so there is
  -- no second spelling to disagree with the first.
  --
  -- THE RESIDUE REPAIR (3a).  The mini-core appended `lockBinds (nrev Θ₂)`,
  -- which masks EXTERIOR slots that need not exist (proof/MaskFacts.agda,
  -- `¬Bwf-cancel-residue`).  It is dropped: `intC` retains the entries
  -- anyway and ⊢retag covers the extra knowledge.
  --
  -- THE SINGLE-NAME PRESUMPTION, EXAMINED (3b).  The mini-core wrote ONE
  -- name X on both faces.  That presumes `nrev Θ₁ ≡ 0`: the inner face is
  -- checked on `fceC Θ₁ (intC Θ₂ Δ)`, which is `nrev Θ₁` binders INSIDE the
  -- type context `fceC Θ₂ Δ` the outer face is checked on.  The honest general form
  -- carries TWO names — and needs no extra premise to relate them, because
  -- typing already FORCES `X ≡ nrev Θ₁ + Y` (proof/IdLayer.agda,
  -- `cancel-name`), exactly as it does for IdPush (`idpush-name`).
  --
  -- THE LOOKUP PREMISE (3c).  `idc A` is an identity face minted at a
  -- looked-up rep, so the rule carries the owner lookup; determinism for it
  -- is `∋:=-det`.
  CancelR : ∀ {Δ V Θ₁ Θ₂ X Y A} → Value V → fceC Θ₂ Δ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ V ⟪ reps→bind (reps Θ₂) , idc A ⟫

  -- DROP$ — a base-faced boundary over a numeral (`⊢$` types it anywhere).
  Drop$ : ∀ {Δ n Θ A} → Base A
    → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ -→ $ n

  -- IDPUSH (repair (4)) — the transparent-layer rule, as ruled.  An inert
  -- `id (` X)` layer under an ACTIVE face is not a value and no other rule
  -- fires; instead of merging the two frames (IdAbsorb's `⊳`, retired for
  -- failing the no-⊕ test) the two FACES are swapped: the transparent layer
  -- becomes the revealing one and the outer becomes transparent.  BOTH
  -- FRAMES ARE UNTOUCHED.  `unseal` is the only active face this LHS can
  -- meet (proof/IdLayer.agda, `outer-id-base-untypeable`), and the pushed
  -- name is already written in the id-face (`idpush-name`).
  IdPush : ∀ {Δ V Θ₁ Θ₂ X Y A} → Value V → fceC Θ₂ Δ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , idc A ⟫

  ξ-·-l : ∀ {Δ L L′ M} → Δ ⊢ L -→ L′ → Δ ⊢ L · M -→ L′ · M
  ξ-·-r : ∀ {Δ V M M′} → Value V → Δ ⊢ M -→ M′ → Δ ⊢ V · M -→ V · M′
  ξ-·[] : ∀ {Δ L L′ B A} → Δ ⊢ L -→ L′ → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ]
  ξ-Λ   : ∀ {Δ N N′} → (abst ∷ Δ) ⊢ N -→ N′ → Δ ⊢ Λ N -→ Λ N′
  ξ-⟪⟫  : ∀ {Δ M M′ Θ c} → intC Θ Δ ⊢ M -→ M′
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

-- TyPeelR
det (TyPeelR v)  (TyPeelR v′) = refl
det (TyPeelR v)  (ξ-·[] st)   = ⊥-elim (value-¬step (V-⟪⟫ v I-all) st)
det (ξ-·[] st)   (TyPeelR v)  = ⊥-elim (value-¬step (V-⟪⟫ v I-all) st)

-- CancelR — the two contracta agree because the lookup is a function.
det (CancelR v d) (CancelR v′ d′) = cong (λ A → _ ⟪ _ , idc A ⟫) (∋:=-det d d′)
det (CancelR v d) (ξ-⟪⟫ st) = ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)
det (ξ-⟪⟫ st) (CancelR v d) = ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)

-- Drop$
det (Drop$ b)    (Drop$ b′)   = refl
det (Drop$ b)    (ξ-⟪⟫ st)    = ⊥-elim (value-¬step V-$ st)
det (ξ-⟪⟫ st)    (Drop$ b)    = ⊥-elim (value-¬step V-$ st)

-- IdPush — likewise determined by the lookup.
det (IdPush v d) (IdPush v′ d′) = cong (λ A → _ ⟪ _ , idc A ⟫) (∋:=-det d d′)
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
