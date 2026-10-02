module Reduction where

-- File Charter:
--   * §0 (GTNF) `InstX`, design.md §6.2's meta-operation `inst_X`, and
--     `exitEnv`, the mode environment of a tag `IdDyn` moves out.
--     §1 `_⊢_-→_∣_`: νF's rules TyBeta (now through `InstX`, which
--     subsumes νF's TyWrap as its boundary case), Beta, Wrap, Merge,
--     Id; GTNF's cast rules CastId, CastSeq, CastSeq?, CastFun, Inst,
--     TagUntag,
--     TagUntagBad, IdDyn/IdDyn-var, TagUntagBad-⟪⟫, BlameBotIntro; the
--     blame rules Blame-·₁, Blame-·₂, Blame-ν, Blame-⟪⟫, Blame-cast (one
--     per frame of design.md §6.1); and the congruences ξ-·₁, ξ-·₂,
--     ξ-ν, ξ-⟪⟫, ξ-cast (NO ξ-Λ) — with `TyBeta-ℕ`, the multi-step
--     `_⊢_-→*_` and `runCtx`.  §2 `value-¬step`.
--   * NO OPERATORS.  νF's Agda has no primitive operators, so design.md's
--     `op(M⃗)`, `Delta` and the operator frame are not here.
--   * DE BRUIJN READINGS OF design.md §6 (each also in the report):
--     - `IdDyn` re-tags with the EXTERIOR spelling of the name:
--       `toExt Θ X ≡ just X′` is both the side condition `X ∉ fresh(δ)`
--       and the new spelling; the identity left inside, `id(X)`, is
--       spelled on the CONVERSION context and carried as `Xᶜ`, pinned
--       by `_⊢_≈_⊣_` (the crossing-spelling law below).  A non-name
--       ground tag needs neither, so it is the separate rule `IdDyn`.
--     - The moved tag's cast carries `exitEnv`: the interior modes read
--       back at the exterior positions, `X∼X` for exterior names the
--       interior does not see.
--     - `TyBeta`'s `gen` case puts the value under `genᵖ` beneath the
--       binder's dual (`crossΛᴹ`, TermSubst §5) instead of weakening it
--       by the new name, and gives the freed variable the mode `★∼X`;
--       the `∀ᵖ` case gives it `X∼X`.
--     - CastFun's argument cast carries `flipEnv μ` (GTSFImp `β-⇒`:
--       the domain coercion was typed under the flipped environment).
--   * THE STORE CHANGE.  A step returns the change `δ : Alloc` it made
--     to the store, so the contractum lives at `apply δ Δ` and each
--     congruence shifts the redex's siblings by `↑ᴹ[ δ ]`/`↑ᴮ[ δ ]`.
--   * THE CROSSING-SPELLING LAW.  When a rule MOVES a subterm between
--     two name maps, the moved spelling is CARRIED as a named premise
--     and PINNED by `SameConv` or `_⊢_≈_⊣_`, never computed by a fixed
--     renaming.  Three spellings are carried: Wrap's `s′`, Merge's
--     `t₁′` and `c₂′`.
-- Commentary (νF): SystemF/agda/strong-rep-nu/Commentary.md § Reduction.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import Types
  using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ; Base; base-ℕ; base-𝔹)
open import Ctx
open import proof.Ctx
open import Conversion
open import Coercion
open import Terms
open import Boundary
open import TermSubst

------------------------------------------------------------------------
-- 0.  (GTNF) inst_X, and the environment of a moved tag
------------------------------------------------------------------------

-- `InstX V N`: instantiate the ∀-value V at the new name 0 of `TyBeta`'s
-- boundary, reaching through every layer (design.md §6.2).  N is read
-- in that boundary's interior.  A cast stays a cast and a boundary stays
-- a boundary; nothing is allocated here.
data InstX : Term → Term → Set where
  -- inst_X(ΛX. V) = V
  inst-Λ   : ∀ {N} → Value N → InstX (Λ N) N
  -- inst_X(W ⟨gen X. p⟩) = ([−X^α] W ⟨Id(A)⟩) ⟨p⟩: W does NOT move
  -- under the new name; it sits under the binder's dual (`crossΛᴹ`), so
  -- its names keep their spelling and only the representation universe
  -- shifts for the allocation.  The freed variable keeps the gen mode.
  inst-gen : ∀ {W μ p} → Value W
    → InstX (W ⟨ μ ∣ genᵖ p ⟩)
            (crossΛᴹ W (srcᵖ (genᵖ p)) ⟨ ★∼X ∷ μ ∣ p ⟩)
  -- inst_X(W ⟨∀X. p⟩) = inst_X(W) ⟨p⟩, the freed variable strict
  inst-∀   : ∀ {W N μ p} → Value W → InstX W N
    → InstX (W ⟨ μ ∣ ∀ᵖ p ⟩) (N ⟨ X∼X ∷ μ ∣ p ⟩)
  -- inst_X([δ] U ⟨∀X. c⟩) = [δ] inst_X(U) ⟨c⟩ (νF's TyWrap): the scope
  -- is read under the new name (`liftᴮ`), the conversion moves verbatim
  -- U SIMPLE: a boundary over a boundary is a Merge redex, not a value
  inst-⟪⟫  : ∀ {U N Θ s} → Simple U → InstX U N
    → InstX (U ⟪ Θ , ⌞ `∀ s ⌟ ⟫) (N ⟪ liftᴮ Θ , s ⟫)

-- the mode of exterior position j: the mode of the interior name that
-- `toExt` sends to j, or `X∼X` if the interior does not see it
modeAtExt : Boundary → ModeEnv → ℕ → ℕ → Mode
modeAtExt Θ []      i j = X∼X
modeAtExt Θ (m ∷ μ) i j with toExt Θ i
modeAtExt Θ (m ∷ μ) i j | nothing = modeAtExt Θ μ (suc i) j
modeAtExt Θ (m ∷ μ) i j | just j′ with j ≟ j′
modeAtExt Θ (m ∷ μ) i j | just j′ | yes _ = m
modeAtExt Θ (m ∷ μ) i j | just j′ | no  _ = modeAtExt Θ μ (suc i) j

-- `exitEnvFrom Θ μ j r`: the modes of exterior positions j, …, j+r-1
exitEnvFrom : Boundary → ModeEnv → ℕ → ℕ → ModeEnv
exitEnvFrom Θ μ j zero    = []
exitEnvFrom Θ μ j (suc r) = modeAtExt Θ μ 0 j ∷ exitEnvFrom Θ μ (suc j) r

-- `exitEnv Θ μ n`: the exterior environment, n names long
exitEnv : Boundary → ModeEnv → ℕ → ModeEnv
exitEnv Θ μ n = exitEnvFrom Θ μ 0 n

------------------------------------------------------------------------
-- 1.  The rules
------------------------------------------------------------------------

-- the small-step relation, indexed by the store change it made
-- νF Commentary.md § Reduction.agda / `_⊢_-→_∣_` — the store change
infix 2 _⊢_-→_∣_
data _⊢_-→_∣_ : Ctxᵗ → Term → Term → Alloc → Set where

  -- a boundary is BORN: `ν` creates THE BINDER of the event, and the
  -- conversion is the one `ν` carries.  (GTNF) V is any ∀-value, and
  -- `InstX` instantiates it through all of its layers.
  TyBeta : ∀ {Δ A R V N c} → Value V → InstX V N
    → Δ ⊢ᶜ A ~ R
      --------------------------------------------------
    → Δ ⊢ ν A · V ⟨ c ⟩ -→ N ⟪ inst [] , c ⟫ ∣ new R

  -- beta, FRAME-EXACT: the substitution carries the ƛ's annotation A
  Beta : ∀ {Δ A N W} → Value W
      ----------------------------------------
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ ∣ none

  -- THE CROSSING (νF): the application is pushed in one layer and the
  -- argument acquires the DUAL, whose spelling `s′` the rule carries.
  Wrap : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Simple V → Value W
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ
    → SameConv Δᵈ s′ Δᶜ s
      -----------------------------------------------
    → Δ ⊢ (V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · W
        -→ (V · (W ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫ ∣ none

  -- MERGE (νF) — a boundary directly over a boundary VALUE.  (GTNF) the
  -- inner value may be the fresh-tag form, whose `t₁` is `id ★`.
  Merge : ∀ {Δ Δᵢ Δ₁ᶜ Δ₂ᶜ Δ⋉ᶜ U Θ₁ Θ₂ t₁ t₁′ c₂ c₂′}
    → Value (U ⟪ Θ₁ , tail t₁ ⟫)
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
    → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
    → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂
      -------------------------------------------------
    → Δ ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫
        -→ U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫ ∣ none

  -- an identity boundary at a base type, over a simple value
  Id : ∀ {Δ U Θ A} → Simple U → Base A
      ----------------------------------
    → Δ ⊢ U ⟪ Θ , ⌞ id A ⌟ ⟫ -→ U ∣ none

  -- (GTNF) THE CAST RULES, design.md §6.3
  CastId : ∀ {Δ V μ A} → Value V
      ----------------------------------
    → Δ ⊢ V ⟨ μ ∣ idᵖ A ⟩ -→ V ∣ none

  -- the two evidence-shaped sequences split into their two casts
  CastSeq : ∀ {Δ V μ p G} → Value V
      ----------------------------------
    → Δ ⊢ V ⟨ μ ∣ p ︔ G ! ⟩ -→ V ⟨ μ ∣ p ⟩ ⟨ μ ∣ G ! ⟩ ∣ none

  CastSeq? : ∀ {Δ V μ p G ℓ} → Value V
      ----------------------------------
    → Δ ⊢ V ⟨ μ ∣ G ？ ℓ ︔ p ⟩ -→ V ⟨ μ ∣ G ？ ℓ ⟩ ⟨ μ ∣ p ⟩ ∣ none

  CastFun : ∀ {Δ V W μ p q} → Value V → Value W
      ----------------------------------
    → Δ ⊢ (V ⟨ μ ∣ p ↦ᵖ q ⟩) · W
        -→ (V · (W ⟨ flipEnv μ ∣ p ⟩)) ⟨ μ ∣ q ⟩ ∣ none

  -- instantiate at ★ by a ν X:=★, revealing the source, and close the
  -- coercion at ★ (no allocation here: the ν's TyBeta allocates).
  -- On a typed redex, V : ∀X. A and `⊢inst` gives
  --   p : A ⟹ ⇑ᵗ B   under  X∼★ ∷ μ   (A = srcᵖ p, ⇑ᵗ B = trgᵖ p),
  -- so the contractum is (ν …) : A[★/X], cast by closeᵖ 0 p to B.
  Inst : ∀ {Δ V μ p} → Value V
      ----------------------------------
    → Δ ⊢ V ⟨ μ ∣ instᵖ p ⟩
        -→ (ν ★ · V ⟨ reveal 0 (srcᵖ p) ⟩) ⟨ μ ∣ closeᵖ 0 p ⟩ ∣ none

  TagUntag : ∀ {Δ V μ μ′ G ℓ} → Value V
      ----------------------------------
    → Δ ⊢ V ⟨ μ ∣ G ! ⟩ ⟨ μ′ ∣ G ？ ℓ ⟩ -→ V ∣ none

  TagUntagBad : ∀ {Δ V μ μ′ G H ℓ} → Value V → G ≢ H
      ----------------------------------
    → Δ ⊢ V ⟨ μ ∣ G ! ⟩ ⟨ μ′ ∣ H ？ ℓ ⟩ -→ blame ℓ ∣ none

  -- move a tag out of a boundary: a non-name ground tag always moves
  IdDyn : ∀ {Δ V μ Θ G} → Value V → GroundNV G
      ----------------------------------
    → Δ ⊢ (V ⟨ μ ∣ G ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫
        -→ (V ⟪ Θ , mkId G ⟫) ⟨ exitEnv Θ μ (length (names Δ)) ∣ G ! ⟩
           ∣ none

  -- ... and a name moves when the exterior sees it (X ∉ fresh(δ)), at
  -- its exterior spelling X′; the identity left inside is spelled Xᶜ
  IdDyn-var : ∀ {Δ Δᵢ Δᶜ V μ Θ X X′ Xᶜ} → Value V
    → toExt Θ X ≡ just X′
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δᵢ ⊢ ` X ≈ ` Xᶜ ⊣ Δᶜ
      ----------------------------------
    → Δ ⊢ (V ⟨ μ ∣ (` X) ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫
        -→ (V ⟪ Θ , ⌞ id (` Xᶜ) ⌟ ⟫)
             ⟨ exitEnv Θ μ (length (names Δ)) ∣ (` X′) ! ⟩ ∣ none

  -- a check meets a tag that only the boundary keeps in scope
  TagUntagBad-⟪⟫ : ∀ {Δ V μ μ′ Θ X H ℓ} → Value V → Fresh Θ X
      ----------------------------------
    → Δ ⊢ ((V ⟨ μ ∣ (` X) ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫) ⟨ μ′ ∣ H ？ ℓ ⟩
        -→ blame ℓ ∣ none

  BlameBotIntro : ∀ {Δ V μ ℓ} → Value V
      ----------------------------------
    → Δ ⊢ V ⟨ μ ∣ bot-intro ℓ ⟩ -→ blame ℓ ∣ none

  -- BLAME, one rule per frame (design.md §6.1)
  Blame-·₁ : ∀ {Δ M ℓ}
    → Δ ⊢ blame ℓ · M -→ blame ℓ ∣ none

  Blame-·₂ : ∀ {Δ V ℓ} → Value V
    → Δ ⊢ V · blame ℓ -→ blame ℓ ∣ none

  Blame-ν : ∀ {Δ A c ℓ}
    → Δ ⊢ ν A · blame ℓ ⟨ c ⟩ -→ blame ℓ ∣ none

  Blame-⟪⟫ : ∀ {Δ Θ c ℓ}
    → Δ ⊢ blame ℓ ⟪ Θ , c ⟫ -→ blame ℓ ∣ none

  Blame-cast : ∀ {Δ μ p ℓ}
    → Δ ⊢ blame ℓ ⟨ μ ∣ p ⟩ -→ blame ℓ ∣ none

  -- THE CONGRUENCES pass the store change up and shift the SIBLINGS
  -- by it.
  ξ-·₁ : ∀ {Δ L L′ M δ} → Δ ⊢ L -→ L′ ∣ δ
      -------------------------------
    → Δ ⊢ L · M -→ L′ · ↑ᴹ[ δ ] M ∣ δ

  ξ-·₂ : ∀ {Δ V M M′ δ} → Value V → Δ ⊢ M -→ M′ ∣ δ
      -------------------------------
    → Δ ⊢ V · M -→ ↑ᴹ[ δ ] V · M′ ∣ δ

  ξ-ν : ∀ {Δ L L′ A c δ} → Δ ⊢ L -→ L′ ∣ δ
      ---------------------------------------
    → Δ ⊢ ν A · L ⟨ c ⟩ -→ ν A · L′ ⟨ c ⟩ ∣ δ

  -- (NO ξ-Λ: nothing reduces under a type binder — see `⊢Λ`.)
  ξ-⟪⟫  : ∀ {Δ Δᵢ M M′ Θ c δ} → Δ ⊢ⁱ Θ ⇒ Δᵢ
        → Δᵢ ⊢ M -→ M′ ∣ δ
          -------------------------------------------
        → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ ↑ᴮ[ δ ] Θ , c ⟫ ∣ δ

  -- (GTNF) the cast frame; a cast has no sibling to shift
  ξ-cast : ∀ {Δ M M′ μ p δ} → Δ ⊢ M -→ M′ ∣ δ
      ---------------------------------------
    → Δ ⊢ M ⟨ μ ∣ p ⟩ -→ M′ ⟨ μ ∣ p ⟩ ∣ δ

-- Concrete instantiation check: the ordinary argument `ℕ` translates to
-- representation payload `ℕ`, and `inst []` is TyBetaBoundary.
TyBeta-ℕ : empty ⊢ ν `ℕ · (Λ ($ 7)) ⟨ ⌞ id `ℕ ⌟ ⟩
  -→ ($ 7) ⟪ TyBetaBoundary , ⌞ id `ℕ ⌟ ⟫ ∣ new `ℕ
TyBeta-ℕ = TyBeta (V-simple (S-Λ (V-simple S-$))) (inst-Λ (V-simple S-$))
  same-ℕ

-- A run needs no store index: each step's change is applied to the
-- context the tail runs at.
infix 2 _⊢_-→*_
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : ∀ {Δ M} → Δ ⊢ M -→* M
  _then_ : ∀ {Δ L M N δ} → Δ ⊢ L -→ M ∣ δ → apply δ Δ ⊢ M -→* N
    → Δ ⊢ L -→* N

infixr 2 _then_

-- The context a run ENDS at: every step's change applied in order.
runCtx : ∀ {Δ M N} → Δ ⊢ M -→* N → Ctxᵗ
runCtx {Δ = Δ} done = Δ
runCtx (_then_ {δ = δ} st sts) = runCtx sts

------------------------------------------------------------------------
-- 2.  VALUES DON'T STEP
------------------------------------------------------------------------

-- the `S-Λ` case is absurd outright: there is no ξ-Λ; a `Merge` needs
-- a boundary over a boundary, which is not a value.  (GTNF) a cast
-- value's coercion is inert, which no cast rule's redex is; and a
-- fresh-tag boundary is never an `IdDyn-var` redex, since the name is
-- fresh exactly when `toExt` finds no exterior spelling.
value-¬step : ∀ {Δ M M′ δ} → Value M → Δ ⊢ M -→ M′ ∣ δ → ⊥
value-¬step (V-simple S-$) ()
value-¬step (V-simple S-true) ()
value-¬step (V-simple S-false) ()
value-¬step (V-simple S-ƛ) ()
value-¬step (V-simple (S-Λ v)) ()
value-¬step (V-simple (S-cast v ())) (CastId _)
value-¬step (V-simple (S-cast v ())) (CastSeq _)
value-¬step (V-simple (S-cast v ())) (CastSeq? _)
value-¬step (V-simple (S-cast v ())) (Inst _)
value-¬step (V-simple (S-cast v ())) (TagUntag _)
value-¬step (V-simple (S-cast v ())) (TagUntagBad _ _)
value-¬step (V-simple (S-cast v ())) (TagUntagBad-⟪⟫ _ _)
value-¬step (V-simple (S-cast v ())) (BlameBotIntro _)
value-¬step (V-simple (S-cast (V-simple ()) i)) Blame-cast
value-¬step (V-simple (S-cast v i)) (ξ-cast st) = value-¬step v st
value-¬step (V-⟪⟫ u I-idv) (Id u′ ())
value-¬step (V-⟪⟫ () it) (Merge v ri r₁ r₂ r⋉ sc₁ sc₂)
value-¬step (V-⟪⟫ () it) Blame-⟪⟫
value-¬step (V-⟪⟫ u it) (ξ-⟪⟫ rel st) = value-¬step (V-simple u) st
value-¬step (V-fresh v fr) (Id u ())
value-¬step (V-fresh v fr) (IdDyn _ ())
value-¬step (V-fresh v fr) (IdDyn-var _ eq _ _ _) with trans (sym fr) eq
value-¬step (V-fresh v fr) (IdDyn-var _ eq _ _ _) | ()
value-¬step (V-fresh v fr) (ξ-⟪⟫ rel st) =
  value-¬step (V-simple (S-cast v I-tag)) st
