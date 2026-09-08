module strong.proof.DualTightness where

-- TIGHTNESS OF THE DUAL — Jeremy's test (2026-09-06), MACHINE-CHECKED,
-- AND THE LEAK CLOSED.
--
-- THE DEFECT THAT WAS.  `dualScope` DROPPED the crossed boundary's
-- `unlock` entries, so a boundary whose morphism UNMASKS an exterior slot
-- handed its crossing argument a frame in which that slot was STILL
-- unmasked: `interior (dual Θ) (interior Θ Δ)` was
-- `map masked (bind prefix) ++ unlockedScope Θ Δ`, STRICTLY MORE
-- NAMEABLE than Δ whenever Θ unlocked a slot Δ masked.  SCOPE WAS GAINED
-- THROUGH THE BOUNDARY: the redex below is ILL TYPED at Δᵤ (its argument
-- W names a slot MASKED at Δᵤ) and its `Peel` contractum was WELL TYPED.
--
-- THE REPAIR, in two coupled halves (strong.CtxMorph §3, `_⊢ᵐ_` in §2):
--
--   (1) `sw-u` demands `applyChanges S Δ ∋lk X` — the slot must be LOCKED.  A
--       VACUOUS unlock is REFUSED (§5 below); it is the premise the
--       judgement used to drop.
--   (2) `dualScope n (unlock X ∷ S) = dualScope n S ++ lock (n + X) ∷ []`
--       — the dual RESTORES what Θ unlocked, and the list is REVERSED,
--       because `scope` applies it HEAD-LAST.
--
-- With both, `interior (dual Θ) (interior Θ Δ) ≡ map masked (bind prefix)
-- ++ Δ` EXACTLY (proof/PeelDual, `interior-dual`), the crossing is
-- `⊢rename` alone, and the contractum below is REFUSED — §3.

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.Reduction

------------------------------------------------------------------------
-- §1  The exterior: one MASKED binder
------------------------------------------------------------------------

-- Δᵤ = ↓U (one slot U, a binder at ℕ, CONCEALED: we sit inside a region
-- that masks it).
Δᵤ : Ctxᵗ
Δᵤ = masked (bind `ℕ) ∷ []

-- U is not nameable at the exterior — that is the whole of tightness.
¬∋tv-Δᵤ : ¬ (Δᵤ ∋tv 0)
¬∋tv-Δᵤ (_ , ez , ())

-- … but it IS locked, so an `unlock` may cite it.
∋lk-Δᵤ : Δᵤ ∋lk 0
∋lk-Δᵤ = masked (bind `ℕ) , ez , locked

-- The boundary's morphism UNMASKS U for its interior (the
-- crossing-of-crossing shape: an inner region re-exposes what an outer
-- one concealed).
Θᵤ : CtxMorph
Θᵤ = morph [] (unlock 0 ∷ [])

_ : interior Θᵤ Δᵤ ≡ unmasked (bind `ℕ) ∷ []
_ = refl

------------------------------------------------------------------------
-- §2  The redex
------------------------------------------------------------------------

-- V = λx:(U ⇒ ℕ). x
--   scripts/render_term.sh 'showTmIn 1 V'  =  (λx:(X⇒ℕ). x)
V : Term
V = ƛ (` 0 ⇒ `ℕ) ∙ (` 0)

-- the conversion: (U⇒ℕ)⇒(U⇒ℕ) inside  ⇝  (ℕ⇒ℕ)⇒(ℕ⇒ℕ) outside
cᵤ : Conv
cᵤ = (unseal 0 ↦ id `ℕ) ↦ (seal 0 ↦ id `ℕ)

-- W = λy:ℕ. (ΛZ. 3)[U] : ℕ ⇒ ℕ — a VALUE, and ILL TYPED at the exterior,
-- because its type argument NAMES U, which Δᵤ masks.
--   scripts/render_term.sh 'showTmIn 1 W'  =  (λx:ℕ. (ΛY. 3) [X])
W : Term
W = ƛ `ℕ ∙ ((Λ ($ 3)) ·[ `ℕ , ` 0 ])

¬⊢W-ext : ∀ {Γ A} → ¬ (Δᵤ ∣ Γ ⊢ W ⦂ A)
¬⊢W-ext (⊢ƛ _ (⊢·[] _ (wf-var (_ , ez , ()))))

-- The boundary ALONE is well typed at Δᵤ …
⊢Vb : Δᵤ ∣ [] ⊢ V ⟪ Θᵤ , cᵤ ⟫ ⦂ ((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))
⊢Vb = env (mw rw[] (sw-u ∋lk-Δᵤ sw[]))
          (⊢ƛ (wf-⇒ (wf-var (unmasked (bind `ℕ) , ez , nameable)) wf-ℕ) (⊢` here))
          (conv-fun (conv-fun (conv-unseal ez) (conv-id base-ℕ))
                    (conv-fun (conv-seal ez) (conv-id base-ℕ)))
          (wf-⇒ (wf-⇒ wf-ℕ wf-ℕ) (wf-⇒ wf-ℕ wf-ℕ))

-- … so the redex is ill typed ONLY because of W.
--   scripts/render_term.sh 'showTmIn 1 Redex'  =
--     (((λx:(X⇒ℕ). x) ⟪ ↥X , ((unseal X ↦ id ℕ) ↦ (seal X ↦ id ℕ)) ⟫)
--        · (λx:ℕ. (ΛY. 3) [X]))
Redex : Term
Redex = (V ⟪ Θᵤ , cᵤ ⟫) · W

¬⊢Redex : ∀ {A} → ¬ (Δᵤ ∣ [] ⊢ Redex ⦂ A)
¬⊢Redex (⊢· _ ⊢W) = ¬⊢W-ext ⊢W

------------------------------------------------------------------------
-- §3  The step, and the contractum — NOW REFUSED
------------------------------------------------------------------------

-- THE DUAL RESTORES THE LOCK.
_ : dual Θᵤ ≡ morph [] (lock 0 ∷ [])
_ = refl

--   scripts/render_term.sh 'showTmIn 1 Contractum'  =
--     (((λx:(X⇒ℕ). x) · ((λx:ℕ. (ΛY. 3) [X]) ⟪ ↧X , (unseal X ↦ id ℕ) ⟫))
--        ⟪ ↥X , (seal X ↦ id ℕ) ⟫)
Contractum : Term
Contractum = (V · (W ⟪ dual Θᵤ , unseal 0 ↦ id `ℕ ⟫)) ⟪ Θᵤ , seal 0 ↦ id `ℕ ⟫

step-u : Δᵤ ⊢ Redex -→ Contractum
step-u = Peel V-ƛ V-ƛ

-- (†) AT THIS Θ: W's frame INSIDE the crossing IS THE EXTERIOR — U is
-- masked there, exactly as it is outside.  Nothing is gained.
_ : interior (dual Θᵤ) (interior Θᵤ Δᵤ) ≡ Δᵤ
_ = refl

-- … and so the contractum DOES NOT TYPE.  The reduction relation no
-- longer relates a term the exterior refuses to one it accepts.
¬⊢Contractum : ∀ {A} → ¬ (Δᵤ ∣ [] ⊢ Contractum ⦂ A)
¬⊢Contractum (env _ (⊢· _ (env _ ⊢W _ _)) _ _) = ¬⊢W-ext ⊢W

------------------------------------------------------------------------
-- §4  THE POSITIVE CONTROL
------------------------------------------------------------------------

-- The same shape with a Θ-LOCKED slot still behaves correctly: `dual`
-- mints an `unlock` for a `lock`, so a crossing argument that names a
-- slot the boundary locked keeps its frame.  Δ has ONE nameable binder Z;
-- Θˡ locks it; the dual unlocks it again, and the argument's frame inside
-- is Δ with the bind prefix masked — Z still nameable.
Δˡ : Ctxᵗ
Δˡ = unmasked (bind `ℕ) ∷ []

Θˡ : CtxMorph
Θˡ = morph [] (lock 0 ∷ [])

_ : interior Θˡ Δˡ ≡ masked (bind `ℕ) ∷ []
_ = refl

_ : dual Θˡ ≡ morph [] (unlock 0 ∷ [])
_ = refl

-- the crossing frame is Δˡ back: Z is nameable, exactly as at the exterior
_ : interior (dual Θˡ) (interior Θˡ Δˡ) ≡ unmasked (bind `ℕ) ∷ []
_ = refl

------------------------------------------------------------------------
-- §5  THE VACUOUS UNLOCK, REFUSED
------------------------------------------------------------------------

-- The restoring `lock` of §3 is sound ONLY because the slot really was
-- masked: `mask ∘ unmask` is the identity at a LOCKED slot and nowhere
-- else (`mask-unmask`, strong.Ctx §6b).  At a slot the exterior leaves
-- NAMEABLE, an `unlock` does nothing and its restored `lock` would mask
-- what the exterior left visible — so the judgement must refuse it, and
-- does.
Δᵥ : Ctxᵗ
Δᵥ = unmasked (bind `ℕ) ∷ []

Θᵥ : CtxMorph
Θᵥ = morph [] (unlock 0 ∷ [])

_ : interior Θᵥ Δᵥ ≡ Δᵥ            -- the unlock does nothing …
_ = refl

¬⊢ᵐΘᵥ : ¬ (Δᵥ ⊢ᵐ Θᵥ)              -- … and is REFUSED
¬⊢ᵐΘᵥ (mw _ (sw-u (_ , ez , ()) _))

-- A DOUBLE LOCK IS REFUSED TOO — which is what keeps `Locked` one mask
-- deep, and hence `unmaskEnt` an exact inverse of `masked`.
¬⊢ᵐ-double-lock : ¬ (Δᵥ ⊢ᵐ morph [] (lock 0 ∷ lock 0 ∷ []))
¬⊢ᵐ-double-lock (mw _ (sw-l (_ , ez , ()) _))
