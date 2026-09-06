module strong.proof.DualTightness where

-- TIGHTNESS OF THE DUAL — Jeremy's test (2026-09-06), MACHINE-CHECKED.
--
-- THE DEFECT.  `dualScope` (strong.Reduction §2) DROPS the crossed
-- boundary's `unlock` entries.  So a boundary whose morphism UNMASKS an
-- exterior slot hands its crossing argument a frame in which that slot is
-- STILL unmasked: `interior (dual Θ) (interior Θ Δ)` is
-- `map masked (bind prefix) ++ unlockedScope Θ Δ` (proof/PeelDual,
-- `interior-dual`), and `unlockedScope Θ Δ` is STRICTLY MORE NAMEABLE than
-- Δ whenever Θ unlocks a slot Δ masks.  SCOPE IS GAINED THROUGH THE
-- BOUNDARY.
--
-- The witness below exhibits the gain as a rule-level fact: a redex that
-- is ILL TYPED at Δ (its argument W names a slot MASKED at Δ) whose `Peel`
-- contractum is WELL TYPED.  `Peel` therefore does not preserve the
-- exterior's scope discipline; the crossing is not tight.
--
-- Nothing here contradicts preservation — `Peel`'s preservation case is
-- proven (proof/PeelDual.preserve-Peel) and only ever runs on a
-- WELL-TYPED redex, which this one is not.  What fails is TIGHTNESS: the
-- REDUCTION RELATION relates a term the exterior refuses to a term it
-- accepts.
--
-- The repair Jeremy proposes — `dualScope n (unlock X ∷ Θ) =
-- lock (n + X) ∷ dualScope n Θ`, together with an `mw-u` that requires the
-- slot to be MASKED — is REFUTED in proof/MwUObstruct.agda: it is
-- incompatible with the scope move (`_⋉_`) and with `⊢retag`.

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
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

-- The boundary's morphism UNMASKS U for its interior (the
-- crossing-of-crossing shape: an inner region re-exposes what an outer
-- one concealed).
Θᵤ : CtxMorph
Θᵤ = unlock 0 ∷ []

_ : interior Θᵤ Δᵤ ≡ bind `ℕ ∷ []
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
⊢Vb = env (mw-u ez mw[])
          (⊢ƛ (wf-⇒ (wf-var (bind `ℕ , ez , nameable-b)) wf-ℕ) (⊢` here))
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
-- §3  The step, and the WELL-TYPED contractum
------------------------------------------------------------------------

-- THE DUAL DROPS THE UNLOCK.
_ : dual Θᵤ ≡ []
_ = refl

--   scripts/render_term.sh 'showTmIn 1 Contractum'  =
--     (((λx:(X⇒ℕ). x) · ((λx:ℕ. (ΛY. 3) [X]) ⟪ (unseal X ↦ id ℕ) ⟫))
--        ⟪ ↥X , (seal X ↦ id ℕ) ⟫)
-- — note the crossing argument's frame is EMPTY (`dual Θᵤ ≡ []`).
Contractum : Term
Contractum = (V · (W ⟪ dual Θᵤ , unseal 0 ↦ id `ℕ ⟫)) ⟪ Θᵤ , seal 0 ↦ id `ℕ ⟫

step-u : Δᵤ ⊢ Redex -→ Contractum
step-u = Peel V-ƛ V-ƛ

-- W's frame INSIDE the crossing is `bind ℕ ∷ []` — U is nameable there,
-- because the dual restored nothing.
_ : interior (dual Θᵤ) (interior Θᵤ Δᵤ) ≡ bind `ℕ ∷ []
_ = refl

-- … and so the contractum TYPES.  SCOPE WAS GAINED.
⊢Contractum : Δᵤ ∣ [] ⊢ Contractum ⦂ (`ℕ ⇒ `ℕ)
⊢Contractum =
  env (mw-u ez mw[])
      (⊢· (⊢ƛ (wf-⇒ (wf-var (bind `ℕ , ez , nameable-b)) wf-ℕ) (⊢` here))
          (env mw[]
               (⊢ƛ wf-ℕ (⊢·[] (⊢Λ ⊢$) (wf-var (bind `ℕ , ez , nameable-b))))
               (conv-fun (conv-unseal ez) (conv-id base-ℕ))
               (wf-⇒ (wf-var (bind `ℕ , ez , nameable-b)) wf-ℕ)))
      (conv-fun (conv-seal ez) (conv-id base-ℕ))
      (wf-⇒ wf-ℕ wf-ℕ)

------------------------------------------------------------------------
-- §4  THE POSITIVE CONTROL
------------------------------------------------------------------------

-- The same shape with a Θ-LOCKED slot behaves correctly: `dual` DOES mint
-- an `unlock` for a `lock`, so a crossing argument that names a slot the
-- boundary locked keeps its frame.  Δ has ONE nameable binder Z; Θˡ locks
-- it; the dual unlocks it again, and the argument's frame inside is Δ with
-- the bind prefix masked — Z still nameable.
Δˡ : Ctxᵗ
Δˡ = bind `ℕ ∷ []

Θˡ : CtxMorph
Θˡ = lock 0 ∷ []

_ : interior Θˡ Δˡ ≡ masked (bind `ℕ) ∷ []
_ = refl

_ : dual Θˡ ≡ unlock 0 ∷ []
_ = refl

-- the crossing frame is Δˡ back: Z is nameable, exactly as at the exterior
_ : interior (dual Θˡ) (interior Θˡ Δˡ) ≡ bind `ℕ ∷ []
_ = refl
