module strong.proof.PreserveObstruct where

-- THE FOUR PRESERVATION OBSTRUCTIONS, as refutations.
--
-- Each section exhibits a TYPED redex, the step the rule takes on it, and
-- a proof that the CONTRACTUM IS NOT TYPEABLE AT THE REDEX'S TYPE.  Each
-- therefore refutes the corresponding case statement of proof/Preserve
-- (`¬PeelCase`, `¬TyPeelRCase`, `¬CancelRCase`, `¬IdPushCase`), which is
-- why those four are module parameters there and not lemmas.
--
-- The four root causes are distinct:
--
--   §1 CancelR  DROPS Θ₁'S FRAME.  The residue rebinds only Θ₂'s owners,
--               so a value that names one of Θ₁'s `nbind` slots loses it.
--   §2 TyPeelR  REUSES THE EXTERIOR ANNOTATION.  The pushed-in `·[ B , _ ]`
--               must be annotated with the INTERIOR face's ∀-body, which
--               differs from `B` at every non-identity ∀-face.  (The rule's
--               `renᴮ suc Θ` is a second, independent defect: `prep`
--               already lifts past the new owner, so the shift double-counts
--               — visible in `intC (bind A ∷ renᴮ suc Θ) Δ` below.)
--   §3 Peel     THE DUAL RE-BLOCKS A NO-OP `unlock`.  `dualS` maps
--               `unlock X ↦ lock (n+X)` unconditionally, so a Θ whose
--               `unlock` names an ALREADY-NAMEABLE slot (which `Bwf`'s
--               `bw-u` explicitly permits) makes the dual BLOCK a slot the
--               crossing argument's own derivation needs.
--   §4 IdPush   PUSHES A REP ACROSS A LOCK.  The inner wrapper's new
--               exterior type is the owner's rep `A`, which `env`'s last
--               premise then demands be well formed on the INTERIOR type
--               context — where Θ₂'s `lock` may have blocked the slot the
--               rep names (the chained-rep configuration of §5's c10/c11).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.Preserve
  using (PeelCase; TyPeelRCase; CancelRCase; IdPushCase)

------------------------------------------------------------------------
-- §1  CancelR drops Θ₁'s frame
------------------------------------------------------------------------

-- Θ₁ binds ONE owner, so the cancelled value V lives two binders deep;
-- the residue `reps→bind (reps Θ₂)` rebinds only Θ₂'s one owner, and V's
-- `lock 1` — perfectly well formed inside — names a slot that no longer
-- exists.

Θc₁ Θc₂ : CtxMorph
Θc₁ = bind `𝔹 ∷ []
Θc₂ = bind (`ℕ ⇒ `ℕ) ∷ []

Vc : Term
Vc = ƛ `ℕ ∙ (($ 5) ⟪ lock 1 ∷ [] , id `ℕ ⟫)

-- V's home: Θ₁'s owner over Θ₂'s owner over the empty type context.
Ξc : Ctxᵗ
Ξc = bind `𝔹 ∷ bind (`ℕ ⇒ `ℕ) ∷ []

_ : intC Θc₁ (intC Θc₂ []) ≡ Ξc
_ = refl

⊢Vc : Ξc ∣ [] ⊢ Vc ⦂ (`ℕ ⇒ `ℕ)
⊢Vc = ⊢ƛ wf-ℕ
        (env {p = ↑ˢ} (bw-l (bind (`ℕ ⇒ `ℕ) , es ez , vis-b) bw[])
             ⊢$ (conv-id base-ℕ) wf-ℕ)

val-Vc : Value Vc
val-Vc = V-ƛ

Rc : Term
Rc = (Vc ⟪ Θc₁ , seal 1 ⟫) ⟪ Θc₂ , unseal 0 ⟫

⊢Rc : [] ∣ [] ⊢ Rc ⦂ (`ℕ ⇒ `ℕ)
⊢Rc = env {p = ↑ˢ} (bw-b (wf-⇒ wf-ℕ wf-ℕ) bw[])
          (env {p = ↓ˢ} (bw-b wf-𝔹 bw[]) ⊢Vc
               (conv-seal (es ez))
               (wf-var (bind (`ℕ ⇒ `ℕ) , ez , vis-b)))
          (conv-unseal ez) (wf-⇒ wf-ℕ wf-ℕ)

step-c : [] ⊢ Rc -→ Vc ⟪ reps→bind (reps Θc₂) , idc (`ℕ ⇒ `ℕ) ⟫
step-c = CancelR val-Vc ez

-- the contractum, with the residue and the identity face computed out
_ : Vc ⟪ reps→bind (reps Θc₂) , idc (`ℕ ⇒ `ℕ) ⟫
      ≡ Vc ⟪ bind (`ℕ ⇒ `ℕ) ∷ [] , id `ℕ ↦ id `ℕ ⟫
_ = refl

¬⊢c-contractum :
  ¬ ([] ∣ [] ⊢ Vc ⟪ bind (`ℕ ⇒ `ℕ) ∷ [] , id `ℕ ↦ id `ℕ ⟫ ⦂ (`ℕ ⇒ `ℕ))
¬⊢c-contractum (env _ (⊢ƛ _ (env (bw-l (_ , es () , _) _) _ _ _)) _ _)

¬CancelRCase : ¬ CancelRCase
¬CancelRCase cc = ¬⊢c-contractum (cc val-Vc ez ⊢Rc)

------------------------------------------------------------------------
-- §2  TyPeelR reuses the exterior annotation
------------------------------------------------------------------------

-- The boundary's ∀-face is a REVEAL, so its interior body (` 1) and its
-- exterior body (`ℕ) differ.  The contractum annotates the pushed-in
-- instantiation with the EXTERIOR one, and the interior application then
-- has the wrong type.

Δt : Ctxᵗ
Δt = bind `ℕ ∷ []

Vt : Term
Vt = Λ (($ 7) ⟪ [] , seal 1 ⟫)

⊢Vt : Δt ∣ [] ⊢ Vt ⦂ `∀ (` 1)
⊢Vt = ⊢Λ (env {p = ↓ˢ} bw[] ⊢$ (conv-seal (es ez))
              (wf-var (bind `ℕ , es ez , vis-b)))

val-Vt : Value Vt
val-Vt = V-Λ (V-⟪⟫ V-$ I-seal)

Bt : Term
Bt = Vt ⟪ [] , `∀ (unseal 1) ⟫

⊢Bt : Δt ∣ [] ⊢ Bt ⦂ `∀ `ℕ
⊢Bt = env {p = ↑ˢ} bw[] ⊢Vt
          (conv-all (conv-unseal (es ez))) (wf-∀ wf-ℕ)

Rt : Term
Rt = Bt ·[ `ℕ , `ℕ ]

⊢Rt : Δt ∣ [] ⊢ Rt ⦂ `ℕ
⊢Rt = ⊢·[] ⊢Bt wf-ℕ

step-t : Δt ⊢ Rt
       -→ (wkᴹ 1 Vt ·[ renameᵗ (extᵗ suc) `ℕ , ` 0 ])
            ⟪ bind `ℕ ∷ renᴮ suc [] , unseal 1 ⟫
step-t = TyPeelR val-Vt

_ : (wkᴹ 1 Vt ·[ renameᵗ (extᵗ suc) `ℕ , ` 0 ])
      ⟪ bind `ℕ ∷ renᴮ suc [] , unseal 1 ⟫
  ≡ (wkᴹ 1 Vt ·[ `ℕ , ` 0 ]) ⟪ bind `ℕ ∷ [] , unseal 1 ⟫
_ = refl

-- The face forces the interior to have type ` 1; the annotation gives it
-- type `ℕ [ ` 0 ]ᵗ = `ℕ.
¬⊢t-interior :
  ¬ ((bind `ℕ ∷ Δt) ∣ [] ⊢ wkᴹ 1 Vt ·[ `ℕ , ` 0 ] ⦂ ` 1)
¬⊢t-interior ()

¬⊢t-contractum :
  ¬ (Δt ∣ [] ⊢ (wkᴹ 1 Vt ·[ `ℕ , ` 0 ]) ⟪ bind `ℕ ∷ [] , unseal 1 ⟫ ⦂ `ℕ)
¬⊢t-contractum (env _ ⊢i (conv-unseal _) _) = ¬⊢t-interior ⊢i

¬TyPeelRCase : ¬ TyPeelRCase
¬TyPeelRCase tc = ¬⊢t-contractum (tc val-Vt ⊢Rt)

------------------------------------------------------------------------
-- §3  Peel — REPAIRED (refutation removed)
------------------------------------------------------------------------

-- The old §3 refuted the OLD `dual` (`unlock X ↦ lock (n+X)`), which
-- re-blocked a no-op `unlock` (`Θ = unlock 0` at an unmasked slot) and
-- failed same-slot cancellation.  strong.Reduction's repaired `dualS`
-- DROPS the `unlock` case, so `dual (unlock 0 ∷ []) ≡ []` and the
-- crossing no longer masks the owner.  `PeelCase` is now PROVEN
-- (strong.proof.PeelDual.preserve-Peel), with `intC-dual`/`fceC-dual`
-- true in general — so this refutation is gone.

------------------------------------------------------------------------
-- §4  IdPush pushes a rep across a lock
------------------------------------------------------------------------

-- The CHAINED configuration: slot 0's rep NAMES slot 1, and the outer
-- boundary locks slot 1.  IdPush swaps the faces, so the inner wrapper's
-- exterior type becomes that rep — and `env`'s last premise demands it be
-- well formed INSIDE, where slot 1 is blocked.

Δi : Ctxᵗ
Δi = bind (` 0) ∷ bind `ℕ ∷ []

Θi : CtxMorph
Θi = lock 1 ∷ []

Ξi : Ctxᵗ
Ξi = bind (` 0) ∷ blk (bind `ℕ) ∷ []

_ : intC Θi Δi ≡ Ξi
_ = refl

_ : fceC Θi Δi ≡ Δi
_ = refl

-- slot 0's rep, read on the face type context, is slot 1
_ : Δi ∋ 0 := ` 1
_ = ez

Vi : Term
Vi = (($ 7) ⟪ [] , seal 1 ⟫) ⟪ unlock 1 ∷ [] , seal 0 ⟫

⊢Vi : Ξi ∣ [] ⊢ Vi ⦂ ` 0
⊢Vi = env {p = ↓ˢ} (bw-u (es ez) bw[])
          (env {p = ↓ˢ} bw[] ⊢$ (conv-seal (es ez))
               (wf-var (bind `ℕ , es ez , vis-b)))
          (conv-seal ez)
          (wf-var (_ , ez , vis-b))

val-Vi : Value Vi
val-Vi = V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal

Ri : Term
Ri = (Vi ⟪ [] , id (` 0) ⟫) ⟪ Θi , unseal 0 ⟫

⊢Ri : Δi ∣ [] ⊢ Ri ⦂ ` 1
⊢Ri = env {p = ↑ˢ} (bw-l (bind `ℕ , es ez , vis-b) bw[])
          (env {p = ↑ˢ} bw[] ⊢Vi
               (conv-idv (_ , ez , vis-b))
               (wf-var (_ , ez , vis-b)))
          (conv-unseal ez)
          (wf-var (bind `ℕ , es ez , vis-b))

step-i : Δi ⊢ Ri -→ (Vi ⟪ [] , unseal 0 ⟫) ⟪ Θi , idc (` 1) ⟫
step-i = IdPush val-Vi ez

_ : idc (` 1) ≡ id (` 1)
_ = refl

-- inside, the rep ` 1 is not even a well-formed type
¬wf-i : ¬ (Ξi ⊢ᵗ ` 1)
¬wf-i (wf-var (_ , es ez , ()))

¬⊢i-contractum :
  ¬ (Δi ∣ [] ⊢ (Vi ⟪ [] , unseal 0 ⟫) ⟪ Θi , id (` 1) ⟫ ⦂ ` 1)
¬⊢i-contractum (env _ (env _ _ (conv-unseal ez) w) (conv-idv _) _) = ¬wf-i w

¬IdPushCase : ¬ IdPushCase
¬IdPushCase ic = ¬⊢i-contractum (ic val-Vi ez ⊢Ri)

------------------------------------------------------------------------
-- §5  THE HEADLINE, and the verdict on `intC-dual`
------------------------------------------------------------------------

-- Preservation, as targeted, is still FALSE while IdPush stands (§4 is the
-- surviving witness; Peel is now repaired and proven).
¬preservation :
  ¬ (∀ {Δ M M′ A} → Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A)
¬preservation pr = ¬⊢i-contractum (pr ⊢Ri step-i)
