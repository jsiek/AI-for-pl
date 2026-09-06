module strong.proof.PreserveObstruct where

-- THE PRESERVATION OBSTRUCTIONS, as refutations — and what is LEFT of
-- them after the 2026-09-05/06 rule repairs.
--
-- Each section exhibits a TYPED redex, the step the rule takes on it, and
-- a proof that the CONTRACTUM IS NOT TYPEABLE AT THE REDEX'S TYPE.
--
--   §1 CancelR  REPAIRED.  The old contractum dropped Θ₁'s frame, so a
--               value naming one of Θ₁'s own slots lost it.  The repaired
--               rule keeps BOTH frames, and §1's witness now TYPES
--               (`⊢c-contractum`) — the refutation is gone.
--   §2 TyPeelR  REPAIRED, and what remains is THE POLARITY DISCIPLINE,
--               not the rule.  The pushed-in annotation is now the
--               premise-determined interior ∀-body and the frame is plain
--               `Θ`; the minted face `unsealAtᶜ 0 s` types at an `↑ˢ`
--               (reveal) ∀-face (proof/Preserve.preserve-TyPeelR-↑) and is
--               MIXED-POLARITY at a `↓ˢ` (conceal) one — `¬TyPeelRCase`
--               below, reached from closed plain source in Examples §13a.
--   §3 Peel     REPAIRED and PROVEN (proof/PeelDual); refutation removed.
--   §4 IdPush   PUSHES A REP ACROSS A LOCK.  The inner wrapper's new
--               exterior type is the owner's rep `A`, which `env`'s last
--               premise then demands be well formed on the INTERIOR type
--               context — where Θ₂'s `lock` may have blocked the slot the
--               rep names (the chained-rep configuration of §5's c10/c11).
--               proof/WallReach answers it over the `RepWf` invariant.

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

step-c : [] ⊢ Rc
       -→ (Vc ⟪ Θc₁ , idc (liftN (nbind Θc₁) (`ℕ ⇒ `ℕ)) ⟫)
            ⟪ Θc₂ , idc (`ℕ ⇒ `ℕ) ⟫
step-c = CancelR val-Vc ez

-- the contractum, with both identity faces computed out
_ : (Vc ⟪ Θc₁ , idc (liftN (nbind Θc₁) (`ℕ ⇒ `ℕ)) ⟫) ⟪ Θc₂ , idc (`ℕ ⇒ `ℕ) ⟫
      ≡ (Vc ⟪ bind `𝔹 ∷ [] , id `ℕ ↦ id `ℕ ⟫)
          ⟪ bind (`ℕ ⇒ `ℕ) ∷ [] , id `ℕ ↦ id `ℕ ⟫
_ = refl

-- AND IT TYPES.  The old contractum `V ⟪ reps→bind (reps Θ₂) , idc A ⟫`
-- dropped Θ₁'s frame, so `Vc`'s `lock 1` named a slot that no longer
-- existed; the repaired one KEEPS BOTH FRAMES, and `Vc` retypes exactly
-- where it was — `⊢Vc` is reused verbatim.
⊢c-contractum :
  [] ∣ [] ⊢ (Vc ⟪ bind `𝔹 ∷ [] , id `ℕ ↦ id `ℕ ⟫)
              ⟪ bind (`ℕ ⇒ `ℕ) ∷ [] , id `ℕ ↦ id `ℕ ⟫ ⦂ (`ℕ ⇒ `ℕ)
⊢c-contractum =
  env {p = ↑ˢ} (bw-b (wf-⇒ wf-ℕ wf-ℕ) bw[])
      (env {p = ↑ˢ} (bw-b wf-𝔹 bw[]) ⊢Vc
           (conv-fun (conv-id base-ℕ) (conv-id base-ℕ))
           (wf-⇒ wf-ℕ wf-ℕ))
      (conv-fun (conv-id base-ℕ) (conv-id base-ℕ))
      (wf-⇒ wf-ℕ wf-ℕ)

------------------------------------------------------------------------
-- §2  TyPeelR under a `↓ˢ` ∀-face — THE POLARITY OBSTRUCTION
------------------------------------------------------------------------

-- The two old defects (exterior annotation, double shift) are REPAIRED
-- in strong.Reduction: the pushed-in annotation is the premise-determined
-- interior body, the frame is plain `Θ`, and the face is `unsealAtᶜ 0 s`
-- — the leaf-wise mint that turns the face's now-OWNED slot 0 into its
-- instantiation.  At an `↑ˢ` (reveal) ∀-face that is a THEOREM
-- (proof/Preserve.preserve-TyPeelR-↑).
--
-- WHAT REMAINS IS NOT A RULE DEFECT BUT THE POLARITY DISCIPLINE.  Under a
-- `↓ˢ` (conceal) ∀-face — a POLYMORPHIC ARGUMENT that crossed a Peel —
-- the mint inserts `seal 0` at CONTRAVARIANT positions and `unseal 0` at
-- COVARIANT ones, i.e. at `↑ˢ` and `↓ˢ` respectively; but `conv-unseal`
-- is fixed at `↑ˢ` and `conv-seal` at `↓ˢ`, so under a `↓ˢ` face EVERY
-- inserted leaf sits at the polarity the judgment refuses, while the
-- face's own pre-existing `seal` leaves sit at the other one.  The
-- resulting face is MIXED-POLARITY and has NO typing at either p.
--
-- The witness below is exactly the shape Examples §13 reaches from closed
-- plain source: `f : ∀Y. Y ⇒ X` crossing a Peel and then instantiated.

-- the crossed boundary's interior — the owner X := ℕ
Δt : Ctxᵗ
Δt = bind `ℕ ∷ []

-- the polymorphic ARGUMENT, closed and plain: ΛY. λy:Y. 3
Wt : Term
Wt = Λ (ƛ (` 0) ∙ ($ 3))

val-Wt : Value Wt
val-Wt = V-Λ V-ƛ

⊢Wt : ∀ {Δ Γ} → Δ ∣ Γ ⊢ Wt ⦂ `∀ (` 0 ⇒ `ℕ)
⊢Wt = ⊢Λ (⊢ƛ (wf-var (abst , ez , vis-a)) ⊢$)

-- the `↓ˢ` ∀-face a Peel hands it: `sealAt 0 (∀Y. Y ⇒ X)`
Θt : CtxMorph
Θt = lock 0 ∷ []

st : Conv
st = id (` 0) ↦ seal 1

_ : sealAt 0 (`∀ (` 0 ⇒ ` 1)) ≡ `∀ st
_ = refl

-- the premise TyPeelR carries, at THIS redex: p = ↓ˢ, and no other p
-- types it (the pre-existing `seal 1` leaf is covariant).
⊢st : (abst ∷ fceC Θt Δt) ⊢ st ∶ (` 0 ⇒ `ℕ) ⇝ (` 0 ⇒ ` 1) ∙ ↓ˢ
⊢st = conv-fun (conv-idv (abst , ez , vis-a)) (conv-seal (es ez))

Wft : Term
Wft = Wt ⟪ Θt , `∀ st ⟫

⊢Wft : Δt ∣ [] ⊢ Wft ⦂ `∀ (` 0 ⇒ ` 1)
⊢Wft = env {p = ↓ˢ} (bw-l (bind `ℕ , ez , vis-b) bw[]) ⊢Wt
           (conv-all ⊢st)
           (wf-∀ (wf-⇒ (wf-var (abst , ez , vis-a))
                       (wf-var (bind `ℕ , es ez , vis-b))))

Rt : Term
Rt = Wft ·[ ` 0 ⇒ ` 1 , ` 0 ]

⊢Rt : Δt ∣ [] ⊢ Rt ⦂ (` 0 ⇒ ` 0)
⊢Rt = ⊢·[] ⊢Wft (wf-var (bind `ℕ , ez , vis-b))

step-t : Δt ⊢ Rt
       -→ (wkᴹ 1 Wt ·[ renameᵗ (extᵗ suc) (` 0 ⇒ `ℕ) , ` 0 ])
            ⟪ bind (` 0) ∷ Θt , unsealAtᶜ 0 st ⟫
step-t = TyPeelR val-Wt ⊢st

-- THE MINTED FACE, computed: the inserted leaf is the DOMAIN `seal 0`.
_ : unsealAtᶜ 0 st ≡ seal 0 ↦ seal 1
_ = refl

-- THE FAILING LEAF, precisely.  `seal 0` sits contravariantly, so it
-- needs `flip p ≡ ↓ˢ` (p = ↑ˢ); `seal 1` sits covariantly, so it needs
-- `p ≡ ↓ˢ`.  Nothing else about the types matters — the refutation does
-- not even look at them.
¬seal↦seal : ∀ {Δ A B p} → ¬ (Δ ⊢ seal 0 ↦ seal 1 ∶ A ⇝ B ∙ p)
¬seal↦seal {p = ↑ˢ} (conv-fun ⊢s ())
¬seal↦seal {p = ↓ˢ} (conv-fun () ⊢t)

¬⊢t-contractum : ∀ {C}
  → ¬ (Δt ∣ [] ⊢ (wkᴹ 1 Wt ·[ ` 0 ⇒ `ℕ , ` 0 ])
                   ⟪ bind (` 0) ∷ Θt , seal 0 ↦ seal 1 ⟫ ⦂ C)
¬⊢t-contractum (env _ _ ⊢c _) = ¬seal↦seal ⊢c

¬TyPeelRCase : ¬ TyPeelRCase
¬TyPeelRCase tc = ¬⊢t-contractum (tc val-Wt ⊢st ⊢Rt)

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
