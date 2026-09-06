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
--   §2 TyPeelR  REPAIRED and PROVEN.  The pushed-in annotation is now the
--               premise-determined interior ∀-body, the frame is plain
--               `Θ`, and the minted face `unsealAtᶜ 0 s` types at EVERY
--               ∀-face once the polarity index is gone
--               (proof/Preserve.preserve-TyPeelR).  §2 keeps the old
--               counterexample's witness and records the POSITIVE fact on
--               it; Examples §13 reaches it from closed plain source.
--   §3 Peel     REPAIRED and PROVEN (proof/PeelDual); refutation removed.
--   §4 IdPush   REPAIRED by the SCOPE MOVE (Jeremy, 2026-09-06).  The
--               inner wrapper's new exterior type is the owner's rep `A`,
--               which `env`'s last premise demands be well formed where
--               the contractum puts it.  The old contractum put it INSIDE
--               Θ₂'s `lock` — §4's witness, and the refutation that stood
--               here.  The repaired rule MOVES Θ₂'s scope into the inner
--               frame, so the rep is presented on Θ₂'s FACE type context,
--               where it is nameable; §4 now records the POSITIVE fact on
--               the very same witness (`⊢i-contractum`).

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
open import strong.proof.Preserve using (preserve-TyPeelR)
open import strong.proof.MoveScope using (preserve-IdPush)

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
        (env (bw-l (bind (`ℕ ⇒ `ℕ) , es ez , vis-b) bw[])
             ⊢$ (conv-id base-ℕ) wf-ℕ)

val-Vc : Value Vc
val-Vc = V-ƛ

Rc : Term
Rc = (Vc ⟪ Θc₁ , seal 1 ⟫) ⟪ Θc₂ , unseal 0 ⟫

⊢Rc : [] ∣ [] ⊢ Rc ⦂ (`ℕ ⇒ `ℕ)
⊢Rc = env (bw-b (wf-⇒ wf-ℕ wf-ℕ) bw[])
          (env (bw-b wf-𝔹 bw[]) ⊢Vc
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
  env (bw-b (wf-⇒ wf-ℕ wf-ℕ) bw[])
      (env (bw-b wf-𝔹 bw[]) ⊢Vc
           (conv-fun (conv-id base-ℕ) (conv-id base-ℕ))
           (wf-⇒ wf-ℕ wf-ℕ))
      (conv-fun (conv-id base-ℕ) (conv-id base-ℕ))
      (wf-⇒ wf-ℕ wf-ℕ)

------------------------------------------------------------------------
-- §2  TyPeelR under a CONCEAL ∀-face — SETTLED, AND POSITIVELY
------------------------------------------------------------------------

-- The two old defects (exterior annotation, double shift) are REPAIRED in
-- strong.Reduction: the pushed-in annotation is the premise-determined
-- interior body, the frame is plain `Θ`, and the face is `unsealAtᶜ 0 s`
-- — the leaf-wise mint that turns the face's now-OWNED slot 0 into its
-- instantiation.
--
-- WHAT USED TO STAND HERE was a refutation, and it was a statement about
-- the POLARITY INDEX, not about the rule.  Under a CONCEAL ∀-face — a
-- POLYMORPHIC ARGUMENT that crossed a Peel — the mint inserts `seal 0`
-- CONTRAVARIANTLY under the face's own covariant `seal`, so the tree was
-- MIXED-POLARITY and the indexed judgment refused it at both `p`.  With
-- the index retired (Jeremy's ruling, strong.Conversion) the tree types:
-- each leaf cites its own owner, `seal 0` the owner this very rule bound
-- and `seal 1` the crossed boundary's, and no global index has to
-- reconcile them.
--
-- So the section now records the POSITIVE fact, on the same witness —
-- the shape Examples §13 reaches from closed plain source, `f : ∀Y. Y ⇒ X`
-- crossing a Peel and then instantiated.

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

-- the CONCEAL ∀-face a Peel hands it: `sealAt 0 (∀Y. Y ⇒ X)`
Θt : CtxMorph
Θt = lock 0 ∷ []

st : Conv
st = id (` 0) ↦ seal 1

_ : sealAt 0 (`∀ (` 0 ⇒ ` 1)) ≡ `∀ st
_ = refl

-- the premise TyPeelR carries, at THIS redex.
⊢st : (abst ∷ fceC Θt Δt) ⊢ st ∶ (` 0 ⇒ `ℕ) ⇝ (` 0 ⇒ ` 1)
⊢st = conv-fun (conv-idv (abst , ez , vis-a)) (conv-seal (es ez))

Wft : Term
Wft = Wt ⟪ Θt , `∀ st ⟫

⊢Wft : Δt ∣ [] ⊢ Wft ⦂ `∀ (` 0 ⇒ ` 1)
⊢Wft = env (bw-l (bind `ℕ , ez , vis-b) bw[]) ⊢Wt
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

-- BOTH LEAVES, on the contractum's face type context: the INSERTED one
-- conceals the new owner's rep at the new owner's name, the face's OWN
-- one conceals ℕ at the crossed boundary's owner.  Per variable each is
-- exactly the conceal its owner licenses.
t-face-ctx : Ctxᵗ
t-face-ctx = fceC (bind (` 0) ∷ Θt) Δt

_ : t-face-ctx ≡ bind (` 0) ∷ bind `ℕ ∷ []
_ = refl

t-dom : t-face-ctx ⊢ seal 0 ∶ ` 1 ⇝ ` 0
t-dom = conv-seal ez

t-cod : t-face-ctx ⊢ seal 1 ∶ `ℕ ⇝ ` 1
t-cod = conv-seal (es ez)

-- … and so does the TREE, which is what the polarity index refused.
⊢t-face : t-face-ctx ⊢ seal 0 ↦ seal 1 ∶ (` 0 ⇒ `ℕ) ⇝ (` 1 ⇒ ` 1)
⊢t-face = conv-fun t-dom t-cod

-- THE CONTRACTUM TYPES, by the theorem — no hand-built derivation.
⊢t-contractum :
  Δt ∣ [] ⊢ (wkᴹ 1 Wt ·[ ` 0 ⇒ `ℕ , ` 0 ])
              ⟪ bind (` 0) ∷ Θt , seal 0 ↦ seal 1 ⟫ ⦂ (` 0 ⇒ ` 0)
⊢t-contractum = preserve-TyPeelR val-Wt ⊢st ⊢Rt

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
⊢Vi = env (bw-u (es ez) bw[])
          (env bw[] ⊢$ (conv-seal (es ez))
               (wf-var (bind `ℕ , es ez , vis-b)))
          (conv-seal ez)
          (wf-var (_ , ez , vis-b))

val-Vi : Value Vi
val-Vi = V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal

Ri : Term
Ri = (Vi ⟪ [] , id (` 0) ⟫) ⟪ Θi , unseal 0 ⟫

⊢Ri : Δi ∣ [] ⊢ Ri ⦂ ` 1
⊢Ri = env (bw-l (bind `ℕ , es ez , vis-b) bw[])
          (env bw[] ⊢Vi
               (conv-idv (_ , ez , vis-b))
               (wf-var (_ , ez , vis-b)))
          (conv-unseal ez)
          (wf-var (bind `ℕ , es ez , vis-b))

-- THE STEP, AT THE MOVED SCOPE.  `Θ₂ = lock 1 ∷ []` is binder-free, so
-- the move is `[] ◃ Θi ≡ lock 1 ∷ []` and `unlocked Θi ≡ []`: the lock
-- goes INTO the inner boundary and the outer one keeps nothing.
step-i : Δi ⊢ Ri -→ (Vi ⟪ [] ◃ Θi , unseal 0 ⟫) ⟪ unlocked Θi , idc (` 1) ⟫
step-i = IdPush val-Vi ez

_ : _≡_ {A = CtxMorph} ([] ◃ Θi) (lock 1 ∷ [])
_ = refl

_ : _≡_ {A = CtxMorph} (unlocked Θi) []
_ = refl

_ : idc (` 1) ≡ id (` 1)
_ = refl

-- The rep ` 1 is STILL not well formed inside the lock …
¬wf-i : ¬ (Ξi ⊢ᵗ ` 1)
¬wf-i (wf-var (_ , es ez , ()))

-- … and that is exactly why the OLD contractum, which presented it
-- there, was untypeable.  This is the refutation that used to stand
-- here; it is kept because it is what the rule change answers.
¬⊢i-old-contractum :
  ¬ (Δi ∣ [] ⊢ (Vi ⟪ [] , unseal 0 ⟫) ⟪ Θi , id (` 1) ⟫ ⦂ ` 1)
¬⊢i-old-contractum (env _ (env _ _ (conv-unseal ez) w) (conv-idv _) _) =
  ¬wf-i w

-- THE POSITIVE FACT.  With the lock moved into the inner boundary the
-- rep is presented on the FACE type context `fceC Θi Δi ≡ Δi`, where
-- slot 1 is live — and the contractum TYPES.  (`ProbeMove.agda` in the
-- main tree checked this derivation by hand; here it is the theorem.)
⊢i-contractum :
  Δi ∣ [] ⊢ (Vi ⟪ lock 1 ∷ [] , unseal 0 ⟫) ⟪ [] , id (` 1) ⟫ ⦂ ` 1
⊢i-contractum = preserve-IdPush val-Vi ez ⊢Ri

------------------------------------------------------------------------
-- §5  THE HEADLINE
------------------------------------------------------------------------

-- Every §-witness above now TYPES: §1's (the repaired CancelR residue),
-- §2's (the repaired TyPeelR contractum) and §4's (the moved scope).
-- There is no surviving refutation, and `strong.Preservation` states the
-- theorem outright.
