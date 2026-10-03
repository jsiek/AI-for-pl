module proof.DGG.notes.ForallBoundaryRisks where

-- File Charter:
--   * THE THREE RISKS OF `∀⊑⟪+⟫` that the SimBack skeleton flagged
--     (proof/DGG/notes/M2-child-statements.md, Risks and Misfit 2);
--     findings in ForallBoundaryRisks.md.  NOT a Def module, not
--     imported by All.agda.
--   * §1 BLAME SPINES.  `BlameSpine M`: blame under one-sided frames
--     (cast, ν, boundary).  `⊑-spine`: a term related to a blame spine is
--     a blame spine.  No value is one (`value-¬spine`) and no `inst_X`
--     image is one (`inst-¬spine`).  So R1 AS STATED is refuted:
--     `∀⊑⟪+⟫ × Blame-⟪⟫` is absurd (`R1-absurd`).
--   * §2 THE COUNTEREXAMPLE TO SimBack (R1 one step earlier, which is
--     also R2): a ∀-value whose `inst_X` image blames by itself,
--     `(Λ true⟨𝔹!⟩)⟨∀X. ℕ?ℓ⟩ : ∀X.ℕ`, related by `∀⊑⟪+⟫` to a right
--     boundary whose interior performs that blame.  `simBack-false`
--     held for the rule as it was; with the fix (NonVar A, 0 ∈ᵗ A in
--     ∀⊑⟪+⟫) the derivation `cex` is gone and both are kept commented.
--   * §3 PROGRAMS for R2 (L2c/R2c: a Merge inside the right's Inst
--     boundary, which the stuck left cannot match) and R3 (L3c/R3c: a
--     duplicated Inst boundary, one copy instantiated on the left);
--     §4 the proposed side conditions, checked on the counterexample
--     and on the existing derivations' arguments; §5 their runs.
--   * Design.md D26 (2026-10-03) removed `∀⊑⟪+⟫`: its instances are
--     `⊑⟪⟫` with one opening.  `⊑-spine` covers the openings
--     (`opens-spine`); the prose about `∀⊑⟪+⟫` is history.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import TermSubst using (renᴹᴿ; crossΛᴹ)
open import Reduction
open import Imprecision
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.RunFrames using (value-run≡)
open import proof.DGG.SimBackDef using (SimBack)
open import proof.TypeSafety.PreservationSupport using (alloc-wf)
open import proof.Ctx using (wf-empty)
open import examples.TypeCheck using (tc)
open import examples.Eval
open import examples.CambridgeExamples using (I; genI; instI)

------------------------------------------------------------------------
-- 1. Blame spines
------------------------------------------------------------------------

data BlameSpine : Term → Set where
  bs-blame : ∀ {ℓ} → BlameSpine (blame ℓ)
  bs-cast  : ∀ {M μ p} → BlameSpine M → BlameSpine (M ⟨ μ ∣ p ⟩)
  bs-ν     : ∀ {L A c} → BlameSpine L → BlameSpine (ν A · L ⟨ c ⟩)
  bs-⟪⟫    : ∀ {M Θ c} → BlameSpine M → BlameSpine (M ⟪ Θ , c ⟫)

value-¬spine : ∀ {V} → Value V → BlameSpine V → ⊥
value-¬spine (V-simple S-$) ()
value-¬spine (V-simple S-true) ()
value-¬spine (V-simple S-false) ()
value-¬spine (V-simple S-ƛ) ()
value-¬spine (V-simple (S-Λ _)) ()
value-¬spine (V-simple (S-cast v _)) (bs-cast b) = value-¬spine v b
value-¬spine (V-⟪⟫ u _) (bs-⟪⟫ b) = value-¬spine (V-simple u) b
value-¬spine (V-fresh v _) (bs-⟪⟫ (bs-cast b)) = value-¬spine v b

ren-spine : ∀ ρ M → BlameSpine (renᴹᴿ ρ M) → BlameSpine M
ren-spine ρ (` x) ()
ren-spine ρ ($ n) ()
ren-spine ρ `true ()
ren-spine ρ `false ()
ren-spine ρ (ƛ A ∙ N) ()
ren-spine ρ (L · M) ()
ren-spine ρ (Λ N) ()
ren-spine ρ (ν A · L ⟨ c ⟩) (bs-ν b) = bs-ν (ren-spine ρ L b)
ren-spine ρ (M ⟪ Θ , c ⟫) (bs-⟪⟫ b) = bs-⟪⟫ (ren-spine ρ M b)
ren-spine ρ (M ⟨ μ ∣ p ⟩) (bs-cast b) = bs-cast (ren-spine ρ M b)
ren-spine ρ (blame ℓ) b = bs-blame

-- inst_X(V) is never a blame spine: each layer of V is a value
inst-¬spine : ∀ {V N} → Value V → InstX V N → BlameSpine N → ⊥
inst-¬spine v (inst-Λ n) b = value-¬spine n b
inst-¬spine v (inst-gen {W = W} w) (bs-cast (bs-⟪⟫ b)) =
  value-¬spine w (ren-spine suc W b)
inst-¬spine v (inst-∀ w i) (bs-cast b) = inst-¬spine w i b
inst-¬spine v (inst-⟪⟫ u i) (bs-⟪⟫ b) = inst-¬spine (V-simple u) i b

-- what is related to a blame spine is a blame spine
-- the openings of `⊑⟪⟫` (design.md D26): an opened image is no blame
-- spine (the former ∀⊑⟪+⟫ case), so with an opening the spine is absurd
opens-spine : ∀ {Δ Δ′ Δ⁺ Θ′} {W : World Δ Δ′} {W⁺ : World Δ⁺ Δ′}
    {M M₀ A A₀}
  → Opens Θ′ W M A W⁺ M₀ A₀ → BlameSpine M₀ → BlameSpine M
opens-spine open-none b = b
opens-spine (open-∀ _ _ v _ i _ _ os) b =
  ⊥-elim (inst-¬spine v i (opens-spine os b))

⊑-spine : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {M M′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶ p → BlameSpine M′ → BlameSpine M
⊑-spine (x⊑x _) ()
⊑-spine (κ⊑κ lit-$ _) ()
⊑-spine (κ⊑κ lit-true _) ()
⊑-spine (κ⊑κ lit-false _) ()
⊑-spine (ƛ⊑ƛ _ _ _) ()
⊑-spine (·⊑· _ _) ()
⊑-spine (blame⊑ _ _ _) b = bs-blame
⊑-spine (cast⊑cast d _ _ _) (bs-cast b) = bs-cast (⊑-spine d b)
⊑-spine (cast⊑ d _ _) b = bs-cast (⊑-spine d b)
⊑-spine (⊑cast d _ _) (bs-cast b) = ⊑-spine d b
⊑-spine (Λ⊑Λ _ _ _ _ _) ()
⊑-spine (Λ⊑ _ _ _ v d _) b = ⊥-elim (value-¬spine v (⊑-spine d b))
⊑-spine (ν⊑ν d _ _ _ _ _) (bs-ν b) = bs-ν (⊑-spine d b)
⊑-spine (ν⊑ d _ _ _) b = bs-ν (⊑-spine d b)
⊑-spine (⟪⟫⊑⟪⟫ _ _ d _ _ _ _) (bs-⟪⟫ b) = bs-⟪⟫ (⊑-spine d b)
⊑-spine (⟪⟫⊑ _ _ d _ _) b = bs-⟪⟫ (⊑-spine d b)
⊑-spine (⊑⟪⟫ _ os _ d _ _) (bs-⟪⟫ b) = opens-spine os (⊑-spine d b)

-- no value is related to a blame spine
value-⋢-spine : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {V M′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Value V → BlameSpine M′ → ¬ (W ∣ γ ⊢ V ⊑ M′ ∶ p)
value-⋢-spine v b d = value-¬spine v (⊑-spine d b)

-- R1 as stated: the right boundary `[+X^β] blame ℓ ⟨c′⟩` (the redex of
-- Blame-⟪⟫) is related to no value, by ∀⊑⟪+⟫ or any other rule
R1-absurd : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {V Θ c ℓ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Value V → ¬ (W ∣ γ ⊢ V ⊑ blame ℓ ⟪ Θ , c ⟫ ∶ p)
R1-absurd v = value-⋢-spine v (bs-⟪⟫ bs-blame)

-- ... and ∀⊑⟪+⟫'s premise `inst_X(V) ⊑ blame ℓ` is impossible
inst-⋢-blame : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {V N ℓ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Value V → InstX V N → ¬ (W ∣ γ ⊢ N ⊑ blame ℓ ∶ p)
inst-⋢-blame v i d = inst-¬spine v i (⊑-spine d bs-blame)

-- a blame spine only steps to a blame spine
spine-step : ∀ {Δ M M′ δ} → BlameSpine M → Δ ⊢ M -→ M′ ∣ δ
  → BlameSpine M′
spine-step (bs-ν b) (TyBeta v _ _) = ⊥-elim (value-¬spine v b)
spine-step (bs-⟪⟫ b) (Merge v _ _ _ _ _ _) = ⊥-elim (value-¬spine v b)
spine-step (bs-⟪⟫ b) (Id u _) = ⊥-elim (value-¬spine (V-simple u) b)
spine-step (bs-cast b) (CastId v) = ⊥-elim (value-¬spine v b)
spine-step (bs-cast b) (CastSeq v) = ⊥-elim (value-¬spine v b)
spine-step (bs-cast b) (CastSeq? v) = ⊥-elim (value-¬spine v b)
spine-step (bs-cast b) (Inst v) = ⊥-elim (value-¬spine v b)
spine-step (bs-cast (bs-cast b)) (TagUntag v) = ⊥-elim (value-¬spine v b)
spine-step b (TagUntagBad _ _) = bs-blame
spine-step (bs-⟪⟫ (bs-cast b)) (IdDyn v _) = ⊥-elim (value-¬spine v b)
spine-step (bs-⟪⟫ (bs-cast b)) (IdDyn-var v _ _ _ _) =
  ⊥-elim (value-¬spine v b)
spine-step b (TagUntagBad-⟪⟫ _ _) = bs-blame
spine-step b (BlameBotIntro _) = bs-blame
spine-step b Blame-ν = bs-blame
spine-step b Blame-⟪⟫ = bs-blame
spine-step b Blame-cast = bs-blame
spine-step (bs-ν b) (ξ-ν st) = bs-ν (spine-step b st)
spine-step (bs-⟪⟫ b) (ξ-⟪⟫ _ st) = bs-⟪⟫ (spine-step b st)
spine-step (bs-cast b) (ξ-cast st) = bs-cast (spine-step b st)

spine-run : ∀ {Δ M N} → BlameSpine M → Δ ⊢ M -→* N → BlameSpine N
spine-run b done = b
spine-run b (st then r) = spine-run (spine-step b st) r

------------------------------------------------------------------------
-- 2. A counterexample to SimBack (the rule as it stands)
------------------------------------------------------------------------

-- the contexts of p3-inst: the left empty; the right with αᴿ:=★ at
-- rep. var 0, and inside the Inst boundary `+X^αᴿ`
ΔR ΔRₓ : Ctxᵗ
ΔR  = allocate ★ empty
ΔRₓ = reps ΔR ∣ (0 ∷ [])

Θ₀ : Boundary
Θ₀ = bind 0 0 ∷ []

μX : ModeEnv
μX = X∼X ∷ []

-- B₀ = true⟨𝔹!⟩ (under one Λ),  Vc = (ΛX. B₀) ⟨∀X. ℕ?ℓ⟩ : ∀X.ℕ
B₀ Vc : Term
B₀ = `true ⟨ μX ∣ `𝔹 ! ⟩
Vc = Λ B₀ ⟨ [] ∣ ∀ᵖ (`ℕ ？ 0) ⟩

-- Nc = inst_X(Vc) = true⟨𝔹!⟩⟨ℕ?ℓ⟩: it BLAMES by itself (TagUntagBad)
Nc : Term
Nc = B₀ ⟨ μX ∣ `ℕ ？ 0 ⟩

-- the right: Nc⟨ℕ!⟩ inside `+X^αᴿ` (β := ★), at interior type ★
Mc Rc Rc₁ : Term
Mc  = Nc ⟨ μX ∣ `ℕ ! ⟩
Rc  = Mc ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫
Rc₁ = (blame 0 ⟨ μX ∣ `ℕ ! ⟩) ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫

vB₀ : Value B₀
vB₀ = V-simple (S-cast (V-simple S-true) I-tag)

vVc : Value Vc
vVc = V-simple (S-cast (V-simple (S-Λ vB₀)) I-∀ᵖ)

Vc-⊢ : empty ∣ [] ⊢ Vc ⦂ `∀ `ℕ
Vc-⊢ = tc

instVc : InstX Vc Nc
instVc = inst-∀ (V-simple (S-Λ vB₀)) (inst-Λ vB₀)

Rc-ty : BdyTy ΔR Θ₀ ΔRₓ ★ ⌞ id ★ ⌟ ★
Rc-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = Rc}))))

W₃ : World empty ΔR
W₃ = world [] []↪ []↪ [] []

-- ∀X.ℕ ⊑ ★ by ∀⊑★ (ℕ is not ★; X does not occur)
qc : `∀ `ℕ ⊑ᵂ⟨ W₃ ⟩ ★
qc = ∀⊑★ ns-ℕ (ι⊑★ base-ℕ)

-- the premise: Nc ⊑ Nc⟨ℕ!⟩ at ℕ ⊑ ★ in W₃ ⊕⁺ X⊑X ^ 0
Nc⊑Mc : W₃ ⊕⁺ X⊑X ^ 0 ∣ [] ⊢ Nc ⊑ Mc ∶ ι⊑★ base-ℕ
Nc⊑Mc =
  ⊑cast
    (cast⊑cast
      (cast⊑cast (κ⊑κ lit-true (ι⊑ι base-𝔹))
        (cast-ty (⊢tag g-𝔹) refl) (cast-ty (⊢tag g-𝔹) refl) ★⊑★)
      (cast-ty (⊢check g-ℕ) refl) (cast-ty (⊢check g-ℕ) refl)
      (ι⊑ι base-ℕ))
    (cast-ty (⊢tag g-ℕ) refl) (ι⊑★ base-ℕ)

-- FIXED (2026-10-03): under the rule as it was, `cex` below was a
-- derivation and `simBack-false : SimBack → ⊥` held.  ∀⊑⟪+⟫ now has
-- the premises `NonVar A` and `0 ∈ᵗ A` (here A = ℕ, and `cex-excluded`
-- shows `¬ (0 ∈ᵗ ℕ)`), so `cex` is no longer derivable.  The old
-- construction, kept for the record:
{-
cex : W₃ ∣ [] ⊢ Vc ⊑ Rc ∶ qc
cex = ∀⊑⟪+⟫ {m = X⊑X} vVc Vc-⊢ instVc Nc⊑Mc r-here Rc-ty qc
-}

-- the right's step: the interior's TagUntagBad, under ξ-⟪⟫ and ξ-cast
int₀ : ΔR ⊢ⁱ Θ₀ ⇒ ΔRₓ
int₀ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

st : ΔR ⊢ Rc -→ Rc₁ ∣ none
st = ξ-⟪⟫ int₀ (ξ-cast (TagUntagBad (V-simple S-true) (λ ())))

-- the three premises of SimBack
wfΔR : WfCtx ΔR
wfΔR = alloc-wf wf-empty wfᴿ-★

wfW₃ : WfWorld W₃
wfW₃ = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
  (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
  (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })

{-
-- SimBack fails: the left value cannot step, and every state the right
-- reaches from Rc₁ is a blame spine, which no value is related to
simBack-false : SimBack → ⊥
simBack-false sb with sb wf-empty wfΔR wfW₃ cex st
simBack-false sb | inj₁ (N₂ , N₂′ , r , r″ , W′ , ev , wf′ , q , N₂⊑N₂′)
  with value-run≡ vVc r
simBack-false sb | inj₁ (N₂ , N₂′ , r , r″ , W′ , ev , wf′ , q , N₂⊑N₂′)
  | refl =
  value-⋢-spine vVc (spine-run (bs-⟪⟫ (bs-cast bs-blame)) r″) N₂⊑N₂′
simBack-false sb | inj₂ (ℓ , r) with value-run≡ vVc r
simBack-false sb | inj₂ (ℓ , r) | ()
-}

------------------------------------------------------------------------
-- 3. Programs (hand-compiled as ImprecisionExamples does)
------------------------------------------------------------------------

∀X⇒X : Ty
∀X⇒X = `∀ (` 0 ⇒ ` 0)

revX : Conv
revX = reveal 0 (` 0 ⇒ ` 0)

-- R2: a gen-cast ∀-value over a BOUNDARY value, instantiated by the
-- right's Inst; inst_X puts that boundary under `−X`, a Merge redex.
--   L  (λh:∀X.X→X. h) ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
--   R  (λh:★→★. h)    ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
I[★] Gc L2c R2c : Term
I[★] = ν ★ · I ⟨ revX ⟩
Gc   = (ƛ ∀X⇒X ∙ ` 0) · (I[★] ⟨ [] ∣ genI ⟩)
L2c  = (ƛ ∀X⇒X ∙ ` 0) · Gc
R2c  = (ƛ (★ ⇒ ★) ∙ ` 0) · (Gc ⟨ [] ∣ instI ⟩)

L2c-⊢ : empty ∣ [] ⊢ L2c ⦂ ∀X⇒X
L2c-⊢ = tc

R2c-⊢ : empty ∣ [] ⊢ R2c ⦂ (★ ⇒ ★)
R2c-⊢ = tc

-- R3: the right's Inst boundary is DUPLICATED by Beta; the left
-- instantiates one copy, so β gets a global left partner while the
-- other copy is still related by ∀⊑⟪+⟫.
--   L  (λf:∀X.X→X. (λy:ℕ. f) (f[ℕ] 5)) (ΛX.λx:X.x)
--   R  (λf:★→★.    (λy:★. f) (f 5))    (ΛX.λx:X.x)
L3c R3c : Term
L3c = (ƛ ∀X⇒X ∙ ((ƛ `ℕ ∙ ` 1) · ((ν `ℕ · ` 0 ⟨ revX ⟩) · $ 5))) · I
R3c = (ƛ (★ ⇒ ★) ∙ ((ƛ ★ ∙ ` 1) · (` 0 · ($ 5 ⟨ [] ∣ `ℕ ! ⟩))))
    · (I ⟨ [] ∣ instI ⟩)

L3c-⊢ : empty ∣ [] ⊢ L3c ⦂ ∀X⇒X
L3c-⊢ = tc

R3c-⊢ : empty ∣ [] ⊢ R3c ⦂ (★ ⇒ ★)
R3c-⊢ = tc

------------------------------------------------------------------------
-- 4. The proposed side conditions
------------------------------------------------------------------------

-- the right term of §2 as a run (for the renderer)
Rc-⊢ : ΔR ∣ [] ⊢ Rc ⦂ ★
Rc-⊢ = tc

-- (fix for R1/R2) `NonVar A` and `0 ∈ᵗ A`, Λ⊑'s side conditions: the
-- counterexample's A = ℕ violates the second
cex-excluded : ¬ (0 ∈ᵗ `ℕ)
cex-excluded ()

-- ... and every existing ∀⊑⟪+⟫ derivation (p3-inst, ch-x0 = p3-inst,
-- cg-x0, c2-x0, c12-x0) has A = X → X and the world W₃:
existing-A : NonVar (` 0 ⇒ ` 0)
existing-A = nv-⇒

existing-occ : 0 ∈ᵗ (` 0 ⇒ ` 0)
existing-occ = ∈-⇒ˡ ∈-var

-- (R3) `NoLeftPartner W₃ 0`, written out (`∀ α → ¬ Paired W α β`, a
-- premise of Evolve's `ev-L⇔` until design.md D25 dropped it): W₃
-- pairs nothing
existing-no-partner : ∀ α → ¬ Paired W₃ α 0
existing-no-partner α (inj₁ ())
existing-no-partner α (inj₂ ())

------------------------------------------------------------------------
-- 5. The runs of §3
------------------------------------------------------------------------

L2c-rules : evalRules 20 L2c-⊢ ≡ "TyBeta" ∷ "Beta" ∷ "Beta" ∷ []
L2c-rules = refl

R2c-rules : evalRules 20 R2c-⊢
  ≡ "TyBeta" ∷ "Beta" ∷ "Inst" ∷ "TyBeta" ∷ "Merge" ∷ "Beta" ∷ []
R2c-rules = refl

L3c-run : Reaches 20 7 L3c-⊢ I
L3c-run = reaches refl (ans-value (V-simple (S-Λ (V-simple S-ƛ))))

L3c-rules : evalRules 20 L3c-⊢
  ≡ "Beta" ∷ "TyBeta" ∷ "Wrap" ∷ "Beta" ∷ "Merge" ∷ "Id" ∷ "Beta" ∷ []
L3c-rules = refl

R3c-rules : evalRules 25 R3c-⊢
  ≡ "Inst" ∷ "TyBeta" ∷ "Beta" ∷ "CastFun" ∷ "CastId" ∷ "Wrap" ∷ "Beta"
    ∷ "Merge" ∷ "IdDyn" ∷ "Id" ∷ "CastId" ∷ "Beta" ∷ []
R3c-rules = refl
