module proof.DGG.notes.FixA-MergedBoundary where

-- File Charter:
--   * HISTORICAL: written against the relation before design.md D26
--     (2026-10-03), which removed `∀⊑⟪+⟫` and generalized `⊑⟪⟫` with
--     `Opens`.  It no longer type-checks against TermImprecision (it, or
--     a note it imports, uses the old rule) and is excluded from every
--     check: All.agda does not import it and it is not a *Proof.agda.
--     FixA (`∀⊑⟪+⟫ᴹ`) was not adopted; D26 took the generalized `⊑⟪⟫`.
--   * FIX (a) FOR THE BOUNDARY-MERGE COUNTEREXAMPLE of
--     RestrictedForallBoundary §3: a second rule `∀⊑⟪+⟫ᴹ` for a
--     MERGED right boundary `(θ ∷ Θ′) ++ (bind 0 β ∷ [])`.  Findings
--     in FixA-MergedBoundary.md.  NOT a Def module, not imported by
--     All.agda; nothing outside this file and its .md is edited.
--   * §1 a LOCAL COPY of the relation: RestrictedForallBoundary's
--     (∀⊑⟪+⟫ with `Simple V′`) plus `∀⊑⟪+⟫ᴹ`.  The rule is
--     SYNTAX-DIRECTED: the inner conversion of its premise is not
--     existential, it is `Δ⋉ᶜ ⊢ c′ ⨟ c₂⁻`, with c₂⁻ the merged
--     context's spelling of `conceal 0 A′` (the inverse of the Inst
--     entry's `reveal 0 A′`).  `embed` maps RestrictedForallBoundary's
--     relation into this one, so its derivations (the seven blocks,
--     `lk⊑rk`, `lk₁⊑rk₁`) carry over unchanged.
--   * §2 the counterexample K: every synchronization pair, by
--     ∀⊑⟪+⟫ᴹ after the right's Merge; and the Sim, SimBack and DGG
--     part 1 obligations that RestrictedForallBoundary refuted, now
--     MET at those pairs (`sim-K`, `simBack-K-inst`, `simBack-K-beta`,
--     `dgg1-K`).
--   * §3 the composition inverse (question 2): the merged conversion,
--     composed with `conceal 0 A′`, gives back the inner conversion,
--     checked by `refl` on K and on C18's shapes; the general law is
--     stated (`RevealCancel`), not proved.
--   * §4 the LEFT'S LATER TyBeta (question 3): K2, where the left
--     instantiates the ∀-value after the right merged.  The pair after
--     the left's TyBeta (left boundary over a left-only boundary,
--     right merged) and after the left's Merge are derived, at the
--     world of `ev-L⇔`, with Sim's two left steps (`sim-K2-tyBeta`,
--     `sim-K2-merge`) and DGG part 1 (`dgg1-K2`).
--   * §5 the new lemma statements (question 3): `InstSyncᴬ` (the
--     Inst cases; no `¬ ForallBdy`) and `RightMergeInterior` (the
--     left's later TyBeta).  Statements only.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction
  using (InstX; inst-Λ; inst-gen; inst-∀; inst-⟪⟫; _⊢_-→_∣_; _⊢_-→*_;
         done; _then_)
open import Imprecision
open import ImprecisionWorld
open import ConversionImprecision
import TermImprecision as TI
open TI
  using (Lit; lit-$; lit-true; lit-false; CastTy; cast-ty; NuTy; BdyTy;
         bdy-ty; NuConversionImp; BdyConversionImp; ⟪⟫-inv; cast-inv; ν-inv)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; ev-L⇔; ev-R; ev-noneᴸ; ev-noneᴿ; ev-done; applyˢ;
         allocs)
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms)
open import examples.TermImprecisionExamples using (idX; revX; Θ₀; ΔL)
open import examples.TermImprecisionRebaseExamples
  using (id★↦; ∀id⊑★; ℕ⇒ℕ⊑★⇒★)
import proof.DGG.notes.RestrictedForallBoundary as R
open R
  using (KK; cId; cK; ∀X⇒X; VL; Nk; Rarg₃; Bm; RF; LK; LK₁; RK; RK₁; RK₂;
         RK₃; RK₄; ΔRk; wfΔL; wfΔRk; vVL; vRF; Wk; Wk-wf; PwK; ΘX; WX;
         WX-int; WX-conv; WX-wf; instVL; bNL; bNR; bBm; id★↦ᴿk-ty; VL-⊢;
         Θ₂; cId⊑cId; Wk1; Wk1-wf; st₀; st₁; st₂; st₃; st₄; stL; stL₀)

private
  variable
    Δ Δ′ : Ctxᵗ

------------------------------------------------------------------------
-- 1. The relation with ∀⊑⟪+⟫ᴹ (a local copy)
------------------------------------------------------------------------

infix 3 _∣_⊢_⊑_∶_

data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) (γ : CtxImp W)
    : Term → Term → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

  x⊑x : ∀ {x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

  κ⊑κ : ∀ {k ι} → Lit k ι → (p : ι ⊑ᵂ⟨ W ⟩ ι) → W ∣ γ ⊢ k ⊑ k ∶ p

  ƛ⊑ƛ : ∀ {N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

  ·⊑· : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ M′ ∶ pA
    → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

  blame⊑ : ∀ {ℓ M′ A A′}
    → Δ ⊢ᵗ A → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′ → (p : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

  cast⊑cast : ∀ {M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  cast⊑ : ∀ {M M′ μ c B A A′} {p : B ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ μ c B A → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

  ⊑cast : ∀ {M M′ μ′ c′ A B′ A′} {p : A ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ′ μ′ c′ B′ A′ → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  Λ⊑Λ : ∀ {γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕ X⊑X ⟩ A′}
    → LiftCtx X⊑X γ γ′ → Value V → Value V′
    → W ⊕ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
    → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

  Λ⊑ : ∀ {γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′}
    → NonVar A → 0 ∈ᵗ A → LiftCtxᴸ γ γ′ → Value V
    → W ⊕ᴸ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  -- RestrictedForallBoundary's rule (a simple interior)
  ∀⊑⟪+⟫ : ∀ {V N V′ β m c′ A A′ B′} {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
    → NonVar A
    → 0 ∈ᵗ A
    → Value V
    → Δ ∣ lhs γ ⊢ V ⦂ `∀ A
    → InstX V N
    → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
    → Simple V′
    → Δ′ ∋rep β := ★
    → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q

  -- FIX (a): THE MERGED RULE.  The right is the Inst boundary merged
  -- with a non-empty inner boundary `θ ∷ Θ′` (the Inst entry acts
  -- first).  The premise un-merges it: the inner conversion is the
  -- merged one composed with c₂⁻, the merged context's spelling of
  -- `conceal 0 A′`, the inverse of the Inst entry's `reveal 0 A′`.
  -- Every premise is determined by the conclusion (Δ⋉ᶜ, Δ₂ᶜ by
  -- `conversion-functional`, c₂⁻ by `SameConv`), so the rule is
  -- syntax-directed.
  ∀⊑⟪+⟫ᴹ : ∀ {Δ′ᵢ Δ₂ᶜ Δ⋉ᶜ V N U′ θ Θ′ β m c′ c₂⁻ A A′ A′ᵢ B′}
      {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
    → NonVar A
    → 0 ∈ᵗ A
    → Value V
    → Δ ∣ lhs γ ⊢ V ⦂ `∀ A
    → InstX V N
    → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ U′ ⟪ θ ∷ Θ′ , Δ⋉ᶜ ⊢ c′ ⨟ c₂⁻ ⟫ ∶ r
    → Simple U′
    → Δ′ ∋rep β := ★
    → BdyTy Δ′ ((θ ∷ Θ′) ++ (bind 0 β ∷ [])) Δ′ᵢ A′ᵢ c′ B′
    → Δ′ ⊢ᶜ (θ ∷ Θ′) ++ (bind 0 β ∷ []) ⇒ Δ⋉ᶜ
    → Δ′ ⊢ᶜ bind 0 β ∷ [] ⇒ Δ₂ᶜ
    → SameConv Δ⋉ᶜ c₂⁻ Δ₂ᶜ (conceal 0 A′)
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ V ⊑ U′ ⟪ (θ ∷ Θ′) ++ (bind 0 β ∷ []) , c′ ⟫ ∶ q

  ν⊑ν : ∀ {L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ r → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′ → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ M′ ∶ r → A ⊑ᵂ⟨ W ⟩ ★ → NuTy Δ A C c B
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

  ⟪⟫⊑⟪⟫ : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ}
      {M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′ → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  ⟪⟫⊑ : ∀ {Δᵢ} {Wᵢ : World Δᵢ Δ′}
      {M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
    → Interior W Θ [] Wᵢ → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

  ⊑⟪⟫ : ∀ {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
      {M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′ → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

-- RestrictedForallBoundary's relation embeds (∀⊑⟪+⟫ᴹ is the only new
-- rule), so the seven blocks and its counterexample pairs carry over
embed : ∀ {W : World Δ Δ′} {γ : CtxImp W} {M M′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W R.∣ γ ⊢ M ⊑ M′ ∶ p → W ∣ γ ⊢ M ⊑ M′ ∶ p
embed (R.x⊑x x) = x⊑x x
embed (R.κ⊑κ k p) = κ⊑κ k p
embed (R.ƛ⊑ƛ wA wA′ d) = ƛ⊑ƛ wA wA′ (embed d)
embed (R.·⊑· d e) = ·⊑· (embed d) (embed e)
embed (R.blame⊑ wA ⊢M p) = blame⊑ wA ⊢M p
embed (R.cast⊑cast d c c′ q) = cast⊑cast (embed d) c c′ q
embed (R.cast⊑ d c q) = cast⊑ (embed d) c q
embed (R.⊑cast d c′ q) = ⊑cast (embed d) c′ q
embed (R.Λ⊑Λ l v v′ d q) = Λ⊑Λ l v v′ (embed d) q
embed (R.Λ⊑ nv occ l v d q) = Λ⊑ nv occ l v (embed d) q
embed (R.∀⊑⟪+⟫ nv occ v ⊢V i d s hβ b q) =
  ∀⊑⟪+⟫ nv occ v ⊢V i (embed d) s hβ b q
embed (R.ν⊑ν d a n n′ nc q) = ν⊑ν (embed d) a n n′ nc q
embed (R.ν⊑ d a n q) = ν⊑ (embed d) a n q
embed (R.⟪⟫⊑⟪⟫ int wf d b b′ bc q) = ⟪⟫⊑⟪⟫ int wf (embed d) b b′ bc q
embed (R.⟪⟫⊑ int wf d b q) = ⟪⟫⊑ int wf (embed d) b q
embed (R.⊑⟪⟫ int wf d b′ q) = ⊑⟪⟫ int wf (embed d) b′ q

------------------------------------------------------------------------
-- 1b. The seven blocks (RestrictedForallBoundary §2), carried over
------------------------------------------------------------------------

open import examples.TermImprecisionExamples
  using (W₃; W₁; L1′; R3′; ℕ⊑★)
open import examples.ImprecisionExamples using (L1)
open import examples.TermImprecisionRebaseExamples using (Cg-R₂; C12-R₂)
open import examples.CambridgeExamples using (C2-L; C12-L)
open import proof.DGG.notes.ForallBoundaryFixes
  using (L3c₁; L3c₂; R3c₃; W₂d; L2c₂; R2c₅; W4)

p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
p3-inst = embed R.p3-inst

cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ℕ⊑★
cg-x0 = embed R.cg-x0

c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ℕ⊑★
c2-x0 = embed R.c2-x0

c12-x0 : W₃ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
c12-x0 = embed R.c12-x0

l3c-pre : W₃ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ ∀id⊑★ W₃
l3c-pre = embed R.l3c-pre

l3c-post : W₁ ∣ [] ⊢ L3c₂ ⊑ R3c₃ ∶ ∀id⊑★ W₁
l3c-post = embed R.l3c-post

l3d-before : W₁ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
l3d-before = embed R.l3d-before

l3d-after : W₂d ∣ [] ⊢ L1′ ⊑ R3′ ∶ ℕ⊑★
l3d-after = embed R.l3d-after

r2c-post : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ ∀id⊑★ W4
r2c-post = embed R.r2c-post

------------------------------------------------------------------------
-- 2. The counterexample K, with ∀⊑⟪+⟫ᴹ
------------------------------------------------------------------------

--   L  (λf:∀X.X→X. f) (K[ℕ])        K = ΛY.ΛX.λx:X.x
--   R  (λf:★→★.    f) (K[ℕ]⟨inst⟩)
-- L: TyBeta, Beta.  R: TyBeta, Inst, TyBeta, Merge, Beta.

-- the merged context and the Inst entry's conversion context
Δ⋉K Δ₂K : Ctxᵗ
Δ⋉K = reps ΔRk ∣ (0 ∷ 1 ∷ [])
Δ₂K = reps ΔRk ∣ (0 ∷ [])

conv⋉K : ΔRk ⊢ᶜ Θ₂ ⇒ Δ⋉K
conv⋉K = conversion
  (conv-bind (_ , there here)
    (conv-bind (_ , here) conv[] fresh[] ins-here)
    (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

conv₂K : ΔRk ⊢ᶜ bind 0 0 ∷ [] ⇒ Δ₂K
conv₂K = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)

-- the inverse of revX = reveal 0 (X → X)
revX⁻ : Conv
revX⁻ = conceal 0 (` 0 ⇒ ` 0)

revX⁻-same : SameConv Δ⋉K revX⁻ Δ₂K revX⁻
revX⁻-same =
  _ , same , same
  where
  same : ∀ {η} → (0 ∷ η) ⊩ revX⁻ ~
    ⌞ unseal 0 ↦ tail (seal 0) ⌟
  same = sameᶜ-tail (sameᶜ-mid (sameᶜ-fun (sameᶜ-unseal here)
           (sameᶜ-tail (sameᶜ-seal here))))

-- THE UN-MERGE IS COMPUTED: revX ⨟ conceal = cId, the inner conversion
unmerge-K : (Δ⋉K ⊢ revX ⨟ revX⁻) ≡ cId
unmerge-K = refl

-- ... and the right's Merge composed exactly that: cId ⨟ revX = revX
merge-K : (Δ⋉K ⊢ cId ⨟ revX) ≡ revX
merge-K = refl

-- the premise: N = inst_Y(VL) = Nk against the un-merged right
Nk⊑Nk : PwK ∣ [] ⊢ Nk ⊑ Nk ∶ ⇒⊑⇒ X⊑X X⊑X
Nk⊑Nk =
  ⟪⟫⊑⟪⟫ WX-int WX-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bNL bNR
    (WX , WX-conv , cId⊑cId X⊑X) (⇒⊑⇒ X⊑X X⊑X)

-- THE FINAL ARGUMENT PAIR, by ∀⊑⟪+⟫ᴹ (it was `final-unrelated`)
VL⊑Bm : Wk ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk
VL⊑Bm =
  ∀⊑⟪+⟫ᴹ {Θ′ = []} {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var) vVL VL-⊢ instVL Nk⊑Nk
    S-ƛ r-here bBm conv⋉K conv₂K revX⁻-same (∀id⊑★ Wk)

VL⊑RF : Wk ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk
VL⊑RF = ⊑cast VL⊑Bm id★↦ᴿk-ty (∀id⊑★ Wk)

-- the other synchronization pairs: the initial pair and the pair after
-- both source TyBetas (no ∀⊑⟪+⟫ needed, carried over) ...
lk⊑rk : ∅ʷ ∣ [] ⊢ LK ⊑ RK ∶ ∀id⊑★ ∅ʷ
lk⊑rk = embed R.lk⊑rk

lk₁⊑rk₁ : Wk1 ∣ [] ⊢ LK₁ ⊑ RK₁ ∶ ∀id⊑★ Wk1
lk₁⊑rk₁ = embed R.lk₁⊑rk₁

-- ... and the pair after the right's Inst, TyBeta, Merge (the left
-- still before its Beta)
lk₁⊑rk₄ : Wk ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ ∀id⊑★ Wk
lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

------------------------------------------------------------------------
-- 2b. The obligations RestrictedForallBoundary refuted, now met
------------------------------------------------------------------------

-- Sim's conclusion (SimDef), for this relation
SimConcl : ∀ {Δ Δ′} → World Δ Δ′ → Term → Term → (A A′ : Ty) → Alloc
  → Set
SimConcl {Δ} {Δ′} W M′ N A A′ ξ =
  ∃[ N′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* N′ ]
    Σ[ W′ ∈ World (apply ξ Δ) (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ ξ ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N ⊑ N′ ∶ q)

-- SimBack's first disjunct (SimBackDef), for this relation
SimBackConcl : ∀ {Δ Δ′ N′ ξ′} {M′ : Term} → World Δ Δ′ → Term
  → Δ′ ⊢ M′ -→ N′ ∣ ξ′ → (A A′ : Ty) → Set
SimBackConcl {Δ} {Δ′} {N′} {ξ′} W M st′ A A′ =
  ∃[ N₂ ] ∃[ N₂′ ] Σ[ r ∈ Δ ⊢ M -→* N₂ ]
    Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
    Σ[ W′ ∈ World (applyˢ (allocs r) Δ)
                  (applyˢ (allocs (st′ then r″)) Δ′) ]
      (W ⟿[ allocs r ∣ allocs (st′ then r″) ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N₂ ⊑ N₂′ ∶ q)

-- Sim at (LK₁, RK₁) and the left's Beta: the right runs Inst, TyBeta,
-- Merge, Beta (it was `sim-false`, `simᴿ-false`)
sim-K : SimConcl Wk1 RK₁ VL ∀X⇒X (★ ⇒ ★) none
sim-K =
  RF , (st₁ then st₂ then st₃ then st₄ then done) , Wk ,
  ev-noneᴸ (ev-noneᴿ (ev-R wfᴿ-★ (ev-noneᴿ (ev-noneᴿ ev-done)))) ,
  Wk-wf , ∀id⊑★ Wk , VL⊑RF

-- SimBack at (LK₁, RK₁) and the right's Inst: the right continues
-- through TyBeta and Merge, the left waits
simBack-K-inst : SimBackConcl Wk1 LK₁ st₁ ∀X⇒X (★ ⇒ ★)
simBack-K-inst =
  LK₁ , RK₄ , done , (st₂ then st₃ then done) , Wk ,
  ev-noneᴿ (ev-R wfᴿ-★ (ev-noneᴿ ev-done)) , Wk-wf , _ , lk₁⊑rk₄

-- SimBack at (LK₁, RK₄) and the right's Beta: the left's Beta
simBack-K-beta : SimBackConcl Wk LK₁ st₄ ∀X⇒X (★ ⇒ ★)
simBack-K-beta =
  VL , RF , (stL then done) , done , Wk ,
  ev-noneᴸ (ev-noneᴿ ev-done) , Wk-wf , ∀id⊑★ Wk , VL⊑RF

-- DGG part 1 on the initial pair (it was `dgg1-false`, `dgg1ᴿ-false`)
dgg1-K :
  ∃[ V′ ] Σ[ r′ ∈ empty ⊢ RK -→* V′ ] Value V′
    × Σ[ W′ ∈ World ΔL (applyˢ (allocs r′) empty) ]
        Σ[ q ∈ ∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ V′ ∶ q)
dgg1-K =
  RF , (st₀ then st₁ then st₂ then st₃ then st₄ then done) , vRF ,
  Wk , ∀id⊑★ Wk , VL⊑RF

------------------------------------------------------------------------
-- 4. K2: the left's later TyBeta, after the right merged
------------------------------------------------------------------------

--   L  (λf:∀X.X→X. f[ℕ]) (K[ℕ])
--   R  (λf:★→★.    f)    (K[ℕ]⟨inst⟩)        (= RK)
LK2 : Term
LK2 = (ƛ ∀X⇒X ∙ (ν `ℕ · ` 0 ⟨ revX ⟩)) · (ν `ℕ · KK ⟨ cK ⟩)

LK2-⊢ : empty ∣ [] ⊢ LK2 ⦂ `ℕ ⇒ `ℕ
LK2-⊢ = tc

-- the left's states (pinned to the evaluator): TyBeta, Beta, TyBeta,
-- Merge.  After its TyBeta the left is literally the right's pre-Merge
-- argument, and after its Merge the right's merged boundary Bm.
LK2₁ LK2₂ LK2₃ : Term
LK2₁ = (ƛ ∀X⇒X ∙ (ν `ℕ · ` 0 ⟨ revX ⟩)) · VL
LK2₂ = ν `ℕ · VL ⟨ revX ⟩
LK2₃ = Nk ⟪ Θ₀ , revX ⟫

LK2-states : evalTerms 20 LK2-⊢ ≡ LK2 ∷ LK2₁ ∷ LK2₂ ∷ LK2₃ ∷ Bm ∷ []
LK2-states = refl

-- the left contexts: after the source TyBeta (ΔL) and the second (ΔL2)
ΔL2 ΔL2ᵢ ΔL2X : Ctxᵗ
ΔL2  = allocate `ℕ ΔL
ΔL2ᵢ = reps ΔL2 ∣ (0 ∷ [])
ΔL2X = reps ΔL2 ∣ (0 ∷ 1 ∷ [])

ΔRX′ : Ctxᵗ
ΔRX′ = reps ΔRk ∣ (0 ∷ 1 ∷ [])

-- (LK2₁, RK₄) and (LK2₂, RF) at Wk: the left's ν over ∀⊑⟪+⟫ᴹ
νL2-ty : NuTy ΔL `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
νL2-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = ΔL} {M = LK2₂})))

lk2₂⊑rf : Wk ∣ [] ⊢ LK2₂ ⊑ RF ∶ ℕ⇒ℕ⊑★⇒★ Wk
lk2₂⊑rf = ν⊑ VL⊑RF ℕ⊑★ νL2-ty (ℕ⇒ℕ⊑★⇒★ Wk)

lk2₁⊑rk₄ : Wk ∣ [] ⊢ LK2₁ ⊑ RK₄ ∶ ℕ⇒ℕ⊑★⇒★ Wk
lk2₁⊑rk₄ =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf
        (ν⊑ (x⊑x Zʷ) ℕ⊑★ νL2-ty (ℕ⇒ℕ⊑★⇒★ Wk)))
      VL⊑RF

-- the left's TyBeta catches up (ev-L⇔): its new rep. var 0 (ℕ) is
-- paired with the Inst's β = 0 (★); αᴸ, αᴿ stay paired (now (1, 1))
Wk2 : World ΔL2 ΔRk
Wk2 = world [] []↪ []↪ ((0 , 0) ∷ (1 , 1) ∷ []) []

agree2 : ∀ {Δ Δ′} {W : World Δ Δ′} {α β}
  → (reps Δ ≡ (bindR `ℕ ∷ bindR `ℕ ∷ []))
  → (reps Δ′ ≡ (bindR ★ ∷ bindR `ℕ ∷ []))
  → ((0 , 0) ∷ (1 , 1) ∷ []) ∋ᵨ α ⇔ β → Agree W α β
agree2 refl refl here⇔ = rep-rep r-here r-here (ι⊑★ base-ℕ)
agree2 refl refl (there⇔ here⇔) =
  rep-rep (r-there r-here) (r-there r-here) (ι⊑ι base-ℕ)
agree2 refl refl (there⇔ (there⇔ ()))

ev2 : Wk ⟿[ new `ℕ ∷ [] ∣ [] ] Wk2
ev2 = ev-L⇔ wfᴿ-ℕ r-here (agree2 refl refl here⇔) ev-done

Wk2-wf : WfWorld Wk2
Wk2-wf = wf-world joint[] agree (λ ()) (λ _ ())
  where
  agree : ∀ {α β} → Paired Wk2 α β → Agree Wk2 α β
  agree (inj₁ x) = agree2 refl refl x
  agree (inj₂ ())

-- the pair after the left's TyBeta: the left boundary `+Y^γ` over the
-- left-only `+X^αᴸ`, against the right's merged `+Y^β, +X^αᴿ`
--   outer interior Wo: left name 0 (γ) joins right name 0 (β); right
--     name 1 (αᴿ) is right-only;
--   inner interior Wi (left-only `+X^αᴸ`): left name 1 (αᴸ) joins
--     right name 1 (αᴿ), through the global pair (1, 1).
Wo : World ΔL2ᵢ ΔRX′
Wo = world (X⊑X ∷ X⊑X ∷ []) (keep (skip []↪)) (keep (keep []↪))
       ((0 , 0) ∷ (1 , 1) ∷ []) []

Wi : World ΔL2X ΔRX′
Wi = world (X⊑X ∷ X⊑X ∷ []) (keep (keep []↪)) (keep (keep []↪))
       ((0 , 0) ∷ (1 , 1) ∷ []) []

int-Θ₀ : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ⁱ Θ₀ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ []))
int-Θ₀ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

int-Θ₂ : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ⁱ Θ₂ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
int-Θ₂ = interior
  (changes∷ (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))
    (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

int-ΘX : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ⁱ ΘX ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
int-ΘX = interior (changes∷ changes[]
  (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

conv-Θ₀ : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ᶜ Θ₀ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ []))
conv-Θ₀ = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)

conv-Θ₂ : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ᶜ Θ₂ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
conv-Θ₂ = conversion
  (conv-bind (_ , there here)
    (conv-bind (_ , here) conv[] fresh[] ins-here)
    (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

Wo-int : Interior Wk2 Θ₀ Θ₂ Wo
Wo-int = record
  { int-left   = int-Θ₀
  ; int-right  = int-Θ₂
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ
      { (_ , here) () _ ; (_ , there here) () _
      ; (_ , there (there ())) _ _ }
  }

Wo-wf : WfWorld Wo
Wo-wf = wf-world (both (inj₁ here⇔) (right-only joint[])) agree uniqᴸ uniqᴿ
  where
  agree : ∀ {α β} → Paired Wo α β → Agree Wo α β
  agree (inj₁ x) = agree2 refl refl x
  agree (inj₂ ())
  uniqᴸ : NamedUniqueᴸ Wo
  uniqᴸ (_ , here) (_ , here) _ _ _ = refl
  uniqᴸ (_ , there ()) _ _ _ _
  uniqᴸ (_ , here) (_ , there ()) _ _ _
  uniqᴿ : NamedUniqueᴿ Wo
  uniqᴿ _ _ _ (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴿ _ _ _ (inj₁ (there⇔ here⇔)) (inj₁ (there⇔ here⇔)) = refl
  uniqᴿ _ _ _ (inj₁ (there⇔ (there⇔ ()))) _
  uniqᴿ _ _ _ _ (inj₁ (there⇔ (there⇔ ())))
  uniqᴿ _ _ _ (inj₂ ()) _
  uniqᴿ _ _ _ _ (inj₂ ())

Wi-int : Interior Wo ΘX [] Wi
Wi-int = record
  { int-left   = int-ΘX
  ; int-right  = interior changes[]
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ
      { (_ , here) (_ , here) refl refl → (λ _ → refl) , (λ _ → refl)
      ; (_ , here) (_ , there here) refl refl → (λ ()) , (λ ())
      ; (_ , here) (_ , there (there ())) _ _
      ; (_ , there here) _ () _
      ; (_ , there (there ())) _ _ _
      }
  ; join-fresh = λ
      { here here (inj₁ ()) ; here here (inj₂ ())
      ; here (there here) (inj₁ ()) ; here (there here) (inj₂ ())
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
      ; (there here) (there here) _ →
          (λ _ → inj₁ (there⇔ here⇔)) , (λ _ → refl)
      ; _ (there (there ())) _
      ; (there (there ())) _ _
      }
  ; mark-left  = λ
      { (_ , here) refl x → x
      ; (_ , there here) () _
      ; (_ , there (there ())) _ _
      }
  ; mark-right = λ
      { (_ , here) refl x → x
      ; (_ , there here) refl x → x
      ; (_ , there (there ())) _ _
      }
  }

Wi-wf : WfWorld Wi
Wi-wf = wf-world (both (inj₁ here⇔) (both (inj₁ (there⇔ here⇔)) joint[]))
  agree uniqᴸ uniqᴿ
  where
  agree : ∀ {α β} → Paired Wi α β → Agree Wi α β
  agree (inj₁ x) = agree2 refl refl x
  agree (inj₂ ())
  uniqᴸ : NamedUniqueᴸ Wi
  uniqᴸ _ _ _ (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴸ _ _ _ (inj₁ (there⇔ here⇔)) (inj₁ (there⇔ here⇔)) = refl
  uniqᴸ _ _ _ (inj₁ (there⇔ (there⇔ ()))) _
  uniqᴸ _ _ _ _ (inj₁ (there⇔ (there⇔ ())))
  uniqᴸ _ _ _ (inj₂ ()) _
  uniqᴸ _ _ _ _ (inj₂ ())
  uniqᴿ : NamedUniqueᴿ Wi
  uniqᴿ _ _ _ (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴿ _ _ _ (inj₁ (there⇔ here⇔)) (inj₁ (there⇔ here⇔)) = refl
  uniqᴿ _ _ _ (inj₁ (there⇔ (there⇔ ()))) _
  uniqᴿ _ _ _ _ (inj₁ (there⇔ (there⇔ ())))
  uniqᴿ _ _ _ (inj₂ ()) _
  uniqᴿ _ _ _ _ (inj₂ ())

-- the left's inner boundary `+X^αᴸ`, typed at the left interior
bNk2 : BdyTy ΔL2ᵢ ΘX ΔL2X (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
bNk2 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL2ᵢ} {M = Nk}))))

-- the left boundary over it, and the right's merged one
bL2 : BdyTy ΔL2 Θ₀ ΔL2ᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
bL2 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL2} {M = LK2₃}))))

-- the two outer conversions, compared in their conversion contexts:
-- name 0 (γ on the left, β on the right) joins, through (0, 0)
Wco : World ΔL2ᵢ ΔRX′
Wco = Wo

Wco-conv : ConversionInterior Wk2 Θ₀ Θ₂ Wco
Wco-conv = record
  { conv-left       = conv-Θ₀
  ; conv-right      = conv-Θ₂
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ { _ () _ }
  }

open import examples.TermImprecisionExamples using (revX⊑revX)

-- THE PAIR AFTER THE LEFT'S TyBeta (left before its Merge)
lk2₃⊑rf : Wk2 ∣ [] ⊢ LK2₃ ⊑ RF ∶ ℕ⇒ℕ⊑★⇒★ Wk2
lk2₃⊑rf =
  ⊑cast
    (⟪⟫⊑⟪⟫ Wo-int Wo-wf
      (⟪⟫⊑ Wi-int Wi-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bNk2
        (⇒⊑⇒ X⊑X X⊑X))
      bL2 bBm (Wco , Wco-conv , revX⊑revX refl) (ℕ⇒ℕ⊑★⇒★ Wk2))
    id★↦ᴿk-ty (ℕ⇒ℕ⊑★⇒★ Wk2)

-- THE PAIR AFTER THE LEFT'S MERGE: both sides `+Y, +X` over λx:Y.x
Wm-int : Interior Wk2 Θ₂ Θ₂ Wi
Wm-int = record
  { int-left   = int-Θ₂
  ; int-right  = int-Θ₂
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ
      { (_ , here) _ () _ ; (_ , there here) _ () _
      ; (_ , there (there ())) _ _ _ }
  ; join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
      ; (there here) (there here) _ →
          (λ _ → inj₁ (there⇔ here⇔)) , (λ _ → refl)
      ; _ (there (there ())) _
      ; (there (there ())) _ _
      }
  ; mark-left  = λ
      { (_ , here) () _ ; (_ , there here) () _
      ; (_ , there (there ())) _ _ }
  ; mark-right = λ
      { (_ , here) () _ ; (_ , there here) () _
      ; (_ , there (there ())) _ _ }
  }

Wm-conv : ConversionInterior Wk2 Θ₂ Θ₂ Wi
Wm-conv = record
  { conv-left       = conv-Θ₂
  ; conv-right      = conv-Θ₂
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
      ; (there here) (there here) _ →
          (λ _ → inj₁ (there⇔ here⇔)) , (λ _ → refl)
      ; _ (there (there ())) _
      ; (there (there ())) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ { _ () _ }
  }

bBmL : BdyTy ΔL2 Θ₂ ΔL2X (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
bBmL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL2} {M = Bm}))))

bm⊑rf : Wk2 ∣ [] ⊢ Bm ⊑ RF ∶ ℕ⇒ℕ⊑★⇒★ Wk2
bm⊑rf =
  ⊑cast
    (⟪⟫⊑⟪⟫ Wm-int Wi-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
      bBmL bBm (Wi , Wm-conv , revX⊑revX refl) (ℕ⇒ℕ⊑★⇒★ Wk2))
    id★↦ᴿk-ty (ℕ⇒ℕ⊑★⇒★ Wk2)

-- the left's steps, and Sim at those two pairs: the right (a value)
-- does not move
stL2₂ : ΔL ⊢ LK2₂ -→ LK2₃ ∣ new `ℕ
stL2₂ = R.justStep refl

stL2₃ : ΔL2 ⊢ LK2₃ -→ Bm ∣ none
stL2₃ = R.justStep refl

sim-K2-tyBeta : SimConcl Wk RF LK2₃ (`ℕ ⇒ `ℕ) (★ ⇒ ★) (new `ℕ)
sim-K2-tyBeta = RF , done , Wk2 , ev2 , Wk2-wf , _ , lk2₃⊑rf

sim-K2-merge : SimConcl Wk2 RF Bm (`ℕ ⇒ `ℕ) (★ ⇒ ★) none
sim-K2-merge = RF , done , Wk2 , ev-noneᴸ ev-done , Wk2-wf , _ , bm⊑rf

-- DGG part 1 on K2: the two final values are related
LK2-run : empty ⊢ LK2 -→* Bm
LK2-run = R.justStep refl then R.justStep refl then stL2₂ then stL2₃ then done

dgg1-K2 :
  Σ[ r′ ∈ empty ⊢ RK -→* RF ] Value RF
    × Σ[ W′ ∈ World (applyˢ (allocs LK2-run) empty)
                    (applyˢ (allocs r′) empty) ]
        Σ[ q ∈ (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ Bm ⊑ RF ∶ q)
dgg1-K2 =
  (st₀ then st₁ then st₂ then st₃ then st₄ then done) , vRF ,
  Wk2 , ℕ⇒ℕ⊑★⇒★ Wk2 , bm⊑rf

------------------------------------------------------------------------
-- 3. Question 2: the un-merge is a function
------------------------------------------------------------------------

-- C18's second Inst (CambridgeExamples): the inner conversion
-- `−X → (id(Y) → +X)` (X is name 1, Y name 0), the Inst entry's
-- `reveal 0 (★ → (Y → ★)) = id(★) → (−Y → id(★))`, and the merged
-- `−X → (−Y → +X)` (all three as in the rendered C18 run)
A18 : Ty
c18 c18ᴹ : Conv
A18  = ★ ⇒ (` 0 ⇒ ★)
c18  = ⌞ tail (seal 1) ↦ ⌞ ⌞ id (` 0) ⌟ ↦ unseal 1 ⌟ ⌟
c18ᴹ = ⌞ tail (seal 1) ↦ ⌞ tail (seal 0) ↦ unseal 1 ⌟ ⌟

merge-C18 : (Δ⋉K ⊢ c18 ⨟ reveal 0 A18) ≡ c18ᴹ
merge-C18 = refl

unmerge-C18 : (Δ⋉K ⊢ c18ᴹ ⨟ conceal 0 A18) ≡ c18
unmerge-C18 = refl

-- a ∀ in the Inst body (the Inst name is 1 under the binder)
A∀ : Ty
c∀ c∀ᴹ : Conv
A∀  = `∀ (` 0 ⇒ ` 1)
c∀  = ⌞ `∀ ⌞ ⌞ id (` 0) ⌟ ↦ ⌞ id (` 1) ⌟ ⌟ ⌟
c∀ᴹ = ⌞ `∀ ⌞ ⌞ id (` 0) ⌟ ↦ unseal 1 ⌟ ⌟

merge-∀ : (Δ⋉K ⊢ c∀ ⨟ reveal 0 A∀) ≡ c∀ᴹ
merge-∀ = refl

unmerge-∀ : (Δ⋉K ⊢ c∀ᴹ ⨟ conceal 0 A∀) ≡ c∀
unmerge-∀ = refl

-- an unseal chain at a covariant Inst position (an inner name whose
-- representation is the Inst name), and a seal chain at a
-- contravariant one: the smart constructors cancel and re-tighten
Aᵘ Aˢ : Ty
cᵘ cᵘᴹ cˢ cˢᴹ : Conv
Aᵘ  = ★ ⇒ ` 0
cᵘ  = ⌞ ⌞ id ★ ⌟ ↦ unseal 2 ⌟
cᵘᴹ = ⌞ ⌞ id ★ ⌟ ↦ (unseal 2 ⨾ unseal 0) ⌟
Aˢ  = ` 0 ⇒ ★
cˢ  = ⌞ tail (seal 2) ↦ ⌞ id ★ ⌟ ⌟
cˢᴹ = ⌞ tail (seal 0 ⨾seal 2) ↦ ⌞ id ★ ⌟ ⌟

merge-u : (Δ⋉K ⊢ cᵘ ⨟ reveal 0 Aᵘ) ≡ cᵘᴹ
merge-u = refl

unmerge-u : (Δ⋉K ⊢ cᵘᴹ ⨟ conceal 0 Aᵘ) ≡ cᵘ
unmerge-u = refl

merge-s : (Δ⋉K ⊢ cˢ ⨟ reveal 0 Aˢ) ≡ cˢᴹ
merge-s = refl

unmerge-s : (Δ⋉K ⊢ cˢᴹ ⨟ conceal 0 Aˢ) ≡ cˢ
unmerge-s = refl

-- THE GENERAL LAW (statement only).  The inner conversion c was typed
-- with the Inst name abstract (it is the body s of the right value's
-- `∀ s`, read by inst-⟪⟫), so it seals and unseals no name 0; then
-- conceal undoes reveal after it.  It makes ∀⊑⟪+⟫ᴹ's premise the
-- un-merge of what the right's Merge composed.
RevealCancel : Set
RevealCancel = ∀ {Γ Δ c Cᵢ A′}
  → underΛ Γ ⊢ c ∶ Cᵢ ⇝ A′
  → (Δ ⊢ (Δ ⊢ c ⨟ reveal 0 A′) ⨟ conceal 0 A′) ≡ c

------------------------------------------------------------------------
-- 5. Question 3: the new lemma statements (statements only)
------------------------------------------------------------------------

-- The Inst cases (CatchupCast's Inst, SimBack on a right Inst): the
-- right's Inst boundary runs to a VALUE related to the left ∀-value.
-- Replaces RestrictedForallBoundary's InstSync: no `¬ ForallBdy V₀′`,
-- no `Simple U′` in the conclusion; the derivation ends in ∀⊑⟪+⟫
-- (V₀′ not a ∀-boundary value) or ∀⊑⟪+⟫ᴹ (it is: Merge, possibly
-- after the inner value's own Merges).
InstSyncᴬ : Set
InstSyncᴬ = ∀ {Δ Δ′} {W : World Δ Δ′} {V V₀′ N N₀′ C C′}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′                       -- binders match
  → NonVar C → 0 ∈ᵗ C
  → Value V → Value V₀′ → InstX V N → InstX V₀′ N₀′
  → W ∣ [] ⊢ V ⊑ V₀′ ∶ r
  → ∃[ U′ ] Σ[ ρ ∈ allocate ★ Δ′ ⊢ N₀′ ⟪ bind 0 0 ∷ [] , reveal 0 C′ ⟫
                     -→* U′ ]
      Value U′
      × Σ[ W′ ∈ World Δ (applyˢ (allocs ρ) (allocate ★ Δ′)) ]
          (allocᴿ ★ W ⟿[ [] ∣ allocs ρ ] W′) × WfWorld W′
          × ∃[ B′ ] Σ[ q ∈ `∀ C ⊑ᵂ⟨ W′ ⟩ B′ ] (W′ ∣ [] ⊢ V ⊑ U′ ∶ q)

-- The left's later TyBeta against ∀⊑⟪+⟫ᴹ (K2, `lk2₃⊑rf`): after the
-- ev-L⇔ step the old ∀⊑⟪+⟫ recipe (L3c) gives ⟪⟫⊑⟪⟫ with the right
-- boundary `bind 0 β` over `U′ ⟪ Θ₁′ , t₁′ ⟫`; this lemma moves the
-- right's inner boundary out into the outer right boundary.  It is
-- the term-level half of SimBack's right-Merge case under ⟪⟫⊑⟪⟫ (the
-- conversion-level half is MergeImpR, drafts/MergeImpDef.agda), so it
-- is needed anyway.
RightMergeInterior : Set
RightMergeInterior = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ₁′ Θ₂′ M U′ t₁′ A A′}
    {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′}
  → WfWorld W → Interior W Θ Θ₂′ Wᵢ → WfWorld Wᵢ
  → Simple U′
  → Wᵢ ∣ [] ⊢ M ⊑ U′ ⟪ Θ₁′ , t₁′ ⟫ ∶ r
  → ∃[ Δ″ ] Σ[ Wₘ ∈ World Δᵢ Δ″ ]
      Interior W Θ (Θ₁′ ++ Θ₂′) Wₘ × WfWorld Wₘ
      × ∃[ A″ ] Σ[ r′ ∈ A ⊑ᵂ⟨ Wₘ ⟩ A″ ] (Wₘ ∣ [] ⊢ M ⊑ U′ ∶ r′)
