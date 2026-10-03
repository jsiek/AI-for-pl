module proof.DGG.notes.RestrictedForallBoundary where

-- File Charter:
--   * THE PROPOSAL CHECKED HERE: keep ∀⊑⟪+⟫ but restrict its right
--     interior to a SIMPLE value (a syntactic premise `Simple V′`).
--     Findings in RestrictedForallBoundary.md.  NOT a Def module, not
--     imported by All.agda; nothing outside proof/DGG/notes is edited.
--   * §1 a LOCAL COPY of the relation, `_∣_⊢_⊑_∶_`, with the same
--     constructor names as TermImprecision; the only difference is
--     the premise `Simple V′` of ∀⊑⟪+⟫.  `forget` maps it into
--     TermImprecision's relation (the restricted relation is a
--     subrelation), so every non-derivability fact proved for
--     TermImprecision also holds for the restricted relation.
--   * §2 the blocks that used ∀⊑⟪+⟫, re-derived with the restricted
--     rule: P3 (= Ch), Cg, C2, C12, L3c (before and after the left's
--     TyBeta), L3d (before and after the second TyBeta), and R2c
--     after the right's Merge.  Each right interior is simple.  The
--     R2c pair BEFORE the Merge is no longer an instance of ∀⊑⟪+⟫:
--     its interior is not simple (`R2c₄-interior-¬simple`).
--   * §3 A COUNTEREXAMPLE TO THE PROPOSAL, and to the current rule:
--     the right's Inst on a ∀-BOUNDARY value.  The interior after the
--     TyBeta is a boundary value, never a simple one; the next step
--     merges the Inst boundary into it.  After the Merge the right
--     boundary has two entries and no rule relates it to the left
--     ∀-boundary value (`final-unrelated`).  Consequences, all proved:
--     `sim-false : Sim → ⊥` (current relation), `simᴿ-false` (the same
--     for the restricted relation), `simBack-false : SimBack → ⊥`
--     (current relation: the pre-Merge pair is a ∀⊑⟪+⟫ instance with a
--     non-simple interior), and, from the related initial pair
--     `lk⊑rk`, `dgg1-false`/`dgg1ᴿ-false`: DGG part 1 (design.md §9.7)
--     fails on this pair for both relations.  §3g: the premises of a
--     candidate repair (∀⊑⟪+⟫ over a MERGED right boundary) hold on
--     the final pair (sketch; the rule is not added).
--   * §4 the lemma the Inst cases would need (statement only), and the
--     binder-matching remark.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; head; drop)
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
open import proof.ImprecisionWorld using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[])
open import ConversionImprecision
import TermImprecision as TI
open TI
  using (Lit; lit-$; lit-true; lit-false; CastTy; cast-ty; NuTy; BdyTy;
         bdy-ty; NuConversionImp; BdyConversionImp; ⟪⟫-inv; cast-inv; ν-inv)
open import proof.DGG.SimDef using (Sim)
open import proof.DGG.SimBackDef using (SimBack)
open import proof.DGG.RunFrames using (value-run≡)
open import proof.TypeSafety.Determinism using (det)
open import proof.TypeSafety.PreservationSupport using (alloc-wf)
open import proof.Ctx using (wf-empty)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; ev-L⇔; ev-noneᴿ; ev-done; applyˢ; allocs)
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms; step; StepResult)
open import examples.CambridgeExamples using (I; instI; genI; C2-L; C12-L)
open import examples.ImprecisionExamples using (L1)
open import examples.TermImprecisionExamples
  using (idX; revX; ℕ⊑★; 5⟨ℕ!⟩; Θ₀; L1′; ΔL; ΔR; ΔLᵢ; ΔRᵢ; W₁; Wᵢ₁; Wᵢ₁-int;
         Wᵢ₁-wf; bL-ty; bR-ty; bLR-conv; revX⊑revX; νL-ty; W₃; R3′; int₀;
         conv₀; Wν; Wν-conv)
open import examples.TermImprecisionRebaseExamples
  using (id★↦; id★→; tagX↦; ∀id⊑★; ∀id⊑∀id; ★⇒★; ℕ⇒ℕ; ℕ⇒ℕ⊑★⇒★;
         id★→⊑id★→; X⇒X⊑★⇒★; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty; id★↦ᴿ-ty; ΛidX-⊢;
         Cg-R₂; Wg⁺; Wg⁻-int; Wg⁻-wf; I★genI-⊢; C2-L-ν-ty; W2⁺; W2⁻-int;
         W2⁻-wf; W2⁺-conv; I★⁻ᴸ-ty; tagᴸ-ty; C12-R₂; C12-ν₂-ty; genIᴿ-ty;
         Wν₂; Wν₂-conv)
open import proof.DGG.notes.ForallBoundaryFixes
  using (B⟨id⟩; L3c₁; L3c₂; R3c₃; W₁-wf; l3c-evolve; post-premise-wf;
         νLₗ-ty; W₂d; Wᵢ₂d-int; Wᵢ₂d-wf; bL₂-ty; bLR₂-conv; l3d-evolve;
         second-paired-wf; L2c₂; R2c₄; R2c₅; Nu; Bin; N; N₀; vV2; V2-⊢;
         instV2; W4; Pw; Iu′; Pu′; Pu′-wf; Ib′; Pb-wf; bBᴸ; bMᴿ; Pc′; Ibc′;
         bUᴸ; tagNᴸ; tagN₀ᴿ; bOut₅; id★↦ᴿ₂-ty; shiftβ)

private
  variable
    Δ Δ′ : Ctxᵗ

------------------------------------------------------------------------
-- 1. The restricted relation (a local copy)
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

  -- THE RESTRICTED RULE: as TermImprecision's, plus `Simple V′`
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

-- the restricted relation is a subrelation of TermImprecision's
forget : ∀ {W : World Δ Δ′} {γ : CtxImp W} {M M′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶ p → W TI.∣ γ ⊢ M ⊑ M′ ∶ p
forget (x⊑x x) = TI.x⊑x x
forget (κ⊑κ k p) = TI.κ⊑κ k p
forget (ƛ⊑ƛ wA wA′ d) = TI.ƛ⊑ƛ wA wA′ (forget d)
forget (·⊑· d e) = TI.·⊑· (forget d) (forget e)
forget (blame⊑ wA ⊢M p) = TI.blame⊑ wA ⊢M p
forget (cast⊑cast d c c′ q) = TI.cast⊑cast (forget d) c c′ q
forget (cast⊑ d c q) = TI.cast⊑ (forget d) c q
forget (⊑cast d c′ q) = TI.⊑cast (forget d) c′ q
forget (Λ⊑Λ l v v′ d q) = TI.Λ⊑Λ l v v′ (forget d) q
forget (Λ⊑ nv occ l v d q) = TI.Λ⊑ nv occ l v (forget d) q
forget (∀⊑⟪+⟫ nv occ v ⊢V i d s hβ b q) =
  TI.∀⊑⟪+⟫ nv occ v ⊢V i (forget d) hβ b q
forget (ν⊑ν d a n n′ nc q) = TI.ν⊑ν (forget d) a n n′ nc q
forget (ν⊑ d a n q) = TI.ν⊑ (forget d) a n q
forget (⟪⟫⊑⟪⟫ int wf d b b′ bc q) = TI.⟪⟫⊑⟪⟫ int wf (forget d) b b′ bc q
forget (⟪⟫⊑ int wf d b q) = TI.⟪⟫⊑ int wf (forget d) b q
forget (⊑⟪⟫ int wf d b′ q) = TI.⊑⟪⟫ int wf (forget d) b′ q

------------------------------------------------------------------------
-- 2. The blocks that used ∀⊑⟪+⟫, with the restricted rule
------------------------------------------------------------------------

-- the right interiors at the synchronization points
idX-simple : Simple idX
idX-simple = S-ƛ

five⊑ : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ : CtxImp W}
  → W ∣ γ ⊢ $ 5 ⊑ 5⟨ℕ!⟩ ∶ ℕ⊑★
five⊑ = ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

-- P3 = Ch (block X0): the right's interior after Inst, TyBeta is λx:X.x
p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
p3-inst =
  ·⊑· (ν⊑ (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
                    (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
                    (inst-Λ (V-simple S-ƛ))
                    (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) idX-simple
                    r-here bR-ty (∀id⊑★ W₃))
                 id★↦ᴿ-ty (∀id⊑★ W₃))
          ℕ⊑★ νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

-- Cg (block X0): the interior is the gen wrapper over the crossed body,
-- `([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩`: an inert cast over
-- a boundary value, so simple, right after the TyBeta
gen-wrapper-simple : ∀ {μ} → Simple
  (((ƛ ★ ∙ ` 0) ⟪ unbind 0 0 ∷ [] , id★→ ⟫) ⟨ μ ∣ tagX↦ ⟩)
gen-wrapper-simple = S-cast (V-⟪⟫ S-ƛ I-fun) I-↦

cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ℕ⊑★
cg-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (∀⊑⟪+⟫ {m = X⊑★} nv-⇒ (∈-⇒ˡ ∈-var)
          (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
          (inst-Λ (V-simple S-ƛ))
          (⊑cast
            (⊑⟪⟫ Wg⁻-int Wg⁻-wf
              (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
              I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = Wg⁺} here))
            tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
          gen-wrapper-simple
          r-here Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

-- C2 (block X0): the same right interior, against a left gen-cast value
c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ℕ⊑★
c2-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
          (V-simple (S-cast (V-simple S-ƛ) I-gen))
          I★genI-⊢ (inst-gen (V-simple S-ƛ))
          (cast⊑cast
            (⟪⟫⊑⟪⟫ W2⁻-int W2⁻-wf
              (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ))
              I★⁻ᴸ-ty I★⁻ᴿ-ty
              (W2⁺ , W2⁺-conv , id★→⊑id★→) (★⇒★ W2⁺))
            tagᴸ-ty tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
          gen-wrapper-simple
          r-here Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

-- C12 (block X0): interior λx:X.x
c12-x0 : W₃ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
c12-x0 =
  ·⊑·
    (ν⊑ν
      (⊑cast
        (⊑cast
          (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
            (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
            (inst-Λ (V-simple S-ƛ))
            (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
            idX-simple r-here bR-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        genIᴿ-ty (∀id⊑∀id W₃))
      (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , revX⊑revX refl)
      (ℕ⇒ℕ W₃))
    (κ⊑κ lit-$ (ι⊑ι base-ℕ))

-- L3c: copy 2 of the duplicated Inst boundary, interior λx:X.x
copy2 : ∀ {Ξ} {W : World (Ξ ∣ []) ΔR}
  → (Ξ ∣ []) ∣ `ℕ ∷ [] ⊢ I ⦂ `∀ (` 0 ⇒ ` 0)
  → W ∣ ctx-imp `ℕ ★ ℕ⊑★ ∷ [] ⊢ I ⊑ B⟨id⟩ ∶ ∀id⊑★ W
copy2 {W = W} ⊢I =
  ⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
           (V-simple (S-Λ (V-simple S-ƛ))) ⊢I (inst-Λ (V-simple S-ƛ))
           (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) idX-simple
           r-here bR-ty (∀id⊑★ W))
        id★↦ᴿ-ty (∀id⊑★ W)

-- before the left's TyBeta of copy 1 (world W₃) ...
l3c-pre : W₃ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ ∀id⊑★ W₃
l3c-pre = ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 tc)) p3-inst

-- ... and after it (world W₁, l3c-evolve; premise world well formed,
-- post-premise-wf)
l3c-post : W₁ ∣ [] ⊢ L3c₂ ⊑ R3c₃ ∶ ∀id⊑★ W₁
l3c-post =
  ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 tc))
    (·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
          (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
          bL-ty bR-ty bLR-conv (ℕ⇒ℕ⊑★⇒★ W₁))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ W₁))
      five⊑)

-- L3d: the second copy, before (W₁) and after (W₂d, l3d-evolve) the
-- left's second TyBeta
l3d-before : W₁ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
l3d-before =
  ·⊑· (ν⊑ (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
                    (V-simple (S-Λ (V-simple S-ƛ))) tc
                    (inst-Λ (V-simple S-ƛ))
                    (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) idX-simple
                    r-here bR-ty (∀id⊑★ W₁))
                 id★↦ᴿ-ty (∀id⊑★ W₁))
          ℕ⊑★ νLₗ-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

l3d-after : W₂d ∣ [] ⊢ L1′ ⊑ R3′ ∶ ℕ⊑★
l3d-after =
  ·⊑·
    (⊑cast
      (⟪⟫⊑⟪⟫ Wᵢ₂d-int Wᵢ₂d-wf
        (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
        bL₂-ty bR-ty bLR₂-conv (ℕ⇒ℕ⊑★⇒★ W₂d))
      id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ W₂d))
    five⊑

-- R2c (L2c/R2c, ForallBoundaryFixes §8).  At the right's TyBeta (R2c₄)
-- the interior is `([−Y^β] ([+X^α] λx:X.x ⟨…⟩) ⟨…⟩)⟨Y! → Y?ℓ0⟩`, a
-- cast over a Merge redex: NOT simple, so R2c₄'s pair is no longer an
-- instance of ∀⊑⟪+⟫ ...
Nu-¬value : ¬ Value Nu
Nu-¬value (V-simple ())
Nu-¬value (V-⟪⟫ () _)

R2c₄-interior-¬simple : ¬ Simple N
R2c₄-interior-¬simple (S-cast v _) = Nu-¬value v

-- ... and after the right's own Merge (R2c₅) the interior is the gen
-- wrapper over a boundary value: simple.  The pair derives with the
-- restricted rule; the premise still has the left's UNMERGED
-- N = inst_Y(V2) (candidate A of ForallBoundaryFixes)
N₀-simple : Simple N₀
N₀-simple = S-cast (V-⟪⟫ S-ƛ I-fun) I-↦

N⊑N₀ : Pw ∣ [] ⊢ N ⊑ N₀ ∶ ⇒⊑⇒ X⊑X X⊑X
N⊑N₀ =
  cast⊑cast
    (⟪⟫⊑ Iu′ Pu′-wf
      (⟪⟫⊑⟪⟫ Ib′ Pb-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bBᴸ bMᴿ
        (Pc′ , Ibc′ , revX⊑revX refl) (★⇒★ Pu′))
      bUᴸ (★⇒★ Pw))
    tagNᴸ tagN₀ᴿ (⇒⊑⇒ X⊑X X⊑X)

r2c-post : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ ∀id⊑★ W4
r2c-post =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
    (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var) vV2 V2-⊢ instV2 N⊑N₀
              N₀-simple r-here bOut₅ (∀id⊑★ W4))
           id★↦ᴿ₂-ty (∀id⊑★ W4))

------------------------------------------------------------------------
-- 3. Counterexample: Inst on a ∀-boundary value
------------------------------------------------------------------------

--   L  (λf:∀X.X→X. f) (K[ℕ])        K = ΛY.ΛX.λx:X.x
--   R  (λf:★→★.    f) (K[ℕ])        (the argument cast by instI)
-- K[ℕ] is a ∀-BOUNDARY value `[+Y^α] (ΛX.λx:X.x) ⟨∀X.(id(X) → id(X))⟩`.
-- The right's Inst on it creates an Inst boundary whose interior is a
-- boundary value; the next step merges the two boundaries.

KK : Term
KK = Λ I

cId cK : Conv
cId = ⌞ ⌞ id (` 0) ⌟ ↦ ⌞ id (` 0) ⌟ ⌟
cK  = ⌞ `∀ cId ⌟

cK-reveal : reveal 0 (`∀ (` 0 ⇒ ` 0)) ≡ cK
cK-reveal = refl

∀X⇒X : Ty
∀X⇒X = `∀ (` 0 ⇒ ` 0)

-- the left value, the Inst boundary's interior, the merged boundary
VL Nk Rarg₃ Bm RF : Term
VL    = I ⟪ Θ₀ , cK ⟫
Nk    = idX ⟪ bind 1 1 ∷ [] , cId ⟫
Rarg₃ = (Nk ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩
Bm    = idX ⟪ bind 1 1 ∷ bind 0 0 ∷ [] , revX ⟫
RF    = Bm ⟨ [] ∣ id★↦ ⟩

LK LK₁ RK RK₁ RK₂ RK₃ RK₄ : Term
LK  = (ƛ ∀X⇒X ∙ ` 0) · (ν `ℕ · KK ⟨ cK ⟩)
LK₁ = (ƛ ∀X⇒X ∙ ` 0) · VL
RK  = (ƛ (★ ⇒ ★) ∙ ` 0) · ((ν `ℕ · KK ⟨ cK ⟩) ⟨ [] ∣ instI ⟩)
RK₁ = (ƛ (★ ⇒ ★) ∙ ` 0) · (VL ⟨ [] ∣ instI ⟩)
RK₂ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((ν ★ · VL ⟨ revX ⟩) ⟨ [] ∣ id★↦ ⟩)
RK₃ = (ƛ (★ ⇒ ★) ∙ ` 0) · Rarg₃
RK₄ = (ƛ (★ ⇒ ★) ∙ ` 0) · RF

LK-⊢ : empty ∣ [] ⊢ LK ⦂ ∀X⇒X
LK-⊢ = tc

RK-⊢ : empty ∣ [] ⊢ RK ⦂ ★ ⇒ ★
RK-⊢ = tc

-- the runs (states pinned to the evaluator):
--   L: TyBeta, Beta                         (ends at VL, a value)
--   R: TyBeta, Inst, TyBeta, Merge, Beta    (ends at RF, a value)
LK-states : evalTerms 20 LK-⊢ ≡ LK ∷ LK₁ ∷ VL ∷ []
LK-states = refl

RK-states : evalTerms 20 RK-⊢ ≡ RK ∷ RK₁ ∷ RK₂ ∷ RK₃ ∷ RK₄ ∷ RF ∷ []
RK-states = refl

-- the contexts: the left after its TyBeta (α:=ℕ); the right after its
-- source TyBeta (α:=ℕ) and after the Inst's TyBeta (β:=★, rep. var 0)
ΔRk : Ctxᵗ
ΔRk = allocate ★ ΔL

wfΔL : WfCtx ΔL
wfΔL = alloc-wf wf-empty wfᴿ-ℕ

wfΔRk : WfCtx ΔRk
wfΔRk = alloc-wf wfΔL wfᴿ-★

vVL : Value VL
vVL = V-⟪⟫ (S-Λ (V-simple S-ƛ)) I-all

vRF : Value RF
vRF = V-simple (S-cast (V-⟪⟫ S-ƛ I-fun) I-↦)

-- AT THE INST'S TyBeta (RK₃) THE INTERIOR IS A BOUNDARY VALUE, NOT A
-- SIMPLE ONE: the proposal's premise fails, and it never becomes true,
-- because the next step is the Merge of the Inst boundary into it
Nk-value : Value Nk
Nk-value = V-⟪⟫ S-ƛ I-fun

Nk-¬simple : ¬ Simple Nk
Nk-¬simple ()

------------------------------------------------------------------------
-- 3a. The final pair is related by no rule (current relation)
------------------------------------------------------------------------

-- a type imprecision between two variables joins their center names
var⊑var : ∀ {μ A B x y} → μ ⊢ A ⊑ B → A ≡ ` x → B ≡ ` y → x ≡ y
var⊑var ★⊑★ () _
var⊑var (ι⊑ι base-ℕ) () _
var⊑var (ι⊑ι base-𝔹) () _
var⊑var X⊑X refl refl = refl
var⊑var (⇒⊑⇒ _ _) () _
var⊑var (∀⊑∀ _) () _
var⊑var (⇒⊑★ _ _) _ ()
var⊑var (ι⊑★ _) _ ()
var⊑var (X⊑★ _) _ ()
var⊑var (∀⊑ _ _ _) () _
var⊑var ∀★⊑★ () _
var⊑var (∀⊑★ _ _) () _
var⊑var bot-elim () _
var⊑var bot⊑★ () _

-- λx:X.x ⊑ λx:X′.x forces X and X′ to name one center name
λ-joins : ∀ {W : World Δ Δ′} {γ : CtxImp W} {A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W TI.∣ γ ⊢ idX ⊑ idX ∶ p → Joins W 0 0
λ-joins (TI.κ⊑κ () _)
λ-joins (TI.ƛ⊑ƛ {pA = pA} _ _ _) = var⊑var pA refl refl

-- Λ⊑'s left-only binder joins no right name ...
⊕ᴸ-¬joins : ∀ {W : World Δ Δ′} {b} → ¬ Joins (W ⊕ᴸ) 0 b
⊕ᴸ-¬joins ()

-- ... and its abstract rep. var is paired with nothing
shiftᴸ-¬0 : ∀ (ϱ : RepRel) {β} → ¬ (shiftᴸ ϱ ∋ᵨ 0 ⇔ β)
shiftᴸ-¬0 [] ()
shiftᴸ-¬0 ((a , b) ∷ ϱ) (there⇔ x) = shiftᴸ-¬0 ϱ x

⊕ᴸ-¬paired : ∀ {W : World Δ Δ′} {β} → ¬ Paired (W ⊕ᴸ) 0 β
⊕ᴸ-¬paired {W = W} (inj₁ x) = shiftᴸ-¬0 (ϱᵍʷ W) x
⊕ᴸ-¬paired {W = W} (inj₂ x) = shiftᴸ-¬0 (ϱˡʷ W) x

-- the merged boundary's interior name 0 is β, introduced by it
Θ₂ : Boundary
Θ₂ = bind 1 1 ∷ bind 0 0 ∷ []

Θ₂-fresh0 : Fresh Θ₂ 0
Θ₂-fresh0 = refl

Θ₂-look0 : ∀ {Γ Γᵢ} → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ → Γᵢ ∋ᵗ 0 := 0
Θ₂-look0 (interior (changes∷ (changes∷ changes[] (step-bind _ _ ins-here))
                              (step-bind _ _ (ins-there ins-here)))) = here

-- the left λ under Λ⊑'s binder, against the right's merged boundary
lam-id : ∀ {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⊕ᴸ ⟩ A′}
  → ¬ (W ⊕ᴸ TI.∣ γ ⊢ idX ⊑ idX ∶ p)
lam-id {W = W} d = ⊕ᴸ-¬joins {W = W} {b = 0} (λ-joins d)

lam-Bm : ∀ {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⊕ᴸ ⟩ A′}
  → ¬ (W ⊕ᴸ TI.∣ γ ⊢ idX ⊑ Bm ∶ p)
lam-Bm {W = W} (TI.⊑⟪⟫ int wf d b′ q) =
  ⊕ᴸ-¬paired {W = W} (proj₁ (join-fresh int here (Θ₂-look0 (int-right int))
                       (inj₂ Θ₂-fresh0))
                    (λ-joins d))

lam-RF : ∀ {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⊕ᴸ ⟩ A′}
  → ¬ (W ⊕ᴸ TI.∣ γ ⊢ idX ⊑ RF ∶ p)
lam-RF (TI.⊑cast d _ _) = lam-Bm d

-- the left Λ (left-only: the right has no Λ, and the right boundary is
-- not a single bind, so ∀⊑⟪+⟫ does not apply)
I-id : ∀ {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W TI.∣ γ ⊢ I ⊑ idX ∶ p)
I-id (TI.Λ⊑ _ _ _ _ d _) = lam-id d

I-Bm : ∀ {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W TI.∣ γ ⊢ I ⊑ Bm ∶ p)
I-Bm (TI.Λ⊑ _ _ _ _ d _) = lam-Bm d
I-Bm (TI.⊑⟪⟫ _ _ d _ _)  = I-id d

I-RF : ∀ {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W TI.∣ γ ⊢ I ⊑ RF ∶ p)
I-RF (TI.Λ⊑ _ _ _ _ d _) = lam-RF d
I-RF (TI.⊑cast d _ _)    = I-Bm d

-- the left ∀-boundary value
VL-id : ∀ {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W TI.∣ γ ⊢ VL ⊑ idX ∶ p)
VL-id (TI.⟪⟫⊑ _ _ d _ _) = I-id d

VL-Bm : ∀ {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W TI.∣ γ ⊢ VL ⊑ Bm ∶ p)
VL-Bm (TI.⟪⟫⊑⟪⟫ _ _ d _ _ _ _) = I-id d
VL-Bm (TI.⟪⟫⊑ _ _ d _ _)       = I-Bm d
VL-Bm (TI.⊑⟪⟫ _ _ d _ _)       = VL-id d

-- THE FINAL VALUES ARE UNRELATED, in any world
final-unrelated : ∀ {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W TI.∣ γ ⊢ VL ⊑ RF ∶ p)
final-unrelated (TI.⊑cast d _ _)    = VL-Bm d
final-unrelated (TI.⟪⟫⊑ _ _ d _ _) = I-RF d

-- the left value is related to no application either
lam-app : ∀ {W : World Δ Δ′} {γ A A′ L′ M′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W TI.∣ γ ⊢ idX ⊑ L′ · M′ ∶ p)
lam-app ()

I-app : ∀ {W : World Δ Δ′} {γ A A′ L′ M′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W TI.∣ γ ⊢ I ⊑ L′ · M′ ∶ p)
I-app (TI.Λ⊑ _ _ _ _ d _) = lam-app d

VL-app : ∀ {W : World Δ Δ′} {γ A A′ L′ M′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W TI.∣ γ ⊢ VL ⊑ L′ · M′ ∶ p)
VL-app (TI.⟪⟫⊑ _ _ d _ _) = I-app d

------------------------------------------------------------------------
-- 3b. The pair before the left's Beta is related (no ∀⊑⟪+⟫ needed)
------------------------------------------------------------------------

-- after both source TyBetas (α:=ℕ on each side, matched: ev-2)
Wk1 : World ΔL ΔL
Wk1 = world [] []↪ []↪ ((0 , 0) ∷ []) []

Wk1ᵢ : World ΔLᵢ ΔLᵢ
Wk1ᵢ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

Wk1-wf : WfWorld Wk1
Wk1-wf = wf-world joint[] agree (namedᴸ-≤1 Wk1 ≤1-[]) (namedᴿ-≤1 Wk1 ≤1-[])
  where
  agree : ∀ {α β} → Paired Wk1 α β → Agree Wk1 α β
  agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

Wk1ᵢ-wf : WfWorld Wk1ᵢ
Wk1ᵢ-wf = wf-world (both (inj₁ here⇔) joint[]) agree
  (namedᴸ-≤1 Wk1ᵢ ≤1-∷[]) (namedᴿ-≤1 Wk1ᵢ ≤1-∷[])
  where
  agree : ∀ {α β} → Paired Wk1ᵢ α β → Agree Wk1ᵢ α β
  agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

Wk1ᵢ-int : Interior Wk1 Θ₀ Θ₀ Wk1ᵢ
Wk1ᵢ-int = record
  { int-left   = int₀
  ; int-right  = int₀
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Wk1ᵢ-conv : ConversionInterior Wk1 Θ₀ Θ₀ Wk1ᵢ
Wk1ᵢ-conv = record
  { conv-left       = conv₀
  ; conv-right      = conv₀
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ { _ () _ }
  }

cId⊑cId : ∀ {Δ Δ′} {W : World Δ Δ′} → ` 0 ⊑ᵂ⟨ W ⟩ ` 0 → ConvImp W cId cId
cId⊑cId x = conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
  where
  i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id x))

cK⊑cK : ConvImp Wk1ᵢ cK cK
cK⊑cK = conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId X⊑X)))

bVL : BdyTy ΔL Θ₀ ΔLᵢ ∀X⇒X cK ∀X⇒X
bVL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = VL}))))

instI-ty : CastTy ΔL [] instI ∀X⇒X (★ ⇒ ★)
instI-ty =
  proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔL} {M = VL ⟨ [] ∣ instI ⟩})))

-- in the RESTRICTED relation (hence, by forget, in the current one)
lk₁⊑rk₁ : Wk1 ∣ [] ⊢ LK₁ ⊑ RK₁ ∶ ∀id⊑★ Wk1
lk₁⊑rk₁ =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk1} tf tf (x⊑x Zʷ))
    (⊑cast
      (⟪⟫⊑⟪⟫ Wk1ᵢ-int Wk1ᵢ-wf
        (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
          (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
        bVL bVL (Wk1ᵢ , Wk1ᵢ-conv , cK⊑cK) (∀id⊑∀id Wk1))
      instI-ty (∀id⊑★ Wk1))

------------------------------------------------------------------------
-- 3c. The right's runs, step by step (Determinism)
------------------------------------------------------------------------

justStep : ∀ {Δ M} {r : StepResult Δ M} → step Δ M ≡ just r
  → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
justStep {r = r} _ = proj₂ (proj₂ r)

stL : ΔL ⊢ LK₁ -→ VL ∣ none
stL = justStep refl

st₁ : ΔL ⊢ RK₁ -→ RK₂ ∣ none
st₁ = justStep refl

st₂ : ΔL ⊢ RK₂ -→ RK₃ ∣ new ★
st₂ = justStep refl

st₃ : ΔRk ⊢ RK₃ -→ RK₄ ∣ none
st₃ = justStep refl

st₄ : ΔRk ⊢ RK₄ -→ RF ∣ none
st₄ = justStep refl

-- the Merge alone, on the argument
stM : ΔRk ⊢ Rarg₃ -→ RF ∣ none
stM = justStep refl

RK₁-⊢ : ΔL ∣ [] ⊢ RK₁ ⦂ ★ ⇒ ★
RK₁-⊢ = tc

RK₂-⊢ : ΔL ∣ [] ⊢ RK₂ ⦂ ★ ⇒ ★
RK₂-⊢ = tc

RK₃-⊢ : ΔRk ∣ [] ⊢ RK₃ ⦂ ★ ⇒ ★
RK₃-⊢ = tc

RK₄-⊢ : ΔRk ∣ [] ⊢ RK₄ ⦂ ★ ⇒ ★
RK₄-⊢ = tc

-- every state the right reaches from RK₁ is an application or RF
data Ends : Term → Set where
  e-app : ∀ {L′ M′} → Ends (L′ · M′)
  e-RF  : Ends RF

runs-RK₄ : ∀ {N′} → ΔRk ⊢ RK₄ -→* N′ → Ends N′
runs-RK₄ done = e-app
runs-RK₄ (st then r) with det RK₄-⊢ st st₄
runs-RK₄ (st then r) | refl , refl with value-run≡ vRF r
runs-RK₄ (st then r) | refl , refl | refl = e-RF

runs-RK₃ : ∀ {N′} → ΔRk ⊢ RK₃ -→* N′ → Ends N′
runs-RK₃ done = e-app
runs-RK₃ (st then r) with det RK₃-⊢ st st₃
runs-RK₃ (st then r) | refl , refl = runs-RK₄ r

runs-RK₂ : ∀ {N′} → ΔL ⊢ RK₂ -→* N′ → Ends N′
runs-RK₂ done = e-app
runs-RK₂ (st then r) with det RK₂-⊢ st st₂
runs-RK₂ (st then r) | refl , refl = runs-RK₃ r

runs-RK₁ : ∀ {N′} → ΔL ⊢ RK₁ -→* N′ → Ends N′
runs-RK₁ done = e-app
runs-RK₁ (st then r) with det RK₁-⊢ st st₁
runs-RK₁ (st then r) | refl , refl = runs-RK₂ r

unrelated : ∀ {W : World Δ Δ′} {γ A A′ N′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Ends N′ → ¬ (W TI.∣ γ ⊢ VL ⊑ N′ ∶ p)
unrelated e-app = VL-app
unrelated e-RF  = final-unrelated

------------------------------------------------------------------------
-- 3d. Sim fails (current and restricted relation)
------------------------------------------------------------------------

-- the left's Beta (LK₁ → VL) cannot be matched: the right never reaches
-- a state related to VL
sim-false : Sim → ⊥
sim-false sim
  with sim wfΔL wfΔL Wk1-wf (forget lk₁⊑rk₁) stL
sim-false sim | N′ , r′ , W′ , ev , wf′ , q , d = unrelated (runs-RK₁ r′) d

-- Sim for the restricted relation (SimDef's statement, local relation)
Simᴿ : Set
Simᴿ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N : Term} {A A′ : Ty}
        {p : A ⊑ᵂ⟨ W ⟩ A′} {ξ : Alloc}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ ⊢ M -→ N ∣ ξ
  → ∃[ N′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* N′ ]
      Σ[ W′ ∈ World (apply ξ Δ) (applyˢ (allocs r′) Δ′) ]
        (W ⟿[ ξ ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
        × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N ⊑ N′ ∶ q)

-- THE COUNTEREXAMPLE TO THE PROPOSAL
simᴿ-false : Simᴿ → ⊥
simᴿ-false sim
  with sim wfΔL wfΔL Wk1-wf lk₁⊑rk₁ stL
simᴿ-false sim | N′ , r′ , W′ , ev , wf′ , q , d =
  unrelated (runs-RK₁ r′) (forget d)

------------------------------------------------------------------------
-- 3e. SimBack fails for the current rule (the boundary-Merge risk)
------------------------------------------------------------------------

-- the world after the right's Inst TyBeta: (αᴸ, αᴿ) global, β unpaired
Wk : World ΔL ΔRk
Wk = world [] []↪ []↪ ((0 , 1) ∷ []) []

Wk-wf : WfWorld Wk
Wk-wf = wf-world joint[] agree (namedᴸ-≤1 Wk ≤1-[]) (namedᴿ-≤1 Wk ≤1-[])
  where
  agree : ∀ {α β} → Paired Wk α β → Agree Wk α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

-- the premise world: Y (the opened left binder) lexically paired with β
PwK : World (underΛ ΔL) (reps ΔRk ∣ (0 ∷ []))
PwK = Wk ⊕⁺ X⊑X ^ 0

PwK-is : PwK ≡ world (X⊑X ∷ []) (keep []↪) (keep []↪) ((1 , 1) ∷ [])
                     ((0 , 0) ∷ [])
PwK-is = refl

-- inside the inner boundary `+X^α` (both sides): Y at 0, X at 1
ΘX : Boundary
ΘX = bind 1 1 ∷ []

ΔLX ΔRX : Ctxᵗ
ΔLX = (abstR ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
ΔRX = (bindR ★ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

bindX-int : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ⁱ ΘX ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
bindX-int = interior (changes∷ changes[]
  (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

bindX-conv : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ᶜ ΘX ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
bindX-conv = conversion (conv-bind (_ , there here) conv[]
  (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

WX : World ΔLX ΔRX
WX = world (X⊑X ∷ X⊑X ∷ []) (keep (keep []↪)) (keep (keep []↪))
       ((1 , 1) ∷ []) ((0 , 0) ∷ [])

WX-int : Interior PwK ΘX ΘX WX
WX-int = record
  { int-left   = bindX-int
  ; int-right  = bindX-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ
      { (_ , here) (_ , here) refl refl → (λ _ → refl) , (λ _ → refl)
      ; (_ , here) (_ , there here) _ ()
      ; (_ , here) (_ , there (there ())) _ _
      ; (_ , there here) _ () _
      ; (_ , there (there ())) _ _ _
      }
  ; join-fresh = λ
      { here here (inj₁ ()) ; here here (inj₂ ())
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there (there ())) _
      ; (there here) (there (there ())) _
      ; (there (there ())) _ _
      }
  ; mark-left  = λ
      { (_ , here) refl here → here
      ; (_ , there here) () _
      ; (_ , there (there ())) _ _
      }
  ; mark-right = λ
      { (_ , here) refl here → here
      ; (_ , there here) () _
      ; (_ , there (there ())) _ _
      }
  }

WX-conv : ConversionInterior PwK ΘX ΘX WX
WX-conv = record
  { conv-left       = bindX-conv
  ; conv-right      = bindX-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ
      { here here here here → (λ _ → refl) , (λ _ → refl)
      ; here here here (there ())
      ; here here (there ()) _
      ; here (there here) _ (there ())
      ; here (there (there ())) _ _
      ; (there here) _ (there ()) _
      ; (there (there ())) _ _ _
      }
  ; conv-join-fresh = λ
      { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there (there ())) _
      ; (there here) (there (there ())) _
      ; (there (there ())) _ _
      }
  ; conv-mark-left  = λ
      { here here here → here
      ; here (there ()) _
      ; (there here) (there ()) _
      ; (there (there ())) _ _
      }
  ; conv-mark-right = λ
      { here here here → here
      ; here (there ()) _
      ; (there here) (there ()) _
      ; (there (there ())) _ _
      }
  }

WX-wf : WfWorld WX
WX-wf = wf-world (both (inj₂ here⇔) (both (inj₁ here⇔) joint[])) agree
  (λ _ _ _ → uniqᴸ) (λ _ _ _ → uniqᴿ)
  where
  agree : ∀ {α β} → Paired WX α β → Agree WX α β
  agree (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))
  uniqᴸ : ∀ {α α′ β} → Paired WX α β → Paired WX α′ β → α ≡ α′
  uniqᴸ (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴸ (inj₁ here⇔) (inj₁ (there⇔ ()))
  uniqᴸ (inj₁ (there⇔ ())) _
  uniqᴸ (inj₂ here⇔) (inj₂ here⇔) = refl
  uniqᴸ (inj₂ here⇔) (inj₂ (there⇔ ()))
  uniqᴸ (inj₂ (there⇔ ())) _
  uniqᴸ (inj₁ here⇔) (inj₂ (there⇔ ()))
  uniqᴸ (inj₂ here⇔) (inj₁ (there⇔ ()))
  uniqᴿ : ∀ {α β β′} → Paired WX α β → Paired WX α β′ → β ≡ β′
  uniqᴿ (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴿ (inj₁ here⇔) (inj₁ (there⇔ ()))
  uniqᴿ (inj₁ (there⇔ ())) _
  uniqᴿ (inj₂ here⇔) (inj₂ here⇔) = refl
  uniqᴿ (inj₂ here⇔) (inj₂ (there⇔ ()))
  uniqᴿ (inj₂ (there⇔ ())) _
  uniqᴿ (inj₁ here⇔) (inj₂ (there⇔ ()))
  uniqᴿ (inj₂ here⇔) (inj₁ (there⇔ ()))

-- N_L = inst_Y(VL) is literally the right's interior Nk
instVL : InstX VL Nk
instVL = inst-⟪⟫ (S-Λ (V-simple S-ƛ)) (inst-Λ (V-simple S-ƛ))

bNL : BdyTy (underΛ ΔL) ΘX ΔLX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
bNL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = underΛ ΔL} {M = Nk}))))

bNR : BdyTy (reps ΔRk ∣ (0 ∷ [])) ΘX ΔRX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
bNR = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = reps ΔRk ∣ (0 ∷ [])} {M = Nk}))))

bOutK : BdyTy ΔRk Θ₀ (reps ΔRk ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bOutK = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Nk ⟪ Θ₀ , revX ⟫}))))

id★↦ᴿk-ty : CastTy ΔRk [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
id★↦ᴿk-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

VL-⊢ : ΔL ∣ [] ⊢ VL ⦂ ∀X⇒X
VL-⊢ = tc

Nk⊑Nk : PwK TI.∣ [] ⊢ Nk ⊑ Nk ∶ ⇒⊑⇒ X⊑X X⊑X
Nk⊑Nk =
  TI.⟪⟫⊑⟪⟫ WX-int WX-wf (TI.ƛ⊑ƛ {pA = X⊑X} tf tf (TI.x⊑x Zʷ)) bNL bNR
    (WX , WX-conv , cId⊑cId X⊑X) (⇒⊑⇒ X⊑X X⊑X)

-- THE PRE-MERGE PAIR, by the CURRENT ∀⊑⟪+⟫ with the non-simple
-- interior Nk (the restricted rule would need `Simple Nk`, false)
cexK : Wk TI.∣ [] ⊢ VL ⊑ Rarg₃ ∶ ∀id⊑★ Wk
cexK =
  TI.⊑cast (TI.∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var) vVL VL-⊢ instVL Nk⊑Nk
              r-here bOutK (∀id⊑★ Wk))
           id★↦ᴿk-ty (∀id⊑★ Wk)

-- the right's Merge (Rarg₃ → RF): the left value cannot move, the right
-- ends at the value RF, and VL ⊑ RF holds in no world
simBack-false : SimBack → ⊥
simBack-false sb with sb wfΔL wfΔRk Wk-wf cexK stM
simBack-false sb | inj₁ (N₂ , N₂′ , r , r″ , W′ , ev , wf′ , q , d)
  with value-run≡ vVL r | value-run≡ vRF r″
simBack-false sb | inj₁ (N₂ , N₂′ , r , r″ , W′ , ev , wf′ , q , d)
  | refl | refl = final-unrelated d
simBack-false sb | inj₂ (ℓ , r) with value-run≡ vVL r
simBack-false sb | inj₂ (ℓ , r) | ()

------------------------------------------------------------------------
-- 3f. The initial pair is related: DGG part 1 fails on this pair
------------------------------------------------------------------------

νK-ty : NuTy empty `ℕ ∀X⇒X cK ∀X⇒X
νK-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = ν `ℕ · KK ⟨ cK ⟩})))

instI₀-ty : CastTy empty [] instI ∀X⇒X (★ ⇒ ★)
instI₀-ty = proj₂ (proj₂ (cast-inv {Γ = []}
  (tc {Δ = empty} {M = (ν `ℕ · KK ⟨ cK ⟩) ⟨ [] ∣ instI ⟩})))

-- the conversions of the two ν, compared under their TyBeta boundaries
νK-conv : NuConversionImp ∅ʷ νK-ty νK-ty
νK-conv = Wν , Wν-conv , conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId X⊑X)))

-- (in the restricted relation, hence by forget in the current one)
lk⊑rk : ∅ʷ ∣ [] ⊢ LK ⊑ RK ∶ ∀id⊑★ ∅ʷ
lk⊑rk =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ ∅ʷ} tf tf (x⊑x Zʷ))
    (⊑cast
      (ν⊑ν
        (Λ⊑Λ lift-[] (V-simple (S-Λ (V-simple S-ƛ)))
          (V-simple (S-Λ (V-simple S-ƛ)))
          (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
          (∀⊑∀ (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))))
        (ι⊑ι base-ℕ) νK-ty νK-ty νK-conv (∀id⊑∀id ∅ʷ))
      instI₀-ty (∀id⊑★ ∅ʷ))

st₀ : empty ⊢ RK -→ RK₁ ∣ new `ℕ
st₀ = justStep refl

stL₀ : empty ⊢ LK -→ LK₁ ∣ new `ℕ
stL₀ = justStep refl

RK-run : ∀ {N′} → empty ⊢ RK -→* N′ → Ends N′
RK-run done = e-app
RK-run (st then r) with det RK-⊢ st st₀
RK-run (st then r) | refl , refl = runs-RK₁ r

LK-run : empty ⊢ LK -→* VL
LK-run = stL₀ then stL then done

-- DGG part 1 (design.md §9.7) at the cast calculus, for each relation
DGG1 DGG1ᴿ : Set
DGG1 = ∀ {M M′ V A A′} {W : World empty empty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W TI.∣ [] ⊢ M ⊑ M′ ∶ p
  → (r : empty ⊢ M -→* V) → Value V
  → ∃[ V′ ] Σ[ r′ ∈ empty ⊢ M′ -→* V′ ] Value V′
      × Σ[ W′ ∈ World (applyˢ (allocs r) empty) (applyˢ (allocs r′) empty) ]
          Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ TI.∣ [] ⊢ V ⊑ V′ ∶ q)
DGG1ᴿ = ∀ {M M′ V A A′} {W : World empty empty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → (r : empty ⊢ M -→* V) → Value V
  → ∃[ V′ ] Σ[ r′ ∈ empty ⊢ M′ -→* V′ ] Value V′
      × Σ[ W′ ∈ World (applyˢ (allocs r) empty) (applyˢ (allocs r′) empty) ]
          Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ V ⊑ V′ ∶ q)

dgg1-false : DGG1 → ⊥
dgg1-false dgg with dgg (forget lk⊑rk) LK-run vVL
dgg1-false dgg | V′ , r′ , v′ , W′ , q , d = unrelated (RK-run r′) d

dgg1ᴿ-false : DGG1ᴿ → ⊥
dgg1ᴿ-false dgg with dgg lk⊑rk LK-run vVL
dgg1ᴿ-false dgg | V′ , r′ , v′ , W′ , q , d =
  unrelated (RK-run r′) (forget d)

------------------------------------------------------------------------
-- 3g. A candidate repair (sketch, not adopted): ∀⊑⟪+⟫ after a Merge
------------------------------------------------------------------------

-- Candidate rule ∀⊑⟪+⟫ᴹ: the right boundary is the merged
-- `Θ′ ++ (bind 0 β ∷ [])` (the Inst entry acts first), and the premise
-- relates N = inst_X(V) to `U′ ⟪ Θ′ , c″ ⟫` for SOME conversion c″
-- typing that inner boundary (c″ is not in the conclusion: Merge
-- composed it into c′).  Restricted form: U′ simple.  A right Merge of
-- the Inst boundary then keeps the premise unchanged.  On §3's final
-- pair every premise holds; the term premise is cexK's own:
bBm : BdyTy ΔRk Θ₂ ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bBm = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Bm}))))

Θ₂-merged : Θ₂ ≡ ΘX ++ (bind 0 0 ∷ [])
Θ₂-merged = refl

final-candidate-premises :
    (PwK TI.∣ [] ⊢ Nk ⊑ idX ⟪ ΘX , cId ⟫ ∶ ⇒⊑⇒ X⊑X X⊑X)
  × Simple idX
  × BdyTy (reps ΔRk ∣ (0 ∷ [])) ΘX ΔRX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
  × BdyTy ΔRk Θ₂ ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  × (ΔRk ∋rep 0 := ★)
  × (∀X⇒X ⊑ᵂ⟨ Wk ⟩ (★ ⇒ ★))
final-candidate-premises = Nk⊑Nk , S-ƛ , bNR , bBm , r-here , ∀id⊑★ Wk

------------------------------------------------------------------------
-- 4. What the Inst cases need under the restriction (statement only)
------------------------------------------------------------------------

-- a ∀-boundary value: the one form whose InstX image is a boundary
-- (inst-⟪⟫), so that the Inst boundary over it merges (§3)
data ForallBdy : Term → Set where
  fbdy : ∀ {U Θ s} → ForallBdy (U ⟪ Θ , ⌞ `∀ s ⌟ ⟫)

VL-forallBdy : ForallBdy VL
VL-forallBdy = fbdy

-- The forward and backward Inst cases: from V ⊑ V₀′ (inside the cast
-- `inst X.p`), after the right's Inst and TyBeta (β:=★ at rep. var 0 of
-- Δ⁺ = allocate ★ Δ′) the right runs the interior N₀′ = inst_X(V₀′) to
-- a SIMPLE U′, the left unmoved at N = inst_X(V); the pair N ⊑ U′ is
-- related in the premise world of the evolved exterior world.
--   * `C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′`: the binders match.  It does NOT follow from
--     `V ⊑ V₀′ ⟨inst X.p⟩` (the premise index may be `∀⊑`, a left-only
--     outer binder; the derivation may end with cast⊑cast, cast⊑, Λ⊑ or
--     ⟪⟫⊑).  InstXImp2/InstXImp⁺ already take it as a premise.
--   * `¬ ForallBdy V₀′`: NECESSARY.  §3 (V₀′ = VL) has no simple U′:
--     the interior Nk is a boundary value and its next step is the
--     Merge of the Inst boundary.
--   * ρ may allocate (a nested Inst and TyBeta inside a gen- or
--     ∀-cast's coercion), so it is not `Admin`.
InstSync : Set
InstSync = ∀ {Δ Δ′} {W : World Δ Δ′} {V V₀′ N N₀′ C C′}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′
  → NonVar C → 0 ∈ᵗ C
  → Value V → Value V₀′ → InstX V N → InstX V₀′ N₀′
  → W ∣ [] ⊢ V ⊑ V₀′ ∶ r
  → ¬ ForallBdy V₀′
  → ∃[ m ] ∃[ U′ ]
      Σ[ ρ ∈ (reps (allocate ★ Δ′) ∣ (0 ∷ names (allocate ★ Δ′)))
               ⊢ N₀′ -→* U′ ]
      Simple U′
      × Σ[ W′ ∈ World Δ (applyˢ (allocs ρ) (allocate ★ Δ′)) ]
          (allocᴿ ★ W ⟿[ [] ∣ allocs ρ ] W′) × WfWorld W′
          × Σ[ q ∈ C ⊑ᵂ⟨ W′ ⊕⁺ m ^ shiftβ (allocs ρ) 0 ⟩ C′ ]
              (W′ ⊕⁺ m ^ shiftβ (allocs ρ) 0 ∣ [] ⊢ N ⊑ U′ ∶ q)
