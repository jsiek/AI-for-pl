module proof.DGG.notes.ForallBoundaryFixes where

-- File Charter:
--   * FIXES for the two open items of ForallBoundaryRisks.md (R3, R2);
--     findings in ForallBoundaryFixes.md, re-evaluated under design.md
--     D25 in D25.md.  NOT a Def module, not imported by All.agda.
--     Works against ∀⊑⟪+⟫ with D22's `NonVar A`/`0 ∈ᵗ A` premises,
--     D23's payload imprecision `RepImp` and D25's `WfWorld` (named
--     uniqueness, no one-left-partner rule).
--   * §1 (R3) UNDER D25 THE PLAIN PREMISE WORLD `W ⊕⁺ m ^ β` SUFFICES:
--     it is well formed whenever W is, β:=★ and β has no left partner
--     named in Δ (`wf-⊕⁺`, proof/ImprecisionWorld.agda).  The earlier
--     proposal `W ⊕⁺ˢ m ^ β` (drop every pair of β first) is withdrawn:
--     under D23 a surviving pair's agreement may read a dropped pair
--     (`⊕⁺ˢ-breaks-agreement`).
--   * §4 a LOCAL COPY of the relation, `_∣_⊢_⊑_∶_` with the same
--     constructor names as TermImprecision, plus one constructor
--     `∀⊑⟪+⟫ᵃ` (candidate B of R2).
--   * §5 (R3, b) the five existing ∀⊑⟪+⟫ derivations (p3-inst = ch-x0,
--     cg-x0, c2-x0, c12-x0), copied verbatim into the local relation.
--   * §6 (R3, c) L3c/R3c: the pair before and after the left's TyBeta;
--     the premise world after it gives αᴿ two left partners, only one
--     of them named, and is well formed.
--   * §7 L3d/R3d: BOTH copies instantiated on the left.  The second
--     catch-up (`ev-L⇔` without D13's premise) gives αᴿ a second left
--     partner; the evolved world is well formed and the pair after the
--     second TyBeta is related (`l3d-after`).
--   * §8 (R2) L2c/R2c: the pair at the right's TyBeta (`r2c-pre`) and
--     after the right's Merge with the left unmoved, derived twice:
--     (A) with ∀⊑⟪+⟫ as it is (`r2c-post-A`, premise N ⊑ merged), and
--     (B) with the candidate `∀⊑⟪+⟫ᵃ` (`r2c-post-B`, premise read after
--     the left's own administrative Merge).
--   * §9 (R2) the statements: `allocᴿ-⊕⁺` (proved), `InstExpand`
--     (left-expansion), `B-admissible` (B follows from A + InstExpand,
--     proved), and the child `SimBackInstX` (statement only).
--   * Orientation: the LEFT term is the more precise one.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; head; drop)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction
  using (InstX; inst-Λ; inst-gen; _⊢_-→_∣_; _⊢_-→*_; done; _then_)
open import Data.Unit using (⊤; tt)
open import Imprecision
open import ImprecisionWorld
open import proof.ImprecisionWorld
  using (wf-⊕⁺; NoNamedPartner; namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[])
open import ConversionImprecision
open import TermImprecision
  using (Lit; lit-$; lit-true; lit-false; CastTy; cast-ty; NuTy; BdyTy;
         bdy-ty; NuConversionImp; BdyConversionImp; ⟪⟫-inv; cast-inv; ν-inv)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; ev-L⇔; ev-noneᴿ; ev-done; applyˢ; allocs)
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms; eval-sound)
open import examples.CambridgeExamples using (I; instI; genI; C2-L; C12-L)
open import examples.ImprecisionExamples using (L1)
open import examples.TermImprecisionExamples
  using (idX; revX; ℕ⊑★; 5⟨ℕ!⟩; Θ₀; L1′; ΔL; ΔR; ΔRᵢ; W₁; Wᵢ₁; Wᵢ₁-int;
         Wᵢ₁-wf; bL-ty; bR-ty; bLR-conv; revX⊑revX; νL-ty; W₃; R3′; int₀;
         conv₀)
open import examples.TermImprecisionRebaseExamples
  using (id★↦; id★→; tagX↦; ∀id⊑★; ∀id⊑∀id; ★⇒★; ℕ⇒ℕ; ℕ⇒ℕ⊑★⇒★; id★→⊑id★→;
         X⇒X⊑★⇒★; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty; id★↦ᴿ-ty; ΛidX-⊢; Cg-R₂;
         Wg⁺; Wg⁻-int; Wg⁻-wf; I★genI-⊢; C2-L-ν-ty; W2⁺; W2⁻-int; W2⁻-wf;
         W2⁺-conv; I★⁻ᴸ-ty; tagᴸ-ty; C12-R₂; C12-ν₂-ty; genIᴿ-ty; Wν₂;
         Wν₂-conv)
open import proof.DGG.notes.ForallBoundaryRisks
  using (L2c-⊢; R2c-⊢; L3c-⊢; R3c-⊢)

private
  variable
    Δ Δ′ : Ctxᵗ

------------------------------------------------------------------------
-- 1. (R3) The premise world under D25
------------------------------------------------------------------------

-- ∀⊑⟪+⟫ reads the plain `W ⊕⁺ m ^ β` (ImprecisionWorld §5).  It is well
-- formed when W is, β:=★ (a premise of the rule) and β has no left
-- partner named in Δ (`wf-⊕⁺`).  β may keep unnamed left partners: the
-- premise names only the new left rep. var 0 for β, so a right rejoin
-- of β inside the premise joins 0 and nothing else.
wf-premise : ∀ {W : World Δ Δ′} {m β}
  → WfWorld W → Δ′ ∋rep β := ★ → NoNamedPartner W β
  → WfWorld (W ⊕⁺ m ^ β)
wf-premise = wf-⊕⁺

-- THE WITHDRAWN PROPOSAL: drop every pair whose right member is β ...
dropᴿ : RVar → RepRel → RepRel
dropᴿ β [] = []
dropᴿ β ((α , β′) ∷ ϱ) with β′ ≟ β
dropᴿ β ((α , β′) ∷ ϱ) | yes _ = dropᴿ β ϱ
dropᴿ β ((α , β′) ∷ ϱ) | no _  = (α , β′) ∷ dropᴿ β ϱ

-- ... before adding the lexical (0, β)
infixl 6 _⊕⁺ˢ_^_
_⊕⁺ˢ_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
world μ η η′ ϱᵍ ϱˡ ⊕⁺ˢ m ^ β =
  world (m ∷ μ) (keep (relabel suc η)) (keep η′)
        (dropᴿ β (shiftᴸ ϱᵍ)) ((zero , β) ∷ dropᴿ β (shiftᴸ ϱˡ))

-- Why it is withdrawn (D23): payloads mention rep. vars, and a payload
-- pair may be related THROUGH a pair of β.  In Wd, rep. var 1 is
-- ℕ on the left and ★ (= β) on the right, paired; rep. var 0 holds
-- ` 1 on both sides, and (0, 0) agrees by ` 1 ⊑ᴿ ` 1 through (1, 1).
-- ⊕⁺ˢ at β = 1 drops (1+1, 1), so the shifted (0+1, 0) no longer agrees.
ΞLd ΞRd : RepCtx
ΞLd = bindR (` 0) ∷ bindR `ℕ ∷ []
ΞRd = bindR (` 0) ∷ bindR ★ ∷ []

Wd : World (ΞLd ∣ []) (ΞRd ∣ [])
Wd = world [] []↪ []↪ ((0 , 0) ∷ (1 , 1) ∷ []) []

Wd-agree : ∀ {α β} → Paired Wd α β → Agree Wd α β
Wd-agree (inj₁ here⇔) = rep-rep r-here r-here (α⊑β (inj₁ (there⇔ here⇔)))
Wd-agree (inj₁ (there⇔ here⇔)) =
  rep-rep (r-there r-here) (r-there r-here) (ι⊑★ base-ℕ)
Wd-agree (inj₁ (there⇔ (there⇔ ())))
Wd-agree (inj₂ ())

Wd-wf : WfWorld Wd
Wd-wf = wf-world joint[] Wd-agree (namedᴸ-≤1 Wd ≤1-[])
  (namedᴿ-≤1 Wd ≤1-[])

-- the plain premise world keeps both pairs, and is well formed ...
Wd⁺-wf : WfWorld (Wd ⊕⁺ X⊑X ^ 1)
Wd⁺-wf = wf-premise Wd-wf (r-there r-here) (λ { (_ , ()) })

-- ... the shadowing one is not: (1, 0) has payloads ` 2 / ` 1, and
-- (2, 1) was dropped
-- the two payload lookups of (1, 0) in the shadowing premise world
lookupᴸ1 : ∀ {b} → (abstR ∷ ΞLd) ∋ʳ 1 := b → b ≡ bindR (` 2)
lookupᴸ1 (r-there-abst r-here) = refl

lookupᴿ0 : ∀ {b} → ΞRd ∋ʳ 0 := b → b ≡ bindR (` 1)
lookupᴿ0 r-here = refl

no-2⊑1 : ¬ ([] ⊢ ` 2 ⊑ᴿ⟨ Wd ⊕⁺ˢ X⊑X ^ 1 ⟩ ` 1)
no-2⊑1 (α⊑β (inj₁ (there⇔ ())))
no-2⊑1 (α⊑β (inj₂ (there⇔ ())))

⊕⁺ˢ-breaks-agreement : ¬ WfWorld (Wd ⊕⁺ˢ X⊑X ^ 1)
⊕⁺ˢ-breaks-agreement wf with wf-agree wf (inj₁ here⇔)
⊕⁺ˢ-breaks-agreement wf | abst-abst l _ with lookupᴸ1 l
⊕⁺ˢ-breaks-agreement wf | abst-abst l _ | ()
⊕⁺ˢ-breaks-agreement wf | abst-★ l _ with lookupᴸ1 l
⊕⁺ˢ-breaks-agreement wf | abst-★ l _ | ()
⊕⁺ˢ-breaks-agreement wf | rep-rep l r p with lookupᴸ1 l | lookupᴿ0 r
⊕⁺ˢ-breaks-agreement wf | rep-rep l r p | refl | refl = no-2⊑1 p

------------------------------------------------------------------------
-- 3. Administrative runs: no step allocates
------------------------------------------------------------------------

Admin : ∀ {Δ M N} → Δ ⊢ M -→* N → Set
Admin done = ⊤
Admin (_then_ {δ = none} st r)  = Admin r
Admin (_then_ {δ = new R} st r) = ⊥

------------------------------------------------------------------------
-- 4. A local copy of the relation, with one extra rule ∀⊑⟪+⟫ᵃ
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

  -- as in TermImprecision: the premise world is `W ⊕⁺ m ^ β`
  ∀⊑⟪+⟫ : ∀ {V N V′ β m c′ A A′ B′} {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
    → NonVar A
    → 0 ∈ᵗ A
    → Value V
    → Δ ∣ lhs γ ⊢ V ⦂ `∀ A
    → InstX V N
    → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
    → Δ′ ∋rep β := ★
    → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q

  -- (R2, candidate B; §8) the premise may be read after an
  -- administrative (non-allocating) run of the inst_X image
  ∀⊑⟪+⟫ᵃ : ∀ {V N N₀ V′ β m c′ A A′ B′} {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
    → NonVar A
    → 0 ∈ᵗ A
    → Value V
    → Δ ∣ lhs γ ⊢ V ⦂ `∀ A
    → InstX V N
    → (ρ : underΛ Δ ⊢ N -→* N₀) → Admin ρ
    → W ⊕⁺ m ^ β ∣ [] ⊢ N₀ ⊑ V′ ∶ r
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

------------------------------------------------------------------------
-- 5. (R3, b) The five existing ∀⊑⟪+⟫ derivations still go through
------------------------------------------------------------------------

five⊑ : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ : CtxImp W}
  → W ∣ γ ⊢ $ 5 ⊑ 5⟨ℕ!⟩ ∶ ℕ⊑★
five⊑ = ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

-- p3-inst (TermImprecisionExamples) = ch-x0, verbatim but `∀id⊑★ W₃`
p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
p3-inst =
  ·⊑· (ν⊑ (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
                    (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
                    (inst-Λ (V-simple S-ƛ))
                    (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
                    r-here bR-ty (∀id⊑★ W₃))
                 id★↦ᴿ-ty (∀id⊑★ W₃))
          ℕ⊑★ νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

-- cg-x0, verbatim (its Wg⁻-int is an `Interior Wg⁺ …`, Wg⁺ = W₃ ⊕⁺ …)
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
          r-here Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

-- c2-x0, verbatim
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
          r-here Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

-- c12-x0, verbatim
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
            r-here bR-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        genIᴿ-ty (∀id⊑∀id W₃))
      (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , revX⊑revX refl)
      (ℕ⇒ℕ W₃))
    (κ⊑κ lit-$ (ι⊑ι base-ℕ))

------------------------------------------------------------------------
-- 6. (R3, c) L3c/R3c: the left's TyBeta of copy 1
------------------------------------------------------------------------

-- the right's Inst boundary over αᴿ:=★, under its `id(★) → id(★)` cast
B⟨id⟩ : Term
B⟨id⟩ = (idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩

-- left after Beta (copy 1 is the ν, copy 2 the Λ under λy); left after
-- the TyBeta of copy 1; right after Inst, TyBeta and Beta
L3c₁ L3c₂ R3c₃ : Term
L3c₁ = (ƛ `ℕ ∙ I) · L1
L3c₂ = (ƛ `ℕ ∙ I) · L1′
R3c₃ = (ƛ ★ ∙ B⟨id⟩) · R3′

L3c₁-state : head (drop 1 (evalTerms 20 L3c-⊢)) ≡ just L3c₁
L3c₁-state = refl

L3c₂-state : head (drop 2 (evalTerms 20 L3c-⊢)) ≡ just L3c₂
L3c₂-state = refl

R3c₃-state : head (drop 3 (evalTerms 25 R3c-⊢)) ≡ just R3c₃
R3c₃-state = refl

-- copy 2, `Λ ⊑ [+X^αᴿ] … ⟨id(★) → id(★)⟩`, under λy:ℕ ⊑ λy:★, in any
-- world over the two runtime contexts
copy2 : ∀ {Ξ} {W : World (Ξ ∣ []) ΔR}
  → (Ξ ∣ []) ∣ `ℕ ∷ [] ⊢ I ⦂ `∀ (` 0 ⇒ ` 0)
  → W ∣ ctx-imp `ℕ ★ ℕ⊑★ ∷ [] ⊢ I ⊑ B⟨id⟩ ∶ ∀id⊑★ W
copy2 {W = W} ⊢I =
  ⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
           (V-simple (S-Λ (V-simple S-ƛ))) ⊢I (inst-Λ (V-simple S-ƛ))
           (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
           r-here bR-ty (∀id⊑★ W))
        id★↦ᴿ-ty (∀id⊑★ W)

-- BEFORE the TyBeta: both copies by ∀⊑⟪+⟫, in W₃ (αᴿ unpaired)
l3c-pre : W₃ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ ∀id⊑★ W₃
l3c-pre = ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 tc)) p3-inst

-- AFTER it: copy 1 by ⟪⟫⊑⟪⟫ through the new global pair (αᴸ, αᴿ)
-- (= ch-b1), copy 2 still by ∀⊑⟪+⟫, now in W₁
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

-- the world evolution of the step (Evolve's catch-up `ev-L⇔`) and
-- the well-formedness of both worlds
W₁-agree : ∀ {α β} → Paired W₁ α β → Agree W₁ α β
W₁-agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑★ base-ℕ)
W₁-agree (inj₁ (there⇔ ()))
W₁-agree (inj₂ ())

W₁-wf : WfWorld W₁
W₁-wf = wf-world joint[] W₁-agree (namedᴸ-≤1 W₁ ≤1-[])
  (namedᴿ-≤1 W₁ ≤1-[])

l3c-evolve : W₃ ⟿[ new `ℕ ∷ [] ∣ [] ] W₁
l3c-evolve = ev-L⇔ wfᴿ-ℕ r-here (W₁-agree (inj₁ here⇔)) ev-done

-- copy 2's premise world keeps the global (αᴸ+1, αᴿ) next to the
-- lexical (0, αᴿ) ...
post-premise : W₁ ⊕⁺ X⊑X ^ 0
  ≡ world (X⊑X ∷ []) (keep []↪) (keep []↪) ((1 , 0) ∷ []) ((0 , 0) ∷ [])
post-premise = refl

two-partners : Paired (W₁ ⊕⁺ X⊑X ^ 0) 1 0 × Paired (W₁ ⊕⁺ X⊑X ^ 0) 0 0
two-partners = inj₁ here⇔ , inj₂ here⇔

-- ... but only 0 has a left name, so a rejoin of αᴿ is unambiguous ...
only-0-named : ∀ {α} → names (underΛ ΔL) ∋ᵅ α → α ≡ 0
only-0-named (_ , here)     = refl
only-0-named (_ , there ())

-- ... and the premise world is well formed (D25; under D13 it was not)
post-premise-wf : WfWorld (W₁ ⊕⁺ X⊑X ^ 0)
post-premise-wf = wf-premise W₁-wf r-here (λ { (_ , ()) })

------------------------------------------------------------------------
-- 7. (R3, beyond) both copies instantiated on the left
------------------------------------------------------------------------

--   L  (λf:∀X.X→X. (λy:ℕ. f[ℕ] 5) (f[ℕ] 5)) (ΛX.λx:X.x)
--   R  (λf:★→★.    (λy:★. f 5)    (f 5))    (ΛX.λx:X.x)
L3d R3d : Term
L3d = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙
        ((ƛ `ℕ ∙ ((ν `ℕ · ` 1 ⟨ revX ⟩) · $ 5))
          · ((ν `ℕ · ` 0 ⟨ revX ⟩) · $ 5))) · I
R3d = (ƛ (★ ⇒ ★) ∙ ((ƛ ★ ∙ (` 1 · 5⟨ℕ!⟩)) · (` 0 · 5⟨ℕ!⟩)))
    · (I ⟨ [] ∣ instI ⟩)

L3d-⊢ : empty ∣ [] ⊢ L3d ⦂ `ℕ
L3d-⊢ = tc

R3d-⊢ : empty ∣ [] ⊢ R3d ⦂ ★
R3d-⊢ = tc

-- the left's second TyBeta (copy 2) meets the right's copy 2: the pair
-- is P3's (L1, R3′) again, now in W₁ (αᴸ of copy 1 paired with αᴿ)
L3d₇-state : head (drop 7 (evalTerms 30 L3d-⊢)) ≡ just L1
L3d₇-state = refl

L3d₈-state : head (drop 8 (evalTerms 30 L3d-⊢)) ≡ just L1′
L3d₈-state = refl

R3d₁₂-state : head (drop 12 (evalTerms 40 R3d-⊢)) ≡ just R3′
R3d₁₂-state = refl

νLₗ-ty : NuTy ΔL `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
νLₗ-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = ΔL} {M = ν `ℕ · I ⟨ revX ⟩})))

l3d-before : W₁ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
l3d-before =
  ·⊑· (ν⊑ (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
                    (V-simple (S-Λ (V-simple S-ƛ))) tc
                    (inst-Λ (V-simple S-ƛ))
                    (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
                    r-here bR-ty (∀id⊑★ W₁))
                 id★↦ᴿ-ty (∀id⊑★ W₁))
          ℕ⊑★ νLₗ-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

-- the second catch-up: copy 2's left TyBeta finds αᴿ already paired
-- with copy 1's αᴸ.  `ev-L` would leave the new left rep. var (0)
-- unpaired, so copy 2's ⟪⟫⊑⟪⟫ (whose Interior joins the two fresh
-- names iff Paired) could not join X with X′ ...
second-unpaired : ¬ Paired (allocᴸ `ℕ W₁) 0 0
second-unpaired (inj₁ (there⇔ ()))
second-unpaired (inj₂ ())

-- ... so the catch-up is `ev-L⇔` again (D25 dropped its no-partner
-- premise): αᴿ gets the two left partners 0 (copy 2) and 1 (copy 1),
-- both store rep. vars without a name
W₂d : World (allocate `ℕ ΔL) ΔR
W₂d = allocᴸ⇔ `ℕ 0 W₁

W₂d-agree : ∀ {α β} → Paired W₂d α β → Agree W₂d α β
W₂d-agree (inj₁ here⇔)          = rep-rep r-here r-here (ι⊑★ base-ℕ)
W₂d-agree (inj₁ (there⇔ here⇔)) =
  rep-rep (r-there r-here) r-here (ι⊑★ base-ℕ)
W₂d-agree (inj₁ (there⇔ (there⇔ ())))
W₂d-agree (inj₂ ())

second-paired-wf : WfWorld W₂d
second-paired-wf = wf-world joint[] W₂d-agree (namedᴸ-≤1 W₂d ≤1-[])
  (namedᴿ-≤1 W₂d ≤1-[])

l3d-evolve : W₁ ⟿[ new `ℕ ∷ [] ∣ [] ] W₂d
l3d-evolve = ev-L⇔ wfᴿ-ℕ r-here (W₂d-agree (inj₁ here⇔)) ev-done

-- AFTER the second TyBeta: copy 2 by ⟪⟫⊑⟪⟫ through the new global pair
-- (0, αᴿ), as ch-b1 for copy 1.  Inside, X names 0 only: copy 1's
-- rep. var 1 has no name, so named uniqueness holds
ΔL₂ᵢ : Ctxᵗ
ΔL₂ᵢ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ [])

Wᵢ₂d : World ΔL₂ᵢ ΔRᵢ
Wᵢ₂d = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ (1 , 0) ∷ []) []

int₂ : allocate `ℕ ΔL ⊢ⁱ Θ₀ ⇒ ΔL₂ᵢ
int₂ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

conv₂ : allocate `ℕ ΔL ⊢ᶜ Θ₀ ⇒ ΔL₂ᵢ
conv₂ = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)

Wᵢ₂d-int : Interior W₂d Θ₀ Θ₀ Wᵢ₂d
Wᵢ₂d-int = record
  { int-left   = int₂
  ; int-right  = int₀
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Wᵢ₂d-conv : ConversionInterior W₂d Θ₀ Θ₀ Wᵢ₂d
Wᵢ₂d-conv = record
  { conv-left       = conv₂
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

Wᵢ₂d-agree : ∀ {α β} → Paired Wᵢ₂d α β → Agree Wᵢ₂d α β
Wᵢ₂d-agree (inj₁ here⇔)          = rep-rep r-here r-here (ι⊑★ base-ℕ)
Wᵢ₂d-agree (inj₁ (there⇔ here⇔)) =
  rep-rep (r-there r-here) r-here (ι⊑★ base-ℕ)
Wᵢ₂d-agree (inj₁ (there⇔ (there⇔ ())))
Wᵢ₂d-agree (inj₂ ())

Wᵢ₂d-wf : WfWorld Wᵢ₂d
Wᵢ₂d-wf = wf-world (both (inj₁ here⇔) joint[]) Wᵢ₂d-agree
  (namedᴸ-≤1 Wᵢ₂d ≤1-∷[]) (namedᴿ-≤1 Wᵢ₂d ≤1-∷[])

bL₂-ty : BdyTy (allocate `ℕ ΔL) Θ₀ ΔL₂ᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
bL₂-ty = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = allocate `ℕ ΔL} {M = idX ⟪ Θ₀ , revX ⟫}))))

bLR₂-conv : BdyConversionImp W₂d bL₂-ty bR-ty
bLR₂-conv = Wᵢ₂d , Wᵢ₂d-conv , revX⊑revX refl

l3d-after : W₂d ∣ [] ⊢ L1′ ⊑ R3′ ∶ ℕ⊑★
l3d-after =
  ·⊑·
    (⊑cast
      (⟪⟫⊑⟪⟫ Wᵢ₂d-int Wᵢ₂d-wf
        (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
        bL₂-ty bR-ty bLR₂-conv (ℕ⇒ℕ⊑★⇒★ W₂d))
      id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ W₂d))
    five⊑

------------------------------------------------------------------------
-- 8. (R2) L2c/R2c: the right's Merge inside its Inst boundary
------------------------------------------------------------------------

-- the left after its TyBeta (αᴸ:=★) and one Beta: a gen-cast ∀-value
-- over a boundary value
Bα V2 L2c₂ : Term
Bα   = idX ⟪ Θ₀ , revX ⟫
V2   = Bα ⟨ [] ∣ genI ⟩
L2c₂ = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙ ` 0) · V2

L2c₂-state : head (drop 2 (evalTerms 20 L2c-⊢)) ≡ just L2c₂
L2c₂-state = refl

-- N = inst_Y(V2) (Y at rep. var 0, αᴸ at 1); the right's interior
-- after Inst and TyBeta (β at 0, αᴿ at 1) is the same term
Θ₁ Θm : Boundary
Θ₁ = bind 0 1 ∷ []
Θm = bind 0 1 ∷ unbind 0 0 ∷ []

Bin Nu N N₀ : Term
Bin = idX ⟪ Θ₁ , revX ⟫
Nu  = Bin ⟪ unbind 0 0 ∷ [] , id★→ ⟫
N   = Nu ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩
-- ... and after the Merge (left: N₀; right: the interior of R2c₅)
N₀  = (idX ⟪ Θm , revX ⟫) ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩

R2c₄ R2c₅ : Term
R2c₄ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((N ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)
R2c₅ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((N₀ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)

R2c₄-state : head (drop 4 (evalTerms 20 R2c-⊢)) ≡ just R2c₄
R2c₄-state = refl

R2c₅-state : head (drop 5 (evalTerms 20 R2c-⊢)) ≡ just R2c₅
R2c₅-state = refl

vBα : Value Bα
vBα = V-⟪⟫ S-ƛ I-fun

vV2 : Value V2
vV2 = V-simple (S-cast vBα I-gen)

instV2 : InstX V2 N
instV2 = inst-gen vBα

-- the contexts and worlds
ΔR2 : Ctxᵗ
ΔR2 = allocate ★ ΔR

ΞL ΞR : RepCtx
ΞL = abstR ∷ bindR ★ ∷ []
ΞR = bindR ★ ∷ bindR ★ ∷ []

-- after the matched TyBetas of αᴸ/αᴿ (ev-2) and the right's β (ev-R)
W4 : World ΔR ΔR2
W4 = world [] []↪ []↪ ((0 , 1) ∷ []) []

-- every world below has ϱᵍ = {(αᴸ, αᴿ)} and ϱˡ = {(Y, β)}
module P {nsL nsR : TyCtx} (μ : ImpEnv) (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

  W : World (ΞL ∣ nsL) (ΞR ∣ nsR)
  W = world μ η η′ ((1 , 1) ∷ []) ((0 , 0) ∷ [])

  agree : ∀ {α β} → Paired W α β → Agree W α β
  agree (inj₁ here⇔) = rep-rep (r-there-abst r-here) (r-there r-here) ★⊑★
  agree (inj₁ (there⇔ ()))
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))

-- the premise world of ∀⊑⟪+⟫
Pw : World (underΛ ΔR) (ΞR ∣ (0 ∷ []))
Pw = W4 ⊕⁺ X⊑X ^ 0

Pw-is : Pw ≡ P.W (X⊑X ∷ []) (keep []↪) (keep []↪)
Pw-is = refl

-- inside both −Y: no names
Pu : World (ΞL ∣ []) (ΞR ∣ [])
Pu = P.W [] []↪ []↪

Pu-wf : WfWorld Pu
Pu-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[])
  where open P [] []↪ []↪

-- inside both +X^α: X both-sided at X⊑X
Pb : World (ΞL ∣ (1 ∷ [])) (ΞR ∣ (1 ∷ []))
Pb = P.W (X⊑X ∷ []) (keep []↪) (keep []↪)

Pb-wf : WfWorld Pb
Pb-wf = wf-world (both (inj₁ here⇔) joint[]) agree
  (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[])
  where open P (X⊑X ∷ []) (keep []↪) (keep []↪)

-- the boundary readings
unb-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ (unbind 0 0 ∷ [])
  ⇒ ((b ∷ Ξ) ∣ [])
unb-int = interior (changes∷ changes[]
  (step-unbind (_ , here) del-here fresh[]))

unb-conv-self : ∀ {b b′ Ξ Ξ′}
    {W : World ((b ∷ Ξ) ∣ (0 ∷ [])) ((b′ ∷ Ξ′) ∣ (0 ∷ []))}
  → ConversionInterior W (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W
unb-conv-self = record
  { conv-left       = conversion (conv-unbind (_ , here) conv[])
  ; conv-right      = conversion (conv-unbind (_ , here) conv[])
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ
      { here here here here → (λ j → j) , (λ j → j)
      ; here here here (there ())
      ; here here (there ()) _
      ; here (there ()) _ _
      ; (there ()) _ _ _
      }
  ; conv-join-fresh = λ
      { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                        ; (there ()) _ _ }
  ; conv-mark-right = λ { here here m → m ; here (there ()) _
                        ; (there ()) _ _ }
  }

bind₁-int : ∀ {Ξ} {b₀ b₁ : RepBinding} → ((b₀ ∷ b₁ ∷ Ξ) ∣ []) ⊢ⁱ Θ₁
  ⇒ ((b₀ ∷ b₁ ∷ Ξ) ∣ (1 ∷ []))
bind₁-int = interior (changes∷ changes[]
  (step-bind (_ , there here) fresh[] ins-here))

bind₁-conv : ∀ {Ξ} {b₀ b₁ : RepBinding} → ((b₀ ∷ b₁ ∷ Ξ) ∣ []) ⊢ᶜ Θ₁
  ⇒ ((b₀ ∷ b₁ ∷ Ξ) ∣ (1 ∷ []))
bind₁-conv = conversion (conv-bind (_ , there here) conv[] fresh[] ins-here)

Θm-int : ∀ {Ξ} {b₀ b₁ : RepBinding} → ((b₀ ∷ b₁ ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ Θm
  ⇒ ((b₀ ∷ b₁ ∷ Ξ) ∣ (1 ∷ []))
Θm-int = interior (changes∷
  (changes∷ changes[] (step-unbind (_ , here) del-here fresh[]))
  (step-bind (_ , there here) fresh[] ins-here))

Θm-conv : ∀ {Ξ} {b₀ b₁ : RepBinding} → ((b₀ ∷ b₁ ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ Θm
  ⇒ ((b₀ ∷ b₁ ∷ Ξ) ∣ (1 ∷ 0 ∷ []))
Θm-conv = conversion (conv-bind (_ , there here)
  (conv-unbind (_ , here) conv[]) (fresh∷ (λ ()) fresh[]) ins-here)

Iu : Interior Pw (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) Pu
Iu = record
  { int-left   = unb-int
  ; int-right  = unb-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , ()) _ _ }
  }

Ib : Interior Pu Θ₁ Θ₁ Pb
Ib = record
  { int-left   = bind₁-int
  ; int-right  = bind₁-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Ibc : ConversionInterior Pu Θ₁ Θ₁ Pb
Ibc = record
  { conv-left       = bind₁-conv
  ; conv-right      = bind₁-conv
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

-- typing side premises, read off `tc`
bBᴸ : BdyTy (ΞL ∣ []) Θ₁ (ΞL ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bBᴸ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΞL ∣ []} {M = Bin}))))

bBᴿ : BdyTy (ΞR ∣ []) Θ₁ (ΞR ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bBᴿ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΞR ∣ []} {M = Bin}))))

bUᴸ : BdyTy (underΛ ΔR) (unbind 0 0 ∷ []) (ΞL ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
bUᴸ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = underΛ ΔR} {M = Nu}))))

bUᴿ : BdyTy (ΞR ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (ΞR ∣ []) (★ ⇒ ★) id★→
  (★ ⇒ ★)
bUᴿ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΞR ∣ (0 ∷ [])} {M = Nu}))))

bMᴸ : BdyTy (underΛ ΔR) Θm (ΞL ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bMᴸ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = underΛ ΔR} {M = idX ⟪ Θm , revX ⟫}))))

bMᴿ : BdyTy (ΞR ∣ (0 ∷ [])) Θm (ΞR ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bMᴿ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΞR ∣ (0 ∷ [])} {M = idX ⟪ Θm , revX ⟫}))))

tagNᴸ : CastTy (underΛ ΔR) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagNᴸ = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = underΛ ΔR} {M = N})))

tagNᴿ : CastTy (ΞR ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagNᴿ = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΞR ∣ (0 ∷ [])} {M = N})))

bOut₄ : BdyTy ΔR2 Θ₀ (ΞR ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bOut₄ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔR2} {M = N ⟪ Θ₀ , revX ⟫}))))

bOut₅ : BdyTy ΔR2 Θ₀ (ΞR ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bOut₅ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔR2} {M = N₀ ⟪ Θ₀ , revX ⟫}))))

id★↦ᴿ₂-ty : CastTy ΔR2 [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
id★↦ᴿ₂-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

V2-⊢ : ΔR ∣ [] ⊢ V2 ⦂ `∀ (` 0 ⇒ ` 0)
V2-⊢ = tc

-- the pair at the right's TyBeta (before its Merge): ∀⊑⟪+⟫ with
-- premise N ⊑ N, two nested ⟪⟫⊑⟪⟫ under the matched tag casts
N⊑N : Pw ∣ [] ⊢ N ⊑ N ∶ ⇒⊑⇒ X⊑X X⊑X
N⊑N =
  cast⊑cast
    (⟪⟫⊑⟪⟫ Iu Pu-wf
      (⟪⟫⊑⟪⟫ Ib Pb-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bBᴸ bBᴿ
        (Pb , Ibc , revX⊑revX refl) (★⇒★ Pu))
      bUᴸ bUᴿ (Pw , unb-conv-self , id★→⊑id★→) (★⇒★ Pw))
    tagNᴸ tagNᴿ (⇒⊑⇒ X⊑X X⊑X)

r2c-pre : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₄ ∶ ∀id⊑★ W4
r2c-pre =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
    (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var) vV2 V2-⊢ instV2 N⊑N r-here
              bOut₄ (∀id⊑★ W4))
           id★↦ᴿ₂-ty (∀id⊑★ W4))

-- the right's Merge step is matched by ev-noneᴿ: the world stays W4

-- (B) the left's own Merge, as the administrative run of the premise
N-⊢ : underΛ ΔR ∣ [] ⊢ N ⦂ (` 0 ⇒ ` 0)
N-⊢ = tc

N-merge : underΛ ΔR ⊢ N -→* N₀
N-merge = eval-sound 1 N-⊢

N-merge-admin : Admin N-merge
N-merge-admin = tt

-- the final interior world of Θm ∥ Θm is Pb again; the conversion
-- contexts keep Y (Θm's unbind is skipped)
Pcm : World (ΞL ∣ (1 ∷ 0 ∷ [])) (ΞR ∣ (1 ∷ 0 ∷ []))
Pcm = P.W (X⊑X ∷ X⊑X ∷ []) (keep (keep []↪)) (keep (keep []↪))

Im : Interior Pw Θm Θm Pb
Im = record
  { int-left   = Θm-int
  ; int-right  = Θm-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Imc : ConversionInterior Pw Θm Θm Pcm
Imc = record
  { conv-left       = Θm-conv
  ; conv-right      = Θm-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ
      { (there here) (there here) here here → (λ _ → refl) , (λ _ → refl)
      ; here _ (there ()) _
      ; (there here) here _ (there ())
      ; (there here) (there (there ())) _ _
      ; (there (there ())) _ _ _
      }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) (there here) (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
      ; (there here) (there here) (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here (there (there ())) _
      ; (there here) (there (there ())) _
      ; (there (there ())) _ _
      }
  ; conv-mark-left  = λ
      { (there here) here here → there here ; here (there ()) _
      ; (there here) (there ()) _ ; (there (there ())) _ _ }
  ; conv-mark-right = λ
      { (there here) here here → there here ; here (there ()) _
      ; (there here) (there ()) _ ; (there (there ())) _ _ }
  }

tagN₀ᴸ : CastTy (underΛ ΔR) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagN₀ᴸ = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = underΛ ΔR} {M = N₀})))

tagN₀ᴿ : CastTy (ΞR ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagN₀ᴿ = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΞR ∣ (0 ∷ [])} {M = N₀})))

N₀⊑N₀ : Pw ∣ [] ⊢ N₀ ⊑ N₀ ∶ ⇒⊑⇒ X⊑X X⊑X
N₀⊑N₀ =
  cast⊑cast
    (⟪⟫⊑⟪⟫ Im Pb-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bMᴸ bMᴿ
      (Pcm , Imc , revX⊑revX refl) (★⇒★ Pw))
    tagN₀ᴸ tagN₀ᴿ (⇒⊑⇒ X⊑X X⊑X)

r2c-post-B : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ ∀id⊑★ W4
r2c-post-B =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
    (⊑cast (∀⊑⟪+⟫ᵃ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var) vV2 V2-⊢ instV2
              N-merge N-merge-admin N₀⊑N₀ r-here bOut₅ (∀id⊑★ W4))
           id★↦ᴿ₂-ty (∀id⊑★ W4))

-- (A) the left unmerged against the right merged: the left's −Y is
-- one-sided (Y goes right-only, keeping X⊑X), then [+X^α] ∥ [−Y, +X^α]
Pu′ : World (ΞL ∣ []) (ΞR ∣ (0 ∷ []))
Pu′ = P.W (X⊑X ∷ []) (skip []↪) (keep []↪)

Pu′-wf : WfWorld Pu′
Pu′-wf = wf-world (right-only joint[]) agree
  (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-∷[])
  where open P (X⊑X ∷ []) (skip []↪) (keep []↪)

Pc′ : World (ΞL ∣ (1 ∷ [])) (ΞR ∣ (1 ∷ 0 ∷ []))
Pc′ = P.W (X⊑X ∷ X⊑X ∷ []) (keep (skip []↪)) (keep (keep []↪))

Iu′ : Interior Pw (unbind 0 0 ∷ []) [] Pu′
Iu′ = record
  { int-left   = unb-int
  ; int-right  = interior changes[]
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , here) refl m → m ; (_ , there ()) _ _ }
  }

Ib′ : Interior Pu′ Θ₁ Θm Pb
Ib′ = record
  { int-left   = bind₁-int
  ; int-right  = Θm-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Ibc′ : ConversionInterior Pu′ Θ₁ Θm Pc′
Ibc′ = record
  { conv-left       = bind₁-conv
  ; conv-right      = Θm-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ
      { (there here) here here → there here ; here (there ()) _
      ; (there here) (there ()) _ ; (there (there ())) _ _ }
  }

N⊑N₀ : Pw ∣ [] ⊢ N ⊑ N₀ ∶ ⇒⊑⇒ X⊑X X⊑X
N⊑N₀ =
  cast⊑cast
    (⟪⟫⊑ Iu′ Pu′-wf
      (⟪⟫⊑⟪⟫ Ib′ Pb-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bBᴸ bMᴿ
        (Pc′ , Ibc′ , revX⊑revX refl) (★⇒★ Pu′))
      bUᴸ (★⇒★ Pw))
    tagNᴸ tagN₀ᴿ (⇒⊑⇒ X⊑X X⊑X)

-- with the UNCHANGED ∀⊑⟪+⟫ (premise at N = inst_Y(V2) itself)
r2c-post-A : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ ∀id⊑★ W4
r2c-post-A =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
    (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var) vV2 V2-⊢ instV2 N⊑N₀ r-here
              bOut₅ (∀id⊑★ W4))
           id★↦ᴿ₂-ty (∀id⊑★ W4))

W4-same : W4 ⟿[ [] ∣ none ∷ [] ] W4
W4-same = ev-noneᴿ ev-done

------------------------------------------------------------------------
-- 9. (R2) What SimBackFrame-∀⊑⟪+⟫ needs
------------------------------------------------------------------------

-- (i) the right's allocations inside the boundary commute with the
-- premise world: the IH's world can be read back as `W′ ⊕⁺ m ^ β′`
shiftᴿᴸ : (ϱ : RepRel) → shiftᴿ (shiftᴸ ϱ) ≡ shiftᴸ (shiftᴿ ϱ)
shiftᴿᴸ []      = refl
shiftᴿᴸ (π ∷ ϱ) = cong (_ ∷_) (shiftᴿᴸ ϱ)

allocᴿ-⊕⁺ : ∀ {Δ Δ′} (R′ : Ty) (W : World Δ Δ′) (m : VarImp) (β : RVar)
  → allocᴿ R′ (W ⊕⁺ m ^ β) ≡ allocᴿ R′ W ⊕⁺ m ^ suc β
allocᴿ-⊕⁺ R′ (world μ η η′ ϱᵍ ϱˡ) m β =
  cong₂ (world (m ∷ μ) (keep (relabel suc η)) (keep (relabel suc η′)))
    (shiftᴿᴸ ϱᵍ) (cong ((zero , suc β) ∷_) (shiftᴿᴸ ϱˡ))

-- (ii) LEFT-EXPANSION along an administrative run of an inst_X image
-- (candidate A's lemma; on L2c/R2c it is `N⊑N₀` from `N₀⊑N₀`)
InstExpand : Set
InstExpand = ∀ {Δ Δ′ᵢ} {Wᵢ : World (underΛ Δ) Δ′ᵢ} {V N N₂ M′ A A′}
    {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′}
  → Value V → InstX V N
  → (ρ : underΛ Δ ⊢ N -→* N₂) → Admin ρ
  → WfWorld Wᵢ
  → Wᵢ ∣ [] ⊢ N₂ ⊑ M′ ∶ r
  → Wᵢ ∣ [] ⊢ N ⊑ M′ ∶ r

-- with InstExpand, candidate B's rule is admissible from the existing
-- one: B adds no derivable pair, it only moves the expansion
B-admissible : InstExpand
  → ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {V N N₀ V′ β m c′ A A′ B′}
      {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
  → WfWorld W → NoNamedPartner W β
  → NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ lhs γ ⊢ V ⦂ `∀ A → InstX V N
  → (ρ : underΛ Δ ⊢ N -→* N₀) → Admin ρ
  → W ⊕⁺ m ^ β ∣ [] ⊢ N₀ ⊑ V′ ∶ r
  → Δ′ ∋rep β := ★
  → (b : BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′)
  → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
  → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q
B-admissible ex wf nn nv occ v ⊢V i ρ a d hβ b q =
  ∀⊑⟪+⟫ nv occ v ⊢V i (ex v i ρ a (wf-premise wf hβ nn) d) hβ b q

-- (iii) THE CHILD the frame needs: backward simulation INSIDE a
-- ∀⊑⟪+⟫ premise with the left UNMOVED (the left value V cannot step,
-- so the IH of SimBack, which may answer with any left run, is too
-- weak).  The right's allocations are read back through allocᴿ-⊕⁺.
shiftβ : List Alloc → RVar → RVar
shiftβ []           β = β
shiftβ (none  ∷ ξs) β = shiftβ ξs β
shiftβ (new R ∷ ξs) β = shiftβ ξs (suc β)

SimBackInstX : Set
SimBackInstX = ∀ {Δ Δ′} {W : World Δ Δ′} {V N M′ M₁′ β m A A′ δ′}
    {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ [] ⊢ V ⦂ `∀ A → InstX V N
  → Δ′ ∋rep β := ★
  → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ M′ ∶ r
  → (st′ : (reps Δ′ ∣ (β ∷ names Δ′)) ⊢ M′ -→ M₁′ ∣ δ′)
  → ∃[ M₂′ ] Σ[ r″ ∈ apply δ′ (reps Δ′ ∣ (β ∷ names Δ′)) ⊢ M₁′ -→* M₂′ ]
      Σ[ W′ ∈ World Δ (applyˢ (allocs (st′ then r″)) Δ′) ]
        (W ⟿[ [] ∣ allocs (st′ then r″) ] W′) × WfWorld W′
        × Σ[ r′ ∈ A ⊑ᵂ⟨ W′ ⊕⁺ m ^ shiftβ (allocs (st′ then r″)) β ⟩ A′ ]
            (W′ ⊕⁺ m ^ shiftβ (allocs (st′ then r″)) β ∣ [] ⊢ N ⊑ M₂′ ∶ r′)
