module proof.DGG.notes.FixB-BoundaryAbsorbs where

-- File Charter:
--   * HISTORICAL: written against the relation before design.md D26
--     (2026-10-03), which removed `∀⊑⟪+⟫` and generalized `⊑⟪⟫` with
--     `Opens`.  It no longer type-checks against TermImprecision (it, or
--     a note it imports, uses the old rule) and is excluded from every
--     check: All.agda does not import it and it is not a *Proof.agda.
--     FixB (∀⊑ʸ, Λ⊑ʳ) was not adopted; D26 took the generalized `⊑⟪⟫`.
--   * FIX (b) FOR THE ∀-BOUNDARY MERGE COUNTEREXAMPLE
--     (RestrictedForallBoundary §3): a left `[+X^α] (ΛY. V) ⟨∀Y. c⟩`
--     against the right's MERGED `[+Y^β, +X^α] V′ ⟨c′⟩` by the
--     boundary-pair rule ⟪⟫⊑⟪⟫, the extra right entry `+Y^β` giving a
--     right-only name that a left Λ then takes.  Findings in
--     FixB-BoundaryAbsorbs.md.  NOT a Def module, not imported by
--     All.agda; nothing outside this file is edited.
--   * §1 THE OBSTACLE.  As proposed (only a term rule and conversion
--     clauses), fix (b) is impossible: the interior type index
--     `∀Y.Y→Y ⊑ Y→Y` (Y a right name) has no type-imprecision
--     derivation in any world (`index-empty`).  So fix (b) needs ONE
--     TYPE CLAUSE, `∀⊑ʸ`, besides the term rule `Λ⊑ʳ` and the
--     conversion clauses.
--   * §2–§6 a LOCAL COPY of the relations: type imprecision plus `∀⊑ʸ`
--     (`_⊢_⊑ᵇ_`); the world relation `JoinΛ` (a left Λ binder takes
--     the right-only name at the head of the center); conversion
--     imprecision plus `conv-∀⊑ʸ`, `conv-id⊑seal`, `conv-id⊑unseal`;
--     term imprecision = TermImprecision MINUS ∀⊑⟪+⟫ PLUS `Λ⊑ʳ`.
--     `up`/`upC` embed the global type and conversion relations.
--     Simplification: term-context entries (`CtxImp`) keep global type
--     proofs, so a λ-annotation never uses `∀⊑ʸ` (none does below).
--   * §7 THE COUNTEREXAMPLE, REPAIRED: every synchronization pair,
--     including the final one, is derived; the pre- and post-Merge
--     pairs share the SAME interior derivation `I⊑idX`; the Sim
--     obligation that `sim-false` refuted is met (`sim-cex`), so are the
--     SimBack obligation at the right's Merge (`simBack-cex`) and DGG
--     part 1 (`dgg1-cex`).
--   * §8 THE BLOCKS THAT USED ∀⊑⟪+⟫, re-derived WITHOUT it: P3 (= Ch),
--     Cg, C2, C12, L3c, L3d, R2c (before and after the right's Merge).
--     ∀⊑⟪+⟫'s premise world is literally `JoinΛ` of the right-only
--     interior world of ⊑⟪⟫ (`join-⊕⁺`).
--   * §9 statements (only) of the lemmas the simulations need.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing; Is-just; from-just)
import Data.Maybe.Relation.Unary.Any as Any
open import Data.Unit using (tt)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
open import proof.ImprecisionWorld
  using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[]; NoNamedPartner)
import ConversionImprecision as CI
import TermImprecision as TI
open TI
  using (Lit; lit-$; CastTy; cast-ty; NuTy; nu-ty; BdyTy; bdy-ty;
         ⟪⟫-inv; cast-inv; ν-inv)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; ev-done; ev-R; ev-noneᴸ; ev-noneᴿ; applyˢ; allocs)
open import examples.TypeCheck using (tc; tf)
open import examples.CambridgeExamples using (I; I★; instI; genI; C2-L; C12-L)
open import examples.ImprecisionExamples using (L1)
open import examples.TermImprecisionExamples
  using (idX; revX; ℕ⊑★; 5⟨ℕ!⟩; Θ₀; ΔL; ΔR; ΔLᵢ; ΔRᵢ; W₁; W₃; R3′; int₀;
         conv₀; Wν; Wν-conv; νL-ty; bR-ty; revX⊑revX)
open import examples.TermImprecisionRebaseExamples
  using (id★↦; id★→; tagX↦; ∀id⊑★; ∀id⊑∀id; ★⇒★; ℕ⇒ℕ; ℕ⇒ℕ⊑★⇒★;
         X⇒X⊑★⇒★; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty; id★↦ᴿ-ty; ΛidX-⊢; Cg-R₂;
         Wg⁻-int; Wg⁻-wf; Wg⁺-wf; I★genI; I★genI-⊢; C2-L-ν-ty; W2⁺-wf;
         C12-R₂; C12-ν₂-ty; genIᴿ-ty; Wν₂; Wν₂-conv; ΔRₓ)
open import proof.DGG.notes.ForallBoundaryFixes
  using (B⟨id⟩; L3c₁; L3c₂; R3c₃; post-premise-wf; νLₗ-ty; L2c₂; R2c₄; R2c₅;
         Bα; Bin; Nu; N; N₀; Θ₁; Θm; ΔR2; ΞR; W4; bBᴿ; bUᴿ; bMᴿ; tagNᴿ;
         tagN₀ᴿ; bOut₄; bOut₅; id★↦ᴿ₂-ty; bind₁-int; bind₁-conv; Θm-int;
         Θm-conv; unb-int; shiftβ)
open import examples.TermImprecisionExamples
  using (p1-init; p1-tybeta; p2-tybeta; p6-tybeta)
open import examples.TermImprecisionRebaseExamples
  using (c12-b1; leaf⊑; c2-b6; c2-b7; c13-b1; c14-b1; ΛI⊑ΛI; ch-b0; cg-b0;
         c2-b0; c12-b0; ch-b1)
open import proof.DGG.notes.RestrictedForallBoundary
  using (forget; l3d-after;
         KK; cId; cK; ∀X⇒X; VL; Nk; Rarg₃; Bm; RF; LK; LK₁; RK; RK₁; RK₂;
         RK₃; RK₄; ΔRk; wfΔL; vVL; vRF; Wk1; Wk1ᵢ; Wk1-wf; Wk1ᵢ-wf; Wk1ᵢ-int;
         Wk1ᵢ-conv; bVL; instI-ty; Wk; Wk-wf; ΘX; ΔRX; bindX-int; bindX-conv;
         WX; WX-wf; bNR; bOutK; id★↦ᴿk-ty; Θ₂; bBm; νK-ty; instI₀-ty; st₀;
         st₁; st₂; st₃; st₄; stM; stL; LK-run; cId⊑cId)

private
  variable
    Δ Δ′ : Ctxᵗ

------------------------------------------------------------------------
-- 1. The obstacle: the interior type index has no derivation
------------------------------------------------------------------------

-- `∀X. X → X ⊑ Y → Y` fails for every name Y and every environment:
-- the only candidate is `∀⊑`, whose premise needs `X ⊑ Y` at a left
-- variable X ≠ Y
no-∀⊑var : ∀ {μ c} → ¬ (μ ⊢ ∀X⇒X ⊑ (` c ⇒ ` c))
no-∀⊑var (∀⊑ _ _ (⇒⊑⇒ () _))

-- hence, in EVERY world, the interior index of the proposed ⟪⟫⊑⟪⟫ (and
-- the conclusion index of any term rule relating `ΛY. λx:Y. x` to
-- `λx:Y. x`) is empty: fix (b) as proposed needs a type clause
index-empty : ∀ {W : World Δ Δ′} → ¬ (∀X⇒X ⊑ᵂ⟨ W ⟩ (` 0 ⇒ ` 0))
index-empty = no-∀⊑var

------------------------------------------------------------------------
-- 2. Type imprecision with the new clause ∀⊑ʸ (a local copy)
------------------------------------------------------------------------

infix 4 _⊢_⊑ᵇ_

-- Imprecision's rules, plus `∀⊑ʸ`: a left ∀ against a right type that
-- shows, at the bound variable's positions, a NAME Y (in a world: a
-- right-only name that a left binder takes, see JoinΛ).  The intended
-- rule also requires Y to be right-only (stateable only in a world);
-- with that, `Y ∈ᵗ B` makes it disjoint from `∀⊑` (which needs ★ there).
data _⊢_⊑ᵇ_ (μ : ImpEnv) : Ty → Ty → Set where
  ★⊑★ : μ ⊢ ★ ⊑ᵇ ★
  ι⊑ι : ∀ {ι} → Base ι → μ ⊢ ι ⊑ᵇ ι
  X⊑X : ∀ {X} → μ ⊢ ` X ⊑ᵇ ` X
  ⇒⊑⇒ : ∀ {A A′ B B′} → μ ⊢ A ⊑ᵇ A′ → μ ⊢ B ⊑ᵇ B′
    → μ ⊢ (A ⇒ B) ⊑ᵇ (A′ ⇒ B′)
  ∀⊑∀ : ∀ {A B} → extᵐ μ ⊢ A ⊑ᵇ B → μ ⊢ (`∀ A) ⊑ᵇ (`∀ B)
  ⇒⊑★ : ∀ {A B} → μ ⊢ A ⊑ᵇ ★ → μ ⊢ B ⊑ᵇ ★ → μ ⊢ A ⇒ B ⊑ᵇ ★
  ι⊑★ : ∀ {ι} → Base ι → μ ⊢ ι ⊑ᵇ ★
  X⊑★ : ∀ {X} → μ ∋ˡ X := X⊑★ → μ ⊢ ` X ⊑ᵇ ★
  ∀⊑ : ∀ {A B} → NonVar A → 0 ∈ᵗ A → instᵐ μ ⊢ A ⊑ᵇ ⇑ᵗ B
    → μ ⊢ (`∀ A) ⊑ᵇ B
  ∀★⊑★ : μ ⊢ (`∀ ★) ⊑ᵇ ★
  ∀⊑★ : ∀ {A} → NonStar A → extᵐ μ ⊢ A ⊑ᵇ ★ → μ ⊢ (`∀ A) ⊑ᵇ ★
  bot-elim : μ ⊢ (`∀ (` 0)) ⊑ᵇ (`∀ ★)
  bot⊑★ : μ ⊢ (`∀ (` 0)) ⊑ᵇ ★
  -- NEW
  ∀⊑ʸ : ∀ {A B Y m} → μ ∋ˡ Y := m → NonVar A → 0 ∈ᵗ A → Y ∈ᵗ B
    → μ ⊢ A [ ` Y ]ᵗ ⊑ᵇ B
    → μ ⊢ (`∀ A) ⊑ᵇ B

up : ∀ {μ A B} → μ ⊢ A ⊑ B → μ ⊢ A ⊑ᵇ B
up ★⊑★ = ★⊑★
up (ι⊑ι b) = ι⊑ι b
up X⊑X = X⊑X
up (⇒⊑⇒ p q) = ⇒⊑⇒ (up p) (up q)
up (∀⊑∀ p) = ∀⊑∀ (up p)
up (⇒⊑★ p q) = ⇒⊑★ (up p) (up q)
up (ι⊑★ b) = ι⊑★ b
up (X⊑★ x) = X⊑★ x
up (∀⊑ nv occ p) = ∀⊑ nv occ (up p)
up ∀★⊑★ = ∀★⊑★
up (∀⊑★ ns p) = ∀⊑★ ns (up p)
up bot-elim = bot-elim
up bot⊑★ = bot⊑★

infix 4 _⊑ᴮ⟨_⟩_
_⊑ᴮ⟨_⟩_ : Ty → World Δ Δ′ → Ty → Set
A ⊑ᴮ⟨ W ⟩ A′ = μʷ W ⊢ embᴸ W A ⊑ᵇ embᴿ W A′

------------------------------------------------------------------------
-- 3. The world operation: a left Λ takes the right-only head name
------------------------------------------------------------------------

-- `JoinΛ W β W⁺`: the head of W's center is a RIGHT-ONLY name (skip on
-- the left), the right's name 0, whose rep. var is β.  A left Λ binder
-- joins it: the new left name 0 is kept into that center name (its
-- mark unchanged), and the left's abstract rep. var 0 is paired with β
-- lexically.  The choice is syntax-directed: always the head.
data JoinΛ {Δ : Ctxᵗ}
    : ∀ {Δ′} → World Δ Δ′ → RVar → World (underΛ Δ) Δ′ → Set where
  join-head : ∀ {Ξ′ η′ β μ m} {ι : names Δ ↪ μ} {ι′ : η′ ↪ μ}
      {ϱᵍ ϱˡ : RepRel}
    → JoinΛ {Δ′ = Ξ′ ∣ (β ∷ η′)} (world (m ∷ μ) (skip ι) (keep ι′) ϱᵍ ϱˡ) β
        (world (m ∷ μ) (keep (relabel suc ι)) (keep ι′) (shiftᴸ ϱᵍ)
               ((zero , β) ∷ shiftᴸ ϱˡ))

-- the interior world of ⊑⟪⟫ at a single right entry `+X^β`: X is a
-- right-only name with mark m
infixl 6 _⊕ʳ_^_
_⊕ʳ_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World Δ (reps Δ′ ∣ (β ∷ names Δ′))
world μ η η′ ϱᵍ ϱˡ ⊕ʳ m ^ β = world (m ∷ μ) (skip η) (keep η′) ϱᵍ ϱˡ

-- ∀⊑⟪+⟫'s premise world IS JoinΛ of that interior world: ∀⊑⟪+⟫ is the
-- composite ⊑⟪⟫ ∘ Λ⊑ʳ (for a left Λ)
join-⊕⁺ : ∀ {W : World Δ Δ′} {m β} → JoinΛ (W ⊕ʳ m ^ β) β (W ⊕⁺ m ^ β)
join-⊕⁺ = join-head

-- term contexts under JoinΛ: left types shifted, right types kept
data LiftCtxᴶ {W : World Δ Δ′} {Δ⁺} {W⁺ : World Δ⁺ Δ′}
    : CtxImp W → CtxImp W⁺ → Set where
  liftᴶ-[] : LiftCtxᴶ [] []
  liftᴶ-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtxᴶ γ γ′
    → LiftCtxᴶ (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

------------------------------------------------------------------------
-- 4. Conversion imprecision with the new clauses (a local copy)
------------------------------------------------------------------------

mutual
  data MidImpᵇ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) : Mid → Mid → Set where
    conv-id⊑id : ∀ {A A′} → A ⊑ᵂ⟨ W ⟩ A′ → MidImpᵇ W (id A) (id A′)
    conv-↦⊑↦ : ∀ {s s′ c c′} → ConvImpᵇ W s s′ → ConvImpᵇ W c c′
      → MidImpᵇ W (s ↦ c) (s′ ↦ c′)
    conv-∀⊑∀ : ∀ {c c′} → ConvImpᵇ (W ⊕ X⊑X) c c′
      → MidImpᵇ W (`∀ c) (`∀ c′)
    conv-∀⊑ : ∀ {c g′} → ConvImpᵇ (W ⊕ᴸ) c ⌞ g′ ⌟ → MidImpᵇ W (`∀ c) g′
    -- NEW: the left binder takes the right-only head name (JoinΛ), in
    -- which the right conversion has revealed it
    conv-∀⊑ʸ : ∀ {c g′ β} {W⁺ : World (underΛ Δ) Δ′} → JoinΛ W β W⁺
      → ConvImpᵇ W⁺ c ⌞ g′ ⌟ → MidImpᵇ W (`∀ c) g′

  data TailImpᵇ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) : Tail → Tail → Set where
    conv-mid⊑mid : ∀ {g g′} → MidImpᵇ W g g′ → TailImpᵇ W (mid g) (mid g′)
    conv-seal⊑seal : ∀ {X X′} → Joins W X X′
      → TailImpᵇ W (seal X) (seal X′)
    conv-⨾seal⊑⨾seal : ∀ {t t′ X X′} → TailImpᵇ W t t′ → Joins W X X′
      → TailImpᵇ W (t ⨾seal X) (t′ ⨾seal X′)
    conv-seal⊑id★ : ∀ {X} → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → TailImpᵇ W (seal X) (mid (id ★))
    conv-⨾seal⊑ : ∀ {t t′ X} → TailImpᵇ W t t′
      → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★ → TailImpᵇ W (t ⨾seal X) t′
    -- NEW (mirror of conv-seal⊑id★): a right seal of the joined name
    -- is an identity on the left
    conv-id⊑seal : ∀ {X X′} → Joins W X X′
      → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → TailImpᵇ W (mid (id (` X))) (seal X′)

  data ConvImpᵇ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) : Conv → Conv → Set where
    conv-tail⊑tail : ∀ {t t′} → TailImpᵇ W t t′
      → ConvImpᵇ W (tail t) (tail t′)
    conv-unseal⊑unseal : ∀ {X X′} → Joins W X X′
      → ConvImpᵇ W (unseal X) (unseal X′)
    conv-unseal⨾⊑unseal⨾ : ∀ {X X′ c c′} → Joins W X X′ → ConvImpᵇ W c c′
      → ConvImpᵇ W (unseal X ⨾ c) (unseal X′ ⨾ c′)
    conv-unseal⊑id★ : ∀ {X} → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → ConvImpᵇ W (unseal X) ⌞ id ★ ⌟
    conv-unseal⨾⊑ : ∀ {X c c′} → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → ConvImpᵇ W c c′ → ConvImpᵇ W (unseal X ⨾ c) c′
    -- NEW (mirror of conv-unseal⊑id★)
    conv-id⊑unseal : ∀ {X X′} → Joins W X X′
      → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → ConvImpᵇ W ⌞ id (` X) ⌟ (unseal X′)

mutual
  upM : ∀ {W : World Δ Δ′} {g g′} → CI.MidImp W g g′ → MidImpᵇ W g g′
  upM (CI.conv-id⊑id p) = conv-id⊑id p
  upM (CI.conv-↦⊑↦ s c) = conv-↦⊑↦ (upC s) (upC c)
  upM (CI.conv-∀⊑∀ c) = conv-∀⊑∀ (upC c)
  upM (CI.conv-∀⊑ c) = conv-∀⊑ (upC c)

  upT : ∀ {W : World Δ Δ′} {t t′} → CI.TailImp W t t′ → TailImpᵇ W t t′
  upT (CI.conv-mid⊑mid g) = conv-mid⊑mid (upM g)
  upT (CI.conv-seal⊑seal j) = conv-seal⊑seal j
  upT (CI.conv-⨾seal⊑⨾seal t j) = conv-⨾seal⊑⨾seal (upT t) j
  upT (CI.conv-seal⊑id★ x) = conv-seal⊑id★ x
  upT (CI.conv-⨾seal⊑ t x) = conv-⨾seal⊑ (upT t) x

  upC : ∀ {W : World Δ Δ′} {c c′} → CI.ConvImp W c c′ → ConvImpᵇ W c c′
  upC (CI.conv-tail⊑tail t) = conv-tail⊑tail (upT t)
  upC (CI.conv-unseal⊑unseal j) = conv-unseal⊑unseal j
  upC (CI.conv-unseal⨾⊑unseal⨾ j c) = conv-unseal⨾⊑unseal⨾ j (upC c)
  upC (CI.conv-unseal⊑id★ x) = conv-unseal⊑id★ x
  upC (CI.conv-unseal⨾⊑ x c) = conv-unseal⨾⊑ x (upC c)

------------------------------------------------------------------------
-- 5. The conversion premises, over the local conversion relation
------------------------------------------------------------------------

NuConvImpᵇ : ∀ {Δ Δ′ A A′ C C′ c c′ B B′}
  → (W : World Δ Δ′) → NuTy Δ A C c B → NuTy Δ′ A′ C′ c′ B′ → Set
NuConvImpᵇ {c = c} {c′ = c′} W
  (nu-ty {R = R} {Δᶜ = Δᶜ} wA rA mw ⊢c eq wB)
  (nu-ty {R = R′} {Δᶜ = Δ′ᶜ} wA′ rA′ mw′ ⊢c′ eq′ wB′) =
  Σ[ Wᶜ ∈ World Δᶜ Δ′ᶜ ]
    (ConversionInterior (underν² R R′ W) TyBetaBoundary TyBetaBoundary Wᶜ
    × ConvImpᵇ Wᶜ c c′)

BdyConvImpᵇ : ∀ {Δ Δ′ Δᵢ Δ′ᵢ Θ Θ′} {Aᵢ A′ᵢ c c′ A A′}
  → (W : World Δ Δ′) → BdyTy Δ Θ Δᵢ Aᵢ c A → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → Set
BdyConvImpᵇ {Θ = Θ} {Θ′ = Θ′} {c = c} {c′ = c′} W
  (bdy-ty {Δᶜ = Δᶜ} mw ⊢c eqᵢ eqₑ wB)
  (bdy-ty {Δᶜ = Δ′ᶜ} mw′ ⊢c′ eq′ᵢ eq′ₑ wB′) =
  Σ[ Wᶜ ∈ World Δᶜ Δ′ᶜ ]
    (ConversionInterior W Θ Θ′ Wᶜ × ConvImpᵇ Wᶜ c c′)

------------------------------------------------------------------------
-- 6. Term imprecision: TermImprecision MINUS ∀⊑⟪+⟫ PLUS Λ⊑ʳ
------------------------------------------------------------------------

infix 3 _∣_⊢_⊑_∶_

data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) (γ : CtxImp W)
    : Term → Term → {A A′ : Ty} → A ⊑ᴮ⟨ W ⟩ A′ → Set where

  x⊑x : ∀ {x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → W ∣ γ ⊢ ` x ⊑ ` x ∶ up p

  κ⊑κ : ∀ {k ι} → Lit k ι → (p : ι ⊑ᴮ⟨ W ⟩ ι) → W ∣ γ ⊢ k ⊑ k ∶ p

  ƛ⊑ƛ : ∀ {N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᴮ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ (up pA) pB

  ·⊑· : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᴮ⟨ W ⟩ A′} {pB : B ⊑ᴮ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ M′ ∶ pA
    → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

  blame⊑ : ∀ {ℓ M′ A A′}
    → Δ ⊢ᵗ A → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′ → (p : A ⊑ᴮ⟨ W ⟩ A′)
    → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

  cast⊑cast : ∀ {M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᴮ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᴮ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  cast⊑ : ∀ {M M′ μ c B A A′} {p : B ⊑ᴮ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ μ c B A → (q : A ⊑ᴮ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

  ⊑cast : ∀ {M M′ μ′ c′ A B′ A′} {p : A ⊑ᴮ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ′ μ′ c′ B′ A′ → (q : A ⊑ᴮ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  Λ⊑Λ : ∀ {γ′ V V′ A A′} {r : A ⊑ᴮ⟨ W ⊕ X⊑X ⟩ A′}
    → LiftCtx X⊑X γ γ′ → Value V → Value V′
    → W ⊕ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
    → (q : `∀ A ⊑ᴮ⟨ W ⟩ `∀ A′)
    → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

  Λ⊑ : ∀ {γ′ V M′ A B′} {r : A ⊑ᴮ⟨ W ⊕ᴸ ⟩ B′}
    → NonVar A → 0 ∈ᵗ A → LiftCtxᴸ γ γ′ → Value V
    → W ⊕ᴸ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᴮ⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  -- NEW: the left Λ's binder takes the right-only head name (bound to ★
  -- by a right boundary entry, D16's lexical pair); the right type
  -- mentions that name
  Λ⊑ʳ : ∀ {V M′ A B′ β} {W⁺ : World (underΛ Δ) Δ′} {γ′ : CtxImp W⁺}
      {r : A ⊑ᴮ⟨ W⁺ ⟩ B′}
    → JoinΛ W β W⁺
    → WfWorld W⁺
    → Δ′ ∋rep β := ★
    → NonVar A → 0 ∈ᵗ A → 0 ∈ᵗ B′
    → LiftCtxᴶ γ γ′ → Value V
    → W⁺ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᴮ⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  ν⊑ν : ∀ {L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᴮ⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ r → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConvImpᵇ W n n′ → (q : B ⊑ᴮ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {L M′ A C c B B′} {r : `∀ C ⊑ᴮ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ M′ ∶ r → A ⊑ᵂ⟨ W ⟩ ★ → NuTy Δ A C c B
    → (q : B ⊑ᴮ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

  ⟪⟫⊑⟪⟫ : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ}
      {M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᴮ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConvImpᵇ W b b′ → (q : A ⊑ᴮ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  ⟪⟫⊑ : ∀ {Δᵢ} {Wᵢ : World Δᵢ Δ′}
      {M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᴮ⟨ Wᵢ ⟩ A′}
    → Interior W Θ [] Wᵢ → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A → (q : A ⊑ᴮ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

  ⊑⟪⟫ : ∀ {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
      {M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᴮ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′ → (q : A ⊑ᴮ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

------------------------------------------------------------------------
-- 7. The counterexample, repaired
------------------------------------------------------------------------

-- the type index ∀⊑ʸ gives every interior below: `∀X.X→X ⊑ Y→Y` with
-- Y the head center name
q∀ʸ : ∀ {μ m} → (m ∷ μ) ⊢ ∀X⇒X ⊑ᵇ (` 0 ⇒ ` 0)
q∀ʸ = ∀⊑ʸ here nv-⇒ (∈-⇒ˡ ∈-var) (∈-⇒ˡ ∈-var) (⇒⊑⇒ X⊑X X⊑X)

-- 7a. The worlds.  Wk: after the right's Inst TyBeta (β:=★ at rep. var
-- 0, the source pair (αᴸ, αᴿ) = (0, 1) global).  Wʳk: inside the Inst
-- boundary `+Y^β`, Y right-only.  WiK: inside the left `+X^α` and the
-- right `+X^α` (or the merged `+Y^β, +X^α`): Y right-only at the head,
-- X both-sided.  JoinΛ WiK 0 is RestrictedForallBoundary's WX.

Wʳk : World ΔL (reps ΔRk ∣ (0 ∷ []))
Wʳk = Wk ⊕ʳ X⊑X ^ 0

WiK WiK★ : World ΔLᵢ ΔRX
WiK  = world (X⊑X ∷ X⊑X ∷ []) (skip (keep []↪)) (keep (keep []↪))
         ((0 , 1) ∷ []) []
-- the conversion world after the Merge: Y at X⊑★ (a fresh mark, D11)
WiK★ = world (X⊑★ ∷ X⊑X ∷ []) (skip (keep []↪)) (keep (keep []↪))
         ((0 , 1) ∷ []) []

joinK : JoinΛ WiK 0 WX
joinK = join-head

Θ₀-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ []) ⊢ⁱ Θ₀ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
Θ₀-int = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

Θ₂-int : ΔRk ⊢ⁱ Θ₂ ⇒ ΔRX
Θ₂-int = interior (changes∷
  (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))
  (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

Θ₂-conv : ΔRk ⊢ᶜ Θ₂ ⇒ ΔRX
Θ₂-conv = conversion (conv-bind (_ , there here)
  (conv-bind (_ , here) conv[] fresh[] ins-here)
  (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

Wʳk-wf : WfWorld Wʳk
Wʳk-wf = wf-world (right-only joint[]) agree
  (namedᴸ-≤1 Wʳk ≤1-[]) (namedᴿ-≤1 Wʳk ≤1-∷[])
  where
  agree : ∀ {α β} → Paired Wʳk α β → Agree Wʳk α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

WiK-uniqᴿ : ∀ {α β β′} → Paired WiK α β → Paired WiK α β′ → β ≡ β′
WiK-uniqᴿ (inj₁ here⇔) (inj₁ here⇔) = refl
WiK-uniqᴿ (inj₁ here⇔) (inj₁ (there⇔ ()))
WiK-uniqᴿ (inj₁ (there⇔ ())) _
WiK-uniqᴿ (inj₂ ()) _
WiK-uniqᴿ (inj₁ here⇔) (inj₂ ())

WiK-wf : WfWorld WiK
WiK-wf = wf-world (right-only (both (inj₁ here⇔) joint[])) agree
  (namedᴸ-≤1 WiK ≤1-∷[]) (λ _ _ _ → WiK-uniqᴿ)
  where
  agree : ∀ {α β} → Paired WiK α β → Agree WiK α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

-- the Inst boundary `+Y^β` alone (⊑⟪⟫): Y is introduced right-only
IntK-ro : Interior Wk [] Θ₀ Wʳk
IntK-ro = record
  { int-left   = interior changes[]
  ; int-right  = Θ₀-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

-- before the Merge: `+X^α` against the inner `+X^α` (⟪⟫⊑⟪⟫ inside the
-- ⊑⟪⟫); Y continues, right-only
IntK-pre : Interior Wʳk Θ₀ ΘX WiK
IntK-pre = record
  { int-left   = int₀
  ; int-right  = bindX-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ
      { here here _ → (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
      ; here (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ
      { (_ , here) refl here → here
      ; (_ , there here) () _
      ; (_ , there (there ())) _ _
      }
  }

ConvK-pre : ConversionInterior Wʳk Θ₀ ΘX WiK
ConvK-pre = record
  { conv-left       = conv₀
  ; conv-right      = bindX-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
      ; here (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ
      { here here here → here
      ; here (there ()) _
      ; (there here) (there ()) _
      ; (there (there ())) _ _
      }
  }

-- after the Merge: `+X^α` against the merged `+Y^β, +X^α` (⟪⟫⊑⟪⟫);
-- Y is introduced right-only by the boundary itself (β unpaired)
IntK-post : Interior Wk Θ₀ Θ₂ WiK
IntK-post = record
  { int-left   = int₀
  ; int-right  = Θ₂-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ
      { here here _ → (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
      ; here (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ
      { (_ , here) () _
      ; (_ , there here) () _
      ; (_ , there (there ())) _ _
      }
  }

ConvK-post : ConversionInterior Wk Θ₀ Θ₂ WiK★
ConvK-post = record
  { conv-left       = conv₀
  ; conv-right      = Θ₂-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
      ; here (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ { _ () _ }
  }

-- 7b. The conversions.  Before the Merge: `∀Y. (id(Y) → id(Y))` against
-- `id(Y) → id(Y)` (conv-∀⊑ʸ, then the structural clauses).  After it:
-- against the merged `−Y → +Y` (conv-∀⊑ʸ, conv-id⊑seal, conv-id⊑unseal)
cK⊑cId : ConvImpᵇ WiK cK cId
cK⊑cId = conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑ʸ joinK (upC (cId⊑cId X⊑X))))

cK⊑revX : ConvImpᵇ WiK★ cK revX
cK⊑revX =
  conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑ʸ join-head
    (conv-tail⊑tail (conv-mid⊑mid
      (conv-↦⊑↦ (conv-tail⊑tail (conv-id⊑seal refl here))
                (conv-id⊑unseal refl here))))))

-- 7c. THE INTERIOR PREMISE, shared by the pre- and post-Merge pairs: the
-- left Λ takes the right-only Y (Λ⊑ʳ), then λx:Y.x ⊑ λx:Y.x
I⊑idX : WiK ∣ [] ⊢ I ⊑ idX ∶ q∀ʸ
I⊑idX =
  Λ⊑ʳ joinK WX-wf r-here nv-⇒ (∈-⇒ˡ ∈-var) (∈-⇒ˡ ∈-var) liftᴶ-[]
    (V-simple S-ƛ) (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) q∀ʸ

-- before the Merge (RK₃'s argument): ⊑cast, ⊑⟪⟫ (Inst entry), ⟪⟫⊑⟪⟫
VL⊑Nk : Wʳk ∣ [] ⊢ VL ⊑ Nk ∶ q∀ʸ
VL⊑Nk = ⟪⟫⊑⟪⟫ IntK-pre WiK-wf I⊑idX bVL bNR (WiK , ConvK-pre , cK⊑cId) q∀ʸ

VL⊑Rarg₃ : Wk ∣ [] ⊢ VL ⊑ Rarg₃ ∶ up (∀id⊑★ Wk)
VL⊑Rarg₃ =
  ⊑cast (⊑⟪⟫ IntK-ro Wʳk-wf VL⊑Nk bOutK (up (∀id⊑★ Wk)))
    id★↦ᴿk-ty (up (∀id⊑★ Wk))

-- AFTER the Merge (the final value RF; `final-unrelated` for the
-- current relation): ⊑cast, ⟪⟫⊑⟪⟫ absorbing the extra right entry
VL⊑RF : Wk ∣ [] ⊢ VL ⊑ RF ∶ up (∀id⊑★ Wk)
VL⊑RF =
  ⊑cast (⟪⟫⊑⟪⟫ IntK-post WiK-wf I⊑idX bVL bBm (WiK★ , ConvK-post , cK⊑revX)
           (up (∀id⊑★ Wk)))
    id★↦ᴿk-ty (up (∀id⊑★ Wk))

-- 7d. The synchronization pairs of the two runs
--   L: LK →(TyBeta) LK₁ →(Beta) VL
--   R: RK →(TyBeta) RK₁ →(Inst) RK₂ →(TyBeta) RK₃ →(Merge) RK₄ →(Beta) RF
-- (RK₂ is never related: there is no ⊑ν; Inst and TyBeta go together)

νK-conv : NuConvImpᵇ ∅ʷ νK-ty νK-ty
νK-conv = Wν , Wν-conv
  , conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (upC (cId⊑cId X⊑X))))

lk⊑rk : ∅ʷ ∣ [] ⊢ LK ⊑ RK ∶ up (∀id⊑★ ∅ʷ)
lk⊑rk =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ ∅ʷ} tf tf (x⊑x Zʷ))
    (⊑cast
      (ν⊑ν
        (Λ⊑Λ lift-[] (V-simple (S-Λ (V-simple S-ƛ)))
          (V-simple (S-Λ (V-simple S-ƛ)))
          (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
          (∀⊑∀ (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))))
        (ι⊑ι base-ℕ) νK-ty νK-ty νK-conv (up (∀id⊑∀id ∅ʷ)))
      instI₀-ty (up (∀id⊑★ ∅ʷ)))

lk₁⊑rk₁ : Wk1 ∣ [] ⊢ LK₁ ⊑ RK₁ ∶ up (∀id⊑★ Wk1)
lk₁⊑rk₁ =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk1} tf tf (x⊑x Zʷ))
    (⊑cast
      (⟪⟫⊑⟪⟫ Wk1ᵢ-int Wk1ᵢ-wf
        (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
          (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
        bVL bVL
        (Wk1ᵢ , Wk1ᵢ-conv
          , conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (upC (cId⊑cId X⊑X)))))
        (up (∀id⊑∀id Wk1)))
      instI-ty (up (∀id⊑★ Wk1)))

lk₁⊑rk₃ : Wk ∣ [] ⊢ LK₁ ⊑ RK₃ ∶ up (∀id⊑★ Wk)
lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

lk₁⊑rk₄ : Wk ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ up (∀id⊑★ Wk)
lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

-- 7e. The three refuted obligations, met on this pair.

-- Sim at (LK₁, RK₁) and the left's Beta (refuted for the current and
-- the restricted relation by `sim-false`, `simᴿ-false`): the right runs
-- Inst, TyBeta, Merge, Beta to RF
sim-cex : ∃[ N′ ] Σ[ r′ ∈ ΔL ⊢ RK₁ -→* N′ ]
    Σ[ W′ ∈ World ΔL (applyˢ (allocs r′) ΔL) ]
      (Wk1 ⟿[ none ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ ∀X⇒X ⊑ᴮ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ N′ ∶ q)
sim-cex =
  RF , (st₁ then st₂ then st₃ then st₄ then done) , Wk
  , ev-noneᴸ (ev-noneᴿ (ev-R wfᴿ-★ (ev-noneᴿ (ev-noneᴿ ev-done))))
  , Wk-wf , up (∀id⊑★ Wk) , VL⊑RF

-- SimBack at (VL, Rarg₃) and the right's Merge (refuted for the current
-- relation by `simBack-false`): both sides stop (r = r″ = done), the
-- Merge allocates nothing
simBack-cex : (ΔRk ⊢ Rarg₃ -→ RF ∣ none)
  × (Wk ⟿[ [] ∣ none ∷ [] ] Wk) × WfWorld Wk
  × Σ[ q ∈ ∀X⇒X ⊑ᴮ⟨ Wk ⟩ (★ ⇒ ★) ] (Wk ∣ [] ⊢ VL ⊑ RF ∶ q)
simBack-cex = stM , ev-noneᴿ ev-done , Wk-wf , up (∀id⊑★ Wk) , VL⊑RF

-- DGG part 1 on (LK, RK) (refuted by `dgg1-false`, `dgg1ᴿ-false`)
dgg1-cex : ∃[ V′ ] Σ[ r′ ∈ empty ⊢ RK -→* V′ ] Value V′
    × Σ[ W′ ∈ World (applyˢ (allocs LK-run) empty)
                    (applyˢ (allocs r′) empty) ]
        Σ[ q ∈ ∀X⇒X ⊑ᴮ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ V′ ∶ q)
dgg1-cex =
  RF , (st₀ then st₁ then st₂ then st₃ then st₄ then done) , vRF , Wk
  , up (∀id⊑★ Wk) , VL⊑RF

------------------------------------------------------------------------
-- 8. The blocks that used ∀⊑⟪+⟫, without it
------------------------------------------------------------------------

-- the argument `5 ⊑ 5⟨ℕ!⟩`
five⊑ : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ : CtxImp W}
  → W ∣ γ ⊢ $ 5 ⊑ 5⟨ℕ!⟩ ∶ ι⊑★ base-ℕ
five⊑ = ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) (ι⊑★ base-ℕ)

-- 8a. The Inst boundary `+X^α` (α:=★ at rep. var 0) alone, over W₃ and
-- W₁: X right-only with the mark m chosen here (D11)
int-ro₃ : ∀ {m} → Interior W₃ [] Θ₀ (W₃ ⊕ʳ m ^ 0)
int-ro₃ = record
  { int-left   = interior changes[]
  ; int-right  = int₀
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

wf-ro₃ : ∀ {m} → WfWorld (W₃ ⊕ʳ m ^ 0)
wf-ro₃ {m} = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
  (namedᴸ-≤1 (W₃ ⊕ʳ m ^ 0) ≤1-[]) (namedᴿ-≤1 (W₃ ⊕ʳ m ^ 0) ≤1-∷[])

int-ro₁ : Interior W₁ [] Θ₀ (W₁ ⊕ʳ X⊑X ^ 0)
int-ro₁ = record
  { int-left   = interior changes[]
  ; int-right  = int₀
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

wf-ro₁ : WfWorld (W₁ ⊕ʳ X⊑X ^ 0)
wf-ro₁ = wf-world (right-only joint[]) agree
  (namedᴸ-≤1 (W₁ ⊕ʳ X⊑X ^ 0) ≤1-[]) (namedᴿ-≤1 (W₁ ⊕ʳ X⊑X ^ 0) ≤1-∷[])
  where
  agree : ∀ {α β} → Paired (W₁ ⊕ʳ X⊑X ^ 0) α β → Agree (W₁ ⊕ʳ X⊑X ^ 0) α β
  agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑★ base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

-- the left Λ against the right `λx:X.x` inside `+X^α`: Λ⊑ʳ; its premise
-- world is ∀⊑⟪+⟫'s, W ⊕⁺ m ^ 0 (join-⊕⁺), so the old premise is reused
ΛidX⊑idX : ∀ {W : World Δ Δ′} {m}
  → WfWorld (W ⊕⁺ m ^ 0) → reps Δ′ ∋ʳ 0 := bindR ★
  → (W ⊕ʳ m ^ 0) ∣ [] ⊢ I ⊑ idX ∶ q∀ʸ
ΛidX⊑idX wf hβ =
  Λ⊑ʳ join-⊕⁺ wf hβ nv-⇒ (∈-⇒ˡ ∈-var) (∈-⇒ˡ ∈-var) liftᴶ-[] (V-simple S-ƛ)
    (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) q∀ʸ

-- the Inst boundary over it, then the inert `id(★) → id(★)`
B⊑ : ∀ {γ : CtxImp W₃} → W₃ ∣ γ ⊢ I ⊑ B⟨id⟩ ∶ up (∀id⊑★ W₃)
B⊑ =
  ⊑cast (⊑⟪⟫ int-ro₃ wf-ro₃ (ΛidX⊑idX W2⁺-wf r-here) bR-ty (up (∀id⊑★ W₃)))
    id★↦ᴿ-ty (up (∀id⊑★ W₃))

-- 8b. P3 = Ch (block X0)
p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ι⊑★ base-ℕ
p3-inst = ·⊑· (ν⊑ B⊑ ℕ⊑★ νL-ty (up (ℕ⇒ℕ⊑★⇒★ W₃))) five⊑

-- 8c. Cg (block X0): the mark X⊑★, and the right's gen wrapper inside
cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ι⊑★ base-ℕ
cg-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (⊑⟪⟫ int-ro₃ wf-ro₃
          (Λ⊑ʳ join-⊕⁺ Wg⁺-wf r-here nv-⇒ (∈-⇒ˡ ∈-var) (∈-⇒ˡ ∈-var)
            liftᴶ-[] (V-simple S-ƛ)
            (⊑cast
              (⊑⟪⟫ Wg⁻-int Wg⁻-wf
                (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
                I★⁻ᴿ-ty (up (X⇒X⊑★⇒★ {W = W₃ ⊕⁺ X⊑★ ^ 0} here)))
              tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
            q∀ʸ)
          Bg-ty (up (∀id⊑★ W₃)))
        id★↦ᴿ-ty (up (∀id⊑★ W₃)))
      ℕ⊑★ νL-ty (up (ℕ⇒ℕ⊑★⇒★ W₃)))
    five⊑

-- 8d. C2 (block X0): a left GEN-CAST ∀-value.  No Λ⊑ʳ, no JoinΛ: the
-- two casts are related by cast⊑cast at the index ∀⊑ʸ, their sources by
-- ⊑⟪⟫ over the right's unbind of the right-only X (X dropped)
W∅ : World empty ΔR
W∅ = world [] []↪ []↪ [] []

int-unb₃ : ∀ {m} → Interior (W₃ ⊕ʳ m ^ 0) [] (unbind 0 0 ∷ []) W∅
int-unb₃ = record
  { int-left   = interior changes[]
  ; int-right  = unb-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , ()) _ _ }
  }

W∅-wf : WfWorld W∅
W∅-wf = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
  (namedᴸ-≤1 W∅ ≤1-[]) (namedᴿ-≤1 W∅ ≤1-[])

genIᴸ-ty : CastTy empty [] genI (★ ⇒ ★) ∀X⇒X
genIᴸ-ty = proj₂ (proj₂ (cast-inv {Γ = []} I★genI-⊢))

c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ι⊑★ base-ℕ
c2-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (⊑⟪⟫ (int-ro₃ {m = X⊑X}) wf-ro₃
          (cast⊑cast
            (⊑⟪⟫ int-unb₃ W∅-wf (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ))
              I★⁻ᴿ-ty (up (★⇒★ (W₃ ⊕ʳ X⊑X ^ 0))))
            genIᴸ-ty tagᴿ-ty q∀ʸ)
          Bg-ty (up (∀id⊑★ W₃)))
        id★↦ᴿ-ty (up (∀id⊑★ W₃)))
      ℕ⊑★ C2-L-ν-ty (up (ℕ⇒ℕ⊑★⇒★ W₃)))
    five⊑

-- 8e. C12 (block X0)
c12-x0 : W₃ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
c12-x0 =
  ·⊑·
    (ν⊑ν (⊑cast B⊑ genIᴿ-ty (up (∀id⊑∀id W₃)))
      (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , upC (revX⊑revX refl))
      (up (ℕ⇒ℕ W₃)))
    (κ⊑κ lit-$ (ι⊑ι base-ℕ))

-- 8f. L3c: copy 2 of the duplicated Inst boundary, under λy:ℕ ⊑ λy:★
l3c-pre : W₃ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ up (∀id⊑★ W₃)
l3c-pre = ·⊑· {pA = ι⊑★ base-ℕ} (ƛ⊑ƛ {pA = ℕ⊑★} tf tf B⊑) p3-inst

-- 8g. L3d: the second copy, before the left's second TyBeta (world W₁;
-- the premise world W₁ ⊕⁺ X⊑X ^ 0 is ForallBoundaryFixes'
-- post-premise-wf)
l3d-before : W₁ ∣ [] ⊢ L1 ⊑ R3′ ∶ ι⊑★ base-ℕ
l3d-before =
  ·⊑·
    (ν⊑
      (⊑cast
        (⊑⟪⟫ int-ro₁ wf-ro₁ (ΛidX⊑idX post-premise-wf r-here) bR-ty
          (up (∀id⊑★ W₁)))
        id★↦ᴿ-ty (up (∀id⊑★ W₁)))
      ℕ⊑★ νLₗ-ty (up (ℕ⇒ℕ⊑★⇒★ W₁)))
    five⊑

-- 8h. R2c: a left gen-cast value over a boundary value, against the
-- right's Inst boundary before (R2c₄) and after (R2c₅) the right's
-- Merge INSIDE it.  Both by ⊑⟪⟫ and cast⊑cast at ∀⊑ʸ; the Merge only
-- changes the source premise (⊑⟪⟫ ∘ ⟪⟫⊑⟪⟫ becomes one ⟪⟫⊑⟪⟫).

Wʳ4 : World ΔR (ΞR ∣ (0 ∷ []))
Wʳ4 = W4 ⊕ʳ X⊑X ^ 0

Wd4 : World ΔR (ΞR ∣ [])
Wd4 = world [] []↪ []↪ ((0 , 1) ∷ []) []

Wb4 : World ΔRᵢ (ΞR ∣ (1 ∷ []))
Wb4 = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 1) ∷ []) []

Wc4 : World ΔRᵢ (ΞR ∣ (1 ∷ 0 ∷ []))
Wc4 = world (X⊑X ∷ X⊑X ∷ []) (keep (skip []↪)) (keep (keep []↪))
        ((0 , 1) ∷ []) []

int-ro₄ : Interior W4 [] Θ₀ Wʳ4
int-ro₄ = record
  { int-left   = interior changes[]
  ; int-right  = Θ₀-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

wf-ro₄ : WfWorld Wʳ4
wf-ro₄ = wf-world (right-only joint[]) agree
  (namedᴸ-≤1 Wʳ4 ≤1-[]) (namedᴿ-≤1 Wʳ4 ≤1-∷[])
  where
  agree : ∀ {α β} → Paired Wʳ4 α β → Agree Wʳ4 α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) ★⊑★
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

int-unb₄ : Interior Wʳ4 [] (unbind 0 0 ∷ []) Wd4
int-unb₄ = record
  { int-left   = interior changes[]
  ; int-right  = unb-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , ()) _ _ }
  }

Wd4-wf : WfWorld Wd4
Wd4-wf = wf-world joint[] agree (namedᴸ-≤1 Wd4 ≤1-[]) (namedᴿ-≤1 Wd4 ≤1-[])
  where
  agree : ∀ {α β} → Paired Wd4 α β → Agree Wd4 α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) ★⊑★
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

Wb4-wf : WfWorld Wb4
Wb4-wf = wf-world (both (inj₁ here⇔) joint[]) agree
  (namedᴸ-≤1 Wb4 ≤1-∷[]) (namedᴿ-≤1 Wb4 ≤1-∷[])
  where
  agree : ∀ {α β} → Paired Wb4 α β → Agree Wb4 α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) ★⊑★
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

int-b₄ : Interior Wd4 Θ₀ Θ₁ Wb4
int-b₄ = record
  { int-left   = int₀
  ; int-right  = bind₁-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

conv-b₄ : ConversionInterior Wd4 Θ₀ Θ₁ Wb4
conv-b₄ = record
  { conv-left       = conv₀
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

int-m₄ : Interior Wʳ4 Θ₀ Θm Wb4
int-m₄ = record
  { int-left   = int₀
  ; int-right  = Θm-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

conv-m₄ : ConversionInterior Wʳ4 Θ₀ Θm Wc4
conv-m₄ = record
  { conv-left       = conv₀
  ; conv-right      = Θm-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ
      { (there here) here here → there here
      ; here (there ()) _
      ; (there here) (there ()) _
      ; (there (there ())) _ _
      }
  }

-- before the right's Merge: Bα ⊑ [−Y^β] ([+X^α] λx:X.x ⟨…⟩) ⟨…⟩
Bα⊑Nu : Wʳ4 ∣ [] ⊢ Bα ⊑ Nu ∶ up (★⇒★ Wʳ4)
Bα⊑Nu =
  ⊑⟪⟫ int-unb₄ Wd4-wf
    (⟪⟫⊑⟪⟫ int-b₄ Wb4-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bR-ty bBᴿ
      (Wb4 , conv-b₄ , upC (revX⊑revX refl)) (up (★⇒★ Wd4)))
    bUᴿ (up (★⇒★ Wʳ4))

r2c-pre : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₄ ∶ up (∀id⊑★ W4)
r2c-pre =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
    (⊑cast
      (⊑⟪⟫ int-ro₄ wf-ro₄ (cast⊑cast Bα⊑Nu genIᴿ-ty tagNᴿ q∀ʸ) bOut₄
        (up (∀id⊑★ W4)))
      id★↦ᴿ₂-ty (up (∀id⊑★ W4)))

-- after it: Bα ⊑ [+X^α, −Y^β] λx:X.x ⟨…⟩ (one ⟪⟫⊑⟪⟫)
Bα⊑M : Wʳ4 ∣ [] ⊢ Bα ⊑ idX ⟪ Θm , revX ⟫ ∶ up (★⇒★ Wʳ4)
Bα⊑M =
  ⟪⟫⊑⟪⟫ int-m₄ Wb4-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bR-ty bMᴿ
    (Wc4 , conv-m₄ , upC (revX⊑revX refl)) (up (★⇒★ Wʳ4))

r2c-post : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ up (∀id⊑★ W4)
r2c-post =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
    (⊑cast
      (⊑⟪⟫ int-ro₄ wf-ro₄ (cast⊑cast Bα⊑M genIᴿ-ty tagN₀ᴿ q∀ʸ) bOut₅
        (up (∀id⊑★ W4)))
      id★↦ᴿ₂-ty (up (∀id⊑★ W4)))

------------------------------------------------------------------------
-- 8i. Every other mechanized block carries over unchanged
------------------------------------------------------------------------

-- TermImprecision's derivations without ∀⊑⟪+⟫ embed (all other rules
-- are copied verbatim); a ∀⊑⟪+⟫ node gives `nothing`
upNu : ∀ {Δ Δ′ A A′ C C′ c c′ B B′} {W : World Δ Δ′}
  → (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
  → TI.NuConversionImp W n n′ → NuConvImpᵇ W n n′
upNu (nu-ty _ _ _ _ _ _) (nu-ty _ _ _ _ _ _) (Wᶜ , i , c) = Wᶜ , i , upC c

upBdy : ∀ {Δ Δ′ Δᵢ Δ′ᵢ Θ Θ′ Aᵢ A′ᵢ c c′ A A′} {W : World Δ Δ′}
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → TI.BdyConversionImp W b b′ → BdyConvImpᵇ W b b′
upBdy (bdy-ty _ _ _ _ _) (bdy-ty _ _ _ _ _) (Wᶜ , i , c) = Wᶜ , i , upC c

map₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (A → B → C) → Maybe A → Maybe B → Maybe C
map₂ f (just x) (just y) = just (f x y)
map₂ f (just x) nothing  = nothing
map₂ f nothing  _        = nothing

mapᴹ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
mapᴹ f (just x) = just (f x)
mapᴹ f nothing  = nothing

tr : ∀ {W : World Δ Δ′} {γ : CtxImp W} {M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W TI.∣ γ ⊢ M ⊑ M′ ∶ p → Maybe (W ∣ γ ⊢ M ⊑ M′ ∶ up p)
tr (TI.x⊑x x) = just (x⊑x x)
tr (TI.κ⊑κ k p) = just (κ⊑κ k (up p))
tr (TI.ƛ⊑ƛ wA wA′ d) = mapᴹ (ƛ⊑ƛ wA wA′) (tr d)
tr (TI.·⊑· d e) = map₂ ·⊑· (tr d) (tr e)
tr (TI.blame⊑ wA ⊢M p) = just (blame⊑ wA ⊢M (up p))
tr (TI.cast⊑cast d c c′ q) = mapᴹ (λ d′ → cast⊑cast d′ c c′ (up q)) (tr d)
tr (TI.cast⊑ d c q) = mapᴹ (λ d′ → cast⊑ d′ c (up q)) (tr d)
tr (TI.⊑cast d c′ q) = mapᴹ (λ d′ → ⊑cast d′ c′ (up q)) (tr d)
tr (TI.Λ⊑Λ l v v′ d q) = mapᴹ (λ d′ → Λ⊑Λ l v v′ d′ (up q)) (tr d)
tr (TI.Λ⊑ nv occ l v d q) = mapᴹ (λ d′ → Λ⊑ nv occ l v d′ (up q)) (tr d)
tr (TI.∀⊑⟪+⟫ _ _ _ _ _ _ _ _ _) = nothing
tr (TI.ν⊑ν d a n n′ nc q) =
  mapᴹ (λ d′ → ν⊑ν d′ a n n′ (upNu n n′ nc) (up q)) (tr d)
tr (TI.ν⊑ d a n q) = mapᴹ (λ d′ → ν⊑ d′ a n (up q)) (tr d)
tr (TI.⟪⟫⊑⟪⟫ int wf d b b′ bc q) =
  mapᴹ (λ d′ → ⟪⟫⊑⟪⟫ int wf d′ b b′ (upBdy b b′ bc) (up q)) (tr d)
tr (TI.⟪⟫⊑ int wf d b q) = mapᴹ (λ d′ → ⟪⟫⊑ int wf d′ b (up q)) (tr d)
tr (TI.⊑⟪⟫ int wf d b′ q) = mapᴹ (λ d′ → ⊑⟪⟫ int wf d′ b′ (up q)) (tr d)

-- the mechanized blocks of P1, P2, P6, Ch, Cg, C2, C12, C13, C14 (all
-- but the X0 blocks above), and L3c/L3d after the left's TyBeta
carry-p1-init   : Is-just (tr p1-init)
carry-p1-init   = Any.just tt
carry-p1-tybeta : Is-just (tr p1-tybeta)
carry-p1-tybeta = Any.just tt
carry-p2-tybeta : Is-just (tr p2-tybeta)
carry-p2-tybeta = Any.just tt
carry-p6-tybeta : Is-just (tr p6-tybeta)
carry-p6-tybeta = Any.just tt
carry-ch-b0     : Is-just (tr ch-b0)
carry-ch-b0     = Any.just tt
carry-ch-b1     : Is-just (tr ch-b1)
carry-ch-b1     = Any.just tt
carry-cg-b0     : Is-just (tr cg-b0)
carry-cg-b0     = Any.just tt
carry-c2-b0     : Is-just (tr c2-b0)
carry-c2-b0     = Any.just tt
carry-c2-b6     : Is-just (tr c2-b6)
carry-c2-b6     = Any.just tt
carry-c2-b7     : Is-just (tr c2-b7)
carry-c2-b7     = Any.just tt
carry-leaf      : Is-just (tr leaf⊑)
carry-leaf      = Any.just tt
carry-c12-b0    : Is-just (tr c12-b0)
carry-c12-b0    = Any.just tt
carry-c12-b1    : Is-just (tr c12-b1)
carry-c12-b1    = Any.just tt
carry-c13-b1    : Is-just (tr c13-b1)
carry-c13-b1    = Any.just tt
carry-c14-b1    : Is-just (tr c14-b1)
carry-c14-b1    = Any.just tt
carry-ΛI        : Is-just (tr ΛI⊑ΛI)
carry-ΛI        = Any.just tt
carry-l3d-after : Is-just (tr (forget l3d-after))
carry-l3d-after = Any.just tt

-- L3c after the left's TyBeta of copy 1 (world W₁): copy 2 still faces
-- its Inst boundary, by ⊑⟪⟫ and Λ⊑ʳ; copy 1 is Ch B1
B⊑₁ : ∀ {γ : CtxImp W₁} → W₁ ∣ γ ⊢ I ⊑ B⟨id⟩ ∶ up (∀id⊑★ W₁)
B⊑₁ =
  ⊑cast (⊑⟪⟫ int-ro₁ wf-ro₁ (ΛidX⊑idX post-premise-wf r-here) bR-ty
           (up (∀id⊑★ W₁)))
    id★↦ᴿ-ty (up (∀id⊑★ W₁))

l3c-post : W₁ ∣ [] ⊢ L3c₂ ⊑ R3c₃ ∶ up (∀id⊑★ W₁)
l3c-post =
  ·⊑· {pA = ι⊑★ base-ℕ} (ƛ⊑ƛ {pA = ℕ⊑★} tf tf B⊑₁) (from-just (tr ch-b1))

------------------------------------------------------------------------
-- 9. What the simulations need (statements only)
------------------------------------------------------------------------

-- (i) Frames under Λ⊑ʳ (SimBack, CatchupRight, EvolveImp): JoinΛ
-- commutes with the right's allocations.  The right head name's rep.
-- var β is renumbered like any right rep. var.
JoinΛEvolveᴿ : Set
JoinΛEvolveᴿ = ∀ {Δ Δ′} {W : World Δ Δ′} {W⁺ : World (underΛ Δ) Δ′}
    {β ξs′} {W′ : World Δ (applyˢ ξs′ Δ′)}
  → JoinΛ W β W⁺ → W ⟿[ [] ∣ ξs′ ] W′
  → Σ[ W⁺′ ∈ World (underΛ Δ) (applyˢ ξs′ Δ′) ]
      JoinΛ W′ (shiftβ ξs′ β) W⁺′ × (W⁺ ⟿[ [] ∣ ξs′ ] W⁺′)

-- (ii) The right's Inst (CatchupCast and SimBack on `V′⟨inst X.p⟩`):
-- right after Inst and TyBeta the left value V is related, by ⊑⟪⟫, to
-- the RAW interior N′ = inst_X(V′) — no normalization of N′, no
-- Simple, no `¬ ForallBdy`, and the result type is read through ∀⊑ʸ.
-- The proof is by induction on InstX V′ N′ and inversion of V ⊑ V′; it
-- calls no catch-up lemma.  (inst-Λ × Λ⊑Λ: Λ⊑ʳ over the Λ⊑Λ premise
-- moved from W ⊕ X⊑X to allocᴿ ★ W ⊕⁺ m ^ 0, the right abstract rep.
-- var becoming the store's β:=★; inst-Λ × Λ⊑: needs the left-only
-- binder inserted BELOW the pending right-only name, see md §4.)
InstXImpᴿ : Set
InstXImpᴿ = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ N′ B C′}
    {r : B ⊑ᴮ⟨ W ⟩ `∀ C′}
  → WfWorld W → Value V → Value V′ → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m ] Σ[ q ∈ B ⊑ᴮ⟨ allocᴿ ★ W ⊕ʳ m ^ 0 ⟩ C′ ]
      (allocᴿ ★ W ⊕ʳ m ^ 0 ∣ [] ⊢ V ⊑ N′ ∶ q)

-- (iii) The left's later TyBeta catching up (ev-L⇔): the left opens V
-- at the name the right-only head joins.  Then ev-L⇔ turns W⁺'s
-- lexical (0, β) into a global (α, β), as for ∀⊑⟪+⟫ (L3c, L3d).
InstXImpᴸ : Set
InstXImpᴸ = ∀ {Δ Δ′} {W : World Δ Δ′} {W⁺ : World (underΛ Δ) Δ′}
    {β V N M′ A B′} {q : `∀ A ⊑ᴮ⟨ W ⟩ B′}
  → JoinΛ W β W⁺ → Value V → InstX V N
  → W ∣ [] ⊢ V ⊑ M′ ∶ q
  → Σ[ r ∈ A ⊑ᴮ⟨ W⁺ ⟩ B′ ] (W⁺ ∣ [] ⊢ N ⊑ M′ ∶ r)

-- (iv) The premise world: Λ⊑ʳ carries `WfWorld W⁺`.  Where Λ⊑ʳ is
-- created it is wf-⊕⁺'s condition, NoNamedPartner, which a right-only
-- name has: a left NAMED partner of β would have been joined to it by
-- Interior's join-fresh.
WfJoin : Set
WfJoin = ∀ {Δ Δ′} {W : World Δ Δ′} {W⁺ : World (underΛ Δ) Δ′} {β}
  → JoinΛ W β W⁺ → WfWorld W → Δ′ ∋rep β := ★ → NoNamedPartner W β
  → WfWorld W⁺

-- (v) Binder matching under ∀⊑ (Λ⊑ outside, the right's Inst opening
-- the right's outer binder): the left-only name must sit BELOW the
-- pending right-only head, or JoinΛ (head only, order-preserving
-- embeddings) cannot reach it.  The world of the needed Λ⊑ variant:
data UnderRO {Δ : Ctxᵗ}
    : ∀ {Δ′} → World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  under-head : ∀ {Ξ′ η′ β μ m} {ι : names Δ ↪ μ} {ι′ : η′ ↪ μ}
      {ϱᵍ ϱˡ : RepRel}
    → UnderRO {Δ′ = Ξ′ ∣ (β ∷ η′)} (world (m ∷ μ) (skip ι) (keep ι′) ϱᵍ ϱˡ)
        (world (m ∷ X⊑★ ∷ μ) (skip (keep (relabel suc ι))) (keep (skip ι′))
               (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ))

-- It is the world InstXImpᴿ's IH produces for Λ⊑'s premise,
-- (allocᴿ ★ (W ⊕ᴸ)) ⊕ʳ m ^ 0, up to commuting shiftᴸ and shiftᴿ on ϱ
-- (equal as lists, not definitionally).
