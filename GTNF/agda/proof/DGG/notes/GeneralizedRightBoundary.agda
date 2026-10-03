module proof.DGG.notes.GeneralizedRightBoundary where

-- File Charter:
--   * HISTORICAL: written against the relation before design.md D26
--     (2026-10-03), which removed `∀⊑⟪+⟫` and generalized `⊑⟪⟫` with
--     `Opens`.  It no longer type-checks against TermImprecision (it, or
--     a note it imports, uses the old rule) and is excluded from every
--     check: All.agda does not import it and it is not a *Proof.agda.
--     This is the checked LOCAL COPY of the rule that D26 ADOPTED; the
--     rule now lives in TermImprecision.agda (with `Join↪`/`Open1` in
--     ImprecisionWorld.agda), its §3 blocks in examples/, and its §4
--     counterexample K in examples/TermImprecisionRegressionExamples.
--     It last checked at commit 1281c636.
--   * THE PROPOSAL CHECKED HERE: one right-only boundary rule ⊑⟪⟫ that
--     covers plain right-only boundaries, ∀⊑⟪+⟫ and the merged case of
--     the boundary-Merge counterexample (RestrictedForallBoundary §3).
--     The rule may OPEN the left ∀-value inside the right boundary:
--     its binder joins a name that the right boundary δ′ introduces,
--     bound to a ★ rep. var.  ∀⊑⟪+⟫ is removed; type imprecision is
--     unchanged.  Findings in GeneralizedRightBoundary.md.  NOT a Def
--     module, not imported by All.agda; nothing outside this file and
--     its .md is edited.
--   * §1 `Join↪`, `Open1`, `Opens` (the openings, D22's side
--     conditions included), and the LOCAL COPY of the relation:
--     TermImprecision MINUS ∀⊑⟪+⟫, with ⊑⟪⟫ generalized.
--   * §2 ∀⊑⟪+⟫ is admissible (one opening at name 0), given the two
--     facts the old rule lacked: the right-only interior world and the
--     premise world's WfWorld.  `tr` embeds TermImprecision, failing
--     only at ∀⊑⟪+⟫ nodes; the blocks without ∀⊑⟪+⟫ carry over.
--   * §3 the seven blocks that used ∀⊑⟪+⟫ (P3 = Ch, Cg, C2, C12, L3c,
--     L3d, R2c before and after the right's Merge), re-derived.
--   * §4 the counterexample K: every synchronization pair, including
--     the final one, with Sim, SimBack (at the right's Inst and at its
--     Merge) and DGG part 1 met; and FixA's K2 (the left's later
--     TyBeta).
--   * §5 syntax-directedness on K: zero openings are impossible, the
--     opening is forced to name 0 and to the InstX image; and the
--     boundary-order freedom (left boundary first) gives a second
--     derivation of the final pair.
--   * §6 statements (only) of what the simulations need.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
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
open import TermSubst using (↑ᴮ[_])
open import Reduction
  using (InstX; inst-Λ; inst-gen; inst-∀; inst-⟪⟫; _⊢_-→_∣_; _⊢_-→*_;
         done; _then_)
open import Imprecision
open import ImprecisionWorld
open import proof.ImprecisionWorld
  using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[]; NoNamedPartner)
open import ConversionImprecision
import TermImprecision as TI
open TI
  using (Lit; lit-$; CastTy; cast-ty; NuTy; BdyTy; NuConversionImp;
         BdyConversionImp; ⟪⟫-inv; cast-inv; ν-inv)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; ev-done; ev-R; ev-noneᴸ; ev-noneᴿ; applyˢ; allocs)
open import examples.TypeCheck using (tc; tf)

private
  variable
    Δ Δ′ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Openings, and the relation
------------------------------------------------------------------------

-- `Join↪ ι ι′ ι⁺ k`: the left's NEW name 0 (an opened binder) is kept
-- into the center name of the right's name k, which is RIGHT-ONLY;
-- the center names before it are right-only names too (the left skips
-- them), so the left's order is preserved.  `ι⁺` is the left embedding
-- after the opening.  This is FixB's `JoinΛ` (k = 0) at any position.
data Join↪ {η : TyCtx}
    : ∀ {η′ μ} → η ↪ μ → η′ ↪ μ → (zero ∷ map suc η) ↪ μ → ℕ → Set where
  join-here : ∀ {β η′ μ m} {ι : η ↪ μ} {ι′ : η′ ↪ μ}
    → Join↪ (skip {m = m} ι) (keep {α = β} ι′) (keep (relabel suc ι)) zero
  join-there : ∀ {β η′ μ m k} {ι : η ↪ μ} {ι′ : η′ ↪ μ}
      {ι⁺ : (zero ∷ map suc η) ↪ μ}
    → Join↪ ι ι′ ι⁺ k
    → Join↪ (skip {m = m} ι) (keep {α = β} ι′) (skip ι⁺) (suc k)

-- One opening.  The left opens a binder (a Λ-like abstract rep. var
-- at 0, as `underΛ`); its name joins the right name k, whose rep. var
-- β is bound to ★; the left abstract rep. var is paired with β
-- LEXICALLY (D16).  `W ⊕⁺ m ^ β` is the case k = 0 of `W ⊕ʳ m ^ β`
-- (`open-⊕` below).
data Open1 {Δ Δ′ : Ctxᵗ}
    : World Δ Δ′ → ℕ → World (underΛ Δ) Δ′ → Set where
  open1 : ∀ {μ ϱᵍ ϱˡ k β} {ι : names Δ ↪ μ} {ι′ : names Δ′ ↪ μ}
      {ι⁺ : names (underΛ Δ) ↪ μ}
    → Join↪ ι ι′ ι⁺ k
    → Δ′ ∋ᵗ k := β
    → Δ′ ∋rep β := ★
    → Open1 (world μ ι ι′ ϱᵍ ϱˡ) k
            (world μ ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ))

-- `Opens Θ′ W M A W⁺ M₀ A₀`: M (at type A, world W) seen from inside
-- the right boundary Θ′: M itself (no opening), or M a ∀-value whose
-- binder is opened, M₀ the opening of `inst_X(M)`, at a name that Θ′
-- introduces (`Fresh Θ′ k`).  D22's side conditions (`NonVar A`,
-- `0 ∈ᵗ A`) and the left typing of the opened value (not recoverable
-- from its InstX image) are premises of each opening.  The right
-- context does not change.
data Opens {Δ′ : Ctxᵗ} (Θ′ : Boundary)
    : ∀ {Δ Δ⁺} → World Δ Δ′ → Term → Ty → World Δ⁺ Δ′ → Term → Ty
    → Set where
  open-none : ∀ {Δ} {W : World Δ Δ′} {M A}
    → Opens Θ′ W M A W M A
  open-∀ : ∀ {Δ Δ⁺ k} {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
      {W⁺ : World Δ⁺ Δ′} {V N M₀ A A₀}
    → NonVar A
    → 0 ∈ᵗ A
    → Value V
    → Δ ∣ [] ⊢ V ⦂ `∀ A
    → InstX V N
    → Fresh Θ′ k
    → Open1 W k W₁
    → Opens Θ′ W₁ N A W⁺ M₀ A₀
    → Opens Θ′ W V (`∀ A) W⁺ M₀ A₀

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

  -- (∀⊑⟪+⟫ is REMOVED)

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

  -- THE GENERALIZED RIGHT-ONLY BOUNDARY RULE.  Wᵢ is the right
  -- boundary's interior world (any δ′, as before); M is seen from
  -- inside through `Opens` (zero openings: the old ⊑⟪⟫; one opening at
  -- the boundary's own `bind 0 β`: the old ∀⊑⟪+⟫; an opening at a
  -- name of a merged boundary: the counterexample's final pair).  The
  -- premise world Wᵢ⁺ must be well formed.
  ⊑⟪⟫ : ∀ {Δ′ᵢ Δ⁺} {Wᵢ : World Δ Δ′ᵢ} {Wᵢ⁺ : World Δ⁺ Δ′ᵢ}
      {M M₀ M′ Θ′ c′ A A₀ A′ᵢ A′} {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ
    → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
    → WfWorld Wᵢ⁺
    → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

------------------------------------------------------------------------
-- 2. ∀⊑⟪+⟫ is admissible; the embedding of TermImprecision
------------------------------------------------------------------------

open import proof.DGG.notes.FixB-BoundaryAbsorbs using (_⊕ʳ_^_)

-- ∀⊑⟪+⟫'s premise world is the opening, at name 0, of the right-only
-- interior world of its boundary `bind 0 β`
open-⊕ : ∀ {W : World Δ Δ′} {m β}
  → Δ′ ∋rep β := ★ → Open1 (W ⊕ʳ m ^ β) 0 (W ⊕⁺ m ^ β)
open-⊕ hβ = open1 join-here here hβ

-- the old rule, from the new one: its premises, plus the two facts it
-- did not carry (the interior world of `bind 0 β`, in which the new
-- name is right-only, and the premise world's WfWorld; both are open
-- questions of CatchupRightChildren.md, 3)
∀⊑⟪+⟫-adm : ∀ {W : World Δ Δ′} {γ : CtxImp W}
    {V N V′ β m c′ A A′ B′} {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
  → NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ [] ⊢ V ⦂ `∀ A → InstX V N
  → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
  → Δ′ ∋rep β := ★
  → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
  → Interior W [] (bind 0 β ∷ []) (W ⊕ʳ m ^ β)
  → WfWorld (W ⊕⁺ m ^ β)
  → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
  → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q
∀⊑⟪+⟫-adm nv occ v ⊢V i d hβ b int wf q =
  ⊑⟪⟫ int (open-∀ nv occ v ⊢V i refl (open-⊕ hβ) open-none) wf d b q

-- TermImprecision's derivations embed, except at ∀⊑⟪+⟫ nodes
-- (`nothing`); every other rule is copied, ⊑⟪⟫ with no opening
mapᴹ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
mapᴹ f (just x) = just (f x)
mapᴹ f nothing  = nothing

map₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (A → B → C) → Maybe A → Maybe B → Maybe C
map₂ f (just x) (just y) = just (f x y)
map₂ f (just x) nothing  = nothing
map₂ f nothing  _        = nothing

tr : ∀ {W : World Δ Δ′} {γ : CtxImp W} {M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W TI.∣ γ ⊢ M ⊑ M′ ∶ p → Maybe (W ∣ γ ⊢ M ⊑ M′ ∶ p)
tr (TI.x⊑x x) = just (x⊑x x)
tr (TI.κ⊑κ k p) = just (κ⊑κ k p)
tr (TI.ƛ⊑ƛ wA wA′ d) = mapᴹ (ƛ⊑ƛ wA wA′) (tr d)
tr (TI.·⊑· d e) = map₂ ·⊑· (tr d) (tr e)
tr (TI.blame⊑ wA ⊢M p) = just (blame⊑ wA ⊢M p)
tr (TI.cast⊑cast d c c′ q) = mapᴹ (λ d′ → cast⊑cast d′ c c′ q) (tr d)
tr (TI.cast⊑ d c q) = mapᴹ (λ d′ → cast⊑ d′ c q) (tr d)
tr (TI.⊑cast d c′ q) = mapᴹ (λ d′ → ⊑cast d′ c′ q) (tr d)
tr (TI.Λ⊑Λ l v v′ d q) = mapᴹ (λ d′ → Λ⊑Λ l v v′ d′ q) (tr d)
tr (TI.Λ⊑ nv occ l v d q) = mapᴹ (λ d′ → Λ⊑ nv occ l v d′ q) (tr d)
tr (TI.∀⊑⟪+⟫ _ _ _ _ _ _ _ _ _) = nothing
tr (TI.ν⊑ν d a n n′ nc q) = mapᴹ (λ d′ → ν⊑ν d′ a n n′ nc q) (tr d)
tr (TI.ν⊑ d a n q) = mapᴹ (λ d′ → ν⊑ d′ a n q) (tr d)
tr (TI.⟪⟫⊑⟪⟫ int wf d b b′ bc q) =
  mapᴹ (λ d′ → ⟪⟫⊑⟪⟫ int wf d′ b b′ bc q) (tr d)
tr (TI.⟪⟫⊑ int wf d b q) = mapᴹ (λ d′ → ⟪⟫⊑ int wf d′ b q) (tr d)
tr (TI.⊑⟪⟫ int wf d b′ q) =
  mapᴹ (λ d′ → ⊑⟪⟫ int open-none wf d′ b′ q) (tr d)

-- the mechanized blocks without ∀⊑⟪+⟫ (P1, P2, P6, Ch, Cg, C2, C12,
-- C13, C14, and L3d after the left's second TyBeta) carry over
open import examples.TermImprecisionExamples
  using (p1-init; p1-tybeta; p2-tybeta; p6-tybeta)
open import examples.TermImprecisionRebaseExamples
  using (c12-b1; leaf⊑; c2-b6; c2-b7; c13-b1; c14-b1; ΛI⊑ΛI; ch-b0; cg-b0;
         c2-b0; c12-b0; ch-b1)
import proof.DGG.notes.RestrictedForallBoundary as R

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
carry-l3d-after : Is-just (tr (R.forget R.l3d-after))
carry-l3d-after = Any.just tt

-- ... and `tr` fails exactly at the four example derivations with a
-- ∀⊑⟪+⟫ node (re-derived in §3)
import examples.TermImprecisionExamples as TIE
import examples.TermImprecisionRebaseExamples as TIR

fail-p3  : tr TIE.p3-inst ≡ nothing
fail-p3  = refl
fail-cg  : tr TIR.cg-x0 ≡ nothing
fail-cg  = refl
fail-c2  : tr TIR.c2-x0 ≡ nothing
fail-c2  = refl
fail-c12 : tr TIR.c12-x0 ≡ nothing
fail-c12 = refl

------------------------------------------------------------------------
-- 3. The seven blocks that used ∀⊑⟪+⟫
------------------------------------------------------------------------

open import examples.CambridgeExamples using (I; instI; genI; C2-L; C12-L)
open import examples.ImprecisionExamples using (L1)
open import examples.TermImprecisionExamples
  using (idX; revX; ℕ⊑★; 5⟨ℕ!⟩; Θ₀; L1′; ΔL; ΔR; ΔLᵢ; W₁; Wᵢ₁-int;
         Wᵢ₁-wf; bL-ty; bR-ty; bLR-conv; revX⊑revX; νL-ty; W₃; R3′)
open import examples.TermImprecisionRebaseExamples
  using (id★↦; id★→; tagX↦; ∀id⊑★; ∀id⊑∀id; ★⇒★; ℕ⇒ℕ; ℕ⇒ℕ⊑★⇒★;
         id★→⊑id★→; X⇒X⊑★⇒★; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty; id★↦ᴿ-ty; ΛidX-⊢;
         Cg-R₂; Wg⁺; Wg⁺-wf; Wg⁻-int; Wg⁻-wf; I★genI-⊢; C2-L-ν-ty; W2⁺;
         W2⁺-wf; W2⁻-int; W2⁻-wf; W2⁺-conv; I★⁻ᴸ-ty; tagᴸ-ty; C12-R₂;
         C12-ν₂-ty; genIᴿ-ty; Wν₂; Wν₂-conv)
open import proof.DGG.notes.ForallBoundaryFixes
  using (B⟨id⟩; L3c₁; L3c₂; R3c₃; post-premise-wf; wf-premise; νLₗ-ty; W₂d;
         Wᵢ₂d-int; Wᵢ₂d-wf; bL₂-ty; bLR₂-conv; L2c₂; R2c₄; R2c₅; N; N₀;
         vV2; V2-⊢; instV2; W4; Pw; Pu; Pu-wf; Iu; Ib; Ibc; Pb; Pb-wf;
         unb-conv-self; bBᴸ; bBᴿ; bUᴸ; bUᴿ; tagNᴸ; tagNᴿ; bOut₄; Iu′;
         Pu′; Pu′-wf; Ib′; Pc′; Ibc′; bMᴿ; tagN₀ᴿ; bOut₅; id★↦ᴿ₂-ty)
open import proof.DGG.notes.FixB-BoundaryAbsorbs
  using (int-ro₃; int-ro₁; int-ro₄)

five⊑ : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ : CtxImp W}
  → W ∣ γ ⊢ $ 5 ⊑ 5⟨ℕ!⟩ ∶ ℕ⊑★
five⊑ = ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

-- the opening of the left value `ΛX. λx:X. x` at name 0 (inst-Λ)
openI : ∀ {Ξ} {W : World (Ξ ∣ []) Δ′} {W₁ : World (underΛ (Ξ ∣ [])) Δ′}
  → (Ξ ∣ []) ∣ [] ⊢ I ⦂ `∀ (` 0 ⇒ ` 0)
  → Open1 W 0 W₁
  → Opens (bind 0 0 ∷ []) W I (`∀ (` 0 ⇒ ` 0)) W₁ idX (` 0 ⇒ ` 0)
openI ⊢I o =
  open-∀ nv-⇒ (∈-⇒ˡ ∈-var) (V-simple (S-Λ (V-simple S-ƛ))) ⊢I
    (inst-Λ (V-simple S-ƛ)) refl o open-none

idX⊑idX : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W}
  → (p : ` 0 ⊑ᵂ⟨ W ⟩ ` 0)
  → Δ ⊢ᵗ ` 0 → Δ′ ⊢ᵗ ` 0
  → W ∣ γ ⊢ idX ⊑ idX ∶ ⇒⊑⇒ p p
idX⊑idX p wA wA′ = ƛ⊑ƛ wA wA′ (x⊑x Zʷ)

-- P3 = Ch (block X0): the Inst boundary `+X^α` over λx:X.x; one
-- opening of the left ΛX.λx:X.x at the boundary's name
p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
p3-inst =
  ·⊑· (ν⊑ (⊑cast (⊑⟪⟫ int-ro₃ (openI ΛidX-⊢ (open-⊕ r-here)) W2⁺-wf
                    (idX⊑idX X⊑X tf tf) bR-ty (∀id⊑★ W₃))
                 id★↦ᴿ-ty (∀id⊑★ W₃))
          ℕ⊑★ νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

-- examples' ch-x0 is p3-inst (Ch-L is L1)
open import examples.CambridgeExamples using (Ch-L)

ch-x0 : W₃ ∣ [] ⊢ Ch-L ⊑ R3′ ∶ ℕ⊑★
ch-x0 = p3-inst

-- Cg (block X0): mark X⊑★, the right's gen wrapper inside
cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ℕ⊑★
cg-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (⊑⟪⟫ int-ro₃ (openI ΛidX-⊢ (open-⊕ r-here)) Wg⁺-wf
          (⊑cast
            (⊑⟪⟫ Wg⁻-int open-none Wg⁻-wf
              (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
              I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = Wg⁺} here))
            tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
          Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

-- C2 (block X0): a left GEN-CAST ∀-value, opened by inst-gen (FixB
-- needed cast⊑cast at its new type clause here; the opening needs
-- nothing new)
c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ℕ⊑★
c2-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (⊑⟪⟫ int-ro₃
          (open-∀ nv-⇒ (∈-⇒ˡ ∈-var)
            (V-simple (S-cast (V-simple S-ƛ) I-gen)) I★genI-⊢
            (inst-gen (V-simple S-ƛ)) refl (open-⊕ r-here) open-none)
          W2⁺-wf
          (cast⊑cast
            (⟪⟫⊑⟪⟫ W2⁻-int W2⁻-wf
              (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ))
              I★⁻ᴸ-ty I★⁻ᴿ-ty
              (W2⁺ , W2⁺-conv , id★→⊑id★→) (★⇒★ W2⁺))
            tagᴸ-ty tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
          Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

-- C12 (block X0)
c12-x0 : W₃ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
c12-x0 =
  ·⊑·
    (ν⊑ν
      (⊑cast
        (⊑cast
          (⊑⟪⟫ int-ro₃ (openI ΛidX-⊢ (open-⊕ r-here)) W2⁺-wf
            (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
            bR-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        genIᴿ-ty (∀id⊑∀id W₃))
      (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , revX⊑revX refl)
      (ℕ⇒ℕ W₃))
    (κ⊑κ lit-$ (ι⊑ι base-ℕ))

-- L3c: copy 2 of the duplicated Inst boundary, under λy:ℕ ⊑ λy:★, at
-- any exterior world with the right-only interior and the opening
copy2 : ∀ {Ξ} {W : World (Ξ ∣ []) ΔR}
  → (Ξ ∣ []) ∣ [] ⊢ I ⦂ `∀ (` 0 ⇒ ` 0)
  → Interior W [] Θ₀ (W ⊕ʳ X⊑X ^ 0)
  → WfWorld (W ⊕⁺ X⊑X ^ 0)
  → W ∣ ctx-imp `ℕ ★ ℕ⊑★ ∷ [] ⊢ I ⊑ B⟨id⟩ ∶ ∀id⊑★ W
copy2 {W = W} ⊢I int wf =
  ⊑cast (⊑⟪⟫ int (openI ⊢I (open-⊕ r-here)) wf (idX⊑idX X⊑X tf tf) bR-ty
           (∀id⊑★ W))
        id★↦ᴿ-ty (∀id⊑★ W)

-- before the left's TyBeta of copy 1 (world W₃) ...
l3c-pre : W₃ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ ∀id⊑★ W₃
l3c-pre = ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 tc int-ro₃ W2⁺-wf)) p3-inst

-- ... and after it (world W₁)
l3c-post : W₁ ∣ [] ⊢ L3c₂ ⊑ R3c₃ ∶ ∀id⊑★ W₁
l3c-post =
  ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 tc int-ro₁ post-premise-wf))
    (·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
          (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
          bL-ty bR-ty bLR-conv (ℕ⇒ℕ⊑★⇒★ W₁))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ W₁))
      five⊑)

-- L3d: the second copy, before (W₁) and after (W₂d) the left's second
-- TyBeta
l3d-before : W₁ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
l3d-before =
  ·⊑· (ν⊑ (⊑cast (⊑⟪⟫ int-ro₁ (openI tc (open-⊕ r-here)) post-premise-wf
                    (idX⊑idX X⊑X tf tf) bR-ty (∀id⊑★ W₁))
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

-- R2c: a left gen-cast value over a boundary value (V2), against the
-- right's Inst boundary before (R2c₄) and after (R2c₅) the right's
-- Merge INSIDE it.  Both by ⊑⟪⟫ with one opening (inst-gen); the
-- Merge changes only the premise (two nested ⟪⟫⊑⟪⟫ become one).
W4-wf : WfWorld W4
W4-wf = wf-world joint[] agree (namedᴸ-≤1 W4 ≤1-[]) (namedᴿ-≤1 W4 ≤1-[])
  where
  agree : ∀ {α β} → Paired W4 α β → Agree W4 α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) ★⊑★
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

Pw-wf : WfWorld Pw
Pw-wf = wf-premise W4-wf r-here (λ { (_ , ()) })

openV2 : Opens (bind 0 0 ∷ []) (W4 ⊕ʳ X⊑X ^ 0) _ (`∀ (` 0 ⇒ ` 0)) Pw N
  (` 0 ⇒ ` 0)
openV2 =
  open-∀ nv-⇒ (∈-⇒ˡ ∈-var) vV2 V2-⊢ instV2 refl (open-⊕ r-here) open-none

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
    (⊑cast (⊑⟪⟫ int-ro₄ openV2 Pw-wf N⊑N bOut₄ (∀id⊑★ W4))
           id★↦ᴿ₂-ty (∀id⊑★ W4))

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
    (⊑cast (⊑⟪⟫ int-ro₄ openV2 Pw-wf N⊑N₀ bOut₅ (∀id⊑★ W4))
           id★↦ᴿ₂-ty (∀id⊑★ W4))

------------------------------------------------------------------------
-- 4. The counterexample K, and K2 (the left's later TyBeta)
------------------------------------------------------------------------

--   L  (λf:∀X.X→X. f) (K[ℕ])        K = ΛY.ΛX.λx:X.x
--   R  (λf:★→★.    f) (K[ℕ]⟨inst⟩)
-- L: TyBeta, Beta.  R: TyBeta, Inst, TyBeta, Merge, Beta.

open R
  using (KK; cId; cK; ∀X⇒X; VL; Nk; Rarg₃; Bm; RF; LK; LK₁; RK; RK₁; RK₂;
         RK₃; RK₄; ΔRk; wfΔL; wfΔRk; vVL; vRF; Wk; Wk-wf; PwK; ΘX; ΔLX;
         ΔRX; WX; WX-int; WX-conv; WX-wf; bindX-int; instVL; bNL; bNR;
         bOutK; bBm; id★↦ᴿk-ty; VL-⊢; Θ₂; cId⊑cId; Wk1; Wk1-wf; bVL; st₀;
         st₁; st₂; st₃; st₄; stM; stL; stL₀; var⊑var; ⊕ᴸ-¬joins)
open import proof.DGG.notes.FixB-BoundaryAbsorbs using (IntK-ro; Θ₀-int)
import proof.DGG.notes.FixA-MergedBoundary as A
open A
  using (int-Θ₂; LK2; LK2₁; LK2₂; LK2₃; νL2-ty; ΔL2; Wk2; ev2; Wk2-wf;
         stL2₂; stL2₃; LK2-run)

-- 4a. Before the right's Merge (RK₃): the Inst boundary `+Y^β` over the
-- boundary value Nk.  One opening (inst-⟪⟫ of VL) at name 0; the
-- premise is the old cexK's `Nk ⊑ Nk`.
PwK-wf : WfWorld PwK
PwK-wf = wf-premise Wk-wf r-here (λ { (_ , ()) })

openVLₖ : Opens Θ₀ (Wk ⊕ʳ X⊑X ^ 0) VL ∀X⇒X PwK Nk (` 0 ⇒ ` 0)
openVLₖ =
  open-∀ nv-⇒ (∈-⇒ˡ ∈-var) vVL VL-⊢ instVL refl (open-⊕ r-here) open-none

Nk⊑Nk : PwK ∣ [] ⊢ Nk ⊑ Nk ∶ ⇒⊑⇒ X⊑X X⊑X
Nk⊑Nk =
  ⟪⟫⊑⟪⟫ WX-int WX-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bNL bNR
    (WX , WX-conv , cId⊑cId X⊑X) (⇒⊑⇒ X⊑X X⊑X)

VL⊑Rarg₃ : Wk ∣ [] ⊢ VL ⊑ Rarg₃ ∶ ∀id⊑★ Wk
VL⊑Rarg₃ =
  ⊑cast (⊑⟪⟫ IntK-ro openVLₖ PwK-wf Nk⊑Nk bOutK (∀id⊑★ Wk))
    id★↦ᴿk-ty (∀id⊑★ Wk)

-- 4b. AFTER the right's Merge (RK₄, RF): the merged `+Y^β, +X^αᴿ` over
-- λx:Y.x.  Interior world WiR: both right names right-only.  One
-- opening of VL at name 0 (Y, β:=★): the premise world WoK.  The
-- premise is `Nk ⊑ idX` by ⟪⟫⊑: the left's inner `+X^αᴸ` is now
-- left-only, and its name joins the right's X (introduced by the merged
-- boundary) through the global pair (αᴸ, αᴿ).
WiR : World ΔL ΔRX
WiR = world (X⊑X ∷ X⊑X ∷ []) (skip (skip []↪)) (keep (keep []↪))
        ((0 , 1) ∷ []) []

WoK : World (underΛ ΔL) ΔRX
WoK = world (X⊑X ∷ X⊑X ∷ []) (keep (skip []↪)) (keep (keep []↪))
        ((1 , 1) ∷ []) ((0 , 0) ∷ [])

IntK-Θ₂ : Interior Wk [] Θ₂ WiR
IntK-Θ₂ = record
  { int-left   = interior changes[]
  ; int-right  = int-Θ₂
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ
      { (_ , here) () _ ; (_ , there here) () _
      ; (_ , there (there ())) _ _ }
  }

-- the opening joins the left's opened binder to right name 0 (Y)
openK : Open1 WiR 0 WoK
openK = open1 join-here here r-here

openVL : Opens Θ₂ WiR VL ∀X⇒X WoK Nk (` 0 ⇒ ` 0)
openVL = open-∀ nv-⇒ (∈-⇒ˡ ∈-var) vVL VL-⊢ instVL refl openK open-none

-- WX's two lexical/global pairs are those of WoK (same ϱ)
uniqᴸK : ∀ {α α′ β} → Paired WX α β → Paired WX α′ β → α ≡ α′
uniqᴸK (inj₁ here⇔) (inj₁ here⇔) = refl
uniqᴸK (inj₁ here⇔) (inj₁ (there⇔ ()))
uniqᴸK (inj₁ (there⇔ ())) _
uniqᴸK (inj₂ here⇔) (inj₂ here⇔) = refl
uniqᴸK (inj₂ here⇔) (inj₂ (there⇔ ()))
uniqᴸK (inj₂ (there⇔ ())) _
uniqᴸK (inj₁ here⇔) (inj₂ (there⇔ ()))
uniqᴸK (inj₂ here⇔) (inj₁ (there⇔ ()))

uniqᴿK : ∀ {α β β′} → Paired WX α β → Paired WX α β′ → β ≡ β′
uniqᴿK (inj₁ here⇔) (inj₁ here⇔) = refl
uniqᴿK (inj₁ here⇔) (inj₁ (there⇔ ()))
uniqᴿK (inj₁ (there⇔ ())) _
uniqᴿK (inj₂ here⇔) (inj₂ here⇔) = refl
uniqᴿK (inj₂ here⇔) (inj₂ (there⇔ ()))
uniqᴿK (inj₂ (there⇔ ())) _
uniqᴿK (inj₁ here⇔) (inj₂ (there⇔ ()))
uniqᴿK (inj₂ here⇔) (inj₁ (there⇔ ()))

WoK-wf : WfWorld WoK
WoK-wf = wf-world (both (inj₂ here⇔) (right-only joint[])) agree
  (λ _ _ _ → uniqᴸK) (λ _ _ _ → uniqᴿK)
  where
  agree : ∀ {α β} → Paired WoK α β → Agree WoK α β
  agree (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))

-- inside the left's inner `+X^αᴸ` (left-only): the interior world is
-- RestrictedForallBoundary's WX
IntK-X : Interior WoK ΘX [] WX
IntK-X = record
  { int-left   = bindX-int
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
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
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

Nk⊑idX : WoK ∣ [] ⊢ Nk ⊑ idX ∶ ⇒⊑⇒ X⊑X X⊑X
Nk⊑idX =
  ⟪⟫⊑ IntK-X WX-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bNL (⇒⊑⇒ X⊑X X⊑X)

-- THE FINAL ARGUMENT PAIR (RestrictedForallBoundary's `final-unrelated`
-- for the current relation)
VL⊑Bm : Wk ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk
VL⊑Bm = ⊑⟪⟫ IntK-Θ₂ openVL WoK-wf Nk⊑idX bBm (∀id⊑★ Wk)

VL⊑RF : Wk ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk
VL⊑RF = ⊑cast VL⊑Bm id★↦ᴿk-ty (∀id⊑★ Wk)

-- 4c. The synchronization pairs
lk⊑rk : ∅ʷ ∣ [] ⊢ LK ⊑ RK ∶ ∀id⊑★ ∅ʷ
lk⊑rk = from-just (tr (R.forget R.lk⊑rk))

lk₁⊑rk₁ : Wk1 ∣ [] ⊢ LK₁ ⊑ RK₁ ∶ ∀id⊑★ Wk1
lk₁⊑rk₁ = from-just (tr (R.forget R.lk₁⊑rk₁))

lk₁⊑rk₃ : Wk ∣ [] ⊢ LK₁ ⊑ RK₃ ∶ ∀id⊑★ Wk
lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

lk₁⊑rk₄ : Wk ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ ∀id⊑★ Wk
lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

-- 4d. The refuted obligations, met.  Sim's and SimBack's conclusions
-- (SimDef, SimBackDef) for this relation
SimConcl : ∀ {Δ Δ′} → World Δ Δ′ → Term → Term → (A A′ : Ty) → Alloc
  → Set
SimConcl {Δ} {Δ′} W M′ N A A′ ξ =
  ∃[ N′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* N′ ]
    Σ[ W′ ∈ World (apply ξ Δ) (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ ξ ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N ⊑ N′ ∶ q)

SimBackConcl : ∀ {Δ Δ′ N′ ξ′} {M′ : Term} → World Δ Δ′ → Term
  → Δ′ ⊢ M′ -→ N′ ∣ ξ′ → (A A′ : Ty) → Set
SimBackConcl {Δ} {Δ′} {N′} {ξ′} W M st′ A A′ =
  ∃[ N₂ ] ∃[ N₂′ ] Σ[ r ∈ Δ ⊢ M -→* N₂ ]
    Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
    Σ[ W′ ∈ World (applyˢ (allocs r) Δ)
                  (applyˢ (allocs (st′ then r″)) Δ′) ]
      (W ⟿[ allocs r ∣ allocs (st′ then r″) ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N₂ ⊑ N₂′ ∶ q)

-- Sim at (LK₁, RK₁) and the left's Beta (`sim-false`, `simᴿ-false`):
-- the right runs Inst, TyBeta, Merge, Beta
sim-K : SimConcl Wk1 RK₁ VL ∀X⇒X (★ ⇒ ★) none
sim-K =
  RF , (st₁ then st₂ then st₃ then st₄ then done) , Wk ,
  ev-noneᴸ (ev-noneᴿ (ev-R wfᴿ-★ (ev-noneᴿ (ev-noneᴿ ev-done)))) ,
  Wk-wf , ∀id⊑★ Wk , VL⊑RF

-- SimBack at (LK₁, RK₁) and the right's Inst: the right takes only its
-- TyBeta (no Merge needed: the pre-Merge pair is related)
simBack-K-inst : SimBackConcl Wk1 LK₁ st₁ ∀X⇒X (★ ⇒ ★)
simBack-K-inst =
  LK₁ , RK₃ , done , (st₂ then done) , Wk ,
  ev-noneᴿ (ev-R wfᴿ-★ ev-done) , Wk-wf , _ , lk₁⊑rk₃

-- SimBack at the right's MERGE (`simBack-false` for the current
-- relation): both sides stop; the premise changes from ⟪⟫⊑⟪⟫ (Nk ⊑ Nk)
-- to ⟪⟫⊑ (Nk ⊑ idX), the opening stays
simBack-K-merge : SimBackConcl Wk VL stM ∀X⇒X (★ ⇒ ★)
simBack-K-merge =
  VL , RF , done , done , Wk , ev-noneᴿ ev-done , Wk-wf , _ , VL⊑RF

simBack-K-merge₁ : SimBackConcl Wk LK₁ st₃ ∀X⇒X (★ ⇒ ★)
simBack-K-merge₁ =
  LK₁ , RK₄ , done , done , Wk , ev-noneᴿ ev-done , Wk-wf , _ , lk₁⊑rk₄

-- SimBack at (LK₁, RK₄) and the right's Beta: the left's Beta
simBack-K-beta : SimBackConcl Wk LK₁ st₄ ∀X⇒X (★ ⇒ ★)
simBack-K-beta =
  VL , RF , (stL then done) , done , Wk ,
  ev-noneᴸ (ev-noneᴿ ev-done) , Wk-wf , ∀id⊑★ Wk , VL⊑RF

-- DGG part 1 on the initial pair (`dgg1-false`, `dgg1ᴿ-false`)
dgg1-K :
  ∃[ V′ ] Σ[ r′ ∈ empty ⊢ RK -→* V′ ] Value V′
    × Σ[ W′ ∈ World ΔL (applyˢ (allocs r′) empty) ]
        Σ[ q ∈ ∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ V′ ∶ q)
dgg1-K =
  RF , (st₀ then st₁ then st₂ then st₃ then st₄ then done) , vRF ,
  Wk , ∀id⊑★ Wk , VL⊑RF

-- 4e. K2 (FixA §4): the left instantiates the ∀-value AFTER the right
-- merged.
--   L  (λf:∀X.X→X. f[ℕ]) (K[ℕ])     TyBeta, Beta, TyBeta, Merge
--   R  RK                            (as K)
-- Before the left's TyBeta: ν⊑ over the opened ⊑⟪⟫.  After it: the
-- opening has become the left boundary `+Y^γ` (ev-L⇔ turns the lexical
-- (0, β) into the global (γ, β)), and FixA's derivations carry over
-- (they use no ∀⊑⟪+⟫, ∀⊑⟪+⟫ᴹ).
trA : ∀ {W : World Δ Δ′} {γ : CtxImp W} {M M′ A′ B′} {p : A′ ⊑ᵂ⟨ W ⟩ B′}
  → W A.∣ γ ⊢ M ⊑ M′ ∶ p → Maybe (W ∣ γ ⊢ M ⊑ M′ ∶ p)
trA (A.x⊑x x) = just (x⊑x x)
trA (A.κ⊑κ k p) = just (κ⊑κ k p)
trA (A.ƛ⊑ƛ wA wA′ d) = mapᴹ (ƛ⊑ƛ wA wA′) (trA d)
trA (A.·⊑· d e) = map₂ ·⊑· (trA d) (trA e)
trA (A.blame⊑ wA ⊢M p) = just (blame⊑ wA ⊢M p)
trA (A.cast⊑cast d c c′ q) = mapᴹ (λ d′ → cast⊑cast d′ c c′ q) (trA d)
trA (A.cast⊑ d c q) = mapᴹ (λ d′ → cast⊑ d′ c q) (trA d)
trA (A.⊑cast d c′ q) = mapᴹ (λ d′ → ⊑cast d′ c′ q) (trA d)
trA (A.Λ⊑Λ l v v′ d q) = mapᴹ (λ d′ → Λ⊑Λ l v v′ d′ q) (trA d)
trA (A.Λ⊑ nv occ l v d q) = mapᴹ (λ d′ → Λ⊑ nv occ l v d′ q) (trA d)
trA (A.∀⊑⟪+⟫ _ _ _ _ _ _ _ _ _ _) = nothing
trA (A.∀⊑⟪+⟫ᴹ _ _ _ _ _ _ _ _ _ _ _ _ _) = nothing
trA (A.ν⊑ν d a n n′ nc q) = mapᴹ (λ d′ → ν⊑ν d′ a n n′ nc q) (trA d)
trA (A.ν⊑ d a n q) = mapᴹ (λ d′ → ν⊑ d′ a n q) (trA d)
trA (A.⟪⟫⊑⟪⟫ int wf d b b′ bc q) =
  mapᴹ (λ d′ → ⟪⟫⊑⟪⟫ int wf d′ b b′ bc q) (trA d)
trA (A.⟪⟫⊑ int wf d b q) = mapᴹ (λ d′ → ⟪⟫⊑ int wf d′ b q) (trA d)
trA (A.⊑⟪⟫ int wf d b′ q) =
  mapᴹ (λ d′ → ⊑⟪⟫ int open-none wf d′ b′ q) (trA d)

lk2₁⊑rk₄ : Wk ∣ [] ⊢ LK2₁ ⊑ RK₄ ∶ ℕ⇒ℕ⊑★⇒★ Wk
lk2₁⊑rk₄ =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf
        (ν⊑ (x⊑x Zʷ) ℕ⊑★ νL2-ty (ℕ⇒ℕ⊑★⇒★ Wk)))
      VL⊑RF

lk2₂⊑rf : Wk ∣ [] ⊢ LK2₂ ⊑ RF ∶ ℕ⇒ℕ⊑★⇒★ Wk
lk2₂⊑rf = ν⊑ VL⊑RF ℕ⊑★ νL2-ty (ℕ⇒ℕ⊑★⇒★ Wk)

-- the left's ν over the PRE-Merge right also relates (not in FixA:
-- ∀⊑⟪+⟫ᴹ needed the Merge; here the same rule covers both)
lk2₂⊑rarg₃ : Wk ∣ [] ⊢ LK2₂ ⊑ Rarg₃ ∶ ℕ⇒ℕ⊑★⇒★ Wk
lk2₂⊑rarg₃ = ν⊑ VL⊑Rarg₃ ℕ⊑★ νL2-ty (ℕ⇒ℕ⊑★⇒★ Wk)

lk2₃⊑rf : Wk2 ∣ [] ⊢ LK2₃ ⊑ RF ∶ ℕ⇒ℕ⊑★⇒★ Wk2
lk2₃⊑rf = from-just (trA A.lk2₃⊑rf)

bm⊑rf : Wk2 ∣ [] ⊢ Bm ⊑ RF ∶ ℕ⇒ℕ⊑★⇒★ Wk2
bm⊑rf = from-just (trA A.bm⊑rf)

sim-K2-tyBeta : SimConcl Wk RF LK2₃ (`ℕ ⇒ `ℕ) (★ ⇒ ★) (new `ℕ)
sim-K2-tyBeta = RF , done , Wk2 , ev2 , Wk2-wf , _ , lk2₃⊑rf

sim-K2-merge : SimConcl Wk2 RF Bm (`ℕ ⇒ `ℕ) (★ ⇒ ★) none
sim-K2-merge = RF , done , Wk2 , ev-noneᴸ ev-done , Wk2-wf , _ , bm⊑rf

dgg1-K2 :
  Σ[ r′ ∈ empty ⊢ RK -→* RF ] Value RF
    × Σ[ W′ ∈ World (applyˢ (allocs LK2-run) empty)
                    (applyˢ (allocs r′) empty) ]
        Σ[ q ∈ (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ Bm ⊑ RF ∶ q)
dgg1-K2 =
  (st₀ then st₁ then st₂ then st₃ then st₄ then done) , vRF ,
  Wk2 , ℕ⇒ℕ⊑★⇒★ Wk2 , bm⊑rf

------------------------------------------------------------------------
-- 5. Syntax-directedness, on K
------------------------------------------------------------------------

-- 5a. ZERO openings are impossible for the final pair: VL against the
-- merged boundary's interior λx:Y.x relates in no world (the left Λ
-- can only go left-only, and then λx:X.x ⊑ λx:Y.x needs a join)
λ-joins : ∀ {W : World Δ Δ′} {γ : CtxImp W} {A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ γ ⊢ idX ⊑ idX ∶ p → Joins W 0 0
λ-joins (κ⊑κ () _)
λ-joins (ƛ⊑ƛ {pA = pA} _ _ _) = var⊑var pA refl refl

I-id : ∀ {W : World Δ Δ′} {γ : CtxImp W} {A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W ∣ γ ⊢ I ⊑ idX ∶ p)
I-id {W = W} (Λ⊑ _ _ _ _ d _) = ⊕ᴸ-¬joins {W = W} {b = 0} (λ-joins d)

VL-id : ∀ {W : World Δ Δ′} {γ : CtxImp W} {A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W ∣ γ ⊢ VL ⊑ idX ∶ p)
VL-id (⟪⟫⊑ _ _ d _ _) = I-id d

-- 5b. The opening's NAME is forced: in the merged interior context only
-- name 0 (Y) names a ★ rep. var (name 1, X, names αᴿ:=ℕ)
rep-1 : ∀ {b} → reps ΔRX ∋ʳ 1 := b → b ≡ bindR `ℕ
rep-1 (r-there r-here) = refl

★≢ℕ : ¬ (bindR ★ ≡ bindR `ℕ)
★≢ℕ ()

open1-name : ∀ {Δ} {Wᵢ : World Δ ΔRX} {k W₁} → Open1 Wᵢ k W₁ → k ≡ 0
open1-name (open1 _ here _) = refl
open1-name (open1 _ (there here) h) = ⊥-elim (★≢ℕ (rep-1 h))
open1-name (open1 _ (there (there ())) _)

-- 5c. The NUMBER of openings and the opened term are forced: given the
-- premise against λx:Y.x, Opens is exactly one opening, to inst_Y(VL)
-- = Nk (a second one would need Nk at a ∀ type; zero is 5a)
opens-K : ∀ {Δ⁺} {Wᵢ : World ΔL ΔRX} {W⁺ : World Δ⁺ ΔRX} {M₀ A₀ A′}
    {r : A₀ ⊑ᵂ⟨ W⁺ ⟩ A′}
  → Opens Θ₂ Wᵢ VL ∀X⇒X W⁺ M₀ A₀
  → W⁺ ∣ [] ⊢ M₀ ⊑ idX ∶ r
  → (M₀ ≡ Nk) × (A₀ ≡ (` 0 ⇒ ` 0))
opens-K open-none d = ⊥-elim (VL-id d)
opens-K (open-∀ _ _ _ _ (inst-⟪⟫ _ (inst-Λ _)) _ _ open-none) _ =
  refl , refl

-- 5d. NOT unique at the level of RULES: the left boundary may be peeled
-- first (⟪⟫⊑), and the opening then happens one boundary further in,
-- on the left interior's ΛX.λx:X.x.  This is the boundary-order
-- freedom ⟪⟫⊑/⊑⟪⟫ the relation already has (the current ∀⊑⟪+⟫ applied
-- to I under ⟪⟫⊑ as well); it is not a choice inside Opens.
W₁ᴸ : World ΔLᵢ ΔRk
W₁ᴸ = world (X⊑★ ∷ []) (keep []↪) (skip []↪) ((0 , 1) ∷ []) []

IntL : Interior Wk Θ₀ [] W₁ᴸ
IntL = record
  { int-left   = Θ₀-int
  ; int-right  = interior changes[]
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { _ () _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , ()) _ _ }
  }

W₁ᴸ-wf : WfWorld W₁ᴸ
W₁ᴸ-wf = wf-world (left-only joint[]) agree
  (namedᴸ-≤1 W₁ᴸ ≤1-∷[]) (namedᴿ-≤1 W₁ᴸ ≤1-[])
  where
  agree : ∀ {α β} → Paired W₁ᴸ α β → Agree W₁ᴸ α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

-- inside the right's merged boundary: the right X (fresh) rejoins the
-- left's X (αᴸ paired with αᴿ), keeping its mark X⊑★; Y right-only
WiK′ : World ΔLᵢ ΔRX
WiK′ = world (X⊑X ∷ X⊑★ ∷ []) (skip (keep []↪)) (keep (keep []↪))
         ((0 , 1) ∷ []) []

IntAlt : Interior W₁ᴸ [] Θ₂ WiK′
IntAlt = record
  { int-left   = interior changes[]
  ; int-right  = int-Θ₂
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ
      { (_ , here) (_ , here) _ () ; (_ , here) (_ , there here) _ ()
      ; (_ , here) (_ , there (there ())) _ _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ
      { here here _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
      ; here (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; mark-left  = λ { (_ , here) refl here → there here ; (_ , there ()) _ _ }
  ; mark-right = λ
      { (_ , here) () _ ; (_ , there here) () _
      ; (_ , there (there ())) _ _ }
  }

WX★ : World ΔLX ΔRX
WX★ = world (X⊑X ∷ X⊑★ ∷ []) (keep (keep []↪)) (keep (keep []↪))
        ((1 , 1) ∷ []) ((0 , 0) ∷ [])

openAlt : Open1 WiK′ 0 WX★
openAlt = open1 join-here here r-here

WX★-wf : WfWorld WX★
WX★-wf = wf-world (both (inj₂ here⇔) (both (inj₁ here⇔) joint[])) agree
  (λ _ _ _ → uniqᴸK) (λ _ _ _ → uniqᴿK)
  where
  agree : ∀ {α β} → Paired WX★ α β → Agree WX★ α β
  agree (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))

I⊑Bm : W₁ᴸ ∣ [] ⊢ I ⊑ Bm ∶ ∀id⊑★ W₁ᴸ
I⊑Bm =
  ⊑⟪⟫ IntAlt
    (open-∀ nv-⇒ (∈-⇒ˡ ∈-var) (V-simple (S-Λ (V-simple S-ƛ))) tc
      (inst-Λ (V-simple S-ƛ)) refl openAlt open-none)
    WX★-wf (idX⊑idX X⊑X tf tf) bBm (∀id⊑★ W₁ᴸ)

VL⊑Bm-alt : Wk ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk
VL⊑Bm-alt = ⟪⟫⊑ IntL W₁ᴸ-wf I⊑Bm bVL (∀id⊑★ Wk)

------------------------------------------------------------------------
-- 6. What the simulations need (statements only)
------------------------------------------------------------------------

↑ᴮ*[_] : List Alloc → Boundary → Boundary
↑ᴮ*[ []     ] Θ = Θ
↑ᴮ*[ ξ ∷ ξs ] Θ = ↑ᴮ*[ ξs ] (↑ᴮ[ ξ ] Θ)

-- (i) The premise world's WfWorld follows from the interior world's:
-- an opened name is right-only and fresh, so by Interior's join-fresh
-- its rep. var has no left partner NAMED in Δ (NoNamedPartner), which
-- is wf-⊕⁺'s condition.  With it the rule's `WfWorld Wᵢ⁺` could be
-- `WfWorld Wᵢ`, as in ⟪⟫⊑⟪⟫ and ⟪⟫⊑.  (k = 0, one opening: wf-⊕⁺.)
WfOpens : Set
WfOpens = ∀ {Δ Δ′ Δ′ᵢ Δ⁺ Θ′} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {M A M₀ A₀}
  → WfCtx Δ → WfCtx Δ′ᵢ → WfWorld W
  → Interior W [] Θ′ Wᵢ → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ → WfWorld Wᵢ⁺

-- (ii) Where the rule is created: the right's Inst (CatchupCast's Inst
-- case; SimBack on `V₀′ ⟨inst X.p⟩`).  Right after Inst and TyBeta the
-- pair is related, with the RAW interior N₀′ = inst_X(V₀′): no run of
-- the interior, no `Simple`, no `¬ ForallBdy` (RestrictedForallBoundary
-- §4), no conversion inversion (FixA §3).  Proof plan: InstXImp⁺
-- (CatchupRightChildren, for this relation) gives the premise at
-- `allocᴿ ★ W ⊕⁺ m ^ 0`, the opening at name 0 of
-- `allocᴿ ★ W ⊕ʳ m ^ 0` (`open-⊕`); rep. var 0 is fresh, so it has no
-- partner (Interior, WfOpens); then `∀⊑⟪+⟫-adm`.
InstSyncᴳ : Set
InstSyncᴳ = ∀ {Δ Δ′} {W : World Δ Δ′} {V V₀′ N N₀′ C C′}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′                       -- binders match
  → NonVar C → 0 ∈ᵗ C
  → Value V → Value V₀′ → InstX V N → InstX V₀′ N₀′
  → W ∣ [] ⊢ V ⊑ V₀′ ∶ r
  → ∃[ B′ ] Σ[ q ∈ `∀ C ⊑ᵂ⟨ allocᴿ ★ W ⟩ B′ ]
      (allocᴿ ★ W ∣ [] ⊢ V ⊑ N₀′ ⟪ bind 0 0 ∷ [] , reveal 0 C′ ⟫ ∶ q)

-- (iii) Frames (SimBack's ξ-⟪⟫ under ⊑⟪⟫, CatchupFrame-⊑⟪⟫): the
-- interior's allocations, recorded on the premise world, read back on
-- the interior world; Opens moves along (allocations renumber rep.
-- vars, not names, so `Fresh` and the joins are kept).  Then
-- EvolveInteriorᴿ (CatchupRightChildren §b) lifts to W.
OpensEvolveᴿ : Set
OpensEvolveᴿ = ∀ {Δ Δ⁺ Δ′ᵢ Θ′ ξs′} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {Wᵢ⁺′ : World Δ⁺ (applyˢ ξs′ Δ′ᵢ)} {M A M₀ A₀}
  → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → Wᵢ⁺ ⟿[ [] ∣ ξs′ ] Wᵢ⁺′
  → Σ[ Wᵢ′ ∈ World Δ (applyˢ ξs′ Δ′ᵢ) ]
      (Wᵢ ⟿[ [] ∣ ξs′ ] Wᵢ′) × Opens (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′ M A Wᵢ⁺′ M₀ A₀

-- (iv) THE INNER-STEP GAP (R2): SimBack inside the premise with the
-- left FIXED at its Opens image (the conclusion's left is the value V,
-- which cannot step, so SimBack's IH, which may answer with a left
-- run, is too weak).  Zero openings: M₀ = V, SimBack with a value left.
-- One or more: ForallBoundaryFixes' SimBackInstX, unchanged.
SimBackOpened : Set
SimBackOpened = ∀ {Δ Δ⁺ Δ′ᵢ Θ′} {Wᵢ : World Δ Δ′ᵢ} {Wᵢ⁺ : World Δ⁺ Δ′ᵢ}
    {V M₀ M′ M₁′ A A₀ A′ δ′} {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′}
  → WfCtx Δ⁺ → WfCtx Δ′ᵢ → WfWorld Wᵢ⁺
  → Value V → Opens Θ′ Wᵢ V A Wᵢ⁺ M₀ A₀
  → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ M′ ∶ r
  → (st′ : Δ′ᵢ ⊢ M′ -→ M₁′ ∣ δ′)
  → ∃[ M₂′ ] Σ[ r″ ∈ apply δ′ Δ′ᵢ ⊢ M₁′ -→* M₂′ ]
      Σ[ W′ ∈ World Δ⁺ (applyˢ (allocs (st′ then r″)) Δ′ᵢ) ]
        (Wᵢ⁺ ⟿[ [] ∣ allocs (st′ then r″) ] W′) × WfWorld W′
        × Σ[ r′ ∈ A₀ ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ M₀ ⊑ M₂′ ∶ r′)

-- (v) THE MERGE (SimBack's right Merge and CatchupBdy's Merge under
-- ⊑⟪⟫): the inner right boundary moves out into the outer one; the
-- openings stay (their names, renumbered through Θ₁′, are still
-- introduced by the merged boundary), the left M₀ is unchanged.  Zero
-- openings: FixA's RightMergeInterior for a right-only outer boundary,
-- needed by SimBack anyway (its conversion half is MergeImpR).
RightMergeOpens : Set
RightMergeOpens = ∀ {Δ Δ′ Δ′ᵢ Δ⁺} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {Θ₁′ Θ₂′ M M₀ U′ t₁′ A A₀ A′ᵢ}
    {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′ᵢ}
  → WfWorld W → Interior W [] Θ₂′ Wᵢ → Opens Θ₂′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ⁺
  → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ U′ ⟪ Θ₁′ , t₁′ ⟫ ∶ r
  → ∃[ Δ″ ] Σ[ Wₘ ∈ World Δ Δ″ ] Σ[ Wₘ⁺ ∈ World Δ⁺ Δ″ ]
      Interior W [] (Θ₁′ ++ Θ₂′) Wₘ
      × Opens (Θ₁′ ++ Θ₂′) Wₘ M A Wₘ⁺ M₀ A₀ × WfWorld Wₘ⁺
      × ∃[ A″ ] Σ[ r′ ∈ A₀ ⊑ᵂ⟨ Wₘ⁺ ⟩ A″ ] (Wₘ⁺ ∣ [] ⊢ M₀ ⊑ U′ ∶ r′)

-- its instance on K: from (Θ₀, Nk ⊑ Nk by ⟪⟫⊑⟪⟫) to (Θ₂, Nk ⊑ idX by
-- ⟪⟫⊑), the opening at name 0 in both
RightMergeOpens-K :
    (Wk ∣ [] ⊢ VL ⊑ Nk ⟪ Θ₀ , revX ⟫ ∶ ∀id⊑★ Wk)
  × ∃[ Δ″ ] Σ[ Wₘ ∈ World ΔL Δ″ ] Σ[ Wₘ⁺ ∈ World (underΛ ΔL) Δ″ ]
      Interior Wk [] (ΘX ++ Θ₀) Wₘ
      × Opens (ΘX ++ Θ₀) Wₘ VL ∀X⇒X Wₘ⁺ Nk (` 0 ⇒ ` 0) × WfWorld Wₘ⁺
      × Σ[ r′ ∈ (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wₘ⁺ ⟩ (` 0 ⇒ ` 0) ]
          (Wₘ⁺ ∣ [] ⊢ Nk ⊑ idX ∶ r′)
RightMergeOpens-K =
  ⊑⟪⟫ IntK-ro openVLₖ PwK-wf Nk⊑Nk bOutK (∀id⊑★ Wk) ,
  ΔRX , WiR , WoK , IntK-Θ₂ , openVL , WoK-wf , ⇒⊑⇒ X⊑X X⊑X , Nk⊑idX

-- (vi) THE LEFT'S LATER TyBeta (Sim's TyBeta case under ν⊑ over an
-- opened ⊑⟪⟫): the first opening becomes the left's new boundary
-- `bind 0 0`; ev-L⇔ pairs the new left rep. var with β GLOBALLY,
-- replacing the lexical (0, β).  The conclusion's derivation ends in
-- ⟪⟫⊑⟪⟫ when no opening remains (K2: `lk2₃⊑rf`), or in ⟪⟫⊑ over ⊑⟪⟫
-- with the remaining openings (⟪⟫⊑⟪⟫ has no Opens; the shape of
-- `VL⊑Bm-alt`).
OpenCatchUp : Set
OpenCatchUp = ∀ {Δ Δ′ Δ′ᵢ Δ⁺ k} {W : World Δ Δ′}
    {Wᵢ : World Δ Δ′ᵢ} {W₁ : World (underΛ Δ) Δ′ᵢ} {Wᵢ⁺ : World Δ⁺ Δ′ᵢ}
    {Θ′ c′ V N M₀ M′ R C c A₀ A′ᵢ A′ B} {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′ᵢ}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → NonVar C → 0 ∈ᵗ C → Value V → Δ ∣ [] ⊢ V ⦂ `∀ C → InstX V N
  → Interior W [] Θ′ Wᵢ → Fresh Θ′ k → Open1 Wᵢ k W₁
  → Opens Θ′ W₁ N C Wᵢ⁺ M₀ A₀ → WfWorld Wᵢ⁺
  → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ M′ ∶ r
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → `∀ C ⊑ᵂ⟨ W ⟩ A′
  → NuTy Δ R C c B → R ⊑ᵂ⟨ W ⟩ ★
  → B ⊑ᵂ⟨ W ⟩ A′
  → Σ[ W′ ∈ World (allocate R Δ) Δ′ ]
      (W ⟿[ new R ∷ [] ∣ [] ] W′) × WfWorld W′
      × Σ[ q′ ∈ B ⊑ᵂ⟨ W′ ⟩ A′ ]
          (W′ ∣ [] ⊢ N ⟪ bind 0 0 ∷ [] , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q′)

-- (vii) CatchupRight with the left an OPENS IMAGE of a value (the
-- generalization CatchupRightChildren §c recommends, now uniform): the
-- generalized ⊑⟪⟫ case recurses on its own premise (a subderivation),
-- so CatchupFrame-∀⊑⟪+⟫ and CatchupInstX merge into CatchupFrame-⊑⟪⟫.
CatchupRightConcl : ∀ {Δ Δ′} (W : World Δ Δ′) (M M′ : Term)
  (A A′ : Ty) → Set
CatchupRightConcl {Δ} {Δ′} W M M′ A A′ =
  ∃[ V′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* V′ ] Value V′
    × Σ[ W′ ∈ World Δ (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ M ⊑ V′ ∶ q)

CatchupRightᴳ : Set
CatchupRightᴳ = ∀ {Δ Δ⁺ Δ′ Θ′} {W₀ : World Δ Δ′} {W : World Δ⁺ Δ′}
    {V M M′ A₀ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ⁺ → WfCtx Δ′ → WfWorld W
  → Value V → Opens Θ′ W₀ V A₀ W M A
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → CatchupRightConcl W M M′ A A′

-- (viii) Syntax-directedness (md §5): a right name free in the right
-- type forces a left name joined to it (type imprecision has no rule
-- with a variable on the right only: `X⊑X` is the only one).  So a
-- right-only ★-name of δ′ free in A′ᵢ MUST be opened, by the left
-- binder at its positions; this pins the number of openings and their
-- names (the canonical choice, md §5).
RightNameForcesJoin : Set
RightNameForcesJoin = ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ k}
  → A ⊑ᵂ⟨ W ⟩ A′ → k ∈ᵗ A′ → ∃[ X ] ((X ∈ᵗ A) × Joins W X k)
