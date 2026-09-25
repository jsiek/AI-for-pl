module strong-rep-nu.proof.ShiftAudit where

-- File Charter:
--   * THE SHIFT AUDIT — every place a rule MOVES A SUBTERM, checked
--     against FRAME EXACTNESS.  §1 the site table; §2 Wrap; §3 the
--     two ν rules; §4 the tower measure (ONE boundary per value, and
--     `Merge` lowers it); §5 Beta; §6 Merge; §7 the drops; §8 the ξ
--     rules; §9 dead machinery.
--   * THE CRITERION.  A moved subterm's type context at the new
--     position must be EXACTLY its context at the old one, up to
--     (i) the binders it CROSSED and (ii) refinement
--     `abstR → bindR R` of a variable it could ALREADY name.  Anything
--     else it can name after and could not before is a FRAME LEAK.
--   * Since the store there are no binds to cross, so the per-site
--     facts are `strong-rep-nu.Boundary` §3a's transport lemmas,
--     CITED not restated.
--   * THE VERDICTS ARE THIS MODULE.  notes/ShiftAudit.md is the
--     ARCHIVED 2026-09-08 audit and is written against the bind-block
--     calculus; read it for the leak's diagnosis and the rejected
--     repairs, never for a verdict.  Prose: Commentary.md.
-- Commentary: Commentary.md § proof/ShiftAudit.agda

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.TermSubst
open import strong-rep-nu.proof.TermSubst
open import strong-rep-nu.Reduction
open import strong-rep-nu.proof.Canonical using (canon-∀)

private
  variable
    Δ Δ′ Γᵗ : Ctxᵗ
    Γ : Ctx
    A B C : Ty
    X Y : ℕ
    Θ Θ₁ Θ₂ : Boundary

------------------------------------------------------------------------
-- §1  THE SITES
------------------------------------------------------------------------

-- The site table — every rule that moves a subterm, with its verdict —
-- is Commentary.md § proof/ShiftAudit.agda / §1.

------------------------------------------------------------------------
-- §2  PEEL — the crossing argument's frame is the EXTERIOR ITSELF
------------------------------------------------------------------------

-- Before: `Δ`.  After: the dual's interior, which `dual-interior` says
-- is `Δ`.  EXACT, and the rule carries W verbatim.
Wrap-frame : ∀ {Γᵢ : Ctxᵗ} (Θ : Boundary) (Γ : Ctxᵗ)
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ dual Θ ⇒ Γ
Wrap-frame Θ Γ = dual-interior

-- … and Wrap allocates nothing, so its siblings do not move either.
Wrap-no-alloc : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Simple V → Value W
  → Δ ⊢ᶜ Θ ⇒ Δᶜ → Δ ⊢ⁱ Θ ⇒ Δᵢ
  → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ → SameConv Δᵈ s′ Δᶜ s
  → Δ ⊢ (V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · W
      -→ (V · (W ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫ ∣ none
Wrap-no-alloc = Wrap

------------------------------------------------------------------------
-- §3  THE TWO ν RULES
------------------------------------------------------------------------

-- `TyBeta` MOVES NOTHING: the allocation REFINES `N`'s own `abstR` binder
-- to `bindR R` in place and `inst []` gives it ordinary name 0.
-- Criterion (ii), no renaming at all.
TyBeta-restores-name-0 :
  (inst []) ≡ bind 0 0 ∷ []
TyBeta-restores-name-0 = refl

-- `TyWrap` is the same refinement one boundary in, with the two layers
-- STACKED: the outer `inst []` restores name 0, and the middle
-- `liftᴮ Θ` is the crossed frame read under it.  Read inside out they
-- are exactly the fused `inst Θ` the retired TyPeelR-Λ wrote.
TyWrap-stacks-to-inst : (Θ : Boundary)
  → inst Θ ≡ liftᴮ Θ ++ inst []
TyWrap-stacks-to-inst Θ = refl

------------------------------------------------------------------------
-- §4  THE TOWER MEASURE — one boundary per value
------------------------------------------------------------------------

-- The number of nested boundaries at the head of a term.  Under the
-- one-boundary invariant a value's is at most one, and a `Merge` step
-- lowers it by one — so the retired `Nu-⟪⟫` tower descent is gone.
-- Commentary.md § proof/ShiftAudit.agda / §4
towerHeight : Term → ℕ
towerHeight (` x)          = 0
towerHeight ($ n)          = 0
towerHeight `true          = 0
towerHeight `false         = 0
towerHeight (ƛ A ∙ N)      = 0
towerHeight (L · M)        = 0
towerHeight (Λ N)          = 0
towerHeight (ν A · L ⟨ c ⟩) = 0
towerHeight (M ⟪ Θ , c ⟫)  = suc (towerHeight M)

-- No renaming changes it.
towerHeight-renᴹᴿ : (ρ : Renameᵗ) (M : Term)
  → towerHeight (renᴹᴿ ρ M) ≡ towerHeight M
towerHeight-renᴹᴿ ρ (` x)          = refl
towerHeight-renᴹᴿ ρ ($ n)          = refl
towerHeight-renᴹᴿ ρ `true          = refl
towerHeight-renᴹᴿ ρ `false         = refl
towerHeight-renᴹᴿ ρ (ƛ A ∙ N)      = refl
towerHeight-renᴹᴿ ρ (L · M)        = refl
towerHeight-renᴹᴿ ρ (Λ N)          = refl
towerHeight-renᴹᴿ ρ (ν A · L ⟨ c ⟩) = refl
towerHeight-renᴹᴿ ρ (M ⟪ Θ , c ⟫)  =
  cong suc (towerHeight-renᴹᴿ ρ M)

-- … and neither does the sibling shift, at either `Alloc`.
towerHeight-↑ᴹ : (δ : Alloc) (M : Term)
  → towerHeight (↑ᴹ[ δ ] M) ≡ towerHeight M
towerHeight-↑ᴹ none    M = refl
towerHeight-↑ᴹ (new R) M = towerHeight-renᴹᴿ suc M

simple-height : ∀ {U} → Simple U → towerHeight U ≡ 0
simple-height S-$     = refl
simple-height S-true  = refl
simple-height S-false = refl
simple-height S-ƛ     = refl
simple-height (S-Λ v) = refl

-- ONE BOUNDARY PER VALUE.
value-height : ∀ {V} → Value V → (towerHeight V ≡ 0) ⊎ (towerHeight V ≡ 1)
value-height (V-simple u) = inj₁ (simple-height u)
value-height (V-⟪⟫ u it)  = inj₂ (cong suc (simple-height u))

-- `Merge` strictly lowers the measure.
Merge-height : (U : Term) (Θ₁ Θ₂ : Boundary) (c₁ c₂ c : Conv)
  → towerHeight (U ⟪ Θ₁ ++ Θ₂ , c ⟫)
      ≡ towerHeight ((U ⟪ Θ₁ , c₁ ⟫) ⟪ Θ₂ , c₂ ⟫) ∸ 1
Merge-height U Θ₁ Θ₂ c₁ c₂ c = refl

-- An identity conversion at a `∀` is necessarily `` `∀ ``, hence INERT.
mkId-∀ : (B : Ty) → mkId (`∀ B) ≡ ⌞ `∀ (mkId B) ⌟
mkId-∀ B = refl

mkId-∀-inert : (B : Ty) → Inert (mkId (`∀ B))
mkId-∀-inert B = I-tail I-all

-- Values and inertness survive the renamings the rules perform.
-- (`inert-renᶜ`, `value-renᴹ²`, `value-renᴹᴿ` moved to
-- strong-rep-nu.proof.TermSubst §2.)
value-↑ᴹ : ∀ {M} (δ : Alloc) → Value M → Value (↑ᴹ[ δ ] M)
value-↑ᴹ none    v = v
value-↑ᴹ (new R) v = value-renᴹᴿ suc v

-- A `∀`-value of tower height 0 is a `Λ`.
canon-∀-height : ∀ {Δ V C} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ C
  → towerHeight V ≡ 0
  → Σ[ N ∈ Term ] (Value N × (V ≡ Λ N))
canon-∀-height v ⊢V eq with canon-∀ v ⊢V
canon-∀-height v ⊢V eq | inj₁ p = p
canon-∀-height v ⊢V ()
    | inj₂ (N , Θ′ , s′ , vN , refl)

-- … stated as the progress clause it decides, against the LIVE relation.
-- The step is `TyWrap`, which ALLOCATES the cell for the type
-- argument's representation.
progress-Λ-at-0 : ∀ {Δ Δᶜ V Θ s c A R C} → Value V
  → Δ ∣ [] ⊢ ν A · (V ⟪ Θ , ⌞ `∀ s ⌟ ⟫) ⟨ c ⟩ ⦂ C
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → Δ ⊢ᶜ A ~ R
  → towerHeight V ≡ 0
    ----------------------------------------------------------------
  → Σ[ N ∈ Term ]
      ((V ≡ Λ N)
       × (Δ ⊢ ν A · (V ⟪ Θ , ⌞ `∀ s ⌟ ⟫) ⟨ c ⟩
            -→ (N ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫ ∣ new R))
progress-Λ-at-0 v
    (⊢ν wA rA (boundary mwᵥ ⊢V ⊢c smᵢ smₑ wE) mw ⊢cν sm wB) rc pA eq
  with conv-all-inv ⊢c
progress-Λ-at-0 v
    (⊢ν wA rA (boundary mwᵥ ⊢V ⊢c smᵢ smₑ wE) mw ⊢cν sm wB) rc pA eq
  | A₀ , B₀ , refl , eqₑ , ⊢s with smᵢ
progress-Λ-at-0 v
    (⊢ν wA rA (boundary mwᵥ ⊢V ⊢c smᵢ smₑ wE) mw ⊢cν sm wB) rc pA eq
  | A₀ , B₀ , refl , eqₑ , ⊢s | _ , same-∀ pᵢ , same-∀ qᵢ
  with conversion-functional (bw-conversion mwᵥ) rc
progress-Λ-at-0 v
    (⊢ν wA rA (boundary mwᵥ ⊢V ⊢c smᵢ smₑ wE) mw ⊢cν sm wB) rc pA eq
  | A₀ , B₀ , refl , eqₑ , ⊢s | _ , same-∀ pᵢ , same-∀ qᵢ | refl
  with canon-∀-height v ⊢V eq
progress-Λ-at-0 v
    (⊢ν wA rA (boundary mwᵥ ⊢V ⊢c smᵢ smₑ wE) mw ⊢cν sm wB) rc pA eq
  | A₀ , B₀ , refl , eqₑ , ⊢s | _ , same-∀ pᵢ , same-∀ qᵢ | refl
  | N , vN , refl = N , refl , TyWrap vN rc ⊢s pA

------------------------------------------------------------------------
-- §5  BETA — the two crossings do not interfere
------------------------------------------------------------------------

-- THE `ƛ` CLAUSE.  A `ƛ` binds a TERM variable, so `shiftᴵ` must not
-- touch the type side; on a value image it is the IDENTITY, which is
-- correct because a value image is TERM-CLOSED and stays so.
Beta-ƛ-no-shift : ∀ {W A} → shiftᴵ (ival W A) ≡ ival W A
Beta-ƛ-no-shift = refl

Beta-ƛ-crossed-no-shift : ∀ {W A} → shiftᴵ (⇑ᴵ (ival W A)) ≡ ⇑ᴵ (ival W A)
Beta-ƛ-crossed-no-shift = refl

-- … and the two crossings DO NOT INTERFERE (design law: simultaneity).
-- Crossing a `ƛ` then a `Λ` is crossing a `Λ` then a `ƛ`, on the nose,
-- for EVERY image — which is what makes the two clauses of `substᵐ`
-- independent.
⇑ᴵ-shiftᴵ-comm : (i : Img) → ⇑ᴵ (shiftᴵ i) ≡ shiftᴵ (⇑ᴵ i)
⇑ᴵ-shiftᴵ-comm (ivar x)   = refl
⇑ᴵ-shiftᴵ-comm (ival W A) = refl

-- THE `Λ` CROSSING IS REP-ONLY, AND ITS UNBIND IS WHAT MAKES IT SO: the
-- wrapper's `unbind 0 0` deletes the ordinary name the `Λ` just bound.
Beta-Λ-crossing : ∀ {W A}
  → ⇑ᴵ (ival W A)
      ≡ ival (renᴹ² (ren² idᵗ suc) W
                ⟪ (unbind 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
             (⇑ᵗ A)
Beta-Λ-crossing = refl

-- Beta allocates nothing: the substitution moves no representation.
Beta-no-alloc : ∀ {Δ A N W} → Value W
  → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ ∣ none
Beta-no-alloc = Beta

------------------------------------------------------------------------
-- §6  MERGE — the merged frame is exact
------------------------------------------------------------------------

-- THE ONE FRAME LEFT (the one U lives in) is preserved ON THE NOSE: the
-- merged frame's interior IS the inner frame's own.  Θ₂'s changes travel
-- inward and the surviving boundary REAPPLIES them, so the contractum is
-- one layer, not two; both conversions are weakened onto the merged
-- conversion context (the carried `t₁′`, `c₂′`) and composed there.
Move-inner-frame : ∀ {Γ Γᵢ Γ₁ᵢ : Ctxᵗ} (Θ₁ Θ₂ : Boundary)
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ Θ₁ ⇒ Γ₁ᵢ
  → Γ ⊢ⁱ Θ₁ ++ Θ₂ ⇒ Γ₁ᵢ
Move-inner-frame Θ₁ Θ₂ = merged-interior

-- U is not renamed at all — it retypes exactly where it was.

------------------------------------------------------------------------
-- §7  THE DROP RULE — the frame change in the OTHER direction, and why
--     it is vacuous
------------------------------------------------------------------------

-- The new frame can be STRICTLY MORE NAMEABLE, which the criterion also
-- forbids — but a literal names no type variable at all.
-- Commentary.md § proof/ShiftAudit.agda / §7
Drop$-vacuous : (n : ℕ) (Δ : Ctxᵗ) (Γ : Ctx) → Δ ∣ Γ ⊢ ($ n) ⦂ `ℕ
Drop$-vacuous n Δ Γ = ⊢$

Id-true-vacuous : (Δ : Ctxᵗ) (Γ : Ctx) → Δ ∣ Γ ⊢ `true ⦂ `𝔹
Id-true-vacuous Δ Γ = ⊢true

Id-false-vacuous : (Δ : Ctxᵗ) (Γ : Ctx) → Δ ∣ Γ ⊢ `false ⦂ `𝔹
Id-false-vacuous Δ Γ = ⊢false

-- AND THE STEP RETURNS EXACTLY THE SIMPLE VALUE: the rule's left-hand
-- side is the simple value itself, and a closed simple value at a base
-- type IS a literal (`preserve-Id`).
Id-only-simple : ∀ {Δ M M′ δ} → Δ ⊢ M -→ M′ ∣ δ
  → (∀ {U Θ A} → Simple U → M ≡ U ⟪ Θ , ⌞ id A ⌟ ⟫ → M′ ≡ U)
Id-only-simple (TyBeta v p)              u ()
Id-only-simple (Beta w)                u ()
Id-only-simple (Wrap v w rc ri rd sc)  u ()
Id-only-simple (TyWrap v rc ⊢s p)      u ()
Id-only-simple (Merge u′ it ri r₁ r₂ r⋉ sc₁ sc₂) () refl
Id-only-simple (Id u′ b)             u refl = refl
Id-only-simple (ξ-·₁ st)              u ()
Id-only-simple (ξ-·₂ v st)            u ()
Id-only-simple (ξ-ν st)                u ()
Id-only-simple (ξ-⟪⟫ ri st)            u refl =
  ⊥-elim (value-¬step (V-simple u) st)

------------------------------------------------------------------------
-- §8  THE ξ RULES — the sibling shift IS the context move
------------------------------------------------------------------------

-- Each congruence reduces a subterm IN PLACE, at the very type context
-- the corresponding TYPING rule reads it on.  For ξ-⟪⟫ that is not an
-- equation: it CARRIES the interior reading `boundary` carries, so the two
-- are identified by `interior-functional`.
-- Commentary.md § proof/ShiftAudit.agda / §8
ξ-⟪⟫-frame : ∀ {Γ Γᵢ Γᵢ′ : Ctxᵗ} {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ → Γ ⊢ⁱ Θ ⇒ Γᵢ′ → Γᵢ ≡ Γᵢ′
ξ-⟪⟫-frame = interior-functional

-- THE NEW OBLIGATION OF THE STORE: the sibling must move by EXACTLY
-- the move the context made.  Both are read off the same `Alloc`, so it
-- holds definitionally at both.
ξ-shift-none : (M : Term) (Θ : Boundary) (Δ : Ctxᵗ)
  → (↑ᴹ[ none ] M ≡ M) × (↑ᴮ[ none ] Θ ≡ Θ) × (apply none Δ ≡ Δ)
ξ-shift-none M Θ Δ = refl , refl , refl

ξ-shift-new : (R : Ty) (M : Term) (Θ : Boundary) (Δ : Ctxᵗ)
  → (↑ᴹ[ new R ] M ≡ renᴹᴿ suc M)
    × (↑ᴮ[ new R ] Θ ≡ renᴮᴿ suc Θ)
    × (apply (new R) Δ ≡ (bindR R ∷ reps Δ) ∣ map suc (names Δ))
ξ-shift-new R M Θ Δ = refl , refl , refl

-- … and the reading of the shifted scope at the shifted context is the
-- shifted reading: `interior-ren` at `suc`, cited not restated.

------------------------------------------------------------------------
-- §9  DEAD SHIFT MACHINERY
------------------------------------------------------------------------

-- `shiftᵐ` has NO CONSUMERS (`canon-shiftᵐ` went with
-- proof/Canonicity.agda); `renⁿ` itself is LIVE.
-- Recorded, not deleted: an audit proposes, it does not land.
-- Commentary.md § proof/ShiftAudit.agda / §9
shiftᵐ-is-renⁿ : (M : Term) → shiftᵐ M ≡ renⁿ suc M
shiftᵐ-is-renⁿ M = refl
