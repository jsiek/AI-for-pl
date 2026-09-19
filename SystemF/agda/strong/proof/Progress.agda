module strong.proof.Progress where

-- PROGRESS for the two-universe conversion-boundary calculus.
--
-- The ordinary cases are the standard induction, using
-- strong.proof.Canonical.  Boundary reductions additionally construct the
-- relational context readings and re-spellings carried by the new rules.
-- `Peel`'s package is proved in strong.CtxMorph/strong.Conversion.
--
-- One new major invariant remains for review: a merged frame `Θ₁ ⋉ Θ₂`
-- has a conversion reading that retains every name available in both the
-- outer and inner conversion contexts.  `MergedReading` states that fact
-- directly; `Impl` proves progress from it.  Nothing is postulated.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.Canonical

private
  variable
    Δ Δ′ : Ctxᵗ
    A B R : Ty
    X α : ℕ

------------------------------------------------------------------------
-- 1. Local inversions and representation readings
------------------------------------------------------------------------

wf-same : Δ ⊢ᵗ A → ∃[ R ] names Δ ⊢ A ~ R
wf-same (wf-var (α , name)) = ` α , same-var name
wf-same wf-ℕ = `ℕ , same-ℕ
wf-same wf-𝔹 = `𝔹 , same-𝔹
wf-same (wf-⇒ wA wB) with wf-same wA | wf-same wB
wf-same (wf-⇒ wA wB) | R , p | S , q = R ⇒ S , same-⇒ p q
wf-same (wf-∀ wA) with wf-same wA
wf-same (wf-∀ wA) | R , p = `∀ R , same-∀ p

sameTy-base-src : Base A → SameTy Δ B Δ′ A → B ≡ A
sameTy-base-src base-ℕ (`ℕ , same-ℕ , same-ℕ) = refl
sameTy-base-src base-𝔹 (`𝔹 , same-𝔹 , same-𝔹) = refl

sameTy-target-var⁻ : SameTy Δ A Δ′ (` X)
  → Σ[ Y ∈ ℕ ] ((A ≡ ` Y) × SameTy Δ (` Y) Δ′ (` X))
sameTy-target-var⁻ (` α , same-var p , same-var q) =
  _ , refl , (` α , same-var p , same-var q)

sameTy-target-∀⁻ : SameTy Δ A Δ′ (`∀ B)
  → Σ[ A₀ ∈ Ty ] ((A ≡ `∀ A₀) × SameTy (underΛ Δ) A₀
                                                (underΛ Δ′) B)
sameTy-target-∀⁻ (`∀ R , same-∀ p , same-∀ q) =
  _ , refl , (R , p , q)

------------------------------------------------------------------------
-- 2. The reviewed boundary package and the deferred merged invariant
------------------------------------------------------------------------

-- The conversion reading of `Θ₁ ⋉ Θ₂` must retain both sources whose
-- spellings the two id-layer rules move into that merged frame:
--
--   * repaired `CancelR` (2026-09-19) moves the cancelled seal's source,
--     read at Θ₁'s conversion context;
--   * `IdPush` moves a variable read at the same context.
--
-- `Keeps` states only name availability.  strong.Conversion.respell-ty then
-- constructs the `SameTy` premise at the exact type being moved.
--
-- NOTE, PENDING REVIEW.  With `CancelR` repaired, BOTH id-layer rules now
-- read at `Δ₁ᶜ`, so this proof no longer consumes the outer
-- `Keeps (names Δᶜ) (names Δ⋉ᶜ)` component.  The statement is NOT shrunk
-- here: it is one of the statements awaiting Jeremy's review, and
-- shrinking it is a separate decision.
MergedReading : Set
MergedReading = ∀ {Δ Δᵢ Δᶜ Δ₁ᵢ Δ₁ᶜ Θ₁ Θ₂}
  → MorphWf Δ Θ₂ Δᵢ Δᶜ
  → MorphWf Δᵢ Θ₁ Δ₁ᵢ Δ₁ᶜ
  → Σ[ Δ⋉ᶜ ∈ Ctxᵗ ]
      ((extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ)
        × Keeps (names Δᶜ) (names Δ⋉ᶜ)
        × Keeps (names Δ₁ᶜ) (names Δ⋉ᶜ))

------------------------------------------------------------------------
-- 3. Base identities
------------------------------------------------------------------------

progress-id-base : ∀ {Δ Δᵢ Θ M A}
  → Value M
  → Base A
  → Δᵢ ∣ [] ⊢ M ⦂ A
  → Σ[ M′ ∈ Term ] (Δ ⊢ M ⟪ Θ , id A ⟫ -→ M′)
progress-id-base v b ⊢M with canon-base v b ⊢M
progress-id-base v b ⊢M | inj₁ (n , refl) = $ n , Drop$ b
progress-id-base v base-ℕ ⊢M | inj₂ (inj₁ refl) with ⊢M
progress-id-base v base-ℕ ⊢M | inj₂ (inj₁ refl) | ()
progress-id-base v base-𝔹 ⊢M | inj₂ (inj₁ refl) = `true , Drop-true
progress-id-base v base-ℕ ⊢M | inj₂ (inj₂ refl) with ⊢M
progress-id-base v base-ℕ ⊢M | inj₂ (inj₂ refl) | ()
progress-id-base v base-𝔹 ⊢M | inj₂ (inj₂ refl) = `false , Drop-false

------------------------------------------------------------------------
-- 4. Progress from the merged-reading invariant
------------------------------------------------------------------------

module Impl (merged-reading : MergedReading) where

  -- An active `unseal` sees a value at a variable type.  `canon-var`
  -- exposes either CancelR's or IdPush's inner layer; the two `MorphWf`
  -- witnesses then feed the deferred merged-reading invariant.
  progress-unseal : ∀ {Δ Δᵢ Δᶜ Θ Y M Bᵢ A}
    → Value M
    → MorphWf Δ Θ Δᵢ Δᶜ
    → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
    → SameTy Δᵢ Bᵢ Δᶜ (` Y)
    → Δᶜ ∋ Y := A
    → Σ[ M′ ∈ Term ] (Δ ⊢ M ⟪ Θ , unseal Y ⟫ -→ M′)
  progress-unseal {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} v mwΘ ⊢M sameᵢ d
    with sameTy-target-var⁻ {Δ = Δᵢ} {Δ′ = Δᶜ} sameᵢ
  progress-unseal v mwΘ ⊢M sameᵢ d | Z , refl , sameZ
    with canon-var v ⊢M
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl with ⊢M
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl
    | env mw₁ ⊢W (conv-seal dX) same₁ sameₑ₁ wE₁
    with merged-reading mwΘ mw₁
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl
    | env mw₁ ⊢W (conv-seal dX) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₂ , keep₁ with dX
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl
    | env mw₁ ⊢W (conv-seal dX) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₂ , keep₁
    | α , R , nameX , repX , sameA with respell-ty keep₁ sameA
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl
    | env mw₁ ⊢W (conv-seal dX) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₂ , keep₁
    | α , R , nameX , repX , sameA | A′ , sameA′ =
    _ , CancelR vW (mw-interior mwΘ) (mw-conversion mw₁)
                (α , R , nameX , repX , sameA)
                r⋉ (R , sameA′ , sameA) (mw-conversion mwΘ) d
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₂ refl with ⊢M
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₂ refl
    | env mw₁ ⊢W (conv-idv (α , nameX)) same₁ sameₑ₁ wE₁
    with merged-reading mwΘ mw₁
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₂ refl
    | env mw₁ ⊢W (conv-idv (α , nameX)) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₂ , keep₁ with keep₁ (_ , nameX)
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₂ refl
    | env mw₁ ⊢W (conv-idv (α , nameX)) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₂ , keep₁ | X′ , nameX′ =
    _ , IdPush vW (mw-interior mwΘ) (mw-conversion mw₁) r⋉
               (` α , same-var nameX′ , same-var nameX)
               (mw-conversion mwΘ) d

  -- Once the interior is a value, conversion classification decides whether
  -- the whole boundary is a value or one of the four active redex shapes.
  progress-env : ∀ {Δ Δᵢ Δᶜ Θ c M Bᵢ Cᵢ Cₑ}
    → Value M
    → MorphWf Δ Θ Δᵢ Δᶜ
    → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
    → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
    → SameTy Δᵢ Bᵢ Δᶜ Cᵢ
    → Value (M ⟪ Θ , c ⟫)
      ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M ⟪ Θ , c ⟫ -→ M′))
  progress-env v mwΘ ⊢M ⊢c sameᵢ with act-or-inert ⊢c
  progress-env v mwΘ ⊢M ⊢c sameᵢ | inj₂ ic = inj₁ (V-⟪⟫ v ic)
  progress-env v mwΘ ⊢M ⊢c sameᵢ | inj₁ (A-idb b)
    with conv-id-base-src b ⊢c
  progress-env {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} v mwΘ ⊢M ⊢c sameᵢ
    | inj₁ (A-idb b) | refl =
    inj₂ (progress-id-base v b
      (⊢ty≡ (sameTy-base-src {Δ = Δᵢ} {Δ′ = Δᶜ} b sameᵢ) ⊢M))
  progress-env v mwΘ ⊢M ⊢c sameᵢ | inj₁ A-unseal
    with conv-unseal-src ⊢c
  progress-env v mwΘ ⊢M ⊢c sameᵢ | inj₁ A-unseal | refl =
    inj₂ (progress-unseal v mwΘ ⊢M sameᵢ
             (unseal-target-is-rep ⊢c))

  -- A function-conversion wrapper carries its own MorphWf and the domain
  -- conversion typing needed by the core `peel-premises-env` theorem.
  progress-peel : ∀ {Δ W M Θ s t A B}
    → Value W
    → Value M
    → Δ ∣ [] ⊢ W ⟪ Θ , s ↦ t ⟫ ⦂ (A ⇒ B)
    → Σ[ N ∈ Term ] (Δ ⊢ (W ⟪ Θ , s ↦ t ⟫) · M -→ N)
  progress-peel vW vM
    (env mwΘ ⊢W (conv-fun ⊢s ⊢t) sameᵢ sameₑ wE)
    with peel-premises-env mwΘ ⊢s
  progress-peel vW vM
    (env mwΘ ⊢W (conv-fun ⊢s ⊢t) sameᵢ sameₑ wE)
    | Δᵈ , s′ , rd , sc =
    _ , Peel vW vM (mw-conversion mwΘ) (mw-interior mwΘ) rd sc

  -- The outer conversion's `SameTy` premise exposes the interior ∀ body and
  -- is exactly TyPeelR-⟪⟫'s re-spelling premise.
  progress-·[]-∀conv : ∀ {Δ V Θ s B A C}
    → Value V
    → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
    → Σ[ M ∈ Term ] (Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] -→ M)
  progress-·[]-∀conv v
    (⊢·[] (env mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    with conv-all-inv ⊢c
  progress-·[]-∀conv v
    (⊢·[] (env {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
                mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    | A₀ , B₀ , refl , eqₑ , ⊢s
    with sameTy-target-∀⁻ {Δ = Δᵢ} {Δ′ = Δᶜ} sameᵢ
  progress-·[]-∀conv v
    (⊢·[] (env mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    | A₀ , B₀ , refl , eqₑ , ⊢s | D , refl , sameD
    with canon-∀ v ⊢V | wf-same wA
  progress-·[]-∀conv v
    (⊢·[] (env mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    | A₀ , B₀ , refl , eqₑ , ⊢s | D , refl , sameD
    | inj₁ (N , vN , refl) | R , p =
    _ , TyPeelR-Λ vN (mw-conversion mwΘ) ⊢s p
  progress-·[]-∀conv v
    (⊢·[] (env mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    | A₀ , B₀ , refl , eqₑ , ⊢s | D , refl , sameD
    | inj₂ (W , Θ′ , s′ , vW , refl) | R , p =
    _ , TyPeelR-⟪⟫ vW (mw-interior mwΘ) (mw-conversion mwΘ)
                      ⊢s sameD p

  ----------------------------------------------------------------------
  -- 5. The induction
  ----------------------------------------------------------------------

  progress : ∀ {Δ M A} → Δ ∣ [] ⊢ M ⦂ A
    → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))
  progress (⊢` ())
  progress ⊢$ = inj₁ V-$
  progress ⊢true = inj₁ V-true
  progress ⊢false = inj₁ V-false
  progress (⊢ƛ _ _) = inj₁ V-ƛ
  progress (⊢Λ ⊢N) with progress ⊢N
  progress (⊢Λ ⊢N) | inj₁ vN = inj₁ (V-Λ vN)
  progress (⊢Λ ⊢N) | inj₂ (N′ , st) = inj₂ (Λ N′ , ξ-Λ st)
  progress (⊢· ⊢L ⊢M) with progress ⊢L
  progress (⊢· ⊢L ⊢M) | inj₂ (L′ , st) =
    inj₂ (L′ · _ , ξ-·-l st)
  progress (⊢· ⊢L ⊢M) | inj₁ vL with progress ⊢M
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₂ (M′ , st) =
    inj₂ (_ · M′ , ξ-·-r vL st)
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM with canon-⇒ vL ⊢L
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM | inj₁ (N , refl) =
    inj₂ (_ , Beta vM)
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM
    | inj₂ (W , Θ , s , t , vW , refl) =
    inj₂ (progress-peel vW vM ⊢L)
  progress (⊢·[] ⊢L wA) with progress ⊢L
  progress (⊢·[] ⊢L wA) | inj₂ (L′ , st) =
    inj₂ (L′ ·[ _ , _ ] , ξ-·[] st)
  progress (⊢·[] ⊢L wA) | inj₁ vL with canon-∀ vL ⊢L
  progress (⊢·[] ⊢L wA) | inj₁ vL | inj₁ (N , vN , refl)
    with wf-same wA
  progress (⊢·[] ⊢L wA) | inj₁ vL | inj₁ (N , vN , refl)
    | R , p = inj₂ (_ , TyBeta vN p)
  progress (⊢·[] ⊢L wA) | inj₁ vL
    | inj₂ (W , Θ , s , vW , refl) =
    inj₂ (progress-·[]-∀conv vW (⊢·[] ⊢L wA))
  progress (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) with progress ⊢M
  progress (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | inj₂ (M′ , st) =
    inj₂ (M′ ⟪ _ , _ ⟫ , ξ-⟪⟫ (mw-interior mwΘ) st)
  progress (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | inj₁ vM =
    progress-env vM mwΘ ⊢M ⊢c sameᵢ
