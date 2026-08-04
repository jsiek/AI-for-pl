module proof.Core.Properties.NuCastModeRenamerProperties where

-- File Charter:
--   * Defines reusable coercion-mode renamers for type-name insertions,
--     adjacent-name swaps, identity, and composition.
--   * Proves only coercion-mode algebra; it is independent of term
--     imprecision, quotienting, simulation results, and relational worlds.
--   * Supplies the stable cast-mode renaming boundary used by allocation and
--     world-renaming proofs.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import Types using (Renameᵗ; TyVar; extᵗ)
open import ForallPermutation using (swap01ᵗ)
open import Coercions using
  ( Mode
  ; ModeEnv
  ; extᵈ
  ; genᵈ
  ; id-only
  ; instᵈ
  ; mode≤
  ; sealModeAllowed
  ; seal-or-id
  ; tag-or-id
  ; tag-or-idᵈ
  )
open import TermTyping using
  ( CastMode
  ; cast-ext
  ; cast-gen
  ; cast-inst
  ; cast-tag-or-id
  ; cast-weaken
  ; weakenCastᵈ
  )
open import proof.Core.Properties.CoercionProperties using (ModeRename)
open import proof.Core.Properties.TypePreservation using
  ( CastModeRenamer
  ; castModeRenamer-ext
  ; castModeRenamer-suc
  ; modeRename-suc-weakenCast
  )

data LeftInsertion : Renameᵗ → Set where
  left-insertion-suc : LeftInsertion suc
  left-insertion-ext : ∀ {τ} →
    LeftInsertion τ → LeftInsertion (extᵗ τ)

left-insertion-mode :
  ∀ {τ} → LeftInsertion τ → ModeEnv → ModeEnv
left-insertion-mode left-insertion-suc μ = weakenCastᵈ μ
left-insertion-mode (left-insertion-ext ins) μ zero = μ zero
left-insertion-mode (left-insertion-ext ins) μ (suc X) =
  left-insertion-mode ins (λ Y → μ (suc Y)) X

mode≤-refl : ∀ m → mode≤ m m ≡ true
mode≤-refl id-only = refl
mode≤-refl tag-or-id = refl
mode≤-refl seal-or-id = refl

left-insertion-mode-rename :
  ∀ {τ} (ins : LeftInsertion τ) (μ : ModeEnv) →
  ModeRename τ μ (left-insertion-mode ins μ)
left-insertion-mode-rename left-insertion-suc μ =
  modeRename-suc-weakenCast
left-insertion-mode-rename (left-insertion-ext ins) μ zero =
  mode≤-refl (μ zero)
left-insertion-mode-rename (left-insertion-ext ins) μ (suc X) =
  left-insertion-mode-rename ins (λ Y → μ (suc Y)) X

left-insertion-cast-renamer :
  ∀ {τ} → LeftInsertion τ → CastModeRenamer τ
left-insertion-cast-renamer left-insertion-suc = castModeRenamer-suc
left-insertion-cast-renamer (left-insertion-ext ins) =
  castModeRenamer-ext (left-insertion-cast-renamer ins)

push-modeᵈ : Mode → ModeEnv → ModeEnv
push-modeᵈ id-only = extᵈ
push-modeᵈ tag-or-id = genᵈ
push-modeᵈ seal-or-id = instᵈ

cast-push-mode :
  ∀ {m μ} → CastMode μ → CastMode (push-modeᵈ m μ)
cast-push-mode {m = id-only} mode = cast-ext mode
cast-push-mode {m = tag-or-id} mode = cast-gen mode
cast-push-mode {m = seal-or-id} mode = cast-inst mode

swap-head-targetᵈ :
  ∀ {μ} → Mode → CastMode μ → ModeEnv
swap-head-targetᵈ m cast-tag-or-id =
  genᵈ (push-modeᵈ m tag-or-idᵈ)
swap-head-targetᵈ m (cast-ext {μ = μ} mode) =
  extᵈ (push-modeᵈ m μ)
swap-head-targetᵈ m (cast-gen {μ = μ} mode) =
  genᵈ (push-modeᵈ m μ)
swap-head-targetᵈ m (cast-inst {μ = μ} mode) =
  instᵈ (push-modeᵈ m μ)
swap-head-targetᵈ m (cast-weaken {μ = μ} mode) =
  extᵈ (push-modeᵈ m μ)

swap-head-target-mode :
  ∀ {m μ} (mode : CastMode μ) →
  CastMode (swap-head-targetᵈ m mode)
swap-head-target-mode {m = m} cast-tag-or-id =
  cast-gen (cast-push-mode {m = m} cast-tag-or-id)
swap-head-target-mode {m = m} (cast-ext mode) =
  cast-ext (cast-push-mode {m = m} mode)
swap-head-target-mode {m = m} (cast-gen mode) =
  cast-gen (cast-push-mode {m = m} mode)
swap-head-target-mode {m = m} (cast-inst mode) =
  cast-inst (cast-push-mode {m = m} mode)
swap-head-target-mode {m = m} (cast-weaken mode) =
  cast-ext (cast-push-mode {m = m} mode)

swap-mode-targetᵈ :
  ∀ {μ} → CastMode μ → ModeEnv
swap-mode-targetᵈ cast-tag-or-id = tag-or-idᵈ
swap-mode-targetᵈ (cast-ext mode) =
  swap-head-targetᵈ id-only mode
swap-mode-targetᵈ (cast-gen mode) =
  swap-head-targetᵈ tag-or-id mode
swap-mode-targetᵈ (cast-inst mode) =
  swap-head-targetᵈ seal-or-id mode
swap-mode-targetᵈ (cast-weaken mode) =
  swap-head-targetᵈ id-only mode

swap-mode-target-mode :
  ∀ {μ} (mode : CastMode μ) → CastMode (swap-mode-targetᵈ mode)
swap-mode-target-mode cast-tag-or-id = cast-tag-or-id
swap-mode-target-mode (cast-ext mode) =
  swap-head-target-mode mode
swap-mode-target-mode (cast-gen mode) =
  swap-head-target-mode mode
swap-mode-target-mode (cast-inst mode) =
  swap-head-target-mode mode
swap-mode-target-mode (cast-weaken mode) =
  swap-head-target-mode mode

swap-push-agrees :
  ∀ m n μ X →
  push-modeᵈ n (push-modeᵈ m μ) X ≡
    push-modeᵈ m (push-modeᵈ n μ) (swap01ᵗ X)
swap-push-agrees id-only id-only μ zero = refl
swap-push-agrees id-only id-only μ (suc zero) = refl
swap-push-agrees id-only id-only μ (suc (suc X)) = refl
swap-push-agrees id-only tag-or-id μ zero = refl
swap-push-agrees id-only tag-or-id μ (suc zero) = refl
swap-push-agrees id-only tag-or-id μ (suc (suc X)) = refl
swap-push-agrees id-only seal-or-id μ zero = refl
swap-push-agrees id-only seal-or-id μ (suc zero) = refl
swap-push-agrees id-only seal-or-id μ (suc (suc X)) = refl
swap-push-agrees tag-or-id id-only μ zero = refl
swap-push-agrees tag-or-id id-only μ (suc zero) = refl
swap-push-agrees tag-or-id id-only μ (suc (suc X)) = refl
swap-push-agrees tag-or-id tag-or-id μ zero = refl
swap-push-agrees tag-or-id tag-or-id μ (suc zero) = refl
swap-push-agrees tag-or-id tag-or-id μ (suc (suc X)) = refl
swap-push-agrees tag-or-id seal-or-id μ zero = refl
swap-push-agrees tag-or-id seal-or-id μ (suc zero) = refl
swap-push-agrees tag-or-id seal-or-id μ (suc (suc X)) = refl
swap-push-agrees seal-or-id id-only μ zero = refl
swap-push-agrees seal-or-id id-only μ (suc zero) = refl
swap-push-agrees seal-or-id id-only μ (suc (suc X)) = refl
swap-push-agrees seal-or-id tag-or-id μ zero = refl
swap-push-agrees seal-or-id tag-or-id μ (suc zero) = refl
swap-push-agrees seal-or-id tag-or-id μ (suc (suc X)) = refl
swap-push-agrees seal-or-id seal-or-id μ zero = refl
swap-push-agrees seal-or-id seal-or-id μ (suc zero) = refl
swap-push-agrees seal-or-id seal-or-id μ (suc (suc X)) = refl

swap-head-base-agrees :
  ∀ m X →
  genᵈ (push-modeᵈ m tag-or-idᵈ) X ≡
    push-modeᵈ m tag-or-idᵈ (swap01ᵗ X)
swap-head-base-agrees id-only zero = refl
swap-head-base-agrees id-only (suc zero) = refl
swap-head-base-agrees id-only (suc (suc X)) = refl
swap-head-base-agrees tag-or-id zero = refl
swap-head-base-agrees tag-or-id (suc zero) = refl
swap-head-base-agrees tag-or-id (suc (suc X)) = refl
swap-head-base-agrees seal-or-id zero = refl
swap-head-base-agrees seal-or-id (suc zero) = refl
swap-head-base-agrees seal-or-id (suc (suc X)) = refl

swap-head-weaken-agrees :
  ∀ m μ X →
  extᵈ (push-modeᵈ m μ) X ≡
    push-modeᵈ m (weakenCastᵈ μ) (swap01ᵗ X)
swap-head-weaken-agrees id-only μ zero = refl
swap-head-weaken-agrees id-only μ (suc zero) = refl
swap-head-weaken-agrees id-only μ (suc (suc X)) = refl
swap-head-weaken-agrees tag-or-id μ zero = refl
swap-head-weaken-agrees tag-or-id μ (suc zero) = refl
swap-head-weaken-agrees tag-or-id μ (suc (suc X)) = refl
swap-head-weaken-agrees seal-or-id μ zero = refl
swap-head-weaken-agrees seal-or-id μ (suc zero) = refl
swap-head-weaken-agrees seal-or-id μ (suc (suc X)) = refl

swap-head-target-agrees :
  ∀ {m μ} (mode : CastMode μ) X →
  swap-head-targetᵈ m mode X ≡ push-modeᵈ m μ (swap01ᵗ X)
swap-head-target-agrees {m = m} cast-tag-or-id X =
  swap-head-base-agrees m X
swap-head-target-agrees {m = m} (cast-ext {μ = μ} mode) X =
  swap-push-agrees m id-only μ X
swap-head-target-agrees {m = m} (cast-gen {μ = μ} mode) X =
  swap-push-agrees m tag-or-id μ X
swap-head-target-agrees {m = m} (cast-inst {μ = μ} mode) X =
  swap-push-agrees m seal-or-id μ X
swap-head-target-agrees {m = m} (cast-weaken {μ = μ} mode) X =
  swap-head-weaken-agrees m μ X

swap-mode-target-agrees :
  ∀ {μ} (mode : CastMode μ) X →
  swap-mode-targetᵈ mode X ≡ μ (swap01ᵗ X)
swap-mode-target-agrees cast-tag-or-id X = refl
swap-mode-target-agrees (cast-ext mode) X =
  swap-head-target-agrees mode X
swap-mode-target-agrees (cast-gen mode) X =
  swap-head-target-agrees mode X
swap-mode-target-agrees (cast-inst mode) X =
  swap-head-target-agrees mode X
swap-mode-target-agrees (cast-weaken mode) zero =
  swap-head-target-agrees mode zero
swap-mode-target-agrees (cast-weaken mode) (suc zero) =
  swap-head-target-agrees mode (suc zero)
swap-mode-target-agrees (cast-weaken mode) (suc (suc X)) =
  swap-head-target-agrees mode (suc (suc X))

swap01-involutiveᵐ : ∀ X → swap01ᵗ (swap01ᵗ X) ≡ X
swap01-involutiveᵐ zero = refl
swap01-involutiveᵐ (suc zero) = refl
swap01-involutiveᵐ (suc (suc X)) = refl

swap-mode-target-rename :
  ∀ {μ} (mode : CastMode μ) →
  ModeRename swap01ᵗ μ (swap-mode-targetᵈ mode)
swap-mode-target-rename {μ = μ} mode X =
  subst
    (λ m → mode≤ (μ X) m ≡ true)
    target-eq
    (mode≤-refl (μ X))
  where
  target-eq : μ X ≡ swap-mode-targetᵈ mode (swap01ᵗ X)
  target-eq =
    sym
      (trans
        (swap-mode-target-agrees mode (swap01ᵗ X))
        (cong μ (swap01-involutiveᵐ X)))

swap-mode-seal-source :
  ∀ {μ} (mode : CastMode μ) (α : TyVar) →
  sealModeAllowed (swap-mode-targetᵈ mode α) ≡ true →
  ∃[ b ]
    (sealModeAllowed (μ b) ≡ true × swap01ᵗ b ≡ α)
swap-mode-seal-source {μ = μ} mode α ok =
  swap01ᵗ α , source-ok , swap01-involutiveᵐ α
  where
  source-ok : sealModeAllowed (μ (swap01ᵗ α)) ≡ true
  source-ok =
    subst (λ m → sealModeAllowed m ≡ true)
      (swap-mode-target-agrees mode α) ok

castModeRenamer-swap01 : CastModeRenamer swap01ᵗ
castModeRenamer-swap01 =
  record
    { targetᵈ = swap-mode-targetᵈ
    ; target-mode = swap-mode-target-mode
    ; target-rename = swap-mode-target-rename
    ; target-seal-source = swap-mode-seal-source
    }

castModeRenamer-id : CastModeRenamer (λ X → X)
castModeRenamer-id =
  record
    { targetᵈ = λ {μ} mode → μ
    ; target-mode = λ mode → mode
    ; target-rename = λ {μ} mode X → mode≤-refl (μ X)
    ; target-seal-source = λ mode α ok → α , ok , refl
    }

mode≤-trans :
  ∀ m n p →
  mode≤ m n ≡ true →
  mode≤ n p ≡ true →
  mode≤ m p ≡ true
mode≤-trans id-only id-only id-only mn np = refl
mode≤-trans id-only id-only tag-or-id mn np = refl
mode≤-trans id-only id-only seal-or-id mn np = refl
mode≤-trans id-only tag-or-id id-only mn ()
mode≤-trans id-only tag-or-id tag-or-id mn np = refl
mode≤-trans id-only tag-or-id seal-or-id mn ()
mode≤-trans id-only seal-or-id id-only mn ()
mode≤-trans id-only seal-or-id tag-or-id mn ()
mode≤-trans id-only seal-or-id seal-or-id mn np = refl
mode≤-trans tag-or-id id-only id-only () np
mode≤-trans tag-or-id id-only tag-or-id () np
mode≤-trans tag-or-id id-only seal-or-id () np
mode≤-trans tag-or-id tag-or-id id-only mn ()
mode≤-trans tag-or-id tag-or-id tag-or-id mn np = refl
mode≤-trans tag-or-id tag-or-id seal-or-id mn ()
mode≤-trans tag-or-id seal-or-id id-only () np
mode≤-trans tag-or-id seal-or-id tag-or-id () np
mode≤-trans tag-or-id seal-or-id seal-or-id () np
mode≤-trans seal-or-id id-only id-only () np
mode≤-trans seal-or-id id-only tag-or-id () np
mode≤-trans seal-or-id id-only seal-or-id () np
mode≤-trans seal-or-id tag-or-id id-only () np
mode≤-trans seal-or-id tag-or-id tag-or-id () np
mode≤-trans seal-or-id tag-or-id seal-or-id () np
mode≤-trans seal-or-id seal-or-id id-only mn ()
mode≤-trans seal-or-id seal-or-id tag-or-id mn ()
mode≤-trans seal-or-id seal-or-id seal-or-id mn np = refl

modeRename-compose :
  ∀ {τ σ μ ν ξ} →
  ModeRename τ μ ν →
  ModeRename σ ν ξ →
  ModeRename (λ X → σ (τ X)) μ ξ
modeRename-compose
    {τ = τ} {σ = σ} {μ = μ} {ν = nu} {ξ = ξ} rel₁ rel₂ X =
  mode≤-trans (μ X) (nu (τ X)) (ξ (σ (τ X)))
    (rel₁ X) (rel₂ (τ X))

castModeRenamer-compose :
  ∀ {τ σ} →
  CastModeRenamer τ →
  CastModeRenamer σ →
  CastModeRenamer (λ X → σ (τ X))
castModeRenamer-compose {τ = τ} {σ = σ} η θ =
  record
    { targetᵈ = target₂
    ; target-mode = target-mode₂
    ; target-rename = target-rename₂
    ; target-seal-source = target-seal-source₂
    }
  where
  target₂ : ∀ {μ} → CastMode μ → ModeEnv
  target₂ mode =
    CastModeRenamer.targetᵈ θ (CastModeRenamer.target-mode η mode)

  target-mode₂ :
    ∀ {μ} (mode : CastMode μ) → CastMode (target₂ mode)
  target-mode₂ mode =
    CastModeRenamer.target-mode θ
      (CastModeRenamer.target-mode η mode)

  target-rename₂ :
    ∀ {μ} (mode : CastMode μ) →
    ModeRename (λ X → σ (τ X)) μ (target₂ mode)
  target-rename₂ {μ = μ} mode =
    modeRename-compose {τ = τ} {σ = σ} {μ = μ}
      {ν = CastModeRenamer.targetᵈ η mode}
      {ξ = target₂ mode}
      (CastModeRenamer.target-rename η mode)
      (CastModeRenamer.target-rename θ
        (CastModeRenamer.target-mode η mode))

  target-seal-source₂ :
    ∀ {μ} (mode : CastMode μ) (α : TyVar) →
    sealModeAllowed (target₂ mode α) ≡ true →
    ∃[ a ]
      (sealModeAllowed (μ a) ≡ true × σ (τ a) ≡ α)
  target-seal-source₂ mode α ok =
    let b , ok-b , eq-b = CastModeRenamer.target-seal-source θ
          (CastModeRenamer.target-mode η mode) α ok
        a , ok-a , eq-a =
          CastModeRenamer.target-seal-source η mode b ok-b in
    a , ok-a , trans (cong σ eq-a) eq-b
