module LogicalRelationDownward where

-- File Charter:
--   * Experimental downward-closed step-indexed logical relation.
--   * Keeps the existing `LogicalRelation.agda` unchanged.
--   * Uses staged approximants `LR≤ n` so recursion is structurally on `n`.
--   * Exposes the same elimination surface as `LogicalRelation`.

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_; zero; suc; z≤n; s≤s; z<s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.List using (length; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift; 0ℓ) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Types
open import Imprecision
open import TypeProperties
  using
    ( liftSubstˢ
    ; substᵗ-ν-src
    ; substᵗ-⇑ˢ
    ; substᵗ-id
    ; renameᵗ-substᵗ
    ; substᵗ-ground
    ; renameᵗ-preserves-WfTy
    ; renameˢ-preserves-WfTy
    ; TyRenameWf-suc
    ; SealRenameWf-suc
    )
open import UpDown
open import Terms
open import TermPrecision using (PCtx)
open import TermProperties using (Substˣ; substˣ-term)
open import ReductionFresh using (Value; _∣_—→_∣_; _∣_—↠_∣_)

import LogicalRelation as LR
open LR public hiding
  ( 𝒱
  ; ℰ
  ; ℰObs≼
  ; ℰObs≽
  ; observeℰ≼
  ; observeℰ≽
  ; obs≼-stepˡ
  ; obs≼-blameʳ
  ; obs≼-value
  ; obs≽-stepʳ
  ; obs≽-blameʳ
  ; obs≽-value
  ; WfTyClosedᵗ
  ; RelSub
  ; ∅ρ
  ; shift-substᵗ
  ; ⇑ᵗρ
  ; ⇑ˢρ
  ; substᴿ-⊑
  ; RelEnv
  ; ∅γ
  ; ⇓γ
  ; 𝒢
  ; _∣_⊨_⊑_⦂_
  ; _⊨_⊑_⦂_
  ; proj⊨
  )

record LR≤ (n : ℕ) : Set₂ where
  field
    V≤ : ∀ {k A B} → k ≤ n → A ⊑ B → Dir → World → Term → Term → Set₁
    E≤ : ∀ {k A B} → k ≤ n → A ⊑ B → Dir → World → Term → Term → Set₁

mutual
  V-top :
    ∀ {n k A B} →
    LR≤ n →
    k ≤ suc n →
    A ⊑ B →
    Dir →
    World →
    Term →
    Term →
    Set₁
  V-top {k = zero} hist z≤n p dir w V W = Value V × Value W × Lift (lsuc 0ℓ) ⊤
  V-top {k = suc k} hist (s≤s k≤n) p dir w V W =
    Value V × Value W × V-body hist k≤n p dir w V W

  V-body :
    ∀ {n k A B} →
    LR≤ n →
    k ≤ n →
    A ⊑ B →
    Dir →
    World →
    Term →
    Term →
    Set₁
  V-body hist k≤n ⊑-‵ dir w ($ (κℕ m)) ($ (κℕ m′)) = Lift (lsuc 0ℓ) (m ≡ m′)

  V-body {n = n} {k = k} hist k≤n (⊑-⇒ pA pB) dir w V W =
    ∀ {j V′ W′} →
    (j≤k : j ≤ k) →
    LR≤.V≤ hist (≤-trans j≤k k≤n) pA dir w V′ W′ →
    LR≤.E≤ hist (≤-trans j≤k k≤n) pB dir w (V · V′) (W · W′)

  V-body {n = n} {k = k} {A = `∀ A} {B = `∀ B} hist k≤n (⊑-∀ p) dir w V W =
    ∀ {j w′} →
    (j≤k : j ≤ k) →
    w′ ⪰ w →
    (R : Rel) →
    (T U : Ty) →
    LR≤.E≤ hist (≤-trans j≤k k≤n) p dir (extendWorld w′ R)
      (V ⦂∀ A [ T ])
      (W ⦂∀ B [ U ])

  V-body {n = n} {k = k} {A = `∀ A} {B = B} hist k≤n (⊑-ν p) dir w V W =
    ∀ {j w′} →
    (j≤k : j ≤ k) →
    w′ ⪰ w →
    (R : Rel) →
    LR≤.E≤ hist (≤-trans j≤k k≤n) p dir (extendWorld w′ R)
      (V ⦂∀ A [ ｀ length (Σˡ w′) ])
      W

  V-body hist k≤n ⊑-★★ dir w (V up tag G) (W up tag H) =
    Lift (lsuc 0ℓ) (G ≡ H) × LR≤.V≤ hist k≤n (⊑-refl {A = G}) dir w V W

  V-body {k = k} hist k≤n ⊑-★★ dir w (V down seal αˡ) (W down seal αʳ) =
    Σ[ R ∈ Rel ] (η w ∋η αˡ ↔ αʳ ∶ R) × (∀ {j} → j ≤ k → R j dir V W)

  V-body hist k≤n (⊑-★ {G = G} g p) ≼ w V (W up tag H) =
    Lift (lsuc 0ℓ) (G ≡ H) × LR≤.V≤ hist k≤n p ≼ w V W

  V-body hist k≤n (⊑-★ {G = G} g p) ≽ w V (W up tag H) =
    Lift (lsuc 0ℓ) (G ≡ H) × LR≤.V≤ hist k≤n p ≽ w V W

  V-body {k = k} hist k≤n (⊑-｀ {α = α}) dir w (V down seal βˡ) (W down seal βʳ) =
    Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
      (η w ∋η α ↔ α ∶ R) ×
      (∀ {j} → j ≤ k → R j dir V W)

  V-body hist k≤n p dir w V W = Lift (lsuc 0ℓ) ⊥

  E-top :
    ∀ {n k A B} →
    LR≤ n →
    k ≤ suc n →
    A ⊑ B →
    Dir →
    World →
    Term →
    Term →
    Set₁
  E-top {k = zero} hist z≤n p dir w Mˡ Mʳ = Lift (lsuc 0ℓ) ⊤

  E-top {k = suc k} hist (s≤s k≤n) p ≼ w Mˡ Mʳ =
    (Σ[ Σˡ′ ∈ Store ] Σ[ Mˡ′ ∈ Term ]
      (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) ×
      LR≤.E≤ hist k≤n p ≼ (mkWorld Σˡ′ (Σʳ w) (η w)) Mˡ′ Mʳ)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mˡ × Σ[ Σʳ′ ∈ Store ] Σ[ Wʳ ∈ Term ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) ×
      LR≤.V≤ hist k≤n p ≼ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Wʳ)

  E-top {k = suc k} hist (s≤s k≤n) p ≽ w Mˡ Mʳ =
    (Σ[ Σʳ′ ∈ Store ] Σ[ Mʳ′ ∈ Term ]
      (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) ×
      LR≤.E≤ hist k≤n p ≽ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Mʳ′)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mʳ × Σ[ Σˡ′ ∈ Store ] Σ[ Wˡ ∈ Term ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) ×
      LR≤.V≤ hist k≤n p ≽ (mkWorld Σˡ′ (Σʳ w) (η w)) Wˡ Mʳ)

build : (n : ℕ) → LR≤ n
build zero .LR≤.V≤ {zero} z≤n p dir w V W = Value V × Value W × Lift (lsuc 0ℓ) ⊤
build zero .LR≤.V≤ {suc k} ()
build zero .LR≤.E≤ {zero} z≤n p dir w M M′ = Lift (lsuc 0ℓ) ⊤
build zero .LR≤.E≤ {suc k} ()
build (suc n) .LR≤.V≤ {k} k≤ p dir w V W = V-top (build n) k≤ p dir w V W
build (suc n) .LR≤.E≤ {k} k≤ p dir w M M′ = E-top (build n) k≤ p dir w M M′

𝒱 : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
𝒱 p n dir w V W = LR≤.V≤ (build n) ≤-refl p dir w V W

𝒱′ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
𝒱′ p zero dir w V W = Lift (lsuc 0ℓ) ⊤
𝒱′ p (suc n) dir w V W = V-body (build n) ≤-refl p dir w V W

ℰ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
ℰ p n dir w M M′ = LR≤.E≤ (build n) ≤-refl p dir w M M′

𝒱↓ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
𝒱↓ = 𝒱

ℰ↓ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
ℰ↓ = ℰ

------------------------------------------------------------------------
-- Elimination interface (same surface as `LogicalRelation`)
------------------------------------------------------------------------

𝒱-left-value :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {dir : Dir} {w : World}
    {V W : Term} →
  𝒱 p n dir w V W →
  Value V
𝒱-left-value {n = zero} rel = proj₁ rel
𝒱-left-value {n = suc n} rel = proj₁ rel

𝒱-right-value :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {dir : Dir} {w : World}
    {V W : Term} →
  𝒱 p n dir w V W →
  Value W
𝒱-right-value {n = zero} rel = proj₁ (proj₂ rel)
𝒱-right-value {n = suc n} rel = proj₁ (proj₂ rel)

𝒱-core :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {dir : Dir} {w : World}
    {V W : Term} →
  𝒱 p n dir w V W →
  𝒱′ p n dir w V W
𝒱-core {n = zero} rel = proj₂ (proj₂ rel)
𝒱-core {n = suc n} rel = proj₂ (proj₂ rel)

data ℰObs≼ {A B : Ty} (p : A ⊑ B) (n : ℕ) (w : World)
  (Mˡ Mʳ : Term) : Set₁ where
  obs≼-stepˡ :
    (Σˡ′ : Store) (Mˡ′ : Term) →
    (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) →
    ℰ p n ≼ (mkWorld Σˡ′ (Σʳ w) (η w)) Mˡ′ Mʳ →
    ℰObs≼ p n w Mˡ Mʳ

  obs≼-blameʳ :
    (Σʳ′ : Store) (ℓ : Label) →
    (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ) →
    ℰObs≼ p n w Mˡ Mʳ

  obs≼-value :
    Value Mˡ →
    (Σʳ′ : Store) (Wʳ : Term) →
    (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) →
    𝒱 p n ≼ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Wʳ →
    ℰObs≼ p n w Mˡ Mʳ

data ℰObs≽ {A B : Ty} (p : A ⊑ B) (n : ℕ) (w : World)
  (Mˡ Mʳ : Term) : Set₁ where
  obs≽-stepʳ :
    (Σʳ′ : Store) (Mʳ′ : Term) →
    (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) →
    ℰ p n ≽ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Mʳ′ →
    ℰObs≽ p n w Mˡ Mʳ

  obs≽-blameʳ :
    (Σʳ′ : Store) (ℓ : Label) →
    (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ) →
    ℰObs≽ p n w Mˡ Mʳ

  obs≽-value :
    Value Mʳ →
    (Σˡ′ : Store) (Wˡ : Term) →
    (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) →
    𝒱 p n ≽ (mkWorld Σˡ′ (Σʳ w) (η w)) Wˡ Mʳ →
    ℰObs≽ p n w Mˡ Mʳ

observeℰ≼ :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {w : World} {Mˡ Mʳ : Term} →
  ℰ p (suc n) ≼ w Mˡ Mʳ →
  ℰObs≼ p n w Mˡ Mʳ
observeℰ≼ rel with rel
observeℰ≼ rel | inj₁ red =
  obs≼-stepˡ (proj₁ red) (proj₁ (proj₂ red))
    (proj₁ (proj₂ (proj₂ red))) (proj₂ (proj₂ (proj₂ red)))
observeℰ≼ rel | inj₂ (inj₁ blm) =
  obs≼-blameʳ (proj₁ blm) (proj₁ (proj₂ blm)) (proj₂ (proj₂ blm))
observeℰ≼ rel | inj₂ (inj₂ val) =
  obs≼-value (proj₁ val) (proj₁ (proj₂ val)) (proj₁ (proj₂ (proj₂ val)))
    (proj₁ (proj₂ (proj₂ (proj₂ val)))) (proj₂ (proj₂ (proj₂ (proj₂ val))))

observeℰ≽ :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {w : World} {Mˡ Mʳ : Term} →
  ℰ p (suc n) ≽ w Mˡ Mʳ →
  ℰObs≽ p n w Mˡ Mʳ
observeℰ≽ rel with rel
observeℰ≽ rel | inj₁ red =
  obs≽-stepʳ (proj₁ red) (proj₁ (proj₂ red))
    (proj₁ (proj₂ (proj₂ red))) (proj₂ (proj₂ (proj₂ red)))
observeℰ≽ rel | inj₂ (inj₁ blm) =
  obs≽-blameʳ (proj₁ blm) (proj₁ (proj₂ blm)) (proj₂ (proj₂ blm))
observeℰ≽ rel | inj₂ (inj₂ val) =
  obs≽-value (proj₁ val) (proj₁ (proj₂ val)) (proj₁ (proj₂ (proj₂ val)))
    (proj₁ (proj₂ (proj₂ (proj₂ val)))) (proj₂ (proj₂ (proj₂ (proj₂ val))))

------------------------------------------------------------------------
-- Environment interpretation for open terms
------------------------------------------------------------------------

WfTyClosedᵗ : TyCtx → Ty → Set
WfTyClosedᵗ Δ A = Σ[ Ψ ∈ SealCtx ] WfTy Δ Ψ A

record RelSub (Δ : TyCtx) : Set₁ where
  field
    leftᵗ : Substᵗ
    rightᵗ : Substᵗ
    left-closed : (X : TyVar) → WfTyClosedᵗ Δ (leftᵗ X)
    right-closed : (X : TyVar) → WfTyClosedᵗ Δ (rightᵗ X)
    precᵗ : (X : TyVar) → leftᵗ X ⊑ rightᵗ X
open RelSub public

∅ρ : RelSub 0
(∅ρ .leftᵗ) = λ _ → ‵ `ℕ
(∅ρ .rightᵗ) = λ _ → ‵ `ℕ
(∅ρ .left-closed) = λ _ → 0 , wfBase
(∅ρ .right-closed) = λ _ → 0 , wfBase
(∅ρ .precᵗ) = λ _ → ⊑-‵

shift-substᵗ : (A : Ty) → substᵗ (λ X → ＇ suc X) A ≡ renameᵗ suc A
shift-substᵗ A = trans (sym (renameᵗ-substᵗ suc (λ X → ＇ X) A))
                       (cong (renameᵗ suc) (substᵗ-id A))

⇑ᵗρ : ∀ {Δ} → RelSub Δ → RelSub (suc Δ)
(⇑ᵗρ ρ .leftᵗ) = extsᵗ (leftᵗ ρ)
(⇑ᵗρ ρ .rightᵗ) = extsᵗ (rightᵗ ρ)
(⇑ᵗρ ρ .left-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .left-closed) (suc X) =
  let Ψ , wfA = left-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .right-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .right-closed) (suc X) =
  let Ψ , wfA = right-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .precᵗ) zero = ⊑-＇
(⇑ᵗρ ρ .precᵗ) (suc X) =
  cast-⊑ (shift-substᵗ (leftᵗ ρ X))
          (shift-substᵗ (rightᵗ ρ X))
          (Imprecision.substᵗ-⊑ (λ Y → ＇ suc Y) (precᵗ ρ X))

⇑ˢρ : ∀ {Δ} → RelSub Δ → RelSub Δ
(⇑ˢρ ρ .leftᵗ) = liftSubstˢ (leftᵗ ρ)
(⇑ˢρ ρ .rightᵗ) = liftSubstˢ (rightᵗ ρ)
(⇑ˢρ ρ .left-closed) X =
  let Ψ , wfA = left-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .right-closed) X =
  let Ψ , wfA = right-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .precᵗ) X = renameˢ-⊑ suc (precᵗ ρ X)

substᴿ-⊑ : ∀ {Δ} → (ρ : RelSub Δ) → ∀ {A B} → A ⊑ B → substᵗ (leftᵗ ρ) A ⊑ substᵗ (rightᵗ ρ) B
substᴿ-⊑ ρ ⊑-★★ = ⊑-★★
substᴿ-⊑ ρ (⊑-★ g p) = ⊑-★ (substᵗ-ground (rightᵗ ρ) g) (substᴿ-⊑ ρ p)
substᴿ-⊑ ρ (⊑-＇ {X}) = precᵗ ρ X
substᴿ-⊑ ρ ⊑-｀ = ⊑-｀
substᴿ-⊑ ρ ⊑-‵ = ⊑-‵
substᴿ-⊑ ρ (⊑-⇒ p q) = ⊑-⇒ (substᴿ-⊑ ρ p) (substᴿ-⊑ ρ q)
substᴿ-⊑ ρ (⊑-∀ p) = ⊑-∀ (substᴿ-⊑ (⇑ᵗρ ρ) p)
substᴿ-⊑ ρ (⊑-ν {A = A} {B = B} p) =
  ⊑-ν (cast-⊑ (substᵗ-ν-src (leftᵗ ρ) A)
               (substᵗ-⇑ˢ (rightᵗ ρ) B)
               (substᴿ-⊑ (⇑ˢρ ρ) p))

record RelEnv : Set where
  field
    leftˣ : Substˣ
    rightˣ : Substˣ
open RelEnv public

∅γ : RelEnv
(∅γ .leftˣ) x = ` x
(∅γ .rightˣ) x = ` x

⇓γ : RelEnv → RelEnv
(⇓γ γ .leftˣ) x = leftˣ γ (suc x)
(⇓γ γ .rightˣ) x = rightˣ γ (suc x)

𝒢 : PCtx → ℕ → Dir → World → RelSub 0 → RelEnv → Set₁
𝒢 [] n dir w ρ γ = Lift (lsuc 0ℓ) ⊤
𝒢 ((A , B , p) ∷ Γ) zero dir w ρ γ =
  Value (leftˣ γ zero) ×
  Value (rightˣ γ zero) ×
  𝒱 (substᴿ-⊑ ρ p) zero dir w (leftˣ γ zero) (rightˣ γ zero) ×
  𝒢 Γ zero dir w ρ (⇓γ γ)
𝒢 ((A , B , p) ∷ Γ) (suc n) dir w ρ γ =
  Value (leftˣ γ zero) ×
  Value (rightˣ γ zero) ×
  𝒱 (substᴿ-⊑ ρ p) n dir w (leftˣ γ zero) (rightˣ γ zero) ×
  𝒢 Γ (suc n) dir w ρ (⇓γ γ)

_∣_⊨_⊑_⦂_ : PCtx → Dir → Term → Term → ∀ {A B} → A ⊑ B → Set₁
Γ ∣ dir ⊨ M ⊑ M′ ⦂ p =
  ∀ (n : ℕ) (w : World) (ρ : RelSub 0) (γ : RelEnv) →
  𝒢 Γ n dir w ρ γ →
  ℰ (substᴿ-⊑ ρ p) n dir w
    (substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M))
    (substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′))

_⊨_⊑_⦂_ : PCtx → Term → Term → ∀ {A B} → A ⊑ B → Set₁
Γ ⊨ M ⊑ M′ ⦂ p = (Γ ∣ ≼ ⊨ M ⊑ M′ ⦂ p) × (Γ ∣ ≽ ⊨ M ⊑ M′ ⦂ p)

proj⊨ :
  ∀ {Γ M M′ A B} {p : A ⊑ B} →
  (dir : Dir) →
  Γ ⊨ M ⊑ M′ ⦂ p →
  Γ ∣ dir ⊨ M ⊑ M′ ⦂ p
proj⊨ ≼ rel = proj₁ rel
proj⊨ ≽ rel = proj₂ rel
