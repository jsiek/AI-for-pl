module proof.DynamicGradualGuaranteeCounterexample where

-- File Charter:
--   * Tests a right-`ν` candidate counterexample for the current
--     `dynamicGradualGuarantee` statement.
--   * The target opens a `ν` and emits a right-only runtime bullet, while the
--     source is a closed numeric constant and therefore cannot take a source
--     step.
--   * No postulates are introduced; the final theorem states that the current
--     DGG statement would imply `⊥`.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction
open import NarrowWiden
open import TermNarrowing
open import proof.CatchupStore using (combineStoreNrw)
open import proof.NuPreservation using (value-no-step)

ℕ0 : Term
ℕ0 = $ (κℕ 0)

data Isℕ0 : Term → Set where
  isℕ0 : Isℕ0 ℕ0

data Isℕ0Bullet : Term → Set where
  isℕ0-bullet : Isℕ0Bullet (ℕ0 •)

data Isℕ0BulletIdCast : Term → Set where
  isℕ0-bullet-id-cast :
    Isℕ0BulletIdCast ((ℕ0 •) ⟨ id (‵ `ℕ) ⟩)

isℕ0-⇑ᵗᵐ-inv :
  ∀ {M} →
  Isℕ0 (⇑ᵗᵐ M) →
  Isℕ0 M
isℕ0-⇑ᵗᵐ-inv {` x} ()
isℕ0-⇑ᵗᵐ-inv {ƛ M} ()
isℕ0-⇑ᵗᵐ-inv {L · M} ()
isℕ0-⇑ᵗᵐ-inv {Λ M} ()
isℕ0-⇑ᵗᵐ-inv {M •} ()
isℕ0-⇑ᵗᵐ-inv {ν A M c} ()
isℕ0-⇑ᵗᵐ-inv {$ (κℕ zero)} isℕ0 = isℕ0
isℕ0-⇑ᵗᵐ-inv {$ (κℕ (suc n))} ()
isℕ0-⇑ᵗᵐ-inv {L ⊕[ op ] M} ()
isℕ0-⇑ᵗᵐ-inv {M ⟨ c ⟩} ()
isℕ0-⇑ᵗᵐ-inv {blame} ()

isℕ0-open-any :
  ∀ {M α β} →
  Isℕ0 (M [ α ]ᵀ) →
  Isℕ0 (M [ β ]ᵀ)
isℕ0-open-any {` x} ()
isℕ0-open-any {ƛ M} ()
isℕ0-open-any {L · M} ()
isℕ0-open-any {Λ M} ()
isℕ0-open-any {M •} ()
isℕ0-open-any {ν A M c} ()
isℕ0-open-any {$ (κℕ zero)} isℕ0 = isℕ0
isℕ0-open-any {$ (κℕ (suc n))} ()
isℕ0-open-any {L ⊕[ op ] M} ()
isℕ0-open-any {M ⟨ c ⟩} ()
isℕ0-open-any {blame} ()

isℕ0-bullet-inner :
  ∀ {M} →
  Isℕ0Bullet (M •) →
  Isℕ0 M
isℕ0-bullet-inner isℕ0-bullet = isℕ0

isℕ0-bullet-id-cast-inner :
  ∀ {M c} →
  Isℕ0BulletIdCast (M ⟨ c ⟩) →
  Isℕ0Bullet M
isℕ0-bullet-id-cast-inner isℕ0-bullet-id-cast = isℕ0-bullet

idℕᶜ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ
idℕᶜ = cast-id wfBase refl , cross (id-‵ `ℕ)

right-ν-example :
  zero ∣ [] ∣ [] ⊢
    ℕ0 ⊒ ν ★ ℕ0 (id (‵ `ℕ)) ∶ id (‵ `ℕ)
right-ν-example =
  ⊒ν idℕᶜ (κ⊒κ (κℕ 0))

right-ν-step-example :
  ν ★ ℕ0 (id (‵ `ℕ)) —→[ bind ★ ]
    ((ℕ0 •) ⟨ id (‵ `ℕ) ⟩)
right-ν-step-example = ν-step ($ (κℕ 0)) no•-$

no-const-const-gen :
  ∀ {Δ σ γ L L′ r A p} →
  Isℕ0 L →
  Isℕ0 L′ →
  Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ r →
  r ≡ gen A p →
  ⊥
no-const-const-gen isL isL′ (extend qᶜ pαᶜ M⊒M′) eq =
  no-const-const-gen isL isL′ M⊒M′ eq
no-const-const-gen isL isL′ (split qᶜ pαᶜ M⊒M′) eq =
  no-const-const-gen (isℕ0-open-any isL) isL′ M⊒M′ eq
no-const-const-gen isL () (⊒blame pᶜ) eq
no-const-const-gen () isL′ (x⊒x pᶜ x∋p) eq
no-const-const-gen () isL′ (ƛ⊒ƛ p↦qᶜ M⊒M′) eq
no-const-const-gen () isL′ (·⊒· qᶜ L⊒L′ M⊒M′) eq
no-const-const-gen () isL′ (Λ⊒Λ allᶜ vV V⊒V′) eq
no-const-const-gen isL () (⊒Λ pᶜ M⊒V′) eq
no-const-const-gen isL () (⊒⟨ν⟩ pᶜ i M⊒V′s) eq
no-const-const-gen () isL′ (α⊒α qᶜ pαᶜ L⊒L′) eq
no-const-const-gen isL () (⊒α pαᶜ L⊒L′) eq
no-const-const-gen () isL′ (ν⊒ν pᶜ qᶜ M⊒M′) eq
no-const-const-gen isL () (⊒ν pᶜ M⊒M′) eq
no-const-const-gen () isL′ (ν⊒ pᶜ M⊒M′) eq
no-const-const-gen isℕ0 isℕ0 (κ⊒κ κ) eq = no-id-gen eq
  where
    no-id-gen : ∀ {A p} → id (‵ `ℕ) ≡ gen A p → ⊥
    no-id-gen ()
no-const-const-gen () isL′ (⊕⊒⊕ M⊒M′ N⊒N′) eq
no-const-const-gen isL () (⊒cast+ qᶜ q⨟s≈r M⊒M′) eq
no-const-const-gen isL () (⊒cast- qᶜ q⨟s≈r M⊒M′) eq
no-const-const-gen () isL′ (cast+⊒ pᶜ r≈t⨟p M⊒M′) eq
no-const-const-gen () isL′ (cast-⊒ pᶜ r≈t⨟p M⊒M′) eq

no-const-runtime-bullet :
  ∀ {Δ σ γ L T p} →
  Isℕ0 L →
  Isℕ0Bullet T →
  Δ ∣ σ ∣ γ ⊢ L ⊒ T ∶ p →
  ⊥
no-const-runtime-bullet isL isT (extend qᶜ pαᶜ M⊒M′) =
  no-const-runtime-bullet isL isT M⊒M′
no-const-runtime-bullet isL isT (split qᶜ pαᶜ M⊒M′) =
  no-const-runtime-bullet (isℕ0-open-any isL) isT M⊒M′
no-const-runtime-bullet isL () (⊒blame pᶜ)
no-const-runtime-bullet () isT (x⊒x pᶜ x∋p)
no-const-runtime-bullet () isT (ƛ⊒ƛ p↦qᶜ M⊒M′)
no-const-runtime-bullet () isT (·⊒· qᶜ L⊒L′ M⊒M′)
no-const-runtime-bullet () isT (Λ⊒Λ allᶜ vV V⊒V′)
no-const-runtime-bullet isL () (⊒Λ pᶜ M⊒V′)
no-const-runtime-bullet isL () (⊒⟨ν⟩ pᶜ i M⊒V′s)
no-const-runtime-bullet () isT (α⊒α qᶜ pαᶜ L⊒L′)
no-const-runtime-bullet isL isT (⊒α pαᶜ L⊒L′) =
  no-const-const-gen
    (isℕ0-⇑ᵗᵐ-inv isL)
    (isℕ0-⇑ᵗᵐ-inv (isℕ0-bullet-inner isT))
    L⊒L′
    refl
no-const-runtime-bullet () isT (ν⊒ν pᶜ qᶜ M⊒M′)
no-const-runtime-bullet isL () (⊒ν pᶜ M⊒M′)
no-const-runtime-bullet () isT (ν⊒ pᶜ M⊒M′)
no-const-runtime-bullet isL () (κ⊒κ κ)
no-const-runtime-bullet () isT (⊕⊒⊕ M⊒M′ N⊒N′)
no-const-runtime-bullet isL () (⊒cast+ qᶜ q⨟s≈r M⊒M′)
no-const-runtime-bullet isL () (⊒cast- qᶜ q⨟s≈r M⊒M′)
no-const-runtime-bullet () isT (cast+⊒ pᶜ r≈t⨟p M⊒M′)
no-const-runtime-bullet () isT (cast-⊒ pᶜ r≈t⨟p M⊒M′)

no-const-runtime-bullet-id-cast :
  ∀ {Δ σ γ L T p} →
  Isℕ0 L →
  Isℕ0BulletIdCast T →
  Δ ∣ σ ∣ γ ⊢ L ⊒ T ∶ p →
  ⊥
no-const-runtime-bullet-id-cast isL isT (extend qᶜ pαᶜ M⊒M′) =
  no-const-runtime-bullet-id-cast isL isT M⊒M′
no-const-runtime-bullet-id-cast isL isT (split qᶜ pαᶜ M⊒M′) =
  no-const-runtime-bullet-id-cast (isℕ0-open-any isL) isT M⊒M′
no-const-runtime-bullet-id-cast isL () (⊒blame pᶜ)
no-const-runtime-bullet-id-cast () isT (x⊒x pᶜ x∋p)
no-const-runtime-bullet-id-cast () isT (ƛ⊒ƛ p↦qᶜ M⊒M′)
no-const-runtime-bullet-id-cast () isT (·⊒· qᶜ L⊒L′ M⊒M′)
no-const-runtime-bullet-id-cast () isT (Λ⊒Λ allᶜ vV V⊒V′)
no-const-runtime-bullet-id-cast isL () (⊒Λ pᶜ M⊒V′)
no-const-runtime-bullet-id-cast isL () (⊒⟨ν⟩ pᶜ i M⊒V′s)
no-const-runtime-bullet-id-cast () isT (α⊒α qᶜ pαᶜ L⊒L′)
no-const-runtime-bullet-id-cast isL () (⊒α pαᶜ L⊒L′)
no-const-runtime-bullet-id-cast () isT (ν⊒ν pᶜ qᶜ M⊒M′)
no-const-runtime-bullet-id-cast isL () (⊒ν pᶜ M⊒M′)
no-const-runtime-bullet-id-cast () isT (ν⊒ pᶜ M⊒M′)
no-const-runtime-bullet-id-cast isL () (κ⊒κ κ)
no-const-runtime-bullet-id-cast () isT (⊕⊒⊕ M⊒M′ N⊒N′)
no-const-runtime-bullet-id-cast isL isT (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  no-const-runtime-bullet
    isL
    (isℕ0-bullet-id-cast-inner isT)
    M⊒M′
no-const-runtime-bullet-id-cast isL isT (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  no-const-runtime-bullet
    isL
    (isℕ0-bullet-id-cast-inner isT)
    M⊒M′
no-const-runtime-bullet-id-cast () isT (cast+⊒ pᶜ r≈t⨟p M⊒M′)
no-const-runtime-bullet-id-cast () isT (cast-⊒ pᶜ r≈t⨟p M⊒M′)

DynamicGradualGuaranteeStatement : Set₁
DynamicGradualGuaranteeStatement =
  ∀ {Δ σ M M′ N′ p χ′} →
  RuntimeOK M →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p →
  M′ —→[ χ′ ] N′ →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ p′ ]
    (M —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore χ′ []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N ⊒ N′ ∶ p′

dynamicGradualGuarantee-counterexample :
  DynamicGradualGuaranteeStatement →
  ⊥
dynamicGradualGuarantee-counterexample dgg
    with dgg (ok-no no•-$) right-ν-example right-ν-step-example
dynamicGradualGuarantee-counterexample dgg
    | [] , .ℕ0 , Δ′ , Π , Π′ , π , p′ ,
      ↠-refl , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  no-const-runtime-bullet-id-cast
    isℕ0
    isℕ0-bullet-id-cast
    N⊒N′
dynamicGradualGuarantee-counterexample dgg
    | χ ∷ χs , N , Δ′ , Π , Π′ , π , p′ ,
      ↠-step red reds , Π≡ , Π′≡ , π⊒ , N⊒N′ =
  ⊥-elim (value-no-step ($ (κℕ 0)) red)
