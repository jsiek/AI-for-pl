module proof.NarrowWidenDeterminism where

-- File Charter:
--   * Proves that mode-indexed narrowing and widening are determined by
--     their endpoints and a recursively well-formed type store.
--   * Supplies the tag and variable-chain uniqueness lemmas needed by the
--     main mutual proof.

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; suc; zero)
open import Data.Nat.Properties using (<-irrefl; <-trans)
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; subst; sym; trans)

open import Types
open import TyStore
open import Coercions
open import NarrowWiden
open import proof.TyStore using
  (older; unique; StoreWf-⟰ᵗ; StoreWf-bind)
open import proof.TypeInTypeSubst using (rename-preserves-tagged)
open import proof.TypeInTypeSubst using
  ( predᵗ
  ; RenameLeftInverse-suc
  ; renameᵗ-left-inverse
  )
open import proof.ImprecisionComposition using
  (inst-variable-source-no-zero; shifted-variable-target-no-zero)
open import proof.NarrowWidenBinderGap using
  (narrowing-all-gen-overlap⊥; widening-all-inst-overlap⊥)

------------------------------------------------------------------------
-- Small syntactic and mode exclusions
------------------------------------------------------------------------

tag-seal-modes-exclusive : ∀ {μ X}
  → tagAllowed μ (＇ X) ≡ true
  → sealModeAllowed (μ X) ≡ true
  → ⊥
tag-seal-modes-exclusive {μ} {X} tag-ok seal-ok with μ X
tag-seal-modes-exclusive tag-ok () | id-only
tag-seal-modes-exclusive tag-ok () | tag-or-id
tag-seal-modes-exclusive () seal-ok | seal-or-id

tagged-tag-unique : ∀ {G H A}
  → G ꞉ A
  → H ꞉ A
  → G ≡ H
tagged-tag-unique (tag-var X) (tag-var .X) = refl
tagged-tag-unique (tag-base ι) (tag-base .ι) = refl
tagged-tag-unique tag-fun tag-fun = refl

⇑ᵗ-injective : ∀ {A B}
  → ⇑ᵗ A ≡ ⇑ᵗ B
  → A ≡ B
⇑ᵗ-injective {A} {B} eq =
  trans (sym (renameᵗ-left-inverse RenameLeftInverse-suc A))
    (trans (cong (renameᵗ predᵗ) eq)
      (renameᵗ-left-inverse RenameLeftInverse-suc B))

narrowing-target-star : ∀ {μ Δ Σ c A}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ ★
  → A ≡ ★
narrowing-target-star (idᵃ ★ hA) = refl
narrowing-target-star
    (untag-seq G hG allowed G꞉A p nonvar★ A≢★) = refl

widening-source-star : ∀ {μ Δ Σ c B}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ★ ⊑ B
  → B ≡ ★
widening-source-star (idᵃ ★ hA) = refl
widening-source-star
    (tag-seq G p hG allowed G꞉B nonvar★ ★≢B) = refl

tagged-narrowing-endpoints-equal : ∀ {μ Δ Σ G H c A B}
  → G ꞉ A
  → H ꞉ B
  → NonVar B
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
  → A ≡ B
tagged-narrowing-endpoints-equal (tag-base ι) (tag-base .ι)
    nonvar-base (idᵃ (‵ .ι) hA) = refl
tagged-narrowing-endpoints-equal tag-fun tag-fun nonvar-fun
    (p ↦ q) = refl

tagged-widening-endpoints-equal : ∀ {μ Δ Σ G H c A B}
  → G ꞉ A
  → H ꞉ B
  → NonVar A
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
  → A ≡ B
tagged-widening-endpoints-equal (tag-base ι) (tag-base .ι)
    nonvar-base (idᵃ (‵ .ι) hA) = refl
tagged-widening-endpoints-equal tag-fun tag-fun nonvar-fun
    (p ↦ q) = refl

------------------------------------------------------------------------
-- Variable chains follow the recursive store order
------------------------------------------------------------------------

narrowing-variable-target : ∀ {μ Δ Σ X A c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊒ A
  → Σ[ Y ∈ TyVar ] A ≡ ＇ Y
narrowing-variable-target (idᵃ (＇ X) hX) = X , refl
narrowing-variable-target
    (seal {X = Y} Y<Δ hA Y,A∈Σ allowed) = Y , refl
narrowing-variable-target
    (seal-seq {X = Y} p Y<Δ Y,A∈Σ allowed A≢B) = Y , refl
narrowing-variable-target
    (gen nonvarA zero∈A hX p X≢★) =
  ⊥-elim (shifted-variable-target-no-zero p zero∈A)

widening-variable-source : ∀ {μ Δ Σ A Y c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ ＇ Y
  → Σ[ X ∈ TyVar ] A ≡ ＇ X
widening-variable-source (idᵃ (＇ Y) hY) = Y , refl
widening-variable-source
    (unseal {X = X} X<Δ hA X,A∈Σ allowed) = X , refl
widening-variable-source
    (unseal-seq {X = X} X<Δ X,A∈Σ allowed p A≢B) = X , refl
widening-variable-source
    (inst nonvarA zero∈A hY p Y≢★) =
  ⊥-elim (inst-variable-source-no-zero p zero∈A)

narrowing-variable-order : ∀ {μ Δ Σ X Y c}
  → StoreWf Δ Σ
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊒ ＇ Y
  → X ≡ Y ⊎ Y < X
narrowing-variable-order wfΣ (idᵃ (＇ X) hX) = inj₁ refl
narrowing-variable-order wfΣ
    (seal {X = Y} Y<Δ hX Y,X∈Σ allowed) =
  inj₂ (older wfΣ Y,X∈Σ var-∈)
narrowing-variable-order wfΣ
    (seal-seq {X = Y} p Y<Δ Y,A∈Σ allowed X≢A)
    with narrowing-variable-target p
narrowing-variable-order wfΣ
    (seal-seq {X = Y} p Y<Δ Y,A∈Σ allowed X≢A)
    | z , refl with narrowing-variable-order wfΣ p
narrowing-variable-order wfΣ
    (seal-seq {X = Y} p Y<Δ Y,A∈Σ allowed X≢A)
    | z , refl | inj₁ refl =
  inj₂ (older wfΣ Y,A∈Σ var-∈)
narrowing-variable-order wfΣ
    (seal-seq {X = Y} p Y<Δ Y,A∈Σ allowed X≢A)
    | z , refl | inj₂ z<X =
  inj₂ (<-trans (older wfΣ Y,A∈Σ var-∈) z<X)

widening-variable-order : ∀ {μ Δ Σ X Y c}
  → StoreWf Δ Σ
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊑ ＇ Y
  → X ≡ Y ⊎ X < Y
widening-variable-order wfΣ (idᵃ (＇ X) hX) = inj₁ refl
widening-variable-order wfΣ
    (unseal {X = X} X<Δ hY X,Y∈Σ allowed) =
  inj₂ (older wfΣ X,Y∈Σ var-∈)
widening-variable-order wfΣ
    (unseal-seq {X = X} X<Δ X,A∈Σ allowed p A≢Y)
    with widening-variable-source p
widening-variable-order wfΣ
    (unseal-seq {X = X} X<Δ X,A∈Σ allowed p A≢Y)
    | z , refl with widening-variable-order wfΣ p
widening-variable-order wfΣ
    (unseal-seq {X = X} X<Δ X,A∈Σ allowed p A≢Y)
    | z , refl | inj₁ refl =
  inj₂ (older wfΣ X,A∈Σ var-∈)
widening-variable-order wfΣ
    (unseal-seq {X = X} X<Δ X,A∈Σ allowed p A≢Y)
    | z , refl | inj₂ z<Y =
  inj₂ (<-trans (older wfΣ X,A∈Σ var-∈) z<Y)

narrowing-self-seal-seq⊥ : ∀ {μ Δ Σ X A c}
  → StoreWf Δ Σ
  → (X , A) ∈ Σ
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊒ A
  → ⊥
narrowing-self-seal-seq⊥ wfΣ X,A∈Σ p
    with narrowing-variable-target p
narrowing-self-seal-seq⊥ wfΣ X,A∈Σ p | y , refl
    with older wfΣ X,A∈Σ var-∈ | narrowing-variable-order wfΣ p
narrowing-self-seal-seq⊥ wfΣ X,A∈Σ p
    | y , refl | X<Y | inj₁ refl =
  <-irrefl refl X<Y
narrowing-self-seal-seq⊥ wfΣ X,A∈Σ p
    | y , refl | X<Y | inj₂ Y<X =
  <-irrefl refl (<-trans X<Y Y<X)

widening-self-unseal-seq⊥ : ∀ {μ Δ Σ X A c}
  → StoreWf Δ Σ
  → (X , A) ∈ Σ
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ ＇ X
  → ⊥
widening-self-unseal-seq⊥ wfΣ X,A∈Σ p
    with widening-variable-source p
widening-self-unseal-seq⊥ wfΣ X,A∈Σ p | y , refl
    with older wfΣ X,A∈Σ var-∈ | widening-variable-order wfΣ p
widening-self-unseal-seq⊥ wfΣ X,A∈Σ p
    | y , refl | X<Y | inj₁ refl =
  <-irrefl refl X<Y
widening-self-unseal-seq⊥ wfΣ X,A∈Σ p
    | y , refl | X<Y | inj₂ Y<X =
  <-irrefl refl (<-trans X<Y Y<X)

------------------------------------------------------------------------
-- Determinism
------------------------------------------------------------------------

mutual

  narrowing-determinedᵐ : ∀ {μ Δ Σ c d A B}
    → StoreWf Δ Σ
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → μ ∣ Δ ∣ Σ ⊢ d ⦂ A ⊒ B
    → c ≡ d
  narrowing-determinedᵐ wfΣ (idᵃ a hA) (idᵃ b hB) = refl
  narrowing-determinedᵐ wfΣ (p ↦ q) (p′ ↦ q′) =
    cong₂ _↦_ (widening-determinedᵐ wfΣ p p′)
      (narrowing-determinedᵐ wfΣ q q′)
  narrowing-determinedᵐ wfΣ (∀ⁿ p) (∀ⁿ q) =
    cong `∀ (narrowing-determinedᵐ (StoreWf-⟰ᵗ wfΣ) p q)
  narrowing-determinedᵐ wfΣ (∀ⁿ p)
      (gen nonvarB zero∈B hA q A≢★) =
    ⊥-elim (narrowing-all-gen-overlap⊥ wfΣ zero∈B p q)
  narrowing-determinedᵐ wfΣ
      (gen nonvarB zero∈B hA p A≢★) (∀ⁿ q) =
    ⊥-elim (narrowing-all-gen-overlap⊥ wfΣ zero∈B q p)
  narrowing-determinedᵐ wfΣ (∀ⁿ p) (idᵃ () hA)
  narrowing-determinedᵐ wfΣ
      (untag G hG G-ok G꞉B) (untag H hH H-ok H꞉B) =
    cong _？ (tagged-tag-unique G꞉B H꞉B)
  narrowing-determinedᵐ wfΣ
      (untag G hG G-ok G꞉B)
      (untag-seq H hH H-ok H꞉A q nonvarB A≢B) =
    ⊥-elim (A≢B
      (tagged-narrowing-endpoints-equal H꞉A G꞉B nonvarB q))
  narrowing-determinedᵐ wfΣ
      (untag-seq G hG G-ok G꞉A p nonvarB A≢B)
      (untag H hH H-ok H꞉B) =
    ⊥-elim (A≢B
      (tagged-narrowing-endpoints-equal G꞉A H꞉B nonvarB p))
  narrowing-determinedᵐ wfΣ
      (untag-seq G hG G-ok G꞉A p nonvarB A≢B)
      (untag-seq H hH H-ok H꞉C q nonvarB′ C≢B)
      with narrowing-tag-source-determined wfΣ
        G꞉A H꞉C nonvarB p q
  narrowing-determinedᵐ wfΣ
      (untag-seq G hG G-ok G꞉A p nonvarB A≢B)
      (untag-seq H hH H-ok H꞉C q nonvarB′ C≢B)
      | refl , eq =
    cong₂ _︔_ (cong _？ (tagged-tag-unique G꞉A H꞉C)) eq
  narrowing-determinedᵐ wfΣ
      (untag-seq G hG G-ok G꞉A p nonvarB A≢B)
      (gen nonvarC zero∈C h★ q ★≢★) =
    ⊥-elim (★≢★ refl)
  narrowing-determinedᵐ {μ = μ} wfΣ
      (untag (＇ X) hG tag-ok (tag-var .X))
      (seal X<Δ h★ X,★∈Σ seal-ok) =
    ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
      tag-ok seal-ok)
  narrowing-determinedᵐ {μ = μ} wfΣ
      (untag (＇ X) hG tag-ok (tag-var .X))
      (seal-seq p X<Δ X,A∈Σ seal-ok ★≢A) =
    ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
      tag-ok seal-ok)
  narrowing-determinedᵐ {μ = μ} wfΣ
      (seal X<Δ h★ X,★∈Σ seal-ok)
      (untag (＇ X) hG tag-ok (tag-var .X)) =
    ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
      tag-ok seal-ok)
  narrowing-determinedᵐ {μ = μ} wfΣ
      (seal-seq p X<Δ X,A∈Σ seal-ok ★≢A)
      (untag (＇ X) hG tag-ok (tag-var .X)) =
    ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
      tag-ok seal-ok)
  narrowing-determinedᵐ wfΣ
      (seal X<Δ hA X,A∈Σ allowed)
      (seal X<Δ′ hA′ X,A∈Σ′ allowed′) = refl
  narrowing-determinedᵐ wfΣ
      (seal X<Δ hA X,A∈Σ allowed)
      (seal-seq q X<Δ′ X,B∈Σ allowed′ A≢B)
      with unique wfΣ X,A∈Σ X,B∈Σ
  narrowing-determinedᵐ wfΣ
      (seal X<Δ hA X,A∈Σ allowed)
      (seal-seq q X<Δ′ X,B∈Σ allowed′ A≢B) | refl =
    ⊥-elim (A≢B refl)
  narrowing-determinedᵐ wfΣ
      (seal-seq p X<Δ X,B∈Σ allowed A≢B)
      (seal X<Δ′ hA X,A∈Σ allowed′)
      with unique wfΣ X,B∈Σ X,A∈Σ
  narrowing-determinedᵐ wfΣ
      (seal-seq p X<Δ X,B∈Σ allowed A≢B)
      (seal X<Δ′ hA X,A∈Σ allowed′) | refl =
    ⊥-elim (A≢B refl)
  narrowing-determinedᵐ wfΣ
      (seal-seq {X = X} p X<Δ X,B∈Σ allowed A≢B)
      (seal-seq q X<Δ′ X,C∈Σ allowed′ A≢C)
      with unique wfΣ X,B∈Σ X,C∈Σ
  narrowing-determinedᵐ wfΣ
      (seal-seq {X = X} p X<Δ X,B∈Σ allowed A≢B)
      (seal-seq q X<Δ′ X,C∈Σ allowed′ A≢C) | refl =
    cong (λ c → c ︔ seal X) (narrowing-determinedᵐ wfΣ p q)
  narrowing-determinedᵐ wfΣ (idᵃ (＇ X) hX)
      (seal X<Δ hX′ X,X∈Σ allowed) =
    ⊥-elim (<-irrefl refl (older wfΣ X,X∈Σ var-∈))
  narrowing-determinedᵐ wfΣ
      (seal X<Δ hX X,X∈Σ allowed) (idᵃ (＇ X) hX′) =
    ⊥-elim (<-irrefl refl (older wfΣ X,X∈Σ var-∈))
  narrowing-determinedᵐ wfΣ (idᵃ (＇ X) hX)
      (seal-seq p X<Δ X,A∈Σ allowed X≢A) =
    ⊥-elim (narrowing-self-seal-seq⊥ wfΣ X,A∈Σ p)
  narrowing-determinedᵐ wfΣ
      (seal-seq p X<Δ X,A∈Σ allowed X≢A) (idᵃ (＇ X) hX) =
    ⊥-elim (narrowing-self-seal-seq⊥ wfΣ X,A∈Σ p)
  narrowing-determinedᵐ wfΣ (idᵃ ★ h★)
      (untag-seq G hG allowed G꞉A p nonvar★ A≢★) =
    ⊥-elim (A≢★ (narrowing-target-star p))
  narrowing-determinedᵐ wfΣ
      (untag-seq G hG allowed G꞉A p nonvar★ A≢★)
      (idᵃ ★ h★) =
    ⊥-elim (A≢★ (narrowing-target-star p))
  narrowing-determinedᵐ wfΣ
      (gen nonvarA zero∈A hB p B≢★)
      (gen nonvarA′ zero∈A′ hB′ q B≢★′) =
    cong gen (narrowing-determinedᵐ (StoreWf-⟰ᵗ wfΣ) p q)
  narrowing-determinedᵐ wfΣ
      (gen nonvarA zero∈A hB p B≢★) (idᵃ () hC)
  narrowing-determinedᵐ wfΣ
      (gen nonvarA zero∈A h★ p ★≢★)
      (untag-seq G hG allowed G꞉B q nonvarC B≢C) =
    ⊥-elim (★≢★ refl)
  narrowing-determinedᵐ wfΣ
      (gen nonvarA zero∈A hB p B≢★)
      (untag G hG allowed ())

  widening-determinedᵐ : ∀ {μ Δ Σ c d A B}
    → StoreWf Δ Σ
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → μ ∣ Δ ∣ Σ ⊢ d ⦂ A ⊑ B
    → c ≡ d
  widening-determinedᵐ wfΣ (idᵃ a hA) (idᵃ b hB) = refl
  widening-determinedᵐ wfΣ (p ↦ q) (p′ ↦ q′) =
    cong₂ _↦_ (narrowing-determinedᵐ wfΣ p p′)
      (widening-determinedᵐ wfΣ q q′)
  widening-determinedᵐ wfΣ (∀ʷ p) (∀ʷ q) =
    cong `∀ (widening-determinedᵐ (StoreWf-⟰ᵗ wfΣ) p q)
  widening-determinedᵐ wfΣ (∀ʷ p)
      (inst nonvarA zero∈A hB q B≢★) =
    ⊥-elim (widening-all-inst-overlap⊥ wfΣ zero∈A p q)
  widening-determinedᵐ wfΣ
      (inst nonvarA zero∈A hB p B≢★) (∀ʷ q) =
    ⊥-elim (widening-all-inst-overlap⊥ wfΣ zero∈A q p)
  widening-determinedᵐ wfΣ (∀ʷ p) (idᵃ () hA)
  widening-determinedᵐ wfΣ
      (tag G hG G-ok G꞉A) (tag H hH H-ok H꞉A) =
    cong _! (tagged-tag-unique G꞉A H꞉A)
  widening-determinedᵐ wfΣ
      (tag G hG G-ok G꞉A)
      (tag-seq H q hH H-ok H꞉B nonvarA A≢B) =
    ⊥-elim (A≢B
      (tagged-widening-endpoints-equal G꞉A H꞉B nonvarA q))
  widening-determinedᵐ wfΣ
      (tag-seq G p hG G-ok G꞉B nonvarA A≢B)
      (tag H hH H-ok H꞉A) =
    ⊥-elim (A≢B
      (tagged-widening-endpoints-equal H꞉A G꞉B nonvarA p))
  widening-determinedᵐ wfΣ
      (tag-seq G p hG G-ok G꞉B nonvarA A≢B)
      (tag-seq H q hH H-ok H꞉C nonvarA′ A≢C)
      with widening-tag-target-determined wfΣ
        G꞉B H꞉C nonvarA p q
  widening-determinedᵐ wfΣ
      (tag-seq G p hG G-ok G꞉B nonvarA A≢B)
      (tag-seq H q hH H-ok H꞉C nonvarA′ A≢C)
      | refl , eq =
    cong₂ _︔_ eq (cong _! (tagged-tag-unique G꞉B H꞉C))
  widening-determinedᵐ wfΣ
      (tag-seq G p hG G-ok G꞉B nonvarA A≢B)
      (inst nonvarC zero∈C h★ q ★≢★) =
    ⊥-elim (★≢★ refl)
  widening-determinedᵐ {μ = μ} wfΣ
      (tag (＇ X) hG tag-ok (tag-var .X))
      (unseal X<Δ h★ X,★∈Σ seal-ok) =
    ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
      tag-ok seal-ok)
  widening-determinedᵐ {μ = μ} wfΣ
      (tag (＇ X) hG tag-ok (tag-var .X))
      (unseal-seq X<Δ X,A∈Σ seal-ok p A≢★) =
    ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
      tag-ok seal-ok)
  widening-determinedᵐ {μ = μ} wfΣ
      (unseal X<Δ h★ X,★∈Σ seal-ok)
      (tag (＇ X) hG tag-ok (tag-var .X)) =
    ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
      tag-ok seal-ok)
  widening-determinedᵐ {μ = μ} wfΣ
      (unseal-seq X<Δ X,A∈Σ seal-ok p A≢★)
      (tag (＇ X) hG tag-ok (tag-var .X)) =
    ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
      tag-ok seal-ok)
  widening-determinedᵐ wfΣ
      (unseal X<Δ hA X,A∈Σ allowed)
      (unseal X<Δ′ hA′ X,A∈Σ′ allowed′) = refl
  widening-determinedᵐ wfΣ
      (unseal X<Δ hA X,A∈Σ allowed)
      (unseal-seq X<Δ′ X,B∈Σ allowed′ q B≢A)
      with unique wfΣ X,A∈Σ X,B∈Σ
  widening-determinedᵐ wfΣ
      (unseal X<Δ hA X,A∈Σ allowed)
      (unseal-seq X<Δ′ X,B∈Σ allowed′ q B≢A) | refl =
    ⊥-elim (B≢A refl)
  widening-determinedᵐ wfΣ
      (unseal-seq X<Δ X,B∈Σ allowed p B≢A)
      (unseal X<Δ′ hA X,A∈Σ allowed′)
      with unique wfΣ X,B∈Σ X,A∈Σ
  widening-determinedᵐ wfΣ
      (unseal-seq X<Δ X,B∈Σ allowed p B≢A)
      (unseal X<Δ′ hA X,A∈Σ allowed′) | refl =
    ⊥-elim (B≢A refl)
  widening-determinedᵐ wfΣ
      (unseal-seq {X = X} X<Δ X,B∈Σ allowed p B≢A)
      (unseal-seq X<Δ′ X,C∈Σ allowed′ q C≢A)
      with unique wfΣ X,B∈Σ X,C∈Σ
  widening-determinedᵐ wfΣ
      (unseal-seq {X = X} X<Δ X,B∈Σ allowed p B≢A)
      (unseal-seq X<Δ′ X,C∈Σ allowed′ q C≢A) | refl =
    cong (unseal X ︔_) (widening-determinedᵐ wfΣ p q)
  widening-determinedᵐ wfΣ (idᵃ (＇ X) hX)
      (unseal X<Δ hX′ X,X∈Σ allowed) =
    ⊥-elim (<-irrefl refl (older wfΣ X,X∈Σ var-∈))
  widening-determinedᵐ wfΣ
      (unseal X<Δ hX X,X∈Σ allowed) (idᵃ (＇ X) hX′) =
    ⊥-elim (<-irrefl refl (older wfΣ X,X∈Σ var-∈))
  widening-determinedᵐ wfΣ (idᵃ (＇ X) hX)
      (unseal-seq X<Δ X,A∈Σ allowed p A≢X) =
    ⊥-elim (widening-self-unseal-seq⊥ wfΣ X,A∈Σ p)
  widening-determinedᵐ wfΣ
      (unseal-seq X<Δ X,A∈Σ allowed p A≢X) (idᵃ (＇ X) hX) =
    ⊥-elim (widening-self-unseal-seq⊥ wfΣ X,A∈Σ p)
  widening-determinedᵐ wfΣ (idᵃ ★ h★)
      (tag-seq G p hG allowed G꞉B nonvar★ ★≢B) =
    ⊥-elim (★≢B (sym (widening-source-star p)))
  widening-determinedᵐ wfΣ
      (tag-seq G p hG allowed G꞉B nonvar★ ★≢B)
      (idᵃ ★ h★) =
    ⊥-elim (★≢B (sym (widening-source-star p)))
  widening-determinedᵐ wfΣ
      (inst nonvarA zero∈A hB p B≢★)
      (inst nonvarA′ zero∈A′ hB′ q B≢★′) =
    cong inst (widening-determinedᵐ (StoreWf-bind wfΣ wf★) p q)
  widening-determinedᵐ wfΣ
      (inst nonvarA zero∈A hB p B≢★) (idᵃ () hC)
  widening-determinedᵐ wfΣ
      (inst nonvarA zero∈A h★ p ★≢★)
      (tag-seq G q hG allowed G꞉B nonvarC C≢B) =
    ⊥-elim (★≢★ refl)
  widening-determinedᵐ wfΣ
      (inst nonvarA zero∈A hB p B≢★)
      (tag G hG allowed ())

  narrowing-tag-source-determined : ∀ {μ Δ Σ G H c d A C B}
    → StoreWf Δ Σ
    → G ꞉ A
    → H ꞉ C
    → NonVar B
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → μ ∣ Δ ∣ Σ ⊢ d ⦂ C ⊒ B
    → A ≡ C × c ≡ d
  narrowing-tag-source-determined wfΣ (tag-base ι) (tag-base .ι)
      nonvar-base (idᵃ (‵ .ι) hA) (idᵃ (‵ .ι) hA′) =
    refl , refl
  narrowing-tag-source-determined wfΣ tag-fun tag-fun nonvar-fun
      (p ↦ q) (p′ ↦ q′) =
    refl , cong₂ _↦_ (widening-determinedᵐ wfΣ p p′)
      (narrowing-determinedᵐ wfΣ q q′)
  narrowing-tag-source-determined wfΣ G꞉A H꞉C nonvar-all
      (gen nonvarB zero∈B hA p A≢★)
      (gen nonvarB′ zero∈B′ hC q C≢★) =
    let rec = narrowing-tag-source-determined (StoreWf-⟰ᵗ wfΣ)
          (rename-preserves-tagged suc G꞉A)
          (rename-preserves-tagged suc H꞉C) nonvarB p q
    in ⇑ᵗ-injective (proj₁ rec) , cong gen (proj₂ rec)

  widening-tag-target-determined : ∀ {μ Δ Σ G H c d A B C}
    → StoreWf Δ Σ
    → G ꞉ B
    → H ꞉ C
    → NonVar A
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → μ ∣ Δ ∣ Σ ⊢ d ⦂ A ⊑ C
    → B ≡ C × c ≡ d
  widening-tag-target-determined wfΣ (tag-base ι) (tag-base .ι)
      nonvar-base (idᵃ (‵ .ι) hA) (idᵃ (‵ .ι) hA′) =
    refl , refl
  widening-tag-target-determined wfΣ tag-fun tag-fun nonvar-fun
      (p ↦ q) (p′ ↦ q′) =
    refl , cong₂ _↦_ (narrowing-determinedᵐ wfΣ p p′)
      (widening-determinedᵐ wfΣ q q′)
  widening-tag-target-determined wfΣ G꞉B H꞉C nonvar-all
      (inst nonvarA zero∈A hB p B≢★)
      (inst nonvarA′ zero∈A′ hC q C≢★) =
    let rec = widening-tag-target-determined (StoreWf-bind wfΣ wf★)
          (rename-preserves-tagged suc G꞉B)
          (rename-preserves-tagged suc H꞉C) nonvarA p q
    in ⇑ᵗ-injective (proj₁ rec) , cong inst (proj₂ rec)

narrowing-determined : ∀ {μ Δ Σ A B}
  → StoreWf Δ Σ
  → (p q : μ ∣ Δ ∣ Σ ⊢ A ⊒ B)
  → p ≐ⁿ q
narrowing-determined wfΣ (c , p) (d , q) =
  narrowing-determinedᵐ wfΣ p q

widening-determined : ∀ {μ Δ Σ c d A B}
  → StoreWf Δ Σ
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
  → μ ∣ Δ ∣ Σ ⊢ d ⦂ A ⊑ B
  → c ≡ d
widening-determined = widening-determinedᵐ
