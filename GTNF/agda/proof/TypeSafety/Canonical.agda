module proof.TypeSafety.Canonical where

-- File Charter:
--   * Provides the canonical forms needed by GTNF progress.
--   * Function values are lambdas, function-cast values, or function
--     boundaries; polymorphic values provide an `InstX` result; dynamic
--     values are tagged values or fresh-name boundary tags.
--   * Extends the νF canonical-form argument with casts and `★`.

open import Data.Nat using (ℕ; zero)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Ctx
open import proof.Ctx
open import Conversion
open import Coercion
open import Terms
open import Boundary
open import Reduction using (InstX; inst-Λ; inst-gen; inst-∀; inst-⟪⟫)

private
  variable
    Δ Δ′ : Ctxᵗ
    η : TyCtx
    A B C R S : Ty
    X α : ℕ
    c : Conv

------------------------------------------------------------------------
-- Representation-reading inversions
------------------------------------------------------------------------

same-base-target : η ⊢ A ~ R → Base R → Base A
same-base-target same-ℕ base-ℕ = base-ℕ
same-base-target same-𝔹 base-𝔹 = base-𝔹

same-⇒-target : η ⊢ A ~ (R ⇒ S)
  → Σ[ B ∈ Ty ] Σ[ C ∈ Ty ] (A ≡ B ⇒ C)
same-⇒-target (same-⇒ p q) = _ , _ , refl

same-∀-target : η ⊢ A ~ `∀ R → Σ[ B ∈ Ty ] (A ≡ `∀ B)
same-∀-target (same-∀ p) = _ , refl

same-★-target : η ⊢ A ~ ★ → A ≡ ★
same-★-target same-★ = refl

≈-base-target : Base A → Δ ⊢ A ≈ B ⊣ Δ′ → Base B
≈-base-target base-ℕ (`ℕ , same-ℕ , q) = same-base-target q base-ℕ
≈-base-target base-𝔹 (`𝔹 , same-𝔹 , q) = same-base-target q base-𝔹

≈-⇒-target : Δ ⊢ (A ⇒ B) ≈ C ⊣ Δ′
  → Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ] (C ≡ A′ ⇒ B′)
≈-⇒-target (_ , same-⇒ p q , r) = same-⇒-target r

≈-∀-target : Δ ⊢ `∀ A ≈ B ⊣ Δ′
  → Σ[ A′ ∈ Ty ] (B ≡ `∀ A′)
≈-∀-target (_ , same-∀ p , q) = same-∀-target q

≈-★-target : Δ ⊢ ★ ≈ B ⊣ Δ′ → B ≡ ★
≈-★-target (_ , same-★ , q) = same-★-target q

≈-★-source : Δ ⊢ B ≈ ★ ⊣ Δ′ → B ≡ ★
≈-★-source (_ , p , same-★) = same-★-target p

≈-∀-source : Δ ⊢ B ≈ `∀ A ⊣ Δ′
  → Σ[ B′ ∈ Ty ] (B ≡ `∀ B′)
≈-∀-source (_ , p , same-∀ q) = same-∀-target p

≈-var-source : Δ ⊢ B ≈ ` X ⊣ Δ′
  → Σ[ Y ∈ ℕ ] (B ≡ ` Y)
≈-var-source (_ , same-var {α = α} d , q) with q
≈-var-source (_ , same-var {α = α} d , q) | same-var d′ = _ , refl

lookup-local-zero : (zero ∷ shiftReps η) ∋ˡ X := zero → X ≡ zero
lookup-local-zero here = refl
lookup-local-zero (there d) = ⊥-elim (fresh-not-lookup fresh-zero-shift d)

same-local-zero : (zero ∷ shiftReps η) ⊢ A ~ ` zero → A ≡ ` zero
same-local-zero (same-var d) with lookup-local-zero d
same-local-zero (same-var d) | refl = refl

≈-∀-fresh-source : Δ ⊢ B ≈ `∀ (` zero) ⊣ Δ′
  → B ≡ `∀ (` zero)
≈-∀-fresh-source (_ , same-∀ p , same-∀ q)
    with same-rep-unique q (same-var here)
≈-∀-fresh-source (_ , same-∀ p , same-∀ q) | refl
    rewrite same-local-zero p = refl

≈-∀-fresh-target : Δ ⊢ `∀ (` zero) ≈ B ⊣ Δ′
  → B ≡ `∀ (` zero)
≈-∀-fresh-target (_ , same-∀ p , same-∀ q)
    with same-rep-unique p (same-var here)
≈-∀-fresh-target (_ , same-∀ p , same-∀ q) | refl
    rewrite same-local-zero q = refl

conv-tgt≡ : ∀ {B′} → B ≡ B′
  → Δ ⊢ c ∶ A ⇝ B → Δ ⊢ c ∶ A ⇝ B′
conv-tgt≡ refl ⊢c = ⊢c

------------------------------------------------------------------------
-- Inert conversion tails by target head
------------------------------------------------------------------------

inert-¬base : ∀ {t} → InertTail t → Δ ⊢ tail t ∶ A ⇝ B → ¬ Base B
inert-¬base I-idv (conv-tail (conv-mid (conv-id ())))
inert-¬base I-idv (conv-tail (conv-mid (conv-idv _))) ()
inert-¬base I-fun (conv-tail (conv-mid (conv-fun _ _))) ()
inert-¬base I-all (conv-tail (conv-mid (conv-all _))) ()
inert-¬base I-seal (conv-tail (conv-seal _)) ()
inert-¬base I-seal-seq (conv-tail (conv-seal-seq _ _ _)) ()

inert-¬★ : ∀ {t} → InertTail t → Δ ⊢ tail t ∶ A ⇝ ★ → ⊥
inert-¬★ I-idv (conv-tail p) with p
inert-¬★ I-idv (conv-tail p) | conv-mid ()
inert-¬★ I-fun (conv-tail p) with p
inert-¬★ I-fun (conv-tail p) | conv-mid ()
inert-¬★ I-all (conv-tail p) with p
inert-¬★ I-all (conv-tail p) | conv-mid ()
inert-¬★ I-seal (conv-tail ())
inert-¬★ I-seal-seq (conv-tail ())

inert-fun-conv : ∀ {t} → InertTail t → Δ ⊢ tail t ∶ A ⇝ (B ⇒ C)
  → Σ[ s ∈ Conv ] Σ[ u ∈ Conv ] (t ≡ mid (s ↦ u))
inert-fun-conv I-fun (conv-tail (conv-mid (conv-fun ⊢s ⊢t))) =
  _ , _ , refl

inert-all-conv : ∀ {t} → InertTail t → Δ ⊢ tail t ∶ A ⇝ `∀ B
  → Σ[ s ∈ Conv ] (t ≡ mid (`∀ s))
inert-all-conv I-all (conv-tail (conv-mid (conv-all ⊢s))) = _ , refl

------------------------------------------------------------------------
-- Canonical views
------------------------------------------------------------------------

data FunView (V : Term) (A B : Ty) : Set where
  fun-ƛ : ∀ {N} → V ≡ ƛ A ∙ N → FunView V A B
  fun-boundary : ∀ {U Θ s t}
    → Simple U
    → V ≡ U ⟪ Θ , ⌞ s ↦ t ⌟ ⟫
    → FunView V A B
  fun-cast : ∀ {W μ p q}
    → Value W
    → V ≡ W ⟨ μ ∣ p ↦ᵖ q ⟩
    → FunView V A B

data StarView (V : Term) : Set where
  star-tag : ∀ {W μ G}
    → Value W
    → V ≡ W ⟨ μ ∣ G ! ⟩
    → StarView V
  star-fresh : ∀ {W μ Θ X}
    → Value W
    → Fresh Θ X
    → V ≡ (W ⟨ μ ∣ (` X) ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫
    → StarView V

simple-¬var : ∀ {Γ U} → Simple U → Δ ∣ Γ ⊢ U ⦂ ` X → ⊥
simple-¬var S-$ ()
simple-¬var S-true ()
simple-¬var S-false ()
simple-¬var S-ƛ ()
simple-¬var (S-Λ _) ()
simple-¬var (S-cast _ I-tag) (⊢cast _ () _)
simple-¬var (S-cast _ I-↦) (⊢cast _ () _)
simple-¬var (S-cast _ I-∀ᵖ) (⊢cast _ () _)
simple-¬var (S-cast _ I-gen) (⊢cast _ () _)

canonical-base : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ A → Base A
  → (Σ[ n ∈ ℕ ] (V ≡ $ n)) ⊎ (V ≡ `true) ⊎ (V ≡ `false)
canonical-base (V-simple S-$) ⊢$ b = inj₁ (_ , refl)
canonical-base (V-simple S-true) ⊢true base-𝔹 = inj₂ (inj₁ refl)
canonical-base (V-simple S-false) ⊢false base-𝔹 = inj₂ (inj₂ refl)
canonical-base (V-simple S-ƛ) (⊢ƛ _ _) ()
canonical-base (V-simple (S-Λ _)) (⊢Λ _ _) ()
canonical-base (V-simple (S-cast _ I-tag)) (⊢cast _ (⊢tag _) _) ()
canonical-base (V-simple (S-cast _ I-tag))
    (⊢cast _ (⊢tag-var _ _ _) _) ()
canonical-base (V-simple (S-cast _ I-↦)) (⊢cast _ (⊢fun _ _) _) ()
canonical-base (V-simple (S-cast _ I-∀ᵖ)) (⊢cast _ (⊢all _) _) ()
canonical-base (V-simple (S-cast _ I-gen))
    (⊢cast _ (⊢gen _ _ _ _ _ _) _) ()
canonical-base {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _) b =
  ⊥-elim (inert-¬base it ⊢c
    (≈-base-target {Δ = Δ} {Δ′ = Δᶜ} b sameₑ))
canonical-base (V-fresh _ _)
    (boundary _ _ (conv-tail (conv-mid conv-id★)) _
      (_ , same-ℕ , ()) _) base-ℕ
canonical-base (V-fresh _ _)
    (boundary _ _ (conv-tail (conv-mid conv-id★)) _
      (_ , same-𝔹 , ()) _) base-𝔹

canonical-⇒ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ (A ⇒ B)
  → FunView V A B
canonical-⇒ (V-simple S-$) ()
canonical-⇒ (V-simple S-true) ()
canonical-⇒ (V-simple S-false) ()
canonical-⇒ (V-simple S-ƛ) (⊢ƛ _ _) = fun-ƛ refl
canonical-⇒ (V-simple (S-Λ _)) ()
canonical-⇒ (V-simple (S-cast v I-tag)) (⊢cast _ () _)
canonical-⇒ (V-simple (S-cast v I-↦)) (⊢cast _ (⊢fun _ _) _) =
  fun-cast v refl
canonical-⇒ (V-simple (S-cast v I-∀ᵖ)) (⊢cast _ () _)
canonical-⇒ (V-simple (S-cast v I-gen)) (⊢cast _ () _)
canonical-⇒ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
    with ≈-⇒-target {Δ = Δ} {Δ′ = Δᶜ} sameₑ
canonical-⇒ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
    | A′ , B′ , eq with inert-fun-conv it (conv-tgt≡ eq ⊢c)
canonical-⇒ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
    | A′ , B′ , eq | s , t , refl = fun-boundary u refl
canonical-⇒ (V-fresh _ _)
    (boundary _ _ (conv-tail (conv-mid conv-id★)) _
      (_ , same-⇒ _ _ , ()) _)

canonical-∀ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ C
  → Σ[ N ∈ Term ] InstX V N
canonical-∀ (V-simple S-$) ()
canonical-∀ (V-simple S-true) ()
canonical-∀ (V-simple S-false) ()
canonical-∀ (V-simple S-ƛ) ()
canonical-∀ (V-simple (S-Λ vN)) (⊢Λ _ _) = _ , inst-Λ vN
canonical-∀ (V-simple (S-cast v I-tag)) (⊢cast _ () _)
canonical-∀ (V-simple (S-cast v I-↦)) (⊢cast _ () _)
canonical-∀ (V-simple (S-cast v I-∀ᵖ)) (⊢cast ⊢W (⊢all ⊢p) len)
    with canonical-∀ v ⊢W
canonical-∀ (V-simple (S-cast v I-∀ᵖ)) (⊢cast ⊢W (⊢all ⊢p) len)
    | N , inst = _ , inst-∀ v inst
canonical-∀ (V-simple (S-cast v I-gen)) (⊢cast ⊢W (⊢gen _ _ _ _ _ _) _) =
  _ , inst-gen v
canonical-∀ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} _ ⊢U ⊢c sameᵢ sameₑ _)
    with ≈-∀-target {Δ = Δ} {Δ′ = Δᶜ} sameₑ
canonical-∀ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} _ ⊢U ⊢c sameᵢ sameₑ _)
    | C′ , eq with inert-all-conv it (conv-tgt≡ eq ⊢c)
canonical-∀ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} _ ⊢U ⊢c sameᵢ sameₑ _)
    | C′ , eq | s , refl with conv-all-inv ⊢c
canonical-∀ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} _ ⊢U ⊢c sameᵢ sameₑ _)
    | C′ , eq | s , refl | A₀ , B₀ , refl , eqB , ⊢s
    with ≈-∀-source {Δ = Δᵢ} {Δ′ = Δᶜ} sameᵢ
canonical-∀ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} _ ⊢U ⊢c sameᵢ sameₑ _)
    | C′ , eq | s , refl | A₀ , B₀ , refl , eqB , ⊢s | D , refl
    with canonical-∀ (V-simple u) ⊢U
canonical-∀ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} _ ⊢U ⊢c sameᵢ sameₑ _)
    | C′ , eq | s , refl | A₀ , B₀ , refl , eqB , ⊢s | D , refl
    | N , inst = _ , inst-⟪⟫ u inst
canonical-∀ (V-fresh _ _)
    (boundary _ _ (conv-tail (conv-mid conv-id★)) _
      (_ , same-∀ _ , ()) _)

canonical-★ : ∀ {V} → Value V → Δ ∣ [] ⊢ V ⦂ ★ → StarView V
canonical-★ (V-simple S-$) ()
canonical-★ (V-simple S-true) ()
canonical-★ (V-simple S-false) ()
canonical-★ (V-simple S-ƛ) ()
canonical-★ (V-simple (S-Λ _)) ()
canonical-★ (V-simple (S-cast v I-tag)) (⊢cast _ (⊢tag _) _) =
  star-tag v refl
canonical-★ (V-simple (S-cast v I-tag)) (⊢cast _ (⊢tag-var _ _ _) _) =
  star-tag v refl
canonical-★ (V-simple (S-cast v I-↦)) (⊢cast _ () _)
canonical-★ (V-simple (S-cast v I-∀ᵖ)) (⊢cast _ () _)
canonical-★ (V-simple (S-cast v I-gen)) (⊢cast _ () _)
canonical-★ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _)
    with ≈-★-target {Δ = Δ} {Δ′ = Δᶜ} sameₑ
canonical-★ {Δ = Δ} (V-⟪⟫ u it)
    (boundary {Δᶜ = Δᶜ} _ _ ⊢c _ sameₑ _) | refl =
  ⊥-elim (inert-¬★ it ⊢c)
canonical-★ (V-fresh v fresh) (boundary _ _ _ _ _ _) =
  star-fresh v fresh refl
