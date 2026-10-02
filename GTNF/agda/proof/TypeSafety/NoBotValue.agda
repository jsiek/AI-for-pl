module proof.TypeSafety.NoBotValue where

-- File Charter:
--   * Proves that no GTNF value has type `∀X. X`.
--   * The proof uses strict coercion modes, the absence of a representation
--     for a freshly abstract rep. var, and canonical boundary inversions.
--   * This is the progress argument for a value under `bot-elim`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)

open import Types
open import Ctx
open import proof.Ctx
open import Conversion
open import Coercion
open import Boundary
open import Terms
open import proof.TypeSafety.Canonical

private
  variable
    Δ Δᵢ Δᶜ : Ctxᵗ
    Ξ : RepCtx
    Γ : Ctx
    μ : ModeEnv
    A B : Ty
    X : ℕ

------------------------------------------------------------------------
-- A strict mode pins a coercion endpoint to the same variable
------------------------------------------------------------------------

zero-not-in-suc-var : zero ∈ᵗ ` suc X → ⊥
zero-not-in-suc-var ()

coercion-to-strict : ∀ {Δ μ p A X}
  → μ ∋ˡ X := X∼X
  → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ ` X
  → A ≡ ` X
coercion-to-strict strict (⊢id wA) = refl
coercion-to-strict strict (⊢check-var tv mode ok)
    with ∋ˡ-det mode strict
coercion-to-strict strict (⊢check-var tv mode ok) | refl with ok
coercion-to-strict strict (⊢check-var tv mode ok) | refl | ()
coercion-to-strict {X = X} strict
    (⊢inst ⊢p wB nvA z∈A nsB)
    with coercion-to-strict (there strict) ⊢p
coercion-to-strict {X = X} strict
    (⊢inst ⊢p wB nvA z∈A nsB) | refl =
  ⊥-elim (zero-not-in-suc-var z∈A)
coercion-to-strict strict (⊢seq-check (cg-nv g) ⊢p ns)
    with coercion-to-strict strict ⊢p
coercion-to-strict strict (⊢seq-check (cg-nv g) ⊢p ns)
    | refl with g
coercion-to-strict strict (⊢seq-check (cg-nv g) ⊢p ns)
    | refl | ()
coercion-to-strict strict (⊢seq-check (cg-var tv mode ok) ⊢p ns)
    with coercion-to-strict strict ⊢p
coercion-to-strict strict (⊢seq-check (cg-var tv mode ok) ⊢p ns)
    | refl with ∋ˡ-det mode strict
coercion-to-strict strict (⊢seq-check (cg-var tv mode ok) ⊢p ns)
    | refl | refl with ok
coercion-to-strict strict (⊢seq-check (cg-var tv mode ok) ⊢p ns)
    | refl | refl | ()

coercion-to-fresh : ∀ {Δ μ p A}
  → underΛ Δ ∣ X∼X ∷ μ ⊢ᵖ p ∶ A ⟹ ` zero
  → A ≡ ` zero
coercion-to-fresh = coercion-to-strict here

------------------------------------------------------------------------
-- A fresh abstract rep. var has no representation
------------------------------------------------------------------------

fresh-not-shifted : (R : Ty) → renameᵗ suc R ≢ ` zero
fresh-not-shifted (` X) ()
fresh-not-shifted `ℕ ()
fresh-not-shifted `𝔹 ()
fresh-not-shifted ★ ()
fresh-not-shifted (A ⇒ B) ()
fresh-not-shifted (`∀ A) ()

bindR-injective : ∀ {A B} → bindR A ≡ bindR B → A ≡ B
bindR-injective refl = refl

no-fresh-rep-eq : ∀ {Ξ α b}
  → (abstR ∷ Ξ) ∋ʳ α := b
  → b ≡ bindR (` zero)
  → ⊥
no-fresh-rep-eq r-here ()
no-fresh-rep-eq (r-there-abst {b = abstR} d) ()
no-fresh-rep-eq (r-there-abst {b = bindR R} d) eq =
  fresh-not-shifted R (bindR-injective eq)

no-fresh-rep : ∀ {Ξ α}
  → (abstR ∷ Ξ) ∋ʳ α := bindR (` zero)
  → ⊥
no-fresh-rep d = no-fresh-rep-eq d refl

no-zero-rep : ∀ {Ξ R}
  → (abstR ∷ Ξ) ∋ʳ zero := bindR R
  → ⊥
no-zero-rep ()

no-fresh-name-square : underΛ Δ ∋ zero := A → ⊥
no-fresh-name-square (α , R , name , rep , same)
    with ∋ˡ-det name here
no-fresh-name-square (α , R , name , rep , same) | refl =
  no-zero-rep rep

no-fresh-square : underΛ Δ ∋ X := ` zero → ⊥
no-fresh-square (α , R , name , rep , same-var d)
    with ∋ˡ-det d here
no-fresh-square (α , R , name , rep , same-var d) | refl =
  no-fresh-rep rep

conversion-to-fresh : ∀ {Δ c A}
  → underΛ Δ ⊢ c ∶ A ⇝ ` zero
  → A ≡ ` zero
conversion-to-fresh (conv-tail (conv-mid (conv-idv tv))) = refl
conversion-to-fresh (conv-tail (conv-seal square)) =
  ⊥-elim (no-fresh-name-square square)
conversion-to-fresh (conv-tail (conv-seal-seq ⊢t square not-id)) =
  ⊥-elim (no-fresh-name-square square)
conversion-to-fresh (conv-unseal square) =
  ⊥-elim (no-fresh-square square)
conversion-to-fresh (conv-unseal-seq square ⊢c not-id no-cancel)
    with conversion-to-fresh ⊢c
conversion-to-fresh (conv-unseal-seq square ⊢c not-id no-cancel)
    | refl = ⊥-elim (no-fresh-square square)

------------------------------------------------------------------------
-- Fresh-variable values and bottom values
------------------------------------------------------------------------

fresh-seal-impossible : ∀ {Δ Θ Δᶜ Y A}
  → underΛ Δ ⊢ᶜ Θ ⇒ Δᶜ
  → underΛ Δ ⊢ ` zero ≈ ` Y ⊣ Δᶜ
  → Δᶜ ∋ Y := A
  → ⊥
fresh-seal-impossible (conversion cs)
    (R , same-var exterior , same-var target)
    (α , S , name , rep , same)
    with ∋ˡ-det exterior here
fresh-seal-impossible (conversion cs)
    (R , same-var exterior , same-var target)
    (α , S , name , rep , same) | refl
    with ∋ˡ-det target name
fresh-seal-impossible (conversion cs)
    (R , same-var exterior , same-var target)
    (α , S , name , rep , same) | refl | refl =
  no-zero-rep rep

no-fresh-value : ∀ {Δ Γ V}
  → Value V
  → underΛ Δ ∣ Γ ⊢ V ⦂ ` zero
  → ⊥
no-fresh-value (V-simple u) V⊢ = simple-¬var u V⊢
no-fresh-value (V-⟪⟫ u I-idv)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} mw ⊢U
      (conv-tail (conv-mid (conv-idv tv))) sameᵢ sameₑ wE)
    with ≈-var-source {Δ = Δᵢ} {Δ′ = Δᶜ} sameᵢ
no-fresh-value (V-⟪⟫ u I-idv)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} mw ⊢U
      (conv-tail (conv-mid (conv-idv tv))) sameᵢ sameₑ wE)
    | Y , refl = simple-¬var u ⊢U
no-fresh-value (V-⟪⟫ u I-fun)
    (boundary _ _ (conv-tail (conv-mid (conv-fun _ _))) _
      (_ , same-var _ , ()) _)
no-fresh-value (V-⟪⟫ u I-all)
    (boundary _ _ (conv-tail (conv-mid (conv-all _))) _
      (_ , same-var _ , ()) _)
no-fresh-value (V-⟪⟫ u I-seal)
    (boundary mw ⊢U (conv-tail (conv-seal square)) sameᵢ sameₑ wE) =
  fresh-seal-impossible (bw-conversion mw) sameₑ square
no-fresh-value (V-⟪⟫ u I-seal-seq)
    (boundary mw ⊢U
      (conv-tail (conv-seal-seq ⊢t square not-id)) sameᵢ sameₑ wE) =
  fresh-seal-impossible (bw-conversion mw) sameₑ square
no-fresh-value (V-fresh v fresh)
    (boundary _ _ (conv-tail (conv-mid conv-id★)) _
      (_ , same-var _ , ()) _)

no-bot-value : ∀ {Δ Γ V}
  → Value V
  → Δ ∣ Γ ⊢ V ⦂ `∀ (` zero)
  → ⊥
no-bot-value (V-simple S-$) ()
no-bot-value (V-simple S-true) ()
no-bot-value (V-simple S-false) ()
no-bot-value (V-simple S-ƛ) ()
no-bot-value (V-simple (S-Λ vN)) (⊢Λ _ ⊢N) =
  no-fresh-value vN ⊢N
no-bot-value (V-simple (S-cast v I-tag)) (⊢cast _ () _)
no-bot-value (V-simple (S-cast v I-↦)) (⊢cast _ () _)
no-bot-value (V-simple (S-cast v I-∀ᵖ))
    (⊢cast W⊢ (⊢all ⊢p) len) with coercion-to-fresh ⊢p
no-bot-value (V-simple (S-cast v I-∀ᵖ))
    (⊢cast W⊢ (⊢all ⊢p) len) | refl = no-bot-value v W⊢
no-bot-value (V-simple (S-cast v I-gen))
    (⊢cast W⊢ (⊢gen ⊢p wA () z∈B nsA safe) len)
no-bot-value (V-⟪⟫ u I-idv)
    (boundary _ _ (conv-tail (conv-mid (conv-idv _))) _
      (_ , same-∀ _ , ()) _)
no-bot-value (V-⟪⟫ u I-fun)
    (boundary _ _ (conv-tail (conv-mid (conv-fun _ _))) _
      (_ , same-∀ _ , ()) _)
no-bot-value {Δ = Δ} (V-⟪⟫ u I-all)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} mw ⊢U
      (conv-tail (conv-mid (conv-all ⊢s))) sameᵢ sameₑ wE)
    with ≈-∀-fresh-target {Δ = Δ} {Δ′ = Δᶜ} sameₑ
no-bot-value {Δ = Δ} (V-⟪⟫ u I-all)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} mw ⊢U
      (conv-tail (conv-mid (conv-all ⊢s))) sameᵢ sameₑ wE)
    | refl with conversion-to-fresh ⊢s
no-bot-value {Δ = Δ} (V-⟪⟫ u I-all)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} mw ⊢U
      (conv-tail (conv-mid (conv-all ⊢s))) sameᵢ sameₑ wE)
    | refl | refl with ≈-∀-fresh-source {Δ = Δᵢ} {Δ′ = Δᶜ} sameᵢ
no-bot-value {Δ = Δ} (V-⟪⟫ u I-all)
    (boundary {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} mw ⊢U
      (conv-tail (conv-mid (conv-all ⊢s))) sameᵢ sameₑ wE)
    | refl | refl | refl = no-bot-value (V-simple u) ⊢U
no-bot-value (V-⟪⟫ u I-seal)
    (boundary _ _ (conv-tail (conv-seal _)) _
      (_ , same-∀ _ , ()) _)
no-bot-value (V-⟪⟫ u I-seal-seq)
    (boundary _ _ (conv-tail (conv-seal-seq _ _ _)) _
      (_ , same-∀ _ , ()) _)
no-bot-value (V-fresh v fresh)
    (boundary _ _ (conv-tail (conv-mid conv-id★)) _
      (_ , same-∀ _ , ()) _)
