module SimLeftLemmas where

-- File Charter:
--   * Local helper lemmas for the left-to-right simulation proof in
--   * `DGGSim.agda`.
--   * Provides the beta-family lemmas used by `sim-left`: ordinary beta,
--     left-up function casts, and left-down function casts.
--   * Keeps the catchup and substitution proof obligations owned by these
--     lemmas next to the lemmas that use them.

open import Data.List using ([]; List; length; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-comm; m+[n∸m]≡n)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; trans)

open import Types
open import UpDown using
  ( Up
  ; Down
  ; CastPerm
  ; wt-tag
  ; wt-unseal
  ; wt-unseal★
  ; wt-↦
  ; wt-∀
  ; wt-ν
  ; wt-id
  ; wt-untag
  ; wt-seal
  ; wt-seal★
  ; cast-tag
  ; _∣_∣_∣_⊢_⦂_⊑_
  ; _∣_∣_∣_⊢_⦂_⊒_
  )
open import Store using (StoreWf; _⊆ˢ_)
open import ImprecisionIndexed
open import Terms using (Term; ƛ_⇒_; _·_; _⦂∀_[_]; _up_; _down_; wk⊒)
open import TermProperties using (_[_])
open import TermImprecisionIndexed
open import ReductionFresh
open import PreservationFresh using (length-append-tag; wkΨ-cast-tag-⊒)

{-
   If V ⊑ N′ then N′ —↠ V′ and V ⊑ V′.
-}
right-extra-up-catchup :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ u′} →
  {pB : [] ⊢ A ⊑ᵢ B′} →
  (Φ : List CastPerm) →
  length Φ ≡ Ψˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ A′ →
  0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  Σ[ Ψʳ′ ∈ SealCtx ]
  Σ[ Σʳ′ ∈ Store ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
    Σ[ W′ ∈ Term ]
      (Value W′ ×
       (Σʳ ∣ (V′ up u′) —↠ Σʳ′ ∣ W′) ×
       (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ W′ ⦂ A ⊑ B′))
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′}
  {pB = pB} Φ lenΦ wfΣʳ vV vV′ rel (wt-tag p g ok) =
  Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up tag , (V′ up u′ ∎) ,
  ⊑upR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel (wt-tag p g ok)
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  {pB = pB} Φ lenΦ wfΣʳ vV (_down_ {V = W} vW seal)
  (⊑down Φd lenD rel hd (wt-seal d⊢ h₂ α∈₂))
  (wt-unseal {p = u} h α∈Φ u⊢)
    with left-value-right-catchup wfΣʳ vV
           (⊑upR {pB = pB} Φ lenΦ
             (⊑down Φd lenD rel hd d⊢)
             (subst (λ X → 0 ∣ _ ∣ _ ∣ Φ ⊢ u ⦂ X ⊑ _) {!!} u⊢))
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  {pB = pB} Φ lenΦ wfΣʳ vV (_down_ {V = W} vW seal)
  (⊑down Φd lenD rel hd (wt-seal d⊢ h₂ α∈₂))
  (wt-unseal {p = u} h α∈Φ u⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , W′ , vW′ , Wdownup↠W′ , V⊑W′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , W′ , vW′ ,
  (_ —→⟨ id-step (seal-unseal vW) ⟩ Wdownup↠W′) ,
  V⊑W′
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  {pB = pB} Φ lenΦ wfΣʳ vV (_down_ {V = W} vW seal)
  (⊑down Φd lenD rel hd (wt-seal★ d⊢ h₂ α∈₂))
  (wt-unseal {p = u} h α∈Φ u⊢)
    with left-value-right-catchup wfΣʳ vV
           (⊑upR {pB = pB} Φ lenΦ
             (⊑down Φd lenD rel hd d⊢)
             (subst (λ X → 0 ∣ _ ∣ _ ∣ Φ ⊢ u ⦂ X ⊑ _) {!!} u⊢))
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  {pB = pB} Φ lenΦ wfΣʳ vV (_down_ {V = W} vW seal)
  (⊑down Φd lenD rel hd (wt-seal★ d⊢ h₂ α∈₂))
  (wt-unseal {p = u} h α∈Φ u⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , W′ , vW′ , Wdownup↠W′ , V⊑W′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , W′ , vW′ ,
  (_ —→⟨ id-step (seal-unseal vW) ⟩ Wdownup↠W′) ,
  V⊑W′
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  {pB = pB} Φ lenΦ wfΣʳ vV (_down_ {V = W} vW seal)
  (⊑downR Φd lenD rel (wt-seal d⊢ h₂ α∈₂))
  (wt-unseal {p = u} h α∈Φ u⊢)
    with left-value-right-catchup wfΣʳ vV
           (⊑upR {pB = pB} Φ lenΦ
             (⊑downR Φd lenD rel d⊢)
             (subst (λ X → 0 ∣ _ ∣ _ ∣ Φ ⊢ u ⦂ X ⊑ _) {!!} u⊢))
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  {pB = pB} Φ lenΦ wfΣʳ vV (_down_ {V = W} vW seal)
  (⊑downR Φd lenD rel (wt-seal d⊢ h₂ α∈₂))
  (wt-unseal {p = u} h α∈Φ u⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , W′ , vW′ , Wdownup↠W′ , V⊑W′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , W′ , vW′ ,
  (_ —→⟨ id-step (seal-unseal vW) ⟩ Wdownup↠W′) ,
  V⊑W′
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  {pB = pB} Φ lenΦ wfΣʳ vV (_down_ {V = W} vW seal)
  (⊑downR Φd lenD rel (wt-seal★ d⊢ h₂ α∈₂))
  (wt-unseal {p = u} h α∈Φ u⊢)
    with left-value-right-catchup wfΣʳ vV
           (⊑upR {pB = pB} Φ lenΦ
             (⊑downR Φd lenD rel d⊢)
             (subst (λ X → 0 ∣ _ ∣ _ ∣ Φ ⊢ u ⦂ X ⊑ _) {!!} u⊢))
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  {pB = pB} Φ lenΦ wfΣʳ vV (_down_ {V = W} vW seal)
  (⊑downR Φd lenD rel (wt-seal★ d⊢ h₂ α∈₂))
  (wt-unseal {p = u} h α∈Φ u⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , W′ , vW′ , Wdownup↠W′ , V⊑W′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , W′ , vW′ ,
  (_ —→⟨ id-step (seal-unseal vW) ⟩ Wdownup↠W′) ,
  V⊑W′
right-extra-up-catchup Φ lenΦ wfΣʳ vV vV′ rel
  (wt-unseal h α∈Φ p) = {!!}
right-extra-up-catchup Φ lenΦ wfΣʳ vV vV′ rel
  (wt-unseal★ h α∈Φ p) = {!!}
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′}
  {pB = pB} Φ lenΦ wfΣʳ vV vV′ rel (wt-↦ hp hq) =
  Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up _↦_ , (V′ up u′ ∎) ,
  ⊑upR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel (wt-↦ hp hq)
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′}
  {pB = pB} Φ lenΦ wfΣʳ vV vV′ rel (wt-∀ hp) =
  Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up ∀ᵖ , (V′ up u′ ∎) ,
  ⊑upR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel (wt-∀ hp)
right-extra-up-catchup Φ lenΦ wfΣʳ vV vV′ rel
  (wt-ν hp) = {!!}
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′}
  Φ lenΦ wfΣʳ vV vV′ rel (wt-id wfA) =
  Ψʳ , Σʳ , wfΣʳ , V′ , vV′ ,
  ((V′ up u′) —→⟨ id-step (id-up vV′) ⟩ V′ ∎) ,
  rel

right-extra-down-catchup :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ d′} →
  {pB : [] ⊢ A ⊑ᵢ B′} →
  (Φ : List CastPerm) →
  length Φ ≡ Ψˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ A′ →
  0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  Σ[ Ψʳ′ ∈ SealCtx ]
  Σ[ Σʳ′ ∈ Store ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
    Σ[ W′ ∈ Term ]
      (Value W′ ×
       (Σʳ ∣ (V′ down d′) —↠ Σʳ′ ∣ W′) ×
       (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ W′ ⦂ A ⊑ B′))
right-extra-down-catchup Φ lenΦ wfΣʳ vV vV′ rel
  (wt-untag g ok ℓ p) = {!!}
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
  {pB = pB} Φ lenΦ wfΣʳ vV vV′ rel (wt-seal p h α∈Φ) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down seal , (V′ down d′ ∎) ,
  ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel (wt-seal p h α∈Φ)
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
  {pB = pB} Φ lenΦ wfΣʳ vV vV′ rel (wt-seal★ p h α∈Φ) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down seal , (V′ down d′ ∎) ,
  ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel (wt-seal★ p h α∈Φ)
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
  {pB = pB} Φ lenΦ wfΣʳ vV vV′ rel (wt-↦ hp hq) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down _↦_ , (V′ down d′ ∎) ,
  ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel (wt-↦ hp hq)
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
  {pB = pB} Φ lenΦ wfΣʳ vV vV′ rel (wt-∀ hp) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down ∀ᵖ , (V′ down d′ ∎) ,
  ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel (wt-∀ hp)
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
  {pB = pB} Φ lenΦ wfΣʳ vV vV′ rel (wt-ν hp) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down ν_ , (V′ down d′ ∎) ,
  ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel (wt-ν hp)
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′}
  Φ lenΦ wfΣʳ vV vV′ rel (wt-id wfA) =
  Ψʳ , Σʳ , wfΣʳ , V′ , vV′ ,
  ((V′ down d′) —→⟨ id-step (id-down vV′) ⟩ V′ ∎) ,
  rel

right-extra-up-catchup-left :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B B′ u u′} →
  {pB : [] ⊢ B ⊑ᵢ B′} →
  (Φ : List CastPerm) →
  length Φ ≡ Ψˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ A′ →
  0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ u ⦂ A ⊑ B →
  0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  Σ[ Ψʳ′ ∈ SealCtx ]
  Σ[ Σʳ′ ∈ Store ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
    Σ[ W′ ∈ Term ]
      (Value W′ ×
       (Σʳ ∣ (V′ up u′) —↠ Σʳ′ ∣ W′) ×
       (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          (V up u) ⊑ W′ ⦂ B ⊑ B′))
right-extra-up-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hu (wt-tag p g ok) =
  Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up tag , (V′ up u′ ∎) ,
  ⊑up {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hu (wt-tag p g ok)
right-extra-up-catchup-left Φ lenΦ wfΣʳ vV vV′ rel hu
  (wt-unseal h α∈Φ p) = {!!}
right-extra-up-catchup-left Φ lenΦ wfΣʳ vV vV′ rel hu
  (wt-unseal★ h α∈Φ p) = {!!}
right-extra-up-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hu (wt-↦ hp hq) =
  Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up _↦_ , (V′ up u′ ∎) ,
  ⊑up {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hu (wt-↦ hp hq)
right-extra-up-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hu (wt-∀ hp) =
  Ψʳ , Σʳ , wfΣʳ , V′ up u′ , vV′ up ∀ᵖ , (V′ up u′ ∎) ,
  ⊑up {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hu (wt-∀ hp)
right-extra-up-catchup-left Φ lenΦ wfΣʳ vV vV′ rel hu
  (wt-ν hp) = {!!}
right-extra-up-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {u′ = u′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hu (wt-id wfA) =
  Ψʳ , Σʳ , wfΣʳ , V′ , vV′ ,
  ((V′ up u′) —→⟨ id-step (id-up vV′) ⟩ V′ ∎) ,
  ⊑upL {pA = ⊑-type-imprecision rel} {pB = pB} Φ lenΦ rel hu

right-extra-down-catchup-left :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B B′ d d′} →
  {pB : [] ⊢ B ⊑ᵢ B′} →
  (Φ : List CastPerm) →
  length Φ ≡ Ψˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ A′ →
  0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ d ⦂ A ⊒ B →
  0 ∣ Ψˡ ∣ Σˡ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  Σ[ Ψʳ′ ∈ SealCtx ]
  Σ[ Σʳ′ ∈ Store ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
    Σ[ W′ ∈ Term ]
      (Value W′ ×
       (Σʳ ∣ (V′ down d′) —↠ Σʳ′ ∣ W′) ×
       (⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          (V down d) ⊑ W′ ⦂ B ⊑ B′))
right-extra-down-catchup-left Φ lenΦ wfΣʳ vV vV′ rel hd
  (wt-untag g ok ℓ p) = {!!}
right-extra-down-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hd (wt-seal p h α∈Φ) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down seal , (V′ down d′ ∎) ,
  ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hd (wt-seal p h α∈Φ)
right-extra-down-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hd (wt-seal★ p h α∈Φ) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down seal , (V′ down d′ ∎) ,
  ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hd (wt-seal★ p h α∈Φ)
right-extra-down-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hd (wt-↦ hp hq) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down _↦_ , (V′ down d′ ∎) ,
  ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hd (wt-↦ hp hq)
right-extra-down-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hd (wt-∀ hp) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down ∀ᵖ , (V′ down d′ ∎) ,
  ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hd (wt-∀ hp)
right-extra-down-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hd (wt-ν hp) =
  Ψʳ , Σʳ , wfΣʳ , V′ down d′ , vV′ down ν_ , (V′ down d′ ∎) ,
  ⊑down {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hd (wt-ν hp)
right-extra-down-catchup-left
  {Ψʳ = Ψʳ} {Σʳ = Σʳ} {V′ = V′} {d′ = d′} {pB = pB}
  Φ lenΦ wfΣʳ vV vV′ rel hd (wt-id wfA) =
  Ψʳ , Σʳ , wfΣʳ , V′ , vV′ ,
  ((V′ down d′) —→⟨ id-step (id-down vV′) ⟩ V′ ∎) ,
  ⊑downL {pA = ⊑-type-imprecision rel} {pB = pB} Φ lenΦ rel hd

left-value-right-catchup wfΣʳ vV (⊑` ())
left-value-right-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣʳ (ƛ A ⇒ N)
  (⊑ƛ {A′ = A′} {M′ = N′} {pA = pA} {pB = pB} hA hA′ rel) =
  Ψʳ , Σʳ , wfΣʳ , ƛ A′ ⇒ N′ , ƛ A′ ⇒ N′ , (ƛ A′ ⇒ N′ ∎) ,
  ⊑ƛ {pA = pA} {pB = pB} hA hA′ rel
left-value-right-catchup wfΣʳ () (⊑· L⊑L′ M⊑M′)
left-value-right-catchup wfΣʳ () (⊑⦂∀ rel wfA wfB hT)
left-value-right-catchup wfΣʳ () (⊑⦂∀-ν A B p rel wfA hT inst)
left-value-right-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ} wfΣʳ ($ κ) ⊑$ =
  Ψʳ , Σʳ , wfΣʳ , $ κ , $ κ , ($ κ ∎) , ⊑$
left-value-right-catchup wfΣʳ () (⊑⊕ L⊑L′ M⊑M′)
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_up_ {V = V} {p = u} vV vu)
  (⊑up {B = B} {B′ = B′} {pB = pB} {u′ = u′} Φ lenΦ rel hu hu′)
    with left-value-right-catchup wfΣʳ vV rel
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_up_ {V = V} {p = u} vV vu)
  (⊑up {B = B} {B′ = B′} {pB = pB} {u′ = u′} Φ lenΦ rel hu hu′)
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , M′↠V′ᵥ , V⊑V′ᵥ
    with right-extra-up-catchup-left {pB = pB} Φ lenΦ wfΣʳᵃ
           vV vV′ᵥ V⊑V′ᵥ hu hu′
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_up_ {V = V} {p = u} vV vu)
  (⊑up {B = B} {B′ = B′} {pB = pB} {u′ = u′} Φ lenΦ rel hu hu′)
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ᵥ , vV′ᵥ , M′↠V′ᵥ , V⊑V′ᵥ
  | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′ᵥup↠W′ , Vup⊑W′ =
  Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
  multi-trans (up-↠ M′↠V′ᵥ) V′ᵥup↠W′ ,
  Vup⊑W′
{-
    Case E ⊢ (V up p) ⊑ (M′ up u′) ⦂ B ⊑ B′
                                     ^^   
                                     |  \ 
             V        ⊑ M′         ⦂ A₁ ⊑ A′
             
    have:
      V ⊑ M′ ⦂ A₁ ⊑ A′
      u′ ⦂ A′ ⊑ B
      p ⦂ A₁ ⊑ A
      pB : [] ⊢ A ⊑ᵢ B   (not in scope)
      pA : [] ⊢ A₁ ⊑ᵢ A′   (not in scope)
    nts:
      M′ up u′ —↠ V′
      V up p ⊑ V′     for some V′ 
-}
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_up_ vV vu) (⊑upL {pB = pB} Φ lenΦ rel hu)
    with left-value-right-catchup wfΣʳ vV rel
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_up_ vV vu) (⊑upL {pB = pB} Φ lenΦ rel hu)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ ,
  ⊑upL {pA = ⊑-type-imprecision V⊑V′} {pB = pB} Φ lenΦ V⊑V′ hu
left-value-right-catchup
  {Σʳ = Σʳ} wfΣʳ vV (⊑upR {pB = pB} Φ lenΦ rel hu′)
    with left-value-right-catchup wfΣʳ vV rel
left-value-right-catchup
  {Σʳ = Σʳ} wfΣʳ vV (⊑upR {pB = pB} Φ lenΦ rel hu′)
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-up-catchup {pB = pB} Φ lenΦ wfΣʳᵃ vV vV′ V⊑V′ hu′
left-value-right-catchup
  {Σʳ = Σʳ} wfΣʳ vV (⊑upR {pB = pB} Φ lenΦ rel hu′)
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′up↠W′ , V⊑W′ =
  Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
  multi-trans (up-↠ M′↠V′) V′up↠W′ ,
  V⊑W′
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_down_ vV vd) (⊑down {pB = pB} Φ lenΦ rel hd hd′)
    with left-value-right-catchup wfΣʳ vV rel
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_down_ vV vd) (⊑down {pB = pB} Φ lenΦ rel hd hd′)
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-down-catchup-left {pB = pB} Φ lenΦ wfΣʳᵃ
           vV vV′ V⊑V′ hd hd′
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_down_ vV vd) (⊑down {pB = pB} Φ lenΦ rel hd hd′)
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′down↠W′ , Vdown⊑W′ =
  Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
  multi-trans (down-↠ M′↠V′) V′down↠W′ ,
  Vdown⊑W′
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_down_ vV vd) (⊑downL {pB = pB} Φ lenΦ rel hd)
    with left-value-right-catchup wfΣʳ vV rel
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣʳ (_down_ vV vd) (⊑downL {pB = pB} Φ lenΦ rel hd)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ ,
  ⊑downL {pA = ⊑-type-imprecision V⊑V′} {pB = pB}
    Φ lenΦ V⊑V′ hd
left-value-right-catchup
  {Σʳ = Σʳ} wfΣʳ vV (⊑downR {pB = pB} Φ lenΦ rel hd′)
    with left-value-right-catchup wfΣʳ vV rel
left-value-right-catchup
  {Σʳ = Σʳ} wfΣʳ vV (⊑downR {pB = pB} Φ lenΦ rel hd′)
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-down-catchup {pB = pB} Φ lenΦ wfΣʳᵃ vV vV′ V⊑V′ hd′
left-value-right-catchup
  {Σʳ = Σʳ} wfΣʳ vV (⊑downR {pB = pB} Φ lenΦ rel hd′)
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ , V′down↠W′ , V⊑W′ =
  Ψʳᵝ , Σʳᵝ , wfΣʳᵝ , W′ , vW′ ,
  multi-trans (down-↠ M′↠V′) V′down↠W′ ,
  V⊑W′
left-value-right-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣʳ (Λ N) (⊑Λ {M′ = N′} {p = p} vM vM′ wfA wfB rel) =
  Ψʳ , Σʳ , wfΣʳ , Λ N′ , Λ N′ , (Λ N′ ∎) ,
  ⊑Λ {p = p} vM vM′ wfA wfB rel
left-value-right-catchup wfΣʳ () (⊑blameR M⊢)

--------------------------------------------------------------------------------
-- GTLC `sim-beta`, adapted to imprecision orientation.

sim-left-beta :
  ∀ {Ψ Ψʳ Σˡ Σʳ V′ W W′ N A A′ A₂ B B′} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
    (ƛ A₂ ⇒ N) ⊑ V′ ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) →
  StoreWf 0 Ψʳ Σʳ →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ N [ W ] ⊑ N′ ⦂ B ⊑ B′))
sim-left-beta
  {Σʳ = Σʳ} {W′ = W′}
  (⊑ƛ {pA = pA} {pB = pB} hA hA′ rel)
  wfΣʳ (ƛ A′ ⇒ N′) W⊑W′ vW vW′ =
  Σʳ , N′ [ W′ ] ,
  (((ƛ A′ ⇒ N′) · W′) —→⟨ id-step (β vW′) ⟩
   (N′ [ W′ ]) ∎) ,
  []-⊑ {pA = pA} {pB = pB} rel W⊑W′
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣʳ vW
           (⊑downR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣʳᵃ vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR {pA = ⊑-type-imprecision N[W]⊑N′} {pB = pCod′}
    Φ lenΦ N[W]⊑N′ hq
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣʳ vW
           (⊑upR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣʳᵃ vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR {pA = ⊑-type-imprecision N[W]⊑N′} {pB = pCod′}
    Φ lenΦ N[W]⊑N′ hq

--------------------------------------------------------------------------------

-- GTLC `sim-beta-cast`, adapted to left `up` function casts.
sim-left-beta-up :
  ∀ {Ψ Ψʳ Σˡ Σʳ V V′ W W′ A A′ B B′}
    {p : Down} {q : Up} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
    (V up (Up._↦_ p q)) ⊑ V′ ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          ((V · (W down p)) up q) ⊑ N′ ⦂ B ⊑ B′))
sim-left-beta-up
  {Σʳ = Σʳ} {V′ = V′} {W′ = W′}
  (⊑upL {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV vV′ W⊑W′ vW vW′ =
  Σʳ , V′ · W′ ,
  ((V′ · W′) ∎) ,
  ⊑upL {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑downL {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp))
    hq
sim-left-beta-up
  {Σʳ = Σʳ} {W′ = W′}
  (⊑up {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq) (wt-↦ hp′ hq′))
  wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′ =
  Σʳ , _ ,
  (_ —→⟨ id-step (β-up-↦ vV′ vW′) ⟩ _ ∎) ,
  ⊑up {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑down {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp hp′))
    hq hq′
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣʳ vW
           (⊑downR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣʳᵃ vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣʳ vW
           (⊑upR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣʳᵃ vV vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left-beta-up
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq

--------------------------------------------------------------------------------

-- GTLC `sim-beta-cast`, adapted to left `down` function casts.
sim-left-beta-down :
  ∀ {Ψ Ψʳ Σˡ Σʳ V V′ W W′ A A′ B B′}
    {p : Up} {q : Down} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
    (V down (Down._↦_ p q)) ⊑ V′ ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′) →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Value W →
  Value W′ →
  Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ (V′ · W′) —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          ((V · (W up p)) down q) ⊑ N′ ⦂ B ⊑ B′))
sim-left-beta-down
  {Σʳ = Σʳ} {V′ = V′} {W′ = W′}
  (⊑downL {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV vV′ W⊑W′ vW vW′ =
  Σʳ , V′ · W′ ,
  ((V′ · W′) ∎) ,
  ⊑downL {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑upL {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp))
    hq
sim-left-beta-down
  {Σʳ = Σʳ} {W′ = W′}
  (⊑down {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq) (wt-↦ hp′ hq′))
  wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′ =
  Σʳ , _ ,
  (_ —→⟨ id-step (β-down-↦ vV′ vW′) ⟩ _ ∎) ,
  ⊑down {pA = pCod} {pB = pCod′} Φ lenΦ
    (⊑· {pA = pDom} {pB = pCod} rel
      (⊑up {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
        Φ lenΦ W⊑W′ hp hp′))
    hq hq′
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣʳ vW
           (⊑downR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣʳᵃ vV vV′ W⊑W′ᵥ
           vW vW′ᵥ
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑upR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_up_ vV′ uv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ up _ ,
  (((_ up _) · W′) —→⟨ id-step (β-up-↦ vV′ vW′) ⟩
   up-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑upR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} wfΣʳ vW
           (⊑upR {pA = ⊑-type-imprecision W⊑W′} {pB = pDom}
             Φ lenΦ W⊑W′ hp)
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Ψʳ = Ψʳᵃ} {Σʳ = Σʳᵃ} rel wfΣʳᵃ vV vV′ W⊑W′ᵥ
           vW vW′ᵥ
sim-left-beta-down
  {Ψ = Ψ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ} {W′ = W′}
  (⊑downR {pA = ⊑ᵢ-⇒ A₀ A′₀ B₀ B′₀ pDom pCod}
    {pB = ⊑ᵢ-⇒ A₁ A′₁ B₁ B′₁ pDom′ pCod′}
    Φ lenΦ rel (wt-↦ hp hq))
  wfΣʳ vV (_down_ vV′ dv′) W⊑W′ vW vW′
  | Ψʳᵃ , Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Σʳᵝ , N′ down _ ,
  (((_ down _) · W′) —→⟨ id-step (β-down-↦ vV′ vW′) ⟩
   down-↠ (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′)) ,
  ⊑downR {pA = ⊑-type-imprecision N⊑N′} {pB = pCod′}
    Φ lenΦ N⊑N′ hq

--------------------------------------------------------------------------------
-- Worker helper slots for `sim-left` parallelization.
--
-- Rule: add new helper lemmas only in your worker slot and use the prefix
-- `sim-left-wXX-...` where XX is your worker id.
--
-- Keep each helper self-contained: statement + implementation + short note
-- naming the `DGGSim.agda` hole lines it supports.

-- Worker W01 helper slot

-- Worker W02 helper slot

-- Worker W03 helper slot

-- Supports DGGSim.agda H42 (line 528): eliminate a left identity-down cast,
-- commuting through right-only casts.
sim-left-w03-id-down :
  ∀ {Ψ Σˡ Σʳ V M′ C A B} →
  ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ (V down Down.id C) ⊑ M′ ⦂ A ⊑ B →
  Σ[ N′ ∈ Term ]
    ((Σʳ ∣ M′ —↠ Σʳ ∣ N′) ×
     (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢ V ⊑ N′ ⦂ A ⊑ B))
sim-left-w03-id-down (⊑upR {pB = pB} Φ lenΦ rel hu′)
    with sim-left-w03-id-down rel
sim-left-w03-id-down (⊑upR {pB = pB} Φ lenΦ rel hu′)
  | N′ , M′↠N′ , V⊑N′ =
  N′ up _ , up-↠ M′↠N′ ,
  ⊑upR {pA = ⊑-type-imprecision V⊑N′} {pB = pB}
    Φ lenΦ V⊑N′ hu′
sim-left-w03-id-down (⊑down {pB = pB} Φ lenΦ rel (UpDown.wt-id wfA) hd′) =
  _ , (_ ∎) ,
  ⊑downR {pA = ⊑-type-imprecision rel} {pB = pB}
    Φ lenΦ rel hd′
sim-left-w03-id-down (⊑downL Φ lenΦ rel (UpDown.wt-id wfA)) =
  _ , (_ ∎) , rel
sim-left-w03-id-down (⊑downR {pB = pB} Φ lenΦ rel hd′)
    with sim-left-w03-id-down rel
sim-left-w03-id-down (⊑downR {pB = pB} Φ lenΦ rel hd′)
  | N′ , M′↠N′ , V⊑N′ =
  N′ down _ , down-↠ M′↠N′ ,
  ⊑downR {pA = ⊑-type-imprecision V⊑N′} {pB = pB}
    Φ lenΦ V⊑N′ hd′

-- Worker W04 helper slot

-- Worker W05 helper slot

postulate
  -- Supports SimLeft.agda H28: eliminate a left seal/unseal redex,
  -- commuting through right-only casts.
  sim-left-w05-seal-unseal :
    ∀ {Ψ Σˡ Σʳ V M′ A B}
      {d : Down} {u : Up} {α : Seal} →
    Value V →
    ⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
      ((V down (UpDown.seal d α)) up (UpDown.unseal α u)) ⊑ M′ ⦂ A ⊑ B →
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ ∣ N′) ×
       (⟪ 0 , Ψ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
          ((V down d) up u) ⊑ N′ ⦂ A ⊑ B))

-- Worker W06 helper slot

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

postulate
  -- Supports SimLeft.agda H41: left `β-up-ν` allocation step.
  sim-left-w09-H41 :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ V M′ N A B} {u : Up} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] , plain-[] , refl ⟫ ⊢
      (V up (UpDown.ν u)) ⊑ M′ ⦂ A ⊑ B →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Σˡ ∣ (V up (UpDown.ν u)) —→ Σˡ′ ∣ N →
    Value V →
    (Σ[ Ψˡ″ ∈ SealCtx ]
      Σ[ Ψˡ≤Ψˡ″ ∈ Ψˡ ≤ Ψˡ″ ]
      Σ[ Σʳ′ ∈ Store ]
      Σ[ N′ ∈ Term ]
        ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
         (⟪ 0 , Ψˡ″ , Σˡ′ , [] , [] , plain-[] , refl ⟫ ⊢ N ⊑ N′ ⦂ A ⊑ B)))

-- Supports DGGSim.agda H09 (line 215): lift right multi-steps through
-- type application.
sim-left-w09-tyapp-↠ :
  ∀ {Σ Σ′ L L′ B T} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ∣ (L ⦂∀ B [ T ]) —↠ Σ′ ∣ (L′ ⦂∀ B [ T ])
sim-left-w09-tyapp-↠ (L ∎) = (L ⦂∀ _ [ _ ]) ∎
sim-left-w09-tyapp-↠ (L —→⟨ L→M ⟩ M↠N) =
  (L ⦂∀ _ [ _ ]) —→⟨ ξ-·α L→M ⟩ sim-left-w09-tyapp-↠ M↠N

-- Supports DGGSim.agda H17 (line 275): weaken both down-cast typings
-- through the same seal-context extension and store growth.
sim-left-w09-down-casts-+ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}
    {d d′ : Down} →
  (k : ℕ) →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ k + Ψ) ×
     ((Δ ∣ (k + Ψ) ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) ×
      (Δ ∣ (k + Ψ) ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′)))
sim-left-w09-down-casts-+ zero w lenΦ hd hd′ =
  _ , lenΦ , wk⊒ w hd , wk⊒ w hd′
sim-left-w09-down-casts-+ (suc k) w lenΦ hd hd′
    with sim-left-w09-down-casts-+ k w lenΦ hd hd′
sim-left-w09-down-casts-+ (suc k) w lenΦ hd hd′
  | Φ′ , lenΦ′ , hdᵣ , hdᵣ′ =
  (Φ′ ++ cast-tag ∷ []) ,
  trans (length-append-tag Φ′) (cong suc lenΦ′) ,
  wkΨ-cast-tag-⊒ hdᵣ ,
  wkΨ-cast-tag-⊒ hdᵣ′

sim-left-w09-down-casts-≤ :
  ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}
    {d d′ : Down} →
  Ψ ≤ Ψ′ →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ Ψ′) ×
     ((Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) ×
      (Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′)))
sim-left-w09-down-casts-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {A′ = A′} {B = B} {B′ = B′} {d = d} {d′ = d′}
  Ψ≤Ψ′ w lenΦ hd hd′
    with sim-left-w09-down-casts-+ (Ψ′ ∸ Ψ) w lenΦ hd hd′
sim-left-w09-down-casts-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {A′ = A′} {B = B} {B′ = B′} {d = d} {d′ = d′}
  Ψ≤Ψ′ w lenΦ hd hd′
  | Φ′ , lenΦ′ , hdᵣ , hdᵣ′ =
  let eq = trans (+-comm (Ψ′ ∸ Ψ) Ψ) (m+[n∸m]≡n Ψ≤Ψ′) in
  Φ′ , trans lenΦ′ eq ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) eq hdᵣ ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′) eq hdᵣ′

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot
