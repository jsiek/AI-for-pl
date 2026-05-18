module proof.ConsistencyProperties where

-- File Charter:
--   * Properties of the Consistency relation

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Properties using (length-replicate; ++-identityʳ)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective; m<n⇒m<1+n)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Consistency
open import Types
open import proof.TypeProperties
  using
    ( raiseVarFrom
    ; raiseVarFrom-injective
    ; raiseVarFrom-<-inv
    )

cong-~ :
  ∀ {Γ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Γ ⊢ A ~ B →
  Γ ⊢ A′ ~ B′
cong-~ refl refl h = h

swapMode : CMode → CMode
swapMode left = right
swapMode right = left
swapMode both = both
swapMode neither = neither

swapCCtx : CCtx → CCtx
swapCCtx [] = []
swapCCtx (m ∷ Γ) = swapMode m ∷ swapCCtx Γ

swap∋ᶜ :
  ∀ {Γ X m} →
  Γ ∋ᶜ X ∶ m →
  swapCCtx Γ ∋ᶜ X ∶ swapMode m
swap∋ᶜ here = here
swap∋ᶜ (there x∈) = there (swap∋ᶜ x∈)

length-swapCCtx :
  ∀ Γ →
  length (swapCCtx Γ) ≡ length Γ
length-swapCCtx [] = refl
length-swapCCtx (m ∷ Γ) = cong suc (length-swapCCtx Γ)

------------------------------------------------------------------------
-- Consistency is Symmetric
------------------------------------------------------------------------

~-sym :
  ∀ {Γ A B} →
  Γ ⊢ A ~ B →
  swapCCtx Γ ⊢ B ~ A
~-sym ★-~-★ = ★-~-★
~-sym (X-~-X x∈) = X-~-X (swap∋ᶜ x∈)
~-sym ι-~-ι = ι-~-ι
~-sym (⇒-~-⇒ A~A′ B~B′) =
  ⇒-~-⇒ (~-sym A~A′) (~-sym B~B′)
~-sym (∀-~-∀ A~B) = ∀-~-∀ (~-sym A~B)
~-sym (A-~-★ g A~G) = ★-~-B g (~-sym A~G)
~-sym (★-~-B h H~B) = A-~-★ h (~-sym H~B)
~-sym (νX-~-★ x∈) = ★-~-νX (swap∋ᶜ x∈)
~-sym (★-~-νX x∈) = νX-~-★ (swap∋ᶜ x∈)
~-sym {Γ = Γ} (∀-~-B {B = B} wfB A~⇑B) =
  A-~-∀
    (subst (λ n → WfTy n 0 B) (sym (length-swapCCtx Γ)) wfB)
    (~-sym A~⇑B)
~-sym {Γ = Γ} (A-~-∀ {A = A} wfA ⇑A~B) =
  ∀-~-B
    (subst (λ n → WfTy n 0 A) (sym (length-swapCCtx Γ)) wfA)
    (~-sym ⇑A~B)


------------------------------------------------------------------------
-- Consistency Context Helpers
------------------------------------------------------------------------

length-leftICtx : ∀ Γ → length (leftICtx Γ) ≡ length Γ
length-leftICtx [] = refl
length-leftICtx (m ∷ Γ) = cong suc (length-leftICtx Γ)

length-rightICtx : ∀ Γ → length (rightICtx Γ) ≡ length Γ
length-rightICtx [] = refl
length-rightICtx (m ∷ Γ) = cong suc (length-rightICtx Γ)

length-boths[] : ∀ Δ → length (boths Δ []) ≡ Δ
length-boths[] Δ
  rewrite ++-identityʳ (replicate Δ both)
        | (length-replicate Δ {both}) = refl


drop∋ᶜ-mode :
  ∀ {d Φ Γ X m} →
  (Φ ++ d ∷ Γ) ∋ᶜ raiseVarFrom (length Φ) X ∶ m →
  (Φ ++ Γ) ∋ᶜ X ∶ m
drop∋ᶜ-mode {Φ = []} (there x∈) = x∈
drop∋ᶜ-mode {Φ = m₀ ∷ Φ} {X = zero} here = here
drop∋ᶜ-mode {Φ = m₀ ∷ Φ} {X = suc X} (there x∈) =
  there (drop∋ᶜ-mode {Φ = Φ} x∈)

drop∋ᶜ-neither :
  ∀ {Φ Γ X m} →
  (Φ ++ neither ∷ Γ) ∋ᶜ raiseVarFrom (length Φ) X ∶ m →
  (Φ ++ Γ) ∋ᶜ X ∶ m
drop∋ᶜ-neither {Φ = Φ} {Γ = Γ} {X = X} x∈ =
  drop∋ᶜ-mode {d = neither} {Φ = Φ} {Γ = Γ} {X = X} x∈

drop<-raise-mode :
  ∀ {d : CMode}{ Φ Γ X} →
  raiseVarFrom (length Φ) X < length (Φ ++ d ∷ Γ) →
  X < length (Φ ++ Γ)
drop<-raise-mode {Φ = []} (s<s X<Γ) = X<Γ
drop<-raise-mode {Φ = m ∷ Φ} {X = zero} z<s = z<s
drop<-raise-mode {Φ = m ∷ Φ} {X = suc X} (s<s X<Γ) =
  s<s (drop<-raise-mode {Φ = Φ} X<Γ)

drop<-raise :
  ∀ {Φ Γ X} →
  raiseVarFrom (length Φ) X < length (Φ ++ neither ∷ Γ) →
  X < length (Φ ++ Γ)
drop<-raise {Φ = Φ} {Γ = Γ} {X = X} X<Γ =
  drop<-raise-mode {d = neither} {Φ = Φ} {Γ = Γ} {X = X} X<Γ
