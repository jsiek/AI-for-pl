module SimRightLemmas where

-- File Charter:
--   * Local helper lemmas for the right-to-left simulation proof in
--   * `SimRight.agda`.
--   * This module is the shared helper namespace for parallel worker tasks.
--   * Keep helper lemmas grouped by worker slot to minimize merge conflicts.

open import Data.List using ([]; List; length; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-comm; m+[n∸m]≡n)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst; trans)

open import Types
open import UpDown
  using
    ( Up
    ; Down
    ; Label
    ; CastPerm
    ; cast-tag
    ; WfTy-weakenˢ
    ; _∣_∣_∣_⊢_⦂_⊑_
    ; _∣_∣_∣_⊢_⦂_⊒_
    )
open import Store using (_⊆ˢ_; ⊆ˢ-refl; ⊆ˢ-trans)
open import Terms using (Term; blame; _up_; _down_; _⦂∀_[_]; wk⊑; wk⊒)
open import ImprecisionIndexed
open import TermImprecisionIndexed
open import ReductionFresh
  using
    ( _∣_—↠_∣_
    ; _∎
    ; _—→⟨_⟩_
    ; id-step
    ; store-growth
    ; up-↠
    ; down-↠
    ; blame-up
    ; blame-down
    ; blame-·α
    ; ξ-up
    ; ξ-down
    ; ξ-·α
    )
open import PreservationFresh
  using (length-append-tag; wkΨ-cast-tag-⊑; wkΨ-cast-tag-⊒)

--------------------------------------------------------------------------------
-- Worker helper slots for `sim-right` parallelization.
--
-- Rule: add new helper lemmas only in your worker slot and use the prefix
-- `sim-right-wXX-...` where XX is your worker id.
--
-- Keep each helper self-contained: statement + implementation + short note
-- naming the `SimRight.agda` hole lines it supports.

-- Worker W01 helper slot

sim-right-w01-blames : Store → Term → Set
sim-right-w01-blames Σ M =
  Σ[ Σ′ ∈ Store ]
    Σ[ ℓ ∈ Label ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ)

sim-right-w01-result :
  ∀ {A B} →
  SealCtx → Store → Term → Term → [] ⊢ A ⊑ᵢ B → Set
sim-right-w01-result Ψ Σ M N′ p =
  (Σ[ Ψ″ ∈ SealCtx ]
    Σ[ Ψ≤Ψ″ ∈ Ψ ≤ Ψ″ ]
    Σ[ Σ′ ∈ Store ]
    Σ[ N ∈ Term ]
      ((Σ ∣ M —↠ Σ′ ∣ N) ×
       (⟪ 0 , Ψ″ , Σ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
  ⊎ sim-right-w01-blames Σ M

sim-right-w01-multi-store-growth :
  ∀ {Σ Σ′ M N} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ⊆ˢ Σ′
sim-right-w01-multi-store-growth (_ ∎) = ⊆ˢ-refl
sim-right-w01-multi-store-growth (_ —→⟨ M→M′ ⟩ M′↠N) =
  ⊆ˢ-trans (store-growth M→M′)
            (sim-right-w01-multi-store-growth M′↠N)

sim-right-w01-up-blame-↠ :
  ∀ {Σ Σ′ M ℓ p} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M up p) —↠ Σ′ ∣ blame ℓ
sim-right-w01-up-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ up p) —→⟨ id-step blame-up ⟩ blame ℓ ∎
sim-right-w01-up-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M up p) —→⟨ ξ-up M→M′ ⟩ sim-right-w01-up-blame-↠ M′↠blame

sim-right-w01-down-blame-↠ :
  ∀ {Σ Σ′ M ℓ p} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M down p) —↠ Σ′ ∣ blame ℓ
sim-right-w01-down-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ down p) —→⟨ id-step blame-down ⟩ blame ℓ ∎
sim-right-w01-down-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M down p) —→⟨ ξ-down M→M′ ⟩
  sim-right-w01-down-blame-↠ M′↠blame

sim-right-w01-tyapp-blame-↠ :
  ∀ {Σ Σ′ M ℓ B T} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ blame ℓ
sim-right-w01-tyapp-blame-↠ {ℓ = ℓ} {B = B} {T = T} (_ ∎) =
  (blame ℓ ⦂∀ B [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎
sim-right-w01-tyapp-blame-↠ {B = B} {T = T}
    (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩
  sim-right-w01-tyapp-blame-↠ M′↠blame

sim-right-w01-tyapp-↠ :
  ∀ {Σ Σ′ M N B T} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ (N ⦂∀ B [ T ])
sim-right-w01-tyapp-↠ (M ∎) = (M ⦂∀ _ [ _ ]) ∎
sim-right-w01-tyapp-↠ (M —→⟨ M→M′ ⟩ M′↠N) =
  (M ⦂∀ _ [ _ ]) —→⟨ ξ-·α M→M′ ⟩
  sim-right-w01-tyapp-↠ M′↠N

sim-right-w01-up-cast-+ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Φ : List CastPerm}{A B : Ty}{u : Up} →
  (k : ℕ) →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u ⦂ A ⊑ B →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ k + Ψ) ×
     (Δ ∣ (k + Ψ) ∣ Σ′ ∣ Φ′ ⊢ u ⦂ A ⊑ B))
sim-right-w01-up-cast-+ zero w lenΦ hu = _ , lenΦ , wk⊑ w hu
sim-right-w01-up-cast-+ (suc k) w lenΦ hu
    with sim-right-w01-up-cast-+ k w lenΦ hu
sim-right-w01-up-cast-+ (suc k) w lenΦ hu | Φ′ , lenΦ′ , hu′ =
  (Φ′ ++ cast-tag ∷ []) ,
  trans (length-append-tag Φ′) (cong suc lenΦ′) ,
  wkΨ-cast-tag-⊑ hu′

sim-right-w01-up-cast-≤ :
  ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{Φ : List CastPerm}{A B : Ty}{u : Up} →
  Ψ ≤ Ψ′ →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u ⦂ A ⊑ B →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ Ψ′) ×
     (Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ u ⦂ A ⊑ B))
sim-right-w01-up-cast-≤
    {Δ} {Ψ} {Ψ′} {Σ′ = Σ′} {A = A} {B = B} {u = u}
    Ψ≤Ψ′ w lenΦ hu
    with sim-right-w01-up-cast-+ (Ψ′ ∸ Ψ) w lenΦ hu
sim-right-w01-up-cast-≤
    {Δ} {Ψ} {Ψ′} {Σ′ = Σ′} {A = A} {B = B} {u = u}
    Ψ≤Ψ′ w lenΦ hu
  | Φ′ , lenΦ′ , hu′ =
  let eq = trans (+-comm (Ψ′ ∸ Ψ) Ψ) (m+[n∸m]≡n Ψ≤Ψ′) in
  Φ′ , trans lenΦ′ eq ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ u ⦂ A ⊑ B) eq hu′

sim-right-w01-down-cast-+ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Φ : List CastPerm}{A B : Ty}{d : Down} →
  (k : ℕ) →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ k + Ψ) ×
     (Δ ∣ (k + Ψ) ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B))
sim-right-w01-down-cast-+ zero w lenΦ hd = _ , lenΦ , wk⊒ w hd
sim-right-w01-down-cast-+ (suc k) w lenΦ hd
    with sim-right-w01-down-cast-+ k w lenΦ hd
sim-right-w01-down-cast-+ (suc k) w lenΦ hd | Φ′ , lenΦ′ , hd′ =
  (Φ′ ++ cast-tag ∷ []) ,
  trans (length-append-tag Φ′) (cong suc lenΦ′) ,
  wkΨ-cast-tag-⊒ hd′

sim-right-w01-down-cast-≤ :
  ∀ {Δ Ψ Ψ′}{Σ Σ′ : Store}{Φ : List CastPerm}
    {A B : Ty}{d : Down} →
  Ψ ≤ Ψ′ →
  Σ ⊆ˢ Σ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ Ψ′) ×
     (Δ ∣ Ψ′ ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B))
sim-right-w01-down-cast-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {B = B} {d = d} Ψ≤Ψ′ w lenΦ hd
    with sim-right-w01-down-cast-+ (Ψ′ ∸ Ψ) w lenΦ hd
sim-right-w01-down-cast-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {B = B} {d = d} Ψ≤Ψ′ w lenΦ hd
  | Φ′ , lenΦ′ , hd′ =
  let eq = trans (+-comm (Ψ′ ∸ Ψ) Ψ) (m+[n∸m]≡n Ψ≤Ψ′) in
  Φ′ , trans lenΦ′ eq ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) eq hd′

sim-right-w01-down-casts-+ :
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
sim-right-w01-down-casts-+ zero w lenΦ hd hd′ =
  _ , lenΦ , wk⊒ w hd , wk⊒ w hd′
sim-right-w01-down-casts-+ (suc k) w lenΦ hd hd′
    with sim-right-w01-down-casts-+ k w lenΦ hd hd′
sim-right-w01-down-casts-+ (suc k) w lenΦ hd hd′
  | Φ′ , lenΦ′ , hdᵣ , hdᵣ′ =
  (Φ′ ++ cast-tag ∷ []) ,
  trans (length-append-tag Φ′) (cong suc lenΦ′) ,
  wkΨ-cast-tag-⊒ hdᵣ ,
  wkΨ-cast-tag-⊒ hdᵣ′

sim-right-w01-down-casts-≤ :
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
sim-right-w01-down-casts-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {A′ = A′} {B = B} {B′ = B′} {d = d} {d′ = d′}
  Ψ≤Ψ′ w lenΦ hd hd′
    with sim-right-w01-down-casts-+ (Ψ′ ∸ Ψ) w lenΦ hd hd′
sim-right-w01-down-casts-≤ {Δ} {Ψ} {Ψ′} {Σ′ = Σ′}
  {A = A} {A′ = A′} {B = B} {B′ = B′} {d = d} {d′ = d′}
  Ψ≤Ψ′ w lenΦ hd hd′
  | Φ′ , lenΦ′ , hdᵣ , hdᵣ′ =
  let eq = trans (+-comm (Ψ′ ∸ Ψ) Ψ) (m+[n∸m]≡n Ψ≤Ψ′) in
  Φ′ , trans lenΦ′ eq ,
  subst (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ d ⦂ A ⊒ B) eq hdᵣ ,
  subst
    (λ q → Δ ∣ q ∣ Σ′ ∣ Φ′ ⊢ d′ ⦂ A′ ⊒ B′)
    eq
    hdᵣ′

-- Supports SimRight.agda R26: lift recursive right simulations through a
-- left-only type application introduced by `⊑⦂∀-ν`.
sim-right-w01-tyappν-result :
  ∀ {Ψ Σ M N′ A B T}
    {pν : ν-bound ∷ [] ⊢ A ⊑ᵢ ⇑ᵗ B} →
  {pT : [] ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  WfTy 1 Ψ A →
  WfTy 0 Ψ T →
  νClosedInstᵢ pν pT →
  sim-right-w01-result Ψ Σ M N′ (⊑ᵢ-ν A B pν) →
  sim-right-w01-result Ψ Σ (M ⦂∀ A [ T ]) N′ pT
sim-right-w01-tyappν-result wfA hT closed
    (inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , rel)) =
  inj₁
    ( Ψ″
    , Ψ≤Ψ″
    , Σ′
    , N ⦂∀ _ [ _ ]
    , sim-right-w01-tyapp-↠ M↠N
    , ⊑⦂∀-ν _ _ _ rel (WfTy-weakenˢ wfA Ψ≤Ψ″)
        (WfTy-weakenˢ hT Ψ≤Ψ″) closed
    )
sim-right-w01-tyappν-result wfA hT closed (inj₂ (Σ′ , ℓ , M↠blame)) =
  inj₂ (Σ′ , ℓ , sim-right-w01-tyapp-blame-↠ M↠blame)

-- Supports SimRight.agda R26: lift recursive right simulations through a
-- left-only `up` wrapper.
sim-right-w01-upL-result :
  ∀ {Ψ Σ M N′ A A′ B}
    {pA : [] ⊢ A ⊑ᵢ A′} {pB : [] ⊢ B ⊑ᵢ A′} {Φ u} →
  length Φ ≡ Ψ →
  0 ∣ Ψ ∣ Σ ∣ Φ ⊢ u ⦂ A ⊑ B →
  sim-right-w01-result Ψ Σ M N′ pA →
  sim-right-w01-result Ψ Σ (M up u) N′ pB
sim-right-w01-upL-result lenΦ hu
    (inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , rel))
    with sim-right-w01-up-cast-≤ Ψ≤Ψ″
           (sim-right-w01-multi-store-growth M↠N) lenΦ hu
sim-right-w01-upL-result lenΦ hu
    (inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , rel))
  | Φ′ , lenΦ′ , hu′ =
  inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N up _ , up-↠ M↠N ,
        ⊑upL Φ′ lenΦ′ rel hu′)
sim-right-w01-upL-result lenΦ hu (inj₂ (Σ′ , ℓ , M↠blame)) =
  inj₂ (Σ′ , ℓ , sim-right-w01-up-blame-↠ M↠blame)

-- Supports SimRight.agda R26: lift recursive right simulations through a
-- left-only `down` wrapper.
sim-right-w01-downL-result :
  ∀ {Ψ Σ M N′ A A′ B}
    {pA : [] ⊢ A ⊑ᵢ A′} {pB : [] ⊢ B ⊑ᵢ A′} {Φ d} →
  length Φ ≡ Ψ →
  0 ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  sim-right-w01-result Ψ Σ M N′ pA →
  sim-right-w01-result Ψ Σ (M down d) N′ pB
sim-right-w01-downL-result lenΦ hd
    (inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , rel))
    with sim-right-w01-down-cast-≤ Ψ≤Ψ″
           (sim-right-w01-multi-store-growth M↠N) lenΦ hd
sim-right-w01-downL-result lenΦ hd
    (inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , rel))
  | Φ′ , lenΦ′ , hd′ =
  inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N down _ , down-↠ M↠N ,
        ⊑downL Φ′ lenΦ′ rel hd′)
sim-right-w01-downL-result lenΦ hd (inj₂ (Σ′ , ℓ , M↠blame)) =
  inj₂ (Σ′ , ℓ , sim-right-w01-down-blame-↠ M↠blame)

-- Supports SimRight.agda R26: rebuild a two-sided `down` relation after
-- recursively simulating the stepped right subterm.
sim-right-w01-down-result :
  ∀ {Ψ Σ M N′ A A′ B B′}
    {pA : [] ⊢ A ⊑ᵢ A′} {pB : [] ⊢ B ⊑ᵢ B′} {Φ d d′} →
  length Φ ≡ Ψ →
  0 ∣ Ψ ∣ Σ ∣ Φ ⊢ d ⦂ A ⊒ B →
  0 ∣ Ψ ∣ Σ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  sim-right-w01-result Ψ Σ M N′ pA →
  sim-right-w01-result Ψ Σ (M down d) (N′ down d′) pB
sim-right-w01-down-result lenΦ hd hd′
    (inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , rel))
    with sim-right-w01-down-casts-≤ Ψ≤Ψ″
           (sim-right-w01-multi-store-growth M↠N) lenΦ hd hd′
sim-right-w01-down-result lenΦ hd hd′
    (inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , rel))
  | Φ′ , lenΦ′ , hdᵣ , hdᵣ′ =
  inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N down _ , down-↠ M↠N ,
        ⊑down Φ′ lenΦ′ rel hdᵣ hdᵣ′)
sim-right-w01-down-result lenΦ hd hd′ (inj₂ (Σ′ , ℓ , M↠blame)) =
  inj₂ (Σ′ , ℓ , sim-right-w01-down-blame-↠ M↠blame)

-- Supports SimRight.agda R26: rebuild a right-only `down` relation after
-- recursively simulating the stepped right subterm.
sim-right-w01-downR-result :
  ∀ {Ψ Σ M N′ A A′ B′}
    {pA : [] ⊢ A ⊑ᵢ A′} {pB : [] ⊢ A ⊑ᵢ B′} {Φ d′} →
  length Φ ≡ Ψ →
  0 ∣ Ψ ∣ Σ ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  sim-right-w01-result Ψ Σ M N′ pA →
  sim-right-w01-result Ψ Σ M (N′ down d′) pB
sim-right-w01-downR-result lenΦ hd′
    (inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , rel))
    with sim-right-w01-down-cast-≤ Ψ≤Ψ″
           (sim-right-w01-multi-store-growth M↠N) lenΦ hd′
sim-right-w01-downR-result lenΦ hd′
    (inj₁ (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , rel))
  | Φ′ , lenΦ′ , hd″ =
  inj₁
    (Ψ″ , Ψ≤Ψ″ , Σ′ , N , M↠N , ⊑downR Φ′ lenΦ′ rel hd″)
sim-right-w01-downR-result lenΦ hd′ (inj₂ blames) = inj₂ blames

mutual
  -- Supports SimRight.agda R15: a right-side blame forces the left term to
  -- reach blame through any left-only wrappers.
  sim-right-w01-right-blame :
    ∀ {Ψ Σ M A B ℓ} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ blame ℓ ⦂ p →
    Σ[ Σ′ ∈ Store ] Σ[ ℓ′ ∈ Label ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ′)
  sim-right-w01-right-blame (⊑⦂∀-ν A B pν rel wfA hT closed) with
      sim-right-w01-right-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-tyapp-blame-↠ M↠blame
  sim-right-w01-right-blame (⊑upL Φ lenΦ rel hu) with
      sim-right-w01-right-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-up-blame-↠ M↠blame
  sim-right-w01-right-blame (⊑downL Φ lenΦ rel hd) with
      sim-right-w01-right-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-down-blame-↠ M↠blame
  sim-right-w01-right-blame (⊑blameR hM) = _ , _ , (blame _ ∎)

  -- Supports SimRight.agda R15: a right `blame down p` step is simulated by
  -- showing that the left term already reaches blame.
  sim-right-w01-right-down-blame :
    ∀ {Ψ Σ M A B ℓ d} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ (blame ℓ down d) ⦂ p →
    Σ[ Σ′ ∈ Store ] Σ[ ℓ′ ∈ Label ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ′)
  sim-right-w01-right-down-blame (⊑⦂∀-ν A B pν rel wfA hT closed) with
      sim-right-w01-right-down-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-tyapp-blame-↠ M↠blame
  sim-right-w01-right-down-blame (⊑upL Φ lenΦ rel hu) with
      sim-right-w01-right-down-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-up-blame-↠ M↠blame
  sim-right-w01-right-down-blame (⊑down Φ lenΦ rel hd hd′) with
      sim-right-w01-right-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-down-blame-↠ M↠blame
  sim-right-w01-right-down-blame (⊑downL Φ lenΦ rel hd) with
      sim-right-w01-right-down-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-down-blame-↠ M↠blame
  sim-right-w01-right-down-blame (⊑downR Φ lenΦ rel hd′) =
    sim-right-w01-right-blame rel
  sim-right-w01-right-down-blame (⊑blameR hM) = _ , _ , (blame _ ∎)

-- Worker W02 helper slot

-- Worker W03 helper slot

-- Worker W04 helper slot

-- Worker W05 helper slot

-- Worker W06 helper slot

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot
