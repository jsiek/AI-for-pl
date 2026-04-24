module Parametricity where

-- File Charter:
--   * Decomposes the fundamental theorem into compatibility lemmas,
--   * following the style used in `SystemF/agda/extrinsic/Parametricity.agda`.
--   * Provides a recursive proof skeleton of `fundamental` by induction on
--   * term precision derivations.
--   * Keeps hard compatibility cases as explicit proof holes for now, while
--   * exposing the final theorem with the intended interface.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat
  using (ℕ; zero; suc; _<′_; <′-base; ≤′-reflexive; ≤′-step)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Types
open import TypeProperties using (substᵗ-preserves-WfTy)
open import Store using (_⊆ˢ_; ⊆ˢ-refl; ⊆ˢ-trans)
open import Imprecision
open import UpDown
open import Terms
open import Data.Product using (_,_; proj₁; proj₂)
open import TermPrecision
open import TermProperties
  using
    ( Substˣ-wt
    ; Substˣ
    ; extˣ
    ; extˣ-wt
    ; extˣ-sub-cons
    ; wkʳ
    ; _•ˣ_
    ; _[_]
    ; singleVarEnv
    ; substˣ-term
    ; substˣ-term-cong
    ; substˣ-term-wt
    ; renameˣᵐ-substᵗᵐ-commute
    ; substᵗᵐ-substˣ-term-commute
    ; substᵗᵐ-substˣ-term-commute-gen
    ; substᵗᵐ-id-emptyΔ
    )
open import ReductionFresh
  using
    ( Value
    ; _∣_—↠_∣_
    ; _∎
    ; _—→⟨_⟩_
    ; id-step
    ; β
    ; ξ-·₁
    ; ξ-·₂
    ; blame-·₁
    ; blame-·₂
    ; store-growth
    )
  renaming ($ to v$; ƛ_⇒_ to vƛ_⇒_)
open import LogicalRelationAlt

𝒢-lookup :
  ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  𝒢 Γ (suc n) dir w ρ γ →
  𝒱 (substᴿ-⊑ ρ p) n dir w (leftˣ γ x) (rightˣ γ x)
𝒢-lookup {A = A} {B = B} {p = p} Zₚ
  (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒱-monotone _ _ (substᴿ-⊑ _ p) _ _ _ _ _ rel
𝒢-lookup (Sₚ x∈) (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒢-lookup x∈ env

𝒢-left-typed :
  ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  𝒢 Γ n dir w ρ γ →
  0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ leftˣ γ x ⦂ substᵗ (leftᵗ ρ) A
𝒢-left-typed Zₚ
  (vˡ , vʳ , (vV , vW , (V⊢ , W⊢) , payload) , lclosed , rclosed , env) = V⊢
𝒢-left-typed (Sₚ x∈) (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒢-left-typed x∈ env

𝒢-right-typed :
  ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  𝒢 Γ n dir w ρ γ →
  0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ rightˣ γ x ⦂ substᵗ (rightᵗ ρ) B
𝒢-right-typed Zₚ
  (vˡ , vʳ , (vV , vW , (V⊢ , W⊢) , payload) , lclosed , rclosed , env) = W⊢
𝒢-right-typed (Sₚ x∈) (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒢-right-typed x∈ env

𝒢-left-Substˣ-wt :
  ∀ {Γ n dir w} {ρ : RelSub 0} {γ} →
  𝒢 Γ n dir w ρ γ →
  Substˣ-wt {0} {Ψ w} {Σˡ w}
    {map (substᵗ (leftᵗ ρ)) (leftCtx Γ)} {[]}
    (λ x → substᵗᵐ (leftᵗ ρ) (leftˣ γ x))
𝒢-left-Substˣ-wt {Γ = []} env ()
𝒢-left-Substˣ-wt {Γ = (A , B , p) ∷ Γ}
  (vˡ , vʳ , (vV , vW , (V⊢ , W⊢) , payload) ,
   lclosed , rclosed , env)
  Z =
  cong-⊢⦂ refl refl (sym lclosed) refl V⊢
𝒢-left-Substˣ-wt {Γ = (A , B , p) ∷ Γ}
  (vˡ , vʳ , rel , lclosed , rclosed , env)
  (S x∈) =
  𝒢-left-Substˣ-wt env x∈

𝒢-right-Substˣ-wt :
  ∀ {Γ n dir w} {ρ : RelSub 0} {γ} →
  𝒢 Γ n dir w ρ γ →
  Substˣ-wt {0} {Ψ w} {Σʳ w}
    {map (substᵗ (rightᵗ ρ)) (rightCtx Γ)} {[]}
    (λ x → substᵗᵐ (rightᵗ ρ) (rightˣ γ x))
𝒢-right-Substˣ-wt {Γ = []} env ()
𝒢-right-Substˣ-wt {Γ = (A , B , p) ∷ Γ}
  (vˡ , vʳ , (vV , vW , (V⊢ , W⊢) , payload) ,
   lclosed , rclosed , env)
  Z =
  cong-⊢⦂ refl refl (sym rclosed) refl W⊢
𝒢-right-Substˣ-wt {Γ = (A , B , p) ∷ Γ}
  (vˡ , vʳ , rel , lclosed , rclosed , env)
  (S x∈) =
  𝒢-right-Substˣ-wt env x∈

𝒢-lookup-substᵗ :
  ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  𝒢 Γ (suc n) dir w ρ γ →
  𝒱 (substᴿ-⊑ ρ p) n dir w
    (substᵗᵐ (leftᵗ ρ) (leftˣ γ x))
    (substᵗᵐ (rightᵗ ρ) (rightˣ γ x))
𝒢-lookup-substᵗ {p = p} Zₚ
  (vˡ , vʳ , rel , lclosed , rclosed , env)
  rewrite lclosed | rclosed =
  𝒱-monotone _ _ (substᴿ-⊑ _ p) _ _ _ _ _ rel
𝒢-lookup-substᵗ (Sₚ x∈) (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒢-lookup-substᵗ x∈ env

const-𝒱 :
  ∀ {n dir w m} →
  𝒱 (⊑-‵ `ℕ) n dir w ($ (κℕ m)) ($ (κℕ m))
const-𝒱 {n = zero} = v$ _ , v$ _ , (⊢$ _ , ⊢$ _) , lift refl
const-𝒱 {n = suc n} = v$ _ , v$ _ , (⊢$ _ , ⊢$ _) , lift refl

𝒱⇒ℰ :
  ∀ {A B} {p : A ⊑ B} {n dir w V W} →
  𝒱 p n dir w V W →
  ℰ p (suc n) dir w V W
𝒱⇒ℰ {p = p} {n = n} {dir = ≼} {w = w} {V = V} {W = W}
  (vV , vW , (V⊢ , W⊢) , payload) =
  (V⊢ , W⊢) ,
  inj₂ (inj₂ (vV , Σʳ w , wfΣʳ w , W , (W ∎) ,
    𝒱-⪰ {n = n} {dir = ≼} p (mkWorldʳ-⪰ ⊆ˢ-refl)
      (vV , vW , (V⊢ , W⊢) , payload)))
𝒱⇒ℰ {p = p} {n = n} {dir = ≽} {w = w} {V = V} {W = W}
  (vV , vW , (V⊢ , W⊢) , payload) =
  (V⊢ , W⊢) ,
  inj₂ (inj₂ (vW , Σˡ w , wfΣˡ w , V , (V ∎) ,
    𝒱-⪰ {n = n} {dir = ≽} p (mkWorldˡ-⪰ ⊆ˢ-refl)
      (vV , vW , (V⊢ , W⊢) , payload)))

𝒱⇒ℰ-zero :
  ∀ {A B} {p : A ⊑ B} {dir w V W} →
  𝒱 p zero dir w V W →
  ℰ p zero dir w V W
𝒱⇒ℰ-zero (vV , vW , (V⊢ , W⊢) , payload) =
  (V⊢ , W⊢) , lift tt

close-left-body-typed :
  ∀ {E A B M n dir w} {ρ : RelSub 0} {γ} →
  RelWf E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣
    (A ∷ leftCtx (TPEnv.Γ E)) ⊢ M ⦂ B →
  0 ∣ Ψ w ∣ Σˡ w ∣ (substᵗ (leftᵗ ρ) A ∷ []) ⊢
    substᵗᵐ (leftᵗ ρ) (substˣ-term (extˣ (leftˣ γ)) M) ⦂
    substᵗ (leftᵗ ρ) B
close-left-body-typed {M = M} {ρ = ρ} {γ = γ} rwf env M⊢
  rewrite Ψ≡ rwf =
  cong-⊢⦂ refl refl
    (sym
      (substᵗᵐ-substˣ-term-commute-gen
        (leftᵗ ρ)
        (extˣ (leftˣ γ))
        (extˣ (λ x → substᵗᵐ (leftᵗ ρ) (leftˣ γ x)))
        (λ { zero → refl
           ; (suc x) →
               renameˣᵐ-substᵗᵐ-commute wkʳ (leftᵗ ρ) (leftˣ γ x)
           })
        M))
    refl
    (substˣ-term-wt
      (extˣ (λ x → substᵗᵐ (leftᵗ ρ) (leftˣ γ x)))
      (extˣ-wt _ (𝒢-left-Substˣ-wt env))
      (wkΣ-term (storeˡ rwf)
        (substᵗ-wt (leftᵗ ρ) (leftᵗ-wf rwf) M⊢)))

close-right-body-typed :
  ∀ {E A B M n dir w} {ρ : RelSub 0} {γ} →
  RelWf E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣
    (A ∷ rightCtx (TPEnv.Γ E)) ⊢ M ⦂ B →
  0 ∣ Ψ w ∣ Σʳ w ∣ (substᵗ (rightᵗ ρ) A ∷ []) ⊢
    substᵗᵐ (rightᵗ ρ) (substˣ-term (extˣ (rightˣ γ)) M) ⦂
    substᵗ (rightᵗ ρ) B
close-right-body-typed {M = M} {ρ = ρ} {γ = γ} rwf env M⊢
  rewrite Ψ≡ rwf =
  cong-⊢⦂ refl refl
    (sym
      (substᵗᵐ-substˣ-term-commute-gen
        (rightᵗ ρ)
        (extˣ (rightˣ γ))
        (extˣ (λ x → substᵗᵐ (rightᵗ ρ) (rightˣ γ x)))
        (λ { zero → refl
           ; (suc x) →
               renameˣᵐ-substᵗᵐ-commute wkʳ (rightᵗ ρ) (rightˣ γ x)
           })
        M))
    refl
    (substˣ-term-wt
      (extˣ (λ x → substᵗᵐ (rightᵗ ρ) (rightˣ γ x)))
      (extˣ-wt _ (𝒢-right-Substˣ-wt env))
      (wkΣ-term (storeʳ rwf)
        (substᵗ-wt (rightᵗ ρ) (rightᵗ-wf rwf) M⊢)))

𝒢-lookup-substᵗ-current :
  ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  𝒢 Γ n dir w ρ γ →
  𝒱 (substᴿ-⊑ ρ p) n dir w
    (substᵗᵐ (leftᵗ ρ) (leftˣ γ x))
    (substᵗᵐ (rightᵗ ρ) (rightˣ γ x))
𝒢-lookup-substᵗ-current Zₚ
  (vˡ , vʳ , rel , lclosed , rclosed , env)
  rewrite lclosed | rclosed = rel
𝒢-lookup-substᵗ-current (Sₚ x∈)
  (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒢-lookup-substᵗ-current x∈ env

extendγ : RelEnv → Term → Term → RelEnv
(extendγ γ V W .leftˣ) = V •ˣ leftˣ γ
(extendγ γ V W .rightˣ) = W •ˣ rightˣ γ

𝒢-monotone :
  ∀ {Γ n dir w} {ρ : RelSub 0} {γ} →
  𝒢 Γ (suc n) dir w ρ γ →
  𝒢 Γ n dir w ρ γ
𝒢-monotone {Γ = []} env = lift tt
𝒢-monotone {Γ = (A , B , p) ∷ Γ} {n = n} {dir = dir} {w = w}
  {ρ = ρ} {γ = γ}
  (vˡ , vʳ , rel , lclosed , rclosed , env) =
  vˡ , vʳ ,
  𝒱-monotone _ _ (substᴿ-⊑ ρ p) n dir w _ _ rel ,
  lclosed , rclosed , 𝒢-monotone env

𝒢-lower :
  ∀ {Γ n j dir w} {ρ : RelSub 0} {γ} →
  j <′ n →
  𝒢 Γ n dir w ρ γ →
  𝒢 Γ j dir w ρ γ
𝒢-lower {n = zero} (≤′-reflexive ())
𝒢-lower {n = suc n} <′-base env = 𝒢-monotone env
𝒢-lower {n = suc n} (≤′-step j<n) env =
  𝒢-lower j<n (𝒢-monotone env)

𝒢-⪰ :
  ∀ {Γ n dir w w′ ρ γ} →
  w′ ⪰ w →
  𝒢 Γ n dir w ρ γ →
  𝒢 Γ n dir w′ ρ γ
𝒢-⪰ {Γ = []} w′⪰ env = lift tt
𝒢-⪰ {Γ = (A , B , p) ∷ Γ} {n = n} {dir = dir} {ρ = ρ} w′⪰
  (vˡ , vʳ , rel , lclosed , rclosed , env) =
  vˡ , vʳ , 𝒱-⪰ {n = n} {dir = dir} (substᴿ-⊑ ρ p) w′⪰ rel ,
  lclosed , rclosed , 𝒢-⪰ {n = n} {dir = dir} w′⪰ env

singleVarEnv-close :
  (τ : Substᵗ) (V : Term) →
  substᵗᵐ τ V ≡ V →
  (x : Var) → singleVarEnv V x ≡ substᵗᵐ τ (singleVarEnv V x)
singleVarEnv-close τ V closed zero = sym closed
singleVarEnv-close τ V closed (suc x) = refl

β-subst-bridge :
  (τ : Substᵗ) (σ : Substˣ) (M V : Term) →
  substᵗᵐ τ V ≡ V →
  (substᵗᵐ τ (substˣ-term (extˣ σ) M)) [ V ] ≡
  substᵗᵐ τ (substˣ-term (V •ˣ σ) M)
β-subst-bridge τ σ M V closed =
  trans
    (substˣ-term-cong (singleVarEnv-close τ V closed)
      (substᵗᵐ τ (substˣ-term (extˣ σ) M)))
    (trans
      (sym
        (substᵗᵐ-substˣ-term-commute τ (singleVarEnv V)
          (substˣ-term (extˣ σ) M)))
      (cong (substᵗᵐ τ) (extˣ-sub-cons σ M V)))

multi-store-growth :
  ∀ {Σ Σ′ M N} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ⊆ˢ Σ′
multi-store-growth (_ ∎) = ⊆ˢ-refl
multi-store-growth (_ —→⟨ M→N ⟩ N↠V) =
  ⊆ˢ-trans (store-growth M→N) (multi-store-growth N↠V)

appL-blame-↠ :
  ∀ {Σ Σ′ L M ℓ} →
  Σ ∣ L —↠ Σ′ ∣ blame ℓ →
  Σ ∣ L · M —↠ Σ′ ∣ blame ℓ
appL-blame-↠ {M = M} {ℓ = ℓ} (_ ∎) =
  (blame ℓ · M) —→⟨ id-step blame-·₁ ⟩ blame ℓ ∎
appL-blame-↠ {M = M} (L —→⟨ L→L′ ⟩ L′↠blame) =
  (L · M) —→⟨ ξ-·₁ L→L′ ⟩ appL-blame-↠ L′↠blame

appL-↠ :
  ∀ {Σ Σ′ L L′ M} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ∣ L · M —↠ Σ′ ∣ L′ · M
appL-↠ {M = M} (L ∎) = (L · M) ∎
appL-↠ {M = M} (L —→⟨ L→L′ ⟩ L′↠W) =
  (L · M) —→⟨ ξ-·₁ L→L′ ⟩ appL-↠ L′↠W

appR-blame-↠ :
  ∀ {Σ Σ′ V M ℓ} →
  Value V →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ V · M —↠ Σ′ ∣ blame ℓ
appR-blame-↠ {V = V} {ℓ = ℓ} vV (_ ∎) =
  (V · blame ℓ) —→⟨ id-step (blame-·₂ vV) ⟩ blame ℓ ∎
appR-blame-↠ {V = V} vV (M —→⟨ M→M′ ⟩ M′↠blame) =
  (V · M) —→⟨ ξ-·₂ vV M→M′ ⟩ appR-blame-↠ vV M′↠blame

appR-↠ :
  ∀ {Σ Σ′ V M M′} →
  Value V →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ V · M —↠ Σ′ ∣ V · M′
appR-↠ {V = V} vV (M ∎) = (V · M) ∎
appR-↠ {V = V} vV (M —→⟨ M→M′ ⟩ M′↠W) =
  (V · M) —→⟨ ξ-·₂ vV M→M′ ⟩ appR-↠ vV M′↠W

compat-var :
  ∀ {E dir x A B} {p : A ⊑ B} →
  TPEnv.Γ E ∋ₚ x ⦂ (A , B , p) →
  E ∣ dir ⊨ (` x) ⊑ (` x) ⦂ p
compat-var {dir = dir} {p = p} x∈ zero w ρ γ rwf env =
  𝒱⇒ℰ-zero {p = substᴿ-⊑ ρ p} {dir = dir} {w = w}
    (𝒢-lookup-substᵗ-current {p = p} {n = zero} {dir = dir}
      {w = w} {ρ = ρ} {γ = γ} x∈ env)
compat-var {dir = dir} {p = p} x∈ (suc n) w ρ γ rwf env =
  𝒱⇒ℰ {p = substᴿ-⊑ ρ p} {n = n} {dir = dir} {w = w}
    (𝒢-lookup-substᵗ {p = p} {n = n} {dir = dir}
      {w = w} {ρ = ρ} {γ = γ} x∈ env)

compat-$ :
  ∀ {E dir n} →
  E ∣ dir ⊨ ($ (κℕ n)) ⊑ ($ (κℕ n)) ⦂ (⊑-‵ `ℕ)
compat-$ {dir = dir} {n = m} zero w ρ γ rwf env =
  𝒱⇒ℰ-zero {p = ⊑-‵ `ℕ} {dir = dir} {w = w}
    (const-𝒱 {n = zero} {dir = dir} {w = w} {m = m})
compat-$ {dir = dir} {n = m} (suc n) w ρ γ rwf env =
  𝒱⇒ℰ {p = ⊑-‵ `ℕ} {n = n} {dir = dir} {w = w}
    (const-𝒱 {n = n} {dir = dir} {w = w} {m = m})

compat-ƛ :
  ∀ {E dir A A′ B B′ M M′} {pA : A ⊑ A′} {pB : B ⊑ B′} →
  WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A →
  WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A′ →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣
    (A ∷ leftCtx (TPEnv.Γ E)) ⊢ M ⦂ B →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣
    (A′ ∷ rightCtx (TPEnv.Γ E)) ⊢ M′ ⦂ B′ →
  extendᴾ E (A , A′ , pA) ∣ dir ⊨ M ⊑ M′ ⦂ pB →
  E ∣ dir ⊨ (ƛ A ⇒ M) ⊑ (ƛ A′ ⇒ M′) ⦂ (⊑-⇒ A A′ B B′ pA pB)
compat-ƛ {E = E} {dir = dir} {A = A} {A′ = A′} {B = B} {B′ = B′}
  {M = M} {M′ = M′} {pA = pA} {pB = pB} hA hA′ M⊢ M′⊢ M-rel
  zero w ρ γ rwf env =
  𝒱⇒ℰ-zero {p = substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ pA pB)}
    {dir = dir} {w = w}
    lambda-𝒱-zero
  where
  L : Term
  L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (ƛ A ⇒ M))

  R : Term
  R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) (ƛ A′ ⇒ M′))

  left-typed :
    0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA (Ψ≤ rwf)) (leftᵗ-wf rwf))
    (close-left-body-typed rwf env M⊢)

  right-typed :
    0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA′ (Ψ≤ rwf)) (rightᵗ-wf rwf))
    (close-right-body-typed rwf env M′⊢)

  lambda-𝒱-zero :
    𝒱 (substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ pA pB)) zero dir w L R
  lambda-𝒱-zero =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) , lift tt
compat-ƛ {E = E} {dir = ≼} {A = A} {A′ = A′} {B = B} {B′ = B′}
  {M = M} {M′ = M′} {pA = pA} {pB = pB} hA hA′ M⊢ M′⊢ M-rel
  (suc n) w ρ γ rwf env =
  𝒱⇒ℰ {p = substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ pA pB)} {n = n}
    {dir = ≼} {w = w}
    (lambda-𝒱 n env)
  where
  L : Term
  L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (ƛ A ⇒ M))

  R : Term
  R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) (ƛ A′ ⇒ M′))

  left-typed :
    0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA (Ψ≤ rwf)) (leftᵗ-wf rwf))
    (close-left-body-typed rwf env M⊢)

  right-typed :
    0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA′ (Ψ≤ rwf)) (rightᵗ-wf rwf))
    (close-right-body-typed rwf env M′⊢)

  left-typed′ :
    ∀ {w′} →
    w′ ⪰ w →
    0 ∣ Ψ w′ ∣ Σˡ w′ ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed′ w′⪰ = wk⪰ˡ w′⪰ left-typed

  right-typed′ :
    ∀ {w′} →
    w′ ⪰ w →
    0 ∣ Ψ w′ ∣ Σʳ w′ ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed′ w′⪰ = wk⪰ʳ w′⪰ right-typed

  lambda-𝒱 :
    (m : ℕ) →
    𝒢 (TPEnv.Γ E) (suc m) ≼ w ρ γ →
    𝒱 (substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ pA pB)) m ≼ w L R
  lambda-𝒱 zero env′ =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) , lift tt
  lambda-𝒱 (suc k) env′ =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) ,
      FunAll→𝒱′ (λ {w′} w′⪰ → λ
        { zero j<suc {V′ = V′} {W′ = W′} arg-rel →
            app-zero w′⪰ arg-rel
        ; (suc j) j<suc {V′ = V′} {W′ = W′} arg-rel →
            app-suc w′⪰ j<suc arg-rel
        }
      )
    where
    app-zero :
      ∀ {w′ V′ W′} →
      w′ ⪰ w →
      𝒱 (substᴿ-⊑ ρ pA) zero ≼ w′ V′ W′ →
      ℰ (substᴿ-⊑ ρ pB) zero ≼ w′ (L · V′) (R · W′)
    app-zero w′⪰ (vV′ , vW′ , (V′⊢ , W′⊢) , payload) =
      (⊢· (left-typed′ w′⪰) V′⊢ ,
       ⊢· (right-typed′ w′⪰) W′⊢) ,
      lift tt

    app-suc :
      ∀ {w′ j V′ W′} →
      w′ ⪰ w →
      suc j <′ suc k →
      𝒱 (substᴿ-⊑ ρ pA) (suc j) ≼ w′ V′ W′ →
      ℰ (substᴿ-⊑ ρ pB) (suc j) ≼ w′ (L · V′) (R · W′)
    app-suc {w′ = w′} {j = j} {V′ = V′} {W′ = W′} w′⪰ j<suc
      (vV′ , vW′ , (V′⊢ , W′⊢) , payload) =
      ℰ-expand-≼-left
        {p = substᴿ-⊑ ρ pB} {k = j} {w = w′}
        {Mˡ = L · V′} {Mˡ′ = Lβ} {Mʳ = R · W′}
        (⊢· (left-typed′ w′⪰) V′⊢)
        (⊢· (right-typed′ w′⪰) W′⊢)
        (id-step (β vV′))
        (ℰ-expand-≼-right
          {p = substᴿ-⊑ ρ pB} {k = j} {w = w′}
          {Mˡ = Lβ} {Mʳ = R · W′} {Mʳ′ = Rβ}
          (proj₁ (proj₁ body-beta-j))
          (⊢· (right-typed′ w′⪰) W′⊢)
          (id-step (β vW′))
          body-beta-j)
      where
      Lβ : Term
      Lβ =
        (substᵗᵐ (leftᵗ ρ) (substˣ-term (extˣ (leftˣ γ)) M)) [ V′ ]

      Rβ : Term
      Rβ =
        (substᵗᵐ (rightᵗ ρ) (substˣ-term (extˣ (rightˣ γ)) M′)) [ W′ ]

      V′-closed : substᵗᵐ (leftᵗ ρ) V′ ≡ V′
      V′-closed = substᵗᵐ-id-emptyΔ V′⊢

      W′-closed : substᵗᵐ (rightᵗ ρ) W′ ≡ W′
      W′-closed = substᵗᵐ-id-emptyΔ W′⊢

      body-rel :
        ℰ (substᴿ-⊑ ρ pB) (suc j) ≼ w′
          (substᵗᵐ (leftᵗ ρ) (substˣ-term (V′ •ˣ leftˣ γ) M))
          (substᵗᵐ (rightᵗ ρ) (substˣ-term (W′ •ˣ rightˣ γ) M′))
      body-rel =
        M-rel (suc j) w′ ρ (extendγ γ V′ W′)
          (RelWf-extend (RelWf-⪰ w′⪰ rwf))
          (vV′ , vW′ , (vV′ , vW′ , (V′⊢ , W′⊢) , payload) ,
           V′-closed , W′-closed ,
           𝒢-lower (≤′-step j<suc) (𝒢-⪰ w′⪰ env′))

      body-beta-suc :
        ℰ (substᴿ-⊑ ρ pB) (suc j) ≼ w′ Lβ Rβ
      body-beta-suc
        rewrite β-subst-bridge (leftᵗ ρ) (leftˣ γ) M V′ V′-closed
              | β-subst-bridge (rightᵗ ρ) (rightˣ γ) M′ W′ W′-closed =
        body-rel

      body-beta-j :
        ℰ (substᴿ-⊑ ρ pB) j ≼ w′ Lβ Rβ
      body-beta-j =
        ℰ-monotone _ _ (substᴿ-⊑ ρ pB) j ≼ w′ _ _ body-beta-suc

compat-ƛ {E = E} {dir = ≽} {A = A} {A′ = A′} {B = B} {B′ = B′}
  {M = M} {M′ = M′} {pA = pA} {pB = pB} hA hA′ M⊢ M′⊢ M-rel
  (suc n) w ρ γ rwf env =
  𝒱⇒ℰ {p = substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ pA pB)} {n = n}
    {dir = ≽} {w = w}
    (lambda-𝒱 n env)
  where
  L : Term
  L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (ƛ A ⇒ M))

  R : Term
  R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) (ƛ A′ ⇒ M′))

  left-typed :
    0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA (Ψ≤ rwf)) (leftᵗ-wf rwf))
    (close-left-body-typed rwf env M⊢)

  right-typed :
    0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA′ (Ψ≤ rwf)) (rightᵗ-wf rwf))
    (close-right-body-typed rwf env M′⊢)

  left-typed′ :
    ∀ {w′} →
    w′ ⪰ w →
    0 ∣ Ψ w′ ∣ Σˡ w′ ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed′ w′⪰ = wk⪰ˡ w′⪰ left-typed

  right-typed′ :
    ∀ {w′} →
    w′ ⪰ w →
    0 ∣ Ψ w′ ∣ Σʳ w′ ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed′ w′⪰ = wk⪰ʳ w′⪰ right-typed

  lambda-𝒱 :
    (m : ℕ) →
    𝒢 (TPEnv.Γ E) (suc m) ≽ w ρ γ →
    𝒱 (substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ pA pB)) m ≽ w L R
  lambda-𝒱 zero env′ =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) , lift tt
  lambda-𝒱 (suc k) env′ =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) ,
      FunAll→𝒱′ (λ {w′} w′⪰ → λ
        { zero j<suc {V′ = V′} {W′ = W′} arg-rel →
            app-zero w′⪰ arg-rel
        ; (suc j) j<suc {V′ = V′} {W′ = W′} arg-rel →
            app-suc w′⪰ j<suc arg-rel
        }
      )
    where
    app-zero :
      ∀ {w′ V′ W′} →
      w′ ⪰ w →
      𝒱 (substᴿ-⊑ ρ pA) zero ≽ w′ V′ W′ →
      ℰ (substᴿ-⊑ ρ pB) zero ≽ w′ (L · V′) (R · W′)
    app-zero w′⪰ (vV′ , vW′ , (V′⊢ , W′⊢) , payload) =
      (⊢· (left-typed′ w′⪰) V′⊢ ,
       ⊢· (right-typed′ w′⪰) W′⊢) ,
      lift tt

    app-suc :
      ∀ {w′ j V′ W′} →
      w′ ⪰ w →
      suc j <′ suc k →
      𝒱 (substᴿ-⊑ ρ pA) (suc j) ≽ w′ V′ W′ →
      ℰ (substᴿ-⊑ ρ pB) (suc j) ≽ w′ (L · V′) (R · W′)
    app-suc {w′ = w′} {j = j} {V′ = V′} {W′ = W′} w′⪰ j<suc
      (vV′ , vW′ , (V′⊢ , W′⊢) , payload) =
      ℰ-expand-≽-right
        {p = substᴿ-⊑ ρ pB} {k = j} {w = w′}
        {Mˡ = L · V′} {Mʳ = R · W′} {Mʳ′ = Rβ}
        (⊢· (left-typed′ w′⪰) V′⊢)
        (⊢· (right-typed′ w′⪰) W′⊢)
        (id-step (β vW′))
        (ℰ-expand-≽-left
          {p = substᴿ-⊑ ρ pB} {k = j} {w = w′}
          {Mˡ = L · V′} {Mˡ′ = Lβ} {Mʳ = Rβ}
          (⊢· (left-typed′ w′⪰) V′⊢)
          (proj₂ (proj₁ body-beta-j))
          (id-step (β vV′))
          body-beta-j)
      where
      Lβ : Term
      Lβ =
        (substᵗᵐ (leftᵗ ρ) (substˣ-term (extˣ (leftˣ γ)) M)) [ V′ ]

      Rβ : Term
      Rβ =
        (substᵗᵐ (rightᵗ ρ) (substˣ-term (extˣ (rightˣ γ)) M′)) [ W′ ]

      V′-closed : substᵗᵐ (leftᵗ ρ) V′ ≡ V′
      V′-closed = substᵗᵐ-id-emptyΔ V′⊢

      W′-closed : substᵗᵐ (rightᵗ ρ) W′ ≡ W′
      W′-closed = substᵗᵐ-id-emptyΔ W′⊢

      body-rel :
        ℰ (substᴿ-⊑ ρ pB) (suc j) ≽ w′
          (substᵗᵐ (leftᵗ ρ) (substˣ-term (V′ •ˣ leftˣ γ) M))
          (substᵗᵐ (rightᵗ ρ) (substˣ-term (W′ •ˣ rightˣ γ) M′))
      body-rel =
        M-rel (suc j) w′ ρ (extendγ γ V′ W′)
          (RelWf-extend (RelWf-⪰ w′⪰ rwf))
          (vV′ , vW′ , (vV′ , vW′ , (V′⊢ , W′⊢) , payload) ,
           V′-closed , W′-closed ,
           𝒢-lower (≤′-step j<suc) (𝒢-⪰ w′⪰ env′))

      body-beta-suc :
        ℰ (substᴿ-⊑ ρ pB) (suc j) ≽ w′ Lβ Rβ
      body-beta-suc
        rewrite β-subst-bridge (leftᵗ ρ) (leftˣ γ) M V′ V′-closed
              | β-subst-bridge (rightᵗ ρ) (rightˣ γ) M′ W′ W′-closed =
        body-rel

      body-beta-j :
        ℰ (substᴿ-⊑ ρ pB) j ≽ w′ Lβ Rβ
      body-beta-j =
        ℰ-monotone _ _ (substᴿ-⊑ ρ pB) j ≽ w′ _ _ body-beta-suc
compat-· :
  ∀ {E dir A A′ B B′ L L′ M M′} {pA : A ⊑ A′} {pB : B ⊑ B′} →
  E ∣ dir ⊨ L ⊑ L′ ⦂ (⊑-⇒ A A′ B B′ pA pB) →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  E ∣ dir ⊨ (L · M) ⊑ (L′ · M′) ⦂ pB
compat-· L-rel M-rel zero w ρ γ rwf env =
  (⊢· (proj₁ (proj₁ Lℰ)) (proj₁ (proj₁ Mℰ)) ,
   ⊢· (proj₂ (proj₁ Lℰ)) (proj₂ (proj₁ Mℰ))) ,
  lift tt
  where
  Lℰ = L-rel zero w ρ γ rwf env
  Mℰ = M-rel zero w ρ γ rwf env
compat-· L-rel M-rel (suc k) w ρ γ rwf env = {!!}

compat-Λ :
  ∀ {E dir A B M M′} {p : A ⊑ B} →
  ⇑ᵗᴱ E ∣ dir ⊨ M ⊑ M′ ⦂ p →
  E ∣ dir ⊨ (Λ M) ⊑ (Λ M′) ⦂ (⊑-∀ A B p)
compat-Λ M-rel n w ρ γ rwf env = {!!}

compat-⦂∀ :
  ∀ {E dir A B M M′ T} {p : A ⊑ B} →
  E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑-∀ A B p) →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
  WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T →
  E ∣ dir ⊨ (M ⦂∀ A [ T ]) ⊑ (M′ ⦂∀ B [ T ]) ⦂
    substᵗ-⊑ (singleTyEnv T) p
compat-⦂∀ M-rel wfA wfB hT n w ρ γ rwf env = {!!}

compat-⦂∀-ν :
  ∀ (A B : Ty) {E dir M M′ T} (p : ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B)) →
  E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑-ν A B p) →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
  (hT : WfTy 0 (TPEnv.Ψ E) T) →
  E ∣ dir ⊨ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ ν-inst-⊑ A B T hT p
compat-⦂∀-ν A B p M-rel wfA hT n w ρ γ rwf env = {!!}

compat-⊕ :
  ∀ {E dir L L′ M M′} {op : Prim} →
  E ∣ dir ⊨ L ⊑ L′ ⦂ (⊑-‵ `ℕ) →
  E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑-‵ `ℕ) →
  E ∣ dir ⊨ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′) ⦂ (⊑-‵ `ℕ)
compat-⊕ L-rel M-rel n w ρ γ rwf env = {!!}

compat-up :
  ∀ {E dir M M′ A A′ B B′}
    {pA : A ⊑ A′} {pB : B ⊑ B′} {u : Up} {u′ : Up} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  E ∣ dir ⊨ (M up u) ⊑ (M′ up u′) ⦂ pB
compat-up Φ lenΦ M-rel u⊢ u′⊢ n w ρ γ rwf env = {!!}

compat-upL :
  ∀ {E dir M M′ A A′ B} {pA : A ⊑ A′} {pB : B ⊑ A′} {u : Up} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
  E ∣ dir ⊨ (M up u) ⊑ M′ ⦂ pB
compat-upL Φ lenΦ M-rel u⊢ n w ρ γ rwf env = {!!}

compat-upR :
  ∀ {E dir M M′ A A′ B′} {pA : A ⊑ A′} {pB : A ⊑ B′} {u′ : Up} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  E ∣ dir ⊨ M ⊑ (M′ up u′) ⦂ pB
compat-upR Φ lenΦ M-rel u′⊢ n w ρ γ rwf env = {!!}

compat-down :
  ∀ {E dir M M′ A A′ B B′}
    {pA : A ⊑ A′} {pB : B ⊑ B′} {d : Down} {d′ : Down} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  E ∣ dir ⊨ (M down d) ⊑ (M′ down d′) ⦂ pB
compat-down Φ lenΦ M-rel d⊢ d′⊢ n w ρ γ rwf env = {!!}

compat-downL :
  ∀ {E dir M M′ A A′ B} {pA : A ⊑ A′} {pB : B ⊑ A′} {d : Down} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
  E ∣ dir ⊨ (M down d) ⊑ M′ ⦂ pB
compat-downL Φ lenΦ M-rel d⊢ n w ρ γ rwf env = {!!}

compat-downR :
  ∀ {E dir M M′ A A′ B′} {pA : A ⊑ A′} {pB : A ⊑ B′} {d′ : Down} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  E ∣ dir ⊨ M ⊑ (M′ down d′) ⦂ pB
compat-downR Φ lenΦ M-rel d′⊢ n w ρ γ rwf env = {!!}

compat-blameR :
  ∀ {E dir M A B ℓ} {p : A ⊑ B} →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ leftCtx (TPEnv.Γ E) ⊢ M ⦂ A →
  E ∣ dir ⊨ M ⊑ (blame ℓ) ⦂ p
compat-blameR M⊢ n w ρ γ rwf env = {!!}

fundamental :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  (dir : Dir) →
  E ⊢ M ⊑ M′ ⦂ p →
  E ∣ dir ⊨ M ⊑ M′ ⦂ p
fundamental {E = E} {p = p} dir (⊑` {x = x} x∈) =
  compat-var {E = E} {dir = dir} {x = x} {p = p} x∈
fundamental {E = E} dir
  (⊑ƛ {A = A} {A′ = A′} {B = B} {B′ = B′} {M = M} {M′ = M′}
      {pA = pA} {pB = pB} hA hA′ rel) =
  compat-ƛ {E = E} {dir = dir} {A = A} {A′ = A′} {B = B} {B′ = B′}
    {M = M} {M′ = M′} {pA = pA} {pB = pB} hA hA′
    (⊑-left-typed rel)
    (⊑-right-typed rel)
    (fundamental {E = extendᴾ E (A , A′ , pA)} {M = M} {M′ = M′} {p = pB} dir rel)
fundamental {E = E} dir
  (⊑· {A = A} {A′ = A′} {B = B} {B′ = B′}
      {L = L} {L′ = L′} {M = M} {M′ = M′} {pA = pA} {pB = pB}
      relL relM) =
  compat-· {E = E} {dir = dir} {A = A} {A′ = A′} {B = B} {B′ = B′}
    {L = L} {L′ = L′} {M = M} {M′ = M′} {pA = pA} {pB = pB}
    (fundamental {E = E} {M = L} {M′ = L′} {p = ⊑-⇒ A A′ B B′ pA pB} dir relL)
    (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir relM)
fundamental {E = E} dir
  (⊑Λ {A = A} {B = B} {M = M} {M′ = M′} {p = p} rel) =
  compat-Λ {E = E} {dir = dir} {A = A} {B = B} {M = M} {M′ = M′} {p = p}
    (fundamental {E = ⇑ᵗᴱ E} {M = M} {M′ = M′} {p = p} dir rel)
fundamental {E = E} dir
  (⊑⦂∀ {A = A} {B = B} {M = M} {M′ = M′} {T = T} {p = p}
        rel wfA wfB hT) =
  compat-⦂∀ {E = E} {dir = dir} {A = A} {B = B} {M = M}
    {M′ = M′} {T = T} {p = p}
    (fundamental {E = E} {M = M} {M′ = M′} {p = ⊑-∀ A B p} dir rel)
    wfA
    wfB
    hT
fundamental {E = E} dir
  (⊑⦂∀-ν A B {M = M} {M′ = M′} {T = T} p rel wfA hT) =
  compat-⦂∀-ν A B {E = E} {dir = dir} {M = M} {M′ = M′} {T = T} p
    (fundamental {E = E} {M = M} {M′ = M′} {p = ⊑-ν A B p} dir rel)
    wfA
    hT
fundamental {E = E} dir (⊑$ {n}) = compat-$ {E = E} {dir = dir} {n = n}
fundamental {E = E} dir
  (⊑⊕ {L = L} {L′ = L′} {M = M} {M′ = M′} {op = op}
       relL relM) =
  compat-⊕ {E = E} {dir = dir} {L = L} {L′ = L′} {M = M}
    {M′ = M′} {op = op}
    (fundamental {E = E} {M = L} {M′ = L′} {p = ⊑-‵ `ℕ} dir relL)
    (fundamental {E = E} {M = M} {M′ = M′} {p = ⊑-‵ `ℕ} dir relM)
fundamental {E = E} dir
  (⊑up {M = M} {M′ = M′} {A = A} {A′ = A′} {B = B} {B′ = B′}
      {pA = pA} {pB = pB} {u = u} {u′ = u′} Φ lenΦ rel hu hu′) =
  compat-up {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {pA = pA} {pB = pB} {u = u} {u′ = u′}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hu hu′
fundamental {E = E} dir
  (⊑upL {M = M} {M′ = M′} {A = A} {A′ = A′} {B = B}
      {pA = pA} {pB = pB} {u = u} Φ lenΦ rel hu) =
  compat-upL {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B = B} {pA = pA} {pB = pB} {u = u}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hu
fundamental {E = E} dir
  (⊑upR {M = M} {M′ = M′} {A = A} {A′ = A′} {B′ = B′}
      {pA = pA} {pB = pB} {u′ = u′} Φ lenΦ rel hu′) =
  compat-upR {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B′ = B′} {pA = pA} {pB = pB} {u′ = u′}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hu′
fundamental {E = E} dir
  (⊑down {M = M} {M′ = M′} {A = A} {A′ = A′} {B = B} {B′ = B′}
      {pA = pA} {pB = pB} {d = d} {d′ = d′} Φ lenΦ rel hd hd′) =
  compat-down {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {pA = pA} {pB = pB} {d = d} {d′ = d′}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hd hd′
fundamental {E = E} dir
  (⊑downL {M = M} {M′ = M′} {A = A} {A′ = A′} {B = B}
      {pA = pA} {pB = pB} {d = d} Φ lenΦ rel hd) =
  compat-downL {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B = B} {pA = pA} {pB = pB} {d = d}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hd
fundamental {E = E} dir
  (⊑downR {M = M} {M′ = M′} {A = A} {A′ = A′} {B′ = B′}
      {pA = pA} {pB = pB} {d′ = d′} Φ lenΦ rel hd′) =
  compat-downR {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B′ = B′} {pA = pA} {pB = pB} {d′ = d′}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hd′
fundamental {E = E} {M = M} {A = A} {B = B} {p = p} dir (⊑blameR {ℓ = ℓ} hM) =
  compat-blameR {E = E} {dir = dir} {M = M} {A = A} {B = B} {ℓ = ℓ} {p = p} hM

fundamental-⊨ :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  E ⊨ M ⊑ M′ ⦂ p
fundamental-⊨ rel = (fundamental ≼ rel) , (fundamental ≽ rel)
