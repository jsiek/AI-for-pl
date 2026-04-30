module Parametricity where

-- File Charter:
--   * Decomposes the fundamental theorem into compatibility lemmas,
--   * following the style used in `SystemF/agda/extrinsic/Parametricity.agda`.
--   * Provides a recursive proof skeleton of `fundamental` by induction on
--   * term precision derivations.
--   * Keeps hard compatibility cases as explicit proof holes for now, while
--   * exposing the final theorem with the intended interface.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; cong₂; subst; sym; trans)
open import Data.Nat
  using (ℕ; zero; suc; _<_; z<s; s<s; z≤n; _<′_; <′-base; ≤′-reflexive; ≤′-step)
open import Data.Nat.Properties using (n≤1+n; <-≤-trans; ≤-trans)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Types
open import Ctx using (⤊ᵗ; map-substᵗ-⤊ᵗ)
open import TypeProperties
  using
    ( substᵗ-preserves-WfTy
    ; liftSubstˢ
    ; TySubstWf-exts
    ; substᵗ-renameᵗ
    ; substᵗ-substᵗ
    ; substᵗ-cong
    ; substᵗ-ground
    ; open-renᵗ-suc
    )
open import Store
  using
    ( _⊆ˢ_
    ; ⊆ˢ-refl
    ; ⊆ˢ-trans
    ; Uniqueˢ
    ; uniq∷_
    ; StoreWf
    ; lookup-unique
    ; wkLookupˢ
    ; storeWf-unique
    ; storeWf-wfTy
    ; storeWf-dom<
    ; storeWf-dom∋
    ; storeWf-length
    ; LookupStoreAny
    ; storeWf-ν-ext
    ; substStoreᵗ
    ; substStoreᵗ-ext-⟰ᵗ
    )
open import Imprecision
open import UpDown
open import Terms
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
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
    ; substˣ-term-value
    ; substˣ-term-cong
    ; substᵗᵐ-cong
    ; substˣ-term-wt
    ; renameˣᵐ-substᵗᵐ-commute
    ; substᵗᵐ-substˣ-term-commute
    ; substᵗᵐ-substˣ-term-commute-gen
    ; substᵗᵐ-substᵗᵐ
    ; substᵗᵐ-id-emptyΔ
    ; cong₃
    ; []-wt
    ; ↑ᵗᵐ
    ; ↑ᵗᵐ-wt
    ; renameᵗᵐ-suc-extsᵗ
    )
open import ReductionFresh
  using
    ( Value
    ; _∣_—→_∣_
    ; _∣_—↠_∣_
    ; _∎
    ; _—→⟨_⟩_
    ; multi-trans
    ; id-step
    ; β
    ; β-Λ
    ; β-up-↦
    ; β-down-↦
    ; id-up
    ; id-down
    ; seal-unseal
    ; ξ-·₁
    ; ξ-·₂
    ; ξ-·α
    ; ξ-up
    ; ξ-down
    ; blame-·₁
    ; blame-·₂
    ; blame-·α
    ; blame-up
    ; blame-down
    ; store-growth
    )
  renaming ($ to v$; ƛ_⇒_ to vƛ_⇒_)
open import ProgressFresh using (FunView; canonical-⇒; fv-ƛ; fv-up-↦; fv-down-↦)
open import PreservationFresh using (len<suc-StoreWf; length∉dom-StoreWf)
open import LogicalRelation

𝒢-lookup :
  ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  𝒢 Γ (suc n) dir w ρ γ →
  𝒱 ρ p n dir w (leftˣ γ x) (rightˣ γ x)
𝒢-lookup {A = A} {B = B} {p = p} Zₚ
  (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒱-monotone _ _ _ p _ _ _ _ _ rel
𝒢-lookup (Sₚ x∈) (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒢-lookup x∈ env

𝒢-left-typed :
  ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  𝒢 Γ n dir w ρ γ →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ leftˣ γ x ⦂ substᵗ (leftᵗ ρ) A
𝒢-left-typed Zₚ
  (vˡ , vʳ , (vV , vW , (V⊢ , W⊢) , payload) , lclosed , rclosed , env) = V⊢
𝒢-left-typed (Sₚ x∈) (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒢-left-typed x∈ env

𝒢-right-typed :
  ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  𝒢 Γ n dir w ρ γ →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ rightˣ γ x ⦂ substᵗ (rightᵗ ρ) B
𝒢-right-typed Zₚ
  (vˡ , vʳ , (vV , vW , (V⊢ , W⊢) , payload) , lclosed , rclosed , env) = W⊢
𝒢-right-typed (Sₚ x∈) (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒢-right-typed x∈ env

𝒢-left-Substˣ-wt :
  ∀ {Γ n dir w} {ρ : RelSub 0} {γ} →
  𝒢 Γ n dir w ρ γ →
  Substˣ-wt {0} {Ψˡ w} {Σˡ w}
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
  Substˣ-wt {0} {Ψʳ w} {Σʳ w}
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
  𝒱 ρ p n dir w
    (substᵗᵐ (leftᵗ ρ) (leftˣ γ x))
    (substᵗᵐ (rightᵗ ρ) (rightˣ γ x))
𝒢-lookup-substᵗ {p = p} Zₚ
  (vˡ , vʳ , rel , lclosed , rclosed , env)
  rewrite lclosed | rclosed =
  𝒱-monotone _ _ _ p _ _ _ _ _ rel
𝒢-lookup-substᵗ (Sₚ x∈) (vˡ , vʳ , rel , lclosed , rclosed , env) =
  𝒢-lookup-substᵗ x∈ env

const-𝒱 :
  ∀ {n dir w m} {ρ : RelSub 0} →
  𝒱 ρ (⊑-‵ `ℕ) n dir w ($ (κℕ m)) ($ (κℕ m))
const-𝒱 {n = zero} = v$ _ , v$ _ , (⊢$ _ , ⊢$ _) , lift refl
const-𝒱 {n = suc n} = v$ _ , v$ _ , (⊢$ _ , ⊢$ _) , lift refl

𝒱⇒ℰ :
  ∀ {A B} {ρ : RelSub 0} {p : A ⊑ B} {n dir w V W} →
  𝒱 ρ p n dir w V W →
  ℰ ρ p (suc n) dir w V W
𝒱⇒ℰ {ρ = ρ} {p = p} {n = n} {dir = ≼} {w = w} {V = V} {W = W}
  (vV , vW , (V⊢ , W⊢) , payload) =
  (V⊢ , W⊢) ,
  inj₂ (inj₂ (vV , Σʳ w , Ψʳ w , wfΣʳ w , W , (W ∎) ,
    𝒱-⪰ {n = n} {dir = ≼} ρ p (mkWorldʳ-⪰ ⊆ˢ-refl)
      (vV , vW , (V⊢ , W⊢) , payload)))
𝒱⇒ℰ {ρ = ρ} {p = p} {n = n} {dir = ≽} {w = w} {V = V} {W = W}
  (vV , vW , (V⊢ , W⊢) , payload) =
  (V⊢ , W⊢) ,
  inj₂ (inj₂ (vW , Σˡ w , Ψˡ w , wfΣˡ w , V , (V ∎) ,
    𝒱-⪰ {n = n} {dir = ≽} ρ p (mkWorldˡ-⪰ ⊆ˢ-refl)
      (vV , vW , (V⊢ , W⊢) , payload)))

𝒱⇒ℰ-zero :
  ∀ {A B} {ρ : RelSub 0} {p : A ⊑ B} {dir w V W} →
  𝒱 ρ p zero dir w V W →
  ℰ ρ p zero dir w V W
𝒱⇒ℰ-zero (vV , vW , (V⊢ , W⊢) , payload) =
  (V⊢ , W⊢) , lift tt

close-left-body-typed :
  ∀ {E A B M n dir w} {ρ : RelSub 0} {γ} →
  RelWf E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣
    (A ∷ leftCtx (TPEnv.Γ E)) ⊢ M ⦂ B →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ (substᵗ (leftᵗ ρ) A ∷ []) ⊢
    substᵗᵐ (leftᵗ ρ) (substˣ-term (extˣ (leftˣ γ)) M) ⦂
    substᵗ (leftᵗ ρ) B
close-left-body-typed {M = M} {ρ = ρ} {γ = γ} rwf env M⊢
  =
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
        (substᵗ-wt (leftᵗ ρ) (leftᵗ-wf rwf)
          (wkΨ-term-≤ (Ψˡ≤ rwf) M⊢))))

close-right-body-typed :
  ∀ {E A B M n dir w} {ρ : RelSub 0} {γ} →
  RelWf E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣
    (A ∷ rightCtx (TPEnv.Γ E)) ⊢ M ⦂ B →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ (substᵗ (rightᵗ ρ) A ∷ []) ⊢
    substᵗᵐ (rightᵗ ρ) (substˣ-term (extˣ (rightˣ γ)) M) ⦂
    substᵗ (rightᵗ ρ) B
close-right-body-typed {M = M} {ρ = ρ} {γ = γ} rwf env M⊢
  =
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
        (substᵗ-wt (rightᵗ ρ) (rightᵗ-wf rwf)
          (wkΨ-term-≤ (Ψʳ≤ rwf) M⊢))))

close-left-Λ-body-typed :
  ∀ {E A M n dir w} {ρ : RelSub 0} {γ} →
  RelWf E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  (suc (TPEnv.Δ E)) ∣ TPEnv.Ψ E ∣ ⟰ᵗ (TPEnv.store E) ∣
    ⤊ᵗ (leftCtx (TPEnv.Γ E)) ⊢ M ⦂ A →
  (suc zero) ∣ Ψˡ w ∣ ⟰ᵗ (Σˡ w) ∣ [] ⊢
    substᵗᵐ (extsᵗ (leftᵗ ρ)) (substˣ-term (↑ᵗᵐ (leftˣ γ)) M) ⦂
    substᵗ (extsᵗ (leftᵗ ρ)) A
close-left-Λ-body-typed {E = E} {M = M} {ρ = ρ} {γ = γ} rwf env M⊢
  =
  cong-⊢⦂ refl refl
    (sym
      (substᵗᵐ-substˣ-term-commute-gen
        (extsᵗ (leftᵗ ρ))
        (↑ᵗᵐ (leftˣ γ))
        (↑ᵗᵐ (λ x → substᵗᵐ (leftᵗ ρ) (leftˣ γ x)))
        (λ x → renameᵗᵐ-suc-extsᵗ (leftᵗ ρ) (leftˣ γ x))
        M))
    refl
    (substˣ-term-wt
      (↑ᵗᵐ (λ x → substᵗᵐ (leftᵗ ρ) (leftˣ γ x)))
      (↑ᵗᵐ-wt _ (𝒢-left-Substˣ-wt env))
      (wkΣ-term (inst-⟰ᵗ-⊆ˢ (storeˡ rwf))
        (cong-⊢⦂
          (substStoreᵗ-ext-⟰ᵗ (leftᵗ ρ) (TPEnv.store E))
          (map-substᵗ-⤊ᵗ (leftᵗ ρ) (leftCtx (TPEnv.Γ E)))
          refl
          refl
          (substᵗ-wt (extsᵗ (leftᵗ ρ)) (TySubstWf-exts (leftᵗ-wf rwf))
            (wkΨ-term-≤ (Ψˡ≤ rwf) M⊢)))))

close-right-Λ-body-typed :
  ∀ {E A M n dir w} {ρ : RelSub 0} {γ} →
  RelWf E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  (suc (TPEnv.Δ E)) ∣ TPEnv.Ψ E ∣ ⟰ᵗ (TPEnv.store E) ∣
    ⤊ᵗ (rightCtx (TPEnv.Γ E)) ⊢ M ⦂ A →
  (suc zero) ∣ Ψʳ w ∣ ⟰ᵗ (Σʳ w) ∣ [] ⊢
    substᵗᵐ (extsᵗ (rightᵗ ρ)) (substˣ-term (↑ᵗᵐ (rightˣ γ)) M) ⦂
    substᵗ (extsᵗ (rightᵗ ρ)) A
close-right-Λ-body-typed {E = E} {M = M} {ρ = ρ} {γ = γ} rwf env M⊢
  =
  cong-⊢⦂ refl refl
    (sym
      (substᵗᵐ-substˣ-term-commute-gen
        (extsᵗ (rightᵗ ρ))
        (↑ᵗᵐ (rightˣ γ))
        (↑ᵗᵐ (λ x → substᵗᵐ (rightᵗ ρ) (rightˣ γ x)))
        (λ x → renameᵗᵐ-suc-extsᵗ (rightᵗ ρ) (rightˣ γ x))
        M))
    refl
    (substˣ-term-wt
      (↑ᵗᵐ (λ x → substᵗᵐ (rightᵗ ρ) (rightˣ γ x)))
      (↑ᵗᵐ-wt _ (𝒢-right-Substˣ-wt env))
      (wkΣ-term (inst-⟰ᵗ-⊆ˢ (storeʳ rwf))
        (cong-⊢⦂
          (substStoreᵗ-ext-⟰ᵗ (rightᵗ ρ) (TPEnv.store E))
          (map-substᵗ-⤊ᵗ (rightᵗ ρ) (rightCtx (TPEnv.Γ E)))
          refl
          refl
          (substᵗ-wt (extsᵗ (rightᵗ ρ)) (TySubstWf-exts (rightᵗ-wf rwf))
            (wkΨ-term-≤ (Ψʳ≤ rwf) M⊢)))))

𝒢-lookup-substᵗ-current :
  ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  𝒢 Γ n dir w ρ γ →
  𝒱 ρ p n dir w
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

dir-case :
  ∀ {ℓ} {P : Dir → Set ℓ} →
  P ≼ →
  P ≽ →
  (d : Dir) →
  P d
dir-case p q ≼ = p
dir-case p q ≽ = q

𝒢-monotone :
  ∀ {Γ n dir w} {ρ : RelSub 0} {γ} →
  𝒢 Γ (suc n) dir w ρ γ →
  𝒢 Γ n dir w ρ γ
𝒢-monotone {Γ = []} env = lift tt
𝒢-monotone {Γ = (A , B , p) ∷ Γ} {n = n} {dir = dir} {w = w}
  {ρ = ρ} {γ = γ}
  (vˡ , vʳ , rel , lclosed , rclosed , env) =
  vˡ , vʳ ,
  𝒱-monotone ρ _ _ p n dir w _ _ rel ,
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
  vˡ , vʳ , 𝒱-⪰ {n = n} {dir = dir} ρ p w′⪰ rel ,
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

close-left-term-typed :
  ∀ {E A M n dir w} {ρ : RelSub 0} {γ} →
  RelWf E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣
    leftCtx (TPEnv.Γ E) ⊢ M ⦂ A →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M) ⦂
    substᵗ (leftᵗ ρ) A
close-left-term-typed {E = E} {M = M} {ρ = ρ} {γ = γ} rwf env M⊢ =
  cong-⊢⦂ refl refl
    (sym
      (substᵗᵐ-substˣ-term-commute-gen
        (leftᵗ ρ)
        (leftˣ γ)
        (λ x → substᵗᵐ (leftᵗ ρ) (leftˣ γ x))
        (λ x → refl)
        M))
    refl
    (substˣ-term-wt
      (λ x → substᵗᵐ (leftᵗ ρ) (leftˣ γ x))
      (𝒢-left-Substˣ-wt env)
      (wkΣ-term (storeˡ rwf)
        (substᵗ-wt (leftᵗ ρ) (leftᵗ-wf rwf)
          (wkΨ-term-≤ (Ψˡ≤ rwf) M⊢))))

exts-as-renameᵗ :
  (ρ : Renameᵗ) →
  (X : TyVar) →
  extsᵗ (λ Y → ＇ ρ Y) X ≡ ＇ extᵗ ρ X
exts-as-renameᵗ ρ zero = refl
exts-as-renameᵗ ρ (suc X) = refl

liftSubstˢ-as-renameᵗ :
  (ρ : Renameᵗ) →
  (X : TyVar) →
  liftSubstˢ (λ Y → ＇ ρ Y) X ≡ ＇ ρ X
liftSubstˢ-as-renameᵗ ρ X = refl

mutual
  subst⊑ᵗ-as-renameᵗ :
    (ρ : Renameᵗ) (p : Up) →
    subst⊑ᵗ (λ X → ＇ ρ X) p ≡ rename⊑ᵗ ρ p
  subst⊑ᵗ-as-renameᵗ ρ (tag p G) =
    cong₂ tag (subst⊑ᵗ-as-renameᵗ ρ p) (subst-as-renameᵗ ρ G)
  subst⊑ᵗ-as-renameᵗ ρ (unseal α p) =
    cong (unseal α) (subst⊑ᵗ-as-renameᵗ ρ p)
  subst⊑ᵗ-as-renameᵗ ρ (p ↦ q) =
    cong₂ _↦_ (subst⊒ᵗ-as-renameᵗ ρ p) (subst⊑ᵗ-as-renameᵗ ρ q)
  subst⊑ᵗ-as-renameᵗ ρ (∀ᵖ p) =
    cong ∀ᵖ
      (trans (subst⊑ᵗ-cong (exts-as-renameᵗ ρ) p)
             (subst⊑ᵗ-as-renameᵗ (extᵗ ρ) p))
  subst⊑ᵗ-as-renameᵗ ρ (ν p) =
    cong ν_
      (trans (subst⊑ᵗ-cong (liftSubstˢ-as-renameᵗ ρ) p)
             (subst⊑ᵗ-as-renameᵗ ρ p))
  subst⊑ᵗ-as-renameᵗ ρ (id A) = cong id (subst-as-renameᵗ ρ A)

  subst⊒ᵗ-as-renameᵗ :
    (ρ : Renameᵗ) (p : Down) →
    subst⊒ᵗ (λ X → ＇ ρ X) p ≡ rename⊒ᵗ ρ p
  subst⊒ᵗ-as-renameᵗ ρ (untag G ℓ p) =
    cong₂ (λ T q → untag T ℓ q)
      (subst-as-renameᵗ ρ G)
      (subst⊒ᵗ-as-renameᵗ ρ p)
  subst⊒ᵗ-as-renameᵗ ρ (seal p α) =
    cong (λ q → seal q α) (subst⊒ᵗ-as-renameᵗ ρ p)
  subst⊒ᵗ-as-renameᵗ ρ (p ↦ q) =
    cong₂ _↦_ (subst⊑ᵗ-as-renameᵗ ρ p) (subst⊒ᵗ-as-renameᵗ ρ q)
  subst⊒ᵗ-as-renameᵗ ρ (∀ᵖ p) =
    cong ∀ᵖ
      (trans (subst⊒ᵗ-cong (exts-as-renameᵗ ρ) p)
             (subst⊒ᵗ-as-renameᵗ (extᵗ ρ) p))
  subst⊒ᵗ-as-renameᵗ ρ (ν p) =
    cong ν_
      (trans (subst⊒ᵗ-cong (liftSubstˢ-as-renameᵗ ρ) p)
             (subst⊒ᵗ-as-renameᵗ ρ p))
  subst⊒ᵗ-as-renameᵗ ρ (id A) = cong id (subst-as-renameᵗ ρ A)

substᵗᵐ-as-renameᵗ :
  (ρ : Renameᵗ) (M : Term) →
  substᵗᵐ (λ X → ＇ ρ X) M ≡ renameᵗᵐ ρ M
substᵗᵐ-as-renameᵗ ρ (` x) = refl
substᵗᵐ-as-renameᵗ ρ (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_ (subst-as-renameᵗ ρ A) (substᵗᵐ-as-renameᵗ ρ M)
substᵗᵐ-as-renameᵗ ρ (L · M) =
  cong₂ _·_ (substᵗᵐ-as-renameᵗ ρ L) (substᵗᵐ-as-renameᵗ ρ M)
substᵗᵐ-as-renameᵗ ρ (Λ M) =
  cong Λ_
    (trans (substᵗᵐ-cong (exts-as-renameᵗ ρ) M)
           (substᵗᵐ-as-renameᵗ (extᵗ ρ) M))
substᵗᵐ-as-renameᵗ ρ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (substᵗᵐ-as-renameᵗ ρ M)
    (trans (substᵗ-cong (exts-as-renameᵗ ρ) B)
           (subst-as-renameᵗ (extᵗ ρ) B))
    (subst-as-renameᵗ ρ T)
substᵗᵐ-as-renameᵗ ρ ($ κ) = refl
substᵗᵐ-as-renameᵗ ρ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (substᵗᵐ-as-renameᵗ ρ L) refl
    (substᵗᵐ-as-renameᵗ ρ M)
substᵗᵐ-as-renameᵗ ρ (M up p) =
  cong₂ _up_ (substᵗᵐ-as-renameᵗ ρ M) (subst⊑ᵗ-as-renameᵗ ρ p)
substᵗᵐ-as-renameᵗ ρ (M down p) =
  cong₂ _down_ (substᵗᵐ-as-renameᵗ ρ M) (subst⊒ᵗ-as-renameᵗ ρ p)
substᵗᵐ-as-renameᵗ ρ (blame ℓ) = refl

renameᵗᵐ-id-emptyΔ :
  ∀ {Ψ Σ Γ M A} (ρ : Renameᵗ) →
  0 ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  renameᵗᵐ ρ M ≡ M
renameᵗᵐ-id-emptyΔ ρ M⊢ =
  trans (sym (substᵗᵐ-as-renameᵗ ρ _)) (substᵗᵐ-id-emptyΔ M⊢)

store-subst-suc :
  (σ : Substᵗ) (τ : Substᵗ) →
  ((X : TyVar) → σ (suc X) ≡ τ X) →
  (Σ : Store) →
  substStoreᵗ σ (⟰ᵗ Σ) ≡ substStoreᵗ τ Σ
store-subst-suc σ τ h [] = refl
store-subst-suc σ τ h ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl
      (trans
        (substᵗ-renameᵗ suc σ A)
        (substᵗ-cong h A)))
    (store-subst-suc σ τ h Σ)

pred-< :
  ∀ {α Ψ} →
  α < suc Ψ →
  α ≢ Ψ →
  α < Ψ
pred-< {zero} {zero} z<s α≢Ψ = ⊥-elim (α≢Ψ refl)
pred-< {zero} {suc Ψ} z<s α≢Ψ = z<s
pred-< {suc α} {zero} (s<s ()) α≢Ψ
pred-< {suc α} {suc Ψ} (s<s α<sucΨ) α≢sucΨ =
  s<s (pred-< α<sucΨ (λ eq → α≢sucΨ (cong suc eq)))

storeWf-fresh-ext :
  ∀ {Δ Ψ Σ} {T : Ty} →
  WfTy Δ Ψ T →
  StoreWf Δ Ψ Σ →
  StoreWf Δ (suc Ψ) ((length Σ , T) ∷ Σ)
storeWf-fresh-ext {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {T = T} wfT wfΣ =
  record
    { unique = uniq∷_ (length∉dom-StoreWf wfΣ) (storeWf-unique wfΣ)
    ; wfTy = wf
    ; dom< = domBound
    ; dom∋ = domAny
    ; len = cong suc (storeWf-length wfΣ)
    }
  where
  wf : ∀ {α A} → ((length Σ , T) ∷ Σ) ∋ˢ α ⦂ A → WfTy Δ (suc Ψ) A
  wf (Z∋ˢ α≡β A≡B) =
    subst
      (WfTy Δ (suc Ψ))
      (sym A≡B)
      (WfTy-weakenˢ wfT (n≤1+n _))
  wf (S∋ˢ h) = WfTy-weakenˢ (storeWf-wfTy wfΣ h) (n≤1+n _)

  domBound : ∀ {α A} → ((length Σ , T) ∷ Σ) ∋ˢ α ⦂ A → α < suc Ψ
  domBound (Z∋ˢ α≡β A≡B) =
    subst
      (λ γ → γ < suc Ψ)
      (sym α≡β)
      (len<suc-StoreWf wfΣ)
  domBound (S∋ˢ h) = <-≤-trans (storeWf-dom< wfΣ h) (n≤1+n _)

  domAny : ∀ {α} → α < suc Ψ → LookupStoreAny ((length Σ , T) ∷ Σ) α
  domAny {α} α<sucΨ with seal-≟ α (length Σ)
  domAny {α} α<sucΨ | yes α≡len = T , Z∋ˢ α≡len refl
  domAny {α} α<sucΨ | no α≢len with
    storeWf-dom∋ wfΣ
      (pred-< α<sucΨ (λ eq → α≢len (trans eq (sym (storeWf-length wfΣ)))))
  domAny {α} α<sucΨ | no α≢len | A , h = A , S∋ˢ h

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

up-blame-↠ :
  ∀ {Σ Σ′ M ℓ} {p : Up} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ M up p —↠ Σ′ ∣ blame ℓ
up-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ up p) —→⟨ id-step blame-up ⟩ blame ℓ ∎
up-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M up p) —→⟨ ξ-up M→M′ ⟩ up-blame-↠ M′↠blame

up-↠ :
  ∀ {Σ Σ′ M M′} {p : Up} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (M up p) —↠ Σ′ ∣ (M′ up p)
up-↠ {p = p} (M ∎) = (M up p) ∎
up-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠W) =
  (M up p) —→⟨ ξ-up M→M′ ⟩ up-↠ M′↠W

down-blame-↠ :
  ∀ {Σ Σ′ M ℓ} {p : Down} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (_down_ M p) —↠ Σ′ ∣ blame ℓ
down-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (_down_ (blame ℓ) p) —→⟨ id-step blame-down ⟩ blame ℓ ∎
down-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (_down_ M p) —→⟨ ξ-down M→M′ ⟩ down-blame-↠ M′↠blame

down-↠ :
  ∀ {Σ Σ′ M M′} {p : Down} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (_down_ M p) —↠ Σ′ ∣ (_down_ M′ p)
down-↠ {p = p} (M ∎) = (_down_ M p) ∎
down-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠W) =
  (_down_ M p) —→⟨ ξ-down M→M′ ⟩ down-↠ M′↠W

tyapp-blame-↠ :
  ∀ {Σ Σ′ M ℓ B T} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ blame ℓ
tyapp-blame-↠ {ℓ = ℓ} {B = B} {T = T} (_ ∎) =
  (blame ℓ ⦂∀ B [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎
tyapp-blame-↠ {B = B} {T = T} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩ tyapp-blame-↠ M′↠blame

tyapp-↠ :
  ∀ {Σ Σ′ M M′ B T} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ (M′ ⦂∀ B [ T ])
tyapp-↠ {B = B} {T = T} (M ∎) = (M ⦂∀ B [ T ]) ∎
tyapp-↠ {B = B} {T = T} (M —→⟨ M→M′ ⟩ M′↠W) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩ tyapp-↠ M′↠W

mutual
  ℰ-pull-≼-right-↠ :
    ∀ {A B} {ρ : RelSub 0} {p : A ⊑ B} {k : ℕ} {w : World}
      {Σʳ′ : Store} {Ψʳ′ : SealCtx} {wfΣʳ′ : StoreWf (Δ w) Ψʳ′ Σʳ′}
      {Mˡ Mʳ Mʳ′ : Term} →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ substᵗ (leftᵗ ρ) A →
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ substᵗ (rightᵗ ρ) B →
    Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Mʳ′ →
    ℰ ρ p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′ →
    ℰ ρ p k ≼ w Mˡ Mʳ
  ℰ-pull-≼-right-↠ {k = zero} Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′ rel =
    (Mˡ⊢ , Mʳ⊢) , lift tt
  ℰ-pull-≼-right-↠ {ρ = ρ} {p = p} {k = suc k} {w = w}
    Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ , rel)) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₁
      (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ ,
        ℰ-pull-≼-right-↠ {ρ = ρ} {p = p} {k = k}
          {w = mkWorldˡ w Σˡ′ wfΣˡ′}
          (proj₁ (proj₁ rel)) Mʳ⊢ Mʳ↠Mʳ′ rel)
  ℰ-pull-≼-right-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₂ (inj₁ (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ , Mʳ′↠blame))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂ (inj₁ (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ , multi-trans Mʳ↠Mʳ′ Mʳ′↠blame))
  ℰ-pull-≼-right-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳ , Mʳ′↠Wʳ , rel))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳ , multi-trans Mʳ↠Mʳ′ Mʳ′↠Wʳ , rel))

  ℰ-pull-≽-left-↠ :
    ∀ {A B} {ρ : RelSub 0} {p : A ⊑ B} {k : ℕ} {w : World}
      {Σˡ′ : Store} {Ψˡ′ : SealCtx} {wfΣˡ′ : StoreWf (Δ w) Ψˡ′ Σˡ′}
      {Mˡ Mˡ′ Mʳ : Term} →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ substᵗ (leftᵗ ρ) A →
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ substᵗ (rightᵗ ρ) B →
    Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Mˡ′ →
    ℰ ρ p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ →
    ℰ ρ p k ≽ w Mˡ Mʳ
  ℰ-pull-≽-left-↠ {k = zero} Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′ rel =
    (Mˡ⊢ , Mʳ⊢) , lift tt
  ℰ-pull-≽-left-↠ {ρ = ρ} {p = p} {k = suc k} {w = w}
    Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ , rel)) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₁
      (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ ,
        ℰ-pull-≽-left-↠ {ρ = ρ} {p = p} {k = k}
          {w = mkWorldʳ w Σʳ′ wfΣʳ′}
          Mˡ⊢ (proj₂ (proj₁ rel)) Mˡ↠Mˡ′ rel)
  ℰ-pull-≽-left-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , Mʳ↠blame))) =
    (Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , Mʳ↠blame))
  ℰ-pull-≽-left-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡ , Mˡ′↠Wˡ , rel))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂ (inj₂
      (vMʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡ , multi-trans Mˡ↠Mˡ′ Mˡ′↠Wˡ , rel))

compat-var :
  ∀ {E dir x A B} {p : A ⊑ B} →
  TPEnv.Γ E ∋ₚ x ⦂ (A , B , p) →
  E ∣ dir ⊨ (` x) ⊑ (` x) ⦂ p
compat-var {dir = dir} {p = p} x∈ zero w ρ γ rwf env =
  𝒱⇒ℰ-zero {ρ = ρ} {p = p} {dir = dir} {w = w}
    (𝒢-lookup-substᵗ-current {p = p} {n = zero} {dir = dir}
      {w = w} {ρ = ρ} {γ = γ} x∈ env)
compat-var {dir = dir} {p = p} x∈ (suc n) w ρ γ rwf env =
  𝒱⇒ℰ {ρ = ρ} {p = p} {n = n} {dir = dir} {w = w}
    (𝒢-lookup-substᵗ {p = p} {n = n} {dir = dir}
      {w = w} {ρ = ρ} {γ = γ} x∈ env)

compat-$ :
  ∀ {E dir n} →
  E ∣ dir ⊨ ($ (κℕ n)) ⊑ ($ (κℕ n)) ⦂ (⊑-‵ `ℕ)
compat-$ {dir = dir} {n = m} zero w ρ γ rwf env =
  𝒱⇒ℰ-zero {ρ = ρ} {p = ⊑-‵ `ℕ} {dir = dir} {w = w}
    (const-𝒱 {n = zero} {dir = dir} {w = w} {m = m} {ρ = ρ})
compat-$ {dir = dir} {n = m} (suc n) w ρ γ rwf env =
  𝒱⇒ℰ {ρ = ρ} {p = ⊑-‵ `ℕ} {n = n} {dir = dir} {w = w}
    (const-𝒱 {n = n} {dir = dir} {w = w} {m = m} {ρ = ρ})

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
  𝒱⇒ℰ-zero {ρ = ρ} {p = ⊑-⇒ A A′ B B′ pA pB}
    {dir = dir} {w = w}
    lambda-𝒱-zero
  where
  L : Term
  L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (ƛ A ⇒ M))

  R : Term
  R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) (ƛ A′ ⇒ M′))

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA (Ψˡ≤ rwf)) (leftᵗ-wf rwf))
    (close-left-body-typed rwf env M⊢)

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA′ (Ψʳ≤ rwf)) (rightᵗ-wf rwf))
    (close-right-body-typed rwf env M′⊢)

  lambda-𝒱-zero :
    𝒱 ρ (⊑-⇒ A A′ B B′ pA pB) zero dir w L R
  lambda-𝒱-zero =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) , lift tt
compat-ƛ {E = E} {dir = ≼} {A = A} {A′ = A′} {B = B} {B′ = B′}
  {M = M} {M′ = M′} {pA = pA} {pB = pB} hA hA′ M⊢ M′⊢ M-rel
  (suc n) w ρ γ rwf env =
  𝒱⇒ℰ {ρ = ρ} {p = ⊑-⇒ A A′ B B′ pA pB} {n = n}
    {dir = ≼} {w = w}
    (lambda-𝒱 n env)
  where
  L : Term
  L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (ƛ A ⇒ M))

  R : Term
  R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) (ƛ A′ ⇒ M′))

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA (Ψˡ≤ rwf)) (leftᵗ-wf rwf))
    (close-left-body-typed rwf env M⊢)

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA′ (Ψʳ≤ rwf)) (rightᵗ-wf rwf))
    (close-right-body-typed rwf env M′⊢)

  left-typed′ :
    ∀ {w′} →
    w′ ⪰ w →
    0 ∣ Ψˡ w′ ∣ Σˡ w′ ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed′ w′⪰ = wk⪰ˡ w′⪰ left-typed

  right-typed′ :
    ∀ {w′} →
    w′ ⪰ w →
    0 ∣ Ψʳ w′ ∣ Σʳ w′ ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed′ w′⪰ = wk⪰ʳ w′⪰ right-typed

  lambda-𝒱 :
    (m : ℕ) →
    𝒢 (TPEnv.Γ E) (suc m) ≼ w ρ γ →
    𝒱 ρ (⊑-⇒ A A′ B B′ pA pB) m ≼ w L R
  lambda-𝒱 zero env′ =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) , lift tt
  lambda-𝒱 (suc k) env′ =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) ,
      FunAll→𝒱′ (app-top , all-rest)
    where
    app-top :
      ∀ {w′} →
      w′ ⪰ w →
      ∀ {V′ W′} →
      𝒱 ρ pA (suc k) ≼ w′ V′ W′ →
      Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
        ((Σˡ w′ ∣ (L · V′) —→ Σˡ w′ ∣ Lβ) ×
         ((Σʳ w′ ∣ (R · W′) —→ Σʳ w′ ∣ Rβ) ×
          ℰ ρ pB (suc k) ≼ w′ Lβ Rβ))
    app-top {w′ = w′} w′⪰ {V′ = V′} {W′ = W′}
      (vV′ , vW′ , (V′⊢ , W′⊢) , payload) =
      Lβ , Rβ , id-step (β vV′) , id-step (β vW′) , body-beta-suc
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
        ℰ ρ pB (suc k) ≼ w′
          (substᵗᵐ (leftᵗ ρ) (substˣ-term (V′ •ˣ leftˣ γ) M))
          (substᵗᵐ (rightᵗ ρ) (substˣ-term (W′ •ˣ rightˣ γ) M′))
      body-rel =
        M-rel (suc k) w′ ρ (extendγ γ V′ W′)
          (RelWf-extend (RelWf-⪰ w′⪰ rwf))
          (vV′ , vW′ , (vV′ , vW′ , (V′⊢ , W′⊢) , payload) ,
           V′-closed , W′-closed ,
           𝒢-monotone (𝒢-⪰ w′⪰ env′))

      body-beta-suc :
        ℰ ρ pB (suc k) ≼ w′ Lβ Rβ
      body-beta-suc
        rewrite β-subst-bridge (leftᵗ ρ) (leftˣ γ) M V′ V′-closed
              | β-subst-bridge (rightᵗ ρ) (rightˣ γ) M′ W′ W′-closed =
        body-rel

    rest-𝒱 : 𝒱′ ρ k ≼ pA pB w L R
    rest-𝒱 with lambda-𝒱 k (𝒢-monotone env′)
    ... | _ , _ , _ , payload = payload

    all-rest :
      FunAll ρ k pA pB ≼ w L R
    all-rest = 𝒱′→FunAll rest-𝒱

compat-ƛ {E = E} {dir = ≽} {A = A} {A′ = A′} {B = B} {B′ = B′}
  {M = M} {M′ = M′} {pA = pA} {pB = pB} hA hA′ M⊢ M′⊢ M-rel
  (suc n) w ρ γ rwf env =
  𝒱⇒ℰ {ρ = ρ} {p = ⊑-⇒ A A′ B B′ pA pB} {n = n}
    {dir = ≽} {w = w}
    (lambda-𝒱 n env)
  where
  L : Term
  L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (ƛ A ⇒ M))

  R : Term
  R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) (ƛ A′ ⇒ M′))

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA (Ψˡ≤ rwf)) (leftᵗ-wf rwf))
    (close-left-body-typed rwf env M⊢)

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed = ⊢ƛ
    (substᵗ-preserves-WfTy (WfTy-weakenˢ hA′ (Ψʳ≤ rwf)) (rightᵗ-wf rwf))
    (close-right-body-typed rwf env M′⊢)

  left-typed′ :
    ∀ {w′} →
    w′ ⪰ w →
    0 ∣ Ψˡ w′ ∣ Σˡ w′ ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  left-typed′ w′⪰ = wk⪰ˡ w′⪰ left-typed

  right-typed′ :
    ∀ {w′} →
    w′ ⪰ w →
    0 ∣ Ψʳ w′ ∣ Σʳ w′ ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  right-typed′ w′⪰ = wk⪰ʳ w′⪰ right-typed

  lambda-𝒱 :
    (m : ℕ) →
    𝒢 (TPEnv.Γ E) (suc m) ≽ w ρ γ →
    𝒱 ρ (⊑-⇒ A A′ B B′ pA pB) m ≽ w L R
  lambda-𝒱 zero env′ =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) , lift tt
  lambda-𝒱 (suc k) env′ =
    vƛ _ ⇒ _ , vƛ _ ⇒ _ , (left-typed , right-typed) ,
      FunAll→𝒱′ (app-top , all-rest)
    where
    app-top :
      ∀ {w′} →
      w′ ⪰ w →
      ∀ {V′ W′} →
      𝒱 ρ pA (suc k) ≽ w′ V′ W′ →
      Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
        ((Σˡ w′ ∣ (L · V′) —→ Σˡ w′ ∣ Lβ) ×
         ((Σʳ w′ ∣ (R · W′) —→ Σʳ w′ ∣ Rβ) ×
          ℰ ρ pB (suc k) ≽ w′ Lβ Rβ))
    app-top {w′ = w′} w′⪰ {V′ = V′} {W′ = W′}
      (vV′ , vW′ , (V′⊢ , W′⊢) , payload) =
      Lβ , Rβ , id-step (β vV′) , id-step (β vW′) , body-beta-suc
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
        ℰ ρ pB (suc k) ≽ w′
          (substᵗᵐ (leftᵗ ρ) (substˣ-term (V′ •ˣ leftˣ γ) M))
          (substᵗᵐ (rightᵗ ρ) (substˣ-term (W′ •ˣ rightˣ γ) M′))
      body-rel =
        M-rel (suc k) w′ ρ (extendγ γ V′ W′)
          (RelWf-extend (RelWf-⪰ w′⪰ rwf))
          (vV′ , vW′ , (vV′ , vW′ , (V′⊢ , W′⊢) , payload) ,
           V′-closed , W′-closed ,
           𝒢-monotone (𝒢-⪰ w′⪰ env′))

      body-beta-suc :
        ℰ ρ pB (suc k) ≽ w′ Lβ Rβ
      body-beta-suc
        rewrite β-subst-bridge (leftᵗ ρ) (leftˣ γ) M V′ V′-closed
              | β-subst-bridge (rightᵗ ρ) (rightˣ γ) M′ W′ W′-closed =
        body-rel

    rest-𝒱 : 𝒱′ ρ k ≽ pA pB w L R
    rest-𝒱 with lambda-𝒱 k (𝒢-monotone env′)
    ... | _ , _ , _ , payload = payload

    all-rest :
      FunAll ρ k pA pB ≽ w L R
    all-rest = 𝒱′→FunAll rest-𝒱

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
compat-· {E = E} {dir = ≼}
  {A = A} {A′ = A′} {B = B} {B′ = B′}
  {L = L} {L′ = L′} {M = M} {M′ = M′} {pA = pA} {pB = pB}
  L-rel M-rel (suc k) w ρ γ rwf env =
  appExpr (suc k) rwf env (L-rel (suc k) w ρ γ rwf env)
  where
  pFun : substᵗ (leftᵗ ρ) (A ⇒ B) ⊑ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  pFun = substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ pA pB)

  pAρ : substᵗ (leftᵗ ρ) A ⊑ substᵗ (rightᵗ ρ) A′
  pAρ = substᴿ-⊑ ρ pA

  pBρ : substᵗ (leftᵗ ρ) B ⊑ substᵗ (rightᵗ ρ) B′
  pBρ = substᴿ-⊑ ρ pB

  Mˡ₀ : Term
  Mˡ₀ = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)

  Mʳ₀ : Term
  Mʳ₀ = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)

  appVal :
    (k′ : ℕ) →
    ∀ {wbase Σʳ′ Ψʳ′} {wfΣʳ′ : StoreWf (Δ wbase) Ψʳ′ Σʳ′}
      {Lˡ Lʳ Wʳ Pˡ} →
    Σʳ wbase ∣ Lʳ —↠ Σʳ′ ∣ Wʳ →
    𝒱 ρ (⊑-⇒ A A′ B B′ pA pB) k′ ≼ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Lˡ Wʳ →
    ℰ ρ pA (suc k′) ≼ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Pˡ Mʳ₀ →
    0 ∣ Ψʳ wbase ∣ Σʳ wbase ∣ [] ⊢ Lʳ ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′) →
    0 ∣ Ψʳ wbase ∣ Σʳ wbase ∣ [] ⊢ Mʳ₀ ⦂ substᵗ (rightᵗ ρ) A′ →
    ℰ ρ pB (suc k′) ≼ wbase (Lˡ · Pˡ) (Lʳ · Mʳ₀)

  appExpr :
    (n : ℕ) →
    ∀ {w′ Lˡ Lʳ} →
    RelWf E w′ ρ →
    𝒢 (TPEnv.Γ E) n ≼ w′ ρ γ →
    ℰ ρ (⊑-⇒ A A′ B B′ pA pB) n ≼ w′ Lˡ Lʳ →
    ℰ ρ pB n ≼ w′ (Lˡ · Mˡ₀) (Lʳ · Mʳ₀)
  appExpr zero {w′ = w′} rwf′ env′ ((Lˡ⊢ , Lʳ⊢) , Lbody) =
    (⊢· Lˡ⊢ (proj₁ (proj₁ Mrel0)) , ⊢· Lʳ⊢ (proj₂ (proj₁ Mrel0))) ,
    lift tt
    where
    Mrel0 : ℰ ρ pA zero ≼ w′ Mˡ₀ Mʳ₀
    Mrel0 = M-rel zero w′ ρ γ rwf′ env′

  appExpr (suc k′) {w′ = w′} rwf′ env′
    ((Lˡ⊢ , Lʳ⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Lˡ′ , Lˡ→Lˡ′ , Lrel′)) =
    (⊢· Lˡ⊢ (proj₁ (proj₁ Mrel-suc)) , ⊢· Lʳ⊢ (proj₂ (proj₁ Mrel-suc))) ,
    inj₁
      (Σˡ′ , Ψˡ′ , wfΣˡ′ , (Lˡ′ · Mˡ₀) , ξ-·₁ Lˡ→Lˡ′ ,
        appExpr k′
          (RelWf-⪰ (mkWorldˡ-⪰ (store-growth Lˡ→Lˡ′)) rwf′)
          (𝒢-monotone (𝒢-⪰ (mkWorldˡ-⪰ (store-growth Lˡ→Lˡ′)) env′))
          Lrel′)
    where
    Mrel-suc : ℰ ρ pA (suc k′) ≼ w′ Mˡ₀ Mʳ₀
    Mrel-suc = M-rel (suc k′) w′ ρ γ rwf′ env′

  appExpr (suc k′) {w′ = w′} rwf′ env′
    ((Lˡ⊢ , Lʳ⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , Lʳ↠blame))) =
    (⊢· Lˡ⊢ (proj₁ (proj₁ Mrel-suc)) , ⊢· Lʳ⊢ (proj₂ (proj₁ Mrel-suc))) ,
    inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , appL-blame-↠ {M = Mʳ₀} Lʳ↠blame))
    where
    Mrel-suc : ℰ ρ pA (suc k′) ≼ w′ Mˡ₀ Mʳ₀
    Mrel-suc = M-rel (suc k′) w′ ρ γ rwf′ env′

  appExpr (suc k′) {w′ = w′} rwf′ env′
    ((Lˡ⊢ , Lʳ⊢) ,
      inj₂ (inj₂ (vLˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Wʳ , Lʳ↠Wʳ , Vfun))) =
    appVal k′ Lʳ↠Wʳ Vfun Mrel′ Lʳ⊢ (proj₂ (proj₁ Mrel-base))
    where
    growʳ : Σʳ w′ ⊆ˢ Σʳ′
    growʳ = multi-store-growth Lʳ↠Wʳ

    rwfʳ : RelWf E (mkWorldʳ w′ Σʳ′ wfΣʳ′) ρ
    rwfʳ = RelWf-⪰ (mkWorldʳ-⪰ growʳ) rwf′

    envʳ : 𝒢 (TPEnv.Γ E) (suc k′) ≼ (mkWorldʳ w′ Σʳ′ wfΣʳ′) ρ γ
    envʳ = 𝒢-⪰ (mkWorldʳ-⪰ growʳ) env′

    Mrel′ : ℰ ρ pA (suc k′) ≼ (mkWorldʳ w′ Σʳ′ wfΣʳ′) Mˡ₀ Mʳ₀
    Mrel′ = M-rel (suc k′) (mkWorldʳ w′ Σʳ′ wfΣʳ′) ρ γ rwfʳ envʳ

    Mrel-base : ℰ ρ pA (suc k′) ≼ w′ Mˡ₀ Mʳ₀
    Mrel-base = M-rel (suc k′) w′ ρ γ rwf′ env′

  appVal zero {wbase = wbase} {Σʳ′ = Σʳ′} {wfΣʳ′ = wfΣʳ′}
    {Lˡ = Lˡ} {Wʳ = Wʳ} {Pˡ = Pˡ} Lʳ↠Wʳ
    Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , fun0)
    ((Mˡ⊢ , Mʳ⊢′) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ , Mrel′))
    Lʳ⊢ Mʳ⊢ =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· Lʳ⊢ Mʳ⊢) ,
    inj₁
      (Σˡ′ , Ψˡ′ , wfΣˡ′ , (Lˡ · Mˡ′) , ξ-·₂ vLˡ Mˡ→Mˡ′ ,
       ((⊢· Lˡ⊢′ (proj₁ (proj₁ Mrel′)) ,
         ⊢· Lʳ⊢ Mʳ⊢) , lift tt))
    where
    Lˡ⊢′ :
      0 ∣ Ψˡ (mkWorldˡ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σˡ′ wfΣˡ′) ∣
        Σˡ (mkWorldˡ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σˡ′ wfΣˡ′) ∣ [] ⊢
        Lˡ ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
    Lˡ⊢′ = wk⪰ˡ
      {w = mkWorldʳ wbase Σʳ′ wfΣʳ′}
      {w′ = mkWorldˡ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σˡ′ wfΣˡ′}
      (mkWorldˡ-⪰ (store-growth Mˡ→Mˡ′))
      Lˡ⊢

  appVal zero {wbase = wbase} {Wʳ = Wʳ} {Pˡ = Pˡ} Lʳ↠Wʳ
    Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , fun0)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₁ (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ , Mʳ↠blame)))
    Lʳ⊢ Mʳ⊢ =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· Lʳ⊢ Mʳ⊢) ,
    inj₂ (inj₁
      (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ ,
       multi-trans
         (appL-↠ {M = Mʳ₀} Lʳ↠Wʳ)
         (appR-blame-↠ vWʳ Mʳ↠blame)))

  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , fun0)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳarg , Mʳ↠Wʳarg , Varg)))
    Lʳ⊢ Mʳ⊢ with canonical-⇒ vLˡ Lˡ⊢
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , fun0)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳarg , Mʳ↠Wʳarg , Varg)))
    Lʳ⊢ Mʳ⊢ | fv-ƛ refl with Lˡ⊢
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , fun0)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳarg , Mʳ↠Wʳarg , Varg)))
    Lʳ⊢ Mʳ⊢ | fv-ƛ refl | ⊢ƛ {M = N} wfA N⊢ =
    (⊢· (⊢ƛ {M = N} wfA N⊢) Mˡ⊢ , right-app-typed) ,
    inj₁
      (Σˡ wbase , Ψˡ wbase , wfΣˡ wbase , substˣ-term (singleVarEnv Pˡ) N ,
       id-step (β vMˡ) ,
       (([]-wt N⊢ Mˡ⊢ , right-app-typed) , lift tt))
    where
    right-app-typed :
      0 ∣ Ψʳ wbase ∣ Σʳ wbase ∣ [] ⊢ (Lʳ · Mʳ₀) ⦂ substᵗ (rightᵗ ρ) B′
    right-app-typed = ⊢· Lʳ⊢ Mʳ⊢

  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , fun0)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳarg , Mʳ↠Wʳarg , Varg)))
    Lʳ⊢ Mʳ⊢ | fv-up-↦ vW refl with Lˡ⊢
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , fun0)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳarg , Mʳ↠Wʳarg , Varg)))
    Lʳ⊢ Mʳ⊢ | fv-up-↦ vW refl | ⊢up Φ lenΦ W⊢ (wt-↦ p⊢ q⊢) =
    (⊢· (⊢up Φ lenΦ W⊢ (wt-↦ p⊢ q⊢)) Mˡ⊢ , right-app-typed) ,
    inj₁
      (Σˡ wbase , Ψˡ wbase , wfΣˡ wbase , _ ,
       id-step (β-up-↦ vW vMˡ) ,
       ((left-red-typed , right-app-typed) , lift tt))
    where
    right-app-typed :
      0 ∣ Ψʳ wbase ∣ Σʳ wbase ∣ [] ⊢ (Lʳ · Mʳ₀) ⦂ substᵗ (rightᵗ ρ) B′
    right-app-typed = ⊢· Lʳ⊢ Mʳ⊢

    left-red-typed :
      0 ∣ Ψˡ wbase ∣ Σˡ wbase ∣ [] ⊢ _ ⦂ substᵗ (leftᵗ ρ) B
    left-red-typed = ⊢up Φ lenΦ (⊢· W⊢ (⊢down Φ lenΦ Mˡ⊢ p⊢)) q⊢

  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , fun0)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳarg , Mʳ↠Wʳarg , Varg)))
    Lʳ⊢ Mʳ⊢ | fv-down-↦ vW refl with Lˡ⊢
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , fun0)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳarg , Mʳ↠Wʳarg , Varg)))
    Lʳ⊢ Mʳ⊢ | fv-down-↦ vW refl | ⊢down Φ lenΦ W⊢ (wt-↦ p⊢ q⊢) =
    (⊢· (⊢down Φ lenΦ W⊢ (wt-↦ p⊢ q⊢)) Mˡ⊢ , right-app-typed) ,
    inj₁
      (Σˡ wbase , Ψˡ wbase , wfΣˡ wbase , _ ,
       id-step (β-down-↦ vW vMˡ) ,
       ((left-red-typed , right-app-typed) , lift tt))
    where
    right-app-typed :
      0 ∣ Ψʳ wbase ∣ Σʳ wbase ∣ [] ⊢ (Lʳ · Mʳ₀) ⦂ substᵗ (rightᵗ ρ) B′
    right-app-typed = ⊢· Lʳ⊢ Mʳ⊢

    left-red-typed :
      0 ∣ Ψˡ wbase ∣ Σˡ wbase ∣ [] ⊢ _ ⦂ substᵗ (leftᵗ ρ) B
    left-red-typed = ⊢down Φ lenΦ (⊢· W⊢ (⊢up Φ lenΦ Mˡ⊢ p⊢)) q⊢

  appVal (suc j) {wbase = wbase} {Σʳ′ = Σʳ′} {wfΣʳ′ = wfΣʳ′}
    {Lˡ = Lˡ} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , funsuc)
    ((Mˡ⊢ , Mʳ⊢′) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ , Mrel′))
    Lʳ⊢ Mʳ⊢ =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· Lʳ⊢ Mʳ⊢) ,
    inj₁
      (Σˡ′ , Ψˡ′ , wfΣˡ′ , (Lˡ · Mˡ′) , ξ-·₂ vLˡ Mˡ→Mˡ′ ,
        appVal j
          {wbase = mkWorldˡ wbase Σˡ′ wfΣˡ′}
          Lʳ↠Wʳ
          (𝒱-monotone ρ _ _ (⊑-⇒ A A′ B B′ pA pB) j ≼
            (mkWorldˡ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σˡ′ wfΣˡ′)
            Lˡ Wʳ
            (𝒱-⪰ ρ (⊑-⇒ A A′ B B′ pA pB) (mkWorldˡ-⪰ (store-growth Mˡ→Mˡ′)) Vfun))
          Mrel′
          Lʳ⊢
          Mʳ⊢)

  appVal (suc j) {wbase = wbase} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , funsuc)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₁ (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ , Mʳ↠blame)))
    Lʳ⊢ Mʳ⊢ =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· Lʳ⊢ Mʳ⊢) ,
    inj₂ (inj₁
      (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ ,
       multi-trans
         (appL-↠ {M = Mʳ₀} Lʳ↠Wʳ)
         (appR-blame-↠ {V = Wʳ} vWʳ Mʳ↠blame)))

  appVal (suc j) {wbase = wbase} {Σʳ′ = Σʳ′} {wfΣʳ′ = wfΣʳ′}
    {Lˡ = Lˡ} {Lʳ = Lʳ} {Wʳ = Wʳ} {Pˡ = Pˡ}
    Lʳ↠Wʳ Vfun@(vLˡ , vWʳ , (Lˡ⊢ , Wʳ⊢) , funsuc)
    ((Mˡ⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳarg , Mʳ↠Wʳarg , Varg)))
    Lʳ⊢ Mʳ⊢ =
    (left-app-typed , right-app-typed) ,
    inj₁ (Σˡ wbase , Ψˡ wbase , wfΣˡ wbase , Lβ , stepL , pulled)
    where
    growʳ : Σʳ′ ⊆ˢ Σʳ″
    growʳ = multi-store-growth Mʳ↠Wʳarg

    Vfun↑ : 𝒱 ρ (⊑-⇒ A A′ B B′ pA pB) (suc j) ≼ (mkWorldʳ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σʳ″ wfΣʳ″) Lˡ Wʳ
    Vfun↑ = 𝒱-⪰ ρ (⊑-⇒ A A′ B B′ pA pB) (mkWorldʳ-⪰ growʳ) Vfun

    top-step :
      ∀ {w′} →
      w′ ⪰ (mkWorldʳ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σʳ″ wfΣʳ″) →
      ∀ {V′ W′} →
      𝒱 ρ pA (suc j) ≼ w′ V′ W′ →
      Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
        ((Σˡ w′ ∣ (Lˡ · V′) —→ Σˡ w′ ∣ Lβ) ×
         ((Σʳ w′ ∣ (Wʳ · W′) —→ Σʳ w′ ∣ Rβ) ×
          ℰ ρ pB (suc j) ≼ w′ Lβ Rβ))
    top-step = proj₁ (proj₂ (proj₂ (proj₂ Vfun↑)))

    arg↑ : 𝒱 ρ pA (suc j) ≼ (mkWorldʳ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σʳ″ wfΣʳ″) Pˡ Wʳarg
    arg↑ = Varg

    LβRβ :
      Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
        ((Σˡ (mkWorldʳ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σʳ″ wfΣʳ″) ∣
          (Lˡ · Pˡ) —→
          Σˡ (mkWorldʳ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σʳ″ wfΣʳ″) ∣ Lβ) ×
         ((Σʳ (mkWorldʳ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σʳ″ wfΣʳ″) ∣
           (Wʳ · Wʳarg) —→
           Σʳ (mkWorldʳ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σʳ″ wfΣʳ″) ∣ Rβ) ×
          ℰ ρ pB (suc j) ≼
            (mkWorldʳ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σʳ″ wfΣʳ″) Lβ Rβ))
    LβRβ = top-step (mkWorldʳ-⪰ ⊆ˢ-refl) arg↑

    Lβ : Term
    Lβ = proj₁ LβRβ

    Rβ : Term
    Rβ = proj₁ (proj₂ LβRβ)

    stepL : Σˡ wbase ∣ (Lˡ · Pˡ) —→ Σˡ wbase ∣ Lβ
    stepL = proj₁ (proj₂ (proj₂ LβRβ))

    stepR : Σʳ″ ∣ (Wʳ · Wʳarg) —→ Σʳ″ ∣ Rβ
    stepR = proj₁ (proj₂ (proj₂ (proj₂ LβRβ)))

    body : ℰ ρ pB (suc j) ≼ (mkWorldʳ (mkWorldʳ wbase Σʳ′ wfΣʳ′) Σʳ″ wfΣʳ″) Lβ Rβ
    body = proj₂ (proj₂ (proj₂ (proj₂ LβRβ)))

    left-app-typed :
      0 ∣ Ψˡ wbase ∣ Σˡ wbase ∣ [] ⊢ (Lˡ · Pˡ) ⦂ substᵗ (leftᵗ ρ) B
    left-app-typed = ⊢· Lˡ⊢ Mˡ⊢

    right-app-typed :
      0 ∣ Ψʳ wbase ∣ Σʳ wbase ∣ [] ⊢ (Lʳ · Mʳ₀) ⦂ substᵗ (rightᵗ ρ) B′
    right-app-typed = ⊢· Lʳ⊢ Mʳ⊢

    right-path :
      Σʳ wbase ∣ (Lʳ · Mʳ₀) —↠ Σʳ″ ∣ Rβ
    right-path =
      multi-trans
        (appL-↠ {M = Mʳ₀} Lʳ↠Wʳ)
        (multi-trans
          (appR-↠ vWʳ Mʳ↠Wʳarg)
          ((Wʳ · Wʳarg) —→⟨ stepR ⟩ Rβ ∎))

    pulled : ℰ ρ pB (suc j) ≼ wbase Lβ (Lʳ · Mʳ₀)
    pulled = ℰ-pull-≼-right-↠ {ρ = ρ} {p = pB} {k = suc j}
      (proj₁ (proj₁ body))
      right-app-typed
      right-path
      body

compat-· {E = E} {dir = ≽}
  {A = A} {A′ = A′} {B = B} {B′ = B′}
  {L = L} {L′ = L′} {M = M} {M′ = M′} {pA = pA} {pB = pB}
  L-rel M-rel (suc k) w ρ γ rwf env =
  appExpr (suc k) rwf env (L-rel (suc k) w ρ γ rwf env)
  where
  pFun : substᵗ (leftᵗ ρ) (A ⇒ B) ⊑ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  pFun = substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ pA pB)

  pAρ : substᵗ (leftᵗ ρ) A ⊑ substᵗ (rightᵗ ρ) A′
  pAρ = substᴿ-⊑ ρ pA

  pBρ : substᵗ (leftᵗ ρ) B ⊑ substᵗ (rightᵗ ρ) B′
  pBρ = substᴿ-⊑ ρ pB

  Mˡ₀ : Term
  Mˡ₀ = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)

  Mʳ₀ : Term
  Mʳ₀ = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)

  appVal :
    (k′ : ℕ) →
    ∀ {wbase Σˡ′ Ψˡ′} {wfΣˡ′ : StoreWf (Δ wbase) Ψˡ′ Σˡ′}
      {Lˡ Lʳ Wˡ Qʳ} →
    Σˡ wbase ∣ Lˡ —↠ Σˡ′ ∣ Wˡ →
    𝒱 ρ (⊑-⇒ A A′ B B′ pA pB) k′ ≽ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Wˡ Lʳ →
    ℰ ρ pA (suc k′) ≽ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Mˡ₀ Qʳ →
    0 ∣ Ψˡ wbase ∣ Σˡ wbase ∣ [] ⊢ Lˡ ⦂ substᵗ (leftᵗ ρ) (A ⇒ B) →
    0 ∣ Ψʳ wbase ∣ Σʳ wbase ∣ [] ⊢ Lʳ ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′) →
    0 ∣ Ψˡ wbase ∣ Σˡ wbase ∣ [] ⊢ Mˡ₀ ⦂ substᵗ (leftᵗ ρ) A →
    0 ∣ Ψʳ wbase ∣ Σʳ wbase ∣ [] ⊢ Qʳ ⦂ substᵗ (rightᵗ ρ) A′ →
    ℰ ρ pB (suc k′) ≽ wbase (Lˡ · Mˡ₀) (Lʳ · Qʳ)

  appExpr :
    (n : ℕ) →
    ∀ {w′ Lˡ Lʳ} →
    RelWf E w′ ρ →
    𝒢 (TPEnv.Γ E) n ≽ w′ ρ γ →
    ℰ ρ (⊑-⇒ A A′ B B′ pA pB) n ≽ w′ Lˡ Lʳ →
    ℰ ρ pB n ≽ w′ (Lˡ · Mˡ₀) (Lʳ · Mʳ₀)
  appExpr zero {w′ = w′} rwf′ env′ ((Lˡ⊢ , Lʳ⊢) , Lbody) =
    (⊢· Lˡ⊢ (proj₁ (proj₁ Mrel0)) , ⊢· Lʳ⊢ (proj₂ (proj₁ Mrel0))) ,
    lift tt
    where
    Mrel0 : ℰ ρ pA zero ≽ w′ Mˡ₀ Mʳ₀
    Mrel0 = M-rel zero w′ ρ γ rwf′ env′

  appExpr (suc k′) {w′ = w′} rwf′ env′
    ((Lˡ⊢ , Lʳ⊢) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , Lʳ′ , Lʳ→Lʳ′ , Lrel′)) =
    (⊢· Lˡ⊢ (proj₁ (proj₁ Mrel-suc)) , ⊢· Lʳ⊢ (proj₂ (proj₁ Mrel-suc))) ,
    inj₁
      (Σʳ′ , Ψʳ′ , wfΣʳ′ , (Lʳ′ · Mʳ₀) , ξ-·₁ Lʳ→Lʳ′ ,
        appExpr k′
          (RelWf-⪰ (mkWorldʳ-⪰ (store-growth Lʳ→Lʳ′)) rwf′)
          (𝒢-monotone (𝒢-⪰ (mkWorldʳ-⪰ (store-growth Lʳ→Lʳ′)) env′))
          Lrel′)
    where
    Mrel-suc : ℰ ρ pA (suc k′) ≽ w′ Mˡ₀ Mʳ₀
    Mrel-suc = M-rel (suc k′) w′ ρ γ rwf′ env′

  appExpr (suc k′) {w′ = w′} rwf′ env′
    ((Lˡ⊢ , Lʳ⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , Lʳ↠blame))) =
    (⊢· Lˡ⊢ (proj₁ (proj₁ Mrel-suc)) , ⊢· Lʳ⊢ (proj₂ (proj₁ Mrel-suc))) ,
    inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , appL-blame-↠ {M = Mʳ₀} Lʳ↠blame))
    where
    Mrel-suc : ℰ ρ pA (suc k′) ≽ w′ Mˡ₀ Mʳ₀
    Mrel-suc = M-rel (suc k′) w′ ρ γ rwf′ env′

  appExpr (suc k′) {w′ = w′} rwf′ env′
    ((Lˡ⊢ , Lʳ⊢) ,
      inj₂ (inj₂ (vLʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Wˡ , Lˡ↠Wˡ , Vfun))) =
    appVal k′ Lˡ↠Wˡ Vfun Mrel′
      Lˡ⊢ Lʳ⊢
      (proj₁ (proj₁ Mrel-base))
      (proj₂ (proj₁ Mrel-base))
    where
    growˡ : Σˡ w′ ⊆ˢ Σˡ′
    growˡ = multi-store-growth Lˡ↠Wˡ

    rwfˡ : RelWf E (mkWorldˡ w′ Σˡ′ wfΣˡ′) ρ
    rwfˡ = RelWf-⪰ (mkWorldˡ-⪰ growˡ) rwf′

    envˡ : 𝒢 (TPEnv.Γ E) (suc k′) ≽ (mkWorldˡ w′ Σˡ′ wfΣˡ′) ρ γ
    envˡ = 𝒢-⪰ (mkWorldˡ-⪰ growˡ) env′

    Mrel′ : ℰ ρ pA (suc k′) ≽ (mkWorldˡ w′ Σˡ′ wfΣˡ′) Mˡ₀ Mʳ₀
    Mrel′ = M-rel (suc k′) (mkWorldˡ w′ Σˡ′ wfΣˡ′) ρ γ rwfˡ envˡ

    Mrel-base : ℰ ρ pA (suc k′) ≽ w′ Mˡ₀ Mʳ₀
    Mrel-base = M-rel (suc k′) w′ ρ γ rwf′ env′

  appVal zero {wbase = wbase} {Σˡ′ = Σˡ′} {wfΣˡ′ = wfΣˡ′}
    {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , fun0)
    ((Mˡ⊢g , Qʳ⊢) , inj₁ (Σʳ″ , Ψʳ″ , wfΣʳ″ , Qʳ′ , Qʳ→Qʳ′ , rel))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· Lʳ⊢ Qʳ⊢base) ,
    inj₁
      (Σʳ″ , Ψʳ″ , wfΣʳ″ , (Lʳ · Qʳ′) , ξ-·₂ vLʳ Qʳ→Qʳ′ ,
       ((⊢· Lˡ⊢ Mˡ⊢ , ⊢· Lʳ⊢′ (proj₂ (proj₁ rel))) , lift tt))
    where
    growʳ : Σʳ wbase ⊆ˢ Σʳ″
    growʳ = store-growth Qʳ→Qʳ′

    Lʳ⊢′ :
      0 ∣ Ψʳ (mkWorldʳ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σʳ″ wfΣʳ″) ∣
        Σʳ″ ∣ [] ⊢ Lʳ ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
    Lʳ⊢′ = wk⪰ʳ
      {w = mkWorldˡ wbase Σˡ′ wfΣˡ′}
      {w′ = mkWorldʳ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σʳ″ wfΣʳ″}
      (mkWorldʳ-⪰ growʳ)
      Lʳ⊢

  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , fun0)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₁ (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ , Qʳ↠blame)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· Lʳ⊢ Qʳ⊢base) ,
    inj₂ (inj₁
      (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ , appR-blame-↠ vLʳ Qʳ↠blame))

  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , fun0)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₂
      (vQʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡarg , Mˡ↠Wˡarg , Varg)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base with canonical-⇒ vLʳ Lʳ⊢
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , fun0)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₂
      (vQʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡarg , Mˡ↠Wˡarg , Varg)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base | fv-ƛ refl with Lʳ⊢
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , fun0)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₂
      (vQʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡarg , Mˡ↠Wˡarg , Varg)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base | fv-ƛ refl | ⊢ƛ {M = N} wfA N⊢ =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· (⊢ƛ {M = N} wfA N⊢) Qʳ⊢base) ,
    inj₁
      (Σʳ wbase , Ψʳ wbase , wfΣʳ wbase , substˣ-term (singleVarEnv Qʳ) N ,
       id-step (β vQʳ) ,
       ((⊢· Lˡ⊢ Mˡ⊢ , []-wt N⊢ Qʳ⊢base) , lift tt))
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , fun0)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₂
      (vQʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡarg , Mˡ↠Wˡarg , Varg)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base | fv-up-↦ vW refl with Lʳ⊢
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , fun0)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₂
      (vQʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡarg , Mˡ↠Wˡarg , Varg)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base | fv-up-↦ vW refl | ⊢up Φ lenΦ W⊢ (wt-↦ p⊢ q⊢) =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· (⊢up Φ lenΦ W⊢ (wt-↦ p⊢ q⊢)) Qʳ⊢base) ,
    inj₁
      (Σʳ wbase , Ψʳ wbase , wfΣʳ wbase , _ ,
       id-step (β-up-↦ vW vQʳ) ,
       ((⊢· Lˡ⊢ Mˡ⊢ , ⊢up Φ lenΦ (⊢· W⊢ (⊢down Φ lenΦ Qʳ⊢base p⊢)) q⊢) ,
        lift tt))
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , fun0)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₂
      (vQʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡarg , Mˡ↠Wˡarg , Varg)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base | fv-down-↦ vW refl with Lʳ⊢
  appVal zero {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , fun0)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₂
      (vQʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡarg , Mˡ↠Wˡarg , Varg)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base | fv-down-↦ vW refl | ⊢down Φ lenΦ W⊢ (wt-↦ p⊢ q⊢) =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· (⊢down Φ lenΦ W⊢ (wt-↦ p⊢ q⊢)) Qʳ⊢base) ,
    inj₁
      (Σʳ wbase , Ψʳ wbase , wfΣʳ wbase , _ ,
       id-step (β-down-↦ vW vQʳ) ,
       ((⊢· Lˡ⊢ Mˡ⊢ , ⊢down Φ lenΦ (⊢· W⊢ (⊢up Φ lenΦ Qʳ⊢base p⊢)) q⊢) ,
        lift tt))

  appVal (suc j) {wbase = wbase} {Σˡ′ = Σˡ′} {wfΣˡ′ = wfΣˡ′}
    {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , funsuc)
    ((Mˡ⊢g , Qʳ⊢) , inj₁ (Σʳ″ , Ψʳ″ , wfΣʳ″ , Qʳ′ , Qʳ→Qʳ′ , rel))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· Lʳ⊢ Qʳ⊢base) ,
    inj₁
      (Σʳ″ , Ψʳ″ , wfΣʳ″ , (Lʳ · Qʳ′) , ξ-·₂ vLʳ Qʳ→Qʳ′ ,
        appVal j
          {wbase = mkWorldʳ wbase Σʳ″ wfΣʳ″}
          Lˡ↠Wˡ
          (𝒱-monotone ρ _ _ (⊑-⇒ A A′ B B′ pA pB) j ≽
            (mkWorldʳ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σʳ″ wfΣʳ″)
            Wˡ Lʳ
            (𝒱-⪰ ρ (⊑-⇒ A A′ B B′ pA pB) (mkWorldʳ-⪰ (store-growth Qʳ→Qʳ′)) Vfun))
          rel
          Lˡ⊢
          (wk⪰ʳ
            {w = wbase}
            {w′ = mkWorldʳ wbase Σʳ″ wfΣʳ″}
            (mkWorldʳ-⪰ (store-growth Qʳ→Qʳ′))
            Lʳ⊢)
          Mˡ⊢
          (proj₂ (proj₁ rel)))

  appVal (suc j) {wbase = wbase} {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , funsuc)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₁ (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ , Qʳ↠blame)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base =
    (⊢· Lˡ⊢ Mˡ⊢ , ⊢· Lʳ⊢ Qʳ⊢base) ,
    inj₂ (inj₁
      (Σʳ″ , Ψʳ″ , wfΣʳ″ , ℓ , appR-blame-↠ vLʳ Qʳ↠blame))

  appVal (suc j) {wbase = wbase} {Σˡ′ = Σˡ′} {wfΣˡ′ = wfΣˡ′}
    {Lˡ = Lˡ} {Lʳ = Lʳ} {Wˡ = Wˡ} {Qʳ = Qʳ}
    Lˡ↠Wˡ
    Vfun@(vWˡ , vLʳ , (Wˡ⊢ , Lʳ⊢g) , funsuc)
    ((Mˡ⊢g , Qʳ⊢) , inj₂ (inj₂
      (vQʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡarg , Mˡ↠Wˡarg , Varg)))
    Lˡ⊢ Lʳ⊢ Mˡ⊢ Qʳ⊢base =
    ℰ-expand-≽-right {ρ = ρ} {p = pB} {k = suc j}
      left-app-typed
      right-app-typed
      stepR
      (ℰ-pull-≽-left-↠ {ρ = ρ} {p = pB} {k = suc j}
        left-app-typed
        (proj₂ (proj₁ body))
        left-path
        body)
    where
    growˡ : Σˡ′ ⊆ˢ Σˡ″
    growˡ = multi-store-growth Mˡ↠Wˡarg

    Vfun↑ : 𝒱 ρ (⊑-⇒ A A′ B B′ pA pB) (suc j) ≽ (mkWorldˡ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σˡ″ wfΣˡ″) Wˡ Lʳ
    Vfun↑ = 𝒱-⪰ ρ (⊑-⇒ A A′ B B′ pA pB) (mkWorldˡ-⪰ growˡ) Vfun

    top-step :
      ∀ {w′} →
      w′ ⪰ (mkWorldˡ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σˡ″ wfΣˡ″) →
      ∀ {V′ W′} →
      𝒱 ρ pA (suc j) ≽ w′ V′ W′ →
      Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
        ((Σˡ w′ ∣ (Wˡ · V′) —→ Σˡ w′ ∣ Lβ) ×
         ((Σʳ w′ ∣ (Lʳ · W′) —→ Σʳ w′ ∣ Rβ) ×
          ℰ ρ pB (suc j) ≽ w′ Lβ Rβ))
    top-step = proj₁ (proj₂ (proj₂ (proj₂ Vfun↑)))

    arg↑ : 𝒱 ρ pA (suc j) ≽ (mkWorldˡ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σˡ″ wfΣˡ″) Wˡarg Qʳ
    arg↑ = Varg

    LβRβ :
      Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
        ((Σˡ (mkWorldˡ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σˡ″ wfΣˡ″) ∣
          (Wˡ · Wˡarg) —→
          Σˡ (mkWorldˡ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σˡ″ wfΣˡ″) ∣ Lβ) ×
         ((Σʳ (mkWorldˡ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σˡ″ wfΣˡ″) ∣
           (Lʳ · Qʳ) —→
           Σʳ (mkWorldˡ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σˡ″ wfΣˡ″) ∣ Rβ) ×
          ℰ ρ pB (suc j) ≽
            (mkWorldˡ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σˡ″ wfΣˡ″) Lβ Rβ))
    LβRβ = top-step (mkWorldˡ-⪰ ⊆ˢ-refl) arg↑

    Lβ : Term
    Lβ = proj₁ LβRβ

    Rβ : Term
    Rβ = proj₁ (proj₂ LβRβ)

    stepL : Σˡ″ ∣ (Wˡ · Wˡarg) —→ Σˡ″ ∣ Lβ
    stepL = proj₁ (proj₂ (proj₂ LβRβ))

    stepR : Σʳ wbase ∣ (Lʳ · Qʳ) —→ Σʳ wbase ∣ Rβ
    stepR = proj₁ (proj₂ (proj₂ (proj₂ LβRβ)))

    body : ℰ ρ pB (suc j) ≽ (mkWorldˡ (mkWorldˡ wbase Σˡ′ wfΣˡ′) Σˡ″ wfΣˡ″) Lβ Rβ
    body = proj₂ (proj₂ (proj₂ (proj₂ LβRβ)))

    left-app-typed :
      0 ∣ Ψˡ wbase ∣ Σˡ wbase ∣ [] ⊢ (Lˡ · Mˡ₀) ⦂ substᵗ (leftᵗ ρ) B
    left-app-typed = ⊢· Lˡ⊢ Mˡ⊢

    right-app-typed :
      0 ∣ Ψʳ wbase ∣ Σʳ wbase ∣ [] ⊢ (Lʳ · Qʳ) ⦂ substᵗ (rightᵗ ρ) B′
    right-app-typed = ⊢· Lʳ⊢ Qʳ⊢base

    left-path :
      Σˡ wbase ∣ (Lˡ · Mˡ₀) —↠ Σˡ″ ∣ Lβ
    left-path =
      multi-trans
        (appL-↠ {M = Mˡ₀} Lˡ↠Wˡ)
        (multi-trans
          (appR-↠ vWˡ Mˡ↠Wˡarg)
          ((Wˡ · Wˡarg) —→⟨ stepL ⟩ Lβ ∎))

extendρ-left-open :
  ∀ {A Tˡ Tʳ Rrel} (ρ : RelSub 0)
    {wfTˡ wfTʳ pT} {downR : DownClosed Rrel} →
  substᵗ (leftᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) A ≡
  substᵗ (singleTyEnv Tˡ) (substᵗ (extsᵗ (leftᵗ ρ)) A)
extendρ-left-open {A = A} {Tˡ = Tˡ} ρ =
  trans
    (substᵗ-cong env A)
    (sym (substᵗ-substᵗ (singleTyEnv Tˡ) (extsᵗ (leftᵗ ρ)) A))
  where
  env : (X : TyVar) →
    leftᵗ (extendρ ρ Tˡ _ _ _ _ _ _) X ≡
    substᵗ (singleTyEnv Tˡ) (extsᵗ (leftᵗ ρ) X)
  env zero = refl
  env (suc X) = sym (open-renᵗ-suc (leftᵗ ρ X) Tˡ)

extendρ-right-open :
  ∀ {A Tˡ Tʳ Rrel} (ρ : RelSub 0)
    {wfTˡ wfTʳ pT} {downR : DownClosed Rrel} →
  substᵗ (rightᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) A ≡
  substᵗ (singleTyEnv Tʳ) (substᵗ (extsᵗ (rightᵗ ρ)) A)
extendρ-right-open {A = A} {Tʳ = Tʳ} ρ =
  trans
    (substᵗ-cong env A)
    (sym (substᵗ-substᵗ (singleTyEnv Tʳ) (extsᵗ (rightᵗ ρ)) A))
  where
  env : (X : TyVar) →
    rightᵗ (extendρ ρ _ Tʳ _ _ _ _ _) X ≡
    substᵗ (singleTyEnv Tʳ) (extsᵗ (rightᵗ ρ) X)
  env zero = refl
  env (suc X) = sym (open-renᵗ-suc (rightᵗ ρ X) Tʳ)

extendρ-left-openᵐ :
  ∀ {Tˡ Tʳ Rrel} (ρ : RelSub 0)
    {wfTˡ wfTʳ pT} {downR : DownClosed Rrel} →
  (M : Term) →
  substᵗᵐ (leftᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) M ≡
  substᵗᵐ (singleTyEnv Tˡ) (substᵗᵐ (extsᵗ (leftᵗ ρ)) M)
extendρ-left-openᵐ {Tˡ = Tˡ} ρ M =
  trans
    (substᵗᵐ-cong env M)
    (sym (substᵗᵐ-substᵗᵐ (singleTyEnv Tˡ) (extsᵗ (leftᵗ ρ)) M))
  where
  env : (X : TyVar) →
    leftᵗ (extendρ ρ Tˡ _ _ _ _ _ _) X ≡
    substᵗ (singleTyEnv Tˡ) (extsᵗ (leftᵗ ρ) X)
  env zero = refl
  env (suc X) = sym (open-renᵗ-suc (leftᵗ ρ X) Tˡ)

extendρ-right-openᵐ :
  ∀ {Tˡ Tʳ Rrel} (ρ : RelSub 0)
    {wfTˡ wfTʳ pT} {downR : DownClosed Rrel} →
  (M : Term) →
  substᵗᵐ (rightᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) M ≡
  substᵗᵐ (singleTyEnv Tʳ) (substᵗᵐ (extsᵗ (rightᵗ ρ)) M)
extendρ-right-openᵐ {Tʳ = Tʳ} ρ M =
  trans
    (substᵗᵐ-cong env M)
    (sym (substᵗᵐ-substᵗᵐ (singleTyEnv Tʳ) (extsᵗ (rightᵗ ρ)) M))
  where
  env : (X : TyVar) →
    rightᵗ (extendρ ρ _ Tʳ _ _ _ _ _) X ≡
    substᵗ (singleTyEnv Tʳ) (extsᵗ (rightᵗ ρ) X)
  env zero = refl
  env (suc X) = sym (open-renᵗ-suc (rightᵗ ρ X) Tʳ)

substᵗ-open :
  (σ : Substᵗ) (A T : Ty) →
  substᵗ σ (A [ T ]ᵗ) ≡
  substᵗ (singleTyEnv (substᵗ σ T)) (substᵗ (extsᵗ σ) A)
substᵗ-open σ A T =
  trans
    (substᵗ-substᵗ σ (singleTyEnv T) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv (substᵗ σ T)) (extsᵗ σ) A)))
  where
  env : (X : TyVar) →
    substᵗ σ (singleTyEnv T X) ≡
    substᵗ (singleTyEnv (substᵗ σ T)) (extsᵗ σ X)
  env zero = refl
  env (suc X) = sym (open-renᵗ-suc (σ X) (substᵗ σ T))

sealedRel : Seal → Seal → Rel → Rel
sealedRel αˡ αʳ R k dir V W =
  Σ[ V′ ∈ Term ] Σ[ W′ ∈ Term ] Σ[ pˡ ∈ Down ] Σ[ pʳ ∈ Down ]
    (V ≡ (_down_ V′ (seal pˡ αˡ))) × (W ≡ (_down_ W′ (seal pʳ αʳ))) ×
    R k dir V′ W′

sealedRel-down :
  ∀ {αˡ αʳ R} →
  DownClosed R →
  DownClosed (sealedRel αˡ αʳ R)
sealedRel-down downR (V′ , W′ , pˡ , pʳ , eqV , eqW , rel) =
  V′ , W′ , pˡ , pʳ , eqV , eqW , downR rel

seal-value-inv :
  ∀ {V α p} →
  Value (_down_ V (seal p α)) →
  Value V
seal-value-inv (ReductionFresh._down_ vV ReductionFresh.seal) = vV

seal-typed-inv :
  ∀ {Δ Ψ Σ Γ V α A} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ _down_ V (seal (id A) α) ⦂ ｀ α →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A
seal-typed-inv uΣ α∈ (⊢down Φ lenΦ V⊢ (wt-seal (wt-id wfA) h α∈Φ)) =
  cong-⊢⦂ refl refl refl (lookup-unique uΣ h α∈) V⊢
seal-typed-inv uΣ α∈ (⊢down Φ lenΦ V⊢ (wt-seal★ (wt-id wfA) h α∈Φ)) =
  cong-⊢⦂ refl refl refl (lookup-unique uΣ h α∈) V⊢

instCast-up-left-typed :
  ∀ {A Tˡ Tʳ αˡ αʳ Rrel} {ρ : RelSub 0} {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} {downR : DownClosed Rrel}
    {w L} →
  (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
  (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
  Σˡ w ∋ˢ αˡ ⦂ Tˡ →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂
    substᵗ
      (leftᵗ
        (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
          (sealedRel αˡ αʳ Rrel)
          (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
      A →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    L up (instCast⊑
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ})
    ⦂ substᵗ (leftᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) A
instCast-up-left-typed
    {A = A} {Tˡ = Tˡ} {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel}
    {ρ = ρ} {w = w} hTˡ hAˡ αˡ∈ L⊢ =
  cong-⊢⦂ refl refl refl
    (sym (extendρ-left-open {A = A} {Tˡ = Tˡ} {Rrel = Rrel} ρ))
    (⊢up (every (Ψˡ w)) (length-every (Ψˡ w))
      (cong-⊢⦂ refl refl refl
        (extendρ-left-open
          {A = A}
          {Tˡ = ｀ αˡ}
          {Rrel = sealedRel αˡ αʳ Rrel}
          ρ)
        L⊢)
      (instCast⊑-wt hTˡ hAˡ αˡ∈
        (every-member-conv αˡ (storeWf-dom< (wfΣˡ w) αˡ∈))))

instCast-up-right-typed :
  ∀ {B Tˡ Tʳ αˡ αʳ Rrel} {ρ : RelSub 0} {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} {downR : DownClosed Rrel}
    {w R} →
  (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
  (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
  Σʳ w ∋ˢ αʳ ⦂ Tʳ →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂
    substᵗ
      (rightᵗ
        (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
          (sealedRel αˡ αʳ Rrel)
          (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
      B →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
    R up (instCast⊑
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ})
    ⦂ substᵗ (rightᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) B
instCast-up-right-typed
    {B = B} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel}
    {ρ = ρ} {w = w} hTʳ hBʳ αʳ∈ R⊢ =
  cong-⊢⦂ refl refl refl
    (sym (extendρ-right-open {A = B} {Tʳ = Tʳ} {Rrel = Rrel} ρ))
    (⊢up (every (Ψʳ w)) (length-every (Ψʳ w))
      (cong-⊢⦂ refl refl refl
        (extendρ-right-open
          {A = B}
          {Tʳ = ｀ αʳ}
          {Rrel = sealedRel αˡ αʳ Rrel}
          ρ)
        R⊢)
      (instCast⊑-wt hTʳ hBʳ αʳ∈
        (every-member-conv αʳ (storeWf-dom< (wfΣʳ w) αʳ∈))))

instCast-down-left-typed :
  ∀ {A Tˡ Tʳ αˡ αʳ Rrel} {ρ : RelSub 0} {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} {downR : DownClosed Rrel}
    {w L} →
  (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
  (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
  Σˡ w ∋ˢ αˡ ⦂ Tˡ →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂
    substᵗ (leftᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) A →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    L down (instCast⊒
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ})
    ⦂ substᵗ
        (leftᵗ
          (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
            (sealedRel αˡ αʳ Rrel)
            (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
        A
instCast-down-left-typed
    {A = A} {Tˡ = Tˡ} {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel}
    {ρ = ρ} {w = w} hTˡ hAˡ αˡ∈ L⊢ =
  cong-⊢⦂ refl refl refl
    (sym
      (extendρ-left-open
        {A = A}
        {Tˡ = ｀ αˡ}
        {Rrel = sealedRel αˡ αʳ Rrel}
        ρ))
    (⊢down (every (Ψˡ w)) (length-every (Ψˡ w))
      (cong-⊢⦂ refl refl refl
        (extendρ-left-open {A = A} {Tˡ = Tˡ} {Rrel = Rrel} ρ)
        L⊢)
      (instCast⊒-wt hTˡ hAˡ αˡ∈
        (every-member-conv αˡ (storeWf-dom< (wfΣˡ w) αˡ∈))))

instCast-down-right-typed :
  ∀ {B Tˡ Tʳ αˡ αʳ Rrel} {ρ : RelSub 0} {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} {downR : DownClosed Rrel}
    {w R} →
  (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
  (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
  Σʳ w ∋ˢ αʳ ⦂ Tʳ →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂
    substᵗ (rightᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) B →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
    R down (instCast⊒
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ})
    ⦂ substᵗ
        (rightᵗ
          (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
            (sealedRel αˡ αʳ Rrel)
            (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
        B
instCast-down-right-typed
    {B = B} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel}
    {ρ = ρ} {w = w} hTʳ hBʳ αʳ∈ R⊢ =
  cong-⊢⦂ refl refl refl
    (sym
      (extendρ-right-open
        {A = B}
        {Tʳ = ｀ αʳ}
        {Rrel = sealedRel αˡ αʳ Rrel}
        ρ))
    (⊢down (every (Ψʳ w)) (length-every (Ψʳ w))
      (cong-⊢⦂ refl refl refl
        (extendρ-right-open {A = B} {Tʳ = Tʳ} {Rrel = Rrel} ρ)
        R⊢)
      (instCast⊒-wt hTʳ hBʳ αʳ∈
        (every-member-conv αʳ (storeWf-dom< (wfΣʳ w) αʳ∈))))

InstCastBridgeℰ⊑′ : Set₁
InstCastBridgeℰ⊑′ =
  ∀ {A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub 0}
    {p : A ⊑ B}
    {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (L R : Term) →
  ℰ (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
       (sealedRel αˡ αʳ Rrel)
       (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR))
    p n dir w L R →
  ℰ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w
    (L up (instCast⊑
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ}))
    (R up (instCast⊑
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ}))

InstCastBridgeℰ⊒′ : Set₁
InstCastBridgeℰ⊒′ =
  ∀ {A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub 0}
    {p : A ⊑ B}
    {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (L R : Term) →
  ℰ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w L R →
  ℰ (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
       (sealedRel αˡ αʳ Rrel)
       (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR))
    p n dir w
    (L down (instCast⊒
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ}))
    (R down (instCast⊒
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ}))

postulate
  instCast-bridge-ℰ⊑′-for-value : InstCastBridgeℰ⊑′
  instCast-bridge-ℰ⊒′-for-value : InstCastBridgeℰ⊒′

fun-app-ℰ :
  ∀ {A A′ B B′ n dir w V W M N} {ρ : RelSub 0}
    {pA : A ⊑ A′} {pB : B ⊑ B′} →
  𝒱 ρ (⊑-⇒ A A′ B B′ pA pB) n dir w V W →
  ℰ ρ pA (suc n) dir w M N →
  ℰ ρ pB (suc n) dir w (V · M) (W · N)
fun-app-ℰ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA} {pB = pB}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , M′ , M→M′ , rel′)) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , V · M′ , ξ-·₂ vV M→M′ ,
    ((⊢· V⊢′ (proj₁ (proj₁ rel′)) , ⊢· W⊢ N⊢) , lift tt))
  where
  V⊢′ :
    0 ∣ Ψˡ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ Σˡ′ ∣ [] ⊢
      V ⦂ substᵗ (leftᵗ ρ) (A ⇒ B)
  V⊢′ =
    wk⪰ˡ
      {w = w}
      {w′ = mkWorldˡ w Σˡ′ wfΣˡ′}
      {A = substᵗ (leftᵗ ρ) (A ⇒ B)}
      {V = V}
      (mkWorldˡ-⪰ (store-growth M→M′))
      V⊢
fun-app-ℰ {n = zero} {dir = ≼} {w = w} {V = V} {W = W}
    {M = M} {N = N} {ρ = ρ} {pB = pB}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , N↠blame))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , appR-blame-↠ vW N↠blame))
fun-app-ℰ {A = A} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pB = pB}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg ,
      N↠Warg , Varg))) with canonical-⇒ vV V⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≼} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg ,
      N↠Warg , Varg))) | fv-ƛ refl with V⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≼} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg ,
      N↠Warg , Varg))) | fv-ƛ refl | ⊢ƛ {M = Body} wfA Body⊢ =
  (⊢· (⊢ƛ {M = Body} wfA Body⊢) M⊢ , right-app-typed) ,
  inj₁ (Σˡ w , Ψˡ w , wfΣˡ w , substˣ-term (singleVarEnv M) Body ,
    id-step (β vM) ,
    (([]-wt Body⊢ M⊢ , right-app-typed) , lift tt))
  where
  right-app-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W · N ⦂ substᵗ (rightᵗ ρ) B′
  right-app-typed = ⊢· W⊢ N⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≼} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg ,
      N↠Warg , Varg))) | fv-up-↦ vU refl with V⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≼} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg ,
      N↠Warg , Varg))) | fv-up-↦ vU refl | ⊢up Φ lenΦ U⊢ (wt-↦ p⊢ q⊢) =
  (⊢· (⊢up Φ lenΦ U⊢ (wt-↦ p⊢ q⊢)) M⊢ , right-app-typed) ,
  inj₁ (Σˡ w , Ψˡ w , wfΣˡ w , _ , id-step (β-up-↦ vU vM) ,
    ((left-red-typed , right-app-typed) , lift tt))
  where
  right-app-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W · N ⦂ substᵗ (rightᵗ ρ) B′
  right-app-typed = ⊢· W⊢ N⊢

  left-red-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ _ ⦂ substᵗ (leftᵗ ρ) B
  left-red-typed = ⊢up Φ lenΦ (⊢· U⊢ (⊢down Φ lenΦ M⊢ p⊢)) q⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≼} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg ,
      N↠Warg , Varg))) | fv-down-↦ vU refl with V⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≼} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg ,
      N↠Warg , Varg))) | fv-down-↦ vU refl | ⊢down Φ lenΦ U⊢ (wt-↦ p⊢ q⊢) =
  (⊢· (⊢down Φ lenΦ U⊢ (wt-↦ p⊢ q⊢)) M⊢ , right-app-typed) ,
  inj₁ (Σˡ w , Ψˡ w , wfΣˡ w , _ , id-step (β-down-↦ vU vM) ,
    ((left-red-typed , right-app-typed) , lift tt))
  where
  right-app-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W · N ⦂ substᵗ (rightᵗ ρ) B′
  right-app-typed = ⊢· W⊢ N⊢

  left-red-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ _ ⦂ substᵗ (leftᵗ ρ) B
  left-red-typed = ⊢down Φ lenΦ (⊢· U⊢ (⊢up Φ lenΦ M⊢ p⊢)) q⊢

fun-app-ℰ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = suc k} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA} {pB = pB}
    Vfun@(vV , vW , (V⊢ , W⊢) , funsuc)
    ((M⊢ , N⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , M′ , M→M′ , rel′)) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , V · M′ , ξ-·₂ vV M→M′ ,
    fun-app-ℰ
      {ρ = ρ} {pA = pA} {pB = pB}
      (𝒱-monotone ρ _ _ (⊑-⇒ A A′ B B′ pA pB) k ≼
        (mkWorldˡ w Σˡ′ wfΣˡ′) V W
        (𝒱-⪰ ρ (⊑-⇒ A A′ B B′ pA pB)
          (mkWorldˡ-⪰ (store-growth M→M′)) Vfun))
      rel′)
fun-app-ℰ {n = suc k} {dir = ≼} {w = w} {V = V} {W = W}
    {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , funsuc)
    ((M⊢ , N⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , N↠blame))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , appR-blame-↠ vW N↠blame))
fun-app-ℰ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = suc k} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA} {pB = pB}
    Vfun@(vV , vW , (V⊢ , W⊢) , funsuc)
    ((M⊢ , N⊢) , inj₂ (inj₂
      (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg , N↠Warg , Varg))) =
  (left-app-typed , right-app-typed) ,
  inj₁ (Σˡ w , Ψˡ w , wfΣˡ w , Lβ , stepL , pulled)
  where
  funp : A ⇒ B ⊑ A′ ⇒ B′
  funp = ⊑-⇒ A A′ B B′ pA pB

  growʳ : Σʳ w ⊆ˢ Σʳ′
  growʳ = multi-store-growth N↠Warg

  Vfun↑ : 𝒱 ρ funp (suc k) ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) V W
  Vfun↑ = 𝒱-⪰ ρ funp (mkWorldʳ-⪰ growʳ) Vfun

  top-step :
    ∀ {w′} →
    w′ ⪰ (mkWorldʳ w Σʳ′ wfΣʳ′) →
    ∀ {V′ W′} →
    𝒱 ρ pA (suc k) ≼ w′ V′ W′ →
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ w′ ∣ (V · V′) —→ Σˡ w′ ∣ Lβ) ×
      (Σʳ w′ ∣ (W · W′) —→ Σʳ w′ ∣ Rβ) ×
      ℰ ρ pB (suc k) ≼ w′ Lβ Rβ
  top-step = proj₁ (proj₂ (proj₂ (proj₂ Vfun↑)))

  LβRβ :
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ (V · M) —→
       Σˡ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ Lβ) ×
      (Σʳ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ (W · Warg) —→
       Σʳ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ Rβ) ×
      ℰ ρ pB (suc k) ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Lβ Rβ
  LβRβ = top-step (mkWorldʳ-⪰ ⊆ˢ-refl) Varg

  Lβ : Term
  Lβ = proj₁ LβRβ

  Rβ : Term
  Rβ = proj₁ (proj₂ LβRβ)

  stepL : Σˡ w ∣ V · M —→ Σˡ w ∣ Lβ
  stepL = proj₁ (proj₂ (proj₂ LβRβ))

  stepR : Σʳ′ ∣ W · Warg —→ Σʳ′ ∣ Rβ
  stepR = proj₁ (proj₂ (proj₂ (proj₂ LβRβ)))

  body : ℰ ρ pB (suc k) ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Lβ Rβ
  body = proj₂ (proj₂ (proj₂ (proj₂ LβRβ)))

  left-app-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V · M ⦂ substᵗ (leftᵗ ρ) B
  left-app-typed = ⊢· V⊢ M⊢

  right-app-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W · N ⦂ substᵗ (rightᵗ ρ) B′
  right-app-typed = ⊢· W⊢ N⊢

  right-path : Σʳ w ∣ W · N —↠ Σʳ′ ∣ Rβ
  right-path =
    multi-trans
      (appR-↠ vW N↠Warg)
      ((W · Warg) —→⟨ stepR ⟩ Rβ ∎)

  pulled : ℰ ρ pB (suc k) ≼ w Lβ (W · N)
  pulled =
    ℰ-pull-≼-right-↠
      {ρ = ρ} {p = pB} {k = suc k} {w = w}
      (proj₁ (proj₁ body))
      right-app-typed
      right-path
      body

fun-app-ℰ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , N′ , N→N′ , rel′)) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , W · N′ , ξ-·₂ vW N→N′ ,
    ((⊢· V⊢ M⊢ , ⊢· W⊢′ (proj₂ (proj₁ rel′))) , lift tt))
  where
  W⊢′ :
    0 ∣ Ψʳ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ Σʳ′ ∣ [] ⊢
      W ⦂ substᵗ (rightᵗ ρ) (A′ ⇒ B′)
  W⊢′ =
    wk⪰ʳ
      {w = w}
      {w′ = mkWorldʳ w Σʳ′ wfΣʳ′}
      {A = substᵗ (rightᵗ ρ) (A′ ⇒ B′)}
      {V = W}
      (mkWorldʳ-⪰ (store-growth N→N′))
      W⊢
fun-app-ℰ {n = zero} {dir = ≽} {w = w} {V = V} {W = W}
    {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , N↠blame))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , appR-blame-↠ vW N↠blame))
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≽} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg ,
      M↠Warg , Varg))) with canonical-⇒ vW W⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≽} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg ,
      M↠Warg , Varg))) | fv-ƛ refl with W⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≽} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg ,
      M↠Warg , Varg))) | fv-ƛ refl | ⊢ƛ {M = Body} wfA Body⊢ =
  (left-app-typed , ⊢· (⊢ƛ {M = Body} wfA Body⊢) N⊢) ,
  inj₁ (Σʳ w , Ψʳ w , wfΣʳ w , substˣ-term (singleVarEnv N) Body ,
    id-step (β vN) ,
    ((left-app-typed , []-wt Body⊢ N⊢) , lift tt))
  where
  left-app-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V · M ⦂ substᵗ (leftᵗ ρ) B
  left-app-typed = ⊢· V⊢ M⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≽} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg ,
      M↠Warg , Varg))) | fv-up-↦ vU refl with W⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≽} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg ,
      M↠Warg , Varg))) | fv-up-↦ vU refl | ⊢up Φ lenΦ U⊢ (wt-↦ p⊢ q⊢) =
  (left-app-typed , ⊢· (⊢up Φ lenΦ U⊢ (wt-↦ p⊢ q⊢)) N⊢) ,
  inj₁ (Σʳ w , Ψʳ w , wfΣʳ w , _ , id-step (β-up-↦ vU vN) ,
    ((left-app-typed , right-red-typed) , lift tt))
  where
  left-app-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V · M ⦂ substᵗ (leftᵗ ρ) B
  left-app-typed = ⊢· V⊢ M⊢

  right-red-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ _ ⦂ substᵗ (rightᵗ ρ) B′
  right-red-typed = ⊢up Φ lenΦ (⊢· U⊢ (⊢down Φ lenΦ N⊢ p⊢)) q⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≽} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg ,
      M↠Warg , Varg))) | fv-down-↦ vU refl with W⊢
fun-app-ℰ {B = B} {B′ = B′} {n = zero} {dir = ≽} {w = w}
    {V = V} {W = W} {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , fun0)
    ((M⊢ , N⊢) , inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg ,
      M↠Warg , Varg))) | fv-down-↦ vU refl | ⊢down Φ lenΦ U⊢ (wt-↦ p⊢ q⊢) =
  (left-app-typed , ⊢· (⊢down Φ lenΦ U⊢ (wt-↦ p⊢ q⊢)) N⊢) ,
  inj₁ (Σʳ w , Ψʳ w , wfΣʳ w , _ , id-step (β-down-↦ vU vN) ,
    ((left-app-typed , right-red-typed) , lift tt))
  where
  left-app-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V · M ⦂ substᵗ (leftᵗ ρ) B
  left-app-typed = ⊢· V⊢ M⊢

  right-red-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ _ ⦂ substᵗ (rightᵗ ρ) B′
  right-red-typed = ⊢down Φ lenΦ (⊢· U⊢ (⊢up Φ lenΦ N⊢ p⊢)) q⊢

fun-app-ℰ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = suc k} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA} {pB = pB}
    Vfun@(vV , vW , (V⊢ , W⊢) , funsuc)
    ((M⊢ , N⊢) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , N′ , N→N′ , rel′)) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , W · N′ , ξ-·₂ vW N→N′ ,
    fun-app-ℰ
      {ρ = ρ} {pA = pA} {pB = pB}
      (𝒱-monotone ρ _ _ (⊑-⇒ A A′ B B′ pA pB) k ≽
        (mkWorldʳ w Σʳ′ wfΣʳ′) V W
        (𝒱-⪰ ρ (⊑-⇒ A A′ B B′ pA pB)
          (mkWorldʳ-⪰ (store-growth N→N′)) Vfun))
      rel′)
fun-app-ℰ {n = suc k} {dir = ≽} {w = w} {V = V} {W = W}
    {M = M} {N = N} {ρ = ρ}
    Vfun@(vV , vW , (V⊢ , W⊢) , funsuc)
    ((M⊢ , N⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , N↠blame))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , appR-blame-↠ vW N↠blame))
fun-app-ℰ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = suc k} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA} {pB = pB}
    Vfun@(vV , vW , (V⊢ , W⊢) , funsuc)
    ((M⊢ , N⊢) , inj₂ (inj₂
      (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg , M↠Warg , Varg))) =
  ℰ-expand-≽-right {ρ = ρ} {p = pB} {k = suc k} {w = w}
    left-app-typed
    right-app-typed
    stepR
    (ℰ-pull-≽-left-↠ {ρ = ρ} {p = pB} {k = suc k} {w = w}
      left-app-typed
      (proj₂ (proj₁ body))
      left-path
      body)
  where
  funp : A ⇒ B ⊑ A′ ⇒ B′
  funp = ⊑-⇒ A A′ B B′ pA pB

  growˡ : Σˡ w ⊆ˢ Σˡ′
  growˡ = multi-store-growth M↠Warg

  Vfun↑ : 𝒱 ρ funp (suc k) ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) V W
  Vfun↑ = 𝒱-⪰ ρ funp (mkWorldˡ-⪰ growˡ) Vfun

  top-step :
    ∀ {w′} →
    w′ ⪰ (mkWorldˡ w Σˡ′ wfΣˡ′) →
    ∀ {V′ W′} →
    𝒱 ρ pA (suc k) ≽ w′ V′ W′ →
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ w′ ∣ (V · V′) —→ Σˡ w′ ∣ Lβ) ×
      (Σʳ w′ ∣ (W · W′) —→ Σʳ w′ ∣ Rβ) ×
      ℰ ρ pB (suc k) ≽ w′ Lβ Rβ
  top-step = proj₁ (proj₂ (proj₂ (proj₂ Vfun↑)))

  LβRβ :
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ (V · Warg) —→
       Σˡ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ Lβ) ×
      (Σʳ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ (W · N) —→
       Σʳ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ Rβ) ×
      ℰ ρ pB (suc k) ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Lβ Rβ
  LβRβ = top-step (mkWorldˡ-⪰ ⊆ˢ-refl) Varg

  Lβ : Term
  Lβ = proj₁ LβRβ

  Rβ : Term
  Rβ = proj₁ (proj₂ LβRβ)

  stepL : Σˡ′ ∣ V · Warg —→ Σˡ′ ∣ Lβ
  stepL = proj₁ (proj₂ (proj₂ LβRβ))

  stepR : Σʳ w ∣ W · N —→ Σʳ w ∣ Rβ
  stepR = proj₁ (proj₂ (proj₂ (proj₂ LβRβ)))

  body : ℰ ρ pB (suc k) ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Lβ Rβ
  body = proj₂ (proj₂ (proj₂ (proj₂ LβRβ)))

  left-app-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V · M ⦂ substᵗ (leftᵗ ρ) B
  left-app-typed = ⊢· V⊢ M⊢

  right-app-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W · N ⦂ substᵗ (rightᵗ ρ) B′
  right-app-typed = ⊢· W⊢ N⊢

  left-path : Σˡ w ∣ V · M —↠ Σˡ′ ∣ Lβ
  left-path =
    multi-trans
      (appR-↠ vV M↠Warg)
      ((V · Warg) —→⟨ stepL ⟩ Lβ ∎)

InstCastBridge𝒱⇒ℰ⊑′ : Set₁
InstCastBridge𝒱⇒ℰ⊑′ =
  ∀ {A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub 0}
    {p : A ⊑ B}
    {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (V W : Term) →
  𝒱 (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
       (sealedRel αˡ αʳ Rrel)
       (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR))
    p n dir w V W →
  ℰ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p (suc n) dir w
    (V up (instCast⊑
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ}))
    (W up (instCast⊑
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ}))

postulate
  instCast-bridge-𝒱⇒ℰ⊑′-fallback : InstCastBridge𝒱⇒ℰ⊑′

instCast-bridge-𝒱⇒ℰ⊑′ : InstCastBridge𝒱⇒ℰ⊑′
instCast-bridge-𝒱⇒ℰ⊑′
    {A = ＇ zero} {B = ＇ zero} {n = n} {dir = ≼} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = ⊑-＇ zero} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W
    (vV , vW , (V⊢ , W⊢) , lift (V′ , W′ , pˡ , pʳ , refl , refl , RrelVW)) =
  (left-typed , right-typed) ,
  inj₁ (Σˡ w , Ψˡ w , wfΣˡ w , V′ ,
    id-step (seal-unseal vV′) , right-unsealed)
  where
  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (V′ down seal (id Tˡ) αˡ) up (unseal αˡ (id Tˡ))
      ⦂ substᵗ (leftᵗ ρApp) (＇ zero)
  left-typed =
    instCast-up-left-typed
      {A = ＇ zero} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {L = V′ down seal (id Tˡ) αˡ}
      hTˡ hAˡ αˡ∈ V⊢

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      (W′ down seal (id Tʳ) αʳ) up (unseal αʳ (id Tʳ))
      ⦂ substᵗ (rightᵗ ρApp) (＇ zero)
  right-typed =
    instCast-up-right-typed
      {B = ＇ zero} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {R = W′ down seal (id Tʳ) αʳ}
      hTʳ hBʳ αʳ∈ W⊢

  vV′ : Value V′
  vV′ = seal-value-inv vV

  vW′ : Value W′
  vW′ = seal-value-inv vW

  V′⊢ : 0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V′ ⦂ Tˡ
  V′⊢ = seal-typed-inv (storeWf-unique (wfΣˡ w)) αˡ∈ V⊢

  W′⊢ : 0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W′ ⦂ Tʳ
  W′⊢ = seal-typed-inv (storeWf-unique (wfΣʳ w)) αʳ∈ W⊢

  rep-𝒱 : (m : ℕ) → Rrel m ≼ V′ W′ → 𝒱 ρApp (⊑-＇ zero) m ≼ w V′ W′
  rep-𝒱 m rel = vV′ , vW′ , (V′⊢ , W′⊢) , lift rel

  rep-ℰ′ : (m : ℕ) → Rrel m ≼ V′ W′ → ℰ ρApp (⊑-＇ zero) m ≼ w V′ W′
  rep-ℰ′ zero rel =
    𝒱⇒ℰ-zero
      {A = ＇ zero} {B = ＇ zero} {ρ = ρApp} {p = ⊑-＇ zero}
      {dir = ≼} {w = w} {V = V′} {W = W′}
      (rep-𝒱 zero rel)
  rep-ℰ′ (suc k) rel =
    𝒱⇒ℰ
      {A = ＇ zero} {B = ＇ zero} {ρ = ρApp} {p = ⊑-＇ zero}
      {n = k} {dir = ≼} {w = w} {V = V′} {W = W′}
      (rep-𝒱 k (downR rel))

  rep-ℰ : ℰ ρApp (⊑-＇ zero) n ≼ w V′ W′
  rep-ℰ = rep-ℰ′ n RrelVW

  right-unsealed :
    ℰ ρApp (⊑-＇ zero) n ≼ w V′ ((W′ down seal (id Tʳ) αʳ) up (unseal αʳ (id Tʳ)))
  right-unsealed =
    ℰ-expand-≼-right
      {ρ = ρApp} {p = ⊑-＇ zero} {k = n} {w = w}
      V′⊢ right-typed (id-step (seal-unseal vW′)) rep-ℰ
instCast-bridge-𝒱⇒ℰ⊑′
    {A = ＇ zero} {B = ＇ zero} {n = n} {dir = ≽} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = ⊑-＇ zero} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W
    (vV , vW , (V⊢ , W⊢) , lift (V′ , W′ , pˡ , pʳ , refl , refl , RrelVW)) =
  (left-typed , right-typed) ,
  inj₁ (Σʳ w , Ψʳ w , wfΣʳ w , W′ ,
    id-step (seal-unseal vW′) , left-unsealed)
  where
  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (V′ down seal (id Tˡ) αˡ) up (unseal αˡ (id Tˡ))
      ⦂ substᵗ (leftᵗ ρApp) (＇ zero)
  left-typed =
    instCast-up-left-typed
      {A = ＇ zero} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {L = V′ down seal (id Tˡ) αˡ}
      hTˡ hAˡ αˡ∈ V⊢

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      (W′ down seal (id Tʳ) αʳ) up (unseal αʳ (id Tʳ))
      ⦂ substᵗ (rightᵗ ρApp) (＇ zero)
  right-typed =
    instCast-up-right-typed
      {B = ＇ zero} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {R = W′ down seal (id Tʳ) αʳ}
      hTʳ hBʳ αʳ∈ W⊢

  vV′ : Value V′
  vV′ = seal-value-inv vV

  vW′ : Value W′
  vW′ = seal-value-inv vW

  V′⊢ : 0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V′ ⦂ Tˡ
  V′⊢ = seal-typed-inv (storeWf-unique (wfΣˡ w)) αˡ∈ V⊢

  W′⊢ : 0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W′ ⦂ Tʳ
  W′⊢ = seal-typed-inv (storeWf-unique (wfΣʳ w)) αʳ∈ W⊢

  rep-𝒱 : (m : ℕ) → Rrel m ≽ V′ W′ → 𝒱 ρApp (⊑-＇ zero) m ≽ w V′ W′
  rep-𝒱 m rel = vV′ , vW′ , (V′⊢ , W′⊢) , lift rel

  rep-ℰ′ : (m : ℕ) → Rrel m ≽ V′ W′ → ℰ ρApp (⊑-＇ zero) m ≽ w V′ W′
  rep-ℰ′ zero rel =
    𝒱⇒ℰ-zero
      {A = ＇ zero} {B = ＇ zero} {ρ = ρApp} {p = ⊑-＇ zero}
      {dir = ≽} {w = w} {V = V′} {W = W′}
      (rep-𝒱 zero rel)
  rep-ℰ′ (suc k) rel =
    𝒱⇒ℰ
      {A = ＇ zero} {B = ＇ zero} {ρ = ρApp} {p = ⊑-＇ zero}
      {n = k} {dir = ≽} {w = w} {V = V′} {W = W′}
      (rep-𝒱 k (downR rel))

  rep-ℰ : ℰ ρApp (⊑-＇ zero) n ≽ w V′ W′
  rep-ℰ = rep-ℰ′ n RrelVW

  left-unsealed :
    ℰ ρApp (⊑-＇ zero) n ≽ w ((V′ down seal (id Tˡ) αˡ) up (unseal αˡ (id Tˡ))) W′
  left-unsealed =
    ℰ-expand-≽-left
      {ρ = ρApp} {p = ⊑-＇ zero} {k = n} {w = w}
      left-typed W′⊢ (id-step (seal-unseal vV′)) rep-ℰ
instCast-bridge-𝒱⇒ℰ⊑′
    {A = ‵ `ℕ} {B = ‵ `ℕ} {n = n} {dir = ≼} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = ⊑-‵ `ℕ} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W
    Vrel@(vV , vW , (V⊢ , W⊢) , nat-rel) =
  (left-typed , right-typed) ,
  inj₁ (Σˡ w , Ψˡ w , wfΣˡ w , V , id-step (id-up vV) , right-id)
  where
  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  VrelApp : 𝒱 ρApp (⊑-‵ `ℕ) n ≼ w V W
  VrelApp = Vrel

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      V up (id (‵ `ℕ))
      ⦂ substᵗ (leftᵗ ρApp) (‵ `ℕ)
  left-typed =
    instCast-up-left-typed
      {A = ‵ `ℕ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {L = V}
      hTˡ hAˡ αˡ∈ V⊢

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      W up (id (‵ `ℕ))
      ⦂ substᵗ (rightᵗ ρApp) (‵ `ℕ)
  right-typed =
    instCast-up-right-typed
      {B = ‵ `ℕ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {R = W}
      hTʳ hBʳ αʳ∈ W⊢

  rep-ℰ′ :
    (m : ℕ) →
    𝒱 ρApp (⊑-‵ `ℕ) m ≼ w V W →
    ℰ ρApp (⊑-‵ `ℕ) m ≼ w V W
  rep-ℰ′ zero rel =
    𝒱⇒ℰ-zero
      {ρ = ρApp} {p = ⊑-‵ `ℕ} {dir = ≼} {w = w} {V = V} {W = W}
      rel
  rep-ℰ′ (suc k) rel =
    𝒱⇒ℰ
      {ρ = ρApp} {p = ⊑-‵ `ℕ} {n = k} {dir = ≼}
      {w = w} {V = V} {W = W}
      (𝒱-monotone ρApp (‵ `ℕ) (‵ `ℕ) (⊑-‵ `ℕ) k ≼ w V W rel)

  rep-ℰ : ℰ ρApp (⊑-‵ `ℕ) n ≼ w V W
  rep-ℰ = rep-ℰ′ n VrelApp

  right-id : ℰ ρApp (⊑-‵ `ℕ) n ≼ w V (W up (id (‵ `ℕ)))
  right-id =
    ℰ-expand-≼-right
      {ρ = ρApp} {p = ⊑-‵ `ℕ} {k = n} {w = w}
      V⊢ right-typed (id-step (id-up vW)) rep-ℰ
instCast-bridge-𝒱⇒ℰ⊑′
    {A = ‵ `ℕ} {B = ‵ `ℕ} {n = n} {dir = ≽} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = ⊑-‵ `ℕ} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W
    Vrel@(vV , vW , (V⊢ , W⊢) , nat-rel) =
  (left-typed , right-typed) ,
  inj₁ (Σʳ w , Ψʳ w , wfΣʳ w , W , id-step (id-up vW) , left-id)
  where
  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  VrelApp : 𝒱 ρApp (⊑-‵ `ℕ) n ≽ w V W
  VrelApp = Vrel

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      V up (id (‵ `ℕ))
      ⦂ substᵗ (leftᵗ ρApp) (‵ `ℕ)
  left-typed =
    instCast-up-left-typed
      {A = ‵ `ℕ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {L = V}
      hTˡ hAˡ αˡ∈ V⊢

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      W up (id (‵ `ℕ))
      ⦂ substᵗ (rightᵗ ρApp) (‵ `ℕ)
  right-typed =
    instCast-up-right-typed
      {B = ‵ `ℕ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {R = W}
      hTʳ hBʳ αʳ∈ W⊢

  rep-ℰ′ :
    (m : ℕ) →
    𝒱 ρApp (⊑-‵ `ℕ) m ≽ w V W →
    ℰ ρApp (⊑-‵ `ℕ) m ≽ w V W
  rep-ℰ′ zero rel =
    𝒱⇒ℰ-zero
      {ρ = ρApp} {p = ⊑-‵ `ℕ} {dir = ≽} {w = w} {V = V} {W = W}
      rel
  rep-ℰ′ (suc k) rel =
    𝒱⇒ℰ
      {ρ = ρApp} {p = ⊑-‵ `ℕ} {n = k} {dir = ≽}
      {w = w} {V = V} {W = W}
      (𝒱-monotone ρApp (‵ `ℕ) (‵ `ℕ) (⊑-‵ `ℕ) k ≽ w V W rel)

  rep-ℰ : ℰ ρApp (⊑-‵ `ℕ) n ≽ w V W
  rep-ℰ = rep-ℰ′ n VrelApp

  left-id : ℰ ρApp (⊑-‵ `ℕ) n ≽ w (V up (id (‵ `ℕ))) W
  left-id =
    ℰ-expand-≽-left
      {ρ = ρApp} {p = ⊑-‵ `ℕ} {k = n} {w = w}
      left-typed W⊢ (id-step (id-up vV)) rep-ℰ
instCast-bridge-𝒱⇒ℰ⊑′
    {A = ‵ `𝔹} {B = ‵ `𝔹} {p = ⊑-‵ `𝔹}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W
    (vV , vW , (V⊢ , W⊢) , lift ())
instCast-bridge-𝒱⇒ℰ⊑′
    {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ} {n = n} {dir = dir} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = ⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ (wf⇒ hAˡ hBˡ) (wf⇒ hAʳ hBʳ)
    αˡ∈ αʳ∈ V W Vrel@(vV , vW , (V⊢ , W⊢) , fun-rel) =
  𝒱⇒ℰ
    {ρ = ρApp}
    {p = ⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB}
    {n = n}
    {dir = dir}
    {w = w}
    {V = V up castL}
    {W = W up castR}
    casted-𝒱
  where
  ρSeal : RelSub 0
  ρSeal =
    extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
      (sealedRel αˡ αʳ Rrel)
      (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)

  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  arrow-p : Aˡ ⇒ Bˡ ⊑ Aʳ ⇒ Bʳ
  arrow-p = ⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB

  castDomL : Down
  castDomL =
    instCast⊒
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) Aˡ}
      {α = αˡ}

  castDomR : Down
  castDomR =
    instCast⊒
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) Aʳ}
      {α = αʳ}

  castCodL : Up
  castCodL =
    instCast⊑
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) Bˡ}
      {α = αˡ}

  castCodR : Up
  castCodR =
    instCast⊑
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) Bʳ}
      {α = αʳ}

  castL : Up
  castL =
    instCast⊑
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) (Aˡ ⇒ Bˡ)}
      {α = αˡ}

  castR : Up
  castR =
    instCast⊑
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) (Aʳ ⇒ Bʳ)}
      {α = αʳ}

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      V up castL ⦂ substᵗ (leftᵗ ρApp) (Aˡ ⇒ Bˡ)
  left-typed =
    instCast-up-left-typed
      {A = Aˡ ⇒ Bˡ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {L = V}
      hTˡ (wf⇒ hAˡ hBˡ) αˡ∈ V⊢

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      W up castR ⦂ substᵗ (rightᵗ ρApp) (Aʳ ⇒ Bʳ)
  right-typed =
    instCast-up-right-typed
      {B = Aʳ ⇒ Bʳ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {R = W}
      hTʳ (wf⇒ hAʳ hBʳ) αʳ∈ W⊢

  casted-𝒱′ :
    (m : ℕ) →
    𝒱 ρSeal arrow-p m dir w V W →
    𝒱 ρApp arrow-p m dir w (V up castL) (W up castR)
  casted-𝒱′ zero rel =
    ReductionFresh._up_ (proj₁ rel) ReductionFresh._↦_ ,
    ReductionFresh._up_ (proj₁ (proj₂ rel)) ReductionFresh._↦_ ,
    (left-typed , right-typed) ,
    lift tt
  casted-𝒱′ (suc k) rel =
    ReductionFresh._up_ (proj₁ rel) ReductionFresh._↦_ ,
    ReductionFresh._up_ (proj₁ (proj₂ rel)) ReductionFresh._↦_ ,
    (left-typed , right-typed) ,
    FunAll→𝒱′ (app-top , all-rest)
    where
    rel↓ : 𝒱 ρSeal arrow-p k dir w V W
    rel↓ = 𝒱-monotone ρSeal _ _ arrow-p k dir w V W rel

    rest-𝒱 : 𝒱 ρApp arrow-p k dir w (V up castL) (W up castR)
    rest-𝒱 = casted-𝒱′ k rel↓

    all-rest :
      FunAll ρApp k pA pB dir w (V up castL) (W up castR)
    all-rest = 𝒱′→FunAll (proj₂ (proj₂ (proj₂ rest-𝒱)))

    app-top :
      ∀ {w′} →
      w′ ⪰ w →
      ∀ {V′ W′} →
      𝒱 ρApp pA (suc k) dir w′ V′ W′ →
      Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
        (Σˡ w′ ∣ ((V up castL) · V′) —→ Σˡ w′ ∣ Lβ) ×
        (Σʳ w′ ∣ ((W up castR) · W′) —→ Σʳ w′ ∣ Rβ) ×
        ℰ ρApp pB (suc k) dir w′ Lβ Rβ
    app-top {w′ = w′} w′⪰ {V′ = V′} {W′ = W′} arg =
      Lβ , Rβ ,
      id-step (β-up-↦ (proj₁ (𝒱-⪰ ρSeal arrow-p w′⪰ rel))
                      (proj₁ arg)) ,
      id-step (β-up-↦ (proj₁ (proj₂ (𝒱-⪰ ρSeal arrow-p w′⪰ rel)))
                      (proj₁ (proj₂ arg))) ,
      cod-up
      where
      Lβ : Term
      Lβ = (V · (V′ down castDomL)) up castCodL

      Rβ : Term
      Rβ = (W · (W′ down castDomR)) up castCodR

      fun′ : 𝒱 ρSeal arrow-p k dir w′ V W
      fun′ =
        𝒱-monotone ρSeal _ _ arrow-p k dir w′ V W
          (𝒱-⪰ ρSeal arrow-p w′⪰ rel)

      arg-real :
        ℰ ρApp pA (suc k) dir w′ V′ W′
      arg-real =
        𝒱⇒ℰ
          {ρ = ρApp} {p = pA} {n = k} {dir = dir}
          {w = w′} {V = V′} {W = W′}
          (𝒱-monotone ρApp Aˡ Aʳ pA k dir w′ V′ W′ arg)

      arg-down :
        ℰ ρSeal pA (suc k) dir w′
          (V′ down castDomL)
          (W′ down castDomR)
      arg-down =
        instCast-bridge-ℰ⊒′-for-value
          {A = Aˡ} {B = Aʳ} {n = suc k} {dir = dir} {w = w′}
          {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
          {ρ = ρ} {p = pA} {pT = pT}
          {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
          {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
          Rrel downR
          (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ w′⪰))
          (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ w′⪰))
          (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ w′⪰))
          (WfTy-weakenˢ hAʳ (_⪰_.growΨʳ w′⪰))
          (wkLookupˢ (_⪰_.growˡ w′⪰) αˡ∈)
          (wkLookupˢ (_⪰_.growʳ w′⪰) αʳ∈)
          V′ W′
          arg-real

      app-rel :
        ℰ ρSeal pB (suc k) dir w′
          (V · (V′ down castDomL))
          (W · (W′ down castDomR))
      app-rel = fun-app-ℰ fun′ arg-down

      cod-up :
        ℰ ρApp pB (suc k) dir w′ Lβ Rβ
      cod-up =
        instCast-bridge-ℰ⊑′-for-value
          {A = Bˡ} {B = Bʳ} {n = suc k} {dir = dir} {w = w′}
          {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
          {ρ = ρ} {p = pB} {pT = pT}
          {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
          {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
          Rrel downR
          (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ w′⪰))
          (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ w′⪰))
          (WfTy-weakenˢ hBˡ (_⪰_.growΨˡ w′⪰))
          (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ w′⪰))
          (wkLookupˢ (_⪰_.growˡ w′⪰) αˡ∈)
          (wkLookupˢ (_⪰_.growʳ w′⪰) αʳ∈)
          (V · (V′ down castDomL))
          (W · (W′ down castDomR))
          app-rel

  casted-𝒱 : 𝒱 ρApp arrow-p n dir w (V up castL) (W up castR)
  casted-𝒱 = casted-𝒱′ n Vrel
instCast-bridge-𝒱⇒ℰ⊑′ Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W Vrel =
  instCast-bridge-𝒱⇒ℰ⊑′-fallback
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W Vrel

InstCastBridge𝒱⇒ℰ⊒′ : Set₁
InstCastBridge𝒱⇒ℰ⊒′ =
  ∀ {A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub 0}
    {p : A ⊑ B}
    {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (V W : Term) →
  𝒱 (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w V W →
  ℰ (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
       (sealedRel αˡ αʳ Rrel)
       (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR))
    p (suc n) dir w
    (V down (instCast⊒
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ}))
    (W down (instCast⊒
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ}))

postulate
  instCast-bridge-𝒱⇒ℰ⊒′-fallback : InstCastBridge𝒱⇒ℰ⊒′

instCast-bridge-𝒱⇒ℰ⊒′ : InstCastBridge𝒱⇒ℰ⊒′
instCast-bridge-𝒱⇒ℰ⊒′
    {A = ＇ zero} {B = ＇ zero} {n = n} {dir = dir} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = ⊑-＇ zero} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W
    (vV , vW , (V⊢ , W⊢) , lift RrelVW) =
  𝒱⇒ℰ
    {ρ = ρSeal} {p = ⊑-＇ zero} {n = n} {dir = dir}
    {w = w} {V = V down seal (id Tˡ) αˡ} {W = W down seal (id Tʳ) αʳ}
    sealed-𝒱
  where
  ρSeal : RelSub 0
  ρSeal =
    extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
      (sealedRel αˡ αʳ Rrel)
      (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)

  V↓⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V down seal (id Tˡ) αˡ ⦂
      substᵗ (leftᵗ ρSeal) (＇ zero)
  V↓⊢ =
    instCast-down-left-typed
      {A = ＇ zero} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {L = V}
      hTˡ hAˡ αˡ∈ V⊢

  W↓⊢ :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W down seal (id Tʳ) αʳ ⦂
      substᵗ (rightᵗ ρSeal) (＇ zero)
  W↓⊢ =
    instCast-down-right-typed
      {B = ＇ zero} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {R = W}
      hTʳ hBʳ αʳ∈ W⊢

  sealed-𝒱 :
    𝒱 ρSeal (⊑-＇ zero) n dir w
      (V down seal (id Tˡ) αˡ)
      (W down seal (id Tʳ) αʳ)
  sealed-𝒱 =
    ReductionFresh._down_ vV ReductionFresh.seal ,
    ReductionFresh._down_ vW ReductionFresh.seal ,
    (V↓⊢ , W↓⊢) ,
    lift (V , W , id Tˡ , id Tʳ , refl , refl , RrelVW)
instCast-bridge-𝒱⇒ℰ⊒′
    {A = ‵ `ℕ} {B = ‵ `ℕ} {n = n} {dir = ≼} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = ⊑-‵ `ℕ} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W
    Vrel@(vV , vW , (V⊢ , W⊢) , nat-rel) =
  (left-typed , right-typed) ,
  inj₁ (Σˡ w , Ψˡ w , wfΣˡ w , V , id-step (id-down vV) , right-id)
  where
  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  ρSeal : RelSub 0
  ρSeal =
    extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
      (sealedRel αˡ αʳ Rrel)
      (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      V down id (‵ `ℕ) ⦂ substᵗ (leftᵗ ρSeal) (‵ `ℕ)
  left-typed =
    instCast-down-left-typed
      {A = ‵ `ℕ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {L = V}
      hTˡ hAˡ αˡ∈ V⊢

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      W down id (‵ `ℕ) ⦂ substᵗ (rightᵗ ρSeal) (‵ `ℕ)
  right-typed =
    instCast-down-right-typed
      {B = ‵ `ℕ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {R = W}
      hTʳ hBʳ αʳ∈ W⊢

  VrelSeal : 𝒱 ρSeal (⊑-‵ `ℕ) n ≼ w V W
  VrelSeal = Vrel

  rep-ℰ′ :
    (m : ℕ) →
    𝒱 ρSeal (⊑-‵ `ℕ) m ≼ w V W →
    ℰ ρSeal (⊑-‵ `ℕ) m ≼ w V W
  rep-ℰ′ zero rel =
    𝒱⇒ℰ-zero
      {ρ = ρSeal} {p = ⊑-‵ `ℕ} {dir = ≼} {w = w} {V = V} {W = W}
      rel
  rep-ℰ′ (suc k) rel =
    𝒱⇒ℰ
      {ρ = ρSeal} {p = ⊑-‵ `ℕ} {n = k} {dir = ≼}
      {w = w} {V = V} {W = W}
      (𝒱-monotone ρSeal (‵ `ℕ) (‵ `ℕ) (⊑-‵ `ℕ) k ≼ w V W rel)

  rep-ℰ : ℰ ρSeal (⊑-‵ `ℕ) n ≼ w V W
  rep-ℰ = rep-ℰ′ n VrelSeal

  right-id :
    ℰ ρSeal (⊑-‵ `ℕ) n ≼ w V (W down id (‵ `ℕ))
  right-id =
    ℰ-expand-≼-right
      {ρ = ρSeal} {p = ⊑-‵ `ℕ} {k = n} {w = w}
      V⊢ right-typed (id-step (id-down vW)) rep-ℰ
instCast-bridge-𝒱⇒ℰ⊒′
    {A = ‵ `ℕ} {B = ‵ `ℕ} {n = n} {dir = ≽} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = ⊑-‵ `ℕ} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W
    Vrel@(vV , vW , (V⊢ , W⊢) , nat-rel) =
  (left-typed , right-typed) ,
  inj₁ (Σʳ w , Ψʳ w , wfΣʳ w , W , id-step (id-down vW) , left-id)
  where
  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  ρSeal : RelSub 0
  ρSeal =
    extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
      (sealedRel αˡ αʳ Rrel)
      (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      V down id (‵ `ℕ) ⦂ substᵗ (leftᵗ ρSeal) (‵ `ℕ)
  left-typed =
    instCast-down-left-typed
      {A = ‵ `ℕ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {L = V}
      hTˡ hAˡ αˡ∈ V⊢

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      W down id (‵ `ℕ) ⦂ substᵗ (rightᵗ ρSeal) (‵ `ℕ)
  right-typed =
    instCast-down-right-typed
      {B = ‵ `ℕ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {R = W}
      hTʳ hBʳ αʳ∈ W⊢

  VrelSeal : 𝒱 ρSeal (⊑-‵ `ℕ) n ≽ w V W
  VrelSeal = Vrel

  rep-ℰ′ :
    (m : ℕ) →
    𝒱 ρSeal (⊑-‵ `ℕ) m ≽ w V W →
    ℰ ρSeal (⊑-‵ `ℕ) m ≽ w V W
  rep-ℰ′ zero rel =
    𝒱⇒ℰ-zero
      {ρ = ρSeal} {p = ⊑-‵ `ℕ} {dir = ≽} {w = w} {V = V} {W = W}
      rel
  rep-ℰ′ (suc k) rel =
    𝒱⇒ℰ
      {ρ = ρSeal} {p = ⊑-‵ `ℕ} {n = k} {dir = ≽}
      {w = w} {V = V} {W = W}
      (𝒱-monotone ρSeal (‵ `ℕ) (‵ `ℕ) (⊑-‵ `ℕ) k ≽ w V W rel)

  rep-ℰ : ℰ ρSeal (⊑-‵ `ℕ) n ≽ w V W
  rep-ℰ = rep-ℰ′ n VrelSeal

  left-id :
    ℰ ρSeal (⊑-‵ `ℕ) n ≽ w (V down id (‵ `ℕ)) W
  left-id =
    ℰ-expand-≽-left
      {ρ = ρSeal} {p = ⊑-‵ `ℕ} {k = n} {w = w}
      left-typed W⊢ (id-step (id-down vV)) rep-ℰ
instCast-bridge-𝒱⇒ℰ⊒′
    {A = ‵ `𝔹} {B = ‵ `𝔹} {p = ⊑-‵ `𝔹}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W
    (vV , vW , (V⊢ , W⊢) , lift ())
instCast-bridge-𝒱⇒ℰ⊒′
    {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ} {n = n} {dir = dir} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = ⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ (wf⇒ hAˡ hBˡ) (wf⇒ hAʳ hBʳ)
    αˡ∈ αʳ∈ V W Vrel@(vV , vW , (V⊢ , W⊢) , fun-rel) =
  𝒱⇒ℰ
    {ρ = ρSeal}
    {p = ⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB}
    {n = n}
    {dir = dir}
    {w = w}
    {V = V down castL}
    {W = W down castR}
    casted-𝒱
  where
  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  ρSeal : RelSub 0
  ρSeal =
    extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
      (sealedRel αˡ αʳ Rrel)
      (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)

  arrow-p : Aˡ ⇒ Bˡ ⊑ Aʳ ⇒ Bʳ
  arrow-p = ⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB

  castDomL : Up
  castDomL =
    instCast⊑
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) Aˡ}
      {α = αˡ}

  castDomR : Up
  castDomR =
    instCast⊑
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) Aʳ}
      {α = αʳ}

  castCodL : Down
  castCodL =
    instCast⊒
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) Bˡ}
      {α = αˡ}

  castCodR : Down
  castCodR =
    instCast⊒
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) Bʳ}
      {α = αʳ}

  castL : Down
  castL =
    instCast⊒
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) (Aˡ ⇒ Bˡ)}
      {α = αˡ}

  castR : Down
  castR =
    instCast⊒
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) (Aʳ ⇒ Bʳ)}
      {α = αʳ}

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      V down castL ⦂ substᵗ (leftᵗ ρSeal) (Aˡ ⇒ Bˡ)
  left-typed =
    instCast-down-left-typed
      {A = Aˡ ⇒ Bˡ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {L = V}
      hTˡ (wf⇒ hAˡ hBˡ) αˡ∈ V⊢

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      W down castR ⦂ substᵗ (rightᵗ ρSeal) (Aʳ ⇒ Bʳ)
  right-typed =
    instCast-down-right-typed
      {B = Aʳ ⇒ Bʳ} {Tˡ = Tˡ} {Tʳ = Tʳ}
      {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
      {pT = pT} {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
      {wfαˡ = wfαˡ} {wfαʳ = wfαʳ} {downR = downR}
      {w = w} {R = W}
      hTʳ (wf⇒ hAʳ hBʳ) αʳ∈ W⊢

  casted-𝒱′ :
    (m : ℕ) →
    𝒱 ρApp arrow-p m dir w V W →
    𝒱 ρSeal arrow-p m dir w (V down castL) (W down castR)
  casted-𝒱′ zero rel =
    ReductionFresh._down_ (proj₁ rel) ReductionFresh._↦_ ,
    ReductionFresh._down_ (proj₁ (proj₂ rel)) ReductionFresh._↦_ ,
    (left-typed , right-typed) ,
    lift tt
  casted-𝒱′ (suc k) rel =
    ReductionFresh._down_ (proj₁ rel) ReductionFresh._↦_ ,
    ReductionFresh._down_ (proj₁ (proj₂ rel)) ReductionFresh._↦_ ,
    (left-typed , right-typed) ,
    FunAll→𝒱′ (app-top , all-rest)
    where
    rel↓ : 𝒱 ρApp arrow-p k dir w V W
    rel↓ = 𝒱-monotone ρApp _ _ arrow-p k dir w V W rel

    rest-𝒱 : 𝒱 ρSeal arrow-p k dir w (V down castL) (W down castR)
    rest-𝒱 = casted-𝒱′ k rel↓

    all-rest :
      FunAll ρSeal k pA pB dir w (V down castL) (W down castR)
    all-rest = 𝒱′→FunAll (proj₂ (proj₂ (proj₂ rest-𝒱)))

    app-top :
      ∀ {w′} →
      w′ ⪰ w →
      ∀ {V′ W′} →
      𝒱 ρSeal pA (suc k) dir w′ V′ W′ →
      Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
        (Σˡ w′ ∣ ((V down castL) · V′) —→ Σˡ w′ ∣ Lβ) ×
        (Σʳ w′ ∣ ((W down castR) · W′) —→ Σʳ w′ ∣ Rβ) ×
        ℰ ρSeal pB (suc k) dir w′ Lβ Rβ
    app-top {w′ = w′} w′⪰ {V′ = V′} {W′ = W′} arg =
      Lβ , Rβ ,
      id-step (β-down-↦ (proj₁ (𝒱-⪰ ρApp arrow-p w′⪰ rel))
                        (proj₁ arg)) ,
      id-step (β-down-↦ (proj₁ (proj₂ (𝒱-⪰ ρApp arrow-p w′⪰ rel)))
                        (proj₁ (proj₂ arg))) ,
      cod-down
      where
      Lβ : Term
      Lβ = (V · (V′ up castDomL)) down castCodL

      Rβ : Term
      Rβ = (W · (W′ up castDomR)) down castCodR

      fun′ : 𝒱 ρApp arrow-p k dir w′ V W
      fun′ =
        𝒱-monotone ρApp _ _ arrow-p k dir w′ V W
          (𝒱-⪰ ρApp arrow-p w′⪰ rel)

      arg-up :
        ℰ ρApp pA (suc k) dir w′
          (V′ up castDomL)
          (W′ up castDomR)
      arg-up =
        instCast-bridge-𝒱⇒ℰ⊑′
          {A = Aˡ} {B = Aʳ} {n = k} {dir = dir} {w = w′}
          {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
          {ρ = ρ} {p = pA} {pT = pT}
          {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
          {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
          Rrel downR
          (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ w′⪰))
          (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ w′⪰))
          (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ w′⪰))
          (WfTy-weakenˢ hAʳ (_⪰_.growΨʳ w′⪰))
          (wkLookupˢ (_⪰_.growˡ w′⪰) αˡ∈)
          (wkLookupˢ (_⪰_.growʳ w′⪰) αʳ∈)
          V′ W′
          (𝒱-monotone ρSeal Aˡ Aʳ pA k dir w′ V′ W′ arg)

      app-rel :
        ℰ ρApp pB (suc k) dir w′
          (V · (V′ up castDomL))
          (W · (W′ up castDomR))
      app-rel = fun-app-ℰ fun′ arg-up

      cod-down :
        ℰ ρSeal pB (suc k) dir w′ Lβ Rβ
      cod-down =
        instCast-bridge-ℰ⊒′-for-value
          {A = Bˡ} {B = Bʳ} {n = suc k} {dir = dir} {w = w′}
          {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
          {ρ = ρ} {p = pB} {pT = pT}
          {wfTˡ = wfTˡ} {wfTʳ = wfTʳ}
          {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
          Rrel downR
          (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ w′⪰))
          (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ w′⪰))
          (WfTy-weakenˢ hBˡ (_⪰_.growΨˡ w′⪰))
          (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ w′⪰))
          (wkLookupˢ (_⪰_.growˡ w′⪰) αˡ∈)
          (wkLookupˢ (_⪰_.growʳ w′⪰) αʳ∈)
          (V · (V′ up castDomL))
          (W · (W′ up castDomR))
          app-rel

  casted-𝒱 : 𝒱 ρSeal arrow-p n dir w (V down castL) (W down castR)
  casted-𝒱 = casted-𝒱′ n Vrel
instCast-bridge-𝒱⇒ℰ⊒′ Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W Vrel =
  instCast-bridge-𝒱⇒ℰ⊒′-fallback
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W Vrel

instCast-bridge-ℰ⊑′ :
  ∀ {A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub 0}
    {p : A ⊑ B}
    {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (L R : Term) →
  ℰ (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
       (sealedRel αˡ αʳ Rrel)
       (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR))
    p n dir w L R →
  ℰ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w
    (L up (instCast⊑
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ}))
    (R up (instCast⊑
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ}))
instCast-bridge-ℰ⊑′
    {A = A} {B = B} {n = zero} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , rel) =
  (instCast-up-left-typed
     {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
     hTˡ hAˡ αˡ∈ L⊢ ,
   instCast-up-right-typed
     {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
     hTʳ hBʳ αʳ∈ R⊢) ,
  lift tt
instCast-bridge-ℰ⊑′
    {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L→L′ , rel′)) =
  (L↑⊢ , R↑⊢) ,
  inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , _ , ξ-up L→L′ ,
    instCast-bridge-ℰ⊑′
      {A = A} {B = B} {n = k} {dir = ≼}
      {w = mkWorldˡ w Σˡ′ wfΣˡ′}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR
      (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
      hTʳ
      (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
      hBʳ
      (wkLookupˢ (store-growth L→L′) αˡ∈)
      αʳ∈
      L′ R rel′)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (store-growth L→L′)

  L↑⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      L up (instCast⊑
        {A = Tˡ}
        {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
        {α = αˡ})
      ⦂ substᵗ (leftᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) A
  L↑⊢ =
    instCast-up-left-typed
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
      hTˡ hAˡ αˡ∈ L⊢

  R↑⊢ :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      R up (instCast⊑
        {A = Tʳ}
        {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
        {α = αʳ})
      ⦂ substᵗ (rightᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) B
  R↑⊢ =
    instCast-up-right-typed
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
      hTʳ hBʳ αʳ∈ R⊢
instCast-bridge-ℰ⊑′
    {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))) =
  (instCast-up-left-typed
     {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
     hTˡ hAˡ αˡ∈ L⊢ ,
   instCast-up-right-typed
     {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
     hTʳ hBʳ αʳ∈ R⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , up-blame-↠ R↠blame))
instCast-bridge-ℰ⊑′
    {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₂ (inj₂
      (vL , Σʳ′ , Ψʳ′ , wfΣʳ′ , W , R↠W , Vrel))) =
  ℰ-pull-≼-right-↠
    {A = A} {B = B}
    {ρ = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR}
    {p = p} {k = suc k} {w = w}
    {Σʳ′ = Σʳ′} {Ψʳ′ = Ψʳ′} {wfΣʳ′ = wfΣʳ′}
    {Mˡ = L up (instCast⊑ {A = Tˡ}
                  {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
                  {α = αˡ})}
    {Mʳ = R up (instCast⊑ {A = Tʳ}
                  {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
                  {α = αʳ})}
    {Mʳ′ = W up (instCast⊑ {A = Tʳ}
                   {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
                   {α = αʳ})}
    (instCast-up-left-typed
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
      hTˡ hAˡ αˡ∈ L⊢)
    (instCast-up-right-typed
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
      hTʳ hBʳ αʳ∈ R⊢)
    (up-↠ R↠W)
    (instCast-bridge-𝒱⇒ℰ⊑′
      {A = A} {B = B} {n = k} {dir = ≼}
      {w = mkWorldʳ w Σʳ′ wfΣʳ′}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR
      hTˡ
      (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
      hAˡ
      (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
      αˡ∈
      (wkLookupˢ (multi-store-growth R↠W) αʳ∈)
      L W Vrel)
  where
  grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  grow = mkWorldʳ-⪰ (multi-store-growth R↠W)

instCast-bridge-ℰ⊑′
    {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ , rel′)) =
  (L↑⊢ , R↑⊢) ,
  inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , _ , ξ-up R→R′ ,
    instCast-bridge-ℰ⊑′
      {A = A} {B = B} {n = k} {dir = ≽}
      {w = mkWorldʳ w Σʳ′ wfΣʳ′}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR
      hTˡ
      (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
      hAˡ
      (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
      αˡ∈
      (wkLookupˢ (store-growth R→R′) αʳ∈)
      L R′ rel′)
  where
  grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  grow = mkWorldʳ-⪰ (store-growth R→R′)

  L↑⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      L up (instCast⊑
        {A = Tˡ}
        {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
        {α = αˡ})
      ⦂ substᵗ (leftᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) A
  L↑⊢ =
    instCast-up-left-typed
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
      hTˡ hAˡ αˡ∈ L⊢

  R↑⊢ :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      R up (instCast⊑
        {A = Tʳ}
        {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
        {α = αʳ})
      ⦂ substᵗ (rightᵗ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)) B
  R↑⊢ =
    instCast-up-right-typed
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
      hTʳ hBʳ αʳ∈ R⊢
instCast-bridge-ℰ⊑′
    {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))) =
  (instCast-up-left-typed
     {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
     hTˡ hAˡ αˡ∈ L⊢ ,
   instCast-up-right-typed
     {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
     hTʳ hBʳ αʳ∈ R⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , up-blame-↠ R↠blame))
instCast-bridge-ℰ⊑′
    {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₂ (inj₂
      (vR , Σˡ′ , Ψˡ′ , wfΣˡ′ , W , L↠W , Vrel))) =
  ℰ-pull-≽-left-↠
    {A = A} {B = B}
    {ρ = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR}
    {p = p} {k = suc k} {w = w}
    {Σˡ′ = Σˡ′} {Ψˡ′ = Ψˡ′} {wfΣˡ′ = wfΣˡ′}
    {Mˡ = L up (instCast⊑ {A = Tˡ}
                  {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
                  {α = αˡ})}
    {Mˡ′ = W up (instCast⊑ {A = Tˡ}
                   {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
                   {α = αˡ})}
    {Mʳ = R up (instCast⊑ {A = Tʳ}
                  {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
                  {α = αʳ})}
    (instCast-up-left-typed
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
      hTˡ hAˡ αˡ∈ L⊢)
    (instCast-up-right-typed
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
      hTʳ hBʳ αʳ∈ R⊢)
    (up-↠ L↠W)
    (instCast-bridge-𝒱⇒ℰ⊑′
      {A = A} {B = B} {n = k} {dir = ≽}
      {w = mkWorldˡ w Σˡ′ wfΣˡ′}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR
      (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
      hTʳ
      (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
      hBʳ
      (wkLookupˢ (multi-store-growth L↠W) αˡ∈)
      αʳ∈
      W R Vrel)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (multi-store-growth L↠W)

instCast-bridge-ℰ⊒′ :
  ∀ {A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub 0}
    {p : A ⊑ B}
    {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (L R : Term) →
  ℰ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w L R →
  ℰ (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
       (sealedRel αˡ αʳ Rrel)
       (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR))
    p n dir w
    (L down (instCast⊒
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ}))
    (R down (instCast⊒
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ}))
instCast-bridge-ℰ⊒′
    {A = A} {B = B} {n = zero} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , rel) =
  (instCast-down-left-typed
     {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
     hTˡ hAˡ αˡ∈ L⊢ ,
   instCast-down-right-typed
     {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
     hTʳ hBʳ αʳ∈ R⊢) ,
  lift tt
instCast-bridge-ℰ⊒′
    {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L→L′ , rel′)) =
  (L↓⊢ , R↓⊢) ,
  inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , _ , ξ-down L→L′ ,
    instCast-bridge-ℰ⊒′
      {A = A} {B = B} {n = k} {dir = ≼}
      {w = mkWorldˡ w Σˡ′ wfΣˡ′}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR
      (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
      hTʳ
      (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
      hBʳ
      (wkLookupˢ (store-growth L→L′) αˡ∈)
      αʳ∈
      L′ R rel′)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (store-growth L→L′)

  L↓⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      L down (instCast⊒
        {A = Tˡ}
        {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
        {α = αˡ})
      ⦂ substᵗ
          (leftᵗ
            (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
              (sealedRel αˡ αʳ Rrel)
              (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
          A
  L↓⊢ =
    instCast-down-left-typed
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
      hTˡ hAˡ αˡ∈ L⊢

  R↓⊢ :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      R down (instCast⊒
        {A = Tʳ}
        {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
        {α = αʳ})
      ⦂ substᵗ
          (rightᵗ
            (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
              (sealedRel αˡ αʳ Rrel)
              (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
          B
  R↓⊢ =
    instCast-down-right-typed
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
      hTʳ hBʳ αʳ∈ R⊢
instCast-bridge-ℰ⊒′
    {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))) =
  (instCast-down-left-typed
     {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
     hTˡ hAˡ αˡ∈ L⊢ ,
   instCast-down-right-typed
     {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
     hTʳ hBʳ αʳ∈ R⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , down-blame-↠ R↠blame))
instCast-bridge-ℰ⊒′
    {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₂ (inj₂
      (vL , Σʳ′ , Ψʳ′ , wfΣʳ′ , W , R↠W , Vrel))) =
  ℰ-pull-≼-right-↠
    {A = A} {B = B}
    {ρ = extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
           (sealedRel αˡ αʳ Rrel)
           (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)}
    {p = p} {k = suc k} {w = w}
    {Σʳ′ = Σʳ′} {Ψʳ′ = Ψʳ′} {wfΣʳ′ = wfΣʳ′}
    {Mˡ = L down (instCast⊒ {A = Tˡ}
                    {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
                    {α = αˡ})}
    {Mʳ = R down (instCast⊒ {A = Tʳ}
                    {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
                    {α = αʳ})}
    {Mʳ′ = W down (instCast⊒ {A = Tʳ}
                     {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
                     {α = αʳ})}
    (instCast-down-left-typed
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
      hTˡ hAˡ αˡ∈ L⊢)
    (instCast-down-right-typed
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
      hTʳ hBʳ αʳ∈ R⊢)
    (down-↠ R↠W)
    (instCast-bridge-𝒱⇒ℰ⊒′
      {A = A} {B = B} {n = k} {dir = ≼}
      {w = mkWorldʳ w Σʳ′ wfΣʳ′}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR
      hTˡ
      (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
      hAˡ
      (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
      αˡ∈
      (wkLookupˢ (multi-store-growth R↠W) αʳ∈)
      L W Vrel)
  where
  grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  grow = mkWorldʳ-⪰ (multi-store-growth R↠W)

instCast-bridge-ℰ⊒′
    {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ , rel′)) =
  (L↓⊢ , R↓⊢) ,
  inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , _ , ξ-down R→R′ ,
    instCast-bridge-ℰ⊒′
      {A = A} {B = B} {n = k} {dir = ≽}
      {w = mkWorldʳ w Σʳ′ wfΣʳ′}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR
      hTˡ
      (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
      hAˡ
      (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
      αˡ∈
      (wkLookupˢ (store-growth R→R′) αʳ∈)
      L R′ rel′)
  where
  grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  grow = mkWorldʳ-⪰ (store-growth R→R′)

  L↓⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      L down (instCast⊒
        {A = Tˡ}
        {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
        {α = αˡ})
      ⦂ substᵗ
          (leftᵗ
            (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
              (sealedRel αˡ αʳ Rrel)
              (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
          A
  L↓⊢ =
    instCast-down-left-typed
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
      hTˡ hAˡ αˡ∈ L⊢

  R↓⊢ :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      R down (instCast⊒
        {A = Tʳ}
        {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
        {α = αʳ})
      ⦂ substᵗ
          (rightᵗ
            (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
              (sealedRel αˡ αʳ Rrel)
              (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
          B
  R↓⊢ =
    instCast-down-right-typed
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
      hTʳ hBʳ αʳ∈ R⊢
instCast-bridge-ℰ⊒′
    {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))) =
  (instCast-down-left-typed
     {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
     hTˡ hAˡ αˡ∈ L⊢ ,
   instCast-down-right-typed
     {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
     {Rrel = Rrel} {ρ = ρ} {pT = pT}
     {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
     {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
     hTʳ hBʳ αʳ∈ R⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , down-blame-↠ R↠blame))
instCast-bridge-ℰ⊒′
    {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
    ((L⊢ , R⊢) , inj₂ (inj₂
      (vR , Σˡ′ , Ψˡ′ , wfΣˡ′ , W , L↠W , Vrel))) =
  ℰ-pull-≽-left-↠
    {A = A} {B = B}
    {ρ = extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
           (sealedRel αˡ αʳ Rrel)
           (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)}
    {p = p} {k = suc k} {w = w}
    {Σˡ′ = Σˡ′} {Ψˡ′ = Ψˡ′} {wfΣˡ′ = wfΣˡ′}
    {Mˡ = L down (instCast⊒ {A = Tˡ}
                    {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
                    {α = αˡ})}
    {Mˡ′ = W down (instCast⊒ {A = Tˡ}
                     {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
                     {α = αˡ})}
    {Mʳ = R down (instCast⊒ {A = Tʳ}
                    {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
                    {α = αʳ})}
    (instCast-down-left-typed
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {L = L}
      hTˡ hAˡ αˡ∈ L⊢)
    (instCast-down-right-typed
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ}
      {wfαʳ = wfαʳ} {downR = downR} {w = w} {R = R}
      hTʳ hBʳ αʳ∈ R⊢)
    (down-↠ L↠W)
    (instCast-bridge-𝒱⇒ℰ⊒′
      {A = A} {B = B} {n = k} {dir = ≽}
      {w = mkWorldˡ w Σˡ′ wfΣˡ′}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR
      (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
      hTʳ
      (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
      hBʳ
      (wkLookupˢ (multi-store-growth L↠W) αˡ∈)
      αʳ∈
      W R Vrel)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (multi-store-growth L↠W)

instCast-bridge-ℰ⊒ :
  ∀ {A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub 0}
    {p : A ⊑ B}
    {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (M N : Term) →
  ℰ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w
    (substᵗᵐ
      (leftᵗ
        (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR))
      M)
    (substᵗᵐ
      (rightᵗ
        (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR))
      N) →
  ℰ (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
       (sealedRel αˡ αʳ Rrel)
       (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR))
    p n dir w
    ((substᵗᵐ (extsᵗ (leftᵗ ρ)) M [ Tˡ ]ᵀ)
     down (instCast⊒
        {A = Tˡ}
        {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
        {α = αˡ}))
    ((substᵗᵐ (extsᵗ (rightᵗ ρ)) N [ Tʳ ]ᵀ)
     down (instCast⊒
        {A = Tʳ}
        {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
        {α = αʳ}))
instCast-bridge-ℰ⊒
    {A = A} {B = B} {n = n} {dir = dir} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ M N rel =
  subst
    (λ L →
      ℰ ρSeal p n dir w L targetR)
    (cong (λ L → L down castL) eqL)
    (subst
      (λ R →
        ℰ ρSeal p n dir w sourceL R)
      (cong (λ R → R down castR) eqR)
      bridge)
  where
  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  ρSeal : RelSub 0
  ρSeal =
    extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
      (sealedRel αˡ αʳ Rrel)
      (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)

  castL : Down
  castL =
    instCast⊒
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ}

  castR : Down
  castR =
    instCast⊒
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ}

  sourceL : Term
  sourceL = substᵗᵐ (leftᵗ ρApp) M down castL

  sourceR : Term
  sourceR = substᵗᵐ (rightᵗ ρApp) N down castR

  targetR : Term
  targetR = (substᵗᵐ (extsᵗ (rightᵗ ρ)) N [ Tʳ ]ᵀ) down castR

  eqL : substᵗᵐ (leftᵗ ρApp) M ≡
        substᵗᵐ (extsᵗ (leftᵗ ρ)) M [ Tˡ ]ᵀ
  eqL =
    extendρ-left-openᵐ
      {Tˡ = Tˡ} {Tʳ = Tʳ}
      {Rrel = Rrel}
      ρ M

  eqR : substᵗᵐ (rightᵗ ρApp) N ≡
        substᵗᵐ (extsᵗ (rightᵗ ρ)) N [ Tʳ ]ᵀ
  eqR =
    extendρ-right-openᵐ
      {Tˡ = Tˡ} {Tʳ = Tʳ}
      {Rrel = Rrel}
      ρ N

  bridge : ℰ ρSeal p n dir w sourceL sourceR
  bridge =
    instCast-bridge-ℰ⊒′
      {A = A} {B = B} {n = n} {dir = dir} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈
      (substᵗᵐ (leftᵗ ρApp) M)
      (substᵗᵐ (rightᵗ ρApp) N)
      rel

instCast-bridge-ℰ :
  ∀ {A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub 0}
    {p : A ⊑ B}
    {pT : Tˡ ⊑ Tʳ}
    {wfTˡ wfTʳ wfαˡ wfαʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (M N : Term) →
  ℰ (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
       (sealedRel αˡ αʳ Rrel)
       (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR))
    p n dir w
    (substᵗᵐ
      (leftᵗ
        (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ
          (⊑-｀ αˡ αʳ)
          (sealedRel αˡ αʳ Rrel)
          (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
      M)
    (substᵗᵐ
      (rightᵗ
        (extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ
          (⊑-｀ αˡ αʳ)
          (sealedRel αˡ αʳ Rrel)
          (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)))
      N) →
  ℰ (extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w
    ((substᵗᵐ (extsᵗ (leftᵗ ρ)) M [ ｀ αˡ ]ᵀ)
     up (instCast⊑
        {A = Tˡ}
        {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
        {α = αˡ}))
    ((substᵗᵐ (extsᵗ (rightᵗ ρ)) N [ ｀ αʳ ]ᵀ)
     up (instCast⊑
        {A = Tʳ}
        {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
        {α = αʳ}))
instCast-bridge-ℰ
      {A = A} {B = B} {n = n} {dir = dir} {w = w}
    {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {ρ = ρ} {p = p} {pT = pT}
    {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
    Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ M N rel =
  subst
    (λ L →
      ℰ ρApp p n dir w L targetR)
    (cong (λ L → L up castL) eqL)
    (subst
      (λ R →
        ℰ ρApp p n dir w sourceL R)
      (cong (λ R → R up castR) eqR)
      bridge)
  where
  ρT : RelSub 0
  ρT =
    extendρ ρ (｀ αˡ) (｀ αʳ) wfαˡ wfαʳ (⊑-｀ αˡ αʳ)
      (sealedRel αˡ αʳ Rrel)
      (sealedRel-down {αˡ = αˡ} {αʳ = αʳ} {R = Rrel} downR)

  ρApp : RelSub 0
  ρApp = extendρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR

  castL : Up
  castL =
    instCast⊑
      {A = Tˡ}
      {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
      {α = αˡ}

  castR : Up
  castR =
    instCast⊑
      {A = Tʳ}
      {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
      {α = αʳ}

  sourceL : Term
  sourceL = substᵗᵐ (leftᵗ ρT) M up castL

  sourceR : Term
  sourceR = substᵗᵐ (rightᵗ ρT) N up castR

  targetR : Term
  targetR = (substᵗᵐ (extsᵗ (rightᵗ ρ)) N [ ｀ αʳ ]ᵀ) up castR

  eqL : substᵗᵐ (leftᵗ ρT) M ≡
        substᵗᵐ (extsᵗ (leftᵗ ρ)) M [ ｀ αˡ ]ᵀ
  eqL =
    extendρ-left-openᵐ
      {Tˡ = ｀ αˡ} {Tʳ = ｀ αʳ}
      {Rrel = sealedRel αˡ αʳ Rrel}
      ρ M

  eqR : substᵗᵐ (rightᵗ ρT) N ≡
        substᵗᵐ (extsᵗ (rightᵗ ρ)) N [ ｀ αʳ ]ᵀ
  eqR =
    extendρ-right-openᵐ
      {Tˡ = ｀ αˡ} {Tʳ = ｀ αʳ}
      {Rrel = sealedRel αˡ αʳ Rrel}
      ρ N

  bridge : ℰ ρApp p n dir w sourceL sourceR
  bridge =
    instCast-bridge-ℰ⊑′
      {A = A} {B = B} {n = n} {dir = dir} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡ} {wfTʳ = wfTʳ} {wfαˡ = wfαˡ} {wfαʳ = wfαʳ}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈
      (substᵗᵐ (leftᵗ ρT) M)
      (substᵗᵐ (rightᵗ ρT) N)
      rel

∀-payload-semantic-open :
  ∀ {A B T n dir w V W} {ρ : RelSub 0} {p : A ⊑ B} →
  (kit : SemanticRelKit ρ (substᴿ-⊑ ρ (⊑-refl {A = T})) w) →
  (wfTˡ : WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T)) →
  (wfTʳ : WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T)) →
  𝒱 ρ (⊑-∀ A B p) n dir w V W →
  ℰ ρ (substᵗ-⊑ (singleTyEnv T) p) n dir
    (extendWorld w
      (SemanticRelKit.rel kit)
      (semantic-down (SemanticRelKit.semantic kit)))
    (V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ])
    (W ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ])
∀-payload-semantic-open {A = A} {B = B} {T = T} {n = n} {dir = dir}
    {w = w} {V = V} {W = W} {ρ = ρ} {p = p}
    kit wfTˡ wfTʳ (vV , vW , (V⊢ , W⊢) , payload) =
  ℰ-semantic-open
    {A = A} {B = B} {T = T} {n = n} {dir = dir}
    {w₀ = w} {w = extendWorld w R sem-down}
    {M = V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]}
    {N = W ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ]}
    {R = R}
    {ρ = ρ}
    {p = p}
    {wfTˡ = wfTˡ}
    {wfTʳ = wfTʳ}
    (extendWorld-⪰ R sem-down)
    sem
    (payload
      ⪰-refl
      R
      sem-down
      (substᵗ (leftᵗ ρ) T)
      (substᵗ (rightᵗ ρ) T)
      wfTˡ
      wfTʳ
      (substᴿ-⊑ ρ (⊑-refl {A = T})))
  where
  R : Rel
  R = SemanticRelKit.rel kit

  sem : SemanticRelAt ρ (substᴿ-⊑ ρ (⊑-refl {A = T})) w R
  sem = SemanticRelKit.semantic kit

  sem-down : DownClosed R
  sem-down = semantic-down sem

postulate
  ∀-payload-semantic-current :
    ∀ {A B T k dir w V W} {ρ : RelSub 0} {p : A ⊑ B} →
    (wfA : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (wfB : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)) →
    (wfTˡ : WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T)) →
    (wfTʳ : WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T)) →
    𝒱 ρ (⊑-∀ A B p) k dir w V W →
    ℰ ρ (substᵗ-⊑ (singleTyEnv T) p) (suc k) dir w
      (V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ])
      (W ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ])

tyapp-left-typed :
  ∀ {A B T w L} {ρ : RelSub 0} {p : A ⊑ B} →
  WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A) →
  WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T) →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (`∀ A) →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]) ⦂
    substᵗ (leftᵗ ρ) (substᵗ (singleTyEnv T) A)
tyapp-left-typed {A = A} {T = T} {ρ = ρ} wfA wfT L⊢ =
  cong-⊢⦂ refl refl refl
    (sym (substᵗ-open (leftᵗ ρ) A T))
    (⊢• L⊢ wfA wfT)

tyapp-right-typed :
  ∀ {A B T w R} {ρ : RelSub 0} {p : A ⊑ B} →
  WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B) →
  WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T) →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (`∀ B) →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
    (R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ]) ⦂
    substᵗ (rightᵗ ρ) (substᵗ (singleTyEnv T) B)
tyapp-right-typed {B = B} {T = T} {ρ = ρ} wfB wfT R⊢ =
  cong-⊢⦂ refl refl refl
    (sym (substᵗ-open (rightᵗ ρ) B T))
    (⊢• R⊢ wfB wfT)

tyapp-ℰ :
  ∀ {A B T n dir w L R} {ρ : RelSub 0} {p : A ⊑ B} →
  WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A) →
  WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B) →
  WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T) →
  WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T) →
  ℰ ρ (⊑-∀ A B p) n dir w L R →
  ℰ ρ (substᵗ-⊑ (singleTyEnv T) p) n dir w
    (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ])
    (R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ])
tyapp-ℰ {A = A} {B = B} {T = T} {n = zero} {w = w}
    {L = L} {R = R} {ρ = ρ} {p = p}
    wfA wfB wfTˡ wfTʳ ((L⊢ , R⊢) , rel) =
  (tyapp-left-typed {A = A} {B = B} {T = T} {w = w} {L = L}
     {ρ = ρ} {p = p} wfA wfTˡ L⊢ ,
   tyapp-right-typed {A = A} {B = B} {T = T} {w = w} {R = R}
     {ρ = ρ} {p = p} wfB wfTʳ R⊢) ,
  lift tt
tyapp-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≼} {w = w}
    {L = L} {R = R} {ρ = ρ} {p = p}
    wfA wfB wfTˡ wfTʳ
    ((L⊢ , R⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L→L′ , rel′)) =
  (L•⊢ , R•⊢) ,
  inj₁
    (Σˡ′ , Ψˡ′ , wfΣˡ′ ,
      (L′ ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]) ,
      ξ-·α L→L′ ,
      tyapp-ℰ
        {A = A} {B = B} {T = T} {n = k} {dir = ≼}
        {w = mkWorldˡ w Σˡ′ wfΣˡ′} {ρ = ρ} {p = p}
        (WfTy-weakenˢ wfA (_⪰_.growΨˡ grow))
        wfB
        (WfTy-weakenˢ wfTˡ (_⪰_.growΨˡ grow))
        wfTʳ
        rel′)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (store-growth L→L′)

  L•⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]) ⦂
      substᵗ (leftᵗ ρ) (substᵗ (singleTyEnv T) A)
  L•⊢ = tyapp-left-typed {A = A} {B = B} {T = T} {w = w} {L = L}
           {ρ = ρ} {p = p} wfA wfTˡ L⊢

  R•⊢ :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      (R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ]) ⦂
      substᵗ (rightᵗ ρ) (substᵗ (singleTyEnv T) B)
  R•⊢ = tyapp-right-typed {A = A} {B = B} {T = T} {w = w} {R = R}
           {ρ = ρ} {p = p} wfB wfTʳ R⊢
tyapp-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≼} {w = w}
    {L = L} {R = R} {ρ = ρ} {p = p}
    wfA wfB wfTˡ wfTʳ
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))) =
  (tyapp-left-typed {A = A} {B = B} {T = T} {w = w} {L = L}
     {ρ = ρ} {p = p} wfA wfTˡ L⊢ ,
   tyapp-right-typed {A = A} {B = B} {T = T} {w = w} {R = R}
     {ρ = ρ} {p = p} wfB wfTʳ R⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , tyapp-blame-↠ R↠blame))
tyapp-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≼} {w = w}
    {L = L} {R = R} {ρ = ρ} {p = p}
    wfA wfB wfTˡ wfTʳ
    ((L⊢ , R⊢) , inj₂ (inj₂ (vL , Σʳ′ , Ψʳ′ , wfΣʳ′ , W , R↠W , Vrel))) =
  ℰ-pull-≼-right-↠
    {ρ = ρ}
    {p = substᵗ-⊑ (singleTyEnv T) p}
    {k = suc k}
    {w = w}
    {Σʳ′ = Σʳ′} {Ψʳ′ = Ψʳ′} {wfΣʳ′ = wfΣʳ′}
    {Mˡ = L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]}
    {Mʳ = R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ]}
    {Mʳ′ = W ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ]}
    (tyapp-left-typed {A = A} {B = B} {T = T} {w = w} {L = L}
       {ρ = ρ} {p = p} wfA wfTˡ L⊢)
    (tyapp-right-typed {A = A} {B = B} {T = T} {w = w} {R = R}
       {ρ = ρ} {p = p} wfB wfTʳ R⊢)
    (tyapp-↠ R↠W)
    (∀-payload-semantic-current
      {A = A} {B = B} {T = T} {k = k} {dir = ≼}
      {w = mkWorldʳ w Σʳ′ wfΣʳ′} {V = L} {W = W} {ρ = ρ} {p = p}
      wfA
      (WfTy-weakenˢ wfB (_⪰_.growΨʳ grow))
      wfTˡ
      (WfTy-weakenˢ wfTʳ (_⪰_.growΨʳ grow))
      Vrel)
  where
  grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  grow = mkWorldʳ-⪰ (multi-store-growth R↠W)
tyapp-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≽} {w = w}
    {L = L} {R = R} {ρ = ρ} {p = p}
    wfA wfB wfTˡ wfTʳ
    ((L⊢ , R⊢) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ , rel′)) =
  (L•⊢ , R•⊢) ,
  inj₁
    (Σʳ′ , Ψʳ′ , wfΣʳ′ ,
      (R′ ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ]) ,
      ξ-·α R→R′ ,
      tyapp-ℰ
        {A = A} {B = B} {T = T} {n = k} {dir = ≽}
        {w = mkWorldʳ w Σʳ′ wfΣʳ′} {ρ = ρ} {p = p}
        wfA
        (WfTy-weakenˢ wfB (_⪰_.growΨʳ grow))
        wfTˡ
        (WfTy-weakenˢ wfTʳ (_⪰_.growΨʳ grow))
        rel′)
  where
  grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  grow = mkWorldʳ-⪰ (store-growth R→R′)

  L•⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]) ⦂
      substᵗ (leftᵗ ρ) (substᵗ (singleTyEnv T) A)
  L•⊢ = tyapp-left-typed {A = A} {B = B} {T = T} {w = w} {L = L}
           {ρ = ρ} {p = p} wfA wfTˡ L⊢

  R•⊢ :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      (R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ]) ⦂
      substᵗ (rightᵗ ρ) (substᵗ (singleTyEnv T) B)
  R•⊢ = tyapp-right-typed {A = A} {B = B} {T = T} {w = w} {R = R}
           {ρ = ρ} {p = p} wfB wfTʳ R⊢
tyapp-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≽} {w = w}
    {L = L} {R = R} {ρ = ρ} {p = p}
    wfA wfB wfTˡ wfTʳ
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))) =
  (tyapp-left-typed {A = A} {B = B} {T = T} {w = w} {L = L}
     {ρ = ρ} {p = p} wfA wfTˡ L⊢ ,
   tyapp-right-typed {A = A} {B = B} {T = T} {w = w} {R = R}
     {ρ = ρ} {p = p} wfB wfTʳ R⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , tyapp-blame-↠ R↠blame))
tyapp-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≽} {w = w}
    {L = L} {R = R} {ρ = ρ} {p = p}
    wfA wfB wfTˡ wfTʳ
    ((L⊢ , R⊢) , inj₂ (inj₂ (vR , Σˡ′ , Ψˡ′ , wfΣˡ′ , W , L↠W , Vrel))) =
  ℰ-pull-≽-left-↠
    {ρ = ρ}
    {p = substᵗ-⊑ (singleTyEnv T) p}
    {k = suc k}
    {w = w}
    {Σˡ′ = Σˡ′} {Ψˡ′ = Ψˡ′} {wfΣˡ′ = wfΣˡ′}
    {Mˡ = L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]}
    {Mˡ′ = W ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]}
    {Mʳ = R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ substᵗ (rightᵗ ρ) T ]}
    (tyapp-left-typed {A = A} {B = B} {T = T} {w = w} {L = L}
       {ρ = ρ} {p = p} wfA wfTˡ L⊢)
    (tyapp-right-typed {A = A} {B = B} {T = T} {w = w} {R = R}
       {ρ = ρ} {p = p} wfB wfTʳ R⊢)
    (tyapp-↠ L↠W)
    (∀-payload-semantic-current
      {A = A} {B = B} {T = T} {k = k} {dir = ≽}
      {w = mkWorldˡ w Σˡ′ wfΣˡ′} {V = W} {W = R} {ρ = ρ} {p = p}
      (WfTy-weakenˢ wfA (_⪰_.growΨˡ grow))
      wfB
      (WfTy-weakenˢ wfTˡ (_⪰_.growΨˡ grow))
      wfTʳ
      Vrel)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (multi-store-growth L↠W)

tyappν-left-typed :
  ∀ {A T w L} {ρ : RelSub 0} →
  WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A) →
  WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T) →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (`∀ A) →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]) ⦂
    substᵗ (leftᵗ ρ) (A [ T ]ᵗ)
tyappν-left-typed {A = A} {T = T} {ρ = ρ} wfA wfT L⊢ =
  cong-⊢⦂ refl refl refl
    (sym (substᵗ-open (leftᵗ ρ) A T))
    (⊢• L⊢ wfA wfT)

postulate
  ν-fresh-current-ℰ :
    ∀ {A B T k dir w V W} {ρ : RelSub 0}
      {pν : ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B)} →
    ∀ {ΨT} →
    (hT : WfTy 0 ΨT T) →
    (wfA : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)) →
    (wfTˡ : WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T)) →
    (wfTʳ : WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T)) →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    ℰ (⇑ˢρ ρ) pν k dir
      (extendWorldν w Rrel downR
        (substᵗ (leftᵗ ρ) T)
        (substᵗ (rightᵗ ρ) T)
        wfTˡ
        wfTʳ)
      (V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ ｀ length (Σˡ w) ])
      W →
    ℰ ρ (ν-inst-⊑ A B T hT pν) (suc k) dir w
      (V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ])
      W

ν-payload-current :
  ∀ {A B T k dir w V W} {ρ : RelSub 0}
    {pν : ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B)} →
  ∀ {ΨT} →
  (hT : WfTy 0 ΨT T) →
  WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A) →
  WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T) →
  WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T) →
  𝒱 ρ (⊑-ν A B pν) k dir w V W →
  ℰ ρ (ν-inst-⊑ A B T hT pν) (suc k) dir w
    (V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ])
    W
ν-payload-current {A = A} {B = B} {T = T} {k = k} {dir = dir}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν}
    hT wfA wfTˡ wfTʳ (vV , vW , (V⊢ , W⊢) , payload) =
  ν-fresh-current-ℰ
    {A = A} {B = B} {T = T} {k = k} {dir = dir}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν}
    hT wfA wfTˡ wfTʳ R sem-down
    (payload
      ⪰-refl
      R
      sem-down
      (substᵗ (leftᵗ ρ) T)
      (substᵗ (rightᵗ ρ) T)
      wfTˡ
      wfTʳ
      (substᴿ-⊑ ρ (⊑-refl {A = T})))
  where
  kit : SemanticRelKit ρ (substᴿ-⊑ ρ (⊑-refl {A = T})) w
  kit = semanticRelAt ρ (substᴿ-⊑ ρ (⊑-refl {A = T})) w

  R : Rel
  R = SemanticRelKit.rel kit

  sem : SemanticRelAt ρ (substᴿ-⊑ ρ (⊑-refl {A = T})) w R
  sem = SemanticRelKit.semantic kit

  sem-down : DownClosed R
  sem-down = semantic-down sem

tyappν-ℰ :
  ∀ {A B T n dir w L R} {ρ : RelSub 0}
    {pν : ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B)} →
  ∀ {ΨT} →
  (hT : WfTy 0 ΨT T) →
  WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A) →
  WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T) →
  WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T) →
  ℰ ρ (⊑-ν A B pν) n dir w L R →
  ℰ ρ (ν-inst-⊑ A B T hT pν) n dir w
    (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ])
    R
tyappν-ℰ {A = A} {B = B} {T = T} {n = zero} {w = w}
    {L = L} {R = R} {ρ = ρ}
    hT wfA wfT wfTʳ ((L⊢ , R⊢) , rel) =
  (tyappν-left-typed {A = A} {T = T} {w = w} {L = L} {ρ = ρ}
     wfA wfT L⊢ ,
   R⊢) ,
  lift tt
tyappν-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≼} {w = w}
    {L = L} {R = R} {ρ = ρ} {pν = pν}
    hT wfA wfT wfTʳ
    ((L⊢ , R⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L→L′ , rel′)) =
  (L•⊢ , R⊢) ,
  inj₁
    (Σˡ′ , Ψˡ′ , wfΣˡ′ ,
      (L′ ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]) ,
      ξ-·α L→L′ ,
      tyappν-ℰ
        {A = A} {B = B} {T = T} {n = k} {dir = ≼}
        {w = mkWorldˡ w Σˡ′ wfΣˡ′} {ρ = ρ} {pν = pν}
        hT
        (WfTy-weakenˢ wfA (_⪰_.growΨˡ grow))
        (WfTy-weakenˢ wfT (_⪰_.growΨˡ grow))
        wfTʳ
        rel′)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (store-growth L→L′)

  L•⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]) ⦂
      substᵗ (leftᵗ ρ) (A [ T ]ᵗ)
  L•⊢ =
    tyappν-left-typed {A = A} {T = T} {w = w} {L = L} {ρ = ρ}
      wfA wfT L⊢
tyappν-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≼} {w = w}
    {L = L} {R = R} {ρ = ρ}
    hT wfA wfT wfTʳ
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))) =
  (tyappν-left-typed {A = A} {T = T} {w = w} {L = L} {ρ = ρ}
     wfA wfT L⊢ ,
   R⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))
tyappν-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≼} {w = w}
    {L = L} {R = R} {ρ = ρ} {pν = pν}
    hT wfA wfT wfTʳ
    ((L⊢ , R⊢) , inj₂ (inj₂ (vL , Σʳ′ , Ψʳ′ , wfΣʳ′ , W , R↠W , Vrel))) =
  ℰ-pull-≼-right-↠
    {ρ = ρ}
    {p = ν-inst-⊑ A B T hT pν}
    {k = suc k}
    {w = w}
    {Σʳ′ = Σʳ′} {Ψʳ′ = Ψʳ′} {wfΣʳ′ = wfΣʳ′}
    {Mˡ = L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]}
    {Mʳ = R}
    {Mʳ′ = W}
    (tyappν-left-typed {A = A} {T = T} {w = w} {L = L} {ρ = ρ}
       wfA wfT L⊢)
    R⊢
    R↠W
    (ν-payload-current
      {A = A} {B = B} {T = T} {k = k} {dir = ≼}
      {w = mkWorldʳ w Σʳ′ wfΣʳ′} {V = L} {W = W}
      {ρ = ρ} {pν = pν}
      hT
      wfA
      wfT
      (WfTy-weakenˢ wfTʳ
        (_⪰_.growΨʳ
          (mkWorldʳ-⪰ {w = w} {Σʳ′ = Σʳ′} {wfΣʳ′ = wfΣʳ′}
            (multi-store-growth R↠W))))
      Vrel)
tyappν-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≽} {w = w}
    {L = L} {R = R} {ρ = ρ} {pν = pν}
    hT wfA wfT wfTʳ
    ((L⊢ , R⊢) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ , rel′)) =
  (L•⊢ , R⊢) ,
  inj₁
    (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ ,
      tyappν-ℰ
        {A = A} {B = B} {T = T} {n = k} {dir = ≽}
        {w = mkWorldʳ w Σʳ′ wfΣʳ′} {ρ = ρ} {pν = pν}
        hT
        wfA
        wfT
        (WfTy-weakenˢ wfTʳ
          (_⪰_.growΨʳ
            (mkWorldʳ-⪰ {w = w} {Σʳ′ = Σʳ′} {wfΣʳ′ = wfΣʳ′}
              (store-growth R→R′))))
        rel′)
  where
  L•⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]) ⦂
      substᵗ (leftᵗ ρ) (A [ T ]ᵗ)
  L•⊢ =
    tyappν-left-typed {A = A} {T = T} {w = w} {L = L} {ρ = ρ}
      wfA wfT L⊢
tyappν-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≽} {w = w}
    {L = L} {R = R} {ρ = ρ}
    hT wfA wfT wfTʳ
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))) =
  (tyappν-left-typed {A = A} {T = T} {w = w} {L = L} {ρ = ρ}
     wfA wfT L⊢ ,
   R⊢) ,
  inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , R↠blame))
tyappν-ℰ {A = A} {B = B} {T = T} {n = suc k} {dir = ≽} {w = w}
    {L = L} {R = R} {ρ = ρ} {pν = pν}
    hT wfA wfT wfTʳ
    ((L⊢ , R⊢) , inj₂ (inj₂ (vR , Σˡ′ , Ψˡ′ , wfΣˡ′ , W , L↠W , Vrel))) =
  ℰ-pull-≽-left-↠
    {ρ = ρ}
    {p = ν-inst-⊑ A B T hT pν}
    {k = suc k}
    {w = w}
    {Σˡ′ = Σˡ′} {Ψˡ′ = Ψˡ′} {wfΣˡ′ = wfΣˡ′}
    {Mˡ = L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]}
    {Mˡ′ = W ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ substᵗ (leftᵗ ρ) T ]}
    {Mʳ = R}
    (tyappν-left-typed {A = A} {T = T} {w = w} {L = L} {ρ = ρ}
       wfA wfT L⊢)
    R⊢
    (tyapp-↠ L↠W)
    (ν-payload-current
      {A = A} {B = B} {T = T} {k = k} {dir = ≽}
      {w = mkWorldˡ w Σˡ′ wfΣˡ′} {V = W} {W = R}
      {ρ = ρ} {pν = pν}
      hT
      (WfTy-weakenˢ wfA (_⪰_.growΨˡ grow))
      (WfTy-weakenˢ wfT (_⪰_.growΨˡ grow))
      wfTʳ
      Vrel)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (multi-store-growth L↠W)

compat-Λ :
  ∀ {E dir A B M M′} {p : A ⊑ B} →
  Value M →
  Value M′ →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
  (suc (TPEnv.Δ E)) ∣ TPEnv.Ψ E ∣ ⟰ᵗ (TPEnv.store E) ∣
    ⤊ᵗ (leftCtx (TPEnv.Γ E)) ⊢ M ⦂ A →
  (suc (TPEnv.Δ E)) ∣ TPEnv.Ψ E ∣ ⟰ᵗ (TPEnv.store E) ∣
    ⤊ᵗ (rightCtx (TPEnv.Γ E)) ⊢ M′ ⦂ B →
  ⇑ᵗᴱ E ∣ dir ⊨ M ⊑ M′ ⦂ p →
  E ∣ dir ⊨ (Λ M) ⊑ (Λ M′) ⦂ (⊑-∀ A B p)
compat-Λ {E = E} {dir = dir} {A = A} {B = B} {M = M} {M′ = M′} {p = p}
  vM vM′ wfA wfB M⊢ M′⊢ M-rel zero w ρ γ rwf env =
  𝒱⇒ℰ-zero {ρ = ρ} {p = ⊑-∀ A B p} {dir = dir} {w = w}
    lambda-𝒱-zero
  where
  L : Term
  L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (Λ M))

  R : Term
  R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) (Λ M′))

  left-typed : 0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (`∀ A)
  left-typed = ⊢Λ left-value (close-left-Λ-body-typed rwf env M⊢)
    where
    left-value : Value (substᵗᵐ (extsᵗ (leftᵗ ρ)) (substˣ-term (↑ᵗᵐ (leftˣ γ)) M))
    left-value = substᵗᵐ-value (extsᵗ (leftᵗ ρ))
                   (substˣ-term-value (↑ᵗᵐ (leftˣ γ)) vM)

  right-typed : 0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (`∀ B)
  right-typed = ⊢Λ right-value (close-right-Λ-body-typed rwf env M′⊢)
    where
    right-value : Value (substᵗᵐ (extsᵗ (rightᵗ ρ)) (substˣ-term (↑ᵗᵐ (rightˣ γ)) M′))
    right-value = substᵗᵐ-value (extsᵗ (rightᵗ ρ))
                    (substˣ-term-value (↑ᵗᵐ (rightˣ γ)) vM′)

  wfA-left :
    ∀ {w′} →
    w′ ⪰ w →
    WfTy (suc zero) (Ψˡ w′) (substᵗ (extsᵗ (leftᵗ ρ)) A)
  wfA-left {w′} w′⪰ =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfA (Ψˡ≤ (RelWf-⪰ w′⪰ rwf)))
      (TySubstWf-exts (leftᵗ-wf (RelWf-⪰ w′⪰ rwf)))

  wfB-right :
    ∀ {w′} →
    w′ ⪰ w →
    WfTy (suc zero) (Ψʳ w′) (substᵗ (extsᵗ (rightᵗ ρ)) B)
  wfB-right {w′} w′⪰ =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfB (Ψʳ≤ (RelWf-⪰ w′⪰ rwf)))
      (TySubstWf-exts (rightᵗ-wf (RelWf-⪰ w′⪰ rwf)))

  lambda-𝒱-zero :
    𝒱 ρ (⊑-∀ A B p) zero dir w L R
  lambda-𝒱-zero =
    ReductionFresh.Λ _ , ReductionFresh.Λ _ ,
    (left-typed , right-typed) ,
    λ w′⪰ Rrel downR Tˡ Tʳ hTˡ hTʳ pT →
      (cong-⊢⦂ refl refl refl
         (sym (extendρ-left-open {A = A} {Tˡ = Tˡ} {Rrel = Rrel} ρ))
         (⊢• (wk⪰ˡ w′⪰ left-typed) (wfA-left w′⪰) hTˡ) ,
       cong-⊢⦂ refl refl refl
         (sym (extendρ-right-open {A = B} {Tʳ = Tʳ} {Rrel = Rrel} ρ))
         (⊢• (wk⪰ʳ w′⪰ right-typed) (wfB-right w′⪰) hTʳ)) ,
      lift tt

compat-Λ {E = E} {dir = dir} {A = A} {B = B} {M = M} {M′ = M′} {p = p}
  vM vM′ wfA wfB M⊢ M′⊢ M-rel (suc n) w ρ γ rwf env =
  𝒱⇒ℰ {ρ = ρ} {p = ⊑-∀ A B p} {n = n} {dir = dir} {w = w}
    lambda-𝒱
  where
  L : Term
  L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (Λ M))

  R : Term
  R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) (Λ M′))

  left-typed : 0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂ substᵗ (leftᵗ ρ) (`∀ A)
  left-typed = ⊢Λ left-value (close-left-Λ-body-typed rwf env M⊢)
    where
    left-value : Value (substᵗᵐ (extsᵗ (leftᵗ ρ)) (substˣ-term (↑ᵗᵐ (leftˣ γ)) M))
    left-value = substᵗᵐ-value (extsᵗ (leftᵗ ρ))
                   (substˣ-term-value (↑ᵗᵐ (leftˣ γ)) vM)

  right-typed : 0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂ substᵗ (rightᵗ ρ) (`∀ B)
  right-typed = ⊢Λ right-value (close-right-Λ-body-typed rwf env M′⊢)
    where
    right-value : Value (substᵗᵐ (extsᵗ (rightᵗ ρ)) (substˣ-term (↑ᵗᵐ (rightˣ γ)) M′))
    right-value = substᵗᵐ-value (extsᵗ (rightᵗ ρ))
                    (substˣ-term-value (↑ᵗᵐ (rightˣ γ)) vM′)

  wfA-left :
    ∀ {w′} →
    w′ ⪰ w →
    WfTy (suc zero) (Ψˡ w′) (substᵗ (extsᵗ (leftᵗ ρ)) A)
  wfA-left {w′} w′⪰ =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfA (Ψˡ≤ (RelWf-⪰ w′⪰ rwf)))
      (TySubstWf-exts (leftᵗ-wf (RelWf-⪰ w′⪰ rwf)))

  wfB-right :
    ∀ {w′} →
    w′ ⪰ w →
    WfTy (suc zero) (Ψʳ w′) (substᵗ (extsᵗ (rightᵗ ρ)) B)
  wfB-right {w′} w′⪰ =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfB (Ψʳ≤ (RelWf-⪰ w′⪰ rwf)))
      (TySubstWf-exts (rightᵗ-wf (RelWf-⪰ w′⪰ rwf)))

  payload-n :
    (m : ℕ) →
    𝒢 (TPEnv.Γ E) (suc m) dir w ρ γ →
    ∀ {w′} →
    w′ ⪰ w →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (Tˡ Tʳ : Ty) →
    (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
    (pT : Tˡ ⊑ Tʳ) →
    ℰ (extendρ ρ Tˡ Tʳ
         (Ψˡ w′ , WfTy-weakenᵗ hTˡ z≤n)
         (Ψʳ w′ , WfTy-weakenᵗ hTʳ z≤n)
         pT Rrel downR)
      p
      m dir (extendWorld w′ Rrel downR)
      (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ Tˡ ])
      (R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ Tʳ ])
  payload-n zero env′ {w′} w′⪰ Rrel downR Tˡ Tʳ hTˡ hTʳ pT =
    (cong-⊢⦂ refl refl refl
       (sym (extendρ-left-open {A = A} {Tˡ = Tˡ} {Rrel = Rrel} ρ))
       (⊢• (wk⪰ˡ (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰) left-typed)
          (wfA-left (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰)) hTˡ) ,
     cong-⊢⦂ refl refl refl
       (sym (extendρ-right-open {A = B} {Tʳ = Tʳ} {Rrel = Rrel} ρ))
       (⊢• (wk⪰ʳ (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰) right-typed)
          (wfB-right (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰)) hTʳ)) ,
    lift tt
  payload-n (suc k) env′ {w′} w′⪰ Rrel downR Tˡ Tʳ hTˡ hTʳ pT =
    bridge-suc
    where
    ρApp : RelSub 0
    ρApp =
      extendρ ρ Tˡ Tʳ
        (Ψˡ w′ , WfTy-weakenᵗ hTˡ z≤n)
        (Ψʳ w′ , WfTy-weakenᵗ hTʳ z≤n)
        pT
        Rrel
        downR

    wβ : World
    wβ = extendWorld w′ Rrel downR

    L• : Term
    L• = L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ Tˡ ]

    R• : Term
    R• = R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ Tʳ ]

    Lβ : Term
    Lβ =
      ((substᵗᵐ (extsᵗ (leftᵗ ρ)) (substˣ-term (↑ᵗᵐ (leftˣ γ)) M)
        [ ｀ (length (Σˡ wβ)) ]ᵀ)
       up (instCast⊑
          {A = Tˡ}
          {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
          {α = length (Σˡ wβ)}))

    Rβ : Term
    Rβ =
      ((substᵗᵐ (extsᵗ (rightᵗ ρ)) (substˣ-term (↑ᵗᵐ (rightˣ γ)) M′)
        [ ｀ (length (Σʳ wβ)) ]ᵀ)
       up (instCast⊑
          {A = Tʳ}
          {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
          {α = length (Σʳ wβ)}))

    stepLβ :
      Σˡ wβ ∣ L• —→ ((length (Σˡ wβ) , Tˡ) ∷ Σˡ wβ) ∣ Lβ
    stepLβ =
      β-Λ
        {Σ = Σˡ wβ}
        {A = Tˡ}
        {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
        {V = substᵗᵐ (extsᵗ (leftᵗ ρ)) (substˣ-term (↑ᵗᵐ (leftˣ γ)) M)}

    stepRβ :
      Σʳ wβ ∣ R• —→ ((length (Σʳ wβ) , Tʳ) ∷ Σʳ wβ) ∣ Rβ
    stepRβ =
      β-Λ
        {Σ = Σʳ wβ}
        {A = Tʳ}
        {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
        {V = substᵗᵐ (extsᵗ (rightᵗ ρ)) (substˣ-term (↑ᵗᵐ (rightˣ γ)) M′)}

    L•⊢ :
      0 ∣ Ψˡ wβ ∣ Σˡ wβ ∣ [] ⊢ L• ⦂
      (substᵗ (extsᵗ (leftᵗ ρ)) A [ Tˡ ]ᵗ)
    L•⊢ =
      ⊢• (wk⪰ˡ (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰) left-typed)
         (wfA-left (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
         hTˡ

    R•⊢ :
      0 ∣ Ψʳ wβ ∣ Σʳ wβ ∣ [] ⊢ R• ⦂
      (substᵗ (extsᵗ (rightᵗ ρ)) B [ Tʳ ]ᵗ)
    R•⊢ =
      ⊢• (wk⪰ʳ (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰) right-typed)
         (wfB-right (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
         hTʳ

    instCastL⊢ :
      0 ∣ suc (Ψˡ wβ) ∣ ((length (Σˡ wβ) , Tˡ) ∷ Σˡ wβ) ∣ every (suc (Ψˡ wβ)) ⊢
      instCast⊑ {A = Tˡ}
                {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
                {α = length (Σˡ wβ)}
      ⦂ (substᵗ (extsᵗ (leftᵗ ρ)) A [ ｀ (length (Σˡ wβ)) ]ᵗ)
        ⊑ (substᵗ (extsᵗ (leftᵗ ρ)) A [ Tˡ ]ᵗ)
    instCastL⊢ =
      instCast⊑-wt
        {A = Tˡ}
        {B = substᵗ (extsᵗ (leftᵗ ρ)) A}
        {α = length (Σˡ wβ)}
        (WfTy-weakenˢ hTˡ (n≤1+n _))
        (WfTy-weakenˢ (wfA-left (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
                     (n≤1+n _))
        (Z∋ˢ refl refl)
        (every-member-conv (length (Σˡ wβ)) (len<suc-StoreWf (wfΣˡ wβ)))

    instCastR⊢ :
      0 ∣ suc (Ψʳ wβ) ∣ ((length (Σʳ wβ) , Tʳ) ∷ Σʳ wβ) ∣ every (suc (Ψʳ wβ)) ⊢
      instCast⊑ {A = Tʳ}
                {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
                {α = length (Σʳ wβ)}
      ⦂ (substᵗ (extsᵗ (rightᵗ ρ)) B [ ｀ (length (Σʳ wβ)) ]ᵗ)
        ⊑ (substᵗ (extsᵗ (rightᵗ ρ)) B [ Tʳ ]ᵗ)
    instCastR⊢ =
      instCast⊑-wt
        {A = Tʳ}
        {B = substᵗ (extsᵗ (rightᵗ ρ)) B}
        {α = length (Σʳ wβ)}
        (WfTy-weakenˢ hTʳ (n≤1+n _))
        (WfTy-weakenˢ (wfB-right (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
                     (n≤1+n _))
        (Z∋ˢ refl refl)
        (every-member-conv (length (Σʳ wβ)) (len<suc-StoreWf (wfΣʳ wβ)))

    bridge-suc :
      ℰ ρApp p (suc k) dir (extendWorld w′ Rrel downR)
        (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ Tˡ ])
        (R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ Tʳ ])

    bridge-suc-≼ :
      dir ≡ ≼ →
      ℰ ρApp p (suc k) ≼ wβ L• R•
    bridge-suc-≼ dir≡≼ =
      ℰ-pull-≼-right-↠
        {ρ = ρApp}
        {p = p}
        {k = suc k}
        {w = wβ}
        (cong-⊢⦂ refl refl refl
          (sym (extendρ-left-open {A = A} {Tˡ = Tˡ} {Rrel = Rrel} ρ))
          L•⊢)
        (cong-⊢⦂ refl refl refl
          (sym (extendρ-right-open {A = B} {Tʳ = Tʳ} {Rrel = Rrel} ρ))
          R•⊢)
        right-path
        body-at-right
      where
      Σˡβ⁺ : Store
      Σˡβ⁺ = (length (Σˡ wβ) , Tˡ) ∷ Σˡ wβ

      Σʳβ⁺ : Store
      Σʳβ⁺ = (length (Σʳ wβ) , Tʳ) ∷ Σʳ wβ

      wfΣˡβ⁺ : StoreWf (Δ wβ) (suc (Ψˡ wβ)) Σˡβ⁺
      wfΣˡβ⁺ = storeWf-fresh-ext (WfTy-weakenᵗ hTˡ z≤n) (wfΣˡ wβ)

      wfΣʳβ⁺ : StoreWf (Δ wβ) (suc (Ψʳ wβ)) Σʳβ⁺
      wfΣʳβ⁺ = storeWf-fresh-ext (WfTy-weakenᵗ hTʳ z≤n) (wfΣʳ wβ)

      wβα : World
      wβα = mkWorldʳ (mkWorldˡ wβ Σˡβ⁺ wfΣˡβ⁺) Σʳβ⁺ wfΣʳβ⁺

      right-path : Σʳ wβ ∣ R• —↠ Σʳβ⁺ ∣ Rβ
      right-path = R• —→⟨ stepRβ ⟩ Rβ ∎

      ρT : RelSub 0
      ρT =
        extendρ ρ
          (｀ (length (Σˡ wβ)))
          (｀ (length (Σʳ wβ)))
          (suc (Ψˡ wβ) , wfSeal (len<suc-StoreWf (wfΣˡ wβ)))
          (suc (Ψʳ wβ) , wfSeal (len<suc-StoreWf (wfΣʳ wβ)))
          (⊑-｀ (length (Σˡ wβ)) (length (Σʳ wβ)))
          (sealedRel (length (Σˡ wβ)) (length (Σʳ wβ)) Rrel)
          (sealedRel-down
            {αˡ = length (Σˡ wβ)} {αʳ = length (Σʳ wβ)}
            {R = Rrel} downR)

      γT : RelEnv
      (γT .leftˣ) = ↑ᵗᵐ (leftˣ γ)
      (γT .rightˣ) = ↑ᵗᵐ (rightˣ γ)

      wβα⪰wβ : wβα ⪰ wβ
      wβα⪰wβ =
        ⪰-trans
          (mkWorldʳ-⪰ (store-growth stepRβ))
          (mkWorldˡ-⪰ (store-growth stepLβ))

      rwfβ : RelWf E wβ ρ
      rwfβ = RelWf-⪰ (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰) rwf

      rwfT : RelWf (⇑ᵗᴱ E) wβα ρT
      rwfT .RelWf.Ψˡ≤ = ≤-trans (Ψˡ≤ rwfβ) (_⪰_.growΨˡ wβα⪰wβ)
      rwfT .RelWf.Ψʳ≤ = ≤-trans (Ψʳ≤ rwfβ) (_⪰_.growΨʳ wβα⪰wβ)
      rwfT .RelWf.leftᵗ-wf {zero} z<s =
        wfSeal (len<suc-StoreWf (wfΣˡ wβ))
      rwfT .RelWf.leftᵗ-wf {suc X} (s<s X<Δ) =
        WfTy-weakenˢ (leftᵗ-wf rwfβ X<Δ) (_⪰_.growΨˡ wβα⪰wβ)
      rwfT .RelWf.rightᵗ-wf {zero} z<s =
        wfSeal (len<suc-StoreWf (wfΣʳ wβ))
      rwfT .RelWf.rightᵗ-wf {suc X} (s<s X<Δ) =
        WfTy-weakenˢ (rightᵗ-wf rwfβ X<Δ) (_⪰_.growΨʳ wβα⪰wβ)
      rwfT .RelWf.storeˡ =
        subst
          (λ S → S ⊆ˢ Σˡ wβα)
          (sym
            (store-subst-suc (leftᵗ ρT) (leftᵗ ρ) (λ X → refl) (TPEnv.store E)))
          (⊆ˢ-trans (storeˡ rwfβ) (_⪰_.growˡ wβα⪰wβ))
      rwfT .RelWf.storeʳ =
        subst
          (λ S → S ⊆ˢ Σʳ wβα)
          (sym
            (store-subst-suc (rightᵗ ρT) (rightᵗ ρ) (λ X → refl) (TPEnv.store E)))
          (⊆ˢ-trans (storeʳ rwfβ) (_⪰_.growʳ wβα⪰wβ))

      wkρT : WkRel suc ρ ρT
      wkρT = WkRel-suc

      env-base : 𝒢 (TPEnv.Γ E) (suc k) ≼ wβα ρ γ
      env-base =
        𝒢-⪰
          (⪰-trans wβα⪰wβ
            (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
          (subst
            (λ d → 𝒢 (TPEnv.Γ E) (suc k) d w ρ γ)
            dir≡≼
            (𝒢-monotone env′))

      envT : 𝒢 (TPEnv.Γ (⇑ᵗᴱ E)) (suc k) ≼ wβα ρT γT
      envT = 𝒢-rename-suc wkρT env-base

      Mbody :
        ℰ ρT p (suc k) ≼ wβα
          (substᵗᵐ (leftᵗ ρT) (substˣ-term (leftˣ γT) M))
          (substᵗᵐ (rightᵗ ρT) (substˣ-term (rightˣ γT) M′))
      Mbody = subst
        (λ d →
          ℰ ρT p (suc k) d wβα
            (substᵗᵐ (leftᵗ ρT) (substˣ-term (leftˣ γT) M))
            (substᵗᵐ (rightᵗ ρT) (substˣ-term (rightˣ γT) M′)))
        dir≡≼
        (M-rel
          (suc k)
          wβα
          ρT
          γT
          rwfT
          (subst
            (λ d → 𝒢 (TPEnv.Γ (⇑ᵗᴱ E)) (suc k) d wβα ρT γT)
            (sym dir≡≼)
            envT))

      body-at-right :
        ℰ ρApp p (suc k) ≼ (mkWorldʳ wβ Σʳβ⁺ wfΣʳβ⁺) L• Rβ
      body-at-right =
        (L•⊢ρApp , Rβ⊢ρApp) ,
        inj₁ (Σˡβ⁺ , suc (Ψˡ wβ) , wfΣˡβ⁺ , Lβ , stepLβ ,
          ℰ-monotone ρApp A B p k ≼ wβα Lβ Rβ casted-body-suc)
        where
        L•⊢ρApp :
          0 ∣ Ψˡ wβ ∣ Σˡ wβ ∣ [] ⊢ L• ⦂ substᵗ (leftᵗ ρApp) A
        L•⊢ρApp =
          cong-⊢⦂ refl refl refl
            (sym (extendρ-left-open {A = A} {Tˡ = Tˡ} {Rrel = Rrel} ρ))
            L•⊢

        casted-body-suc :
          ℰ ρApp p (suc k) ≼ wβα Lβ Rβ
        casted-body-suc =
          instCast-bridge-ℰ
            {A = A}
            {B = B}
            {n = suc k}
            {dir = ≼}
            {w = wβα}
            {Tˡ = Tˡ}
            {Tʳ = Tʳ}
            {αˡ = length (Σˡ wβ)}
            {αʳ = length (Σʳ wβ)}
            {ρ = ρ}
            {p = p}
            {pT = pT}
            {wfTˡ = Ψˡ w′ , WfTy-weakenᵗ hTˡ z≤n}
            {wfTʳ = Ψʳ w′ , WfTy-weakenᵗ hTʳ z≤n}
            {wfαˡ =
              suc (Ψˡ wβ) , wfSeal (len<suc-StoreWf (wfΣˡ wβ))}
            {wfαʳ =
              suc (Ψʳ wβ) , wfSeal (len<suc-StoreWf (wfΣʳ wβ))}
            Rrel
            downR
            (WfTy-weakenˢ hTˡ (n≤1+n _))
            (WfTy-weakenˢ hTʳ (n≤1+n _))
            (WfTy-weakenˢ
              (wfA-left (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
              (n≤1+n _))
            (WfTy-weakenˢ
              (wfB-right (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
              (n≤1+n _))
            (Z∋ˢ refl refl)
            (Z∋ˢ refl refl)
            (substˣ-term (leftˣ γT) M)
            (substˣ-term (rightˣ γT) M′)
            Mbody

        Rβ⊢ρApp :
          0 ∣ suc (Ψʳ wβ) ∣ Σʳβ⁺ ∣ [] ⊢ Rβ ⦂ substᵗ (rightᵗ ρApp) B
        Rβ⊢ρApp = proj₂ (proj₁ casted-body-suc)

    bridge-suc-≽ :
      dir ≡ ≽ →
      ℰ ρApp p (suc k) ≽ wβ L• R•
    bridge-suc-≽ dir≡≽ =
      (L•⊢ρApp , R•⊢ρApp) ,
      inj₁ (Σʳβ⁺ , suc (Ψʳ wβ) , wfΣʳβ⁺ , Rβ , stepRβ ,
        body-at-left)
      where
      Σˡβ⁺ : Store
      Σˡβ⁺ = (length (Σˡ wβ) , Tˡ) ∷ Σˡ wβ

      Σʳβ⁺ : Store
      Σʳβ⁺ = (length (Σʳ wβ) , Tʳ) ∷ Σʳ wβ

      wfΣˡβ⁺ : StoreWf (Δ wβ) (suc (Ψˡ wβ)) Σˡβ⁺
      wfΣˡβ⁺ = storeWf-fresh-ext (WfTy-weakenᵗ hTˡ z≤n) (wfΣˡ wβ)

      wfΣʳβ⁺ : StoreWf (Δ wβ) (suc (Ψʳ wβ)) Σʳβ⁺
      wfΣʳβ⁺ = storeWf-fresh-ext (WfTy-weakenᵗ hTʳ z≤n) (wfΣʳ wβ)

      wβα : World
      wβα = mkWorldʳ (mkWorldˡ wβ Σˡβ⁺ wfΣˡβ⁺) Σʳβ⁺ wfΣʳβ⁺

      left-path : Σˡ wβ ∣ L• —↠ Σˡβ⁺ ∣ Lβ
      left-path = L• —→⟨ stepLβ ⟩ Lβ ∎

      ρT : RelSub 0
      ρT =
        extendρ ρ
          (｀ (length (Σˡ wβ)))
          (｀ (length (Σʳ wβ)))
          (suc (Ψˡ wβ) , wfSeal (len<suc-StoreWf (wfΣˡ wβ)))
          (suc (Ψʳ wβ) , wfSeal (len<suc-StoreWf (wfΣʳ wβ)))
          (⊑-｀ (length (Σˡ wβ)) (length (Σʳ wβ)))
          (sealedRel (length (Σˡ wβ)) (length (Σʳ wβ)) Rrel)
          (sealedRel-down
            {αˡ = length (Σˡ wβ)} {αʳ = length (Σʳ wβ)}
            {R = Rrel} downR)

      γT : RelEnv
      (γT .leftˣ) = ↑ᵗᵐ (leftˣ γ)
      (γT .rightˣ) = ↑ᵗᵐ (rightˣ γ)

      wβα⪰wβ : wβα ⪰ wβ
      wβα⪰wβ =
        ⪰-trans
          (mkWorldʳ-⪰ (store-growth stepRβ))
          (mkWorldˡ-⪰ (store-growth stepLβ))

      rwfβ : RelWf E wβ ρ
      rwfβ = RelWf-⪰ (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰) rwf

      rwfT : RelWf (⇑ᵗᴱ E) wβα ρT
      rwfT .RelWf.Ψˡ≤ = ≤-trans (Ψˡ≤ rwfβ) (_⪰_.growΨˡ wβα⪰wβ)
      rwfT .RelWf.Ψʳ≤ = ≤-trans (Ψʳ≤ rwfβ) (_⪰_.growΨʳ wβα⪰wβ)
      rwfT .RelWf.leftᵗ-wf {zero} z<s =
        wfSeal (len<suc-StoreWf (wfΣˡ wβ))
      rwfT .RelWf.leftᵗ-wf {suc X} (s<s X<Δ) =
        WfTy-weakenˢ (leftᵗ-wf rwfβ X<Δ) (_⪰_.growΨˡ wβα⪰wβ)
      rwfT .RelWf.rightᵗ-wf {zero} z<s =
        wfSeal (len<suc-StoreWf (wfΣʳ wβ))
      rwfT .RelWf.rightᵗ-wf {suc X} (s<s X<Δ) =
        WfTy-weakenˢ (rightᵗ-wf rwfβ X<Δ) (_⪰_.growΨʳ wβα⪰wβ)
      rwfT .RelWf.storeˡ =
        subst
          (λ S → S ⊆ˢ Σˡ wβα)
          (sym
            (store-subst-suc (leftᵗ ρT) (leftᵗ ρ) (λ X → refl) (TPEnv.store E)))
          (⊆ˢ-trans (storeˡ rwfβ) (_⪰_.growˡ wβα⪰wβ))
      rwfT .RelWf.storeʳ =
        subst
          (λ S → S ⊆ˢ Σʳ wβα)
          (sym
            (store-subst-suc (rightᵗ ρT) (rightᵗ ρ) (λ X → refl) (TPEnv.store E)))
          (⊆ˢ-trans (storeʳ rwfβ) (_⪰_.growʳ wβα⪰wβ))

      wkρT : WkRel suc ρ ρT
      wkρT = WkRel-suc

      env-base : 𝒢 (TPEnv.Γ E) (suc k) ≽ wβα ρ γ
      env-base =
        𝒢-⪰
          (⪰-trans wβα⪰wβ
            (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
          (subst
            (λ d → 𝒢 (TPEnv.Γ E) (suc k) d w ρ γ)
            dir≡≽
            (𝒢-monotone env′))

      envT : 𝒢 (TPEnv.Γ (⇑ᵗᴱ E)) (suc k) ≽ wβα ρT γT
      envT = 𝒢-rename-suc wkρT env-base

      Mbody :
        ℰ ρT p (suc k) ≽ wβα
          (substᵗᵐ (leftᵗ ρT) (substˣ-term (leftˣ γT) M))
          (substᵗᵐ (rightᵗ ρT) (substˣ-term (rightˣ γT) M′))
      Mbody = subst
        (λ d →
          ℰ ρT p (suc k) d wβα
            (substᵗᵐ (leftᵗ ρT) (substˣ-term (leftˣ γT) M))
            (substᵗᵐ (rightᵗ ρT) (substˣ-term (rightˣ γT) M′)))
        dir≡≽
        (M-rel
          (suc k)
          wβα
          ρT
          γT
          rwfT
          (subst
            (λ d → 𝒢 (TPEnv.Γ (⇑ᵗᴱ E)) (suc k) d wβα ρT γT)
            (sym dir≡≽)
            envT))

      casted-body-suc :
        ℰ ρApp p (suc k) ≽ wβα Lβ Rβ
      casted-body-suc =
        instCast-bridge-ℰ
          {A = A}
          {B = B}
          {n = suc k}
          {dir = ≽}
          {w = wβα}
          {Tˡ = Tˡ}
          {Tʳ = Tʳ}
          {αˡ = length (Σˡ wβ)}
          {αʳ = length (Σʳ wβ)}
          {ρ = ρ}
          {p = p}
          {pT = pT}
          {wfTˡ = Ψˡ w′ , WfTy-weakenᵗ hTˡ z≤n}
          {wfTʳ = Ψʳ w′ , WfTy-weakenᵗ hTʳ z≤n}
          {wfαˡ =
            suc (Ψˡ wβ) , wfSeal (len<suc-StoreWf (wfΣˡ wβ))}
          {wfαʳ =
            suc (Ψʳ wβ) , wfSeal (len<suc-StoreWf (wfΣʳ wβ))}
          Rrel
          downR
          (WfTy-weakenˢ hTˡ (n≤1+n _))
          (WfTy-weakenˢ hTʳ (n≤1+n _))
          (WfTy-weakenˢ
            (wfA-left (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
            (n≤1+n _))
          (WfTy-weakenˢ
            (wfB-right (⪰-trans (extendWorld-⪰ Rrel downR) w′⪰))
            (n≤1+n _))
          (Z∋ˢ refl refl)
          (Z∋ˢ refl refl)
          (substˣ-term (leftˣ γT) M)
          (substˣ-term (rightˣ γT) M′)
          Mbody

      L•⊢ρApp :
        0 ∣ Ψˡ wβ ∣ Σˡ wβ ∣ [] ⊢ L• ⦂ substᵗ (leftᵗ ρApp) A
      L•⊢ρApp =
        cong-⊢⦂ refl refl refl
          (sym (extendρ-left-open {A = A} {Tˡ = Tˡ} {Rrel = Rrel} ρ))
          L•⊢

      R•⊢ρApp :
        0 ∣ Ψʳ wβ ∣ Σʳ wβ ∣ [] ⊢ R• ⦂ substᵗ (rightᵗ ρApp) B
      R•⊢ρApp =
        cong-⊢⦂ refl refl refl
          (sym (extendρ-right-open {A = B} {Tʳ = Tʳ} {Rrel = Rrel} ρ))
          R•⊢

      Rβ⊢ρApp :
        0 ∣ suc (Ψʳ wβ) ∣ Σʳβ⁺ ∣ [] ⊢ Rβ ⦂ substᵗ (rightᵗ ρApp) B
      Rβ⊢ρApp = proj₂ (proj₁ casted-body-suc)

      body-at-left :
        ℰ ρApp p k ≽ (mkWorldʳ wβ Σʳβ⁺ wfΣʳβ⁺) L• Rβ
      body-at-left =
        ℰ-pull-≽-left-↠
          {ρ = ρApp}
          {p = p}
          {k = k}
          {w = mkWorldʳ wβ Σʳβ⁺ wfΣʳβ⁺}
          L•⊢ρApp
          Rβ⊢ρApp
          left-path
          (ℰ-monotone ρApp A B p k ≽ wβα Lβ Rβ casted-body-suc)

    bridge-suc =
      dir-case
        {P = λ d →
          dir ≡ d →
          ℰ ρApp p (suc k) d wβ L• R•}
        bridge-suc-≼
        bridge-suc-≽
        dir
        refl

  payload :
    ∀ {w′} →
    w′ ⪰ w →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (Tˡ Tʳ : Ty) →
    (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
    (pT : Tˡ ⊑ Tʳ) →
    ℰ (extendρ ρ Tˡ Tʳ
         (Ψˡ w′ , WfTy-weakenᵗ hTˡ z≤n)
         (Ψʳ w′ , WfTy-weakenᵗ hTʳ z≤n)
         pT Rrel downR)
      p n dir (extendWorld w′ Rrel downR)
      (L ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A [ Tˡ ])
      (R ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) B [ Tʳ ])
  payload {w′} w′⪰ Rrel downR Tˡ Tʳ hTˡ hTʳ pT =
    payload-n n env w′⪰ Rrel downR Tˡ Tʳ hTˡ hTʳ pT

  lambda-𝒱 : 𝒱 ρ (⊑-∀ A B p) n dir w L R
  lambda-𝒱 =
    ReductionFresh.Λ _ , ReductionFresh.Λ _ ,
    (left-typed , right-typed) ,
    payload

compat-⦂∀ :
  ∀ {E dir A B M M′ T} {p : A ⊑ B} →
  E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑-∀ A B p) →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
  WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T →
  E ∣ dir ⊨ (M ⦂∀ A [ T ]) ⊑ (M′ ⦂∀ B [ T ]) ⦂
    substᵗ-⊑ (singleTyEnv T) p
compat-⦂∀ {dir = dir} {A = A} {B = B} {M = M} {M′ = M′} {T = T} {p = p}
  M-rel wfA wfB hT zero w ρ γ rwf env =
  (left-typed , right-typed) , lift tt
  where
  Mℰ : ℰ ρ (⊑-∀ A B p) zero dir w
        (substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M))
        (substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′))
  Mℰ = M-rel zero w ρ γ rwf env

  Tˡ-wf : WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T)
  Tˡ-wf =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ hT (Ψˡ≤ rwf))
      (leftᵗ-wf rwf)

  Tʳ-wf : WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T)
  Tʳ-wf =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ hT (Ψʳ≤ rwf))
      (rightᵗ-wf rwf)

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (M ⦂∀ A [ T ])) ⦂
      substᵗ (leftᵗ ρ) (substᵗ (singleTyEnv T) A)
  left-typed =
    cong-⊢⦂ refl refl refl
      (sym (substᵗ-open (leftᵗ ρ) A T))
      (⊢• (proj₁ (proj₁ Mℰ))
        (substᵗ-preserves-WfTy
          (WfTy-weakenˢ wfA (Ψˡ≤ rwf))
          (TySubstWf-exts (leftᵗ-wf rwf)))
        Tˡ-wf)

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) (M′ ⦂∀ B [ T ])) ⦂
      substᵗ (rightᵗ ρ) (substᵗ (singleTyEnv T) B)
  right-typed =
    cong-⊢⦂ refl refl refl
      (sym (substᵗ-open (rightᵗ ρ) B T))
      (⊢• (proj₂ (proj₁ Mℰ))
        (substᵗ-preserves-WfTy
          (WfTy-weakenˢ wfB (Ψʳ≤ rwf))
          (TySubstWf-exts (rightᵗ-wf rwf)))
        Tʳ-wf)
compat-⦂∀ {dir = dir} {A = A} {B = B} {M = M} {M′ = M′} {T = T} {p = p}
  M-rel wfA wfB hT (suc n) w ρ γ rwf env =
  tyapp-ℰ {A = A} {B = B} {T = T} {n = suc n} {dir = dir}
    {w = w}
    {L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)}
    {R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)}
    {ρ = ρ} {p = p}
    wfA-left
    wfB-right
    Tˡ-wf
    Tʳ-wf
    (M-rel (suc n) w ρ γ rwf env)
  where
  wfA-left : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)
  wfA-left =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfA (Ψˡ≤ rwf))
      (TySubstWf-exts (leftᵗ-wf rwf))

  wfB-right : WfTy (suc 0) (Ψʳ w) (substᵗ (extsᵗ (rightᵗ ρ)) B)
  wfB-right =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfB (Ψʳ≤ rwf))
      (TySubstWf-exts (rightᵗ-wf rwf))

  Tˡ-wf : WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T)
  Tˡ-wf =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ hT (Ψˡ≤ rwf))
      (leftᵗ-wf rwf)

  Tʳ-wf : WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T)
  Tʳ-wf =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ hT (Ψʳ≤ rwf))
      (rightᵗ-wf rwf)

compat-⦂∀-ν :
  ∀ (A B : Ty) {E dir M M′ T} (p : ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B)) →
  E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑-ν A B p) →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
  (hT : WfTy 0 (TPEnv.Ψ E) T) →
  E ∣ dir ⊨ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ ν-inst-⊑ A B T hT p
compat-⦂∀-ν A B {dir = dir} {M = M} {M′ = M′} {T = T} p
  M-rel wfA hT zero w ρ γ rwf env =
  (left-typed , right-typed) , lift tt
  where
  Mℰ : ℰ ρ (⊑-ν A B p) zero dir w
        (substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M))
        (substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′))
  Mℰ = M-rel zero w ρ γ rwf env

  Tˡ-wf : WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T)
  Tˡ-wf =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ hT (Ψˡ≤ rwf))
      (λ ())

  left-typed :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) (M ⦂∀ A [ T ])) ⦂
      substᵗ (leftᵗ ρ) (A [ T ]ᵗ)
  left-typed =
    cong-⊢⦂ refl refl refl
      (sym (substᵗ-open (leftᵗ ρ) A T))
      (⊢• (proj₁ (proj₁ Mℰ))
        (substᵗ-preserves-WfTy
          (WfTy-weakenˢ wfA (Ψˡ≤ rwf))
          (TySubstWf-exts (leftᵗ-wf rwf)))
        Tˡ-wf)

  right-typed :
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
      substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′) ⦂
      substᵗ (rightᵗ ρ) B
  right-typed = proj₂ (proj₁ Mℰ)
compat-⦂∀-ν A B {dir = dir} {M = M} {M′ = M′} {T = T} p
  M-rel wfA hT (suc n) w ρ γ rwf env =
  tyappν-ℰ
    {A = A} {B = B} {T = T} {n = suc n} {dir = dir}
    {w = w}
    {L = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)}
    {R = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)}
    {ρ = ρ} {pν = p}
    hT
    wfA-left
    Tˡ-wf
    Tʳ-wf
    (M-rel (suc n) w ρ γ rwf env)
  where
  wfA-left : WfTy (suc 0) (Ψˡ w) (substᵗ (extsᵗ (leftᵗ ρ)) A)
  wfA-left =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfA (Ψˡ≤ rwf))
      (TySubstWf-exts (leftᵗ-wf rwf))

  Tˡ-wf : WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T)
  Tˡ-wf =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ hT (Ψˡ≤ rwf))
      (λ ())

  Tʳ-wf : WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T)
  Tʳ-wf =
    substᵗ-preserves-WfTy
      (WfTy-weakenˢ hT (Ψʳ≤ rwf))
      (λ ())

postulate
  prim-ℰ :
    ∀ {n dir w L L′ M M′ op} {ρ : RelSub 0} →
    ℰ ρ (⊑-‵ `ℕ) n dir w L L′ →
    ℰ ρ (⊑-‵ `ℕ) n dir w M M′ →
    ℰ ρ (⊑-‵ `ℕ) n dir w (L ⊕[ op ] M) (L′ ⊕[ op ] M′)

compat-⊕ :
  ∀ {E dir L L′ M M′} {op : Prim} →
  E ∣ dir ⊨ L ⊑ L′ ⦂ (⊑-‵ `ℕ) →
  E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑-‵ `ℕ) →
  E ∣ dir ⊨ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′) ⦂ (⊑-‵ `ℕ)
compat-⊕ {op = op} L-rel M-rel n w ρ γ rwf env =
  prim-ℰ {op = op} (L-rel n w ρ γ rwf env) (M-rel n w ρ γ rwf env)

postulate
  cast-up-ℰ :
    ∀ {A A′ B B′ n dir w M M′ u u′}
      {pA : A ⊑ A′} {pB : B ⊑ B′} {ρ : RelSub 0} →
    ℰ ρ pA n dir w M M′ →
    ℰ ρ pB n dir w (M up u) (M′ up u′)

  cast-upL-ℰ :
    ∀ {A A′ B n dir w M M′ u}
      {pA : A ⊑ A′} {pB : B ⊑ A′} {ρ : RelSub 0} →
    ℰ ρ pA n dir w M M′ →
    ℰ ρ pB n dir w (M up u) M′

  cast-upR-ℰ :
    ∀ {A A′ B′ n dir w M M′ u′}
      {pA : A ⊑ A′} {pB : A ⊑ B′} {ρ : RelSub 0} →
    ℰ ρ pA n dir w M M′ →
    ℰ ρ pB n dir w M (M′ up u′)

  cast-down-ℰ :
    ∀ {A A′ B B′ n dir w M M′ d d′}
      {pA : A ⊑ A′} {pB : B ⊑ B′} {ρ : RelSub 0} →
    ℰ ρ pA n dir w M M′ →
    ℰ ρ pB n dir w (_down_ M d) (_down_ M′ d′)

  cast-downL-ℰ :
    ∀ {A A′ B n dir w M M′ d}
      {pA : A ⊑ A′} {pB : B ⊑ A′} {ρ : RelSub 0} →
    ℰ ρ pA n dir w M M′ →
    ℰ ρ pB n dir w (_down_ M d) M′

  cast-downR-ℰ :
    ∀ {A A′ B′ n dir w M M′ d′}
      {pA : A ⊑ A′} {pB : A ⊑ B′} {ρ : RelSub 0} →
    ℰ ρ pA n dir w M M′ →
    ℰ ρ pB n dir w M (_down_ M′ d′)

compat-up :
  ∀ {E dir M M′ A A′ B B′}
    {pA : A ⊑ A′} {pB : B ⊑ B′} {u : Up} {u′ : Up} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  E ∣ dir ⊨ (M up u) ⊑ (M′ up u′) ⦂ pB
compat-up {M = M} {M′ = M′} {u = u} {u′ = u′}
  Φ lenΦ M-rel u⊢ u′⊢ n w ρ γ rwf env =
  cast-up-ℰ
    {M = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)}
    {M′ = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)}
    {u = subst⊑ᵗ (leftᵗ ρ) u}
    {u′ = subst⊑ᵗ (rightᵗ ρ) u′}
    (M-rel n w ρ γ rwf env)

compat-upL :
  ∀ {E dir M M′ A A′ B} {pA : A ⊑ A′} {pB : B ⊑ A′} {u : Up} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
  E ∣ dir ⊨ (M up u) ⊑ M′ ⦂ pB
compat-upL {M = M} {M′ = M′} {u = u}
  Φ lenΦ M-rel u⊢ n w ρ γ rwf env =
  cast-upL-ℰ
    {M = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)}
    {M′ = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)}
    {u = subst⊑ᵗ (leftᵗ ρ) u}
    (M-rel n w ρ γ rwf env)

compat-upR :
  ∀ {E dir M M′ A A′ B′} {pA : A ⊑ A′} {pB : A ⊑ B′} {u′ : Up} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  E ∣ dir ⊨ M ⊑ (M′ up u′) ⦂ pB
compat-upR {M = M} {M′ = M′} {u′ = u′}
  Φ lenΦ M-rel u′⊢ n w ρ γ rwf env =
  cast-upR-ℰ
    {M = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)}
    {M′ = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)}
    {u′ = subst⊑ᵗ (rightᵗ ρ) u′}
    (M-rel n w ρ γ rwf env)

compat-down :
  ∀ {E dir M M′ A A′ B B′}
    {pA : A ⊑ A′} {pB : B ⊑ B′} {d : Down} {d′ : Down} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  E ∣ dir ⊨ (M down d) ⊑ (M′ down d′) ⦂ pB
compat-down {M = M} {M′ = M′} {d = d} {d′ = d′}
  Φ lenΦ M-rel d⊢ d′⊢ n w ρ γ rwf env =
  cast-down-ℰ
    {M = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)}
    {M′ = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)}
    {d = subst⊒ᵗ (leftᵗ ρ) d}
    {d′ = subst⊒ᵗ (rightᵗ ρ) d′}
    (M-rel n w ρ γ rwf env)

compat-downL :
  ∀ {E dir M M′ A A′ B} {pA : A ⊑ A′} {pB : B ⊑ A′} {d : Down} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
  E ∣ dir ⊨ (M down d) ⊑ M′ ⦂ pB
compat-downL {M = M} {M′ = M′} {d = d}
  Φ lenΦ M-rel d⊢ n w ρ γ rwf env =
  cast-downL-ℰ
    {M = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)}
    {M′ = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)}
    {d = subst⊒ᵗ (leftᵗ ρ) d}
    (M-rel n w ρ γ rwf env)

compat-downR :
  ∀ {E dir M M′ A A′ B′} {pA : A ⊑ A′} {pB : A ⊑ B′} {d′ : Down} →
  (Φ : List CastPerm) →
  length Φ ≡ TPEnv.Ψ E →
  E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
  E ∣ dir ⊨ M ⊑ (M′ down d′) ⦂ pB
compat-downR {M = M} {M′ = M′} {d′ = d′}
  Φ lenΦ M-rel d′⊢ n w ρ γ rwf env =
  cast-downR-ℰ
    {M = substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M)}
    {M′ = substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′)}
    {d′ = subst⊒ᵗ (rightᵗ ρ) d′}
    (M-rel n w ρ γ rwf env)

compat-blameR :
  ∀ {E dir M A B ℓ} {p : A ⊑ B} →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ leftCtx (TPEnv.Γ E) ⊢ M ⦂ A →
  E ∣ dir ⊨ M ⊑ (blame ℓ) ⦂ p
compat-blameR {E = E} {dir = dir} {M = M} {B = B} {ℓ = ℓ}
    M⊢ zero w ρ γ rwf env =
  (left-typed , ⊢blame ℓ) , lift tt
  where
  left-typed =
    close-left-term-typed {E = E} {M = M} {ρ = ρ} {γ = γ}
      rwf env M⊢
compat-blameR {E = E} {dir = ≼} {M = M} {B = B} {ℓ = ℓ}
    M⊢ (suc n) w ρ γ rwf env =
  (left-typed , ⊢blame ℓ) ,
  inj₂ (inj₁ (Σʳ w , Ψʳ w , wfΣʳ w , ℓ , ((blame ℓ) ∎)))
  where
  left-typed =
    close-left-term-typed {E = E} {M = M} {ρ = ρ} {γ = γ}
      rwf env M⊢
compat-blameR {E = E} {dir = ≽} {M = M} {B = B} {ℓ = ℓ}
    M⊢ (suc n) w ρ γ rwf env =
  (left-typed , ⊢blame ℓ) ,
  inj₂ (inj₁ (Σʳ w , Ψʳ w , wfΣʳ w , ℓ , ((blame ℓ) ∎)))
  where
  left-typed =
    close-left-term-typed {E = E} {M = M} {ρ = ρ} {γ = γ}
      rwf env M⊢

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
  (⊑Λ {A = A} {B = B} {M = M} {M′ = M′} {p = p}
       vM vM′ wfA wfB rel) =
  compat-Λ {E = E} {dir = dir} {A = A} {B = B} {M = M} {M′ = M′} {p = p}
    vM
    vM′
    wfA
    wfB
    (cong-⊢⦂ refl (leftCtx-⇑ᵗᴾ (TPEnv.Γ E)) refl refl (⊑-left-typed rel))
    (cong-⊢⦂ refl (rightCtx-⇑ᵗᴾ (TPEnv.Γ E)) refl refl (⊑-right-typed rel))
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
