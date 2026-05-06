module proof.ConsistencyCoerce where

-- File Charter:
--   * Well-typedness of the raw consistency-to-imprecision decomposition.
--   * The consistency context records which side may use a type variable as
--     `ν-bound`; its left and right projections are used for the two
--     imprecision witnesses returned by `coerce`.

open import Data.List using (length)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Types
open import Imprecision
open import Consistency

wf-leftICtx :
  ∀ {Γ A} →
  WfTy (length Γ) 0 A →
  WfTy (length (leftICtx Γ)) 0 A
wf-leftICtx {Γ = Γ} wfA =
  subst (λ Δ → WfTy Δ 0 _) (sym (length-leftICtx Γ)) wfA

wf-rightICtx :
  ∀ {Γ A} →
  WfTy (length Γ) 0 A →
  WfTy (length (rightICtx Γ)) 0 A
wf-rightICtx {Γ = Γ} wfA =
  subst (λ Δ → WfTy Δ 0 _) (sym (length-rightICtx Γ)) wfA

coerce-⊒ :
  ∀ {Γ A C} →
  Γ ⊢ A ~ C →
  Imp
coerce-⊒ A~C = proj₁ (coerce A~C)

coerce-⊑ :
  ∀ {Γ A C} →
  Γ ⊢ A ~ C →
  Imp
coerce-⊑ A~C = proj₂ (coerce A~C)

coerce-wt :
  ∀ {Γ A C} →
  (A~C : Γ ⊢ A ~ C) →
  ∃[ B ]
    ((0 ∣ leftICtx Γ ⊢ coerce-⊒ A~C ⦂ A ⊒ B) ×
     (0 ∣ rightICtx Γ ⊢ coerce-⊑ A~C ⦂ B ⊑ C))
coerce-wt ★-~-★ =
  ★ , ⊑-★★ , ⊑-★★
coerce-wt (X-~-X {X} x∈) =
  ＇ X ,
  ⊑-＇ (left-lookup-both x∈) ,
  ⊑-＇ (right-lookup-both x∈)
coerce-wt ι-~-ι =
  ‵ _ , ⊑-‵ , ⊑-‵
coerce-wt (⇒-~-⇒ A~A′ B~B′)
    with coerce A~A′ | coerce B~B′ | coerce-wt A~A′ | coerce-wt B~B′
coerce-wt (⇒-~-⇒ A~A′ B~B′)
    | pA⊒ , pA⊑
    | pB⊒ , pB⊑
    | Aₘ , pA⊒⊢ , pA⊑⊢
    | Bₘ , pB⊒⊢ , pB⊑⊢ =
  Aₘ ⇒ Bₘ ,
  ⊑-⇒ pA⊒⊢ pB⊒⊢ ,
  ⊑-⇒ pA⊑⊢ pB⊑⊢
coerce-wt (∀-~-∀ A~B) with coerce A~B | coerce-wt A~B
coerce-wt (∀-~-∀ A~B) | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊑-∀ p⊒⊢ , ⊑-∀ p⊑⊢
coerce-wt (A-~-★ g A~G) with coerce A~G | coerce-wt A~G
coerce-wt (A-~-★ g A~G) | p⊒ , p⊑ | B , p⊒⊢ , p⊑⊢ =
  B ,
  p⊒⊢ , ⊑-★ g p⊑⊢
coerce-wt (★-~-B h H~B) with coerce H~B | coerce-wt H~B
coerce-wt (★-~-B h H~B) | p⊒ , p⊑ | B , p⊒⊢ , p⊑⊢ =
  B ,
  ⊑-★ h p⊒⊢ , p⊑⊢
coerce-wt (νX-~-★ {X} x∈) =
  ＇ X ,
  ⊑-＇ (left-lookup-left x∈) ,
  ⊑-★ν (right-lookup-left x∈)
coerce-wt (★-~-νX {X} x∈) =
  ＇ X ,
  ⊑-★ν (left-lookup-right x∈) ,
  ⊑-＇ (right-lookup-right x∈)
coerce-wt {Γ = Γ} (∀-~-B {B = B} wfB A~⇑B)
    with coerce A~⇑B | coerce-wt A~⇑B
coerce-wt {Γ = Γ} (∀-~-B {B = B} wfB A~⇑B)
    | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊑-∀ p⊒⊢ , ⊑-ν (wf-rightICtx {Γ = Γ} wfB) p⊑⊢
coerce-wt {Γ = Γ} (A-~-∀ {A = A} wfA ⇑A~B)
    with coerce ⇑A~B | coerce-wt ⇑A~B
coerce-wt {Γ = Γ} (A-~-∀ {A = A} wfA ⇑A~B)
    | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊑-ν (wf-leftICtx {Γ = Γ} wfA) p⊒⊢ , ⊑-∀ p⊑⊢
