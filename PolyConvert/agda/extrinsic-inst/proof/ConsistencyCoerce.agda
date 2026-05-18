module proof.ConsistencyCoerce where

-- File Charter:
--   * Well-typedness of the raw consistency-to-imprecision decomposition.
--   * The consistency context records which side may use a type variable as
--     `X⊑★`; its left and right projections are used for the two
--     imprecision witnesses returned by `coerce`.

open import Data.List using ([]; length)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Types
open import Imprecision
open import Consistency
open import proof.ImprecisionConsistent
open import proof.ConsistencyProperties

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

coerce-wt : ∀ {Γ A C} →
  (A~C : Γ ⊢ A ~ C) →
  ∃[ B ]
    (0 ∣ leftICtx Γ ⊢ proj₁ (coerce A~C) ⦂ A ⊒ B) ×
    (0 ∣ rightICtx Γ ⊢ proj₂ (coerce A~C) ⦂ B ⊑ C)
coerce-wt ★-~-★ =
  ★ , ⊢★-⊑-★ , ⊢★-⊑-★
coerce-wt (X-~-X {X} x∈) =
  ＇ X ,
  ⊢X-⊑-X (left-lookup-both x∈) ,
  ⊢X-⊑-X (right-lookup-both x∈)
coerce-wt ι-~-ι =
  ‵ _ , ⊢ι-⊑-ι , ⊢ι-⊑-ι
coerce-wt (⇒-~-⇒ A~A′ B~B′)
    with coerce A~A′ | coerce B~B′ | coerce-wt A~A′ | coerce-wt B~B′
coerce-wt (⇒-~-⇒ A~A′ B~B′)
    | pA⊒ , pA⊑
    | pB⊒ , pB⊑
    | Aₘ , pA⊒⊢ , pA⊑⊢
    | Bₘ , pB⊒⊢ , pB⊑⊢ =
  Aₘ ⇒ Bₘ ,
  ⊢A⇒B-⊑-A′⇒B′ pA⊒⊢ pB⊒⊢ ,
  ⊢A⇒B-⊑-A′⇒B′ pA⊑⊢ pB⊑⊢
coerce-wt (∀-~-∀ A~B) with coerce A~B | coerce-wt A~B
coerce-wt (∀-~-∀ A~B) | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊢∀A-⊑-∀B p⊒⊢ , ⊢∀A-⊑-∀B p⊑⊢
coerce-wt (A-~-★ g A~G) with coerce A~G | coerce-wt A~G
coerce-wt (A-~-★ g A~G) | p⊒ , p⊑ | B , p⊒⊢ , p⊑⊢ =
  B ,
  p⊒⊢ , ⊢A-⊑-★ g p⊑⊢
coerce-wt (★-~-B h H~B) with coerce H~B | coerce-wt H~B
coerce-wt (★-~-B h H~B) | p⊒ , p⊑ | B , p⊒⊢ , p⊑⊢ =
  B ,
  ⊢A-⊑-★ h p⊒⊢ , p⊑⊢
coerce-wt (νX-~-★ {X} x∈) =
  ＇ X ,
  ⊢X-⊑-X (left-lookup-left x∈) ,
  ⊢X-⊑-★ (right-lookup-left x∈)
coerce-wt (★-~-νX {X} x∈) =
  ＇ X ,
  ⊢X-⊑-★ (left-lookup-right x∈) ,
  ⊢X-⊑-X (right-lookup-right x∈)
coerce-wt {Γ = Γ} (∀-~-B {B = B} wfB A~⇑B)
    with coerce A~⇑B | coerce-wt A~⇑B
coerce-wt {Γ = Γ} (∀-~-B {B = B} wfB A~⇑B)
    | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊢∀A-⊑-∀B p⊒⊢ , ⊢∀A-⊑-B (wf-rightICtx {Γ = Γ} wfB) p⊑⊢
coerce-wt {Γ = Γ} (A-~-∀ {A = A} wfA ⇑A~B)
    with coerce ⇑A~B | coerce-wt ⇑A~B
coerce-wt {Γ = Γ} (A-~-∀ {A = A} wfA ⇑A~B)
    | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊢∀A-⊑-B (wf-leftICtx {Γ = Γ} wfA) p⊒⊢ , ⊢∀A-⊑-∀B p⊑⊢

coerce-wt-plains :
  ∀ {Δ A C} →
  (A~C : boths Δ [] ⊢ A ~ C) →
  ∃[ B ]
    ((0 ∣ plains Δ [] ⊢ coerce-⊒ A~C ⦂ A ⊒ B) ×
     (0 ∣ plains Δ [] ⊢ coerce-⊑ A~C ⦂ B ⊑ C))
coerce-wt-plains {Δ = Δ} A~C with coerce-wt A~C
coerce-wt-plains {Δ = Δ} A~C | B , p⊒⊢ , p⊑⊢
  rewrite leftICtx-boths[] Δ | rightICtx-boths[] Δ =
  B , p⊒⊢ , p⊑⊢

