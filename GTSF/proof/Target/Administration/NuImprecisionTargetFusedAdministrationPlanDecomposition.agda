module
  proof.Target.Administration.NuImprecisionTargetFusedAdministrationPlanDecomposition
  where

-- File Charter:
--   * Decomposes the two fused eager target-administration plans into their
--     exact component plans.
--   * Derives the intermediate precision index by composing with the
--     canonical `gen` or `inst` type-imprecision edge.
--   * Derives the second component triangle by associativity from the stored
--     sequence and outer composition witnesses.
--   * Contains no simulation result, operational proof, postulate, hole,
--     permissive option, compatibility wrapper, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import CastImprecisionShape as CastShape
import Coercions as C
open import Coercions using
  ( genᵈ
  ; instᵈ
  ; tagTyAllowed
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; comp-↦-↦
  ; comp-↦-tag
  ; comp-∀-ν
  ; comp-ν
  ; compose-right-id★
  ; id★ˢ
  ; tag_⇛ˢ_
  ; _；_≋_
  )
open import ImprecisionWf using
  ( NonVar
  ; nonvar-all
  ; nonvar-base
  ; nonvar-fun
  ; nonvar-star
  ; tag_⇛_
  ; ν
  ; ∀ⁱ_
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; rightStoreⁱ
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  ( Ground
  ; Ty
  ; TyCtx
  ; WfTy
  ; occurs
  ; ★
  ; _⇒_
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
import Types as T
open import proof.Core.Properties.ImprecisionCompositionProperties using
  (compose-assoc-left)
open import proof.Target.SealTag.NuImprecisionTargetGroundUniqueness
  using
  ( nonvar-occurs-star-to-function
  ; universal-star-to-function
  )
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using
  ( TargetAdministrationPlan
  ; plan-fun-untag-gen
  ; plan-id-widen-seq
  ; plan-inert
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-narrow-seq
  ; plan-untag
  ; plan-widen-seq
  )


nonvar-occurs-function-midpoint-triangle :
  ∀ {Φ Δᴸ Δᴿ A}
    (safe : NonVar A)
    (occ : occurs zero A ≡ true)
    (star : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ)
    {component sequence other} →
  component ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ sequence →
  other ； sequence ≋ ⌊ star ⌋ →
  other ； component ≋
    ⌊ nonvar-occurs-star-to-function safe occ star ⌋
nonvar-occurs-function-midpoint-triangle nonvar-base ()
    star sequence-comp outer-comp
nonvar-occurs-function-midpoint-triangle nonvar-star ()
    star sequence-comp outer-comp
nonvar-occurs-function-midpoint-triangle nonvar-fun occ
    (tag star-left ⇛ star-right)
    (comp-↦-tag left-id right-id)
    (comp-↦-tag left-outer right-outer)
    with compose-right-id★ left-id
       | compose-right-id★ right-id
nonvar-occurs-function-midpoint-triangle nonvar-fun occ
    (tag star-left ⇛ star-right)
    (comp-↦-tag left-id right-id)
    (comp-↦-tag left-outer right-outer)
    | refl | refl =
  comp-↦-↦ left-outer right-outer
nonvar-occurs-function-midpoint-triangle nonvar-all occ
    (ν safe inner-occ star)
    sequence-comp@(comp-↦-tag left-id right-id)
    (comp-ν outer-comp) =
  comp-ν
    (nonvar-occurs-function-midpoint-triangle
      safe inner-occ star sequence-comp outer-comp)
nonvar-occurs-function-midpoint-triangle nonvar-all occ
    (ν safe inner-occ star)
    (comp-ν sequence-comp)
    (comp-∀-ν outer-comp) =
  comp-∀-ν
    (nonvar-occurs-function-midpoint-triangle
      safe inner-occ star sequence-comp outer-comp)
nonvar-occurs-function-midpoint-triangle nonvar-all occ
    (ν safe inner-occ star)
    (comp-ν sequence-comp)
    (comp-ν outer-comp) =
  comp-ν
    (nonvar-occurs-function-midpoint-triangle
      safe inner-occ star (comp-ν sequence-comp) outer-comp)


universal-function-midpoint :
  ∀ {Φ Δᴸ Δᴿ A C} →
  (star : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
universal-function-midpoint star (∀ⁱ relation) =
  universal-star-to-function star
universal-function-midpoint star (ν safe occ relation) =
  universal-star-to-function star


universal-function-midpoint-triangle :
  ∀ {Φ Δᴸ Δᴿ A C}
    (star : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ)
    (universal : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ)
    {component sequence} →
  component ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ sequence →
  ⌊ universal ⌋ ； sequence ≋ ⌊ star ⌋ →
  ⌊ universal ⌋ ； component ≋
    ⌊ universal-function-midpoint star universal ⌋
universal-function-midpoint-triangle
    (ν safe occ star) (ν other-safe other-occ other)
    sequence-comp@(comp-↦-tag left-id right-id)
    (comp-ν outer-comp) =
  comp-ν
    (nonvar-occurs-function-midpoint-triangle
      safe occ star sequence-comp outer-comp)
universal-function-midpoint-triangle
    (ν safe occ star) (∀ⁱ other)
    (comp-ν sequence-comp)
    (comp-∀-ν outer-comp) =
  comp-∀-ν
    (nonvar-occurs-function-midpoint-triangle
      safe occ star sequence-comp outer-comp)
universal-function-midpoint-triangle
    (ν safe occ star) (ν other-safe other-occ other)
    (comp-ν sequence-comp)
    (comp-ν outer-comp) =
  comp-ν
    (nonvar-occurs-function-midpoint-triangle
      safe occ star (comp-ν sequence-comp) outer-comp)


target-fun-untag-gen-plan-decompositionᵀ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A C : Ty} {μ s}
    {hG : WfTy Δᴿ (★ ⇒ ★)}
    {gG : Ground (★ ⇒ ★)}
    {tag-ok : tagTyAllowed μ (★ ⇒ ★) ≡ true}
    {hFun : WfTy Δᴿ (★ ⇒ ★)}
    {occ : occurs zero C ≡ true}
    {s⊢ : genᵈ μ ∣ suc Δᴿ ∣ ⟰ᵗ (rightStoreⁱ ρ)
      ⊢ s ∶ ⇑ᵗ (★ ⇒ ★) =⇒ C}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ} →
  TargetAdministrationPlan ρ A
    (C.cast-seq
      (C.cast-untag hG gG tag-ok)
      (C.cast-gen hFun occ s⊢))
    p q →
  Σ[ r ∈ (Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ) ]
    Σ[ untag-shape ∈ ImprecisionShape ]
      (CastShape.narrowing CastShape.⊢ᶜ
        (★ ⇒ ★) C.？ ⦂ untag-shape)
    × (⌊ r ⌋ ； untag-shape ≋ ⌊ p ⌋)
    × Σ[ gen-shape ∈ ImprecisionShape ]
      (CastShape.narrowing CastShape.⊢ᶜ
        C.gen (★ ⇒ ★) s ⦂ gen-shape)
    × (⌊ q ⌋ ； gen-shape ≋ ⌊ r ⌋)
    × TargetAdministrationPlan ρ A
      (C.cast-untag {μ = μ} hG gG tag-ok) p r
    × TargetAdministrationPlan ρ A
      (C.cast-gen {μ = μ} hFun occ s⊢) r q
target-fun-untag-gen-plan-decompositionᵀ
    (plan-narrow-seq
      {s-shape = untag-shape} {t-shape = gen-shape}
      mode seal★ whole narrowing sequence-evidence outer-comp
      untag-evidence untag-comp gen-evidence gen-comp
      untag-plan gen-plan) =
  _ ,
  untag-shape , untag-evidence , untag-comp ,
  gen-shape , gen-evidence , gen-comp ,
  untag-plan , gen-plan
target-fun-untag-gen-plan-decompositionᵀ
    (plan-fun-untag-gen
      (inj₁ (μ′ , β , X′ , () , replacement)))
target-fun-untag-gen-plan-decompositionᵀ
    (plan-fun-untag-gen
      (inj₂ (inj₁ (μ′ , β , X′ , () , replacement))))
target-fun-untag-gen-plan-decompositionᵀ
    {s = s} {p = p} {q = q}
    (plan-fun-untag-gen
      (inj₂ (inj₂ (inj₁
      (μ′ , sequence-shape , mode , seal★ ,
       (C.cast-seq untag⊢
         (C.cast-gen hFun occ s⊢) ,
        NW.fun-untag-gen safe) ,
       (CastShape.shape-sequence-narrowing
         CastShape.shape-untag-fun
         (CastShape.shape-gen body-shape)
         sequence-comp) ,
       outer-comp))))) =
  middle ,
  _ ,
  CastShape.shape-untag-fun ,
  untag-comp ,
  _ ,
  CastShape.shape-gen body-shape ,
  gen-comp ,
  plan-untag mode seal★
    (untag⊢ , NW.untag T.★⇒★)
    CastShape.shape-untag-fun untag-comp ,
  plan-inert (C.gen (★ ⇒ ★) s)
    (inj₂ (inj₂ (inj₁
      (μ′ , _ , mode , seal★ ,
       (C.cast-gen hFun occ s⊢ , NW.gen safe) ,
       CastShape.shape-gen body-shape ,
       gen-comp))))
  where
  middle =
    universal-function-midpoint p q

  gen-comp =
    universal-function-midpoint-triangle
      p q sequence-comp outer-comp

  untag-comp =
    compose-assoc-left gen-comp sequence-comp outer-comp
target-fun-untag-gen-plan-decompositionᵀ
    (plan-fun-untag-gen
      (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , shape , mode , seal★ ,
       (C.cast-seq untag⊢ gen⊢ , NW.cross ()) ,
       c-shape , composition))))))
target-fun-untag-gen-plan-decompositionᵀ
    (plan-fun-untag-gen
      (inj₂ (inj₂ (inj₂ (inj₂
      (shape , seal★ ,
       (C.cast-seq untag⊢ gen⊢ , NW.cross ()) ,
       c-shape , composition))))))


target-inst-fun-tag-plan-decompositionᵀ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A C : Ty} {μ s}
    {hFun : WfTy Δᴿ (★ ⇒ ★)}
    {occ : occurs zero C ≡ true}
    {s⊢ : instᵈ μ ∣ suc Δᴿ
      ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
      ⊢ s ∶ C =⇒ ⇑ᵗ (★ ⇒ ★)}
    {hG : WfTy Δᴿ (★ ⇒ ★)}
    {gG : Ground (★ ⇒ ★)}
    {tag-ok : tagTyAllowed μ (★ ⇒ ★) ≡ true}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ} →
  TargetAdministrationPlan ρ A
    (C.cast-seq
      (C.cast-inst hFun occ s⊢)
      (C.cast-tag hG gG tag-ok))
    p q →
  Σ[ r ∈ (Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ) ]
    Σ[ inst-shape ∈ ImprecisionShape ]
      (CastShape.widening CastShape.⊢ᶜ
        C.inst (★ ⇒ ★) s ⦂ inst-shape)
    × (⌊ p ⌋ ； inst-shape ≋ ⌊ r ⌋)
    × Σ[ tag-shape ∈ ImprecisionShape ]
      (CastShape.widening CastShape.⊢ᶜ
        (★ ⇒ ★) C.! ⦂ tag-shape)
    × (⌊ r ⌋ ； tag-shape ≋ ⌊ q ⌋)
    × TargetAdministrationPlan ρ A
      (C.cast-inst {μ = μ} hFun occ s⊢) p r
    × TargetAdministrationPlan ρ A
      (C.cast-tag {μ = μ} hG gG tag-ok) r q
target-inst-fun-tag-plan-decompositionᵀ
    (plan-widen-seq
      {s-shape = inst-shape} {t-shape = tag-shape}
      mode seal★ whole widening sequence-evidence outer-comp
      inst-evidence inst-comp tag-evidence tag-comp
      inst-plan tag-plan) =
  _ ,
  inst-shape , inst-evidence , inst-comp ,
  tag-shape , tag-evidence , tag-comp ,
  inst-plan , tag-plan
target-inst-fun-tag-plan-decompositionᵀ
    (plan-id-widen-seq
      {s-shape = inst-shape} {t-shape = tag-shape}
      seal★ whole widening sequence-evidence outer-comp
      inst-evidence inst-comp tag-evidence tag-comp
      inst-plan tag-plan) =
  _ ,
  inst-shape , inst-evidence , inst-comp ,
  tag-shape , tag-evidence , tag-comp ,
  inst-plan , tag-plan
target-inst-fun-tag-plan-decompositionᵀ
    (plan-inst-fun-tag
      (inj₁ (μ′ , β , X′ , () , replacement)))
target-inst-fun-tag-plan-decompositionᵀ
    (plan-inst-fun-tag
      (inj₂ (inj₁ (μ′ , β , X′ , () , replacement))))
target-inst-fun-tag-plan-decompositionᵀ
    (plan-inst-fun-tag
      (inj₂ (inj₂ (inj₁
      (μ′ , shape , mode , seal★ ,
       (C.cast-seq inst⊢ tag⊢ , NW.cross ()) ,
       c-shape , composition)))))
target-inst-fun-tag-plan-decompositionᵀ {p = p} {q = q}
    (plan-inst-fun-tag
      (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , sequence-shape , mode , seal★ ,
       (C.cast-seq
         (C.cast-inst hFun occ s⊢)
         (C.cast-tag hG gG tag-ok) ,
        NW.inst-fun-tag safe) ,
       (CastShape.shape-sequence-widening
         (CastShape.shape-inst body-shape)
         CastShape.shape-tag-fun
         sequence-comp) ,
       outer-comp)))))) =
  middle ,
  _ ,
  CastShape.shape-inst body-shape ,
  inst-comp ,
  _ ,
  CastShape.shape-tag-fun ,
  tag-comp ,
  plan-inst
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , _ , mode , seal★ ,
       (C.cast-inst hFun occ s⊢ , NW.inst safe) ,
       CastShape.shape-inst body-shape ,
       inst-comp))))) ,
  plan-inert ((★ ⇒ ★) C.!)
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , _ , mode , seal★ ,
       (C.cast-tag hG gG tag-ok , NW.tag T.★⇒★) ,
       CastShape.shape-tag-fun ,
       tag-comp)))))
  where
  middle =
    universal-function-midpoint q p

  inst-comp =
    universal-function-midpoint-triangle
      q p sequence-comp outer-comp

  tag-comp =
    compose-assoc-left inst-comp sequence-comp outer-comp
target-inst-fun-tag-plan-decompositionᵀ {p = p} {q = q}
    (plan-inst-fun-tag
      (inj₂ (inj₂ (inj₂ (inj₂
      (sequence-shape , seal★ ,
       (C.cast-seq
         (C.cast-inst hFun occ s⊢)
         (C.cast-tag hG gG tag-ok) ,
        NW.inst-fun-tag safe) ,
       (CastShape.shape-sequence-widening
         (CastShape.shape-inst body-shape)
         CastShape.shape-tag-fun
         sequence-comp) ,
       outer-comp)))))) =
  middle ,
  _ ,
  CastShape.shape-inst body-shape ,
  inst-comp ,
  _ ,
  CastShape.shape-tag-fun ,
  tag-comp ,
  plan-inst
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ ,
       (C.cast-inst hFun occ s⊢ , NW.inst safe) ,
       CastShape.shape-inst body-shape ,
          inst-comp))))) ,
  plan-inert ((★ ⇒ ★) C.!)
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ ,
       (C.cast-tag hG gG tag-ok , NW.tag T.★⇒★) ,
       CastShape.shape-tag-fun ,
       tag-comp)))))
  where
  middle =
    universal-function-midpoint q p

  inst-comp =
    universal-function-midpoint-triangle
      q p sequence-comp outer-comp

  tag-comp =
    compose-assoc-left inst-comp sequence-comp outer-comp
