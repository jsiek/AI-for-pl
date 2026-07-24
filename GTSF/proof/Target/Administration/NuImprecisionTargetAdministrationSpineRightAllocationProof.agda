module
  proof.Target.Administration.NuImprecisionTargetAdministrationSpineRightAllocationProof
  where

-- File Charter:
--   * Proves hereditary target-administration spine transport through one
--     right-only runtime allocation.
--   * Renames and weakens every retained cast, conversion, mode, and plan,
--     while preserving the exact target-lifted precision indices.
--   * Contains no simulation recursion, result/view/outcome type, postulate,
--     hole, permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; cast-seq
  ; id-onlyᵈ
  ; renameᶜ
  ; ⇑ᶜ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; rename-conceal-conversion
  ; rename-reveal-conversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Data.List using (List; map; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Imprecision using (ImpCtx; ⇑ᴿᵢ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
import NarrowWiden as NW
open import NarrowWiden using
  ( narrow-renameᵗ
  ; narrow-weaken
  ; widen-renameᵗ
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-right
  ; store-right
  )
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)
open import Store using (StoreIncl-drop)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-weaken
  ; weakenCastᵈ
  )
open import Types using
  ( Ty
  ; TyCtx
  ; wf★
  ; ★
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Core.Properties.CoercionProperties using
  ( ModeRename
  ; coercion-renameᵗᵐ
  ; coercion-weakenᵐ
  ; renameᶜ-preserves-Inert
  )
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-suc; renameᵗ-preserves-WfTy)
open import proof.Core.Properties.TypePreservation using
  (modeRename-suc-weakenCast; seal★-weakenCast-bind)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (⊑-target-lift-rightᵢ)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using
  ( TargetAdministrationPlan
  ; plan-fun-untag-gen
  ; plan-id
  ; plan-inert
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-seq
  ; plan-unseal
  ; plan-untag
  )
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationSpineRightAllocationDef
  using (TargetAdministrationSpineRightAllocationᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( TargetAdministrationSpine
  ; pending-cons
  ; pending-empty
  )


private
  allocated-right-store :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ) ≡
      (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
  allocated-right-store liftρ =
    cong ((zero , ★) ∷_) (rightStoreⁱ-lift-right liftρ)

  allocate-coercion :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {μ : ModeEnv} {A B : Ty} {c : Coercion} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A =⇒ B →
    weakenCastᵈ μ
      ∣ suc Δᴿ
      ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
      ⊢ ⇑ᶜ c ∶ ⇑ᵗ A =⇒ ⇑ᵗ B
  allocate-coercion {Δᴿ = Δᴿ} {μ = μ} {A = A} {B = B} {c = c}
      liftρ c⊢ =
    subst
      (λ Σ →
        weakenCastᵈ μ ∣ suc Δᴿ ∣ Σ
          ⊢ ⇑ᶜ c ∶ ⇑ᵗ A =⇒ ⇑ᵗ B)
      (sym (allocated-right-store liftρ))
      (coercion-weakenᵐ ≤-refl StoreIncl-drop
        (coercion-renameᵗᵐ TyRenameWf-suc
          modeRename-suc-weakenCast c⊢))

  allocate-narrowing :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {μ : ModeEnv} {A B : Ty} {c : Coercion} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊒ B →
    weakenCastᵈ μ
      ∣ suc Δᴿ
      ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
      ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
  allocate-narrowing
      {Δᴿ = Δᴿ} {μ = μ} {A = A} {B = B} {c = c}
      liftρ c⊒ =
    subst
      (λ Σ →
        weakenCastᵈ μ ∣ suc Δᴿ ∣ Σ
          ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B)
      (sym (allocated-right-store liftρ))
      (narrow-weaken ≤-refl StoreIncl-drop
        (narrow-renameᵗ TyRenameWf-suc
          modeRename-suc-weakenCast c⊒))

  allocate-widening :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {μ : ModeEnv} {A B : Ty} {c : Coercion} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊑ B →
    weakenCastᵈ μ
      ∣ suc Δᴿ
      ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
      ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
  allocate-widening
      {Δᴿ = Δᴿ} {μ = μ} {A = A} {B = B} {c = c}
      liftρ c⊑ =
    subst
      (λ Σ →
        weakenCastᵈ μ ∣ suc Δᴿ ∣ Σ
          ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B)
      (sym (allocated-right-store liftρ))
      (widen-weaken ≤-refl StoreIncl-drop
        (widen-renameᵗ TyRenameWf-suc
          modeRename-suc-weakenCast c⊑))

  modeRename-suc-id-only :
    ModeRename suc id-onlyᵈ id-onlyᵈ
  modeRename-suc-id-only X = refl

  allocate-id-widening :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {A B : Ty} {c : Coercion} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊑ B →
    id-onlyᵈ
      ∣ suc Δᴿ
      ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
      ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
  allocate-id-widening
      {Δᴿ = Δᴿ} {A = A} {B = B} {c = c}
      liftρ c⊑ =
    subst
      (λ Σ →
        id-onlyᵈ ∣ suc Δᴿ ∣ Σ
          ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B)
      (sym (allocated-right-store liftρ))
      (widen-weaken ≤-refl StoreIncl-drop
        (widen-renameᵗ TyRenameWf-suc
          modeRename-suc-id-only c⊑))

  allocate-reveal :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {μ : ModeEnv} {α} {X A B : Ty} {c : Coercion} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    RevealConversion μ Δᴿ (rightStoreⁱ ρ) α X c A B →
    RevealConversion
      (weakenCastᵈ μ)
      (suc Δᴿ)
      (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
      (suc α) (⇑ᵗ X) (⇑ᶜ c) (⇑ᵗ A) (⇑ᵗ B)
  allocate-reveal
      {Δᴿ = Δᴿ} {μ = μ} {α = α}
      {X = X} {A = A} {B = B} {c = c}
      liftρ reveal =
    subst
      (λ Σ →
        RevealConversion (weakenCastᵈ μ) (suc Δᴿ) Σ
          (suc α) (⇑ᵗ X) (⇑ᶜ c) (⇑ᵗ A) (⇑ᵗ B))
      (sym (allocated-right-store liftρ))
      (weaken-reveal-conversion StoreIncl-drop
        (rename-reveal-conversion TyRenameWf-suc
          modeRename-suc-weakenCast reveal))

  allocate-conceal :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {μ : ModeEnv} {α} {X A B : Ty} {c : Coercion} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    ConcealConversion μ Δᴿ (rightStoreⁱ ρ) α X c A B →
    ConcealConversion
      (weakenCastᵈ μ)
      (suc Δᴿ)
      (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
      (suc α) (⇑ᵗ X) (⇑ᶜ c) (⇑ᵗ A) (⇑ᵗ B)
  allocate-conceal
      {Δᴿ = Δᴿ} {μ = μ} {α = α}
      {X = X} {A = A} {B = B} {c = c}
      liftρ conceal =
    subst
      (λ Σ →
        ConcealConversion (weakenCastᵈ μ) (suc Δᴿ) Σ
          (suc α) (⇑ᵗ X) (⇑ᶜ c) (⇑ᵗ A) (⇑ᵗ B))
      (sym (allocated-right-store liftρ))
      (weaken-conceal-conversion StoreIncl-drop
        (rename-conceal-conversion TyRenameWf-suc
          modeRename-suc-weakenCast conceal))

  allocate-seal★ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {μ : ModeEnv} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    SealModeStore★ μ (rightStoreⁱ ρ) →
    SealModeStore★ (weakenCastᵈ μ)
      (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
  allocate-seal★ liftρ seal★ =
    subst
      (SealModeStore★ _)
      (sym (allocated-right-store liftρ))
      (seal★-weakenCast-bind seal★)

  allocate-id-seal★ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    SealModeStore★ id-onlyᵈ
      (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
  allocate-id-seal★ liftρ α ()

  allocate-plan :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {A B C : Ty} {μ : ModeEnv} {c : Coercion}
      {c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ) →
    TargetAdministrationPlan ρ A c⊢ p q →
    Σ[ c⊢′ ∈
      weakenCastᵈ μ
        ∣ suc Δᴿ
        ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
        ⊢ ⇑ᶜ c ∶ ⇑ᵗ B =⇒ ⇑ᵗ C ]
      TargetAdministrationPlan
        (store-right zero ★ wf★ ∷ ρᴿ)
        A c⊢′
        (⊑-target-lift-rightᵢ p)
        (⊑-target-lift-rightᵢ q)
  allocate-plan liftρ (plan-inert {c⊢ = c⊢} inert) =
    allocate-coercion liftρ c⊢ ,
    plan-inert (renameᶜ-preserves-Inert suc inert)
  allocate-plan liftρ (plan-id {hB = hB} {ok = ok})
      with allocate-coercion liftρ (C.cast-id hB ok)
  allocate-plan liftρ (plan-id {hB = hB} {ok = ok})
      | c⊢′@(C.cast-id hB′ ok′) =
    c⊢′ , plan-id
  allocate-plan liftρ (plan-untag {hH = hH} {gH = gH} {ok = ok})
      with allocate-coercion liftρ (C.cast-untag hH gH ok)
  allocate-plan liftρ (plan-untag {hH = hH} {gH = gH} {ok = ok})
      | c⊢′@(C.cast-untag hH′ gH′ ok′) =
    c⊢′ , plan-untag
  allocate-plan liftρ
      (plan-unseal {hB = hB} {αB∈Σ = αB∈Σ} {ok = ok})
      with allocate-coercion liftρ
        (C.cast-unseal hB αB∈Σ ok)
  allocate-plan liftρ
      (plan-unseal {hB = hB} {αB∈Σ = αB∈Σ} {ok = ok})
      | c⊢′@(C.cast-unseal hB′ αB∈Σ′ ok′) =
    c⊢′ , plan-unseal
  allocate-plan liftρ
      (plan-inst {hB = hB} {occ = occ} {s⊢ = s⊢})
      with allocate-coercion liftρ (C.cast-inst hB occ s⊢)
  allocate-plan liftρ
      (plan-inst {hB = hB} {occ = occ} {s⊢ = s⊢})
      | c⊢′@(C.cast-inst hB′ occ′ s⊢′) =
    c⊢′ , plan-inst
  allocate-plan liftρ
      (plan-fun-untag-gen
        {hG = hG} {gG = gG} {tag-ok = tag-ok}
        {hFun = hFun} {occ = occ} {s⊢ = s⊢})
      with allocate-coercion liftρ
        (C.cast-seq
          (C.cast-untag hG gG tag-ok)
          (C.cast-gen hFun occ s⊢))
  allocate-plan liftρ
      (plan-fun-untag-gen
        {hG = hG} {gG = gG} {tag-ok = tag-ok}
        {hFun = hFun} {occ = occ} {s⊢ = s⊢})
      | c⊢′@(C.cast-seq
          (C.cast-untag hG′ gG′ tag-ok′)
          (C.cast-gen hFun′ occ′ s⊢′)) =
    c⊢′ , plan-fun-untag-gen
  allocate-plan liftρ
      (plan-inst-fun-tag
        {hFun = hFun} {occ = occ} {s⊢ = s⊢}
        {hG = hG} {gG = gG} {tag-ok = tag-ok})
      with allocate-coercion liftρ
        (C.cast-seq
          (C.cast-inst hFun occ s⊢)
          (C.cast-tag hG gG tag-ok))
  allocate-plan liftρ
      (plan-inst-fun-tag
        {hFun = hFun} {occ = occ} {s⊢ = s⊢}
        {hG = hG} {gG = gG} {tag-ok = tag-ok})
      | c⊢′@(C.cast-seq
          (C.cast-inst hFun′ occ′ s⊢′)
          (C.cast-tag hG′ gG′ tag-ok′)) =
    c⊢′ , plan-inst-fun-tag
  allocate-plan liftρ (plan-seq s-plan t-plan)
      with allocate-plan liftρ s-plan
         | allocate-plan liftρ t-plan
  allocate-plan liftρ (plan-seq s-plan t-plan)
      | s⊢′ , s-plan′ | t⊢′ , t-plan′ =
    cast-seq s⊢′ t⊢′ , plan-seq s-plan′ t-plan′

  allocate-evidence :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {B C : Ty} {c : Coercion} →
    (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ) →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ c B C)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ c B C)
     ⊎
     (∃[ μ′ ]
        CastMode μ′ ×
        SealModeStore★ μ′ (rightStoreⁱ ρ) ×
        (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊒ C))
     ⊎
     (∃[ μ′ ]
        CastMode μ′ ×
        SealModeStore★ μ′ (rightStoreⁱ ρ) ×
        (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊑ C))
     ⊎
     (SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) ×
      (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ c ∶ B ⊑ C))) →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ (suc Δᴿ)
          (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
          β X′ (⇑ᶜ c) (⇑ᵗ B) (⇑ᵗ C))
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ (suc Δᴿ)
          (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
          β X′ (⇑ᶜ c) (⇑ᵗ B) (⇑ᵗ C))
     ⊎
     (∃[ μ′ ]
        CastMode μ′ ×
        SealModeStore★ μ′
          (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)) ×
        (μ′ ∣ suc Δᴿ
          ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
          ⊢ ⇑ᶜ c ∶ ⇑ᵗ B ⊒ ⇑ᵗ C))
     ⊎
     (∃[ μ′ ]
        CastMode μ′ ×
        SealModeStore★ μ′
          (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)) ×
        (μ′ ∣ suc Δᴿ
          ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
          ⊢ ⇑ᶜ c ∶ ⇑ᵗ B ⊑ ⇑ᵗ C))
     ⊎
     (SealModeStore★ id-onlyᵈ
        (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)) ×
      (id-onlyᵈ ∣ suc Δᴿ
        ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
        ⊢ ⇑ᶜ c ∶ ⇑ᵗ B ⊑ ⇑ᵗ C)))
  allocate-evidence liftρ
      (inj₁ (μ′ , β , X′ , reveal)) =
    inj₁ (weakenCastᵈ μ′ , suc β , ⇑ᵗ X′ ,
      allocate-reveal liftρ reveal)
  allocate-evidence liftρ
      (inj₂ (inj₁ (μ′ , β , X′ , conceal))) =
    inj₂ (inj₁ (weakenCastᵈ μ′ , suc β , ⇑ᵗ X′ ,
      allocate-conceal liftρ conceal))
  allocate-evidence liftρ
      (inj₂ (inj₂ (inj₁ (μ′ , mode , seal★ , c⊒)))) =
    inj₂ (inj₂ (inj₁
      (weakenCastᵈ μ′ , cast-weaken mode ,
       allocate-seal★ liftρ seal★ ,
       allocate-narrowing liftρ c⊒)))
  allocate-evidence liftρ
      (inj₂ (inj₂ (inj₂ (inj₁
        (μ′ , mode , seal★ , c⊑))))) =
    inj₂ (inj₂ (inj₂ (inj₁
      (weakenCastᵈ μ′ , cast-weaken mode ,
       allocate-seal★ liftρ seal★ ,
       allocate-widening liftρ c⊑))))
  allocate-evidence liftρ
      (inj₂ (inj₂ (inj₂ (inj₂ (seal★ , c⊑))))) =
    inj₂ (inj₂ (inj₂ (inj₂
      (allocate-id-seal★ liftρ ,
       allocate-id-widening liftρ c⊑))))


target-administration-spine-right-allocation-proofᵀ :
  TargetAdministrationSpineRightAllocationᵀ
target-administration-spine-right-allocation-proofᵀ
    liftρ pending-empty =
  pending-empty
target-administration-spine-right-allocation-proofᵀ
    liftρ (pending-cons plan evidence tail)
    with allocate-plan liftρ plan
       | allocate-evidence liftρ evidence
       | target-administration-spine-right-allocation-proofᵀ liftρ tail
target-administration-spine-right-allocation-proofᵀ
    liftρ (pending-cons plan evidence tail)
    | c⊢′ , plan′ | evidence′ | tail′ =
  pending-cons plan′ evidence′ tail′
