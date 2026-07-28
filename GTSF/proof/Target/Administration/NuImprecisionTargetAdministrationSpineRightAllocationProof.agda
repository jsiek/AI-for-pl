module
  proof.Target.Administration.NuImprecisionTargetAdministrationSpineRightAllocationProof
  where

-- File Charter:
--   * Proves hereditary target-administration spine transport through one
--     right-only runtime allocation.
--   * Renames and weakens every retained cast, conversion, mode, and plan,
--     while preserving the exact target-lifted precision indices.
--   * Transports retained replacement, cast-shape, and composition evidence;
--     sequence-component triangles are never reconstructed.
--   * Contains no simulation recursion, result/view/outcome type, postulate,
--     hole, permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
import CastImprecisionShape as CastShape
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
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import Data.List using (List; map; _∷_)
open import Data.Nat using (s<s; suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import ImprecisionComposition using
  (⌊_⌋; _；_≋_)
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
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-right
  ; store-right
  )
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
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
  ; renameᵗ
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
  (TyRenameWf-suc; renameᵗ-id; renameᵗ-preserves-WfTy)
open import
  proof.Core.Properties.ConversionIndexCompatibilityProperties
  using
  ( replace-right-rename²ᵢ
  ; replace-right-source-shape
  ; replace-right-target-shape
  ; replace-right-transport-endpoints
  ; shape-transport-imprecision-endpoints
  )
open import proof.Core.Properties.TypePreservation using
  (modeRename-suc-weakenCast; seal★-weakenCast-bind)
open import
  proof.Core.Properties.NuImprecisionIndexedRenamingProperties
  using
  ( rename-assm²-target-rightᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using
  ( TargetAdministrationPlan
  ; plan-fun-untag-gen
  ; plan-id
  ; plan-id-widen-seq
  ; plan-inert
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-narrow-seq
  ; plan-unseal
  ; plan-untag
  ; plan-widen-seq
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-rename
  ; imprecision-composition-shape-transport
  ; shape-rename
  ; shape-target-lift-rightᵢ
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

  allocate-composition :
    ∀ {Φ Δᴸ Δᴿ A B C shape}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
    ⌊ ⊑-target-lift-rightᵢ p ⌋ ； shape ≋
      ⌊ ⊑-target-lift-rightᵢ q ⌋
  allocate-composition {p = p} {q = q} comp =
    imprecision-composition-shape-transport
      (shape-target-lift-rightᵢ p)
      refl
      (shape-target-lift-rightᵢ q)
      comp

  allocate-right-replacement :
    ∀ {Φ Δᴸ Δᴿ A A′ B′ β X′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
    p [ β ↦ X′ ]ᴿ q →
    ⊑-target-lift-rightᵢ p
      [ suc β ↦ ⇑ᵗ X′ ]ᴿ
    ⊑-target-lift-rightᵢ q
  allocate-right-replacement
      {A = A} {p = p} {q = q} replacement =
    replace-right-target-shape
      (trans (shape-target-lift-rightᵢ q)
        (sym transported-q-shape))
      (replace-right-source-shape
        (trans (shape-target-lift-rightᵢ p)
          (sym transported-p-shape))
        transported)
    where
    renamed-p = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
      (λ X<Δ → X<Δ) TyRenameWf-suc p
    renamed-q = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
      (λ X<Δ → X<Δ) TyRenameWf-suc q
    transported =
      replace-right-transport-endpoints
        (renameᵗ-id A) refl refl refl
        (replace-right-rename²ᵢ rename-assm²-target-rightᵢ
          (λ X<Δ → X<Δ) TyRenameWf-suc replacement)
    transported-p-shape =
      trans
        (shape-transport-imprecision-endpoints
          (renameᵗ-id A) refl renamed-p)
        (shape-rename rename-assm²-target-rightᵢ
          (λ X<Δ → X<Δ) TyRenameWf-suc p)
    transported-q-shape =
      trans
        (shape-transport-imprecision-endpoints
          (renameᵗ-id A) refl renamed-q)
        (shape-rename rename-assm²-target-rightᵢ
          (λ X<Δ → X<Δ) TyRenameWf-suc q)

  allocate-plan-evidence :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {A B C : Ty} {c : Coercion}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ) →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ c B C
        × p [ β ↦ X′ ]ᴿ q)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ c B C
        × q [ β ↦ X′ ]ᴿ p)
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊒ C)
        × (CastShape.narrowing CastShape.⊢ᶜ c ⦂ shape)
        × (⌊ q ⌋ ； shape ≋ ⌊ p ⌋))
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊑ C)
        × (CastShape.widening CastShape.⊢ᶜ c ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))
     ⊎
     (∃[ shape ]
        SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ)
        × (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ c ∶ B ⊑ C)
        × (CastShape.widening CastShape.⊢ᶜ c ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))) →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ (suc Δᴿ)
          (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
          β X′ (⇑ᶜ c) (⇑ᵗ B) (⇑ᵗ C)
        × ⊑-target-lift-rightᵢ p
          [ β ↦ X′ ]ᴿ
          ⊑-target-lift-rightᵢ q)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ (suc Δᴿ)
          (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
          β X′ (⇑ᶜ c) (⇑ᵗ B) (⇑ᵗ C)
        × ⊑-target-lift-rightᵢ q
          [ β ↦ X′ ]ᴿ
          ⊑-target-lift-rightᵢ p)
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′
          (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
        × (μ′ ∣ suc Δᴿ
          ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
          ⊢ ⇑ᶜ c ∶ ⇑ᵗ B ⊒ ⇑ᵗ C)
        × (CastShape.narrowing CastShape.⊢ᶜ
          ⇑ᶜ c ⦂ shape)
        × (⌊ ⊑-target-lift-rightᵢ q ⌋ ； shape ≋
          ⌊ ⊑-target-lift-rightᵢ p ⌋))
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′
          (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
        × (μ′ ∣ suc Δᴿ
          ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
          ⊢ ⇑ᶜ c ∶ ⇑ᵗ B ⊑ ⇑ᵗ C)
        × (CastShape.widening CastShape.⊢ᶜ
          ⇑ᶜ c ⦂ shape)
        × (⌊ ⊑-target-lift-rightᵢ p ⌋ ； shape ≋
          ⌊ ⊑-target-lift-rightᵢ q ⌋))
     ⊎
     (∃[ shape ]
        SealModeStore★ id-onlyᵈ
          (rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ))
        × (id-onlyᵈ ∣ suc Δᴿ
          ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
          ⊢ ⇑ᶜ c ∶ ⇑ᵗ B ⊑ ⇑ᵗ C)
        × (CastShape.widening CastShape.⊢ᶜ
          ⇑ᶜ c ⦂ shape)
        × (⌊ ⊑-target-lift-rightᵢ p ⌋ ； shape ≋
          ⌊ ⊑-target-lift-rightᵢ q ⌋)))
  allocate-plan-evidence liftρ
      (inj₁ (μ′ , β , X′ , reveal , replacement)) =
    inj₁
      (weakenCastᵈ μ′ , suc β , ⇑ᵗ X′ ,
       allocate-reveal liftρ reveal ,
       allocate-right-replacement replacement)
  allocate-plan-evidence liftρ
      (inj₂ (inj₁
        (μ′ , β , X′ , conceal , replacement))) =
    inj₂ (inj₁
      (weakenCastᵈ μ′ , suc β , ⇑ᵗ X′ ,
       allocate-conceal liftρ conceal ,
       allocate-right-replacement replacement))
  allocate-plan-evidence liftρ
      (inj₂ (inj₂ (inj₁
        (μ′ , shape , mode , seal★ , c⊒ ,
         c-shape , comp)))) =
    inj₂ (inj₂ (inj₁
      (weakenCastᵈ μ′ , shape , cast-weaken mode ,
       allocate-seal★ liftρ seal★ ,
       allocate-narrowing liftρ c⊒ ,
       cast-shape-rename suc c-shape ,
       allocate-composition comp)))
  allocate-plan-evidence liftρ
      (inj₂ (inj₂ (inj₂ (inj₁
        (μ′ , shape , mode , seal★ , c⊑ ,
         c-shape , comp))))) =
    inj₂ (inj₂ (inj₂ (inj₁
      (weakenCastᵈ μ′ , shape , cast-weaken mode ,
       allocate-seal★ liftρ seal★ ,
       allocate-widening liftρ c⊑ ,
       cast-shape-rename suc c-shape ,
       allocate-composition comp))))
  allocate-plan-evidence liftρ
      (inj₂ (inj₂ (inj₂ (inj₂
        (shape , seal★ , c⊑ , c-shape , comp))))) =
    inj₂ (inj₂ (inj₂ (inj₂
      (shape , allocate-id-seal★ liftρ ,
       allocate-id-widening liftρ c⊑ ,
       cast-shape-rename suc c-shape ,
       allocate-composition comp))))

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
  allocate-plan liftρ
      (plan-inert {c⊢ = c⊢} inert evidence) =
    allocate-coercion liftρ c⊢ ,
    plan-inert
      (renameᶜ-preserves-Inert suc inert)
      (allocate-plan-evidence liftρ evidence)
  allocate-plan liftρ (plan-id {hB = hB} {ok = ok} evidence)
      with allocate-coercion liftρ (C.cast-id hB ok)
  allocate-plan liftρ (plan-id {hB = hB} {ok = ok} evidence)
      | c⊢′@(C.cast-id hB′ ok′) =
    c⊢′ , plan-id (allocate-plan-evidence liftρ evidence)
  allocate-plan liftρ
      (plan-untag {hH = hH} {gH = gH} {ok = ok}
        mode seal★ c⊒ c-shape comp)
      with allocate-coercion liftρ (C.cast-untag hH gH ok)
  allocate-plan liftρ
      (plan-untag {hH = hH} {gH = gH} {ok = ok}
        mode seal★ c⊒ c-shape comp)
      | c⊢′@(C.cast-untag hH′ gH′ ok′) =
    c⊢′ ,
    plan-untag
      (cast-weaken mode)
      (allocate-seal★ liftρ seal★)
      (allocate-narrowing liftρ c⊒)
      (cast-shape-rename suc c-shape)
      (allocate-composition comp)
  allocate-plan liftρ
      (plan-unseal
        {hB = hB} {αB∈Σ = αB∈Σ} {ok = ok}
        evidence)
      with allocate-coercion liftρ
        (C.cast-unseal hB αB∈Σ ok)
  allocate-plan liftρ
      (plan-unseal
        {hB = hB} {αB∈Σ = αB∈Σ} {ok = ok}
        evidence)
      | c⊢′@(C.cast-unseal hB′ αB∈Σ′ ok′) =
    c⊢′ , plan-unseal (allocate-plan-evidence liftρ evidence)
  allocate-plan liftρ
      (plan-inst
        {hB = hB} {occ = occ} {s⊢ = s⊢}
        evidence)
      with allocate-coercion liftρ (C.cast-inst hB occ s⊢)
  allocate-plan liftρ
      (plan-inst
        {hB = hB} {occ = occ} {s⊢ = s⊢}
        evidence)
      | c⊢′@(C.cast-inst hB′ occ′ s⊢′) =
    c⊢′ , plan-inst (allocate-plan-evidence liftρ evidence)
  allocate-plan liftρ
      (plan-fun-untag-gen
        {hG = hG} {gG = gG} {tag-ok = tag-ok}
        {hFun = hFun} {occ = occ} {s⊢ = s⊢}
        evidence)
      with allocate-coercion liftρ
        (C.cast-seq
          (C.cast-untag hG gG tag-ok)
          (C.cast-gen hFun occ s⊢))
  allocate-plan liftρ
      (plan-fun-untag-gen
        {hG = hG} {gG = gG} {tag-ok = tag-ok}
        {hFun = hFun} {occ = occ} {s⊢ = s⊢}
        evidence)
      | c⊢′@(C.cast-seq
          (C.cast-untag hG′ gG′ tag-ok′)
          (C.cast-gen hFun′ occ′ s⊢′)) =
    c⊢′ ,
    plan-fun-untag-gen
      (allocate-plan-evidence liftρ evidence)
  allocate-plan liftρ
      (plan-inst-fun-tag
        {hFun = hFun} {occ = occ} {s⊢ = s⊢}
        {hG = hG} {gG = gG} {tag-ok = tag-ok}
        evidence)
      with allocate-coercion liftρ
        (C.cast-seq
          (C.cast-inst hFun occ s⊢)
          (C.cast-tag hG gG tag-ok))
  allocate-plan liftρ
      (plan-inst-fun-tag
        {hFun = hFun} {occ = occ} {s⊢ = s⊢}
        {hG = hG} {gG = gG} {tag-ok = tag-ok}
        evidence)
      | c⊢′@(C.cast-seq
          (C.cast-inst hFun′ occ′ s⊢′)
          (C.cast-tag hG′ gG′ tag-ok′)) =
    c⊢′ ,
    plan-inst-fun-tag
      (allocate-plan-evidence liftρ evidence)
  allocate-plan liftρ
      (plan-narrow-seq
        mode seal★ c⊒
        narrowing sequence-shape outer-comp
        s-shape s-comp t-shape t-comp
        s-plan t-plan)
      with allocate-plan liftρ s-plan
         | allocate-plan liftρ t-plan
  allocate-plan liftρ
      (plan-narrow-seq
        mode seal★ c⊒
        narrowing sequence-shape outer-comp
        s-shape s-comp t-shape t-comp
        s-plan t-plan)
      | s⊢′ , s-plan′ | t⊢′ , t-plan′ =
    cast-seq s⊢′ t⊢′ ,
    plan-narrow-seq
      (cast-weaken mode)
      (allocate-seal★ liftρ seal★)
      (cast-seq s⊢′ t⊢′ , NW.renameⁿ suc narrowing)
      (NW.renameⁿ suc narrowing)
      (cast-shape-rename suc sequence-shape)
      (allocate-composition outer-comp)
      (cast-shape-rename suc s-shape)
      (allocate-composition s-comp)
      (cast-shape-rename suc t-shape)
      (allocate-composition t-comp)
      s-plan′ t-plan′
  allocate-plan liftρ
      (plan-widen-seq
        mode seal★ c⊑
        widening sequence-shape outer-comp
        s-shape s-comp t-shape t-comp
        s-plan t-plan)
      with allocate-plan liftρ s-plan
         | allocate-plan liftρ t-plan
  allocate-plan liftρ
      (plan-widen-seq
        mode seal★ c⊑
        widening sequence-shape outer-comp
        s-shape s-comp t-shape t-comp
        s-plan t-plan)
      | s⊢′ , s-plan′ | t⊢′ , t-plan′ =
    cast-seq s⊢′ t⊢′ ,
    plan-widen-seq
      (cast-weaken mode)
      (allocate-seal★ liftρ seal★)
      (cast-seq s⊢′ t⊢′ , NW.renameʷ suc widening)
      (NW.renameʷ suc widening)
      (cast-shape-rename suc sequence-shape)
      (allocate-composition outer-comp)
      (cast-shape-rename suc s-shape)
      (allocate-composition s-comp)
      (cast-shape-rename suc t-shape)
      (allocate-composition t-comp)
      s-plan′ t-plan′
  allocate-plan liftρ
      (plan-id-widen-seq
        seal★ c⊑
        widening sequence-shape outer-comp
        s-shape s-comp t-shape t-comp
        s-plan t-plan)
      with allocate-plan liftρ s-plan
         | allocate-plan liftρ t-plan
  allocate-plan liftρ
      (plan-id-widen-seq
        seal★ c⊑
        widening sequence-shape outer-comp
        s-shape s-comp t-shape t-comp
        s-plan t-plan)
      | s⊢′ , s-plan′ | t⊢′ , t-plan′ =
    cast-seq s⊢′ t⊢′ ,
    plan-id-widen-seq
      (allocate-id-seal★ liftρ)
      (allocate-id-widening liftρ c⊑)
      (NW.renameʷ suc widening)
      (cast-shape-rename suc sequence-shape)
      (allocate-composition outer-comp)
      (cast-shape-rename suc s-shape)
      (allocate-composition s-comp)
      (cast-shape-rename suc t-shape)
      (allocate-composition t-comp)
      s-plan′ t-plan′

target-administration-spine-right-allocation-proofᵀ :
  TargetAdministrationSpineRightAllocationᵀ
target-administration-spine-right-allocation-proofᵀ
    liftρ pending-empty =
  pending-empty
target-administration-spine-right-allocation-proofᵀ
    liftρ (pending-cons plan tail)
    with allocate-plan liftρ plan
       | target-administration-spine-right-allocation-proofᵀ liftρ tail
target-administration-spine-right-allocation-proofᵀ
    liftρ (pending-cons plan tail)
    | c⊢′ , plan′ | tail′ =
  pending-cons plan′ tail′
