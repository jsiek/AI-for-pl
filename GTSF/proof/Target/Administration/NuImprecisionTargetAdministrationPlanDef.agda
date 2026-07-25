module proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef where

-- File Charter:
--   * Defines cast-local hereditary evidence for target administration.
--   * Stores exact right replacement or cast shape/composition evidence in
--     every plan that advances term imprecision directly.
--   * Distinguishes narrow, ordinary-widen, and identity-only-widen sequence
--     plans, retaining the whole cast evidence and each component triangle.
--   * Records the intermediate precision index at every coercion sequence;
--     `inst` is a boundary where post-allocation QTI supplies a fresh plan.
--   * Contains no simulation result, outcome carrier, implementation,
--     postulate, hole, permissive option, or compatibility wrapper.

open import Agda.Builtin.Equality using (_≡_)
import CastImprecisionShape as CastShape
open import Coercions using
  ( Inert
  ; cast-id
  ; cast-gen
  ; cast-inst
  ; cast-seq
  ; cast-tag
  ; cast-unseal
  ; cast-untag
  ; genᵈ
  ; gen
  ; id
  ; id-onlyᵈ
  ; inst
  ; instᵈ
  ; tagTyAllowed
  ; unseal
  ; _!
  ; _？
  ; _︔_
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import ImprecisionComposition using
  (⌊_⌋; _；_≋_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (Narrowing; Widening; _∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( StoreImp
  ; rightStoreⁱ
  )
open import Types using
  ( Ty
  ; WfTy
  ; occurs
  ; ★
  ; Ground
  ; ＇_
  ; _⇒_
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import TermTyping using (CastMode; SealModeStore★)


data TargetAdministrationPlan
    {Φ Δᴸ Δᴿ}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (A : Ty) :
    ∀ {μ B C c}
      (c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ)
      (q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ) →
    Set where

  plan-inert :
    ∀ {μ B C c}
      {c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    Inert c →
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
     (∃[ μ′ ] ∃[ s ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊒ C)
        × (CastShape.narrowing CastShape.⊢ᶜ c ⦂ s)
        × (⌊ q ⌋ ； s ≋ ⌊ p ⌋))
     ⊎
     (∃[ μ′ ] ∃[ s ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊑ C)
        × (CastShape.widening CastShape.⊢ᶜ c ⦂ s)
        × (⌊ p ⌋ ； s ≋ ⌊ q ⌋))
     ⊎
     (∃[ s ]
        SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ)
        × (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ c ∶ B ⊑ C)
        × (CastShape.widening CastShape.⊢ᶜ c ⦂ s)
        × (⌊ p ⌋ ； s ≋ ⌊ q ⌋))) →
    TargetAdministrationPlan ρ A c⊢ p q

  plan-id :
    ∀ {μ B hB ok}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ (id B) B B
        × p [ β ↦ X′ ]ᴿ q)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ (id B) B B
        × q [ β ↦ X′ ]ᴿ p)
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ id B ∶ B ⊒ B)
        × (CastShape.narrowing CastShape.⊢ᶜ
          id B ⦂ shape)
        × (⌊ q ⌋ ； shape ≋ ⌊ p ⌋))
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ id B ∶ B ⊑ B)
        × (CastShape.widening CastShape.⊢ᶜ
          id B ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))
     ⊎
     (∃[ shape ]
        SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ)
        × (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ id B ∶ B ⊑ B)
        × (CastShape.widening CastShape.⊢ᶜ
          id B ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))) →
    TargetAdministrationPlan ρ A (cast-id {μ = μ} hB ok) p q

  plan-untag :
    ∀ {μ μ′ H hH gH ok}
      {shape}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ} →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ H ？ ∶ ★ ⊒ H →
    CastShape.narrowing CastShape.⊢ᶜ H ？ ⦂ shape →
    ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
    TargetAdministrationPlan ρ A
      (cast-untag {μ = μ} hH gH ok) p q

  plan-unseal :
    ∀ {μ α B hB αB∈Σ ok}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ (unseal α B) (＇ α) B
        × p [ β ↦ X′ ]ᴿ q)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ (unseal α B) (＇ α) B
        × q [ β ↦ X′ ]ᴿ p)
     ⊎
     (∃[ μ′ ] ∃[ s ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ unseal α B ∶ ＇ α ⊒ B)
        × (CastShape.narrowing CastShape.⊢ᶜ
          unseal α B ⦂ s)
        × (⌊ q ⌋ ； s ≋ ⌊ p ⌋))
     ⊎
     (∃[ μ′ ] ∃[ s ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ unseal α B ∶ ＇ α ⊑ B)
        × (CastShape.widening CastShape.⊢ᶜ
          unseal α B ⦂ s)
        × (⌊ p ⌋ ； s ≋ ⌊ q ⌋))
     ⊎
     (∃[ s ]
        SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ)
        × (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ unseal α B ∶ ＇ α ⊑ B)
        × (CastShape.widening CastShape.⊢ᶜ
          unseal α B ⦂ s)
        × (⌊ p ⌋ ； s ≋ ⌊ q ⌋))) →
    TargetAdministrationPlan ρ A
      (cast-unseal {μ = μ} {α = α} hB αB∈Σ ok) p q

  plan-inst :
    ∀ {μ B C s}
      {hB : WfTy Δᴿ B}
      {occ : occurs zero C ≡ true}
      {s⊢ : instᵈ μ ∣ suc Δᴿ
        ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s ∶ C =⇒ ⇑ᵗ B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ (inst B s) (`∀ C) B
        × p [ β ↦ X′ ]ᴿ q)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ (inst B s) (`∀ C) B
        × q [ β ↦ X′ ]ᴿ p)
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ inst B s ∶ `∀ C ⊒ B)
        × (CastShape.narrowing CastShape.⊢ᶜ
          inst B s ⦂ shape)
        × (⌊ q ⌋ ； shape ≋ ⌊ p ⌋))
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ inst B s ∶ `∀ C ⊑ B)
        × (CastShape.widening CastShape.⊢ᶜ
          inst B s ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))
     ⊎
     (∃[ shape ]
        SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ)
        × (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ inst B s ∶ `∀ C ⊑ B)
        × (CastShape.widening CastShape.⊢ᶜ
          inst B s ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))) →
    TargetAdministrationPlan ρ A
      (cast-inst {μ = μ} {A = C} hB occ s⊢) p q

  plan-fun-untag-gen :
    ∀ {μ C s}
      {hG : WfTy Δᴿ (★ ⇒ ★)}
      {gG : Ground (★ ⇒ ★)}
      {tag-ok : tagTyAllowed μ (★ ⇒ ★) ≡ true}
      {hFun : WfTy Δᴿ (★ ⇒ ★)}
      {occ : occurs zero C ≡ true}
      {s⊢ : genᵈ μ ∣ suc Δᴿ ∣ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s ∶ ⇑ᵗ (★ ⇒ ★) =⇒ C}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ} →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ (((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s)
          ★ (`∀ C)
        × p [ β ↦ X′ ]ᴿ q)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ (((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s)
          ★ (`∀ C)
        × q [ β ↦ X′ ]ᴿ p)
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s
          ∶ ★ ⊒ `∀ C)
        × (CastShape.narrowing CastShape.⊢ᶜ
          ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s ⦂ shape)
        × (⌊ q ⌋ ； shape ≋ ⌊ p ⌋))
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s
          ∶ ★ ⊑ `∀ C)
        × (CastShape.widening CastShape.⊢ᶜ
          ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))
     ⊎
     (∃[ shape ]
        SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ)
        × (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s
          ∶ ★ ⊑ `∀ C)
        × (CastShape.widening CastShape.⊢ᶜ
          ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))) →
    TargetAdministrationPlan ρ A
      (cast-seq
        (cast-untag hG gG tag-ok)
        (cast-gen hFun occ s⊢))
      p q

  plan-inst-fun-tag :
    ∀ {μ C s}
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
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ ((inst (★ ⇒ ★) s) ︔ ((★ ⇒ ★) !))
          (`∀ C) ★
        × p [ β ↦ X′ ]ᴿ q)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ ((inst (★ ⇒ ★) s) ︔ ((★ ⇒ ★) !))
          (`∀ C) ★
        × q [ β ↦ X′ ]ᴿ p)
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ (inst (★ ⇒ ★) s) ︔ ((★ ⇒ ★) !)
          ∶ `∀ C ⊒ ★)
        × (CastShape.narrowing CastShape.⊢ᶜ
          (inst (★ ⇒ ★) s) ︔ ((★ ⇒ ★) !) ⦂ shape)
        × (⌊ q ⌋ ； shape ≋ ⌊ p ⌋))
     ⊎
     (∃[ μ′ ] ∃[ shape ]
        CastMode μ′
        × SealModeStore★ μ′ (rightStoreⁱ ρ)
        × (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ (inst (★ ⇒ ★) s) ︔ ((★ ⇒ ★) !)
          ∶ `∀ C ⊑ ★)
        × (CastShape.widening CastShape.⊢ᶜ
          (inst (★ ⇒ ★) s) ︔ ((★ ⇒ ★) !) ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))
     ⊎
     (∃[ shape ]
        SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ)
        × (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
          ⊢ (inst (★ ⇒ ★) s) ︔ ((★ ⇒ ★) !)
          ∶ `∀ C ⊑ ★)
        × (CastShape.widening CastShape.⊢ᶜ
          (inst (★ ⇒ ★) s) ︔ ((★ ⇒ ★) !) ⦂ shape)
        × (⌊ p ⌋ ； shape ≋ ⌊ q ⌋))) →
    TargetAdministrationPlan ρ A
      (cast-seq
        (cast-inst hFun occ s⊢)
        (cast-tag hG gG tag-ok))
      p q

  plan-narrow-seq :
    ∀ {μ B C D s t}
      {s⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ B =⇒ C}
      {t⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C =⇒ D}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ}
      {shape s-shape t-shape} →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ s ︔ t ∶ B ⊒ D →
    Narrowing (s ︔ t) →
    CastShape.narrowing CastShape.⊢ᶜ s ︔ t ⦂ shape →
    ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
    CastShape.narrowing CastShape.⊢ᶜ s ⦂ s-shape →
    ⌊ r ⌋ ； s-shape ≋ ⌊ p ⌋ →
    CastShape.narrowing CastShape.⊢ᶜ t ⦂ t-shape →
    ⌊ q ⌋ ； t-shape ≋ ⌊ r ⌋ →
    TargetAdministrationPlan ρ A s⊢ p r →
    TargetAdministrationPlan ρ A t⊢ r q →
    TargetAdministrationPlan ρ A (cast-seq s⊢ t⊢) p q

  plan-widen-seq :
    ∀ {μ B C D s t}
      {s⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ B =⇒ C}
      {t⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C =⇒ D}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ}
      {shape s-shape t-shape} →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ s ︔ t ∶ B ⊑ D →
    Widening (s ︔ t) →
    CastShape.widening CastShape.⊢ᶜ s ︔ t ⦂ shape →
    ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
    CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
    ⌊ p ⌋ ； s-shape ≋ ⌊ r ⌋ →
    CastShape.widening CastShape.⊢ᶜ t ⦂ t-shape →
    ⌊ r ⌋ ； t-shape ≋ ⌊ q ⌋ →
    TargetAdministrationPlan ρ A s⊢ p r →
    TargetAdministrationPlan ρ A t⊢ r q →
    TargetAdministrationPlan ρ A (cast-seq s⊢ t⊢) p q

  plan-id-widen-seq :
    ∀ {μ B C D s t}
      {s⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ B =⇒ C}
      {t⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C =⇒ D}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ}
      {shape s-shape t-shape} →
    SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ s ︔ t ∶ B ⊑ D →
    Widening (s ︔ t) →
    CastShape.widening CastShape.⊢ᶜ s ︔ t ⦂ shape →
    ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
    CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
    ⌊ p ⌋ ； s-shape ≋ ⌊ r ⌋ →
    CastShape.widening CastShape.⊢ᶜ t ⦂ t-shape →
    ⌊ r ⌋ ； t-shape ≋ ⌊ q ⌋ →
    TargetAdministrationPlan ρ A s⊢ p r →
    TargetAdministrationPlan ρ A t⊢ r q →
    TargetAdministrationPlan ρ A (cast-seq s⊢ t⊢) p q
