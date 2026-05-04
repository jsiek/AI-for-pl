module proof.DGGSimLeftTypeApp where

-- File Charter:
--   * Type-application helper interfaces for the left-to-right simulation.
--   * Owns polymorphic beta-family obligations and fresh-seal synchronization
--     points for type application.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([]; length)
open import Data.Product using (_×_; ∃-syntax)

open import Types
open import Imprecision
open import Conversion
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon

postulate
  sim-left-tyapp :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B T C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ M M′ (`∀ A) (`∀ B) →
    Σˡ ∣ M —→ Σˡ′ ∣ N →
    ∃[ Ψˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Σʳ′ ] ∃[ N′ ]
         ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ′ Σˡ′ (N ⦂∀ A [ T ]) N′ C D))

  sim-left-beta-Λ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ (Λ V) M′ (`∀ A) (`∀ B) →
    ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Σʳ′ ] ∃[ N′ ]
         ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ′ Σˡ′
            ((V [ ｀ (length Σˡ) ]ᵀ) ↑ convert↑ A (length Σˡ))
            N′ C D))

  sim-left-beta-up-∀ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T p C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ (V ⇑ (`∀A⊑∀B p)) M′ (`∀ A) (`∀ B) →
    ∃[ Σʳ′ ] ∃[ N′ ]
      ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
       TermRel Ψˡ Σˡ ((V ⦂∀ src⊑ p [ T ]) ⇑ p [ T ]⊑) N′ C D)

  sim-left-beta-down-∀ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T p C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ (V ⇓ (`∀A⊑∀B p)) M′ (`∀ A) (`∀ B) →
    ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Σʳ′ ] ∃[ N′ ]
         ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ′ Σˡ′
            (((V ⦂∀ tgt⊑ p [ ｀ (length Σˡ) ]) ⇓
              p [ ｀ (length Σˡ) ]⊑) ↑
              convert↑ (src⊑ p) (length Σˡ))
            N′ C D))

  sim-left-beta-down-ν :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B C T p D E} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ (V ⇓ (`∀A⊑B B p)) M′ (`∀ A) C →
    ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Σʳ′ ] ∃[ N′ ]
         ((Σʳ ∣ (M′ ⦂∀ C [ T ]) —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ′ Σˡ′
            ((V ⇓ p [ ｀ (length Σˡ) ]⊑) ↑
              convert↑ (src⊑ p) (length Σˡ))
            N′ D E))

  sim-left-beta-up-ν :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B p C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ (V ⇑ (`∀A⊑B B p)) M′ A B →
    ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ Σʳ′ ] ∃[ N′ ]
         ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
          TermRel Ψˡ′ Σˡ′
            ((V ⦂∀ src⊑ p [ ｀ (length Σˡ) ]) ⇑
              p [ ｀ (length Σˡ) ]⊑)
            N′ C D))

  sim-left-beta-reveal-∀ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T c C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ (V ↑ ↑-∀ c) M′ (`∀ A) (`∀ B) →
    ∃[ Σʳ′ ] ∃[ N′ ]
      ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
       TermRel Ψˡ Σˡ
         ((V ⦂∀ src↑ (⟰ᵗ Σˡ) c [ T ]) ↑ subst↑ (singleTyEnv T) c)
         N′ C D)

  sim-left-beta-conceal-∀ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V M′ A B T c C D} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ (V ↓ ↓-∀ c) M′ (`∀ A) (`∀ B) →
    ∃[ Σʳ′ ] ∃[ N′ ]
      ((Σʳ ∣ (M′ ⦂∀ B [ T ]) —↠ Σʳ′ ∣ N′) ×
       TermRel Ψˡ Σˡ
         ((V ⦂∀ src↓ (⟰ᵗ Σˡ) c [ T ]) ↓ subst↓ (singleTyEnv T) c)
         N′ C D)
