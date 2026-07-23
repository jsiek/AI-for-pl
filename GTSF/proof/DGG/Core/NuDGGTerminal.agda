module proof.DGG.Core.NuDGGTerminal where

-- File Charter:
--   * Gives the three terminal DGG obligations separate, complete interfaces.
--   * Checks that independent forward-value, backward-value, and
--     backward-blame proofs compose through the closed Nu DGG spine to the
--     public gradual guarantee.
--   * Contains no operational proof assumptions beyond its three arguments.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)

open import DynamicGradualGuarantee using (GradualDGG)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; _—↠[_]_
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; Value; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.DGG.Core.NuDGGSpine using
  ( closed-nu-dgg⇒gradual-dgg
  ; closed-nu-terminal-simulation⇒closed-nu-dgg
  )


terminal-components⇒gradual-dgg :
  (forward-source-value :
    ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
    RuntimeOK N →
    RuntimeOK N′ →
    [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
    ∀ V χs →
    N —↠[ χs ] V →
    Value V →
    ∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
    (∃[ Φ ] (Σ[ ρ ∈
        StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
    (Σ[ q ∈
        (Φ ∣ applyTyCtxs χs 0
          ⊢ applyTys χs A ⊑ applyTys χs′ B
          ⊣ applyTyCtxs χs′ 0) ]
      ((N′ —↠[ χs′ ] V′) ×
       Value V′ ×
       (leftStoreⁱ ρ ≡ applyStores χs []) ×
       (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
       Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
         ⊢ᴺ V ⊑ V′
         ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))) →
  (backward-target-value-or-source-blame :
    ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
    RuntimeOK N →
    RuntimeOK N′ →
    [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
    ∀ V′ χs′ →
    N′ —↠[ χs′ ] V′ →
    Value V′ →
      (∃[ V ] (Σ[ χs ∈ StoreChanges ]
      (∃[ Φ ] (Σ[ ρ ∈
          StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
      (Σ[ q ∈
          (Φ ∣ applyTyCtxs χs 0
            ⊢ applyTys χs A ⊑ applyTys χs′ B
            ⊣ applyTyCtxs χs′ 0) ]
        ((N —↠[ χs ] V) ×
         Value V ×
         (leftStoreⁱ ρ ≡ applyStores χs []) ×
         (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
         Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
           ⊢ᴺ V ⊑ V′
           ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))
      ⊎ (∃[ χs ] (N —↠[ χs ] blame)))) →
  (backward-target-blame :
    ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
    RuntimeOK N →
    RuntimeOK N′ →
    [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
    ∀ χs′ →
    N′ —↠[ χs′ ] blame →
    ∃[ χs ] (N —↠[ χs ] blame)) →
  GradualDGG
terminal-components⇒gradual-dgg
    forward-source-value
    backward-target-value-or-source-blame
    backward-target-blame =
  closed-nu-dgg⇒gradual-dgg
    (closed-nu-terminal-simulation⇒closed-nu-dgg
      (λ okN okN′ N⊑N′ →
        forward-source-value okN okN′ N⊑N′ ,
        backward-target-value-or-source-blame okN okN′ N⊑N′ ,
        backward-target-blame okN okN′ N⊑N′))
