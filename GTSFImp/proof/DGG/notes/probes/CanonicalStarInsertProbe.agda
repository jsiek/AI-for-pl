module proof.DGG.notes.probes.CanonicalStarInsertProbe where

-- File Charter:
--   * Shows that a structural `bind ★` plan need not retain the canonical
--     `rightBindTargetInsert` geometry used by the target step constructor.
--   * Builds the same dynamic target cell one unused center farther out.
--   * Confirms that direct-★-off-image insertion evidence, rather than
--     definitional equality with the canonical constructor, is sufficient.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans)

open import Types using
  (Ty; NonVar; _∈ᵗ_; ＇_; ★; _[_]ᵗ; ⇑ᵗ)
open import Consistency using
  (_↪ᵗ_; empty; id↪ᵗ; skip; wk↪ᵗ; Env∼; _⊢_∼_; instᵐ; inst_;
   ↑ᶜ_; close-instᶜ)
open import Imprecision using (X⊑★)
open import TyStore using (store-empty; store-bind; lookupStore)
open import CastTerms using
  (Term; Value; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import proof.TypeInTermSubst using (StoreRename-wk-bind)
open import proof.TypeInTermSubst using (renameᵗ-wk-eq)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import proof.DGG.CtxImp as CTX
import proof.DGG.CenterRename as CR
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.TargetExtend as TE
import Reduction
open import Reduction using
  (StoreChanges; []; _∷_; bind; applyBody; applyStores; β-inst)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof


base : CTX.World 0 0 0
base = CTX.emptyʷ

canonical : CTX.World 0 1 1
canonical = CTX.rightOnlyWorld base ★ (inj₁ refl)

shifted : CTX.World 0 1 2
shifted = CTX.skip-centerʷ canonical

base-to-shifted : 0 ↪ᵗ 2
base-to-shifted = empty


shifted-star-insert : TE.TargetInsert wk↪ᵗ base-to-shifted base shifted
shifted-star-insert = TE.target-insert-view record
  { sourceStore-kept = refl
  ; transport⊑ᵂ = λ p →
      CR.rename-⊑ᵂ {W = canonical} (skip id↪ᵗ)
        (TE.right-bind-transport⊑ᵂᵀ
          {W = base} {B′ = ★} {fresh = inj₁ refl} p)
  ; targetStore-rename = StoreRename-wk-bind {C = ★}
  ; source-resolve = λ ()
  ; target-resolve = λ ()
  ; align-insert = λ { {Xᴸ = ()} }
  ; source-insert = λ ()
  ; target-insert = λ ()
  ; impEnv-insert = λ ()
  ; impEnv-off-insert = λ
      { {Z′ = Fin.zero} off → refl
      ; {Z′ = Fin.suc Fin.zero} off → refl
      }
  ; target-center-reflect = λ { {Z = ()} }
  ; target-source-reflect = λ { {Xᴸ = ()} }
  ; targetLookup-insert = λ ()
  ; targetLookup-off = λ { Fin.zero off → inj₁ refl }
  }
shifted-follows-bind-star : CTX.targetStoreʷ shifted ≡
    applyStores (bind ★ ∷ []) (CTX.targetStoreʷ base)
shifted-follows-bind-star = refl

shifted-direct-star-off : TE.TargetInsertDirectStarOff shifted-star-insert
shifted-direct-star-off =
  TE.bindStarTargetInsertDirectStarOff
    shifted-star-insert shifted-follows-bind-star

shifted-provenance : ∀ {γ : CTX.CtxImp base}
    {M M′ : Term 0} {A B : Ty 0} {p : A CTX.⊑ᵂ⟨ base ⟩ B}
  → (rel : base CTI2.∣ γ ⊢² M ⊑ M′ ∶ p)
  → TE.TargetInsertProvenance shifted shifted-star-insert rel
shifted-provenance =
  TE.directStarOffTargetInsertProvenance
    shifted-star-insert shifted-direct-star-off


shifted-center≢canonical-center : 2 ≢ 1
shifted-center≢canonical-center ()


shifted-plan : StructuralWorldExtendᴿ (bind ★ ∷ []) base shifted
shifted-plan = structural-bind shifted-star-insert shifted-follows-bind-star
  structural-[]


shifted-structural-target-inst-step : ∀
    {A : Ty 1} {B E : Ty 0}
    {μ : Env∼ 0} {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    {V : Term 0}
  → (vV : Value V)
  → (B≠★ : B ≢ ★)
  → (spine : InstantiationSpine B E)
  → StructuralTargetInstantiationPackage shifted (⇑ᵗᵐ V)
      (name-type-app-frame (applyBody (bind ★) A) Fin.zero
          refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero A) ▻ⁱ
        reveal-frame (〖 Fin.zero , ★ ↑ A 〗) ▻ⁱ
        type-transport-frame
          (trans (replace-zero-open A ★)
            (sym (renameᵗ-wk-eq (A [ ★ ]ᵗ)))) ▻ⁱ
        cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
        type-transport-frame (renameᵗ-wk-eq B) ▻ⁱ
        mapInstantiationSpine (bind ★) spine)
  → StructuralTargetInstantiationPackage base V
      (cast-frame ((inst c) B≠★) ▻ⁱ spine)
shifted-structural-target-inst-step vV B≠★ spine child =
  structural-target-bind-step shifted-star-insert refl
    (lift-instantiation-spine-bind (β-inst vV B≠★) spine) child
