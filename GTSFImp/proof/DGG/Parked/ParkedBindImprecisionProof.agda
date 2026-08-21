module proof.DGG.Parked.ParkedBindImprecisionProof where

-- File Charter:
--   * Proves type-imprecision transport across the three canonical parked
--     bind worlds.
--   * Sits below both parked evolution and structural target insertion so
--     those modules can share the bind facts without an import cycle.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyVar; _⇒_; `∀; ★; ⇑ᵗ; ＇_; renameᵗ; renameᵗ-comp;
   renameᵗ-cong; renameᵗ-shift)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Consistency using (_↪ᵗ_; toRenameᵗ; keep; skip)
open import Imprecision using (X⊑X; X⊑★; _⊢_⊑_)
import proof.DGG.CtxImp as CTI2
open import proof.ImprecisionConsistency using
  (fin-suc-injective; rename-⊑)
open import proof.TypeInTermSubst using (toRename-keep-eq)

open CTI2 using
  (World;
   embedᴸ;
   embedᴿ;
   impEnvʷ;
   _⊑ᵂ⟨_⟩_)


renameᵗ-skip-eq : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ) (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (skip η)) B
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) B)
renameᵗ-skip-eq η B =
  trans (renameᵗ-cong B (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc B))


embed-keep-shift : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
  → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
embed-keep-shift η A =
  trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq η))
    (renameᵗ-shift (toRenameᵗ η) A)


both-bind-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {C : Ty Δᴸ} {D : Ty Δᴿ}
  → C ⊑ᵂ⟨ W ⟩ D
  → (bind : A ⊑ᵂ⟨ W ⟩ B)
  → ⇑ᵗ C ⊑ᵂ⟨ CTI2.bothBindWorld W A B bind ⟩ ⇑ᵗ D
both-bind-⊑ᵂ {W = W} {A = A} {B = B} {C = C} {D = D} p bind =
  subst≡
    (λ L → impEnvʷ (CTI2.bothBindWorld W A B bind) ⊢ L ⊑
      embedᴿ (CTI2.bothBindWorld W A B bind) (⇑ᵗ D))
    (sym (embed-keep-shift (CTI2.ηᴸʷ W) C))
    (subst≡
      (λ R → impEnvʷ (CTI2.bothBindWorld W A B bind) ⊢
        ⇑ᵗ (embedᴸ W C) ⊑ R)
      (sym (embed-keep-shift (CTI2.ηᴿʷ W) D))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))


right-bind-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {fresh : ⇑ᵗ B′ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (⇑ᵗ B′ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (skip (CTI2.ηᴸʷ W)) Xᴸ
              ≢ toRenameᵗ (keep (CTI2.ηᴿʷ W)) Yᴿ)}
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ CTI2.rightOnlyWorld W B′ fresh ⟩ ⇑ᵗ B
right-bind-⊑ᵂ {W = W} {B′ = B′} {A = A} {B = B}
    {fresh = fresh} p =
  subst≡
    (λ L → impEnvʷ (CTI2.rightOnlyWorld W B′ fresh) ⊢ L ⊑
      embedᴿ (CTI2.rightOnlyWorld W B′ fresh) (⇑ᵗ B))
    (sym (renameᵗ-skip-eq (CTI2.ηᴸʷ W) A))
    (subst≡
      (λ R → impEnvʷ (CTI2.rightOnlyWorld W B′ fresh) ⊢
        ⇑ᵗ (embedᴸ W A) ⊑ R)
      (sym (embed-keep-shift (CTI2.ηᴿʷ W) B))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))


left-bind-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A′ : Ty Δᴸ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → A ⊑ᵂ⟨ W ⟩ B
  → ⇑ᵗ A ⊑ᵂ⟨ CTI2.leftOnlyWorld W A′ ⟩ B
left-bind-⊑ᵂ {W = W} {A′ = A′} {A = A} {B = B} p =
  subst≡
    (λ L → impEnvʷ (CTI2.leftOnlyWorld W A′) ⊢ L ⊑
      embedᴿ (CTI2.leftOnlyWorld W A′) B)
    (sym (embed-keep-shift (CTI2.ηᴸʷ W) A))
    (subst≡
      (λ R → impEnvʷ (CTI2.leftOnlyWorld W A′) ⊢
        ⇑ᵗ (embedᴸ W A) ⊑ R)
      (sym (renameᵗ-skip-eq (CTI2.ηᴿʷ W) B))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))
