{-# OPTIONS --safe #-}

module proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareProof where

-- File Charter:
--   * Derives the four constructor-specific paired all/gen ground-cast
--     squares from the general GenSafe consistency/imprecision induction.
--   * Projection is injection under consistency symmetry.
--   * Is parameterized only by that separate semantic induction.

open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types
import Imprecision as I
open import Consistency using
  (Env∼; _⊢_∼_; ∀ᶜ_; inst_; gen_)
import Consistency as C
open import CastTerms using
  (GenSafe; safe-⇒; safe-∀; safe-inst; safe-gen)
open import proof.Consistency using (gen-safe)
open import proof.ImprecisionConsistency using (nonstar-from-≢★)
open import
  proof.DGG.Catchup.MorePreciseGenSafeTargetGroundCastSquareDef
  using (MorePreciseGenSafeTargetGroundCastSquareᵀ)
open import
  proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareDef
open import proof.DGG.InjectionConsistency using
  (rename∼ⁱ; renameGenSafeⁱ)
open import proof.DGG.World


private
  sym-gen-safe : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {A B : Ty Δ}
      {c : ν ⊢ A ∼ B}
    → GenSafe c
    → GenSafe (C.sym∼ c)
  sym-gen-safe safe-⇒ = safe-⇒
  sym-gen-safe safe-∀ = safe-∀
  sym-gen-safe (safe-inst {c = c} ⦃ Anv ⦄ ⦃ zero∈A ⦄ B≢★) =
    safe-gen B≢★
      (gen-safe (C.transport-env∼ C.flip-instᵐ (C.sym∼ c))
        B≢★ Anv zero∈A)
  sym-gen-safe (safe-gen A≢★ safe) = safe-inst A≢★

  gen-safe-source-nonstar : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {A B : Ty Δ} {c : ν ⊢ A ∼ B}
    → GenSafe c
    → NonStar A
  gen-safe-source-nonstar safe-⇒ = nonstar-⇒
  gen-safe-source-nonstar safe-∀ = nonstar-∀
  gen-safe-source-nonstar (safe-inst B≢★) = nonstar-∀
  gen-safe-source-nonstar (safe-gen A≢★ safe) =
    nonstar-from-≢★ A≢★


module _
    (ground-square : MorePreciseGenSafeTargetGroundCastSquareᵀ)
  where

  endpoint-ground-square : ∀ {Γᴸ Γᴿ : CastTerms.Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ}
      {C A : Ty (CastTerms.Δᵉ Γᴸ)}
      {B G : Ty (CastTerms.Δᵉ Γᴿ)}
      {νᴸ : Env∼ (CastTerms.Δᵉ Γᴸ)}
      {νᴿ : Env∼ (CastTerms.Δᵉ Γᴿ)}
      {cᴸ : νᴸ ⊢ C ∼ A}
    → GenSafe cᴸ
    → Ground G
    → NonStar B
    → νᴿ ⊢ B ∼ G
    → C ⊑ᵀ⟨ γ ⟩ B
    → A ⊑ᵀ⟨ γ ⟩ ★
    → A ⊑ᵀ⟨ γ ⟩ G
  endpoint-ground-square {γ = γ} {cᴸ = cᴸ}
      safe Gᵍ Bns cᴿ pC qA =
    ground-square (renameGenSafeⁱ (ηᴸᶜ γ) safe)
      (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ)
      (C.renameNonStar (toRenameⁱ (ηᴿᶜ γ)) Bns)
      (rename∼ⁱ (ηᴿᶜ γ) cᴿ) pC qA

  endpoint-ground-projection-square : ∀ {Γᴸ Γᴿ : CastTerms.Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ}
      {C A : Ty (CastTerms.Δᵉ Γᴸ)}
      {G B : Ty (CastTerms.Δᵉ Γᴿ)}
      {νᴸ : Env∼ (CastTerms.Δᵉ Γᴸ)}
      {νᴿ : Env∼ (CastTerms.Δᵉ Γᴿ)}
      {cᴸ : νᴸ ⊢ C ∼ A}
    → GenSafe cᴸ
    → Ground G
    → NonStar B
    → νᴿ ⊢ G ∼ B
    → C ⊑ᵀ⟨ γ ⟩ ★
    → A ⊑ᵀ⟨ γ ⟩ B
    → C ⊑ᵀ⟨ γ ⟩ G
  endpoint-ground-projection-square {γ = γ} safe Gᵍ Bns cᴿ pC qA =
    endpoint-ground-square {γ = γ} (sym-gen-safe safe)
      Gᵍ Bns (C.sym∼ cᴿ) qA pC

  more-precise-paired-target-all-injection-ground-square :
    MorePrecisePairedTargetAllInjectionGroundSquareᵀ
  more-precise-paired-target-all-injection-ground-square
      {γ = γ} cᴸ Gᵍ Bns cᴿ pC qA =
    endpoint-ground-square {γ = γ} {cᴸ = ∀ᶜ cᴸ}
      safe-∀ Gᵍ Bns cᴿ pC qA

  more-precise-paired-target-gen-injection-ground-square :
    MorePrecisePairedTargetGenInjectionGroundSquareᵀ
  more-precise-paired-target-gen-injection-ground-square
      {γ = γ} {C = C} {cᴸ = cᴸ} safe Gᵍ Bns cᴿ pC qA =
    endpoint-ground-square {γ = γ} (safe-gen C≢★ safe)
      Gᵍ Bns cᴿ pC qA
    where
    C≢★ : C ≢ ★
    C≢★ refl = nonStar≢★ (gen-safe-source-nonstar safe) refl

  more-precise-paired-target-all-projection-ground-square :
    MorePrecisePairedTargetAllProjectionGroundSquareᵀ
  more-precise-paired-target-all-projection-ground-square
      {γ = γ} cᴸ Gᵍ Bns cᴿ pC qA =
    endpoint-ground-projection-square {γ = γ} {cᴸ = ∀ᶜ cᴸ}
      safe-∀ Gᵍ Bns cᴿ pC qA

  more-precise-paired-target-gen-projection-ground-square :
    MorePrecisePairedTargetGenProjectionGroundSquareᵀ
  more-precise-paired-target-gen-projection-ground-square
      {γ = γ} {C = C} {cᴸ = cᴸ} safe Gᵍ Bns cᴿ pC qA =
    endpoint-ground-projection-square {γ = γ}
      (safe-gen C≢★ safe)
      Gᵍ Bns cᴿ pC qA
    where
    C≢★ : C ≢ ★
    C≢★ refl = nonStar≢★ (gen-safe-source-nonstar safe) refl
