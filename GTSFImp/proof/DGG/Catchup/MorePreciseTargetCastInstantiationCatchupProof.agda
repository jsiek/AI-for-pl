{-# OPTIONS --safe #-}

module proof.DGG.Catchup.MorePreciseTargetCastInstantiationCatchupProof where

-- File Charter:
--   * Builds one private well-founded driver for target consistency-cast and
--     target-instantiation catch-up, including the paired instantiation root.
--   * Tracks pending casts, name frames, conversion potential, spine length,
--     and CTI structural descent in one lexicographic measure.
--   * Performs beta-inst allocation before the name phase, so gen/reveal/
--     conceal branches recurse in the target-extended world carried by gamma.
--   * Exports the three direct semantic interfaces without public fuel,
--     residual-family dispatchers, compatibility contexts, or result wrappers.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using () renaming ([] to []ᵗ)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_)
import Data.Nat.Induction as NatInduction
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (_×_; Σ-syntax; _,_)
import Data.Product.Relation.Binary.Lex.Strict as ProductLex
open import Data.Sum.Base using (inj₁; inj₂)
import Induction.WellFounded as WF
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
import Imprecision as I
open import TyStore using (TyStore)
open import TermCtx using (TermCtx)
open import Consistency using
  ( Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; idᵍ; _↦_; ∀ᶜ_; _!
  ; ？_; inst_; gen_; instᵐ; bot-elim; bot-intro; ground-nonstar
  ; _[_]ᶜ; ↑ᶜ_; close-instᶜ; wk↪ᵗ
  )
import Consistency as C
import Conversion as Conv
open Conv using (〖_,_↑_〗)
open import CastTerms using
  ( Ctx; Term; Value; Inert; GenSafe; ⟨_,_,_⟩; _⊢_⦂_; _⟨_⟩; _《_》
  ; `_; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_; _↑_; _↓_; blame
  ; inj; fun; all; genᵥ; ⇑ᵗᵐ
  )
import CastTerms as CT
open import Reduction using
  ( StoreChanges; []; _∷_; keep; bind; applyTy; applyBody; applyTys
  ; applyVar
  ; pure-step; β-id; β-inst; β-∀; β-gen; ground
  ; expand; tag-untag; ξ-⟨⟩; applyConsistencies
  ; _—↠[_]_; _—→[_]⟨_⟩_; _—↠[_]⟨_⟩_; _∎[]
  )
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
import proof.DGG.CastTermImprecisionTyping as CTIT
open import proof.DGG.Catchup.MorePreciseTargetCastValueCatchupDef
  using (MorePreciseTargetCastValueCatchupᵀ)
open import proof.DGG.Catchup.MorePreciseSourceLambdaClosingDef
  using (MorePreciseSourceLambdaClosingᵀ)
open import
  proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareDef
  using
    ( MorePrecisePairedTargetAllInjectionGroundSquareᵀ
    ; MorePrecisePairedTargetGenInjectionGroundSquareᵀ
    ; MorePrecisePairedTargetAllProjectionGroundSquareᵀ
    ; MorePrecisePairedTargetGenProjectionGroundSquareᵀ
    )
open import
  proof.DGG.Catchup.MorePreciseTargetInstantiationValueCatchupDef
  using (MorePreciseTargetInstantiationValueCatchupᵀ)
open import
  proof.DGG.Catchup.MorePrecisePairedTargetInstantiationValueCatchupDef
  using (MorePrecisePairedTargetInstantiationValueCatchupᵀ)
open import proof.DGG.TransportTermImprecisionStepDef
  using (TransportTargetBindᵀ)
open import proof.DGG.InjectionConsistency using (rename∼ⁱ)
open import proof.DGG.ConversionAbsentEndpointLemma using
  (reveal-absent-endpoints; conceal-absent-endpoints)
open import proof.DGG.SourceConversionLeftImprecisionLemma using
  (source-conceal-input-imprecisionᵀ)
open import proof.DGG.Inversion.SpineValueDef using
  ( AllValueView; allv-Λ; allv-∀; allv-gen; allv-reveal; allv-conceal
  ; SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal
  ; sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all
  ; variable-obligation-aligns
  )
open import proof.DGG.Inversion.RightInjInversion2Lemma using
  (right-inj-inversion²)
import proof.DGG.TagTransport as TT
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  ( CtxChange; WorldEvolution; keep-ctx; storeChange
  ; evolution-keep; evolution-bind-right; evolution-⊑ᵀ
  )
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution; evolutions-refl; evolutions-step-right; multi-⊑ᵀ
  ; applyVars-prepend
  ; multi-source-mark; multi-source-disaligned
  ; multi-source-reveal; multi-source-conceal
  ; multi-source-reveal-position; multi-source-conceal-position
  )
open import proof.Consistency using
  (gen-safe; castSize; castSize-open-var-≤)
open import proof.Imprecision using
  (imprecision-to-fresh; imprecision-no-star-to-bot; ★⊑-inv; ⊑-unique)
open import proof.ImprecisionConsistency using
  ( refl⊑; ground-cast-target⊑; ground-cast-source⊑
  ; expand-cast-source⊑; ground-targets-unique⊑
  ; ground-cast-target-unique⊑
  ; ground-target-nonvar-to-star⊑; all-ground-body
  ; nonstar-from-≢★; rename-occurs; unshift-nonvar
  ; ext-injective; renameᵗ-injective; fin-suc-injective
  )
import proof.TypeSafety.Progress as Prog
open import proof.TypeSafety.Progress using
  ( no-bot-value; to-ground; from-ground; same; other
  ; canonical-★; sv-tag
  )
open import proof.Reduction using
  (cast-↠; applyConsistencies-Inert; applyTys-★; applyVars)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef using
  ( InstantiationFrame; type-transport-frame; name-type-app-frame
  ; cast-frame; reveal-frame; conceal-frame
  ; InstantiationSpine; []ⁱ; _▻ⁱ_; applyInstantiationSpine
  ; mapInstantiationSpine; lambda-ready-child-spine
  )
open import proof.DGG.Catchup.StructuralValueInstantiationCastMassDef using
  (valueCastMass; spineCastMass; pendingCastMass)
open import proof.DGG.Catchup.StructuralValueInstantiationRankDef using
  ( InstantiationRank; inst-rank; pendingRank
  ; nameFrames; expPotential; spineLength
  )
open import proof.DGG.Catchup.StructuralValueInstantiationCastMassProof
  using (all-cast-mass-decreases)
open import proof.DGG.Catchup.StructuralValueInstantiationGenCastMassProof
  using (gen-primary-decreases)
open import
  proof.DGG.Catchup.StructuralValueInstantiationPendingCastMassProof
  using (pending-cast-mass-bind)
open import proof.DGG.Catchup.StructuralValueInstantiationRankProof using
  ( _<ʳ_; rank-name<; rank-exp<; rank-length<
  ; reveal-rank-decreases; conceal-rank-decreases
  )
open import proof.DGG.Catchup.StructuralValueInstantiationSpineCastMassProof
  using (spine-cast-mass-map)
open import proof.DGG.Catchup.StructuralValueInstantiationReductionProof
  using (lift-instantiation-spine-keep; lift-instantiation-spine-bind)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
open import proof.TypeInTermSubst using
  (renameᵗ-wk-eq; renameᵗᵐ-preserves-Value)


------------------------------------------------------------------------
-- Small canonical helpers retained from the old proof
------------------------------------------------------------------------

value→spine : ∀ {Δ} {V : Term Δ} → Value V → SpineValue V
value→spine (ƛ N) = sv-ƛ N
value→spine (Λ vV) = sv-Λ (value→spine vV)
value→spine ($ κ) = sv-$ κ
value→spine (vV 《 inert 》) = sv-cast (value→spine vV) inert
value→spine (vV ↑ fun) = sv-reveal-fun (value→spine vV)
value→spine (vV ↑ all) = sv-reveal-all (value→spine vV)
value→spine (vV ↓ CT.seal) = sv-seal (value→spine vV)
value→spine (vV ↓ fun) = sv-conceal-fun (value→spine vV)
value→spine (vV ↓ all) = sv-conceal-all (value→spine vV)


target-ground-cast-witness : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {A : Ty (CT.Δᵉ Γᴸ)}
    {B G : Ty (CT.Δᵉ Γᴿ)} {ν : Env∼ (CT.Δᵉ Γᴿ)}
  → (Gᵍ : Ground G)
  → (Bns : NonStar B)
  → (c : ν ⊢ B ∼ G)
  → A ⊑ᵀ⟨ γ ⟩ B
  → A ⊑ᵀ⟨ γ ⟩ ★
  → A ⊑ᵀ⟨ γ ⟩ G
target-ground-cast-witness {γ = γ} Gᵍ Bns c p q =
  ground-cast-target⊑
    (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ)
    (C.renameNonStar (toRenameⁱ (ηᴿᶜ γ)) Bns)
    (rename∼ⁱ (ηᴿᶜ γ) c) p q


target-expand-cast-witness : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {A : Ty (CT.Δᵉ Γᴸ)}
    {G B : Ty (CT.Δᵉ Γᴿ)} {ν : Env∼ (CT.Δᵉ Γᴿ)}
  → (Gᵍ : Ground G)
  → (Bns : NonStar B)
  → (c : ν ⊢ G ∼ B)
  → A ⊑ᵀ⟨ γ ⟩ ★
  → A ⊑ᵀ⟨ γ ⟩ B
  → A ⊑ᵀ⟨ γ ⟩ G
target-expand-cast-witness {γ = γ} Gᵍ Bns c p q =
  expand-cast-source⊑
    (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ)
    (C.renameNonStar (toRenameⁱ (ηᴿᶜ γ)) Bns)
    (rename∼ⁱ (ηᴿᶜ γ) c) p q


source-ground-cast-witness : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {H : Ty (CT.Δᵉ Γᴸ)} {B G : Ty (CT.Δᵉ Γᴿ)}
    {ν : Env∼ (CT.Δᵉ Γᴿ)}
  → (Hᵍ : Ground H)
  → (Gᵍ : Ground G)
  → (Bns : NonStar B)
  → (ν ⊢ B ∼ G)
  → H ⊑ᵀ⟨ γ ⟩ B
  → H ⊑ᵀ⟨ γ ⟩ G
source-ground-cast-witness {γ = γ} {H = H} {G = G}
    Hᵍ Gᵍ Bns c p =
  subst≡ (λ T → I._⊢_⊑_ (marksᶜ γ)
      (renameᵗ (toRenameⁱ (ηᴸᶜ γ)) H) T)
    center-eq (refl⊑ (renameᵗ (toRenameⁱ (ηᴸᶜ γ)) H))
  where
  center-eq : renameᵗ (toRenameⁱ (ηᴸᶜ γ)) H ≡
      renameᵗ (toRenameⁱ (ηᴿᶜ γ)) G
  center-eq = ground-cast-target-unique⊑
    (C.renameGround (toRenameⁱ (ηᴸᶜ γ)) Hᵍ)
    (C.renameGround (toRenameⁱ (ηᴸᶜ γ)) Hᵍ)
    (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ)
    (C.renameNonStar (toRenameⁱ (ηᴿᶜ γ)) Bns)
    (rename∼ⁱ (ηᴿᶜ γ) c)
    (refl⊑ (renameᵗ (toRenameⁱ (ηᴸᶜ γ)) H)) p


fun-target-ground-witness : ∀ {Δ : TyCtx} {μ : I.ImpEnv Δ}
    {ν : Env∼ Δ} {C D A A′ B G : Ty Δ}
  → Ground G
  → NonStar B
  → ν ⊢ B ∼ G
  → μ I.⊢ (C ⇒ D) ⊑ B
  → μ I.⊢ (A ⇒ A′) ⊑ ★
  → μ I.⊢ (A ⇒ A′) ⊑ G
fun-target-ground-witness ★⇒★ Bns (c ↦ d)
    (I.⇒⊑⇒ pC pD) (I.⇒⊑★ pA pA′) =
  I.⇒⊑⇒ pA pA′
fun-target-ground-witness (＇ X) Bns ()
    (I.⇒⊑⇒ pC pD) (I.⇒⊑★ pA pA′)
fun-target-ground-witness (‵ ι) Bns ()
    (I.⇒⊑⇒ pC pD) (I.⇒⊑★ pA pA′)
fun-target-ground-witness ∀★ Bns (∀ᶜ c) ()
    (I.⇒⊑★ pA pA′)
fun-target-ground-witness ∀★ Bns
    (gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c A≠★)
    (I.⇒⊑⇒ pC pD) (I.⇒⊑★ pA pA′)


fun-source-ground-witness : ∀ {Δ : TyCtx} {μ : I.ImpEnv Δ}
    {ν : Env∼ Δ} {C D A A′ B G : Ty Δ}
  → Ground G
  → NonStar B
  → ν ⊢ G ∼ B
  → μ I.⊢ (C ⇒ D) ⊑ ★
  → μ I.⊢ (A ⇒ A′) ⊑ B
  → μ I.⊢ (C ⇒ D) ⊑ G
fun-source-ground-witness ★⇒★ Bns (c ↦ d)
    (I.⇒⊑★ pC pD) (I.⇒⊑⇒ pA pA′) =
  I.⇒⊑⇒ pC pD
fun-source-ground-witness (＇ X) Bns ()
    (I.⇒⊑★ pC pD) (I.⇒⊑⇒ pA pA′)
fun-source-ground-witness (‵ ι) Bns ()
    (I.⇒⊑★ pC pD) (I.⇒⊑⇒ pA pA′)
fun-source-ground-witness ∀★ Bns
    (inst_ ⦃ Anv ⦄ ⦃ () ⦄ c B≢★)
    (I.⇒⊑★ pC pD) (I.⇒⊑⇒ pA pA′)


source-value-target-bottom-impossible : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {V : Term (CT.Δᵉ Γᴸ)}
    {A : Ty (CT.Δᵉ Γᴸ)}
  → Value V
  → Γᴸ ⊢ V ⦂ A
  → A ⊑ᵀ⟨ γ ⟩ `∀ (＇ Fin.zero)
  → ⊥
source-value-target-bottom-impossible {γ = γ} {A = `∀ A}
    vV V⊢ (I.∀⊑∀ body) =
  no-bot-value vV
    (subst≡ (λ A′ → _ ⊢ _ ⦂ `∀ A′) body-eq V⊢)
  where
  body-eq : A ≡ ＇ Fin.zero
  body-eq =
    renameᵗ-injective
      (ext-injective (toRenameⁱ-injective (ηᴸᶜ γ)))
      (imprecision-to-fresh body)
source-value-target-bottom-impossible {A = `∀ A} vV V⊢
    (I.∀⊑ Anv zero∈A body) =
  imprecision-no-star-to-bot refl body zero∈A


inert-source-nonstar : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {A B : Ty Δ}
    {c : ν ⊢ A ∼ B}
  → Inert c
  → NonStar A
inert-source-nonstar (inj ⦃ Gᵍ = Gᵍ ⦄) = ground-nonstar Gᵍ
inert-source-nonstar fun = nonstar-⇒
inert-source-nonstar all = nonstar-∀
inert-source-nonstar (genᵥ A≠★ safe) = nonstar-from-≢★ A≠★


gen-safe-source-nonvar : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
    {A B : Ty Δ} {c : ν ⊢ A ∼ B}
  → CT.GenSafe c
  → NonVar A
gen-safe-source-nonvar CT.safe-⇒ = nonvar-fun
gen-safe-source-nonvar CT.safe-∀ = nonvar-all
gen-safe-source-nonvar (CT.safe-inst B≠★) = nonvar-all
gen-safe-source-nonvar (CT.safe-gen A≠★ safe) =
  unshift-nonvar (gen-safe-source-nonvar safe)


paired-cast-ground-match : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {C A : Ty (CT.Δᵉ Γᴸ)} {H G : Ty (CT.Δᵉ Γᴿ)}
    {ν : Env∼ (CT.Δᵉ Γᴸ)}
  → (Cnv : NonVar C)
  → (Cns : NonStar C)
  → (Hᵍ : Ground H)
  → (Gᵍ : Ground G)
  → (c : ν ⊢ C ∼ A)
  → C ⊑ᵀ⟨ γ ⟩ H
  → A ⊑ᵀ⟨ γ ⟩ ★
  → A ⊑ᵀ⟨ γ ⟩ G
  → H ≡ G
paired-cast-ground-match {γ = γ} Cnv Cns Hᵍ Gᵍ c pH p★ qG =
  renameᵗ-injective (toRenameⁱ-injective (ηᴿᶜ γ))
    (ground-targets-unique⊑
      (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Hᵍ)
      (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ) pH q-inner)
  where
  p-inner-star = ground-target-nonvar-to-star⊑
    (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Hᵍ)
    (renameNonVar (toRenameⁱ (ηᴸᶜ γ)) Cnv) pH

  q-inner = ground-cast-source⊑
    (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ)
    (C.renameNonStar (toRenameⁱ (ηᴸᶜ γ)) Cns)
    (rename∼ⁱ (ηᴸᶜ γ) c) p-inner-star p★ qG


lift-left-ground-obligation : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {A : Ty (suc (CT.Δᵉ Γᴸ))} {B : Ty (CT.Δᵉ Γᴿ)}
  → I._⊢_⊑_ (I.instᵐ (marksᶜ γ))
      (renameᵗ (extᵗ (toRenameⁱ (ηᴸᶜ γ))) A)
      (⇑ᵗ (renameᵗ (toRenameⁱ (ηᴿᶜ γ)) B))
  → A ⊑ᵀ⟨ liftLeftᶜ γ ⟩ B
lift-left-ground-obligation {γ = γ} {A = A} body =
  subst≡ (λ Bᶜ → I._⊢_⊑_ _ _ Bᶜ)
    (sym (renameᵗ-skipⁱ (ηᴿᶜ γ) _))
    (subst≡ (λ Aᶜ → I._⊢_⊑_ _ Aᶜ _)
      (sym (renameᵗ-cong A
        (λ { Fin.zero → refl; (Fin.suc X) → refl }))) body)


right-injection-ground-match² : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (CT.Δᵉ Γᴸ)} {N : Term (CT.Δᵉ Γᴿ)}
    {A : Ty (CT.Δᵉ Γᴸ)} {H G : Ty (CT.Δᵉ Γᴿ)}
    {ν : Env∼ (CT.Δᵉ Γᴿ)}
    {Hᵍ : Ground H} {Gᵍ : Ground G}
    {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {p★ : A ⊑ᵀ⟨ γ ⟩ ★}
  → SpineValue M
  → Value N
  → γ ⊢² M
      ⊑ N ⟨ _! ⦃ Hᵍ ⦄ ⦃ H∼★ ⦄ (idᵍ Hᵍ) ⦃ Hns ⦄ ⟩ ∶ p★
  → A ⊑ᵀ⟨ γ ⟩ G
  → H ≡ G
right-injection-ground-match² {γ = γ} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
    sv vN (CTI.⊑cast² {p = pH} c′ prem p★) qG =
  renameᵗ-injective (toRenameⁱ-injective (ηᴿᶜ γ))
    (ground-targets-unique⊑
      (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Hᵍ)
      (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ) pH qG)
right-injection-ground-match² {γ = γ} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
    (sv-cast sv fun) vN
    (CTI.cast⊑cast² {p = pH} c c′ prem p★) qG =
  paired-cast-ground-match {γ = γ}
    nonvar-fun nonstar-⇒ Hᵍ Gᵍ c pH p★ qG
right-injection-ground-match² {γ = γ} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
    (sv-cast sv all) vN
    (CTI.cast⊑cast² {p = pH} c c′ prem p★) qG =
  paired-cast-ground-match {γ = γ}
    nonvar-all nonstar-∀ Hᵍ Gᵍ c pH p★ qG
right-injection-ground-match² {γ = γ} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
    (sv-cast sv (genᵥ A≠★ safe)) vN
    (CTI.cast⊑cast² {p = pH} c c′ prem p★) qG =
  paired-cast-ground-match {γ = γ}
    (unshift-nonvar (gen-safe-source-nonvar safe))
    (nonstar-from-≢★ A≠★) Hᵍ Gᵍ c pH p★ qG
right-injection-ground-match² {Gᵍ = ＇ Y} (sv-cast sv inj) vN
    (CTI.cast⊑cast² c c′ prem p★) ()
right-injection-ground-match² {Gᵍ = ‵ ι} (sv-cast sv inj) vN
    (CTI.cast⊑cast² c c′ prem p★) ()
right-injection-ground-match² {Gᵍ = ★⇒★} (sv-cast sv inj) vN
    (CTI.cast⊑cast² c c′ prem p★) ()
right-injection-ground-match² {Gᵍ = ∀★} (sv-cast sv inj) vN
    (CTI.cast⊑cast² c c′ prem p★) ()
right-injection-ground-match² {γ = γ} {H = H} {G = G}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-cast sv inert) vN
    (CTI.cast⊑² {p = p-inner-star} c prem p-outer-star) qG =
  right-injection-ground-match² {γ = γ} {H = H} {G = G}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem q-inner
  where
  q-inner = ground-cast-source⊑
    (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ)
    (C.renameNonStar (toRenameⁱ (ηᴸᶜ γ))
      (inert-source-nonstar inert))
    (rename∼ⁱ (ηᴸᶜ γ) c) p-inner-star p-outer-star qG
right-injection-ground-match² {γ = γ} {A = `∀ A} {H = H}
    {G = G} {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
    {H∼★ = H∼★} {Hns = Hns} (sv-Λ sv) vN
    (CTI.Λ⊑² Anv zero∈A vM (CT.⊢⟨⟩ N⊢ _) prem p★) qG =
  right-injection-ground-match² {γ = liftLeftᶜ γ} {H = H} {G = G}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem
    (lift-left-ground-obligation {γ = γ} {A = A} {B = G}
      (all-ground-body
        (renameNonVar (extᵗ (toRenameⁱ (ηᴸᶜ γ))) Anv)
        (rename-occurs (extᵗ (toRenameⁱ (ηᴸᶜ γ)))
          (ext-injective (toRenameⁱ-injective (ηᴸᶜ γ))) zero∈A)
        (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ) qG))

right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-reveal-fun sv) vN
    (CTI.reveal⊑-identity {p = I.⇒⊑★ pA pB}
      c⊢ position prem p★) (I.⇒⊑⇒ qA qB) =
  right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem (I.⇒⊑⇒ pA pB)
right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-reveal-fun sv) vN
    (CTI.reveal⊑-only² {p = I.⇒⊑★ pA pB}
      c⊢ position mark no-target represented prem p★)
    (I.⇒⊑⇒ qA qB) =
  right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem (I.⇒⊑⇒ pA pB)
right-injection-ground-match² {G = ＇ Y} (sv-reveal-fun sv) vN
    (CTI.reveal⊑-identity _ _ _ _) ()
right-injection-ground-match² {G = ‵ ι} (sv-reveal-fun sv) vN
    (CTI.reveal⊑-identity _ _ _ _) ()
right-injection-ground-match² {G = `∀ ★} (sv-reveal-fun sv) vN
    (CTI.reveal⊑-identity _ _ _ _) ()
right-injection-ground-match² {G = ＇ Y} (sv-reveal-fun sv) vN
    (CTI.reveal⊑-only² _ _ _ _ _ _ _) ()
right-injection-ground-match² {G = ‵ ι} (sv-reveal-fun sv) vN
    (CTI.reveal⊑-only² _ _ _ _ _ _ _) ()
right-injection-ground-match² {G = `∀ ★} (sv-reveal-fun sv) vN
    (CTI.reveal⊑-only² _ _ _ _ _ _ _) ()

right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-conceal-fun sv) vN
    (CTI.conceal⊑-identity {p = I.⇒⊑★ pA pB}
      c⊢ position prem p★) (I.⇒⊑⇒ qA qB) =
  right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem (I.⇒⊑⇒ pA pB)
right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-conceal-fun sv) vN
    (CTI.conceal⊑-only² {p = I.⇒⊑★ pA pB}
      c⊢ position mark no-target represented prem p★)
    (I.⇒⊑⇒ qA qB) =
  right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem (I.⇒⊑⇒ pA pB)
right-injection-ground-match² {G = ＇ Y} (sv-conceal-fun sv) vN
    (CTI.conceal⊑-identity _ _ _ _) ()
right-injection-ground-match² {G = ‵ ι} (sv-conceal-fun sv) vN
    (CTI.conceal⊑-identity _ _ _ _) ()
right-injection-ground-match² {G = `∀ ★} (sv-conceal-fun sv) vN
    (CTI.conceal⊑-identity _ _ _ _) ()
right-injection-ground-match² {G = ＇ Y} (sv-conceal-fun sv) vN
    (CTI.conceal⊑-only² _ _ _ _ _ _ _) ()
right-injection-ground-match² {G = ‵ ι} (sv-conceal-fun sv) vN
    (CTI.conceal⊑-only² _ _ _ _ _ _ _) ()
right-injection-ground-match² {G = `∀ ★} (sv-conceal-fun sv) vN
    (CTI.conceal⊑-only² _ _ _ _ _ _ _) ()


right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-reveal-all sv) vN
    (CTI.reveal⊑-identity {p = p₀} (Conv.⊢↑-∀ refl c⊢)
      position prem p★) qG =
  right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem
    (TT.transport↑-∀-fun c⊢
      (toRenameⁱ-injective (ηᴸᶜ γ))
      (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {H = H} {G = `∀ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-reveal-all sv) vN
    (CTI.reveal⊑-identity {p = p₀} (Conv.⊢↑-∀ refl c⊢)
      position prem p★) qG =
  right-injection-ground-match² {γ = γ} {H = H} {G = `∀ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem
    (TT.transport↑-∀-all c⊢
      (toRenameⁱ-injective (ηᴸᶜ γ))
      (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {G = ‵ ι}
    (sv-reveal-all sv) vN
    (CTI.reveal⊑-identity {p = p₀} (Conv.⊢↑-∀ refl c⊢)
      position prem p★) qG =
  ⊥-elim (TT.transport↑-∀-ι-⊥ c⊢
    (toRenameⁱ-injective (ηᴸᶜ γ))
    (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {G = ＇ Y}
    (sv-reveal-all sv) vN
    (CTI.reveal⊑-identity {p = p₀} (Conv.⊢↑-∀ refl c⊢)
      position prem p★) qG =
  ⊥-elim (TT.transport↑-∀-var-⊥ c⊢
    (toRenameⁱ-injective (ηᴸᶜ γ))
    (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-reveal-all sv) vN
    (CTI.reveal⊑-only² {p = p₀} (Conv.⊢↑-∀ refl c⊢)
      position mark no-target represented prem p★) qG =
  right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem
    (TT.transport↑-∀-fun c⊢
      (toRenameⁱ-injective (ηᴸᶜ γ))
      (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {H = H} {G = `∀ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-reveal-all sv) vN
    (CTI.reveal⊑-only² {p = p₀} (Conv.⊢↑-∀ refl c⊢)
      position mark no-target represented prem p★) qG =
  right-injection-ground-match² {γ = γ} {H = H} {G = `∀ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem
    (TT.transport↑-∀-all c⊢
      (toRenameⁱ-injective (ηᴸᶜ γ))
      (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {G = ‵ ι}
    (sv-reveal-all sv) vN
    (CTI.reveal⊑-only² {p = p₀} (Conv.⊢↑-∀ refl c⊢)
      position mark no-target represented prem p★) qG =
  ⊥-elim (TT.transport↑-∀-ι-⊥ c⊢
    (toRenameⁱ-injective (ηᴸᶜ γ))
    (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {G = ＇ Y}
    (sv-reveal-all sv) vN
    (CTI.reveal⊑-only² {p = p₀} (Conv.⊢↑-∀ refl c⊢)
      position mark no-target represented prem p★) qG =
  ⊥-elim (TT.transport↑-∀-var-⊥ c⊢
    (toRenameⁱ-injective (ηᴸᶜ γ))
    (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)

right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-conceal-all sv) vN
    (CTI.conceal⊑-identity {p = p₀} (Conv.⊢↓-∀ refl c⊢)
      position prem p★) qG =
  right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem
    (TT.transport↓-∀-fun c⊢
      (toRenameⁱ-injective (ηᴸᶜ γ))
      (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {H = H} {G = `∀ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-conceal-all sv) vN
    (CTI.conceal⊑-identity {p = p₀} (Conv.⊢↓-∀ refl c⊢)
      position prem p★) qG =
  right-injection-ground-match² {γ = γ} {H = H} {G = `∀ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem
    (TT.transport↓-∀-all c⊢
      (toRenameⁱ-injective (ηᴸᶜ γ))
      (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {G = ‵ ι}
    (sv-conceal-all sv) vN
    (CTI.conceal⊑-identity {p = p₀} (Conv.⊢↓-∀ refl c⊢)
      position prem p★) qG =
  ⊥-elim (TT.transport↓-∀-ι-⊥ c⊢
    (toRenameⁱ-injective (ηᴸᶜ γ))
    (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {G = ＇ Y}
    (sv-conceal-all sv) vN
    (CTI.conceal⊑-identity {p = p₀} (Conv.⊢↓-∀ refl c⊢)
      position prem p★) qG =
  ⊥-elim (TT.transport↓-∀-var-⊥ c⊢
    (toRenameⁱ-injective (ηᴸᶜ γ))
    (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-conceal-all sv) vN
    (CTI.conceal⊑-only² {p = p₀} (Conv.⊢↓-∀ refl c⊢)
      position mark no-target represented prem p★) qG =
  right-injection-ground-match² {γ = γ} {H = H} {G = ★ ⇒ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem
    (TT.transport↓-∀-fun c⊢
      (toRenameⁱ-injective (ηᴸᶜ γ))
      (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {H = H} {G = `∀ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    (sv-conceal-all sv) vN
    (CTI.conceal⊑-only² {p = p₀} (Conv.⊢↓-∀ refl c⊢)
      position mark no-target represented prem p★) qG =
  right-injection-ground-match² {γ = γ} {H = H} {G = `∀ ★}
    {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ} {H∼★ = H∼★} {Hns = Hns}
    sv vN prem
    (TT.transport↓-∀-all c⊢
      (toRenameⁱ-injective (ηᴸᶜ γ))
      (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {G = ‵ ι}
    (sv-conceal-all sv) vN
    (CTI.conceal⊑-only² {p = p₀} (Conv.⊢↓-∀ refl c⊢)
      position mark no-target represented prem p★) qG =
  ⊥-elim (TT.transport↓-∀-ι-⊥ c⊢
    (toRenameⁱ-injective (ηᴸᶜ γ))
    (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)
right-injection-ground-match² {γ = γ} {G = ＇ Y}
    (sv-conceal-all sv) vN
    (CTI.conceal⊑-only² {p = p₀} (Conv.⊢↓-∀ refl c⊢)
      position mark no-target represented prem p★) qG =
  ⊥-elim (TT.transport↓-∀-var-⊥ c⊢
    (toRenameⁱ-injective (ηᴸᶜ γ))
    (toRenameⁱ-injective (ηᴸᶜ γ)) p₀ qG)

right-injection-ground-match² {G = ‵ ι} (sv-seal sv) vN
    (CTI.conceal⊑-only² (Conv.⊢↓-seal X∈) position
      mark no-target represented prem p★) qG
    with qG
right-injection-ground-match² {G = ‵ ι} (sv-seal sv) vN
    (CTI.conceal⊑-only² (Conv.⊢↓-seal X∈) position
      mark no-target represented prem p★) qG | ()
right-injection-ground-match² {G = ★ ⇒ ★} (sv-seal sv) vN
    (CTI.conceal⊑-only² (Conv.⊢↓-seal X∈) position
      mark no-target represented prem p★) qG
    with qG
right-injection-ground-match² {G = ★ ⇒ ★} (sv-seal sv) vN
    (CTI.conceal⊑-only² (Conv.⊢↓-seal X∈) position
      mark no-target represented prem p★) qG | ()
right-injection-ground-match² {G = `∀ ★} (sv-seal sv) vN
    (CTI.conceal⊑-only² (Conv.⊢↓-seal X∈) position
      mark no-target represented prem p★) qG
    with qG
right-injection-ground-match² {G = `∀ ★} (sv-seal sv) vN
    (CTI.conceal⊑-only² (Conv.⊢↓-seal X∈) position
      mark no-target represented prem p★) qG | ()
right-injection-ground-match² {γ = γ} {G = ＇ Y}
    (sv-seal {X = Xᴸ} sv) vN
    (CTI.conceal⊑-only² (Conv.⊢↓-seal X∈) position
      mark no-target represented prem p★) qG =
  ⊥-elim (no-target Y
    (sym (variable-obligation-aligns {γ = γ} {X = Xᴸ} {Y = Y} qG)))
right-injection-ground-match² (sv-seal sv) vN
    (CTI.conceal⊑-identity (Conv.⊢↓-seal X∈) () prem p★) qG

right-injection-ground-match² () vN (CTI.•⊑² _ _ _ _) qG


target-id-cast-typing : ∀ {Γ : Ctx} {M : Term (CT.Δᵉ Γ)}
    {B : Ty (CT.Δᵉ Γ)} {ν : Env∼ (CT.Δᵉ Γ)}
  → (a : Atom B)
  → Γ ⊢ M ⟨ id {μ = ν} a ⟩ ⦂ B
  → Γ ⊢ M ⦂ B
target-id-cast-typing a (CT.⊢⟨⟩ M⊢ (id a′)) = M⊢


target-id-cast-inversion² : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (CT.Δᵉ Γᴸ)} {V′ : Term (CT.Δᵉ Γᴿ)}
    {A : Ty (CT.Δᵉ Γᴸ)} {B : Ty (CT.Δᵉ Γᴿ)}
    {ν : Env∼ (CT.Δᵉ Γᴿ)} {q : A ⊑ᵀ⟨ γ ⟩ B}
  → (a : Atom B)
  → Value V
  → Value V′
  → γ ⊢² V ⊑ V′ ⟨ id {μ = ν} a ⟩ ∶ q
  → γ ⊢² V ⊑ V′ ∶ q
target-id-cast-inversion² a vV vV′
    (CTI.⊑cast² {p = p} (id a′) prem q) =
  subst≡ (λ r → _ ⊢² _ ⊑ _ ∶ r) (⊑-unique p q) prem
target-id-cast-inversion² a (vV 《 inert 》) vV′
    (CTI.cast⊑cast² c (id a′) prem q) =
  CTI.cast⊑² c prem q
target-id-cast-inversion² a (vV 《 inert 》) vV′
    (CTI.cast⊑² c prem q) =
  CTI.cast⊑² c (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (Λ vV) vV′
    (CTI.Λ⊑² Anv zero∈A vV₀ V′⊢ prem q) =
  CTI.Λ⊑² Anv zero∈A vV₀ (target-id-cast-typing a V′⊢)
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↑ fun) vV′
    (CTI.reveal⊑-identity c⊢ position prem q) =
  CTI.reveal⊑-identity c⊢ position
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↑ fun) vV′
    (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q) =
  CTI.reveal⊑-only² c⊢ position mark no-target represented
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↑ all) vV′
    (CTI.reveal⊑-identity c⊢ position prem q) =
  CTI.reveal⊑-identity c⊢ position
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↑ all) vV′
    (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q) =
  CTI.reveal⊑-only² c⊢ position mark no-target represented
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↓ CT.seal) vV′
    (CTI.conceal⊑-identity c⊢ position prem q) =
  CTI.conceal⊑-identity c⊢ position
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↓ CT.seal) vV′
    (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q) =
  CTI.conceal⊑-only² c⊢ position mark no-target represented
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↓ fun) vV′
    (CTI.conceal⊑-identity c⊢ position prem q) =
  CTI.conceal⊑-identity c⊢ position
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↓ fun) vV′
    (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q) =
  CTI.conceal⊑-only² c⊢ position mark no-target represented
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↓ all) vV′
    (CTI.conceal⊑-identity c⊢ position prem q) =
  CTI.conceal⊑-identity c⊢ position
    (target-id-cast-inversion² a vV vV′ prem) q
target-id-cast-inversion² a (vV ↓ all) vV′
    (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q) =
  CTI.conceal⊑-only² c⊢ position mark no-target represented
    (target-id-cast-inversion² a vV vV′ prem) q


target-project-tag-untag : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (CT.Δᵉ Γᴸ)} {N : Term (CT.Δᵉ Γᴿ)}
    {A : Ty (CT.Δᵉ Γᴸ)} {H G : Ty (CT.Δᵉ Γᴿ)}
    {μ ν : Env∼ (CT.Δᵉ Γᴿ)} {Hᵍ : Ground H} {Gᵍ : Ground G}
    ⦃ H∼★ : μ ⊢ H ∼★ ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Hns : NonStar H ⦄ ⦃ Gns : NonStar G ⦄
    {p★ : A ⊑ᵀ⟨ γ ⟩ ★} {qG : A ⊑ᵀ⟨ γ ⟩ G}
  → SpineValue V
  → Value N
  → γ ⊢² V ⊑ N ⟨
      _! ⦃ Hᵍ ⦄ ⦃ H∼★ ⦄ (idᵍ Hᵍ) ⦃ Hns ⦄ ⟩ ∶ p★
  → H ≡ G
  → (N ⟨ _! ⦃ Hᵍ ⦄ ⦃ H∼★ ⦄ (idᵍ Hᵍ) ⦃ Hns ⦄ ⟩
      ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ) ⦃ Gns ⦄ ⟩
      Reduction.—→ N)
    × (γ ⊢² V ⊑ N ∶ qG)
target-project-tag-untag {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
    ⦃ H∼★ ⦄ ⦃ ★∼G ⦄ ⦃ Hns ⦄ ⦃ Gns ⦄ sv vN rel refl
    rewrite ground-unique Gᵍ Hᵍ | nonStar-unique Gns Hns =
  tag-untag ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄
      ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = Hns ⦄ vN ,
    right-inj-inversion² sv vN rel _


target-catchup-refl : ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , []ᵗ ⟩}
    {V : Term Δᴸ} {W′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → Value W′
  → γ ⊢² V ⊑ W′ ∶ p
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ W″ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈ ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , []ᵗ ⟩ ]
    Σ[ q ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (W′ —↠[ χsᴿ ] W″)
      × Value W″
      × MultiWorldEvolution {W = γ} {W′ = γ′} [] χsᴿ
      × (γ′ ⊢² V ⊑ W″ ∶ q)
target-catchup-refl {γ = γ} {W′ = W′} {p = p} vW′ rel =
  _ , _ , [] , W′ , γ , p , (W′ ∎[]) , vW′ , evolutions-refl , rel


target-catchup-keep : ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , []ᵗ ⟩}
    {V : Term Δᴸ} {L′ W′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → L′ Reduction.—→ W′
  → Value W′
  → γ ⊢² V ⊑ W′ ∶ p
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ W″ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈ ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ
      ⟨ Δᴿ′ , Σᴿ′ , []ᵗ ⟩ ]
    Σ[ q ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B ]
      (L′ —↠[ χsᴿ ] W″)
      × Value W″
      × MultiWorldEvolution {W = γ} {W′ = γ′} [] χsᴿ
      × (γ′ ⊢² V ⊑ W″ ∶ q)
target-catchup-keep {γ = γ} {L′ = L′} {W′ = W′} {p = p}
    step vW′ rel =
  _ , _ , keep ∷ [] , W′ , γ , p ,
    (L′
      —→[ keep ]⟨ pure-step step ⟩
     W′ ∎[]) ,
    vW′ ,
    evolutions-step-right refl evolution-keep evolutions-refl ,
    rel


------------------------------------------------------------------------
-- Private well-founded state for pending target instantiation
------------------------------------------------------------------------

private

  value-term : ∀ {Δ} {V : Term Δ} → Value V → Term Δ
  value-term {V = V} vV = V

  all-primary-decreases-at : ∀ {Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} {E : Ty Δ} {V : Term Δ}
    → (vV : Value V)
    → (d : C.extᵐ μ ⊢ A ∼ B)
    → (X : TyVar Δ)
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → pendingCastMass vV
        (name-type-app-frame A X refl refl ▻ⁱ
          cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
          mapInstantiationSpine keep spine) <
      pendingCastMass (vV 《 all {c = d} 》)
        (name-type-app-frame B X refl refl ▻ⁱ spine)
  all-primary-decreases-at {μ = μ} {A = A} {B = B}
      vV d X spine =
    subst≡
      (λ n → n < pendingCastMass (vV 《 all {c = d} 》)
        (name-type-app-frame B X refl refl ▻ⁱ spine))
      (sym (cong
        (λ n → valueCastMass vV + (castSize (d [ ＇ X ]ᶜ) + n))
        (spine-cast-mass-map keep spine)))
      (all-cast-mass-decreases
        {c = d [ ＇ X ]ᶜ} {d = d} vV spine
        (castSize-open-var-≤ d X))

  transport-target-type : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
      {V : Term (CT.Δᵉ Γᴸ)} {V′ : Term (CT.Δᵉ Γᴿ)}
      {A : Ty (CT.Δᵉ Γᴸ)} {B B′ : Ty (CT.Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → (eq : B ≡ B′)
    → γ ⊢² V ⊑ V′ ∶ p
    → γ ⊢² V ⊑ V′ ∶ subst≡ (A ⊑ᵀ⟨ γ ⟩_) eq p
  transport-target-type refl rel = rel

  cti-size : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
      {M : Term (CT.Δᵉ Γᴸ)} {M′ : Term (CT.Δᵉ Γᴿ)}
      {A : Ty (CT.Δᵉ Γᴸ)} {B : Ty (CT.Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → γ ⊢² M ⊑ M′ ∶ p
    → ℕ
  cti-size (CTI.x⊑x² x x′) = zero
  cti-size (CTI.ƛ⊑ƛ² prem) = suc (cti-size prem)
  cti-size (CTI.·⊑·² fun-prem arg-prem) =
    suc (cti-size fun-prem + cti-size arg-prem)
  cti-size (CTI.Λ⊑Λ² vV vV′ prem q) = suc (cti-size prem)
  cti-size (CTI.Λ⊑² Anv zero∈A vV target-typing prem q) =
    suc (cti-size prem)
  cti-size (CTI.•⊑•² p∀ prem q r) = suc (cti-size prem)
  cti-size (CTI.•⊑² p∀ prem q r) = suc (cti-size prem)
  cti-size (CTI.κ⊑κ² κ p) = zero
  cti-size (CTI.cast⊑cast² c c′ prem q) = suc (cti-size prem)
  cti-size (CTI.⊑cast² c′ prem q) = suc (cti-size prem)
  cti-size (CTI.⊑reveal-identity c′⊢ position prem q) =
    suc (cti-size prem)
  cti-size (CTI.⊑conceal-identity c′⊢ position prem q) =
    suc (cti-size prem)
  cti-size (CTI.cast⊑² c prem q) = suc (cti-size prem)
  cti-size (CTI.reveal⊑-identity c⊢ position prem q) =
    suc (cti-size prem)
  cti-size
      (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q) =
    suc (cti-size prem)
  cti-size (CTI.conceal⊑-identity c⊢ position prem q) =
    suc (cti-size prem)
  cti-size
      (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q) =
    suc (cti-size prem)
  cti-size
      (CTI.reveal⊑reveal² source-typing target-typing positions aligned
        represented prem q) =
    suc (cti-size prem)
  cti-size
      (CTI.conceal⊑conceal² source-typing target-typing positions aligned
        represented prem q) =
    suc (cti-size prem)
  cti-size (CTI.⊑reveal-rebase² target-typing rebase prem q) =
    suc (cti-size prem)
  cti-size (CTI.⊑conceal-rebase² target-typing rebase prem q) =
    suc (cti-size prem)
  cti-size (CTI.blame⊑² target-typing p) = zero
  cti-size (CTI.⊕⊑⊕² op left-prem right-prem r) =
    suc (cti-size left-prem + cti-size right-prem)

  InstantiationMeasure : Set
  InstantiationMeasure = ℕ × (ℕ × (ℕ × (ℕ × ℕ)))

  infix 4 _<measure_

  _<measure_ : InstantiationMeasure → InstantiationMeasure → Set
  _<measure_ =
    ProductLex.×-Lex _≡_ _<_
      (ProductLex.×-Lex _≡_ _<_
        (ProductLex.×-Lex _≡_ _<_
          (ProductLex.×-Lex _≡_ _<_ _<_)))

  rank-decrease→measure : ∀ {m m′ n n′ e e′ l l′ s s′}
    → m ≡ m′
    → inst-rank n e l <ʳ inst-rank n′ e′ l′
    → (m , (n , (e , (l , s)))) <measure
      (m′ , (n′ , (e′ , (l′ , s′))))
  rank-decrease→measure mass-eq (rank-name< names<) =
    inj₂ (mass-eq , inj₁ names<)
  rank-decrease→measure mass-eq (rank-exp< names-eq potential<) =
    inj₂ (mass-eq , inj₂ (names-eq , inj₁ potential<))
  rank-decrease→measure mass-eq
      (rank-length< names-eq potential-eq length<) =
    inj₂ (mass-eq ,
      inj₂ (names-eq ,
        inj₂ (potential-eq , inj₁ length<)))

  pending-measure : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
      {V : Term (CT.Δᵉ Γᴸ)} {V′ : Term (CT.Δᵉ Γᴿ)}
      {A : Ty (CT.Δᵉ Γᴸ)} {B E : Ty (CT.Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → (vV′ : Value V′)
    → (spine : InstantiationSpine B E)
    → γ ⊢² V ⊑ V′ ∶ p
    → InstantiationMeasure
  pending-measure vV′ spine rel =
    pendingCastMass vV′ spine ,
      (nameFrames spine ,
        (expPotential vV′ spine ,
          (spineLength spine , suc (cti-size rel))))

  name-measure : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
      {V : Term (CT.Δᵉ Γᴸ)} {V′ : Term (CT.Δᵉ Γᴿ)}
      {A : Ty (CT.Δᵉ Γᴸ)} {B E : Ty (CT.Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → (vV′ : Value V′)
    → (spine : InstantiationSpine B E)
    → γ ⊢² V ⊑ V′ ∶ p
    → InstantiationMeasure
  name-measure vV′ spine rel =
    pendingCastMass vV′ spine ,
      (nameFrames spine ,
        (expPotential vV′ spine ,
          (spineLength spine , cti-size rel)))

  measure-well-founded : WF.WellFounded _<measure_
  measure-well-founded =
    ProductLex.×-wellFounded NatInduction.<-wellFounded
      (ProductLex.×-wellFounded NatInduction.<-wellFounded
        (ProductLex.×-wellFounded NatInduction.<-wellFounded
          (ProductLex.×-wellFounded NatInduction.<-wellFounded
            NatInduction.<-wellFounded)))

  -- Unlike Progress.AllView, this private view puts the target syntax in the
  -- constructor index.  That constructor-form index lets Agda eliminate
  -- impossible CTI roots without a stuck equality split.
  data InstantiationAllView {Δ : TyCtx} (body : Ty (suc Δ)) :
      Term Δ → Set where
    inst-view-Λ : ∀ {W}
      → Value W
      → InstantiationAllView body (Λ W)

    inst-view-all : ∀ {μ : Env∼ Δ} {W} {A : Ty (suc Δ)}
        {c : C.extᵐ μ ⊢ A ∼ body}
      → Value W
      → InstantiationAllView body (W ⟨ ∀ᶜ c ⟩)

    inst-view-gen : ∀ {μ : Env∼ Δ} {W} {A : Ty Δ}
        {c : C.genᵐ μ ⊢ ⇑ᵗ A ∼ body}
        ⦃ body-nonvar : NonVar body ⦄
        ⦃ zero-in-body : Fin.zero ∈ᵗ body ⦄
      → Value W
      → (A≠★ : A ≢ ★)
      → GenSafe c
      → InstantiationAllView body (W ⟨ (gen c) A≠★ ⟩)

    inst-view-reveal : ∀ {W A}
        {c : Conv.Conv↑ (suc Δ) A body}
      → Value W
      → InstantiationAllView body (W ↑ Conv.`∀↑ c)

    inst-view-conceal : ∀ {W A}
        {c : Conv.Conv↓ (suc Δ) A body}
      → Value W
      → InstantiationAllView body (W ↓ Conv.`∀↓ c)

  progress-all-view : ∀ {Δ : TyCtx} {body : Ty (suc Δ)} {V : Term Δ}
    → Prog.AllView body V
    → InstantiationAllView body V
  progress-all-view (Prog.av-Λ vW refl) = inst-view-Λ vW
  progress-all-view (Prog.av-∀ vW refl) = inst-view-all vW
  progress-all-view (Prog.av-gen vW A≠★ safe refl) =
    inst-view-gen vW A≠★ safe
  progress-all-view (Prog.av-reveal vW refl) = inst-view-reveal vW
  progress-all-view (Prog.av-conceal vW refl) = inst-view-conceal vW

  -- A pending name application is operationally admissible only when its
  -- target name has no aligned source occupant in the current world.  The
  -- public beta-inst step establishes this provenance; the private driver
  -- retains it alongside the syntax-only InstantiationSpine.
  TargetOnlyNameᶜ : ∀ {Γᴸ Γᴿ : Ctx}
    → (γ : Γᴸ ⊑ᶜ Γᴿ)
    → TyVar (CT.Δᵉ Γᴿ)
    → Set
  TargetOnlyNameᶜ γ X = ∀ Xᴸ
    → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≢ toRenameⁱ (ηᴿᶜ γ) X

  target-only-name-fresh : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {X : TyVar (CT.Δᵉ Γᴿ)}
    → TargetOnlyNameᶜ γ X
    → RightBindFreshᶜ γ (＇ X)
  target-only-name-fresh {γ = γ} {X = X} target-only =
    inj₂ (Fin.suc X , refl , λ Xᴸ aligned →
      target-only Xᴸ (fin-suc-injective aligned))

  right-bind-new-target-only : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {B : Ty (CT.Δᵉ Γᴿ)}
      {fresh : RightBindFreshᶜ γ B}
    → TargetOnlyNameᶜ (bindRightᶜ γ B fresh) Fin.zero
  right-bind-new-target-only {γ = γ} Xᴸ ()

  target-only-name-evolution : ∀ {Γᴸ Γᴿ Γᴿ′ : Ctx}
      {W : Γᴸ ⊑ᶜ Γᴿ} {W′ : Γᴸ ⊑ᶜ Γᴿ′}
      {stepᴿ : CtxChange Γᴿ Γᴿ′}
      {X : TyVar (CT.Δᵉ Γᴿ)}
    → WorldEvolution {W = W} {W′ = W′} keep-ctx stepᴿ
    → TargetOnlyNameᶜ W X
    → TargetOnlyNameᶜ W′ (applyVar (storeChange stepᴿ) X)
  target-only-name-evolution {W = W} {W′ = W′} {X = X}
      evolution-keep target-only = target-only
  target-only-name-evolution {W = W} {W′ = W′} {X = X}
      (evolution-bind-right fresh refl) target-only
      Xᴸ aligned =
    target-only Xᴸ (fin-suc-injective aligned)

  lift-left-target-only : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {X : TyVar (CT.Δᵉ Γᴿ)}
    → TargetOnlyNameᶜ γ X
    → TargetOnlyNameᶜ (liftLeftᶜ γ) X
  lift-left-target-only {γ = γ} {X = X} target-only Fin.zero ()
  lift-left-target-only {γ = γ} {X = X} target-only
      (Fin.suc Xᴸ) aligned =
    target-only Xᴸ (fin-suc-injective aligned)

  multi-target-only-name : ∀ {Γᴸ Γᴿ Γᴿ′ : Ctx}
      {W : Γᴸ ⊑ᶜ Γᴿ} {W′ : Γᴸ ⊑ᶜ Γᴿ′}
      {χsᴿ : StoreChanges (CT.Δᵉ Γᴿ) (CT.Δᵉ Γᴿ′)}
      {X : TyVar (CT.Δᵉ Γᴿ)}
    → MultiWorldEvolution {W = W} {W′ = W′} [] χsᴿ
    → TargetOnlyNameᶜ W X
    → TargetOnlyNameᶜ W′ (applyVars χsᴿ X)
  multi-target-only-name {W = W} {W′ = W′} {X = X}
      evolutions-refl target-only = target-only
  multi-target-only-name {W = W} {W′ = W′} {X = X}
      (evolutions-step-right {W¹ = W¹} {χsᴿ = χsᴿ}
        {stepᴿ = stepᴿ}
        refl one tail) target-only
      rewrite applyVars-prepend stepᴿ χsᴿ X =
    multi-target-only-name {W = W¹} {W′ = W′} tail
      (target-only-name-evolution {W = W} one target-only)

  data SpineNamesTargetOnlyᶜ {Γᴸ Γᴿ : Ctx}
      (γ : Γᴸ ⊑ᶜ Γᴿ) : ∀ {A E}
      → InstantiationSpine A E → Set where
    names-[] : ∀ {A}
      → SpineNamesTargetOnlyᶜ γ ([]ⁱ {A = A})

    names-type-transport : ∀ {A B E} {eq : A ≡ B}
        {spine : InstantiationSpine B E}
      → SpineNamesTargetOnlyᶜ γ spine
      → SpineNamesTargetOnlyᶜ γ
          (type-transport-frame eq ▻ⁱ spine)

    names-name-type-app : ∀ {A C E} {B : Ty (suc (CT.Δᵉ Γᴿ))}
        {X : TyVar (CT.Δᵉ Γᴿ)} {eqA : A ≡ `∀ B}
        {eqC : C ≡ B [ ＇ X ]ᵗ} {spine : InstantiationSpine C E}
      → TargetOnlyNameᶜ γ X
      → SpineNamesTargetOnlyᶜ γ spine
      → SpineNamesTargetOnlyᶜ γ
          (name-type-app-frame B X eqA eqC ▻ⁱ spine)

    names-cast : ∀ {A B E} {μ : Env∼ (CT.Δᵉ Γᴿ)}
        {c : μ ⊢ A ∼ B} {spine : InstantiationSpine B E}
      → SpineNamesTargetOnlyᶜ γ spine
      → SpineNamesTargetOnlyᶜ γ (cast-frame c ▻ⁱ spine)

    names-reveal : ∀ {A B E} {c : Conv.Conv↑ (CT.Δᵉ Γᴿ) A B}
        {spine : InstantiationSpine B E}
      → SpineNamesTargetOnlyᶜ γ spine
      → SpineNamesTargetOnlyᶜ γ (reveal-frame c ▻ⁱ spine)

    names-conceal : ∀ {A B E} {c : Conv.Conv↓ (CT.Δᵉ Γᴿ) A B}
        {spine : InstantiationSpine B E}
      → SpineNamesTargetOnlyᶜ γ spine
      → SpineNamesTargetOnlyᶜ γ (conceal-frame c ▻ⁱ spine)

  map-spine-names-target-only : ∀ {Γᴸ Γᴿ Γᴿ′ : Ctx}
      {W : Γᴸ ⊑ᶜ Γᴿ} {W′ : Γᴸ ⊑ᶜ Γᴿ′}
      {stepᴿ : CtxChange Γᴿ Γᴿ′} {A E}
      {spine : InstantiationSpine A E}
    → (evolution : WorldEvolution {W = W} {W′ = W′}
        keep-ctx stepᴿ)
    → SpineNamesTargetOnlyᶜ W spine
    → SpineNamesTargetOnlyᶜ W′
        (mapInstantiationSpine (storeChange stepᴿ) spine)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution-keep names-[] = names-[] {γ = W′}
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution-keep
      (names-type-transport names) =
    names-type-transport {γ = W′}
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution-keep names)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution-keep
      (names-name-type-app target-only names) =
    names-name-type-app {γ = W′}
      (target-only-name-evolution {W = W} {W′ = W′}
        evolution-keep target-only)
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution-keep names)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution-keep (names-cast names) =
    names-cast {γ = W′}
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution-keep names)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution-keep (names-reveal names) =
    names-reveal {γ = W′}
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution-keep names)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution-keep (names-conceal names) =
    names-conceal {γ = W′}
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution-keep names)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution@(evolution-bind-right fresh refl) names-[] =
    names-[] {γ = W′}
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution@(evolution-bind-right fresh refl)
      (names-type-transport names) =
    names-type-transport {γ = W′}
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution names)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution@(evolution-bind-right fresh refl)
      (names-name-type-app target-only names) =
    names-name-type-app {γ = W′}
      (target-only-name-evolution {W = W} {W′ = W′}
        evolution target-only)
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution names)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution@(evolution-bind-right fresh refl) (names-cast names) =
    names-cast {γ = W′}
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution names)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution@(evolution-bind-right fresh refl) (names-reveal names) =
    names-reveal {γ = W′}
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution names)
  map-spine-names-target-only {W = W} {W′ = W′}
      evolution@(evolution-bind-right fresh refl) (names-conceal names) =
    names-conceal {γ = W′}
      (map-spine-names-target-only {W = W} {W′ = W′}
        evolution names)

  lift-left-spine-names : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {A E}
      {spine : InstantiationSpine A E}
    → SpineNamesTargetOnlyᶜ γ spine
    → SpineNamesTargetOnlyᶜ (liftLeftᶜ γ) spine
  lift-left-spine-names {γ = γ} names-[] =
    names-[] {γ = liftLeftᶜ γ}
  lift-left-spine-names {γ = γ} (names-type-transport names) =
    names-type-transport {γ = liftLeftᶜ γ}
      (lift-left-spine-names {γ = γ} names)
  lift-left-spine-names {γ = γ}
      (names-name-type-app target-only names) =
    names-name-type-app {γ = liftLeftᶜ γ}
      (lift-left-target-only {γ = γ} target-only)
      (lift-left-spine-names {γ = γ} names)
  lift-left-spine-names {γ = γ} (names-cast names) =
    names-cast {γ = liftLeftᶜ γ}
      (lift-left-spine-names {γ = γ} names)
  lift-left-spine-names {γ = γ} (names-reveal names) =
    names-reveal {γ = liftLeftᶜ γ}
      (lift-left-spine-names {γ = γ} names)
  lift-left-spine-names {γ = γ} (names-conceal names) =
    names-conceal {γ = liftLeftᶜ γ}
      (lift-left-spine-names {γ = γ} names)

  all-child-spine : ∀ {Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} {E : Ty Δ} {X : TyVar Δ}
      {d : C.extᵐ μ ⊢ A ∼ B}
    → InstantiationSpine (B [ ＇ X ]ᵗ) E
    → InstantiationSpine (`∀ A) E
  all-child-spine {A = A} {X = X} {d = d} spine =
    name-type-app-frame A X refl refl ▻ⁱ
    cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
    mapInstantiationSpine keep spine

  gen-child-spine : ∀ {Δ} {μ : Env∼ Δ}
      {A E : Ty Δ} {B : Ty (suc Δ)} {X : TyVar Δ}
      {c : C.genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    → InstantiationSpine (B [ ＇ X ]ᵗ) E
    → InstantiationSpine (⇑ᵗ A) (applyTy (bind (＇ X)) E)
  gen-child-spine {B = B} {X = X} {c = c} spine =
    cast-frame c ▻ⁱ
    reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
    type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
    mapInstantiationSpine (bind (＇ X)) spine

  reveal-child-spine : ∀ {Δ} {A B : Ty (suc Δ)} {E : Ty Δ}
      {X : TyVar Δ} {c : Conv.Conv↑ (suc Δ) A B}
    → InstantiationSpine (B [ ＇ X ]ᵗ) E
    → InstantiationSpine (applyTy (bind (＇ X)) (`∀ A))
        (applyTy (bind (＇ X)) E)
  reveal-child-spine {A = A} {B = B} {X = X} {c = c} spine =
    name-type-app-frame (applyBody (bind (＇ X)) A) Fin.zero
      refl refl ▻ⁱ
    type-transport-frame (applyBody-open-zero A) ▻ⁱ
    reveal-frame c ▻ⁱ
    reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
    type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
    mapInstantiationSpine (bind (＇ X)) spine

  conceal-child-spine : ∀ {Δ} {A B : Ty (suc Δ)} {E : Ty Δ}
      {X : TyVar Δ} {c : Conv.Conv↓ (suc Δ) A B}
    → InstantiationSpine (B [ ＇ X ]ᵗ) E
    → InstantiationSpine (applyTy (bind (＇ X)) (`∀ A))
        (applyTy (bind (＇ X)) E)
  conceal-child-spine {A = A} {B = B} {X = X} {c = c} spine =
    name-type-app-frame (applyBody (bind (＇ X)) A) Fin.zero
      refl refl ▻ⁱ
    type-transport-frame (applyBody-open-zero A) ▻ⁱ
    conceal-frame c ▻ⁱ
    reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
    type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
    mapInstantiationSpine (bind (＇ X)) spine

  inst-residual-tail : ∀ {Δ} {μ : Env∼ Δ}
      {B : Ty (suc Δ)} {B′ : Ty Δ}
      {c : instᵐ μ ⊢ B ∼ ⇑ᵗ B′}
    → InstantiationSpine
        ((applyBody (bind ★) B) [ ＇ Fin.zero ]ᵗ)
        (applyTy (bind ★) B′)
  inst-residual-tail {B = B} {B′ = B′} {c = c} =
    type-transport-frame (applyBody-open-zero B) ▻ⁱ
    reveal-frame (〖 Fin.zero , ★ ↑ B 〗) ▻ⁱ
    type-transport-frame
      (trans (replace-zero-open B ★)
        (sym (renameᵗ-wk-eq (B [ ★ ]ᵗ)))) ▻ⁱ
    cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
    type-transport-frame (renameᵗ-wk-eq B′) ▻ⁱ
    []ⁱ

  name-frame-target-only : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {A C E}
      {B : Ty (suc (CT.Δᵉ Γᴿ))} {X : TyVar (CT.Δᵉ Γᴿ)}
      {eqA : A ≡ `∀ B} {eqC : C ≡ B [ ＇ X ]ᵗ}
      {spine : InstantiationSpine C E}
    → SpineNamesTargetOnlyᶜ γ
        (name-type-app-frame B X eqA eqC ▻ⁱ spine)
    → TargetOnlyNameᶜ γ X
  name-frame-target-only {γ = γ}
      (names-name-type-app target-only names) =
    target-only

  name-frame-tail-names : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {A C E}
      {B : Ty (suc (CT.Δᵉ Γᴿ))} {X : TyVar (CT.Δᵉ Γᴿ)}
      {eqA : A ≡ `∀ B} {eqC : C ≡ B [ ＇ X ]ᵗ}
      {spine : InstantiationSpine C E}
    → SpineNamesTargetOnlyᶜ γ
        (name-type-app-frame B X eqA eqC ▻ⁱ spine)
    → SpineNamesTargetOnlyᶜ γ spine
  name-frame-tail-names {γ = γ}
      (names-name-type-app target-only names) = names

  all-child-spine-names : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {μ : Env∼ (CT.Δᵉ Γᴿ)}
      {A B : Ty (suc (CT.Δᵉ Γᴿ))} {E : Ty (CT.Δᵉ Γᴿ)}
      {X : TyVar (CT.Δᵉ Γᴿ)} {d : C.extᵐ μ ⊢ A ∼ B}
      {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
    → SpineNamesTargetOnlyᶜ γ
        (name-type-app-frame B X refl refl ▻ⁱ spine)
    → SpineNamesTargetOnlyᶜ γ (all-child-spine {d = d} spine)
  all-child-spine-names {γ = γ}
      (names-name-type-app target-only names) =
    names-name-type-app {γ = γ} target-only
      (names-cast {γ = γ}
        (map-spine-names-target-only {W = γ} {W′ = γ}
          evolution-keep names))

  gen-child-spine-names : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {μ : Env∼ (CT.Δᵉ Γᴿ)}
      {A E : Ty (CT.Δᵉ Γᴿ)}
      {B : Ty (suc (CT.Δᵉ Γᴿ))} {X : TyVar (CT.Δᵉ Γᴿ)}
      {c : C.genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
    → (target-only : TargetOnlyNameᶜ γ X)
    → SpineNamesTargetOnlyᶜ γ spine
    → SpineNamesTargetOnlyᶜ
        (bindRightᶜ γ (＇ X)
          (target-only-name-fresh {γ = γ} target-only))
        (gen-child-spine {c = c} spine)
  gen-child-spine-names {γ = γ} {X = X} target-only names =
    names-cast {γ = bindRightᶜ γ (＇ X)
        (target-only-name-fresh {γ = γ} target-only)}
      (names-reveal {γ = bindRightᶜ γ (＇ X)
          (target-only-name-fresh {γ = γ} target-only)}
        (names-type-transport {γ = bindRightᶜ γ (＇ X)
            (target-only-name-fresh {γ = γ} target-only)}
          (map-spine-names-target-only {W = γ}
            (evolution-bind-right
              (target-only-name-fresh {γ = γ} target-only) refl)
            names)))

  reveal-child-spine-names : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {A B : Ty (suc (CT.Δᵉ Γᴿ))}
      {E : Ty (CT.Δᵉ Γᴿ)} {X : TyVar (CT.Δᵉ Γᴿ)}
      {c : Conv.Conv↑ (suc (CT.Δᵉ Γᴿ)) A B}
      {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
    → (target-only : TargetOnlyNameᶜ γ X)
    → SpineNamesTargetOnlyᶜ γ spine
    → SpineNamesTargetOnlyᶜ
        (bindRightᶜ γ (＇ X)
          (target-only-name-fresh {γ = γ} target-only))
        (reveal-child-spine {c = c} spine)
  reveal-child-spine-names {γ = γ} {X = X} target-only names =
    names-name-type-app
      {γ = bindRightᶜ γ (＇ X)
        (target-only-name-fresh {γ = γ} target-only)}
      (right-bind-new-target-only {γ = γ})
      (names-type-transport
        {γ = bindRightᶜ γ (＇ X)
          (target-only-name-fresh {γ = γ} target-only)}
        (names-reveal
          {γ = bindRightᶜ γ (＇ X)
            (target-only-name-fresh {γ = γ} target-only)}
          (names-reveal
            {γ = bindRightᶜ γ (＇ X)
              (target-only-name-fresh {γ = γ} target-only)}
            (names-type-transport
              {γ = bindRightᶜ γ (＇ X)
                (target-only-name-fresh {γ = γ} target-only)}
              (map-spine-names-target-only {W = γ}
                (evolution-bind-right
                  (target-only-name-fresh {γ = γ} target-only) refl)
                names)))))

  conceal-child-spine-names : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {A B : Ty (suc (CT.Δᵉ Γᴿ))}
      {E : Ty (CT.Δᵉ Γᴿ)} {X : TyVar (CT.Δᵉ Γᴿ)}
      {c : Conv.Conv↓ (suc (CT.Δᵉ Γᴿ)) A B}
      {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
    → (target-only : TargetOnlyNameᶜ γ X)
    → SpineNamesTargetOnlyᶜ γ spine
    → SpineNamesTargetOnlyᶜ
        (bindRightᶜ γ (＇ X)
          (target-only-name-fresh {γ = γ} target-only))
        (conceal-child-spine {c = c} spine)
  conceal-child-spine-names {γ = γ} {X = X} target-only names =
    names-name-type-app
      {γ = bindRightᶜ γ (＇ X)
        (target-only-name-fresh {γ = γ} target-only)}
      (right-bind-new-target-only {γ = γ})
      (names-type-transport
        {γ = bindRightᶜ γ (＇ X)
          (target-only-name-fresh {γ = γ} target-only)}
        (names-conceal
          {γ = bindRightᶜ γ (＇ X)
            (target-only-name-fresh {γ = γ} target-only)}
          (names-reveal
            {γ = bindRightᶜ γ (＇ X)
              (target-only-name-fresh {γ = γ} target-only)}
            (names-type-transport
              {γ = bindRightᶜ γ (＇ X)
                (target-only-name-fresh {γ = γ} target-only)}
              (map-spine-names-target-only {W = γ}
                (evolution-bind-right
                  (target-only-name-fresh {γ = γ} target-only) refl)
                names)))))

  inst-residual-tail-names : ∀ {Γᴸ : Ctx} {Δ : TyCtx}
      {Σᴿ : TyStore (suc Δ)} {Ψᴿ : TermCtx (suc Δ)}
      {γ : Γᴸ ⊑ᶜ ⟨ suc Δ , Σᴿ , Ψᴿ ⟩} {μ : Env∼ Δ}
      {B : Ty (suc Δ)} {B′ : Ty Δ}
      {c : instᵐ μ ⊢ B ∼ ⇑ᵗ B′}
    → SpineNamesTargetOnlyᶜ γ
        (inst-residual-tail {B = B} {B′ = B′} {c = c})
  inst-residual-tail-names {γ = γ} {c = c} =
    names-type-transport {γ = γ}
      (names-reveal {γ = γ}
        (names-type-transport {γ = γ}
          (names-cast {γ = γ} {c = ↑ᶜ (close-instᶜ c)}
            (names-type-transport {γ = γ} (names-[] {γ = γ})))))


------------------------------------------------------------------------
-- Structural catch-up for a target cast
------------------------------------------------------------------------

module _
    (transport-target-bind : TransportTargetBindᵀ)
    (close-source-Λ : MorePreciseSourceLambdaClosingᵀ)
    (paired-all-injection-square :
      MorePrecisePairedTargetAllInjectionGroundSquareᵀ)
    (paired-gen-injection-square :
      MorePrecisePairedTargetGenInjectionGroundSquareᵀ)
    (paired-all-projection-square :
      MorePrecisePairedTargetAllProjectionGroundSquareᵀ)
    (paired-gen-projection-square :
      MorePrecisePairedTargetGenProjectionGroundSquareᵀ)
  where

  paired-projection-ground-witness : ∀ {Γᴸ Γᴿ : Ctx}
      {γ : Γᴸ ⊑ᶜ Γᴿ}
      {C A : Ty (CT.Δᵉ Γᴸ)} {G B : Ty (CT.Δᵉ Γᴿ)}
      {νᴸ : Env∼ (CT.Δᵉ Γᴸ)} {νᴿ : Env∼ (CT.Δᵉ Γᴿ)}
      {cᴸ : νᴸ ⊢ C ∼ A}
    → Inert cᴸ
    → Ground G
    → NonStar B
    → νᴿ ⊢ G ∼ B
    → C ⊑ᵀ⟨ γ ⟩ ★
    → A ⊑ᵀ⟨ γ ⟩ B
    → C ⊑ᵀ⟨ γ ⟩ G
  paired-projection-ground-witness {γ = γ} inj Gᵍ Bns cᴿ p★ qB =
    ⊥-elim (nonStar≢★ Bns
      (renameᵗ-injective (toRenameⁱ-injective (ηᴿᶜ γ)) (★⊑-inv qB)))
  paired-projection-ground-witness {γ = γ} fun Gᵍ Bns cᴿ p★ qB =
    fun-source-ground-witness
      (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ)
      (C.renameNonStar (toRenameⁱ (ηᴿᶜ γ)) Bns)
      (rename∼ⁱ (ηᴿᶜ γ) cᴿ) p★ qB
  paired-projection-ground-witness {γ = γ} {cᴸ = ∀ᶜ cᴸ}
      all Gᵍ Bns cᴿ p★ qB =
    paired-all-projection-square {γ = γ} cᴸ Gᵍ Bns cᴿ p★ qB
  paired-projection-ground-witness {γ = γ}
      (genᵥ A≠★ safe) Gᵍ Bns cᴿ p★ qB =
    paired-gen-projection-square {γ = γ} safe Gᵍ Bns cᴿ p★ qB

  -- The general spine phase starts once a polymorphic wrapper has exposed an
  -- arbitrary target value (notably beneath a generated universal cast).
  -- Its primary split is the next milestone; the name phase below already
  -- calls it at every transition that leaves the polymorphic-value grammar.
  mutual

    value-spine-catchup-acc : ∀ {Δᴸ Δᴿ : TyCtx}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {γ : ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , []ᵗ ⟩}
        {V : Term Δᴸ} {V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B E : Ty Δᴿ}
        {p : A ⊑ᵀ⟨ γ ⟩ B} {q : A ⊑ᵀ⟨ γ ⟩ E}
      → (rel : γ ⊢² V ⊑ V′ ∶ p)
      → (vV : Value V)
      → (vV′ : Value V′)
      → (spine : InstantiationSpine B E)
      → {spine-names : SpineNamesTargetOnlyᶜ γ spine}
      → Acc _<measure_ (pending-measure vV′ spine rel)
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ W′ ∈ Term Δᴿ′ ]
        Σ[ γ′ ∈
          ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ
          ⟨ Δᴿ′ , Σᴿ′ , []ᵗ ⟩ ]
        Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ E ]
          (applyInstantiationSpine V′ spine —↠[ χsᴿ ] W′)
          × Value W′
          × MultiWorldEvolution {W = γ} {W′ = γ′} [] χsᴿ
          × (γ′ ⊢² V ⊑ W′ ∶ r)
    value-spine-catchup-acc {Δᴿ = Δᴿ} {Σᴿ = Σᴿ} {γ = γ}
        {V′ = V′} {p = p} rel source-value target-value []ⁱ
        {spine-names = names-[]} access =
      Δᴿ , Σᴿ , [] , V′ , γ , p ,
        (V′ ∎[]) , target-value , evolutions-refl , rel

    value-spine-catchup-acc rel source-value target-value
        (type-transport-frame eq ▻ⁱ spine)
        {spine-names = names-type-transport names} (acc smaller)
        with value-spine-catchup-acc
          (transport-target-type eq rel)
          source-value target-value spine {spine-names = names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl , inj₁ (n<1+n _))))))
    value-spine-catchup-acc rel source-value target-value
        (type-transport-frame eq ▻ⁱ spine) (acc smaller)
      | child =
        child

    value-spine-catchup-acc rel source-value target-value
        (name-type-app-frame B X refl refl ▻ⁱ spine)
        {spine-names = names} (acc smaller)
        with name-spine-catchup-acc
          (progress-all-view
            (Prog.canonical-∀ target-value (CTIT.target-typing rel)))
          rel source-value target-value spine {spine-names = names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl ,
                  inj₂ (refl , n<1+n _))))))
    value-spine-catchup-acc rel source-value target-value
        (name-type-app-frame B X refl refl ▻ⁱ spine) (acc smaller)
      | child = child

    value-spine-catchup-acc rel source-value target-value
        (cast-frame c ▻ⁱ spine) {spine-names = names-cast names} access =
      {! normalize the pending target cast, then continue with the exact
         evolved relation, value, spine, and justified smaller state !}

    value-spine-catchup-acc rel source-value target-value
        (reveal-frame c ▻ⁱ spine)
        {spine-names = names-reveal names} access =
      {! normalize the pending target reveal, then continue with the exact
         evolved relation, value, spine, and justified smaller state !}

    value-spine-catchup-acc rel source-value target-value
        (conceal-frame c ▻ⁱ spine)
        {spine-names = names-conceal names} access =
      {! normalize the pending target conceal, then continue with the exact
         evolved relation, value, spine, and justified smaller state !}

    -- The name phase retains the target instantiation continuation explicitly.
    -- Every recursive target-wrapper case moves that wrapper into the spine;
    -- therefore the recursive relation is the actual CTI premise, even when a
    -- reveal-rebase enters a world with a nonempty gamma-carried frame stack.
    name-spine-catchup-acc : ∀ {Δᴸ Δᴿ : TyCtx}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {γ : ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , []ᵗ ⟩}
        {V : Term Δᴸ} {V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
        {X : TyVar Δᴿ}
        {p : A ⊑ᵀ⟨ γ ⟩ `∀ B} {q : A ⊑ᵀ⟨ γ ⟩ E}
      → InstantiationAllView B V′
      → (rel : γ ⊢² V ⊑ V′ ∶ p)
      → (vV : Value V)
      → (vV′ : Value V′)
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → {spine-names : SpineNamesTargetOnlyᶜ γ
          (name-type-app-frame B X refl refl ▻ⁱ spine)}
      → Acc _<measure_
          (name-measure vV′
            (name-type-app-frame B X refl refl ▻ⁱ spine) rel)
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ W′ ∈ Term Δᴿ′ ]
        Σ[ γ′ ∈
          ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ
          ⟨ Δᴿ′ , Σᴿ′ , []ᵗ ⟩ ]
        Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ E ]
          (applyInstantiationSpine V′
            (name-type-app-frame B X refl refl ▻ⁱ spine) —↠[ χsᴿ ] W′)
          × Value W′
          × MultiWorldEvolution {W = γ} {W′ = γ′} [] χsᴿ
          × (γ′ ⊢² V ⊑ W′ ∶ r)

    -- Constructor-indexed view impossibilities.  Listing every non-view target
    -- syntax keeps the subsequent CTI split exhaustive without a catch-all.
    name-spine-catchup-acc {V′ = ` x} () rel source-value target-value
        spine access
    name-spine-catchup-acc {V′ = ƛ M′} () rel source-value target-value
        spine access
    name-spine-catchup-acc {V′ = L′ · M′} () rel source-value target-value
        spine access
    name-spine-catchup-acc {V′ = M′ ⦂∀ C [ D ]} () rel source-value
        target-value spine access
    name-spine-catchup-acc {V′ = $ κ} () rel source-value target-value
        spine access
    name-spine-catchup-acc {V′ = L′ ⊕[ op ] M′} () rel source-value
        target-value spine access
    name-spine-catchup-acc {V′ = blame} () rel source-value target-value
        spine access

    -- Complete generic source-wrapper pass.  Each branch establishes the
    -- structural recursive call before its source replay obligation.
    name-spine-catchup-acc {γ = γ} view
        (CTI.Λ⊑² Anv zero∈A body-value target-typing prem q)
        (Λ outer-value) target-value spine {spine-names = names} (acc smaller)
        with name-spine-catchup-acc
          {q = {! pre-Lambda spine imprecision !}}
          view prem body-value target-value spine
          {spine-names = lift-left-spine-names {γ = γ} names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl ,
                  inj₂ (refl , n<1+n _))))))
    name-spine-catchup-acc view
        (CTI.Λ⊑² Anv zero∈A body-value target-typing prem q)
        (Λ outer-value) target-value spine (acc smaller)
      | child =
        {! replay source type abstraction after the spine catch-up !}

    name-spine-catchup-acc view (CTI.cast⊑² c prem q)
        (source-value 《 inert 》) target-value spine
        {spine-names = names} (acc smaller)
        with paired-name-spine-catchup-acc
          view prem inert source-value target-value spine
          {spine-names = names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl ,
                  inj₂ (refl , n<1+n _))))))
    name-spine-catchup-acc view (CTI.cast⊑² c prem q)
        (source-value 《 inert 》) target-value spine (acc smaller)
      | child = child

    name-spine-catchup-acc {γ = γ} {E = E} {q = final-q} view
        (CTI.reveal⊑-identity c⊢ position prem q)
        (source-value ↑ all) target-value spine
        {spine-names = names} (acc smaller)
        with name-spine-catchup-acc
          {q = subst≡ (λ A → A ⊑ᵀ⟨ γ ⟩ E)
            (sym (reveal-absent-endpoints c⊢ position)) final-q}
          view prem source-value target-value spine {spine-names = names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl ,
                  inj₂ (refl , n<1+n _))))))
    name-spine-catchup-acc {γ = γ} {q = final-q} view
        (CTI.reveal⊑-identity c⊢ position prem q)
        (source-value ↑ all) target-value spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution final-q ,
          reduction , value , evolution ,
          CTI.reveal⊑-identity
            (multi-source-reveal evolution c⊢)
            (trans (multi-source-reveal-position evolution c⊢) position)
            final (multi-⊑ᵀ evolution final-q)

    name-spine-catchup-acc view
        (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q)
        (source-value ↑ all) target-value spine
        {spine-names = names} (acc smaller)
        with name-spine-catchup-acc
          {q = {! pre-source-only-reveal spine imprecision !}}
          view prem source-value target-value spine {spine-names = names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl ,
                  inj₂ (refl , n<1+n _))))))
    name-spine-catchup-acc {q = final-q} view
        (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q)
        (source-value ↑ all) target-value spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution final-q ,
          reduction , value , evolution ,
          CTI.reveal⊑-only²
            (multi-source-reveal evolution c⊢)
            (λ eq → position
              (trans (sym (multi-source-reveal-position evolution c⊢)) eq))
            (multi-source-mark evolution mark)
            (multi-source-disaligned evolution no-target)
            (subst≡ (λ B → _ ⊑ᵀ⟨ γ′ ⟩ B) (applyTys-★ χsᴿ)
              (multi-⊑ᵀ evolution represented))
            final (multi-⊑ᵀ evolution final-q)

    name-spine-catchup-acc {γ = γ} {E = E} {q = final-q} view
        (CTI.conceal⊑-identity c⊢ position prem q)
        (source-value ↓ all) target-value spine
        {spine-names = names} (acc smaller)
        with name-spine-catchup-acc
          {q = subst≡ (λ A → A ⊑ᵀ⟨ γ ⟩ E)
            (sym (conceal-absent-endpoints c⊢ position)) final-q}
          view prem source-value target-value spine {spine-names = names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl ,
                  inj₂ (refl , n<1+n _))))))
    name-spine-catchup-acc {q = final-q} view
        (CTI.conceal⊑-identity c⊢ position prem q)
        (source-value ↓ all) target-value spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution final-q ,
          reduction , value , evolution ,
          CTI.conceal⊑-identity
            (multi-source-conceal evolution c⊢)
            (trans (multi-source-conceal-position evolution c⊢) position)
            final (multi-⊑ᵀ evolution final-q)

    name-spine-catchup-acc {γ = γ} {q = final-q} view
        (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
        (source-value ↓ all) target-value spine
        {spine-names = names} (acc smaller)
        with name-spine-catchup-acc
          {q = source-conceal-input-imprecisionᵀ {γ = γ}
            c⊢ mark no-target
            represented final-q}
          view prem source-value target-value spine {spine-names = names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl ,
                  inj₂ (refl , n<1+n _))))))
    name-spine-catchup-acc {q = final-q} view
        (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
        (source-value ↓ all) target-value spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution final-q ,
          reduction , value , evolution ,
          CTI.conceal⊑-only²
            (multi-source-conceal evolution c⊢)
            (λ eq → position
              (trans (sym (multi-source-conceal-position evolution c⊢)) eq))
            (multi-source-mark evolution mark)
            (multi-source-disaligned evolution no-target)
            (subst≡ (λ B → _ ⊑ᵀ⟨ γ′ ⟩ B) (applyTys-★ χsᴿ)
              (multi-⊑ᵀ evolution represented))
            final (multi-⊑ᵀ evolution final-q)

    name-spine-catchup-acc view (CTI.blame⊑² target-typing p)
        () target-value spine access

    -- Strict Lambda exposes the beta-inst allocation and then enters the
    -- general value/spine phase in the extended target store.
    name-spine-catchup-acc {B = B} {E = E} {X = X}
        (inst-view-Λ target-body-value)
        (CTI.Λ⊑Λ² source-body-value target-body-value′ prem p)
        (Λ source-outer-value) (Λ target-outer-value) spine access =
      {! expose the beta-inst/beta-Lambda residual relation and values in the
         extended worlds, then recurse at its exact smaller state !}

    -- A target all cast is moved from the value into the pending spine.
    name-spine-catchup-acc {γ = γ} {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p)
        source-value (target-body-value 《 all 》) spine
        {spine-names = names} (acc smaller)
        with value-spine-catchup-acc
          prem source-value target-body-value
          (all-child-spine {d = d} spine)
          {spine-names = all-child-spine-names {γ = γ} {d = d} names}
          (smaller (inj₁ (all-primary-decreases-at
            target-body-value d X spine)))
    name-spine-catchup-acc {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p)
        source-value (target-body-value 《 all 》) spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ , W′ , γ′ , r ,
          (applyInstantiationSpine (value-term target-body-value ⟨ ∀ᶜ d ⟩)
            (name-type-app-frame B X refl refl ▻ⁱ spine)
          —→[ keep ]⟨ lift-instantiation-spine-keep
            (pure-step (β-∀ target-body-value refl)) spine ⟩
            applyInstantiationSpine (value-term target-body-value)
              (all-child-spine {d = d} spine)
          —↠[ χsᴿ ]⟨ reduction ⟩
            W′ ∎[]) ,
          value ,
          evolutions-step-right refl evolution-keep evolution ,
          final

    name-spine-catchup-acc {γ = γ} {B = B} {X = X} {q = q}
        (inst-view-all view-body-value)
        (CTI.cast⊑cast² c (∀ᶜ d) prem p)
        (source-value 《 source-inert 》)
        (target-body-value 《 all 》) spine
        {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc {c = c} {q = q}
          prem source-inert source-value target-body-value
          (all-child-spine {d = d} spine)
          {spine-names = all-child-spine-names {γ = γ} {d = d} names}
          (smaller (inj₁ (all-primary-decreases-at
            target-body-value d X spine)))
    name-spine-catchup-acc {B = B} {X = X} {q = q}
        (inst-view-all view-body-value)
        (CTI.cast⊑cast² c (∀ᶜ d) prem p)
        (source-value 《 source-inert 》)
        (target-body-value 《 all 》) spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ , W′ , γ′ , r ,
          (applyInstantiationSpine (value-term target-body-value ⟨ ∀ᶜ d ⟩)
            (name-type-app-frame B X refl refl ▻ⁱ spine)
          —→[ keep ]⟨ lift-instantiation-spine-keep
            (pure-step (β-∀ target-body-value refl)) spine ⟩
            applyInstantiationSpine (value-term target-body-value)
              (all-child-spine {d = d} spine)
          —↠[ χsᴿ ]⟨ reduction ⟩
            W′ ∎[]) ,
          value ,
          evolutions-step-right refl evolution-keep evolution ,
          final

    -- A generated universal cast exposes an arbitrary target value, so the
    -- recursive call changes to the general value/spine phase.
    name-spine-catchup-acc {γ = γ} {B = B} {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p)
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine {spine-names = names} (acc smaller)
        with value-spine-catchup-acc
          (transport-target-bind
            (target-only-name-fresh {γ = γ}
              (name-frame-target-only {γ = γ} names))
            refl prem)
          source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (gen-child-spine {X = X} {c = d} spine)
          {spine-names = gen-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (inj₁
            (gen-primary-decreases target-body-value safe′ spine)))
    name-spine-catchup-acc {γ = γ} {B = B} {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p)
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine {spine-names = names} (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , bind (＇ X) ∷ χsᴿ , W′ , γ′ , r ,
          (applyInstantiationSpine
            (value-term target-body-value ⟨ (gen d) D≠★ ⟩)
            (name-type-app-frame B X refl refl ▻ⁱ spine)
          —→[ bind (＇ X) ]⟨ lift-instantiation-spine-bind
            (β-gen target-body-value D≠★ safe′) spine ⟩
            applyInstantiationSpine
              (⇑ᵗᵐ (value-term target-body-value) ⟨ d ⟩
                ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
              (mapInstantiationSpine (bind (＇ X)) spine)
          —↠[ χsᴿ ]⟨ reduction ⟩
            W′ ∎[]) ,
          value ,
          evolutions-step-right refl
            (evolution-bind-right
              (target-only-name-fresh {γ = γ}
                (name-frame-target-only {γ = γ} names))
              refl)
            evolution ,
          final

    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.cast⊑cast² c ((gen d) D≠★) prem p)
        (source-value 《 source-inert 》)
        (target-body-value 《 genᵥ D≠★ safe′ 》) spine
        {spine-names = names} (acc smaller)
        with value-spine-catchup-acc
          {q = {! post-allocation paired-gen source imprecision !}}
          {! transport the paired gen premise through target allocation !}
          source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (gen-child-spine {X = X} {c = d} spine)
          {spine-names = gen-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (inj₁
            (gen-primary-decreases target-body-value safe′ spine)))
    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.cast⊑cast² c ((gen d) D≠★) prem p)
        (source-value 《 source-inert 》)
        (target-body-value 《 genᵥ D≠★ safe′ 》) spine (acc smaller)
      | child =
        {! prepend target gen beta-inst and replay the source inert cast !}

    -- Universal conversions remain in the name phase.  Rebase branches recurse
    -- in their premise world; gamma itself carries the open-frame balance.
    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        source-value (target-body-value ↑ all) spine
        {spine-names = names} (acc smaller)
        with value-spine-catchup-acc
          {! transport the reveal premise through target allocation !}
          source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        source-value (target-body-value ↑ all) spine (acc smaller)
      | child =
        {! prepend the target reveal beta-inst reduction !}

    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.reveal⊑reveal² source-typing target-typing positions aligned
          represented prem p)
        (source-value ↑ all) (target-body-value ↑ all)
        spine {spine-names = names} (acc smaller)
        with value-spine-catchup-acc
          {q = {! post-allocation paired-reveal source imprecision !}}
          {! transport the paired reveal premise through target allocation !}
          source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.reveal⊑reveal² source-typing target-typing positions aligned
          represented prem p)
        (source-value ↑ all) (target-body-value ↑ all)
        spine (acc smaller)
      | child =
        {! prepend target reveal beta-inst and replay the source reveal !}

    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        source-value (target-body-value ↑ all) spine
        {spine-names = names} (acc smaller)
        with value-spine-catchup-acc
          {! transport the reveal-rebase premise through target allocation !}
          source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        source-value (target-body-value ↑ all) spine (acc smaller)
      | child =
        {! prepend target reveal beta-inst and close its rebase world !}

    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        source-value (target-body-value ↓ all) spine
        {spine-names = names} (acc smaller)
        with value-spine-catchup-acc
          {! transport the conceal premise through target allocation !}
          source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        source-value (target-body-value ↓ all) spine (acc smaller)
      | child =
        {! prepend the target conceal beta-inst reduction !}

    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.conceal⊑conceal² source-typing target-typing positions aligned
          represented prem p)
        (source-value ↓ all) (target-body-value ↓ all)
        spine {spine-names = names} (acc smaller)
        with value-spine-catchup-acc
          {q = {! post-allocation paired-conceal source imprecision !}}
          {! transport the paired conceal premise through target allocation !}
          source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.conceal⊑conceal² source-typing target-typing positions aligned
          represented prem p)
        (source-value ↓ all) (target-body-value ↓ all)
        spine (acc smaller)
      | child =
        {! prepend target conceal beta-inst and replay the source conceal !}

    name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        source-value (target-body-value ↓ all) spine
        {spine-names = names} (acc smaller)
        with value-spine-catchup-acc
          {! transport the conceal-rebase premise through target allocation !}
          source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    name-spine-catchup-acc {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        source-value (target-body-value ↓ all) spine (acc smaller)
      | child =
        {! close the gamma-carried frame after target conceal !}

    paired-value-spine-catchup-acc : ∀ {Δᴸ Δᴿ : TyCtx}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {γ : ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , []ᵗ ⟩}
        {V : Term Δᴸ} {V′ : Term Δᴿ}
        {C A : Ty Δᴸ} {B E : Ty Δᴿ}
        {ν : Env∼ Δᴸ} {c : ν ⊢ C ∼ A}
        {p : C ⊑ᵀ⟨ γ ⟩ B} {q : A ⊑ᵀ⟨ γ ⟩ E}
      → (rel : γ ⊢² V ⊑ V′ ∶ p)
      → Inert c
      → (vV : Value V)
      → (vV′ : Value V′)
      → (spine : InstantiationSpine B E)
      → {spine-names : SpineNamesTargetOnlyᶜ γ spine}
      → Acc _<measure_ (pending-measure vV′ spine rel)
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ W′ ∈ Term Δᴿ′ ]
        Σ[ γ′ ∈
          ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ
          ⟨ Δᴿ′ , Σᴿ′ , []ᵗ ⟩ ]
        Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ E ]
          (applyInstantiationSpine V′ spine —↠[ χsᴿ ] W′)
          × Value W′
          × MultiWorldEvolution {W = γ} {W′ = γ′} [] χsᴿ
          × (γ′ ⊢² V ⟨ c ⟩ ⊑ W′ ∶ r)
    paired-value-spine-catchup-acc {Δᴿ = Δᴿ} {Σᴿ = Σᴿ}
        {γ = γ} {V′ = V′} {c = c} {q = q}
        rel inert source-value target-value []ⁱ
        {spine-names = names-[]} access =
      Δᴿ , Σᴿ , [] , V′ , γ , q ,
        (V′ ∎[]) , target-value , evolutions-refl ,
        CTI.cast⊑² c rel q

    paired-value-spine-catchup-acc rel inert source-value target-value
        (type-transport-frame eq ▻ⁱ spine)
        {spine-names = names-type-transport names} (acc smaller)
        with paired-value-spine-catchup-acc
          (transport-target-type eq rel) inert source-value target-value spine
          {spine-names = names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl , inj₁ (n<1+n _))))))
    paired-value-spine-catchup-acc rel inert source-value target-value
        (type-transport-frame eq ▻ⁱ spine) (acc smaller)
      | child =
        child

    paired-value-spine-catchup-acc rel inert source-value target-value
        (name-type-app-frame B X refl refl ▻ⁱ spine)
        {spine-names = names} (acc smaller)
        with paired-name-spine-catchup-acc
          (progress-all-view
            (Prog.canonical-∀ target-value (CTIT.target-typing rel)))
          rel inert source-value target-value spine {spine-names = names}
          (smaller
            (inj₂ (refl ,
              inj₂ (refl ,
                inj₂ (refl ,
                  inj₂ (refl , n<1+n _))))))
    paired-value-spine-catchup-acc rel inert source-value target-value
        (name-type-app-frame B X refl refl ▻ⁱ spine) (acc smaller)
      | child = child

    paired-value-spine-catchup-acc rel inert source-value target-value
        (cast-frame c′ ▻ⁱ spine)
        {spine-names = names-cast names} access =
      {! normalize the paired pending target cast, then continue with the
         exact evolved relation, value, and strictly smaller tail state !}

    paired-value-spine-catchup-acc rel inert source-value target-value
        (reveal-frame d ▻ⁱ spine)
        {spine-names = names-reveal names} access =
      {! normalize the paired pending target reveal, then continue with the
         exact evolved relation, value, and strictly smaller tail state !}

    paired-value-spine-catchup-acc rel inert source-value target-value
        (conceal-frame d ▻ⁱ spine)
        {spine-names = names-conceal names} access =
      {! normalize the paired pending target conceal, then continue with the
         exact evolved relation, value, and strictly smaller tail state !}

    paired-name-spine-catchup-acc : ∀ {Δᴸ Δᴿ : TyCtx}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {γ : ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , []ᵗ ⟩}
        {V : Term Δᴸ} {V′ : Term Δᴿ}
        {C A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
        {X : TyVar Δᴿ} {ν : Env∼ Δᴸ} {c : ν ⊢ C ∼ A}
        {p : C ⊑ᵀ⟨ γ ⟩ `∀ B} {q : A ⊑ᵀ⟨ γ ⟩ E}
      → InstantiationAllView B V′
      → (rel : γ ⊢² V ⊑ V′ ∶ p)
      → Inert c
      → (vV : Value V)
      → (vV′ : Value V′)
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → {spine-names : SpineNamesTargetOnlyᶜ γ
          (name-type-app-frame B X refl refl ▻ⁱ spine)}
      → Acc _<measure_
          (name-measure vV′
            (name-type-app-frame B X refl refl ▻ⁱ spine) rel)
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ W′ ∈ Term Δᴿ′ ]
        Σ[ γ′ ∈
          ⟨ Δᴸ , Σᴸ , []ᵗ ⟩ ⊑ᶜ
          ⟨ Δᴿ′ , Σᴿ′ , []ᵗ ⟩ ]
        Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ E ]
          (applyInstantiationSpine V′
            (name-type-app-frame B X refl refl ▻ⁱ spine)
              —↠[ χsᴿ ] W′)
          × Value W′
          × MultiWorldEvolution {W = γ} {W′ = γ′} [] χsᴿ
          × (γ′ ⊢² V ⟨ c ⟩ ⊑ W′ ∶ r)
    paired-name-spine-catchup-acc {V′ = ` x} () rel inert source-value
        target-value spine access
    paired-name-spine-catchup-acc {V′ = ƛ M′} () rel inert source-value
        target-value spine access
    paired-name-spine-catchup-acc {V′ = L′ · M′} () rel inert
        source-value target-value spine access
    paired-name-spine-catchup-acc {V′ = M′ ⦂∀ C [ D ]} () rel inert
        source-value target-value spine access
    paired-name-spine-catchup-acc {V′ = $ κ} () rel inert source-value
        target-value spine access
    paired-name-spine-catchup-acc {V′ = L′ ⊕[ op ] M′} () rel inert
        source-value target-value spine access
    paired-name-spine-catchup-acc {V′ = blame} () rel inert source-value
        target-value spine access

    -- Outer injection cast.
    -- Generic source wrappers descend structurally while retaining an exact
    -- child cast obligation.  The returned child is replayed under the source
    -- wrapper only after the recursive catch-up is available.
    paired-name-spine-catchup-acc view
        (CTI.Λ⊑² Anv zero∈A body-value target-typing prem q)
        inj (Λ outer-value) target-value spine access =
      {! derive the constructor-specific child cast through source Lambda,
         recurse structurally, then replay Lambda and the outer cast !}

    paired-name-spine-catchup-acc view (CTI.cast⊑² c₀ prem q)
        inj (source-value 《 source-inert 》) target-value spine access =
      {! compose the constructor-specific outer cast with the nested source
         cast, recurse structurally, then replay both casts !}

    paired-name-spine-catchup-acc view
        (CTI.reveal⊑-identity c⊢ position prem q)
        inj (source-value ↑ all) target-value spine access =
      {! move the constructor-specific outer cast through the source identity
         reveal, recurse structurally, then replay reveal and cast !}

    paired-name-spine-catchup-acc view
        (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q)
        inj (source-value ↑ all) target-value spine access =
      {! move the constructor-specific outer cast through the source-only
         reveal, recurse structurally, then replay reveal and cast !}

    paired-name-spine-catchup-acc view
        (CTI.conceal⊑-identity c⊢ position prem q)
        inj (source-value ↓ all) target-value spine access =
      {! move the constructor-specific outer cast through the source identity
         conceal, recurse structurally, then replay conceal and cast !}

    paired-name-spine-catchup-acc view
        (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
        inj (source-value ↓ all) target-value spine access =
      {! move the constructor-specific outer cast through the source-only
         conceal, recurse structurally, then replay conceal and cast !}

    paired-name-spine-catchup-acc {B = B} {E = E} {X = X}
        (inst-view-Λ target-body-value)
        (CTI.Λ⊑Λ² source-body-value target-body-value′ prem p)
        inj (Λ source-outer-value) (Λ target-outer-value)
        spine access =
      {! expose the paired beta-Lambda residual consistency and value in the
         extended worlds, then recurse at its exact smaller state !}

    paired-name-spine-catchup-acc {γ = γ} {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p) outer-inert@inj source-value
        (target-body-value 《 all 》) spine
        {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          prem outer-inert source-value target-body-value
          (all-child-spine {d = d} spine)
          {spine-names = all-child-spine-names {γ = γ} {d = d} names}
          (smaller (inj₁ (all-primary-decreases-at
            target-body-value d X spine)))
    paired-name-spine-catchup-acc {γ = γ} {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p) inj source-value
        (target-body-value 《 all 》) spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ , W′ , γ′ , r ,
          (applyInstantiationSpine (value-term target-body-value ⟨ ∀ᶜ d ⟩)
            (name-type-app-frame B X refl refl ▻ⁱ spine)
          —→[ keep ]⟨ lift-instantiation-spine-keep
            (pure-step (β-∀ target-body-value refl)) spine ⟩
            applyInstantiationSpine (value-term target-body-value)
              (all-child-spine {d = d} spine)
          —↠[ χsᴿ ]⟨ reduction ⟩
            W′ ∎[]) ,
          value ,
          evolutions-step-right refl evolution-keep evolution ,
          final

    paired-name-spine-catchup-acc {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.cast⊑cast² c₀ (∀ᶜ d) prem p) inj
        (source-value 《 source-inert 》)
        (target-body-value 《 all 》) spine access =
      {! compose the constructor-specific outer cast with the paired source
         cast, move the target all cast into the spine, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p) outer-inert@inj
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation gen final imprecision !}}
          {! transport paired gen premise through target allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (gen-child-spine {X = X} {c = d} spine)
          {spine-names = gen-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (inj₁
            (gen-primary-decreases target-body-value safe′ spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p) inj
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine (acc smaller)
      | child =
        {! prepend paired target gen beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.cast⊑cast² c₀ ((gen d) D≠★) prem p) inj
        (source-value 《 source-inert 》)
        (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine access =
      {! transport the paired gen premise through allocation, compose the
         constructor-specific source casts, and recurse at smaller mass !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        outer-inert@inj source-value (target-body-value ↑ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation reveal final imprecision !}}
          {! transport paired reveal premise through target allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        inj source-value (target-body-value ↑ all)
        spine (acc smaller)
      | child =
        {! prepend paired target reveal beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.reveal⊑reveal² source-typing target-typing positions aligned
          represented prem p) inj (source-value ↑ all)
        (target-body-value ↑ all) spine access =
      {! transport the paired reveal premise through allocation, move the
         constructor-specific source cast through reveal, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        outer-inert@inj source-value (target-body-value ↑ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired reveal-rebase child final imprecision !}}
          {! transport paired reveal-rebase premise through allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        inj source-value (target-body-value ↑ all)
        spine (acc smaller)
      | child =
        {! prepend paired reveal and close its rebase world !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        outer-inert@inj source-value (target-body-value ↓ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation conceal final imprecision !}}
          {! transport paired conceal premise through target allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        inj source-value (target-body-value ↓ all)
        spine (acc smaller)
      | child =
        {! prepend paired target conceal beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.conceal⊑conceal² source-typing target-typing positions aligned
          represented prem p) inj (source-value ↓ all)
        (target-body-value ↓ all) spine access =
      {! transport the paired conceal premise through allocation, move the
         constructor-specific source cast through conceal, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        outer-inert@inj source-value (target-body-value ↓ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired conceal-rebase child final imprecision !}}
          {! transport paired conceal-rebase premise through allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        inj source-value (target-body-value ↓ all)
        spine (acc smaller)
      | child =
        {! close paired gamma-carried frame after target conceal !}


    -- Outer function cast.
    -- Generic source wrappers descend structurally while retaining an exact
    -- child cast obligation.  The returned child is replayed under the source
    -- wrapper only after the recursive catch-up is available.
    paired-name-spine-catchup-acc view (CTI.cast⊑² c₀ prem q)
        outer-inert@fun (source-value 《 source-inert 》) target-value
        spine access =
      {! compose the constructor-specific outer cast with the nested source
         cast, recurse structurally, then replay both casts !}

    paired-name-spine-catchup-acc {γ = γ} {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p) outer-inert@fun source-value
        (target-body-value 《 all 》) spine
        {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          prem outer-inert source-value target-body-value
          (all-child-spine {d = d} spine)
          {spine-names = all-child-spine-names {γ = γ} {d = d} names}
          (smaller (inj₁ (all-primary-decreases-at
            target-body-value d X spine)))
    paired-name-spine-catchup-acc {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p) outer-inert@fun source-value
        (target-body-value 《 all 》) spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ , W′ , γ′ , r ,
          (applyInstantiationSpine (value-term target-body-value ⟨ ∀ᶜ d ⟩)
            (name-type-app-frame B X refl refl ▻ⁱ spine)
          —→[ keep ]⟨ lift-instantiation-spine-keep
            (pure-step (β-∀ target-body-value refl)) spine ⟩
            applyInstantiationSpine (value-term target-body-value)
              (all-child-spine {d = d} spine)
          —↠[ χsᴿ ]⟨ reduction ⟩
            W′ ∎[]) ,
          value ,
          evolutions-step-right refl evolution-keep evolution ,
          final

    paired-name-spine-catchup-acc {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.cast⊑cast² c₀ (∀ᶜ d) prem p) outer-inert@fun
        (source-value 《 source-inert 》)
        (target-body-value 《 all 》) spine access =
      {! compose the constructor-specific outer cast with the paired source
         cast, move the target all cast into the spine, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p) outer-inert@fun
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation gen final imprecision !}}
          {! transport paired gen premise through target allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (gen-child-spine {X = X} {c = d} spine)
          {spine-names = gen-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (inj₁
            (gen-primary-decreases target-body-value safe′ spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p) outer-inert@fun
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine (acc smaller)
      | child =
        {! prepend paired target gen beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.cast⊑cast² c₀ ((gen d) D≠★) prem p) outer-inert@fun
        (source-value 《 source-inert 》)
        (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine access =
      {! transport the paired gen premise through allocation, compose the
         constructor-specific source casts, and recurse at smaller mass !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        outer-inert@fun source-value (target-body-value ↑ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation reveal final imprecision !}}
          {! transport paired reveal premise through target allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        outer-inert@fun source-value (target-body-value ↑ all)
        spine (acc smaller)
      | child =
        {! prepend paired target reveal beta-inst reduction !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        outer-inert@fun source-value (target-body-value ↑ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired reveal-rebase child final imprecision !}}
          {! transport paired reveal-rebase premise through allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        outer-inert@fun source-value (target-body-value ↑ all)
        spine (acc smaller)
      | child =
        {! prepend paired reveal and close its rebase world !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        outer-inert@fun source-value (target-body-value ↓ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation conceal final imprecision !}}
          {! transport paired conceal premise through target allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        outer-inert@fun source-value (target-body-value ↓ all)
        spine (acc smaller)
      | child =
        {! prepend paired target conceal beta-inst reduction !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        outer-inert@fun source-value (target-body-value ↓ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired conceal-rebase child final imprecision !}}
          {! transport paired conceal-rebase premise through allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        outer-inert@fun source-value (target-body-value ↓ all)
        spine (acc smaller)
      | child =
        {! close paired gamma-carried frame after target conceal !}


    -- Outer universal cast.
    -- Generic source wrappers descend structurally while retaining an exact
    -- child cast obligation.  The returned child is replayed under the source
    -- wrapper only after the recursive catch-up is available.
    paired-name-spine-catchup-acc view
        (CTI.Λ⊑² Anv zero∈A body-value target-typing prem q)
        outer-inert@all (Λ outer-value) target-value spine access =
      {! derive the constructor-specific child cast through source Lambda,
         recurse structurally, then replay Lambda and the outer cast !}

    paired-name-spine-catchup-acc view (CTI.cast⊑² c₀ prem q)
        outer-inert@all (source-value 《 source-inert 》) target-value
        spine access =
      {! compose the constructor-specific outer cast with the nested source
         cast, recurse structurally, then replay both casts !}

    paired-name-spine-catchup-acc view
        (CTI.reveal⊑-identity c⊢ position prem q)
        outer-inert@all (source-value ↑ all) target-value spine access =
      {! move the constructor-specific outer cast through the source identity
         reveal, recurse structurally, then replay reveal and cast !}

    paired-name-spine-catchup-acc view
        (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q)
        outer-inert@all (source-value ↑ all) target-value spine access =
      {! move the constructor-specific outer cast through the source-only
         reveal, recurse structurally, then replay reveal and cast !}

    paired-name-spine-catchup-acc view
        (CTI.conceal⊑-identity c⊢ position prem q)
        outer-inert@all (source-value ↓ all) target-value spine access =
      {! move the constructor-specific outer cast through the source identity
         conceal, recurse structurally, then replay conceal and cast !}

    paired-name-spine-catchup-acc view
        (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
        outer-inert@all (source-value ↓ all) target-value spine access =
      {! move the constructor-specific outer cast through the source-only
         conceal, recurse structurally, then replay conceal and cast !}

    paired-name-spine-catchup-acc {B = B} {E = E} {X = X}
        (inst-view-Λ target-body-value)
        (CTI.Λ⊑Λ² source-body-value target-body-value′ prem p)
        outer-inert@all (Λ source-outer-value) (Λ target-outer-value)
        spine access =
      {! expose the paired beta-Lambda residual consistency and value in the
         extended worlds, then recurse at its exact smaller state !}

    paired-name-spine-catchup-acc {γ = γ} {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p) outer-inert@all source-value
        (target-body-value 《 all 》) spine
        {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          prem outer-inert source-value target-body-value
          (all-child-spine {d = d} spine)
          {spine-names = all-child-spine-names {γ = γ} {d = d} names}
          (smaller (inj₁ (all-primary-decreases-at
            target-body-value d X spine)))
    paired-name-spine-catchup-acc {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p) outer-inert@all source-value
        (target-body-value 《 all 》) spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ , W′ , γ′ , r ,
          (applyInstantiationSpine (value-term target-body-value ⟨ ∀ᶜ d ⟩)
            (name-type-app-frame B X refl refl ▻ⁱ spine)
          —→[ keep ]⟨ lift-instantiation-spine-keep
            (pure-step (β-∀ target-body-value refl)) spine ⟩
            applyInstantiationSpine (value-term target-body-value)
              (all-child-spine {d = d} spine)
          —↠[ χsᴿ ]⟨ reduction ⟩
            W′ ∎[]) ,
          value ,
          evolutions-step-right refl evolution-keep evolution ,
          final

    paired-name-spine-catchup-acc {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.cast⊑cast² c₀ (∀ᶜ d) prem p) outer-inert@all
        (source-value 《 source-inert 》)
        (target-body-value 《 all 》) spine access =
      {! compose the constructor-specific outer cast with the paired source
         cast, move the target all cast into the spine, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p) outer-inert@all
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation gen final imprecision !}}
          {! transport paired gen premise through target allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (gen-child-spine {X = X} {c = d} spine)
          {spine-names = gen-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (inj₁
            (gen-primary-decreases target-body-value safe′ spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p) outer-inert@all
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine (acc smaller)
      | child =
        {! prepend paired target gen beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.cast⊑cast² c₀ ((gen d) D≠★) prem p) outer-inert@all
        (source-value 《 source-inert 》)
        (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine access =
      {! transport the paired gen premise through allocation, compose the
         constructor-specific source casts, and recurse at smaller mass !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        outer-inert@all source-value (target-body-value ↑ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation reveal final imprecision !}}
          {! transport paired reveal premise through target allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        outer-inert@all source-value (target-body-value ↑ all)
        spine (acc smaller)
      | child =
        {! prepend paired target reveal beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.reveal⊑reveal² source-typing target-typing positions aligned
          represented prem p) outer-inert@all (source-value ↑ all)
        (target-body-value ↑ all) spine access =
      {! transport the paired reveal premise through allocation, move the
         constructor-specific source cast through reveal, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        outer-inert@all source-value (target-body-value ↑ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired reveal-rebase child final imprecision !}}
          {! transport paired reveal-rebase premise through allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        outer-inert@all source-value (target-body-value ↑ all)
        spine (acc smaller)
      | child =
        {! prepend paired reveal and close its rebase world !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        outer-inert@all source-value (target-body-value ↓ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation conceal final imprecision !}}
          {! transport paired conceal premise through target allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        outer-inert@all source-value (target-body-value ↓ all)
        spine (acc smaller)
      | child =
        {! prepend paired target conceal beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.conceal⊑conceal² source-typing target-typing positions aligned
          represented prem p) outer-inert@all (source-value ↓ all)
        (target-body-value ↓ all) spine access =
      {! transport the paired conceal premise through allocation, move the
         constructor-specific source cast through conceal, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        outer-inert@all source-value (target-body-value ↓ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired conceal-rebase child final imprecision !}}
          {! transport paired conceal-rebase premise through allocation !}
          outer-inert source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        outer-inert@all source-value (target-body-value ↓ all)
        spine (acc smaller)
      | child =
        {! close paired gamma-carried frame after target conceal !}


    -- Outer generated universal cast.
    -- Generic source wrappers descend structurally while retaining an exact
    -- child cast obligation.  The returned child is replayed under the source
    -- wrapper only after the recursive catch-up is available.
    paired-name-spine-catchup-acc view
        (CTI.Λ⊑² Anv zero∈A body-value target-typing prem q)
        outer@(genᵥ A≠★ safeᵒ) (Λ outer-value) target-value spine access =
      {! derive the constructor-specific child cast through source Lambda,
         recurse structurally, then replay Lambda and the outer cast !}

    paired-name-spine-catchup-acc view (CTI.cast⊑² c₀ prem q)
        outer@(genᵥ A≠★ safeᵒ) (source-value 《 source-inert 》)
        target-value spine access =
      {! compose the constructor-specific outer cast with the nested source
         cast, recurse structurally, then replay both casts !}

    paired-name-spine-catchup-acc view
        (CTI.reveal⊑-identity c⊢ position prem q)
        outer@(genᵥ A≠★ safeᵒ) (source-value ↑ all) target-value spine access =
      {! move the constructor-specific outer cast through the source identity
         reveal, recurse structurally, then replay reveal and cast !}

    paired-name-spine-catchup-acc view
        (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q)
        outer@(genᵥ A≠★ safeᵒ) (source-value ↑ all) target-value spine access =
      {! move the constructor-specific outer cast through the source-only
         reveal, recurse structurally, then replay reveal and cast !}

    paired-name-spine-catchup-acc view
        (CTI.conceal⊑-identity c⊢ position prem q)
        outer@(genᵥ A≠★ safeᵒ) (source-value ↓ all) target-value spine access =
      {! move the constructor-specific outer cast through the source identity
         conceal, recurse structurally, then replay conceal and cast !}

    paired-name-spine-catchup-acc view
        (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
        outer@(genᵥ A≠★ safeᵒ) (source-value ↓ all) target-value spine access =
      {! move the constructor-specific outer cast through the source-only
         conceal, recurse structurally, then replay conceal and cast !}

    paired-name-spine-catchup-acc {B = B} {E = E} {X = X}
        (inst-view-Λ target-body-value)
        (CTI.Λ⊑Λ² source-body-value target-body-value′ prem p)
        outer@(genᵥ A≠★ safeᵒ) (Λ source-outer-value) (Λ target-outer-value)
        spine access =
      {! expose the paired beta-Lambda residual consistency and value in the
         extended worlds, then recurse at its exact smaller state !}

    paired-name-spine-catchup-acc {γ = γ} {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p) outer@(genᵥ A≠★ safeᵒ) source-value
        (target-body-value 《 all 》) spine
        {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          prem outer source-value target-body-value
          (all-child-spine {d = d} spine)
          {spine-names = all-child-spine-names {γ = γ} {d = d} names}
          (smaller (inj₁ (all-primary-decreases-at
            target-body-value d X spine)))
    paired-name-spine-catchup-acc {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.⊑cast² (∀ᶜ d) prem p) outer@(genᵥ A≠★ safeᵒ) source-value
        (target-body-value 《 all 》) spine (acc smaller)
      | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
        evolution , final =
        Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ , W′ , γ′ , r ,
          (applyInstantiationSpine (value-term target-body-value ⟨ ∀ᶜ d ⟩)
            (name-type-app-frame B X refl refl ▻ⁱ spine)
          —→[ keep ]⟨ lift-instantiation-spine-keep
            (pure-step (β-∀ target-body-value refl)) spine ⟩
            applyInstantiationSpine (value-term target-body-value)
              (all-child-spine {d = d} spine)
          —↠[ χsᴿ ]⟨ reduction ⟩
            W′ ∎[]) ,
          value ,
          evolutions-step-right refl evolution-keep evolution ,
          final

    paired-name-spine-catchup-acc {B = B} {X = X}
        (inst-view-all view-body-value)
        (CTI.cast⊑cast² c₀ (∀ᶜ d) prem p) outer@(genᵥ A≠★ safeᵒ)
        (source-value 《 source-inert 》)
        (target-body-value 《 all 》) spine access =
      {! compose the constructor-specific outer cast with the paired source
         cast, move the target all cast into the spine, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p) outer@(genᵥ A≠★ safeᵒ)
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation gen final imprecision !}}
          {! transport paired gen premise through target allocation !}
          outer source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (gen-child-spine {X = X} {c = d} spine)
          {spine-names = gen-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (inj₁
            (gen-primary-decreases target-body-value safe′ spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.⊑cast² ((gen d) D≠★) prem p) outer@(genᵥ A≠★ safeᵒ)
        source-value (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine (acc smaller)
      | child =
        {! prepend paired target gen beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-gen view-body-value D≠★ safe)
        (CTI.cast⊑cast² c₀ ((gen d) D≠★) prem p) outer@(genᵥ A≠★ safeᵒ)
        (source-value 《 source-inert 》)
        (target-body-value 《 genᵥ D≠★ safe′ 》)
        spine access =
      {! transport the paired gen premise through allocation, compose the
         constructor-specific source casts, and recurse at smaller mass !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        outer@(genᵥ A≠★ safeᵒ) source-value (target-body-value ↑ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation reveal final imprecision !}}
          {! transport paired reveal premise through target allocation !}
          outer source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-identity target-typing position prem p)
        outer@(genᵥ A≠★ safeᵒ) source-value (target-body-value ↑ all)
        spine (acc smaller)
      | child =
        {! prepend paired target reveal beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.reveal⊑reveal² source-typing target-typing positions aligned
          represented prem p) outer@(genᵥ A≠★ safeᵒ) (source-value ↑ all)
        (target-body-value ↑ all) spine access =
      {! transport the paired reveal premise through allocation, move the
         constructor-specific source cast through reveal, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        outer@(genᵥ A≠★ safeᵒ) source-value (target-body-value ↑ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired reveal-rebase child final imprecision !}}
          {! transport paired reveal-rebase premise through allocation !}
          outer source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (reveal-child-spine {X = X} {c = d} spine)
          {spine-names = reveal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (reveal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-reveal {c = d} view-body-value)
        (CTI.⊑reveal-rebase² target-typing rebase prem p)
        outer@(genᵥ A≠★ safeᵒ) source-value (target-body-value ↑ all)
        spine (acc smaller)
      | child =
        {! prepend paired reveal and close its rebase world !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        outer@(genᵥ A≠★ safeᵒ) source-value (target-body-value ↓ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired post-allocation conceal final imprecision !}}
          {! transport paired conceal premise through target allocation !}
          outer source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-identity target-typing position prem p)
        outer@(genᵥ A≠★ safeᵒ) source-value (target-body-value ↓ all)
        spine (acc smaller)
      | child =
        {! prepend paired target conceal beta-inst reduction !}

    paired-name-spine-catchup-acc {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.conceal⊑conceal² source-typing target-typing positions aligned
          represented prem p) outer@(genᵥ A≠★ safeᵒ) (source-value ↓ all)
        (target-body-value ↓ all) spine access =
      {! transport the paired conceal premise through allocation, move the
         constructor-specific source cast through conceal, and recurse !}

    paired-name-spine-catchup-acc {γ = γ} {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        outer@(genᵥ A≠★ safeᵒ) source-value (target-body-value ↓ all)
        spine {spine-names = names} (acc smaller)
        with paired-value-spine-catchup-acc
          {q = {! paired conceal-rebase child final imprecision !}}
          {! transport paired conceal-rebase premise through allocation !}
          outer source-value
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-body-value)
          (conceal-child-spine {X = X} {c = d} spine)
          {spine-names = conceal-child-spine-names {γ = γ} {c = d}
            (name-frame-target-only {γ = γ} names)
            (name-frame-tail-names {γ = γ} names)}
          (smaller (rank-decrease→measure
            (pending-cast-mass-bind (＇ X) target-body-value spine)
            (conceal-rank-decreases {X = X} {c = d}
              target-body-value spine)))
    paired-name-spine-catchup-acc {X = X}
        (inst-view-conceal {c = d} view-body-value)
        (CTI.⊑conceal-rebase² target-typing rebase prem p)
        outer@(genᵥ A≠★ safeᵒ) source-value (target-body-value ↓ all)
        spine (acc smaller)
      | child =
        {! close paired gamma-carried frame after target conceal !}

  more-precise-target-instantiation-value-catchup :
    MorePreciseTargetInstantiationValueCatchupᵀ
  more-precise-target-instantiation-value-catchup
      {γ = γ} {V′ = V′} {B = B} {B′ = B′} {c′ = c′}
      {B′≠★ = B′≠★} {q = q}
      no-rebase rel source-value target-value
      with name-spine-catchup-acc
      {γ = γ ▻ᶜ bind-right-changeᶜ ★ (inj₁ refl) refl}
      {X = Fin.zero}
      {q = evolution-⊑ᵀ
        (evolution-bind-right {B = ★} {W = γ} (inj₁ refl) refl) q}
      (progress-all-view
        (Prog.canonical-∀
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-value)
          (CTIT.target-typing
            (transport-target-bind (inj₁ refl) refl rel))))
      (transport-target-bind (inj₁ refl) refl rel)
      source-value
      (renameᵗᵐ-preserves-Value wk↪ᵗ target-value)
      (inst-residual-tail {B = B} {B′ = B′} {c = c′})
      {spine-names = names-name-type-app
        {γ = γ ▻ᶜ bind-right-changeᶜ ★ (inj₁ refl) refl}
        (right-bind-new-target-only {γ = γ} {B = ★}
          {fresh = inj₁ refl})
        (inst-residual-tail-names
          {γ = γ ▻ᶜ bind-right-changeᶜ ★ (inj₁ refl) refl}
          {c = c′})}
      (measure-well-founded _)
  more-precise-target-instantiation-value-catchup
      {γ = γ} {V′ = V′} {B = B} {B′ = B′} {c′ = c′}
      {B′≠★ = B′≠★} {q = q}
      no-rebase rel source-value target-value
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
      evolution , final =
      Δᴿ′ , Σᴿ′ , bind ★ ∷ χsᴿ , W′ , γ′ , r ,
        (V′ ⟨ (inst c′) B′≠★ ⟩
        —→[ bind ★ ]⟨ β-inst target-value B′≠★ ⟩
          applyInstantiationSpine (⇑ᵗᵐ V′)
            (name-type-app-frame (applyBody (bind ★) B) Fin.zero
              refl refl ▻ⁱ
            inst-residual-tail {B = B} {B′ = B′} {c = c′})
        —↠[ χsᴿ ]⟨ reduction ⟩
          W′ ∎[]) ,
        value ,
        evolutions-step-right refl
          (evolution-bind-right
            {B = ★} {W = γ} (inj₁ refl) refl)
          evolution ,
        final

  -- The paired root cannot be reduced through a target-only intermediate:
  -- the required post-source-cast/pre-instantiation type edge is false in
  -- general.  Its whole-branch induction shares the private measure and will
  -- retain the source inert cast until the final CTI evidence.
  more-precise-paired-target-instantiation-value-catchup :
    MorePrecisePairedTargetInstantiationValueCatchupᵀ
  more-precise-paired-target-instantiation-value-catchup
      {γ = γ} {V′ = V′} {B = B} {B′ = B′}
      {cᴸ = cᴸ} {cᴿ = cᴿ}
      {B′≠★ = B′≠★} {q = q}
      no-rebase rel inert source-value target-value
      with paired-name-spine-catchup-acc
      {γ = γ ▻ᶜ bind-right-changeᶜ ★ (inj₁ refl) refl}
      {X = Fin.zero}
      {c = cᴸ}
      {q = evolution-⊑ᵀ
        (evolution-bind-right {B = ★} {W = γ} (inj₁ refl) refl) q}
      (progress-all-view
        (Prog.canonical-∀
          (renameᵗᵐ-preserves-Value wk↪ᵗ target-value)
          (CTIT.target-typing
            (transport-target-bind (inj₁ refl) refl rel))))
      (transport-target-bind (inj₁ refl) refl rel)
      inert source-value
      (renameᵗᵐ-preserves-Value wk↪ᵗ target-value)
      (inst-residual-tail {B = B} {B′ = B′} {c = cᴿ})
      {spine-names = names-name-type-app
        {γ = γ ▻ᶜ bind-right-changeᶜ ★ (inj₁ refl) refl}
        (right-bind-new-target-only {γ = γ} {B = ★}
          {fresh = inj₁ refl})
        (inst-residual-tail-names
          {γ = γ ▻ᶜ bind-right-changeᶜ ★ (inj₁ refl) refl}
          {c = cᴿ})}
      (measure-well-founded _)
  more-precise-paired-target-instantiation-value-catchup
      {γ = γ} {V′ = V′} {B = B} {B′ = B′}
      {cᴸ = cᴸ} {cᴿ = cᴿ}
      {B′≠★ = B′≠★} {q = q}
      no-rebase rel inert source-value target-value
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , value ,
      evolution , final =
      Δᴿ′ , Σᴿ′ , bind ★ ∷ χsᴿ , W′ , γ′ , r ,
        (V′ ⟨ (inst cᴿ) B′≠★ ⟩
        —→[ bind ★ ]⟨ β-inst target-value B′≠★ ⟩
          applyInstantiationSpine (⇑ᵗᵐ V′)
            (name-type-app-frame (applyBody (bind ★) B) Fin.zero
              refl refl ▻ⁱ
            inst-residual-tail {B = B} {B′ = B′} {c = cᴿ})
        —↠[ χsᴿ ]⟨ reduction ⟩
          W′ ∎[]) ,
        value ,
        evolutions-step-right refl
          (evolution-bind-right
            {B = ★} {W = γ} (inj₁ refl) refl)
          evolution ,
        final

  more-precise-target-cast-value-catchup :
    MorePreciseTargetCastValueCatchupᵀ

  -- Source-only inert casts are replayed after the target catch-up.
  more-precise-target-cast-value-catchup {p = q}
      no-rebase (CTI.cast⊑² c prem q) (vV 《 inert 》) vV′
      with more-precise-target-cast-value-catchup
        no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase (CTI.cast⊑² c prem q) (vV 《 inert 》) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.cast⊑² c final (multi-⊑ᵀ evolution q)

  -- A target-only evolution below Λ is closed by the dedicated scope lemma.
  more-precise-target-cast-value-catchup {p = q}
      no-rebase (CTI.Λ⊑² Anv zero∈A body-value V′⊢ prem q)
      (Λ outer-value) vV′
      with more-precise-target-cast-value-catchup
        (renameOpenFrames-empty no-rebase) prem body-value vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase (CTI.Λ⊑² Anv zero∈A body-value V′⊢ prem q)
      (Λ outer-value) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γᵇ , r , reduction , vW′ , evolution , final
      with close-source-Λ no-rebase Anv zero∈A body-value evolution final q
  more-precise-target-cast-value-catchup {p = q}
      no-rebase (CTI.Λ⊑² Anv zero∈A body-value V′⊢ prem q)
      (Λ outer-value) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γᵇ , r , reduction , vW′ , evolution , final
    | γ′ , s , outer-evolution , outer-final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , s ,
        reduction , vW′ , outer-evolution , outer-final

  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.reveal⊑-identity c⊢ position prem q) (vV ↑ fun) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.reveal⊑-identity c⊢ position prem q) (vV ↑ fun) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.reveal⊑-identity
          (multi-source-reveal evolution c⊢)
          (trans (multi-source-reveal-position evolution c⊢) position)
          final (multi-⊑ᵀ evolution q)
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↑ fun) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↑ fun) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.reveal⊑-only²
          (multi-source-reveal evolution c⊢)
          (λ eq → position
            (trans (sym (multi-source-reveal-position evolution c⊢)) eq))
          (multi-source-mark evolution mark)
          (multi-source-disaligned evolution no-target)
          (subst≡ (λ B → _ ⊑ᵀ⟨ γ′ ⟩ B) (applyTys-★ χsᴿ)
            (multi-⊑ᵀ evolution represented))
          final (multi-⊑ᵀ evolution q)

  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.reveal⊑-identity c⊢ position prem q) (vV ↑ all) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.reveal⊑-identity c⊢ position prem q) (vV ↑ all) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.reveal⊑-identity
          (multi-source-reveal evolution c⊢)
          (trans (multi-source-reveal-position evolution c⊢) position)
          final (multi-⊑ᵀ evolution q)
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↑ all) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.reveal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↑ all) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.reveal⊑-only²
          (multi-source-reveal evolution c⊢)
          (λ eq → position
            (trans (sym (multi-source-reveal-position evolution c⊢)) eq))
          (multi-source-mark evolution mark)
          (multi-source-disaligned evolution no-target)
          (subst≡ (λ B → _ ⊑ᵀ⟨ γ′ ⟩ B) (applyTys-★ χsᴿ)
            (multi-⊑ᵀ evolution represented))
          final (multi-⊑ᵀ evolution q)

  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-identity c⊢ position prem q) (vV ↓ CT.seal) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-identity c⊢ position prem q) (vV ↓ CT.seal) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.conceal⊑-identity
          (multi-source-conceal evolution c⊢)
          (trans (multi-source-conceal-position evolution c⊢) position)
          final (multi-⊑ᵀ evolution q)
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↓ CT.seal) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↓ CT.seal) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.conceal⊑-only²
          (multi-source-conceal evolution c⊢)
          (λ eq → position
            (trans (sym (multi-source-conceal-position evolution c⊢)) eq))
          (multi-source-mark evolution mark)
          (multi-source-disaligned evolution no-target)
          (subst≡ (λ B → _ ⊑ᵀ⟨ γ′ ⟩ B) (applyTys-★ χsᴿ)
            (multi-⊑ᵀ evolution represented))
          final (multi-⊑ᵀ evolution q)

  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-identity c⊢ position prem q) (vV ↓ fun) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-identity c⊢ position prem q) (vV ↓ fun) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.conceal⊑-identity
          (multi-source-conceal evolution c⊢)
          (trans (multi-source-conceal-position evolution c⊢) position)
          final (multi-⊑ᵀ evolution q)
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↓ fun) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↓ fun) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.conceal⊑-only²
          (multi-source-conceal evolution c⊢)
          (λ eq → position
            (trans (sym (multi-source-conceal-position evolution c⊢)) eq))
          (multi-source-mark evolution mark)
          (multi-source-disaligned evolution no-target)
          (subst≡ (λ B → _ ⊑ᵀ⟨ γ′ ⟩ B) (applyTys-★ χsᴿ)
            (multi-⊑ᵀ evolution represented))
          final (multi-⊑ᵀ evolution q)

  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-identity c⊢ position prem q) (vV ↓ all) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-identity c⊢ position prem q) (vV ↓ all) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.conceal⊑-identity
          (multi-source-conceal evolution c⊢)
          (trans (multi-source-conceal-position evolution c⊢) position)
          final (multi-⊑ᵀ evolution q)
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↓ all) vV′
      with more-precise-target-cast-value-catchup no-rebase prem vV vV′
  more-precise-target-cast-value-catchup {p = q}
      no-rebase
      (CTI.conceal⊑-only² c⊢ position mark no-target represented prem q)
      (vV ↓ all) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution , final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.conceal⊑-only²
          (multi-source-conceal evolution c⊢)
          (λ eq → position
            (trans (sym (multi-source-conceal-position evolution c⊢)) eq))
          (multi-source-mark evolution mark)
          (multi-source-disaligned evolution no-target)
          (subst≡ (λ B → _ ⊑ᵀ⟨ γ′ ⟩ B) (applyTys-★ χsᴿ)
            (multi-⊑ᵀ evolution represented))
          final (multi-⊑ᵀ evolution q)

  -- Generic source wrappers have now been stripped.  Dispatching on the
  -- target consistency therefore reaches only an exposed or paired cast.
  more-precise-target-cast-value-catchup {c′ = id a}
      no-rebase rel vV vV′ =
    target-catchup-keep (β-id vV′) vV′
      (target-id-cast-inversion² a vV vV′ rel)

  more-precise-target-cast-value-catchup {c′ = c ↦ d}
      no-rebase rel vV vV′ =
    target-catchup-refl (vV′ 《 fun 》) rel

  more-precise-target-cast-value-catchup {c′ = ∀ᶜ c}
      no-rebase rel vV vV′ =
    target-catchup-refl (vV′ 《 all 》) rel

  more-precise-target-cast-value-catchup
      {c′ = gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≠★}
      no-rebase rel vV vV′ =
    target-catchup-refl
      (vV′ 《 genᵥ A≠★ (gen-safe c A≠★ Bnv zero∈B) 》) rel

  more-precise-target-cast-value-catchup
      {c′ = (inst cᴿ) B′≠★} {p = q}
      no-rebase (CTI.⊑cast² c′ prem q) vV vV′ =
    more-precise-target-instantiation-value-catchup
      no-rebase prem vV vV′

  more-precise-target-cast-value-catchup
      {γ = γ} {c′ = (inst cᴿ) B′≠★} {p = q}
      no-rebase
      (CTI.cast⊑cast² {p = p∀} cᴸ c′ prem q)
      (vV 《 inert 》) vV′ =
    more-precise-paired-target-instantiation-value-catchup
      no-rebase prem inert vV vV′

  more-precise-target-cast-value-catchup {c′ = bot-elim}
      no-rebase rel vV vV′
      with CTIT.target-typing rel
  more-precise-target-cast-value-catchup {c′ = bot-elim}
      no-rebase rel vV vV′ | CT.⊢⟨⟩ V′⊢ bot-elim =
    ⊥-elim (no-bot-value vV′ V′⊢)

  more-precise-target-cast-value-catchup {γ = γ}
      {c′ = bot-intro} {p = q}
      no-rebase rel vV vV′ =
    ⊥-elim (source-value-target-bottom-impossible {γ = γ}
      vV (CTIT.source-typing rel) q)

  -- An identity ground injection is already an inert value.  A proper
  -- ground injection first exposes its inner cast, recursively catches that
  -- cast up, and then reattaches the generated identity tag.
  more-precise-target-cast-value-catchup
      {γ = γ}
      {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄}
      {p = q★}
      no-rebase (CTI.⊑cast² {p = pB} c′ prem q★) vV vV′
      with to-ground Gᵍ c
  more-precise-target-cast-value-catchup
      {γ = γ}
      {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄}
      {p = q★}
      no-rebase (CTI.⊑cast² {p = pB} c′ prem q★) vV vV′
    | same =
      target-catchup-refl (vV′ 《 inj 》)
        (CTI.⊑cast² c′ prem q★)
  more-precise-target-cast-value-catchup
      {γ = γ}
      {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄}
      {p = q★}
      no-rebase (CTI.⊑cast² {p = pB} c′ prem q★) vV vV′
    | other B≠G
    =
      let qG = target-ground-cast-witness { γ = γ }
            Gᵍ Bns c pB q★
          child = more-precise-target-cast-value-catchup no-rebase
            (CTI.⊑cast² c prem qG) vV vV′
          Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ ,
            evolution , final = child
          tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ ground-nonstar Gᵍ ⦄
      in
      Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ ,
        W′ ⟨ applyConsistencies χsᴿ tag ⟩ , γ′ ,
        multi-⊑ᵀ evolution q★ ,
        (V′ ⟨ c ! ⟩
          —→[ keep ]⟨ pure-step
            (ground ⦃ Gns = ground-nonstar Gᵍ ⦄ vV′ B≠G) ⟩
         (V′ ⟨ c ⟩) ⟨ tag ⟩
          —↠[ χsᴿ ]⟨ cast-↠ tag reduction ⟩
         W′ ⟨ applyConsistencies χsᴿ tag ⟩ ∎[]) ,
        (vW′ 《 applyConsistencies-Inert χsᴿ
          (inj ⦃ Gns = ground-nonstar Gᵍ ⦄) 》) ,
        evolutions-step-right refl evolution-keep evolution ,
        CTI.⊑cast² (applyConsistencies χsᴿ tag) final
          (multi-⊑ᵀ evolution q★)

  -- When both sides carry a generated ground tag, the body catch-up is at
  -- the two ground payload types and the generated tags are paired again.
  more-precise-target-cast-value-catchup
      {γ = γ} {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ cᴿ ⦃ Bns ⦄}
      {p = q★}
      no-rebase
      (CTI.cast⊑cast² {p = pB} cᴸ c′ prem q★)
      (vV 《 inertᴸ 》) vV′
      with to-ground Gᵍ cᴿ
  more-precise-target-cast-value-catchup
      {γ = γ} {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄}
      {p = q★}
      no-rebase
      (CTI.cast⊑cast² {p = pB} cᴸ c′ prem q★)
      (vV 《 inertᴸ 》) vV′
    | same =
      target-catchup-refl
        (vV′ 《 inj ⦃ Gns = Bns ⦄ 》)
        (CTI.cast⊑cast² cᴸ c′ prem q★)
  more-precise-target-cast-value-catchup
      {γ = γ} {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ cᴿ ⦃ Bns ⦄}
      {p = q★}
      no-rebase
      (CTI.cast⊑cast² {p = pB} cᴸ c′ prem q★)
      (vV 《 inertᴸ 》) vV′
    | other B≠G
      with inertᴸ
  more-precise-target-cast-value-catchup
      {γ = γ} {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ cᴿ ⦃ Bns ⦄}
      {p = q★}
      no-rebase
      (CTI.cast⊑cast² {p = pB} cᴸ c′ prem q★)
      (vV 《 inertᴸ 》) vV′
    | other B≠G
    | inj ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄ ⦃ Gns = Hns ⦄
    =
      let qHG = source-ground-cast-witness {γ = γ}
            Hᵍ Gᵍ Bns cᴿ pB
          child = more-precise-target-cast-value-catchup no-rebase
            (CTI.⊑cast² cᴿ prem qHG) vV vV′
          Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ ,
            evolution , final = child
          tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ ground-nonstar Gᵍ ⦄
      in
      Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ ,
        W′ ⟨ applyConsistencies χsᴿ tag ⟩ , γ′ ,
        multi-⊑ᵀ evolution q★ ,
        (V′ ⟨ cᴿ ! ⟩
          —→[ keep ]⟨ pure-step
            (ground ⦃ Gns = ground-nonstar Gᵍ ⦄ vV′ B≠G) ⟩
         (V′ ⟨ cᴿ ⟩) ⟨ tag ⟩
          —↠[ χsᴿ ]⟨ cast-↠ tag reduction ⟩
         W′ ⟨ applyConsistencies χsᴿ tag ⟩ ∎[]) ,
        (vW′ 《 applyConsistencies-Inert χsᴿ
          (inj ⦃ Gns = ground-nonstar Gᵍ ⦄) 》) ,
        evolutions-step-right refl evolution-keep evolution ,
        CTI.cast⊑cast² cᴸ (applyConsistencies χsᴿ tag) final
          (multi-⊑ᵀ evolution q★)

  more-precise-target-cast-value-catchup
      {γ = γ} {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ cᴿ ⦃ Bns ⦄}
      {p = q★}
      no-rebase
      (CTI.cast⊑cast² {p = pB} (c₁ ↦ c₂) c′ prem q★)
      (vV 《 fun 》) vV′
    | other B≠G
    | fun
    =
      let qG = fun-target-ground-witness
            (C.renameGround (toRenameⁱ (ηᴿᶜ γ)) Gᵍ)
            (C.renameNonStar (toRenameⁱ (ηᴿᶜ γ)) Bns)
            (rename∼ⁱ (ηᴿᶜ γ) cᴿ) pB q★
          child = more-precise-target-cast-value-catchup no-rebase
            (CTI.cast⊑cast² (c₁ ↦ c₂) cᴿ prem qG)
            (vV 《 fun 》) vV′
          Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ ,
            evolution , final = child
          tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ ground-nonstar Gᵍ ⦄
      in
      Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ ,
        W′ ⟨ applyConsistencies χsᴿ tag ⟩ , γ′ ,
        multi-⊑ᵀ evolution q★ ,
        (V′ ⟨ cᴿ ! ⟩
          —→[ keep ]⟨ pure-step
            (ground ⦃ Gns = ground-nonstar Gᵍ ⦄ vV′ B≠G) ⟩
         (V′ ⟨ cᴿ ⟩) ⟨ tag ⟩
          —↠[ χsᴿ ]⟨ cast-↠ tag reduction ⟩
         W′ ⟨ applyConsistencies χsᴿ tag ⟩ ∎[]) ,
        (vW′ 《 applyConsistencies-Inert χsᴿ
          (inj ⦃ Gns = ground-nonstar Gᵍ ⦄) 》) ,
        evolutions-step-right refl evolution-keep evolution ,
        CTI.⊑cast² (applyConsistencies χsᴿ tag) final
          (multi-⊑ᵀ evolution q★)

  more-precise-target-cast-value-catchup
      {γ = γ} {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ cᴿ ⦃ Bns ⦄}
      {p = q★}
      no-rebase
      (CTI.cast⊑cast² {p = pB} (∀ᶜ cᴸ) c′ prem q★)
      (vV 《 all 》) vV′
    | other B≠G
    | all
    =
      let qG = paired-all-injection-square {γ = γ}
            cᴸ Gᵍ Bns cᴿ pB q★
          child = more-precise-target-cast-value-catchup no-rebase
            (CTI.cast⊑cast² (∀ᶜ cᴸ) cᴿ prem qG)
            (vV 《 all 》) vV′
          Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ ,
            evolution , final = child
          tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ ground-nonstar Gᵍ ⦄
      in
      Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ ,
        W′ ⟨ applyConsistencies χsᴿ tag ⟩ , γ′ ,
        multi-⊑ᵀ evolution q★ ,
        (V′ ⟨ cᴿ ! ⟩
          —→[ keep ]⟨ pure-step
            (ground ⦃ Gns = ground-nonstar Gᵍ ⦄ vV′ B≠G) ⟩
         (V′ ⟨ cᴿ ⟩) ⟨ tag ⟩
          —↠[ χsᴿ ]⟨ cast-↠ tag reduction ⟩
         W′ ⟨ applyConsistencies χsᴿ tag ⟩ ∎[]) ,
        (vW′ 《 applyConsistencies-Inert χsᴿ
          (inj ⦃ Gns = ground-nonstar Gᵍ ⦄) 》) ,
        evolutions-step-right refl evolution-keep evolution ,
        CTI.⊑cast² (applyConsistencies χsᴿ tag) final
          (multi-⊑ᵀ evolution q★)

  more-precise-target-cast-value-catchup
      {γ = γ} {V′ = V′}
      {c′ = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ cᴿ ⦃ Bns ⦄}
      {p = q★}
      no-rebase
      (CTI.cast⊑cast² {p = pB} ((gen cᴸ) A≠★) c′ prem q★)
      (vV 《 genᵥ A≠★ safe 》) vV′
    | other B≠G
    | genᵥ A≠★′ safe′
    =
      let qG = paired-gen-injection-square {γ = γ}
            safe Gᵍ Bns cᴿ pB q★
          child = more-precise-target-cast-value-catchup no-rebase
            (CTI.cast⊑cast² ((gen cᴸ) A≠★) cᴿ prem qG)
            (vV 《 genᵥ A≠★ safe 》) vV′
          Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ ,
            evolution , final = child
          tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ ground-nonstar Gᵍ ⦄
      in
      Δᴿ′ , Σᴿ′ , keep ∷ χsᴿ ,
        W′ ⟨ applyConsistencies χsᴿ tag ⟩ , γ′ ,
        multi-⊑ᵀ evolution q★ ,
        (V′ ⟨ cᴿ ! ⟩
          —→[ keep ]⟨ pure-step
            (ground ⦃ Gns = ground-nonstar Gᵍ ⦄ vV′ B≠G) ⟩
         (V′ ⟨ cᴿ ⟩) ⟨ tag ⟩
          —↠[ χsᴿ ]⟨ cast-↠ tag reduction ⟩
         W′ ⟨ applyConsistencies χsᴿ tag ⟩ ∎[]) ,
        (vW′ 《 applyConsistencies-Inert χsᴿ
          (inj ⦃ Gns = ground-nonstar Gᵍ ⦄) 》) ,
        evolutions-step-right refl evolution-keep evolution ,
        CTI.⊑cast² (applyConsistencies χsᴿ tag) final
          (multi-⊑ᵀ evolution q★)

  -- A projection can fire only against a generated ground tag.  The live
  -- right-injection inversion removes that tag after its ground is shown to
  -- be the projection ground.
  more-precise-target-cast-value-catchup
      {γ = γ} {V = V} {V′ = V′} {A = A}
      {ν′ = ν}
      {c′ = ？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄}
      {p = qB}
      no-rebase (CTI.⊑cast² {p = p★} c′ prem qB) vV vV′
      with from-ground Gᵍ c | canonical-★ vV′ (CTIT.target-typing prem)
  more-precise-target-cast-value-catchup
      {γ = γ} {V = V} {V′ = V′} {A = A}
      {ν′ = ν}
      {c′ = ？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄}
      {p = qB}
      no-rebase (CTI.⊑cast² {p = p★} c′ prem qB) vV vV′
    | same
    | sv-tag {μ = μ} {W = N} {G = H} {Gᵍ = Hᵍ}
        ⦃ G∼★ = H∼★ ⦄ ⦃ Gns = Hns ⦄
        vN refl
      =
      let qG : A ⊑ᵀ⟨ γ ⟩ G
          qG = target-expand-cast-witness {γ = γ} {G = G} {B = G}
            {ν = ν}
            Gᵍ Bns (idᵍ Gᵍ) p★ qB
          step , core = target-project-tag-untag
            {γ = γ} {V = V} {N = N} {A = A} {H = H} {G = G}
            {μ = μ} {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
            ⦃ H∼★ = H∼★ ⦄ ⦃ ★∼G = ★∼G ⦄
            ⦃ Hns = Hns ⦄ ⦃ Gns = Bns ⦄ {p★ = p★} {qG = qG}
            (value→spine vV) vN prem
            (right-injection-ground-match² {γ = γ} {M = V} {N = N}
              {A = A} {H = H} {G = G} {ν = μ}
              {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
              {H∼★ = H∼★} {Hns = Hns} {p★ = p★}
              (value→spine vV) vN prem qG)
      in target-catchup-keep step vN core
  more-precise-target-cast-value-catchup
      {γ = γ} {V = V} {V′ = V′} {A = A}
      {ν′ = ν}
      {c′ = ？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄}
      {p = qB}
      no-rebase (CTI.⊑cast² {p = p★} c′ prem qB) vV vV′
    | other B≠G
    | sv-tag {μ = μ} {W = N} {G = H} {Gᵍ = Hᵍ}
        ⦃ G∼★ = H∼★ ⦄ ⦃ Gns = Hns ⦄
        vN refl
      =
      let qG : A ⊑ᵀ⟨ γ ⟩ G
          qG = target-expand-cast-witness {γ = γ} {G = G} {ν = ν}
            Gᵍ Bns c p★ qB
          untag-step , core = target-project-tag-untag
            {γ = γ} {V = V} {N = N} {A = A} {H = H} {G = G}
            {μ = μ} {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
            ⦃ H∼★ = H∼★ ⦄ ⦃ ★∼G = ★∼G ⦄
            ⦃ Hns = Hns ⦄
            ⦃ Gns = ground-nonstar Gᵍ ⦄ {p★ = p★} {qG = qG}
            (value→spine vV) vN prem
            (right-injection-ground-match² {γ = γ} {M = V} {N = N}
              {A = A} {H = H} {G = G} {ν = μ}
              {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
              {H∼★ = H∼★} {Hns = Hns} {p★ = p★}
              (value→spine vV) vN prem qG)
          child = more-precise-target-cast-value-catchup no-rebase
            (CTI.⊑cast² c core qB) vV vN
          Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ ,
            evolution , final = child
          proj = ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
            ⦃ ground-nonstar Gᵍ ⦄
      in
      Δᴿ′ , Σᴿ′ , keep ∷ keep ∷ χsᴿ , W′ , γ′ ,
        multi-⊑ᵀ evolution qB ,
        ((N ⟨ _! ⦃ Hᵍ ⦄ ⦃ H∼★ ⦄ (idᵍ Hᵍ) ⦃ Hns ⦄ ⟩)
          ⟨ ？ c ⟩
          —→[ keep ]⟨ pure-step
            (expand ⦃ Gns = ground-nonstar Gᵍ ⦄
              (vN 《 inj ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄ ⦃ Gns = Hns ⦄ 》)
              (λ G≡B → B≠G (sym G≡B))) ⟩
         ((N ⟨ _! ⦃ Hᵍ ⦄ ⦃ H∼★ ⦄ (idᵍ Hᵍ) ⦃ Hns ⦄ ⟩)
           ⟨ proj ⟩) ⟨ c ⟩
          —→[ keep ]⟨ ξ-⟨⟩ (pure-step untag-step) refl ⟩
         N ⟨ c ⟩
          —↠[ χsᴿ ]⟨ reduction ⟩
         W′ ∎[]) ,
        vW′ ,
        evolutions-step-right refl evolution-keep
          (evolutions-step-right refl evolution-keep evolution) ,
        subst≡ (λ s → γ′ ⊢² _ ⊑ W′ ∶ s)
          (⊑-unique r (multi-⊑ᵀ evolution qB)) final

  -- For a paired projection, the ground square supplies the input-type
  -- relation needed to remove the target tag.  The source inert cast is then
  -- replayed either alone or paired with the remaining target cast.
  more-precise-target-cast-value-catchup
      {γ = γ} {V = M ⟨ cᴸ ⟩} {V′ = V′}
      {ν′ = ν}
      {c′ = ？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ cᴿ ⦃ Bns ⦄}
      {p = qB}
      no-rebase
      (CTI.cast⊑cast² {p = p★} cᴸ c′ prem qB)
      (vM 《 inertᴸ 》) vV′
      with from-ground Gᵍ cᴿ
         | canonical-★ vV′ (CTIT.target-typing prem)
  more-precise-target-cast-value-catchup
      {γ = γ} {V = M ⟨ cᴸ ⟩} {V′ = V′}
      {ν′ = ν}
      {c′ = ？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄}
      {p = qB}
      no-rebase
      (CTI.cast⊑cast² {p = p★} cᴸ c′ prem qB)
      (vM 《 inertᴸ 》) vV′
    | same
    | sv-tag {μ = μ} {W = N} {G = H} {Gᵍ = Hᵍ}
        ⦃ G∼★ = H∼★ ⦄ ⦃ Gns = Hns ⦄
        vN refl
      =
      let qG = paired-projection-ground-witness
            {γ = γ} {G = G} {B = G} {νᴿ = ν} {cᴸ = cᴸ}
            inertᴸ Gᵍ Bns (idᵍ Gᵍ) p★ qB
          step , core = target-project-tag-untag
            {γ = γ} {V = M} {N = N} {H = H} {G = G}
            {μ = μ} {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
            ⦃ H∼★ = H∼★ ⦄ ⦃ ★∼G = ★∼G ⦄
            ⦃ Hns = Hns ⦄ ⦃ Gns = Bns ⦄ {p★ = p★} {qG = qG}
            (value→spine vM) vN prem
            (right-injection-ground-match² {γ = γ} {M = M} {N = N}
              {H = H} {G = G} {ν = μ}
              {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
              {H∼★ = H∼★} {Hns = Hns} {p★ = p★}
              (value→spine vM) vN prem qG)
      in target-catchup-keep step vN (CTI.cast⊑² cᴸ core qB)
  more-precise-target-cast-value-catchup
      {γ = γ} {V = M ⟨ cᴸ ⟩} {V′ = V′}
      {ν′ = ν}
      {c′ = ？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ cᴿ ⦃ Bns ⦄}
      {p = qB}
      no-rebase
      (CTI.cast⊑cast² {p = p★} cᴸ c′ prem qB)
      (vM 《 inertᴸ 》) vV′
    | other G≠B
    | sv-tag {μ = μ} {W = N} {G = H} {Gᵍ = Hᵍ}
        ⦃ G∼★ = H∼★ ⦄ ⦃ Gns = Hns ⦄
        vN refl
      =
      let qG = paired-projection-ground-witness {γ = γ} {cᴸ = cᴸ}
            inertᴸ Gᵍ Bns cᴿ p★ qB
          untag-step , core = target-project-tag-untag
            {γ = γ} {V = M} {N = N} {H = H} {G = G}
            {μ = μ} {ν = ν} {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
            ⦃ H∼★ = H∼★ ⦄ ⦃ ★∼G = ★∼G ⦄
            ⦃ Hns = Hns ⦄
            ⦃ Gns = ground-nonstar Gᵍ ⦄ {p★ = p★} {qG = qG}
            (value→spine vM) vN prem
            (right-injection-ground-match² {γ = γ} {M = M} {N = N}
              {H = H} {G = G} {ν = μ}
              {Hᵍ = Hᵍ} {Gᵍ = Gᵍ}
              {H∼★ = H∼★} {Hns = Hns} {p★ = p★}
              (value→spine vM) vN prem qG)
          child = more-precise-target-cast-value-catchup no-rebase
            (CTI.cast⊑cast² cᴸ cᴿ core qB) (vM 《 inertᴸ 》) vN
          Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ ,
            evolution , final = child
          proj = ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
            ⦃ ground-nonstar Gᵍ ⦄
      in
      Δᴿ′ , Σᴿ′ , keep ∷ keep ∷ χsᴿ , W′ , γ′ ,
        multi-⊑ᵀ evolution qB ,
        ((N ⟨ _! ⦃ Hᵍ ⦄ ⦃ H∼★ ⦄ (idᵍ Hᵍ) ⦃ Hns ⦄ ⟩)
          ⟨ ？ cᴿ ⟩
          —→[ keep ]⟨ pure-step
            (expand ⦃ Gns = ground-nonstar Gᵍ ⦄
              (vN 《 inj ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄ ⦃ Gns = Hns ⦄ 》)
              (λ G≡B → G≠B (sym G≡B))) ⟩
         ((N ⟨ _! ⦃ Hᵍ ⦄ ⦃ H∼★ ⦄ (idᵍ Hᵍ) ⦃ Hns ⦄ ⟩)
           ⟨ proj ⟩) ⟨ cᴿ ⟩
          —→[ keep ]⟨ ξ-⟨⟩ (pure-step untag-step) refl ⟩
         N ⟨ cᴿ ⟩
          —↠[ χsᴿ ]⟨ reduction ⟩
         W′ ∎[]) ,
        vW′ ,
        evolutions-step-right refl evolution-keep
          (evolutions-step-right refl evolution-keep evolution) ,
        subst≡ (λ s → γ′ ⊢² _ ⊑ W′ ∶ s)
          (⊑-unique r (multi-⊑ᵀ evolution qB)) final
