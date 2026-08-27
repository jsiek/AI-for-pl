{-# OPTIONS --safe #-}

module proof.DGG.Catchup.MorePreciseTargetCastValueCatchupProof where

-- File Charter:
--   * Proves target consistency-cast catch-up for every non-instantiation
--     constructor by direct structural recursion on the target cast.
--   * Strips generic source cast, type-abstraction, reveal, and conceal
--     wrappers before dispatching on the target consistency.
--   * Is parameterized by the exposed beta-instantiation induction, the
--     source-scope closing induction, and their exact pre-induction squares.
--   * Uses no fuel, residual-family dispatcher, compatibility context, or
--     named result wrapper.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using () renaming ([] to []ᵗ)
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
import Imprecision as I
open import TyStore using (TyStore)
open import Consistency using
  ( Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; idᵍ; _↦_; ∀ᶜ_; _!
  ; ？_; inst_; gen_; instᵐ; bot-elim; bot-intro; ground-nonstar
  )
import Consistency as C
import Conversion as Conv
open import CastTerms using
  ( Ctx; Term; Value; Inert; ⟨_,_,_⟩; _⊢_⦂_; _⟨_⟩; _《_》
  ; ƛ_; Λ_; $; _↑_; _↓_; inj; fun; all; genᵥ
  )
import CastTerms as CT
open import Reduction using
  ( StoreChanges; []; _∷_; keep; applyTys; pure-step; β-id; ground
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
  proof.DGG.Catchup.MorePrecisePairedTargetInstantiationInputSquareDef
  using (MorePrecisePairedTargetInstantiationInputSquareᵀ)
open import proof.DGG.InjectionConsistency using (rename∼ⁱ)
open import proof.DGG.Inversion.SpineValueDef using
  ( SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal
  ; sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all
  ; variable-obligation-aligns
  )
open import proof.DGG.Inversion.RightInjInversion2Lemma using
  (right-inj-inversion²)
import proof.DGG.TagTransport as TT
open import proof.DGG.World
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution; evolutions-refl; evolutions-step-right; multi-⊑ᵀ
  ; multi-source-mark; multi-source-disaligned
  ; multi-source-reveal; multi-source-conceal
  ; multi-source-reveal-position; multi-source-conceal-position
  )
open import proof.Consistency using (gen-safe)
open import proof.Imprecision using
  (imprecision-to-fresh; imprecision-no-star-to-bot; ★⊑-inv; ⊑-unique)
open import proof.ImprecisionConsistency using
  ( refl⊑; ground-cast-target⊑; ground-cast-source⊑
  ; expand-cast-source⊑; ground-targets-unique⊑
  ; ground-cast-target-unique⊑
  ; ground-target-nonvar-to-star⊑; all-ground-body
  ; nonstar-from-≢★; rename-occurs; unshift-nonvar
  ; ext-injective; renameᵗ-injective
  )
open import proof.TypeSafety.Progress using
  ( no-bot-value; to-ground; from-ground; same; other
  ; canonical-★; sv-tag
  )
open import proof.Reduction using
  (cast-↠; applyConsistencies-Inert; applyTys-★)


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
-- Structural catch-up for a target cast
------------------------------------------------------------------------

module _
    (inst-catchup : MorePreciseTargetInstantiationValueCatchupᵀ)
    (paired-inst-input-square :
      MorePrecisePairedTargetInstantiationInputSquareᵀ)
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
        no-rebase prem body-value vV′
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
    inst-catchup {q = q} no-rebase prem vV vV′

  more-precise-target-cast-value-catchup
      {γ = γ} {c′ = (inst cᴿ) B′≠★} {p = q}
      no-rebase
      (CTI.cast⊑cast² {p = p∀} cᴸ c′ prem q)
      (vV 《 inert 》) vV′
      with inst-catchup {q = paired-inst-input-square
          {γ = γ} {cᴸ = cᴸ} {cᴿ = cᴿ}
          inert B′≠★ p∀ q}
        no-rebase prem vV vV′
  more-precise-target-cast-value-catchup
      {γ = γ} {c′ = (inst cᴿ) B′≠★} {p = q}
      no-rebase
      (CTI.cast⊑cast² {p = p∀} cᴸ c′ prem q)
      (vV 《 inert 》) vV′
    | Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , r , reduction , vW′ , evolution ,
      final =
      Δᴿ′ , Σᴿ′ , χsᴿ , W′ , γ′ , multi-⊑ᵀ evolution q ,
        reduction , vW′ , evolution ,
        CTI.cast⊑² cᴸ final (multi-⊑ᵀ evolution q)

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
