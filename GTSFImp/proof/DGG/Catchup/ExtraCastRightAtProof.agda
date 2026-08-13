module proof.DGG.Catchup.ExtraCastRightAtProof where

-- File Charter:
--   * Adapts the M4 extra-cast proof to the fuel-indexed M6 surface.
--   * Uses strictly smaller fuel only for recursive ground/projection
--     provenance and delegates instantiation to the supplied current-fuel
--     M5 worker.
--   * Depends on the M3 right-injection inversion theorem, the stage-1 M4
--     world interface, and the M6 fuel/decrease support.

import Data.Fin as Fin
import Data.List as List
open import Data.Empty using (⊥-elim)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
import Consistency as C
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; idᵍ; _!; ？_)
open import CastTerms using
  (Term; Value; Inert; _⊢_⦂_; ⟨_,_,_⟩; ƛ_; Λ_; $; inj; fun; all;
   seal; genᵥ; _⟨_⟩; _《_》; _↑_; _↓_)
open import Reduction

import Imprecision as I
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (ExtraCastRightAt; InstCatchupRightAt; FuelStepSurface)
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
open import proof.DGG.Inversion.SpineValueDef using
  (AllValueView; allv-Λ; allv-∀; allv-gen; allv-reveal; allv-conceal;
   SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
   sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all)
open import proof.ImprecisionConsistency using
  (renameᵗ-injective; ext-injective; toRenameᵗ-injective)
import proof.Imprecision as PI
open import proof.Reduction using (cast-↠; applyConsistencies-Inert)
import proof.TypeSafety.Progress as Prog

open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


value→spine : ∀ {Δ} {V : Term Δ}
  → Value V
  → SpineValue V
value→spine (ƛ N) = sv-ƛ N
value→spine (Λ vV) = sv-Λ (value→spine vV)
value→spine ($ κ) = sv-$ κ
value→spine (vV 《 inert 》) = sv-cast (value→spine vV) inert
value→spine (vV ↑ fun) = sv-reveal-fun (value→spine vV)
value→spine (vV ↑ all) = sv-reveal-all (value→spine vV)
value→spine (vV ↓ seal) = sv-seal (value→spine vV)
value→spine (vV ↓ fun) = sv-conceal-fun (value→spine vV)
value→spine (vV ↓ all) = sv-conceal-all (value→spine vV)


all-view→all-value-view : ∀ {Δ} {V : Term Δ} {A : Ty (suc Δ)}
  → Prog.AllView A V
  → AllValueView V
all-view→all-value-view (Prog.av-Λ vV eq) = allv-Λ vV eq
all-view→all-value-view (Prog.av-∀ vV eq) = allv-∀ vV eq
all-view→all-value-view (Prog.av-gen vV A≢★ safe eq) =
  allv-gen vV A≢★ safe eq
all-view→all-value-view (Prog.av-reveal vV eq) = allv-reveal vV eq
all-view→all-value-view (Prog.av-conceal vV eq) = allv-conceal vV eq


keepWorldExtendᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → ECR.WorldExtendᴿ χs W W′
  → ECR.WorldExtendᴿ (keep ∷ χs) W W′
keepWorldExtendᴿ ext = record
  { sourceStore-kept = ECR.sourceStore-kept ext
  ; targetStore-follows = ECR.targetStore-follows ext
  ; transport⊑ᵂ = ECR.transport⊑ᵂ ext
  }


mapCtxᴿ-keepWorldExtend : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → (gamma : CtxImp W)
  → ECR.mapCtxᴿ (keepWorldExtendᴿ ext) gamma ≡ ECR.mapCtxᴿ ext gamma
mapCtxᴿ-keepWorldExtend ext List.[] = refl
mapCtxᴿ-keepWorldExtend {χs = χs} ext
    (CTI2.ctx-imp A B p List.∷ gamma) =
  cong (λ gamma′ →
    CTI2.ctx-imp A (applyTys χs B) (ECR.transport⊑ᵂ ext p)
      List.∷ gamma′)
    (mapCtxᴿ-keepWorldExtend ext gamma)


mapCtxᴿ-keep²WorldExtend : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → (gamma : CtxImp W)
  → ECR.mapCtxᴿ (keepWorldExtendᴿ (keepWorldExtendᴿ ext)) gamma ≡
    ECR.mapCtxᴿ ext gamma
mapCtxᴿ-keep²WorldExtend ext gamma =
  trans (mapCtxᴿ-keepWorldExtend (keepWorldExtendᴿ ext) gamma)
    (mapCtxᴿ-keepWorldExtend ext gamma)


extra-cast-right-at : ∀ {fuel}
  → RightInjInversion²
  → FuelStepSurface fuel
  → InstCatchupRightAt fuel
  → ExtraCastRightAt fuel
extra-cast-right-at inversion fuel-step inst-catchup
    {W = W} {γ = gamma} {M = M} {M′ = M′}
    M⊑M′ vM vM′ c′ c′<fuel q (ECR.catchup-inert inert) =
  ECR.inert-extra-cast-right² M⊑M′ vM vM′ c′ inert q
extra-cast-right-at inversion fuel-step inst-catchup
    M⊑M′ vM vM′ _ c′<fuel q (ECR.catchup-id a) =
  ECR.id-extra-cast-right² M⊑M′ vM vM′ a q
extra-cast-right-at inversion fuel-step inst-catchup
    {γ = gamma} {M = M} {M′ = M′}
    M⊑M′ vM vM′ _ c′<fuel q
    (ECR.catchup-ground-other {Gᵍ = Gᵍ} {G∼★ = G∼★}
      {Bns = Bns} {c = c} B≢G r generated-c)
    with FuelStepSurface.smaller-extra fuel-step c′<fuel
      M⊑M′ vM vM′ c (n<1+n _) r generated-c
... | Δᴿ′ , χs , Δ′ , W′ , ext , N′ ,
      (vN′ , M′c↠N′ , M⊑N′) =
  Δᴿ′ , keep ∷ χs , Δ′ , W′ , keepWorldExtendᴿ ext ,
  N′ ⟨ applyConsistencies χs tag ⟩ ,
  vN′ 《 applyConsistencies-Inert χs tag-inert 》 ,
  (M′ ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄ ⟩
    —→[ keep ]⟨
      pure-step
        (ground ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
          ⦃ Ans = Bns ⦄ ⦃ Gns = C.ground-nonstar Gᵍ ⦄
          vM′ B≢G)
    ⟩
  M′ ⟨ c ⟩ ⟨ tag ⟩
    —↠[ χs ]⟨ cast-↠ tag M′c↠N′ ⟩
  N′ ⟨ applyConsistencies χs tag ⟩ ∎[]) ,
  subst≡
    (λ gamma′ → W′ ∣ gamma′ ⊢² M ⊑
      N′ ⟨ applyConsistencies χs tag ⟩ ∶ ECR.transport⊑ᵂ ext q)
    (sym (mapCtxᴿ-keepWorldExtend ext gamma))
    (CTI2.⊑cast² (applyConsistencies χs tag) M⊑N′
      (ECR.transport⊑ᵂ ext q))
  where
  tag : _ ⊢ _ ∼ ★
  tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
    ⦃ C.ground-nonstar Gᵍ ⦄

  tag-inert : Inert tag
  tag-inert = inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
    ⦃ Gns = C.ground-nonstar Gᵍ ⦄
extra-cast-right-at inversion fuel-step inst-catchup
    {γ = gamma} {M = M}
    M⊑N! vM vN! _ c′<fuel q
    (ECR.catchup-projection
      (ECR.generated-project-same {Gᵍ = Gᵍ} {G∼★ = G∼★}
        {★∼G = ★∼G} vN)) =
  _ , keep ∷ [] , _ , _ , ECR.sameWorldKeepExtendᴿ , _ , vN ,
  (_
    —→[ keep ]⟨
      pure-step
        (tag-untag ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
          ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = C.ground-nonstar Gᵍ ⦄ vN)
    ⟩
  _ ∎[]) ,
  subst≡ (λ gamma′ → _ ∣ gamma′ ⊢² M ⊑ _ ∶ q)
    (sym (ECR.mapCtxᴿ-keep gamma))
    (inversion (value→spine vM) vN M⊑N! q)
extra-cast-right-at inversion fuel-step inst-catchup
    {γ = gamma} {M = M}
    M⊑N! vM vN! _ c′<fuel q
    (ECR.catchup-projection
      (ECR.generated-project-expand {Gᵍ = Gᵍ} {G∼★ = G∼★}
        {★∼G = ★∼G} {Bns = Bns} {N = N} {c = c}
        vN B≢G r generated-c))
    with FuelStepSurface.smaller-extra fuel-step c′<fuel
      (inversion (value→spine vM) vN M⊑N! r)
      vM vN c (n<1+n _) q generated-c
... | Δᴿ′ , χs , Δ′ , W′ , ext , N′ ,
      (vN′ , Nc↠N′ , M⊑N′) =
  Δᴿ′ , keep ∷ keep ∷ χs , Δ′ , W′ ,
  keepWorldExtendᴿ (keepWorldExtendᴿ ext) , N′ , vN′ ,
  (N ⟨ tag ⟩ ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄ ⟩
    —→[ keep ]⟨
      pure-step
        (expand ⦃ Gᵍ = Gᵍ ⦄ ⦃ ★∼G = ★∼G ⦄ ⦃ Bns = Bns ⦄
          ⦃ Gns = C.ground-nonstar Gᵍ ⦄
          (vN 《 tag-inert 》) (λ eq → B≢G (sym eq)))
    ⟩
  N ⟨ tag ⟩ ⟨ proj ⟩ ⟨ c ⟩
    —→[ keep ]⟨
      ξ-⟨⟩
        (pure-step
          (tag-untag ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
            ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = C.ground-nonstar Gᵍ ⦄ vN))
        refl
    ⟩
  N ⟨ c ⟩
    —↠[ χs ]⟨ Nc↠N′ ⟩
  N′ ∎[]) ,
  subst≡
    (λ gamma′ → W′ ∣ gamma′ ⊢² M ⊑ N′ ∶
      ECR.transport⊑ᵂ ext q)
    (sym (mapCtxᴿ-keep²WorldExtend ext gamma)) M⊑N′
  where
  tag : _ ⊢ _ ∼ ★
  tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
    ⦃ C.ground-nonstar Gᵍ ⦄

  tag-inert : Inert tag
  tag-inert = inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
    ⦃ Gns = C.ground-nonstar Gᵍ ⦄

  proj : _ ⊢ ★ ∼ _
  proj = ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
    ⦃ C.ground-nonstar Gᵍ ⦄
extra-cast-right-at inversion fuel-step inst-catchup
    M⊑M′ vM vM′ _ c′<fuel q ECR.catchup-inst =
  inst-catchup M⊑M′ vM vM′
    (all-view→all-value-view
      (Prog.canonical-∀ vM′ (CTI2T.target-typing² M⊑M′)))
    _ _ c′<fuel q
extra-cast-right-at inversion fuel-step inst-catchup
    M⊑M′ vM vM′ _ c′<fuel q ECR.catchup-bot-elim =
  ⊥-elim (Prog.no-bot-value vM′ (CTI2T.target-typing² M⊑M′))
extra-cast-right-at inversion fuel-step inst-catchup
    {A = ＇ X} M⊑M′ vM vM′ _ c′<fuel () ECR.catchup-bot-intro
extra-cast-right-at inversion fuel-step inst-catchup
    {A = ‵ ι} M⊑M′ vM vM′ _ c′<fuel () ECR.catchup-bot-intro
extra-cast-right-at inversion fuel-step inst-catchup
    {A = ★} M⊑M′ vM vM′ _ c′<fuel () ECR.catchup-bot-intro
extra-cast-right-at inversion fuel-step inst-catchup
    {A = A ⇒ B} M⊑M′ vM vM′ _ c′<fuel () ECR.catchup-bot-intro
extra-cast-right-at inversion fuel-step inst-catchup
    {W = W} {M = M} {A = `∀ A₀}
    M⊑M′ vM vM′ _ c′<fuel (I.∀⊑∀ qbody) ECR.catchup-bot-intro =
  ⊥-elim
    (Prog.no-bot-value vM
      (subst≡ (λ T → ⟨ _ , _ , _ ⟩ ⊢ M ⦂ `∀ T)
        (renameᵗ-injective
          (ext-injective (toRenameᵗ-injective (CTI2.ηᴸʷ W)))
          (PI.imprecision-to-fresh qbody))
        (CTI2T.source-typing² M⊑M′)))
extra-cast-right-at inversion fuel-step inst-catchup
    {A = `∀ A₀} M⊑M′ vM vM′ _ c′<fuel
    (I.∀⊑ Anv zero∈A qbody) ECR.catchup-bot-intro =
  ⊥-elim (PI.imprecision-no-star-to-bot refl qbody zero∈A)
