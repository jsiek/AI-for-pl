module proof.DGG.Catchup.ExtraCastRightProof where

-- File Charter:
--   * Higher-order M4 workers for `ExtraCastRight²`.
--   * The module is parameterized by the M3 right-injection inversion
--     statement and the M5 inst-catch-up statement, so it does not import
--     either proof implementation.
--   * This file is intentionally limited to total case-family workers while
--     the consuming projection families are being closed.

import Data.List as List
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
import Consistency as C
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; idᵍ; _↦_; ∀ᶜ_;
   _!; ？_; gen_; inst_; bot-elim; bot-intro; extᵐ; genᵐ;
   instᵐ; toRenameᵗ)
import CastTerms
open import CastTerms using
  (Term; Value; Inert; GenSafe; _⊢_⦂_; ⟨_,_,_⟩; ƛ_; Λ_; $;
   inj; fun; all; seal;
   genᵥ; _⟨_⟩; _《_》; _↑_; _↓_)
open import Reduction
import Imprecision as I
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.ExtraCastRight2 using
  (ExtraCastRight²; InstCatchupRight²; CatchupCast;
   catchup-inert; catchup-id; catchup-ground-other; catchup-projection;
   catchup-inst; catchup-bot-elim; catchup-bot-intro;
   generated-project-same; generated-project-expand;
   WorldExtendᴿ; mapCtxᴿ;
   mapCtxᴿ-keep; sameWorldKeepExtendᴿ; inert-extra-cast-right²;
   id-extra-cast-right²)
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
open import proof.DGG.Inversion.SpineValueDef using
  (AllValueView; allv-Λ; allv-∀; allv-gen; allv-reveal; allv-conceal;
   SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
   sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all)
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)
open import proof.Consistency using (gen-safe)
open import proof.ImprecisionConsistency using
  (renameᵗ-injective; ext-injective; toRenameᵗ-injective)
import proof.Imprecision as PI
open import proof.Reduction using (cast-↠; applyConsistencies-Inert)
import proof.TypeSafety.Progress as Prog

module _
    (inversion : RightInjInversion²)
    (inst-catchup : InstCatchupRight²)
  where

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
    → WorldExtendᴿ χs W W′
    → WorldExtendᴿ (keep ∷ χs) W W′
  keepWorldExtendᴿ ext = record
    { sourceStore-kept = WorldExtendᴿ.sourceStore-kept ext
    ; targetStore-follows = WorldExtendᴿ.targetStore-follows ext
    ; transport⊑ᵂ = WorldExtendᴿ.transport⊑ᵂ ext
    }

  mapCtxᴿ-keepWorldExtend : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    → (ext : WorldExtendᴿ χs W W′)
    → (γ : CtxImp W)
    → mapCtxᴿ (keepWorldExtendᴿ ext) γ ≡ mapCtxᴿ ext γ
  mapCtxᴿ-keepWorldExtend ext List.[] = refl
  mapCtxᴿ-keepWorldExtend {χs = χs} ext
      (CTI2.ctx-imp A B p List.∷ γ) =
    cong (λ γ′ →
      CTI2.ctx-imp A (χs ▶ᵗ B)
        (WorldExtendᴿ.transport⊑ᵂ ext p) List.∷ γ′)
      (mapCtxᴿ-keepWorldExtend ext γ)

  mapCtxᴿ-keep²WorldExtend : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    → (ext : WorldExtendᴿ χs W W′)
    → (γ : CtxImp W)
    → mapCtxᴿ (keepWorldExtendᴿ (keepWorldExtendᴿ ext)) γ ≡
      mapCtxᴿ ext γ
  mapCtxᴿ-keep²WorldExtend ext γ =
    trans
      (mapCtxᴿ-keepWorldExtend (keepWorldExtendᴿ ext) γ)
      (mapCtxᴿ-keepWorldExtend ext γ)

  extra-cast-right-inert² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → (vM′ : Value M′)
    → (c′ : ν ⊢ B ∼ B′)
    → Inert c′
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-inert² M⊑M′ vM vM′ c′ inert q =
    inert-extra-cast-right² M⊑M′ vM vM′ c′ inert q

  extra-cast-right-fun² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ C C′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ (B ⇒ C)}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → (vM′ : Value M′)
    → (c : ν ⊢ B ∼ B′)
    → (d : ν ⊢ C ∼ C′)
    → (q : A ⊑ᵂ⟨ W ⟩ (B′ ⇒ C′))
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ c ↦ d ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-fun² M⊑M′ vM vM′ c d q =
    extra-cast-right-inert² M⊑M′ vM vM′ (c ↦ d) fun q

  extra-cast-right-all² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ : Ty (suc Δᴿ)} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → (vM′ : Value M′)
    → (c : extᵐ ν ⊢ B ∼ B′)
    → (q : A ⊑ᵂ⟨ W ⟩ `∀ B′)
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ ∀ᶜ c ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-all² M⊑M′ vM vM′ c q =
    extra-cast-right-inert² M⊑M′ vM vM′ (∀ᶜ c) all q

  extra-cast-right-gen-safe² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ} {C : Ty (suc Δᴿ)}
      {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → (vM′ : Value M′)
    → (c : genᵐ ν ⊢ ⇑ᵗ B ∼ C)
    → ⦃ Cnv : NonVar C ⦄
    → ⦃ zero∈C : Fin.zero ∈ᵗ C ⦄
    → (B≢★ : B ≢ ★)
    → GenSafe c
    → (q : A ⊑ᵂ⟨ W ⟩ `∀ C)
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ (gen c) B≢★ ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-gen-safe² M⊑M′ vM vM′ c B≢★ safe q =
    extra-cast-right-inert² M⊑M′ vM vM′
      ((gen c) B≢★) (genᵥ B≢★ safe) q

  extra-cast-right-ground-same² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {G : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {Gᵍ : Ground G} {G∼★ : ν ⊢ G ∼★}
      {p : A ⊑ᵂ⟨ W ⟩ G}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → (vM′ : Value M′)
    → (q : A ⊑ᵂ⟨ W ⟩ ★)
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨
                _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
                  ⦃ C.ground-nonstar Gᵍ ⦄
              ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-ground-same² {Gᵍ = Gᵍ} {G∼★ = G∼★}
      M⊑M′ vM vM′ q =
    extra-cast-right-inert² M⊑M′ vM vM′
      (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
        ⦃ C.ground-nonstar Gᵍ ⦄)
      (inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
        ⦃ Gns = C.ground-nonstar Gᵍ ⦄)
      q

  extra-cast-right-ground-other² : ExtraCastRight²
    → ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {Gᵍ : Ground G} {G∼★ : ν ⊢ G ∼★}
      {Bns : NonStar B} {p : A ⊑ᵂ⟨ W ⟩ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → (vM′ : Value M′)
    → (c : ν ⊢ B ∼ G)
    → B ≢ G
    → (q : A ⊑ᵂ⟨ W ⟩ ★)
    → (r : A ⊑ᵂ⟨ W ⟩ G)
    → CatchupCast p M′ c r
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨
                _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄
              ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-ground-other² ecr
      {W = W} {γ = γ} {M = M} {M′ = M′}
      {Gᵍ = Gᵍ} {G∼★ = G∼★} {Bns = Bns} {p = p}
      M⊑M′ vM vM′ c B≢G q r generated-c
      with ecr M⊑M′ vM vM′ c r generated-c
  ... | Δᴿ′ , χs , Δ′ , W′ , ext , N′ ,
        vN′ , M′c↠N′ , M⊑N′ =
    Δᴿ′ , keep ∷ χs , Δ′ , W′ , keepWorldExtendᴿ ext ,
    N′ ⟨ χs ▶ᶜ tag ⟩ ,
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
    N′ ⟨ χs ▶ᶜ tag ⟩ ∎[]) ,
    subst≡
      (λ γ′ → W′ ∣ γ′ ⊢² M ⊑ N′ ⟨ χs ▶ᶜ tag ⟩ ∶
        WorldExtendᴿ.transport⊑ᵂ ext q)
      (sym (mapCtxᴿ-keepWorldExtend ext γ))
      (CTI2.⊑cast² (χs ▶ᶜ tag) M⊑N′
        (WorldExtendᴿ.transport⊑ᵂ ext q))
    where
    tag : _ ⊢ _ ∼ ★
    tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
      ⦃ C.ground-nonstar Gᵍ ⦄

    tag-inert : Inert tag
    tag-inert = inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
      ⦃ Gns = C.ground-nonstar Gᵍ ⦄

  extra-cast-right-project-same² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {N : Term Δᴿ}
      {A : Ty Δᴸ} {G : Ty Δᴿ} {μ ν : Env∼ Δᴿ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {★∼G : ν ⊢★∼ G}
      {p : A ⊑ᵂ⟨ W ⟩ ★}
    → W ∣ γ ⊢² M ⊑
        N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ C.ground-nonstar Gᵍ ⦄ ⟩ ∶ p
    → Value M
    → Value N
    → (q : A ⊑ᵂ⟨ W ⟩ G)
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (N ⟨
                _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
                  ⦃ C.ground-nonstar Gᵍ ⦄
              ⟩ ⟨
                ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
                  ⦃ C.ground-nonstar Gᵍ ⦄
              ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-project-same²
      {W = W} {γ = γ} {M = M} {N = N}
      {Gᵍ = Gᵍ} {G∼★ = G∼★} {★∼G = ★∼G}
      M⊑N! vM vN q =
    _ , keep ∷ [] , _ , W , sameWorldKeepExtendᴿ , N ,
    vN ,
    ((N ⟨ tag ⟩ ⟨ proj ⟩)
      —→[ keep ]⟨
        pure-step
          (tag-untag ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
            ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = C.ground-nonstar Gᵍ ⦄
            vN)
      ⟩
    N ∎[]) ,
    subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ N ∶ q)
      (sym (mapCtxᴿ-keep γ))
      (inversion (value→spine vM) vN M⊑N! q)
    where
    tag : _ ⊢ _ ∼ ★
    tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
      ⦃ C.ground-nonstar Gᵍ ⦄

    proj : _ ⊢ ★ ∼ _
    proj = ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
      ⦃ C.ground-nonstar Gᵍ ⦄

  extra-cast-right-project-expand² : ExtraCastRight²
    → ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {N : Term Δᴿ}
      {A : Ty Δᴸ} {G B : Ty Δᴿ} {μ ν : Env∼ Δᴿ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {★∼G : ν ⊢★∼ G} {Bns : NonStar B}
      {p : A ⊑ᵂ⟨ W ⟩ ★}
    → W ∣ γ ⊢² M ⊑
        N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ C.ground-nonstar Gᵍ ⦄ ⟩ ∶ p
    → Value M
    → Value N
    → (c : ν ⊢ G ∼ B)
    → B ≢ G
    → (q : A ⊑ᵂ⟨ W ⟩ B)
    → (r : A ⊑ᵂ⟨ W ⟩ G)
    → CatchupCast r N c q
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (N ⟨
                _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
                  ⦃ C.ground-nonstar Gᵍ ⦄
              ⟩ ⟨
                ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄
              ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-project-expand² ecr
      {W = W} {γ = γ} {M = M} {N = N}
      {Gᵍ = Gᵍ} {G∼★ = G∼★} {★∼G = ★∼G}
      {Bns = Bns} {p = p}
      M⊑N! vM vN c B≢G q r generated-c
      with ecr
        (inversion (value→spine vM) vN M⊑N! r)
        vM vN c q generated-c
  ... | Δᴿ′ , χs , Δ′ , W′ , ext , N′ ,
        vN′ , Nc↠N′ , M⊑N′ =
    Δᴿ′ , keep ∷ keep ∷ χs , Δ′ , W′ ,
    keepWorldExtendᴿ (keepWorldExtendᴿ ext) , N′ ,
    vN′ ,
    (N ⟨ tag ⟩ ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄ ⟩
      —→[ keep ]⟨
        pure-step
          (expand ⦃ Gᵍ = Gᵍ ⦄ ⦃ ★∼G = ★∼G ⦄
            ⦃ Bns = Bns ⦄ ⦃ Gns = C.ground-nonstar Gᵍ ⦄
            (vN 《 tag-inert 》) (λ eq → B≢G (sym eq)))
      ⟩
    N ⟨ tag ⟩ ⟨ proj ⟩ ⟨ c ⟩
      —→[ keep ]⟨
        ξ-⟨⟩
          (pure-step
            (tag-untag ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = C.ground-nonstar Gᵍ ⦄
              vN))
          refl
      ⟩
    N ⟨ c ⟩
      —↠[ χs ]⟨ Nc↠N′ ⟩
    N′ ∎[]) ,
    subst≡
      (λ γ′ → W′ ∣ γ′ ⊢² M ⊑ N′ ∶
        WorldExtendᴿ.transport⊑ᵂ ext q)
      (sym (mapCtxᴿ-keep²WorldExtend ext γ))
      M⊑N′
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

  extra-cast-right-id² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → (vM′ : Value M′)
    → (a : Atom B)
    → (q : A ⊑ᵂ⟨ W ⟩ B)
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ id {μ = ν} a ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-id² M⊑M′ vM vM′ a q =
    id-extra-cast-right² M⊑M′ vM vM′ a q

  extra-cast-right-bot-elim² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ `∀ (＇ Fin.zero)}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → Value M′
    → (q : A ⊑ᵂ⟨ W ⟩ `∀ ★)
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ bot-elim {μ = ν} ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-bot-elim² M⊑M′ vM vM′ q =
    ⊥-elim (Prog.no-bot-value vM′ (CTI2T.target-typing² M⊑M′))

  extra-cast-right-bot-intro² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ `∀ ★}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → Value M′
    → (q : A ⊑ᵂ⟨ W ⟩ `∀ (＇ Fin.zero))
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ bot-intro {μ = ν} ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-bot-intro² {A = ＇ X} M⊑M′ vM vM′ ()
  extra-cast-right-bot-intro² {A = ‵ ι} M⊑M′ vM vM′ ()
  extra-cast-right-bot-intro² {A = ★} M⊑M′ vM vM′ ()
  extra-cast-right-bot-intro² {A = A ⇒ B} M⊑M′ vM vM′ ()
  extra-cast-right-bot-intro² {W = W} {M = M} {A = `∀ A₀}
      M⊑M′ vM vM′ (I.∀⊑∀ qbody) =
    ⊥-elim
      (Prog.no-bot-value vM
        (subst≡ (λ T →
          ⟨ _ , _ , _ ⟩ ⊢ M ⦂ `∀ T)
          (renameᵗ-injective
            (ext-injective (toRenameᵗ-injective (CTI2.ηᴸʷ W)))
            (PI.imprecision-to-fresh qbody))
          (CTI2T.source-typing² M⊑M′)))
  extra-cast-right-bot-intro² {A = `∀ A₀} M⊑M′ vM vM′
      (I.∀⊑ Anv zero∈A qbody) =
    ⊥-elim (PI.imprecision-no-star-to-bot refl qbody zero∈A)

  extra-cast-right-inst² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
      {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → Value M′
    → AllValueView M′
    → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
    → ⦃ Bnv : NonVar B ⦄
    → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
    → (B′≢★ : B′ ≢ ★)
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-inst² M⊑M′ vM vM′ view c′ B′≢★ q =
    inst-catchup M⊑M′ vM vM′ view c′ B′≢★ q

  extra-cast-right-inst-canonical² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
      {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → Value M′
    → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
    → ⦃ Bnv : NonVar B ⦄
    → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
    → (B′≢★ : B′ ≢ ★)
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-inst-canonical² M⊑M′ vM vM′ c′ B′≢★ q =
    extra-cast-right-inst² M⊑M′ vM vM′
      (all-view→all-value-view
        (Prog.canonical-∀ vM′ (CTI2T.target-typing² M⊑M′)))
      c′ B′≢★ q

  extra-cast-right-by-provenance : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B} {c′ : ν ⊢ B ∼ B′}
      {q : A ⊑ᵂ⟨ W ⟩ B′}
    → CatchupCast {W = W} {A = A} p M′ c′ q
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → Value M
    → Value M′
    → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
          × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              WorldExtendᴿ.transport⊑ᵂ ext q))
  extra-cast-right-by-provenance {c′ = c′} {q = q}
      (catchup-inert inert) M⊑M′ vM vM′ =
    extra-cast-right-inert² M⊑M′ vM vM′ c′ inert q
  extra-cast-right-by-provenance {q = q}
      (catchup-id a) M⊑M′ vM vM′ =
    extra-cast-right-id² M⊑M′ vM vM′ a q
  extra-cast-right-by-provenance
      {W = W} {γ = γ} {M = M} {M′ = M′} {q = q}
      (catchup-ground-other {Gᵍ = Gᵍ} {G∼★ = G∼★}
        {Bns = Bns} {c = c} B≢G r generated-c)
      M⊑M′ vM vM′
      with extra-cast-right-by-provenance generated-c M⊑M′ vM vM′
  ... | Δᴿ′ , χs , Δ′ , W′ , ext , N′ ,
        vN′ , M′c↠N′ , M⊑N′ =
    Δᴿ′ , keep ∷ χs , Δ′ , W′ , keepWorldExtendᴿ ext ,
    N′ ⟨ χs ▶ᶜ tag ⟩ ,
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
    N′ ⟨ χs ▶ᶜ tag ⟩ ∎[]) ,
    subst≡
      (λ γ′ → W′ ∣ γ′ ⊢² M ⊑ N′ ⟨ χs ▶ᶜ tag ⟩ ∶
        WorldExtendᴿ.transport⊑ᵂ ext q)
      (sym (mapCtxᴿ-keepWorldExtend ext γ))
      (CTI2.⊑cast² (χs ▶ᶜ tag) M⊑N′
        (WorldExtendᴿ.transport⊑ᵂ ext q))
    where
    tag : _ ⊢ _ ∼ ★
    tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
      ⦃ C.ground-nonstar Gᵍ ⦄

    tag-inert : Inert tag
    tag-inert = inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
      ⦃ Gns = C.ground-nonstar Gᵍ ⦄
  extra-cast-right-by-provenance {q = q}
      (catchup-projection
        (generated-project-same {Gᵍ = Gᵍ} vN))
      M⊑N! vM vN! =
    extra-cast-right-project-same² M⊑N! vM vN q
  extra-cast-right-by-provenance
      {W = W} {γ = γ} {M = M} {q = q}
      (catchup-projection
        (generated-project-expand {Gᵍ = Gᵍ} {G∼★ = G∼★}
          {★∼G = ★∼G} {Bns = Bns} {N = N} {c = c}
          vN B≢G r generated-c))
      M⊑N! vM vN!
      with extra-cast-right-by-provenance generated-c
        (inversion (value→spine vM) vN M⊑N! r)
        vM vN
  ... | Δᴿ′ , χs , Δ′ , W′ , ext , N′ ,
        vN′ , Nc↠N′ , M⊑N′ =
    Δᴿ′ , keep ∷ keep ∷ χs , Δ′ , W′ ,
    keepWorldExtendᴿ (keepWorldExtendᴿ ext) , N′ ,
    vN′ ,
    (N ⟨ tag ⟩ ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄ ⟩
      —→[ keep ]⟨
        pure-step
          (expand ⦃ Gᵍ = Gᵍ ⦄ ⦃ ★∼G = ★∼G ⦄
            ⦃ Bns = Bns ⦄ ⦃ Gns = C.ground-nonstar Gᵍ ⦄
            (vN 《 tag-inert 》) (λ eq → B≢G (sym eq)))
      ⟩
    N ⟨ tag ⟩ ⟨ proj ⟩ ⟨ c ⟩
      —→[ keep ]⟨
        ξ-⟨⟩
          (pure-step
            (tag-untag ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = C.ground-nonstar Gᵍ ⦄
              vN))
          refl
      ⟩
    N ⟨ c ⟩
      —↠[ χs ]⟨ Nc↠N′ ⟩
    N′ ∎[]) ,
    subst≡
      (λ γ′ → W′ ∣ γ′ ⊢² M ⊑ N′ ∶
        WorldExtendᴿ.transport⊑ᵂ ext q)
      (sym (mapCtxᴿ-keep²WorldExtend ext γ))
      M⊑N′
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
  extra-cast-right-by-provenance
      {q = q} catchup-inst M⊑M′ vM vM′ =
    extra-cast-right-inst-canonical² M⊑M′ vM vM′ _ _ q
  extra-cast-right-by-provenance
      {q = q} catchup-bot-elim M⊑M′ vM vM′ =
    extra-cast-right-bot-elim² M⊑M′ vM vM′ q
  extra-cast-right-by-provenance
      {q = q} catchup-bot-intro M⊑M′ vM vM′ =
    extra-cast-right-bot-intro² M⊑M′ vM vM′ q

  extra-cast-right² : ExtraCastRight²
  extra-cast-right² M⊑M′ vM vM′ c′ q generated =
    extra-cast-right-by-provenance generated M⊑M′ vM vM′
