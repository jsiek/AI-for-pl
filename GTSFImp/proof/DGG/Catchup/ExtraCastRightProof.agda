module proof.DGG.Catchup.ExtraCastRightProof where

-- File Charter:
--   * Higher-order M4 workers for `ExtraCastRight²`.
--   * The module is parameterized by the M3 right-injection inversion
--     statement and the M5 inst-catch-up statement, so it does not import
--     either proof implementation.
--   * This file is intentionally limited to total case-family workers while
--     the consuming projection families are being closed.

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≢_; sym)
  renaming (subst to subst≡)

open import Types
import Consistency as C
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; idᵍ; _↦_; ∀ᶜ_;
   _!; ？_; gen_; inst_; extᵐ; genᵐ; instᵐ)
import CastTerms
open import CastTerms using
  (Term; Value; Inert; GenSafe; ƛ_; Λ_; $; inj; fun; all; seal;
   genᵥ; _⟨_⟩; _《_》; _↑_; _↓_)
open import Reduction
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.ExtraCastRight2 using
  (ExtraCastRight²; InstCatchupRight²; WorldExtendᴿ; mapCtxᴿ;
   mapCtxᴿ-keep; sameWorldKeepExtendᴿ; inert-extra-cast-right²;
   id-extra-cast-right²)
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
open import proof.DGG.Inversion.SpineValueDef using
  (AllValueView; SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
   sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all)
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

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
