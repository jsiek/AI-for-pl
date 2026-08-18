module proof.DGG.Catchup.TagLayerExtractionProof where

-- File Charter:
--   * Extracts the target injection layer from a whole CTI premise whose
--     target is a canonical `★` value.
--   * Folds through source-only wrappers and records the peeled core relation,
--     tag data, and a replay function for rebuilding the tagged premise from a
--     transformed core.
--   * Does not change the CTI relation or any public fuel surface.

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyCtx; Ground; NonStar; ★)
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; idᵍ; _!)
open import Conversion using (Conv↓)
open import CastTerms using
  (Term; Value; _⊢_⦂_; ⟨_,_,_⟩; _⟨_⟩; Λ_; _《_》; _↑_; _↓_)
open import proof.TypeSafety.Progress using (StarView; sv-tag)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


record TagLayerExtraction {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (M : Term Δᴸ) (M′ : Term Δᴿ) {A : Ty Δᴸ}
    (p★ : A ⊑ᵂ⟨ W ⟩ ★) : Set₁ where
  field
    Δᴸ₀ : TyCtx
    Δ₀ : TyCtx
    W₀ : World Δᴸ₀ Δᴿ Δ₀
    γ₀ : CtxImp W₀
    M₀ : Term Δᴸ₀
    A₀ : Ty Δᴸ₀
    G : Ty Δᴿ
    μ : Env∼ Δᴿ
    Gᵍ : Ground G
    G∼★ : μ ⊢ G ∼★
    Gns : NonStar G
    N : Term Δᴿ
    N-value : Value N
    target-eq : M′ ≡
      N ⟨ _! ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
            (idᵍ {μ = μ} Gᵍ) ⦃ Ans = Gns ⦄ ⟩
    qG : A₀ ⊑ᵂ⟨ W₀ ⟩ G
    core-relation : W₀ ∣ γ₀ ⊢² M₀ ⊑ N ∶ qG
    replay-tag :
      W₀ ∣ γ₀ ⊢² M₀ ⊑ N ∶ qG
      → W ∣ γ ⊢² M ⊑ M′ ∶ p★


extract-tag-layer : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {p★ : A ⊑ᵂ⟨ W ⟩ ★}
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p★)
  → Value M
  → Value M′
  → StarView M′
  → TagLayerExtraction W γ M M′ p★
extract-tag-layer {W = W} {γ = γ}
    (CTI2.⊑cast² c′ rel q) vM vM′
    (sv-tag {μ = μ} {W = N} {G = G} {Gᵍ = Gᵍ}
      ⦃ G∼★ = G∼★ ⦄ ⦃ Gns = Gns ⦄ vN refl) =
  record
    { Δᴸ₀ = _
    ; Δ₀ = _
    ; W₀ = W
    ; γ₀ = γ
    ; M₀ = _
    ; A₀ = _
    ; G = G
    ; μ = μ
    ; Gᵍ = Gᵍ
    ; G∼★ = G∼★
    ; Gns = Gns
    ; N = N
    ; N-value = vN
    ; target-eq = refl
    ; qG = _
    ; core-relation = rel
    ; replay-tag = λ rel′ →
        CTI2.⊑cast²
          (_! ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
            (idᵍ {μ = μ} Gᵍ) ⦃ Ans = Gns ⦄)
          rel′ q
    }
extract-tag-layer {W = W} {γ = γ}
    (CTI2.cast⊑cast² c c′ rel q) (vM 《 inert 》) vM′
    (sv-tag {μ = μ} {W = N} {G = G} {Gᵍ = Gᵍ}
      ⦃ G∼★ = G∼★ ⦄ ⦃ Gns = Gns ⦄ vN refl) =
  record
    { Δᴸ₀ = _
    ; Δ₀ = _
    ; W₀ = W
    ; γ₀ = γ
    ; M₀ = _
    ; A₀ = _
    ; G = G
    ; μ = μ
    ; Gᵍ = Gᵍ
    ; G∼★ = G∼★
    ; Gns = Gns
    ; N = N
    ; N-value = vN
    ; target-eq = refl
    ; qG = _
    ; core-relation = rel
    ; replay-tag = λ rel′ →
        CTI2.cast⊑cast² c
          (_! ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
            (idᵍ {μ = μ} Gᵍ) ⦃ Ans = Gns ⦄)
          rel′ q
    }
extract-tag-layer (CTI2.cast⊑² c rel q) (vM 《 inert 》) vM′ view
    with extract-tag-layer rel vM vM′ view
extract-tag-layer (CTI2.cast⊑² c rel q) (vM 《 inert 》) vM′ view
    | child = record
  { Δᴸ₀ = TagLayerExtraction.Δᴸ₀ child
  ; Δ₀ = TagLayerExtraction.Δ₀ child
  ; W₀ = TagLayerExtraction.W₀ child
  ; γ₀ = TagLayerExtraction.γ₀ child
  ; M₀ = TagLayerExtraction.M₀ child
  ; A₀ = TagLayerExtraction.A₀ child
  ; G = TagLayerExtraction.G child
  ; μ = TagLayerExtraction.μ child
  ; Gᵍ = TagLayerExtraction.Gᵍ child
  ; G∼★ = TagLayerExtraction.G∼★ child
  ; Gns = TagLayerExtraction.Gns child
  ; N = TagLayerExtraction.N child
  ; N-value = TagLayerExtraction.N-value child
  ; target-eq = TagLayerExtraction.target-eq child
  ; qG = TagLayerExtraction.qG child
  ; core-relation = TagLayerExtraction.core-relation child
  ; replay-tag = λ rel′ →
      CTI2.cast⊑² c (TagLayerExtraction.replay-tag child rel′) q
  }
extract-tag-layer (CTI2.Λ⊑² Anv z∈A liftγ vV M′⊢ rel q)
    (Λ vM) vM′ view
    with extract-tag-layer rel vV vM′ view
extract-tag-layer (CTI2.Λ⊑² Anv z∈A liftγ vV M′⊢ rel q)
    (Λ vM) vM′ view
    | child = record
  { Δᴸ₀ = TagLayerExtraction.Δᴸ₀ child
  ; Δ₀ = TagLayerExtraction.Δ₀ child
  ; W₀ = TagLayerExtraction.W₀ child
  ; γ₀ = TagLayerExtraction.γ₀ child
  ; M₀ = TagLayerExtraction.M₀ child
  ; A₀ = TagLayerExtraction.A₀ child
  ; G = TagLayerExtraction.G child
  ; μ = TagLayerExtraction.μ child
  ; Gᵍ = TagLayerExtraction.Gᵍ child
  ; G∼★ = TagLayerExtraction.G∼★ child
  ; Gns = TagLayerExtraction.Gns child
  ; N = TagLayerExtraction.N child
  ; N-value = TagLayerExtraction.N-value child
  ; target-eq = TagLayerExtraction.target-eq child
  ; qG = TagLayerExtraction.qG child
  ; core-relation = TagLayerExtraction.core-relation child
  ; replay-tag = λ rel′ →
      CTI2.Λ⊑² Anv z∈A liftγ vV M′⊢
        (TagLayerExtraction.replay-tag child rel′) q
  }
extract-tag-layer
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M′⊢ rel q)
    (Λ vM) vM′ view
    with extract-tag-layer rel vV vM′ view
extract-tag-layer
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M′⊢ rel q)
    (Λ vM) vM′ view
    | child = record
  { Δᴸ₀ = TagLayerExtraction.Δᴸ₀ child
  ; Δ₀ = TagLayerExtraction.Δ₀ child
  ; W₀ = TagLayerExtraction.W₀ child
  ; γ₀ = TagLayerExtraction.γ₀ child
  ; M₀ = TagLayerExtraction.M₀ child
  ; A₀ = TagLayerExtraction.A₀ child
  ; G = TagLayerExtraction.G child
  ; μ = TagLayerExtraction.μ child
  ; Gᵍ = TagLayerExtraction.Gᵍ child
  ; G∼★ = TagLayerExtraction.G∼★ child
  ; Gns = TagLayerExtraction.Gns child
  ; N = TagLayerExtraction.N child
  ; N-value = TagLayerExtraction.N-value child
  ; target-eq = TagLayerExtraction.target-eq child
  ; qG = TagLayerExtraction.qG child
  ; core-relation = TagLayerExtraction.core-relation child
  ; replay-tag = λ rel′ →
      CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M′⊢
        (TagLayerExtraction.replay-tag child rel′) q
  }
extract-tag-layer (CTI2.reveal⊑² mono rb sameγ c⊢ rel q)
    (vM ↑ rv) vM′ view
    with extract-tag-layer rel vM vM′ view
extract-tag-layer (CTI2.reveal⊑² mono rb sameγ c⊢ rel q)
    (vM ↑ rv) vM′ view
    | child = record
  { Δᴸ₀ = TagLayerExtraction.Δᴸ₀ child
  ; Δ₀ = TagLayerExtraction.Δ₀ child
  ; W₀ = TagLayerExtraction.W₀ child
  ; γ₀ = TagLayerExtraction.γ₀ child
  ; M₀ = TagLayerExtraction.M₀ child
  ; A₀ = TagLayerExtraction.A₀ child
  ; G = TagLayerExtraction.G child
  ; μ = TagLayerExtraction.μ child
  ; Gᵍ = TagLayerExtraction.Gᵍ child
  ; G∼★ = TagLayerExtraction.G∼★ child
  ; Gns = TagLayerExtraction.Gns child
  ; N = TagLayerExtraction.N child
  ; N-value = TagLayerExtraction.N-value child
  ; target-eq = TagLayerExtraction.target-eq child
  ; qG = TagLayerExtraction.qG child
  ; core-relation = TagLayerExtraction.core-relation child
  ; replay-tag = λ rel′ →
      CTI2.reveal⊑² mono rb sameγ c⊢
        (TagLayerExtraction.replay-tag child rel′) q
  }
extract-tag-layer
    (CTI2.conceal⊑²-seal-star-open no-target mono rb sameγ c⊢ rel q)
    (vM ↓ cv) vM′ view
    with extract-tag-layer rel vM vM′ view
extract-tag-layer
    (CTI2.conceal⊑²-seal-star-open no-target mono rb sameγ c⊢ rel q)
    (vM ↓ cv) vM′ view
    | child = record
  { Δᴸ₀ = TagLayerExtraction.Δᴸ₀ child
  ; Δ₀ = TagLayerExtraction.Δ₀ child
  ; W₀ = TagLayerExtraction.W₀ child
  ; γ₀ = TagLayerExtraction.γ₀ child
  ; M₀ = TagLayerExtraction.M₀ child
  ; A₀ = TagLayerExtraction.A₀ child
  ; G = TagLayerExtraction.G child
  ; μ = TagLayerExtraction.μ child
  ; Gᵍ = TagLayerExtraction.Gᵍ child
  ; G∼★ = TagLayerExtraction.G∼★ child
  ; Gns = TagLayerExtraction.Gns child
  ; N = TagLayerExtraction.N child
  ; N-value = TagLayerExtraction.N-value child
  ; target-eq = TagLayerExtraction.target-eq child
  ; qG = TagLayerExtraction.qG child
  ; core-relation = TagLayerExtraction.core-relation child
  ; replay-tag = λ rel′ →
      CTI2.conceal⊑²-seal-star-open no-target mono rb sameγ c⊢
        (TagLayerExtraction.replay-tag child rel′) q
  }
extract-tag-layer
    (CTI2.conceal⊑²-source-ok ok mono rb sameγ c⊢ rel q)
    (vM ↓ cv) vM′ view
    with extract-tag-layer rel vM vM′ view
extract-tag-layer
    (CTI2.conceal⊑²-source-ok ok mono rb sameγ c⊢ rel q)
    (vM ↓ cv) vM′ view
    | child = record
  { Δᴸ₀ = TagLayerExtraction.Δᴸ₀ child
  ; Δ₀ = TagLayerExtraction.Δ₀ child
  ; W₀ = TagLayerExtraction.W₀ child
  ; γ₀ = TagLayerExtraction.γ₀ child
  ; M₀ = TagLayerExtraction.M₀ child
  ; A₀ = TagLayerExtraction.A₀ child
  ; G = TagLayerExtraction.G child
  ; μ = TagLayerExtraction.μ child
  ; Gᵍ = TagLayerExtraction.Gᵍ child
  ; G∼★ = TagLayerExtraction.G∼★ child
  ; Gns = TagLayerExtraction.Gns child
  ; N = TagLayerExtraction.N child
  ; N-value = TagLayerExtraction.N-value child
  ; target-eq = TagLayerExtraction.target-eq child
  ; qG = TagLayerExtraction.qG child
  ; core-relation = TagLayerExtraction.core-relation child
  ; replay-tag = λ rel′ →
      CTI2.conceal⊑²-source-ok ok mono rb sameγ c⊢
        (TagLayerExtraction.replay-tag child rel′) q
  }
extract-tag-layer (CTI2.blame⊑² M′⊢ p) () vM′ view
