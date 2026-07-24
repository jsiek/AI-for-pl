module proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewProperties where

-- File Charter:
--   * Proves strict structural projections for paired lambda target-closing
--     frame views.
--   * Reconstructs the exact ordinary QTI relation carried by a view and
--     projects source/target `Value` and `No•` evidence.
--   * Recurses only through the view leaf and frame spine; paired and quotient
--     frames are reconstructed atomically from the evidence stored in the Def.
--   * Contains no classifier, wrapper layer, postulate, hole, or permissive
--     option.

import Coercions as C
open import Coercions using (_!)
open import Data.List using ([])
open import Data.Product using (_,_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_; ∀ⁱ_; ν)
import NarrowWiden as NW
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-Λ
  ; no•-⟨⟩
  ; Λ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; Λ⊑instβᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv⊑convᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; gen⊑groundᵀ
  ; up⊑upᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import Types using (Ty; TyCtx)
open import proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using
  ( PairedLambdaTargetClosingFrameView
  ; PairedLambdaTargetClosingFrames
  ; PairedLambdaTargetClosingLeaf
  ; closing-frame-view
  ; frame-cast⊒⊑
  ; frame-cast⊑⊑
  ; frame-conv⊑conv
  ; frame-conv↑⊑
  ; frame-conv↓⊑
  ; frame-gen-all
  ; frame-prefix
  ; frame-refl
  ; frame-up-gen-all
  ; frame-up-id
  ; frame-⊑cast⊒
  ; frame-⊑cast⊑
  ; frame-⊑cast⊑id
  ; frame-⊑conv↑
  ; frame-⊑conv↓
  ; leaf-gen-ν
  ; leaf-gen-ground
  ; leaf-up-gen
  ; leaf-instβ
  ; leaf-Λ
  ; leaf-ΛΛ
  )


paired-lambda-target-closing-frame-view-leaf-relation :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ : Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingLeaf ρ L L′ A A′ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ [] ⊢ᴺ L ⊑ L′ ⦂ A ⊑ A′ ∶ p
paired-lambda-target-closing-frame-view-leaf-relation
    (leaf-ΛΛ liftρ liftγ vV noV vV′ noV′ V⊑V′) =
  Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′
paired-lambda-target-closing-frame-view-leaf-relation
    (leaf-Λ occ liftρ liftγ vV noV vN′ noN′ V⊑N′) =
  Λ⊑ᵀ occ liftρ liftγ vV V⊑N′
paired-lambda-target-closing-frame-view-leaf-relation
    (leaf-instβ prefix mode seal★ inst⊑ liftρ liftρᴿ
      vW noW vW′ noW′ inert body f assm hτ hσ
      store-emb eqM eqM′ eqA eqA′ p
      vM noM closedM vM′ noM′ closedM′ M⊢ M′⊢) =
  Λ⊑instβᵀ prefix mode seal★ inst⊑ liftρ liftρᴿ
    vW noW vW′ noW′ inert body f assm hτ hσ
    store-emb eqM eqM′ eqA eqA′ p
    vM noM closedM vM′ noM′ closedM′ M⊢ M′⊢
paired-lambda-target-closing-frame-view-leaf-relation
    (leaf-gen-ν vV noV vN′ noN′ mode seal★ hA occ-g c⊢ cⁿ
      V⊑N′ occ-r r) =
  cast⊒⊑ᵀ mode seal★ (C.cast-gen hA occ-g c⊢ , NW.gen cⁿ)
    V⊑N′ (ν _ occ-r r)
paired-lambda-target-closing-frame-view-leaf-relation
    (leaf-gen-ground mode seal★ c⊒ gH
      vV noV vW noW W⊢ V⊑Wtag q) =
  gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q
paired-lambda-target-closing-frame-view-leaf-relation
    (leaf-up-gen vM noM vM′ noM′ inert-d′ inert-u′
      d⊒ d′⊒ M⊑M′ qD widening q) =
  up⊑upᵀ
    (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD)
    widening q


paired-lambda-target-closing-frame-view-frames-relation :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ W W′ : Term} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ [] ⊢ᴺ L ⊑ L′ ⦂ A ⊑ A′ ∶ p →
  PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p ρ W W′ B B′ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ [] ⊢ᴺ W ⊑ W′ ⦂ B ⊑ B′ ∶ q
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    frame-refl =
  L⊑L′
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-prefix frames prefix W⊢ W′⊢) =
  allocation-prefixᵀ prefix
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    W⊢ W′⊢
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-cast⊒⊑ frames mode seal★ c⊒ r) =
  cast⊒⊑ᵀ mode seal★ c⊒
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    r
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-cast⊑⊑ frames mode seal★ c⊑ r) =
  cast⊑⊑ᵀ mode seal★ c⊑
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    r
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-conv↑⊑ frames conv r) =
  conv↑⊑ᵀ conv
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    r
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-conv↓⊑ frames conv r) =
  conv↓⊑ᵀ conv
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    r
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-gen-all frames mode seal★ hA occ c⊢ cⁿ r) =
  cast⊒⊑ᵀ mode seal★ (C.cast-gen hA occ c⊢ , NW.gen cⁿ)
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    (∀ⁱ r)
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-⊑cast⊒ frames inert mode seal★ c⊒ r) =
  ⊑cast⊒ᵀ mode seal★ c⊒
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    r
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-⊑cast⊑ frames inert mode seal★ c⊑ r) =
  ⊑cast⊑ᵀ mode seal★ c⊑
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    r
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-⊑cast⊑id frames inert seal★ c⊑ r) =
  ⊑cast⊑idᵀ seal★ c⊑
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    r
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-⊑conv↑ frames inert conv r) =
  ⊑conv↑ᵀ conv
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    r
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-⊑conv↓ frames inert conv r) =
  ⊑conv↓ᵀ conv
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
    r
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-conv⊑conv frames inert paired) =
  conv⊑convᵀ paired
    (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-up-id frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  up⊑upᵀ
    (down⊑downᵀ d⊒ d′⊒
      (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
      qD)
    widening q
paired-lambda-target-closing-frame-view-frames-relation L⊑L′
    (frame-up-gen-all frames inert-d′ inert-u′ d⊒ d′⊒ qD
      widening q) =
  up⊑upᵀ
    (gen-down⊑gen-downᵀ d⊒ d′⊒
      (paired-lambda-target-closing-frame-view-frames-relation L⊑L′ frames)
      qD)
    widening q


paired-lambda-target-closing-frame-view-relation :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameView ρ W W′ B B′ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ [] ⊢ᴺ W ⊑ W′ ⦂ B ⊑ B′ ∶ q
paired-lambda-target-closing-frame-view-relation
    (closing-frame-view leaf frames) =
  paired-lambda-target-closing-frame-view-frames-relation
    (paired-lambda-target-closing-frame-view-leaf-relation leaf)
    frames


paired-lambda-target-closing-frame-view-leaf-source-value :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ : Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingLeaf ρ L L′ A A′ p →
  Value L
paired-lambda-target-closing-frame-view-leaf-source-value
    (leaf-ΛΛ liftρ liftγ vV noV vV′ noV′ V⊑V′) =
  Λ vV
paired-lambda-target-closing-frame-view-leaf-source-value
    (leaf-Λ occ liftρ liftγ vV noV vN′ noN′ V⊑N′) =
  Λ vV
paired-lambda-target-closing-frame-view-leaf-source-value
    (leaf-instβ prefix mode seal★ inst⊑ liftρ liftρᴿ
      vW noW vW′ noW′ inert body f assm hτ hσ
      store-emb eqM eqM′ eqA eqA′ p
      vM noM closedM vM′ noM′ closedM′ M⊢ M′⊢) =
  vM
paired-lambda-target-closing-frame-view-leaf-source-value
    (leaf-gen-ν {A = A} {c = c}
      vV noV vN′ noN′ mode seal★ hA occ-g c⊢ cⁿ
      V⊑N′ occ-r r) =
  vV ⟨ C.gen A c ⟩
paired-lambda-target-closing-frame-view-leaf-source-value
    (leaf-gen-ground {A = A} {c = c}
      mode seal★ c⊒ gH vV noV vW noW W⊢ V⊑Wtag q) =
  vV ⟨ C.gen A c ⟩
paired-lambda-target-closing-frame-view-leaf-source-value
    (leaf-up-gen {X = X} {d = d} {u = u}
      vM noM vM′ noM′ inert-d′ inert-u′ d⊒ d′⊒
      M⊑M′ qD widening q) =
  (vM ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩


paired-lambda-target-closing-frame-view-frames-source-value :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ W W′ : Term} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  Value L →
  PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p ρ W W′ B B′ q →
  Value W
paired-lambda-target-closing-frame-view-frames-source-value vL
    frame-refl =
  vL
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-prefix frames prefix W⊢ W′⊢) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-cast⊒⊑ {c = c} frames mode seal★ c⊒ r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
    ⟨ C.`∀ c ⟩
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-cast⊑⊑ {c = c} frames mode seal★ c⊑ r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
    ⟨ C.`∀ c ⟩
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-conv↑⊑ {c = c} frames conv r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
    ⟨ C.`∀ c ⟩
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-conv↓⊑ {c = c} frames conv r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
    ⟨ C.`∀ c ⟩
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-gen-all {c = c} frames mode seal★ hA occ c⊢ cⁿ r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
    ⟨ C.gen _ c ⟩
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-⊑cast⊒ frames inert mode seal★ c⊒ r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-⊑cast⊑ frames inert mode seal★ c⊑ r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-⊑cast⊑id frames inert seal★ c⊑ r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-⊑conv↑ frames inert conv r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-⊑conv↓ frames inert conv r) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-conv⊑conv {c = c} frames inert paired) =
  paired-lambda-target-closing-frame-view-frames-source-value vL frames
    ⟨ C.`∀ c ⟩
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-up-id {d = d} {u = u}
      frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  (paired-lambda-target-closing-frame-view-frames-source-value vL frames
    ⟨ C.`∀ d ⟩)
    ⟨ C.`∀ u ⟩
paired-lambda-target-closing-frame-view-frames-source-value vL
    (frame-up-gen-all {d = d} {u = u}
      frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  (paired-lambda-target-closing-frame-view-frames-source-value vL frames
    ⟨ C.`∀ d ⟩)
    ⟨ C.`∀ u ⟩


paired-lambda-target-closing-frame-view-source-value :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameView ρ W W′ B B′ q →
  Value W
paired-lambda-target-closing-frame-view-source-value
    (closing-frame-view leaf frames) =
  paired-lambda-target-closing-frame-view-frames-source-value
    (paired-lambda-target-closing-frame-view-leaf-source-value leaf)
    frames


paired-lambda-target-closing-frame-view-leaf-source-no-bullet :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ : Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingLeaf ρ L L′ A A′ p →
  No• L
paired-lambda-target-closing-frame-view-leaf-source-no-bullet
    (leaf-ΛΛ liftρ liftγ vV noV vV′ noV′ V⊑V′) =
  no•-Λ noV
paired-lambda-target-closing-frame-view-leaf-source-no-bullet
    (leaf-Λ occ liftρ liftγ vV noV vN′ noN′ V⊑N′) =
  no•-Λ noV
paired-lambda-target-closing-frame-view-leaf-source-no-bullet
    (leaf-instβ prefix mode seal★ inst⊑ liftρ liftρᴿ
      vW noW vW′ noW′ inert body f assm hτ hσ
      store-emb eqM eqM′ eqA eqA′ p
      vM noM closedM vM′ noM′ closedM′ M⊢ M′⊢) =
  noM
paired-lambda-target-closing-frame-view-leaf-source-no-bullet
    (leaf-gen-ν vV noV vN′ noN′ mode seal★ hA occ-g c⊢ cⁿ
      V⊑N′ occ-r r) =
  no•-⟨⟩ noV
paired-lambda-target-closing-frame-view-leaf-source-no-bullet
    (leaf-gen-ground mode seal★ c⊒ gH
      vV noV vW noW W⊢ V⊑Wtag q) =
  no•-⟨⟩ noV
paired-lambda-target-closing-frame-view-leaf-source-no-bullet
    (leaf-up-gen vM noM vM′ noM′ inert-d′ inert-u′ d⊒ d′⊒
      M⊑M′ qD widening q) =
  no•-⟨⟩ (no•-⟨⟩ noM)


paired-lambda-target-closing-frame-view-frames-source-no-bullet :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ W W′ : Term} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  No• L →
  PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p ρ W W′ B B′ q →
  No• W
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    frame-refl =
  noL
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-prefix frames prefix W⊢ W′⊢) =
  paired-lambda-target-closing-frame-view-frames-source-no-bullet noL frames
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-cast⊒⊑ frames mode seal★ c⊒ r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-source-no-bullet
      noL frames)
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-cast⊑⊑ frames mode seal★ c⊑ r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-source-no-bullet
      noL frames)
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-conv↑⊑ frames conv r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-source-no-bullet
      noL frames)
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-conv↓⊑ frames conv r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-source-no-bullet
      noL frames)
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-gen-all frames mode seal★ hA occ c⊢ cⁿ r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-source-no-bullet
      noL frames)
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-⊑cast⊒ frames inert mode seal★ c⊒ r) =
  paired-lambda-target-closing-frame-view-frames-source-no-bullet noL frames
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-⊑cast⊑ frames inert mode seal★ c⊑ r) =
  paired-lambda-target-closing-frame-view-frames-source-no-bullet noL frames
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-⊑cast⊑id frames inert seal★ c⊑ r) =
  paired-lambda-target-closing-frame-view-frames-source-no-bullet noL frames
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-⊑conv↑ frames inert conv r) =
  paired-lambda-target-closing-frame-view-frames-source-no-bullet noL frames
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-⊑conv↓ frames inert conv r) =
  paired-lambda-target-closing-frame-view-frames-source-no-bullet noL frames
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-conv⊑conv frames inert paired) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-source-no-bullet
      noL frames)
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-up-id frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  no•-⟨⟩
    (no•-⟨⟩
      (paired-lambda-target-closing-frame-view-frames-source-no-bullet
        noL frames))
paired-lambda-target-closing-frame-view-frames-source-no-bullet noL
    (frame-up-gen-all frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  no•-⟨⟩
    (no•-⟨⟩
      (paired-lambda-target-closing-frame-view-frames-source-no-bullet
        noL frames))


paired-lambda-target-closing-frame-view-source-no-bullet :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameView ρ W W′ B B′ q →
  No• W
paired-lambda-target-closing-frame-view-source-no-bullet
    (closing-frame-view leaf frames) =
  paired-lambda-target-closing-frame-view-frames-source-no-bullet
    (paired-lambda-target-closing-frame-view-leaf-source-no-bullet leaf)
    frames


paired-lambda-target-closing-frame-view-leaf-target-value :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ : Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingLeaf ρ L L′ A A′ p →
  Value L′
paired-lambda-target-closing-frame-view-leaf-target-value
    (leaf-ΛΛ liftρ liftγ vV noV vV′ noV′ V⊑V′) =
  Λ vV′
paired-lambda-target-closing-frame-view-leaf-target-value
    (leaf-Λ occ liftρ liftγ vV noV vN′ noN′ V⊑N′) =
  vN′
paired-lambda-target-closing-frame-view-leaf-target-value
    (leaf-instβ prefix mode seal★ inst⊑ liftρ liftρᴿ
      vW noW vW′ noW′ inert body f assm hτ hσ
      store-emb eqM eqM′ eqA eqA′ p
      vM noM closedM vM′ noM′ closedM′ M⊢ M′⊢) =
  vM′
paired-lambda-target-closing-frame-view-leaf-target-value
    (leaf-gen-ν vV noV vN′ noN′ mode seal★ hA occ-g c⊢ cⁿ
      V⊑N′ occ-r r) =
  vN′
paired-lambda-target-closing-frame-view-leaf-target-value
    (leaf-gen-ground mode seal★ c⊒ gH
      vV noV vW noW W⊢ V⊑Wtag q) =
  vW
paired-lambda-target-closing-frame-view-leaf-target-value
    (leaf-up-gen vM noM vM′ noM′ inert-d′ inert-u′ d⊒ d′⊒
      M⊑M′ qD widening q) =
  (vM′ ⟨ inert-d′ ⟩) ⟨ inert-u′ ⟩


paired-lambda-target-closing-frame-view-frames-target-value :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ W W′ : Term} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  Value L′ →
  PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p ρ W W′ B B′ q →
  Value W′
paired-lambda-target-closing-frame-view-frames-target-value vL′
    frame-refl =
  vL′
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-prefix frames prefix W⊢ W′⊢) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-cast⊒⊑ frames mode seal★ c⊒ r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-cast⊑⊑ frames mode seal★ c⊑ r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-conv↑⊑ frames conv r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-conv↓⊑ frames conv r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-gen-all frames mode seal★ hA occ c⊢ cⁿ r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-⊑cast⊒ frames inert mode seal★ c⊒ r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
    ⟨ inert ⟩
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-⊑cast⊑ frames inert mode seal★ c⊑ r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
    ⟨ inert ⟩
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-⊑cast⊑id frames inert seal★ c⊑ r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
    ⟨ inert ⟩
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-⊑conv↑ frames inert conv r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
    ⟨ inert ⟩
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-⊑conv↓ frames inert conv r) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
    ⟨ inert ⟩
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-conv⊑conv frames inert paired) =
  paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
    ⟨ inert ⟩
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-up-id frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  (paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
    ⟨ inert-d′ ⟩)
    ⟨ inert-u′ ⟩
paired-lambda-target-closing-frame-view-frames-target-value vL′
    (frame-up-gen-all frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  (paired-lambda-target-closing-frame-view-frames-target-value vL′ frames
    ⟨ inert-d′ ⟩)
    ⟨ inert-u′ ⟩


paired-lambda-target-closing-frame-view-target-value :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameView ρ W W′ B B′ q →
  Value W′
paired-lambda-target-closing-frame-view-target-value
    (closing-frame-view leaf frames) =
  paired-lambda-target-closing-frame-view-frames-target-value
    (paired-lambda-target-closing-frame-view-leaf-target-value leaf)
    frames


paired-lambda-target-closing-frame-view-leaf-target-no-bullet :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ : Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingLeaf ρ L L′ A A′ p →
  No• L′
paired-lambda-target-closing-frame-view-leaf-target-no-bullet
    (leaf-ΛΛ liftρ liftγ vV noV vV′ noV′ V⊑V′) =
  no•-Λ noV′
paired-lambda-target-closing-frame-view-leaf-target-no-bullet
    (leaf-Λ occ liftρ liftγ vV noV vN′ noN′ V⊑N′) =
  noN′
paired-lambda-target-closing-frame-view-leaf-target-no-bullet
    (leaf-instβ prefix mode seal★ inst⊑ liftρ liftρᴿ
      vW noW vW′ noW′ inert body f assm hτ hσ
      store-emb eqM eqM′ eqA eqA′ p
      vM noM closedM vM′ noM′ closedM′ M⊢ M′⊢) =
  noM′
paired-lambda-target-closing-frame-view-leaf-target-no-bullet
    (leaf-gen-ν vV noV vN′ noN′ mode seal★ hA occ-g c⊢ cⁿ
      V⊑N′ occ-r r) =
  noN′
paired-lambda-target-closing-frame-view-leaf-target-no-bullet
    (leaf-gen-ground mode seal★ c⊒ gH
      vV noV vW noW W⊢ V⊑Wtag q) =
  noW
paired-lambda-target-closing-frame-view-leaf-target-no-bullet
    (leaf-up-gen vM noM vM′ noM′ inert-d′ inert-u′ d⊒ d′⊒
      M⊑M′ qD widening q) =
  no•-⟨⟩ (no•-⟨⟩ noM′)


paired-lambda-target-closing-frame-view-frames-target-no-bullet :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ W W′ : Term} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  No• L′ →
  PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p ρ W W′ B B′ q →
  No• W′
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    frame-refl =
  noL′
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-prefix frames prefix W⊢ W′⊢) =
  paired-lambda-target-closing-frame-view-frames-target-no-bullet
    noL′ frames
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-cast⊒⊑ frames mode seal★ c⊒ r) =
  paired-lambda-target-closing-frame-view-frames-target-no-bullet
    noL′ frames
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-cast⊑⊑ frames mode seal★ c⊑ r) =
  paired-lambda-target-closing-frame-view-frames-target-no-bullet
    noL′ frames
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-conv↑⊑ frames conv r) =
  paired-lambda-target-closing-frame-view-frames-target-no-bullet
    noL′ frames
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-conv↓⊑ frames conv r) =
  paired-lambda-target-closing-frame-view-frames-target-no-bullet
    noL′ frames
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-gen-all frames mode seal★ hA occ c⊢ cⁿ r) =
  paired-lambda-target-closing-frame-view-frames-target-no-bullet
    noL′ frames
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-⊑cast⊒ frames inert mode seal★ c⊒ r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-target-no-bullet
      noL′ frames)
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-⊑cast⊑ frames inert mode seal★ c⊑ r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-target-no-bullet
      noL′ frames)
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-⊑cast⊑id frames inert seal★ c⊑ r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-target-no-bullet
      noL′ frames)
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-⊑conv↑ frames inert conv r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-target-no-bullet
      noL′ frames)
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-⊑conv↓ frames inert conv r) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-target-no-bullet
      noL′ frames)
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-conv⊑conv frames inert paired) =
  no•-⟨⟩
    (paired-lambda-target-closing-frame-view-frames-target-no-bullet
      noL′ frames)
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-up-id frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  no•-⟨⟩
    (no•-⟨⟩
      (paired-lambda-target-closing-frame-view-frames-target-no-bullet
        noL′ frames))
paired-lambda-target-closing-frame-view-frames-target-no-bullet noL′
    (frame-up-gen-all frames inert-d′ inert-u′ d⊒ d′⊒ qD widening q) =
  no•-⟨⟩
    (no•-⟨⟩
      (paired-lambda-target-closing-frame-view-frames-target-no-bullet
        noL′ frames))


paired-lambda-target-closing-frame-view-target-no-bullet :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameView ρ W W′ B B′ q →
  No• W′
paired-lambda-target-closing-frame-view-target-no-bullet
    (closing-frame-view leaf frames) =
  paired-lambda-target-closing-frame-view-frames-target-no-bullet
    (paired-lambda-target-closing-frame-view-leaf-target-no-bullet leaf)
    frames
