module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationHandlersDef
  where

-- File Charter:
--   * Defines the thirteen semantic handlers for the continuation-indexed
--     paired-lambda target-closing motive.
--   * Preserves the four terminal leaves, the recursive source-gen frame,
--     four source-all frames, paired conversion, paired widening, and the
--     two quotient frames from the frame-closing handler boundary.
--   * Gives every non-leaf handler both the recursive continuation motive
--     and the exact inner proof-relevant frame view.
--   * Contains no continuation interpreter, implementation, postulate, hole,
--     permissive option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; genᵈ
  ; id-onlyᵈ
  ; tag-or-idᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  )
import NarrowWiden as NW
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; Λ_
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  ( PairedConversion
  ; QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; TyVar
  ; WfTy
  ; `∀
  ; occurs
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


record PairedLambdaTargetClosingContinuationHandlers : Set₁ where
  field
    handle-leaf-ΛΛ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
            (suc Δᴸ) (suc Δᴿ)}
          {γ′ : CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
            (suc Δᴸ) (suc Δᴿ)}
          {V V′ : Term} {A B : Ty}
          {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
            ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ} →
      LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
      LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] γ′ →
      Value V → No• V →
      Value V′ → No• V′ →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (Λ V) (Λ V′) A (`∀ B) (∀ⁱ p)

    handle-leaf-Λ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
            (suc Δᴸ) Δᴿ}
          {γ′ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
            (suc Δᴸ) Δᴿ}
          {V N′ : Term} {A B : Ty}
          {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
            ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      (occ : occurs zero A ≡ true) →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] γ′ →
      Value V → No• V →
      Value N′ → No• N′ →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (Λ V) N′ A B (ν occ p)

    handle-leaf-gen-ν :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {V N′ : Term} {A B B′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
          {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
            ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} →
      Value V → No• V →
      Value N′ → No• N′ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      (hA : WfTy Δᴸ A) →
      (occ : occurs zero B ≡ true) →
      genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ c ∶ ⇑ᵗ A =⇒ B →
      NW.Narrowing c →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B′ ∶ q →
      (occ-r : occurs zero B ≡ true) →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (V ⟨ C.gen A c ⟩) N′ B B′ (ν occ-r r)

    handle-leaf-up-gen :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {M M′ : Term} {X C′ D D′ B B′ : Ty}
          {pC : Φ ∣ Δᴸ ⊢ X ⊑ C′ ⊣ Δᴿ}
          {d d′ u u′ : Coercion} →
      Value M → No• M →
      Value M′ → No• M′ →
      Inert d′ → Inert u′ →
      genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.gen X d ∶ X ⊒ `∀ D →
      genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ d′ ∶ C′ ⊒ D′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ X ⊑ C′ ∶ pC →
      (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
      QuotientWideningPair Δᴸ Δᴿ ρ
        (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
      (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        ((M ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩)
        ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) B B′ q

    handle-frame-gen-all :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {V N′ : Term} {F B B′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ `∀ B′ ⊣ Δᴿ}
          {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
            ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ}
          {c : Coercion} {μ : ModeEnv} →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        V N′ F (`∀ B′) q →
      PairedLambdaTargetClosingFrameView ρ
        V N′ (`∀ F) (`∀ B′) q →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      (hA : WfTy Δᴸ (`∀ F)) →
      (occ : occurs zero B ≡ true) →
      genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ c ∶ ⇑ᵗ (`∀ F) =⇒ B →
      NW.Narrowing c →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (V ⟨ C.gen (`∀ F) c ⟩) N′ B (`∀ B′) (∀ⁱ r)

    handle-frame-cast⊒⊑ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.`∀ c ∶ `∀ B ⊒ `∀ C →
      (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (W ⟨ C.`∀ c ⟩) W′ C B′ r

    handle-frame-cast⊑⊑ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.`∀ c ∶ `∀ B ⊑ `∀ C →
      (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (W ⟨ C.`∀ c ⟩) W′ C B′ r

    handle-frame-conv↑⊑ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ X : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} {α : TyVar} →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ)
        α X (C.`∀ c) (`∀ B) (`∀ C) →
      (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (W ⟨ C.`∀ c ⟩) W′ C B′ r

    handle-frame-conv↓⊑ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ X : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} {α : TyVar} →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ)
        α X (C.`∀ c) (`∀ B) (`∀ C) →
      (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (W ⟨ C.`∀ c ⟩) W′ C B′ r

    handle-frame-paired-conversion :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ C′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
          {c c′ : Coercion} →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      Inert c′ →
      PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′ q r →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) C C′ r

    handle-frame-paired-widening :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ C′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
          {c c′ : Coercion} {μ μ′ : ModeEnv} →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      Inert c′ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.`∀ c ∶ `∀ B ⊑ `∀ C →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊑ C′ →
      PairedWideningCompatible Φ Δᴸ Δᴿ
        (C.`∀ c) c′ (`∀ C) B′ →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) C C′ r

    handle-frame-up-id :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {M M′ : Term} {C C′ D D′ B B′ : Ty}
          {pC : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
          {d d′ u u′ : Coercion} →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        M M′ C C′ pC →
      PairedLambdaTargetClosingFrameView ρ
        M M′ (`∀ C) C′ pC →
      Inert d′ → Inert u′ →
      id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.`∀ d ∶ `∀ C ⊒ `∀ D →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ d′ ∶ C′ ⊒ D′ →
      (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
      QuotientWideningPair Δᴸ Δᴿ ρ
        (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
      (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
        ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) B B′ q

    handle-frame-up-gen-all :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {M M′ : Term} {C C′ D D′ B B′ : Ty}
          {pC : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
          {d d′ u u′ : Coercion} →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        M M′ C C′ pC →
      PairedLambdaTargetClosingFrameView ρ
        M M′ (`∀ C) C′ pC →
      Inert d′ → Inert u′ →
      genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.`∀ d ∶ `∀ C ⊒ `∀ D →
      genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ d′ ∶ C′ ⊒ D′ →
      (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
      QuotientWideningPair Δᴸ Δᴿ ρ
        (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
      (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
        ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
        ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) B B′ q

open PairedLambdaTargetClosingContinuationHandlers public
