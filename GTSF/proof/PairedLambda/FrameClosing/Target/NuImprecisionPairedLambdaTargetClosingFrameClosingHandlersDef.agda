module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  where

-- File Charter:
--   * Defines the post-bullet target-closing motive for one proof-relevant
--     paired-lambda frame spine.
--   * Defines the fifteen genuinely semantic handlers: six terminal
--     leaves, the recursive source-gen frame, four source-all frames, paired
--     conversion, paired widening, and the two quotient frames.
--   * Gives every non-leaf handler both the recursive motive and the exact
--     inner proof-relevant frame view.
--   * Leaves prefix extension, reflexivity, and target-only frames to the
--     administrative interpreter.
--   * In the motive, c is the body of the source universal coercion consumed
--     after the bullet, while c′ is the whole target coercion.
--   * Exposes the fused instantiation-beta leaf as an exact semantic
--     capability; it does not assume an implementation.
--   * Contains no interpreter, implementation, postulate, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; _!
  ; genᵈ
  ; id-onlyᵈ
  ; inst
  ; tag-or-idᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
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
open import Imprecision using (NonVar; ⇑ᴿᵢ)
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
  ; LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  ; store-right
  )
open import NuStore using (StoreWf)
open import NuTerms using
  ( Closedᵐ
  ; No•
  ; Term
  ; Value
  ; Λ_
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  ; renameᵗᵐ
  )
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  ( PairedConversion
  ; QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Ground
  ; Renameᵗ
  ; Ty
  ; TyCtx
  ; TyVar
  ; WfTy
  ; wf★
  ; ★
  ; `∀
  ; extᵗ
  ; occurs
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


PairedLambdaTargetClosingFrameClosingMotive :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} →
  ( ρ₀ : StoreImp Φ Δᴸ Δᴿ) →
  (W W′ : Term) → (F B′ : Ty) →
  (s : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ) → Set₁
PairedLambdaTargetClosingFrameClosingMotive
    {Φ} {Δᴸ} {Δᴿ} ρ₀ W W′ F B′ s =
  ∀ {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {A C′ D E : Ty} {c c′ t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion (C.extᵈ μ) (suc (suc Δᴸ))
    (⟰ᵗ (leftStoreⁱ
      (store-left zero (⇑ᵗ A) h⇑A ∷ ρν)))
    (suc zero) (⇑ᵗ (⇑ᵗ A)) t E
    (renameᵗ (extᵗ suc) D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ F} {B′} {`∀ (`∀ E)} {`∀ C′} s (∀ⁱ q) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρν ∣ []
    ⊢ᴺ (((⇑ᵗᵐ W) •) ⟨ c ⟩) ⟨ C.`∀ t ⟩
      ⊑ W′ ⟨ c′ ⟩
      ⦂ ⇑ᵗ (`∀ D) ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ p


record PairedLambdaTargetClosingFrameClosingHandlers : Set₁ where
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
      PairedLambdaTargetClosingFrameClosingMotive ρ
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
      {{safe : NonVar A}} →
      (occ : occurs zero A ≡ true) →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] γ′ →
      Value V → No• V →
      Value N′ → No• N′ →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (Λ V) N′ A B (ν safe occ p)

    handle-leaf-instβ :
        ∀ {Φ Φ₀ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
          {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
            (suc Θᴸ) (suc Θᴿ)}
          {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
          {τ σ : Renameᵗ}
          {W W′ M M′ : Term}
          {A′ B C D F : Ty}
          {s : Coercion} {μ : ModeEnv} {r} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      μ ∣ Θᴿ ∣ rightStoreⁱ ρ₀
        ⊢ inst B s ∶ `∀ C ⊑ B →
      LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀) ρ₀ ρ∀ →
      LiftRightStoreⁱ (⇑ᴿᵢ Φ₀) ρ⁺ ρᴿ⁺ →
      Value W →
      No• W →
      Value W′ →
      No• W′ →
      Inert s →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
        ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
        ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ r →
      (f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ) →
      (assm :
        ∀ {a} → a ∈ ⇑ᴿᵢ Φ₀ →
          rename-assm²ᵢ τ σ a ∈ Φ) →
      (hτ : TyRenameWf Θᴸ Δᴸ τ) →
      (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ) →
      RelStoreEmbeddingⁱ τ σ
        (store-right zero ★ wf★ ∷ ρᴿ⁺) ρ →
      renameᵗᵐ τ (Λ W) ≡ M →
      renameᵗᵐ σ (W′ ⟨ s ⟩) ≡ M′ →
      renameᵗ τ (`∀ D) ≡ `∀ F →
      renameᵗ σ (⇑ᵗ B) ≡ A′ →
      (p : Φ ∣ Δᴸ ⊢ `∀ F ⊑ A′ ⊣ Δᴿ) →
      Value M →
      No• M →
      Closedᵐ M →
      Value M′ →
      No• M′ →
      Closedᵐ M′ →
      Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ `∀ F →
      Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ A′ →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        M M′ F A′ p

    handle-leaf-gen-ν :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {V N′ : Term} {A B B′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
          {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
            ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} →
      {{safe : NonVar B}} →
      Value V → No• V →
      Value N′ → No• N′ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      (hA : WfTy Δᴸ A) →
      (occ : occurs zero B ≡ true) →
      genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ c ∶ ⇑ᵗ A =⇒ B →
      NW.GenSafe c →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B′ ∶ q →
      (occ-r : occurs zero B ≡ true) →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (V ⟨ C.gen A c ⟩) N′ B B′ (ν safe occ-r r)

    handle-leaf-gen-ground :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {V W : Term} {A B H : Ty}
          {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.gen A c ∶ A ⊒ `∀ B →
      Ground H →
      Value V → No• V →
      Value W → No• W →
      Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ W ⦂ H →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ W ⟨ H ! ⟩ ⦂ A ⊑ ★ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ H ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (V ⟨ C.gen A c ⟩) W B H q

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
      PairedLambdaTargetClosingFrameClosingMotive ρ
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
      PairedLambdaTargetClosingFrameClosingMotive ρ
        V N′ F (`∀ B′) q →
      PairedLambdaTargetClosingFrameView ρ
        V N′ (`∀ F) (`∀ B′) q →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      (hA : WfTy Δᴸ (`∀ F)) →
      (occ : occurs zero B ≡ true) →
      genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ c ∶ ⇑ᵗ (`∀ F) =⇒ B →
      NW.GenSafe c →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (V ⟨ C.gen (`∀ F) c ⟩) N′ B (`∀ B′) (∀ⁱ r)

    handle-frame-cast⊒⊑ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.`∀ c ∶ `∀ B ⊒ `∀ C →
      (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (W ⟨ C.`∀ c ⟩) W′ C B′ r

    handle-frame-cast⊑⊑ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ
        ⊢ C.`∀ c ∶ `∀ B ⊑ `∀ C →
      (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (W ⟨ C.`∀ c ⟩) W′ C B′ r

    handle-frame-conv↑⊑ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ X : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} {α : TyVar} →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ)
        α X (C.`∀ c) (`∀ B) (`∀ C) →
      (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (W ⟨ C.`∀ c ⟩) W′ C B′ r

    handle-frame-conv↓⊑ :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ X : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {c : Coercion} {μ : ModeEnv} {α : TyVar} →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ)
        α X (C.`∀ c) (`∀ B) (`∀ C) →
      (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (W ⟨ C.`∀ c ⟩) W′ C B′ r

    handle-frame-paired-conversion :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ C′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
          {c c′ : Coercion} →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        W W′ B B′ q →
      PairedLambdaTargetClosingFrameView ρ
        W W′ (`∀ B) B′ q →
      Inert c′ →
      PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′ q r →
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) C C′ r

    handle-frame-paired-widening :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {W W′ : Term} {B C B′ C′ : Ty}
          {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
          {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
          {c c′ : Coercion} {μ μ′ : ModeEnv} →
      PairedLambdaTargetClosingFrameClosingMotive ρ
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
      PairedLambdaTargetClosingFrameClosingMotive ρ
        (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) C C′ r

    handle-frame-up-id :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {M M′ : Term} {C C′ D D′ B B′ : Ty}
          {pC : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
          {d d′ u u′ : Coercion} →
      PairedLambdaTargetClosingFrameClosingMotive ρ
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
      PairedLambdaTargetClosingFrameClosingMotive ρ
        ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
        ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) B B′ q

    handle-frame-up-gen-all :
        ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
          {ρ : StoreImp Φ Δᴸ Δᴿ}
          {M M′ : Term} {C C′ D D′ B B′ : Ty}
          {pC : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
          {d d′ u u′ : Coercion} →
      PairedLambdaTargetClosingFrameClosingMotive ρ
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
      PairedLambdaTargetClosingFrameClosingMotive ρ
        ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
        ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) B B′ q

open PairedLambdaTargetClosingFrameClosingHandlers public
