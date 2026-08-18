module proof.DGG.SimBackProof where

-- File Charter:
--   * Gives a parameterized top-down case skeleton for SimBackᵀ.
--   * Proves structural backward simulation cases whose target step occurs in
--     an immediate premise under ordinary application, cast, or primitive
--     frames.
--   * Leaves value-closing, target-boundary, and other blocked case families
--     behind an explicit residual simulation parameter documented in notes.

open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Empty using (⊥)
import Data.List as List
import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyCtx; Atom; Ground; NonStar; NonVar; _⇒_; ★; `∀; _[_]ᵗ;
   _∈ᵗ_; ⇑ᵗ; renameᵗ)
open import Consistency using
  ( Env∼
  ; flipᵐ
  ; extᵐ
  ; instᵐ
  ; genᵐ
  ; _⊢_∼_
  ; _⊢_∼★
  ; _⊢★∼_
  ; _[_]ᶜ
  )
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import Primitives using (Prim; primArgTy; primResultTy; δ)
open import CastTerms
open import Reduction
open import Imprecision using (⇒⊑⇒)
open import proof.Reduction using
  ( applyTy-⇒
  ; applyTy-∀
  ; applyBodies
  ; applyTys-⇒
  ; applyTys-∀
  ; applyTys-open
  ; applyTys-primArgTy
  ; applyTys-primResultTy
  ; appL-↠
  ; cast-↠
  ; primL-↠
  ; typeApp-↠
  )
import proof.Imprecision as PI
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using
    ( ParkedWorld
    ; ParkedEvolve
    ; evolve-refl
    ; evolve-keepᴿ
    ; evolve-right-bind
    )
open import proof.DGG.Parked.ParkedWorldLemma using (transport⊑ᴾ)
open import proof.DGG.SimBackDef using (SimBackᵀ)
open import proof.DGG.TransportTermImprecisionDef
  using (TransportTermImprecisionᴾᵀ)
open import proof.TypeSafety.Preservation using (apply-open; preservation)

------------------------------------------------------------------------
-- Narrow residual-family classifiers
------------------------------------------------------------------------

ApplicationRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² L · M ⊑ L′ · M′ ∶ p → Set
ApplicationRel (·⊑·² _ _) = ⊤
ApplicationRel _ = ⊥

PairedTypeApplicationRel : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {C : Ty (Nat.suc Δᴸ)} {C′ : Ty (Nat.suc Δᴿ)}
    {A : Ty Δᴸ} {A′ : Ty Δᴿ}
    {p : C [ A ]ᵗ ⊑ᵂ⟨ W ⟩ C′ [ A′ ]ᵗ}
  → W ∣ List.[] ⊢²
      M ⦂∀ C [ A ] ⊑ M′ ⦂∀ C′ [ A′ ] ∶ p → Set
PairedTypeApplicationRel (•⊑•² _ _ _ _) = ⊤
PairedTypeApplicationRel _ = ⊥

SourceTypeApplicationRel : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
    {B : Ty Δᴿ} {p : C [ A ]ᵗ ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² M ⦂∀ C [ A ] ⊑ M′ ∶ p → Set
SourceTypeApplicationRel (•⊑² _ _ _ _) = ⊤
SourceTypeApplicationRel _ = ⊥

PairedCastRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p → Set
PairedCastRel (cast⊑cast² _ _ _ _) = ⊤
PairedCastRel _ = ⊥

TargetCastRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p → Set
TargetCastRel (⊑cast² _ _ _) = ⊤
TargetCastRel _ = ⊥

TargetRevealRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p → Set
TargetRevealRel (⊑reveal² _ _ _ _ _ _) = ⊤
TargetRevealRel (reveal⊑reveal² _ _ _ _ _ _ _) = ⊤
TargetRevealRel _ = ⊥

TargetConcealRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p → Set
TargetConcealRel (⊑conceal² _ _ _ _ _ _) = ⊤
TargetConcealRel (conceal⊑conceal² _ _ _ _ _ _ _ _) = ⊤
TargetConcealRel (packaged-seal-star² _ _ _ _ _ _ _ _ _) = ⊤
TargetConcealRel _ = ⊥

SourceRevealRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p → Set
SourceRevealRel (reveal⊑² _ _ _ _ _ _) = ⊤
SourceRevealRel _ = ⊥

SourceConcealRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² M ⊑ M′ ∶ p → Set
SourceConcealRel (conceal⊑² _ _ _ _ _ _ _) = ⊤
SourceConcealRel (conceal⊑²-seal-star-open _ _ _ _ _ _ _) = ⊤
SourceConcealRel (conceal⊑²-source-ok _ _ _ _ _ _ _) = ⊤
SourceConcealRel _ = ⊥

PrimitiveRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {op : Prim}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′ ∶ p
  → Set
PrimitiveRel (⊕⊑⊕² _ _ _ _) = ⊤
PrimitiveRel _ = ⊥

PlainSourceLambdaRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {V : Term (Nat.suc Δᴸ)} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² Λ V ⊑ M′ ∶ p → Set
PlainSourceLambdaRel (Λ⊑² _ _ _ _ _ _ _) = ⊤
PlainSourceLambdaRel _ = ⊥

SmartSourceLambdaRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {V : Term (Nat.suc Δᴸ)} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ List.[] ⊢² Λ V ⊑ M′ ∶ p → Set
SmartSourceLambdaRel (Λ⊑²-smart-comma _ _ _ _ _ _ _ _) = ⊤
SmartSourceLambdaRel _ = ⊥

ApplicationRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ApplicationRootStep (pure-step (β _)) = ⊤
ApplicationRootStep (pure-step (β-⇒ _ _)) = ⊤
ApplicationRootStep (pure-step (β-reveal-⇒ _ _)) = ⊤
ApplicationRootStep (pure-step (β-conceal-⇒ _ _)) = ⊤
ApplicationRootStep (pure-step blame-·₁) = ⊤
ApplicationRootStep (pure-step (blame-·₂ _)) = ⊤
ApplicationRootStep _ = ⊥

ApplicationRightStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ApplicationRightStep (ξ-·₂ _ _ _) = ⊤
ApplicationRightStep _ = ⊥

TypeApplicationRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
TypeApplicationRootStep (pure-step (β-∀ _ _)) = ⊤
TypeApplicationRootStep (pure-step blame-•) = ⊤
TypeApplicationRootStep (β-Λ _) = ⊤
TypeApplicationRootStep (β-gen _ _ _) = ⊤
TypeApplicationRootStep (β-reveal-∀ _) = ⊤
TypeApplicationRootStep (β-conceal-∀ _) = ⊤
TypeApplicationRootStep _ = ⊥

CastRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
CastRootStep (pure-step (β-id _)) = ⊤
CastRootStep (pure-step (ground _ _)) = ⊤
CastRootStep (pure-step (expand _ _)) = ⊤
CastRootStep (pure-step (tag-untag _)) = ⊤
CastRootStep (pure-step (tag-untag-bad _ _)) = ⊤
CastRootStep (pure-step (blame-bot-intro _)) = ⊤
CastRootStep (pure-step blame-⟨⟩) = ⊤
CastRootStep (β-inst _ _) = ⊤
CastRootStep _ = ⊥

RevealRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
RevealRootStep (pure-step (id-reveal _)) = ⊤
RevealRootStep (pure-step (conceal-reveal _)) = ⊤
RevealRootStep (pure-step blame-reveal) = ⊤
RevealRootStep _ = ⊥

RevealFrameStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
RevealFrameStep (ξ-reveal _ _) = ⊤
RevealFrameStep _ = ⊥

ConcealRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ConcealRootStep (pure-step (id-conceal _)) = ⊤
ConcealRootStep (pure-step blame-conceal) = ⊤
ConcealRootStep _ = ⊥

ConcealFrameStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ConcealFrameStep (ξ-conceal _ _) = ⊤
ConcealFrameStep _ = ⊥

PrimitiveRootStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
PrimitiveRootStep (pure-step (δ-⊕ _)) = ⊤
PrimitiveRootStep (pure-step blame-⊕₁) = ⊤
PrimitiveRootStep (pure-step (blame-⊕₂ _)) = ⊤
PrimitiveRootStep _ = ⊥

PrimitiveRightStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
PrimitiveRightStep (ξ-⊕₂ _ _ _) = ⊤
PrimitiveRightStep _ = ⊥

------------------------------------------------------------------------
-- Narrow residual-family surfaces
------------------------------------------------------------------------

SimBackApplicationRootᵀ : Set
SimBackApplicationRootᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² L · M ⊑ L′ · M′ ∶ p)
  → ApplicationRel rel
  → (step : L′ · M′ —→[ χᴿ ] N′)
  → ApplicationRootStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (L · M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackApplicationRightᵀ : Set
SimBackApplicationRightᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² L · M ⊑ L′ · M′ ∶ p)
  → ApplicationRel rel
  → (step : L′ · M′ —→[ χᴿ ] N′)
  → ApplicationRightStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (L · M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackPairedTypeApplicationRootᵀ : Set
SimBackPairedTypeApplicationRootᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {C : Ty (Nat.suc Δᴸ)} {C′ : Ty (Nat.suc Δᴿ)}
    {A : Ty Δᴸ} {A′ : Ty Δᴿ}
    {p : C [ A ]ᵗ ⊑ᵂ⟨ W ⟩ C′ [ A′ ]ᵗ}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢²
      M ⦂∀ C [ A ] ⊑ M′ ⦂∀ C′ [ A′ ] ∶ p)
  → PairedTypeApplicationRel rel
  → (step : M′ ⦂∀ C′ [ A′ ] —→[ χᴿ ] N′)
  → TypeApplicationRootStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ (C [ A ]ᵗ) ⊑ᵂ⟨ W′ ⟩
        applyTy χᴿ (C′ [ A′ ]ᵗ) ]
      (M ⦂∀ C [ A ] —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackSourceTypeApplicationᵀ : Set
SimBackSourceTypeApplicationᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : C [ A ]ᵗ ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⦂∀ C [ A ] ⊑ M′ ∶ p)
  → SourceTypeApplicationRel rel
  → (step : M′ —→[ χᴿ ] N′)
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ (C [ A ]ᵗ) ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M ⦂∀ C [ A ] —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackPairedCastRootᵀ : Set
SimBackPairedCastRootᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → PairedCastRel rel
  → (step : M′ —→[ χᴿ ] N′)
  → CastRootStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackTargetCastRootᵀ : Set
SimBackTargetCastRootᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → TargetCastRel rel
  → (step : M′ —→[ χᴿ ] N′)
  → CastRootStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackTargetRevealRootᵀ : Set
SimBackTargetRevealRootᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → TargetRevealRel rel
  → (step : M′ —→[ χᴿ ] N′)
  → RevealRootStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackTargetRevealFrameᵀ : Set
SimBackTargetRevealFrameᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → TargetRevealRel rel
  → (step : M′ —→[ χᴿ ] N′)
  → RevealFrameStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackTargetConcealRootᵀ : Set
SimBackTargetConcealRootᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → TargetConcealRel rel
  → (step : M′ —→[ χᴿ ] N′)
  → ConcealRootStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackTargetConcealFrameᵀ : Set
SimBackTargetConcealFrameᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → TargetConcealRel rel
  → (step : M′ —→[ χᴿ ] N′)
  → ConcealFrameStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackSourceRevealBoundaryᵀ : Set
SimBackSourceRevealBoundaryᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → SourceRevealRel rel
  → M′ —→[ χᴿ ] N′
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackSourceConcealBoundaryᵀ : Set
SimBackSourceConcealBoundaryᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² M ⊑ M′ ∶ p)
  → SourceConcealRel rel
  → M′ —→[ χᴿ ] N′
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackPrimitiveRootᵀ : Set
SimBackPrimitiveRootᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {op : Prim}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′ ∶ p)
  → PrimitiveRel rel
  → (step : L′ ⊕[ op ] M′ —→[ χᴿ ] N′)
  → PrimitiveRootStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (L ⊕[ op ] M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackPrimitiveRightᵀ : Set
SimBackPrimitiveRightᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {op : Prim}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′ ∶ p)
  → PrimitiveRel rel
  → (step : L′ ⊕[ op ] M′ —→[ χᴿ ] N′)
  → PrimitiveRightStep step
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (L ⊕[ op ] M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackPlainSourceLambdaᵀ : Set
SimBackPlainSourceLambdaᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {V : Term (Nat.suc Δᴸ)} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² Λ V ⊑ M′ ∶ p)
  → PlainSourceLambdaRel rel
  → M′ —→[ χᴿ ] N′
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (Λ V —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)

SimBackSmartSourceLambdaᵀ : Set
SimBackSmartSourceLambdaᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {V : Term (Nat.suc Δᴸ)} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (rel : W ∣ List.[] ⊢² Λ V ⊑ M′ ∶ p)
  → SmartSourceLambdaRel rel
  → M′ —→[ χᴿ ] N′
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (Λ V —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ []) W W′ ×
      (W′ ∣ List.[] ⊢² N ⊑ N′ ∶ q)


module _
    (sim-back-application-root : SimBackApplicationRootᵀ)
    (sim-back-application-right : SimBackApplicationRightᵀ)
    (sim-back-paired-type-application-root :
      SimBackPairedTypeApplicationRootᵀ)
    (sim-back-source-type-application : SimBackSourceTypeApplicationᵀ)
    (sim-back-paired-cast-root : SimBackPairedCastRootᵀ)
    (sim-back-target-cast-root : SimBackTargetCastRootᵀ)
    (sim-back-target-reveal-root : SimBackTargetRevealRootᵀ)
    (sim-back-target-reveal-frame : SimBackTargetRevealFrameᵀ)
    (sim-back-target-conceal-root : SimBackTargetConcealRootᵀ)
    (sim-back-target-conceal-frame : SimBackTargetConcealFrameᵀ)
    (sim-back-source-reveal-boundary : SimBackSourceRevealBoundaryᵀ)
    (sim-back-source-conceal-boundary : SimBackSourceConcealBoundaryᵀ)
    (sim-back-primitive-root : SimBackPrimitiveRootᵀ)
    (sim-back-primitive-right : SimBackPrimitiveRightᵀ)
    (sim-back-plain-source-lambda : SimBackPlainSourceLambdaᵀ)
    (sim-back-smart-source-lambda : SimBackSmartSourceLambdaᵀ)
    (tr : TransportTermImprecisionᴾᵀ)
  where

  ------------------------------------------------------------------------
  -- Direct backward simulation skeleton
  ------------------------------------------------------------------------

  sim-back : SimBackᵀ

  ------------------------------------------------------------------------
  -- Irreducible target forms
  ------------------------------------------------------------------------

  sim-back parked
      (x⊑x² x) (pure-step ())
  sim-back parked
      (ƛ⊑ƛ² rel) (pure-step ())
  sim-back parked
      (Λ⊑Λ² lift vV vV′ rel q) (pure-step ())
  sim-back parked
      (κ⊑κ² κ p) (pure-step ())

  ------------------------------------------------------------------------
  -- Application squares: target operator step
  ------------------------------------------------------------------------

  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N′} L′→N′ refl)
      with sim-back parked L⊑L′ L′→N′
  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , q ,
        L↠N , evol , N⊑N′
      with subst≡
        (λ S →
          Σ[ r ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (A′ ⇒ B′) ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ r)
        (applyTys-⇒ χsᴸ A B)
        (q , N⊑N′)
  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , q ,
        L↠N , evol , N⊑N′
      | q′ , N⊑N′′
      with subst≡
        (λ T →
          Σ[ r ∈
              (applyTys χsᴸ A ⇒ applyTys χsᴸ B) ⊑ᵂ⟨ W′ ⟩ T ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ r)
        (applyTy-⇒ χ A′ B′)
        (q′ , N⊑N′′)
  sim-back parked
      (·⊑·² {M = M} {M′ = M′}
        {A = A} {A′ = A′} {B = B} {B′ = B′}
        L⊑L′ M⊑M′)
      (ξ-·₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , q ,
        L↠N , evol , N⊑N′
      | q′ , N⊑N′′
      | (⇒⊑⇒ qA qB) , N⊑N′⁺ =
    Δᴸ′ , χsᴸ , N · applyTerms χsᴸ M , Δ′ , W′ , qB ,
    appL-↠ L↠N ,
    evol ,
    ·⊑·² N⊑N′⁺
      (subst≡ (λ r → W′ ∣ List.[] ⊢² _ ⊑ _ ∶ r)
        (PI.⊑-unique _ qA) (tr evol M⊑M′))

  ------------------------------------------------------------------------
  -- Cast squares: target body step
  ------------------------------------------------------------------------

  sim-back parked
      (cast⊑cast² c c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M′→N′ refl)
      with sim-back parked M⊑M′ M′→N′
  sim-back parked
      (cast⊑cast² c c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′ =
    Δᴸ′ , χsᴸ , N ⟨ applyConsistencies χsᴸ c ⟩ ,
    Δ′ , W′ , transport⊑ᴾ evol q ,
    cast-↠ c M↠N ,
    evol ,
    cast⊑cast² (applyConsistencies χsᴸ c)
      (applyConsistency χ c′) N⊑N′ (transport⊑ᴾ evol q)

  sim-back parked
      (⊑cast² c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M′→N′ refl)
      with sim-back parked M⊑M′ M′→N′
  sim-back parked
      (⊑cast² c′ M⊑M′ q)
      (ξ-⟨⟩ {χ = χ} M′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′ =
    Δᴸ′ , χsᴸ , N , Δ′ , W′ , transport⊑ᴾ evol q ,
    M↠N ,
    evol ,
    ⊑cast² (applyConsistency χ c′) N⊑N′ (transport⊑ᴾ evol q)

  sim-back parked
      (cast⊑² c M⊑M′ q) M′→N′
      with sim-back parked M⊑M′ M′→N′
  sim-back parked
      (cast⊑² c M⊑M′ q) M′→N′
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′ =
    Δᴸ′ , χsᴸ , N ⟨ applyConsistencies χsᴸ c ⟩ ,
    Δ′ , W′ , transport⊑ᴾ evol q ,
    cast-↠ c M↠N ,
    evol ,
    cast⊑² (applyConsistencies χsᴸ c)
      N⊑N′ (transport⊑ᴾ evol q)

  ------------------------------------------------------------------------
  -- Primitive-operation squares: target left operand step
  ------------------------------------------------------------------------

  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      with sim-back parked L⊑L′ L′→N′
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (primArgTy op) ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
        (applyTys-primArgTy χsᴸ op)
        (p , N⊑N′)
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      with subst≡
        (λ T →
          Σ[ s ∈ primArgTy op ⊑ᵂ⟨ W′ ⟩ T ]
            W′ ∣ List.[] ⊢² N ⊑ N′ ∶ s)
        (applyTys-primArgTy (χ ∷ []) op)
        (p′ , N⊑N′′)
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      | qL , N⊑N′⁺
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ primArgTy op ]
            W′ ∣ List.[] ⊢²
              applyTerms χsᴸ M ⊑ applyTerm χ M′ ∶ s)
        (applyTys-primArgTy χsᴸ op)
        (subst≡
          (λ T →
            Σ[ s ∈ applyTys χsᴸ (primArgTy op) ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢²
                applyTerms χsᴸ M ⊑ applyTerm χ M′ ∶ s)
          (applyTys-primArgTy (χ ∷ []) op)
          (transport⊑ᴾ evol _ , tr evol M⊑M′))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      | qL , N⊑N′⁺
      | qM , M⊑M′⁺
      with subst≡
        (λ S → S ⊑ᵂ⟨ W′ ⟩ primResultTy op)
        (applyTys-primResultTy χsᴸ op)
        (subst≡
          (λ T → applyTys χsᴸ (primResultTy op) ⊑ᵂ⟨ W′ ⟩ T)
          (applyTys-primResultTy (χ ∷ []) op)
          (transport⊑ᴾ evol r))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      | qL , N⊑N′⁺
      | qM , M⊑M′⁺
      | r′
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (primResultTy op) ]
            W′ ∣ List.[] ⊢²
              N ⊕[ op ] applyTerms χsᴸ M ⊑
              N′ ⊕[ op ] applyTerm χ M′ ∶ s)
        (sym (applyTys-primResultTy χsᴸ op))
        (subst≡
          (λ T →
            Σ[ s ∈ primResultTy op ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢²
                N ⊕[ op ] applyTerms χsᴸ M ⊑
                N′ ⊕[ op ] applyTerm χ M′ ∶ s)
          (sym (applyTys-primResultTy (χ ∷ []) op))
          (r′ , ⊕⊑⊕² op N⊑N′⁺ M⊑M′⁺ r′))
  sim-back parked
      (⊕⊑⊕² op {M = M} {M′ = M′} L⊑L′ M⊑M′ r)
      (ξ-⊕₁ {χ = χ} {L′ = N′} L′→N′ refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        L↠N , evol , N⊑N′
      | p′ , N⊑N′′
      | qL , N⊑N′⁺
      | qM , M⊑M′⁺
      | r′
      | r″ , whole-rel =
    Δᴸ′ , χsᴸ , N ⊕[ op ] applyTerms χsᴸ M ,
    Δ′ , W′ , r″ ,
    primL-↠ L↠N ,
    evol ,
    whole-rel

  ------------------------------------------------------------------------
  -- Residual case families
  ------------------------------------------------------------------------

  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (β vV)) =
    sim-back-application-root parked rel tt step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (β-⇒ vV vW)) =
    sim-back-application-root parked rel tt step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (β-reveal-⇒ vV vW)) =
    sim-back-application-root parked rel tt step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (β-conceal-⇒ vV vW)) =
    sim-back-application-root parked rel tt step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step blame-·₁) =
    sim-back-application-root parked rel tt step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(pure-step (blame-·₂ vV)) =
    sim-back-application-root parked rel tt step tt
  sim-back parked rel@(·⊑·² L⊑L′ M⊑M′)
      step@(ξ-·₂ vV M′→N′ refl) =
    sim-back-application-right parked rel tt step tt

  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(pure-step (β-∀ vV eq)) =
    sim-back-paired-type-application-root parked rel tt step tt
  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(pure-step blame-•) =
    sim-back-paired-type-application-root parked rel tt step tt
  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(β-Λ vV) =
    sim-back-paired-type-application-root parked rel tt step tt
  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(β-gen vV A≢★ safe) =
    sim-back-paired-type-application-root parked rel tt step tt
  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(β-reveal-∀ vV) =
    sim-back-paired-type-application-root parked rel tt step tt
  sim-back parked rel@(•⊑•² p∀ M⊑M′ q r)
      step@(β-conceal-∀ vV) =
    sim-back-paired-type-application-root parked rel tt step tt
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N′} M′→N′ refl refl)
      with sim-back parked M⊑M′ M′→N′
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N′} M′→N′ refl refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′
      rewrite applyTys-∀ χsᴸ C
            | applyTy-∀ χ C′
      with p | N⊑N′
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N′} M′→N′ refl refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
      with subst≡
        (λ S →
          Σ[ s ∈ S ⊑ᵂ⟨ W′ ⟩ applyTy χ (C′ [ A′ ]ᵗ) ]
            W′ ∣ List.[] ⊢²
              N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ⊑
              N′ ⦂∀ applyBody χ C′ [ applyTy χ A′ ]
              ∶ s)
        (sym (applyTys-open χsᴸ C A))
        (subst≡
          (λ T →
            Σ[ s ∈
                (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                  ⊑ᵂ⟨ W′ ⟩ T ]
              W′ ∣ List.[] ⊢²
                N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ⊑
                N′ ⦂∀ applyBody χ C′ [ applyTy χ A′ ]
                ∶ s)
          (sym (apply-open χ C′ A′))
          ( subst≡
              (λ T →
                (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                  ⊑ᵂ⟨ W′ ⟩ T)
              (apply-open χ C′ A′)
              (subst≡
                (λ S →
                  S ⊑ᵂ⟨ W′ ⟩ applyTy χ (C′ [ A′ ]ᵗ))
                (applyTys-open χsᴸ C A)
                (transport⊑ᴾ evol r))
          , •⊑•² p∀⁺ N⊑N′⁺
              (transport⊑ᴾ evol q)
              (subst≡
                (λ T →
                  (applyBodies χsᴸ C [ applyTys χsᴸ A ]ᵗ)
                    ⊑ᵂ⟨ W′ ⟩ T)
                (apply-open χ C′ A′)
                (subst≡
                  (λ S →
                    S ⊑ᵂ⟨ W′ ⟩ applyTy χ (C′ [ A′ ]ᵗ))
                  (applyTys-open χsᴸ C A)
                  (transport⊑ᴾ evol r)))
          ))
  sim-back parked
      (•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ M⊑M′ q r)
      (ξ-• {χ = χ} {M′ = N′} M′→N′ refl refl)
      | Δᴸ′ , χsᴸ , N , Δ′ , W′ , p ,
        M↠N , evol , N⊑N′
      | p∀⁺ | N⊑N′⁺
      | r⁺ , whole-rel =
    Δᴸ′ , χsᴸ ,
    N ⦂∀ applyBodies χsᴸ C [ applyTys χsᴸ A ] ,
    Δ′ , W′ , r⁺ ,
    typeApp-↠ M↠N ,
    evol ,
    whole-rel

  sim-back parked rel@(•⊑² p∀ M⊑M′ q r) step =
    sim-back-source-type-application parked rel tt step

  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (β-id vV)) =
    sim-back-paired-cast-root parked rel tt step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (ground vV A≢G)) =
    sim-back-paired-cast-root parked rel tt step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (expand vV G≢B)) =
    sim-back-paired-cast-root parked rel tt step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (tag-untag vV)) =
    sim-back-paired-cast-root parked rel tt step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (tag-untag-bad vV G≢H)) =
    sim-back-paired-cast-root parked rel tt step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step (blame-bot-intro vV)) =
    sim-back-paired-cast-root parked rel tt step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(pure-step blame-⟨⟩) =
    sim-back-paired-cast-root parked rel tt step tt
  sim-back parked rel@(cast⊑cast² c c′ M⊑M′ q)
      step@(β-inst vV B≢★) =
    sim-back-paired-cast-root parked rel tt step tt

  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (β-id vV)) =
    sim-back-target-cast-root parked rel tt step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (ground vV A≢G)) =
    sim-back-target-cast-root parked rel tt step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (expand vV G≢B)) =
    sim-back-target-cast-root parked rel tt step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (tag-untag vV)) =
    sim-back-target-cast-root parked rel tt step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (tag-untag-bad vV G≢H)) =
    sim-back-target-cast-root parked rel tt step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step (blame-bot-intro vV)) =
    sim-back-target-cast-root parked rel tt step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(pure-step blame-⟨⟩) =
    sim-back-target-cast-root parked rel tt step tt
  sim-back parked rel@(⊑cast² c′ M⊑M′ q)
      step@(β-inst vV B≢★) =
    sim-back-target-cast-root parked rel tt step tt

  sim-back parked rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q)
      step@(pure-step (id-reveal vV)) =
    sim-back-target-reveal-root parked rel tt step tt
  sim-back parked rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q)
      step@(pure-step (conceal-reveal vV)) =
    sim-back-target-reveal-root parked rel tt step tt
  sim-back parked rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q)
      step@(pure-step blame-reveal) =
    sim-back-target-reveal-root parked rel tt step tt
  sim-back parked rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q)
      step@(ξ-reveal M′→N′ refl) =
    sim-back-target-reveal-frame parked rel tt step tt

  sim-back parked rel@(⊑conceal² mono rebase same c′⊢ M⊑M′ q)
      step@(pure-step (id-conceal vV)) =
    sim-back-target-conceal-root parked rel tt step tt
  sim-back parked rel@(⊑conceal² mono rebase same c′⊢ M⊑M′ q)
      step@(pure-step blame-conceal) =
    sim-back-target-conceal-root parked rel tt step tt
  sim-back parked rel@(⊑conceal² mono rebase same c′⊢ M⊑M′ q)
      step@(ξ-conceal M′→N′ refl) =
    sim-back-target-conceal-frame parked rel tt step tt

  sim-back parked rel@(reveal⊑² mono rebase same c⊢ M⊑M′ q) step =
    sim-back-source-reveal-boundary parked rel tt step

  sim-back parked rel@(conceal⊑² partner mono rebase same c⊢ M⊑M′ q)
      step =
    sim-back-source-conceal-boundary parked rel tt step
  sim-back parked
      rel@(conceal⊑²-seal-star-open no-target mono rebase same c⊢ M⊑M′ q)
      step =
    sim-back-source-conceal-boundary parked rel tt step
  sim-back parked
      rel@(conceal⊑²-source-ok ok mono rebase same c⊢ M⊑M′ q) step =
    sim-back-source-conceal-boundary parked rel tt step

  sim-back parked rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(pure-step (id-reveal vV)) =
    sim-back-target-reveal-root parked rel tt step tt
  sim-back parked rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(pure-step (conceal-reveal vV)) =
    sim-back-target-reveal-root parked rel tt step tt
  sim-back parked rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(pure-step blame-reveal) =
    sim-back-target-reveal-root parked rel tt step tt
  sim-back parked rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(ξ-reveal M′→N′ refl) =
    sim-back-target-reveal-frame parked rel tt step tt

  sim-back parked
      rel@(conceal⊑conceal² partner mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(pure-step (id-conceal vV)) =
    sim-back-target-conceal-root parked rel tt step tt
  sim-back parked
      rel@(conceal⊑conceal² partner mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(pure-step blame-conceal) =
    sim-back-target-conceal-root parked rel tt step tt
  sim-back parked
      rel@(conceal⊑conceal² partner mono rebase same c⊢ c′⊢ M⊑M′ q)
      step@(ξ-conceal M′→N′ refl) =
    sim-back-target-conceal-frame parked rel tt step tt

  sim-back parked
      rel@(packaged-seal-star² partner mono rebase same c⊢ c′⊢
        M⊑M′ sealed q)
      step@(pure-step blame-conceal) =
    sim-back-target-conceal-root parked rel tt step tt
  sim-back parked
      rel@(packaged-seal-star² partner mono rebase same c⊢ c′⊢
        M⊑M′ sealed q)
      step@(ξ-conceal M′→N′ refl) =
    sim-back-target-conceal-frame parked rel tt step tt

  sim-back {Δᴸ = Δᴸ} {W = W} {p = p} {χᴿ = keep}
      parked (blame⊑² M′⊢ q) step =
    Δᴸ , [] , blame , _ , W , p ,
    (blame ∎[]) ,
    evolve-keepᴿ evolve-refl ,
    blame⊑² (preservation M′⊢ step) p
  sim-back {Δᴸ = Δᴸ} {W = W} {p = p} {χᴿ = bind B₀}
      parked (blame⊑² M′⊢ q) step =
    Δᴸ , [] , blame , _ , CTI2.rightOnlyWorld W B₀ ,
    transport⊑ᴾ
      (evolve-right-bind {W = W} {B = B₀} evolve-refl) p ,
    (blame ∎[]) ,
    evolve-right-bind {W = W} {B = B₀} evolve-refl ,
    blame⊑² (preservation M′⊢ step)
      (transport⊑ᴾ
        (evolve-right-bind {W = W} {B = B₀} evolve-refl) p)

  sim-back parked rel@(Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q)
      step =
    sim-back-plain-source-lambda parked rel tt step
  sim-back parked
      rel@(Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV M′⊢ V⊑M′ q)
      step =
    sim-back-smart-source-lambda parked rel tt step

  sim-back parked rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r)
      step@(pure-step (δ-⊕ δκ)) =
    sim-back-primitive-root parked rel tt step tt
  sim-back parked rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r)
      step@(pure-step blame-⊕₁) =
    sim-back-primitive-root parked rel tt step tt
  sim-back parked rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r)
      step@(pure-step (blame-⊕₂ vV)) =
    sim-back-primitive-root parked rel tt step tt
  sim-back parked rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r)
      step@(ξ-⊕₂ vV M′→N′ refl) =
    sim-back-primitive-right parked rel tt step tt
