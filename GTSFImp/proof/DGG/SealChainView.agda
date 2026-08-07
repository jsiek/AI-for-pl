module proof.DGG.SealChainView where

-- File Charter:
--   * Reifies chain-ride inputs into an explicit telescope of spine nodes.
--   * Separates pure constructor inventory from the world-moving fold.
--   * Names each moving-premise sub-row carried by source, target, and
--     paired reveal/conceal rules.
--   * Depends only on CastTermImprecision2 and SpineValueDef's SpineValue.

import Data.Nat as Nat
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just)
open import CastTerms using
  (Term; Value; _⊢_⦂_; ⟨_,_,_⟩; `_ ; ƛ_; _·_; Λ_; _⦂∀_[_];
   $; _⟨_⟩; _↑_; _↓_; blame; _⊕[_]_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import Imprecision
open import Types
open import Primitives using (Const; Prim; constTy; primArgTy; primResultTy)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.Inversion.SpineValueDef as SVD
open CTI2 using
  (World; CtxImp; ctx-imp; _∋ʷ_⦂_; LiftCtx; LiftCtxᴸ;
   RebaseAt; RebaseAtᴸ; RebaseAtᴿ; ImpEnvMono; SameCtx;
   _⊑ᵂ⟨_⟩_; _⊢↑[_]_; _⊢↓[_]_; _∣_⊢²_⊑_∶_)
open SVD using (SpineValue)

------------------------------------------------------------------------
-- Reified node inventory
------------------------------------------------------------------------

data ChainNodeKind : Set where
  core-node : ChainNodeKind

  source-cast-node : ChainNodeKind
  target-cast-node : ChainNodeKind
  paired-cast-node : ChainNodeKind
  target-tag-node : ChainNodeKind

  source-reveal-idᴸ-node : ChainNodeKind
  source-reveal-onlyᴸ-node : ChainNodeKind
  source-reveal-varᴸ-node : ChainNodeKind
  source-conceal-idᴸ-node : ChainNodeKind
  source-conceal-onlyᴸ-node : ChainNodeKind
  source-conceal-varᴸ-node : ChainNodeKind

  target-reveal-idᴿ-node : ChainNodeKind
  target-reveal-varᴿ-node : ChainNodeKind
  target-conceal-idᴿ-node : ChainNodeKind
  target-conceal-varᴿ-node : ChainNodeKind

  paired-reveal-node : ChainNodeKind
  paired-conceal-node : ChainNodeKind

  lambda-node : ChainNodeKind
  ty-lambda-node : ChainNodeKind
  app-node : ChainNodeKind
  ty-app-node : ChainNodeKind
  const-node : ChainNodeKind
  prim-node : ChainNodeKind
  var-node : ChainNodeKind
  blame-node : ChainNodeKind

data ChainTelescope : Set where

  tel-x : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {x A B p}
    → (x∈ : γ ∋ʷ x ⦂ ctx-imp A B p)
    → ChainTelescope

  tel-ƛ : ChainTelescope
    → ChainTelescope

  tel-· : ChainTelescope
    → ChainTelescope
    → ChainTelescope

  tel-ΛΛ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W}
      {γ′ : CtxImp (CTI2.liftWorldBoth X⊑X W)}
      {A : Ty (Nat.suc Δᴸ)} {B : Ty (Nat.suc Δᴿ)}
      (liftγ : LiftCtx X⊑X γ γ′)
      {V : Term (Nat.suc Δᴸ)} {V′ : Term (Nat.suc Δᴿ)}
    → (vV : Value V)
    → (vV′ : Value V′)
    → ChainTelescope
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ B)
    → ChainTelescope

  tel-Λ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W}
      {γ′ : CtxImp (CTI2.liftWorldLeft X⊑★ W)}
      {M : Term Δᴿ} {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
      (Anv : NonVar A)
      (zero∈A : Fin.zero ∈ᵗ A)
      (liftγ : LiftCtxᴸ X⊑★ γ γ′)
      {V : Term (Nat.suc Δᴸ)}
      (vV : Value V)
      (M⊢ : ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
        ⊢ M ⦂ B)
    → ChainTelescope
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
    → ChainTelescope

  tel-•• : ChainTelescope
    → ChainTelescope

  tel-• : ChainTelescope
    → ChainTelescope

  tel-κ : (κ : Const)
    → ChainTelescope

  tel-castcast : ChainTelescope
    → ChainTelescope

  tel-⊑cast : ChainTelescope
    → ChainTelescope

  tel-⊑reveal : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
      {Xᴿ? : Maybe (TyVar Δᴿ)}
      {c′ : Conv↑ Δᴿ B B′}
      (mono : ImpEnvMono W W′)
      (rb : RebaseAtᴿ W W′ Xᴿ?)
      (sc : SameCtx γ γ′)
      (c′⊢ : CTI2.targetStoreʷ W ⊢↑[ Xᴿ? ] c′)
    → ChainTelescope
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
    → ChainTelescope

  tel-⊑conceal : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
      {Xᴿ? : Maybe (TyVar Δᴿ)}
      {c′ : Conv↓ Δᴿ B B′}
      (mono : ImpEnvMono W W′)
      (rb : RebaseAtᴿ W′ W Xᴿ?)
      (sc : SameCtx γ γ′)
      (c′⊢ : CTI2.targetStoreʷ W ⊢↓[ Xᴿ? ] c′)
    → ChainTelescope
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
    → ChainTelescope

  tel-cast⊑ : ChainTelescope
    → ChainTelescope

  tel-reveal⊑ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
      {Xᴸ? : Maybe (TyVar Δᴸ)}
      {c : Conv↑ Δᴸ A A′}
      (mono : ImpEnvMono W W′)
      (rb : RebaseAtᴸ W W′ Xᴸ?)
      (sc : SameCtx γ γ′)
      (c⊢ : CTI2.sourceStoreʷ W ⊢↑[ Xᴸ? ] c)
    → ChainTelescope
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
    → ChainTelescope

  tel-conceal⊑ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
      {Xᴸ? : Maybe (TyVar Δᴸ)}
      {c : Conv↓ Δᴸ A A′}
      (mono : ImpEnvMono W W′)
      (rb : RebaseAtᴸ W′ W Xᴸ?)
      (sc : SameCtx γ γ′)
      (c⊢ : CTI2.sourceStoreʷ W ⊢↓[ Xᴸ? ] c)
    → ChainTelescope
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
    → ChainTelescope

  tel-revealreveal : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵖ : CtxImp Wᵖ} {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
      (mono : ImpEnvMono W Wᵖ)
      (rb : RebaseAt W Wᵖ Xᴸ Xᴿ)
      (sc : SameCtx γ γᵖ)
      (c⊢ : CTI2.sourceStoreʷ W ⊢↑[ just Xᴸ ] c)
      (c′⊢ : CTI2.targetStoreʷ W ⊢↑[ just Xᴿ ] c′)
    → ChainTelescope
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → ChainTelescope

  tel-concealconceal : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵖ : CtxImp Wᵖ} {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
      (mono : ImpEnvMono W Wᵖ)
      (rb : RebaseAt Wᵖ W Xᴸ Xᴿ)
      (sc : SameCtx γ γᵖ)
      (c⊢ : CTI2.sourceStoreʷ W ⊢↓[ just Xᴸ ] c)
      (c′⊢ : CTI2.targetStoreʷ W ⊢↓[ just Xᴿ ] c′)
    → ChainTelescope
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → ChainTelescope

  tel-blame : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {M′ A B}
      (M′⊢ : ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
        ⊢ M′ ⦂ B)
      (p : A ⊑ᵂ⟨ W ⟩ B)
    → ChainTelescope

  tel-⊕ : (op : Prim)
    → ChainTelescope
    → ChainTelescope
    → ChainTelescope

data TypedChainTelescope {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    : (M : Term Δᴸ) (N : Term Δᴿ)
    → {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B
    → Set where

  typed-x : ∀ {x A B p}
    → (x∈ : γ ∋ʷ x ⦂ ctx-imp A B p)
    → TypedChainTelescope W γ (` x) (` x) p

  typed-ƛ : ∀ {M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′}
      {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → TypedChainTelescope W (ctx-imp A A′ pA ∷ γ) M M′ pB
    → TypedChainTelescope W γ (ƛ M) (ƛ M′) (⇒⊑⇒ pA pB)

  typed-· : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′}
      {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → TypedChainTelescope W γ L L′ (⇒⊑⇒ pA pB)
    → TypedChainTelescope W γ M M′ pA
    → TypedChainTelescope W γ (L · M) (L′ · M′) pB

  typed-ΛΛ : ∀ {γ′ V V′ A B}
      {p : A ⊑ᵂ⟨ CTI2.liftWorldBoth X⊑X W ⟩ B}
    → (liftγ : LiftCtx X⊑X γ γ′)
    → (vV : Value V)
    → (vV′ : Value V′)
    → TypedChainTelescope (CTI2.liftWorldBoth X⊑X W) γ′ V V′ p
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ B)
    → TypedChainTelescope W γ (Λ V) (Λ V′) q

  typed-Λ : ∀ {γ′ V M A B}
      {p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ B}
    → (Anv : NonVar A)
    → (zero∈A : Fin.zero ∈ᵗ A)
    → (liftγ : LiftCtxᴸ X⊑★ γ γ′)
    → (vV : Value V)
    → (M⊢ : ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
        ⊢ M ⦂ B)
    → TypedChainTelescope (CTI2.liftWorldLeft X⊑★ W) γ′ V M p
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
    → TypedChainTelescope W γ (Λ V) M q

  typed-•• : ∀ {M M′ C C′ A A′}
    → (p∀ : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′)
    → TypedChainTelescope W γ M M′ p∀
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → (r : (C [ A ]ᵗ) ⊑ᵂ⟨ W ⟩ (C′ [ A′ ]ᵗ))
    → TypedChainTelescope W γ
        (M ⦂∀ C [ A ]) (M′ ⦂∀ C′ [ A′ ]) r

  typed-• : ∀ {M M′ C A B}
    → (p∀ : `∀ C ⊑ᵂ⟨ W ⟩ B)
    → TypedChainTelescope W γ M M′ p∀
    → (q : A ⊑ᵂ⟨ W ⟩ ★)
    → (r : (C [ A ]ᵗ) ⊑ᵂ⟨ W ⟩ B)
    → TypedChainTelescope W γ (M ⦂∀ C [ A ]) M′ r

  typed-κ : ∀ (κ : Const)
    → (p : constTy κ ⊑ᵂ⟨ W ⟩ constTy κ)
    → TypedChainTelescope W γ ($ κ) ($ κ) p

  typed-castcast : ∀ {M M′ C C′ A A′}
      {p : C ⊑ᵂ⟨ W ⟩ C′} {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
    → (c : ν ⊢ C ∼ A)
    → (c′ : ν′ ⊢ C′ ∼ A′)
    → TypedChainTelescope W γ M M′ p
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → TypedChainTelescope W γ (M ⟨ c ⟩) (M′ ⟨ c′ ⟩) q

  typed-⊑cast : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴿ}
    → (c′ : ν ⊢ B ∼ B′)
    → TypedChainTelescope W γ M M′ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
    → TypedChainTelescope W γ M (M′ ⟨ c′ ⟩) q

  typed-⊑reveal : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A B B′ Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c′ : Conv↑ Δᴿ B B′}
    → (mono : ImpEnvMono W W′)
    → (rb : RebaseAtᴿ W W′ Xᴿ?)
    → (sc : SameCtx γ γ′)
    → (c′⊢ : CTI2.targetStoreʷ W ⊢↑[ Xᴿ? ] c′)
    → TypedChainTelescope W′ γ′ M M′ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
    → TypedChainTelescope W γ M (M′ ↑ c′) q

  typed-⊑conceal : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A B B′ Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c′ : Conv↓ Δᴿ B B′}
    → (mono : ImpEnvMono W W′)
    → (rb : RebaseAtᴿ W′ W Xᴿ?)
    → (sc : SameCtx γ γ′)
    → (c′⊢ : CTI2.targetStoreʷ W ⊢↓[ Xᴿ? ] c′)
    → TypedChainTelescope W′ γ′ M M′ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
    → TypedChainTelescope W γ M (M′ ↓ c′) q

  typed-cast⊑ : ∀ {M M′ A A′ B}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴸ}
    → (c : ν ⊢ A ∼ A′)
    → TypedChainTelescope W γ M M′ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
    → TypedChainTelescope W γ (M ⟨ c ⟩) M′ q

  typed-reveal⊑ : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↑ Δᴸ A A′}
    → (mono : ImpEnvMono W W′)
    → (rb : RebaseAtᴸ W W′ Xᴸ?)
    → (sc : SameCtx γ γ′)
    → (c⊢ : CTI2.sourceStoreʷ W ⊢↑[ Xᴸ? ] c)
    → TypedChainTelescope W′ γ′ M M′ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
    → TypedChainTelescope W γ (M ↑ c) M′ q

  typed-conceal⊑ : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → (mono : ImpEnvMono W W′)
    → (rb : RebaseAtᴸ W′ W Xᴸ?)
    → (sc : SameCtx γ γ′)
    → (c⊢ : CTI2.sourceStoreʷ W ⊢↓[ Xᴸ? ] c)
    → TypedChainTelescope W′ γ′ M M′ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
    → TypedChainTelescope W γ (M ↓ c) M′ q

  typed-revealreveal : ∀ {Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵖ : CtxImp Wᵖ} {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
    → (mono : ImpEnvMono W Wᵖ)
    → (rb : RebaseAt W Wᵖ Xᴸ Xᴿ)
    → (sc : SameCtx γ γᵖ)
    → (c⊢ : CTI2.sourceStoreʷ W ⊢↑[ just Xᴸ ] c)
    → (c′⊢ : CTI2.targetStoreʷ W ⊢↑[ just Xᴿ ] c′)
    → TypedChainTelescope Wᵖ γᵖ M M′ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → TypedChainTelescope W γ (M ↑ c) (M′ ↑ c′) q

  typed-concealconceal : ∀ {Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵖ : CtxImp Wᵖ} {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
    → (mono : ImpEnvMono W Wᵖ)
    → (rb : RebaseAt Wᵖ W Xᴸ Xᴿ)
    → (sc : SameCtx γ γᵖ)
    → (c⊢ : CTI2.sourceStoreʷ W ⊢↓[ just Xᴸ ] c)
    → (c′⊢ : CTI2.targetStoreʷ W ⊢↓[ just Xᴿ ] c′)
    → TypedChainTelescope Wᵖ γᵖ M M′ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → TypedChainTelescope W γ (M ↓ c) (M′ ↓ c′) q

  typed-blame : ∀ {M′ A B}
    → (M′⊢ : ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
        ⊢ M′ ⦂ B)
    → (p : A ⊑ᵂ⟨ W ⟩ B)
    → TypedChainTelescope W γ blame M′ p

  typed-⊕ : ∀ (op : Prim) {L L′ M M′}
      {p q : primArgTy op ⊑ᵂ⟨ W ⟩ primArgTy op}
    → TypedChainTelescope W γ L L′ p
    → TypedChainTelescope W γ M M′ q
    → (r : primResultTy op ⊑ᵂ⟨ W ⟩ primResultTy op)
    → TypedChainTelescope W γ (L ⊕[ op ] M) (L′ ⊕[ op ] M′) r

record ChainRideReification {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    (sv : SpineValue V)
    (vN : Value N)
    (D : W ∣ γ ⊢² V ⊑ N ∶ p) : Set where
  constructor ride-reified
  field
    typed-telescope : TypedChainTelescope W γ V N p
    telescope : ChainTelescope
    nodes : List ChainNodeKind
    node-count : Nat.ℕ

------------------------------------------------------------------------
-- Total reification
------------------------------------------------------------------------

nodesOf : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → List ChainNodeKind
nodesOf (CTI2.x⊑x² x∈) = var-node ∷ []
nodesOf (CTI2.ƛ⊑ƛ² D) = lambda-node ∷ nodesOf D
nodesOf (CTI2.·⊑·² D₁ D₂) = app-node ∷ (nodesOf D₁ ++ nodesOf D₂)
nodesOf (CTI2.Λ⊑Λ² liftγ vV vV′ D q) =
  ty-lambda-node ∷ nodesOf D
nodesOf (CTI2.Λ⊑² Anv zero∈A liftγ vV M⊢ D q) =
  ty-lambda-node ∷ nodesOf D
nodesOf (CTI2.•⊑•² p∀ D q r) = ty-app-node ∷ nodesOf D
nodesOf (CTI2.•⊑² p∀ D q r) = ty-app-node ∷ nodesOf D
nodesOf (CTI2.κ⊑κ² κ p) = const-node ∷ []
nodesOf (CTI2.cast⊑cast² c c′ D q) =
  paired-cast-node ∷ nodesOf D
nodesOf (CTI2.⊑cast² c′ D q) = target-tag-node ∷ nodesOf D
nodesOf (CTI2.⊑reveal² mono CTI2.rebase-idᴿ sc c′⊢ D q) =
  target-reveal-idᴿ-node ∷ nodesOf D
nodesOf (CTI2.⊑reveal² mono (CTI2.rebase-varᴿ rb) sc c′⊢ D q) =
  target-reveal-varᴿ-node ∷ nodesOf D
nodesOf (CTI2.⊑conceal² mono CTI2.rebase-idᴿ sc c′⊢ D q) =
  target-conceal-idᴿ-node ∷ nodesOf D
nodesOf (CTI2.⊑conceal² mono (CTI2.rebase-varᴿ rb) sc c′⊢ D q) =
  target-conceal-varᴿ-node ∷ nodesOf D
nodesOf (CTI2.cast⊑² c D q) = source-cast-node ∷ nodesOf D
nodesOf (CTI2.reveal⊑² mono CTI2.rebase-idᴸ sc c⊢ D q) =
  source-reveal-idᴸ-node ∷ nodesOf D
nodesOf (CTI2.reveal⊑² mono (CTI2.rebase-varᴸ rb) sc c⊢ D q) =
  source-reveal-varᴸ-node ∷ nodesOf D
nodesOf (CTI2.reveal⊑² mono
    (CTI2.rebase-onlyᴸ mark disaligned represented) sc c⊢ D q) =
  source-reveal-onlyᴸ-node ∷ nodesOf D
nodesOf (CTI2.conceal⊑² mono CTI2.rebase-idᴸ sc c⊢ D q) =
  source-conceal-idᴸ-node ∷ nodesOf D
nodesOf (CTI2.conceal⊑² mono (CTI2.rebase-varᴸ rb) sc c⊢ D q) =
  source-conceal-varᴸ-node ∷ nodesOf D
nodesOf (CTI2.conceal⊑² mono
    (CTI2.rebase-onlyᴸ mark disaligned represented) sc c⊢ D q) =
  source-conceal-onlyᴸ-node ∷ nodesOf D
nodesOf (CTI2.reveal⊑reveal² mono rb sc c⊢ c′⊢ D q) =
  paired-reveal-node ∷ nodesOf D
nodesOf (CTI2.conceal⊑conceal² mono rb sc c⊢ c′⊢ D q) =
  paired-conceal-node ∷ nodesOf D
nodesOf (CTI2.blame⊑² M′⊢ p) = blame-node ∷ []
nodesOf (CTI2.⊕⊑⊕² op D₁ D₂ r) =
  prim-node ∷ (nodesOf D₁ ++ nodesOf D₂)

telescopeOf : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (D : W ∣ γ ⊢² M ⊑ N ∶ p)
  → ChainTelescope
telescopeOf (CTI2.x⊑x² x∈) = tel-x x∈
telescopeOf (CTI2.ƛ⊑ƛ² D) = tel-ƛ (telescopeOf D)
telescopeOf (CTI2.·⊑·² D₁ D₂) =
  tel-· (telescopeOf D₁) (telescopeOf D₂)
telescopeOf (CTI2.Λ⊑Λ² liftγ vV vV′ D q) =
  tel-ΛΛ liftγ vV vV′ (telescopeOf D) q
telescopeOf (CTI2.Λ⊑² Anv zero∈A liftγ vV M⊢ D q) =
  tel-Λ Anv zero∈A liftγ vV M⊢ (telescopeOf D) q
telescopeOf (CTI2.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
    p∀ D q r) =
  tel-•• (telescopeOf D)
telescopeOf (CTI2.•⊑² {C = C} {A = A} {B = B} p∀ D q r) =
  tel-• (telescopeOf D)
telescopeOf (CTI2.κ⊑κ² κ p) = tel-κ κ
telescopeOf (CTI2.cast⊑cast² {C = C} {C′ = C′} {A = A}
    {A′ = A′} c c′ D q) =
  tel-castcast (telescopeOf D)
telescopeOf (CTI2.⊑cast² {A = A} {B = B} {B′ = B′} c′ D q) =
  tel-⊑cast (telescopeOf D)
telescopeOf (CTI2.⊑reveal² mono rb sc c′⊢ D q) =
  tel-⊑reveal mono rb sc c′⊢ (telescopeOf D) q
telescopeOf (CTI2.⊑conceal² mono rb sc c′⊢ D q) =
  tel-⊑conceal mono rb sc c′⊢ (telescopeOf D) q
telescopeOf (CTI2.cast⊑² {A = A} {A′ = A′} {B = B} c D q) =
  tel-cast⊑ (telescopeOf D)
telescopeOf (CTI2.reveal⊑² mono rb sc c⊢ D q) =
  tel-reveal⊑ mono rb sc c⊢ (telescopeOf D) q
telescopeOf (CTI2.conceal⊑² mono rb sc c⊢ D q) =
  tel-conceal⊑ mono rb sc c⊢ (telescopeOf D) q
telescopeOf (CTI2.reveal⊑reveal² mono rb sc c⊢ c′⊢ D q) =
  tel-revealreveal mono rb sc c⊢ c′⊢ (telescopeOf D) q
telescopeOf (CTI2.conceal⊑conceal² mono rb sc c⊢ c′⊢ D q) =
  tel-concealconceal mono rb sc c⊢ c′⊢ (telescopeOf D) q
telescopeOf (CTI2.blame⊑² M′⊢ p) = tel-blame M′⊢ p
telescopeOf (CTI2.⊕⊑⊕² op {p = p} {q = q} D₁ D₂ r) =
  tel-⊕ op (telescopeOf D₁) (telescopeOf D₂)

typedTelescopeOf : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (D : W ∣ γ ⊢² M ⊑ N ∶ p)
  → TypedChainTelescope W γ M N p
typedTelescopeOf (CTI2.x⊑x² x∈) = typed-x x∈
typedTelescopeOf (CTI2.ƛ⊑ƛ² D) =
  typed-ƛ (typedTelescopeOf D)
typedTelescopeOf (CTI2.·⊑·² D₁ D₂) =
  typed-· (typedTelescopeOf D₁) (typedTelescopeOf D₂)
typedTelescopeOf (CTI2.Λ⊑Λ² liftγ vV vV′ D q) =
  typed-ΛΛ liftγ vV vV′ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.Λ⊑² Anv zero∈A liftγ vV M⊢ D q) =
  typed-Λ Anv zero∈A liftγ vV M⊢ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.•⊑•² p∀ D q r) =
  typed-•• p∀ (typedTelescopeOf D) q r
typedTelescopeOf (CTI2.•⊑² p∀ D q r) =
  typed-• p∀ (typedTelescopeOf D) q r
typedTelescopeOf (CTI2.κ⊑κ² κ p) = typed-κ κ p
typedTelescopeOf (CTI2.cast⊑cast² c c′ D q) =
  typed-castcast c c′ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.⊑cast² c′ D q) =
  typed-⊑cast c′ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.⊑reveal² mono rb sc c′⊢ D q) =
  typed-⊑reveal mono rb sc c′⊢ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.⊑conceal² mono rb sc c′⊢ D q) =
  typed-⊑conceal mono rb sc c′⊢ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.cast⊑² c D q) =
  typed-cast⊑ c (typedTelescopeOf D) q
typedTelescopeOf (CTI2.reveal⊑² mono rb sc c⊢ D q) =
  typed-reveal⊑ mono rb sc c⊢ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.conceal⊑² mono rb sc c⊢ D q) =
  typed-conceal⊑ mono rb sc c⊢ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.reveal⊑reveal² mono rb sc c⊢ c′⊢ D q) =
  typed-revealreveal mono rb sc c⊢ c′⊢ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.conceal⊑conceal² mono rb sc c⊢ c′⊢ D q) =
  typed-concealconceal mono rb sc c⊢ c′⊢ (typedTelescopeOf D) q
typedTelescopeOf (CTI2.blame⊑² M′⊢ p) = typed-blame M′⊢ p
typedTelescopeOf (CTI2.⊕⊑⊕² op D₁ D₂ r) =
  typed-⊕ op (typedTelescopeOf D₁) (typedTelescopeOf D₂) r

reify : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (sv : SpineValue V)
  → (vN : Value N)
  → (D : W ∣ γ ⊢² V ⊑ N ∶ p)
  → ChainRideReification sv vN D
reify sv vN D =
  ride-reified (typedTelescopeOf D) (telescopeOf D)
    (nodesOf D) (length (nodesOf D))
