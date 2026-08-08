module proof.DGG.TermImpDecay where

-- File Charter:
--   * Transports version-2 cast-term imprecision across world decay.
--   * Lifts decay through type binders and term-context lifting.
--   * Decays pivot-local rebasing and wrapper-rule premise worlds.
--   * Exports obligation-insensitive transport via proof irrelevance.

open import Data.List using ([]; _∷_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)
  renaming (subst to subst≡)

open import Types
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.DGG.WorldDecay
import proof.Imprecision as PI

------------------------------------------------------------------------
-- Decay under type binders
------------------------------------------------------------------------

liftDecayBoth : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → EnvDecay W Wᵈ
  → EnvDecay (CTI2.liftWorldBoth v W) (CTI2.liftWorldBoth v Wᵈ)
liftDecayBoth
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′}
    v
    (env-decay refl refl refl refl mono) =
  env-decay refl refl refl refl lift-mono
  where
  lift-mono : ∀ Z
    → extendᵐ v μ Z ≡ X⊑★
    → extendᵐ v μᵈ Z ≡ X⊑★
  lift-mono Fin.zero eq = eq
  lift-mono (Fin.suc Z) eq = mono Z eq

liftDecayLeft : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → EnvDecay W Wᵈ
  → EnvDecay (CTI2.liftWorldLeft v W) (CTI2.liftWorldLeft v Wᵈ)
liftDecayLeft
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′}
    v
    (env-decay refl refl refl refl mono) =
  env-decay refl refl refl refl lift-mono
  where
  lift-mono : ∀ Z
    → extendᵐ v μ Z ≡ X⊑★
    → extendᵐ v μᵈ Z ≡ X⊑★
  lift-mono Fin.zero eq = eq
  lift-mono (Fin.suc Z) eq = mono Z eq

decayLiftCtx : ∀ {Δᴸ Δᴿ Δ} {v} {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γ′ : CTI2.CtxImp (CTI2.liftWorldBoth v W)}
  → (dec : EnvDecay W Wᵈ)
  → CTI2.LiftCtx v γ γ′
  → CTI2.LiftCtx v (decayCtx dec γ)
      (decayCtx (liftDecayBoth v dec) γ′)
decayLiftCtx dec CTI2.lift-[] = CTI2.lift-[]
decayLiftCtx dec (CTI2.lift-∷ liftγ) =
  CTI2.lift-∷ (decayLiftCtx dec liftγ)

decayLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ} {v} {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γ′ : CTI2.CtxImp (CTI2.liftWorldLeft v W)}
  → (dec : EnvDecay W Wᵈ)
  → CTI2.LiftCtxᴸ v γ γ′
  → CTI2.LiftCtxᴸ v (decayCtx dec γ)
      (decayCtx (liftDecayLeft v dec) γ′)
decayLiftCtxᴸ dec CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
decayLiftCtxᴸ dec (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (decayLiftCtxᴸ dec liftγ)

decayCtx-tgt : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
  → (dec : EnvDecay W Wᵈ)
  → (γ : CTI2.CtxImp W)
  → CTI2.tgtCtxʷ (decayCtx dec γ) ≡ CTI2.tgtCtxʷ γ
decayCtx-tgt dec [] = refl
decayCtx-tgt dec (CTI2.ctx-imp A B p ∷ γ) =
  cong (_ ∷_) (decayCtx-tgt dec γ)

------------------------------------------------------------------------
-- Decay of pivot-local rebasing
------------------------------------------------------------------------

decayRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W₁ W₁ᵈ W₂ W₂ᵈ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (dec₁ : EnvDecay W₁ W₁ᵈ)
  → (dec₂ : EnvDecay W₂ W₂ᵈ)
  → CTI2.RebaseAt W₁ W₂ Xᴸ Xᴿ
  → CTI2.RebaseAt W₁ᵈ W₂ᵈ Xᴸ Xᴿ
decayRebaseAt
    {W₁ = CTI2.world ηL₁ ηR₁ μ₁ ΣL₁ ΣR₁}
    {W₁ᵈ = CTI2.world ηL₁′ ηR₁′ μ₁ᵈ ΣL₁′ ΣR₁′}
    {W₂ = CTI2.world ηL₂ ηR₂ μ₂ ΣL₂ ΣR₂}
    {W₂ᵈ = CTI2.world ηL₂′ ηR₂′ μ₂ᵈ ΣL₂′ ΣR₂′}
    (env-decay refl refl refl refl mono₁)
    dec₂@(env-decay refl refl refl refl mono₂)
    (CTI2.rebase-at (CTI2.same-runtime source-eq target-eq)
      offL frozenR aligned (CTI2.store-rep-imp represented)) =
  CTI2.rebase-at (CTI2.same-runtime source-eq target-eq)
    offL frozenR aligned
    (CTI2.store-rep-imp (decay⊑ᵂ dec₂ represented))

------------------------------------------------------------------------
-- Term-imprecision decay
------------------------------------------------------------------------

⊢²-decay : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → (dec : EnvDecay W Wᵈ)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ decay⊑ᵂ dec p
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.x⊑x² x∈) =
  CTI2.x⊑x² (decay∋ʷ dec x∈)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.ƛ⊑ƛ² M⊑M′) =
  CTI2.ƛ⊑ƛ² (⊢²-decay dec M⊑M′)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.·⊑·² L⊑L′ M⊑M′) =
  CTI2.·⊑·² (⊢²-decay dec L⊑L′) (⊢²-decay dec M⊑M′)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.Λ⊑Λ² liftγ vV vV′ V⊑V′ q) =
  CTI2.Λ⊑Λ² (decayLiftCtx dec liftγ) vV vV′
    (⊢²-decay (liftDecayBoth X⊑X dec) V⊑V′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    {γ = γ}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q) =
  CTI2.Λ⊑² Anv zero∈A (decayLiftCtxᴸ dec liftγ) vV
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (decayCtx-tgt dec γ)) M′⊢)
    (⊢²-decay (liftDecayLeft X⊑★ dec) V⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.•⊑•² p∀ M⊑M′ q r) =
  CTI2.•⊑•² (decay⊑ᵂ dec p∀) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q) (decay⊑ᵂ dec r)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.•⊑² p∀ M⊑M′ q r) =
  CTI2.•⊑² (decay⊑ᵂ dec p∀) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q) (decay⊑ᵂ dec r)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.κ⊑κ² κ p) =
  CTI2.κ⊑κ² κ (decay⊑ᵂ dec p)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.cast⊑cast² c c′ M⊑M′ q) =
  CTI2.cast⊑cast² c c′ (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑cast² c′ M⊑M′ q) =
  CTI2.⊑cast² c′ (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.cast⊑² c M⊑M′ q) =
  CTI2.cast⊑² c (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑reveal² rule-mono CTI2.rebase-idᴿ sc
      c′⊢ M⊑M′ q) =
  CTI2.⊑reveal² (λ _ eq → eq) CTI2.rebase-idᴿ
    (decaySameCtx dec dec sc) c′⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑reveal² {W′ = W′} rule-mono
      (CTI2.rebase-varᴿ rb) sc c′⊢ M⊑M′ q) =
  CTI2.⊑reveal²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ})
    (CTI2.rebase-varᴿ
      (decayRebaseAt dec
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) sc)
    c′⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑conceal² rule-mono CTI2.rebase-idᴿ sc
      c′⊢ M⊑M′ q) =
  CTI2.⊑conceal² (λ _ eq → eq) CTI2.rebase-idᴿ
    (decaySameCtx dec dec sc) c′⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑conceal² {W′ = W′} rule-mono
      (CTI2.rebase-varᴿ rb) sc c′⊢ M⊑M′ q) =
  CTI2.⊑conceal²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ})
    (CTI2.rebase-varᴿ
      (decayRebaseAt
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) dec rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) sc)
    c′⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.reveal⊑² rule-mono CTI2.rebase-idᴸ sc
      c⊢ M⊑M′ q) =
  CTI2.reveal⊑² (λ _ eq → eq) CTI2.rebase-idᴸ
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.reveal⊑² {W′ = W′} rule-mono
      (CTI2.rebase-varᴸ rb) sc c⊢ M⊑M′ q) =
  CTI2.reveal⊑²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ})
    (CTI2.rebase-varᴸ
      (decayRebaseAt dec
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) sc)
    c⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.reveal⊑² rule-mono
      (CTI2.rebase-onlyᴸ to-star disaligned represented)
      sc c⊢ M⊑M′ q) =
  CTI2.reveal⊑² (λ _ eq → eq)
    (CTI2.rebase-onlyᴸ (mono _ to-star) disaligned
      (decay⊑ᵂ dec represented))
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.conceal⊑² rule-mono CTI2.rebase-idᴸ sc
      c⊢ M⊑M′ q) =
  CTI2.conceal⊑² (λ _ eq → eq) CTI2.rebase-idᴸ
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.conceal⊑² {W′ = W′} rule-mono
      (CTI2.rebase-varᴸ rb) sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ})
    (CTI2.rebase-varᴸ
      (decayRebaseAt
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) dec rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) sc)
    c⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.conceal⊑² rule-mono
      (CTI2.rebase-onlyᴸ to-star disaligned represented)
      sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑² (λ _ eq → eq)
    (CTI2.rebase-onlyᴸ (mono _ to-star) disaligned
      (decay⊑ᵂ dec represented))
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} rule-mono rb sc
      c⊢ c′⊢ M⊑M′ q) =
  CTI2.reveal⊑reveal²
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ})
    (decayRebaseAt dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) sc)
    c⊢ c′⊢
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} rule-mono rb sc
      c⊢ c′⊢ M⊑M′ q) =
  CTI2.conceal⊑conceal²
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ})
    (decayRebaseAt
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) dec rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) sc)
    c⊢ c′⊢
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.blame⊑² M′⊢ p) =
  CTI2.blame⊑²
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (decayCtx-tgt dec _)) M′⊢)
    (decay⊑ᵂ dec p)
⊢²-decay
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊕⊑⊕² op L⊑L′ M⊑M′ r) =
  CTI2.⊕⊑⊕² op (⊢²-decay dec L⊑L′) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec r)

⊢²-decay-at : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → (dec : EnvDecay W Wᵈ)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → (pᵈ : A CTI2.⊑ᵂ⟨ Wᵈ ⟩ B)
  → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ pᵈ
⊢²-decay-at {Wᵈ = Wᵈ} {γ = γ} {M = M} {M′ = M′} {p = p}
    dec M⊑M′ pᵈ =
  subst≡ (λ q → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ q)
    (PI.⊑-unique (decay⊑ᵂ dec p) pᵈ) (⊢²-decay dec M⊑M′)
