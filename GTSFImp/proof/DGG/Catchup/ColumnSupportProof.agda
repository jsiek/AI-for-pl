module proof.DGG.Catchup.ColumnSupportProof where

-- File Charter:
--   * Proves the non-blocked M6 cast-column support lemmas stated in
--     ValueCatchupRightDef.
--   * Keeps the support proofs independent of the higher-order M4/M5 proof
--     implementations.
--   * Depends on core consistency/reduction, the value-catch-up Def surface,
--     and stage-1 DGG world-extension interfaces.

import Data.Fin as Fin
import Data.List as List
open import Data.Nat using (suc)
open import Data.Nat.Properties using (n<1+n; ≤-<-trans)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans)
  renaming (subst to subst≡)

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!)
open import proof.Consistency using
  (castSize-renameEnvᶜ; castSize-close-inst-≤)
open import proof.ImprecisionConsistency using
  (fin-suc-injective; ext-injective; renameᵗ-injective; rename-occurs)
open import proof.TypeInTermSubst using (rename-star-injective)
open import proof.Reduction using (applyConsistencies-Inert)
open import CastTerms using (Term)
open import Reduction using
  (StoreChange; StoreChanges; _—→[_]_; _—↠[_]_; keep; bind;
   []; _∷_; ↠-refl; ↠-step; ξ-⟨⟩; applyConsistency;
   applyStore; applyTy; applyStores; applyTys)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.Imprecision as PI
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_)
open import proof.DGG.Catchup.ValueCatchupRightDef
  using
    ( castSize; CastColumn; []ᶜ; _▻ᶜ_; columnSize; applyColumn
    ; mapColumn₁; mapColumn; _++χ_
    ; CatchupCast⁻; catchup⁻-inert; catchup⁻-id
    ; catchup⁻-ground-other; catchup⁻-inst
    ; catchup⁻-bot-elim; catchup⁻-bot-intro
    ; CatchupColumn⁻; ccol⁻-[]; ccol⁻-▻
    ; Catchup⁻Embedᵀ; CatchupColumn⁻Transportᵀ
    ; ground-other-decreaseᵀ; project-expand-decreaseᵀ
    ; castSize-↑close-instᵀ; inst-alloc-decreaseᵀ
    ; columnSize-mapᵀ
    ; composeWorldExtendᴿᵀ; mapCtxᴿ-composeᵀ
    ; composeReductionᵀ; liftReductionThroughColumnᵀ
    )

------------------------------------------------------------------------
-- Strict-decrease one-step obligations that do not allocate
------------------------------------------------------------------------

ground-other-decrease : ground-other-decreaseᵀ
ground-other-decrease c = n<1+n (castSize c)

project-expand-decrease : project-expand-decreaseᵀ
project-expand-decrease c = n<1+n (castSize c)

castSize-↑close-inst : castSize-↑close-instᵀ
castSize-↑close-inst {c = c} = castSize-close-inst-≤ c

inst-alloc-decrease : inst-alloc-decreaseᵀ
inst-alloc-decrease {c = c} B≢★ =
  ≤-<-trans (castSize-close-inst-≤ c) (n<1+n (castSize c))

------------------------------------------------------------------------
-- Cast-column size preservation under store changes
------------------------------------------------------------------------

castSize-applyConsistency : ∀ {Δ Δ′} {μ : Env∼ Δ}
    {A B : Ty Δ}
  → (χ : StoreChange Δ Δ′)
  → (c : μ ⊢ A ∼ B)
  → castSize (applyConsistency χ c) ≡ castSize c
castSize-applyConsistency keep c = refl
castSize-applyConsistency (bind A) c =
  castSize-renameEnvᶜ Fin.suc (λ X → refl) c


castSize-applyConsistencies : ∀ {Δ Δ′} {μ : Env∼ Δ}
    {A B : Ty Δ}
  → (χs : StoreChanges Δ Δ′)
  → (c : μ ⊢ A ∼ B)
  → castSize (Reduction.applyConsistencies χs c) ≡ castSize c
castSize-applyConsistencies [] c = refl
castSize-applyConsistencies (χ ∷ χs) c =
  trans (castSize-applyConsistencies χs (applyConsistency χ c))
    (castSize-applyConsistency χ c)


columnSize-map₁ : ∀ {Δ Δ′} {A B : Ty Δ}
  → (χ : StoreChange Δ Δ′)
  → (κ : CastColumn A B)
  → columnSize (mapColumn₁ χ κ) ≡ columnSize κ
columnSize-map₁ χ []ᶜ = refl
columnSize-map₁ χ (c ▻ᶜ κ)
  rewrite castSize-applyConsistency χ c | columnSize-map₁ χ κ = refl

columnSize-map : columnSize-mapᵀ
columnSize-map [] κ = refl
columnSize-map (χ ∷ χs) κ =
  trans (columnSize-map χs (mapColumn₁ χ κ)) (columnSize-map₁ χ κ)

------------------------------------------------------------------------
-- Store-change append algebra
------------------------------------------------------------------------

applyStores-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → ∀ Σ
  → applyStores ψs (applyStores χs Σ) ≡ applyStores (χs ++χ ψs) Σ
applyStores-++ [] ψs Σ = refl
applyStores-++ (χ ∷ χs) ψs Σ =
  applyStores-++ χs ψs (applyStore χ Σ)

applyTys-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → ∀ A
  → applyTys ψs (applyTys χs A) ≡ applyTys (χs ++χ ψs) A
applyTys-++ [] ψs A = refl
applyTys-++ (χ ∷ χs) ψs A = applyTys-++ χs ψs (applyTy χ A)

composeWorldExtendᴿ : composeWorldExtendᴿᵀ
composeWorldExtendᴿ {χs = χs} {ψs = ψs} {W₀ = W₀} {W₂ = W₂}
    ext₁ ext₂ =
  record
    { sourceStore-kept =
        trans (ECR.sourceStore-kept ext₂) (ECR.sourceStore-kept ext₁)
    ; targetStore-follows =
        trans (ECR.targetStore-follows ext₂)
          (trans
            (cong (applyStores ψs) (ECR.targetStore-follows ext₁))
            (applyStores-++ χs ψs (CTI2.targetStoreʷ W₀)))
    ; transport⊑ᵂ = λ {A = A} {C = C} p →
        subst≡ (λ C′ → A ⊑ᵂ⟨ W₂ ⟩ C′)
          (applyTys-++ χs ψs C)
          (ECR.transport⊑ᵂ ext₂ (ECR.transport⊑ᵂ ext₁ p))
    }

ctx-imp-transportᴿ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → (eq : B ≡ B′)
  → (p : A ⊑ᵂ⟨ W ⟩ B)
  → CTI2.ctx-imp {W = W} A B p ≡
    CTI2.ctx-imp {W = W} A B′
      (subst≡ (λ C → A ⊑ᵂ⟨ W ⟩ C) eq p)
ctx-imp-transportᴿ refl p = refl

mapCtxᴿ-compose : mapCtxᴿ-composeᵀ composeWorldExtendᴿ
mapCtxᴿ-compose ext₁ ext₂ List.[] = refl
mapCtxᴿ-compose {χs = χs} {ψs = ψs} {W₂ = W₂} ext₁ ext₂
    (CTI2.ctx-imp A B p List.∷ γ) =
  cong₂ List._∷_
    (ctx-imp-transportᴿ {W = W₂} (applyTys-++ χs ψs B)
      (ECR.transport⊑ᵂ ext₂ (ECR.transport⊑ᵂ ext₁ p)))
    (mapCtxᴿ-compose ext₁ ext₂ γ)

------------------------------------------------------------------------
-- Store-changing trace composition and column lifting
------------------------------------------------------------------------

composeReduction : composeReductionᵀ
composeReduction ↠-refl N↠P = N↠P
composeReduction (↠-step M→N N↠P) P↠Q =
  ↠-step M→N (composeReduction N↠P P↠Q)

liftStepThroughColumn : ∀ {Δ Δ′} {A B : Ty Δ}
    {χ : StoreChange Δ Δ′} {M : Term Δ} {N : Term Δ′}
  → (κ : CastColumn A B)
  → M —→[ χ ] N
  → applyColumn M κ —→[ χ ] applyColumn N (mapColumn₁ χ κ)
liftStepThroughColumn []ᶜ M→N = M→N
liftStepThroughColumn (c ▻ᶜ κ) M→N =
  liftStepThroughColumn κ (ξ-⟨⟩ M→N refl)

liftReductionThroughColumn : liftReductionThroughColumnᵀ
liftReductionThroughColumn κ ↠-refl = ↠-refl
liftReductionThroughColumn κ (↠-step M→N N↠P) =
  ↠-step (liftStepThroughColumn κ M→N)
    (liftReductionThroughColumn (mapColumn₁ _ κ) N↠P)

------------------------------------------------------------------------
-- Fragment embedding: term-independent provenance holds at any term
------------------------------------------------------------------------

catchup⁻-embed : Catchup⁻Embedᵀ
catchup⁻-embed N (catchup⁻-inert i) = ECR.catchup-inert i
catchup⁻-embed N (catchup⁻-id a) = ECR.catchup-id a
catchup⁻-embed N (catchup⁻-ground-other B≢G r k) =
  ECR.catchup-ground-other B≢G r (catchup⁻-embed N k)
catchup⁻-embed N catchup⁻-inst = ECR.catchup-inst
catchup⁻-embed N catchup⁻-bot-elim = ECR.catchup-bot-elim
catchup⁻-embed N catchup⁻-bot-intro = ECR.catchup-bot-intro

------------------------------------------------------------------------
-- Column-provenance transport through target store changes
------------------------------------------------------------------------

mapAtom : ∀ {Δ Δ′} {χs : StoreChanges Δ Δ′}
    {A : Ty Δ}
  → Atom A
  → Atom (applyTys χs A)
mapAtom {χs = []} a = a
mapAtom {χs = keep ∷ χs} a = mapAtom {χs = χs} a
mapAtom {χs = bind A ∷ χs} (＇ X) =
  mapAtom {χs = χs} (＇ Fin.suc X)
mapAtom {χs = bind A ∷ χs} (‵ ι) = mapAtom {χs = χs} (‵ ι)
mapAtom {χs = bind A ∷ χs} ★ = mapAtom {χs = χs} ★

applyConsistencies-id : ∀ {Δ Δ′} {χs : StoreChanges Δ Δ′}
    {A : Ty Δ} {ν : Env∼ Δ}
  → (a : Atom A)
  → Reduction.applyConsistencies χs (Consistency.id {μ = ν} a) ≡
    Consistency.id (mapAtom {χs = χs} a)
applyConsistencies-id {χs = []} a = refl
applyConsistencies-id {χs = keep ∷ χs} a =
  applyConsistencies-id {χs = χs} a
applyConsistencies-id {χs = bind A ∷ χs} (＇ X) =
  applyConsistencies-id {χs = χs} (＇ Fin.suc X)
applyConsistencies-id {χs = bind A ∷ χs} (‵ ι) =
  applyConsistencies-id {χs = χs} (‵ ι)
applyConsistencies-id {χs = bind A ∷ χs} ★ =
  applyConsistencies-id {χs = χs} ★

mapGroundOther : ∀ {Δᴸ Δ₀ Δ₁ Δ}
    {χs : StoreChanges Δ₀ Δ₁} {W : World Δᴸ Δ₁ Δ}
    {A : Ty Δᴸ} {B G : Ty Δ₀} {ν : Env∼ Δ₀}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄ {c : ν ⊢ B ∼ G}
    {p : A ⊑ᵂ⟨ W ⟩ applyTys χs B}
    {r : A ⊑ᵂ⟨ W ⟩ applyTys χs G}
    {q : A ⊑ᵂ⟨ W ⟩ applyTys χs ★}
  → B ≢ G
  → CatchupCast⁻ {W = W} {A = A} p
      (Reduction.applyConsistencies χs c) r
  → CatchupCast⁻ {W = W} {A = A} p
      (Reduction.applyConsistencies χs
        (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄)) q
mapGroundOther {χs = []} B≢G k = catchup⁻-ground-other B≢G _ k
mapGroundOther {χs = keep ∷ χs} B≢G k =
  mapGroundOther {χs = χs} B≢G k
mapGroundOther {χs = bind A ∷ χs} ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄
    ⦃ Bns ⦄ B≢G k =
  mapGroundOther {χs = χs}
    ⦃ Gᵍ = Consistency.renameGround Fin.suc Gᵍ ⦄
    ⦃ G∼★ = Consistency.rename∼★ Fin.suc (λ X → refl) G∼★ ⦄
    ⦃ Bns = Consistency.renameNonStar Fin.suc Bns ⦄
    (λ eq → B≢G (renameᵗ-injective fin-suc-injective eq)) k

mapInst : ∀ {Δᴸ Δ₀ Δ₁ Δ}
    {χs : StoreChanges Δ₀ Δ₁} {W : World Δᴸ Δ₁ Δ}
    {A : Ty Δᴸ} {B₀ : Ty (suc Δ₀)} {B′ : Ty Δ₀}
    {ν : Env∼ Δ₀} {c′ : Consistency.instᵐ ν ⊢ B₀ ∼ ⇑ᵗ B′}
    ⦃ Bnv : NonVar B₀ ⦄ ⦃ zero∈B : Fin.zero ∈ᵗ B₀ ⦄
    {B′≢★ : B′ ≢ ★}
    {p : A ⊑ᵂ⟨ W ⟩ applyTys χs (`∀ B₀)}
    {q : A ⊑ᵂ⟨ W ⟩ applyTys χs B′}
  → CatchupCast⁻ {W = W} {A = A} p
      (Reduction.applyConsistencies χs ((Consistency.inst c′) B′≢★)) q
mapInst {χs = []} = catchup⁻-inst
mapInst {χs = keep ∷ χs} = mapInst {χs = χs}
mapInst {χs = bind A ∷ χs} {B₀ = B₀} {B′ = B′} {c′ = c′}
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ {B′≢★} =
  subst≡
    (λ z → CatchupCast⁻ _
      (Reduction.applyConsistencies χs
        (Consistency.inst_
          ⦃ Anv = renameNonVar (extᵗ Fin.suc) Bnv ⦄
          ⦃ z∈A = z ⦄ c′₁ B′₁≢★)) _)
    (PI.∈ᵗ-unique zero∈B₁ _)
    (mapInst {χs = χs}
      {B₀ = renameᵗ (extᵗ Fin.suc) B₀}
      {B′ = renameᵗ Fin.suc B′} {c′ = c′₁}
      ⦃ Bnv = renameNonVar (extᵗ Fin.suc) Bnv ⦄
      ⦃ zero∈B = zero∈B₁ ⦄ {B′≢★ = B′₁≢★})
  where
  c′₁ = Consistency.subst-right-∼ (renameᵗ-shift Fin.suc B′)
    (Consistency.rename∼ (extᵗ Fin.suc)
      (Consistency.instᵐ-rename Fin.suc (λ X → refl)) c′)
  zero∈B₁ = rename-occurs (extᵗ Fin.suc)
    (ext-injective fin-suc-injective) zero∈B
  B′₁≢★ = λ eq → B′≢★ (rename-star-injective Fin.suc eq)

mapBotElim : ∀ {Δᴸ Δ₀ Δ₁ Δ}
    {χs : StoreChanges Δ₀ Δ₁} {W : World Δᴸ Δ₁ Δ}
    {A : Ty Δᴸ} {ν : Env∼ Δ₀}
    {p : A ⊑ᵂ⟨ W ⟩ applyTys χs (`∀ (＇ Fin.zero))}
    {q : A ⊑ᵂ⟨ W ⟩ applyTys χs (`∀ ★)}
  → CatchupCast⁻ {W = W} {A = A} p
      (Reduction.applyConsistencies χs
        (Consistency.bot-elim {μ = ν})) q
mapBotElim {χs = []} = catchup⁻-bot-elim
mapBotElim {χs = keep ∷ χs} = mapBotElim {χs = χs}
mapBotElim {χs = bind A ∷ χs} = mapBotElim {χs = χs}

mapBotIntro : ∀ {Δᴸ Δ₀ Δ₁ Δ}
    {χs : StoreChanges Δ₀ Δ₁} {W : World Δᴸ Δ₁ Δ}
    {A : Ty Δᴸ} {ν : Env∼ Δ₀}
    {p : A ⊑ᵂ⟨ W ⟩ applyTys χs (`∀ ★)}
    {q : A ⊑ᵂ⟨ W ⟩ applyTys χs (`∀ (＇ Fin.zero))}
  → CatchupCast⁻ {W = W} {A = A} p
      (Reduction.applyConsistencies χs
        (Consistency.bot-intro {μ = ν})) q
mapBotIntro {χs = []} = catchup⁻-bot-intro
mapBotIntro {χs = keep ∷ χs} = mapBotIntro {χs = χs}
mapBotIntro {χs = bind A ∷ χs} = mapBotIntro {χs = χs}

transportCatchup⁻ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ᵂ}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′ᵂ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {c : ν ⊢ B ∼ B′}
    {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → CatchupCast⁻ {W = W} {A = A} p c q
  → CatchupCast⁻ {W = W′} {A = A}
      (ECR.transport⊑ᵂ ext p) (Reduction.applyConsistencies χs c)
      (ECR.transport⊑ᵂ ext q)
transportCatchup⁻ {χs = χs} ext (catchup⁻-inert i) =
  catchup⁻-inert (applyConsistencies-Inert χs i)
transportCatchup⁻ {χs = χs} ext (catchup⁻-id a) =
  subst≡
    (λ c → CatchupCast⁻ (ECR.transport⊑ᵂ ext _) c
      (ECR.transport⊑ᵂ ext _))
    (sym (applyConsistencies-id {χs = χs} a))
    (catchup⁻-id (mapAtom {χs = χs} a))
transportCatchup⁻ {χs = χs} ext
    (catchup⁻-ground-other {Gᵍ = Gᵍ} {G∼★ = G∼★}
      {Bns = Bns} B≢G r k) =
  mapGroundOther {χs = χs} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
    ⦃ Bns = Bns ⦄ B≢G (transportCatchup⁻ ext k)
transportCatchup⁻ {χs = χs} ext catchup⁻-inst = mapInst {χs = χs}
transportCatchup⁻ {χs = χs} ext catchup⁻-bot-elim =
  mapBotElim {χs = χs}
transportCatchup⁻ {χs = χs} ext catchup⁻-bot-intro =
  mapBotIntro {χs = χs}

mapColumn-▻ : ∀ {Δ Δ′} {χs : StoreChanges Δ Δ′}
    {A B C : Ty Δ} {ν : Env∼ Δ}
  → (c : ν ⊢ A ∼ B)
  → (k : CastColumn B C)
  → mapColumn χs (c ▻ᶜ k) ≡
    (Reduction.applyConsistencies χs c ▻ᶜ mapColumn χs k)
mapColumn-▻ {χs = []} c k = refl
mapColumn-▻ {χs = χ ∷ χs} c k =
  mapColumn-▻ {χs = χs} (applyConsistency χ c) (mapColumn₁ χ k)

mapColumn-[] : ∀ {Δ Δ′} {χs : StoreChanges Δ Δ′} {A : Ty Δ}
  → mapColumn χs ([]ᶜ {A = A}) ≡ []ᶜ
mapColumn-[] {χs = []} = refl
mapColumn-[] {χs = χ ∷ χs} = mapColumn-[] {χs = χs}

catchup-column⁻-transport : CatchupColumn⁻Transportᵀ
catchup-column⁻-transport {χs = χs} ext (ccol⁻-[] {B = B})
  rewrite mapColumn-[] {χs = χs} {A = B} = ccol⁻-[]
catchup-column⁻-transport {χs = χs} ext
    (ccol⁻-▻ {c = c} {κ = κ} k ks)
  rewrite mapColumn-▻ {χs = χs} c κ =
  ccol⁻-▻ (transportCatchup⁻ ext k)
    (catchup-column⁻-transport ext ks)
