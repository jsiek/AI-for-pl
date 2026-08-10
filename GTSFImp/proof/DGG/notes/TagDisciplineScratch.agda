module TagDisciplineScratch where

-- Root-level scratch for the sealed-name tag discipline investigation.
-- It defines a small restricted cast-term-imprecision fragment for the
-- source-seal/right-tag cases involved in MismatchProbeScratch.agda.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Bool using (true)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (Env∼; Var∼; X∼★; ★∼X; _⊢_∼_; _↪ᵗ_; empty; keep; skip;
   toRenameᵗ; id; _!)
open import Conversion using (Conv↑; Conv↓; seal)
open import Imprecision
open import CastTerms using
  (Term; `_ ; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_; _↓_;
   blame)
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.Examples as Ex
import proof.DGG.Examples2 as Ex2
import proof.DGG.CompilePreservesImprecision2 as CPI2
import proof.DGG.Phase3DeepDives as P3
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.CompileImageShape as CIS

open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_; RebaseAt; CtxImp;
   ImpEnvMono; SameCtx; StoreRepImp; store-rep-imp; same-runtime;
   ⊢↓-sealˣ; same-[])

private
  Z : TyVar 2
  Z = Fin.zero

  U : TyVar 2
  U = Fin.suc Fin.zero

  Y : TyVar 1
  Y = Fin.zero

source-store : TyStore 2
source-store = store-bind (store-bind store-empty (‵ `ℕ)) ★

target-store : TyStore 1
target-store = store-bind store-empty ★

source-U∋ : source-store ∋ U ⦂ ‵ `ℕ
source-U∋ = S-bind∋ (Z∋ refl) refl

target-Y∋ : target-store ∋ Y ⦂ ★
target-Y∋ = Z∋ refl

source-η : 2 ↪ᵗ 2
source-η = keep (keep empty)

target-η-U : 1 ↪ᵗ 2
target-η-U = skip (keep empty)

imp-env-dyn : ImpEnv 2
imp-env-dyn Fin.zero = X⊑★
imp-env-dyn (Fin.suc Fin.zero) = X⊑★

probe-world : World 2 1 2
probe-world = world source-η target-η-U imp-env-dyn source-store target-store

target-env-tag : Env∼ 1
target-env-tag _ = X∼★

ℕ! : target-env-tag ⊢ (‵ `ℕ) ∼ ★
ℕ! = id (‵ `ℕ) !

Y! : target-env-tag ⊢ ＇ Y ∼ ★
Y! = id (＇ Y) !

source-U-seal-typed : source-store CTI2.⊢↓[ just U ] seal U (‵ `ℕ)
source-U-seal-typed = ⊢↓-sealˣ source-U∋

target-Y-seal-typed : target-store CTI2.⊢↓[ just Y ] seal Y ★
target-Y-seal-typed = ⊢↓-sealˣ target-Y∋

U-Y-representation : StoreRepImp probe-world U Y
U-Y-representation = store-rep-imp ι⊑★

U-Y-rebase : RebaseAt probe-world probe-world U Y
U-Y-rebase = CTI2.sameWorldRebaseAt refl U-Y-representation

probe-p : ＇ U ⊑ᵂ⟨ probe-world ⟩ ★
probe-p = X⊑★ refl

probe-q : ＇ U ⊑ᵂ⟨ probe-world ⟩ ＇ Y
probe-q = X⊑X

source-term : Term 2
source-term = ($ (κℕ 0)) ↓ seal U (‵ `ℕ)

target-untagged : Term 1
target-untagged = $ (κℕ 0)

target-tagged : Term 1
target-tagged = target-untagged ⟨ ℕ! ⟩

target-name-tagged : Term 1
target-name-tagged = (target-tagged ↓ seal Y ★) ⟨ Y! ⟩

------------------------------------------------------------------------
-- Proposed source-seal target-side tag discipline
------------------------------------------------------------------------

data NotTopTag {Δ : TyCtx} : Term Δ → Set where
  not-` : ∀ x → NotTopTag (` x)
  not-ƛ : ∀ {M} → NotTopTag (ƛ M)
  not-· : ∀ {L M} → NotTopTag (L · M)
  not-Λ : ∀ {M} → NotTopTag (Λ M)
  not-⦂∀ : ∀ {M A B} → NotTopTag (M ⦂∀ A [ B ])
  not-$ : ∀ κ → NotTopTag ($ κ)
  not-⊕ : ∀ {L M} op → NotTopTag (L ⊕[ op ] M)
  not-↑ : ∀ {M A B} {c : Conv↑ _ A B} → NotTopTag (M ↑ c)
  not-↓ : ∀ {M A B} {c : Conv↓ _ A B} → NotTopTag (M ↓ c)
  not-blame : NotTopTag blame

data SealTargetOK {Δ : TyCtx} :
    Maybe (TyVar Δ) → Term Δ → Set where
  plain-target : ∀ {X? M}
    → NotTopTag M
      -------------------
    → SealTargetOK X? M

  name-tagged-target : ∀ {X R M μ} {c : μ ⊢ ＇ X ∼ ★}
      -------------------------------------------------
    → SealTargetOK (just X) ((M ↓ seal X R) ⟨ c ⟩)

data TagRebaseAtᴸ {Δᴸ Δᴿ Δ}
    : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Maybe (TyVar Δᴿ) → Set where
  tag-rebase-idᴸ : ∀ {W}
      ---------------------------------------------
    → TagRebaseAtᴸ W W nothing nothing

  tag-rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------------------------
    → TagRebaseAtᴸ W W′ (just Xᴸ) (just Xᴿ)

  tag-rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
            ≢ toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
    → CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
      ---------------------------------------------------
    → TagRebaseAtᴸ W W (just Xᴸ) nothing

forgetTagRebaseᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → TagRebaseAtᴸ W W′ Xᴸ? Xᴿ?
    --------------------------
  → CTI2.RebaseAtᴸ W W′ Xᴸ?
forgetTagRebaseᴸ tag-rebase-idᴸ = CTI2.rebase-idᴸ
forgetTagRebaseᴸ (tag-rebase-varᴸ rb) = CTI2.rebase-varᴸ rb
forgetTagRebaseᴸ (tag-rebase-onlyᴸ to-star disaligned represented) =
  CTI2.rebase-onlyᴸ to-star disaligned represented

------------------------------------------------------------------------
-- Restricted fragment used by the probe
------------------------------------------------------------------------

infix 4 _∣_⊢ᵗᵈ_⊑_∶_

data _∣_⊢ᵗᵈ_⊑_∶_ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) :
    Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B → Set where

  κℕ⊑κℕᵗᵈ : ∀ n
    → (p : (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (‵ `ℕ))
      ----------------------------------------------------
    → W ∣ γ ⊢ᵗᵈ $ (κℕ n) ⊑ $ (κℕ n) ∶ p

  ⊑castᵗᵈ : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴿ}
    → (c′ : ν ⊢ B ∼ B′)
    → W ∣ γ ⊢ᵗᵈ M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢ᵗᵈ M ⊑ M′ ⟨ c′ ⟩ ∶ q

  conceal⊑ᵗᵈ : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → SealTargetOK Xᴿ? M′
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢ᵗᵈ M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢ᵗᵈ M ↓ c ⊑ M′ ∶ q

  conceal⊑concealᵗᵈ : ∀
      {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
    → ImpEnvMono W Wᵖ
    → RebaseAt Wᵖ W Xᴸ Xᴿ
    → SameCtx γ γᵖ
    → CTI2.sourceStoreʷ W CTI2.⊢↓[ just Xᴸ ] c
    → CTI2.targetStoreʷ W CTI2.⊢↓[ just Xᴿ ] c′
    → Wᵖ ∣ γᵖ ⊢ᵗᵈ M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢ᵗᵈ M ↓ c ⊑ M′ ↓ c′ ∶ q

forgetᵗᵈ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢ᵗᵈ M ⊑ M′ ∶ p
    ---------------------
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
forgetᵗᵈ (κℕ⊑κℕᵗᵈ n p) = CTI2.κ⊑κ² (κℕ n) p
forgetᵗᵈ (⊑castᵗᵈ c′ D q) = CTI2.⊑cast² c′ (forgetᵗᵈ D) q
forgetᵗᵈ (conceal⊑ᵗᵈ ok mono rb sc c⊢ D q) =
  CTI2.conceal⊑² mono (forgetTagRebaseᴸ rb) sc c⊢ (forgetᵗᵈ D) q
forgetᵗᵈ (conceal⊑concealᵗᵈ mono rb sc c⊢ c′⊢ D q) =
  CTI2.conceal⊑conceal² mono rb sc c⊢ c′⊢ (forgetᵗᵈ D) q

target-tagged-not-plain : NotTopTag target-tagged → ⊥
target-tagged-not-plain ()

mismatch-target-not-ok-any : ∀ {X?}
  → SealTargetOK X? target-tagged
  → ⊥
mismatch-target-not-ok-any (plain-target not-tag) =
  target-tagged-not-plain not-tag

mismatch-target-not-ok : SealTargetOK (just Y) target-tagged → ⊥
mismatch-target-not-ok = mismatch-target-not-ok-any

U-not-ℕ : ＇ U ⊑ᵂ⟨ probe-world ⟩ ‵ `ℕ → ⊥
U-not-ℕ ()

restricted-mismatch-premise-empty :
  _∣_⊢ᵗᵈ_⊑_∶_ probe-world [] source-term target-tagged
    {A = ＇ U} {B = ★} probe-p
  → ⊥
restricted-mismatch-premise-empty (⊑castᵗᵈ {p = p} c′ D q) =
  U-not-ℕ p
restricted-mismatch-premise-empty (conceal⊑ᵗᵈ ok mono rb sc c⊢ D q) =
  mismatch-target-not-ok-any ok

name-tag-target-ok : SealTargetOK (just Y) target-name-tagged
name-tag-target-ok = name-tagged-target

baseᵗᵈ : probe-world ∣ [] ⊢ᵗᵈ
    $ (κℕ 0) ⊑ $ (κℕ 0) ∶ ι⊑ι
baseᵗᵈ = κℕ⊑κℕᵗᵈ 0 ι⊑ι

target-rep-tagᵗᵈ : probe-world ∣ [] ⊢ᵗᵈ
    $ (κℕ 0) ⊑ target-tagged ∶ ι⊑★
target-rep-tagᵗᵈ = ⊑castᵗᵈ ℕ! baseᵗᵈ ι⊑★

paired-name-sealᵗᵈ : probe-world ∣ [] ⊢ᵗᵈ
    source-term ⊑ target-tagged ↓ seal Y ★ ∶ probe-q
paired-name-sealᵗᵈ =
  conceal⊑concealᵗᵈ (λ _ eq → eq) U-Y-rebase same-[]
    source-U-seal-typed target-Y-seal-typed target-rep-tagᵗᵈ probe-q

sealed-source-name-tag-positiveᵗᵈ : probe-world ∣ [] ⊢ᵗᵈ
    source-term ⊑ target-name-tagged ∶ probe-p
sealed-source-name-tag-positiveᵗᵈ =
  ⊑castᵗᵈ Y! paired-name-sealᵗᵈ probe-p

------------------------------------------------------------------------
-- Gate-shape checks that do not use the rejected source-only rep tag
------------------------------------------------------------------------

example12-checkpoint₁-gate :
  CTI2.example12-world-X ∣ [] ⊢² Ex.left₁ ⊑ Ex.right₃ ∶
    Ex2.example12-ℕ⊑ℕ-X
example12-checkpoint₁-gate = Ex2.example12-checkpoint₁

example12-paired-seal-gate :
  CTI2.example12-world-X ∣ [] ⊢²
    ($ (κℕ 7)) ↓ Ex2.example12-source-X-seal
    ⊑ ($ (κℕ 7)) ↓ Ex2.example12-target-X-seal ∶
      Ex2.example12-X-var⊑
example12-paired-seal-gate = Ex2.example12-sealed-const

representative-catalog-initial-gate :
  P3.entry-initial² RC.adversarial-source-chain ≡
  P3.adversarial-source-chain-initial²
representative-catalog-initial-gate = refl

representative-catalog-image-gate :
  CIS.compiled-entry-image-shape? RC.adversarial-source-chain ≡ true
representative-catalog-image-gate = CIS.adversarial-source-chain-image-shape

compile-preserves-imprecision²-gate :
  CPI2.compile-preserves-imprecision²-statement
compile-preserves-imprecision²-gate = CPI2.compile-preserves-imprecision²
