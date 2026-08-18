module proof.DGG.TerminusRebuildProbe where

-- File Charter:
--   * Records concrete terminus-rebuild instances for the M3 head cases.
--   * Instance A is the S = ★ base template: rebuild a `Λ⊑²` head
--     against the unsealed target value, then pair the source and target
--     seals with `conceal⊑conceal²`.  The direct source-seal/bare
--     `dyn-id` input is recorded negatively because `dyn-id` is a
--     top-level function-to-★ tag and the source seal representation is
--     not literally ★.
--   * Instance B is the S = ＇Y₂ chain template: the input has the
--     source inert variable cast required by the blocked M3 branch, and
--     the output pairs at the ★ terminus before re-emitting the outer
--     target-only seal.  The old occupied source-star/tagged-target
--     direct witness is now tracked as a D15 migration residual.
--   * This is the positive counterpart to the refuted tag-peel-first
--     family documented in `RightInjInversion2Def`: the head is rebuilt
--     at the target-chain terminus instead of against a right variable.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import TermCtx using (Z)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; id; _↦_; _!)
open import Conversion using (seal; _⊢↓_; ⊢↓-seal)
open import CastTerms
open import Imprecision
import CastTerms as CTerms
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   RebaseAt; rebase-at; same-runtime; store-rep-imp)

------------------------------------------------------------------------
-- Shared tiny values
------------------------------------------------------------------------

dyn-env : ∀ {Δ} → Env∼ Δ
dyn-env _ = X∼★

fun! : ∀ {Δ} → dyn-env {Δ} ⊢ ★ ⇒ ★ ∼ ★
fun! = (id ★ ↦ id ★) !

dyn-id : ∀ {Δ} → Term Δ
dyn-id = (ƛ (` 0)) ⟨ fun! ⟩

dyn-id-⊢ : ∀ {Δ Σ Γ}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ ƛ (` 0) ⦂ ★ ⇒ ★
dyn-id-⊢ = ⊢ƛ (⊢` Z)

dyn-id!-⊢ : ∀ {Δ Σ Γ}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ dyn-id ⦂ ★
dyn-id!-⊢ = ⊢⟨⟩ dyn-id-⊢ fun!

dyn-id-value : ∀ {Δ} → Value (dyn-id {Δ})
dyn-id-value = (CTerms.ƛ (` 0)) CTerms.《 CTerms.inj 》

mono-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → CTI2.ImpEnvMono W W
mono-refl _ eq = eq

------------------------------------------------------------------------
-- Instance A: the S = ★ terminus
------------------------------------------------------------------------

module InstanceA where
  X : TyVar 1
  X = Fin.zero

  Y : TyVar 1
  Y = Fin.zero

  ∀X⇒X₀ : Ty 0
  ∀X⇒X₀ = `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)

  ∀X⇒X : Ty 1
  ∀X⇒X = `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)

  body : Ty 2
  body = ＇ Fin.zero ⇒ ＇ Fin.zero

  source-store : TyStore 1
  source-store = store-bind store-empty ∀X⇒X₀

  target-store : TyStore 1
  target-store = store-bind store-empty ★

  env : ImpEnv 1
  env Fin.zero = X⊑★

  η-id : 1 ↪ᵗ 1
  η-id = keep empty

  -- Placement table:
  --
  --             X   Y
  --   W         0   0

  W : World 1 1 1
  W = world η-id η-id env source-store target-store

  X∈ : source-store ∋ X ⦂ ∀X⇒X
  X∈ = Z∋ refl

  Y∈ : target-store ∋ Y ⦂ ★
  Y∈ = Z∋ refl

  target-env : Env∼ 1
  target-env Fin.zero = X∼★

  Y! : target-env ⊢ ＇ Y ∼ ★
  Y! = id (＇ Y) !

  source-∀⊑★ : ∀X⇒X ⊑ᵂ⟨ W ⟩ ★
  source-∀⊑★ =
    ∀⊑ nonvar-fun (∈-fun-left var-∈)
      (⇒⊑★ (X⊑★ refl) (X⊑★ refl))

  X⊑Y : ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y
  X⊑Y = X⊑X

  X⊑★-W : ＇ X ⊑ᵂ⟨ W ⟩ ★
  X⊑★-W = X⊑★ refl

  X-Y-rep : CTI2.StoreRepImp W X Y
  X-Y-rep = store-rep-imp source-∀⊑★

  rb-X-Y : RebaseAt W W X Y
  rb-X-Y = CTI2.sameWorldRebaseAt refl X-Y-rep

  target-seal-⊢ : target-store Conv.⊢↓[ just Y ] seal Y ★
  target-seal-⊢ = Conv.⊢↓-sealˣ Y∈

  source-seal-⊢ : source-store Conv.⊢↓[ just X ] seal X ∀X⇒X
  source-seal-⊢ = Conv.⊢↓-sealˣ X∈

  target-seal-⊢ᶜ : target-store ⊢↓ seal Y ★
  target-seal-⊢ᶜ = ⊢↓-seal Y∈

  U : Term 1
  U = dyn-id

  target-sealed : Term 1
  target-sealed = U ↓ seal Y ★

  target-tagged : Term 1
  target-tagged = target-sealed ⟨ Y! ⟩

  source : Term 1
  source = (Λ (ƛ (` 0))) ↓ seal X ∀X⇒X

  U-⊢ : ⟨ 1 , target-store , [] ⟩ ⊢ U ⦂ ★
  U-⊢ = dyn-id!-⊢

  target-sealed-⊢ : ⟨ 1 , target-store , [] ⟩ ⊢ target-sealed ⦂ ＇ Y
  target-sealed-⊢ = ⊢conceal target-seal-⊢ᶜ U-⊢

  target-tagged-⊢ : ⟨ 1 , target-store , [] ⟩ ⊢ target-tagged ⦂ ★
  target-tagged-⊢ = ⊢⟨⟩ target-sealed-⊢ Y!

  body-X⊑★ : ＇ Fin.zero ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ ★
  body-X⊑★ = X⊑★ refl

  body⊑★ : body ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ ★
  body⊑★ = ⇒⊑★ body-X⊑★ body-X⊑★

  body⊑★⇒★ :
    body ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ ★ ⇒ ★
  body⊑★⇒★ = ⇒⊑⇒ body-X⊑★ body-X⊑★

  body-fun² :
    CTI2.liftWorldLeft X⊑★ W ∣ [] ⊢²
      ƛ (` 0) ⊑ ƛ (` 0) ∶ body⊑★⇒★
  body-fun² =
    CTI2.ƛ⊑ƛ²
      {A = ＇ Fin.zero} {A′ = ★}
      {pA = body-X⊑★} {pB = body-X⊑★}
      (CTI2.x⊑x² {p = body-X⊑★} CTI2.Zʷ)

  body-U² :
    CTI2.liftWorldLeft X⊑★ W ∣ [] ⊢²
      ƛ (` 0) ⊑ U ∶ body⊑★
  body-U² = CTI2.⊑cast² fun! body-fun² body⊑★

  head-U² : W ∣ [] ⊢² Λ (ƛ (` 0)) ⊑ U ∶ source-∀⊑★
  head-U² =
    CTI2.Λ⊑² nonvar-fun (∈-fun-left var-∈)
      CTI2.liftᴸ-[] (ƛ (` 0)) U-⊢ body-U² source-∀⊑★

  terminus-input-ok-empty : ∀ {Wᵖ : World 1 1 1} {P Xᴿ?}
    → CTI2.SourceConcealOK Wᵖ P (seal X ∀X⇒X) Xᴿ? U
    → ⊥
  terminus-input-ok-empty
      (CTI2.seal-nonstar-plain-ok Rns ())

  terminus-input-empty′ : ∀ {X′}
    → (q : ＇ X′ ⊑ᵂ⟨ W ⟩ ★)
    → W ∣ [] ⊢² source ⊑ U ∶ q
    → ⊥
  terminus-input-empty′ q₀
      (CTI2.⊑cast² {p = p} c′ D .q₀) with p
  terminus-input-empty′ (X⊑★ eq)
      (CTI2.⊑cast² {p = p} c′ D .(X⊑★ eq)) | ()
  terminus-input-empty′ q₀
      (CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ D .q₀) =
    terminus-input-ok-empty ok

  terminus-input-empty : W ∣ [] ⊢² source ⊑ U ∶ X⊑★-W → ⊥
  terminus-input-empty =
    terminus-input-empty′ {X′ = X} X⊑★-W

  output : W ∣ [] ⊢² source ⊑ target-sealed ∶ X⊑Y
  output =
    CTI2.conceal⊑conceal²
      (CTI2.matched-seal-nonstar {Xᴿ? = just Y} nonstar-∀)
      (mono-refl {W = W}) rb-X-Y CTI2.same-[]
      source-seal-⊢ target-seal-⊢ head-U² X⊑Y

  -- The observable tagged premise is available, but the rebuild above
  -- deliberately avoids using this tag-peel-first derivation.
  tagged-input : W ∣ [] ⊢² source ⊑ target-tagged ∶ X⊑★-W
  tagged-input = CTI2.⊑cast² Y! output X⊑★-W

------------------------------------------------------------------------
-- Instance B: the S = ＇Y₂ chain
------------------------------------------------------------------------

module InstanceB where
  X : TyVar 1
  X = Fin.zero

  Y : TyVar 2
  Y = Fin.zero

  Y₂ : TyVar 2
  Y₂ = Fin.suc Fin.zero

  source-store : TyStore 1
  source-store = store-bind store-empty ★

  target-store : TyStore 2
  target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)

  env : ImpEnv 2
  env Fin.zero = X⊑★
  env (Fin.suc Fin.zero) = X⊑★

  η-X-Y : 1 ↪ᵗ 2
  η-X-Y = keep (skip empty)

  η-X-Y₂ : 1 ↪ᵗ 2
  η-X-Y₂ = skip (keep empty)

  η-target : 2 ↪ᵗ 2
  η-target = keep (keep empty)

  -- Placement table:
  --
  --             X   Y   Y₂
  --   W         0   0   1
  --   Wᵖ        1   0   1

  W : World 1 2 2
  W = world η-X-Y η-target env source-store target-store

  Wᵖ : World 1 2 2
  Wᵖ = world η-X-Y₂ η-target env source-store target-store

  X∈ : source-store ∋ X ⦂ ★
  X∈ = Z∋ refl

  Y∈ : target-store ∋ Y ⦂ ＇ Y₂
  Y∈ = Z∋ refl

  Y₂∈ : target-store ∋ Y₂ ⦂ ★
  Y₂∈ = S-bind∋ (Z∋ refl) refl

  source-env : Env∼ 1
  source-env Fin.zero = X∼★

  target-env : Env∼ 2
  target-env Fin.zero = X∼★
  target-env (Fin.suc Fin.zero) = X∼★

  X! : source-env ⊢ ＇ X ∼ ★
  X! = id (＇ X) !

  Y! : target-env ⊢ ＇ Y ∼ ★
  Y! = id (＇ Y) !

  X⊑★-W : ＇ X ⊑ᵂ⟨ W ⟩ ★
  X⊑★-W = X⊑★ refl

  X⊑★-Wᵖ : ＇ X ⊑ᵂ⟨ Wᵖ ⟩ ★
  X⊑★-Wᵖ = X⊑★ refl

  X⊑Y : ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y
  X⊑Y = X⊑X

  X⊑Y₂ : ＇ X ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y₂
  X⊑Y₂ = X⊑X

  X-Y-rep : CTI2.StoreRepImp W X Y
  X-Y-rep = store-rep-imp ★⊑★

  X-Y₂-rep : CTI2.StoreRepImp Wᵖ X Y₂
  X-Y₂-rep = store-rep-imp ★⊑★

  rb-X-Y : RebaseAt W W X Y
  rb-X-Y = CTI2.sameWorldRebaseAt refl X-Y-rep

  rb-X-Y₂ : RebaseAt Wᵖ Wᵖ X Y₂
  rb-X-Y₂ = CTI2.sameWorldRebaseAt refl X-Y₂-rep

  rb-chain : RebaseAt Wᵖ W X Y
  rb-chain =
    rebase-at (same-runtime refl refl)
      (λ { {Fin.zero} X≢ → ⊥-elim (X≢ refl) })
      (λ _ → refl) refl X-Y-rep

  mono-W-Wᵖ : CTI2.ImpEnvMono W Wᵖ
  mono-W-Wᵖ Fin.zero eq = eq
  mono-W-Wᵖ (Fin.suc Fin.zero) eq = eq

  source-seal-⊢ : source-store Conv.⊢↓[ just X ] seal X ★
  source-seal-⊢ = Conv.⊢↓-sealˣ X∈

  target-Y-seal-⊢ :
    target-store Conv.⊢↓[ just Y ] seal Y (＇ Y₂)
  target-Y-seal-⊢ = Conv.⊢↓-sealˣ Y∈

  target-Y₂-seal-⊢ : target-store Conv.⊢↓[ just Y₂ ] seal Y₂ ★
  target-Y₂-seal-⊢ = Conv.⊢↓-sealˣ Y₂∈

  source-seal-⊢ᶜ : source-store ⊢↓ seal X ★
  source-seal-⊢ᶜ = ⊢↓-seal X∈

  target-Y-seal-⊢ᶜ : target-store ⊢↓ seal Y (＇ Y₂)
  target-Y-seal-⊢ᶜ = ⊢↓-seal Y∈

  target-Y₂-seal-⊢ᶜ : target-store ⊢↓ seal Y₂ ★
  target-Y₂-seal-⊢ᶜ = ⊢↓-seal Y₂∈

  V₀ : Term 1
  V₀ = dyn-id

  V : Term 1
  V = V₀ ↓ seal X ★

  source-payload : Term 1
  source-payload = V ⟨ X! ⟩

  source : Term 1
  source = source-payload ↓ seal X ★

  U₀ : Term 2
  U₀ = dyn-id

  U : Term 2
  U = U₀ ↓ seal Y₂ ★

  target-chain : Term 2
  target-chain = U ↓ seal Y (＇ Y₂)

  target-tagged : Term 2
  target-tagged = target-chain ⟨ Y! ⟩

  U₀-⊢ : ⟨ 2 , target-store , [] ⟩ ⊢ U₀ ⦂ ★
  U₀-⊢ = dyn-id!-⊢

  U-⊢ : ⟨ 2 , target-store , [] ⟩ ⊢ U ⦂ ＇ Y₂
  U-⊢ = ⊢conceal target-Y₂-seal-⊢ᶜ U₀-⊢

  target-chain-⊢ : ⟨ 2 , target-store , [] ⟩ ⊢ target-chain ⦂ ＇ Y
  target-chain-⊢ = ⊢conceal target-Y-seal-⊢ᶜ U-⊢

  target-tagged-⊢ : ⟨ 2 , target-store , [] ⟩ ⊢ target-tagged ⦂ ★
  target-tagged-⊢ = ⊢⟨⟩ target-chain-⊢ Y!

  base² : Wᵖ ∣ [] ⊢² V₀ ⊑ U₀ ∶ ★⊑★
  base² =
    CTI2.cast⊑cast² fun! fun!
      (CTI2.ƛ⊑ƛ²
        {A = ★} {A′ = ★} {pA = ★⊑★} {pB = ★⊑★}
        (CTI2.x⊑x² {p = ★⊑★} CTI2.Zʷ))
      ★⊑★

  premise-chain² : W ∣ [] ⊢² V ⊑ target-chain ∶ X⊑Y
  premise-chain² =
    CTI2.⊑conceal² mono-W-Wᵖ (CTI2.rebase-varᴿ rb-chain)
      CTI2.same-[] target-Y-seal-⊢
      (CTI2.conceal⊑conceal²
        (CTI2.matched-seal-star-partner {Xᴿ? = just Y₂}
          (CTI2.rep★-nonvar-tag nonvar-fun))
        (mono-refl {W = Wᵖ}) rb-X-Y₂
        CTI2.same-[]
        source-seal-⊢ target-Y₂-seal-⊢ base² X⊑Y₂)
      X⊑Y

  premise-casts² :
    W ∣ [] ⊢² source-payload ⊑ target-tagged ∶ ★⊑★
  premise-casts² =
    CTI2.cast⊑cast² X! Y! premise-chain² ★⊑★

  -- D15 M1 residual: the old checked `tagged-input` used the removed
  -- occupied source-star/name-protected source-only route.  The matched
  -- chain pieces above remain checked; reassembling this tagged endpoint
  -- needs the later source-star package migration.
