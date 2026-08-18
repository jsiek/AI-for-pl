module proof.DGG.Inversion.TargetChainProof where

-- File Charter:
--   * Proves the checked source-star-at and source-star-chain inhabitants
--     for the target walk surface.
--   * Imports only the Set-level Def module and the shared proven support.
--   * Contains no target-tag-seal-walk clauses.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
  renaming (subst to subst≡)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; id; _!; sym∼)
open import Conversion using (seal; _↦↓_; `∀↓_)
open import CastTerms
open import Imprecision
open import Primitives using (κℕ; κ𝔹)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.SealTransferCore as STC
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.Occupancy as Occ
open import proof.DGG.Inversion.SpineValueDef using
  (sv-cast; sv-seal; sv-reveal-fun; sv-reveal-all; varv-seal;
   var-tag-value-sealed; var-value-view)
open import proof.DGG.Inversion.TargetWalkDef using
  (TargetSourceStarAt; TargetSourceStarChain; TargetSourceStarChainResult;
   target-source-star-final; target-source-star-residual;
   target-source-star-var-residual; target-source-star-paired;
   target-source-star-payload;
   target-source-star-chain-final; target-source-star-chain-residual;
   target-source-star-chain-paired; target-source-star-chain-payload)
open import proof.DGG.Inversion.TargetWalkSupport using
  (composeOuterRebase; composeSamePivotRebase; impEnvMono-∘;
   inner-source-pivot-eq;
   rebase-source-membership; sameCtx-∘; star-source-nonstar-⊥;
   star-store-rep; store-lookup-unique; target-seal-rebase-source;
   var-source-nonstar-⊥)
open CTI2 using (_∣_⊢²_⊑_∶_; _⊑ᵂ⟨_⟩_)

pattern st-stripped W₂ γ₂ link mono sc q D =
  STC.seal-transfer-stripped {W₂ = W₂} {γ₂ = γ₂} {q₂ = q}
    link mono sc D

target-source-star-at : TargetSourceStarAt
target-source-star-at {V = M ⦂∀ C [ A ]} ()
    inert vU X∈ Y∈ D
target-source-star-at {W = W} {X = X} {Y = Y}
    {c = c} {q = q} (sv-cast sv₀ ()) inert vU X∈ Y∈
    (CTI2.cast⊑² c₁ prem .q)
target-source-star-at {W = W} {X = X} {Y = Y}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑² {W′ = Wᵖ} {p = p} ok mono rb sc
      (CTI2.⊢↓-sealˣ X∈′) prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-X)
target-source-star-at {W = W} {X = X} {Y = Y}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑²-source-ok {W′ = Wᵖ} {p = p}
      ok mono rb sc (CTI2.⊢↓-sealˣ X∈′) prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-X)
target-source-star-at {W = W} {X = X} {S = ＇ Y₂}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono rb sc (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y₂}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y₂)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-X)
target-source-star-at {W = W} {X = X} {S = ‵ ι}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono rb sc (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ‵ ι}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ‵ ι)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-ι)
target-source-star-at {W = W} {X = X} {S = A ⇒ B}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono rb sc (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = A ⇒ B}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ A ⇒ B)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-⇒)
target-source-star-at {W = W} {X = X} {S = `∀ A}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono rb sc (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = `∀ A}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ `∀ A)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-∀)
target-source-star-at {X = X} {S = ★} {c = c} {q = q}
    sv (inj ⦃ Gᵍ = ＇ .X ⦄) vU X∈ Y∈ D
    with STC.seal-transfer sv vU X∈ D
target-source-star-at {S = ★} {c = c} {q = q} sv inert vU X∈ Y∈ D
    | STC.seal-transfer-paired {P = P}
        monoᵖ rbᵖ scᵖ source⊢ target⊢ partner prem =
  target-source-star-paired refl monoᵖ rbᵖ scᵖ X∈ Y∈ partner prem
target-source-star-at {V = ƛ N} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    with CTI2T.source-typing² D₂
target-source-star-at {V = ƛ N} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ | ()
target-source-star-at {V = Λ V} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    with CTI2T.source-typing² D₂
target-source-star-at {V = Λ V} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ | ()
target-source-star-at {V = $ (κℕ n)} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    with CTI2T.source-typing² D₂
target-source-star-at {V = $ (κℕ n)} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ | ()
target-source-star-at {V = $ (κ𝔹 b)} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    with CTI2T.source-typing² D₂
target-source-star-at {V = $ (κ𝔹 b)} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ | ()
target-source-star-at {V = V ⟨ c₁ ⟩} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    with CTI2T.source-typing² D₂
target-source-star-at {V = V ⟨ c₁ ⟩} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    | ⊢⟨⟩ V⊢ .c₁
    with sv
target-source-star-at {V = V ⟨ c₁ ⟩} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    | ⊢⟨⟩ V⊢ .c₁ | sv-cast sv₀ ()
target-source-star-at {V = V ↑ c₁} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    with sv
target-source-star-at {V = V ↑ c₁} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    | sv-reveal-fun sv₀
    with CTI2T.source-typing² D₂
target-source-star-at {V = V ↑ c₁} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    | sv-reveal-fun sv₀ | ()
target-source-star-at {V = V ↑ c₁} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    | sv-reveal-all sv₀
    with CTI2T.source-typing² D₂
target-source-star-at {V = V ↑ c₁} {S = ★} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    | sv-reveal-all sv₀ | ()
target-source-star-at {V = V ↓ (c₁ ↦↓ d₁)} {S = ★}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    with CTI2T.source-typing² D₂
target-source-star-at {V = V ↓ (c₁ ↦↓ d₁)} {S = ★}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ | ()
target-source-star-at {V = V ↓ `∀↓ d₁} {S = ★}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    with CTI2T.source-typing² D₂
target-source-star-at {V = V ↓ `∀↓ d₁} {S = ★}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ | ()
target-source-star-at {X = X} {S = ★} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²-seal-star-open no-target monoᵖ rbᵖ scᵖ
        (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂) =
  target-source-star-payload refl mono₂ link sc₂ X∈ Y∈ D₂
target-source-star-at {X = X} {S = ★} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²-source-ok
        (CTI2.seal-nonstar-plain-ok {R = R} Rns nt)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    with store-lookup-unique X∈ᵖ (rebase-source-membership link X∈)
target-source-star-at {X = X} {S = ★} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²-source-ok
        (CTI2.seal-nonstar-plain-ok {R = R} Rns nt)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    | refl
    with Rns
target-source-star-at {X = X} {S = ★} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²-source-ok
        (CTI2.seal-nonstar-plain-ok Rns nt)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    | refl
    | ()
target-source-star-at {X = X} {S = ★} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²-source-ok
        (CTI2.seal-nonstar-name-protected-ok {R = R} Rns aligned)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    with store-lookup-unique X∈ᵖ (rebase-source-membership link X∈)
target-source-star-at {X = X} {S = ★} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²-source-ok
        (CTI2.seal-nonstar-name-protected-ok {R = R} Rns aligned)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    | refl
    with Rns
target-source-star-at {X = X} {S = ★} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²-source-ok
        (CTI2.seal-nonstar-name-protected-ok Rns aligned)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    | refl
    | ()
target-source-star-at {X = X} {S = ★} {c = c} {q = q}
    sv (inj ⦃ Gᵍ = ＇ .X ⦄) vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok
          (CTI2.star-rep-target no-target (CTI2.rep★-untagged nt)))
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    with store-lookup-unique X∈ᵖ (rebase-source-membership link X∈)
target-source-star-at {X = X} {S = ★} {c = c} {q = q}
    sv (inj ⦃ Gᵍ = ＇ .X ⦄) vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok
          (CTI2.star-rep-target no-target (CTI2.rep★-untagged nt)))
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    | refl
    =
  target-source-star-final
    (CTI2.conceal⊑conceal²
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-round-trip (CTI2.rep★-untagged nt)))
      mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.cast⊑² c D₂ ★⊑★) q)
target-source-star-at {X = X} {S = ★} {c = c} {q = q}
    sv (inj ⦃ Gᵍ = ＇ .X ⦄) vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok
          (CTI2.star-rep-target no-target (CTI2.rep★-nonvar-tag Gnv)))
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    with store-lookup-unique X∈ᵖ (rebase-source-membership link X∈)
target-source-star-at {X = X} {S = ★} {c = c} {q = q}
    sv (inj ⦃ Gᵍ = ＇ .X ⦄) vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok
          (CTI2.star-rep-target no-target (CTI2.rep★-nonvar-tag Gnv)))
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    | refl
    =
  target-source-star-final
    (CTI2.conceal⊑conceal²
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-round-trip (CTI2.rep★-nonvar-tag Gnv)))
      mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.cast⊑² c D₂ ★⊑★) q)
target-source-star-at {X = X} {S = ★} {c = c} {q = q}
    sv (inj ⦃ Gᵍ = ＇ .X ⦄) vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok
          (CTI2.star-rep-target no-target
            (CTI2.rep★-matched-inner-tags X₂≢X aligned)))
        monoᵖ (CTI2.tag-rebase-varᴸ rbᵖ) scᵖ
        (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    with store-lookup-unique X∈ᵖ (rebase-source-membership link X∈)
target-source-star-at {X = X} {S = ★} {c = c} {q = q}
    sv (inj ⦃ Gᵍ = ＇ .X ⦄) vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok
          (CTI2.star-rep-target no-target
            (CTI2.rep★-matched-inner-tags X₂≢X aligned)))
        monoᵖ (CTI2.tag-rebase-varᴸ rbᵖ) scᵖ
        (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    | refl
    =
  target-source-star-final
    (CTI2.conceal⊑conceal²
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-round-trip
          (CTI2.rep★-matched-inner-tags X₂≢X
            (STC.transport-non-pivot-aligned rbᵖ X₂≢X aligned))))
      mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.cast⊑² c D₂ ★⊑★) q)
target-source-star-at {S = ★} {q = q} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok
          (CTI2.star-rep-target no-target
            (CTI2.rep★-var-tag aligned)))
        monoᵖ (CTI2.tag-rebase-varᴸ rbᵖ) scᵖ
        (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂) =
  target-source-star-payload refl
    mono₂ link sc₂ X∈ Y∈ D₂
target-source-star-at {S = ★} {c = c} {q = q} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok
          (CTI2.star-rep-target no-target
            (CTI2.rep★-round-trip partner)))
        monoᵖ (CTI2.tag-rebase-varᴸ rbᵖ) scᵖ
        (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂) =
  target-source-star-payload refl
    mono₂ link sc₂ X∈ Y∈ D₂
target-source-star-at {X = X} {S = ★} {c = c} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok
          (CTI2.star-rep-target no-target
            (CTI2.rep★-round-trip partner)))
        monoᵖ rbᵖ@(CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
        scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    =
  target-source-star-final
    (STC.emit-tagged-transfer mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (STC.tagged-transfer-output
        (CTI2.cast⊑² c D₂ ★⊑★)
        (STC.premise-partner-from-tag-rebase rbᵖ)
        (CTI2.matched-seal-star-partner
          (CTI2.rep★-round-trip {cX = id (＇ X)}
            (STC.transport-rep★-partner-ok-tag rbᵖ
              (CTI2.rep★-round-trip partner)))))
      (CTI2.conceal⊑²-seal-star-open
        (Occ.tag-rebase-no-target-forwardᴼ rbᵖ no-target)
        (STC.impEnvMono-refl {W = W₂})
        (STC.self-tag-rebase-from-tag-rebase rbᵖ)
        (STC.sameCtx-refl {γ = γ₂})
        (CTI2.⊢↓-sealˣ X∈ᵖ)
        (CTI2.cast⊑² c D₂ ★⊑★)
        q₂))
target-source-star-at {S = ★} {q = q} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        ok@(CTI2.seal-partner-ok CTI2.name-protected-target)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    with store-lookup-unique X∈ᵖ (rebase-source-membership link X∈)
target-source-star-at {S = ★} {q = q} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        ok@(CTI2.seal-partner-ok CTI2.name-protected-target)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂)
    | refl =
  target-source-star-payload refl mono₂ link sc₂ X∈ Y∈ D₂
target-source-star-at {S = ★} {c = c} {q = q} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.conceal⊑²
        (CTI2.seal-partner-ok (CTI2.plain-target nt))
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈ᵖ) prem .q₂) =
  target-source-star-final
    (CTI2.conceal⊑conceal²
      (CTI2.matched-seal-star-partner (CTI2.rep★-untagged nt))
      mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.cast⊑² c D₂ ★⊑★) q)
target-source-star-at
    {U = U ⟨ _! ⦃ Gᵍ = ‵ ι ⦄ cᴿ ⟩} {S = ★} {c = c} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ =
  target-source-star-final
    (CTI2.conceal⊑conceal²
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-nonvar-tag nonvar-base))
      mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.cast⊑² c D₂ ★⊑★) q)
target-source-star-at
    {U = U ⟨ _! ⦃ Gᵍ = ★⇒★ ⦄ cᴿ ⟩} {S = ★} {c = c}
    {q = q} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ =
  target-source-star-final
    (CTI2.conceal⊑conceal²
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-nonvar-tag nonvar-fun))
      mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.cast⊑² c D₂ ★⊑★) q)
target-source-star-at
    {U = U ⟨ _! ⦃ Gᵍ = ∀★ ⦄ cᴿ ⟩} {S = ★} {c = c}
    {q = q} sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ =
  target-source-star-final
    (CTI2.conceal⊑conceal²
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-nonvar-tag nonvar-all))
      mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.cast⊑² c D₂ ★⊑★) q)
target-source-star-at {U = U ⟨ id A ⟩} {S = ★}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    with vU
target-source-star-at {U = U ⟨ id A ⟩} {S = ★}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂
    | vU₀ Value.《 () 》
target-source-star-at {U = U ↑ cᴿ} {S = ★} {c = c} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ =
  target-source-star-final
    (CTI2.conceal⊑conceal²
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-untagged CTI2.not-↑))
      mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.cast⊑² c D₂ ★⊑★) q)
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = Ansᴿ ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    with SPT.var-consistency-view (sym∼ cᴿ)
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = Ansᴿ ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    | inj₁ refl
    with var-tag-value-sealed vU (CTI2T.target-typing² D₂)
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = Ansᴿ ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    | inj₁ refl
    | varv-seal {W = U₀} vU₀ Y₂∈ refl
    with SPT.right-var-obligation-view {W = W₂} {Y = Y₂} p₂
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = Ansᴿ ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    | inj₁ refl
    | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | ._ , refl , aligned
    with target-source-star-at (sv-seal sv₀) inert vU₀
      (rebase-source-membership link X∈) Y₂∈ prem
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = Ansᴿ ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    | inj₁ refl
    | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | ._ , refl , aligned
    | target-source-star-final sourcePrem =
  target-source-star-final
    (STC.emit-tagged-transfer mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (STC.tagged-transfer-output
        (CTI2.cast⊑² c D₂ ★⊑★)
        (STC.premise-partner-just aligned)
        (CTI2.matched-seal-star-partner
          (CTI2.rep★-var-tag aligned)))
      (CTI2.⊑cast² cᴿ! sourcePrem q₂))
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = Ansᴿ ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    | inj₁ refl
    | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | ._ , refl , aligned
    | target-source-star-residual refl X∈ᵒ Y₂∈ᵒ rbᵒ residualᵒ =
  target-source-star-final
    (STC.emit-tagged-transfer mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (STC.tagged-transfer-output
        (CTI2.cast⊑² c D₂ ★⊑★)
        (STC.premise-partner-just aligned)
        (CTI2.matched-seal-star-partner
          (CTI2.rep★-var-tag aligned)))
      (CTI2.conceal⊑²
        (CTI2.seal-partner-ok CTI2.name-protected-target)
        (STC.impEnvMono-refl {W = W₂})
        (CTI2.tag-rebase-varᴸ
          rbᵒ)
        (STC.sameCtx-refl {γ = γ₂})
        (CTI2.⊢↓-sealˣ X∈ᵒ)
        (CTI2.cast⊑cast² c cᴿ! residualᵒ ★⊑★)
        q₂))
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = Ansᴿ ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    | inj₁ refl
    | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | ._ , refl , aligned
    | target-source-star-var-residual refl X∈ᵒ Y₂∈ᵒ rbᵒ residualᵒ =
  target-source-star-final
    (STC.emit-tagged-transfer mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (STC.tagged-transfer-output
        (CTI2.cast⊑² c D₂ ★⊑★)
        (STC.premise-partner-just aligned)
        (CTI2.matched-seal-star-partner
          (CTI2.rep★-var-tag aligned)))
      (CTI2.conceal⊑²
        (CTI2.seal-partner-ok CTI2.name-protected-target)
        (STC.impEnvMono-refl {W = W₂})
        (CTI2.tag-rebase-varᴸ rbᵒ)
        (STC.sameCtx-refl {γ = γ₂})
        (CTI2.⊢↓-sealˣ X∈ᵒ)
        (CTI2.cast⊑cast² c cᴿ! residualᵒ ★⊑★)
        q₂))
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = Ansᴿ ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    | inj₁ refl
    | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | ._ , refl , aligned
    | target-source-star-paired refl monoᵒ rbᵒ scᵒ X∈ᵒ Y₂∈ᵒ
        partnerᵒ premᵒ =
  target-source-star-final
    (STC.emit-tagged-transfer mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (STC.tagged-transfer-output
        (CTI2.cast⊑² c D₂ ★⊑★)
        (STC.premise-partner-just aligned)
        (CTI2.matched-seal-star-partner
          (CTI2.rep★-var-tag aligned)))
      (CTI2.conceal⊑²
        (CTI2.seal-partner-ok CTI2.name-protected-target)
        (STC.impEnvMono-refl {W = W₂})
        (CTI2.tag-rebase-varᴸ
          (CTI2.sameWorldRebaseAt aligned
            (CTI2.RebaseAt.storeRepresentations rbᵒ)))
        (STC.sameCtx-refl {γ = γ₂})
        (CTI2.⊢↓-sealˣ X∈ᵒ)
        (CTI2.cast⊑cast² c cᴿ!
          (CTI2.conceal⊑conceal² partnerᵒ monoᵒ rbᵒ scᵒ
            (CTI2.⊢↓-sealˣ X∈ᵒ) (CTI2.⊢↓-sealˣ Y₂∈ᵒ)
            premᵒ p₂)
          ★⊑★)
        q₂))
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = Ansᴿ ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    | inj₁ refl
    | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | ._ , refl , aligned
    | target-source-star-payload refl monoᵒ rbᵒ scᵒ X∈ᵒ Y₂∈ᵒ
        sourcePremᵒ =
  target-source-star-final
    (STC.emit-tagged-transfer mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (STC.tagged-transfer-output
        (CTI2.cast⊑² c D₂ ★⊑★)
        (STC.premise-partner-just aligned)
        (CTI2.matched-seal-star-partner
          (CTI2.rep★-var-tag aligned)))
      (CTI2.conceal⊑²
        (CTI2.seal-partner-ok CTI2.name-protected-target)
        (STC.impEnvMono-refl {W = W₂})
        (CTI2.tag-rebase-varᴸ
          (CTI2.sameWorldRebaseAt aligned
            (CTI2.RebaseAt.storeRepresentations rbᵒ)))
        (STC.sameCtx-refl {γ = γ₂})
        (CTI2.⊢↓-sealˣ X∈ᵒ)
        (CTI2.cast⊑cast² c cᴿ!
          (CTI2.⊑conceal² monoᵒ (CTI2.rebase-varᴿ rbᵒ) scᵒ
            (CTI2.⊢↓-sealˣ Y₂∈ᵒ) sourcePremᵒ p₂)
          ★⊑★)
        q₂))
target-source-star-at
    {V = V ↓ x}
    {U = U ⟨ _! ⦃ Gᵍ = ＇ Y₂ ⦄ cᴿ ⦃ Ans = () ⦄ ⟩}
    {S = ★} {c = c} {q = q} (sv-seal sv₀) inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂
      D₂@(CTI2.⊑cast² {p = p₂} cᴿ! prem .q₂)
    | inj₂ refl
target-source-star-at {U = U ↓ cᴿ} {S = ★} {c = c} {q = q}
    sv inert vU X∈ Y∈ D
    | st-stripped W₂ γ₂ link mono₂ sc₂ q₂ D₂ =
  target-source-star-final
    (CTI2.conceal⊑conceal²
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-untagged CTI2.not-↓))
      mono₂ link sc₂
      (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.cast⊑² c D₂ ★⊑★) q)
target-source-star-at {W = W} {X = X} {Y = Y} {S = ＇ Y₂}
    {c = c} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ Y∈′) prem .q)
    with target-seal-rebase-source rbᴿ q
target-source-star-at {W = W} {X = X} {Y = Y} {S = ＇ Y₂}
    {c = c} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ Y∈′) prem .q)
    | link
    with var-value-view vU (CTI2T.target-typing² prem)
target-source-star-at {W = W} {X = X} {Y = Y} {S = ＇ Y₂}
    {c = c} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ Y∈′) prem .q)
    | link | varv-seal {W = U₀} vU₀ Y₂∈ refl
    with target-source-star-at sv inert vU₀
      (rebase-source-membership link X∈) Y₂∈ prem
target-source-star-at {W = W} {X = X} {Y = Y} {S = ＇ Y₂}
    {c = c} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ Y∈′) prem .q)
    | link | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-final sourcePrem =
  target-source-star-final
    (CTI2.⊑conceal² mono rbᴿ sc (CTI2.⊢↓-sealˣ Y∈)
      sourcePrem q)
target-source-star-at {W = W} {X = X} {Y = Y} {S = ＇ Y₂}
    {c = c} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ Y∈′) prem .q)
    | link | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-residual refl X∈ᵒ Y₂∈ᵒ rbᵒ residualᵒ =
  target-source-star-var-residual refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned link)
      (CTI2.RebaseAt.storeRepresentations link))
    (CTI2.⊑conceal² mono rbᴿ sc (CTI2.⊢↓-sealˣ Y∈)
      residualᵒ q)
target-source-star-at {W = W} {X = X} {Y = Y} {S = ＇ Y₂}
    {c = c} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ Y∈′) prem .q)
    | link | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-var-residual refl X∈ᵒ Y₂∈ᵒ rbᵒ residualᵒ =
  target-source-star-var-residual refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned link)
      (CTI2.RebaseAt.storeRepresentations link))
    (CTI2.⊑conceal² mono rbᴿ sc (CTI2.⊢↓-sealˣ Y∈)
      residualᵒ q)
target-source-star-at {W = W} {X = X} {Y = Y} {S = ＇ Y₂}
    {c = c} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ Y∈′) prem .q)
    | link | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-paired refl monoᵒ rbᵒ scᵒ X∈ᵒ Y₂∈ᵒ
        partnerᵒ premᵒ =
  target-source-star-var-residual refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned link)
      (CTI2.RebaseAt.storeRepresentations link))
    (CTI2.⊑conceal² mono rbᴿ sc (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.conceal⊑conceal² partnerᵒ monoᵒ rbᵒ scᵒ
        (CTI2.⊢↓-sealˣ X∈ᵒ) (CTI2.⊢↓-sealˣ Y₂∈ᵒ)
        premᵒ pᵈ)
      q)
target-source-star-at {W = W} {X = X} {Y = Y} {S = ＇ Y₂}
    {c = c} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ Y∈′) prem .q)
    | link | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-payload refl monoᵒ rbᵒ scᵒ X∈ᵒ Y₂∈ᵒ
        sourcePremᵒ =
  target-source-star-var-residual refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned link)
      (CTI2.RebaseAt.storeRepresentations link))
    (CTI2.⊑conceal² mono rbᴿ sc (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.⊑conceal² monoᵒ (CTI2.rebase-varᴿ rbᵒ) scᵒ
        (CTI2.⊢↓-sealˣ Y₂∈ᵒ) sourcePremᵒ pᵈ)
      q)
target-source-star-at {X = X} {S = ‵ ι} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = p}
      mono rbᴿ sc target⊢ prem .q) =
  ⊥-elim
    (var-source-nonstar-⊥ {W = Wᵈ} {X = X} {S = ‵ ι}
      p nonvar-base nonstar-ι)
target-source-star-at {X = X} {S = A ⇒ B} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = p}
      mono rbᴿ sc target⊢ prem .q) =
  ⊥-elim
    (var-source-nonstar-⊥ {W = Wᵈ} {X = X} {S = A ⇒ B}
      p nonvar-fun nonstar-⇒)
target-source-star-at {X = X} {S = `∀ A} {q = q} sv inert vU X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {p = p}
      mono rbᴿ sc target⊢ prem .q) =
  ⊥-elim
    (var-source-nonstar-⊥ {W = Wᵈ} {X = X} {S = `∀ A}
      p nonvar-all nonstar-∀)

target-source-star-chain-wrap-target : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {γ′ : CTI2.CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y Y₂ Y₃ : TyVar Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
    {p : (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ (＇ Y₂)}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → CTI2.ImpEnvMono W W′
  → CTI2.RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → CTI2.sourceStoreʷ W ∋ Xᴸ ⦂ ★
  → CTI2.targetStoreʷ W ∋ Y ⦂ (＇ Y₂)
  → TargetSourceStarChainResult W′ γ′ V U Xᴸ X₂ Y₂ Y₃ c p
  → TargetSourceStarChainResult W γ V (U ↓ seal Y₂ (＇ Y₃))
      Xᴸ X₂ Y Y₂ c q
target-source-star-chain-wrap-target {W = W} {W′ = W′}
    {γ = γ} {γ′ = γ′} {V = V} {U = U} {Xᴸ = Xᴸ}
    {Y = Y} {Y₂ = Y₂} {Y₃ = Y₃} {q = q}
    mono rb sc X∈ Y∈ (target-source-star-chain-final final) =
  target-source-star-chain-final
    (CTI2.⊑conceal² mono (CTI2.rebase-varᴿ rb) sc
      (CTI2.⊢↓-sealˣ Y∈) final q)
target-source-star-chain-wrap-target {W = W} {W′ = W′}
    {γ = γ} {γ′ = γ′} {V = V} {U = U} {Xᴸ = Xᴸ}
    {Y = Y} {Y₂ = Y₂} {Y₃ = Y₃} {q = q}
    mono rb sc X∈ Y∈
    (target-source-star-chain-residual refl X∈′ Y₂∈′ rb′ residual) =
  target-source-star-chain-residual refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned rb)
      (CTI2.RebaseAt.storeRepresentations rb))
    (CTI2.⊑conceal² mono (CTI2.rebase-varᴿ rb) sc
      (CTI2.⊢↓-sealˣ Y∈) residual q)
target-source-star-chain-wrap-target {W = W} {W′ = W′}
    {γ = γ} {γ′ = γ′} {V = V} {U = U} {Xᴸ = Xᴸ}
    {Y = Y} {Y₂ = Y₂} {Y₃ = Y₃} {q = q}
    mono rb sc X∈ Y∈
    (target-source-star-chain-paired {Wᵖ = Wᵖ} refl X∈′ Y₂∈′ rb′
      residual monoᵖ rbᵖ scᵖ partner prem) =
  target-source-star-chain-paired refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned rb)
      (CTI2.RebaseAt.storeRepresentations rb))
    (CTI2.⊑conceal² mono (CTI2.rebase-varᴿ rb) sc
      (CTI2.⊢↓-sealˣ Y∈) residual q)
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵖ} mono monoᵖ)
    (composeOuterRebase rb rbᵖ)
    (sameCtx-∘ sc scᵖ)
    partner prem
target-source-star-chain-wrap-target {W = W} {W′ = W′}
    {γ = γ} {γ′ = γ′} {V = V} {U = U} {Xᴸ = Xᴸ}
    {Y = Y} {Y₂ = Y₂} {Y₃ = Y₃} {q = q}
    mono rb sc X∈ Y∈
    (target-source-star-chain-payload {Wᵖ = Wᵖ} refl X∈′ Y₂∈′ rb′
      residual monoᵖ rbᵖ scᵖ sourcePrem) =
  target-source-star-chain-payload refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned rb)
      (CTI2.RebaseAt.storeRepresentations rb))
    (CTI2.⊑conceal² mono (CTI2.rebase-varᴿ rb) sc
      (CTI2.⊢↓-sealˣ Y∈) residual q)
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵖ} mono monoᵖ)
    (composeOuterRebase rb rbᵖ)
    (sameCtx-∘ sc scᵖ)
    sourcePrem

target-source-star-chain : TargetSourceStarChain
target-source-star-chain {V = M ⦂∀ C [ A ]} ()
    inert vU mono ra sc X∈ Y∈ D
target-source-star-chain {V = V ⟨ c₁ ⟩} (sv-cast sv₀ ())
    inert vU mono ra sc X∈ Y∈ (CTI2.cast⊑² .c₁ prem p₂)
target-source-star-chain {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {p₂ = p₂} {q = q}
    (sv-seal sv₀) inert vU mono ra sc X∈ Y∈
    (CTI2.conceal⊑² {W′ = Wᵖ} {p = p} ok mono₁ rb₁ sc₁
      (CTI2.⊢↓-sealˣ X∈′) prem .p₂)
    with inner-source-pivot-eq ra q p₂
target-source-star-chain {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y} {p₂ = p₂} {q = q}
    (sv-seal sv₀) inert vU mono ra sc X∈ Y∈
    (CTI2.conceal⊑² {W′ = Wᵖ} {p = p} ok mono₁ rb₁ sc₁
      (CTI2.⊢↓-sealˣ X∈′) prem .p₂)
    | refl =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y)
        (store-lookup-unique X∈′ (rebase-source-membership ra X∈)) p)
      nonstar-X)
target-source-star-chain {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {p₂ = p₂} {q = q}
    (sv-seal sv₀) inert vU mono ra sc X∈ Y∈
    (CTI2.conceal⊑²-source-ok {W′ = Wᵖ} {p = p}
      ok mono₁ rb₁ sc₁ (CTI2.⊢↓-sealˣ X∈′) prem .p₂)
    with inner-source-pivot-eq ra q p₂
target-source-star-chain {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y} {p₂ = p₂} {q = q}
    (sv-seal sv₀) inert vU mono ra sc X∈ Y∈
    (CTI2.conceal⊑²-source-ok {W′ = Wᵖ} {p = p}
      ok mono₁ rb₁ sc₁ (CTI2.⊢↓-sealˣ X∈′) prem .p₂)
    | refl =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y)
        (store-lookup-unique X∈′ (rebase-source-membership ra X∈)) p)
      nonstar-X)
target-source-star-chain {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y₂ = Y₂} {p₂ = p₂} {q = q}
    (sv-seal sv₀) inert vU mono ra sc X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono₁ rb₁ sc₁ (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .p₂)
    with inner-source-pivot-eq ra q p₂
target-source-star-chain {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y₂ = Y₂} {p₂ = p₂} {q = q}
    (sv-seal sv₀) inert vU mono ra sc X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono₁ rb₁ sc₁ (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .p₂)
    | refl =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y₂}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y₂)
        (store-lookup-unique X∈′ (rebase-source-membership ra X∈)) p)
      nonstar-X)
target-source-star-chain {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y}
    {Y₂ = Y₂} {c = c} {p₂ = p₂} {q = q}
    sv inert vU mono ra sc X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono₁ rbᴿ sc₁ (CTI2.⊢↓-sealˣ Y∈′) prem .p₂)
    with inner-source-pivot-eq ra q p₂
target-source-star-chain {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {Xᴸ = Xᴸ} {Y = Y}
    {Y₂ = Y₂} {c = c} {p₂ = p₂} {q = q}
    sv inert vU mono ra sc X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono₁ rbᴿ sc₁ (CTI2.⊢↓-sealˣ Y∈′) prem ._)
    | refl
    with target-seal-rebase-source rbᴿ p₂
target-source-star-chain {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {Xᴸ = Xᴸ} {Y = Y}
    {Y₂ = Y₂} {c = c} {p₂ = p₂} {q = q}
    sv inert vU mono ra sc X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono₁ rbᴿ sc₁ (CTI2.⊢↓-sealˣ Y∈′) prem ._)
    | refl | link₁
    with var-value-view vU (CTI2T.target-typing² prem)
target-source-star-chain {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {Xᴸ = Xᴸ} {Y = Y} {Y₂ = Y₂}
    {c = c} {p₂ = p₂} {q = q} sv inert vU mono ra sc X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono₁ rbᴿ sc₁ (CTI2.⊢↓-sealˣ Y∈′) prem ._)
    | refl | link₁ | varv-seal {W = U₀} vU₀ Y₂∈ refl
    with target-source-star-at sv inert vU₀
      (rebase-source-membership (composeSamePivotRebase ra link₁) X∈)
      Y₂∈ prem
target-source-star-chain {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {Xᴸ = Xᴸ} {Y = Y} {Y₂ = Y₂}
    {c = c} {p₂ = p₂} {q = q} sv inert vU mono ra sc X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono₁ rbᴿ sc₁ (CTI2.⊢↓-sealˣ Y∈′) prem ._)
    | refl | link₁ | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-final sourcePrem =
  target-source-star-chain-final
    (CTI2.⊑conceal²
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵈ} mono mono₁)
      (CTI2.rebase-varᴿ (composeSamePivotRebase ra link₁))
      (sameCtx-∘ sc sc₁)
      (CTI2.⊢↓-sealˣ Y∈)
      sourcePrem q)
target-source-star-chain {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {Xᴸ = Xᴸ} {Y = Y} {Y₂ = Y₂}
    {c = c} {p₂ = p₂} {q = q} sv inert vU mono ra sc X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono₁ rbᴿ sc₁ (CTI2.⊢↓-sealˣ Y∈′) prem ._)
    | refl | link₁ | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-var-residual {Y′ = Y₃} refl
        X∈ᵒ Y₂∈ᵒ rbᵒ residualᵒ =
  target-source-star-chain-wrap-target {W = W} {W′ = Wᵈ}
    {γ = γ} {γ′ = γᵈ} {V = V} {U = U₀}
    {Xᴸ = Xᴸ} {X₂ = Xᴸ} {Y = Y} {Y₂ = Y₂} {Y₃ = Y₃}
    {c = c} {p = pᵈ} {q = q}
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵈ} mono mono₁)
    (composeSamePivotRebase ra link₁)
    (sameCtx-∘ sc sc₁)
    X∈ Y∈
    (target-source-star-chain {Y₂ = Y₃} sv inert vU₀
      (STC.impEnvMono-refl {W = Wᵈ}) rbᵒ
      (STC.sameCtx-refl {γ = γᵈ}) X∈ᵒ Y₂∈ᵒ residualᵒ)
target-source-star-chain {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {Xᴸ = Xᴸ} {Y = Y} {Y₂ = Y₂}
    {c = c} {p₂ = p₂} {q = q} sv inert vU mono ra sc X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono₁ rbᴿ sc₁ (CTI2.⊢↓-sealˣ Y∈′) prem ._)
    | refl | link₁ | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-residual refl X∈ᵒ Y₂∈ᵒ rbᵒ residualᵒ =
  target-source-star-chain-residual refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned ra)
      (CTI2.RebaseAt.storeRepresentations ra))
    (CTI2.⊑conceal²
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵈ} mono mono₁)
      (CTI2.rebase-varᴿ (composeSamePivotRebase ra link₁))
      (sameCtx-∘ sc sc₁)
      (CTI2.⊢↓-sealˣ Y∈)
      residualᵒ q)
target-source-star-chain {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {Xᴸ = Xᴸ} {Y = Y} {Y₂ = Y₂}
    {c = c} {p₂ = p₂} {q = q} sv inert vU mono ra sc X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono₁ rbᴿ sc₁ (CTI2.⊢↓-sealˣ Y∈′) prem ._)
    | refl | link₁ | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-paired {Wᵖ = Wᵖ} refl monoᵒ rbᵒ scᵒ X∈ᵒ Y₂∈ᵒ
        partnerᵒ premᵒ =
  target-source-star-chain-paired refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned ra)
      (CTI2.RebaseAt.storeRepresentations ra))
    (CTI2.⊑conceal²
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵈ} mono mono₁)
      (CTI2.rebase-varᴿ (composeSamePivotRebase ra link₁))
      (sameCtx-∘ sc sc₁)
      (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.conceal⊑conceal² partnerᵒ monoᵒ rbᵒ scᵒ
        (CTI2.⊢↓-sealˣ X∈ᵒ) (CTI2.⊢↓-sealˣ Y₂∈ᵒ)
        premᵒ pᵈ)
      q)
    (impEnvMono-∘ {W₁ = W} {W₂ = Wᵈ}
      {W₃ = Wᵖ}
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵈ}
        mono mono₁)
      monoᵒ)
    (composeOuterRebase (composeSamePivotRebase ra link₁) rbᵒ)
    (sameCtx-∘ (sameCtx-∘ sc sc₁) scᵒ)
    partnerᵒ premᵒ
target-source-star-chain {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {Xᴸ = Xᴸ} {Y = Y} {Y₂ = Y₂}
    {c = c} {p₂ = p₂} {q = q} sv inert vU mono ra sc X∈ Y∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono₁ rbᴿ sc₁ (CTI2.⊢↓-sealˣ Y∈′) prem ._)
    | refl | link₁ | varv-seal {W = U₀} vU₀ Y₂∈ refl
    | target-source-star-payload {Wᵖ = Wᵖ} refl monoᵒ rbᵒ scᵒ X∈ᵒ Y₂∈ᵒ
        sourcePremᵒ =
  target-source-star-chain-payload refl X∈ Y∈
    (CTI2.sameWorldRebaseAt (CTI2.RebaseAt.pivotAligned ra)
      (CTI2.RebaseAt.storeRepresentations ra))
    (CTI2.⊑conceal²
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵈ} mono mono₁)
      (CTI2.rebase-varᴿ (composeSamePivotRebase ra link₁))
      (sameCtx-∘ sc sc₁)
      (CTI2.⊢↓-sealˣ Y∈)
      (CTI2.⊑conceal² monoᵒ (CTI2.rebase-varᴿ rbᵒ) scᵒ
        (CTI2.⊢↓-sealˣ Y₂∈ᵒ) sourcePremᵒ pᵈ)
      q)
    (impEnvMono-∘ {W₁ = W} {W₂ = Wᵈ}
      {W₃ = Wᵖ}
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵈ}
        mono mono₁)
      monoᵒ)
    (composeOuterRebase (composeSamePivotRebase ra link₁) rbᵒ)
    (sameCtx-∘ (sameCtx-∘ sc sc₁) scᵒ)
    sourcePremᵒ
