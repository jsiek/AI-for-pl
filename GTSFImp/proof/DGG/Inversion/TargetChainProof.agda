module proof.DGG.Inversion.TargetChainProof where

-- File Charter:
--   * Proves the checked source-star-at and source-star-chain inhabitants
--     for the target walk surface.
--   * Imports only the Set-level Def module and the shared proven support.
--   * Contains no target-tag-seal-walk clauses.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
  renaming (subst to subst≡)

open import Types
open import TyStore using (_∋_⦂_)
open import Conversion using (seal)
open import CastTerms
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.SealTransferCore as STC
open import proof.DGG.Inversion.SpineValueDef using
  (sv-cast; sv-seal; varv-seal; var-value-view)
open import proof.DGG.Inversion.TargetWalkDef using
  (TargetSourceStarAt; TargetSourceStarChain)
open import proof.DGG.Inversion.TargetWalkSupport using
  (composeSamePivotRebase; impEnvMono-∘; inner-source-pivot-eq;
   rebase-source-membership; sameCtx-∘; star-source-nonstar-⊥;
   store-lookup-unique; target-seal-rebase-source;
   var-source-nonstar-⊥)
open CTI2 using (_∣_⊢²_⊑_∶_; _⊑ᵂ⟨_⟩_)

target-source-star-at : TargetSourceStarAt
target-source-star-at {V = M ⦂∀ C [ A ]} ()
    inert vU X∈ Y∈ D
target-source-star-at {W = W} {X = X} {Y = Y}
    {c = c} {q = q} (sv-cast sv₀ ()) inert vU X∈ Y∈
    (CTI2.cast⊑² c₁ prem .q)
target-source-star-at {W = W} {X = X} {Y = Y}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑² {W′ = Wᵖ} {p = p} mono rb sc
      (CTI2.⊢↓-sealˣ X∈′) prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-X)
target-source-star-at {W = W} {X = X} {S = ＇ Y₂}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y₂}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y₂)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-X)
target-source-star-at {W = W} {X = X} {S = ‵ ι}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ‵ ι}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ‵ ι)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-ι)
target-source-star-at {W = W} {X = X} {S = A ⇒ B}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = A ⇒ B}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ A ⇒ B)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-⇒)
target-source-star-at {W = W} {X = X} {S = `∀ A}
    {q = q} (sv-seal sv₀) inert vU X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .q) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = `∀ A}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ `∀ A)
        (store-lookup-unique X∈′ X∈) p)
      nonstar-∀)
target-source-star-at {S = ★} {c = c} {q = q} sv inert vU X∈ Y∈ D
    with STC.seal-transfer sv vU D
target-source-star-at {S = ★} {c = c} {q = q} sv inert vU X∈ Y∈ D
    | W₂ , γ₂ , link , mono₂ , sc₂ , q₂ , D₂ =
  CTI2.conceal⊑conceal² mono₂ link sc₂
    (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
    (CTI2.cast⊑² c D₂ ★⊑★) q
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
    | link | varv-seal {W = U₀} vU₀ Y₂∈ refl =
  CTI2.⊑conceal² mono rbᴿ sc (CTI2.⊢↓-sealˣ Y∈)
    (target-source-star-at sv inert vU₀
      (rebase-source-membership link X∈) Y₂∈ prem)
    q
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

target-source-star-chain : TargetSourceStarChain
target-source-star-chain {V = M ⦂∀ C [ A ]} ()
    inert vU mono ra sc X∈ Y∈ D
target-source-star-chain {V = V ⟨ c₁ ⟩} (sv-cast sv₀ ())
    inert vU mono ra sc X∈ Y∈ (CTI2.cast⊑² .c₁ prem p₂)
target-source-star-chain {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {p₂ = p₂} {q = q}
    (sv-seal sv₀) inert vU mono ra sc X∈ Y∈
    (CTI2.conceal⊑² {W′ = Wᵖ} {p = p} mono₁ rb₁ sc₁
      (CTI2.⊢↓-sealˣ X∈′) prem .p₂)
    with inner-source-pivot-eq ra q p₂
target-source-star-chain {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y} {p₂ = p₂} {q = q}
    (sv-seal sv₀) inert vU mono ra sc X∈ Y∈
    (CTI2.conceal⊑² {W′ = Wᵖ} {p = p} mono₁ rb₁ sc₁
      (CTI2.⊢↓-sealˣ X∈′) prem .p₂)
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
      mono₁ rb₁ sc₁ (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .p₂)
    with inner-source-pivot-eq ra q p₂
target-source-star-chain {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y₂ = Y₂} {p₂ = p₂} {q = q}
    (sv-seal sv₀) inert vU mono ra sc X∈ Y∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      mono₁ rb₁ sc₁ (CTI2.⊢↓-sealˣ X∈′) target⊢ prem .p₂)
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
    | refl | link₁ | varv-seal {W = U₀} vU₀ Y₂∈ refl =
  CTI2.⊑conceal²
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵈ} mono mono₁)
    (CTI2.rebase-varᴿ (composeSamePivotRebase ra link₁))
    (sameCtx-∘ sc sc₁)
    (CTI2.⊢↓-sealˣ Y∈)
    (target-source-star-at sv inert vU₀
      (rebase-source-membership (composeSamePivotRebase ra link₁) X∈)
      Y₂∈ prem)
    q
