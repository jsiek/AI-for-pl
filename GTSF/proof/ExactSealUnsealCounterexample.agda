{-# OPTIONS --warning=noUnreachableClauses #-}

module proof.ExactSealUnsealCounterexample where

-- File Charter:
--   * Checked counterexample for the exact right-hand `seal-unseal` dynamic
--     gradual guarantee case.
--   * Constructs a source value that narrows to the target seal-unseal redex,
--     but cannot narrow to the target's reduct after any source reduction.
--   * Depends on the broad right-seal counterexample and small cast-factor
--     impossibility lemmas, without adding postulates.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import proof.NarrowWidenProperties
  using
    ( narrowing-target-star-source-star
    ; narrowing-var-to-older⊥
    ; narrowing-var-to-star⊥
    )
open import proof.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.CatchupStore using (combineStoreNrw)
open import proof.NuPreservation using (value-no-step)
open import proof.RightSealBroadCounterexample
open import proof.TermNarrowingProperties

NatTy : Ty
NatTy = ‵ `ℕ

k0 : Const
k0 = κℕ 0

c★ : Term
c★ = $ k0 ⟨ NatTy ! ⟩

c★-value : Value c★
c★-value = ($ k0) ⟨ NatTy ! ⟩

c★-no• : No• c★
c★-no• = no•-⟨⟩ no•-$

baseUntag : Coercion
baseUntag = NatTy ？

idNatᶜ : 1 ∣ StoreStar ⊢ id NatTy ∶ᶜ NatTy ⊒ NatTy
idNatᶜ = cast-id wfBase refl , cross (id-‵ `ℕ)

idNat⊒ : tag-or-idᵈ ∣ 1 ∣ StoreStar ⊢ id NatTy ∶ NatTy ⊒ NatTy
idNat⊒ = cast-id wfBase refl , cross (id-‵ `ℕ)

idStarᶜ : 1 ∣ StoreStar ⊢ id ★ ∶ᶜ ★ ⊒ ★
idStarᶜ = cast-id wf★ refl , id★

idStarTag⊒ : tag-or-idᵈ ∣ 1 ∣ StoreStar ⊢ id ★ ∶ ★ ⊒ ★
idStarTag⊒ = cast-id wf★ refl , id★

baseUntag⊒ : tag-or-idᵈ ∣ 1 ∣ StoreStar ⊢ baseUntag ∶ ★ ⊒ NatTy
baseUntag⊒ = cast-untag wfBase (‵ `ℕ) refl , untag (‵ `ℕ)

endpointsBase : EndpointWf 1 StoreStar ★ NatTy
endpointsBase = wf★ˢ , wfBaseˢ

base-untag-left :
  1 ∣ SigmaStar ⊢ id ★ ⨾ⁿ baseUntag ≈ baseUntag ∶ ★ ⊒ NatTy
base-untag-left =
  compose-leftⁿ wfStoreStar idStarTag⊒ baseUntag⊒
    (endpointsⁿ refl refl refl refl SigmaStar⊒ endpointsBase endpointsBase
      (tag-or-idᵈ ,
       proj₂ (_⨟ⁿ_ {wfΣ = wfStoreStar} idStarTag⊒ baseUntag⊒))
      (tag-or-idᵈ , baseUntag⊒))

base-untag-right :
  1 ∣ SigmaStar ⊢ baseUntag ≈ baseUntag ⨾ⁿ id NatTy ∶ ★ ⊒ NatTy
base-untag-right =
  compose-rightⁿ wfStoreStar baseUntag⊒ idNat⊒
    (endpointsⁿ refl refl refl refl SigmaStar⊒ endpointsBase endpointsBase
      (tag-or-idᵈ , baseUntag⊒)
      (tag-or-idᵈ ,
       proj₂ (_⨟ⁿ_ {wfΣ = wfStoreStar} baseUntag⊒ idNat⊒)))

c★-self-id★ :
  1 ∣ SigmaStar ∣ [] ⊢ c★ ⊒ c★ ∶ id ★
c★-self-id★ =
  cast+⊒cast+
    {p = id NatTy}
    {q = id ★}
    {r = baseUntag}
    {s = baseUntag}
    {t = baseUntag}
    idNatᶜ
    idStarᶜ
    base-untag-left
    base-untag-right
    (κ⊒κ k0)

c★-right-sealed-at-untag :
  1 ∣ SigmaStar ∣ [] ⊢ c★ ⊒ c★ ⟨ sealStar0 ⟩ ∶ untagAlpha0
c★-right-sealed-at-untag =
  ⊒cast- idStarᶜ right-seal-compose-to-untag c★-self-id★

exact-broad-premise :
  1 ∣ SigmaStar ∣ []
    ⊢ c★ ⊒ c★ ⟨ sealStar0 ⟩ ⟨ unseal alpha0 ★ ⟩ ∶ id ★
exact-broad-premise =
  ⊒cast+ idStarᶜ right-seal-compose-to-untag c★-right-sealed-at-untag

idAlpha0 : Coercion
idAlpha0 = id (＇ alpha0)

idAlphaᶜ : 1 ∣ StoreStar ⊢ idAlpha0 ∶ᶜ ＇ alpha0 ⊒ ＇ alpha0
idAlphaᶜ = cast-id (wfVar z<s) refl , cross (id-＇ alpha0)

idAlpha⊒ : seal-or-idᵈ ∣ 1 ∣ StoreStar ⊢ idAlpha0 ∶ ＇ alpha0 ⊒ ＇ alpha0
idAlpha⊒ = cast-id (wfVar z<s) refl , cross (id-＇ alpha0)

idAlphaTag⊒ :
  tag-or-idᵈ ∣ 1 ∣ StoreStar ⊢ idAlpha0 ∶ ＇ alpha0 ⊒ ＇ alpha0
idAlphaTag⊒ = cast-id (wfVar z<s) refl , cross (id-＇ alpha0)

untagAlpha-right :
  1 ∣ SigmaStar ⊢ untagAlpha0 ≈ untagAlpha0 ⨾ⁿ idAlpha0
    ∶ ★ ⊒ ＇ alpha0
untagAlpha-right =
  compose-rightⁿ wfStoreStar untagAlpha⊒ᶜ idAlphaTag⊒
    (endpointsⁿ refl refl refl refl SigmaStar⊒ endpointsStar endpointsStar
      (tag-or-idᵈ , untagAlpha⊒ᶜ)
      (tag-or-idᵈ ,
       proj₂ (_⨟ⁿ_ {wfΣ = wfStoreStar} untagAlpha⊒ᶜ idAlphaTag⊒)))

right-seal-compose-to-seal :
  1 ∣ SigmaStar ⊢ id ★ ⨾ⁿ sealStar0 ≈ sealStar0 ∶ ★ ⊒ ＇ alpha0
right-seal-compose-to-seal =
  compose-leftⁿ wfStoreStar idStar⊒ sealStar⊒
    (endpointsⁿ refl refl refl refl SigmaStar⊒ endpointsStar endpointsStar
      (seal-or-idᵈ ,
       proj₂ (_⨟ⁿ_ {wfΣ = wfStoreStar} idStar⊒ sealStar⊒))
      (seal-or-idᵈ , sealStar⊒))

left-seal-compose :
  1 ∣ SigmaStar ⊢ sealStar0 ≈ sealStar0 ⨾ⁿ idAlpha0
    ∶ ★ ⊒ ＇ alpha0
left-seal-compose =
  compose-rightⁿ wfStoreStar sealStar⊒ idAlpha⊒
    (endpointsⁿ refl refl refl refl SigmaStar⊒ endpointsStar endpointsStar
      (seal-or-idᵈ , sealStar⊒)
      (seal-or-idᵈ ,
       proj₂ (_⨟ⁿ_ {wfΣ = wfStoreStar} sealStar⊒ idAlpha⊒)))

c★-right-sealed-at-seal :
  1 ∣ SigmaStar ∣ [] ⊢ c★ ⊒ c★ ⟨ sealStar0 ⟩ ∶ sealStar0
c★-right-sealed-at-seal =
  ⊒cast- idStarᶜ right-seal-compose-to-seal c★-self-id★

c★-sealed-self-idAlpha :
  1 ∣ SigmaStar ∣ []
    ⊢ c★ ⟨ sealStar0 ⟩ ⊒ c★ ⟨ sealStar0 ⟩ ∶ idAlpha0
c★-sealed-self-idAlpha =
  cast-⊒ idAlphaᶜ left-seal-compose c★-right-sealed-at-seal

c★-tagged-sealed-to-sealed :
  1 ∣ SigmaStar ∣ []
    ⊢ c★ ⟨ sealStar0 ⟩ ⟨ - untagAlpha0 ⟩
      ⊒ c★ ⟨ sealStar0 ⟩ ∶ untagAlpha0
c★-tagged-sealed-to-sealed =
  cast+⊒ idAlphaᶜ untagAlpha-right c★-sealed-self-idAlpha

exact-tagged-sealed-source-premise :
  1 ∣ SigmaStar ∣ []
    ⊢ c★ ⟨ sealStar0 ⟩ ⟨ - untagAlpha0 ⟩
      ⊒ c★ ⟨ sealStar0 ⟩ ⟨ unseal alpha0 ★ ⟩ ∶ id ★
exact-tagged-sealed-source-premise =
  ⊒cast+ idStarᶜ right-seal-compose-to-untag
    c★-tagged-sealed-to-sealed

sealedSource : Term
sealedSource = c★ ⟨ sealStar0 ⟩

badSource : Term
badSource = sealedSource ⟨ - untagAlpha0 ⟩

sealedTarget : Term
sealedTarget = sealedSource ⟨ unseal alpha0 ★ ⟩

badSource-value : Value badSource
badSource-value =
  ((($ k0) ⟨ NatTy ! ⟩) ⟨ seal ★ alpha0 ⟩) ⟨ (＇ alpha0) ! ⟩

badSource-runtime-ok : RuntimeOK badSource
badSource-runtime-ok = ok-no (no•-⟨⟩ (no•-⟨⟩ c★-no•))

sealedTarget-step : sealedTarget —→[ keep ] c★
sealedTarget-step = pure-step (seal-unseal c★-value)

exact-tagged-sealed-source-premise′ :
  1 ∣ SigmaStar ∣ [] ⊢ badSource ⊒ sealedTarget ∶ id ★
exact-tagged-sealed-source-premise′ = exact-tagged-sealed-source-premise

term-cast-inj-term :
  ∀ {M N : Term} {c d : Coercion} →
  M ⟨ c ⟩ ≡ N ⟨ d ⟩ →
  M ≡ N
term-cast-inj-term refl = refl

term-cast-inj-coercion :
  ∀ {M N : Term} {c d : Coercion} →
  M ⟨ c ⟩ ≡ N ⟨ d ⟩ →
  c ≡ d
term-cast-inj-coercion refl = refl

value-multistep-refl :
  ∀ {V N χs} →
  Value V →
  V —↠[ χs ] N →
  χs ≡ [] × N ≡ V
value-multistep-refl vV ↠-refl = refl , refl
value-multistep-refl vV (↠-step V→M M↠N) =
  ⊥-elim (value-no-step vV V→M)

compose-left-tag-factor⊥ :
  ∀ {Δ σ q r G E F} →
  Δ ∣ σ ⊢ q ⨾ⁿ G ! ≈ r ∶ E ⊒ F →
  ⊥
compose-left-tag-factor⊥
    (compose-leftⁿ wfΣ q⊒ (cast-tag hG gG tag-ok , cross ())
      q⨟tag≈r)

source-left-tag-factor⊥ :
  ∀ {Δ σ r p G E F} →
  Δ ∣ σ ⊢ r ≈ G ! ⨾ⁿ p ∶ E ⊒ F →
  ⊥
source-left-tag-factor⊥ = compose-right-tag-factor⊥

data RelevantStore : StoreNrw → Set where
  rel-star : RelevantStore SigmaStar
  rel-source : ∀ {A} → RelevantStore ((alpha0 ꞉= A ⊒) ∷ [])

narrowing-target-idNat :
  ∀ {μ Δ Σ p A B} →
  p ≡ id NatTy →
  μ ∣ Δ ∣ Σ ⊢ p ∶ A ⊒ B →
  B ≡ NatTy
narrowing-target-idNat p≡idNat p⊒ =
  trans (sym (proj₂ (coercion-src-tgtᵐ (proj₁ p⊒))))
        (cong tgt p≡idNat)

Nat≢★ : NatTy ≡ ★ → ⊥
Nat≢★ ()

bare-constant-index-relevant :
  ∀ {Δ σ M M′ p} →
  RelevantStore σ →
  M ≡ $ k0 →
  M′ ≡ $ k0 →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p →
  p ≡ id NatTy
bare-constant-index-relevant rel-star eqM eqM′
    (extend {A = A} qᶜ pαᶜ M⊒M′) =
  bare-constant-index-relevant (rel-source {A = A}) eqM eqM′ M⊒M′
bare-constant-index-relevant () eqM eqM′ (split qᶜ pαᶜ M⊒M′)
bare-constant-index-relevant rs eqM () (⊒blame pᶜ)
bare-constant-index-relevant rs eqM () (x⊒x pᶜ x∋p)
bare-constant-index-relevant rs () eqM′ (ƛ⊒ƛ p↦qᶜ M⊒M′)
bare-constant-index-relevant rs () eqM′ (·⊒· qᶜ L⊒L′ M⊒M′)
bare-constant-index-relevant rs () eqM′ (Λ⊒Λ allᶜ vV M⊒M′)
bare-constant-index-relevant rs eqM () (⊒Λ pᶜ M⊒M′)
bare-constant-index-relevant rs eqM () (⊒⟨ν⟩ pᶜ x M⊒M′)
bare-constant-index-relevant rs () eqM′ (α⊒α qᶜ pαᶜ L⊒L′)
bare-constant-index-relevant rs eqM () (⊒α pαᶜ L⊒L′)
bare-constant-index-relevant rs () eqM′ (ν⊒ν pᶜ qᶜ M⊒M′)
bare-constant-index-relevant rs eqM () (⊒ν pᶜ M⊒M′)
bare-constant-index-relevant rs () eqM′ (ν⊒ pᶜ M⊒M′)
bare-constant-index-relevant rs refl refl (κ⊒κ (κℕ zero)) = refl
bare-constant-index-relevant rs () () (κ⊒κ (κℕ (suc n)))
bare-constant-index-relevant rs () eqM′ (⊕⊒⊕ M⊒M′ N⊒N′)
bare-constant-index-relevant rs eqM () (⊒cast+ qᶜ q⨟s≈r M⊒M′)
bare-constant-index-relevant rs eqM () (⊒cast- qᶜ q⨟s≈r M⊒M′)
bare-constant-index-relevant rs () eqM′ (cast+⊒ pᶜ r≈t⨟p M⊒M′)
bare-constant-index-relevant rs () eqM′ (cast-⊒ pᶜ r≈t⨟p M⊒M′)

dual-eq-seal-factor⊥ :
  ∀ {Δ σ r p t A B} →
  - t ≡ sealStar0 →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  ⊥
dual-eq-seal-factor⊥ {t = id A} () r≈t⨟p
dual-eq-seal-factor⊥ {t = c ︔ d} () r≈t⨟p
dual-eq-seal-factor⊥ {t = c ↦ d} () r≈t⨟p
dual-eq-seal-factor⊥ {t = `∀ c} () r≈t⨟p
dual-eq-seal-factor⊥ {t = (＇ α) !} () r≈t⨟p
dual-eq-seal-factor⊥ {t = (‵ ι) !} () r≈t⨟p
dual-eq-seal-factor⊥ {t = ★ !} () r≈t⨟p
dual-eq-seal-factor⊥ {t = (A ⇒ B) !} () r≈t⨟p
dual-eq-seal-factor⊥ {t = (`∀ A) !} () r≈t⨟p
dual-eq-seal-factor⊥ {t = (＇ α) ？} () r≈t⨟p
dual-eq-seal-factor⊥ {t = (‵ ι) ？} () r≈t⨟p
dual-eq-seal-factor⊥ {t = ★ ？} () r≈t⨟p
dual-eq-seal-factor⊥ {t = (A ⇒ B) ？} () r≈t⨟p
dual-eq-seal-factor⊥ {t = (`∀ A) ？} () r≈t⨟p
dual-eq-seal-factor⊥ {t = seal A α} () r≈t⨟p
dual-eq-seal-factor⊥ {t = unseal α A} refl r≈t⨟p =
  compose-right-unseal-factor⊥ r≈t⨟p
dual-eq-seal-factor⊥ {t = gen A c} () r≈t⨟p
dual-eq-seal-factor⊥ {t = inst B c} () r≈t⨟p

seal-factor-then-dual-nat-tag⊥ :
  ∀ {Δ τ σ q r p s A B C D} →
  - s ≡ NatTy ! →
  Δ ∣ τ ⊢ q ≈ sealStar0 ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ C ⊒ D →
  ⊥
seal-factor-then-dual-nat-tag⊥ {s = id A} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = c ︔ d} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = c ↦ d} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = `∀ c} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = (＇ α) !} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = (‵ ι) !} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = ★ !} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = (A ⇒ B) !} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = (`∀ A) !} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = (＇ α) ？} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = (‵ `ℕ) ？} refl
    (compose-rightⁿ wfΣ₀
      (cast-seal h★ α∈Σ seal-ok , sealⁿ .★ .alpha0)
      p⊒
      (endpointsⁿ src-q₀ tgt-q₀ src-u₀ tgt-u₀
        σ⊒₀ wfΣ₁ wfΣ₂ q⊒₀ u⊒₀))
    (compose-leftⁿ wfΣ
      q⊒
      s⊒@(cast-untag hNat (‵ .`ℕ) untag-ok , untag (‵ .`ℕ))
      q⨟s≈r) =
  let
    B≡★ =
      trans (sym (proj₂ (coercion-src-tgtᵐ (proj₁ (proj₂ q⊒₀)))))
        (trans (proj₂ (coercion-src-tgtᵐ (proj₁ q⊒)))
          (sym (proj₁ (coercion-src-tgtᵐ (proj₁ s⊒)))))
    p⊒★ = subst (λ T → _ ∣ _ ∣ _ ⊢ _ ∶ ＇ alpha0 ⊒ T) B≡★ p⊒
  in
  narrowing-var-to-star⊥ p⊒★
seal-factor-then-dual-nat-tag⊥ {s = (‵ `𝔹) ？} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = ★ ？} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = (A ⇒ B) ？} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = (`∀ A) ？} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = seal A α} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = unseal α A} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = gen A c} () outer q⨟s≈r
seal-factor-then-dual-nat-tag⊥ {s = inst B c} () outer q⨟s≈r

c★-left-neg-bare-seal-factor⊥ :
  ∀ {Δ σ τ M M′ p₀ r p t A B C D} →
  RelevantStore σ →
  M ⟨ - t ⟩ ≡ c★ →
  M′ ≡ $ k0 →
  Δ ∣ τ ⊢ r ≈ sealStar0 ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p₀ ∶ C ⊒ D →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p₀ →
  ⊥
c★-left-neg-bare-seal-factor⊥ {t = id A}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = c ︔ d}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = c ↦ d}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = `∀ c}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = (＇ α) !}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = (‵ ι) !}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = ★ !}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = (A ⇒ B) !}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = (`∀ A) !}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = (＇ α) ？}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = (‵ `ℕ) ？} rs refl refl
    (compose-rightⁿ wfΣ
      (cast-seal h★ α∈Σ seal-ok , sealⁿ .★ .alpha0)
      p⊒
      (endpointsⁿ src-r₁ tgt-r₁ src-u₁ tgt-u₁
        σ⊒₁ wfΣ₁ wfΣ₂ r⊒₁ u⊒₁))
    (compose-rightⁿ wfΣ′
      (cast-untag hNat (‵ .`ℕ) untag-ok , untag (‵ .`ℕ))
      p₀⊒
      (endpointsⁿ src-r₂ tgt-r₂ src-u₂ tgt-u₂
        σ⊒₂ wfΣ₃ wfΣ₄ r⊒₂ u⊒₂))
    M⊒M′ =
  let
    p₀≡idNat = bare-constant-index-relevant rs refl refl M⊒M′
    B₂≡Nat = narrowing-target-idNat p₀≡idNat p₀⊒
    B₁≡B₂ = trans (sym tgt-r₁) tgt-r₂
    B₁≡Nat = trans B₁≡B₂ B₂≡Nat
    p⊒Nat = subst (λ B → _ ∣ _ ∣ _ ⊢ _ ∶ ＇ alpha0 ⊒ B)
                    B₁≡Nat p⊒
  in
  narrowing-var-to-older⊥ wfΣ wfBase p⊒Nat
c★-left-neg-bare-seal-factor⊥ {t = (‵ `𝔹) ？}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = ★ ？}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = (A ⇒ B) ？}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = (`∀ A) ？}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = seal A α}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = unseal α A}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = gen A c}
    rs () eqM′ outer inner M⊒M′
c★-left-neg-bare-seal-factor⊥ {t = inst B c}
    rs () eqM′ outer inner M⊒M′

c★⊒bare-seal-factor⊥ :
  ∀ {Δ σ τ M M′ r p A B} →
  RelevantStore σ →
  M ≡ c★ →
  M′ ≡ $ k0 →
  Δ ∣ τ ⊢ r ≈ sealStar0 ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ r →
  ⊥
c★⊒bare-seal-factor⊥ rel-star eqM eqM′ outer
    (extend {A = A} qᶜ pαᶜ M⊒M′) =
  c★⊒bare-seal-factor⊥ (rel-source {A = A}) eqM eqM′ outer M⊒M′
c★⊒bare-seal-factor⊥ () eqM eqM′ outer (split qᶜ pαᶜ M⊒M′)
c★⊒bare-seal-factor⊥ rs eqM () outer (⊒blame pᶜ)
c★⊒bare-seal-factor⊥ rs eqM () outer (x⊒x pᶜ x∋p)
c★⊒bare-seal-factor⊥ rs () eqM′ outer (ƛ⊒ƛ p↦qᶜ M⊒M′)
c★⊒bare-seal-factor⊥ rs () eqM′ outer (·⊒· qᶜ L⊒L′ M⊒M′)
c★⊒bare-seal-factor⊥ rs () eqM′ outer (Λ⊒Λ allᶜ vV M⊒M′)
c★⊒bare-seal-factor⊥ rs eqM () outer (⊒Λ pᶜ M⊒M′)
c★⊒bare-seal-factor⊥ rs eqM () outer (⊒⟨ν⟩ pᶜ x M⊒M′)
c★⊒bare-seal-factor⊥ rs () eqM′ outer (α⊒α qᶜ pαᶜ L⊒L′)
c★⊒bare-seal-factor⊥ rs eqM () outer (⊒α pαᶜ L⊒L′)
c★⊒bare-seal-factor⊥ rs () eqM′ outer (ν⊒ν pᶜ qᶜ M⊒M′)
c★⊒bare-seal-factor⊥ rs eqM () outer (⊒ν pᶜ M⊒M′)
c★⊒bare-seal-factor⊥ rs () eqM′ outer (ν⊒ pᶜ M⊒M′)
c★⊒bare-seal-factor⊥ rs () eqM′ outer (κ⊒κ κ)
c★⊒bare-seal-factor⊥ rs () eqM′ outer (⊕⊒⊕ M⊒M′ N⊒N′)
c★⊒bare-seal-factor⊥ rs eqM () outer (⊒cast+ qᶜ q⨟s≈r M⊒M′)
c★⊒bare-seal-factor⊥ rs eqM () outer (⊒cast- qᶜ q⨟s≈r M⊒M′)
c★⊒bare-seal-factor⊥ rs eqM refl outer
    (cast+⊒ {p = p₀} {t = t} pᶜ r≈t⨟p M⊒M′) =
  c★-left-neg-bare-seal-factor⊥ rs eqM refl outer r≈t⨟p M⊒M′
c★⊒bare-seal-factor⊥ {σ = σ} rs eqM refl outer
    (cast-⊒ {p = p} {r = r} {t = t} {A = A} {B = B}
      pᶜ r≈t⨟p M⊒M′) =
  compose-right-tag-factor⊥
    (subst
      (λ t₀ → _ ∣ σ ⊢ r ≈ t₀ ⨾ⁿ p ∶ A ⊒ B)
      (term-cast-inj-coercion eqM)
      r≈t⨟p)

sealedSource⊒bare-aux⊥ :
  ∀ {Δ σ M M′ p} →
  RelevantStore σ →
  M ≡ sealedSource →
  M′ ≡ $ k0 →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p →
  ⊥
sealedSource⊒bare-aux⊥ rel-star eqM eqM′
    (extend {A = A} qᶜ pαᶜ M⊒M′) =
  sealedSource⊒bare-aux⊥ (rel-source {A = A}) eqM eqM′ M⊒M′
sealedSource⊒bare-aux⊥ () eqM eqM′ (split qᶜ pαᶜ M⊒M′)
sealedSource⊒bare-aux⊥ rs eqM () (⊒blame pᶜ)
sealedSource⊒bare-aux⊥ rs eqM () (x⊒x pᶜ x∋p)
sealedSource⊒bare-aux⊥ rs () eqM′ (ƛ⊒ƛ p↦qᶜ M⊒M′)
sealedSource⊒bare-aux⊥ rs () eqM′ (·⊒· qᶜ L⊒L′ M⊒M′)
sealedSource⊒bare-aux⊥ rs () eqM′ (Λ⊒Λ allᶜ vV M⊒M′)
sealedSource⊒bare-aux⊥ rs eqM () (⊒Λ pᶜ M⊒M′)
sealedSource⊒bare-aux⊥ rs eqM () (⊒⟨ν⟩ pᶜ x M⊒M′)
sealedSource⊒bare-aux⊥ rs () eqM′ (α⊒α qᶜ pαᶜ L⊒L′)
sealedSource⊒bare-aux⊥ rs eqM () (⊒α pαᶜ L⊒L′)
sealedSource⊒bare-aux⊥ rs () eqM′ (ν⊒ν pᶜ qᶜ M⊒M′)
sealedSource⊒bare-aux⊥ rs eqM () (⊒ν pᶜ M⊒M′)
sealedSource⊒bare-aux⊥ rs () eqM′ (ν⊒ pᶜ M⊒M′)
sealedSource⊒bare-aux⊥ rs () eqM′ (κ⊒κ κ)
sealedSource⊒bare-aux⊥ rs () eqM′ (⊕⊒⊕ M⊒M′ N⊒N′)
sealedSource⊒bare-aux⊥ rs eqM () (⊒cast+ qᶜ q⨟s≈r M⊒M′)
sealedSource⊒bare-aux⊥ rs eqM () (⊒cast- qᶜ q⨟s≈r M⊒M′)
sealedSource⊒bare-aux⊥ rs eqM refl
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  dual-eq-seal-factor⊥ (term-cast-inj-coercion eqM) r≈t⨟p
sealedSource⊒bare-aux⊥ {σ = σ} rs eqM refl
    (cast-⊒ {p = p} {r = r} {t = t} {A = A} {B = B}
      pᶜ r≈t⨟p M⊒M′) =
  c★⊒bare-seal-factor⊥ rs (term-cast-inj-term eqM) refl
    (subst
      (λ t₀ → _ ∣ σ ⊢ r ≈ t₀ ⨾ⁿ p ∶ A ⊒ B)
      (term-cast-inj-coercion eqM)
      r≈t⨟p)
    M⊒M′

bare-right-neg-c★⊥ :
  ∀ {Δ σ M M′ q r s A B} →
  RelevantStore σ →
  M ≡ $ k0 →
  M′ ⟨ - s ⟩ ≡ c★ →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ r →
  ⊥
bare-right-neg-c★⊥ {s = id A} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = c ︔ d} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = c ↦ d} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = `∀ c} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = (＇ α) !} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = (‵ ι) !} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = ★ !} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = (A ⇒ B) !} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = (`∀ A) !} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = (＇ α) ？} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = (‵ `ℕ) ？} rs refl refl
    (compose-leftⁿ wfΣ
      q⊒
      (cast-untag hNat (‵ .`ℕ) untag-ok , untag (‵ .`ℕ))
      (endpointsⁿ src-u tgt-u src-r tgt-r
        σ⊒ wfΣ₁ wfΣ₂ u⊒ r⊒))
    M⊒M′ =
  let
    r≡idNat = bare-constant-index-relevant rs refl refl M⊒M′
    A≡★ = narrowing-target-star-source-star q⊒
    A≡Nat = trans (sym src-r) (cong src r≡idNat)
  in
  Nat≢★ (trans (sym A≡Nat) A≡★)
bare-right-neg-c★⊥ {s = (‵ `𝔹) ？} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = ★ ？} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = (A ⇒ B) ？} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = (`∀ A) ？} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = seal A α} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = unseal α A} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = gen A c} rs eqM () q⨟s≈r M⊒M′
bare-right-neg-c★⊥ {s = inst B c} rs eqM () q⨟s≈r M⊒M′

bare⊒c★-aux⊥ :
  ∀ {Δ σ M M′ p} →
  RelevantStore σ →
  M ≡ $ k0 →
  M′ ≡ c★ →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p →
  ⊥
bare⊒c★-aux⊥ rel-star eqM eqM′
    (extend {A = A} qᶜ pαᶜ M⊒M′) =
  bare⊒c★-aux⊥ (rel-source {A = A}) eqM eqM′ M⊒M′
bare⊒c★-aux⊥ () eqM eqM′ (split qᶜ pαᶜ M⊒M′)
bare⊒c★-aux⊥ rs eqM () (⊒blame pᶜ)
bare⊒c★-aux⊥ rs eqM () (x⊒x pᶜ x∋p)
bare⊒c★-aux⊥ rs () eqM′ (ƛ⊒ƛ p↦qᶜ M⊒M′)
bare⊒c★-aux⊥ rs () eqM′ (·⊒· qᶜ L⊒L′ M⊒M′)
bare⊒c★-aux⊥ rs () eqM′ (Λ⊒Λ allᶜ vV M⊒M′)
bare⊒c★-aux⊥ rs eqM () (⊒Λ pᶜ M⊒M′)
bare⊒c★-aux⊥ rs eqM () (⊒⟨ν⟩ pᶜ x M⊒M′)
bare⊒c★-aux⊥ rs () eqM′ (α⊒α qᶜ pαᶜ L⊒L′)
bare⊒c★-aux⊥ rs eqM () (⊒α pαᶜ L⊒L′)
bare⊒c★-aux⊥ rs () eqM′ (ν⊒ν pᶜ qᶜ M⊒M′)
bare⊒c★-aux⊥ rs eqM () (⊒ν pᶜ M⊒M′)
bare⊒c★-aux⊥ rs () eqM′ (ν⊒ pᶜ M⊒M′)
bare⊒c★-aux⊥ rs eqM () (κ⊒κ κ)
bare⊒c★-aux⊥ rs () eqM′ (⊕⊒⊕ M⊒M′ N⊒N′)
bare⊒c★-aux⊥ rs refl eqM′
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  bare-right-neg-c★⊥ rs refl eqM′ q⨟s≈r M⊒M′
bare⊒c★-aux⊥ {σ = σ} rs refl eqM′
    (⊒cast- {q = q} {r = r} {s = s} {A = A} {B = B}
      qᶜ q⨟s≈r M⊒M′) =
  compose-left-tag-factor⊥
    (subst
      (λ s₀ → _ ∣ σ ⊢ q ⨾ⁿ s₀ ≈ r ∶ A ⊒ B)
      (term-cast-inj-coercion eqM′)
      q⨟s≈r)
bare⊒c★-aux⊥ rs () eqM′ (cast+⊒ pᶜ r≈t⨟p M⊒M′)
bare⊒c★-aux⊥ rs () eqM′ (cast-⊒ pᶜ r≈t⨟p M⊒M′)

c★⊒c★-seal-factor⊥ :
  ∀ {Δ σ τ M M′ r p A B} →
  RelevantStore σ →
  M ≡ c★ →
  M′ ≡ c★ →
  Δ ∣ τ ⊢ r ≈ sealStar0 ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ r →
  ⊥
c★⊒c★-seal-factor⊥ rel-star eqM eqM′ outer
    (extend {A = A} qᶜ pαᶜ M⊒M′) =
  c★⊒c★-seal-factor⊥ (rel-source {A = A}) eqM eqM′ outer M⊒M′
c★⊒c★-seal-factor⊥ () eqM eqM′ outer (split qᶜ pαᶜ M⊒M′)
c★⊒c★-seal-factor⊥ rs eqM () outer (⊒blame pᶜ)
c★⊒c★-seal-factor⊥ rs eqM () outer (x⊒x pᶜ x∋p)
c★⊒c★-seal-factor⊥ rs () eqM′ outer (ƛ⊒ƛ p↦qᶜ M⊒M′)
c★⊒c★-seal-factor⊥ rs () eqM′ outer (·⊒· qᶜ L⊒L′ M⊒M′)
c★⊒c★-seal-factor⊥ rs () eqM′ outer (Λ⊒Λ allᶜ vV M⊒M′)
c★⊒c★-seal-factor⊥ rs eqM () outer (⊒Λ pᶜ M⊒M′)
c★⊒c★-seal-factor⊥ rs eqM () outer (⊒⟨ν⟩ pᶜ x M⊒M′)
c★⊒c★-seal-factor⊥ rs () eqM′ outer (α⊒α qᶜ pαᶜ L⊒L′)
c★⊒c★-seal-factor⊥ rs eqM () outer (⊒α pαᶜ L⊒L′)
c★⊒c★-seal-factor⊥ rs () eqM′ outer (ν⊒ν pᶜ qᶜ M⊒M′)
c★⊒c★-seal-factor⊥ rs eqM () outer (⊒ν pᶜ M⊒M′)
c★⊒c★-seal-factor⊥ rs () eqM′ outer (ν⊒ pᶜ M⊒M′)
c★⊒c★-seal-factor⊥ rs () eqM′ outer (κ⊒κ κ)
c★⊒c★-seal-factor⊥ rs () eqM′ outer (⊕⊒⊕ M⊒M′ N⊒N′)
c★⊒c★-seal-factor⊥ rs refl eqM′ outer
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  seal-factor-then-dual-nat-tag⊥
    (term-cast-inj-coercion eqM′) outer q⨟s≈r
c★⊒c★-seal-factor⊥ {σ = σ} rs refl eqM′ outer
    (⊒cast- {q = q} {r = r} {s = s} {A = A} {B = B}
      qᶜ q⨟s≈r M⊒M′) =
  compose-left-tag-factor⊥
    (subst
      (λ s₀ → _ ∣ σ ⊢ q ⨾ⁿ s₀ ≈ r ∶ A ⊒ B)
      (term-cast-inj-coercion eqM′)
      q⨟s≈r)
c★⊒c★-seal-factor⊥ rs eqM eqM′ outer
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  bare⊒c★-aux⊥ rs (term-cast-inj-term eqM) eqM′ M⊒M′
c★⊒c★-seal-factor⊥ {σ = σ} rs eqM refl outer
    (cast-⊒ {p = p} {r = r} {t = t} {A = A} {B = B}
      pᶜ r≈t⨟p M⊒M′) =
  compose-right-tag-factor⊥
    (subst
      (λ t₀ → _ ∣ σ ⊢ r ≈ t₀ ⨾ⁿ p ∶ A ⊒ B)
      (term-cast-inj-coercion eqM)
      r≈t⨟p)

sealedSource⊒c★-aux⊥ :
  ∀ {Δ σ M M′ p} →
  RelevantStore σ →
  M ≡ sealedSource →
  M′ ≡ c★ →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p →
  ⊥
sealedSource⊒c★-aux⊥ rel-star eqM eqM′
    (extend {A = A} qᶜ pαᶜ M⊒M′) =
  sealedSource⊒c★-aux⊥ (rel-source {A = A}) eqM eqM′ M⊒M′
sealedSource⊒c★-aux⊥ () eqM eqM′ (split qᶜ pαᶜ M⊒M′)
sealedSource⊒c★-aux⊥ rs eqM () (⊒blame pᶜ)
sealedSource⊒c★-aux⊥ rs eqM () (x⊒x pᶜ x∋p)
sealedSource⊒c★-aux⊥ rs () eqM′ (ƛ⊒ƛ p↦qᶜ M⊒M′)
sealedSource⊒c★-aux⊥ rs () eqM′ (·⊒· qᶜ L⊒L′ M⊒M′)
sealedSource⊒c★-aux⊥ rs () eqM′ (Λ⊒Λ allᶜ vV M⊒M′)
sealedSource⊒c★-aux⊥ rs eqM () (⊒Λ pᶜ M⊒M′)
sealedSource⊒c★-aux⊥ rs eqM () (⊒⟨ν⟩ pᶜ x M⊒M′)
sealedSource⊒c★-aux⊥ rs () eqM′ (α⊒α qᶜ pαᶜ L⊒L′)
sealedSource⊒c★-aux⊥ rs eqM () (⊒α pαᶜ L⊒L′)
sealedSource⊒c★-aux⊥ rs () eqM′ (ν⊒ν pᶜ qᶜ M⊒M′)
sealedSource⊒c★-aux⊥ rs eqM () (⊒ν pᶜ M⊒M′)
sealedSource⊒c★-aux⊥ rs () eqM′ (ν⊒ pᶜ M⊒M′)
sealedSource⊒c★-aux⊥ rs () eqM′ (κ⊒κ κ)
sealedSource⊒c★-aux⊥ rs () eqM′ (⊕⊒⊕ M⊒M′ N⊒N′)
sealedSource⊒c★-aux⊥ rs refl eqM′
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  sealedSource⊒bare-aux⊥ rs refl (term-cast-inj-term eqM′) M⊒M′
sealedSource⊒c★-aux⊥ {σ = σ} rs refl eqM′
    (⊒cast- {q = q} {r = r} {s = s} {A = A} {B = B}
      qᶜ q⨟s≈r M⊒M′) =
  compose-left-tag-factor⊥
    (subst
      (λ s₀ → _ ∣ σ ⊢ q ⨾ⁿ s₀ ≈ r ∶ A ⊒ B)
      (term-cast-inj-coercion eqM′)
      q⨟s≈r)
sealedSource⊒c★-aux⊥ rs eqM refl
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  dual-eq-seal-factor⊥ (term-cast-inj-coercion eqM) r≈t⨟p
sealedSource⊒c★-aux⊥ {σ = σ} rs eqM refl
    (cast-⊒ {p = p} {r = r} {t = t} {A = A} {B = B}
      pᶜ r≈t⨟p M⊒M′) =
  c★⊒c★-seal-factor⊥ rs (term-cast-inj-term eqM) refl
    (subst
      (λ t₀ → _ ∣ σ ⊢ r ≈ t₀ ⨾ⁿ p ∶ A ⊒ B)
      (term-cast-inj-coercion eqM)
      r≈t⨟p)
    M⊒M′

badSource⊒bare-aux⊥ :
  ∀ {Δ σ M M′ p} →
  RelevantStore σ →
  M ≡ badSource →
  M′ ≡ $ k0 →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p →
  ⊥
badSource⊒bare-aux⊥ rel-star eqM eqM′
    (extend {A = A} qᶜ pαᶜ M⊒M′) =
  badSource⊒bare-aux⊥ (rel-source {A = A}) eqM eqM′ M⊒M′
badSource⊒bare-aux⊥ () eqM eqM′ (split qᶜ pαᶜ M⊒M′)
badSource⊒bare-aux⊥ rs eqM () (⊒blame pᶜ)
badSource⊒bare-aux⊥ rs eqM () (x⊒x pᶜ x∋p)
badSource⊒bare-aux⊥ rs () eqM′ (ƛ⊒ƛ p↦qᶜ M⊒M′)
badSource⊒bare-aux⊥ rs () eqM′ (·⊒· qᶜ L⊒L′ M⊒M′)
badSource⊒bare-aux⊥ rs () eqM′ (Λ⊒Λ allᶜ vV M⊒M′)
badSource⊒bare-aux⊥ rs eqM () (⊒Λ pᶜ M⊒M′)
badSource⊒bare-aux⊥ rs eqM () (⊒⟨ν⟩ pᶜ x M⊒M′)
badSource⊒bare-aux⊥ rs () eqM′ (α⊒α qᶜ pαᶜ L⊒L′)
badSource⊒bare-aux⊥ rs eqM () (⊒α pαᶜ L⊒L′)
badSource⊒bare-aux⊥ rs () eqM′ (ν⊒ν pᶜ qᶜ M⊒M′)
badSource⊒bare-aux⊥ rs eqM () (⊒ν pᶜ M⊒M′)
badSource⊒bare-aux⊥ rs () eqM′ (ν⊒ pᶜ M⊒M′)
badSource⊒bare-aux⊥ rs () refl (κ⊒κ (κℕ zero))
badSource⊒bare-aux⊥ rs () () (κ⊒κ (κℕ (suc n)))
badSource⊒bare-aux⊥ rs () eqM′ (⊕⊒⊕ M⊒M′ N⊒N′)
badSource⊒bare-aux⊥ rs eqM () (⊒cast+ qᶜ q⨟s≈r M⊒M′)
badSource⊒bare-aux⊥ rs eqM () (⊒cast- qᶜ q⨟s≈r M⊒M′)
badSource⊒bare-aux⊥ rs eqM refl
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  sealedSource⊒bare-aux⊥ rs (term-cast-inj-term eqM) refl M⊒M′
badSource⊒bare-aux⊥ {σ = σ} rs eqM refl
    (cast-⊒ {p = p} {r = r} {t = t} {A = A} {B = B}
      pᶜ r≈t⨟p M⊒M′) =
  compose-right-tag-factor⊥
    (subst
      (λ t₀ → _ ∣ σ ⊢ r ≈ t₀ ⨾ⁿ p ∶ A ⊒ B)
      (term-cast-inj-coercion eqM)
      r≈t⨟p)

badSource⊒bare⊥ :
  ∀ {Δ p} →
  Δ ∣ SigmaStar ∣ [] ⊢ badSource ⊒ $ k0 ∶ p →
  ⊥
badSource⊒bare⊥ = badSource⊒bare-aux⊥ rel-star refl refl

badSource⊒c★-aux⊥ :
  ∀ {Δ σ M M′ p} →
  RelevantStore σ →
  M ≡ badSource →
  M′ ≡ c★ →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p →
  ⊥
badSource⊒c★-aux⊥ rel-star eqM eqM′
    (extend {A = A} qᶜ pαᶜ M⊒M′) =
  badSource⊒c★-aux⊥ (rel-source {A = A}) eqM eqM′ M⊒M′
badSource⊒c★-aux⊥ () eqM eqM′ (split qᶜ pαᶜ M⊒M′)
badSource⊒c★-aux⊥ rs eqM () (⊒blame pᶜ)
badSource⊒c★-aux⊥ rs eqM () (x⊒x pᶜ x∋p)
badSource⊒c★-aux⊥ rs () eqM′ (ƛ⊒ƛ p↦qᶜ M⊒M′)
badSource⊒c★-aux⊥ rs () eqM′ (·⊒· qᶜ L⊒L′ M⊒M′)
badSource⊒c★-aux⊥ rs () eqM′ (Λ⊒Λ allᶜ vV M⊒M′)
badSource⊒c★-aux⊥ rs eqM () (⊒Λ pᶜ M⊒M′)
badSource⊒c★-aux⊥ rs eqM () (⊒⟨ν⟩ pᶜ x M⊒M′)
badSource⊒c★-aux⊥ rs () eqM′ (α⊒α qᶜ pαᶜ L⊒L′)
badSource⊒c★-aux⊥ rs eqM () (⊒α pαᶜ L⊒L′)
badSource⊒c★-aux⊥ rs () eqM′ (ν⊒ν pᶜ qᶜ M⊒M′)
badSource⊒c★-aux⊥ rs eqM () (⊒ν pᶜ M⊒M′)
badSource⊒c★-aux⊥ rs () eqM′ (ν⊒ pᶜ M⊒M′)
badSource⊒c★-aux⊥ rs () () (κ⊒κ κ)
badSource⊒c★-aux⊥ rs () eqM′ (⊕⊒⊕ M⊒M′ N⊒N′)
badSource⊒c★-aux⊥ rs refl eqM′
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  badSource⊒bare-aux⊥ rs refl (term-cast-inj-term eqM′) M⊒M′
badSource⊒c★-aux⊥ {σ = σ} rs refl eqM′
    (⊒cast- {q = q} {r = r} {s = s} {A = A} {B = B}
      qᶜ q⨟s≈r M⊒M′) =
  compose-left-tag-factor⊥
    (subst
      (λ s₀ → _ ∣ σ ⊢ q ⨾ⁿ s₀ ≈ r ∶ A ⊒ B)
      (term-cast-inj-coercion eqM′)
      q⨟s≈r)
badSource⊒c★-aux⊥ rs eqM refl
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  sealedSource⊒c★-aux⊥ rs (term-cast-inj-term eqM) refl M⊒M′
badSource⊒c★-aux⊥ {σ = σ} rs eqM refl
    (cast-⊒ {p = p} {r = r} {t = t} {A = A} {B = B}
      pᶜ r≈t⨟p M⊒M′) =
  compose-right-tag-factor⊥
    (subst
      (λ t₀ → _ ∣ σ ⊢ r ≈ t₀ ⨾ⁿ p ∶ A ⊒ B)
      (term-cast-inj-coercion eqM)
      r≈t⨟p)

badSource⊒c★⊥ :
  ∀ {Δ p} →
  Δ ∣ SigmaStar ∣ [] ⊢ badSource ⊒ c★ ∶ p →
  ⊥
badSource⊒c★⊥ = badSource⊒c★-aux⊥ rel-star refl refl

right-seal-to-idAlpha⊥ :
  ∀ {Δ q C} →
  Δ ∣ SigmaStar ⊢ q ⨾ⁿ sealStar0 ≈ idAlpha0 ∶ C ⊒ ＇ alpha0 →
  ⊥
right-seal-to-idAlpha⊥
    (compose-leftⁿ wfΣ q⊒
      (cast-seal h★ α∈Σ seal-ok , sealⁿ .★ .alpha0)
      (endpointsⁿ src-u tgt-u src-id tgt-id σ⊒ wfΣ₁ wfΣ₂ u⊒ id⊒)) =
  narrowing-var-to-older⊥ wfΣ wf★
    (subst (λ A → _ ∣ _ ∣ _ ⊢ _ ∶ A ⊒ ★) (sym src-id) q⊒)

ExactSealUnsealDGGResult : Set₁
ExactSealUnsealDGGResult =
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ p′ ]
    (badSource —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π SigmaStar ∣ [] ⊢ N ⊒ c★ ∶ p′

exact-seal-unseal-dgg-result⊥ :
  ExactSealUnsealDGGResult → ⊥
exact-seal-unseal-dgg-result⊥
    (χs , N , Δ′ , Π , Π′ , π , p′ ,
      badSource↠N , Π≡ , Π′≡ , π⊒ , N⊒c★)
    with value-multistep-refl badSource-value badSource↠N
... | χs≡[] , N≡badSource
    rewrite χs≡[] | N≡badSource | Π≡ | Π′≡
    with π⊒
... | ⊒ˢ-nil = badSource⊒c★⊥ N⊒c★

DynamicGradualGuaranteeStatement : Set₁
DynamicGradualGuaranteeStatement =
  ∀ {Δ σ M M′ N′ p χ′} →
  RuntimeOK M →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p →
  M′ —→[ χ′ ] N′ →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ] ∃[ p′ ]
    (M —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore χ′ []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N ⊒ N′ ∶ p′

dynamic-gradual-guarantee-statement⊥ :
  DynamicGradualGuaranteeStatement → ⊥
dynamic-gradual-guarantee-statement⊥ dgg =
  exact-seal-unseal-dgg-result⊥
    (dgg badSource-runtime-ok exact-tagged-sealed-source-premise′
      sealedTarget-step)
