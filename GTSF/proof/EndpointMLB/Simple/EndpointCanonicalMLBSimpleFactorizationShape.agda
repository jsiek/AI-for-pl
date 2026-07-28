module
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactorizationShape
  where

-- File Charter:
--   * Supplies shape-facing support for simple endpoint-MLB factorization.
--   * Reconstructs the two target lower bounds from the exact enumeration
--     route carried by an indexed factorization history.
--   * Transports both exact route-soundness leg shapes across retained route
--     alignment and adjacent-exchange evidence.
--   * Keeps selected `∀ⁱ` and source-only `ν` choices proof-relevant.
--   * Contains no term relation, coercion synthesis, or DGG simulation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List)
open import Data.Nat using (_<_; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import ForallPermutation using (≈∀-refl; swap01ᵗ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _↦ˢ_
  ; ∀ˢ_
  ; tag_⇛ˢ_
  ; νˢ_
  ; _⊢_≈∀ˢ_
  ; source-perm-refl
  ; source-perm-sym
  ; source-perm-trans
  ; source-perm-↦
  ; source-perm-tag-⇛
  ; source-perm-∀
  ; source-perm-ν
  ; source-swap-∀ν
  ; source-swap-ν∀
  )
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; id★
  ; idˣ
  ; idι
  ; _↦_
  ; ∀ⁱ_
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  )
open import Types using (Atom; Renameᵗ; Ty; extᵗ; renameᵗ)
import Types as T
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (target-atom-shape-unique)
open import proof.Core.Properties.ImprecisionProperties using
  (WfImpCtx²; WfImpCtx-to²; idᵢ-wf; ∀ᵢ-wf²)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactorization
  using
  ( ActiveExposure
  ; IndexedFactorWorlds
  ; active-both
  ; active-left
  ; active-right
  ; indexed-factor-paired
  ; indexed-factor-root
  ; world-common-depth
  ; world-context
  ; world-left-depth
  ; world-right-depth
  )
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePairedSpan
  using
  ( SpanCtx
  ; bothˢ
  ; leftˢ
  ; rightˢ
  )
open SpanCtx using (left-context; right-context)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleRoutes using
  ( EnumRoute
  ; route-vars
  ; route-var-star
  ; route-star-var
  ; enum-route-sound
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleSoundness using
  (νᵢᶜ-wf²)
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePermutation
  using
  ( AlignedRoutes
  ; aligned-sym
  ; aligned-trans
  ; aligned-both
  ; aligned-left
  ; aligned-right
  ; aligned-arrow
  ; aligned-arrow-star
  ; aligned-star-arrow
  ; aligned-star
  ; aligned-base
  ; aligned-base-star
  ; aligned-star-base
  ; aligned-vars
  ; aligned-var-star
  ; aligned-star-var
  ; aligned-left-right
  ; aligned-routes-≈∀
  )
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleSwapRoutes
  using
  ( Exposure
  ; bothᵉ
  ; leftᵉ
  ; rightᵉ
  ; apply-common-depth
  ; apply-left-depth
  ; apply-right-depth
  ; lr-left-context
  ; lr-right-context
  ; rl-left-context
  ; rl-right-context
  ; swap-under
  ; SwapAlignedRoutes
  ; swap-aligned-both
  ; swap-aligned-left
  ; swap-aligned-right
  ; swap-aligned-arrow
  ; swap-aligned-arrow-star
  ; swap-aligned-star-arrow
  ; swap-aligned-star
  ; swap-aligned-base
  ; swap-aligned-base-star
  ; swap-aligned-star-base
  ; swap-aligned-var
  ; swap-aligned-var-star
  ; swap-aligned-star-var
  )


indexed-target-left-wf :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  WfImpCtx²
    (world-common-depth target)
    (world-left-depth target)
    (left-context (world-context target))
indexed-target-left-wf indexed-factor-root =
  WfImpCtx-to² (idᵢ-wf _)
indexed-target-left-wf
    (indexed-factor-paired bothˢ active-both history) =
  ∀ᵢ-wf² (indexed-target-left-wf history)
indexed-target-left-wf
    (indexed-factor-paired leftˢ active-left history) =
  ∀ᵢ-wf² (indexed-target-left-wf history)
indexed-target-left-wf
    (indexed-factor-paired rightˢ active-right history) =
  νᵢᶜ-wf² (indexed-target-left-wf history)


indexed-target-right-wf :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  WfImpCtx²
    (world-common-depth target)
    (world-right-depth target)
    (right-context (world-context target))
indexed-target-right-wf indexed-factor-root =
  WfImpCtx-to² (idᵢ-wf _)
indexed-target-right-wf
    (indexed-factor-paired bothˢ active-both history) =
  ∀ᵢ-wf² (indexed-target-right-wf history)
indexed-target-right-wf
    (indexed-factor-paired leftˢ active-left history) =
  νᵢᶜ-wf² (indexed-target-right-wf history)
indexed-target-right-wf
    (indexed-factor-paired rightˢ active-right history) =
  ∀ᵢ-wf² (indexed-target-right-wf history)


indexed-target-route-sound :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ fuel A B C} →
  (history :
    IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ) →
  EnumRoute fuel
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target)
    (world-right-depth target)
    A B C →
  (left-context (world-context target)
    ∣ world-common-depth target
    ⊢ C ⊑ A
    ⊣ world-left-depth target) ×
  (right-context (world-context target)
    ∣ world-common-depth target
    ⊢ C ⊑ B
    ⊣ world-right-depth target)
indexed-target-route-sound history route =
  enum-route-sound
    (indexed-target-left-wf history)
    (indexed-target-right-wf history)
    route


source-perm-refl-shape :
  ∀ {A s s′} →
  s ≡ s′ →
  ≈∀-refl {A = A} ⊢ s ≈∀ˢ s′
source-perm-refl-shape refl = source-perm-refl


target-atom-renamed-source-shape :
  ∀ {Φ Φ′ Δᴸ Δᴸ′ Δᴿ Δᴿ′ A A′ B}
    (τ : Renameᵗ)
    (atom : Atom B)
    (eq : renameᵗ τ A ≡ A′)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ)
    (q : Φ′ ∣ Δᴸ′ ⊢ A′ ⊑ B ⊣ Δᴿ′) →
  ⌊ p ⌋ ≡ ⌊ q ⌋
target-atom-renamed-source-shape τ (T.＇ X) refl
    (idˣ x∈ X<Δᴸ Y<Δᴿ) (idˣ x∈′ X<Δᴸ′ Y<Δᴿ′) =
  refl
target-atom-renamed-source-shape τ (T.＇ X) refl
    (ν safe occ p) (ν safe′ occ′ q) =
  cong νˢ_
    (target-atom-renamed-source-shape
      (extᵗ τ) (T.＇ X) refl p q)
target-atom-renamed-source-shape τ (T.‵ ι) refl idι idι =
  refl
target-atom-renamed-source-shape τ (T.‵ ι) refl
    (ν safe occ p) (ν safe′ occ′ q) =
  cong νˢ_
    (target-atom-renamed-source-shape
      (extᵗ τ) (T.‵ ι) refl p q)
target-atom-renamed-source-shape τ T.★ refl id★ id★ =
  refl
target-atom-renamed-source-shape τ T.★ refl (tag ι) (tag .ι) =
  refl
target-atom-renamed-source-shape τ T.★ refl
    (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) =
  cong₂ tag_⇛ˢ_
    (target-atom-renamed-source-shape τ T.★ refl p₁ q₁)
    (target-atom-renamed-source-shape τ T.★ refl p₂ q₂)
target-atom-renamed-source-shape τ T.★ refl
    (tagˣ x∈ X<Δᴸ) (tagˣ x∈′ X<Δᴸ′) =
  refl
target-atom-renamed-source-shape τ T.★ refl
    (ν safe occ p) (ν safe′ occ′ q) =
  cong νˢ_
    (target-atom-renamed-source-shape
      (extᵗ τ) T.★ refl p q)


swap-aligned-leg-shapes :
  ∀ {modes : List Exposure}
    {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
    {route :
      EnumRoute fuel
        (lr-left-context modes Φᴸ)
        (lr-right-context modes Φᴿ)
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-left-depth modes (suc Δᴸ))
        (apply-right-depth modes (suc Δᴿ))
        A B C}
    {route′ :
      EnumRoute fuel
        (rl-left-context modes Φᴸ)
        (rl-right-context modes Φᴿ)
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-left-depth modes (suc Δᴸ))
        (apply-right-depth modes (suc Δᴿ))
        A B D}
    (hLL :
      WfImpCtx²
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-left-depth modes (suc Δᴸ))
        (lr-left-context modes Φᴸ))
    (hLR :
      WfImpCtx²
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-right-depth modes (suc Δᴿ))
        (lr-right-context modes Φᴿ))
    (hRL :
      WfImpCtx²
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-left-depth modes (suc Δᴸ))
        (rl-left-context modes Φᴸ))
    (hRR :
      WfImpCtx²
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-right-depth modes (suc Δᴿ))
        (rl-right-context modes Φᴿ)) →
    SwapAlignedRoutes modes route route′ →
  (⌊ proj₁ (enum-route-sound hLL hLR route) ⌋ ≡
    ⌊ proj₁ (enum-route-sound hRL hRR route′) ⌋) ×
  (⌊ proj₂ (enum-route-sound hLL hLR route) ⌋ ≡
    ⌊ proj₂ (enum-route-sound hRL hRR route′) ⌋)
swap-aligned-leg-shapes hLL hLR hRL hRR
    (swap-aligned-both aligned) =
  cong ∀ˢ_ (proj₁ inner) , cong ∀ˢ_ (proj₂ inner)
  where
  inner =
    swap-aligned-leg-shapes
      (∀ᵢ-wf² hLL) (∀ᵢ-wf² hLR)
      (∀ᵢ-wf² hRL) (∀ᵢ-wf² hRR) aligned
swap-aligned-leg-shapes hLL hLR hRL hRR
    (swap-aligned-left aligned) =
  cong ∀ˢ_ (proj₁ inner) , cong νˢ_ (proj₂ inner)
  where
  inner =
    swap-aligned-leg-shapes
      (∀ᵢ-wf² hLL) (νᵢᶜ-wf² hLR)
      (∀ᵢ-wf² hRL) (νᵢᶜ-wf² hRR) aligned
swap-aligned-leg-shapes hLL hLR hRL hRR
    (swap-aligned-right aligned) =
  cong νˢ_ (proj₁ inner) , cong ∀ˢ_ (proj₂ inner)
  where
  inner =
    swap-aligned-leg-shapes
      (νᵢᶜ-wf² hLL) (∀ᵢ-wf² hLR)
      (νᵢᶜ-wf² hRL) (∀ᵢ-wf² hRR) aligned
swap-aligned-leg-shapes hLL hLR hRL hRR
    (swap-aligned-arrow aligned₁ aligned₂) =
  cong₂ _↦ˢ_ (proj₁ inner₁) (proj₁ inner₂) ,
  cong₂ _↦ˢ_ (proj₂ inner₁) (proj₂ inner₂)
  where
  inner₁ = swap-aligned-leg-shapes hLL hLR hRL hRR aligned₁
  inner₂ = swap-aligned-leg-shapes hLL hLR hRL hRR aligned₂
swap-aligned-leg-shapes hLL hLR hRL hRR
    (swap-aligned-arrow-star aligned₁ aligned₂) =
  cong₂ _↦ˢ_ (proj₁ inner₁) (proj₁ inner₂) ,
  cong₂ tag_⇛ˢ_ (proj₂ inner₁) (proj₂ inner₂)
  where
  inner₁ = swap-aligned-leg-shapes hLL hLR hRL hRR aligned₁
  inner₂ = swap-aligned-leg-shapes hLL hLR hRL hRR aligned₂
swap-aligned-leg-shapes hLL hLR hRL hRR
    (swap-aligned-star-arrow aligned₁ aligned₂) =
  cong₂ tag_⇛ˢ_ (proj₁ inner₁) (proj₁ inner₂) ,
  cong₂ _↦ˢ_ (proj₂ inner₁) (proj₂ inner₂)
  where
  inner₁ = swap-aligned-leg-shapes hLL hLR hRL hRR aligned₁
  inner₂ = swap-aligned-leg-shapes hLL hLR hRL hRR aligned₂
swap-aligned-leg-shapes hLL hLR hRL hRR swap-aligned-star =
  refl , refl
swap-aligned-leg-shapes hLL hLR hRL hRR swap-aligned-base =
  refl , refl
swap-aligned-leg-shapes hLL hLR hRL hRR swap-aligned-base-star =
  refl , refl
swap-aligned-leg-shapes hLL hLR hRL hRR swap-aligned-star-base =
  refl , refl
swap-aligned-leg-shapes {modes = modes} hLL hLR hRL hRR
    (swap-aligned-var
      {X = X} {Y = Y} {route = route} {route′ = route′} eq) =
  target-atom-renamed-source-shape
    (swap-under modes) (T.＇ X) eq
    (proj₁ (enum-route-sound hLL hLR route))
    (proj₁ (enum-route-sound hRL hRR route′)) ,
  target-atom-renamed-source-shape
    (swap-under modes) (T.＇ Y) eq
    (proj₂ (enum-route-sound hLL hLR route))
    (proj₂ (enum-route-sound hRL hRR route′))
swap-aligned-leg-shapes {modes = modes} hLL hLR hRL hRR
    (swap-aligned-var-star
      {X = X} {route = route} {route′ = route′} eq) =
  target-atom-renamed-source-shape
    (swap-under modes) (T.＇ X) eq
    (proj₁ (enum-route-sound hLL hLR route))
    (proj₁ (enum-route-sound hRL hRR route′)) ,
  target-atom-renamed-source-shape
    (swap-under modes) T.★ eq
    (proj₂ (enum-route-sound hLL hLR route))
    (proj₂ (enum-route-sound hRL hRR route′))
swap-aligned-leg-shapes {modes = modes} hLL hLR hRL hRR
    (swap-aligned-star-var
      {Y = Y} {route = route} {route′ = route′} eq) =
  target-atom-renamed-source-shape
    (swap-under modes) T.★ eq
    (proj₁ (enum-route-sound hLL hLR route))
    (proj₁ (enum-route-sound hRL hRR route′)) ,
  target-atom-renamed-source-shape
    (swap-under modes) (T.＇ Y) eq
    (proj₂ (enum-route-sound hLL hLR route))
    (proj₂ (enum-route-sound hRL hRR route′))


aligned-routes-left-leg-shape :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
    {route : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C}
    {route′ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D}
    (hΦᴸ : WfImpCtx² Δᶜ Δᴸ Φᴸ)
    (hΦᴿ : WfImpCtx² Δᶜ Δᴿ Φᴿ)
    (aligned : AlignedRoutes route route′) →
  aligned-routes-≈∀ aligned ⊢
    ⌊ proj₁ (enum-route-sound hΦᴸ hΦᴿ route) ⌋ ≈∀ˢ
    ⌊ proj₁ (enum-route-sound hΦᴸ hΦᴿ route′) ⌋
aligned-routes-left-leg-shape hΦᴸ hΦᴿ (aligned-sym aligned) =
  source-perm-sym
    (aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned)
aligned-routes-left-leg-shape hΦᴸ hΦᴿ
    (aligned-trans aligned₁ aligned₂) =
  source-perm-trans
    (aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned₁)
    (aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned₂)
aligned-routes-left-leg-shape hΦᴸ hΦᴿ (aligned-both aligned) =
  source-perm-∀
    (aligned-routes-left-leg-shape
      (∀ᵢ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) aligned)
aligned-routes-left-leg-shape hΦᴸ hΦᴿ (aligned-left aligned) =
  source-perm-∀
    (aligned-routes-left-leg-shape
      (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ) aligned)
aligned-routes-left-leg-shape hΦᴸ hΦᴿ (aligned-right aligned) =
  source-perm-ν
    (aligned-routes-left-leg-shape
      (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) aligned)
aligned-routes-left-leg-shape hΦᴸ hΦᴿ
    (aligned-arrow aligned₁ aligned₂) =
  source-perm-↦
    (aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned₁)
    (aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned₂)
aligned-routes-left-leg-shape hΦᴸ hΦᴿ
    (aligned-arrow-star aligned₁ aligned₂) =
  source-perm-↦
    (aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned₁)
    (aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned₂)
aligned-routes-left-leg-shape hΦᴸ hΦᴿ
    (aligned-star-arrow aligned₁ aligned₂) =
  source-perm-tag-⇛
    (aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned₁)
    (aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned₂)
aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned-star =
  source-perm-refl
aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned-base =
  source-perm-refl
aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned-base-star =
  source-perm-refl
aligned-routes-left-leg-shape hΦᴸ hΦᴿ aligned-star-base =
  source-perm-refl
aligned-routes-left-leg-shape {route = route} {route′ = route′} hΦᴸ hΦᴿ
    (aligned-vars {X = X} {C = C} {C∈ = C∈} {C∈′ = C∈′}) =
  source-perm-refl-shape {A = C}
    (target-atom-shape-unique (T.＇ X)
      (proj₁ (enum-route-sound hΦᴸ hΦᴿ route))
      (proj₁ (enum-route-sound hΦᴸ hΦᴿ route′)))
aligned-routes-left-leg-shape {route = route} {route′ = route′} hΦᴸ hΦᴿ
    (aligned-var-star {X = X} {C = C} {C∈ = C∈} {C∈′ = C∈′}) =
  source-perm-refl-shape {A = C}
    (target-atom-shape-unique (T.＇ X)
      (proj₁ (enum-route-sound hΦᴸ hΦᴿ route))
      (proj₁ (enum-route-sound hΦᴸ hΦᴿ route′)))
aligned-routes-left-leg-shape {route = route} {route′ = route′} hΦᴸ hΦᴿ
    (aligned-star-var {C = C} {C∈ = C∈} {C∈′ = C∈′})
    =
  source-perm-refl-shape {A = C}
    (target-atom-shape-unique T.★
      (proj₁ (enum-route-sound hΦᴸ hΦᴿ route))
      (proj₁ (enum-route-sound hΦᴸ hΦᴿ route′)))
aligned-routes-left-leg-shape hΦᴸ hΦᴿ
    (aligned-left-right {C = C} swap-aligned) =
  source-perm-trans
    source-swap-∀ν
    (source-perm-ν
      (source-perm-∀
        (source-perm-refl-shape
          {A = renameᵗ swap01ᵗ C} (proj₁ inner))))
  where
  inner =
    swap-aligned-leg-shapes
      (νᵢᶜ-wf² (∀ᵢ-wf² hΦᴸ))
      (∀ᵢ-wf² (νᵢᶜ-wf² hΦᴿ))
      (∀ᵢ-wf² (νᵢᶜ-wf² hΦᴸ))
      (νᵢᶜ-wf² (∀ᵢ-wf² hΦᴿ))
      swap-aligned


aligned-routes-right-leg-shape :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
    {route : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C}
    {route′ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D}
    (hΦᴸ : WfImpCtx² Δᶜ Δᴸ Φᴸ)
    (hΦᴿ : WfImpCtx² Δᶜ Δᴿ Φᴿ)
    (aligned : AlignedRoutes route route′) →
  aligned-routes-≈∀ aligned ⊢
    ⌊ proj₂ (enum-route-sound hΦᴸ hΦᴿ route) ⌋ ≈∀ˢ
    ⌊ proj₂ (enum-route-sound hΦᴸ hΦᴿ route′) ⌋
aligned-routes-right-leg-shape hΦᴸ hΦᴿ (aligned-sym aligned) =
  source-perm-sym
    (aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned)
aligned-routes-right-leg-shape hΦᴸ hΦᴿ
    (aligned-trans aligned₁ aligned₂) =
  source-perm-trans
    (aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned₁)
    (aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned₂)
aligned-routes-right-leg-shape hΦᴸ hΦᴿ (aligned-both aligned) =
  source-perm-∀
    (aligned-routes-right-leg-shape
      (∀ᵢ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) aligned)
aligned-routes-right-leg-shape hΦᴸ hΦᴿ (aligned-left aligned) =
  source-perm-ν
    (aligned-routes-right-leg-shape
      (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ) aligned)
aligned-routes-right-leg-shape hΦᴸ hΦᴿ (aligned-right aligned) =
  source-perm-∀
    (aligned-routes-right-leg-shape
      (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) aligned)
aligned-routes-right-leg-shape hΦᴸ hΦᴿ
    (aligned-arrow aligned₁ aligned₂) =
  source-perm-↦
    (aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned₁)
    (aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned₂)
aligned-routes-right-leg-shape hΦᴸ hΦᴿ
    (aligned-arrow-star aligned₁ aligned₂) =
  source-perm-tag-⇛
    (aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned₁)
    (aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned₂)
aligned-routes-right-leg-shape hΦᴸ hΦᴿ
    (aligned-star-arrow aligned₁ aligned₂) =
  source-perm-↦
    (aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned₁)
    (aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned₂)
aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned-star =
  source-perm-refl
aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned-base =
  source-perm-refl
aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned-base-star =
  source-perm-refl
aligned-routes-right-leg-shape hΦᴸ hΦᴿ aligned-star-base =
  source-perm-refl
aligned-routes-right-leg-shape {route = route} {route′ = route′} hΦᴸ hΦᴿ
    (aligned-vars {Y = Y} {C = C} {C∈ = C∈} {C∈′ = C∈′}) =
  source-perm-refl-shape {A = C}
    (target-atom-shape-unique (T.＇ Y)
      (proj₂ (enum-route-sound hΦᴸ hΦᴿ route))
      (proj₂ (enum-route-sound hΦᴸ hΦᴿ route′)))
aligned-routes-right-leg-shape {route = route} {route′ = route′} hΦᴸ hΦᴿ
    (aligned-var-star {C = C} {C∈ = C∈} {C∈′ = C∈′})
    =
  source-perm-refl-shape {A = C}
    (target-atom-shape-unique T.★
      (proj₂ (enum-route-sound hΦᴸ hΦᴿ route))
      (proj₂ (enum-route-sound hΦᴸ hΦᴿ route′)))
aligned-routes-right-leg-shape {route = route} {route′ = route′} hΦᴸ hΦᴿ
    (aligned-star-var {Y = Y} {C = C} {C∈ = C∈} {C∈′ = C∈′}) =
  source-perm-refl-shape {A = C}
    (target-atom-shape-unique (T.＇ Y)
      (proj₂ (enum-route-sound hΦᴸ hΦᴿ route))
      (proj₂ (enum-route-sound hΦᴸ hΦᴿ route′)))
aligned-routes-right-leg-shape hΦᴸ hΦᴿ
    (aligned-left-right {C = C} swap-aligned) =
  source-perm-trans
    source-swap-ν∀
    (source-perm-∀
      (source-perm-ν
        (source-perm-refl-shape
          {A = renameᵗ swap01ᵗ C} (proj₂ inner))))
  where
  inner =
    swap-aligned-leg-shapes
      (νᵢᶜ-wf² (∀ᵢ-wf² hΦᴸ))
      (∀ᵢ-wf² (νᵢᶜ-wf² hΦᴿ))
      (∀ᵢ-wf² (νᵢᶜ-wf² hΦᴸ))
      (νᵢᶜ-wf² (∀ᵢ-wf² hΦᴿ))
      swap-aligned


------------------------------------------------------------------------
-- Direct shape support for the route-factor worker
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; zero; suc; _<_; s<s; z<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (yes; no)
open import Imprecision using (NonVar; idᵢ; _ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionComposition using
  ( _；_≋_
  ; comp-id★
  ; comp-idˣ-idˣ
  ; comp-idˣ-tagˣ
  ; comp-idι-idι
  ; comp-idι-tag
  ; comp-↦-↦
  ; comp-↦-tag
  ; comp-∀-∀
  ; comp-∀-ν
  ; comp-tag-id★
  ; comp-tag-⇛-id★
  ; comp-tagˣ-id★
  ; comp-ν
  ; id★ˢ
  ; idˣˢ
  ; _↦ˢ_
  ; ∀ˢ_
  ; tag_⇛ˢ_
  ; tagˣˢ
  ; νˢ_
  )
open import ImprecisionWf using
  ( id★
  ; idι
  ; _↦_
  ; ∀ⁱ_
  ; tag_
  ; tag_⇛_
  ; ν
  ; ⊑-src-wf
  )
open import Types using
  ( ＇_
  ; WfTy
  ; wfVar
  ; wfBase
  ; wf★
  ; wf⇒
  ; wf∀
  ; occurs
  ; substᵗ
  ; substVarFrom
  )
open import proof.Core.Properties.ImprecisionCompositionProperties using
  (compose-assoc-left; shape-trans-left-idᵢ)
open import proof.Core.Properties.NuImprecisionTransitivityProperties using
  (⊑-trans-left-idᵢ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (shape-open-unused-atᵢ; shape-subst-source; shape-subst-target)
open import proof.Core.Properties.TypeProperties using (occurs-suc-var)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using
  ( DropAtᵢ
  ; drop-zeroᵢ
  ; drop-∀ᵢ
  ; drop-νᵢ
  ; occurs-var-true→≡ᵢ
  ; open-unused-atᵢ
  ; removeAt-Wfᵢ
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using
  (∀ᵢᶜ; νᵢᶜ)
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleCompleteness
  using
  ( SourceFuel
  ; source-ok
  ; sourceFuelFor
  ; StarInstCtxᵢ
  ; StarInst-zeroᵢ
  ; StarInst-∀ᵢ
  ; drop-var-freshᵢ
  ; inst-star-atᵢ
  ; inst-starᵢ
  ; close-star-lowerᵢ
  ; star-inst-lower-atᵢ
  ; star-inst-lowerᵢ
  ; subst-star-fresh-varᵢ
  ; subst-star-hit-varᵢ
  )
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePairedSpan
  using
  ( PairedLower
  ; pair-lower
  ; paired-lower-left
  ; paired-lower-right
  ; paired-star
  ; paired-base-base
  ; paired-base-star
  ; paired-star-base
  ; paired-base-stars
  ; paired-arrow-arrow
  ; paired-arrow-star
  ; paired-star-arrow
  ; paired-arrow-stars
  ; paired-var-var
  ; paired-var-star
  ; paired-star-var
  ; paired-var-stars
  ; paired-both
  ; paired-left
  ; paired-right
  ; paired-neither
  ; neitherˢ
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleRoutes using
  ( route-both
  ; route-left
  ; route-right
  ; route-star
  ; route-base
  ; route-base-star
  ; route-star-base
  ; route-arrow
  ; route-arrow-star
  ; route-star-arrow
  )


pair-lower-left-shape :
  ∀ {Σ Δᶜ Δᴸ Δᴿ C A B}
    (p : left-context Σ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ)
    (q : right-context Σ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ) →
  ⌊ paired-lower-left (pair-lower p q) ⌋ ≡ ⌊ p ⌋
pair-lower-left-shape id★ id★ = refl
pair-lower-left-shape idι idι = refl
pair-lower-left-shape idι (tag ι) = refl
pair-lower-left-shape (tag ι) idι = refl
pair-lower-left-shape (tag ι) (tag .ι) = refl
pair-lower-left-shape (p₁ ↦ p₂) (q₁ ↦ q₂) =
  cong₂ _↦ˢ_
    (pair-lower-left-shape p₁ q₁)
    (pair-lower-left-shape p₂ q₂)
pair-lower-left-shape (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  cong₂ _↦ˢ_
    (pair-lower-left-shape p₁ q₁)
    (pair-lower-left-shape p₂ q₂)
pair-lower-left-shape (tag p₁ ⇛ p₂) (q₁ ↦ q₂) =
  cong₂ tag_⇛ˢ_
    (pair-lower-left-shape p₁ q₁)
    (pair-lower-left-shape p₂ q₂)
pair-lower-left-shape (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) =
  cong₂ tag_⇛ˢ_
    (pair-lower-left-shape p₁ q₁)
    (pair-lower-left-shape p₂ q₂)
pair-lower-left-shape
    (idˣ x∈ X<Δ Y<Δ) (idˣ y∈ X<Δ′ Y<Δ′) =
  refl
pair-lower-left-shape (idˣ x∈ X<Δ Y<Δ) (tagˣ y∈ X<Δ′) =
  refl
pair-lower-left-shape (tagˣ x∈ X<Δ) (idˣ y∈ X<Δ′ Y<Δ) =
  refl
pair-lower-left-shape (tagˣ x∈ X<Δ) (tagˣ y∈ X<Δ′) =
  refl
pair-lower-left-shape (∀ⁱ p) (∀ⁱ q) =
  cong ∀ˢ_ (pair-lower-left-shape p q)
pair-lower-left-shape (∀ⁱ p) (ν safe occ q) =
  cong ∀ˢ_ (pair-lower-left-shape p q)
pair-lower-left-shape (ν safe occ p) (∀ⁱ q) =
  cong νˢ_ (pair-lower-left-shape p q)
pair-lower-left-shape (ν safe occ p) (ν safe′ occ′ q) =
  cong νˢ_ (pair-lower-left-shape p q)


pair-lower-right-shape :
  ∀ {Σ Δᶜ Δᴸ Δᴿ C A B}
    (p : left-context Σ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ)
    (q : right-context Σ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ) →
  ⌊ paired-lower-right (pair-lower p q) ⌋ ≡ ⌊ q ⌋
pair-lower-right-shape id★ id★ = refl
pair-lower-right-shape idι idι = refl
pair-lower-right-shape idι (tag ι) = refl
pair-lower-right-shape (tag ι) idι = refl
pair-lower-right-shape (tag ι) (tag .ι) = refl
pair-lower-right-shape (p₁ ↦ p₂) (q₁ ↦ q₂) =
  cong₂ _↦ˢ_
    (pair-lower-right-shape p₁ q₁)
    (pair-lower-right-shape p₂ q₂)
pair-lower-right-shape (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  cong₂ tag_⇛ˢ_
    (pair-lower-right-shape p₁ q₁)
    (pair-lower-right-shape p₂ q₂)
pair-lower-right-shape (tag p₁ ⇛ p₂) (q₁ ↦ q₂) =
  cong₂ _↦ˢ_
    (pair-lower-right-shape p₁ q₁)
    (pair-lower-right-shape p₂ q₂)
pair-lower-right-shape (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) =
  cong₂ tag_⇛ˢ_
    (pair-lower-right-shape p₁ q₁)
    (pair-lower-right-shape p₂ q₂)
pair-lower-right-shape
    (idˣ x∈ X<Δ Y<Δ) (idˣ y∈ X<Δ′ Y<Δ′) =
  refl
pair-lower-right-shape (idˣ x∈ X<Δ Y<Δ) (tagˣ y∈ X<Δ′) =
  refl
pair-lower-right-shape (tagˣ x∈ X<Δ) (idˣ y∈ X<Δ′ Y<Δ) =
  refl
pair-lower-right-shape (tagˣ x∈ X<Δ) (tagˣ y∈ X<Δ′) =
  refl
pair-lower-right-shape (∀ⁱ p) (∀ⁱ q) =
  cong ∀ˢ_ (pair-lower-right-shape p q)
pair-lower-right-shape (∀ⁱ p) (ν safe occ q) =
  cong νˢ_ (pair-lower-right-shape p q)
pair-lower-right-shape (ν safe occ p) (∀ⁱ q) =
  cong ∀ˢ_ (pair-lower-right-shape p q)
pair-lower-right-shape (ν safe occ p) (ν safe′ occ′ q) =
  cong νˢ_ (pair-lower-right-shape p q)


data VarOccurrenceᵢ (k X : ℕ) : Set where
  hitᵢ :
    occurs k (＇ X) ≡ true →
    VarOccurrenceᵢ k X

  freshᵢ :
    occurs k (＇ X) ≡ false →
    VarOccurrenceᵢ k X


classify-var-occurrenceᵢ :
  ∀ k X →
  VarOccurrenceᵢ k X
classify-var-occurrenceᵢ zero zero = hitᵢ refl
classify-var-occurrenceᵢ zero (suc X) = freshᵢ refl
classify-var-occurrenceᵢ (suc k) zero = freshᵢ refl
classify-var-occurrenceᵢ (suc k) (suc X)
    with classify-var-occurrenceᵢ k X
classify-var-occurrenceᵢ (suc k) (suc X) | hitᵢ occ =
  hitᵢ (trans (sym (occurs-suc-var k X)) occ)
classify-var-occurrenceᵢ (suc k) (suc X) | freshᵢ occ =
  freshᵢ (trans (sym (occurs-suc-var k X)) occ)


star-inst-tag-hit-shapesᵢ :
  ∀ {k Φˢ Ψ Δˢ Δ Δᴿ X} →
  (occ : occurs k (＇ X) ≡ true) →
  (star-proof :
    Φˢ ∣ suc Δˢ ⊢ ＇ X ⊑
      substᵗ (substVarFrom k T.★) (＇ X) ⊣ Δˢ) →
  (inst-proof :
    Ψ ∣ Δ ⊢ substᵗ (substVarFrom k T.★) (＇ X) ⊑ T.★ ⊣ Δᴿ) →
  ⌊ star-proof ⌋ ； ⌊ inst-proof ⌋ ≋ tagˣˢ
star-inst-tag-hit-shapesᵢ {k = k} {X = X} occ
    star-proof inst-proof
    with
      subst
        (λ T → _ ∣ _ ⊢ ＇ X ⊑ T ⊣ _)
        (subst-star-hit-varᵢ k X occ)
        star-proof in normalized-star-eq
       | subst
           (λ S → _ ∣ _ ⊢ S ⊑ T.★ ⊣ _)
           (subst-star-hit-varᵢ k X occ)
           inst-proof in normalized-inst-eq
star-inst-tag-hit-shapesᵢ {k = k} {X = X} occ
    star-proof inst-proof
    | tagˣ x∈ X<Δ | id★
    rewrite
      sym
        (shape-subst-target
          (subst-star-hit-varᵢ k X occ)
          star-proof)
    | sym
        (shape-subst-source
          (subst-star-hit-varᵢ k X occ)
          inst-proof)
    | cong ⌊_⌋ normalized-star-eq
    | cong ⌊_⌋ normalized-inst-eq =
  comp-tagˣ-id★


star-inst-tag-fresh-shapesᵢ :
  ∀ {k Φˢ Ψ Δˢ Δ Δᴿ X} →
  (occ : occurs k (＇ X) ≡ false) →
  (star-proof :
    Φˢ ∣ suc Δˢ ⊢ ＇ X ⊑
      substᵗ (substVarFrom k T.★) (＇ X) ⊣ Δˢ) →
  (inst-proof :
    Ψ ∣ Δ ⊢ substᵗ (substVarFrom k T.★) (＇ X) ⊑ T.★ ⊣ Δᴿ) →
  ⌊ star-proof ⌋ ； ⌊ inst-proof ⌋ ≋ tagˣˢ
star-inst-tag-fresh-shapesᵢ {k = k} {X = X} occ
    star-proof inst-proof
    with
      subst
        (λ T → _ ∣ _ ⊢ ＇ X ⊑ T ⊣ _)
        (subst-star-fresh-varᵢ k X occ)
        star-proof in normalized-star-eq
       | subst
           (λ S → _ ∣ _ ⊢ S ⊑ T.★ ⊣ _)
           (subst-star-fresh-varᵢ k X occ)
           inst-proof in normalized-inst-eq
star-inst-tag-fresh-shapesᵢ {k = k} {X = X} occ
    star-proof inst-proof
    | idˣ x∈ X<Δ Y<Δ | tagˣ x∈′ X<Δ′
    rewrite
      sym
        (shape-subst-target
          (subst-star-fresh-varᵢ k X occ)
          star-proof)
    | sym
        (shape-subst-source
          (subst-star-fresh-varᵢ k X occ)
          inst-proof)
    | cong ⌊_⌋ normalized-star-eq
    | cong ⌊_⌋ normalized-inst-eq =
  comp-idˣ-tagˣ


star-inst-shape-triangle-atᵢ :
  ∀ {k Φˢ Φ Ψ Δˢ Δ Δᴿ C A}
    (star : StarInstCtxᵢ k Φˢ Δˢ)
    (drop : DropAtᵢ k Φ Ψ)
    (k<Δ : k < suc Δ)
    (hC : WfTy (suc Δˢ) C)
    (p : Φ ∣ suc Δ ⊢ C ⊑ A ⊣ Δᴿ) →
  ⌊ star-inst-lower-atᵢ star hC ⌋ ；
  ⌊ inst-star-atᵢ drop k<Δ p ⌋ ≋
  ⌊ p ⌋
star-inst-shape-triangle-atᵢ star drop k<Δ wf★ id★ =
  comp-id★
star-inst-shape-triangle-atᵢ {k = k} star drop k<Δ
    (wfVar X<Δˢ) (idˣ {X = X} {Y = Y} x∈ X<Δ Y<Δ)
    with occurs k (＇ X) in occ
       | star-inst-lower-atᵢ star (wfVar X<Δˢ)
       | inst-star-atᵢ drop k<Δ (idˣ x∈ X<Δ Y<Δ)
star-inst-shape-triangle-atᵢ {k = k} star drop k<Δ
    (wfVar X<Δˢ) (idˣ {X = X} {Y = Y} x∈ X<Δ Y<Δ)
    | true | star-proof | inst-proof
    with trans (sym occ) (drop-var-freshᵢ drop x∈)
star-inst-shape-triangle-atᵢ {k = k} star drop k<Δ
    (wfVar X<Δˢ)
    (idˣ {X = X} {Y = Y} x∈ X<Δ Y<Δ)
    | true | star-proof | inst-proof | ()
star-inst-shape-triangle-atᵢ {k = k} star drop k<Δ
    (wfVar X<Δˢ)
    (idˣ {X = X} {Y = Y} x∈ X<Δ Y<Δ)
    | false | star-proof | inst-proof
    with
      subst
        (λ T → _ ∣ _ ⊢ ＇ X ⊑ T ⊣ _)
        (subst-star-fresh-varᵢ k X occ)
        star-proof in normalized-star-eq
       | subst
           (λ S → _ ∣ _ ⊢ S ⊑ ＇ Y ⊣ _)
           (subst-star-fresh-varᵢ k X occ)
           inst-proof in normalized-inst-eq
star-inst-shape-triangle-atᵢ {k = k} star drop k<Δ
    (wfVar X<Δˢ)
    (idˣ {X = X} {Y = Y} x∈ X<Δ Y<Δ)
    | false | star-proof | inst-proof
    | idˣ x∈′ X<Δ′ Y<Δ′ | idˣ x∈″ X<Δ″ Y<Δ″
    rewrite
      sym
        (shape-subst-target
          (subst-star-fresh-varᵢ k X occ)
          star-proof)
    | sym
        (shape-subst-source
          (subst-star-fresh-varᵢ k X occ)
          inst-proof)
    | cong ⌊_⌋ normalized-star-eq
    | cong ⌊_⌋ normalized-inst-eq =
  comp-idˣ-idˣ
star-inst-shape-triangle-atᵢ star drop k<Δ wfBase idι =
  comp-idι-idι
star-inst-shape-triangle-atᵢ star drop k<Δ
    (wf⇒ hC hD) (p ↦ q) =
  comp-↦-↦
    (star-inst-shape-triangle-atᵢ star drop k<Δ hC p)
    (star-inst-shape-triangle-atᵢ star drop k<Δ hD q)
star-inst-shape-triangle-atᵢ star drop k<Δ
    (wf∀ hC) (∀ⁱ p) =
  comp-∀-∀
    (star-inst-shape-triangle-atᵢ
      (StarInst-∀ᵢ star) (drop-∀ᵢ drop) (s<s k<Δ) hC p)
star-inst-shape-triangle-atᵢ star drop k<Δ wfBase (tag ι) =
  comp-idι-tag
star-inst-shape-triangle-atᵢ star drop k<Δ
    (wf⇒ hC hD) (tag p ⇛ q) =
  comp-↦-tag
    (star-inst-shape-triangle-atᵢ star drop k<Δ hC p)
    (star-inst-shape-triangle-atᵢ star drop k<Δ hD q)
star-inst-shape-triangle-atᵢ {k = k} star drop k<Δ
    (wfVar X<Δˢ) (tagˣ {X = X} x∈ X<Δ)
    with classify-var-occurrenceᵢ k X
star-inst-shape-triangle-atᵢ {k = k} star drop k<Δ
    (wfVar X<Δˢ) (tagˣ {X = X} x∈ X<Δ)
    | hitᵢ occ
    =
  star-inst-tag-hit-shapesᵢ occ
    (star-inst-lower-atᵢ star (wfVar X<Δˢ))
    (inst-star-atᵢ drop k<Δ (tagˣ x∈ X<Δ))
star-inst-shape-triangle-atᵢ {k = k} star drop k<Δ
    (wfVar X<Δˢ) (tagˣ {X = X} x∈ X<Δ)
    | freshᵢ occ
    =
  star-inst-tag-fresh-shapesᵢ occ
    (star-inst-lower-atᵢ star (wfVar X<Δˢ))
    (inst-star-atᵢ drop k<Δ (tagˣ x∈ X<Δ))
star-inst-shape-triangle-atᵢ star drop k<Δ
    (wf∀ hC) (ν safe occ p) =
  comp-∀-ν
    (star-inst-shape-triangle-atᵢ
      (StarInst-∀ᵢ star) (drop-νᵢ drop) (s<s k<Δ) hC p)


star-inst-shape-triangleᵢ :
  ∀ {Φ Δˢ Δ Δᴿ C A} →
  (hC : WfTy (suc Δˢ) C) →
    (p : νᵢᶜ Φ ∣ suc Δ ⊢ C ⊑ A ⊣ Δᴿ) →
  ⌊ star-inst-lowerᵢ hC ⌋ ；
  ⌊ inst-starᵢ p ⌋ ≋
  ⌊ p ⌋
star-inst-shape-triangleᵢ {Δˢ = Δˢ} hC p =
  star-inst-shape-triangle-atᵢ
    (StarInst-zeroᵢ Δˢ) drop-zeroᵢ z<s hC p


open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactorization
  using
  ( BinderFree
  ; free-★
  ; free-var
  ; free-base
  ; free-arrow
  ; DirectTerminalFactor
  ; direct-star
  ; direct-base
  ; direct-base-star
  ; direct-arrow
  ; direct-arrow-star
  ; direct-variable
  ; direct-variable-star
  ; direct-terminal-factor
  ; indexed-direct-terminal-imprecision
  ; indexed-source-depth
  ; paired-both-compatible-route
  ; paired-left-compatible-route
  ; paired-right-compatible-route
  ; paired-inst-star
  ; route-factor-worker
  ; source-fuel-arrow-left
  ; source-fuel-arrow-right
  ; source-fuel-inst-star
  ; star-factor-worker
  )


direct-terminal-factor-shapes :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ fuel C D A B}
    (history :
      IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ)
    (lower :
      PairedLower
        (world-context source) (world-common-depth source) C A B
        (world-left-depth source) (world-right-depth source))
    (route :
      EnumRoute fuel
        (left-context (world-context target))
        (right-context (world-context target))
        (world-common-depth target)
        (world-left-depth target) (world-right-depth target) A B D)
    (direct : DirectTerminalFactor source target C D) →
  let factor = indexed-direct-terminal-imprecision history direct
      target-lower = indexed-target-route-sound history route
  in
  (⌊ factor ⌋ ； ⌊ proj₁ target-lower ⌋ ≋
    ⌊ paired-lower-left lower ⌋) ×
  (⌊ factor ⌋ ； ⌊ proj₂ target-lower ⌋ ≋
    ⌊ paired-lower-right lower ⌋)
direct-terminal-factor-shapes history paired-star route-star direct-star =
  comp-id★ , comp-id★
direct-terminal-factor-shapes
    history paired-base-base route-base direct-base =
  comp-idι-idι , comp-idι-idι
direct-terminal-factor-shapes
    history paired-base-star route-base-star direct-base =
  comp-idι-idι , comp-idι-tag
direct-terminal-factor-shapes
    history paired-star-base route-star-base direct-base =
  comp-idι-tag , comp-idι-idι
direct-terminal-factor-shapes
    history paired-base-stars route-star direct-base-star =
  comp-tag-id★ , comp-tag-id★
direct-terminal-factor-shapes history
    (paired-arrow-arrow lower₁ lower₂)
    (route-arrow route₁ route₂)
    (direct-arrow direct₁ direct₂)
    with direct-terminal-factor-shapes history lower₁ route₁ direct₁
       | direct-terminal-factor-shapes history lower₂ route₂ direct₂
direct-terminal-factor-shapes history
    (paired-arrow-arrow lower₁ lower₂)
    (route-arrow route₁ route₂)
    (direct-arrow direct₁ direct₂)
    | left₁ , right₁ | left₂ , right₂ =
  comp-↦-↦ left₁ left₂ , comp-↦-↦ right₁ right₂
direct-terminal-factor-shapes history
    (paired-arrow-star lower₁ lower₂)
    (route-arrow-star route₁ route₂)
    (direct-arrow direct₁ direct₂)
    with direct-terminal-factor-shapes history lower₁ route₁ direct₁
       | direct-terminal-factor-shapes history lower₂ route₂ direct₂
direct-terminal-factor-shapes history
    (paired-arrow-star lower₁ lower₂)
    (route-arrow-star route₁ route₂)
    (direct-arrow direct₁ direct₂)
    | left₁ , right₁ | left₂ , right₂ =
  comp-↦-↦ left₁ left₂ , comp-↦-tag right₁ right₂
direct-terminal-factor-shapes history
    (paired-star-arrow lower₁ lower₂)
    (route-star-arrow route₁ route₂)
    (direct-arrow direct₁ direct₂)
    with direct-terminal-factor-shapes history lower₁ route₁ direct₁
       | direct-terminal-factor-shapes history lower₂ route₂ direct₂
direct-terminal-factor-shapes history
    (paired-star-arrow lower₁ lower₂)
    (route-star-arrow route₁ route₂)
    (direct-arrow direct₁ direct₂)
    | left₁ , right₁ | left₂ , right₂ =
  comp-↦-tag left₁ left₂ , comp-↦-↦ right₁ right₂
direct-terminal-factor-shapes history
    (paired-arrow-stars lower₁ lower₂) route-star
    (direct-arrow-star direct₁ direct₂)
    with direct-terminal-factor-shapes
      history lower₁ (route-star {fuel = zero}) direct₁
       | direct-terminal-factor-shapes
           history lower₂ (route-star {fuel = zero}) direct₂
direct-terminal-factor-shapes history
    (paired-arrow-stars lower₁ lower₂) route-star
    (direct-arrow-star direct₁ direct₂)
    | left₁ , right₁ | left₂ , right₂ =
  comp-tag-⇛-id★ left₁ left₂ ,
  comp-tag-⇛-id★ right₁ right₂
direct-terminal-factor-shapes history
    (paired-var-var row Z<Δ X<Δ Y<Δ) route@(route-vars W∈)
    (direct-variable Z<Δ′ W<Δ pull)
    with indexed-target-route-sound history route
direct-terminal-factor-shapes history
    (paired-var-var row Z<Δ X<Δ Y<Δ) (route-vars W∈)
    (direct-variable Z<Δ′ W<Δ pull)
    | idˣ x∈ X<Δ′ Y<Δ′ , idˣ y∈ X<Δ″ Y<Δ″ =
  comp-idˣ-idˣ , comp-idˣ-idˣ
direct-terminal-factor-shapes {D = T.★} history
    (paired-var-var row Z<Δ X<Δ Y<Δ) route@(route-vars W∈) direct
    with indexed-target-route-sound history route
direct-terminal-factor-shapes {D = T.★} history
    (paired-var-var row Z<Δ X<Δ Y<Δ) (route-vars W∈) direct
    | ()
direct-terminal-factor-shapes history
    (paired-var-star row Z<Δ X<Δ) route@(route-var-star W∈)
    (direct-variable Z<Δ′ W<Δ pull)
    with indexed-target-route-sound history route
direct-terminal-factor-shapes history
    (paired-var-star row Z<Δ X<Δ) (route-var-star W∈)
    (direct-variable Z<Δ′ W<Δ pull)
    | idˣ x∈ X<Δ′ Y<Δ′ , tagˣ y∈ X<Δ″ =
  comp-idˣ-idˣ , comp-idˣ-tagˣ
direct-terminal-factor-shapes {D = T.★} history
    (paired-var-star row Z<Δ X<Δ) route@(route-var-star W∈) direct
    with indexed-target-route-sound history route
direct-terminal-factor-shapes {D = T.★} history
    (paired-var-star row Z<Δ X<Δ) (route-var-star W∈) direct
    | ()
direct-terminal-factor-shapes history
    (paired-star-var row Z<Δ Y<Δ) route@(route-star-var W∈)
    (direct-variable Z<Δ′ W<Δ pull)
    with indexed-target-route-sound history route
direct-terminal-factor-shapes history
    (paired-star-var row Z<Δ Y<Δ) (route-star-var W∈)
    (direct-variable Z<Δ′ W<Δ pull)
    | tagˣ x∈ X<Δ′ , idˣ y∈ X<Δ″ Y<Δ″ =
  comp-idˣ-tagˣ , comp-idˣ-idˣ
direct-terminal-factor-shapes {D = T.★} history
    (paired-star-var row Z<Δ Y<Δ) route@(route-star-var W∈) direct
    with indexed-target-route-sound history route
direct-terminal-factor-shapes {D = T.★} history
    (paired-star-var row Z<Δ Y<Δ) (route-star-var W∈) direct
    | target-left , ()
direct-terminal-factor-shapes history
    (paired-var-stars row Z<Δ) route-star
    (direct-variable-star Z<Δ′ source-row) =
  comp-tagˣ-id★ , comp-tagˣ-id★


star-factor-worker-shapes :
  ∀ (sourceFuel : ℕ)
    {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ C} →
  (source-evidence : SourceFuel sourceFuel C) →
  (history :
    IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ) →
  (lower :
    PairedLower
      (world-context source) (world-common-depth source) C T.★ T.★
      (world-left-depth source) (world-right-depth source)) →
  (⌊ star-factor-worker
      sourceFuel source-evidence history lower ⌋ ；
    id★ˢ ≋ ⌊ paired-lower-left lower ⌋) ×
  (⌊ star-factor-worker
      sourceFuel source-evidence history lower ⌋ ；
    id★ˢ ≋ ⌊ paired-lower-right lower ⌋)
star-factor-worker-shapes zero () history lower
star-factor-worker-shapes sourceFuel source-evidence history paired-star
    with star-factor-worker
      sourceFuel source-evidence history paired-star
star-factor-worker-shapes sourceFuel source-evidence history paired-star
    | id★ =
  comp-id★ , comp-id★
star-factor-worker-shapes sourceFuel source-evidence history
    paired-base-stars
    with star-factor-worker
      sourceFuel source-evidence history paired-base-stars
star-factor-worker-shapes sourceFuel source-evidence history
    paired-base-stars
    | tag ι =
  comp-tag-id★ , comp-tag-id★
star-factor-worker-shapes sourceFuel source-evidence history
    (paired-var-stars row Z<Δ)
    with star-factor-worker
      sourceFuel source-evidence history (paired-var-stars row Z<Δ)
star-factor-worker-shapes sourceFuel source-evidence history
    (paired-var-stars row Z<Δ)
    | tagˣ x∈ X<Δ′ =
  comp-tagˣ-id★ , comp-tagˣ-id★
star-factor-worker-shapes .(suc zero)
    (source-ok {budget = zero} ()) history
    (paired-arrow-stars lower₁ lower₂)
star-factor-worker-shapes (suc (suc sourceFuel)) source-evidence history
    (paired-arrow-stars lower₁ lower₂)
    with star-factor-worker-shapes (suc sourceFuel)
      (source-fuel-arrow-left source-evidence) history lower₁
       | star-factor-worker-shapes (suc sourceFuel)
           (source-fuel-arrow-right source-evidence) history lower₂
star-factor-worker-shapes (suc (suc sourceFuel)) source-evidence history
    (paired-arrow-stars lower₁ lower₂)
    | left₁ , right₁ | left₂ , right₂ =
  comp-tag-⇛-id★ left₁ left₂ ,
  comp-tag-⇛-id★ right₁ right₂
star-factor-worker-shapes .(suc zero)
    (source-ok {budget = zero} ()) history
    (paired-neither {{safe}} occ lower)
star-factor-worker-shapes (suc (suc sourceFuel)) source-evidence history
    (paired-neither {C = C} {{safe}} occ lower)
    with star-factor-worker-shapes (suc sourceFuel)
      (source-fuel-inst-star source-evidence) history
      (paired-inst-star lower)
star-factor-worker-shapes (suc (suc sourceFuel)) source-evidence history
    (paired-neither {C = C} {{safe}} occ lower)
    | recursive-left , recursive-right =
  compose-assoc-left
    factor-composition
    instantiated-left
    (comp-ν
      (star-inst-shape-triangleᵢ
        source-wf (paired-lower-left lower))) ,
  compose-assoc-left
    factor-composition
    instantiated-right
    (comp-ν
      (star-inst-shape-triangleᵢ
        source-wf (paired-lower-right lower)))
  where
    source-wf =
      subst (λ Δ → WfTy (suc Δ) C)
        (indexed-source-depth history)
        (⊑-src-wf (paired-lower-left lower))

    close-factor = close-star-lowerᵢ {{safe}} occ source-wf

    recursive-factor =
      star-factor-worker (suc sourceFuel)
        (source-fuel-inst-star source-evidence)
        history (paired-inst-star lower)

    factor-composition =
      shape-trans-left-idᵢ close-factor recursive-factor

    instantiated-left =
      subst
        (λ shape →
          ⌊ recursive-factor ⌋ ； id★ˢ ≋ shape)
        (pair-lower-left-shape
          (inst-starᵢ (paired-lower-left lower))
          (inst-starᵢ (paired-lower-right lower)))
        recursive-left

    instantiated-right =
      subst
        (λ shape →
          ⌊ recursive-factor ⌋ ； id★ˢ ≋ shape)
        (pair-lower-right-shape
          (inst-starᵢ (paired-lower-left lower))
          (inst-starᵢ (paired-lower-right lower)))
        recursive-right


route-factor-worker-shapes :
  ∀ (fuel sourceFuel : ℕ)
    {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ C A B D} →
  (source-evidence : SourceFuel sourceFuel C) →
  (history :
    IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ) →
  (lower :
    PairedLower
      (world-context source) (world-common-depth source) C A B
      (world-left-depth source) (world-right-depth source)) →
  (route :
    EnumRoute fuel
      (left-context (world-context target))
      (right-context (world-context target))
      (world-common-depth target)
      (world-left-depth target) (world-right-depth target) A B D) →
  let result =
        route-factor-worker
          fuel sourceFuel source-evidence history lower route
      route′ = proj₁ (proj₂ result)
      factor = proj₂ (proj₂ result)
      target-lower = indexed-target-route-sound history route′
  in
  (⌊ factor ⌋ ； ⌊ proj₁ target-lower ⌋ ≋
    ⌊ paired-lower-left lower ⌋) ×
  (⌊ factor ⌋ ； ⌊ proj₂ target-lower ⌋ ≋
    ⌊ paired-lower-right lower ⌋)
route-factor-worker-shapes zero sourceFuel source-evidence history lower ()
route-factor-worker-shapes (suc fuel) zero () history lower route
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    source-evidence@(source-ok {budget = sourceBudget} enough) history
    lower@(paired-arrow-stars lower₁ lower₂) route-star
    with star-factor-worker
      (suc sourceBudget) source-evidence history lower
       | star-factor-worker-shapes
           (suc sourceBudget) source-evidence history lower
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    source-evidence@(source-ok {budget = sourceBudget} enough) history
    lower@(paired-arrow-stars lower₁ lower₂) route-star
    | factor | factor-shapes =
  factor-shapes
route-factor-worker-shapes
    (suc fuel) .(suc zero) (source-ok {budget = zero} ()) history
    (paired-neither {{safe}} occ lower) route
route-factor-worker-shapes
    (suc fuel) (suc (suc sourceFuel)) source-evidence history
    (paired-neither {C = C} {{safe}} occ lower) route
    with
      route-factor-worker
        (suc fuel) (suc sourceFuel)
        (source-fuel-inst-star source-evidence)
        history (paired-inst-star lower) route
       | route-factor-worker-shapes
           (suc fuel) (suc sourceFuel)
           (source-fuel-inst-star source-evidence)
           history (paired-inst-star lower) route
route-factor-worker-shapes
    (suc fuel) (suc (suc sourceFuel)) source-evidence history
    (paired-neither {C = C} {{safe}} occ lower) route
    | F , route′ , factor | recursive-left , recursive-right =
  compose-assoc-left
    factor-composition
    instantiated-left
    (comp-ν
      (star-inst-shape-triangleᵢ
        source-wf (paired-lower-left lower))) ,
  compose-assoc-left
    factor-composition
    instantiated-right
    (comp-ν
      (star-inst-shape-triangleᵢ
        source-wf (paired-lower-right lower)))
  where
    source-wf =
      subst (λ Δ → WfTy (suc Δ) C)
        (indexed-source-depth history)
        (⊑-src-wf (paired-lower-left lower))

    close-factor = close-star-lowerᵢ {{safe}} occ source-wf

    factor-composition =
      shape-trans-left-idᵢ close-factor factor

    instantiated-left =
      subst
        (λ shape →
          ⌊ factor ⌋ ；
          ⌊ proj₁ (indexed-target-route-sound history route′) ⌋ ≋
          shape)
        (pair-lower-left-shape
          (inst-starᵢ (paired-lower-left lower))
          (inst-starᵢ (paired-lower-right lower)))
        recursive-left

    instantiated-right =
      subst
        (λ shape →
          ⌊ factor ⌋ ；
          ⌊ proj₂ (indexed-target-route-sound history route′) ⌋ ≋
          shape)
        (pair-lower-right-shape
          (inst-starᵢ (paired-lower-left lower))
          (inst-starᵢ (paired-lower-right lower)))
        recursive-right
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    lower@paired-star route@route-star =
  direct-terminal-factor-shapes history lower route
    (direct-terminal-factor free-★ lower route)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    lower@paired-base-base route@route-base =
  direct-terminal-factor-shapes history lower route
    (direct-terminal-factor free-base lower route)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    lower@paired-base-star route@route-base-star =
  direct-terminal-factor-shapes history lower route
    (direct-terminal-factor free-base lower route)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    lower@paired-star-base route@route-star-base =
  direct-terminal-factor-shapes history lower route
    (direct-terminal-factor free-base lower route)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    lower@paired-base-stars route@route-star =
  direct-terminal-factor-shapes history lower route
    (direct-terminal-factor free-base lower route)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    lower@(paired-var-var source-row Z<Δ X<Δ Y<Δ)
    route@(route-vars W∈) =
  direct-terminal-factor-shapes history lower route
    (direct-terminal-factor free-var lower route)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    lower@(paired-var-star source-row Z<Δ X<Δ)
    route@(route-var-star W∈) =
  direct-terminal-factor-shapes history lower route
    (direct-terminal-factor free-var lower route)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    lower@(paired-star-var source-row Z<Δ Y<Δ)
    route@(route-star-var W∈) =
  direct-terminal-factor-shapes history lower route
    (direct-terminal-factor free-var lower route)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    lower@(paired-var-stars source-row Z<Δ) route@route-star =
  direct-terminal-factor-shapes history lower route
    (direct-terminal-factor free-var lower route)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-arrow-arrow lower₁ lower₂) (route-arrow route₁ route₂)
    with
      route-factor-worker fuel _ sourceFuelFor history lower₁ route₁
       | route-factor-worker fuel _ sourceFuelFor history lower₂ route₂
       | route-factor-worker-shapes
           fuel _ sourceFuelFor history lower₁ route₁
       | route-factor-worker-shapes
           fuel _ sourceFuelFor history lower₂ route₂
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-arrow-arrow lower₁ lower₂) (route-arrow route₁ route₂)
    | F₁ , route₁′ , factor₁ | F₂ , route₂′ , factor₂
    | left₁ , right₁ | left₂ , right₂ =
  comp-↦-↦ left₁ left₂ , comp-↦-↦ right₁ right₂
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-arrow-star lower₁ lower₂)
    (route-arrow-star route₁ route₂)
    with
      route-factor-worker fuel _ sourceFuelFor history lower₁ route₁
       | route-factor-worker fuel _ sourceFuelFor history lower₂ route₂
       | route-factor-worker-shapes
           fuel _ sourceFuelFor history lower₁ route₁
       | route-factor-worker-shapes
           fuel _ sourceFuelFor history lower₂ route₂
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-arrow-star lower₁ lower₂)
    (route-arrow-star route₁ route₂)
    | F₁ , route₁′ , factor₁ | F₂ , route₂′ , factor₂
    | left₁ , right₁ | left₂ , right₂ =
  comp-↦-↦ left₁ left₂ , comp-↦-tag right₁ right₂
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-star-arrow lower₁ lower₂)
    (route-star-arrow route₁ route₂)
    with
      route-factor-worker fuel _ sourceFuelFor history lower₁ route₁
       | route-factor-worker fuel _ sourceFuelFor history lower₂ route₂
       | route-factor-worker-shapes
           fuel _ sourceFuelFor history lower₁ route₁
       | route-factor-worker-shapes
           fuel _ sourceFuelFor history lower₂ route₂
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-star-arrow lower₁ lower₂)
    (route-star-arrow route₁ route₂)
    | F₁ , route₁′ , factor₁ | F₂ , route₂′ , factor₂
    | left₁ , right₁ | left₂ , right₂ =
  comp-↦-tag left₁ left₂ , comp-↦-↦ right₁ right₂
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-both lower) route
    with paired-both-compatible-route history lower route
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-both lower) route
    | E , compatible
    with
      route-factor-worker fuel _ sourceFuelFor
        (indexed-factor-paired bothˢ active-both history)
        lower compatible
       | route-factor-worker-shapes fuel _ sourceFuelFor
           (indexed-factor-paired bothˢ active-both history)
           lower compatible
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-both lower) route
    | E , compatible
    | F , route′ , factor | recursive-left , recursive-right =
  comp-∀-∀ recursive-left , comp-∀-∀ recursive-right
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-left {{safe}} occ lower) route
    with paired-left-compatible-route
      history occ lower route in compatible-eq
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-left {{safe}} occ lower) route
    | E , compatible , target-safe , target-occ
    with
      route-factor-worker-shapes fuel _ sourceFuelFor
        (indexed-factor-paired leftˢ active-left history)
        lower compatible
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-left {{safe}} occ lower) route
    | E , compatible , target-safe , target-occ
    | recursive-left , recursive-right
    =
  comp-∀-∀ (proj₁ transported) ,
  comp-∀-ν (proj₂ transported)
  where
    extended =
      indexed-factor-paired leftˢ active-left history

    transported =
      subst
        (λ result →
          let compatible′ = proj₁ (proj₂ result)
              recursive-result =
                route-factor-worker fuel _ sourceFuelFor
                  extended lower compatible′
              route′ = proj₁ (proj₂ recursive-result)
              factor = proj₂ (proj₂ recursive-result)
              target-lower =
                indexed-target-route-sound extended route′
          in
          (⌊ factor ⌋ ； ⌊ proj₁ target-lower ⌋ ≋
            ⌊ paired-lower-left lower ⌋) ×
          (⌊ factor ⌋ ； ⌊ proj₂ target-lower ⌋ ≋
            ⌊ paired-lower-right lower ⌋))
        (sym compatible-eq)
        (recursive-left , recursive-right)
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-right {{safe}} occ lower) route
    with paired-right-compatible-route
      history occ lower route in compatible-eq
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-right {{safe}} occ lower) route
    | E , compatible , target-safe , target-occ
    with
      route-factor-worker-shapes fuel _ sourceFuelFor
        (indexed-factor-paired rightˢ active-right history)
        lower compatible
route-factor-worker-shapes (suc fuel) .(suc sourceBudget)
    (source-ok {budget = sourceBudget} enough) history
    (paired-right {{safe}} occ lower) route
    | E , compatible , target-safe , target-occ
    | recursive-left , recursive-right
    =
  comp-∀-ν (proj₁ transported) ,
  comp-∀-∀ (proj₂ transported)
  where
    extended =
      indexed-factor-paired rightˢ active-right history

    transported =
      subst
        (λ result →
          let compatible′ = proj₁ (proj₂ result)
              recursive-result =
                route-factor-worker fuel _ sourceFuelFor
                  extended lower compatible′
              route′ = proj₁ (proj₂ recursive-result)
              factor = proj₂ (proj₂ recursive-result)
              target-lower =
                indexed-target-route-sound extended route′
          in
          (⌊ factor ⌋ ； ⌊ proj₁ target-lower ⌋ ≋
            ⌊ paired-lower-left lower ⌋) ×
          (⌊ factor ⌋ ； ⌊ proj₂ target-lower ⌋ ≋
            ⌊ paired-lower-right lower ⌋))
        (sym compatible-eq)
        (recursive-left , recursive-right)
