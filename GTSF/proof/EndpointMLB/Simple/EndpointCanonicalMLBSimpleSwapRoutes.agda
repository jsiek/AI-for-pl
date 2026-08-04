module
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleSwapRoutes
  where

-- File Charter:
--   * Defines the route evidence retained by one adjacent left/right
--     exposure exchange.
--   * Keeps the exchanged assumption contexts and type-variable renaming
--     explicit in the route indices.
--   * Contains no endpoint selection, factorization, or DGG simulation.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)

open import Types
open import Imprecision using (ImpCtx; NonVar)
open import ForallPermutation using (swap01ᵗ)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using
  (∀ᵢᶜ; νᵢᶜ)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleRoutes using
  ( EnumRoute
  ; route-both
  ; route-left
  ; route-right
  ; route-arrow
  ; route-arrow-star
  ; route-star-arrow
  ; route-star
  ; route-base
  ; route-base-star
  ; route-star-base
  )


data Exposure : Set where
  bothᵉ : Exposure
  leftᵉ : Exposure
  rightᵉ : Exposure


lift-left : Exposure → ImpCtx → ImpCtx
lift-left bothᵉ Φ = ∀ᵢᶜ Φ
lift-left leftᵉ Φ = ∀ᵢᶜ Φ
lift-left rightᵉ Φ = νᵢᶜ Φ


lift-right : Exposure → ImpCtx → ImpCtx
lift-right bothᵉ Φ = ∀ᵢᶜ Φ
lift-right leftᵉ Φ = νᵢᶜ Φ
lift-right rightᵉ Φ = ∀ᵢᶜ Φ


apply-left : List Exposure → ImpCtx → ImpCtx
apply-left [] Φ = Φ
apply-left (mode ∷ modes) Φ = lift-left mode (apply-left modes Φ)


apply-right : List Exposure → ImpCtx → ImpCtx
apply-right [] Φ = Φ
apply-right (mode ∷ modes) Φ = lift-right mode (apply-right modes Φ)


apply-common-depth : List Exposure → ℕ → ℕ
apply-common-depth [] Δ = Δ
apply-common-depth (mode ∷ modes) Δ =
  suc (apply-common-depth modes Δ)


apply-left-depth : List Exposure → ℕ → ℕ
apply-left-depth [] Δ = Δ
apply-left-depth (bothᵉ ∷ modes) Δ =
  suc (apply-left-depth modes Δ)
apply-left-depth (leftᵉ ∷ modes) Δ =
  suc (apply-left-depth modes Δ)
apply-left-depth (rightᵉ ∷ modes) Δ =
  apply-left-depth modes Δ


apply-right-depth : List Exposure → ℕ → ℕ
apply-right-depth [] Δ = Δ
apply-right-depth (bothᵉ ∷ modes) Δ =
  suc (apply-right-depth modes Δ)
apply-right-depth (leftᵉ ∷ modes) Δ =
  apply-right-depth modes Δ
apply-right-depth (rightᵉ ∷ modes) Δ =
  suc (apply-right-depth modes Δ)


swap-under : List Exposure → Renameᵗ
swap-under [] = swap01ᵗ
swap-under (mode ∷ modes) = extᵗ (swap-under modes)


lr-left-context : List Exposure → ImpCtx → ImpCtx
lr-left-context modes Φ =
  apply-left modes (νᵢᶜ (∀ᵢᶜ Φ))


lr-right-context : List Exposure → ImpCtx → ImpCtx
lr-right-context modes Φ =
  apply-right modes (∀ᵢᶜ (νᵢᶜ Φ))


rl-left-context : List Exposure → ImpCtx → ImpCtx
rl-left-context modes Φ =
  apply-left modes (∀ᵢᶜ (νᵢᶜ Φ))


rl-right-context : List Exposure → ImpCtx → ImpCtx
rl-right-context modes Φ =
  apply-right modes (νᵢᶜ (∀ᵢᶜ Φ))


data SwapAlignedRoutes (modes : List Exposure) :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D} →
    EnumRoute fuel
      (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
      (apply-common-depth modes (suc (suc Δᶜ)))
      (apply-left-depth modes (suc Δᴸ))
      (apply-right-depth modes (suc Δᴿ))
      A B C →
    EnumRoute fuel
      (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
      (apply-common-depth modes (suc (suc Δᶜ)))
      (apply-left-depth modes (suc Δᴸ))
      (apply-right-depth modes (suc Δᴿ))
      A B D →
    Set where
  swap-aligned-both :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
      {route :
        EnumRoute fuel
          (lr-left-context (bothᵉ ∷ modes) Φᴸ)
          (lr-right-context (bothᵉ ∷ modes) Φᴿ)
          (apply-common-depth (bothᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (bothᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (bothᵉ ∷ modes) (suc Δᴿ)) A B C}
      {route′ :
        EnumRoute fuel
          (rl-left-context (bothᵉ ∷ modes) Φᴸ)
          (rl-right-context (bothᵉ ∷ modes) Φᴿ)
          (apply-common-depth (bothᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (bothᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (bothᵉ ∷ modes) (suc Δᴿ)) A B D} →
    SwapAlignedRoutes (bothᵉ ∷ modes) route route′ →
    SwapAlignedRoutes modes (route-both route) (route-both route′)

  swap-aligned-left :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D occC occD}
      {{safeC : NonVar C}}
      {{safeD : NonVar D}}
      {route :
        EnumRoute fuel
          (lr-left-context (leftᵉ ∷ modes) Φᴸ)
          (lr-right-context (leftᵉ ∷ modes) Φᴿ)
          (apply-common-depth (leftᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (leftᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (leftᵉ ∷ modes) (suc Δᴿ)) A B C}
      {route′ :
        EnumRoute fuel
          (rl-left-context (leftᵉ ∷ modes) Φᴸ)
          (rl-right-context (leftᵉ ∷ modes) Φᴿ)
          (apply-common-depth (leftᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (leftᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (leftᵉ ∷ modes) (suc Δᴿ)) A B D} →
    SwapAlignedRoutes (leftᵉ ∷ modes) route route′ →
    SwapAlignedRoutes modes
      (route-left {{safeC}} occC route)
      (route-left {{safeD}} occD route′)

  swap-aligned-right :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D occC occD}
      {{safeC : NonVar C}}
      {{safeD : NonVar D}}
      {route :
        EnumRoute fuel
          (lr-left-context (rightᵉ ∷ modes) Φᴸ)
          (lr-right-context (rightᵉ ∷ modes) Φᴿ)
          (apply-common-depth (rightᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (rightᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (rightᵉ ∷ modes) (suc Δᴿ)) A B C}
      {route′ :
        EnumRoute fuel
          (rl-left-context (rightᵉ ∷ modes) Φᴸ)
          (rl-right-context (rightᵉ ∷ modes) Φᴿ)
          (apply-common-depth (rightᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (rightᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (rightᵉ ∷ modes) (suc Δᴿ)) A B D} →
    SwapAlignedRoutes (rightᵉ ∷ modes) route route′ →
    SwapAlignedRoutes modes
      (route-right {{safeC}} occC route)
      (route-right {{safeD}} occD route′)

  swap-aligned-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
        A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂}
      {route₁ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₁ B₁ C₁}
      {route₂ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₂ B₂ C₂}
      {route₁′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₁ B₁ D₁}
      {route₂′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₂ B₂ D₂} →
    SwapAlignedRoutes modes route₁ route₁′ →
    SwapAlignedRoutes modes route₂ route₂′ →
    SwapAlignedRoutes modes
      (route-arrow route₁ route₂) (route-arrow route₁′ route₂′)

  swap-aligned-arrow-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ C₁ C₂ D₁ D₂}
      {route₁ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₁ ★ C₁}
      {route₂ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₂ ★ C₂}
      {route₁′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₁ ★ D₁}
      {route₂′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₂ ★ D₂} →
    SwapAlignedRoutes modes route₁ route₁′ →
    SwapAlignedRoutes modes route₂ route₂′ →
    SwapAlignedRoutes modes
      (route-arrow-star route₁ route₂)
      (route-arrow-star route₁′ route₂′)

  swap-aligned-star-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ B₁ B₂ C₁ C₂ D₁ D₂}
      {route₁ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ B₁ C₁}
      {route₂ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ B₂ C₂}
      {route₁′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ B₁ D₁}
      {route₂′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ B₂ D₂} →
    SwapAlignedRoutes modes route₁ route₁′ →
    SwapAlignedRoutes modes route₂ route₂′ →
    SwapAlignedRoutes modes
      (route-star-arrow route₁ route₂)
      (route-star-arrow route₁′ route₂′)

  swap-aligned-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ} →
    SwapAlignedRoutes modes
      (route-star
        {fuel}
        {lr-left-context modes Φᴸ} {lr-right-context modes Φᴿ}
        {apply-common-depth modes (suc (suc Δᶜ))}
        {apply-left-depth modes (suc Δᴸ)}
        {apply-right-depth modes (suc Δᴿ)})
      route-star

  swap-aligned-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    SwapAlignedRoutes modes
      (route-base
        {fuel}
        {lr-left-context modes Φᴸ} {lr-right-context modes Φᴿ}
        {apply-common-depth modes (suc (suc Δᶜ))}
        {apply-left-depth modes (suc Δᴸ)}
        {apply-right-depth modes (suc Δᴿ)} {ι})
      route-base

  swap-aligned-base-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    SwapAlignedRoutes modes
      (route-base-star
        {fuel}
        {lr-left-context modes Φᴸ} {lr-right-context modes Φᴿ}
        {apply-common-depth modes (suc (suc Δᶜ))}
        {apply-left-depth modes (suc Δᴸ)}
        {apply-right-depth modes (suc Δᴿ)} {ι})
      route-base-star

  swap-aligned-star-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    SwapAlignedRoutes modes
      (route-star-base
        {fuel}
        {lr-left-context modes Φᴸ} {lr-right-context modes Φᴿ}
        {apply-common-depth modes (suc (suc Δᶜ))}
        {apply-left-depth modes (suc Δᴸ)}
        {apply-right-depth modes (suc Δᴿ)} {ι})
      route-star-base

  swap-aligned-var :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X Y C D}
      {route :
        EnumRoute (suc fuel)
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) (＇ X) (＇ Y) C}
      {route′ :
        EnumRoute (suc fuel)
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) (＇ X) (＇ Y) D} →
    renameᵗ (swap-under modes) C ≡ D →
    SwapAlignedRoutes modes route route′

  swap-aligned-var-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X C D}
      {route :
        EnumRoute (suc fuel)
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) (＇ X) ★ C}
      {route′ :
        EnumRoute (suc fuel)
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) (＇ X) ★ D} →
    renameᵗ (swap-under modes) C ≡ D →
    SwapAlignedRoutes modes route route′

  swap-aligned-star-var :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ Y C D}
      {route :
        EnumRoute (suc fuel)
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ (＇ Y) C}
      {route′ :
        EnumRoute (suc fuel)
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ (＇ Y) D} →
    renameᵗ (swap-under modes) C ≡ D →
    SwapAlignedRoutes modes route route′
