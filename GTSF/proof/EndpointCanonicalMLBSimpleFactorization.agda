module proof.EndpointCanonicalMLBSimpleFactorization where

-- File Charter:
--   * Proves cross-context factorization through a target raw MLB route.
--   * Tracks asynchronous source and target `∀` exposure through paired span
--     worlds and shared endpoint origins.
--   * Exposes `rawEndpointMlbsAt-factor` for quotient selector monotonicity.

open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using
  (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using
  (m≤m+n; m≤n+m; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym; trans)

open import Types
open import ForallPermutation using (_≈∀_; ≈∀-swap)
open import Imprecision using
  (GenSafeSource; ImpCtx; idᵢ; _ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_; id★; idˣ; idι; _↦_; ∀ⁱ_; tag_; tag_⇛_; tagˣ
  ; ν; ⊑-src-wf
  )
open import proof.EndpointCanonicalMLBSimplePairedSpan using
  ( View; varᵛ; ★ᵛ; SpanCtx; span; _↦⟨_,_⟩∈_; row-var-var
  ; row-var-star; row-star-var; row-star-star; PairedLower; pair-lower
  ; paired-star; paired-base-base; paired-base-star; paired-star-base
  ; paired-base-stars; paired-arrow-arrow; paired-arrow-star
  ; paired-star-arrow; paired-arrow-stars
  ; paired-var-var; paired-var-star; paired-star-var; paired-var-stars
  ; paired-both; paired-left; paired-right; paired-neither
  ; paired-lower-left; paired-lower-right; SpanExposure; bothˢ; leftˢ
  ; rightˢ; neitherˢ; extend-span
  )
open proof.EndpointCanonicalMLBSimplePairedSpan.SpanCtx using
  (left-context; right-context)
open import proof.EndpointCanonicalMLBSimple using
  (fuelFor; hasStar; hasVar; rawEndpointMlbsAt; sizeTy; ∀ᵢᶜ; νᵢᶜ)
open import proof.EndpointCanonicalMLBSimpleRoutes using
  ( EnumRoute; route-both; route-left; route-right; route-star
  ; route-base; route-base-star; route-star-base; route-arrow
  ; route-arrow-star; route-star-arrow; route-vars; route-var-star
  ; route-star-var; raw-endpoint-route→membership
  ; raw-endpoint-membership→route
  )
open import proof.EndpointCanonicalMLBSimplePermutation using
  ( CommonTransport; transport-∀; transport-ν
  ; transport-ν∀-to-∀ν; transport-∀ν-to-ν∀
  ; no-νctx-zero-var; unν-var; unν-star
  ; occurs-swap01-left; occurs-swap01-right
  ; var-candidate-member-shape
  ; Exposure; bothᵉ; leftᵉ; rightᵉ; apply-left; apply-right
  ; apply-common-depth; apply-left-depth; apply-right-depth
  ; LeftStarPath; StarRightPath
  ; path-left-∀; path-right-∀; path-arrow₁; path-arrow₂
  ; path-arrow-star₁; path-arrow-star₂; path-var-star
  ; star-path-left-∀; star-path-right-∀
  ; star-path-arrow₁; star-path-arrow₂
  ; star-path-star-arrow₁; star-path-star-arrow₂
  ; star-path-star-var
  ; LeftOrigin; left-origin-both; left-origin-under-both
  ; left-origin-under-left; left-origin-under-right
  ; RightOrigin; right-origin-both; right-origin-under-both
  ; right-origin-under-left; right-origin-under-right
  ; bubble-left-exposure; bubble-right-exposure
  ; left-origin-left; right-origin-right
  ; left-used-path; right-used-path
  ; remove-right-path; remove-left-path
  ; remove-right-star-path; remove-left-star-path
  )
open proof.EndpointCanonicalMLBSimplePermutation.CommonTransport using
  (transport-var; transport-star)
open import proof.ForallPermutationProperties using (swap01-pres-<)
open import proof.EndpointCanonicalMLBSimpleSoundness using
  (andᵇ-true; hasStar-sound; hasVar-sound)
open import proof.EndpointCanonicalMLBSimpleCompleteness using
  ( close-star-lowerᵢ; inst-starᵢ
  ; EnoughFuel; SourceFuel; fuel-ok; source-ok; sourceFuelFor
  ; fuelFor-enough; fuel-zero-impossible
  ; fuel-∀∀-both; fuel-∀L; fuel-∀R
  ; fuel-⇒⇒-left; fuel-⇒⇒-right
  ; fuel-⇒★-left; fuel-⇒★-right
  ; fuel-★⇒-left; fuel-★⇒-right
  ; sizeTy-subst-starᵢ
  )
open import proof.MaximalLowerBoundsWf using
  (genSafeSource-forward-if-occursᵢ)
open import proof.EndpointCanonicalMLBSimpleFactor using
  ( occurs-zero-factor-∀
  ; source-left-exposure-path; source-right-exposure-path
  ; left-origin-target-track; right-origin-var-track
  ; left-origin-var-track; right-origin-target-track
  ; source-var-star-incompatible; source-star-var-incompatible
  )
open import proof.ImprecisionProperties using
  ( idᵢ-var-identity; idᵢ-no-star
  ; no-⇑ᵢ-zero-left; no-⇑ᵢ-zero-right; no-⇑ᵢ-zero-star
  ; no-⇑ᴸᵢ-zero-left; un⇑ᵢ-ˣ∈; un⇑ᵢ-★∈; un⇑ᴸᵢ-ˣ∈
  ; ⇑ᵢ-ˣ∈; ⇑ᵢ-★∈; ⇑ᴸᵢ-∈
  )
open import proof.MaximalLowerBoundsWf using
  (no-⇑ᴸᵢ-zero-star; un⇑ᴸᵢ-★∈; ⊑-trans-left-idᵢ)
open import proof.TypeProperties using
  (TyRenameWf-ext; occurs-zero-rename-ext)

record SpanRoot : Set where
  constructor span-root
  field
    root-context : SpanCtx
    root-common-depth : TyCtx
    root-left-depth : TyCtx
    root-right-depth : TyCtx

open SpanRoot

data SpanWorld : Set where
  world-root : SpanRoot → SpanWorld
  world-extend : SpanExposure → SpanWorld → SpanWorld

data ActiveExposure : SpanExposure → Set where
  active-both : ActiveExposure bothˢ
  active-left : ActiveExposure leftˢ
  active-right : ActiveExposure rightˢ

world-context : SpanWorld → SpanCtx
world-context (world-root root) = root-context root
world-context (world-extend mode world) =
  extend-span mode (world-context world)

world-common-depth : SpanWorld → TyCtx
world-common-depth (world-root root) = root-common-depth root
world-common-depth (world-extend mode world) =
  suc (world-common-depth world)

world-left-depth : SpanWorld → TyCtx
world-left-depth (world-root root) = root-left-depth root
world-left-depth (world-extend bothˢ world) =
  suc (world-left-depth world)
world-left-depth (world-extend leftˢ world) =
  suc (world-left-depth world)
world-left-depth (world-extend rightˢ world) =
  world-left-depth world
world-left-depth (world-extend neitherˢ world) =
  world-left-depth world

world-right-depth : SpanWorld → TyCtx
world-right-depth (world-root root) = root-right-depth root
world-right-depth (world-extend bothˢ world) =
  suc (world-right-depth world)
world-right-depth (world-extend leftˢ world) =
  world-right-depth world
world-right-depth (world-extend rightˢ world) =
  suc (world-right-depth world)
world-right-depth (world-extend neitherˢ world) =
  world-right-depth world

shift-left-view : SpanExposure → View → View
shift-left-view bothˢ (varᵛ X) = varᵛ (suc X)
shift-left-view bothˢ ★ᵛ = ★ᵛ
shift-left-view leftˢ (varᵛ X) = varᵛ (suc X)
shift-left-view leftˢ ★ᵛ = ★ᵛ
shift-left-view rightˢ view = view
shift-left-view neitherˢ view = view

shift-right-view : SpanExposure → View → View
shift-right-view bothˢ (varᵛ X) = varᵛ (suc X)
shift-right-view bothˢ ★ᵛ = ★ᵛ
shift-right-view leftˢ view = view
shift-right-view rightˢ (varᵛ X) = varᵛ (suc X)
shift-right-view rightˢ ★ᵛ = ★ᵛ
shift-right-view neitherˢ view = view

shift-left-view-injective :
  ∀ mode {L L′} →
  shift-left-view mode L ≡ shift-left-view mode L′ →
  L ≡ L′
shift-left-view-injective bothˢ {varᵛ X} {varᵛ .X} refl = refl
shift-left-view-injective bothˢ {varᵛ X} {★ᵛ} ()
shift-left-view-injective bothˢ {★ᵛ} {varᵛ X} ()
shift-left-view-injective bothˢ {★ᵛ} {★ᵛ} refl = refl
shift-left-view-injective leftˢ {varᵛ X} {varᵛ .X} refl = refl
shift-left-view-injective leftˢ {varᵛ X} {★ᵛ} ()
shift-left-view-injective leftˢ {★ᵛ} {varᵛ X} ()
shift-left-view-injective leftˢ {★ᵛ} {★ᵛ} refl = refl
shift-left-view-injective rightˢ eq = eq
shift-left-view-injective neitherˢ eq = eq

shift-right-view-injective :
  ∀ mode {R R′} →
  shift-right-view mode R ≡ shift-right-view mode R′ →
  R ≡ R′
shift-right-view-injective bothˢ {varᵛ X} {varᵛ .X} refl = refl
shift-right-view-injective bothˢ {varᵛ X} {★ᵛ} ()
shift-right-view-injective bothˢ {★ᵛ} {varᵛ X} ()
shift-right-view-injective bothˢ {★ᵛ} {★ᵛ} refl = refl
shift-right-view-injective leftˢ eq = eq
shift-right-view-injective rightˢ {varᵛ X} {varᵛ .X} refl = refl
shift-right-view-injective rightˢ {varᵛ X} {★ᵛ} ()
shift-right-view-injective rightˢ {★ᵛ} {varᵛ X} ()
shift-right-view-injective rightˢ {★ᵛ} {★ᵛ} refl = refl
shift-right-view-injective neitherˢ eq = eq

shift-left-star : ∀ mode → shift-left-view mode ★ᵛ ≡ ★ᵛ
shift-left-star bothˢ = refl
shift-left-star leftˢ = refl
shift-left-star rightˢ = refl
shift-left-star neitherˢ = refl

shift-right-star : ∀ mode → shift-right-view mode ★ᵛ ≡ ★ᵛ
shift-right-star bothˢ = refl
shift-right-star leftˢ = refl
shift-right-star rightˢ = refl
shift-right-star neitherˢ = refl

no-shift-left-both-zero :
  ∀ {L} → shift-left-view bothˢ L ≡ varᵛ zero → ⊥
no-shift-left-both-zero {varᵛ X} ()
no-shift-left-both-zero {★ᵛ} ()

no-shift-left-left-zero :
  ∀ {L} → shift-left-view leftˢ L ≡ varᵛ zero → ⊥
no-shift-left-left-zero {varᵛ X} ()
no-shift-left-left-zero {★ᵛ} ()

no-shift-right-right-zero :
  ∀ {R} → shift-right-view rightˢ R ≡ varᵛ zero → ⊥
no-shift-right-right-zero {varᵛ X} ()
no-shift-right-right-zero {★ᵛ} ()

data Observation (Φ : ImpCtx) : TyVar → View → Set where
  observes-var :
    ∀ {Z X} →
    (Z ˣ⊑ˣ X) ∈ Φ →
    Observation Φ Z (varᵛ X)

  observes-star :
    ∀ {Z} →
    (Z ˣ⊑★) ∈ Φ →
    Observation Φ Z ★ᵛ

row-left-observation :
  ∀ {Σ Z L R} →
  Z ↦⟨ L , R ⟩∈ Σ →
  Observation (left-context Σ) Z L
row-left-observation (row-var-var Z⊑X Z⊑Y) = observes-var Z⊑X
row-left-observation (row-var-star Z⊑X Z⊑★) = observes-var Z⊑X
row-left-observation (row-star-var Z⊑★ Z⊑Y) = observes-star Z⊑★
row-left-observation (row-star-star Z⊑★ Z⊑★′) = observes-star Z⊑★

row-right-observation :
  ∀ {Σ Z L R} →
  Z ↦⟨ L , R ⟩∈ Σ →
  Observation (right-context Σ) Z R
row-right-observation (row-var-var Z⊑X Z⊑Y) = observes-var Z⊑Y
row-right-observation (row-var-star Z⊑X Z⊑★) = observes-star Z⊑★
row-right-observation (row-star-var Z⊑★ Z⊑Y) = observes-var Z⊑Y
row-right-observation (row-star-star Z⊑★ Z⊑★′) =
  observes-star Z⊑★′

observations-row :
  ∀ {Σ Z L R} →
  Observation (left-context Σ) Z L →
  Observation (right-context Σ) Z R →
  Z ↦⟨ L , R ⟩∈ Σ
observations-row (observes-var Z⊑X) (observes-var Z⊑Y) =
  row-var-var Z⊑X Z⊑Y
observations-row (observes-var Z⊑X) (observes-star Z⊑★) =
  row-var-star Z⊑X Z⊑★
observations-row (observes-star Z⊑★) (observes-var Z⊑Y) =
  row-star-var Z⊑★ Z⊑Y
observations-row (observes-star Z⊑★) (observes-star Z⊑★′) =
  row-star-star Z⊑★ Z⊑★′

shift-all-view : View → View
shift-all-view (varᵛ X) = varᵛ (suc X)
shift-all-view ★ᵛ = ★ᵛ

same-view : View → View
same-view view = view

left-both-shift : ∀ view →
  shift-left-view bothˢ view ≡ shift-all-view view
left-both-shift (varᵛ X) = refl
left-both-shift ★ᵛ = refl

right-both-shift : ∀ view →
  shift-right-view bothˢ view ≡ shift-all-view view
right-both-shift (varᵛ X) = refl
right-both-shift ★ᵛ = refl

left-left-shift : ∀ view →
  shift-left-view leftˢ view ≡ shift-all-view view
left-left-shift (varᵛ X) = refl
left-left-shift ★ᵛ = refl

right-left-shift : ∀ view →
  shift-right-view leftˢ view ≡ same-view view
right-left-shift view = refl

left-right-shift : ∀ view →
  shift-left-view rightˢ view ≡ same-view view
left-right-shift view = refl

right-right-shift : ∀ view →
  shift-right-view rightˢ view ≡ shift-all-view view
right-right-shift (varᵛ X) = refl
right-right-shift ★ᵛ = refl

left-neither-shift : ∀ view →
  shift-left-view neitherˢ view ≡ same-view view
left-neither-shift view = refl

right-neither-shift : ∀ view →
  shift-right-view neitherˢ view ≡ same-view view
right-neither-shift view = refl

data ShiftedObservation
    (Φ : ImpCtx) (head : View) (shift : View → View) :
    TyVar → View → Set where
  shifted-head : ShiftedObservation Φ head shift zero head

  shifted-tail :
    ∀ {Z V V′} →
    Observation Φ Z V →
    shift V ≡ V′ →
    ShiftedObservation Φ head shift (suc Z) V′

unshift-∀-observation :
  ∀ {Φ Z V} →
  Observation (∀ᵢᶜ Φ) Z V →
  ShiftedObservation Φ (varᵛ zero) shift-all-view Z V
unshift-∀-observation {Z = zero}
    (observes-var (here refl)) = shifted-head
unshift-∀-observation {Z = zero}
    (observes-var (there Z⊑X)) =
  ⊥-elim (no-⇑ᵢ-zero-left Z⊑X)
unshift-∀-observation {Z = zero}
    (observes-star (there Z⊑★)) =
  ⊥-elim (no-⇑ᵢ-zero-star Z⊑★)
unshift-∀-observation {Z = suc z} {V = varᵛ zero}
    (observes-var (there Z⊑X)) =
  ⊥-elim (no-⇑ᵢ-zero-right Z⊑X)
unshift-∀-observation {Z = suc z} {V = varᵛ (suc x)}
    (observes-var (there Z⊑X)) =
  shifted-tail (observes-var (un⇑ᵢ-ˣ∈ Z⊑X)) refl
unshift-∀-observation {Z = suc z}
    (observes-star (there Z⊑★)) =
  shifted-tail (observes-star (un⇑ᵢ-★∈ Z⊑★)) refl

unshift-ν-observation :
  ∀ {Φ Z V} →
  Observation (νᵢᶜ Φ) Z V →
  ShiftedObservation Φ ★ᵛ same-view Z V
unshift-ν-observation {Z = zero}
    (observes-var (there Z⊑X)) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left Z⊑X)
unshift-ν-observation {Z = zero}
    (observes-star (here refl)) = shifted-head
unshift-ν-observation {Z = zero}
    (observes-star (there Z⊑★)) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star Z⊑★)
unshift-ν-observation {Z = suc z}
    (observes-var (there Z⊑X)) =
  shifted-tail (observes-var (un⇑ᴸᵢ-ˣ∈ Z⊑X)) refl
unshift-ν-observation {Z = suc z}
    (observes-star (there Z⊑★)) =
  shifted-tail (observes-star (un⇑ᴸᵢ-★∈ Z⊑★)) refl

data WorldRow : SpanWorld → TyVar → View → View → Set where
  world-root-row :
    ∀ {root Z L R} →
    Z ↦⟨ L , R ⟩∈ root-context root →
    WorldRow (world-root root) Z L R

  world-head-both :
    ∀ {world} →
    WorldRow (world-extend bothˢ world)
      zero (varᵛ zero) (varᵛ zero)

  world-head-left :
    ∀ {world} →
    WorldRow (world-extend leftˢ world)
      zero (varᵛ zero) ★ᵛ

  world-head-right :
    ∀ {world} →
    WorldRow (world-extend rightˢ world)
      zero ★ᵛ (varᵛ zero)

  world-head-neither :
    ∀ {world} →
    WorldRow (world-extend neitherˢ world) zero ★ᵛ ★ᵛ

  world-tail :
    ∀ {world mode Z L R L′ R′} →
    WorldRow world Z L R →
    shift-left-view mode L ≡ L′ →
    shift-right-view mode R ≡ R′ →
    WorldRow (world-extend mode world) (suc Z) L′ R′

generated-row-complete :
  ∀ {world Z L R} →
  Z ↦⟨ L , R ⟩∈ world-context world →
  WorldRow world Z L R
generated-row-complete {world = world-root root} row =
  world-root-row row
generated-row-complete {world = world-extend bothˢ world} row
    with unshift-∀-observation (row-left-observation row)
       | unshift-∀-observation (row-right-observation row)
generated-row-complete {world = world-extend bothˢ world} row
    | shifted-head | shifted-head =
  world-head-both
generated-row-complete {world = world-extend bothˢ world} row
    | shifted-tail {V = L} left left-eq
    | shifted-tail {V = R} right right-eq =
  world-tail
    (generated-row-complete (observations-row left right))
    (trans (left-both-shift L) left-eq)
    (trans (right-both-shift R) right-eq)
generated-row-complete {world = world-extend leftˢ world} row
    with unshift-∀-observation (row-left-observation row)
       | unshift-ν-observation (row-right-observation row)
generated-row-complete {world = world-extend leftˢ world} row
    | shifted-head | shifted-head =
  world-head-left
generated-row-complete {world = world-extend leftˢ world} row
    | shifted-tail {V = L} left left-eq
    | shifted-tail {V = R} right right-eq =
  world-tail
    (generated-row-complete (observations-row left right))
    (trans (left-left-shift L) left-eq)
    (trans (right-left-shift R) right-eq)
generated-row-complete {world = world-extend rightˢ world} row
    with unshift-ν-observation (row-left-observation row)
       | unshift-∀-observation (row-right-observation row)
generated-row-complete {world = world-extend rightˢ world} row
    | shifted-head | shifted-head =
  world-head-right
generated-row-complete {world = world-extend rightˢ world} row
    | shifted-tail {V = L} left left-eq
    | shifted-tail {V = R} right right-eq =
  world-tail
    (generated-row-complete (observations-row left right))
    (trans (left-right-shift L) left-eq)
    (trans (right-right-shift R) right-eq)
generated-row-complete {world = world-extend neitherˢ world} row
    with unshift-ν-observation (row-left-observation row)
       | unshift-ν-observation (row-right-observation row)
generated-row-complete {world = world-extend neitherˢ world} row
    | shifted-head | shifted-head =
  world-head-neither
generated-row-complete {world = world-extend neitherˢ world} row
    | shifted-tail {V = L} left left-eq
    | shifted-tail {V = R} right right-eq =
  world-tail
    (generated-row-complete (observations-row left right))
    (trans (left-neither-shift L) left-eq)
    (trans (right-neither-shift R) right-eq)

route-vars-world-row :
  ∀ {world fuel X Y W} →
  EnumRoute fuel
    (left-context (world-context world))
    (right-context (world-context world))
    (world-common-depth world)
    (world-left-depth world)
    (world-right-depth world)
    (＇ X) (＇ Y) (＇ W) →
  (W < world-common-depth world) ×
  WorldRow world W (varᵛ X) (varᵛ Y)
route-vars-world-row
    {world = world} {X = X} {Y = Y} {W = W} (route-vars W∈)
    with var-candidate-member-shape
      {limit = world-common-depth world}
      {Φᴸ = left-context (world-context world)}
      {Φᴿ = right-context (world-context world)}
      {A = ＇ X} {B = ＇ Y} {C = ＇ W} W∈
route-vars-world-row
    {world = world} {X = X} {Y = Y} (route-vars W∈)
    | V , refl , V<Δ , ok
    with andᵇ-true
      {a = hasVar V X (left-context (world-context world))}
      {b = hasVar V Y (right-context (world-context world))} ok
route-vars-world-row
    {world = world} {X = X} {Y = Y} (route-vars W∈)
    | V , refl , V<Δ , ok | V⊑X? , V⊑Y? =
  V<Δ ,
  generated-row-complete
    (row-var-var (hasVar-sound V⊑X?) (hasVar-sound V⊑Y?))

route-var-star-world-row :
  ∀ {world fuel X W} →
  EnumRoute fuel
    (left-context (world-context world))
    (right-context (world-context world))
    (world-common-depth world)
    (world-left-depth world)
    (world-right-depth world)
    (＇ X) ★ (＇ W) →
  (W < world-common-depth world) ×
  WorldRow world W (varᵛ X) ★ᵛ
route-var-star-world-row
    {world = world} {X = X} {W = W} (route-var-star W∈)
    with var-candidate-member-shape
      {limit = world-common-depth world}
      {Φᴸ = left-context (world-context world)}
      {Φᴿ = right-context (world-context world)}
      {A = ＇ X} {B = ★} {C = ＇ W} W∈
route-var-star-world-row
    {world = world} {X = X} (route-var-star W∈)
    | V , refl , V<Δ , ok
    with andᵇ-true
      {a = hasVar V X (left-context (world-context world))}
      {b = hasStar V (right-context (world-context world))} ok
route-var-star-world-row
    {world = world} {X = X} (route-var-star W∈)
    | V , refl , V<Δ , ok | V⊑X? , V⊑★? =
  V<Δ ,
  generated-row-complete
    (row-var-star (hasVar-sound V⊑X?) (hasStar-sound V⊑★?))

route-star-var-world-row :
  ∀ {world fuel Y W} →
  EnumRoute fuel
    (left-context (world-context world))
    (right-context (world-context world))
    (world-common-depth world)
    (world-left-depth world)
    (world-right-depth world)
    ★ (＇ Y) (＇ W) →
  (W < world-common-depth world) ×
  WorldRow world W ★ᵛ (varᵛ Y)
route-star-var-world-row
    {world = world} {Y = Y} {W = W} (route-star-var W∈)
    with var-candidate-member-shape
      {limit = world-common-depth world}
      {Φᴸ = left-context (world-context world)}
      {Φᴿ = right-context (world-context world)}
      {A = ★} {B = ＇ Y} {C = ＇ W} W∈
route-star-var-world-row
    {world = world} {Y = Y} (route-star-var W∈)
    | V , refl , V<Δ , ok
    with andᵇ-true
      {a = hasStar V (left-context (world-context world))}
      {b = hasVar V Y (right-context (world-context world))} ok
route-star-var-world-row
    {world = world} {Y = Y} (route-star-var W∈)
    | V , refl , V<Δ , ok | V⊑★? , V⊑Y? =
  V<Δ ,
  generated-row-complete
    (row-star-var (hasStar-sound V⊑★?) (hasVar-sound V⊑Y?))

data PullsBack
    (source-world target-world : SpanWorld) : TyVar → TyVar → Set where
  pull-row :
    ∀ {Z W L R} →
    WorldRow source-world Z L R →
    WorldRow target-world W L R →
    PullsBack source-world target-world Z W

align-world-rows :
  ∀ {source target Z W L L′ R R′} →
  WorldRow source Z L R →
  WorldRow target W L′ R′ →
  L ≡ L′ →
  R ≡ R′ →
  PullsBack source target Z W
align-world-rows source-row target-row refl refl =
  pull-row source-row target-row

align-world-row-star :
  ∀ {world Z L R} →
  WorldRow world Z L R →
  L ≡ ★ᵛ →
  R ≡ ★ᵛ →
  WorldRow world Z ★ᵛ ★ᵛ
align-world-row-star row refl refl = row

root-pullback-var :
  ∀ {Φ Δᴸ Δᴿ Z W} →
  PullsBack
    (world-root (span-root (span Φ Φ) Δᴸ Δᴿ Δᴿ))
    (world-root
      (span-root (span (idᵢ Δᴿ) (idᵢ Δᴿ)) Δᴿ Δᴿ Δᴿ))
    Z W →
  (Z ˣ⊑ˣ W) ∈ Φ
root-pullback-var
    (pull-row
      (world-root-row (row-var-var Z⊑X Z⊑Y))
      (world-root-row (row-var-var W⊑X W⊑Y)))
    rewrite idᵢ-var-identity W⊑X =
  Z⊑X
root-pullback-var
    (pull-row
      (world-root-row (row-var-star Z⊑X Z⊑★))
      (world-root-row (row-var-star W⊑X W⊑★))) =
  ⊥-elim (idᵢ-no-star W⊑★)
root-pullback-var
    (pull-row
      (world-root-row (row-star-var Z⊑★ Z⊑Y))
      (world-root-row (row-star-var W⊑★ W⊑Y))) =
  ⊥-elim (idᵢ-no-star W⊑★)
root-pullback-var
    (pull-row
      (world-root-row (row-star-star Z⊑★ Z⊑★′))
      (world-root-row (row-star-star W⊑★ W⊑★′))) =
  ⊥-elim (idᵢ-no-star W⊑★)

root-source-star :
  ∀ {Φ Δᴸ Δᴿ Z} →
  WorldRow
    (world-root (span-root (span Φ Φ) Δᴸ Δᴿ Δᴿ))
    Z ★ᵛ ★ᵛ →
  (Z ˣ⊑★) ∈ Φ
root-source-star
    (world-root-row (row-star-star Z⊑★ Z⊑★′)) =
  Z⊑★

data IndexedFactorWorlds (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
    SpanWorld → SpanWorld → ImpCtx → TyCtx → TyCtx → Set where
  indexed-factor-root :
    IndexedFactorWorlds Φ Δᴸ Δᴿ
      (world-root (span-root (span Φ Φ) Δᴸ Δᴿ Δᴿ))
      (world-root
        (span-root (span (idᵢ Δᴿ) (idᵢ Δᴿ)) Δᴿ Δᴿ Δᴿ))
      Φ Δᴸ Δᴿ

  indexed-factor-paired :
    ∀ {source target Ψ Δˢ Δᵗ} mode →
    ActiveExposure mode →
    IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
    IndexedFactorWorlds Φ Δᴸ Δᴿ
      (world-extend mode source)
      (world-extend mode target)
      (∀ᵢᶜ Ψ) (suc Δˢ) (suc Δᵗ)

transport-enum-route :
  ∀ {fuel Φᴸ Φᴸ′ Φᴿ Φᴿ′ Δᶜ Δᶜ′
      Δᴸ Δᴸ′ Δᴿ Δᴿ′
      A A′ B B′ C C′} →
  Φᴸ ≡ Φᴸ′ →
  Φᴿ ≡ Φᴿ′ →
  Δᶜ ≡ Δᶜ′ →
  Δᴸ ≡ Δᴸ′ →
  Δᴿ ≡ Δᴿ′ →
  A ≡ A′ →
  B ≡ B′ →
  C ≡ C′ →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C →
  EnumRoute fuel Φᴸ′ Φᴿ′ Δᶜ′ Δᴸ′ Δᴿ′ A′ B′ C′
transport-enum-route refl refl refl refl refl refl refl refl route =
  route

transport-paired-lower :
  ∀ {Σ Σ′ Δᶜ Δᶜ′ Δᴸ Δᴸ′ Δᴿ Δᴿ′ C A B} →
  Σ ≡ Σ′ →
  Δᶜ ≡ Δᶜ′ →
  Δᴸ ≡ Δᴸ′ →
  Δᴿ ≡ Δᴿ′ →
  PairedLower Σ Δᶜ C A B Δᴸ Δᴿ →
  PairedLower Σ′ Δᶜ′ C A B Δᴸ′ Δᴿ′
transport-paired-lower refl refl refl refl lower = lower

record SourceSchedule (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (source : SpanWorld) : Set where
  constructor source-schedule
  field
    source-modes : List Exposure
    source-context-eq :
      world-context source ≡
      span (apply-left source-modes Φ) (apply-right source-modes Φ)
    source-common-depth-eq :
      world-common-depth source ≡
      apply-common-depth source-modes Δᴸ
    source-left-depth-eq :
      world-left-depth source ≡
      apply-left-depth source-modes Δᴿ
    source-right-depth-eq :
      world-right-depth source ≡
      apply-right-depth source-modes Δᴿ

open SourceSchedule

extend-source-schedule :
  ∀ {Φ Δᴸ Δᴿ source mode} →
  ActiveExposure mode →
  SourceSchedule Φ Δᴸ Δᴿ source →
  SourceSchedule Φ Δᴸ Δᴿ (world-extend mode source)
extend-source-schedule active-both
    (source-schedule modes context-eq common-eq left-eq right-eq) =
  source-schedule (bothᵉ ∷ modes)
    (cong (extend-span bothˢ) context-eq)
    (cong suc common-eq) (cong suc left-eq) (cong suc right-eq)
extend-source-schedule active-left
    (source-schedule modes context-eq common-eq left-eq right-eq) =
  source-schedule (leftᵉ ∷ modes)
    (cong (extend-span leftˢ) context-eq)
    (cong suc common-eq) (cong suc left-eq) right-eq
extend-source-schedule active-right
    (source-schedule modes context-eq common-eq left-eq right-eq) =
  source-schedule (rightᵉ ∷ modes)
    (cong (extend-span rightˢ) context-eq)
    (cong suc common-eq) left-eq (cong suc right-eq)

record TargetSchedule (Δ : TyCtx) (target : SpanWorld) : Set where
  constructor target-schedule
  field
    target-modes : List Exposure
    target-left-context-eq :
      left-context (world-context target) ≡
      apply-left target-modes (idᵢ Δ)
    target-right-context-eq :
      right-context (world-context target) ≡
      apply-right target-modes (idᵢ Δ)
    target-common-depth-eq :
      world-common-depth target ≡
      apply-common-depth target-modes Δ
    target-left-depth-eq :
      world-left-depth target ≡
      apply-left-depth target-modes Δ
    target-right-depth-eq :
      world-right-depth target ≡
      apply-right-depth target-modes Δ

open TargetSchedule

extend-target-schedule :
  ∀ {Δ target mode} →
  ActiveExposure mode →
  TargetSchedule Δ target →
  TargetSchedule Δ (world-extend mode target)
extend-target-schedule active-both
    (target-schedule modes left-eq right-eq common-eq left-depth-eq
      right-depth-eq) =
  target-schedule (bothᵉ ∷ modes)
    (cong ∀ᵢᶜ left-eq) (cong ∀ᵢᶜ right-eq)
    (cong suc common-eq) (cong suc left-depth-eq)
    (cong suc right-depth-eq)
extend-target-schedule active-left
    (target-schedule modes left-eq right-eq common-eq left-depth-eq
      right-depth-eq) =
  target-schedule (leftᵉ ∷ modes)
    (cong ∀ᵢᶜ left-eq) (cong νᵢᶜ right-eq)
    (cong suc common-eq) (cong suc left-depth-eq) right-depth-eq
extend-target-schedule active-right
    (target-schedule modes left-eq right-eq common-eq left-depth-eq
      right-depth-eq) =
  target-schedule (rightᵉ ∷ modes)
    (cong νᵢᶜ left-eq) (cong ∀ᵢᶜ right-eq)
    (cong suc common-eq) left-depth-eq (cong suc right-depth-eq)

indexed-target-schedule :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  TargetSchedule Δᴿ target
indexed-target-schedule indexed-factor-root =
  target-schedule [] refl refl refl refl refl
indexed-target-schedule
    (indexed-factor-paired mode active history) =
  extend-target-schedule active (indexed-target-schedule history)

indexed-source-schedule :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  SourceSchedule Φ Δᴸ Δᴿ source
indexed-source-schedule indexed-factor-root =
  source-schedule [] refl refl refl refl
indexed-source-schedule
    (indexed-factor-paired mode active history) =
  extend-source-schedule active (indexed-source-schedule history)

world-bubble-left-exposure :
  ∀ {Δ target fuel A B C} →
  TargetSchedule Δ target →
  LeftStarPath A B zero →
  EnumRoute (suc fuel)
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target) (world-right-depth target)
    (`∀ A) B C →
  ∃[ E ]
    (EnumRoute fuel
      (left-context (world-context (world-extend leftˢ target)))
      (right-context (world-context (world-extend leftˢ target)))
      (world-common-depth (world-extend leftˢ target))
      (world-left-depth (world-extend leftˢ target))
      (world-right-depth (world-extend leftˢ target)) A B E ×
     GenSafeSource E × occurs zero E ≡ true)
world-bubble-left-exposure {Δ = Δ}
    (target-schedule modes left-eq right-eq common-eq left-depth-eq
      right-depth-eq)
    path route
    with bubble-left-exposure {modes = modes} {Δ = Δ} path
      (transport-enum-route left-eq right-eq common-eq left-depth-eq
        right-depth-eq refl refl refl route)
world-bubble-left-exposure
    (target-schedule modes left-eq right-eq common-eq left-depth-eq
      right-depth-eq)
    path route
    | E , body , safe , occ =
  E ,
  transport-enum-route
    (sym (cong ∀ᵢᶜ left-eq)) (sym (cong νᵢᶜ right-eq))
    (sym (cong suc common-eq)) (sym (cong suc left-depth-eq))
    (sym right-depth-eq) refl refl refl body ,
  safe , occ

world-bubble-right-exposure :
  ∀ {Δ target fuel A B C} →
  TargetSchedule Δ target →
  StarRightPath A B zero →
  EnumRoute (suc fuel)
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target) (world-right-depth target)
    A (`∀ B) C →
  ∃[ E ]
    (EnumRoute fuel
      (left-context (world-context (world-extend rightˢ target)))
      (right-context (world-context (world-extend rightˢ target)))
      (world-common-depth (world-extend rightˢ target))
      (world-left-depth (world-extend rightˢ target))
      (world-right-depth (world-extend rightˢ target)) A B E ×
     GenSafeSource E × occurs zero E ≡ true)
world-bubble-right-exposure {Δ = Δ}
    (target-schedule modes left-eq right-eq common-eq left-depth-eq
      right-depth-eq)
    path route
    with bubble-right-exposure {modes = modes} {Δ = Δ} path route′
  where
    route′ =
      transport-enum-route left-eq right-eq common-eq left-depth-eq
        right-depth-eq refl refl refl route
world-bubble-right-exposure
    (target-schedule modes left-eq right-eq common-eq left-depth-eq
      right-depth-eq)
    path route
    | E , body , safe , occ , aligned =
  E ,
  transport-enum-route
    (sym (cong νᵢᶜ left-eq)) (sym (cong ∀ᵢᶜ right-eq))
    (sym (cong suc common-eq)) (sym left-depth-eq)
    (sym (cong suc right-depth-eq)) refl refl refl body ,
  safe , occ

world-left-route-path :
  ∀ {Δ target fuel A B C} →
  TargetSchedule Δ target →
  occurs zero C ≡ true →
  EnumRoute fuel
    (left-context (world-context (world-extend leftˢ target)))
    (right-context (world-context (world-extend leftˢ target)))
    (world-common-depth (world-extend leftˢ target))
    (world-left-depth (world-extend leftˢ target))
    (world-right-depth (world-extend leftˢ target))
    A (`∀ B) C →
  LeftStarPath A B zero
world-left-route-path {Δ = Δ}
    (target-schedule modes left-eq right-eq common-eq left-depth-eq
      right-depth-eq)
    occ route =
  remove-right-path
    (left-used-path
      {modes = leftᵉ ∷ modes} {Δ = Δ}
      left-origin-left route′ occ)
  where
    route′ =
      transport-enum-route
        (cong ∀ᵢᶜ left-eq) (cong νᵢᶜ right-eq)
        (cong suc common-eq) (cong suc left-depth-eq)
        right-depth-eq refl refl refl route

world-right-route-path :
  ∀ {Δ target fuel A B C} →
  TargetSchedule Δ target →
  occurs zero C ≡ true →
  EnumRoute fuel
    (left-context (world-context (world-extend rightˢ target)))
    (right-context (world-context (world-extend rightˢ target)))
    (world-common-depth (world-extend rightˢ target))
    (world-left-depth (world-extend rightˢ target))
    (world-right-depth (world-extend rightˢ target))
    (`∀ A) B C →
  StarRightPath A B zero
world-right-route-path {Δ = Δ}
    (target-schedule modes left-eq right-eq common-eq left-depth-eq
      right-depth-eq)
    occ route =
  remove-left-star-path
    (right-used-path
      {modes = rightᵉ ∷ modes} {Δ = Δ}
      right-origin-right route′ occ)
  where
    route′ =
      transport-enum-route
        (cong νᵢᶜ left-eq) (cong ∀ᵢᶜ right-eq)
        (cong suc common-eq) left-depth-eq
        (cong suc right-depth-eq) refl refl refl route

paired-left-compatible-route :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ fuel C A B D} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  occurs zero C ≡ true →
  PairedLower
    (world-context (world-extend leftˢ source))
    (world-common-depth (world-extend leftˢ source)) C A B
    (world-left-depth (world-extend leftˢ source))
    (world-right-depth (world-extend leftˢ source)) →
  EnumRoute (suc fuel)
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target) (world-right-depth target)
    (`∀ A) B D →
  ∃[ E ]
    (EnumRoute fuel
      (left-context (world-context (world-extend leftˢ target)))
      (right-context (world-context (world-extend leftˢ target)))
      (world-common-depth (world-extend leftˢ target))
      (world-left-depth (world-extend leftˢ target))
      (world-right-depth (world-extend leftˢ target)) A B E ×
     GenSafeSource E × occurs zero E ≡ true)
paired-left-compatible-route history occ source route =
  world-bubble-left-exposure
    (indexed-target-schedule history)
    (source-left-exposure-path
      (paired-lower-left source) (paired-lower-right source) occ)
    route

paired-right-compatible-route :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ fuel C A B D} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  occurs zero C ≡ true →
  PairedLower
    (world-context (world-extend rightˢ source))
    (world-common-depth (world-extend rightˢ source)) C A B
    (world-left-depth (world-extend rightˢ source))
    (world-right-depth (world-extend rightˢ source)) →
  EnumRoute (suc fuel)
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target) (world-right-depth target)
    A (`∀ B) D →
  ∃[ E ]
    (EnumRoute fuel
      (left-context (world-context (world-extend rightˢ target)))
      (right-context (world-context (world-extend rightˢ target)))
      (world-common-depth (world-extend rightˢ target))
      (world-left-depth (world-extend rightˢ target))
      (world-right-depth (world-extend rightˢ target)) A B E ×
     GenSafeSource E × occurs zero E ≡ true)
paired-right-compatible-route history occ source route =
  world-bubble-right-exposure
    (indexed-target-schedule history)
    (source-right-exposure-path
      (paired-lower-left source) (paired-lower-right source) occ)
    route

indexed-source-depth :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  world-common-depth source ≡ Δˢ
indexed-source-depth indexed-factor-root = refl
indexed-source-depth
    (indexed-factor-paired mode active history) =
  cong suc (indexed-source-depth history)

indexed-target-depth :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  world-common-depth target ≡ Δᵗ
indexed-target-depth indexed-factor-root = refl
indexed-target-depth
    (indexed-factor-paired mode active history) =
  cong suc (indexed-target-depth history)

indexed-pullback-var :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ Z W} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  PullsBack source target Z W →
  (Z ˣ⊑ˣ W) ∈ Ψ
indexed-pullback-var indexed-factor-root pull =
  root-pullback-var pull
indexed-pullback-var
    (indexed-factor-paired bothˢ active-both history)
    (pull-row world-head-both world-head-both) =
  here refl
indexed-pullback-var
    (indexed-factor-paired bothˢ active-both history)
    (pull-row world-head-both
      (world-tail {L = L} row left-eq right-eq)) =
  ⊥-elim (no-shift-left-both-zero {L = L} left-eq)
indexed-pullback-var
    (indexed-factor-paired bothˢ active-both history)
    (pull-row (world-tail {L = L} row left-eq right-eq)
      world-head-both) =
  ⊥-elim (no-shift-left-both-zero {L = L} left-eq)
indexed-pullback-var
    (indexed-factor-paired bothˢ active-both history)
    (pull-row
      (world-tail source-row source-left source-right)
      (world-tail target-row target-left target-right)) =
  there (⇑ᵢ-ˣ∈ (indexed-pullback-var history
    (align-world-rows source-row target-row
      (shift-left-view-injective bothˢ
        (trans source-left (sym target-left)))
      (shift-right-view-injective bothˢ
        (trans source-right (sym target-right))))))
indexed-pullback-var
    (indexed-factor-paired leftˢ active-left history)
    (pull-row world-head-left world-head-left) =
  here refl
indexed-pullback-var
    (indexed-factor-paired leftˢ active-left history)
    (pull-row world-head-left
      (world-tail {L = L} row left-eq right-eq)) =
  ⊥-elim (no-shift-left-left-zero {L = L} left-eq)
indexed-pullback-var
    (indexed-factor-paired leftˢ active-left history)
    (pull-row (world-tail {L = L} row left-eq right-eq)
      world-head-left) =
  ⊥-elim (no-shift-left-left-zero {L = L} left-eq)
indexed-pullback-var
    (indexed-factor-paired leftˢ active-left history)
    (pull-row
      (world-tail source-row source-left source-right)
      (world-tail target-row target-left target-right)) =
  there (⇑ᵢ-ˣ∈ (indexed-pullback-var history
    (align-world-rows source-row target-row
      (shift-left-view-injective leftˢ
        (trans source-left (sym target-left)))
      (shift-right-view-injective leftˢ
        (trans source-right (sym target-right))))))
indexed-pullback-var
    (indexed-factor-paired rightˢ active-right history)
    (pull-row world-head-right world-head-right) =
  here refl
indexed-pullback-var
    (indexed-factor-paired rightˢ active-right history)
    (pull-row world-head-right
      (world-tail {R = R} row left-eq right-eq)) =
  ⊥-elim (no-shift-right-right-zero {R = R} right-eq)
indexed-pullback-var
    (indexed-factor-paired rightˢ active-right history)
    (pull-row (world-tail {R = R} row left-eq right-eq)
      world-head-right) =
  ⊥-elim (no-shift-right-right-zero {R = R} right-eq)
indexed-pullback-var
    (indexed-factor-paired rightˢ active-right history)
    (pull-row
      (world-tail source-row source-left source-right)
      (world-tail target-row target-left target-right)) =
  there (⇑ᵢ-ˣ∈ (indexed-pullback-var history
    (align-world-rows source-row target-row
      (shift-left-view-injective rightˢ
        (trans source-left (sym target-left)))
      (shift-right-view-injective rightˢ
        (trans source-right (sym target-right))))))

indexed-source-star :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ Z} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  WorldRow source Z ★ᵛ ★ᵛ →
  (Z ˣ⊑★) ∈ Ψ
indexed-source-star indexed-factor-root row =
  root-source-star row
indexed-source-star
    (indexed-factor-paired mode active history)
    (world-tail source-row source-left source-right) =
  there
    (⇑ᵢ-★∈
      (indexed-source-star history
        (align-world-row-star source-row
          (shift-left-view-injective mode
            (trans source-left (sym (shift-left-star mode))))
          (shift-right-view-injective mode
            (trans source-right (sym (shift-right-star mode)))))))

paired-route-var-var-pullback :
  ∀ {source-world target-world fuel Z W X Y} →
  PairedLower
    (world-context source-world)
    (world-common-depth source-world)
    (＇ Z) (＇ X) (＇ Y)
    (world-left-depth source-world)
    (world-right-depth source-world) →
  EnumRoute fuel
    (left-context (world-context target-world))
    (right-context (world-context target-world))
    (world-common-depth target-world)
    (world-left-depth target-world)
    (world-right-depth target-world)
    (＇ X) (＇ Y) (＇ W) →
  (Z < world-common-depth source-world) ×
  (W < world-common-depth target-world) ×
  PullsBack source-world target-world Z W
paired-route-var-var-pullback
    (paired-var-var source-row Z<Δ X<Δ Y<Δ) route =
  let W<Δ , target-row = route-vars-world-row route in
  Z<Δ , W<Δ ,
  pull-row (generated-row-complete source-row) target-row

paired-route-var-star-pullback :
  ∀ {source-world target-world fuel Z W X} →
  PairedLower
    (world-context source-world)
    (world-common-depth source-world)
    (＇ Z) (＇ X) ★
    (world-left-depth source-world)
    (world-right-depth source-world) →
  EnumRoute fuel
    (left-context (world-context target-world))
    (right-context (world-context target-world))
    (world-common-depth target-world)
    (world-left-depth target-world)
    (world-right-depth target-world)
    (＇ X) ★ (＇ W) →
  (Z < world-common-depth source-world) ×
  (W < world-common-depth target-world) ×
  PullsBack source-world target-world Z W
paired-route-var-star-pullback
    (paired-var-star source-row Z<Δ X<Δ) route =
  let W<Δ , target-row = route-var-star-world-row route in
  Z<Δ , W<Δ ,
  pull-row (generated-row-complete source-row) target-row

paired-route-star-var-pullback :
  ∀ {source-world target-world fuel Z W Y} →
  PairedLower
    (world-context source-world)
    (world-common-depth source-world)
    (＇ Z) ★ (＇ Y)
    (world-left-depth source-world)
    (world-right-depth source-world) →
  EnumRoute fuel
    (left-context (world-context target-world))
    (right-context (world-context target-world))
    (world-common-depth target-world)
    (world-left-depth target-world)
    (world-right-depth target-world)
    ★ (＇ Y) (＇ W) →
  (Z < world-common-depth source-world) ×
  (W < world-common-depth target-world) ×
  PullsBack source-world target-world Z W
paired-route-star-var-pullback
    (paired-star-var source-row Z<Δ Y<Δ) route =
  let W<Δ , target-row = route-star-var-world-row route in
  Z<Δ , W<Δ ,
  pull-row (generated-row-complete source-row) target-row

paired-inst-star :
  ∀ {Σ Δᶜ Δᴸ Δᴿ C A B} →
  PairedLower (extend-span neitherˢ Σ) (suc Δᶜ)
    C A B Δᴸ Δᴿ →
  PairedLower Σ Δᶜ (C [ ★ ]ᵗ) A B Δᴸ Δᴿ
paired-inst-star lower =
  pair-lower
    (inst-starᵢ (paired-lower-left lower))
    (inst-starᵢ (paired-lower-right lower))

source-fuel-inst-star :
  ∀ {fuel C} →
  SourceFuel (suc (suc fuel)) (`∀ C) →
  SourceFuel (suc fuel) (C [ ★ ]ᵗ)
source-fuel-inst-star (source-ok enough) =
  source-ok
    (subst (λ n → n ≤ _) (sym (sizeTy-subst-starᵢ zero _))
      (s≤s⁻¹ enough))

source-fuel-arrow-left :
  ∀ {fuel C₁ C₂} →
  SourceFuel (suc (suc fuel)) (C₁ ⇒ C₂) →
  SourceFuel (suc fuel) C₁
source-fuel-arrow-left (source-ok enough) =
  source-ok
    (≤-trans (m≤m+n _ _) (s≤s⁻¹ enough))

source-fuel-arrow-right :
  ∀ {fuel C₁ C₂} →
  SourceFuel (suc (suc fuel)) (C₁ ⇒ C₂) →
  SourceFuel (suc fuel) C₂
source-fuel-arrow-right (source-ok enough) =
  source-ok
    (≤-trans (m≤n+m _ _) (s≤s⁻¹ enough))

paired-left-path-incompatible-worker :
  ∀ (pathFuel sourceFuel : ℕ)
    {modes Φ Δᶜ Δᴸ Δᴿ C A B X L R} →
  EnoughFuel pathFuel A B →
  SourceFuel sourceFuel C →
  LeftOrigin modes X bothᵉ L →
  RightOrigin modes X bothᵉ R →
  PairedLower
    (span (apply-left modes Φ) (apply-right modes Φ))
    (apply-common-depth modes Δᶜ) C A B
    (apply-left-depth modes Δᴸ)
    (apply-right-depth modes Δᴿ) →
  LeftStarPath A B L →
  ⊥
paired-left-path-incompatible-worker zero sourceFuel enough source
    left-origin right-origin lower path =
  ⊥-elim (fuel-zero-impossible enough)
paired-left-path-incompatible-worker (suc pathFuel) zero enough ()
    left-origin right-origin lower path
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-star ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-base-base ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-base-star ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-star-base ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-base-stars ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-arrow-arrow lower₁ lower₂)
    (path-arrow₁ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-⇒⇒-left enough) sourceFuelFor
    left-origin right-origin lower₁ path
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-arrow-arrow lower₁ lower₂)
    (path-arrow₂ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-⇒⇒-right enough) sourceFuelFor
    left-origin right-origin lower₂ path
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-arrow-star lower₁ lower₂)
    (path-arrow-star₁ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-⇒★-left enough) sourceFuelFor
    left-origin right-origin lower₁ path
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-arrow-star lower₁ lower₂)
    (path-arrow-star₂ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-⇒★-right enough) sourceFuelFor
    left-origin right-origin lower₂ path
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-star-arrow lower₁ lower₂) ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-arrow-stars lower₁ lower₂) ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin lower@(paired-var-var row Z<Δ X<Δ Y<Δ) ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin
    lower@(paired-var-star row Z<Δ X<Δ) path-var-star =
  source-var-star-incompatible
    (left-origin-target-track left-origin)
    (right-origin-var-track right-origin)
    (paired-lower-left lower) (paired-lower-right lower)
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin lower@(paired-star-var row Z<Δ Y<Δ) ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin lower@(paired-var-stars row Z<Δ) ()
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-both lower)
    (path-left-∀ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-∀∀-both enough) sourceFuelFor
    (left-origin-under-both left-origin)
    (right-origin-under-both right-origin)
    lower (remove-right-path path)
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-both lower)
    (path-right-∀ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-∀∀-both enough) sourceFuelFor
    (left-origin-under-both left-origin)
    (right-origin-under-both right-origin)
    lower (remove-left-path path)
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-left occ lower)
    (path-left-∀ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-∀L enough) sourceFuelFor
    (left-origin-under-left left-origin)
    (right-origin-under-left right-origin) lower path
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-left occ lower)
    (path-right-∀ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-∀L enough) sourceFuelFor
    (left-origin-under-left left-origin)
    (right-origin-under-left right-origin)
    lower (path-right-∀ (remove-left-path path))
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-right occ lower)
    (path-left-∀ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-∀R enough) sourceFuelFor
    (left-origin-under-right left-origin)
    (right-origin-under-right right-origin)
    lower (path-left-∀ (remove-right-path path))
paired-left-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-right occ lower)
    (path-right-∀ path) =
  paired-left-path-incompatible-worker pathFuel _
    (fuel-∀R enough) sourceFuelFor
    (left-origin-under-right left-origin)
    (right-origin-under-right right-origin) lower path
paired-left-path-incompatible-worker
    (suc pathFuel) .(suc zero) enough
    (source-ok {budget = zero} ()) left-origin right-origin
    (paired-neither occ lower) path
paired-left-path-incompatible-worker
    (suc pathFuel) .(suc (suc sourceFuel)) enough
    source@(source-ok {budget = suc sourceFuel} enoughSource)
    left-origin right-origin (paired-neither occ lower) path =
  paired-left-path-incompatible-worker
    (suc pathFuel) (suc sourceFuel) enough
    (source-fuel-inst-star source)
    left-origin right-origin (paired-inst-star lower) path

paired-right-path-incompatible-worker :
  ∀ (pathFuel sourceFuel : ℕ)
    {modes Φ Δᶜ Δᴸ Δᴿ C A B X L R} →
  EnoughFuel pathFuel A B →
  SourceFuel sourceFuel C →
  LeftOrigin modes X bothᵉ L →
  RightOrigin modes X bothᵉ R →
  PairedLower
    (span (apply-left modes Φ) (apply-right modes Φ))
    (apply-common-depth modes Δᶜ) C A B
    (apply-left-depth modes Δᴸ)
    (apply-right-depth modes Δᴿ) →
  StarRightPath A B R →
  ⊥
paired-right-path-incompatible-worker zero sourceFuel enough source
    left-origin right-origin lower path =
  ⊥-elim (fuel-zero-impossible enough)
paired-right-path-incompatible-worker (suc pathFuel) zero enough ()
    left-origin right-origin lower path
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-star ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-base-base ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-base-star ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-star-base ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin paired-base-stars ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-arrow-arrow lower₁ lower₂)
    (star-path-arrow₁ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-⇒⇒-left enough) sourceFuelFor
    left-origin right-origin lower₁ path
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-arrow-arrow lower₁ lower₂)
    (star-path-arrow₂ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-⇒⇒-right enough) sourceFuelFor
    left-origin right-origin lower₂ path
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-arrow-star lower₁ lower₂) ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-star-arrow lower₁ lower₂)
    (star-path-star-arrow₁ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-★⇒-left enough) sourceFuelFor
    left-origin right-origin lower₁ path
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-star-arrow lower₁ lower₂)
    (star-path-star-arrow₂ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-★⇒-right enough) sourceFuelFor
    left-origin right-origin lower₂ path
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-arrow-stars lower₁ lower₂) ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin lower@(paired-var-var row Z<Δ X<Δ Y<Δ) ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin lower@(paired-var-star row Z<Δ X<Δ) ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin
    lower@(paired-star-var row Z<Δ Y<Δ) star-path-star-var =
  source-star-var-incompatible
    (left-origin-var-track left-origin)
    (right-origin-target-track right-origin)
    (paired-lower-left lower) (paired-lower-right lower)
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin lower@(paired-var-stars row Z<Δ) ()
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-both lower)
    (star-path-left-∀ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-∀∀-both enough) sourceFuelFor
    (left-origin-under-both left-origin)
    (right-origin-under-both right-origin)
    lower (remove-right-star-path path)
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-both lower)
    (star-path-right-∀ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-∀∀-both enough) sourceFuelFor
    (left-origin-under-both left-origin)
    (right-origin-under-both right-origin)
    lower (remove-left-star-path path)
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-left occ lower)
    (star-path-left-∀ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-∀L enough) sourceFuelFor
    (left-origin-under-left left-origin)
    (right-origin-under-left right-origin) lower path
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-left occ lower)
    (star-path-right-∀ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-∀L enough) sourceFuelFor
    (left-origin-under-left left-origin)
    (right-origin-under-left right-origin)
    lower (star-path-right-∀ (remove-left-star-path path))
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-right occ lower)
    (star-path-left-∀ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-∀R enough) sourceFuelFor
    (left-origin-under-right left-origin)
    (right-origin-under-right right-origin)
    lower (star-path-left-∀ (remove-right-star-path path))
paired-right-path-incompatible-worker (suc pathFuel) sourceFuel enough source
    left-origin right-origin (paired-right occ lower)
    (star-path-right-∀ path) =
  paired-right-path-incompatible-worker pathFuel _
    (fuel-∀R enough) sourceFuelFor
    (left-origin-under-right left-origin)
    (right-origin-under-right right-origin) lower path
paired-right-path-incompatible-worker
    (suc pathFuel) .(suc zero) enough
    (source-ok {budget = zero} ()) left-origin right-origin
    (paired-neither occ lower) path
paired-right-path-incompatible-worker
    (suc pathFuel) .(suc (suc sourceFuel)) enough
    source@(source-ok {budget = suc sourceFuel} enoughSource)
    left-origin right-origin (paired-neither occ lower) path =
  paired-right-path-incompatible-worker
    (suc pathFuel) (suc sourceFuel) enough
    (source-fuel-inst-star source)
    left-origin right-origin (paired-inst-star lower) path

indexed-paired-left-path-incompatible :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ C A B} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  PairedLower
    (world-context (world-extend bothˢ source))
    (world-common-depth (world-extend bothˢ source)) C A B
    (world-left-depth (world-extend bothˢ source))
    (world-right-depth (world-extend bothˢ source)) →
  LeftStarPath A B zero →
  ⊥
indexed-paired-left-path-incompatible
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    history lower path
    with indexed-source-schedule history
indexed-paired-left-path-incompatible
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    history lower path
    | source-schedule modes context-eq common-eq left-eq right-eq =
  paired-left-path-incompatible-worker (fuelFor A B) _
    {modes = bothᵉ ∷ modes} {Φ = Φ}
    {Δᶜ = Δᴸ} {Δᴸ = Δᴿ} {Δᴿ = Δᴿ}
    fuelFor-enough sourceFuelFor left-origin-both right-origin-both
    (transport-paired-lower
      (cong (extend-span bothˢ) context-eq)
      (cong suc common-eq) (cong suc left-eq) (cong suc right-eq)
      lower)
    path

indexed-paired-right-path-incompatible :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ C A B} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  PairedLower
    (world-context (world-extend bothˢ source))
    (world-common-depth (world-extend bothˢ source)) C A B
    (world-left-depth (world-extend bothˢ source))
    (world-right-depth (world-extend bothˢ source)) →
  StarRightPath A B zero →
  ⊥
indexed-paired-right-path-incompatible
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    history lower path
    with indexed-source-schedule history
indexed-paired-right-path-incompatible
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    history lower path
    | source-schedule modes context-eq common-eq left-eq right-eq =
  paired-right-path-incompatible-worker (fuelFor A B) _
    {modes = bothᵉ ∷ modes} {Φ = Φ}
    {Δᶜ = Δᴸ} {Δᴸ = Δᴿ} {Δᴿ = Δᴿ}
    fuelFor-enough sourceFuelFor left-origin-both right-origin-both
    (transport-paired-lower
      (cong (extend-span bothˢ) context-eq)
      (cong suc common-eq) (cong suc left-eq) (cong suc right-eq)
      lower)
    path

paired-both-compatible-route :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ fuel C A B D} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  PairedLower
    (world-context (world-extend bothˢ source))
    (world-common-depth (world-extend bothˢ source)) C A B
    (world-left-depth (world-extend bothˢ source))
    (world-right-depth (world-extend bothˢ source)) →
  EnumRoute (suc fuel)
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target) (world-right-depth target)
    (`∀ A) (`∀ B) D →
  ∃[ E ]
    EnumRoute fuel
      (left-context (world-context (world-extend bothˢ target)))
      (right-context (world-context (world-extend bothˢ target)))
      (world-common-depth (world-extend bothˢ target))
      (world-left-depth (world-extend bothˢ target))
      (world-right-depth (world-extend bothˢ target)) A B E
paired-both-compatible-route history source (route-both route) =
  _ , route
paired-both-compatible-route history source
    (route-left occ route) =
  ⊥-elim
    (indexed-paired-left-path-incompatible history source
      (world-left-route-path (indexed-target-schedule history) occ route))
paired-both-compatible-route history source
    (route-right occ route) =
  ⊥-elim
    (indexed-paired-right-path-incompatible history source
      (world-right-route-path (indexed-target-schedule history) occ route))

data BinderFree : Ty → Set where
  free-★ : BinderFree ★
  free-var : ∀ {X} → BinderFree (＇ X)
  free-base : ∀ {ι} → BinderFree (‵ ι)
  free-arrow : ∀ {A B} →
    BinderFree A →
    BinderFree B →
    BinderFree (A ⇒ B)

data DirectTerminalFactor (source target : SpanWorld) :
    Ty → Ty → Set where
  direct-star : DirectTerminalFactor source target ★ ★

  direct-base : ∀ {ι} →
    DirectTerminalFactor source target (‵ ι) (‵ ι)

  direct-base-star : ∀ {ι} →
    DirectTerminalFactor source target (‵ ι) ★

  direct-arrow : ∀ {C₁ C₂ D₁ D₂} →
    DirectTerminalFactor source target C₁ D₁ →
    DirectTerminalFactor source target C₂ D₂ →
    DirectTerminalFactor source target (C₁ ⇒ C₂) (D₁ ⇒ D₂)

  direct-arrow-star : ∀ {C₁ C₂} →
    DirectTerminalFactor source target C₁ ★ →
    DirectTerminalFactor source target C₂ ★ →
    DirectTerminalFactor source target (C₁ ⇒ C₂) ★

  direct-variable : ∀ {Z W} →
    Z < world-common-depth source →
    W < world-common-depth target →
    PullsBack source target Z W →
    DirectTerminalFactor source target (＇ Z) (＇ W)

  direct-variable-star : ∀ {Z} →
    Z < world-common-depth source →
    WorldRow source Z ★ᵛ ★ᵛ →
    DirectTerminalFactor source target (＇ Z) ★

indexed-direct-terminal-imprecision :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ C D} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  DirectTerminalFactor source target C D →
  Ψ ∣ Δˢ ⊢ C ⊑ D ⊣ Δᵗ
indexed-direct-terminal-imprecision history direct-star = id★
indexed-direct-terminal-imprecision history direct-base = idι
indexed-direct-terminal-imprecision history direct-base-star = tag _
indexed-direct-terminal-imprecision history
    (direct-arrow factor₁ factor₂) =
  indexed-direct-terminal-imprecision history factor₁ ↦
  indexed-direct-terminal-imprecision history factor₂
indexed-direct-terminal-imprecision history
    (direct-arrow-star factor₁ factor₂) =
  tag indexed-direct-terminal-imprecision history factor₁ ⇛
  indexed-direct-terminal-imprecision history factor₂
indexed-direct-terminal-imprecision {C = ＇ z} {D = ＇ w} history
    (direct-variable Z<source W<target pull) =
  idˣ (indexed-pullback-var history pull)
    (subst (λ Δ → z < Δ) (indexed-source-depth history) Z<source)
    (subst (λ Δ → w < Δ) (indexed-target-depth history) W<target)
indexed-direct-terminal-imprecision {C = ＇ z} {D = ★} history
    (direct-variable-star Z<source source-row) =
  tagˣ (indexed-source-star history source-row)
    (subst (λ Δ → z < Δ) (indexed-source-depth history) Z<source)

paired-both-route-factor-step :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ fuel C A B D} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  PairedLower
    (world-context (world-extend bothˢ source))
    (world-common-depth (world-extend bothˢ source)) C A B
    (world-left-depth (world-extend bothˢ source))
    (world-right-depth (world-extend bothˢ source)) →
  EnumRoute (suc fuel)
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target) (world-right-depth target)
    (`∀ A) (`∀ B) D →
  (∀ {E} →
    EnumRoute fuel
      (left-context (world-context (world-extend bothˢ target)))
      (right-context (world-context (world-extend bothˢ target)))
      (world-common-depth (world-extend bothˢ target))
      (world-left-depth (world-extend bothˢ target))
      (world-right-depth (world-extend bothˢ target)) A B E →
    ∃[ F ]
      (EnumRoute fuel
        (left-context (world-context (world-extend bothˢ target)))
        (right-context (world-context (world-extend bothˢ target)))
        (world-common-depth (world-extend bothˢ target))
        (world-left-depth (world-extend bothˢ target))
        (world-right-depth (world-extend bothˢ target)) A B F ×
       ∀ᵢᶜ Ψ ∣ suc Δˢ ⊢ C ⊑ F ⊣ suc Δᵗ)) →
  ∃[ F ]
    (EnumRoute (suc fuel)
      (left-context (world-context target))
      (right-context (world-context target))
      (world-common-depth target)
      (world-left-depth target) (world-right-depth target)
      (`∀ A) (`∀ B) F ×
     Ψ ∣ Δˢ ⊢ `∀ C ⊑ F ⊣ Δᵗ)
paired-both-route-factor-step history source route recurse
    with paired-both-compatible-route history source route
paired-both-route-factor-step history source route recurse
    | E , compatible
    with recurse compatible
paired-both-route-factor-step history source route recurse
    | E , compatible | F , route′ , factor =
  `∀ F , route-both route′ , ∀ⁱ factor

paired-left-route-factor-step :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ fuel C A B D} →
  {{safeC : GenSafeSource C}} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  occurs zero C ≡ true →
  PairedLower
    (world-context (world-extend leftˢ source))
    (world-common-depth (world-extend leftˢ source)) C A B
    (world-left-depth (world-extend leftˢ source))
    (world-right-depth (world-extend leftˢ source)) →
  EnumRoute (suc fuel)
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target) (world-right-depth target)
    (`∀ A) B D →
  (∀ {E} →
    EnumRoute fuel
      (left-context (world-context (world-extend leftˢ target)))
      (right-context (world-context (world-extend leftˢ target)))
      (world-common-depth (world-extend leftˢ target))
      (world-left-depth (world-extend leftˢ target))
      (world-right-depth (world-extend leftˢ target)) A B E →
    ∃[ F ]
      (EnumRoute fuel
        (left-context (world-context (world-extend leftˢ target)))
        (right-context (world-context (world-extend leftˢ target)))
        (world-common-depth (world-extend leftˢ target))
        (world-left-depth (world-extend leftˢ target))
        (world-right-depth (world-extend leftˢ target)) A B F ×
       ∀ᵢᶜ Ψ ∣ suc Δˢ ⊢ C ⊑ F ⊣ suc Δᵗ)) →
  ∃[ F ]
    (EnumRoute (suc fuel)
      (left-context (world-context target))
      (right-context (world-context target))
      (world-common-depth target)
      (world-left-depth target) (world-right-depth target)
      (`∀ A) B F ×
     Ψ ∣ Δˢ ⊢ `∀ C ⊑ F ⊣ Δᵗ)
paired-left-route-factor-step {{safeC}} history occ source route recurse
    with paired-left-compatible-route history occ source route
paired-left-route-factor-step {{safeC}} history occ source route recurse
    | E , compatible , target-safe , target-occ
    with recurse compatible
paired-left-route-factor-step {{safeC}} history occ source route recurse
    | E , compatible , target-safe , target-occ | F , route′ , factor =
  `∀ F , route-left {{safeF}} factor-occ route′ ,
  ∀ⁱ factor
  where
    factor-occ = occurs-zero-factor-∀ factor occ
    safeF = genSafeSource-forward-if-occursᵢ factor safeC factor-occ

paired-right-route-factor-step :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ fuel C A B D} →
  {{safeC : GenSafeSource C}} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  occurs zero C ≡ true →
  PairedLower
    (world-context (world-extend rightˢ source))
    (world-common-depth (world-extend rightˢ source)) C A B
    (world-left-depth (world-extend rightˢ source))
    (world-right-depth (world-extend rightˢ source)) →
  EnumRoute (suc fuel)
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target) (world-right-depth target)
    A (`∀ B) D →
  (∀ {E} →
    EnumRoute fuel
      (left-context (world-context (world-extend rightˢ target)))
      (right-context (world-context (world-extend rightˢ target)))
      (world-common-depth (world-extend rightˢ target))
      (world-left-depth (world-extend rightˢ target))
      (world-right-depth (world-extend rightˢ target)) A B E →
    ∃[ F ]
      (EnumRoute fuel
        (left-context (world-context (world-extend rightˢ target)))
        (right-context (world-context (world-extend rightˢ target)))
        (world-common-depth (world-extend rightˢ target))
        (world-left-depth (world-extend rightˢ target))
        (world-right-depth (world-extend rightˢ target)) A B F ×
       ∀ᵢᶜ Ψ ∣ suc Δˢ ⊢ C ⊑ F ⊣ suc Δᵗ)) →
  ∃[ F ]
    (EnumRoute (suc fuel)
      (left-context (world-context target))
      (right-context (world-context target))
      (world-common-depth target)
      (world-left-depth target) (world-right-depth target)
      A (`∀ B) F ×
     Ψ ∣ Δˢ ⊢ `∀ C ⊑ F ⊣ Δᵗ)
paired-right-route-factor-step {{safeC}} history occ source route recurse
    with paired-right-compatible-route history occ source route
paired-right-route-factor-step {{safeC}} history occ source route recurse
    | E , compatible , target-safe , target-occ
    with recurse compatible
paired-right-route-factor-step {{safeC}} history occ source route recurse
    | E , compatible , target-safe , target-occ | F , route′ , factor =
  `∀ F , route-right {{safeF}} factor-occ route′ ,
  ∀ⁱ factor
  where
    factor-occ = occurs-zero-factor-∀ factor occ
    safeF = genSafeSource-forward-if-occursᵢ factor safeC factor-occ

paired-neither-route-factor-step :
  ∀ {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ fuel C A B} →
  {{safeC : GenSafeSource C}} →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  occurs zero C ≡ true →
  PairedLower
    (world-context (world-extend neitherˢ source))
    (world-common-depth (world-extend neitherˢ source)) C A B
    (world-left-depth (world-extend neitherˢ source))
    (world-right-depth (world-extend neitherˢ source)) →
  (∃[ F ]
    (EnumRoute fuel
      (left-context (world-context target))
      (right-context (world-context target))
      (world-common-depth target)
      (world-left-depth target) (world-right-depth target) A B F ×
     Ψ ∣ Δˢ ⊢ C [ ★ ]ᵗ ⊑ F ⊣ Δᵗ)) →
  ∃[ F ]
    (EnumRoute fuel
      (left-context (world-context target))
      (right-context (world-context target))
      (world-common-depth target)
      (world-left-depth target) (world-right-depth target) A B F ×
     Ψ ∣ Δˢ ⊢ `∀ C ⊑ F ⊣ Δᵗ)
paired-neither-route-factor-step {C = C} {{safeC}} history occ source
    (F , route , factor) =
  F , route ,
  ⊑-trans-left-idᵢ
    (close-star-lowerᵢ {{safeC}} occ source-wf) factor
  where
    source-wf =
      subst (λ Δ → WfTy (suc Δ) C)
        (indexed-source-depth history)
        (⊑-src-wf (paired-lower-left source))

direct-terminal-factor :
  ∀ {source target fuel C D A B} →
  BinderFree C →
  PairedLower
    (world-context source)
    (world-common-depth source)
    C A B
    (world-left-depth source)
    (world-right-depth source) →
  EnumRoute fuel
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target)
    (world-right-depth target)
    A B D →
  DirectTerminalFactor source target C D
direct-terminal-factor free-★ paired-star route-star =
  direct-star
direct-terminal-factor free-base paired-base-base route-base =
  direct-base
direct-terminal-factor free-base paired-base-star route-base-star =
  direct-base
direct-terminal-factor free-base paired-star-base route-star-base =
  direct-base
direct-terminal-factor free-base paired-base-stars route-star =
  direct-base-star
direct-terminal-factor
    (free-arrow free₁ free₂)
    (paired-arrow-arrow source₁ source₂)
    (route-arrow target₁ target₂) =
  direct-arrow
    (direct-terminal-factor free₁ source₁ target₁)
    (direct-terminal-factor free₂ source₂ target₂)
direct-terminal-factor
    (free-arrow free₁ free₂)
    (paired-arrow-star source₁ source₂)
    (route-arrow-star target₁ target₂) =
  direct-arrow
    (direct-terminal-factor free₁ source₁ target₁)
    (direct-terminal-factor free₂ source₂ target₂)
direct-terminal-factor
    (free-arrow free₁ free₂)
    (paired-star-arrow source₁ source₂)
    (route-star-arrow target₁ target₂) =
  direct-arrow
    (direct-terminal-factor free₁ source₁ target₁)
    (direct-terminal-factor free₂ source₂ target₂)
direct-terminal-factor
    (free-arrow free₁ free₂)
    (paired-arrow-stars source₁ source₂)
    route-star =
  direct-arrow-star
    (direct-terminal-factor free₁ source₁ (route-star {fuel = zero}))
    (direct-terminal-factor free₂ source₂ (route-star {fuel = zero}))
direct-terminal-factor
    {target = target} free-var
    source@(paired-var-var source-row Z<Δ X<Δ Y<Δ)
    route@(route-vars W∈)
    with var-candidate-member-shape
      {limit = world-common-depth target}
      {Φᴸ = left-context (world-context target)}
      {Φᴿ = right-context (world-context target)} W∈
direct-terminal-factor
    free-var source@(paired-var-var source-row Z<Δ X<Δ Y<Δ)
    route@(route-vars W∈)
    | W , refl , W<Δ , ok
    with paired-route-var-var-pullback source route
direct-terminal-factor
    free-var source@(paired-var-var source-row Z<Δ X<Δ Y<Δ)
    route@(route-vars W∈)
    | W , refl , W<Δ , ok | Z<Δ′ , W<Δ′ , pull =
  direct-variable Z<Δ′ W<Δ′ pull
direct-terminal-factor
    {target = target} free-var
    source@(paired-var-star source-row Z<Δ X<Δ)
    route@(route-var-star W∈)
    with var-candidate-member-shape
      {limit = world-common-depth target}
      {Φᴸ = left-context (world-context target)}
      {Φᴿ = right-context (world-context target)} W∈
direct-terminal-factor
    free-var source@(paired-var-star source-row Z<Δ X<Δ)
    route@(route-var-star W∈)
    | W , refl , W<Δ , ok
    with paired-route-var-star-pullback source route
direct-terminal-factor
    free-var source@(paired-var-star source-row Z<Δ X<Δ)
    route@(route-var-star W∈)
    | W , refl , W<Δ , ok | Z<Δ′ , W<Δ′ , pull =
  direct-variable Z<Δ′ W<Δ′ pull
direct-terminal-factor
    {target = target} free-var
    source@(paired-star-var source-row Z<Δ Y<Δ)
    route@(route-star-var W∈)
    with var-candidate-member-shape
      {limit = world-common-depth target}
      {Φᴸ = left-context (world-context target)}
      {Φᴿ = right-context (world-context target)} W∈
direct-terminal-factor
    free-var source@(paired-star-var source-row Z<Δ Y<Δ)
    route@(route-star-var W∈)
    | W , refl , W<Δ , ok
    with paired-route-star-var-pullback source route
direct-terminal-factor
    free-var source@(paired-star-var source-row Z<Δ Y<Δ)
    route@(route-star-var W∈)
    | W , refl , W<Δ , ok | Z<Δ′ , W<Δ′ , pull =
  direct-variable Z<Δ′ W<Δ′ pull
direct-terminal-factor free-var
    (paired-var-stars source-row Z<Δ) route-star =
  direct-variable-star Z<Δ (generated-row-complete source-row)

star-factor-worker :
  ∀ (sourceFuel : ℕ)
    {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ C} →
  SourceFuel sourceFuel C →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  PairedLower
    (world-context source) (world-common-depth source) C ★ ★
    (world-left-depth source) (world-right-depth source) →
  Ψ ∣ Δˢ ⊢ C ⊑ ★ ⊣ Δᵗ
star-factor-worker zero () history lower
star-factor-worker sourceFuel source history paired-star = id★
star-factor-worker sourceFuel source history paired-base-stars = tag _
star-factor-worker sourceFuel source history
    (paired-var-stars source-row Z<Δ) =
  tagˣ
    (indexed-source-star history (generated-row-complete source-row))
    (subst (λ Δ → _ < Δ) (indexed-source-depth history) Z<Δ)
star-factor-worker .(suc zero)
    (source-ok {budget = zero} ()) history
    (paired-arrow-stars lower₁ lower₂)
star-factor-worker (suc (suc sourceFuel)) source history
    (paired-arrow-stars lower₁ lower₂) =
  tag
    (star-factor-worker (suc sourceFuel)
      (source-fuel-arrow-left source) history lower₁)
    ⇛
    star-factor-worker (suc sourceFuel)
      (source-fuel-arrow-right source) history lower₂
star-factor-worker .(suc zero)
    (source-ok {budget = zero} ()) history
    (paired-neither {{safe}} occ lower)
star-factor-worker (suc (suc sourceFuel)) source history
    (paired-neither {C = C} {{safe}} occ lower) =
  ⊑-trans-left-idᵢ
    (close-star-lowerᵢ {{safe}} occ source-wf)
    (star-factor-worker (suc sourceFuel)
      (source-fuel-inst-star source) history (paired-inst-star lower))
  where
    source-wf =
      subst (λ Δ → WfTy (suc Δ) C)
        (indexed-source-depth history)
        (⊑-src-wf (paired-lower-left lower))

route-factor-worker :
  ∀ (fuel sourceFuel : ℕ)
    {Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ C A B D} →
  SourceFuel sourceFuel C →
  IndexedFactorWorlds Φ Δᴸ Δᴿ source target Ψ Δˢ Δᵗ →
  PairedLower
    (world-context source) (world-common-depth source) C A B
    (world-left-depth source) (world-right-depth source) →
  EnumRoute fuel
    (left-context (world-context target))
    (right-context (world-context target))
    (world-common-depth target)
    (world-left-depth target) (world-right-depth target) A B D →
  ∃[ F ]
    (EnumRoute fuel
      (left-context (world-context target))
      (right-context (world-context target))
      (world-common-depth target)
      (world-left-depth target) (world-right-depth target) A B F ×
     Ψ ∣ Δˢ ⊢ C ⊑ F ⊣ Δᵗ)
route-factor-worker zero sourceFuel source history lower ()
route-factor-worker (suc fuel) zero () history lower route
route-factor-worker (suc fuel) sourceFuel source history
    lower@(paired-arrow-stars lower₁ lower₂) route-star =
  ★ , route-star , star-factor-worker sourceFuel source history lower
route-factor-worker
    (suc fuel) .(suc zero) (source-ok {budget = zero} ()) history
    (paired-neither {{safe}} occ lower) route
route-factor-worker
    (suc fuel) (suc (suc sourceFuel)) source history
    (paired-neither {{safe}} occ lower) route =
  paired-neither-route-factor-step {{safe}} history occ lower
    (route-factor-worker (suc fuel) (suc sourceFuel)
      (source-fuel-inst-star source) history
      (paired-inst-star lower) route)
route-factor-worker (suc fuel) sourceFuel source history
    lower@paired-star route@route-star =
  ★ , route-star ,
  indexed-direct-terminal-imprecision history
    (direct-terminal-factor free-★ lower route)
route-factor-worker (suc fuel) sourceFuel source history
    lower@paired-base-base route@route-base =
  _ , route-base ,
  indexed-direct-terminal-imprecision history
    (direct-terminal-factor free-base lower route)
route-factor-worker (suc fuel) sourceFuel source history
    lower@paired-base-star route@route-base-star =
  _ , route-base-star ,
  indexed-direct-terminal-imprecision history
    (direct-terminal-factor free-base lower route)
route-factor-worker (suc fuel) sourceFuel source history
    lower@paired-star-base route@route-star-base =
  _ , route-star-base ,
  indexed-direct-terminal-imprecision history
    (direct-terminal-factor free-base lower route)
route-factor-worker (suc fuel) sourceFuel source history
    lower@paired-base-stars route@route-star =
  ★ , route-star ,
  indexed-direct-terminal-imprecision history
    (direct-terminal-factor free-base lower route)
route-factor-worker (suc fuel) sourceFuel source history
    lower@(paired-var-var source-row Z<Δ X<Δ Y<Δ)
    route@(route-vars W∈) =
  _ , route ,
  indexed-direct-terminal-imprecision history
    (direct-terminal-factor free-var lower route)
route-factor-worker (suc fuel) sourceFuel source history
    lower@(paired-var-star source-row Z<Δ X<Δ)
    route@(route-var-star W∈) =
  _ , route ,
  indexed-direct-terminal-imprecision history
    (direct-terminal-factor free-var lower route)
route-factor-worker (suc fuel) sourceFuel source history
    lower@(paired-star-var source-row Z<Δ Y<Δ)
    route@(route-star-var W∈) =
  _ , route ,
  indexed-direct-terminal-imprecision history
    (direct-terminal-factor free-var lower route)
route-factor-worker (suc fuel) sourceFuel source history
    lower@(paired-var-stars source-row Z<Δ) route@route-star =
  ★ , route-star ,
  indexed-direct-terminal-imprecision history
    (direct-terminal-factor free-var lower route)
route-factor-worker (suc fuel) sourceFuel source history
    (paired-arrow-arrow lower₁ lower₂) (route-arrow route₁ route₂)
    with route-factor-worker fuel _ sourceFuelFor history lower₁ route₁
       | route-factor-worker fuel _ sourceFuelFor history lower₂ route₂
route-factor-worker (suc fuel) sourceFuel source history
    (paired-arrow-arrow lower₁ lower₂) (route-arrow route₁ route₂)
    | F₁ , route₁′ , factor₁ | F₂ , route₂′ , factor₂ =
  F₁ ⇒ F₂ , route-arrow route₁′ route₂′ , factor₁ ↦ factor₂
route-factor-worker (suc fuel) sourceFuel source history
    (paired-arrow-star lower₁ lower₂)
    (route-arrow-star route₁ route₂)
    with route-factor-worker fuel _ sourceFuelFor history lower₁ route₁
       | route-factor-worker fuel _ sourceFuelFor history lower₂ route₂
route-factor-worker (suc fuel) sourceFuel source history
    (paired-arrow-star lower₁ lower₂)
    (route-arrow-star route₁ route₂)
    | F₁ , route₁′ , factor₁ | F₂ , route₂′ , factor₂ =
  F₁ ⇒ F₂ , route-arrow-star route₁′ route₂′ ,
  factor₁ ↦ factor₂
route-factor-worker (suc fuel) sourceFuel source history
    (paired-star-arrow lower₁ lower₂)
    (route-star-arrow route₁ route₂)
    with route-factor-worker fuel _ sourceFuelFor history lower₁ route₁
       | route-factor-worker fuel _ sourceFuelFor history lower₂ route₂
route-factor-worker (suc fuel) sourceFuel source history
    (paired-star-arrow lower₁ lower₂)
    (route-star-arrow route₁ route₂)
    | F₁ , route₁′ , factor₁ | F₂ , route₂′ , factor₂ =
  F₁ ⇒ F₂ , route-star-arrow route₁′ route₂′ ,
  factor₁ ↦ factor₂
route-factor-worker (suc fuel) sourceFuel source history
    (paired-both lower) route =
  paired-both-route-factor-step history lower route
    (λ compatible →
      route-factor-worker fuel _ sourceFuelFor
        (indexed-factor-paired bothˢ active-both history)
        lower compatible)
route-factor-worker (suc fuel) sourceFuel source history
    (paired-left {{safe}} occ lower) route =
  paired-left-route-factor-step {{safe}} history occ lower route
    (λ compatible →
      route-factor-worker fuel _ sourceFuelFor
        (indexed-factor-paired leftˢ active-left history)
        lower compatible)
route-factor-worker (suc fuel) sourceFuel source history
    (paired-right {{safe}} occ lower) route =
  paired-right-route-factor-step {{safe}} history occ lower route
    (λ compatible →
      route-factor-worker fuel _ sourceFuelFor
        (indexed-factor-paired rightˢ active-right history)
        lower compatible)

rawEndpointMlbsAt-factor :
  ∀ {Φ Δᴸ Δᴿ A B C C′} →
  Φ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴿ →
  C′ ∈ rawEndpointMlbsAt Δᴿ A B →
  ∃[ D ]
    (D ∈ rawEndpointMlbsAt Δᴿ A B ×
     Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ)
rawEndpointMlbsAt-factor {A = A} {B = B} C⊑A C⊑B C′∈
    with route-factor-worker (fuelFor A B) _ sourceFuelFor
      indexed-factor-root (pair-lower C⊑A C⊑B)
      (raw-endpoint-membership→route C′∈)
rawEndpointMlbsAt-factor C⊑A C⊑B C′∈
    | D , route , factor =
  D , raw-endpoint-route→membership route , factor
