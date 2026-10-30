module proof.LR.InterpProps where

-- File Charter:
--   * Interpretations (notes/logrel-dgg.md, Section 7, item 1).
--   * Two interpretations are equivalent when they agree pointwise on
--     the types and their leaves are equivalent: equal entries, or
--     semantic relations that imply each other.
--   * Transporting along the identity embeddings, or along two
--     embeddings in turn, gives an equivalent interpretation; so do the
--     reflexive and the composite world extensions.
--   * The value relation and the expression relations respect
--     equivalent interpretations, by induction on the precision
--     derivation and the stage; no function extensionality.

import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst₂)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import CastTerms using (Term; renameᵗᵐ; `_; ƛ_; _·_; Λ_; _⦂∀_[_];
  $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame)
open import Reduction using (StoreChanges)
open import proof.DGG.CenterRename using (_∘↪_)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import proof.LR.WorldProps

private
  variable
    Δ Δ′ ΘL ΘR ΔL₁ ΔR₁ ΔL₂ ΔR₂ ΔL₃ ΔR₃ : TyCtx

------------------------------------------------------------------------
-- Equivalent leaves and interpretations
------------------------------------------------------------------------

infix 4 _≈ˡ_ _≈ᴵ_

data _≈ˡ_ {ΘL ΘR} : Leaf ΘL ΘR → Leaf ΘL ΘR → Set₁ where
  syn≈ : ∀ {e e′} → e ≡ e′ → syn e ≈ˡ syn e′
  sem≈ : ∀ {R R′ : RelΩ ΘL ΘR}
    → (∀ k w τL τR V V′ → R k w τL τR V V′ → R′ k w τL τR V V′)
    → (∀ k w τL τR V V′ → R′ k w τL τR V V′ → R k w τL τR V V′)
    → sem R ≈ˡ sem R′

≈ˡ-refl : ∀ {l : Leaf ΘL ΘR} → l ≈ˡ l
≈ˡ-refl {l = syn e} = syn≈ refl
≈ˡ-refl {l = sem R} = sem≈ (λ k w τL τR V V′ r → r) (λ k w τL τR V V′ r → r)

≈ˡ-sym : ∀ {l l′ : Leaf ΘL ΘR} → l ≈ˡ l′ → l′ ≈ˡ l
≈ˡ-sym (syn≈ e) = syn≈ (sym e)
≈ˡ-sym (sem≈ to from) = sem≈ from to

record _≈ᴵ_ (δ δ′ : Interp Δ Δ′ ΘL ΘR) : Set₁ where
  field
    δl≡ : ∀ X → δl δ X ≡ δl δ′ X
    δr≡ : ∀ Y → δr δ Y ≡ δr δ′ Y
    leaf≈ : ∀ X → leaf δ X ≈ˡ leaf δ′ X

open _≈ᴵ_ public

≈ᴵ-refl : ∀ {δ : Interp Δ Δ′ ΘL ΘR} → δ ≈ᴵ δ
δl≡ ≈ᴵ-refl X = refl
δr≡ ≈ᴵ-refl Y = refl
leaf≈ ≈ᴵ-refl X = ≈ˡ-refl

≈ᴵ-sym : ∀ {δ δ′ : Interp Δ Δ′ ΘL ΘR} → δ ≈ᴵ δ′ → δ′ ≈ᴵ δ
δl≡ (≈ᴵ-sym h) X = sym (δl≡ h X)
δr≡ (≈ᴵ-sym h) Y = sym (δr≡ h Y)
leaf≈ (≈ᴵ-sym h) X = ≈ˡ-sym (leaf≈ h X)

≈ˡ-trans : ∀ {l l′ l″ : Leaf ΘL ΘR} → l ≈ˡ l′ → l′ ≈ˡ l″ → l ≈ˡ l″
≈ˡ-trans (syn≈ e) (syn≈ e′) = syn≈ (trans e e′)
≈ˡ-trans (sem≈ to from) (sem≈ to′ from′) =
  sem≈ (λ k w τL τR V V′ r → to′ k w τL τR V V′ (to k w τL τR V V′ r))
       (λ k w τL τR V V′ r → from k w τL τR V V′ (from′ k w τL τR V V′ r))

≈ᴵ-trans : ∀ {δ δ′ δ″ : Interp Δ Δ′ ΘL ΘR} → δ ≈ᴵ δ′ → δ′ ≈ᴵ δ″ → δ ≈ᴵ δ″
δl≡ (≈ᴵ-trans h h′) X = trans (δl≡ h X) (δl≡ h′ X)
δr≡ (≈ᴵ-trans h h′) Y = trans (δr≡ h Y) (δr≡ h′ Y)
leaf≈ (≈ᴵ-trans h h′) X = ≈ˡ-trans (leaf≈ h X) (leaf≈ h′ X)

------------------------------------------------------------------------
-- Transport
------------------------------------------------------------------------

transportLeaf-resp : (σL : ΔL₁ ↪ᵗ ΔL₂) (σR : ΔR₁ ↪ᵗ ΔR₂)
    {l l′ : Leaf ΔL₁ ΔR₁}
  → l ≈ˡ l′ → transportLeaf σL σR l ≈ˡ transportLeaf σL σR l′
transportLeaf-resp σL σR (syn≈ e) = syn≈ (cong (renameEntry σL σR) e)
transportLeaf-resp σL σR (sem≈ to from) =
  sem≈ (λ k w τL τR → to k w (τL ∘↪ σL) (τR ∘↪ σR))
       (λ k w τL τR → from k w (τL ∘↪ σL) (τR ∘↪ σR))

transportLeaf-id : (l : Leaf ΘL ΘR) → transportLeaf id↪ᵗ id↪ᵗ l ≈ˡ l
transportLeaf-id (syn e) = syn≈ (renameEntry-id e)
transportLeaf-id (sem R) =
  sem≈ (λ k w τL τR V V′ →
          subst₂ (λ a b → R k w a b V V′) (∘↪-idʳ τL) (∘↪-idʳ τR))
       (λ k w τL τR V V′ →
          subst₂ (λ a b → R k w a b V V′)
            (sym (∘↪-idʳ τL)) (sym (∘↪-idʳ τR)))

transportLeaf-∘ : (πL : ΔL₂ ↪ᵗ ΔL₃) (ηL : ΔL₁ ↪ᵗ ΔL₂)
    (πR : ΔR₂ ↪ᵗ ΔR₃) (ηR : ΔR₁ ↪ᵗ ΔR₂) (l : Leaf ΔL₁ ΔR₁)
  → transportLeaf πL πR (transportLeaf ηL ηR l)
    ≈ˡ transportLeaf (πL ∘↪ ηL) (πR ∘↪ ηR) l
transportLeaf-∘ πL ηL πR ηR (syn e) = syn≈ (renameEntry-∘ πL ηL πR ηR e)
transportLeaf-∘ πL ηL πR ηR (sem R) =
  sem≈ (λ k w τL τR V V′ →
          subst₂ (λ a b → R k w a b V V′)
            (∘↪-assoc τL πL ηL) (∘↪-assoc τR πR ηR))
       (λ k w τL τR V V′ →
          subst₂ (λ a b → R k w a b V V′)
            (sym (∘↪-assoc τL πL ηL)) (sym (∘↪-assoc τR πR ηR)))

transportI-resp : (σL : ΔL₁ ↪ᵗ ΔL₂) (σR : ΔR₁ ↪ᵗ ΔR₂)
    {δ δ′ : Interp Δ Δ′ ΔL₁ ΔR₁}
  → δ ≈ᴵ δ′ → transportI σL σR δ ≈ᴵ transportI σL σR δ′
δl≡ (transportI-resp σL σR h) X =
  cong (renameᵗ (toRenameᵗ σL)) (δl≡ h X)
δr≡ (transportI-resp σL σR h) Y =
  cong (renameᵗ (toRenameᵗ σR)) (δr≡ h Y)
leaf≈ (transportI-resp σL σR h) X = transportLeaf-resp σL σR (leaf≈ h X)

transportI-id : (δ : Interp Δ Δ′ ΘL ΘR) → transportI id↪ᵗ id↪ᵗ δ ≈ᴵ δ
δl≡ (transportI-id δ) X = renameTy-id (δl δ X)
δr≡ (transportI-id δ) Y = renameTy-id (δr δ Y)
leaf≈ (transportI-id δ) X = transportLeaf-id (leaf δ X)

transportI-∘ : (πL : ΔL₂ ↪ᵗ ΔL₃) (ηL : ΔL₁ ↪ᵗ ΔL₂)
    (πR : ΔR₂ ↪ᵗ ΔR₃) (ηR : ΔR₁ ↪ᵗ ΔR₂) (δ : Interp Δ Δ′ ΔL₁ ΔR₁)
  → transportI πL πR (transportI ηL ηR δ)
    ≈ᴵ transportI (πL ∘↪ ηL) (πR ∘↪ ηR) δ
δl≡ (transportI-∘ πL ηL πR ηR δ) X = renameTy-∘ πL ηL (δl δ X)
δr≡ (transportI-∘ πL ηL πR ηR δ) Y = renameTy-∘ πR ηR (δr δ Y)
leaf≈ (transportI-∘ πL ηL πR ηR δ) X =
  transportLeaf-∘ πL ηL πR ηR (leaf δ X)

transportI-≡ : ∀ {σL σL′ : ΔL₁ ↪ᵗ ΔL₂} {σR σR′ : ΔR₁ ↪ᵗ ΔR₂}
  → σL ≡ σL′ → σR ≡ σR′ → (δ : Interp Δ Δ′ ΔL₁ ΔR₁)
  → transportI σL σR δ ≈ᴵ transportI σL′ σR′ δ
transportI-≡ refl refl δ = ≈ᴵ-refl

-- along world extensions
↑ᴵ-resp : ∀ {w w′ : World} {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → δ ≈ᴵ δ′ → (e : w′ ⊒ w) → δ ↑ᴵ e ≈ᴵ δ′ ↑ᴵ e
↑ᴵ-resp h e = transportI-resp (ρL e) (ρR e) h

↑ᴵ-refl : ∀ {w : World} (δ : Interp Δ Δ′ (ΔL w) (ΔR w))
  → δ ↑ᴵ ⊒-refl w ≈ᴵ δ
↑ᴵ-refl δ = transportI-id δ

↑ᴵ-trans : ∀ {w w′ w″ : World} (δ : Interp Δ Δ′ (ΔL w) (ΔR w))
    (e′ : w″ ⊒ w′) (e : w′ ⊒ w)
  → (δ ↑ᴵ e) ↑ᴵ e′ ≈ᴵ δ ↑ᴵ ⊒-trans e′ e
↑ᴵ-trans δ e′ e = transportI-∘ (ρL e′) (ρL e) (ρR e′) (ρR e) δ

------------------------------------------------------------------------
-- Extending interpretations
------------------------------------------------------------------------

extPairI-resp : ∀ {T T′} {l l′ : Leaf ΘL ΘR} {δ δ′ : Interp Δ Δ′ ΘL ΘR}
  → l ≈ˡ l′ → δ ≈ᴵ δ′ → extPairI T T′ l δ ≈ᴵ extPairI T T′ l′ δ′
δl≡ (extPairI-resp l≈ h) Fin.zero = refl
δl≡ (extPairI-resp l≈ h) (Fin.suc X) = δl≡ h X
δr≡ (extPairI-resp l≈ h) Fin.zero = refl
δr≡ (extPairI-resp l≈ h) (Fin.suc Y) = δr≡ h Y
leaf≈ (extPairI-resp l≈ h) Fin.zero = l≈
leaf≈ (extPairI-resp l≈ h) (Fin.suc X) = leaf≈ h X

extOnlyI-resp : ∀ {T} {l l′ : Leaf ΘL ΘR} {δ δ′ : Interp Δ Δ′ ΘL ΘR}
  → l ≈ˡ l′ → δ ≈ᴵ δ′ → extOnlyI T l δ ≈ᴵ extOnlyI T l′ δ′
δl≡ (extOnlyI-resp l≈ h) Fin.zero = refl
δl≡ (extOnlyI-resp l≈ h) (Fin.suc X) = δl≡ h X
δr≡ (extOnlyI-resp l≈ h) Y = δr≡ h Y
leaf≈ (extOnlyI-resp l≈ h) Fin.zero = l≈
leaf≈ (extOnlyI-resp l≈ h) (Fin.suc X) = leaf≈ h X

exts-cong : ∀ {σ σ′ : Δ ⇒ˢ Δ′}
  → (∀ X → σ X ≡ σ′ X) → ∀ X → extsᵗ σ X ≡ extsᵗ σ′ X
exts-cong h Fin.zero = refl
exts-cong h (Fin.suc X) = cong (renameᵗ Fin.suc) (h X)

------------------------------------------------------------------------
-- The generic expression closure is monotone in its value relation
------------------------------------------------------------------------

Arrive-map : ∀ {ΔL′ ΔR′} {n n′ : ℕ} {w : World}
    {χsL : StoreChanges (ΔL w) ΔL′} {χsR : StoreChanges (ΔR w) ΔR′}
    {VR VR′ : VRel n w} {le : n′ ≤′ n} {Vl Vr}
  → (∀ {n″} (le′ : n″ ≤′ n) w′ (e : w′ ⊒ w) V V′
       → VR le′ w′ e V V′ → VR′ le′ w′ e V V′)
  → Arrive n n′ w χsL χsR VR le Vl Vr
  → Arrive n n′ w χsL χsR VR′ le Vl Vr
Arrive-map f (tags , ok , v) = tags , ok , f _ _ _ _ _ v

ℰᵍ-map : ∀ d n w {VR VR′ : VRel n w}
  → (∀ {n′} (le : n′ ≤′ n) w′ (e : w′ ⊒ w) V V′
       → VR le w′ e V V′ → VR′ le w′ e V V′)
  → ∀ {Ml Mr} → ℰᵍ d n w VR Ml Mr → ℰᵍ d n w VR′ Ml Mr
ℰᵍ-map ≺ n w f (inj₁ r) = inj₁ r
ℰᵍ-map ≺ n w f (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
ℰᵍ-map ≺ n w f (inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΔR′ , χsR , Vr ,
    eq , sl , sr , vl , vr , a))) =
  inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΔR′ , χsR , Vr ,
    eq , sl , sr , vl , vr , Arrive-map {χsL = χsL} {χsR = χsR} f a))
ℰᵍ-map ≻ n w f (inj₁ r) = inj₁ r
ℰᵍ-map ≻ n w f (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
ℰᵍ-map ≻ n w f (inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΔR′ , χsR , Vr ,
    eq , sl , sr , vl , vr , a))) =
  inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΔR′ , χsR , Vr ,
    eq , sl , sr , vl , vr , Arrive-map {χsL = χsL} {χsR = χsR} f a))

ℰᵍ-≡ : ∀ {d n w} {VR : VRel n w} {Ml Ml′ Mr Mr′}
  → Ml ≡ Ml′ → Mr ≡ Mr′ → ℰᵍ d n w VR Ml Mr → ℰᵍ d n w VR Ml′ Mr′
ℰᵍ-≡ refl refl r = r

------------------------------------------------------------------------
-- The value relation respects equivalent interpretations
------------------------------------------------------------------------

leafRel-resp : ∀ d n w {l l′ : Leaf (ΔL w) (ΔR w)} {Vl Vr}
  → l ≈ˡ l′ → leafRel d n w l Vl Vr → leafRel d n w l′ Vl Vr
leafRel-resp d n w (syn≈ refl) r = r
leafRel-resp d n w (sem≈ to from) r = to n w id↪ᵗ id↪ᵗ _ _ r

mutual
  𝒱-resp : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → δ ≈ᴵ δ′ → 𝒱 d n p w δ Vl Vr → 𝒱 d n p w δ′ Vl Vr
  𝒱-resp ≺ n ★⊑★ w h r = r
  𝒱-resp ≻ n ★⊑★ w h r = G-resp n ★⊑★ w h r
  𝒱-resp ≺ n ι⊑ι w h r = r
  𝒱-resp ≻ n ι⊑ι w h r = r
  𝒱-resp ≺ n (X⊑Y {X = X} x) w h r = leafRel-resp ≺ n w (leaf≈ h X) r
  𝒱-resp ≻ n (X⊑Y {X = X} x) w h r = leafRel-resp ≻ n w (leaf≈ h X) r
  𝒱-resp ≺ n (⇒⊑⇒ p q) w h r = funRel-resp ≺ n p q w h r
  𝒱-resp ≻ n (⇒⊑⇒ p q) w h r = funRel-resp ≻ n p q w h r
  𝒱-resp ≺ n (∀⊑∀ p) w h r = allPair-resp ≺ n p w h r
  𝒱-resp ≻ n (∀⊑∀ p) w h r = allPair-resp ≻ n p w h r
  𝒱-resp ≺ n (⇒⊑★ p q) w h r = funStar-resp ≺ n p q w h r
  𝒱-resp ≻ n (⇒⊑★ p q) w h r = G-resp n (⇒⊑★ p q) w h r
  𝒱-resp ≺ n ι⊑★ w h r = r
  𝒱-resp ≻ n ι⊑★ w h r = G-resp n ι⊑★ w h r
  𝒱-resp ≺ n (X⊑★ {X = X} x) w h r = leafRel-resp ≺ n w (leaf≈ h X) r
  𝒱-resp ≻ n (X⊑★ {X = X} x) w h r = leafRel-resp ≻ n w (leaf≈ h X) r
  𝒱-resp ≺ n (∀⊑ Anv z p) w h r = allOnly-resp ≺ n p w h r
  𝒱-resp ≻ n (∀⊑ {B = ★} Anv z p) w h r = G-resp n (∀⊑ Anv z p) w h r
  𝒱-resp ≻ n (∀⊑ {B = ＇ Y} Anv z p) w h r = allOnly-resp ≻ n p w h r
  𝒱-resp ≻ n (∀⊑ {B = ‵ ι} Anv z p) w h r = allOnly-resp ≻ n p w h r
  𝒱-resp ≻ n (∀⊑ {B = B ⇒ C} Anv z p) w h r = allOnly-resp ≻ n p w h r
  𝒱-resp ≻ n (∀⊑ {B = `∀ B} Anv z p) w h r = allOnly-resp ≻ n p w h r
  𝒱-resp ≺ n ∀★⊑★ w h r = r
  𝒱-resp ≻ n ∀★⊑★ w h r = G-resp n ∀★⊑★ w h r
  𝒱-resp ≺ n (∀⊑★ ns p) w h r = allDeadStar-resp ≺ n p w h r
  𝒱-resp ≻ n (∀⊑★ ns p) w h r = G-resp n (∀⊑★ ns p) w h r
  𝒱-resp ≺ n bot-elim w h ()
  𝒱-resp ≻ n bot-elim w h ()
  𝒱-resp ≺ n bot⊑★ w h ()
  𝒱-resp ≻ n bot⊑★ w h ()

  𝒱≤-resp : ∀ d {n′ n} (le : n′ ≤′ n) {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
      (p : Φ ⊢ A ⊑ A′) w {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → δ ≈ᴵ δ′ → 𝒱≤ d le p w δ Vl Vr → 𝒱≤ d le p w δ′ Vl Vr
  𝒱≤-resp d {n′} ≤′-refl p w h r = 𝒱-resp d n′ p w h r
  𝒱≤-resp d (≤′-step le) p w h r = 𝒱≤-resp d le p w h r

  G-resp : ∀ n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → δ ≈ᴵ δ′ → G n p w δ Vl Vr → G n p w δ′ Vl Vr
  G-resp zero p w h r = r
  G-resp (suc k) ★⊑★ w h r = r
  G-resp (suc k) ι⊑ι w h r = r
  G-resp (suc k) (X⊑Y x) w h r = 𝒱-resp ≻ k (X⊑Y x) w h r
  G-resp (suc k) (⇒⊑⇒ p q) w h r = 𝒱-resp ≻ k (⇒⊑⇒ p q) w h r
  G-resp (suc k) (∀⊑∀ p) w h r = 𝒱-resp ≻ k (∀⊑∀ p) w h r
  G-resp (suc k) (⇒⊑★ p q) w h r = funStar-resp ≻ k p q w h r
  G-resp (suc k) ι⊑★ w h r = r
  G-resp (suc k) (X⊑★ {X = X} x) w h r =
    leafRel-resp ≻ (suc k) w (leaf≈ h X) r
  G-resp (suc k) (∀⊑ {B = ★} Anv z p) w h r = allOnly-resp ≻ k p w h r
  G-resp (suc k) (∀⊑ {B = ＇ Y} Anv z p) w h r =
    𝒱-resp ≻ k (∀⊑ Anv z p) w h r
  G-resp (suc k) (∀⊑ {B = ‵ ι} Anv z p) w h r =
    𝒱-resp ≻ k (∀⊑ Anv z p) w h r
  G-resp (suc k) (∀⊑ {B = B ⇒ C} Anv z p) w h r =
    𝒱-resp ≻ k (∀⊑ Anv z p) w h r
  G-resp (suc k) (∀⊑ {B = `∀ B} Anv z p) w h r =
    𝒱-resp ≻ k (∀⊑ Anv z p) w h r
  G-resp (suc k) ∀★⊑★ w h r = r
  G-resp (suc k) (∀⊑★ ns p) w h r = allDeadStar-resp ≻ k p w h r
  G-resp (suc k) bot-elim w h ()
  G-resp (suc k) bot⊑★ w h ()

  funRel-resp : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′ B B′}
      (p : Φ ⊢ A ⊑ A′) (q : Φ ⊢ B ⊑ B′) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → δ ≈ᴵ δ′ → funRel d n p q w δ Vl Vr → funRel d n p q w δ′ Vl Vr
  funRel-resp d n p q w h r e le Wl Wr vl vr a =
    ℰᵍ-map d _ _
      (λ le′ w″ e′ V V′ →
        𝒱≤-resp d (≤′-trans le′ le) q w″ (↑ᴵ-resp (↑ᴵ-resp h e) e′))
      (r e le Wl Wr vl vr (𝒱≤-resp d le p _ (↑ᴵ-resp (≈ᴵ-sym h) e) a))

  funStar-resp : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
      (p : Φ ⊢ A ⊑ ★) (q : Φ ⊢ B ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → δ ≈ᴵ δ′ → funStar d n p q w δ Vl Vr → funStar d n p q w δ′ Vl Vr
  funStar-resp d n p q w {Vr = ` x} h ()
  funStar-resp d n p q w {Vr = ƛ M} h ()
  funStar-resp d n p q w {Vr = L · M} h ()
  funStar-resp d n p q w {Vr = Λ M} h ()
  funStar-resp d n p q w {Vr = L ⦂∀ C [ T ]} h ()
  funStar-resp d n p q w {Vr = $ κ} h ()
  funStar-resp d n p q w {Vr = L ⊕[ op ] M} h ()
  funStar-resp d n p q w {Vr = Wr ⟨ c ⟩} h (i , r) =
    i , funRel-resp d n p q w h r
  funStar-resp d n p q w {Vr = M ↑ c} h ()
  funStar-resp d n p q w {Vr = M ↓ c} h ()
  funStar-resp d n p q w {Vr = blame} h ()

  allPair-resp : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
      (p : pair Φ ⊢ A ⊑ B) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → δ ≈ᴵ δ′ → allPair d n p w δ Vl Vr → allPair d n p w δ′ Vl Vr
  allPair-resp d n {A = A} {B = B} p w {Vl = Vl} {Vr = Vr} h r e le c =
    ℰᵍ-≡
      (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
        (substᵗ-cong A (exts-cong (δl≡ (↑ᴵ-resp h e)))))
      (cong (λ C → renameᵗᵐ (ρR e) Vr ⦂∀ C [ rightTyS c ])
        (substᵗ-cong B (exts-cong (δr≡ (↑ᴵ-resp h e)))))
      (ℰᵍ-map d _ _
        (λ le′ w″ e′ V V′ →
          𝒱≤-resp d (≤′-trans le′ le) p w″
            (↑ᴵ-resp (extPairI-resp ≈ˡ-refl (↑ᴵ-resp h e)) e′))
        (r e le c))

  allOnly-resp : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
      (p : only Φ ⊢ A ⊑ B) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → δ ≈ᴵ δ′ → allOnly d n p w δ Vl Vr → allOnly d n p w δ′ Vl Vr
  allOnly-resp d n {A = A} p w {Vl = Vl} h r e le c =
    ℰᵍ-≡
      (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTy c ])
        (substᵗ-cong A (exts-cong (δl≡ (↑ᴵ-resp h e)))))
      refl
      (ℰᵍ-map d _ _
        (λ le′ w″ e′ V V′ →
          𝒱≤-resp d (≤′-trans le′ le) p w″
            (↑ᴵ-resp (extOnlyI-resp ≈ˡ-refl (↑ᴵ-resp h e)) e′))
        (r e le c))

  allDead-resp : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A}
      (p : dead Φ ⊢ A ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → δ ≈ᴵ δ′ → allDead d n p w δ Vl Vr → allDead d n p w δ′ Vl Vr
  allDead-resp d n {A = A} p w {Vl = Vl} h r e le T T′ =
    ℰᵍ-≡
      (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ T ])
        (substᵗ-cong A (exts-cong (δl≡ (↑ᴵ-resp h e)))))
      refl
      (ℰᵍ-map d _ _
        (λ le′ w″ e′ V V′ →
          𝒱≤-resp d (≤′-trans le′ le) p w″
            (↑ᴵ-resp (extOnlyI-resp ≈ˡ-refl (↑ᴵ-resp h e)) e′))
        (r e le T T′))

  allDeadStar-resp : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A}
      (p : dead Φ ⊢ A ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → δ ≈ᴵ δ′ → allDeadStar d n p w δ Vl Vr → allDeadStar d n p w δ′ Vl Vr
  allDeadStar-resp d n p w {Vr = ` x} h ()
  allDeadStar-resp d n p w {Vr = ƛ M} h ()
  allDeadStar-resp d n p w {Vr = L · M} h ()
  allDeadStar-resp d n p w {Vr = Λ M} h ()
  allDeadStar-resp d n p w {Vr = L ⦂∀ C [ T ]} h ()
  allDeadStar-resp d n p w {Vr = $ κ} h ()
  allDeadStar-resp d n p w {Vr = L ⊕[ op ] M} h ()
  allDeadStar-resp d n p w {Vr = Wr ⟨ c ⟩} h (i , r) =
    i , allDead-resp d n p w h r
  allDeadStar-resp d n p w {Vr = M ↑ c} h ()
  allDeadStar-resp d n p w {Vr = M ↓ c} h ()
  allDeadStar-resp d n p w {Vr = blame} h ()

------------------------------------------------------------------------
-- The expression relation
------------------------------------------------------------------------

ℰ-resp : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr}
  → δ ≈ᴵ δ′ → ℰ d n p w δ Ml Mr → ℰ d n p w δ′ Ml Mr
ℰ-resp d n p w h =
  ℰᵍ-map d n w (λ le w′ e V V′ → 𝒱≤-resp d le p w′ (↑ᴵ-resp h e))
