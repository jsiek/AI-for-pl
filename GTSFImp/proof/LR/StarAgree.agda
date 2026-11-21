module proof.LR.StarAgree where

-- File Charter:
--   * At a precision derivation into `★`, the value relation reads an
--     interpretation only through its left types and the leaves of its
--     left-only variables: the right types and the paired leaves never
--     occur (notes/logrel-dgg.md, Section 7, the right-only conversion
--     lemma).
--   * So two interpretations that agree there (`_⊢_≈ᴸ_`) relate the
--     same values, by induction on the derivation and the stage, as in
--     `proof.LR.InterpProps`.

import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types
open import Consistency using (toRenameᵗ)
open import CastTerms using (Term; renameᵗᵐ; `_; ƛ_; _·_; Λ_; _⦂∀_[_];
  $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import proof.LR.InterpProps

private
  variable
    Δ Δ′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- Agreement on the left
------------------------------------------------------------------------

infix 4 _⊢_≈ᴸ_

record _⊢_≈ᴸ_ (Φ : Corr Δ Δ′) (δ δ′ : Interp Δ Δ′ ΘL ΘR) : Set₁ where
  field
    δl≡ᴸ : ∀ X → δl δ X ≡ δl δ′ X
    leaf≈ᴸ : ∀ {X} → Φ ∋ X only → leaf δ X ≈ˡ leaf δ′ X

open _⊢_≈ᴸ_ public

≈ᴸ-sym : ∀ {Φ : Corr Δ Δ′} {δ δ′ : Interp Δ Δ′ ΘL ΘR}
  → Φ ⊢ δ ≈ᴸ δ′ → Φ ⊢ δ′ ≈ᴸ δ
δl≡ᴸ (≈ᴸ-sym h) X = sym (δl≡ᴸ h X)
leaf≈ᴸ (≈ᴸ-sym h) x = ≈ˡ-sym (leaf≈ᴸ h x)

↑ᴵ-respᴸ : ∀ {Φ : Corr Δ Δ′} {w w′ : World}
    {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → Φ ⊢ δ ≈ᴸ δ′ → (e : w′ ⊒ w) → Φ ⊢ δ ↑ᴵ e ≈ᴸ δ′ ↑ᴵ e
δl≡ᴸ (↑ᴵ-respᴸ h e) X = cong (renameᵗ (toRenameᵗ (ρL e))) (δl≡ᴸ h X)
leaf≈ᴸ (↑ᴵ-respᴸ h e) x = transportLeaf-resp (ρL e) (ρR e) (leaf≈ᴸ h x)

extOnlyI-respᴸ : ∀ {Φ : Corr Δ Δ′} {T} {l l′ : Leaf ΘL ΘR}
    {δ δ′ : Interp Δ Δ′ ΘL ΘR}
  → l ≈ˡ l′ → Φ ⊢ δ ≈ᴸ δ′ → only Φ ⊢ extOnlyI T l δ ≈ᴸ extOnlyI T l′ δ′
δl≡ᴸ (extOnlyI-respᴸ l≈ h) Fin.zero = refl
δl≡ᴸ (extOnlyI-respᴸ l≈ h) (Fin.suc X) = δl≡ᴸ h X
leaf≈ᴸ (extOnlyI-respᴸ l≈ h) only-here = l≈
leaf≈ᴸ (extOnlyI-respᴸ l≈ h) (only-only x) = leaf≈ᴸ h x

extDeadI-respᴸ : ∀ {Φ : Corr Δ Δ′} {T} {δ δ′ : Interp Δ Δ′ ΘL ΘR}
  → Φ ⊢ δ ≈ᴸ δ′ → dead Φ ⊢ extDeadI T δ ≈ᴸ extDeadI T δ′
δl≡ᴸ (extDeadI-respᴸ h) Fin.zero = refl
δl≡ᴸ (extDeadI-respᴸ h) (Fin.suc X) = δl≡ᴸ h X
leaf≈ᴸ (extDeadI-respᴸ h) (only-dead x) = leaf≈ᴸ h x

------------------------------------------------------------------------
-- The value relation into `★`
------------------------------------------------------------------------

mutual
  𝒱★-agree : ∀ d n {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → Φ ⊢ δ ≈ᴸ δ′ → 𝒱 d n p w δ Vl Vr → 𝒱 d n p w δ′ Vl Vr
  𝒱★-agree ≺ n ★⊑★ w h r = r
  𝒱★-agree ≻ n ★⊑★ w h r = G★-agree n ★⊑★ w h r
  𝒱★-agree ≺ n (⇒⊑★ p q) w h r = funStar-agree ≺ n p q w h r
  𝒱★-agree ≻ n (⇒⊑★ p q) w h r = G★-agree n (⇒⊑★ p q) w h r
  𝒱★-agree ≺ n ι⊑★ w h r = r
  𝒱★-agree ≻ n ι⊑★ w h r = G★-agree n ι⊑★ w h r
  𝒱★-agree ≺ n (X⊑★ x) w h r = leafRel-resp ≺ n w (leaf≈ᴸ h x) r
  𝒱★-agree ≻ n (X⊑★ x) w h r = leafRel-resp ≻ n w (leaf≈ᴸ h x) r
  𝒱★-agree ≺ n (∀⊑ Anv z p) w h r = allOnly★-agree ≺ n p w h r
  𝒱★-agree ≻ n (∀⊑ Anv z p) w h r = G★-agree n (∀⊑ Anv z p) w h r
  𝒱★-agree ≺ n ∀★⊑★ w h r = r
  𝒱★-agree ≻ n ∀★⊑★ w h r = G★-agree n ∀★⊑★ w h r
  𝒱★-agree ≺ n (∀⊑★ ns p) w h r = allDeadStar-agree ≺ n p w h r
  𝒱★-agree ≻ n (∀⊑★ ns p) w h r = G★-agree n (∀⊑★ ns p) w h r
  𝒱★-agree ≺ n bot⊑★ w h ()
  𝒱★-agree ≻ n bot⊑★ w h ()

  𝒱≤★-agree : ∀ d {n′ n} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {A}
      (p : Φ ⊢ A ⊑ ★) w {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → Φ ⊢ δ ≈ᴸ δ′ → 𝒱≤ d le p w δ Vl Vr → 𝒱≤ d le p w δ′ Vl Vr
  𝒱≤★-agree d {n′} ≤′-refl p w h r = 𝒱★-agree d n′ p w h r
  𝒱≤★-agree d (≤′-step le) p w h r = 𝒱≤★-agree d le p w h r

  G★-agree : ∀ n {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → Φ ⊢ δ ≈ᴸ δ′ → G n p w δ Vl Vr → G n p w δ′ Vl Vr
  G★-agree zero p w h r = r
  G★-agree (suc k) ★⊑★ w h r = r
  G★-agree (suc k) ι⊑★ w h r = r
  G★-agree (suc k) (⇒⊑★ p q) w h r = funStar-agree ≻ k p q w h r
  G★-agree (suc k) (X⊑★ x) w h r = leafRel-resp ≻ (suc k) w (leaf≈ᴸ h x) r
  G★-agree (suc k) (∀⊑ Anv z p) w h r = allOnly★-agree ≻ k p w h r
  G★-agree (suc k) ∀★⊑★ w h r = r
  G★-agree (suc k) (∀⊑★ ns p) w h r = allDeadStar-agree ≻ k p w h r
  G★-agree (suc k) bot⊑★ w h ()

  funRel★-agree : ∀ d n {Φ : Corr Δ Δ′} {A B}
      (p : Φ ⊢ A ⊑ ★) (q : Φ ⊢ B ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → Φ ⊢ δ ≈ᴸ δ′ → funRel d n p q w δ Vl Vr → funRel d n p q w δ′ Vl Vr
  funRel★-agree d n p q w h r e le Wl Wr vl vr a =
    ℰᵍ-map d _ _
      (λ le′ w″ e′ V V′ →
        𝒱≤★-agree d (≤′-trans le′ le) q w″ (↑ᴵ-respᴸ (↑ᴵ-respᴸ h e) e′))
      (r e le Wl Wr vl vr
        (𝒱≤★-agree d le p _ (↑ᴵ-respᴸ (≈ᴸ-sym h) e) a))

  funStar-agree : ∀ d n {Φ : Corr Δ Δ′} {A B}
      (p : Φ ⊢ A ⊑ ★) (q : Φ ⊢ B ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → Φ ⊢ δ ≈ᴸ δ′ → funStar d n p q w δ Vl Vr → funStar d n p q w δ′ Vl Vr
  funStar-agree d n p q w {Vr = ` x} h ()
  funStar-agree d n p q w {Vr = ƛ M} h ()
  funStar-agree d n p q w {Vr = L · M} h ()
  funStar-agree d n p q w {Vr = Λ M} h ()
  funStar-agree d n p q w {Vr = L ⦂∀ C [ T ]} h ()
  funStar-agree d n p q w {Vr = $ κ} h ()
  funStar-agree d n p q w {Vr = L ⊕[ op ] M} h ()
  funStar-agree d n p q w {Vr = Wr ⟨ c ⟩} h (i , r) =
    i , funRel★-agree d n p q w h r
  funStar-agree d n p q w {Vr = M ↑ c} h ()
  funStar-agree d n p q w {Vr = M ↓ c} h ()
  funStar-agree d n p q w {Vr = blame} h ()

  allOnly★-agree : ∀ d n {Φ : Corr Δ Δ′} {A}
      (p : only Φ ⊢ A ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → Φ ⊢ δ ≈ᴸ δ′ → allOnly d n p w δ Vl Vr → allOnly d n p w δ′ Vl Vr
  allOnly★-agree d n {A = A} p w {Vl = Vl} h r e le c =
    ℰᵍ-≡
      (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
        (substᵗ-cong A (exts-cong (δl≡ᴸ (↑ᴵ-respᴸ h e)))))
      refl
      (ℰᵍ-map d _ _
        (λ le′ w″ e′ V V′ →
          𝒱≤★-agree d (≤′-trans le′ le) p w″
            (↑ᴵ-respᴸ (extOnlyI-respᴸ ≈ˡ-refl (↑ᴵ-respᴸ h e)) e′))
        (r e le c))

  allDead-agree : ∀ d n {Φ : Corr Δ Δ′} {A}
      (p : dead Φ ⊢ A ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → Φ ⊢ δ ≈ᴸ δ′ → allDead d n p w δ Vl Vr → allDead d n p w δ′ Vl Vr
  allDead-agree d n {A = A} p w {Vl = Vl} h r e le T T′ =
    ℰᵍ-≡
      (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ T ])
        (substᵗ-cong A (exts-cong (δl≡ᴸ (↑ᴵ-respᴸ h e)))))
      refl
      (ℰᵍ-map d _ _
        (λ le′ w″ e′ V V′ →
          𝒱≤★-agree d (≤′-trans le′ le) p w″
            (↑ᴵ-respᴸ (extDeadI-respᴸ (↑ᴵ-respᴸ h e)) e′))
        (r e le T T′))

  allDeadStar-agree : ∀ d n {Φ : Corr Δ Δ′} {A}
      (p : dead Φ ⊢ A ⊑ ★) w
      {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → Φ ⊢ δ ≈ᴸ δ′ → allDeadStar d n p w δ Vl Vr
    → allDeadStar d n p w δ′ Vl Vr
  allDeadStar-agree d n p w {Vr = ` x} h ()
  allDeadStar-agree d n p w {Vr = ƛ M} h ()
  allDeadStar-agree d n p w {Vr = L · M} h ()
  allDeadStar-agree d n p w {Vr = Λ M} h ()
  allDeadStar-agree d n p w {Vr = L ⦂∀ C [ T ]} h ()
  allDeadStar-agree d n p w {Vr = $ κ} h ()
  allDeadStar-agree d n p w {Vr = L ⊕[ op ] M} h ()
  allDeadStar-agree d n p w {Vr = Wr ⟨ c ⟩} h (i , r) =
    i , allDead-agree d n p w h r
  allDeadStar-agree d n p w {Vr = M ↑ c} h ()
  allDeadStar-agree d n p w {Vr = M ↓ c} h ()
  allDeadStar-agree d n p w {Vr = blame} h ()
