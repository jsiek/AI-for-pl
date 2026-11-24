module proof.LR.Expression where

-- File Charter:
--   * Expression lemmas (notes/logrel-dgg.md, Section 6.9, item 3).
--   * Related values are related expressions; blame on the left is
--     related to anything.
--   * Backward reduction: if the two sides reduce, and the results are
--     related at the world of those reductions (its right scope given by
--     the right run's `Steps`), then the originals are related, at a
--     stage larger by the counted side's steps.
--   * The bind lemma: related expressions under evaluation frames whose
--     plugs are related at every related pair of values (`ℰᵍ-bind₂` for
--     any value relation).
--   * Typed right terms: typing moves to futures (`Typedᴿ-mono`); the
--     values a typed right term runs to are typed at the arrival
--     (`ℰᵍ-typed`, by preservation); the bind lemma with typed plugs
--     (`ℰ-bind₂ᵀ`).

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n; _≤′_;
  ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤⇒≤′; ≤′⇒≤; +-assoc; m≤n+m;
  +-monoʳ-<)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import CastTerms using (Term; Value; blame; renameᵗᵐ; _⊢_⦂_;
  ⟨_,_,_⟩)
open import TyStore using (TyStore)
open import Reduction using (StoreChange; StoreChanges; []; _∷_; keep;
  bind; _—↠[_]_; ↠-refl; ↠-step; _—→_; pure-step; applyStores; applyTy;
  applyTys)
open import proof.TypeInTermSubst using (typing-renameᵗ; renameᵗ-wk-eq)
open import proof.TypeSafety.Preservation using (multi-preservation)
open import proof.Reduction using (_++χ_; composeReduction)
open import proof.DGG.CenterRename using (_∘↪_)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Steps
open import LR.Relation
open import LR.Frame
open import proof.LR.WorldProps
open import proof.LR.InterpProps
open import proof.LR.Monotone using (𝒱≤-cast; CohE-ty)
open import proof.LR.FrameProps

------------------------------------------------------------------------
-- The extension made by two reductions
------------------------------------------------------------------------

-- the right run's steps give the new scope and the store's place in it
stepExt : ∀ {w : World} {ΔL₁ ΘR₁ Δ₁}
    (χsL : StoreChanges (ΔL w) ΔL₁) (χsR : StoreChanges (storeR w) ΘR₁)
    {p₁ : Prefix ΘR₁ Δ₁} {ρ : ΔR w ↪ᵗ Δ₁}
  → Steps (pre w) χsR p₁ ρ
  → (tags : TyVar ΔL₁ → Tag ΔL₁ Δ₁)
  → (∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
         ≡ renameTag (embedᶜˢ χsL) ρ (tag w X))
  → mkWorld ΔL₁ Δ₁ tags ΘR₁ p₁ (applyStores χsR (ΣR w)) ⊒ w
stepExt χsL χsR {ρ = ρ} st tags ok =
  ext (embedᶜˢ χsL) ρ (embedᶜˢ χsR) (coh-steps st) (Steps-grows st) ok
    (StoreRen-steps χsR)

------------------------------------------------------------------------
-- Values and blame
------------------------------------------------------------------------

ℰ-value : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → Value Vl → Value Vr → 𝒱 d n p w δ Vl Vr → ℰ d n p w δ Vl Vr
ℰ-value ≺ n p w {δ} {Vl} {Vr} vl vr r =
  inj₂ (inj₂ (zero , n , ≤′-refl , ΔL w , [] , Vl , storeR w , [] , Vr ,
    refl , none , ↠-refl , vl , vr , ΔR w , pre w , id↪ᵗ , done refl ,
    tag w , tags≡ (⊒-refl w) ,
    𝒱-resp ≺ n p w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) r))
ℰ-value ≻ n p w {δ} {Vl} {Vr} vl vr r =
  inj₂ (inj₂ (zero , n , ≤′-refl , ΔL w , [] , Vl , storeR w , [] , Vr ,
    refl , ↠-refl , none , vl , vr , ΔR w , pre w , id↪ᵗ , done refl ,
    tag w , tags≡ (⊒-refl w) ,
    𝒱-resp ≻ n p w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) r))

ℰᵍ-blame : ∀ d n w {VR : VRel n w} {Mr} → ℰᵍ d n w VR blame Mr
ℰᵍ-blame ≺ zero w = inj₁ (ΔL w , [] , blame , none)
ℰᵍ-blame ≺ (suc n) w = inj₂ (inj₁ (zero , ΔL w , [] , s≤s z≤n , none))
ℰᵍ-blame ≻ n w = inj₂ (inj₁ (ΔL w , [] , ↠-refl))

------------------------------------------------------------------------
-- Backward reduction
------------------------------------------------------------------------

-- the value relation at a world with an equal right store
𝒱≤-Σ : ∀ d {n′ n} (le : n′ ≤′ n) {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
    (p : Φ ⊢ A ⊑ A′) {ΔL ΔR Θ} {tags : TyVar ΔL → Tag ΔL ΔR}
    {pr : Prefix Θ ΔR} {Σ Σ′ : TyStore Θ} → Σ ≡ Σ′
  → {δ : Interp Δ Δ′ ΔL ΔR} {Vl : Term ΔL} {Vr : Term Θ}
  → 𝒱≤ d le p (mkWorld ΔL ΔR tags Θ pr Σ) δ Vl Vr
  → 𝒱≤ d le p (mkWorld ΔL ΔR tags Θ pr Σ′) δ Vl Vr
𝒱≤-Σ d le p refl r = r

private
  -- an arrival after the second reductions is an arrival after both
  arrive-back : ∀ d {n₁ n n′} (le₁ : n₁ ≤′ n) {Δ Δ′} {Φ : Corr Δ Δ′}
      {A A′} (p : Φ ⊢ A ⊑ A′) {w : World}
      {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΔL₁ ΘR₁ Δ₁ ΔL₂ ΘR₂}
      {χsL : StoreChanges (ΔL w) ΔL₁} {χsR : StoreChanges (storeR w) ΘR₁}
      {χsL′ : StoreChanges ΔL₁ ΔL₂} {χsR′ : StoreChanges ΘR₁ ΘR₂}
      {p₁ : Prefix ΘR₁ Δ₁} {ρ : ΔR w ↪ᵗ Δ₁}
      (st : Steps (pre w) χsR p₁ ρ)
      (tags : TyVar ΔL₁ → Tag ΔL₁ Δ₁)
      (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
                ≡ renameTag (embedᶜˢ χsL) ρ (tag w X))
      {le : n′ ≤′ n₁} {Vl Vr}
    → Arrive n₁ n′ (mkWorld ΔL₁ Δ₁ tags ΘR₁ p₁ (applyStores χsR (ΣR w)))
        χsL′ χsR′
        (λ le′ w′ e′ → 𝒱≤ d le′ p w′
          ((δ ↑ᴵ stepExt {w = w} χsL χsR st tags ok) ↑ᴵ e′))
        le Vl Vr
    → Arrive n n′ w (χsL ++χ χsL′) (χsR ++χ χsR′)
        (λ le′ w′ e′ → 𝒱≤ d le′ p w′ (δ ↑ᴵ e′))
        (≤′-trans le le₁) Vl Vr
  arrive-back d le₁ p {w} {δ} {ΔL₁} {ΘR₁} {Δ₁} {χsL = χsL} {χsR} {χsL′}
      {χsR′} {p₁} {ρ = ρ} st tags ok {le}
      (Δ₂ , p₂ , ρ′ , st′ , tags′ , ok′ , r) =
    Δ₂ , p₂ , ρ′ ∘↪ ρ , st₂ , tags′ , ok₂ ,
    𝒱≤-cast d le (≤′-trans le le₁) p _
      (𝒱≤-Σ d le p (sym (applyStores-++ χsR χsR′ (ΣR w)))
        (𝒱≤-resp d le p _ h r))
    where
    st₂ = Steps-++ st st′
    e₁ = stepExt {w = w} χsL χsR st tags ok
    e′ = stepExt
      {w = mkWorld ΔL₁ Δ₁ tags ΘR₁ p₁ (applyStores χsR (ΣR w))}
      χsL′ χsR′ st′ tags′ ok′

    ok₂ : ∀ X → tags′ (toRenameᵗ (embedᶜˢ (χsL ++χ χsL′)) X)
      ≡ renameTag (embedᶜˢ (χsL ++χ χsL′)) (ρ′ ∘↪ ρ) (tag w X)
    ok₂ X =
      subst (λ a → tags′ (toRenameᵗ a X) ≡ renameTag a (ρ′ ∘↪ ρ) (tag w X))
        (sym (embedᶜˢ-++ χsL χsL′))
        (tags≡ (⊒-trans e′ e₁) X)

    h : (δ ↑ᴵ e₁) ↑ᴵ e′
      ≈ᴵ δ ↑ᴵ stepExt {w = w} (χsL ++χ χsL′) (χsR ++χ χsR′) st₂ tags′ ok₂
    h = ≈ᴵ-trans (↑ᴵ-trans δ e′ e₁)
          (transportI-≡ (sym (embedᶜˢ-++ χsL χsL′)) refl δ)

-- `≺`: the left takes j counted steps, the right any number
ℰ-anti-≺ : ∀ {j n₁} {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′)
    {w : World} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΔL₁ ΘR₁ Δ₁}
    {Ml : Term (ΔL w)} {Ml′ : Term ΔL₁} {Mr : Term (storeR w)}
    {Mr′ : Term ΘR₁}
    {χsL : StoreChanges (ΔL w) ΔL₁} {χsR : StoreChanges (storeR w) ΘR₁}
    {p₁ : Prefix ΘR₁ Δ₁} {ρ : ΔR w ↪ᵗ Δ₁}
  → Ml —→^ j [ χsL ] Ml′
  → Mr —↠[ χsR ] Mr′
  → (st : Steps (pre w) χsR p₁ ρ)
  → (tags : TyVar ΔL₁ → Tag ΔL₁ Δ₁)
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
            ≡ renameTag (embedᶜˢ χsL) ρ (tag w X))
  → ℰ ≺ n₁ p (mkWorld ΔL₁ Δ₁ tags ΘR₁ p₁ (applyStores χsR (ΣR w)))
      (δ ↑ᴵ stepExt {w = w} χsL χsR st tags ok) Ml′ Mr′
  → ℰ ≺ (j + n₁) p w δ Ml Mr
ℰ-anti-≺ p sl sr st tags ok (inj₁ (Δ″ , χs , N , ss)) =
  inj₁ (Δ″ , _ , N , steps-++ sl ss)
ℰ-anti-≺ {j} p sl sr st tags ok (inj₂ (inj₁ (k , Δ″ , χs , k<n₁ , ss))) =
  inj₂ (inj₁ (j + k , Δ″ , _ , +-monoʳ-< j k<n₁ , steps-++ sl ss))
ℰ-anti-≺ {j} {n₁} p {χsL = χsL} {χsR} sl sr st tags ok
    (inj₂ (inj₂ (k , n′ , le , ΔL₂ , χsL′ , Vl , ΘR₂ , χsR′ , Vr ,
      eq , sl′ , sr′ , vl , vr , a))) =
  inj₂ (inj₂ (j + k , n′ , ≤′-trans le (≤⇒≤′ (m≤n+m n₁ j)) ,
    ΔL₂ , _ , Vl , ΘR₂ , _ , Vr ,
    trans (+-assoc j k n′) (cong (j +_) eq) ,
    steps-++ sl sl′ , composeReduction sr sr′ , vl , vr ,
    arrive-back ≺ (≤⇒≤′ (m≤n+m n₁ j)) p
      {χsL = χsL} {χsR} {χsL′} {χsR′} st tags ok a))

-- `≻`: the right takes j counted steps, the left any number
ℰ-anti-≻ : ∀ {j n₁} {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′)
    {w : World} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΔL₁ ΘR₁ Δ₁}
    {Ml : Term (ΔL w)} {Ml′ : Term ΔL₁} {Mr : Term (storeR w)}
    {Mr′ : Term ΘR₁}
    {χsL : StoreChanges (ΔL w) ΔL₁} {χsR : StoreChanges (storeR w) ΘR₁}
    {p₁ : Prefix ΘR₁ Δ₁} {ρ : ΔR w ↪ᵗ Δ₁}
  → Ml —↠[ χsL ] Ml′
  → Mr —→^ j [ χsR ] Mr′
  → (st : Steps (pre w) χsR p₁ ρ)
  → (tags : TyVar ΔL₁ → Tag ΔL₁ Δ₁)
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
            ≡ renameTag (embedᶜˢ χsL) ρ (tag w X))
  → ℰ ≻ n₁ p (mkWorld ΔL₁ Δ₁ tags ΘR₁ p₁ (applyStores χsR (ΣR w)))
      (δ ↑ᴵ stepExt {w = w} χsL χsR st tags ok) Ml′ Mr′
  → ℰ ≻ (j + n₁) p w δ Ml Mr
ℰ-anti-≻ p sl sr st tags ok (inj₁ (Δ″ , χs , N , ss)) =
  inj₁ (Δ″ , _ , N , steps-++ sr ss)
ℰ-anti-≻ p sl sr st tags ok (inj₂ (inj₁ (Δ″ , χs , b))) =
  inj₂ (inj₁ (Δ″ , _ , composeReduction sl b))
ℰ-anti-≻ {j} {n₁} p {χsL = χsL} {χsR} sl sr st tags ok
    (inj₂ (inj₂ (k , n′ , le , ΔL₂ , χsL′ , Vl , ΘR₂ , χsR′ , Vr ,
      eq , sl′ , sr′ , vl , vr , a))) =
  inj₂ (inj₂ (j + k , n′ , ≤′-trans le (≤⇒≤′ (m≤n+m n₁ j)) ,
    ΔL₂ , _ , Vl , ΘR₂ , _ , Vr ,
    trans (+-assoc j k n′) (cong (j +_) eq) ,
    composeReduction sl sl′ , steps-++ sr sr′ , vl , vr ,
    arrive-back ≻ (≤⇒≤′ (m≤n+m n₁ j)) p
      {χsL = χsL} {χsR} {χsL′} {χsR′} st tags ok a))

------------------------------------------------------------------------
-- Pure steps in the same world
------------------------------------------------------------------------

-- reductions that keep both stores arrive in the same world
keepOk : ∀ (w : World) {χsL : StoreChanges (ΔL w) (ΔL w)}
  → embedᶜˢ χsL ≡ id↪ᵗ
  → ∀ X → tag w (toRenameᵗ (embedᶜˢ χsL) X)
          ≡ renameTag (embedᶜˢ χsL) id↪ᵗ (tag w X)
keepOk w eL rewrite eL = tags≡ (⊒-refl w)

keep≈ : ∀ {w : World} {χsL : StoreChanges (ΔL w) (ΔL w)}
    {χsR : StoreChanges (storeR w) (storeR w)}
    (eL : embedᶜˢ χsL ≡ id↪ᵗ) (st : Steps (pre w) χsR (pre w) id↪ᵗ)
    {Δ Δ′} (δ : Interp Δ Δ′ (ΔL w) (ΔR w))
  → δ ↑ᴵ stepExt {w = w} χsL χsR st (tag w) (keepOk w {χsL} eL) ≈ᴵ δ
keep≈ eL st δ = ≈ᴵ-trans (transportI-≡ eL refl δ) (transportI-id δ)

keep₁ : ∀ {Δ} → embedᶜˢ (keep {Δ} ∷ []) ≡ id↪ᵗ
keep₁ = ∘↪-idʳ id↪ᵗ

-- the stage gained by a step on the left, and on the right
tickL : Dir → ℕ → ℕ
tickL ≺ n = suc n
tickL ≻ n = n

tickR : Dir → ℕ → ℕ
tickR ≺ n = n
tickR ≻ n = suc n

-- one pure step on the left, and on the right
okL : ∀ w → ∀ X → tag w (toRenameᵗ (embedᶜˢ (keep {ΔL w} ∷ [])) X)
  ≡ renameTag (embedᶜˢ (keep ∷ [])) id↪ᵗ (tag w X)
okL w = keepOk w {χsL = keep ∷ []} keep₁

okR : ∀ w → ∀ X → tag w (toRenameᵗ (embedᶜˢ ([] {ΔL w})) X)
  ≡ renameTag (embedᶜˢ []) id↪ᵗ (tag w X)
okR w = keepOk w {χsL = []} refl

ℰ-stepL : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Ml′ Mr}
  → Ml —→ Ml′ → ℰ d n p w δ Ml′ Mr → ℰ d (tickL d n) p w δ Ml Mr
ℰ-stepL ≺ n p w {δ} s r =
  ℰ-anti-≺ p (more (pure-step s) none) ↠-refl (done refl) (tag w) (okL w)
    (ℰ-resp ≺ n p w
      (≈ᴵ-sym (keep≈ {w = w} {χsL = keep ∷ []} {χsR = []} keep₁
        (done refl) δ)) r)
ℰ-stepL ≻ n p w {δ} s r =
  ℰ-anti-≻ p (↠-step (pure-step s) ↠-refl) none (done refl) (tag w)
    (okL w)
    (ℰ-resp ≻ n p w
      (≈ᴵ-sym (keep≈ {w = w} {χsL = keep ∷ []} {χsR = []} keep₁
        (done refl) δ)) r)

ℰ-stepR : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr Mr′}
  → Mr —→ Mr′ → ℰ d n p w δ Ml Mr′ → ℰ d (tickR d n) p w δ Ml Mr
ℰ-stepR ≺ n p w {δ} s r =
  ℰ-anti-≺ p none (↠-step (pure-step s) ↠-refl) (Steps-keep (pre w))
    (tag w) (okR w)
    (ℰ-resp ≺ n p w
      (≈ᴵ-sym (keep≈ {w = w} {χsL = []} {χsR = keep ∷ []} refl
        (Steps-keep (pre w)) δ)) r)
ℰ-stepR ≻ n p w {δ} s r =
  ℰ-anti-≻ p ↠-refl (more (pure-step s) none) (Steps-keep (pre w))
    (tag w) (okR w)
    (ℰ-resp ≻ n p w
      (≈ᴵ-sym (keep≈ {w = w} {χsL = []} {χsR = keep ∷ []} refl
        (Steps-keep (pre w)) δ)) r)

------------------------------------------------------------------------
-- The bind lemma
------------------------------------------------------------------------

-- a frame, or none (a side that does not move)
MFrame : TyCtx → Set
MFrame Δ = Maybe (Frame Δ)

mplug : ∀ {Δ} → MFrame Δ → Term Δ → Term Δ
mplug nothing M = M
mplug (just F) M = plug F M

renameMFrame : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → MFrame Δ → MFrame Δ′
renameMFrame ρ nothing = nothing
renameMFrame ρ (just F) = just (renameFrame ρ F)

mframe-steps : ∀ {Δ Δ′ k} {M : Term Δ} {N : Term Δ′}
    {χs : StoreChanges Δ Δ′} (F : MFrame Δ)
  → M —→^ k [ χs ] N
  → mplug F M —→^ k [ χs ] mplug (renameMFrame (embedᶜˢ χs) F) N
mframe-steps nothing ss = ss
mframe-steps (just F) ss = frame-steps F ss

mframe-↠ : ∀ {Δ Δ′} {M : Term Δ} {N : Term Δ′} {χs : StoreChanges Δ Δ′}
    (F : MFrame Δ)
  → M —↠[ χs ] N
  → mplug F M —↠[ χs ] mplug (renameMFrame (embedᶜˢ χs) F) N
mframe-↠ nothing ss = ss
mframe-↠ (just F) ss = frame-↠ F ss

-- the inside is related by VR, and the plugs at q under δ₂
ℰᵍ-bind₂ : ∀ d n w {VR : VRel n w} {Δ₂ Δ₂′} {Φ₂ : Corr Δ₂ Δ₂′}
    {B B′} (q : Φ₂ ⊢ B ⊑ B′) {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    (Fl : MFrame (ΔL w)) (Fr : MFrame (storeR w)) {Ml Mr}
  → ℰᵍ d n w VR Ml Mr
  → (∀ {w′} (e : w′ ⊒ w) {n′} (le : n′ ≤′ n) → ∀ {Vl Vr}
       → Value Vl → Value Vr → VR le w′ e Vl Vr
       → ℰ d n′ q w′ (δ₂ ↑ᴵ e)
           (mplug (renameMFrame (ρL e) Fl) Vl)
           (mplug (renameMFrame (ρS e) Fr) Vr))
  → ℰ d n q w δ₂ (mplug Fl Ml) (mplug Fr Mr)
ℰᵍ-bind₂ ≺ n w q Fl Fr (inj₁ (Δ″ , χs , N , ss)) K =
  inj₁ (Δ″ , χs , _ , mframe-steps Fl ss)
ℰᵍ-bind₂ ≺ n w q nothing Fr (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))) K =
  inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))
ℰᵍ-bind₂ ≺ n w q (just Fl) Fr (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))) K
    with ≤⇒≤′ k<n
ℰᵍ-bind₂ ≺ n w q (just Fl) Fr (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))) K
    | ≤′-refl =
  inj₁ (Δ″ , _ , blame , steps-snoc (frame-steps Fl ss) (frame-blame _))
ℰᵍ-bind₂ ≺ n w q (just Fl) Fr (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))) K
    | ≤′-step lt =
  inj₂ (inj₁ (suc k , Δ″ , _ , s≤s (≤′⇒≤ lt) ,
    steps-snoc (frame-steps Fl ss) (frame-blame _)))
ℰᵍ-bind₂ ≺ n w q {δ₂} Fl Fr {Ml} {Mr}
    (inj₂ (inj₂ (k , n′ , le , ΔL₁ , χsL , Vl , ΘR₁ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r))) K =
  subst (λ m → ℰ ≺ m q w δ₂ (mplug Fl Ml) (mplug Fr Mr)) eq
    (ℰ-anti-≺ q (mframe-steps Fl sl) (mframe-↠ Fr sr) st tags ok
      (K (stepExt {w = w} χsL χsR st tags ok) le vl vr r))
ℰᵍ-bind₂ ≻ n w q Fl Fr (inj₁ (Δ″ , χs , N , ss)) K =
  inj₁ (Δ″ , χs , _ , mframe-steps Fr ss)
ℰᵍ-bind₂ ≻ n w q nothing Fr (inj₂ (inj₁ (Δ″ , χs , b))) K =
  inj₂ (inj₁ (Δ″ , χs , b))
ℰᵍ-bind₂ ≻ n w q (just Fl) Fr (inj₂ (inj₁ (Δ″ , χs , b))) K =
  inj₂ (inj₁ (Δ″ , _ ,
    composeReduction (frame-↠ Fl b) (↠-step (frame-blame _) ↠-refl)))
ℰᵍ-bind₂ ≻ n w q {δ₂} Fl Fr {Ml} {Mr}
    (inj₂ (inj₂ (k , n′ , le , ΔL₁ , χsL , Vl , ΘR₁ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r))) K =
  subst (λ m → ℰ ≻ m q w δ₂ (mplug Fl Ml) (mplug Fr Mr)) eq
    (ℰ-anti-≻ q (mframe-↠ Fl sl) (mframe-steps Fr sr) st tags ok
      (K (stepExt {w = w} χsL χsR st tags ok) le vl vr r))

-- the inside is related at p under δ₁, and the plugs at q under δ₂
ℰ-bind₂ : ∀ d n {Δ₁ Δ₁′ Δ₂ Δ₂′} {Φ₁ : Corr Δ₁ Δ₁′} {Φ₂ : Corr Δ₂ Δ₂′}
    {A A′ B B′} (p : Φ₁ ⊢ A ⊑ A′) (q : Φ₂ ⊢ B ⊑ B′) w
    {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)} {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    (Fl : MFrame (ΔL w)) (Fr : MFrame (storeR w)) {Ml Mr}
  → ℰ d n p w δ₁ Ml Mr
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → ∀ {Vl Vr}
       → Value Vl → Value Vr → 𝒱 d n′ p w′ (δ₁ ↑ᴵ e) Vl Vr
       → ℰ d n′ q w′ (δ₂ ↑ᴵ e)
           (mplug (renameMFrame (ρL e) Fl) Vl)
           (mplug (renameMFrame (ρS e) Fr) Vr))
  → ℰ d n q w δ₂ (mplug Fl Ml) (mplug Fr Mr)
ℰ-bind₂ d n p q w Fl Fr r K =
  ℰᵍ-bind₂ d n w q Fl Fr r
    (λ e le vl vr a → K e (≤′⇒≤ le) vl vr (𝒱≤-cast d le ≤′-refl p _ a))

------------------------------------------------------------------------
-- Typed right terms
------------------------------------------------------------------------

-- the type of a run's result is the type, renamed along the run
applyTy-ren : ∀ {Θ Θ′} (χ : StoreChange Θ Θ′) (A : Ty Θ)
  → applyTy χ A ≡ renameᵗ (toRenameᵗ (LR.Steps.embedᶜ χ)) A
applyTy-ren keep A = sym (renameTy-id A)
applyTy-ren (bind B) A = sym (renameᵗ-wk-eq A)

applyTys-ren : ∀ {Θ Θ′} (χs : StoreChanges Θ Θ′) (A : Ty Θ)
  → applyTys χs A ≡ renameᵗ (toRenameᵗ (embedᶜˢ χs)) A
applyTys-ren [] A = sym (renameTy-id A)
applyTys-ren (χ ∷ χs) A =
  trans (applyTys-ren χs (applyTy χ A))
    (trans (cong (renameᵗ (toRenameᵗ (embedᶜˢ χs))) (applyTy-ren χ A))
      (renameTy-∘ (embedᶜˢ χs) (LR.Steps.embedᶜ χ) A))

-- a typed right term stays typed in a future
Typedᴿ-mono : ∀ {w w′ : World} (e : w′ ⊒ w) {T M}
  → Typedᴿ w T M
  → Typedᴿ w′ (renameᵗ (toRenameᵗ (ρR e)) T) (renameᵗᵐ (ρS e) M)
Typedᴿ-mono e (typedᴿ T₀ refl t) =
  typedᴿ (renameᵗ (toRenameᵗ (ρS e)) T₀) (CohE-ty (coh e) T₀)
    (typing-renameᵗ (ΣR⊒ e) t)

-- the right's result is typed at the arrival (preservation)
arriveTyped : ∀ (w : World) (T : Ty (ΔR w)) {ΔL′ Δ′ ΘR′}
    {tags : TyVar ΔL′ → Tag ΔL′ Δ′}
    {χsR : StoreChanges (storeR w) ΘR′} {p′ : Prefix ΘR′ Δ′} {ρ}
    {Mr Vr}
  → Typedᴿ w T Mr → Mr —↠[ χsR ] Vr → Steps (pre w) χsR p′ ρ
  → Typedᴿ (mkWorld ΔL′ Δ′ tags ΘR′ p′ (applyStores χsR (ΣR w)))
      (renameᵗ (toRenameᵗ ρ) T) Vr
arriveTyped w T {χsR = χsR} {Vr = Vr} (typedᴿ T₀ refl t) sr st =
  typedᴿ (renameᵗ (toRenameᵗ (embedᶜˢ χsR)) T₀)
    (CohE-ty (coh-steps st) T₀)
    (subst (λ A → ⟨ _ , applyStores χsR (ΣR w) , _ ⟩ ⊢ Vr ⦂ A)
      (applyTys-ren χsR T₀) (multi-preservation t sr))

-- the values a typed right term reaches are typed
ℰᵍ-typed : ∀ d n w {VR : VRel n w} (T : Ty (ΔR w)) {Ml Mr}
  → Typedᴿ w T Mr → ℰᵍ d n w VR Ml Mr
  → ℰᵍ d n w (λ le w′ e V V′ → VR le w′ e V V′
       × Typedᴿ w′ (renameᵗ (toRenameᵗ (ρR e)) T) V′) Ml Mr
ℰᵍ-typed ≺ n w T t (inj₁ r) = inj₁ r
ℰᵍ-typed ≺ n w T t (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
ℰᵍ-typed ≺ n w T t
    (inj₂ (inj₂ (k , n′ , le , ΔL₁ , χsL , Vl , ΘR₁ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r))) =
  inj₂ (inj₂ (k , n′ , le , ΔL₁ , χsL , Vl , ΘR₁ , χsR , Vr ,
    eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r ,
    arriveTyped w T t sr st))
ℰᵍ-typed ≻ n w T t (inj₁ r) = inj₁ r
ℰᵍ-typed ≻ n w T t (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
ℰᵍ-typed ≻ n w T t
    (inj₂ (inj₂ (k , n′ , le , ΔL₁ , χsL , Vl , ΘR₁ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r))) =
  inj₂ (inj₂ (k , n′ , le , ΔL₁ , χsL , Vl , ΘR₁ , χsR , Vr ,
    eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r ,
    arriveTyped w T t (steps→↠ sr) st))

-- the bind lemma, with the inside's right term typed: the plugs see
-- typed values
ℰ-bind₂ᵀ : ∀ d n {Δ₁ Δ₁′ Δ₂ Δ₂′} {Φ₁ : Corr Δ₁ Δ₁′} {Φ₂ : Corr Δ₂ Δ₂′}
    {A A′ B B′} (p : Φ₁ ⊢ A ⊑ A′) (q : Φ₂ ⊢ B ⊑ B′) w
    {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)} {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    (Fl : MFrame (ΔL w)) (Fr : MFrame (storeR w)) {Ml Mr}
  → Typedᴿ w (substᵗ (δr δ₁) A′) Mr
  → ℰ d n p w δ₁ Ml Mr
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → ∀ {Vl Vr}
       → Value Vl → Value Vr → 𝒱 d n′ p w′ (δ₁ ↑ᴵ e) Vl Vr
       → Typedᴿ w′ (substᵗ (δr (δ₁ ↑ᴵ e)) A′) Vr
       → ℰ d n′ q w′ (δ₂ ↑ᴵ e)
           (mplug (renameMFrame (ρL e) Fl) Vl)
           (mplug (renameMFrame (ρS e) Fr) Vr))
  → ℰ d n q w δ₂ (mplug Fl Ml) (mplug Fr Mr)
ℰ-bind₂ᵀ d n {A′ = A′} p q w {δ₁} Fl Fr t r K =
  ℰᵍ-bind₂ d n w q Fl Fr (ℰᵍ-typed d n w (substᵗ (δr δ₁) A′) t r)
    (λ e le vl vr (a , tv) →
      K e (≤′⇒≤ le) vl vr (𝒱≤-cast d le ≤′-refl p _ a)
        (Typedᴿ-≡ (renameᵗ-subst (toRenameᵗ (ρR e)) (δr δ₁) A′) tv))

ℰ-bind : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′ B B′}
    (p : Φ ⊢ A ⊑ A′) (q : Φ ⊢ B ⊑ B′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    (Fl : Frame (ΔL w)) (Fr : Frame (storeR w)) {Ml Mr}
  → ℰ d n p w δ Ml Mr
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → ∀ {Vl Vr}
       → Value Vl → Value Vr → 𝒱 d n′ p w′ (δ ↑ᴵ e) Vl Vr
       → ℰ d n′ q w′ (δ ↑ᴵ e)
           (plug (renameFrame (ρL e) Fl) Vl)
           (plug (renameFrame (ρS e) Fr) Vr))
  → ℰ d n q w δ (plug Fl Ml) (plug Fr Mr)
ℰ-bind d n p q w Fl Fr r K = ℰ-bind₂ d n p q w (just Fl) (just Fr) r K
