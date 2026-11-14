module proof.LR.Expression where

-- File Charter:
--   * Expression lemmas (notes/logrel-dgg.md, Section 6.9, item 3).
--   * Related values are related expressions; blame on the left is
--     related to anything.
--   * Backward reduction: if the two sides reduce, and the results are
--     related at the world of those reductions, then the originals are
--     related, at a stage larger by the counted side's steps.
--   * The bind lemma: related expressions under evaluation frames whose
--     plugs are related at every related pair of values.

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n; _≤′_;
  ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤⇒≤′; ≤′⇒≤; +-assoc; m≤n+m;
  +-monoʳ-<)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import CastTerms using (Term; Value; blame)
open import Reduction using (StoreChanges; []; _∷_; keep; _—↠[_]_;
  ↠-refl; ↠-step; _—→_; pure-step)
open import proof.Reduction using (_++χ_; composeReduction)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Steps
open import LR.Relation
open import LR.Frame
open import proof.LR.WorldProps
open import proof.LR.InterpProps
open import proof.LR.Monotone using (𝒱≤-cast)
open import proof.LR.FrameProps

------------------------------------------------------------------------
-- The extension made by two reductions
------------------------------------------------------------------------

stepExt : ∀ {w : World} {ΔL₁ ΔR₁}
    (χsL : StoreChanges (ΔL w) ΔL₁) (χsR : StoreChanges (ΔR w) ΔR₁)
    (tags : TyVar ΔL₁ → Tag ΔL₁ ΔR₁)
  → (∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
         ≡ renameTag (embedᶜˢ χsL) (embedᶜˢ χsR) (tag w X))
  → world ΔL₁ ΔR₁ tags ⊒ w
stepExt χsL χsR tags ok = ext (embedᶜˢ χsL) (embedᶜˢ χsR) ok

------------------------------------------------------------------------
-- Values and blame
------------------------------------------------------------------------

ℰ-value : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → Value Vl → Value Vr → 𝒱 d n p w δ Vl Vr → ℰ d n p w δ Vl Vr
ℰ-value ≺ n p w {δ} {Vl} {Vr} vl vr r =
  inj₂ (inj₂ (zero , n , ≤′-refl , ΔL w , [] , Vl , ΔR w , [] , Vr ,
    refl , none , ↠-refl , vl , vr , tag w , tags≡ (⊒-refl w) ,
    𝒱-resp ≺ n p w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) r))
ℰ-value ≻ n p w {δ} {Vl} {Vr} vl vr r =
  inj₂ (inj₂ (zero , n , ≤′-refl , ΔL w , [] , Vl , ΔR w , [] , Vr ,
    refl , ↠-refl , none , vl , vr , tag w , tags≡ (⊒-refl w) ,
    𝒱-resp ≻ n p w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) r))

ℰᵍ-blame : ∀ d n w {VR : VRel n w} {Mr} → ℰᵍ d n w VR blame Mr
ℰᵍ-blame ≺ zero w = inj₁ (ΔL w , [] , blame , none)
ℰᵍ-blame ≺ (suc n) w = inj₂ (inj₁ (zero , ΔL w , [] , s≤s z≤n , none))
ℰᵍ-blame ≻ n w = inj₂ (inj₁ (ΔL w , [] , ↠-refl))

------------------------------------------------------------------------
-- Backward reduction
------------------------------------------------------------------------

private
  -- an arrival after the second reductions is an arrival after both
  arrive-back : ∀ d {n₁ n n′} (le₁ : n₁ ≤′ n) {Δ Δ′} {Φ : Corr Δ Δ′}
      {A A′} (p : Φ ⊢ A ⊑ A′) {w : World}
      {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΔL₁ ΔR₁ ΔL₂ ΔR₂}
      {χsL : StoreChanges (ΔL w) ΔL₁} {χsR : StoreChanges (ΔR w) ΔR₁}
      {χsL′ : StoreChanges ΔL₁ ΔL₂} {χsR′ : StoreChanges ΔR₁ ΔR₂}
      (tags : TyVar ΔL₁ → Tag ΔL₁ ΔR₁)
      (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
                ≡ renameTag (embedᶜˢ χsL) (embedᶜˢ χsR) (tag w X))
      {le : n′ ≤′ n₁} {Vl Vr}
    → Arrive n₁ n′ (world ΔL₁ ΔR₁ tags) χsL′ χsR′
        (λ le′ w′ e′ → 𝒱≤ d le′ p w′
          ((δ ↑ᴵ stepExt χsL χsR tags ok) ↑ᴵ e′))
        le Vl Vr
    → Arrive n n′ w (χsL ++χ χsL′) (χsR ++χ χsR′)
        (λ le′ w′ e′ → 𝒱≤ d le′ p w′ (δ ↑ᴵ e′))
        (≤′-trans le le₁) Vl Vr
  arrive-back d le₁ p {w} {δ} {χsL = χsL} {χsR} {χsL′} {χsR′} tags ok
      {le} (tags′ , ok′ , r) =
    tags′ , ok₂ , 𝒱≤-cast d le (≤′-trans le le₁) p _ (𝒱≤-resp d le p _ h r)
    where
    e₁ = stepExt χsL χsR tags ok
    e′ = stepExt χsL′ χsR′ tags′ ok′

    ok₂ : ∀ X → tags′ (toRenameᵗ (embedᶜˢ (χsL ++χ χsL′)) X)
      ≡ renameTag (embedᶜˢ (χsL ++χ χsL′)) (embedᶜˢ (χsR ++χ χsR′))
          (tag w X)
    ok₂ X =
      subst₂ (λ a b → tags′ (toRenameᵗ a X) ≡ renameTag a b (tag w X))
        (sym (embedᶜˢ-++ χsL χsL′)) (sym (embedᶜˢ-++ χsR χsR′))
        (tags≡ (⊒-trans e′ e₁) X)

    h : (δ ↑ᴵ e₁) ↑ᴵ e′
      ≈ᴵ δ ↑ᴵ stepExt (χsL ++χ χsL′) (χsR ++χ χsR′) tags′ ok₂
    h = ≈ᴵ-trans (↑ᴵ-trans δ e′ e₁)
          (transportI-≡ (sym (embedᶜˢ-++ χsL χsL′))
            (sym (embedᶜˢ-++ χsR χsR′)) δ)

-- `≺`: the left takes j counted steps, the right any number
ℰ-anti-≺ : ∀ {j n₁} {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′)
    {w : World} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΔL₁ ΔR₁}
    {Ml : Term (ΔL w)} {Ml′ : Term ΔL₁} {Mr : Term (ΔR w)}
    {Mr′ : Term ΔR₁}
    {χsL : StoreChanges (ΔL w) ΔL₁} {χsR : StoreChanges (ΔR w) ΔR₁}
  → Ml —→^ j [ χsL ] Ml′
  → Mr —↠[ χsR ] Mr′
  → (tags : TyVar ΔL₁ → Tag ΔL₁ ΔR₁)
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
            ≡ renameTag (embedᶜˢ χsL) (embedᶜˢ χsR) (tag w X))
  → ℰ ≺ n₁ p (world ΔL₁ ΔR₁ tags)
      (δ ↑ᴵ stepExt χsL χsR tags ok) Ml′ Mr′
  → ℰ ≺ (j + n₁) p w δ Ml Mr
ℰ-anti-≺ p sl sr tags ok (inj₁ (Δ″ , χs , N , ss)) =
  inj₁ (Δ″ , _ , N , steps-++ sl ss)
ℰ-anti-≺ {j} p sl sr tags ok (inj₂ (inj₁ (k , Δ″ , χs , k<n₁ , ss))) =
  inj₂ (inj₁ (j + k , Δ″ , _ , +-monoʳ-< j k<n₁ , steps-++ sl ss))
ℰ-anti-≺ {j} {n₁} p {χsL = χsL} {χsR} sl sr tags ok
    (inj₂ (inj₂ (k , n′ , le , ΔL₂ , χsL′ , Vl , ΔR₂ , χsR′ , Vr ,
      eq , sl′ , sr′ , vl , vr , a))) =
  inj₂ (inj₂ (j + k , n′ , ≤′-trans le (≤⇒≤′ (m≤n+m n₁ j)) ,
    ΔL₂ , _ , Vl , ΔR₂ , _ , Vr ,
    trans (+-assoc j k n′) (cong (j +_) eq) ,
    steps-++ sl sl′ , composeReduction sr sr′ , vl , vr ,
    arrive-back ≺ (≤⇒≤′ (m≤n+m n₁ j)) p
      {χsL = χsL} {χsR} {χsL′} {χsR′} tags ok a))

-- `≻`: the right takes j counted steps, the left any number
ℰ-anti-≻ : ∀ {j n₁} {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′)
    {w : World} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΔL₁ ΔR₁}
    {Ml : Term (ΔL w)} {Ml′ : Term ΔL₁} {Mr : Term (ΔR w)}
    {Mr′ : Term ΔR₁}
    {χsL : StoreChanges (ΔL w) ΔL₁} {χsR : StoreChanges (ΔR w) ΔR₁}
  → Ml —↠[ χsL ] Ml′
  → Mr —→^ j [ χsR ] Mr′
  → (tags : TyVar ΔL₁ → Tag ΔL₁ ΔR₁)
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
            ≡ renameTag (embedᶜˢ χsL) (embedᶜˢ χsR) (tag w X))
  → ℰ ≻ n₁ p (world ΔL₁ ΔR₁ tags)
      (δ ↑ᴵ stepExt χsL χsR tags ok) Ml′ Mr′
  → ℰ ≻ (j + n₁) p w δ Ml Mr
ℰ-anti-≻ p sl sr tags ok (inj₁ (Δ″ , χs , N , ss)) =
  inj₁ (Δ″ , _ , N , steps-++ sr ss)
ℰ-anti-≻ p sl sr tags ok (inj₂ (inj₁ (Δ″ , χs , b))) =
  inj₂ (inj₁ (Δ″ , _ , composeReduction sl b))
ℰ-anti-≻ {j} {n₁} p {χsL = χsL} {χsR} sl sr tags ok
    (inj₂ (inj₂ (k , n′ , le , ΔL₂ , χsL′ , Vl , ΔR₂ , χsR′ , Vr ,
      eq , sl′ , sr′ , vl , vr , a))) =
  inj₂ (inj₂ (j + k , n′ , ≤′-trans le (≤⇒≤′ (m≤n+m n₁ j)) ,
    ΔL₂ , _ , Vl , ΔR₂ , _ , Vr ,
    trans (+-assoc j k n′) (cong (j +_) eq) ,
    composeReduction sl sl′ , steps-++ sr sr′ , vl , vr ,
    arrive-back ≻ (≤⇒≤′ (m≤n+m n₁ j)) p
      {χsL = χsL} {χsR} {χsL′} {χsR′} tags ok a))

------------------------------------------------------------------------
-- Pure steps in the same world
------------------------------------------------------------------------

-- reductions that keep both stores arrive in the same world
keepOk : ∀ (w : World) {χsL : StoreChanges (ΔL w) (ΔL w)}
    {χsR : StoreChanges (ΔR w) (ΔR w)}
  → embedᶜˢ χsL ≡ id↪ᵗ → embedᶜˢ χsR ≡ id↪ᵗ
  → ∀ X → tag w (toRenameᵗ (embedᶜˢ χsL) X)
          ≡ renameTag (embedᶜˢ χsL) (embedᶜˢ χsR) (tag w X)
keepOk w eL eR rewrite eL | eR = tags≡ (⊒-refl w)

keep≈ : ∀ {w : World} {χsL : StoreChanges (ΔL w) (ΔL w)}
    {χsR : StoreChanges (ΔR w) (ΔR w)}
    (eL : embedᶜˢ χsL ≡ id↪ᵗ) (eR : embedᶜˢ χsR ≡ id↪ᵗ)
    {Δ Δ′} (δ : Interp Δ Δ′ (ΔL w) (ΔR w))
  → δ ↑ᴵ stepExt χsL χsR (tag w) (keepOk w {χsL} {χsR} eL eR) ≈ᴵ δ
keep≈ eL eR δ = ≈ᴵ-trans (transportI-≡ eL eR δ) (transportI-id δ)

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
  ≡ renameTag (embedᶜˢ (keep ∷ [])) (embedᶜˢ ([] {ΔR w})) (tag w X)
okL w = keepOk w {χsL = keep ∷ []} {χsR = []} keep₁ refl

okR : ∀ w → ∀ X → tag w (toRenameᵗ (embedᶜˢ ([] {ΔL w})) X)
  ≡ renameTag (embedᶜˢ []) (embedᶜˢ (keep {ΔR w} ∷ [])) (tag w X)
okR w = keepOk w {χsL = []} {χsR = keep ∷ []} refl keep₁

ℰ-stepL : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Ml′ Mr}
  → Ml —→ Ml′ → ℰ d n p w δ Ml′ Mr → ℰ d (tickL d n) p w δ Ml Mr
ℰ-stepL ≺ n p w {δ} s r =
  ℰ-anti-≺ p (more (pure-step s) none) ↠-refl (tag w) (okL w)
    (ℰ-resp ≺ n p w
      (≈ᴵ-sym (keep≈ {w = w} {χsL = keep ∷ []} {χsR = []} keep₁ refl δ)) r)
ℰ-stepL ≻ n p w {δ} s r =
  ℰ-anti-≻ p (↠-step (pure-step s) ↠-refl) none (tag w) (okL w)
    (ℰ-resp ≻ n p w
      (≈ᴵ-sym (keep≈ {w = w} {χsL = keep ∷ []} {χsR = []} keep₁ refl δ)) r)

ℰ-stepR : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr Mr′}
  → Mr —→ Mr′ → ℰ d n p w δ Ml Mr′ → ℰ d (tickR d n) p w δ Ml Mr
ℰ-stepR ≺ n p w {δ} s r =
  ℰ-anti-≺ p none (↠-step (pure-step s) ↠-refl) (tag w) (okR w)
    (ℰ-resp ≺ n p w
      (≈ᴵ-sym (keep≈ {w = w} {χsL = []} {χsR = keep ∷ []} refl keep₁ δ)) r)
ℰ-stepR ≻ n p w {δ} s r =
  ℰ-anti-≻ p ↠-refl (more (pure-step s) none) (tag w) (okR w)
    (ℰ-resp ≻ n p w
      (≈ᴵ-sym (keep≈ {w = w} {χsL = []} {χsR = keep ∷ []} refl keep₁ δ)) r)

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

-- the inside is related at p under δ₁, and the plugs at q under δ₂
ℰ-bind₂ : ∀ d n {Δ₁ Δ₁′ Δ₂ Δ₂′} {Φ₁ : Corr Δ₁ Δ₁′} {Φ₂ : Corr Δ₂ Δ₂′}
    {A A′ B B′} (p : Φ₁ ⊢ A ⊑ A′) (q : Φ₂ ⊢ B ⊑ B′) w
    {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)} {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    (Fl : MFrame (ΔL w)) (Fr : MFrame (ΔR w)) {Ml Mr}
  → ℰ d n p w δ₁ Ml Mr
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → ∀ {Vl Vr}
       → Value Vl → Value Vr → 𝒱 d n′ p w′ (δ₁ ↑ᴵ e) Vl Vr
       → ℰ d n′ q w′ (δ₂ ↑ᴵ e)
           (mplug (renameMFrame (ρL e) Fl) Vl)
           (mplug (renameMFrame (ρR e) Fr) Vr))
  → ℰ d n q w δ₂ (mplug Fl Ml) (mplug Fr Mr)
ℰ-bind₂ ≺ n p q w Fl Fr (inj₁ (Δ″ , χs , N , ss)) K =
  inj₁ (Δ″ , χs , _ , mframe-steps Fl ss)
ℰ-bind₂ ≺ n p q w nothing Fr (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))) K =
  inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))
ℰ-bind₂ ≺ n p q w (just Fl) Fr (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))) K
    with ≤⇒≤′ k<n
ℰ-bind₂ ≺ n p q w (just Fl) Fr (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))) K
    | ≤′-refl =
  inj₁ (Δ″ , _ , blame , steps-snoc (frame-steps Fl ss) (frame-blame _))
ℰ-bind₂ ≺ n p q w (just Fl) Fr (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss))) K
    | ≤′-step lt =
  inj₂ (inj₁ (suc k , Δ″ , _ , s≤s (≤′⇒≤ lt) ,
    steps-snoc (frame-steps Fl ss) (frame-blame _)))
ℰ-bind₂ ≺ n p q w {δ₂ = δ₂} Fl Fr {Ml} {Mr}
    (inj₂ (inj₂ (k , n′ , le , ΔL₁ , χsL , Vl , ΔR₁ , χsR , Vr ,
      eq , sl , sr , vl , vr , tags , ok , r))) K =
  subst (λ m → ℰ ≺ m q w δ₂ (mplug Fl Ml) (mplug Fr Mr)) eq
    (ℰ-anti-≺ q (mframe-steps Fl sl) (mframe-↠ Fr sr) tags ok
      (K (stepExt χsL χsR tags ok)
        (subst (n′ ≤_) eq (m≤n+m n′ k)) vl vr
        (𝒱≤-cast ≺ le ≤′-refl p _ r)))
ℰ-bind₂ ≻ n p q w Fl Fr (inj₁ (Δ″ , χs , N , ss)) K =
  inj₁ (Δ″ , χs , _ , mframe-steps Fr ss)
ℰ-bind₂ ≻ n p q w nothing Fr (inj₂ (inj₁ (Δ″ , χs , b))) K =
  inj₂ (inj₁ (Δ″ , χs , b))
ℰ-bind₂ ≻ n p q w (just Fl) Fr (inj₂ (inj₁ (Δ″ , χs , b))) K =
  inj₂ (inj₁ (Δ″ , _ ,
    composeReduction (frame-↠ Fl b) (↠-step (frame-blame _) ↠-refl)))
ℰ-bind₂ ≻ n p q w {δ₂ = δ₂} Fl Fr {Ml} {Mr}
    (inj₂ (inj₂ (k , n′ , le , ΔL₁ , χsL , Vl , ΔR₁ , χsR , Vr ,
      eq , sl , sr , vl , vr , tags , ok , r))) K =
  subst (λ m → ℰ ≻ m q w δ₂ (mplug Fl Ml) (mplug Fr Mr)) eq
    (ℰ-anti-≻ q (mframe-↠ Fl sl) (mframe-steps Fr sr) tags ok
      (K (stepExt χsL χsR tags ok)
        (subst (n′ ≤_) eq (m≤n+m n′ k)) vl vr
        (𝒱≤-cast ≻ le ≤′-refl p _ r)))

ℰ-bind : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′ B B′}
    (p : Φ ⊢ A ⊑ A′) (q : Φ ⊢ B ⊑ B′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    (Fl : Frame (ΔL w)) (Fr : Frame (ΔR w)) {Ml Mr}
  → ℰ d n p w δ Ml Mr
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → ∀ {Vl Vr}
       → Value Vl → Value Vr → 𝒱 d n′ p w′ (δ ↑ᴵ e) Vl Vr
       → ℰ d n′ q w′ (δ ↑ᴵ e)
           (plug (renameFrame (ρL e) Fl) Vl)
           (plug (renameFrame (ρR e) Fr) Vr))
  → ℰ d n q w δ (plug Fl Ml) (plug Fr Mr)
ℰ-bind d n p q w Fl Fr r K = ℰ-bind₂ d n p q w (just Fl) (just Fr) r K
