module proof.LR.ConvLemma where

-- File Charter:
--   * The conversion lemma (notes/logrel-dgg.md, Section 6.9, item 5):
--     a type application's reveal turns values related with the bound
--     variable as a store variable (sealed values) into values related
--     with the variable as its representation (the contents), and the
--     conceal turns them back.
--   * The converted variable X is paired (both sides convert, the right
--     at its own store variable), left-only, or dead (it occurs nowhere,
--     so the conversion never unseals).  Every other variable is a store
--     variable on both sides, read by the same leaf.
--   * Two lemmas, each with a reveal and a conceal half, by induction on
--     the precision derivation:
--       - at derivations into `★` the right side is not converted (a
--         paired variable cannot occur on the left there);
--       - at every other derivation the right converts in the paired
--         mode; at a right type `★` it only takes an identity step, and
--         the first lemma takes over.
--   * The leaves of X are tied by hypotheses with one-sided stage bounds
--     (`SealI`): a sealed value is read below the bound, and a value is
--     sealed below it, except in `≻` for a left-only variable, where
--     the left's steps are not counted and the bound is inclusive.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; s≤s; z≤n;
  _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤⇒≤′; ≤′⇒≤; ≤-trans;
  ≤-<-trans; <⇒≤)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import proof.DGG.CenterRename using (toRenameᵗ-∘)
open import proof.TypeInTermSubst using (toRename-id-eq;
  renameᵗᵐ-preserves-Value)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open import Conversion
open import CastTerms using (Term; `_; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_;
  _⟨_⟩; _↑_; _↓_; blame; Value; RevealValue; ConcealValue; renameᵗᵐ)
import CastTerms as CT
open import Reduction using (_—→_; id-reveal; id-conceal; conceal-reveal;
  β-reveal-⇒; β-conceal-⇒)
open import LR.Frame using (Frame; reveal; conceal; app₂; plug;
  renameFrame)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import proof.LR.WorldProps
open import proof.LR.InterpProps
open import proof.LR.Monotone
open import proof.LR.Expression
open import proof.LR.SubstLemma using (ℰᵍ-zero; _⇔_; to; from; 𝒱-XY; 𝒱-X★)
open import proof.LR.ConvSyntax

private
  variable
    Δ Δ′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- Dead variables, and how variables of different kinds differ
------------------------------------------------------------------------

infix 4 _∋_dead

data _∋_dead : ∀ {Δ Δ′} → Corr Δ Δ′ → TyVar Δ → Set where
  dead-here : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} → dead Φ ∋ zero dead
  dead-pair : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    → Φ ∋ X dead → pair Φ ∋ suc X dead
  dead-only : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    → Φ ∋ X dead → only Φ ∋ suc X dead
  dead-dead : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    → Φ ∋ X dead → dead Φ ∋ suc X dead

↔-functional : ∀ {Φ : Corr Δ Δ′} {X Y Y′}
  → Φ ∋ X ↔ Y → Φ ∋ X ↔ Y′ → Y ≡ Y′
↔-functional ↔-here ↔-here = refl
↔-functional (↔-pair x) (↔-pair y) = cong suc (↔-functional x y)
↔-functional (↔-only x) (↔-only y) = ↔-functional x y
↔-functional (↔-dead x) (↔-dead y) = ↔-functional x y

↔-injective : ∀ {Φ : Corr Δ Δ′} {X X′ Y}
  → Φ ∋ X ↔ Y → Φ ∋ X′ ↔ Y → X ≡ X′
↔-injective ↔-here ↔-here = refl
↔-injective (↔-pair x) (↔-pair y) = cong suc (↔-injective x y)
↔-injective (↔-only x) (↔-only y) = cong suc (↔-injective x y)
↔-injective (↔-dead x) (↔-dead y) = cong suc (↔-injective x y)

↔-only-⊥ : ∀ {Φ : Corr Δ Δ′} {X Y} → Φ ∋ X ↔ Y → Φ ∋ X only → ⊥
↔-only-⊥ ↔-here ()
↔-only-⊥ (↔-pair x) (only-pair y) = ↔-only-⊥ x y
↔-only-⊥ (↔-only x) (only-only y) = ↔-only-⊥ x y
↔-only-⊥ (↔-dead x) (only-dead y) = ↔-only-⊥ x y

↔-dead-⊥ : ∀ {Φ : Corr Δ Δ′} {X Y} → Φ ∋ X ↔ Y → Φ ∋ X dead → ⊥
↔-dead-⊥ ↔-here ()
↔-dead-⊥ (↔-pair x) (dead-pair y) = ↔-dead-⊥ x y
↔-dead-⊥ (↔-only x) (dead-only y) = ↔-dead-⊥ x y
↔-dead-⊥ (↔-dead x) (dead-dead y) = ↔-dead-⊥ x y

only-dead-⊥ : ∀ {Φ : Corr Δ Δ′} {X} → Φ ∋ X only → Φ ∋ X dead → ⊥
only-dead-⊥ only-here ()
only-dead-⊥ (only-pair x) (dead-pair y) = only-dead-⊥ x y
only-dead-⊥ (only-only x) (dead-only y) = only-dead-⊥ x y
only-dead-⊥ (only-dead x) (dead-dead y) = only-dead-⊥ x y

------------------------------------------------------------------------
-- Modes: which variable is converted, and how the right side converts
------------------------------------------------------------------------

data CMode {Δ Δ′} (Φ : Corr Δ Δ′) (X : TyVar Δ) (ΘR : TyCtx) : Set where
  -- paired with Y; the right converts its store variable α′
  m-pair : ∀ {Y} → Φ ∋ X ↔ Y → TyVar ΘR → CMode Φ X ΘR
  m-only : Φ ∋ X only → CMode Φ X ΘR
  m-dead : Φ ∋ X dead → CMode Φ X ΘR

-- the right side's conversion, if any: its store variable and
-- representation
RConv : TyCtx → Set
RConv Θ = Maybe (TyVar Θ × Ty Θ)

-- in a mode, with the right representations given by σ
rconv : ∀ {Φ : Corr Δ Δ′} {X} → CMode Φ X ΘR → (Δ′ ⇒ˢ ΘR) → RConv ΘR
rconv (m-pair {Y = Y} x α′) σ = just (α′ , σ Y)
rconv (m-only x) σ = nothing
rconv (m-dead x) σ = nothing

renRConv : ∀ {Θ Θ′} → Θ ↪ᵗ Θ′ → RConv Θ → RConv Θ′
renRConv ρ nothing = nothing
renRConv ρ (just (α′ , R)) =
  just (toRenameᵗ ρ α′ , renameᵗ (toRenameᵗ ρ) R)

-- the frames of the right side's reveal and conceal at the type B
revFrame : ∀ {Θ} → RConv Θ → Ty Θ → MFrame Θ
revFrame nothing B = nothing
revFrame (just (α′ , R)) B = just (reveal 〖 α′ , R ↑ B 〗)

conFrame : ∀ {Θ} → RConv Θ → Ty Θ → MFrame Θ
conFrame nothing B = nothing
conFrame (just (α′ , R)) B = just (conceal (makeConceal α′ R B))

revM : ∀ {Θ} → RConv Θ → Ty Θ → Term Θ → Term Θ
revM rc B V = mplug (revFrame rc B) V

conM : ∀ {Θ} → RConv Θ → Ty Θ → Term Θ → Term Θ
conM rc B V = mplug (conFrame rc B) V

-- the stages at which a conceal is needed: below N when the counted
-- side converts, up to N otherwise (`≻`, the right not converting)
ConB : ∀ {Θ} → Dir → RConv Θ → ℕ → ℕ → Set
ConB ≺ rc k N = k < N
ConB ≻ nothing k N = k ≤ N
ConB ≻ (just c) k N = k < N

------------------------------------------------------------------------
-- Sealed values
------------------------------------------------------------------------

sealedL : TyVar ΘL → Ty ΘL → (Term ΘL → Term ΘR → Set)
  → Term ΘL → Term ΘR → Set
sealedL α R P (W ↓ s) Vr = IsSeal α R s × P W Vr
sealedL α R P Vl Vr = ⊥

sealedR : TyVar ΘR → Ty ΘR → (Term ΘL → Term ΘR → Set)
  → Term ΘL → Term ΘR → Set
sealedR α R P Vl (W ↓ s) = IsSeal α R s × P Vl W
sealedR α R P Vl Vr = ⊥

sealedL-inv : ∀ {α : TyVar ΘL} {R} {P : Term ΘL → Term ΘR → Set} {Vl Vr}
  → sealedL α R P Vl Vr → Σ[ W ∈ Term ΘL ] (Vl ≡ W ↓ seal α R × P W Vr)
sealedL-inv {Vl = W ↓ seal X R′} ((refl , refl) , r) = W , refl , r
sealedL-inv {Vl = W ↓ (c ↦↓ d)} (() , r)
sealedL-inv {Vl = W ↓ (`∀↓ c)} (() , r)
sealedL-inv {Vl = W ↓ id↓ A} (() , r)
sealedL-inv {Vl = ` x} ()
sealedL-inv {Vl = ƛ M} ()
sealedL-inv {Vl = L · M} ()
sealedL-inv {Vl = Λ M} ()
sealedL-inv {Vl = L ⦂∀ C [ T ]} ()
sealedL-inv {Vl = $ κ} ()
sealedL-inv {Vl = L ⊕[ op ] M} ()
sealedL-inv {Vl = W ⟨ c ⟩} ()
sealedL-inv {Vl = M ↑ c} ()
sealedL-inv {Vl = blame} ()

sealedR-inv : ∀ {α : TyVar ΘR} {R} {P : Term ΘL → Term ΘR → Set} {Vl Vr}
  → sealedR α R P Vl Vr → Σ[ W ∈ Term ΘR ] (Vr ≡ W ↓ seal α R × P Vl W)
sealedR-inv {Vr = W ↓ seal X R′} ((refl , refl) , r) = W , refl , r
sealedR-inv {Vr = W ↓ (c ↦↓ d)} (() , r)
sealedR-inv {Vr = W ↓ (`∀↓ c)} (() , r)
sealedR-inv {Vr = W ↓ id↓ A} (() , r)
sealedR-inv {Vr = ` x} ()
sealedR-inv {Vr = ƛ M} ()
sealedR-inv {Vr = L · M} ()
sealedR-inv {Vr = Λ M} ()
sealedR-inv {Vr = L ⦂∀ C [ T ]} ()
sealedR-inv {Vr = $ κ} ()
sealedR-inv {Vr = L ⊕[ op ] M} ()
sealedR-inv {Vr = W ⟨ c ⟩} ()
sealedR-inv {Vr = M ↑ c} ()
sealedR-inv {Vr = blame} ()

value-sealed : ∀ {W : Term Δ} {A B} {s : Conv↓ Δ A B}
  → Value (W ↓ s) → Value W
value-sealed (v CT.↓ cv) = v

-- the stage of a left-only leaf's contents: one down in `≺`, the same
-- in `≻`
onlyStage : Dir → ℕ → ℕ
onlyStage ≺ k = pred k
onlyStage ≻ k = k

-- the strict bound for sealing, inclusive for a left-only `≻` leaf
onlyBelow : Dir → ℕ → ℕ → Set
onlyBelow ≺ k N = k < N
onlyBelow ≻ k N = k ≤ N

------------------------------------------------------------------------
-- The hypotheses
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  -- the right side: the paired variable is a store variable, every
  -- other one the same store variable on both sides
  RightI : ∀ {ΔL ΔR} → CMode Φ X ΔR → (δs δt : Interp Δ Δ′ ΔL ΔR) → Set
  RightI {ΔR = ΔR} (m-pair {Y = Y} x α′) δs δt =
    δr δs Y ≡ ＇ α′
    × (∀ Y′ → Y′ ≢ Y
         → Σ[ γ ∈ TyVar ΔR ] (δr δs Y′ ≡ ＇ γ × δr δt Y′ ≡ ＇ γ × γ ≢ α′))
  RightI (m-only x) δs δt = ∀ Y′ → δr δs Y′ ≡ δr δt Y′
  RightI (m-dead x) δs δt = ∀ Y′ → δr δs Y′ ≡ δr δt Y′

  -- the leaves of X, in every future: the converted side's leaf (δs)
  -- holds of sealed values, sealed contents related by the other leaf
  -- (δt)
  SealI : Dir → ℕ → (w : World) → CMode Φ X (ΔR w) → TyVar (ΔL w)
    → (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) → Set
  SealI d N w (m-pair {Y = Y} x α′) α δs δt =
    (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X) Vl Vr
       → sealedL (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X)
           (sealedR (toRenameᵗ (ρR e) α′) (δr (δt ↑ᴵ e) Y)
             (leafRel d (pred k) w′ (leaf (δt ↑ᴵ e) X))) Vl Vr)
    × (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k < N → ∀ {Wl Wr}
       → leafRel d (pred k) w′ (leaf (δt ↑ᴵ e) X) Wl Wr
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X)
           (Wl ↓ seal (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X))
           (Wr ↓ seal (toRenameᵗ (ρR e) α′) (δr (δt ↑ᴵ e) Y)))
  SealI d N w (m-only x) α δs δt =
    (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X) Vl Vr
       → sealedL (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X)
           (leafRel d (onlyStage d k) w′ (leaf (δt ↑ᴵ e) X)) Vl Vr)
    × (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → onlyBelow d k N → ∀ {Wl Vr}
       → leafRel d (onlyStage d k) w′ (leaf (δt ↑ᴵ e) X) Wl Vr
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X)
           (Wl ↓ seal (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X)) Vr)
  SealI d N w (m-dead x) α δs δt = ⊤

  record ConvI (d : Dir) (N : ℕ) (w : World) (m : CMode Φ X (ΔR w))
      (α : TyVar (ΔL w)) (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) : Set₁ where
    field
      goodS : GoodI δs
      goodT : GoodI δt
      αX : δl δs X ≡ ＇ α
      otherL : ∀ Z → Z ≢ X
        → Σ[ γ ∈ TyVar (ΔL w) ] (δl δs Z ≡ ＇ γ × δl δt Z ≡ ＇ γ × γ ≢ α)
      leafO : ∀ Z → Z ≢ X → leaf δs Z ≈ˡ leaf δt Z
      rightI : RightI m δs δt
      sealI : SealI d N w m α δs δt

  open ConvI public

------------------------------------------------------------------------
-- Sealed values under equal names, representations and relations
------------------------------------------------------------------------

sealedL-map : ∀ {α α′ : TyVar ΘL} {R R′}
    {P P′ : Term ΘL → Term ΘR → Set} {Vl Vr}
  → α ≡ α′ → R ≡ R′ → (∀ {W V} → P W V → P′ W V)
  → sealedL α R P Vl Vr → sealedL α′ R′ P′ Vl Vr
sealedL-map refl refl f s with sealedL-inv s
sealedL-map refl refl f s | W , refl , r = (refl , refl) , f r

sealedR-map : ∀ {α α′ : TyVar ΘR} {R R′}
    {P P′ : Term ΘL → Term ΘR → Set} {Vl Vr}
  → α ≡ α′ → R ≡ R′ → (∀ {W V} → P W V → P′ W V)
  → sealedR α R P Vl Vr → sealedR α′ R′ P′ Vl Vr
sealedR-map refl refl f s with sealedR-inv s
sealedR-map refl refl f s | W , refl , r = (refl , refl) , f r

------------------------------------------------------------------------
-- At most one pure step on each side
------------------------------------------------------------------------

ℰ-≡ : ∀ d n {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) {Ml Ml′ Mr Mr′}
  → Ml ≡ Ml′ → Mr ≡ Mr′ → ℰ d n p w δ Ml Mr → ℰ d n p w δ Ml′ Mr′
ℰ-≡ d n p w δ refl refl r = r

-- the expression relation at stage zero
ℰ-zero : ∀ d {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr} → ℰ d zero p w δ Ml Mr
ℰ-zero d p w {δ} = ℰᵍ-zero d w {VR = λ le w′ e → 𝒱≤ d le p w′ (δ ↑ᴵ e)}

infix 2 _—→?_

data _—→?_ {Δ} : Term Δ → Term Δ → Set where
  stay : ∀ {M} → M —→? M
  step : ∀ {M N} → M —→ N → M —→? N

-- the left is already a value
ℰ-stepR? : ∀ d n {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} → GoodI δ
  → ∀ {Vl Mr Vr} → Mr —→? Vr → Value Vl → Value Vr
  → 𝒱 d n p w δ Vl Vr → ℰ d n p w δ Vl Mr
ℰ-stepR? d n p w g stay vl vr r = ℰ-value d n p w vl vr r
ℰ-stepR? ≺ n p w g (step s) vl vr r =
  ℰ-stepR ≺ n p w s (ℰ-value ≺ n p w vl vr r)
ℰ-stepR? ≻ zero p w g (step s) vl vr r = ℰ-zero ≻ p w
ℰ-stepR? ≻ (suc k) p w g (step s) vl vr r =
  ℰ-stepR ≻ k p w s (ℰ-value ≻ k p w vl vr (𝒱-down ≻ (n≤1+n k) p w g r))

ℰ-steps? : ∀ d n {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} → GoodI δ
  → ∀ {Ml Mr Vl Vr} → Ml —→? Vl → Mr —→? Vr → Value Vl → Value Vr
  → 𝒱 d n p w δ Vl Vr → ℰ d n p w δ Ml Mr
ℰ-steps? d n p w g stay sr vl vr r = ℰ-stepR? d n p w g sr vl vr r
ℰ-steps? ≺ zero p w g (step s) sr vl vr r = ℰ-zero ≺ p w
ℰ-steps? ≺ (suc k) p w g (step s) sr vl vr r =
  ℰ-stepL ≺ k p w s
    (ℰ-stepR? ≺ k p w g sr vl vr (𝒱-down ≺ (n≤1+n k) p w g r))
ℰ-steps? ≻ n p w g (step s) sr vl vr r =
  ℰ-stepL ≻ n p w s (ℰ-stepR? ≻ n p w g sr vl vr r)

------------------------------------------------------------------------
-- Moving the hypotheses to a future world, and under binders
------------------------------------------------------------------------

CMode-↑ : ∀ {Φ : Corr Δ Δ′} {X} {Θ Θ′} → Θ ↪ᵗ Θ′ → CMode Φ X Θ
  → CMode Φ X Θ′
CMode-↑ ρ (m-pair x α′) = m-pair x (toRenameᵗ ρ α′)
CMode-↑ ρ (m-only x) = m-only x
CMode-↑ ρ (m-dead x) = m-dead x

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d N} {w w′ : World}
    {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} (e : w′ ⊒ w) where

  private
    ρl = toRenameᵗ (ρL e)
    ρr = toRenameᵗ (ρR e)

  RightI-↑ : (m : CMode Φ X (ΔR w)) → RightI m δs δt
    → RightI (CMode-↑ (ρR e) m) (δs ↑ᴵ e) (δt ↑ᴵ e)
  RightI-↑ (m-pair x α′) (αY , other) =
    cong (renameᵗ ρr) αY , other′
    where
    other′ : ∀ Y′ → _ → _
    other′ Y′ ne with other Y′ ne
    other′ Y′ ne | γ , es , et , ne′ =
      ρr γ , cong (renameᵗ ρr) es , cong (renameᵗ ρr) et ,
      (λ eq → ne′ (toRenameᵗ-injective (ρR e) eq))
  RightI-↑ (m-only x) h Y′ = cong (renameᵗ ρr) (h Y′)
  RightI-↑ (m-dead x) h Y′ = cong (renameᵗ ρr) (h Y′)

  SealI-↑ : ∀ (m : CMode Φ X (ΔR w)) α → SealI d N w m α δs δt
    → SealI d N w′ (CMode-↑ (ρR e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e)
  SealI-↑ (m-pair {Y = Y} x α′) α (hrev , hcon) = rev′ , con′
    where
    rev′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → k ≤ N → ∀ {Vl Vr} → _ → _
    rev′ e′ {k} pos le r =
      sealedL-map (toRenameᵗ-∘ (ρL e′) (ρL e) α)
        (sym (δl≡ (↑ᴵ-trans δt e′ e) X))
        (sealedR-map (toRenameᵗ-∘ (ρR e′) (ρR e) α′)
          (sym (δr≡ (↑ᴵ-trans δt e′ e) Y))
          (leafRel-resp d (pred k) _ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) X))))
        (hrev (⊒-trans e′ e) pos le
          (leafRel-resp d k _ (leaf≈ (↑ᴵ-trans δs e′ e) X) r))
    con′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → k < N → ∀ {Wl Wr} → _ → _
    con′ {w″} e′ {k} pos lt {Wl} {Wr} r =
      leafRel-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) X))
        (subst₂ (leafRel d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) X))
          (cong₂ (λ a R → Wl ↓ seal a R) (toRenameᵗ-∘ (ρL e′) (ρL e) α)
            (sym (δl≡ (↑ᴵ-trans δt e′ e) X)))
          (cong₂ (λ a R → Wr ↓ seal a R) (toRenameᵗ-∘ (ρR e′) (ρR e) α′)
            (sym (δr≡ (↑ᴵ-trans δt e′ e) Y)))
          (hcon (⊒-trans e′ e) pos lt
            (leafRel-resp d (pred k) _ (leaf≈ (↑ᴵ-trans δt e′ e) X) r)))
  SealI-↑ (m-only x) α (hrev , hcon) = rev′ , con′
    where
    rev′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → k ≤ N → ∀ {Vl Vr} → _ → _
    rev′ e′ {k} pos le r =
      sealedL-map (toRenameᵗ-∘ (ρL e′) (ρL e) α)
        (sym (δl≡ (↑ᴵ-trans δt e′ e) X))
        (leafRel-resp d (onlyStage d k) _
          (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) X)))
        (hrev (⊒-trans e′ e) pos le
          (leafRel-resp d k _ (leaf≈ (↑ᴵ-trans δs e′ e) X) r))
    con′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → onlyBelow d k N
      → ∀ {Wl Vr} → _ → _
    con′ {w″} e′ {k} pos lt {Wl} {Vr} r =
      leafRel-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) X))
        (subst (λ V → leafRel d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) X) V Vr)
          (cong₂ (λ a R → Wl ↓ seal a R) (toRenameᵗ-∘ (ρL e′) (ρL e) α)
            (sym (δl≡ (↑ᴵ-trans δt e′ e) X)))
          (hcon (⊒-trans e′ e) pos lt
            (leafRel-resp d (onlyStage d k) _
              (leaf≈ (↑ᴵ-trans δt e′ e) X) r)))
  SealI-↑ (m-dead x) α h = tt

  ConvI-↑ : ∀ {m : CMode Φ X (ΔR w)} {α} → ConvI d N w m α δs δt
    → ConvI d N w′ (CMode-↑ (ρR e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e)
  goodS (ConvI-↑ h) = GoodI-↑ {δ = δs} (goodS h) e
  goodT (ConvI-↑ h) = GoodI-↑ {δ = δt} (goodT h) e
  αX (ConvI-↑ h) = cong (renameᵗ ρl) (αX h)
  otherL (ConvI-↑ h) Z ne with otherL h Z ne
  otherL (ConvI-↑ h) Z ne | γ , es , et , ne′ =
    ρl γ , cong (renameᵗ ρl) es , cong (renameᵗ ρl) et ,
    (λ eq → ne′ (toRenameᵗ-injective (ρL e) eq))
  leafO (ConvI-↑ h) Z ne = transportLeaf-resp (ρL e) (ρR e) (leafO h Z ne)
  rightI (ConvI-↑ {m = m} h) = RightI-↑ m (rightI h)
  sealI (ConvI-↑ {m = m} {α} h) = SealI-↑ m α (sealI h)

CMode-pair : ∀ {Φ : Corr Δ Δ′} {X} {Θ} → CMode Φ X Θ
  → CMode (pair Φ) (suc X) Θ
CMode-pair (m-pair x α′) = m-pair (↔-pair x) α′
CMode-pair (m-only x) = m-only (only-pair x)
CMode-pair (m-dead x) = m-dead (dead-pair x)

CMode-only : ∀ {Φ : Corr Δ Δ′} {X} {Θ} → CMode Φ X Θ
  → CMode (only Φ) (suc X) Θ
CMode-only (m-pair x α′) = m-pair (↔-only x) α′
CMode-only (m-only x) = m-only (only-only x)
CMode-only (m-dead x) = m-dead (dead-only x)

CMode-dead : ∀ {Φ : Corr Δ Δ′} {X} {Θ} → CMode Φ X Θ
  → CMode (dead Φ) (suc X) Θ
CMode-dead (m-pair x α′) = m-pair (↔-dead x) α′
CMode-dead (m-only x) = m-only (only-dead x)
CMode-dead (m-dead x) = m-dead (dead-dead x)

-- a new right variable differs from the right's converted one
FreshR : ∀ {Φ : Corr Δ Δ′} {X} {Θ} → CMode Φ X Θ → TyVar Θ → Set
FreshR (m-pair x α′) β′ = β′ ≢ α′
FreshR (m-only x) β′ = ⊤
FreshR (m-dead x) β′ = ⊤

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d N} {w : World}
    {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {β : TyVar (ΔL w)}
    {l : Leaf (ΔL w) (ΔR w)} where

  ConvI-extPair : ∀ {m : CMode Φ X (ΔR w)} {α β′}
    → GoodLeaf l → β ≢ α → FreshR m β′
    → ConvI d N w m α δs δt
    → ConvI d N w (CMode-pair m) α
        (extPairI (＇ β) (＇ β′) l δs) (extPairI (＇ β) (＇ β′) l δt)
  goodS (ConvI-extPair {β′ = β′} gl ne fr h) =
    GoodI-extPairI {T = ＇ β} {T′ = ＇ β′} {δ = δs} gl (goodS h)
  goodT (ConvI-extPair {β′ = β′} gl ne fr h) =
    GoodI-extPairI {T = ＇ β} {T′ = ＇ β′} {δ = δt} gl (goodT h)
  αX (ConvI-extPair gl ne fr h) = αX h
  otherL (ConvI-extPair gl ne fr h) zero ne′ = β , refl , refl , ne
  otherL (ConvI-extPair gl ne fr h) (suc Z) ne′ =
    otherL h Z (λ eq → ne′ (cong suc eq))
  leafO (ConvI-extPair gl ne fr h) zero ne′ = ≈ˡ-refl
  leafO (ConvI-extPair gl ne fr h) (suc Z) ne′ =
    leafO h Z (λ eq → ne′ (cong suc eq))
  rightI (ConvI-extPair {m = m-pair x α′} {β′ = β′} gl ne fr h) =
    proj₁ (rightI h) , other
    where
    other : ∀ Y′ → _ → _
    other zero ne′ = β′ , refl , refl , fr
    other (suc Y′) ne′ = proj₂ (rightI h) Y′ (λ eq → ne′ (cong suc eq))
  rightI (ConvI-extPair {m = m-only x} gl ne fr h) zero = refl
  rightI (ConvI-extPair {m = m-only x} gl ne fr h) (suc Y′) = rightI h Y′
  rightI (ConvI-extPair {m = m-dead x} gl ne fr h) zero = refl
  rightI (ConvI-extPair {m = m-dead x} gl ne fr h) (suc Y′) = rightI h Y′
  sealI (ConvI-extPair {m = m-pair x α′} gl ne fr h) = sealI h
  sealI (ConvI-extPair {m = m-only x} gl ne fr h) = sealI h
  sealI (ConvI-extPair {m = m-dead x} gl ne fr h) = sealI h

  ConvI-extOnly : ∀ {m : CMode Φ X (ΔR w)} {α} → GoodLeaf l → β ≢ α
    → ConvI d N w m α δs δt
    → ConvI d N w (CMode-only m) α (extOnlyI (＇ β) l δs) (extOnlyI (＇ β) l δt)
  goodS (ConvI-extOnly gl ne h) =
    GoodI-extOnlyI {T = ＇ β} {δ = δs} gl (goodS h)
  goodT (ConvI-extOnly gl ne h) =
    GoodI-extOnlyI {T = ＇ β} {δ = δt} gl (goodT h)
  αX (ConvI-extOnly gl ne h) = αX h
  otherL (ConvI-extOnly gl ne h) zero ne′ = β , refl , refl , ne
  otherL (ConvI-extOnly gl ne h) (suc Z) ne′ =
    otherL h Z (λ eq → ne′ (cong suc eq))
  leafO (ConvI-extOnly gl ne h) zero ne′ = ≈ˡ-refl
  leafO (ConvI-extOnly gl ne h) (suc Z) ne′ =
    leafO h Z (λ eq → ne′ (cong suc eq))
  rightI (ConvI-extOnly {m = m-pair x α′} gl ne h) = rightI h
  rightI (ConvI-extOnly {m = m-only x} gl ne h) = rightI h
  rightI (ConvI-extOnly {m = m-dead x} gl ne h) = rightI h
  sealI (ConvI-extOnly {m = m-pair x α′} gl ne h) = sealI h
  sealI (ConvI-extOnly {m = m-only x} gl ne h) = sealI h
  sealI (ConvI-extOnly {m = m-dead x} gl ne h) = sealI h

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d N} {w : World}
    {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {β : TyVar (ΔL w)} where

  ConvI-extDead : ∀ {m : CMode Φ X (ΔR w)} {α} → β ≢ α
    → ConvI d N w m α δs δt
    → ConvI d N w (CMode-dead m) α (extDeadI (＇ β) δs) (extDeadI (＇ β) δt)
  goodS (ConvI-extDead ne h) = GoodI-extDeadI {T = ＇ β} {δ = δs} (goodS h)
  goodT (ConvI-extDead ne h) = GoodI-extDeadI {T = ＇ β} {δ = δt} (goodT h)
  αX (ConvI-extDead ne h) = αX h
  otherL (ConvI-extDead ne h) zero ne′ = β , refl , refl , ne
  otherL (ConvI-extDead ne h) (suc Z) ne′ =
    otherL h Z (λ eq → ne′ (cong suc eq))
  leafO (ConvI-extDead ne h) zero ne′ = ≈ˡ-refl
  leafO (ConvI-extDead ne h) (suc Z) ne′ =
    leafO h Z (λ eq → ne′ (cong suc eq))
  rightI (ConvI-extDead {m = m-pair x α′} ne h) = rightI h
  rightI (ConvI-extDead {m = m-only x} ne h) = rightI h
  rightI (ConvI-extDead {m = m-dead x} ne h) = rightI h
  sealI (ConvI-extDead {m = m-pair x α′} ne h) = sealI h
  sealI (ConvI-extDead {m = m-only x} ne h) = sealI h
  sealI (ConvI-extDead {m = m-dead x} ne h) = sealI h

------------------------------------------------------------------------
-- The hypotheses on X, in the current world
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d N} {w : World}
    {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {α : TyVar (ΔL w)} where

  pairRev : ∀ {Y} {x : Φ ∋ X ↔ Y} {α′}
    → ConvI d N w (m-pair x α′) α δs δt → ∀ {k} → 0 < k → k ≤ N
    → ∀ {Vl Vr} → leafRel d k w (leaf δs X) Vl Vr
    → sealedL α (δl δt X) (sealedR α′ (δr δt Y)
        (leafRel d (pred k) w (leaf δt X))) Vl Vr
  pairRev {Y} {α′ = α′} h {k} pos le r =
    sealedL-map (toRename-id-eq α) (δl≡ (↑ᴵ-refl {w = w} δt) X)
      (sealedR-map (toRename-id-eq α′) (δr≡ (↑ᴵ-refl {w = w} δt) Y)
        (leafRel-resp d (pred k) w (leaf≈ (↑ᴵ-refl {w = w} δt) X)))
      (proj₁ (sealI h) (⊒-refl w) pos le
        (leafRel-resp d k w (≈ˡ-sym (leaf≈ (↑ᴵ-refl {w = w} δs) X)) r))

  pairCon : ∀ {Y} {x : Φ ∋ X ↔ Y} {α′}
    → ConvI d N w (m-pair x α′) α δs δt → ∀ {k} → 0 < k → k < N
    → ∀ {Wl Wr} → leafRel d (pred k) w (leaf δt X) Wl Wr
    → leafRel d k w (leaf δs X)
        (Wl ↓ seal α (δl δt X)) (Wr ↓ seal α′ (δr δt Y))
  pairCon {Y} {α′ = α′} h {k} pos lt {Wl} {Wr} r =
    leafRel-resp d k w (leaf≈ (↑ᴵ-refl {w = w} δs) X)
      (subst₂ (leafRel d k w (leaf (δs ↑ᴵ ⊒-refl w) X))
        (cong₂ (λ a R → Wl ↓ seal a R) (toRename-id-eq α)
          (δl≡ (↑ᴵ-refl {w = w} δt) X))
        (cong₂ (λ a R → Wr ↓ seal a R) (toRename-id-eq α′)
          (δr≡ (↑ᴵ-refl {w = w} δt) Y))
        (proj₂ (sealI h) (⊒-refl w) pos lt
          (leafRel-resp d (pred k) w
            (≈ˡ-sym (leaf≈ (↑ᴵ-refl {w = w} δt) X)) r)))

  onlyRev : ∀ {x : Φ ∋ X only}
    → ConvI d N w (m-only x) α δs δt → ∀ {k} → 0 < k → k ≤ N
    → ∀ {Vl Vr} → leafRel d k w (leaf δs X) Vl Vr
    → sealedL α (δl δt X) (leafRel d (onlyStage d k) w (leaf δt X)) Vl Vr
  onlyRev h {k} pos le r =
    sealedL-map (toRename-id-eq α) (δl≡ (↑ᴵ-refl {w = w} δt) X)
      (leafRel-resp d (onlyStage d k) w (leaf≈ (↑ᴵ-refl {w = w} δt) X))
      (proj₁ (sealI h) (⊒-refl w) pos le
        (leafRel-resp d k w (≈ˡ-sym (leaf≈ (↑ᴵ-refl {w = w} δs) X)) r))

  onlyCon : ∀ {x : Φ ∋ X only}
    → ConvI d N w (m-only x) α δs δt → ∀ {k} → 0 < k → onlyBelow d k N
    → ∀ {Wl Vr} → leafRel d (onlyStage d k) w (leaf δt X) Wl Vr
    → leafRel d k w (leaf δs X) (Wl ↓ seal α (δl δt X)) Vr
  onlyCon h {k} pos lt {Wl} {Vr} r =
    leafRel-resp d k w (leaf≈ (↑ᴵ-refl {w = w} δs) X)
      (subst (λ V → leafRel d k w (leaf (δs ↑ᴵ ⊒-refl w) X) V Vr)
        (cong₂ (λ a R → Wl ↓ seal a R) (toRename-id-eq α)
          (δl≡ (↑ᴵ-refl {w = w} δt) X))
        (proj₂ (sealI h) (⊒-refl w) pos lt
          (leafRel-resp d (onlyStage d k) w
            (≈ˡ-sym (leaf≈ (↑ᴵ-refl {w = w} δt) X)) r)))

------------------------------------------------------------------------
-- Renaming the conversions of a reveal and of a conceal
------------------------------------------------------------------------

module _ {Θ Θ′ : TyCtx} (ρ : Θ ↪ᵗ Θ′) where

  private
    ρv = toRenameᵗ ρ
    inj = toRenameᵗ-injective ρ

  〖〗-ren : ∀ (α : TyVar Θ) R (σ : Δ ⇒ˢ Θ) A
    → ⟪ rename↑ ρv 〖 α , R ↑ substᵗ σ A 〗 ⟫↑
      ≡ ⟪ 〖 ρv α , renameᵗ ρv R ↑ substᵗ (λ Z → renameᵗ ρv (σ Z)) A 〗 ⟫↑
  〖〗-ren α R σ A =
    trans (〖〗-rename ρv inj α R (substᵗ σ A))
      (cong (λ B → ⟪ 〖 ρv α , renameᵗ ρv R ↑ B 〗 ⟫↑)
        (renameᵗ-subst ρv σ A))

  makeConceal-ren : ∀ (α : TyVar Θ) R (σ : Δ ⇒ˢ Θ) A
    → ⟪ rename↓ ρv (makeConceal α R (substᵗ σ A)) ⟫↓
      ≡ ⟪ makeConceal (ρv α) (renameᵗ ρv R)
            (substᵗ (λ Z → renameᵗ ρv (σ Z)) A) ⟫↓
  makeConceal-ren α R σ A =
    trans (makeConceal-rename ρv inj α R (substᵗ σ A))
      (cong (λ B → ⟪ makeConceal (ρv α) (renameᵗ ρv R) B ⟫↓)
        (renameᵗ-subst ρv σ A))

  revM-ren : ∀ (rc : RConv Θ) (σ : Δ ⇒ˢ Θ) A (V : Term Θ)
    → renameᵗᵐ ρ (revM rc (substᵗ σ A) V)
      ≡ revM (renRConv ρ rc) (substᵗ (λ Z → renameᵗ ρv (σ Z)) A)
          (renameᵗᵐ ρ V)
  revM-ren nothing σ A V = refl
  revM-ren (just (α′ , R)) σ A V = ↑-pk (〖〗-ren α′ R σ A)

  conM-ren : ∀ (rc : RConv Θ) (σ : Δ ⇒ˢ Θ) A (V : Term Θ)
    → renameᵗᵐ ρ (conM rc (substᵗ σ A) V)
      ≡ conM (renRConv ρ rc) (substᵗ (λ Z → renameᵗ ρv (σ Z)) A)
          (renameᵗᵐ ρ V)
  conM-ren nothing σ A V = refl
  conM-ren (just (α′ , R)) σ A V = ↓-pk (makeConceal-ren α′ R σ A)

  revFrame-ren : ∀ (rc : RConv Θ) (σ : Δ ⇒ˢ Θ) A (V : Term Θ′)
    → mplug (renameMFrame ρ (revFrame rc (substᵗ σ A))) V
      ≡ revM (renRConv ρ rc) (substᵗ (λ Z → renameᵗ ρv (σ Z)) A) V
  revFrame-ren nothing σ A V = refl
  revFrame-ren (just (α′ , R)) σ A V = ↑-pk (〖〗-ren α′ R σ A)

  conFrame-ren : ∀ (rc : RConv Θ) (σ : Δ ⇒ˢ Θ) A (V : Term Θ′)
    → mplug (renameMFrame ρ (conFrame rc (substᵗ σ A))) V
      ≡ conM (renRConv ρ rc) (substᵗ (λ Z → renameᵗ ρv (σ Z)) A) V
  conFrame-ren nothing σ A V = refl
  conFrame-ren (just (α′ , R)) σ A V = ↓-pk (makeConceal-ren α′ R σ A)

rconv-↑ : ∀ {Φ : Corr Δ Δ′} {X} {Θ Θ′} (ρ : Θ ↪ᵗ Θ′) (m : CMode Φ X Θ) σ
  → rconv (CMode-↑ ρ m) (λ Y → renameᵗ (toRenameᵗ ρ) (σ Y))
    ≡ renRConv ρ (rconv m σ)
rconv-↑ ρ (m-pair x α′) σ = refl
rconv-↑ ρ (m-only x) σ = refl
rconv-↑ ρ (m-dead x) σ = refl

------------------------------------------------------------------------
-- Applications of converted functions
------------------------------------------------------------------------

-- the argument, the application, and the conversion of the result
app-core : ∀ d s {Φ : Corr Δ Δ′} {A A′ B B′} (p : Φ ⊢ A ⊑ A′)
    (q : Φ ⊢ B ⊑ B′) w {δ₁ δ₂ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {Vl Vr Ul Ur} (vl : Value Vl) (vr : Value Vr)
    (FL : MFrame (ΔL w)) (FR : MFrame (ΔR w))
  → ℰ d s p w δ₁ Ul Ur
  → funRel d s p q w δ₁ Vl Vr
  → (∀ {w′} (e : w′ ⊒ w) {k} → k ≤ s → ∀ {Ql Qr} → Value Ql → Value Qr
       → 𝒱 d k q w′ (δ₁ ↑ᴵ e) Ql Qr
       → ℰ d k q w′ (δ₂ ↑ᴵ e) (mplug (renameMFrame (ρL e) FL) Ql)
           (mplug (renameMFrame (ρR e) FR) Qr))
  → ℰ d s q w δ₂ (mplug FL (Vl · Ul)) (mplug FR (Vr · Ur))
app-core d s p q w {δ₁} {δ₂} vl vr FL FR inner f K =
  ℰ-bind₂ d s q q w {δ₁ = δ₁} {δ₂ = δ₂} FL FR
    (ℰ-bind₂ d s p q w {δ₁ = δ₁} {δ₂ = δ₁}
      (just (app₂ _ vl)) (just (app₂ _ vr)) inner K₁)
    K
  where
  K₁ : ∀ {w′} (e : w′ ⊒ w) {k} → k ≤ s → ∀ {Pl Pr} → Value Pl → Value Pr
    → 𝒱 d k p w′ (δ₁ ↑ᴵ e) Pl Pr → _
  K₁ e {k} k≤s {Pl} {Pr} pl pr r =
    ℰᵍ-map d k _
      (λ le′ w″ e′ V V′ → 𝒱≤-cast d (≤′-trans le′ (≤⇒≤′ k≤s)) le′ q w″)
      (f e (≤⇒≤′ k≤s) Pl Pr pl pr (𝒱≤-cast d ≤′-refl (≤⇒≤′ k≤s) p _ r))

-- a right step exactly when the right converts
RStep : ∀ {Θ} → RConv Θ → Term Θ → Term Θ → Set
RStep nothing M M′ = M ≡ M′
RStep (just c) M M′ = M —→ M′

-- the stages of an application's step: the counted side steps, unless
-- in `≻` the right does not convert
ℰ-app-steps : ∀ d {n N} {Φ : Corr Δ Δ′} {B B′} (q : Φ ⊢ B ⊑ B′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} (rc : RConv (ΔR w))
    {Ml Ml′ Mr Mr′}
  → n ≤ N → Ml —→ Ml′ → RStep rc Mr Mr′
  → (∀ {s} → s ≤ n → ConB d rc s N → ℰ d s q w δ Ml′ Mr′)
  → ℰ d n q w δ Ml Mr
ℰ-app-steps ≺ {zero} q w rc le sl sr k = ℰ-zero ≺ q w
ℰ-app-steps ≺ {suc n} q w nothing le sl refl k =
  ℰ-stepL ≺ n q w sl (k (n≤1+n n) le)
ℰ-app-steps ≺ {suc n} q w (just c) le sl sr k =
  ℰ-stepL ≺ n q w sl (ℰ-stepR ≺ n q w sr (k (n≤1+n n) le))
ℰ-app-steps ≻ {n} q w nothing le sl refl k =
  ℰ-stepL ≻ n q w sl (k ≤-refl le)
ℰ-app-steps ≻ {zero} q w (just c) le sl sr k = ℰ-zero ≻ q w
ℰ-app-steps ≻ {suc n} q w (just c) le sl sr k =
  ℰ-stepL ≻ (suc n) q w sl (ℰ-stepR ≻ n q w sr (k (n≤1+n n) le))

-- the right's application of a converted function, when it converts
rightApp : ∀ {Θ} (rc : RConv Θ) {A B} {Vr Ur : Term Θ}
  → Value Vr → Value Ur
  → RStep rc (revM rc (A ⇒ B) Vr · Ur)
      (mplug (revFrame rc B) (Vr · conM rc A Ur))
rightApp nothing vr ur = refl
rightApp (just (α′ , R)) vr ur = β-reveal-⇒ vr ur

rightAppC : ∀ {Θ} (rc : RConv Θ) {A B} {Vr Ur : Term Θ}
  → Value Vr → Value Ur
  → RStep rc (conM rc (A ⇒ B) Vr · Ur)
      (mplug (conFrame rc B) (Vr · revM rc A Ur))
rightAppC nothing vr ur = refl
rightAppC (just (α′ , R)) vr ur = β-conceal-⇒ vr ur

ConB-ren : ∀ {Θ Θ′} d (ρ : Θ ↪ᵗ Θ′) (rc : RConv Θ) {k N}
  → ConB d rc k N → ConB d (renRConv ρ rc) k N
ConB-ren ≺ ρ rc cb = cb
ConB-ren ≻ ρ nothing cb = cb
ConB-ren ≻ ρ (just c) cb = cb

ConB-down : ∀ {Θ} d (rc : RConv Θ) {k n N} → k ≤ n
  → ConB d rc n N → ConB d rc k N
ConB-down ≺ rc le cb = ≤-<-trans le cb
ConB-down ≻ nothing le cb = ≤-trans le cb
ConB-down ≻ (just c) le cb = ≤-<-trans le cb

ConB-≤ : ∀ {Θ} d (rc : RConv Θ) {k N} → ConB d rc k N → k ≤ N
ConB-≤ ≺ rc cb = <⇒≤ cb
ConB-≤ ≻ nothing cb = cb
ConB-≤ ≻ (just c) cb = <⇒≤ cb

module FunConv {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} (d : Dir) (N : ℕ)
    {A A′ B B′} (p : Φ ⊢ A ⊑ A′) (q : Φ ⊢ B ⊑ B′)
    (RF : ∀ {Θ} → CMode Φ X Θ → (Δ′ ⇒ˢ Θ) → RConv Θ)
    (RF-↑ : ∀ {Θ Θ′} (ρ : Θ ↪ᵗ Θ′) (m : CMode Φ X Θ) σ
       → RF (CMode-↑ ρ m) (λ Y → renameᵗ (toRenameᵗ ρ) (σ Y))
         ≡ renRConv ρ (RF m σ))
    (revp : ∀ {w m α δs δt} → ConvI d N w m α δs δt → ∀ {k} → k ≤ N
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , δl δt X ↑ substᵗ (δl δs) A 〗)
           (revM (RF m (δr δt)) (substᵗ (δr δs) A′) Vr))
    (conp : ∀ {w m α δs δt} → ConvI d N w m α δs δt → ∀ {k}
       → ConB d (RF m (δr δt)) k N
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs (Wl ↓ makeConceal α (δl δt X) (substᵗ (δl δs) A))
           (conM (RF m (δr δt)) (substᵗ (δr δs) A′) Wr))
    (revq : ∀ {w m α δs δt} → ConvI d N w m α δs δt → ∀ {k} → k ≤ N
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k q w δs Vl Vr
       → ℰ d k q w δt (Vl ↑ 〖 α , δl δt X ↑ substᵗ (δl δs) B 〗)
           (revM (RF m (δr δt)) (substᵗ (δr δs) B′) Vr))
    (conq : ∀ {w m α δs δt} → ConvI d N w m α δs δt → ∀ {k}
       → ConB d (RF m (δr δt)) k N
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k q w δt Wl Wr
       → ℰ d k q w δs (Wl ↓ makeConceal α (δl δt X) (substᵗ (δl δs) B))
           (conM (RF m (δr δt)) (substᵗ (δr δs) B′) Wr))
    where

  -- a converted function applied, in the world of the function
  rev-at : ∀ {n} w {m α δs δt} (h : ConvI d N w m α δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → funRel d n p q w δs Vl Vr
    → ∀ {Ul Ur} → Value Ul → Value Ur → 𝒱 d n p w δt Ul Ur
    → ℰ d n q w δt
        ((Vl ↑ 〖 α , δl δt X ↑ substᵗ (δl δs) (A ⇒ B) 〗) · Ul)
        (revM (RF m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Vr · Ur)
  rev-at w {m} {α} {δs} {δt} h le {Vl} {Vr} vl vr f {Ul} {Ur} ul ur a =
    ℰ-app-steps d q w (RF m (δr δt)) le (β-reveal-⇒ vl ul)
      (rightApp (RF m (δr δt)) vr ur)
      (λ {s} s≤n cb →
        app-core d s p q w vl vr
          (just (reveal 〖 α , δl δt X ↑ substᵗ (δl δs) B 〗))
          (revFrame (RF m (δr δt)) (substᵗ (δr δs) B′))
          (conp h cb ul ur (𝒱-down d s≤n p w (goodT h) a))
          (funRel-down d s≤n p q w f)
          (λ e₂ {k} k≤s {Ql} {Qr} ql qr r →
            ℰᵍ-≡ (sym (↑-pk (〖〗-ren (ρL e₂) α (δl δt X) (δl δs) B)))
              (sym (trans
                (revFrame-ren (ρR e₂) (RF m (δr δt)) (δr δs) B′ Qr)
                (cong (λ c → revM c _ Qr) (sym (RF-↑ (ρR e₂) m (δr δt))))))
              (revq (ConvI-↑ e₂ h) (≤-trans k≤s (≤-trans s≤n le)) ql qr r)))

  con-at : ∀ {n} w {m α δs δt} (h : ConvI d N w m α δs δt)
    → ConB d (RF m (δr δt)) n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → funRel d n p q w δt Wl Wr
    → ∀ {Ul Ur} → Value Ul → Value Ur → 𝒱 d n p w δs Ul Ur
    → ℰ d n q w δs
        ((Wl ↓ makeConceal α (δl δt X) (substᵗ (δl δs) (A ⇒ B))) · Ul)
        (conM (RF m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Wr · Ur)
  con-at w {m} {α} {δs} {δt} h cb {Wl} {Wr} wl wr f {Ul} {Ur} ul ur a =
    ℰ-app-steps d q w (RF m (δr δt)) (ConB-≤ d (RF m (δr δt)) cb)
      (β-conceal-⇒ wl ul) (rightAppC (RF m (δr δt)) wr ur)
      (λ {s} s≤n cb′ →
        app-core d s p q w wl wr
          (just (conceal (makeConceal α (δl δt X) (substᵗ (δl δs) B))))
          (conFrame (RF m (δr δt)) (substᵗ (δr δs) B′))
          (revp h (≤-trans s≤n (ConB-≤ d (RF m (δr δt)) cb)) ul ur
            (𝒱-down d s≤n p w (goodS h) a))
          (funRel-down d s≤n p q w f)
          (λ e₂ {k} k≤s {Ql} {Qr} ql qr r →
            ℰᵍ-≡
              (sym (↓-pk (makeConceal-ren (ρL e₂) α (δl δt X) (δl δs) B)))
              (sym (trans
                (conFrame-ren (ρR e₂) (RF m (δr δt)) (δr δs) B′ Qr)
                (cong (λ c → conM c _ Qr) (sym (RF-↑ (ρR e₂) m (δr δt))))))
              (conq (ConvI-↑ e₂ h)
                (subst (λ c → ConB d c k N) (sym (RF-↑ (ρR e₂) m (δr δt)))
                  (ConB-ren d (ρR e₂) (RF m (δr δt))
                    (ConB-down d (RF m (δr δt)) (≤-trans k≤s s≤n) cb)))
                ql qr r)))

  fun-rev : ∀ {n w m α δs δt} (h : ConvI d N w m α δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → funRel d n p q w δs Vl Vr
    → funRel d n p q w δt
        (Vl ↑ 〖 α , δl δt X ↑ substᵗ (δl δs) (A ⇒ B) 〗)
        (revM (RF m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Vr)
  fun-rev {n} {w} {m} {α} {δs} {δt} h le {Vl} {Vr} vl vr f
      {w′} e {n′} le′ Ul Ur ul ur a =
    ℰᵍ-map d n′ w′ (λ le″ w″ e″ V V′ → 𝒱≤-cast d le″ (≤′-trans le″ le′) q w″)
      (ℰᵍ-≡
        (cong (_· Ul)
          (sym (↑-pk (〖〗-ren (ρL e) α (δl δt X) (δl δs) (A ⇒ B)))))
        (cong (_· Ur) (sym (trans
          (revM-ren (ρR e) (RF m (δr δt)) (δr δs) (A′ ⇒ B′) Vr)
          (cong (λ c → revM c _ _) (sym (RF-↑ (ρR e) m (δr δt)))))))
        (rev-at w′ (ConvI-↑ e h) (≤-trans (≤′⇒≤ le′) le)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (renameᵗᵐ-preserves-Value (ρR e) vr)
          (funRel-down d (≤′⇒≤ le′) p q w′ (funRel-mono d n p q e f))
          ul ur (𝒱≤-cast d le′ ≤′-refl p w′ a)))

  fun-con : ∀ {n w m α δs δt} (h : ConvI d N w m α δs δt)
    → ConB d (RF m (δr δt)) n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → funRel d n p q w δt Wl Wr
    → funRel d n p q w δs
        (Wl ↓ makeConceal α (δl δt X) (substᵗ (δl δs) (A ⇒ B)))
        (conM (RF m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Wr)
  fun-con {n} {w} {m} {α} {δs} {δt} h cb {Wl} {Wr} wl wr f
      {w′} e {n′} le′ Ul Ur ul ur a =
    ℰᵍ-map d n′ w′ (λ le″ w″ e″ V V′ → 𝒱≤-cast d le″ (≤′-trans le″ le′) q w″)
      (ℰᵍ-≡
        (cong (_· Ul)
          (sym (↓-pk
            (makeConceal-ren (ρL e) α (δl δt X) (δl δs) (A ⇒ B)))))
        (cong (_· Ur) (sym (trans
          (conM-ren (ρR e) (RF m (δr δt)) (δr δs) (A′ ⇒ B′) Wr)
          (cong (λ c → conM c _ _) (sym (RF-↑ (ρR e) m (δr δt)))))))
        (con-at w′ (ConvI-↑ e h)
          (subst (λ c → ConB d c n′ N) (sym (RF-↑ (ρR e) m (δr δt)))
            (ConB-ren d (ρR e) (RF m (δr δt))
              (ConB-down d (RF m (δr δt)) (≤′⇒≤ le′) cb)))
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (renameᵗᵐ-preserves-Value (ρR e) wr)
          (funRel-down d (≤′⇒≤ le′) p q w′ (funRel-mono d n p q e f))
          ul ur (𝒱≤-cast d le′ ≤′-refl p w′ a)))

------------------------------------------------------------------------
-- Relations that do not read the interpretation
------------------------------------------------------------------------

module _ {Φ : Corr Δ Δ′} {w : World} {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {Vl Vr} where

  ★★-δ : ∀ d n → 𝒱 d n (★⊑★ {Φ = Φ}) w δ Vl Vr
    → 𝒱 d n (★⊑★ {Φ = Φ}) w δ′ Vl Vr
  ★★-δ ≺ n r = r
  ★★-δ ≻ zero r = r
  ★★-δ ≻ (suc k) r = r

  ι★-δ : ∀ d n {ι} → 𝒱 d n (ι⊑★ {Φ = Φ} {ι = ι}) w δ Vl Vr
    → 𝒱 d n (ι⊑★ {Φ = Φ} {ι = ι}) w δ′ Vl Vr
  ι★-δ ≺ n r = r
  ι★-δ ≻ zero r = r
  ι★-δ ≻ (suc k) r = r

  ιι-δ : ∀ d n {ι} → 𝒱 d n (ι⊑ι {Φ = Φ} {ι = ι}) w δ Vl Vr
    → 𝒱 d n (ι⊑ι {Φ = Φ} {ι = ι}) w δ′ Vl Vr
  ιι-δ ≺ n r = r
  ιι-δ ≻ n r = r

-- the right side of `⇒⊑★`: a function injected into `★`
funStar-map : ∀ {d n} {Φ : Corr Δ Δ′} {A B} {p : Φ ⊢ A ⊑ ★} {q : Φ ⊢ B ⊑ ★}
    {w} {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vl′ Vr}
  → (∀ {Wr} → Value Wr → funRel d n p q w δ Vl Wr
       → funRel d n p q w δ′ Vl′ Wr)
  → Value Vr → funStar d n p q w δ Vl Vr → funStar d n p q w δ′ Vl′ Vr
funStar-map f (v CT.《 i 》) (inj , r) = inj , f v r
funStar-map f (CT.ƛ N) ()
funStar-map f (CT.Λ v) ()
funStar-map f (CT.$ k) ()
funStar-map f (v CT.↑ rv) ()
funStar-map f (v CT.↓ cv) ()

------------------------------------------------------------------------
-- Variables
------------------------------------------------------------------------

-- a left-only variable at `★`
rev★-var : ∀ d n {Φ : Corr Δ Δ′} {Z} (z : Φ ∋ Z only) w {X}
    {m : CMode Φ X (ΔR w)} {N α δs δt} → ConvI d N w m α δs δt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑★ z) w δs Vl Vr
  → ℰ d n (X⊑★ z) w δt (Vl ↑ 〖 α , δl δt X ↑ δl δs Z 〗) Vr
rev★-var d n {Z = Z} z w {X} h le vl vr r with Z ≟ X
rev★-var d n {Z = Z} z w {X} {α = α} {δs} {δt} h le {Vl} vl vr r
    | no ne with otherL h Z ne
rev★-var d n {Z = Z} z w {X} {α = α} {δs} {δt} h le {Vl} vl vr r
    | no ne | γ , es , et , ne′ =
  ℰ-≡ d n (X⊑★ z) w δt (sym (↑-pk (〖〗-other (δl δt X) es ne′))) refl
    (ℰ-steps? d n (X⊑★ z) w (goodT h) (step (id-reveal vl)) stay vl vr
      (to (𝒱-X★ d n z w)
        (leafRel-resp d n w (leafO h Z ne) (from (𝒱-X★ d n z w) r))))
rev★-var d n {Z = .X} z w {X} {m-pair x α′} h le vl vr r | yes refl =
  ⊥-elim (↔-only-⊥ x z)
rev★-var d n {Z = .X} z w {X} {m-dead x} h le vl vr r | yes refl =
  ⊥-elim (only-dead-⊥ z x)
rev★-var d zero {Z = .X} z w {X} {m-only x} h le vl vr r | yes refl =
  ℰ-zero d (X⊑★ z) w
rev★-var d (suc k) {Z = .X} z w {X} {m-only x} {α = α} {δs} {δt} h le
    vl vr r | yes refl
    with sealedL-inv (onlyRev h (s≤s z≤n) le (from (𝒱-X★ d (suc k) z w) r))
rev★-var ≺ (suc k) {Z = .X} z w {X} {m-only x} {α = α} {δs} {δt} h le
    vl vr r | yes refl | W , refl , r′ =
  ℰ-≡ ≺ (suc k) (X⊑★ z) w δt (sym (↑-pk (〖〗-self α (δl δt X) (αX h)))) refl
    (ℰ-stepL ≺ k (X⊑★ z) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≺ k (X⊑★ z) w (value-sealed vl) vr r′))
rev★-var ≻ (suc k) {Z = .X} z w {X} {m-only x} {α = α} {δs} {δt} h le
    vl vr r | yes refl | W , refl , r′ =
  ℰ-≡ ≻ (suc k) (X⊑★ z) w δt (sym (↑-pk (〖〗-self α (δl δt X) (αX h)))) refl
    (ℰ-stepL ≻ (suc k) (X⊑★ z) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≻ (suc k) (X⊑★ z) w (value-sealed vl) vr r′))

con★-var : ∀ d n {Φ : Corr Δ Δ′} {Z} (z : Φ ∋ Z only) w {X}
    {m : CMode Φ X (ΔR w)} {N α δs δt} → ConvI d N w m α δs δt
  → ConB {ΔR w} d nothing n N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑★ z) w δt Wl Wr
  → ℰ d n (X⊑★ z) w δs (Wl ↓ makeConceal α (δl δt X) (δl δs Z)) Wr
con★-var d n {Z = Z} z w {X} h cb wl wr r with Z ≟ X
con★-var d n {Z = Z} z w {X} {α = α} {δs} {δt} h cb {Wl} wl wr r
    | no ne with otherL h Z ne
con★-var d n {Z = Z} z w {X} {α = α} {δs} {δt} h cb {Wl} wl wr r
    | no ne | γ , es , et , ne′ =
  ℰ-≡ d n (X⊑★ z) w δs (sym (↓-pk (makeConceal-other (δl δt X) es ne′)))
    refl
    (ℰ-steps? d n (X⊑★ z) w (goodS h) (step (id-conceal wl)) stay wl wr
      (to (𝒱-X★ d n z w)
        (leafRel-resp d n w (≈ˡ-sym (leafO h Z ne))
          (from (𝒱-X★ d n z w) r))))
con★-var d n {Z = .X} z w {X} {m-pair x α′} h cb wl wr r | yes refl =
  ⊥-elim (↔-only-⊥ x z)
con★-var d n {Z = .X} z w {X} {m-dead x} h cb wl wr r | yes refl =
  ⊥-elim (only-dead-⊥ z x)
con★-var d zero {Z = .X} z w {X} {m-only x} h cb wl wr r | yes refl =
  ℰ-zero d (X⊑★ z) w
con★-var ≺ (suc k) {Z = .X} z w {X} {m-only x} {α = α} {δs} {δt} h cb
    wl wr r | yes refl =
  ℰ-≡ ≺ (suc k) (X⊑★ z) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (αX h)))) refl
    (ℰ-value ≺ (suc k) (X⊑★ z) w (wl CT.↓ CT.seal) wr
      (onlyCon h (s≤s z≤n) cb
        (leafRel-down ≺ (n≤1+n k) w (goodT h X) r)))
con★-var ≻ (suc k) {Z = .X} z w {X} {m-only x} {α = α} {δs} {δt} h cb
    wl wr r | yes refl =
  ℰ-≡ ≻ (suc k) (X⊑★ z) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (αX h)))) refl
    (ℰ-value ≻ (suc k) (X⊑★ z) w (wl CT.↓ CT.seal) wr
      (onlyCon h (s≤s z≤n) cb r))
