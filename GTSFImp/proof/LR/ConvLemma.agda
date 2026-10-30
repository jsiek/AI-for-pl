module proof.LR.ConvLemma where

-- File Charter:
--   * The conversion lemma (notes/logrel-dgg.md, Section 6.9, item 5,
--     and Section 7, "Conversions: design"): a reveal turns values
--     related with a variable X as a store variable α (sealed values)
--     into values related with X as its representation, and the conceal
--     turns them back.
--   * Modes: X paired and the right converts too (`m-pair`), only the
--     left converts (`m-left`), X dead (`m-dead`), or no variable is α,
--     which is fresh (`m-none`, the closure of other leaves).
--   * Hypotheses (`ConvI`):
--       - X's two leaves are tied by `SealI`;
--       - every other leaf is closed under the conversion at hand
--         (`convP`, `convO`), and under conversions at store variables
--         created later (`genP`, `genO`, also for X's target leaf);
--       - the clauses' own leaves are closed below the bound (`Oracle`),
--         which `ConvClose` proves by induction on the stage.
--   * Two lemmas, each with a reveal and a conceal half, by induction on
--     the precision derivation: at derivations into `★` the right is
--     not converted; at the others it converts as the mode says.

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
open import proof.DGG.CenterRename using (toRenameᵗ-∘; _∘↪_)
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
open import proof.LR.ConvBase

private
  variable
    Δ Δ′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- Modes
------------------------------------------------------------------------

data CMode {Δ Δ′} (Φ : Corr Δ Δ′) (X : TyVar Δ) (ΘL ΘR : TyCtx) : Set where
  -- X is paired with Y, and the right converts its store variable α′
  m-pair : ∀ {Y} → Φ ∋ X ↔ Y → TyVar ΘR → CMode Φ X ΘL ΘR
  -- only the left converts; X is paired or left-only
  m-left : CMode Φ X ΘL ΘR
  -- X is dead
  m-dead : Φ ∋ X dead → CMode Φ X ΘL ΘR
  -- no variable is the converted one: the representation and the right
  -- side's conversion are given
  m-none : Ty ΘL → RConv ΘR → CMode Φ X ΘL ΘR

module _ {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  -- the left representation
  repM : CMode Φ X ΘL ΘR → (Δ ⇒ˢ ΘL) → Ty ΘL
  repM (m-pair x α′) σ = σ X
  repM m-left σ = σ X
  repM (m-dead x) σ = σ X
  repM (m-none R rc) σ = R

  -- the right side's conversion
  rconv : CMode Φ X ΘL ΘR → (Δ′ ⇒ˢ ΘR) → RConv ΘR
  rconv (m-pair {Y = Y} x α′) σ = just (α′ , σ Y)
  rconv m-left σ = nothing
  rconv (m-dead x) σ = nothing
  rconv (m-none R rc) σ = rc

  -- the variables that are not converted
  Other : CMode Φ X ΘL ΘR → TyVar Δ → Set
  Other (m-pair x α′) Z = Z ≢ X
  Other m-left Z = Z ≢ X
  Other (m-dead x) Z = Z ≢ X
  Other (m-none R rc) Z = ⊤

  CMode-↑ : ∀ {ΘL′ ΘR′} → ΘL ↪ᵗ ΘL′ → ΘR ↪ᵗ ΘR′ → CMode Φ X ΘL ΘR
    → CMode Φ X ΘL′ ΘR′
  CMode-↑ ρL ρR (m-pair x α′) = m-pair x (toRenameᵗ ρR α′)
  CMode-↑ ρL ρR m-left = m-left
  CMode-↑ ρL ρR (m-dead x) = m-dead x
  CMode-↑ ρL ρR (m-none R rc) =
    m-none (renameᵗ (toRenameᵗ ρL) R) (renRConv ρR rc)

  repM-↑ : ∀ {ΘL′ ΘR′} (ρL : ΘL ↪ᵗ ΘL′) (ρR : ΘR ↪ᵗ ΘR′)
      (m : CMode Φ X ΘL ΘR) σ
    → repM (CMode-↑ ρL ρR m) (λ Z → renameᵗ (toRenameᵗ ρL) (σ Z))
      ≡ renameᵗ (toRenameᵗ ρL) (repM m σ)
  repM-↑ ρL ρR (m-pair x α′) σ = refl
  repM-↑ ρL ρR m-left σ = refl
  repM-↑ ρL ρR (m-dead x) σ = refl
  repM-↑ ρL ρR (m-none R rc) σ = refl

  rconv-↑ : ∀ {ΘL′ ΘR′} (ρL : ΘL ↪ᵗ ΘL′) (ρR : ΘR ↪ᵗ ΘR′)
      (m : CMode Φ X ΘL ΘR) σ
    → rconv (CMode-↑ ρL ρR m) (λ Y → renameᵗ (toRenameᵗ ρR) (σ Y))
      ≡ renRConv ρR (rconv m σ)
  rconv-↑ ρL ρR (m-pair x α′) σ = refl
  rconv-↑ ρL ρR m-left σ = refl
  rconv-↑ ρL ρR (m-dead x) σ = refl
  rconv-↑ ρL ρR (m-none R rc) σ = refl

-- under a binder
CMode-pair : ∀ {Φ : Corr Δ Δ′} {X} → CMode Φ X ΘL ΘR
  → CMode (pair Φ) (suc X) ΘL ΘR
CMode-pair (m-pair x α′) = m-pair (↔-pair x) α′
CMode-pair m-left = m-left
CMode-pair (m-dead x) = m-dead (dead-pair x)
CMode-pair (m-none R rc) = m-none R rc

CMode-only : ∀ {Φ : Corr Δ Δ′} {X} → CMode Φ X ΘL ΘR
  → CMode (only Φ) (suc X) ΘL ΘR
CMode-only (m-pair x α′) = m-pair (↔-only x) α′
CMode-only m-left = m-left
CMode-only (m-dead x) = m-dead (dead-only x)
CMode-only (m-none R rc) = m-none R rc

CMode-dead : ∀ {Φ : Corr Δ Δ′} {X} → CMode Φ X ΘL ΘR
  → CMode (dead Φ) (suc X) ΘL ΘR
CMode-dead (m-pair x α′) = m-pair (↔-dead x) α′
CMode-dead m-left = m-left
CMode-dead (m-dead x) = m-dead (dead-dead x)
CMode-dead (m-none R rc) = m-none R rc

------------------------------------------------------------------------
-- Closure under conversions at new store variables
------------------------------------------------------------------------

-- whether the right side may convert
data RK : Set where
  both left : RK

Allowed : ∀ {Θ} → RK → RConv Θ → Set
Allowed both rc = ⊤
Allowed left nothing = ⊤
Allowed left (just c) = ⊥

-- a store variable created after the extension's source
NewL : ∀ {w w′ : World} → w′ ⊒ w → TyVar (ΔL w′) → Set
NewL e β = ∀ X → toRenameᵗ (ρL e) X ≢ β

NewRC : ∀ {w w′ : World} → w′ ⊒ w → RConv (ΔR w′) → Set
NewRC e nothing = ⊤
NewRC e (just (β′ , R′)) = ∀ Y → toRenameᵗ (ρR e) Y ≢ β′

-- the expression closure of a leaf
ℰL : Dir → ℕ → (w : World) → Leaf (ΔL w) (ΔR w)
  → Term (ΔL w) → Term (ΔR w) → Set
ℰL d n w L =
  ℰᵍ d n w (λ {n′} le w′ e → leafRel d n′ w′ (transportLeaf (ρL e) (ρR e) L))

-- a paired leaf with types T, T′, closed under later conversions
FreshP : Dir → RK → (w : World) → Leaf (ΔL w) (ΔR w)
  → Ty (ΔL w) → Ty (ΔR w) → Set
FreshP d rk w L T T′ =
  ∀ {w′} (e : w′ ⊒ w) {β R} (rc : RConv (ΔR w′)) → Allowed rk rc
  → NewL e β → NewRC e rc → ∀ {k}
  → (∀ {Vl Vr} → Value Vl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) L) Vl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) L)
           (Vl ↑ 〖 β , R ↑ renameᵗ (toRenameᵗ (ρL e)) T 〗)
           (revM rc (renameᵗ (toRenameᵗ (ρR e)) T′) Vr))
    × (∀ {Wl Wr} → Value Wl → Value Wr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) L) Wl Wr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) L)
           (Wl ↓ makeConceal β R (renameᵗ (toRenameᵗ (ρL e)) T))
           (conM rc (renameᵗ (toRenameᵗ (ρR e)) T′) Wr))

-- a left-only leaf with type T: the right does not move
FreshO : Dir → (w : World) → Leaf (ΔL w) (ΔR w) → Ty (ΔL w) → Set
FreshO d w L T =
  ∀ {w′} (e : w′ ⊒ w) {β R} → NewL e β → ∀ {k}
  → (∀ {Vl Vr} → Value Vl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) L) Vl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) L)
           (Vl ↑ 〖 β , R ↑ renameᵗ (toRenameᵗ (ρL e)) T 〗) Vr)
    × (∀ {Wl Vr} → Value Wl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) L) Wl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) L)
           (Wl ↓ makeConceal β R (renameᵗ (toRenameᵗ (ρL e)) T)) Vr)

-- the clauses' leaves, for bounds up to N
Oracle : Dir → ℕ → Set
Oracle d N =
  (∀ {w} {n′ n} (le : n′ ≤′ n) → n′ ≤ N → (c : SDesc (ΔL w) (ΔR w))
     → FreshP d both w (sem (leafBelowS d le c)) (leftTyS c) (rightTyS c))
  × (∀ {w} {n′ n} (le : n′ ≤′ n) → n′ ≤ N → (c : Desc (ΔL w) (ΔR w))
     → FreshO d w (sem (onlyLeaf d le c)) (leftTy c))

------------------------------------------------------------------------
-- The hypotheses
------------------------------------------------------------------------

replaceRC : ∀ {Θ} → RConv Θ → Ty Θ → Ty Θ
replaceRC nothing T = T
replaceRC (just (α′ , R)) T = replaceTy α′ R T

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  -- the converted variable's types under δs
  SelfI : ∀ {ΘL ΘR} → CMode Φ X ΘL ΘR → TyVar ΘL
    → (δs : Interp Δ Δ′ ΘL ΘR) → Set
  SelfI (m-pair {Y = Y} x α′) α δs = δl δs X ≡ ＇ α × δr δs Y ≡ ＇ α′
  SelfI m-left α δs = δl δs X ≡ ＇ α
  SelfI (m-dead x) α δs = δl δs X ≡ ＇ α
  SelfI (m-none R rc) α δs = ⊤

  -- X's leaves, in every future: the converted side's leaf (δs) holds of
  -- sealed values whose contents the target leaf (δt) relates
  SealI : Dir → ℕ → (w : World) → CMode Φ X (ΔL w) (ΔR w) → TyVar (ΔL w)
    → (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) → Set
  SealI d N w (m-pair {Y = Y} x α′) α δs δt =
    (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X) Vl Vr
       → sealedL (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X)
           (sealedR (toRenameᵗ (ρR e) α′) (δr (δt ↑ᴵ e) Y)
             (leafRel d (pred k) w′ (leaf (δt ↑ᴵ e) X))) Vl Vr)
    × (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k < N → ∀ {Wl Wr}
       → leafRel d k w′ (leaf (δt ↑ᴵ e) X) Wl Wr
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X)
           (Wl ↓ seal (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X))
           (Wr ↓ seal (toRenameᵗ (ρR e) α′) (δr (δt ↑ᴵ e) Y)))
  SealI d N w m-left α δs δt =
    (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X) Vl Vr
       → sealedL (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X)
           (leafRel d (onlyStage d k) w′ (leaf (δt ↑ᴵ e) X)) Vl Vr)
    × (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → onlyBelow d k N → ∀ {Wl Vr}
       → leafRel d k w′ (leaf (δt ↑ᴵ e) X) Wl Vr
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X)
           (Wl ↓ seal (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X)) Vr)
  SealI d N w (m-dead x) α δs δt = ⊤
  SealI d N w (m-none R rc) α δs δt = ⊤

  -- an other variable's leaf, under the conversion at hand, in every
  -- future
  ConvP : Dir → ℕ → (w : World) → CMode Φ X (ΔL w) (ΔR w) → TyVar (ΔL w)
    → (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) → ∀ {Z Y′} → Φ ∋ Z ↔ Y′ → Set
  ConvP d N w m α δs δt {Z} {Y′} z =
    ∀ {w′} (e : w′ ⊒ w) {k} → k ≤ N
    → (∀ {Vl Vr} → Value Vl → Value Vr
         → leafRel d k w′ (leaf (δs ↑ᴵ e) Z) Vl Vr
         → ℰ d k (X⊑Y z) w′ (δt ↑ᴵ e)
             (Vl ↑ 〖 toRenameᵗ (ρL e) α
                   , renameᵗ (toRenameᵗ (ρL e)) (repM m (δl δt))
                   ↑ δl (δs ↑ᴵ e) Z 〗)
             (revM (renRConv (ρR e) (rconv m (δr δt)))
               (δr (δs ↑ᴵ e) Y′) Vr))
      × (∀ {Wl Wr} → Value Wl → Value Wr
         → leafRel d k w′ (leaf (δt ↑ᴵ e) Z) Wl Wr
         → ℰ d k (X⊑Y z) w′ (δs ↑ᴵ e)
             (Wl ↓ makeConceal (toRenameᵗ (ρL e) α)
                     (renameᵗ (toRenameᵗ (ρL e)) (repM m (δl δt)))
                     (δl (δs ↑ᴵ e) Z))
             (conM (renRConv (ρR e) (rconv m (δr δt)))
               (δr (δs ↑ᴵ e) Y′) Wr))

  ConvO : Dir → ℕ → (w : World) → CMode Φ X (ΔL w) (ΔR w) → TyVar (ΔL w)
    → (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) → ∀ {Z} → Φ ∋ Z only → Set
  ConvO d N w m α δs δt {Z} z =
    ∀ {w′} (e : w′ ⊒ w) {k} → k ≤ N
    → (∀ {Vl Vr} → Value Vl → Value Vr
         → leafRel d k w′ (leaf (δs ↑ᴵ e) Z) Vl Vr
         → ℰ d k (X⊑★ z) w′ (δt ↑ᴵ e)
             (Vl ↑ 〖 toRenameᵗ (ρL e) α
                   , renameᵗ (toRenameᵗ (ρL e)) (repM m (δl δt))
                   ↑ δl (δs ↑ᴵ e) Z 〗) Vr)
      × (∀ {Wl Vr} → Value Wl → Value Vr
         → leafRel d k w′ (leaf (δt ↑ᴵ e) Z) Wl Vr
         → ℰ d k (X⊑★ z) w′ (δs ↑ᴵ e)
             (Wl ↓ makeConceal (toRenameᵗ (ρL e) α)
                     (renameᵗ (toRenameᵗ (ρL e)) (repM m (δl δt)))
                     (δl (δs ↑ᴵ e) Z)) Vr)

  record ConvI (d : Dir) (N : ℕ) (rk : RK) (w : World)
      (m : CMode Φ X (ΔL w) (ΔR w)) (α : TyVar (ΔL w))
      (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) : Set₁ where
    field
      goodS : GoodI δs
      goodT : GoodI δt
      selfI : SelfI m α δs
      rcOK : Allowed rk (rconv m (δr δt))
      tyL : ∀ Z → replaceTy α (repM m (δl δt)) (δl δs Z) ≡ δl δt Z
      tyR : ∀ Y′ → replaceRC (rconv m (δr δt)) (δr δs Y′) ≡ δr δt Y′
      leafO : ∀ Z → Other m Z → leaf δs Z ≈ˡ leaf δt Z
      convP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → Other m Z
        → ConvP d N w m α δs δt z
      convO : ∀ {Z} (z : Φ ∋ Z only) → Other m Z
        → ConvO d N w m α δs δt z
      genP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′)
        → FreshP d rk w (leaf δt Z) (δl δt Z) (δr δt Y′)
      genO : ∀ {Z} (z : Φ ∋ Z only)
        → FreshO d w (leaf δt Z) (δl δt Z)
      sealI : SealI d N w m α δs δt
      oracle : Oracle d N

  open ConvI public

------------------------------------------------------------------------
-- Equations on conversions and right sides
------------------------------------------------------------------------

↑〖〗-≡ : ∀ {Θ} {V : Term Θ} {α α′ : TyVar Θ} {R R′ T T′}
  → α ≡ α′ → R ≡ R′ → T ≡ T′ → V ↑ 〖 α , R ↑ T 〗 ≡ V ↑ 〖 α′ , R′ ↑ T′ 〗
↑〖〗-≡ refl refl refl = refl

↓mc-≡ : ∀ {Θ} {V : Term Θ} {α α′ : TyVar Θ} {R R′ T T′}
  → α ≡ α′ → R ≡ R′ → T ≡ T′
  → V ↓ makeConceal α R T ≡ V ↓ makeConceal α′ R′ T′
↓mc-≡ refl refl refl = refl

revM-≡ : ∀ {Θ} {V : Term Θ} {rc rc′ : RConv Θ} {T T′}
  → rc ≡ rc′ → T ≡ T′ → revM rc T V ≡ revM rc′ T′ V
revM-≡ refl refl = refl

conM-≡ : ∀ {Θ} {V : Term Θ} {rc rc′ : RConv Θ} {T T′}
  → rc ≡ rc′ → T ≡ T′ → conM rc T V ≡ conM rc′ T′ V
conM-≡ refl refl = refl

renRConv-∘ : ∀ {Θ₁ Θ₂ Θ₃} (π : Θ₂ ↪ᵗ Θ₃) (η : Θ₁ ↪ᵗ Θ₂) (rc : RConv Θ₁)
  → renRConv π (renRConv η rc) ≡ renRConv (π ∘↪ η) rc
renRConv-∘ π η nothing = refl
renRConv-∘ π η (just (α′ , R)) =
  cong₂ (λ a b → just (a , b)) (sym (toRenameᵗ-∘ π η α′)) (renameTy-∘ π η R)

Allowed-ren : ∀ {Θ Θ′} rk (ρ : Θ ↪ᵗ Θ′) (rc : RConv Θ)
  → Allowed rk rc → Allowed rk (renRConv ρ rc)
Allowed-ren both ρ rc ok = tt
Allowed-ren left ρ nothing ok = tt
Allowed-ren left ρ (just c) ()

replaceRC-ren : ∀ {Θ Θ′} (ρ : Θ ↪ᵗ Θ′) (rc : RConv Θ) T
  → replaceRC (renRConv ρ rc) (renameᵗ (toRenameᵗ ρ) T)
    ≡ renameᵗ (toRenameᵗ ρ) (replaceRC rc T)
replaceRC-ren ρ nothing T = refl
replaceRC-ren ρ (just (α′ , R)) T =
  sym (replaceTy-rename (toRenameᵗ ρ) (toRenameᵗ-injective ρ) α′ R T)

Other-↑ : ∀ {Φ : Corr Δ Δ′} {X} {ΘL′ ΘR′} (ρL : ΘL ↪ᵗ ΘL′)
    (ρR : ΘR ↪ᵗ ΘR′) (m : CMode Φ X ΘL ΘR) Z
  → Other (CMode-↑ ρL ρR m) Z → Other m Z
Other-↑ ρL ρR (m-pair x α′) Z o = o
Other-↑ ρL ρR m-left Z o = o
Other-↑ ρL ρR (m-dead x) Z o = o
Other-↑ ρL ρR (m-none R rc) Z o = o

ℰL-resp : ∀ d n w {L L′ : Leaf (ΔL w) (ΔR w)} {M M′}
  → L ≈ˡ L′ → ℰL d n w L M M′ → ℰL d n w L′ M M′
ℰL-resp d n w h =
  ℰᵍ-map d n w (λ le w′ e V V′ →
    leafRel-resp d _ w′ (transportLeaf-resp (ρL e) (ρR e) h))

ℰL-≡ : ∀ d n w (L : Leaf (ΔL w) (ΔR w)) {Ml Ml′ Mr Mr′}
  → Ml ≡ Ml′ → Mr ≡ Mr′ → ℰL d n w L Ml Mr → ℰL d n w L Ml′ Mr′
ℰL-≡ d n w L refl refl r = r

NewL-∘ : ∀ {w w′ w″ : World} (e′ : w″ ⊒ w′) (e : w′ ⊒ w) {β}
  → NewL e′ β → NewL (⊒-trans e′ e) β
NewL-∘ e′ e nb X eq =
  nb (toRenameᵗ (ρL e) X) (trans (sym (toRenameᵗ-∘ (ρL e′) (ρL e) X)) eq)

NewRC-∘ : ∀ {w w′ w″ : World} (e′ : w″ ⊒ w′) (e : w′ ⊒ w)
    (rc : RConv (ΔR w″))
  → NewRC e′ rc → NewRC (⊒-trans e′ e) rc
NewRC-∘ e′ e nothing nb = tt
NewRC-∘ e′ e (just (β′ , R′)) nb Y eq =
  nb (toRenameᵗ (ρR e) Y) (trans (sym (toRenameᵗ-∘ (ρR e′) (ρR e) Y)) eq)

------------------------------------------------------------------------
-- Closure moves to future worlds
------------------------------------------------------------------------

module _ {d} {w w′ : World} (e : w′ ⊒ w) {L : Leaf (ΔL w) (ΔR w)} where

  private
    L′ = transportLeaf (ρL e) (ρR e) L

  FreshP-↑ : ∀ {rk T T′} → FreshP d rk w L T T′
    → FreshP d rk w′ L′ (renameᵗ (toRenameᵗ (ρL e)) T)
        (renameᵗ (toRenameᵗ (ρR e)) T′)
  FreshP-↑ {T = T} {T′} f {w″} e′ {β} {R} rc ok nb nrc {k} =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w″ (≈ˡ-sym L∘)
        (ℰL-≡ d k w″ L₂
          (cong (λ C → Vl ↑ 〖 β , R ↑ C 〗)
            (sym (renameTy-∘ (ρL e′) (ρL e) T)))
          (cong (λ C → revM rc C Vr) (sym (renameTy-∘ (ρR e′) (ρR e) T′)))
          (proj₁ g vl vr (leafRel-resp d k w″ L∘ r)))) ,
    (λ {Wl} {Wr} wl wr r →
      ℰL-resp d k w″ (≈ˡ-sym L∘)
        (ℰL-≡ d k w″ L₂
          (cong (λ C → Wl ↓ makeConceal β R C)
            (sym (renameTy-∘ (ρL e′) (ρL e) T)))
          (cong (λ C → conM rc C Wr) (sym (renameTy-∘ (ρR e′) (ρR e) T′)))
          (proj₂ g wl wr (leafRel-resp d k w″ L∘ r))))
    where
    L∘ = transportLeaf-∘ (ρL e′) (ρL e) (ρR e′) (ρR e) L
    L₂ = transportLeaf (ρL e′ ∘↪ ρL e) (ρR e′ ∘↪ ρR e) L
    g = f (⊒-trans e′ e) rc ok (NewL-∘ e′ e nb) (NewRC-∘ e′ e rc nrc) {k}

  FreshO-↑ : ∀ {T} → FreshO d w L T
    → FreshO d w′ L′ (renameᵗ (toRenameᵗ (ρL e)) T)
  FreshO-↑ {T = T} f {w″} e′ {β} {R} nb {k} =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w″ (≈ˡ-sym L∘)
        (ℰL-≡ d k w″ L₂
          (cong (λ C → Vl ↑ 〖 β , R ↑ C 〗)
            (sym (renameTy-∘ (ρL e′) (ρL e) T)))
          refl
          (proj₁ g vl vr (leafRel-resp d k w″ L∘ r)))) ,
    (λ {Wl} {Vr} wl vr r →
      ℰL-resp d k w″ (≈ˡ-sym L∘)
        (ℰL-≡ d k w″ L₂
          (cong (λ C → Wl ↓ makeConceal β R C)
            (sym (renameTy-∘ (ρL e′) (ρL e) T)))
          refl
          (proj₂ g wl vr (leafRel-resp d k w″ L∘ r))))
    where
    L∘ = transportLeaf-∘ (ρL e′) (ρL e) (ρR e′) (ρR e) L
    L₂ = transportLeaf (ρL e′ ∘↪ ρL e) (ρR e′ ∘↪ ρR e) L
    g = f (⊒-trans e′ e) (NewL-∘ e′ e nb) {k}

------------------------------------------------------------------------
-- The hypotheses move to future worlds
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ}
    {rk : RK} {w w′ : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    (e : w′ ⊒ w) where

  private
    ρl = toRenameᵗ (ρL e)
    ρr = toRenameᵗ (ρR e)

  SelfI-↑ : ∀ (m : CMode Φ X (ΔL w) (ΔR w)) α → SelfI m α δs
    → SelfI (CMode-↑ (ρL e) (ρR e) m) (ρl α) (δs ↑ᴵ e)
  SelfI-↑ (m-pair x α′) α (a , b) = cong (renameᵗ ρl) a , cong (renameᵗ ρr) b
  SelfI-↑ m-left α a = cong (renameᵗ ρl) a
  SelfI-↑ (m-dead x) α a = cong (renameᵗ ρl) a
  SelfI-↑ (m-none R rc) α a = tt

  -- the conversion at hand, in a future of the future
  module Comp (m : CMode Φ X (ΔL w) (ΔR w)) (α : TyVar (ΔL w))
      {w″} (e′ : w″ ⊒ w′) where

    α∘ : toRenameᵗ (ρL (⊒-trans e′ e)) α ≡ toRenameᵗ (ρL e′) (ρl α)
    α∘ = toRenameᵗ-∘ (ρL e′) (ρL e) α

    R∘ : renameᵗ (toRenameᵗ (ρL (⊒-trans e′ e))) (repM m (δl δt))
      ≡ renameᵗ (toRenameᵗ (ρL e′))
          (repM (CMode-↑ (ρL e) (ρR e) m) (δl (δt ↑ᴵ e)))
    R∘ = trans (sym (renameTy-∘ (ρL e′) (ρL e) (repM m (δl δt))))
      (cong (renameᵗ (toRenameᵗ (ρL e′)))
        (sym (repM-↑ (ρL e) (ρR e) m (δl δt))))

    rc∘ : renRConv (ρR (⊒-trans e′ e)) (rconv m (δr δt))
      ≡ renRConv (ρR e′) (rconv (CMode-↑ (ρL e) (ρR e) m) (δr (δt ↑ᴵ e)))
    rc∘ = trans (sym (renRConv-∘ (ρR e′) (ρR e) (rconv m (δr δt))))
      (cong (renRConv (ρR e′)) (sym (rconv-↑ (ρL e) (ρR e) m (δr δt))))

  ConvP-↑ : ∀ (m : CMode Φ X (ΔL w) (ΔR w)) α {Z Y′} (z : Φ ∋ Z ↔ Y′)
    → ConvP d N w m α δs δt z
    → ConvP d N w′ (CMode-↑ (ρL e) (ρR e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e) z
  ConvP-↑ m α {Z} {Y′} z h {w″} e′ {k} k≤N =
    (λ {Vl} {Vr} vl vr r →
      ℰ-resp d k (X⊑Y z) w″ (≈ᴵ-sym (↑ᴵ-trans δt e′ e))
        (ℰ-≡ d k (X⊑Y z) w″ (δt ↑ᴵ ⊒-trans e′ e)
          (↑〖〗-≡ (Comp.α∘ m α e′) (Comp.R∘ m α e′)
            (sym (δl≡ (↑ᴵ-trans δs e′ e) Z)))
          (revM-≡ (Comp.rc∘ m α e′) (sym (δr≡ (↑ᴵ-trans δs e′ e) Y′)))
          (proj₁ g vl vr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) Z) r)))) ,
    (λ {Wl} {Wr} wl wr r →
      ℰ-resp d k (X⊑Y z) w″ (≈ᴵ-sym (↑ᴵ-trans δs e′ e))
        (ℰ-≡ d k (X⊑Y z) w″ (δs ↑ᴵ ⊒-trans e′ e)
          (↓mc-≡ (Comp.α∘ m α e′) (Comp.R∘ m α e′)
            (sym (δl≡ (↑ᴵ-trans δs e′ e) Z)))
          (conM-≡ (Comp.rc∘ m α e′) (sym (δr≡ (↑ᴵ-trans δs e′ e) Y′)))
          (proj₂ g wl wr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δt e′ e) Z) r))))
    where
    g = h (⊒-trans e′ e) k≤N

  ConvO-↑ : ∀ (m : CMode Φ X (ΔL w) (ΔR w)) α {Z} (z : Φ ∋ Z only)
    → ConvO d N w m α δs δt z
    → ConvO d N w′ (CMode-↑ (ρL e) (ρR e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e) z
  ConvO-↑ m α {Z} z h {w″} e′ {k} k≤N =
    (λ {Vl} {Vr} vl vr r →
      ℰ-resp d k (X⊑★ z) w″ (≈ᴵ-sym (↑ᴵ-trans δt e′ e))
        (ℰ-≡ d k (X⊑★ z) w″ (δt ↑ᴵ ⊒-trans e′ e)
          (↑〖〗-≡ (Comp.α∘ m α e′) (Comp.R∘ m α e′)
            (sym (δl≡ (↑ᴵ-trans δs e′ e) Z)))
          refl
          (proj₁ g vl vr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) Z) r)))) ,
    (λ {Wl} {Vr} wl vr r →
      ℰ-resp d k (X⊑★ z) w″ (≈ᴵ-sym (↑ᴵ-trans δs e′ e))
        (ℰ-≡ d k (X⊑★ z) w″ (δs ↑ᴵ ⊒-trans e′ e)
          (↓mc-≡ (Comp.α∘ m α e′) (Comp.R∘ m α e′)
            (sym (δl≡ (↑ᴵ-trans δs e′ e) Z)))
          refl
          (proj₂ g wl vr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δt e′ e) Z) r))))
    where
    g = h (⊒-trans e′ e) k≤N

  SealI-↑ : ∀ (m : CMode Φ X (ΔL w) (ΔR w)) α → SealI d N w m α δs δt
    → SealI d N w′ (CMode-↑ (ρL e) (ρR e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e)
  SealI-↑ (m-pair {Y = Y} x α′) α (hrev , hcon) = rev′ , con′
    where
    rev′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
      → leafRel d k w″ (leaf ((δs ↑ᴵ e) ↑ᴵ e′) X) Vl Vr
      → sealedL (toRenameᵗ (ρL e′) (ρl α)) (δl ((δt ↑ᴵ e) ↑ᴵ e′) X)
          (sealedR (toRenameᵗ (ρR e′) (ρr α′)) (δr ((δt ↑ᴵ e) ↑ᴵ e′) Y)
            (leafRel d (pred k) w″ (leaf ((δt ↑ᴵ e) ↑ᴵ e′) X))) Vl Vr
    rev′ {w″} e′ {k} pos le r =
      sealedL-map (toRenameᵗ-∘ (ρL e′) (ρL e) α)
        (sym (δl≡ (↑ᴵ-trans δt e′ e) X))
        (sealedR-map (toRenameᵗ-∘ (ρR e′) (ρR e) α′)
          (sym (δr≡ (↑ᴵ-trans δt e′ e) Y))
          (leafRel-resp d (pred k) w″
            (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) X))))
        (hrev (⊒-trans e′ e) pos le
          (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) X) r))
    con′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → k < N → ∀ {Wl Wr}
      → leafRel d k w″ (leaf ((δt ↑ᴵ e) ↑ᴵ e′) X) Wl Wr
      → leafRel d k w″ (leaf ((δs ↑ᴵ e) ↑ᴵ e′) X)
          (Wl ↓ seal (toRenameᵗ (ρL e′) (ρl α)) (δl ((δt ↑ᴵ e) ↑ᴵ e′) X))
          (Wr ↓ seal (toRenameᵗ (ρR e′) (ρr α′)) (δr ((δt ↑ᴵ e) ↑ᴵ e′) Y))
    con′ {w″} e′ {k} pos lt {Wl} {Wr} r =
      leafRel-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) X))
        (subst₂ (leafRel d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) X))
          (cong₂ (λ a R → Wl ↓ seal a R) (toRenameᵗ-∘ (ρL e′) (ρL e) α)
            (sym (δl≡ (↑ᴵ-trans δt e′ e) X)))
          (cong₂ (λ a R → Wr ↓ seal a R) (toRenameᵗ-∘ (ρR e′) (ρR e) α′)
            (sym (δr≡ (↑ᴵ-trans δt e′ e) Y)))
          (hcon (⊒-trans e′ e) pos lt
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δt e′ e) X) r)))
  SealI-↑ m-left α (hrev , hcon) = rev′ , con′
    where
    rev′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
      → leafRel d k w″ (leaf ((δs ↑ᴵ e) ↑ᴵ e′) X) Vl Vr
      → sealedL (toRenameᵗ (ρL e′) (ρl α)) (δl ((δt ↑ᴵ e) ↑ᴵ e′) X)
          (leafRel d (onlyStage d k) w″ (leaf ((δt ↑ᴵ e) ↑ᴵ e′) X)) Vl Vr
    rev′ {w″} e′ {k} pos le r =
      sealedL-map (toRenameᵗ-∘ (ρL e′) (ρL e) α)
        (sym (δl≡ (↑ᴵ-trans δt e′ e) X))
        (leafRel-resp d (onlyStage d k) w″
          (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) X)))
        (hrev (⊒-trans e′ e) pos le
          (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) X) r))
    con′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → onlyBelow d k N
      → ∀ {Wl Vr} → leafRel d k w″ (leaf ((δt ↑ᴵ e) ↑ᴵ e′) X) Wl Vr
      → leafRel d k w″ (leaf ((δs ↑ᴵ e) ↑ᴵ e′) X)
          (Wl ↓ seal (toRenameᵗ (ρL e′) (ρl α)) (δl ((δt ↑ᴵ e) ↑ᴵ e′) X)) Vr
    con′ {w″} e′ {k} pos lt {Wl} {Vr} r =
      leafRel-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) X))
        (subst (λ V → leafRel d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) X) V Vr)
          (cong₂ (λ a R → Wl ↓ seal a R) (toRenameᵗ-∘ (ρL e′) (ρL e) α)
            (sym (δl≡ (↑ᴵ-trans δt e′ e) X)))
          (hcon (⊒-trans e′ e) pos lt
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δt e′ e) X) r)))
  SealI-↑ (m-dead x) α h = tt
  SealI-↑ (m-none R rc) α h = tt

  ConvI-↑ : ∀ {m : CMode Φ X (ΔL w) (ΔR w)} {α}
    → ConvI d N rk w m α δs δt
    → ConvI d N rk w′ (CMode-↑ (ρL e) (ρR e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e)
  goodS (ConvI-↑ h) = GoodI-↑ {δ = δs} (goodS h) e
  goodT (ConvI-↑ h) = GoodI-↑ {δ = δt} (goodT h) e
  selfI (ConvI-↑ {m = m} {α} h) = SelfI-↑ m α (selfI h)
  rcOK (ConvI-↑ {m = m} h) =
    subst (Allowed rk) (sym (rconv-↑ (ρL e) (ρR e) m (δr δt)))
      (Allowed-ren rk (ρR e) (rconv m (δr δt)) (rcOK h))
  tyL (ConvI-↑ {m = m} {α} h) Z =
    trans (cong (λ R → replaceTy (ρl α) R (renameᵗ ρl (δl δs Z)))
            (repM-↑ (ρL e) (ρR e) m (δl δt)))
      (trans (sym (replaceTy-rename ρl (toRenameᵗ-injective (ρL e)) α
               (repM m (δl δt)) (δl δs Z)))
        (cong (renameᵗ ρl) (tyL h Z)))
  tyR (ConvI-↑ {m = m} h) Y′ =
    trans (cong (λ c → replaceRC c (renameᵗ ρr (δr δs Y′)))
            (rconv-↑ (ρL e) (ρR e) m (δr δt)))
      (trans (replaceRC-ren (ρR e) (rconv m (δr δt)) (δr δs Y′))
        (cong (renameᵗ ρr) (tyR h Y′)))
  leafO (ConvI-↑ {m = m} h) Z o =
    transportLeaf-resp (ρL e) (ρR e)
      (leafO h Z (Other-↑ (ρL e) (ρR e) m Z o))
  convP (ConvI-↑ {m = m} {α} h) {Z} z o =
    ConvP-↑ m α z (convP h z (Other-↑ (ρL e) (ρR e) m Z o))
  convO (ConvI-↑ {m = m} {α} h) {Z} z o =
    ConvO-↑ m α z (convO h z (Other-↑ (ρL e) (ρR e) m Z o))
  genP (ConvI-↑ h) {Z} {Y′} z =
    FreshP-↑ {d = d} e {L = leaf δt Z} {rk} {δl δt Z} {δr δt Y′} (genP h z)
  genO (ConvI-↑ h) {Z} z =
    FreshO-↑ {d = d} e {L = leaf δt Z} {δl δt Z} (genO h z)
  sealI (ConvI-↑ {m = m} {α} h) = SealI-↑ m α (sealI h)
  oracle (ConvI-↑ h) = oracle h
