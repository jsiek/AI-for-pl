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
open import proof.LR.PrecisionUnique using (↔-unique)

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
-- A leaf under the conversion at hand
------------------------------------------------------------------------

-- the converted leaf Ls and the target leaf Lt of a variable whose
-- types are T and T′, under the conversion at α with representation R
-- and the right side's conversion rc, in every future
ConvLeafP : Dir → ℕ → (w : World) → Ty (ΔL w) → RConv (ΔR w)
  → TyVar (ΔL w) → (Ls Lt : Leaf (ΔL w) (ΔR w))
  → Ty (ΔL w) → Ty (ΔR w) → Set
ConvLeafP d N w R rc α Ls Lt T T′ =
  ∀ {w′} (e : w′ ⊒ w) {k} → k ≤ N
  → (∀ {Vl Vr} → Value Vl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls) Vl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) Lt)
           (Vl ↑ 〖 toRenameᵗ (ρL e) α , renameᵗ (toRenameᵗ (ρL e)) R
                 ↑ renameᵗ (toRenameᵗ (ρL e)) T 〗)
           (revM (renRConv (ρR e) rc) (renameᵗ (toRenameᵗ (ρR e)) T′) Vr))
    × (∀ {Wl Wr} → Value Wl → Value Wr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Lt) Wl Wr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) Ls)
           (Wl ↓ makeConceal (toRenameᵗ (ρL e) α)
                   (renameᵗ (toRenameᵗ (ρL e)) R)
                   (renameᵗ (toRenameᵗ (ρL e)) T))
           (conM (renRConv (ρR e) rc) (renameᵗ (toRenameᵗ (ρR e)) T′) Wr))

ConvLeafO : Dir → ℕ → (w : World) → Ty (ΔL w) → TyVar (ΔL w)
  → (Ls Lt : Leaf (ΔL w) (ΔR w)) → Ty (ΔL w) → Set
ConvLeafO d N w R α Ls Lt T =
  ∀ {w′} (e : w′ ⊒ w) {k} → k ≤ N
  → (∀ {Vl Vr} → Value Vl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls) Vl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) Lt)
           (Vl ↑ 〖 toRenameᵗ (ρL e) α , renameᵗ (toRenameᵗ (ρL e)) R
                 ↑ renameᵗ (toRenameᵗ (ρL e)) T 〗) Vr)
    × (∀ {Wl Vr} → Value Wl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Lt) Wl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) Ls)
           (Wl ↓ makeConceal (toRenameᵗ (ρL e) α)
                   (renameᵗ (toRenameᵗ (ρL e)) R)
                   (renameᵗ (toRenameᵗ (ρL e)) T)) Vr)

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
    ConvLeafP d N w (repM m (δl δt)) (rconv m (δr δt)) α
      (leaf δs Z) (leaf δt Z) (δl δs Z) (δr δs Y′)

  ConvO : Dir → ℕ → (w : World) → CMode Φ X (ΔL w) (ΔR w) → TyVar (ΔL w)
    → (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) → ∀ {Z} → Φ ∋ Z only → Set
  ConvO d N w m α δs δt {Z} z =
    ConvLeafO d N w (repM m (δl δt)) α (leaf δs Z) (leaf δt Z) (δl δs Z)

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
      ℰL-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) Z))
        (ℰL-≡ d k w″ (leaf (δt ↑ᴵ ⊒-trans e′ e) Z)
          (↑〖〗-≡ (Comp.α∘ m α e′) (Comp.R∘ m α e′)
            (sym (δl≡ (↑ᴵ-trans δs e′ e) Z)))
          (revM-≡ (Comp.rc∘ m α e′) (sym (δr≡ (↑ᴵ-trans δs e′ e) Y′)))
          (proj₁ g vl vr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) Z) r)))) ,
    (λ {Wl} {Wr} wl wr r →
      ℰL-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) Z))
        (ℰL-≡ d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) Z)
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
      ℰL-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) Z))
        (ℰL-≡ d k w″ (leaf (δt ↑ᴵ ⊒-trans e′ e) Z)
          (↑〖〗-≡ (Comp.α∘ m α e′) (Comp.R∘ m α e′)
            (sym (δl≡ (↑ᴵ-trans δs e′ e) Z)))
          refl
          (proj₁ g vl vr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) Z) r)))) ,
    (λ {Wl} {Vr} wl vr r →
      ℰL-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) Z))
        (ℰL-≡ d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) Z)
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

------------------------------------------------------------------------
-- A leaf's expression closure, at a variable
------------------------------------------------------------------------

ℰL→XY : ∀ d n {Φ : Corr Δ Δ′} {Z Y′} (z : Φ ∋ Z ↔ Y′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {M M′}
  → ℰL d n w (leaf δ Z) M M′ → ℰ d n (X⊑Y z) w δ M M′
ℰL→XY d n z w =
  ℰᵍ-map d n w (λ le w′ e V V′ r →
    𝒱≤-cast d ≤′-refl le (X⊑Y z) w′ (to (𝒱-XY d _ z w′) r))

XY→ℰL : ∀ d n {Φ : Corr Δ Δ′} {Z Y′} (z : Φ ∋ Z ↔ Y′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {M M′}
  → ℰ d n (X⊑Y z) w δ M M′ → ℰL d n w (leaf δ Z) M M′
XY→ℰL d n z w =
  ℰᵍ-map d n w (λ le w′ e V V′ r →
    from (𝒱-XY d _ z w′) (𝒱≤-cast d le ≤′-refl (X⊑Y z) w′ r))

ℰL→X★ : ∀ d n {Φ : Corr Δ Δ′} {Z} (z : Φ ∋ Z only) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {M M′}
  → ℰL d n w (leaf δ Z) M M′ → ℰ d n (X⊑★ z) w δ M M′
ℰL→X★ d n z w =
  ℰᵍ-map d n w (λ le w′ e V V′ r →
    𝒱≤-cast d ≤′-refl le (X⊑★ z) w′ (to (𝒱-X★ d _ z w′) r))

X★→ℰL : ∀ d n {Φ : Corr Δ Δ′} {Z} (z : Φ ∋ Z only) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {M M′}
  → ℰ d n (X⊑★ z) w δ M M′ → ℰL d n w (leaf δ Z) M M′
X★→ℰL d n z w =
  ℰᵍ-map d n w (λ le w′ e V V′ r →
    from (𝒱-X★ d _ z w′) (𝒱≤-cast d le ≤′-refl (X⊑★ z) w′ r))

------------------------------------------------------------------------
-- Leaves at store variables: a conversion is an identity step
------------------------------------------------------------------------

-- the right side's conversion is absent, or at another store variable
RId : ∀ {Θ} → RConv Θ → Ty Θ → Set
RId {Θ} nothing T′ = ⊤
RId {Θ} (just (α′ , R′)) T′ = Σ[ γ′ ∈ TyVar Θ ] (T′ ≡ ＇ γ′ × γ′ ≢ α′)

rstep : ∀ {Θ} (rc : RConv Θ) {T′} → RId rc T′ → ∀ {V : Term Θ}
  → Value V → revM rc T′ V —→? V
rstep nothing tt v = stay
rstep (just (α′ , R′)) (γ′ , eq , ne) {V} v =
  subst (λ M → M —→? V) (sym (↑-pk (〖〗-other R′ eq ne)))
    (step (id-reveal v))

cstep : ∀ {Θ} (rc : RConv Θ) {T′} → RId rc T′ → ∀ {V : Term Θ}
  → Value V → conM rc T′ V —→? V
cstep nothing tt v = stay
cstep (just (α′ , R′)) (γ′ , eq , ne) {V} v =
  subst (λ M → M —→? V) (sym (↓-pk (makeConceal-other R′ eq ne)))
    (step (id-conceal v))

-- the leaf is read as the only variable of an interpretation
module _ (d : Dir) (k : ℕ) (w : World) (L : Leaf (ΔL w) (ΔR w))
    (gl : GoodLeaf L) where

  idRevP : ∀ {α γ : TyVar (ΔL w)} {R} → γ ≢ α → (rc : RConv (ΔR w))
    → ∀ {T′} → RId rc T′ → ∀ {Vl Vr} → Value Vl → Value Vr
    → leafRel d k w L Vl Vr
    → ℰL d k w L (Vl ↑ 〖 α , R ↑ ＇ γ 〗) (revM rc T′ Vr)
  idRevP {α} {γ} {R} ne rc {T′} ri {Vl} vl vr r =
    XY→ℰL d k (↔-here {Φ = []}) w {δ = extPairI (＇ γ) T′ L closedI}
      (ℰ-≡ d k (X⊑Y ↔-here) w (extPairI (＇ γ) T′ L closedI)
        (sym (↑-pk (〖〗-other R refl ne))) refl
        (ℰ-steps? d k (X⊑Y ↔-here) w
          (GoodI-extPairI {T = ＇ γ} {T′ = T′} {δ = closedI} gl good-closedI)
          (step (id-reveal vl)) (rstep rc ri vr) vl vr
          (to (𝒱-XY d k ↔-here w) r)))

  idConP : ∀ {α γ : TyVar (ΔL w)} {R} → γ ≢ α → (rc : RConv (ΔR w))
    → ∀ {T′} → RId rc T′ → ∀ {Wl Wr} → Value Wl → Value Wr
    → leafRel d k w L Wl Wr
    → ℰL d k w L (Wl ↓ makeConceal α R (＇ γ)) (conM rc T′ Wr)
  idConP {α} {γ} {R} ne rc {T′} ri {Wl} wl wr r =
    XY→ℰL d k (↔-here {Φ = []}) w {δ = extPairI (＇ γ) T′ L closedI}
      (ℰ-≡ d k (X⊑Y ↔-here) w (extPairI (＇ γ) T′ L closedI)
        (sym (↓-pk (makeConceal-other R refl ne)))
        refl
        (ℰ-steps? d k (X⊑Y ↔-here) w
          (GoodI-extPairI {T = ＇ γ} {T′ = T′} {δ = closedI} gl good-closedI)
          (step (id-conceal wl)) (cstep rc ri wr) wl wr
          (to (𝒱-XY d k ↔-here w) r)))

  idRevO : ∀ {α γ : TyVar (ΔL w)} {R} → γ ≢ α → ∀ {Vl Vr}
    → Value Vl → Value Vr → leafRel d k w L Vl Vr
    → ℰL d k w L (Vl ↑ 〖 α , R ↑ ＇ γ 〗) Vr
  idRevO {α} {γ} {R} ne {Vl} vl vr r =
    X★→ℰL d k (only-here {Φ = []}) w {δ = extOnlyI (＇ γ) L closedI}
      (ℰ-≡ d k (X⊑★ only-here) w (extOnlyI (＇ γ) L closedI)
        (sym (↑-pk (〖〗-other R refl ne))) refl
        (ℰ-steps? d k (X⊑★ only-here) w
          (GoodI-extOnlyI {T = ＇ γ} {δ = closedI} gl good-closedI)
          (step (id-reveal vl)) stay vl vr (to (𝒱-X★ d k only-here w) r)))

  idConO : ∀ {α γ : TyVar (ΔL w)} {R} → γ ≢ α → ∀ {Wl Vr}
    → Value Wl → Value Vr → leafRel d k w L Wl Vr
    → ℰL d k w L (Wl ↓ makeConceal α R (＇ γ)) Vr
  idConO {α} {γ} {R} ne {Wl} wl vr r =
    X★→ℰL d k (only-here {Φ = []}) w {δ = extOnlyI (＇ γ) L closedI}
      (ℰ-≡ d k (X⊑★ only-here) w (extOnlyI (＇ γ) L closedI)
        (sym (↓-pk (makeConceal-other R refl ne))) refl
        (ℰ-steps? d k (X⊑★ only-here) w
          (GoodI-extOnlyI {T = ＇ γ} {δ = closedI} gl good-closedI)
          (step (id-conceal wl)) stay wl vr (to (𝒱-X★ d k only-here w) r)))

------------------------------------------------------------------------
-- Modes under binders
------------------------------------------------------------------------

module _ {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  repM-pair : ∀ (m : CMode Φ X ΘL ΘR) σ T
    → repM (CMode-pair m) (T •ˢ σ) ≡ repM m σ
  repM-pair (m-pair x α′) σ T = refl
  repM-pair m-left σ T = refl
  repM-pair (m-dead x) σ T = refl
  repM-pair (m-none R rc) σ T = refl

  repM-only : ∀ (m : CMode Φ X ΘL ΘR) σ T
    → repM (CMode-only m) (T •ˢ σ) ≡ repM m σ
  repM-only (m-pair x α′) σ T = refl
  repM-only m-left σ T = refl
  repM-only (m-dead x) σ T = refl
  repM-only (m-none R rc) σ T = refl

  repM-dead : ∀ (m : CMode Φ X ΘL ΘR) σ T
    → repM (CMode-dead m) (T •ˢ σ) ≡ repM m σ
  repM-dead (m-pair x α′) σ T = refl
  repM-dead m-left σ T = refl
  repM-dead (m-dead x) σ T = refl
  repM-dead (m-none R rc) σ T = refl

  rconv-pair : ∀ (m : CMode Φ X ΘL ΘR) σ T′
    → rconv (CMode-pair m) (T′ •ˢ σ) ≡ rconv m σ
  rconv-pair (m-pair x α′) σ T′ = refl
  rconv-pair m-left σ T′ = refl
  rconv-pair (m-dead x) σ T′ = refl
  rconv-pair (m-none R rc) σ T′ = refl

  rconv-only : ∀ (m : CMode Φ X ΘL ΘR) σ
    → rconv (CMode-only m) σ ≡ rconv m σ
  rconv-only (m-pair x α′) σ = refl
  rconv-only m-left σ = refl
  rconv-only (m-dead x) σ = refl
  rconv-only (m-none R rc) σ = refl

  rconv-dead : ∀ (m : CMode Φ X ΘL ΘR) σ
    → rconv (CMode-dead m) σ ≡ rconv m σ
  rconv-dead (m-pair x α′) σ = refl
  rconv-dead m-left σ = refl
  rconv-dead (m-dead x) σ = refl
  rconv-dead (m-none R rc) σ = refl

  Other-pair : ∀ (m : CMode Φ X ΘL ΘR) Z
    → Other (CMode-pair m) (suc Z) → Other m Z
  Other-pair (m-pair x α′) Z o = λ eq → o (cong suc eq)
  Other-pair m-left Z o = λ eq → o (cong suc eq)
  Other-pair (m-dead x) Z o = λ eq → o (cong suc eq)
  Other-pair (m-none R rc) Z o = tt

  Other-only : ∀ (m : CMode Φ X ΘL ΘR) Z
    → Other (CMode-only m) (suc Z) → Other m Z
  Other-only (m-pair x α′) Z o = λ eq → o (cong suc eq)
  Other-only m-left Z o = λ eq → o (cong suc eq)
  Other-only (m-dead x) Z o = λ eq → o (cong suc eq)
  Other-only (m-none R rc) Z o = tt

  Other-dead : ∀ (m : CMode Φ X ΘL ΘR) Z
    → Other (CMode-dead m) (suc Z) → Other m Z
  Other-dead (m-pair x α′) Z o = λ eq → o (cong suc eq)
  Other-dead m-left Z o = λ eq → o (cong suc eq)
  Other-dead (m-dead x) Z o = λ eq → o (cong suc eq)
  Other-dead (m-none R rc) Z o = tt

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ}
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {α : TyVar (ΔL w)}
    {T : Ty (ΔL w)} {l : Leaf (ΔL w) (ΔR w)} where

  SealI-pair : ∀ (m : CMode Φ X (ΔL w) (ΔR w)) {T′}
    → SealI d N w m α δs δt
    → SealI d N w (CMode-pair m) α (extPairI T T′ l δs) (extPairI T T′ l δt)
  SealI-pair (m-pair x α′) h = h
  SealI-pair m-left h = h
  SealI-pair (m-dead x) h = h
  SealI-pair (m-none R rc) h = h

  SealI-only : ∀ (m : CMode Φ X (ΔL w) (ΔR w))
    → SealI d N w m α δs δt
    → SealI d N w (CMode-only m) α (extOnlyI T l δs) (extOnlyI T l δt)
  SealI-only (m-pair x α′) h = h
  SealI-only m-left h = h
  SealI-only (m-dead x) h = h
  SealI-only (m-none R rc) h = h

  SealI-dead : ∀ (m : CMode Φ X (ΔL w) (ΔR w))
    → SealI d N w m α δs δt
    → SealI d N w (CMode-dead m) α (extDeadI T δs) (extDeadI T δt)
  SealI-dead (m-pair x α′) h = h
  SealI-dead m-left h = h
  SealI-dead (m-dead x) h = h
  SealI-dead (m-none R rc) h = h


SelfI-pair : ∀ {Φ : Corr Δ Δ′} {X} (m : CMode Φ X ΘL ΘR) {α}
    {δs : Interp Δ Δ′ ΘL ΘR} {T T′ l}
  → SelfI m α δs → SelfI (CMode-pair m) α (extPairI T T′ l δs)
SelfI-pair (m-pair x α′) h = h
SelfI-pair m-left h = h
SelfI-pair (m-dead x) h = h
SelfI-pair (m-none R rc) h = h

SelfI-only : ∀ {Φ : Corr Δ Δ′} {X} (m : CMode Φ X ΘL ΘR) {α}
    {δs : Interp Δ Δ′ ΘL ΘR} {T l}
  → SelfI m α δs → SelfI (CMode-only m) α (extOnlyI T l δs)
SelfI-only (m-pair x α′) h = h
SelfI-only m-left h = h
SelfI-only (m-dead x) h = h
SelfI-only (m-none R rc) h = h

SelfI-dead : ∀ {Φ : Corr Δ Δ′} {X} (m : CMode Φ X ΘL ΘR) {α}
    {δs : Interp Δ Δ′ ΘL ΘR} {T}
  → SelfI m α δs → SelfI (CMode-dead m) α (extDeadI T δs)
SelfI-dead (m-pair x α′) h = h
SelfI-dead m-left h = h
SelfI-dead (m-dead x) h = h
SelfI-dead (m-none R rc) h = h

------------------------------------------------------------------------
-- The hypotheses under binders
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ} {rk : RK}
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {β : TyVar (ΔL w)}
    {l : Leaf (ΔL w) (ΔR w)} where

  -- a paired binder: the new variable is the store variable β on the
  -- left, of type T′ on the right, with the same leaf on both sides
  ConvI-extPair : ∀ {m : CMode Φ X (ΔL w) (ΔR w)} {α} {T′ : Ty (ΔR w)}
    → GoodLeaf l → β ≢ α → replaceRC (rconv m (δr δt)) T′ ≡ T′
    → ConvLeafP d N w (repM m (δl δt)) (rconv m (δr δt)) α l l (＇ β) T′
    → FreshP d rk w l (＇ β) T′
    → ConvI d N rk w m α δs δt
    → ConvI d N rk w (CMode-pair m) α
        (extPairI (＇ β) T′ l δs) (extPairI (＇ β) T′ l δt)
  goodS (ConvI-extPair {T′ = T′} gl ne tr cv fr h) =
    GoodI-extPairI {T = ＇ β} {T′ = T′} {δ = δs} gl (goodS h)
  goodT (ConvI-extPair {T′ = T′} gl ne tr cv fr h) =
    GoodI-extPairI {T = ＇ β} {T′ = T′} {δ = δt} gl (goodT h)
  selfI (ConvI-extPair {m = m} {T′ = T′} gl ne tr cv fr h) =
    SelfI-pair m {T = ＇ β} {T′ = T′} {l = l} (selfI h)
  rcOK (ConvI-extPair {m = m} {T′ = T′} gl ne tr cv fr h) =
    subst (Allowed rk) (sym (rconv-pair m (δr δt) T′)) (rcOK h)
  tyL (ConvI-extPair {m = m} {α} gl ne tr cv fr h) zero =
    subst (λ R → replaceTy α R (＇ β) ≡ ＇ β)
      (sym (repM-pair m (δl δt) (＇ β))) (replaceTy-other _ ne)
  tyL (ConvI-extPair {m = m} {α} gl ne tr cv fr h) (suc Z) =
    subst (λ R → replaceTy α R (δl δs Z) ≡ δl δt Z)
      (sym (repM-pair m (δl δt) (＇ β))) (tyL h Z)
  tyR (ConvI-extPair {m = m} {T′ = T′} gl ne tr cv fr h) zero =
    subst (λ c → replaceRC c T′ ≡ T′) (sym (rconv-pair m (δr δt) T′)) tr
  tyR (ConvI-extPair {m = m} {T′ = T′} gl ne tr cv fr h) (suc Y′) =
    subst (λ c → replaceRC c (δr δs Y′) ≡ δr δt Y′)
      (sym (rconv-pair m (δr δt) T′)) (tyR h Y′)
  leafO (ConvI-extPair gl ne tr cv fr h) zero o = ≈ˡ-refl
  leafO (ConvI-extPair {m = m} gl ne tr cv fr h) (suc Z) o =
    leafO h Z (Other-pair m Z o)
  convP (ConvI-extPair {m = m} {α} {T′} gl ne tr cv fr h) ↔-here o =
    subst₂ (λ R c → ConvLeafP d N w R c α l l (＇ β) T′)
      (sym (repM-pair m (δl δt) (＇ β))) (sym (rconv-pair m (δr δt) T′)) cv
  convP (ConvI-extPair {m = m} {α} {T′} gl ne tr cv fr h)
      {suc Z} {suc Y′} (↔-pair z) o =
    subst₂ (λ R c → ConvLeafP d N w R c α (leaf δs Z) (leaf δt Z)
                      (δl δs Z) (δr δs Y′))
      (sym (repM-pair m (δl δt) (＇ β))) (sym (rconv-pair m (δr δt) T′))
      (convP h z (Other-pair m Z o))
  convO (ConvI-extPair {m = m} {α} gl ne tr cv fr h)
      {suc Z} (only-pair z) o =
    subst (λ R → ConvLeafO d N w R α (leaf δs Z) (leaf δt Z) (δl δs Z))
      (sym (repM-pair m (δl δt) (＇ β))) (convO h z (Other-pair m Z o))
  genP (ConvI-extPair gl ne tr cv fr h) ↔-here = fr
  genP (ConvI-extPair gl ne tr cv fr h) (↔-pair z) = genP h z
  genO (ConvI-extPair gl ne tr cv fr h) (only-pair z) = genO h z
  sealI (ConvI-extPair {m = m} gl ne tr cv fr h) = SealI-pair m (sealI h)
  oracle (ConvI-extPair gl ne tr cv fr h) = oracle h

  -- a left-only binder: the new variable is the store variable β
  ConvI-extOnly : ∀ {m : CMode Φ X (ΔL w) (ΔR w)} {α}
    → GoodLeaf l → β ≢ α
    → ConvLeafO d N w (repM m (δl δt)) α l l (＇ β)
    → FreshO d w l (＇ β)
    → ConvI d N rk w m α δs δt
    → ConvI d N rk w (CMode-only m) α
        (extOnlyI (＇ β) l δs) (extOnlyI (＇ β) l δt)
  goodS (ConvI-extOnly gl ne cv fr h) =
    GoodI-extOnlyI {T = ＇ β} {δ = δs} gl (goodS h)
  goodT (ConvI-extOnly gl ne cv fr h) =
    GoodI-extOnlyI {T = ＇ β} {δ = δt} gl (goodT h)
  selfI (ConvI-extOnly {m = m} gl ne cv fr h) =
    SelfI-only m {T = ＇ β} {l = l} (selfI h)
  rcOK (ConvI-extOnly {m = m} gl ne cv fr h) =
    subst (Allowed rk) (sym (rconv-only m (δr δt))) (rcOK h)
  tyL (ConvI-extOnly {m = m} {α} gl ne cv fr h) zero =
    subst (λ R → replaceTy α R (＇ β) ≡ ＇ β)
      (sym (repM-only m (δl δt) (＇ β))) (replaceTy-other _ ne)
  tyL (ConvI-extOnly {m = m} {α} gl ne cv fr h) (suc Z) =
    subst (λ R → replaceTy α R (δl δs Z) ≡ δl δt Z)
      (sym (repM-only m (δl δt) (＇ β))) (tyL h Z)
  tyR (ConvI-extOnly {m = m} gl ne cv fr h) Y′ =
    subst (λ c → replaceRC c (δr δs Y′) ≡ δr δt Y′)
      (sym (rconv-only m (δr δt))) (tyR h Y′)
  leafO (ConvI-extOnly gl ne cv fr h) zero o = ≈ˡ-refl
  leafO (ConvI-extOnly {m = m} gl ne cv fr h) (suc Z) o =
    leafO h Z (Other-only m Z o)
  convP (ConvI-extOnly {m = m} {α} gl ne cv fr h)
      {suc Z} {Y′} (↔-only z) o =
    subst₂ (λ R c → ConvLeafP d N w R c α (leaf δs Z) (leaf δt Z)
                      (δl δs Z) (δr δs Y′))
      (sym (repM-only m (δl δt) (＇ β))) (sym (rconv-only m (δr δt)))
      (convP h z (Other-only m Z o))
  convO (ConvI-extOnly {m = m} {α} gl ne cv fr h) only-here o =
    subst (λ R → ConvLeafO d N w R α l l (＇ β))
      (sym (repM-only m (δl δt) (＇ β))) cv
  convO (ConvI-extOnly {m = m} {α} gl ne cv fr h)
      {suc Z} (only-only z) o =
    subst (λ R → ConvLeafO d N w R α (leaf δs Z) (leaf δt Z) (δl δs Z))
      (sym (repM-only m (δl δt) (＇ β))) (convO h z (Other-only m Z o))
  genP (ConvI-extOnly gl ne cv fr h) (↔-only z) = genP h z
  genO (ConvI-extOnly gl ne cv fr h) only-here = fr
  genO (ConvI-extOnly gl ne cv fr h) (only-only z) = genO h z
  sealI (ConvI-extOnly {m = m} gl ne cv fr h) = SealI-only m (sealI h)
  oracle (ConvI-extOnly gl ne cv fr h) = oracle h

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ} {rk : RK}
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {β : TyVar (ΔL w)}
    where

  -- a dead binder: the new variable occurs nowhere
  ConvI-extDead : ∀ {m : CMode Φ X (ΔL w) (ΔR w)} {α} → β ≢ α
    → ConvI d N rk w m α δs δt
    → ConvI d N rk w (CMode-dead m) α (extDeadI (＇ β) δs) (extDeadI (＇ β) δt)
  goodS (ConvI-extDead ne h) = GoodI-extDeadI {T = ＇ β} {δ = δs} (goodS h)
  goodT (ConvI-extDead ne h) = GoodI-extDeadI {T = ＇ β} {δ = δt} (goodT h)
  selfI (ConvI-extDead {m = m} ne h) =
    SelfI-dead m {T = ＇ β} (selfI h)
  rcOK (ConvI-extDead {m = m} ne h) =
    subst (Allowed rk) (sym (rconv-dead m (δr δt))) (rcOK h)
  tyL (ConvI-extDead {m = m} {α} ne h) zero =
    subst (λ R → replaceTy α R (＇ β) ≡ ＇ β)
      (sym (repM-dead m (δl δt) (＇ β))) (replaceTy-other _ ne)
  tyL (ConvI-extDead {m = m} {α} ne h) (suc Z) =
    subst (λ R → replaceTy α R (δl δs Z) ≡ δl δt Z)
      (sym (repM-dead m (δl δt) (＇ β))) (tyL h Z)
  tyR (ConvI-extDead {m = m} ne h) Y′ =
    subst (λ c → replaceRC c (δr δs Y′) ≡ δr δt Y′)
      (sym (rconv-dead m (δr δt))) (tyR h Y′)
  leafO (ConvI-extDead ne h) zero o = ≈ˡ-refl
  leafO (ConvI-extDead {m = m} ne h) (suc Z) o = leafO h Z (Other-dead m Z o)
  convP (ConvI-extDead {m = m} {α} ne h) {suc Z} {Y′} (↔-dead z) o =
    subst₂ (λ R c → ConvLeafP d N w R c α (leaf δs Z) (leaf δt Z)
                      (δl δs Z) (δr δs Y′))
      (sym (repM-dead m (δl δt) (＇ β))) (sym (rconv-dead m (δr δt)))
      (convP h z (Other-dead m Z o))
  convO (ConvI-extDead {m = m} {α} ne h) {suc Z} (only-dead z) o =
    subst (λ R → ConvLeafO d N w R α (leaf δs Z) (leaf δt Z) (δl δs Z))
      (sym (repM-dead m (δl δt) (＇ β))) (convO h z (Other-dead m Z o))
  genP (ConvI-extDead ne h) (↔-dead z) = genP h z
  genO (ConvI-extDead ne h) (only-dead z) = genO h z
  sealI (ConvI-extDead {m = m} ne h) =
    SealI-dead {T = ＇ β} {l = sem ⊤Ω} m (sealI h)
  oracle (ConvI-extDead ne h) = oracle h

------------------------------------------------------------------------
-- The hypotheses, in the current world
------------------------------------------------------------------------

renRConv-id : ∀ {Θ} (rc : RConv Θ) → renRConv id↪ᵗ rc ≡ rc
renRConv-id nothing = refl
renRConv-id (just (α′ , R′)) =
  cong₂ (λ a b → just (a , b)) (toRename-id-eq α′) (renameTy-id R′)

module Now {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ}
    {rk : RK} {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {α : TyVar (ΔL w)} {m : CMode Φ X (ΔL w) (ΔR w)}
    (h : ConvI d N rk w m α δs δt) where

  private
    ≈s = ↑ᴵ-refl {w = w} δs
    ≈t = ↑ᴵ-refl {w = w} δt

  revP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → Other m Z → ∀ {k} → k ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → leafRel d k w (leaf δs Z) Vl Vr
    → ℰ d k (X⊑Y z) w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ δl δs Z 〗)
        (revM (rconv m (δr δt)) (δr δs Y′) Vr)
  revP {Z} {Y′} z o {k} le {Vl} {Vr} vl vr r =
    ℰL→XY d k z w
      (ℰL-resp d k w (leaf≈ ≈t Z)
        (ℰL-≡ d k w (leaf (δt ↑ᴵ ⊒-refl w) Z)
          (↑〖〗-≡ (toRename-id-eq α) (renameTy-id (repM m (δl δt)))
            (renameTy-id (δl δs Z)))
          (revM-≡ (renRConv-id (rconv m (δr δt))) (renameTy-id (δr δs Y′)))
          (proj₁ (convP h z o (⊒-refl w) le) vl vr
            (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈s Z)) r))))

  conP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → Other m Z → ∀ {k} → k ≤ N
    → ∀ {Wl Wr} → Value Wl → Value Wr → leafRel d k w (leaf δt Z) Wl Wr
    → ℰ d k (X⊑Y z) w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (δl δs Z))
        (conM (rconv m (δr δt)) (δr δs Y′) Wr)
  conP {Z} {Y′} z o {k} le {Wl} {Wr} wl wr r =
    ℰL→XY d k z w
      (ℰL-resp d k w (leaf≈ ≈s Z)
        (ℰL-≡ d k w (leaf (δs ↑ᴵ ⊒-refl w) Z)
          (↓mc-≡ (toRename-id-eq α) (renameTy-id (repM m (δl δt)))
            (renameTy-id (δl δs Z)))
          (conM-≡ (renRConv-id (rconv m (δr δt))) (renameTy-id (δr δs Y′)))
          (proj₂ (convP h z o (⊒-refl w) le) wl wr
            (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈t Z)) r))))

  revO : ∀ {Z} (z : Φ ∋ Z only) → Other m Z → ∀ {k} → k ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → leafRel d k w (leaf δs Z) Vl Vr
    → ℰ d k (X⊑★ z) w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ δl δs Z 〗) Vr
  revO {Z} z o {k} le {Vl} {Vr} vl vr r =
    ℰL→X★ d k z w
      (ℰL-resp d k w (leaf≈ ≈t Z)
        (ℰL-≡ d k w (leaf (δt ↑ᴵ ⊒-refl w) Z)
          (↑〖〗-≡ (toRename-id-eq α) (renameTy-id (repM m (δl δt)))
            (renameTy-id (δl δs Z)))
          refl
          (proj₁ (convO h z o (⊒-refl w) le) vl vr
            (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈s Z)) r))))

  conO : ∀ {Z} (z : Φ ∋ Z only) → Other m Z → ∀ {k} → k ≤ N
    → ∀ {Wl Vr} → Value Wl → Value Vr → leafRel d k w (leaf δt Z) Wl Vr
    → ℰ d k (X⊑★ z) w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (δl δs Z)) Vr
  conO {Z} z o {k} le {Wl} {Vr} wl vr r =
    ℰL→X★ d k z w
      (ℰL-resp d k w (leaf≈ ≈s Z)
        (ℰL-≡ d k w (leaf (δs ↑ᴵ ⊒-refl w) Z)
          (↓mc-≡ (toRename-id-eq α) (renameTy-id (repM m (δl δt)))
            (renameTy-id (δl δs Z)))
          refl
          (proj₂ (convO h z o (⊒-refl w) le) wl vr
            (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈t Z)) r))))

-- X's own leaves, now
module NowX {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ}
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {α : TyVar (ΔL w)}
    where

  private
    ≈s = ↑ᴵ-refl {w = w} δs
    ≈t = ↑ᴵ-refl {w = w} δt

  pairRev : ∀ {Y} {x : Φ ∋ X ↔ Y} {α′}
    → SealI d N w (m-pair x α′) α δs δt → ∀ {k} → 0 < k → k ≤ N
    → ∀ {Vl Vr} → leafRel d k w (leaf δs X) Vl Vr
    → sealedL α (δl δt X) (sealedR α′ (δr δt Y)
        (leafRel d (pred k) w (leaf δt X))) Vl Vr
  pairRev {Y} {α′ = α′} si {k} pos le r =
    sealedL-map (toRename-id-eq α) (δl≡ ≈t X)
      (sealedR-map (toRename-id-eq α′) (δr≡ ≈t Y)
        (leafRel-resp d (pred k) w (leaf≈ ≈t X)))
      (proj₁ si (⊒-refl w) pos le
        (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈s X)) r))

  pairCon : ∀ {Y} {x : Φ ∋ X ↔ Y} {α′}
    → SealI d N w (m-pair x α′) α δs δt → ∀ {k} → 0 < k → k < N
    → ∀ {Wl Wr} → leafRel d k w (leaf δt X) Wl Wr
    → leafRel d k w (leaf δs X)
        (Wl ↓ seal α (δl δt X)) (Wr ↓ seal α′ (δr δt Y))
  pairCon {Y} {α′ = α′} si {k} pos lt {Wl} {Wr} r =
    leafRel-resp d k w (leaf≈ ≈s X)
      (subst₂ (leafRel d k w (leaf (δs ↑ᴵ ⊒-refl w) X))
        (cong₂ (λ a R → Wl ↓ seal a R) (toRename-id-eq α) (δl≡ ≈t X))
        (cong₂ (λ a R → Wr ↓ seal a R) (toRename-id-eq α′) (δr≡ ≈t Y))
        (proj₂ si (⊒-refl w) pos lt
          (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈t X)) r)))

  leftRev : SealI d N w (m-left {Φ = Φ} {X = X}) α δs δt
    → ∀ {k} → 0 < k → k ≤ N
    → ∀ {Vl Vr} → leafRel d k w (leaf δs X) Vl Vr
    → sealedL α (δl δt X) (leafRel d (onlyStage d k) w (leaf δt X)) Vl Vr
  leftRev si {k} pos le r =
    sealedL-map (toRename-id-eq α) (δl≡ ≈t X)
      (leafRel-resp d (onlyStage d k) w (leaf≈ ≈t X))
      (proj₁ si (⊒-refl w) pos le
        (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈s X)) r))

  leftCon : SealI d N w (m-left {Φ = Φ} {X = X}) α δs δt
    → ∀ {k} → 0 < k → onlyBelow d k N
    → ∀ {Wl Vr} → leafRel d k w (leaf δt X) Wl Vr
    → leafRel d k w (leaf δs X) (Wl ↓ seal α (δl δt X)) Vr
  leftCon si {k} pos lt {Wl} {Vr} r =
    leafRel-resp d k w (leaf≈ ≈s X)
      (subst (λ V → leafRel d k w (leaf (δs ↑ᴵ ⊒-refl w) X) V Vr)
        (cong₂ (λ a R → Wl ↓ seal a R) (toRename-id-eq α) (δl≡ ≈t X))
        (proj₂ si (⊒-refl w) pos lt
          (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈t X)) r)))

------------------------------------------------------------------------
-- Variables
------------------------------------------------------------------------

-- X itself, left-only, at `★`
rev★-left : ∀ d n {Φ : Corr Δ Δ′} {X} (z : Φ ∋ X only) w {N rk α δs δt}
  → ConvI d N rk w (m-left {Φ = Φ} {X = X}) α δs δt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑★ z) w δs Vl Vr
  → ℰ d n (X⊑★ z) w δt (Vl ↑ 〖 α , δl δt X ↑ δl δs X 〗) Vr
rev★-left d zero z w h le vl vr r = ℰ-zero d (X⊑★ z) w
rev★-left d (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt} h le vl vr r
    with sealedL-inv
      (NowX.leftRev {Φ = Φ} {X = X} {d = d} {N = N} {w = w} {δs = δs} {δt = δt}
        {α = α} (sealI h) (s≤s z≤n) le
        (from (𝒱-X★ d (suc k) z w {δ = δs}) r))
rev★-left ≺ (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt} h le vl vr r
    | W , refl , r′ =
  ℰ-≡ ≺ (suc k) (X⊑★ z) w δt (sym (↑-pk (〖〗-self α (δl δt X) (selfI h))))
    refl
    (ℰ-stepL ≺ k (X⊑★ z) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≺ k (X⊑★ z) w (value-sealed vl) vr
        (to (𝒱-X★ ≺ k z w {δ = δt}) r′)))
rev★-left ≻ (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt} h le vl vr r
    | W , refl , r′ =
  ℰ-≡ ≻ (suc k) (X⊑★ z) w δt (sym (↑-pk (〖〗-self α (δl δt X) (selfI h))))
    refl
    (ℰ-stepL ≻ (suc k) (X⊑★ z) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≻ (suc k) (X⊑★ z) w (value-sealed vl) vr
        (to (𝒱-X★ ≻ (suc k) z w {δ = δt}) r′)))

con★-left : ∀ d n {Φ : Corr Δ Δ′} {X} (z : Φ ∋ X only) w {N rk α δs δt}
  → ConvI d N rk w (m-left {Φ = Φ} {X = X}) α δs δt
  → ConB {ΔR w} d nothing n N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑★ z) w δt Wl Wr
  → ℰ d n (X⊑★ z) w δs (Wl ↓ makeConceal α (δl δt X) (δl δs X)) Wr
con★-left d zero z w h cb wl wr r = ℰ-zero d (X⊑★ z) w
con★-left ≺ (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt} h cb wl wr r =
  ℰ-≡ ≺ (suc k) (X⊑★ z) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (selfI h)))) refl
    (ℰ-value ≺ (suc k) (X⊑★ z) w (wl CT.↓ CT.seal) wr
      (to (𝒱-X★ ≺ (suc k) z w {δ = δs})
        (NowX.leftCon {Φ = Φ} {X = X} {d = ≺} {N = N} {w = w} {δs = δs}
          {δt = δt}
          {α = α} (sealI h) (s≤s z≤n) cb
          (from (𝒱-X★ ≺ (suc k) z w {δ = δt}) r))))
con★-left ≻ (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt} h cb wl wr r =
  ℰ-≡ ≻ (suc k) (X⊑★ z) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (selfI h)))) refl
    (ℰ-value ≻ (suc k) (X⊑★ z) w (wl CT.↓ CT.seal) wr
      (to (𝒱-X★ ≻ (suc k) z w {δ = δs})
        (NowX.leftCon {Φ = Φ} {X = X} {d = ≻} {N = N} {w = w} {δs = δs}
          {δt = δt}
          {α = α} (sealI h) (s≤s z≤n) cb
          (from (𝒱-X★ ≻ (suc k) z w {δ = δt}) r))))

-- a left-only variable, at `★`
rev★-var : ∀ d n {Φ : Corr Δ Δ′} {Z} (z : Φ ∋ Z only) w {X} {N rk}
    {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt}
  → ConvI d N rk w m α δs δt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑★ z) w δs Vl Vr
  → ℰ d n (X⊑★ z) w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ δl δs Z 〗) Vr
rev★-var d n z w {m = m-none R rc} h le vl vr r =
  Now.revO h z tt le vl vr (from (𝒱-X★ d n z w) r)
rev★-var d n {Z = Z} z w {X} {m = m-pair x α′} h le vl vr r with Z ≟ X
rev★-var d n {Z = Z} z w {X} {m = m-pair x α′} h le vl vr r | no ne =
  Now.revO h z ne le vl vr (from (𝒱-X★ d n z w) r)
rev★-var d n {Z = .X} z w {X} {m = m-pair x α′} h le vl vr r | yes refl =
  ⊥-elim (↔-only-⊥ x z)
rev★-var d n {Z = Z} z w {X} {m = m-dead x} h le vl vr r with Z ≟ X
rev★-var d n {Z = Z} z w {X} {m = m-dead x} h le vl vr r | no ne =
  Now.revO h z ne le vl vr (from (𝒱-X★ d n z w) r)
rev★-var d n {Z = .X} z w {X} {m = m-dead x} h le vl vr r | yes refl =
  ⊥-elim (only-dead-⊥ z x)
rev★-var d n {Z = Z} z w {X} {m = m-left} h le vl vr r with Z ≟ X
rev★-var d n {Z = Z} z w {X} {m = m-left} h le vl vr r | no ne =
  Now.revO h z ne le vl vr (from (𝒱-X★ d n z w) r)
rev★-var d n {Z = .X} z w {X} {m = m-left} h le vl vr r | yes refl =
  rev★-left d n z w h le vl vr r

con★-var : ∀ d n {Φ : Corr Δ Δ′} {Z} (z : Φ ∋ Z only) w {X} {N rk}
    {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt}
  → ConvI d N rk w m α δs δt → n ≤ N → ConB {ΔR w} d nothing n N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑★ z) w δt Wl Wr
  → ℰ d n (X⊑★ z) w δs
      (Wl ↓ makeConceal α (repM m (δl δt)) (δl δs Z)) Wr
con★-var d n z w {m = m-none R rc} h le cb wl wr r =
  Now.conO h z tt le wl wr (from (𝒱-X★ d n z w) r)
con★-var d n {Z = Z} z w {X} {m = m-pair x α′} h le cb wl wr r with Z ≟ X
con★-var d n {Z = Z} z w {X} {m = m-pair x α′} h le cb wl wr r | no ne =
  Now.conO h z ne le wl wr (from (𝒱-X★ d n z w) r)
con★-var d n {Z = .X} z w {X} {m = m-pair x α′} h le cb wl wr r
    | yes refl =
  ⊥-elim (↔-only-⊥ x z)
con★-var d n {Z = Z} z w {X} {m = m-dead x} h le cb wl wr r with Z ≟ X
con★-var d n {Z = Z} z w {X} {m = m-dead x} h le cb wl wr r | no ne =
  Now.conO h z ne le wl wr (from (𝒱-X★ d n z w) r)
con★-var d n {Z = .X} z w {X} {m = m-dead x} h le cb wl wr r | yes refl =
  ⊥-elim (only-dead-⊥ z x)
con★-var d n {Z = Z} z w {X} {m = m-left} h le cb wl wr r with Z ≟ X
con★-var d n {Z = Z} z w {X} {m = m-left} h le cb wl wr r | no ne =
  Now.conO h z ne le wl wr (from (𝒱-X★ d n z w) r)
con★-var d n {Z = .X} z w {X} {m = m-left} h le cb wl wr r | yes refl =
  con★-left d n z w h cb wl wr r

-- X itself, paired, the right converting too
rev-pairX : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w {N rk α α′ δs δt}
  → ConvI d N rk w (m-pair x α′) α δs δt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑Y x) w δs Vl Vr
  → ℰ d n (X⊑Y x) w δt (Vl ↑ 〖 α , δl δt X ↑ δl δs X 〗)
      (Vr ↑ 〖 α′ , δr δt Y ↑ δr δs Y 〗)
rev-pairX d zero x w h le vl vr r = ℰ-zero d (X⊑Y x) w
rev-pairX d (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt} h le vl vr r
    with sealedL-inv
      (NowX.pairRev {Φ = Φ} {X = X} {d = d} {N = N} {w = w} {δs = δs}
        {δt = δt} {α = α} {x = x} {α′ = α′} (sealI h) (s≤s z≤n) le
        (from (𝒱-XY d (suc k) x w {δ = δs}) r))
rev-pairX d (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt} h le vl vr r
    | W , refl , s′ with sealedR-inv s′
rev-pairX ≺ (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt} h le vl vr r
    | W , refl , s′ | W′ , refl , r′ =
  ℰ-≡ ≺ (suc k) (X⊑Y x) w δt
    (sym (↑-pk (〖〗-self α (δl δt X) (proj₁ (selfI h)))))
    (sym (↑-pk (〖〗-self α′ (δr δt Y) (proj₂ (selfI h)))))
    (ℰ-stepL ≺ k (X⊑Y x) w (conceal-reveal (value-sealed vl))
      (ℰ-stepR ≺ k (X⊑Y x) w (conceal-reveal (value-sealed vr))
        (ℰ-value ≺ k (X⊑Y x) w (value-sealed vl) (value-sealed vr)
          (to (𝒱-XY ≺ k x w {δ = δt}) r′))))
rev-pairX ≻ (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt} h le vl vr r
    | W , refl , s′ | W′ , refl , r′ =
  ℰ-≡ ≻ (suc k) (X⊑Y x) w δt
    (sym (↑-pk (〖〗-self α (δl δt X) (proj₁ (selfI h)))))
    (sym (↑-pk (〖〗-self α′ (δr δt Y) (proj₂ (selfI h)))))
    (ℰ-stepL ≻ (suc k) (X⊑Y x) w (conceal-reveal (value-sealed vl))
      (ℰ-stepR ≻ k (X⊑Y x) w (conceal-reveal (value-sealed vr))
        (ℰ-value ≻ k (X⊑Y x) w (value-sealed vl) (value-sealed vr)
          (to (𝒱-XY ≻ k x w {δ = δt}) r′))))

con-pairX : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w {N rk α α′ δs δt}
  → ConvI d N rk w (m-pair x α′) α δs δt → n < N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑Y x) w δt Wl Wr
  → ℰ d n (X⊑Y x) w δs (Wl ↓ makeConceal α (δl δt X) (δl δs X))
      (Wr ↓ makeConceal α′ (δr δt Y) (δr δs Y))
con-pairX d zero x w h lt wl wr r = ℰ-zero d (X⊑Y x) w
con-pairX d (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt} h lt wl wr r =
  ℰ-≡ d (suc k) (X⊑Y x) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (proj₁ (selfI h)))))
    (sym (↓-pk (makeConceal-self α′ (δr δt Y) (proj₂ (selfI h)))))
    (ℰ-value d (suc k) (X⊑Y x) w (wl CT.↓ CT.seal) (wr CT.↓ CT.seal)
      (to (𝒱-XY d (suc k) x w {δ = δs})
        (NowX.pairCon {Φ = Φ} {X = X} {d = d} {N = N} {w = w} {δs = δs}
          {δt = δt} {α = α} {x = x} {α′ = α′} (sealI h) (s≤s z≤n) lt
          (from (𝒱-XY d (suc k) x w {δ = δt}) r))))

-- X itself, paired, only the left converting
rev-leftX : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w {N rk α δs δt}
  → ConvI d N rk w (m-left {Φ = Φ} {X = X}) α δs δt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑Y x) w δs Vl Vr
  → ℰ d n (X⊑Y x) w δt (Vl ↑ 〖 α , δl δt X ↑ δl δs X 〗) Vr
rev-leftX d zero x w h le vl vr r = ℰ-zero d (X⊑Y x) w
rev-leftX d (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt} h le vl vr r
    with sealedL-inv
      (NowX.leftRev {Φ = Φ} {X = X} {d = d} {N = N} {w = w} {δs = δs}
        {δt = δt} {α = α} (sealI h) (s≤s z≤n) le
        (from (𝒱-XY d (suc k) x w {δ = δs}) r))
rev-leftX ≺ (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt} h le vl vr r
    | W , refl , r′ =
  ℰ-≡ ≺ (suc k) (X⊑Y x) w δt
    (sym (↑-pk (〖〗-self α (δl δt X) (selfI h)))) refl
    (ℰ-stepL ≺ k (X⊑Y x) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≺ k (X⊑Y x) w (value-sealed vl) vr
        (to (𝒱-XY ≺ k x w {δ = δt}) r′)))
rev-leftX ≻ (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt} h le vl vr r
    | W , refl , r′ =
  ℰ-≡ ≻ (suc k) (X⊑Y x) w δt
    (sym (↑-pk (〖〗-self α (δl δt X) (selfI h)))) refl
    (ℰ-stepL ≻ (suc k) (X⊑Y x) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≻ (suc k) (X⊑Y x) w (value-sealed vl) vr
        (to (𝒱-XY ≻ (suc k) x w {δ = δt}) r′)))

con-leftX : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w {N rk α δs δt}
  → ConvI d N rk w (m-left {Φ = Φ} {X = X}) α δs δt
  → ConB {ΔR w} d nothing n N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑Y x) w δt Wl Wr
  → ℰ d n (X⊑Y x) w δs (Wl ↓ makeConceal α (δl δt X) (δl δs X)) Wr
con-leftX d zero x w h cb wl wr r = ℰ-zero d (X⊑Y x) w
con-leftX ≺ (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt} h cb wl wr r =
  ℰ-≡ ≺ (suc k) (X⊑Y x) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (selfI h)))) refl
    (ℰ-value ≺ (suc k) (X⊑Y x) w (wl CT.↓ CT.seal) wr
      (to (𝒱-XY ≺ (suc k) x w {δ = δs})
        (NowX.leftCon {Φ = Φ} {X = X} {d = ≺} {N = N} {w = w} {δs = δs}
          {δt = δt} {α = α} (sealI h) (s≤s z≤n) cb
          (from (𝒱-XY ≺ (suc k) x w {δ = δt}) r))))
con-leftX ≻ (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt} h cb wl wr r =
  ℰ-≡ ≻ (suc k) (X⊑Y x) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (selfI h)))) refl
    (ℰ-value ≻ (suc k) (X⊑Y x) w (wl CT.↓ CT.seal) wr
      (to (𝒱-XY ≻ (suc k) x w {δ = δs})
        (NowX.leftCon {Φ = Φ} {X = X} {d = ≻} {N = N} {w = w} {δs = δs}
          {δt = δt} {α = α} (sealI h) (s≤s z≤n) cb
          (from (𝒱-XY ≻ (suc k) x w {δ = δt}) r))))

-- a paired variable
rev-var : ∀ d n {Φ : Corr Δ Δ′} {Z Y′} (z : Φ ∋ Z ↔ Y′) w {X} {N rk}
    {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt}
  → ConvI d N rk w m α δs δt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑Y z) w δs Vl Vr
  → ℰ d n (X⊑Y z) w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ δl δs Z 〗)
      (revM (rconv m (δr δt)) (δr δs Y′) Vr)
rev-var d n z w {m = m-none R rc} h le vl vr r =
  Now.revP h z tt le vl vr (from (𝒱-XY d n z w) r)
rev-var d n {Z = Z} z w {X} {m = m-pair x α′} h le vl vr r with Z ≟ X
rev-var d n {Z = Z} z w {X} {m = m-pair x α′} h le vl vr r | no ne =
  Now.revP h z ne le vl vr (from (𝒱-XY d n z w) r)
rev-var d n {Z = .X} z w {X} {m = m-pair x α′} h le vl vr r | yes refl
    with ↔-functional x z
rev-var d n {Z = .X} z w {X} {m = m-pair x α′} h le vl vr r | yes refl
    | refl with ↔-unique x z
rev-var d n {Z = .X} .x w {X} {m = m-pair x α′} h le vl vr r | yes refl
    | refl | refl =
  rev-pairX d n x w h le vl vr r
rev-var d n {Z = Z} z w {X} {m = m-dead x} h le vl vr r with Z ≟ X
rev-var d n {Z = Z} z w {X} {m = m-dead x} h le vl vr r | no ne =
  Now.revP h z ne le vl vr (from (𝒱-XY d n z w) r)
rev-var d n {Z = .X} z w {X} {m = m-dead x} h le vl vr r | yes refl =
  ⊥-elim (↔-dead-⊥ z x)
rev-var d n {Z = Z} z w {X} {m = m-left} h le vl vr r with Z ≟ X
rev-var d n {Z = Z} z w {X} {m = m-left} h le vl vr r | no ne =
  Now.revP h z ne le vl vr (from (𝒱-XY d n z w) r)
rev-var d n {Z = .X} z w {X} {m = m-left} h le vl vr r | yes refl =
  rev-leftX d n z w h le vl vr r

con-var : ∀ d n {Φ : Corr Δ Δ′} {Z Y′} (z : Φ ∋ Z ↔ Y′) w {X} {N rk}
    {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt}
  → ConvI d N rk w m α δs δt → n ≤ N → ConB d (rconv m (δr δt)) n N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑Y z) w δt Wl Wr
  → ℰ d n (X⊑Y z) w δs (Wl ↓ makeConceal α (repM m (δl δt)) (δl δs Z))
      (conM (rconv m (δr δt)) (δr δs Y′) Wr)
con-var d n z w {m = m-none R rc} h le cb wl wr r =
  Now.conP h z tt le wl wr (from (𝒱-XY d n z w) r)
con-var d n {Z = Z} z w {X} {m = m-pair x α′} h le cb wl wr r with Z ≟ X
con-var d n {Z = Z} z w {X} {m = m-pair x α′} h le cb wl wr r | no ne =
  Now.conP h z ne le wl wr (from (𝒱-XY d n z w) r)
con-var d n {Z = .X} z w {X} {m = m-pair x α′} h le cb wl wr r | yes refl
    with ↔-functional x z
con-var d n {Z = .X} z w {X} {m = m-pair x α′} h le cb wl wr r | yes refl
    | refl with ↔-unique x z
con-var ≺ n {Z = .X} .x w {X} {m = m-pair x α′} h le cb wl wr r
    | yes refl | refl | refl =
  con-pairX ≺ n x w h cb wl wr r
con-var ≻ n {Z = .X} .x w {X} {m = m-pair x α′} h le cb wl wr r
    | yes refl | refl | refl =
  con-pairX ≻ n x w h cb wl wr r
con-var d n {Z = Z} z w {X} {m = m-dead x} h le cb wl wr r with Z ≟ X
con-var d n {Z = Z} z w {X} {m = m-dead x} h le cb wl wr r | no ne =
  Now.conP h z ne le wl wr (from (𝒱-XY d n z w) r)
con-var d n {Z = .X} z w {X} {m = m-dead x} h le cb wl wr r | yes refl =
  ⊥-elim (↔-dead-⊥ z x)
con-var d n {Z = Z} z w {X} {m = m-left} h le cb wl wr r with Z ≟ X
con-var d n {Z = Z} z w {X} {m = m-left} h le cb wl wr r | no ne =
  Now.conP h z ne le wl wr (from (𝒱-XY d n z w) r)
con-var d n {Z = .X} z w {X} {m = m-left} h le cb wl wr r | yes refl =
  con-leftX d n z w h cb wl wr r
