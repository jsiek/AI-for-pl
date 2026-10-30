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
--         created later (`genP`, `genO` for the target interpretation,
--         `genPS`, `genOS` for the source one);
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
  _≤′_; ≤′-refl; ≤′-step; _≤?_)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤⇒≤′; ≤′⇒≤; ≤-trans;
  ≤-<-trans; <⇒≤)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ; wk↪ᵗ)
open import proof.DGG.CenterRename using (toRenameᵗ-∘; _∘↪_)
open import proof.TermRename using (renameᵗᵐ-id)
open import proof.TypeInTermSubst using (toRename-id-eq; toRename-wk-eq;
  renameᵗᵐ-preserves-Value)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open import Conversion
open import CastTerms using (Term; `_; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_;
  _⟨_⟩; _↑_; _↓_; blame; Value; RevealValue; ConcealValue; renameᵗᵐ; ⇑ᵗᵐ)
import CastTerms as CT
open import Reduction using (_—→_; id-reveal; id-conceal; conceal-reveal;
  β-reveal-⇒; β-conceal-⇒; β-reveal-∀; β-conceal-∀; _—→[_]_; bind; keep;
  StoreChange; StoreChanges; applyBody; []; _∷_; ↠-refl; ↠-step)
open import LR.Steps using (embedᶜˢ; more; none)
open import Data.List using (List; []; _∷_; map)
open import Data.Vec using () renaming ([] to []ᵛ)
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
open import proof.LR.SubstLemma using (ℰᵍ-zero; _⇔_; iff; to; from; 𝒱-XY;
  𝒱-X★)
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
  × (∀ {w} {n′ n} (le : n′ ≤′ n) → n′ ≤ N → (c : SDesc (ΔL w) (ΔR w))
     → FreshO d w (sem (onlyLeafS d le c)) (leftTyS c))

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
      genPS : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′)
        → FreshP d rk w (leaf δs Z) (δl δs Z) (δr δs Y′)
      genOS : ∀ {Z} (z : Φ ∋ Z only)
        → FreshO d w (leaf δs Z) (δl δs Z)
      sealI : SealI d N w m α δs δt
      oracle : Oracle d N

  open ConvI public

-- an interpretation whose leaves are closed under later conversions
record FreshI {Δ Δ′} (Φ : Corr Δ Δ′) (d : Dir) (N : ℕ) (rk : RK)
    (w : World) (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) : Set₁ where
  field
    fgood : GoodI δ
    fP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′)
      → FreshP d rk w (leaf δ Z) (δl δ Z) (δr δ Y′)
    fO : ∀ {Z} (z : Φ ∋ Z only) → FreshO d w (leaf δ Z) (δl δ Z)
    forc : Oracle d N

open FreshI public

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d N rk} {w : World}
    {m : CMode Φ X (ΔL w) (ΔR w)} {α} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    where

  -- the two interpretations of the hypotheses
  freshT : ConvI d N rk w m α δs δt → FreshI Φ d N rk w δt
  fgood (freshT h) = goodT h
  fP (freshT h) = genP h
  fO (freshT h) = genO h
  forc (freshT h) = oracle h

  freshS : ConvI d N rk w m α δs δt → FreshI Φ d N rk w δs
  fgood (freshS h) = goodS h
  fP (freshS h) = genPS h
  fO (freshS h) = genOS h
  forc (freshS h) = oracle h

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
  genPS (ConvI-↑ h) {Z} {Y′} z =
    FreshP-↑ {d = d} e {L = leaf δs Z} {rk} {δl δs Z} {δr δs Y′}
      (genPS h z)
  genOS (ConvI-↑ h) {Z} z =
    FreshO-↑ {d = d} e {L = leaf δs Z} {δl δs Z} (genOS h z)
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
  genPS (ConvI-extPair gl ne tr cv fr h) ↔-here = fr
  genPS (ConvI-extPair gl ne tr cv fr h) (↔-pair z) = genPS h z
  genOS (ConvI-extPair gl ne tr cv fr h) (only-pair z) = genOS h z
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
  genPS (ConvI-extOnly gl ne cv fr h) (↔-only z) = genPS h z
  genOS (ConvI-extOnly gl ne cv fr h) only-here = fr
  genOS (ConvI-extOnly gl ne cv fr h) (only-only z) = genOS h z
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
  genPS (ConvI-extDead ne h) (↔-dead z) = genPS h z
  genOS (ConvI-extDead ne h) (only-dead z) = genOS h z
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

------------------------------------------------------------------------
-- Functions
------------------------------------------------------------------------

-- the right side's conversion of a mode, and how it moves to futures:
-- by the mode in the main lemma, none in the lemma at `★`
module FunConv {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} (d : Dir) (N : ℕ)
    (rk : RK) {A A′ B B′} (p : Φ ⊢ A ⊑ A′) (q : Φ ⊢ B ⊑ B′)
    (RF : ∀ {ΘL ΘR} → CMode Φ X ΘL ΘR → (Δ′ ⇒ˢ ΘR) → RConv ΘR)
    (RF-↑ : ∀ {ΘL ΘR ΘL′ ΘR′} (ρL : ΘL ↪ᵗ ΘL′) (ρR : ΘR ↪ᵗ ΘR′)
       (m : CMode Φ X ΘL ΘR) σ
       → RF (CMode-↑ ρL ρR m) (λ Y → renameᵗ (toRenameᵗ ρR) (σ Y))
         ≡ renRConv ρR (RF m σ))
    (revp : ∀ {w m α δs δt} → ConvI d N rk w m α δs δt → ∀ {k} → k ≤ N
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (RF m (δr δt)) (substᵗ (δr δs) A′) Vr))
    (conp : ∀ {w m α δs δt} → ConvI d N rk w m α δs δt → ∀ {k}
       → ConB d (RF m (δr δt)) k N
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (RF m (δr δt)) (substᵗ (δr δs) A′) Wr))
    (revq : ∀ {w m α δs δt} → ConvI d N rk w m α δs δt → ∀ {k} → k ≤ N
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k q w δs Vl Vr
       → ℰ d k q w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) B 〗)
           (revM (RF m (δr δt)) (substᵗ (δr δs) B′) Vr))
    (conq : ∀ {w m α δs δt} → ConvI d N rk w m α δs δt → ∀ {k}
       → ConB d (RF m (δr δt)) k N
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k q w δt Wl Wr
       → ℰ d k q w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) B))
           (conM (RF m (δr δt)) (substᵗ (δr δs) B′) Wr))
    where

  -- the conversion of a result, renamed into a future
  private
    rev-ren : ∀ {w w′} (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (ΔR w)) α
        (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔL w′)) C
      → Q ↑ 〖 toRenameᵗ (ρL e) α
            , repM (CMode-↑ (ρL e) (ρR e) m) (δl (δt ↑ᴵ e))
            ↑ substᵗ (δl (δs ↑ᴵ e)) C 〗
        ≡ Q ↑ rename↑ (toRenameᵗ (ρL e))
              〖 α , repM m (δl δt) ↑ substᵗ (δl δs) C 〗
    rev-ren e m α δs δt Q C =
      trans (↑〖〗-≡ refl (repM-↑ (ρL e) (ρR e) m (δl δt)) refl)
        (sym (↑-pk (〖〗-ren (ρL e) α (repM m (δl δt)) (δl δs) C)))

    con-ren : ∀ {w w′} (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (ΔR w)) α
        (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔL w′)) C
      → Q ↓ makeConceal (toRenameᵗ (ρL e) α)
              (repM (CMode-↑ (ρL e) (ρR e) m) (δl (δt ↑ᴵ e)))
              (substᵗ (δl (δs ↑ᴵ e)) C)
        ≡ Q ↓ rename↓ (toRenameᵗ (ρL e))
              (makeConceal α (repM m (δl δt)) (substᵗ (δl δs) C))
    con-ren e m α δs δt Q C =
      trans (↓mc-≡ refl (repM-↑ (ρL e) (ρR e) m (δl δt)) refl)
        (sym (↓-pk (makeConceal-ren (ρL e) α (repM m (δl δt)) (δl δs) C)))

    rc-ren : ∀ {w w′} (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (ΔR w))
        (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔR w′)) C
      → revM (RF (CMode-↑ (ρL e) (ρR e) m) (δr (δt ↑ᴵ e)))
          (substᵗ (δr (δs ↑ᴵ e)) C) Q
        ≡ mplug (renameMFrame (ρR e)
            (revFrame (RF m (δr δt)) (substᵗ (δr δs) C))) Q
    rc-ren e m δs δt Q C =
      trans (cong (λ c → revM c _ Q) (RF-↑ (ρL e) (ρR e) m (δr δt)))
        (sym (revFrame-ren (ρR e) (RF m (δr δt)) (δr δs) C Q))

    cc-ren : ∀ {w w′} (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (ΔR w))
        (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔR w′)) C
      → conM (RF (CMode-↑ (ρL e) (ρR e) m) (δr (δt ↑ᴵ e)))
          (substᵗ (δr (δs ↑ᴵ e)) C) Q
        ≡ mplug (renameMFrame (ρR e)
            (conFrame (RF m (δr δt)) (substᵗ (δr δs) C))) Q
    cc-ren e m δs δt Q C =
      trans (cong (λ c → conM c _ Q) (RF-↑ (ρL e) (ρR e) m (δr δt)))
        (sym (conFrame-ren (ρR e) (RF m (δr δt)) (δr δs) C Q))

  -- a converted function applied, in the world of the function
  rev-at : ∀ {n} w {m α δs δt} (h : ConvI d N rk w m α δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → funRel d n p q w δs Vl Vr
    → ∀ {Ul Ur} → Value Ul → Value Ur → 𝒱 d n p w δt Ul Ur
    → ℰ d n q w δt
        ((Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (A ⇒ B) 〗) · Ul)
        (revM (RF m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Vr · Ur)
  rev-at w {m} {α} {δs} {δt} h le {Vl} {Vr} vl vr f {Ul} {Ur} ul ur a =
    ℰ-app-steps d q w (RF m (δr δt)) le (β-reveal-⇒ vl ul)
      (rightApp (RF m (δr δt)) vr ur)
      (λ {s} s≤n cb →
        app-core d s p q w vl vr
          (just (reveal 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) B 〗))
          (revFrame (RF m (δr δt)) (substᵗ (δr δs) B′))
          (conp h cb ul ur (𝒱-down d s≤n p w (goodT h) a))
          (funRel-down d s≤n p q w f)
          (λ e₂ {k} k≤s {Ql} {Qr} ql qr r →
            ℰᵍ-≡ (rev-ren e₂ m α δs δt Ql B) (rc-ren e₂ m δs δt Qr B′)
              (revq (ConvI-↑ e₂ h) (≤-trans k≤s (≤-trans s≤n le)) ql qr r)))

  con-at : ∀ {n} w {m α δs δt} (h : ConvI d N rk w m α δs δt)
    → ConB d (RF m (δr δt)) n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → funRel d n p q w δt Wl Wr
    → ∀ {Ul Ur} → Value Ul → Value Ur → 𝒱 d n p w δs Ul Ur
    → ℰ d n q w δs
        ((Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (A ⇒ B)))
          · Ul)
        (conM (RF m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Wr · Ur)
  con-at w {m} {α} {δs} {δt} h cb {Wl} {Wr} wl wr f {Ul} {Ur} ul ur a =
    ℰ-app-steps d q w (RF m (δr δt)) (ConB-≤ d (RF m (δr δt)) cb)
      (β-conceal-⇒ wl ul) (rightAppC (RF m (δr δt)) wr ur)
      (λ {s} s≤n cb′ →
        app-core d s p q w wl wr
          (just (conceal
            (makeConceal α (repM m (δl δt)) (substᵗ (δl δs) B))))
          (conFrame (RF m (δr δt)) (substᵗ (δr δs) B′))
          (revp h (≤-trans s≤n (ConB-≤ d (RF m (δr δt)) cb)) ul ur
            (𝒱-down d s≤n p w (goodS h) a))
          (funRel-down d s≤n p q w f)
          (λ e₂ {k} k≤s {Ql} {Qr} ql qr r →
            ℰᵍ-≡ (con-ren e₂ m α δs δt Ql B) (cc-ren e₂ m δs δt Qr B′)
              (conq (ConvI-↑ e₂ h)
                (subst (λ c → ConB d c k N)
                  (sym (RF-↑ (ρL e₂) (ρR e₂) m (δr δt)))
                  (ConB-ren d (ρR e₂) (RF m (δr δt))
                    (ConB-down d (RF m (δr δt)) (≤-trans k≤s s≤n) cb)))
                ql qr r)))

  fun-rev : ∀ {n w m α δs δt} (h : ConvI d N rk w m α δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → funRel d n p q w δs Vl Vr
    → funRel d n p q w δt
        (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (A ⇒ B) 〗)
        (revM (RF m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Vr)
  fun-rev {n} {w} {m} {α} {δs} {δt} h le {Vl} {Vr} vl vr f
      {w′} e {n′} le′ Ul Ur ul ur a =
    ℰᵍ-map d n′ w′ (λ le″ w″ e″ V V′ → 𝒱≤-cast d le″ (≤′-trans le″ le′) q w″)
      (ℰᵍ-≡
        (cong (_· Ul) (rev-ren e m α δs δt (renameᵗᵐ (ρL e) Vl) (A ⇒ B)))
        (cong (_· Ur) (trans
          (cong (λ c → revM c _ (renameᵗᵐ (ρR e) Vr))
            (RF-↑ (ρL e) (ρR e) m (δr δt)))
          (sym (revM-ren (ρR e) (RF m (δr δt)) (δr δs) (A′ ⇒ B′) Vr))))
        (rev-at w′ (ConvI-↑ e h) (≤-trans (≤′⇒≤ le′) le)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (renameᵗᵐ-preserves-Value (ρR e) vr)
          (funRel-down d (≤′⇒≤ le′) p q w′ (funRel-mono d n p q e f))
          ul ur (𝒱≤-cast d le′ ≤′-refl p w′ a)))

  fun-con : ∀ {n w m α δs δt} (h : ConvI d N rk w m α δs δt)
    → ConB d (RF m (δr δt)) n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → funRel d n p q w δt Wl Wr
    → funRel d n p q w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (A ⇒ B)))
        (conM (RF m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Wr)
  fun-con {n} {w} {m} {α} {δs} {δt} h cb {Wl} {Wr} wl wr f
      {w′} e {n′} le′ Ul Ur ul ur a =
    ℰᵍ-map d n′ w′ (λ le″ w″ e″ V V′ → 𝒱≤-cast d le″ (≤′-trans le″ le′) q w″)
      (ℰᵍ-≡
        (cong (_· Ul) (con-ren e m α δs δt (renameᵗᵐ (ρL e) Wl) (A ⇒ B)))
        (cong (_· Ur) (trans
          (cong (λ c → conM c _ (renameᵗᵐ (ρR e) Wr))
            (RF-↑ (ρL e) (ρR e) m (δr δt)))
          (sym (conM-ren (ρR e) (RF m (δr δt)) (δr δs) (A′ ⇒ B′) Wr))))
        (con-at w′ (ConvI-↑ e h)
          (subst (λ c → ConB d c n′ N) (sym (RF-↑ (ρL e) (ρR e) m (δr δt)))
            (ConB-ren d (ρR e) (RF m (δr δt))
              (ConB-down d (RF m (δr δt)) (≤′⇒≤ le′) cb)))
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (renameᵗᵐ-preserves-Value (ρR e) wr)
          (funRel-down d (≤′⇒≤ le′) p q w′ (funRel-mono d n p q e f))
          ul ur (𝒱≤-cast d le′ ≤′-refl p w′ a)))

------------------------------------------------------------------------
-- When the right does not convert
------------------------------------------------------------------------

FreshP-left : ∀ {d rk w L T T′} → FreshP d rk w L T T′
  → FreshP d left w L T T′
FreshP-left {rk = both} f e rc ok nb nrc = f e rc tt nb nrc
FreshP-left {rk = left} f = f

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ} {rk : RK}
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} where

  ConvI-left : ∀ {m : CMode Φ X (ΔL w) (ΔR w)} {α}
    → rconv m (δr δt) ≡ nothing
    → ConvI d N rk w m α δs δt → ConvI d N left w m α δs δt
  goodS (ConvI-left eq h) = goodS h
  goodT (ConvI-left eq h) = goodT h
  selfI (ConvI-left eq h) = selfI h
  rcOK (ConvI-left eq h) = subst (Allowed left) (sym eq) tt
  tyL (ConvI-left eq h) = tyL h
  tyR (ConvI-left eq h) = tyR h
  leafO (ConvI-left eq h) = leafO h
  convP (ConvI-left eq h) = convP h
  convO (ConvI-left eq h) = convO h
  genP (ConvI-left eq h) {Z} {Y′} z =
    FreshP-left {d = d} {rk = rk} {w = w} {L = leaf δt Z} {T = δl δt Z}
      {T′ = δr δt Y′} (genP h z)
  genO (ConvI-left eq h) = genO h
  genPS (ConvI-left eq h) {Z} {Y′} z =
    FreshP-left {d = d} {rk = rk} {w = w} {L = leaf δs Z} {T = δl δs Z}
      {T′ = δr δs Y′} (genPS h z)
  genOS (ConvI-left eq h) = genOS h
  sealI (ConvI-left eq h) = sealI h
  oracle (ConvI-left eq h) = oracle h

------------------------------------------------------------------------
-- Allocating a store variable
------------------------------------------------------------------------

embed-bind : ∀ {Θ} (T : Ty Θ) → embedᶜˢ (bind T ∷ []) ≡ wk↪ᵗ
embed-bind T = ∘↪-idˡ wk↪ᵗ

embed-var : ∀ {Θ} (T : Ty Θ) X
  → toRenameᵗ (embedᶜˢ (bind T ∷ [])) X ≡ suc X
embed-var T X =
  trans (cong (λ ρ → toRenameᵗ ρ X) (embed-bind T)) (toRename-wk-eq X)

-- a tag for a new store variable; it is never read here
newTag : ∀ {ΘL ΘR} → Tag (suc ΘL) ΘR
newTag = nothing , seals zero [] [] (desc (★⊑★ {Φ = []}) []ᵛ []ᵛ)

-- the left allocates
tagsL : (w : World) → TyVar (suc (ΔL w)) → Tag (suc (ΔL w)) (ΔR w)
tagsL w zero = newTag
tagsL w (suc X) = renameTag wk↪ᵗ id↪ᵗ (tag w X)

okBindL : ∀ (w : World) (T : Ty (ΔL w)) X
  → tagsL w (toRenameᵗ (embedᶜˢ (bind T ∷ [])) X)
    ≡ renameTag (embedᶜˢ (bind T ∷ [])) (embedᶜˢ ([] {ΔR w})) (tag w X)
okBindL w T X =
  trans (cong (tagsL w) (embed-var T X))
    (sym (cong (λ ρ → renameTag ρ id↪ᵗ (tag w X)) (embed-bind T)))

-- both allocate
tagsLR : (w : World) → TyVar (suc (ΔL w))
  → Tag (suc (ΔL w)) (suc (ΔR w))
tagsLR w zero = newTag
tagsLR w (suc X) = renameTag wk↪ᵗ wk↪ᵗ (tag w X)

okBindLR : ∀ (w : World) (T : Ty (ΔL w)) (T′ : Ty (ΔR w)) X
  → tagsLR w (toRenameᵗ (embedᶜˢ (bind T ∷ [])) X)
    ≡ renameTag (embedᶜˢ (bind T ∷ [])) (embedᶜˢ (bind T′ ∷ [])) (tag w X)
okBindLR w T T′ X =
  trans (cong (tagsLR w) (embed-var T X))
    (sym (cong₂ (λ ρ ρ′ → renameTag ρ ρ′ (tag w X))
      (embed-bind T) (embed-bind T′)))

------------------------------------------------------------------------
-- Instantiating a proxy
------------------------------------------------------------------------

revInst : ∀ {Θ} {V : Term Θ} {T} {C B B′ : Ty (suc Θ)}
    (c : Conv↑ (suc Θ) C B) → Value V → B ≡ B′
  → (V ↑ `∀↑ c) ⦂∀ B′ [ T ] —→[ bind T ]
      ((⇑ᵗᵐ V ⦂∀ (bind T ▷ᵇ C) [ ＇ zero ]) ↑ c ↑ 〖 zero , ⇑ᵗ T ↑ B′ 〗)
revInst c v refl = β-reveal-∀ v

conInst : ∀ {Θ} {V : Term Θ} {T} {C B B′ : Ty (suc Θ)}
    (c : Conv↓ (suc Θ) C B) → Value V → B ≡ B′
  → (V ↓ `∀↓ c) ⦂∀ B′ [ T ] —→[ bind T ]
      ((⇑ᵗᵐ V ⦂∀ (bind T ▷ᵇ C) [ ＇ zero ]) ↓ c ↑ 〖 zero , ⇑ᵗ T ↑ B′ 〗)
conInst c v refl = β-conceal-∀ v

------------------------------------------------------------------------
-- Prefixing a sealed descriptor with new store variables
------------------------------------------------------------------------

sealS : ∀ {ΘL ΘR} → TyVar ΘL → TyVar ΘR → SDesc ΘL ΘR → SDesc ΘL ΘR
sealS β β′ (sdesc Xs Ys c) = sdesc (β ∷ Xs) (β′ ∷ Ys) c

sealSL : ∀ {ΘL ΘR} → TyVar ΘL → SDesc ΘL ΘR → SDesc ΘL ΘR
sealSL β (sdesc Xs Ys c) = sdesc (β ∷ Xs) Ys c

-- peeling a right seal is a sealed right value
peelSR→ : ∀ {Y : TyVar ΘR} {Ys} {c : Desc ΘL ΘR} {P V V′}
  → peelSR (Y ∷ Ys) c P V V′ → sealedR Y (repR Ys c) (peelSR Ys c P) V V′
peelSR→ {V′ = V′ ↓ s} r = r
peelSR→ {V′ = ` x₀} ()
peelSR→ {V′ = ƛ M₀} ()
peelSR→ {V′ = L₀ · M₀} ()
peelSR→ {V′ = Λ M₀} ()
peelSR→ {V′ = L₀ ⦂∀ C₀ [ T₀ ]} ()
peelSR→ {V′ = $ κ₀} ()
peelSR→ {V′ = L₀ ⊕[ op₀ ] M₀} ()
peelSR→ {V′ = W₀ ⟨ c₀ ⟩} ()
peelSR→ {V′ = M₀ ↑ c₀} ()
peelSR→ {V′ = blame} ()

peelSR← : ∀ {Y : TyVar ΘR} {Ys} {c : Desc ΘL ΘR} {P V V′}
  → sealedR Y (repR Ys c) (peelSR Ys c P) V V′ → peelSR (Y ∷ Ys) c P V V′
peelSR← r with sealedR-inv r
peelSR← r | W′ , refl , q = r

-- a right seal commutes with peeling left seals
peelSL-sealedR : ∀ (Xs : List (TyVar ΘL)) (c : Desc ΘL ΘR) {β : TyVar ΘR}
    {R} {P : Term ΘL → Term ΘR → Set} {V V′}
  → peelSL Xs c (sealedR β R P) V V′ → sealedR β R (peelSL Xs c P) V V′
peelSL-sealedR [] c r = r
peelSL-sealedR (X ∷ Xs) c {V = V ↓ s} (is , r)
    with sealedR-inv (peelSL-sealedR Xs c r)
peelSL-sealedR (X ∷ Xs) c {V = V ↓ s} (is , r) | W′ , refl , q =
  (refl , refl) , is , q
peelSL-sealedR (X ∷ Xs) c {V = ` x₀} ()
peelSL-sealedR (X ∷ Xs) c {V = ƛ M₀} ()
peelSL-sealedR (X ∷ Xs) c {V = L₀ · M₀} ()
peelSL-sealedR (X ∷ Xs) c {V = Λ M₀} ()
peelSL-sealedR (X ∷ Xs) c {V = L₀ ⦂∀ C₀ [ T₀ ]} ()
peelSL-sealedR (X ∷ Xs) c {V = $ κ₀} ()
peelSL-sealedR (X ∷ Xs) c {V = L₀ ⊕[ op₀ ] M₀} ()
peelSL-sealedR (X ∷ Xs) c {V = W₀ ⟨ c₀ ⟩} ()
peelSL-sealedR (X ∷ Xs) c {V = M₀ ↑ c₀} ()
peelSL-sealedR (X ∷ Xs) c {V = blame} ()

sealedR-peelSL : ∀ (Xs : List (TyVar ΘL)) (c : Desc ΘL ΘR) {β : TyVar ΘR}
    {R} {P : Term ΘL → Term ΘR → Set} {V V′}
  → sealedR β R (peelSL Xs c P) V V′ → peelSL Xs c (sealedR β R P) V V′
sealedR-peelSL [] c r = r
sealedR-peelSL (X ∷ Xs) c {V = V ↓ s} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = V ↓ s} r | W′ , refl , (is , q) =
  is , sealedR-peelSL Xs c ((refl , refl) , q)
sealedR-peelSL (X ∷ Xs) c {V = ` x₀} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = ` x₀} r | W′ , refl , ()
sealedR-peelSL (X ∷ Xs) c {V = ƛ M₀} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = ƛ M₀} r | W′ , refl , ()
sealedR-peelSL (X ∷ Xs) c {V = L₀ · M₀} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = L₀ · M₀} r | W′ , refl , ()
sealedR-peelSL (X ∷ Xs) c {V = Λ M₀} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = Λ M₀} r | W′ , refl , ()
sealedR-peelSL (X ∷ Xs) c {V = L₀ ⦂∀ C₀ [ T₀ ]} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = L₀ ⦂∀ C₀ [ T₀ ]} r | W′ , refl , ()
sealedR-peelSL (X ∷ Xs) c {V = $ κ₀} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = $ κ₀} r | W′ , refl , ()
sealedR-peelSL (X ∷ Xs) c {V = L₀ ⊕[ op₀ ] M₀} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = L₀ ⊕[ op₀ ] M₀} r | W′ , refl , ()
sealedR-peelSL (X ∷ Xs) c {V = W₀ ⟨ c₀ ⟩} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = W₀ ⟨ c₀ ⟩} r | W′ , refl , ()
sealedR-peelSL (X ∷ Xs) c {V = M₀ ↑ c₀} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = M₀ ↑ c₀} r | W′ , refl , ()
sealedR-peelSL (X ∷ Xs) c {V = blame} r with sealedR-inv r
sealedR-peelSL (X ∷ Xs) c {V = blame} r | W′ , refl , ()

-- the leaf of a prefixed descriptor: the new seals, then the leaf of the
-- descriptor
module _ (d : Dir) {n′ n} (le : n′ ≤′ n) {ΘL ΘR}
    (Xs : List (TyVar ΘL)) (Ys : List (TyVar ΘR)) (c : Desc ΘL ΘR)
    (β : TyVar ΘL) (β′ : TyVar ΘR) (k : ℕ) (w : World)
    (τL : ΘL ↪ᵗ ΔL w) (τR : ΘR ↪ᵗ ΔR w) where

  private
    c′ = renameDesc τL τR c
    Xs′ = map (renameVar τL) Xs
    Ys′ = map (renameVar τR) Ys

  sealS→ : ∀ {V V′}
    → leafBelowS d le (sealS β β′ (sdesc Xs Ys c)) k w τL τR V V′
    → sealedL (renameVar τL β) (repL Xs′ c′)
        (sealedR (renameVar τR β′) (repR Ys′ c′)
          (leafBelowS d le (sdesc Xs Ys c) k w τL τR)) V V′
  sealS→ {V = V ↓ s} (is , r) =
    is , peelSL-sealedR Xs′ c′ (peelSL-map Xs′ c′ peelSR→ r)
  sealS→ {V = ` x₀} ()
  sealS→ {V = ƛ M₀} ()
  sealS→ {V = L₀ · M₀} ()
  sealS→ {V = Λ M₀} ()
  sealS→ {V = L₀ ⦂∀ C₀ [ T₀ ]} ()
  sealS→ {V = $ κ₀} ()
  sealS→ {V = L₀ ⊕[ op₀ ] M₀} ()
  sealS→ {V = W₀ ⟨ c₀ ⟩} ()
  sealS→ {V = M₀ ↑ c₀} ()
  sealS→ {V = blame} ()

  sealS← : ∀ {V V′}
    → sealedL (renameVar τL β) (repL Xs′ c′)
        (sealedR (renameVar τR β′) (repR Ys′ c′)
          (leafBelowS d le (sdesc Xs Ys c) k w τL τR)) V V′
    → leafBelowS d le (sealS β β′ (sdesc Xs Ys c)) k w τL τR V V′
  sealS← r with sealedL-inv r
  sealS← r | W , refl , q =
    proj₁ r , peelSL-map Xs′ c′ peelSR← (sealedR-peelSL Xs′ c′ q)

-- a left prefix
module _ (d : Dir) {n′ n} (le : n′ ≤′ n) {ΘL ΘR}
    (Xs : List (TyVar ΘL)) (Ys : List (TyVar ΘR)) (c : Desc ΘL ΘR)
    (β : TyVar ΘL) (k : ℕ) (w : World)
    (τL : ΘL ↪ᵗ ΔL w) (τR : ΘR ↪ᵗ ΔR w) where

  private
    c′ = renameDesc τL τR c
    Xs′ = map (renameVar τL) Xs

  sealSL→ : ∀ {V V′}
    → leafBelowS d le (sealSL β (sdesc Xs Ys c)) k w τL τR V V′
    → sealedL (renameVar τL β) (repL Xs′ c′)
        (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′
  sealSL→ {V = V ↓ s} r = r
  sealSL→ {V = ` x₀} ()
  sealSL→ {V = ƛ M₀} ()
  sealSL→ {V = L₀ · M₀} ()
  sealSL→ {V = Λ M₀} ()
  sealSL→ {V = L₀ ⦂∀ C₀ [ T₀ ]} ()
  sealSL→ {V = $ κ₀} ()
  sealSL→ {V = L₀ ⊕[ op₀ ] M₀} ()
  sealSL→ {V = W₀ ⟨ c₀ ⟩} ()
  sealSL→ {V = M₀ ↑ c₀} ()
  sealSL→ {V = blame} ()

  sealSL← : ∀ {V V′}
    → sealedL (renameVar τL β) (repL Xs′ c′)
        (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′
    → leafBelowS d le (sealSL β (sdesc Xs Ys c)) k w τL τR V V′
  sealSL← r with sealedL-inv r
  sealSL← r | W , refl , q = r

------------------------------------------------------------------------
-- Clause leaves under other bounds and renamings
------------------------------------------------------------------------

-- below both bounds, the bound does not matter
leafBelow-bound : ∀ d {n₁ a₁ n₂ a₂} (le₁ : n₁ ≤′ a₁) (le₂ : n₂ ≤′ a₂)
    (c : Desc ΘL ΘR) {k} → suc k ≤ n₂ → ∀ w τL τR {V V′}
  → leafBelow d le₁ c k w τL τR V V′ → leafBelow d le₂ c k w τL τR V V′
leafBelow-bound d {n₁} {n₂ = n₂} le₁ le₂ c {k} lt w τL τR r
    with suc k ≤? n₁ | suc k ≤? n₂
leafBelow-bound d le₁ le₂ (desc p env envR) {k} lt w τL τR r
    | yes lt₁ | yes lt₂ =
  𝒱→𝒱< d (≤′-trans (≤⇒≤′ lt₂) le₂) p w
    (𝒱<→𝒱 d (≤′-trans (≤⇒≤′ lt₁) le₁) p w r)
leafBelow-bound d le₁ le₂ c {k} lt w τL τR r | yes lt₁ | no ¬lt₂ =
  ⊥-elim (¬lt₂ lt)
leafBelow-bound d le₁ le₂ c {k} lt w τL τR () | no ¬lt₁ | _

leafBelowS-bound : ∀ d {n₁ a₁ n₂ a₂} (le₁ : n₁ ≤′ a₁) (le₂ : n₂ ≤′ a₂)
    (c : SDesc ΘL ΘR) {k} → suc k ≤ n₂ → ∀ w τL τR {V V′}
  → leafBelowS d le₁ c k w τL τR V V′ → leafBelowS d le₂ c k w τL τR V V′
leafBelowS-bound d le₁ le₂ c lt w τL τR =
  peelS-map c (leafBelow-bound d le₁ le₂ (core c) lt w τL τR)

-- a renamed descriptor's leaf is the leaf at the composite embeddings
leafBelow-ren : ∀ d {n′ n} (le : n′ ≤′ n) {ΘL′ ΘR′}
    (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′) (c : Desc ΘL ΘR) k w τL τR {V V′}
  → leafBelow d le (renameDesc σL σR c) k w τL τR V V′
    ⇔ leafBelow d le c k w (τL ∘↪ σL) (τR ∘↪ σR) V V′
leafBelow-ren d {n′} le σL σR c k w τL τR with suc k ≤? n′
leafBelow-ren d {n′} le σL σR c k w τL τR | yes lt =
  iff (subst (λ c′ → descBelow d _ w c′ _ _) (renameDesc-∘ τL σL τR σR c))
      (subst (λ c′ → descBelow d _ w c′ _ _)
        (sym (renameDesc-∘ τL σL τR σR c)))
leafBelow-ren d {n′} le σL σR c k w τL τR | no ¬lt = iff (λ r → r) (λ r → r)

leafBelowS-ren : ∀ d {n′ n} (le : n′ ≤′ n) {ΘL′ ΘR′}
    (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′) (c : SDesc ΘL ΘR) k w τL τR {V V′}
  → leafBelowS d le (renameSDesc σL σR c) k w τL τR V V′
    ⇔ leafBelowS d le c k w (τL ∘↪ σL) (τR ∘↪ σR) V V′
leafBelowS-ren d le σL σR (sdesc Xs Ys c) k w τL τR {V} {V′} =
  iff
    (λ r → subst (λ c′ → F Xs₂ Ys₂ c′) eqc
             (subst (λ Ys′ → F Xs₂ Ys′ c₁) eqY
               (subst (λ Xs′ → F Xs′ Ys₁ c₁) eqX
                 (peelSL-map Xs₁ c₁
                   (peelSR-map Ys₁ c₁
                     (to (leafBelow-ren d le σL σR c k w τL τR))) r))))
    (λ r → peelSL-map Xs₁ c₁
             (peelSR-map Ys₁ c₁
               (from (leafBelow-ren d le σL σR c k w τL τR)))
             (subst (λ Xs′ → F Xs′ Ys₁ c₁) (sym eqX)
               (subst (λ Ys′ → F Xs₂ Ys′ c₁) (sym eqY)
                 (subst (λ c′ → F Xs₂ Ys₂ c′) (sym eqc) r))))
  where
  Xs₁ = map (renameVar τL) (map (renameVar σL) Xs)
  Xs₂ = map (renameVar (τL ∘↪ σL)) Xs
  Ys₁ = map (renameVar τR) (map (renameVar σR) Ys)
  Ys₂ = map (renameVar (τR ∘↪ σR)) Ys
  c₁ = renameDesc τL τR (renameDesc σL σR c)
  eqX = map-renameVar-∘ τL σL Xs
  eqY = map-renameVar-∘ τR σR Ys
  eqc = renameDesc-∘ τL σL τR σR c
  F : List (TyVar (ΔL w)) → List (TyVar (ΔR w)) → Desc (ΔL w) (ΔR w)
    → Set
  F Xs′ Ys′ c′ =
    peelSL Xs′ c′
      (peelSR Ys′ c′ (leafBelow d le c k w (τL ∘↪ σL) (τR ∘↪ σR))) V V′

-- the oracle at a lower bound
Oracle-down : ∀ {d N N′} → N′ ≤ N → Oracle d N → Oracle d N′
Oracle-down le (op , oo) =
  (λ l b c → op l (≤-trans b le) c) , (λ l b c → oo l (≤-trans b le) c)

------------------------------------------------------------------------
-- The store variable an allocation creates
------------------------------------------------------------------------

-- the new variable is not the image of an old one
new-bind : ∀ {Θ} (T : Ty Θ) X → toRenameᵗ (embedᶜˢ (bind T ∷ [])) X ≢ zero
new-bind T X eq with trans (sym (embed-var T X)) eq
new-bind T X eq | ()

-- and stays new in later futures
NewL-after : ∀ {w w₁ w′ : World} (e₁ : w₁ ⊒ w) (e′ : w′ ⊒ w₁) {β}
  → (∀ X → toRenameᵗ (ρL e₁) X ≢ β)
  → NewL (⊒-trans e′ e₁) (toRenameᵗ (ρL e′) β)
NewL-after e₁ e′ nb X eq =
  nb X (toRenameᵗ-injective (ρL e′)
    (trans (sym (toRenameᵗ-∘ (ρL e′) (ρL e₁) X)) eq))

NewR-after : ∀ {w w₁ w′ : World} (e₁ : w₁ ⊒ w) (e′ : w′ ⊒ w₁) {β′}
  → (∀ Y → toRenameᵗ (ρR e₁) Y ≢ β′)
  → ∀ Y → toRenameᵗ (ρR (⊒-trans e′ e₁)) Y ≢ toRenameᵗ (ρR e′) β′
NewR-after e₁ e′ nb Y eq =
  nb Y (toRenameᵗ-injective (ρR e′)
    (trans (sym (toRenameᵗ-∘ (ρR e′) (ρR e₁) Y)) eq))

------------------------------------------------------------------------
-- Closure under the conversion at a new store variable
------------------------------------------------------------------------

NewRC₁ : ∀ {w w₁ : World} → w₁ ⊒ w → RConv (ΔR w₁) → Set
NewRC₁ e₁ nothing = ⊤
NewRC₁ e₁ (just (β′ , R′)) = ∀ Y → toRenameᵗ (ρR e₁) Y ≢ β′

NewRC-after : ∀ {w w₁ w′ : World} (e₁ : w₁ ⊒ w) (e′ : w′ ⊒ w₁)
    (rc : RConv (ΔR w₁))
  → NewRC₁ e₁ rc → NewRC (⊒-trans e′ e₁) (renRConv (ρR e′) rc)
NewRC-after e₁ e′ nothing nb = tt
NewRC-after e₁ e′ (just (β′ , R′)) nb = NewR-after e₁ e′ nb

module _ {d} {w w₁ : World} (e₁ : w₁ ⊒ w) {L : Leaf (ΔL w) (ΔR w)}
    {β : TyVar (ΔL w₁)} (nb : ∀ X → toRenameᵗ (ρL e₁) X ≢ β) where

  private
    L₁ = transportLeaf (ρL e₁) (ρR e₁) L

  fresh→convP : ∀ {rk T T′ N} (R : Ty (ΔL w₁)) (rc : RConv (ΔR w₁))
    → Allowed rk rc → NewRC₁ e₁ rc → FreshP d rk w L T T′
    → ConvLeafP d N w₁ R rc β L₁ L₁ (renameᵗ (toRenameᵗ (ρL e₁)) T)
        (renameᵗ (toRenameᵗ (ρR e₁)) T′)
  fresh→convP {rk} {T} {T′} R rc ok nrc f {w′} e′ {k} k≤N =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w′ (≈ˡ-sym L∘)
        (ℰL-≡ d k w′ L₂
          (cong (λ C → Vl ↑ 〖 toRenameᵗ (ρL e′) β
                            , renameᵗ (toRenameᵗ (ρL e′)) R ↑ C 〗)
            (sym (renameTy-∘ (ρL e′) (ρL e₁) T)))
          (cong (λ C → revM (renRConv (ρR e′) rc) C Vr)
            (sym (renameTy-∘ (ρR e′) (ρR e₁) T′)))
          (proj₁ g vl vr (leafRel-resp d k w′ L∘ r)))) ,
    (λ {Wl} {Wr} wl wr r →
      ℰL-resp d k w′ (≈ˡ-sym L∘)
        (ℰL-≡ d k w′ L₂
          (cong (λ C → Wl ↓ makeConceal (toRenameᵗ (ρL e′) β)
                            (renameᵗ (toRenameᵗ (ρL e′)) R) C)
            (sym (renameTy-∘ (ρL e′) (ρL e₁) T)))
          (cong (λ C → conM (renRConv (ρR e′) rc) C Wr)
            (sym (renameTy-∘ (ρR e′) (ρR e₁) T′)))
          (proj₂ g wl wr (leafRel-resp d k w′ L∘ r))))
    where
    L∘ = transportLeaf-∘ (ρL e′) (ρL e₁) (ρR e′) (ρR e₁) L
    L₂ = transportLeaf (ρL e′ ∘↪ ρL e₁) (ρR e′ ∘↪ ρR e₁) L
    g = f (⊒-trans e′ e₁) (renRConv (ρR e′) rc) (Allowed-ren rk (ρR e′) rc ok)
          (NewL-after e₁ e′ nb) (NewRC-after e₁ e′ rc nrc) {k}

  fresh→convO : ∀ {T N} (R : Ty (ΔL w₁)) → FreshO d w L T
    → ConvLeafO d N w₁ R β L₁ L₁ (renameᵗ (toRenameᵗ (ρL e₁)) T)
  fresh→convO {T} R f {w′} e′ {k} k≤N =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w′ (≈ˡ-sym L∘)
        (ℰL-≡ d k w′ L₂
          (cong (λ C → Vl ↑ 〖 toRenameᵗ (ρL e′) β
                            , renameᵗ (toRenameᵗ (ρL e′)) R ↑ C 〗)
            (sym (renameTy-∘ (ρL e′) (ρL e₁) T)))
          refl
          (proj₁ g vl vr (leafRel-resp d k w′ L∘ r)))) ,
    (λ {Wl} {Vr} wl vr r →
      ℰL-resp d k w′ (≈ˡ-sym L∘)
        (ℰL-≡ d k w′ L₂
          (cong (λ C → Wl ↓ makeConceal (toRenameᵗ (ρL e′) β)
                            (renameᵗ (toRenameᵗ (ρL e′)) R) C)
            (sym (renameTy-∘ (ρL e′) (ρL e₁) T)))
          refl
          (proj₂ g wl vr (leafRel-resp d k w′ L∘ r))))
    where
    L∘ = transportLeaf-∘ (ρL e′) (ρL e₁) (ρR e′) (ρR e₁) L
    L₂ = transportLeaf (ρL e′ ∘↪ ρL e₁) (ρR e′ ∘↪ ρR e₁) L
    g = f (⊒-trans e′ e₁) (NewL-after e₁ e′ nb) {k}

------------------------------------------------------------------------
-- Store-variable leaves under conversions
------------------------------------------------------------------------

-- the right side's conversion is not at γ′
RNe : ∀ {Θ} → RConv Θ → TyVar Θ → Set
RNe nothing γ′ = ⊤
RNe (just (α′ , R′)) γ′ = γ′ ≢ α′

RNe-ren : ∀ {Θ Θ′} (ρ : Θ ↪ᵗ Θ′) (rc : RConv Θ) {γ′}
  → RNe rc γ′ → RId (renRConv ρ rc) (＇ toRenameᵗ ρ γ′)
RNe-ren ρ nothing ne = tt
RNe-ren ρ (just (α′ , R′)) ne =
  toRenameᵗ ρ _ , refl , (λ eq → ne (toRenameᵗ-injective ρ eq))

module _ {d : Dir} {N : ℕ} {w : World} {L : Leaf (ΔL w) (ΔR w)}
    (gl : GoodLeaf L) {γ : TyVar (ΔL w)} {γ′ : TyVar (ΔR w)} where

  -- under the conversion at hand, at another store variable
  storeConvP : ∀ R (rc : RConv (ΔR w)) {α} → γ ≢ α → RNe rc γ′
    → ConvLeafP d N w R rc α L L (＇ γ) (＇ γ′)
  storeConvP R rc ne rn {w′} e {k} k≤N =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq))
        (renRConv (ρR e) rc) (RNe-ren (ρR e) rc rn) vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq))
        (renRConv (ρR e) rc) (RNe-ren (ρR e) rc rn) wl wr r)

  -- under later conversions
  storeFreshP : ∀ {rk} → FreshP d rk w L (＇ γ) (＇ γ′)
  storeFreshP {rk} {w′} e {β} {R} rc ok nb nrc {k} =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) rc (rid rc nrc) vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) rc (rid rc nrc) wl wr r)
    where
    rid : (rc′ : RConv (ΔR w′)) → NewRC e rc′
      → RId rc′ (＇ toRenameᵗ (ρR e) γ′)
    rid nothing n = tt
    rid (just (β′ , R′)) n = toRenameᵗ (ρR e) γ′ , refl , n γ′

-- a store-variable leaf whose right side is not converted
module _ {d : Dir} {N : ℕ} {w : World} {L : Leaf (ΔL w) (ΔR w)}
    (gl : GoodLeaf L) {γ : TyVar (ΔL w)} {T′ : Ty (ΔR w)} where

  storeConvPN : ∀ R {α} → γ ≢ α
    → ConvLeafP d N w R nothing α L L (＇ γ) T′
  storeConvPN R ne {w′} e {k} k≤N =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq)) nothing
        {T′ = renameᵗ (toRenameᵗ (ρR e)) T′} tt vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq)) nothing
        {T′ = renameᵗ (toRenameᵗ (ρR e)) T′} tt wl wr r)

  storeFreshPL : FreshP d left w L (＇ γ) T′
  storeFreshPL {w′} e {β} {R} nothing ok nb nrc {k} =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) nothing
        {T′ = renameᵗ (toRenameᵗ (ρR e)) T′} tt vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) nothing
        {T′ = renameᵗ (toRenameᵗ (ρR e)) T′} tt wl wr r)
  storeFreshPL e (just c) () nb nrc

-- a left-only store-variable leaf, under later conversions
module _ {d : Dir} {w : World} {L : Leaf (ΔL w) (ΔR w)}
    (gl : GoodLeaf L) {γ : TyVar (ΔL w)} where

  storeFreshO : FreshO d w L (＇ γ)
  storeFreshO {w′} e {β} {R} nb {k} =
    (λ vl vr r →
      idRevO d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) vl vr r) ,
    (λ wl vr r →
      idConO d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) wl vr r)

------------------------------------------------------------------------
-- The hypotheses for a type application's bound variable
------------------------------------------------------------------------

Allowed-nothing : ∀ {Θ} rk → Allowed {Θ} rk nothing
Allowed-nothing both = tt
Allowed-nothing left = tt

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {d : Dir} {N : ℕ}
    {w : World} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {w₁ : World} (e₁ : w₁ ⊒ w)
    {β : TyVar (ΔL w₁)} (nb : ∀ X → toRenameᵗ (ρL e₁) X ≢ β)
    {Ls : Leaf (ΔL w₁) (ΔR w₁)} {Lt : Leaf (ΔL w) (ΔR w)}
    {Tl : Ty (ΔL w)} where

  private
    ρl = toRenameᵗ (ρL e₁)
    ρr = toRenameᵗ (ρR e₁)

  -- a paired binder; the right converts its own store variable β′
  ConvI-newP : ∀ {Tr : Ty (ΔR w)} {β′ : TyVar (ΔR w₁)} {Nβ}
    → (∀ Y → ρr Y ≢ β′) → Nβ ≤ N → FreshI Φ d N both w δt
    → GoodLeaf Ls → GoodLeaf Lt → FreshP d both w Lt Tl Tr
    → SealI d Nβ w₁ (m-pair {Φ = pair Φ} ↔-here β′) β
        (extPairI (＇ β) (＇ β′) Ls (δt ↑ᴵ e₁)) (extPairI Tl Tr Lt δt ↑ᴵ e₁)
    → ConvI d Nβ both w₁ (m-pair {Φ = pair Φ} ↔-here β′) β
        (extPairI (＇ β) (＇ β′) Ls (δt ↑ᴵ e₁)) (extPairI Tl Tr Lt δt ↑ᴵ e₁)
  goodS (ConvI-newP {β′ = β′} nb′ le h gs gt ft si) =
    GoodI-extPairI {T = ＇ β} {T′ = ＇ β′} {δ = δt ↑ᴵ e₁} gs
      (GoodI-↑ {δ = δt} (fgood h) e₁)
  goodT (ConvI-newP {Tr = Tr} nb′ le h gs gt ft si) =
    GoodI-↑ {δ = extPairI Tl Tr Lt δt}
      (GoodI-extPairI {T = Tl} {T′ = Tr} {δ = δt} gt (fgood h)) e₁
  selfI (ConvI-newP nb′ le h gs gt ft si) = refl , refl
  rcOK (ConvI-newP nb′ le h gs gt ft si) = tt
  tyL (ConvI-newP nb′ le h gs gt ft si) zero = replaceTy-self β _
  tyL (ConvI-newP nb′ le h gs gt ft si) (suc Z) =
    replaceTy-new ρl _ nb (δl δt Z)
  tyR (ConvI-newP {β′ = β′} nb′ le h gs gt ft si) zero = replaceTy-self β′ _
  tyR (ConvI-newP nb′ le h gs gt ft si) (suc Y) =
    replaceTy-new ρr _ nb′ (δr δt Y)
  leafO (ConvI-newP nb′ le h gs gt ft si) zero o = ⊥-elim (o refl)
  leafO (ConvI-newP nb′ le h gs gt ft si) (suc Z) o = ≈ˡ-refl
  convP (ConvI-newP nb′ le h gs gt ft si) ↔-here o = ⊥-elim (o refl)
  convP (ConvI-newP {Tr = Tr} {β′} nb′ le h gs gt ft si)
      (↔-pair {X = Z} {Y = Y′} z) o =
    fresh→convP {d = d} e₁ {L = leaf δt Z} nb {rk = both}
      (renameᵗ ρl Tl) (just (β′ , renameᵗ ρr Tr)) tt nb′
      (fP h z)
  convO (ConvI-newP nb′ le h gs gt ft si) (only-pair {X = Z} z) o =
    fresh→convO {d = d} e₁ {L = leaf δt Z} nb (renameᵗ ρl Tl) (fO h z)
  genP (ConvI-newP nb′ le h gs gt ft si) ↔-here =
    FreshP-↑ {d = d} e₁ {L = Lt} {rk = both} {T = Tl} ft
  genP (ConvI-newP nb′ le h gs gt ft si) (↔-pair {X =
    Z} {Y = Y′} z) = FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = both}
      {T = δl δt Z}
      {T′ = δr δt Y′} (fP h z)
  genO (ConvI-newP nb′ le h gs gt ft si) (only-pair {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z}
      (fO h z)
  genPS (ConvI-newP {β′ = β′} nb′ le h gs gt ft si) ↔-here =
    storeFreshP {d = d} {N = N} {w = w₁} {L = Ls} gs {γ = β} {γ′ = β′}
      {rk = both}
  genPS (ConvI-newP nb′ le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) =
    FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = both} {T = δl δt Z}
      {T′ = δr δt Y′} (fP h z)
  genOS (ConvI-newP nb′ le h gs gt ft si) (only-pair {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z} (fO h z)
  sealI (ConvI-newP nb′ le h gs gt ft si) = si
  oracle (ConvI-newP nb′ le h gs gt ft si) = Oracle-down le (forc h)

  -- a paired binder; the right does not convert, and is instantiated at
  -- Tr itself
  ConvI-newL : ∀ {rk} {Tr : Ty (ΔR w)} {T′ : Ty (ΔR w₁)} {Nβ}
    → T′ ≡ renameᵗ ρr Tr → Nβ ≤ N
    → FreshI Φ d N rk w δt
    → GoodLeaf Ls → GoodLeaf Lt → FreshP d both w Lt Tl Tr
    → SealI d Nβ w₁ (m-left {Φ = pair Φ} {X = zero}) β
        (extPairI (＇ β) T′ Ls (δt ↑ᴵ e₁))
        (extPairI Tl Tr Lt δt ↑ᴵ e₁)
    → ConvI d Nβ left w₁ (m-left {Φ = pair Φ} {X = zero}) β
        (extPairI (＇ β) T′ Ls (δt ↑ᴵ e₁))
        (extPairI Tl Tr Lt δt ↑ᴵ e₁)
  goodS (ConvI-newL {Tr = Tr} {T′} eqT le h gs gt ft si) =
    GoodI-extPairI {T = ＇ β} {T′ = T′} {δ = δt ↑ᴵ e₁} gs
      (GoodI-↑ {δ = δt} (fgood h) e₁)
  goodT (ConvI-newL {Tr = Tr} {T′} eqT le h gs gt ft si) =
    GoodI-↑ {δ = extPairI Tl Tr Lt δt}
      (GoodI-extPairI {T = Tl} {T′ = Tr} {δ = δt} gt (fgood h)) e₁
  selfI (ConvI-newL eqT le h gs gt ft si) = refl
  rcOK (ConvI-newL eqT le h gs gt ft si) = tt
  tyL (ConvI-newL eqT le h gs gt ft si) zero = replaceTy-self β _
  tyL (ConvI-newL eqT le h gs gt ft si) (suc Z) =
    replaceTy-new ρl _ nb (δl δt Z)
  tyR (ConvI-newL eqT le h gs gt ft si) zero = eqT
  tyR (ConvI-newL eqT le h gs gt ft si) (suc Y) = refl
  leafO (ConvI-newL eqT le h gs gt ft si) zero o = ⊥-elim (o refl)
  leafO (ConvI-newL eqT le h gs gt ft si) (suc Z) o = ≈ˡ-refl
  convP (ConvI-newL {rk} eqT le h gs gt ft si) ↔-here o = ⊥-elim (o refl)
  convP (ConvI-newL {rk} eqT le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) o =
    fresh→convP {d = d} e₁ {L = leaf δt Z} nb {rk = left}
      (renameᵗ ρl Tl) nothing tt tt
      (FreshP-left {rk = rk} {L = leaf δt Z} {T = δl δt Z}
        {T′ = δr δt Y′} (fP h z))
  convO (ConvI-newL eqT le h gs gt ft si) (only-pair {X = Z} z) o =
    fresh→convO {d = d} e₁ {L = leaf δt Z} nb (renameᵗ ρl Tl) (fO h z)
  genP (ConvI-newL {rk} {Tr = Tr} eqT le h gs gt ft si) ↔-here =
    FreshP-left {rk = both}
      {L = transportLeaf (ρL e₁) (ρR e₁) Lt} {T = renameᵗ ρl Tl}
      {T′ = renameᵗ ρr Tr}
      (FreshP-↑ {d = d} e₁ {L = Lt} {rk = both} {T = Tl} ft)
  genP (ConvI-newL {rk} eqT le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) =
    FreshP-left {rk = rk}
      {L = transportLeaf (ρL e₁) (ρR e₁) (leaf δt Z)}
      {T = renameᵗ ρl (δl δt Z)} {T′ = renameᵗ ρr (δr δt Y′)}
      (FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
        {T′ = δr δt Y′} (fP h z))
  genO (ConvI-newL eqT le h gs gt ft si) (only-pair {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z}
      (fO h z)
  genPS (ConvI-newL {T′ = T′} eqT le h gs gt ft si) ↔-here =
    storeFreshPL {d = d} {N = N} {w = w₁} {L = Ls} gs {γ = β} {T′ = T′}
  genPS (ConvI-newL {rk} eqT le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) =
    FreshP-left {rk = rk}
      {L = transportLeaf (ρL e₁) (ρR e₁) (leaf δt Z)}
      {T = renameᵗ ρl (δl δt Z)} {T′ = renameᵗ ρr (δr δt Y′)}
      (FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
        {T′ = δr δt Y′} (fP h z))
  genOS (ConvI-newL eqT le h gs gt ft si) (only-pair {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z} (fO h z)
  sealI (ConvI-newL eqT le h gs gt ft si) = si
  oracle (ConvI-newL eqT le h gs gt ft si) = Oracle-down le (forc h)

  -- a left-only binder
  ConvI-newO : ∀ {rk} {Nβ} → Nβ ≤ N → FreshI Φ d N rk w δt
    → GoodLeaf Ls → GoodLeaf Lt → FreshO d w Lt Tl
    → SealI d Nβ w₁ (m-left {Φ = only Φ} {X = zero}) β
        (extOnlyI (＇ β) Ls (δt ↑ᴵ e₁)) (extOnlyI Tl Lt δt ↑ᴵ e₁)
    → ConvI d Nβ rk w₁ (m-left {Φ = only Φ} {X = zero}) β
        (extOnlyI (＇ β) Ls (δt ↑ᴵ e₁)) (extOnlyI Tl Lt δt ↑ᴵ e₁)
  goodS (ConvI-newO le h gs gt ft si) =
    GoodI-extOnlyI {T = ＇ β} {δ = δt ↑ᴵ e₁} gs
      (GoodI-↑ {δ = δt} (fgood h) e₁)
  goodT (ConvI-newO le h gs gt ft si) =
    GoodI-↑ {δ = extOnlyI Tl Lt δt}
      (GoodI-extOnlyI {T = Tl} {δ = δt} gt (fgood h)) e₁
  selfI (ConvI-newO le h gs gt ft si) = refl
  rcOK (ConvI-newO {rk} le h gs gt ft si) = Allowed-nothing rk
  tyL (ConvI-newO le h gs gt ft si) zero = replaceTy-self β _
  tyL (ConvI-newO le h gs gt ft si) (suc Z) = replaceTy-new ρl _ nb (δl δt Z)
  tyR (ConvI-newO le h gs gt ft si) Y = refl
  leafO (ConvI-newO le h gs gt ft si) zero o = ⊥-elim (o refl)
  leafO (ConvI-newO le h gs gt ft si) (suc Z) o = ≈ˡ-refl
  convP (ConvI-newO {rk} le h gs gt ft si) (↔-only {X = Z} {Y = Y′} z) o =
    fresh→convP {d = d} e₁ {L = leaf δt Z} nb {rk = rk}
      (renameᵗ ρl Tl) nothing (Allowed-nothing rk) tt
      (fP h z)
  convO (ConvI-newO le h gs gt ft si) only-here o = ⊥-elim (o refl)
  convO (ConvI-newO le h gs gt ft si) (only-only {X = Z} z) o =
    fresh→convO {d = d} e₁ {L = leaf δt Z} nb (renameᵗ ρl Tl) (fO h z)
  genP (ConvI-newO {rk} le h gs gt ft si) (↔-only {X =
    Z} {Y = Y′} z) = FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
      {T′ = δr δt Y′} (fP h z)
  genO (ConvI-newO le h gs gt ft si) only-here =
    FreshO-↑ {d = d} e₁ {L = Lt} {T = Tl} ft
  genO (ConvI-newO le h gs gt ft si) (only-only {X =
    Z} z) = FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z}
      (fO h z)
  genPS (ConvI-newO {rk} le h gs gt ft si) (↔-only {X = Z} {Y = Y′} z) =
    FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
      {T′ = δr δt Y′} (fP h z)
  genOS (ConvI-newO le h gs gt ft si) only-here =
    storeFreshO {d = d} {w = w₁} {L = Ls} gs {γ = β}
  genOS (ConvI-newO le h gs gt ft si) (only-only {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z} (fO h z)
  sealI (ConvI-newO le h gs gt ft si) = si
  oracle (ConvI-newO le h gs gt ft si) = Oracle-down le (forc h)

  -- a dead binder, instantiated at Tl
  ConvI-newD : ∀ {rk} {Nβ} → Nβ ≤ N → FreshI Φ d N rk w δt
    → ConvI d Nβ rk w₁ (m-dead {Φ = dead Φ} dead-here) β
        (extDeadI (＇ β) (δt ↑ᴵ e₁)) (extDeadI Tl δt ↑ᴵ e₁)
  goodS (ConvI-newD le h) =
    GoodI-extDeadI {T = ＇ β} {δ = δt ↑ᴵ e₁} (GoodI-↑ {δ = δt} (fgood h) e₁)
  goodT (ConvI-newD le h) =
    GoodI-↑ {δ = extDeadI Tl δt} (GoodI-extDeadI {T = Tl} {δ = δt} (fgood h))
      e₁
  selfI (ConvI-newD le h) = refl
  rcOK (ConvI-newD {rk} le h) = Allowed-nothing rk
  tyL (ConvI-newD le h) zero = replaceTy-self β _
  tyL (ConvI-newD le h) (suc Z) = replaceTy-new ρl _ nb (δl δt Z)
  tyR (ConvI-newD le h) Y = refl
  leafO (ConvI-newD le h) zero o = ⊥-elim (o refl)
  leafO (ConvI-newD le h) (suc Z) o = ≈ˡ-refl
  convP (ConvI-newD {rk} le h) (↔-dead {X = Z} {Y = Y′} z) o =
    fresh→convP {d = d} e₁ {L = leaf δt Z} nb {rk = rk}
      (renameᵗ ρl Tl) nothing (Allowed-nothing rk) tt
      (fP h z)
  convO (ConvI-newD le h) (only-dead {X = Z} z) o =
    fresh→convO {d = d} e₁ {L = leaf δt Z} nb (renameᵗ ρl Tl) (fO h z)
  genP (ConvI-newD {rk} le h) (↔-dead {X =
    Z} {Y = Y′} z) = FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
      {T′ = δr δt Y′} (fP h z)
  genO (ConvI-newD le h) (only-dead {X =
    Z} z) = FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z}
      (fO h z)
  genPS (ConvI-newD {rk} le h) (↔-dead {X = Z} {Y = Y′} z) =
    FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
      {T′ = δr δt Y′} (fP h z)
  genOS (ConvI-newD le h) (only-dead {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z} (fO h z)
  sealI (ConvI-newD le h) = tt
  oracle (ConvI-newD le h) = Oracle-down le (forc h)

-- a larger bound keeps the leaf
leafBelow-up : ∀ d {n₁ a₁ n₂ a₂} (le₁ : n₁ ≤′ a₁) (le₂ : n₂ ≤′ a₂)
    (c : Desc ΘL ΘR) → n₁ ≤ n₂ → ∀ {k} w τL τR {V V′}
  → leafBelow d le₁ c k w τL τR V V′ → leafBelow d le₂ c k w τL τR V V′
leafBelow-up d {n₁} {n₂ = n₂} le₁ le₂ c n₁≤n₂ {k} w τL τR r
    with suc k ≤? n₁ | suc k ≤? n₂
leafBelow-up d le₁ le₂ (desc p env envR) n₁≤n₂ {k} w τL τR r
    | yes lt₁ | yes lt₂ =
  𝒱→𝒱< d (≤′-trans (≤⇒≤′ lt₂) le₂) p w
    (𝒱<→𝒱 d (≤′-trans (≤⇒≤′ lt₁) le₁) p w r)
leafBelow-up d le₁ le₂ c n₁≤n₂ {k} w τL τR r | yes lt₁ | no ¬lt₂ =
  ⊥-elim (¬lt₂ (≤-trans lt₁ n₁≤n₂))
leafBelow-up d le₁ le₂ c n₁≤n₂ {k} w τL τR () | no ¬lt₁ | _

leafBelowS-up : ∀ d {n₁ a₁ n₂ a₂} (le₁ : n₁ ≤′ a₁) (le₂ : n₂ ≤′ a₂)
    (c : SDesc ΘL ΘR) → n₁ ≤ n₂ → ∀ {k} w τL τR {V V′}
  → leafBelowS d le₁ c k w τL τR V V′ → leafBelowS d le₂ c k w τL τR V V′
leafBelowS-up d le₁ le₂ c n₁≤n₂ w τL τR =
  peelS-map c (leafBelow-up d le₁ le₂ (core c) n₁≤n₂ w τL τR)

-- the stage of a left-only leaf is at most the stage
onlyStage-≤ : ∀ d k → onlyStage d k ≤ k
onlyStage-≤ ≺ zero = z≤n
onlyStage-≤ ≺ (suc k) = n≤1+n k
onlyStage-≤ ≻ k = ≤-refl

------------------------------------------------------------------------
-- The seal hypotheses for a type application's bound variable
------------------------------------------------------------------------

-- V's clause, used at the new store variables: the leaf of the prefixed
-- descriptor, with bound s, against the target's leaf, with bound n
module SealNew (d : Dir) {s n a b} (le_s : s ≤′ a) (le_n : n ≤′ b)
    (s≤n : s ≤ n) {w w₁ : World} (e₁ : w₁ ⊒ w)
    (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
    (c : Desc (ΔL w) (ΔR w)) (β : TyVar (ΔL w₁)) where

  private
    c₀ = sdesc Xs Ys c
    c₁ = renameSDesc (ρL e₁) (ρR e₁) c₀
    Lt = sem (leafBelowS d le_n c₀)

  -- the target leaf, read in a future of w₁
  readT : ∀ {w′} (e : w′ ⊒ w₁) k {V V′}
    → leafBelowS d le_s c₁ k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
    → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
        (transportLeaf (ρL e₁) (ρR e₁) Lt)) V V′
  readT e k r =
    leafBelowS-up d le_s le_n c₀ s≤n _ _ _
      (to (leafBelowS-ren d le_s (ρL e₁) (ρR e₁) c₀ k _ _ _) r)

  writeS : ∀ {w′} (e : w′ ⊒ w₁) k → suc k ≤ s → ∀ {V V′}
    → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
        (transportLeaf (ρL e₁) (ρR e₁) Lt)) V V′
    → leafBelowS d le_s c₁ k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
  writeS e k lt r =
    from (leafBelowS-ren d le_s (ρL e₁) (ρR e₁) c₀ k _ _ _)
      (leafBelowS-bound d le_n le_s c₀ lt _ _ _ r)

  -- the representation of the new seal
  repβ : ∀ {w′} (e : w′ ⊒ w₁)
    → repL (map (renameVar (id↪ᵗ ∘↪ ρL e)) (sealsL c₁))
        (renameDesc (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) (core c₁))
      ≡ renameᵗ (toRenameᵗ (ρL e)) (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c))
  repβ e =
    trans (repL-rename (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) (sealsL c₁) (core c₁))
      (trans (cong (λ σ → renameᵗ (toRenameᵗ σ) (repL (sealsL c₁) (core c₁)))
               (∘↪-idˡ (ρL e)))
        (cong (renameᵗ (toRenameᵗ (ρL e)))
          (repL-rename (ρL e₁) (ρR e₁) Xs c)))

  repβ′ : ∀ {w′} (e : w′ ⊒ w₁)
    → repR (map (renameVar (id↪ᵗ ∘↪ ρR e)) (sealsR c₁))
        (renameDesc (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) (core c₁))
      ≡ renameᵗ (toRenameᵗ (ρR e)) (renameᵗ (toRenameᵗ (ρR e₁)) (repR Ys c))
  repβ′ e =
    trans (repR-rename (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) (sealsR c₁) (core c₁))
      (trans (cong (λ σ → renameᵗ (toRenameᵗ σ) (repR (sealsR c₁) (core c₁)))
               (∘↪-idˡ (ρR e)))
        (cong (renameᵗ (toRenameᵗ (ρR e)))
          (repR-rename (ρL e₁) (ρR e₁) Ys c)))

  varβ : ∀ {w′} (e : w′ ⊒ w₁) (X : TyVar (ΔL w₁))
    → renameVar (id↪ᵗ ∘↪ ρL e) X ≡ toRenameᵗ (ρL e) X
  varβ e X = cong (λ σ → toRenameᵗ σ X) (∘↪-idˡ (ρL e))

  varβR : ∀ {w′} (e : w′ ⊒ w₁) (Y : TyVar (ΔR w₁))
    → renameVar (id↪ᵗ ∘↪ ρR e) Y ≡ toRenameᵗ (ρR e) Y
  varβR e Y = cong (λ σ → toRenameᵗ σ Y) (∘↪-idˡ (ρR e))

-- whether a left-only conversion's stage may reach the target's bound
UpB : Dir → ℕ → ℕ → Set
UpB ≺ s n = ⊤
UpB ≻ s n = n ≤ s

-- the target leaf, written into the prefixed descriptor's core, at the
-- stages a left-only conceal needs
writeUp : ∀ d {s n a b} (le_s : s ≤′ a) (le_n : n ≤′ b) {w w₁ : World}
    (e₁ : w₁ ⊒ w) (c₀ : SDesc (ΔL w) (ΔR w)) {w′} (e : w′ ⊒ w₁) k
  → UpB d s n → onlyBelow d k s → ∀ {V V′}
  → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
      (transportLeaf (ρL e₁) (ρR e₁) (sem (leafBelowS d le_n c₀)))) V V′
  → leafBelowS d le_s (renameSDesc (ρL e₁) (ρR e₁) c₀) k w′
      (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
writeUp ≺ le_s le_n e₁ c₀ e k up lt r =
  from (leafBelowS-ren ≺ le_s (ρL e₁) (ρR e₁) c₀ k _ _ _)
    (leafBelowS-bound ≺ le_n le_s c₀ lt _ _ _ r)
writeUp ≻ le_s le_n e₁ c₀ e k up lt r =
  from (leafBelowS-ren ≻ le_s (ρL e₁) (ρR e₁) c₀ k _ _ _)
    (leafBelowS-up ≻ le_n le_s c₀ up _ _ _ r)

module SealNewP (d : Dir) {s n a b} (le_s : s ≤′ a) (le_n : n ≤′ b)
    (s≤n : s ≤ n) {w w₁ : World} (e₁ : w₁ ⊒ w)
    (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
    (c : Desc (ΔL w) (ΔR w)) (β : TyVar (ΔL w₁)) where

  open SealNew d le_s le_n s≤n e₁ Xs Ys c β

  private
    Xs₁ = map (renameVar (ρL e₁)) Xs
    Ys₁ = map (renameVar (ρR e₁)) Ys
    c₁ = renameDesc (ρL e₁) (ρR e₁) c
    c₀ = sdesc Xs Ys c
    Lt = sem (leafBelowS d le_n c₀)

  -- a paired binder whose right converts at β′
  sealNewP : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
      (β′ : TyVar (ΔR w₁))
    → SealI d s w₁ (m-pair {Φ = pair Φ} {X = zero} ↔-here β′) β
        (extPairI (＇ β) (＇ β′)
          (sem (leafBelowS d le_s (sdesc (β ∷ Xs₁) (β′ ∷ Ys₁) c₁)))
          (δt ↑ᴵ e₁))
        (extPairI (repL Xs c) (repR Ys c) Lt δt ↑ᴵ e₁)
  sealNewP β′ = rev , con
    where
    rev : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k ≤ s → ∀ {Vl Vr}
      → leafBelowS d le_s (sdesc (β ∷ Xs₁) (β′ ∷ Ys₁) c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) Vl Vr
      → sealedL (toRenameᵗ (ρL e) β)
          (renameᵗ (toRenameᵗ (ρL e))
            (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c)))
          (sealedR (toRenameᵗ (ρR e) β′)
            (renameᵗ (toRenameᵗ (ρR e))
              (renameᵗ (toRenameᵗ (ρR e₁)) (repR Ys c)))
            (leafRel d (pred k) w′ (transportLeaf (ρL e) (ρR e)
              (transportLeaf (ρL e₁) (ρR e₁) Lt)))) Vl Vr
    rev {w′} e {k} pos le r =
      sealedL-map (varβ e β) (repβ e)
        (sealedR-map (varβR e β′) (repβ′ e)
          (λ q → leafBelowS-down d le_n c₀ (onlyStage-≤ ≺ k) w′ _ _
                   (readT e k q)))
        (sealS→ d le_s Xs₁ Ys₁ c₁ β β′ k w′ (id↪ᵗ ∘↪ ρL e)
          (id↪ᵗ ∘↪ ρR e) r)

    con : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k < s → ∀ {Wl Wr}
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
          (transportLeaf (ρL e₁) (ρR e₁) Lt)) Wl Wr
      → leafBelowS d le_s (sdesc (β ∷ Xs₁) (β′ ∷ Ys₁) c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
          (Wl ↓ seal (toRenameᵗ (ρL e) β)
            (renameᵗ (toRenameᵗ (ρL e))
              (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c))))
          (Wr ↓ seal (toRenameᵗ (ρR e) β′)
            (renameᵗ (toRenameᵗ (ρR e))
              (renameᵗ (toRenameᵗ (ρR e₁)) (repR Ys c))))
    con {w′} e {k} pos lt r =
      sealS← d le_s Xs₁ Ys₁ c₁ β β′ k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
        ((sym (varβ e β) , sym (repβ e)) ,
          (sym (varβR e β′) , sym (repβ′ e)) , writeS e k lt r)

  -- a paired binder whose right does not convert
  sealNewL : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
      {T′ : Ty (ΔR w₁)}
    → UpB d s n
    → SealI d s w₁ (m-left {Φ = pair Φ} {X = zero}) β
        (extPairI (＇ β) T′
          (sem (leafBelowS d le_s (sdesc (β ∷ Xs₁) Ys₁ c₁)))
          (δt ↑ᴵ e₁))
        (extPairI (repL Xs c) (repR Ys c) Lt δt ↑ᴵ e₁)
  sealNewL up = rev , con
    where
    rev : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k ≤ s → ∀ {Vl Vr}
      → leafBelowS d le_s (sdesc (β ∷ Xs₁) Ys₁ c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) Vl Vr
      → sealedL (toRenameᵗ (ρL e) β)
          (renameᵗ (toRenameᵗ (ρL e))
            (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c)))
          (leafRel d (onlyStage d k) w′ (transportLeaf (ρL e) (ρR e)
            (transportLeaf (ρL e₁) (ρR e₁) Lt))) Vl Vr
    rev {w′} e {k} pos le r =
      sealedL-map (varβ e β) (repβ e)
        (λ q → leafBelowS-down d le_n c₀ (onlyStage-≤ d k) w′ _ _
                 (readT e k q))
        (sealSL→ d le_s Xs₁ Ys₁ c₁ β k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) r)

    con : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → onlyBelow d k s
      → ∀ {Wl Vr}
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
          (transportLeaf (ρL e₁) (ρR e₁) Lt)) Wl Vr
      → leafBelowS d le_s (sdesc (β ∷ Xs₁) Ys₁ c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
          (Wl ↓ seal (toRenameᵗ (ρL e) β)
            (renameᵗ (toRenameᵗ (ρL e))
              (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c)))) Vr
    con {w′} e {k} pos lt r =
      sealSL← d le_s Xs₁ Ys₁ c₁ β k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
        ((sym (varβ e β) , sym (repβ e)) ,
          writeUp d le_s le_n e₁ c₀ e k up lt r)

------------------------------------------------------------------------
-- Equations for instantiating a proxy at a new store variable
------------------------------------------------------------------------

module _ {Θ} (T : Ty Θ) where

  private
    ρ₁ = toRenameᵗ (embedᶜˢ (bind T ∷ []))

  -- the shifted term
  shift-term : (V : Term Θ) → renameᵗᵐ (embedᶜˢ (bind T ∷ [])) V ≡ ⇑ᵗᵐ V
  shift-term V = cong (λ σ → renameᵗᵐ σ V) (embed-bind T)

  shift-ty : (C : Ty Θ) → renameᵗ ρ₁ C ≡ ⇑ᵗ C
  shift-ty C = renameᵗ-cong C (embed-var T)

  -- the annotation of the instantiation after the allocation
  annot : (σ : Δ ⇒ˢ Θ) (A : Ty (suc Δ))
    → substᵗ (extsᵗ (λ Z → renameᵗ ρ₁ (σ Z))) A
      ≡ renameᵗ (extᵗ suc) (substᵗ (extsᵗ σ) A)
  annot σ A =
    trans (substᵗ-cong A pw) (sym (renameᵗ-subst (extᵗ suc) (extsᵗ σ) A))
    where
    pw : ∀ Z → extsᵗ (λ Z′ → renameᵗ ρ₁ (σ Z′)) Z
      ≡ renameᵗ (extᵗ suc) (extsᵗ σ Z)
    pw zero = refl
    pw (suc Z) =
      trans (renameᵗ-comp ρ₁ suc (σ Z))
        (trans (renameᵗ-cong (σ Z) (λ X → cong suc (embed-var T X)))
          (sym (renameᵗ-comp suc (extᵗ suc) (σ Z))))

  -- the body opened at the new store variable
  open0 : (σ : Δ ⇒ˢ Θ) (A : Ty (suc Δ))
    → substᵗ ((＇ zero) •ˢ (λ Z → renameᵗ ρ₁ (σ Z))) A
      ≡ substᵗ (extsᵗ σ) A
  open0 σ A = substᵗ-cong A pw
    where
    pw : ∀ Z → ((＇ zero) •ˢ (λ Z′ → renameᵗ ρ₁ (σ Z′))) Z ≡ extsᵗ σ Z
    pw zero = refl
    pw (suc Z) = shift-ty (σ Z)

-- the target of a converted body
tgt-body : ∀ {Θ} (α : TyVar Θ) R (σs σt : Δ ⇒ˢ Θ)
  → (∀ Z → replaceTy α R (σs Z) ≡ σt Z) → (A : Ty (suc Δ))
  → replaceTy (suc α) (⇑ᵗ R) (substᵗ (extsᵗ σs) A) ≡ substᵗ (extsᵗ σt) A
tgt-body α R σs σt eq A =
  trans (replaceTy-subst (suc α) (⇑ᵗ R) (extsᵗ σs) A) (substᵗ-cong A pw)
  where
  pw : ∀ Z → replaceTy (suc α) (⇑ᵗ R) (extsᵗ σs Z) ≡ extsᵗ σt Z
  pw zero = replaceTy-other {X = suc α} (⇑ᵗ R) (λ ())
  pw (suc Z) =
    trans (sym (replaceTy-rename suc suc-inj α R (σs Z)))
      (cong (renameᵗ suc) (eq Z))

-- renaming equal packed conversions
pk-ren↑ : ∀ {Θ Θ′} (ρ : Θ ⇒ʳ Θ′) {A B C D} {c : Conv↑ Θ A B}
    {c′ : Conv↑ Θ C D}
  → ⟪ c ⟫↑ ≡ ⟪ c′ ⟫↑ → ⟪ rename↑ ρ c ⟫↑ ≡ ⟪ rename↑ ρ c′ ⟫↑
pk-ren↑ ρ refl = refl

pk-ren↓ : ∀ {Θ Θ′} (ρ : Θ ⇒ʳ Θ′) {A B C D} {c : Conv↓ Θ A B}
    {c′ : Conv↓ Θ C D}
  → ⟪ c ⟫↓ ≡ ⟪ c′ ⟫↓ → ⟪ rename↓ ρ c ⟫↓ ≡ ⟪ rename↓ ρ c′ ⟫↓
pk-ren↓ ρ refl = refl

pk-〖〗 : ∀ {Θ} {α α′ : TyVar Θ} {R R′ T T′}
  → α ≡ α′ → R ≡ R′ → T ≡ T′ → ⟪ 〖 α , R ↑ T 〗 ⟫↑ ≡ ⟪ 〖 α′ , R′ ↑ T′ 〗 ⟫↑
pk-〖〗 refl refl refl = refl

pk-mc : ∀ {Θ} {α α′ : TyVar Θ} {R R′ T T′}
  → α ≡ α′ → R ≡ R′ → T ≡ T′
  → ⟪ makeConceal α R T ⟫↓ ≡ ⟪ makeConceal α′ R′ T′ ⟫↓
pk-mc refl refl refl = refl

-- one step on each side, the counted one included
anti₁₁ : ∀ d {s} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) {w : World}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΘL ΘR} {Ml : Term (ΔL w)}
    {Ml′ : Term ΘL} {Mr : Term (ΔR w)} {Mr′ : Term ΘR}
    {χL : StoreChange (ΔL w) ΘL} {χR : StoreChange (ΔR w) ΘR}
  → Ml —→[ χL ] Ml′ → Mr —→[ χR ] Mr′
  → (tags : TyVar ΘL → Tag ΘL ΘR)
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ (χL ∷ [])) X)
            ≡ renameTag (embedᶜˢ (χL ∷ [])) (embedᶜˢ (χR ∷ [])) (tag w X))
  → ℰ d s p (world ΘL ΘR tags)
      (δ ↑ᴵ stepExt (χL ∷ []) (χR ∷ []) tags ok) Ml′ Mr′
  → ℰ d (suc s) p w δ Ml Mr
anti₁₁ ≺ p sl sr tags ok r =
  ℰ-anti-≺ p (more sl none) (↠-step sr ↠-refl) tags ok r
anti₁₁ ≻ p sl sr tags ok r =
  ℰ-anti-≻ p (↠-step sl ↠-refl) (more sr none) tags ok r

------------------------------------------------------------------------
-- Conversions renamed into a future, in the main lemma
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {w w′ : World}
    (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (ΔR w)) where

  revRen : ∀ α (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔL w′)) C
    → Q ↑ 〖 toRenameᵗ (ρL e) α
          , repM (CMode-↑ (ρL e) (ρR e) m) (δl (δt ↑ᴵ e))
          ↑ substᵗ (δl (δs ↑ᴵ e)) C 〗
      ≡ Q ↑ rename↑ (toRenameᵗ (ρL e))
            〖 α , repM m (δl δt) ↑ substᵗ (δl δs) C 〗
  revRen α δs δt Q C =
    trans (↑〖〗-≡ refl (repM-↑ (ρL e) (ρR e) m (δl δt)) refl)
      (sym (↑-pk (〖〗-ren (ρL e) α (repM m (δl δt)) (δl δs) C)))

  conRen : ∀ α (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔL w′)) C
    → Q ↓ makeConceal (toRenameᵗ (ρL e) α)
            (repM (CMode-↑ (ρL e) (ρR e) m) (δl (δt ↑ᴵ e)))
            (substᵗ (δl (δs ↑ᴵ e)) C)
      ≡ Q ↓ rename↓ (toRenameᵗ (ρL e))
            (makeConceal α (repM m (δl δt)) (substᵗ (δl δs) C))
  conRen α δs δt Q C =
    trans (↓mc-≡ refl (repM-↑ (ρL e) (ρR e) m (δl δt)) refl)
      (sym (↓-pk (makeConceal-ren (ρL e) α (repM m (δl δt)) (δl δs) C)))

  rcRen : ∀ (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔR w′)) C
    → revM (rconv (CMode-↑ (ρL e) (ρR e) m) (δr (δt ↑ᴵ e)))
        (substᵗ (δr (δs ↑ᴵ e)) C) Q
      ≡ mplug (renameMFrame (ρR e)
          (revFrame (rconv m (δr δt)) (substᵗ (δr δs) C))) Q
  rcRen δs δt Q C =
    trans (cong (λ c → revM c _ Q) (rconv-↑ (ρL e) (ρR e) m (δr δt)))
      (sym (revFrame-ren (ρR e) (rconv m (δr δt)) (δr δs) C Q))

  ccRen : ∀ (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔR w′)) C
    → conM (rconv (CMode-↑ (ρL e) (ρR e) m) (δr (δt ↑ᴵ e)))
        (substᵗ (δr (δs ↑ᴵ e)) C) Q
      ≡ mplug (renameMFrame (ρR e)
          (conFrame (rconv m (δr δt)) (substᵗ (δr δs) C))) Q
  ccRen δs δt Q C =
    trans (cong (λ c → conM c _ Q) (rconv-↑ (ρL e) (ρR e) m (δr δt)))
      (sym (conFrame-ren (ρR e) (rconv m (δr δt)) (δr δs) C Q))

------------------------------------------------------------------------
-- `∀⊑∀`, the reveal, when the right converts too
------------------------------------------------------------------------

module PairRev (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B)
    (rev : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (rconv m (δr δt)) (substᵗ (δr δs) B) Vr))
    where

  pairRev : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt}
      (h : ConvI d N both w m α δs δt) → n ≤ N
    → ∀ {α′ R′} → rconv m (δr δt) ≡ just (α′ , R′)
    → ∀ {Vl Vr} → Value Vl → Value Vr → allPair d n p w δs Vl Vr
    → ∀ Xs Ys c
    → ℰ d n p w (extPairI (repL Xs c) (repR Ys c)
          (sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))) δt)
        ((Vl ↑ `∀↑ 〖 suc α , ⇑ᵗ (repM m (δl δt))
                    ↑ substᵗ (extsᵗ (δl δs)) A 〗)
           ⦂∀ substᵗ (extsᵗ (δl δt)) A [ repL Xs c ])
        ((Vr ↑ `∀↑ 〖 suc α′ , ⇑ᵗ R′ ↑ substᵗ (extsᵗ (δr δs)) B 〗)
           ⦂∀ substᵗ (extsᵗ (δr δt)) B [ repR Ys c ])
  pairRev {zero} w h le eq vl vr r Xs Ys c = ℰ-zero d p w
  pairRev {suc s} w {X} {m} {α} {δs} {δt} h le {α′} {R′} eq {Vl} {Vr}
      vl vr r Xs Ys c =
    anti₁₁ d p stepL stepR (tagsLR w) (okBindLR w Tl Tr) inner
    where
    Tl = repL Xs c
    Tr = repR Ys c
    R = repM m (δl δt)
    cL = 〖 suc α , ⇑ᵗ R ↑ substᵗ (extsᵗ (δl δs)) A 〗
    cR = 〖 suc α′ , ⇑ᵗ R′ ↑ substᵗ (extsᵗ (δr δs)) B 〗
    BtL = substᵗ (extsᵗ (δl δt)) A
    BtR = substᵗ (extsᵗ (δr δt)) B

    tyR′ : ∀ Y → replaceTy α′ R′ (δr δs Y) ≡ δr δt Y
    tyR′ = subst (λ rc → ∀ Y → replaceRC rc (δr δs Y) ≡ δr δt Y) eq (tyR h)

    stepL = revInst cL vl (tgt-body α R (δl δs) (δl δt) (tyL h) A)
    stepR = revInst cR vr (tgt-body α′ R′ (δr δs) (δr δt) tyR′ B)

    e₁ = stepExt (bind Tl ∷ []) (bind Tr ∷ []) (tagsLR w) (okBindLR w Tl Tr)
    w₁ = world (suc (ΔL w)) (suc (ΔR w)) (tagsLR w)
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    c″ = sdesc (zero ∷ Xs₁) (zero ∷ Ys₁) c₁
    le_s : s ≤′ suc s
    le_s = ≤′-step ≤′-refl
    s≤N : s ≤ N
    s≤N = ≤-trans (n≤1+n s) le
    Ls = sem (leafBelowS d le_s c″)
    Lt = sem (leafBelowS d (≤′-refl {suc s}) (sdesc Xs Ys c))
    gLs = leafBelowS-good d le_s c″
    δsβ = extPairI (＇ zero) (＇ zero) Ls (δs ↑ᴵ e₁)
    δtβ = extPairI (＇ zero) (＇ zero) Ls (δt ↑ᴵ e₁)
    δtg = extPairI Tl Tr Lt δt ↑ᴵ e₁
    m₁ = CMode-pair (CMode-↑ ρL₁ ρR₁ m)
    α₁ = toRenameᵗ ρL₁ α

    rc↑ : rconv (CMode-↑ ρL₁ ρR₁ m) (δr (δt ↑ᴵ e₁))
      ≡ just (toRenameᵗ ρR₁ α′ , renameᵗ (toRenameᵗ ρR₁) R′)
    rc↑ = trans (rconv-↑ ρL₁ ρR₁ m (δr δt)) (cong (renRConv ρR₁) eq)

    hα : ConvI d N both w₁ m₁ α₁ δsβ δtβ
    hα = ConvI-extPair {β = zero} {l = Ls} gLs
      (λ e′ → new-bind Tl α (sym e′))
      (subst (λ rc → replaceRC rc (＇ zero) ≡ ＇ zero) (sym rc↑)
        (replaceTy-other (renameᵗ (toRenameᵗ ρR₁) R′)
          (λ e′ → new-bind Tr α′ (sym e′))))
      (subst (λ rc → ConvLeafP d N w₁ R₁ rc α₁ Ls Ls (＇ zero) (＇ zero))
        (sym rc↑)
        (storeConvP gLs R₁
          (just (toRenameᵗ ρR₁ α′ , renameᵗ (toRenameᵗ ρR₁) R′))
          (λ e′ → new-bind Tl α (sym e′))
          (λ e′ → new-bind Tr α′ (sym e′))))
      (storeFreshP {N = N} gLs {γ = zero} {γ′ = zero} {rk = both})
      (ConvI-↑ e₁ h)
      where
      R₁ = repM (CMode-↑ ρL₁ ρR₁ m) (δl (δt ↑ᴵ e₁))

    hβ : ConvI d s both w₁ (m-pair {Φ = pair Φ} ↔-here zero) zero δtβ δtg
    hβ = ConvI-newP e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
      {Tr = Tr} (new-bind Tr) s≤N (freshT h) gLs
      (leafBelowS-good d (≤′-refl {suc s}) (sdesc Xs Ys c))
      (proj₁ (oracle h) (≤′-refl {suc s}) le (sdesc Xs Ys c))
      (SealNewP.sealNewP d le_s (≤′-refl {suc s}) (n≤1+n s) e₁ Xs Ys c zero
        {Φ = Φ} {δt = δt} zero)

    clause : ℰ d s p w₁ δsβ
      (⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
      (⇑ᵗᵐ Vr ⦂∀ (bind Tr ▷ᵇ substᵗ (extsᵗ (δr δs)) B) [ ＇ zero ])
    clause =
      ℰᵍ-≡
        (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tl Vl)
          (annot Tl (δl δs) A))
        (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tr Vr)
          (annot Tr (δr δs) B))
        (ℰᵍ-map d s w₁
          (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
          (r e₁ le_s c″))

    R≡ : repM m₁ (δl δtβ) ≡ ⇑ᵗ R
    R≡ = trans (repM-pair (CMode-↑ ρL₁ ρR₁ m) (δl (δt ↑ᴵ e₁)) (＇ zero))
      (trans (repM-↑ ρL₁ ρR₁ m (δl δt)) (shift-ty Tl R))

    rc₁≡ : rconv m₁ (δr δtβ) ≡ just (suc α′ , ⇑ᵗ R′)
    rc₁≡ = trans (rconv-pair (CMode-↑ ρL₁ ρR₁ m) (δr (δt ↑ᴵ e₁)) (＇ zero))
      (trans rc↑
        (cong₂ (λ a b → just (a , b)) (embed-var Tr α′) (shift-ty Tr R′)))

    K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₂ (δsβ ↑ᴵ e₂) Ql Qr
      → ℰ d k p w₂ (δtβ ↑ᴵ e₂)
          (mplug (renameMFrame (ρL e₂) (just (reveal cL))) Ql)
          (mplug (renameMFrame (ρR e₂) (just (reveal cR))) Qr)
    K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans (revRen e₂ m₁ α₁ δsβ δtβ Ql A)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₂))
            (pk-〖〗 (embed-var Tl α) R≡ (open0 Tl (δl δs) A)))))
        (trans (rcRen e₂ m₁ δsβ δtβ Qr B)
          (trans (cong (λ rc → mplug (renameMFrame (ρR e₂)
                          (revFrame rc (substᵗ (δr δsβ) B))) Qr) rc₁≡)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρR e₂))
              (pk-〖〗 refl refl (open0 Tr (δr δs) B))))))
        (rev (ConvI-↑ e₂ hα) (≤-trans k≤s s≤N) ql qr q)

    K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₃ (δtβ ↑ᴵ e₃) Ql Qr
      → ℰ d k p w₃ (δtg ↑ᴵ e₃)
          (mplug (renameMFrame (ρL e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗))) Ql)
          (mplug (renameMFrame (ρR e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BtR 〗))) Qr)
    K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans (revRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) zero δtβ δtg Ql A)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
            (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δt) A)))))
        (trans (rcRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) δtβ δtg Qr B)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρR e₃))
            (pk-〖〗 refl (shift-ty Tr Tr) (open0 Tr (δr δt) B)))))
        (rev (ConvI-↑ e₃ hβ) k≤s ql qr q)

    inner : ℰ d s p w₁ δtg
      ((⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
         ↑ cL ↑ 〖 zero , ⇑ᵗ Tl ↑ BtL 〗)
      ((⇑ᵗᵐ Vr ⦂∀ (bind Tr ▷ᵇ substᵗ (extsᵗ (δr δs)) B) [ ＇ zero ])
         ↑ cR ↑ 〖 zero , ⇑ᵗ Tr ↑ BtR 〗)
    inner =
      ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δtg}
        (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗))
        (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BtR 〗))
        (ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δtβ}
          (just (reveal cL)) (just (reveal cR)) clause K₁)
        K₂

------------------------------------------------------------------------
-- `∀⊑∀`, the reveal, when the right does not convert
------------------------------------------------------------------------

-- one left store step, counted in `≺` only
antiL₁ : ∀ d {n N} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) {w : World}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΘL} {Ml : Term (ΔL w)}
    {Ml′ : Term ΘL} {Mr : Term (ΔR w)} {χL : StoreChange (ΔL w) ΘL}
  → n ≤ N → Ml —→[ χL ] Ml′
  → (tags : TyVar ΘL → Tag ΘL (ΔR w))
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ (χL ∷ [])) X)
            ≡ renameTag (embedᶜˢ (χL ∷ [])) (embedᶜˢ ([] {ΔR w})) (tag w X))
  → (∀ {s} → s ≤′ n → s ≤ N → UpB d s n
       → ℰ d s p (world ΘL (ΔR w) tags)
           (δ ↑ᴵ stepExt (χL ∷ []) [] tags ok) Ml′ Mr)
  → ℰ d n p w δ Ml Mr
antiL₁ ≺ {zero} p le sl tags ok k = ℰ-zero ≺ p _
antiL₁ ≺ {suc s} p le sl tags ok k =
  ℰ-anti-≺ p (more sl none) ↠-refl tags ok
    (k (≤′-step ≤′-refl) (≤-trans (n≤1+n s) le) tt)
antiL₁ ≻ {n} p le sl tags ok k =
  ℰ-anti-≻ p (↠-step sl ↠-refl) none tags ok (k ≤′-refl le ≤-refl)

module PairRevL (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B)
    (rev : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (rconv m (δr δt)) (substᵗ (δr δs) B) Vr))
    where

  pairRevL : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt} {rk}
      (h : ConvI d N rk w m α δs δt) → n ≤ N → rconv m (δr δt) ≡ nothing
    → ∀ {Vl Vr} → Value Vl → Value Vr → allPair d n p w δs Vl Vr
    → ∀ Xs Ys c
    → ℰ d n p w (extPairI (repL Xs c) (repR Ys c)
          (sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))) δt)
        ((Vl ↑ `∀↑ 〖 suc α , ⇑ᵗ (repM m (δl δt))
                    ↑ substᵗ (extsᵗ (δl δs)) A 〗)
           ⦂∀ substᵗ (extsᵗ (δl δt)) A [ repL Xs c ])
        (Vr ⦂∀ substᵗ (extsᵗ (δr δt)) B [ repR Ys c ])
  pairRevL {n} w {X} {m} {α} {δs} {δt} {rk} h le eqn {Vl} {Vr} vl vr r
      Xs Ys c =
    antiL₁ d p le stepL (tagsL w) (okBindL w Tl) inner
    where
    Tl = repL Xs c
    Tr = repR Ys c
    R = repM m (δl δt)
    cL = 〖 suc α , ⇑ᵗ R ↑ substᵗ (extsᵗ (δl δs)) A 〗
    BtL = substᵗ (extsᵗ (δl δt)) A
    BtR = substᵗ (extsᵗ (δr δt)) B
    stepL = revInst cL vl (tgt-body α R (δl δs) (δl δt) (tyL h) A)

    e₁ = stepExt (bind Tl ∷ []) [] (tagsL w) (okBindL w Tl)
    w₁ = world (suc (ΔL w)) (ΔR w) (tagsL w)
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    T′ = repR Ys₁ c₁
    Lt = sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))
    m₁ = CMode-pair (CMode-↑ ρL₁ ρR₁ m)
    α₁ = toRenameᵗ ρL₁ α

    -- the right side is not converted, so δs and δt agree on it
    sameR : ∀ Y → δr δs Y ≡ δr δt Y
    sameR Y = subst (λ rc → replaceRC rc (δr δs Y) ≡ δr δt Y) eqn (tyR h Y)

    rc↑ : rconv (CMode-↑ ρL₁ ρR₁ m) (δr (δt ↑ᴵ e₁)) ≡ nothing
    rc↑ = trans (rconv-↑ ρL₁ ρR₁ m (δr δt)) (cong (renRConv ρR₁) eqn)

    rc₁≡ : rconv m₁ (δr (extPairI (＇ zero) T′ (sem ⊤Ω) (δt ↑ᴵ e₁)))
      ≡ nothing
    rc₁≡ = trans (rconv-pair (CMode-↑ ρL₁ ρR₁ m) (δr (δt ↑ᴵ e₁)) T′) rc↑

    inner : ∀ {s} → s ≤′ n → s ≤ N → UpB d s n
      → ℰ d s p w₁ (extPairI Tl Tr Lt δt ↑ᴵ e₁)
          ((⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
             ↑ cL ↑ 〖 zero , ⇑ᵗ Tl ↑ BtL 〗)
          (Vr ⦂∀ BtR [ Tr ])
    inner {s} le_s s≤N up =
      ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δtg}
        (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗)) nothing
        (ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δtβ}
          (just (reveal cL)) nothing clause K₁)
        K₂
      where
      c″ = sdesc (zero ∷ Xs₁) Ys₁ c₁
      Ls = sem (leafBelowS d le_s c″)
      gLs = leafBelowS-good d le_s c″
      δsβ = extPairI (＇ zero) T′ Ls (δs ↑ᴵ e₁)
      δtβ = extPairI (＇ zero) T′ Ls (δt ↑ᴵ e₁)
      δtg = extPairI Tl Tr Lt δt ↑ᴵ e₁

      hα : ConvI d N left w₁ m₁ α₁ δsβ δtβ
      hα = ConvI-extPair {β = zero} {l = Ls} gLs
        (λ e′ → new-bind Tl α (sym e′))
        (subst (λ rc → replaceRC rc T′ ≡ T′) (sym rc↑) refl)
        (subst (λ rc → ConvLeafP d N w₁
                         (repM (CMode-↑ ρL₁ ρR₁ m) (δl (δt ↑ᴵ e₁))) rc α₁
                         Ls Ls (＇ zero) T′)
          (sym rc↑)
          (storeConvPN {N = N} gLs {γ = zero} {T′ = T′}
            (repM (CMode-↑ ρL₁ ρR₁ m) (δl (δt ↑ᴵ e₁)))
            (λ e′ → new-bind Tl α (sym e′))))
        (storeFreshPL {N = N} gLs {γ = zero} {T′ = T′})
        (ConvI-left rc↑ (ConvI-↑ e₁ h))

      hβ : ConvI d s left w₁ (m-left {Φ = pair Φ} {X = zero}) zero δtβ δtg
      hβ = ConvI-newL e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
        {Tr = Tr} {T′ = T′} (repR-rename ρL₁ ρR₁ Ys c) s≤N (freshT h) gLs
        (leafBelowS-good d (≤′-refl {n}) (sdesc Xs Ys c))
        (proj₁ (oracle h) (≤′-refl {n}) le (sdesc Xs Ys c))
        (SealNewP.sealNewL d le_s (≤′-refl {n}) (≤′⇒≤ le_s) e₁ Xs Ys c zero
          {Φ = Φ} {δt = δt} {T′ = T′} up)

      clause : ℰ d s p w₁ δsβ
        (⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
        (Vr ⦂∀ BtR [ Tr ])
      clause =
        ℰᵍ-≡
          (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tl Vl)
            (annot Tl (δl δs) A))
          (cong₃′ (renameᵗᵐ-id Vr)
            (substᵗ-cong B (exts-cong (λ Y →
              trans (renameTy-id (δr δs Y)) (sameR Y))))
            (trans (repR-rename ρL₁ ρR₁ Ys c) (renameTy-id Tr)))
          (ℰᵍ-map d s w₁
            (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
            (r e₁ le_s c″))
        where
        cong₃′ : ∀ {M M′ : Term (ΔR w)} {C C′ T T″}
          → M ≡ M′ → C ≡ C′ → T ≡ T″ → M ⦂∀ C [ T ] ≡ M′ ⦂∀ C′ [ T″ ]
        cong₃′ refl refl refl = refl

      R≡ : repM m₁ (δl δtβ) ≡ ⇑ᵗ R
      R≡ = trans (repM-pair (CMode-↑ ρL₁ ρR₁ m) (δl (δt ↑ᴵ e₁)) (＇ zero))
        (trans (repM-↑ ρL₁ ρR₁ m (δl δt)) (shift-ty Tl R))

      K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₂ (δsβ ↑ᴵ e₂) Ql Qr
        → ℰ d k p w₂ (δtβ ↑ᴵ e₂)
            (mplug (renameMFrame (ρL e₂) (just (reveal cL))) Ql) Qr
      K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₂ m₁ α₁ δsβ δtβ Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₂))
              (pk-〖〗 (embed-var Tl α) R≡ (open0 Tl (δl δs) A)))))
          (trans (rcRen e₂ m₁ δsβ δtβ Qr B)
            (cong (λ rc → mplug (renameMFrame (ρR e₂)
                            (revFrame rc (substᵗ (δr δsβ) B))) Qr) rc₁≡))
          (rev (ConvI-↑ e₂ hα) (≤-trans k≤s s≤N) ql qr q)

      K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₃ (δtβ ↑ᴵ e₃) Ql Qr
        → ℰ d k p w₃ (δtg ↑ᴵ e₃)
            (mplug (renameMFrame (ρL e₃)
              (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗))) Ql) Qr
      K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₃ (m-left {Φ = pair Φ} {X = zero}) zero δtβ δtg Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
              (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δt) A)))))
          refl
          (rev (ConvI-↑ e₃ hβ) k≤s ql qr q)

------------------------------------------------------------------------
-- `∀⊑∀`, the conceal, when the right converts too
------------------------------------------------------------------------

ConB-just : ∀ {Θ} d {c : TyVar Θ × Ty Θ} {k N} → k < N → ConB d (just c) k N
ConB-just ≺ lt = lt
ConB-just ≻ lt = lt

module PairCon (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B)
    (rev : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (rconv m (δr δt)) (substᵗ (δr δs) B) Vr))
    (con : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k}
       → ConB d (rconv m (δr δt)) k N′
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (rconv m (δr δt)) (substᵗ (δr δs) B) Wr))
    where

  pairCon : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt}
      (h : ConvI d N both w m α δs δt) → n ≤ N
    → ∀ {α′ R′} → rconv m (δr δt) ≡ just (α′ , R′)
    → ∀ {Wl Wr} → Value Wl → Value Wr → allPair d n p w δt Wl Wr
    → ∀ Xs Ys c
    → ℰ d n p w (extPairI (repL Xs c) (repR Ys c)
          (sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))) δs)
        ((Wl ↓ `∀↓ makeConceal (suc α) (⇑ᵗ (repM m (δl δt)))
                    (substᵗ (extsᵗ (δl δs)) A))
           ⦂∀ substᵗ (extsᵗ (δl δs)) A [ repL Xs c ])
        ((Wr ↓ `∀↓ makeConceal (suc α′) (⇑ᵗ R′)
                    (substᵗ (extsᵗ (δr δs)) B))
           ⦂∀ substᵗ (extsᵗ (δr δs)) B [ repR Ys c ])
  pairCon {zero} w h le eq wl wr r Xs Ys c = ℰ-zero d p w
  pairCon {suc s} w {X} {m} {α} {δs} {δt} h le {α′} {R′} eq {Wl} {Wr}
      wl wr r Xs Ys c =
    anti₁₁ d p stepL stepR (tagsLR w) (okBindLR w Tl Tr) inner
    where
    Tl = repL Xs c
    Tr = repR Ys c
    R = repM m (δl δt)
    BsL = substᵗ (extsᵗ (δl δs)) A
    BsR = substᵗ (extsᵗ (δr δs)) B
    cL = makeConceal (suc α) (⇑ᵗ R) BsL
    cR = makeConceal (suc α′) (⇑ᵗ R′) BsR

    tyR′ : ∀ Y → replaceTy α′ R′ (δr δs Y) ≡ δr δt Y
    tyR′ = subst (λ rc → ∀ Y → replaceRC rc (δr δs Y) ≡ δr δt Y) eq (tyR h)

    tgtL : replaceTy (suc α) (⇑ᵗ R) BsL ≡ substᵗ (extsᵗ (δl δt)) A
    tgtL = tgt-body α R (δl δs) (δl δt) (tyL h) A

    tgtR : replaceTy (suc α′) (⇑ᵗ R′) BsR ≡ substᵗ (extsᵗ (δr δt)) B
    tgtR = tgt-body α′ R′ (δr δs) (δr δt) tyR′ B

    stepL = conInst {T = Tl} cL wl refl
    stepR = conInst {T = Tr} cR wr refl

    e₁ = stepExt (bind Tl ∷ []) (bind Tr ∷ []) (tagsLR w) (okBindLR w Tl Tr)
    w₁ = world (suc (ΔL w)) (suc (ΔR w)) (tagsLR w)
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    c″ = sdesc (zero ∷ Xs₁) (zero ∷ Ys₁) c₁
    le_s : s ≤′ suc s
    le_s = ≤′-step ≤′-refl
    s≤N : s ≤ N
    s≤N = ≤-trans (n≤1+n s) le
    Ls = sem (leafBelowS d le_s c″)
    Lt = sem (leafBelowS d (≤′-refl {suc s}) (sdesc Xs Ys c))
    gLs = leafBelowS-good d le_s c″
    δsβ = extPairI (＇ zero) (＇ zero) Ls (δs ↑ᴵ e₁)
    δtβ = extPairI (＇ zero) (＇ zero) Ls (δt ↑ᴵ e₁)
    δsg = extPairI Tl Tr Lt δs ↑ᴵ e₁
    m₁ = CMode-pair (CMode-↑ ρL₁ ρR₁ m)
    α₁ = toRenameᵗ ρL₁ α

    rc↑ : rconv (CMode-↑ ρL₁ ρR₁ m) (δr (δt ↑ᴵ e₁))
      ≡ just (toRenameᵗ ρR₁ α′ , renameᵗ (toRenameᵗ ρR₁) R′)
    rc↑ = trans (rconv-↑ ρL₁ ρR₁ m (δr δt)) (cong (renRConv ρR₁) eq)

    hα : ConvI d N both w₁ m₁ α₁ δsβ δtβ
    hα = ConvI-extPair {β = zero} {l = Ls} gLs
      (λ e′ → new-bind Tl α (sym e′))
      (subst (λ rc → replaceRC rc (＇ zero) ≡ ＇ zero) (sym rc↑)
        (replaceTy-other (renameᵗ (toRenameᵗ ρR₁) R′)
          (λ e′ → new-bind Tr α′ (sym e′))))
      (subst (λ rc → ConvLeafP d N w₁ R₁ rc α₁ Ls Ls (＇ zero) (＇ zero))
        (sym rc↑)
        (storeConvP gLs R₁
          (just (toRenameᵗ ρR₁ α′ , renameᵗ (toRenameᵗ ρR₁) R′))
          (λ e′ → new-bind Tl α (sym e′))
          (λ e′ → new-bind Tr α′ (sym e′))))
      (storeFreshP {N = N} gLs {γ = zero} {γ′ = zero} {rk = both})
      (ConvI-↑ e₁ h)
      where
      R₁ = repM (CMode-↑ ρL₁ ρR₁ m) (δl (δt ↑ᴵ e₁))

    hβ : ConvI d s both w₁ (m-pair {Φ = pair Φ} ↔-here zero) zero δsβ δsg
    hβ = ConvI-newP e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
      {Tr = Tr} (new-bind Tr) s≤N (freshS h) gLs
      (leafBelowS-good d (≤′-refl {suc s}) (sdesc Xs Ys c))
      (proj₁ (oracle h) (≤′-refl {suc s}) le (sdesc Xs Ys c))
      (SealNewP.sealNewP d le_s (≤′-refl {suc s}) (n≤1+n s) e₁ Xs Ys c zero
        {Φ = Φ} {δt = δs} zero)

    clause : ℰ d s p w₁ δtβ
      (⇑ᵗᵐ Wl ⦂∀ (bind Tl ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL) [ ＇ zero ])
      (⇑ᵗᵐ Wr ⦂∀ (bind Tr ▷ᵇ replaceTy (suc α′) (⇑ᵗ R′) BsR) [ ＇ zero ])
    clause =
      ℰᵍ-≡
        (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tl Wl)
          (trans (annot Tl (δl δt) A)
            (cong (renameᵗ (extᵗ suc)) (sym tgtL))))
        (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tr Wr)
          (trans (annot Tr (δr δt) B)
            (cong (renameᵗ (extᵗ suc)) (sym tgtR))))
        (ℰᵍ-map d s w₁
          (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
          (r e₁ le_s c″))

    R≡ : repM m₁ (δl δtβ) ≡ ⇑ᵗ R
    R≡ = trans (repM-pair (CMode-↑ ρL₁ ρR₁ m) (δl (δt ↑ᴵ e₁)) (＇ zero))
      (trans (repM-↑ ρL₁ ρR₁ m (δl δt)) (shift-ty Tl R))

    rc₁≡ : rconv m₁ (δr δtβ) ≡ just (suc α′ , ⇑ᵗ R′)
    rc₁≡ = trans (rconv-pair (CMode-↑ ρL₁ ρR₁ m) (δr (δt ↑ᴵ e₁)) (＇ zero))
      (trans rc↑
        (cong₂ (λ a b → just (a , b)) (embed-var Tr α′) (shift-ty Tr R′)))

    K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₂ (δtβ ↑ᴵ e₂) Ql Qr
      → ℰ d k p w₂ (δsβ ↑ᴵ e₂)
          (mplug (renameMFrame (ρL e₂) (just (conceal cL))) Ql)
          (mplug (renameMFrame (ρR e₂) (just (conceal cR))) Qr)
    K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans (conRen e₂ m₁ α₁ δsβ δtβ Ql A)
          (↓-pk (pk-ren↓ (toRenameᵗ (ρL e₂))
            (pk-mc (embed-var Tl α) R≡ (open0 Tl (δl δs) A)))))
        (trans (ccRen e₂ m₁ δsβ δtβ Qr B)
          (trans (cong (λ rc → mplug (renameMFrame (ρR e₂)
                          (conFrame rc (substᵗ (δr δsβ) B))) Qr) rc₁≡)
            (↓-pk (pk-ren↓ (toRenameᵗ (ρR e₂))
              (pk-mc refl refl (open0 Tr (δr δs) B))))))
        (con (ConvI-↑ e₂ hα) cb ql qr q)
      where
      cb : ConB d (rconv (CMode-↑ (ρL e₂) (ρR e₂) m₁) (δr (δtβ ↑ᴵ e₂))) k N
      cb = subst (λ rc → ConB d rc k N)
        (sym (trans (rconv-↑ (ρL e₂) (ρR e₂) m₁ (δr δtβ))
          (cong (renRConv (ρR e₂)) rc₁≡)))
        (ConB-just d (≤-trans (s≤s k≤s) le))

    K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₃ (δsβ ↑ᴵ e₃) Ql Qr
      → ℰ d k p w₃ (δsg ↑ᴵ e₃)
          (mplug (renameMFrame (ρL e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BsL 〗))) Ql)
          (mplug (renameMFrame (ρR e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BsR 〗))) Qr)
    K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans (revRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) zero δsβ δsg Ql A)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
            (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δs) A)))))
        (trans (rcRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) δsβ δsg Qr B)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρR e₃))
            (pk-〖〗 refl (shift-ty Tr Tr) (open0 Tr (δr δs) B)))))
        (rev (ConvI-↑ e₃ hβ) k≤s ql qr q)

    inner : ℰ d s p w₁ δsg
      ((⇑ᵗᵐ Wl ⦂∀ (bind Tl ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL) [ ＇ zero ])
         ↓ cL ↑ 〖 zero , ⇑ᵗ Tl ↑ BsL 〗)
      ((⇑ᵗᵐ Wr ⦂∀ (bind Tr ▷ᵇ replaceTy (suc α′) (⇑ᵗ R′) BsR) [ ＇ zero ])
         ↓ cR ↑ 〖 zero , ⇑ᵗ Tr ↑ BsR 〗)
    inner =
      ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δsg}
        (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BsL 〗))
        (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BsR 〗))
        (ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δsβ}
          (just (conceal cL)) (just (conceal cR)) clause K₁)
        K₂
