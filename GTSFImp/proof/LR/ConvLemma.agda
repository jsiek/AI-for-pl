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
--   * The right side (Section 7, "Design (W)"): its conversions, terms
--     and the types it runs at are in the world's right store; the
--     interpretations' right types are in the scope, and the hypotheses
--     carry store types `σs`, `σt` for them.  Only the right type at
--     hand needs store preimages (`PreB`), and only where the right
--     converts; where it does not, the two interpretations agree on it
--     (`PreM`).  An interpretation's other right types may name reserved
--     scope variables.  A right allocation takes its step in the store
--     (`stᴬ`, `worldLR`); the new store variable is new for the older
--     store variables.
--   * Typing: a function clause's right arguments are typed, so a
--     converted function converts its typed argument back
--     (`revTyped`, `conTyped`).  This needs the right store to bind
--     the right's converted variable to its representation (`RCΣ`, the
--     field `rcΣ`, and a hypothesis of `FreshP`).
--   * Two lemmas, each with a reveal and a conceal half, by induction on
--     the precision derivation: at derivations into `★` the right is
--     not converted; at the others it converts as the mode says.
--   * The left-only clause's cases (`OnlyRev`, `OnlyCon`) take a slack
--     g: the clause's stage may exceed the bound by g, and its new
--     variable's leaf is bounded by the stage minus g (`OnlyCl`).  g = 0
--     is `allOnly`; g = 1 is the guarded clause `allOnlyG`, whose body
--     at stage k + 1 reads its leaves at stage k only.

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; s≤s; z≤n;
  _≤′_; ≤′-refl; ≤′-step; _≤?_; _+_; _∸_)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤⇒≤′; ≤′⇒≤; ≤-trans;
  ≤-<-trans; <⇒≤; m∸n≤m; ∸-monoˡ-≤)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ; wk↪ᵗ)
  renaming (keep to keepᵗ)
open import proof.DGG.CenterRename using (toRenameᵗ-∘; _∘↪_)
open import proof.TermRename using (renameᵗᵐ-id)
open import proof.TypeInTermSubst using (toRename-id-eq; toRename-wk-eq;
  renameᵗᵐ-preserves-Value; renameᵗ-wk-eq)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective;
  renameᵗ-injective)
open import Conversion
open import TyStore using () renaming (_∋_⦂_ to _∋Σ_⦂_)
open import proof.TypeSafety.Preservation using (structural-reveal-typing;
  structural-conceal-typing)
open import CastTerms using (Term; `_; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_;
  _⟨_⟩; _↑_; _↓_; blame; Value; RevealValue; ConcealValue; renameᵗᵐ; ⇑ᵗᵐ)
import CastTerms as CT
open import Reduction using (_—→_; id-reveal; id-conceal; conceal-reveal;
  β-reveal-⇒; β-conceal-⇒; β-reveal-∀; β-conceal-∀; _—→[_]_; bind; keep;
  StoreChange; StoreChanges; applyBody; []; _∷_; ↠-refl; ↠-step;
  applyStores)
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
open import proof.LR.SubstLemma using (substᵗ-∘; ℰᵍ-zero; _⇔_; iff; to;
  from; 𝒱-XY; 𝒱-X★)
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

-- The conceal's bound: strict when the counted side converts (`ConB`),
-- because the converted variable's seal hypothesis is read below the
-- bound; in mode none no variable is converted, and the bound is not
-- strict.
isNone : ∀ {Φ : Corr Δ Δ′} {X} → CMode Φ X ΘL ΘR → Bool
isNone (m-pair x α′) = false
isNone m-left = false
isNone (m-dead x) = false
isNone (m-none R rc) = true

ConMb : ∀ {Θ} → Dir → Bool → RConv Θ → ℕ → ℕ → Set
ConMb d false rc k N = ConB d rc k N
ConMb d true rc k N = k ≤ N

ConM : ∀ {Φ : Corr Δ Δ′} {X} → Dir → CMode Φ X ΘL ΘR → RConv ΘR → ℕ → ℕ
  → Set
ConM d m rc k N = ConMb d (isNone m) rc k N

ConB-lt : ∀ {Θ} d (rc : RConv Θ) {k N} → k < N → ConB d rc k N
ConB-lt ≺ rc lt = lt
ConB-lt ≻ nothing lt = <⇒≤ lt
ConB-lt ≻ (just c) lt = lt

module _ {Θ} (d : Dir) where

  ConMb-≤ : ∀ b (rc : RConv Θ) {k N} → ConMb d b rc k N → k ≤ N
  ConMb-≤ false rc cb = ConB-≤ d rc cb
  ConMb-≤ true rc cb = cb

  ConMb-down : ∀ b (rc : RConv Θ) {k n N} → k ≤ n → ConMb d b rc n N
    → ConMb d b rc k N
  ConMb-down false rc le cb = ConB-down d rc le cb
  ConMb-down true rc le cb = ≤-trans le cb

  ConMb-lt : ∀ b (rc : RConv Θ) {k N} → k < N → ConMb d b rc k N
  ConMb-lt false rc lt = ConB-lt d rc lt
  ConMb-lt true rc lt = <⇒≤ lt

  ConB→ConMb : ∀ b (rc : RConv Θ) {k N} → ConB d rc k N
    → ConMb d b rc k N
  ConB→ConMb false rc cb = cb
  ConB→ConMb true rc cb = ConB-≤ d rc cb

-- in `≺` the bound does not depend on the right side
ConMb-≺ : ∀ {Θ Θ′} b (rc : RConv Θ) (rc′ : RConv Θ′) {k N}
  → ConMb ≺ b rc k N → ConMb ≺ b rc′ k N
ConMb-≺ false rc rc′ cb = cb
ConMb-≺ true rc rc′ cb = cb

-- one stage down, any right side
ConMb-pred : ∀ {Θ Θ′} d b (rc : RConv Θ) (rc′ : RConv Θ′) {k N}
  → ConMb d b rc (suc k) N → ConMb d b rc′ k N
ConMb-pred d true rc rc′ cb = ≤-trans (n≤1+n _) cb
ConMb-pred ≺ false rc rc′ cb = ≤-<-trans (n≤1+n _) cb
ConMb-pred ≻ false nothing rc′ cb = ConB-lt ≻ rc′ cb
ConMb-pred ≻ false (just c) rc′ cb =
  ConB-lt ≻ rc′ (≤-<-trans (n≤1+n _) cb)

-- moving a conceal's bound to another right side
ConMb-ren : ∀ {Θ Θ′} d b (ρ : Θ ↪ᵗ Θ′) (rc : RConv Θ) {k N}
  → ConMb d b rc k N → ConMb d b (renRConv ρ rc) k N
ConMb-ren d false ρ rc cb = ConB-ren d ρ rc cb
ConMb-ren d true ρ rc cb = cb

ConMb-cast : ∀ {Θ Θ′} d b {k N} → ConMb {Θ} d b nothing k N
  → ConMb {Θ′} d b nothing k N
ConMb-cast ≺ false cb = cb
ConMb-cast ≻ false cb = cb
ConMb-cast d true cb = cb

module _ {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  isNone-↑ : ∀ {ΘL′ ΘR′} (ρL : ΘL ↪ᵗ ΘL′) (ρR : ΘR ↪ᵗ ΘR′)
      (m : CMode Φ X ΘL ΘR) → isNone (CMode-↑ ρL ρR m) ≡ isNone m
  isNone-↑ ρL ρR (m-pair x α′) = refl
  isNone-↑ ρL ρR m-left = refl
  isNone-↑ ρL ρR (m-dead x) = refl
  isNone-↑ ρL ρR (m-none R rc) = refl

  isNone-pair : (m : CMode Φ X ΘL ΘR) → isNone (CMode-pair m) ≡ isNone m
  isNone-pair (m-pair x α′) = refl
  isNone-pair m-left = refl
  isNone-pair (m-dead x) = refl
  isNone-pair (m-none R rc) = refl

  isNone-only : (m : CMode Φ X ΘL ΘR) → isNone (CMode-only m) ≡ isNone m
  isNone-only (m-pair x α′) = refl
  isNone-only m-left = refl
  isNone-only (m-dead x) = refl
  isNone-only (m-none R rc) = refl

  isNone-dead : (m : CMode Φ X ΘL ΘR) → isNone (CMode-dead m) ≡ isNone m
  isNone-dead (m-pair x α′) = refl
  isNone-dead m-left = refl
  isNone-dead (m-dead x) = refl
  isNone-dead (m-none R rc) = refl

  -- the bound of a mode moved to a future, at a lower stage
  ConM-↑ : ∀ d {ΘL′ ΘR′} (ρL : ΘL ↪ᵗ ΘL′) (ρR : ΘR ↪ᵗ ΘR′)
      (m : CMode Φ X ΘL ΘR) {rc rc′} → rc′ ≡ renRConv ρR rc
    → ∀ {k n N} → k ≤ n → ConM d m rc n N
    → ConM d (CMode-↑ ρL ρR m) rc′ k N
  ConM-↑ d ρL ρR m {rc} eq le cb =
    subst (λ b → ConMb d b _ _ _) (sym (isNone-↑ ρL ρR m))
      (subst (λ c → ConMb d (isNone m) c _ _) (sym eq)
        (ConMb-ren d (isNone m) ρR rc
          (ConMb-down d (isNone m) rc le cb)))

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

-- a right store variable created after the extension's source
NewRC : ∀ {w w′ : World} → w′ ⊒ w → RConv (storeR w′) → Set
NewRC e nothing = ⊤
NewRC e (just (β′ , R′)) = ∀ Y → toRenameᵗ (ρS e) Y ≢ β′

-- the right store binds the right's converted variable to its
-- representation
RCΣ : (w : World) → RConv (storeR w) → Set
RCΣ w nothing = ⊤
RCΣ w (just (α′ , R)) = ΣR w ∋Σ α′ ⦂ R

RCΣ-ren : ∀ {w w′ : World} (e : w′ ⊒ w) (rc : RConv (storeR w))
  → RCΣ w rc → RCΣ w′ (renRConv (ρS e) rc)
RCΣ-ren e nothing tt = tt
RCΣ-ren e (just (α′ , R)) x = ΣR⊒ e x

-- the expression closure of a leaf
ℰL : Dir → ℕ → (w : World) → Leaf (ΔL w) (ΔR w)
  → Term (ΔL w) → Term (storeR w) → Set
ℰL d n w L =
  ℰᵍ d n w (λ {n′} le w′ e → leafRel d n′ w′ (transportLeaf (ρL e) (ρR e) L))

-- a paired leaf with types T, T′ (T′ in the right store), closed under
-- later conversions
FreshP : Dir → RK → (w : World) → Leaf (ΔL w) (ΔR w)
  → Ty (ΔL w) → Ty (storeR w) → Set
FreshP d rk w L T T′ =
  ∀ {w′} (e : w′ ⊒ w) {β R} (rc : RConv (storeR w′)) → Allowed rk rc
  → NewL e β → NewRC e rc → RCΣ w′ rc → ∀ {k}
  → (∀ {Vl Vr} → Value Vl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) L) Vl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) L)
           (Vl ↑ 〖 β , R ↑ renameᵗ (toRenameᵗ (ρL e)) T 〗)
           (revM rc (renameᵗ (toRenameᵗ (ρS e)) T′) Vr))
    × (∀ {Wl Wr} → Value Wl → Value Wr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) L) Wl Wr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) L)
           (Wl ↓ makeConceal β R (renameᵗ (toRenameᵗ (ρL e)) T))
           (conM rc (renameᵗ (toRenameᵗ (ρS e)) T′) Wr))

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

-- the clauses' leaves, for bounds up to N; a pair clause's leaf at each
-- store preimage of its right type
Oracle : Dir → ℕ → Set
Oracle d N =
  (∀ {w} {n′ n} (le : n′ ≤′ n) → n′ ≤ N → (c : SDesc (ΔL w) (ΔR w))
     → WFS c → PreTy (ιʷ w) (rightTyS c) λ T₀
     → FreshP d both w (sem (leafBelowS d le c)) (leftTyS c) T₀)
  × (∀ {w} {n′ n} (le : n′ ≤′ n) → n′ ≤ N → (c : SDesc (ΔL w) (ΔR w))
     → FreshO d w (sem (onlyLeafS d le c)) (leftTyS c))

------------------------------------------------------------------------
-- A leaf under the conversion at hand
------------------------------------------------------------------------

-- the converted leaf Ls and the target leaf Lt of a variable whose
-- types are T and T′, under the conversion at α with representation R
-- and the right side's conversion rc, in every future; rc and T′ are in
-- the right store
ConvLeafP : Dir → ℕ → (w : World) → Ty (ΔL w) → RConv (storeR w)
  → TyVar (ΔL w) → (Ls Lt : Leaf (ΔL w) (ΔR w))
  → Ty (ΔL w) → Ty (storeR w) → Set
ConvLeafP d N w R rc α Ls Lt T T′ =
  ∀ {w′} (e : w′ ⊒ w) {k} → k ≤ N
  → (∀ {Vl Vr} → Value Vl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls) Vl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) Lt)
           (Vl ↑ 〖 toRenameᵗ (ρL e) α , renameᵗ (toRenameᵗ (ρL e)) R
                 ↑ renameᵗ (toRenameᵗ (ρL e)) T 〗)
           (revM (renRConv (ρS e) rc) (renameᵗ (toRenameᵗ (ρS e)) T′) Vr))
    × (∀ {Wl Wr} → Value Wl → Value Wr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Lt) Wl Wr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) Ls)
           (Wl ↓ makeConceal (toRenameᵗ (ρL e) α)
                   (renameᵗ (toRenameᵗ (ρL e)) R)
                   (renameᵗ (toRenameᵗ (ρL e)) T))
           (conM (renRConv (ρS e) rc) (renameᵗ (toRenameᵗ (ρS e)) T′) Wr))

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

-- a store substitution along an extension
_↑ˢ_ : ∀ {Δ′} {w w′ : World} → Δ′ ⇒ˢ storeR w → w′ ⊒ w
  → Δ′ ⇒ˢ storeR w′
(σ ↑ˢ e) Y = renameᵗ (toRenameᵗ (ρS e)) (σ Y)

-- a store type along an extension, embedded in the scope
coh-ty : ∀ {w w′ : World} (e : w′ ⊒ w) (T : Ty (storeR w))
  → renameᵗ (toRenameᵗ (ρR e)) (renameᵗ (toRenameᵗ (ιʷ w)) T)
    ≡ renameᵗ (toRenameᵗ (ιʷ w′)) (renameᵗ (toRenameᵗ (ρS e)) T)
coh-ty e T = CohE-ty (coh e) T

-- σ gives the store preimage of the right type B under the scope
-- substitution ρ (an interpretation's `δr`).  Only the right type at
-- hand needs one: an interpretation's other right types may name
-- reserved scope variables.
record PreB {Δ′} (w : World) (ρ : Δ′ ⇒ˢ ΔR w) (σ : Δ′ ⇒ˢ storeR w)
    (B : Ty Δ′) : Set where
  constructor preB
  field
    pre≡ : substᵗ ρ B ≡ renameᵗ (toRenameᵗ (ιʷ w)) (substᵗ σ B)

open PreB public

-- for both interpretations of the hypotheses
record PreS {Δ Δ′} (w : World) (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w))
    (σs σt : Δ′ ⇒ˢ storeR w) (B : Ty Δ′) : Set where
  constructor _,ᵖ_
  field
    pS : PreB w (δr δs) σs B
    pT : PreB w (δr δt) σt B

open PreS public

PreB-↑ : ∀ {Δ′} {w w′ : World} {ρ : Δ′ ⇒ˢ ΔR w} {σ B}
  → PreB w ρ σ B → (e : w′ ⊒ w)
  → PreB w′ (λ Y → renameᵗ (toRenameᵗ (ρR e)) (ρ Y)) (σ ↑ˢ e) B
pre≡ (PreB-↑ {w′ = w′} {ρ} {σ} {B} h e) =
  trans (sym (renameᵗ-subst (toRenameᵗ (ρR e)) ρ B))
    (trans (cong (renameᵗ (toRenameᵗ (ρR e))) (pre≡ h))
      (trans (coh-ty e (substᵗ σ B))
        (cong (renameᵗ (toRenameᵗ (ιʷ w′)))
          (renameᵗ-subst (toRenameᵗ (ρS e)) σ B))))

PreS-↑ : ∀ {Δ Δ′} {w w′ : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt B}
  → PreS w δs δt σs σt B → (e : w′ ⊒ w)
  → PreS w′ (δs ↑ᴵ e) (δt ↑ᴵ e) (σs ↑ˢ e) (σt ↑ˢ e) B
PreS-↑ (ps ,ᵖ pt) e = PreB-↑ ps e ,ᵖ PreB-↑ pt e

module _ {Δ′} {w : World} {ρ : Δ′ ⇒ˢ ΔR w} {σ : Δ′ ⇒ˢ storeR w} where

  private
    ⇒-inj₁ : ∀ {Θ} {A A′ B B′ : Ty Θ} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
    ⇒-inj₁ refl = refl
    ⇒-inj₂ : ∀ {Θ} {A A′ B B′ : Ty Θ} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
    ⇒-inj₂ refl = refl

  PreB-⇒₁ : ∀ {A B} → PreB w ρ σ (A ⇒ B) → PreB w ρ σ A
  pre≡ (PreB-⇒₁ h) = ⇒-inj₁ (pre≡ h)

  PreB-⇒₂ : ∀ {A B} → PreB w ρ σ (A ⇒ B) → PreB w ρ σ B
  pre≡ (PreB-⇒₂ h) = ⇒-inj₂ (pre≡ h)

  -- the body of a `∀` type, under the store substitution
  PreB-body : ∀ B → PreB w ρ σ (`∀ B)
    → substᵗ (extsᵗ ρ) B
      ≡ renameᵗ (toRenameᵗ (keepᵗ (ιʷ w))) (substᵗ (extsᵗ σ) B)
  PreB-body B h =
    trans (∀-inj (pre≡ h)) (renameᵗ-cong (substᵗ (extsᵗ σ) B) keep-ext)
    where
    ∀-inj : ∀ {Θ} {C C′ : Ty (suc Θ)} → `∀ C ≡ `∀ C′ → C ≡ C′
    ∀-inj refl = refl
    keep-ext : ∀ X → extᵗ (toRenameᵗ (ιʷ w)) X
      ≡ toRenameᵗ (keepᵗ (ιʷ w)) X
    keep-ext zero = refl
    keep-ext (suc X) = refl

  -- the body of a `∀` type, its variable at a store type T′
  PreB-ext : ∀ B → PreB w ρ σ (`∀ B) → (T′ : Ty (storeR w))
    → PreB w (renameᵗ (toRenameᵗ (ιʷ w)) T′ •ˢ ρ) (T′ •ˢ σ) B
  pre≡ (PreB-ext B h T′) =
    trans (sym (open-ext ρ (renameᵗ ι T′)))
      (trans (cong (substᵗ (singleSubᵗ (renameᵗ ι T′))) (PreB-body B h))
        (trans (substᵗ-rename (singleSubᵗ (renameᵗ ι T′))
                 (toRenameᵗ (keepᵗ (ιʷ w))) C)
          (trans (substᵗ-cong C pw)
            (trans (sym (renameᵗ-subst ι (singleSubᵗ T′) C))
              (cong (renameᵗ ι) (open-ext σ T′))))))
    where
    ι = toRenameᵗ (ιʷ w)
    C = substᵗ (extsᵗ σ) B
    open-ext : ∀ {Θ} (τ : Δ′ ⇒ˢ Θ) (U : Ty Θ)
      → substᵗ (singleSubᵗ U) (substᵗ (extsᵗ τ) B) ≡ substᵗ (U •ˢ τ) B
    open-ext τ U = trans (substᵗ-∘ (singleSubᵗ U) (extsᵗ τ) B)
      (substᵗ-cong B λ { zero → refl ; (suc Y) → shift-openᵗ (τ Y) U })
    pw : ∀ X → singleSubᵗ (renameᵗ ι T′) (toRenameᵗ (keepᵗ (ιʷ w)) X)
      ≡ renameᵗ ι (singleSubᵗ T′ X)
    pw zero = refl
    pw (suc X) = refl

module _ {Δ Δ′} {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt : Δ′ ⇒ˢ storeR w} where

  PreS-⇒₁ : ∀ {A B} → PreS w δs δt σs σt (A ⇒ B) → PreS w δs δt σs σt A
  PreS-⇒₁ (ps ,ᵖ pt) = PreB-⇒₁ ps ,ᵖ PreB-⇒₁ pt

  PreS-⇒₂ : ∀ {A B} → PreS w δs δt σs σt (A ⇒ B) → PreS w δs δt σs σt B
  PreS-⇒₂ (ps ,ᵖ pt) = PreB-⇒₂ ps ,ᵖ PreB-⇒₂ pt

∀-inj : ∀ {Θ} {C C′ : Ty (suc Θ)} → `∀ C ≡ `∀ C′ → C ≡ C′
∀-inj refl = refl

-- two scope substitutions agree on the right type B, in a future and
-- under a binder at T
module _ {Δ′ Θ} {ρs ρt : Δ′ ⇒ˢ Θ} where

  Agree-↑ : ∀ {Θ′} (π : Θ ⇒ʳ Θ′) B → substᵗ ρs B ≡ substᵗ ρt B
    → substᵗ (λ Y → renameᵗ π (ρs Y)) B ≡ substᵗ (λ Y → renameᵗ π (ρt Y)) B
  Agree-↑ π B a =
    trans (sym (renameᵗ-subst π ρs B))
      (trans (cong (renameᵗ π) a) (renameᵗ-subst π ρt B))

  Agree-ext : ∀ B → substᵗ ρs (`∀ B) ≡ substᵗ ρt (`∀ B) → ∀ T
    → substᵗ (T •ˢ ρs) B ≡ substᵗ (T •ˢ ρt) B
  Agree-ext B a T =
    trans (sym (open-ext ρs))
      (trans (cong (substᵗ (singleSubᵗ T)) (∀-inj a)) (open-ext ρt))
    where
    open-ext : ∀ (τ : Δ′ ⇒ˢ Θ)
      → substᵗ (singleSubᵗ T) (substᵗ (extsᵗ τ) B) ≡ substᵗ (T •ˢ τ) B
    open-ext τ = trans (substᵗ-∘ (singleSubᵗ T) (extsᵗ τ) B)
      (substᵗ-cong B λ { zero → refl ; (suc Y) → shift-openᵗ (τ Y) T })

-- what the lemma's right side needs of the right type B: when the
-- right does not convert, the two interpretations agree on B; when it
-- converts, B has store preimages under both
record PreM {Δ Δ′} (w : World) (rc : RConv (storeR w))
    (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (σs σt : Δ′ ⇒ˢ storeR w)
    (B : Ty Δ′) : Set where
  field
    pNo : rc ≡ nothing → substᵗ (δr δs) B ≡ substᵗ (δr δt) B
    pJust : ∀ {c} → rc ≡ just c → PreS w δs δt σs σt B

open PreM public

module _ {Δ Δ′} {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt : Δ′ ⇒ˢ storeR w} {B : Ty Δ′} where

  PreM-just : ∀ {rc c} → rc ≡ just c → PreS w δs δt σs σt B
    → PreM w rc δs δt σs σt B
  pNo (PreM-just refl ps) ()
  pJust (PreM-just eq ps) eq′ = ps

  PreM-nothing : ∀ {rc} → rc ≡ nothing
    → substᵗ (δr δs) B ≡ substᵗ (δr δt) B → PreM w rc δs δt σs σt B
  pNo (PreM-nothing eq a) eq′ = a
  pJust (PreM-nothing refl a) ()

  -- interpretations with the same right types
  PreM-re : ∀ {rc Δ₁} {δs′ δt′ : Interp Δ₁ Δ′ (ΔL w) (ΔR w)}
    → δr δs′ ≡ δr δs → δr δt′ ≡ δr δt → PreM w rc δs δt σs σt B
    → PreM w rc δs′ δt′ σs σt B
  pNo (PreM-re es et h) eq =
    subst₂ (λ a b → substᵗ a B ≡ substᵗ b B) (sym es) (sym et) (pNo h eq)
  pJust (PreM-re es et h) eq =
    subst (λ a → PreB w a σs B) (sym es) (pS (pJust h eq)) ,ᵖ
    subst (λ a → PreB w a σt B) (sym et) (pT (pJust h eq))

PreM-↑ : ∀ {Δ Δ′} {w w′ : World} {rc} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt B}
  → PreM w rc δs δt σs σt B → (e : w′ ⊒ w) → ∀ {rc′}
  → rc′ ≡ renRConv (ρS e) rc
  → PreM w′ rc′ (δs ↑ᴵ e) (δt ↑ᴵ e) (σs ↑ˢ e) (σt ↑ˢ e) B
pNo (PreM-↑ {rc = nothing} {B = B} h e eq) eq′ =
  Agree-↑ (toRenameᵗ (ρR e)) B (pNo h refl)
pNo (PreM-↑ {rc = just c} h e refl) ()
pJust (PreM-↑ {rc = nothing} h e refl) ()
pJust (PreM-↑ {rc = just c} h e eq) eq′ = PreS-↑ (pJust h refl) e

module _ {Δ Δ′} {w : World} {rc : RConv (storeR w)}
    {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {σs σt : Δ′ ⇒ˢ storeR w} where

  private
    ⇒-inj₁ : ∀ {Θ} {A A′ B B′ : Ty Θ} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
    ⇒-inj₁ refl = refl
    ⇒-inj₂ : ∀ {Θ} {A A′ B B′ : Ty Θ} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
    ⇒-inj₂ refl = refl

  PreM-⇒₁ : ∀ {A B} → PreM w rc δs δt σs σt (A ⇒ B)
    → PreM w rc δs δt σs σt A
  pNo (PreM-⇒₁ h) eq = ⇒-inj₁ (pNo h eq)
  pJust (PreM-⇒₁ h) eq = PreS-⇒₁ (pJust h eq)

  PreM-⇒₂ : ∀ {A B} → PreM w rc δs δt σs σt (A ⇒ B)
    → PreM w rc δs δt σs σt B
  pNo (PreM-⇒₂ h) eq = ⇒-inj₂ (pNo h eq)
  pJust (PreM-⇒₂ h) eq = PreS-⇒₂ (pJust h eq)

------------------------------------------------------------------------
-- The right's conversions keep right terms typed
------------------------------------------------------------------------

-- a typed term's store type is the preimage PreB gives
pre-typed : ∀ {Δ′} {w : World} {ρ : Δ′ ⇒ˢ ΔR w} {σ B V}
  → PreB w ρ σ B → Typedᴿ w (substᵗ ρ B) V
  → CT.⟨ storeR w , ΣR w , Data.List.[] ⟩ CT.⊢ V ⦂ substᵗ σ B
pre-typed {w = w} {V = V} pb (typedᴿ T₀ eq t) =
  subst (λ A → CT.⟨ storeR w , ΣR w , Data.List.[] ⟩ CT.⊢ V ⦂ A)
    (sym (renameᵗ-injective (toRenameᵗ-injective (ιʷ w))
      (trans (sym (pre≡ pb)) eq)))
    t

-- replacing a variable in a substituted type
replace-substᵗ : ∀ {Δ′ Θ} (α′ : TyVar Θ) (R : Ty Θ) (σs σt : Δ′ ⇒ˢ Θ) B
  → (∀ Y → replaceTy α′ R (σs Y) ≡ σt Y)
  → replaceTy α′ R (substᵗ σs B) ≡ substᵗ σt B
replace-substᵗ α′ R σs σt B ty =
  trans (replaceTy-subst α′ R σs B) (substᵗ-cong B ty)

module _ {Δ Δ′} {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt : Δ′ ⇒ˢ storeR w} where

  revTyped : ∀ (rc : RConv (storeR w)) B {V} → RCΣ w rc
    → (∀ Y → replaceRC rc (σs Y) ≡ σt Y) → PreM w rc δs δt σs σt B
    → Typedᴿ w (substᵗ (δr δs) B) V
    → Typedᴿ w (substᵗ (δr δt) B) (revM rc (substᵗ σs B) V)
  revTyped nothing B rs ty pm t = Typedᴿ-≡ (pNo pm refl) t
  revTyped (just (α′ , R)) B {V} rs ty pm t =
    typedᴿ (substᵗ σt B) (pre≡ (pT ps))
      (subst (λ A → CT.⟨ storeR w , ΣR w , Data.List.[] ⟩
                      CT.⊢ V ↑ 〖 α′ , R ↑ substᵗ σs B 〗 ⦂ A)
        (replace-substᵗ α′ R σs σt B ty)
        (CT.⊢reveal (structural-reveal-typing (substᵗ σs B) rs)
          (pre-typed (pS ps) t)))
    where
    ps = pJust pm refl

  conTyped : ∀ (rc : RConv (storeR w)) B {V} → RCΣ w rc
    → (∀ Y → replaceRC rc (σs Y) ≡ σt Y) → PreM w rc δs δt σs σt B
    → Typedᴿ w (substᵗ (δr δt) B) V
    → Typedᴿ w (substᵗ (δr δs) B) (conM rc (substᵗ σs B) V)
  conTyped nothing B rs ty pm t = Typedᴿ-≡ (sym (pNo pm refl)) t
  conTyped (just (α′ , R)) B {V} rs ty pm t =
    typedᴿ (substᵗ σs B) (pre≡ (pS ps))
      (CT.⊢conceal (structural-conceal-typing (substᵗ σs B) rs)
        (subst (λ A → CT.⟨ storeR w , ΣR w , Data.List.[] ⟩ CT.⊢ V ⦂ A)
          (sym (replace-substᵗ α′ R σs σt B ty))
          (pre-typed (pT ps) t)))
    where
    ps = pJust pm refl

  -- where the right does not convert
  noTypedR : ∀ B {V} → PreM w nothing δs δt σs σt B
    → Typedᴿ w (substᵗ (δr δs) B) V → Typedᴿ w (substᵗ (δr δt) B) V
  noTypedR B pm t = Typedᴿ-≡ (pNo pm refl) t

  noTypedC : ∀ B {V} → PreM w nothing δs δt σs σt B
    → Typedᴿ w (substᵗ (δr δt) B) V → Typedᴿ w (substᵗ (δr δs) B) V
  noTypedC B pm t = Typedᴿ-≡ (sym (pNo pm refl)) t

↑ˢ-trans : ∀ {Δ′} {w w′ w″ : World} (σ : Δ′ ⇒ˢ storeR w) (e′ : w″ ⊒ w′)
    (e : w′ ⊒ w) Y
  → ((σ ↑ˢ e) ↑ˢ e′) Y ≡ (σ ↑ˢ ⊒-trans e′ e) Y
↑ˢ-trans σ e′ e Y = renameTy-∘ (ρS e′) (ρS e) (σ Y)

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  -- the converted variable's types under the source substitutions (the
  -- left one, and the right store one)
  SelfI : ∀ {ΘL ΘR} → CMode Φ X ΘL ΘR → TyVar ΘL
    → (Δ ⇒ˢ ΘL) → (Δ′ ⇒ˢ ΘR) → Set
  SelfI (m-pair {Y = Y} x α′) α σl σs = σl X ≡ ＇ α × σs Y ≡ ＇ α′
  SelfI m-left α σl σs = σl X ≡ ＇ α
  SelfI (m-dead x) α σl σs = σl X ≡ ＇ α
  SelfI (m-none R rc) α σl σs = ⊤

  -- X's leaves, in every future: the converted side's leaf (δs) holds of
  -- sealed values whose contents the target leaf (δt) relates; the right
  -- seals at the store type σt Y
  SealI : Dir → ℕ → (w : World) → CMode Φ X (ΔL w) (storeR w)
    → TyVar (ΔL w) → (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w))
    → Δ′ ⇒ˢ storeR w → Set
  SealI d N w (m-pair {Y = Y} x α′) α δs δt σt =
    (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X) Vl Vr
       → sealedL (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X)
           (sealedR (toRenameᵗ (ρS e) α′) ((σt ↑ˢ e) Y)
             (leafRel d (pred k) w′ (leaf (δt ↑ᴵ e) X))) Vl Vr)
    × (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k < N → ∀ {Wl Wr}
       → leafRel d k w′ (leaf (δt ↑ᴵ e) X) Wl Wr
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X)
           (Wl ↓ seal (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X))
           (Wr ↓ seal (toRenameᵗ (ρS e) α′) ((σt ↑ˢ e) Y)))
  SealI d N w m-left α δs δt σt =
    (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X) Vl Vr
       → sealedL (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X)
           (leafRel d (onlyStage d k) w′ (leaf (δt ↑ᴵ e) X)) Vl Vr)
    × (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → onlyBelow d k N → ∀ {Wl Vr}
       → leafRel d k w′ (leaf (δt ↑ᴵ e) X) Wl Vr
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X)
           (Wl ↓ seal (toRenameᵗ (ρL e) α) (δl (δt ↑ᴵ e) X)) Vr)
  SealI d N w (m-dead x) α δs δt σt = ⊤
  SealI d N w (m-none R rc) α δs δt σt = ⊤

  -- an other variable's leaf, under the conversion at hand, in every
  -- future
  ConvP : Dir → ℕ → (w : World) → CMode Φ X (ΔL w) (storeR w)
    → TyVar (ΔL w) → (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w))
    → (σs σt : Δ′ ⇒ˢ storeR w) → ∀ {Z Y′} → Φ ∋ Z ↔ Y′ → Set
  ConvP d N w m α δs δt σs σt {Z} {Y′} z =
    ConvLeafP d N w (repM m (δl δt)) (rconv m σt) α
      (leaf δs Z) (leaf δt Z) (δl δs Z) (σs Y′)

  ConvO : Dir → ℕ → (w : World) → CMode Φ X (ΔL w) (storeR w)
    → TyVar (ΔL w) → (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) → ∀ {Z}
    → Φ ∋ Z only → Set
  ConvO d N w m α δs δt {Z} z =
    ConvLeafO d N w (repM m (δl δt)) α (leaf δs Z) (leaf δt Z) (δl δs Z)

  -- σs, σt: the store preimages of δs's and δt's right types
  record ConvI (d : Dir) (N : ℕ) (rk : RK) (w : World)
      (m : CMode Φ X (ΔL w) (storeR w)) (α : TyVar (ΔL w))
      (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w))
      (σs σt : Δ′ ⇒ˢ storeR w) : Set₁ where
    field
      goodS : GoodI δs
      goodT : GoodI δt
      selfI : SelfI m α (δl δs) σs
      rcOK : Allowed rk (rconv m σt)
      tyL : ∀ Z → replaceTy α (repM m (δl δt)) (δl δs Z) ≡ δl δt Z
      tyR : ∀ Y′ → replaceRC (rconv m σt) (σs Y′) ≡ σt Y′
      rcΣ : RCΣ w (rconv m σt)
      leafO : ∀ Z → Other m Z → leaf δs Z ≈ˡ leaf δt Z
      convP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → Other m Z
        → ConvP d N w m α δs δt σs σt z
      convO : ∀ {Z} (z : Φ ∋ Z only) → Other m Z
        → ConvO d N w m α δs δt z
      genP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′)
        → FreshP d rk w (leaf δt Z) (δl δt Z) (σt Y′)
      genO : ∀ {Z} (z : Φ ∋ Z only)
        → FreshO d w (leaf δt Z) (δl δt Z)
      genPS : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′)
        → FreshP d rk w (leaf δs Z) (δl δs Z) (σs Y′)
      genOS : ∀ {Z} (z : Φ ∋ Z only)
        → FreshO d w (leaf δs Z) (δl δs Z)
      sealI : SealI d N w m α δs δt σt
      oracle : Oracle d N

  open ConvI public

-- an interpretation whose leaves are closed under later conversions; σ
-- gives the store preimages of its right types
record FreshI {Δ Δ′} (Φ : Corr Δ Δ′) (d : Dir) (N : ℕ) (rk : RK)
    (w : World) (δ : Interp Δ Δ′ (ΔL w) (ΔR w))
    (σ : Δ′ ⇒ˢ storeR w) : Set₁ where
  field
    fgood : GoodI δ
    fP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′)
      → FreshP d rk w (leaf δ Z) (δl δ Z) (σ Y′)
    fO : ∀ {Z} (z : Φ ∋ Z only) → FreshO d w (leaf δ Z) (δl δ Z)
    forc : Oracle d N

open FreshI public

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d N rk} {w : World}
    {m : CMode Φ X (ΔL w) (storeR w)} {α}
    {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {σs σt : Δ′ ⇒ˢ storeR w}
    where

  -- the two interpretations of the hypotheses
  freshT : ConvI d N rk w m α δs δt σs σt → FreshI Φ d N rk w δt σt
  fgood (freshT h) = goodT h
  fP (freshT h) = genP h
  fO (freshT h) = genO h
  forc (freshT h) = oracle h

  freshS : ConvI d N rk w m α δs δt σs σt → FreshI Φ d N rk w δs σs
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
    (rc : RConv (storeR w″))
  → NewRC e′ rc → NewRC (⊒-trans e′ e) rc
NewRC-∘ e′ e nothing nb = tt
NewRC-∘ e′ e (just (β′ , R′)) nb Y eq =
  nb (toRenameᵗ (ρS e) Y) (trans (sym (toRenameᵗ-∘ (ρS e′) (ρS e) Y)) eq)

------------------------------------------------------------------------
-- Closure moves to future worlds
------------------------------------------------------------------------

module _ {d} {w w′ : World} (e : w′ ⊒ w) {L : Leaf (ΔL w) (ΔR w)} where

  private
    L′ = transportLeaf (ρL e) (ρR e) L

  FreshP-↑ : ∀ {rk T T′} → FreshP d rk w L T T′
    → FreshP d rk w′ L′ (renameᵗ (toRenameᵗ (ρL e)) T)
        (renameᵗ (toRenameᵗ (ρS e)) T′)
  FreshP-↑ {T = T} {T′} f {w″} e′ {β} {R} rc ok nb nrc rs {k} =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w″ (≈ˡ-sym L∘)
        (ℰL-≡ d k w″ L₂
          (cong (λ C → Vl ↑ 〖 β , R ↑ C 〗)
            (sym (renameTy-∘ (ρL e′) (ρL e) T)))
          (cong (λ C → revM rc C Vr) (sym (renameTy-∘ (ρS e′) (ρS e) T′)))
          (proj₁ g vl vr (leafRel-resp d k w″ L∘ r)))) ,
    (λ {Wl} {Wr} wl wr r →
      ℰL-resp d k w″ (≈ˡ-sym L∘)
        (ℰL-≡ d k w″ L₂
          (cong (λ C → Wl ↓ makeConceal β R C)
            (sym (renameTy-∘ (ρL e′) (ρL e) T)))
          (cong (λ C → conM rc C Wr) (sym (renameTy-∘ (ρS e′) (ρS e) T′)))
          (proj₂ g wl wr (leafRel-resp d k w″ L∘ r))))
    where
    L∘ = transportLeaf-∘ (ρL e′) (ρL e) (ρR e′) (ρR e) L
    L₂ = transportLeaf (ρL e′ ∘↪ ρL e) (ρR e′ ∘↪ ρR e) L
    g = f (⊒-trans e′ e) rc ok (NewL-∘ e′ e nb) (NewRC-∘ e′ e rc nrc) rs
          {k}


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
    {σs σt : Δ′ ⇒ˢ storeR w} (e : w′ ⊒ w) where

  private
    ρl = toRenameᵗ (ρL e)
    ρs = toRenameᵗ (ρS e)

  SelfI-↑ : ∀ (m : CMode Φ X (ΔL w) (storeR w)) α → SelfI m α (δl δs) σs
    → SelfI (CMode-↑ (ρL e) (ρS e) m) (ρl α) (δl (δs ↑ᴵ e)) (σs ↑ˢ e)
  SelfI-↑ (m-pair x α′) α (a , b) = cong (renameᵗ ρl) a , cong (renameᵗ ρs) b
  SelfI-↑ m-left α a = cong (renameᵗ ρl) a
  SelfI-↑ (m-dead x) α a = cong (renameᵗ ρl) a
  SelfI-↑ (m-none R rc) α a = tt

  -- the conversion at hand, in a future of the future
  module Comp (m : CMode Φ X (ΔL w) (storeR w)) (α : TyVar (ΔL w))
      {w″} (e′ : w″ ⊒ w′) where

    α∘ : toRenameᵗ (ρL (⊒-trans e′ e)) α ≡ toRenameᵗ (ρL e′) (ρl α)
    α∘ = toRenameᵗ-∘ (ρL e′) (ρL e) α

    R∘ : renameᵗ (toRenameᵗ (ρL (⊒-trans e′ e))) (repM m (δl δt))
      ≡ renameᵗ (toRenameᵗ (ρL e′))
          (repM (CMode-↑ (ρL e) (ρS e) m) (δl (δt ↑ᴵ e)))
    R∘ = trans (sym (renameTy-∘ (ρL e′) (ρL e) (repM m (δl δt))))
      (cong (renameᵗ (toRenameᵗ (ρL e′)))
        (sym (repM-↑ (ρL e) (ρS e) m (δl δt))))

    rc∘ : renRConv (ρS (⊒-trans e′ e)) (rconv m σt)
      ≡ renRConv (ρS e′) (rconv (CMode-↑ (ρL e) (ρS e) m) (σt ↑ˢ e))
    rc∘ = trans (sym (renRConv-∘ (ρS e′) (ρS e) (rconv m σt)))
      (cong (renRConv (ρS e′)) (sym (rconv-↑ (ρL e) (ρS e) m σt)))

  ConvP-↑ : ∀ (m : CMode Φ X (ΔL w) (storeR w)) α {Z Y′}
      (z : Φ ∋ Z ↔ Y′)
    → ConvP d N w m α δs δt σs σt z
    → ConvP d N w′ (CMode-↑ (ρL e) (ρS e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e)
        (σs ↑ˢ e) (σt ↑ˢ e) z
  ConvP-↑ m α {Z} {Y′} z h {w″} e′ {k} k≤N =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) Z))
        (ℰL-≡ d k w″ (leaf (δt ↑ᴵ ⊒-trans e′ e) Z)
          (↑〖〗-≡ (Comp.α∘ m α e′) (Comp.R∘ m α e′)
            (sym (δl≡ (↑ᴵ-trans δs e′ e) Z)))
          (revM-≡ (Comp.rc∘ m α e′) (sym (↑ˢ-trans σs e′ e Y′)))
          (proj₁ g vl vr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) Z) r)))) ,
    (λ {Wl} {Wr} wl wr r →
      ℰL-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) Z))
        (ℰL-≡ d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) Z)
          (↓mc-≡ (Comp.α∘ m α e′) (Comp.R∘ m α e′)
            (sym (δl≡ (↑ᴵ-trans δs e′ e) Z)))
          (conM-≡ (Comp.rc∘ m α e′) (sym (↑ˢ-trans σs e′ e Y′)))
          (proj₂ g wl wr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δt e′ e) Z) r))))
    where
    g = h (⊒-trans e′ e) k≤N

  ConvO-↑ : ∀ (m : CMode Φ X (ΔL w) (storeR w)) α {Z} (z : Φ ∋ Z only)
    → ConvO d N w m α δs δt z
    → ConvO d N w′ (CMode-↑ (ρL e) (ρS e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e) z
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

  SealI-↑ : ∀ (m : CMode Φ X (ΔL w) (storeR w)) α
    → SealI d N w m α δs δt σt
    → SealI d N w′ (CMode-↑ (ρL e) (ρS e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e)
        (σt ↑ˢ e)
  SealI-↑ (m-pair {Y = Y} x α′) α (hrev , hcon) = rev′ , con′
    where
    rev′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
      → leafRel d k w″ (leaf ((δs ↑ᴵ e) ↑ᴵ e′) X) Vl Vr
      → sealedL (toRenameᵗ (ρL e′) (ρl α)) (δl ((δt ↑ᴵ e) ↑ᴵ e′) X)
          (sealedR (toRenameᵗ (ρS e′) (ρs α′)) (((σt ↑ˢ e) ↑ˢ e′) Y)
            (leafRel d (pred k) w″ (leaf ((δt ↑ᴵ e) ↑ᴵ e′) X))) Vl Vr
    rev′ {w″} e′ {k} pos le r =
      sealedL-map (toRenameᵗ-∘ (ρL e′) (ρL e) α)
        (sym (δl≡ (↑ᴵ-trans δt e′ e) X))
        (sealedR-map (toRenameᵗ-∘ (ρS e′) (ρS e) α′)
          (sym (↑ˢ-trans σt e′ e Y))
          (leafRel-resp d (pred k) w″
            (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) X))))
        (hrev (⊒-trans e′ e) pos le
          (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) X) r))
    con′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → k < N → ∀ {Wl Wr}
      → leafRel d k w″ (leaf ((δt ↑ᴵ e) ↑ᴵ e′) X) Wl Wr
      → leafRel d k w″ (leaf ((δs ↑ᴵ e) ↑ᴵ e′) X)
          (Wl ↓ seal (toRenameᵗ (ρL e′) (ρl α)) (δl ((δt ↑ᴵ e) ↑ᴵ e′) X))
          (Wr ↓ seal (toRenameᵗ (ρS e′) (ρs α′)) (((σt ↑ˢ e) ↑ˢ e′) Y))
    con′ {w″} e′ {k} pos lt {Wl} {Wr} r =
      leafRel-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) X))
        (subst₂ (leafRel d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) X))
          (cong₂ (λ a R → Wl ↓ seal a R) (toRenameᵗ-∘ (ρL e′) (ρL e) α)
            (sym (δl≡ (↑ᴵ-trans δt e′ e) X)))
          (cong₂ (λ a R → Wr ↓ seal a R) (toRenameᵗ-∘ (ρS e′) (ρS e) α′)
            (sym (↑ˢ-trans σt e′ e Y)))
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

  ConvI-↑ : ∀ {m : CMode Φ X (ΔL w) (storeR w)} {α}
    → ConvI d N rk w m α δs δt σs σt
    → ConvI d N rk w′ (CMode-↑ (ρL e) (ρS e) m) (ρl α) (δs ↑ᴵ e) (δt ↑ᴵ e)
        (σs ↑ˢ e) (σt ↑ˢ e)
  goodS (ConvI-↑ h) = GoodI-↑ {δ = δs} (goodS h) e
  goodT (ConvI-↑ h) = GoodI-↑ {δ = δt} (goodT h) e
  selfI (ConvI-↑ {m = m} {α} h) = SelfI-↑ m α (selfI h)
  rcOK (ConvI-↑ {m = m} h) =
    subst (Allowed rk) (sym (rconv-↑ (ρL e) (ρS e) m σt))
      (Allowed-ren rk (ρS e) (rconv m σt) (rcOK h))
  tyL (ConvI-↑ {m = m} {α} h) Z =
    trans (cong (λ R → replaceTy (ρl α) R (renameᵗ ρl (δl δs Z)))
            (repM-↑ (ρL e) (ρS e) m (δl δt)))
      (trans (sym (replaceTy-rename ρl (toRenameᵗ-injective (ρL e)) α
               (repM m (δl δt)) (δl δs Z)))
        (cong (renameᵗ ρl) (tyL h Z)))
  tyR (ConvI-↑ {m = m} h) Y′ =
    trans (cong (λ c → replaceRC c (renameᵗ ρs (σs Y′)))
            (rconv-↑ (ρL e) (ρS e) m σt))
      (trans (replaceRC-ren (ρS e) (rconv m σt) (σs Y′))
        (cong (renameᵗ ρs) (tyR h Y′)))
  rcΣ (ConvI-↑ {m = m} h) =
    subst (RCΣ w′) (sym (rconv-↑ (ρL e) (ρS e) m σt))
      (RCΣ-ren e (rconv m σt) (rcΣ h))
  leafO (ConvI-↑ {m = m} h) Z o =
    transportLeaf-resp (ρL e) (ρR e)
      (leafO h Z (Other-↑ (ρL e) (ρS e) m Z o))
  convP (ConvI-↑ {m = m} {α} h) {Z} z o =
    ConvP-↑ m α z (convP h z (Other-↑ (ρL e) (ρS e) m Z o))
  convO (ConvI-↑ {m = m} {α} h) {Z} z o =
    ConvO-↑ m α z (convO h z (Other-↑ (ρL e) (ρS e) m Z o))
  genP (ConvI-↑ h) {Z} {Y′} z =
    FreshP-↑ {d = d} e {L = leaf δt Z} {rk} {δl δt Z} {σt Y′} (genP h z)
  genO (ConvI-↑ h) {Z} z =
    FreshO-↑ {d = d} e {L = leaf δt Z} {δl δt Z} (genO h z)
  genPS (ConvI-↑ h) {Z} {Y′} z =
    FreshP-↑ {d = d} e {L = leaf δs Z} {rk} {δl δs Z} {σs Y′}
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

-- the right side's conversion is absent, or at ★ or another store
-- variable
RId : ∀ {Θ} → RConv Θ → Ty Θ → Set
RId {Θ} nothing T′ = ⊤
RId {Θ} (just (α′ , R′)) T′ =
  T′ ≡ ★ ⊎ Σ[ γ′ ∈ TyVar Θ ] (T′ ≡ ＇ γ′ × γ′ ≢ α′)

rstep : ∀ {Θ} (rc : RConv Θ) {T′} → RId rc T′ → ∀ {V : Term Θ}
  → Value V → revM rc T′ V —→? V
rstep nothing tt v = stay
rstep (just (α′ , R′)) (inj₁ refl) v = step (id-reveal v)
rstep (just (α′ , R′)) (inj₂ (γ′ , eq , ne)) {V} v =
  subst (λ M → M —→? V) (sym (↑-pk (〖〗-other R′ eq ne)))
    (step (id-reveal v))

cstep : ∀ {Θ} (rc : RConv Θ) {T′} → RId rc T′ → ∀ {V : Term Θ}
  → Value V → conM rc T′ V —→? V
cstep nothing tt v = stay
cstep (just (α′ , R′)) (inj₁ refl) v = step (id-conceal v)
cstep (just (α′ , R′)) (inj₂ (γ′ , eq , ne)) {V} v =
  subst (λ M → M —→? V) (sym (↓-pk (makeConceal-other R′ eq ne)))
    (step (id-conceal v))

-- a store type in the scope
ιT : (w : World) → Ty (storeR w) → Ty (ΔR w)
ιT w = renameᵗ (toRenameᵗ (ιʷ w))

-- the leaf is read as the only variable of an interpretation
module _ (d : Dir) (k : ℕ) (w : World) (L : Leaf (ΔL w) (ΔR w))
    (gl : GoodLeaf L) where

  idRevP : ∀ {α γ : TyVar (ΔL w)} {R} → γ ≢ α → (rc : RConv (storeR w))
    → ∀ {T′} → RId rc T′ → ∀ {Vl Vr} → Value Vl → Value Vr
    → leafRel d k w L Vl Vr
    → ℰL d k w L (Vl ↑ 〖 α , R ↑ ＇ γ 〗) (revM rc T′ Vr)
  idRevP {α} {γ} {R} ne rc {T′} ri {Vl} vl vr r =
    XY→ℰL d k (↔-here {Φ = []}) w {δ = extPairI (＇ γ) (ιT w T′) L closedI}
      (ℰ-≡ d k (X⊑Y ↔-here) w (extPairI (＇ γ) (ιT w T′) L closedI)
        (sym (↑-pk (〖〗-other R refl ne))) refl
        (ℰ-steps? d k (X⊑Y ↔-here) w
          (GoodI-extPairI {T = ＇ γ} {T′ = ιT w T′} {δ = closedI} gl
            good-closedI)
          (step (id-reveal vl)) (rstep rc ri vr) vl vr
          (to (𝒱-XY d k ↔-here w) r)))

  idConP : ∀ {α γ : TyVar (ΔL w)} {R} → γ ≢ α → (rc : RConv (storeR w))
    → ∀ {T′} → RId rc T′ → ∀ {Wl Wr} → Value Wl → Value Wr
    → leafRel d k w L Wl Wr
    → ℰL d k w L (Wl ↓ makeConceal α R (＇ γ)) (conM rc T′ Wr)
  idConP {α} {γ} {R} ne rc {T′} ri {Wl} wl wr r =
    XY→ℰL d k (↔-here {Φ = []}) w {δ = extPairI (＇ γ) (ιT w T′) L closedI}
      (ℰ-≡ d k (X⊑Y ↔-here) w (extPairI (＇ γ) (ιT w T′) L closedI)
        (sym (↓-pk (makeConceal-other R refl ne)))
        refl
        (ℰ-steps? d k (X⊑Y ↔-here) w
          (GoodI-extPairI {T = ＇ γ} {T′ = ιT w T′} {δ = closedI} gl
            good-closedI)
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
    {σt : Δ′ ⇒ˢ storeR w} {T : Ty (ΔL w)} {l : Leaf (ΔL w) (ΔR w)} where

  SealI-pair : ∀ (m : CMode Φ X (ΔL w) (storeR w)) {T′ T₀}
    → SealI d N w m α δs δt σt
    → SealI d N w (CMode-pair m) α (extPairI T T′ l δs) (extPairI T T′ l δt)
        (T₀ •ˢ σt)
  SealI-pair (m-pair x α′) h = h
  SealI-pair m-left h = h
  SealI-pair (m-dead x) h = h
  SealI-pair (m-none R rc) h = h

  SealI-only : ∀ (m : CMode Φ X (ΔL w) (storeR w))
    → SealI d N w m α δs δt σt
    → SealI d N w (CMode-only m) α (extOnlyI T l δs) (extOnlyI T l δt) σt
  SealI-only (m-pair x α′) h = h
  SealI-only m-left h = h
  SealI-only (m-dead x) h = h
  SealI-only (m-none R rc) h = h

  SealI-dead : ∀ (m : CMode Φ X (ΔL w) (storeR w))
    → SealI d N w m α δs δt σt
    → SealI d N w (CMode-dead m) α (extDeadI T δs) (extDeadI T δt) σt
  SealI-dead (m-pair x α′) h = h
  SealI-dead m-left h = h
  SealI-dead (m-dead x) h = h
  SealI-dead (m-none R rc) h = h


SelfI-pair : ∀ {Φ : Corr Δ Δ′} {X} (m : CMode Φ X ΘL ΘR) {α}
    {σl : Δ ⇒ˢ ΘL} {σs : Δ′ ⇒ˢ ΘR} {T T′}
  → SelfI m α σl σs → SelfI (CMode-pair m) α (T •ˢ σl) (T′ •ˢ σs)
SelfI-pair (m-pair x α′) h = h
SelfI-pair m-left h = h
SelfI-pair (m-dead x) h = h
SelfI-pair (m-none R rc) h = h

SelfI-only : ∀ {Φ : Corr Δ Δ′} {X} (m : CMode Φ X ΘL ΘR) {α}
    {σl : Δ ⇒ˢ ΘL} {σs : Δ′ ⇒ˢ ΘR} {T}
  → SelfI m α σl σs → SelfI (CMode-only m) α (T •ˢ σl) σs
SelfI-only (m-pair x α′) h = h
SelfI-only m-left h = h
SelfI-only (m-dead x) h = h
SelfI-only (m-none R rc) h = h

SelfI-dead : ∀ {Φ : Corr Δ Δ′} {X} (m : CMode Φ X ΘL ΘR) {α}
    {σl : Δ ⇒ˢ ΘL} {σs : Δ′ ⇒ˢ ΘR} {T}
  → SelfI m α σl σs → SelfI (CMode-dead m) α (T •ˢ σl) σs

SelfI-dead (m-pair x α′) h = h
SelfI-dead m-left h = h
SelfI-dead (m-dead x) h = h
SelfI-dead (m-none R rc) h = h

------------------------------------------------------------------------
-- The hypotheses under binders
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ} {rk : RK}
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt : Δ′ ⇒ˢ storeR w} {β : TyVar (ΔL w)}
    {l : Leaf (ΔL w) (ΔR w)} where

  -- a paired binder: the new variable is the store variable β on the
  -- left, of store type T′ on the right, with the same leaf on both
  -- sides
  ConvI-extPair : ∀ {m : CMode Φ X (ΔL w) (storeR w)} {α}
      {T′ : Ty (storeR w)}
    → GoodLeaf l → β ≢ α → replaceRC (rconv m σt) T′ ≡ T′
    → ConvLeafP d N w (repM m (δl δt)) (rconv m σt) α l l (＇ β) T′
    → FreshP d rk w l (＇ β) T′
    → ConvI d N rk w m α δs δt σs σt
    → ConvI d N rk w (CMode-pair m) α
        (extPairI (＇ β) (ιT w T′) l δs) (extPairI (＇ β) (ιT w T′) l δt)
        (T′ •ˢ σs) (T′ •ˢ σt)
  goodS (ConvI-extPair {T′ = T′} gl ne tr cv fr h) =
    GoodI-extPairI {T = ＇ β} {T′ = ιT w T′} {δ = δs} gl (goodS h)
  goodT (ConvI-extPair {T′ = T′} gl ne tr cv fr h) =
    GoodI-extPairI {T = ＇ β} {T′ = ιT w T′} {δ = δt} gl (goodT h)
  selfI (ConvI-extPair {m = m} {T′ = T′} gl ne tr cv fr h) =
    SelfI-pair m {T = ＇ β} {T′ = T′} (selfI h)
  rcOK (ConvI-extPair {m = m} {T′ = T′} gl ne tr cv fr h) =
    subst (Allowed rk) (sym (rconv-pair m σt T′)) (rcOK h)
  tyL (ConvI-extPair {m = m} {α} gl ne tr cv fr h) zero =
    subst (λ R → replaceTy α R (＇ β) ≡ ＇ β)
      (sym (repM-pair m (δl δt) (＇ β))) (replaceTy-other _ ne)
  tyL (ConvI-extPair {m = m} {α} gl ne tr cv fr h) (suc Z) =
    subst (λ R → replaceTy α R (δl δs Z) ≡ δl δt Z)
      (sym (repM-pair m (δl δt) (＇ β))) (tyL h Z)
  tyR (ConvI-extPair {m = m} {T′ = T′} gl ne tr cv fr h) zero =
    subst (λ c → replaceRC c T′ ≡ T′) (sym (rconv-pair m σt T′)) tr
  tyR (ConvI-extPair {m = m} {T′ = T′} gl ne tr cv fr h) (suc Y′) =
    subst (λ c → replaceRC c (σs Y′) ≡ σt Y′)
      (sym (rconv-pair m σt T′)) (tyR h Y′)
  rcΣ (ConvI-extPair {m = m} {T′ = T′} gl ne tr cv fr h) =
    subst (RCΣ w) (sym (rconv-pair m σt T′)) (rcΣ h)
  leafO (ConvI-extPair gl ne tr cv fr h) zero o = ≈ˡ-refl
  leafO (ConvI-extPair {m = m} gl ne tr cv fr h) (suc Z) o =
    leafO h Z (Other-pair m Z o)
  convP (ConvI-extPair {m = m} {α} {T′} gl ne tr cv fr h) ↔-here o =
    subst₂ (λ R c → ConvLeafP d N w R c α l l (＇ β) T′)
      (sym (repM-pair m (δl δt) (＇ β))) (sym (rconv-pair m σt T′)) cv
  convP (ConvI-extPair {m = m} {α} {T′} gl ne tr cv fr h)
      {suc Z} {suc Y′} (↔-pair z) o =
    subst₂ (λ R c → ConvLeafP d N w R c α (leaf δs Z) (leaf δt Z)
                      (δl δs Z) (σs Y′))
      (sym (repM-pair m (δl δt) (＇ β))) (sym (rconv-pair m σt T′))
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
  ConvI-extOnly : ∀ {m : CMode Φ X (ΔL w) (storeR w)} {α}
    → GoodLeaf l → β ≢ α
    → ConvLeafO d N w (repM m (δl δt)) α l l (＇ β)
    → FreshO d w l (＇ β)
    → ConvI d N rk w m α δs δt σs σt
    → ConvI d N rk w (CMode-only m) α
        (extOnlyI (＇ β) l δs) (extOnlyI (＇ β) l δt) σs σt
  goodS (ConvI-extOnly gl ne cv fr h) =
    GoodI-extOnlyI {T = ＇ β} {δ = δs} gl (goodS h)
  goodT (ConvI-extOnly gl ne cv fr h) =
    GoodI-extOnlyI {T = ＇ β} {δ = δt} gl (goodT h)
  selfI (ConvI-extOnly {m = m} gl ne cv fr h) =
    SelfI-only m {T = ＇ β} (selfI h)
  rcOK (ConvI-extOnly {m = m} gl ne cv fr h) =
    subst (Allowed rk) (sym (rconv-only m σt)) (rcOK h)
  tyL (ConvI-extOnly {m = m} {α} gl ne cv fr h) zero =
    subst (λ R → replaceTy α R (＇ β) ≡ ＇ β)
      (sym (repM-only m (δl δt) (＇ β))) (replaceTy-other _ ne)
  tyL (ConvI-extOnly {m = m} {α} gl ne cv fr h) (suc Z) =
    subst (λ R → replaceTy α R (δl δs Z) ≡ δl δt Z)
      (sym (repM-only m (δl δt) (＇ β))) (tyL h Z)
  tyR (ConvI-extOnly {m = m} gl ne cv fr h) Y′ =
    subst (λ c → replaceRC c (σs Y′) ≡ σt Y′)
      (sym (rconv-only m σt)) (tyR h Y′)
  rcΣ (ConvI-extOnly {m = m} gl ne cv fr h) =
    subst (RCΣ w) (sym (rconv-only m σt)) (rcΣ h)
  leafO (ConvI-extOnly gl ne cv fr h) zero o = ≈ˡ-refl
  leafO (ConvI-extOnly {m = m} gl ne cv fr h) (suc Z) o =
    leafO h Z (Other-only m Z o)
  convP (ConvI-extOnly {m = m} {α} gl ne cv fr h)
      {suc Z} {Y′} (↔-only z) o =
    subst₂ (λ R c → ConvLeafP d N w R c α (leaf δs Z) (leaf δt Z)
                      (δl δs Z) (σs Y′))
      (sym (repM-only m (δl δt) (＇ β))) (sym (rconv-only m σt))
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
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt : Δ′ ⇒ˢ storeR w} {β : TyVar (ΔL w)}
    where

  -- a dead binder: the new variable occurs nowhere
  ConvI-extDead : ∀ {m : CMode Φ X (ΔL w) (storeR w)} {α} → β ≢ α
    → ConvI d N rk w m α δs δt σs σt
    → ConvI d N rk w (CMode-dead m) α (extDeadI (＇ β) δs)
        (extDeadI (＇ β) δt) σs σt
  goodS (ConvI-extDead ne h) = GoodI-extDeadI {T = ＇ β} {δ = δs} (goodS h)
  goodT (ConvI-extDead ne h) = GoodI-extDeadI {T = ＇ β} {δ = δt} (goodT h)
  selfI (ConvI-extDead {m = m} ne h) =
    SelfI-dead m {T = ＇ β} (selfI h)
  rcOK (ConvI-extDead {m = m} ne h) =
    subst (Allowed rk) (sym (rconv-dead m σt)) (rcOK h)
  tyL (ConvI-extDead {m = m} {α} ne h) zero =
    subst (λ R → replaceTy α R (＇ β) ≡ ＇ β)
      (sym (repM-dead m (δl δt) (＇ β))) (replaceTy-other _ ne)
  tyL (ConvI-extDead {m = m} {α} ne h) (suc Z) =
    subst (λ R → replaceTy α R (δl δs Z) ≡ δl δt Z)
      (sym (repM-dead m (δl δt) (＇ β))) (tyL h Z)
  tyR (ConvI-extDead {m = m} ne h) Y′ =
    subst (λ c → replaceRC c (σs Y′) ≡ σt Y′)
      (sym (rconv-dead m σt)) (tyR h Y′)
  rcΣ (ConvI-extDead {m = m} ne h) =
    subst (RCΣ w) (sym (rconv-dead m σt)) (rcΣ h)
  leafO (ConvI-extDead ne h) zero o = ≈ˡ-refl
  leafO (ConvI-extDead {m = m} ne h) (suc Z) o = leafO h Z (Other-dead m Z o)
  convP (ConvI-extDead {m = m} {α} ne h) {suc Z} {Y′} (↔-dead z) o =
    subst₂ (λ R c → ConvLeafP d N w R c α (leaf δs Z) (leaf δt Z)
                      (δl δs Z) (σs Y′))
      (sym (repM-dead m (δl δt) (＇ β))) (sym (rconv-dead m σt))
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
    {σs σt : Δ′ ⇒ˢ storeR w}
    {α : TyVar (ΔL w)} {m : CMode Φ X (ΔL w) (storeR w)}
    (h : ConvI d N rk w m α δs δt σs σt) where

  private
    ≈s = ↑ᴵ-refl {w = w} δs
    ≈t = ↑ᴵ-refl {w = w} δt

  revP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → Other m Z → ∀ {k} → k ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → leafRel d k w (leaf δs Z) Vl Vr
    → ℰ d k (X⊑Y z) w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ δl δs Z 〗)
        (revM (rconv m σt) (σs Y′) Vr)
  revP {Z} {Y′} z o {k} le {Vl} {Vr} vl vr r =
    ℰL→XY d k z w
      (ℰL-resp d k w (leaf≈ ≈t Z)
        (ℰL-≡ d k w (leaf (δt ↑ᴵ ⊒-refl w) Z)
          (↑〖〗-≡ (toRename-id-eq α) (renameTy-id (repM m (δl δt)))
            (renameTy-id (δl δs Z)))
          (revM-≡ (renRConv-id (rconv m σt)) (renameTy-id (σs Y′)))
          (proj₁ (convP h z o (⊒-refl w) le) vl vr
            (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈s Z)) r))))

  conP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → Other m Z → ∀ {k} → k ≤ N
    → ∀ {Wl Wr} → Value Wl → Value Wr → leafRel d k w (leaf δt Z) Wl Wr
    → ℰ d k (X⊑Y z) w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (δl δs Z))
        (conM (rconv m σt) (σs Y′) Wr)
  conP {Z} {Y′} z o {k} le {Wl} {Wr} wl wr r =
    ℰL→XY d k z w
      (ℰL-resp d k w (leaf≈ ≈s Z)
        (ℰL-≡ d k w (leaf (δs ↑ᴵ ⊒-refl w) Z)
          (↓mc-≡ (toRename-id-eq α) (renameTy-id (repM m (δl δt)))
            (renameTy-id (δl δs Z)))
          (conM-≡ (renRConv-id (rconv m σt)) (renameTy-id (σs Y′)))
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
    {σt : Δ′ ⇒ˢ storeR w} where

  private
    ≈s = ↑ᴵ-refl {w = w} δs
    ≈t = ↑ᴵ-refl {w = w} δt

  pairRev : ∀ {Y} {x : Φ ∋ X ↔ Y} {α′}
    → SealI d N w (m-pair x α′) α δs δt σt → ∀ {k} → 0 < k → k ≤ N
    → ∀ {Vl Vr} → leafRel d k w (leaf δs X) Vl Vr
    → sealedL α (δl δt X) (sealedR α′ (σt Y)
        (leafRel d (pred k) w (leaf δt X))) Vl Vr
  pairRev {Y} {α′ = α′} si {k} pos le r =
    sealedL-map (toRename-id-eq α) (δl≡ ≈t X)
      (sealedR-map (toRename-id-eq α′) (renameTy-id (σt Y))
        (leafRel-resp d (pred k) w (leaf≈ ≈t X)))
      (proj₁ si (⊒-refl w) pos le
        (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈s X)) r))

  pairCon : ∀ {Y} {x : Φ ∋ X ↔ Y} {α′}
    → SealI d N w (m-pair x α′) α δs δt σt → ∀ {k} → 0 < k → k < N
    → ∀ {Wl Wr} → leafRel d k w (leaf δt X) Wl Wr
    → leafRel d k w (leaf δs X)
        (Wl ↓ seal α (δl δt X)) (Wr ↓ seal α′ (σt Y))
  pairCon {Y} {α′ = α′} si {k} pos lt {Wl} {Wr} r =
    leafRel-resp d k w (leaf≈ ≈s X)
      (subst₂ (leafRel d k w (leaf (δs ↑ᴵ ⊒-refl w) X))
        (cong₂ (λ a R → Wl ↓ seal a R) (toRename-id-eq α) (δl≡ ≈t X))
        (cong₂ (λ a R → Wr ↓ seal a R) (toRename-id-eq α′)
          (renameTy-id (σt Y)))
        (proj₂ si (⊒-refl w) pos lt
          (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈t X)) r)))

  leftRev : SealI d N w (m-left {Φ = Φ} {X = X}) α δs δt σt
    → ∀ {k} → 0 < k → k ≤ N
    → ∀ {Vl Vr} → leafRel d k w (leaf δs X) Vl Vr
    → sealedL α (δl δt X) (leafRel d (onlyStage d k) w (leaf δt X)) Vl Vr
  leftRev si {k} pos le r =
    sealedL-map (toRename-id-eq α) (δl≡ ≈t X)
      (leafRel-resp d (onlyStage d k) w (leaf≈ ≈t X))
      (proj₁ si (⊒-refl w) pos le
        (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈s X)) r))

  leftCon : SealI d N w (m-left {Φ = Φ} {X = X}) α δs δt σt

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
rev★-left : ∀ d n {Φ : Corr Δ Δ′} {X} (z : Φ ∋ X only) w {N rk α δs δt σs σt}
  → ConvI d N rk w (m-left {Φ = Φ} {X = X}) α δs δt σs σt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑★ z) w δs Vl Vr
  → ℰ d n (X⊑★ z) w δt (Vl ↑ 〖 α , δl δt X ↑ δl δs X 〗) Vr
rev★-left d zero z w h le vl vr r = ℰ-zero d (X⊑★ z) w
rev★-left d (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt}
    {σt = σt} h le vl vr r
    with sealedL-inv
      (NowX.leftRev {Φ = Φ} {X = X} {d = d} {N = N} {w = w} {δs = δs} {δt = δt}
        {α = α} {σt = σt} (sealI h) (s≤s z≤n) le
        (from (𝒱-X★ d (suc k) z w {δ = δs}) r))
rev★-left ≺ (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt}
    {σt = σt} h le vl vr r
    | W , refl , r′ =
  ℰ-≡ ≺ (suc k) (X⊑★ z) w δt (sym (↑-pk (〖〗-self α (δl δt X) (selfI h))))
    refl
    (ℰ-stepL ≺ k (X⊑★ z) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≺ k (X⊑★ z) w (value-sealed vl) vr
        (to (𝒱-X★ ≺ k z w {δ = δt}) r′)))
rev★-left ≻ (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt}
    {σt = σt} h le vl vr r
    | W , refl , r′ =
  ℰ-≡ ≻ (suc k) (X⊑★ z) w δt (sym (↑-pk (〖〗-self α (δl δt X) (selfI h))))
    refl
    (ℰ-stepL ≻ (suc k) (X⊑★ z) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≻ (suc k) (X⊑★ z) w (value-sealed vl) vr
        (to (𝒱-X★ ≻ (suc k) z w {δ = δt}) r′)))

con★-left : ∀ d n {Φ : Corr Δ Δ′} {X} (z : Φ ∋ X only) w {N rk α δs δt σs σt}
  → ConvI d N rk w (m-left {Φ = Φ} {X = X}) α δs δt σs σt
  → ConB {storeR w} d nothing n N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑★ z) w δt Wl Wr
  → ℰ d n (X⊑★ z) w δs (Wl ↓ makeConceal α (δl δt X) (δl δs X)) Wr
con★-left d zero z w h cb wl wr r = ℰ-zero d (X⊑★ z) w
con★-left ≺ (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt}
    {σt = σt} h cb wl wr r =
  ℰ-≡ ≺ (suc k) (X⊑★ z) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (selfI h)))) refl
    (ℰ-value ≺ (suc k) (X⊑★ z) w (wl CT.↓ CT.seal) wr
      (to (𝒱-X★ ≺ (suc k) z w {δ = δs})
        (NowX.leftCon {Φ = Φ} {X = X} {d = ≺} {N = N} {w = w} {δs = δs}
          {δt = δt}
          {α = α} {σt = σt} (sealI h) (s≤s z≤n) cb
          (from (𝒱-X★ ≺ (suc k) z w {δ = δt}) r))))
con★-left ≻ (suc k) {Φ = Φ} {X = X} z w {N} {α = α} {δs} {δt}
    {σt = σt} h cb wl wr r =
  ℰ-≡ ≻ (suc k) (X⊑★ z) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (selfI h)))) refl
    (ℰ-value ≻ (suc k) (X⊑★ z) w (wl CT.↓ CT.seal) wr
      (to (𝒱-X★ ≻ (suc k) z w {δ = δs})
        (NowX.leftCon {Φ = Φ} {X = X} {d = ≻} {N = N} {w = w} {δs = δs}
          {δt = δt}
          {α = α} {σt = σt} (sealI h) (s≤s z≤n) cb
          (from (𝒱-X★ ≻ (suc k) z w {δ = δt}) r))))

-- a left-only variable, at `★`
rev★-var : ∀ d n {Φ : Corr Δ Δ′} {Z} (z : Φ ∋ Z only) w {X} {N rk}
    {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
  → ConvI d N rk w m α δs δt σs σt → n ≤ N
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
    {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
  → ConvI d N rk w m α δs δt σs σt → n ≤ N → ConM d m nothing n N
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
rev-pairX : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w
    {N rk α α′ δs δt σs σt}
  → ConvI d N rk w (m-pair x α′) α δs δt σs σt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑Y x) w δs Vl Vr
  → ℰ d n (X⊑Y x) w δt (Vl ↑ 〖 α , δl δt X ↑ δl δs X 〗)
      (Vr ↑ 〖 α′ , σt Y ↑ σs Y 〗)
rev-pairX d zero x w h le vl vr r = ℰ-zero d (X⊑Y x) w
rev-pairX d (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt}
    {σt = σt} h le vl vr r
    with sealedL-inv
      (NowX.pairRev {Φ = Φ} {X = X} {d = d} {N = N} {w = w} {δs = δs}
        {δt = δt} {α = α} {σt = σt} {x = x} {α′ = α′} (sealI h) (s≤s z≤n) le
        (from (𝒱-XY d (suc k) x w {δ = δs}) r))
rev-pairX d (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt}
    {σt = σt} h le vl vr r
    | W , refl , s′ with sealedR-inv s′
rev-pairX ≺ (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt}
    {σt = σt} h le vl vr r
    | W , refl , s′ | W′ , refl , r′ =
  ℰ-≡ ≺ (suc k) (X⊑Y x) w δt
    (sym (↑-pk (〖〗-self α (δl δt X) (proj₁ (selfI h)))))
    (sym (↑-pk (〖〗-self α′ (σt Y) (proj₂ (selfI h)))))
    (ℰ-stepL ≺ k (X⊑Y x) w (conceal-reveal (value-sealed vl))
      (ℰ-stepR ≺ k (X⊑Y x) w (conceal-reveal (value-sealed vr))
        (ℰ-value ≺ k (X⊑Y x) w (value-sealed vl) (value-sealed vr)
          (to (𝒱-XY ≺ k x w {δ = δt}) r′))))
rev-pairX ≻ (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt}
    {σt = σt} h le vl vr r
    | W , refl , s′ | W′ , refl , r′ =
  ℰ-≡ ≻ (suc k) (X⊑Y x) w δt
    (sym (↑-pk (〖〗-self α (δl δt X) (proj₁ (selfI h)))))
    (sym (↑-pk (〖〗-self α′ (σt Y) (proj₂ (selfI h)))))
    (ℰ-stepL ≻ (suc k) (X⊑Y x) w (conceal-reveal (value-sealed vl))
      (ℰ-stepR ≻ k (X⊑Y x) w (conceal-reveal (value-sealed vr))
        (ℰ-value ≻ k (X⊑Y x) w (value-sealed vl) (value-sealed vr)
          (to (𝒱-XY ≻ k x w {δ = δt}) r′))))

con-pairX : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w
    {N rk α α′ δs δt σs σt}
  → ConvI d N rk w (m-pair x α′) α δs δt σs σt → n < N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑Y x) w δt Wl Wr
  → ℰ d n (X⊑Y x) w δs (Wl ↓ makeConceal α (δl δt X) (δl δs X))
      (Wr ↓ makeConceal α′ (σt Y) (σs Y))
con-pairX d zero x w h lt wl wr r = ℰ-zero d (X⊑Y x) w
con-pairX d (suc k) {Φ} {X} {Y} x w {N} {α = α} {α′} {δs} {δt}
    {σt = σt} h lt wl wr r =
  ℰ-≡ d (suc k) (X⊑Y x) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (proj₁ (selfI h)))))
    (sym (↓-pk (makeConceal-self α′ (σt Y) (proj₂ (selfI h)))))
    (ℰ-value d (suc k) (X⊑Y x) w (wl CT.↓ CT.seal) (wr CT.↓ CT.seal)
      (to (𝒱-XY d (suc k) x w {δ = δs})
        (NowX.pairCon {Φ = Φ} {X = X} {d = d} {N = N} {w = w} {δs = δs}
          {δt = δt} {α = α} {σt = σt} {x = x} {α′ = α′} (sealI h) (s≤s z≤n) lt
          (from (𝒱-XY d (suc k) x w {δ = δt}) r))))

-- X itself, paired, only the left converting
rev-leftX : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w {N rk α δs δt σs σt}
  → ConvI d N rk w (m-left {Φ = Φ} {X = X}) α δs δt σs σt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑Y x) w δs Vl Vr
  → ℰ d n (X⊑Y x) w δt (Vl ↑ 〖 α , δl δt X ↑ δl δs X 〗) Vr
rev-leftX d zero x w h le vl vr r = ℰ-zero d (X⊑Y x) w
rev-leftX d (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt}
    {σt = σt} h le vl vr r
    with sealedL-inv
      (NowX.leftRev {Φ = Φ} {X = X} {d = d} {N = N} {w = w} {δs = δs}
        {δt = δt} {α = α} {σt = σt} (sealI h) (s≤s z≤n) le
        (from (𝒱-XY d (suc k) x w {δ = δs}) r))
rev-leftX ≺ (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt}
    {σt = σt} h le vl vr r
    | W , refl , r′ =
  ℰ-≡ ≺ (suc k) (X⊑Y x) w δt
    (sym (↑-pk (〖〗-self α (δl δt X) (selfI h)))) refl
    (ℰ-stepL ≺ k (X⊑Y x) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≺ k (X⊑Y x) w (value-sealed vl) vr
        (to (𝒱-XY ≺ k x w {δ = δt}) r′)))
rev-leftX ≻ (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt}
    {σt = σt} h le vl vr r
    | W , refl , r′ =
  ℰ-≡ ≻ (suc k) (X⊑Y x) w δt
    (sym (↑-pk (〖〗-self α (δl δt X) (selfI h)))) refl
    (ℰ-stepL ≻ (suc k) (X⊑Y x) w (conceal-reveal (value-sealed vl))
      (ℰ-value ≻ (suc k) (X⊑Y x) w (value-sealed vl) vr
        (to (𝒱-XY ≻ (suc k) x w {δ = δt}) r′)))

con-leftX : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w {N rk α δs δt σs σt}
  → ConvI d N rk w (m-left {Φ = Φ} {X = X}) α δs δt σs σt
  → ConB {storeR w} d nothing n N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑Y x) w δt Wl Wr
  → ℰ d n (X⊑Y x) w δs (Wl ↓ makeConceal α (δl δt X) (δl δs X)) Wr
con-leftX d zero x w h cb wl wr r = ℰ-zero d (X⊑Y x) w
con-leftX ≺ (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt}
    {σt = σt} h cb wl wr r =
  ℰ-≡ ≺ (suc k) (X⊑Y x) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (selfI h)))) refl
    (ℰ-value ≺ (suc k) (X⊑Y x) w (wl CT.↓ CT.seal) wr
      (to (𝒱-XY ≺ (suc k) x w {δ = δs})
        (NowX.leftCon {Φ = Φ} {X = X} {d = ≺} {N = N} {w = w} {δs = δs}
          {δt = δt} {α = α} {σt = σt} (sealI h) (s≤s z≤n) cb
          (from (𝒱-XY ≺ (suc k) x w {δ = δt}) r))))
con-leftX ≻ (suc k) {Φ} {X} {Y} x w {N} {α = α} {δs} {δt}
    {σt = σt} h cb wl wr r =
  ℰ-≡ ≻ (suc k) (X⊑Y x) w δs
    (sym (↓-pk (makeConceal-self α (δl δt X) (selfI h)))) refl
    (ℰ-value ≻ (suc k) (X⊑Y x) w (wl CT.↓ CT.seal) wr
      (to (𝒱-XY ≻ (suc k) x w {δ = δs})
        (NowX.leftCon {Φ = Φ} {X = X} {d = ≻} {N = N} {w = w} {δs = δs}
          {δt = δt} {α = α} {σt = σt} (sealI h) (s≤s z≤n) cb
          (from (𝒱-XY ≻ (suc k) x w {δ = δt}) r))))

-- a paired variable
rev-var : ∀ d n {Φ : Corr Δ Δ′} {Z Y′} (z : Φ ∋ Z ↔ Y′) w {X} {N rk}
    {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
  → ConvI d N rk w m α δs δt σs σt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑Y z) w δs Vl Vr
  → ℰ d n (X⊑Y z) w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ δl δs Z 〗)
      (revM (rconv m σt) (σs Y′) Vr)
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
    {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
  → ConvI d N rk w m α δs δt σs σt → n ≤ N → ConM d m (rconv m σt) n N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑Y z) w δt Wl Wr
  → ℰ d n (X⊑Y z) w δs (Wl ↓ makeConceal α (repM m (δl δt)) (δl δs Z))
      (conM (rconv m σt) (σs Y′) Wr)
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
    (revp : ∀ {w m α δs δt σs σt} → ConvI d N rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt A′
       → ∀ {k} → k ≤ N
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (RF m σt) (substᵗ σs A′) Vr))
    (conp : ∀ {w m α δs δt σs σt} → ConvI d N rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt A′
       → ∀ {k} → ConM d m (RF m σt) k N
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (RF m σt) (substᵗ σs A′) Wr))
    (revq : ∀ {w m α δs δt σs σt} → ConvI d N rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt B′
       → ∀ {k} → k ≤ N
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k q w δs Vl Vr
       → ℰ d k q w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) B 〗)
           (revM (RF m σt) (substᵗ σs B′) Vr))
    (conq : ∀ {w m α δs δt σs σt} → ConvI d N rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt B′
       → ∀ {k} → ConM d m (RF m σt) k N
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k q w δt Wl Wr
       → ℰ d k q w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) B))
           (conM (RF m σt) (substᵗ σs B′) Wr))
    (revT : ∀ {w m α δs δt σs σt} → ConvI d N rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt A′
       → ∀ {V} → Typedᴿ w (substᵗ (δr δs) A′) V
       → Typedᴿ w (substᵗ (δr δt) A′) (revM (RF m σt) (substᵗ σs A′) V))
    (conT : ∀ {w m α δs δt σs σt} → ConvI d N rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt A′
       → ∀ {V} → Typedᴿ w (substᵗ (δr δt) A′) V
       → Typedᴿ w (substᵗ (δr δs) A′) (conM (RF m σt) (substᵗ σs A′) V))
    where

  -- the conversion of a result, renamed into a future
  private
    rev-ren : ∀ {w w′} (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (storeR w)) α
        (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔL w′)) C
      → Q ↑ 〖 toRenameᵗ (ρL e) α
            , repM (CMode-↑ (ρL e) (ρS e) m) (δl (δt ↑ᴵ e))
            ↑ substᵗ (δl (δs ↑ᴵ e)) C 〗
        ≡ Q ↑ rename↑ (toRenameᵗ (ρL e))
              〖 α , repM m (δl δt) ↑ substᵗ (δl δs) C 〗
    rev-ren e m α δs δt Q C =
      trans (↑〖〗-≡ refl (repM-↑ (ρL e) (ρS e) m (δl δt)) refl)
        (sym (↑-pk (〖〗-ren (ρL e) α (repM m (δl δt)) (δl δs) C)))

    con-ren : ∀ {w w′} (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (storeR w)) α
        (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔL w′)) C
      → Q ↓ makeConceal (toRenameᵗ (ρL e) α)
              (repM (CMode-↑ (ρL e) (ρS e) m) (δl (δt ↑ᴵ e)))
              (substᵗ (δl (δs ↑ᴵ e)) C)
        ≡ Q ↓ rename↓ (toRenameᵗ (ρL e))
              (makeConceal α (repM m (δl δt)) (substᵗ (δl δs) C))
    con-ren e m α δs δt Q C =
      trans (↓mc-≡ refl (repM-↑ (ρL e) (ρS e) m (δl δt)) refl)
        (sym (↓-pk (makeConceal-ren (ρL e) α (repM m (δl δt)) (δl δs) C)))

    rc-ren : ∀ {w w′} (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (storeR w))
        (σs σt : Δ′ ⇒ˢ storeR w) (Q : Term (storeR w′)) C
      → revM (RF (CMode-↑ (ρL e) (ρS e) m) (σt ↑ˢ e))
          (substᵗ (σs ↑ˢ e) C) Q
        ≡ mplug (renameMFrame (ρS e)
            (revFrame (RF m σt) (substᵗ σs C))) Q
    rc-ren e m σs σt Q C =
      trans (cong (λ c → revM c _ Q) (RF-↑ (ρL e) (ρS e) m σt))
        (sym (revFrame-ren (ρS e) (RF m σt) σs C Q))

    cc-ren : ∀ {w w′} (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (storeR w))
        (σs σt : Δ′ ⇒ˢ storeR w) (Q : Term (storeR w′)) C
      → conM (RF (CMode-↑ (ρL e) (ρS e) m) (σt ↑ˢ e))
          (substᵗ (σs ↑ˢ e) C) Q
        ≡ mplug (renameMFrame (ρS e)
            (conFrame (RF m σt) (substᵗ σs C))) Q
    cc-ren e m σs σt Q C =
      trans (cong (λ c → conM c _ Q) (RF-↑ (ρL e) (ρS e) m σt))
        (sym (conFrame-ren (ρS e) (RF m σt) σs C Q))

  -- a converted function applied, in the world of the function
  rev-at : ∀ {n} w {m α δs δt σs σt}
      (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (RF m σt) δs δt σs σt (A′ ⇒ B′) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → funRel d n p q w δs Vl Vr
    → ∀ {Ul Ur} → Value Ul → Value Ur → 𝒱 d n p w δt Ul Ur
    → Typedᴿ w (substᵗ (δr δt) A′) Ur
    → ℰ d n q w δt
        ((Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (A ⇒ B) 〗) · Ul)
        (revM (RF m σt) (substᵗ σs (A′ ⇒ B′)) Vr · Ur)
  rev-at w {m} {α} {δs} {δt} {σs} {σt} h ps le {Vl} {Vr} vl vr f {Ul} {Ur}
      ul ur a tU =
    ℰ-app-steps d q w (RF m σt) le (β-reveal-⇒ vl ul)
      (rightApp (RF m σt) vr ur)
      (λ {s} s≤n cb →
        app-core d s p q w vl vr
          (just (reveal 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) B 〗))
          (revFrame (RF m σt) (substᵗ σs B′))
          (conT h (PreM-⇒₁ ps) tU)
          (conp h (PreM-⇒₁ ps) (ConB→ConMb d (isNone m) (RF m σt) cb)
            ul ur (𝒱-down d s≤n p w (goodT h) a))
          (funRel-down d s≤n p q w f)
          (λ e₂ {k} k≤s {Ql} {Qr} ql qr r →
            ℰᵍ-≡ (rev-ren e₂ m α δs δt Ql B) (rc-ren e₂ m σs σt Qr B′)
              (revq (ConvI-↑ e₂ h)
                (PreM-↑ (PreM-⇒₂ ps) e₂ (RF-↑ (ρL e₂) (ρS e₂) m σt))
                (≤-trans k≤s (≤-trans s≤n le)) ql qr r)))

  con-at : ∀ {n} w {m α δs δt σs σt} (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (RF m σt) δs δt σs σt (A′ ⇒ B′) → ConM d m (RF m σt) n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → funRel d n p q w δt Wl Wr
    → ∀ {Ul Ur} → Value Ul → Value Ur → 𝒱 d n p w δs Ul Ur
    → Typedᴿ w (substᵗ (δr δs) A′) Ur
    → ℰ d n q w δs
        ((Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (A ⇒ B)))
          · Ul)
        (conM (RF m σt) (substᵗ σs (A′ ⇒ B′)) Wr · Ur)
  con-at w {m} {α} {δs} {δt} {σs} {σt} h ps cb {Wl} {Wr} wl wr f {Ul} {Ur}
      ul ur a tU =
    ℰ-app-steps d q w (RF m σt) (ConMb-≤ d (isNone m) (RF m σt) cb)
      (β-conceal-⇒ wl ul) (rightAppC (RF m σt) wr ur)
      (λ {s} s≤n cb′ →
        app-core d s p q w wl wr
          (just (conceal
            (makeConceal α (repM m (δl δt)) (substᵗ (δl δs) B))))
          (conFrame (RF m σt) (substᵗ σs B′))
          (revT h (PreM-⇒₁ ps) tU)
          (revp h (PreM-⇒₁ ps)
            (≤-trans s≤n (ConMb-≤ d (isNone m) (RF m σt) cb)) ul ur
            (𝒱-down d s≤n p w (goodS h) a))
          (funRel-down d s≤n p q w f)
          (λ e₂ {k} k≤s {Ql} {Qr} ql qr r →
            ℰᵍ-≡ (con-ren e₂ m α δs δt Ql B) (cc-ren e₂ m σs σt Qr B′)
              (conq (ConvI-↑ e₂ h)
                (PreM-↑ (PreM-⇒₂ ps) e₂ (RF-↑ (ρL e₂) (ρS e₂) m σt))
                (ConM-↑ d (ρL e₂) (ρS e₂) m (RF-↑ (ρL e₂) (ρS e₂) m σt)
                  (≤-trans k≤s s≤n) cb)
                ql qr r)))

  fun-rev : ∀ {n w m α δs δt σs σt} (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (RF m σt) δs δt σs σt (A′ ⇒ B′) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → funRel d n p q w δs Vl Vr
    → funRel d n p q w δt
        (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (A ⇒ B) 〗)
        (revM (RF m σt) (substᵗ σs (A′ ⇒ B′)) Vr)
  fun-rev {n} {w} {m} {α} {δs} {δt} {σs} {σt} h ps le {Vl} {Vr} vl vr f
      {w′} e {n′} le′ Ul Ur ul ur a tU =
    ℰᵍ-map d n′ w′ (λ le″ w″ e″ V V′ → 𝒱≤-cast d le″ (≤′-trans le″ le′) q w″)
      (ℰᵍ-≡
        (cong (_· Ul) (rev-ren e m α δs δt (renameᵗᵐ (ρL e) Vl) (A ⇒ B)))
        (cong (_· Ur) (trans
          (cong (λ c → revM c _ (renameᵗᵐ (ρS e) Vr))
            (RF-↑ (ρL e) (ρS e) m σt))
          (sym (revM-ren (ρS e) (RF m σt) σs (A′ ⇒ B′) Vr))))
        (rev-at w′ (ConvI-↑ e h) (PreM-↑ ps e (RF-↑ (ρL e) (ρS e) m σt))
          (≤-trans (≤′⇒≤ le′) le)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (renameᵗᵐ-preserves-Value (ρS e) vr)
          (funRel-down d (≤′⇒≤ le′) p q w′ (funRel-mono d n p q e f))
          ul ur (𝒱≤-cast d le′ ≤′-refl p w′ a) tU))

  fun-con : ∀ {n w m α δs δt σs σt} (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (RF m σt) δs δt σs σt (A′ ⇒ B′) → ConM d m (RF m σt) n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → funRel d n p q w δt Wl Wr
    → funRel d n p q w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (A ⇒ B)))
        (conM (RF m σt) (substᵗ σs (A′ ⇒ B′)) Wr)
  fun-con {n} {w} {m} {α} {δs} {δt} {σs} {σt} h ps cb {Wl} {Wr} wl wr f
      {w′} e {n′} le′ Ul Ur ul ur a tU =
    ℰᵍ-map d n′ w′ (λ le″ w″ e″ V V′ → 𝒱≤-cast d le″ (≤′-trans le″ le′) q w″)
      (ℰᵍ-≡
        (cong (_· Ul) (con-ren e m α δs δt (renameᵗᵐ (ρL e) Wl) (A ⇒ B)))
        (cong (_· Ur) (trans
          (cong (λ c → conM c _ (renameᵗᵐ (ρS e) Wr))
            (RF-↑ (ρL e) (ρS e) m σt))
          (sym (conM-ren (ρS e) (RF m σt) σs (A′ ⇒ B′) Wr))))
        (con-at w′ (ConvI-↑ e h) (PreM-↑ ps e (RF-↑ (ρL e) (ρS e) m σt))
          (ConM-↑ d (ρL e) (ρS e) m (RF-↑ (ρL e) (ρS e) m σt)
            (≤′⇒≤ le′) cb)
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (renameᵗᵐ-preserves-Value (ρS e) wr)
          (funRel-down d (≤′⇒≤ le′) p q w′ (funRel-mono d n p q e f))
          ul ur (𝒱≤-cast d le′ ≤′-refl p w′ a) tU))

------------------------------------------------------------------------
-- When the right does not convert
------------------------------------------------------------------------

FreshP-left : ∀ {d rk w L T T′} → FreshP d rk w L T T′
  → FreshP d left w L T T′
FreshP-left {rk = both} f e rc ok nb nrc rs = f e rc tt nb nrc rs
FreshP-left {rk = left} f = f

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ} {rk : RK}
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt : Δ′ ⇒ˢ storeR w} where

  ConvI-left : ∀ {m : CMode Φ X (ΔL w) (storeR w)} {α}
    → rconv m σt ≡ nothing
    → ConvI d N rk w m α δs δt σs σt → ConvI d N left w m α δs δt σs σt
  goodS (ConvI-left eq h) = goodS h
  goodT (ConvI-left eq h) = goodT h
  selfI (ConvI-left eq h) = selfI h
  rcOK (ConvI-left eq h) = subst (Allowed left) (sym eq) tt
  tyL (ConvI-left eq h) = tyL h
  tyR (ConvI-left eq h) = tyR h
  rcΣ (ConvI-left eq h) = rcΣ h
  leafO (ConvI-left eq h) = leafO h
  convP (ConvI-left eq h) = convP h
  convO (ConvI-left eq h) = convO h
  genP (ConvI-left eq h) {Z} {Y′} z =
    FreshP-left {d = d} {rk = rk} {w = w} {L = leaf δt Z} {T = δl δt Z}
      {T′ = σt Y′} (genP h z)
  genO (ConvI-left eq h) = genO h
  genPS (ConvI-left eq h) {Z} {Y′} z =
    FreshP-left {d = d} {rk = rk} {w = w} {L = leaf δs Z} {T = δl δs Z}
      {T′ = σs Y′} (genPS h z)
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

-- an allocation binds the new store variable to its type
bind-Σ : ∀ {Θ} (Σ : TyStore.TyStore Θ) (T : Ty Θ)
  → applyStores (bind T ∷ []) Σ
      ∋Σ zero ⦂ renameᵗ (toRenameᵗ (embedᶜˢ (bind T ∷ []))) T
bind-Σ Σ T =
  TyStore.Z∋ (trans (cong (λ ρ → renameᵗ (toRenameᵗ ρ) T) (embed-bind T))
    (renameᵗ-wk-eq T))

-- a tag for a new store variable; it is never read here
newTag : ∀ {ΘL ΘR} → Tag (suc ΘL) ΘR
newTag = nothing , seals zero [] [] (desc (★⊑★ {Φ = []}) []ᵛ []ᵛ)

-- the left allocates; the right scope and store stay
tagsL : (w : World) → TyVar (suc (ΔL w)) → Tag (suc (ΔL w)) (ΔR w)
tagsL w zero = newTag
tagsL w (suc X) = renameTag wk↪ᵗ id↪ᵗ (tag w X)

okBindL : ∀ (w : World) (T : Ty (ΔL w)) X
  → tagsL w (toRenameᵗ (embedᶜˢ (bind T ∷ [])) X)
    ≡ renameTag (embedᶜˢ (bind T ∷ [])) id↪ᵗ (tag w X)
okBindL w T X =
  trans (cong (tagsL w) (embed-var T X))
    (sym (cong (λ ρ → renameTag ρ id↪ᵗ (tag w X)) (embed-bind T)))

worldL : World → World
worldL w =
  mkWorld (suc (ΔL w)) (ΔR w) (tagsL w) (storeR w) (pre w) (ΣR w)

extL : ∀ (w : World) (T : Ty (ΔL w)) → worldL w ⊒ w
extL w T =
  stepExt {w = w} (bind T ∷ []) [] (done refl) (tagsL w) (okBindL w T)

-- the right allocates in its store: it takes the oldest reserved scope
-- variable, or extends the scope (`step1`); the new scope, the store's
-- place in it, and the old scope's embedding
ΔRᴬ : (w : World) → Ty (storeR w) → TyCtx
ΔRᴬ w A = proj₁ (step1 (pre w) (bind A))

preᴬ : (w : World) (A : Ty (storeR w)) → Prefix (suc (storeR w)) (ΔRᴬ w A)
preᴬ w A = proj₁ (proj₂ (step1 (pre w) (bind A)))

ρᴬ : (w : World) (A : Ty (storeR w)) → ΔR w ↪ᵗ ΔRᴬ w A
ρᴬ w A = proj₁ (proj₂ (proj₂ (step1 (pre w) (bind A))))

stᴬ : (w : World) (A : Ty (storeR w))
  → Steps (pre w) (bind A ∷ []) (preᴬ w A) (ρᴬ w A)
stᴬ w A =
  more (proj₂ (proj₂ (proj₂ (step1 (pre w) (bind A))))) (done refl)
    (sym (∘↪-idˡ (ρᴬ w A)))

-- both allocate
tagsLR : (w : World) (A : Ty (storeR w)) → TyVar (suc (ΔL w))
  → Tag (suc (ΔL w)) (ΔRᴬ w A)
tagsLR w A zero = newTag
tagsLR w A (suc X) = renameTag wk↪ᵗ (ρᴬ w A) (tag w X)

okBindLR : ∀ (w : World) (T : Ty (ΔL w)) (A : Ty (storeR w)) X
  → tagsLR w A (toRenameᵗ (embedᶜˢ (bind T ∷ [])) X)
    ≡ renameTag (embedᶜˢ (bind T ∷ [])) (ρᴬ w A) (tag w X)
okBindLR w T A X =
  trans (cong (tagsLR w A) (embed-var T X))
    (sym (cong (λ ρ → renameTag ρ (ρᴬ w A) (tag w X)) (embed-bind T)))

worldLR : (w : World) → Ty (storeR w) → World
worldLR w A =
  mkWorld (suc (ΔL w)) (ΔRᴬ w A) (tagsLR w A) (suc (storeR w)) (preᴬ w A)
    (applyStores (bind A ∷ []) (ΣR w))

extLR : ∀ (w : World) (T : Ty (ΔL w)) (A : Ty (storeR w))
  → worldLR w A ⊒ w
extLR w T A =
  stepExt {w = w} (bind T ∷ []) (bind A ∷ []) (stᴬ w A) (tagsLR w A)
    (okBindLR w T A)


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

-- a right store value sealed at the scope variable Y, read through ι
sealedRᴿ : ∀ {Θ} → Θ ↪ᵗ ΘR → TyVar ΘR → Ty ΘR
  → (Term ΘL → Term Θ → Set) → Term ΘL → Term Θ → Set
sealedRᴿ ι Y R P Vl (W ↓ s) = IsSealᴿ ι Y R s × P Vl W
sealedRᴿ ι Y R P Vl Vr = ⊥

sealedRᴿ-inv : ∀ {Θ} {ι : Θ ↪ᵗ ΘR} {Y R} {P : Term ΘL → Term Θ → Set}
    {Vl Vr}
  → sealedRᴿ ι Y R P Vl Vr
  → Σ[ W ∈ Term Θ ] Σ[ Y′ ∈ TyVar Θ ] Σ[ R′ ∈ Ty Θ ]
      (Vr ≡ W ↓ seal Y′ R′ × IsSealᴿ ι Y R (seal Y′ R′) × P Vl W)
sealedRᴿ-inv {Vr = W ↓ seal X R′} (is , r) = W , X , R′ , refl , is , r
sealedRᴿ-inv {Vr = W ↓ (c ↦↓ d)} (() , r)
sealedRᴿ-inv {Vr = W ↓ (`∀↓ c)} (() , r)
sealedRᴿ-inv {Vr = W ↓ id↓ A} (() , r)
sealedRᴿ-inv {Vr = ` x} ()
sealedRᴿ-inv {Vr = ƛ M} ()
sealedRᴿ-inv {Vr = L · M} ()
sealedRᴿ-inv {Vr = Λ M} ()
sealedRᴿ-inv {Vr = L ⦂∀ C [ T ]} ()
sealedRᴿ-inv {Vr = $ κ} ()
sealedRᴿ-inv {Vr = L ⊕[ op ] M} ()
sealedRᴿ-inv {Vr = W ⟨ c ⟩} ()
sealedRᴿ-inv {Vr = M ↑ c} ()
sealedRᴿ-inv {Vr = blame} ()

-- at an embedded store variable and type, it is a store seal
sealedRᴿ→ : ∀ {Θ} (ι : Θ ↪ᵗ ΘR) {α : TyVar Θ} {R₀}
    {P : Term ΘL → Term Θ → Set} {Vl Vr}
  → sealedRᴿ ι (toRenameᵗ ι α) (renameᵗ (toRenameᵗ ι) R₀) P Vl Vr
  → sealedR α R₀ P Vl Vr
sealedRᴿ→ ι r with sealedRᴿ-inv r
sealedRᴿ→ ι r | W , Y′ , R′ , refl , (eY , eR) , q =
  (toRenameᵗ-injective ι eY ,
   renameᵗ-injective (toRenameᵗ-injective ι) eR) , q

sealedRᴿ← : ∀ {Θ} (ι : Θ ↪ᵗ ΘR) {α : TyVar Θ} {R₀}
    {P : Term ΘL → Term Θ → Set} {Vl Vr}
  → sealedR α R₀ P Vl Vr
  → sealedRᴿ ι (toRenameᵗ ι α) (renameᵗ (toRenameᵗ ι) R₀) P Vl Vr
sealedRᴿ← ι r with sealedR-inv r
sealedRᴿ← ι r | W , refl , q = (refl , refl) , q

sealedRᴿ-map : ∀ {Θ} {ι : Θ ↪ᵗ ΘR} {Y Y′ R R′}
    {P P′ : Term ΘL → Term Θ → Set} {Vl Vr}
  → Y ≡ Y′ → R ≡ R′ → (∀ {W V} → P W V → P′ W V)
  → sealedRᴿ ι Y R P Vl Vr → sealedRᴿ ι Y′ R′ P′ Vl Vr
sealedRᴿ-map refl refl f r with sealedRᴿ-inv r
sealedRᴿ-map refl refl f r | W , Y₀ , R₀ , refl , is , q = is , f q


-- peeling a right seal is a sealed right value
peelSR→ : ∀ {Θ} {ι : Θ ↪ᵗ ΘR} {Y : TyVar ΘR} {Ys} {c : Desc ΘL ΘR} {P V V′}
  → peelSR ι (Y ∷ Ys) c P V V′
  → sealedRᴿ ι Y (repR Ys c) (peelSR ι Ys c P) V V′
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

peelSR← : ∀ {Θ} {ι : Θ ↪ᵗ ΘR} {Y : TyVar ΘR} {Ys} {c : Desc ΘL ΘR} {P V V′}
  → sealedRᴿ ι Y (repR Ys c) (peelSR ι Ys c P) V V′
  → peelSR ι (Y ∷ Ys) c P V V′
peelSR← r with sealedRᴿ-inv r
peelSR← r | W′ , Y′ , R′ , refl , q = r

-- a right seal commutes with peeling left seals
peelSL-sealedR : ∀ {Θ} (ι : Θ ↪ᵗ ΘR) (Xs : List (TyVar ΘL))
    (c : Desc ΘL ΘR) {β : TyVar ΘR} {R} {P : Term ΘL → Term Θ → Set} {V V′}
  → peelSL Xs c (sealedRᴿ ι β R P) V V′
  → sealedRᴿ ι β R (peelSL Xs c P) V V′
peelSL-sealedR ι [] c r = r
peelSL-sealedR ι (X ∷ Xs) c {V = V ↓ s} (is , r)
    with sealedRᴿ-inv (peelSL-sealedR ι Xs c r)
peelSL-sealedR ι (X ∷ Xs) c {V = V ↓ s} (is , r)
    | W′ , Y′ , R′ , refl , is′ , q =
  is′ , is , q
peelSL-sealedR ι (X ∷ Xs) c {V = ` x₀} ()
peelSL-sealedR ι (X ∷ Xs) c {V = ƛ M₀} ()
peelSL-sealedR ι (X ∷ Xs) c {V = L₀ · M₀} ()
peelSL-sealedR ι (X ∷ Xs) c {V = Λ M₀} ()
peelSL-sealedR ι (X ∷ Xs) c {V = L₀ ⦂∀ C₀ [ T₀ ]} ()
peelSL-sealedR ι (X ∷ Xs) c {V = $ κ₀} ()
peelSL-sealedR ι (X ∷ Xs) c {V = L₀ ⊕[ op₀ ] M₀} ()
peelSL-sealedR ι (X ∷ Xs) c {V = W₀ ⟨ c₀ ⟩} ()
peelSL-sealedR ι (X ∷ Xs) c {V = M₀ ↑ c₀} ()
peelSL-sealedR ι (X ∷ Xs) c {V = blame} ()

sealedR-peelSL : ∀ {Θ} (ι : Θ ↪ᵗ ΘR) (Xs : List (TyVar ΘL))
    (c : Desc ΘL ΘR) {β : TyVar ΘR} {R} {P : Term ΘL → Term Θ → Set} {V V′}
  → sealedRᴿ ι β R (peelSL Xs c P) V V′
  → peelSL Xs c (sealedRᴿ ι β R P) V V′
sealedR-peelSL ι [] c r = r
sealedR-peelSL ι (X ∷ Xs) c {V = V} r with sealedRᴿ-inv r
sealedR-peelSL ι (X ∷ Xs) c {V = V ↓ s} r
    | W′ , Y′ , R′ , refl , is′ , (is , q) =
  is , sealedR-peelSL ι Xs c (is′ , q)
sealedR-peelSL ι (X ∷ Xs) c {V = ` x₀} r | W′ , Y′ , R′ , refl , is′ , ()
sealedR-peelSL ι (X ∷ Xs) c {V = ƛ M₀} r | W′ , Y′ , R′ , refl , is′ , ()
sealedR-peelSL ι (X ∷ Xs) c {V = L₀ · M₀} r
    | W′ , Y′ , R′ , refl , is′ , ()
sealedR-peelSL ι (X ∷ Xs) c {V = Λ M₀} r | W′ , Y′ , R′ , refl , is′ , ()
sealedR-peelSL ι (X ∷ Xs) c {V = L₀ ⦂∀ C₀ [ T₀ ]} r
    | W′ , Y′ , R′ , refl , is′ , ()
sealedR-peelSL ι (X ∷ Xs) c {V = $ κ₀} r | W′ , Y′ , R′ , refl , is′ , ()
sealedR-peelSL ι (X ∷ Xs) c {V = L₀ ⊕[ op₀ ] M₀} r
    | W′ , Y′ , R′ , refl , is′ , ()
sealedR-peelSL ι (X ∷ Xs) c {V = W₀ ⟨ c₀ ⟩} r
    | W′ , Y′ , R′ , refl , is′ , ()
sealedR-peelSL ι (X ∷ Xs) c {V = M₀ ↑ c₀} r
    | W′ , Y′ , R′ , refl , is′ , ()
sealedR-peelSL ι (X ∷ Xs) c {V = blame} r
    | W′ , Y′ , R′ , refl , is′ , ()

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
        (sealedRᴿ (ιʷ w) (renameVar τR β′) (repR Ys′ c′)
          (leafBelowS d le (sdesc Xs Ys c) k w τL τR)) V V′
  sealS→ {V = V ↓ s} (is , r) =
    is , peelSL-sealedR (ιʷ w) Xs′ c′ (peelSL-map Xs′ c′ peelSR→ r)
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
        (sealedRᴿ (ιʷ w) (renameVar τR β′) (repR Ys′ c′)
          (leafBelowS d le (sdesc Xs Ys c) k w τL τR)) V V′
    → leafBelowS d le (sealS β β′ (sdesc Xs Ys c)) k w τL τR V V′
  sealS← r with sealedL-inv r
  sealS← r | W , refl , q =
    proj₁ r ,
    peelSL-map Xs′ c′ (peelSR← {ι = ιʷ w}) (sealedR-peelSL (ιʷ w) Xs′ c′ q)

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
                   (peelSR-map (ιʷ w) Ys₁ c₁
                     (to (leafBelow-ren d le σL σR c k w τL τR))) r))))
    (λ r → peelSL-map Xs₁ c₁
             (peelSR-map (ιʷ w) Ys₁ c₁
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
      (peelSR (ιʷ w) Ys′ c′ (leafBelow d le c k w (τL ∘↪ σL) (τR ∘↪ σR)))
      V V′

-- the oracle at a lower bound
Oracle-down : ∀ {d N N′} → N′ ≤ N → Oracle d N → Oracle d N′
Oracle-down le (op , oo) =
  (λ l b c wf → op l (≤-trans b le) c wf) ,
  (λ l b c → oo l (≤-trans b le) c)

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
  → (∀ Y → toRenameᵗ (ρS e₁) Y ≢ β′)
  → ∀ Y → toRenameᵗ (ρS (⊒-trans e′ e₁)) Y ≢ toRenameᵗ (ρS e′) β′
NewR-after e₁ e′ nb Y eq =
  nb Y (toRenameᵗ-injective (ρS e′)
    (trans (sym (toRenameᵗ-∘ (ρS e′) (ρS e₁) Y)) eq))

------------------------------------------------------------------------
-- Closure under the conversion at a new store variable
------------------------------------------------------------------------

NewRC₁ : ∀ {w w₁ : World} → w₁ ⊒ w → RConv (storeR w₁) → Set
NewRC₁ e₁ nothing = ⊤
NewRC₁ e₁ (just (β′ , R′)) = ∀ Y → toRenameᵗ (ρS e₁) Y ≢ β′

NewRC-after : ∀ {w w₁ w′ : World} (e₁ : w₁ ⊒ w) (e′ : w′ ⊒ w₁)
    (rc : RConv (storeR w₁))
  → NewRC₁ e₁ rc → NewRC (⊒-trans e′ e₁) (renRConv (ρS e′) rc)
NewRC-after e₁ e′ nothing nb = tt
NewRC-after e₁ e′ (just (β′ , R′)) nb = NewR-after e₁ e′ nb

module _ {d} {w w₁ : World} (e₁ : w₁ ⊒ w) {L : Leaf (ΔL w) (ΔR w)}
    {β : TyVar (ΔL w₁)} (nb : ∀ X → toRenameᵗ (ρL e₁) X ≢ β) where

  private
    L₁ = transportLeaf (ρL e₁) (ρR e₁) L

  fresh→convP : ∀ {rk T T′ N} (R : Ty (ΔL w₁)) (rc : RConv (storeR w₁))
    → Allowed rk rc → NewRC₁ e₁ rc → RCΣ w₁ rc → FreshP d rk w L T T′
    → ConvLeafP d N w₁ R rc β L₁ L₁ (renameᵗ (toRenameᵗ (ρL e₁)) T)
        (renameᵗ (toRenameᵗ (ρS e₁)) T′)
  fresh→convP {rk} {T} {T′} R rc ok nrc rs f {w′} e′ {k} k≤N =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w′ (≈ˡ-sym L∘)
        (ℰL-≡ d k w′ L₂
          (cong (λ C → Vl ↑ 〖 toRenameᵗ (ρL e′) β
                            , renameᵗ (toRenameᵗ (ρL e′)) R ↑ C 〗)
            (sym (renameTy-∘ (ρL e′) (ρL e₁) T)))
          (cong (λ C → revM (renRConv (ρS e′) rc) C Vr)
            (sym (renameTy-∘ (ρS e′) (ρS e₁) T′)))
          (proj₁ g vl vr (leafRel-resp d k w′ L∘ r)))) ,
    (λ {Wl} {Wr} wl wr r →
      ℰL-resp d k w′ (≈ˡ-sym L∘)
        (ℰL-≡ d k w′ L₂
          (cong (λ C → Wl ↓ makeConceal (toRenameᵗ (ρL e′) β)
                            (renameᵗ (toRenameᵗ (ρL e′)) R) C)
            (sym (renameTy-∘ (ρL e′) (ρL e₁) T)))
          (cong (λ C → conM (renRConv (ρS e′) rc) C Wr)
            (sym (renameTy-∘ (ρS e′) (ρS e₁) T′)))
          (proj₂ g wl wr (leafRel-resp d k w′ L∘ r))))
    where
    L∘ = transportLeaf-∘ (ρL e′) (ρL e₁) (ρR e′) (ρR e₁) L
    L₂ = transportLeaf (ρL e′ ∘↪ ρL e₁) (ρR e′ ∘↪ ρR e₁) L
    g = f (⊒-trans e′ e₁) (renRConv (ρS e′) rc) (Allowed-ren rk (ρS e′) rc ok)
          (NewL-after e₁ e′ nb) (NewRC-after e₁ e′ rc nrc)
          (RCΣ-ren e′ rc rs) {k}

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
  inj₂ (toRenameᵗ ρ _ , refl , (λ eq → ne (toRenameᵗ-injective ρ eq)))

module _ {d : Dir} {N : ℕ} {w : World} {L : Leaf (ΔL w) (ΔR w)}
    (gl : GoodLeaf L) {γ : TyVar (ΔL w)} {γ′ : TyVar (storeR w)} where

  -- under the conversion at hand, at another store variable
  storeConvP : ∀ R (rc : RConv (storeR w)) {α} → γ ≢ α → RNe rc γ′
    → ConvLeafP d N w R rc α L L (＇ γ) (＇ γ′)
  storeConvP R rc ne rn {w′} e {k} k≤N =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq))
        (renRConv (ρS e) rc) (RNe-ren (ρS e) rc rn) vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq))
        (renRConv (ρS e) rc) (RNe-ren (ρS e) rc rn) wl wr r)

  -- under later conversions
  storeFreshP : ∀ {rk} → FreshP d rk w L (＇ γ) (＇ γ′)
  storeFreshP {rk} {w′} e {β} {R} rc ok nb nrc rs {k} =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) rc (rid rc nrc) vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) rc (rid rc nrc) wl wr r)
    where
    rid : (rc′ : RConv (storeR w′)) → NewRC e rc′
      → RId rc′ (＇ toRenameᵗ (ρS e) γ′)
    rid nothing n = tt
    rid (just (β′ , R′)) n = inj₂ (toRenameᵗ (ρS e) γ′ , refl , n γ′)

-- a store-variable leaf whose right side is not converted
module _ {d : Dir} {N : ℕ} {w : World} {L : Leaf (ΔL w) (ΔR w)}
    (gl : GoodLeaf L) {γ : TyVar (ΔL w)} {T′ : Ty (storeR w)} where

  storeConvPN : ∀ R {α} → γ ≢ α
    → ConvLeafP d N w R nothing α L L (＇ γ) T′
  storeConvPN R ne {w′} e {k} k≤N =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq)) nothing
        {T′ = renameᵗ (toRenameᵗ (ρS e)) T′} tt vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq)) nothing
        {T′ = renameᵗ (toRenameᵗ (ρS e)) T′} tt wl wr r)

  storeFreshPL : FreshP d left w L (＇ γ) T′
  storeFreshPL {w′} e {β} {R} nothing ok nb nrc rs {k} =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) nothing
        {T′ = renameᵗ (toRenameᵗ (ρS e)) T′} tt vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ) nothing
        {T′ = renameᵗ (toRenameᵗ (ρS e)) T′} tt wl wr r)
  storeFreshPL e (just c) () nb nrc rs

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
    {w : World} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {σt : Δ′ ⇒ˢ storeR w}
    {w₁ : World} (e₁ : w₁ ⊒ w)
    {β : TyVar (ΔL w₁)} (nb : ∀ X → toRenameᵗ (ρL e₁) X ≢ β)
    {Ls : Leaf (ΔL w₁) (ΔR w₁)} {Lt : Leaf (ΔL w) (ΔR w)}
    {Tl : Ty (ΔL w)} where

  private
    ρl = toRenameᵗ (ρL e₁)
    ρs = toRenameᵗ (ρS e₁)


  -- a paired binder; the right converts its own store variable β′, new
  -- in the store
  ConvI-newP : ∀ {Tr : Ty (storeR w)} {β′ : TyVar (storeR w₁)} {Nβ}
    → (∀ Y → ρs Y ≢ β′) → Nβ ≤ N → FreshI Φ d N both w δt σt
    → GoodLeaf Ls → GoodLeaf Lt → FreshP d both w Lt Tl Tr
    → SealI d Nβ w₁ (m-pair {Φ = pair Φ} ↔-here β′) β
        (extPairI (＇ β) (ιT w₁ (＇ β′)) Ls (δt ↑ᴵ e₁))
        (extPairI Tl (ιT w Tr) Lt δt ↑ᴵ e₁) ((Tr •ˢ σt) ↑ˢ e₁)
    → ΣR w₁ ∋Σ β′ ⦂ renameᵗ ρs Tr
    → ConvI d Nβ both w₁ (m-pair {Φ = pair Φ} ↔-here β′) β
        (extPairI (＇ β) (ιT w₁ (＇ β′)) Ls (δt ↑ᴵ e₁))
        (extPairI Tl (ιT w Tr) Lt δt ↑ᴵ e₁)
        (＇ β′ •ˢ (σt ↑ˢ e₁)) ((Tr •ˢ σt) ↑ˢ e₁)
  goodS (ConvI-newP {β′ = β′} nb′ le h gs gt ft si bs) =
    GoodI-extPairI {T = ＇ β} {T′ = ιT w₁ (＇ β′)} {δ = δt ↑ᴵ e₁} gs
      (GoodI-↑ {δ = δt} (fgood h) e₁)
  goodT (ConvI-newP {Tr = Tr} nb′ le h gs gt ft si bs) =
    GoodI-↑ {δ = extPairI Tl (ιT w Tr) Lt δt}
      (GoodI-extPairI {T = Tl} {T′ = ιT w Tr} {δ = δt} gt (fgood h)) e₁
  selfI (ConvI-newP nb′ le h gs gt ft si bs) = refl , refl
  rcOK (ConvI-newP nb′ le h gs gt ft si bs) = tt
  tyL (ConvI-newP nb′ le h gs gt ft si bs) zero = replaceTy-self β _
  tyL (ConvI-newP nb′ le h gs gt ft si bs) (suc Z) =
    replaceTy-new ρl _ nb (δl δt Z)
  tyR (ConvI-newP {β′ = β′} nb′ le h gs gt ft si bs) zero = replaceTy-self β′ _
  tyR (ConvI-newP nb′ le h gs gt ft si bs) (suc Y) =
    replaceTy-new ρs _ nb′ (σt Y)
  rcΣ (ConvI-newP nb′ le h gs gt ft si bs) = bs
  leafO (ConvI-newP nb′ le h gs gt ft si bs) zero o = ⊥-elim (o refl)
  leafO (ConvI-newP nb′ le h gs gt ft si bs) (suc Z) o = ≈ˡ-refl
  convP (ConvI-newP nb′ le h gs gt ft si bs) ↔-here o = ⊥-elim (o refl)
  convP (ConvI-newP {Tr = Tr} {β′} nb′ le h gs gt ft si bs)
      (↔-pair {X = Z} {Y = Y′} z) o =
    fresh→convP {d = d} e₁ {L = leaf δt Z} nb {rk = both}
      (renameᵗ ρl Tl) (just (β′ , renameᵗ ρs Tr)) tt nb′ bs
      (fP h z)
  convO (ConvI-newP nb′ le h gs gt ft si bs) (only-pair {X = Z} z) o =
    fresh→convO {d = d} e₁ {L = leaf δt Z} nb (renameᵗ ρl Tl) (fO h z)
  genP (ConvI-newP nb′ le h gs gt ft si bs) ↔-here =
    FreshP-↑ {d = d} e₁ {L = Lt} {rk = both} {T = Tl} ft
  genP (ConvI-newP nb′ le h gs gt ft si bs) (↔-pair {X = Z} {Y = Y′} z) =
    FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = both} {T = δl δt Z}
      {T′ = σt Y′} (fP h z)
  genO (ConvI-newP nb′ le h gs gt ft si bs) (only-pair {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z}
      (fO h z)
  genPS (ConvI-newP {β′ = β′} nb′ le h gs gt ft si bs) ↔-here =
    storeFreshP {d = d} {N = N} {w = w₁} {L = Ls} gs {γ = β} {γ′ = β′}
      {rk = both}
  genPS (ConvI-newP nb′ le h gs gt ft si bs) (↔-pair {X = Z} {Y = Y′} z) =
    FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = both} {T = δl δt Z}
      {T′ = σt Y′} (fP h z)
  genOS (ConvI-newP nb′ le h gs gt ft si bs) (only-pair {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z} (fO h z)
  sealI (ConvI-newP nb′ le h gs gt ft si bs) = si
  oracle (ConvI-newP nb′ le h gs gt ft si bs) = Oracle-down le (forc h)

  -- a paired binder; the right does not convert, and is instantiated at
  -- Tr itself
  ConvI-newL : ∀ {rk} {Tr : Ty (storeR w)} {T′ : Ty (storeR w₁)} {Nβ}
    → T′ ≡ renameᵗ ρs Tr → Nβ ≤ N
    → FreshI Φ d N rk w δt σt
    → GoodLeaf Ls → GoodLeaf Lt → FreshP d both w Lt Tl Tr
    → SealI d Nβ w₁ (m-left {Φ = pair Φ} {X = zero}) β
        (extPairI (＇ β) (ιT w₁ T′) Ls (δt ↑ᴵ e₁))
        (extPairI Tl (ιT w Tr) Lt δt ↑ᴵ e₁) ((Tr •ˢ σt) ↑ˢ e₁)
    → ConvI d Nβ left w₁ (m-left {Φ = pair Φ} {X = zero}) β
        (extPairI (＇ β) (ιT w₁ T′) Ls (δt ↑ᴵ e₁))
        (extPairI Tl (ιT w Tr) Lt δt ↑ᴵ e₁)
        (T′ •ˢ (σt ↑ˢ e₁)) ((Tr •ˢ σt) ↑ˢ e₁)
  goodS (ConvI-newL {Tr = Tr} {T′} eqT le h gs gt ft si) =
    GoodI-extPairI {T = ＇ β} {T′ = ιT w₁ T′} {δ = δt ↑ᴵ e₁} gs
      (GoodI-↑ {δ = δt} (fgood h) e₁)
  goodT (ConvI-newL {Tr = Tr} {T′} eqT le h gs gt ft si) =
    GoodI-↑ {δ = extPairI Tl (ιT w Tr) Lt δt}
      (GoodI-extPairI {T = Tl} {T′ = ιT w Tr} {δ = δt} gt (fgood h)) e₁
  selfI (ConvI-newL eqT le h gs gt ft si) = refl
  rcOK (ConvI-newL eqT le h gs gt ft si) = tt
  tyL (ConvI-newL eqT le h gs gt ft si) zero = replaceTy-self β _
  tyL (ConvI-newL eqT le h gs gt ft si) (suc Z) =
    replaceTy-new ρl _ nb (δl δt Z)
  tyR (ConvI-newL eqT le h gs gt ft si) zero = eqT
  tyR (ConvI-newL eqT le h gs gt ft si) (suc Y) = refl
  rcΣ (ConvI-newL eqT le h gs gt ft si) = tt
  leafO (ConvI-newL eqT le h gs gt ft si) zero o = ⊥-elim (o refl)
  leafO (ConvI-newL eqT le h gs gt ft si) (suc Z) o = ≈ˡ-refl
  convP (ConvI-newL {rk} eqT le h gs gt ft si) ↔-here o = ⊥-elim (o refl)
  convP (ConvI-newL {rk} eqT le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) o =
    fresh→convP {d = d} e₁ {L = leaf δt Z} nb {rk = left}
      (renameᵗ ρl Tl) nothing tt tt tt
      (FreshP-left {rk = rk} {L = leaf δt Z} {T = δl δt Z}
        {T′ = σt Y′} (fP h z))
  convO (ConvI-newL eqT le h gs gt ft si) (only-pair {X = Z} z) o =
    fresh→convO {d = d} e₁ {L = leaf δt Z} nb (renameᵗ ρl Tl) (fO h z)
  genP (ConvI-newL {rk} {Tr = Tr} eqT le h gs gt ft si) ↔-here =
    FreshP-left {rk = both}
      {L = transportLeaf (ρL e₁) (ρR e₁) Lt} {T = renameᵗ ρl Tl}
      {T′ = renameᵗ ρs Tr}
      (FreshP-↑ {d = d} e₁ {L = Lt} {rk = both} {T = Tl} ft)
  genP (ConvI-newL {rk} eqT le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) =
    FreshP-left {rk = rk}
      {L = transportLeaf (ρL e₁) (ρR e₁) (leaf δt Z)}
      {T = renameᵗ ρl (δl δt Z)} {T′ = renameᵗ ρs (σt Y′)}
      (FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
        {T′ = σt Y′} (fP h z))
  genO (ConvI-newL eqT le h gs gt ft si) (only-pair {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z}
      (fO h z)
  genPS (ConvI-newL {T′ = T′} eqT le h gs gt ft si) ↔-here =
    storeFreshPL {d = d} {N = N} {w = w₁} {L = Ls} gs {γ = β} {T′ = T′}
  genPS (ConvI-newL {rk} eqT le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) =
    FreshP-left {rk = rk}
      {L = transportLeaf (ρL e₁) (ρR e₁) (leaf δt Z)}
      {T = renameᵗ ρl (δl δt Z)} {T′ = renameᵗ ρs (σt Y′)}
      (FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
        {T′ = σt Y′} (fP h z))
  genOS (ConvI-newL eqT le h gs gt ft si) (only-pair {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z} (fO h z)
  sealI (ConvI-newL eqT le h gs gt ft si) = si
  oracle (ConvI-newL eqT le h gs gt ft si) = Oracle-down le (forc h)

  -- a left-only binder
  ConvI-newO : ∀ {rk} {Nβ} → Nβ ≤ N → FreshI Φ d N rk w δt σt
    → GoodLeaf Ls → GoodLeaf Lt → FreshO d w Lt Tl
    → SealI d Nβ w₁ (m-left {Φ = only Φ} {X = zero}) β
        (extOnlyI (＇ β) Ls (δt ↑ᴵ e₁)) (extOnlyI Tl Lt δt ↑ᴵ e₁)
        (σt ↑ˢ e₁)
    → ConvI d Nβ rk w₁ (m-left {Φ = only Φ} {X = zero}) β
        (extOnlyI (＇ β) Ls (δt ↑ᴵ e₁)) (extOnlyI Tl Lt δt ↑ᴵ e₁)
        (σt ↑ˢ e₁) (σt ↑ˢ e₁)
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
  rcΣ (ConvI-newO le h gs gt ft si) = tt
  leafO (ConvI-newO le h gs gt ft si) zero o = ⊥-elim (o refl)
  leafO (ConvI-newO le h gs gt ft si) (suc Z) o = ≈ˡ-refl
  convP (ConvI-newO {rk} le h gs gt ft si) (↔-only {X = Z} {Y = Y′} z) o =
    fresh→convP {d = d} e₁ {L = leaf δt Z} nb {rk = rk}
      (renameᵗ ρl Tl) nothing (Allowed-nothing rk) tt tt
      (fP h z)
  convO (ConvI-newO le h gs gt ft si) only-here o = ⊥-elim (o refl)
  convO (ConvI-newO le h gs gt ft si) (only-only {X = Z} z) o =
    fresh→convO {d = d} e₁ {L = leaf δt Z} nb (renameᵗ ρl Tl) (fO h z)
  genP (ConvI-newO {rk} le h gs gt ft si) (↔-only {X = Z} {Y = Y′} z) =
    FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
      {T′ = σt Y′} (fP h z)
  genO (ConvI-newO le h gs gt ft si) only-here =
    FreshO-↑ {d = d} e₁ {L = Lt} {T = Tl} ft
  genO (ConvI-newO le h gs gt ft si) (only-only {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z} (fO h z)
  genPS (ConvI-newO {rk} le h gs gt ft si) (↔-only {X = Z} {Y = Y′} z) =
    FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
      {T′ = σt Y′} (fP h z)
  genOS (ConvI-newO le h gs gt ft si) only-here =
    storeFreshO {d = d} {w = w₁} {L = Ls} gs {γ = β}
  genOS (ConvI-newO le h gs gt ft si) (only-only {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z} (fO h z)
  sealI (ConvI-newO le h gs gt ft si) = si
  oracle (ConvI-newO le h gs gt ft si) = Oracle-down le (forc h)

  -- a dead binder, instantiated at Tl
  ConvI-newD : ∀ {rk} {Nβ} → Nβ ≤ N → FreshI Φ d N rk w δt σt
    → ConvI d Nβ rk w₁ (m-dead {Φ = dead Φ} dead-here) β
        (extDeadI (＇ β) (δt ↑ᴵ e₁)) (extDeadI Tl δt ↑ᴵ e₁)
        (σt ↑ˢ e₁) (σt ↑ˢ e₁)
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
  rcΣ (ConvI-newD le h) = tt
  leafO (ConvI-newD le h) zero o = ⊥-elim (o refl)
  leafO (ConvI-newD le h) (suc Z) o = ≈ˡ-refl
  convP (ConvI-newD {rk} le h) (↔-dead {X = Z} {Y = Y′} z) o =
    fresh→convP {d = d} e₁ {L = leaf δt Z} nb {rk = rk}
      (renameᵗ ρl Tl) nothing (Allowed-nothing rk) tt tt
      (fP h z)
  convO (ConvI-newD le h) (only-dead {X = Z} z) o =
    fresh→convO {d = d} e₁ {L = leaf δt Z} nb (renameᵗ ρl Tl) (fO h z)
  genP (ConvI-newD {rk} le h) (↔-dead {X = Z} {Y = Y′} z) =
    FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
      {T′ = σt Y′} (fP h z)
  genO (ConvI-newD le h) (only-dead {X = Z} z) =
    FreshO-↑ {d = d} e₁ {L = leaf δt Z} {T = δl δt Z} (fO h z)
  genPS (ConvI-newD {rk} le h) (↔-dead {X = Z} {Y = Y′} z) =
    FreshP-↑ {d = d} e₁ {L = leaf δt Z} {rk = rk} {T = δl δt Z}
      {T′ = σt Y′} (fP h z)
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

  -- a paired binder whose right converts at the store variable β′; the
  -- descriptor's right type Ys, c has the store preimage Tr
  sealNewP : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
      {σt : Δ′ ⇒ˢ storeR w} (β′ : TyVar (storeR w₁)) {Tr : Ty (storeR w)}
    → repR Ys c ≡ ιT w Tr
    → SealI d s w₁ (m-pair {Φ = pair Φ} {X = zero} ↔-here β′) β
        (extPairI (＇ β) (ιT w₁ (＇ β′))
          (sem (leafBelowS d le_s
            (sdesc (β ∷ Xs₁) (toRenameᵗ (ιʷ w₁) β′ ∷ Ys₁) c₁)))
          (δt ↑ᴵ e₁))
        (extPairI (repL Xs c) (ιT w Tr) Lt δt ↑ᴵ e₁) ((Tr •ˢ σt) ↑ˢ e₁)
  sealNewP β′ {Tr} hTr = rev , con
    where
    β″ = toRenameᵗ (ιʷ w₁) β′

    eY : ∀ {w′} (e : w′ ⊒ w₁)
      → renameVar (id↪ᵗ ∘↪ ρR e) β″
        ≡ toRenameᵗ (ιʷ w′) (toRenameᵗ (ρS e) β′)
    eY e = trans (varβR e β″) (coh e β′)

    TrS : ∀ {w′} (e : w′ ⊒ w₁) → Ty (storeR w′)
    TrS e = renameᵗ (toRenameᵗ (ρS e)) (renameᵗ (toRenameᵗ (ρS e₁)) Tr)

    eR : ∀ {w′} (e : w′ ⊒ w₁)
      → repR (map (renameVar (id↪ᵗ ∘↪ ρR e)) Ys₁)
          (renameDesc (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) c₁)
        ≡ renameᵗ (toRenameᵗ (ιʷ w′)) (TrS e)
    eR e =
      trans (repβ′ e)
        (trans (cong (λ T → renameᵗ (toRenameᵗ (ρR e))
                              (renameᵗ (toRenameᵗ (ρR e₁)) T)) hTr)
          (trans (cong (renameᵗ (toRenameᵗ (ρR e))) (coh-ty e₁ Tr))
            (coh-ty e (renameᵗ (toRenameᵗ (ρS e₁)) Tr))))

    rev : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k ≤ s → ∀ {Vl Vr}
      → leafBelowS d le_s (sdesc (β ∷ Xs₁) (β″ ∷ Ys₁) c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) Vl Vr
      → sealedL (toRenameᵗ (ρL e) β)
          (renameᵗ (toRenameᵗ (ρL e))
            (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c)))
          (sealedR (toRenameᵗ (ρS e) β′) (TrS e)
            (leafRel d (pred k) w′ (transportLeaf (ρL e) (ρR e)
              (transportLeaf (ρL e₁) (ρR e₁) Lt)))) Vl Vr
    rev {w′} e {k} pos le r =
      sealedL-map (varβ e β) (repβ e)
        (λ q → sealedRᴿ→ (ιʷ w′)
          (sealedRᴿ-map (eY e) (eR e)
            (λ q′ → leafBelowS-down d le_n c₀ (onlyStage-≤ ≺ k) w′ _ _
                      (readT e k q′)) q))
        (sealS→ d le_s Xs₁ Ys₁ c₁ β β″ k w′ (id↪ᵗ ∘↪ ρL e)
          (id↪ᵗ ∘↪ ρR e) r)

    con : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k < s → ∀ {Wl Wr}
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
          (transportLeaf (ρL e₁) (ρR e₁) Lt)) Wl Wr
      → leafBelowS d le_s (sdesc (β ∷ Xs₁) (β″ ∷ Ys₁) c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
          (Wl ↓ seal (toRenameᵗ (ρL e) β)
            (renameᵗ (toRenameᵗ (ρL e))
              (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c))))
          (Wr ↓ seal (toRenameᵗ (ρS e) β′) (TrS e))
    con {w′} e {k} pos lt r =
      sealS← d le_s Xs₁ Ys₁ c₁ β β″ k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
        ((sym (varβ e β) , sym (repβ e)) ,
          (sym (eY e) , sym (eR e)) , writeS e k lt r)

  -- a paired binder whose right does not convert
  sealNewL : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
      {σt : Δ′ ⇒ˢ storeR w} {T′ : Ty (storeR w₁)} {Tr : Ty (storeR w)}
    → UpB d s n
    → SealI d s w₁ (m-left {Φ = pair Φ} {X = zero}) β
        (extPairI (＇ β) (ιT w₁ T′)
          (sem (leafBelowS d le_s (sdesc (β ∷ Xs₁) Ys₁ c₁)))
          (δt ↑ᴵ e₁))
        (extPairI (repL Xs c) (ιT w Tr) Lt δt ↑ᴵ e₁) ((Tr •ˢ σt) ↑ˢ e₁)
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
-- Left-only leaves under other bounds and renamings
------------------------------------------------------------------------

-- below both bounds, the bound does not matter
leafG-bound : ∀ {n₁ a₁ n₂ a₂} (le₁ : n₁ ≤′ a₁) (le₂ : n₂ ≤′ a₂)
    (c : Desc ΘL ΘR) {k} → k ≤ n₂ → ∀ w τL τR {V V′}
  → leafG le₁ c k w τL τR V V′ → leafG le₂ c k w τL τR V V′
leafG-bound {n₁ = n₁} {n₂ = n₂} le₁ le₂ c {k} k≤ w τL τR r
    with k ≤? n₁ | k ≤? n₂
leafG-bound le₁ le₂ (desc p env envR) {k} k≤ w τL τR r
    | yes l₁ | yes l₂ =
  G→G≤ (≤′-trans (≤⇒≤′ l₂) le₂) p w (G≤→G (≤′-trans (≤⇒≤′ l₁) le₁) p w r)
leafG-bound le₁ le₂ c {k} k≤ w τL τR r | yes l₁ | no ¬l₂ = ⊥-elim (¬l₂ k≤)
leafG-bound le₁ le₂ c {k} k≤ w τL τR () | no ¬l₁ | _

-- a larger bound keeps the leaf
leafG-up : ∀ {n₁ a₁ n₂ a₂} (le₁ : n₁ ≤′ a₁) (le₂ : n₂ ≤′ a₂)
    (c : Desc ΘL ΘR) → n₁ ≤ n₂ → ∀ {k} w τL τR {V V′}
  → leafG le₁ c k w τL τR V V′ → leafG le₂ c k w τL τR V V′
leafG-up {n₁ = n₁} {n₂ = n₂} le₁ le₂ c n₁≤n₂ {k} w τL τR r
    with k ≤? n₁ | k ≤? n₂
leafG-up le₁ le₂ (desc p env envR) n₁≤n₂ {k} w τL τR r
    | yes l₁ | yes l₂ =
  G→G≤ (≤′-trans (≤⇒≤′ l₂) le₂) p w (G≤→G (≤′-trans (≤⇒≤′ l₁) le₁) p w r)
leafG-up le₁ le₂ c n₁≤n₂ {k} w τL τR r | yes l₁ | no ¬l₂ =
  ⊥-elim (¬l₂ (≤-trans l₁ n₁≤n₂))
leafG-up le₁ le₂ c n₁≤n₂ {k} w τL τR () | no ¬l₁ | _

onlyLeaf-up : ∀ d {n₁ a₁ n₂ a₂} (le₁ : n₁ ≤′ a₁) (le₂ : n₂ ≤′ a₂)
    (c : Desc ΘL ΘR) → n₁ ≤ n₂ → ∀ {k} w τL τR {V V′}
  → onlyLeaf d le₁ c k w τL τR V V′ → onlyLeaf d le₂ c k w τL τR V V′
onlyLeaf-up ≺ le₁ le₂ c = leafBelow-up ≺ le₁ le₂ c
onlyLeaf-up ≻ le₁ le₂ c = leafG-up le₁ le₂ c

-- the target's left-only leaf, read at the stages a conceal needs
onlyLeaf-write : ∀ d {s n a b} (le_n : n ≤′ b) (le_s : s ≤′ a)
    (c : Desc ΘL ΘR) → UpB d s n → ∀ {k} → onlyBelow d k s
  → ∀ w τL τR {V V′}
  → onlyLeaf d le_n c k w τL τR V V′ → onlyLeaf d le_s c k w τL τR V V′
onlyLeaf-write ≺ le_n le_s c up {k} lt =
  leafBelow-bound ≺ le_n le_s c {k} lt
onlyLeaf-write ≻ le_n le_s c up {k} lt w τL τR =
  leafG-up le_n le_s c up {k} w τL τR

-- a renamed descriptor's left-only leaf
leafG-ren : ∀ {n′ n} (le : n′ ≤′ n) {ΘL′ ΘR′}
    (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′) (c : Desc ΘL ΘR) k w τL τR {V V′}
  → leafG le (renameDesc σL σR c) k w τL τR V V′
    ⇔ leafG le c k w (τL ∘↪ σL) (τR ∘↪ σR) V V′
leafG-ren {n′ = n′} le σL σR c k w τL τR with k ≤? n′
leafG-ren {n′ = n′} le σL σR c k w τL τR | yes k≤ =
  iff (subst (λ c′ → descG _ w c′ _ _) (renameDesc-∘ τL σL τR σR c))
      (subst (λ c′ → descG _ w c′ _ _) (sym (renameDesc-∘ τL σL τR σR c)))
leafG-ren {n′ = n′} le σL σR c k w τL τR | no ¬k≤ = iff (λ r → r) (λ r → r)

onlyLeaf-ren : ∀ d {n′ n} (le : n′ ≤′ n) {ΘL′ ΘR′}
    (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′) (c : Desc ΘL ΘR) k w τL τR {V V′}
  → onlyLeaf d le (renameDesc σL σR c) k w τL τR V V′
    ⇔ onlyLeaf d le c k w (τL ∘↪ σL) (τR ∘↪ σR) V V′
onlyLeaf-ren ≺ le = leafBelow-ren ≺ le
onlyLeaf-ren ≻ le = leafG-ren le

onlyLeafS-ren : ∀ d {n′ n} (le : n′ ≤′ n) {ΘL′ ΘR′}
    (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′) (c : SDesc ΘL ΘR) k w τL τR {V V′}
  → onlyLeafS d le (renameSDesc σL σR c) k w τL τR V V′
    ⇔ onlyLeafS d le c k w (τL ∘↪ σL) (τR ∘↪ σR) V V′
onlyLeafS-ren d le σL σR (sdesc Xs Ys c) k w τL τR {V} {V′} =
  iff
    (λ r → subst (λ c′ → F Xs₂ c′) eqc
             (subst (λ Xs′ → F Xs′ c₁) eqX
               (peelSL-map Xs₁ c₁
                 (to (onlyLeaf-ren d le σL σR c k w τL τR)) r)))
    (λ r → peelSL-map Xs₁ c₁
             (from (onlyLeaf-ren d le σL σR c k w τL τR))
             (subst (λ Xs′ → F Xs′ c₁) (sym eqX)
               (subst (λ c′ → F Xs₂ c′) (sym eqc) r)))
  where
  Xs₁ = map (renameVar τL) (map (renameVar σL) Xs)
  Xs₂ = map (renameVar (τL ∘↪ σL)) Xs
  c₁ = renameDesc τL τR (renameDesc σL σR c)
  eqX = map-renameVar-∘ τL σL Xs
  eqc = renameDesc-∘ τL σL τR σR c
  F : List (TyVar (ΔL w)) → Desc (ΔL w) (ΔR w) → Set
  F Xs′ c′ =
    peelSL Xs′ c′ (onlyLeaf d le c k w (τL ∘↪ σL) (τR ∘↪ σR)) V V′

-- a map on the core leaf of a sealed descriptor
onlyS-map : ∀ d {n₁ a₁ n₂ a₂} (le₁ : n₁ ≤′ a₁) (le₂ : n₂ ≤′ a₂)
    (s : SDesc ΘL ΘR) {k w τL τR}
  → (∀ {V V′} → onlyLeaf d le₁ (core s) k w τL τR V V′
       → onlyLeaf d le₂ (core s) k w τL τR V V′)
  → ∀ {V V′} → onlyLeafS d le₁ s k w τL τR V V′
  → onlyLeafS d le₂ s k w τL τR V V′
onlyS-map d le₁ le₂ (sdesc Xs Ys c) {τL = τL} {τR} f =
  peelSL-map (map (renameVar τL) Xs) (renameDesc τL τR c) f

-- a left prefix of a left-only leaf
module _ (d : Dir) {n′ n} (le : n′ ≤′ n) {ΘL ΘR}
    (Xs : List (TyVar ΘL)) (Ys : List (TyVar ΘR)) (c : Desc ΘL ΘR)
    (β : TyVar ΘL) (k : ℕ) (w : World)
    (τL : ΘL ↪ᵗ ΔL w) (τR : ΘR ↪ᵗ ΔR w) where

  private
    c′ = renameDesc τL τR c
    Xs′ = map (renameVar τL) Xs

  onlyS→ : ∀ {V V′}
    → onlyLeafS d le (sealSL β (sdesc Xs Ys c)) k w τL τR V V′
    → sealedL (renameVar τL β) (repL Xs′ c′)
        (onlyLeafS d le (sdesc Xs Ys c) k w τL τR) V V′
  onlyS→ {V = V ↓ s} r = r
  onlyS→ {V = ` x₀} ()
  onlyS→ {V = ƛ M₀} ()
  onlyS→ {V = L₀ · M₀} ()
  onlyS→ {V = Λ M₀} ()
  onlyS→ {V = L₀ ⦂∀ C₀ [ T₀ ]} ()
  onlyS→ {V = $ κ₀} ()
  onlyS→ {V = L₀ ⊕[ op₀ ] M₀} ()
  onlyS→ {V = W₀ ⟨ c₀ ⟩} ()
  onlyS→ {V = M₀ ↑ c₀} ()
  onlyS→ {V = blame} ()

  onlyS← : ∀ {V V′}
    → sealedL (renameVar τL β) (repL Xs′ c′)
        (onlyLeafS d le (sdesc Xs Ys c) k w τL τR) V V′
    → onlyLeafS d le (sealSL β (sdesc Xs Ys c)) k w τL τR V V′
  onlyS← r with sealedL-inv r
  onlyS← r | W , refl , q = r

-- a left-only store-variable leaf, under the conversion at hand
module _ {d : Dir} {w : World} {L : Leaf (ΔL w) (ΔR w)}
    (gl : GoodLeaf L) {γ : TyVar (ΔL w)} where

  storeConvO : ∀ {N} R {α} → γ ≢ α → ConvLeafO d N w R α L L (＇ γ)
  storeConvO R ne {w′} e {k} k≤N =
    (λ vl vr r →
      idRevO d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq)) vl vr r) ,
    (λ wl vr r →
      idConO d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρL e) eq)) wl vr r)

-- a left-only binder
module SealNewO (d : Dir) {s n a b} (le_s : s ≤′ a) (le_n : n ≤′ b)
    (s≤n : s ≤ n) {w w₁ : World} (e₁ : w₁ ⊒ w)
    (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
    (c : Desc (ΔL w) (ΔR w)) (β : TyVar (ΔL w₁)) where

  open SealNew d le_s le_n s≤n e₁ Xs Ys c β using (varβ; repβ)

  private
    Xs₁ = map (renameVar (ρL e₁)) Xs
    Ys₁ = map (renameVar (ρR e₁)) Ys
    c₁ = renameDesc (ρL e₁) (ρR e₁) c
    c₀ = sdesc Xs Ys c
    Lt = sem (onlyLeafS d le_n c₀)

  -- the target leaf, read in a future of w₁
  readO : ∀ {w′} (e : w′ ⊒ w₁) k {V V′}
    → onlyLeafS d le_s (sdesc Xs₁ Ys₁ c₁) k w′
        (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
    → leafRel d (onlyStage d k) w′ (transportLeaf (ρL e) (ρR e)
        (transportLeaf (ρL e₁) (ρR e₁) Lt)) V V′
  readO {w′} e k r =
    onlyLeafS-down d le_n c₀ (onlyStage-≤ d k) w′ _ _
      (onlyS-map d le_s le_n c₀ (onlyLeaf-up d le_s le_n c s≤n _ _ _)
        (to (onlyLeafS-ren d le_s (ρL e₁) (ρR e₁) c₀ k _ _ _) r))

  writeO : ∀ {w′} (e : w′ ⊒ w₁) k → UpB d s n → onlyBelow d k s
    → ∀ {V V′}
    → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
        (transportLeaf (ρL e₁) (ρR e₁) Lt)) V V′
    → onlyLeafS d le_s (sdesc Xs₁ Ys₁ c₁) k w′
        (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
  writeO e k up lt r =
    from (onlyLeafS-ren d le_s (ρL e₁) (ρR e₁) c₀ k _ _ _)
      (onlyS-map d le_n le_s c₀ (onlyLeaf-write d le_n le_s c up lt _ _ _)
        r)

  sealNewO : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
      {σt : Δ′ ⇒ˢ storeR w}
    → UpB d s n
    → SealI d s w₁ (m-left {Φ = only Φ} {X = zero}) β
        (extOnlyI (＇ β)
          (sem (onlyLeafS d le_s (sdesc (β ∷ Xs₁) Ys₁ c₁)))
          (δt ↑ᴵ e₁))
        (extOnlyI (repL Xs c) Lt δt ↑ᴵ e₁) (σt ↑ˢ e₁)
  sealNewO up = rev , con
    where
    rev : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k ≤ s → ∀ {Vl Vr}
      → onlyLeafS d le_s (sdesc (β ∷ Xs₁) Ys₁ c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) Vl Vr
      → sealedL (toRenameᵗ (ρL e) β)
          (renameᵗ (toRenameᵗ (ρL e))
            (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c)))
          (leafRel d (onlyStage d k) w′ (transportLeaf (ρL e) (ρR e)
            (transportLeaf (ρL e₁) (ρR e₁) Lt))) Vl Vr
    rev {w′} e {k} pos le r =
      sealedL-map (varβ e β) (repβ e) (readO e k)
        (onlyS→ d le_s Xs₁ Ys₁ c₁ β k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) r)

    con : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → onlyBelow d k s
      → ∀ {Wl Vr}
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
          (transportLeaf (ρL e₁) (ρR e₁) Lt)) Wl Vr
      → onlyLeafS d le_s (sdesc (β ∷ Xs₁) Ys₁ c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
          (Wl ↓ seal (toRenameᵗ (ρL e) β)
            (renameᵗ (toRenameᵗ (ρL e))
              (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c)))) Vr
    con {w′} e {k} pos lt r =
      onlyS← d le_s Xs₁ Ys₁ c₁ β k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
        ((sym (varβ e β) , sym (repβ e)) , writeO e k up lt r)

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

-- one step on each side, the counted one included; the right's step runs
-- in its store (`Steps`)
anti₁₁ : ∀ d {s} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) {w : World}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΘL ΘR Δ₁} {Ml : Term (ΔL w)}
    {Ml′ : Term ΘL} {Mr : Term (storeR w)} {Mr′ : Term ΘR}
    {χL : StoreChange (ΔL w) ΘL} {χR : StoreChange (storeR w) ΘR}
    {p₁ : Prefix ΘR Δ₁} {ρ : ΔR w ↪ᵗ Δ₁}
  → Ml —→[ χL ] Ml′ → Mr —→[ χR ] Mr′
  → (st : Steps (pre w) (χR ∷ []) p₁ ρ)
  → (tags : TyVar ΘL → Tag ΘL Δ₁)
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ (χL ∷ [])) X)
            ≡ renameTag (embedᶜˢ (χL ∷ [])) ρ (tag w X))
  → ℰ d s p (mkWorld ΘL Δ₁ tags ΘR p₁ (applyStores (χR ∷ []) (ΣR w)))
      (δ ↑ᴵ stepExt {w = w} (χL ∷ []) (χR ∷ []) st tags ok) Ml′ Mr′
  → ℰ d (suc s) p w δ Ml Mr
anti₁₁ ≺ p sl sr st tags ok r =
  ℰ-anti-≺ p (more sl none) (↠-step sr ↠-refl) st tags ok r
anti₁₁ ≻ p sl sr st tags ok r =
  ℰ-anti-≻ p (↠-step sl ↠-refl) (more sr none) st tags ok r

------------------------------------------------------------------------
-- Conversions renamed into a future, in the main lemma
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {w w′ : World}
    (e : w′ ⊒ w) (m : CMode Φ X (ΔL w) (storeR w)) where

  revRen : ∀ α (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔL w′)) C
    → Q ↑ 〖 toRenameᵗ (ρL e) α
          , repM (CMode-↑ (ρL e) (ρS e) m) (δl (δt ↑ᴵ e))
          ↑ substᵗ (δl (δs ↑ᴵ e)) C 〗
      ≡ Q ↑ rename↑ (toRenameᵗ (ρL e))
            〖 α , repM m (δl δt) ↑ substᵗ (δl δs) C 〗
  revRen α δs δt Q C =
    trans (↑〖〗-≡ refl (repM-↑ (ρL e) (ρS e) m (δl δt)) refl)
      (sym (↑-pk (〖〗-ren (ρL e) α (repM m (δl δt)) (δl δs) C)))

  conRen : ∀ α (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) (Q : Term (ΔL w′)) C
    → Q ↓ makeConceal (toRenameᵗ (ρL e) α)
            (repM (CMode-↑ (ρL e) (ρS e) m) (δl (δt ↑ᴵ e)))
            (substᵗ (δl (δs ↑ᴵ e)) C)
      ≡ Q ↓ rename↓ (toRenameᵗ (ρL e))
            (makeConceal α (repM m (δl δt)) (substᵗ (δl δs) C))
  conRen α δs δt Q C =
    trans (↓mc-≡ refl (repM-↑ (ρL e) (ρS e) m (δl δt)) refl)
      (sym (↓-pk (makeConceal-ren (ρL e) α (repM m (δl δt)) (δl δs) C)))

  rcRen : ∀ (σs σt : Δ′ ⇒ˢ storeR w) (Q : Term (storeR w′)) C
    → revM (rconv (CMode-↑ (ρL e) (ρS e) m) (σt ↑ˢ e))
        (substᵗ (σs ↑ˢ e) C) Q
      ≡ mplug (renameMFrame (ρS e)
          (revFrame (rconv m σt) (substᵗ σs C))) Q
  rcRen σs σt Q C =
    trans (cong (λ c → revM c _ Q) (rconv-↑ (ρL e) (ρS e) m σt))
      (sym (revFrame-ren (ρS e) (rconv m σt) σs C Q))

  ccRen : ∀ (σs σt : Δ′ ⇒ˢ storeR w) (Q : Term (storeR w′)) C
    → conM (rconv (CMode-↑ (ρL e) (ρS e) m) (σt ↑ˢ e))
        (substᵗ (σs ↑ˢ e) C) Q
      ≡ mplug (renameMFrame (ρS e)
          (conFrame (rconv m σt) (substᵗ σs C))) Q
  ccRen σs σt Q C =
    trans (cong (λ c → conM c _ Q) (rconv-↑ (ρL e) (ρS e) m σt))
      (sym (conFrame-ren (ρS e) (rconv m σt) σs C Q))

------------------------------------------------------------------------
-- `∀⊑∀`, the reveal, when the right converts too
------------------------------------------------------------------------

module PairRev (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B)
    (rev : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (rconv m σt) δs δt σs σt B → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (rconv m σt) (substᵗ σs B) Vr))
    where

  -- the descriptor's right type has the store preimage Tr, at which the
  -- right instantiates
  pairRev : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)}
      {α δs δt σs σt} (h : ConvI d N both w m α δs δt σs σt)
    → PreS w δs δt σs σt (`∀ B) → n ≤ N
    → ∀ {α′ R′} → rconv m σt ≡ just (α′ , R′)
    → ∀ {Vl Vr} → Value Vl → Value Vr → allPair d n p w δs Vl Vr
    → ∀ Xs Ys c → WFDesc c → ∀ {Tr} → repR Ys c ≡ ιT w Tr
    → ℰ d n p w (extPairI (repL Xs c) (ιT w Tr)
          (sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))) δt)
        ((Vl ↑ `∀↑ 〖 suc α , ⇑ᵗ (repM m (δl δt))
                    ↑ substᵗ (extsᵗ (δl δs)) A 〗)
           ⦂∀ substᵗ (extsᵗ (δl δt)) A [ repL Xs c ])
        ((Vr ↑ `∀↑ 〖 suc α′ , ⇑ᵗ R′ ↑ substᵗ (extsᵗ σs) B 〗)
           ⦂∀ substᵗ (extsᵗ σt) B [ Tr ])
  pairRev {zero} w h ps le eq vl vr r Xs Ys c wf hTr = ℰ-zero d p w
  pairRev {suc s} w {X} {m} {α} {δs} {δt} {σs} {σt} h ps le {α′} {R′} eq
      {Vl} {Vr} vl vr r Xs Ys c wf {Tr} hTr =
    anti₁₁ d p stepL stepR (stᴬ w Tr) (tagsLR w Tr) (okBindLR w Tl Tr) inner
    where
    Tl = repL Xs c
    R = repM m (δl δt)
    cL = 〖 suc α , ⇑ᵗ R ↑ substᵗ (extsᵗ (δl δs)) A 〗
    cR = 〖 suc α′ , ⇑ᵗ R′ ↑ substᵗ (extsᵗ σs) B 〗
    BtL = substᵗ (extsᵗ (δl δt)) A
    BtR = substᵗ (extsᵗ σt) B

    tyR′ : ∀ Y → replaceTy α′ R′ (σs Y) ≡ σt Y
    tyR′ = subst (λ rc → ∀ Y → replaceRC rc (σs Y) ≡ σt Y) eq (tyR h)

    stepL = revInst cL vl (tgt-body α R (δl δs) (δl δt) (tyL h) A)
    stepR = revInst cR vr (tgt-body α′ R′ σs σt tyR′ B)

    e₁ = extLR w Tl Tr
    w₁ = worldLR w Tr
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    ρS₁ = ρS e₁
    β″ = toRenameᵗ (ιʷ w₁) zero
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    c″ = sdesc (zero ∷ Xs₁) (β″ ∷ Ys₁) c₁
    le_s : s ≤′ suc s
    le_s = ≤′-step ≤′-refl
    s≤N : s ≤ N
    s≤N = ≤-trans (n≤1+n s) le
    Ls = sem (leafBelowS d le_s c″)
    Lt = sem (leafBelowS d (≤′-refl {suc s}) (sdesc Xs Ys c))
    gLs = leafBelowS-good d le_s c″
    δsβ = extPairI (＇ zero) (ιT w₁ (＇ zero)) Ls (δs ↑ᴵ e₁)
    δtβ = extPairI (＇ zero) (ιT w₁ (＇ zero)) Ls (δt ↑ᴵ e₁)
    δtg = extPairI Tl (ιT w Tr) Lt δt ↑ᴵ e₁
    σsβ = ＇ zero •ˢ (σs ↑ˢ e₁)
    σtβ = ＇ zero •ˢ (σt ↑ˢ e₁)
    σtg = (Tr •ˢ σt) ↑ˢ e₁
    m₁ = CMode-pair (CMode-↑ ρL₁ ρS₁ m)
    α₁ = toRenameᵗ ρL₁ α

    rc↑ : rconv (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁)
      ≡ just (toRenameᵗ ρS₁ α′ , renameᵗ (toRenameᵗ ρS₁) R′)
    rc↑ = trans (rconv-↑ ρL₁ ρS₁ m σt) (cong (renRConv ρS₁) eq)

    psα : PreS w₁ δsβ δtβ σsβ σtβ B
    psα = PreB-ext B (PreB-↑ (pS ps) e₁) (＇ zero) ,ᵖ
      PreB-ext B (PreB-↑ (pT ps) e₁) (＇ zero)

    psβ : PreS w₁ δtβ δtg σtβ σtg B
    psβ = pT psα ,ᵖ PreB-↑ (PreB-ext B (pT ps) Tr) e₁

    hα : ConvI d N both w₁ m₁ α₁ δsβ δtβ σsβ σtβ
    hα = ConvI-extPair {β = zero} {l = Ls} gLs
      (λ e′ → new-bind Tl α (sym e′))
      (subst (λ rc → replaceRC rc (＇ zero) ≡ ＇ zero) (sym rc↑)
        (replaceTy-other (renameᵗ (toRenameᵗ ρS₁) R′)
          (λ e′ → new-bind Tr α′ (sym e′))))
      (subst (λ rc → ConvLeafP d N w₁ R₁ rc α₁ Ls Ls (＇ zero) (＇ zero))
        (sym rc↑)
        (storeConvP gLs R₁
          (just (toRenameᵗ ρS₁ α′ , renameᵗ (toRenameᵗ ρS₁) R′))
          (λ e′ → new-bind Tl α (sym e′))
          (λ e′ → new-bind Tr α′ (sym e′))))
      (storeFreshP {N = N} gLs {γ = zero} {γ′ = zero} {rk = both})
      (ConvI-↑ e₁ h)
      where
      R₁ = repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁))

    hβ : ConvI d s both w₁ (m-pair {Φ = pair Φ} ↔-here zero) zero δtβ δtg
      σtβ σtg
    hβ = ConvI-newP e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
      {Tr = Tr} (new-bind Tr) s≤N (freshT h) gLs
      (leafBelowS-good d (≤′-refl {suc s}) (sdesc Xs Ys c))
      (proj₁ (oracle h) (≤′-refl {suc s}) le (sdesc Xs Ys c) wf Tr hTr)
      (SealNewP.sealNewP d le_s (≤′-refl {suc s}) (n≤1+n s) e₁ Xs Ys c zero
        {Φ = Φ} {δt = δt} {σt = σt} zero hTr)
      (bind-Σ (ΣR w) Tr)

    clause : ℰ d s p w₁ δsβ
      (⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
      (⇑ᵗᵐ Vr ⦂∀ (bind Tr ▷ᵇ substᵗ (extsᵗ σs) B) [ ＇ zero ])
    clause =
      ℰᵍ-≡
        (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tl Vl)
          (annot Tl (δl δs) A))
        (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tr Vr)
          (annot Tr σs B))
        (ℰᵍ-map d s w₁
          (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
          (r e₁ le_s c″ (WFDesc-rename ρL₁ ρR₁ c wf) (＇ zero) refl
            (substᵗ (extsᵗ (σs ↑ˢ e₁)) B)
            (PreB-body B (PreB-↑ (pS ps) e₁))))

    R≡ : repM m₁ (δl δtβ) ≡ ⇑ᵗ R
    R≡ = trans (repM-pair (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)) (＇ zero))
      (trans (repM-↑ ρL₁ ρS₁ m (δl δt)) (shift-ty Tl R))

    rc₁≡ : rconv m₁ σtβ ≡ just (suc α′ , ⇑ᵗ R′)
    rc₁≡ = trans (rconv-pair (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁) (＇ zero))
      (trans rc↑
        (cong₂ (λ a b → just (a , b)) (embed-var Tr α′) (shift-ty Tr R′)))

    K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₂ (δsβ ↑ᴵ e₂) Ql Qr
      → ℰ d k p w₂ (δtβ ↑ᴵ e₂)
          (mplug (renameMFrame (ρL e₂) (just (reveal cL))) Ql)
          (mplug (renameMFrame (ρS e₂) (just (reveal cR))) Qr)
    K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans (revRen e₂ m₁ α₁ δsβ δtβ Ql A)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₂))
            (pk-〖〗 (embed-var Tl α) R≡ (open0 Tl (δl δs) A)))))
        (trans (rcRen e₂ m₁ σsβ σtβ Qr B)
          (trans (cong (λ rc → mplug (renameMFrame (ρS e₂)
                          (revFrame rc (substᵗ σsβ B))) Qr) rc₁≡)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρS e₂))
              (pk-〖〗 refl refl (open0 Tr σs B))))))
        (rev (ConvI-↑ e₂ hα)
            (PreM-↑ (PreM-just rc₁≡ psα) e₂
              (rconv-↑ (ρL e₂) (ρS e₂) m₁ σtβ))
            (≤-trans k≤s s≤N) ql qr q)

    K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₃ (δtβ ↑ᴵ e₃) Ql Qr
      → ℰ d k p w₃ (δtg ↑ᴵ e₃)
          (mplug (renameMFrame (ρL e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗))) Ql)
          (mplug (renameMFrame (ρS e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BtR 〗))) Qr)
    K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans (revRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) zero δtβ δtg Ql A)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
            (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δt) A)))))
        (trans (rcRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) σtβ σtg Qr B)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρS e₃))
            (pk-〖〗 refl (shift-ty Tr Tr) (open0 Tr σt B)))))
        (rev (ConvI-↑ e₃ hβ) (PreM-just refl (PreS-↑ psβ e₃))
            k≤s ql qr q)

    inner : ℰ d s p w₁ δtg
      ((⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
         ↑ cL ↑ 〖 zero , ⇑ᵗ Tl ↑ BtL 〗)
      ((⇑ᵗᵐ Vr ⦂∀ (bind Tr ▷ᵇ substᵗ (extsᵗ σs) B) [ ＇ zero ])
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
    {Ml′ : Term ΘL} {Mr : Term (storeR w)} {χL : StoreChange (ΔL w) ΘL}
  → n ≤ N → Ml —→[ χL ] Ml′
  → (tags : TyVar ΘL → Tag ΘL (ΔR w))
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ (χL ∷ [])) X)
            ≡ renameTag (embedᶜˢ (χL ∷ [])) id↪ᵗ (tag w X))
  → (∀ {s} → s ≤′ n → s ≤ N → UpB d s n
       → ℰ d s p (mkWorld ΘL (ΔR w) tags (storeR w) (pre w) (ΣR w))
           (δ ↑ᴵ stepExt {w = w} (χL ∷ []) [] (done refl) tags ok) Ml′ Mr)
  → ℰ d n p w δ Ml Mr
antiL₁ ≺ {zero} p le sl tags ok k = ℰ-zero ≺ p _
antiL₁ ≺ {suc s} p le sl tags ok k =
  ℰ-anti-≺ p (more sl none) ↠-refl (done refl) tags ok
    (k (≤′-step ≤′-refl) (≤-trans (n≤1+n s) le) tt)
antiL₁ ≻ {n} p le sl tags ok k =
  ℰ-anti-≻ p (↠-step sl ↠-refl) none (done refl) tags ok
    (k ≤′-refl le ≤-refl)

module PairRevL (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B)
    (rev : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (rconv m σt) δs δt σs σt B → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (rconv m σt) (substᵗ σs B) Vr))
    where

  pairRevL : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)}
      {α δs δt σs σt} {rk} (h : ConvI d N rk w m α δs δt σs σt)
    → substᵗ (δr δs) (`∀ B) ≡ substᵗ (δr δt) (`∀ B) → n ≤ N
    → rconv m σt ≡ nothing
    → ∀ {Vl Vr} → Value Vl → Value Vr → allPair d n p w δs Vl Vr
    → ∀ Xs Ys c → WFDesc c → ∀ {Tr} → repR Ys c ≡ ιT w Tr
    → ∀ {B₀} → substᵗ (extsᵗ (δr δt)) B
        ≡ renameᵗ (toRenameᵗ (keepᵗ (ιʷ w))) B₀
    → ℰ d n p w (extPairI (repL Xs c) (ιT w Tr)
          (sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))) δt)
        ((Vl ↑ `∀↑ 〖 suc α , ⇑ᵗ (repM m (δl δt))
                    ↑ substᵗ (extsᵗ (δl δs)) A 〗)
           ⦂∀ substᵗ (extsᵗ (δl δt)) A [ repL Xs c ])
        (Vr ⦂∀ B₀ [ Tr ])
  pairRevL {n} w {X} {m} {α} {δs} {δt} {σs} {σt} {rk} h ag le eqn {Vl} {Vr}
      vl vr r Xs Ys c wf {Tr} hTr {B₀} eqB =
    antiL₁ d p le stepL (tagsL w) (okBindL w Tl) inner
    where
    Tl = repL Xs c
    R = repM m (δl δt)
    cL = 〖 suc α , ⇑ᵗ R ↑ substᵗ (extsᵗ (δl δs)) A 〗
    BtL = substᵗ (extsᵗ (δl δt)) A
    BtR = B₀
    stepL = revInst cL vl (tgt-body α R (δl δs) (δl δt) (tyL h) A)

    e₁ = extL w Tl
    w₁ = worldL w
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    ρS₁ = ρS e₁
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    Lt = sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))
    m₁ = CMode-pair (CMode-↑ ρL₁ ρS₁ m)
    α₁ = toRenameᵗ ρL₁ α

    -- the clause's right type, in the store
    hTr₁ : repR Ys₁ c₁ ≡ ιT w₁ Tr
    hTr₁ = trans (repR-rename ρL₁ ρR₁ Ys c) (trans (renameTy-id _) hTr)

    rc↑ : rconv (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁) ≡ nothing
    rc↑ = trans (rconv-↑ ρL₁ ρS₁ m σt) (cong (renRConv ρS₁) eqn)

    rc₁≡ : rconv m₁ (Tr •ˢ (σt ↑ˢ e₁)) ≡ nothing
    rc₁≡ = trans (rconv-pair (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁) Tr) rc↑

    inner : ∀ {s} → s ≤′ n → s ≤ N → UpB d s n
      → ℰ d s p w₁ (extPairI Tl (ιT w Tr) Lt δt ↑ᴵ e₁)
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
      δsβ = extPairI (＇ zero) (ιT w₁ Tr) Ls (δs ↑ᴵ e₁)
      δtβ = extPairI (＇ zero) (ιT w₁ Tr) Ls (δt ↑ᴵ e₁)
      δtg = extPairI Tl (ιT w Tr) Lt δt ↑ᴵ e₁
      σsβ = Tr •ˢ (σs ↑ˢ e₁)
      σtβ = Tr •ˢ (σt ↑ˢ e₁)
      σtg = (Tr •ˢ σt) ↑ˢ e₁

      pmα : PreM w₁ (rconv m₁ σtβ) δsβ δtβ σsβ σtβ B
      pmα = PreM-nothing rc₁≡
        (Agree-ext B (Agree-↑ (toRenameᵗ ρR₁) (`∀ B) ag) (ιT w₁ Tr))

      pmβ : PreM w₁ nothing
        δtβ δtg σtβ σtg B
      pmβ = PreM-nothing refl (substᵗ-cong B λ
        { zero → sym (renameTy-id (ιT w Tr)) ; (suc Y) → refl })

      hα : ConvI d N left w₁ m₁ α₁ δsβ δtβ σsβ σtβ
      hα = ConvI-extPair {β = zero} {l = Ls} gLs
        (λ e′ → new-bind Tl α (sym e′))
        (subst (λ rc → replaceRC rc Tr ≡ Tr) (sym rc↑) refl)
        (subst (λ rc → ConvLeafP d N w₁
                         (repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁))) rc α₁
                         Ls Ls (＇ zero) Tr)
          (sym rc↑)
          (storeConvPN {N = N} gLs {γ = zero} {T′ = Tr}
            (repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)))
            (λ e′ → new-bind Tl α (sym e′))))
        (storeFreshPL {N = N} gLs {γ = zero} {T′ = Tr})
        (ConvI-left rc↑ (ConvI-↑ e₁ h))

      hβ : ConvI d s left w₁ (m-left {Φ = pair Φ} {X = zero}) zero δtβ δtg
        σtβ σtg
      hβ = ConvI-newL e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
        {Tr = Tr} {T′ = Tr} (sym (renameTy-id Tr)) s≤N (freshT h) gLs
        (leafBelowS-good d (≤′-refl {n}) (sdesc Xs Ys c))
        (proj₁ (oracle h) (≤′-refl {n}) le (sdesc Xs Ys c) wf Tr hTr)
        (SealNewP.sealNewL d le_s (≤′-refl {n}) (≤′⇒≤ le_s) e₁ Xs Ys c zero
          {Φ = Φ} {δt = δt} {σt = σt} {T′ = Tr} {Tr = Tr} up)

      clause : ℰ d s p w₁ δsβ
        (⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
        (Vr ⦂∀ BtR [ Tr ])
      clause =
        subst (λ T → ℰ d s p w₁ (extPairI (＇ zero) T Ls (δs ↑ᴵ e₁))
                       (⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A)
                         [ ＇ zero ])
                       (Vr ⦂∀ BtR [ Tr ]))
          hTr₁
          (ℰᵍ-≡
            (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tl Vl)
              (annot Tl (δl δs) A))
            (cong (λ M → M ⦂∀ B₀ [ Tr ]) (renameᵗᵐ-id Vr))
            (ℰᵍ-map d s w₁
              (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
              (r e₁ le_s c″ (WFDesc-rename ρL₁ ρR₁ c wf) Tr hTr₁
                B₀ (trans (substᵗ-cong B (exts-cong (λ Y →
                  renameTy-id (δr δs Y)))) (trans (∀-inj ag) eqB)))))

      R≡ : repM m₁ (δl δtβ) ≡ ⇑ᵗ R
      R≡ = trans (repM-pair (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)) (＇ zero))
        (trans (repM-↑ ρL₁ ρS₁ m (δl δt)) (shift-ty Tl R))

      K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₂ (δsβ ↑ᴵ e₂) Ql Qr
        → ℰ d k p w₂ (δtβ ↑ᴵ e₂)
            (mplug (renameMFrame (ρL e₂) (just (reveal cL))) Ql) Qr
      K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₂ m₁ α₁ δsβ δtβ Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₂))
              (pk-〖〗 (embed-var Tl α) R≡ (open0 Tl (δl δs) A)))))
          (trans (rcRen e₂ m₁ σsβ σtβ Qr B)
            (cong (λ rc → mplug (renameMFrame (ρS e₂)
                            (revFrame rc (substᵗ σsβ B))) Qr) rc₁≡))
          (rev (ConvI-↑ e₂ hα)
            (PreM-↑ pmα e₂ (rconv-↑ (ρL e₂) (ρS e₂) m₁ σtβ))
            (≤-trans k≤s s≤N) ql qr q)

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
          (rev (ConvI-↑ e₃ hβ) (PreM-↑ pmβ e₃ refl)
            k≤s ql qr q)

------------------------------------------------------------------------
-- `∀⊑∀`, the conceal, when the right converts too
------------------------------------------------------------------------

ConB-just : ∀ {Θ} d {c : TyVar Θ × Ty Θ} {k N} → k < N → ConB d (just c) k N
ConB-just ≺ lt = lt
ConB-just ≻ lt = lt

module PairCon (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B)
    (rev : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (rconv m σt) δs δt σs σt B → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (rconv m σt) (substᵗ σs B) Vr))
    (con : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (rconv m σt) δs δt σs σt B → ∀ {k}
       → ConM d m (rconv m σt) k N′
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (rconv m σt) (substᵗ σs B) Wr))
    where

  pairCon : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)}
      {α δs δt σs σt} (h : ConvI d N both w m α δs δt σs σt)
    → PreS w δs δt σs σt (`∀ B) → n ≤ N
    → ∀ {α′ R′} → rconv m σt ≡ just (α′ , R′)
    → ∀ {Wl Wr} → Value Wl → Value Wr → allPair d n p w δt Wl Wr
    → ∀ Xs Ys c → WFDesc c → ∀ {Tr} → repR Ys c ≡ ιT w Tr
    → ℰ d n p w (extPairI (repL Xs c) (ιT w Tr)
          (sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))) δs)
        ((Wl ↓ `∀↓ makeConceal (suc α) (⇑ᵗ (repM m (δl δt)))
                    (substᵗ (extsᵗ (δl δs)) A))
           ⦂∀ substᵗ (extsᵗ (δl δs)) A [ repL Xs c ])
        ((Wr ↓ `∀↓ makeConceal (suc α′) (⇑ᵗ R′)
                    (substᵗ (extsᵗ σs) B))
           ⦂∀ substᵗ (extsᵗ σs) B [ Tr ])
  pairCon {zero} w h ps le eq wl wr r Xs Ys c wf hTr = ℰ-zero d p w
  pairCon {suc s} w {X} {m} {α} {δs} {δt} {σs} {σt} h ps le {α′} {R′} eq
      {Wl} {Wr} wl wr r Xs Ys c wf {Tr} hTr =
    anti₁₁ d p stepL stepR (stᴬ w Tr) (tagsLR w Tr) (okBindLR w Tl Tr) inner
    where
    Tl = repL Xs c
    R = repM m (δl δt)
    BsL = substᵗ (extsᵗ (δl δs)) A
    BsR = substᵗ (extsᵗ σs) B
    cL = makeConceal (suc α) (⇑ᵗ R) BsL
    cR = makeConceal (suc α′) (⇑ᵗ R′) BsR

    tyR′ : ∀ Y → replaceTy α′ R′ (σs Y) ≡ σt Y
    tyR′ = subst (λ rc → ∀ Y → replaceRC rc (σs Y) ≡ σt Y) eq (tyR h)

    tgtL : replaceTy (suc α) (⇑ᵗ R) BsL ≡ substᵗ (extsᵗ (δl δt)) A
    tgtL = tgt-body α R (δl δs) (δl δt) (tyL h) A

    tgtR : replaceTy (suc α′) (⇑ᵗ R′) BsR ≡ substᵗ (extsᵗ σt) B
    tgtR = tgt-body α′ R′ σs σt tyR′ B

    stepL = conInst {T = Tl} cL wl refl
    stepR = conInst {T = Tr} cR wr refl

    e₁ = extLR w Tl Tr
    w₁ = worldLR w Tr
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    ρS₁ = ρS e₁
    β″ = toRenameᵗ (ιʷ w₁) zero
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    c″ = sdesc (zero ∷ Xs₁) (β″ ∷ Ys₁) c₁
    le_s : s ≤′ suc s
    le_s = ≤′-step ≤′-refl
    s≤N : s ≤ N
    s≤N = ≤-trans (n≤1+n s) le
    Ls = sem (leafBelowS d le_s c″)
    Lt = sem (leafBelowS d (≤′-refl {suc s}) (sdesc Xs Ys c))
    gLs = leafBelowS-good d le_s c″
    δsβ = extPairI (＇ zero) (ιT w₁ (＇ zero)) Ls (δs ↑ᴵ e₁)
    δtβ = extPairI (＇ zero) (ιT w₁ (＇ zero)) Ls (δt ↑ᴵ e₁)
    δsg = extPairI Tl (ιT w Tr) Lt δs ↑ᴵ e₁
    σsβ = ＇ zero •ˢ (σs ↑ˢ e₁)
    σtβ = ＇ zero •ˢ (σt ↑ˢ e₁)
    σsg = (Tr •ˢ σs) ↑ˢ e₁
    m₁ = CMode-pair (CMode-↑ ρL₁ ρS₁ m)
    α₁ = toRenameᵗ ρL₁ α

    rc↑ : rconv (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁)
      ≡ just (toRenameᵗ ρS₁ α′ , renameᵗ (toRenameᵗ ρS₁) R′)
    rc↑ = trans (rconv-↑ ρL₁ ρS₁ m σt) (cong (renRConv ρS₁) eq)

    psα : PreS w₁ δsβ δtβ σsβ σtβ B
    psα = PreB-ext B (PreB-↑ (pS ps) e₁) (＇ zero) ,ᵖ
      PreB-ext B (PreB-↑ (pT ps) e₁) (＇ zero)

    psβ : PreS w₁ δsβ δsg σsβ σsg B
    psβ = pS psα ,ᵖ PreB-↑ (PreB-ext B (pS ps) Tr) e₁

    hα : ConvI d N both w₁ m₁ α₁ δsβ δtβ σsβ σtβ
    hα = ConvI-extPair {β = zero} {l = Ls} gLs
      (λ e′ → new-bind Tl α (sym e′))
      (subst (λ rc → replaceRC rc (＇ zero) ≡ ＇ zero) (sym rc↑)
        (replaceTy-other (renameᵗ (toRenameᵗ ρS₁) R′)
          (λ e′ → new-bind Tr α′ (sym e′))))
      (subst (λ rc → ConvLeafP d N w₁ R₁ rc α₁ Ls Ls (＇ zero) (＇ zero))
        (sym rc↑)
        (storeConvP gLs R₁
          (just (toRenameᵗ ρS₁ α′ , renameᵗ (toRenameᵗ ρS₁) R′))
          (λ e′ → new-bind Tl α (sym e′))
          (λ e′ → new-bind Tr α′ (sym e′))))
      (storeFreshP {N = N} gLs {γ = zero} {γ′ = zero} {rk = both})
      (ConvI-↑ e₁ h)
      where
      R₁ = repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁))

    hβ : ConvI d s both w₁ (m-pair {Φ = pair Φ} ↔-here zero) zero δsβ δsg
      σsβ σsg
    hβ = ConvI-newP e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
      {Tr = Tr} (new-bind Tr) s≤N (freshS h) gLs
      (leafBelowS-good d (≤′-refl {suc s}) (sdesc Xs Ys c))
      (proj₁ (oracle h) (≤′-refl {suc s}) le (sdesc Xs Ys c) wf Tr hTr)
      (SealNewP.sealNewP d le_s (≤′-refl {suc s}) (n≤1+n s) e₁ Xs Ys c zero
        {Φ = Φ} {δt = δs} {σt = σs} zero hTr)
      (bind-Σ (ΣR w) Tr)

    clause : ℰ d s p w₁ δtβ
      (⇑ᵗᵐ Wl ⦂∀ (bind Tl ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL) [ ＇ zero ])
      (⇑ᵗᵐ Wr ⦂∀ (bind Tr ▷ᵇ replaceTy (suc α′) (⇑ᵗ R′) BsR) [ ＇ zero ])
    clause =
      ℰᵍ-≡
        (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tl Wl)
          (trans (annot Tl (δl δt) A)
            (cong (renameᵗ (extᵗ suc)) (sym tgtL))))
        (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tr Wr)
          (trans (annot Tr σt B)
            (cong (renameᵗ (extᵗ suc)) (sym tgtR))))
        (ℰᵍ-map d s w₁
          (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
          (r e₁ le_s c″ (WFDesc-rename ρL₁ ρR₁ c wf) (＇ zero) refl
            (substᵗ (extsᵗ (σt ↑ˢ e₁)) B)
            (PreB-body B (PreB-↑ (pT ps) e₁))))

    R≡ : repM m₁ (δl δtβ) ≡ ⇑ᵗ R
    R≡ = trans (repM-pair (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)) (＇ zero))
      (trans (repM-↑ ρL₁ ρS₁ m (δl δt)) (shift-ty Tl R))

    rc₁≡ : rconv m₁ σtβ ≡ just (suc α′ , ⇑ᵗ R′)
    rc₁≡ = trans (rconv-pair (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁) (＇ zero))
      (trans rc↑
        (cong₂ (λ a b → just (a , b)) (embed-var Tr α′) (shift-ty Tr R′)))

    K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₂ (δtβ ↑ᴵ e₂) Ql Qr
      → ℰ d k p w₂ (δsβ ↑ᴵ e₂)
          (mplug (renameMFrame (ρL e₂) (just (conceal cL))) Ql)
          (mplug (renameMFrame (ρS e₂) (just (conceal cR))) Qr)
    K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans (conRen e₂ m₁ α₁ δsβ δtβ Ql A)
          (↓-pk (pk-ren↓ (toRenameᵗ (ρL e₂))
            (pk-mc (embed-var Tl α) R≡ (open0 Tl (δl δs) A)))))
        (trans (ccRen e₂ m₁ σsβ σtβ Qr B)
          (trans (cong (λ rc → mplug (renameMFrame (ρS e₂)
                          (conFrame rc (substᵗ σsβ B))) Qr) rc₁≡)
            (↓-pk (pk-ren↓ (toRenameᵗ (ρS e₂))
              (pk-mc refl refl (open0 Tr σs B))))))
        (con (ConvI-↑ e₂ hα)
            (PreM-↑ (PreM-just rc₁≡ psα) e₂
              (rconv-↑ (ρL e₂) (ρS e₂) m₁ σtβ))
            cb ql qr q)
      where
      cb : ConM d (CMode-↑ (ρL e₂) (ρS e₂) m₁)
        (rconv (CMode-↑ (ρL e₂) (ρS e₂) m₁) (σtβ ↑ˢ e₂)) k N
      cb = ConMb-lt d (isNone (CMode-↑ (ρL e₂) (ρS e₂) m₁)) _
        (≤-trans (s≤s k≤s) le)

    K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₃ (δsβ ↑ᴵ e₃) Ql Qr
      → ℰ d k p w₃ (δsg ↑ᴵ e₃)
          (mplug (renameMFrame (ρL e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BsL 〗))) Ql)
          (mplug (renameMFrame (ρS e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BsR 〗))) Qr)
    K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans (revRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) zero δsβ δsg Ql A)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
            (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δs) A)))))
        (trans (rcRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) σsβ σsg Qr B)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρS e₃))
            (pk-〖〗 refl (shift-ty Tr Tr) (open0 Tr σs B)))))
        (rev (ConvI-↑ e₃ hβ) (PreM-just refl (PreS-↑ psβ e₃))
            k≤s ql qr q)

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

------------------------------------------------------------------------
-- `∀⊑∀`, the conceal, when the right does not convert
------------------------------------------------------------------------

-- the bound without a right conversion does not depend on the context
ConB-cast : ∀ {Θ Θ′} d {k N} → ConB {Θ} d nothing k N
  → ConB {Θ′} d nothing k N
ConB-cast ≺ cb = cb
ConB-cast ≻ cb = cb

module PairConL (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B)
    (rev : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (rconv m σt) δs δt σs σt B → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (rconv m σt) (substᵗ σs B) Vr))
    (con : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (rconv m σt) δs δt σs σt B → ∀ {k}
       → ConM d m (rconv m σt) k N′
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (rconv m σt) (substᵗ σs B) Wr))
    where

  pairConL : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)}
      {α δs δt σs σt} {rk} (h : ConvI d N rk w m α δs δt σs σt)
    → substᵗ (δr δs) (`∀ B) ≡ substᵗ (δr δt) (`∀ B)
    → ConM d m (rconv m σt) n N
    → rconv m σt ≡ nothing
    → ∀ {Wl Wr} → Value Wl → Value Wr → allPair d n p w δt Wl Wr
    → ∀ Xs Ys c → WFDesc c → ∀ {Tr} → repR Ys c ≡ ιT w Tr
    → ∀ {B₀} → substᵗ (extsᵗ (δr δs)) B
        ≡ renameᵗ (toRenameᵗ (keepᵗ (ιʷ w))) B₀
    → ℰ d n p w (extPairI (repL Xs c) (ιT w Tr)
          (sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))) δs)
        ((Wl ↓ `∀↓ makeConceal (suc α) (⇑ᵗ (repM m (δl δt)))
                    (substᵗ (extsᵗ (δl δs)) A))
           ⦂∀ substᵗ (extsᵗ (δl δs)) A [ repL Xs c ])
        (Wr ⦂∀ B₀ [ Tr ])
  pairConL {n} w {X} {m} {α} {δs} {δt} {σs} {σt} {rk} h ag cbn eqn {Wl} {Wr}
      wl wr r Xs Ys c wf {Tr} hTr {B₀} eqB =
    antiL₁ d p n≤N stepL (tagsL w) (okBindL w Tl) inner
    where
    cbn₀ : ConMb {storeR w} d (isNone m) nothing n N
    cbn₀ = subst (λ rc → ConMb d (isNone m) rc n N) eqn cbn

    n≤N : n ≤ N
    n≤N = ConMb-≤ d (isNone m) nothing cbn₀

    Tl = repL Xs c
    R = repM m (δl δt)
    BsL = substᵗ (extsᵗ (δl δs)) A
    BsR = B₀
    cL = makeConceal (suc α) (⇑ᵗ R) BsL

    tgtL : replaceTy (suc α) (⇑ᵗ R) BsL ≡ substᵗ (extsᵗ (δl δt)) A
    tgtL = tgt-body α R (δl δs) (δl δt) (tyL h) A

    stepL = conInst {T = Tl} cL wl refl

    e₁ = extL w Tl
    w₁ = worldL w
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    ρS₁ = ρS e₁
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    Lt = sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))
    m₁ = CMode-pair (CMode-↑ ρL₁ ρS₁ m)
    α₁ = toRenameᵗ ρL₁ α

    -- the clause's right type, in the store
    hTr₁ : repR Ys₁ c₁ ≡ ιT w₁ Tr
    hTr₁ = trans (repR-rename ρL₁ ρR₁ Ys c) (trans (renameTy-id _) hTr)

    rc↑ : rconv (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁) ≡ nothing
    rc↑ = trans (rconv-↑ ρL₁ ρS₁ m σt) (cong (renRConv ρS₁) eqn)

    rc₁≡ : rconv m₁ (Tr •ˢ (σt ↑ˢ e₁)) ≡ nothing
    rc₁≡ = trans (rconv-pair (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁) Tr) rc↑

    inner : ∀ {s} → s ≤′ n → s ≤ N → UpB d s n
      → ℰ d s p w₁ (extPairI Tl (ιT w Tr) Lt δs ↑ᴵ e₁)
          ((⇑ᵗᵐ Wl ⦂∀ (bind Tl ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL) [ ＇ zero ])
             ↓ cL ↑ 〖 zero , ⇑ᵗ Tl ↑ BsL 〗)
          (Wr ⦂∀ BsR [ Tr ])
    inner {s} le_s s≤N up =
      ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δsg}
        (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BsL 〗)) nothing
        (ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δsβ}
          (just (conceal cL)) nothing clause K₁)
        K₂
      where
      c″ = sdesc (zero ∷ Xs₁) Ys₁ c₁
      Ls = sem (leafBelowS d le_s c″)
      gLs = leafBelowS-good d le_s c″
      δsβ = extPairI (＇ zero) (ιT w₁ Tr) Ls (δs ↑ᴵ e₁)
      δtβ = extPairI (＇ zero) (ιT w₁ Tr) Ls (δt ↑ᴵ e₁)
      δsg = extPairI Tl (ιT w Tr) Lt δs ↑ᴵ e₁
      σsβ = Tr •ˢ (σs ↑ˢ e₁)
      σtβ = Tr •ˢ (σt ↑ˢ e₁)
      σsg = (Tr •ˢ σs) ↑ˢ e₁

      pmα : PreM w₁ (rconv m₁ σtβ) δsβ δtβ σsβ σtβ B
      pmα = PreM-nothing rc₁≡
        (Agree-ext B (Agree-↑ (toRenameᵗ ρR₁) (`∀ B) ag) (ιT w₁ Tr))

      pmβ : PreM w₁ nothing
        δsβ δsg σsβ σsg B
      pmβ = PreM-nothing refl (substᵗ-cong B λ
        { zero → sym (renameTy-id (ιT w Tr)) ; (suc Y) → refl })

      hα : ConvI d N left w₁ m₁ α₁ δsβ δtβ σsβ σtβ
      hα = ConvI-extPair {β = zero} {l = Ls} gLs
        (λ e′ → new-bind Tl α (sym e′))
        (subst (λ rc → replaceRC rc Tr ≡ Tr) (sym rc↑) refl)
        (subst (λ rc → ConvLeafP d N w₁
                         (repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁))) rc α₁
                         Ls Ls (＇ zero) Tr)
          (sym rc↑)
          (storeConvPN {N = N} gLs {γ = zero} {T′ = Tr}
            (repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)))
            (λ e′ → new-bind Tl α (sym e′))))
        (storeFreshPL {N = N} gLs {γ = zero} {T′ = Tr})
        (ConvI-left rc↑ (ConvI-↑ e₁ h))

      hβ : ConvI d s left w₁ (m-left {Φ = pair Φ} {X = zero}) zero δsβ δsg
        σsβ σsg
      hβ = ConvI-newL e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
        {Tr = Tr} {T′ = Tr} (sym (renameTy-id Tr)) s≤N (freshS h) gLs
        (leafBelowS-good d (≤′-refl {n}) (sdesc Xs Ys c))
        (proj₁ (oracle h) (≤′-refl {n}) n≤N (sdesc Xs Ys c) wf Tr hTr)
        (SealNewP.sealNewL d le_s (≤′-refl {n}) (≤′⇒≤ le_s) e₁ Xs Ys c zero
          {Φ = Φ} {δt = δs} {σt = σs} {T′ = Tr} {Tr = Tr} up)

      clause : ℰ d s p w₁ δtβ
        (⇑ᵗᵐ Wl ⦂∀ (bind Tl ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL) [ ＇ zero ])
        (Wr ⦂∀ BsR [ Tr ])
      clause =
        subst (λ T → ℰ d s p w₁ (extPairI (＇ zero) T Ls (δt ↑ᴵ e₁))
                       (⇑ᵗᵐ Wl ⦂∀ (bind Tl ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL)
                         [ ＇ zero ])
                       (Wr ⦂∀ BsR [ Tr ]))
          hTr₁
          (ℰᵍ-≡
            (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tl Wl)
              (trans (annot Tl (δl δt) A)
                (cong (renameᵗ (extᵗ suc)) (sym tgtL))))
            (cong (λ M → M ⦂∀ B₀ [ Tr ]) (renameᵗᵐ-id Wr))
            (ℰᵍ-map d s w₁
              (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
              (r e₁ le_s c″ (WFDesc-rename ρL₁ ρR₁ c wf) Tr hTr₁
                B₀ (trans (substᵗ-cong B (exts-cong (λ Y →
                  renameTy-id (δr δt Y)))) (trans (sym (∀-inj ag)) eqB)))))

      R≡ : repM m₁ (δl δtβ) ≡ ⇑ᵗ R
      R≡ = trans (repM-pair (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)) (＇ zero))
        (trans (repM-↑ ρL₁ ρS₁ m (δl δt)) (shift-ty Tl R))

      K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₂ (δtβ ↑ᴵ e₂) Ql Qr
        → ℰ d k p w₂ (δsβ ↑ᴵ e₂)
            (mplug (renameMFrame (ρL e₂) (just (conceal cL))) Ql) Qr
      K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (conRen e₂ m₁ α₁ δsβ δtβ Ql A)
            (↓-pk (pk-ren↓ (toRenameᵗ (ρL e₂))
              (pk-mc (embed-var Tl α) R≡ (open0 Tl (δl δs) A)))))
          (trans (ccRen e₂ m₁ σsβ σtβ Qr B)
            (cong (λ rc → mplug (renameMFrame (ρS e₂)
                            (conFrame rc (substᵗ σsβ B))) Qr) rc₁≡))
          (con (ConvI-↑ e₂ hα)
            (PreM-↑ pmα e₂ (rconv-↑ (ρL e₂) (ρS e₂) m₁ σtβ))
            cb ql qr q)
        where
        cb : ConM d (CMode-↑ (ρL e₂) (ρS e₂) m₁)
          (rconv (CMode-↑ (ρL e₂) (ρS e₂) m₁) (σtβ ↑ˢ e₂)) k N
        cb = subst
          (λ rc → ConMb d (isNone (CMode-↑ (ρL e₂) (ρS e₂) m₁)) rc k N)
          (sym (trans (rconv-↑ (ρL e₂) (ρS e₂) m₁ σtβ)
            (cong (renRConv (ρS e₂)) rc₁≡)))
          (subst (λ b → ConMb d b nothing k N)
            (sym (trans (isNone-↑ (ρL e₂) (ρS e₂) m₁)
              (trans (isNone-pair (CMode-↑ ρL₁ ρS₁ m))
                (isNone-↑ ρL₁ ρS₁ m))))
            (ConMb-cast d (isNone m)
              (ConMb-down d (isNone m) nothing (≤-trans k≤s (≤′⇒≤ le_s))
                cbn₀)))

      K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₃ (δsβ ↑ᴵ e₃) Ql Qr
        → ℰ d k p w₃ (δsg ↑ᴵ e₃)
            (mplug (renameMFrame (ρL e₃)
              (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BsL 〗))) Ql) Qr
      K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₃ (m-left {Φ = pair Φ} {X = zero}) zero δsβ δsg Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
              (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δs) A)))))
          refl
          (rev (ConvI-↑ e₃ hβ) (PreM-↑ pmβ e₃ refl)
            k≤s ql qr q)

------------------------------------------------------------------------
-- `∀⊑`, the reveal: only the left instantiates
------------------------------------------------------------------------

-- the leaf bound of a left-only clause whose body is read at stage n′:
-- n′ ∸ g, where g is 0, or 1 for the guarded clause (`allOnlyG`,
-- notes/logrel-dgg.md, F2)
leafLe : ∀ g {n′ n} → n′ ≤′ n → n′ ∸ g ≤′ n
leafLe zero le = le
leafLe (suc g) {n′} le = ≤′-trans (≤⇒≤′ (m∸n≤m n′ (suc g))) le

-- the left-only clause with that leaf bound; at g = 0 it is `allOnly`
OnlyCl : Dir → ℕ → ℕ → ∀ {Φ : Corr Δ Δ′} {A B} → only Φ ⊢ A ⊑ B
  → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
  → Term (ΔL w) → Term (storeR w) → Set
OnlyCl d g n {A = A} p w δ Vl Vr =
  ∀ {w′} (e : w′ ⊒ w) {n′} (le : n′ ≤′ n) (c : SDesc (ΔL w′) (ΔR w′))
  → OnlyS c
  → ℰᵍ d n′ w′
      (λ le′ w″ e′ → 𝒱≤ d (≤′-trans le′ le) p w″
        (extOnlyI (leftTyS c) (sem (onlyLeafS d (leafLe g le) c))
          (δ ↑ᴵ e) ↑ᴵ e′))
      (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A [ leftTyS c ])
      (renameᵗᵐ (ρS e) Vr)

-- the arithmetic of the slack g: the clause's stage may exceed the bound
-- by g, and the new variable's leaf is bounded by the stage minus g
∸-slack : ∀ {s} g {N} → s ≤ g + N → s ∸ g ≤ N
∸-slack {s} zero le = le
∸-slack {zero} (suc g) le = z≤n
∸-slack {suc s} (suc g) (s≤s le) = ∸-slack g le

slack-∸ : ∀ s g → s ≤ g + (s ∸ g)
slack-∸ s zero = ≤-refl
slack-∸ zero (suc g) = z≤n
slack-∸ (suc s) (suc g) = s≤s (slack-∸ s g)

∸-mono : ∀ {s n} g → s ≤ n → s ∸ g ≤ n ∸ g
∸-mono g le = ∸-monoˡ-≤ g le

UpB-∸ : ∀ d {s n} g → UpB d s n → UpB d (s ∸ g) (n ∸ g)
UpB-∸ ≺ g up = tt
UpB-∸ ≻ g up = ∸-mono g up

-- the right side's conversion is `RF`: `rconv` in the main lemma,
-- nothing in the `★` lemma; g is the slack (`leafLe`)
module OnlyRev (d : Dir) (g : ℕ) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : only Φ ⊢ A ⊑ B)
    (RF : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
       → CMode Ψ X′ ΘL ΘR → (Δ′ ⇒ˢ ΘR) → RConv ΘR)
    (RF-↑ : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR ΘL′ ΘR′}
       (ρL : ΘL ↪ᵗ ΘL′) (ρR : ΘR ↪ᵗ ΘR′) (m : CMode Ψ X′ ΘL ΘR) σ
       → RF (CMode-↑ ρL ρR m) (λ Y → renameᵗ (toRenameᵗ ρR) (σ Y))
         ≡ renRConv ρR (RF m σ))
    (RF-only : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
       (m : CMode Ψ X′ ΘL ΘR) σ → RF (CMode-only m) σ ≡ RF m σ)
    (RF-left : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
       (σ : Δ′ ⇒ˢ ΘR) → RF (m-left {Φ = Ψ} {X = X′} {ΘL = ΘL}) σ ≡ nothing)
    (rev : ∀ {N′ rk w X′} {m : CMode (only Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt B → ∀ {k} → k ≤ g + N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (RF m σt) (substᵗ σs B) Vr))
    where

  -- the right side's conversion, renamed into a future
  rfRen : ∀ {w w′ : World} (e : w′ ⊒ w) {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′}
      (m : CMode Ψ X′ (ΔL w) (storeR w)) (σs σt : Δ′ ⇒ˢ storeR w)
      (Q : Term (storeR w′)) C
    → revM (RF (CMode-↑ (ρL e) (ρS e) m) (σt ↑ˢ e))
        (substᵗ (σs ↑ˢ e) C) Q
      ≡ mplug (renameMFrame (ρS e)
          (revFrame (RF m σt) (substᵗ σs C))) Q
  rfRen e m σs σt Q C =
    trans (cong (λ c → revM c _ Q) (RF-↑ (ρL e) (ρS e) m σt))
      (sym (revFrame-ren (ρS e) (RF m σt) σs C Q))

  onlyRev : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)}
      {α δs δt σs σt} {rk} (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (RF m σt) δs δt σs σt B → n ≤ g + N
    → ∀ {Vl Vr} → Value Vl → Value Vr → OnlyCl d g n p w δs Vl Vr
    → ∀ Xs Ys c → OnlyS (sdesc Xs Ys c)
    → ℰ d n p w (extOnlyI (repL Xs c)
          (sem (onlyLeafS d (leafLe g (≤′-refl {n})) (sdesc Xs Ys c))) δt)
        ((Vl ↑ `∀↑ 〖 suc α , ⇑ᵗ (repM m (δl δt))
                    ↑ substᵗ (extsᵗ (δl δs)) A 〗)
           ⦂∀ substᵗ (extsᵗ (δl δt)) A [ repL Xs c ])
        (revM (RF m σt) (substᵗ σs B) Vr)
  onlyRev {n} w {X} {m} {α} {δs} {δt} {σs} {σt} {rk} h ps le {Vl} {Vr} vl vr r
      Xs Ys c oc =
    antiL₁ d p le stepL (tagsL w) (okBindL w Tl) inner
    where
    Tl = repL Xs c
    R = repM m (δl δt)
    cL = 〖 suc α , ⇑ᵗ R ↑ substᵗ (extsᵗ (δl δs)) A 〗
    BtL = substᵗ (extsᵗ (δl δt)) A
    BsR = substᵗ σs B
    Fr = revFrame (RF m σt) BsR
    stepL = revInst cL vl (tgt-body α R (δl δs) (δl δt) (tyL h) A)

    e₁ = extL w Tl
    w₁ = worldL w
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    ρS₁ = ρS e₁
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    Lt = sem (onlyLeafS d (leafLe g (≤′-refl {n})) (sdesc Xs Ys c))
    m₁ = CMode-only (CMode-↑ ρL₁ ρS₁ m)
    α₁ = toRenameᵗ ρL₁ α

    -- the right side's conversion in w₁, whose right store is w's
    rf₁ : RF m₁ (σt ↑ˢ e₁) ≡ RF m σt
    rf₁ = trans (RF-only (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁))
      (trans (RF-↑ ρL₁ ρS₁ m σt) (renRConv-id (RF m σt)))

    BR≡ : substᵗ (σs ↑ˢ e₁) B ≡ BsR
    BR≡ = substᵗ-cong B (λ Y → renameTy-id (σs Y))

    R≡ : repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)) ≡ ⇑ᵗ R
    R≡ = trans (repM-↑ ρL₁ ρS₁ m (δl δt)) (shift-ty Tl R)

    inner : ∀ {s} → s ≤′ n → s ≤ g + N → UpB d s n
      → ℰ d s p w₁ (extOnlyI Tl Lt δt ↑ᴵ e₁)
          ((⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
             ↑ cL ↑ 〖 zero , ⇑ᵗ Tl ↑ BtL 〗)
          (mplug Fr Vr)
    inner {s} le_s s≤N up =
      ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δtg}
        (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗)) nothing
        (ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δtβ}
          (just (reveal cL)) Fr clause K₁)
        K₂
      where
      c″ = sdesc (zero ∷ Xs₁) Ys₁ c₁
      Ls = sem (onlyLeafS d (leafLe g le_s) c″)
      gLs = onlyLeafS-good d (leafLe g le_s) c″
      δsβ = extOnlyI (＇ zero) Ls (δs ↑ᴵ e₁)
      δtβ = extOnlyI (＇ zero) Ls (δt ↑ᴵ e₁)
      δtg = extOnlyI Tl Lt δt ↑ᴵ e₁

      pmα : PreM w₁ (RF m₁ (σt ↑ˢ e₁)) δsβ δtβ (σs ↑ˢ e₁) (σt ↑ˢ e₁) B
      pmα = PreM-re refl refl (PreM-↑ ps e₁
        (trans (RF-only (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁))
          (RF-↑ ρL₁ ρS₁ m σt)))

      pmβ : PreM w₁ (RF (m-left {Φ = only Φ} {X = zero}) (σt ↑ˢ e₁))
        δtβ δtg (σt ↑ˢ e₁) (σt ↑ˢ e₁) B
      pmβ = PreM-nothing (RF-left (σt ↑ˢ e₁)) refl

      hα : ConvI d N rk w₁ m₁ α₁ δsβ δtβ (σs ↑ˢ e₁) (σt ↑ˢ e₁)
      hα = ConvI-extOnly {β = zero} {l = Ls} gLs
        (λ e′ → new-bind Tl α (sym e′))
        (storeConvO {d = d} {w = w₁} {L = Ls} gLs {γ = zero} {N = N}
          (repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)))
          (λ e′ → new-bind Tl α (sym e′)))
        (storeFreshO {d = d} {w = w₁} {L = Ls} gLs {γ = zero})
        (ConvI-↑ e₁ h)

      hβ : ConvI d (s ∸ g) rk w₁ (m-left {Φ = only Φ} {X = zero}) zero δtβ
        δtg (σt ↑ˢ e₁) (σt ↑ˢ e₁)
      hβ = ConvI-newO e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
        (∸-slack g s≤N)
        (freshT h) gLs
        (onlyLeafS-good d (leafLe g (≤′-refl {n})) (sdesc Xs Ys c))
        (proj₂ (oracle h) (leafLe g (≤′-refl {n})) (∸-slack g le)
          (sdesc Xs Ys c))
        (SealNewO.sealNewO d (leafLe g le_s) (leafLe g (≤′-refl {n}))
          (∸-mono g (≤′⇒≤ le_s)) e₁ Xs Ys c zero
          {Φ = Φ} {δt = δt} {σt = σt} (UpB-∸ d g up))

      clause : ℰ d s p w₁ δsβ
        (⇑ᵗᵐ Vl ⦂∀ (bind Tl ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ]) Vr
      clause =
        ℰᵍ-≡
          (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tl Vl)
            (annot Tl (δl δs) A))
          (renameᵗᵐ-id Vr)
          (ℰᵍ-map d s w₁
            (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
            (r e₁ le_s c″ (OnlyS-rename ρL₁ ρR₁ c oc)))

      K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₂ (δsβ ↑ᴵ e₂) Ql Qr
        → ℰ d k p w₂ (δtβ ↑ᴵ e₂)
            (mplug (renameMFrame (ρL e₂) (just (reveal cL))) Ql)
            (mplug (renameMFrame (ρS e₂) Fr) Qr)
      K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₂ m₁ α₁ δsβ δtβ Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₂))
              (pk-〖〗 (embed-var Tl α)
                (trans (repM-only (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁))
                         (＇ zero)) R≡)
                (open0 Tl (δl δs) A)))))
          (trans (rfRen e₂ m₁ (σs ↑ˢ e₁) (σt ↑ˢ e₁) Qr B)
            (cong (λ F → mplug (renameMFrame (ρS e₂) F) Qr)
              (cong₂ revFrame rf₁ BR≡)))
          (rev (ConvI-↑ e₂ hα)
            (PreM-↑ pmα e₂ (RF-↑ (ρL e₂) (ρS e₂) m₁ (σt ↑ˢ e₁)))
            (≤-trans k≤s s≤N) ql qr q)

      K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₃ (δtβ ↑ᴵ e₃) Ql Qr
        → ℰ d k p w₃ (δtg ↑ᴵ e₃)
            (mplug (renameMFrame (ρL e₃)
              (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗))) Ql) Qr
      K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₃ (m-left {Φ = only Φ} {X = zero}) zero δtβ δtg Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
              (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δt) A)))))
          (cong (λ c → revM c (substᵗ ((σt ↑ˢ e₁) ↑ˢ e₃) B) Qr)
            (RF-left ((σt ↑ˢ e₁) ↑ˢ e₃)))
          (rev (ConvI-↑ e₃ hβ)
            (PreM-↑ pmβ e₃
              (RF-↑ (ρL e₃) (ρS e₃) (m-left {Φ = only Φ} {X = zero})
                (σt ↑ˢ e₁)))
            (≤-trans k≤s (slack-∸ s g)) ql qr q)

------------------------------------------------------------------------
-- `∀⊑`, the conceal
------------------------------------------------------------------------

module OnlyCon (d : Dir) (g : ℕ) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : only Φ ⊢ A ⊑ B)
    (RF : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
       → CMode Ψ X′ ΘL ΘR → (Δ′ ⇒ˢ ΘR) → RConv ΘR)
    (RF-↑ : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR ΘL′ ΘR′}
       (ρL : ΘL ↪ᵗ ΘL′) (ρR : ΘR ↪ᵗ ΘR′) (m : CMode Ψ X′ ΘL ΘR) σ
       → RF (CMode-↑ ρL ρR m) (λ Y → renameᵗ (toRenameᵗ ρR) (σ Y))
         ≡ renRConv ρR (RF m σ))
    (RF-only : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
       (m : CMode Ψ X′ ΘL ΘR) σ → RF (CMode-only m) σ ≡ RF m σ)
    (RF-left : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
       (σ : Δ′ ⇒ˢ ΘR) → RF (m-left {Φ = Ψ} {X = X′} {ΘL = ΘL}) σ ≡ nothing)
    (rev : ∀ {N′ rk w X′} {m : CMode (only Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt B → ∀ {k} → k ≤ g + N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (RF m σt) (substᵗ σs B) Vr))
    (con : ∀ {N′ rk w X′} {m : CMode (only Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt B → ∀ {k}
       → ConM d m (RF m σt) k (g + N′)
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (RF m σt) (substᵗ σs B) Wr))
    where

  -- the right side's conceal, renamed into a future
  cfRen : ∀ {w w′ : World} (e : w′ ⊒ w) {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′}
      (m : CMode Ψ X′ (ΔL w) (storeR w)) (σs σt : Δ′ ⇒ˢ storeR w)
      (Q : Term (storeR w′)) C
    → conM (RF (CMode-↑ (ρL e) (ρS e) m) (σt ↑ˢ e))
        (substᵗ (σs ↑ˢ e) C) Q
      ≡ mplug (renameMFrame (ρS e)
          (conFrame (RF m σt) (substᵗ σs C))) Q
  cfRen e m σs σt Q C =
    trans (cong (λ c → conM c _ Q) (RF-↑ (ρL e) (ρS e) m σt))
      (sym (conFrame-ren (ρS e) (RF m σt) σs C Q))

  onlyCon : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)}
      {α δs δt σs σt} {rk} (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (RF m σt) δs δt σs σt B → ConM d m (RF m σt) n (g + N)
    → ∀ {Wl Wr} → Value Wl → Value Wr → OnlyCl d g n p w δt Wl Wr
    → ∀ Xs Ys c → OnlyS (sdesc Xs Ys c)
    → ℰ d n p w (extOnlyI (repL Xs c)
          (sem (onlyLeafS d (leafLe g (≤′-refl {n})) (sdesc Xs Ys c))) δs)
        ((Wl ↓ `∀↓ makeConceal (suc α) (⇑ᵗ (repM m (δl δt)))
                    (substᵗ (extsᵗ (δl δs)) A))
           ⦂∀ substᵗ (extsᵗ (δl δs)) A [ repL Xs c ])
        (conM (RF m σt) (substᵗ σs B) Wr)
  onlyCon {n} w {X} {m} {α} {δs} {δt} {σs} {σt} {rk} h ps cbn {Wl} {Wr}
      wl wr r Xs Ys c oc =
    antiL₁ d p n≤N stepL (tagsL w) (okBindL w Tl) inner
    where
    rc = RF m σt
    n≤N : n ≤ g + N
    n≤N = ConMb-≤ d (isNone m) rc cbn
    Tl = repL Xs c
    R = repM m (δl δt)
    BsL = substᵗ (extsᵗ (δl δs)) A
    cL = makeConceal (suc α) (⇑ᵗ R) BsL
    BsR = substᵗ σs B
    Fr = conFrame rc BsR

    tgtL : replaceTy (suc α) (⇑ᵗ R) BsL ≡ substᵗ (extsᵗ (δl δt)) A
    tgtL = tgt-body α R (δl δs) (δl δt) (tyL h) A

    stepL = conInst {T = Tl} cL wl refl

    e₁ = extL w Tl
    w₁ = worldL w
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    ρS₁ = ρS e₁
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    Lt = sem (onlyLeafS d (leafLe g (≤′-refl {n})) (sdesc Xs Ys c))
    m₁ = CMode-only (CMode-↑ ρL₁ ρS₁ m)
    α₁ = toRenameᵗ ρL₁ α

    rf₁ : RF m₁ (σt ↑ˢ e₁) ≡ rc
    rf₁ = trans (RF-only (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁))
      (trans (RF-↑ ρL₁ ρS₁ m σt) (renRConv-id rc))

    BR≡ : substᵗ (σs ↑ˢ e₁) B ≡ BsR
    BR≡ = substᵗ-cong B (λ Y → renameTy-id (σs Y))

    R≡ : repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)) ≡ ⇑ᵗ R
    R≡ = trans (repM-↑ ρL₁ ρS₁ m (δl δt)) (shift-ty Tl R)

    inner : ∀ {s} → s ≤′ n → s ≤ g + N → UpB d s n
      → ℰ d s p w₁ (extOnlyI Tl Lt δs ↑ᴵ e₁)
          ((⇑ᵗᵐ Wl ⦂∀ (bind Tl ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL) [ ＇ zero ])
             ↓ cL ↑ 〖 zero , ⇑ᵗ Tl ↑ BsL 〗)
          (mplug Fr Wr)
    inner {s} le_s s≤N up =
      ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δsg}
        (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BsL 〗)) nothing
        (ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δsβ}
          (just (conceal cL)) Fr clause K₁)
        K₂
      where
      c″ = sdesc (zero ∷ Xs₁) Ys₁ c₁
      Ls = sem (onlyLeafS d (leafLe g le_s) c″)
      gLs = onlyLeafS-good d (leafLe g le_s) c″
      δsβ = extOnlyI (＇ zero) Ls (δs ↑ᴵ e₁)
      δtβ = extOnlyI (＇ zero) Ls (δt ↑ᴵ e₁)
      δsg = extOnlyI Tl Lt δs ↑ᴵ e₁

      pmα : PreM w₁ (RF m₁ (σt ↑ˢ e₁)) δsβ δtβ (σs ↑ˢ e₁) (σt ↑ˢ e₁) B
      pmα = PreM-re refl refl (PreM-↑ ps e₁
        (trans (RF-only (CMode-↑ ρL₁ ρS₁ m) (σt ↑ˢ e₁))
          (RF-↑ ρL₁ ρS₁ m σt)))

      pmβ : PreM w₁ (RF (m-left {Φ = only Φ} {X = zero}) (σs ↑ˢ e₁))
        δsβ δsg (σs ↑ˢ e₁) (σs ↑ˢ e₁) B
      pmβ = PreM-nothing (RF-left (σs ↑ˢ e₁)) refl

      hα : ConvI d N rk w₁ m₁ α₁ δsβ δtβ (σs ↑ˢ e₁) (σt ↑ˢ e₁)
      hα = ConvI-extOnly {β = zero} {l = Ls} gLs
        (λ e′ → new-bind Tl α (sym e′))
        (storeConvO {d = d} {w = w₁} {L = Ls} gLs {γ = zero} {N = N}
          (repM (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)))
          (λ e′ → new-bind Tl α (sym e′)))
        (storeFreshO {d = d} {w = w₁} {L = Ls} gLs {γ = zero})
        (ConvI-↑ e₁ h)

      hβ : ConvI d (s ∸ g) rk w₁ (m-left {Φ = only Φ} {X = zero}) zero δsβ
        δsg (σs ↑ˢ e₁) (σs ↑ˢ e₁)
      hβ = ConvI-newO e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
        (∸-slack g s≤N)
        (freshS h) gLs
        (onlyLeafS-good d (leafLe g (≤′-refl {n})) (sdesc Xs Ys c))
        (proj₂ (oracle h) (leafLe g (≤′-refl {n})) (∸-slack g n≤N)
          (sdesc Xs Ys c))
        (SealNewO.sealNewO d (leafLe g le_s) (leafLe g (≤′-refl {n}))
          (∸-mono g (≤′⇒≤ le_s)) e₁ Xs Ys c zero
          {Φ = Φ} {δt = δs} {σt = σs} (UpB-∸ d g up))

      clause : ℰ d s p w₁ δtβ
        (⇑ᵗᵐ Wl ⦂∀ (bind Tl ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL) [ ＇ zero ]) Wr
      clause =
        ℰᵍ-≡
          (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tl Wl)
            (trans (annot Tl (δl δt) A)
              (cong (renameᵗ (extᵗ suc)) (sym tgtL))))
          (renameᵗᵐ-id Wr)
          (ℰᵍ-map d s w₁
            (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
            (r e₁ le_s c″ (OnlyS-rename ρL₁ ρR₁ c oc)))

      K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₂ (δtβ ↑ᴵ e₂) Ql Qr
        → ℰ d k p w₂ (δsβ ↑ᴵ e₂)
            (mplug (renameMFrame (ρL e₂) (just (conceal cL))) Ql)
            (mplug (renameMFrame (ρS e₂) Fr) Qr)
      K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (conRen e₂ m₁ α₁ δsβ δtβ Ql A)
            (↓-pk (pk-ren↓ (toRenameᵗ (ρL e₂))
              (pk-mc (embed-var Tl α)
                (trans (repM-only (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁))
                         (＇ zero)) R≡)
                (open0 Tl (δl δs) A)))))
          (trans (cfRen e₂ m₁ (σs ↑ˢ e₁) (σt ↑ˢ e₁) Qr B)
            (cong (λ F → mplug (renameMFrame (ρS e₂) F) Qr)
              (cong₂ conFrame rf₁ BR≡)))
          (con (ConvI-↑ e₂ hα)
            (PreM-↑ pmα e₂ (RF-↑ (ρL e₂) (ρS e₂) m₁ (σt ↑ˢ e₁)))
            cb ql qr q)
        where
        cb : ConM d (CMode-↑ (ρL e₂) (ρS e₂) m₁)
          (RF (CMode-↑ (ρL e₂) (ρS e₂) m₁) ((σt ↑ˢ e₁) ↑ˢ e₂)) k (g + N)
        cb = subst
          (λ rc′ →
            ConMb d (isNone (CMode-↑ (ρL e₂) (ρS e₂) m₁)) rc′ k (g + N))
          (sym (trans (RF-↑ (ρL e₂) (ρS e₂) m₁ (σt ↑ˢ e₁))
            (cong (renRConv (ρS e₂)) rf₁)))
          (subst (λ b → ConMb d b (renRConv (ρS e₂) rc) k (g + N))
            (sym (trans (isNone-↑ (ρL e₂) (ρS e₂) m₁)
              (trans (isNone-only (CMode-↑ ρL₁ ρS₁ m))
                (isNone-↑ ρL₁ ρS₁ m))))
            (ConMb-ren d (isNone m) (ρS e₂) rc
              (ConMb-down d (isNone m) rc (≤-trans k≤s (≤′⇒≤ le_s)) cbn)))

      K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₃ (δsβ ↑ᴵ e₃) Ql Qr
        → ℰ d k p w₃ (δsg ↑ᴵ e₃)
            (mplug (renameMFrame (ρL e₃)
              (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BsL 〗))) Ql) Qr
      K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₃ (m-left {Φ = only Φ} {X = zero}) zero δsβ δsg Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
              (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δs) A)))))
          (cong (λ c′ → revM c′ (substᵗ ((σs ↑ˢ e₁) ↑ˢ e₃) B) Qr)
            (RF-left ((σs ↑ˢ e₁) ↑ˢ e₃)))
          (rev (ConvI-↑ e₃ hβ)
            (PreM-↑ pmβ e₃
              (RF-↑ (ρL e₃) (ρS e₃) (m-left {Φ = only Φ} {X = zero})
                (σs ↑ˢ e₁)))
            (≤-trans k≤s (slack-∸ s g)) ql qr q)

------------------------------------------------------------------------
-- `∀⊑★`, in the `★` lemma: the left instantiates, the bound variable is
-- dead, and the right is the `∀★` payload, instantiated as it is
------------------------------------------------------------------------

module DeadConv (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A}
    (p : dead Φ ⊢ A ⊑ ★)
    (rev : ∀ {N′ rk w X′} {m : CMode (dead Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           Vr)
    (con : ∀ {N′ rk w X′} {m : CMode (dead Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt → ∀ {k}
       → ConM d m nothing k N′
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A)) Wr)
    where

  module Step (w : World) (T : Ty (ΔL w)) where
    e₁ = extL w T
    w₁ = worldL w
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    ρS₁ = ρS e₁

  deadRev : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)}
      {α δs δt σs σt} {rk} (h : ConvI d N rk w m α δs δt σs σt) → n ≤ N
    → ∀ {Vl Wr} → Value Vl → allDead d n p w δs Vl Wr
    → ∀ Xs Ys c → WFDesc c → ∀ {T′} → repR Ys c ≡ ιT w T′
    → ℰ d n p w (extDeadI (repL Xs c) δt)
        ((Vl ↑ `∀↑ 〖 suc α , ⇑ᵗ (repM m (δl δt))
                    ↑ substᵗ (extsᵗ (δl δs)) A 〗)
           ⦂∀ substᵗ (extsᵗ (δl δt)) A [ repL Xs c ])
        (Wr ⦂∀ ★ [ T′ ])
  deadRev {n} w {X} {m} {α} {δs} {δt} {σs} {σt} {rk} h le {Vl} {Wr} vl r
    Xs Ys c wf {T′} hTr =
    antiL₁ d p le stepL (tagsL w) (okBindL w T) inner
    where
    T = repL Xs c
    open Step w T
    c″ = sdesc (zero ∷ map (renameVar ρL₁) Xs) (map (renameVar ρR₁) Ys)
      (renameDesc ρL₁ ρR₁ c)
    hTr₁ : rightTyS c″ ≡ ιT w₁ T′
    hTr₁ = trans (repR-rename ρL₁ ρR₁ Ys c) (trans (renameTy-id _) hTr)
    R = repM m (δl δt)
    cL = 〖 suc α , ⇑ᵗ R ↑ substᵗ (extsᵗ (δl δs)) A 〗
    BtL = substᵗ (extsᵗ (δl δt)) A
    stepL = revInst cL vl (tgt-body α R (δl δs) (δl δt) (tyL h) A)
    m₁ = CMode-dead (CMode-↑ ρL₁ ρS₁ m)
    α₁ = toRenameᵗ ρL₁ α
    δsβ = extDeadI (＇ zero) (δs ↑ᴵ e₁)
    δtβ = extDeadI (＇ zero) (δt ↑ᴵ e₁)
    δtg = extDeadI T δt ↑ᴵ e₁

    R≡ : repM m₁ (δl δtβ) ≡ ⇑ᵗ R
    R≡ = trans (repM-dead (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)) (＇ zero))
      (trans (repM-↑ ρL₁ ρS₁ m (δl δt)) (shift-ty T R))

    hα : ConvI d N rk w₁ m₁ α₁ δsβ δtβ (σs ↑ˢ e₁) (σt ↑ˢ e₁)
    hα = ConvI-extDead {β = zero} (λ e′ → new-bind T α (sym e′))
      (ConvI-↑ e₁ h)

    inner : ∀ {s} → s ≤′ n → s ≤ N → UpB d s n
      → ℰ d s p w₁ δtg
          ((⇑ᵗᵐ Vl ⦂∀ (bind T ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
             ↑ cL ↑ 〖 zero , ⇑ᵗ T ↑ BtL 〗)
          (Wr ⦂∀ ★ [ T′ ])
    inner {s} le_s s≤N up =
      ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δtg}
        (just (reveal 〖 zero , ⇑ᵗ T ↑ BtL 〗)) nothing
        (ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δtβ}
          (just (reveal cL)) nothing clause K₁)
        K₂
      where
      hβ : ConvI d s rk w₁ (m-dead {Φ = dead Φ} dead-here) zero δtβ δtg
        (σt ↑ˢ e₁) (σt ↑ˢ e₁)
      hβ = ConvI-newD e₁ (new-bind T) {Ls = sem ⊤Ω} {Lt = sem ⊤Ω} {Tl = T}
        s≤N (freshT h)

      clause : ℰ d s p w₁ δsβ
        (⇑ᵗᵐ Vl ⦂∀ (bind T ▷ᵇ substᵗ (extsᵗ (δl δs)) A) [ ＇ zero ])
        (Wr ⦂∀ ★ [ T′ ])
      clause =
        ℰᵍ-≡
          (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term T Vl)
            (annot T (δl δs) A))
          (cong (λ M → M ⦂∀ ★ [ T′ ]) (renameᵗᵐ-id Wr))
          (ℰᵍ-map d s w₁
            (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
            (r e₁ le_s c″ (WFDesc-rename ρL₁ ρR₁ c wf) T′ hTr₁))

      K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₂ (δsβ ↑ᴵ e₂) Ql Qr
        → ℰ d k p w₂ (δtβ ↑ᴵ e₂)
            (mplug (renameMFrame (ρL e₂) (just (reveal cL))) Ql) Qr
      K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₂ m₁ α₁ δsβ δtβ Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₂))
              (pk-〖〗 (embed-var T α) R≡ (open0 T (δl δs) A)))))
          refl
          (rev (ConvI-↑ e₂ hα) (≤-trans k≤s s≤N) ql qr q)

      K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₃ (δtβ ↑ᴵ e₃) Ql Qr
        → ℰ d k p w₃ (δtg ↑ᴵ e₃)
            (mplug (renameMFrame (ρL e₃)
              (just (reveal 〖 zero , ⇑ᵗ T ↑ BtL 〗))) Ql) Qr
      K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₃ (m-dead {Φ = dead Φ} dead-here) zero δtβ δtg Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
              (pk-〖〗 refl (shift-ty T T) (open0 T (δl δt) A)))))
          refl
          (rev (ConvI-↑ e₃ hβ) k≤s ql qr q)

  deadCon : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)}
      {α δs δt σs σt} {rk} (h : ConvI d N rk w m α δs δt σs σt)
    → ConM d m nothing n N
    → ∀ {Wl Wr} → Value Wl → allDead d n p w δt Wl Wr
    → ∀ Xs Ys c → WFDesc c → ∀ {T′} → repR Ys c ≡ ιT w T′
    → ℰ d n p w (extDeadI (repL Xs c) δs)
        ((Wl ↓ `∀↓ makeConceal (suc α) (⇑ᵗ (repM m (δl δt)))
                    (substᵗ (extsᵗ (δl δs)) A))
           ⦂∀ substᵗ (extsᵗ (δl δs)) A [ repL Xs c ])
        (Wr ⦂∀ ★ [ T′ ])
  deadCon {n} w {X} {m} {α} {δs} {δt} {σs} {σt} {rk} h cbn {Wl} {Wr} wl r
    Xs Ys c wf {T′} hTr =
    antiL₁ d p n≤N stepL (tagsL w) (okBindL w T) inner
    where
    T = repL Xs c
    open Step w T
    c″ = sdesc (zero ∷ map (renameVar ρL₁) Xs) (map (renameVar ρR₁) Ys)
      (renameDesc ρL₁ ρR₁ c)
    hTr₁ : rightTyS c″ ≡ ιT w₁ T′
    hTr₁ = trans (repR-rename ρL₁ ρR₁ Ys c) (trans (renameTy-id _) hTr)
    n≤N : n ≤ N
    n≤N = ConMb-≤ d (isNone m) nothing cbn
    R = repM m (δl δt)
    BsL = substᵗ (extsᵗ (δl δs)) A
    cL = makeConceal (suc α) (⇑ᵗ R) BsL
    tgtL : replaceTy (suc α) (⇑ᵗ R) BsL ≡ substᵗ (extsᵗ (δl δt)) A
    tgtL = tgt-body α R (δl δs) (δl δt) (tyL h) A
    stepL = conInst {T = T} cL wl refl
    m₁ = CMode-dead (CMode-↑ ρL₁ ρS₁ m)
    α₁ = toRenameᵗ ρL₁ α
    δsβ = extDeadI (＇ zero) (δs ↑ᴵ e₁)
    δtβ = extDeadI (＇ zero) (δt ↑ᴵ e₁)
    δsg = extDeadI T δs ↑ᴵ e₁

    R≡ : repM m₁ (δl δtβ) ≡ ⇑ᵗ R
    R≡ = trans (repM-dead (CMode-↑ ρL₁ ρS₁ m) (δl (δt ↑ᴵ e₁)) (＇ zero))
      (trans (repM-↑ ρL₁ ρS₁ m (δl δt)) (shift-ty T R))

    hα : ConvI d N rk w₁ m₁ α₁ δsβ δtβ (σs ↑ˢ e₁) (σt ↑ˢ e₁)
    hα = ConvI-extDead {β = zero} (λ e′ → new-bind T α (sym e′))
      (ConvI-↑ e₁ h)

    inner : ∀ {s} → s ≤′ n → s ≤ N → UpB d s n
      → ℰ d s p w₁ δsg
          ((⇑ᵗᵐ Wl ⦂∀ (bind T ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL) [ ＇ zero ])
             ↓ cL ↑ 〖 zero , ⇑ᵗ T ↑ BsL 〗)
          (Wr ⦂∀ ★ [ T′ ])
    inner {s} le_s s≤N up =
      ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δsg}
        (just (reveal 〖 zero , ⇑ᵗ T ↑ BsL 〗)) nothing
        (ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δsβ}
          (just (conceal cL)) nothing clause K₁)
        K₂
      where
      hβ : ConvI d s rk w₁ (m-dead {Φ = dead Φ} dead-here) zero δsβ δsg
        (σs ↑ˢ e₁) (σs ↑ˢ e₁)
      hβ = ConvI-newD e₁ (new-bind T) {Ls = sem ⊤Ω} {Lt = sem ⊤Ω} {Tl = T}
        s≤N (freshS h)

      clause : ℰ d s p w₁ δtβ
        (⇑ᵗᵐ Wl ⦂∀ (bind T ▷ᵇ replaceTy (suc α) (⇑ᵗ R) BsL) [ ＇ zero ])
        (Wr ⦂∀ ★ [ T′ ])
      clause =
        ℰᵍ-≡
          (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term T Wl)
            (trans (annot T (δl δt) A)
              (cong (renameᵗ (extᵗ suc)) (sym tgtL))))
          (cong (λ M → M ⦂∀ ★ [ T′ ]) (renameᵗᵐ-id Wr))
          (ℰᵍ-map d s w₁
            (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
            (r e₁ le_s c″ (WFDesc-rename ρL₁ ρR₁ c wf) T′ hTr₁))

      K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₂ (δtβ ↑ᴵ e₂) Ql Qr
        → ℰ d k p w₂ (δsβ ↑ᴵ e₂)
            (mplug (renameMFrame (ρL e₂) (just (conceal cL))) Ql) Qr
      K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (conRen e₂ m₁ α₁ δsβ δtβ Ql A)
            (↓-pk (pk-ren↓ (toRenameᵗ (ρL e₂))
              (pk-mc (embed-var T α) R≡ (open0 T (δl δs) A)))))
          refl
          (con (ConvI-↑ e₂ hα)
            (subst (λ b → ConMb d b nothing k N)
              (sym (trans (isNone-↑ (ρL e₂) (ρS e₂) m₁)
                (trans (isNone-dead (CMode-↑ ρL₁ ρS₁ m))
                  (isNone-↑ ρL₁ ρS₁ m))))
              (ConMb-cast d (isNone m)
                (ConMb-down d (isNone m) nothing (≤-trans k≤s (≤′⇒≤ le_s))
                  cbn)))
            ql qr q)

      K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₃ (δsβ ↑ᴵ e₃) Ql Qr
        → ℰ d k p w₃ (δsg ↑ᴵ e₃)
            (mplug (renameMFrame (ρL e₃)
              (just (reveal 〖 zero , ⇑ᵗ T ↑ BsL 〗))) Ql) Qr
      K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡
          (trans (revRen e₃ (m-dead {Φ = dead Φ} dead-here) zero δsβ δsg Ql A)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
              (pk-〖〗 refl (shift-ty T T) (open0 T (δl δs) A)))))
          refl
          (rev (ConvI-↑ e₃ hβ) k≤s ql qr q)

