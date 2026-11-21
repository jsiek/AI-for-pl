module proof.LR.ConvRight where

-- File Charter:
--   * The right-only conversion lemma (notes/logrel-dgg.md, Section 7,
--     "Gap in the oracle"): the right converts and the left does not
--     move.  A reveal turns values related with the right side's
--     variable as a store variable α′ (sealed on the right) into values
--     related with it as its representation; the conceal turns them
--     back.
--   * Modes: X paired with Y and the right converts Y's store variable
--     (`r-pair`), or no variable is converted and α′ is fresh
--     (`r-none`, the closure of other leaves).
--   * Hypotheses (`RConvI`): X's leaves are tied by `SealR`; the other
--     leaves are the same on both sides and closed under the conversion
--     at hand (`convP`) and under right conversions at store variables
--     created later (`genR`, `genRS`); the clauses' own leaves are
--     closed below the bound (`OracleR`).
--   * The lemma, with a reveal and a conceal half, by induction on the
--     precision derivation.  Into `★` the right takes an identity step
--     and the relation reads only the left (`proof.LR.StarAgree`).  At
--     `∀⊑∀` the right instantiates its proxy and the left's
--     instantiation is read from the clause, the mirror of
--     `PairRevL`/`PairConL` in `proof.LR.ConvLemma`.

open import Data.Bool using (Bool; true; false)
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
open import proof.LR.ConvLemma
open import proof.LR.PrecisionUnique using (↔-unique)
open import proof.LR.ConvMain using (allPair-from; allOnly-from; inst≡;
  revM-fun; revM-all; conM-fun; conM-all; 𝒱-⇒; 𝒱-∀; 𝒱-∀⊑⇒; 𝒱-∀⊑∀;
  𝒱-bot; nv⊑var; ⊑ι-closed)
open import proof.LR.StarAgree

private
  variable
    Δ Δ′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- Modes
------------------------------------------------------------------------

data RMode {Δ Δ′} (Φ : Corr Δ Δ′) (X : TyVar Δ) (ΘR : TyCtx) : Set where
  -- X is paired with Y, and the right converts its store variable α′
  r-pair : ∀ {Y} → Φ ∋ X ↔ Y → TyVar ΘR → RMode Φ X ΘR
  -- no variable is the converted one: the store variable and the
  -- representation are given
  r-none : TyVar ΘR → Ty ΘR → RMode Φ X ΘR

module _ {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  -- the store variable and the representation
  rα : RMode Φ X ΘR → TyVar ΘR
  rα (r-pair x α′) = α′
  rα (r-none α′ R′) = α′

  rR : RMode Φ X ΘR → (Δ′ ⇒ˢ ΘR) → Ty ΘR
  rR (r-pair {Y = Y} x α′) σ = σ Y
  rR (r-none α′ R′) σ = R′

  -- the right side's conversion, as an optional one that is present
  rcR : RMode Φ X ΘR → (Δ′ ⇒ˢ ΘR) → RConv ΘR
  rcR m σ = just (rα m , rR m σ)

  -- the variables that are not converted
  OtherR : RMode Φ X ΘR → TyVar Δ → Set
  OtherR (r-pair x α′) Z = Z ≢ X
  OtherR (r-none α′ R′) Z = ⊤

  RMode-↑ : ∀ {ΘR′} → ΘR ↪ᵗ ΘR′ → RMode Φ X ΘR → RMode Φ X ΘR′
  RMode-↑ ρ (r-pair x α′) = r-pair x (toRenameᵗ ρ α′)
  RMode-↑ ρ (r-none α′ R′) = r-none (toRenameᵗ ρ α′) (renameᵗ (toRenameᵗ ρ) R′)

  rR-↑ : ∀ {ΘR′} (ρ : ΘR ↪ᵗ ΘR′) (m : RMode Φ X ΘR) σ
    → rR (RMode-↑ ρ m) (λ Y → renameᵗ (toRenameᵗ ρ) (σ Y))
      ≡ renameᵗ (toRenameᵗ ρ) (rR m σ)
  rR-↑ ρ (r-pair x α′) σ = refl
  rR-↑ ρ (r-none α′ R′) σ = refl

  rα-↑ : ∀ {ΘR′} (ρ : ΘR ↪ᵗ ΘR′) (m : RMode Φ X ΘR)
    → rα (RMode-↑ ρ m) ≡ toRenameᵗ ρ (rα m)
  rα-↑ ρ (r-pair x α′) = refl
  rα-↑ ρ (r-none α′ R′) = refl

  rcR-↑ : ∀ {ΘR′} (ρ : ΘR ↪ᵗ ΘR′) (m : RMode Φ X ΘR) σ
    → rcR (RMode-↑ ρ m) (λ Y → renameᵗ (toRenameᵗ ρ) (σ Y))
      ≡ renRConv ρ (rcR m σ)
  rcR-↑ ρ m σ = cong₂ (λ a b → just (a , b)) (rα-↑ ρ m) (rR-↑ ρ m σ)

  OtherR-↑ : ∀ {ΘR′} (ρ : ΘR ↪ᵗ ΘR′) (m : RMode Φ X ΘR) Z
    → OtherR (RMode-↑ ρ m) Z → OtherR m Z
  OtherR-↑ ρ (r-pair x α′) Z o = o
  OtherR-↑ ρ (r-none α′ R′) Z o = o

  -- a left-only variable is never the converted one
  OtherR-only : ∀ (m : RMode Φ X ΘR) {Z} → Φ ∋ Z only → OtherR m Z
  OtherR-only (r-pair x α′) z refl = ↔-only-⊥ x z
  OtherR-only (r-none α′ R′) z = tt

-- under a binder
RMode-pair : ∀ {Φ : Corr Δ Δ′} {X} → RMode Φ X ΘR
  → RMode (pair Φ) (suc X) ΘR
RMode-pair (r-pair x α′) = r-pair (↔-pair x) α′
RMode-pair (r-none α′ R′) = r-none α′ R′

RMode-only : ∀ {Φ : Corr Δ Δ′} {X} → RMode Φ X ΘR
  → RMode (only Φ) (suc X) ΘR
RMode-only (r-pair x α′) = r-pair (↔-only x) α′
RMode-only (r-none α′ R′) = r-none α′ R′

module _ {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  rα-pair : ∀ (m : RMode Φ X ΘR) → rα (RMode-pair m) ≡ rα m
  rα-pair (r-pair x α′) = refl
  rα-pair (r-none α′ R′) = refl

  rR-pair : ∀ (m : RMode Φ X ΘR) σ T′
    → rR (RMode-pair m) (T′ •ˢ σ) ≡ rR m σ
  rR-pair (r-pair x α′) σ T′ = refl
  rR-pair (r-none α′ R′) σ T′ = refl

  rα-only : ∀ (m : RMode Φ X ΘR) → rα (RMode-only m) ≡ rα m
  rα-only (r-pair x α′) = refl
  rα-only (r-none α′ R′) = refl

  rR-only : ∀ (m : RMode Φ X ΘR) σ → rR (RMode-only m) σ ≡ rR m σ
  rR-only (r-pair x α′) σ = refl
  rR-only (r-none α′ R′) σ = refl

  OtherR-pair : ∀ (m : RMode Φ X ΘR) Z
    → OtherR (RMode-pair m) (suc Z) → OtherR m Z
  OtherR-pair (r-pair x α′) Z o = λ eq → o (cong suc eq)
  OtherR-pair (r-none α′ R′) Z o = tt

  OtherR-only′ : ∀ (m : RMode Φ X ΘR) Z
    → OtherR (RMode-only m) (suc Z) → OtherR m Z
  OtherR-only′ (r-pair x α′) Z o = λ eq → o (cong suc eq)
  OtherR-only′ (r-none α′ R′) Z o = tt

------------------------------------------------------------------------
-- Closure under right conversions at new store variables
------------------------------------------------------------------------

-- a right store variable created after the extension's source
NewR : ∀ {w w′ : World} → w′ ⊒ w → TyVar (ΔR w′) → Set
NewR e β′ = ∀ Y → toRenameᵗ (ρR e) Y ≢ β′

-- a paired leaf with right type T′, closed under later right
-- conversions
FreshR : Dir → (w : World) → Leaf (ΔL w) (ΔR w) → Ty (ΔR w) → Set
FreshR d w L T′ =
  ∀ {w′} (e : w′ ⊒ w) {β′ R′} → NewR e β′ → ∀ {k}
  → (∀ {Vl Vr} → Value Vl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) L) Vl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) L) Vl
           (Vr ↑ 〖 β′ , R′ ↑ renameᵗ (toRenameᵗ (ρR e)) T′ 〗))
    × (∀ {Vl Wr} → Value Vl → Value Wr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) L) Vl Wr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) L) Vl
           (Wr ↓ makeConceal β′ R′ (renameᵗ (toRenameᵗ (ρR e)) T′)))

-- the clauses' leaves, for bounds up to N
OracleR : Dir → ℕ → Set
OracleR d N =
  ∀ {w} {n′ n} (le : n′ ≤′ n) → n′ ≤ N → (c : SDesc (ΔL w) (ΔR w))
  → WFS c → FreshR d w (sem (leafBelowS d le c)) (rightTyS c)

OracleR-down : ∀ {d N N′} → N′ ≤ N → OracleR d N → OracleR d N′
OracleR-down le o l b c wf = o l (≤-trans b le) c wf

-- an other variable's leaf under the conversion at hand, in every
-- future
ConvLeafR : Dir → ℕ → (w : World) → TyVar (ΔR w) → Ty (ΔR w)
  → (Ls Lt : Leaf (ΔL w) (ΔR w)) → Ty (ΔR w) → Set
ConvLeafR d N w α′ R′ Ls Lt T′ =
  ∀ {w′} (e : w′ ⊒ w) {k} → k ≤ N
  → (∀ {Vl Vr} → Value Vl → Value Vr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls) Vl Vr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) Lt) Vl
           (Vr ↑ 〖 toRenameᵗ (ρR e) α′ , renameᵗ (toRenameᵗ (ρR e)) R′
                 ↑ renameᵗ (toRenameᵗ (ρR e)) T′ 〗))
    × (∀ {Vl Wr} → Value Vl → Value Wr
       → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Lt) Vl Wr
       → ℰL d k w′ (transportLeaf (ρL e) (ρR e) Ls) Vl
           (Wr ↓ makeConceal (toRenameᵗ (ρR e) α′)
                   (renameᵗ (toRenameᵗ (ρR e)) R′)
                   (renameᵗ (toRenameᵗ (ρR e)) T′)))

------------------------------------------------------------------------
-- The hypotheses
------------------------------------------------------------------------

-- the stage of a right-sealed leaf's contents: the same in `≺`, one
-- down in `≻`
rStage : Dir → ℕ → ℕ
rStage ≺ k = k
rStage ≻ k = pred k

-- the bound for sealing: inclusive in `≺`, strict in `≻`
rBelow : Dir → ℕ → ℕ → Set
rBelow ≺ k N = k ≤ N
rBelow ≻ k N = k < N

-- the stages at which a conceal is needed
ConBR : Dir → ℕ → ℕ → Set
ConBR ≺ k N = k ≤ N
ConBR ≻ k N = k < N

ConBR-≤ : ∀ d {k N} → ConBR d k N → k ≤ N
ConBR-≤ ≺ cb = cb
ConBR-≤ ≻ cb = <⇒≤ cb

ConBR-down : ∀ d {k n N} → k ≤ n → ConBR d n N → ConBR d k N
ConBR-down ≺ le cb = ≤-trans le cb
ConBR-down ≻ le cb = ≤-<-trans le cb

-- The conceal's bound by mode: `ConBR` for the converted variable's
-- seal hypothesis, and up to the bound in mode none, where no variable
-- is converted.
isNoneR : ∀ {Φ : Corr Δ Δ′} {X} → RMode Φ X ΘR → Bool
isNoneR (r-pair x α′) = false
isNoneR (r-none α′ R′) = true

ConRb : Dir → Bool → ℕ → ℕ → Set
ConRb d false k N = ConBR d k N
ConRb d true k N = k ≤ N

ConRm : ∀ {Φ : Corr Δ Δ′} {X} → Dir → RMode Φ X ΘR → ℕ → ℕ → Set
ConRm d m k N = ConRb d (isNoneR m) k N

ConRb-≤ : ∀ d b {k N} → ConRb d b k N → k ≤ N
ConRb-≤ d false cb = ConBR-≤ d cb
ConRb-≤ d true cb = cb

ConRb-down : ∀ d b {k n N} → k ≤ n → ConRb d b n N → ConRb d b k N
ConRb-down d false le cb = ConBR-down d le cb
ConRb-down d true le cb = ≤-trans le cb

ConBR→ConRb : ∀ d b {k N} → ConBR d k N → ConRb d b k N
ConBR→ConRb d false cb = cb
ConBR→ConRb d true cb = ConBR-≤ d cb

module _ {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  isNoneR-↑ : ∀ {ΘR′} (ρ : ΘR ↪ᵗ ΘR′) (m : RMode Φ X ΘR)
    → isNoneR (RMode-↑ ρ m) ≡ isNoneR m
  isNoneR-↑ ρ (r-pair x α′) = refl
  isNoneR-↑ ρ (r-none α′ R′) = refl

  isNoneR-pair : (m : RMode Φ X ΘR) → isNoneR (RMode-pair m) ≡ isNoneR m
  isNoneR-pair (r-pair x α′) = refl
  isNoneR-pair (r-none α′ R′) = refl

  isNoneR-only : (m : RMode Φ X ΘR) → isNoneR (RMode-only m) ≡ isNoneR m
  isNoneR-only (r-pair x α′) = refl
  isNoneR-only (r-none α′ R′) = refl

  -- the bound of a mode moved to a future, at a lower stage
  ConRm-↑ : ∀ d {ΘR′} (ρ : ΘR ↪ᵗ ΘR′) (m : RMode Φ X ΘR) {k n N} → k ≤ n
    → ConRm d m n N → ConRm d (RMode-↑ ρ m) k N
  ConRm-↑ d ρ m le cb =
    subst (λ b → ConRb d b _ _) (sym (isNoneR-↑ ρ m))
      (ConRb-down d (isNoneR m) le cb)

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} where

  SelfR : ∀ {ΘL ΘR} → RMode Φ X ΘR → (δs : Interp Δ Δ′ ΘL ΘR) → Set
  SelfR (r-pair {Y = Y} x α′) δs = δr δs Y ≡ ＇ α′
  SelfR (r-none α′ R′) δs = ⊤

  -- X's leaves, in every future: the source leaf (δs) holds of values
  -- sealed on the right whose contents the target leaf (δt) relates
  SealR : Dir → ℕ → (w : World) → RMode Φ X (ΔR w)
    → (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) → Set
  SealR d N w (r-pair {Y = Y} x α′) δs δt =
    (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X) Vl Vr
       → sealedR (toRenameᵗ (ρR e) α′) (δr (δt ↑ᴵ e) Y)
           (leafRel d (rStage d k) w′ (leaf (δt ↑ᴵ e) X)) Vl Vr)
    × (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → rBelow d k N → ∀ {Vl Wr}
       → leafRel d k w′ (leaf (δt ↑ᴵ e) X) Vl Wr
       → leafRel d k w′ (leaf (δs ↑ᴵ e) X) Vl
           (Wr ↓ seal (toRenameᵗ (ρR e) α′) (δr (δt ↑ᴵ e) Y)))
  SealR d N w (r-none α′ R′) δs δt = ⊤

  record RConvI (d : Dir) (N : ℕ) (w : World) (m : RMode Φ X (ΔR w))
      (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) : Set₁ where
    field
      goodS : GoodI δs
      goodT : GoodI δt
      selfR : SelfR m δs
      tyL : ∀ Z → δl δs Z ≡ δl δt Z
      tyR : ∀ Y′ → replaceTy (rα m) (rR m (δr δt)) (δr δs Y′) ≡ δr δt Y′
      leafO : ∀ Z → OtherR m Z → leaf δs Z ≈ˡ leaf δt Z
      convP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → OtherR m Z
        → ConvLeafR d N w (rα m) (rR m (δr δt)) (leaf δs Z) (leaf δt Z)
            (δr δs Y′)
      genR : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → FreshR d w (leaf δt Z) (δr δt Y′)
      genRS : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → FreshR d w (leaf δs Z) (δr δs Y′)
      sealR : SealR d N w m δs δt
      oracleR : OracleR d N

  open RConvI public

  -- the two interpretations agree on the left
  agreeR : ∀ {d N w} {m : RMode Φ X (ΔR w)} {δs δt}
    → RConvI d N w m δs δt → Φ ⊢ δs ≈ᴸ δt
  δl≡ᴸ (agreeR h) = tyL h
  leaf≈ᴸ (agreeR {m = m} h) {Z} z = leafO h Z (OtherR-only m z)

-- an interpretation whose leaves are closed under later right conversions
record FreshIR {Δ Δ′} (Φ : Corr Δ Δ′) (d : Dir) (N : ℕ) (w : World)
    (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) : Set₁ where
  field
    fgoodR : GoodI δ
    fR : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → FreshR d w (leaf δ Z) (δr δ Y′)
    forcR : OracleR d N

open FreshIR public

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d N} {w : World}
    {m : RMode Φ X (ΔR w)} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)} where

  freshTR : RConvI d N w m δs δt → FreshIR Φ d N w δt
  fgoodR (freshTR h) = goodT h
  fR (freshTR h) = genR h
  forcR (freshTR h) = oracleR h

  freshSR : RConvI d N w m δs δt → FreshIR Φ d N w δs
  fgoodR (freshSR h) = goodS h
  fR (freshSR h) = genRS h
  forcR (freshSR h) = oracleR h

------------------------------------------------------------------------
-- Closure moves to future worlds
------------------------------------------------------------------------

NewR-∘ : ∀ {w w′ w″ : World} (e′ : w″ ⊒ w′) (e : w′ ⊒ w) {β′}
  → NewR e′ β′ → NewR (⊒-trans e′ e) β′
NewR-∘ e′ e nb Y eq =
  nb (toRenameᵗ (ρR e) Y) (trans (sym (toRenameᵗ-∘ (ρR e′) (ρR e) Y)) eq)

module _ {d} {w w′ : World} (e : w′ ⊒ w) {L : Leaf (ΔL w) (ΔR w)} where

  private
    L′ = transportLeaf (ρL e) (ρR e) L

  FreshR-↑ : ∀ {T′} → FreshR d w L T′
    → FreshR d w′ L′ (renameᵗ (toRenameᵗ (ρR e)) T′)
  FreshR-↑ {T′} f {w″} e′ {β′} {R′} nb {k} =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w″ (≈ˡ-sym L∘)
        (ℰL-≡ d k w″ L₂ refl
          (cong (λ C → Vr ↑ 〖 β′ , R′ ↑ C 〗)
            (sym (renameTy-∘ (ρR e′) (ρR e) T′)))
          (proj₁ g vl vr (leafRel-resp d k w″ L∘ r)))) ,
    (λ {Vl} {Wr} vl wr r →
      ℰL-resp d k w″ (≈ˡ-sym L∘)
        (ℰL-≡ d k w″ L₂ refl
          (cong (λ C → Wr ↓ makeConceal β′ R′ C)
            (sym (renameTy-∘ (ρR e′) (ρR e) T′)))
          (proj₂ g vl wr (leafRel-resp d k w″ L∘ r))))
    where
    L∘ = transportLeaf-∘ (ρL e′) (ρL e) (ρR e′) (ρR e) L
    L₂ = transportLeaf (ρL e′ ∘↪ ρL e) (ρR e′ ∘↪ ρR e) L
    g = f (⊒-trans e′ e) (NewR-∘ e′ e nb) {k}

------------------------------------------------------------------------
-- The hypotheses move to future worlds
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ}
    {w w′ : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    (e : w′ ⊒ w) where

  private
    ρl = toRenameᵗ (ρL e)
    ρr = toRenameᵗ (ρR e)

  SelfR-↑ : ∀ (m : RMode Φ X (ΔR w)) → SelfR m δs
    → SelfR (RMode-↑ (ρR e) m) (δs ↑ᴵ e)
  SelfR-↑ (r-pair x α′) a = cong (renameᵗ ρr) a
  SelfR-↑ (r-none α′ R′) a = tt

  module CompR (m : RMode Φ X (ΔR w)) {w″} (e′ : w″ ⊒ w′) where

    α∘ : toRenameᵗ (ρR (⊒-trans e′ e)) (rα m)
      ≡ toRenameᵗ (ρR e′) (rα (RMode-↑ (ρR e) m))
    α∘ = trans (toRenameᵗ-∘ (ρR e′) (ρR e) (rα m))
      (cong (toRenameᵗ (ρR e′)) (sym (rα-↑ (ρR e) m)))

    R∘ : renameᵗ (toRenameᵗ (ρR (⊒-trans e′ e))) (rR m (δr δt))
      ≡ renameᵗ (toRenameᵗ (ρR e′)) (rR (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e)))
    R∘ = trans (sym (renameTy-∘ (ρR e′) (ρR e) (rR m (δr δt))))
      (cong (renameᵗ (toRenameᵗ (ρR e′))) (sym (rR-↑ (ρR e) m (δr δt))))

  ConvLeafR-↑ : ∀ (m : RMode Φ X (ΔR w)) {Z Y′}
    → ConvLeafR d N w (rα m) (rR m (δr δt)) (leaf δs Z) (leaf δt Z)
        (δr δs Y′)
    → ConvLeafR d N w′ (rα (RMode-↑ (ρR e) m))
        (rR (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e)))
        (leaf (δs ↑ᴵ e) Z) (leaf (δt ↑ᴵ e) Z) (δr (δs ↑ᴵ e) Y′)
  ConvLeafR-↑ m {Z} {Y′} h {w″} e′ {k} k≤N =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) Z))
        (ℰL-≡ d k w″ (leaf (δt ↑ᴵ ⊒-trans e′ e) Z) refl
          (↑〖〗-≡ (CompR.α∘ m e′) (CompR.R∘ m e′)
            (sym (δr≡ (↑ᴵ-trans δs e′ e) Y′)))
          (proj₁ g vl vr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) Z) r)))) ,
    (λ {Vl} {Wr} vl wr r →
      ℰL-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) Z))
        (ℰL-≡ d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) Z) refl
          (↓mc-≡ (CompR.α∘ m e′) (CompR.R∘ m e′)
            (sym (δr≡ (↑ᴵ-trans δs e′ e) Y′)))
          (proj₂ g vl wr
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δt e′ e) Z) r))))
    where
    g = h (⊒-trans e′ e) k≤N

  SealR-↑ : ∀ (m : RMode Φ X (ΔR w)) → SealR d N w m δs δt
    → SealR d N w′ (RMode-↑ (ρR e) m) (δs ↑ᴵ e) (δt ↑ᴵ e)
  SealR-↑ (r-pair {Y = Y} x α′) (hrev , hcon) = rev′ , con′
    where
    rev′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
      → leafRel d k w″ (leaf ((δs ↑ᴵ e) ↑ᴵ e′) X) Vl Vr
      → sealedR (toRenameᵗ (ρR e′) (ρr α′)) (δr ((δt ↑ᴵ e) ↑ᴵ e′) Y)
          (leafRel d (rStage d k) w″ (leaf ((δt ↑ᴵ e) ↑ᴵ e′) X)) Vl Vr
    rev′ {w″} e′ {k} pos le r =
      sealedR-map (toRenameᵗ-∘ (ρR e′) (ρR e) α′)
        (sym (δr≡ (↑ᴵ-trans δt e′ e) Y))
        (leafRel-resp d (rStage d k) w″
          (≈ˡ-sym (leaf≈ (↑ᴵ-trans δt e′ e) X)))
        (hrev (⊒-trans e′ e) pos le
          (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δs e′ e) X) r))
    con′ : ∀ {w″} (e′ : w″ ⊒ w′) {k} → 0 < k → rBelow d k N
      → ∀ {Vl Wr} → leafRel d k w″ (leaf ((δt ↑ᴵ e) ↑ᴵ e′) X) Vl Wr
      → leafRel d k w″ (leaf ((δs ↑ᴵ e) ↑ᴵ e′) X) Vl
          (Wr ↓ seal (toRenameᵗ (ρR e′) (ρr α′)) (δr ((δt ↑ᴵ e) ↑ᴵ e′) Y))
    con′ {w″} e′ {k} pos lt {Vl} {Wr} r =
      leafRel-resp d k w″ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δs e′ e) X))
        (subst (leafRel d k w″ (leaf (δs ↑ᴵ ⊒-trans e′ e) X) Vl)
          (cong₂ (λ a R → Wr ↓ seal a R) (toRenameᵗ-∘ (ρR e′) (ρR e) α′)
            (sym (δr≡ (↑ᴵ-trans δt e′ e) Y)))
          (hcon (⊒-trans e′ e) pos lt
            (leafRel-resp d k w″ (leaf≈ (↑ᴵ-trans δt e′ e) X) r)))
  SealR-↑ (r-none α′ R′) h = tt

  RConvI-↑ : ∀ {m : RMode Φ X (ΔR w)}
    → RConvI d N w m δs δt
    → RConvI d N w′ (RMode-↑ (ρR e) m) (δs ↑ᴵ e) (δt ↑ᴵ e)
  goodS (RConvI-↑ h) = GoodI-↑ {δ = δs} (goodS h) e
  goodT (RConvI-↑ h) = GoodI-↑ {δ = δt} (goodT h) e
  selfR (RConvI-↑ {m = m} h) = SelfR-↑ m (selfR h)
  tyL (RConvI-↑ h) Z = cong (renameᵗ ρl) (tyL h Z)
  tyR (RConvI-↑ {m = m} h) Y′ =
    trans (cong₂ (λ a R → replaceTy a R (renameᵗ ρr (δr δs Y′)))
            (rα-↑ (ρR e) m) (rR-↑ (ρR e) m (δr δt)))
      (trans (sym (replaceTy-rename ρr (toRenameᵗ-injective (ρR e)) (rα m)
               (rR m (δr δt)) (δr δs Y′)))
        (cong (renameᵗ ρr) (tyR h Y′)))
  leafO (RConvI-↑ {m = m} h) Z o =
    transportLeaf-resp (ρL e) (ρR e) (leafO h Z (OtherR-↑ (ρR e) m Z o))
  convP (RConvI-↑ {m = m} h) {Z} z o =
    ConvLeafR-↑ m (convP h z (OtherR-↑ (ρR e) m Z o))
  genR (RConvI-↑ h) {Z} {Y′} z =
    FreshR-↑ {d = d} e {L = leaf δt Z} {δr δt Y′} (genR h z)
  genRS (RConvI-↑ h) {Z} {Y′} z =
    FreshR-↑ {d = d} e {L = leaf δs Z} {δr δs Y′} (genRS h z)
  sealR (RConvI-↑ {m = m} h) = SealR-↑ m (sealR h)
  oracleR (RConvI-↑ h) = oracleR h

------------------------------------------------------------------------
-- The hypotheses under binders
------------------------------------------------------------------------

SelfR-pair : ∀ {Φ : Corr Δ Δ′} {X} (m : RMode Φ X ΘR)
    {δs : Interp Δ Δ′ ΘL ΘR} {T T′ l}
  → SelfR m δs → SelfR (RMode-pair m) (extPairI T T′ l δs)
SelfR-pair (r-pair x α′) h = h
SelfR-pair (r-none α′ R′) h = h

SelfR-only : ∀ {Φ : Corr Δ Δ′} {X} (m : RMode Φ X ΘR)
    {δs : Interp Δ Δ′ ΘL ΘR} {T l}
  → SelfR m δs → SelfR (RMode-only m) (extOnlyI T l δs)
SelfR-only (r-pair x α′) h = h
SelfR-only (r-none α′ R′) h = h

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ}
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {T : Ty (ΔL w)} {l : Leaf (ΔL w) (ΔR w)} where

  SealR-pair : ∀ (m : RMode Φ X (ΔR w)) {T′}
    → SealR d N w m δs δt
    → SealR d N w (RMode-pair m) (extPairI T T′ l δs) (extPairI T T′ l δt)
  SealR-pair (r-pair x α′) h = h
  SealR-pair (r-none α′ R′) h = h

  SealR-only : ∀ (m : RMode Φ X (ΔR w))
    → SealR d N w m δs δt
    → SealR d N w (RMode-only m) (extOnlyI T l δs) (extOnlyI T l δt)
  SealR-only (r-pair x α′) h = h
  SealR-only (r-none α′ R′) h = h

  -- a paired binder: the new variable is T on the left and the store
  -- variable β′ on the right, with the same leaf on both sides
  RConvI-extPair : ∀ {m : RMode Φ X (ΔR w)} {β′ : TyVar (ΔR w)}
    → GoodLeaf l → β′ ≢ rα m
    → ConvLeafR d N w (rα m) (rR m (δr δt)) l l (＇ β′)
    → FreshR d w l (＇ β′)
    → RConvI d N w m δs δt
    → RConvI d N w (RMode-pair m)
        (extPairI T (＇ β′) l δs) (extPairI T (＇ β′) l δt)
  goodS (RConvI-extPair {β′ = β′} gl ne cv fr h) =
    GoodI-extPairI {T = T} {T′ = ＇ β′} {δ = δs} gl (goodS h)
  goodT (RConvI-extPair {β′ = β′} gl ne cv fr h) =
    GoodI-extPairI {T = T} {T′ = ＇ β′} {δ = δt} gl (goodT h)
  selfR (RConvI-extPair {m = m} {β′} gl ne cv fr h) =
    SelfR-pair m {T = T} {T′ = ＇ β′} {l = l} (selfR h)
  tyL (RConvI-extPair gl ne cv fr h) zero = refl
  tyL (RConvI-extPair gl ne cv fr h) (suc Z) = tyL h Z
  tyR (RConvI-extPair {m = m} {β′} gl ne cv fr h) zero =
    subst₂ (λ a R → replaceTy a R (＇ β′) ≡ ＇ β′)
      (sym (rα-pair m)) (sym (rR-pair m (δr δt) (＇ β′)))
      (replaceTy-other _ ne)
  tyR (RConvI-extPair {m = m} {β′} gl ne cv fr h) (suc Y′) =
    subst₂ (λ a R → replaceTy a R (δr δs Y′) ≡ δr δt Y′)
      (sym (rα-pair m)) (sym (rR-pair m (δr δt) (＇ β′))) (tyR h Y′)
  leafO (RConvI-extPair gl ne cv fr h) zero o = ≈ˡ-refl
  leafO (RConvI-extPair {m = m} gl ne cv fr h) (suc Z) o =
    leafO h Z (OtherR-pair m Z o)
  convP (RConvI-extPair {m = m} {β′} gl ne cv fr h) ↔-here o =
    subst₂ (λ a R → ConvLeafR d N w a R l l (＇ β′))
      (sym (rα-pair m)) (sym (rR-pair m (δr δt) (＇ β′))) cv
  convP (RConvI-extPair {m = m} {β′} gl ne cv fr h)
      {suc Z} {suc Y′} (↔-pair z) o =
    subst₂ (λ a R → ConvLeafR d N w a R (leaf δs Z) (leaf δt Z) (δr δs Y′))
      (sym (rα-pair m)) (sym (rR-pair m (δr δt) (＇ β′)))
      (convP h z (OtherR-pair m Z o))
  genR (RConvI-extPair gl ne cv fr h) ↔-here = fr
  genR (RConvI-extPair gl ne cv fr h) (↔-pair z) = genR h z
  genRS (RConvI-extPair gl ne cv fr h) ↔-here = fr
  genRS (RConvI-extPair gl ne cv fr h) (↔-pair z) = genRS h z
  sealR (RConvI-extPair {m = m} gl ne cv fr h) = SealR-pair m (sealR h)
  oracleR (RConvI-extPair gl ne cv fr h) = oracleR h

  -- a left-only binder: the new variable is T, with the same leaf on
  -- both sides
  RConvI-extOnly : ∀ {m : RMode Φ X (ΔR w)}
    → GoodLeaf l → RConvI d N w m δs δt
    → RConvI d N w (RMode-only m) (extOnlyI T l δs) (extOnlyI T l δt)
  goodS (RConvI-extOnly gl h) = GoodI-extOnlyI {T = T} {δ = δs} gl (goodS h)
  goodT (RConvI-extOnly gl h) = GoodI-extOnlyI {T = T} {δ = δt} gl (goodT h)
  selfR (RConvI-extOnly {m = m} gl h) = SelfR-only m {T = T} {l = l} (selfR h)
  tyL (RConvI-extOnly gl h) zero = refl
  tyL (RConvI-extOnly gl h) (suc Z) = tyL h Z
  tyR (RConvI-extOnly {m = m} gl h) Y′ =
    subst₂ (λ a R → replaceTy a R (δr δs Y′) ≡ δr δt Y′)
      (sym (rα-only m)) (sym (rR-only m (δr δt))) (tyR h Y′)
  leafO (RConvI-extOnly gl h) zero o = ≈ˡ-refl
  leafO (RConvI-extOnly {m = m} gl h) (suc Z) o =
    leafO h Z (OtherR-only′ m Z o)
  convP (RConvI-extOnly {m = m} gl h) {suc Z} {Y′} (↔-only z) o =
    subst₂ (λ a R → ConvLeafR d N w a R (leaf δs Z) (leaf δt Z) (δr δs Y′))
      (sym (rα-only m)) (sym (rR-only m (δr δt)))
      (convP h z (OtherR-only′ m Z o))
  genR (RConvI-extOnly gl h) (↔-only z) = genR h z
  genRS (RConvI-extOnly gl h) (↔-only z) = genRS h z
  sealR (RConvI-extOnly {m = m} gl h) = SealR-only m (sealR h)
  oracleR (RConvI-extOnly gl h) = oracleR h

------------------------------------------------------------------------
-- Leaves at right store variables: a conversion is an identity step
------------------------------------------------------------------------

module _ (d : Dir) (k : ℕ) (w : World) (L : Leaf (ΔL w) (ΔR w))
    (gl : GoodLeaf L) where

  -- the leaf is read as the only variable of an interpretation
  idRevR : ∀ {α′ γ′ : TyVar (ΔR w)} {R′} → γ′ ≢ α′ → ∀ {Vl Vr}
    → Value Vl → Value Vr → leafRel d k w L Vl Vr
    → ℰL d k w L Vl (Vr ↑ 〖 α′ , R′ ↑ ＇ γ′ 〗)
  idRevR {α′} {γ′} {R′} ne {Vl} {Vr} vl vr r =
    XY→ℰL d k (↔-here {Φ = []}) w {δ = extPairI ★ (＇ γ′) L closedI}
      (ℰ-≡ d k (X⊑Y ↔-here) w (extPairI ★ (＇ γ′) L closedI)
        refl (sym (↑-pk (〖〗-other R′ refl ne)))
        (ℰ-steps? d k (X⊑Y ↔-here) w
          (GoodI-extPairI {T = ★} {T′ = ＇ γ′} {δ = closedI} gl good-closedI)
          stay (step (id-reveal vr)) vl vr (to (𝒱-XY d k ↔-here w) r)))

  idConR : ∀ {α′ γ′ : TyVar (ΔR w)} {R′} → γ′ ≢ α′ → ∀ {Vl Wr}
    → Value Vl → Value Wr → leafRel d k w L Vl Wr
    → ℰL d k w L Vl (Wr ↓ makeConceal α′ R′ (＇ γ′))
  idConR {α′} {γ′} {R′} ne {Vl} {Wr} vl wr r =
    XY→ℰL d k (↔-here {Φ = []}) w {δ = extPairI ★ (＇ γ′) L closedI}
      (ℰ-≡ d k (X⊑Y ↔-here) w (extPairI ★ (＇ γ′) L closedI)
        refl (sym (↓-pk (makeConceal-other R′ refl ne)))
        (ℰ-steps? d k (X⊑Y ↔-here) w
          (GoodI-extPairI {T = ★} {T′ = ＇ γ′} {δ = closedI} gl good-closedI)
          stay (step (id-conceal wr)) vl wr (to (𝒱-XY d k ↔-here w) r)))

module _ {d : Dir} {N : ℕ} {w : World} {L : Leaf (ΔL w) (ΔR w)}
    (gl : GoodLeaf L) {γ′ : TyVar (ΔR w)} where

  -- under the conversion at hand, at another store variable
  storeConvR : ∀ R′ {α′} → γ′ ≢ α′ → ConvLeafR d N w α′ R′ L L (＇ γ′)
  storeConvR R′ ne {w′} e {k} k≤N =
    (λ vl vr r →
      idRevR d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρR e) eq)) vl vr r) ,
    (λ vl wr r →
      idConR d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl)
        (λ eq → ne (toRenameᵗ-injective (ρR e) eq)) vl wr r)

  -- under later conversions
  storeFreshR : FreshR d w L (＇ γ′)
  storeFreshR {w′} e {β′} {R′} nb {k} =
    (λ vl vr r →
      idRevR d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ′) vl vr r) ,
    (λ vl wr r →
      idConR d k w′ (transportLeaf (ρL e) (ρR e) L)
        (GoodLeaf-transport (ρL e) (ρR e) gl) (nb γ′) vl wr r)

------------------------------------------------------------------------
-- Closure under the conversion at a new right store variable
------------------------------------------------------------------------

module _ {d} {w w₁ : World} (e₁ : w₁ ⊒ w) {L : Leaf (ΔL w) (ΔR w)}
    {β′ : TyVar (ΔR w₁)} (nb : ∀ Y → toRenameᵗ (ρR e₁) Y ≢ β′) where

  private
    L₁ = transportLeaf (ρL e₁) (ρR e₁) L

  fresh→convR : ∀ {T′ N} (R′ : Ty (ΔR w₁)) → FreshR d w L T′
    → ConvLeafR d N w₁ β′ R′ L₁ L₁ (renameᵗ (toRenameᵗ (ρR e₁)) T′)
  fresh→convR {T′} R′ f {w′} e′ {k} k≤N =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w′ (≈ˡ-sym L∘)
        (ℰL-≡ d k w′ L₂ refl
          (cong (λ C → Vr ↑ 〖 toRenameᵗ (ρR e′) β′
                            , renameᵗ (toRenameᵗ (ρR e′)) R′ ↑ C 〗)
            (sym (renameTy-∘ (ρR e′) (ρR e₁) T′)))
          (proj₁ g vl vr (leafRel-resp d k w′ L∘ r)))) ,
    (λ {Vl} {Wr} vl wr r →
      ℰL-resp d k w′ (≈ˡ-sym L∘)
        (ℰL-≡ d k w′ L₂ refl
          (cong (λ C → Wr ↓ makeConceal (toRenameᵗ (ρR e′) β′)
                            (renameᵗ (toRenameᵗ (ρR e′)) R′) C)
            (sym (renameTy-∘ (ρR e′) (ρR e₁) T′)))
          (proj₂ g vl wr (leafRel-resp d k w′ L∘ r))))
    where
    L∘ = transportLeaf-∘ (ρL e′) (ρL e₁) (ρR e′) (ρR e₁) L
    L₂ = transportLeaf (ρL e′ ∘↪ ρL e₁) (ρR e′ ∘↪ ρR e₁) L
    g = f (⊒-trans e′ e₁) (NewR-after e₁ e′ nb) {k}

------------------------------------------------------------------------
-- The hypotheses, in the current world
------------------------------------------------------------------------

module NowR {Δ Δ′} {Φ : Corr Δ Δ′} {X : TyVar Δ} {d : Dir} {N : ℕ}
    {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {m : RMode Φ X (ΔR w)} (h : RConvI d N w m δs δt) where

  private
    ≈s = ↑ᴵ-refl {w = w} δs
    ≈t = ↑ᴵ-refl {w = w} δt

  revP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → OtherR m Z → ∀ {k} → k ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → leafRel d k w (leaf δs Z) Vl Vr
    → ℰ d k (X⊑Y z) w δt Vl (Vr ↑ 〖 rα m , rR m (δr δt) ↑ δr δs Y′ 〗)
  revP {Z} {Y′} z o {k} le {Vl} {Vr} vl vr r =
    ℰL→XY d k z w
      (ℰL-resp d k w (leaf≈ ≈t Z)
        (ℰL-≡ d k w (leaf (δt ↑ᴵ ⊒-refl w) Z) refl
          (↑〖〗-≡ (toRename-id-eq (rα m)) (renameTy-id (rR m (δr δt)))
            (renameTy-id (δr δs Y′)))
          (proj₁ (convP h z o (⊒-refl w) le) vl vr
            (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈s Z)) r))))

  conP : ∀ {Z Y′} (z : Φ ∋ Z ↔ Y′) → OtherR m Z → ∀ {k} → k ≤ N
    → ∀ {Vl Wr} → Value Vl → Value Wr → leafRel d k w (leaf δt Z) Vl Wr
    → ℰ d k (X⊑Y z) w δs Vl
        (Wr ↓ makeConceal (rα m) (rR m (δr δt)) (δr δs Y′))
  conP {Z} {Y′} z o {k} le {Vl} {Wr} vl wr r =
    ℰL→XY d k z w
      (ℰL-resp d k w (leaf≈ ≈s Z)
        (ℰL-≡ d k w (leaf (δs ↑ᴵ ⊒-refl w) Z) refl
          (↓mc-≡ (toRename-id-eq (rα m)) (renameTy-id (rR m (δr δt)))
            (renameTy-id (δr δs Y′)))
          (proj₂ (convP h z o (⊒-refl w) le) vl wr
            (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈t Z)) r))))

-- X's own leaves, now
module NowXR {Δ Δ′} {Φ : Corr Δ Δ′} {X Y} {x : Φ ∋ X ↔ Y} {d : Dir}
    {N : ℕ} {w : World} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {α′ : TyVar (ΔR w)} (si : SealR d N w (r-pair x α′) δs δt) where

  private
    ≈s = ↑ᴵ-refl {w = w} δs
    ≈t = ↑ᴵ-refl {w = w} δt

  sealRev : ∀ {k} → 0 < k → k ≤ N
    → ∀ {Vl Vr} → leafRel d k w (leaf δs X) Vl Vr
    → sealedR α′ (δr δt Y) (leafRel d (rStage d k) w (leaf δt X)) Vl Vr
  sealRev {k} pos le r =
    sealedR-map (toRename-id-eq α′) (δr≡ ≈t Y)
      (leafRel-resp d (rStage d k) w (leaf≈ ≈t X))
      (proj₁ si (⊒-refl w) pos le
        (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈s X)) r))

  sealCon : ∀ {k} → 0 < k → rBelow d k N
    → ∀ {Vl Wr} → leafRel d k w (leaf δt X) Vl Wr
    → leafRel d k w (leaf δs X) Vl (Wr ↓ seal α′ (δr δt Y))
  sealCon {k} pos lt {Vl} {Wr} r =
    leafRel-resp d k w (leaf≈ ≈s X)
      (subst (leafRel d k w (leaf (δs ↑ᴵ ⊒-refl w) X) Vl)
        (cong₂ (λ a R → Wr ↓ seal a R) (toRename-id-eq α′) (δr≡ ≈t Y))
        (proj₂ si (⊒-refl w) pos lt
          (leafRel-resp d k w (≈ˡ-sym (leaf≈ ≈t X)) r)))

------------------------------------------------------------------------
-- The statements
------------------------------------------------------------------------

RevR : Dir → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A B} → Φ ⊢ A ⊑ B → Set₁
RevR d {Φ = Φ} {A} {B} p =
  ∀ {N w X} {m : RMode Φ X (ΔR w)} {δs δt}
  → RConvI d N w m δs δt → ∀ {k} → k ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
  → ℰ d k p w δt Vl (revM (rcR m (δr δt)) (substᵗ (δr δs) B) Vr)

ConR : Dir → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A B} → Φ ⊢ A ⊑ B → Set₁
ConR d {Φ = Φ} {A} {B} p =
  ∀ {N w X} {m : RMode Φ X (ΔR w)} {δs δt}
  → RConvI d N w m δs δt → ∀ {k} → ConRm d m k N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
  → ℰ d k p w δs Wl (conM (rcR m (δr δt)) (substᵗ (δr δs) B) Wr)

------------------------------------------------------------------------
-- Variables
------------------------------------------------------------------------

-- X itself
rev-pairXR : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w {N α′ δs δt}
  → RConvI d N w (r-pair x α′) δs δt → n ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n (X⊑Y x) w δs Vl Vr
  → ℰ d n (X⊑Y x) w δt Vl (Vr ↑ 〖 α′ , δr δt Y ↑ δr δs Y 〗)
rev-pairXR d zero x w h le vl vr r = ℰ-zero d (X⊑Y x) w
rev-pairXR d (suc k) {Φ} {X} {Y} x w {N} {α′} {δs} {δt} h le vl vr r
    with sealedR-inv
      (NowXR.sealRev {x = x} {d = d} {N = N} {w = w} {δs = δs} {δt = δt}
        {α′ = α′} (sealR h) (s≤s z≤n) le
        (from (𝒱-XY d (suc k) x w {δ = δs}) r))
rev-pairXR ≺ (suc k) {Φ} {X} {Y} x w {N} {α′} {δs} {δt} h le vl vr r
    | W′ , refl , r′ =
  ℰ-≡ ≺ (suc k) (X⊑Y x) w δt refl
    (sym (↑-pk (〖〗-self α′ (δr δt Y) (selfR h))))
    (ℰ-stepR ≺ (suc k) (X⊑Y x) w (conceal-reveal (value-sealed vr))
      (ℰ-value ≺ (suc k) (X⊑Y x) w vl (value-sealed vr)
        (to (𝒱-XY ≺ (suc k) x w {δ = δt}) r′)))
rev-pairXR ≻ (suc k) {Φ} {X} {Y} x w {N} {α′} {δs} {δt} h le vl vr r
    | W′ , refl , r′ =
  ℰ-≡ ≻ (suc k) (X⊑Y x) w δt refl
    (sym (↑-pk (〖〗-self α′ (δr δt Y) (selfR h))))
    (ℰ-stepR ≻ k (X⊑Y x) w (conceal-reveal (value-sealed vr))
      (ℰ-value ≻ k (X⊑Y x) w vl (value-sealed vr)
        (to (𝒱-XY ≻ k x w {δ = δt}) r′)))

con-pairXR : ∀ d n {Φ : Corr Δ Δ′} {X Y} (x : Φ ∋ X ↔ Y) w {N α′ δs δt}
  → RConvI d N w (r-pair x α′) δs δt → ConBR d n N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d n (X⊑Y x) w δt Wl Wr
  → ℰ d n (X⊑Y x) w δs Wl (Wr ↓ makeConceal α′ (δr δt Y) (δr δs Y))
con-pairXR d zero x w h cb wl wr r = ℰ-zero d (X⊑Y x) w
con-pairXR ≺ (suc k) {Φ} {X} {Y} x w {N} {α′} {δs} {δt} h cb wl wr r =
  ℰ-≡ ≺ (suc k) (X⊑Y x) w δs refl
    (sym (↓-pk (makeConceal-self α′ (δr δt Y) (selfR h))))
    (ℰ-value ≺ (suc k) (X⊑Y x) w wl (wr CT.↓ CT.seal)
      (to (𝒱-XY ≺ (suc k) x w {δ = δs})
        (NowXR.sealCon {x = x} {d = ≺} {N = N} {w = w} {δs = δs} {δt = δt}
          {α′ = α′} (sealR h) (s≤s z≤n) cb
          (from (𝒱-XY ≺ (suc k) x w {δ = δt}) r))))
con-pairXR ≻ (suc k) {Φ} {X} {Y} x w {N} {α′} {δs} {δt} h cb wl wr r =
  ℰ-≡ ≻ (suc k) (X⊑Y x) w δs refl
    (sym (↓-pk (makeConceal-self α′ (δr δt Y) (selfR h))))
    (ℰ-value ≻ (suc k) (X⊑Y x) w wl (wr CT.↓ CT.seal)
      (to (𝒱-XY ≻ (suc k) x w {δ = δs})
        (NowXR.sealCon {x = x} {d = ≻} {N = N} {w = w} {δs = δs} {δt = δt}
          {α′ = α′} (sealR h) (s≤s z≤n) cb
          (from (𝒱-XY ≻ (suc k) x w {δ = δt}) r))))

-- a paired variable
rev-varR : ∀ d {Φ : Corr Δ Δ′} {Z Y′} (z : Φ ∋ Z ↔ Y′) → RevR d (X⊑Y z)
rev-varR d z {m = r-none α′ R′} h {k} le vl vr r =
  NowR.revP h z tt le vl vr (from (𝒱-XY d k z _) r)
rev-varR d {Z = Z} z {X = X} {m = r-pair x α′} h le vl vr r with Z ≟ X
rev-varR d {Z = Z} z {X = X} {m = r-pair x α′} h {k} le vl vr r
    | no ne =
  NowR.revP h z ne le vl vr (from (𝒱-XY d k z _) r)
rev-varR d {Z = .X} z {X = X} {m = r-pair x α′} h le vl vr r
    | yes refl with ↔-functional x z
rev-varR d {Z = .X} z {X = X} {m = r-pair x α′} h le vl vr r
    | yes refl | refl with ↔-unique x z
rev-varR d {Z = .X} .x {X = X} {m = r-pair x α′} h {k} le vl vr r
    | yes refl | refl | refl =
  rev-pairXR d k x _ h le vl vr r

con-varR : ∀ d {Φ : Corr Δ Δ′} {Z Y′} (z : Φ ∋ Z ↔ Y′) → ConR d (X⊑Y z)
con-varR d z {m = r-none α′ R′} h {k} cb wl wr r =
  NowR.conP h z tt cb wl wr (from (𝒱-XY d k z _) r)
con-varR d {Z = Z} z {X = X} {m = r-pair x α′} h cb wl wr r with Z ≟ X
con-varR d {Z = Z} z {X = X} {m = r-pair x α′} h {k} cb wl wr r
    | no ne =
  NowR.conP h z ne (ConBR-≤ d cb) wl wr (from (𝒱-XY d k z _) r)
con-varR d {Z = .X} z {X = X} {m = r-pair x α′} h cb wl wr r
    | yes refl with ↔-functional x z
con-varR d {Z = .X} z {X = X} {m = r-pair x α′} h cb wl wr r
    | yes refl | refl with ↔-unique x z
con-varR d {Z = .X} .x {X = X} {m = r-pair x α′} h {k} cb wl wr r
    | yes refl | refl | refl =
  con-pairXR d k x _ h cb wl wr r

------------------------------------------------------------------------
-- Into `★` and at base types: the right's identity step
------------------------------------------------------------------------

revR★ : ∀ d {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) → RevR d p
revR★ ≺ p h {k} le vl vr r =
  ℰ-stepR ≺ k p _ (id-reveal vr)
    (ℰ-value ≺ k p _ vl vr (𝒱★-agree ≺ k p _ (agreeR h) r))
revR★ ≻ p h {zero} le vl vr r = ℰ-zero ≻ p _
revR★ ≻ p h {suc k} le vl vr r =
  ℰ-stepR ≻ k p _ (id-reveal vr)
    (ℰ-value ≻ k p _ vl vr
      (𝒱★-agree ≻ k p _ (agreeR h) (𝒱-down ≻ (n≤1+n k) p _ (goodS h) r)))

conR★ : ∀ d {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) → ConR d p
conR★ ≺ p h {k} cb wl wr r =
  ℰ-stepR ≺ k p _ (id-conceal wr)
    (ℰ-value ≺ k p _ wl wr (𝒱★-agree ≺ k p _ (≈ᴸ-sym (agreeR h)) r))
conR★ ≻ p h {zero} cb wl wr r = ℰ-zero ≻ p _
conR★ ≻ p h {suc k} cb wl wr r =
  ℰ-stepR ≻ k p _ (id-conceal wr)
    (ℰ-value ≻ k p _ wl wr
      (𝒱★-agree ≻ k p _ (≈ᴸ-sym (agreeR h))
        (𝒱-down ≻ (n≤1+n k) p _ (goodT h) r)))

revRι : ∀ d {Φ : Corr Δ Δ′} {ι} → RevR d (ι⊑ι {Φ = Φ} {ι = ι})
revRι d h {k} le vl vr r =
  ℰ-steps? d k ι⊑ι _ (goodT h) stay (step (id-reveal vr)) vl vr (ιι-δ d k r)

conRι : ∀ d {Φ : Corr Δ Δ′} {ι} → ConR d (ι⊑ι {Φ = Φ} {ι = ι})
conRι d h {k} cb wl wr r =
  ℰ-steps? d k ι⊑ι _ (goodS h) stay (step (id-conceal wr)) wl wr (ιι-δ d k r)

------------------------------------------------------------------------
-- Functions
------------------------------------------------------------------------

-- the right's step of an application: counted in `≻` only
ℰ-app-stepsR : ∀ d {n N} {Φ : Corr Δ Δ′} {B B′} (q : Φ ⊢ B ⊑ B′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr Mr′}
  → n ≤ N → Mr —→ Mr′
  → (∀ {s} → s ≤ n → ConBR d s N → ℰ d s q w δ Ml Mr′)
  → ℰ d n q w δ Ml Mr
ℰ-app-stepsR ≺ {n} q w le sr k = ℰ-stepR ≺ n q w sr (k ≤-refl le)
ℰ-app-stepsR ≻ {zero} q w le sr k = ℰ-zero ≻ q w
ℰ-app-stepsR ≻ {suc n} q w le sr k =
  ℰ-stepR ≻ n q w sr (k (n≤1+n n) le)

-- the right side's conversion, renamed into a future
module _ {Φ : Corr Δ Δ′} {X : TyVar Δ} {w w′ : World} (e : w′ ⊒ w)
    (m : RMode Φ X (ΔR w)) (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)) where

  rcRenR : ∀ (Q : Term (ΔR w′)) C
    → revM (rcR (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e)))
        (substᵗ (δr (δs ↑ᴵ e)) C) Q
      ≡ mplug (renameMFrame (ρR e)
          (revFrame (rcR m (δr δt)) (substᵗ (δr δs) C))) Q
  rcRenR Q C =
    trans (cong (λ c → revM c (substᵗ (δr (δs ↑ᴵ e)) C) Q)
            (rcR-↑ (ρR e) m (δr δt)))
      (sym (revFrame-ren (ρR e) (rcR m (δr δt)) (δr δs) C Q))

  ccRenR : ∀ (Q : Term (ΔR w′)) C
    → conM (rcR (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e)))
        (substᵗ (δr (δs ↑ᴵ e)) C) Q
      ≡ mplug (renameMFrame (ρR e)
          (conFrame (rcR m (δr δt)) (substᵗ (δr δs) C))) Q
  ccRenR Q C =
    trans (cong (λ c → conM c (substᵗ (δr (δs ↑ᴵ e)) C) Q)
            (rcR-↑ (ρR e) m (δr δt)))
      (sym (conFrame-ren (ρR e) (rcR m (δr δt)) (δr δs) C Q))

  -- the converted right value, renamed
  revVR : ∀ (V : Term (ΔR w)) C
    → renameᵗᵐ (ρR e) (revM (rcR m (δr δt)) (substᵗ (δr δs) C) V)
      ≡ revM (rcR (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e)))
          (substᵗ (δr (δs ↑ᴵ e)) C) (renameᵗᵐ (ρR e) V)
  revVR V C =
    trans (revM-ren (ρR e) (rcR m (δr δt)) (δr δs) C V)
      (cong (λ c → revM c (substᵗ (δr (δs ↑ᴵ e)) C) (renameᵗᵐ (ρR e) V))
        (sym (rcR-↑ (ρR e) m (δr δt))))

  conVR : ∀ (V : Term (ΔR w)) C
    → renameᵗᵐ (ρR e) (conM (rcR m (δr δt)) (substᵗ (δr δs) C) V)
      ≡ conM (rcR (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e)))
          (substᵗ (δr (δs ↑ᴵ e)) C) (renameᵗᵐ (ρR e) V)
  conVR V C =
    trans (conM-ren (ρR e) (rcR m (δr δt)) (δr δs) C V)
      (cong (λ c → conM c (substᵗ (δr (δs ↑ᴵ e)) C) (renameᵗᵐ (ρR e) V))
        (sym (rcR-↑ (ρR e) m (δr δt))))

module FunConvR {Δ Δ′} {Φ : Corr Δ Δ′} (d : Dir) (N : ℕ)
    {A A′ B B′} (p : Φ ⊢ A ⊑ A′) (q : Φ ⊢ B ⊑ B′)
    (revp : RevR d p) (conp : ConR d p) (revq : RevR d q) (conq : ConR d q)
    where

  -- a converted function applied, in the world of the function
  rev-at : ∀ {n} w {X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → funRel d n p q w δs Vl Vr
    → ∀ {Ul Ur} → Value Ul → Value Ur → 𝒱 d n p w δt Ul Ur
    → ℰ d n q w δt (Vl · Ul)
        (revM (rcR m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Vr · Ur)
  rev-at w {m = m} {δs} {δt} h le {Vl} {Vr} vl vr f {Ul} {Ur} ul ur a =
    ℰ-app-stepsR d q w le (rightApp (rcR m (δr δt)) vr ur)
      (λ {s} s≤n cb →
        app-core d s p q w vl vr nothing
          (revFrame (rcR m (δr δt)) (substᵗ (δr δs) B′))
          (conp h (ConBR→ConRb d (isNoneR m) cb) ul ur
            (𝒱-down d s≤n p w (goodT h) a))
          (funRel-down d s≤n p q w f)
          (λ e₂ {k} k≤s {Ql} {Qr} ql qr r →
            ℰᵍ-≡ refl (rcRenR e₂ m δs δt Qr B′)
              (revq (RConvI-↑ e₂ h) (≤-trans k≤s (≤-trans s≤n le))
                ql qr r)))

  con-at : ∀ {n} w {X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → ConRm d m n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → funRel d n p q w δt Wl Wr
    → ∀ {Ul Ur} → Value Ul → Value Ur → 𝒱 d n p w δs Ul Ur
    → ℰ d n q w δs (Wl · Ul)
        (conM (rcR m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Wr · Ur)
  con-at w {m = m} {δs} {δt} h cb {Wl} {Wr} wl wr f {Ul} {Ur} ul ur a =
    ℰ-app-stepsR d q w (ConRb-≤ d (isNoneR m) cb)
      (rightAppC (rcR m (δr δt)) wr ur)
      (λ {s} s≤n cb′ →
        app-core d s p q w wl wr nothing
          (conFrame (rcR m (δr δt)) (substᵗ (δr δs) B′))
          (revp h (≤-trans s≤n (ConRb-≤ d (isNoneR m) cb)) ul ur
            (𝒱-down d s≤n p w (goodS h) a))
          (funRel-down d s≤n p q w f)
          (λ e₂ {k} k≤s {Ql} {Qr} ql qr r →
            ℰᵍ-≡ refl (ccRenR e₂ m δs δt Qr B′)
              (conq (RConvI-↑ e₂ h)
                (subst (λ b → ConRb d b k N) (sym (isNoneR-↑ (ρR e₂) m))
                  (ConBR→ConRb d (isNoneR m) (ConBR-down d k≤s cb′)))
                ql qr r)))

  fun-rev : ∀ {n w X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → funRel d n p q w δs Vl Vr
    → funRel d n p q w δt Vl
        (revM (rcR m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Vr)
  fun-rev {n} {w} {m = m} {δs} {δt} h le {Vl} {Vr} vl vr f
      {w′} e {n′} le′ Ul Ur ul ur a =
    ℰᵍ-map d n′ w′ (λ le″ w″ e″ V V′ → 𝒱≤-cast d le″ (≤′-trans le″ le′) q w″)
      (ℰᵍ-≡ refl (cong (_· Ur) (sym (revVR e m δs δt Vr (A′ ⇒ B′))))
        (rev-at w′ (RConvI-↑ e h) (≤-trans (≤′⇒≤ le′) le)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (renameᵗᵐ-preserves-Value (ρR e) vr)
          (funRel-down d (≤′⇒≤ le′) p q w′ (funRel-mono d n p q e f))
          ul ur (𝒱≤-cast d le′ ≤′-refl p w′ a)))

  fun-con : ∀ {n w X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → ConRm d m n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → funRel d n p q w δt Wl Wr
    → funRel d n p q w δs Wl
        (conM (rcR m (δr δt)) (substᵗ (δr δs) (A′ ⇒ B′)) Wr)
  fun-con {n} {w} {m = m} {δs} {δt} h cb {Wl} {Wr} wl wr f
      {w′} e {n′} le′ Ul Ur ul ur a =
    ℰᵍ-map d n′ w′ (λ le″ w″ e″ V V′ → 𝒱≤-cast d le″ (≤′-trans le″ le′) q w″)
      (ℰᵍ-≡ refl (cong (_· Ur) (sym (conVR e m δs δt Wr (A′ ⇒ B′))))
        (con-at w′ (RConvI-↑ e h) (ConRm-↑ d (ρR e) m (≤′⇒≤ le′) cb)
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (renameᵗᵐ-preserves-Value (ρR e) wr)
          (funRel-down d (≤′⇒≤ le′) p q w′ (funRel-mono d n p q e f))
          ul ur (𝒱≤-cast d le′ ≤′-refl p w′ a)))

------------------------------------------------------------------------
-- `∀⊑`: only the left instantiates, and its instantiation is read
-- from the clause
------------------------------------------------------------------------

module OnlyVR (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : only Φ ⊢ A ⊑ B) (rev : RevR d p) (con : ConR d p) where

  private
    -- the clause at the descriptor's own bound, with the left types of
    -- another interpretation that agrees with it on the left
    clauseAt : ∀ {n} w {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)}
      → (∀ Z → δl δ Z ≡ δl δ′ Z)
      → ∀ {Vl Vr} → allOnly d n p w δ Vl Vr
      → ∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → (c : SDesc (ΔL w′) (ΔR w′))
      → ℰ d n′ p w′ (extOnlyI (leftTyS c)
            (sem (onlyLeafS d (≤′-refl {n′}) c)) (δ ↑ᴵ e))
          (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ′ ↑ᴵ e))) A
            [ leftTyS c ])
          (renameᵗᵐ (ρR e) Vr)
    clauseAt w {δ} {δ′} eqL {Vl} {Vr} r e {n′} le c =
      ℰᵍ-≡
        (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
          (substᵗ-cong A (exts-cong (λ Z →
            cong (renameᵗ (toRenameᵗ (ρL e))) (eqL Z)))))
        refl
        (ℰᵍ-map d _ _
          (λ le′ w″ e′ V V′ r′ →
            𝒱≤-resp d le′ p w″
              (↑ᴵ-resp
                (extOnlyI-resp (onlyLeafS-≈ d (≤⇒≤′ le) ≤′-refl c) ≈ᴵ-refl)
                e′)
              (𝒱≤-cast d (≤′-trans le′ (≤⇒≤′ le)) le′ p w″ r′))
          (r e (≤⇒≤′ le) c))

  revV : ∀ {n} w {X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → allOnly d n p w δs Vl Vr
    → allOnly d n p w δt Vl (revM (rcR m (δr δt)) (substᵗ (δr δs) B) Vr)
  revV {n} w {m = m} {δs} {δt} h le {Vl} {Vr} vl vr r =
    allOnly-from d n p w {δ = δt} λ {w′} e {n′} le′ c →
      ℰᵍ-≡ refl (sym (revVR e m δs δt Vr B))
        (ℰ-bind₂ d n′ p p _
          {δ₁ = extOnlyI (leftTyS c) (L w′ n′ c) (δs ↑ᴵ e)}
          {δ₂ = extOnlyI (leftTyS c) (L w′ n′ c) (δt ↑ᴵ e)}
          nothing
          (revFrame (rcR (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e)))
            (substᵗ (δr (δs ↑ᴵ e)) B))
          (clauseAt w {δ = δs} {δ′ = δt} (tyL h) r e le′ c)
          (λ e₂ {k} k≤ {Ql} {Qr} ql qr q →
            ℰᵍ-≡ refl
              (trans (rcRenR e₂ (RMode-only (RMode-↑ (ρR e) m))
                        (extOnlyI (leftTyS c) (L w′ n′ c) (δs ↑ᴵ e))
                        (extOnlyI (leftTyS c) (L w′ n′ c) (δt ↑ᴵ e)) Qr B)
                (cong (λ rc → mplug (renameMFrame (ρR e₂)
                                (revFrame rc (substᵗ (δr (δs ↑ᴵ e)) B))) Qr)
                  (cong₂ (λ a b → just (a , b))
                    (rα-only (RMode-↑ (ρR e) m))
                    (rR-only (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e))))))
              (rev (RConvI-↑ e₂
                     (RConvI-extOnly {T = leftTyS c} {l = L w′ n′ c}
                       (onlyLeafS-good d (≤′-refl {n′}) c) (RConvI-↑ e h)))
                (≤-trans k≤ (≤-trans le′ le)) ql qr q)))
    where
    L : ∀ w′ n′ (c : SDesc (ΔL w′) (ΔR w′)) → Leaf (ΔL w′) (ΔR w′)
    L w′ n′ c = sem (onlyLeafS d (≤′-refl {n′}) c)

  conV : ∀ {n} w {X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → ConRm d m n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → allOnly d n p w δt Wl Wr
    → allOnly d n p w δs Wl (conM (rcR m (δr δt)) (substᵗ (δr δs) B) Wr)
  conV {n} w {m = m} {δs} {δt} h cb {Wl} {Wr} wl wr r =
    allOnly-from d n p w {δ = δs} λ {w′} e {n′} le′ c →
      ℰᵍ-≡ refl (sym (conVR e m δs δt Wr B))
        (ℰ-bind₂ d n′ p p _
          {δ₁ = extOnlyI (leftTyS c) (L w′ n′ c) (δt ↑ᴵ e)}
          {δ₂ = extOnlyI (leftTyS c) (L w′ n′ c) (δs ↑ᴵ e)}
          nothing
          (conFrame (rcR (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e)))
            (substᵗ (δr (δs ↑ᴵ e)) B))
          (clauseAt w {δ = δt} {δ′ = δs} (λ Z → sym (tyL h Z)) r e le′ c)
          (λ e₂ {k} k≤ {Ql} {Qr} ql qr q →
            ℰᵍ-≡ refl
              (trans (ccRenR e₂ (RMode-only (RMode-↑ (ρR e) m))
                        (extOnlyI (leftTyS c) (L w′ n′ c) (δs ↑ᴵ e))
                        (extOnlyI (leftTyS c) (L w′ n′ c) (δt ↑ᴵ e)) Qr B)
                (cong (λ rc → mplug (renameMFrame (ρR e₂)
                                (conFrame rc (substᵗ (δr (δs ↑ᴵ e)) B))) Qr)
                  (cong₂ (λ a b → just (a , b))
                    (rα-only (RMode-↑ (ρR e) m))
                    (rR-only (RMode-↑ (ρR e) m) (δr (δt ↑ᴵ e))))))
              (con (RConvI-↑ e₂
                     (RConvI-extOnly {T = leftTyS c} {l = L w′ n′ c}
                       (onlyLeafS-good d (≤′-refl {n′}) c) (RConvI-↑ e h)))
                (subst (λ b → ConRb d b k _)
                  (sym (trans
                    (isNoneR-↑ (ρR e₂) (RMode-only (RMode-↑ (ρR e) m)))
                    (trans (isNoneR-only (RMode-↑ (ρR e) m))
                      (isNoneR-↑ (ρR e) m))))
                  (ConRb-down d (isNoneR m) (≤-trans k≤ le′) cb))
                ql qr q)))
    where
    L : ∀ w′ n′ (c : SDesc (ΔL w′) (ΔR w′)) → Leaf (ΔL w′) (ΔR w′)
    L w′ n′ c = sem (onlyLeafS d (≤′-refl {n′}) c)

------------------------------------------------------------------------
-- Allocating a right store variable
------------------------------------------------------------------------

-- the right allocates
tagsR : (w : World) → TyVar (ΔL w) → Tag (ΔL w) (suc (ΔR w))
tagsR w X = renameTag id↪ᵗ wk↪ᵗ (tag w X)

okBindR : ∀ (w : World) (T′ : Ty (ΔR w)) X
  → tagsR w (toRenameᵗ (embedᶜˢ ([] {ΔL w})) X)
    ≡ renameTag (embedᶜˢ ([] {ΔL w})) (embedᶜˢ (bind T′ ∷ [])) (tag w X)
okBindR w T′ X =
  trans (cong (tagsR w) (toRename-id-eq X))
    (sym (cong (λ ρ → renameTag id↪ᵗ ρ (tag w X)) (embed-bind T′)))

-- whether a right-only conversion's stage may stay at the target's
-- bound
UpBR : Dir → ℕ → ℕ → Set
UpBR ≺ s n = n ≤ s
UpBR ≻ s n = ⊤

-- one right store step, counted in `≻` only
antiR₁ : ∀ d {n N} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) {w : World}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΘR} {Ml : Term (ΔL w)}
    {Mr : Term (ΔR w)} {Mr′ : Term ΘR} {χR : StoreChange (ΔR w) ΘR}
  → n ≤ N → Mr —→[ χR ] Mr′
  → (tags : TyVar (ΔL w) → Tag (ΔL w) ΘR)
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ ([] {ΔL w})) X)
            ≡ renameTag (embedᶜˢ ([] {ΔL w})) (embedᶜˢ (χR ∷ [])) (tag w X))
  → (∀ {s} → s ≤′ n → s ≤ N → UpBR d s n
       → ℰ d s p (world (ΔL w) ΘR tags)
           (δ ↑ᴵ stepExt [] (χR ∷ []) tags ok) Ml Mr′)
  → ℰ d n p w δ Ml Mr
antiR₁ ≺ {n} p le sr tags ok k =
  ℰ-anti-≺ p none (↠-step sr ↠-refl) tags ok (k ≤′-refl le ≤-refl)
antiR₁ ≻ {zero} p le sr tags ok k = ℰ-zero ≻ p _
antiR₁ ≻ {suc s} p le sr tags ok k =
  ℰ-anti-≻ p ↠-refl (more sr none) tags ok
    (k (≤′-step ≤′-refl) (≤-trans (n≤1+n s) le) tt)

------------------------------------------------------------------------
-- A right prefix of a sealed descriptor
------------------------------------------------------------------------

module _ (d : Dir) {n′ n} (le : n′ ≤′ n) {ΘL ΘR}
    (Xs : List (TyVar ΘL)) (Ys : List (TyVar ΘR)) (c : Desc ΘL ΘR)
    (β′ : TyVar ΘR) (k : ℕ) (w : World)
    (τL : ΘL ↪ᵗ ΔL w) (τR : ΘR ↪ᵗ ΔR w) where

  private
    c′ = renameDesc τL τR c
    Xs′ = map (renameVar τL) Xs
    Ys′ = map (renameVar τR) Ys

  sealSR→ : ∀ {V V′}
    → leafBelowS d le (sdesc Xs (β′ ∷ Ys) c) k w τL τR V V′
    → sealedR (renameVar τR β′) (repR Ys′ c′)
        (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′
  sealSR→ r = peelSL-sealedR Xs′ c′ (peelSL-map Xs′ c′ peelSR→ r)

  sealSR← : ∀ {V V′}
    → sealedR (renameVar τR β′) (repR Ys′ c′)
        (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′
    → leafBelowS d le (sdesc Xs (β′ ∷ Ys) c) k w τL τR V V′
  sealSR← r = peelSL-map Xs′ c′ peelSR← (sealedR-peelSL Xs′ c′ r)

-- the stage of a right-sealed leaf is at most the stage
rStage-≤ : ∀ d k → rStage d k ≤ k
rStage-≤ ≺ k = ≤-refl
rStage-≤ ≻ zero = z≤n
rStage-≤ ≻ (suc k) = n≤1+n k

-- the target leaf, written into the prefixed descriptor's core, at the
-- stages a right-only conceal needs
writeUpR : ∀ d {s n a b} (le_s : s ≤′ a) (le_n : n ≤′ b) {w w₁ : World}
    (e₁ : w₁ ⊒ w) (c₀ : SDesc (ΔL w) (ΔR w)) {w′} (e : w′ ⊒ w₁) k
  → UpBR d s n → rBelow d k s → ∀ {V V′}
  → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
      (transportLeaf (ρL e₁) (ρR e₁) (sem (leafBelowS d le_n c₀)))) V V′
  → leafBelowS d le_s (renameSDesc (ρL e₁) (ρR e₁) c₀) k w′
      (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
writeUpR ≺ le_s le_n e₁ c₀ e k up lt r =
  from (leafBelowS-ren ≺ le_s (ρL e₁) (ρR e₁) c₀ k _ _ _)
    (leafBelowS-up ≺ le_n le_s c₀ up _ _ _ r)
writeUpR ≻ le_s le_n e₁ c₀ e k up lt r =
  from (leafBelowS-ren ≻ le_s (ρL e₁) (ρR e₁) c₀ k _ _ _)
    (leafBelowS-bound ≻ le_n le_s c₀ lt _ _ _ r)

------------------------------------------------------------------------
-- The seal hypotheses for a type application's bound variable
------------------------------------------------------------------------

-- V's clause, used at the new right store variable: the leaf of the
-- prefixed descriptor, with bound s, against the target's leaf, with
-- bound n
module SealNewR (d : Dir) {s n a b} (le_s : s ≤′ a) (le_n : n ≤′ b)
    (s≤n : s ≤ n) {w w₁ : World} (e₁ : w₁ ⊒ w)
    (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
    (c : Desc (ΔL w) (ΔR w)) where

  private
    c₀ = sdesc Xs Ys c
    cs₁ = renameSDesc (ρL e₁) (ρR e₁) c₀
    Lt = sem (leafBelowS d le_n c₀)
    Xs₁ = map (renameVar (ρL e₁)) Xs
    Ys₁ = map (renameVar (ρR e₁)) Ys
    c₁ = renameDesc (ρL e₁) (ρR e₁) c

  -- the target leaf, read in a future of w₁
  readT : ∀ {w′} (e : w′ ⊒ w₁) k {V V′}
    → leafBelowS d le_s cs₁ k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
    → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
        (transportLeaf (ρL e₁) (ρR e₁) Lt)) V V′
  readT e k r =
    leafBelowS-up d le_s le_n c₀ s≤n _ _ _
      (to (leafBelowS-ren d le_s (ρL e₁) (ρR e₁) c₀ k _ _ _) r)

  -- the representation of the new seal
  repβ′ : ∀ {w′} (e : w′ ⊒ w₁)
    → repR (map (renameVar (id↪ᵗ ∘↪ ρR e)) Ys₁)
        (renameDesc (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) c₁)
      ≡ renameᵗ (toRenameᵗ (ρR e)) (renameᵗ (toRenameᵗ (ρR e₁)) (repR Ys c))
  repβ′ e =
    trans (repR-rename (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) Ys₁ c₁)
      (trans (cong (λ σ → renameᵗ (toRenameᵗ σ) (repR Ys₁ c₁))
               (∘↪-idˡ (ρR e)))
        (cong (renameᵗ (toRenameᵗ (ρR e)))
          (repR-rename (ρL e₁) (ρR e₁) Ys c)))

  varβR : ∀ {w′} (e : w′ ⊒ w₁) (Y : TyVar (ΔR w₁))
    → renameVar (id↪ᵗ ∘↪ ρR e) Y ≡ toRenameᵗ (ρR e) Y
  varβR e Y = cong (λ σ → toRenameᵗ σ Y) (∘↪-idˡ (ρR e))

  -- a paired binder whose right converts at β′ and whose left does not
  -- move
  sealNewR : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
      {T : Ty (ΔL w₁)} (β′ : TyVar (ΔR w₁))
    → UpBR d s n
    → SealR d s w₁ (r-pair {Φ = pair Φ} {X = zero} ↔-here β′)
        (extPairI T (＇ β′)
          (sem (leafBelowS d le_s (sdesc Xs₁ (β′ ∷ Ys₁) c₁)))
          (δt ↑ᴵ e₁))
        (extPairI (repL Xs c) (repR Ys c) Lt δt ↑ᴵ e₁)
  sealNewR β′ up = rev , con
    where
    rev : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k ≤ s → ∀ {Vl Vr}
      → leafBelowS d le_s (sdesc Xs₁ (β′ ∷ Ys₁) c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) Vl Vr
      → sealedR (toRenameᵗ (ρR e) β′)
          (renameᵗ (toRenameᵗ (ρR e))
            (renameᵗ (toRenameᵗ (ρR e₁)) (repR Ys c)))
          (leafRel d (rStage d k) w′ (transportLeaf (ρL e) (ρR e)
            (transportLeaf (ρL e₁) (ρR e₁) Lt))) Vl Vr
    rev {w′} e {k} pos le r =
      sealedR-map (varβR e β′) (repβ′ e)
        (λ q → leafBelowS-down d le_n c₀ (rStage-≤ d k) w′ _ _
                 (readT e k q))
        (sealSR→ d le_s Xs₁ Ys₁ c₁ β′ k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) r)

    con : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → rBelow d k s
      → ∀ {Vl Wr}
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
          (transportLeaf (ρL e₁) (ρR e₁) Lt)) Vl Wr
      → leafBelowS d le_s (sdesc Xs₁ (β′ ∷ Ys₁) c₁) k w′
          (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) Vl
          (Wr ↓ seal (toRenameᵗ (ρR e) β′)
            (renameᵗ (toRenameᵗ (ρR e))
              (renameᵗ (toRenameᵗ (ρR e₁)) (repR Ys c))))
    con {w′} e {k} pos lt r =
      sealSR← d le_s Xs₁ Ys₁ c₁ β′ k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
        ((sym (varβR e β′) , sym (repβ′ e)) ,
          writeUpR d le_s le_n e₁ c₀ e k up lt r)

------------------------------------------------------------------------
-- The hypotheses for a type application's bound variable
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {d : Dir} {N : ℕ}
    {w : World} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)} {w₁ : World} (e₁ : w₁ ⊒ w)
    {β′ : TyVar (ΔR w₁)} (nb : ∀ Y → toRenameᵗ (ρR e₁) Y ≢ β′)
    {Ls : Leaf (ΔL w₁) (ΔR w₁)} {Lt : Leaf (ΔL w) (ΔR w)}
    {Tr : Ty (ΔR w)} where

  private
    ρl = toRenameᵗ (ρL e₁)
    ρr = toRenameᵗ (ρR e₁)

  -- a paired binder; the left does not convert, and is instantiated at
  -- Tl itself
  RConvI-newR : ∀ {Tl : Ty (ΔL w)} {T : Ty (ΔL w₁)} {Nβ}
    → T ≡ renameᵗ ρl Tl → Nβ ≤ N
    → FreshIR Φ d N w δt
    → GoodLeaf Ls → GoodLeaf Lt → FreshR d w Lt Tr
    → SealR d Nβ w₁ (r-pair {Φ = pair Φ} {X = zero} ↔-here β′)
        (extPairI T (＇ β′) Ls (δt ↑ᴵ e₁))
        (extPairI Tl Tr Lt δt ↑ᴵ e₁)
    → RConvI d Nβ w₁ (r-pair {Φ = pair Φ} {X = zero} ↔-here β′)
        (extPairI T (＇ β′) Ls (δt ↑ᴵ e₁))
        (extPairI Tl Tr Lt δt ↑ᴵ e₁)
  goodS (RConvI-newR {T = T} eqT le h gs gt ft si) =
    GoodI-extPairI {T = T} {T′ = ＇ β′} {δ = δt ↑ᴵ e₁} gs
      (GoodI-↑ {δ = δt} (fgoodR h) e₁)
  goodT (RConvI-newR {Tl = Tl} eqT le h gs gt ft si) =
    GoodI-↑ {δ = extPairI Tl Tr Lt δt}
      (GoodI-extPairI {T = Tl} {T′ = Tr} {δ = δt} gt (fgoodR h)) e₁
  selfR (RConvI-newR eqT le h gs gt ft si) = refl
  tyL (RConvI-newR eqT le h gs gt ft si) zero = eqT
  tyL (RConvI-newR eqT le h gs gt ft si) (suc Z) = refl
  tyR (RConvI-newR eqT le h gs gt ft si) zero = replaceTy-self β′ _
  tyR (RConvI-newR eqT le h gs gt ft si) (suc Y) =
    replaceTy-new ρr _ nb (δr δt Y)
  leafO (RConvI-newR eqT le h gs gt ft si) zero o = ⊥-elim (o refl)
  leafO (RConvI-newR eqT le h gs gt ft si) (suc Z) o = ≈ˡ-refl
  convP (RConvI-newR eqT le h gs gt ft si) ↔-here o = ⊥-elim (o refl)
  convP (RConvI-newR eqT le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) o =
    fresh→convR {d = d} e₁ {L = leaf δt Z} nb (renameᵗ ρr Tr) (fR h z)
  genR (RConvI-newR eqT le h gs gt ft si) ↔-here =
    FreshR-↑ {d = d} e₁ {L = Lt} {Tr} ft
  genR (RConvI-newR eqT le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) =
    FreshR-↑ {d = d} e₁ {L = leaf δt Z} {δr δt Y′} (fR h z)
  genRS (RConvI-newR eqT le h gs gt ft si) ↔-here =
    storeFreshR {d = d} {N = N} {w = w₁} {L = Ls} gs {γ′ = β′}
  genRS (RConvI-newR eqT le h gs gt ft si) (↔-pair {X = Z} {Y = Y′} z) =
    FreshR-↑ {d = d} e₁ {L = leaf δt Z} {δr δt Y′} (fR h z)
  sealR (RConvI-newR eqT le h gs gt ft si) = si
  oracleR (RConvI-newR eqT le h gs gt ft si) = OracleR-down le (forcR h)

------------------------------------------------------------------------
-- `∀⊑∀`: the right instantiates its proxy; the left's instantiation is
-- read from the clause at a right-sealed descriptor
------------------------------------------------------------------------

module PairR (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B) (rev : RevR d p) (con : ConR d p) where

  private
    cong₃′ : ∀ {Θ} {M M′ : Term Θ} {C C′ T T″}
      → M ≡ M′ → C ≡ C′ → T ≡ T″ → M ⦂∀ C [ T ] ≡ M′ ⦂∀ C′ [ T″ ]
    cong₃′ refl refl refl = refl

  pairRevR : ∀ {n} w {X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → allPair d n p w δs Vl Vr
    → ∀ Xs Ys c → WFDesc c
    → ℰ d n p w (extPairI (repL Xs c) (repR Ys c)
          (sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))) δt)
        (Vl ⦂∀ substᵗ (extsᵗ (δl δt)) A [ repL Xs c ])
        ((Vr ↑ `∀↑ 〖 suc (rα m) , ⇑ᵗ (rR m (δr δt))
                    ↑ substᵗ (extsᵗ (δr δs)) B 〗)
           ⦂∀ substᵗ (extsᵗ (δr δt)) B [ repR Ys c ])
  pairRevR {n} w {X} {m} {δs} {δt} h le {Vl} {Vr} vl vr r Xs Ys c wf =
    antiR₁ d p le stepR (tagsR w) (okBindR w Tr) inner
    where
    Tl = repL Xs c
    Tr = repR Ys c
    α′ = rα m
    R′ = rR m (δr δt)
    cR = 〖 suc α′ , ⇑ᵗ R′ ↑ substᵗ (extsᵗ (δr δs)) B 〗
    BtL = substᵗ (extsᵗ (δl δt)) A
    BtR = substᵗ (extsᵗ (δr δt)) B
    stepR = revInst cR vr (tgt-body α′ R′ (δr δs) (δr δt) (tyR h) B)

    e₁ = stepExt [] (bind Tr ∷ []) (tagsR w) (okBindR w Tr)
    w₁ = world (ΔL w) (suc (ΔR w)) (tagsR w)
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    T₁ = repL Xs₁ c₁
    Lt = sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))
    m₀ = RMode-↑ ρR₁ m
    m₁ = RMode-pair m₀

    α₁≡ : rα m₁ ≡ suc α′
    α₁≡ = trans (rα-pair m₀) (trans (rα-↑ ρR₁ m) (embed-var Tr α′))

    R₁≡ : rR m₁ (＇ zero •ˢ δr (δt ↑ᴵ e₁)) ≡ ⇑ᵗ R′
    R₁≡ = trans (rR-pair m₀ (δr (δt ↑ᴵ e₁)) (＇ zero))
      (trans (rR-↑ ρR₁ m (δr δt)) (shift-ty Tr R′))

    ne₀ : zero ≢ rα m₀
    ne₀ eq = new-bind Tr α′ (sym (trans eq (rα-↑ ρR₁ m)))

    inner : ∀ {s} → s ≤′ n → s ≤ N → UpBR d s n
      → ℰ d s p w₁ (extPairI Tl Tr Lt δt ↑ᴵ e₁)
          (Vl ⦂∀ BtL [ Tl ])
          ((⇑ᵗᵐ Vr ⦂∀ (bind Tr ▷ᵇ substᵗ (extsᵗ (δr δs)) B) [ ＇ zero ])
             ↑ cR ↑ 〖 zero , ⇑ᵗ Tr ↑ BtR 〗)
    inner {s} le_s s≤N up =
      ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δtg}
        nothing (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BtR 〗))
        (ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δtβ}
          nothing (just (reveal cR)) clause K₁)
        K₂
      where
      c″ = sdesc Xs₁ (zero ∷ Ys₁) c₁
      Ls = sem (leafBelowS d le_s c″)
      gLs = leafBelowS-good d le_s c″
      δsβ = extPairI T₁ (＇ zero) Ls (δs ↑ᴵ e₁)
      δtβ = extPairI T₁ (＇ zero) Ls (δt ↑ᴵ e₁)
      δtg = extPairI Tl Tr Lt δt ↑ᴵ e₁

      hα : RConvI d N w₁ m₁ δsβ δtβ
      hα = RConvI-extPair {T = T₁} {l = Ls} gLs ne₀
        (storeConvR {d = d} {N = N} {w = w₁} gLs {γ′ = zero}
          (rR m₀ (δr (δt ↑ᴵ e₁))) ne₀)
        (storeFreshR {d = d} {N = N} {w = w₁} gLs {γ′ = zero})
        (RConvI-↑ e₁ h)

      hβ : RConvI d s w₁ (r-pair {Φ = pair Φ} {X = zero} ↔-here zero)
        δtβ δtg
      hβ = RConvI-newR e₁ (new-bind Tr) {Ls = Ls} {Lt = Lt} {Tr = Tr}
        {Tl = Tl} {T = T₁} (repL-rename ρL₁ ρR₁ Xs c) s≤N (freshTR h) gLs
        (leafBelowS-good d (≤′-refl {n}) (sdesc Xs Ys c))
        (oracleR h (≤′-refl {n}) le (sdesc Xs Ys c) wf)
        (SealNewR.sealNewR d le_s (≤′-refl {n}) (≤′⇒≤ le_s) e₁ Xs Ys c
          {Φ = Φ} {δt = δt} {T = T₁} zero up)

      clause : ℰ d s p w₁ δsβ (Vl ⦂∀ BtL [ Tl ])
        (⇑ᵗᵐ Vr ⦂∀ (bind Tr ▷ᵇ substᵗ (extsᵗ (δr δs)) B) [ ＇ zero ])
      clause =
        ℰᵍ-≡
          (cong₃′ (renameᵗᵐ-id Vl)
            (substᵗ-cong A (exts-cong (λ Z →
              trans (renameTy-id (δl δs Z)) (tyL h Z))))
            (trans (repL-rename ρL₁ ρR₁ Xs c) (renameTy-id Tl)))
          (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tr Vr)
            (annot Tr (δr δs) B))
          (ℰᵍ-map d s w₁
            (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
            (r e₁ le_s c″ (WFDesc-rename ρL₁ ρR₁ c wf)))

      K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₂ (δsβ ↑ᴵ e₂) Ql Qr
        → ℰ d k p w₂ (δtβ ↑ᴵ e₂) Ql
            (mplug (renameMFrame (ρR e₂) (just (reveal cR))) Qr)
      K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡ refl
          (trans (rcRenR e₂ m₁ δsβ δtβ Qr B)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρR e₂))
              (pk-〖〗 α₁≡ R₁≡ (open0 Tr (δr δs) B)))))
          (rev (RConvI-↑ e₂ hα) (≤-trans k≤s s≤N) ql qr q)

      K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₃ (δtβ ↑ᴵ e₃) Ql Qr
        → ℰ d k p w₃ (δtg ↑ᴵ e₃) Ql
            (mplug (renameMFrame (ρR e₃)
              (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BtR 〗))) Qr)
      K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡ refl
          (trans (rcRenR e₃ (r-pair {Φ = pair Φ} {X = zero} ↔-here zero)
                    δtβ δtg Qr B)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρR e₃))
              (pk-〖〗 refl (shift-ty Tr Tr) (open0 Tr (δr δt) B)))))
          (rev (RConvI-↑ e₃ hβ) k≤s ql qr q)

  pairConR : ∀ {n} w {X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → ConRm d m n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → allPair d n p w δt Wl Wr
    → ∀ Xs Ys c → WFDesc c
    → ℰ d n p w (extPairI (repL Xs c) (repR Ys c)
          (sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))) δs)
        (Wl ⦂∀ substᵗ (extsᵗ (δl δs)) A [ repL Xs c ])
        ((Wr ↓ `∀↓ makeConceal (suc (rα m)) (⇑ᵗ (rR m (δr δt)))
                    (substᵗ (extsᵗ (δr δs)) B))
           ⦂∀ substᵗ (extsᵗ (δr δs)) B [ repR Ys c ])
  pairConR {n} w {X} {m} {δs} {δt} h cb {Wl} {Wr} wl wr r Xs Ys c wf =
    antiR₁ d p (ConRb-≤ d (isNoneR m) cb) stepR (tagsR w) (okBindR w Tr)
      inner
    where
    Tl = repL Xs c
    Tr = repR Ys c
    α′ = rα m
    R′ = rR m (δr δt)
    BsL = substᵗ (extsᵗ (δl δs)) A
    BsR = substᵗ (extsᵗ (δr δs)) B
    cR = makeConceal (suc α′) (⇑ᵗ R′) BsR

    tgtR : replaceTy (suc α′) (⇑ᵗ R′) BsR ≡ substᵗ (extsᵗ (δr δt)) B
    tgtR = tgt-body α′ R′ (δr δs) (δr δt) (tyR h) B

    stepR = conInst {T = Tr} cR wr refl

    e₁ = stepExt [] (bind Tr ∷ []) (tagsR w) (okBindR w Tr)
    w₁ = world (ΔL w) (suc (ΔR w)) (tagsR w)
    ρL₁ = ρL e₁
    ρR₁ = ρR e₁
    Xs₁ = map (renameVar ρL₁) Xs
    Ys₁ = map (renameVar ρR₁) Ys
    c₁ = renameDesc ρL₁ ρR₁ c
    T₁ = repL Xs₁ c₁
    Lt = sem (leafBelowS d (≤′-refl {n}) (sdesc Xs Ys c))
    m₀ = RMode-↑ ρR₁ m
    m₁ = RMode-pair m₀

    α₁≡ : rα m₁ ≡ suc α′
    α₁≡ = trans (rα-pair m₀) (trans (rα-↑ ρR₁ m) (embed-var Tr α′))

    R₁≡ : rR m₁ (＇ zero •ˢ δr (δt ↑ᴵ e₁)) ≡ ⇑ᵗ R′
    R₁≡ = trans (rR-pair m₀ (δr (δt ↑ᴵ e₁)) (＇ zero))
      (trans (rR-↑ ρR₁ m (δr δt)) (shift-ty Tr R′))

    ne₀ : zero ≢ rα m₀
    ne₀ eq = new-bind Tr α′ (sym (trans eq (rα-↑ ρR₁ m)))

    inner : ∀ {s} → s ≤′ n → s ≤ N → UpBR d s n
      → ℰ d s p w₁ (extPairI Tl Tr Lt δs ↑ᴵ e₁)
          (Wl ⦂∀ BsL [ Tl ])
          ((⇑ᵗᵐ Wr ⦂∀ (bind Tr ▷ᵇ replaceTy (suc α′) (⇑ᵗ R′) BsR) [ ＇ zero ])
             ↓ cR ↑ 〖 zero , ⇑ᵗ Tr ↑ BsR 〗)
    inner {s} le_s s≤N up =
      ℰ-bind₂ d s p p w₁ {δ₁ = δsβ} {δ₂ = δsg}
        nothing (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BsR 〗))
        (ℰ-bind₂ d s p p w₁ {δ₁ = δtβ} {δ₂ = δsβ}
          nothing (just (conceal cR)) clause K₁)
        K₂
      where
      c″ = sdesc Xs₁ (zero ∷ Ys₁) c₁
      Ls = sem (leafBelowS d le_s c″)
      gLs = leafBelowS-good d le_s c″
      δsβ = extPairI T₁ (＇ zero) Ls (δs ↑ᴵ e₁)
      δtβ = extPairI T₁ (＇ zero) Ls (δt ↑ᴵ e₁)
      δsg = extPairI Tl Tr Lt δs ↑ᴵ e₁

      hα : RConvI d N w₁ m₁ δsβ δtβ
      hα = RConvI-extPair {T = T₁} {l = Ls} gLs ne₀
        (storeConvR {d = d} {N = N} {w = w₁} gLs {γ′ = zero}
          (rR m₀ (δr (δt ↑ᴵ e₁))) ne₀)
        (storeFreshR {d = d} {N = N} {w = w₁} gLs {γ′ = zero})
        (RConvI-↑ e₁ h)

      hβ : RConvI d s w₁ (r-pair {Φ = pair Φ} {X = zero} ↔-here zero)
        δsβ δsg
      hβ = RConvI-newR e₁ (new-bind Tr) {Ls = Ls} {Lt = Lt} {Tr = Tr}
        {Tl = Tl} {T = T₁} (repL-rename ρL₁ ρR₁ Xs c) s≤N (freshSR h) gLs
        (leafBelowS-good d (≤′-refl {n}) (sdesc Xs Ys c))
        (oracleR h (≤′-refl {n}) (ConRb-≤ d (isNoneR m) cb)
          (sdesc Xs Ys c) wf)
        (SealNewR.sealNewR d le_s (≤′-refl {n}) (≤′⇒≤ le_s) e₁ Xs Ys c
          {Φ = Φ} {δt = δs} {T = T₁} zero up)

      clause : ℰ d s p w₁ δtβ (Wl ⦂∀ BsL [ Tl ])
        (⇑ᵗᵐ Wr ⦂∀ (bind Tr ▷ᵇ replaceTy (suc α′) (⇑ᵗ R′) BsR) [ ＇ zero ])
      clause =
        ℰᵍ-≡
          (cong₃′ (renameᵗᵐ-id Wl)
            (substᵗ-cong A (exts-cong (λ Z →
              trans (renameTy-id (δl δt Z)) (sym (tyL h Z)))))
            (trans (repL-rename ρL₁ ρR₁ Xs c) (renameTy-id Tl)))
          (cong₂ (λ M C → M ⦂∀ C [ ＇ zero ]) (shift-term Tr Wr)
            (trans (annot Tr (δr δt) B)
              (cong (renameᵗ (extᵗ suc)) (sym tgtR))))
          (ℰᵍ-map d s w₁
            (λ le′ w″ e″ V V′ → 𝒱≤-cast d (≤′-trans le′ le_s) le′ p w″)
            (r e₁ le_s c″ (WFDesc-rename ρL₁ ρR₁ c wf)))

      K₁ : ∀ {w₂} (e₂ : w₂ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₂ (δtβ ↑ᴵ e₂) Ql Qr
        → ℰ d k p w₂ (δsβ ↑ᴵ e₂) Ql
            (mplug (renameMFrame (ρR e₂) (just (conceal cR))) Qr)
      K₁ e₂ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡ refl
          (trans (ccRenR e₂ m₁ δsβ δtβ Qr B)
            (↓-pk (pk-ren↓ (toRenameᵗ (ρR e₂))
              (pk-mc α₁≡ R₁≡ (open0 Tr (δr δs) B)))))
          (con (RConvI-↑ e₂ hα)
            (subst (λ b → ConRb d b k _)
              (sym (trans (isNoneR-↑ (ρR e₂) m₁)
                (trans (isNoneR-pair m₀) (isNoneR-↑ ρR₁ m))))
              (ConRb-down d (isNoneR m) (≤-trans k≤s (≤′⇒≤ le_s)) cb))
            ql qr q)

      K₂ : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
        → Value Ql → Value Qr → 𝒱 d k p w₃ (δsβ ↑ᴵ e₃) Ql Qr
        → ℰ d k p w₃ (δsg ↑ᴵ e₃) Ql
            (mplug (renameMFrame (ρR e₃)
              (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BsR 〗))) Qr)
      K₂ e₃ {k} k≤s {Ql} {Qr} ql qr q =
        ℰᵍ-≡ refl
          (trans (rcRenR e₃ (r-pair {Φ = pair Φ} {X = zero} ↔-here zero)
                    δsβ δsg Qr B)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρR e₃))
              (pk-〖〗 refl (shift-ty Tr Tr) (open0 Tr (δr δs) B)))))
          (rev (RConvI-↑ e₃ hβ) k≤s ql qr q)

  -- the clauses of converted values
  revV : ∀ {n} w {X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → allPair d n p w δs Vl Vr
    → allPair d n p w δt Vl
        (revM (rcR m (δr δt)) (substᵗ (δr δs) (`∀ B)) Vr)
  revV {n} w {m = m} {δs} {δt} h le {Vl} {Vr} vl vr r =
    allPair-from d n p w {δ = δt} λ e {n′} le′ (sdesc Xs Ys c) wf →
      ℰᵍ-≡ refl (inst≡ (sym (revVR e m δs δt Vr (`∀ B))))
        (pairRevR {n′} _ (RConvI-↑ e h) (≤-trans le′ le)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (renameᵗᵐ-preserves-Value (ρR e) vr)
          (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c wf)

  conV : ∀ {n} w {X} {m : RMode Φ X (ΔR w)} {δs δt}
      (h : RConvI d N w m δs δt) → ConRm d m n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → allPair d n p w δt Wl Wr
    → allPair d n p w δs Wl
        (conM (rcR m (δr δt)) (substᵗ (δr δs) (`∀ B)) Wr)
  conV {n} w {m = m} {δs} {δt} h cb {Wl} {Wr} wl wr r =
    allPair-from d n p w {δ = δs} λ e {n′} le′ (sdesc Xs Ys c) wf →
      ℰᵍ-≡ refl (inst≡ (sym (conVR e m δs δt Wr (`∀ B))))
        (pairConR {n′} _ (RConvI-↑ e h) (ConRm-↑ d (ρR e) m le′ cb)
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (renameᵗᵐ-preserves-Value (ρR e) wr)
          (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c wf)

------------------------------------------------------------------------
-- The lemma
------------------------------------------------------------------------

mutual
  revR : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p : Φ ⊢ A ⊑ B) → RevR d p
  revR d ★⊑★ = revR★ d ★⊑★
  revR d ι⊑ι = revRι d
  revR d (X⊑Y z) = rev-varR d z
  revR d (⇒⊑⇒ p q) {N} {w} {m = m} {δt = δt} h {k} le vl vr r =
    ℰ-value d k (⇒⊑⇒ p q) w vl (revM-fun (rcR m (δr δt)) vr)
      (to (𝒱-⇒ d k p q w) (fun-rev h le vl vr (from (𝒱-⇒ d k p q w) r)))
    where
    open FunConvR d N p q (λ h′ → revR d p h′) (λ h′ → conR d p h′)
      (λ h′ → revR d q h′) (λ h′ → conR d q h′)
  revR d (∀⊑∀ p) {N} {w} {m = m} {δt = δt} h {k} le vl vr r =
    ℰ-value d k (∀⊑∀ p) w vl (revM-all (rcR m (δr δt)) vr)
      (to (𝒱-∀ d k p w)
        (PairR.revV d N p (λ h′ → revR d p h′) (λ h′ → conR d p h′)
          w h le vl vr (from (𝒱-∀ d k p w) r)))
  revR d (⇒⊑★ p q) = revR★ d (⇒⊑★ p q)
  revR d ι⊑★ = revR★ d ι⊑★
  revR d (X⊑★ z) = revR★ d (X⊑★ z)
  revR d (∀⊑ {B = ★} Anv z p) = revR★ d (∀⊑ Anv z p)
  revR d (∀⊑ {B = ＇ Y} Anv z p) h le vl vr r = ⊥-elim (nv⊑var p Anv)
  revR d (∀⊑ {B = ‵ ι} Anv z p) h le vl vr r = ⊥-elim (⊑ι-closed p z)
  revR d (∀⊑ {B = B₁ ⇒ B₂} Anv z p) {N} {w} {m = m} {δt = δt} h {k}
      le vl vr r =
    ℰ-value d k (∀⊑ Anv z p) w vl (revM-fun (rcR m (δr δt)) vr)
      (to (𝒱-∀⊑⇒ d k Anv z p w)
        (OnlyVR.revV d N p (λ h′ → revR d p h′) (λ h′ → conR d p h′)
          w h le vl vr (from (𝒱-∀⊑⇒ d k Anv z p w) r)))
  revR d (∀⊑ {B = `∀ B₁} Anv z p) {N} {w} {m = m} {δt = δt} h {k}
      le vl vr r =
    ℰ-value d k (∀⊑ Anv z p) w vl (revM-all (rcR m (δr δt)) vr)
      (to (𝒱-∀⊑∀ d k Anv z p w)
        (OnlyVR.revV d N p (λ h′ → revR d p h′) (λ h′ → conR d p h′)
          w h le vl vr (from (𝒱-∀⊑∀ d k Anv z p w) r)))
  revR d ∀★⊑★ = revR★ d ∀★⊑★
  revR d (∀⊑★ ns p) = revR★ d (∀⊑★ ns p)
  revR d bot-elim h {k} le vl vr r = ⊥-elim (𝒱-bot d k _ r)
  revR d bot⊑★ = revR★ d bot⊑★

  conR : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p : Φ ⊢ A ⊑ B) → ConR d p
  conR d ★⊑★ = conR★ d ★⊑★
  conR d ι⊑ι = conRι d
  conR d (X⊑Y z) = con-varR d z
  conR d (⇒⊑⇒ p q) {N} {w} {m = m} {δt = δt} h {k} cb wl wr r =
    ℰ-value d k (⇒⊑⇒ p q) w wl (conM-fun (rcR m (δr δt)) wr)
      (to (𝒱-⇒ d k p q w) (fun-con h cb wl wr (from (𝒱-⇒ d k p q w) r)))
    where
    open FunConvR d N p q (λ h′ → revR d p h′) (λ h′ → conR d p h′)
      (λ h′ → revR d q h′) (λ h′ → conR d q h′)
  conR d (∀⊑∀ p) {N} {w} {m = m} {δt = δt} h {k} cb wl wr r =
    ℰ-value d k (∀⊑∀ p) w wl (conM-all (rcR m (δr δt)) wr)
      (to (𝒱-∀ d k p w)
        (PairR.conV d N p (λ h′ → revR d p h′) (λ h′ → conR d p h′)
          w h cb wl wr (from (𝒱-∀ d k p w) r)))
  conR d (⇒⊑★ p q) = conR★ d (⇒⊑★ p q)
  conR d ι⊑★ = conR★ d ι⊑★
  conR d (X⊑★ z) = conR★ d (X⊑★ z)
  conR d (∀⊑ {B = ★} Anv z p) = conR★ d (∀⊑ Anv z p)
  conR d (∀⊑ {B = ＇ Y} Anv z p) h cb wl wr r = ⊥-elim (nv⊑var p Anv)
  conR d (∀⊑ {B = ‵ ι} Anv z p) h cb wl wr r = ⊥-elim (⊑ι-closed p z)
  conR d (∀⊑ {B = B₁ ⇒ B₂} Anv z p) {N} {w} {m = m} {δt = δt} h {k}
      cb wl wr r =
    ℰ-value d k (∀⊑ Anv z p) w wl (conM-fun (rcR m (δr δt)) wr)
      (to (𝒱-∀⊑⇒ d k Anv z p w)
        (OnlyVR.conV d N p (λ h′ → revR d p h′) (λ h′ → conR d p h′)
          w h cb wl wr (from (𝒱-∀⊑⇒ d k Anv z p w) r)))
  conR d (∀⊑ {B = `∀ B₁} Anv z p) {N} {w} {m = m} {δt = δt} h {k}
      cb wl wr r =
    ℰ-value d k (∀⊑ Anv z p) w wl (conM-all (rcR m (δr δt)) wr)
      (to (𝒱-∀⊑∀ d k Anv z p w)
        (OnlyVR.conV d N p (λ h′ → revR d p h′) (λ h′ → conR d p h′)
          w h cb wl wr (from (𝒱-∀⊑∀ d k Anv z p w) r)))
  conR d ∀★⊑★ = conR★ d ∀★⊑★
  conR d (∀⊑★ ns p) = conR★ d (∀⊑★ ns p)
  conR d bot-elim h {k} cb wl wr r = ⊥-elim (𝒱-bot d k _ r)
  conR d bot⊑★ = conR★ d bot⊑★
