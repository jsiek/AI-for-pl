module LR.Relation where

-- File Charter:
--   * The step-indexed Kripke logical relation for the dynamic gradual
--     guarantee (notes/logrel-dgg.md, Sections 6 and 6.11), in two
--     directions: `≺` counts the left program's steps, `≻` the right
--     program's.
--   * `𝒱 d n p w δ Vl Vr`: the value relation at stage n, indexed by a
--     two-context precision derivation p, in world w, under an
--     interpretation δ of p's type variables.  `ℰ d n p w δ Ml Mr` is
--     its expression closure.
--   * An interpretation gives each left variable a left type and a
--     leaf: either a syntactic entry (`LR.Desc`, a store-variable
--     leaf, read on demand) or a semantic relation (a type
--     application's bound variable after its reveal, built by the `∀`
--     clause from a descriptor and defined only below the clause's
--     stage).
--   * Well-foundedness:
--       - the value relation recurses on p at one stage;
--       - every leaf entry has a left seal, so it is read one stage down
--         (`≺`, or `≻` with a right seal), or by the guarded relation
--         `G` at the same stage after peeling a seal (`≻`, left-only);
--       - `G` reads the same stage only through tags and entries, each
--         of which peels the left term, and every other call drops the
--         stage;
--       - the semantic leaves and the stage-bounded helpers recurse on
--         `≤′` proofs.
--   * The guard convention for `≻` (Section 6.6): a relation whose
--     right type is `★` is `G`, whose stage-n content reads stage n − 1
--     (or the same stage on a smaller left term).

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤′_; ≤′-refl; ≤′-step;
  _<_; _≤_; _<?_; _≤?_)
open import Data.Nat.Properties using (≤⇒≤′)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using (_⊢_∼_; _!; _↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import Conversion using (Conv↓; seal; _↦↓_; `∀↓_; id↓)
open import CastTerms using (Term; $; _·_; _⦂∀_[_]; _⟨_⟩; _↓_; blame;
  Value; renameᵗᵐ)
open import Primitives using (Const)
open import Reduction using (StoreChanges; _—↠[_]_)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Steps

------------------------------------------------------------------------
-- Directions and interpretations
------------------------------------------------------------------------

-- which program's steps are counted
data Dir : Set where
  ≺ ≻ : Dir

data Leaf (ΔL ΔR : TyCtx) : Set₁ where
  syn : Entry ΔL ΔR → Leaf ΔL ΔR
  sem : RelΩ ΔL ΔR → Leaf ΔL ΔR

record Interp (Δ Δ′ ΔL ΔR : TyCtx) : Set₁ where
  constructor interp
  field
    δl : Δ ⇒ˢ ΔL
    δr : Δ′ ⇒ˢ ΔR
    leaf : TyVar Δ → Leaf ΔL ΔR

open Interp public

infixr 5 _•ˢ_ _•ˡ_

_•ˢ_ : ∀ {Δ Δ′} → Ty Δ′ → Δ ⇒ˢ Δ′ → suc Δ ⇒ˢ Δ′
(T •ˢ σ) Fin.zero = T
(T •ˢ σ) (Fin.suc X) = σ X

_•ˡ_ : ∀ {Δ ΔL ΔR}
  → Leaf ΔL ΔR → (TyVar Δ → Leaf ΔL ΔR) → TyVar (suc Δ) → Leaf ΔL ΔR
(l •ˡ ls) Fin.zero = l
(l •ˡ ls) (Fin.suc X) = ls X

transportLeaf : ∀ {ΔL ΔR ΔL′ ΔR′}
  → ΔL ↪ᵗ ΔL′ → ΔR ↪ᵗ ΔR′ → Leaf ΔL ΔR → Leaf ΔL′ ΔR′
transportLeaf σL σR (syn e) = syn (renameEntry σL σR e)
transportLeaf σL σR (sem R) = sem (transportΩ σL σR R)

transportI : ∀ {Δ Δ′ ΔL ΔR ΔL′ ΔR′}
  → ΔL ↪ᵗ ΔL′ → ΔR ↪ᵗ ΔR′ → Interp Δ Δ′ ΔL ΔR → Interp Δ Δ′ ΔL′ ΔR′
transportI σL σR (interp δl δr leaf) =
  interp (λ X → renameᵗ (toRenameᵗ σL) (δl X))
    (λ Y → renameᵗ (toRenameᵗ σR) (δr Y))
    (λ X → transportLeaf σL σR (leaf X))

-- along an extension
_↑ᴵ_ : ∀ {Δ Δ′} {w w′ : World}
  → Interp Δ Δ′ (ΔL w) (ΔR w) → w′ ⊒ w → Interp Δ Δ′ (ΔL w′) (ΔR w′)
δ ↑ᴵ e = transportI (ρL e) (ρR e) δ

extPairI : ∀ {Δ Δ′ ΔL ΔR} → Ty ΔL → Ty ΔR → Leaf ΔL ΔR
  → Interp Δ Δ′ ΔL ΔR → Interp (suc Δ) (suc Δ′) ΔL ΔR
extPairI T T′ l (interp δl δr leaf) =
  interp (T •ˢ δl) (T′ •ˢ δr) (l •ˡ leaf)

extOnlyI : ∀ {Δ Δ′ ΔL ΔR} → Ty ΔL → Leaf ΔL ΔR
  → Interp Δ Δ′ ΔL ΔR → Interp (suc Δ) Δ′ ΔL ΔR
extOnlyI T l (interp δl δr leaf) = interp (T •ˢ δl) δr (l •ˡ leaf)

-- a dead variable occurs nowhere, so its leaf is never read
extDeadI : ∀ {Δ Δ′ ΔL ΔR} → Ty ΔL
  → Interp Δ Δ′ ΔL ΔR → Interp (suc Δ) Δ′ ΔL ΔR
extDeadI T δ = extOnlyI T (sem ⊤Ω) δ

-- the interpretation of a descriptor's own variables
envI : ∀ {Δ Δ′ ΔL ΔR}
  → Vec (Entry ΔL ΔR) Δ → Vec (Ty ΔR) Δ′ → Interp Δ Δ′ ΔL ΔR
envI env envR =
  interp (λ X → entryTy (lookup env X)) (lookup envR) (λ X → syn (lookup env X))

-- the empty interpretation, for closed precision derivations
closedI : ∀ {ΔL ΔR} → Interp zero zero ΔL ΔR
closedI = interp (λ ()) (λ ()) (λ ())

------------------------------------------------------------------------
-- Shapes of values
------------------------------------------------------------------------

-- the conversion seals with X, at the representation type R
IsSeal : ∀ {Δ A B} → TyVar Δ → Ty Δ → Conv↓ Δ A B → Set
IsSeal X R (seal X′ R′) = X′ ≡ X × R′ ≡ R
IsSeal X R (c ↦↓ d) = ⊥
IsSeal X R (`∀↓ c) = ⊥
IsSeal X R (id↓ A) = ⊥

-- the cast injects at a given ground
IsInjVar : ∀ {Δ} {μ} {A B : Ty Δ} → TyVar Δ → μ ⊢ A ∼ B → Set
IsInjVar X (_! ⦃ Gᵍ = ＇ Y ⦄ c) = Y ≡ X
IsInjVar X c = ⊥

IsInjBase : ∀ {Δ} {μ} {A B : Ty Δ} → Base → μ ⊢ A ∼ B → Set
IsInjBase ι (_! ⦃ Gᵍ = ‵ ι′ ⦄ c) = ι′ ≡ ι
IsInjBase ι c = ⊥

IsInj⇒ : ∀ {Δ} {μ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set
IsInj⇒ (_! ⦃ Gᵍ = ★⇒★ ⦄ c) = ⊤
IsInj⇒ c = ⊥

IsInj∀ : ∀ {Δ} {μ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set
IsInj∀ (_! ⦃ Gᵍ = ∀★ ⦄ c) = ⊤
IsInj∀ c = ⊥

-- a constant against its injection at a base type
baseInj : ∀ {ΔL ΔR} → Base → Term ΔL → Term ΔR → Set
baseInj ι ($ κ) (W ⟨ c ⟩) = IsInjBase ι c × W ≡ $ κ
baseInj ι Vl Vr = ⊥

------------------------------------------------------------------------
-- Peeling a list of seals around a semantic relation
------------------------------------------------------------------------

peelSL : ∀ {ΘL ΘR} → List (TyVar ΘL) → Desc ΘL ΘR
  → (Term ΘL → Term ΘR → Set) → Term ΘL → Term ΘR → Set
peelSL [] c P V V′ = P V V′
peelSL (X ∷ Xs) c P (V ↓ s) V′ = IsSeal X (repL Xs c) s × peelSL Xs c P V V′
peelSL (X ∷ Xs) c P V V′ = ⊥

peelSR : ∀ {ΘL ΘR} → List (TyVar ΘR) → Desc ΘL ΘR
  → (Term ΘL → Term ΘR → Set) → Term ΘL → Term ΘR → Set
peelSR [] c P V V′ = P V V′
peelSR (Y ∷ Ys) c P V (V′ ↓ s) = IsSeal Y (repR Ys c) s × peelSR Ys c P V V′
peelSR (Y ∷ Ys) c P V V′ = ⊥

------------------------------------------------------------------------
-- The generic expression closure
------------------------------------------------------------------------

-- a value relation at the futures of w, at every stage up to n
VRel : ℕ → World → Set₁
VRel n w = ∀ {n′} → n′ ≤′ n → (w′ : World) → w′ ⊒ w
  → Term (ΔL w′) → Term (ΔR w′) → Set

-- the world after two reductions, with chosen tags for the new left
-- store variables
Arrive : ∀ {ΔL′ ΔR′} (n n′ : ℕ) (w : World)
  → StoreChanges (ΔL w) ΔL′ → StoreChanges (ΔR w) ΔR′
  → VRel n w → n′ ≤′ n → Term ΔL′ → Term ΔR′ → Set
Arrive {ΔL′} {ΔR′} n n′ w χsL χsR VR le Vl Vr =
  Σ[ tags ∈ (TyVar ΔL′ → Tag ΔL′ ΔR′) ]
  Σ[ ok ∈ (∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
                   ≡ renameTag (embedᶜˢ χsL) (embedᶜˢ χsR) (tag w X)) ]
    VR le (world ΔL′ ΔR′ tags) (ext (embedᶜˢ χsL) (embedᶜˢ χsR) ok) Vl Vr

ℰᵍ : Dir → (n : ℕ) (w : World) → VRel n w
  → Term (ΔL w) → Term (ΔR w) → Set
-- the left runs out, blames within the steps, or reaches a value in k
-- steps while the right reaches a related value
ℰᵍ ≺ n w VR Ml Mr =
  Runs Ml n
  ⊎ (Σ[ k ∈ ℕ ] Σ[ Δ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges (ΔL w) Δ′ ]
       (k < n × (Ml —→^ k [ χs ] blame)))
  ⊎ (Σ[ k ∈ ℕ ] Σ[ n′ ∈ ℕ ] Σ[ le ∈ n′ ≤′ n ]
     Σ[ ΔL′ ∈ TyCtx ] Σ[ χsL ∈ StoreChanges (ΔL w) ΔL′ ] Σ[ Vl ∈ Term ΔL′ ]
     Σ[ ΔR′ ∈ TyCtx ] Σ[ χsR ∈ StoreChanges (ΔR w) ΔR′ ] Σ[ Vr ∈ Term ΔR′ ]
       (k + n′ ≡ n × (Ml —→^ k [ χsL ] Vl) × (Mr —↠[ χsR ] Vr)
        × Value Vl × Value Vr × Arrive n n′ w χsL χsR VR le Vl Vr))
-- the right runs out, the left blames, or the right reaches a value in k
-- steps while the left reaches a related value
ℰᵍ ≻ n w VR Ml Mr =
  Runs Mr n
  ⊎ (Σ[ Δ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges (ΔL w) Δ′ ]
       (Ml —↠[ χs ] blame))
  ⊎ (Σ[ k ∈ ℕ ] Σ[ n′ ∈ ℕ ] Σ[ le ∈ n′ ≤′ n ]
     Σ[ ΔL′ ∈ TyCtx ] Σ[ χsL ∈ StoreChanges (ΔL w) ΔL′ ] Σ[ Vl ∈ Term ΔL′ ]
     Σ[ ΔR′ ∈ TyCtx ] Σ[ χsR ∈ StoreChanges (ΔR w) ΔR′ ] Σ[ Vr ∈ Term ΔR′ ]
       (k + n′ ≡ n × (Ml —↠[ χsL ] Vl) × (Mr —→^ k [ χsR ] Vr)
        × Value Vl × Value Vr × Arrive n n′ w χsL χsR VR le Vl Vr))

------------------------------------------------------------------------
-- Stage arithmetic
------------------------------------------------------------------------

≤′-trans : ∀ {a b c} → a ≤′ b → b ≤′ c → a ≤′ c
≤′-trans ab ≤′-refl = ab
≤′-trans ab (≤′-step bc) = ≤′-step (≤′-trans ab bc)

------------------------------------------------------------------------
-- The value relation
------------------------------------------------------------------------

-- how an entry's contents are read: one stage down, or by `G` at the
-- same stage (`≻`, no right seal)
data Mode : Set where
  later guarded : Mode

modeOf : ∀ {ΔR} → Dir → List (TyVar ΔR) → Mode
modeOf ≻ [] = guarded
modeOf ≻ (Y ∷ Ys) = later
modeOf ≺ Ys = later

mutual
  𝒱 : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
    → Φ ⊢ A ⊑ A′ → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  𝒱 ≺ n ★⊑★ w δ Vl Vr = star ≺ n w Vl Vr
  𝒱 ≻ n p@★⊑★ w δ Vl Vr = G n p w δ Vl Vr
  𝒱 d n ι⊑ι w δ Vl Vr = Σ[ κ ∈ Const ] (Vl ≡ $ κ × Vr ≡ $ κ)
  𝒱 d n (X⊑Y {X = X} x) w δ Vl Vr = leafRel d n w (leaf δ X) Vl Vr
  𝒱 d n (⇒⊑⇒ p q) w δ Vl Vr = funRel d n p q w δ Vl Vr
  𝒱 d n (∀⊑∀ p) w δ Vl Vr = allPair d n p w δ Vl Vr
  𝒱 ≺ n (⇒⊑★ p q) w δ Vl Vr = funStar ≺ n p q w δ Vl Vr
  𝒱 ≻ n r@(⇒⊑★ p q) w δ Vl Vr = G n r w δ Vl Vr
  𝒱 ≺ n (ι⊑★ {ι = ι}) w δ Vl Vr = baseInj ι Vl Vr
  𝒱 ≻ n p@ι⊑★ w δ Vl Vr = G n p w δ Vl Vr
  𝒱 d n (X⊑★ {X = X} x) w δ Vl Vr = leafRel d n w (leaf δ X) Vl Vr
  𝒱 ≺ n (∀⊑ Anv z p) w δ Vl Vr = allOnly ≺ n p w δ Vl Vr
  𝒱 ≻ n {A′ = ★} r@(∀⊑ Anv z p) w δ Vl Vr = G n r w δ Vl Vr
  𝒱 ≻ n (∀⊑ Anv z p) w δ Vl Vr = allOnly ≻ n p w δ Vl Vr
  𝒱 ≺ n ∀★⊑★ w δ Vl Vr = allStar ≺ n w Vl Vr
  𝒱 ≻ n p@∀★⊑★ w δ Vl Vr = G n p w δ Vl Vr
  𝒱 ≺ n (∀⊑★ ns p) w δ Vl Vr = allDeadStar ≺ n p w δ Vl Vr
  𝒱 ≻ n r@(∀⊑★ ns p) w δ Vl Vr = G n r w δ Vl Vr
  𝒱 d n bot-elim w δ Vl Vr = ⊥
  𝒱 d n bot⊑★ w δ Vl Vr = ⊥

  -- the value relation at a lower stage
  𝒱≤ : Dir → ∀ {n′ n} → n′ ≤′ n → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
    → Φ ⊢ A ⊑ A′ → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  𝒱≤ d {n′} ≤′-refl p = 𝒱 d n′ p
  𝒱≤ d (≤′-step le) p = 𝒱≤ d le p

  -- the value relation strictly below n
  𝒱< : Dir → ∀ {m n} → suc m ≤′ n → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
    → Φ ⊢ A ⊑ A′ → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  𝒱< d {m} ≤′-refl p = 𝒱 d m p
  𝒱< d (≤′-step lt) p = 𝒱< d lt p

  -- `≻` at a precision whose right type is `★`: nothing at stage 0, and
  -- otherwise the content read from stage n − 1, or from stage n on a
  -- smaller left term
  G : ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
    → Φ ⊢ A ⊑ A′ → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  G zero p w δ Vl Vr = ⊤
  G (suc k) ★⊑★ w δ Vl Vr = star ≻ (suc k) w Vl Vr
  G (suc k) (ι⊑★ {ι = ι}) w δ Vl Vr = baseInj ι Vl Vr
  G (suc k) (⇒⊑★ p q) w δ Vl Vr = funStar ≻ k p q w δ Vl Vr
  G (suc k) (X⊑★ {X = X} x) w δ Vl Vr = leafRel ≻ (suc k) w (leaf δ X) Vl Vr
  G (suc k) {A′ = ★} (∀⊑ Anv z p) w δ Vl Vr = allOnly ≻ k p w δ Vl Vr
  G (suc k) ∀★⊑★ w δ Vl Vr = allStar ≻ k w Vl Vr
  G (suc k) (∀⊑★ ns p) w δ Vl Vr = allDeadStar ≻ k p w δ Vl Vr
  G (suc k) bot⊑★ w δ Vl Vr = ⊥
  G (suc k) p w δ Vl Vr = 𝒱 ≻ k p w δ Vl Vr

  G≤ : ∀ {m n} → m ≤′ n → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
    → Φ ⊢ A ⊑ A′ → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  G≤ {m} ≤′-refl p = G m p
  G≤ (≤′-step le) p = G≤ le p

  -- a leaf: a syntactic entry, or a semantic relation
  leafRel : Dir → ℕ → (w : World) → Leaf (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  leafRel d n w (syn e) Vl Vr = entry d n w e Vl Vr
  leafRel d n w (sem R) Vl Vr = R n w id↪ᵗ id↪ᵗ Vl Vr

  -- an entry: peel the seals, then read the contents
  entry : Dir → ℕ → (w : World) → Entry (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  entry d n w (seals X Xs Ys c) (V ↓ s) Vr =
    IsSeal X (repL Xs c) s × peelL d n w (modeOf d Ys) Xs Ys c V Vr
  entry d n w (seals X Xs Ys c) Vl Vr = ⊥

  peelL : Dir → ℕ → (w : World) → Mode → List (TyVar (ΔL w))
    → List (TyVar (ΔR w)) → Desc (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  peelL d n w g [] Ys c V Vr = peelR d n w g Ys c V Vr
  peelL d n w g (X ∷ Xs) Ys c (V ↓ s) Vr =
    IsSeal X (repL Xs c) s × peelL d n w g Xs Ys c V Vr
  peelL d n w g (X ∷ Xs) Ys c V Vr = ⊥

  peelR : Dir → ℕ → (w : World) → Mode
    → List (TyVar (ΔR w)) → Desc (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  peelR d n w g [] c V V′ = contents d n w g c V V′
  peelR d n w g (Y ∷ Ys) c V (V′ ↓ s) =
    IsSeal Y (repR Ys c) s × peelR d n w g Ys c V V′
  peelR d n w g (Y ∷ Ys) c V V′ = ⊥

  contents : Dir → ℕ → (w : World) → Mode → Desc (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  contents d zero w later c V V′ = ⊤
  contents d (suc k) w later (desc p env envR) V V′ =
    𝒱 d k p w (envI env envR) V V′
  contents d n w guarded (desc p env envR) V V′ =
    G n p w (envI env envR) V V′

  -- `★`: both are injections, compared by the left ground
  star : Dir → ℕ → (w : World) → Term (ΔL w) → Term (ΔR w) → Set
  star d n w (W ⟨ _! ⦃ Gᵍ = g ⦄ c ⟩) Vr = starGround d n w g W Vr
  star d n w Vl Vr = ⊥

  starGround : Dir → ℕ → (w : World) → ∀ {G} → Ground G
    → Term (ΔL w) → Term (ΔR w) → Set
  starGround d n w (＇ X) W Vr = tagRel d n w (tag w X) W Vr
  starGround d n w (‵ ι) W Vr = baseInj ι W Vr
  starGround d zero w ★⇒★ W Vr = ⊤
  starGround d (suc k) w ★⇒★ W Vr = starFun d k w W Vr
  starGround d zero w ∀★ W Vr = ⊤
  starGround d (suc k) w ∀★ W Vr = starAll d k w W Vr

  tagRel : Dir → ℕ → (w : World) → Tag (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  tagRel d n w (just Y , e) W (Wr ⟨ c ⟩) = IsInjVar Y c × entry d n w e W Wr
  tagRel d n w (just Y , e) W Vr = ⊥
  tagRel d n w (nothing , e) W Vr = entry d n w e W Vr

  starFun : Dir → ℕ → (w : World) → Term (ΔL w) → Term (ΔR w) → Set
  starFun d k w W (Wr ⟨ c ⟩) =
    IsInj⇒ c × 𝒱 d k (⇒⊑⇒ {Φ = []} ★⊑★ ★⊑★) w closedI W Wr
  starFun d k w W Vr = ⊥

  starAll : Dir → ℕ → (w : World) → Term (ΔL w) → Term (ΔR w) → Set
  starAll d k w W (Wr ⟨ c ⟩) =
    IsInj∀ c × 𝒱 d k (∀⊑∀ {Φ = []} ★⊑★) w closedI W Wr
  starAll d k w W Vr = ⊥

  -- functions: related argument values in any future give related
  -- results
  funRel : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′ B B′}
    → Φ ⊢ A ⊑ A′ → Φ ⊢ B ⊑ B′ → (w : World)
    → Interp Δ Δ′ (ΔL w) (ΔR w) → Term (ΔL w) → Term (ΔR w) → Set
  funRel d n p q w δ Vl Vr =
    ∀ {w′} (e : w′ ⊒ w) {n′} (le : n′ ≤′ n) Wl Wr → Value Wl → Value Wr
    → 𝒱≤ d le p w′ (δ ↑ᴵ e) Wl Wr
    → ℰᵍ d n′ w′
        (λ le′ w″ e′ → 𝒱≤ d (≤′-trans le′ le) q w″ ((δ ↑ᴵ e) ↑ᴵ e′))
        (renameᵗᵐ (ρL e) Vl · Wl) (renameᵗᵐ (ρR e) Vr · Wr)

  funStar : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    → Φ ⊢ A ⊑ ★ → Φ ⊢ B ⊑ ★ → (w : World)
    → Interp Δ Δ′ (ΔL w) (ΔR w) → Term (ΔL w) → Term (ΔR w) → Set
  funStar d n p q w δ Vl (Wr ⟨ c ⟩) = IsInj⇒ c × funRel d n p q w δ Vl Wr
  funStar d n p q w δ Vl Vr = ⊥

  -- a semantic leaf from a descriptor, defined below the stage n′ ≤ n
  leafBelow : Dir → ∀ {n′ n} → n′ ≤′ n → ∀ {ΔL ΔR}
    → Desc ΔL ΔR → RelΩ ΔL ΔR
  leafBelow d {n′} le c m w τL τR V V′ with suc m ≤? n′
  ... | yes lt =
    descBelow d (≤′-trans (≤⇒≤′ lt) le) w (renameDesc τL τR c) V V′
  ... | no _ = ⊥

  descBelow : Dir → ∀ {m n} → suc m ≤′ n → (w : World)
    → Desc (ΔL w) (ΔR w) → Term (ΔL w) → Term (ΔR w) → Set
  descBelow d lt w (desc p env envR) V V′ = 𝒱< d lt p w (envI env envR) V V′

  -- `≻`, left-only: the leaf is `G` itself, at stages up to n′ ≤ n
  leafG : ∀ {n′ n} → n′ ≤′ n → ∀ {ΔL ΔR} → Desc ΔL ΔR → RelΩ ΔL ΔR
  leafG {n′} le c m w τL τR V V′ with m ≤? n′
  ... | yes le′ = descG (≤′-trans (≤⇒≤′ le′) le) w (renameDesc τL τR c) V V′
  ... | no _ = ⊥

  descG : ∀ {m n} → m ≤′ n → (w : World)
    → Desc (ΔL w) (ΔR w) → Term (ΔL w) → Term (ΔR w) → Set
  descG le w (desc p env envR) V V′ = G≤ le p w (envI env envR) V V′

  -- the leaf for a left-only variable
  onlyLeaf : Dir → ∀ {n′ n} → n′ ≤′ n → ∀ {ΔL ΔR}
    → Desc ΔL ΔR → RelΩ ΔL ΔR
  onlyLeaf ≺ le c = leafBelow ≺ le c
  onlyLeaf ≻ le c = leafG le c

  -- a sealed descriptor's leaf: peel the seals, then read the
  -- descriptor below n′ at the same stage
  leafBelowS : Dir → ∀ {n′ n} → n′ ≤′ n → ∀ {ΔL ΔR}
    → SDesc ΔL ΔR → RelΩ ΔL ΔR
  leafBelowS d le (sdesc Xs Ys c) m w τL τR =
    peelSL (map (renameVar τL) Xs) (renameDesc τL τR c)
      (peelSR (map (renameVar τR) Ys) (renameDesc τL τR c)
        (leafBelow d le c m w τL τR))

  -- both instantiate, at any sealed descriptor
  allPair : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    → pair Φ ⊢ A ⊑ B → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  allPair d n {A = A} {B = B} p w δ Vl Vr =
    ∀ {w′} (e : w′ ⊒ w) {n′} (le : n′ ≤′ n) (c : SDesc (ΔL w′) (ΔR w′))
    → ℰᵍ d n′ w′
        (λ le′ w″ e′ → 𝒱≤ d (≤′-trans le′ le) p w″
          (extPairI (leftTyS c) (rightTyS c) (sem (leafBelowS d le c))
            (δ ↑ᴵ e) ↑ᴵ e′))
        (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A [ leftTyS c ])
        (renameᵗᵐ (ρR e) Vr ⦂∀ substᵗ (extsᵗ (δr (δ ↑ᴵ e))) B
          [ rightTyS c ])

  -- a sealed descriptor's leaf for a left-only variable: peel the left
  -- seals, then the left-only leaf of the descriptor at the same stage
  onlyLeafS : Dir → ∀ {n′ n} → n′ ≤′ n → ∀ {ΔL ΔR}
    → SDesc ΔL ΔR → RelΩ ΔL ΔR
  onlyLeafS d le (sdesc Xs Ys c) m w τL τR =
    peelSL (map (renameVar τL) Xs) (renameDesc τL τR c)
      (onlyLeaf d le c m w τL τR)

  -- only the left instantiates
  allOnly : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    → only Φ ⊢ A ⊑ B → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  allOnly d n {A = A} p w δ Vl Vr =
    ∀ {w′} (e : w′ ⊒ w) {n′} (le : n′ ≤′ n) (c : SDesc (ΔL w′) (ΔR w′))
    → ℰᵍ d n′ w′
        (λ le′ w″ e′ → 𝒱≤ d (≤′-trans le′ le) p w″
          (extOnlyI (leftTyS c) (sem (onlyLeafS d le c)) (δ ↑ᴵ e) ↑ᴵ e′))
        (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A [ leftTyS c ])
        (renameᵗᵐ (ρR e) Vr)

  -- left `∀`, right `∀★` payload, with a dead variable
  allDead : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A}
    → dead Φ ⊢ A ⊑ ★ → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  allDead d n {A = A} p w δ Vl Wr =
    ∀ {w′} (e : w′ ⊒ w) {n′} (le : n′ ≤′ n)
      (T : Ty (ΔL w′)) (T′ : Ty (ΔR w′))
    → ℰᵍ d n′ w′
        (λ le′ w″ e′ → 𝒱≤ d (≤′-trans le′ le) p w″
          (extDeadI T (δ ↑ᴵ e) ↑ᴵ e′))
        (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A [ T ])
        (renameᵗᵐ (ρR e) Wr ⦂∀ ★ [ T′ ])

  allDeadStar : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A}
    → dead Φ ⊢ A ⊑ ★ → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
    → Term (ΔL w) → Term (ΔR w) → Set
  allDeadStar d n p w δ Vl (Wr ⟨ c ⟩) = IsInj∀ c × allDead d n p w δ Vl Wr
  allDeadStar d n p w δ Vl Vr = ⊥

  -- left `∀★` against the right's `∀★` payload: both instantiate, and
  -- the bodies are related at `★`
  allStar : Dir → ℕ → (w : World) → Term (ΔL w) → Term (ΔR w) → Set
  allStar d n w Vl (Wr ⟨ c ⟩) =
    IsInj∀ c
    × (∀ {w′} (e : w′ ⊒ w) {n′} (le : n′ ≤′ n)
         (T : Ty (ΔL w′)) (T′ : Ty (ΔR w′))
       → ℰᵍ d n′ w′
           (λ le′ w″ e′ → starAt d (≤′-trans le′ le) w″)
           (renameᵗᵐ (ρL e) Vl ⦂∀ ★ [ T ])
           (renameᵗᵐ (ρR e) Wr ⦂∀ ★ [ T′ ]))
  allStar d n w Vl Vr = ⊥

  -- `★` at a stage up to n
  starAt : Dir → ∀ {m n} → m ≤′ n → (w : World)
    → Term (ΔL w) → Term (ΔR w) → Set
  starAt ≺ {m} ≤′-refl w = star ≺ m w
  starAt ≻ {m} ≤′-refl w = G m (★⊑★ {Φ = []}) w closedI
  starAt d (≤′-step le) w = starAt d le w

------------------------------------------------------------------------
-- The expression relation
------------------------------------------------------------------------

ℰ : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
  → Φ ⊢ A ⊑ A′ → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
  → Term (ΔL w) → Term (ΔR w) → Set
ℰ d n p w δ = ℰᵍ d n w (λ le w′ e → 𝒱≤ d le p w′ (δ ↑ᴵ e))
