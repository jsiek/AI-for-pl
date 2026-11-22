module proof.LR.ConvLambda where

-- File Charter:
--   * The conversion lemma's instances for the fundamental lemma's `Λ`
--     cases (notes/logrel-dgg.md, Section 7).  A type application of
--     `Λ V` allocates a store variable (on both sides for `Λ⊑Λ`, on the
--     left for a left-only `Λ`) and reveals it: `V ↑ 〖 0 , ⇑ T ↑ A 〗`.
--     The fundamental lemma relates the bodies with the bound variable
--     a store variable, whose leaf is its store entry; the instances
--     (`lamPair`, `lamOnly`) turn that into the `∀` clause's relation,
--     where the bound variable has the clause's leaf.
--   * The store entry is the clause's leaf with the new seals in front,
--     read one stage up when its contents are read later (`entryP⇔`,
--     `entryO⇔`).  So the entry's seal hypotheses need no downward step
--     (`SealEntryP`, `SealEntryO`).
--   * The fundamental lemma's interpretations, whose types are store
--     variables, are closed under conversions (`FreshI-store`).

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; s≤s; z≤n;
  _≤′_; ≤′-refl)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤-trans; <⇒≤)
open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import proof.DGG.CenterRename using (_∘↪_)
open import Conversion
open import CastTerms using (Term; `_; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_;
  _⟨_⟩; _↑_; _↓_; blame; Value)
open import Reduction using (bind; []; _∷_)
open import LR.Steps using (embedᶜˢ)
open import LR.Frame using (reveal)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import proof.LR.WorldProps
open import proof.LR.InterpProps
open import proof.LR.Monotone
open import proof.LR.Expression
open import proof.LR.SubstLemma using (_⇔_; iff; to; from; leafBelow-⇔;
  leafG-⇔)
open import proof.LR.ConvSyntax
open import proof.LR.ConvBase
open import proof.LR.ConvLemma
open import proof.LR.ConvMain using (revC)
open import proof.LR.ConvClose using (oracle-all)

private
  variable
    Δ Δ′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- The fundamental lemma's interpretations
------------------------------------------------------------------------

-- every type is a store variable
record StoreI {Δ Δ′ ΘL ΘR} (δ : Interp Δ Δ′ ΘL ΘR) : Set where
  field
    varL : ∀ X → Σ[ γ ∈ TyVar ΘL ] δl δ X ≡ ＇ γ
    varR : ∀ Y → Σ[ γ′ ∈ TyVar ΘR ] δr δ Y ≡ ＇ γ′

open StoreI public

-- store-variable leaves are closed under later conversions
FreshI-store : ∀ {Φ : Corr Δ Δ′} d N rk {w}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → GoodI δ → StoreI δ → FreshI Φ d N rk w δ
fgood (FreshI-store d N rk g sv) = g
fP (FreshI-store d N rk {w} {δ} g sv) {Z} {Y′} z =
  subst₂ (FreshP d rk w (leaf δ Z))
    (sym (proj₂ (varL sv Z))) (sym (proj₂ (varR sv Y′)))
    (storeFreshP {d = d} {N = N} {w = w} (g Z) {γ = proj₁ (varL sv Z)}
      {γ′ = proj₁ (varR sv Y′)} {rk = rk})
fO (FreshI-store d N rk {w} {δ} g sv) {Z} z =
  subst (FreshO d w (leaf δ Z)) (sym (proj₂ (varL sv Z)))
    (storeFreshO {d = d} {w = w} (g Z) {γ = proj₁ (varL sv Z)})
forc (FreshI-store d N rk g sv) = oracle-all d N

------------------------------------------------------------------------
-- An entry is a sealed descriptor's leaf
------------------------------------------------------------------------

peelR⇔ : ∀ d n w g (Ys : List (TyVar (ΔR w))) (c : Desc (ΔL w) (ΔR w))
    {V V′}
  → peelR d n w g Ys c V V′ ⇔ peelSR Ys c (contents d n w g c) V V′
peelR⇔ d n w g [] c = iff (λ r → r) (λ r → r)
peelR⇔ d n w g (Y ∷ Ys) c {V′ = V′ ↓ s} =
  iff (λ (is , r) → is , to (peelR⇔ d n w g Ys c) r)
      (λ (is , r) → is , from (peelR⇔ d n w g Ys c) r)
peelR⇔ d n w g (Y ∷ Ys) c {V′ = ` x₀} = iff (λ ()) (λ ())
peelR⇔ d n w g (Y ∷ Ys) c {V′ = ƛ M₀} = iff (λ ()) (λ ())
peelR⇔ d n w g (Y ∷ Ys) c {V′ = L₀ · M₀} = iff (λ ()) (λ ())
peelR⇔ d n w g (Y ∷ Ys) c {V′ = Λ M₀} = iff (λ ()) (λ ())
peelR⇔ d n w g (Y ∷ Ys) c {V′ = L₀ ⦂∀ C₀ [ T₀ ]} = iff (λ ()) (λ ())
peelR⇔ d n w g (Y ∷ Ys) c {V′ = $ κ₀} = iff (λ ()) (λ ())
peelR⇔ d n w g (Y ∷ Ys) c {V′ = L₀ ⊕[ op₀ ] M₀} = iff (λ ()) (λ ())
peelR⇔ d n w g (Y ∷ Ys) c {V′ = W₀ ⟨ c₀ ⟩} = iff (λ ()) (λ ())
peelR⇔ d n w g (Y ∷ Ys) c {V′ = M₀ ↑ c₀} = iff (λ ()) (λ ())
peelR⇔ d n w g (Y ∷ Ys) c {V′ = blame} = iff (λ ()) (λ ())

peelL⇔ : ∀ d n w g (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
    (c : Desc (ΔL w) (ΔR w)) {V V′}
  → peelL d n w g Xs Ys c V V′
    ⇔ peelSL Xs c (peelSR Ys c (contents d n w g c)) V V′
peelL⇔ d n w g [] Ys c = peelR⇔ d n w g Ys c
peelL⇔ d n w g (X ∷ Xs) Ys c {V = V ↓ s} =
  iff (λ (is , r) → is , to (peelL⇔ d n w g Xs Ys c) r)
      (λ (is , r) → is , from (peelL⇔ d n w g Xs Ys c) r)
peelL⇔ d n w g (X ∷ Xs) Ys c {V = ` x₀} = iff (λ ()) (λ ())
peelL⇔ d n w g (X ∷ Xs) Ys c {V = ƛ M₀} = iff (λ ()) (λ ())
peelL⇔ d n w g (X ∷ Xs) Ys c {V = L₀ · M₀} = iff (λ ()) (λ ())
peelL⇔ d n w g (X ∷ Xs) Ys c {V = Λ M₀} = iff (λ ()) (λ ())
peelL⇔ d n w g (X ∷ Xs) Ys c {V = L₀ ⦂∀ C₀ [ T₀ ]} = iff (λ ()) (λ ())
peelL⇔ d n w g (X ∷ Xs) Ys c {V = $ κ₀} = iff (λ ()) (λ ())
peelL⇔ d n w g (X ∷ Xs) Ys c {V = L₀ ⊕[ op₀ ] M₀} = iff (λ ()) (λ ())
peelL⇔ d n w g (X ∷ Xs) Ys c {V = W₀ ⟨ c₀ ⟩} = iff (λ ()) (λ ())
peelL⇔ d n w g (X ∷ Xs) Ys c {V = M₀ ↑ c₀} = iff (λ ()) (λ ())
peelL⇔ d n w g (X ∷ Xs) Ys c {V = blame} = iff (λ ()) (λ ())

-- an entry with a right seal is read later, in both directions
later-∷ : ∀ d {Θ} (Y : TyVar Θ) (Ys : List (TyVar Θ))
  → modeOf d (Y ∷ Ys) ≡ later
later-∷ ≺ Y Ys = refl
later-∷ ≻ Y Ys = refl

-- guarded contents are `G` at the same stage
contentsG⇔ : ∀ k {w} {Φ : Corr Δ Δ′} {T T′} (q : Φ ⊢ T ⊑ T′)
    (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′)
    {V V′}
  → contents ≻ k w guarded (desc q env envR) V V′
    ⇔ G k q w (envI env envR) V V′
contentsG⇔ zero q env envR = iff (λ r → r) (λ r → r)
contentsG⇔ (suc k) q env envR = iff (λ r → r) (λ r → r)

-- a paired entry: one stage up from the leaf of its sealed descriptor
entryP⇔ : ∀ d {n′ n} (le : n′ ≤′ n) (X : TyVar ΘL) Xs (Y : TyVar ΘR) Ys
    (c : Desc ΘL ΘR) {k} → suc k ≤ n′ → ∀ w τL τR {V V′}
  → entry d (suc k) w (renameEntry τL τR (seals X Xs (Y ∷ Ys) c)) V V′
    ⇔ leafBelowS d le (sdesc (X ∷ Xs) (Y ∷ Ys) c) k w τL τR V V′
entryP⇔ d le X Xs Y Ys (desc q env envR) {k} lt w τL τR {V ↓ s} {V′} =
  iff
    (λ (is , r) → is ,
      peelSL-map Xs′ c′ {P = peelSR Ys′ c′ Vk} {P′ = peelSR Ys′ c′ Lb}
        (λ {W} {W′} → peelSR-map Ys′ c′ {P = Vk} {P′ = Lb}
          (λ {U} {U′} → from (leafBelow-⇔ d le q env envR lt w τL τR
                                {U} {U′}))
          {W} {W′})
        (to (peelL⇔ d (suc k) w later Xs′ Ys′ c′ {V} {V′})
          (subst (λ g → peelL d (suc k) w g Xs′ Ys′ c′ V V′)
            (later-∷ d (renameVar τR Y) (map (renameVar τR) Ys)) r)))
    (λ (is , r) → is ,
      subst (λ g → peelL d (suc k) w g Xs′ Ys′ c′ V V′)
        (sym (later-∷ d (renameVar τR Y) (map (renameVar τR) Ys)))
        (from (peelL⇔ d (suc k) w later Xs′ Ys′ c′ {V} {V′})
          (peelSL-map Xs′ c′ {P = peelSR Ys′ c′ Lb} {P′ = peelSR Ys′ c′ Vk}
            (λ {W} {W′} → peelSR-map Ys′ c′ {P = Lb} {P′ = Vk}
              (λ {U} {U′} → to (leafBelow-⇔ d le q env envR lt w τL τR
                                  {U} {U′}))
              {W} {W′})
            r)))
  where
  c′ = renameDesc τL τR (desc q env envR)
  Xs′ = map (renameVar τL) Xs
  Ys′ = map (renameVar τR) (Y ∷ Ys)
  Lb = leafBelow d le (desc q env envR) k w τL τR
  Vk : Term (ΔL w) → Term (ΔR w) → Set
  Vk = 𝒱 d k q w (envI (renameEntries τL τR env)
         (Vec.map (renameᵗ (toRenameᵗ τR)) envR))
entryP⇔ d le X Xs Y Ys c lt w τL τR {` x₀} = iff (λ ()) (λ ())
entryP⇔ d le X Xs Y Ys c lt w τL τR {ƛ M₀} = iff (λ ()) (λ ())
entryP⇔ d le X Xs Y Ys c lt w τL τR {L₀ · M₀} = iff (λ ()) (λ ())
entryP⇔ d le X Xs Y Ys c lt w τL τR {Λ M₀} = iff (λ ()) (λ ())
entryP⇔ d le X Xs Y Ys c lt w τL τR {L₀ ⦂∀ C₀ [ T₀ ]} =
  iff (λ ()) (λ ())
entryP⇔ d le X Xs Y Ys c lt w τL τR {$ κ₀} = iff (λ ()) (λ ())
entryP⇔ d le X Xs Y Ys c lt w τL τR {L₀ ⊕[ op₀ ] M₀} = iff (λ ()) (λ ())
entryP⇔ d le X Xs Y Ys c lt w τL τR {W₀ ⟨ c₀ ⟩} = iff (λ ()) (λ ())
entryP⇔ d le X Xs Y Ys c lt w τL τR {M₀ ↑ c₀} = iff (λ ()) (λ ())
entryP⇔ d le X Xs Y Ys c lt w τL τR {blame} = iff (λ ()) (λ ())

-- a left-only entry in `≺`: one stage up from the left-only leaf
entryO≺⇔ : ∀ {n′ n} (le : n′ ≤′ n) (X : TyVar ΘL) Xs (Ys : List (TyVar ΘR))
    (c : Desc ΘL ΘR) {k} → suc k ≤ n′ → ∀ w τL τR {V V′}
  → entry ≺ (suc k) w (renameEntry τL τR (seals X Xs [] c)) V V′
    ⇔ onlyLeafS ≺ le (sdesc (X ∷ Xs) Ys c) k w τL τR V V′
entryO≺⇔ le X Xs Ys (desc q env envR) {k} lt w τL τR {V ↓ s} {V′} =
  iff
    (λ (is , r) → is ,
      peelSL-map Xs′ c′ {P = Vk} {P′ = Lb}
        (λ {U} {U′} → from (leafBelow-⇔ ≺ le q env envR lt w τL τR
                              {U} {U′}))
        (to (peelL⇔ ≺ (suc k) w later Xs′ [] c′ {V} {V′}) r))
    (λ (is , r) → is ,
      from (peelL⇔ ≺ (suc k) w later Xs′ [] c′ {V} {V′})
        (peelSL-map Xs′ c′ {P = Lb} {P′ = Vk}
          (λ {U} {U′} → to (leafBelow-⇔ ≺ le q env envR lt w τL τR
                              {U} {U′}))
          r))
  where
  c′ = renameDesc τL τR (desc q env envR)
  Xs′ = map (renameVar τL) Xs
  Lb = leafBelow ≺ le (desc q env envR) k w τL τR
  Vk : Term (ΔL w) → Term (ΔR w) → Set
  Vk = 𝒱 ≺ k q w (envI (renameEntries τL τR env)
         (Vec.map (renameᵗ (toRenameᵗ τR)) envR))
entryO≺⇔ le X Xs Ys c lt w τL τR {` x₀} = iff (λ ()) (λ ())
entryO≺⇔ le X Xs Ys c lt w τL τR {ƛ M₀} = iff (λ ()) (λ ())
entryO≺⇔ le X Xs Ys c lt w τL τR {L₀ · M₀} = iff (λ ()) (λ ())
entryO≺⇔ le X Xs Ys c lt w τL τR {Λ M₀} = iff (λ ()) (λ ())
entryO≺⇔ le X Xs Ys c lt w τL τR {L₀ ⦂∀ C₀ [ T₀ ]} = iff (λ ()) (λ ())
entryO≺⇔ le X Xs Ys c lt w τL τR {$ κ₀} = iff (λ ()) (λ ())
entryO≺⇔ le X Xs Ys c lt w τL τR {L₀ ⊕[ op₀ ] M₀} = iff (λ ()) (λ ())
entryO≺⇔ le X Xs Ys c lt w τL τR {W₀ ⟨ c₀ ⟩} = iff (λ ()) (λ ())
entryO≺⇔ le X Xs Ys c lt w τL τR {M₀ ↑ c₀} = iff (λ ()) (λ ())
entryO≺⇔ le X Xs Ys c lt w τL τR {blame} = iff (λ ()) (λ ())

-- a left-only entry in `≻`: the left-only leaf at the same stage
entryO≻⇔ : ∀ {n′ n} (le : n′ ≤′ n) (X : TyVar ΘL) Xs (Ys : List (TyVar ΘR))
    (c : Desc ΘL ΘR) {k} → k ≤ n′ → ∀ w τL τR {V V′}
  → entry ≻ k w (renameEntry τL τR (seals X Xs [] c)) V V′
    ⇔ onlyLeafS ≻ le (sdesc (X ∷ Xs) Ys c) k w τL τR V V′
entryO≻⇔ le X Xs Ys (desc q env envR) {k} lt w τL τR {V ↓ s} {V′} =
  iff
    (λ (is , r) → is ,
      peelSL-map Xs′ c′ {P = contents ≻ k w guarded c′} {P′ = Lg}
        (λ {U} {U′} r′ → from (leafG-⇔ le q env envR lt w τL τR {U} {U′})
                  (to (contentsG⇔ k q env′ envR′ {U} {U′}) r′))
        (to (peelL⇔ ≻ k w guarded Xs′ [] c′ {V} {V′}) r))
    (λ (is , r) → is ,
      from (peelL⇔ ≻ k w guarded Xs′ [] c′ {V} {V′})
        (peelSL-map Xs′ c′ {P = Lg} {P′ = contents ≻ k w guarded c′}
          (λ {U} {U′} r′ → from (contentsG⇔ k q env′ envR′ {U} {U′})
                    (to (leafG-⇔ le q env envR lt w τL τR {U} {U′}) r′))
          r))
  where
  Lg = leafG le (desc q env envR) k w τL τR
  c′ = renameDesc τL τR (desc q env envR)
  env′ = renameEntries τL τR env
  envR′ = Vec.map (renameᵗ (toRenameᵗ τR)) envR
  Xs′ = map (renameVar τL) Xs
entryO≻⇔ le X Xs Ys c lt w τL τR {` x₀} = iff (λ ()) (λ ())
entryO≻⇔ le X Xs Ys c lt w τL τR {ƛ M₀} = iff (λ ()) (λ ())
entryO≻⇔ le X Xs Ys c lt w τL τR {L₀ · M₀} = iff (λ ()) (λ ())
entryO≻⇔ le X Xs Ys c lt w τL τR {Λ M₀} = iff (λ ()) (λ ())
entryO≻⇔ le X Xs Ys c lt w τL τR {L₀ ⦂∀ C₀ [ T₀ ]} = iff (λ ()) (λ ())
entryO≻⇔ le X Xs Ys c lt w τL τR {$ κ₀} = iff (λ ()) (λ ())
entryO≻⇔ le X Xs Ys c lt w τL τR {L₀ ⊕[ op₀ ] M₀} = iff (λ ()) (λ ())
entryO≻⇔ le X Xs Ys c lt w τL τR {W₀ ⟨ c₀ ⟩} = iff (λ ()) (λ ())
entryO≻⇔ le X Xs Ys c lt w τL τR {M₀ ↑ c₀} = iff (λ ()) (λ ())
entryO≻⇔ le X Xs Ys c lt w τL τR {blame} = iff (λ ()) (λ ())

-- a left-only entry at a positive stage k: the left-only leaf at the
-- stage the reveal reads
entryO⇔ : ∀ d {n′ n} (le : n′ ≤′ n) (X : TyVar ΘL) Xs
    (Ys : List (TyVar ΘR)) (c : Desc ΘL ΘR) {k} → 0 < k → k ≤ n′
  → ∀ w τL τR {V V′}
  → entry d k w (renameEntry τL τR (seals X Xs [] c)) V V′
    ⇔ onlyLeafS d le (sdesc (X ∷ Xs) Ys c) (onlyStage d k) w τL τR V V′
entryO⇔ ≺ le X Xs Ys c {zero} () lt
entryO⇔ ≺ le X Xs Ys c {suc k} pos lt = entryO≺⇔ le X Xs Ys c lt
entryO⇔ ≻ le X Xs Ys c {k} pos lt = entryO≻⇔ le X Xs Ys c lt

onlyBelow-≤ : ∀ d {k N} → onlyBelow d k N → k ≤ N
onlyBelow-≤ ≺ lt = <⇒≤ lt
onlyBelow-≤ ≻ le = le

------------------------------------------------------------------------
-- The seal hypotheses for a store entry
------------------------------------------------------------------------

-- the bound variable of `Λ⊑Λ`: its entry against the `∀⊑∀` clause's
-- leaf, at the clause's stage suc s
module SealEntryP (d : Dir) (s : ℕ) {w w₁ : World} (e₁ : w₁ ⊒ w)
    (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
    (c : Desc (ΔL w) (ΔR w)) (β : TyVar (ΔL w₁)) (β′ : TyVar (ΔR w₁))
    where

  private
    le₀ = ≤′-refl {suc s}
    Xs₁ = map (renameVar (ρL e₁)) Xs
    Ys₁ = map (renameVar (ρR e₁)) Ys
    c₁ = renameDesc (ρL e₁) (ρR e₁) c
    Lt = sem (leafBelowS d le₀ (sdesc Xs Ys c))
    Ls = syn (seals β Xs₁ (β′ ∷ Ys₁) c₁)

  open SealNew d le₀ le₀ ≤-refl e₁ Xs Ys c β

  -- the entry in a future of w₁, at the embeddings the clause leaf uses
  readE : ∀ {w′} (e : w′ ⊒ w₁) k → suc k ≤ suc s → ∀ {V V′}
    → leafRel d (suc k) w′ (transportLeaf (ρL e) (ρR e) Ls) V V′
    → leafBelowS d le₀ (sdesc (β ∷ Xs₁) (β′ ∷ Ys₁) c₁) k w′
        (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
  readE {w′} e k lt {V} {V′} r =
    to (entryP⇔ d le₀ β Xs₁ β′ Ys₁ c₁ lt w′ (id↪ᵗ ∘↪ ρL e)
         (id↪ᵗ ∘↪ ρR e))
      (subst₂ (λ σL σR → leafRel d (suc k) w′ (transportLeaf σL σR Ls) V V′)
        (sym (∘↪-idˡ (ρL e))) (sym (∘↪-idˡ (ρR e))) r)

  writeE : ∀ {w′} (e : w′ ⊒ w₁) k → suc k ≤ suc s → ∀ {V V′}
    → leafBelowS d le₀ (sdesc (β ∷ Xs₁) (β′ ∷ Ys₁) c₁) k w′
        (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
    → leafRel d (suc k) w′ (transportLeaf (ρL e) (ρR e) Ls) V V′
  writeE {w′} e k lt {V} {V′} r =
    subst₂ (λ σL σR → leafRel d (suc k) w′ (transportLeaf σL σR Ls) V V′)
      (∘↪-idˡ (ρL e)) (∘↪-idˡ (ρR e))
      (from (entryP⇔ d le₀ β Xs₁ β′ Ys₁ c₁ lt w′ (id↪ᵗ ∘↪ ρL e)
              (id↪ᵗ ∘↪ ρR e)) r)

  sealEntryP : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    → SealI d s w₁ (m-pair {Φ = pair Φ} {X = zero} ↔-here β′) β
        (extPairI (＇ β) (＇ β′) Ls (δt ↑ᴵ e₁))
        (extPairI (repL Xs c) (repR Ys c) Lt δt ↑ᴵ e₁)
  sealEntryP = rev , con
    where
    rev : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k ≤ s → ∀ {Vl Vr}
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls) Vl Vr
      → sealedL (toRenameᵗ (ρL e) β)
          (renameᵗ (toRenameᵗ (ρL e))
            (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c)))
          (sealedR (toRenameᵗ (ρR e) β′)
            (renameᵗ (toRenameᵗ (ρR e))
              (renameᵗ (toRenameᵗ (ρR e₁)) (repR Ys c)))
            (leafRel d (pred k) w′ (transportLeaf (ρL e) (ρR e)
              (transportLeaf (ρL e₁) (ρR e₁) Lt)))) Vl Vr
    rev {w′} e {zero} () le r
    rev {w′} e {suc k} pos le r =
      sealedL-map (varβ e β) (repβ e)
        (sealedR-map (varβR e β′) (repβ′ e) (readT e k))
        (sealS→ d le₀ Xs₁ Ys₁ c₁ β β′ k w′ (id↪ᵗ ∘↪ ρL e)
          (id↪ᵗ ∘↪ ρR e) (readE e k (≤-trans le (n≤1+n s)) r))

    con : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k < s → ∀ {Wl Wr}
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
          (transportLeaf (ρL e₁) (ρR e₁) Lt)) Wl Wr
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls)
          (Wl ↓ seal (toRenameᵗ (ρL e) β)
            (renameᵗ (toRenameᵗ (ρL e))
              (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c))))
          (Wr ↓ seal (toRenameᵗ (ρR e) β′)
            (renameᵗ (toRenameᵗ (ρR e))
              (renameᵗ (toRenameᵗ (ρR e₁)) (repR Ys c))))
    con {w′} e {zero} () lt r
    con {w′} e {suc k} pos lt r =
      writeE e k lt′
        (sealS← d le₀ Xs₁ Ys₁ c₁ β β′ k w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)
          ((sym (varβ e β) , sym (repβ e)) ,
            (sym (varβR e β′) , sym (repβ′ e)) ,
            writeS e k lt′
              (leafBelowS-down d le₀ (sdesc Xs Ys c) (n≤1+n k) w′ _ _ r)))
      where
      lt′ : suc k ≤ suc s
      lt′ = ≤-trans (n≤1+n (suc k)) (≤-trans lt (n≤1+n s))

-- the bound variable of a left-only `Λ`: its entry against the `∀⊑`
-- clause's leaf, at the clause's stage n ≥ s
module SealEntryO (d : Dir) {s n : ℕ} (s≤n : s ≤ n) {w w₁ : World}
    (e₁ : w₁ ⊒ w) (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
    (c : Desc (ΔL w) (ΔR w)) (β : TyVar (ΔL w₁)) where

  private
    le₀ = ≤′-refl {n}
    Xs₁ = map (renameVar (ρL e₁)) Xs
    Ys₁ = map (renameVar (ρR e₁)) Ys
    c₁ = renameDesc (ρL e₁) (ρR e₁) c
    c₀ = sdesc Xs Ys c
    Lt = sem (onlyLeafS d le₀ c₀)
    Ls = syn (seals β Xs₁ [] c₁)

  open SealNew d le₀ le₀ ≤-refl e₁ Xs Ys c β using (varβ; repβ)

  readE : ∀ {w′} (e : w′ ⊒ w₁) k → 0 < k → k ≤ n → ∀ {V V′}
    → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls) V V′
    → onlyLeafS d le₀ (sdesc (β ∷ Xs₁) Ys₁ c₁) (onlyStage d k) w′
        (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
  readE {w′} e k pos lt {V} {V′} r =
    to (entryO⇔ d le₀ β Xs₁ Ys₁ c₁ pos lt w′ (id↪ᵗ ∘↪ ρL e)
         (id↪ᵗ ∘↪ ρR e))
      (subst₂ (λ σL σR → leafRel d k w′ (transportLeaf σL σR Ls) V V′)
        (sym (∘↪-idˡ (ρL e))) (sym (∘↪-idˡ (ρR e))) r)

  writeE : ∀ {w′} (e : w′ ⊒ w₁) k → 0 < k → k ≤ n → ∀ {V V′}
    → onlyLeafS d le₀ (sdesc (β ∷ Xs₁) Ys₁ c₁) (onlyStage d k) w′
        (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
    → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls) V V′
  writeE {w′} e k pos lt {V} {V′} r =
    subst₂ (λ σL σR → leafRel d k w′ (transportLeaf σL σR Ls) V V′)
      (∘↪-idˡ (ρL e)) (∘↪-idˡ (ρR e))
      (from (entryO⇔ d le₀ β Xs₁ Ys₁ c₁ pos lt w′ (id↪ᵗ ∘↪ ρL e)
              (id↪ᵗ ∘↪ ρR e)) r)

  -- the target leaf and the clause leaf of the renamed descriptor
  readT : ∀ {w′} (e : w′ ⊒ w₁) k {V V′}
    → onlyLeafS d le₀ (sdesc Xs₁ Ys₁ c₁) k w′
        (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
    → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
        (transportLeaf (ρL e₁) (ρR e₁) Lt)) V V′
  readT e k r = to (onlyLeafS-ren d le₀ (ρL e₁) (ρR e₁) c₀ k _ _ _) r

  writeT : ∀ {w′} (e : w′ ⊒ w₁) k {V V′}
    → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
        (transportLeaf (ρL e₁) (ρR e₁) Lt)) V V′
    → onlyLeafS d le₀ (sdesc Xs₁ Ys₁ c₁) k w′
        (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) V V′
  writeT e k r = from (onlyLeafS-ren d le₀ (ρL e₁) (ρR e₁) c₀ k _ _ _) r

  sealEntryO : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    → SealI d s w₁ (m-left {Φ = only Φ} {X = zero}) β
        (extOnlyI (＇ β) Ls (δt ↑ᴵ e₁))
        (extOnlyI (repL Xs c) Lt δt ↑ᴵ e₁)
  sealEntryO = rev , con
    where
    rev : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → k ≤ s → ∀ {Vl Vr}
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls) Vl Vr
      → sealedL (toRenameᵗ (ρL e) β)
          (renameᵗ (toRenameᵗ (ρL e))
            (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c)))
          (leafRel d (onlyStage d k) w′ (transportLeaf (ρL e) (ρR e)
            (transportLeaf (ρL e₁) (ρR e₁) Lt))) Vl Vr
    rev {w′} e {k} pos le r =
      sealedL-map (varβ e β) (repβ e) (readT e (onlyStage d k))
        (onlyS→ d le₀ Xs₁ Ys₁ c₁ β (onlyStage d k) w′ (id↪ᵗ ∘↪ ρL e)
          (id↪ᵗ ∘↪ ρR e) (readE e k pos (≤-trans le s≤n) r))

    con : ∀ {w′} (e : w′ ⊒ w₁) {k} → 0 < k → onlyBelow d k s
      → ∀ {Wl Vr}
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e)
          (transportLeaf (ρL e₁) (ρR e₁) Lt)) Wl Vr
      → leafRel d k w′ (transportLeaf (ρL e) (ρR e) Ls)
          (Wl ↓ seal (toRenameᵗ (ρL e) β)
            (renameᵗ (toRenameᵗ (ρL e))
              (renameᵗ (toRenameᵗ (ρL e₁)) (repL Xs c)))) Vr
    con {w′} e {k} pos lt r =
      writeE e k pos (≤-trans (onlyBelow-≤ d lt) s≤n)
        (onlyS← d le₀ Xs₁ Ys₁ c₁ β (onlyStage d k) w′ (id↪ᵗ ∘↪ ρL e)
          (id↪ᵗ ∘↪ ρR e)
          ((sym (varβ e β) , sym (repβ e)) ,
            writeT e (onlyStage d k)
              (onlyLeafS-down d le₀ c₀ (onlyStage-≤ d k) w′ _ _ r)))

------------------------------------------------------------------------
-- The instances
------------------------------------------------------------------------

-- `Λ⊑Λ`: both sides allocate and reveal; the body, related with the
-- bound variable's store entry, gives the `∀⊑∀` clause's relation at
-- the sealed descriptor `sdesc Xs Ys c`, one stage below the clause's
module LamPair (d : Dir) (s : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B) (w : World) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    (fδ : FreshI Φ d s both w δ)
    (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
    (c : Desc (ΔL w) (ΔR w)) (wf : WFDesc c)
    (tags : TyVar (suc (ΔL w)) → Tag (suc (ΔL w)) (suc (ΔR w)))
    (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ (bind (repL Xs c) ∷ [])) X)
            ≡ renameTag (embedᶜˢ (bind (repL Xs c) ∷ []))
                (embedᶜˢ (bind (repR Ys c) ∷ [])) (tag w X))
    where

  Tl = repL Xs c
  Tr = repR Ys c
  e₁ = stepExt (bind Tl ∷ []) (bind Tr ∷ []) tags ok
  w₁ = world (suc (ΔL w)) (suc (ΔR w)) tags

  -- the bound variable's store entry, and the clause's leaf
  Ls = syn (seals zero (map (renameVar (ρL e₁)) Xs)
             (zero ∷ map (renameVar (ρR e₁)) Ys)
             (renameDesc (ρL e₁) (ρR e₁) c))
  Lt = sem (leafBelowS d (≤′-refl {suc s}) (sdesc Xs Ys c))

  δβ = extPairI (＇ zero) (＇ zero) Ls (δ ↑ᴵ e₁)
  δg = extPairI Tl Tr Lt δ ↑ᴵ e₁
  BtL = substᵗ (extsᵗ (δl δ)) A
  BtR = substᵗ (extsᵗ (δr δ)) B

  private
    hβ : ConvI d s both w₁ (m-pair {Φ = pair Φ} ↔-here zero) zero δβ δg
    hβ = ConvI-newP e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl}
      {Tr = Tr} (new-bind Tr) ≤-refl fδ good-syn
      (leafBelowS-good d (≤′-refl {suc s}) (sdesc Xs Ys c))
      (proj₁ (oracle-all d (suc s)) (≤′-refl {suc s}) ≤-refl
        (sdesc Xs Ys c) wf)
      (SealEntryP.sealEntryP d s e₁ Xs Ys c zero zero {Φ = Φ} {δt = δ})

    K : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₃ (δβ ↑ᴵ e₃) Ql Qr
      → ℰ d k p w₃ (δg ↑ᴵ e₃)
          (mplug (renameMFrame (ρL e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗))) Ql)
          (mplug (renameMFrame (ρR e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BtR 〗))) Qr)
    K e₃ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans (revRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) zero δβ δg Ql A)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
            (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δ) A)))))
        (trans (rcRen e₃ (m-pair {Φ = pair Φ} ↔-here zero) δβ δg Qr B)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρR e₃))
            (pk-〖〗 refl (shift-ty Tr Tr) (open0 Tr (δr δ) B)))))
        (revC d p (ConvI-↑ e₃ hβ) k≤s ql qr q)

  lamPair : ∀ {Ml Mr} → ℰ d s p w₁ δβ Ml Mr
    → ℰ d s p w₁ δg (Ml ↑ 〖 zero , ⇑ᵗ Tl ↑ BtL 〗)
        (Mr ↑ 〖 zero , ⇑ᵗ Tr ↑ BtR 〗)
  lamPair r =
    ℰ-bind₂ d s p p w₁ {δ₁ = δβ} {δ₂ = δg}
      (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗))
      (just (reveal 〖 zero , ⇑ᵗ Tr ↑ BtR 〗)) r K

-- a left-only `Λ`: the left allocates and reveals; the right does not
-- move.  The `∀⊑` clause's stage is n, and the body is read at s ≤ n
-- (s = n in `≻`, where the left's steps are not counted)
module LamOnly (d : Dir) {n s : ℕ} (s≤n : s ≤ n) {Δ Δ′} {Φ : Corr Δ Δ′}
    {A B} (p : only Φ ⊢ A ⊑ B) (w : World)
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {rk} (fδ : FreshI Φ d s rk w δ)
    (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
    (c : Desc (ΔL w) (ΔR w))
    (tags : TyVar (suc (ΔL w)) → Tag (suc (ΔL w)) (ΔR w))
    (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ (bind (repL Xs c) ∷ [])) X)
            ≡ renameTag (embedᶜˢ (bind (repL Xs c) ∷ []))
                (embedᶜˢ ([] {ΔR w})) (tag w X))
    where

  Tl = repL Xs c
  e₁ = stepExt (bind Tl ∷ []) [] tags ok
  w₁ = world (suc (ΔL w)) (ΔR w) tags

  Ls = syn (seals zero (map (renameVar (ρL e₁)) Xs) []
             (renameDesc (ρL e₁) (ρR e₁) c))
  Lt = sem (onlyLeafS d (≤′-refl {n}) (sdesc Xs Ys c))

  δβ = extOnlyI (＇ zero) Ls (δ ↑ᴵ e₁)
  δg = extOnlyI Tl Lt δ ↑ᴵ e₁
  BtL = substᵗ (extsᵗ (δl δ)) A

  private
    hβ : ConvI d s rk w₁ (m-left {Φ = only Φ} {X = zero}) zero δβ δg
    hβ = ConvI-newO e₁ (new-bind Tl) {Ls = Ls} {Lt = Lt} {Tl = Tl} ≤-refl
      fδ good-syn (onlyLeafS-good d (≤′-refl {n}) (sdesc Xs Ys c))
      (proj₂ (oracle-all d n) (≤′-refl {n}) ≤-refl (sdesc Xs Ys c))
      (SealEntryO.sealEntryO d s≤n e₁ Xs Ys c zero {Φ = Φ} {δt = δ})

    K : ∀ {w₃} (e₃ : w₃ ⊒ w₁) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p w₃ (δβ ↑ᴵ e₃) Ql Qr
      → ℰ d k p w₃ (δg ↑ᴵ e₃)
          (mplug (renameMFrame (ρL e₃)
            (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗))) Ql) Qr
    K e₃ {k} k≤s {Ql} {Qr} ql qr q =
      ℰᵍ-≡
        (trans
          (revRen e₃ (m-left {Φ = only Φ} {X = zero}) zero δβ δg Ql A)
          (↑-pk (pk-ren↑ (toRenameᵗ (ρL e₃))
            (pk-〖〗 refl (shift-ty Tl Tl) (open0 Tl (δl δ) A)))))
        refl
        (revC d p (ConvI-↑ e₃ hβ) k≤s ql qr q)

  lamOnly : ∀ {Ml Mr} → ℰ d s p w₁ δβ Ml Mr
    → ℰ d s p w₁ δg (Ml ↑ 〖 zero , ⇑ᵗ Tl ↑ BtL 〗) Mr
  lamOnly r =
    ℰ-bind₂ d s p p w₁ {δ₁ = δβ} {δ₂ = δg}
      (just (reveal 〖 zero , ⇑ᵗ Tl ↑ BtL 〗)) nothing r K
