module proof.LR.IdentityCast where

-- File Charter:
--   * The identity-cast lemma (notes/logrel-dgg.md, Section 6.9, item
--     6): a left value cast by `refl∼` of the left type of the
--     precision at hand stays related to the same right value
--     (`identityCast`).
--   * `refl∼ T` is an identity step (`id` at an atom) or inert (a
--     function or `∀` proxy, a value; `reflShape`).  The lemma at values
--     (`idV`) is the inert case: the proxy is related.  The expression
--     form (`idE`) takes the identity step in the other case.
--   * Proxies, by induction on the derivation: a function proxy applies
--     by `β-⇒`, its argument and result cast by identity casts on the
--     two subderivations (`funId`, through `app-core`); a `∀` proxy
--     instantiates by `β-∀` to its body cast by
--     `(refl∼ A) [ T ]ᶜ = refl∼ (A [ T ]ᵗ)` (`refl-open`, `tyAppId`).
--   * Variables: the lemma at a leaf is a hypothesis on the
--     interpretation (`IdI`, every future).  Descriptor entries satisfy
--     it vacuously: their types are store variables, whose identity
--     casts are not inert.  The leaves the `∀` clauses build satisfy it
--     by the lemma on the descriptor's derivation, at lower stages
--     (`Below`), or in `≻` at the same stage through `G`, whose content
--     is one stage down (`idG`, `BelowG`).
--   * `ora`: the lemma at every stage, by induction on the stage; so the
--     clause leaves are closed at every bound (`leafBelowS-closed`,
--     `onlyLeafS-closed`).
--   * `selfO`: the base case `VarI.selfO` of the cast lemma
--     (`proof.LR.CastLemma`, whose `CastRel` and `ℰ-down` this file
--     uses) at a left-only variable whose world cast is `refl∼` of its
--     left type; `selfO-only` at the new variable of a left-only clause
--     (case 6's induction hypothesis).

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _≤′_;
  ≤′-refl; _≤?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤⇒≤′; ≤′⇒≤;
  n≤1+n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Vec using (Vec; lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency
open import CastTerms using (Term; Value; _⟨_⟩; _·_; _⦂∀_[_]; renameᵗᵐ;
  Inert; fun; all)
import CastTerms as CT
open import Reduction using (_—→_; β-id; β-⇒; β-∀)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import LR.Frame using (cast)
open import proof.DGG.CenterRename using (_∘↪_; toRenameᵗ-∘)
open import proof.TypeInTermSubst using (toRename-id-eq;
  renameᵗᵐ-preserves-Value)
open import proof.LR.WorldProps using (⊒-refl; ⊒-trans; entryTy-rename;
  leftTy-rename)
open import proof.LR.InterpProps
open import proof.LR.Monotone using (GoodI; GoodI-↑; GoodI-extPairI;
  GoodI-extOnlyI; GoodI-extDeadI; good-envI; good-closedI;
  leafBelowS-good; onlyLeafS-good; 𝒱≤-cast; 𝒱<→𝒱; 𝒱→𝒱<; G≤→G; G→G≤;
  𝒱-down; funRel-mono; funRel-down)
open import proof.LR.Expression using (ℰ-value; ℰ-bind₂)
open import proof.LR.ConvBase using (ℰ-zero; ℰ-steps?; stay; step;
  app-core; ℰ-app-steps; funStar-map; ★★-δ)
open import proof.LR.SubstLemma using (substᵗ-∘)
open import proof.LR.CastLemma using (CastRel; ℰ-down)

private
  variable
    Δ Δ′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- Identity casts
------------------------------------------------------------------------

-- an identity cast is an identity step or inert
reflShape : ∀ {Θ} {μ : Env∼ Θ} (T : Ty Θ)
  → (Σ[ a ∈ Atom T ] refl∼ {μ = μ} T ≡ id a) ⊎ Inert (refl∼ {μ = μ} T)
reflShape (＇ X) = inj₁ (＇ X , refl)
reflShape (‵ ι) = inj₁ (‵ ι , refl)
reflShape ★ = inj₁ (★ , refl)
reflShape (A ⇒ B) = inj₂ fun
reflShape (`∀ A) = inj₂ all

refl-transport : ∀ {Θ} {μ ν : Env∼ Θ} (eq : Env∼Eq μ ν) (A : Ty Θ)
  → transport-env∼ eq (refl∼ A) ≡ refl∼ A
refl-transport eq (＇ X) = refl
refl-transport eq (‵ ι) = refl
refl-transport eq ★ = refl
refl-transport eq (A ⇒ B) =
  cong₂ _↦_ (refl-transport (flipEnv∼Eq eq) A) (refl-transport eq B)
refl-transport eq (`∀ A) = cong ∀ᶜ_ (refl-transport (extEnv∼Eq eq) A)

refl-sym : ∀ {Θ} {μ : Env∼ Θ} (A : Ty Θ)
  → sym∼ (refl∼ {μ = μ} A) ≡ refl∼ A
refl-sym (＇ X) = refl
refl-sym (‵ ι) = refl
refl-sym ★ = refl
refl-sym (A ⇒ B) = cong₂ _↦_ (refl-sym A) (refl-sym B)
refl-sym (`∀ A) =
  cong ∀ᶜ_ (trans (cong (transport-env∼ flip-extᵐ) (refl-sym A))
    (refl-transport flip-extᵐ A))

refl-rename : ∀ {Θ Θ′} {μ : Env∼ Θ} {μ′ : Env∼ Θ′} (ρ : Θ ⇒ʳ Θ′)
    (h : ∀ X → μ′ ‼ (ρ X) ≡ μ ‼ X) (A : Ty Θ)
  → rename∼ {μ = μ} {μ′ = μ′} ρ h (refl∼ A) ≡ refl∼ (renameᵗ ρ A)
refl-rename ρ h (＇ X) = refl
refl-rename ρ h (‵ ι) = refl
refl-rename ρ h ★ = refl
refl-rename {μ = μ} {μ′} ρ h (A ⇒ B) =
  cong₂ _↦_ (refl-rename {μ = flipᵐ μ} {μ′ = flipᵐ μ′} ρ _ A)
    (refl-rename ρ h B)
refl-rename {μ = μ} {μ′} ρ h (`∀ A) =
  cong ∀ᶜ_ (refl-rename {μ = extᵐ μ} {μ′ = extᵐ μ′} (extᵗ ρ) _ A)

-- a substitution whose casts at the variables are identity casts
refl-subst : ∀ {Θ Θ′} {μ : Env∼ Θ} {ν : Env∼ Θ′} {σ : Θ ⇒ˢ Θ′}
    (s : SubstEnv∼ μ ν σ)
  → (∀ X → SubstEnv∼.self s X ≡ refl∼ (σ X))
  → ∀ A → subst∼ s (refl∼ A) ≡ refl∼ (substᵗ σ A)
refl-subst s hs (＇ X) = hs X
refl-subst s hs (‵ ι) = refl
refl-subst s hs ★ = refl
refl-subst {σ = σ} s hs (A ⇒ B) =
  cong₂ _↦_
    (refl-subst (flip-SubstEnv∼ s)
      (λ X → trans (cong sym∼ (hs X)) (refl-sym (σ X))) A)
    (refl-subst s hs B)
refl-subst {ν = ν} {σ = σ} s hs (`∀ A) =
  cong ∀ᶜ_ (refl-subst (ext-SubstEnv∼ s) hs′ A)
  where
  hs′ : ∀ X → SubstEnv∼.self (ext-SubstEnv∼ s) X ≡ refl∼ (extsᵗ σ X)
  hs′ zero = refl
  hs′ (suc X) =
    trans (cong (rename∼ {μ = ν} {μ′ = extᵐ ν} suc _) (hs X))
      (refl-rename {μ = ν} {μ′ = extᵐ ν} suc _ (σ X))

-- the identity cast, opened at T
refl-open : ∀ {Θ} {μ : Env∼ Θ} (A : Ty (suc Θ)) (T : Ty Θ)
  → (refl∼ {μ = extᵐ μ} A) [ T ]ᶜ ≡ refl∼ (A [ T ]ᵗ)
refl-open A T = refl-subst _ (λ X → refl) A

-- opening a body substituted under a binder
open-• : ∀ {Θ Θ′} (σ : Θ ⇒ˢ Θ′) (T : Ty Θ′) (A : Ty (suc Θ))
  → substᵗ (T •ˢ σ) A ≡ (substᵗ (extsᵗ σ) A) [ T ]ᵗ
open-• σ T A =
  sym (trans (substᵗ-∘ (singleSubᵗ T) (extsᵗ σ) A) (substᵗ-cong A eq))
  where
  eq : ∀ X → substᵗ (singleSubᵗ T) (extsᵗ σ X) ≡ (T •ˢ σ) X
  eq zero = refl
  eq (suc X) = shift-openᵗ (σ X) T

-- the interpretation's left types, in a future
δ↑-ty : ∀ {w w′ : World} (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) (e : w′ ⊒ w)
    (A : Ty Δ)
  → substᵗ (δl (δ ↑ᴵ e)) A ≡ renameᵗ (toRenameᵗ (ρL e)) (substᵗ (δl δ) A)
δ↑-ty δ e A = sym (renameᵗ-subst (toRenameᵗ (ρL e)) (δl δ) A)

-- a renamed identity cast is the identity cast at the renamed type
ren-refl : ∀ {Θ Θ′} (ρ : Θ ↪ᵗ Θ′) {μ : Env∼ Θ} (V : Term Θ′) (T : Ty Θ)
    {T′} → T′ ≡ renameᵗ (toRenameᵗ ρ) T
  → V ⟨ renameᵐᶜ ρ (refl∼ {μ = μ} T) ⟩
    ≡ V ⟨ refl∼ {μ = renameEnv∼ ρ μ} T′ ⟩
ren-refl ρ {μ} V T refl =
  cong (λ c → V ⟨ c ⟩)
    (refl-rename {μ = μ} {μ′ = renameEnv∼ ρ μ} (toRenameᵗ ρ)
      (renameEnv∼-preserves ρ μ) T)

------------------------------------------------------------------------
-- Leaves closed under identity casts
------------------------------------------------------------------------

-- the left identity cast at T keeps values related by the leaf, when it
-- is inert
IdLeaf : Dir → (w : World) → Leaf (ΔL w) (ΔR w) → Ty (ΔL w) → Set
IdLeaf d w l T = ∀ k {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → Inert (refl∼ {μ = μ} T) → leafRel d k w l Vl Vr
  → leafRel d k w l (Vl ⟨ refl∼ {μ = μ} T ⟩) Vr

-- every leaf of the interpretation, in every future
IdI : Dir → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w) → Set
IdI d w δ =
  ∀ {w′} (e : w′ ⊒ w) X → IdLeaf d w′ (leaf (δ ↑ᴵ e) X) (δl (δ ↑ᴵ e) X)

-- the same, for a relation read through embeddings
IdΩ : Dir → RelΩ ΘL ΘR → Ty ΘL → Set
IdΩ d R T = ∀ k w τL τR {T′} → T′ ≡ renameᵗ (toRenameᵗ τL) T
  → ∀ {μ : Env∼ (ΔL w)} {V V′} → Value V → Value V′
  → Inert (refl∼ {μ = μ} T′) → R k w τL τR V V′
  → R k w τL τR (V ⟨ refl∼ {μ = μ} T′ ⟩) V′

IdLeaf-resp : ∀ d {w} {l l′ : Leaf (ΔL w) (ΔR w)} {T T′}
  → T ≡ T′ → l ≈ˡ l′ → IdLeaf d w l T → IdLeaf d w l′ T′
IdLeaf-resp d {w} refl h c k {μ} vl vr i r =
  leafRel-resp d k w h
    (c k {μ = μ} vl vr i (leafRel-resp d k w (≈ˡ-sym h) r))

IdI-now : ∀ d {w} (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → IdI d w δ
  → ∀ X → IdLeaf d w (leaf δ X) (δl δ X)
IdI-now d {w} δ h X =
  IdLeaf-resp d (δl≡ (↑ᴵ-refl {w = w} δ) X) (leaf≈ (↑ᴵ-refl {w = w} δ) X)
    (h (⊒-refl w) X)

IdI-↑ : ∀ d {w w′} (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → IdI d w δ
  → (e : w′ ⊒ w) → IdI d w′ (δ ↑ᴵ e)
IdI-↑ d δ h e e′ X =
  IdLeaf-resp d (δl≡ (≈ᴵ-sym (↑ᴵ-trans δ e′ e)) X)
    (leaf≈ (≈ᴵ-sym (↑ᴵ-trans δ e′ e)) X) (h (⊒-trans e′ e) X)

-- a semantic leaf, moved to a world
IdLeaf-transport : ∀ d {R : RelΩ ΘL ΘR} {T} → IdΩ d R T
  → ∀ w (σL : ΘL ↪ᵗ ΔL w) (σR : ΘR ↪ᵗ ΔR w)
  → IdLeaf d w (transportLeaf σL σR (sem R)) (renameᵗ (toRenameᵗ σL) T)
IdLeaf-transport d {T = T} hR w σL σR k {μ} vl vr i r =
  hR k w (id↪ᵗ ∘↪ σL) (id↪ᵗ ∘↪ σR)
    (renameᵗ-cong T
      (λ X → sym (trans (toRenameᵗ-∘ id↪ᵗ σL X) (toRename-id-eq _))))
    {μ = μ} vl vr i r

IdI-pair : ∀ d {w} {T T′} {R : RelΩ (ΔL w) (ΔR w)}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → IdΩ d R T → IdI d w δ → IdI d w (extPairI T T′ (sem R) δ)
IdI-pair d hR h e zero = IdLeaf-transport d hR _ (ρL e) (ρR e)
IdI-pair d hR h e (suc X) = h e X

IdI-only : ∀ d {w} {T} {R : RelΩ (ΔL w) (ΔR w)}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → IdΩ d R T → IdI d w δ → IdI d w (extOnlyI T (sem R) δ)
IdI-only d hR h e zero = IdLeaf-transport d hR _ (ρL e) (ρR e)
IdI-only d hR h e (suc X) = h e X

IdI-dead : ∀ d {w} {T} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → IdI d w δ → IdI d w (extDeadI T δ)
IdI-dead d h e zero k vl vr i r = tt
IdI-dead d h e (suc X) = h e X

-- an entry's type is a store variable: its identity cast is not inert
IdLeaf-syn : ∀ d w (en : Entry (ΔL w) (ΔR w))
  → IdLeaf d w (syn en) (entryTy en)
IdLeaf-syn d w (seals X Xs Ys c) k vl vr () r

IdI-envI : ∀ d {w} (env : Vec (Entry (ΔL w) (ΔR w)) Δ)
    (envR : Vec (Ty (ΔR w)) Δ′)
  → IdI d w (envI env envR)
IdI-envI d env envR {w′} e X =
  IdLeaf-resp d {w′} {l = syn en} {l′ = syn en}
    (entryTy-rename (ρL e) (ρR e) (lookup env X)) ≈ˡ-refl
    (IdLeaf-syn d w′ en)
  where
  en = renameEntry (ρL e) (ρR e) (lookup env X)

------------------------------------------------------------------------
-- The statements, at a stage
------------------------------------------------------------------------

-- the inert case, at values
IdVp : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} → Φ ⊢ A ⊑ A′ → Set₁
IdVp d n {Δ} {Δ′} {A = A} p =
  ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI d w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → Inert (refl∼ {μ = μ} (substᵗ (δl δ) A))
  → 𝒱 d n p w δ Vl Vr
  → 𝒱 d n p w δ (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) A) ⟩) Vr

-- the same for `G`
IdGp : ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} → Φ ⊢ A ⊑ A′ → Set₁
IdGp n {Δ} {Δ′} {A = A} p =
  ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI ≻ w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → Inert (refl∼ {μ = μ} (substᵗ (δl δ) A))
  → G n p w δ Vl Vr
  → G n p w δ (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) A) ⟩) Vr

-- the lemma below a stage
Below : Dir → ℕ → Set₁
Below d N = ∀ {k} → k < N → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
  (p : Φ ⊢ A ⊑ A′) → IdVp d k p

BelowG : ℕ → Set₁
BelowG N = ∀ {k} → k < N → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
  (p : Φ ⊢ A ⊑ A′) → IdGp k p

-- `G` up to a stage, which the left-only leaves of `≻` read
UpG : ℕ → Set₁
UpG N = ∀ {k} → k ≤ N → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
  (p : Φ ⊢ A ⊑ A′) → IdGp k p

BG : Dir → ℕ → Set₁
BG ≺ N = ⊤₁
BG ≻ N = BelowG N

UpD : Dir → ℕ → Set₁
UpD ≺ N = ⊤₁
UpD ≻ N = UpG N

Below-≤ : ∀ d {m n} → m ≤ n → Below d n → Below d m
Below-≤ d m≤n b k<m = b (≤-trans k<m m≤n)

BG-≤ : ∀ d {m n} → m ≤ n → BG d n → BG d m
BG-≤ ≺ m≤n b = tt₁
BG-≤ ≻ m≤n b k<m = b (≤-trans k<m m≤n)

UpD-≤ : ∀ d {m n} → m ≤ n → UpD d n → UpD d m
UpD-≤ ≺ m≤n u = tt₁
UpD-≤ ≻ m≤n u k≤m = u (≤-trans k≤m m≤n)

-- the expression form, from the inert case
idE : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) → IdVp d n p
  → ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI d w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → 𝒱 d n p w δ Vl Vr
  → ℰ d n p w δ (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) A) ⟩) Vr
idE d n {A = A} p iv w δ g h {μ} {Vl} {Vr} vl vr r
    with reflShape {μ = μ} (substᵗ (δl δ) A)
idE d n {A = A} p iv w δ g h {μ} {Vl} {Vr} vl vr r | inj₁ (a , eq) =
  subst (λ c → ℰ d n p w δ (Vl ⟨ c ⟩) Vr) (sym eq)
    (ℰ-steps? d n p w g (step (β-id vl)) stay vl vr r)
idE d n {A = A} p iv w δ g h {μ} {Vl} {Vr} vl vr r | inj₂ i =
  ℰ-value d n p w (vl CT.《 i 》) vr (iv w δ g h {μ = μ} vl vr i r)

------------------------------------------------------------------------
-- Stage and relation plumbing
------------------------------------------------------------------------

toℰ : ∀ d {n n′} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {A A′}
    (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr}
  → ℰᵍ d n′ w (λ le′ w′ e → 𝒱≤ d (≤′-trans le′ le) p w′ (δ ↑ᴵ e)) Ml Mr
  → ℰ d n′ p w δ Ml Mr
toℰ d le p w =
  ℰᵍ-map d _ w (λ le′ w′ e V V′ → 𝒱≤-cast d (≤′-trans le′ le) le′ p w′)

fromℰ : ∀ d {n n′} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {A A′}
    (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr}
  → ℰ d n′ p w δ Ml Mr
  → ℰᵍ d n′ w (λ le′ w′ e → 𝒱≤ d (≤′-trans le′ le) p w′ (δ ↑ᴵ e)) Ml Mr
fromℰ d le p w =
  ℰᵍ-map d _ w (λ le′ w′ e V V′ → 𝒱≤-cast d le′ (≤′-trans le′ le) p w′)

-- one left step, then any stage up to n
ℰ-stepL≤ : ∀ d n {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Ml′ Mr}
  → Ml —→ Ml′ → (∀ {s} → s ≤ n → ℰ d s p w δ Ml′ Mr)
  → ℰ d n p w δ Ml Mr
ℰ-stepL≤ d n p w sl k =
  ℰ-app-steps d p w nothing ≤-refl sl refl (λ s≤ _ → k s≤)

-- `★` at a stage up to n, as the value relation at `★ ⊑ ★`
starAt→𝒱 : ∀ d {m n} (le : m ≤′ n) w {V V′}
  → starAt d le w V V′ → 𝒱 d m (★⊑★ {Φ = []}) w closedI V V′
starAt→𝒱 ≺ ≤′-refl w r = r
starAt→𝒱 ≻ ≤′-refl w r = r
starAt→𝒱 ≺ (Data.Nat.≤′-step le) w r = starAt→𝒱 ≺ le w r
starAt→𝒱 ≻ (Data.Nat.≤′-step le) w r = starAt→𝒱 ≻ le w r

𝒱→starAt : ∀ d {m n} (le : m ≤′ n) w {V V′}
  → 𝒱 d m (★⊑★ {Φ = []}) w closedI V V′ → starAt d le w V V′
𝒱→starAt ≺ ≤′-refl w r = r
𝒱→starAt ≻ ≤′-refl w r = r
𝒱→starAt ≺ (Data.Nat.≤′-step le) w r = 𝒱→starAt ≺ le w r
𝒱→starAt ≻ (Data.Nat.≤′-step le) w r = 𝒱→starAt ≻ le w r

starTo : ∀ d {n n′} (le : n′ ≤′ n) w {M M′}
  → ℰᵍ d n′ w (λ le′ w″ e′ → starAt d (≤′-trans le′ le) w″) M M′
  → ℰ d n′ (★⊑★ {Φ = []}) w closedI M M′
starTo d le w =
  ℰᵍ-map d _ w (λ le′ w″ e′ V V′ r →
    𝒱≤-cast d ≤′-refl le′ ★⊑★ w″
      (★★-δ d _ (starAt→𝒱 d (≤′-trans le′ le) w″ r)))

starFrom : ∀ d {n n′} (le : n′ ≤′ n) w {M M′}
  → ℰ d n′ (★⊑★ {Φ = []}) w closedI M M′
  → ℰᵍ d n′ w (λ le′ w″ e′ → starAt d (≤′-trans le′ le) w″) M M′
starFrom d le w =
  ℰᵍ-map d _ w (λ le′ w″ e′ V V′ r →
    𝒱→starAt d (≤′-trans le′ le) w″
      (★★-δ d _ (𝒱≤-cast d le′ ≤′-refl ★⊑★ w″ r)))

------------------------------------------------------------------------
-- Function proxies
------------------------------------------------------------------------

funId : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′ B B′}
    (p : Φ ⊢ A ⊑ A′) (q : Φ ⊢ B ⊑ B′)
  → (∀ {m} → m ≤ n → IdVp d m p) → (∀ {m} → m ≤ n → IdVp d m q)
  → ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI d w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → funRel d n p q w δ Vl Vr
  → funRel d n p q w δ (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) (A ⇒ B)) ⟩)
      Vr
funId d n {A = A} {B = B} p q rp rq w δ g h {μ} {Vl} {Vr} vl vr f
    {w′} e {n′} le Wl Wr wl wr a t =
  ℰᵍ-≡
    (sym (cong (_· Wl)
      (ren-refl (ρL e) (renameᵗᵐ (ρL e) Vl) (substᵗ (δl δ) (A ⇒ B))
        (δ↑-ty δ e (A ⇒ B)))))
    refl
    (fromℰ d le q w′
      (ℰ-stepL≤ d n′ q w′
        (β-⇒ (renameᵗᵐ-preserves-Value (ρL e) vl) wl)
        (λ {s} s≤ →
          app-core d s p q w′ {δ ↑ᴵ e} {δ ↑ᴵ e}
            (renameᵗᵐ-preserves-Value (ρL e) vl)
            (renameᵗᵐ-preserves-Value (ρS e) vr)
            (just (cast (refl∼ {μ = renameEnv∼ (ρL e) μ}
              (substᵗ (δl (δ ↑ᴵ e)) B))))
            nothing t
            (idE d s p (rp (≤-trans s≤ (≤′⇒≤ le))) w′ (δ ↑ᴵ e)
              (GoodI-↑ {δ = δ} g e) (IdI-↑ d δ h e) wl wr
              (𝒱-down d s≤ p w′ (GoodI-↑ {δ = δ} g e)
                (𝒱≤-cast d le ≤′-refl p w′ a)))
            (funRel-down d (≤-trans s≤ (≤′⇒≤ le)) p q w′
              (funRel-mono d n p q e f))
            (λ e″ {k} k≤s {Ql} {Qr} ql qr r →
              ℰᵍ-≡
                (sym (ren-refl (ρL e″) Ql (substᵗ (δl (δ ↑ᴵ e)) B)
                  (δ↑-ty (δ ↑ᴵ e) e″ B)))
                refl
                (idE d k q (rq (≤-trans k≤s (≤-trans s≤ (≤′⇒≤ le))))
                  _ ((δ ↑ᴵ e) ↑ᴵ e″)
                  (GoodI-↑ {δ = δ ↑ᴵ e} (GoodI-↑ {δ = δ} g e) e″)
                  (IdI-↑ d (δ ↑ᴵ e) (IdI-↑ d δ h e) e″) ql qr r)))))

funStarId : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : Φ ⊢ A ⊑ ★) (q : Φ ⊢ B ⊑ ★)
  → (∀ {m} → m ≤ n → IdVp d m p) → (∀ {m} → m ≤ n → IdVp d m q)
  → ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI d w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → funStar d n p q w δ Vl Vr
  → funStar d n p q w δ (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) (A ⇒ B)) ⟩)
      Vr
funStarId d n p q rp rq w δ g h vl vr r =
  funStar-map (λ wr f → funId d n p q rp rq w δ g h vl wr f) vr r

------------------------------------------------------------------------
-- `∀` proxies
------------------------------------------------------------------------

-- a `∀` proxy's type application: `β-∀`, then the body's identity cast
tyAppId : ∀ d n′ {Δ₁ Δ₁′} {Φ₁ : Corr Δ₁ Δ₁′} {A B} (p : Φ₁ ⊢ A ⊑ B)
  → (∀ {m} → m ≤ n′ → IdVp d m p)
  → ∀ w (δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)) → GoodI δ₁ → IdI d w δ₁
  → ∀ {μ : Env∼ (ΔL w)} (A₁ : Ty (suc (ΔL w))) (T : Ty (ΔL w))
  → substᵗ (δl δ₁) A ≡ A₁ [ T ]ᵗ
  → ∀ {Vl Mr} → Value Vl
  → ℰ d n′ p w δ₁ (Vl ⦂∀ A₁ [ T ]) Mr
  → ℰ d n′ p w δ₁ ((Vl ⟨ refl∼ {μ = μ} (`∀ A₁) ⟩) ⦂∀ A₁ [ T ]) Mr
tyAppId d n′ {A = A} p rp w δ₁ g₁ h₁ {μ} A₁ T eqA vl inner =
  ℰ-stepL≤ d n′ p w (β-∀ vl (sym (refl-open A₁ T)))
    (λ {s} s≤ →
      ℰ-bind₂ d s p p w {δ₁ = δ₁} {δ₂ = δ₁}
        (just (cast (refl∼ {μ = μ} (A₁ [ T ]ᵗ)))) nothing
        (ℰ-down d s≤ p w g₁ inner)
        (λ e″ {k} k≤s {Ql} {Qr} ql qr r →
          ℰᵍ-≡
            (sym (ren-refl (ρL e″) Ql (A₁ [ T ]ᵗ)
              (trans (δ↑-ty δ₁ e″ A)
                (cong (renameᵗ (toRenameᵗ (ρL e″))) eqA))))
            refl
            (idE d k p (rp (≤-trans k≤s s≤)) _ (δ₁ ↑ᴵ e″)
              (GoodI-↑ {δ = δ₁} g₁ e″) (IdI-↑ d δ₁ h₁ e″) ql qr r)))

------------------------------------------------------------------------
-- The leaves the `∀` clauses build
------------------------------------------------------------------------

-- a descriptor's relation, at a stage, and by `G`
descV : Dir → ℕ → (w : World) → Desc (ΔL w) (ΔR w)
  → Term (ΔL w) → Term (storeR w) → Set
descV d k w (desc p env envR) = 𝒱 d k p w (envI env envR)

descGv : ℕ → (w : World) → Desc (ΔL w) (ΔR w)
  → Term (ΔL w) → Term (storeR w) → Set
descGv k w (desc p env envR) = G k p w (envI env envR)

-- the lemma on a descriptor's derivation, whose leaves are entries
descId : ∀ d k {w} (c : Desc (ΔL w) (ΔR w))
  → (∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) → IdVp d k p)
  → ∀ {T′} → T′ ≡ leftTy c
  → ∀ {μ : Env∼ (ΔL w)} {V V′} → Value V → Value V′
  → Inert (refl∼ {μ = μ} T′) → descV d k w c V V′
  → descV d k w c (V ⟨ refl∼ {μ = μ} T′ ⟩) V′
descId d k {w} (desc p env envR) iv refl {μ} vl vr i r =
  iv p w (envI env envR) (good-envI {env = env} {envR = envR})
    (IdI-envI d env envR) {μ = μ}
    vl vr i r

descGId : ∀ k {w} (c : Desc (ΔL w) (ΔR w))
  → (∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) → IdGp k p)
  → ∀ {T′} → T′ ≡ leftTy c
  → ∀ {μ : Env∼ (ΔL w)} {V V′} → Value V → Value V′
  → Inert (refl∼ {μ = μ} T′) → descGv k w c V V′
  → descGv k w c (V ⟨ refl∼ {μ = μ} T′ ⟩) V′
descGId k {w} (desc p env envR) ig refl {μ} vl vr i r =
  ig p w (envI env envR) (good-envI {env = env} {envR = envR})
    (IdI-envI ≻ env envR) {μ = μ}
    vl vr i r

-- right seals around a relation that the left cast keeps
peelSR-left : ∀ {Θ} (ι : Θ ↪ᵗ ΘR) (Ys : List (TyVar ΘR))
    (c : Desc ΘL ΘR) {P : Term ΘL → Term Θ → Set} {V V₁ : Term ΘL}
  → (∀ {V′} → Value V′ → P V V′ → P V₁ V′)
  → ∀ {V′} → Value V′ → peelSR ι Ys c P V V′ → peelSR ι Ys c P V₁ V′
peelSR-left ι [] c f v′ r = f v′ r
peelSR-left ι (Y ∷ Ys) c f (v CT.↓ cv) (is , r) =
  is , peelSR-left ι Ys c f v r
peelSR-left ι (Y ∷ Ys) c f (CT.ƛ N) ()
peelSR-left ι (Y ∷ Ys) c f (CT.Λ v) ()
peelSR-left ι (Y ∷ Ys) c f (CT.$ k) ()
peelSR-left ι (Y ∷ Ys) c f (v CT.《 i 》) ()
peelSR-left ι (Y ∷ Ys) c f (v CT.↑ rv) ()

leafBelow-id : ∀ d {n′ n} (le : n′ ≤′ n) (c : Desc ΘL ΘR) → Below d n′
  → ∀ k w τL τR {T′} → T′ ≡ renameᵗ (toRenameᵗ τL) (leftTy c)
  → ∀ {μ : Env∼ (ΔL w)} {V V′} → Value V → Value V′
  → Inert (refl∼ {μ = μ} T′) → leafBelow d le c k w τL τR V V′
  → leafBelow d le c k w τL τR (V ⟨ refl∼ {μ = μ} T′ ⟩) V′
leafBelow-id d {n′} le (desc p env envR) bv k w τL τR eq vl vr i r
    with suc k ≤? n′
leafBelow-id d {n′} le (desc p env envR) bv k w τL τR eq {μ} vl vr i r
    | yes lt =
  𝒱→𝒱< d lt′ p w
    (descId d k (renameDesc τL τR (desc p env envR)) (bv lt)
      (trans eq (sym (leftTy-rename τL τR (desc p env envR))))
      {μ = μ} vl vr i (𝒱<→𝒱 d lt′ p w r))
  where
  lt′ = ≤′-trans (≤⇒≤′ lt) le
leafBelow-id d {n′} le (desc p env envR) bv k w τL τR eq vl vr i ()
    | no _

leafG-id : ∀ {n′ n} (le : n′ ≤′ n) (c : Desc ΘL ΘR) → UpG n′
  → ∀ k w τL τR {T′} → T′ ≡ renameᵗ (toRenameᵗ τL) (leftTy c)
  → ∀ {μ : Env∼ (ΔL w)} {V V′} → Value V → Value V′
  → Inert (refl∼ {μ = μ} T′) → leafG le c k w τL τR V V′
  → leafG le c k w τL τR (V ⟨ refl∼ {μ = μ} T′ ⟩) V′
leafG-id {n′ = n′} le (desc p env envR) ug k w τL τR eq vl vr i r
    with k ≤? n′
leafG-id {n′ = n′} le (desc p env envR) ug k w τL τR eq {μ} vl vr i r
    | yes k≤ =
  G→G≤ (≤′-trans (≤⇒≤′ k≤) le) p w
    (descGId k (renameDesc τL τR (desc p env envR)) (ug k≤)
      (trans eq (sym (leftTy-rename τL τR (desc p env envR))))
      {μ = μ} vl vr i (G≤→G (≤′-trans (≤⇒≤′ k≤) le) p w r))
leafG-id {n′ = n′} le (desc p env envR) ug k w τL τR eq vl vr i ()
    | no _

-- a sealed left side is a store variable, whose identity cast is not
-- inert
leafBelowS-id : ∀ d {n′ n} (le : n′ ≤′ n) (c : SDesc ΘL ΘR)
  → Below d n′ → IdΩ d (leafBelowS d le c) (leftTyS c)
leafBelowS-id d le (sdesc (X ∷ Xs) Ys c) bv k w τL τR refl vl vr () r
leafBelowS-id d le (sdesc [] Ys c) bv k w τL τR eq {μ} vl vr i r =
  peelSR-left (ιʷ w) (map (renameVar τR) Ys) (renameDesc τL τR c)
    (λ v′ r′ → leafBelow-id d le c bv k w τL τR eq {μ = μ} vl v′ i r′)
    vr r

onlyLeafS-id : ∀ d {n′ n} (le : n′ ≤′ n) (c : SDesc ΘL ΘR)
  → Below d n′ → UpD d n′ → IdΩ d (onlyLeafS d le c) (leftTyS c)
onlyLeafS-id d le (sdesc (X ∷ Xs) Ys c) bv ud k w τL τR refl vl vr () r
onlyLeafS-id ≺ le (sdesc [] Ys c) bv ud k w τL τR eq {μ} vl vr i r =
  leafBelow-id ≺ le c bv k w τL τR eq {μ = μ} vl vr i r
onlyLeafS-id ≻ le (sdesc [] Ys c) bv ud k w τL τR eq {μ} vl vr i r =
  leafG-id le c ud k w τL τR eq {μ = μ} vl vr i r

allPairId : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p : pair Φ ⊢ A ⊑ B)
  → (∀ {m} → m ≤ n → IdVp d m p) → Below d n
  → ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI d w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → allPair d n p w δ Vl Vr
  → allPair d n p w δ (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) (`∀ A)) ⟩) Vr
allPairId d n {A = A} p rp bv w δ g h {μ} {Vl} {Vr} vl vr f
    {w′} e {n′} le c wf T₀ eqT B₀ eqB =
  ℰᵍ-≡
    (sym (cong (λ M → M ⦂∀ A₁ [ leftTyS c ])
      (ren-refl (ρL e) (renameᵗᵐ (ρL e) Vl) (substᵗ (δl δ) (`∀ A))
        (δ↑-ty δ e (`∀ A)))))
    refl
    (fromℰ d le p w′
      (tyAppId d n′ p (λ m≤ → rp (≤-trans m≤ (≤′⇒≤ le))) w′ δ₁
        (GoodI-extPairI {T = leftTyS c} {T′ = rightTyS c}
          {δ = δ ↑ᴵ e} (leafBelowS-good d le c)
          (GoodI-↑ {δ = δ} g e))
        (IdI-pair d {T′ = rightTyS c} {R = leafBelowS d le c}
          {δ = δ ↑ᴵ e} (leafBelowS-id d le c (Below-≤ d (≤′⇒≤ le) bv))
          (IdI-↑ d δ h e))
        A₁ (leftTyS c) (open-• (δl (δ ↑ᴵ e)) (leftTyS c) A)
        (renameᵗᵐ-preserves-Value (ρL e) vl)
        (toℰ d le p w′ (f e le c wf T₀ eqT B₀ eqB))))
  where
  A₁ = substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A
  δ₁ = extPairI (leftTyS c) (rightTyS c) (sem (leafBelowS d le c))
    (δ ↑ᴵ e)

allOnlyId : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p : only Φ ⊢ A ⊑ B)
  → (∀ {m} → m ≤ n → IdVp d m p) → Below d n → UpD d n
  → ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI d w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → allOnly d n p w δ Vl Vr
  → allOnly d n p w δ (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) (`∀ A)) ⟩) Vr
allOnlyId d n {A = A} p rp bv ud w δ g h {μ} {Vl} {Vr} vl vr f
    {w′} e {n′} le c oc =
  ℰᵍ-≡
    (sym (cong (λ M → M ⦂∀ A₁ [ leftTyS c ])
      (ren-refl (ρL e) (renameᵗᵐ (ρL e) Vl) (substᵗ (δl δ) (`∀ A))
        (δ↑-ty δ e (`∀ A)))))
    refl
    (fromℰ d le p w′
      (tyAppId d n′ p (λ m≤ → rp (≤-trans m≤ (≤′⇒≤ le))) w′ δ₁
        (GoodI-extOnlyI {T = leftTyS c} {δ = δ ↑ᴵ e} (onlyLeafS-good d le c)
          (GoodI-↑ {δ = δ} g e))
        (IdI-only d {R = onlyLeafS d le c} {δ = δ ↑ᴵ e}
          (onlyLeafS-id d le c (Below-≤ d (≤′⇒≤ le) bv)
            (UpD-≤ d (≤′⇒≤ le) ud))
          (IdI-↑ d δ h e))
        A₁ (leftTyS c) (open-• (δl (δ ↑ᴵ e)) (leftTyS c) A)
        (renameᵗᵐ-preserves-Value (ρL e) vl)
        (toℰ d le p w′ (f e le c oc))))
  where
  A₁ = substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A
  δ₁ = extOnlyI (leftTyS c) (sem (onlyLeafS d le c)) (δ ↑ᴵ e)

allDeadId : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A} (p : dead Φ ⊢ A ⊑ ★)
  → (∀ {m} → m ≤ n → IdVp d m p)
  → ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI d w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Wr} → Value Vl
  → allDead d n p w δ Vl Wr
  → allDead d n p w δ (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) (`∀ A)) ⟩) Wr
allDeadId d n {A = A} p rp w δ g h {μ} {Vl} {Wr} vl f
    {w′} e {n′} le T T′ =
  ℰᵍ-≡
    (sym (cong (λ M → M ⦂∀ A₁ [ T ])
      (ren-refl (ρL e) (renameᵗᵐ (ρL e) Vl) (substᵗ (δl δ) (`∀ A))
        (δ↑-ty δ e (`∀ A)))))
    refl
    (fromℰ d le p w′
      (tyAppId d n′ p (λ m≤ → rp (≤-trans m≤ (≤′⇒≤ le))) w′
        (extDeadI T (δ ↑ᴵ e))
        (GoodI-extDeadI {T = T} {δ = δ ↑ᴵ e} (GoodI-↑ {δ = δ} g e))
        (IdI-dead d {T = T} {δ = δ ↑ᴵ e} (IdI-↑ d δ h e))
        A₁ T (open-• (δl (δ ↑ᴵ e)) T A)
        (renameᵗᵐ-preserves-Value (ρL e) vl)
        (toℰ d le p w′ (f e le T T′))))
  where
  A₁ = substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A

allDeadStarId : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A} (p : dead Φ ⊢ A ⊑ ★)
  → (∀ {m} → m ≤ n → IdVp d m p)
  → ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI d w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → allDeadStar d n p w δ Vl Vr
  → allDeadStar d n p w δ
      (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) (`∀ A)) ⟩) Vr
allDeadStarId d n p rp w δ g h vl (v CT.《 i 》) (inj , f) =
  inj , allDeadId d n p rp w δ g h vl f
allDeadStarId d n p rp w δ g h vl (CT.ƛ N) ()
allDeadStarId d n p rp w δ g h vl (CT.Λ v) ()
allDeadStarId d n p rp w δ g h vl (CT.$ k) ()
allDeadStarId d n p rp w δ g h vl (v CT.↑ rv) ()
allDeadStarId d n p rp w δ g h vl (v CT.↓ cv) ()

-- `∀★` against the right's `∀★` payload
allStarId : ∀ d n w {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → allStar d n w Vl Vr
  → allStar d n w (Vl ⟨ ∀ᶜ (id {μ = extᵐ μ} ★) ⟩) Vr
allStarId d n w {μ} {Vl} vl (v CT.《 i 》) (inj , f) =
  inj , λ {w′} e {n′} le T T′ →
    starFrom d le w′
      (ℰ-stepL≤ d n′ ★⊑★ w′
        (β-∀ (renameᵗᵐ-preserves-Value (ρL e) vl) refl)
        (λ {s} s≤ →
          ℰ-bind₂ d s ★⊑★ ★⊑★ w′ {δ₁ = closedI} {δ₂ = closedI}
            (just (cast (id {μ = renameEnv∼ (ρL e) μ} ★))) nothing
            (ℰ-down d s≤ ★⊑★ w′ good-closedI
              (starTo d le w′ (f e le T T′)))
            (λ e″ k≤s ql qr r →
              ℰ-steps? d _ ★⊑★ _ (GoodI-↑ {δ = closedI} good-closedI e″)
                (step (β-id ql)) stay ql qr r)))
allStarId d n w vl (CT.ƛ N) ()
allStarId d n w vl (CT.Λ v) ()
allStarId d n w vl (CT.$ k) ()
allStarId d n w vl (v CT.↑ rv) ()
allStarId d n w vl (v CT.↓ cv) ()

------------------------------------------------------------------------
-- The lemma, by induction on the derivation within a stage
------------------------------------------------------------------------

-- `G` at stage N: its content is read below N, or is a leaf
idG : ∀ N → Below ≻ N → BelowG N → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
  (p : Φ ⊢ A ⊑ A′) → IdGp N p
idG zero bv bg p w δ g h vl vr i r = tt
idG (suc k) bv bg ★⊑★ w δ g h vl vr () r
idG (suc k) bv bg ι⊑ι w δ g h vl vr () r
idG (suc k) bv bg (X⊑Y x) w δ g h {μ} vl vr i r =
  bv ≤-refl (X⊑Y x) w δ g h {μ = μ} vl vr i r
idG (suc k) bv bg (⇒⊑⇒ p q) w δ g h {μ} vl vr i r =
  bv ≤-refl (⇒⊑⇒ p q) w δ g h {μ = μ} vl vr i r
idG (suc k) bv bg (∀⊑∀ p) w δ g h {μ} vl vr i r =
  bv ≤-refl (∀⊑∀ p) w δ g h {μ = μ} vl vr i r
idG (suc k) bv bg (⇒⊑★ p q) w δ g h {μ} vl vr i r =
  funStarId ≻ k p q (λ m≤ → bv (s≤s m≤) p) (λ m≤ → bv (s≤s m≤) q)
    w δ g h {μ = μ} vl vr r
idG (suc k) bv bg ι⊑★ w δ g h vl vr () r
idG (suc k) bv bg (X⊑★ {X = X} o) w δ g h {μ} vl vr i r =
  IdI-now ≻ δ h X (suc k) {μ = μ} vl vr i r
idG (suc k) bv bg (∀⊑ {B = ★} Anv z p) w δ g h {μ} vl vr i r =
  allOnlyId ≻ k p (λ m≤ → bv (s≤s m≤) p) (Below-≤ ≻ (n≤1+n k) bv)
    (λ m≤ → bg (s≤s m≤)) w δ g h {μ = μ} vl vr r
idG (suc k) bv bg (∀⊑ {B = ＇ Y} Anv z p) w δ g h {μ} vl vr i r =
  bv ≤-refl (∀⊑ Anv z p) w δ g h {μ = μ} vl vr i r
idG (suc k) bv bg (∀⊑ {B = ‵ ι} Anv z p) w δ g h {μ} vl vr i r =
  bv ≤-refl (∀⊑ Anv z p) w δ g h {μ = μ} vl vr i r
idG (suc k) bv bg (∀⊑ {B = B ⇒ C} Anv z p) w δ g h {μ} vl vr i r =
  bv ≤-refl (∀⊑ Anv z p) w δ g h {μ = μ} vl vr i r
idG (suc k) bv bg (∀⊑ {B = `∀ B} Anv z p) w δ g h {μ} vl vr i r =
  bv ≤-refl (∀⊑ Anv z p) w δ g h {μ = μ} vl vr i r
idG (suc k) bv bg ∀★⊑★ w δ g h {μ} vl vr i r =
  allStarId ≻ k w {μ = μ} vl vr r
idG (suc k) bv bg (∀⊑★ ns p) w δ g h {μ} vl vr i r =
  allDeadStarId ≻ k p (λ m≤ → bv (s≤s m≤) p) w δ g h {μ = μ} vl vr r
idG (suc k) bv bg bot-elim w δ g h vl vr i ()
idG (suc k) bv bg bot⊑★ w δ g h vl vr i ()

-- a stage up to N is below N or is N
≤-split : ∀ {k N} → k ≤ N → k < N ⊎ k ≡ N
≤-split {zero} {zero} z≤n = inj₂ refl
≤-split {zero} {suc N} z≤n = inj₁ (s≤s z≤n)
≤-split {suc k} {suc N} (s≤s le) with ≤-split le
≤-split {suc k} {suc N} (s≤s le) | inj₁ lt = inj₁ (s≤s lt)
≤-split {suc k} {suc N} (s≤s le) | inj₂ refl = inj₂ refl

upG : ∀ N → Below ≻ N → BelowG N → UpG N
upG N bv bg k≤N p with ≤-split k≤N
upG N bv bg k≤N p | inj₁ lt = bg lt p
upG N bv bg k≤N p | inj₂ refl = idG N bv bg p

upD : ∀ d N → Below d N → BG d N → UpD d N
upD ≺ N bv bg = tt₁
upD ≻ N bv bg = upG N bv bg

-- the inert case at stage n, from the stages below
idV : ∀ d n → Below d n → BG d n → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
  (p : Φ ⊢ A ⊑ A′) → IdVp d n p
idV d n bv bg ★⊑★ w δ g h vl vr () r
idV d n bv bg ι⊑ι w δ g h vl vr () r
idV ≺ n bv bg (X⊑Y {X = X} x) w δ g h {μ} vl vr i r =
  IdI-now ≺ δ h X n {μ = μ} vl vr i r
idV ≻ n bv bg (X⊑Y {X = X} x) w δ g h {μ} vl vr i r =
  IdI-now ≻ δ h X n {μ = μ} vl vr i r
idV ≺ n bv bg (⇒⊑⇒ p q) w δ g h {μ} vl vr i r =
  funId ≺ n p q
    (λ m≤ → idV ≺ _ (Below-≤ ≺ m≤ bv) (BG-≤ ≺ m≤ bg) p)
    (λ m≤ → idV ≺ _ (Below-≤ ≺ m≤ bv) (BG-≤ ≺ m≤ bg) q)
    w δ g h {μ = μ} vl vr r
idV ≻ n bv bg (⇒⊑⇒ p q) w δ g h {μ} vl vr i r =
  funId ≻ n p q
    (λ m≤ → idV ≻ _ (Below-≤ ≻ m≤ bv) (BG-≤ ≻ m≤ bg) p)
    (λ m≤ → idV ≻ _ (Below-≤ ≻ m≤ bv) (BG-≤ ≻ m≤ bg) q)
    w δ g h {μ = μ} vl vr r
idV ≺ n bv bg (∀⊑∀ p) w δ g h {μ} vl vr i r =
  allPairId ≺ n p (λ m≤ → idV ≺ _ (Below-≤ ≺ m≤ bv) (BG-≤ ≺ m≤ bg) p)
    bv w δ g h {μ = μ} vl vr r
idV ≻ n bv bg (∀⊑∀ p) w δ g h {μ} vl vr i r =
  allPairId ≻ n p (λ m≤ → idV ≻ _ (Below-≤ ≻ m≤ bv) (BG-≤ ≻ m≤ bg) p)
    bv w δ g h {μ = μ} vl vr r
idV ≺ n bv bg (⇒⊑★ p q) w δ g h {μ} vl vr i r =
  funStarId ≺ n p q
    (λ m≤ → idV ≺ _ (Below-≤ ≺ m≤ bv) tt₁ p)
    (λ m≤ → idV ≺ _ (Below-≤ ≺ m≤ bv) tt₁ q)
    w δ g h {μ = μ} vl vr r
idV ≻ n bv bg (⇒⊑★ p q) w δ g h {μ} vl vr i r =
  idG n bv bg (⇒⊑★ p q) w δ g h {μ = μ} vl vr i r
idV d n bv bg ι⊑★ w δ g h vl vr () r
idV ≺ n bv bg (X⊑★ {X = X} o) w δ g h {μ} vl vr i r =
  IdI-now ≺ δ h X n {μ = μ} vl vr i r
idV ≻ n bv bg (X⊑★ {X = X} o) w δ g h {μ} vl vr i r =
  IdI-now ≻ δ h X n {μ = μ} vl vr i r
idV ≺ n bv bg (∀⊑ Anv z p) w δ g h {μ} vl vr i r =
  allOnlyId ≺ n p (λ m≤ → idV ≺ _ (Below-≤ ≺ m≤ bv) tt₁ p) bv tt₁
    w δ g h {μ = μ} vl vr r
idV ≻ n bv bg (∀⊑ {B = ★} Anv z p) w δ g h {μ} vl vr i r =
  idG n bv bg (∀⊑ Anv z p) w δ g h {μ = μ} vl vr i r
idV ≻ n bv bg (∀⊑ {B = ＇ Y} Anv z p) w δ g h {μ} vl vr i r =
  allOnlyId ≻ n p (λ m≤ → idV ≻ _ (Below-≤ ≻ m≤ bv) (BG-≤ ≻ m≤ bg) p)
    bv (upG n bv bg) w δ g h {μ = μ} vl vr r
idV ≻ n bv bg (∀⊑ {B = ‵ ι} Anv z p) w δ g h {μ} vl vr i r =
  allOnlyId ≻ n p (λ m≤ → idV ≻ _ (Below-≤ ≻ m≤ bv) (BG-≤ ≻ m≤ bg) p)
    bv (upG n bv bg) w δ g h {μ = μ} vl vr r
idV ≻ n bv bg (∀⊑ {B = B ⇒ C} Anv z p) w δ g h {μ} vl vr i r =
  allOnlyId ≻ n p (λ m≤ → idV ≻ _ (Below-≤ ≻ m≤ bv) (BG-≤ ≻ m≤ bg) p)
    bv (upG n bv bg) w δ g h {μ = μ} vl vr r
idV ≻ n bv bg (∀⊑ {B = `∀ B} Anv z p) w δ g h {μ} vl vr i r =
  allOnlyId ≻ n p (λ m≤ → idV ≻ _ (Below-≤ ≻ m≤ bv) (BG-≤ ≻ m≤ bg) p)
    bv (upG n bv bg) w δ g h {μ = μ} vl vr r
idV ≺ n bv bg ∀★⊑★ w δ g h {μ} vl vr i r =
  allStarId ≺ n w {μ = μ} vl vr r
idV ≻ n bv bg ∀★⊑★ w δ g h {μ} vl vr i r =
  idG n bv bg ∀★⊑★ w δ g h {μ = μ} vl vr i r
idV ≺ n bv bg (∀⊑★ ns p) w δ g h {μ} vl vr i r =
  allDeadStarId ≺ n p (λ m≤ → idV ≺ _ (Below-≤ ≺ m≤ bv) tt₁ p)
    w δ g h {μ = μ} vl vr r
idV ≻ n bv bg (∀⊑★ ns p) w δ g h {μ} vl vr i r =
  idG n bv bg (∀⊑★ ns p) w δ g h {μ = μ} vl vr i r
idV ≺ n bv bg bot-elim w δ g h vl vr i ()
idV ≻ n bv bg bot-elim w δ g h vl vr i ()
idV ≺ n bv bg bot⊑★ w δ g h vl vr i ()
idV ≻ n bv bg bot⊑★ w δ g h vl vr i ()

------------------------------------------------------------------------
-- Every stage
------------------------------------------------------------------------

extB : ∀ d N → Below d N
  → (∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) → IdVp d N p)
  → Below d (suc N)
extB d N bv iv (s≤s k≤N) p with ≤-split k≤N
extB d N bv iv (s≤s k≤N) p | inj₁ lt = bv lt p
extB d N bv iv (s≤s k≤N) p | inj₂ refl = iv p

extG : ∀ N → BelowG N
  → (∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) → IdGp N p)
  → BelowG (suc N)
extG N bg ig (s≤s k≤N) p with ≤-split k≤N
extG N bg ig (s≤s k≤N) p | inj₁ lt = bg lt p
extG N bg ig (s≤s k≤N) p | inj₂ refl = ig p

ora : ∀ d N → Below d N × BG d N
ora ≺ zero = (λ ()) , tt₁
ora ≻ zero = (λ ()) , (λ ())
ora ≺ (suc N) =
  extB ≺ N (proj₁ (ora ≺ N)) (idV ≺ N (proj₁ (ora ≺ N)) tt₁) , tt₁
ora ≻ (suc N) =
  extB ≻ N bv (idV ≻ N bv bg) , extG N bg (idG N bv bg)
  where
  bv = proj₁ (ora ≻ N)
  bg = proj₂ (ora ≻ N)

-- The identity-cast lemma: under an interpretation whose leaves are
-- closed under identity casts, values related at p stay related after
-- the left is cast by `refl∼` of p's left type.
identityCast : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′)
  → ∀ w (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ → IdI d w δ
  → ∀ {μ : Env∼ (ΔL w)} {Vl Vr} → Value Vl → Value Vr
  → 𝒱 d n p w δ Vl Vr
  → ℰ d n p w δ (Vl ⟨ refl∼ {μ = μ} (substᵗ (δl δ) A) ⟩) Vr
identityCast d n p =
  idE d n p (idV d n (proj₁ (ora d n)) (proj₂ (ora d n)) p)

-- the leaves of the clauses are closed, at every bound
leafBelowS-closed : ∀ d {n′ n} (le : n′ ≤′ n) (c : SDesc ΘL ΘR)
  → IdΩ d (leafBelowS d le c) (leftTyS c)
leafBelowS-closed d {n′} le c = leafBelowS-id d le c (proj₁ (ora d n′))

onlyLeafS-closed : ∀ d {n′ n} (le : n′ ≤′ n) (c : SDesc ΘL ΘR)
  → IdΩ d (onlyLeafS d le c) (leftTyS c)
onlyLeafS-closed d {n′} le c =
  onlyLeafS-id d le c (proj₁ (ora d n′))
    (upD d n′ (proj₁ (ora d n′)) (proj₂ (ora d n′)))

------------------------------------------------------------------------
-- The cast lemma's base case at a left-only variable
------------------------------------------------------------------------

-- the value relation at a left-only variable is its leaf
X★→leaf : ∀ d k {Δ Δ′} {Φ : Corr Δ Δ′} {Z} (o : Φ ∋ Z only) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → 𝒱 d k (X⊑★ o) w δ Vl Vr → leafRel d k w (leaf δ Z) Vl Vr
X★→leaf ≺ k o w r = r
X★→leaf ≻ k o w r = r

leaf→X★ : ∀ d k {Δ Δ′} {Φ : Corr Δ Δ′} {Z} (o : Φ ∋ Z only) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → leafRel d k w (leaf δ Z) Vl Vr → 𝒱 d k (X⊑★ o) w δ Vl Vr
leaf→X★ ≺ k o w r = r
leaf→X★ ≻ k o w r = r

-- `VarI.selfO`, when the variable's world cast is `refl∼` of its left
-- type and its leaf is closed under identity casts
selfO : ∀ d k {Δ Δ′} {Φ : Corr Δ Δ′} {Z} (o : Φ ∋ Z only) w
    (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ
  → IdLeaf d w (leaf δ Z) (δl δ Z)
  → ∀ {μ : Env∼ (ΔL w)} {μ′ : Env∼ (storeR w)}
  → CastRel d k (X⊑★ o) (X⊑★ o) w δ (λ V → V ⟨ refl∼ {μ = μ} (δl δ Z) ⟩)
      (λ V → V ⟨ id {μ = μ′} ★ ⟩)
selfO d k {Z = Z} o w δ g hZ {μ} {μ′} {Vl} {Vr} vl vr r
    with reflShape {μ = μ} (δl δ Z)
selfO d k {Z = Z} o w δ g hZ {μ} {μ′} {Vl} {Vr} vl vr r
    | inj₁ (a , eq) =
  subst (λ c → ℰ d k (X⊑★ o) w δ (Vl ⟨ c ⟩) (Vr ⟨ id {μ = μ′} ★ ⟩))
    (sym eq)
    (ℰ-steps? d k (X⊑★ o) w g (step (β-id vl)) (step (β-id vr)) vl vr r)
selfO d k {Z = Z} o w δ g hZ {μ} {μ′} {Vl} {Vr} vl vr r | inj₂ i =
  ℰ-steps? d k (X⊑★ o) w g stay (step (β-id vr)) (vl CT.《 i 》) vr
    (leaf→X★ d k o w (hZ k {μ = μ} vl vr i (X★→leaf d k o w r)))

-- Case 6's new variable: a left-only clause's variable, at the
-- clause's leaf for a sealed descriptor c, read in a future w″
selfO-only : ∀ d k {Δ Δ′} {Φ : Corr Δ Δ′} {n′ n} (le : n′ ≤′ n) {w}
    (c : SDesc (ΔL w) (ΔR w)) (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → GoodI δ
  → ∀ {w″} (e″ : w″ ⊒ w) {μ : Env∼ (ΔL w″)} {μ′ : Env∼ (storeR w″)}
  → CastRel d k (X⊑★ (only-here {Φ = Φ})) (X⊑★ only-here) w″
      (extOnlyI (leftTyS c) (sem (onlyLeafS d le c)) δ ↑ᴵ e″)
      (λ V → V ⟨ refl∼ {μ = μ} (renameᵗ (toRenameᵗ (ρL e″)) (leftTyS c))
        ⟩)
      (λ V → V ⟨ id {μ = μ′} ★ ⟩)
selfO-only d k le {w} c δ g {w″} e″ =
  selfO d k only-here w″ (extOnlyI (leftTyS c) (sem (onlyLeafS d le c)) δ
    ↑ᴵ e″)
    (GoodI-↑ {δ = extOnlyI (leftTyS c) (sem (onlyLeafS d le c)) δ}
      (GoodI-extOnlyI {T = leftTyS c} {δ = δ} (onlyLeafS-good d le c) g)
      e″)
    (IdLeaf-transport d (onlyLeafS-closed d le c) w″ (ρL e″) (ρR e″))
