module proof.LR.Monotone where

-- File Charter:
--   * Kripke monotonicity and downward closure of the value relation
--     (notes/logrel-dgg.md, Section 6.9, lemma 2; Section 7).
--   * Monotonicity: values related in a world stay related, renamed, in
--     every future world under the transported interpretation.  The
--     function and `∀` clauses are monotone by their own quantification
--     over futures; `★`, tags, entries and contents by induction on the
--     stage and the left term, following the definitions.
--   * Downward closure: values related at a stage are related at every
--     lower stage.
--   * Both need the semantic leaves of the interpretation to be monotone
--     and downward closed (`GoodI`).  The leaves the relation builds
--     itself (`leafBelow`, `leafG`, `⊤Ω`) are, by these lemmas at lower
--     stages on the descriptors' own interpretations, which have no
--     semantic leaves.
--   * The absurd clauses spell out the catch-all clauses of the
--     definitions, one per term or cast constructor.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≤′_; ≤′-refl;
  ≤′-step; _≤?_)
open import Data.Nat.Properties using (≤⇒≤′; ≤-trans)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
import Data.Vec as Vec
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using (Env∼; _‼_; _⊢_∼_; id; _↦_; ∀ᶜ_; _!; ？_;
  inst_; gen_; bot-elim; bot-intro; rename∼; renameGround; _↪ᵗ_;
  toRenameᵗ; id↪ᵗ)
open import Conversion using (Conv↓; seal; _↦↓_; `∀↓_; id↓; rename↓)
open import CastTerms using (Term; renameᵗᵐ; `_; ƛ_; _·_; Λ_; _⦂∀_[_];
  $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame)
open import proof.DGG.CenterRename using (_∘↪_)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import proof.TermRename using (renameᵗᵐ-∘)
open import proof.LR.WorldProps
open import proof.LR.InterpProps

private
  variable
    Δ Δ′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- Shapes under renaming
------------------------------------------------------------------------

IsSeal-rename : ∀ {A B : Ty Δ} (σ : Δ ⇒ʳ Δ′) {X R R′} (s : Conv↓ Δ A B)
  → R′ ≡ renameᵗ σ R → IsSeal X R s → IsSeal (σ X) R′ (rename↓ σ s)
IsSeal-rename σ (seal X′ R₀) eq (refl , refl) = refl , sym eq
IsSeal-rename σ (c ↦↓ d) eq ()
IsSeal-rename σ (`∀↓ c) eq ()
IsSeal-rename σ (id↓ A) eq ()

IsInjVar-rename : ∀ {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B : Ty Δ}
    (ρ : Δ ⇒ʳ Δ′) (eq : ∀ X → μ′ ‼ (ρ X) ≡ μ ‼ X) {X} (c : μ ⊢ A ∼ B)
  → IsInjVar X c → IsInjVar (ρ X) (rename∼ {μ′ = μ′} ρ eq c)
IsInjVar-rename ρ eq (_! ⦃ Gᵍ = ＇ Y ⦄ c) refl = refl
IsInjVar-rename ρ eq (id a₀) ()
IsInjVar-rename ρ eq (c₀ ↦ d₀) ()
IsInjVar-rename ρ eq (∀ᶜ c₀) ()
IsInjVar-rename ρ eq (？ c₀) ()
IsInjVar-rename ρ eq (inst_ c₀ h₀) ()
IsInjVar-rename ρ eq (gen_ c₀ h₀) ()
IsInjVar-rename ρ eq (bot-elim) ()
IsInjVar-rename ρ eq (bot-intro) ()
IsInjVar-rename ρ eq (_! ⦃ Gᵍ = ‵ ι₀ ⦄ c₀) ()
IsInjVar-rename ρ eq (_! ⦃ Gᵍ = ★⇒★ ⦄ c₀) ()
IsInjVar-rename ρ eq (_! ⦃ Gᵍ = ∀★ ⦄ c₀) ()

IsInjBase-rename : ∀ {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B : Ty Δ}
    (ρ : Δ ⇒ʳ Δ′) (eq : ∀ X → μ′ ‼ (ρ X) ≡ μ ‼ X) {ι} (c : μ ⊢ A ∼ B)
  → IsInjBase ι c → IsInjBase ι (rename∼ {μ′ = μ′} ρ eq c)
IsInjBase-rename ρ eq (_! ⦃ Gᵍ = ‵ ι′ ⦄ c) refl = refl
IsInjBase-rename ρ eq (id a₀) ()
IsInjBase-rename ρ eq (c₀ ↦ d₀) ()
IsInjBase-rename ρ eq (∀ᶜ c₀) ()
IsInjBase-rename ρ eq (？ c₀) ()
IsInjBase-rename ρ eq (inst_ c₀ h₀) ()
IsInjBase-rename ρ eq (gen_ c₀ h₀) ()
IsInjBase-rename ρ eq (bot-elim) ()
IsInjBase-rename ρ eq (bot-intro) ()
IsInjBase-rename ρ eq (_! ⦃ Gᵍ = ＇ Y₀ ⦄ c₀) ()
IsInjBase-rename ρ eq (_! ⦃ Gᵍ = ★⇒★ ⦄ c₀) ()
IsInjBase-rename ρ eq (_! ⦃ Gᵍ = ∀★ ⦄ c₀) ()

IsInj⇒-rename : ∀ {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B : Ty Δ}
    (ρ : Δ ⇒ʳ Δ′) (eq : ∀ X → μ′ ‼ (ρ X) ≡ μ ‼ X) (c : μ ⊢ A ∼ B)
  → IsInj⇒ c → IsInj⇒ (rename∼ {μ′ = μ′} ρ eq c)
IsInj⇒-rename ρ eq (_! ⦃ Gᵍ = ★⇒★ ⦄ c) tt = tt
IsInj⇒-rename ρ eq (id a₀) ()
IsInj⇒-rename ρ eq (c₀ ↦ d₀) ()
IsInj⇒-rename ρ eq (∀ᶜ c₀) ()
IsInj⇒-rename ρ eq (？ c₀) ()
IsInj⇒-rename ρ eq (inst_ c₀ h₀) ()
IsInj⇒-rename ρ eq (gen_ c₀ h₀) ()
IsInj⇒-rename ρ eq (bot-elim) ()
IsInj⇒-rename ρ eq (bot-intro) ()
IsInj⇒-rename ρ eq (_! ⦃ Gᵍ = ＇ Y₀ ⦄ c₀) ()
IsInj⇒-rename ρ eq (_! ⦃ Gᵍ = ‵ ι₀ ⦄ c₀) ()
IsInj⇒-rename ρ eq (_! ⦃ Gᵍ = ∀★ ⦄ c₀) ()

IsInj∀-rename : ∀ {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B : Ty Δ}
    (ρ : Δ ⇒ʳ Δ′) (eq : ∀ X → μ′ ‼ (ρ X) ≡ μ ‼ X) (c : μ ⊢ A ∼ B)
  → IsInj∀ c → IsInj∀ (rename∼ {μ′ = μ′} ρ eq c)
IsInj∀-rename ρ eq (_! ⦃ Gᵍ = ∀★ ⦄ c) tt = tt
IsInj∀-rename ρ eq (id a₀) ()
IsInj∀-rename ρ eq (c₀ ↦ d₀) ()
IsInj∀-rename ρ eq (∀ᶜ c₀) ()
IsInj∀-rename ρ eq (？ c₀) ()
IsInj∀-rename ρ eq (inst_ c₀ h₀) ()
IsInj∀-rename ρ eq (gen_ c₀ h₀) ()
IsInj∀-rename ρ eq (bot-elim) ()
IsInj∀-rename ρ eq (bot-intro) ()
IsInj∀-rename ρ eq (_! ⦃ Gᵍ = ＇ Y₀ ⦄ c₀) ()
IsInj∀-rename ρ eq (_! ⦃ Gᵍ = ‵ ι₀ ⦄ c₀) ()
IsInj∀-rename ρ eq (_! ⦃ Gᵍ = ★⇒★ ⦄ c₀) ()

modeOf-map : ∀ {ΘR ΘR′} d (f : TyVar ΘR → TyVar ΘR′) (Ys : List (TyVar ΘR))
  → modeOf d (map f Ys) ≡ modeOf d Ys
modeOf-map ≺ f Ys = refl
modeOf-map ≻ f [] = refl
modeOf-map ≻ f (Y ∷ Ys) = refl

------------------------------------------------------------------------
-- The interpretations of descriptors and of closed derivations
------------------------------------------------------------------------

envI-transport : ∀ {ΘL′ ΘR′} (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′)
    (env : Vec (Entry ΘL ΘR) Δ) (envR : Vec (Ty ΘR) Δ′)
  → transportI σL σR (envI env envR)
    ≈ᴵ envI (renameEntries σL σR env)
         (Vec.map (renameᵗ (toRenameᵗ σR)) envR)
δl≡ (envI-transport σL σR env envR) X =
  sym (trans (cong entryTy (lookup-renameEntries σL σR env X))
             (entryTy-rename σL σR (lookup env X)))
δr≡ (envI-transport σL σR env envR) Y =
  sym (lookup-map Y (renameᵗ (toRenameᵗ σR)) envR)
leaf≈ (envI-transport σL σR env envR) X =
  syn≈ (sym (lookup-renameEntries σL σR env X))

closedI-transport : ∀ {ΘL′ ΘR′} (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′)
  → transportI σL σR closedI ≈ᴵ closedI
δl≡ (closedI-transport σL σR) ()
δr≡ (closedI-transport σL σR) ()
leaf≈ (closedI-transport σL σR) ()

------------------------------------------------------------------------
-- Good leaves: monotone and downward closed
------------------------------------------------------------------------

MonoΩ : RelΩ ΘL ΘR → Set
MonoΩ R = ∀ k w τL τR {w′} (e : w′ ⊒ w) {V V′}
  → R k w τL τR V V′
  → R k w′ (ρL e ∘↪ τL) (ρR e ∘↪ τR)
      (renameᵗᵐ (ρL e) V) (renameᵗᵐ (ρR e) V′)

DownΩ : RelΩ ΘL ΘR → Set
DownΩ R = ∀ {k k′} → k′ ≤ k → ∀ w τL τR {V V′}
  → R k w τL τR V V′ → R k′ w τL τR V V′

data GoodLeaf {ΘL ΘR} : Leaf ΘL ΘR → Set₁ where
  good-syn : ∀ {en} → GoodLeaf (syn en)
  good-sem : ∀ {R} → MonoΩ R → DownΩ R → GoodLeaf (sem R)

GoodI : Interp Δ Δ′ ΘL ΘR → Set₁
GoodI δ = ∀ X → GoodLeaf (leaf δ X)

good-envI : ∀ {env : Vec (Entry ΘL ΘR) Δ} {envR : Vec (Ty ΘR) Δ′}
  → GoodI (envI env envR)
good-envI X = good-syn

good-closedI : GoodI (closedI {ΘL} {ΘR})
good-closedI ()

------------------------------------------------------------------------
-- Stage-bounded helpers depend only on the stage
------------------------------------------------------------------------

𝒱≤-cast : ∀ d {m a b} (le₁ : m ≤′ a) (le₂ : m ≤′ b) {Φ : Corr Δ Δ′}
    {A A′} (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → 𝒱≤ d le₁ p w δ V V′ → 𝒱≤ d le₂ p w δ V V′
𝒱≤-cast d (≤′-step le₁) le₂ p w r = 𝒱≤-cast d le₁ le₂ p w r
𝒱≤-cast d ≤′-refl (≤′-step le₂) p w r = 𝒱≤-cast d ≤′-refl le₂ p w r
𝒱≤-cast d ≤′-refl ≤′-refl p w r = r

𝒱<→𝒱 : ∀ d {m n} (lt : suc m ≤′ n) {Φ : Corr Δ Δ′} {A A′}
    (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → 𝒱< d lt p w δ V V′ → 𝒱 d m p w δ V V′
𝒱<→𝒱 d ≤′-refl p w r = r
𝒱<→𝒱 d (≤′-step lt) p w r = 𝒱<→𝒱 d lt p w r

𝒱→𝒱< : ∀ d {m n} (lt : suc m ≤′ n) {Φ : Corr Δ Δ′} {A A′}
    (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → 𝒱 d m p w δ V V′ → 𝒱< d lt p w δ V V′
𝒱→𝒱< d ≤′-refl p w r = r
𝒱→𝒱< d (≤′-step lt) p w r = 𝒱→𝒱< d lt p w r

G≤→G : ∀ {m n} (le : m ≤′ n) {Φ : Corr Δ Δ′} {A A′}
    (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → G≤ le p w δ V V′ → G m p w δ V V′
G≤→G ≤′-refl p w r = r
G≤→G (≤′-step le) p w r = G≤→G le p w r

G→G≤ : ∀ {m n} (le : m ≤′ n) {Φ : Corr Δ Δ′} {A A′}
    (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → G m p w δ V V′ → G≤ le p w δ V V′
G→G≤ ≤′-refl p w r = r
G→G≤ (≤′-step le) p w r = G→G≤ le p w r

starAt-cast : ∀ d {m a b} (le₁ : m ≤′ a) (le₂ : m ≤′ b) w {V V′}
  → starAt d le₁ w V V′ → starAt d le₂ w V V′
starAt-cast ≺ (≤′-step le₁) le₂ w r = starAt-cast ≺ le₁ le₂ w r
starAt-cast ≺ ≤′-refl (≤′-step le₂) w r = starAt-cast ≺ ≤′-refl le₂ w r
starAt-cast ≺ ≤′-refl ≤′-refl w r = r
starAt-cast ≻ (≤′-step le₁) le₂ w r = starAt-cast ≻ le₁ le₂ w r
starAt-cast ≻ ≤′-refl (≤′-step le₂) w r = starAt-cast ≻ ≤′-refl le₂ w r
starAt-cast ≻ ≤′-refl ≤′-refl w r = r

-- the semantic leaves depend on the bound, not on its proof
leafBelow-≈ : ∀ d {n′ a b} (le₁ : n′ ≤′ a) (le₂ : n′ ≤′ b)
    (c : Desc ΘL ΘR)
  → sem (leafBelow d le₁ c) ≈ˡ sem (leafBelow d le₂ c)
leafBelow-≈ d {n′} le₁ le₂ c = sem≈ (to le₁ le₂) (to le₂ le₁)
  where
  cast : ∀ {m x y} (lt₁ : suc m ≤′ x) (lt₂ : suc m ≤′ y) w
      (c′ : Desc (ΔL w) (ΔR w)) {V V′}
    → descBelow d lt₁ w c′ V V′ → descBelow d lt₂ w c′ V V′
  cast lt₁ lt₂ w (desc p env envR) r =
    𝒱→𝒱< d lt₂ p w (𝒱<→𝒱 d lt₁ p w r)

  to : ∀ {x y} (l₁ : n′ ≤′ x) (l₂ : n′ ≤′ y) k w τL τR V V′
    → leafBelow d l₁ c k w τL τR V V′ → leafBelow d l₂ c k w τL τR V V′
  to l₁ l₂ k w τL τR V V′ r with suc k ≤? n′
  ... | yes lt = cast _ _ w (renameDesc τL τR c) r
  ... | no _ = r

leafG-≈ : ∀ {n′ a b} (le₁ : n′ ≤′ a) (le₂ : n′ ≤′ b) (c : Desc ΘL ΘR)
  → sem (leafG le₁ c) ≈ˡ sem (leafG le₂ c)
leafG-≈ {n′ = n′} le₁ le₂ c = sem≈ (to le₁ le₂) (to le₂ le₁)
  where
  cast : ∀ {m x y} (l₁ : m ≤′ x) (l₂ : m ≤′ y) w
      (c′ : Desc (ΔL w) (ΔR w)) {V V′}
    → descG l₁ w c′ V V′ → descG l₂ w c′ V V′
  cast l₁ l₂ w (desc p env envR) r = G→G≤ l₂ p w (G≤→G l₁ p w r)

  to : ∀ {x y} (l₁ : n′ ≤′ x) (l₂ : n′ ≤′ y) k w τL τR V V′
    → leafG l₁ c k w τL τR V V′ → leafG l₂ c k w τL τR V V′
  to l₁ l₂ k w τL τR V V′ r with k ≤? n′
  ... | yes le = cast _ _ w (renameDesc τL τR c) r
  ... | no _ = r

onlyLeaf-≈ : ∀ d {n′ a b} (le₁ : n′ ≤′ a) (le₂ : n′ ≤′ b)
    (c : Desc ΘL ΘR)
  → sem (onlyLeaf d le₁ c) ≈ˡ sem (onlyLeaf d le₂ c)
onlyLeaf-≈ ≺ le₁ le₂ c = leafBelow-≈ ≺ le₁ le₂ c
onlyLeaf-≈ ≻ le₁ le₂ c = leafG-≈ le₁ le₂ c

------------------------------------------------------------------------
-- Peeling a list of seals
------------------------------------------------------------------------

peelSL-map : ∀ (Xs : List (TyVar ΘL)) (c : Desc ΘL ΘR)
    {P P′ : Term ΘL → Term ΘR → Set}
  → (∀ {V V′} → P V V′ → P′ V V′)
  → ∀ {V V′} → peelSL Xs c P V V′ → peelSL Xs c P′ V V′
peelSL-map [] c f r = f r
peelSL-map (X ∷ Xs) c f {V = V ↓ s} (is , r) = is , peelSL-map Xs c f r
peelSL-map (X ∷ Xs) c f {V = ` x₀} ()
peelSL-map (X ∷ Xs) c f {V = ƛ M₀} ()
peelSL-map (X ∷ Xs) c f {V = L₀ · M₀} ()
peelSL-map (X ∷ Xs) c f {V = Λ M₀} ()
peelSL-map (X ∷ Xs) c f {V = L₀ ⦂∀ C₀ [ T₀ ]} ()
peelSL-map (X ∷ Xs) c f {V = $ κ₀} ()
peelSL-map (X ∷ Xs) c f {V = L₀ ⊕[ op₀ ] M₀} ()
peelSL-map (X ∷ Xs) c f {V = W₀ ⟨ c₀ ⟩} ()
peelSL-map (X ∷ Xs) c f {V = M₀ ↑ c₀} ()
peelSL-map (X ∷ Xs) c f {V = blame} ()

peelSR-map : ∀ (Ys : List (TyVar ΘR)) (c : Desc ΘL ΘR)
    {P P′ : Term ΘL → Term ΘR → Set}
  → (∀ {V V′} → P V V′ → P′ V V′)
  → ∀ {V V′} → peelSR Ys c P V V′ → peelSR Ys c P′ V V′
peelSR-map [] c f r = f r
peelSR-map (Y ∷ Ys) c f {V′ = V′ ↓ s} (is , r) = is , peelSR-map Ys c f r
peelSR-map (Y ∷ Ys) c f {V′ = ` x₀} ()
peelSR-map (Y ∷ Ys) c f {V′ = ƛ M₀} ()
peelSR-map (Y ∷ Ys) c f {V′ = L₀ · M₀} ()
peelSR-map (Y ∷ Ys) c f {V′ = Λ M₀} ()
peelSR-map (Y ∷ Ys) c f {V′ = L₀ ⦂∀ C₀ [ T₀ ]} ()
peelSR-map (Y ∷ Ys) c f {V′ = $ κ₀} ()
peelSR-map (Y ∷ Ys) c f {V′ = L₀ ⊕[ op₀ ] M₀} ()
peelSR-map (Y ∷ Ys) c f {V′ = W₀ ⟨ c₀ ⟩} ()
peelSR-map (Y ∷ Ys) c f {V′ = M₀ ↑ c₀} ()
peelSR-map (Y ∷ Ys) c f {V′ = blame} ()

-- renaming the values, the seals and the descriptor
peelSL-ren : ∀ {ΘL′ ΘR′} (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′)
    (Xs : List (TyVar ΘL)) (c : Desc ΘL ΘR)
    {P : Term ΘL → Term ΘR → Set} {P′ : Term ΘL′ → Term ΘR′ → Set}
  → (∀ {V V′} → P V V′ → P′ (renameᵗᵐ σL V) (renameᵗᵐ σR V′))
  → ∀ {V V′} → peelSL Xs c P V V′
  → peelSL (map (renameVar σL) Xs) (renameDesc σL σR c) P′
      (renameᵗᵐ σL V) (renameᵗᵐ σR V′)
peelSL-ren σL σR [] c f r = f r
peelSL-ren σL σR (X ∷ Xs) c f {V = V ↓ s} (is , r) =
  IsSeal-rename (toRenameᵗ σL) s (repL-rename σL σR Xs c) is ,
  peelSL-ren σL σR Xs c f r
peelSL-ren σL σR (X ∷ Xs) c f {V = ` x₀} ()
peelSL-ren σL σR (X ∷ Xs) c f {V = ƛ M₀} ()
peelSL-ren σL σR (X ∷ Xs) c f {V = L₀ · M₀} ()
peelSL-ren σL σR (X ∷ Xs) c f {V = Λ M₀} ()
peelSL-ren σL σR (X ∷ Xs) c f {V = L₀ ⦂∀ C₀ [ T₀ ]} ()
peelSL-ren σL σR (X ∷ Xs) c f {V = $ κ₀} ()
peelSL-ren σL σR (X ∷ Xs) c f {V = L₀ ⊕[ op₀ ] M₀} ()
peelSL-ren σL σR (X ∷ Xs) c f {V = W₀ ⟨ c₀ ⟩} ()
peelSL-ren σL σR (X ∷ Xs) c f {V = M₀ ↑ c₀} ()
peelSL-ren σL σR (X ∷ Xs) c f {V = blame} ()

peelSR-ren : ∀ {ΘL′ ΘR′} (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′)
    (Ys : List (TyVar ΘR)) (c : Desc ΘL ΘR)
    {P : Term ΘL → Term ΘR → Set} {P′ : Term ΘL′ → Term ΘR′ → Set}
  → (∀ {V V′} → P V V′ → P′ (renameᵗᵐ σL V) (renameᵗᵐ σR V′))
  → ∀ {V V′} → peelSR Ys c P V V′
  → peelSR (map (renameVar σR) Ys) (renameDesc σL σR c) P′
      (renameᵗᵐ σL V) (renameᵗᵐ σR V′)
peelSR-ren σL σR [] c f r = f r
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = V′ ↓ s} (is , r) =
  IsSeal-rename (toRenameᵗ σR) s (repR-rename σL σR Ys c) is ,
  peelSR-ren σL σR Ys c f r
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = ` x₀} ()
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = ƛ M₀} ()
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = L₀ · M₀} ()
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = Λ M₀} ()
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = L₀ ⦂∀ C₀ [ T₀ ]} ()
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = $ κ₀} ()
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = L₀ ⊕[ op₀ ] M₀} ()
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = W₀ ⟨ c₀ ⟩} ()
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = M₀ ↑ c₀} ()
peelSR-ren σL σR (Y ∷ Ys) c f {V′ = blame} ()

-- the sealed descriptor's leaf, with its peeling made explicit
peelS-map : ∀ (s : SDesc ΘL ΘR) {ΘL′ ΘR′}
    {τL : ΘL ↪ᵗ ΘL′} {τR : ΘR ↪ᵗ ΘR′} {P P′ : Term ΘL′ → Term ΘR′ → Set}
  → (∀ {V V′} → P V V′ → P′ V V′)
  → ∀ {V V′}
  → peelSL (map (renameVar τL) (sealsL s)) (renameDesc τL τR (core s))
      (peelSR (map (renameVar τR) (sealsR s)) (renameDesc τL τR (core s)) P)
      V V′
  → peelSL (map (renameVar τL) (sealsL s)) (renameDesc τL τR (core s))
      (peelSR (map (renameVar τR) (sealsR s)) (renameDesc τL τR (core s)) P′)
      V V′
peelS-map (sdesc Xs Ys c) {τL = τL} {τR = τR} f =
  peelSL-map (map (renameVar τL) Xs) (renameDesc τL τR c)
    (peelSR-map (map (renameVar τR) Ys) (renameDesc τL τR c) f)

leafBelowS-≈ : ∀ d {n′ a b} (le₁ : n′ ≤′ a) (le₂ : n′ ≤′ b)
    (s : SDesc ΘL ΘR)
  → sem (leafBelowS d le₁ s) ≈ˡ sem (leafBelowS d le₂ s)
leafBelowS-≈ d le₁ le₂ s@(sdesc Xs Ys c) with leafBelow-≈ d le₁ le₂ c
leafBelowS-≈ d le₁ le₂ s@(sdesc Xs Ys c) | sem≈ to from =
  sem≈ (λ k w τL τR V V′ → peelS-map s (to k w τL τR _ _))
       (λ k w τL τR V V′ → peelS-map s (from k w τL τR _ _))

------------------------------------------------------------------------
-- Monotonicity: the clauses that quantify over futures
------------------------------------------------------------------------


funRel-mono : ∀ d n {Φ : Corr Δ Δ′} {A A′ B B′}
    (p : Φ ⊢ A ⊑ A′) (q : Φ ⊢ B ⊑ B′) {w w′} (e : w′ ⊒ w)
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → funRel d n p q w δ Vl Vr
  → funRel d n p q w′ (δ ↑ᴵ e) (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
funRel-mono d n p q e {δ} {Vl} {Vr} f e′ le Wl Wr vl vr a =
  ℰᵍ-≡ (cong (_· Wl) (sym (renameᵗᵐ-∘ (ρL e′) (ρL e) Vl)))
    (cong (_· Wr) (sym (renameᵗᵐ-∘ (ρR e′) (ρR e) Vr)))
    (ℰᵍ-map d _ _
      (λ le′ w″ e″ V V′ →
        𝒱≤-resp d (≤′-trans le′ le) q w″
          (↑ᴵ-resp (≈ᴵ-sym (↑ᴵ-trans δ e′ e)) e″))
      (f (⊒-trans e′ e) le Wl Wr vl vr
        (𝒱≤-resp d le p _ (↑ᴵ-trans δ e′ e) a)))

allPair-mono : ∀ d n {Φ : Corr Δ Δ′} {A B} (p : pair Φ ⊢ A ⊑ B)
    {w w′} (e : w′ ⊒ w) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → allPair d n p w δ Vl Vr
  → allPair d n p w′ (δ ↑ᴵ e) (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
allPair-mono d n {A = A} {B = B} p e {δ} {Vl} {Vr} f e′ le c =
  ℰᵍ-≡
    (cong₂ (λ M C → M ⦂∀ C [ leftTyS c ])
      (sym (renameᵗᵐ-∘ (ρL e′) (ρL e) Vl))
      (substᵗ-cong A (exts-cong (λ X → sym (δl≡ (↑ᴵ-trans δ e′ e) X)))))
    (cong₂ (λ M C → M ⦂∀ C [ rightTyS c ])
      (sym (renameᵗᵐ-∘ (ρR e′) (ρR e) Vr))
      (substᵗ-cong B (exts-cong (λ Y → sym (δr≡ (↑ᴵ-trans δ e′ e) Y)))))
    (ℰᵍ-map d _ _
      (λ le′ w″ e″ V V′ →
        𝒱≤-resp d (≤′-trans le′ le) p w″
          (↑ᴵ-resp (extPairI-resp ≈ˡ-refl (≈ᴵ-sym (↑ᴵ-trans δ e′ e))) e″))
      (f (⊒-trans e′ e) le c))

allOnly-mono : ∀ d n {Φ : Corr Δ Δ′} {A B} (p : only Φ ⊢ A ⊑ B)
    {w w′} (e : w′ ⊒ w) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → allOnly d n p w δ Vl Vr
  → allOnly d n p w′ (δ ↑ᴵ e) (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
allOnly-mono d n {A = A} p e {δ} {Vl} {Vr} f e′ le c =
  ℰᵍ-≡
    (cong₂ (λ M C → M ⦂∀ C [ leftTy c ])
      (sym (renameᵗᵐ-∘ (ρL e′) (ρL e) Vl))
      (substᵗ-cong A (exts-cong (λ X → sym (δl≡ (↑ᴵ-trans δ e′ e) X)))))
    (sym (renameᵗᵐ-∘ (ρR e′) (ρR e) Vr))
    (ℰᵍ-map d _ _
      (λ le′ w″ e″ V V′ →
        𝒱≤-resp d (≤′-trans le′ le) p w″
          (↑ᴵ-resp (extOnlyI-resp ≈ˡ-refl (≈ᴵ-sym (↑ᴵ-trans δ e′ e))) e″))
      (f (⊒-trans e′ e) le c))

allDead-mono : ∀ d n {Φ : Corr Δ Δ′} {A} (p : dead Φ ⊢ A ⊑ ★)
    {w w′} (e : w′ ⊒ w) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → allDead d n p w δ Vl Vr
  → allDead d n p w′ (δ ↑ᴵ e) (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
allDead-mono d n {A = A} p e {δ} {Vl} {Vr} f e′ le T T′ =
  ℰᵍ-≡
    (cong₂ (λ M C → M ⦂∀ C [ T ])
      (sym (renameᵗᵐ-∘ (ρL e′) (ρL e) Vl))
      (substᵗ-cong A (exts-cong (λ X → sym (δl≡ (↑ᴵ-trans δ e′ e) X)))))
    (cong (λ M → M ⦂∀ ★ [ T′ ]) (sym (renameᵗᵐ-∘ (ρR e′) (ρR e) Vr)))
    (ℰᵍ-map d _ _
      (λ le′ w″ e″ V V′ →
        𝒱≤-resp d (≤′-trans le′ le) p w″
          (↑ᴵ-resp (extOnlyI-resp ≈ˡ-refl (≈ᴵ-sym (↑ᴵ-trans δ e′ e))) e″))
      (f (⊒-trans e′ e) le T T′))

allStar-mono : ∀ d n {w w′} (e : w′ ⊒ w) {Vl Vr}
  → allStar d n w Vl Vr
  → allStar d n w′ (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
allStar-mono d n e {Vl} {Vr = Wr ⟨ c ⟩} (inj , f) =
  IsInj∀-rename _ _ c inj ,
  λ e′ le T T′ →
    ℰᵍ-≡ (cong (λ M → M ⦂∀ ★ [ T ]) (sym (renameᵗᵐ-∘ (ρL e′) (ρL e) Vl)))
      (cong (λ M → M ⦂∀ ★ [ T′ ]) (sym (renameᵗᵐ-∘ (ρR e′) (ρR e) Wr)))
      (f (⊒-trans e′ e) le T T′)
allStar-mono d n e {Vr = ` x₀} ()
allStar-mono d n e {Vr = ƛ M₀} ()
allStar-mono d n e {Vr = L₀ · M₀} ()
allStar-mono d n e {Vr = Λ M₀} ()
allStar-mono d n e {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
allStar-mono d n e {Vr = $ κ₀} ()
allStar-mono d n e {Vr = L₀ ⊕[ op₀ ] M₀} ()
allStar-mono d n e {Vr = M₀ ↑ c₀} ()
allStar-mono d n e {Vr = M₀ ↓ c₀} ()
allStar-mono d n e {Vr = blame} ()

funStar-mono : ∀ d n {Φ : Corr Δ Δ′} {A B}
    (p : Φ ⊢ A ⊑ ★) (q : Φ ⊢ B ⊑ ★) {w w′} (e : w′ ⊒ w)
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → funStar d n p q w δ Vl Vr
  → funStar d n p q w′ (δ ↑ᴵ e) (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
funStar-mono d n p q e {Vr = Wr ⟨ c ⟩} (inj , f) =
  IsInj⇒-rename _ _ c inj , funRel-mono d n p q e f
funStar-mono d n p q e {Vr = ` x₀} ()
funStar-mono d n p q e {Vr = ƛ M₀} ()
funStar-mono d n p q e {Vr = L₀ · M₀} ()
funStar-mono d n p q e {Vr = Λ M₀} ()
funStar-mono d n p q e {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
funStar-mono d n p q e {Vr = $ κ₀} ()
funStar-mono d n p q e {Vr = L₀ ⊕[ op₀ ] M₀} ()
funStar-mono d n p q e {Vr = M₀ ↑ c₀} ()
funStar-mono d n p q e {Vr = M₀ ↓ c₀} ()
funStar-mono d n p q e {Vr = blame} ()

allDeadStar-mono : ∀ d n {Φ : Corr Δ Δ′} {A} (p : dead Φ ⊢ A ⊑ ★)
    {w w′} (e : w′ ⊒ w) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → allDeadStar d n p w δ Vl Vr
  → allDeadStar d n p w′ (δ ↑ᴵ e)
      (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
allDeadStar-mono d n p e {Vr = Wr ⟨ c ⟩} (inj , f) =
  IsInj∀-rename _ _ c inj , allDead-mono d n p e f
allDeadStar-mono d n p e {Vr = ` x₀} ()
allDeadStar-mono d n p e {Vr = ƛ M₀} ()
allDeadStar-mono d n p e {Vr = L₀ · M₀} ()
allDeadStar-mono d n p e {Vr = Λ M₀} ()
allDeadStar-mono d n p e {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
allDeadStar-mono d n p e {Vr = $ κ₀} ()
allDeadStar-mono d n p e {Vr = L₀ ⊕[ op₀ ] M₀} ()
allDeadStar-mono d n p e {Vr = M₀ ↑ c₀} ()
allDeadStar-mono d n p e {Vr = M₀ ↓ c₀} ()
allDeadStar-mono d n p e {Vr = blame} ()

baseInj-mono : ∀ {ΘL′ ΘR′} ι (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′) {Vl Vr}
  → baseInj ι Vl Vr
  → baseInj ι (renameᵗᵐ σL Vl) (renameᵗᵐ σR Vr)
baseInj-mono ι σL σR {Vl = $ κ} {Vr = W ⟨ c ⟩} (inj , eq) =
  IsInjBase-rename _ _ c inj , cong (renameᵗᵐ σR) eq
baseInj-mono ι σL σR {Vl = $ κ} {Vr = ` x₀} ()
baseInj-mono ι σL σR {Vl = $ κ} {Vr = ƛ M₀} ()
baseInj-mono ι σL σR {Vl = $ κ} {Vr = L₀ · M₀} ()
baseInj-mono ι σL σR {Vl = $ κ} {Vr = Λ M₀} ()
baseInj-mono ι σL σR {Vl = $ κ} {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
baseInj-mono ι σL σR {Vl = $ κ} {Vr = $ κ₀} ()
baseInj-mono ι σL σR {Vl = $ κ} {Vr = L₀ ⊕[ op₀ ] M₀} ()
baseInj-mono ι σL σR {Vl = $ κ} {Vr = M₀ ↑ c₀} ()
baseInj-mono ι σL σR {Vl = $ κ} {Vr = M₀ ↓ c₀} ()
baseInj-mono ι σL σR {Vl = $ κ} {Vr = blame} ()
baseInj-mono ι σL σR {Vl = ` x₀} ()
baseInj-mono ι σL σR {Vl = ƛ M₀} ()
baseInj-mono ι σL σR {Vl = L₀ · M₀} ()
baseInj-mono ι σL σR {Vl = Λ M₀} ()
baseInj-mono ι σL σR {Vl = L₀ ⦂∀ C₀ [ T₀ ]} ()
baseInj-mono ι σL σR {Vl = L₀ ⊕[ op₀ ] M₀} ()
baseInj-mono ι σL σR {Vl = W₀ ⟨ c₀ ⟩} ()
baseInj-mono ι σL σR {Vl = M₀ ↑ c₀} ()
baseInj-mono ι σL σR {Vl = M₀ ↓ c₀} ()
baseInj-mono ι σL σR {Vl = blame} ()

starFun-mono : ∀ d k {w w′} (e : w′ ⊒ w) {W Vr}
  → starFun d k w W Vr
  → starFun d k w′ (renameᵗᵐ (ρL e) W) (renameᵗᵐ (ρR e) Vr)
starFun-mono ≺ k e {Vr = Wr ⟨ c ⟩} (inj , r) =
  IsInj⇒-rename _ _ c inj ,
  funRel-resp ≺ k ★⊑★ ★⊑★ _ (closedI-transport (ρL e) (ρR e))
    (funRel-mono ≺ k ★⊑★ ★⊑★ e r)
starFun-mono ≻ k e {Vr = Wr ⟨ c ⟩} (inj , r) =
  IsInj⇒-rename _ _ c inj ,
  funRel-resp ≻ k ★⊑★ ★⊑★ _ (closedI-transport (ρL e) (ρR e))
    (funRel-mono ≻ k ★⊑★ ★⊑★ e r)
starFun-mono ≺ k e {Vr = ` x₀} ()
starFun-mono ≺ k e {Vr = ƛ M₀} ()
starFun-mono ≺ k e {Vr = L₀ · M₀} ()
starFun-mono ≺ k e {Vr = Λ M₀} ()
starFun-mono ≺ k e {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
starFun-mono ≺ k e {Vr = $ κ₀} ()
starFun-mono ≺ k e {Vr = L₀ ⊕[ op₀ ] M₀} ()
starFun-mono ≺ k e {Vr = M₀ ↑ c₀} ()
starFun-mono ≺ k e {Vr = M₀ ↓ c₀} ()
starFun-mono ≺ k e {Vr = blame} ()
starFun-mono ≻ k e {Vr = ` x₀} ()
starFun-mono ≻ k e {Vr = ƛ M₀} ()
starFun-mono ≻ k e {Vr = L₀ · M₀} ()
starFun-mono ≻ k e {Vr = Λ M₀} ()
starFun-mono ≻ k e {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
starFun-mono ≻ k e {Vr = $ κ₀} ()
starFun-mono ≻ k e {Vr = L₀ ⊕[ op₀ ] M₀} ()
starFun-mono ≻ k e {Vr = M₀ ↑ c₀} ()
starFun-mono ≻ k e {Vr = M₀ ↓ c₀} ()
starFun-mono ≻ k e {Vr = blame} ()

starAll-mono : ∀ d k {w w′} (e : w′ ⊒ w) {W Vr}
  → starAll d k w W Vr
  → starAll d k w′ (renameᵗᵐ (ρL e) W) (renameᵗᵐ (ρR e) Vr)
starAll-mono ≺ k e {Vr = Wr ⟨ c ⟩} (inj , r) =
  IsInj∀-rename _ _ c inj ,
  allPair-resp ≺ k ★⊑★ _ (closedI-transport (ρL e) (ρR e))
    (allPair-mono ≺ k ★⊑★ e r)
starAll-mono ≻ k e {Vr = Wr ⟨ c ⟩} (inj , r) =
  IsInj∀-rename _ _ c inj ,
  allPair-resp ≻ k ★⊑★ _ (closedI-transport (ρL e) (ρR e))
    (allPair-mono ≻ k ★⊑★ e r)
starAll-mono ≺ k e {Vr = ` x₀} ()
starAll-mono ≺ k e {Vr = ƛ M₀} ()
starAll-mono ≺ k e {Vr = L₀ · M₀} ()
starAll-mono ≺ k e {Vr = Λ M₀} ()
starAll-mono ≺ k e {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
starAll-mono ≺ k e {Vr = $ κ₀} ()
starAll-mono ≺ k e {Vr = L₀ ⊕[ op₀ ] M₀} ()
starAll-mono ≺ k e {Vr = M₀ ↑ c₀} ()
starAll-mono ≺ k e {Vr = M₀ ↓ c₀} ()
starAll-mono ≺ k e {Vr = blame} ()
starAll-mono ≻ k e {Vr = ` x₀} ()
starAll-mono ≻ k e {Vr = ƛ M₀} ()
starAll-mono ≻ k e {Vr = L₀ · M₀} ()
starAll-mono ≻ k e {Vr = Λ M₀} ()
starAll-mono ≻ k e {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
starAll-mono ≻ k e {Vr = $ κ₀} ()
starAll-mono ≻ k e {Vr = L₀ ⊕[ op₀ ] M₀} ()
starAll-mono ≻ k e {Vr = M₀ ↑ c₀} ()
starAll-mono ≻ k e {Vr = M₀ ↓ c₀} ()
starAll-mono ≻ k e {Vr = blame} ()

------------------------------------------------------------------------
-- Monotonicity: induction on the stage and the left term
------------------------------------------------------------------------

mutual
  𝒱-mono : ∀ d n {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′)
      {w w′} (e : w′ ⊒ w) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → GoodI δ → 𝒱 d n p w δ Vl Vr
    → 𝒱 d n p w′ (δ ↑ᴵ e) (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
  𝒱-mono ≺ n ★⊑★ e {Vl = Vl} {Vr} g r = star-mono ≺ n e {Vl} {Vr} r
  𝒱-mono ≻ n ★⊑★ e g r = G-mono n ★⊑★ e g r
  𝒱-mono ≺ n ι⊑ι e g (κ , refl , refl) = κ , refl , refl
  𝒱-mono ≻ n ι⊑ι e g (κ , refl , refl) = κ , refl , refl
  𝒱-mono ≺ n (X⊑Y {X = X} x) e g r = leafRel-mono ≺ n e (g X) r
  𝒱-mono ≻ n (X⊑Y {X = X} x) e g r = leafRel-mono ≻ n e (g X) r
  𝒱-mono ≺ n (⇒⊑⇒ p q) e g r = funRel-mono ≺ n p q e r
  𝒱-mono ≻ n (⇒⊑⇒ p q) e g r = funRel-mono ≻ n p q e r
  𝒱-mono ≺ n (∀⊑∀ p) e g r = allPair-mono ≺ n p e r
  𝒱-mono ≻ n (∀⊑∀ p) e g r = allPair-mono ≻ n p e r
  𝒱-mono ≺ n (⇒⊑★ p q) e g r = funStar-mono ≺ n p q e r
  𝒱-mono ≻ n (⇒⊑★ p q) e g r = G-mono n (⇒⊑★ p q) e g r
  𝒱-mono ≺ n (ι⊑★ {ι = ι}) e g r = baseInj-mono ι (ρL e) (ρR e) r
  𝒱-mono ≻ n ι⊑★ e g r = G-mono n ι⊑★ e g r
  𝒱-mono ≺ n (X⊑★ {X = X} x) e g r = leafRel-mono ≺ n e (g X) r
  𝒱-mono ≻ n (X⊑★ {X = X} x) e g r = leafRel-mono ≻ n e (g X) r
  𝒱-mono ≺ n (∀⊑ Anv z p) e g r = allOnly-mono ≺ n p e r
  𝒱-mono ≻ n (∀⊑ {B = ★} Anv z p) e g r = G-mono n (∀⊑ Anv z p) e g r
  𝒱-mono ≻ n (∀⊑ {B = ＇ Y} Anv z p) e g r = allOnly-mono ≻ n p e r
  𝒱-mono ≻ n (∀⊑ {B = ‵ ι} Anv z p) e g r = allOnly-mono ≻ n p e r
  𝒱-mono ≻ n (∀⊑ {B = B ⇒ C} Anv z p) e g r = allOnly-mono ≻ n p e r
  𝒱-mono ≻ n (∀⊑ {B = `∀ B} Anv z p) e g r = allOnly-mono ≻ n p e r
  𝒱-mono ≺ n ∀★⊑★ e g r = allStar-mono ≺ n e r
  𝒱-mono ≻ n ∀★⊑★ e g r = G-mono n ∀★⊑★ e g r
  𝒱-mono ≺ n (∀⊑★ ns p) e g r = allDeadStar-mono ≺ n p e r
  𝒱-mono ≻ n (∀⊑★ ns p) e g r = G-mono n (∀⊑★ ns p) e g r
  𝒱-mono ≺ n bot-elim e g ()
  𝒱-mono ≻ n bot-elim e g ()
  𝒱-mono ≺ n bot⊑★ e g ()
  𝒱-mono ≻ n bot⊑★ e g ()

  G-mono : ∀ n {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′)
      {w w′} (e : w′ ⊒ w) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → GoodI δ → G n p w δ Vl Vr
    → G n p w′ (δ ↑ᴵ e) (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
  G-mono zero p e g r = r
  G-mono (suc k) ★⊑★ e {Vl = Vl} {Vr} g r =
    star-mono ≻ (suc k) e {Vl} {Vr} r
  G-mono (suc k) ι⊑ι e g (κ , refl , refl) = κ , refl , refl
  G-mono (suc k) (X⊑Y {X = X} x) e g r = leafRel-mono ≻ k e (g X) r
  G-mono (suc k) (⇒⊑⇒ p q) e g r = funRel-mono ≻ k p q e r
  G-mono (suc k) (∀⊑∀ p) e g r = allPair-mono ≻ k p e r
  G-mono (suc k) (⇒⊑★ p q) e g r = funStar-mono ≻ k p q e r
  G-mono (suc k) (ι⊑★ {ι = ι}) e g r = baseInj-mono ι (ρL e) (ρR e) r
  G-mono (suc k) (X⊑★ {X = X} x) e g r =
    leafRel-mono ≻ (suc k) e (g X) r
  G-mono (suc k) (∀⊑ {B = ★} Anv z p) e g r = allOnly-mono ≻ k p e r
  G-mono (suc k) (∀⊑ {B = ＇ Y} Anv z p) e {Vl = Vl} {Vr} g r =
    𝒱-mono ≻ k (∀⊑ Anv z p) e {Vl = Vl} {Vr} g r
  G-mono (suc k) (∀⊑ {B = ‵ ι} Anv z p) e {Vl = Vl} {Vr} g r =
    𝒱-mono ≻ k (∀⊑ Anv z p) e {Vl = Vl} {Vr} g r
  G-mono (suc k) (∀⊑ {B = B ⇒ C} Anv z p) e {Vl = Vl} {Vr} g r =
    𝒱-mono ≻ k (∀⊑ Anv z p) e {Vl = Vl} {Vr} g r
  G-mono (suc k) (∀⊑ {B = `∀ B} Anv z p) e {Vl = Vl} {Vr} g r =
    𝒱-mono ≻ k (∀⊑ Anv z p) e {Vl = Vl} {Vr} g r
  G-mono (suc k) ∀★⊑★ e g r = allStar-mono ≻ k e r
  G-mono (suc k) (∀⊑★ ns p) e g r = allDeadStar-mono ≻ k p e r
  G-mono (suc k) bot-elim e g ()
  G-mono (suc k) bot⊑★ e g ()

  leafRel-mono : ∀ d n {w w′} (e : w′ ⊒ w) {l : Leaf (ΔL w) (ΔR w)}
      {Vl Vr}
    → GoodLeaf l → leafRel d n w l Vl Vr
    → leafRel d n w′ (transportLeaf (ρL e) (ρR e) l)
        (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
  leafRel-mono d n e (good-syn {en = en}) r = entry-mono d n e en r
  leafRel-mono d n {w′ = w′} e {Vl = Vl} {Vr} (good-sem {R = R} mono down) r =
    subst₂ (λ a b → R n w′ a b (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr))
      (trans (∘↪-idʳ (ρL e)) (sym (∘↪-idˡ (ρL e))))
      (trans (∘↪-idʳ (ρR e)) (sym (∘↪-idˡ (ρR e))))
      (mono n _ id↪ᵗ id↪ᵗ e r)

  entry-mono : ∀ d n {w w′} (e : w′ ⊒ w) (en : Entry (ΔL w) (ΔR w))
      {Vl Vr}
    → entry d n w en Vl Vr
    → entry d n w′ (renameEntry (ρL e) (ρR e) en)
        (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
  entry-mono d n {w′ = w′} e (seals X Xs Ys c) {Vl = V ↓ s} {Vr} (is , r) =
    IsSeal-rename (toRenameᵗ (ρL e)) s (repL-rename (ρL e) (ρR e) Xs c) is ,
    subst (λ m → peelL d n w′ m (map (renameVar (ρL e)) Xs)
                   (map (renameVar (ρR e)) Ys) (renameDesc (ρL e) (ρR e) c)
                   (renameᵗᵐ (ρL e) V) (renameᵗᵐ (ρR e) Vr))
      (sym (modeOf-map d (renameVar (ρR e)) Ys))
      (peelL-mono d n e (modeOf d Ys) Xs Ys c r)
  entry-mono d n e (seals X Xs Ys c) {Vl = ` x₀} ()
  entry-mono d n e (seals X Xs Ys c) {Vl = ƛ M₀} ()
  entry-mono d n e (seals X Xs Ys c) {Vl = L₀ · M₀} ()
  entry-mono d n e (seals X Xs Ys c) {Vl = Λ M₀} ()
  entry-mono d n e (seals X Xs Ys c) {Vl = L₀ ⦂∀ C₀ [ T₀ ]} ()
  entry-mono d n e (seals X Xs Ys c) {Vl = $ κ₀} ()
  entry-mono d n e (seals X Xs Ys c) {Vl = L₀ ⊕[ op₀ ] M₀} ()
  entry-mono d n e (seals X Xs Ys c) {Vl = W₀ ⟨ c₀ ⟩} ()
  entry-mono d n e (seals X Xs Ys c) {Vl = M₀ ↑ c₀} ()
  entry-mono d n e (seals X Xs Ys c) {Vl = blame} ()

  peelL-mono : ∀ d n {w w′} (e : w′ ⊒ w) m Xs Ys
      (c : Desc (ΔL w) (ΔR w)) {Vl Vr}
    → peelL d n w m Xs Ys c Vl Vr
    → peelL d n w′ m (map (renameVar (ρL e)) Xs)
        (map (renameVar (ρR e)) Ys) (renameDesc (ρL e) (ρR e) c)
        (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
  peelL-mono d n e m [] Ys c r = peelR-mono d n e m Ys c r
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = V ↓ s} (is , r) =
    IsSeal-rename (toRenameᵗ (ρL e)) s (repL-rename (ρL e) (ρR e) Xs c) is ,
    peelL-mono d n e m Xs Ys c r
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = ` x₀} ()
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = ƛ M₀} ()
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = L₀ · M₀} ()
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = Λ M₀} ()
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = L₀ ⦂∀ C₀ [ T₀ ]} ()
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = $ κ₀} ()
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = L₀ ⊕[ op₀ ] M₀} ()
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = W₀ ⟨ c₀ ⟩} ()
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = M₀ ↑ c₀} ()
  peelL-mono d n e m (X ∷ Xs) Ys c {Vl = blame} ()

  peelR-mono : ∀ d n {w w′} (e : w′ ⊒ w) m Ys
      (c : Desc (ΔL w) (ΔR w)) {Vl Vr}
    → peelR d n w m Ys c Vl Vr
    → peelR d n w′ m (map (renameVar (ρR e)) Ys)
        (renameDesc (ρL e) (ρR e) c)
        (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
  peelR-mono d n e m [] c r = contents-mono d n e m c r
  peelR-mono d n e m (Y ∷ Ys) c {Vr = V′ ↓ s} (is , r) =
    IsSeal-rename (toRenameᵗ (ρR e)) s (repR-rename (ρL e) (ρR e) Ys c) is ,
    peelR-mono d n e m Ys c r
  peelR-mono d n e m (Y ∷ Ys) c {Vr = ` x₀} ()
  peelR-mono d n e m (Y ∷ Ys) c {Vr = ƛ M₀} ()
  peelR-mono d n e m (Y ∷ Ys) c {Vr = L₀ · M₀} ()
  peelR-mono d n e m (Y ∷ Ys) c {Vr = Λ M₀} ()
  peelR-mono d n e m (Y ∷ Ys) c {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
  peelR-mono d n e m (Y ∷ Ys) c {Vr = $ κ₀} ()
  peelR-mono d n e m (Y ∷ Ys) c {Vr = L₀ ⊕[ op₀ ] M₀} ()
  peelR-mono d n e m (Y ∷ Ys) c {Vr = W₀ ⟨ c₀ ⟩} ()
  peelR-mono d n e m (Y ∷ Ys) c {Vr = M₀ ↑ c₀} ()
  peelR-mono d n e m (Y ∷ Ys) c {Vr = blame} ()

  contents-mono : ∀ d n {w w′} (e : w′ ⊒ w) m
      (c : Desc (ΔL w) (ΔR w)) {Vl Vr}
    → contents d n w m c Vl Vr
    → contents d n w′ m (renameDesc (ρL e) (ρR e) c)
        (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
  contents-mono d zero e later c r = r
  contents-mono d (suc k) e later (desc p env envR) r =
    𝒱-resp d k p _ (envI-transport (ρL e) (ρR e) env envR)
      (𝒱-mono d k p e (good-envI {env = env} {envR = envR}) r)
  contents-mono d zero e guarded (desc p env envR) r = r
  contents-mono d (suc k) e guarded (desc p env envR) r =
    G-resp (suc k) p _ (envI-transport (ρL e) (ρR e) env envR)
      (G-mono (suc k) p e (good-envI {env = env} {envR = envR}) r)

  star-mono : ∀ d n {w w′} (e : w′ ⊒ w) {Vl Vr}
    → star d n w Vl Vr
    → star d n w′ (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρR e) Vr)
  star-mono d n e {Vl = W ⟨ _! ⦃ Gᵍ = g ⦄ c ⟩} r =
    starGround-mono d n e g r
  star-mono d n e {Vl = ` x₀} ()
  star-mono d n e {Vl = ƛ M₀} ()
  star-mono d n e {Vl = L₀ · M₀} ()
  star-mono d n e {Vl = Λ M₀} ()
  star-mono d n e {Vl = L₀ ⦂∀ C₀ [ T₀ ]} ()
  star-mono d n e {Vl = $ κ₀} ()
  star-mono d n e {Vl = L₀ ⊕[ op₀ ] M₀} ()
  star-mono d n e {Vl = M₀ ↑ c₀} ()
  star-mono d n e {Vl = M₀ ↓ c₀} ()
  star-mono d n e {Vl = blame} ()
  star-mono d n e {Vl = W₀ ⟨ id a₀ ⟩} ()
  star-mono d n e {Vl = W₀ ⟨ c₀ ↦ d₀ ⟩} ()
  star-mono d n e {Vl = W₀ ⟨ ∀ᶜ c₀ ⟩} ()
  star-mono d n e {Vl = W₀ ⟨ ？ c₀ ⟩} ()
  star-mono d n e {Vl = W₀ ⟨ inst_ c₀ h₀ ⟩} ()
  star-mono d n e {Vl = W₀ ⟨ gen_ c₀ h₀ ⟩} ()
  star-mono d n e {Vl = W₀ ⟨ bot-elim ⟩} ()
  star-mono d n e {Vl = W₀ ⟨ bot-intro ⟩} ()

  starGround-mono : ∀ d n {w w′} (e : w′ ⊒ w) {G} (g : Ground G) {W Vr}
    → starGround d n w g W Vr
    → starGround d n w′ (renameGround (toRenameᵗ (ρL e)) g)
        (renameᵗᵐ (ρL e) W) (renameᵗᵐ (ρR e) Vr)
  starGround-mono d n {w} {w′} e (＇ X) {W} {Vr} r =
    subst (λ t → tagRel d n w′ t (renameᵗᵐ (ρL e) W) (renameᵗᵐ (ρR e) Vr))
      (sym (tags≡ e X))
      (tagRel-mono d n e (tag w X) r)
  starGround-mono d n e (‵ ι) r = baseInj-mono ι (ρL e) (ρR e) r
  starGround-mono d zero e ★⇒★ r = r
  starGround-mono d (suc k) e ★⇒★ r = starFun-mono d k e r
  starGround-mono d zero e ∀★ r = r
  starGround-mono d (suc k) e ∀★ r = starAll-mono d k e r

  tagRel-mono : ∀ d n {w w′} (e : w′ ⊒ w) (t : Tag (ΔL w) (ΔR w)) {W Vr}
    → tagRel d n w t W Vr
    → tagRel d n w′ (renameTag (ρL e) (ρR e) t)
        (renameᵗᵐ (ρL e) W) (renameᵗᵐ (ρR e) Vr)
  tagRel-mono d n e (just Y , en) {Vr = Wr ⟨ c ⟩} (inj , r) =
    IsInjVar-rename _ _ c inj , entry-mono d n e en r
  tagRel-mono d n e (just Y , en) {Vr = ` x₀} ()
  tagRel-mono d n e (just Y , en) {Vr = ƛ M₀} ()
  tagRel-mono d n e (just Y , en) {Vr = L₀ · M₀} ()
  tagRel-mono d n e (just Y , en) {Vr = Λ M₀} ()
  tagRel-mono d n e (just Y , en) {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
  tagRel-mono d n e (just Y , en) {Vr = $ κ₀} ()
  tagRel-mono d n e (just Y , en) {Vr = L₀ ⊕[ op₀ ] M₀} ()
  tagRel-mono d n e (just Y , en) {Vr = M₀ ↑ c₀} ()
  tagRel-mono d n e (just Y , en) {Vr = M₀ ↓ c₀} ()
  tagRel-mono d n e (just Y , en) {Vr = blame} ()
  tagRel-mono d n e (nothing , en) r = entry-mono d n e en r

------------------------------------------------------------------------
-- Downward closure: the clauses that quantify over futures
------------------------------------------------------------------------

funRel-down : ∀ d {n n′} (le : n′ ≤ n) {Φ : Corr Δ Δ′} {A A′ B B′}
    (p : Φ ⊢ A ⊑ A′) (q : Φ ⊢ B ⊑ B′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → funRel d n p q w δ Vl Vr → funRel d n′ p q w δ Vl Vr
funRel-down d le p q w f e le₁ Wl Wr vl vr a =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ →
      𝒱≤-cast d (≤′-trans le′ le₂) (≤′-trans le′ le₁) q w″)
    (f e le₂ Wl Wr vl vr (𝒱≤-cast d le₁ le₂ p _ a))
  where le₂ = ≤′-trans le₁ (≤⇒≤′ le)

allPair-down : ∀ d {n n′} (le : n′ ≤ n) {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → allPair d n p w δ Vl Vr → allPair d n′ p w δ Vl Vr
allPair-down d le p w f e le₁ c =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ r →
      𝒱≤-resp d (≤′-trans le′ le₁) p w″
        (↑ᴵ-resp (extPairI-resp (leafBelowS-≈ d le₂ le₁ c) ≈ᴵ-refl) e′)
        (𝒱≤-cast d (≤′-trans le′ le₂) (≤′-trans le′ le₁) p w″ r))
    (f e le₂ c)
  where le₂ = ≤′-trans le₁ (≤⇒≤′ le)

allOnly-down : ∀ d {n n′} (le : n′ ≤ n) {Φ : Corr Δ Δ′} {A B}
    (p : only Φ ⊢ A ⊑ B) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → allOnly d n p w δ Vl Vr → allOnly d n′ p w δ Vl Vr
allOnly-down d le p w f e le₁ c =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ r →
      𝒱≤-resp d (≤′-trans le′ le₁) p w″
        (↑ᴵ-resp (extOnlyI-resp (onlyLeaf-≈ d le₂ le₁ c) ≈ᴵ-refl) e′)
        (𝒱≤-cast d (≤′-trans le′ le₂) (≤′-trans le′ le₁) p w″ r))
    (f e le₂ c)
  where le₂ = ≤′-trans le₁ (≤⇒≤′ le)

allDead-down : ∀ d {n n′} (le : n′ ≤ n) {Φ : Corr Δ Δ′} {A}
    (p : dead Φ ⊢ A ⊑ ★) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → allDead d n p w δ Vl Vr → allDead d n′ p w δ Vl Vr
allDead-down d le p w f e le₁ T T′ =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ →
      𝒱≤-cast d (≤′-trans le′ le₂) (≤′-trans le′ le₁) p w″)
    (f e le₂ T T′)
  where le₂ = ≤′-trans le₁ (≤⇒≤′ le)

allStar-down : ∀ d {n n′} (le : n′ ≤ n) w {Vl Vr}
  → allStar d n w Vl Vr → allStar d n′ w Vl Vr
allStar-down d le w {Vr = Wr ⟨ c ⟩} (inj , f) =
  inj ,
  λ e le₁ T T′ →
    ℰᵍ-map d _ _
      (λ le′ w″ e′ V V′ →
        starAt-cast d (≤′-trans le′ (≤′-trans le₁ (≤⇒≤′ le)))
          (≤′-trans le′ le₁) w″)
      (f e (≤′-trans le₁ (≤⇒≤′ le)) T T′)
allStar-down d le w {Vr = ` x₀} ()
allStar-down d le w {Vr = ƛ M₀} ()
allStar-down d le w {Vr = L₀ · M₀} ()
allStar-down d le w {Vr = Λ M₀} ()
allStar-down d le w {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
allStar-down d le w {Vr = $ κ₀} ()
allStar-down d le w {Vr = L₀ ⊕[ op₀ ] M₀} ()
allStar-down d le w {Vr = M₀ ↑ c₀} ()
allStar-down d le w {Vr = M₀ ↓ c₀} ()
allStar-down d le w {Vr = blame} ()

funStar-down : ∀ d {n n′} (le : n′ ≤ n) {Φ : Corr Δ Δ′} {A B}
    (p : Φ ⊢ A ⊑ ★) (q : Φ ⊢ B ⊑ ★) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → funStar d n p q w δ Vl Vr → funStar d n′ p q w δ Vl Vr
funStar-down d le p q w {Vr = Wr ⟨ c ⟩} (inj , f) =
  inj , funRel-down d le p q w f
funStar-down d le p q w {Vr = ` x₀} ()
funStar-down d le p q w {Vr = ƛ M₀} ()
funStar-down d le p q w {Vr = L₀ · M₀} ()
funStar-down d le p q w {Vr = Λ M₀} ()
funStar-down d le p q w {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
funStar-down d le p q w {Vr = $ κ₀} ()
funStar-down d le p q w {Vr = L₀ ⊕[ op₀ ] M₀} ()
funStar-down d le p q w {Vr = M₀ ↑ c₀} ()
funStar-down d le p q w {Vr = M₀ ↓ c₀} ()
funStar-down d le p q w {Vr = blame} ()

allDeadStar-down : ∀ d {n n′} (le : n′ ≤ n) {Φ : Corr Δ Δ′} {A}
    (p : dead Φ ⊢ A ⊑ ★) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → allDeadStar d n p w δ Vl Vr → allDeadStar d n′ p w δ Vl Vr
allDeadStar-down d le p w {Vr = Wr ⟨ c ⟩} (inj , f) =
  inj , allDead-down d le p w f
allDeadStar-down d le p w {Vr = ` x₀} ()
allDeadStar-down d le p w {Vr = ƛ M₀} ()
allDeadStar-down d le p w {Vr = L₀ · M₀} ()
allDeadStar-down d le p w {Vr = Λ M₀} ()
allDeadStar-down d le p w {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
allDeadStar-down d le p w {Vr = $ κ₀} ()
allDeadStar-down d le p w {Vr = L₀ ⊕[ op₀ ] M₀} ()
allDeadStar-down d le p w {Vr = M₀ ↑ c₀} ()
allDeadStar-down d le p w {Vr = M₀ ↓ c₀} ()
allDeadStar-down d le p w {Vr = blame} ()

starFun-down : ∀ d {k k′} (le : k′ ≤ k) w {W Vr}
  → starFun d k w W Vr → starFun d k′ w W Vr
starFun-down ≺ le w {Vr = Wr ⟨ c ⟩} (inj , r) =
  inj , funRel-down ≺ le ★⊑★ ★⊑★ w r
starFun-down ≻ le w {Vr = Wr ⟨ c ⟩} (inj , r) =
  inj , funRel-down ≻ le ★⊑★ ★⊑★ w r
starFun-down ≺ le w {Vr = ` x₀} ()
starFun-down ≺ le w {Vr = ƛ M₀} ()
starFun-down ≺ le w {Vr = L₀ · M₀} ()
starFun-down ≺ le w {Vr = Λ M₀} ()
starFun-down ≺ le w {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
starFun-down ≺ le w {Vr = $ κ₀} ()
starFun-down ≺ le w {Vr = L₀ ⊕[ op₀ ] M₀} ()
starFun-down ≺ le w {Vr = M₀ ↑ c₀} ()
starFun-down ≺ le w {Vr = M₀ ↓ c₀} ()
starFun-down ≺ le w {Vr = blame} ()
starFun-down ≻ le w {Vr = ` x₀} ()
starFun-down ≻ le w {Vr = ƛ M₀} ()
starFun-down ≻ le w {Vr = L₀ · M₀} ()
starFun-down ≻ le w {Vr = Λ M₀} ()
starFun-down ≻ le w {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
starFun-down ≻ le w {Vr = $ κ₀} ()
starFun-down ≻ le w {Vr = L₀ ⊕[ op₀ ] M₀} ()
starFun-down ≻ le w {Vr = M₀ ↑ c₀} ()
starFun-down ≻ le w {Vr = M₀ ↓ c₀} ()
starFun-down ≻ le w {Vr = blame} ()

starAll-down : ∀ d {k k′} (le : k′ ≤ k) w {W Vr}
  → starAll d k w W Vr → starAll d k′ w W Vr
starAll-down ≺ le w {Vr = Wr ⟨ c ⟩} (inj , r) =
  inj , allPair-down ≺ le ★⊑★ w r
starAll-down ≻ le w {Vr = Wr ⟨ c ⟩} (inj , r) =
  inj , allPair-down ≻ le ★⊑★ w r
starAll-down ≺ le w {Vr = ` x₀} ()
starAll-down ≺ le w {Vr = ƛ M₀} ()
starAll-down ≺ le w {Vr = L₀ · M₀} ()
starAll-down ≺ le w {Vr = Λ M₀} ()
starAll-down ≺ le w {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
starAll-down ≺ le w {Vr = $ κ₀} ()
starAll-down ≺ le w {Vr = L₀ ⊕[ op₀ ] M₀} ()
starAll-down ≺ le w {Vr = M₀ ↑ c₀} ()
starAll-down ≺ le w {Vr = M₀ ↓ c₀} ()
starAll-down ≺ le w {Vr = blame} ()
starAll-down ≻ le w {Vr = ` x₀} ()
starAll-down ≻ le w {Vr = ƛ M₀} ()
starAll-down ≻ le w {Vr = L₀ · M₀} ()
starAll-down ≻ le w {Vr = Λ M₀} ()
starAll-down ≻ le w {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
starAll-down ≻ le w {Vr = $ κ₀} ()
starAll-down ≻ le w {Vr = L₀ ⊕[ op₀ ] M₀} ()
starAll-down ≻ le w {Vr = M₀ ↑ c₀} ()
starAll-down ≻ le w {Vr = M₀ ↓ c₀} ()
starAll-down ≻ le w {Vr = blame} ()

------------------------------------------------------------------------
-- Downward closure: induction on the stage and the left term
------------------------------------------------------------------------

mutual
  𝒱-down : ∀ d {n n′} (le : n′ ≤ n) {Φ : Corr Δ Δ′} {A A′}
      (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → GoodI δ → 𝒱 d n p w δ Vl Vr → 𝒱 d n′ p w δ Vl Vr
  𝒱-down ≺ le ★⊑★ w {Vl = Vl} {Vr} g r = star-down ≺ le w {Vl} {Vr} r
  𝒱-down ≻ le ★⊑★ w g r = G-down le ★⊑★ w g r
  𝒱-down ≺ le ι⊑ι w g r = r
  𝒱-down ≻ le ι⊑ι w g r = r
  𝒱-down ≺ le (X⊑Y {X = X} x) w g r = leafRel-down ≺ le w (g X) r
  𝒱-down ≻ le (X⊑Y {X = X} x) w g r = leafRel-down ≻ le w (g X) r
  𝒱-down ≺ le (⇒⊑⇒ p q) w g r = funRel-down ≺ le p q w r
  𝒱-down ≻ le (⇒⊑⇒ p q) w g r = funRel-down ≻ le p q w r
  𝒱-down ≺ le (∀⊑∀ p) w g r = allPair-down ≺ le p w r
  𝒱-down ≻ le (∀⊑∀ p) w g r = allPair-down ≻ le p w r
  𝒱-down ≺ le (⇒⊑★ p q) w g r = funStar-down ≺ le p q w r
  𝒱-down ≻ le (⇒⊑★ p q) w g r = G-down le (⇒⊑★ p q) w g r
  𝒱-down ≺ le ι⊑★ w g r = r
  𝒱-down ≻ le ι⊑★ w g r = G-down le ι⊑★ w g r
  𝒱-down ≺ le (X⊑★ {X = X} x) w g r = leafRel-down ≺ le w (g X) r
  𝒱-down ≻ le (X⊑★ {X = X} x) w g r = leafRel-down ≻ le w (g X) r
  𝒱-down ≺ le (∀⊑ Anv z p) w g r = allOnly-down ≺ le p w r
  𝒱-down ≻ le (∀⊑ {B = ★} Anv z p) w g r = G-down le (∀⊑ Anv z p) w g r
  𝒱-down ≻ le (∀⊑ {B = ＇ Y} Anv z p) w g r = allOnly-down ≻ le p w r
  𝒱-down ≻ le (∀⊑ {B = ‵ ι} Anv z p) w g r = allOnly-down ≻ le p w r
  𝒱-down ≻ le (∀⊑ {B = B ⇒ C} Anv z p) w g r = allOnly-down ≻ le p w r
  𝒱-down ≻ le (∀⊑ {B = `∀ B} Anv z p) w g r = allOnly-down ≻ le p w r
  𝒱-down ≺ le ∀★⊑★ w g r = allStar-down ≺ le w r
  𝒱-down ≻ le ∀★⊑★ w g r = G-down le ∀★⊑★ w g r
  𝒱-down ≺ le (∀⊑★ ns p) w g r = allDeadStar-down ≺ le p w r
  𝒱-down ≻ le (∀⊑★ ns p) w g r = G-down le (∀⊑★ ns p) w g r
  𝒱-down ≺ le bot-elim w g ()
  𝒱-down ≻ le bot-elim w g ()
  𝒱-down ≺ le bot⊑★ w g ()
  𝒱-down ≻ le bot⊑★ w g ()

  G-down : ∀ {n n′} (le : n′ ≤ n) {Φ : Corr Δ Δ′} {A A′}
      (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → GoodI δ → G n p w δ Vl Vr → G n′ p w δ Vl Vr
  G-down z≤n p w g r = tt
  G-down (s≤s le) ★⊑★ w {Vl = Vl} {Vr} g r =
    star-down ≻ (s≤s le) w {Vl} {Vr} r
  G-down (s≤s le) ι⊑ι w g r = r
  G-down (s≤s le) (X⊑Y {X = X} x) w g r = leafRel-down ≻ le w (g X) r
  G-down (s≤s le) (⇒⊑⇒ p q) w g r = funRel-down ≻ le p q w r
  G-down (s≤s le) (∀⊑∀ p) w g r = allPair-down ≻ le p w r
  G-down (s≤s le) (⇒⊑★ p q) w g r = funStar-down ≻ le p q w r
  G-down (s≤s le) ι⊑★ w g r = r
  G-down (s≤s le) (X⊑★ {X = X} x) w g r =
    leafRel-down ≻ (s≤s le) w (g X) r
  G-down (s≤s le) (∀⊑ {B = ★} Anv z p) w g r = allOnly-down ≻ le p w r
  G-down (s≤s le) (∀⊑ {B = ＇ Y} Anv z p) w {Vl = Vl} {Vr} g r =
    𝒱-down ≻ le (∀⊑ Anv z p) w {Vl = Vl} {Vr} g r
  G-down (s≤s le) (∀⊑ {B = ‵ ι} Anv z p) w {Vl = Vl} {Vr} g r =
    𝒱-down ≻ le (∀⊑ Anv z p) w {Vl = Vl} {Vr} g r
  G-down (s≤s le) (∀⊑ {B = B ⇒ C} Anv z p) w {Vl = Vl} {Vr} g r =
    𝒱-down ≻ le (∀⊑ Anv z p) w {Vl = Vl} {Vr} g r
  G-down (s≤s le) (∀⊑ {B = `∀ B} Anv z p) w {Vl = Vl} {Vr} g r =
    𝒱-down ≻ le (∀⊑ Anv z p) w {Vl = Vl} {Vr} g r
  G-down (s≤s le) ∀★⊑★ w g r = allStar-down ≻ le w r
  G-down (s≤s le) (∀⊑★ ns p) w g r = allDeadStar-down ≻ le p w r
  G-down (s≤s le) bot-elim w g ()
  G-down (s≤s le) bot⊑★ w g ()

  leafRel-down : ∀ d {n n′} (le : n′ ≤ n) w {l : Leaf (ΔL w) (ΔR w)}
      {Vl Vr}
    → GoodLeaf l → leafRel d n w l Vl Vr → leafRel d n′ w l Vl Vr
  leafRel-down d le w (good-syn {en = en}) r = entry-down d le w en r
  leafRel-down d le w (good-sem mono down) r = down le w id↪ᵗ id↪ᵗ r

  entry-down : ∀ d {n n′} (le : n′ ≤ n) w (en : Entry (ΔL w) (ΔR w))
      {Vl Vr}
    → entry d n w en Vl Vr → entry d n′ w en Vl Vr
  entry-down d le w (seals X Xs Ys c) {Vl = V ↓ s} (is , r) =
    is , peelL-down d le w (modeOf d Ys) Xs Ys c r
  entry-down d le w (seals X Xs Ys c) {Vl = ` x₀} ()
  entry-down d le w (seals X Xs Ys c) {Vl = ƛ M₀} ()
  entry-down d le w (seals X Xs Ys c) {Vl = L₀ · M₀} ()
  entry-down d le w (seals X Xs Ys c) {Vl = Λ M₀} ()
  entry-down d le w (seals X Xs Ys c) {Vl = L₀ ⦂∀ C₀ [ T₀ ]} ()
  entry-down d le w (seals X Xs Ys c) {Vl = $ κ₀} ()
  entry-down d le w (seals X Xs Ys c) {Vl = L₀ ⊕[ op₀ ] M₀} ()
  entry-down d le w (seals X Xs Ys c) {Vl = W₀ ⟨ c₀ ⟩} ()
  entry-down d le w (seals X Xs Ys c) {Vl = M₀ ↑ c₀} ()
  entry-down d le w (seals X Xs Ys c) {Vl = blame} ()

  peelL-down : ∀ d {n n′} (le : n′ ≤ n) w m Xs Ys
      (c : Desc (ΔL w) (ΔR w)) {Vl Vr}
    → peelL d n w m Xs Ys c Vl Vr → peelL d n′ w m Xs Ys c Vl Vr
  peelL-down d le w m [] Ys c r = peelR-down d le w m Ys c r
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = V ↓ s} (is , r) =
    is , peelL-down d le w m Xs Ys c r
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = ` x₀} ()
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = ƛ M₀} ()
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = L₀ · M₀} ()
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = Λ M₀} ()
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = L₀ ⦂∀ C₀ [ T₀ ]} ()
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = $ κ₀} ()
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = L₀ ⊕[ op₀ ] M₀} ()
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = W₀ ⟨ c₀ ⟩} ()
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = M₀ ↑ c₀} ()
  peelL-down d le w m (X ∷ Xs) Ys c {Vl = blame} ()

  peelR-down : ∀ d {n n′} (le : n′ ≤ n) w m Ys
      (c : Desc (ΔL w) (ΔR w)) {Vl Vr}
    → peelR d n w m Ys c Vl Vr → peelR d n′ w m Ys c Vl Vr
  peelR-down d le w m [] c r = contents-down d le w m c r
  peelR-down d le w m (Y ∷ Ys) c {Vr = V′ ↓ s} (is , r) =
    is , peelR-down d le w m Ys c r
  peelR-down d le w m (Y ∷ Ys) c {Vr = ` x₀} ()
  peelR-down d le w m (Y ∷ Ys) c {Vr = ƛ M₀} ()
  peelR-down d le w m (Y ∷ Ys) c {Vr = L₀ · M₀} ()
  peelR-down d le w m (Y ∷ Ys) c {Vr = Λ M₀} ()
  peelR-down d le w m (Y ∷ Ys) c {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
  peelR-down d le w m (Y ∷ Ys) c {Vr = $ κ₀} ()
  peelR-down d le w m (Y ∷ Ys) c {Vr = L₀ ⊕[ op₀ ] M₀} ()
  peelR-down d le w m (Y ∷ Ys) c {Vr = W₀ ⟨ c₀ ⟩} ()
  peelR-down d le w m (Y ∷ Ys) c {Vr = M₀ ↑ c₀} ()
  peelR-down d le w m (Y ∷ Ys) c {Vr = blame} ()

  contents-down : ∀ d {n n′} (le : n′ ≤ n) w m
      (c : Desc (ΔL w) (ΔR w)) {Vl Vr}
    → contents d n w m c Vl Vr → contents d n′ w m c Vl Vr
  contents-down d (z≤n {zero}) w later c r = r
  contents-down d (z≤n {suc k}) w later c r = tt
  contents-down d (s≤s le) w later (desc p env envR) r =
    𝒱-down d le p w (good-envI {env = env} {envR = envR}) r
  contents-down d (z≤n {zero}) w guarded (desc p env envR) r = r
  contents-down d (z≤n {suc k}) w guarded (desc p env envR) r = tt
  contents-down d (s≤s le) w guarded (desc p env envR) r =
    G-down (s≤s le) p w (good-envI {env = env} {envR = envR}) r

  star-down : ∀ d {n n′} (le : n′ ≤ n) w {Vl Vr}
    → star d n w Vl Vr → star d n′ w Vl Vr
  star-down d le w {Vl = W ⟨ _! ⦃ Gᵍ = g ⦄ c ⟩} r =
    starGround-down d le w g r
  star-down d le w {Vl = ` x₀} ()
  star-down d le w {Vl = ƛ M₀} ()
  star-down d le w {Vl = L₀ · M₀} ()
  star-down d le w {Vl = Λ M₀} ()
  star-down d le w {Vl = L₀ ⦂∀ C₀ [ T₀ ]} ()
  star-down d le w {Vl = $ κ₀} ()
  star-down d le w {Vl = L₀ ⊕[ op₀ ] M₀} ()
  star-down d le w {Vl = M₀ ↑ c₀} ()
  star-down d le w {Vl = M₀ ↓ c₀} ()
  star-down d le w {Vl = blame} ()
  star-down d le w {Vl = W₀ ⟨ id a₀ ⟩} ()
  star-down d le w {Vl = W₀ ⟨ c₀ ↦ d₀ ⟩} ()
  star-down d le w {Vl = W₀ ⟨ ∀ᶜ c₀ ⟩} ()
  star-down d le w {Vl = W₀ ⟨ ？ c₀ ⟩} ()
  star-down d le w {Vl = W₀ ⟨ inst_ c₀ h₀ ⟩} ()
  star-down d le w {Vl = W₀ ⟨ gen_ c₀ h₀ ⟩} ()
  star-down d le w {Vl = W₀ ⟨ bot-elim ⟩} ()
  star-down d le w {Vl = W₀ ⟨ bot-intro ⟩} ()

  starGround-down : ∀ d {n n′} (le : n′ ≤ n) w {G} (g : Ground G) {W Vr}
    → starGround d n w g W Vr → starGround d n′ w g W Vr
  starGround-down d le w (＇ X) r = tagRel-down d le w (tag w X) r
  starGround-down d le w (‵ ι) r = r
  starGround-down d z≤n w ★⇒★ r = tt
  starGround-down d (s≤s le) w ★⇒★ r = starFun-down d le w r
  starGround-down d z≤n w ∀★ r = tt
  starGround-down d (s≤s le) w ∀★ r = starAll-down d le w r

  tagRel-down : ∀ d {n n′} (le : n′ ≤ n) w (t : Tag (ΔL w) (ΔR w)) {W Vr}
    → tagRel d n w t W Vr → tagRel d n′ w t W Vr
  tagRel-down d le w (just Y , en) {Vr = Wr ⟨ c ⟩} (inj , r) =
    inj , entry-down d le w en r
  tagRel-down d le w (just Y , en) {Vr = ` x₀} ()
  tagRel-down d le w (just Y , en) {Vr = ƛ M₀} ()
  tagRel-down d le w (just Y , en) {Vr = L₀ · M₀} ()
  tagRel-down d le w (just Y , en) {Vr = Λ M₀} ()
  tagRel-down d le w (just Y , en) {Vr = L₀ ⦂∀ C₀ [ T₀ ]} ()
  tagRel-down d le w (just Y , en) {Vr = $ κ₀} ()
  tagRel-down d le w (just Y , en) {Vr = L₀ ⊕[ op₀ ] M₀} ()
  tagRel-down d le w (just Y , en) {Vr = M₀ ↑ c₀} ()
  tagRel-down d le w (just Y , en) {Vr = M₀ ↓ c₀} ()
  tagRel-down d le w (just Y , en) {Vr = blame} ()
  tagRel-down d le w (nothing , en) r = entry-down d le w en r

------------------------------------------------------------------------
-- The leaves the relation builds are good
------------------------------------------------------------------------

descBelow-mono : ∀ d {m n} (lt : suc m ≤′ n) {w w′} (e : w′ ⊒ w)
    (c : Desc (ΔL w) (ΔR w)) {V V′}
  → descBelow d lt w c V V′
  → descBelow d lt w′ (renameDesc (ρL e) (ρR e) c)
      (renameᵗᵐ (ρL e) V) (renameᵗᵐ (ρR e) V′)
descBelow-mono d {m} lt e (desc p env envR) r =
  𝒱→𝒱< d lt p _
    (𝒱-resp d m p _ (envI-transport (ρL e) (ρR e) env envR)
      (𝒱-mono d m p e (good-envI {env = env} {envR = envR}) (𝒱<→𝒱 d lt p _ r)))

descBelow-down : ∀ d {m n m′ n′} (lt : suc m ≤′ n) (lt′ : suc m′ ≤′ n′)
  → m′ ≤ m → ∀ w (c : Desc (ΔL w) (ΔR w)) {V V′}
  → descBelow d lt w c V V′ → descBelow d lt′ w c V V′
descBelow-down d lt lt′ le w (desc p env envR) r =
  𝒱→𝒱< d lt′ p w
    (𝒱-down d le p w (good-envI {env = env} {envR = envR})
      (𝒱<→𝒱 d lt p w r))

leafBelow-mono : ∀ d {n′ n} (le : n′ ≤′ n) (c : Desc ΘL ΘR)
  → MonoΩ (leafBelow d le c)
leafBelow-mono d {n′} le c k w τL τR {w′} e {V} {V′} r with suc k ≤? n′
... | yes lt =
  subst (λ c′ → descBelow d (≤′-trans (≤⇒≤′ lt) le) w′ c′
                  (renameᵗᵐ (ρL e) V) (renameᵗᵐ (ρR e) V′))
    (renameDesc-∘ (ρL e) τL (ρR e) τR c)
    (descBelow-mono d _ e (renameDesc τL τR c) r)
... | no _ = r

leafBelow-down : ∀ d {n′ n} (le : n′ ≤′ n) (c : Desc ΘL ΘR)
  → DownΩ (leafBelow d le c)
leafBelow-down d {n′} le c {k} {k′} k′≤k w τL τR r
    with suc k ≤? n′ | suc k′ ≤? n′
... | yes lt | yes lt′ =
  descBelow-down d _ _ k′≤k w (renameDesc τL τR c) r
... | yes lt | no ¬lt′ = ⊥-elim (¬lt′ (≤-trans (s≤s k′≤k) lt))
... | no _ | _ = ⊥-elim r

descG-mono : ∀ {m n} (le : m ≤′ n) {w w′} (e : w′ ⊒ w)
    (c : Desc (ΔL w) (ΔR w)) {V V′}
  → descG le w c V V′
  → descG le w′ (renameDesc (ρL e) (ρR e) c)
      (renameᵗᵐ (ρL e) V) (renameᵗᵐ (ρR e) V′)
descG-mono {m} le e (desc p env envR) r =
  G→G≤ le p _
    (G-resp m p _ (envI-transport (ρL e) (ρR e) env envR)
      (G-mono m p e (good-envI {env = env} {envR = envR}) (G≤→G le p _ r)))

descG-down : ∀ {m n m′ n′} (le : m ≤′ n) (le′ : m′ ≤′ n′)
  → m′ ≤ m → ∀ w (c : Desc (ΔL w) (ΔR w)) {V V′}
  → descG le w c V V′ → descG le′ w c V V′
descG-down le le′ m′≤m w (desc p env envR) r =
  G→G≤ le′ p w
    (G-down m′≤m p w (good-envI {env = env} {envR = envR})
      (G≤→G le p w r))

leafG-mono : ∀ {n′ n} (le : n′ ≤′ n) (c : Desc ΘL ΘR)
  → MonoΩ (leafG le c)
leafG-mono {n′ = n′} le c k w τL τR {w′} e {V} {V′} r with k ≤? n′
... | yes k≤n′ =
  subst (λ c′ → descG (≤′-trans (≤⇒≤′ k≤n′) le) w′ c′
                  (renameᵗᵐ (ρL e) V) (renameᵗᵐ (ρR e) V′))
    (renameDesc-∘ (ρL e) τL (ρR e) τR c)
    (descG-mono _ e (renameDesc τL τR c) r)
... | no _ = r

leafG-down : ∀ {n′ n} (le : n′ ≤′ n) (c : Desc ΘL ΘR)
  → DownΩ (leafG le c)
leafG-down {n′ = n′} le c {k} {k′} k′≤k w τL τR r with k ≤? n′ | k′ ≤? n′
... | yes k≤n′ | yes k′≤n′ =
  descG-down _ _ k′≤k w (renameDesc τL τR c) r
... | yes k≤n′ | no ¬k′≤n′ = ⊥-elim (¬k′≤n′ (≤-trans k′≤k k≤n′))
... | no _ | _ = ⊥-elim r

leafBelow-good : ∀ d {n′ n} (le : n′ ≤′ n) (c : Desc ΘL ΘR)
  → GoodLeaf (sem (leafBelow d le c))
leafBelow-good d le c =
  good-sem (leafBelow-mono d le c) (leafBelow-down d le c)

leafG-good : ∀ {n′ n} (le : n′ ≤′ n) (c : Desc ΘL ΘR)
  → GoodLeaf (sem (leafG le c))
leafG-good le c = good-sem (leafG-mono le c) (leafG-down le c)

onlyLeaf-good : ∀ d {n′ n} (le : n′ ≤′ n) (c : Desc ΘL ΘR)
  → GoodLeaf (sem (onlyLeaf d le c))
onlyLeaf-good ≺ le c = leafBelow-good ≺ le c
onlyLeaf-good ≻ le c = leafG-good le c

⊤Ω-good : GoodLeaf (sem (⊤Ω {ΘL} {ΘR}))
⊤Ω-good = good-sem (λ k w τL τR e r → r) (λ le w τL τR r → r)

------------------------------------------------------------------------
-- Good interpretations stay good
------------------------------------------------------------------------

GoodLeaf-transport : ∀ {ΘL′ ΘR′} (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′)
    {l : Leaf ΘL ΘR}
  → GoodLeaf l → GoodLeaf (transportLeaf σL σR l)
GoodLeaf-transport σL σR good-syn = good-syn
GoodLeaf-transport σL σR (good-sem {R = R} mono down) =
  good-sem
    (λ k w τL τR {w′} e {V} {V′} r →
      subst₂ (λ a b → R k w′ a b (renameᵗᵐ (ρL e) V) (renameᵗᵐ (ρR e) V′))
        (sym (∘↪-assoc (ρL e) τL σL)) (sym (∘↪-assoc (ρR e) τR σR))
        (mono k w (τL ∘↪ σL) (τR ∘↪ σR) e r))
    (λ le w τL τR r → down le w (τL ∘↪ σL) (τR ∘↪ σR) r)

GoodI-↑ : ∀ {w w′ : World} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → GoodI δ → (e : w′ ⊒ w) → GoodI (δ ↑ᴵ e)
GoodI-↑ g e X = GoodLeaf-transport (ρL e) (ρR e) (g X)

GoodI-extPairI : ∀ {T T′} {l : Leaf ΘL ΘR} {δ : Interp Δ Δ′ ΘL ΘR}
  → GoodLeaf l → GoodI δ → GoodI (extPairI T T′ l δ)
GoodI-extPairI gl g Fin.zero = gl
GoodI-extPairI gl g (Fin.suc X) = g X

GoodI-extOnlyI : ∀ {T} {l : Leaf ΘL ΘR} {δ : Interp Δ Δ′ ΘL ΘR}
  → GoodLeaf l → GoodI δ → GoodI (extOnlyI T l δ)
GoodI-extOnlyI gl g Fin.zero = gl
GoodI-extOnlyI gl g (Fin.suc X) = g X

GoodI-extDeadI : ∀ {T} {δ : Interp Δ Δ′ ΘL ΘR}
  → GoodI δ → GoodI (extDeadI T δ)
GoodI-extDeadI g Fin.zero = ⊤Ω-good
GoodI-extDeadI g (Fin.suc X) = g X
