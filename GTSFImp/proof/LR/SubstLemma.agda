module proof.LR.SubstLemma where

-- File Charter:
--   * The substitution lemma for the value relation (notes/logrel-dgg.md,
--     Section 6.9, item 4): relating at `p : A ⊑ B` with the bound
--     variable read at `q : T ⊑ T′` is relating at the derivation of
--     `A [ T ] ⊑ B [ T′ ]` that `•⊑•` carries.
--   * First a renaming lemma: the value relation at a renamed derivation,
--     under an interpretation that agrees along the renaming, is the
--     value relation at the original.  The substitution lemma needs it
--     for the weakenings under binders.
--   * Then the substitution lemma for a substitution of derivations
--     (`proof.LR.PrecisionSubst`): the interpretations agree on the
--     types, on the left-only variables, and, below a stage bound, on
--     the paired variables, where the leaf of the first is the value
--     relation of the second at the substituted derivation.  The bound
--     is there because the semantic leaf of a type application's bound
--     variable is empty from its stage on.
--   * Both lemmas are one induction on the derivation and the stage,
--     mirroring `𝒱-resp`; each case gives both directions.
--   * The `•⊑•` instance: a type application's bound variable is read
--     by the `∀⊑∀` clause through a descriptor of `q` and the
--     interpretation's own entries.  Uniqueness of precision
--     (`proof.LR.PrecisionUnique`) replaces the substituted derivation
--     by the premise of `•⊑•`.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _<_; _≤′_; ≤′-refl; ≤′-step;
  _≤?_)
open import Data.Nat.Properties using (≤′⇒≤; ≤⇒≤′; ≤-<-trans; <-trans;
  n<1+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import CastTerms using (Term; renameᵗᵐ; `_; ƛ_; _·_; Λ_; _⦂∀_[_];
  $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import proof.DGG.CenterRename using (_∘↪_)
open import proof.TypeInTermSubst using (renameᵗ-id)
open import proof.LR.WorldProps
open import proof.LR.InterpProps
open import proof.LR.Monotone using (𝒱<→𝒱; 𝒱→𝒱<; envI-transport)
open import proof.LR.PrecisionSubst
open import proof.LR.PrecisionUnique using (⊑-unique)

private
  variable
    Δ Δ′ Δ₁ Δ₁′ Δ₂ Δ₂′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- Logical equivalence
------------------------------------------------------------------------

infix 3 _⇔_

record _⇔_ (P Q : Set) : Set where
  constructor iff
  field
    to : P → Q
    from : Q → P

open _⇔_ public

⇔-id : ∀ {P} → P ⇔ P
⇔-id = iff (λ r → r) (λ r → r)

⇔-trans : ∀ {P Q R} → P ⇔ Q → Q ⇔ R → P ⇔ R
⇔-trans f g = iff (λ r → to g (to f r)) (λ r → from f (from g r))

leafRel-⇔ : ∀ d n w {l l′ : Leaf (ΔL w) (ΔR w)} → l ≈ˡ l′
  → ∀ {Vl Vr} → leafRel d n w l Vl Vr ⇔ leafRel d n w l′ Vl Vr
leafRel-⇔ d n w h =
  iff (leafRel-resp d n w h) (leafRel-resp d n w (≈ˡ-sym h))

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

substᵗ-∘ : ∀ {Δ₁ Δ₂ Δ₃} (τ : Δ₂ ⇒ˢ Δ₃) (σ : Δ₁ ⇒ˢ Δ₂) (A : Ty Δ₁)
  → substᵗ τ (substᵗ σ A) ≡ substᵗ (λ X → substᵗ τ (σ X)) A
substᵗ-∘ τ σ (＇ X) = refl
substᵗ-∘ τ σ (‵ ι) = refl
substᵗ-∘ τ σ ★ = refl
substᵗ-∘ τ σ (A ⇒ B)
  rewrite substᵗ-∘ τ σ A | substᵗ-∘ τ σ B = refl
substᵗ-∘ τ σ (`∀ A) = cong `∀
  (trans (substᵗ-∘ (extsᵗ τ) (extsᵗ σ) A) (substᵗ-cong A exts-comp))
  where
  exts-comp : ∀ X
    → substᵗ (extsᵗ τ) (extsᵗ σ X) ≡ extsᵗ (λ Y → substᵗ τ (σ Y)) X
  exts-comp Fin.zero = refl
  exts-comp (Fin.suc X) = substᵗ-shift τ (σ X)

•ˢ-shift : ∀ (T : Ty Δ′) (σ : Δ ⇒ˢ Δ′) (A : Ty Δ)
  → substᵗ (T •ˢ σ) (⇑ᵗ A) ≡ substᵗ σ A
•ˢ-shift T σ A =
  trans (substᵗ-rename (T •ˢ σ) Fin.suc A) (substᵗ-cong A (λ X → refl))

-- the type annotations of the `∀` clauses
annot-ren : ∀ {Θ} {f : Δ₁ ⇒ˢ Θ} {g : Δ₂ ⇒ˢ Θ} {ρ : Δ₁ ⇒ʳ Δ₂}
  → (∀ X → f X ≡ g (ρ X))
  → ∀ A → substᵗ (extsᵗ f) A ≡ substᵗ (extsᵗ g) (renameᵗ (extᵗ ρ) A)
annot-ren {f = f} {g} {ρ} h A =
  trans (substᵗ-cong A pw) (sym (substᵗ-rename (extsᵗ g) (extᵗ ρ) A))
  where
  pw : ∀ X → extsᵗ f X ≡ extsᵗ g (extᵗ ρ X)
  pw Fin.zero = refl
  pw (Fin.suc X) = cong ⇑ᵗ (h X)

annot-subst : ∀ {Θ} {f : Δ₁ ⇒ˢ Θ} {g : Δ₂ ⇒ˢ Θ} {σ : Δ₁ ⇒ˢ Δ₂}
  → (∀ X → f X ≡ substᵗ g (σ X))
  → ∀ A → substᵗ (extsᵗ f) A ≡ substᵗ (extsᵗ g) (substᵗ (extsᵗ σ) A)
annot-subst {f = f} {g} {σ} h A =
  trans (substᵗ-cong A pw) (sym (substᵗ-∘ (extsᵗ g) (extsᵗ σ) A))
  where
  pw : ∀ X → extsᵗ f X ≡ substᵗ (extsᵗ g) (extsᵗ σ X)
  pw Fin.zero = refl
  pw (Fin.suc X) = trans (cong ⇑ᵗ (h X)) (sym (substᵗ-shift g (σ X)))

-- stage bounds
below : ∀ {a b N} → a ≤′ b → b < N → a < N
below le lt = ≤-<-trans (≤′⇒≤ le) lt

pred< : ∀ {k N} → suc k < N → k < N
pred< {k} lt = <-trans (n<1+n k) lt

------------------------------------------------------------------------
-- Derivations moved along an equation of types
------------------------------------------------------------------------

𝒱-substR : ∀ d n {Ψ : Corr Δ Δ′} {A B₁ B₂} (eq : B₁ ≡ B₂)
    (s : Ψ ⊢ A ⊑ B₁) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → 𝒱 d n s w δ V V′ ⇔ 𝒱 d n (subst (λ C → Ψ ⊢ A ⊑ C) eq s) w δ V V′
𝒱-substR d n refl s w = ⇔-id

-- a paired variable
𝒱-XY : ∀ d n {Ψ : Corr Δ Δ′} {X Y} (x : Ψ ∋ X ↔ Y) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → leafRel d n w (leaf δ X) V V′ ⇔ 𝒱 d n (X⊑Y x) w δ V V′
𝒱-XY ≺ n x w = ⇔-id
𝒱-XY ≻ n x w = ⇔-id

-- a left-only variable, at a type equal to it
𝒱-X★ : ∀ d n {Ψ : Corr Δ Δ′} {X C} (eq : ＇ X ≡ C) (o : Ψ ∋ X only) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → leafRel d n w (leaf δ X) V V′
    ⇔ 𝒱 d n (subst (λ C → Ψ ⊢ C ⊑ ★) eq (X⊑★ o)) w δ V V′
𝒱-X★ ≺ n refl o w = ⇔-id
𝒱-X★ ≻ n refl o w = ⇔-id

G-X★ : ∀ k {Ψ : Corr Δ Δ′} {X C} (eq : ＇ X ≡ C) (o : Ψ ∋ X only) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → leafRel ≻ (suc k) w (leaf δ X) V V′
    ⇔ G (suc k) (subst (λ C → Ψ ⊢ C ⊑ ★) eq (X⊑★ o)) w δ V V′
G-X★ k refl o w = ⇔-id

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

record RenI {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (R : CRen Ψ Ψ′)
    (δ₁ : Interp Δ₁ Δ₁′ ΘL ΘR) (δ₂ : Interp Δ₂ Δ₂′ ΘL ΘR) : Set₁ where
  field
    rl≡ : ∀ X → δl δ₁ X ≡ δl δ₂ (ρl R X)
    rr≡ : ∀ Y → δr δ₁ Y ≡ δr δ₂ (ρr R Y)
    rleaf : ∀ X → leaf δ₁ X ≈ˡ leaf δ₂ (ρl R X)

open RenI public

module _ {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} {R : CRen Ψ Ψ′}
    {δ₁ : Interp Δ₁ Δ₁′ ΘL ΘR} {δ₂ : Interp Δ₂ Δ₂′ ΘL ΘR} where

  RenI-transport : ∀ {ΘL′ ΘR′} (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′)
    → RenI R δ₁ δ₂ → RenI R (transportI σL σR δ₁) (transportI σL σR δ₂)
  rl≡ (RenI-transport σL σR h) X =
    cong (renameᵗ (toRenameᵗ σL)) (rl≡ h X)
  rr≡ (RenI-transport σL σR h) Y =
    cong (renameᵗ (toRenameᵗ σR)) (rr≡ h Y)
  rleaf (RenI-transport σL σR h) X = transportLeaf-resp σL σR (rleaf h X)

  RenI-extPair : ∀ {T T′} {l : Leaf ΘL ΘR} → RenI R δ₁ δ₂
    → RenI (ext-pairᴿ R) (extPairI T T′ l δ₁) (extPairI T T′ l δ₂)
  rl≡ (RenI-extPair h) Fin.zero = refl
  rl≡ (RenI-extPair h) (Fin.suc X) = rl≡ h X
  rr≡ (RenI-extPair h) Fin.zero = refl
  rr≡ (RenI-extPair h) (Fin.suc Y) = rr≡ h Y
  rleaf (RenI-extPair h) Fin.zero = ≈ˡ-refl
  rleaf (RenI-extPair h) (Fin.suc X) = rleaf h X

  RenI-extOnly : ∀ {T} {l : Leaf ΘL ΘR} → RenI R δ₁ δ₂
    → RenI (ext-onlyᴿ R) (extOnlyI T l δ₁) (extOnlyI T l δ₂)
  rl≡ (RenI-extOnly h) Fin.zero = refl
  rl≡ (RenI-extOnly h) (Fin.suc X) = rl≡ h X
  rr≡ (RenI-extOnly h) Y = rr≡ h Y
  rleaf (RenI-extOnly h) Fin.zero = ≈ˡ-refl
  rleaf (RenI-extOnly h) (Fin.suc X) = rleaf h X

  RenI-extDead : ∀ {T} → RenI R δ₁ δ₂
    → RenI (ext-deadᴿ R) (extDeadI T δ₁) (extDeadI T δ₂)
  rl≡ (RenI-extDead h) Fin.zero = refl
  rl≡ (RenI-extDead h) (Fin.suc X) = rl≡ h X
  rr≡ (RenI-extDead h) Y = rr≡ h Y
  rleaf (RenI-extDead h) Fin.zero = ≈ˡ-refl
  rleaf (RenI-extDead h) (Fin.suc X) = rleaf h X

RenI-↑ : ∀ {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} {R : CRen Ψ Ψ′}
    {w w′ : World} {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
    {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
  → RenI R δ₁ δ₂ → (e : w′ ⊒ w) → RenI R (δ₁ ↑ᴵ e) (δ₂ ↑ᴵ e)
RenI-↑ h e = RenI-transport (ρL e) (ρR e) h

-- the weakenings, after a transport
module _ {Ψ : Corr Δ Δ′} {ΘL′ ΘR′} (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′)
    {δ : Interp Δ Δ′ ΘL ΘR} where

  RenI-wkPair : ∀ {T T′} {l : Leaf ΘL ΘR}
    → RenI (wk-pairᴿ {Ψ = Ψ}) (transportI σL σR δ)
        (transportI σL σR (extPairI T T′ l δ))
  rl≡ RenI-wkPair X = refl
  rr≡ RenI-wkPair Y = refl
  rleaf RenI-wkPair X = ≈ˡ-refl

  RenI-wkOnly : ∀ {T} {l : Leaf ΘL ΘR}
    → RenI (wk-onlyᴿ {Ψ = Ψ}) (transportI σL σR δ)
        (transportI σL σR (extOnlyI T l δ))
  rl≡ RenI-wkOnly X = refl
  rr≡ RenI-wkOnly Y = refl
  rleaf RenI-wkOnly X = ≈ˡ-refl

  RenI-wkDead : ∀ {T}
    → RenI (wk-deadᴿ {Ψ = Ψ}) (transportI σL σR δ)
        (transportI σL σR (extDeadI T δ))
  rl≡ RenI-wkDead X = refl
  rr≡ RenI-wkDead Y = refl
  rleaf RenI-wkDead X = ≈ˡ-refl

mutual
  𝒱-ren : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (R : CRen Ψ Ψ′)
      {A B} (p : Ψ ⊢ A ⊑ B) w {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → RenI R δ₁ δ₂
    → ∀ {Vl Vr} → 𝒱 d n p w δ₁ Vl Vr ⇔ 𝒱 d n (renᵖ R p) w δ₂ Vl Vr
  𝒱-ren ≺ n R ★⊑★ w h = ⇔-id
  𝒱-ren ≻ n R ★⊑★ w h = G-ren n R ★⊑★ w h
  𝒱-ren ≺ n R ι⊑ι w h = ⇔-id
  𝒱-ren ≻ n R ι⊑ι w h = ⇔-id
  𝒱-ren ≺ n R (X⊑Y {X = X} x) w h = leafRel-⇔ ≺ n w (rleaf h X)
  𝒱-ren ≻ n R (X⊑Y {X = X} x) w h = leafRel-⇔ ≻ n w (rleaf h X)
  𝒱-ren ≺ n R (⇒⊑⇒ p q) w h = funRel-ren ≺ n R p q w h
  𝒱-ren ≻ n R (⇒⊑⇒ p q) w h = funRel-ren ≻ n R p q w h
  𝒱-ren ≺ n R (∀⊑∀ p) w h = allPair-ren ≺ n R p w h
  𝒱-ren ≻ n R (∀⊑∀ p) w h = allPair-ren ≻ n R p w h
  𝒱-ren ≺ n R (⇒⊑★ p q) w h = funStar-ren ≺ n R p q w h
  𝒱-ren ≻ n R (⇒⊑★ p q) w h = G-ren n R (⇒⊑★ p q) w h
  𝒱-ren ≺ n R ι⊑★ w h = ⇔-id
  𝒱-ren ≻ n R ι⊑★ w h = G-ren n R ι⊑★ w h
  𝒱-ren ≺ n R (X⊑★ {X = X} x) w h = leafRel-⇔ ≺ n w (rleaf h X)
  𝒱-ren ≻ n R (X⊑★ {X = X} x) w h = leafRel-⇔ ≻ n w (rleaf h X)
  𝒱-ren ≺ n R (∀⊑ a z p) w h = allOnly-ren ≺ n R p w h
  𝒱-ren ≻ n R (∀⊑ {B = ★} a z p) w h = G-ren n R (∀⊑ a z p) w h
  𝒱-ren ≻ n R (∀⊑ {B = ＇ Y} a z p) w h = allOnly-ren ≻ n R p w h
  𝒱-ren ≻ n R (∀⊑ {B = ‵ ι} a z p) w h = allOnly-ren ≻ n R p w h
  𝒱-ren ≻ n R (∀⊑ {B = B ⇒ C} a z p) w h = allOnly-ren ≻ n R p w h
  𝒱-ren ≻ n R (∀⊑ {B = `∀ B} a z p) w h = allOnly-ren ≻ n R p w h
  𝒱-ren ≺ n R ∀★⊑★ w h = ⇔-id
  𝒱-ren ≻ n R ∀★⊑★ w h = G-ren n R ∀★⊑★ w h
  𝒱-ren ≺ n R (∀⊑★ ns p) w h = allDeadStar-ren ≺ n R p w h
  𝒱-ren ≻ n R (∀⊑★ ns p) w h = G-ren n R (∀⊑★ ns p) w h
  𝒱-ren ≺ n R bot-elim w h = iff (λ ()) (λ ())
  𝒱-ren ≻ n R bot-elim w h = iff (λ ()) (λ ())
  𝒱-ren ≺ n R bot⊑★ w h = iff (λ ()) (λ ())
  𝒱-ren ≻ n R bot⊑★ w h = iff (λ ()) (λ ())

  𝒱≤-ren : ∀ d {n′ n} (le : n′ ≤′ n) {Ψ : Corr Δ₁ Δ₁′}
      {Ψ′ : Corr Δ₂ Δ₂′} (R : CRen Ψ Ψ′) {A B} (p : Ψ ⊢ A ⊑ B) w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → RenI R δ₁ δ₂
    → ∀ {Vl Vr} → 𝒱≤ d le p w δ₁ Vl Vr ⇔ 𝒱≤ d le (renᵖ R p) w δ₂ Vl Vr
  𝒱≤-ren d {n′} ≤′-refl R p w h = 𝒱-ren d n′ R p w h
  𝒱≤-ren d (≤′-step le) R p w h = 𝒱≤-ren d le R p w h

  G-ren : ∀ n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (R : CRen Ψ Ψ′)
      {A} (p : Ψ ⊢ A ⊑ ★) w {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → RenI R δ₁ δ₂
    → ∀ {Vl Vr} → G n p w δ₁ Vl Vr ⇔ G n (renᵖ R p) w δ₂ Vl Vr
  G-ren zero R p w h = ⇔-id
  G-ren (suc k) R ★⊑★ w h = ⇔-id
  G-ren (suc k) R (⇒⊑★ p q) w h = funStar-ren ≻ k R p q w h
  G-ren (suc k) R ι⊑★ w h = ⇔-id
  G-ren (suc k) R (X⊑★ {X = X} x) w h = leafRel-⇔ ≻ (suc k) w (rleaf h X)
  G-ren (suc k) R (∀⊑ a z p) w h = allOnly-ren ≻ k R p w h
  G-ren (suc k) R ∀★⊑★ w h = ⇔-id
  G-ren (suc k) R (∀⊑★ ns p) w h = allDeadStar-ren ≻ k R p w h
  G-ren (suc k) R bot⊑★ w h = iff (λ ()) (λ ())

  funRel-ren : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (R : CRen Ψ Ψ′)
      {A A′ B B′} (p : Ψ ⊢ A ⊑ A′) (q : Ψ ⊢ B ⊑ B′) w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → RenI R δ₁ δ₂
    → ∀ {Vl Vr} → funRel d n p q w δ₁ Vl Vr
        ⇔ funRel d n (renᵖ R p) (renᵖ R q) w δ₂ Vl Vr
  funRel-ren d n R p q w h =
    iff (λ r e le Wl Wr a →
           ℰᵍ-map d _ _
             (λ le′ w″ e′ V V′ →
               to (𝒱≤-ren d (≤′-trans le′ le) R q w″
                    (RenI-↑ (RenI-↑ h e) e′)))
             (r e le Wl Wr (from (𝒱≤-ren d le R p _ (RenI-↑ h e)) a)))
        (λ r e le Wl Wr a →
           ℰᵍ-map d _ _
             (λ le′ w″ e′ V V′ →
               from (𝒱≤-ren d (≤′-trans le′ le) R q w″
                      (RenI-↑ (RenI-↑ h e) e′)))
             (r e le Wl Wr (to (𝒱≤-ren d le R p _ (RenI-↑ h e)) a)))

  funStar-ren : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (R : CRen Ψ Ψ′) {A B} (p : Ψ ⊢ A ⊑ ★) (q : Ψ ⊢ B ⊑ ★) w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → RenI R δ₁ δ₂
    → ∀ {Vl Vr} → funStar d n p q w δ₁ Vl Vr
        ⇔ funStar d n (renᵖ R p) (renᵖ R q) w δ₂ Vl Vr
  funStar-ren d n R p q w h {Vr = ` x} = iff (λ ()) (λ ())
  funStar-ren d n R p q w h {Vr = ƛ M} = iff (λ ()) (λ ())
  funStar-ren d n R p q w h {Vr = L · M} = iff (λ ()) (λ ())
  funStar-ren d n R p q w h {Vr = Λ M} = iff (λ ()) (λ ())
  funStar-ren d n R p q w h {Vr = L ⦂∀ C [ T ]} = iff (λ ()) (λ ())
  funStar-ren d n R p q w h {Vr = $ κ} = iff (λ ()) (λ ())
  funStar-ren d n R p q w h {Vr = L ⊕[ op ] M} = iff (λ ()) (λ ())
  funStar-ren d n R p q w h {Vr = Wr ⟨ c ⟩} =
    iff (λ r → proj₁ r , to (funRel-ren d n R p q w h) (proj₂ r))
        (λ r → proj₁ r , from (funRel-ren d n R p q w h) (proj₂ r))
  funStar-ren d n R p q w h {Vr = M ↑ c} = iff (λ ()) (λ ())
  funStar-ren d n R p q w h {Vr = M ↓ c} = iff (λ ()) (λ ())
  funStar-ren d n R p q w h {Vr = blame} = iff (λ ()) (λ ())

  allPair-ren : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (R : CRen Ψ Ψ′) {A B} (p : pair Ψ ⊢ A ⊑ B) w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → RenI R δ₁ δ₂
    → ∀ {Vl Vr} → allPair d n p w δ₁ Vl Vr
        ⇔ allPair d n (renᵖ (ext-pairᴿ R) p) w δ₂ Vl Vr
  allPair-ren d n R {A = A} {B = B} p w h {Vl = Vl} {Vr = Vr} =
    iff (λ r e le c →
           ℰᵍ-≡
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTy c ])
               (annot-ren (rl≡ (RenI-↑ h e)) A))
             (cong (λ C → renameᵗᵐ (ρR e) Vr ⦂∀ C [ rightTy c ])
               (annot-ren (rr≡ (RenI-↑ h e)) B))
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 to (𝒱≤-ren d (≤′-trans le′ le) (ext-pairᴿ R) p w″
                      (RenI-↑ (RenI-extPair {T = leftTy c}
                        {T′ = rightTy c} (RenI-↑ h e)) e′)))
               (r e le c)))
        (λ r e le c →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTy c ])
               (annot-ren (rl≡ (RenI-↑ h e)) A)))
             (sym (cong (λ C → renameᵗᵐ (ρR e) Vr ⦂∀ C [ rightTy c ])
               (annot-ren (rr≡ (RenI-↑ h e)) B)))
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 from (𝒱≤-ren d (≤′-trans le′ le) (ext-pairᴿ R) p w″
                        (RenI-↑ (RenI-extPair {T = leftTy c}
                          {T′ = rightTy c} (RenI-↑ h e)) e′)))
               (r e le c)))

  allOnly-ren : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (R : CRen Ψ Ψ′) {A B} (p : only Ψ ⊢ A ⊑ B) w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → RenI R δ₁ δ₂
    → ∀ {Vl Vr} → allOnly d n p w δ₁ Vl Vr
        ⇔ allOnly d n (renᵖ (ext-onlyᴿ R) p) w δ₂ Vl Vr
  allOnly-ren d n R {A = A} p w h {Vl = Vl} =
    iff (λ r e le c →
           ℰᵍ-≡
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTy c ])
               (annot-ren (rl≡ (RenI-↑ h e)) A))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 to (𝒱≤-ren d (≤′-trans le′ le) (ext-onlyᴿ R) p w″
                      (RenI-↑ (RenI-extOnly {T = leftTy c}
                        (RenI-↑ h e)) e′)))
               (r e le c)))
        (λ r e le c →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTy c ])
               (annot-ren (rl≡ (RenI-↑ h e)) A)))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 from (𝒱≤-ren d (≤′-trans le′ le) (ext-onlyᴿ R) p w″
                        (RenI-↑ (RenI-extOnly {T = leftTy c}
                          (RenI-↑ h e)) e′)))
               (r e le c)))

  allDead-ren : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (R : CRen Ψ Ψ′) {A} (p : dead Ψ ⊢ A ⊑ ★) w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → RenI R δ₁ δ₂
    → ∀ {Vl Vr} → allDead d n p w δ₁ Vl Vr
        ⇔ allDead d n (renᵖ (ext-deadᴿ R) p) w δ₂ Vl Vr
  allDead-ren d n R {A = A} p w h {Vl = Vl} =
    iff (λ r e le T T′ →
           ℰᵍ-≡
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ T ])
               (annot-ren (rl≡ (RenI-↑ h e)) A))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 to (𝒱≤-ren d (≤′-trans le′ le) (ext-deadᴿ R) p w″
                      (RenI-↑ (RenI-extDead {T = T} (RenI-↑ h e)) e′)))
               (r e le T T′)))
        (λ r e le T T′ →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ T ])
               (annot-ren (rl≡ (RenI-↑ h e)) A)))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 from (𝒱≤-ren d (≤′-trans le′ le) (ext-deadᴿ R) p w″
                        (RenI-↑ (RenI-extDead {T = T} (RenI-↑ h e)) e′)))
               (r e le T T′)))

  allDeadStar-ren : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (R : CRen Ψ Ψ′) {A} (p : dead Ψ ⊢ A ⊑ ★) w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → RenI R δ₁ δ₂
    → ∀ {Vl Vr} → allDeadStar d n p w δ₁ Vl Vr
        ⇔ allDeadStar d n (renᵖ (ext-deadᴿ R) p) w δ₂ Vl Vr
  allDeadStar-ren d n R p w h {Vr = ` x} = iff (λ ()) (λ ())
  allDeadStar-ren d n R p w h {Vr = ƛ M} = iff (λ ()) (λ ())
  allDeadStar-ren d n R p w h {Vr = L · M} = iff (λ ()) (λ ())
  allDeadStar-ren d n R p w h {Vr = Λ M} = iff (λ ()) (λ ())
  allDeadStar-ren d n R p w h {Vr = L ⦂∀ C [ T ]} = iff (λ ()) (λ ())
  allDeadStar-ren d n R p w h {Vr = $ κ} = iff (λ ()) (λ ())
  allDeadStar-ren d n R p w h {Vr = L ⊕[ op ] M} = iff (λ ()) (λ ())
  allDeadStar-ren d n R p w h {Vr = Wr ⟨ c ⟩} =
    iff (λ r → proj₁ r , to (allDead-ren d n R p w h) (proj₂ r))
        (λ r → proj₁ r , from (allDead-ren d n R p w h) (proj₂ r))
  allDeadStar-ren d n R p w h {Vr = M ↑ c} = iff (λ ()) (λ ())
  allDeadStar-ren d n R p w h {Vr = M ↓ c} = iff (λ ()) (λ ())
  allDeadStar-ren d n R p w h {Vr = blame} = iff (λ ()) (λ ())

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

record SubI {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (S : PSub Ψ Ψ′)
    (d : Dir) (N : ℕ) (w : World)
    (δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)) (δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w))
    : Set₁ where
  field
    sl≡ : ∀ X → δl δ₁ X ≡ substᵗ (δl δ₂) (σl S X)
    sr≡ : ∀ Y → δr δ₁ Y ≡ substᵗ (δr δ₂) (σr S Y)
    sonly : ∀ {X} (x : Ψ ∋ X only) → leaf δ₁ X ≈ˡ leaf δ₂ (σvar S x)
    spair : ∀ {X Y} (x : Ψ ∋ X ↔ Y) {w′} (e : w′ ⊒ w) {k} → k < N
      → ∀ {Vl Vr} → leafRel d k w′ (leaf (δ₁ ↑ᴵ e) X) Vl Vr
          ⇔ 𝒱 d k (σ↔ S x) w′ (δ₂ ↑ᴵ e) Vl Vr

open SubI public

module _ {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} {S : PSub Ψ Ψ′} {d N}
    {w : World} {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
    {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)} where

  SubI-↑ : ∀ {w′} → SubI S d N w δ₁ δ₂ → (e : w′ ⊒ w)
    → SubI S d N w′ (δ₁ ↑ᴵ e) (δ₂ ↑ᴵ e)
  sl≡ (SubI-↑ h e) X =
    trans (cong (renameᵗ (toRenameᵗ (ρL e))) (sl≡ h X))
      (renameᵗ-subst (toRenameᵗ (ρL e)) (δl δ₂) (σl S X))
  sr≡ (SubI-↑ h e) Y =
    trans (cong (renameᵗ (toRenameᵗ (ρR e))) (sr≡ h Y))
      (renameᵗ-subst (toRenameᵗ (ρR e)) (δr δ₂) (σr S Y))
  sonly (SubI-↑ h e) x = transportLeaf-resp (ρL e) (ρR e) (sonly h x)
  spair (SubI-↑ h e) {X = X} x e′ {k} lt =
    iff (λ r →
           𝒱-resp d k (σ↔ S x) _ (≈ᴵ-sym (↑ᴵ-trans δ₂ e′ e))
             (to (spair h x (⊒-trans e′ e) lt)
               (leafRel-resp d k _ (leaf≈ (↑ᴵ-trans δ₁ e′ e) X) r)))
        (λ r →
           leafRel-resp d k _ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δ₁ e′ e) X))
             (from (spair h x (⊒-trans e′ e) lt)
               (𝒱-resp d k (σ↔ S x) _ (↑ᴵ-trans δ₂ e′ e) r)))

  SubI-extPair : ∀ {T T′} (l : Leaf (ΔL w) (ΔR w)) → SubI S d N w δ₁ δ₂
    → SubI (exts-pairˢ S) d N w (extPairI T T′ l δ₁) (extPairI T T′ l δ₂)
  sl≡ (SubI-extPair l h) Fin.zero = refl
  sl≡ (SubI-extPair {T = T} l h) (Fin.suc X) =
    trans (sl≡ h X) (sym (•ˢ-shift T (δl δ₂) (σl S X)))
  sr≡ (SubI-extPair l h) Fin.zero = refl
  sr≡ (SubI-extPair {T′ = T′} l h) (Fin.suc Y) =
    trans (sr≡ h Y) (sym (•ˢ-shift T′ (δr δ₂) (σr S Y)))
  sonly (SubI-extPair l h) (only-pair x) = sonly h x
  spair (SubI-extPair l h) ↔-here e {k} lt = 𝒱-XY d k ↔-here _
  spair (SubI-extPair l h) (↔-pair x) e {k} lt =
    ⇔-trans (spair h x e lt)
      (𝒱-ren d k wk-pairᴿ (σ↔ S x) _ (RenI-wkPair (ρL e) (ρR e)))

  SubI-extOnly : ∀ {T} (l : Leaf (ΔL w) (ΔR w)) → SubI S d N w δ₁ δ₂
    → SubI (exts-onlyˢ S) d N w (extOnlyI T l δ₁) (extOnlyI T l δ₂)
  sl≡ (SubI-extOnly l h) Fin.zero = refl
  sl≡ (SubI-extOnly {T = T} l h) (Fin.suc X) =
    trans (sl≡ h X) (sym (•ˢ-shift T (δl δ₂) (σl S X)))
  sr≡ (SubI-extOnly l h) Y = sr≡ h Y
  sonly (SubI-extOnly l h) only-here = ≈ˡ-refl
  sonly (SubI-extOnly l h) (only-only x) = sonly h x
  spair (SubI-extOnly l h) (↔-only x) e {k} lt =
    ⇔-trans (spair h x e lt)
      (⇔-trans (𝒱-ren d k wk-onlyᴿ (σ↔ S x) _ (RenI-wkOnly (ρL e) (ρR e)))
        (𝒱-substR d k (renameᵗ-id _) (renᵖ wk-onlyᴿ (σ↔ S x)) _))

  SubI-extDead : ∀ {T} → SubI S d N w δ₁ δ₂
    → SubI (exts-deadˢ S) d N w (extDeadI T δ₁) (extDeadI T δ₂)
  sl≡ (SubI-extDead h) Fin.zero = refl
  sl≡ (SubI-extDead {T = T} h) (Fin.suc X) =
    trans (sl≡ h X) (sym (•ˢ-shift T (δl δ₂) (σl S X)))
  sr≡ (SubI-extDead h) Y = sr≡ h Y
  sonly (SubI-extDead h) (only-dead x) = sonly h x
  spair (SubI-extDead h) (↔-dead x) e {k} lt =
    ⇔-trans (spair h x e lt)
      (⇔-trans (𝒱-ren d k wk-deadᴿ (σ↔ S x) _ (RenI-wkDead (ρL e) (ρR e)))
        (𝒱-substR d k (renameᵗ-id _) (renᵖ wk-deadᴿ (σ↔ S x)) _))

  -- a paired variable, read now
  var-⇔ : ∀ {X Y} (x : Ψ ∋ X ↔ Y) {n} → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → leafRel d n w (leaf δ₁ X) Vl Vr
        ⇔ 𝒱 d n (σ↔ S x) w δ₂ Vl Vr
  var-⇔ {X = X} x {n} h lt =
    iff (λ r →
           𝒱-resp d n (σ↔ S x) w (↑ᴵ-refl {w = w} δ₂)
             (to (spair h x (⊒-refl w) lt)
               (leafRel-resp d n w (≈ˡ-sym (leaf≈ (↑ᴵ-refl {w = w} δ₁) X)) r)))
        (λ r →
           leafRel-resp d n w (leaf≈ (↑ᴵ-refl {w = w} δ₁) X)
             (from (spair h x (⊒-refl w) lt)
               (𝒱-resp d n (σ↔ S x) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ₂)) r)))

mutual
  𝒱-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (S : PSub Ψ Ψ′)
      {A B} (p : Ψ ⊢ A ⊑ B) {N} w {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → 𝒱 d n p w δ₁ Vl Vr ⇔ 𝒱 d n (substᵖ S p) w δ₂ Vl Vr
  𝒱-subst ≺ n S ★⊑★ w h lt = ⇔-id
  𝒱-subst ≻ n S ★⊑★ w h lt = G-subst n S ★⊑★ w h lt
  𝒱-subst ≺ n S ι⊑ι w h lt = ⇔-id
  𝒱-subst ≻ n S ι⊑ι w h lt = ⇔-id
  𝒱-subst ≺ n S (X⊑Y x) w h lt = var-⇔ x h lt
  𝒱-subst ≻ n S (X⊑Y x) w h lt = var-⇔ x h lt
  𝒱-subst ≺ n S (⇒⊑⇒ p q) w h lt = funRel-subst ≺ n S p q w h lt
  𝒱-subst ≻ n S (⇒⊑⇒ p q) w h lt = funRel-subst ≻ n S p q w h lt
  𝒱-subst ≺ n S (∀⊑∀ p) w h lt = allPair-subst ≺ n S p w h lt
  𝒱-subst ≻ n S (∀⊑∀ p) w h lt = allPair-subst ≻ n S p w h lt
  𝒱-subst ≺ n S (⇒⊑★ p q) w h lt = funStar-subst ≺ n S p q w h lt
  𝒱-subst ≻ n S (⇒⊑★ p q) w h lt = G-subst n S (⇒⊑★ p q) w h lt
  𝒱-subst ≺ n S ι⊑★ w h lt = ⇔-id
  𝒱-subst ≻ n S ι⊑★ w h lt = G-subst n S ι⊑★ w h lt
  𝒱-subst ≺ n S (X⊑★ x) w h lt =
    ⇔-trans (leafRel-⇔ ≺ n w (sonly h x))
      (𝒱-X★ ≺ n (σvar≡ S x) (σvar-only S x) w)
  𝒱-subst ≻ n S (X⊑★ x) w h lt =
    ⇔-trans (leafRel-⇔ ≻ n w (sonly h x))
      (𝒱-X★ ≻ n (σvar≡ S x) (σvar-only S x) w)
  𝒱-subst ≺ n S (∀⊑ a z p) w h lt = allOnly-subst ≺ n S p w h lt
  𝒱-subst ≻ n S (∀⊑ {B = ★} a z p) w h lt = G-subst n S (∀⊑ a z p) w h lt
  𝒱-subst ≻ n S (∀⊑ {B = ＇ Y} a z p) w h lt = ⊥-elim (∀⊑-var⊥ a z p)
  𝒱-subst ≻ n S (∀⊑ {B = ‵ ι} a z p) w h lt =
    allOnly-subst ≻ n S p w h lt
  𝒱-subst ≻ n S (∀⊑ {B = B ⇒ C} a z p) w h lt =
    allOnly-subst ≻ n S p w h lt
  𝒱-subst ≻ n S (∀⊑ {B = `∀ B} a z p) w h lt =
    allOnly-subst ≻ n S p w h lt
  𝒱-subst ≺ n S ∀★⊑★ w h lt = ⇔-id
  𝒱-subst ≻ n S ∀★⊑★ w h lt = G-subst n S ∀★⊑★ w h lt
  𝒱-subst ≺ n S (∀⊑★ ns p) w h lt = allDeadStar-subst ≺ n S p w h lt
  𝒱-subst ≻ n S (∀⊑★ ns p) w h lt = G-subst n S (∀⊑★ ns p) w h lt
  𝒱-subst ≺ n S bot-elim w h lt = iff (λ ()) (λ ())
  𝒱-subst ≻ n S bot-elim w h lt = iff (λ ()) (λ ())
  𝒱-subst ≺ n S bot⊑★ w h lt = iff (λ ()) (λ ())
  𝒱-subst ≻ n S bot⊑★ w h lt = iff (λ ()) (λ ())

  𝒱≤-subst : ∀ d {n′ n} (le : n′ ≤′ n) {Ψ : Corr Δ₁ Δ₁′}
      {Ψ′ : Corr Δ₂ Δ₂′} (S : PSub Ψ Ψ′) {A B} (p : Ψ ⊢ A ⊑ B) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n′ < N
    → ∀ {Vl Vr} → 𝒱≤ d le p w δ₁ Vl Vr ⇔ 𝒱≤ d le (substᵖ S p) w δ₂ Vl Vr
  𝒱≤-subst d {n′} ≤′-refl S p w h lt = 𝒱-subst d n′ S p w h lt
  𝒱≤-subst d (≤′-step le) S p w h lt = 𝒱≤-subst d le S p w h lt

  G-subst : ∀ n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (S : PSub Ψ Ψ′)
      {A} (p : Ψ ⊢ A ⊑ ★) {N} w {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S ≻ N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → G n p w δ₁ Vl Vr ⇔ G n (substᵖ S p) w δ₂ Vl Vr
  G-subst zero S p w h lt = ⇔-id
  G-subst (suc k) S ★⊑★ w h lt = ⇔-id
  G-subst (suc k) S (⇒⊑★ p q) w h lt =
    funStar-subst ≻ k S p q w h (pred< lt)
  G-subst (suc k) S ι⊑★ w h lt = ⇔-id
  G-subst (suc k) S (X⊑★ x) w h lt =
    ⇔-trans (leafRel-⇔ ≻ (suc k) w (sonly h x))
      (G-X★ k (σvar≡ S x) (σvar-only S x) w)
  G-subst (suc k) S (∀⊑ a z p) w h lt = allOnly-subst ≻ k S p w h (pred< lt)
  G-subst (suc k) S ∀★⊑★ w h lt = ⇔-id
  G-subst (suc k) S (∀⊑★ ns p) w h lt =
    allDeadStar-subst ≻ k S p w h (pred< lt)
  G-subst (suc k) S bot⊑★ w h lt = iff (λ ()) (λ ())

  funRel-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (S : PSub Ψ Ψ′) {A A′ B B′} (p : Ψ ⊢ A ⊑ A′) (q : Ψ ⊢ B ⊑ B′) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → funRel d n p q w δ₁ Vl Vr
        ⇔ funRel d n (substᵖ S p) (substᵖ S q) w δ₂ Vl Vr
  funRel-subst d n S p q w h lt =
    iff (λ r e le Wl Wr a →
           ℰᵍ-map d _ _
             (λ le′ w″ e′ V V′ →
               to (𝒱≤-subst d (≤′-trans le′ le) S q w″
                    (SubI-↑ (SubI-↑ h e) e′) (below (≤′-trans le′ le) lt)))
             (r e le Wl Wr
               (from (𝒱≤-subst d le S p _ (SubI-↑ h e) (below le lt)) a)))
        (λ r e le Wl Wr a →
           ℰᵍ-map d _ _
             (λ le′ w″ e′ V V′ →
               from (𝒱≤-subst d (≤′-trans le′ le) S q w″
                      (SubI-↑ (SubI-↑ h e) e′)
                      (below (≤′-trans le′ le) lt)))
             (r e le Wl Wr
               (to (𝒱≤-subst d le S p _ (SubI-↑ h e) (below le lt)) a)))

  funStar-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (S : PSub Ψ Ψ′) {A B} (p : Ψ ⊢ A ⊑ ★) (q : Ψ ⊢ B ⊑ ★) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → funStar d n p q w δ₁ Vl Vr
        ⇔ funStar d n (substᵖ S p) (substᵖ S q) w δ₂ Vl Vr
  funStar-subst d n S p q w h lt {Vr = ` x} = iff (λ ()) (λ ())
  funStar-subst d n S p q w h lt {Vr = ƛ M} = iff (λ ()) (λ ())
  funStar-subst d n S p q w h lt {Vr = L · M} = iff (λ ()) (λ ())
  funStar-subst d n S p q w h lt {Vr = Λ M} = iff (λ ()) (λ ())
  funStar-subst d n S p q w h lt {Vr = L ⦂∀ C [ T ]} = iff (λ ()) (λ ())
  funStar-subst d n S p q w h lt {Vr = $ κ} = iff (λ ()) (λ ())
  funStar-subst d n S p q w h lt {Vr = L ⊕[ op ] M} = iff (λ ()) (λ ())
  funStar-subst d n S p q w h lt {Vr = Wr ⟨ c ⟩} =
    iff (λ r → proj₁ r , to (funRel-subst d n S p q w h lt) (proj₂ r))
        (λ r → proj₁ r , from (funRel-subst d n S p q w h lt) (proj₂ r))
  funStar-subst d n S p q w h lt {Vr = M ↑ c} = iff (λ ()) (λ ())
  funStar-subst d n S p q w h lt {Vr = M ↓ c} = iff (λ ()) (λ ())
  funStar-subst d n S p q w h lt {Vr = blame} = iff (λ ()) (λ ())

  allPair-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (S : PSub Ψ Ψ′) {A B} (p : pair Ψ ⊢ A ⊑ B) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → allPair d n p w δ₁ Vl Vr
        ⇔ allPair d n (substᵖ (exts-pairˢ S) p) w δ₂ Vl Vr
  allPair-subst d n S {A = A} {B = B} p w h lt {Vl = Vl} {Vr = Vr} =
    iff (λ r e le c →
           ℰᵍ-≡
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTy c ])
               (annot-subst (sl≡ (SubI-↑ h e)) A))
             (cong (λ C → renameᵗᵐ (ρR e) Vr ⦂∀ C [ rightTy c ])
               (annot-subst (sr≡ (SubI-↑ h e)) B))
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 to (𝒱≤-subst d (≤′-trans le′ le) (exts-pairˢ S) p w″
                      (SubI-↑ (SubI-extPair (sem (leafBelow d le c))
                        (SubI-↑ h e)) e′)
                      (below (≤′-trans le′ le) lt)))
               (r e le c)))
        (λ r e le c →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTy c ])
               (annot-subst (sl≡ (SubI-↑ h e)) A)))
             (sym (cong (λ C → renameᵗᵐ (ρR e) Vr ⦂∀ C [ rightTy c ])
               (annot-subst (sr≡ (SubI-↑ h e)) B)))
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 from (𝒱≤-subst d (≤′-trans le′ le) (exts-pairˢ S) p w″
                        (SubI-↑ (SubI-extPair (sem (leafBelow d le c))
                          (SubI-↑ h e)) e′)
                        (below (≤′-trans le′ le) lt)))
               (r e le c)))

  allOnly-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (S : PSub Ψ Ψ′) {A B} (p : only Ψ ⊢ A ⊑ B) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → allOnly d n p w δ₁ Vl Vr
        ⇔ allOnly d n (substᵖ (exts-onlyˢ S) p) w δ₂ Vl Vr
  allOnly-subst d n S {A = A} p w h lt {Vl = Vl} =
    iff (λ r e le c →
           ℰᵍ-≡
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTy c ])
               (annot-subst (sl≡ (SubI-↑ h e)) A))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 to (𝒱≤-subst d (≤′-trans le′ le) (exts-onlyˢ S) p w″
                      (SubI-↑ (SubI-extOnly (sem (onlyLeaf d le c))
                        (SubI-↑ h e)) e′)
                      (below (≤′-trans le′ le) lt)))
               (r e le c)))
        (λ r e le c →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTy c ])
               (annot-subst (sl≡ (SubI-↑ h e)) A)))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 from (𝒱≤-subst d (≤′-trans le′ le) (exts-onlyˢ S) p w″
                        (SubI-↑ (SubI-extOnly (sem (onlyLeaf d le c))
                          (SubI-↑ h e)) e′)
                        (below (≤′-trans le′ le) lt)))
               (r e le c)))

  allDead-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (S : PSub Ψ Ψ′) {A} (p : dead Ψ ⊢ A ⊑ ★) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → allDead d n p w δ₁ Vl Vr
        ⇔ allDead d n (substᵖ (exts-deadˢ S) p) w δ₂ Vl Vr
  allDead-subst d n S {A = A} p w h lt {Vl = Vl} =
    iff (λ r e le T T′ →
           ℰᵍ-≡
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ T ])
               (annot-subst (sl≡ (SubI-↑ h e)) A))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 to (𝒱≤-subst d (≤′-trans le′ le) (exts-deadˢ S) p w″
                      (SubI-↑ (SubI-extDead {T = T} (SubI-↑ h e)) e′)
                      (below (≤′-trans le′ le) lt)))
               (r e le T T′)))
        (λ r e le T T′ →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ T ])
               (annot-subst (sl≡ (SubI-↑ h e)) A)))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 from (𝒱≤-subst d (≤′-trans le′ le) (exts-deadˢ S) p w″
                        (SubI-↑ (SubI-extDead {T = T} (SubI-↑ h e)) e′)
                        (below (≤′-trans le′ le) lt)))
               (r e le T T′)))

  allDeadStar-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (S : PSub Ψ Ψ′) {A} (p : dead Ψ ⊢ A ⊑ ★) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → allDeadStar d n p w δ₁ Vl Vr
        ⇔ allDeadStar d n (substᵖ (exts-deadˢ S) p) w δ₂ Vl Vr
  allDeadStar-subst d n S p w h lt {Vr = ` x} = iff (λ ()) (λ ())
  allDeadStar-subst d n S p w h lt {Vr = ƛ M} = iff (λ ()) (λ ())
  allDeadStar-subst d n S p w h lt {Vr = L · M} = iff (λ ()) (λ ())
  allDeadStar-subst d n S p w h lt {Vr = Λ M} = iff (λ ()) (λ ())
  allDeadStar-subst d n S p w h lt {Vr = L ⦂∀ C [ T ]} = iff (λ ()) (λ ())
  allDeadStar-subst d n S p w h lt {Vr = $ κ} = iff (λ ()) (λ ())
  allDeadStar-subst d n S p w h lt {Vr = L ⊕[ op ] M} = iff (λ ()) (λ ())
  allDeadStar-subst d n S p w h lt {Vr = Wr ⟨ c ⟩} =
    iff (λ r → proj₁ r , to (allDead-subst d n S p w h lt) (proj₂ r))
        (λ r → proj₁ r , from (allDead-subst d n S p w h lt) (proj₂ r))
  allDeadStar-subst d n S p w h lt {Vr = M ↑ c} = iff (λ ()) (λ ())
  allDeadStar-subst d n S p w h lt {Vr = M ↓ c} = iff (λ ()) (λ ())
  allDeadStar-subst d n S p w h lt {Vr = blame} = iff (λ ()) (λ ())

------------------------------------------------------------------------
-- The shared type application
------------------------------------------------------------------------

-- the semantic leaf of the bound variable, below its stage, is the value
-- relation of its descriptor
leafBelow-⇔ : ∀ d {n′ n} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {T T′}
    (q : Φ ⊢ T ⊑ T′) (env : Vec (Entry ΘL ΘR) Δ) (envR : Vec (Ty ΘR) Δ′)
    {k} → k < n′ → ∀ w τL τR {V V′}
  → leafBelow d le (desc q env envR) k w τL τR V V′
    ⇔ 𝒱 d k q w (envI (renameEntries τL τR env)
          (Vec.map (renameᵗ (toRenameᵗ τR)) envR)) V V′
leafBelow-⇔ d {n′} le q env envR {k} lt w τL τR with suc k ≤? n′
leafBelow-⇔ d {n′} le q env envR {k} lt w τL τR | yes lt′ =
  iff (𝒱<→𝒱 d (≤′-trans (≤⇒≤′ lt′) le) q w)
      (𝒱→𝒱< d (≤′-trans (≤⇒≤′ lt′) le) q w)
leafBelow-⇔ d {n′} le q env envR {k} lt w τL τR | no ¬lt = ⊥-elim (¬lt lt)


-- the descriptor's own interpretation, read in a future world
envI-↑ : ∀ {w w′ : World} (e : w′ ⊒ w) {env : Vec (Entry (ΔL w) (ΔR w)) Δ}
    {envR : Vec (Ty (ΔR w)) Δ′} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → δ ≈ᴵ envI env envR
  → envI (renameEntries (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) env)
      (Vec.map (renameᵗ (toRenameᵗ (id↪ᵗ ∘↪ ρR e))) envR)
    ≈ᴵ δ ↑ᴵ e
envI-↑ e {env} {envR} hδ =
  ≈ᴵ-trans (≈ᴵ-sym (envI-transport (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e) env envR))
    (≈ᴵ-trans
      (transportI-≡ (∘↪-idˡ (ρL e)) (∘↪-idˡ (ρR e)) (envI env envR))
      (transportI-resp (ρL e) (ρR e) (≈ᴵ-sym hδ)))

-- the interpretation of the `∀⊑∀` clause, with the descriptor of `q`
-- over the interpretation's own entries, substitutes `q` for the bound
-- variable below the clause's stage
SubI-single : ∀ d {n′ n} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {T T′}
    (q : Φ ⊢ T ⊑ T′) {w} (env : Vec (Entry (ΔL w) (ΔR w)) Δ)
    (envR : Vec (Ty (ΔR w)) Δ′) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → δ ≈ᴵ envI env envR
  → SubI (singleˢ q) d n′ w
      (extPairI (leftTy (desc q env envR)) (rightTy (desc q env envR))
        (sem (leafBelow d le (desc q env envR))) δ)
      δ
sl≡ (SubI-single d le {T = T} q env envR hδ) Fin.zero =
  substᵗ-cong T (λ X → sym (δl≡ hδ X))
sl≡ (SubI-single d le q env envR hδ) (Fin.suc X) = refl
sr≡ (SubI-single d le {T′ = T′} q env envR hδ) Fin.zero =
  substᵗ-cong T′ (λ Y → sym (δr≡ hδ Y))
sr≡ (SubI-single d le q env envR hδ) (Fin.suc Y) = refl
sonly (SubI-single d le q env envR hδ) (only-pair x) = ≈ˡ-refl
spair (SubI-single d le q env envR hδ) ↔-here {w′} e {k} lt =
  iff (λ r →
         𝒱-resp d k q w′ (envI-↑ e {env} {envR} hδ)
           (to (leafBelow-⇔ d le q env envR lt w′
                 (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)) r))
      (λ r →
         from (leafBelow-⇔ d le q env envR lt w′
                (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e))
           (𝒱-resp d k q w′ (≈ᴵ-sym (envI-↑ e {env} {envR} hδ)) r))
spair (SubI-single d le q env envR hδ) (↔-pair x) e {k} lt =
  𝒱-XY d k x _

-- The substitution lemma for `•⊑•`: below the stage of the `∀⊑∀`
-- clause, the body at `p` with the bound variable read at `q` is related
-- exactly when it is related at the premise `r` of `•⊑•`.
𝒱-tyapp : ∀ d {n′ n} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {T T′ A B}
    (q : Φ ⊢ T ⊑ T′) (p : pair Φ ⊢ A ⊑ B)
    (r : Φ ⊢ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ)
    {w} (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′)
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → δ ≈ᴵ envI env envR
  → ∀ {w′} (e : w′ ⊒ w) {k} → k < n′ → ∀ {Vl Vr}
  → 𝒱 d k p w′
      (extPairI (leftTy (desc q env envR)) (rightTy (desc q env envR))
        (sem (leafBelow d le (desc q env envR))) δ ↑ᴵ e) Vl Vr
    ⇔ 𝒱 d k r w′ (δ ↑ᴵ e) Vl Vr
𝒱-tyapp d le q p r env envR {δ} hδ e {k} lt {Vl} {Vr} =
  ⇔-trans
    (𝒱-subst d k (singleˢ q) p _
      (SubI-↑ (SubI-single d le q env envR hδ) e) lt)
    (iff (subst (λ r′ → 𝒱 d k r′ _ (δ ↑ᴵ e) Vl Vr)
           (⊑-unique (substᵖ (singleˢ q) p) r))
         (subst (λ r′ → 𝒱 d k r′ _ (δ ↑ᴵ e) Vl Vr)
           (sym (⊑-unique (substᵖ (singleˢ q) p) r))))
