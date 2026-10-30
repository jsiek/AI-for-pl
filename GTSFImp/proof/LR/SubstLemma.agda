module proof.LR.SubstLemma where

-- File Charter:
--   * The substitution lemma for the value relation (notes/logrel-dgg.md,
--     Section 6.9, item 4): relating at `p : A ⊑ B` with the bound
--     variable read at `q` is relating at the derivation of the
--     substituted types that `•⊑•` or `•⊑` carries.
--   * First a renaming lemma: the value relation at a renamed derivation,
--     under an interpretation that agrees along the renaming, is the
--     value relation at the original.  The substitution lemma needs it
--     for the weakenings under binders.
--   * Then the substitution lemma for a substitution of derivations
--     (`proof.LR.PrecisionSubst`): the interpretations agree on the
--     types and, below a stage bound, at every variable, where the leaf
--     of the first is the value relation of the second at the
--     substituted derivation.  The bound is there because the semantic
--     leaf of a type application's bound variable is empty from its
--     stage on.
--   * The lemma holds at positive stages.  At stage 0 a left-only
--     variable's guarded leaf holds in `≻` while the relation at its
--     substitute may not; but the expression relation never needs a
--     value at stage 0 (`ℰᵍ-map⁺`): a value reached there took all the
--     counted steps.
--   * Both lemmas are one induction on the derivation and the stage,
--     mirroring `𝒱-resp`; each case gives both directions.
--   * The instances: a type application's bound variable is read by
--     the `∀⊑∀` (`•⊑•`) or `∀⊑` (`•⊑`) clause through a descriptor of
--     `q` and the interpretation's own entries.  Uniqueness of
--     precision (`proof.LR.PrecisionUnique`) replaces the substituted
--     derivation by the rule's premise.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤′_; ≤′-refl;
  ≤′-step; _≤?_; s≤s; z≤n)
open import Data.Nat.Properties using (≤′⇒≤; ≤⇒≤′; ≤-<-trans; <-trans;
  n<1+n; ≤-pred; +-identityʳ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
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
open import LR.Steps using (_—→^_[_]_; none)
open import Reduction using ([])
open import proof.DGG.CenterRename using (_∘↪_)
open import proof.TypeInTermSubst using (renameᵗ-id)
open import proof.LR.WorldProps
open import proof.LR.InterpProps
open import proof.LR.Monotone using (𝒱<→𝒱; 𝒱→𝒱<; G≤→G; G→G≤;
  envI-transport)
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

⇔-sym : ∀ {P Q} → P ⇔ Q → Q ⇔ P
⇔-sym f = iff (from f) (to f)

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
-- Stage zero
------------------------------------------------------------------------

-- the expression relation holds at stage 0: every term runs 0 steps
ℰᵍ-zero : ∀ d w {VR : VRel zero w} {Ml Mr} → ℰᵍ d zero w VR Ml Mr
ℰᵍ-zero ≺ w {Ml = Ml} = inj₁ (_ , [] , Ml , none)
ℰᵍ-zero ≻ w {Mr = Mr} = inj₁ (_ , [] , Mr , none)

ℰᵍ-pos : ∀ d n w {VR : VRel n w} {Ml Mr}
  → (0 < n → ℰᵍ d n w VR Ml Mr) → ℰᵍ d n w VR Ml Mr
ℰᵍ-pos d zero w f = ℰᵍ-zero d w
ℰᵍ-pos d (suc n) w f = f (s≤s z≤n)

-- so the value relations need to agree at positive stages only: a
-- value reached at stage 0 took all the counted steps, and those steps
-- are the first disjunct
ℰᵍ-map⁺ : ∀ d n w {VR VR′ : VRel n w}
  → (∀ {n′} (le : n′ ≤′ n) → 0 < n′ → ∀ w′ (e : w′ ⊒ w) V V′
       → VR le w′ e V V′ → VR′ le w′ e V V′)
  → ∀ {Ml Mr} → ℰᵍ d n w VR Ml Mr → ℰᵍ d n w VR′ Ml Mr
ℰᵍ-map⁺ ≺ n w f (inj₁ r) = inj₁ r
ℰᵍ-map⁺ ≺ n w f (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
ℰᵍ-map⁺ ≺ n w f (inj₂ (inj₂ (k , zero , le , ΔL′ , χsL , Vl , ΔR′ , χsR ,
    Vr , eq , sl , sr , vl , vr , a))) =
  inj₁ (ΔL′ , χsL , Vl ,
    subst (λ j → _ —→^ j [ χsL ] Vl) (trans (sym (+-identityʳ k)) eq) sl)
ℰᵍ-map⁺ ≺ n w f (inj₂ (inj₂ (k , suc m , le , ΔL′ , χsL , Vl , ΔR′ ,
    χsR , Vr , eq , sl , sr , vl , vr , tags , ok , v))) =
  inj₂ (inj₂ (k , suc m , le , ΔL′ , χsL , Vl , ΔR′ , χsR , Vr ,
    eq , sl , sr , vl , vr , tags , ok , f le (s≤s z≤n) _ _ _ _ v))
ℰᵍ-map⁺ ≻ n w f (inj₁ r) = inj₁ r
ℰᵍ-map⁺ ≻ n w f (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
ℰᵍ-map⁺ ≻ n w f (inj₂ (inj₂ (k , zero , le , ΔL′ , χsL , Vl , ΔR′ , χsR ,
    Vr , eq , sl , sr , vl , vr , a))) =
  inj₁ (ΔR′ , χsR , Vr ,
    subst (λ j → _ —→^ j [ χsR ] Vr) (trans (sym (+-identityʳ k)) eq) sr)
ℰᵍ-map⁺ ≻ n w f (inj₂ (inj₂ (k , suc m , le , ΔL′ , χsL , Vl , ΔR′ ,
    χsR , Vr , eq , sl , sr , vl , vr , tags , ok , v))) =
  inj₂ (inj₂ (k , suc m , le , ΔL′ , χsL , Vl , ΔR′ , χsR , Vr ,
    eq , sl , sr , vl , vr , tags , ok , f le (s≤s z≤n) _ _ _ _ v))

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

-- a left-only variable
𝒱-X★ : ∀ d n {Ψ : Corr Δ Δ′} {X} (o : Ψ ∋ X only) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → leafRel d n w (leaf δ X) V V′ ⇔ 𝒱 d n (X⊑★ o) w δ V V′
𝒱-X★ ≺ n o w = ⇔-id
𝒱-X★ ≻ n o w = ⇔-id

------------------------------------------------------------------------
-- `∀⊑★`, `∀★⊑★`, and `G`
------------------------------------------------------------------------

-- the relation at `∀⊑★` with body p, without the non-`★` premise
deadStarRel : Dir → ℕ → ∀ {Ψ : Corr Δ Δ′} {A} → dead Ψ ⊢ A ⊑ ★
  → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
  → Term (ΔL w) → Term (ΔR w) → Set
deadStarRel ≺ n p w δ Vl Vr = allDeadStar ≺ n p w δ Vl Vr
deadStarRel ≻ zero p w δ Vl Vr = ⊤
deadStarRel ≻ (suc k) p w δ Vl Vr = allDeadStar ≻ k p w δ Vl Vr

𝒱-deadStar : ∀ d n {Ψ : Corr Δ Δ′} {A} (ns : NonStar A)
    (p : dead Ψ ⊢ A ⊑ ★) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → 𝒱 d n (∀⊑★ ns p) w δ Vl Vr ⇔ deadStarRel d n p w δ Vl Vr
𝒱-deadStar ≺ n ns p w = ⇔-id
𝒱-deadStar ≻ zero ns p w = ⇔-id
𝒱-deadStar ≻ (suc k) ns p w = ⇔-id

-- `★`, whatever the interpretation
𝒱≤-★ : ∀ d {m n} (le : m ≤′ n) {Ψ : Corr Δ Δ′} w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → 𝒱≤ d le (★⊑★ {Φ = Ψ}) w δ V V′ ⇔ starAt d le w V V′
𝒱≤-★ ≺ ≤′-refl w = ⇔-id
𝒱≤-★ ≻ {zero} ≤′-refl w = ⇔-id
𝒱≤-★ ≻ {suc m} ≤′-refl w = ⇔-id
𝒱≤-★ ≺ (≤′-step le) w = 𝒱≤-★ ≺ le w
𝒱≤-★ ≻ (≤′-step le) w = 𝒱≤-★ ≻ le w

-- `∀X.★` with a dead X is `∀★`
allDeadStar-★ : ∀ d n {Ψ : Corr Δ Δ′} w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {Vl Vr}
  → allDeadStar d n (★⊑★ {Φ = dead Ψ}) w δ Vl Vr ⇔ allStar d n w Vl Vr
allDeadStar-★ d n w {Vr = ` x} = iff (λ ()) (λ ())
allDeadStar-★ d n w {Vr = ƛ M} = iff (λ ()) (λ ())
allDeadStar-★ d n w {Vr = L · M} = iff (λ ()) (λ ())
allDeadStar-★ d n w {Vr = Λ M} = iff (λ ()) (λ ())
allDeadStar-★ d n w {Vr = L ⦂∀ C [ T ]} = iff (λ ()) (λ ())
allDeadStar-★ d n w {Vr = $ κ} = iff (λ ()) (λ ())
allDeadStar-★ d n w {Vr = L ⊕[ op ] M} = iff (λ ()) (λ ())
allDeadStar-★ d n w {Vr = Wr ⟨ c ⟩} =
  iff (λ r → proj₁ r , λ e le T T′ →
         ℰᵍ-map d _ _
           (λ le′ w″ e′ V V′ → to (𝒱≤-★ d (≤′-trans le′ le) w″))
           (proj₂ r e le T T′))
      (λ r → proj₁ r , λ e le T T′ →
         ℰᵍ-map d _ _
           (λ le′ w″ e′ V V′ → from (𝒱≤-★ d (≤′-trans le′ le) w″))
           (proj₂ r e le T T′))
allDeadStar-★ d n w {Vr = M ↑ c} = iff (λ ()) (λ ())
allDeadStar-★ d n w {Vr = M ↓ c} = iff (λ ()) (λ ())
allDeadStar-★ d n w {Vr = blame} = iff (λ ()) (λ ())

-- the relation at `∀★ᵖ q`
deadStar-∀★ᵖ : ∀ d n {Ψ : Corr Δ Δ′} {C} (q : Ψ ⊢ C ⊑ ★) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → deadStarRel d n (wk-deadᵖ q) w δ Vl Vr ⇔ 𝒱 d n (∀★ᵖ q) w δ Vl Vr
deadStar-∀★ᵖ ≺ n ★⊑★ w = allDeadStar-★ ≺ n w
deadStar-∀★ᵖ ≻ zero ★⊑★ w = ⇔-id
deadStar-∀★ᵖ ≻ (suc k) ★⊑★ w = allDeadStar-★ ≻ k w
deadStar-∀★ᵖ d n q@(⇒⊑★ p₁ p₂) w =
  ⇔-sym (𝒱-deadStar d n nonstar-⇒ (wk-deadᵖ q) w)
deadStar-∀★ᵖ d n q@ι⊑★ w = ⇔-sym (𝒱-deadStar d n nonstar-ι (wk-deadᵖ q) w)
deadStar-∀★ᵖ d n q@(X⊑★ x) w =
  ⇔-sym (𝒱-deadStar d n nonstar-X (wk-deadᵖ q) w)
deadStar-∀★ᵖ d n q@(∀⊑ a z p) w =
  ⇔-sym (𝒱-deadStar d n nonstar-∀ (wk-deadᵖ q) w)
deadStar-∀★ᵖ d n q@∀★⊑★ w =
  ⇔-sym (𝒱-deadStar d n nonstar-∀ (wk-deadᵖ q) w)
deadStar-∀★ᵖ d n q@(∀⊑★ ns p) w =
  ⇔-sym (𝒱-deadStar d n nonstar-∀ (wk-deadᵖ q) w)
deadStar-∀★ᵖ d n q@bot⊑★ w =
  ⇔-sym (𝒱-deadStar d n nonstar-∀ (wk-deadᵖ q) w)

-- at a right type `★` and a positive stage, `≻` is `G`
𝒱≻★-G : ∀ k {Ψ : Corr Δ Δ′} {C} (q : Ψ ⊢ C ⊑ ★) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → 𝒱 ≻ (suc k) q w δ Vl Vr ⇔ G (suc k) q w δ Vl Vr
𝒱≻★-G k ★⊑★ w = ⇔-id
𝒱≻★-G k (⇒⊑★ p₁ p₂) w = ⇔-id
𝒱≻★-G k ι⊑★ w = ⇔-id
𝒱≻★-G k (X⊑★ x) w = ⇔-id
𝒱≻★-G k (∀⊑ a z p) w = ⇔-id
𝒱≻★-G k ∀★⊑★ w = ⇔-id
𝒱≻★-G k (∀⊑★ ns p) w = ⇔-id
𝒱≻★-G k bot⊑★ w = ⇔-id

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
    iff (λ r e le Wl Wr vl vr a →
           ℰᵍ-map d _ _
             (λ le′ w″ e′ V V′ →
               to (𝒱≤-ren d (≤′-trans le′ le) R q w″
                    (RenI-↑ (RenI-↑ h e) e′)))
             (r e le Wl Wr vl vr (from (𝒱≤-ren d le R p _ (RenI-↑ h e)) a)))
        (λ r e le Wl Wr vl vr a →
           ℰᵍ-map d _ _
             (λ le′ w″ e′ V V′ →
               from (𝒱≤-ren d (≤′-trans le′ le) R q w″
                      (RenI-↑ (RenI-↑ h e) e′)))
             (r e le Wl Wr vl vr (to (𝒱≤-ren d le R p _ (RenI-↑ h e)) a)))

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
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
               (annot-ren (rl≡ (RenI-↑ h e)) A))
             (cong (λ C → renameᵗᵐ (ρR e) Vr ⦂∀ C [ rightTyS c ])
               (annot-ren (rr≡ (RenI-↑ h e)) B))
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 to (𝒱≤-ren d (≤′-trans le′ le) (ext-pairᴿ R) p w″
                      (RenI-↑ (RenI-extPair {T = leftTyS c}
                        {T′ = rightTyS c} (RenI-↑ h e)) e′)))
               (r e le c)))
        (λ r e le c →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
               (annot-ren (rl≡ (RenI-↑ h e)) A)))
             (sym (cong (λ C → renameᵗᵐ (ρR e) Vr ⦂∀ C [ rightTyS c ])
               (annot-ren (rr≡ (RenI-↑ h e)) B)))
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 from (𝒱≤-ren d (≤′-trans le′ le) (ext-pairᴿ R) p w″
                        (RenI-↑ (RenI-extPair {T = leftTyS c}
                          {T′ = rightTyS c} (RenI-↑ h e)) e′)))
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
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
               (annot-ren (rl≡ (RenI-↑ h e)) A))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 to (𝒱≤-ren d (≤′-trans le′ le) (ext-onlyᴿ R) p w″
                      (RenI-↑ (RenI-extOnly {T = leftTyS c}
                        (RenI-↑ h e)) e′)))
               (r e le c)))
        (λ r e le c →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
               (annot-ren (rl≡ (RenI-↑ h e)) A)))
             refl
             (ℰᵍ-map d _ _
               (λ le′ w″ e′ V V′ →
                 from (𝒱≤-ren d (≤′-trans le′ le) (ext-onlyᴿ R) p w″
                        (RenI-↑ (RenI-extOnly {T = leftTyS c}
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
    sonly : ∀ {X} (x : Ψ ∋ X only) {w′} (e : w′ ⊒ w) {k} → 0 < k → k < N
      → ∀ {Vl Vr} → leafRel d k w′ (leaf (δ₁ ↑ᴵ e) X) Vl Vr
          ⇔ 𝒱 d k (σo S x) w′ (δ₂ ↑ᴵ e) Vl Vr
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
  sonly (SubI-↑ h e) {X = X} x e′ {k} pos lt =
    iff (λ r →
           𝒱-resp d k (σo S x) _ (≈ᴵ-sym (↑ᴵ-trans δ₂ e′ e))
             (to (sonly h x (⊒-trans e′ e) pos lt)
               (leafRel-resp d k _ (leaf≈ (↑ᴵ-trans δ₁ e′ e) X) r)))
        (λ r →
           leafRel-resp d k _ (≈ˡ-sym (leaf≈ (↑ᴵ-trans δ₁ e′ e) X))
             (from (sonly h x (⊒-trans e′ e) pos lt)
               (𝒱-resp d k (σo S x) _ (↑ᴵ-trans δ₂ e′ e) r)))
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
  sonly (SubI-extPair l h) (only-pair x) e {k} pos lt =
    ⇔-trans (sonly h x e pos lt)
      (𝒱-ren d k wk-pairᴿ (σo S x) _ (RenI-wkPair (ρL e) (ρR e)))
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
  sonly (SubI-extOnly l h) only-here e {k} pos lt =
    𝒱-X★ d k only-here _
  sonly (SubI-extOnly l h) (only-only x) e {k} pos lt =
    ⇔-trans (sonly h x e pos lt)
      (⇔-trans (𝒱-ren d k wk-onlyᴿ (σo S x) _ (RenI-wkOnly (ρL e) (ρR e)))
        (𝒱-substR d k (renameᵗ-id _) (renᵖ wk-onlyᴿ (σo S x)) _))
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
  sonly (SubI-extDead h) (only-dead x) e {k} pos lt =
    ⇔-trans (sonly h x e pos lt)
      (⇔-trans (𝒱-ren d k wk-deadᴿ (σo S x) _ (RenI-wkDead (ρL e) (ρR e)))
        (𝒱-substR d k (renameᵗ-id _) (renᵖ wk-deadᴿ (σo S x)) _))
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

  -- a left-only variable, read now
  only-⇔ : ∀ {X} (x : Ψ ∋ X only) {n} → SubI S d N w δ₁ δ₂ → 0 < n
    → n < N → ∀ {Vl Vr} → leafRel d n w (leaf δ₁ X) Vl Vr
        ⇔ 𝒱 d n (σo S x) w δ₂ Vl Vr
  only-⇔ {X = X} x {n} h pos lt =
    iff (λ r →
           𝒱-resp d n (σo S x) w (↑ᴵ-refl {w = w} δ₂)
             (to (sonly h x (⊒-refl w) pos lt)
               (leafRel-resp d n w (≈ˡ-sym (leaf≈ (↑ᴵ-refl {w = w} δ₁) X)) r)))
        (λ r →
           leafRel-resp d n w (leaf≈ (↑ᴵ-refl {w = w} δ₁) X)
             (from (sonly h x (⊒-refl w) pos lt)
               (𝒱-resp d n (σo S x) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ₂)) r)))

mutual
  𝒱-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (S : PSub Ψ Ψ′)
      {A B} (p : Ψ ⊢ A ⊑ B) {N} w {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → 0 < n → n < N
    → ∀ {Vl Vr} → 𝒱 d n p w δ₁ Vl Vr ⇔ 𝒱 d n (substᵖ S p) w δ₂ Vl Vr
  𝒱-subst ≺ n S ★⊑★ w h pos lt = ⇔-id
  𝒱-subst ≻ n S ★⊑★ w h pos lt = G-subst n S ★⊑★ w h lt
  𝒱-subst ≺ n S ι⊑ι w h pos lt = ⇔-id
  𝒱-subst ≻ n S ι⊑ι w h pos lt = ⇔-id
  𝒱-subst ≺ n S (X⊑Y x) w h pos lt = var-⇔ x h lt
  𝒱-subst ≻ n S (X⊑Y x) w h pos lt = var-⇔ x h lt
  𝒱-subst ≺ n S (⇒⊑⇒ p q) w h pos lt = funRel-subst ≺ n S p q w h lt
  𝒱-subst ≻ n S (⇒⊑⇒ p q) w h pos lt = funRel-subst ≻ n S p q w h lt
  𝒱-subst ≺ n S (∀⊑∀ p) w h pos lt = allPair-subst ≺ n S p w h lt
  𝒱-subst ≻ n S (∀⊑∀ p) w h pos lt = allPair-subst ≻ n S p w h lt
  𝒱-subst ≺ n S (⇒⊑★ p q) w h pos lt = funStar-subst ≺ n S p q w h lt
  𝒱-subst ≻ n S (⇒⊑★ p q) w h pos lt = G-subst n S (⇒⊑★ p q) w h lt
  𝒱-subst ≺ n S ι⊑★ w h pos lt = ⇔-id
  𝒱-subst ≻ n S ι⊑★ w h pos lt = G-subst n S ι⊑★ w h lt
  𝒱-subst ≺ n S (X⊑★ x) w h pos lt = only-⇔ x h pos lt
  𝒱-subst ≻ n S (X⊑★ x) w h pos lt = only-⇔ x h pos lt
  𝒱-subst ≺ n S (∀⊑ a z p) w h pos lt = allOnly-subst ≺ n S p w h lt
  𝒱-subst ≻ n S (∀⊑ {B = ★} a z p) w h pos lt = G-subst n S (∀⊑ a z p) w h lt
  𝒱-subst ≻ n S (∀⊑ {B = ＇ Y} a z p) w h pos lt = ⊥-elim (∀⊑-var⊥ a z p)
  𝒱-subst ≻ n S (∀⊑ {B = ‵ ι} a z p) w h pos lt =
    allOnly-subst ≻ n S p w h lt
  𝒱-subst ≻ n S (∀⊑ {B = B ⇒ C} a z p) w h pos lt =
    allOnly-subst ≻ n S p w h lt
  𝒱-subst ≻ n S (∀⊑ {B = `∀ B} a z p) w h pos lt =
    allOnly-subst ≻ n S p w h lt
  𝒱-subst ≺ n S ∀★⊑★ w h pos lt = ⇔-id
  𝒱-subst ≻ n S ∀★⊑★ w h pos lt = G-subst n S ∀★⊑★ w h lt
  𝒱-subst ≺ n S (∀⊑★ ns p) w h pos lt =
    deadStar-subst ≺ n S ns p w h lt
  𝒱-subst ≻ n S (∀⊑★ ns p) w h pos lt =
    deadStar-subst ≻ n S ns p w h lt
  𝒱-subst ≺ n S bot-elim w h pos lt = iff (λ ()) (λ ())
  𝒱-subst ≻ n S bot-elim w h pos lt = iff (λ ()) (λ ())
  𝒱-subst ≺ n S bot⊑★ w h pos lt = iff (λ ()) (λ ())
  𝒱-subst ≻ n S bot⊑★ w h pos lt = iff (λ ()) (λ ())

  𝒱≤-subst : ∀ d {n′ n} (le : n′ ≤′ n) {Ψ : Corr Δ₁ Δ₁′}
      {Ψ′ : Corr Δ₂ Δ₂′} (S : PSub Ψ Ψ′) {A B} (p : Ψ ⊢ A ⊑ B) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → 0 < n′ → n′ < N
    → ∀ {Vl Vr} → 𝒱≤ d le p w δ₁ Vl Vr ⇔ 𝒱≤ d le (substᵖ S p) w δ₂ Vl Vr
  𝒱≤-subst d {n′} ≤′-refl S p w h pos lt = 𝒱-subst d n′ S p w h pos lt
  𝒱≤-subst d (≤′-step le) S p w h pos lt = 𝒱≤-subst d le S p w h pos lt

  -- `∀⊑★`: the body is substituted under a dead variable; over a
  -- left-only variable sent to `★`, the result is `∀★⊑★`
  deadStar-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (S : PSub Ψ Ψ′) {A} (ns : NonStar A) (p : dead Ψ ⊢ A ⊑ ★) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → 𝒱 d n (∀⊑★ ns p) w δ₁ Vl Vr
        ⇔ 𝒱 d n (substᵖ S (∀⊑★ ns p)) w δ₂ Vl Vr
  deadStar-subst d n S nonstar-X p@(X⊑★ (only-dead x)) w h lt =
    ⇔-trans (𝒱-deadStar d n nonstar-X p w)
      (⇔-trans (deadStarRel-subst d n S p w h lt)
        (deadStar-∀★ᵖ d n (σo S x) w))
  deadStar-subst d n S nonstar-ι p w h lt =
    ⇔-trans (𝒱-deadStar d n nonstar-ι p w)
      (⇔-trans (deadStarRel-subst d n S p w h lt)
        (⇔-sym (𝒱-deadStar d n nonstar-ι (substᵖ (exts-deadˢ S) p) w)))
  deadStar-subst d n S nonstar-⇒ p w h lt =
    ⇔-trans (𝒱-deadStar d n nonstar-⇒ p w)
      (⇔-trans (deadStarRel-subst d n S p w h lt)
        (⇔-sym (𝒱-deadStar d n nonstar-⇒ (substᵖ (exts-deadˢ S) p) w)))
  deadStar-subst d n S nonstar-∀ p w h lt =
    ⇔-trans (𝒱-deadStar d n nonstar-∀ p w)
      (⇔-trans (deadStarRel-subst d n S p w h lt)
        (⇔-sym (𝒱-deadStar d n nonstar-∀ (substᵖ (exts-deadˢ S) p) w)))

  deadStarRel-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (S : PSub Ψ Ψ′) {A} (p : dead Ψ ⊢ A ⊑ ★) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → deadStarRel d n p w δ₁ Vl Vr
        ⇔ deadStarRel d n (substᵖ (exts-deadˢ S) p) w δ₂ Vl Vr
  deadStarRel-subst ≺ n S p w h lt = allDeadStar-subst ≺ n S p w h lt
  deadStarRel-subst ≻ zero S p w h lt = ⇔-id
  deadStarRel-subst ≻ (suc k) S p w h lt =
    allDeadStar-subst ≻ k S p w h (pred< lt)

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
    ⇔-trans (only-⇔ x h (s≤s z≤n) lt) (𝒱≻★-G k (σo S x) w)
  G-subst (suc k) S (∀⊑ a z p) w h lt = allOnly-subst ≻ k S p w h (pred< lt)
  G-subst (suc k) S ∀★⊑★ w h lt = ⇔-id
  G-subst (suc k) S (∀⊑★ ns p) w h lt =
    ⇔-trans (deadStar-subst ≻ (suc k) S ns p w h lt)
      (𝒱≻★-G k (substᵖ S (∀⊑★ ns p)) w)
  G-subst (suc k) S bot⊑★ w h lt = iff (λ ()) (λ ())

  funRel-subst : ∀ d n {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′}
      (S : PSub Ψ Ψ′) {A A′ B B′} (p : Ψ ⊢ A ⊑ A′) (q : Ψ ⊢ B ⊑ B′) {N} w
      {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    → SubI S d N w δ₁ δ₂ → n < N
    → ∀ {Vl Vr} → funRel d n p q w δ₁ Vl Vr
        ⇔ funRel d n (substᵖ S p) (substᵖ S q) w δ₂ Vl Vr
  funRel-subst d n S p q w h lt =
    iff (λ r e le Wl Wr vl vr a →
           ℰᵍ-pos d _ _ λ pos →
             ℰᵍ-map⁺ d _ _
               (λ le′ pos′ w″ e′ V V′ →
                 to (𝒱≤-subst d (≤′-trans le′ le) S q w″
                      (SubI-↑ (SubI-↑ h e) e′) pos′
                      (below (≤′-trans le′ le) lt)))
               (r e le Wl Wr vl vr
                 (from (𝒱≤-subst d le S p _ (SubI-↑ h e) pos
                         (below le lt)) a)))
        (λ r e le Wl Wr vl vr a →
           ℰᵍ-pos d _ _ λ pos →
             ℰᵍ-map⁺ d _ _
               (λ le′ pos′ w″ e′ V V′ →
                 from (𝒱≤-subst d (≤′-trans le′ le) S q w″
                        (SubI-↑ (SubI-↑ h e) e′) pos′
                        (below (≤′-trans le′ le) lt)))
               (r e le Wl Wr vl vr
                 (to (𝒱≤-subst d le S p _ (SubI-↑ h e) pos
                       (below le lt)) a)))

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
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
               (annot-subst (sl≡ (SubI-↑ h e)) A))
             (cong (λ C → renameᵗᵐ (ρR e) Vr ⦂∀ C [ rightTyS c ])
               (annot-subst (sr≡ (SubI-↑ h e)) B))
             (ℰᵍ-map⁺ d _ _
               (λ le′ pos′ w″ e′ V V′ →
                 to (𝒱≤-subst d (≤′-trans le′ le) (exts-pairˢ S) p w″
                      (SubI-↑ (SubI-extPair (sem (leafBelowS d le c))
                        (SubI-↑ h e)) e′)
                      pos′ (below (≤′-trans le′ le) lt)))
               (r e le c)))
        (λ r e le c →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
               (annot-subst (sl≡ (SubI-↑ h e)) A)))
             (sym (cong (λ C → renameᵗᵐ (ρR e) Vr ⦂∀ C [ rightTyS c ])
               (annot-subst (sr≡ (SubI-↑ h e)) B)))
             (ℰᵍ-map⁺ d _ _
               (λ le′ pos′ w″ e′ V V′ →
                 from (𝒱≤-subst d (≤′-trans le′ le) (exts-pairˢ S) p w″
                        (SubI-↑ (SubI-extPair (sem (leafBelowS d le c))
                          (SubI-↑ h e)) e′)
                        pos′ (below (≤′-trans le′ le) lt)))
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
             (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
               (annot-subst (sl≡ (SubI-↑ h e)) A))
             refl
             (ℰᵍ-map⁺ d _ _
               (λ le′ pos′ w″ e′ V V′ →
                 to (𝒱≤-subst d (≤′-trans le′ le) (exts-onlyˢ S) p w″
                      (SubI-↑ (SubI-extOnly (sem (onlyLeafS d le c))
                        (SubI-↑ h e)) e′)
                      pos′ (below (≤′-trans le′ le) lt)))
               (r e le c)))
        (λ r e le c →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ leftTyS c ])
               (annot-subst (sl≡ (SubI-↑ h e)) A)))
             refl
             (ℰᵍ-map⁺ d _ _
               (λ le′ pos′ w″ e′ V V′ →
                 from (𝒱≤-subst d (≤′-trans le′ le) (exts-onlyˢ S) p w″
                        (SubI-↑ (SubI-extOnly (sem (onlyLeafS d le c))
                          (SubI-↑ h e)) e′)
                        pos′ (below (≤′-trans le′ le) lt)))
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
             (ℰᵍ-map⁺ d _ _
               (λ le′ pos′ w″ e′ V V′ →
                 to (𝒱≤-subst d (≤′-trans le′ le) (exts-deadˢ S) p w″
                      (SubI-↑ (SubI-extDead {T = T} (SubI-↑ h e)) e′)
                      pos′ (below (≤′-trans le′ le) lt)))
               (r e le T T′)))
        (λ r e le T T′ →
           ℰᵍ-≡
             (sym (cong (λ C → renameᵗᵐ (ρL e) Vl ⦂∀ C [ T ])
               (annot-subst (sl≡ (SubI-↑ h e)) A)))
             refl
             (ℰᵍ-map⁺ d _ _
               (λ le′ pos′ w″ e′ V V′ →
                 from (𝒱≤-subst d (≤′-trans le′ le) (exts-deadˢ S) p w″
                        (SubI-↑ (SubI-extDead {T = T} (SubI-↑ h e)) e′)
                        pos′ (below (≤′-trans le′ le) lt)))
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
sonly (SubI-single d le q env envR hδ) (only-pair x) e {k} pos lt =
  𝒱-X★ d k x _
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

-- The substitution lemma for `•⊑•`: at positive stages below the stage
-- of the `∀⊑∀` clause, the body at `p` with the bound variable read at
-- `q` is related exactly when it is related at the premise `r` of `•⊑•`.
𝒱-tyapp : ∀ d {n′ n} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {T T′ A B}
    (q : Φ ⊢ T ⊑ T′) (p : pair Φ ⊢ A ⊑ B)
    (r : Φ ⊢ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ)
    {w} (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′)
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → δ ≈ᴵ envI env envR
  → ∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k < n′ → ∀ {Vl Vr}
  → 𝒱 d k p w′
      (extPairI (leftTy (desc q env envR)) (rightTy (desc q env envR))
        (sem (leafBelow d le (desc q env envR))) δ ↑ᴵ e) Vl Vr
    ⇔ 𝒱 d k r w′ (δ ↑ᴵ e) Vl Vr
𝒱-tyapp d le q p r env envR {δ} hδ e {k} pos lt {Vl} {Vr} =
  ⇔-trans
    (𝒱-subst d k (singleˢ q) p _
      (SubI-↑ (SubI-single d le q env envR hδ) e) pos lt)
    (iff (subst (λ r′ → 𝒱 d k r′ _ (δ ↑ᴵ e) Vl Vr)
           (⊑-unique (substᵖ (singleˢ q) p) r))
         (subst (λ r′ → 𝒱 d k r′ _ (δ ↑ᴵ e) Vl Vr)
           (sym (⊑-unique (substᵖ (singleˢ q) p) r))))

------------------------------------------------------------------------
-- The left-only type application
------------------------------------------------------------------------

-- the guarded leaf of a left-only bound variable, up to its stage, is
-- `G` at its descriptor
leafG-⇔ : ∀ {n′ n} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {T T′}
    (q : Φ ⊢ T ⊑ T′) (env : Vec (Entry ΘL ΘR) Δ) (envR : Vec (Ty ΘR) Δ′)
    {k} → k ≤ n′ → ∀ w τL τR {V V′}
  → leafG le (desc q env envR) k w τL τR V V′
    ⇔ G k q w (envI (renameEntries τL τR env)
          (Vec.map (renameᵗ (toRenameᵗ τR)) envR)) V V′
leafG-⇔ {n′ = n′} le q env envR {k} le₁ w τL τR with k ≤? n′
leafG-⇔ {n′ = n′} le q env envR {k} le₁ w τL τR | yes le₂ =
  iff (G≤→G (≤′-trans (≤⇒≤′ le₂) le) q w)
      (G→G≤ (≤′-trans (≤⇒≤′ le₂) le) q w)
leafG-⇔ {n′ = n′} le q env envR {k} le₁ w τL τR | no ¬le = ⊥-elim (¬le le₁)

-- the stages at which a left-only bound variable's leaf is defined:
-- below the clause's stage in `≺`, up to it in `≻`
onlyBound : Dir → ℕ → ℕ
onlyBound ≺ n′ = n′
onlyBound ≻ n′ = suc n′

-- the interpretation of the `∀⊑` clause, with the descriptor of `q`
-- over the interpretation's own entries, substitutes `q` for the bound
-- variable, at positive stages up to the clause's
SubI-singleO : ∀ d {n′ n} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {T}
    (q : Φ ⊢ T ⊑ ★) {w} (env : Vec (Entry (ΔL w) (ΔR w)) Δ)
    (envR : Vec (Ty (ΔR w)) Δ′) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → δ ≈ᴵ envI env envR
  → SubI (singleOˢ q) d (onlyBound d n′) w
      (extOnlyI (leftTy (desc q env envR))
        (sem (onlyLeaf d le (desc q env envR))) δ)
      δ
sl≡ (SubI-singleO d le {T = T} q env envR hδ) Fin.zero =
  substᵗ-cong T (λ X → sym (δl≡ hδ X))
sl≡ (SubI-singleO d le q env envR hδ) (Fin.suc X) = refl
sr≡ (SubI-singleO d le q env envR hδ) Y = refl
sonly (SubI-singleO ≺ le q env envR hδ) only-here {w′} e {k} pos lt =
  iff (λ r →
         𝒱-resp ≺ k q w′ (envI-↑ e {env} {envR} hδ)
           (to (leafBelow-⇔ ≺ le q env envR lt w′
                 (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)) r))
      (λ r →
         from (leafBelow-⇔ ≺ le q env envR lt w′
                (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e))
           (𝒱-resp ≺ k q w′ (≈ᴵ-sym (envI-↑ e {env} {envR} hδ)) r))
sonly (SubI-singleO ≻ le q env envR hδ) only-here {w′} e {suc j}
    (s≤s z≤n) lt =
  iff (λ r →
         from (𝒱≻★-G j q w′)
           (G-resp (suc j) q w′ (envI-↑ e {env} {envR} hδ)
             (to (leafG-⇔ le q env envR (≤-pred lt) w′
                   (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e)) r)))
      (λ r →
         from (leafG-⇔ le q env envR (≤-pred lt) w′
                (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e))
           (G-resp (suc j) q w′ (≈ᴵ-sym (envI-↑ e {env} {envR} hδ))
             (to (𝒱≻★-G j q w′) r)))
sonly (SubI-singleO d le q env envR hδ) (only-only x) e {k} pos lt =
  𝒱-X★ d k x _
spair (SubI-singleO d le q env envR hδ) (↔-only x) e {k} lt =
  𝒱-XY d k x _

-- The substitution lemma for `•⊑`: at positive stages up to the `∀⊑`
-- clause's, the body at `p` with the bound variable read at `q` is
-- related exactly when it is related at the premise `r` of `•⊑`.  At
-- stage 0 the two can differ in `≻` (the guarded leaf holds there, the
-- relation at a left-only store variable needs a seal), but no
-- expression relation needs a value at stage 0 (`ℰᵍ-map⁺`).
𝒱-tyappO : ∀ d {n′ n} (le : n′ ≤′ n) {Φ : Corr Δ Δ′} {T A B}
    (q : Φ ⊢ T ⊑ ★) (p : only Φ ⊢ A ⊑ B) (r : Φ ⊢ A [ T ]ᵗ ⊑ B)
    {w} (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′)
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
  → δ ≈ᴵ envI env envR
  → ∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k < onlyBound d n′ → ∀ {Vl Vr}
  → 𝒱 d k p w′
      (extOnlyI (leftTy (desc q env envR))
        (sem (onlyLeaf d le (desc q env envR))) δ ↑ᴵ e) Vl Vr
    ⇔ 𝒱 d k r w′ (δ ↑ᴵ e) Vl Vr
𝒱-tyappO d le {B = B} q p r env envR {δ} hδ e {k} pos lt {Vl} {Vr} =
  ⇔-trans
    (𝒱-subst d k (singleOˢ q) p _
      (SubI-↑ (SubI-singleO d le q env envR hδ) e) pos lt)
    (⇔-trans (𝒱-substR d k (substᵗ-id B) (substᵖ (singleOˢ q) p) _)
      (iff (subst (λ r′ → 𝒱 d k r′ _ (δ ↑ᴵ e) Vl Vr) eq)
           (subst (λ r′ → 𝒱 d k r′ _ (δ ↑ᴵ e) Vl Vr) (sym eq))))
  where
  eq = ⊑-unique
         (subst (λ C → _ ⊢ _ ⊑ C) (substᵗ-id B) (substᵖ (singleOˢ q) p)) r
