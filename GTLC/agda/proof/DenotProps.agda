module proof.DenotProps where

-- File Charter:
--   * Basic properties of the denotation (Denotation.agda): monotonicity of
--     the operators, of coercions and of terms; finite support (continuity)
--     of coercions in their argument and of terms in their environment; and
--     the β law of Λ in the direction F E ⊆ Λ F ● E.
--   * Finite support is stated for functions of an environment (Finₑ), with
--     finite environments (FEnv) joined pointwise; a coercion is a function of
--     the environment through variable 0, and the body of a function wrapper
--     through variables 0, 1 (and 2).

open import Agda.Builtin.Nat using (zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Contexts using (Var)
open import Coercions
open import CastCalculus using (Termᶜ; `_; $_; ƛ_⇒_; _·_; cast_[_]; blame)
open import GraphModel
open import Denotation

------------------------------------------------------------------------
-- Inclusion
------------------------------------------------------------------------

⊆-refl : ∀ {D} → D ⊆ D
⊆-refl d d∈ = d∈

⊆-trans : ∀ {D E F} → D ⊆ E → E ⊆ F → D ⊆ F
⊆-trans D⊆ E⊆ d d∈ = E⊆ d (D⊆ d d∈)

infix 4 _⊆ₑ_

_⊆ₑ_ : Env → Env → Set
ρ ⊆ₑ ρ′ = ∀ x → ρ x ⊆ ρ′ x

⊆ₑ-refl : ∀ {ρ} → ρ ⊆ₑ ρ
⊆ₑ-refl x = ⊆-refl

ext-⊆ₑ : ∀ {X X′ ρ ρ′} → X ⊆ X′ → ρ ⊆ₑ ρ′ → (X • ρ) ⊆ₑ (X′ • ρ′)
ext-⊆ₑ X⊆ ρ⊆ zero = X⊆
ext-⊆ₑ X⊆ ρ⊆ (suc x) = ρ⊆ x

------------------------------------------------------------------------
-- Monotonicity of the operators
------------------------------------------------------------------------

⌊⌋-mono : ∀ {D D′} → D ⊆ D′ → ⌊ D ⌋ ⊆ ⌊ D′ ⌋
⌊⌋-mono D⊆ d (d∈ , d≢) = D⊆ d d∈ , d≢

⌊⌋-⊆ : ∀ {D} → ⌊ D ⌋ ⊆ D
⌊⌋-⊆ d (d∈ , d≢) = d∈

≫=-mono : ∀ {D D′ F F′} → D ⊆ D′
  → (∀ {X X′} → X ⊆ X′ → F X ⊆ F′ X′)
  → (D ≫= F) ⊆ (D′ ≫= F′)
≫=-mono D⊆ F⊆ w (inj₁ (eq , ω∈)) = inj₁ (eq , D⊆ ω ω∈)
≫=-mono D⊆ F⊆ w (inj₂ ((d , d∈ , d≢) , w∈)) =
  inj₂ ((d , D⊆ d d∈ , d≢) , F⊆ (⌊⌋-mono D⊆) w w∈)

guard-mono : ∀ {X X′ D D′} → X ⊆ X′ → D ⊆ D′ → guard X D ⊆ guard X′ D′
guard-mono X⊆ D⊆ w ((x , x∈ , x≢) , w∈) = (x , X⊆ x x∈ , x≢) , D⊆ w w∈

Λ-mono : ∀ {F F′} → (∀ Y → F Y ⊆ F′ Y) → Λ F ⊆ Λ F′
Λ-mono F⊆ (V ⟼ w) (w∈ , ne , noerr) = F⊆ (mem V) w w∈ , ne , noerr
Λ-mono F⊆ ν tt = tt
Λ-mono F⊆ (nat n) ()
Λ-mono F⊆ ω ()
Λ-mono F⊆ (tag t d) ()

●-mono : ∀ {D D′ E E′} → D ⊆ D′ → E ⊆ E′ → (D ● E) ⊆ (D′ ● E′)
●-mono D⊆ E⊆ w (V , e∈ , V⊆ , ne) =
  V , D⊆ _ e∈ , (λ d d∈ → E⊆ d (V⊆ d d∈)) , ne

------------------------------------------------------------------------
-- Monotonicity of coercions and terms
------------------------------------------------------------------------

⟦⟧ᶜ-mono : ∀ c {X Y} → X ⊆ Y → ⟦ c ⟧ᶜ X ⊆ ⟦ c ⟧ᶜ Y
⟦⟧ᶜ-mono (idᶜ A) X⊆ = X⊆
⟦⟧ᶜ-mono (A !) X⊆ (tag t v) (eq , v∈) = eq , X⊆ v v∈
⟦⟧ᶜ-mono (A !) X⊆ (nat n) ()
⟦⟧ᶜ-mono (A !) X⊆ (V ⟼ w) ()
⟦⟧ᶜ-mono (A !) X⊆ ν ()
⟦⟧ᶜ-mono (A !) X⊆ ω ()
⟦⟧ᶜ-mono (A `?) X⊆ w (inj₁ (t , eq , w∈)) = inj₁ (t , eq , X⊆ _ w∈)
⟦⟧ᶜ-mono (A `?) X⊆ w (inj₂ (eq , t , v , v∈ , neq)) =
  inj₂ (eq , t , v , X⊆ _ v∈ , neq)
⟦⟧ᶜ-mono (c ↦ d) X⊆ =
  guard-mono X⊆ (Λ-mono (λ Y → ≫=-mono ⊆-refl
    (λ Y₁⊆ → ≫=-mono (●-mono X⊆ Y₁⊆) (⟦⟧ᶜ-mono d))))
⟦⟧ᶜ-mono (c ⨟ d) X⊆ = ≫=-mono (⟦⟧ᶜ-mono c X⊆) (⟦⟧ᶜ-mono d)
⟦⟧ᶜ-mono (⊥ᶜ A ⇨ B at ℓ) X⊆ = guard-mono X⊆ ⊆-refl

⟦⟧-mono : ∀ M {ρ ρ′} → (∀ x → ρ x ⊆ ρ′ x) → ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ′
⟦⟧-mono (` x) ρ⊆ = ρ⊆ x
⟦⟧-mono ($ n) ρ⊆ = ⊆-refl
⟦⟧-mono (ƛ A ⇒ N) ρ⊆ = Λ-mono (λ Y → ⟦⟧-mono N (ext-⊆ₑ ⊆-refl ρ⊆))
⟦⟧-mono (L · M) ρ⊆ =
  ≫=-mono (⟦⟧-mono L ρ⊆)
    (λ F⊆ → ≫=-mono (⟦⟧-mono M ρ⊆) (λ X⊆ → ●-mono F⊆ X⊆))
⟦⟧-mono (cast M [ c ]) ρ⊆ = ≫=-mono (⟦⟧-mono M ρ⊆) (⟦⟧ᶜ-mono c)
⟦⟧-mono blame ρ⊆ = ⊆-refl

------------------------------------------------------------------------
-- Functions of an environment: monotonicity and finite support
------------------------------------------------------------------------

Monoₑ : (Env → 𝒫) → Set₁
Monoₑ Φ = ∀ {ρ ρ′} → ρ ⊆ₑ ρ′ → Φ ρ ⊆ Φ ρ′

-- finite environments
FEnv : Set
FEnv = Var → List Val

⟪_⟫ : FEnv → Env
⟪ φ ⟫ x = mem (φ x)

infix 4 _⊑ₑ_

_⊑ₑ_ : FEnv → Env → Set
φ ⊑ₑ ρ = ∀ x → mem (φ x) ⊆ ρ x

Finₑ : (Env → 𝒫) → Set₁
Finₑ Φ = ∀ ρ w → w ∈ Φ ρ → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × w ∈ Φ ⟪ φ ⟫)

∅ₑ : FEnv
∅ₑ x = []

∅ₑ-⊑ : ∀ ρ → ∅ₑ ⊑ₑ ρ
∅ₑ-⊑ ρ x d ()

join : FEnv → FEnv → FEnv
join φ ψ x = φ x ++ ψ x

join-⊑ : ∀ {φ ψ ρ} → φ ⊑ₑ ρ → ψ ⊑ₑ ρ → join φ ψ ⊑ₑ ρ
join-⊑ {φ = φ} φ⊑ ψ⊑ x d d∈ with ∈-++⁻ (φ x) d∈
join-⊑ {φ = φ} φ⊑ ψ⊑ x d d∈ | inj₁ d∈φ = φ⊑ x d d∈φ
join-⊑ {φ = φ} φ⊑ ψ⊑ x d d∈ | inj₂ d∈ψ = ψ⊑ x d d∈ψ

join-l : ∀ {φ ψ} → ⟪ φ ⟫ ⊆ₑ ⟪ join φ ψ ⟫
join-l x d d∈ = ∈-++⁺ˡ d∈

join-r : ∀ {φ ψ} → ⟪ ψ ⟫ ⊆ₑ ⟪ join φ ψ ⟫
join-r {φ = φ} x d d∈ = ∈-++⁺ʳ (φ x) d∈

-- one finite environment for every element of a list
collect : ∀ {ρ} (P : Val → Env → Set)
  → (∀ k {ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ₂ → P k ρ₁ → P k ρ₂)
  → ∀ K
  → (∀ k → k ⋵ K → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × P k ⟪ φ ⟫))
  → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × (∀ k → k ⋵ K → P k ⟪ φ ⟫))
collect {ρ = ρ} P Pm [] h = ∅ₑ , ∅ₑ-⊑ ρ , λ k ()
collect P Pm (k ∷ K) h =
  join φk φK , join-⊑ (proj₁ (proj₂ rk)) (proj₁ (proj₂ rK)) , all
  where
  rk = h k (here refl)
  rK = collect P Pm K (λ k′ k′∈ → h k′ (there k′∈))
  φk = proj₁ rk
  φK = proj₁ rK
  all : ∀ k′ → k′ ⋵ (k ∷ K) → P k′ ⟪ join φk φK ⟫
  all .k (here refl) = Pm k (join-l {φ = φk} {ψ = φK}) (proj₂ (proj₂ rk))
  all k′ (there k′∈) =
    Pm k′ (join-r {φ = φk} {ψ = φK}) (proj₂ (proj₂ rK) k′ k′∈)

-- Basic functions of an environment

const-mono : ∀ {D} → Monoₑ (λ ρ → D)
const-mono ρ⊆ = ⊆-refl

const-fin : ∀ {D} → Finₑ (λ ρ → D)
const-fin ρ w w∈ = ∅ₑ , ∅ₑ-⊑ ρ , w∈

var-mono : ∀ x → Monoₑ (λ ρ → ρ x)
var-mono x ρ⊆ = ρ⊆ x

at0 : List Val → FEnv
at0 L zero = L
at0 L (suc x) = []

var0-fin : Finₑ (λ ρ → ρ zero)
var0-fin ρ w w∈ = at0 (w ∷ []) , ⊑ , here refl
  where
  ⊑ : at0 (w ∷ []) ⊑ₑ ρ
  ⊑ zero d (here refl) = w∈
  ⊑ zero d (there ())
  ⊑ (suc x) d ()

shiftₑ : FEnv → FEnv
shiftₑ φ zero = []
shiftₑ φ (suc x) = φ x

shift-mono : ∀ {Φ} → Monoₑ Φ → Monoₑ (λ ρ → Φ (λ x → ρ (suc x)))
shift-mono m ρ⊆ = m (λ x → ρ⊆ (suc x))

shift-fin : ∀ {Φ} → Finₑ Φ → Finₑ (λ ρ → Φ (λ x → ρ (suc x)))
shift-fin f ρ w w∈ =
  shiftₑ (proj₁ r) , ⊑ , proj₂ (proj₂ r)
  where
  r = f (λ x → ρ (suc x)) w w∈
  ⊑ : shiftₑ (proj₁ r) ⊑ₑ ρ
  ⊑ zero d ()
  ⊑ (suc x) = proj₁ (proj₂ r) x

var-fin : ∀ x → Finₑ (λ ρ → ρ x)
var-fin zero = var0-fin
var-fin (suc x) = shift-fin (var-fin x)

bind-mono : ∀ {Ψ Θ} → Monoₑ Ψ → Monoₑ Θ
  → Monoₑ (λ ρ → Ψ ρ ≫= λ Y → Θ (Y • ρ))
bind-mono mΨ mΘ ρ⊆ = ≫=-mono (mΨ ρ⊆) (λ Y⊆ → mΘ (ext-⊆ₑ Y⊆ ρ⊆))

bind-fin : ∀ {Ψ Θ} → Monoₑ Ψ → Finₑ Ψ → Monoₑ Θ → Finₑ Θ
  → Finₑ (λ ρ → Ψ ρ ≫= λ Y → Θ (Y • ρ))
bind-fin mΨ fΨ mΘ fΘ ρ w (inj₁ (eq , ω∈)) =
  proj₁ r , proj₁ (proj₂ r) , inj₁ (eq , proj₂ (proj₂ r))
  where
  r = fΨ ρ ω ω∈
bind-fin {Ψ = Ψ} {Θ = Θ} mΨ fΨ mΘ fΘ ρ w
    (inj₂ ((d , d∈ , d≢) , w∈)) =
  φ , φ⊑ ,
  inj₂ ((d , mΨ ⊆d d (proj₂ (proj₂ rd)) , d≢) ,
        mΘ incl w (proj₂ (proj₂ rθ)))
  where
  rd = fΨ ρ d d∈
  rθ = fΘ (⌊ Ψ ρ ⌋ • ρ) w w∈
  φd = proj₁ rd
  φθ = proj₁ rθ
  φθ⊑ = proj₁ (proj₂ rθ)
  rk = collect (λ k ρ′ → k ∈ Ψ ρ′) (λ k ρ⊆ → mΨ ρ⊆ k) (φθ zero)
         (λ k k∈ → fΨ ρ k (proj₁ (φθ⊑ zero k k∈)))
  φ₁ : FEnv
  φ₁ x = φθ (suc x)
  φ₂ : FEnv
  φ₂ = join φ₁ (proj₁ rk)
  φ : FEnv
  φ = join φd φ₂
  φ⊑ : φ ⊑ₑ ρ
  φ⊑ = join-⊑ (proj₁ (proj₂ rd))
         (join-⊑ (λ x → φθ⊑ (suc x)) (proj₁ (proj₂ rk)))
  ⊆d : ⟪ φd ⟫ ⊆ₑ ⟪ φ ⟫
  ⊆d = join-l {φ = φd} {ψ = φ₂}
  ⊆k : ⟪ proj₁ rk ⟫ ⊆ₑ ⟪ φ ⟫
  ⊆k x k k∈ =
    join-r {φ = φd} {ψ = φ₂} x k (join-r {φ = φ₁} {ψ = proj₁ rk} x k k∈)
  incl : ⟪ φθ ⟫ ⊆ₑ (⌊ Ψ ⟪ φ ⟫ ⌋ • ⟪ φ ⟫)
  incl zero k k∈ =
    mΨ ⊆k k (proj₂ (proj₂ rk) k k∈) , proj₂ (φθ⊑ zero k k∈)
  incl (suc x) k k∈ =
    join-r {φ = φd} {ψ = φ₂} x k (join-l {φ = φ₁} {ψ = proj₁ rk} x k k∈)

●-mono-env : ∀ {Ψ₁ Ψ₂} → Monoₑ Ψ₁ → Monoₑ Ψ₂
  → Monoₑ (λ ρ → Ψ₁ ρ ● Ψ₂ ρ)
●-mono-env m₁ m₂ ρ⊆ = ●-mono (m₁ ρ⊆) (m₂ ρ⊆)

●-fin : ∀ {Ψ₁ Ψ₂} → Monoₑ Ψ₁ → Monoₑ Ψ₂ → Finₑ Ψ₁ → Finₑ Ψ₂
  → Finₑ (λ ρ → Ψ₁ ρ ● Ψ₂ ρ)
●-fin {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} m₁ m₂ f₁ f₂ ρ w (V , e∈ , V⊆ , ne) =
  φ , join-⊑ (proj₁ (proj₂ re)) (proj₁ (proj₂ rk)) ,
  (V , m₁ (join-l {φ = φe} {ψ = φk}) _ (proj₂ (proj₂ re)) ,
   (λ v v∈ → m₂ (join-r {φ = φe} {ψ = φk}) v (proj₂ (proj₂ rk) v v∈)) ,
   ne)
  where
  re = f₁ ρ (V ⟼ w) e∈
  rk = collect (λ k ρ′ → k ∈ Ψ₂ ρ′) (λ k ρ⊆ → m₂ ρ⊆ k) V
         (λ k k∈ → f₂ ρ k (V⊆ k k∈))
  φe = proj₁ re
  φk = proj₁ rk
  φ : FEnv
  φ = join φe φk

------------------------------------------------------------------------
-- Finite support of functions on sets
------------------------------------------------------------------------

Mono : (𝒫 → 𝒫) → Set₁
Mono F = ∀ {X Y} → X ⊆ Y → F X ⊆ F Y

Finitary : (𝒫 → 𝒫) → Set₁
Finitary f = ∀ X w → w ∈ f X → Σ[ L ∈ List Val ] (mem L ⊆ X × w ∈ f (mem L))

Finitary→Finₑ : ∀ {f} → Finitary f → Finₑ (λ ρ → f (ρ zero))
Finitary→Finₑ fin ρ w w∈ = at0 (proj₁ r) , ⊑ , proj₂ (proj₂ r)
  where
  r = fin (ρ zero) w w∈
  ⊑ : at0 (proj₁ r) ⊑ₑ ρ
  ⊑ zero = proj₁ (proj₂ r)
  ⊑ (suc x) d ()

Finₑ→Finitary : ∀ f → Finₑ (λ ρ → f (ρ zero)) → Finitary f
Finₑ→Finitary f fin X w w∈ =
  proj₁ r zero , proj₁ (proj₂ r) zero , proj₂ (proj₂ r)
  where
  r = fin (X • ρ₀) w w∈

single⊆ : ∀ {w X} → w ∈ X → mem (w ∷ []) ⊆ X
single⊆ w∈ d (here refl) = w∈
single⊆ w∈ d (there ())

-- the body of a function wrapper, after its argument coercion:
-- (ρ i ● ρ 0) ≫= f
wrapₑ-mono : ∀ {f} → (∀ {X Y} → X ⊆ Y → f X ⊆ f Y) → ∀ i
  → Monoₑ (λ ρ → (ρ i ● ρ zero) ≫= f)
wrapₑ-mono {f = f} fm i =
  bind-mono {Ψ = λ ρ → ρ i ● ρ zero} {Θ = λ ρ → f (ρ zero)}
    (●-mono-env (var-mono i) (var-mono zero)) (λ ρ⊆ → fm (ρ⊆ zero))

wrapₑ-fin : ∀ {f} → (∀ {X Y} → X ⊆ Y → f X ⊆ f Y) → Finitary f → ∀ i
  → Finₑ (λ ρ → (ρ i ● ρ zero) ≫= f)
wrapₑ-fin {f = f} fm ff i =
  bind-fin {Ψ = λ ρ → ρ i ● ρ zero} {Θ = λ ρ → f (ρ zero)}
    (●-mono-env (var-mono i) (var-mono zero))
    (●-fin (var-mono i) (var-mono zero) (var-fin i) (var-fin zero))
    (λ ρ⊆ → fm (ρ⊆ zero))
    (Finitary→Finₑ {f = f} ff)

------------------------------------------------------------------------
-- Finite support of coercions and terms
------------------------------------------------------------------------

⟦⟧ᶜ-fin : ∀ c → Finitary ⟦ c ⟧ᶜ
⟦⟧ᶜ-fin (idᶜ A) X w w∈ = w ∷ [] , single⊆ w∈ , here refl
⟦⟧ᶜ-fin (A !) X (tag t v) (eq , v∈) = v ∷ [] , single⊆ v∈ , eq , here refl
⟦⟧ᶜ-fin (A !) X (nat n) ()
⟦⟧ᶜ-fin (A !) X (V ⟼ w) ()
⟦⟧ᶜ-fin (A !) X ν ()
⟦⟧ᶜ-fin (A !) X ω ()
⟦⟧ᶜ-fin (A `?) X w (inj₁ (t , eq , w∈)) =
  tag t w ∷ [] , single⊆ w∈ , inj₁ (t , eq , here refl)
⟦⟧ᶜ-fin (A `?) X w (inj₂ (eq , t , v , v∈ , neq)) =
  tag t v ∷ [] , single⊆ v∈ , inj₂ (eq , t , v , here refl , neq)
⟦⟧ᶜ-fin (c ↦ d) X ν ((x , x∈ , x≢) , tt) =
  x ∷ [] , single⊆ x∈ , (x , here refl , x≢) , tt
⟦⟧ᶜ-fin (c ↦ d) X (nat n) (_ , ())
⟦⟧ᶜ-fin (c ↦ d) X ω (_ , ())
⟦⟧ᶜ-fin (c ↦ d) X (tag t v) (_ , ())
⟦⟧ᶜ-fin (c ↦ d) X (U ⟼ w) ((x , x∈ , x≢) , w∈ , ne , noerr) =
  L , L⊆ , (x , here refl , x≢) , mH incl w (proj₂ (proj₂ r)) , ne , noerr
  where
  H : Env → 𝒫
  H ρ = ⟦ c ⟧ᶜ (mem U) ≫= λ Y₁ → (ρ zero ● Y₁) ≫= ⟦ d ⟧ᶜ
  mH : Monoₑ H
  mH = bind-mono {Ψ = λ ρ → ⟦ c ⟧ᶜ (mem U)}
         {Θ = λ ρ → (ρ (suc zero) ● ρ zero) ≫= ⟦ d ⟧ᶜ}
         const-mono (wrapₑ-mono (⟦⟧ᶜ-mono d) (suc zero))
  fH : Finₑ H
  fH = bind-fin {Ψ = λ ρ → ⟦ c ⟧ᶜ (mem U)}
         {Θ = λ ρ → (ρ (suc zero) ● ρ zero) ≫= ⟦ d ⟧ᶜ}
         const-mono const-fin
         (wrapₑ-mono (⟦⟧ᶜ-mono d) (suc zero))
         (wrapₑ-fin (⟦⟧ᶜ-mono d) (⟦⟧ᶜ-fin d) (suc zero))
  r = fH (X • ρ₀) w w∈
  φ = proj₁ r
  L : List Val
  L = x ∷ φ zero
  L⊆ : mem L ⊆ X
  L⊆ d (here refl) = x∈
  L⊆ d (there d∈) = proj₁ (proj₂ r) zero d d∈
  incl : ⟪ φ ⟫ ⊆ₑ (mem L • (λ y → ⟪ φ ⟫ (suc y)))
  incl zero d d∈ = there d∈
  incl (suc y) = ⊆-refl
⟦⟧ᶜ-fin (c ⨟ d) =
  Finₑ→Finitary ⟦ c ⨟ d ⟧ᶜ
    (bind-fin {Ψ = λ ρ → ⟦ c ⟧ᶜ (ρ zero)} {Θ = λ ρ → ⟦ d ⟧ᶜ (ρ zero)}
      (λ ρ⊆ → ⟦⟧ᶜ-mono c (ρ⊆ zero)) (Finitary→Finₑ {f = ⟦ c ⟧ᶜ} (⟦⟧ᶜ-fin c))
      (λ ρ⊆ → ⟦⟧ᶜ-mono d (ρ⊆ zero)) (Finitary→Finₑ {f = ⟦ d ⟧ᶜ} (⟦⟧ᶜ-fin d)))
⟦⟧ᶜ-fin (⊥ᶜ A ⇨ B at ℓ) X w ((x , x∈ , x≢) , eq) =
  x ∷ [] , single⊆ x∈ , (x , here refl , x≢) , eq

⟦⟧-fin : ∀ M → Finₑ ⟦ M ⟧
⟦⟧-fin (` x) = var-fin x
⟦⟧-fin ($ n) = const-fin
⟦⟧-fin (ƛ A ⇒ N) ρ ν tt = ∅ₑ , ∅ₑ-⊑ ρ , tt
⟦⟧-fin (ƛ A ⇒ N) ρ (nat n) ()
⟦⟧-fin (ƛ A ⇒ N) ρ ω ()
⟦⟧-fin (ƛ A ⇒ N) ρ (tag t d) ()
⟦⟧-fin (ƛ A ⇒ N) ρ (U ⟼ w) (w∈ , ne , noerr) =
  φ′ , (λ x → proj₁ (proj₂ r) (suc x)) ,
  ⟦⟧-mono N incl w (proj₂ (proj₂ r)) , ne , noerr
  where
  r = ⟦⟧-fin N (mem U • ρ) w w∈
  φ′ : FEnv
  φ′ x = proj₁ r (suc x)
  incl : ⟪ proj₁ r ⟫ ⊆ₑ (mem U • ⟪ φ′ ⟫)
  incl zero = proj₁ (proj₂ r) zero
  incl (suc x) = ⊆-refl
⟦⟧-fin (L · M) =
  bind-fin {Ψ = ⟦ L ⟧} {Θ = Θ} (⟦⟧-mono L) (⟦⟧-fin L) mΘ fΘ
  where
  Θ : Env → 𝒫
  Θ ρ = ⟦ M ⟧ (λ x → ρ (suc x)) ≫= λ X → ρ zero ● X
  app-mono : Monoₑ (λ ρ → ρ (suc zero) ● ρ zero)
  app-mono = ●-mono-env (var-mono (suc zero)) (var-mono zero)
  app-fin : Finₑ (λ ρ → ρ (suc zero) ● ρ zero)
  app-fin =
    ●-fin (var-mono (suc zero)) (var-mono zero)
      (var-fin (suc zero)) (var-fin zero)
  mΘ : Monoₑ Θ
  mΘ = bind-mono {Ψ = λ ρ → ⟦ M ⟧ (λ x → ρ (suc x))}
         {Θ = λ ρ → ρ (suc zero) ● ρ zero}
         (shift-mono {Φ = ⟦ M ⟧} (⟦⟧-mono M)) app-mono
  fΘ : Finₑ Θ
  fΘ = bind-fin {Ψ = λ ρ → ⟦ M ⟧ (λ x → ρ (suc x))}
         {Θ = λ ρ → ρ (suc zero) ● ρ zero}
         (shift-mono {Φ = ⟦ M ⟧} (⟦⟧-mono M))
         (shift-fin {Φ = ⟦ M ⟧} (⟦⟧-fin M)) app-mono app-fin
⟦⟧-fin (cast M [ c ]) =
  bind-fin {Ψ = ⟦ M ⟧} {Θ = λ ρ → ⟦ c ⟧ᶜ (ρ zero)}
    (⟦⟧-mono M) (⟦⟧-fin M)
    (λ ρ⊆ → ⟦⟧ᶜ-mono c (ρ⊆ zero)) (Finitary→Finₑ {f = ⟦ c ⟧ᶜ} (⟦⟧ᶜ-fin c))
⟦⟧-fin blame = const-fin

------------------------------------------------------------------------
-- The β law of Λ
------------------------------------------------------------------------

Λ-β-gen : ∀ {Φ} → Monoₑ Φ → Finₑ Φ → ∀ ρ {E} → ValSet E → Conv E
  → Φ (E • ρ) ⊆ Λ (λ Y → Φ (Y • ρ)) ● E
Λ-β-gen {Φ = Φ} mΦ fΦ ρ {E} noω (e , e∈ , e≢) w w∈ =
  U , (mΦ incl w (proj₂ (proj₂ r)) , (λ ()) , noerrU) , U⊆ , (λ ())
  where
  r = fΦ (E • ρ) w w∈
  φ = proj₁ r
  U : List Val
  U = e ∷ φ zero
  U⊆ : mem U ⊆ E
  U⊆ d (here refl) = e∈
  U⊆ d (there d∈) = proj₁ (proj₂ r) zero d d∈
  incl : ⟪ φ ⟫ ⊆ₑ (mem U • ρ)
  incl zero d d∈ = there d∈
  incl (suc x) = proj₁ (proj₂ r) (suc x)
  noerrU : NoErr U
  noerrU ω∈ = noω (U⊆ ω ω∈)

Λ-β : ∀ N ρ {E} → ValSet E → Conv E
  → ⟦ N ⟧ (E • ρ) ⊆ Λ (λ Y → ⟦ N ⟧ (Y • ρ)) ● E
Λ-β N ρ = Λ-β-gen {Φ = ⟦ N ⟧} (⟦⟧-mono N) (⟦⟧-fin N) ρ

Λ-βᶜ : ∀ c d X {E} → ValSet E → Conv E
  → (⟦ c ⟧ᶜ E ≫= λ Y₁ → (X ● Y₁) ≫= ⟦ d ⟧ᶜ)
    ⊆ Λ (λ Y → ⟦ c ⟧ᶜ Y ≫= λ Y₁ → (X ● Y₁) ≫= ⟦ d ⟧ᶜ) ● E
Λ-βᶜ c d X =
  Λ-β-gen {Φ = W} mW fW (X • ρ₀)
  where
  W : Env → 𝒫
  W ρ = ⟦ c ⟧ᶜ (ρ zero) ≫= λ Y₁ → (ρ (suc zero) ● Y₁) ≫= ⟦ d ⟧ᶜ
  mW : Monoₑ W
  mW = bind-mono {Ψ = λ ρ → ⟦ c ⟧ᶜ (ρ zero)}
         {Θ = λ ρ → (ρ (suc (suc zero)) ● ρ zero) ≫= ⟦ d ⟧ᶜ}
         (λ ρ⊆ → ⟦⟧ᶜ-mono c (ρ⊆ zero))
         (wrapₑ-mono (⟦⟧ᶜ-mono d) (suc (suc zero)))
  fW : Finₑ W
  fW = bind-fin {Ψ = λ ρ → ⟦ c ⟧ᶜ (ρ zero)}
         {Θ = λ ρ → (ρ (suc (suc zero)) ● ρ zero) ≫= ⟦ d ⟧ᶜ}
         (λ ρ⊆ → ⟦⟧ᶜ-mono c (ρ⊆ zero))
         (Finitary→Finₑ {f = ⟦ c ⟧ᶜ} (⟦⟧ᶜ-fin c))
         (wrapₑ-mono (⟦⟧ᶜ-mono d) (suc (suc zero)))
         (wrapₑ-fin (⟦⟧ᶜ-mono d) (⟦⟧ᶜ-fin d) (suc (suc zero)))

------------------------------------------------------------------------
-- The body of a function wrapper, as a function of its argument
------------------------------------------------------------------------

wrap-mono : ∀ X d → Mono (λ Y₁ → (X ● Y₁) ≫= ⟦ d ⟧ᶜ)
wrap-mono X d Y⊆ = ≫=-mono (●-mono {D = X} ⊆-refl Y⊆) (⟦⟧ᶜ-mono d)

wrap-fin : ∀ X d → Finitary (λ Y₁ → (X ● Y₁) ≫= ⟦ d ⟧ᶜ)
wrap-fin X d Y₁ w w∈ =
  proj₁ r zero , proj₁ (proj₂ r) zero ,
  ≫=-mono (●-mono (proj₁ (proj₂ r) (suc zero)) ⊆-refl) (⟦⟧ᶜ-mono d)
    w (proj₂ (proj₂ r))
  where
  r = wrapₑ-fin (⟦⟧ᶜ-mono d) (⟦⟧ᶜ-fin d) (suc zero) (Y₁ • X • ρ₀) w w∈
