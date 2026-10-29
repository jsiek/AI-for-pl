module proof.Denot.DenotProps where

-- File Charter:
--   * Basic properties of the GTSFImp denotation (`Denot.Denotation`),
--     ported from PolyG's `proof/DenotProps`:
--       - monotonicity of the model operators, of transformers (reveals,
--         conversions, casts) in their input, and of terms in their
--         environment;
--       - finite support (continuity) of transformers and of terms;
--       - laws of bind;
--       - consistency of finite lists drawn from a consistent set;
--       - the β law of `Λᶠ` in both directions.
--   * Transformers (`𝒱 → ℕ → ℛ`) are handled generically: sequencing,
--     function proxies, conversion ∀-proxies and cast ∀-proxies each get
--     one monotonicity and one finite-support lemma, and reveals,
--     conversions and casts follow by induction.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
  renaming (subst to substEq)
open import Relation.Nullary using (yes; no)

open import Types using (Ty; TyCtx; TyVar; ＇_; ‵_; ★; _⇒_; `∀; Ground;
  ★⇒★; ∀★; renameᵗ; extᵗ; ⇑ᵗ)
open import Consistency
open import Conversion
open import CastTerms using (Term; `_; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_;
  _⟨_⟩; _↑_; _↓_; blame)
open import Denot.GraphModel
open import Denot.Denotation

------------------------------------------------------------------------
-- Inclusion
------------------------------------------------------------------------

⊆-refl : ∀ {D} → D ⊆ D
⊆-refl v v∈ = v∈

⊆-trans : ∀ {D E F} → D ⊆ E → E ⊆ F → D ⊆ F
⊆-trans D⊆ E⊆ v v∈ = E⊆ v (D⊆ v v∈)

⊆ᴿ-refl : ∀ {R} → R ⊆ᴿ R
⊆ᴿ-refl r r∈ = r∈

⊆ᴿ-trans : ∀ {R S T} → R ⊆ᴿ S → S ⊆ᴿ T → R ⊆ᴿ T
⊆ᴿ-trans R⊆ S⊆ r r∈ = S⊆ r (R⊆ r r∈)

infix 4 _⊆ₑ_

_⊆ₑ_ : Env → Env → Set
ρ ⊆ₑ ρ′ = ∀ x → ρ x ⊆ ρ′ x

⊆ₑ-refl : ∀ {ρ} → ρ ⊆ₑ ρ
⊆ₑ-refl x = ⊆-refl

ext-⊆ₑ : ∀ {D D′ ρ ρ′} → D ⊆ D′ → ρ ⊆ₑ ρ′ → (D • ρ) ⊆ₑ (D′ • ρ′)
ext-⊆ₑ D⊆ ρ⊆ zero = D⊆
ext-⊆ₑ D⊆ ρ⊆ (suc x) = ρ⊆ x

single⊆ : ∀ {v D} → v ∈ D → mem (v ∷ []) ⊆ D
single⊆ v∈ u (here refl) = v∈

------------------------------------------------------------------------
-- Monotonicity of the operators
------------------------------------------------------------------------

⌊⌋-mono : ∀ {R R′} → R ⊆ᴿ R′ → ∀ m → ⌊ R ⌋ m ⊆ ⌊ R′ ⌋ m
⌊⌋-mono R⊆ m v v∈ = R⊆ (ret v m) v∈

Conv-mono : ∀ {D E} → D ⊆ E → Conv D → Conv E
Conv-mono D⊆ (v , v∈) = v , D⊆ v v∈

retᴿ-mono : ∀ {D E n} → D ⊆ E → retᴿ D n ⊆ᴿ retᴿ E n
retᴿ-mono D⊆ (ret v m) (eq , v∈) = eq , D⊆ v v∈

≫=-mono : ∀ {R R′ K K′} → R ⊆ᴿ R′
  → (∀ {D D′} m → D ⊆ D′ → K D m ⊆ᴿ K′ D′ m)
  → (R ≫= K) ⊆ᴿ (R′ ≫= K′)
≫=-mono R⊆ K⊆ r (inj₁ (eq , e∈)) = inj₁ (eq , R⊆ err e∈)
≫=-mono R⊆ K⊆ r (inj₂ (m , c , r∈)) =
  inj₂ (m , Conv-mono (⌊⌋-mono R⊆ m) c , K⊆ m (⌊⌋-mono R⊆ m) r r∈)

guard-mono : ∀ {v D D′ R R′} → D ⊆ D′ → R ⊆ᴿ R′
  → guard v D R ⊆ᴿ guard v D′ R′
guard-mono D⊆ R⊆ r (v∈ , r∈) = D⊆ _ v∈ , R⊆ r r∈

Λᶠ-mono : ∀ {F F′} → (∀ D m → F D m ⊆ᴿ F′ D m) → Λᶠ F ⊆ Λᶠ F′
Λᶠ-mono F⊆ (U ⟼ r at m) (r∈ , ne , c) = F⊆ (mem U) m r r∈ , ne , c
Λᶠ-mono F⊆ νλ tt = tt

●-mono : ∀ {D D′ E E′ m} → D ⊆ D′ → E ⊆ E′
  → (D ●[ m ] E) ⊆ᴿ (D′ ●[ m ] E′)
●-mono D⊆ E⊆ r (U , e∈ , U⊆ , ne) = U , D⊆ _ e∈ , ⊆-trans U⊆ E⊆ , ne

Λᴾ-mono : ∀ {F F′} → (∀ σ → F σ ⊆ᴿ F′ σ) → Λᴾ F ⊆ Λᴾ F′
Λᴾ-mono F⊆ (σ ⟼∀ r) r∈ = F⊆ σ r r∈
Λᴾ-mono F⊆ ν∀ tt = tt

◆-mono : ∀ {D D′ σ} → D ⊆ D′ → (D ◆ σ) ⊆ᴿ (D′ ◆ σ)
◆-mono D⊆ r r∈ = D⊆ _ r∈

sealᴾ-mono : ∀ {σ D D′} → D ⊆ D′ → sealᴾ σ D ⊆ sealᴾ σ D′
sealᴾ-mono D⊆ (sealᵛ σ′ v) (e , v∈) = e , D⊆ v v∈

unsealᴾ-mono : ∀ {σ D D′} → D ⊆ D′ → unsealᴾ σ D ⊆ unsealᴾ σ D′
unsealᴾ-mono D⊆ v v∈ = D⊆ _ v∈

injᴾ-mono : ∀ {G D D′} → D ⊆ D′ → injᴾ G D ⊆ injᴾ G D′
injᴾ-mono D⊆ (injᵛ H v) (eq , v∈) = eq , D⊆ v v∈

proj-mono : ∀ {G D D′ m} → D ⊆ D′ → proj G D m ⊆ᴿ proj G D′ m
proj-mono D⊆ (ret v m′) (eq , v∈) = eq , D⊆ _ v∈
proj-mono D⊆ err (H , v , v∈ , ne) = H , v , D⊆ _ v∈ , ne

δᴾ-mono : ∀ {op D D′ E E′} → D ⊆ D′ → E ⊆ E′ → δᴾ op D E ⊆ δᴾ op D′ E′
δᴾ-mono D⊆ E⊆ (vconst κ″) (κ , κ′ , d∈ , e∈ , δκ) =
  κ , κ′ , D⊆ _ d∈ , E⊆ _ e∈ , δκ

unsealR-mono : ∀ ρ {D D′} → D ⊆ D′ → unsealR ρ D ⊆ unsealR ρ D′
unsealR-mono (sealʳ σ) D⊆ = unsealᴾ-mono D⊆
unsealR-mono starʳ D⊆ = D⊆

sealR-mono : ∀ ρ {D D′} → D ⊆ D′ → sealR ρ D ⊆ sealR ρ D′
sealR-mono (sealʳ σ) D⊆ = sealᴾ-mono D⊆
sealR-mono starʳ D⊆ = D⊆

injR-mono : ∀ {Δ} {G : Ty Δ} (g : Ground G) (θ : REnv Δ) {D D′}
  → D ⊆ D′ → injR g θ D ⊆ injR g θ D′
injR-mono (＇ X) θ D⊆ with θ X
injR-mono (＇ X) θ D⊆ | sealʳ σ = injᴾ-mono D⊆
injR-mono (＇ X) θ D⊆ | starʳ = D⊆
injR-mono (‵ ι) θ D⊆ = injᴾ-mono D⊆
injR-mono ★⇒★ θ D⊆ = injᴾ-mono D⊆
injR-mono ∀★ θ D⊆ = injᴾ-mono D⊆

------------------------------------------------------------------------
-- Laws of bind
------------------------------------------------------------------------

-- the results of R that return a value all end at counter n
Pure : ℛ → ℕ → Set
Pure R n = ∀ v m → ret v m ∈ᴿ R → m ≡ n

retᴿ-pure : ∀ {D n} → Pure (retᴿ D n) n
retᴿ-pure v m (eq , v∈) = eq

≫=-unit : ∀ {R} → R ⊆ᴿ (R ≫= λ D m → retᴿ D m)
≫=-unit (ret v m) v∈ = inj₂ (m , (v , v∈) , refl , v∈)
≫=-unit err e∈ = inj₁ (refl , e∈)

≫=-unit⁻ : ∀ {R} → (R ≫= λ D m → retᴿ D m) ⊆ᴿ R
≫=-unit⁻ r (inj₁ (refl , e∈)) = e∈
≫=-unit⁻ (ret v m) (inj₂ (m′ , c , refl , v∈)) = v∈

-- a value on the left of a bind
≫=-retᴸ : ∀ {R D n K} → R ⊆ᴿ retᴿ D n
  → (∀ {E E′} m → E ⊆ E′ → K E m ⊆ᴿ K E′ m)
  → (R ≫= K) ⊆ᴿ K D n
≫=-retᴸ R⊆ Km r (inj₁ (eq , e∈)) = ⊥-elim (R⊆ err e∈)
≫=-retᴸ R⊆ Km r (inj₂ (m , (v , v∈) , r∈)) with R⊆ (ret v m) v∈
≫=-retᴸ R⊆ Km r (inj₂ (m , (v , v∈) , r∈)) | refl , v∈D =
  Km m (λ u u∈ → proj₂ (R⊆ (ret u m) u∈)) r r∈

≫=-retᴿ : ∀ {R D n K} → retᴿ D n ⊆ᴿ R → Conv D
  → (∀ {E E′} m → E ⊆ E′ → K E m ⊆ᴿ K E′ m)
  → K D n ⊆ᴿ (R ≫= K)
≫=-retᴿ {n = n} R⊇ (v , v∈) Km r r∈ =
  inj₂ (n , (v , R⊇ (ret v n) (refl , v∈)) ,
        Km n (λ u u∈ → R⊇ (ret u n) (refl , u∈)) r r∈)

-- associativity, when the left side returns at a single counter
≫=-assoc : ∀ {R K L n} → Pure R n
  → (∀ {D D′} m → D ⊆ D′ → L D m ⊆ᴿ L D′ m)
  → ((R ≫= K) ≫= L) ⊆ᴿ (R ≫= λ D m → K D m ≫= L)
≫=-assoc pR Lm r (inj₁ (eq , inj₁ (_ , e∈R))) = inj₁ (eq , e∈R)
≫=-assoc pR Lm r (inj₁ (eq , inj₂ (m , c , e∈K))) =
  inj₂ (m , c , inj₁ (eq , e∈K))
≫=-assoc pR Lm r (inj₂ (m′ , (u , inj₁ (() , _)) , r∈))
≫=-assoc {R = R} {K = K} pR Lm r
    (inj₂ (m′ , (u , inj₂ (m , c , u∈K)) , r∈)) =
  inj₂ (m , c , inj₂ (m′ , (u , u∈K) , Lm m′ sub r r∈))
  where
  sub : ⌊ R ≫= K ⌋ m′ ⊆ ⌊ K (⌊ R ⌋ m) m ⌋ m′
  sub w (inj₁ (() , _))
  sub w (inj₂ (m″ , c″ , w∈)) =
    substEq (λ k → ret w m′ ∈ᴿ K (⌊ R ⌋ k) k)
      (trans (pR _ m″ (proj₂ c″)) (sym (pR _ m (proj₂ c)))) w∈

guard-elim : ∀ {v D R} → guard v D R ⊆ᴿ R
guard-elim r (v∈ , r∈) = r∈

guard-intro : ∀ {v D R} → v ∈ D → R ⊆ᴿ guard v D R
guard-intro v∈ r r∈ = v∈ , r∈

-- application of an abstraction, in the easy direction
Λᶠ-β⁻ : ∀ {F E m} → (∀ {D D′} m → D ⊆ D′ → F D m ⊆ᴿ F D′ m)
  → (Λᶠ F ●[ m ] E) ⊆ᴿ F E m
Λᶠ-β⁻ Fm r (U , (r∈ , ne , c) , U⊆ , ne′) = Fm _ U⊆ r r∈

------------------------------------------------------------------------
-- Functions of an environment: monotonicity and finite support
------------------------------------------------------------------------

FEnv : Set
FEnv = ℕ → List Val

⟪_⟫ : FEnv → Env
⟪ φ ⟫ x = mem (φ x)

infix 4 _⊑ₑ_

_⊑ₑ_ : FEnv → Env → Set
φ ⊑ₑ ρ = ∀ x → mem (φ x) ⊆ ρ x

Monoₑ : ∀ {A : Set} → (Env → A → Set) → Set₁
Monoₑ Φ = ∀ {ρ ρ′} → ρ ⊆ₑ ρ′ → ∀ a → Φ ρ a → Φ ρ′ a

Finₑ : ∀ {A : Set} → (Env → A → Set) → Set₁
Finₑ Φ = ∀ ρ a → Φ ρ a → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × Φ ⟪ φ ⟫ a)

tailₑ : Env → Env
tailₑ ρ x = ρ (suc x)

∅ₑ : FEnv
∅ₑ x = []

∅ₑ-⊑ : ∀ ρ → ∅ₑ ⊑ₑ ρ
∅ₑ-⊑ ρ x v ()

join : FEnv → FEnv → FEnv
join φ ψ x = φ x ++ ψ x

join-⊑ : ∀ {φ ψ ρ} → φ ⊑ₑ ρ → ψ ⊑ₑ ρ → join φ ψ ⊑ₑ ρ
join-⊑ {φ = φ} φ⊑ ψ⊑ x v v∈ with ∈-++⁻ (φ x) v∈
join-⊑ {φ = φ} φ⊑ ψ⊑ x v v∈ | inj₁ v∈φ = φ⊑ x v v∈φ
join-⊑ {φ = φ} φ⊑ ψ⊑ x v v∈ | inj₂ v∈ψ = ψ⊑ x v v∈ψ

join-l : ∀ {φ ψ} → ⟪ φ ⟫ ⊆ₑ ⟪ join φ ψ ⟫
join-l x v v∈ = ∈-++⁺ˡ v∈

join-r : ∀ {φ ψ} → ⟪ ψ ⟫ ⊆ₑ ⟪ join φ ψ ⟫
join-r {φ = φ} x v v∈ = ∈-++⁺ʳ (φ x) v∈

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

const-fin : ∀ {A : Set} {X : A → Set} → Finₑ (λ ρ → X)
const-fin ρ a a∈ = ∅ₑ , ∅ₑ-⊑ ρ , a∈

var-mono : ∀ x → Monoₑ (λ ρ → ρ x)
var-mono x ρ⊆ = ρ⊆ x

at0 : List Val → FEnv
at0 L zero = L
at0 L (suc x) = []

var0-fin : Finₑ (λ ρ → ρ zero)
var0-fin ρ w w∈ = at0 (w ∷ []) , ⊑ , here refl
  where
  ⊑ : at0 (w ∷ []) ⊑ₑ ρ
  ⊑ zero v (here refl) = w∈
  ⊑ (suc x) v ()

shiftₑ : FEnv → FEnv
shiftₑ φ zero = []
shiftₑ φ (suc x) = φ x

shift-mono : ∀ {A : Set} {Φ : Env → A → Set} → Monoₑ Φ
  → Monoₑ (λ ρ → Φ (tailₑ ρ))
shift-mono m ρ⊆ = m (λ x → ρ⊆ (suc x))

shift-fin : ∀ {A : Set} {Φ : Env → A → Set} → Finₑ Φ
  → Finₑ (λ ρ → Φ (tailₑ ρ))
shift-fin f ρ w w∈ =
  shiftₑ (proj₁ r) , ⊑ , proj₂ (proj₂ r)
  where
  r = f (tailₑ ρ) w w∈
  ⊑ : shiftₑ (proj₁ r) ⊑ₑ ρ
  ⊑ zero v ()
  ⊑ (suc x) = proj₁ (proj₂ r) x

var-fin : ∀ x → Finₑ (λ ρ → ρ x)
var-fin zero = var0-fin
var-fin (suc x) = shift-fin {Φ = λ ρ → ρ x} (var-fin x)

ret-mono : ∀ {Ψ : Env → 𝒱} {n} → Monoₑ Ψ → Monoₑ (λ ρ → retᴿ (Ψ ρ) n)
ret-mono mΨ ρ⊆ = retᴿ-mono (mΨ ρ⊆)

ret-fin : ∀ {Ψ : Env → 𝒱} {n} → Finₑ Ψ → Finₑ (λ ρ → retᴿ (Ψ ρ) n)
ret-fin fΨ ρ (ret v m) (eq , v∈) with fΨ ρ v v∈
ret-fin fΨ ρ (ret v m) (eq , v∈) | φ , φ⊑ , v∈′ = φ , φ⊑ , eq , v∈′

bind-mono : ∀ {Ψ : Env → ℛ} {Θ : ℕ → Env → ℛ}
  → Monoₑ Ψ → (∀ m → Monoₑ (Θ m))
  → Monoₑ (λ ρ → Ψ ρ ≫= λ D m → Θ m (D • ρ))
bind-mono mΨ mΘ ρ⊆ =
  ≫=-mono (mΨ ρ⊆) (λ m D⊆ → mΘ m (ext-⊆ₑ D⊆ ρ⊆))

bind-fin : ∀ {Ψ : Env → ℛ} {Θ : ℕ → Env → ℛ}
  → Monoₑ Ψ → Finₑ Ψ → (∀ m → Monoₑ (Θ m)) → (∀ m → Finₑ (Θ m))
  → Finₑ (λ ρ → Ψ ρ ≫= λ D m → Θ m (D • ρ))
bind-fin mΨ fΨ mΘ fΘ ρ w (inj₁ (eq , e∈)) =
  proj₁ r , proj₁ (proj₂ r) , inj₁ (eq , proj₂ (proj₂ r))
  where
  r = fΨ ρ err e∈
bind-fin {Ψ = Ψ} {Θ = Θ} mΨ fΨ mΘ fΘ ρ w (inj₂ (m , (v , v∈) , w∈)) =
  φ , φ⊑ , inj₂ (m , (v , mΨ ⊆d (ret v m) (proj₂ (proj₂ rd))) ,
                 mΘ m incl w (proj₂ (proj₂ rθ)))
  where
  rd = fΨ ρ (ret v m) v∈
  rθ = fΘ m (⌊ Ψ ρ ⌋ m • ρ) w w∈
  φd = proj₁ rd
  φθ = proj₁ rθ
  φθ⊑ = proj₁ (proj₂ rθ)
  rk = collect (λ k ρ′ → ret k m ∈ᴿ Ψ ρ′) (λ k ρ⊆ → mΨ ρ⊆ (ret k m))
         (φθ zero) (λ k k∈ → fΨ ρ (ret k m) (φθ⊑ zero k k∈))
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
  incl : ⟪ φθ ⟫ ⊆ₑ (⌊ Ψ ⟪ φ ⟫ ⌋ m • ⟪ φ ⟫)
  incl zero k k∈ =
    mΨ (λ x u u∈ → join-r {φ = φd} {ψ = φ₂} x u
                     (join-r {φ = φ₁} {ψ = proj₁ rk} x u u∈))
       (ret k m) (proj₂ (proj₂ rk) k k∈)
  incl (suc x) k k∈ =
    join-r {φ = φd} {ψ = φ₂} x k (join-l {φ = φ₁} {ψ = proj₁ rk} x k k∈)

join₂ : ∀ {A B : Set} {Φ₁ : Env → A → Set} {Φ₂ : Env → B → Set} {ρ a b}
  → Monoₑ Φ₁ → Monoₑ Φ₂
  → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × Φ₁ ⟪ φ ⟫ a)
  → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × Φ₂ ⟪ φ ⟫ b)
  → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × Φ₁ ⟪ φ ⟫ a × Φ₂ ⟪ φ ⟫ b)
join₂ m₁ m₂ (φ₁ , φ₁⊑ , a∈) (φ₂ , φ₂⊑ , b∈) =
  join φ₁ φ₂ , join-⊑ φ₁⊑ φ₂⊑ ,
  m₁ (join-l {φ = φ₁} {ψ = φ₂}) _ a∈ , m₂ (join-r {φ = φ₁} {ψ = φ₂}) _ b∈

Λᶠ-monoₑ : ∀ {Φ : ℕ → Env → ℛ} → (∀ m → Monoₑ (Φ m))
  → Monoₑ (λ ρ → Λᶠ (λ D m → Φ m (D • ρ)))
Λᶠ-monoₑ mΦ ρ⊆ = Λᶠ-mono (λ D m → mΦ m (ext-⊆ₑ ⊆-refl ρ⊆))

Λᶠ-fin : ∀ {Φ : ℕ → Env → ℛ} → (∀ m → Monoₑ (Φ m)) → (∀ m → Finₑ (Φ m))
  → Finₑ (λ ρ → Λᶠ (λ D m → Φ m (D • ρ)))
Λᶠ-fin mΦ fΦ ρ (U ⟼ r at m) (r∈ , ne , c) =
  φ′ , (λ x → proj₁ (proj₂ rr) (suc x)) ,
  mΦ m incl r (proj₂ (proj₂ rr)) , ne , c
  where
  rr = fΦ m (mem U • ρ) r r∈
  φ′ : FEnv
  φ′ x = proj₁ rr (suc x)
  incl : ⟪ proj₁ rr ⟫ ⊆ₑ (mem U • ⟪ φ′ ⟫)
  incl zero = proj₁ (proj₂ rr) zero
  incl (suc x) = ⊆-refl
Λᶠ-fin mΦ fΦ ρ νλ tt = ∅ₑ , ∅ₑ-⊑ ρ , tt

Λᴾ-monoₑ : ∀ {Φ : Seal → Env → ℛ} → (∀ σ → Monoₑ (Φ σ))
  → Monoₑ (λ ρ → Λᴾ (λ σ → Φ σ ρ))
Λᴾ-monoₑ mΦ ρ⊆ = Λᴾ-mono (λ σ → mΦ σ ρ⊆)

Λᴾ-fin : ∀ {Φ : Seal → Env → ℛ} → (∀ σ → Finₑ (Φ σ))
  → Finₑ (λ ρ → Λᴾ (λ σ → Φ σ ρ))
Λᴾ-fin fΦ ρ (σ ⟼∀ r) r∈ = fΦ σ ρ r r∈
Λᴾ-fin fΦ ρ ν∀ tt = ∅ₑ , ∅ₑ-⊑ ρ , tt

●-monoₑ : ∀ {Ψ₁ Ψ₂ : Env → 𝒱} {m} → Monoₑ Ψ₁ → Monoₑ Ψ₂
  → Monoₑ (λ ρ → Ψ₁ ρ ●[ m ] Ψ₂ ρ)
●-monoₑ m₁ m₂ ρ⊆ = ●-mono (m₁ ρ⊆) (m₂ ρ⊆)

●-fin : ∀ {Ψ₁ Ψ₂ : Env → 𝒱} {m} → Monoₑ Ψ₁ → Monoₑ Ψ₂
  → Finₑ Ψ₁ → Finₑ Ψ₂ → Finₑ (λ ρ → Ψ₁ ρ ●[ m ] Ψ₂ ρ)
●-fin {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {m = m} m₁ m₂ f₁ f₂ ρ r (U , e∈ , U⊆ , ne) =
  join φe φk , join-⊑ (proj₁ (proj₂ re)) (proj₁ (proj₂ rk)) ,
  (U , m₁ (join-l {φ = φe} {ψ = φk}) _ (proj₂ (proj₂ re)) ,
   (λ v v∈ → m₂ (join-r {φ = φe} {ψ = φk}) v (proj₂ (proj₂ rk) v v∈)) ,
   ne)
  where
  re = f₁ ρ (U ⟼ r at m) e∈
  rk = collect (λ k ρ′ → k ∈ Ψ₂ ρ′) (λ k ρ⊆ → m₂ ρ⊆ k) U
         (λ k k∈ → f₂ ρ k (U⊆ k k∈))
  φe = proj₁ re
  φk = proj₁ rk

◆-fin : ∀ {Ψ : Env → 𝒱} {σ} → Finₑ Ψ → Finₑ (λ ρ → Ψ ρ ◆ σ)
◆-fin {σ = σ} fΨ ρ r r∈ = fΨ ρ (σ ⟼∀ r) r∈

sealᴾ-fin : ∀ {Ψ : Env → 𝒱} {σ} → Finₑ Ψ → Finₑ (λ ρ → sealᴾ σ (Ψ ρ))
sealᴾ-fin fΨ ρ (sealᵛ σ′ v) (e , v∈) with fΨ ρ v v∈
sealᴾ-fin fΨ ρ (sealᵛ σ′ v) (e , v∈) | φ , φ⊑ , v∈′ = φ , φ⊑ , e , v∈′

unsealᴾ-fin : ∀ {Ψ : Env → 𝒱} {σ} → Finₑ Ψ
  → Finₑ (λ ρ → unsealᴾ σ (Ψ ρ))
unsealᴾ-fin {σ = σ} fΨ ρ v v∈ = fΨ ρ (sealᵛ σ v) v∈

injᴾ-fin : ∀ {Ψ : Env → 𝒱} {G} → Finₑ Ψ → Finₑ (λ ρ → injᴾ G (Ψ ρ))
injᴾ-fin fΨ ρ (injᵛ H v) (eq , v∈) with fΨ ρ v v∈
injᴾ-fin fΨ ρ (injᵛ H v) (eq , v∈) | φ , φ⊑ , v∈′ = φ , φ⊑ , eq , v∈′

proj-fin : ∀ {Ψ : Env → 𝒱} {G m} → Finₑ Ψ → Finₑ (λ ρ → proj G (Ψ ρ) m)
proj-fin {G = G} fΨ ρ (ret v m′) (eq , v∈) with fΨ ρ (injᵛ G v) v∈
proj-fin {G = G} fΨ ρ (ret v m′) (eq , v∈) | φ , φ⊑ , v∈′ =
  φ , φ⊑ , eq , v∈′
proj-fin fΨ ρ err (H , v , v∈ , ne) with fΨ ρ (injᵛ H v) v∈
proj-fin fΨ ρ err (H , v , v∈ , ne) | φ , φ⊑ , v∈′ =
  φ , φ⊑ , H , v , v∈′ , ne

δᴾ-fin : ∀ {Ψ₁ Ψ₂ : Env → 𝒱} {op} → Monoₑ Ψ₁ → Monoₑ Ψ₂
  → Finₑ Ψ₁ → Finₑ Ψ₂ → Finₑ (λ ρ → δᴾ op (Ψ₁ ρ) (Ψ₂ ρ))
δᴾ-fin m₁ m₂ f₁ f₂ ρ (vconst κ″) (κ , κ′ , d∈ , e∈ , δκ)
  with join₂ m₁ m₂ (f₁ ρ (vconst κ) d∈) (f₂ ρ (vconst κ′) e∈)
δᴾ-fin m₁ m₂ f₁ f₂ ρ (vconst κ″) (κ , κ′ , d∈ , e∈ , δκ)
    | φ , φ⊑ , d∈′ , e∈′ =
  φ , φ⊑ , κ , κ′ , d∈′ , e∈′ , δκ

------------------------------------------------------------------------
-- Finite support of functions of one set
------------------------------------------------------------------------

Finitary : (𝒱 → ℛ) → Set₁
Finitary C =
  ∀ E r → r ∈ᴿ C E → Σ[ L ∈ List Val ] (mem L ⊆ E × r ∈ᴿ C (mem L))

Finitary→Finₑ : ∀ {C} → Finitary C → Finₑ (λ ρ → C (ρ zero))
Finitary→Finₑ fin ρ r r∈ = at0 (proj₁ rr) , ⊑ , proj₂ (proj₂ rr)
  where
  rr = fin (ρ zero) r r∈
  ⊑ : at0 (proj₁ rr) ⊑ₑ ρ
  ⊑ zero = proj₁ (proj₂ rr)
  ⊑ (suc x) v ()

Finₑ→Finitary : ∀ C → Finₑ (λ ρ → C (ρ zero)) → Finitary C
Finₑ→Finitary C fin E r r∈ =
  proj₁ rr zero , proj₁ (proj₂ rr) zero , proj₂ (proj₂ rr)
  where
  rr = fin (E • ρ₀) r r∈

------------------------------------------------------------------------
-- Transformers
------------------------------------------------------------------------

-- a transformer takes a set of values and a counter to results
Trans : Set₁
Trans = 𝒱 → ℕ → ℛ

MonoT : Trans → Set₁
MonoT T = ∀ {D D′} m → D ⊆ D′ → T D m ⊆ᴿ T D′ m

FinT : Trans → Set₁
FinT T = ∀ m → Finitary (λ E → T E m)

transₑ-mono : ∀ {T} → MonoT T → ∀ m → Monoₑ (λ ρ → T (ρ zero) m)
transₑ-mono mT m ρ⊆ = mT m (ρ⊆ zero)

ret-monoT : MonoT retᴿ
ret-monoT m = retᴿ-mono

ret-finT : FinT retᴿ
ret-finT m E (ret v m′) (eq , v∈) = v ∷ [] , single⊆ v∈ , eq , here refl

-- sequencing: `T₁` then `T₂`
seqT : Trans → Trans → Trans
seqT T₁ T₂ E m = T₁ E m ≫= T₂

seq-monoT : ∀ {T₁ T₂} → MonoT T₁ → MonoT T₂ → MonoT (seqT T₁ T₂)
seq-monoT m₁ m₂ m E⊆ = ≫=-mono (m₁ m E⊆) m₂

seq-finT : ∀ {T₁ T₂} → MonoT T₁ → FinT T₁ → MonoT T₂ → FinT T₂
  → FinT (seqT T₁ T₂)
seq-finT {T₁} {T₂} m₁ f₁ m₂ f₂ m =
  Finₑ→Finitary (λ E → seqT T₁ T₂ E m)
    (bind-fin {Ψ = λ ρ → T₁ (ρ zero) m} {Θ = λ m′ ρ → T₂ (ρ zero) m′}
      (transₑ-mono m₁ m) (Finitary→Finₑ (f₁ m))
      (transₑ-mono m₂) (λ m′ → Finitary→Finₑ (f₂ m′)))

-- a pointwise operation on sets, then return
pointT : (𝒱 → 𝒱) → Trans
pointT f E m = retᴿ (f E) m

point-monoT : ∀ {f} → (∀ {D D′} → D ⊆ D′ → f D ⊆ f D′) → MonoT (pointT f)
point-monoT fm m E⊆ = retᴿ-mono (fm E⊆)

point-finT : ∀ {f} → (∀ {Ψ : Env → 𝒱} → Finₑ Ψ → Finₑ (λ ρ → f (Ψ ρ)))
  → FinT (pointT f)
point-finT {f} ff m =
  Finₑ→Finitary (λ E → pointT f E m) (ret-fin (ff var0-fin))

unsealR-fin : ∀ ρ {Ψ : Env → 𝒱} → Finₑ Ψ → Finₑ (λ ρ′ → unsealR ρ (Ψ ρ′))
unsealR-fin (sealʳ σ) fΨ = unsealᴾ-fin fΨ
unsealR-fin starʳ fΨ = fΨ

sealR-fin : ∀ ρ {Ψ : Env → 𝒱} → Finₑ Ψ → Finₑ (λ ρ′ → sealR ρ (Ψ ρ′))
sealR-fin (sealʳ σ) fΨ = sealᴾ-fin fΨ
sealR-fin starʳ fΨ = fΨ

-- function proxies

-- the body of a function proxy, as a function of its argument (variable
-- 0) and the proxied function (variable 1)
wrapᴱ : Trans → Trans → ℕ → Env → ℛ
wrapᴱ a b m ρ =
  a (ρ zero) m ≫= λ E₁ m₁ → (ρ (suc zero) ●[ m₁ ] E₁) ≫= b

wrap-mono : ∀ {a b} → MonoT a → MonoT b → ∀ m → Monoₑ (wrapᴱ a b m)
wrap-mono {a} {b} ma mb m =
  bind-mono {Ψ = λ ρ → a (ρ zero) m}
    {Θ = λ m₁ ρ → (ρ (suc (suc zero)) ●[ m₁ ] ρ zero) ≫= λ E₂ m₂ →
                  b ((E₂ • ρ) zero) m₂}
    (transₑ-mono ma m)
    (λ m₁ → bind-mono
      (●-monoₑ (var-mono (suc (suc zero))) (var-mono zero))
      (λ m₂ → transₑ-mono mb m₂))

wrap-fin : ∀ {a b} → MonoT a → FinT a → MonoT b → FinT b
  → ∀ m → Finₑ (wrapᴱ a b m)
wrap-fin {a} {b} ma fa mb fb m =
  bind-fin {Ψ = λ ρ → a (ρ zero) m}
    {Θ = λ m₁ ρ → (ρ (suc (suc zero)) ●[ m₁ ] ρ zero) ≫= λ E₂ m₂ →
                  b ((E₂ • ρ) zero) m₂}
    (transₑ-mono ma m) (Finitary→Finₑ (fa m))
    (λ m₁ → bind-mono
      (●-monoₑ (var-mono (suc (suc zero))) (var-mono zero))
      (λ m₂ → transₑ-mono mb m₂))
    (λ m₁ → bind-fin
      (●-monoₑ (var-mono (suc (suc zero))) (var-mono zero))
      (●-fin (var-mono (suc (suc zero))) (var-mono zero)
             (var-fin (suc (suc zero))) (var-fin zero))
      (λ m₂ → transₑ-mono mb m₂)
      (λ m₂ → Finitary→Finₑ (fb m₂)))

funProxy-mono : ∀ {a b} → MonoT b → MonoT (funProxy a b)
funProxy-mono {a} {b} mb m E⊆ =
  guard-mono E⊆ (retᴿ-mono (Λᶠ-mono (λ D m′ →
    ≫=-mono (⊆ᴿ-refl {R = a D m′}) (λ m₁ D⊆ →
      ≫=-mono (●-mono E⊆ D⊆) mb))))

funProxy-fin : ∀ {a b} → MonoT a → FinT a → MonoT b → FinT b
  → FinT (funProxy a b)
funProxy-fin ma fa mb fb m E (ret νλ m′) (e∈ , eq , tt) =
  νλ ∷ [] , single⊆ e∈ , here refl , eq , tt
funProxy-fin {a} {b} ma fa mb fb m E (ret (U ⟼ r at m″) m′)
    (e∈ , eq , r∈ , ne , c) =
  L , L⊆ , here refl , eq ,
  wrap-mono ma mb m″ incl r (proj₂ (proj₂ rr)) , ne , c
  where
  rr = wrap-fin ma fa mb fb m″ (mem U • E • ρ₀) r r∈
  φ = proj₁ rr
  L : List Val
  L = νλ ∷ φ (suc zero)
  L⊆ : mem L ⊆ E
  L⊆ v (here refl) = e∈
  L⊆ v (there v∈) = proj₁ (proj₂ rr) (suc zero) v v∈
  incl : ⟪ φ ⟫ ⊆ₑ (mem U • mem L • ρ₀)
  incl zero = proj₁ (proj₂ rr) zero
  incl (suc zero) v v∈ = there v∈
  incl (suc (suc x)) v v∈ = ⊥-elim (proj₁ (proj₂ rr) (suc (suc x)) v v∈)

-- ∀ proxies: instantiate the proxied value at a seal, then transform

-- the body of a ∀ proxy at seal σ, as a function of the proxied value
-- (variable 0): instantiate at `k σ`, then `t σ`
allᴱ : (Seal → Seal) → (Seal → Trans) → Seal → Env → ℛ
allᴱ k t σ ρ = (ρ zero ◆ k σ) ≫= t σ

all-mono : ∀ {k t} → (∀ σ → MonoT (t σ)) → ∀ σ → Monoₑ (allᴱ k t σ)
all-mono {k} {t} mt σ =
  bind-mono {Ψ = λ ρ → ρ zero ◆ k σ} {Θ = λ m₁ ρ → t σ (ρ zero) m₁}
    (λ ρ⊆ → ◆-mono (ρ⊆ zero)) (λ m₁ → transₑ-mono (mt σ) m₁)

all-fin : ∀ {k t} → (∀ σ → MonoT (t σ)) → (∀ σ → FinT (t σ))
  → ∀ σ → Finₑ (allᴱ k t σ)
all-fin {k} {t} mt ft σ =
  bind-fin {Ψ = λ ρ → ρ zero ◆ k σ} {Θ = λ m₁ ρ → t σ (ρ zero) m₁}
    (λ ρ⊆ → ◆-mono (ρ⊆ zero)) (◆-fin var0-fin)
    (λ m₁ → transₑ-mono (mt σ) m₁) (λ m₁ → Finitary→Finₑ (ft σ m₁))

-- the ∀ proxy itself
allProxy : (Seal → Seal) → (Seal → Trans) → Trans
allProxy k t E m =
  guard ν∀ E (retᴿ (Λᴾ (λ σ → (E ◆ k σ) ≫= t σ)) m)

allProxy-mono : ∀ {k t} → (∀ σ → MonoT (t σ)) → MonoT (allProxy k t)
allProxy-mono mt m E⊆ =
  guard-mono E⊆ (retᴿ-mono (Λᴾ-mono (λ σ → ≫=-mono (◆-mono E⊆) (mt σ))))

allProxy-fin : ∀ {k t} → (∀ σ → MonoT (t σ)) → (∀ σ → FinT (t σ))
  → FinT (allProxy k t)
allProxy-fin mt ft m E (ret ν∀ m′) (e∈ , eq , tt) =
  ν∀ ∷ [] , single⊆ e∈ , here refl , eq , tt
allProxy-fin {k} {t} mt ft m E (ret (σ ⟼∀ r) m′) (e∈ , eq , r∈) =
  L , L⊆ , here refl , eq , all-mono {k} {t} mt σ incl r (proj₂ (proj₂ rr))
  where
  rr = all-fin {k} {t} mt ft σ (E • ρ₀) r r∈
  φ = proj₁ rr
  L : List Val
  L = ν∀ ∷ φ zero
  L⊆ : mem L ⊆ E
  L⊆ v (here refl) = e∈
  L⊆ v (there v∈) = proj₁ (proj₂ rr) zero v v∈
  incl : ⟪ φ ⟫ ⊆ₑ (mem L • ρ₀)
  incl zero v v∈ = there v∈
  incl (suc x) v v∈ = ⊥-elim (proj₁ (proj₂ rr) (suc x) v v∈)

-- a conversion ∀ proxy is a ∀ proxy at the next seal
convAll≡ : ∀ inner body E m
  → convAllProxy inner body E m
    ≡ allProxy suc (λ σ → seqT (inner σ) (body σ)) E m
convAll≡ inner body E m = refl

------------------------------------------------------------------------
-- Reveals at one variable
------------------------------------------------------------------------

mutual
  revV-mono : ∀ {Δ} (C : Ty Δ) X θ → MonoT (revV C X θ)
  revV-mono (＇ Y) X θ m E⊆ with X ≟ Y
  revV-mono (＇ Y) X θ m E⊆ | yes _ = retᴿ-mono (unsealR-mono (θ X) E⊆)
  revV-mono (＇ Y) X θ m E⊆ | no _ = retᴿ-mono E⊆
  revV-mono (‵ ι) X θ m E⊆ = retᴿ-mono E⊆
  revV-mono ★ X θ m E⊆ = retᴿ-mono E⊆
  revV-mono (A ⇒ B) X θ = funProxy-mono {a = conV A X θ} (revV-mono B X θ)
  revV-mono (`∀ A) X θ =
    allProxy-mono (λ σ →
      seq-monoT (revV-mono A fzero (sealʳ (suc σ) •ʳ θ))
                (revV-mono A (fsuc X) (sealʳ σ •ʳ θ)))

  conV-mono : ∀ {Δ} (C : Ty Δ) X θ → MonoT (conV C X θ)
  conV-mono (＇ Y) X θ m E⊆ with X ≟ Y
  conV-mono (＇ Y) X θ m E⊆ | yes _ = retᴿ-mono (sealR-mono (θ X) E⊆)
  conV-mono (＇ Y) X θ m E⊆ | no _ = retᴿ-mono E⊆
  conV-mono (‵ ι) X θ m E⊆ = retᴿ-mono E⊆
  conV-mono ★ X θ m E⊆ = retᴿ-mono E⊆
  conV-mono (A ⇒ B) X θ = funProxy-mono {a = revV A X θ} (conV-mono B X θ)
  conV-mono (`∀ A) X θ =
    allProxy-mono (λ σ →
      seq-monoT (revV-mono A fzero (sealʳ (suc σ) •ʳ θ))
                (conV-mono A (fsuc X) (sealʳ σ •ʳ θ)))

mutual
  revV-fin : ∀ {Δ} (C : Ty Δ) X θ → FinT (revV C X θ)
  revV-fin (＇ Y) X θ m E r r∈ with X ≟ Y
  revV-fin (＇ Y) X θ m E r r∈ | yes _ =
    point-finT {f = unsealR (θ X)} (unsealR-fin (θ X)) m E r r∈
  revV-fin (＇ Y) X θ m E r r∈ | no _ = ret-finT m E r r∈
  revV-fin (‵ ι) X θ = ret-finT
  revV-fin ★ X θ = ret-finT
  revV-fin (A ⇒ B) X θ =
    funProxy-fin (conV-mono A X θ) (conV-fin A X θ)
      (revV-mono B X θ) (revV-fin B X θ)
  revV-fin (`∀ A) X θ =
    allProxy-fin
      (λ σ → seq-monoT (revV-mono A fzero (sealʳ (suc σ) •ʳ θ))
                       (revV-mono A (fsuc X) (sealʳ σ •ʳ θ)))
      (λ σ → seq-finT (revV-mono A fzero (sealʳ (suc σ) •ʳ θ))
                      (revV-fin A fzero (sealʳ (suc σ) •ʳ θ))
                      (revV-mono A (fsuc X) (sealʳ σ •ʳ θ))
                      (revV-fin A (fsuc X) (sealʳ σ •ʳ θ)))

  conV-fin : ∀ {Δ} (C : Ty Δ) X θ → FinT (conV C X θ)
  conV-fin (＇ Y) X θ m E r r∈ with X ≟ Y
  conV-fin (＇ Y) X θ m E r r∈ | yes _ =
    point-finT {f = sealR (θ X)} (sealR-fin (θ X)) m E r r∈
  conV-fin (＇ Y) X θ m E r r∈ | no _ = ret-finT m E r r∈
  conV-fin (‵ ι) X θ = ret-finT
  conV-fin ★ X θ = ret-finT
  conV-fin (A ⇒ B) X θ =
    funProxy-fin (revV-mono A X θ) (revV-fin A X θ)
      (conV-mono B X θ) (conV-fin B X θ)
  conV-fin (`∀ A) X θ =
    allProxy-fin
      (λ σ → seq-monoT (revV-mono A fzero (sealʳ (suc σ) •ʳ θ))
                       (conV-mono A (fsuc X) (sealʳ σ •ʳ θ)))
      (λ σ → seq-finT (revV-mono A fzero (sealʳ (suc σ) •ʳ θ))
                      (revV-fin A fzero (sealʳ (suc σ) •ʳ θ))
                      (conV-mono A (fsuc X) (sealʳ σ •ʳ θ))
                      (conV-fin A (fsuc X) (sealʳ σ •ʳ θ)))

------------------------------------------------------------------------
-- Conversions
------------------------------------------------------------------------

mutual
  conv↑-mono : ∀ {Δ A B} (c : Conv↑ Δ A B) θ → MonoT (⟦ c ⟧↑ θ)
  conv↑-mono (unseal X R) θ m E⊆ = retᴿ-mono (unsealR-mono (θ X) E⊆)
  conv↑-mono (c ↦↑ d) θ = funProxy-mono {a = ⟦ c ⟧↓ θ} (conv↑-mono d θ)
  conv↑-mono (`∀↑_ {A = C} c) θ =
    allProxy-mono (λ σ →
      seq-monoT (revV-mono C fzero (sealʳ (suc σ) •ʳ θ))
                (conv↑-mono c (sealʳ σ •ʳ θ)))
  conv↑-mono (id↑ A) θ m E⊆ = retᴿ-mono E⊆

  conv↓-mono : ∀ {Δ A B} (c : Conv↓ Δ A B) θ → MonoT (⟦ c ⟧↓ θ)
  conv↓-mono (seal X R) θ m E⊆ = retᴿ-mono (sealR-mono (θ X) E⊆)
  conv↓-mono (c ↦↓ d) θ = funProxy-mono {a = ⟦ c ⟧↑ θ} (conv↓-mono d θ)
  conv↓-mono (`∀↓_ {A = C} c) θ =
    allProxy-mono (λ σ →
      seq-monoT (revV-mono C fzero (sealʳ (suc σ) •ʳ θ))
                (conv↓-mono c (sealʳ σ •ʳ θ)))
  conv↓-mono (id↓ A) θ m E⊆ = retᴿ-mono E⊆

mutual
  conv↑-fin : ∀ {Δ A B} (c : Conv↑ Δ A B) θ → FinT (⟦ c ⟧↑ θ)
  conv↑-fin (unseal X R) θ =
    point-finT {f = unsealR (θ X)} (unsealR-fin (θ X))
  conv↑-fin (c ↦↑ d) θ =
    funProxy-fin (conv↓-mono c θ) (conv↓-fin c θ)
      (conv↑-mono d θ) (conv↑-fin d θ)
  conv↑-fin (`∀↑_ {A = C} c) θ =
    allProxy-fin
      (λ σ → seq-monoT (revV-mono C fzero (sealʳ (suc σ) •ʳ θ))
                       (conv↑-mono c (sealʳ σ •ʳ θ)))
      (λ σ → seq-finT (revV-mono C fzero (sealʳ (suc σ) •ʳ θ))
                      (revV-fin C fzero (sealʳ (suc σ) •ʳ θ))
                      (conv↑-mono c (sealʳ σ •ʳ θ))
                      (conv↑-fin c (sealʳ σ •ʳ θ)))
  conv↑-fin (id↑ A) θ = ret-finT

  conv↓-fin : ∀ {Δ A B} (c : Conv↓ Δ A B) θ → FinT (⟦ c ⟧↓ θ)
  conv↓-fin (seal X R) θ =
    point-finT {f = sealR (θ X)} (sealR-fin (θ X))
  conv↓-fin (c ↦↓ d) θ =
    funProxy-fin (conv↑-mono c θ) (conv↑-fin c θ)
      (conv↓-mono d θ) (conv↓-fin d θ)
  conv↓-fin (`∀↓_ {A = C} c) θ =
    allProxy-fin
      (λ σ → seq-monoT (revV-mono C fzero (sealʳ (suc σ) •ʳ θ))
                       (conv↓-mono c (sealʳ σ •ʳ θ)))
      (λ σ → seq-finT (revV-mono C fzero (sealʳ (suc σ) •ʳ θ))
                      (revV-fin C fzero (sealʳ (suc σ) •ʳ θ))
                      (conv↓-mono c (sealʳ σ •ʳ θ))
                      (conv↓-fin c (sealʳ σ •ʳ θ)))
  conv↓-fin (id↓ A) θ = ret-finT

------------------------------------------------------------------------
-- Casts
------------------------------------------------------------------------

projR-mono : ∀ {Δ} {G : Ty Δ} (g : Ground G) (θ : REnv Δ)
  → MonoT (projR g θ)
projR-mono (＇ X) θ m E⊆ with θ X
projR-mono (＇ X) θ m E⊆ | sealʳ σ = proj-mono E⊆
projR-mono (＇ X) θ m E⊆ | starʳ = retᴿ-mono E⊆
projR-mono (‵ ι) θ m E⊆ = proj-mono E⊆
projR-mono ★⇒★ θ m E⊆ = proj-mono E⊆
projR-mono ∀★ θ m E⊆ = proj-mono E⊆

proj-finT : ∀ G → FinT (proj G)
proj-finT G m = Finₑ→Finitary (λ E → proj G E m) (proj-fin var0-fin)

projR-fin : ∀ {Δ} {G : Ty Δ} (g : Ground G) (θ : REnv Δ)
  → FinT (projR g θ)
projR-fin (＇ X) θ m E r r∈ with θ X
projR-fin (＇ X) θ m E r r∈ | sealʳ σ = proj-finT (gσ σ) m E r r∈
projR-fin (＇ X) θ m E r r∈ | starʳ = ret-finT m E r r∈
projR-fin (‵ ι) θ = proj-finT (gι ι)
projR-fin ★⇒★ θ = proj-finT g⇒
projR-fin ∀★ θ = proj-finT g∀

injR-fin : ∀ {Δ} {G : Ty Δ} (g : Ground G) (θ : REnv Δ)
  → ∀ {Ψ : Env → 𝒱} → Finₑ Ψ → Finₑ (λ ρ → injR g θ (Ψ ρ))
injR-fin (＇ X) θ fΨ with θ X
injR-fin (＇ X) θ fΨ | sealʳ σ = injᴾ-fin fΨ
injR-fin (＇ X) θ fΨ | starʳ = fΨ
injR-fin (‵ ι) θ fΨ = injᴾ-fin fΨ
injR-fin ★⇒★ θ fΨ = injᴾ-fin fΨ
injR-fin ∀★ θ fΨ = injᴾ-fin fΨ

-- instantiating the input at a seal fixed by the counter
inst◆ : Trans
inst◆ E m = E ◆ suc m

inst◆-mono : MonoT inst◆
inst◆-mono m E⊆ = ◆-mono E⊆

inst◆-fin : FinT inst◆
inst◆-fin m E r r∈ = (suc m ⟼∀ r) ∷ [] , single⊆ r∈ , here refl

-- a gen value, as a transformer
genT : (Seal → Trans) → Trans
genT t E m = retᴿ (Λᴾ (λ σ → t σ E (suc σ))) m

genT-mono : ∀ {t} → (∀ σ → MonoT (t σ)) → MonoT (genT t)
genT-mono mt m E⊆ = retᴿ-mono (Λᴾ-mono (λ σ → mt σ (suc σ) E⊆))

genT-fin : ∀ {t} → (∀ σ → FinT (t σ)) → FinT (genT t)
genT-fin ft m E (ret ν∀ m′) (eq , tt) = [] , (λ v ()) , eq , tt
genT-fin {t} ft m E (ret (σ ⟼∀ r) m′) (eq , r∈)
  with ft σ (suc σ) E r r∈
genT-fin {t} ft m E (ret (σ ⟼∀ r) m′) (eq , r∈) | L , L⊆ , r∈′ =
  L , L⊆ , eq , r∈′

errT : Trans
errT E m = errᴿ

errT-mono : MonoT errT
errT-mono m E⊆ r r∈ = r∈

errT-fin : FinT errT
errT-fin m E err tt = [] , (λ v ()) , tt

-- the body of an `inst` cast at counter m, after the instantiation
instBodyT : ∀ {Δ} {μ : Env∼ Δ} (A : Ty (suc Δ)) {B : Ty Δ}
  → instᵐ μ ⊢ A ∼ ⇑ᵗ B → REnv Δ → ℕ → Trans
instBodyT A c θ m E₁ m₁ =
  ⟦ 〖 fzero , ＇ fsuc fzero ↑ renameᵗ (extᵗ fsuc) A 〗 ⟧↑
    (sealʳ (suc m) •ʳ sealʳ m •ʳ θ) E₁ m₁ ≫= λ E₂ m₂ →
  ⟦ 〖 fzero , ★ ↑ A 〗 ⟧↑ (sealʳ m •ʳ θ) E₂ m₂ ≫=
  ⟦ c ⟧ᶜ (starʳ •ʳ θ)

mutual
  cast-mono : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} (c : μ ⊢ A ∼ B) θ
    → MonoT (⟦ c ⟧ᶜ θ)
  cast-mono (id a) θ = ret-monoT
  cast-mono (c ↦ d) θ = funProxy-mono {a = ⟦ c ⟧ᶜ θ} (cast-mono d θ)
  cast-mono (∀ᶜ c) θ = allProxy-mono (λ σ → cast-mono c (sealʳ σ •ʳ θ))
  cast-mono (_! ⦃ Gᵍ ⦄ c) θ =
    seq-monoT (cast-mono c θ) (point-monoT (injR-mono Gᵍ θ))
  cast-mono (？_ ⦃ Gᵍ ⦄ c) θ = seq-monoT (projR-mono Gᵍ θ) (cast-mono c θ)
  cast-mono ((inst_ {A = A} c) B≢★) θ m =
    seq-monoT inst◆-mono (instBody-mono A c θ m) m
  cast-mono ((gen c) A≢★) θ = genT-mono (λ σ → cast-mono c (sealʳ σ •ʳ θ))
  cast-mono bot-elim θ =
    allProxy-mono (λ σ → point-monoT injᴾ-mono)
  cast-mono bot-intro θ = errT-mono

  instBody-mono : ∀ {Δ} {μ : Env∼ Δ} (A : Ty (suc Δ)) {B : Ty Δ}
    → (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B) → ∀ θ m → MonoT (instBodyT A c θ m)
  instBody-mono A c θ m =
    seq-monoT
      (conv↑-mono 〖 fzero , ＇ fsuc fzero ↑ renameᵗ (extᵗ fsuc) A 〗
        (sealʳ (suc m) •ʳ sealʳ m •ʳ θ))
      (seq-monoT (conv↑-mono 〖 fzero , ★ ↑ A 〗 (sealʳ m •ʳ θ))
        (cast-mono c (starʳ •ʳ θ)))

mutual
  cast-fin : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} (c : μ ⊢ A ∼ B) θ
    → FinT (⟦ c ⟧ᶜ θ)
  cast-fin (id a) θ = ret-finT
  cast-fin (c ↦ d) θ =
    funProxy-fin (cast-mono c θ) (cast-fin c θ)
      (cast-mono d θ) (cast-fin d θ)
  cast-fin (∀ᶜ c) θ =
    allProxy-fin (λ σ → cast-mono c (sealʳ σ •ʳ θ))
      (λ σ → cast-fin c (sealʳ σ •ʳ θ))
  cast-fin (_! ⦃ Gᵍ ⦄ c) θ =
    seq-finT (cast-mono c θ) (cast-fin c θ)
      (point-monoT (injR-mono Gᵍ θ)) (point-finT (injR-fin Gᵍ θ))
  cast-fin (？_ ⦃ Gᵍ ⦄ c) θ =
    seq-finT (projR-mono Gᵍ θ) (projR-fin Gᵍ θ)
      (cast-mono c θ) (cast-fin c θ)
  cast-fin ((inst_ {A = A} c) B≢★) θ m =
    seq-finT inst◆-mono inst◆-fin
      (instBody-mono A c θ m) (instBody-fin A c θ m) m
  cast-fin ((gen c) A≢★) θ = genT-fin (λ σ → cast-fin c (sealʳ σ •ʳ θ))
  cast-fin bot-elim θ =
    allProxy-fin (λ σ → point-monoT injᴾ-mono)
      (λ σ → point-finT (injᴾ-fin {G = gσ σ}))
  cast-fin bot-intro θ = errT-fin

  instBody-fin : ∀ {Δ} {μ : Env∼ Δ} (A : Ty (suc Δ)) {B : Ty Δ}
    → (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B) → ∀ θ m → FinT (instBodyT A c θ m)
  instBody-fin A c θ m =
    seq-finT
      (conv↑-mono 〖 fzero , ＇ fsuc fzero ↑ renameᵗ (extᵗ fsuc) A 〗
        (sealʳ (suc m) •ʳ sealʳ m •ʳ θ))
      (conv↑-fin 〖 fzero , ＇ fsuc fzero ↑ renameᵗ (extᵗ fsuc) A 〗
        (sealʳ (suc m) •ʳ sealʳ m •ʳ θ))
      (seq-monoT (conv↑-mono 〖 fzero , ★ ↑ A 〗 (sealʳ m •ʳ θ))
        (cast-mono c (starʳ •ʳ θ)))
      (seq-finT (conv↑-mono 〖 fzero , ★ ↑ A 〗 (sealʳ m •ʳ θ))
        (conv↑-fin 〖 fzero , ★ ↑ A 〗 (sealʳ m •ʳ θ))
        (cast-mono c (starʳ •ʳ θ)) (cast-fin c (starʳ •ʳ θ)))

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

⟦⟧-mono : ∀ {Δ} (M : Term Δ) {θ ρ ρ′ n} → ρ ⊆ₑ ρ′
  → ⟦ M ⟧ θ ρ n ⊆ᴿ ⟦ M ⟧ θ ρ′ n
⟦⟧-mono (` x) ρ⊆ = retᴿ-mono (ρ⊆ x)
⟦⟧-mono (ƛ M) ρ⊆ =
  retᴿ-mono (Λᶠ-mono (λ D m → ⟦⟧-mono M (ext-⊆ₑ ⊆-refl ρ⊆)))
⟦⟧-mono (L · M) ρ⊆ =
  ≫=-mono (⟦⟧-mono L ρ⊆)
    (λ n₁ F⊆ → ≫=-mono (⟦⟧-mono M ρ⊆) (λ n₂ E⊆ → ●-mono F⊆ E⊆))
⟦⟧-mono (Λ M) ρ⊆ = retᴿ-mono (Λᴾ-mono (λ σ → ⟦⟧-mono M ρ⊆))
⟦⟧-mono (M ⦂∀ B [ A ]) {θ = θ} ρ⊆ =
  ≫=-mono (⟦⟧-mono M ρ⊆) (λ n₁ F⊆ →
    ≫=-mono (◆-mono F⊆)
      (conv↑-mono 〖 fzero , ⇑ᵗ A ↑ B 〗 (sealʳ n₁ •ʳ θ)))
⟦⟧-mono ($ κ) ρ⊆ = ⊆ᴿ-refl
⟦⟧-mono (L ⊕[ op ] M) ρ⊆ =
  ≫=-mono (⟦⟧-mono L ρ⊆) (λ n₁ D⊆ →
    ≫=-mono (⟦⟧-mono M ρ⊆) (λ n₂ E⊆ → retᴿ-mono (δᴾ-mono D⊆ E⊆)))
⟦⟧-mono (M ⟨ c ⟩) {θ = θ} ρ⊆ = ≫=-mono (⟦⟧-mono M ρ⊆) (cast-mono c θ)
⟦⟧-mono (M ↑ c) {θ = θ} ρ⊆ = ≫=-mono (⟦⟧-mono M ρ⊆) (conv↑-mono c θ)
⟦⟧-mono (M ↓ c) {θ = θ} ρ⊆ = ≫=-mono (⟦⟧-mono M ρ⊆) (conv↓-mono c θ)
⟦⟧-mono blame ρ⊆ = ⊆ᴿ-refl

⟦⟧-monoₑ : ∀ {Δ} (M : Term Δ) θ n → Monoₑ (λ ρ → ⟦ M ⟧ θ ρ n)
⟦⟧-monoₑ M θ n ρ⊆ = ⟦⟧-mono M ρ⊆

-- a transformer applied to the variable 0
transₑ-fin : ∀ {T} → FinT T → ∀ m → Finₑ (λ ρ → T (ρ zero) m)
transₑ-fin fT m = Finitary→Finₑ (fT m)

⟦⟧-fin : ∀ {Δ} (M : Term Δ) θ n → Finₑ (λ ρ → ⟦ M ⟧ θ ρ n)
⟦⟧-fin (` x) θ n = ret-fin (var-fin x)
⟦⟧-fin (ƛ M) θ n =
  ret-fin (Λᶠ-fin (λ m → ⟦⟧-monoₑ M θ m) (λ m → ⟦⟧-fin M θ m))
⟦⟧-fin (L · M) θ n =
  bind-fin (⟦⟧-monoₑ L θ n) (⟦⟧-fin L θ n)
    (λ n₁ → bind-mono (shift-mono (⟦⟧-monoₑ M θ n₁))
              (λ n₂ → ●-monoₑ (var-mono (suc zero)) (var-mono zero)))
    (λ n₁ → bind-fin (shift-mono (⟦⟧-monoₑ M θ n₁))
              (shift-fin (⟦⟧-fin M θ n₁))
              (λ n₂ → ●-monoₑ (var-mono (suc zero)) (var-mono zero))
              (λ n₂ → ●-fin (var-mono (suc zero)) (var-mono zero)
                        (var-fin (suc zero)) var0-fin))
⟦⟧-fin (Λ M) θ n =
  ret-fin (Λᴾ-fin (λ σ → ⟦⟧-fin M (sealʳ σ •ʳ θ) (suc σ)))
⟦⟧-fin (M ⦂∀ B [ A ]) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (λ n₁ → all-mono {k = λ σ → σ}
              {t = λ σ → ⟦ 〖 fzero , ⇑ᵗ A ↑ B 〗 ⟧↑ (sealʳ σ •ʳ θ)}
              (λ σ → conv↑-mono 〖 fzero , ⇑ᵗ A ↑ B 〗 (sealʳ σ •ʳ θ)) n₁)
    (λ n₁ → all-fin {k = λ σ → σ}
              {t = λ σ → ⟦ 〖 fzero , ⇑ᵗ A ↑ B 〗 ⟧↑ (sealʳ σ •ʳ θ)}
              (λ σ → conv↑-mono 〖 fzero , ⇑ᵗ A ↑ B 〗 (sealʳ σ •ʳ θ))
              (λ σ → conv↑-fin 〖 fzero , ⇑ᵗ A ↑ B 〗 (sealʳ σ •ʳ θ)) n₁)
⟦⟧-fin ($ κ) θ n = const-fin
⟦⟧-fin (L ⊕[ op ] M) θ n =
  bind-fin (⟦⟧-monoₑ L θ n) (⟦⟧-fin L θ n)
    (λ n₁ → bind-mono (shift-mono (⟦⟧-monoₑ M θ n₁))
              (λ n₂ → ret-mono (λ ρ⊆ → δᴾ-mono (ρ⊆ (suc zero)) (ρ⊆ zero))))
    (λ n₁ → bind-fin (shift-mono (⟦⟧-monoₑ M θ n₁))
              (shift-fin (⟦⟧-fin M θ n₁))
              (λ n₂ → ret-mono (λ ρ⊆ → δᴾ-mono (ρ⊆ (suc zero)) (ρ⊆ zero)))
              (λ n₂ → ret-fin (δᴾ-fin (var-mono (suc zero)) (var-mono zero)
                        (var-fin (suc zero)) var0-fin)))
⟦⟧-fin (M ⟨ c ⟩) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (transₑ-mono (cast-mono c θ)) (transₑ-fin (cast-fin c θ))
⟦⟧-fin (M ↑ c) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (transₑ-mono (conv↑-mono c θ)) (transₑ-fin (conv↑-fin c θ))
⟦⟧-fin (M ↓ c) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (transₑ-mono (conv↓-mono c θ)) (transₑ-fin (conv↓-fin c θ))
⟦⟧-fin blame θ n = const-fin

------------------------------------------------------------------------
-- Finite lists drawn from a consistent set
------------------------------------------------------------------------

mem-~* : ∀ {E} → Consistent E → ∀ u V → u ∈ E → mem V ⊆ E → u ~* V
mem-~* cE u [] u∈ V⊆ = tt
mem-~* cE u (v ∷ V) u∈ V⊆ =
  cE u v u∈ (V⊆ v (here refl)) ,
  mem-~* cE u V u∈ (λ w w∈ → V⊆ w (there w∈))

mem-≈ : ∀ {E} → Consistent E → ∀ U V → mem U ⊆ E → mem V ⊆ E → U ≈ V
mem-≈ cE [] V U⊆ V⊆ = tt
mem-≈ cE (u ∷ U) V U⊆ V⊆ =
  mem-~* cE u V (U⊆ u (here refl)) V⊆ ,
  mem-≈ cE U V (λ w w∈ → U⊆ w (there w∈)) V⊆

------------------------------------------------------------------------
-- The β law of Λᶠ
------------------------------------------------------------------------

Λᶠ-β-gen : ∀ {Φ : ℕ → Env → ℛ} → (∀ m → Monoₑ (Φ m)) → (∀ m → Finₑ (Φ m))
  → ∀ ρ {E m} → Consistent E → Conv E
  → Φ m (E • ρ) ⊆ᴿ (Λᶠ (λ D m′ → Φ m′ (D • ρ)) ●[ m ] E)
Λᶠ-β-gen {Φ = Φ} mΦ fΦ ρ {E} {m} cE (e , e∈) r r∈ =
  U , (mΦ m incl r (proj₂ (proj₂ rr)) , (λ ()) , mem-≈ cE U U U⊆ U⊆) ,
  U⊆ , (λ ())
  where
  rr = fΦ m (E • ρ) r r∈
  φ = proj₁ rr
  U : List Val
  U = e ∷ φ zero
  U⊆ : mem U ⊆ E
  U⊆ v (here refl) = e∈
  U⊆ v (there v∈) = proj₁ (proj₂ rr) zero v v∈
  incl : ⟪ φ ⟫ ⊆ₑ (mem U • ρ)
  incl zero v v∈ = there v∈
  incl (suc x) = proj₁ (proj₂ rr) (suc x)

Λᶠ-β : ∀ {Δ} (N : Term Δ) θ ρ {E m} → Consistent E → Conv E
  → ⟦ N ⟧ θ (E • ρ) m ⊆ᴿ (Λᶠ (λ D m′ → ⟦ N ⟧ θ (D • ρ) m′) ●[ m ] E)
Λᶠ-β N θ ρ = Λᶠ-β-gen (λ m → ⟦⟧-monoₑ N θ m) (λ m → ⟦⟧-fin N θ m) ρ

-- the β law of a function proxy
funProxy-β : ∀ {a b} → MonoT a → FinT a → MonoT b → FinT b
  → ∀ D {E m} → Consistent E → Conv E
  → (a E m ≫= λ E₁ m₁ → (D ●[ m₁ ] E₁) ≫= b)
    ⊆ᴿ (Λᶠ (λ E′ m′ → a E′ m′ ≫= λ E₁ m₁ → (D ●[ m₁ ] E₁) ≫= b)
          ●[ m ] E)
funProxy-β ma fa mb fb D =
  Λᶠ-β-gen (wrap-mono ma mb) (wrap-fin ma fa mb fb) (D • ρ₀)
