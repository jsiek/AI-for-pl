module proof.DenotProps where

-- File Charter:
--   * Basic properties of the denotation (Denotation.agda):
--       - monotonicity of the model operators (GraphModel.agda), of casts
--         and stacks in their input, and of terms in the environment
--         (⟦⟧ᶜ-mono, ⟦⟧ˢ-mono, ⟦⟧-mono);
--       - laws of bind: unit (≫=-unit), a value on the left (≫=-retᴸ,
--         ≫=-retᴿ), and associativity when the left side ends at a
--         single counter (≫=-assoc, with ⟦⟧ᶜ-pure: casts do not change
--         the counter);
--       - finite support (continuity): of casts in their input
--         (⟦⟧ᶜ-fin) and of terms in their environment (⟦⟧-fin), stated
--         for functions of an environment (Finₑ) as in GTLC;
--       - consistency of finite lists drawn from a consistent set
--         (mem-≈);
--       - the β law of Λ in both directions: F E m ⊆ Λ F ●[ m ] E for
--         monotone finitary F and nonempty consistent E (Λ-β-gen, Λ-β,
--         Λ-βᶜ), and
--         Λ F ●[ m ] E ⊆ F E m for monotone F (Λ-β⁻).
--   * Consumed by proof/DenotSubst.agda, proof/DenotSoundness.agda and
--     the relational proofs.

open import Data.Empty using (⊥; ⊥-elim)
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

open import Types
open import Terms
open import GraphModel
open import Denotation

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

Λ-mono : ∀ {F F′} → (∀ D m → F D m ⊆ᴿ F′ D m) → Λ F ⊆ Λ F′
Λ-mono F⊆ (U ⟼ r at m) (r∈ , ne , c) = F⊆ (mem U) m r r∈ , ne , c
Λ-mono F⊆ νλ tt = tt

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

testᴾ-mono : ∀ {G D D′} → D ⊆ D′ → testᴾ G D ⊆ testᴾ G D′
testᴾ-mono D⊆ vtrue (v , v∈) = v , D⊆ _ v∈
testᴾ-mono D⊆ vfalse (H , v , v∈ , ne) = H , v , D⊆ _ v∈ , ne

proj-mono : ∀ {G D D′ m} → D ⊆ D′ → proj G D m ⊆ᴿ proj G D′ m
proj-mono D⊆ (ret v m′) (eq , v∈) = eq , D⊆ _ v∈
proj-mono D⊆ err (H , v , v∈ , ne) = H , v , D⊆ _ v∈ , ne

condᴿ-mono : ∀ {D D′ R R′ T T′} → D ⊆ D′ → R ⊆ᴿ R′ → T ⊆ᴿ T′
  → condᴿ D R T ⊆ᴿ condᴿ D′ R′ T′
condᴿ-mono D⊆ R⊆ T⊆ r (inj₁ (t∈ , r∈)) = inj₁ (D⊆ _ t∈ , R⊆ r r∈)
condᴿ-mono D⊆ R⊆ T⊆ r (inj₂ (f∈ , r∈)) = inj₂ (D⊆ _ f∈ , T⊆ r r∈)

------------------------------------------------------------------------
-- Monotonicity of casts, stacks and terms
------------------------------------------------------------------------

⟦⟧ᶜ-mono : ∀ d p θ {E E′ m} → E ⊆ E′ → ⟦ d , p ⟧ᶜ θ E m ⊆ᴿ ⟦ d , p ⟧ᶜ θ E′ m
⟦⟧ᶜ-mono d ★⊑ θ E⊆ = retᴿ-mono E⊆
⟦⟧ᶜ-mono d 𝔹⊑ θ E⊆ = retᴿ-mono E⊆
⟦⟧ᶜ-mono d (‵⊑ α) θ E⊆ = retᴿ-mono E⊆
⟦⟧ᶜ-mono d (p ⇒⊑ q) θ E⊆ =
  guard-mono E⊆ (retᴿ-mono (Λ-mono (λ D m′ →
    ≫=-mono (⊆ᴿ-refl {R = ⟦ flip d , p ⟧ᶜ θ D m′}) (λ m₁ D⊆ →
      ≫=-mono (●-mono E⊆ D⊆) (λ m₂ → ⟦⟧ᶜ-mono d q θ)))))
⟦⟧ᶜ-mono d (∀⊑ p) θ E⊆ =
  guard-mono E⊆ (retᴿ-mono (Λᴾ-mono (λ σ →
    ≫=-mono (◆-mono E⊆) (λ m₁ → ⟦⟧ᶜ-mono d p (σ •ᵗ θ)))))
⟦⟧ᶜ-mono up (tag G p) θ E⊆ =
  ≫=-mono (⟦⟧ᶜ-mono up p θ E⊆) (λ m₁ D⊆ → retᴿ-mono (injᴾ-mono D⊆))
⟦⟧ᶜ-mono down (tag G p) θ E⊆ =
  ≫=-mono (proj-mono E⊆) (λ m₁ → ⟦⟧ᶜ-mono down p θ)

⟦⟧ˢ-mono : ∀ cs θ {R R′} → R ⊆ᴿ R′ → ⟦ cs ⟧ˢ θ R ⊆ᴿ ⟦ cs ⟧ˢ θ R′
⟦⟧ˢ-mono [] θ R⊆ = R⊆
⟦⟧ˢ-mono ((d , p) ∷ cs) θ R⊆ =
  ≫=-mono (⟦⟧ˢ-mono cs θ R⊆) (λ m → ⟦⟧ᶜ-mono d p θ)

⟦⟧-mono : ∀ M {θ ρ ρ′ n} → ρ ⊆ₑ ρ′ → ⟦ M ⟧ θ ρ n ⊆ᴿ ⟦ M ⟧ θ ρ′ n
⟦⟧-mono (` x) ρ⊆ = retᴿ-mono (ρ⊆ x)
⟦⟧-mono ℧ ρ⊆ = ⊆ᴿ-refl
⟦⟧-mono true ρ⊆ = ⊆ᴿ-refl
⟦⟧-mono false ρ⊆ = ⊆ᴿ-refl
⟦⟧-mono (if L M N) ρ⊆ =
  ≫=-mono (⟦⟧-mono L ρ⊆)
    (λ m D⊆ → condᴿ-mono D⊆ (⟦⟧-mono M ρ⊆) (⟦⟧-mono N ρ⊆))
⟦⟧-mono (ƛ A M) ρ⊆ =
  retᴿ-mono (Λ-mono (λ D m → ⟦⟧-mono M (ext-⊆ₑ ⊆-refl ρ⊆)))
⟦⟧-mono (L · M) ρ⊆ =
  ≫=-mono (⟦⟧-mono L ρ⊆)
    (λ n₁ F⊆ → ≫=-mono (⟦⟧-mono M ρ⊆) (λ n₂ E⊆ → ●-mono F⊆ E⊆))
⟦⟧-mono (letv M N) ρ⊆ =
  ≫=-mono (⟦⟧-mono M ρ⊆) (λ m D⊆ → ⟦⟧-mono N (ext-⊆ₑ D⊆ ρ⊆))
⟦⟧-mono (seal α M) ρ⊆ =
  ≫=-mono (⟦⟧-mono M ρ⊆) (λ m D⊆ → retᴿ-mono (sealᴾ-mono D⊆))
⟦⟧-mono (unseal α M) ρ⊆ =
  ≫=-mono (⟦⟧-mono M ρ⊆) (λ m D⊆ → retᴿ-mono (unsealᴾ-mono D⊆))
⟦⟧-mono (is G M) ρ⊆ =
  ≫=-mono (⟦⟧-mono M ρ⊆) (λ m D⊆ → retᴿ-mono (testᴾ-mono D⊆))
⟦⟧-mono (inj G M) ρ⊆ =
  ≫=-mono (⟦⟧-mono M ρ⊆) (λ m D⊆ → retᴿ-mono (injᴾ-mono D⊆))
⟦⟧-mono (cast d p M) {θ = θ} ρ⊆ =
  ≫=-mono (⟦⟧-mono M ρ⊆) (λ m → ⟦⟧ᶜ-mono d p θ)
⟦⟧-mono (Λν cs M) {θ = θ} ρ⊆ =
  retᴿ-mono (Λᴾ-mono (λ σ → ⟦⟧ˢ-mono cs (σ •ᵗ θ) (⟦⟧-mono M ρ⊆)))
⟦⟧-mono (inst M B N) ρ⊆ =
  ≫=-mono (⟦⟧-mono M ρ⊆) (λ n₁ F⊆ →
    ≫=-mono (◆-mono F⊆) (λ n₂ E⊆ → ⟦⟧-mono N (ext-⊆ₑ E⊆ ρ⊆)))

------------------------------------------------------------------------
-- Laws of bind
------------------------------------------------------------------------

-- the results of R that return a value all end at counter n
Pure : ℛ → ℕ → Set
Pure R n = ∀ v m → ret v m ∈ᴿ R → m ≡ n

retᴿ-pure : ∀ {D n} → Pure (retᴿ D n) n
retᴿ-pure v m (eq , v∈) = eq

-- casts never change the counter
⟦⟧ᶜ-pure : ∀ d p θ {E m} → Pure (⟦ d , p ⟧ᶜ θ E m) m
⟦⟧ᶜ-pure d ★⊑ θ = retᴿ-pure
⟦⟧ᶜ-pure d 𝔹⊑ θ = retᴿ-pure
⟦⟧ᶜ-pure d (‵⊑ α) θ = retᴿ-pure
⟦⟧ᶜ-pure d (p ⇒⊑ q) θ v m′ (c , eq , w∈) = eq
⟦⟧ᶜ-pure d (∀⊑ p) θ v m′ (c , eq , w∈) = eq
⟦⟧ᶜ-pure up (tag G p) θ v m′ (inj₁ (() , e∈))
⟦⟧ᶜ-pure up (tag G p) θ v m′ (inj₂ (m₁ , (u , u∈) , eq , w∈)) =
  trans eq (⟦⟧ᶜ-pure up p θ u m₁ u∈)
⟦⟧ᶜ-pure down (tag G p) θ v m′ (inj₁ (() , e∈))
⟦⟧ᶜ-pure down (tag G p) θ v m′ (inj₂ (m₁ , (u , eq₁ , u∈) , r∈)) =
  trans (⟦⟧ᶜ-pure down p θ v m′ r∈) eq₁

≫=-unit : ∀ {R} → R ⊆ᴿ (R ≫= λ D m → retᴿ D m)
≫=-unit (ret v m) v∈ = inj₂ (m , (v , v∈) , refl , v∈)
≫=-unit err e∈ = inj₁ (refl , e∈)

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
Λ-β⁻ : ∀ {F E m} → (∀ {D D′} m → D ⊆ D′ → F D m ⊆ᴿ F D′ m)
  → (Λ F ●[ m ] E) ⊆ᴿ F E m
Λ-β⁻ Fm r (U , (r∈ , ne , c) , U⊆ , ne′) = Fm _ U⊆ r r∈

------------------------------------------------------------------------
-- Functions of an environment: monotonicity and finite support
------------------------------------------------------------------------

-- finite environments
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

-- constants and variables

const-mono : ∀ {A : Set} {X : A → Set} → Monoₑ (λ ρ → X)
const-mono ρ⊆ a a∈ = a∈

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

-- skipping the variable 1
skipₑ : Env → Env
skipₑ ρ = ρ zero • tailₑ (tailₑ ρ)

skip-mono : ∀ {A : Set} {Φ : Env → A → Set} → Monoₑ Φ
  → Monoₑ (λ ρ → Φ (skipₑ ρ))
skip-mono m ρ⊆ = m (ext-⊆ₑ (ρ⊆ zero) (λ x → ρ⊆ (suc (suc x))))

skip-fin : ∀ {A : Set} {Φ : Env → A → Set} → Monoₑ Φ → Finₑ Φ
  → Finₑ (λ ρ → Φ (skipₑ ρ))
skip-fin {Φ = Φ} m f ρ w w∈ = φ′ , ⊑ , m incl w (proj₂ (proj₂ r))
  where
  r = f (skipₑ ρ) w w∈
  φ = proj₁ r
  φ′ : FEnv
  φ′ zero = φ zero
  φ′ (suc zero) = []
  φ′ (suc (suc x)) = φ (suc x)
  ⊑ : φ′ ⊑ₑ ρ
  ⊑ zero = proj₁ (proj₂ r) zero
  ⊑ (suc zero) v ()
  ⊑ (suc (suc x)) = proj₁ (proj₂ r) (suc x)
  incl : ⟪ φ ⟫ ⊆ₑ skipₑ ⟪ φ′ ⟫
  incl zero = ⊆-refl
  incl (suc x) = ⊆-refl

-- values and binds

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

-- two finite environments joined

join₂ : ∀ {A B : Set} {Φ₁ : Env → A → Set} {Φ₂ : Env → B → Set} {ρ a b}
  → Monoₑ Φ₁ → Monoₑ Φ₂
  → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × Φ₁ ⟪ φ ⟫ a)
  → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × Φ₂ ⟪ φ ⟫ b)
  → Σ[ φ ∈ FEnv ] (φ ⊑ₑ ρ × Φ₁ ⟪ φ ⟫ a × Φ₂ ⟪ φ ⟫ b)
join₂ m₁ m₂ (φ₁ , φ₁⊑ , a∈) (φ₂ , φ₂⊑ , b∈) =
  join φ₁ φ₂ , join-⊑ φ₁⊑ φ₂⊑ ,
  m₁ (join-l {φ = φ₁} {ψ = φ₂}) _ a∈ , m₂ (join-r {φ = φ₁} {ψ = φ₂}) _ b∈

guard-fin : ∀ {v} {Ψ : Env → 𝒱} {Φ : Env → ℛ}
  → Monoₑ Ψ → Finₑ Ψ → Monoₑ Φ → Finₑ Φ
  → Finₑ (λ ρ → guard v (Ψ ρ) (Φ ρ))
guard-fin {v} mΨ fΨ mΦ fΦ ρ r (v∈ , r∈)
  with join₂ mΨ mΦ (fΨ ρ v v∈) (fΦ ρ r r∈)
guard-fin {v} mΨ fΨ mΦ fΦ ρ r (v∈ , r∈) | φ , φ⊑ , v∈′ , r∈′ =
  φ , φ⊑ , v∈′ , r∈′

-- abstractions

Λ-monoₑ : ∀ {Φ : ℕ → Env → ℛ} → (∀ m → Monoₑ (Φ m))
  → Monoₑ (λ ρ → Λ (λ D m → Φ m (D • ρ)))
Λ-monoₑ mΦ ρ⊆ = Λ-mono (λ D m → mΦ m (ext-⊆ₑ ⊆-refl ρ⊆))

Λ-fin : ∀ {Φ : ℕ → Env → ℛ} → (∀ m → Monoₑ (Φ m)) → (∀ m → Finₑ (Φ m))
  → Finₑ (λ ρ → Λ (λ D m → Φ m (D • ρ)))
Λ-fin mΦ fΦ ρ (U ⟼ r at m) (r∈ , ne , c) =
  φ′ , (λ x → proj₁ (proj₂ rr) (suc x)) ,
  mΦ m incl r (proj₂ (proj₂ rr)) , ne , c
  where
  rr = fΦ m (mem U • ρ) r r∈
  φ′ : FEnv
  φ′ x = proj₁ rr (suc x)
  incl : ⟪ proj₁ rr ⟫ ⊆ₑ (mem U • ⟪ φ′ ⟫)
  incl zero = proj₁ (proj₂ rr) zero
  incl (suc x) = ⊆-refl
Λ-fin mΦ fΦ ρ νλ tt = ∅ₑ , ∅ₑ-⊑ ρ , tt

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

◆-monoₑ : ∀ {Ψ : Env → 𝒱} {σ} → Monoₑ Ψ → Monoₑ (λ ρ → Ψ ρ ◆ σ)
◆-monoₑ mΨ ρ⊆ = ◆-mono (mΨ ρ⊆)

◆-fin : ∀ {Ψ : Env → 𝒱} {σ} → Finₑ Ψ → Finₑ (λ ρ → Ψ ρ ◆ σ)
◆-fin {σ = σ} fΨ ρ r r∈ = fΨ ρ (σ ⟼∀ r) r∈

-- seals, tags and conditionals

sealᴾ-fin : ∀ {Ψ : Env → 𝒱} {σ} → Finₑ Ψ → Finₑ (λ ρ → sealᴾ σ (Ψ ρ))
sealᴾ-fin fΨ ρ (sealᵛ σ′ v) (e , v∈) with fΨ ρ v v∈
sealᴾ-fin fΨ ρ (sealᵛ σ′ v) (e , v∈) | φ , φ⊑ , v∈′ = φ , φ⊑ , e , v∈′

unsealᴾ-fin : ∀ {Ψ : Env → 𝒱} {σ} → Finₑ Ψ
  → Finₑ (λ ρ → unsealᴾ σ (Ψ ρ))
unsealᴾ-fin {σ = σ} fΨ ρ v v∈ = fΨ ρ (sealᵛ σ v) v∈

injᴾ-fin : ∀ {Ψ : Env → 𝒱} {G} → Finₑ Ψ → Finₑ (λ ρ → injᴾ G (Ψ ρ))
injᴾ-fin fΨ ρ (injᵛ H v) (eq , v∈) with fΨ ρ v v∈
injᴾ-fin fΨ ρ (injᵛ H v) (eq , v∈) | φ , φ⊑ , v∈′ = φ , φ⊑ , eq , v∈′

testᴾ-fin : ∀ {Ψ : Env → 𝒱} {G} → Finₑ Ψ → Finₑ (λ ρ → testᴾ G (Ψ ρ))
testᴾ-fin {G = G} fΨ ρ vtrue (v , v∈) with fΨ ρ (injᵛ G v) v∈
testᴾ-fin {G = G} fΨ ρ vtrue (v , v∈) | φ , φ⊑ , v∈′ = φ , φ⊑ , v , v∈′
testᴾ-fin fΨ ρ vfalse (H , v , v∈ , ne) with fΨ ρ (injᵛ H v) v∈
testᴾ-fin fΨ ρ vfalse (H , v , v∈ , ne) | φ , φ⊑ , v∈′ =
  φ , φ⊑ , H , v , v∈′ , ne

proj-fin : ∀ {Ψ : Env → 𝒱} {G m} → Finₑ Ψ → Finₑ (λ ρ → proj G (Ψ ρ) m)
proj-fin {G = G} fΨ ρ (ret v m′) (eq , v∈) with fΨ ρ (injᵛ G v) v∈
proj-fin {G = G} fΨ ρ (ret v m′) (eq , v∈) | φ , φ⊑ , v∈′ =
  φ , φ⊑ , eq , v∈′
proj-fin fΨ ρ err (H , v , v∈ , ne) with fΨ ρ (injᵛ H v) v∈
proj-fin fΨ ρ err (H , v , v∈ , ne) | φ , φ⊑ , v∈′ =
  φ , φ⊑ , H , v , v∈′ , ne

cond-monoₑ : ∀ {Ψ : Env → 𝒱} {Φ₁ Φ₂ : Env → ℛ}
  → Monoₑ Ψ → Monoₑ Φ₁ → Monoₑ Φ₂
  → Monoₑ (λ ρ → condᴿ (Ψ ρ) (Φ₁ ρ) (Φ₂ ρ))
cond-monoₑ mΨ m₁ m₂ ρ⊆ = condᴿ-mono (mΨ ρ⊆) (m₁ ρ⊆) (m₂ ρ⊆)

cond-fin : ∀ {Ψ : Env → 𝒱} {Φ₁ Φ₂ : Env → ℛ}
  → Monoₑ Ψ → Finₑ Ψ → Monoₑ Φ₁ → Finₑ Φ₁ → Monoₑ Φ₂ → Finₑ Φ₂
  → Finₑ (λ ρ → condᴿ (Ψ ρ) (Φ₁ ρ) (Φ₂ ρ))
cond-fin mΨ fΨ m₁ f₁ m₂ f₂ ρ r (inj₁ (t∈ , r∈))
  with join₂ mΨ m₁ (fΨ ρ vtrue t∈) (f₁ ρ r r∈)
cond-fin mΨ fΨ m₁ f₁ m₂ f₂ ρ r (inj₁ (t∈ , r∈)) | φ , φ⊑ , t∈′ , r∈′ =
  φ , φ⊑ , inj₁ (t∈′ , r∈′)
cond-fin mΨ fΨ m₁ f₁ m₂ f₂ ρ r (inj₂ (f∈ , r∈))
  with join₂ mΨ m₂ (fΨ ρ vfalse f∈) (f₂ ρ r r∈)
cond-fin mΨ fΨ m₁ f₁ m₂ f₂ ρ r (inj₂ (f∈ , r∈)) | φ , φ⊑ , f∈′ , r∈′ =
  φ , φ⊑ , inj₂ (f∈′ , r∈′)

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

-- casts as functions of their input variable

castₑ-mono : ∀ d p θ m → Monoₑ (λ ρ → ⟦ d , p ⟧ᶜ θ (ρ zero) m)
castₑ-mono d p θ m ρ⊆ = ⟦⟧ᶜ-mono d p θ (ρ⊆ zero)

-- the body of a function cast, as a function of its argument (variable
-- 0) and the function (variable 1)
wrapᴱ : Dir → Prec → Prec → SEnv → ℕ → Env → ℛ
wrapᴱ d p q θ m ρ =
  ⟦ flip d , p ⟧ᶜ θ (ρ zero) m ≫= λ E₁ m₁ →
  (ρ (suc zero) ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ

wrap-mono : ∀ d p q θ m → Monoₑ (wrapᴱ d p q θ m)
wrap-mono d p q θ m =
  bind-mono {Ψ = λ ρ → ⟦ flip d , p ⟧ᶜ θ (ρ zero) m}
    {Θ = λ m₁ ρ → (ρ (suc (suc zero)) ●[ m₁ ] ρ zero) ≫= λ E₂ m₂ →
                  ⟦ d , q ⟧ᶜ θ ((E₂ • ρ) zero) m₂}
    (castₑ-mono (flip d) p θ m)
    (λ m₁ → bind-mono
      (●-monoₑ (var-mono (suc (suc zero))) (var-mono zero))
      (λ m₂ → castₑ-mono d q θ m₂))

wrap-fin : ∀ d p q θ m
  → (∀ m → Finitary (λ E → ⟦ flip d , p ⟧ᶜ θ E m))
  → (∀ m → Finitary (λ E → ⟦ d , q ⟧ᶜ θ E m))
  → Finₑ (wrapᴱ d p q θ m)
wrap-fin d p q θ m finp finq =
  bind-fin {Ψ = λ ρ → ⟦ flip d , p ⟧ᶜ θ (ρ zero) m}
    {Θ = λ m₁ ρ → (ρ (suc (suc zero)) ●[ m₁ ] ρ zero) ≫= λ E₂ m₂ →
                  ⟦ d , q ⟧ᶜ θ ((E₂ • ρ) zero) m₂}
    (castₑ-mono (flip d) p θ m) (Finitary→Finₑ (finp m))
    (λ m₁ → bind-mono
      (●-monoₑ (var-mono (suc (suc zero))) (var-mono zero))
      (λ m₂ → castₑ-mono d q θ m₂))
    (λ m₁ → bind-fin
      (●-monoₑ (var-mono (suc (suc zero))) (var-mono zero))
      (●-fin (var-mono (suc (suc zero))) (var-mono zero)
             (var-fin (suc (suc zero))) (var-fin zero))
      (λ m₂ → castₑ-mono d q θ m₂)
      (λ m₂ → Finitary→Finₑ (finq m₂)))

⟦⟧ᶜ-fin : ∀ d p θ m → Finitary (λ E → ⟦ d , p ⟧ᶜ θ E m)
⟦⟧ᶜ-fin d ★⊑ θ m E (ret v m′) (eq , v∈) =
  v ∷ [] , single⊆ v∈ , eq , here refl
⟦⟧ᶜ-fin d 𝔹⊑ θ m E (ret v m′) (eq , v∈) =
  v ∷ [] , single⊆ v∈ , eq , here refl
⟦⟧ᶜ-fin d (‵⊑ α) θ m E (ret v m′) (eq , v∈) =
  v ∷ [] , single⊆ v∈ , eq , here refl
⟦⟧ᶜ-fin d (p ⇒⊑ q) θ m E (ret νλ m′) (e∈ , eq , tt) =
  νλ ∷ [] , single⊆ e∈ , here refl , eq , tt
⟦⟧ᶜ-fin d (p ⇒⊑ q) θ m E (ret (U ⟼ r at m″) m′)
    (e∈ , eq , r∈ , ne , c) =
  L , L⊆ , here refl , eq ,
  wrap-mono d p q θ m″ incl r (proj₂ (proj₂ rr)) , ne , c
  where
  rr = wrap-fin d p q θ m″ (⟦⟧ᶜ-fin (flip d) p θ) (⟦⟧ᶜ-fin d q θ)
         (mem U • E • ρ₀) r r∈
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
⟦⟧ᶜ-fin d (∀⊑ p) θ m E (ret ν∀ m′) (e∈ , eq , tt) =
  ν∀ ∷ [] , single⊆ e∈ , here refl , eq , tt
⟦⟧ᶜ-fin d (∀⊑ p) θ m E (ret (σ ⟼∀ r) m′) (e∈ , eq , r∈) =
  L , L⊆ , here refl , eq , mW incl r (proj₂ (proj₂ rr))
  where
  θ′ = σ •ᵗ θ
  W : Env → ℛ
  W ρ = (ρ zero ◆ σ) ≫= λ D m₁ → ⟦ d , p ⟧ᶜ θ′ ((D • ρ) zero) m₁
  mW : Monoₑ W
  mW = bind-mono (◆-monoₑ (var-mono zero)) (λ m₁ → castₑ-mono d p θ′ m₁)
  rr = bind-fin (◆-monoₑ (var-mono zero)) (◆-fin var0-fin)
         (λ m₁ → castₑ-mono d p θ′ m₁)
         (λ m₁ → Finitary→Finₑ (⟦⟧ᶜ-fin d p θ′ m₁))
         (E • ρ₀) r r∈
  φ = proj₁ rr
  L : List Val
  L = ν∀ ∷ φ zero
  L⊆ : mem L ⊆ E
  L⊆ v (here refl) = e∈
  L⊆ v (there v∈) = proj₁ (proj₂ rr) zero v v∈
  incl : ⟪ φ ⟫ ⊆ₑ (mem L • ρ₀)
  incl zero v v∈ = there v∈
  incl (suc x) v v∈ = ⊥-elim (proj₁ (proj₂ rr) (suc x) v v∈)
⟦⟧ᶜ-fin up (tag G p) θ m =
  Finₑ→Finitary (λ E → ⟦ up , tag G p ⟧ᶜ θ E m)
    (bind-fin (castₑ-mono up p θ m) (Finitary→Finₑ (⟦⟧ᶜ-fin up p θ m))
      (λ m₁ → ret-mono (λ ρ⊆ → injᴾ-mono (ρ⊆ zero)))
      (λ m₁ → ret-fin (injᴾ-fin var0-fin)))
⟦⟧ᶜ-fin down (tag G p) θ m =
  Finₑ→Finitary (λ E → ⟦ down , tag G p ⟧ᶜ θ E m)
    (bind-fin (λ ρ⊆ → proj-mono (ρ⊆ zero)) (proj-fin var0-fin)
      (λ m₁ → castₑ-mono down p θ m₁)
      (λ m₁ → Finitary→Finₑ (⟦⟧ᶜ-fin down p θ m₁)))

-- stacks, as functions of the environment of their body

⟦⟧ˢ-monoₑ : ∀ cs θ {Φ : Env → ℛ} → Monoₑ Φ
  → Monoₑ (λ ρ → ⟦ cs ⟧ˢ θ (Φ ρ))
⟦⟧ˢ-monoₑ cs θ mΦ ρ⊆ = ⟦⟧ˢ-mono cs θ (mΦ ρ⊆)

⟦⟧ˢ-fin : ∀ cs θ {Φ : Env → ℛ} → Monoₑ Φ → Finₑ Φ
  → Finₑ (λ ρ → ⟦ cs ⟧ˢ θ (Φ ρ))
⟦⟧ˢ-fin [] θ mΦ fΦ = fΦ
⟦⟧ˢ-fin ((d , p) ∷ cs) θ mΦ fΦ =
  bind-fin (⟦⟧ˢ-monoₑ cs θ mΦ) (⟦⟧ˢ-fin cs θ mΦ fΦ)
    (λ m → castₑ-mono d p θ m) (λ m → Finitary→Finₑ (⟦⟧ᶜ-fin d p θ m))

------------------------------------------------------------------------
-- Finite support of terms
------------------------------------------------------------------------

⟦⟧-monoₑ : ∀ M θ n → Monoₑ (λ ρ → ⟦ M ⟧ θ ρ n)
⟦⟧-monoₑ M θ n ρ⊆ = ⟦⟧-mono M ρ⊆

⟦⟧-fin : ∀ M θ n → Finₑ (λ ρ → ⟦ M ⟧ θ ρ n)
⟦⟧-fin (` x) θ n = ret-fin (var-fin x)
⟦⟧-fin ℧ θ n = const-fin
⟦⟧-fin true θ n = const-fin
⟦⟧-fin false θ n = const-fin
⟦⟧-fin (if L M N) θ n =
  bind-fin (⟦⟧-monoₑ L θ n) (⟦⟧-fin L θ n)
    (λ m → cond-monoₑ (var-mono zero)
             (shift-mono (⟦⟧-monoₑ M θ m))
             (shift-mono (⟦⟧-monoₑ N θ m)))
    (λ m → cond-fin (var-mono zero) var0-fin
             (shift-mono (⟦⟧-monoₑ M θ m)) (shift-fin (⟦⟧-fin M θ m))
             (shift-mono (⟦⟧-monoₑ N θ m)) (shift-fin (⟦⟧-fin N θ m)))
⟦⟧-fin (ƛ A M) θ n =
  ret-fin (Λ-fin (λ m → ⟦⟧-monoₑ M θ m) (λ m → ⟦⟧-fin M θ m))
⟦⟧-fin (L · M) θ n =
  bind-fin (⟦⟧-monoₑ L θ n) (⟦⟧-fin L θ n)
    (λ n₁ → bind-mono (shift-mono (⟦⟧-monoₑ M θ n₁))
              (λ n₂ → ●-monoₑ (var-mono (suc zero)) (var-mono zero)))
    (λ n₁ → bind-fin (shift-mono (⟦⟧-monoₑ M θ n₁))
              (shift-fin (⟦⟧-fin M θ n₁))
              (λ n₂ → ●-monoₑ (var-mono (suc zero)) (var-mono zero))
              (λ n₂ → ●-fin (var-mono (suc zero)) (var-mono zero)
                        (var-fin (suc zero)) var0-fin))
⟦⟧-fin (letv M N) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (λ m → ⟦⟧-monoₑ N θ m) (λ m → ⟦⟧-fin N θ m)
⟦⟧-fin (seal α M) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (λ m → ret-mono (λ ρ⊆ → sealᴾ-mono (ρ⊆ zero)))
    (λ m → ret-fin (sealᴾ-fin var0-fin))
⟦⟧-fin (unseal α M) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (λ m → ret-mono (λ ρ⊆ → unsealᴾ-mono (ρ⊆ zero)))
    (λ m → ret-fin (unsealᴾ-fin var0-fin))
⟦⟧-fin (is G M) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (λ m → ret-mono (λ ρ⊆ → testᴾ-mono (ρ⊆ zero)))
    (λ m → ret-fin (testᴾ-fin var0-fin))
⟦⟧-fin (inj G M) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (λ m → ret-mono (λ ρ⊆ → injᴾ-mono (ρ⊆ zero)))
    (λ m → ret-fin (injᴾ-fin var0-fin))
⟦⟧-fin (cast d p M) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (λ m → castₑ-mono d p θ m)
    (λ m → Finitary→Finₑ (⟦⟧ᶜ-fin d p θ m))
⟦⟧-fin (Λν cs M) θ n =
  ret-fin (Λᴾ-fin (λ σ →
    ⟦⟧ˢ-fin cs (σ •ᵗ θ)
      (⟦⟧-monoₑ M (σ •ᵗ θ) (suc σ))
      (⟦⟧-fin M (σ •ᵗ θ) (suc σ))))
⟦⟧-fin (inst M B N) θ n =
  bind-fin (⟦⟧-monoₑ M θ n) (⟦⟧-fin M θ n)
    (λ n₁ → bind-mono (◆-monoₑ (var-mono zero))
              (λ n₂ → skip-mono (⟦⟧-monoₑ N (n₁ •ᵗ θ) n₂)))
    (λ n₁ → bind-fin (◆-monoₑ (var-mono zero)) (◆-fin var0-fin)
              (λ n₂ → skip-mono (⟦⟧-monoₑ N (n₁ •ᵗ θ) n₂))
              (λ n₂ → skip-fin (⟦⟧-monoₑ N (n₁ •ᵗ θ) n₂)
                               (⟦⟧-fin N (n₁ •ᵗ θ) n₂)))

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
-- The β law of Λ
------------------------------------------------------------------------

Λ-β-gen : ∀ {Φ : ℕ → Env → ℛ} → (∀ m → Monoₑ (Φ m)) → (∀ m → Finₑ (Φ m))
  → ∀ ρ {E m} → Consistent E → Conv E
  → Φ m (E • ρ) ⊆ᴿ (Λ (λ D m′ → Φ m′ (D • ρ)) ●[ m ] E)
Λ-β-gen {Φ = Φ} mΦ fΦ ρ {E} {m} cE (e , e∈) r r∈ =
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

Λ-β : ∀ N θ ρ {E m} → Consistent E → Conv E
  → ⟦ N ⟧ θ (E • ρ) m ⊆ᴿ (Λ (λ D m′ → ⟦ N ⟧ θ (D • ρ) m′) ●[ m ] E)
Λ-β N θ ρ = Λ-β-gen (λ m → ⟦⟧-monoₑ N θ m) (λ m → ⟦⟧-fin N θ m) ρ

Λ-βᶜ : ∀ d p q θ D {E m} → Consistent E → Conv E
  → (⟦ flip d , p ⟧ᶜ θ E m ≫= λ E₁ m₁ → (D ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ)
    ⊆ᴿ (Λ (λ E′ m′ → ⟦ flip d , p ⟧ᶜ θ E′ m′ ≫= λ E₁ m₁ →
                     (D ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ) ●[ m ] E)
Λ-βᶜ d p q θ D =
  Λ-β-gen (wrap-mono d p q θ)
    (λ m → wrap-fin d p q θ m (⟦⟧ᶜ-fin (flip d) p θ) (⟦⟧ᶜ-fin d q θ))
    (D • ρ₀)
