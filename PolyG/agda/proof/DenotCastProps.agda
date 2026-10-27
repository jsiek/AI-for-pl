module proof.DenotCastProps where

-- File Charter:
--   * Facts about the cast denotation ⟦ d , p ⟧ᶜ (Denotation.agda) that
--     the cast lemmas (proof/DenotCast.agda) and the relational
--     properties (proof/DenotRelationProps.agda) need:
--       c-mono, c-fin     monotonicity and finite support in the input;
--       c-ctr             a cast does not change the counter;
--       c-nonempty        a cast of an empty set denotes nothing;
--       c-up-noerr        an up cast never errs;
--       c-cons            a cast of a consistent set is consistent;
--       c-Λ-β             a finitary monotone body is below application
--                         of its abstraction to a nonempty consistent set;
--       c-app⇒, c-inst∀   the function and ∀ casts as such abstractions.
--   * Also symmetry of consistency (~-sym, ≈-sym) and the consistency of
--     the model operators (bind, application, instantiation, tags).
--   * Finite support is the constructive device that replaces deciding
--     whether a set holds err: an element of Φ X needs only a finite list
--     of elements of X.
--   * Names of the set-operator facts carry the prefix c- so that they do
--     not clash with proof/DenotProps.agda.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)
open import Relation.Nullary using (¬_)

open import Types
open import Terms using (Dir; up; down; flip)
open import GraphModel
open import Denotation

------------------------------------------------------------------------
-- Finite support and monotonicity of set operators
------------------------------------------------------------------------

c-FinR : (𝒱 → ℛ) → Set₁
c-FinR Φ =
  ∀ X r → r ∈ᴿ Φ X → Σ[ L ∈ List Val ] (mem L ⊆ X × r ∈ᴿ Φ (mem L))

c-MonoR : (𝒱 → ℛ) → Set₁
c-MonoR Φ = ∀ {X Y} → X ⊆ Y → Φ X ⊆ᴿ Φ Y

c-FinV : (𝒱 → 𝒱) → Set₁
c-FinV Φ =
  ∀ X v → v ∈ Φ X → Σ[ L ∈ List Val ] (mem L ⊆ X × v ∈ Φ (mem L))

c-MonoV : (𝒱 → 𝒱) → Set₁
c-MonoV Φ = ∀ {X Y} → X ⊆ Y → Φ X ⊆ Φ Y

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

c-mem-++ˡ : ∀ {L L′} → mem L ⊆ mem (L ++ L′)
c-mem-++ˡ v v∈ = ∈-++⁺ˡ v∈

c-mem-++ʳ : ∀ {L L′} → mem L′ ⊆ mem (L ++ L′)
c-mem-++ʳ {L} v v∈ = ∈-++⁺ʳ L v∈

c-++-⊆ : ∀ {L L′ X} → mem L ⊆ X → mem L′ ⊆ X → mem (L ++ L′) ⊆ X
c-++-⊆ {L} L⊆ L′⊆ v v∈ with ∈-++⁻ L v∈
c-++-⊆ {L} L⊆ L′⊆ v v∈ | inj₁ v∈L = L⊆ v v∈L
c-++-⊆ {L} L⊆ L′⊆ v v∈ | inj₂ v∈L′ = L′⊆ v v∈L′

c-∷-⊆ : ∀ {v L X} → v ∈ X → mem L ⊆ X → mem (v ∷ L) ⊆ X
c-∷-⊆ v∈ L⊆ u (here refl) = v∈
c-∷-⊆ v∈ L⊆ u (there u∈) = L⊆ u u∈

c-[]-⊆ : ∀ {X} → mem [] ⊆ X
c-[]-⊆ v ()

c-there-⊆ : ∀ {v L} → mem L ⊆ mem (v ∷ L)
c-there-⊆ u u∈ = there u∈

------------------------------------------------------------------------
-- Results
------------------------------------------------------------------------

c-retᴿ⌊⌋-⊆ : ∀ {R m} → retᴿ (⌊ R ⌋ m) m ⊆ᴿ R
c-retᴿ⌊⌋-⊆ (ret v m′) (refl , v∈) = v∈
c-retᴿ⌊⌋-⊆ err ()

c-⊆⌊retᴿ⌋ : ∀ {D m} → D ⊆ ⌊ retᴿ D m ⌋ m
c-⊆⌊retᴿ⌋ v v∈ = refl , v∈

c-⌊retᴿ⌋-⊆ : ∀ {D m m′} → ⌊ retᴿ D m ⌋ m′ ⊆ D
c-⌊retᴿ⌋-⊆ v (eq , v∈) = v∈

c-retᴿ-mono : ∀ {D D′ m} → D ⊆ D′ → retᴿ D m ⊆ᴿ retᴿ D′ m
c-retᴿ-mono D⊆ (ret v m′) (eq , v∈) = eq , D⊆ v v∈
c-retᴿ-mono D⊆ err ()

c-⌊⌋-mono : ∀ {R R′ m} → R ⊆ᴿ R′ → ⌊ R ⌋ m ⊆ ⌊ R′ ⌋ m
c-⌊⌋-mono R⊆ v v∈ = R⊆ _ v∈

------------------------------------------------------------------------
-- Bind
------------------------------------------------------------------------

c-≫=-mono : ∀ {R R′ K K′}
  → R ⊆ᴿ R′
  → (∀ {X Y} m → X ⊆ Y → K X m ⊆ᴿ K′ Y m)
  → (R ≫= K) ⊆ᴿ (R′ ≫= K′)
c-≫=-mono R⊆ KK r (inj₁ (eq , e∈)) = inj₁ (eq , R⊆ err e∈)
c-≫=-mono R⊆ KK r (inj₂ (m , (v , v∈) , r∈)) =
  inj₂ (m , (v , R⊆ _ v∈) , KK m (c-⌊⌋-mono R⊆) r r∈)

c-≫=-group : ∀ {R K m} → Conv (⌊ R ⌋ m) → K (⌊ R ⌋ m) m ⊆ᴿ (R ≫= K)
c-≫=-group {m = m} c r r∈ = inj₂ (m , c , r∈)

c-≫=-err : ∀ {R K} → err ∈ᴿ R → err ∈ᴿ (R ≫= K)
c-≫=-err e∈ = inj₁ (refl , e∈)

c-≫=-monoR : ∀ {Φ K} → c-MonoR Φ → (∀ m → c-MonoR (λ X → K X m))
  → c-MonoR (λ X → Φ X ≫= K)
c-≫=-monoR monoΦ monoK X⊆ = c-≫=-mono (monoΦ X⊆) (λ m → monoK m)

-- the inputs of a finite list of elements of ⌊ Φ X ⌋ m
c-collect : ∀ {Φ X m} → c-FinR Φ → c-MonoR Φ
  → ∀ L₀ → mem L₀ ⊆ ⌊ Φ X ⌋ m
  → Σ[ L ∈ List Val ] (mem L ⊆ X × mem L₀ ⊆ ⌊ Φ (mem L) ⌋ m)
c-collect finΦ monoΦ [] h = [] , c-[]-⊆ , c-[]-⊆
c-collect {X = X} {m} finΦ monoΦ (x ∷ L₀) h
  with finΦ X (ret x m) (h x (here refl))
     | c-collect finΦ monoΦ L₀ (λ y y∈ → h y (there y∈))
c-collect {Φ} {X} {m} finΦ monoΦ (x ∷ L₀) h
  | Lx , Lx⊆ , x∈ | L , L⊆ , L₀⊆ =
  Lx ++ L , c-++-⊆ Lx⊆ L⊆ , sub
  where
  sub : mem (x ∷ L₀) ⊆ ⌊ Φ (mem (Lx ++ L)) ⌋ m
  sub y (here refl) = monoΦ (c-mem-++ˡ {Lx} {L}) (ret y m) x∈
  sub y (there y∈) = monoΦ (c-mem-++ʳ {Lx} {L}) (ret y m) (L₀⊆ y y∈)

c-≫=-fin : ∀ {Φ K} → c-FinR Φ → c-MonoR Φ
  → (∀ m → c-FinR (λ X → K X m)) → (∀ m → c-MonoR (λ X → K X m))
  → c-FinR (λ X → Φ X ≫= K)
c-≫=-fin finΦ monoΦ finK monoK X r (inj₁ (refl , e∈))
  with finΦ X err e∈
c-≫=-fin finΦ monoΦ finK monoK X r (inj₁ (refl , e∈))
  | L , L⊆ , e∈′ = L , L⊆ , inj₁ (refl , e∈′)
c-≫=-fin {Φ} {K} finΦ monoΦ finK monoK X r (inj₂ (m , (c , c∈) , r∈))
  with finK m (⌊ Φ X ⌋ m) r r∈
c-≫=-fin {Φ} {K} finΦ monoΦ finK monoK X r (inj₂ (m , (c , c∈) , r∈))
  | L₀ , L₀⊆ , r∈′
  with c-collect {Φ} {X} {m} finΦ monoΦ (c ∷ L₀) (c-∷-⊆ c∈ L₀⊆)
c-≫=-fin {Φ} {K} finΦ monoΦ finK monoK X r (inj₂ (m , (c , c∈) , r∈))
  | L₀ , L₀⊆ , r∈′ | L , L⊆ , sub =
  L , L⊆ ,
  inj₂ (m , (c , sub c (here refl)) ,
        monoK m (λ y y∈ → sub y (there y∈)) r r∈′)

-- bind of a fixed set into a continuation that depends on X
c-≫=-finK : ∀ {R : ℛ} {K : 𝒱 → 𝒱 → ℕ → ℛ}
  → (∀ E m → c-FinR (λ X → K X E m)) → c-FinR (λ X → R ≫= K X)
c-≫=-finK finK X r (inj₁ (refl , e∈)) = [] , c-[]-⊆ , inj₁ (refl , e∈)
c-≫=-finK {R} finK X r (inj₂ (m , c , r∈)) with finK (⌊ R ⌋ m) m X r r∈
c-≫=-finK {R} finK X r (inj₂ (m , c , r∈)) | L , L⊆ , r∈′ =
  L , L⊆ , inj₂ (m , c , r∈′)

c-≫=-monoK : ∀ {R : ℛ} {K : 𝒱 → 𝒱 → ℕ → ℛ}
  → (∀ E m → c-MonoR (λ X → K X E m)) → c-MonoR (λ X → R ≫= K X)
c-≫=-monoK monoK X⊆ r (inj₁ e) = inj₁ e
c-≫=-monoK {R} monoK X⊆ r (inj₂ (m , c , r∈)) =
  inj₂ (m , c , monoK (⌊ R ⌋ m) m X⊆ r r∈)

------------------------------------------------------------------------
-- Application and instantiation
------------------------------------------------------------------------

c-●ˡ-fin : ∀ {E m} → c-FinR (λ X → X ●[ m ] E)
c-●ˡ-fin {m = m} X r (U , e∈ , U⊆ , U≢) =
  (U ⟼ r at m) ∷ [] , c-∷-⊆ e∈ c-[]-⊆ , (U , here refl , U⊆ , U≢)

c-●ˡ-mono : ∀ {E m} → c-MonoR (λ X → X ●[ m ] E)
c-●ˡ-mono X⊆ r (U , e∈ , U⊆ , U≢) = U , X⊆ _ e∈ , U⊆ , U≢

c-●ʳ-fin : ∀ {D m} → c-FinR (λ X → D ●[ m ] X)
c-●ʳ-fin X r (U , e∈ , U⊆ , U≢) = U , U⊆ , (U , e∈ , (λ v v∈ → v∈) , U≢)

c-●ʳ-mono : ∀ {D m} → c-MonoR (λ X → D ●[ m ] X)
c-●ʳ-mono X⊆ r (U , e∈ , U⊆ , U≢) = U , e∈ , (λ v v∈ → X⊆ v (U⊆ v v∈)) , U≢

c-●-mono : ∀ {D D′ E E′ m} → D ⊆ D′ → E ⊆ E′
  → (D ●[ m ] E) ⊆ᴿ (D′ ●[ m ] E′)
c-●-mono D⊆ E⊆ r (U , e∈ , U⊆ , U≢) =
  U , D⊆ _ e∈ , (λ v v∈ → E⊆ v (U⊆ v v∈)) , U≢

c-◆-fin : ∀ {σ} → c-FinR (λ X → X ◆ σ)
c-◆-fin {σ} X r e∈ = (σ ⟼∀ r) ∷ [] , c-∷-⊆ e∈ c-[]-⊆ , here refl

c-◆-mono : ∀ {σ} → c-MonoR (λ X → X ◆ σ)
c-◆-mono X⊆ r e∈ = X⊆ _ e∈

------------------------------------------------------------------------
-- Tags
------------------------------------------------------------------------

c-injᴾ-mono : ∀ {G X Y} → X ⊆ Y → injᴾ G X ⊆ injᴾ G Y
c-injᴾ-mono X⊆ vtrue ()
c-injᴾ-mono X⊆ vfalse ()
c-injᴾ-mono X⊆ (sealᵛ σ v) ()
c-injᴾ-mono X⊆ (injᵛ H v) (eq , v∈) = eq , X⊆ v v∈
c-injᴾ-mono X⊆ (U ⟼ r at m) ()
c-injᴾ-mono X⊆ (σ ⟼∀ r) ()
c-injᴾ-mono X⊆ νλ ()
c-injᴾ-mono X⊆ ν∀ ()

c-inj-ret-fin : ∀ {G m} → c-FinR (λ X → retᴿ (injᴾ G X) m)
c-inj-ret-fin X (ret vtrue m′) (eq , ())
c-inj-ret-fin X (ret vfalse m′) (eq , ())
c-inj-ret-fin X (ret (sealᵛ σ v) m′) (eq , ())
c-inj-ret-fin X (ret (injᵛ H v) m′) (eq , h , v∈) =
  v ∷ [] , c-∷-⊆ v∈ c-[]-⊆ , (eq , h , here refl)
c-inj-ret-fin X (ret (U ⟼ r at k) m′) (eq , ())
c-inj-ret-fin X (ret (σ ⟼∀ r) m′) (eq , ())
c-inj-ret-fin X (ret νλ m′) (eq , ())
c-inj-ret-fin X (ret ν∀ m′) (eq , ())
c-inj-ret-fin X err ()

c-inj-ret-mono : ∀ {G m} → c-MonoR (λ X → retᴿ (injᴾ G X) m)
c-inj-ret-mono X⊆ = c-retᴿ-mono (c-injᴾ-mono X⊆)

-- the elements of retᴿ (injᴾ G X) k
c-inj-ret-inv : ∀ {G X k} r → r ∈ᴿ retᴿ (injᴾ G X) k
  → Σ[ v ∈ Val ] (r ≡ ret (injᵛ G v) k × v ∈ X)
c-inj-ret-inv (ret vtrue k′) (eq , ())
c-inj-ret-inv (ret vfalse k′) (eq , ())
c-inj-ret-inv (ret (sealᵛ σ v) k′) (eq , ())
c-inj-ret-inv (ret (injᵛ H v) k′) (refl , refl , v∈) = v , refl , v∈
c-inj-ret-inv (ret (U ⟼ r at m) k′) (eq , ())
c-inj-ret-inv (ret (σ ⟼∀ r) k′) (eq , ())
c-inj-ret-inv (ret νλ k′) (eq , ())
c-inj-ret-inv (ret ν∀ k′) (eq , ())
c-inj-ret-inv err ()

c-proj-fin : ∀ {G m} → c-FinR (λ X → proj G X m)
c-proj-fin {G} X (ret v m′) (eq , i∈) =
  injᵛ G v ∷ [] , c-∷-⊆ i∈ c-[]-⊆ , (eq , here refl)
c-proj-fin X err (H , v , i∈ , H≢) =
  injᵛ H v ∷ [] , c-∷-⊆ i∈ c-[]-⊆ , (H , v , here refl , H≢)

c-proj-mono : ∀ {G m} → c-MonoR (λ X → proj G X m)
c-proj-mono X⊆ (ret v m′) (eq , i∈) = eq , X⊆ _ i∈
c-proj-mono X⊆ err (H , v , i∈ , H≢) = H , v , X⊆ _ i∈ , H≢

------------------------------------------------------------------------
-- Guarded abstractions
------------------------------------------------------------------------

c-guard-ret-fin : ∀ {w Φ m} → c-FinV Φ → c-MonoV Φ
  → c-FinR (λ X → guard w X (retᴿ (Φ X) m))
c-guard-ret-fin {w} finΦ monoΦ X (ret v m′) (w∈ , eq , v∈)
  with finΦ X v v∈
c-guard-ret-fin {w} finΦ monoΦ X (ret v m′) (w∈ , eq , v∈)
  | L , L⊆ , v∈′ =
  w ∷ L , c-∷-⊆ w∈ L⊆ , (here refl , eq , monoΦ c-there-⊆ v v∈′)
c-guard-ret-fin finΦ monoΦ X err (w∈ , ())

c-guard-ret-mono : ∀ {w Φ m} → c-MonoV Φ
  → c-MonoR (λ X → guard w X (retᴿ (Φ X) m))
c-guard-ret-mono monoΦ X⊆ (ret v m′) (w∈ , eq , v∈) =
  X⊆ _ w∈ , eq , monoΦ X⊆ v v∈
c-guard-ret-mono monoΦ X⊆ err (w∈ , ())

c-Λ-fin : ∀ {F : 𝒱 → 𝒱 → ℕ → ℛ}
  → (∀ Y m → c-FinR (λ X → F X Y m)) → c-FinV (λ X → Λ (F X))
c-Λ-fin finF X vtrue ()
c-Λ-fin finF X vfalse ()
c-Λ-fin finF X (sealᵛ σ v) ()
c-Λ-fin finF X (injᵛ G v) ()
c-Λ-fin finF X (U ⟼ r at m) (r∈ , U≢ , U≈) with finF (mem U) m X r r∈
c-Λ-fin finF X (U ⟼ r at m) (r∈ , U≢ , U≈) | L , L⊆ , r∈′ =
  L , L⊆ , (r∈′ , U≢ , U≈)
c-Λ-fin finF X (σ ⟼∀ r) ()
c-Λ-fin finF X νλ tt = [] , c-[]-⊆ , tt
c-Λ-fin finF X ν∀ ()

c-Λ-mono : ∀ {F : 𝒱 → 𝒱 → ℕ → ℛ}
  → (∀ Y m → c-MonoR (λ X → F X Y m)) → c-MonoV (λ X → Λ (F X))
c-Λ-mono monoF X⊆ vtrue ()
c-Λ-mono monoF X⊆ vfalse ()
c-Λ-mono monoF X⊆ (sealᵛ σ v) ()
c-Λ-mono monoF X⊆ (injᵛ G v) ()
c-Λ-mono monoF X⊆ (U ⟼ r at m) (r∈ , U≢ , U≈) =
  monoF (mem U) m X⊆ r r∈ , U≢ , U≈
c-Λ-mono monoF X⊆ (σ ⟼∀ r) ()
c-Λ-mono monoF X⊆ νλ tt = tt
c-Λ-mono monoF X⊆ ν∀ ()

c-Λᴾ-fin : ∀ {F : 𝒱 → Seal → ℛ}
  → (∀ σ → c-FinR (λ X → F X σ)) → c-FinV (λ X → Λᴾ (F X))
c-Λᴾ-fin finF X vtrue ()
c-Λᴾ-fin finF X vfalse ()
c-Λᴾ-fin finF X (sealᵛ σ v) ()
c-Λᴾ-fin finF X (injᵛ G v) ()
c-Λᴾ-fin finF X (U ⟼ r at m) ()
c-Λᴾ-fin finF X (σ ⟼∀ r) r∈ = finF σ X r r∈
c-Λᴾ-fin finF X νλ ()
c-Λᴾ-fin finF X ν∀ tt = [] , c-[]-⊆ , tt

c-Λᴾ-mono : ∀ {F : 𝒱 → Seal → ℛ}
  → (∀ σ → c-MonoR (λ X → F X σ)) → c-MonoV (λ X → Λᴾ (F X))
c-Λᴾ-mono monoF X⊆ vtrue ()
c-Λᴾ-mono monoF X⊆ vfalse ()
c-Λᴾ-mono monoF X⊆ (sealᵛ σ v) ()
c-Λᴾ-mono monoF X⊆ (injᵛ G v) ()
c-Λᴾ-mono monoF X⊆ (U ⟼ r at m) ()
c-Λᴾ-mono monoF X⊆ (σ ⟼∀ r) r∈ = monoF σ X⊆ r r∈
c-Λᴾ-mono monoF X⊆ νλ ()
c-Λᴾ-mono monoF X⊆ ν∀ tt = tt

------------------------------------------------------------------------
-- Casts: monotonicity and finite support
------------------------------------------------------------------------

-- the body of a function cast, as a function of the function set X and
-- the argument set Y
c-⇒F : Dir → Prec → Prec → SEnv → 𝒱 → 𝒱 → ℕ → ℛ
c-⇒F d p q θ X Y m′ =
  ⟦ flip d , p ⟧ᶜ θ Y m′ ≫= λ E₁ m₁ → (X ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ

-- the body of a ∀ cast, as a function of the polymorphic set X
c-∀F : Dir → Prec → SEnv → 𝒱 → Seal → ℛ
c-∀F d p θ X σ = (X ◆ σ) ≫= ⟦ d , p ⟧ᶜ (σ •ᵗ θ)

c-ret-fin : ∀ {m} → c-FinR (λ X → retᴿ X m)
c-ret-fin X (ret v m′) (eq , v∈) =
  v ∷ [] , c-∷-⊆ v∈ c-[]-⊆ , (eq , here refl)
c-ret-fin X err ()

c-mono : ∀ d p θ m → c-MonoR (λ X → ⟦ d , p ⟧ᶜ θ X m)
c-mono d ★⊑ θ m = c-retᴿ-mono
c-mono d 𝔹⊑ θ m = c-retᴿ-mono
c-mono d (‵⊑ α) θ m = c-retᴿ-mono
c-mono d (p ⇒⊑ q) θ m =
  c-guard-ret-mono {w = νλ} {Φ = λ X → Λ (c-⇒F d p q θ X)}
    (c-Λ-mono {F = c-⇒F d p q θ} (λ Y m′ →
      c-≫=-monoK {R = ⟦ flip d , p ⟧ᶜ θ Y m′}
        {K = λ X E₁ m₁ → (X ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ}
        (λ E₁ m₁ → c-≫=-monoR {Φ = λ X → X ●[ m₁ ] E₁}
           {K = ⟦ d , q ⟧ᶜ θ} (c-●ˡ-mono {E₁} {m₁})
           (λ m₂ → c-mono d q θ m₂))))
c-mono d (∀⊑ p) θ m =
  c-guard-ret-mono {w = ν∀} {Φ = λ X → Λᴾ (c-∀F d p θ X)}
    (c-Λᴾ-mono {F = c-∀F d p θ} (λ σ →
      c-≫=-monoR {Φ = λ X → X ◆ σ} {K = ⟦ d , p ⟧ᶜ (σ •ᵗ θ)}
        (c-◆-mono {σ}) (λ m₂ → c-mono d p (σ •ᵗ θ) m₂)))
c-mono up (tag G p) θ m =
  c-≫=-monoR {Φ = λ X → ⟦ up , p ⟧ᶜ θ X m}
    {K = λ E₁ m₁ → retᴿ (injᴾ (⟦ G ⟧ᴳ θ) E₁) m₁}
    (c-mono up p θ m) (λ m₁ → c-inj-ret-mono)
c-mono down (tag G p) θ m =
  c-≫=-monoR {Φ = λ X → proj (⟦ G ⟧ᴳ θ) X m} {K = ⟦ down , p ⟧ᶜ θ}
    c-proj-mono (λ m₁ → c-mono down p θ m₁)

c-fin : ∀ d p θ m → c-FinR (λ X → ⟦ d , p ⟧ᶜ θ X m)
c-fin d ★⊑ θ m = c-ret-fin
c-fin d 𝔹⊑ θ m = c-ret-fin
c-fin d (‵⊑ α) θ m = c-ret-fin
c-fin d (p ⇒⊑ q) θ m =
  c-guard-ret-fin {w = νλ} {Φ = λ X → Λ (c-⇒F d p q θ X)}
    (c-Λ-fin {F = c-⇒F d p q θ} (λ Y m′ →
      c-≫=-finK {R = ⟦ flip d , p ⟧ᶜ θ Y m′}
        {K = λ X E₁ m₁ → (X ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ}
        (λ E₁ m₁ → c-≫=-fin {Φ = λ X → X ●[ m₁ ] E₁}
           {K = ⟦ d , q ⟧ᶜ θ} (c-●ˡ-fin {E₁} {m₁}) (c-●ˡ-mono {E₁} {m₁})
           (λ m₂ → c-fin d q θ m₂) (λ m₂ → c-mono d q θ m₂))))
    (c-Λ-mono {F = c-⇒F d p q θ} (λ Y m′ →
      c-≫=-monoK {R = ⟦ flip d , p ⟧ᶜ θ Y m′}
        {K = λ X E₁ m₁ → (X ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ}
        (λ E₁ m₁ → c-≫=-monoR {Φ = λ X → X ●[ m₁ ] E₁}
           {K = ⟦ d , q ⟧ᶜ θ} (c-●ˡ-mono {E₁} {m₁})
           (λ m₂ → c-mono d q θ m₂))))
c-fin d (∀⊑ p) θ m =
  c-guard-ret-fin {w = ν∀} {Φ = λ X → Λᴾ (c-∀F d p θ X)}
    (c-Λᴾ-fin {F = c-∀F d p θ} (λ σ →
      c-≫=-fin {Φ = λ X → X ◆ σ} {K = ⟦ d , p ⟧ᶜ (σ •ᵗ θ)}
        (c-◆-fin {σ}) (c-◆-mono {σ}) (λ m₂ → c-fin d p (σ •ᵗ θ) m₂)
        (λ m₂ → c-mono d p (σ •ᵗ θ) m₂)))
    (c-Λᴾ-mono {F = c-∀F d p θ} (λ σ →
      c-≫=-monoR {Φ = λ X → X ◆ σ} {K = ⟦ d , p ⟧ᶜ (σ •ᵗ θ)}
        (c-◆-mono {σ}) (λ m₂ → c-mono d p (σ •ᵗ θ) m₂)))
c-fin up (tag G p) θ m =
  c-≫=-fin {Φ = λ X → ⟦ up , p ⟧ᶜ θ X m}
    {K = λ E₁ m₁ → retᴿ (injᴾ (⟦ G ⟧ᴳ θ) E₁) m₁}
    (c-fin up p θ m) (c-mono up p θ m) (λ m₁ → c-inj-ret-fin)
    (λ m₁ → c-inj-ret-mono)
c-fin down (tag G p) θ m =
  c-≫=-fin {Φ = λ X → proj (⟦ G ⟧ᴳ θ) X m} {K = ⟦ down , p ⟧ᶜ θ}
    c-proj-fin c-proj-mono (λ m₁ → c-fin down p θ m₁)
    (λ m₁ → c-mono down p θ m₁)

------------------------------------------------------------------------
-- Counters, emptiness and errors
------------------------------------------------------------------------

c-ctr : ∀ d p θ {E m v m′} → ret v m′ ∈ᴿ ⟦ d , p ⟧ᶜ θ E m → m′ ≡ m
c-ctr d ★⊑ θ (eq , v∈) = eq
c-ctr d 𝔹⊑ θ (eq , v∈) = eq
c-ctr d (‵⊑ α) θ (eq , v∈) = eq
c-ctr d (p ⇒⊑ q) θ (w∈ , eq , v∈) = eq
c-ctr d (∀⊑ p) θ (w∈ , eq , v∈) = eq
c-ctr up (tag G p) θ (inj₁ (() , e∈))
c-ctr up (tag G p) θ (inj₂ (m₁ , (c , c∈) , eq , v∈)) =
  trans eq (c-ctr up p θ c∈)
c-ctr down (tag G p) θ (inj₁ (() , e∈))
c-ctr down (tag G p) θ (inj₂ (m₁ , (c , eq₁ , c∈) , r∈)) =
  trans (c-ctr down p θ r∈) eq₁

-- a cast of the empty set denotes nothing
c-nonempty : ∀ d p θ {E m} r → r ∈ᴿ ⟦ d , p ⟧ᶜ θ E m → Conv E
c-nonempty d ★⊑ θ (ret v k) (eq , v∈) = v , v∈
c-nonempty d ★⊑ θ err ()
c-nonempty d 𝔹⊑ θ (ret v k) (eq , v∈) = v , v∈
c-nonempty d 𝔹⊑ θ err ()
c-nonempty d (‵⊑ α) θ (ret v k) (eq , v∈) = v , v∈
c-nonempty d (‵⊑ α) θ err ()
c-nonempty d (p ⇒⊑ q) θ r (w∈ , r∈) = νλ , w∈
c-nonempty d (∀⊑ p) θ r (w∈ , r∈) = ν∀ , w∈
c-nonempty up (tag G p) θ r (inj₁ (eq , e∈)) = c-nonempty up p θ err e∈
c-nonempty up (tag G p) θ r (inj₂ (m₁ , (c , c∈) , r∈)) =
  c-nonempty up p θ (ret c m₁) c∈
c-nonempty down (tag G p) θ r (inj₁ (eq , H , v , i∈ , H≢)) =
  injᵛ H v , i∈
c-nonempty down (tag G p) θ r (inj₂ (m₁ , (c , eq , i∈) , r∈)) =
  injᵛ (⟦ G ⟧ᴳ θ) c , i∈

c-up-noerr : ∀ p θ {E m} → ¬ (err ∈ᴿ ⟦ up , p ⟧ᶜ θ E m)
c-up-noerr ★⊑ θ ()
c-up-noerr 𝔹⊑ θ ()
c-up-noerr (‵⊑ α) θ ()
c-up-noerr (p ⇒⊑ q) θ (w∈ , ())
c-up-noerr (∀⊑ p) θ (w∈ , ())
c-up-noerr (tag G p) θ (inj₁ (eq , e∈)) = c-up-noerr p θ e∈
c-up-noerr (tag G p) θ (inj₂ (m₁ , c , ()))

------------------------------------------------------------------------
-- Symmetry of consistency
------------------------------------------------------------------------

-- every element of U is consistent with v
c-col : ∀ U v V → U ≈ (v ∷ V) → All (λ u → u ~ v) U
c-col [] v V h = []
c-col (u ∷ U) v V ((uv , uV) , hU) = uv ∷ c-col U v V hU

c-rest : ∀ U v V → U ≈ (v ∷ V) → U ≈ V
c-rest [] v V h = tt
c-rest (u ∷ U) v V ((uv , uV) , hU) = uV , c-rest U v V hU

mutual
  ~-sym : ∀ u v → u ~ v → v ~ u
  ~-sym vtrue vtrue h = tt
  ~-sym vtrue vfalse ()
  ~-sym vtrue (sealᵛ σ′ u′) ()
  ~-sym vtrue (injᵛ H u′) ()
  ~-sym vtrue (U′ ⟼ r′ at m′) ()
  ~-sym vtrue (σ′ ⟼∀ r′) ()
  ~-sym vtrue νλ ()
  ~-sym vtrue ν∀ ()
  ~-sym vfalse vtrue ()
  ~-sym vfalse vfalse h = tt
  ~-sym vfalse (sealᵛ σ′ u′) ()
  ~-sym vfalse (injᵛ H u′) ()
  ~-sym vfalse (U′ ⟼ r′ at m′) ()
  ~-sym vfalse (σ′ ⟼∀ r′) ()
  ~-sym vfalse νλ ()
  ~-sym vfalse ν∀ ()
  ~-sym (sealᵛ σ u) vtrue ()
  ~-sym (sealᵛ σ u) vfalse ()
  ~-sym (sealᵛ σ u) (sealᵛ σ′ u′) (e , h) = sym e , ~-sym u u′ h
  ~-sym (sealᵛ σ u) (injᵛ H u′) ()
  ~-sym (sealᵛ σ u) (U′ ⟼ r′ at m′) ()
  ~-sym (sealᵛ σ u) (σ′ ⟼∀ r′) ()
  ~-sym (sealᵛ σ u) νλ ()
  ~-sym (sealᵛ σ u) ν∀ ()
  ~-sym (injᵛ G u) vtrue ()
  ~-sym (injᵛ G u) vfalse ()
  ~-sym (injᵛ G u) (sealᵛ σ′ u′) ()
  ~-sym (injᵛ G u) (injᵛ H u′) (e , h) = sym e , ~-sym u u′ h
  ~-sym (injᵛ G u) (U′ ⟼ r′ at m′) ()
  ~-sym (injᵛ G u) (σ′ ⟼∀ r′) ()
  ~-sym (injᵛ G u) νλ ()
  ~-sym (injᵛ G u) ν∀ ()
  ~-sym (U ⟼ r at m) vtrue ()
  ~-sym (U ⟼ r at m) vfalse ()
  ~-sym (U ⟼ r at m) (sealᵛ σ′ u′) ()
  ~-sym (U ⟼ r at m) (injᵛ H u′) ()
  ~-sym (U ⟼ r at m) (U′ ⟼ r′ at m′) h =
    λ e h′ → ~ᴿ-sym r r′ (h (sym e) (≈-sym U′ U h′))
  ~-sym (U ⟼ r at m) (σ′ ⟼∀ r′) ()
  ~-sym (U ⟼ r at m) νλ h = tt
  ~-sym (U ⟼ r at m) ν∀ ()
  ~-sym (σ ⟼∀ r) vtrue ()
  ~-sym (σ ⟼∀ r) vfalse ()
  ~-sym (σ ⟼∀ r) (sealᵛ σ′ u′) ()
  ~-sym (σ ⟼∀ r) (injᵛ H u′) ()
  ~-sym (σ ⟼∀ r) (U′ ⟼ r′ at m′) ()
  ~-sym (σ ⟼∀ r) (σ′ ⟼∀ r′) h = λ e → ~ᴿ-sym r r′ (h (sym e))
  ~-sym (σ ⟼∀ r) νλ ()
  ~-sym (σ ⟼∀ r) ν∀ h = tt
  ~-sym νλ vtrue ()
  ~-sym νλ vfalse ()
  ~-sym νλ (sealᵛ σ′ u′) ()
  ~-sym νλ (injᵛ H u′) ()
  ~-sym νλ (U′ ⟼ r′ at m′) h = tt
  ~-sym νλ (σ′ ⟼∀ r′) ()
  ~-sym νλ νλ h = tt
  ~-sym νλ ν∀ ()
  ~-sym ν∀ vtrue ()
  ~-sym ν∀ vfalse ()
  ~-sym ν∀ (sealᵛ σ′ u′) ()
  ~-sym ν∀ (injᵛ H u′) ()
  ~-sym ν∀ (U′ ⟼ r′ at m′) ()
  ~-sym ν∀ (σ′ ⟼∀ r′) h = tt
  ~-sym ν∀ νλ ()
  ~-sym ν∀ ν∀ h = tt

  ~ᴿ-sym : ∀ r r′ → r ~ᴿ r′ → r′ ~ᴿ r
  ~ᴿ-sym (ret v m) (ret v′ m′) (e , h) = sym e , ~-sym v v′ h
  ~ᴿ-sym (ret v m) err ()
  ~ᴿ-sym err (ret v′ m′) ()
  ~ᴿ-sym err err h = tt

  ≈-sym : ∀ U V → U ≈ V → V ≈ U
  ≈-sym U [] h = tt
  ≈-sym U (v ∷ V) h =
    ~*-sym U v (c-col U v V h) , ≈-sym U V (c-rest U v V h)

  ~*-sym : ∀ U v → All (λ u → u ~ v) U → v ~* U
  ~*-sym [] v [] = tt
  ~*-sym (u ∷ U) v (uv ∷ us) = ~-sym u v uv , ~*-sym U v us

-- reading and building ≈
~*→ : ∀ {u} V → u ~* V → ∀ v → v ⋵ V → u ~ v
~*→ (x ∷ V) (ux , uV) v (here refl) = ux
~*→ (x ∷ V) (ux , uV) v (there v∈) = ~*→ V uV v v∈

≈→ : ∀ U V → U ≈ V → ∀ u v → u ⋵ U → v ⋵ V → u ~ v
≈→ (x ∷ U) V (xV , UV) u v (here refl) v∈ = ~*→ V xV v v∈
≈→ (x ∷ U) V (xV , UV) u v (there u∈) v∈ = ≈→ U V UV u v u∈ v∈

~*← : ∀ {u} V → (∀ v → v ⋵ V → u ~ v) → u ~* V
~*← [] h = tt
~*← (x ∷ V) h = h x (here refl) , ~*← V (λ v v∈ → h v (there v∈))

≈← : ∀ U V → (∀ u v → u ⋵ U → v ⋵ V → u ~ v) → U ≈ V
≈← [] V h = tt
≈← (x ∷ U) V h =
  ~*← V (λ v v∈ → h x v (here refl) v∈) ,
  ≈← U V (λ u v u∈ v∈ → h u v (there u∈) v∈)

-- two lists drawn from a consistent set
c-≈-⊆ : ∀ {E} U V → Consistent E → mem U ⊆ E → mem V ⊆ E → U ≈ V
c-≈-⊆ U V CE U⊆ V⊆ =
  ≈← U V (λ u v u∈ v∈ → CE u v (U⊆ u u∈) (V⊆ v v∈))

-- the union of two mutually consistent lists
c-cons-++ : ∀ U V → U ≈ U → U ≈ V → V ≈ V → Consistent (mem (U ++ V))
c-cons-++ U V UU UV VV u v u∈ v∈ with ∈-++⁻ U u∈ | ∈-++⁻ U v∈
c-cons-++ U V UU UV VV u v u∈ v∈ | inj₁ uU | inj₁ vU = ≈→ U U UU u v uU vU
c-cons-++ U V UU UV VV u v u∈ v∈ | inj₁ uU | inj₂ vV = ≈→ U V UV u v uU vV
c-cons-++ U V UU UV VV u v u∈ v∈ | inj₂ uV | inj₁ vU =
  ≈→ V U (≈-sym U V UV) u v uV vU
c-cons-++ U V UU UV VV u v u∈ v∈ | inj₂ uV | inj₂ vV = ≈→ V V VV u v uV vV

------------------------------------------------------------------------
-- Consistency of the operators and of casts
------------------------------------------------------------------------

c-retᴿ-cons : ∀ {D m} → Consistent D → Consistentᴿ (retᴿ D m)
c-retᴿ-cons CD (ret v k) (ret v′ k′) (e , v∈) (e′ , v′∈) =
  trans e (sym e′) , CD v v′ v∈ v′∈
c-retᴿ-cons CD (ret v k) err r∈ ()
c-retᴿ-cons CD err s () s∈

c-⌊⌋-cons : ∀ {R m} → Consistentᴿ R → Consistent (⌊ R ⌋ m)
c-⌊⌋-cons {m = m} CR u v u∈ v∈ = proj₂ (CR (ret u m) (ret v m) u∈ v∈)

c-≫=-cons : ∀ {R} (K : 𝒱 → ℕ → ℛ) → Consistentᴿ R
  → (∀ D m → Consistent D → Consistentᴿ (K D m))
  → Consistentᴿ (R ≫= K)
c-≫=-cons K CR CK .err .err (inj₁ (refl , e∈)) (inj₁ (refl , e′∈)) = tt
c-≫=-cons K CR CK .err s (inj₁ (refl , e∈)) (inj₂ (m , (v , v∈) , s∈)) =
  ⊥-elim (CR err (ret v m) e∈ v∈)
c-≫=-cons K CR CK r .err (inj₂ (m , (v , v∈) , r∈)) (inj₁ (refl , e∈)) =
  ⊥-elim (CR (ret v m) err v∈ e∈)
c-≫=-cons {R} K CR CK r s (inj₂ (m , (v , v∈) , r∈))
    (inj₂ (m′ , (v′ , v′∈) , s∈))
  with CR (ret v m) (ret v′ m′) v∈ v′∈
c-≫=-cons {R} K CR CK r s (inj₂ (m , (v , v∈) , r∈))
    (inj₂ (m′ , (v′ , v′∈) , s∈))
  | refl , vv′ = CK (⌊ R ⌋ m) m (c-⌊⌋-cons CR) r s r∈ s∈

c-●-cons : ∀ {D E m} → Consistent D → Consistent E
  → Consistentᴿ (D ●[ m ] E)
c-●-cons {m = m} CD CE r s (U , e∈ , U⊆ , U≢) (V , f∈ , V⊆ , V≢) =
  CD (U ⟼ r at m) (V ⟼ s at m) e∈ f∈ refl (c-≈-⊆ U V CE U⊆ V⊆)

c-◆-cons : ∀ {D σ} → Consistent D → Consistentᴿ (D ◆ σ)
c-◆-cons {σ = σ} CD r s r∈ s∈ = CD (σ ⟼∀ r) (σ ⟼∀ s) r∈ s∈ refl

c-proj-cons : ∀ {G D m} → Consistent D → Consistentᴿ (proj G D m)
c-proj-cons CD (ret v k) (ret v′ k′) (e , i∈) (e′ , i′∈) =
  trans e (sym e′) , proj₂ (CD _ _ i∈ i′∈)
c-proj-cons CD (ret v k) err (e , i∈) (H , v′ , i′∈ , H≢) =
  ⊥-elim (H≢ (sym (proj₁ (CD _ _ i∈ i′∈))))
c-proj-cons CD err (ret v k) (H , v′ , i′∈ , H≢) (e , i∈) =
  ⊥-elim (H≢ (proj₁ (CD _ _ i′∈ i∈)))
c-proj-cons CD err err r∈ s∈ = tt

c-injᴾ-cons : ∀ {G D} → Consistent D → Consistent (injᴾ G D)
c-injᴾ-cons CD vtrue v ()
c-injᴾ-cons CD vfalse v ()
c-injᴾ-cons CD (sealᵛ σ u) v ()
c-injᴾ-cons CD (U ⟼ r at m) v ()
c-injᴾ-cons CD (σ ⟼∀ r) v ()
c-injᴾ-cons CD νλ v ()
c-injᴾ-cons CD ν∀ v ()
c-injᴾ-cons CD (injᵛ H u) vtrue u∈ ()
c-injᴾ-cons CD (injᵛ H u) vfalse u∈ ()
c-injᴾ-cons CD (injᵛ H u) (sealᵛ σ v) u∈ ()
c-injᴾ-cons CD (injᵛ H u) (U ⟼ r at m) u∈ ()
c-injᴾ-cons CD (injᵛ H u) (σ ⟼∀ r) u∈ ()
c-injᴾ-cons CD (injᵛ H u) νλ u∈ ()
c-injᴾ-cons CD (injᵛ H u) ν∀ u∈ ()
c-injᴾ-cons CD (injᵛ H u) (injᵛ H′ v) (e , u∈) (e′ , v∈) =
  trans e (sym e′) , CD u v u∈ v∈

c-guard-cons : ∀ {w D R} → Consistentᴿ R → Consistentᴿ (guard w D R)
c-guard-cons CR r s (w∈ , r∈) (w∈′ , s∈) = CR r s r∈ s∈

c-Λ-cons : ∀ {F : 𝒱 → ℕ → ℛ} → (∀ m → c-MonoR (λ X → F X m))
  → (∀ m Y → Consistent Y → Consistentᴿ (F Y m)) → Consistent (Λ F)
c-Λ-cons monoF CF vtrue v ()
c-Λ-cons monoF CF vfalse v ()
c-Λ-cons monoF CF (sealᵛ σ u) v ()
c-Λ-cons monoF CF (injᵛ G u) v ()
c-Λ-cons monoF CF (σ ⟼∀ r) v ()
c-Λ-cons monoF CF ν∀ v ()
c-Λ-cons monoF CF (U ⟼ r at m) vtrue u∈ ()
c-Λ-cons monoF CF (U ⟼ r at m) vfalse u∈ ()
c-Λ-cons monoF CF (U ⟼ r at m) (sealᵛ σ v) u∈ ()
c-Λ-cons monoF CF (U ⟼ r at m) (injᵛ G v) u∈ ()
c-Λ-cons monoF CF (U ⟼ r at m) (σ ⟼∀ s) u∈ ()
c-Λ-cons monoF CF (U ⟼ r at m) ν∀ u∈ ()
c-Λ-cons {F} monoF CF (U ⟼ r at m) (V ⟼ s at m′)
    (r∈ , U≢ , UU) (s∈ , V≢ , VV) = body
  where
  body : m ≡ m′ → U ≈ V → r ~ᴿ s
  body refl UV =
    CF m (mem (U ++ V)) (c-cons-++ U V UU UV VV) r s
      (monoF m (c-mem-++ˡ {U} {V}) r r∈)
      (monoF m (c-mem-++ʳ {U} {V}) s s∈)
c-Λ-cons monoF CF (U ⟼ r at m) νλ u∈ v∈ = tt
c-Λ-cons monoF CF νλ vtrue u∈ ()
c-Λ-cons monoF CF νλ vfalse u∈ ()
c-Λ-cons monoF CF νλ (sealᵛ σ v) u∈ ()
c-Λ-cons monoF CF νλ (injᵛ G v) u∈ ()
c-Λ-cons monoF CF νλ (σ ⟼∀ s) u∈ ()
c-Λ-cons monoF CF νλ ν∀ u∈ ()
c-Λ-cons monoF CF νλ (V ⟼ s at m′) u∈ v∈ = tt
c-Λ-cons monoF CF νλ νλ u∈ v∈ = tt

c-Λᴾ-cons : ∀ {F : Seal → ℛ} → (∀ σ → Consistentᴿ (F σ))
  → Consistent (Λᴾ F)
c-Λᴾ-cons CF vtrue v ()
c-Λᴾ-cons CF vfalse v ()
c-Λᴾ-cons CF (sealᵛ σ u) v ()
c-Λᴾ-cons CF (injᵛ G u) v ()
c-Λᴾ-cons CF (U ⟼ r at m) v ()
c-Λᴾ-cons CF νλ v ()
c-Λᴾ-cons CF (σ ⟼∀ r) vtrue u∈ ()
c-Λᴾ-cons CF (σ ⟼∀ r) vfalse u∈ ()
c-Λᴾ-cons CF (σ ⟼∀ r) (sealᵛ σ′ v) u∈ ()
c-Λᴾ-cons CF (σ ⟼∀ r) (injᵛ G v) u∈ ()
c-Λᴾ-cons CF (σ ⟼∀ r) (V ⟼ s at m) u∈ ()
c-Λᴾ-cons CF (σ ⟼∀ r) νλ u∈ ()
c-Λᴾ-cons CF (σ ⟼∀ r) (σ′ ⟼∀ s) r∈ s∈ = body
  where
  body : σ ≡ σ′ → r ~ᴿ s
  body refl = CF σ r s r∈ s∈
c-Λᴾ-cons CF (σ ⟼∀ r) ν∀ u∈ v∈ = tt
c-Λᴾ-cons CF ν∀ vtrue u∈ ()
c-Λᴾ-cons CF ν∀ vfalse u∈ ()
c-Λᴾ-cons CF ν∀ (sealᵛ σ′ v) u∈ ()
c-Λᴾ-cons CF ν∀ (injᵛ G v) u∈ ()
c-Λᴾ-cons CF ν∀ (V ⟼ s at m) u∈ ()
c-Λᴾ-cons CF ν∀ νλ u∈ ()
c-Λᴾ-cons CF ν∀ (σ′ ⟼∀ s) u∈ v∈ = tt
c-Λᴾ-cons CF ν∀ ν∀ u∈ v∈ = tt

c-⇒body-mono : ∀ d p q θ E m′ → c-MonoR (λ Y → c-⇒F d p q θ E Y m′)
c-⇒body-mono d p q θ E m′ =
  c-≫=-monoR {Φ = λ Y → ⟦ flip d , p ⟧ᶜ θ Y m′}
    {K = λ E₁ m₁ → (E ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ}
    (c-mono (flip d) p θ m′)
    (λ m₁ → c-≫=-monoR {Φ = λ Y → E ●[ m₁ ] Y} {K = ⟦ d , q ⟧ᶜ θ}
              (c-●ʳ-mono {E} {m₁}) (λ m₂ → c-mono d q θ m₂))

c-⇒body-fin : ∀ d p q θ E m′ → c-FinR (λ Y → c-⇒F d p q θ E Y m′)
c-⇒body-fin d p q θ E m′ =
  c-≫=-fin {Φ = λ Y → ⟦ flip d , p ⟧ᶜ θ Y m′}
    {K = λ E₁ m₁ → (E ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ}
    (c-fin (flip d) p θ m′) (c-mono (flip d) p θ m′)
    (λ m₁ → c-≫=-fin {Φ = λ Y → E ●[ m₁ ] Y} {K = ⟦ d , q ⟧ᶜ θ}
              (c-●ʳ-fin {E} {m₁}) (c-●ʳ-mono {E} {m₁})
              (λ m₂ → c-fin d q θ m₂) (λ m₂ → c-mono d q θ m₂))
    (λ m₁ → c-≫=-monoR {Φ = λ Y → E ●[ m₁ ] Y} {K = ⟦ d , q ⟧ᶜ θ}
              (c-●ʳ-mono {E} {m₁}) (λ m₂ → c-mono d q θ m₂))

c-cons : ∀ d p θ m {E} → Consistent E → Consistentᴿ (⟦ d , p ⟧ᶜ θ E m)
c-cons d ★⊑ θ m CE = c-retᴿ-cons CE
c-cons d 𝔹⊑ θ m CE = c-retᴿ-cons CE
c-cons d (‵⊑ α) θ m CE = c-retᴿ-cons CE
c-cons d (p ⇒⊑ q) θ m {E} CE =
  c-guard-cons {w = νλ} {D = E}
    (c-retᴿ-cons (c-Λ-cons {F = c-⇒F d p q θ E}
      (λ m′ → c-⇒body-mono d p q θ E m′)
      (λ m′ Y CY →
        c-≫=-cons (λ E₁ m₁ → (E ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ)
          (c-cons (flip d) p θ m′ CY)
          (λ E₁ m₁ CE₁ → c-≫=-cons (⟦ d , q ⟧ᶜ θ) (c-●-cons CE CE₁)
             (λ D k CD → c-cons d q θ k CD)))))
c-cons d (∀⊑ p) θ m {E} CE =
  c-guard-cons {w = ν∀} {D = E}
    (c-retᴿ-cons (c-Λᴾ-cons {F = c-∀F d p θ E} (λ σ →
      c-≫=-cons (⟦ d , p ⟧ᶜ (σ •ᵗ θ)) (c-◆-cons CE)
        (λ D k CD → c-cons d p (σ •ᵗ θ) k CD))))
c-cons up (tag G p) θ m CE =
  c-≫=-cons (λ E₁ m₁ → retᴿ (injᴾ (⟦ G ⟧ᴳ θ) E₁) m₁) (c-cons up p θ m CE)
    (λ E₁ m₁ CE₁ → c-retᴿ-cons (c-injᴾ-cons CE₁))
c-cons down (tag G p) θ m CE =
  c-≫=-cons (⟦ down , p ⟧ᶜ θ) (c-proj-cons CE)
    (λ D k CD → c-cons down p θ k CD)

-- the values of a cast of a consistent set
c-cons⌊⌋ : ∀ d p θ m m′ {E} → Consistent E
  → Consistent (⌊ ⟦ d , p ⟧ᶜ θ E m ⌋ m′)
c-cons⌊⌋ d p θ m m′ CE = c-⌊⌋-cons (c-cons d p θ m CE)

------------------------------------------------------------------------
-- Abstraction and application
------------------------------------------------------------------------

c-Λ-β : ∀ {F : 𝒱 → ℕ → ℛ} {E m}
  → c-FinR (λ X → F X m) → c-MonoR (λ X → F X m) → Conv E
  → Consistent E
  → F E m ⊆ᴿ (Λ F ●[ m ] E)
c-Λ-β {E = E} finF monoF (e₀ , e₀∈) CE r r∈ with finF E r r∈
c-Λ-β {E = E} finF monoF (e₀ , e₀∈) CE r r∈ | L , L⊆ , r∈′ =
  e₀ ∷ L ,
  (monoF c-there-⊆ r r∈′ , (λ ()) ,
   c-≈-⊆ (e₀ ∷ L) (e₀ ∷ L) CE (c-∷-⊆ e₀∈ L⊆) (c-∷-⊆ e₀∈ L⊆)) ,
  c-∷-⊆ e₀∈ L⊆ , λ ()

c-app⇒ : ∀ d p q θ {E m X m′} → νλ ∈ E → Conv X → Consistent X
  → c-⇒F d p q θ E X m′ ⊆ᴿ (⌊ ⟦ d , p ⇒⊑ q ⟧ᶜ θ E m ⌋ m ●[ m′ ] X)
c-app⇒ d p q θ {E} {m} {X} {m′} ν∈ cX CX r r∈
  with c-Λ-β {F = c-⇒F d p q θ E}
         (c-⇒body-fin d p q θ E m′) (c-⇒body-mono d p q θ E m′) cX CX r r∈
c-app⇒ d p q θ {E} {m} {X} {m′} ν∈ cX CX r r∈ | U , e∈ , U⊆ , U≢ =
  U , (ν∈ , refl , e∈) , U⊆ , U≢

c-inst∀ : ∀ d p θ {E m σ} → ν∀ ∈ E
  → c-∀F d p θ E σ ⊆ᴿ (⌊ ⟦ d , ∀⊑ p ⟧ᶜ θ E m ⌋ m ◆ σ)
c-inst∀ d p θ ν∈ r r∈ = ν∈ , refl , r∈
