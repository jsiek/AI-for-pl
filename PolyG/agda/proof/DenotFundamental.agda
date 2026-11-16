module proof.DenotFundamental where

-- File Charter:
--   * The fundamental lemma of the denotational proof of graduality
--     (PolyG/notes/denotational-graduality.md, Section 8): term
--     precision Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p (TermPrecision.agda) implies, under
--     related environments and a world W of length n,
--       fundamental▹: every finite list of left results of ⟦ M ⟧ is
--                     related (▹ᶜ) to ⟦ M′ ⟧;
--       fundamental◃: ⟦ M ⟧ is related (◃ᶜ) to every finite list of right
--                     results of ⟦ M′ ⟧.
--   * The invariants: TOK (the world's entry for the seal of a known type
--     variable is the closed form of its derivation), Env▹ and Env◃ (the
--     variables' value sets are related, list by list), and consistency
--     of the set side's environment.
--   * By induction on term precision, with the bind and application
--     compatibility lemmas and the uniformity facts of
--     proof/DenotRelationProps.agda and the cast lemmas of
--     proof/DenotCast.agda.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Binary.Sublist.Propositional
  using ([]; _∷_; _∷ʳ_) renaming (_⊆_ to _⊑ˢ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans; <-≤-trans)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Function.Bundles using (Equivalence)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong) renaming (subst to substEq)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Terms
  using (Term; Dir; up; down; flip; `_; ℧; true; false; if; ƛ; _·_; letv;
         seal; unseal; is; inj; cast; Λν; inst)
open import TermPrecision
open import GraphModel
open import Denotation
open import proof.TermSubst using (substᵖ-fuse)
open import proof.DenotProps
  using (_⊆ₑ_; ⊆ₑ-refl; ext-⊆ₑ; ⟦⟧-mono; ⟦⟧-fin; ⟪_⟫; Λ-β)
open import proof.DenotConsistency
  using (⟦⟧-consistent; ext-consistent; ◆-consistent; ⌊⌋-consistent)
open import proof.DenotRelation
open import proof.DenotCastProps
open import proof.DenotRelationProps
open import proof.DenotCast

open Equivalence using (to; from)

------------------------------------------------------------------------
-- Invariants
------------------------------------------------------------------------

-- the world's entry for the seal of a known type variable
TOK : PEnv → SEnv → World → Set
TOK Δ⊑ θ W = ∀ {X q} → Δ⊑ ∋ X ≅ᵖ q → W ∋ʷ θ X ⦂ ⟦ q ⟧ᵖ θ

-- related environments, for reflection and for preservation
Env▹ : PCtx → SEnv → World → Env → Env → Set₁
Env▹ Γ⊑ θ W ρ ρ′ =
  ∀ {x p} → Γ⊑ ∋ x ⦂ᵖ p → ∀ L → mem L ⊆ ρ x → W ∣ θ ⊢ p ⊢ L ▹ ρ′ x

Env◃ : PCtx → SEnv → World → Env → Env → Set₁
Env◃ Γ⊑ θ W ρ ρ′ =
  ∀ {x p} → Γ⊑ ∋ x ⦂ᵖ p → ∀ L′ → mem L′ ⊆ ρ′ x → W ∣ θ ⊢ p ⊢ ρ x ◃ L′

------------------------------------------------------------------------
-- Worlds and type variables
------------------------------------------------------------------------

length-++1 : ∀ (W : World) q → length (W ++ (q ∷ [])) ≡ suc (length W)
length-++1 [] q = refl
length-++1 (q′ ∷ W) q = cong suc (length-++1 W q)

∋ʷ-last : ∀ (W : World) q → (W ++ (q ∷ [])) ∋ʷ length W ⦂ q
∋ʷ-last [] q = Zʷ
∋ʷ-last (q′ ∷ W) q = Sʷ (∋ʷ-last W q)

∋ʷ-unique : ∀ {W σ q q′} → W ∋ʷ σ ⦂ q → W ∋ʷ σ ⦂ q′ → q ≡ q′
∋ʷ-unique Zʷ Zʷ = refl
∋ʷ-unique (Sʷ w) (Sʷ w′) = ∋ʷ-unique w w′

⟦⇑ᵖ⟧ : ∀ θ σ q → ⟦ ⇑ᵖ q ⟧ᵖ (σ •ᵗ θ) ≡ ⟦ q ⟧ᵖ θ
⟦⇑ᵖ⟧ θ σ q = substᵖ-fuse (λ i → refl) q

TOK-kripke : ∀ {Δ⊑ θ W W′} → W ⊑ʷ W′ → TOK Δ⊑ θ W → TOK Δ⊑ θ W′
TOK-kripke ext tok X∈ = ∋ʷ-ext ext (tok X∈)

-- under an abstract type variable
TOK-abs : ∀ {Δ⊑ θ W σ} → TOK Δ⊑ θ W → TOK (absᵖ ∷ Δ⊑) (σ •ᵗ θ) W
TOK-abs {θ = θ} {σ = σ} tok (S≅ᵖ {q = q} X∈) =
  substEq (λ q′ → _ ∋ʷ θ _ ⦂ q′) (sym (⟦⇑ᵖ⟧ θ σ q)) (tok X∈)

-- under a known type variable, whose seal is the world's last entry
TOK-known : ∀ {Δ⊑ θ W q W′}
  → TOK Δ⊑ θ W → (W ++ (⟦ q ⟧ᵖ θ ∷ [])) ⊑ʷ W′
  → TOK (knownᵖ q ∷ Δ⊑) (length W •ᵗ θ) W′
TOK-known {θ = θ} {W} {q} tok ext Z≅ᵖ =
  ∋ʷ-ext ext
    (substEq (λ q′ → (W ++ (⟦ q ⟧ᵖ θ ∷ [])) ∋ʷ length W ⦂ q′)
       (sym (⟦⇑ᵖ⟧ θ (length W) q)) (∋ʷ-last W (⟦ q ⟧ᵖ θ)))
TOK-known {θ = θ} {W} {q} tok ext (S≅ᵖ {q = q₀} X∈) =
  ∋ʷ-ext (⊑ʷ-trans (_ , refl) ext)
    (substEq (λ q′ → W ∋ʷ θ _ ⦂ q′) (sym (⟦⇑ᵖ⟧ θ (length W) q₀)) (tok X∈))

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

∋-⤊⁻ : ∀ {Γ⊑ x p} → ⤊ᵖ Γ⊑ ∋ x ⦂ᵖ p
  → Σ[ p₀ ∈ Prec ] (Γ⊑ ∋ x ⦂ᵖ p₀ × p ≡ ⇑ᵖ p₀)
∋-⤊⁻ {p₀ ∷ Γ⊑} Zᵖ = p₀ , Zᵖ , refl
∋-⤊⁻ {p₀ ∷ Γ⊑} (Sᵖ x∈) with ∋-⤊⁻ {Γ⊑} x∈
∋-⤊⁻ {p₀ ∷ Γ⊑} (Sᵖ x∈) | p₁ , x∈′ , eq = p₁ , Sᵖ x∈′ , eq

Env▹-kripke : ∀ {Γ⊑ θ W W′ ρ ρ′} → W ⊑ʷ W′
  → Env▹ Γ⊑ θ W ρ ρ′ → Env▹ Γ⊑ θ W′ ρ ρ′
Env▹-kripke {θ = θ} {W} {W′} {ρ} {ρ′} ext env {x} {p} x∈ L L⊆ =
  ▹-kripke (suc (sizeᴸ L)) {W} {W′} {θ} {p} {L} {ρ′ x} ext (env x∈ L L⊆)

Env◃-kripke : ∀ {Γ⊑ θ W W′ ρ ρ′} → W ⊑ʷ W′
  → Env◃ Γ⊑ θ W ρ ρ′ → Env◃ Γ⊑ θ W′ ρ ρ′
Env◃-kripke {θ = θ} {W} {W′} {ρ} {ρ′} ext env {x} {p} x∈ L′ L⊆ =
  ◃-kripke (suc (sizeᴸ L′)) {W} {W′} {θ} {p} {ρ x} {L′} ext
    (env x∈ L′ L⊆)

Env▹-ext : ∀ {Γ⊑ θ W ρ ρ′ p D D′}
  → (∀ L → mem L ⊆ D → W ∣ θ ⊢ p ⊢ L ▹ D′)
  → Env▹ Γ⊑ θ W ρ ρ′ → Env▹ (p ∷ Γ⊑) θ W (D • ρ) (D′ • ρ′)
Env▹-ext h env Zᵖ = h
Env▹-ext h env (Sᵖ x∈) = env x∈

Env◃-ext : ∀ {Γ⊑ θ W ρ ρ′ p D D′}
  → (∀ L′ → mem L′ ⊆ D′ → W ∣ θ ⊢ p ⊢ D ◃ L′)
  → Env◃ Γ⊑ θ W ρ ρ′ → Env◃ (p ∷ Γ⊑) θ W (D • ρ) (D′ • ρ′)
Env◃-ext h env Zᵖ = h
Env◃-ext h env (Sᵖ x∈) = env x∈

-- under a type binder: the derivations are shifted
Env▹-⤊ : ∀ {Γ⊑ θ W ρ ρ′ σ}
  → Env▹ Γ⊑ θ W ρ ρ′ → Env▹ (⤊ᵖ Γ⊑) (σ •ᵗ θ) W ρ ρ′
Env▹-⤊ {Γ⊑} {θ} {W} {ρ} {ρ′} {σ} env {x} x∈ L L⊆ with ∋-⤊⁻ {Γ⊑} x∈
Env▹-⤊ {Γ⊑} {θ} {W} {ρ} {ρ′} {σ} env {x} x∈ L L⊆ | p₀ , x∈′ , refl =
  from (▹-subst (suc (sizeᴸ L)) {θ} {σ •ᵗ θ} {↑ₙ} {W} {p₀} {L} {ρ′ x}
          (λ i → refl))
    (env x∈′ L L⊆)

Env◃-⤊ : ∀ {Γ⊑ θ W ρ ρ′ σ}
  → Env◃ Γ⊑ θ W ρ ρ′ → Env◃ (⤊ᵖ Γ⊑) (σ •ᵗ θ) W ρ ρ′
Env◃-⤊ {Γ⊑} {θ} {W} {ρ} {ρ′} {σ} env {x} x∈ L′ L⊆ with ∋-⤊⁻ {Γ⊑} x∈
Env◃-⤊ {Γ⊑} {θ} {W} {ρ} {ρ′} {σ} env {x} x∈ L′ L⊆ | p₀ , x∈′ , refl =
  from (◃-subst (suc (sizeᴸ L′)) {θ} {σ •ᵗ θ} {↑ₙ} {W} {p₀} {ρ x} {L′}
          (λ i → refl))
    (env x∈′ L′ L⊆)

------------------------------------------------------------------------
-- Results
------------------------------------------------------------------------

-- results all of whose values end at counter k, related at world W of
-- length k
val▹ᶜ : ∀ {W θ p Rs D′ k} → length W ≡ k
  → (∀ v m → ret v m ⋵ Rs → m ≡ k)
  → (∀ m → W ∣ θ ⊢ p ⊢ valuesAt m Rs ▹ D′)
  → W ∣ θ ⊢ p ⊢ Rs ▹ᶜ retᴿ D′ k
val▹ᶜ {W} {θ} {p} {Rs} {D′} {k} len ctr h m ne
  with ctr _ m (values-∈⁻ Rs (proj₂ (ne-head (valuesAt m Rs) ne)))
val▹ᶜ {W} {θ} {p} {Rs} {D′} {k} len ctr h m ne | refl =
  W , lift ⊑ʷ-refl , lift len ,
  ▹-fuel (suc (sizeᴸ (valuesAt k Rs))) (suc (sizeᴿᴸ Rs))
    {W} {θ} {p} {valuesAt k Rs} {⌊ retᴿ D′ k ⌋ k}
    ≤-refl (s≤s (values-≤ k Rs))
    (▹-mono (suc (sizeᴸ (valuesAt k Rs))) {W} {θ} {p} {valuesAt k Rs}
       {D′} {⌊ retᴿ D′ k ⌋ k} c-⊆⌊retᴿ⌋ (h k))

val◃ᶜ : ∀ {W θ p D Rs′ k} → length W ≡ k
  → (err ⋵ Rs′ → ⊥)
  → (∀ v m → ret v m ⋵ Rs′ → m ≡ k)
  → (∀ m → W ∣ θ ⊢ p ⊢ D ◃ valuesAt m Rs′)
  → W ∣ θ ⊢ p ⊢ retᴿ D k ◃ᶜ Rs′
val◃ᶜ {W} {θ} {p} {D} {Rs′} {k} len noerr ctr h =
  inj₂ (lift (λ he → noerr (HasErr→∈ he)) , h′)
  where
  h′ : ∀ m → valuesAt m Rs′ ≢ []
    → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m)
        × Rel◃ (suc (sizeᴿᴸ Rs′)) W′ θ p (⌊ retᴿ D k ⌋ m)
            (valuesAt m Rs′))
  h′ m ne with ctr _ m (values-∈⁻ Rs′ (proj₂ (ne-head (valuesAt m Rs′) ne)))
  h′ m ne | refl =
    W , lift ⊑ʷ-refl , lift len ,
    ◃-fuel (suc (sizeᴸ (valuesAt k Rs′))) (suc (sizeᴿᴸ Rs′))
      {W} {θ} {p} {⌊ retᴿ D k ⌋ k} {valuesAt k Rs′}
      ≤-refl (s≤s (values-≤ k Rs′))
      (◃-mono (suc (sizeᴸ (valuesAt k Rs′))) {W} {θ} {p} {D}
         {⌊ retᴿ D k ⌋ k} {valuesAt k Rs′} c-⊆⌊retᴿ⌋ (h k))

-- results of a retᴿ set
ret▹ᶜ : ∀ {W θ p Rs D D′ k} → length W ≡ k
  → (∀ r → r ⋵ Rs → r ∈ᴿ retᴿ D k)
  → (∀ L → mem L ⊆ D → W ∣ θ ⊢ p ⊢ L ▹ D′)
  → W ∣ θ ⊢ p ⊢ Rs ▹ᶜ retᴿ D′ k
ret▹ᶜ {Rs = Rs} len Rs⊆ h =
  val▹ᶜ len (λ v m r∈ → proj₁ (Rs⊆ _ r∈))
    (λ m → h (valuesAt m Rs) (λ y y∈ → proj₂ (Rs⊆ _ (values-∈⁻ Rs y∈))))

ret◃ᶜ : ∀ {W θ p D D′ Rs′ k} → length W ≡ k
  → (∀ r → r ⋵ Rs′ → r ∈ᴿ retᴿ D′ k)
  → (∀ L′ → mem L′ ⊆ D′ → W ∣ θ ⊢ p ⊢ D ◃ L′)
  → W ∣ θ ⊢ p ⊢ retᴿ D k ◃ᶜ Rs′
ret◃ᶜ {Rs′ = Rs′} len Rs⊆ h =
  val◃ᶜ len (λ e∈ → Rs⊆ err e∈) (λ v m r∈ → proj₁ (Rs⊆ _ r∈))
    (λ m → h (valuesAt m Rs′) (λ y y∈ → proj₂ (Rs⊆ _ (values-∈⁻ Rs′ y∈))))

-- a list with no members
empty▹ᶜ : ∀ {W θ p Rs R′} → (∀ r → r ⋵ Rs → ⊥) → W ∣ θ ⊢ p ⊢ Rs ▹ᶜ R′
empty▹ᶜ {Rs = Rs} none m ne =
  ⊥-elim (none _ (values-∈⁻ Rs (proj₂ (ne-head (valuesAt m Rs) ne))))

empty◃ᶜ : ∀ {W θ p R Rs′} → (∀ r → r ⋵ Rs′ → ⊥) → W ∣ θ ⊢ p ⊢ R ◃ᶜ Rs′
empty◃ᶜ {Rs′ = Rs′} none =
  inj₂ (lift (λ he → none _ (HasErr→∈ he)) ,
        λ m ne → ⊥-elim (none _ (values-∈⁻ Rs′
                                   (proj₂ (ne-head (valuesAt m Rs′) ne)))))

-- a related list of results also relates under a smaller world
▹ᶜ-weaken : ∀ {k W W₂ θ p Rs R′} → W ⊑ʷ W₂
  → Rel▹ᶜ k W₂ θ p Rs R′ → Rel▹ᶜ k W θ p Rs R′
▹ᶜ-weaken ext h m ne with h m ne
▹ᶜ-weaken ext h m ne | W₃ , lift e , len , rel =
  W₃ , lift (⊑ʷ-trans ext e) , len , rel

◃ᶜ-weaken : ∀ {k W W₂ θ p R Rs′} → W ⊑ʷ W₂
  → Rel◃ᶜ k W₂ θ p R Rs′ → Rel◃ᶜ k W θ p R Rs′
◃ᶜ-weaken ext (inj₁ e) = inj₁ e
◃ᶜ-weaken {k} {W} {W₂} {θ} {p} {R} {Rs′} ext (inj₂ (ne , h)) =
  inj₂ (ne , h′)
  where
  h′ : ∀ m → valuesAt m Rs′ ≢ []
    → Σ[ W₃ ∈ World ] (Lift₁ (W ⊑ʷ W₃) × Lift₁ (length W₃ ≡ m)
        × Rel◃ k W₃ θ p (⌊ R ⌋ m) (valuesAt m Rs′))
  h′ m ne₃ with h m ne₃
  h′ m ne₃ | W₃ , lift e , len , rel = W₃ , lift (⊑ʷ-trans ext e) , len , rel

-- binding into retᴿ adds nothing
≫=-ret⊆ : ∀ {R} → (R ≫= λ D m → retᴿ D m) ⊆ᴿ R
≫=-ret⊆ r (inj₁ (refl , e)) = e
≫=-ret⊆ {R} r (inj₂ (m , c , r∈)) = c-retᴿ⌊⌋-⊆ {R} {m} r r∈

------------------------------------------------------------------------
-- Finite support of the continuations of the denotation
------------------------------------------------------------------------

ext-fin : ∀ M θ ρ m → c-FinR (λ X → ⟦ M ⟧ θ (X • ρ) m)
ext-fin M θ ρ m X r r∈ with ⟦⟧-fin M θ m (X • ρ) r r∈
ext-fin M θ ρ m X r r∈ | φ , φ⊑ , r∈′ =
  φ zero , φ⊑ zero , ⟦⟧-mono M incl r r∈′
  where
  incl : ⟪ φ ⟫ ⊆ₑ (mem (φ zero) • ρ)
  incl zero v v∈ = v∈
  incl (suc x) = φ⊑ (suc x)

ext-mono : ∀ M θ ρ m → c-MonoR (λ X → ⟦ M ⟧ θ (X • ρ) m)
ext-mono M θ ρ m X⊆ = ⟦⟧-mono M (ext-⊆ₑ X⊆ ⊆ₑ-refl)

cond-fin : ∀ {R S} → c-FinR (λ X → condᴿ X R S)
cond-fin X r (inj₁ (t∈ , r∈)) =
  vtrue ∷ [] , c-∷-⊆ t∈ c-[]-⊆ , inj₁ (here refl , r∈)
cond-fin X r (inj₂ (f∈ , r∈)) =
  vfalse ∷ [] , c-∷-⊆ f∈ c-[]-⊆ , inj₂ (here refl , r∈)

cond-mono : ∀ {R S} → c-MonoR (λ X → condᴿ X R S)
cond-mono X⊆ r (inj₁ (t∈ , r∈)) = inj₁ (X⊆ _ t∈ , r∈)
cond-mono X⊆ r (inj₂ (f∈ , r∈)) = inj₂ (X⊆ _ f∈ , r∈)

seal-inv : ∀ {σ X} x → x ∈ sealᴾ σ X
  → Σ[ u ∈ Val ] (x ≡ sealᵛ σ u × u ∈ X)
seal-inv vtrue ()
seal-inv vfalse ()
seal-inv (sealᵛ σ′ u) (refl , u∈) = u , refl , u∈
seal-inv (injᵛ G u) ()
seal-inv (U ⟼ r at m) ()
seal-inv (σ′ ⟼∀ r) ()
seal-inv νλ ()
seal-inv ν∀ ()

seal-fin : ∀ {σ m} → c-FinR (λ X → retᴿ (sealᴾ σ X) m)
seal-fin X err ()
seal-fin {σ} X (ret x k) (eq , x∈) with seal-inv x x∈
seal-fin {σ} X (ret x k) (eq , x∈) | u , refl , u∈ =
  u ∷ [] , c-∷-⊆ u∈ c-[]-⊆ , (eq , refl , here refl)

seal-mono : ∀ {σ m} → c-MonoR (λ X → retᴿ (sealᴾ σ X) m)
seal-mono X⊆ err ()
seal-mono X⊆ (ret x k) (eq , x∈) with seal-inv x x∈
seal-mono X⊆ (ret x k) (eq , x∈) | u , refl , u∈ = eq , refl , X⊆ u u∈

unseal-fin : ∀ {σ m} → c-FinR (λ X → retᴿ (unsealᴾ σ X) m)
unseal-fin X err ()
unseal-fin {σ} X (ret x k) (eq , x∈) =
  sealᵛ σ x ∷ [] , c-∷-⊆ x∈ c-[]-⊆ , (eq , here refl)

unseal-mono : ∀ {σ m} → c-MonoR (λ X → retᴿ (unsealᴾ σ X) m)
unseal-mono X⊆ err ()
unseal-mono X⊆ (ret x k) (eq , x∈) = eq , X⊆ _ x∈

test-fin : ∀ {G m} → c-FinR (λ X → retᴿ (testᴾ G X) m)
test-fin X err ()
test-fin {G} X (ret vtrue k) (eq , v , i∈) =
  injᵛ G v ∷ [] , c-∷-⊆ i∈ c-[]-⊆ , (eq , v , here refl)
test-fin X (ret vfalse k) (eq , H , v , i∈ , H≢) =
  injᵛ H v ∷ [] , c-∷-⊆ i∈ c-[]-⊆ , (eq , H , v , here refl , H≢)
test-fin X (ret (sealᵛ σ u) k) (eq , ())
test-fin X (ret (injᵛ H u) k) (eq , ())
test-fin X (ret (U ⟼ r at m) k) (eq , ())
test-fin X (ret (σ ⟼∀ r) k) (eq , ())
test-fin X (ret νλ k) (eq , ())
test-fin X (ret ν∀ k) (eq , ())

test-mono : ∀ {G m} → c-MonoR (λ X → retᴿ (testᴾ G X) m)
test-mono X⊆ err ()
test-mono X⊆ (ret vtrue k) (eq , v , i∈) = eq , v , X⊆ _ i∈
test-mono X⊆ (ret vfalse k) (eq , H , v , i∈ , H≢) =
  eq , H , v , X⊆ _ i∈ , H≢
test-mono X⊆ (ret (sealᵛ σ u) k) (eq , ())
test-mono X⊆ (ret (injᵛ H u) k) (eq , ())
test-mono X⊆ (ret (U ⟼ r at m) k) (eq , ())
test-mono X⊆ (ret (σ ⟼∀ r) k) (eq , ())
test-mono X⊆ (ret νλ k) (eq , ())
test-mono X⊆ (ret ν∀ k) (eq , ())

------------------------------------------------------------------------
-- Helpers for the cases
------------------------------------------------------------------------

sub▹ : ∀ {W θ p D′} L L₂ → mem L₂ ⊆ mem L
  → W ∣ θ ⊢ p ⊢ L ▹ D′ → W ∣ θ ⊢ p ⊢ L₂ ▹ D′
sub▹ {W} {θ} {p} {D′} L L₂ L⊆ = ▹-sub⊆ {W} {θ} {p} {L} {L₂} {D′} L⊆

sub◃ : ∀ {W θ p D} L L₂ → mem L₂ ⊆ mem L
  → W ∣ θ ⊢ p ⊢ D ◃ L → W ∣ θ ⊢ p ⊢ D ◃ L₂
sub◃ {W} {θ} {p} {D} L L₂ L⊆ = ◃-sub⊆ {W} {θ} {p} {D} {L} {L₂} L⊆

kripke▹ : ∀ {W W′ θ p D′} L → W ⊑ʷ W′
  → W ∣ θ ⊢ p ⊢ L ▹ D′ → W′ ∣ θ ⊢ p ⊢ L ▹ D′
kripke▹ {W} {W′} {θ} {p} {D′} L ext =
  ▹-kripke (suc (sizeᴸ L)) {W} {W′} {θ} {p} {L} {D′} ext

kripke◃ : ∀ {W W′ θ p D} L → W ⊑ʷ W′
  → W ∣ θ ⊢ p ⊢ D ◃ L → W′ ∣ θ ⊢ p ⊢ D ◃ L
kripke◃ {W} {W′} {θ} {p} {D} L ext =
  ◃-kripke (suc (sizeᴸ L)) {W} {W′} {θ} {p} {D} {L} ext

-- the value of a cast's result is at the cast's counter
cast-out : ∀ d p θ {E m₁ m y} → ret y m ∈ᴿ ⟦ d , p ⟧ᶜ θ E m₁
  → y ∈ ⌊ ⟦ d , p ⟧ᶜ θ E m₁ ⌋ m₁
cast-out d p θ y∈ with c-ctr d p θ y∈
cast-out d p θ y∈ | refl = y∈

-- booleans
true-rel : ∀ {D} x → x ≡ vtrue → vtrue ∈ D → IsBool D x
true-rel .vtrue refl t∈ = t∈

false-rel : ∀ {D} x → x ≡ vfalse → vfalse ∈ D → IsBool D x
false-rel .vfalse refl f∈ = f∈

const▹ : ∀ {W θ} b → (∀ {D} x → x ≡ b → b ∈ D → IsBool D x) → ∀ L
  → mem L ⊆ ⌈ b ⌉ → W ∣ θ ⊢ 𝔹⊑ ⊢ L ▹ ⌈ b ⌉
const▹ b isb [] L⊆ = tt₁
const▹ b isb (v ∷ L) L⊆ =
  lift (All-tab (v ∷ L) (λ x x∈ → isb x (L⊆ x x∈) refl))

const◃ : ∀ {W θ} b → (∀ {D} x → x ≡ b → b ∈ D → IsBool D x) → ∀ L′
  → mem L′ ⊆ ⌈ b ⌉ → W ∣ θ ⊢ 𝔹⊑ ⊢ ⌈ b ⌉ ◃ L′
const◃ b isb [] L⊆ = tt₁
const◃ b isb (v ∷ L) L⊆ =
  lift (All-tab (v ∷ L) (λ x x∈ → isb x (L⊆ x x∈) refl))

-- a boolean in a related list is in the set
bool-in▹ : ∀ {W θ D′} L x → W ∣ θ ⊢ 𝔹⊑ ⊢ L ▹ D′ → x ⋵ L → IsBool D′ x
bool-in▹ (v ∷ L) x (lift all) x∈ = All-lookup all x∈

bool-in◃ : ∀ {W θ D} L x → W ∣ θ ⊢ 𝔹⊑ ⊢ D ◃ L → x ⋵ L → IsBool D x
bool-in◃ (v ∷ L) x (lift all) x∈ = All-lookup all x∈

-- the seal case, on a related list of contents
seal▹ : ∀ {W θ q D′} α L → W ∣ θ ⊢ q ⊢ L ▹ D′
  → W ∋ʷ ⟦ α ⟧ₙ θ ⦂ ⟦ q ⟧ᵖ θ
  → ∀ Ys → mem Ys ⊆ sealᴾ (⟦ α ⟧ₙ θ) (mem L)
  → W ∣ θ ⊢ ‵⊑ α ⊢ Ys ▹ sealᴾ (⟦ α ⟧ₙ θ) D′
seal▹ α L rel w∋ [] Ys⊆ = tt₁
seal▹ {W} {θ} {q} {D′} α L rel w∋ (y ∷ Ys) Ys⊆ =
  lift (All-tab (y ∷ Ys) atS) , ⟦ q ⟧ᵖ θ , lift w∋ ,
  ▹-fuel (suc (sizeᴸ P)) (sizeᴸ (y ∷ Ys))
    {W} {θ₀} {⟦ q ⟧ᵖ θ} {P} {unsealᴾ σ (sealᴾ σ D′)}
    ≤-refl (unseal-< σ y Ys)
    (from (▹-close (suc (sizeᴸ P)) θ θ₀ {W} {q} {P}
             {unsealᴾ σ (sealᴾ σ D′)})
      (▹-mono′ P (λ x x∈ → refl , x∈) (sub▹ L P P⊆ rel)))
  where
  σ = ⟦ α ⟧ₙ θ
  P = unsealᴸ σ (y ∷ Ys)
  atS : ∀ x → x ⋵ (y ∷ Ys) → IsSealAt σ x
  atS x x∈ with seal-inv x (Ys⊆ x x∈)
  atS x x∈ | u , refl , u∈ = is-seal-at
  P⊆ : mem P ⊆ mem L
  P⊆ u u∈ with seal-inv {σ} {mem L} (sealᵛ σ u)
                  (Ys⊆ (sealᵛ σ u) (unseal-∈⁻ (y ∷ Ys) u∈))
  P⊆ u u∈ | u′ , refl , u′∈ = u′∈

seal◃ : ∀ {W θ q D} α L′ → W ∣ θ ⊢ q ⊢ D ◃ L′
  → W ∋ʷ ⟦ α ⟧ₙ θ ⦂ ⟦ q ⟧ᵖ θ
  → ∀ Ys → mem Ys ⊆ sealᴾ (⟦ α ⟧ₙ θ) (mem L′)
  → W ∣ θ ⊢ ‵⊑ α ⊢ sealᴾ (⟦ α ⟧ₙ θ) D ◃ Ys
seal◃ α L′ rel w∋ [] Ys⊆ = tt₁
seal◃ {W} {θ} {q} {D} α L′ rel w∋ (y ∷ Ys) Ys⊆ =
  lift (All-tab (y ∷ Ys) atS) , ⟦ q ⟧ᵖ θ , lift w∋ ,
  ◃-fuel (suc (sizeᴸ P)) (sizeᴸ (y ∷ Ys))
    {W} {θ₀} {⟦ q ⟧ᵖ θ} {unsealᴾ σ (sealᴾ σ D)} {P}
    ≤-refl (unseal-< σ y Ys)
    (from (◃-close (suc (sizeᴸ P)) θ θ₀ {W} {q}
             {unsealᴾ σ (sealᴾ σ D)} {P})
      (◃-mono′ P (λ x x∈ → refl , x∈) (sub◃ L′ P P⊆ rel)))
  where
  σ = ⟦ α ⟧ₙ θ
  P = unsealᴸ σ (y ∷ Ys)
  atS : ∀ x → x ⋵ (y ∷ Ys) → IsSealAt σ x
  atS x x∈ with seal-inv x (Ys⊆ x x∈)
  atS x x∈ | u , refl , u∈ = is-seal-at
  P⊆ : mem P ⊆ mem L′
  P⊆ u u∈ with seal-inv {σ} {mem L′} (sealᵛ σ u)
                  (Ys⊆ (sealᵛ σ u) (unseal-∈⁻ (y ∷ Ys) u∈))
  P⊆ u u∈ | u′ , refl , u′∈ = u′∈

-- the unseal case: the contents of a related list of sealed values
unseal▹ : ∀ {W θ q D′} α L → W ∣ θ ⊢ ‵⊑ α ⊢ L ▹ D′
  → W ∋ʷ ⟦ α ⟧ₙ θ ⦂ ⟦ q ⟧ᵖ θ
  → W ∣ θ ⊢ q ⊢ unsealᴸ (⟦ α ⟧ₙ θ) L ▹ unsealᴾ (⟦ α ⟧ₙ θ) D′
unseal▹ α [] rel w∋ = tt₁
unseal▹ {W} {θ} {q} {D′} α (v ∷ L) (all , q′ , lift w∋′ , rel₀) w∋
  with ∋ʷ-unique w∋′ w∋
unseal▹ {W} {θ} {q} {D′} α (v ∷ L) (all , q′ , lift w∋′ , rel₀) w∋
  | refl =
  to (▹-close (suc (sizeᴸ P)) θ θ₀ {W} {q} {P} {unsealᴾ σ D′})
    (▹-fuel (sizeᴸ (v ∷ L)) (suc (sizeᴸ P))
       {W} {θ₀} {⟦ q ⟧ᵖ θ} {P} {unsealᴾ σ D′}
       (unseal-< σ v L) ≤-refl rel₀)
  where
  σ = ⟦ α ⟧ₙ θ
  P = unsealᴸ σ (v ∷ L)

unseal◃ : ∀ {W θ q D} α L′ → W ∣ θ ⊢ ‵⊑ α ⊢ D ◃ L′
  → W ∋ʷ ⟦ α ⟧ₙ θ ⦂ ⟦ q ⟧ᵖ θ
  → W ∣ θ ⊢ q ⊢ unsealᴾ (⟦ α ⟧ₙ θ) D ◃ unsealᴸ (⟦ α ⟧ₙ θ) L′
unseal◃ α [] rel w∋ = tt₁
unseal◃ {W} {θ} {q} {D} α (v ∷ L) (all , q′ , lift w∋′ , rel₀) w∋
  with ∋ʷ-unique w∋′ w∋
unseal◃ {W} {θ} {q} {D} α (v ∷ L) (all , q′ , lift w∋′ , rel₀) w∋
  | refl =
  to (◃-close (suc (sizeᴸ P)) θ θ₀ {W} {q} {unsealᴾ σ D} {P})
    (◃-fuel (sizeᴸ (v ∷ L)) (suc (sizeᴸ P))
       {W} {θ₀} {⟦ q ⟧ᵖ θ} {unsealᴾ σ D} {P}
       (unseal-< σ v L) ≤-refl rel₀)
  where
  σ = ⟦ α ⟧ₙ θ
  P = unsealᴸ σ (v ∷ L)

unseal-sub : ∀ σ L Ys → mem Ys ⊆ unsealᴾ σ (mem L)
  → mem Ys ⊆ mem (unsealᴸ σ L)
unseal-sub σ L Ys Ys⊆ y y∈ = unseal-∈⁺ (Ys⊆ y y∈)

-- the tag-test case: each boolean of the left has a counterpart
test▹ : ∀ {W θ G D′} L → W ∣ θ ⊢ ★⊑ ⊢ L ▹ D′
  → ∀ x → x ∈ testᴾ G (mem L) → IsBool (testᴾ G D′) x
test▹ [] rel vtrue (v , ())
test▹ [] rel vfalse (H , v , () , H≢)
test▹ {G = G} (w ∷ L) (all , f) vtrue (v , i∈) =
  ▹-conv (sizeᴸ (w ∷ L)) (untag-∈⁺ i∈) (f G)
test▹ (w ∷ L) (all , f) vfalse (H , v , i∈ , H≢)
  with ▹-conv (sizeᴸ (w ∷ L)) (untag-∈⁺ i∈) (f H)
... | u , u∈ = H , u , u∈ , H≢
test▹ L rel (sealᵛ σ u) ()
test▹ L rel (injᵛ H u) ()
test▹ L rel (U ⟼ r at m) ()
test▹ L rel (σ ⟼∀ r) ()
test▹ L rel νλ ()
test▹ L rel ν∀ ()

test◃ : ∀ {W θ G D} L′ → W ∣ θ ⊢ ★⊑ ⊢ D ◃ L′
  → ∀ x → x ∈ testᴾ G (mem L′) → IsBool (testᴾ G D) x
test◃ [] rel vtrue (v , ())
test◃ [] rel vfalse (H , v , () , H≢)
test◃ {G = G} (w ∷ L) (all , f) vtrue (v , i∈) =
  ◃-conv (sizeᴸ (w ∷ L)) (untag-∈⁺ i∈) (f G)
test◃ (w ∷ L) (all , f) vfalse (H , v , i∈ , H≢)
  with ◃-conv (sizeᴸ (w ∷ L)) (untag-∈⁺ i∈) (f H)
... | u , u∈ = H , u , u∈ , H≢
test◃ L rel (sealᵛ σ u) ()
test◃ L rel (injᵛ H u) ()
test◃ L rel (U ⟼ r at m) ()
test◃ L rel (σ ⟼∀ r) ()
test◃ L rel νλ ()
test◃ L rel ν∀ ()

bool▹ : ∀ {W θ D D′} Ys → (∀ x → x ⋵ Ys → x ∈ D → IsBool D′ x)
  → mem Ys ⊆ D → W ∣ θ ⊢ 𝔹⊑ ⊢ Ys ▹ D′
bool▹ [] h Ys⊆ = tt₁
bool▹ (y ∷ Ys) h Ys⊆ =
  lift (All-tab (y ∷ Ys) (λ x x∈ → h x x∈ (Ys⊆ x x∈)))

bool◃ : ∀ {W θ D D′} Ys → (∀ x → x ⋵ Ys → x ∈ D′ → IsBool D x)
  → mem Ys ⊆ D′ → W ∣ θ ⊢ 𝔹⊑ ⊢ D ◃ Ys
bool◃ [] h Ys⊆ = tt₁
bool◃ (y ∷ Ys) h Ys⊆ =
  lift (All-tab (y ∷ Ys) (λ x x∈ → h x x∈ (Ys⊆ x x∈)))

------------------------------------------------------------------------
-- The fundamental lemma, reflection
------------------------------------------------------------------------

fundamental▹ : ∀ {Δ⊑ Γ⊑ M M′ p} → Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p
  → ∀ {θ W ρ ρ′ n} → TOK Δ⊑ θ W → Env▹ Γ⊑ θ W ρ ρ′
  → (∀ x → Consistent (ρ′ x)) → length W ≡ n
  → ∀ Rs → (∀ r → r ⋵ Rs → r ∈ᴿ ⟦ M ⟧ θ ρ n)
  → W ∣ θ ⊢ p ⊢ Rs ▹ᶜ ⟦ M′ ⟧ θ ρ′ n
fundamental▹ (⊑` x∈) tok env cρ′ len Rs Rs⊆ = ret▹ᶜ len Rs⊆ (env x∈)
fundamental▹ (⊑letv {M = M} {M′} {N} {N′} {p} {q} dM dN)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  bind▹ {θ} {θ} {W} {p} {q} {⟦ M ⟧ θ ρ n} {R′}
    {λ E m → ⟦ N ⟧ θ (E • ρ) m} {λ E m → ⟦ N′ ⟧ θ (E • ρ′) m}
    (λ m → ext-fin N θ ρ m) (λ m → ext-mono N θ ρ m) CR′
    (fundamental▹ dM tok env cρ′ len) hK Rs Rs⊆
  where
  R′ = ⟦ M′ ⟧ θ ρ′ n
  CR′ : Consistentᴿ R′
  CR′ = ⟦⟧-consistent M′ θ {ρ′} {n} cρ′
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L → W₁ ∣ θ ⊢ p ⊢ L ▹ ⌊ R′ ⌋ m₁
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ ⟦ N ⟧ θ (mem L • ρ) m₁)
    → W₁ ∣ θ ⊢ q ⊢ Rs₁ ▹ᶜ ⟦ N′ ⟧ θ (⌊ R′ ⌋ m₁ • ρ′) m₁
  hK m₁ W₁ ext₁ len₁ L rel Rs₁ Rs₁⊆ =
    fundamental▹ dN (TOK-kripke ext₁ tok)
      (Env▹-ext (λ L₀ L₀⊆ → sub▹ L L₀ L₀⊆ rel) (Env▹-kripke ext₁ env))
      (ext-consistent (⌊⌋-consistent CR′ m₁) cρ′) len₁ Rs₁ Rs₁⊆
fundamental▹ (⊑seal {X = X} {M} {M′} {q} X∈ dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  bind▹ {θ} {θ} {W} {q} {‵⊑ (tvar X)} {⟦ M ⟧ θ ρ n} {R′}
    {λ E m → retᴿ (sealᴾ (θ X) E) m} {λ E m → retᴿ (sealᴾ (θ X) E) m}
    (λ m → seal-fin) (λ m → seal-mono) CR′
    (fundamental▹ dM tok env cρ′ len) hK Rs Rs⊆
  where
  R′ = ⟦ M′ ⟧ θ ρ′ n
  CR′ : Consistentᴿ R′
  CR′ = ⟦⟧-consistent M′ θ {ρ′} {n} cρ′
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L → W₁ ∣ θ ⊢ q ⊢ L ▹ ⌊ R′ ⌋ m₁
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ retᴿ (sealᴾ (θ X) (mem L)) m₁)
    → W₁ ∣ θ ⊢ ‵⊑ (tvar X) ⊢ Rs₁ ▹ᶜ retᴿ (sealᴾ (θ X) (⌊ R′ ⌋ m₁)) m₁
  hK m₁ W₁ ext₁ len₁ L rel Rs₁ Rs₁⊆ =
    ret▹ᶜ len₁ Rs₁⊆
      (seal▹ (tvar X) L rel (TOK-kripke ext₁ tok X∈))
fundamental▹ (⊑unseal {X = X} {M} {M′} {q} X∈ dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  bind▹ {θ} {θ} {W} {‵⊑ (tvar X)} {q} {⟦ M ⟧ θ ρ n} {R′}
    {λ E m → retᴿ (unsealᴾ (θ X) E) m} {λ E m → retᴿ (unsealᴾ (θ X) E) m}
    (λ m → unseal-fin) (λ m → unseal-mono) CR′
    (fundamental▹ dM tok env cρ′ len) hK Rs Rs⊆
  where
  R′ = ⟦ M′ ⟧ θ ρ′ n
  CR′ : Consistentᴿ R′
  CR′ = ⟦⟧-consistent M′ θ {ρ′} {n} cρ′
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L → W₁ ∣ θ ⊢ ‵⊑ (tvar X) ⊢ L ▹ ⌊ R′ ⌋ m₁
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ retᴿ (unsealᴾ (θ X) (mem L)) m₁)
    → W₁ ∣ θ ⊢ q ⊢ Rs₁ ▹ᶜ retᴿ (unsealᴾ (θ X) (⌊ R′ ⌋ m₁)) m₁
  hK m₁ W₁ ext₁ len₁ L rel Rs₁ Rs₁⊆ =
    ret▹ᶜ len₁ Rs₁⊆
      (λ Ys Ys⊆ →
         sub▹ (unsealᴸ (θ X) L) Ys (unseal-sub (θ X) L Ys Ys⊆)
           (unseal▹ (tvar X) L rel (TOK-kripke ext₁ tok X∈)))
fundamental▹ (⊑is {G = G} {M} {M′} wfG dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  bind▹ {θ} {θ} {W} {★⊑} {𝔹⊑} {⟦ M ⟧ θ ρ n} {R′}
    {λ E m → retᴿ (testᴾ (⟦ G ⟧ᴳ θ) E) m}
    {λ E m → retᴿ (testᴾ (⟦ G ⟧ᴳ θ) E) m}
    (λ m → test-fin) (λ m → test-mono) CR′
    (fundamental▹ dM tok env cρ′ len) hK Rs Rs⊆
  where
  R′ = ⟦ M′ ⟧ θ ρ′ n
  CR′ : Consistentᴿ R′
  CR′ = ⟦⟧-consistent M′ θ {ρ′} {n} cρ′
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L → W₁ ∣ θ ⊢ ★⊑ ⊢ L ▹ ⌊ R′ ⌋ m₁
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ retᴿ (testᴾ (⟦ G ⟧ᴳ θ) (mem L)) m₁)
    → W₁ ∣ θ ⊢ 𝔹⊑ ⊢ Rs₁ ▹ᶜ retᴿ (testᴾ (⟦ G ⟧ᴳ θ) (⌊ R′ ⌋ m₁)) m₁
  hK m₁ W₁ ext₁ len₁ L rel Rs₁ Rs₁⊆ =
    ret▹ᶜ len₁ Rs₁⊆
      (λ Ys Ys⊆ → bool▹ Ys (λ x x∈ → test▹ L rel x) Ys⊆)
fundamental▹ ⊑true tok env cρ′ len Rs Rs⊆ =
  ret▹ᶜ len Rs⊆ (const▹ vtrue true-rel)
fundamental▹ ⊑false tok env cρ′ len Rs Rs⊆ =
  ret▹ᶜ len Rs⊆ (const▹ vfalse false-rel)
fundamental▹ (⊑if {L = L} {L′} {M} {M′} {N} {N′} {q} dL dM dN)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  bind▹ {θ} {θ} {W} {𝔹⊑} {q} {⟦ L ⟧ θ ρ n} {R′}
    {λ E m → condᴿ E (⟦ M ⟧ θ ρ m) (⟦ N ⟧ θ ρ m)}
    {λ E m → condᴿ E (⟦ M′ ⟧ θ ρ′ m) (⟦ N′ ⟧ θ ρ′ m)}
    (λ m → cond-fin) (λ m → cond-mono) CR′
    (fundamental▹ dL tok env cρ′ len) hK Rs Rs⊆
  where
  R′ = ⟦ L′ ⟧ θ ρ′ n
  CR′ : Consistentᴿ R′
  CR′ = ⟦⟧-consistent L′ θ {ρ′} {n} cρ′
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ Lb → W₁ ∣ θ ⊢ 𝔹⊑ ⊢ Lb ▹ ⌊ R′ ⌋ m₁
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁
                 → r ∈ᴿ condᴿ (mem Lb) (⟦ M ⟧ θ ρ m₁) (⟦ N ⟧ θ ρ m₁))
    → W₁ ∣ θ ⊢ q ⊢ Rs₁
        ▹ᶜ condᴿ (⌊ R′ ⌋ m₁) (⟦ M′ ⟧ θ ρ′ m₁) (⟦ N′ ⟧ θ ρ′ m₁)
  hK m₁ W₁ ext₁ len₁ Lb rel [] Rs₁⊆ =
    empty▹ᶜ {W₁} {θ} {q} {[]}
      {condᴿ (⌊ R′ ⌋ m₁) (⟦ M′ ⟧ θ ρ′ m₁) (⟦ N′ ⟧ θ ρ′ m₁)} (λ r ())
  hK m₁ W₁ ext₁ len₁ Lb rel (r₀ ∷ Rs₁) Rs₁⊆
    with ▹-bool (suc (sizeᴸ Lb)) {W₁} {θ} {Lb} {⌊ R′ ⌋ m₁}
           (⌊⌋-consistent CR′ m₁) rel
  hK m₁ W₁ ext₁ len₁ Lb rel (r₀ ∷ Rs₁) Rs₁⊆ | inj₁ allT =
    ▹ᶜ-mono (suc (sizeᴿᴸ (r₀ ∷ Rs₁))) {W₁} {θ} {q} {r₀ ∷ Rs₁}
      {⟦ M′ ⟧ θ ρ′ m₁}
      {condᴿ (⌊ R′ ⌋ m₁) (⟦ M′ ⟧ θ ρ′ m₁) (⟦ N′ ⟧ θ ρ′ m₁)}
      (λ r r∈ → inj₁ (t∈ , r∈))
      (fundamental▹ dM (TOK-kripke ext₁ tok) (Env▹-kripke ext₁ env) cρ′
         len₁ (r₀ ∷ Rs₁) inM)
    where
    inM : ∀ r → r ⋵ (r₀ ∷ Rs₁) → r ∈ᴿ ⟦ M ⟧ θ ρ m₁
    inM r r∈ with Rs₁⊆ r r∈
    inM r r∈ | inj₁ (t∈′ , r∈′) = r∈′
    inM r r∈ | inj₂ (f∈ , r∈′) with All-lookup allT f∈
    inM r r∈ | inj₂ (f∈ , r∈′) | ()
    t∈ : vtrue ∈ ⌊ R′ ⌋ m₁
    t∈ with Rs₁⊆ r₀ (here refl)
    t∈ | inj₁ (t∈′ , r∈′) = bool-in▹ Lb vtrue rel t∈′
    t∈ | inj₂ (f∈ , r∈′) with All-lookup allT f∈
    t∈ | inj₂ (f∈ , r∈′) | ()
  hK m₁ W₁ ext₁ len₁ Lb rel (r₀ ∷ Rs₁) Rs₁⊆ | inj₂ allF =
    ▹ᶜ-mono (suc (sizeᴿᴸ (r₀ ∷ Rs₁))) {W₁} {θ} {q} {r₀ ∷ Rs₁}
      {⟦ N′ ⟧ θ ρ′ m₁}
      {condᴿ (⌊ R′ ⌋ m₁) (⟦ M′ ⟧ θ ρ′ m₁) (⟦ N′ ⟧ θ ρ′ m₁)}
      (λ r r∈ → inj₂ (f∈ , r∈))
      (fundamental▹ dN (TOK-kripke ext₁ tok) (Env▹-kripke ext₁ env) cρ′
         len₁ (r₀ ∷ Rs₁) inN)
    where
    inN : ∀ r → r ⋵ (r₀ ∷ Rs₁) → r ∈ᴿ ⟦ N ⟧ θ ρ m₁
    inN r r∈ with Rs₁⊆ r r∈
    inN r r∈ | inj₂ (f∈′ , r∈′) = r∈′
    inN r r∈ | inj₁ (t∈ , r∈′) with All-lookup allF t∈
    inN r r∈ | inj₁ (t∈ , r∈′) | ()
    f∈ : vfalse ∈ ⌊ R′ ⌋ m₁
    f∈ with Rs₁⊆ r₀ (here refl)
    f∈ | inj₂ (f∈′ , r∈′) = bool-in▹ Lb vfalse rel f∈′
    f∈ | inj₁ (t∈ , r∈′) with All-lookup allF t∈
    f∈ | inj₁ (t∈ , r∈′) | ()
fundamental▹ (⊑ƛ {A = A} {A′} {M} {M′} {p} {q} p⊢ dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  ret▹ᶜ len Rs⊆ lam
  where
  F : 𝒱 → ℕ → ℛ
  F E m = ⟦ M ⟧ θ (E • ρ) m
  F′ : 𝒱 → ℕ → ℛ
  F′ E m = ⟦ M′ ⟧ θ (E • ρ′) m
  lam : ∀ Ys → mem Ys ⊆ Λ F → W ∣ θ ⊢ p ⇒⊑ q ⊢ Ys ▹ Λ F′
  lam [] Ys⊆ = tt₁
  lam (y ∷ Ys) Ys⊆ =
    lift (All-tab (y ∷ Ys) (λ x x∈ → Λ-IsFun {F = F} x (Ys⊆ x x∈))) ,
    lift tt , g
    where
    g : ∀ L₀ → L₀ ⊑ˢ (y ∷ Ys) → ∀ m′ W′ → W ⊑ʷ W′ → length W′ ≡ m′
      → ∀ E′ → Consistent E′
      → Rel▹ (sizeᴸ (y ∷ Ys)) W′ θ p (argsAt m′ L₀) E′
      → Rel▹ᶜ (sizeᴸ (y ∷ Ys)) W′ θ q (resultsAt m′ L₀) (Λ F′ ●[ m′ ] E′)
    g L₀ s m′ W′ ext len′ E′ CE′ relA m₃ ne₃ = result
      where
      A₀ = argsAt m′ L₀
      Rs₀ = resultsAt m′ L₀
      relA′ : W′ ∣ θ ⊢ p ⊢ A₀ ▹ E′
      relA′ = ▹-out A₀ (args-sub-< m′ y Ys s) relA
      in₀ : ∀ r → r ⋵ Rs₀ → r ∈ᴿ ⟦ M ⟧ θ (mem A₀ • ρ) m′
      in₀ r r∈ with results-∈⁻ L₀ r∈
      in₀ r r∈ | U , e∈ with Ys⊆ _ (sub-mem s _ e∈)
      in₀ r r∈ | U , e∈ | r∈′ , U≢ , U≈ =
        ⟦⟧-mono M (ext-⊆ₑ (λ u u∈ → args-∈⁺ e∈ u∈) ⊆ₑ-refl) r r∈′
      IH : W′ ∣ θ ⊢ q ⊢ Rs₀ ▹ᶜ ⟦ M′ ⟧ θ (E′ • ρ′) m′
      IH = fundamental▹ dM (TOK-kripke ext tok)
             (Env▹-ext (λ L L⊆ → sub▹ A₀ L L⊆ relA′) (Env▹-kripke ext env))
             (ext-consistent CE′ cρ′) len′ Rs₀ in₀
      -- the arguments are nonempty, since some entry has a result here
      cE′ : Conv E′
      cE′ with values-∈⁻ Rs₀ (proj₂ (ne-head (valuesAt m₃ Rs₀) ne₃))
      cE′ | r∈ with results-∈⁻ L₀ r∈
      cE′ | r∈ | U , e∈ with Ys⊆ _ (sub-mem s _ e∈)
      cE′ | r∈ | [] , e∈ | r∈′ , U≢ , U≈ = ⊥-elim (U≢ refl)
      cE′ | r∈ | (u ∷ U) , e∈ | r∈′ , U≢ , U≈ =
        ▹-conv (sizeᴸ (y ∷ Ys)) (args-∈⁺ e∈ (here refl)) relA
      result : Σ[ W₃ ∈ World ] (Lift₁ (W′ ⊑ʷ W₃) × Lift₁ (length W₃ ≡ m₃)
                 × Rel▹ (sizeᴸ (y ∷ Ys)) W₃ θ q (valuesAt m₃ Rs₀)
                     (⌊ Λ F′ ●[ m′ ] E′ ⌋ m₃))
      result with IH m₃ ne₃
      result | W₃ , ext₃ , len₃ , rel₃ =
        W₃ , ext₃ , len₃ ,
        ▹-mono (sizeᴸ (y ∷ Ys)) {W₃} {θ} {q} {valuesAt m₃ Rs₀}
          {⌊ ⟦ M′ ⟧ θ (E′ • ρ′) m′ ⌋ m₃} {⌊ Λ F′ ●[ m′ ] E′ ⌋ m₃}
          (c-⌊⌋-mono (Λ-β M′ θ ρ′ CE′ cE′))
          (▹-fuel (suc (sizeᴿᴸ Rs₀)) (sizeᴸ (y ∷ Ys))
             {W₃} {θ} {q} {valuesAt m₃ Rs₀} {⌊ ⟦ M′ ⟧ θ (E′ • ρ′) m′ ⌋ m₃}
             (s≤s (values-≤ m₃ Rs₀))
             (values-results-< m₃ m′ y Ys s) rel₃)
fundamental▹ (⊑· {L = L} {L′} {M} {M′} {p} {q} dL dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  bind▹ {θ} {θ} {W} {p ⇒⊑ q} {q} {⟦ L ⟧ θ ρ n} {R′} {K} {K′}
    (λ n₁ → c-≫=-finK {R = ⟦ M ⟧ θ ρ n₁} {K = λ F E n₂ → F ●[ n₂ ] E}
              (λ E n₂ → c-●ˡ-fin {E} {n₂}))
    (λ n₁ → c-≫=-monoK {R = ⟦ M ⟧ θ ρ n₁} {K = λ F E n₂ → F ●[ n₂ ] E}
              (λ E n₂ → c-●ˡ-mono {E} {n₂}))
    CR′ (fundamental▹ dL tok env cρ′ len) hK Rs Rs⊆
  where
  R′ = ⟦ L′ ⟧ θ ρ′ n
  CR′ : Consistentᴿ R′
  CR′ = ⟦⟧-consistent L′ θ {ρ′} {n} cρ′
  K : 𝒱 → ℕ → ℛ
  K F n₁ = ⟦ M ⟧ θ ρ n₁ ≫= λ E n₂ → F ●[ n₂ ] E
  K′ : 𝒱 → ℕ → ℛ
  K′ F n₁ = ⟦ M′ ⟧ θ ρ′ n₁ ≫= λ E n₂ → F ●[ n₂ ] E
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ Lf → W₁ ∣ θ ⊢ p ⇒⊑ q ⊢ Lf ▹ ⌊ R′ ⌋ m₁
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ K (mem Lf) m₁)
    → W₁ ∣ θ ⊢ q ⊢ Rs₁ ▹ᶜ K′ (⌊ R′ ⌋ m₁) m₁
  hK m₁ W₁ ext₁ len₁ Lf relF Rs₁ Rs₁⊆ =
    bind▹ {θ} {θ} {W₁} {p} {q} {⟦ M ⟧ θ ρ m₁} {⟦ M′ ⟧ θ ρ′ m₁}
      {λ E n₂ → mem Lf ●[ n₂ ] E} {λ E n₂ → ⌊ R′ ⌋ m₁ ●[ n₂ ] E}
      (λ n₂ → c-●ʳ-fin {mem Lf} {n₂}) (λ n₂ → c-●ʳ-mono {mem Lf} {n₂})
      CM′
      (fundamental▹ dM (TOK-kripke ext₁ tok) (Env▹-kripke ext₁ env) cρ′
         len₁)
      hK₂ Rs₁ Rs₁⊆
    where
    CM′ : Consistentᴿ (⟦ M′ ⟧ θ ρ′ m₁)
    CM′ = ⟦⟧-consistent M′ θ {ρ′} {m₁} cρ′
    hK₂ : ∀ m₂ W₂ → W₁ ⊑ʷ W₂ → length W₂ ≡ m₂
      → ∀ La → W₂ ∣ θ ⊢ p ⊢ La ▹ ⌊ ⟦ M′ ⟧ θ ρ′ m₁ ⌋ m₂
      → ∀ Rs₂ → (∀ r → r ⋵ Rs₂ → r ∈ᴿ (mem Lf ●[ m₂ ] mem La))
      → W₂ ∣ θ ⊢ q ⊢ Rs₂ ▹ᶜ (⌊ R′ ⌋ m₁ ●[ m₂ ] ⌊ ⟦ M′ ⟧ θ ρ′ m₁ ⌋ m₂)
    hK₂ m₂ W₂ ext₂ len₂ La relA Rs₂ Rs₂⊆ =
      app▹ {θ} {W₂} {p} {q} {Lf} {⌊ R′ ⌋ m₁} {mem La}
        {⌊ ⟦ M′ ⟧ θ ρ′ m₁ ⌋ m₂} {m₂}
        (kripke▹ Lf ext₂ relF) len₂ (⌊⌋-consistent CM′ m₂)
        (λ La′ La′⊆ → sub▹ La La′ La′⊆ relA) Rs₂ Rs₂⊆
fundamental▹ (⊑Λν {M = M} {M′} {p} dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  ret▹ᶜ len Rs⊆ poly
  where
  F : Seal → ℛ
  F σ = ⟦ M ⟧ (σ •ᵗ θ) ρ (suc σ)
  F′ : Seal → ℛ
  F′ σ = ⟦ M′ ⟧ (σ •ᵗ θ) ρ′ (suc σ)
  poly : ∀ Ys → mem Ys ⊆ Λᴾ F → W ∣ θ ⊢ ∀⊑ p ⊢ Ys ▹ Λᴾ F′
  poly [] Ys⊆ = tt₁
  poly (y ∷ Ys) Ys⊆ =
    lift (All-tab (y ∷ Ys) (λ x x∈ → Λᴾ-IsPoly {F = F} x (Ys⊆ x x∈))) ,
    lift tt , g
    where
    g : ∀ σ W′ q′ → W ⊑ʷ W′ → length W′ ≡ σ
      → Rel▹ᶜ (sizeᴸ (y ∷ Ys)) (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) p
          (bodiesAt σ (y ∷ Ys)) (Λᴾ F′ ◆ σ)
    g σ W′ q′ ext len′ =
      ▹ᶜ-fuel (suc (sizeᴿᴸ B)) (sizeᴸ (y ∷ Ys))
        {W′ ++ (q′ ∷ [])} {σ •ᵗ θ} {p} {B} {Λᴾ F′ ◆ σ}
        ≤-refl (bodies-< σ y Ys)
        (fundamental▹ dM
           (TOK-kripke ext′ (TOK-abs {σ = σ} tok))
           (Env▹-kripke ext′ (Env▹-⤊ {σ = σ} env)) cρ′
           (trans (length-++1 W′ q′) (cong suc len′)) B B⊆)
      where
      B = bodiesAt σ (y ∷ Ys)
      ext′ : W ⊑ʷ (W′ ++ (q′ ∷ []))
      ext′ = ⊑ʷ-trans ext (q′ ∷ [] , refl)
      B⊆ : ∀ r → r ⋵ B → r ∈ᴿ F σ
      B⊆ r r∈ = Ys⊆ _ (bodies-∈⁻ (y ∷ Ys) r∈)
fundamental▹ (⊑inst {M = M} {M′} {B} {B′} {N} {N′} {p} {q} {r} dM q⊢ dN)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  bind▹ {θ} {θ} {W} {∀⊑ p} {r} {⟦ M ⟧ θ ρ n} {R′} {K} {K′}
    (λ n₁ → c-≫=-fin {Φ = λ F → F ◆ n₁}
              {K = λ E n₂ → ⟦ N ⟧ (n₁ •ᵗ θ) (E • ρ) n₂}
              (c-◆-fin {n₁}) (c-◆-mono {n₁})
              (λ n₂ → ext-fin N (n₁ •ᵗ θ) ρ n₂)
              (λ n₂ → ext-mono N (n₁ •ᵗ θ) ρ n₂))
    (λ n₁ → c-≫=-monoR {Φ = λ F → F ◆ n₁}
              {K = λ E n₂ → ⟦ N ⟧ (n₁ •ᵗ θ) (E • ρ) n₂}
              (c-◆-mono {n₁}) (λ n₂ → ext-mono N (n₁ •ᵗ θ) ρ n₂))
    CR′ (fundamental▹ dM tok env cρ′ len) hK Rs Rs⊆
  where
  R′ = ⟦ M′ ⟧ θ ρ′ n
  CR′ : Consistentᴿ R′
  CR′ = ⟦⟧-consistent M′ θ {ρ′} {n} cρ′
  K : 𝒱 → ℕ → ℛ
  K F n₁ = (F ◆ n₁) ≫= λ E n₂ → ⟦ N ⟧ (n₁ •ᵗ θ) (E • ρ) n₂
  K′ : 𝒱 → ℕ → ℛ
  K′ F n₁ = (F ◆ n₁) ≫= λ E n₂ → ⟦ N′ ⟧ (n₁ •ᵗ θ) (E • ρ′) n₂
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ Lf → W₁ ∣ θ ⊢ ∀⊑ p ⊢ Lf ▹ ⌊ R′ ⌋ m₁
    → ∀ Rs₁ → (∀ r₁ → r₁ ⋵ Rs₁ → r₁ ∈ᴿ K (mem Lf) m₁)
    → W₁ ∣ θ ⊢ r ⊢ Rs₁ ▹ᶜ K′ (⌊ R′ ⌋ m₁) m₁
  hK .(length W₁) W₁ ext₁ refl [] relF Rs₁ Rs₁⊆ =
    empty▹ᶜ {W₁} {θ} {r} {Rs₁} {K′ (⌊ R′ ⌋ (length W₁)) (length W₁)}
      (λ r₁ r₁∈ → none (Rs₁⊆ r₁ r₁∈))
    where
    none : ∀ {r₁} → r₁ ∈ᴿ K (mem []) (length W₁) → ⊥
    none (inj₁ (eq , ()))
    none (inj₂ (m₂ , (c , ()) , r∈))
  hK .(length W₁) W₁ ext₁ refl (v ∷ Lf) (all , ν∈ , f) Rs₁ Rs₁⊆ =
    ▹ᶜ-weaken {suc (sizeᴿᴸ Rs₁)} {W₁} {W₂} {θ} {r} {Rs₁}
      {K′ (⌊ R′ ⌋ m₁) m₁} (q′ ∷ [] , refl)
      (to (▹ᶜ-subst (suc (sizeᴿᴸ Rs₁)) {θ} {θ₂} {↑ₙ} {W₂} {r} {Rs₁}
             {K′ (⌊ R′ ⌋ m₁) m₁} (λ i → refl))
        inner)
    where
    m₁ = length W₁
    θ₂ = m₁ •ᵗ θ
    q′ = ⟦ q ⟧ᵖ θ
    W₂ = W₁ ++ (q′ ∷ [])
    D′ = ⌊ R′ ⌋ m₁
    hB : Rel▹ᶜ (sizeᴸ (v ∷ Lf)) W₂ θ₂ p (bodiesAt m₁ (v ∷ Lf)) (D′ ◆ m₁)
    hB = f m₁ W₁ q′ ⊑ʷ-refl refl
    hR₂ : ∀ Rs₂ → (∀ r₂ → r₂ ⋵ Rs₂ → r₂ ∈ᴿ (mem (v ∷ Lf) ◆ m₁))
      → W₂ ∣ θ₂ ⊢ p ⊢ Rs₂ ▹ᶜ (D′ ◆ m₁)
    hR₂ Rs₂ Rs₂⊆ =
      ▹ᶜ-⊆ (sizeᴸ (v ∷ Lf)) (sizeᴸ (v ∷ Lf)) (suc (sizeᴿᴸ Rs₂))
        {W₂} {θ₂} {p} {bodiesAt m₁ (v ∷ Lf)} {Rs₂} {D′ ◆ m₁}
        (bodies-bound (v ∷ Lf) (size-bound (v ∷ Lf)))
        (bodies-< m₁ v Lf) ≤-refl
        (λ r₂ r₂∈ → bodies-∈⁺ (Rs₂⊆ r₂ r₂∈)) hB
    CD : Consistentᴿ (D′ ◆ m₁)
    CD = ◆-consistent {σ = m₁} (⌊⌋-consistent CR′ m₁)
    hK₂ : ∀ m₂ W₃ → W₂ ⊑ʷ W₃ → length W₃ ≡ m₂
      → ∀ La → W₃ ∣ θ₂ ⊢ p ⊢ La ▹ ⌊ D′ ◆ m₁ ⌋ m₂
      → ∀ Rs₂ → (∀ r₂ → r₂ ⋵ Rs₂ → r₂ ∈ᴿ ⟦ N ⟧ θ₂ (mem La • ρ) m₂)
      → W₃ ∣ θ₂ ⊢ ⇑ᵖ r ⊢ Rs₂ ▹ᶜ ⟦ N′ ⟧ θ₂ (⌊ D′ ◆ m₁ ⌋ m₂ • ρ′) m₂
    hK₂ m₂ W₃ ext₃ len₃ La relA Rs₂ Rs₂⊆ =
      fundamental▹ dN
        (TOK-known {q = q} (TOK-kripke ext₁ tok) ext₃)
        (Env▹-ext (λ L₀ L₀⊆ → sub▹ La L₀ L₀⊆ relA)
           (Env▹-⤊ {σ = m₁}
              (Env▹-kripke (⊑ʷ-trans ext₁ (⊑ʷ-trans (q′ ∷ [] , refl) ext₃))
                 env)))
        (ext-consistent (⌊⌋-consistent CD m₂) cρ′) len₃ Rs₂ Rs₂⊆
    inner : W₂ ∣ θ₂ ⊢ ⇑ᵖ r ⊢ Rs₁ ▹ᶜ K′ D′ m₁
    inner =
      bind▹ {θ₂} {θ₂} {W₂} {p} {⇑ᵖ r} {mem (v ∷ Lf) ◆ m₁} {D′ ◆ m₁}
        {λ E n₂ → ⟦ N ⟧ θ₂ (E • ρ) n₂} {λ E n₂ → ⟦ N′ ⟧ θ₂ (E • ρ′) n₂}
        (λ n₂ → ext-fin N θ₂ ρ n₂) (λ n₂ → ext-mono N θ₂ ρ n₂) CD
        hR₂ hK₂ Rs₁ Rs₁⊆
fundamental▹ (⊑upL {M = M} {M′} {AB} {BC} {AC} dM AB⊢ BC⊢ AC⊢)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  ▹ᶜ-mono (suc (sizeᴿᴸ Rs)) {W} {θ} {BC} {Rs}
    {R′ ≫= λ D m → retᴿ D m} {R′} (≫=-ret⊆ {R′})
    (bind▹ {θ} {θ} {W} {AC} {BC} {⟦ M ⟧ θ ρ n} {R′}
       {⟦ up , AB ⟧ᶜ θ} {λ D m → retᴿ D m}
       (c-fin up AB θ) (c-mono up AB θ) CR′
       (fundamental▹ dM tok env cρ′ len) hK Rs Rs⊆)
  where
  R′ = ⟦ M′ ⟧ θ ρ′ n
  CR′ : Consistentᴿ R′
  CR′ = ⟦⟧-consistent M′ θ {ρ′} {n} cρ′
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L → W₁ ∣ θ ⊢ AC ⊢ L ▹ ⌊ R′ ⌋ m₁
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ ⟦ up , AB ⟧ᶜ θ (mem L) m₁)
    → W₁ ∣ θ ⊢ BC ⊢ Rs₁ ▹ᶜ retᴿ (⌊ R′ ⌋ m₁) m₁
  hK m₁ W₁ ext₁ len₁ L rel Rs₁ Rs₁⊆ =
    val▹ᶜ len₁ (λ v m r∈ → c-ctr up AB θ (Rs₁⊆ _ r∈))
      (λ m → upL▹ {L = L} {D′ = ⌊ R′ ⌋ m₁} {m = m₁} AB⊢ BC⊢ AC⊢ rel
               (valuesAt m Rs₁)
               (λ y y∈ → cast-out up AB θ (Rs₁⊆ _ (values-∈⁻ Rs₁ y∈))))
fundamental▹ (⊑downL {M = M} {M′} {AB} {BC} {AC} dM AB⊢ BC⊢ AC⊢)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ =
  ▹ᶜ-mono (suc (sizeᴿᴸ Rs)) {W} {θ} {AC} {Rs}
    {R′ ≫= λ D m → retᴿ D m} {R′} (≫=-ret⊆ {R′})
    (bind▹ {θ} {θ} {W} {BC} {AC} {⟦ M ⟧ θ ρ n} {R′}
       {⟦ down , AB ⟧ᶜ θ} {λ D m → retᴿ D m}
       (c-fin down AB θ) (c-mono down AB θ) CR′
       (fundamental▹ dM tok env cρ′ len) hK Rs Rs⊆)
  where
  R′ = ⟦ M′ ⟧ θ ρ′ n
  CR′ : Consistentᴿ R′
  CR′ = ⟦⟧-consistent M′ θ {ρ′} {n} cρ′
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L → W₁ ∣ θ ⊢ BC ⊢ L ▹ ⌊ R′ ⌋ m₁
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ ⟦ down , AB ⟧ᶜ θ (mem L) m₁)
    → W₁ ∣ θ ⊢ AC ⊢ Rs₁ ▹ᶜ retᴿ (⌊ R′ ⌋ m₁) m₁
  hK m₁ W₁ ext₁ len₁ L rel Rs₁ Rs₁⊆ =
    val▹ᶜ len₁ (λ v m r∈ → c-ctr down AB θ (Rs₁⊆ _ r∈))
      (λ m → downL▹ {L = L} {D′ = ⌊ R′ ⌋ m₁} {m = m₁} AB⊢ BC⊢ AC⊢ rel
               (valuesAt m Rs₁)
               (λ y y∈ → cast-out down AB θ (Rs₁⊆ _ (values-∈⁻ Rs₁ y∈))))
fundamental▹ (⊑upR {M = M} {M′} {AB} {BC} {AC} dM AB⊢ BC⊢ AC⊢)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ m ne
  with fundamental▹ dM tok env cρ′ len Rs Rs⊆ m ne
... | W′ , ext , len′ , rel =
  W′ , ext , len′ ,
  ▹-in Ys (s≤s (values-≤ m Rs))
    (▹-mono′ Ys incl
       (upR▹ {L = Ys} {D′ = ⌊ R′ ⌋ m} {m = m} AB⊢ BC⊢ AC⊢
          (▹-out Ys (s≤s (values-≤ m Rs)) rel)))
  where
  R′ = ⟦ M′ ⟧ θ ρ′ n
  Ys = valuesAt m Rs
  incl : ⌊ ⟦ up , BC ⟧ᶜ θ (⌊ R′ ⌋ m) m ⌋ m ⊆ ⌊ R′ ≫= ⟦ up , BC ⟧ᶜ θ ⌋ m
  incl x x∈ =
    inj₂ (m , ▹-conv (suc (sizeᴿᴸ Rs)) (proj₂ (ne-head Ys ne)) rel , x∈)
fundamental▹ (⊑downR {M = M} {M′} {AB} {BC} {AC} dM AB⊢ BC⊢ AC⊢)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ′ len Rs Rs⊆ m ne
  with fundamental▹ dM tok env cρ′ len Rs Rs⊆ m ne
... | W′ , ext , len′ , rel =
  W′ , ext , len′ ,
  ▹-in Ys (s≤s (values-≤ m Rs))
    (▹-mono′ Ys incl
       (downR▹ {L = Ys} {D′ = ⌊ R′ ⌋ m} {m = m} AB⊢ BC⊢ AC⊢
          (▹-out Ys (s≤s (values-≤ m Rs)) rel)))
  where
  R′ = ⟦ M′ ⟧ θ ρ′ n
  Ys = valuesAt m Rs
  incl : ⌊ ⟦ down , BC ⟧ᶜ θ (⌊ R′ ⌋ m) m ⌋ m
         ⊆ ⌊ R′ ≫= ⟦ down , BC ⟧ᶜ θ ⌋ m
  incl x x∈ =
    inj₂ (m , ▹-conv (suc (sizeᴿᴸ Rs)) (proj₂ (ne-head Ys ne)) rel , x∈)

------------------------------------------------------------------------
-- The fundamental lemma, preservation
------------------------------------------------------------------------

list-case : ∀ {A : Set} (X : List A) → X ≡ [] ⊎ Σ[ x ∈ A ] (x ⋵ X)
list-case [] = inj₁ refl
list-case (x ∷ X) = inj₂ (x , here refl)

no-member : ∀ {A : Set} {X : List A} → X ≡ [] → ∀ x → x ⋵ X → ⊥
no-member refl x ()

-- a cast on the left, after the operand's preservation
leftcast◃ : ∀ {θ W H K R Rs′} d AB → Consistentᴿ R
  → (∀ {W′ X Y k} → Consistent X → W′ ∣ θ ⊢ H ⊢ X ◃ Y
       → Lift₁ (err ∈ᴿ ⟦ d , AB ⟧ᶜ θ X k)
         ⊎ W′ ∣ θ ⊢ K ⊢ ⌊ ⟦ d , AB ⟧ᶜ θ X k ⌋ k ◃ Y)
  → W ∣ θ ⊢ H ⊢ R ◃ᶜ Rs′
  → W ∣ θ ⊢ K ⊢ (R ≫= ⟦ d , AB ⟧ᶜ θ) ◃ᶜ Rs′
leftcast◃ {θ} {W} {H} {K} {R} {Rs′} d AB CR castL (inj₁ (lift e)) =
  inj₁ (lift (c-≫=-err {R} {⟦ d , AB ⟧ᶜ θ} e))
leftcast◃ {θ} {W} {H} {K} {R} {Rs′} d AB CR castL (inj₂ (lift ne , h)) =
  finish (decide-ctrs Rs′ step)
  where
  step : ∀ m → valuesAt m Rs′ ≢ []
    → Lift₁ (err ∈ᴿ (R ≫= ⟦ d , AB ⟧ᶜ θ))
      ⊎ Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m)
          × Rel◃ (suc (sizeᴿᴸ Rs′)) W′ θ K
              (⌊ R ≫= ⟦ d , AB ⟧ᶜ θ ⌋ m) (valuesAt m Rs′))
  step m ne₃ with h m ne₃
  step m ne₃ | W′ , ext , len , rel
    with castL {W′} {⌊ R ⌋ m} {valuesAt m Rs′} {m} (⌊⌋-consistent CR m)
           (◃-out (valuesAt m Rs′) (s≤s (values-≤ m Rs′)) rel)
  step m ne₃ | W′ , ext , len , rel | inj₁ (lift e′) =
    inj₁ (lift (c-≫=-group {R} {⟦ d , AB ⟧ᶜ θ} {m} conv err e′))
    where
    conv : Conv (⌊ R ⌋ m)
    conv = ◃-conv (suc (sizeᴿᴸ Rs′))
             (proj₂ (ne-head (valuesAt m Rs′) ne₃)) rel
  step m ne₃ | W′ , ext , len , rel | inj₂ rel′ =
    inj₂ (W′ , ext , len ,
          ◃-in (valuesAt m Rs′) (s≤s (values-≤ m Rs′))
            (◃-mono′ (valuesAt m Rs′)
               (λ x x∈ → c-≫=-group {R} {⟦ d , AB ⟧ᶜ θ} {m} conv (ret x m) x∈)
               rel′))
    where
    conv : Conv (⌊ R ⌋ m)
    conv = ◃-conv (suc (sizeᴿᴸ Rs′))
             (proj₂ (ne-head (valuesAt m Rs′) ne₃)) rel
  finish : Lift₁ (err ∈ᴿ (R ≫= ⟦ d , AB ⟧ᶜ θ))
           ⊎ (∀ m → valuesAt m Rs′ ≢ []
                → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m)
                    × Rel◃ (suc (sizeᴿᴸ Rs′)) W′ θ K
                        (⌊ R ≫= ⟦ d , AB ⟧ᶜ θ ⌋ m) (valuesAt m Rs′)))
    → W ∣ θ ⊢ K ⊢ (R ≫= ⟦ d , AB ⟧ᶜ θ) ◃ᶜ Rs′
  finish (inj₁ e) = inj₁ e
  finish (inj₂ all) = inj₂ (lift ne , all)

fundamental◃ : ∀ {Δ⊑ Γ⊑ M M′ p} → Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p
  → ∀ {θ W ρ ρ′ n} → TOK Δ⊑ θ W → Env◃ Γ⊑ θ W ρ ρ′
  → (∀ x → Consistent (ρ x)) → length W ≡ n
  → ∀ Rs′ → (∀ r → r ⋵ Rs′ → r ∈ᴿ ⟦ M′ ⟧ θ ρ′ n)
  → W ∣ θ ⊢ p ⊢ ⟦ M ⟧ θ ρ n ◃ᶜ Rs′
fundamental◃ (⊑` x∈) tok env cρ len Rs′ Rs⊆ = ret◃ᶜ len Rs⊆ (env x∈)
fundamental◃ (⊑letv {M = M} {M′} {N} {N′} {p} {q} dM dN)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  bind◃ {θ} {θ} {W} {p} {q} {R} {⟦ M′ ⟧ θ ρ′ n}
    {λ E m → ⟦ N ⟧ θ (E • ρ) m} {λ E m → ⟦ N′ ⟧ θ (E • ρ′) m}
    (λ m → ext-fin N′ θ ρ′ m) (λ m → ext-mono N′ θ ρ′ m) CR
    (fundamental◃ dM tok env cρ len) hK Rs′ Rs⊆
  where
  R = ⟦ M ⟧ θ ρ n
  CR : Consistentᴿ R
  CR = ⟦⟧-consistent M θ {ρ} {n} cρ
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L′ → W₁ ∣ θ ⊢ p ⊢ ⌊ R ⌋ m₁ ◃ L′
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ ⟦ N′ ⟧ θ (mem L′ • ρ′) m₁)
    → W₁ ∣ θ ⊢ q ⊢ ⟦ N ⟧ θ (⌊ R ⌋ m₁ • ρ) m₁ ◃ᶜ Rs₁
  hK m₁ W₁ ext₁ len₁ L′ rel Rs₁ Rs₁⊆ =
    fundamental◃ dN (TOK-kripke ext₁ tok)
      (Env◃-ext (λ L₀ L₀⊆ → sub◃ L′ L₀ L₀⊆ rel) (Env◃-kripke ext₁ env))
      (ext-consistent (⌊⌋-consistent CR m₁) cρ) len₁ Rs₁ Rs₁⊆
fundamental◃ (⊑seal {X = X} {M} {M′} {q} X∈ dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  bind◃ {θ} {θ} {W} {q} {‵⊑ (tvar X)} {R} {⟦ M′ ⟧ θ ρ′ n}
    {λ E m → retᴿ (sealᴾ (θ X) E) m} {λ E m → retᴿ (sealᴾ (θ X) E) m}
    (λ m → seal-fin) (λ m → seal-mono) CR
    (fundamental◃ dM tok env cρ len) hK Rs′ Rs⊆
  where
  R = ⟦ M ⟧ θ ρ n
  CR : Consistentᴿ R
  CR = ⟦⟧-consistent M θ {ρ} {n} cρ
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L′ → W₁ ∣ θ ⊢ q ⊢ ⌊ R ⌋ m₁ ◃ L′
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ retᴿ (sealᴾ (θ X) (mem L′)) m₁)
    → W₁ ∣ θ ⊢ ‵⊑ (tvar X) ⊢ retᴿ (sealᴾ (θ X) (⌊ R ⌋ m₁)) m₁ ◃ᶜ Rs₁
  hK m₁ W₁ ext₁ len₁ L′ rel Rs₁ Rs₁⊆ =
    ret◃ᶜ len₁ Rs₁⊆ (seal◃ (tvar X) L′ rel (TOK-kripke ext₁ tok X∈))
fundamental◃ (⊑unseal {X = X} {M} {M′} {q} X∈ dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  bind◃ {θ} {θ} {W} {‵⊑ (tvar X)} {q} {R} {⟦ M′ ⟧ θ ρ′ n}
    {λ E m → retᴿ (unsealᴾ (θ X) E) m} {λ E m → retᴿ (unsealᴾ (θ X) E) m}
    (λ m → unseal-fin) (λ m → unseal-mono) CR
    (fundamental◃ dM tok env cρ len) hK Rs′ Rs⊆
  where
  R = ⟦ M ⟧ θ ρ n
  CR : Consistentᴿ R
  CR = ⟦⟧-consistent M θ {ρ} {n} cρ
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L′ → W₁ ∣ θ ⊢ ‵⊑ (tvar X) ⊢ ⌊ R ⌋ m₁ ◃ L′
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ retᴿ (unsealᴾ (θ X) (mem L′)) m₁)
    → W₁ ∣ θ ⊢ q ⊢ retᴿ (unsealᴾ (θ X) (⌊ R ⌋ m₁)) m₁ ◃ᶜ Rs₁
  hK m₁ W₁ ext₁ len₁ L′ rel Rs₁ Rs₁⊆ =
    ret◃ᶜ len₁ Rs₁⊆
      (λ Ys Ys⊆ →
         sub◃ (unsealᴸ (θ X) L′) Ys (unseal-sub (θ X) L′ Ys Ys⊆)
           (unseal◃ (tvar X) L′ rel (TOK-kripke ext₁ tok X∈)))
fundamental◃ (⊑is {G = G} {M} {M′} wfG dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  bind◃ {θ} {θ} {W} {★⊑} {𝔹⊑} {R} {⟦ M′ ⟧ θ ρ′ n}
    {λ E m → retᴿ (testᴾ (⟦ G ⟧ᴳ θ) E) m}
    {λ E m → retᴿ (testᴾ (⟦ G ⟧ᴳ θ) E) m}
    (λ m → test-fin) (λ m → test-mono) CR
    (fundamental◃ dM tok env cρ len) hK Rs′ Rs⊆
  where
  R = ⟦ M ⟧ θ ρ n
  CR : Consistentᴿ R
  CR = ⟦⟧-consistent M θ {ρ} {n} cρ
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L′ → W₁ ∣ θ ⊢ ★⊑ ⊢ ⌊ R ⌋ m₁ ◃ L′
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ retᴿ (testᴾ (⟦ G ⟧ᴳ θ) (mem L′)) m₁)
    → W₁ ∣ θ ⊢ 𝔹⊑ ⊢ retᴿ (testᴾ (⟦ G ⟧ᴳ θ) (⌊ R ⌋ m₁)) m₁ ◃ᶜ Rs₁
  hK m₁ W₁ ext₁ len₁ L′ rel Rs₁ Rs₁⊆ =
    ret◃ᶜ len₁ Rs₁⊆
      (λ Ys Ys⊆ → bool◃ Ys (λ x x∈ → test◃ L′ rel x) Ys⊆)
fundamental◃ ⊑true tok env cρ len Rs′ Rs⊆ =
  ret◃ᶜ len Rs⊆ (const◃ vtrue true-rel)
fundamental◃ ⊑false tok env cρ len Rs′ Rs⊆ =
  ret◃ᶜ len Rs⊆ (const◃ vfalse false-rel)
fundamental◃ (⊑if {L = L} {L′} {M} {M′} {N} {N′} {q} dL dM dN)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  bind◃ {θ} {θ} {W} {𝔹⊑} {q} {R} {⟦ L′ ⟧ θ ρ′ n}
    {λ E m → condᴿ E (⟦ M ⟧ θ ρ m) (⟦ N ⟧ θ ρ m)}
    {λ E m → condᴿ E (⟦ M′ ⟧ θ ρ′ m) (⟦ N′ ⟧ θ ρ′ m)}
    (λ m → cond-fin) (λ m → cond-mono) CR
    (fundamental◃ dL tok env cρ len) hK Rs′ Rs⊆
  where
  R = ⟦ L ⟧ θ ρ n
  CR : Consistentᴿ R
  CR = ⟦⟧-consistent L θ {ρ} {n} cρ
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ Lb → W₁ ∣ θ ⊢ 𝔹⊑ ⊢ ⌊ R ⌋ m₁ ◃ Lb
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁
                 → r ∈ᴿ condᴿ (mem Lb) (⟦ M′ ⟧ θ ρ′ m₁) (⟦ N′ ⟧ θ ρ′ m₁))
    → W₁ ∣ θ ⊢ q ⊢ condᴿ (⌊ R ⌋ m₁) (⟦ M ⟧ θ ρ m₁) (⟦ N ⟧ θ ρ m₁)
        ◃ᶜ Rs₁
  hK m₁ W₁ ext₁ len₁ Lb rel [] Rs₁⊆ =
    empty◃ᶜ {W₁} {θ} {q}
      {condᴿ (⌊ R ⌋ m₁) (⟦ M ⟧ θ ρ m₁) (⟦ N ⟧ θ ρ m₁)} {[]} (λ r ())
  hK m₁ W₁ ext₁ len₁ Lb rel (r₀ ∷ Rs₁) Rs₁⊆
    with ◃-bool (suc (sizeᴸ Lb)) {W₁} {θ} {⌊ R ⌋ m₁} {Lb}
           (⌊⌋-consistent CR m₁) rel
  hK m₁ W₁ ext₁ len₁ Lb rel (r₀ ∷ Rs₁) Rs₁⊆ | inj₁ allT =
    ◃ᶜ-mono (suc (sizeᴿᴸ (r₀ ∷ Rs₁))) {W₁} {θ} {q}
      {⟦ M ⟧ θ ρ m₁}
      {condᴿ (⌊ R ⌋ m₁) (⟦ M ⟧ θ ρ m₁) (⟦ N ⟧ θ ρ m₁)} {r₀ ∷ Rs₁}
      (λ r r∈ → inj₁ (t∈ , r∈))
      (fundamental◃ dM (TOK-kripke ext₁ tok) (Env◃-kripke ext₁ env) cρ
         len₁ (r₀ ∷ Rs₁) inM)
    where
    inM : ∀ r → r ⋵ (r₀ ∷ Rs₁) → r ∈ᴿ ⟦ M′ ⟧ θ ρ′ m₁
    inM r r∈ with Rs₁⊆ r r∈
    inM r r∈ | inj₁ (t∈′ , r∈′) = r∈′
    inM r r∈ | inj₂ (f∈ , r∈′) with All-lookup allT f∈
    inM r r∈ | inj₂ (f∈ , r∈′) | ()
    t∈ : vtrue ∈ ⌊ R ⌋ m₁
    t∈ with Rs₁⊆ r₀ (here refl)
    t∈ | inj₁ (t∈′ , r∈′) = bool-in◃ Lb vtrue rel t∈′
    t∈ | inj₂ (f∈ , r∈′) with All-lookup allT f∈
    t∈ | inj₂ (f∈ , r∈′) | ()
  hK m₁ W₁ ext₁ len₁ Lb rel (r₀ ∷ Rs₁) Rs₁⊆ | inj₂ allF =
    ◃ᶜ-mono (suc (sizeᴿᴸ (r₀ ∷ Rs₁))) {W₁} {θ} {q}
      {⟦ N ⟧ θ ρ m₁}
      {condᴿ (⌊ R ⌋ m₁) (⟦ M ⟧ θ ρ m₁) (⟦ N ⟧ θ ρ m₁)} {r₀ ∷ Rs₁}
      (λ r r∈ → inj₂ (f∈ , r∈))
      (fundamental◃ dN (TOK-kripke ext₁ tok) (Env◃-kripke ext₁ env) cρ
         len₁ (r₀ ∷ Rs₁) inN)
    where
    inN : ∀ r → r ⋵ (r₀ ∷ Rs₁) → r ∈ᴿ ⟦ N′ ⟧ θ ρ′ m₁
    inN r r∈ with Rs₁⊆ r r∈
    inN r r∈ | inj₂ (f∈′ , r∈′) = r∈′
    inN r r∈ | inj₁ (t∈ , r∈′) with All-lookup allF t∈
    inN r r∈ | inj₁ (t∈ , r∈′) | ()
    f∈ : vfalse ∈ ⌊ R ⌋ m₁
    f∈ with Rs₁⊆ r₀ (here refl)
    f∈ | inj₂ (f∈′ , r∈′) = bool-in◃ Lb vfalse rel f∈′
    f∈ | inj₁ (t∈ , r∈′) with All-lookup allF t∈
    f∈ | inj₁ (t∈ , r∈′) | ()
fundamental◃ (⊑ƛ {A = A} {A′} {M} {M′} {p} {q} p⊢ dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  ret◃ᶜ len Rs⊆ lam
  where
  F : 𝒱 → ℕ → ℛ
  F E m = ⟦ M ⟧ θ (E • ρ) m
  F′ : 𝒱 → ℕ → ℛ
  F′ E m = ⟦ M′ ⟧ θ (E • ρ′) m
  lam : ∀ Ys → mem Ys ⊆ Λ F′ → W ∣ θ ⊢ p ⇒⊑ q ⊢ Λ F ◃ Ys
  lam [] Ys⊆ = tt₁
  lam (y ∷ Ys) Ys⊆ =
    lift (All-tab (y ∷ Ys) (λ x x∈ → Λ-IsFun {F = F′} x (Ys⊆ x x∈))) ,
    lift tt , g
    where
    g : ∀ L₀ → L₀ ⊑ˢ (y ∷ Ys) → ∀ m′ W′ → W ⊑ʷ W′ → length W′ ≡ m′
      → ∀ E → Consistent E
      → Rel◃ (sizeᴸ (y ∷ Ys)) W′ θ p E (argsAt m′ L₀)
      → Rel◃ᶜ (sizeᴸ (y ∷ Ys)) W′ θ q (Λ F ●[ m′ ] E) (resultsAt m′ L₀)
    g L₀ s m′ W′ ext len′ E CE relA with list-case (resultsAt m′ L₀)
    g L₀ s m′ W′ ext len′ E CE relA | inj₁ eq =
      ◃ᶜ-fuel (suc (sizeᴿᴸ (resultsAt m′ L₀))) (sizeᴸ (y ∷ Ys))
        {W′} {θ} {q} {Λ F ●[ m′ ] E} {resultsAt m′ L₀}
        ≤-refl (results-sub-< m′ y Ys s)
        (empty◃ᶜ {W′} {θ} {q} {Λ F ●[ m′ ] E} {resultsAt m′ L₀}
           (no-member eq))
    g L₀ s m′ W′ ext len′ E CE relA | inj₂ (r₀ , r₀∈) =
      ◃ᶜ-mono (sizeᴸ (y ∷ Ys)) {W′} {θ} {q} {⟦ M ⟧ θ (E • ρ) m′}
        {Λ F ●[ m′ ] E} {Rs₀} (Λ-β M θ ρ CE cE)
        (◃ᶜ-fuel (suc (sizeᴿᴸ Rs₀)) (sizeᴸ (y ∷ Ys))
           {W′} {θ} {q} {⟦ M ⟧ θ (E • ρ) m′} {Rs₀}
           ≤-refl (results-sub-< m′ y Ys s) IH)
      where
      A₀ = argsAt m′ L₀
      Rs₀ = resultsAt m′ L₀
      relA′ : W′ ∣ θ ⊢ p ⊢ E ◃ A₀
      relA′ = ◃-out A₀ (args-sub-< m′ y Ys s) relA
      in₀ : ∀ r → r ⋵ Rs₀ → r ∈ᴿ ⟦ M′ ⟧ θ (mem A₀ • ρ′) m′
      in₀ r r∈ with results-∈⁻ L₀ r∈
      in₀ r r∈ | U , e∈ with Ys⊆ _ (sub-mem s _ e∈)
      in₀ r r∈ | U , e∈ | r∈′ , U≢ , U≈ =
        ⟦⟧-mono M′ (ext-⊆ₑ (λ u u∈ → args-∈⁺ e∈ u∈) ⊆ₑ-refl) r r∈′
      IH : W′ ∣ θ ⊢ q ⊢ ⟦ M ⟧ θ (E • ρ) m′ ◃ᶜ Rs₀
      IH = fundamental◃ dM (TOK-kripke ext tok)
             (Env◃-ext (λ L L⊆ → sub◃ A₀ L L⊆ relA′) (Env◃-kripke ext env))
             (ext-consistent CE cρ) len′ Rs₀ in₀
      cE : Conv E
      cE with results-∈⁻ L₀ r₀∈
      cE | U , e∈ with Ys⊆ _ (sub-mem s _ e∈)
      cE | [] , e∈ | r∈′ , U≢ , U≈ = ⊥-elim (U≢ refl)
      cE | (u ∷ U) , e∈ | r∈′ , U≢ , U≈ =
        ◃-conv (sizeᴸ (y ∷ Ys)) (args-∈⁺ e∈ (here refl)) relA
fundamental◃ (⊑· {L = L} {L′} {M} {M′} {p} {q} dL dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  bind◃ {θ} {θ} {W} {p ⇒⊑ q} {q} {R} {⟦ L′ ⟧ θ ρ′ n} {K} {K′}
    (λ n₁ → c-≫=-finK {R = ⟦ M′ ⟧ θ ρ′ n₁} {K = λ F E n₂ → F ●[ n₂ ] E}
              (λ E n₂ → c-●ˡ-fin {E} {n₂}))
    (λ n₁ → c-≫=-monoK {R = ⟦ M′ ⟧ θ ρ′ n₁} {K = λ F E n₂ → F ●[ n₂ ] E}
              (λ E n₂ → c-●ˡ-mono {E} {n₂}))
    CR (fundamental◃ dL tok env cρ len) hK Rs′ Rs⊆
  where
  R = ⟦ L ⟧ θ ρ n
  CR : Consistentᴿ R
  CR = ⟦⟧-consistent L θ {ρ} {n} cρ
  K : 𝒱 → ℕ → ℛ
  K F n₁ = ⟦ M ⟧ θ ρ n₁ ≫= λ E n₂ → F ●[ n₂ ] E
  K′ : 𝒱 → ℕ → ℛ
  K′ F n₁ = ⟦ M′ ⟧ θ ρ′ n₁ ≫= λ E n₂ → F ●[ n₂ ] E
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ Lf′ → W₁ ∣ θ ⊢ p ⇒⊑ q ⊢ ⌊ R ⌋ m₁ ◃ Lf′
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ K′ (mem Lf′) m₁)
    → W₁ ∣ θ ⊢ q ⊢ K (⌊ R ⌋ m₁) m₁ ◃ᶜ Rs₁
  hK m₁ W₁ ext₁ len₁ Lf′ relF Rs₁ Rs₁⊆ =
    bind◃ {θ} {θ} {W₁} {p} {q} {⟦ M ⟧ θ ρ m₁} {⟦ M′ ⟧ θ ρ′ m₁}
      {λ E n₂ → ⌊ R ⌋ m₁ ●[ n₂ ] E} {λ E n₂ → mem Lf′ ●[ n₂ ] E}
      (λ n₂ → c-●ʳ-fin {mem Lf′} {n₂}) (λ n₂ → c-●ʳ-mono {mem Lf′} {n₂})
      CM
      (fundamental◃ dM (TOK-kripke ext₁ tok) (Env◃-kripke ext₁ env) cρ
         len₁)
      hK₂ Rs₁ Rs₁⊆
    where
    CM : Consistentᴿ (⟦ M ⟧ θ ρ m₁)
    CM = ⟦⟧-consistent M θ {ρ} {m₁} cρ
    hK₂ : ∀ m₂ W₂ → W₁ ⊑ʷ W₂ → length W₂ ≡ m₂
      → ∀ La′ → W₂ ∣ θ ⊢ p ⊢ ⌊ ⟦ M ⟧ θ ρ m₁ ⌋ m₂ ◃ La′
      → ∀ Rs₂ → (∀ r → r ⋵ Rs₂ → r ∈ᴿ (mem Lf′ ●[ m₂ ] mem La′))
      → W₂ ∣ θ ⊢ q ⊢ (⌊ R ⌋ m₁ ●[ m₂ ] ⌊ ⟦ M ⟧ θ ρ m₁ ⌋ m₂) ◃ᶜ Rs₂
    hK₂ m₂ W₂ ext₂ len₂ La′ relA Rs₂ Rs₂⊆ =
      app◃ {θ} {W₂} {p} {q} {⌊ R ⌋ m₁} {Lf′} {⌊ ⟦ M ⟧ θ ρ m₁ ⌋ m₂}
        {mem La′} {m₂}
        (kripke◃ Lf′ ext₂ relF) len₂ (⌊⌋-consistent CM m₂)
        (λ La″ La″⊆ → sub◃ La′ La″ La″⊆ relA) Rs₂ Rs₂⊆
fundamental◃ (⊑Λν {M = M} {M′} {p} dM)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  ret◃ᶜ len Rs⊆ poly
  where
  F : Seal → ℛ
  F σ = ⟦ M ⟧ (σ •ᵗ θ) ρ (suc σ)
  F′ : Seal → ℛ
  F′ σ = ⟦ M′ ⟧ (σ •ᵗ θ) ρ′ (suc σ)
  poly : ∀ Ys → mem Ys ⊆ Λᴾ F′ → W ∣ θ ⊢ ∀⊑ p ⊢ Λᴾ F ◃ Ys
  poly [] Ys⊆ = tt₁
  poly (y ∷ Ys) Ys⊆ =
    lift (All-tab (y ∷ Ys) (λ x x∈ → Λᴾ-IsPoly {F = F′} x (Ys⊆ x x∈))) ,
    lift tt , g
    where
    g : ∀ σ W′ q′ → W ⊑ʷ W′ → length W′ ≡ σ
      → Rel◃ᶜ (sizeᴸ (y ∷ Ys)) (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) p (Λᴾ F ◆ σ)
          (bodiesAt σ (y ∷ Ys))
    g σ W′ q′ ext len′ =
      ◃ᶜ-fuel (suc (sizeᴿᴸ B)) (sizeᴸ (y ∷ Ys))
        {W′ ++ (q′ ∷ [])} {σ •ᵗ θ} {p} {Λᴾ F ◆ σ} {B}
        ≤-refl (bodies-< σ y Ys)
        (fundamental◃ dM
           (TOK-kripke ext′ (TOK-abs {σ = σ} tok))
           (Env◃-kripke ext′ (Env◃-⤊ {σ = σ} env)) cρ
           (trans (length-++1 W′ q′) (cong suc len′)) B B⊆)
      where
      B = bodiesAt σ (y ∷ Ys)
      ext′ : W ⊑ʷ (W′ ++ (q′ ∷ []))
      ext′ = ⊑ʷ-trans ext (q′ ∷ [] , refl)
      B⊆ : ∀ r → r ⋵ B → r ∈ᴿ F′ σ
      B⊆ r r∈ = Ys⊆ _ (bodies-∈⁻ (y ∷ Ys) r∈)
fundamental◃ (⊑inst {M = M} {M′} {B} {B′} {N} {N′} {p} {q} {r} dM q⊢ dN)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  bind◃ {θ} {θ} {W} {∀⊑ p} {r} {R} {⟦ M′ ⟧ θ ρ′ n} {K} {K′}
    (λ n₁ → c-≫=-fin {Φ = λ F → F ◆ n₁}
              {K = λ E n₂ → ⟦ N′ ⟧ (n₁ •ᵗ θ) (E • ρ′) n₂}
              (c-◆-fin {n₁}) (c-◆-mono {n₁})
              (λ n₂ → ext-fin N′ (n₁ •ᵗ θ) ρ′ n₂)
              (λ n₂ → ext-mono N′ (n₁ •ᵗ θ) ρ′ n₂))
    (λ n₁ → c-≫=-monoR {Φ = λ F → F ◆ n₁}
              {K = λ E n₂ → ⟦ N′ ⟧ (n₁ •ᵗ θ) (E • ρ′) n₂}
              (c-◆-mono {n₁}) (λ n₂ → ext-mono N′ (n₁ •ᵗ θ) ρ′ n₂))
    CR (fundamental◃ dM tok env cρ len) hK Rs′ Rs⊆
  where
  R = ⟦ M ⟧ θ ρ n
  CR : Consistentᴿ R
  CR = ⟦⟧-consistent M θ {ρ} {n} cρ
  K : 𝒱 → ℕ → ℛ
  K F n₁ = (F ◆ n₁) ≫= λ E n₂ → ⟦ N ⟧ (n₁ •ᵗ θ) (E • ρ) n₂
  K′ : 𝒱 → ℕ → ℛ
  K′ F n₁ = (F ◆ n₁) ≫= λ E n₂ → ⟦ N′ ⟧ (n₁ •ᵗ θ) (E • ρ′) n₂
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ Lf′ → W₁ ∣ θ ⊢ ∀⊑ p ⊢ ⌊ R ⌋ m₁ ◃ Lf′
    → ∀ Rs₁ → (∀ r₁ → r₁ ⋵ Rs₁ → r₁ ∈ᴿ K′ (mem Lf′) m₁)
    → W₁ ∣ θ ⊢ r ⊢ K (⌊ R ⌋ m₁) m₁ ◃ᶜ Rs₁
  hK .(length W₁) W₁ ext₁ refl [] relF Rs₁ Rs₁⊆ =
    empty◃ᶜ {W₁} {θ} {r} {K (⌊ R ⌋ (length W₁)) (length W₁)} {Rs₁}
      (λ r₁ r₁∈ → none (Rs₁⊆ r₁ r₁∈))
    where
    none : ∀ {r₁} → r₁ ∈ᴿ K′ (mem []) (length W₁) → ⊥
    none (inj₁ (eq , ()))
    none (inj₂ (m₂ , (c , ()) , r∈))
  hK .(length W₁) W₁ ext₁ refl (v ∷ Lf) (all , ν∈ , f) Rs₁ Rs₁⊆ =
    ◃ᶜ-weaken {suc (sizeᴿᴸ Rs₁)} {W₁} {W₂} {θ} {r} {K D m₁} {Rs₁}
      (q′ ∷ [] , refl)
      (to (◃ᶜ-subst (suc (sizeᴿᴸ Rs₁)) {θ} {θ₂} {↑ₙ} {W₂} {r}
             {K D m₁} {Rs₁} (λ i → refl))
        inner)
    where
    m₁ = length W₁
    θ₂ = m₁ •ᵗ θ
    q′ = ⟦ q ⟧ᵖ θ
    W₂ = W₁ ++ (q′ ∷ [])
    D = ⌊ R ⌋ m₁
    hB : Rel◃ᶜ (sizeᴸ (v ∷ Lf)) W₂ θ₂ p (D ◆ m₁) (bodiesAt m₁ (v ∷ Lf))
    hB = f m₁ W₁ q′ ⊑ʷ-refl refl
    hR₂ : ∀ Rs₂ → (∀ r₂ → r₂ ⋵ Rs₂ → r₂ ∈ᴿ (mem (v ∷ Lf) ◆ m₁))
      → W₂ ∣ θ₂ ⊢ p ⊢ (D ◆ m₁) ◃ᶜ Rs₂
    hR₂ Rs₂ Rs₂⊆ =
      ◃ᶜ-⊆ (sizeᴸ (v ∷ Lf)) (sizeᴸ (v ∷ Lf)) (suc (sizeᴿᴸ Rs₂))
        {W₂} {θ₂} {p} {D ◆ m₁} {bodiesAt m₁ (v ∷ Lf)} {Rs₂}
        (bodies-bound (v ∷ Lf) (size-bound (v ∷ Lf)))
        (bodies-< m₁ v Lf) ≤-refl
        (λ r₂ r₂∈ → bodies-∈⁺ (Rs₂⊆ r₂ r₂∈)) hB
    CD : Consistentᴿ (D ◆ m₁)
    CD = ◆-consistent {σ = m₁} (⌊⌋-consistent CR m₁)
    hK₂ : ∀ m₂ W₃ → W₂ ⊑ʷ W₃ → length W₃ ≡ m₂
      → ∀ La′ → W₃ ∣ θ₂ ⊢ p ⊢ ⌊ D ◆ m₁ ⌋ m₂ ◃ La′
      → ∀ Rs₂ → (∀ r₂ → r₂ ⋵ Rs₂ → r₂ ∈ᴿ ⟦ N′ ⟧ θ₂ (mem La′ • ρ′) m₂)
      → W₃ ∣ θ₂ ⊢ ⇑ᵖ r ⊢ ⟦ N ⟧ θ₂ (⌊ D ◆ m₁ ⌋ m₂ • ρ) m₂ ◃ᶜ Rs₂
    hK₂ m₂ W₃ ext₃ len₃ La′ relA Rs₂ Rs₂⊆ =
      fundamental◃ dN
        (TOK-known {q = q} (TOK-kripke ext₁ tok) ext₃)
        (Env◃-ext (λ L₀ L₀⊆ → sub◃ La′ L₀ L₀⊆ relA)
           (Env◃-⤊ {σ = m₁}
              (Env◃-kripke (⊑ʷ-trans ext₁ (⊑ʷ-trans (q′ ∷ [] , refl) ext₃))
                 env)))
        (ext-consistent (⌊⌋-consistent CD m₂) cρ) len₃ Rs₂ Rs₂⊆
    inner : W₂ ∣ θ₂ ⊢ ⇑ᵖ r ⊢ K D m₁ ◃ᶜ Rs₁
    inner =
      bind◃ {θ₂} {θ₂} {W₂} {p} {⇑ᵖ r} {D ◆ m₁} {mem (v ∷ Lf) ◆ m₁}
        {λ E n₂ → ⟦ N ⟧ θ₂ (E • ρ) n₂} {λ E n₂ → ⟦ N′ ⟧ θ₂ (E • ρ′) n₂}
        (λ n₂ → ext-fin N′ θ₂ ρ′ n₂) (λ n₂ → ext-mono N′ θ₂ ρ′ n₂) CD
        hR₂ hK₂ Rs₁ Rs₁⊆
fundamental◃ (⊑upL {M = M} {M′} {AB} {BC} {AC} dM AB⊢ BC⊢ AC⊢)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  leftcast◃ {θ} {W} {AC} {BC} {⟦ M ⟧ θ ρ n} {Rs′} up AB
    (⟦⟧-consistent M θ {ρ} {n} cρ)
    (λ {W′} {X} {Y} {k} CX r →
       upL◃ {θ = θ} {W′} {E = X} {L′ = Y} {k} AB⊢ BC⊢ AC⊢ CX r)
    (fundamental◃ dM tok env cρ len Rs′ Rs⊆)
fundamental◃ (⊑downL {M = M} {M′} {AB} {BC} {AC} dM AB⊢ BC⊢ AC⊢)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  leftcast◃ {θ} {W} {BC} {AC} {⟦ M ⟧ θ ρ n} {Rs′} down AB
    (⟦⟧-consistent M θ {ρ} {n} cρ)
    (λ {W′} {X} {Y} {k} CX r →
       downL◃ {θ = θ} {W′} {E = X} {L′ = Y} {k} AB⊢ BC⊢ AC⊢ CX r)
    (fundamental◃ dM tok env cρ len Rs′ Rs⊆)
fundamental◃ (⊑upR {M = M} {M′} {AB} {BC} {AC} dM AB⊢ BC⊢ AC⊢)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  ◃ᶜ-mono (suc (sizeᴿᴸ Rs′)) {W} {θ} {AC}
    {R ≫= λ D m → retᴿ D m} {R} {Rs′} (≫=-ret⊆ {R})
    (bind◃ {θ} {θ} {W} {AB} {AC} {R} {⟦ M′ ⟧ θ ρ′ n}
       {λ D m → retᴿ D m} {⟦ up , BC ⟧ᶜ θ}
       (c-fin up BC θ) (c-mono up BC θ) CR
       (fundamental◃ dM tok env cρ len) hK Rs′ Rs⊆)
  where
  R = ⟦ M ⟧ θ ρ n
  CR : Consistentᴿ R
  CR = ⟦⟧-consistent M θ {ρ} {n} cρ
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L′ → W₁ ∣ θ ⊢ AB ⊢ ⌊ R ⌋ m₁ ◃ L′
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ ⟦ up , BC ⟧ᶜ θ (mem L′) m₁)
    → W₁ ∣ θ ⊢ AC ⊢ retᴿ (⌊ R ⌋ m₁) m₁ ◃ᶜ Rs₁
  hK m₁ W₁ ext₁ len₁ L′ rel Rs₁ Rs₁⊆ =
    val◃ᶜ len₁ (λ e∈ → proj₁ C (Rs₁⊆ err e∈))
      (λ v m r∈ → c-ctr up BC θ (Rs₁⊆ _ r∈))
      (λ m → proj₂ C (valuesAt m Rs₁)
               (λ y y∈ → cast-out up BC θ (Rs₁⊆ _ (values-∈⁻ Rs₁ y∈))))
    where
    C = upR◃ {θ = θ} {W₁} {D = ⌊ R ⌋ m₁} {L′ = L′} {m₁} AB⊢ BC⊢ AC⊢ rel
fundamental◃ (⊑downR {M = M} {M′} {AB} {BC} {AC} dM AB⊢ BC⊢ AC⊢)
    {θ} {W} {ρ} {ρ′} {n} tok env cρ len Rs′ Rs⊆ =
  ◃ᶜ-mono (suc (sizeᴿᴸ Rs′)) {W} {θ} {AB}
    {R ≫= λ D m → retᴿ D m} {R} {Rs′} (≫=-ret⊆ {R})
    (bind◃ {θ} {θ} {W} {AC} {AB} {R} {⟦ M′ ⟧ θ ρ′ n}
       {λ D m → retᴿ D m} {⟦ down , BC ⟧ᶜ θ}
       (c-fin down BC θ) (c-mono down BC θ) CR
       (fundamental◃ dM tok env cρ len) hK Rs′ Rs⊆)
  where
  R = ⟦ M ⟧ θ ρ n
  CR : Consistentᴿ R
  CR = ⟦⟧-consistent M θ {ρ} {n} cρ
  hK : ∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
    → ∀ L′ → W₁ ∣ θ ⊢ AC ⊢ ⌊ R ⌋ m₁ ◃ L′
    → ∀ Rs₁ → (∀ r → r ⋵ Rs₁ → r ∈ᴿ ⟦ down , BC ⟧ᶜ θ (mem L′) m₁)
    → W₁ ∣ θ ⊢ AB ⊢ retᴿ (⌊ R ⌋ m₁) m₁ ◃ᶜ Rs₁
  hK m₁ W₁ ext₁ len₁ L′ rel Rs₁ Rs₁⊆ =
    val◃ᶜ len₁ (λ e∈ → proj₁ C (Rs₁⊆ err e∈))
      (λ v m r∈ → c-ctr down BC θ (Rs₁⊆ _ r∈))
      (λ m → proj₂ C (valuesAt m Rs₁)
               (λ y y∈ → cast-out down BC θ (Rs₁⊆ _ (values-∈⁻ Rs₁ y∈))))
    where
    C = downR◃ {θ = θ} {W₁} {D = ⌊ R ⌋ m₁} {L′ = L′} {m₁} AB⊢ BC⊢ AC⊢ rel
