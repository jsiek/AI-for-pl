module proof.DenotAdequacy where

-- File Charter:
--   * Adequacy of the graph-model denotation (Denotation) for the cast
--     calculus's reduction: an element of the denotation of a closed term
--     that is a value is reached by reduction to a syntactic value with the
--     same observation, and ω is reached by reduction to blame.
--   * Proved with a logical relation 𝕍 between denotational elements and
--     syntactic values, by recursion on the element, and a fundamental
--     property under a closing substitution.  Determinism of reduction
--     (proof/CastDeterminism.agda) gives the elements of an argument set one
--     common syntactic value.
--   * Also holds the substitution lemmas (composition and identity) that the
--     β case needs.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Types
open import Coercions
open import CastCalculus
open import GraphModel
open import Denotation
open import DynamicGradualGuaranteeDefinitions
  using (Observation; nat-obs; fun-obs; observe)
open import proof.CastDeterminism using (—↠-value-unique)

------------------------------------------------------------------------
-- Substitution lemmas
------------------------------------------------------------------------

ext-cong : ∀ {r r′ : Renameᶜ}
  → (∀ x → r x ≡ r′ x)
  → ∀ x → extᶜ r x ≡ extᶜ r′ x
ext-cong eq zero = refl
ext-cong eq (suc x) = cong suc (eq x)

rename-cong : ∀ {r r′ : Renameᶜ} M
  → (∀ x → r x ≡ r′ x)
  → renameᶜ r M ≡ renameᶜ r′ M
rename-cong (` x) eq = cong `_ (eq x)
rename-cong ($ n) eq = refl
rename-cong (ƛ A ⇒ N) eq =
  cong (λ N′ → ƛ A ⇒ N′) (rename-cong N (ext-cong eq))
rename-cong (L · M) eq = cong₂ _·_ (rename-cong L eq) (rename-cong M eq)
rename-cong (cast M [ c ]) eq = cong (cast_[ c ]) (rename-cong M eq)
rename-cong blame eq = refl

exts-cong : ∀ {σ τ : Substᶜ}
  → (∀ x → σ x ≡ τ x)
  → ∀ x → extsᶜ σ x ≡ extsᶜ τ x
exts-cong eq zero = refl
exts-cong eq (suc x) = cong (renameᶜ suc) (eq x)

subst-cong : ∀ {σ τ : Substᶜ} M
  → (∀ x → σ x ≡ τ x)
  → substᶜ σ M ≡ substᶜ τ M
subst-cong (` x) eq = eq x
subst-cong ($ n) eq = refl
subst-cong (ƛ A ⇒ N) eq =
  cong (λ N′ → ƛ A ⇒ N′) (subst-cong N (exts-cong eq))
subst-cong (L · M) eq = cong₂ _·_ (subst-cong L eq) (subst-cong M eq)
subst-cong (cast M [ c ]) eq = cong (cast_[ c ]) (subst-cong M eq)
subst-cong blame eq = refl

rename-rename : ∀ (r r′ : Renameᶜ) M
  → renameᶜ r (renameᶜ r′ M) ≡ renameᶜ (λ x → r (r′ x)) M
rename-rename r r′ (` x) = refl
rename-rename r r′ ($ n) = refl
rename-rename r r′ (ƛ A ⇒ N) =
  cong (λ N′ → ƛ A ⇒ N′)
    (trans (rename-rename (extᶜ r) (extᶜ r′) N) (rename-cong N ext-ext))
  where
  ext-ext : ∀ x → extᶜ r (extᶜ r′ x) ≡ extᶜ (λ y → r (r′ y)) x
  ext-ext zero = refl
  ext-ext (suc x) = refl
rename-rename r r′ (L · M) =
  cong₂ _·_ (rename-rename r r′ L) (rename-rename r r′ M)
rename-rename r r′ (cast M [ c ]) = cong (cast_[ c ]) (rename-rename r r′ M)
rename-rename r r′ blame = refl

subst-rename : ∀ (τ : Substᶜ) (r : Renameᶜ) M
  → substᶜ τ (renameᶜ r M) ≡ substᶜ (λ x → τ (r x)) M
subst-rename τ r (` x) = refl
subst-rename τ r ($ n) = refl
subst-rename τ r (ƛ A ⇒ N) =
  cong (λ N′ → ƛ A ⇒ N′)
    (trans (subst-rename (extsᶜ τ) (extᶜ r) N) (subst-cong N exts-ext))
  where
  exts-ext : ∀ x → extsᶜ τ (extᶜ r x) ≡ extsᶜ (λ y → τ (r y)) x
  exts-ext zero = refl
  exts-ext (suc x) = refl
subst-rename τ r (L · M) =
  cong₂ _·_ (subst-rename τ r L) (subst-rename τ r M)
subst-rename τ r (cast M [ c ]) = cong (cast_[ c ]) (subst-rename τ r M)
subst-rename τ r blame = refl

rename-subst : ∀ (r : Renameᶜ) (τ : Substᶜ) M
  → renameᶜ r (substᶜ τ M) ≡ substᶜ (λ x → renameᶜ r (τ x)) M
rename-subst r τ (` x) = refl
rename-subst r τ ($ n) = refl
rename-subst r τ (ƛ A ⇒ N) =
  cong (λ N′ → ƛ A ⇒ N′)
    (trans (rename-subst (extᶜ r) (extsᶜ τ) N) (subst-cong N ext-exts))
  where
  ext-exts : ∀ x
    → renameᶜ (extᶜ r) (extsᶜ τ x) ≡ extsᶜ (λ y → renameᶜ r (τ y)) x
  ext-exts zero = refl
  ext-exts (suc x) =
    trans (rename-rename (extᶜ r) suc (τ x))
          (sym (rename-rename suc r (τ x)))
rename-subst r τ (L · M) =
  cong₂ _·_ (rename-subst r τ L) (rename-subst r τ M)
rename-subst r τ (cast M [ c ]) = cong (cast_[ c ]) (rename-subst r τ M)
rename-subst r τ blame = refl

subst-subst : ∀ (τ σ : Substᶜ) M
  → substᶜ τ (substᶜ σ M) ≡ substᶜ (λ x → substᶜ τ (σ x)) M
subst-subst τ σ (` x) = refl
subst-subst τ σ ($ n) = refl
subst-subst τ σ (ƛ A ⇒ N) =
  cong (λ N′ → ƛ A ⇒ N′)
    (trans (subst-subst (extsᶜ τ) (extsᶜ σ) N) (subst-cong N exts-exts))
  where
  exts-exts : ∀ x
    → substᶜ (extsᶜ τ) (extsᶜ σ x) ≡ extsᶜ (λ y → substᶜ τ (σ y)) x
  exts-exts zero = refl
  exts-exts (suc x) =
    trans (subst-rename (extsᶜ τ) suc (σ x))
          (sym (rename-subst suc τ (σ x)))
subst-subst τ σ (L · M) =
  cong₂ _·_ (subst-subst τ σ L) (subst-subst τ σ M)
subst-subst τ σ (cast M [ c ]) = cong (cast_[ c ]) (subst-subst τ σ M)
subst-subst τ σ blame = refl

subst-id : ∀ M → substᶜ `_ M ≡ M
subst-id (` x) = refl
subst-id ($ n) = refl
subst-id (ƛ A ⇒ N) =
  cong (λ N′ → ƛ A ⇒ N′) (trans (subst-cong N exts-id) (subst-id N))
  where
  exts-id : ∀ x → extsᶜ `_ x ≡ ` x
  exts-id zero = refl
  exts-id (suc x) = refl
subst-id (L · M) = cong₂ _·_ (subst-id L) (subst-id M)
subst-id (cast M [ c ]) = cong (cast_[ c ]) (subst-id M)
subst-id blame = refl

infixr 5 _•ˢ_

_•ˢ_ : Termᶜ → Substᶜ → Substᶜ
(W •ˢ σ) zero = W
(W •ˢ σ) (suc x) = σ x

subst-β : ∀ (σ : Substᶜ) W N
  → (substᶜ (extsᶜ σ) N) [ W ]ᶜ ≡ substᶜ (W •ˢ σ) N
subst-β σ W N =
  trans (subst-subst (singleEnvᶜ W) (extsᶜ σ) N) (subst-cong N single-exts)
  where
  single-exts : ∀ x
    → substᶜ (singleEnvᶜ W) (extsᶜ σ x) ≡ (W •ˢ σ) x
  single-exts zero = refl
  single-exts (suc x) =
    trans (subst-rename (singleEnvᶜ W) suc (σ x)) (subst-id (σ x))

------------------------------------------------------------------------
-- The logical relation
------------------------------------------------------------------------

-- V is a function value
FunVal : Termᶜ → Set
FunVal V =
  (Σ[ A ∈ Ty ] Σ[ N ∈ Termᶜ ] (V ≡ ƛ A ⇒ N))
  ⊎ (Σ[ W ∈ Termᶜ ] Σ[ c ∈ Coercion ] Σ[ d ∈ Coercion ]
       (V ≡ cast W [ c ↦ d ] × Valueᶜ W))

mutual
  𝕍 : Val → Termᶜ → Set
  𝕍 (nat n) V = V ≡ $ n
  𝕍 (U ⟼ w) V =
    FunVal V × (∀ W → Valueᶜ W → 𝕍* U W → 𝔼 w (V · W))
  𝕍 ν V = FunVal V
  𝕍 ω V = ⊥
  𝕍 (tag t d) V =
    Σ[ W ∈ Termᶜ ] (V ≡ cast W [ tagTy t ! ] × Valueᶜ W × 𝕍 d W)

  𝕍* : List Val → Termᶜ → Set
  𝕍* [] W = ⊤
  𝕍* (u ∷ U) W = 𝕍 u W × 𝕍* U W

  𝔼 : Val → Termᶜ → Set
  𝔼 d M =
    (d ≡ ω → Σ[ ℓ ∈ Nat ] (M —↠ blame {ℓ = ℓ}))
    × (d ≢ ω → Σ[ W ∈ Termᶜ ] (Valueᶜ W × M —↠ W × 𝕍 d W))

-- the relation on environments and closing substitutions
𝔾 : Env → Substᶜ → Set
𝔾 ρ σ = ∀ x d → d ∈ ρ x → 𝕍 d (σ x)

------------------------------------------------------------------------
-- Properties of the relation
------------------------------------------------------------------------

FunVal→value : ∀ {V} → FunVal V → Valueᶜ V
FunVal→value (inj₁ (A , N , refl)) = V-ƛ
FunVal→value (inj₂ (W , c , d , refl , vW)) = V-cast↦ vW

𝕍→value : ∀ d {V} → 𝕍 d V → Valueᶜ V
𝕍→value (nat n) refl = V-$
𝕍→value (U ⟼ w) (fv , app) = FunVal→value fv
𝕍→value ν fv = FunVal→value fv
𝕍→value ω ()
𝕍→value (tag t d) (W , refl , vW , rel) = V-cast! vW

𝕍≢ω : ∀ d {V} → 𝕍 d V → d ≢ ω
𝕍≢ω (nat n) rel ()
𝕍≢ω (U ⟼ w) rel ()
𝕍≢ω ν rel ()
𝕍≢ω ω ()
𝕍≢ω (tag t d) rel ()

𝕍→𝔼 : ∀ d {V} → 𝕍 d V → 𝔼 d V
𝕍→𝔼 d {V} rel =
  (λ d≡ω → ⊥-elim (𝕍≢ω d rel d≡ω))
  , (λ d≢ω → V , 𝕍→value d rel , (V ∎) , rel)

𝔼ω : ∀ {M ℓ} → M —↠ blame {ℓ = ℓ} → 𝔼 ω M
𝔼ω {ℓ = ℓ} M—↠blame = (λ ω≡ω → ℓ , M—↠blame) , (λ ω≢ω → ⊥-elim (ω≢ω refl))

expand : ∀ {d M M′} → M —↠ M′ → 𝔼 d M′ → 𝔼 d M
expand M—↠M′ (blames , values) =
  (λ d≡ω → let ℓ , r = blames d≡ω in ℓ , (M—↠M′ ++ᶜ r))
  , (λ d≢ω → let W , vW , r , rel = values d≢ω in
               W , vW , (M—↠M′ ++ᶜ r) , rel)

step : ∀ {M N} → M —→ N → M —↠ N
step {M} {N} M—→N = M —→⟨ M—→N ⟩ (N ∎)

blame-frame : ∀ F {M ℓ}
  → M —↠ blame {ℓ = ℓ}
  → plug F M —↠ blame {ℓ = ℓ}
blame-frame F M—↠blame = ξ* F M—↠blame ++ᶜ step (ξ-blame F)

𝕍*-∋ : ∀ {U W u} → 𝕍* U W → u ⋵ U → 𝕍 u W
𝕍*-∋ (rel , rels) (here refl) = rel
𝕍*-∋ (rel , rels) (there u∈) = 𝕍*-∋ rels u∈

𝕍*-from : ∀ U {W} → (∀ u → u ⋵ U → 𝕍 u W) → 𝕍* U W
𝕍*-from [] h = tt
𝕍*-from (u ∷ U) h = h u (here refl) , 𝕍*-from U (λ u′ u′∈ → h u′ (there u′∈))

-- All the values of D are related to one syntactic value, by determinism.
common : ∀ {M D x₀}
  → x₀ ∈ D
  → x₀ ≢ ω
  → (∀ x → x ∈ D → 𝔼 x M)
  → Σ[ W ∈ Termᶜ ]
      (Valueᶜ W × M —↠ W × (∀ x → x ∈ D → x ≢ ω → 𝕍 x W))
common {M} {D} {x₀} x₀∈ x₀≢ω h
  with proj₂ (h x₀ x₀∈) x₀≢ω
common {M} {D} {x₀} x₀∈ x₀≢ω h
  | W₀ , vW₀ , M—↠W₀ , rel₀ = W₀ , vW₀ , M—↠W₀ , all
  where
  all : ∀ x → x ∈ D → x ≢ ω → 𝕍 x W₀
  all x x∈ x≢ω with proj₂ (h x x∈) x≢ω
  all x x∈ x≢ω | W , vW , M—↠W , rel =
    subst (𝕍 x) (sym (—↠-value-unique vW₀ vW M—↠W₀ M—↠W)) rel

------------------------------------------------------------------------
-- Coercions
------------------------------------------------------------------------

adequacyᶜ : ∀ c {X V}
  → Valueᶜ V
  → (∀ x → x ∈ X → 𝕍 x V)
  → ∀ d → d ∈ ⟦ c ⟧ᶜ X → 𝔼 d (cast V [ c ])
adequacyᶜ (idᶜ A) vV h d d∈ = expand (step (β-id vV)) (𝕍→𝔼 d (h d d∈))
adequacyᶜ (A !) {V = V} vV h (tag t v) (tagTy≡A , v∈) =
  𝕍→𝔼 (tag t v)
    (V , cong (λ B → cast V [ B ! ]) (sym tagTy≡A) , vV , h v v∈)
adequacyᶜ (A !) vV h (nat n) ()
adequacyᶜ (A !) vV h (U ⟼ w) ()
adequacyᶜ (A !) vV h ν ()
adequacyᶜ (A !) vV h ω ()
adequacyᶜ (_`? {ℓ = ℓ} .(tagTy t)) vV h d (inj₁ (t , refl , td∈))
  with h (tag t d) td∈
adequacyᶜ (_`? {ℓ = ℓ} .(tagTy t)) vV h d (inj₁ (t , refl , td∈))
  | W , refl , vW , rel =
  expand (step (β-proj-inj-ok vW)) (𝕍→𝔼 d rel)
adequacyᶜ (_`? {ℓ = ℓ} A) vV h .ω (inj₂ (refl , t , v , tv∈ , tagTy≢A))
  with h (tag t v) tv∈
adequacyᶜ (_`? {ℓ = ℓ} A) vV h .ω (inj₂ (refl , t , v , tv∈ , tagTy≢A))
  | W , refl , vW , rel =
  𝔼ω (step (β-proj-inj-bad vW tagTy≢A))
adequacyᶜ (c ↦ d′) {V = V} vV h ν (convX , tt) =
  𝕍→𝔼 ν (inj₂ (V , c , d′ , refl , vV))
adequacyᶜ (c ↦ d′) {X} {V} vV h (U ⟼ w) (convX , w∈ , U≢[] , noerr) =
  𝕍→𝔼 (U ⟼ w) (inj₂ (V , c , d′ , refl , vV) , app)
  where
  app : ∀ W → Valueᶜ W → 𝕍* U W → 𝔼 w (cast V [ c ↦ d′ ] · W)
  app W vW relU = expand (step (β-↦ vV vW)) (wrap w∈)
    where
    hU : ∀ x → x ∈ mem U → 𝕍 x W
    hU x x∈ = 𝕍*-∋ relU x∈

    wrap : w ∈ (⟦ c ⟧ᶜ (mem U) ≫= λ Y₁ → (X ● Y₁) ≫= ⟦ d′ ⟧ᶜ)
      → 𝔼 w (cast (V · cast W [ c ]) [ d′ ])
    wrap (inj₁ (refl , ω∈c)) =
      let ℓ , r = proj₁ (adequacyᶜ c vW hU ω ω∈c) refl in
      𝔼ω (blame-frame cast□[ d′ ] (blame-frame (V ·□ vV) r))
    wrap (inj₂ ((y , y∈ , y≢ω) , w∈′))
      with common y∈ y≢ω (adequacyᶜ c vW hU)
    wrap (inj₂ ((y , y∈ , y≢ω) , w∈′))
      | W₁ , vW₁ , r₁ , all₁ = expand prefix (rest w∈′)
      where
      prefix : cast (V · cast W [ c ]) [ d′ ] —↠ cast (V · W₁) [ d′ ]
      prefix = ξ* cast□[ d′ ] (ξ* (V ·□ vV) r₁)

      Y₁ : 𝒫
      Y₁ = ⌊ ⟦ c ⟧ᶜ (mem U) ⌋

      relY : ∀ V′ → mem V′ ⊆ Y₁ → 𝕍* V′ W₁
      relY V′ V′⊆ =
        𝕍*-from V′ (λ u u∈ → let u∈Y , u≢ω = V′⊆ u u∈ in
                                all₁ u u∈Y u≢ω)

      appX : ∀ x → x ∈ (X ● Y₁) → 𝔼 x (V · W₁)
      appX x (V′ , e∈ , V′⊆ , V′≢[]) =
        proj₂ (h (V′ ⟼ x) e∈) W₁ vW₁ (relY V′ V′⊆)

      rest : w ∈ ((X ● Y₁) ≫= ⟦ d′ ⟧ᶜ) → 𝔼 w (cast (V · W₁) [ d′ ])
      rest (inj₁ (refl , ω∈X●)) =
        let ℓ , rb = proj₁ (appX ω ω∈X●) refl in
        𝔼ω (blame-frame cast□[ d′ ] rb)
      rest (inj₂ ((r , r∈ , r≢ω) , w∈d))
        with common r∈ r≢ω appX
      rest (inj₂ ((r , r∈ , r≢ω) , w∈d))
        | W₂ , vW₂ , r₂ , all₂ =
        expand (ξ* cast□[ d′ ] r₂)
          (adequacyᶜ d′ vW₂ (λ x x∈ → all₂ x (proj₁ x∈) (proj₂ x∈)) w w∈d)
adequacyᶜ (c ↦ d′) vV h (nat n) (convX , ())
adequacyᶜ (c ↦ d′) vV h ω (convX , ())
adequacyᶜ (c ↦ d′) vV h (tag t d) (convX , ())
adequacyᶜ (c ⨟ d′) {V = V} vV h d (inj₁ (refl , ω∈c)) =
  let ℓ , r = proj₁ (adequacyᶜ c vV h ω ω∈c) refl in
  𝔼ω (step (β-seq vV) ++ᶜ blame-frame cast□[ d′ ] r)
adequacyᶜ (c ⨟ d′) {V = V} vV h d (inj₂ ((y , y∈ , y≢ω) , d∈))
  with common y∈ y≢ω (adequacyᶜ c vV h)
adequacyᶜ (c ⨟ d′) {V = V} vV h d (inj₂ ((y , y∈ , y≢ω) , d∈))
  | W₁ , vW₁ , r₁ , all₁ =
  expand (step (β-seq vV) ++ᶜ ξ* cast□[ d′ ] r₁)
    (adequacyᶜ d′ vW₁ (λ x x∈ → all₁ x (proj₁ x∈) (proj₂ x∈)) d d∈)
adequacyᶜ (⊥ᶜ A ⇨ B at ℓ) vV h .ω (convX , refl) = 𝔼ω (step (β-⊥ vV))

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

fundamental : ∀ M {ρ σ}
  → 𝔾 ρ σ
  → ∀ d → d ∈ ⟦ M ⟧ ρ → 𝔼 d (substᶜ σ M)
fundamental (` x) g d d∈ = 𝕍→𝔼 d (g x d d∈)
fundamental ($ n) g .(nat n) refl = 𝕍→𝔼 (nat n) refl
fundamental (ƛ A ⇒ N) g ν tt = 𝕍→𝔼 ν (inj₁ (A , _ , refl))
fundamental (ƛ A ⇒ N) {ρ} {σ} g (U ⟼ w) (w∈ , U≢[] , noerr) =
  𝕍→𝔼 (U ⟼ w) (inj₁ (A , _ , refl) , app)
  where
  app : ∀ W → Valueᶜ W → 𝕍* U W
    → 𝔼 w ((ƛ A ⇒ substᶜ (extsᶜ σ) N) · W)
  app W vW relU =
    expand (step (β-ƛ vW))
      (subst (𝔼 w) (sym (subst-β σ W N)) (fundamental N g′ w w∈))
    where
    g′ : 𝔾 (mem U • ρ) (W •ˢ σ)
    g′ zero d d∈ = 𝕍*-∋ relU d∈
    g′ (suc x) d d∈ = g x d d∈
fundamental (ƛ A ⇒ N) g (nat n) ()
fundamental (ƛ A ⇒ N) g ω ()
fundamental (ƛ A ⇒ N) g (tag t d) ()
fundamental (L · M) {σ = σ} g .ω (inj₁ (refl , ω∈L)) =
  let ℓ , r = proj₁ (fundamental L g ω ω∈L) refl in
  𝔼ω (blame-frame (□· substᶜ σ M) r)
fundamental (L · M) {σ = σ} g .ω
    (inj₂ ((f , f∈ , f≢ω) , inj₁ (refl , ω∈M)))
  with proj₂ (fundamental L g f f∈) f≢ω
fundamental (L · M) {σ = σ} g .ω
    (inj₂ ((f , f∈ , f≢ω) , inj₁ (refl , ω∈M)))
  | V , vV , rL , rel =
  let ℓ , rM = proj₁ (fundamental M g ω ω∈M) refl in
  𝔼ω (ξ* (□· substᶜ σ M) rL ++ᶜ blame-frame (V ·□ vV) rM)
fundamental (L · M) {σ = σ} g d
    (inj₂ ((f , f∈ , f≢ω) ,
           inj₂ ((a , a∈ , a≢ω) , V′ , (e∈ , e≢ω) , V′⊆ , V′≢[])))
  with proj₂ (fundamental L g (V′ ⟼ d) e∈) e≢ω
     | common a∈ a≢ω (fundamental M g)
fundamental (L · M) {σ = σ} g d
    (inj₂ ((f , f∈ , f≢ω) ,
           inj₂ ((a , a∈ , a≢ω) , V′ , (e∈ , e≢ω) , V′⊆ , V′≢[])))
  | V , vV , rL , (fv , app) | W , vW , rM , allW =
  expand (ξ* (□· substᶜ σ M) rL ++ᶜ ξ* (V ·□ vV) rM)
    (app W vW (𝕍*-from V′ (λ u u∈ → let u∈M , u≢ω = V′⊆ u u∈ in
                                     allW u u∈M u≢ω)))
fundamental (cast M [ c ]) g .ω (inj₁ (refl , ω∈M)) =
  let ℓ , r = proj₁ (fundamental M g ω ω∈M) refl in
  𝔼ω (blame-frame cast□[ c ] r)
fundamental (cast M [ c ]) g d (inj₂ ((a , a∈ , a≢ω) , d∈))
  with common a∈ a≢ω (fundamental M g)
fundamental (cast M [ c ]) g d (inj₂ ((a , a∈ , a≢ω) , d∈))
  | W , vW , rM , allW =
  expand (ξ* cast□[ c ] rM)
    (adequacyᶜ c vW (λ x x∈ → allW x (proj₁ x∈) (proj₂ x∈)) d d∈)
fundamental (blame {ℓ = ℓ}) g .ω refl = 𝔼ω (blame {ℓ = ℓ} ∎)

------------------------------------------------------------------------
-- Adequacy
------------------------------------------------------------------------

𝔾₀ : 𝔾 ρ₀ `_
𝔾₀ x d ()

adequacy : ∀ M d → d ∈ ⟦ M ⟧ ρ₀ → 𝔼 d M
adequacy M d d∈ = subst (𝔼 d) (subst-id M) (fundamental M 𝔾₀ d d∈)

obs-𝕍 : ∀ d {V} (vV : Valueᶜ V) → 𝕍 d V → observe vV ≡ obs d
obs-𝕍 (nat n) V-$ refl = refl
obs-𝕍 (U ⟼ w) V-ƛ rel = refl
obs-𝕍 (U ⟼ w) (V-cast↦ vW) rel = refl
obs-𝕍 (U ⟼ w) V-$ (inj₁ (A , N , ()) , app)
obs-𝕍 (U ⟼ w) V-$ (inj₂ (W , c , d , () , vW) , app)
obs-𝕍 (U ⟼ w) (V-cast! vW) (inj₁ (A , N , ()) , app)
obs-𝕍 (U ⟼ w) (V-cast! vW) (inj₂ (W , c , d , () , vW′) , app)
obs-𝕍 ν V-ƛ rel = refl
obs-𝕍 ν (V-cast↦ vW) rel = refl
obs-𝕍 ν V-$ (inj₁ (A , N , ()))
obs-𝕍 ν V-$ (inj₂ (W , c , d , () , vW))
obs-𝕍 ν (V-cast! vW) (inj₁ (A , N , ()))
obs-𝕍 ν (V-cast! vW) (inj₂ (W , c , d , () , vW′))
obs-𝕍 ω vV ()
obs-𝕍 (tag t d) (V-cast! vW) (W , refl , vW′ , rel) = obs-𝕍 d vW rel

adequacy-val : ∀ {M d}
  → d ∈ ⟦ M ⟧ ρ₀
  → d ≢ ω
  → Σ[ V ∈ Termᶜ ] Σ[ v ∈ Valueᶜ V ] (M —↠ V × observe v ≡ obs d)
adequacy-val {M} {d} d∈ d≢ω with proj₂ (adequacy M d d∈) d≢ω
adequacy-val {M} {d} d∈ d≢ω | V , vV , M—↠V , rel =
  V , vV , M—↠V , obs-𝕍 d vV rel

adequacy-err : ∀ {M}
  → ω ∈ ⟦ M ⟧ ρ₀
  → Σ[ ℓ ∈ Nat ] (M —↠ blame {ℓ = ℓ})
adequacy-err {M} ω∈ = proj₁ (adequacy M ω ω∈) refl
