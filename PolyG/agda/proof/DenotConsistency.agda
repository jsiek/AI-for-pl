module proof.DenotConsistency where

-- File Charter:
--   * Consistency of the denotation (GraphModel.agda, Denotation.agda):
--     if every ρ x is Consistent then Consistentᴿ (⟦ M ⟧ θ ρ n)
--     (⟦⟧-consistent), as in the compiler-correctness development
--     (denotational_semantics, Framework/GraphModel).
--   * Consistency is symmetric (~-sym, ~ᴿ-sym, ≈-sym).
--   * Each operator preserves consistency: retᴿ, bind, guard, Λ (using
--     monotonicity of the body), application ●, Λᴾ, instantiation ◆,
--     seals, tags, tag tests, projections, conditionals, casts
--     (⟦⟧ᶜ-consistent) and stacks (⟦⟧ˢ-consistent).
--   * A consistent set of results ends all its value results at one
--     counter and holds no err beside a value (consistent-counter,
--     consistent-err).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types
open import Terms
open import GraphModel
open import Denotation
open import proof.DenotProps

------------------------------------------------------------------------
-- Symmetry
------------------------------------------------------------------------

≈-tail : ∀ U v V → U ≈ (v ∷ V) → U ≈ V
≈-tail [] v V tt = tt
≈-tail (u ∷ U) v V ((u~v , u~V) , U≈) = u~V , ≈-tail U v V U≈

mutual
  ~-sym : ∀ u v → u ~ v → v ~ u
  ~-sym vtrue vtrue tt = tt
  ~-sym vtrue vfalse ()
  ~-sym vtrue (sealᵛ σ′ u′) ()
  ~-sym vtrue (injᵛ H u′) ()
  ~-sym vtrue (U′ ⟼ r′ at m′) ()
  ~-sym vtrue (σ′ ⟼∀ r′) ()
  ~-sym vtrue νλ ()
  ~-sym vtrue ν∀ ()
  ~-sym vfalse vtrue ()
  ~-sym vfalse vfalse tt = tt
  ~-sym vfalse (sealᵛ σ′ u′) ()
  ~-sym vfalse (injᵛ H u′) ()
  ~-sym vfalse (U′ ⟼ r′ at m′) ()
  ~-sym vfalse (σ′ ⟼∀ r′) ()
  ~-sym vfalse νλ ()
  ~-sym vfalse ν∀ ()
  ~-sym (sealᵛ σ u) vtrue ()
  ~-sym (sealᵛ σ u) vfalse ()
  ~-sym (sealᵛ σ u) (sealᵛ σ′ u′) (e , c) = sym e , ~-sym u u′ c
  ~-sym (sealᵛ σ u) (injᵛ H u′) ()
  ~-sym (sealᵛ σ u) (U′ ⟼ r′ at m′) ()
  ~-sym (sealᵛ σ u) (σ′ ⟼∀ r′) ()
  ~-sym (sealᵛ σ u) νλ ()
  ~-sym (sealᵛ σ u) ν∀ ()
  ~-sym (injᵛ G u) vtrue ()
  ~-sym (injᵛ G u) vfalse ()
  ~-sym (injᵛ G u) (sealᵛ σ′ u′) ()
  ~-sym (injᵛ G u) (injᵛ H u′) (e , c) = sym e , ~-sym u u′ c
  ~-sym (injᵛ G u) (U′ ⟼ r′ at m′) ()
  ~-sym (injᵛ G u) (σ′ ⟼∀ r′) ()
  ~-sym (injᵛ G u) νλ ()
  ~-sym (injᵛ G u) ν∀ ()
  ~-sym (U ⟼ r at m) vtrue ()
  ~-sym (U ⟼ r at m) vfalse ()
  ~-sym (U ⟼ r at m) (sealᵛ σ′ u′) ()
  ~-sym (U ⟼ r at m) (injᵛ H u′) ()
  ~-sym (U ⟼ r at m) (U′ ⟼ r′ at m′) h =
    λ e c → ~ᴿ-sym r r′ (h (sym e) (≈-sym U′ U c))
  ~-sym (U ⟼ r at m) (σ′ ⟼∀ r′) ()
  ~-sym (U ⟼ r at m) νλ tt = tt
  ~-sym (U ⟼ r at m) ν∀ ()
  ~-sym (σ ⟼∀ r) vtrue ()
  ~-sym (σ ⟼∀ r) vfalse ()
  ~-sym (σ ⟼∀ r) (sealᵛ σ′ u′) ()
  ~-sym (σ ⟼∀ r) (injᵛ H u′) ()
  ~-sym (σ ⟼∀ r) (U′ ⟼ r′ at m′) ()
  ~-sym (σ ⟼∀ r) (σ′ ⟼∀ r′) h = λ e → ~ᴿ-sym r r′ (h (sym e))
  ~-sym (σ ⟼∀ r) νλ ()
  ~-sym (σ ⟼∀ r) ν∀ tt = tt
  ~-sym νλ vtrue ()
  ~-sym νλ vfalse ()
  ~-sym νλ (sealᵛ σ′ u′) ()
  ~-sym νλ (injᵛ H u′) ()
  ~-sym νλ (U′ ⟼ r′ at m′) tt = tt
  ~-sym νλ (σ′ ⟼∀ r′) ()
  ~-sym νλ νλ tt = tt
  ~-sym νλ ν∀ ()
  ~-sym ν∀ vtrue ()
  ~-sym ν∀ vfalse ()
  ~-sym ν∀ (sealᵛ σ′ u′) ()
  ~-sym ν∀ (injᵛ H u′) ()
  ~-sym ν∀ (U′ ⟼ r′ at m′) ()
  ~-sym ν∀ (σ′ ⟼∀ r′) tt = tt
  ~-sym ν∀ νλ ()
  ~-sym ν∀ ν∀ tt = tt

  ~ᴿ-sym : ∀ r s → r ~ᴿ s → s ~ᴿ r
  ~ᴿ-sym (ret v m) (ret v′ m′) (e , c) = sym e , ~-sym v v′ c
  ~ᴿ-sym (ret v m) err ()
  ~ᴿ-sym err (ret v′ m′) ()
  ~ᴿ-sym err err tt = tt

  ≈-sym : ∀ U V → U ≈ V → V ≈ U
  ≈-sym U [] h = tt
  ≈-sym U (v ∷ V) h = column U v V h , ≈-sym U V (≈-tail U v V h)

  -- the column of v in U ≈ (v ∷ V)
  column : ∀ U v V → U ≈ (v ∷ V) → v ~* U
  column [] v V tt = tt
  column (u ∷ U) v V ((u~v , u~V) , U≈) =
    ~-sym u v u~v , column U v V U≈

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

~*-at : ∀ {u v} V → u ~* V → v ⋵ V → u ~ v
~*-at (v ∷ V) (u~v , u~V) (here refl) = u~v
~*-at (w ∷ V) (u~w , u~V) (there v∈) = ~*-at V u~V v∈

≈-at : ∀ {u v} U V → U ≈ V → u ⋵ U → v ⋵ V → u ~ v
≈-at (u ∷ U) V (u~V , U≈) (here refl) v∈ = ~*-at V u~V v∈
≈-at (w ∷ U) V (w~V , U≈) (there u∈) v∈ = ≈-at U V U≈ u∈ v∈

-- the arguments of two consistent entries, together
≈-++ : ∀ U V → U ≈ U → V ≈ V → U ≈ V → Consistent (mem (U ++ V))
≈-++ U V cU cV c u v u∈ v∈ with ∈-++⁻ U u∈ | ∈-++⁻ U v∈
≈-++ U V cU cV c u v u∈ v∈ | inj₁ u∈U | inj₁ v∈U = ≈-at U U cU u∈U v∈U
≈-++ U V cU cV c u v u∈ v∈ | inj₁ u∈U | inj₂ v∈V = ≈-at U V c u∈U v∈V
≈-++ U V cU cV c u v u∈ v∈ | inj₂ u∈V | inj₁ v∈U =
  ≈-at V U (≈-sym U V c) u∈V v∈U
≈-++ U V cU cV c u v u∈ v∈ | inj₂ u∈V | inj₂ v∈V = ≈-at V V cV u∈V v∈V

------------------------------------------------------------------------
-- Results
------------------------------------------------------------------------

-- a consistent set of results ends its value results at one counter
consistent-counter : ∀ {R u v m m′} → Consistentᴿ R
  → ret u m ∈ᴿ R → ret v m′ ∈ᴿ R → m ≡ m′
consistent-counter cR u∈ v∈ = proj₁ (cR _ _ u∈ v∈)

-- and does not hold err beside a value
consistent-err : ∀ {R v m} → Consistentᴿ R
  → err ∈ᴿ R → ret v m ∈ᴿ R → ⊥
consistent-err cR e∈ v∈ = cR _ _ e∈ v∈

⌊⌋-consistent : ∀ {R} → Consistentᴿ R → ∀ m → Consistent (⌊ R ⌋ m)
⌊⌋-consistent cR m u v u∈ v∈ = proj₂ (cR _ _ u∈ v∈)

retᴿ-consistent : ∀ {D n} → Consistent D → Consistentᴿ (retᴿ D n)
retᴿ-consistent cD (ret u m) (ret v m′) (e , u∈) (e′ , v∈) =
  trans e (sym e′) , cD u v u∈ v∈

errᴿ-consistent : Consistentᴿ errᴿ
errᴿ-consistent err err tt tt = tt

⌈⌉-consistent : ∀ {v} → v ~ v → Consistent ⌈ v ⌉
⌈⌉-consistent c u w refl refl = c

≫=-consistent : ∀ {R K} → Consistentᴿ R
  → (∀ D m → Consistent D → Consistentᴿ (K D m))
  → Consistentᴿ (R ≫= K)
≫=-consistent cR cK r s (inj₁ (refl , e∈)) (inj₁ (refl , e′∈)) = tt
≫=-consistent cR cK r s (inj₁ (refl , e∈)) (inj₂ (m , (v , v∈) , s∈)) =
  ⊥-elim (consistent-err cR e∈ v∈)
≫=-consistent cR cK r s (inj₂ (m , (v , v∈) , r∈)) (inj₁ (refl , e∈)) =
  ⊥-elim (consistent-err cR e∈ v∈)
≫=-consistent {R} cR cK r s
    (inj₂ (m , (u , u∈) , r∈)) (inj₂ (m′ , (v , v∈) , s∈))
  with consistent-counter cR u∈ v∈
≫=-consistent {R} cR cK r s
    (inj₂ (m , (u , u∈) , r∈)) (inj₂ (m′ , (v , v∈) , s∈)) | refl =
  cK (⌊ R ⌋ m) m (⌊⌋-consistent cR m) r s r∈ s∈

guard-consistent : ∀ {v D R} → Consistentᴿ R → Consistentᴿ (guard v D R)
guard-consistent cR r s (v∈ , r∈) (v∈′ , s∈) = cR r s r∈ s∈

condᴿ-consistent : ∀ {D R T} → Consistent D → Consistentᴿ R
  → Consistentᴿ T → Consistentᴿ (condᴿ D R T)
condᴿ-consistent cD cR cT r s (inj₁ (t∈ , r∈)) (inj₁ (t∈′ , s∈)) =
  cR r s r∈ s∈
condᴿ-consistent cD cR cT r s (inj₁ (t∈ , r∈)) (inj₂ (f∈ , s∈)) =
  ⊥-elim (cD vtrue vfalse t∈ f∈)
condᴿ-consistent cD cR cT r s (inj₂ (f∈ , r∈)) (inj₁ (t∈ , s∈)) =
  ⊥-elim (cD vtrue vfalse t∈ f∈)
condᴿ-consistent cD cR cT r s (inj₂ (f∈ , r∈)) (inj₂ (f∈′ , s∈)) =
  cT r s r∈ s∈

------------------------------------------------------------------------
-- Closures
------------------------------------------------------------------------

Λ-entries : ∀ {F : 𝒱 → ℕ → ℛ} {m r r′}
  → (∀ {D D′} m → D ⊆ D′ → F D m ⊆ᴿ F D′ m)
  → (∀ D m → Consistent D → Consistentᴿ (F D m))
  → ∀ U U′ → U ≈ U → U′ ≈ U′ → U ≈ U′
  → r ∈ᴿ F (mem U) m → r′ ∈ᴿ F (mem U′) m → r ~ᴿ r′
Λ-entries {m = m} Fm cF U U′ cU cU′ c r∈ r′∈ =
  cF (mem (U ++ U′)) m (≈-++ U U′ cU cU′ c) _ _
    (Fm m (λ v v∈ → ∈-++⁺ˡ v∈) _ r∈)
    (Fm m (λ v v∈ → ∈-++⁺ʳ U v∈) _ r′∈)

Λ-cons : ∀ {F : 𝒱 → ℕ → ℛ}
  → (∀ {D D′} m → D ⊆ D′ → F D m ⊆ᴿ F D′ m)
  → (∀ D m → Consistent D → Consistentᴿ (F D m))
  → Consistent (Λ F)
Λ-cons Fm cF vtrue v () v∈
Λ-cons Fm cF vfalse v () v∈
Λ-cons Fm cF (sealᵛ σ u) v () v∈
Λ-cons Fm cF (injᵛ G u) v () v∈
Λ-cons Fm cF (U ⟼ r at m) vtrue u∈ ()
Λ-cons Fm cF (U ⟼ r at m) vfalse u∈ ()
Λ-cons Fm cF (U ⟼ r at m) (sealᵛ σ′ u′) u∈ ()
Λ-cons Fm cF (U ⟼ r at m) (injᵛ H u′) u∈ ()
Λ-cons Fm cF (U ⟼ r at m) (U′ ⟼ r′ at m′) (r∈ , ne , cU) (r′∈ , ne′ , cU′) =
  λ { refl c → Λ-entries Fm cF U U′ cU cU′ c r∈ r′∈ }
Λ-cons Fm cF (U ⟼ r at m) (σ′ ⟼∀ r′) u∈ ()
Λ-cons Fm cF (U ⟼ r at m) νλ u∈ v∈ = tt
Λ-cons Fm cF (U ⟼ r at m) ν∀ u∈ ()
Λ-cons Fm cF (σ ⟼∀ r) v () v∈
Λ-cons Fm cF νλ vtrue u∈ ()
Λ-cons Fm cF νλ vfalse u∈ ()
Λ-cons Fm cF νλ (sealᵛ σ′ u′) u∈ ()
Λ-cons Fm cF νλ (injᵛ H u′) u∈ ()
Λ-cons Fm cF νλ (U′ ⟼ r′ at m′) u∈ v∈ = tt
Λ-cons Fm cF νλ (σ′ ⟼∀ r′) u∈ ()
Λ-cons Fm cF νλ νλ u∈ v∈ = tt
Λ-cons Fm cF νλ ν∀ u∈ ()
Λ-cons Fm cF ν∀ v () v∈

Λᴾ-cons : ∀ {F : Seal → ℛ} → (∀ σ → Consistentᴿ (F σ)) → Consistent (Λᴾ F)
Λᴾ-cons cF vtrue v () v∈
Λᴾ-cons cF vfalse v () v∈
Λᴾ-cons cF (sealᵛ σ u) v () v∈
Λᴾ-cons cF (injᵛ G u) v () v∈
Λᴾ-cons cF (U ⟼ r at m) v () v∈
Λᴾ-cons cF (σ ⟼∀ r) vtrue u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) vfalse u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) (sealᵛ σ′ u′) u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) (injᵛ H u′) u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) (U′ ⟼ r′ at m′) u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) (σ′ ⟼∀ r′) r∈ r′∈ = λ { refl → cF σ r r′ r∈ r′∈ }
Λᴾ-cons cF (σ ⟼∀ r) νλ u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) ν∀ u∈ v∈ = tt
Λᴾ-cons cF νλ v () v∈
Λᴾ-cons cF ν∀ vtrue u∈ ()
Λᴾ-cons cF ν∀ vfalse u∈ ()
Λᴾ-cons cF ν∀ (sealᵛ σ′ u′) u∈ ()
Λᴾ-cons cF ν∀ (injᵛ H u′) u∈ ()
Λᴾ-cons cF ν∀ (U′ ⟼ r′ at m′) u∈ ()
Λᴾ-cons cF ν∀ (σ′ ⟼∀ r′) u∈ v∈ = tt
Λᴾ-cons cF ν∀ νλ u∈ ()
Λᴾ-cons cF ν∀ ν∀ u∈ v∈ = tt

●-consistent : ∀ {D E m} → Consistent D → Consistent E
  → Consistentᴿ (D ●[ m ] E)
●-consistent cD cE r s (U , e∈ , U⊆ , ne) (U′ , e′∈ , U′⊆ , ne′) =
  cD _ _ e∈ e′∈ refl (mem-≈ cE U U′ U⊆ U′⊆)

◆-consistent : ∀ {D σ} → Consistent D → Consistentᴿ (D ◆ σ)
◆-consistent cD r s r∈ s∈ = cD _ _ r∈ s∈ refl

------------------------------------------------------------------------
-- Seals and tags
------------------------------------------------------------------------

sealᴾ-cons : ∀ {σ D} → Consistent D → Consistent (sealᴾ σ D)
sealᴾ-cons cD vtrue v () v∈
sealᴾ-cons cD vfalse v () v∈
sealᴾ-cons cD (sealᵛ σ u) vtrue u∈ ()
sealᴾ-cons cD (sealᵛ σ u) vfalse u∈ ()
sealᴾ-cons cD (sealᵛ σ u) (sealᵛ σ′ u′) (e , u∈) (e′ , u′∈) =
  trans e (sym e′) , cD u u′ u∈ u′∈
sealᴾ-cons cD (sealᵛ σ u) (injᵛ H u′) u∈ ()
sealᴾ-cons cD (sealᵛ σ u) (U′ ⟼ r′ at m′) u∈ ()
sealᴾ-cons cD (sealᵛ σ u) (σ′ ⟼∀ r′) u∈ ()
sealᴾ-cons cD (sealᵛ σ u) νλ u∈ ()
sealᴾ-cons cD (sealᵛ σ u) ν∀ u∈ ()
sealᴾ-cons cD (injᵛ G u) v () v∈
sealᴾ-cons cD (U ⟼ r at m) v () v∈
sealᴾ-cons cD (σ ⟼∀ r) v () v∈
sealᴾ-cons cD νλ v () v∈
sealᴾ-cons cD ν∀ v () v∈

unsealᴾ-consistent : ∀ {σ D} → Consistent D → Consistent (unsealᴾ σ D)
unsealᴾ-consistent cD u v u∈ v∈ = proj₂ (cD _ _ u∈ v∈)

injᴾ-cons : ∀ {G D} → Consistent D → Consistent (injᴾ G D)
injᴾ-cons cD vtrue v () v∈
injᴾ-cons cD vfalse v () v∈
injᴾ-cons cD (sealᵛ σ u) v () v∈
injᴾ-cons cD (injᵛ G u) vtrue u∈ ()
injᴾ-cons cD (injᵛ G u) vfalse u∈ ()
injᴾ-cons cD (injᵛ G u) (sealᵛ σ′ u′) u∈ ()
injᴾ-cons cD (injᵛ G u) (injᵛ H u′) (e , u∈) (e′ , u′∈) =
  trans e (sym e′) , cD u u′ u∈ u′∈
injᴾ-cons cD (injᵛ G u) (U′ ⟼ r′ at m′) u∈ ()
injᴾ-cons cD (injᵛ G u) (σ′ ⟼∀ r′) u∈ ()
injᴾ-cons cD (injᵛ G u) νλ u∈ ()
injᴾ-cons cD (injᵛ G u) ν∀ u∈ ()
injᴾ-cons cD (U ⟼ r at m) v () v∈
injᴾ-cons cD (σ ⟼∀ r) v () v∈
injᴾ-cons cD νλ v () v∈
injᴾ-cons cD ν∀ v () v∈

testᴾ-cons : ∀ {G D} → Consistent D → Consistent (testᴾ G D)
testᴾ-cons cD vtrue vtrue u∈ v∈ = tt
testᴾ-cons cD vtrue vfalse (w , w∈) (H , w′ , w′∈ , H≢G) =
  ⊥-elim (H≢G (sym (proj₁ (cD _ _ w∈ w′∈))))
testᴾ-cons cD vtrue (sealᵛ σ′ u′) u∈ ()
testᴾ-cons cD vtrue (injᵛ H u′) u∈ ()
testᴾ-cons cD vtrue (U′ ⟼ r′ at m′) u∈ ()
testᴾ-cons cD vtrue (σ′ ⟼∀ r′) u∈ ()
testᴾ-cons cD vtrue νλ u∈ ()
testᴾ-cons cD vtrue ν∀ u∈ ()
testᴾ-cons cD vfalse vtrue (H , w′ , w′∈ , H≢G) (w , w∈) =
  ⊥-elim (H≢G (sym (proj₁ (cD _ _ w∈ w′∈))))
testᴾ-cons cD vfalse vfalse u∈ v∈ = tt
testᴾ-cons cD vfalse (sealᵛ σ′ u′) u∈ ()
testᴾ-cons cD vfalse (injᵛ H u′) u∈ ()
testᴾ-cons cD vfalse (U′ ⟼ r′ at m′) u∈ ()
testᴾ-cons cD vfalse (σ′ ⟼∀ r′) u∈ ()
testᴾ-cons cD vfalse νλ u∈ ()
testᴾ-cons cD vfalse ν∀ u∈ ()
testᴾ-cons cD (sealᵛ σ u) v () v∈
testᴾ-cons cD (injᵛ G u) v () v∈
testᴾ-cons cD (U ⟼ r at m) v () v∈
testᴾ-cons cD (σ ⟼∀ r) v () v∈
testᴾ-cons cD νλ v () v∈
testᴾ-cons cD ν∀ v () v∈

proj-consistent : ∀ {G D m} → Consistent D → Consistentᴿ (proj G D m)
proj-consistent cD (ret u m₁) (ret v m₂) (e₁ , u∈) (e₂ , v∈) =
  trans e₁ (sym e₂) , proj₂ (cD _ _ u∈ v∈)
proj-consistent cD (ret u m₁) err (e₁ , u∈) (H , v , v∈ , H≢G) =
  ⊥-elim (H≢G (sym (proj₁ (cD _ _ u∈ v∈))))
proj-consistent cD err (ret u m₁) (H , v , v∈ , H≢G) (e₁ , u∈) =
  ⊥-elim (H≢G (sym (proj₁ (cD _ _ u∈ v∈))))
proj-consistent cD err err h h′ = tt

------------------------------------------------------------------------
-- Casts and stacks
------------------------------------------------------------------------

⟦⟧ᶜ-consistent : ∀ d p θ {E m} → Consistent E
  → Consistentᴿ (⟦ d , p ⟧ᶜ θ E m)
⟦⟧ᶜ-consistent d ★⊑ θ cE = retᴿ-consistent cE
⟦⟧ᶜ-consistent d 𝔹⊑ θ cE = retᴿ-consistent cE
⟦⟧ᶜ-consistent d (‵⊑ α) θ cE = retᴿ-consistent cE
⟦⟧ᶜ-consistent d (p ⇒⊑ q) θ {E} {m} cE =
  guard-consistent {v = νλ} {D = E} (retᴿ-consistent {n = m} (Λ-cons
    (λ m′ D⊆ → ≫=-mono (⟦⟧ᶜ-mono (flip d) p θ D⊆)
      (λ m₁ X⊆ → ≫=-mono (●-mono {D = E} ⊆-refl X⊆)
                         (λ m₂ → ⟦⟧ᶜ-mono d q θ)))
    (λ D m′ cD → ≫=-consistent (⟦⟧ᶜ-consistent (flip d) p θ {m = m′} cD)
      (λ D₁ m₁ cD₁ → ≫=-consistent (●-consistent {m = m₁} cE cD₁)
        (λ D₂ m₂ cD₂ → ⟦⟧ᶜ-consistent d q θ {m = m₂} cD₂)))))
⟦⟧ᶜ-consistent d (∀⊑ p) θ {E} {m} cE =
  guard-consistent {v = ν∀} {D = E} (retᴿ-consistent {n = m}
    (Λᴾ-cons (λ σ →
      ≫=-consistent (◆-consistent {σ = σ} cE)
        (λ D m₁ cD → ⟦⟧ᶜ-consistent d p (σ •ᵗ θ) {m = m₁} cD))))
⟦⟧ᶜ-consistent up (tag G p) θ {m = m} cE =
  ≫=-consistent (⟦⟧ᶜ-consistent up p θ {m = m} cE)
    (λ D m₁ cD → retᴿ-consistent {n = m₁} (injᴾ-cons {G = ⟦ G ⟧ᴳ θ} cD))
⟦⟧ᶜ-consistent down (tag G p) θ {m = m} cE =
  ≫=-consistent (proj-consistent {G = ⟦ G ⟧ᴳ θ} {m = m} cE)
    (λ D m₁ cD → ⟦⟧ᶜ-consistent down p θ {m = m₁} cD)

⟦⟧ˢ-consistent : ∀ cs θ {R} → Consistentᴿ R → Consistentᴿ (⟦ cs ⟧ˢ θ R)
⟦⟧ˢ-consistent [] θ cR = cR
⟦⟧ˢ-consistent ((d , p) ∷ cs) θ cR =
  ≫=-consistent (⟦⟧ˢ-consistent cs θ cR)
    (λ D m cD → ⟦⟧ᶜ-consistent d p θ {m = m} cD)

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

ext-consistent : ∀ {D ρ} → Consistent D → (∀ x → Consistent (ρ x))
  → ∀ x → Consistent ((D • ρ) x)
ext-consistent cD cρ zero = cD
ext-consistent cD cρ (suc x) = cρ x

⟦⟧-consistent : ∀ M θ {ρ n} → (∀ x → Consistent (ρ x))
  → Consistentᴿ (⟦ M ⟧ θ ρ n)
⟦⟧-consistent (` x) θ cρ = retᴿ-consistent (cρ x)
⟦⟧-consistent ℧ θ cρ = errᴿ-consistent
⟦⟧-consistent true θ cρ = retᴿ-consistent (⌈⌉-consistent tt)
⟦⟧-consistent false θ cρ = retᴿ-consistent (⌈⌉-consistent tt)
⟦⟧-consistent (if L M N) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent L θ {n = n} cρ) (λ D m cD →
    condᴿ-consistent cD (⟦⟧-consistent M θ {n = m} cρ)
                        (⟦⟧-consistent N θ {n = m} cρ))
⟦⟧-consistent (ƛ A M) θ cρ =
  retᴿ-consistent (Λ-cons
    (λ m D⊆ → ⟦⟧-mono M (ext-⊆ₑ D⊆ ⊆ₑ-refl))
    (λ D m cD → ⟦⟧-consistent M θ {n = m} (ext-consistent cD cρ)))
⟦⟧-consistent (L · M) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent L θ {n = n} cρ) (λ F n₁ cF →
    ≫=-consistent (⟦⟧-consistent M θ {n = n₁} cρ) (λ E n₂ cE →
      ●-consistent {m = n₂} cF cE))
⟦⟧-consistent (letv M N) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (λ D m cD →
    ⟦⟧-consistent N θ {n = m} (ext-consistent cD cρ))
⟦⟧-consistent (seal α M) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (λ D m cD →
    retᴿ-consistent {n = m} (sealᴾ-cons {σ = ⟦ α ⟧ₙ θ} cD))
⟦⟧-consistent (unseal α M) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (λ D m cD →
    retᴿ-consistent {n = m} (unsealᴾ-consistent {σ = ⟦ α ⟧ₙ θ} cD))
⟦⟧-consistent (is G M) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (λ D m cD →
    retᴿ-consistent {n = m} (testᴾ-cons {G = ⟦ G ⟧ᴳ θ} cD))
⟦⟧-consistent (inj G M) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (λ D m cD →
    retᴿ-consistent {n = m} (injᴾ-cons {G = ⟦ G ⟧ᴳ θ} cD))
⟦⟧-consistent (cast d p M) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (λ D m cD →
    ⟦⟧ᶜ-consistent d p θ {m = m} cD)
⟦⟧-consistent (Λν cs M) θ cρ =
  retᴿ-consistent (Λᴾ-cons (λ σ →
    ⟦⟧ˢ-consistent cs (σ •ᵗ θ)
      (⟦⟧-consistent M (σ •ᵗ θ) {n = suc σ} cρ)))
⟦⟧-consistent (inst M B N) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (λ F n₁ cF →
    ≫=-consistent (◆-consistent {σ = n₁} cF) (λ E n₂ cE →
      ⟦⟧-consistent N (n₁ •ᵗ θ) {n = n₂} (ext-consistent cE cρ)))

-- the environment of a closed term
ρ₀-consistent : ∀ x → Consistent (ρ₀ x)
ρ₀-consistent x u v ()
