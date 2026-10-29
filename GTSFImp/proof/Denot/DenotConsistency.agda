module proof.Denot.DenotConsistency where

-- File Charter:
--   * Consistency of the GTSFImp denotation, ported from PolyG's
--     `proof/DenotConsistency`: if every ρ x is Consistent then
--     Consistentᴿ (⟦ M ⟧ θ ρ n) (⟦⟧-consistent).
--   * Consistency is symmetric (~-sym, ~ᴿ-sym, ≈-sym).
--   * Each operator preserves consistency; transformers are handled
--     generically (sequencing, function and ∀ proxies, gen values), and
--     reveals, conversions and casts follow by induction.
--   * A consistent set of results ends all its value results at one
--     counter and holds no err beside a value (consistent-counter,
--     consistent-err).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
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
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

open import Types using (Ty; ＇_; ‵_; ★; _⇒_; `∀; Ground; ★⇒★; ∀★;
  renameᵗ; extᵗ; ⇑ᵗ)
open import Consistency
open import Conversion
open import Primitives using (δ; δ-add; δ-and)
open import CastTerms using (Term; `_; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_;
  _⟨_⟩; _↑_; _↓_; blame)
open import Denot.GraphModel
open import Denot.Denotation
open import proof.Denot.DenotProps

------------------------------------------------------------------------
-- Symmetry
------------------------------------------------------------------------

≈-tail : ∀ U v V → U ≈ (v ∷ V) → U ≈ V
≈-tail [] v V tt = tt
≈-tail (u ∷ U) v V ((u~v , u~V) , U≈) = u~V , ≈-tail U v V U≈

mutual
  ~-sym : ∀ u v → u ~ v → v ~ u
  ~-sym (vconst κ) (vconst κ′) = λ e → sym e
  ~-sym (vconst κ) (sealᵛ σ′ u′) ()
  ~-sym (vconst κ) (injᵛ H u′) ()
  ~-sym (vconst κ) (U′ ⟼ r′ at m′) ()
  ~-sym (vconst κ) (σ′ ⟼∀ r′) ()
  ~-sym (vconst κ) νλ ()
  ~-sym (vconst κ) ν∀ ()
  ~-sym (sealᵛ σ u) (vconst κ′) ()
  ~-sym (sealᵛ σ u) (sealᵛ σ′ u′) = λ { (e , c) → sym e , ~-sym u u′ c }
  ~-sym (sealᵛ σ u) (injᵛ H u′) ()
  ~-sym (sealᵛ σ u) (U′ ⟼ r′ at m′) ()
  ~-sym (sealᵛ σ u) (σ′ ⟼∀ r′) ()
  ~-sym (sealᵛ σ u) νλ ()
  ~-sym (sealᵛ σ u) ν∀ ()
  ~-sym (injᵛ G u) (vconst κ′) ()
  ~-sym (injᵛ G u) (sealᵛ σ′ u′) ()
  ~-sym (injᵛ G u) (injᵛ H u′) = λ { (e , c) → sym e , ~-sym u u′ c }
  ~-sym (injᵛ G u) (U′ ⟼ r′ at m′) ()
  ~-sym (injᵛ G u) (σ′ ⟼∀ r′) ()
  ~-sym (injᵛ G u) νλ ()
  ~-sym (injᵛ G u) ν∀ ()
  ~-sym (U ⟼ r at m) (vconst κ′) ()
  ~-sym (U ⟼ r at m) (sealᵛ σ′ u′) ()
  ~-sym (U ⟼ r at m) (injᵛ H u′) ()
  ~-sym (U ⟼ r at m) (U′ ⟼ r′ at m′) = λ h e c → ~ᴿ-sym r r′ (h (sym e) (≈-sym U′ U c))
  ~-sym (U ⟼ r at m) (σ′ ⟼∀ r′) ()
  ~-sym (U ⟼ r at m) νλ = λ _ → tt
  ~-sym (U ⟼ r at m) ν∀ ()
  ~-sym (σ ⟼∀ r) (vconst κ′) ()
  ~-sym (σ ⟼∀ r) (sealᵛ σ′ u′) ()
  ~-sym (σ ⟼∀ r) (injᵛ H u′) ()
  ~-sym (σ ⟼∀ r) (U′ ⟼ r′ at m′) ()
  ~-sym (σ ⟼∀ r) (σ′ ⟼∀ r′) = λ h e → ~ᴿ-sym r r′ (h (sym e))
  ~-sym (σ ⟼∀ r) νλ ()
  ~-sym (σ ⟼∀ r) ν∀ = λ _ → tt
  ~-sym νλ (vconst κ′) ()
  ~-sym νλ (sealᵛ σ′ u′) ()
  ~-sym νλ (injᵛ H u′) ()
  ~-sym νλ (U′ ⟼ r′ at m′) = λ _ → tt
  ~-sym νλ (σ′ ⟼∀ r′) ()
  ~-sym νλ νλ = λ _ → tt
  ~-sym νλ ν∀ ()
  ~-sym ν∀ (vconst κ′) ()
  ~-sym ν∀ (sealᵛ σ′ u′) ()
  ~-sym ν∀ (injᵛ H u′) ()
  ~-sym ν∀ (U′ ⟼ r′ at m′) ()
  ~-sym ν∀ (σ′ ⟼∀ r′) = λ _ → tt
  ~-sym ν∀ νλ ()
  ~-sym ν∀ ν∀ = λ _ → tt

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

consistent-counter : ∀ {R u v m m′} → Consistentᴿ R
  → ret u m ∈ᴿ R → ret v m′ ∈ᴿ R → m ≡ m′
consistent-counter cR u∈ v∈ = proj₁ (cR _ _ u∈ v∈)

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

------------------------------------------------------------------------
-- Closures
------------------------------------------------------------------------

Λᶠ-entries : ∀ {F : 𝒱 → ℕ → ℛ} {m r r′}
  → (∀ {D D′} m → D ⊆ D′ → F D m ⊆ᴿ F D′ m)
  → (∀ D m → Consistent D → Consistentᴿ (F D m))
  → ∀ U U′ → U ≈ U → U′ ≈ U′ → U ≈ U′
  → r ∈ᴿ F (mem U) m → r′ ∈ᴿ F (mem U′) m → r ~ᴿ r′
Λᶠ-entries {m = m} Fm cF U U′ cU cU′ c r∈ r′∈ =
  cF (mem (U ++ U′)) m (≈-++ U U′ cU cU′ c) _ _
    (Fm m (λ v v∈ → ∈-++⁺ˡ v∈) _ r∈)
    (Fm m (λ v v∈ → ∈-++⁺ʳ U v∈) _ r′∈)

Λᶠ-cons : ∀ {F : 𝒱 → ℕ → ℛ}
  → (∀ {D D′} m → D ⊆ D′ → F D m ⊆ᴿ F D′ m)
  → (∀ D m → Consistent D → Consistentᴿ (F D m))
  → Consistent (Λᶠ F)
Λᶠ-cons Fm cF (vconst κ) v () v∈
Λᶠ-cons Fm cF (sealᵛ σ u) v () v∈
Λᶠ-cons Fm cF (injᵛ G u) v () v∈
Λᶠ-cons Fm cF (U ⟼ r at m) (vconst κ′) u∈ ()
Λᶠ-cons Fm cF (U ⟼ r at m) (sealᵛ σ′ u′) u∈ ()
Λᶠ-cons Fm cF (U ⟼ r at m) (injᵛ H u′) u∈ ()
Λᶠ-cons Fm cF (U ⟼ r at m) (U′ ⟼ r′ at m′) (r∈ , ne , cU) (r′∈ , ne′ , cU′) =
  λ { refl c → Λᶠ-entries Fm cF U U′ cU cU′ c r∈ r′∈ }
Λᶠ-cons Fm cF (U ⟼ r at m) (σ′ ⟼∀ r′) u∈ ()
Λᶠ-cons Fm cF (U ⟼ r at m) νλ u∈ v∈ = tt
Λᶠ-cons Fm cF (U ⟼ r at m) ν∀ u∈ ()
Λᶠ-cons Fm cF (σ ⟼∀ r) v () v∈
Λᶠ-cons Fm cF νλ (vconst κ′) u∈ ()
Λᶠ-cons Fm cF νλ (sealᵛ σ′ u′) u∈ ()
Λᶠ-cons Fm cF νλ (injᵛ H u′) u∈ ()
Λᶠ-cons Fm cF νλ (U′ ⟼ r′ at m′) u∈ v∈ = tt
Λᶠ-cons Fm cF νλ (σ′ ⟼∀ r′) u∈ ()
Λᶠ-cons Fm cF νλ νλ u∈ v∈ = tt
Λᶠ-cons Fm cF νλ ν∀ u∈ ()
Λᶠ-cons Fm cF ν∀ v () v∈

Λᴾ-cons : ∀ {F : Seal → ℛ} → (∀ σ → Consistentᴿ (F σ)) → Consistent (Λᴾ F)
Λᴾ-cons cF (vconst κ) v () v∈
Λᴾ-cons cF (sealᵛ σ u) v () v∈
Λᴾ-cons cF (injᵛ G u) v () v∈
Λᴾ-cons cF (U ⟼ r at m) v () v∈
Λᴾ-cons cF (σ ⟼∀ r) (vconst κ′) u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) (sealᵛ σ′ u′) u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) (injᵛ H u′) u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) (U′ ⟼ r′ at m′) u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) (σ′ ⟼∀ r′) r∈ r′∈ = λ { refl → cF σ r r′ r∈ r′∈ }
Λᴾ-cons cF (σ ⟼∀ r) νλ u∈ ()
Λᴾ-cons cF (σ ⟼∀ r) ν∀ u∈ v∈ = tt
Λᴾ-cons cF νλ v () v∈
Λᴾ-cons cF ν∀ (vconst κ′) u∈ ()
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
-- Seals, tags and primitives
------------------------------------------------------------------------

sealᴾ-cons : ∀ {σ D} → Consistent D → Consistent (sealᴾ σ D)
sealᴾ-cons cD (vconst κ) v () v∈
sealᴾ-cons cD (sealᵛ σ u) (vconst κ′) u∈ ()
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
injᴾ-cons cD (vconst κ) v () v∈
injᴾ-cons cD (sealᵛ σ u) v () v∈
injᴾ-cons cD (injᵛ G u) (vconst κ′) u∈ ()
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

proj-consistent : ∀ {G D m} → Consistent D → Consistentᴿ (proj G D m)
proj-consistent cD (ret u m₁) (ret v m₂) (e₁ , u∈) (e₂ , v∈) =
  trans e₁ (sym e₂) , proj₂ (cD _ _ u∈ v∈)
proj-consistent cD (ret u m₁) err (e₁ , u∈) (H , v , v∈ , H≢G) =
  ⊥-elim (H≢G (sym (proj₁ (cD _ _ u∈ v∈))))
proj-consistent cD err (ret u m₁) (H , v , v∈ , H≢G) (e₁ , u∈) =
  ⊥-elim (H≢G (sym (proj₁ (cD _ _ u∈ v∈))))
proj-consistent cD err err h h′ = tt

δ-det : ∀ {op κ₁ κ₂ κ₃ κ₄ κ κ′}
  → κ₁ ≡ κ₃ → κ₂ ≡ κ₄ → δ op κ₁ κ₂ κ → δ op κ₃ κ₄ κ′ → κ ≡ κ′
δ-det refl refl δ-add δ-add = refl
δ-det refl refl δ-and δ-and = refl

δᴾ-cons : ∀ {op D E} → Consistent D → Consistent E → Consistent (δᴾ op D E)
δᴾ-cons cD cE (vconst κ) (vconst κ′) (κ₁ , κ₂ , d₁ , e₁ , δ₁) (κ₃ , κ₄ , d₃ , e₃ , δ₃) =
  δ-det (cD _ _ d₁ d₃) (cE _ _ e₁ e₃) δ₁ δ₃
δᴾ-cons cD cE (vconst κ) (sealᵛ σ′ u′) u∈ ()
δᴾ-cons cD cE (vconst κ) (injᵛ H u′) u∈ ()
δᴾ-cons cD cE (vconst κ) (U′ ⟼ r′ at m′) u∈ ()
δᴾ-cons cD cE (vconst κ) (σ′ ⟼∀ r′) u∈ ()
δᴾ-cons cD cE (vconst κ) νλ u∈ ()
δᴾ-cons cD cE (vconst κ) ν∀ u∈ ()
δᴾ-cons cD cE (sealᵛ σ u) v () v∈
δᴾ-cons cD cE (injᵛ G u) v () v∈
δᴾ-cons cD cE (U ⟼ r at m) v () v∈
δᴾ-cons cD cE (σ ⟼∀ r) v () v∈
δᴾ-cons cD cE νλ v () v∈
δᴾ-cons cD cE ν∀ v () v∈

unsealR-cons : ∀ r {D} → Consistent D → Consistent (unsealR r D)
unsealR-cons (sealʳ σ) = unsealᴾ-consistent
unsealR-cons starʳ cD = cD

sealR-cons : ∀ r {D} → Consistent D → Consistent (sealR r D)
sealR-cons (sealʳ σ) = sealᴾ-cons
sealR-cons starʳ cD = cD

injR-cons : ∀ {Δ} {G : Ty Δ} (g : Ground G) θ {D}
  → Consistent D → Consistent (injR g θ D)
injR-cons (＇ X) θ cD with θ X
injR-cons (＇ X) θ cD | sealʳ σ = injᴾ-cons cD
injR-cons (＇ X) θ cD | starʳ = cD
injR-cons (‵ ι) θ cD = injᴾ-cons cD
injR-cons ★⇒★ θ cD = injᴾ-cons cD
injR-cons ∀★ θ cD = injᴾ-cons cD

------------------------------------------------------------------------
-- Transformers
------------------------------------------------------------------------

ConsT : Trans → Set₁
ConsT T = ∀ D m → Consistent D → Consistentᴿ (T D m)

ret-consT : ConsT retᴿ
ret-consT D m = retᴿ-consistent

point-consT : ∀ {f} → (∀ {D} → Consistent D → Consistent (f D))
  → ConsT (pointT f)
point-consT cf D m cD = retᴿ-consistent (cf cD)

seq-consT : ∀ {T₁ T₂} → ConsT T₁ → ConsT T₂ → ConsT (seqT T₁ T₂)
seq-consT c₁ c₂ D m cD = ≫=-consistent (c₁ D m cD) c₂

funProxy-consT : ∀ {a b} → MonoT a → MonoT b → ConsT a → ConsT b
  → ConsT (funProxy a b)
funProxy-consT {a} {b} ma mb ca cb E m cE =
  guard-consistent {v = νλ} {D = E} (retᴿ-consistent {n = m} (Λᶠ-cons
    (λ m′ D⊆ → ≫=-mono (ma m′ D⊆)
      (λ m₁ X⊆ → ≫=-mono (●-mono {D = E} ⊆-refl X⊆) mb))
    (λ D m′ cD → ≫=-consistent (ca D m′ cD)
      (λ D₁ m₁ cD₁ → ≫=-consistent (●-consistent {m = m₁} cE cD₁) cb))))

allProxy-consT : ∀ {k t} → (∀ σ → ConsT (t σ)) → ConsT (allProxy k t)
allProxy-consT {k} ct E m cE =
  guard-consistent {v = ν∀} {D = E} (retᴿ-consistent {n = m} (Λᴾ-cons (λ σ →
    ≫=-consistent (◆-consistent {σ = k σ} cE) (ct σ))))

genT-consT : ∀ {t} → (∀ σ → ConsT (t σ)) → ConsT (genT t)
genT-consT ct E m cE =
  retᴿ-consistent (Λᴾ-cons (λ σ → ct σ E (suc σ) cE))

inst◆-consT : ConsT inst◆
inst◆-consT E m cE = ◆-consistent cE

errT-consT : ConsT errT
errT-consT E m cE = errᴿ-consistent

------------------------------------------------------------------------
-- Reveals, conversions and casts
------------------------------------------------------------------------

mutual
  revV-cons : ∀ {Δ} (C : Ty Δ) X θ → ConsT (revV C X θ)
  revV-cons (＇ Y) X θ D m cD with X ≟ Y
  revV-cons (＇ Y) X θ D m cD | yes _ =
    retᴿ-consistent (unsealR-cons (θ X) cD)
  revV-cons (＇ Y) X θ D m cD | no _ = retᴿ-consistent cD
  revV-cons (‵ ι) X θ = ret-consT
  revV-cons ★ X θ = ret-consT
  revV-cons (A ⇒ B) X θ =
    funProxy-consT (conV-mono A X θ) (revV-mono B X θ)
      (conV-cons A X θ) (revV-cons B X θ)
  revV-cons (`∀ A) X θ =
    allProxy-consT (λ σ →
      seq-consT (revV-cons A fzero (sealʳ (suc σ) •ʳ θ))
                (revV-cons A (fsuc X) (sealʳ σ •ʳ θ)))

  conV-cons : ∀ {Δ} (C : Ty Δ) X θ → ConsT (conV C X θ)
  conV-cons (＇ Y) X θ D m cD with X ≟ Y
  conV-cons (＇ Y) X θ D m cD | yes _ =
    retᴿ-consistent (sealR-cons (θ X) cD)
  conV-cons (＇ Y) X θ D m cD | no _ = retᴿ-consistent cD
  conV-cons (‵ ι) X θ = ret-consT
  conV-cons ★ X θ = ret-consT
  conV-cons (A ⇒ B) X θ =
    funProxy-consT (revV-mono A X θ) (conV-mono B X θ)
      (revV-cons A X θ) (conV-cons B X θ)
  conV-cons (`∀ A) X θ =
    allProxy-consT (λ σ →
      seq-consT (revV-cons A fzero (sealʳ (suc σ) •ʳ θ))
                (conV-cons A (fsuc X) (sealʳ σ •ʳ θ)))

mutual
  conv↑-cons : ∀ {Δ A B} (c : Conv↑ Δ A B) θ → ConsT (⟦ c ⟧↑ θ)
  conv↑-cons (unseal X R) θ D m cD = retᴿ-consistent (unsealR-cons (θ X) cD)
  conv↑-cons (c ↦↑ d) θ =
    funProxy-consT (conv↓-mono c θ) (conv↑-mono d θ)
      (conv↓-cons c θ) (conv↑-cons d θ)
  conv↑-cons (`∀↑_ {A = C} c) θ =
    allProxy-consT (λ σ →
      seq-consT (revV-cons C fzero (sealʳ (suc σ) •ʳ θ))
                (conv↑-cons c (sealʳ σ •ʳ θ)))
  conv↑-cons (id↑ A) θ = ret-consT

  conv↓-cons : ∀ {Δ A B} (c : Conv↓ Δ A B) θ → ConsT (⟦ c ⟧↓ θ)
  conv↓-cons (seal X R) θ D m cD = retᴿ-consistent (sealR-cons (θ X) cD)
  conv↓-cons (c ↦↓ d) θ =
    funProxy-consT (conv↑-mono c θ) (conv↓-mono d θ)
      (conv↑-cons c θ) (conv↓-cons d θ)
  conv↓-cons (`∀↓_ {A = C} c) θ =
    allProxy-consT (λ σ →
      seq-consT (revV-cons C fzero (sealʳ (suc σ) •ʳ θ))
                (conv↓-cons c (sealʳ σ •ʳ θ)))
  conv↓-cons (id↓ A) θ = ret-consT

projR-consT : ∀ {Δ} {G : Ty Δ} (g : Ground G) θ → ConsT (projR g θ)
projR-consT (＇ X) θ D m cD with θ X
projR-consT (＇ X) θ D m cD | sealʳ σ = proj-consistent cD
projR-consT (＇ X) θ D m cD | starʳ = retᴿ-consistent cD
projR-consT (‵ ι) θ D m cD = proj-consistent cD
projR-consT ★⇒★ θ D m cD = proj-consistent cD
projR-consT ∀★ θ D m cD = proj-consistent cD

mutual
  cast-cons : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} (c : μ ⊢ A ∼ B) θ
    → ConsT (⟦ c ⟧ᶜ θ)
  cast-cons (id a) θ = ret-consT
  cast-cons (c ↦ d) θ =
    funProxy-consT (cast-mono c θ) (cast-mono d θ)
      (cast-cons c θ) (cast-cons d θ)
  cast-cons (∀ᶜ c) θ = allProxy-consT (λ σ → cast-cons c (sealʳ σ •ʳ θ))
  cast-cons (_! ⦃ Gᵍ ⦄ c) θ =
    seq-consT (cast-cons c θ) (point-consT (injR-cons Gᵍ θ))
  cast-cons (？_ ⦃ Gᵍ ⦄ c) θ = seq-consT (projR-consT Gᵍ θ) (cast-cons c θ)
  cast-cons ((inst_ {A = A} c) B≢★) θ D m =
    seq-consT inst◆-consT (instBody-cons A c θ m) D m
  cast-cons ((gen c) A≢★) θ = genT-consT (λ σ → cast-cons c (sealʳ σ •ʳ θ))
  cast-cons bot-elim θ =
    allProxy-consT (λ σ → point-consT (injᴾ-cons {G = gσ σ}))
  cast-cons bot-intro θ = errT-consT

  instBody-cons : ∀ {Δ} {μ : Env∼ Δ} (A : Ty (suc Δ)) {B : Ty Δ}
    → (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B) → ∀ θ m → ConsT (instBodyT A c θ m)
  instBody-cons A c θ m =
    seq-consT
      (conv↑-cons 〖 fzero , ＇ fsuc fzero ↑ renameᵗ (extᵗ fsuc) A 〗
        (sealʳ (suc m) •ʳ sealʳ m •ʳ θ))
      (seq-consT (conv↑-cons 〖 fzero , ★ ↑ A 〗 (sealʳ m •ʳ θ))
        (cast-cons c (starʳ •ʳ θ)))

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

ext-consistent : ∀ {D ρ} → Consistent D → (∀ x → Consistent (ρ x))
  → ∀ x → Consistent ((D • ρ) x)
ext-consistent cD cρ zero = cD
ext-consistent cD cρ (suc x) = cρ x

⟦⟧-consistent : ∀ {Δ} (M : Term Δ) θ {ρ n} → (∀ x → Consistent (ρ x))
  → Consistentᴿ (⟦ M ⟧ θ ρ n)
⟦⟧-consistent (` x) θ cρ = retᴿ-consistent (cρ x)
⟦⟧-consistent (ƛ M) θ cρ =
  retᴿ-consistent (Λᶠ-cons
    (λ m D⊆ → ⟦⟧-mono M (ext-⊆ₑ D⊆ ⊆ₑ-refl))
    (λ D m cD → ⟦⟧-consistent M θ {n = m} (ext-consistent cD cρ)))
⟦⟧-consistent (L · M) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent L θ {n = n} cρ) (λ F n₁ cF →
    ≫=-consistent (⟦⟧-consistent M θ {n = n₁} cρ) (λ E n₂ cE →
      ●-consistent {m = n₂} cF cE))
⟦⟧-consistent (Λ M) θ cρ =
  retᴿ-consistent (Λᴾ-cons (λ σ →
    ⟦⟧-consistent M (sealʳ σ •ʳ θ) {n = suc σ} cρ))
⟦⟧-consistent (M ⦂∀ B [ A ]) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (λ F n₁ cF →
    ≫=-consistent (◆-consistent {σ = n₁} cF)
      (conv↑-cons 〖 fzero , ⇑ᵗ A ↑ B 〗 (sealʳ n₁ •ʳ θ)))
⟦⟧-consistent ($ κ) θ cρ = retᴿ-consistent (⌈⌉-consistent refl)
⟦⟧-consistent (L ⊕[ op ] M) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent L θ {n = n} cρ) (λ D n₁ cD →
    ≫=-consistent (⟦⟧-consistent M θ {n = n₁} cρ) (λ E n₂ cE →
      retᴿ-consistent {n = n₂} (δᴾ-cons {op = op} cD cE)))
⟦⟧-consistent (M ⟨ c ⟩) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (cast-cons c θ)
⟦⟧-consistent (M ↑ c) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (conv↑-cons c θ)
⟦⟧-consistent (M ↓ c) θ {n = n} cρ =
  ≫=-consistent (⟦⟧-consistent M θ {n = n} cρ) (conv↓-cons c θ)
⟦⟧-consistent blame θ cρ = errᴿ-consistent

-- the environment of a closed term
ρ₀-consistent : ∀ x → Consistent (ρ₀ x)
ρ₀-consistent x u v ()
