module proof.Denot.BetaAllCounterProbe where

-- File Charter:
--   * A counterexample record (notes/denotational-dgg.md, Section 8c):
--     with seals allocated at an exact counter, the denotation of
--     `Denot.Denotation` is not closed under subject expansion for
--     `β-∀`.
--   * The redex `(V ⟨ ∀ᶜ (inst d) ⟩) ⦂∀ (★ ⇒ ★) [ 𝔹 ]` steps (purely)
--     to `(V ⦂∀ ∀X.(X ⇒ X) [ 𝔹 ]) ⟨ (inst d) [ 𝔹 ]ᶜ ⟩`, where
--     V = ΛY. ΛX. λx. x.  In the reduct the `inst` instantiates a value
--     that passed through the reveal `〖 0 , 𝔹 ↑ ∀X.(X ⇒ X) 〗`, a
--     ∀-conversion, which creates one more seal when instantiated (as
--     `β-reveal-∀` does).  In the redex the `inst` instantiates V's own
--     body directly.  So the reduct's results end at counter 4 and the
--     redex's at counter 3: `⟦ reduct ⟧ ⊄ ⟦ redex ⟧`.
--   * The allocation of a term is therefore not determined by its
--     denotation's structure alone; see the note for the consequences.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_)

open import Types
open import Consistency
open import Conversion
open import CastTerms
open import Reduction
open import Denot.GraphModel
open import Denot.Denotation

------------------------------------------------------------------------
-- The terms
------------------------------------------------------------------------

-- inside the inst: X ⇒ X ∼ ★ ⇒ ★, with X read as ★
μ₀ : Env∼ 0
μ₀ = idᶜ

★⇒★₁ : Ty 1
★⇒★₁ = ★ ⇒ ★

X⇒X : Ty 2
X⇒X = ＇ zero ⇒ ＇ zero

d : instᵐ (extᵐ μ₀) ⊢ X⇒X ∼ ⇑ᵗ ★⇒★₁
d = (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄ (id (＇ zero))
      ⦃ nonstar-X ⦄)
  ↦ (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄ (id (＇ zero))
      ⦃ nonstar-X ⦄)

c : extᵐ μ₀ ⊢ `∀ X⇒X ∼ ★⇒★₁
c = (inst_ ⦃ nonvar-fun ⦄ ⦃ ∈-fun-left var-∈ ⦄ d) (λ ())

V : Term 0
V = Λ (Λ (ƛ (` 0)))

vV : Value V
vV = Λ (Λ (ƛ (` 0)))

C : Ty 0
C = ‵ `𝔹

redex : Term 0
redex = (V ⟨ ∀ᶜ c ⟩) ⦂∀ ★⇒★₁ [ C ]

reduct : Term 0
reduct = (V ⦂∀ `∀ X⇒X [ C ]) ⟨ c [ C ]ᶜ ⟩

step : redex —→ reduct
step = β-∀ vV refl

------------------------------------------------------------------------
-- Results at a single counter
------------------------------------------------------------------------

-- every value result of R ends at counter k
AtOnly : ℛ → ℕ → Set
AtOnly R k = ∀ v m → ret v m ∈ᴿ R → m ≡ k

atOnly-ret : ∀ D n → AtOnly (retᴿ D n) n
atOnly-ret D n v m (eq , _) = eq

atOnly-⊆ : ∀ {R S k} → R ⊆ᴿ S → AtOnly S k → AtOnly R k
atOnly-⊆ R⊆ aS v m r∈ = aS v m (R⊆ (ret v m) r∈)

atOnly-≫= : ∀ (R : ℛ) (K : 𝒱 → ℕ → ℛ) {k k′} → AtOnly R k
  → AtOnly (K (⌊ R ⌋ k) k) k′ → AtOnly (R ≫= K) k′
atOnly-≫= R K aR aK v m (inj₁ (() , _))
atOnly-≫= R K aR aK v m (inj₂ (j , (u , u∈) , r∈))
  with aR u j u∈
... | refl = aK v m r∈

atOnly-guard : ∀ u D R {k} → AtOnly R k → AtOnly (guard u D R) k
atOnly-guard u D R aR v m (_ , r∈) = aR v m r∈

atOnly-fun : ∀ a b E m → AtOnly (funProxy a b E m) m
atOnly-fun a b E m v m′ (_ , eq , _) = eq

-- a conversion returns at the counter it starts from
atOnly↑ : ∀ {Δ A B} (k : Conv↑ Δ A B) θ E m → AtOnly (⟦ k ⟧↑ θ E m) m
atOnly↓ : ∀ {Δ A B} (k : Conv↓ Δ A B) θ E m → AtOnly (⟦ k ⟧↓ θ E m) m
atOnly↑ (unseal X R) θ E m v m′ (eq , _) = eq
atOnly↑ (k ↦↑ k′) θ E m v m′ (_ , eq , _) = eq
atOnly↑ (`∀↑ k) θ E m v m′ (_ , eq , _) = eq
atOnly↑ (id↑ A) θ E m v m′ (eq , _) = eq
atOnly↓ (seal X R) θ E m v m′ (eq , _) = eq
atOnly↓ (k ↦↓ k′) θ E m v m′ (_ , eq , _) = eq
atOnly↓ (`∀↓ k) θ E m v m′ (_ , eq , _) = eq
atOnly↓ (id↓ A) θ E m v m′ (eq , _) = eq

------------------------------------------------------------------------
-- The redex returns only at counter 3
------------------------------------------------------------------------

-- V's results
𝒱V : 𝒱
𝒱V = ⌊ ⟦ V ⟧ θ₀ ρ₀ 0 ⌋ 0

-- the redex's final reveal, at ★ ⇒ ★
revB : Seal → 𝒱 → ℕ → ℛ
revB σ = ⟦ 〖 zero , ⇑ᵗ C ↑ ★⇒★₁ 〗 ⟧↑ (sealʳ σ •ʳ θ₀)

-- the two reveals of `inst d`, instantiated at seals 1 and 2
rev₁ rev₂ : 𝒱 → ℕ → ℛ
rev₁ = ⟦ 〖 zero , ＇ suc zero ↑ renameᵗ (extᵗ suc) X⇒X 〗 ⟧↑
         (sealʳ 2 •ʳ sealʳ 1 •ʳ sealʳ 0 •ʳ θ₀)
rev₂ = ⟦ 〖 zero , ★ ↑ X⇒X 〗 ⟧↑ (sealʳ 1 •ʳ sealʳ 0 •ʳ θ₀)

rev₁-at : ∀ E m → AtOnly (rev₁ E m) m
rev₁-at = atOnly↑ 〖 zero , ＇ suc zero ↑ renameᵗ (extᵗ suc) X⇒X 〗
  (sealʳ 2 •ʳ sealʳ 1 •ʳ sealʳ 0 •ʳ θ₀)

rev₂-at : ∀ E m → AtOnly (rev₂ E m) m
rev₂-at = atOnly↑ 〖 zero , ★ ↑ X⇒X 〗 (sealʳ 1 •ʳ sealʳ 0 •ʳ θ₀)

revB-at : ∀ σ E m → AtOnly (revB σ E m) m
revB-at σ = atOnly↑ 〖 zero , ⇑ᵗ C ↑ ★⇒★₁ 〗 (sealʳ σ •ʳ θ₀)

castV : 𝒱 → ℕ → ℛ
castV = ⟦ ∀ᶜ c ⟧ᶜ θ₀

-- the redex instantiates the cast value at 0: V at 0, then inst d
redex◆0 : ⌊ ⟦ V ⟨ ∀ᶜ c ⟩ ⟧ θ₀ ρ₀ 0 ⌋ 0 ◆ 0
  ⊆ᴿ ((𝒱V ◆ 0) ≫= ⟦ c ⟧ᶜ (sealʳ 0 •ʳ θ₀))
redex◆0 r (inj₁ (() , _))
redex◆0 r (inj₂ (j , (w , refl , w∈) , ν∈ , refl , r∈)) = r∈

-- inst d at counter 1 instantiates V's body at seal 2, ending at 3
inst-at-3 : AtOnly (⟦ c ⟧ᶜ (sealʳ 0 •ʳ θ₀) (⌊ 𝒱V ◆ 0 ⌋ 1) 1) 3
inst-at-3 =
  atOnly-≫= (⌊ 𝒱V ◆ 0 ⌋ 1 ◆ 2) K₁
    (λ { v m (refl , refl , e , _) → e })
    (atOnly-≫= (rev₁ E₁ 3) K₂ (rev₁-at E₁ 3)
      (atOnly-≫= (rev₂ E₂ 3) K₃ (rev₂-at E₂ 3)
        (λ { v m (_ , eq , _) → eq })))
  where
  E₁ : 𝒱
  E₁ = ⌊ ⌊ 𝒱V ◆ 0 ⌋ 1 ◆ 2 ⌋ 3
  E₂ : 𝒱
  E₂ = ⌊ rev₁ E₁ 3 ⌋ 3
  K₃ : 𝒱 → ℕ → ℛ
  K₃ = ⟦ d ⟧ᶜ (starʳ •ʳ sealʳ 0 •ʳ θ₀)
  K₂ : 𝒱 → ℕ → ℛ
  K₂ E₂ m₂ = rev₂ E₂ m₂ ≫= K₃
  K₁ : 𝒱 → ℕ → ℛ
  K₁ E₁ m₁ = rev₁ E₁ m₁ ≫= K₂

redex-at-3 : AtOnly (⟦ redex ⟧ θ₀ ρ₀ 0) 3
redex-at-3 =
  atOnly-≫= (⟦ V ⟨ ∀ᶜ c ⟩ ⟧ θ₀ ρ₀ 0) K cast-at-0
    (atOnly-≫= (⌊ ⟦ V ⟨ ∀ᶜ c ⟩ ⟧ θ₀ ρ₀ 0 ⌋ 0 ◆ 0) (revB 0)
      (atOnly-⊆ redex◆0
        (atOnly-≫= (𝒱V ◆ 0) (⟦ c ⟧ᶜ (sealʳ 0 •ʳ θ₀))
          (λ { v m (refl , e , _) → e }) inst-at-3))
      (revB-at 0 (⌊ ⌊ ⟦ V ⟨ ∀ᶜ c ⟩ ⟧ θ₀ ρ₀ 0 ⌋ 0 ◆ 0 ⌋ 3) 3))
  where
  K : 𝒱 → ℕ → ℛ
  K F n₁ = (F ◆ n₁) ≫= revB n₁
  cast-at-0 : AtOnly (⟦ V ⟨ ∀ᶜ c ⟩ ⟧ θ₀ ρ₀ 0) 0
  cast-at-0 = atOnly-≫= (⟦ V ⟧ θ₀ ρ₀ 0) castV (λ { v m (eq , _) → eq })
    (λ { v m (_ , eq , _) → eq })

------------------------------------------------------------------------
-- The reduct has a result at counter 4
------------------------------------------------------------------------

-- V instantiated at 0 and then at 3 (inside the ∀-conversion's proxy)
V◆0◆3 : ret νλ 4 ∈ᴿ (⌊ 𝒱V ◆ 0 ⌋ 1 ◆ 3)
V◆0◆3 = refl , refl , refl , tt

-- the type application reveals V's body on ∀X.(X ⇒ X): a ∀-proxy whose
-- instantiation at 2 instantiates the body at 3
tyapp∈ : ret (2 ⟼∀ ret νλ 4) 1 ∈ᴿ ⟦ V ⦂∀ `∀ X⇒X [ C ] ⟧ θ₀ ρ₀ 0
tyapp∈ =
  inj₂ (0 , (0 ⟼∀ ret ν∀ 1 , refl , refl , tt) ,
    inj₂ (1 , (ν∀ , refl , refl , tt) ,
      ((refl , refl , tt) , refl ,
        inj₂ (4 , (νλ , V◆0◆3) ,
          inj₂ (4 , (νλ , V◆0◆3 , refl , tt) ,
            ((V◆0◆3 , refl , tt) , refl , tt))))))

-- the substituted inst creates seal 1 and instantiates the proxy at 2
reduct∈ : ret νλ 4 ∈ᴿ ⟦ reduct ⟧ θ₀ ρ₀ 0
reduct∈ =
  inj₂ (1 , (2 ⟼∀ ret νλ 4 , tyapp∈) ,
    inj₂ (4 , (νλ , tyapp∈) ,
      inj₂ (4 , (νλ , r₁) ,
        inj₂ (4 , (νλ , r₂) , (r₂ , refl , tt)))))
  where
  r₁ = (tyapp∈ , refl , tt)
  r₂ = (r₁ , refl , tt)

------------------------------------------------------------------------
-- Subject expansion fails
------------------------------------------------------------------------

no-expansion : ¬ (⟦ reduct ⟧ θ₀ ρ₀ 0 ⊆ᴿ ⟦ redex ⟧ θ₀ ρ₀ 0)
no-expansion ⊆ with redex-at-3 νλ 4 (⊆ (ret νλ 4) reduct∈)
... | ()
