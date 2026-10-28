module proof.Denot.DenotRename where

-- File Charter:
--   * The denotation is invariant under injective renaming of type
--     variables, for reveals (`revV`/`conV`), conversion terms, the
--     conversions `〖_,_↑_〗`/`makeConceal` built for any representation,
--     casts, and terms.  Reduction renames the rest of a term whenever it
--     allocates (`⇑ᵗᵐ`), so soundness needs this.
--   * Transformers are compared by refinement (`TRef`: monotone from
--     one to the other) and equivalence (`≈ᵀ`: refinement both ways);
--     the combinators of the denotation preserve both.

open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency
open import Conversion
open import Denot.GraphModel
open import Denot.Denotation
open import proof.Denot.DenotProps
open import proof.ImprecisionConsistency
  using (ext-injective; toRenameᵗ-injective)
open import CastTerms using (Term; `_; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_;
  _⟨_⟩; _↑_; _↓_; blame; renameᵗᵐ)

------------------------------------------------------------------------
-- Refinement and equivalence of transformers
------------------------------------------------------------------------

TRef : Trans → Trans → Set₁
TRef T₁ T₂ = ∀ {D D′} m → D ⊆ D′ → T₁ D m ⊆ᴿ T₂ D′ m

infix 4 _≈ᵀ_

_≈ᵀ_ : Trans → Trans → Set₁
T₁ ≈ᵀ T₂ = TRef T₁ T₂ × TRef T₂ T₁

SRef : (𝒱 → 𝒱) → (𝒱 → 𝒱) → Set₁
SRef f g = ∀ {D D′} → D ⊆ D′ → f D ⊆ g D′

≈ᵀ-refl : ∀ {T} → MonoT T → T ≈ᵀ T
≈ᵀ-refl mT = mT , mT

≈ᵀ-sym : ∀ {T₁ T₂} → T₁ ≈ᵀ T₂ → T₂ ≈ᵀ T₁
≈ᵀ-sym (r , l) = l , r

ret≈ : retᴿ ≈ᵀ retᴿ
ret≈ = ret-monoT , ret-monoT

point≈ : ∀ {f g} → SRef f g → SRef g f → pointT f ≈ᵀ pointT g
point≈ fg gf = (λ m E⊆ → retᴿ-mono (fg E⊆)) , (λ m E⊆ → retᴿ-mono (gf E⊆))

seqRef : ∀ {T₁ T₁′ T₂ T₂′} → TRef T₁ T₁′ → TRef T₂ T₂′
  → TRef (seqT T₁ T₂) (seqT T₁′ T₂′)
seqRef r₁ r₂ m E⊆ = ≫=-mono (r₁ m E⊆) r₂

seq≈ : ∀ {T₁ T₁′ T₂ T₂′} → T₁ ≈ᵀ T₁′ → T₂ ≈ᵀ T₂′
  → seqT T₁ T₂ ≈ᵀ seqT T₁′ T₂′
seq≈ (r₁ , l₁) (r₂ , l₂) = seqRef r₁ r₂ , seqRef l₁ l₂

funRef : ∀ {a a′ b b′} → (∀ D m → a D m ⊆ᴿ a′ D m) → TRef b b′
  → TRef (funProxy a b) (funProxy a′ b′)
funRef aa bb m E⊆ =
  guard-mono E⊆ (retᴿ-mono (Λᶠ-mono (λ D m′ →
    ≫=-mono (aa D m′) (λ m₁ D⊆ → ≫=-mono (●-mono E⊆ D⊆) bb))))

fun≈ : ∀ {a a′ b b′} → a ≈ᵀ a′ → b ≈ᵀ b′
  → funProxy a b ≈ᵀ funProxy a′ b′
fun≈ (ra , la) (rb , lb) =
  funRef (λ D m → ra m ⊆-refl) rb , funRef (λ D m → la m ⊆-refl) lb

allRef : ∀ {k t t′} → (∀ σ → TRef (t σ) (t′ σ))
  → TRef (allProxy k t) (allProxy k t′)
allRef tt′ m E⊆ =
  guard-mono E⊆ (retᴿ-mono (Λᴾ-mono (λ σ → ≫=-mono (◆-mono E⊆) (tt′ σ))))

all≈ : ∀ {k t t′} → (∀ σ → t σ ≈ᵀ t′ σ) → allProxy k t ≈ᵀ allProxy k t′
all≈ e = allRef (λ σ → proj₁ (e σ)) , allRef (λ σ → proj₂ (e σ))

genRef : ∀ {t t′} → (∀ σ → TRef (t σ) (t′ σ)) → TRef (genT t) (genT t′)
genRef tt′ m E⊆ = retᴿ-mono (Λᴾ-mono (λ σ → tt′ σ (suc σ) E⊆))

gen≈ : ∀ {t t′} → (∀ σ → t σ ≈ᵀ t′ σ) → genT t ≈ᵀ genT t′
gen≈ e = genRef (λ σ → proj₁ (e σ)) , genRef (λ σ → proj₂ (e σ))

------------------------------------------------------------------------
-- Renamings and environments
------------------------------------------------------------------------

Inj : ∀ {Δ Δ′} → Δ ⇒ʳ Δ′ → Set
Inj ρ = ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y

-- θ₂ read through ρ is θ₁
EnvRen : ∀ {Δ Δ′} → Δ ⇒ʳ Δ′ → REnv Δ → REnv Δ′ → Set
EnvRen ρ θ₁ θ₂ = ∀ X → θ₂ (ρ X) ≡ θ₁ X

ext-EnvRen : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} (r : Rep)
  → EnvRen ρ θ₁ θ₂ → EnvRen (extᵗ ρ) (r •ʳ θ₁) (r •ʳ θ₂)
ext-EnvRen r e fzero = refl
ext-EnvRen r e (fsuc X) = e X

unsealR≈ : ∀ {r r′} → r ≡ r′ → SRef (unsealR r) (unsealR r′)
unsealR≈ {r = sealʳ σ} refl = unsealᴾ-mono
unsealR≈ {r = starʳ} refl D⊆ = D⊆

sealR≈ : ∀ {r r′} → r ≡ r′ → SRef (sealR r) (sealR r′)
sealR≈ {r = sealʳ σ} refl = sealᴾ-mono
sealR≈ {r = starʳ} refl D⊆ = D⊆

------------------------------------------------------------------------
-- Reveals at one variable
------------------------------------------------------------------------

private
  dec-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} → Inj ρ → ∀ X Y
    → (X ≡ Y → ρ X ≡ ρ Y) × (ρ X ≡ ρ Y → X ≡ Y)
  dec-ren inj X Y = cong _ , inj

mutual
  revV-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} → Inj ρ → EnvRen ρ θ₁ θ₂
    → ∀ (C : Ty Δ) X → revV C X θ₁ ≈ᵀ revV (renameᵗ ρ C) (ρ X) θ₂
  revV-ren {ρ = ρ} inj e (＇ Y) X with X ≟ Y | ρ X ≟ ρ Y
  revV-ren {ρ = ρ} inj e (＇ Y) X | yes refl | yes _ =
    point≈ (unsealR≈ (sym (e X))) (unsealR≈ (e X))
  revV-ren {ρ = ρ} inj e (＇ Y) X | yes refl | no ne = ⊥-elim (ne refl)
  revV-ren {ρ = ρ} inj e (＇ Y) X | no ne | yes eq = ⊥-elim (ne (inj eq))
  revV-ren {ρ = ρ} inj e (＇ Y) X | no _ | no _ = ret≈
  revV-ren inj e (‵ ι) X = ret≈
  revV-ren inj e ★ X = ret≈
  revV-ren inj e (A ⇒ B) X = fun≈ (conV-ren inj e A X) (revV-ren inj e B X)
  revV-ren inj e (`∀ A) X =
    all≈ (λ σ →
      seq≈ (revV-ren (ext-injective inj) (ext-EnvRen (sealʳ (suc σ)) e)
              A fzero)
           (revV-ren (ext-injective inj) (ext-EnvRen (sealʳ σ) e)
              A (fsuc X)))

  conV-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} → Inj ρ → EnvRen ρ θ₁ θ₂
    → ∀ (C : Ty Δ) X → conV C X θ₁ ≈ᵀ conV (renameᵗ ρ C) (ρ X) θ₂
  conV-ren {ρ = ρ} inj e (＇ Y) X with X ≟ Y | ρ X ≟ ρ Y
  conV-ren {ρ = ρ} inj e (＇ Y) X | yes refl | yes _ =
    point≈ (sealR≈ (sym (e X))) (sealR≈ (e X))
  conV-ren {ρ = ρ} inj e (＇ Y) X | yes refl | no ne = ⊥-elim (ne refl)
  conV-ren {ρ = ρ} inj e (＇ Y) X | no ne | yes eq = ⊥-elim (ne (inj eq))
  conV-ren {ρ = ρ} inj e (＇ Y) X | no _ | no _ = ret≈
  conV-ren inj e (‵ ι) X = ret≈
  conV-ren inj e ★ X = ret≈
  conV-ren inj e (A ⇒ B) X = fun≈ (revV-ren inj e A X) (conV-ren inj e B X)
  conV-ren inj e (`∀ A) X =
    all≈ (λ σ →
      seq≈ (revV-ren (ext-injective inj) (ext-EnvRen (sealʳ (suc σ)) e)
              A fzero)
           (conV-ren (ext-injective inj) (ext-EnvRen (sealʳ σ) e)
              A (fsuc X)))

------------------------------------------------------------------------
-- Replacing a variable commutes with injective renaming
------------------------------------------------------------------------

rename-replace : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} → Inj ρ
  → ∀ X (R A : Ty Δ)
  → renameᵗ ρ (replaceTy X R A) ≡ replaceTy (ρ X) (renameᵗ ρ R) (renameᵗ ρ A)
rename-replace {ρ = ρ} inj X R (＇ Y) with X ≟ Y | ρ X ≟ ρ Y
rename-replace {ρ = ρ} inj X R (＇ Y) | yes refl | yes refl = refl
rename-replace {ρ = ρ} inj X R (＇ Y) | yes refl | no ne = ⊥-elim (ne refl)
rename-replace {ρ = ρ} inj X R (＇ Y) | no ne | yes eq = ⊥-elim (ne (inj eq))
rename-replace {ρ = ρ} inj X R (＇ Y) | no _ | no _ = refl
rename-replace inj X R (‵ ι) = refl
rename-replace inj X R ★ = refl
rename-replace inj X R (A ⇒ B) =
  cong₂ _⇒_ (rename-replace inj X R A) (rename-replace inj X R B)
rename-replace {ρ = ρ} inj X R (`∀ A) =
  cong `∀
    (trans (rename-replace (ext-injective inj) (fsuc X) (⇑ᵗ R) A)
      (cong (λ T → replaceTy (fsuc (ρ X)) T (renameᵗ (extᵗ ρ) A))
        (renameᵗ-shift ρ R)))

------------------------------------------------------------------------
-- Conversion terms
------------------------------------------------------------------------

revV≡ : ∀ {Δ} {C C′ : Ty Δ} X θ → C ≡ C′ → revV C X θ ≈ᵀ revV C′ X θ
revV≡ {C = C} X θ refl = ≈ᵀ-refl (revV-mono C X θ)

mutual
  conv↑-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} → Inj ρ → EnvRen ρ θ₁ θ₂
    → ∀ {A B} (c : Conv↑ Δ A B) → ⟦ c ⟧↑ θ₁ ≈ᵀ ⟦ rename↑ ρ c ⟧↑ θ₂
  conv↑-ren inj e (unseal X R) =
    point≈ (unsealR≈ (sym (e X))) (unsealR≈ (e X))
  conv↑-ren inj e (c ↦↑ d) = fun≈ (conv↓-ren inj e c) (conv↑-ren inj e d)
  conv↑-ren inj e (`∀↑_ {A = C} c) =
    all≈ (λ σ →
      seq≈ (revV-ren (ext-injective inj) (ext-EnvRen (sealʳ (suc σ)) e)
              C fzero)
           (conv↑-ren (ext-injective inj) (ext-EnvRen (sealʳ σ) e) c))
  conv↑-ren inj e (id↑ A) = ret≈

  conv↓-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} → Inj ρ → EnvRen ρ θ₁ θ₂
    → ∀ {A B} (c : Conv↓ Δ A B) → ⟦ c ⟧↓ θ₁ ≈ᵀ ⟦ rename↓ ρ c ⟧↓ θ₂
  conv↓-ren inj e (seal X R) =
    point≈ (sealR≈ (sym (e X))) (sealR≈ (e X))
  conv↓-ren inj e (c ↦↓ d) = fun≈ (conv↑-ren inj e c) (conv↓-ren inj e d)
  conv↓-ren inj e (`∀↓_ {A = C} c) =
    all≈ (λ σ →
      seq≈ (revV-ren (ext-injective inj) (ext-EnvRen (sealʳ (suc σ)) e)
              C fzero)
           (conv↓-ren (ext-injective inj) (ext-EnvRen (sealʳ σ) e) c))
  conv↓-ren inj e (id↓ A) = ret≈

------------------------------------------------------------------------
-- The conversions built for a type application, any representation
------------------------------------------------------------------------

mutual
  reveal-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} → Inj ρ → EnvRen ρ θ₁ θ₂
    → ∀ (B : Ty Δ) X R
    → ⟦ 〖 X , R ↑ B 〗 ⟧↑ θ₁
      ≈ᵀ ⟦ 〖 ρ X , renameᵗ ρ R ↑ renameᵗ ρ B 〗 ⟧↑ θ₂
  reveal-ren {ρ = ρ} inj e (＇ Y) X R with X ≟ Y | ρ X ≟ ρ Y
  reveal-ren {ρ = ρ} inj e (＇ Y) X R | yes refl | yes refl =
    point≈ (unsealR≈ (sym (e X))) (unsealR≈ (e X))
  reveal-ren {ρ = ρ} inj e (＇ Y) X R | yes refl | no ne = ⊥-elim (ne refl)
  reveal-ren {ρ = ρ} inj e (＇ Y) X R | no ne | yes eq = ⊥-elim (ne (inj eq))
  reveal-ren {ρ = ρ} inj e (＇ Y) X R | no _ | no _ = ret≈
  reveal-ren inj e (‵ ι) X R = ret≈
  reveal-ren inj e ★ X R = ret≈
  reveal-ren inj e (A ⇒ B) X R =
    fun≈ (conceal-ren inj e A X R) (reveal-ren inj e B X R)
  reveal-ren {ρ = ρ} {θ₁} {θ₂} inj e (`∀ A) X R =
    all≈ (λ σ →
      seq≈ (revV-ren (ext-injective inj) (ext-EnvRen (sealʳ (suc σ)) e)
              A fzero)
           (≈ᵀ-trans′
             (reveal-ren (ext-injective inj) (ext-EnvRen (sealʳ σ) e)
               A (fsuc X) (⇑ᵗ R))
             (reveal≡ (renameᵗ (extᵗ ρ) A) (fsuc (ρ X))
               (renameᵗ-shift ρ R) (sealʳ σ •ʳ θ₂))))

  conceal-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} → Inj ρ → EnvRen ρ θ₁ θ₂
    → ∀ (B : Ty Δ) X R
    → ⟦ makeConceal X R B ⟧↓ θ₁
      ≈ᵀ ⟦ makeConceal (ρ X) (renameᵗ ρ R) (renameᵗ ρ B) ⟧↓ θ₂
  conceal-ren {ρ = ρ} inj e (＇ Y) X R with X ≟ Y | ρ X ≟ ρ Y
  conceal-ren {ρ = ρ} inj e (＇ Y) X R | yes refl | yes refl =
    point≈ (sealR≈ (sym (e X))) (sealR≈ (e X))
  conceal-ren {ρ = ρ} inj e (＇ Y) X R | yes refl | no ne = ⊥-elim (ne refl)
  conceal-ren {ρ = ρ} inj e (＇ Y) X R | no ne | yes eq = ⊥-elim (ne (inj eq))
  conceal-ren {ρ = ρ} inj e (＇ Y) X R | no _ | no _ = ret≈
  conceal-ren inj e (‵ ι) X R = ret≈
  conceal-ren inj e ★ X R = ret≈
  conceal-ren inj e (A ⇒ B) X R =
    fun≈ (reveal-ren inj e A X R) (conceal-ren inj e B X R)
  conceal-ren {ρ = ρ} {θ₁} {θ₂} inj e (`∀ A) X R =
    all≈ (λ σ →
      seq≈ (≈ᵀ-trans′
              (revV-ren (ext-injective inj) (ext-EnvRen (sealʳ (suc σ)) e)
                (replaceTy (fsuc X) (⇑ᵗ R) A) fzero)
              (revV≡ fzero (sealʳ (suc σ) •ʳ θ₂)
                (trans (rename-replace (ext-injective inj) (fsuc X) (⇑ᵗ R) A)
                  (cong (λ T → replaceTy (fsuc (ρ X)) T (renameᵗ (extᵗ ρ) A))
                    (renameᵗ-shift ρ R)))))
           (≈ᵀ-trans′
             (conceal-ren (ext-injective inj) (ext-EnvRen (sealʳ σ) e)
               A (fsuc X) (⇑ᵗ R))
             (conceal≡ (renameᵗ (extᵗ ρ) A) (fsuc (ρ X))
               (renameᵗ-shift ρ R) (sealʳ σ •ʳ θ₂))))

  -- the representation matters only through its value
  reveal≡ : ∀ {Δ} (B : Ty Δ) X {R R′} → R ≡ R′ → ∀ θ
    → ⟦ 〖 X , R ↑ B 〗 ⟧↑ θ ≈ᵀ ⟦ 〖 X , R′ ↑ B 〗 ⟧↑ θ
  reveal≡ B X {R} refl θ = ≈ᵀ-refl (conv↑-mono 〖 X , R ↑ B 〗 θ)

  conceal≡ : ∀ {Δ} (B : Ty Δ) X {R R′} → R ≡ R′ → ∀ θ
    → ⟦ makeConceal X R B ⟧↓ θ ≈ᵀ ⟦ makeConceal X R′ B ⟧↓ θ
  conceal≡ B X {R} refl θ = ≈ᵀ-refl (conv↓-mono (makeConceal X R B) θ)

  -- transitivity of equivalence
  ≈ᵀ-trans′ : ∀ {T₁ T₂ T₃} → T₁ ≈ᵀ T₂ → T₂ ≈ᵀ T₃ → T₁ ≈ᵀ T₃
  ≈ᵀ-trans′ (r₁ , l₁) (r₂ , l₂) =
    (λ m E⊆ → ⊆ᴿ-trans (r₁ m E⊆) (r₂ m ⊆-refl)) ,
    (λ m E⊆ → ⊆ᴿ-trans (l₂ m E⊆) (l₁ m ⊆-refl))

------------------------------------------------------------------------
-- Casts
------------------------------------------------------------------------

revealTy≡ : ∀ {Δ} {B B′ : Ty Δ} X R → B ≡ B′ → ∀ θ
  → ⟦ 〖 X , R ↑ B 〗 ⟧↑ θ ≈ᵀ ⟦ 〖 X , R ↑ B′ 〗 ⟧↑ θ
revealTy≡ {B = B} X R refl θ = ≈ᵀ-refl (conv↑-mono 〖 X , R ↑ B 〗 θ)

castL≡ : ∀ {Δ} {μ : Env∼ Δ} {A A′ B : Ty Δ} (e : A ≡ A′)
  (c : μ ⊢ A ∼ B) θ → ⟦ c ⟧ᶜ θ ≈ᵀ ⟦ subst-left-∼ e c ⟧ᶜ θ
castL≡ refl c θ = ≈ᵀ-refl (cast-mono c θ)

castR≡ : ∀ {Δ} {μ : Env∼ Δ} {A B B′ : Ty Δ} (e : B ≡ B′)
  (c : μ ⊢ A ∼ B) θ → ⟦ c ⟧ᶜ θ ≈ᵀ ⟦ subst-right-∼ e c ⟧ᶜ θ
castR≡ refl c θ = ≈ᵀ-refl (cast-mono c θ)

injR-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} → EnvRen ρ θ₁ θ₂
  → ∀ {G : Ty Δ} (g : Ground G)
  → SRef (injR g θ₁) (injR (renameGround ρ g) θ₂)
    × SRef (injR (renameGround ρ g) θ₂) (injR g θ₁)
injR-ren {ρ = ρ} {θ₁} {θ₂} e (＇ X) with θ₁ X | θ₂ (ρ X) | e X
injR-ren {ρ = ρ} {θ₁} {θ₂} e (＇ X) | sealʳ σ | .(sealʳ σ) | refl =
  injᴾ-mono , injᴾ-mono
injR-ren {ρ = ρ} {θ₁} {θ₂} e (＇ X) | starʳ | .starʳ | refl =
  (λ D⊆ → D⊆) , (λ D⊆ → D⊆)
injR-ren e (‵ ι) = injᴾ-mono , injᴾ-mono
injR-ren e ★⇒★ = injᴾ-mono , injᴾ-mono
injR-ren e ∀★ = injᴾ-mono , injᴾ-mono

projR-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} → EnvRen ρ θ₁ θ₂
  → ∀ {G : Ty Δ} (g : Ground G)
  → projR g θ₁ ≈ᵀ projR (renameGround ρ g) θ₂
projR-ren {ρ = ρ} {θ₁} {θ₂} e (＇ X) with θ₁ X | θ₂ (ρ X) | e X
projR-ren {ρ = ρ} {θ₁} {θ₂} e (＇ X) | sealʳ σ | .(sealʳ σ) | refl =
  (λ m → proj-mono) , (λ m → proj-mono)
projR-ren {ρ = ρ} {θ₁} {θ₂} e (＇ X) | starʳ | .starʳ | refl = ret≈
projR-ren e (‵ ι) = (λ m → proj-mono) , (λ m → proj-mono)
projR-ren e ★⇒★ = (λ m → proj-mono) , (λ m → proj-mono)
projR-ren e ∀★ = (λ m → proj-mono) , (λ m → proj-mono)

private
  ext2-fsuc : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (A : Ty (suc Δ))
    → renameᵗ (extᵗ (extᵗ ρ)) (renameᵗ (extᵗ fsuc) A)
      ≡ renameᵗ (extᵗ fsuc) (renameᵗ (extᵗ ρ) A)
  ext2-fsuc ρ A =
    trans (renameᵗ-comp (extᵗ fsuc) (extᵗ (extᵗ ρ)) A)
      (trans (renameᵗ-cong A pw)
        (sym (renameᵗ-comp (extᵗ ρ) (extᵗ fsuc) A)))
    where
    pw : ∀ X → extᵗ (extᵗ ρ) (extᵗ fsuc X) ≡ extᵗ fsuc (extᵗ ρ X)
    pw fzero = refl
    pw (fsuc X) = refl

cast-ren : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {θ₁ θ₂} → Inj ρ → EnvRen ρ θ₁ θ₂
  → ∀ {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B : Ty Δ}
  → (eq : ∀ X → μ′ (ρ X) ≡ μ X) (c : μ ⊢ A ∼ B)
  → ⟦ c ⟧ᶜ θ₁ ≈ᵀ ⟦ rename∼ {μ = μ} {μ′ = μ′} ρ eq c ⟧ᶜ θ₂
cast-ren inj e eq (id ★) = ret≈
cast-ren inj e eq (id (‵ ι)) = ret≈
cast-ren inj e eq (id (＇ X)) = ret≈
cast-ren {ρ = ρ} inj e {μ} {μ′} eq (c ↦ d) =
  fun≈ (cast-ren inj e {flipᵐ μ} {flipᵐ μ′}
          (flip-rename-env {μ = μ} {μ′ = μ′} ρ eq) c)
       (cast-ren inj e eq d)
cast-ren {ρ = ρ} inj e {μ} {μ′} eq (∀ᶜ c) =
  all≈ (λ σ → cast-ren (ext-injective inj) (ext-EnvRen (sealʳ σ) e)
                {extᵐ μ} {extᵐ μ′} (extᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) c)
cast-ren {ρ = ρ} {θ₁} {θ₂} inj e eq (_! ⦃ Gᵍ ⦄ c) =
  seq≈ (cast-ren inj e eq c)
    (point≈ (proj₁ (injR-ren {ρ = ρ} {θ₁} {θ₂} e Gᵍ))
            (proj₂ (injR-ren {ρ = ρ} {θ₁} {θ₂} e Gᵍ)))
cast-ren {ρ = ρ} {θ₁} {θ₂} inj e eq (？_ ⦃ Gᵍ ⦄ c) =
  seq≈ (projR-ren {ρ = ρ} {θ₁} {θ₂} e Gᵍ) (cast-ren inj e eq c)
cast-ren {ρ = ρ} {θ₁} {θ₂} inj e {μ} {μ′} eq
    ((inst_ {A = A} {B = B} c) B≢★) =
  (λ m E⊆ → proj₁ (seq≈ (≈ᵀ-refl inst◆-mono) (body m)) m E⊆) ,
  (λ m E⊆ → proj₂ (seq≈ (≈ᵀ-refl inst◆-mono) (body m)) m E⊆)
  where
  c′ = subst-right-∼ (renameᵗ-shift ρ B)
         (rename∼ {μ = instᵐ μ} {μ′ = instᵐ μ′} (extᵗ ρ)
           (instᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) c)
  body : ∀ m → instBodyT A c θ₁ m ≈ᵀ instBodyT (renameᵗ (extᵗ ρ) A) c′ θ₂ m
  body m =
    seq≈
      (≈ᵀ-trans′
        (reveal-ren (ext-injective (ext-injective inj))
          (ext-EnvRen (sealʳ (suc m)) (ext-EnvRen (sealʳ m) e))
          (renameᵗ (extᵗ fsuc) A) fzero (＇ fsuc fzero))
        (revealTy≡ fzero (＇ fsuc fzero) (ext2-fsuc ρ A)
          (sealʳ (suc m) •ʳ sealʳ m •ʳ θ₂)))
      (seq≈
        (reveal-ren (ext-injective inj) (ext-EnvRen (sealʳ m) e) A fzero ★)
        (≈ᵀ-trans′
          (cast-ren (ext-injective inj) (ext-EnvRen starʳ e)
            {instᵐ μ} {instᵐ μ′} (instᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) c)
          (castR≡ (renameᵗ-shift ρ B)
            (rename∼ {μ = instᵐ μ} {μ′ = instᵐ μ′} (extᵗ ρ)
              (instᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) c)
            (starʳ •ʳ θ₂))))
cast-ren {ρ = ρ} {θ₁} {θ₂} inj e {μ} {μ′} eq
    ((gen_ {A = A} c) A≢★) =
  gen≈ (λ σ →
    ≈ᵀ-trans′
      (cast-ren (ext-injective inj) (ext-EnvRen (sealʳ σ) e)
        {genᵐ μ} {genᵐ μ′} (genᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) c)
      (castL≡ (renameᵗ-shift ρ A)
        (rename∼ {μ = genᵐ μ} {μ′ = genᵐ μ′} (extᵗ ρ)
          (genᵐ-rename {μ = μ} {μ′ = μ′} ρ eq) c)
        (sealʳ σ •ʳ θ₂)))
cast-ren inj e eq bot-elim =
  all≈ (λ σ → ≈ᵀ-refl (point-monoT injᴾ-mono))
cast-ren inj e eq bot-intro = errT-mono , errT-mono

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix 4 _≐ᴿ_

_≐ᴿ_ : ℛ → ℛ → Set
R ≐ᴿ S = R ⊆ᴿ S × S ⊆ᴿ R

keep-EnvRen : ∀ {Δ Δ′} {η : Δ ↪ᵗ Δ′} {θ₁ θ₂} (r : Rep)
  → EnvRen (toRenameᵗ η) θ₁ θ₂
  → EnvRen (toRenameᵗ (keep η)) (r •ʳ θ₁) (r •ʳ θ₂)
keep-EnvRen r e fzero = refl
keep-EnvRen r e (fsuc X) = e X

private
  keep-shift : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) (A : Ty Δ)
    → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
  keep-shift η A =
    trans (renameᵗ-comp fsuc (toRenameᵗ (keep η)) A)
      (sym (renameᵗ-comp (toRenameᵗ η) fsuc A))

≫=-≐ : ∀ {R R′ K K′} → R ≐ᴿ R′
  → (∀ {D D′} m → D ⊆ D′ → K D m ⊆ᴿ K′ D′ m)
  → (∀ {D D′} m → D ⊆ D′ → K′ D m ⊆ᴿ K D′ m)
  → (R ≫= K) ≐ᴿ (R′ ≫= K′)
≫=-≐ (r , l) KK K′K = ≫=-mono r KK , ≫=-mono l K′K

term-ren : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) {θ₁ θ₂}
  → EnvRen (toRenameᵗ η) θ₁ θ₂
  → ∀ (M : Term Δ) ρ n → ⟦ M ⟧ θ₁ ρ n ≐ᴿ ⟦ renameᵗᵐ η M ⟧ θ₂ ρ n
term-ren η e (` x) ρ n = ⊆ᴿ-refl , ⊆ᴿ-refl
term-ren η e (ƛ M) ρ n =
  retᴿ-mono (Λᶠ-mono (λ D m → proj₁ (term-ren η e M (D • ρ) m))) ,
  retᴿ-mono (Λᶠ-mono (λ D m → proj₂ (term-ren η e M (D • ρ) m)))
term-ren η e (L · M) ρ n =
  ≫=-mono (proj₁ (term-ren η e L ρ n)) (λ n₁ F⊆ →
    ≫=-mono (proj₁ (term-ren η e M ρ n₁)) (λ n₂ E⊆ → ●-mono F⊆ E⊆)) ,
  ≫=-mono (proj₂ (term-ren η e L ρ n)) (λ n₁ F⊆ →
    ≫=-mono (proj₂ (term-ren η e M ρ n₁)) (λ n₂ E⊆ → ●-mono F⊆ E⊆))
term-ren η e (Λ M) ρ n =
  retᴿ-mono (Λᴾ-mono (λ σ →
    proj₁ (term-ren (keep η) (keep-EnvRen (sealʳ σ) e) M ρ (suc σ)))) ,
  retᴿ-mono (Λᴾ-mono (λ σ →
    proj₂ (term-ren (keep η) (keep-EnvRen (sealʳ σ) e) M ρ (suc σ))))
term-ren η {θ₁} {θ₂} e (M ⦂∀ B [ A ]) ρ n =
  ≫=-mono (proj₁ (term-ren η e M ρ n)) (λ n₁ F⊆ →
    ≫=-mono (◆-mono F⊆) (proj₁ (conv n₁))) ,
  ≫=-mono (proj₂ (term-ren η e M ρ n)) (λ n₁ F⊆ →
    ≫=-mono (◆-mono F⊆) (proj₂ (conv n₁)))
  where
  conv : ∀ n₁ → ⟦ 〖 fzero , ⇑ᵗ A ↑ B 〗 ⟧↑ (sealʳ n₁ •ʳ θ₁)
    ≈ᵀ ⟦ 〖 fzero , ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
          ↑ renameᵗ (toRenameᵗ (keep η)) B 〗 ⟧↑ (sealʳ n₁ •ʳ θ₂)
  conv n₁ =
    ≈ᵀ-trans′
      (reveal-ren (toRenameᵗ-injective (keep η))
        (keep-EnvRen (sealʳ n₁) e) B fzero (⇑ᵗ A))
      (reveal≡ (renameᵗ (toRenameᵗ (keep η)) B) fzero (keep-shift η A)
        (sealʳ n₁ •ʳ θ₂))
term-ren η e ($ κ) ρ n = ⊆ᴿ-refl , ⊆ᴿ-refl
term-ren η e (L ⊕[ op ] M) ρ n =
  ≫=-mono (proj₁ (term-ren η e L ρ n)) (λ n₁ D⊆ →
    ≫=-mono (proj₁ (term-ren η e M ρ n₁))
      (λ n₂ E⊆ → retᴿ-mono (δᴾ-mono D⊆ E⊆))) ,
  ≫=-mono (proj₂ (term-ren η e L ρ n)) (λ n₁ D⊆ →
    ≫=-mono (proj₂ (term-ren η e M ρ n₁))
      (λ n₂ E⊆ → retᴿ-mono (δᴾ-mono D⊆ E⊆)))
term-ren η {θ₁} {θ₂} e (_⟨_⟩ M {μ = μ} c) ρ n =
  ≫=-≐ (term-ren η e M ρ n) (proj₁ r) (proj₂ r)
  where
  r = cast-ren (toRenameᵗ-injective η) e
        {μ} {renameEnv∼ η μ} (renameEnv∼-preserves η μ) c
term-ren η e (M ↑ c) ρ n =
  ≫=-≐ (term-ren η e M ρ n)
    (proj₁ (conv↑-ren (toRenameᵗ-injective η) e c))
    (proj₂ (conv↑-ren (toRenameᵗ-injective η) e c))
term-ren η e (M ↓ c) ρ n =
  ≫=-≐ (term-ren η e M ρ n)
    (proj₁ (conv↓-ren (toRenameᵗ-injective η) e c))
    (proj₂ (conv↓-ren (toRenameᵗ-injective η) e c))
term-ren η e blame ρ n = ⊆ᴿ-refl , ⊆ᴿ-refl

-- the case reduction uses: shifting by a new variable
shift-term : ∀ {Δ} (M : Term Δ) (θ : REnv Δ) (r : Rep) ρ n
  → ⟦ M ⟧ θ ρ n ≐ᴿ ⟦ renameᵗᵐ wk↪ᵗ M ⟧ (r •ʳ θ) ρ n
shift-term M θ r ρ n = term-ren wk↪ᵗ wk-EnvRen M ρ n
  where
  wk-EnvRen : EnvRen (toRenameᵗ (wk↪ᵗ {_})) θ (r •ʳ θ)
  wk-EnvRen X = cong (r •ʳ θ) (toRename-wk X)
    where
    toRename-wk : ∀ {Δ} (X : TyVar Δ) → toRenameᵗ wk↪ᵗ X ≡ fsuc X
    toRename-wk X = wk-suc X
      where
      wk-suc : ∀ {Δ} (X : TyVar Δ) → toRenameᵗ (wk↪ᵗ {Δ}) X ≡ fsuc X
      wk-suc X = cong fsuc (id-pointwise X)
        where
        id-pointwise : ∀ {Δ} (X : TyVar Δ) → toRenameᵗ (id↪ᵗ {Δ}) X ≡ X
        id-pointwise fzero = refl
        id-pointwise (fsuc X) = cong fsuc (id-pointwise X)
