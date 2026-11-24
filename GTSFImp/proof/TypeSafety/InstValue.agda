module proof.TypeSafety.InstValue where

-- File Charter:
--   * Proves that instantiating a well-typed value of type `∀ A`, with A
--     not a variable and mentioning the bound variable, at a type
--     variable reaches a value in finitely many counted steps (no blame).
--   * Proves the same for an `inst` cast applied to such a value.
--   * The induction is on the cast mass of the value (casts under
--     wrappers and Λ, conversions not counted) and, for conversion
--     wrappers, on their nesting depth.  Instantiation at a variable
--     never increases cast mass.
--   * A cast that is applied during the run always has a function,
--     universal, `inst`, or `gen` cast at its top (`Top`); this is kept
--     by renaming and by the substitutions `c [ ＇ X ]ᶜ` and
--     `c [ ★/0 ]ᶜ`, which is what rules out blame.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤; +-monoʳ-≤; m≤m+n;
   n≤1+n; +-suc)
import Data.Fin as Fin
open import Data.Fin.Properties using (suc-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import Primitives using (κℕ; κ𝔹)
open import Consistency
open import Conversion
open import CastTerms
open import Reduction
open import LR.Steps using (_—→^_[_]_; none; more; steps→↠)
open import proof.Consistency using
  (castSize; castSize-renameᵐᶜ; castSize-renameEnvᶜ;
   castSize-open-var-≤; castSize-close-inst-≤; rename-preimage;
   found; zero-not-shift; gen-safe)
open import proof.ImprecisionConsistency using
  (consistency-target-occurs-source)
open import proof.TypeInTermSubst using
  (renameᵗᵐ-preserves-Value; rename-occurs; rename-star-injective;
   typing-shiftᵗ-bind)
open import proof.TypeSafety.Progress using (no-bot-value)
open import proof.TypeSafety.Preservation using
  (preservation; multi-preservation)

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

pred-≤ : ∀ {a n} → suc a ≤ suc n → a ≤ n
pred-≤ (s≤s le) = le

plus-suc-pred : ∀ a b {n} → a + suc b ≤ suc n → a + b ≤ n
plus-suc-pred a b le =
  pred-≤ (≤-trans (≤-reflexive (sym (+-suc a b))) le)

plus-suc-zero : ∀ a b → a + suc b ≤ zero → ⊥
plus-suc-zero a b le
    with ≤-trans (≤-reflexive (sym (+-suc a b))) le
plus-suc-zero a b le | ()

------------------------------------------------------------------------
-- Cast mass and conversion depth
------------------------------------------------------------------------

mass : ∀ {Δ} → Term Δ → ℕ
mass (` x) = zero
mass (ƛ N) = zero
mass (L · M) = zero
mass (Λ W) = mass W
mass (L ⦂∀ B [ A ]) = zero
mass ($ κ) = zero
mass (L ⊕[ op ] M) = zero
mass (W ⟨ c ⟩) = mass W + castSize c
mass (W ↑ c) = mass W
mass (W ↓ c) = mass W
mass blame = zero

mass-rename : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) (M : Term Δ)
  → mass (renameᵗᵐ ρ M) ≡ mass M
mass-rename ρ (` x) = refl
mass-rename ρ (ƛ N) = refl
mass-rename ρ (L · M) = refl
mass-rename ρ (Λ W) = mass-rename (keep ρ) W
mass-rename ρ (L ⦂∀ B [ A ]) = refl
mass-rename ρ ($ κ) = refl
mass-rename ρ (L ⊕[ op ] M) = refl
mass-rename ρ (W ⟨ c ⟩) =
  cong₂ _+_ (mass-rename ρ W) (castSize-renameᵐᶜ ρ c)
mass-rename ρ (W ↑ c) = mass-rename ρ W
mass-rename ρ (W ↓ c) = mass-rename ρ W
mass-rename ρ blame = refl

depth : ∀ {Δ} → Term Δ → ℕ
depth (` x) = zero
depth (ƛ N) = zero
depth (L · M) = zero
depth (Λ W) = zero
depth (L ⦂∀ B [ A ]) = zero
depth ($ κ) = zero
depth (L ⊕[ op ] M) = zero
depth (W ⟨ c ⟩) = zero
depth (W ↑ c) = suc (depth W)
depth (W ↓ c) = suc (depth W)
depth blame = zero

depth-rename : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) (M : Term Δ)
  → depth (renameᵗᵐ ρ M) ≡ depth M
depth-rename ρ (` x) = refl
depth-rename ρ (ƛ N) = refl
depth-rename ρ (L · M) = refl
depth-rename ρ (Λ W) = refl
depth-rename ρ (L ⦂∀ B [ A ]) = refl
depth-rename ρ ($ κ) = refl
depth-rename ρ (L ⊕[ op ] M) = refl
depth-rename ρ (W ⟨ c ⟩) = refl
depth-rename ρ (W ↑ c) = cong suc (depth-rename ρ W)
depth-rename ρ (W ↓ c) = cong suc (depth-rename ρ W)
depth-rename ρ blame = refl

castSize-apply : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (χs : StoreChanges Δ Δ′) (c : μ ⊢ A ∼ B)
  → castSize (applyConsistencies χs c) ≡ castSize c
castSize-apply [] c = refl
castSize-apply (keep ∷ χs) c = castSize-apply χs c
castSize-apply (bind A ∷ χs) c =
  trans (castSize-apply χs _)
    (castSize-renameEnvᶜ Fin.suc (λ X → refl) c)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

subst-≢★ : ∀ {Δ Δ′} {σ : Δ ⇒ˢ Δ′} {A : Ty Δ} {Y : TyVar Δ}
  → NonVar A → Y ∈ᵗ A → substᵗ σ A ≢ ★
subst-≢★ nonvar-base ()
subst-≢★ nonvar-star ()
subst-≢★ nonvar-fun Y∈A = λ ()
subst-≢★ nonvar-all Y∈A = λ ()

nonvar-occ-≢★ : ∀ {Δ} {A : Ty Δ} {Y : TyVar Δ}
  → NonVar A → Y ∈ᵗ A → A ≢ ★
nonvar-occ-≢★ nonvar-base ()
nonvar-occ-≢★ nonvar-star ()
nonvar-occ-≢★ nonvar-fun Y∈A = λ ()
nonvar-occ-≢★ nonvar-all Y∈A = λ ()

var-nonvar : ∀ {Δ} {X : TyVar Δ} → NonVar (＇ X) → ⊥
var-nonvar ()

fun-occ-right : ∀ {Δ} {Y : TyVar Δ} {A B : Ty Δ}
  → Y ∈ᵗ B → Y ∈ᵗ A ⇒ B
fun-occ-right {Y = Y} {A = A} Y∈B with occurs? Y A
fun-occ-right {Y = Y} {A = A} Y∈B | present Y∈A = ∈-fun-left Y∈A
fun-occ-right {Y = Y} {A = A} Y∈B | absent Y∉A = ∈-fun-right Y∉A Y∈B

unshift-occ : ∀ {Δ} {Y : TyVar Δ} {A : Ty Δ}
  → Fin.suc Y ∈ᵗ ⇑ᵗ A → Y ∈ᵗ A
unshift-occ {A = A} p with rename-preimage {ρ = Fin.suc} {A = A} p
unshift-occ {A = A} p | found X refl X∈A = X∈A

-- the body of a universal value's type is not a variable when it
-- mentions the bound variable
body-nonvar : ∀ {Δ} {Σ : TyStore Δ} {W : Term Δ} {C : Ty (suc Δ)}
  → Value W
  → ⟨ Δ , Σ , [] ⟩ ⊢ W ⦂ `∀ C
  → Fin.zero ∈ᵗ C
  → NonVar C
body-nonvar {C = ＇ Fin.zero} vW W⊢ z∈C = ⊥-elim (no-bot-value vW W⊢)
body-nonvar {C = ＇ Fin.suc X} vW W⊢ ()
body-nonvar {C = ‵ ι} vW W⊢ z∈C = nonvar-base
body-nonvar {C = ★} vW W⊢ z∈C = nonvar-star
body-nonvar {C = A ⇒ B} vW W⊢ z∈C = nonvar-fun
body-nonvar {C = `∀ A} vW W⊢ z∈C = nonvar-all

------------------------------------------------------------------------
-- Casts with an inert or `inst` top
------------------------------------------------------------------------

data Top {Δ : TyCtx} {μ : Env∼ Δ} :
    ∀ {A B : Ty Δ} → μ ⊢ A ∼ B → Set where
  top-fun : ∀ {A A′ B B′}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Top (c ↦ d)

  top-all : ∀ {A B : Ty (suc Δ)} {c : extᵐ μ ⊢ A ∼ B}
    → Top (∀ᶜ c)

  top-inst : ∀ {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
      {Anv : NonVar A} {z∈A : Fin.zero ∈ᵗ A}
    → (B≢★ : B ≢ ★)
    → Top (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)

  top-gen : ∀ {A : Ty Δ} {B : Ty (suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      {Bnv : NonVar B} {z∈B : Fin.zero ∈ᵗ B}
    → (A≢★ : A ≢ ★)
    → Top (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)

top-of-safe : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
  → GenSafe c → Top c
top-of-safe safe-⇒ = top-fun
top-of-safe safe-∀ = top-all
top-of-safe (safe-inst B≢★) = top-inst B≢★
top-of-safe (safe-gen A≢★ safe) = top-gen A≢★

-- a cast whose source is not a variable, mentions a variable, and whose
-- target is not ★ has an inert or `inst` top
top-shape : ∀ {Δ} {μ : Env∼ Δ} {S T : Ty Δ} {Y : TyVar Δ}
  → (c : μ ⊢ S ∼ T) → NonVar S → Y ∈ᵗ S → T ≢ ★ → Top c
top-shape (id (＇ X)) Snv Y∈S T≢★ = ⊥-elim (var-nonvar Snv)
top-shape (id (‵ ι)) Snv () T≢★
top-shape (id ★) Snv () T≢★
top-shape (c ↦ d) Snv Y∈S T≢★ = top-fun
top-shape (∀ᶜ c) Snv Y∈S T≢★ = top-all
top-shape (c !) Snv Y∈S T≢★ = ⊥-elim (T≢★ refl)
top-shape (？ c) Snv () T≢★
top-shape (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) Snv Y∈S T≢★ = top-inst B≢★
top-shape (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) Snv Y∈S T≢★ = top-gen A≢★
top-shape bot-elim Snv (∈-all ()) T≢★
top-shape bot-intro Snv (∈-all ()) T≢★

top-rename : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (ρ : Δ ⇒ʳ Δ′) (eq : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X)
  → Top c
  → Top (rename∼ {μ = μ} {μ′ = μ′} ρ eq c)
top-rename ρ eq top-fun = top-fun
top-rename ρ eq top-all = top-all
top-rename ρ eq (top-inst B≢★) = top-inst _
top-rename ρ eq (top-gen A≢★) = top-gen _

top-apply : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
  → (χs : StoreChanges Δ Δ′)
  → Top c
  → Top (applyConsistencies χs c)
top-apply [] t = t
top-apply (keep ∷ χs) t = top-apply χs t
top-apply (bind A ∷ χs) t =
  top-apply χs (top-rename Fin.suc (λ X → refl) t)

top-subst-right : ∀ {Δ} {μ : Env∼ Δ} {A B B′ : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (eq : B ≡ B′) → Top c → Top (subst-right-∼ eq c)
top-subst-right refl t = t

top-subst : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′} {σ : Δ ⇒ˢ Δ′}
    {A B : Ty Δ} {c : μ ⊢ A ∼ B}
  → (s : SubstEnv∼ μ ν σ)
  → Top c
  → substᵗ σ A ≢ ★
  → substᵗ σ B ≢ ★
  → Top (subst∼ s c)
top-subst s top-fun A≢ B≢ = top-fun
top-subst s top-all A≢ B≢ = top-all
top-subst {σ = σ} s (top-inst {B = B} B≢★) A≢ B≢
    with substᵗ σ B ≟Ty ★
top-subst {σ = σ} s (top-inst {B = B} B≢★) A≢ B≢
    | yes Bσ≡★ = ⊥-elim (B≢ Bσ≡★)
top-subst {σ = σ} s (top-inst {B = B} B≢★) A≢ B≢
    | no Bσ≢★ = top-inst Bσ≢★
top-subst {σ = σ} s (top-gen {A = A} A≢★) A≢ B≢
    with substᵗ σ A ≟Ty ★
top-subst {σ = σ} s (top-gen {A = A} A≢★) A≢ B≢
    | yes Aσ≡★ = ⊥-elim (A≢ Aσ≡★)
top-subst {σ = σ} s (top-gen {A = A} A≢★) A≢ B≢
    | no Aσ≢★ = top-gen Aσ≢★

top-close-inst : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)} {B : Ty Δ}
  → (e : instᵐ μ ⊢ A ∼ ⇑ᵗ B)
  → NonVar A → Fin.zero ∈ᵗ A → B ≢ ★
  → Top (↑ᶜ (close-instᶜ e))
top-close-inst {B = B} e Anv z∈A B≢★ =
  top-rename (toRenameᵗ wk↪ᵗ) (renameEnv∼-preserves wk↪ᵗ _)
    (top-subst-right (shift-openᵗ B ★)
      (top-subst _ (top-shape e Anv z∈A ⇑B≢★)
        (subst-≢★ Anv z∈A) Bσ≢★))
  where
  ⇑B≢★ : ⇑ᵗ B ≢ ★
  ⇑B≢★ eq = B≢★ (rename-star-injective Fin.suc eq)

  Bσ≢★ : (⇑ᵗ B) [ ★ ]ᵗ ≢ ★
  Bσ≢★ eq = B≢★ (trans (sym (shift-openᵗ B ★)) eq)

------------------------------------------------------------------------
-- Occurrences across store-valid conversions
------------------------------------------------------------------------

-- Y is neither a stored variable nor mentioned by a stored type
Avoids : ∀ {Δ} → TyStore Δ → TyVar Δ → Set
Avoids Σ Y = ∀ {X R} → Σ ∋ X ⦂ R → (X ≡ Y → ⊥) × (Y ∈ᵗ R → ⊥)

avoids-zero : ∀ {Δ} {Σ : TyStore Δ} → Avoids (store-lift Σ) Fin.zero
avoids-zero (S-lift∋ X∈ refl) = (λ ()) , zero-not-shift

avoids-lift : ∀ {Δ} {Σ : TyStore Δ} {Y : TyVar Δ}
  → Avoids Σ Y → Avoids (store-lift Σ) (Fin.suc Y)
avoids-lift av (S-lift∋ X∈ refl) =
  (λ eq → proj₁ (av X∈) (suc-injective eq)) ,
  (λ p → proj₂ (av X∈) (unshift-occ p))

mutual
  occ↑-st : ∀ {Δ} {Σ : TyStore Δ} {Y : TyVar Δ} {A B : Ty Δ}
      {c : Conv↑ Δ A B}
    → Avoids Σ Y → Σ ⊢↑ c → Y ∈ᵗ A → Y ∈ᵗ B
  occ↑-st av (⊢↑-unseal X∈) var-∈ = ⊥-elim (proj₁ (av X∈) refl)
  occ↑-st av (⊢↑-⇒ c⊢ d⊢) (∈-fun-left p) =
    ∈-fun-left (occ↓-ts av c⊢ p)
  occ↑-st av (⊢↑-⇒ c⊢ d⊢) (∈-fun-right Y∉A p) =
    fun-occ-right (occ↑-st av d⊢ p)
  occ↑-st av (⊢↑-∀ c⊢) (∈-all p) = ∈-all (occ↑-st (avoids-lift av) c⊢ p)
  occ↑-st av ⊢↑-id p = p

  occ↑-ts : ∀ {Δ} {Σ : TyStore Δ} {Y : TyVar Δ} {A B : Ty Δ}
      {c : Conv↑ Δ A B}
    → Avoids Σ Y → Σ ⊢↑ c → Y ∈ᵗ B → Y ∈ᵗ A
  occ↑-ts av (⊢↑-unseal X∈) p = ⊥-elim (proj₂ (av X∈) p)
  occ↑-ts av (⊢↑-⇒ c⊢ d⊢) (∈-fun-left p) =
    ∈-fun-left (occ↓-st av c⊢ p)
  occ↑-ts av (⊢↑-⇒ c⊢ d⊢) (∈-fun-right Y∉A p) =
    fun-occ-right (occ↑-ts av d⊢ p)
  occ↑-ts av (⊢↑-∀ c⊢) (∈-all p) = ∈-all (occ↑-ts (avoids-lift av) c⊢ p)
  occ↑-ts av ⊢↑-id p = p

  occ↓-st : ∀ {Δ} {Σ : TyStore Δ} {Y : TyVar Δ} {A B : Ty Δ}
      {c : Conv↓ Δ A B}
    → Avoids Σ Y → Σ ⊢↓ c → Y ∈ᵗ A → Y ∈ᵗ B
  occ↓-st av (⊢↓-seal X∈) p = ⊥-elim (proj₂ (av X∈) p)
  occ↓-st av (⊢↓-⇒ c⊢ d⊢) (∈-fun-left p) =
    ∈-fun-left (occ↑-ts av c⊢ p)
  occ↓-st av (⊢↓-⇒ c⊢ d⊢) (∈-fun-right Y∉A p) =
    fun-occ-right (occ↓-st av d⊢ p)
  occ↓-st av (⊢↓-∀ c⊢) (∈-all p) = ∈-all (occ↓-st (avoids-lift av) c⊢ p)
  occ↓-st av ⊢↓-id p = p

  occ↓-ts : ∀ {Δ} {Σ : TyStore Δ} {Y : TyVar Δ} {A B : Ty Δ}
      {c : Conv↓ Δ A B}
    → Avoids Σ Y → Σ ⊢↓ c → Y ∈ᵗ B → Y ∈ᵗ A
  occ↓-ts av (⊢↓-seal X∈) var-∈ = ⊥-elim (proj₁ (av X∈) refl)
  occ↓-ts av (⊢↓-⇒ c⊢ d⊢) (∈-fun-left p) =
    ∈-fun-left (occ↑-st av c⊢ p)
  occ↓-ts av (⊢↓-⇒ c⊢ d⊢) (∈-fun-right Y∉A p) =
    fun-occ-right (occ↓-ts av d⊢ p)
  occ↓-ts av (⊢↓-∀ c⊢) (∈-all p) = ∈-all (occ↓-ts (avoids-lift av) c⊢ p)
  occ↓-ts av ⊢↓-id p = p

------------------------------------------------------------------------
-- Shapes of conversions
------------------------------------------------------------------------

-- the generated conversion at a type that is not a variable and
-- mentions a variable is a value former
conv-rv : ∀ {Δ} {X Y : TyVar Δ} {R B : Ty Δ}
  → NonVar B → Y ∈ᵗ B → RevealValue 〖 X , R ↑ B 〗
conv-rv nonvar-base ()
conv-rv nonvar-star ()
conv-rv nonvar-fun Y∈B = fun
conv-rv nonvar-all Y∈B = all

data RShape : ∀ {Δ} {A B : Ty Δ} → Conv↑ Δ A B → Set where
  r-val : ∀ {Δ} {A B : Ty Δ} {c : Conv↑ Δ A B}
    → RevealValue c → RShape c
  r-id : ∀ {Δ} {A : Ty Δ} → RShape (id↑ A)

data CShape : ∀ {Δ} {A B : Ty Δ} → Conv↓ Δ A B → Set where
  c-val : ∀ {Δ} {A B : Ty Δ} {c : Conv↓ Δ A B}
    → ConcealValue c → CShape c
  c-id : ∀ {Δ} {A : Ty Δ} → CShape (id↓ A)

rv-ren : ∀ {Δ Δ′} {A B : Ty Δ} (ρ : Δ ⇒ʳ Δ′) {c : Conv↑ Δ A B}
  → RevealValue c → RevealValue (rename↑ ρ c)
rv-ren ρ fun = fun
rv-ren ρ all = all

cv-ren : ∀ {Δ Δ′} {A B : Ty Δ} (ρ : Δ ⇒ʳ Δ′) {c : Conv↓ Δ A B}
  → ConcealValue c → ConcealValue (rename↓ ρ c)
cv-ren ρ seal = seal
cv-ren ρ fun = fun
cv-ren ρ all = all

rs-ren : ∀ {Δ Δ′} {A B : Ty Δ} (ρ : Δ ⇒ʳ Δ′) {c : Conv↑ Δ A B}
  → RShape c → RShape (rename↑ ρ c)
rs-ren ρ (r-val rv) = r-val (rv-ren ρ rv)
rs-ren ρ r-id = r-id

cs-ren : ∀ {Δ Δ′} {A B : Ty Δ} (ρ : Δ ⇒ʳ Δ′) {c : Conv↓ Δ A B}
  → CShape c → CShape (rename↓ ρ c)
cs-ren ρ (c-val cv) = c-val (cv-ren ρ cv)
cs-ren ρ c-id = c-id

rshape-of : ∀ {Δ} {Σ : TyStore Δ} {A B : Ty Δ} {c : Conv↑ Δ A B}
  → NonVar A → Σ ⊢↑ c → RShape c
rshape-of Anv (⊢↑-unseal X∈) = ⊥-elim (var-nonvar Anv)
rshape-of Anv (⊢↑-⇒ c⊢ d⊢) = r-val fun
rshape-of Anv (⊢↑-∀ c⊢) = r-val all
rshape-of Anv ⊢↑-id = r-id

cshape-of : ∀ {Δ} {Σ : TyStore Δ} {A B : Ty Δ} {c : Conv↓ Δ A B}
  → Σ ⊢↓ c → CShape c
cshape-of (⊢↓-seal X∈) = c-val seal
cshape-of (⊢↓-⇒ c⊢ d⊢) = c-val fun
cshape-of (⊢↓-∀ c⊢) = c-val all
cshape-of ⊢↓-id = c-id

------------------------------------------------------------------------
-- Counted runs: composition and frames
------------------------------------------------------------------------

infixr 5 _++ᶜ_

_++ᶜ_ : ∀ {Δ Δ′ Δ″}
  → StoreChanges Δ Δ′ → StoreChanges Δ′ Δ″ → StoreChanges Δ Δ″
[] ++ᶜ χs′ = χs′
(χ ∷ χs) ++ᶜ χs′ = χ ∷ (χs ++ᶜ χs′)

run-++ : ∀ {Δ Δ′ Δ″ j k} {L : Term Δ} {M : Term Δ′} {N : Term Δ″}
    {χs : StoreChanges Δ Δ′} {χs′ : StoreChanges Δ′ Δ″}
  → L —→^ j [ χs ] M
  → M —→^ k [ χs′ ] N
  → L —→^ j + k [ χs ++ᶜ χs′ ] N
run-++ none r = r
run-++ (more s r₁) r₂ = more s (run-++ r₁ r₂)

run-⟨⟩ : ∀ {Δ Δ′ k} {M : Term Δ} {N : Term Δ′}
    {χs : StoreChanges Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → M —→^ k [ χs ] N
  → M ⟨ c ⟩ —→^ k [ χs ] N ⟨ applyConsistencies χs c ⟩
run-⟨⟩ c none = none
run-⟨⟩ c (more {χ = χ} s r) =
  more (ξ-⟨⟩ s refl) (run-⟨⟩ (applyConsistency χ c) r)

module Frame↑
    (P : ∀ {Δ} {A B : Ty Δ} → Conv↑ Δ A B → Set)
    (P-ren : ∀ {Δ Δ′} {A B : Ty Δ} (ρ : Δ ⇒ʳ Δ′)
      {c : Conv↑ Δ A B} → P c → P (rename↑ ρ c))
  where

  data Run↑ {Δ Δ′ : TyCtx} (k : ℕ) (χs : StoreChanges Δ Δ′)
      (L : Term Δ) (N : Term Δ′) : Set where
    run↑ : ∀ {A B : Ty Δ′} {c : Conv↑ Δ′ A B}
      → P c → L —→^ k [ χs ] N ↑ c → Run↑ k χs L N

  cons↑ : ∀ {Δ Δ′ Δ″ k} {χ : StoreChange Δ Δ′}
      {χs : StoreChanges Δ′ Δ″} {L : Term Δ} {L′ : Term Δ′}
      {N : Term Δ″}
    → L —→[ χ ] L′ → Run↑ k χs L′ N → Run↑ (suc k) (χ ∷ χs) L N
  cons↑ s (run↑ p r) = run↑ p (more s r)

  run-↑ : ∀ {Δ Δ′ k} {χs : StoreChanges Δ Δ′} {M : Term Δ}
      {N : Term Δ′} {A B : Ty Δ} {c : Conv↑ Δ A B}
    → P c → M —→^ k [ χs ] N → Run↑ k χs (M ↑ c) N
  run-↑ p none = run↑ p none
  run-↑ p (more {χ = χ} s r) =
    cons↑ (ξ-reveal s refl) (run-↑ (P-ren (λ X → applyVar χ X) p) r)

module Frame↓
    (P : ∀ {Δ} {A B : Ty Δ} → Conv↓ Δ A B → Set)
    (P-ren : ∀ {Δ Δ′} {A B : Ty Δ} (ρ : Δ ⇒ʳ Δ′)
      {c : Conv↓ Δ A B} → P c → P (rename↓ ρ c))
  where

  data Run↓ {Δ Δ′ : TyCtx} (k : ℕ) (χs : StoreChanges Δ Δ′)
      (L : Term Δ) (N : Term Δ′) : Set where
    run↓ : ∀ {A B : Ty Δ′} {c : Conv↓ Δ′ A B}
      → P c → L —→^ k [ χs ] N ↓ c → Run↓ k χs L N

  cons↓ : ∀ {Δ Δ′ Δ″ k} {χ : StoreChange Δ Δ′}
      {χs : StoreChanges Δ′ Δ″} {L : Term Δ} {L′ : Term Δ′}
      {N : Term Δ″}
    → L —→[ χ ] L′ → Run↓ k χs L′ N → Run↓ (suc k) (χ ∷ χs) L N
  cons↓ s (run↓ p r) = run↓ p (more s r)

  run-↓ : ∀ {Δ Δ′ k} {χs : StoreChanges Δ Δ′} {M : Term Δ}
      {N : Term Δ′} {A B : Ty Δ} {c : Conv↓ Δ A B}
    → P c → M —→^ k [ χs ] N → Run↓ k χs (M ↓ c) N
  run-↓ p none = run↓ p none
  run-↓ p (more {χ = χ} s r) =
    cons↓ (ξ-conceal s refl) (run-↓ (P-ren (λ X → applyVar χ X) p) r)

module RV = Frame↑ RevealValue rv-ren
module RS = Frame↑ RShape rs-ren
module CS = Frame↓ CShape cs-ren

------------------------------------------------------------------------
-- Reaching a value
------------------------------------------------------------------------

data Reaches {Δ : TyCtx} (M : Term Δ) (b : ℕ) : Set where
  reaches : ∀ {k Δ′} {χs : StoreChanges Δ Δ′} {U : Term Δ′}
    → M —→^ k [ χs ] U → Value U → mass U ≤ b → Reaches M b

bindR : ∀ {Δ} {M : Term Δ} {b : ℕ} {P : Set}
  → Reaches M b
  → (∀ {k Δ′} {χs : StoreChanges Δ Δ′} {U : Term Δ′}
       → M —→^ k [ χs ] U → Value U → mass U ≤ b → P)
  → P
bindR (reaches r vU bU) κ = κ r vU bU

pre : ∀ {Δ Δ′ k b} {L : Term Δ} {M : Term Δ′}
    {χs : StoreChanges Δ Δ′}
  → L —→^ k [ χs ] M → Reaches M b → Reaches L b
pre r (reaches r′ vU bU) = reaches (run-++ r r′) vU bU

pre1 : ∀ {Δ Δ′ b} {L : Term Δ} {M : Term Δ′}
    {χ : StoreChange Δ Δ′}
  → L —→[ χ ] M → Reaches M b → Reaches L b
pre1 s (reaches r vU bU) = reaches (more s r) vU bU

weaken : ∀ {Δ} {M : Term Δ} {b b′ : ℕ}
  → b ≤ b′ → Reaches M b → Reaches M b′
weaken le (reaches r vU bU) = reaches r vU (≤-trans bU le)

rv-done : ∀ {Δ Δ′ k b} {χs : StoreChanges Δ Δ′} {L : Term Δ}
    {U : Term Δ′}
  → RV.Run↑ k χs L U → Value U → mass U ≤ b → Reaches L b
rv-done (RV.run↑ rv r) vU bU = reaches r (vU ↑ rv) bU

rv-bind : ∀ {Δ Δ′ k} {χs : StoreChanges Δ Δ′} {L : Term Δ}
    {U : Term Δ′} {P : Set}
  → RV.Run↑ k χs L U
  → (∀ {A B : Ty Δ′} {c : Conv↑ Δ′ A B}
       → RevealValue c → L —→^ k [ χs ] U ↑ c → P)
  → P
rv-bind (RV.run↑ rv r) κ = κ rv r

finish↑ : ∀ {Δ} {U : Term Δ} {A B C D : Ty Δ}
    {c : Conv↑ Δ A B} {d : Conv↑ Δ C D}
  → Value U → RShape c → RevealValue d
  → Reaches ((U ↑ c) ↑ d) (mass U)
finish↑ vU (r-val rv₁) rv = reaches none ((vU ↑ rv₁) ↑ rv) ≤-refl
finish↑ vU r-id rv =
  reaches (more (ξ-reveal (pure-step (id-reveal vU)) refl) none)
    (vU ↑ rv-ren (λ X → X) rv) ≤-refl

finish↓ : ∀ {Δ} {U : Term Δ} {A B C D : Ty Δ}
    {c : Conv↓ Δ A B} {d : Conv↑ Δ C D}
  → Value U → CShape c → RevealValue d
  → Reaches ((U ↓ c) ↑ d) (mass U)
finish↓ vU (c-val cv) rv = reaches none ((vU ↓ cv) ↑ rv) ≤-refl
finish↓ vU c-id rv =
  reaches (more (ξ-reveal (pure-step (id-conceal vU)) refl) none)
    (vU ↑ rv-ren (λ X → X) rv) ≤-refl

two-frames↑ : ∀ {Δ Δ′ k b} {χs : StoreChanges Δ Δ′} {L : Term Δ}
    {U : Term Δ′} {A B C D : Ty Δ}
    {c : Conv↑ Δ A B} {d : Conv↑ Δ C D}
  → RShape c → RevealValue d
  → L —→^ k [ χs ] U → Value U → mass U ≤ b
  → Reaches ((L ↑ c) ↑ d) b
two-frames↑ sh rv r vU bU with RS.run-↑ sh r
two-frames↑ sh rv r vU bU | RS.run↑ sh′ r′ with RV.run-↑ rv r′
two-frames↑ sh rv r vU bU | RS.run↑ sh′ r′ | RV.run↑ rv′ r″ =
  pre r″ (weaken bU (finish↑ vU sh′ rv′))

two-frames↓ : ∀ {Δ Δ′ k b} {χs : StoreChanges Δ Δ′} {L : Term Δ}
    {U : Term Δ′} {A B C D : Ty Δ}
    {c : Conv↓ Δ A B} {d : Conv↑ Δ C D}
  → CShape c → RevealValue d
  → L —→^ k [ χs ] U → Value U → mass U ≤ b
  → Reaches ((L ↓ c) ↑ d) b
two-frames↓ sh rv r vU bU with CS.run-↓ sh r
two-frames↓ sh rv r vU bU | CS.run↓ sh′ r′ with RV.run-↑ rv r′
two-frames↓ sh rv r vU bU | CS.run↓ sh′ r′ | RV.run↑ rv′ r″ =
  pre r″ (weaken bU (finish↓ vU sh′ rv′))

cast-inv : ∀ {Γ : Ctx} {M : Term (Δᵉ Γ)} {μ : Env∼ (Δᵉ Γ)}
    {A B C : Ty (Δᵉ Γ)} {c : μ ⊢ A ∼ B}
  → Γ ⊢ M ⟨ c ⟩ ⦂ C → Γ ⊢ M ⦂ A
cast-inv (⊢⟨⟩ M⊢ _) = M⊢

all-body : ∀ {Δ} {Σ : TyStore Δ} {μ : Env∼ Δ} {W : Term Δ}
    {A₁ A : Ty (suc Δ)}
  → Value W
  → ⟨ Δ , Σ , [] ⟩ ⊢ W ⦂ `∀ A₁
  → extᵐ μ ⊢ A₁ ∼ A
  → Fin.zero ∈ᵗ A
  → NonVar A₁ × Fin.zero ∈ᵗ A₁
all-body vW W⊢ c z∈A = body-nonvar vW W⊢ z∈A₁ , z∈A₁
  where
  z∈A₁ = consistency-target-occurs-source refl c z∈A

------------------------------------------------------------------------
-- Instantiation and cast application reach values
------------------------------------------------------------------------

mutual
  inst-reaches : ∀ (n m : ℕ) {Δ} {Σ : TyStore Δ} {V : Term Δ}
      {A : Ty (suc Δ)}
    → Value V
    → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ `∀ A
    → NonVar A
    → Fin.zero ∈ᵗ A
    → mass V ≤ n
    → depth V ≤ m
    → (X : TyVar Δ)
    → Reaches (V ⦂∀ A [ ＇ X ]) (mass V)
  inst-reaches n m (Λ vW) V⊢ Anv z∈A mV dV X =
    reaches (more (β-Λ vW) none) (vW ↑ conv-rv Anv z∈A) ≤-refl
  inst-reaches zero m (_《_》 {V = W} vW (all {c = c})) V⊢ Anv z∈A
      mV dV X =
    ⊥-elim (plus-suc-zero (mass W) (castSize c) mV)
  inst-reaches (suc n) m (_《_》 {V = W} vW (all {c = c}))
      (⊢⟨⟩ W⊢ _) Anv z∈A mV dV X =
    pre1 (pure-step (β-∀ vW refl))
      (bindR (inst-reaches n (depth W) vW W⊢ A₁nv z∈A₁ mW ≤-refl X)
        (λ {χs = χs} {U = U₁} r₁ vU₁ b₁ →
          bindR
            (cast-reaches n (applyConsistencies χs (c [ ＇ X ]ᶜ))
              (top-apply χs topc) vU₁
              (multi-preservation (⊢• W⊢) (steps→↠ r₁))
              (≤-trans (bound χs {U₁} b₁) le′))
            (λ r₂ vU₂ b₂ →
              reaches (run-++ (run-⟨⟩ (c [ ＇ X ]ᶜ) r₁) r₂) vU₂
                (≤-trans b₂
                  (≤-trans (bound χs {U₁} b₁)
                    (+-monoʳ-≤ (mass W) (n≤1+n (castSize c))))))))
    where
    A₁nv = proj₁ (all-body vW W⊢ c z∈A)
    z∈A₁ = proj₂ (all-body vW W⊢ c z∈A)
    le′ = plus-suc-pred (mass W) (castSize c) mV
    mW = ≤-trans (m≤m+n (mass W) (castSize c)) le′
    topc = top-subst _
      (top-shape c A₁nv z∈A₁ (nonvar-occ-≢★ Anv z∈A))
      (subst-≢★ A₁nv z∈A₁) (subst-≢★ Anv z∈A)
    bound : ∀ {Δ′} (χs : StoreChanges _ Δ′) {U₁ : Term Δ′}
      → mass U₁ ≤ mass W
      → mass U₁ + castSize (applyConsistencies χs (c [ ＇ X ]ᶜ))
        ≤ mass W + castSize c
    bound χs b₁ =
      +-mono-≤ b₁
        (≤-trans (≤-reflexive (castSize-apply χs _))
          (castSize-open-var-≤ c X))
  inst-reaches zero m
      (_《_》 {V = W} vW (genᵥ {c = c} ⦃ Bnv ⦄ ⦃ z∈B ⦄ A₀≢★ safe))
      V⊢ Anv z∈A mV dV X =
    ⊥-elim (plus-suc-zero (mass W) (castSize c) mV)
  inst-reaches (suc n) m
      (_《_》 {V = W} vW (genᵥ {c = c} ⦃ Bnv ⦄ ⦃ z∈B ⦄ A₀≢★ safe))
      (⊢⟨⟩ W⊢ _) Anv z∈A mV dV X =
    pre1 (β-gen ⦃ Bnv = Bnv ⦄ ⦃ z∈B = z∈B ⦄ vW A₀≢★ safe)
      (bindR
        (cast-reaches n c (top-of-safe safe)
          (renameᵗᵐ-preserves-Value wk↪ᵗ vW)
          (typing-shiftᵗ-bind {C = ＇ X} W⊢)
          (≤-trans (≤-reflexive m⇑) le′))
        (λ r₂ vU₂ b₂ →
          rv-done (RV.run-↑ (conv-rv Anv z∈A) r₂) vU₂
            (≤-trans b₂
              (≤-trans (≤-reflexive m⇑)
                (+-monoʳ-≤ (mass W) (n≤1+n (castSize c)))))))
    where
    le′ = plus-suc-pred (mass W) (castSize c) mV
    m⇑ = cong (_+ castSize c) (mass-rename wk↪ᵗ W)
  inst-reaches n zero (vW ↑ all) V⊢ Anv z∈A mV () X
  inst-reaches n (suc m) (_↑_ {V = W} vW all)
      (⊢reveal (⊢↑-∀ c⊢) W⊢) Anv z∈A mV dV X =
    pre1 (β-reveal-∀ vW)
      (bindR
        (inst-reaches n m (renameᵗᵐ-preserves-Value wk↪ᵗ vW)
          (typing-shiftᵗ-bind {C = ＇ X} W⊢)
          (renameNonVar (extᵗ Fin.suc) Cnv)
          (rename-occurs (extᵗ Fin.suc) z∈C)
          (≤-trans (≤-reflexive (mass-rename wk↪ᵗ W)) mV)
          (≤-trans (≤-reflexive (depth-rename wk↪ᵗ W)) (pred-≤ dV))
          Fin.zero)
        (λ r₁ vU₁ b₁ →
          two-frames↑ (rshape-of Cnv c⊢) (conv-rv Anv z∈A) r₁ vU₁
            (≤-trans b₁ (≤-reflexive (mass-rename wk↪ᵗ W)))))
    where
    z∈C = occ↑-ts avoids-zero c⊢ z∈A
    Cnv = body-nonvar vW W⊢ z∈C
  inst-reaches n zero (vW ↓ all) V⊢ Anv z∈A mV () X
  inst-reaches n (suc m) (_↓_ {V = W} vW all)
      (⊢conceal (⊢↓-∀ c⊢) W⊢) Anv z∈A mV dV X =
    pre1 (β-conceal-∀ vW)
      (bindR
        (inst-reaches n m (renameᵗᵐ-preserves-Value wk↪ᵗ vW)
          (typing-shiftᵗ-bind {C = ＇ X} W⊢)
          (renameNonVar (extᵗ Fin.suc) Cnv)
          (rename-occurs (extᵗ Fin.suc) z∈C)
          (≤-trans (≤-reflexive (mass-rename wk↪ᵗ W)) mV)
          (≤-trans (≤-reflexive (depth-rename wk↪ᵗ W)) (pred-≤ dV))
          Fin.zero)
        (λ r₁ vU₁ b₁ →
          two-frames↓ (cshape-of c⊢) (conv-rv Anv z∈A) r₁ vU₁
            (≤-trans b₁ (≤-reflexive (mass-rename wk↪ᵗ W)))))
    where
    z∈C = occ↓-ts avoids-zero c⊢ z∈A
    Cnv = body-nonvar vW W⊢ z∈C
  inst-reaches n m (ƛ N) () Anv z∈A mV dV X
  inst-reaches n m ($ (κℕ k)) () Anv z∈A mV dV X
  inst-reaches n m ($ (κ𝔹 b)) () Anv z∈A mV dV X
  inst-reaches n m (vW 《 inj 》) () Anv z∈A mV dV X
  inst-reaches n m (vW 《 fun 》) () Anv z∈A mV dV X
  inst-reaches n m (vW ↑ fun) () Anv z∈A mV dV X
  inst-reaches n m (vW ↓ seal) () Anv z∈A mV dV X
  inst-reaches n m (vW ↓ fun) () Anv z∈A mV dV X

  cast-reaches : ∀ (n : ℕ) {Δ} {Σ : TyStore Δ} {μ : Env∼ Δ}
      {S T : Ty Δ} {U : Term Δ}
    → (d : μ ⊢ S ∼ T)
    → Top d
    → Value U
    → ⟨ Δ , Σ , [] ⟩ ⊢ U ⦂ S
    → mass U + castSize d ≤ n
    → Reaches (U ⟨ d ⟩) (mass U + castSize d)
  cast-reaches n _ top-fun vU U⊢ le = reaches none (vU 《 fun 》) ≤-refl
  cast-reaches n _ top-all vU U⊢ le = reaches none (vU 《 all 》) ≤-refl
  cast-reaches n (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ e A≢★) (top-gen A≢★′) vU U⊢ le =
    reaches none
      (vU 《 genᵥ ⦃ Bnv = Bnv ⦄ ⦃ z∈B = z∈B ⦄ A≢★
        (gen-safe e A≢★ Bnv z∈B) 》)
      ≤-refl
  cast-reaches zero {U = U} (inst_ e B≢★) (top-inst B≢★′) vU U⊢ le =
    ⊥-elim (plus-suc-zero (mass U) (castSize e) le)
  cast-reaches (suc n) {U = U} (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ e B≢★)
      (top-inst B≢★′) vU U⊢ le =
    pre1 step₁
      (bindR
        (inst-reaches n (depth (⇑ᵗᵐ U))
          (renameᵗᵐ-preserves-Value wk↪ᵗ vU)
          (typing-shiftᵗ-bind {C = ★} U⊢)
          (renameNonVar (extᵗ Fin.suc) Anv)
          (rename-occurs (extᵗ Fin.suc) z∈A)
          (≤-trans (≤-reflexive (mass-rename wk↪ᵗ U))
            (≤-trans (m≤m+n (mass U) (castSize e)) le′))
          ≤-refl Fin.zero)
        (λ {χs = χs} {U = U₁} r₁ vU₁ b₁ →
          rv-bind (RV.run-↑ (conv-rv Anv z∈A) r₁)
            (λ rv r₂ →
              bindR
                (cast-reaches n (applyConsistencies χs d₀)
                  (top-apply χs (top-close-inst e Anv z∈A B≢★))
                  (vU₁ ↑ rv)
                  (multi-preservation M⊢ (steps→↠ r₂))
                  (≤-trans (bound χs {U₁} b₁) le′))
                (λ r₃ vU₃ b₃ →
                  reaches (run-++ (run-⟨⟩ d₀ r₂) r₃) vU₃
                    (≤-trans b₃
                      (≤-trans (bound χs {U₁} b₁)
                        (+-monoʳ-≤ (mass U)
                          (n≤1+n (castSize e)))))))))
    where
    step₁ = β-inst ⦃ Anv = Anv ⦄ ⦃ z∈A = z∈A ⦄ vU B≢★
    d₀ = ↑ᶜ (close-instᶜ e)
    M⊢ = cast-inv (preservation (⊢⟨⟩ U⊢ _) step₁)
    le′ = plus-suc-pred (mass U) (castSize e) le
    bound : ∀ {Δ′} (χs : StoreChanges _ Δ′) {U₁ : Term Δ′}
      → mass U₁ ≤ mass (⇑ᵗᵐ U)
      → mass U₁ + castSize (applyConsistencies χs d₀)
        ≤ mass U + castSize e
    bound χs b₁ =
      +-mono-≤ (≤-trans b₁ (≤-reflexive (mass-rename wk↪ᵗ U)))
        (≤-trans (≤-reflexive (castSize-apply χs d₀))
          (castSize-close-inst-≤ e))

------------------------------------------------------------------------
-- Main statements
------------------------------------------------------------------------

forget : ∀ {Δ} {M : Term Δ} {b : ℕ}
  → Reaches M b
  → Σ[ k ∈ ℕ ] Σ[ Δ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δ Δ′ ]
      Σ[ U ∈ Term Δ′ ] ((M —→^ k [ χs ] U) × Value U)
forget (reaches r vU bU) = _ , _ , _ , _ , r , vU

inst-value : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ} {A : Ty (suc Δ)}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ `∀ A
  → NonVar A
  → Fin.zero ∈ᵗ A
  → (X : TyVar Δ)
  → Σ[ k ∈ ℕ ] Σ[ Δ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δ Δ′ ]
      Σ[ U ∈ Term Δ′ ] ((V ⦂∀ A [ ＇ X ] —→^ k [ χs ] U) × Value U)
inst-value {V = V} vV V⊢ Anv z∈A X =
  forget
    (inst-reaches (mass V) (depth V) vV V⊢ Anv z∈A ≤-refl ≤-refl X)

-- any cast with an inert or `inst` top, applied to a well-typed value
top-cast-value : ∀ {Δ} {Σ : TyStore Δ} {μ : Env∼ Δ} {S T : Ty Δ}
    {U : Term Δ}
  → (d : μ ⊢ S ∼ T)
  → Top d
  → Value U
  → ⟨ Δ , Σ , [] ⟩ ⊢ U ⦂ S
  → Σ[ k ∈ ℕ ] Σ[ Δ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δ Δ′ ]
      Σ[ U′ ∈ Term Δ′ ] ((U ⟨ d ⟩ —→^ k [ χs ] U′) × Value U′)
top-cast-value {U = U} d t vU U⊢ =
  forget (cast-reaches (mass U + castSize d) d t vU U⊢ ≤-refl)

inst-cast-value : ∀ {Δ} {Σ : TyStore Δ} {μ : Env∼ Δ} {V : Term Δ}
    {A : Ty (suc Δ)} {B : Ty Δ}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
  → (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B)
  → (B≢★ : B ≢ ★)
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ `∀ A
  → Σ[ k ∈ ℕ ] Σ[ Δ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δ Δ′ ]
      Σ[ U ∈ Term Δ′ ] ((V ⟨ (inst c) B≢★ ⟩ —→^ k [ χs ] U) × Value U)
inst-cast-value c B≢★ vV V⊢ =
  top-cast-value ((inst c) B≢★) (top-inst B≢★) vV V⊢
