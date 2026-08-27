module alt.ThetaPreservation where

-- File Charter:
--   * Develops one-step preservation for closed configurations of the
--     Θ-indexed alternative calculus, one lemma per reduction rule.
--   * The strict rule repairs the counterexample from commit c5ee0351: its
--     mismatched identity delimiters now form an adapter value rather than a
--     redex.  That historical instance remains below as a regression.
--   * The old loose-anchor counterexample is now untypable: crossing entries
--     record their anchors, so typing forces both nodes' type variable and anchor data.
--   * At a nonempty term context, `β-reveal-⇒` independently moves a
--     captured
--     lambda beneath a conceal delimiter whose typing rule requires a closed
--     interior.  That checked instance explains why arbitrary-context
--     preservation would remain false even after repairing `conceal-reveal`.
--   * The theorem is deliberately stated at `[]`; the checked nonempty-context
--     `β-reveal-⇒` refutation remains as a record of that boundary.
--   * The former `β-reveal-∀` counterexample is retained as a resolved
--     regression: source determinacy now computes its body type from the
--     redex, so the old Boolean contractum is no longer a possible step.
--   * The former type variable-dependent `β-conceal-∀` obstruction is retained as
--     a resolved regression.  The contractum resolves its instantiation and
--     computed source in the ended view, then seals the result on exit.
--   * The former `β-conceal-⇒` counterexample's contractum remains a checked
--     positive instance.  Balanced end/begin extension now supplies the
--     general re-entry transport.
--   * The refuted resolving `float-reveal` rule was deleted together with
--     `float-conceal`: regions now stay at their birth delimiter depth.  The
--     former checked counterexample remains below as a historical comment.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (¬_; yes; no)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst

------------------------------------------------------------------------
-- Generator endpoint at a freshly allocated type variable
------------------------------------------------------------------------

replaceEnv : ∀ {Δ} → TyVar Δ → Ty Δ → Δ ⇒ˢ Δ
replaceEnv X R Y = replaceTy X R (＇ Y)

replaceEnv-ext : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ)
    (Y : TyVar (suc Δ))
  → replaceEnv (suc X) (⇑ᵗ R) Y ≡ extsᵗ (replaceEnv X R) Y
replaceEnv-ext X R zero = refl
replaceEnv-ext X R (suc Y) with X ≟ Y
replaceEnv-ext X R (suc .X) | yes refl = refl
replaceEnv-ext X R (suc Y) | no X≢Y = refl

replaceTy-subst : ∀ {Δ} (X : TyVar Δ) (R B : Ty Δ)
  → replaceTy X R B ≡ substᵗ (replaceEnv X R) B
replaceTy-subst X R (＇ Y) with X ≟ Y
replaceTy-subst X R (＇ .X) | yes refl = refl
replaceTy-subst X R (＇ Y) | no X≢Y = refl
replaceTy-subst X R (‵ ι) = refl
replaceTy-subst X R ★ = refl
replaceTy-subst X R (A ⇒ B)
    rewrite replaceTy-subst X R A | replaceTy-subst X R B =
  refl
replaceTy-subst X R (`∀ B) =
  cong `∀
    (trans (replaceTy-subst (suc X) (⇑ᵗ R) B)
      (substᵗ-cong B (replaceEnv-ext X R)))

generator-endpoint : ∀ {Δ} (B : Ty (suc Δ)) (C : Ty Δ)
  → replaceTy zero (⇑ᵗ C) B ≡ ⇑ᵗ (B [ C ]ᵗ)
generator-endpoint B C =
  trans (replaceTy-subst zero (⇑ᵗ C) B)
    (trans (substᵗ-cong B env-eq)
      (sym (renameᵗ-subst suc (singleSubᵗ C) B)))
  where
  env-eq : ∀ X
    → replaceEnv zero (⇑ᵗ C) X
      ≡ renameᵗ suc (singleSubᵗ C X)
  env-eq zero = refl
  env-eq (suc X) = refl

generator-typed : ∀ {Δ} (B : Ty (suc Δ)) (C : Ty Δ)
  → ⊢↑[ zero ⦂ ⇑ᵗ C ] 〖 zero ↑ B 〗
      ⦂ B ↝ wkᵗ zero (B [ C ]ᵗ)
generator-typed B C =
  subst≡
    (λ T → ⊢↑[ zero ⦂ ⇑ᵗ C ] 〖 zero ↑ B 〗 ⦂ B ↝ T)
    (generator-endpoint B C)
    (generator-typed↑ zero (⇑ᵗ C) B)

replace-resolve : ∀ {Δ} (X : TyVar (suc Δ)) (C : Ty Δ)
    (A : Ty (suc Δ))
  → replaceTy X (wkᵗ X C) A
    ≡ wkᵗ X (substᵗ (resolveSubᵗ X C) A)
replace-resolve X C A =
  trans (replaceTy-subst X (wkᵗ X C) A)
    (trans (substᵗ-cong A env-eq)
      (sym (renameᵗ-subst (punchIn X) (resolveSubᵗ X C) A)))
  where
  env-eq : ∀ Y
    → replaceEnv X (wkᵗ X C) Y
      ≡ renameᵗ (punchIn X) (resolveSubᵗ X C Y)
  env-eq Y = sym (resolveSub-reembed X C Y)

------------------------------------------------------------------------
-- Exchange at the two newest regular type variables
------------------------------------------------------------------------

renameTy-id : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (λ X → X) A ≡ A
renameTy-id (＇ X) = refl
renameTy-id (‵ ι) = refl
renameTy-id ★ = refl
renameTy-id (A ⇒ B) rewrite renameTy-id A | renameTy-id B = refl
renameTy-id (`∀ A) = cong `∀
  (trans (renameᵗ-cong A ext-id) (renameTy-id A))
  where
  ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
  ext-id zero = refl
  ext-id (suc X) = refl

substSecond : ∀ {Δ}
  → Ty (suc Δ) → TyVar (suc (suc Δ)) → Ty (suc Δ)
substSecond B zero = ＇ zero
substSecond B (suc zero) = B
substSecond B (suc (suc X)) = ＇ suc X

swap-open : ∀ {Δ} (A : Ty (suc (suc Δ))) (B : Ty (suc Δ))
  → (swapTopᵗ A) [ B ]ᵗ ≡ substᵗ (substSecond B) A
swap-open A B =
  trans (substᵗ-rename (singleSubᵗ B) swapTop A)
    (substᵗ-cong A after-swap)
  where
  after-swap : ∀ X
    → singleSubᵗ B (swapTop X) ≡ substSecond B X
  after-swap zero = refl
  after-swap (suc zero) = refl
  after-swap (suc (suc X)) = refl

swap-shift-open-zero : ∀ {Δ} (A : Ty (suc Δ))
  → (swapTopᵗ (⇑ᵗ A)) [ ＇ zero ]ᵗ ≡ A
swap-shift-open-zero A =
  trans (swap-open (⇑ᵗ A) (＇ zero))
    (trans (substᵗ-rename (substSecond (＇ zero)) suc A)
      (trans (substᵗ-cong A second-after-shift) (substᵗ-id A)))
  where
  second-after-shift : ∀ X
    → substSecond (＇ zero) (suc X) ≡ ＇ X
  second-after-shift zero = refl
  second-after-shift (suc X) = refl

wk-under-∀ : ∀ {Δ} (X : TyVar (suc Δ)) (A : Ty (suc Δ))
  → renameᵗ (extᵗ (punchIn X)) A ≡ wkᵗ (suc X) A
wk-under-∀ X A = renameᵗ-cong A under-∀
  where
  under-∀ : ∀ Y → extᵗ (punchIn X) Y ≡ punchIn (suc X) Y
  under-∀ zero = refl
  under-∀ (suc Y) = refl

wk-zero-∀-swap : ∀ {Δ} (A : Ty (suc Δ))
  → wkᵗ zero (`∀ A) ≡ `∀ (swapTopᵗ (⇑ᵗ A))
wk-zero-∀-swap A = cong `∀ (sym (swap-shift A))
  where
  swap-shift : ∀ {Δ} (B : Ty (suc Δ))
    → swapTopᵗ (⇑ᵗ B) ≡ renameᵗ (extᵗ suc) B
  swap-shift B =
    trans (renameᵗ-comp suc swapTop B)
      (renameᵗ-cong B swap-after-shift)
    where
    swap-after-shift : ∀ X
      → swapTop (suc X) ≡ extᵗ suc X
    swap-after-shift zero = refl
    swap-after-shift (suc X) = refl

wk-exchange : ∀ {Δ} (X : TyVar (suc Δ)) (A : Ty Δ)
  → wkᵗ zero (wkᵗ X A) ≡ wkᵗ (suc X) (wkᵗ zero A)
wk-exchange X A =
  trans (renameᵗ-comp (punchIn X) (punchIn zero) A)
    (trans (renameᵗ-cong A punch-exchange)
      (sym (renameᵗ-comp (punchIn zero) (punchIn (suc X)) A)))
  where
  punch-exchange : ∀ Y
    → punchIn zero (punchIn X Y) ≡ punchIn (suc X) (punchIn zero Y)
  punch-exchange zero = refl
  punch-exchange (suc Y) = refl

punchIn-injective : ∀ {Δ} (X : TyVar (suc Δ)) {Y Z : TyVar Δ}
  → punchIn X Y ≡ punchIn X Z
  → Y ≡ Z
punchIn-injective zero eq = fin-suc-injective eq
punchIn-injective (suc X) {zero} {zero} eq = refl
punchIn-injective (suc X) {zero} {suc z} ()
punchIn-injective (suc X) {suc y} {zero} ()
punchIn-injective (suc X) {suc y} {suc z} eq =
  cong suc (punchIn-injective X (fin-suc-injective eq))

ty-var-injective : ∀ {Δ} {X Y : TyVar Δ}
  → _≡_ {A = Ty Δ} (＇ X) (＇ Y)
  → X ≡ Y
ty-var-injective {X = X} {.X} refl = refl

ty-fun-left-injective : ∀ {Δ} {A B C D : Ty Δ}
  → A ⇒ B ≡ C ⇒ D
  → A ≡ C
ty-fun-left-injective refl = refl

ty-fun-right-injective : ∀ {Δ} {A B C D : Ty Δ}
  → A ⇒ B ≡ C ⇒ D
  → B ≡ D
ty-fun-right-injective refl = refl

ty-all-injective : ∀ {Δ} {A B : Ty (suc Δ)}
  → `∀ A ≡ `∀ B
  → A ≡ B
ty-all-injective refl = refl

renameTy-injective : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
  → (∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y)
  → ∀ {A B : Ty Δ}
  → renameᵗ ρ A ≡ renameᵗ ρ B
  → A ≡ B
renameTy-injective {ρ = ρ} injective {A = ＇ X} {B = ＇ Y} eq =
  cong ＇_ (injective (ty-var-injective eq))
renameTy-injective injective {A = ＇ X} {B = ‵ ι} ()
renameTy-injective injective {A = ＇ X} {B = ★} ()
renameTy-injective injective {A = ＇ X} {B = B ⇒ C} ()
renameTy-injective injective {A = ＇ X} {B = `∀ B} ()
renameTy-injective injective {A = ‵ ι} {B = ＇ X} ()
renameTy-injective injective {A = ‵ ι} {B = ‵ ι′} refl = refl
renameTy-injective injective {A = ‵ ι} {B = ★} ()
renameTy-injective injective {A = ‵ ι} {B = B ⇒ C} ()
renameTy-injective injective {A = ‵ ι} {B = `∀ B} ()
renameTy-injective injective {A = ★} {B = ＇ X} ()
renameTy-injective injective {A = ★} {B = ‵ ι} ()
renameTy-injective injective {A = ★} {B = ★} eq = refl
renameTy-injective injective {A = ★} {B = B ⇒ C} ()
renameTy-injective injective {A = ★} {B = `∀ B} ()
renameTy-injective injective {A = A ⇒ B} {B = ＇ X} ()
renameTy-injective injective {A = A ⇒ B} {B = ‵ ι} ()
renameTy-injective injective {A = A ⇒ B} {B = ★} ()
renameTy-injective injective {A = A ⇒ B} {B = C ⇒ D} eq =
  cong₂ _⇒_
    (renameTy-injective injective (ty-fun-left-injective eq))
    (renameTy-injective injective (ty-fun-right-injective eq))
renameTy-injective injective {A = A ⇒ B} {B = `∀ C} ()
renameTy-injective injective {A = `∀ A} {B = ＇ X} ()
renameTy-injective injective {A = `∀ A} {B = ‵ ι} ()
renameTy-injective injective {A = `∀ A} {B = ★} ()
renameTy-injective injective {A = `∀ A} {B = B ⇒ C} ()
renameTy-injective {ρ = ρ} injective {A = `∀ A} {B = `∀ B} eq =
  cong `∀
    (renameTy-injective ext-injective (ty-all-injective eq))
  where
  ext-injective : ∀ {X Y}
    → extᵗ ρ X ≡ extᵗ ρ Y
    → X ≡ Y
  ext-injective {zero} {zero} eq = refl
  ext-injective {zero} {suc Y} ()
  ext-injective {suc X} {zero} ()
  ext-injective {suc X} {suc Y} eq =
    cong suc (injective (fin-suc-injective eq))

wkTy-injective : ∀ {Δ} (X : TyVar (suc Δ)) {A B : Ty Δ}
  → wkᵗ X A ≡ wkᵗ X B
  → A ≡ B
wkTy-injective X = renameTy-injective (punchIn-injective X)

id↑-endpoint : ∀ {Δ} {X : TyVar Δ} {R A B : Ty Δ}
  → ⊢↑[ X ⦂ R ] id↑ ⦂ A ↝ B
  → A ≡ B
id↑-endpoint (⊢id↑ A) = refl

id↓-endpoint : ∀ {Δ} {X : TyVar Δ} {R A B : Ty Δ}
  → ⊢↓[ X ⦂ R ] id↓ ⦂ A ↝ B
  → A ≡ B
id↓-endpoint (⊢id↓ A) = refl

constant-type : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {Γ} {κ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ $ κ ⦂ A
  → constTy κ ≡ A
constant-type (⊢$ κ) = refl

const-wk : ∀ {Δ} (X : TyVar (suc Δ)) κ
  → constTy {suc Δ} κ ≡ wkᵗ X (constTy {Δ} κ)
const-wk X (κℕ n) = refl
const-wk X (κ𝔹 b) = refl

unseal-source : ∀ {Δ} {X : TyVar Δ} {R A B : Ty Δ}
  → ⊢↑[ X ⦂ R ] unseal ⦂ A ↝ B
  → A ≡ ＇ X
unseal-source ⊢unseal = refl

unseal-target : ∀ {Δ} {X : TyVar Δ} {R A B : Ty Δ}
  → ⊢↑[ X ⦂ R ] unseal ⦂ A ↝ B
  → B ≡ R
unseal-target ⊢unseal = refl

seal-source : ∀ {Δ} {X : TyVar Δ} {R A B : Ty Δ}
  → ⊢↓[ X ⦂ R ] seal ⦂ A ↝ B
  → A ≡ R
seal-source ⊢seal = refl

seal-target : ∀ {Δ} {X : TyVar Δ} {R A B : Ty Δ}
  → ⊢↓[ X ⦂ R ] seal ⦂ A ↝ B
  → B ≡ ＇ X
seal-target ⊢seal = refl

terminal-anchor : ∀ {Θ Δ} {σ : Vec.Vec (Maybe (TyVar Θ)) Δ}
    {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
  → Vec.lookup (insertᵛ X (just α) σ) Y ≡ just β
  → Y ≡ X
  → β ≡ α
terminal-anchor {σ = σ} {X = X} tyVar-eq refl =
  just-injective
    (trans (sym tyVar-eq) (lookup-insert-here X (just _) σ))

------------------------------------------------------------------------
-- Preservation cases: computational rules
------------------------------------------------------------------------

preserve-δ-⊕ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {op κ₁ κ₂ κ₃} {A}
  → δ op κ₁ κ₂ κ₃
  → Ψ ∣ [] ⊢ ($ κ₁ ⊕[ op ] $ κ₂) ⦂ A
  → Ψ ∣ [] ⊢ $ κ₃ ⦂ A
preserve-δ-⊕ δ-add (⊢⊕ addℕ (⊢$ _) (⊢$ _)) = ⊢$ _
preserve-δ-⊕ δ-and (⊢⊕ and𝔹 (⊢$ _) (⊢$ _)) = ⊢$ _

preserve-β : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {V N : Term Θ Δ} {A B}
  → Ψ ∣ [] ⊢ (ƛ A ˙ N) · V ⦂ B
  → Ψ ∣ [] ⊢ N [ V ] ⦂ B
preserve-β (⊢· (⊢ƛ N⊢) V⊢) = ⊢[] N⊢ V⊢

preserve-β-id : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {A} {a : Atom A}
  → Ψ ∣ [] ⊢ V ⟨ id {μ = μ} a ⟩ ⦂ A
  → Ψ ∣ [] ⊢ V ⦂ A
preserve-β-id (⊢⟨⟩ V⊢ (id a)) = V⊢

preserve-β-⇒ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {V W : Term Θ Δ}
    {μ : Env∼ Δ} {A A′ B B′}
    {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
  → Ψ ∣ [] ⊢ (V ⟨ c ↦ d ⟩) · W ⦂ B′
  → Ψ ∣ [] ⊢ (V · (W ⟨ c ⟩)) ⟨ d ⟩ ⦂ B′
preserve-β-⇒ (⊢· (⊢⟨⟩ V⊢ (c ↦ d)) W⊢) =
  ⊢⟨⟩ (⊢· V⊢ (⊢⟨⟩ W⊢ c)) d

preserve-β-∀ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {A B : Ty (suc Δ)} {C : Ty Δ}
    {c : extᵐ μ ⊢ A ∼ B} {d : μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ}
  → d ≡ c [ C ]ᶜ
  → Ψ ∣ [] ⊢ (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
  → Ψ ∣ [] ⊢ (V ⦂∀ A [ C ]) ⟨ d ⟩ ⦂ B [ C ]ᵗ
preserve-β-∀ refl (⊢⦂∀ (⊢⟨⟩ V⊢ (∀ᶜ c))) =
  ⊢⟨⟩ (⊢⦂∀ V⊢) (c [ _ ]ᶜ)

preserve-ground : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {A G : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    {c : μ ⊢ A ∼ G} ⦃ Ans : NonStar A ⦄ ⦃ Gns : NonStar G ⦄
  → Ψ ∣ [] ⊢ V ⟨ c ! ⟩ ⦂ ★
  → Ψ ∣ [] ⊢ V ⟨ c ⟩ ⟨ (idᵍ Gᵍ) ! ⟩ ⦂ ★
preserve-ground ⦃ Gᵍ = Gᵍ ⦄ (⊢⟨⟩ V⊢ (c !)) =
  ⊢⟨⟩ (⊢⟨⟩ V⊢ c) ((idᵍ Gᵍ) !)

preserve-expand : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {G B : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
    {c : μ ⊢ G ∼ B} ⦃ Bns : NonStar B ⦄ ⦃ Gns : NonStar G ⦄
  → Ψ ∣ [] ⊢ V ⟨ ？ c ⟩ ⦂ B
  → Ψ ∣ [] ⊢ V ⟨ ？ (idᵍ Gᵍ) ⟩ ⟨ c ⟩ ⦂ B
preserve-expand ⦃ Gᵍ = Gᵍ ⦄ (⊢⟨⟩ V⊢ (？ c)) =
  ⊢⟨⟩ (⊢⟨⟩ V⊢ (？ (idᵍ Gᵍ))) c

preserve-tag-untag : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
    {μ ν : Env∼ Δ} {G : Ty Δ} ⦃ Gᵍ : Ground G ⦄
    ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Gns : NonStar G ⦄
  → Ψ ∣ [] ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Gᵍ) ⟩ ⦂ G
  → Ψ ∣ [] ⊢ V ⦂ G
preserve-tag-untag (⊢⟨⟩ (⊢⟨⟩ V⊢ c) d) = V⊢

preserve-tag-untag-bad : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-tag-untag-bad M⊢ = ⊢blame

preserve-blame-bot-intro : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-bot-intro M⊢ = ⊢blame

preserve-β-reveal-⇒ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ (suc Δ)} {W : Term Θ Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal} {d : Reveal}
    {B : Ty Δ}
  → Ψ ∣ [] ⊢ (V ↑[ X ≔ α ] (c ↦↑ d)) · W ⦂ B
  → Ψ ∣ [] ⊢ (V · (W ↓[ X ≔ α ] c)) ↑[ X ≔ α ] d ⦂ B
preserve-β-reveal-⇒ {Ψ = Ψ} {W = W} {X = X} {α = α}
    (⊢· (⊢reveal {C = C} {fresh = fresh} α-eq
      (⊢↑-⇒ c⊢ d⊢) V⊢) W⊢) =
  ⊢reveal α-eq d⊢
    (⊢· V⊢ (⊢conceal tyVar-eq ended-eq c⊢ ended-W⊢))
  where
  tyVar-eq = lookup-insert-here X (just α) _
  ended-eq = rep?-bracket {Ψ = Ψ} {Y = X} {a = α} {q = α}
    {A = C} fresh α-eq
  ended-W⊢ = ⊢bracket {Ψ = Ψ} {Y = X} {a = α} fresh W⊢

preserve-β-conceal-⇒ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {V : Term Θ Δ} {W : Term Θ (suc Δ)}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal} {d : Conceal}
    {B : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ (V ↓[ X ≔ α ] (c ↦↓ d)) · W ⦂ B
  → Ψ ∣ [] ⊢ (V · (W ↑[ X ≔ α ] c)) ↓[ X ≔ α ] d ⦂ B
preserve-β-conceal-⇒
    (⊢· (⊢conceal {A = A ⇒ B} tyVar-eq α-eq
      (⊢↓-⇒ c⊢ d⊢) V⊢) W⊢) =
  ⊢conceal tyVar-eq α-eq d⊢
    (⊢· V⊢ (⊢reveal α-eq c⊢ (⊢reenter tyVar-eq W⊢)))

preserve-id-cancel : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {X : TyVar (suc Δ)} {α : TyVar Θ} {A}
  → Ψ ∣ [] ⊢ (V ↓[ X ≔ α ] id↓) ↑[ X ≔ α ] id↑ ⦂ A
  → Ψ ∣ [] ⊢ V ⦂ A
preserve-id-cancel {Ψ = Ψ} {V = V} {X = X} {α = α}
    (⊢reveal α∈ c↑ (⊢conceal tyVar∈ β∈ c↓ V⊢)) =
  subst≡ (λ B → Ψ ∣ [] ⊢ V ⦂ B) type-eq ambient-V⊢
  where
  ambient-V⊢ = ⊢unbracket V⊢
  type-eq = wkTy-injective X
    (trans (id↓-endpoint c↓) (id↑-endpoint c↑))

preserve-id-reveal : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {X} {α}
    {κ} {A : Ty Δ}
  → Ψ ∣ [] ⊢ ($ κ) ↑[ X ≔ α ] id↑ ⦂ A
  → Ψ ∣ [] ⊢ $ κ ⦂ A
preserve-id-reveal {Ψ = Ψ} {X = X} {κ = κ}
    (⊢reveal α∈ c⊢ M⊢) =
  subst≡ (λ B → Ψ ∣ [] ⊢ $ κ ⦂ B) type-eq (⊢$ κ)
  where
  weakened-eq = trans (sym (const-wk X κ))
    (trans (constant-type M⊢) (id↑-endpoint c⊢))
  type-eq = wkTy-injective X weakened-eq

preserve-id-conceal : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ (suc Δ) σ} {X} {α}
    {κ} {A : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ ($ κ) ↓[ X ≔ α ] id↓ ⦂ A
  → Ψ ∣ [] ⊢ $ κ ⦂ A
preserve-id-conceal {Ψ = Ψ} {X = X} {κ = κ}
    (⊢conceal tyVar∈ α∈ c⊢ M⊢) =
  subst≡ (λ B → Ψ ∣ [] ⊢ $ κ ⦂ B) type-eq (⊢$ κ)
  where
  type-eq = trans (const-wk X κ)
    (trans (cong (wkᵗ X) (constant-type M⊢)) (id↓-endpoint c⊢))

preserve-conceal-reveal-matched : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {X Y : TyVar (suc Δ)} {α β : TyVar Θ} {A}
  → X ≡ Y
  → α ≡ β
  → Ψ ∣ [] ⊢ (V ↓[ X ≔ α ] seal) ↑[ Y ≔ β ] unseal ⦂ A
  → Ψ ∣ [] ⊢ V ⦂ A
preserve-conceal-reveal-matched {Ψ = Ψ} {X = X} {α = α} refl refl
    (⊢reveal {fresh = fresh} β-eq c↑
      (⊢conceal tyVar-eq α-eq c↓ V⊢)) =
  subst≡ (λ B → Ψ ∣ [] ⊢ _ ⦂ B) type-eq ambient-V⊢
  where
  ambient-V⊢ = ⊢unbracket V⊢
  ambient-α-eq = trans
    (sym (rep?-unbracket
      (unbracket-base {fresh = fresh}) α)) α-eq
  source-eq = wkTy-injective X (seal-source c↓)
  target-eq = wkTy-injective X (unseal-target c↑)
  type-eq = trans source-eq
    (trans (just-injective (trans (sym ambient-α-eq) β-eq))
      (sym target-eq))

preserve-conceal-reveal : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {X Y : TyVar (suc Δ)} {α β : TyVar Θ} {A}
  → Ψ ∣ [] ⊢ (V ↓[ X ≔ α ] seal) ↑[ Y ≔ β ] unseal ⦂ A
  → Ψ ∣ [] ⊢ V ⦂ A
preserve-conceal-reveal typing@(⊢reveal β-eq c↑
    (⊢conceal inner-tyVar-eq α-eq c↓ V⊢)) =
  preserve-conceal-reveal-matched node-tyVar-eq anchor-eq typing
  where
  node-tyVar-eq = ty-var-injective
    (trans (sym (seal-target c↓)) (unseal-source c↑))
  anchor-eq = terminal-anchor inner-tyVar-eq node-tyVar-eq

preserve-const-ν : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {C A : Ty Δ} {κ}
  → Ψ ∣ [] ⊢ ν[ C ] ($ κ) ⦂ A
  → Ψ ∣ [] ⊢ $ κ ⦂ A
preserve-const-ν (⊢ν (⊢$ κ)) = ⊢$ κ

preserve-β-inst : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {A : Ty (suc Δ)} {B : Ty Δ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
    {B≠★ : B ≢ ★}
  → Ψ ∣ [] ⊢ V ⟨ (inst c) B≠★ ⟩ ⦂ B
  → Ψ ∣ [] ⊢ (V ⦂∀ A [ ★ ]) ⟨ c [ ★/0 ]ᶜ ⟩ ⦂ B
preserve-β-inst (⊢⟨⟩ V⊢ ((inst c) B≠★)) =
  ⊢⟨⟩ (⊢⦂∀ V⊢) (c [ ★/0 ]ᶜ)

fresh-delimiter-conceal : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M : Term (suc Θ) Δ} {A C : Ty Δ}
  → Ψ ,:= C ∣ [] ⊢ M ⦂ A
  → (Ψ ,:= C) ,begin[ zero ≔ zero
      ]⟨ fresh-zero-after-ν {σ = σ} ⟩ ∣ []
      ⊢ M ↓[ zero ≔ zero ] δ↓ (⇑ᵗ A) ⦂ ⇑ᵗ A
fresh-delimiter-conceal {σ = σ} {Ψ = Ψ} {A = A} {C = C} M⊢ =
  ⊢conceal tyVar-eq ended-eq
    (delimiter-typed↓ zero (⇑ᵗ C) (⇑ᵗ A)) ended-M⊢
  where
  base-eq : rep? (Ψ ,:= C) zero ≡ just C
  base-eq = rep?-here
  tyVar-eq = lookup-insert-here zero (just zero)
    (Vec.map (Data.Maybe.map suc) σ)
  ended-eq = rep?-bracket {Ψ = Ψ ,:= C} {Y = zero} {a = zero}
    {q = zero} {A = C} (fresh-zero-after-ν {σ = σ}) base-eq
  ended-M⊢ = ⊢bracket {Ψ = Ψ ,:= C} {Y = zero} {a = zero}
    (fresh-zero-after-ν {σ = σ}) M⊢

⊢shift-crossing : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M : Term Θ (suc Δ)} {T : Ty (suc Δ)} {A : Ty Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {fresh : α ∉ᵛ σ}
  → Ψ ,begin[ X ≔ α ]⟨ fresh ⟩ ∣ [] ⊢ M ⦂ T
  → (Ψ ,:= A) ,begin[ X ≔ suc α
      ]⟨ fresh-TypingTarget
          (balanced-target (≼-ν {Ψ = Ψ} {B = A} ≼-refl)) fresh ⟩
      ∣ [] ⊢ shiftᶿ M ⦂ T
⊢shift-crossing {Ψ = Ψ} {M = M} {T = T} {A = A}
    {X = X} {α = α} {fresh = fresh} M⊢ =
  subst≡
    (λ Z → (Ψ ,:= A) ,begin[ Z ≔ suc α
      ]⟨ fresh-TypingTarget target fresh ⟩ ∣ [] ⊢ shiftᶿ M ⦂ T)
    (insert-here-pointwise-id X toRename-id-eq) typed
  where
  target = balanced-target (≼-ν {Ψ = Ψ} {B = A} ≼-refl)
  typed = ⊢transport-id (typingTarget-begin target)
    (insert-pointwise-id X toRename-id-eq) M⊢

fresh-∀-entry-crossed : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ (suc Δ)} {C : Ty (suc (suc Δ))} {A : Ty Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {fresh : α ∉ᵛ σ}
  → Ψ ,begin[ X ≔ α ]⟨ fresh ⟩ ∣ [] ⊢ V ⦂ `∀ C
  → ((Ψ ,:= A) ,begin[ zero ≔ zero
      ]⟨ fresh-zero-map-suc {tyVars = σ} ⟩)
      ,begin[ suc X ≔ suc α ]⟨
        fresh-insert-other zero (λ ())
          (fresh-TypingTarget
            (balanced-target (≼-ν {Ψ = Ψ} {B = A} ≼-refl)) fresh)
        ⟩ ∣ [] ⊢
      (shiftᶿ V ↓[ zero ≔ zero ] δ↓ (wkᵗ zero (`∀ C)))
        ⦂∀ swapTopᵗ (⇑ᵗ C) [ ＇ zero ] ⦂ C
fresh-∀-entry-crossed {σ = σ} {Ψ = Ψ} {V = V} {C = C} {A = A}
    {X = X} {α = α} {fresh = fresh} V⊢ =
  subst≡ (λ T → ambient ∣ [] ⊢ applied ⦂ T)
    (swap-shift-open-zero C) (⊢⦂∀ exchanged⊢)
  where
  old-fresh = fresh-TypingTarget
    (balanced-target (≼-ν {Ψ = Ψ} {B = A} ≼-refl)) fresh
  old≢new : suc α ≢ zero
  old≢new ()
  ambient = ((Ψ ,:= A)
      ,begin[ zero ≔ zero ]⟨ fresh-zero-map-suc {tyVars = σ} ⟩)
    ,begin[ suc X ≔ suc α ]⟨
      fresh-insert-other {a = suc α} {b = zero} zero old≢new old-fresh ⟩
  deleted = (Ψ ,:= A) ,begin[ X ≔ suc α ]⟨ old-fresh ⟩
  entered = shiftᶿ V ↓[ zero ≔ zero ] δ↓ (wkᵗ zero (`∀ C))
  applied = entered ⦂∀ swapTopᵗ (⇑ᵗ C) [ ＇ zero ]
  deleted-V⊢ = ⊢shift-crossing V⊢
  target = unbracket-fresh-before-begin
    {a = suc α} {b = zero} {a≢b = old≢new}
  target-V⊢ = ⊢unbracket-target target deleted-V⊢
  deleted-eq : rep? deleted zero ≡ just (wkᵗ X A)
  deleted-eq = rep?-here-begin
  target-eq = trans (sym (rep?-unbracket target zero)) deleted-eq
  tyVar-eq : Vec.lookup (tyVarsOf ambient) zero ≡ just zero
  tyVar-eq = refl
  entered⊢ = ⊢conceal tyVar-eq target-eq
    (delimiter-typed↓ zero (wkᵗ zero (wkᵗ X A))
      (wkᵗ zero (`∀ C))) target-V⊢
  exchanged⊢ = subst≡ (λ T → ambient ∣ [] ⊢ entered ⦂ T)
    (wk-zero-∀-swap C) entered⊢

exchange-reveal-∀ : ∀ {Δ} {X : TyVar (suc Δ)}
    {R : Ty Δ} {B : Ty (suc Δ)} {C : Ty (suc (suc Δ))}
    {c : Reveal}
  → ⊢↑[ suc X ⦂ ⇑ᵗ (wkᵗ X R) ] c
      ⦂ C ↝ renameᵗ (extᵗ (punchIn X)) B
  → ⊢↑[ suc X ⦂ wkᵗ (suc X) (⇑ᵗ R) ] c
      ⦂ C ↝ wkᵗ (suc X) B
exchange-reveal-∀ {X = X} {R = R} {B = B} c⊢ =
  subst≡ (λ Q → ⊢↑[ suc X ⦂ Q ] _ ⦂ _ ↝ wkᵗ (suc X) B)
    (wk-exchange X R)
    (subst≡ (λ T → ⊢↑[ suc X ⦂ ⇑ᵗ (wkᵗ X R) ] _ ⦂ _ ↝ T)
      (wk-under-∀ X B) c⊢)

exchange-conceal-∀ : ∀ {Δ} {X : TyVar (suc Δ)}
    {R : Ty Δ} {B : Ty (suc Δ)} {C : Ty (suc (suc Δ))}
    {c : Conceal}
  → ⊢↓[ suc X ⦂ ⇑ᵗ (wkᵗ X R) ] c
      ⦂ renameᵗ (extᵗ (punchIn X)) B ↝ C
  → ⊢↓[ suc X ⦂ wkᵗ (suc X) (⇑ᵗ R) ] c
      ⦂ wkᵗ (suc X) B ↝ C
exchange-conceal-∀ {X = X} {R = R} {B = B} c⊢ =
  subst≡ (λ Q → ⊢↓[ suc X ⦂ Q ] _ ⦂ wkᵗ (suc X) B ↝ _)
    (wk-exchange X R)
    (subst≡ (λ S → ⊢↓[ suc X ⦂ ⇑ᵗ (wkᵗ X R) ] _ ⦂ S ↝ _)
      (wk-under-∀ X B) c⊢)

fresh-∀-entry : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {A : Ty Δ} {C : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ V ⦂ `∀ C
  → (Ψ ,:= A) ,begin[ zero ≔ zero
      ]⟨ fresh-zero-after-ν {σ = σ} ⟩ ∣ [] ⊢
      (shiftᶿ V ↓[ zero ≔ zero ] δ↓ (wkᵗ zero (`∀ C)))
        ⦂∀ swapTopᵗ (⇑ᵗ C) [ ＇ zero ] ⦂ C
fresh-∀-entry {σ = σ} {Ψ = Ψ} {V = V} {A = A} {C = C} V⊢ =
  subst≡ (λ T → target ∣ [] ⊢ applied ⦂ T)
    (swap-shift-open-zero C) (⊢⦂∀ entered⊢)
  where
  target = (Ψ ,:= A) ,begin[ zero ≔ zero
    ]⟨ fresh-zero-after-ν {σ = σ} ⟩
  entered = shiftᶿ V ↓[ zero ≔ zero ] δ↓ (wkᵗ zero (`∀ C))
  applied = entered ⦂∀ swapTopᵗ (⇑ᵗ C) [ ＇ zero ]
  entered⊢ = subst≡ (λ T → target ∣ [] ⊢ entered ⦂ T)
    (wk-zero-∀-swap C)
    (fresh-delimiter-conceal (⊢shiftᶿ V⊢))

preserve-β-Λ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ (suc Δ)} {B : Ty (suc Δ)} {C : Ty Δ}
  → Ψ ∣ [] ⊢ (Λ V) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
  → Ψ ∣ [] ⊢
      ν[ C ] (shiftᶿ V ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)
      ⦂ B [ C ]ᵗ
preserve-β-Λ {B = B} {C = C} (⊢⦂∀ (⊢Λ V⊢)) =
  ⊢ν (⊢reveal rep?-here (generator-typed B C)
    (⊢allocate-lexical V⊢))

preserve-β-gen : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {μ : Env∼ Δ} {A C : Ty Δ}
    {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄ {A≠★ : A ≢ ★}
  → Ψ ∣ [] ⊢ (V ⟨ (gen c) A≠★ ⟩) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
  → Ψ ∣ [] ⊢ ν[ C ]
      (((shiftᶿ V ↓[ zero ≔ zero ] δ↓ (⇑ᵗ A)) ⟨ c ⟩)
        ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)
      ⦂ B [ C ]ᵗ
preserve-β-gen {Ψ = Ψ} {C = C} {B = bodyTy}
    (⊢⦂∀ (⊢⟨⟩ V⊢ ((gen c) A≠★))) =
  ⊢ν (⊢reveal base-eq (generator-typed bodyTy C)
    (⊢⟨⟩ (fresh-delimiter-conceal (⊢shiftᶿ V⊢)) c))
  where
  base-eq : rep? (Ψ ,:= C) zero ≡ just C
  base-eq = rep?-here

preserve-β-reveal-∀ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ (suc Δ)} {A : Ty Δ} {B : Ty (suc Δ)}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
  → Ψ ∣ [] ⊢ (V ↑[ X ≔ α ] `∀↑ c) ⦂∀ B [ A ]
      ⦂ B [ A ]ᵗ
  → Ψ ∣ [] ⊢
      ν[ A ]
        ((((shiftᶿ V ↓[ zero ≔ zero ]
              δ↓ (wkᵗ zero (`∀
                (src↑ (suc X) c
                  (renameᵗ (extᵗ (punchIn X)) B)))))
              ⦂∀ swapTopᵗ
                (⇑ᵗ (src↑ (suc X) c
                  (renameᵗ (extᵗ (punchIn X)) B))) [ ＇ zero ])
            ↑[ suc X ≔ suc α ] c)
          ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)
      ⦂ B [ A ]ᵗ
preserve-β-reveal-∀ {Ψ = Ψ} {A = A} {B = B}
    {X = X} {α = α}
    (⊢⦂∀ (⊢reveal α∈ (⊢↑-∀ c⊢) V⊢))
    with source-determinacy↑ c⊢
preserve-β-reveal-∀ {Θ = Θ} {Ψ = Ψ} {A = A} {B = B}
    {X = X} {α = α}
    (⊢⦂∀ (⊢reveal {C = C} α∈ (⊢↑-∀ c⊢) V⊢)) | refl =
  ⊢ν (⊢reveal rep?-here (generator-typed B A)
    (⊢reveal (rep?-allocate-lexical
        {Θ = Θ} {Ψ = Ψ} {a = α} {A = C} {C = A} α∈)
      (exchange-reveal-∀ c⊢) (fresh-∀-entry-crossed V⊢)))

fresh-∀-region : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {A : Ty Δ} {C D : Ty (suc Δ)}
  → C ≡ D
  → Ψ ∣ [] ⊢ V ⦂ `∀ C
  → Ψ ∣ [] ⊢
      ν[ A ]
        (((shiftᶿ V ↓[ zero ≔ zero ]
            δ↓ (wkᵗ zero (`∀ D)))
            ⦂∀ swapTopᵗ (⇑ᵗ D) [ ＇ zero ])
          ↑[ zero ≔ zero ] 〖 zero ↑ D 〗)
      ⦂ D [ A ]ᵗ
fresh-∀-region refl V⊢ =
  ⊢ν (⊢reveal rep?-here (generator-typed _ _)
    (fresh-∀-entry V⊢))

conceal-resolved-body : ∀ {Δ} {X : TyVar (suc Δ)} {C₀ : Ty Δ}
    {C : Ty (suc Δ)} {B : Ty (suc (suc Δ))} {c : Conceal}
  → ⊢↓[ suc X ⦂ ⇑ᵗ (wkᵗ X C₀) ] c
      ⦂ renameᵗ (extᵗ (punchIn X)) C ↝ B
  → substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C₀))
      (src↓ (suc X) (⇑ᵗ (wkᵗ X C₀)) c B) ≡ C
conceal-resolved-body {X = X} {C₀ = C₀} {C = C} c⊢ =
  trans (cong (substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C₀)))
      (sym (source-determinacy↓ c⊢)))
    (trans (cong (substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C₀)))
        (wk-under-∀ X C))
      (resolve-wkᵗ (suc X) (⇑ᵗ C₀) C))

conceal-resolved-target : ∀ {Δ} {X : TyVar (suc Δ)} {C₀ : Ty Δ}
    {C : Ty (suc Δ)} {B : Ty (suc (suc Δ))} {c : Conceal}
  → ⊢↓[ suc X ⦂ ⇑ᵗ (wkᵗ X C₀) ] c
      ⦂ renameᵗ (extᵗ (punchIn X)) C ↝ B
  → C ≡ substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C₀)) B
conceal-resolved-target {X = X} {C₀ = C₀} {C = C} c⊢ =
  trans (sym (resolve-wkᵗ (suc X) (⇑ᵗ C₀) C))
    (resolve-conversion↓ (exchange-conceal-∀ c⊢))

conceal-exit-endpoint : ∀ {Δ} {X : TyVar (suc Δ)} {C₀ : Ty Δ}
    {C : Ty (suc Δ)} {B : Ty (suc (suc Δ))} {c : Conceal}
    (A : Ty (suc Δ))
  → ⊢↓[ suc X ⦂ ⇑ᵗ (wkᵗ X C₀) ] c
      ⦂ renameᵗ (extᵗ (punchIn X)) C ↝ B
  → replaceTy X (wkᵗ X C₀) (B [ A ]ᵗ)
    ≡ wkᵗ X
        ((substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C₀))
          (src↓ (suc X) (⇑ᵗ (wkᵗ X C₀)) c B))
          [ substᵗ (resolveSubᵗ X C₀) A ]ᵗ)
conceal-exit-endpoint {X = X} {C₀ = C₀} {C = C} {B = B}
    A c⊢ =
  trans (replace-resolve X C₀ (B [ A ]ᵗ))
    (cong (wkᵗ X)
      (trans (resolve-openᵗ X C₀ B A)
        (cong (λ D → D [ substᵗ (resolveSubᵗ X C₀) A ]ᵗ)
          (trans (sym (conceal-resolved-target c⊢))
            (sym (conceal-resolved-body c⊢))))))

preserve-β-conceal-∀ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {V : Term Θ Δ} {A : Ty (suc Δ)}
    {B : Ty (suc (suc Δ))} {C₀ : Ty Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
  → rep? (Ψ ,end[ X ]) α ≡ just C₀
  → Ψ ∣ [] ⊢ (V ↓[ X ≔ α ] `∀↓ c) ⦂∀ B [ A ]
      ⦂ B [ A ]ᵗ
  → Ψ ∣ [] ⊢
      ( ν[ substᵗ (resolveSubᵗ X C₀) A ]
          ((((shiftᶿ V ↓[ zero ≔ zero ]
                δ↓ (wkᵗ zero (`∀
                  (substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C₀))
                    (src↓ (suc X) (⇑ᵗ (wkᵗ X C₀)) c B)))))
                ⦂∀ swapTopᵗ
                  (⇑ᵗ (substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C₀))
                    (src↓ (suc X) (⇑ᵗ (wkᵗ X C₀)) c B)))
                  [ ＇ zero ])
              ↑[ zero ≔ zero ]
                〖 zero ↑
                  (substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C₀))
                    (src↓ (suc X) (⇑ᵗ (wkᵗ X C₀)) c B)) 〗)))
          ↓[ X ≔ α ] 〖 X ↓ (B [ A ]ᵗ) 〗
      ⦂ B [ A ]ᵗ
preserve-β-conceal-∀ {A = A} {B = B} {X = X} step-eq
    (⊢⦂∀ (⊢conceal {A = `∀ C} {C = R} tyVar-eq typed-eq
      (⊢↓-∀ c⊢) V⊢))
    with just-injective (trans (sym typed-eq) step-eq)
preserve-β-conceal-∀ {A = A} {B = B} {X = X} step-eq
    (⊢⦂∀ (⊢conceal {A = `∀ C} tyVar-eq typed-eq
      (⊢↓-∀ c⊢) V⊢)) | refl =
  ⊢conceal tyVar-eq step-eq exit⊢
    (fresh-∀-region (sym (conceal-resolved-body c⊢)) V⊢)
  where
  exit⊢ = subst≡
    (λ S → ⊢↓[ X ⦂ wkᵗ X _ ] 〖 X ↓ (B [ A ]ᵗ) 〗
      ⦂ S ↝ B [ A ]ᵗ)
    (conceal-exit-endpoint A c⊢)
    (generator-typed↓ X (wkᵗ X _) (B [ A ]ᵗ))

------------------------------------------------------------------------
-- Preservation cases: blame propagation
------------------------------------------------------------------------

preserve-blame-·₁ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ [] ⊢ blame · M ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-·₁ M⊢ = ⊢blame

preserve-blame-·₂ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ [] ⊢ V · blame ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-·₂ M⊢ = ⊢blame

preserve-blame-• : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A : Ty Δ} {B : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ blame ⦂∀ B [ A ] ⦂ B [ A ]ᵗ
  → Ψ ∣ [] ⊢ blame ⦂ B [ A ]ᵗ
preserve-blame-• M⊢ = ⊢blame

preserve-blame-⟨⟩ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M : Term Θ Δ} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → Ψ ∣ [] ⊢ blame ⟨ c ⟩ ⦂ B
  → Ψ ∣ [] ⊢ blame ⦂ B
preserve-blame-⟨⟩ M⊢ = ⊢blame

preserve-blame-reveal : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal} {A : Ty Δ}
  → Ψ ∣ [] ⊢ blame ↑[ X ≔ α ] c ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-reveal M⊢ = ⊢blame

preserve-blame-conceal : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    {A : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ blame ↓[ X ≔ α ] c ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-conceal M⊢ = ⊢blame

preserve-blame-⊕₁ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M : Term Θ Δ} {op : Prim} {A : Ty Δ}
  → Ψ ∣ [] ⊢ blame ⊕[ op ] M ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-⊕₁ M⊢ = ⊢blame

preserve-blame-⊕₂ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {op : Prim} {A : Ty Δ}
  → Ψ ∣ [] ⊢ V ⊕[ op ] blame ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-⊕₂ M⊢ = ⊢blame

preserve-blame-ν : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A B : Ty Δ}
  → Ψ ∣ [] ⊢ ν[ A ] blame ⦂ B
  → Ψ ∣ [] ⊢ blame ⦂ B
preserve-blame-ν M⊢ = ⊢blame

------------------------------------------------------------------------
-- Preservation cases: congruence rules
------------------------------------------------------------------------

preserve-ξ-·₁ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {L′ M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ∣ [] ⊢ L′ ⦂ A ⇒ B
  → Ψ ∣ [] ⊢ L′ · M ⦂ B
preserve-ξ-·₁ M⊢ L′⊢ = ⊢· L′⊢ M⊢

preserve-ξ-·₂ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V M′ : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ [] ⊢ V ⦂ A ⇒ B
  → Ψ ∣ [] ⊢ M′ ⦂ A
  → Ψ ∣ [] ⊢ V · M′ ⦂ B
preserve-ξ-·₂ V⊢ M′⊢ = ⊢· V⊢ M′⊢

preserve-ξ-• : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M M′ : Term Θ Δ} {A : Ty Δ} {B : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ M ⦂∀ B [ A ] ⦂ B [ A ]ᵗ
  → Ψ ∣ [] ⊢ M′ ⦂ `∀ B
  → Ψ ∣ [] ⊢ M′ ⦂∀ B [ A ] ⦂ B [ A ]ᵗ
preserve-ξ-• (⊢⦂∀ M⊢) M′⊢ = ⊢⦂∀ M′⊢

preserve-ξ-⟨⟩ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M M′ : Term Θ Δ} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → Ψ ∣ [] ⊢ M ⟨ c ⟩ ⦂ B
  → Ψ ∣ [] ⊢ M′ ⦂ A
  → Ψ ∣ [] ⊢ M′ ⟨ c ⟩ ⦂ B
preserve-ξ-⟨⟩ (⊢⟨⟩ M⊢ c) M′⊢ = ⊢⟨⟩ M′⊢ c

preserve-ξ-reveal : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {M′ : Term Θ (suc Δ)} {X : TyVar (suc Δ)}
    {α : TyVar Θ} {c : Reveal} {A : Ty (suc Δ)} {B C : Ty Δ}
    {fresh : α ∉ᵛ σ}
  → rep? Ψ α ≡ just C
  → ⊢↑[ X ⦂ wkᵗ X C ] c ⦂ A ↝ wkᵗ X B
  → Ψ ,begin[ X ≔ α ]⟨ fresh ⟩ ∣ [] ⊢ M′ ⦂ A
  → Ψ ∣ [] ⊢ M′ ↑[ X ≔ α ] c ⦂ B
preserve-ξ-reveal α-eq c⊢ M′⊢ = ⊢reveal α-eq c⊢ M′⊢

preserve-ξ-conceal : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {M′ : Term Θ Δ} {X : TyVar (suc Δ)}
    {α : TyVar Θ} {c : Conceal} {A C : Ty Δ}
    {B : Ty (suc Δ)}
  → Vec.lookup σ X ≡ just α
  → rep? (Ψ ,end[ X ]) α ≡ just C
  → ⊢↓[ X ⦂ wkᵗ X C ] c ⦂ wkᵗ X A ↝ B
  → Ψ ,end[ X ] ∣ [] ⊢ M′ ⦂ A
  → Ψ ∣ [] ⊢ M′ ↓[ X ≔ α ] c ⦂ B
preserve-ξ-conceal tyVar-eq α-eq c⊢ M′⊢ =
  ⊢conceal tyVar-eq α-eq c⊢ M′⊢

preserve-ξ-⊕₁ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {L L′ M : Term Θ Δ} {op : Prim}
  → Ψ ∣ [] ⊢ L ⊕[ op ] M ⦂ primResultTy op
  → Ψ ∣ [] ⊢ L′ ⦂ primArgTy op
  → Ψ ∣ [] ⊢ L′ ⊕[ op ] M ⦂ primResultTy op
preserve-ξ-⊕₁ (⊢⊕ op L⊢ M⊢) L′⊢ = ⊢⊕ op L′⊢ M⊢

preserve-ξ-⊕₂ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V M M′ : Term Θ Δ} {op : Prim}
  → Ψ ∣ [] ⊢ V ⊕[ op ] M ⦂ primResultTy op
  → Ψ ∣ [] ⊢ M′ ⦂ primArgTy op
  → Ψ ∣ [] ⊢ V ⊕[ op ] M′ ⦂ primResultTy op
preserve-ξ-⊕₂ (⊢⊕ op V⊢ M⊢) M′⊢ = ⊢⊕ op V⊢ M′⊢

preserve-ξ-ν : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A B : Ty Δ} {M M′ : Term (suc Θ) Δ}
  → Ψ ∣ [] ⊢ ν[ A ] M ⦂ B
  → Ψ ,:= A ∣ [] ⊢ M′ ⦂ B
  → Ψ ∣ [] ⊢ ν[ A ] M′ ⦂ B
preserve-ξ-ν (⊢ν M⊢) M′⊢ = ⊢ν M′⊢

------------------------------------------------------------------------
-- Preservation cases: straightforward region floats
------------------------------------------------------------------------

preserve-float-·₁ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A C : Ty Δ} {M : Term (suc Θ) Δ} {N : Term Θ Δ}
  → Ψ ∣ [] ⊢ (ν[ A ] M) · N ⦂ C
  → Ψ ∣ [] ⊢ ν[ A ] (M · shiftᶿ N) ⦂ C
preserve-float-·₁ (⊢· (⊢ν M⊢) N⊢) =
  ⊢ν (⊢· M⊢ (⊢shiftᶿ N⊢))

preserve-float-·₂ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A C : Ty Δ} {V : Term Θ Δ} {M : Term (suc Θ) Δ}
  → Ψ ∣ [] ⊢ V · (ν[ A ] M) ⦂ C
  → Ψ ∣ [] ⊢ ν[ A ] (shiftᶿ V · M) ⦂ C
preserve-float-·₂ (⊢· V⊢ (⊢ν M⊢)) =
  ⊢ν (⊢· (⊢shiftᶿ V⊢) M⊢)

preserve-float-• : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A C : Ty Δ} {B : Ty (suc Δ)} {M : Term (suc Θ) Δ}
  → Ψ ∣ [] ⊢ (ν[ A ] M) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
  → Ψ ∣ [] ⊢ ν[ A ] (M ⦂∀ B [ C ]) ⦂ B [ C ]ᵗ
preserve-float-• (⊢⦂∀ (⊢ν M⊢)) = ⊢ν (⊢⦂∀ M⊢)

preserve-float-⟨⟩ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A B C : Ty Δ} {M : Term (suc Θ) Δ} {μ : Env∼ Δ}
    {c : μ ⊢ B ∼ C}
  → Ψ ∣ [] ⊢ (ν[ A ] M) ⟨ c ⟩ ⦂ C
  → Ψ ∣ [] ⊢ ν[ A ] (M ⟨ c ⟩) ⦂ C
preserve-float-⟨⟩ (⊢⟨⟩ (⊢ν M⊢) c) = ⊢ν (⊢⟨⟩ M⊢ c)

preserve-float-⊕₁ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A : Ty Δ} {M : Term (suc Θ) Δ} {N : Term Θ Δ} {op}
  → Ψ ∣ [] ⊢ (ν[ A ] M) ⊕[ op ] N ⦂ primResultTy op
  → Ψ ∣ [] ⊢ ν[ A ] (M ⊕[ op ] shiftᶿ N) ⦂ primResultTy op
preserve-float-⊕₁ (⊢⊕ op (⊢ν M⊢) N⊢) =
  ⊢ν (⊢⊕ op M⊢ (⊢shiftᶿ N⊢))

preserve-float-⊕₂ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A : Ty Δ} {V : Term Θ Δ} {M : Term (suc Θ) Δ} {op}
  → Ψ ∣ [] ⊢ V ⊕[ op ] (ν[ A ] M) ⦂ primResultTy op
  → Ψ ∣ [] ⊢ ν[ A ] (shiftᶿ V ⊕[ op ] M) ⦂ primResultTy op
preserve-float-⊕₂ (⊢⊕ op V⊢ (⊢ν M⊢)) =
  ⊢ν (⊢⊕ op (⊢shiftᶿ V⊢) M⊢)

------------------------------------------------------------------------
-- Closed one-step preservation assembler
------------------------------------------------------------------------

preserve : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {M M′ : Term Θ Δ} {A}
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ⊢ M —→ M′
  → Ψ ∣ [] ⊢ M′ ⦂ A
preserve typing (δ-⊕ δ) = preserve-δ-⊕ δ typing
preserve typing (β Vᵥ) = preserve-β typing
preserve (⊢⟨⟩ V⊢ (id a)) (β-id Vᵥ) = V⊢
preserve typing@(⊢· (⊢⟨⟩ V⊢ (c ↦ d)) W⊢) (β-⇒ Vᵥ Wᵥ) =
  preserve-β-⇒ typing
preserve typing@(⊢⦂∀ (⊢⟨⟩ V⊢ (∀ᶜ c))) (β-∀ Vᵥ eq) =
  preserve-β-∀ eq typing
preserve typing@(⊢⟨⟩ V⊢ (c !)) (ground Vᵥ neq) =
  preserve-ground typing
preserve typing@(⊢⟨⟩ V⊢ (？ c)) (expand Vᵥ neq) =
  preserve-expand typing
preserve typing@(⊢⟨⟩ (⊢⟨⟩ V⊢ c) d) (tag-untag Vᵥ) =
  preserve-tag-untag typing
preserve typing (tag-untag-bad Vᵥ neq) = ⊢blame
preserve typing (blame-bot-intro Vᵥ) = ⊢blame
preserve typing (β-reveal-⇒ Vᵥ Wᵥ) = preserve-β-reveal-⇒ typing
preserve typing (β-conceal-⇒ Vᵥ Wᵥ) =
  preserve-β-conceal-⇒ typing
preserve typing (id-cancel canonical) = preserve-id-cancel typing
preserve typing id-reveal = preserve-id-reveal typing
preserve typing id-conceal = preserve-id-conceal typing
preserve typing (conceal-reveal Vᵥ) = preserve-conceal-reveal typing
preserve typing blame-·₁ = ⊢blame
preserve typing (blame-·₂ Vᵥ) = ⊢blame
preserve typing blame-• = ⊢blame
preserve typing blame-⟨⟩ = ⊢blame
preserve typing blame-reveal = ⊢blame
preserve typing blame-conceal = ⊢blame
preserve typing blame-⊕₁ = ⊢blame
preserve typing (blame-⊕₂ Vᵥ) = ⊢blame
preserve typing blame-ν = ⊢blame
preserve typing const-ν = preserve-const-ν typing
preserve typing@(⊢⦂∀ (⊢Λ V⊢)) (β-Λ Vᵥ) = preserve-β-Λ typing
preserve typing@(⊢⦂∀ (⊢⟨⟩ V⊢ c)) (β-gen Vᵥ A≠★ safe) =
  preserve-β-gen typing
preserve typing@(⊢⟨⟩ V⊢ c) (β-inst Vᵥ B≠★) =
  preserve-β-inst typing
preserve typing@(⊢⦂∀ (⊢reveal α∈ c⊢ V⊢)) (β-reveal-∀ Vᵥ) =
  preserve-β-reveal-∀ typing
preserve typing@(⊢⦂∀ (⊢conceal tyVar∈ β∈ c⊢ V⊢))
    (β-conceal-∀ α∈ Vᵥ) =
  preserve-β-conceal-∀ α∈ typing
preserve (⊢· L⊢ M⊢) (ξ-·₁ step) =
  preserve-ξ-·₁ M⊢ (preserve L⊢ step)
preserve (⊢· V⊢ M⊢) (ξ-·₂ Vᵥ step) =
  preserve-ξ-·₂ V⊢ (preserve M⊢ step)
preserve typing@(⊢⦂∀ M⊢) (ξ-• step) =
  preserve-ξ-• typing (preserve M⊢ step)
preserve typing@(⊢⟨⟩ M⊢ c) (ξ-⟨⟩ step) =
  preserve-ξ-⟨⟩ typing (preserve M⊢ step)
preserve (⊢reveal α∈ c⊢ M⊢) (ξ-reveal step) =
  preserve-ξ-reveal α∈ c⊢ (preserve M⊢ step)
preserve (⊢conceal tyVar∈ α∈ c⊢ M⊢) (ξ-conceal step) =
  preserve-ξ-conceal tyVar∈ α∈ c⊢ (preserve M⊢ step)
preserve typing@(⊢⊕ op L⊢ M⊢) (ξ-⊕₁ step) =
  preserve-ξ-⊕₁ typing (preserve L⊢ step)
preserve typing@(⊢⊕ op V⊢ M⊢) (ξ-⊕₂ Vᵥ step) =
  preserve-ξ-⊕₂ typing (preserve M⊢ step)
preserve typing@(⊢ν M⊢) (ξ-ν step) =
  preserve-ξ-ν typing (preserve M⊢ step)
preserve typing (float-·₁ result) = preserve-float-·₁ typing
preserve typing (float-·₂ Vᵥ result) = preserve-float-·₂ typing
preserve typing@(⊢⦂∀ (⊢ν M⊢)) (float-• result) =
  preserve-float-• typing
preserve typing@(⊢⟨⟩ (⊢ν M⊢) c) (float-⟨⟩ result) =
  preserve-float-⟨⟩ typing
preserve typing@(⊢⊕ op (⊢ν M⊢) N⊢) (float-⊕₁ result) =
  preserve-float-⊕₁ typing
preserve typing@(⊢⊕ op V⊢ (⊢ν M⊢)) (float-⊕₂ Vᵥ result) =
  preserve-float-⊕₂ typing

------------------------------------------------------------------------
-- Historical refutation records
------------------------------------------------------------------------

-- `β-reveal-∀`: the old rule chose its source body only in the contractum,
-- so the checked ℕ/𝔹 instance stepped to an untypable term.  Source
-- determinacy now computes ℕ from the redex, making that step impossible.
--
-- `β-conceal-∀`: the old type variable-dependent instantiation lost the abstract
-- type variable.  The deterministic rule resolves it at the ended view and seals the
-- result on exit; the former instance is now preserved.
--
-- `β-conceal-⇒`: the former obstruction was precisely the missing re-entry
-- transport.  `⊢reenter` now supplies the balanced end/begin scope.
--
-- `float-reveal`/`float-conceal`: commits 3ee5de8c/a18f75f4 record the
-- resolving-float counterexample.  U11 deleted both delimiter-crossing
-- ν-floats, so regions remain at birth depth.
--
-- Strict `id-cancel`: commit c5ee0351 records the loose-rule refutation.
-- Mismatched type variable/anchor pairs are adapter values and cannot take the strict
-- rule.  A ν stranded between seal and unseal is classified the same way.
--
-- Loose conceal/reveal anchors: the old term is untypable under σ-indexed
-- telescopes because a type variable has exactly one intrinsic anchor.
--
-- Arbitrary-Γ preservation remains false by design: `β-reveal-⇒` can route a
-- captured lambda into the closed conceal interior.  This is why `preserve`
-- below is stated at `[]`.  The original checked records are retained in the
-- history; current executable coverage lives in `ThetaRegression` and the
-- evaluator probes, whose statements use the equation-based lookup surface.
