module alt.ThetaPreservation where

-- File Charter:
--   * Develops one-step preservation for closed configurations of the
--     Θ-indexed alternative calculus, one lemma per reduction rule.
--   * The strict rule repairs the counterexample from commit c5ee0351: its
--     mismatched identity delimiters now form an adapter value rather than a
--     redex.  That historical instance remains below as a regression.
--   * The old loose-anchor counterexample is now untypable: crossing entries
--     record their anchors, so typing forces both nodes' slot and anchor data.
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
--   * The former slot-dependent `β-conceal-∀` obstruction is retained as
--     a resolved regression.  The contractum resolves its instantiation and
--     computed source in the deleted view, then seals the result on exit.
--   * Resolving deletion makes the former `β-conceal-⇒` counterexample's
--     contractum typable.  The assembler case remains deliberately parked:
--     whether region-interior material may acquire that representation
--     knowledge is a pending direction decision, not a proof-engineering one.
--   * The refuted resolving `float-reveal` rule was deleted together with
--     `float-conceal`: regions now stay at their birth delimiter depth.  The
--     former checked counterexample remains below as a historical comment.
--
-- U12 indexed-OPAQUE obstruction (parked, not forced): let
--
--   Ω = ∅ ,:= ‵ `ℕ ,typ[ zero ≔ zero ] ,end[ zero ]
--   V = ($ (κℕ 7)) ↑[ zero ≔ zero ] id↑.
--
-- The ended telescope resolves its old anchor in knowledge mode, so
-- `Ω ,typ ∣ [] ⊢ V ⦂ ‵ `ℕ`: the lexical entry preserves `know []`, and the
-- lookup then crosses `,end[ zero ]` and resolves the pending slot.  Hence
-- `(Λ V) ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]` is a closed, typed `β-Λ` redex at Ω.
-- Its contractum allocates a fresh anchor and replaces the lexical entry by
-- the live begin `(Ω ,:= ‵ `ℕ) ,typ[ zero ≔ zero ]`.  Typing `shiftᶿ V` now
-- needs the old-anchor lookup
--
--   (Ω ,:= ‵ `ℕ) ,typ[ zero ≔ zero ]
--     ∋rep[ know [] ] suc zero ≔ ‵ `ℕ.
--
-- Crossing that live begin first changes the recursive obligation to
-- `Ω ∋rep[ opaq ] zero ≔ ‵ `ℕ`; Ω's end marker has deliberately no opaque
-- constructor, so the lookup is impossible.  This is the same refusal the
-- required T3 regression demands.  Thus the old arbitrary-telescope
-- `⊢allocate-lexical` lemma, and consequently this `β-Λ` preservation case,
-- cannot coexist with the approved transition table without an additional
-- restriction or a direction change.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (¬_; yes; no)

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
-- Generator endpoint at a freshly allocated slot
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
-- Exchange at the two newest regular slots
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

constant-type : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ} {κ} {A : Ty Δ}
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

terminal-anchor : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
  → (Ψ ,typ[ X ≔ α ]) ∋typ[ KNOWLEDGE ] Y ≔ β
  → Y ≡ X
  → β ≡ α
terminal-anchor here-typ refl = refl
terminal-anchor (skip-cross-typ {Y = Y} Y∈) eq =
  ⊥-elim (punchIn≢ _ Y (sym eq))
terminal-anchor (skip-cross-other-typ {Y = Y} neq Y∈) eq =
  ⊥-elim (punchIn≢ _ Y (sym eq))

------------------------------------------------------------------------
-- Preservation cases: computational rules
------------------------------------------------------------------------

preserve-δ-⊕ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {op κ₁ κ₂ κ₃} {A}
  → δ op κ₁ κ₂ κ₃
  → Ψ ∣ [] ⊢ ($ κ₁ ⊕[ op ] $ κ₂) ⦂ A
  → Ψ ∣ [] ⊢ $ κ₃ ⦂ A
preserve-δ-⊕ δ-add (⊢⊕ addℕ (⊢$ _) (⊢$ _)) = ⊢$ _
preserve-δ-⊕ δ-and (⊢⊕ and𝔹 (⊢$ _) (⊢$ _)) = ⊢$ _

preserve-β : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V N : Term Θ Δ} {A B}
  → Ψ ∣ [] ⊢ (ƛ A ˙ N) · V ⦂ B
  → Ψ ∣ [] ⊢ N [ V ] ⦂ B
preserve-β (⊢· (⊢ƛ N⊢) V⊢) = ⊢[] N⊢ V⊢

preserve-β-id : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {A} {a : Atom A}
  → Ψ ∣ [] ⊢ V ⟨ id {μ = μ} a ⟩ ⦂ A
  → Ψ ∣ [] ⊢ V ⦂ A
preserve-β-id (⊢⟨⟩ V⊢ (id a)) = V⊢

preserve-β-⇒ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V W : Term Θ Δ}
    {μ : Env∼ Δ} {A A′ B B′}
    {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
  → Ψ ∣ [] ⊢ (V ⟨ c ↦ d ⟩) · W ⦂ B′
  → Ψ ∣ [] ⊢ (V · (W ⟨ c ⟩)) ⟨ d ⟩ ⦂ B′
preserve-β-⇒ (⊢· (⊢⟨⟩ V⊢ (c ↦ d)) W⊢) =
  ⊢⟨⟩ (⊢· V⊢ (⊢⟨⟩ W⊢ c)) d

preserve-β-∀ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {A B : Ty (suc Δ)} {C : Ty Δ}
    {c : extᵐ μ ⊢ A ∼ B} {d : μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ}
  → d ≡ c [ C ]ᶜ
  → Ψ ∣ [] ⊢ (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
  → Ψ ∣ [] ⊢ (V ⦂∀ A [ C ]) ⟨ d ⟩ ⦂ B [ C ]ᵗ
preserve-β-∀ refl (⊢⦂∀ (⊢⟨⟩ V⊢ (∀ᶜ c))) =
  ⊢⟨⟩ (⊢⦂∀ V⊢) (c [ _ ]ᶜ)

preserve-ground : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {A G : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    {c : μ ⊢ A ∼ G} ⦃ Ans : NonStar A ⦄ ⦃ Gns : NonStar G ⦄
  → Ψ ∣ [] ⊢ V ⟨ c ! ⟩ ⦂ ★
  → Ψ ∣ [] ⊢ V ⟨ c ⟩ ⟨ (idᵍ Gᵍ) ! ⟩ ⦂ ★
preserve-ground ⦃ Gᵍ = Gᵍ ⦄ (⊢⟨⟩ V⊢ (c !)) =
  ⊢⟨⟩ (⊢⟨⟩ V⊢ c) ((idᵍ Gᵍ) !)

preserve-expand : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {G B : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
    {c : μ ⊢ G ∼ B} ⦃ Bns : NonStar B ⦄ ⦃ Gns : NonStar G ⦄
  → Ψ ∣ [] ⊢ V ⟨ ？ c ⟩ ⦂ B
  → Ψ ∣ [] ⊢ V ⟨ ？ (idᵍ Gᵍ) ⟩ ⟨ c ⟩ ⦂ B
preserve-expand ⦃ Gᵍ = Gᵍ ⦄ (⊢⟨⟩ V⊢ (？ c)) =
  ⊢⟨⟩ (⊢⟨⟩ V⊢ (？ (idᵍ Gᵍ))) c

preserve-tag-untag : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V : Term Θ Δ}
    {μ ν : Env∼ Δ} {G : Ty Δ} ⦃ Gᵍ : Ground G ⦄
    ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Gns : NonStar G ⦄
  → Ψ ∣ [] ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Gᵍ) ⟩ ⦂ G
  → Ψ ∣ [] ⊢ V ⦂ G
preserve-tag-untag (⊢⟨⟩ (⊢⟨⟩ V⊢ c) d) = V⊢

preserve-tag-untag-bad : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-tag-untag-bad M⊢ = ⊢blame

preserve-blame-bot-intro : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-bot-intro M⊢ = ⊢blame

preserve-β-reveal-⇒ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ (suc Δ)} {W : Term Θ Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal} {d : Reveal}
    {B : Ty Δ}
  → Ψ ∣ [] ⊢ (V ↑[ X ≔ α ] (c ↦↑ d)) · W ⦂ B
  → Ψ ∣ [] ⊢ (V · (W ↓[ X ≔ α ] c)) ↑[ X ≔ α ] d ⦂ B
preserve-β-reveal-⇒ {Ψ = Ψ} {W = W} {X = X} {α = α}
    (⊢· (⊢reveal α∈ (⊢↑-⇒ c⊢ d⊢) V⊢) W⊢) =
  ⊢reveal α∈ d⊢
    (⊢· V⊢ (⊢conceal here-typ deleted-lookup c⊢ deleted-W⊢))
  where
  env-eq = ∖-typ-here Ψ X α
  deleted-lookup =
    subst≡ (λ Φ → Φ ∋ α := _) (sym env-eq) α∈
  deleted-W⊢ =
    subst≡ (λ Φ → Φ ∣ [] ⊢ W ⦂ _) (sym env-eq) W⊢

preserve-id-cancel : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ Δ} {X : TyVar (suc Δ)} {α : TyVar Θ} {A}
  → Ψ ∣ [] ⊢ (V ↓[ X ≔ α ] id↓) ↑[ X ≔ α ] id↑ ⦂ A
  → Ψ ∣ [] ⊢ V ⦂ A
preserve-id-cancel {Ψ = Ψ} {V = V} {X = X} {α = α}
    (⊢reveal α∈ c↑ (⊢conceal slot∈ β∈ c↓ V⊢)) =
  subst≡ (λ B → Ψ ∣ [] ⊢ V ⦂ B) type-eq ambient-V⊢
  where
  env-eq = ∖-typ-here Ψ X α
  ambient-V⊢ =
    subst≡ (λ Φ → Φ ∣ [] ⊢ V ⦂ _) env-eq V⊢
  type-eq = wkTy-injective X
    (trans (id↓-endpoint c↓) (id↑-endpoint c↑))

preserve-id-reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {X} {α}
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

preserve-id-conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)} {X} {α}
    {κ} {A : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ ($ κ) ↓[ X ≔ α ] id↓ ⦂ A
  → Ψ ∣ [] ⊢ $ κ ⦂ A
preserve-id-conceal {Ψ = Ψ} {X = X} {κ = κ}
    (⊢conceal slot∈ α∈ c⊢ M⊢) =
  subst≡ (λ B → Ψ ∣ [] ⊢ $ κ ⦂ B) type-eq (⊢$ κ)
  where
  type-eq = trans (const-wk X κ)
    (trans (cong (wkᵗ X) (constant-type M⊢)) (id↓-endpoint c⊢))

preserve-conceal-reveal-matched : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ Δ} {X Y : TyVar (suc Δ)} {α β : TyVar Θ} {A}
  → X ≡ Y
  → α ≡ β
  → Ψ ∣ [] ⊢ (V ↓[ X ≔ α ] seal) ↑[ Y ≔ β ] unseal ⦂ A
  → Ψ ∣ [] ⊢ V ⦂ A
preserve-conceal-reveal-matched {Ψ = Ψ} {X = X} {α = α} refl refl
    (⊢reveal β∈ c↑ (⊢conceal slot∈ α∈ c↓ V⊢)) =
  subst≡ (λ B → Ψ ∣ [] ⊢ _ ⦂ B) type-eq ambient-V⊢
  where
  env-eq = ∖-typ-here Ψ X α
  ambient-V⊢ = subst≡ (λ Φ → Φ ∣ [] ⊢ _ ⦂ _) env-eq V⊢
  ambient-α∈ = subst≡ (λ Φ → Φ ∋ α := _) env-eq α∈
  source-eq = wkTy-injective X (seal-source c↓)
  target-eq = wkTy-injective X (unseal-target c↑)
  type-eq = trans source-eq
    (trans (anchor-lookup-unique ambient-α∈ β∈) (sym target-eq))

preserve-conceal-reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ Δ} {X Y : TyVar (suc Δ)} {α β : TyVar Θ} {A}
  → Ψ ∣ [] ⊢ (V ↓[ X ≔ α ] seal) ↑[ Y ≔ β ] unseal ⦂ A
  → Ψ ∣ [] ⊢ V ⦂ A
preserve-conceal-reveal typing@(⊢reveal β∈ c↑
    (⊢conceal slot∈ α∈ c↓ V⊢)) =
  preserve-conceal-reveal-matched slot-eq anchor-eq typing
  where
  slot-eq = ty-var-injective
    (trans (sym (seal-target c↓)) (unseal-source c↑))
  anchor-eq = terminal-anchor slot∈ slot-eq

preserve-const-ν : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {C A : Ty Δ} {κ}
  → Ψ ∣ [] ⊢ ν[ C ] ($ κ) ⦂ A
  → Ψ ∣ [] ⊢ $ κ ⦂ A
preserve-const-ν (⊢ν (⊢$ κ)) = ⊢$ κ

preserve-β-inst : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V : Term Θ Δ}
    {μ : Env∼ Δ} {A : Ty (suc Δ)} {B : Ty Δ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
    {B≠★ : B ≢ ★}
  → Ψ ∣ [] ⊢ V ⟨ (inst c) B≠★ ⟩ ⦂ B
  → Ψ ∣ [] ⊢ (V ⦂∀ A [ ★ ]) ⟨ c [ ★/0 ]ᶜ ⟩ ⦂ B
preserve-β-inst (⊢⟨⟩ V⊢ ((inst c) B≠★)) =
  ⊢⟨⟩ (⊢⦂∀ V⊢) (c [ ★/0 ]ᶜ)

fresh-delimiter-conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M : Term (suc Θ) Δ} {A C : Ty Δ}
  → Ψ ,:= C ∣ [] ⊢ M ⦂ A
  → (Ψ ,:= C) ,typ[ zero ≔ zero ] ∣ []
      ⊢ M ↓[ zero ≔ zero ] δ↓ (⇑ᵗ A) ⦂ ⇑ᵗ A
fresh-delimiter-conceal {Ψ = Ψ} {A = A} {C = C} M⊢ =
  ⊢conceal here-typ target-lookup
    (delimiter-typed↓ zero (⇑ᵗ C) (⇑ᵗ A)) target-M⊢
  where
  env-eq = ∖-typ-here (Ψ ,:= C) zero zero
  target-lookup =
    subst≡ (λ Φ → Φ ∋ zero := C) (sym env-eq) Z
  target-M⊢ =
    subst≡ (λ Φ → Φ ∣ [] ⊢ _ ⦂ A) (sym env-eq) M⊢

∖-fresh-before-crossing : ∀ {Θ Δ} (Ψ : TyEnv Θ Δ)
    (A : Ty Δ) (X : TyVar (suc Δ)) (α : TyVar Θ)
  → ((((Ψ ,:= A) ,typ[ zero ≔ zero ])
        ,typ[ suc X ≔ suc α ]) ∖ zero)
    ≡ (Ψ ,:= A) ,typ[ X ≔ suc α ]
∖-fresh-before-crossing Ψ A X α =
  trans
    (∖-typ-other ((Ψ ,:= A) ,typ[ zero ≔ zero ])
      (suc X) zero (suc α) (λ ()) (λ ()))
    (cong (λ Φ → Φ ,typ[ X ≔ suc α ])
      (∖-typ-here (Ψ ,:= A) zero zero))

⊢shift-crossing : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M : Term Θ (suc Δ)} {T : Ty (suc Δ)} {A : Ty Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ}
  → Ψ ,typ[ X ≔ α ] ∣ [] ⊢ M ⦂ T
  → (Ψ ,:= A) ,typ[ X ≔ suc α ] ∣ [] ⊢ shiftᶿ M ⦂ T
⊢shift-crossing {X = X} {α = α} M⊢ =
  ⊢renameᶿ-target
    (anchor-target-typ X α visible-shift-target) M⊢

fresh-∀-entry-crossed : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ (suc Δ)} {C : Ty (suc (suc Δ))} {A : Ty Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ}
  → Ψ ,typ[ X ≔ α ] ∣ [] ⊢ V ⦂ `∀ C
  → ((Ψ ,:= A) ,typ[ zero ≔ zero ])
      ,typ[ suc X ≔ suc α ] ∣ [] ⊢
      (shiftᶿ V ↓[ zero ≔ zero ] δ↓ (wkᵗ zero (`∀ C)))
        ⦂∀ swapTopᵗ (⇑ᵗ C) [ ＇ zero ] ⦂ C
fresh-∀-entry-crossed {Ψ = Ψ} {V = V} {C = C} {A = A}
    {X = X} {α = α} V⊢ =
  subst≡ (λ T → ambient ∣ [] ⊢ applied ⦂ T)
    (swap-shift-open-zero C) (⊢⦂∀ exchanged⊢)
  where
  ambient = ((Ψ ,:= A) ,typ[ zero ≔ zero ])
    ,typ[ suc X ≔ suc α ]
  deleted = (Ψ ,:= A) ,typ[ X ≔ suc α ]
  entered = shiftᶿ V ↓[ zero ≔ zero ] δ↓ (wkᵗ zero (`∀ C))
  applied = entered ⦂∀ swapTopᵗ (⇑ᵗ C) [ ＇ zero ]
  env-eq = ∖-fresh-before-crossing Ψ A X α
  deleted-V⊢ = ⊢shift-crossing V⊢
  target-V⊢ =
    subst≡ (λ Φ → Φ ∣ [] ⊢ shiftᶿ V ⦂ `∀ C)
      (sym env-eq) deleted-V⊢
  deleted-lookup : deleted ∋ zero := wkᵗ X A
  deleted-lookup = skip-typ Z
  target-lookup =
    subst≡ (λ Φ → Φ ∋ zero := wkᵗ X A)
      (sym env-eq) deleted-lookup
  entered⊢ = ⊢conceal (skip-cross-typ here-typ) target-lookup
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

fresh-∀-entry : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ Δ} {A : Ty Δ} {C : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ V ⦂ `∀ C
  → (Ψ ,:= A) ,typ[ zero ≔ zero ] ∣ [] ⊢
      (shiftᶿ V ↓[ zero ≔ zero ] δ↓ (wkᵗ zero (`∀ C)))
        ⦂∀ swapTopᵗ (⇑ᵗ C) [ ＇ zero ] ⦂ C
fresh-∀-entry {Ψ = Ψ} {V = V} {A = A} {C = C} V⊢ =
  subst≡ (λ T → target ∣ [] ⊢ applied ⦂ T)
    (swap-shift-open-zero C) (⊢⦂∀ entered⊢)
  where
  target = (Ψ ,:= A) ,typ[ zero ≔ zero ]
  entered = shiftᶿ V ↓[ zero ≔ zero ] δ↓ (wkᵗ zero (`∀ C))
  applied = entered ⦂∀ swapTopᵗ (⇑ᵗ C) [ ＇ zero ]
  entered⊢ = subst≡ (λ T → target ∣ [] ⊢ entered ⦂ T)
    (wk-zero-∀-swap C)
    (fresh-delimiter-conceal (⊢shiftᶿ V⊢))

preserve-β-Λ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ (suc Δ)} {B : Ty (suc Δ)} {C : Ty Δ}
  → Ψ ∣ [] ⊢ (Λ V) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
  → Ψ ∣ [] ⊢
      ν[ C ] (shiftᶿ V ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)
      ⦂ B [ C ]ᵗ
preserve-β-Λ {B = B} {C = C} (⊢⦂∀ (⊢Λ V⊢)) =
  ⊢ν (⊢reveal Z (generator-typed B C) (⊢allocate-lexical V⊢))

preserve-β-gen : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ Δ} {μ : Env∼ Δ} {A C : Ty Δ}
    {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄ {A≠★ : A ≢ ★}
  → Ψ ∣ [] ⊢ (V ⟨ (gen c) A≠★ ⟩) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
  → Ψ ∣ [] ⊢ ν[ C ]
      (((shiftᶿ V ↓[ zero ≔ zero ] δ↓ (⇑ᵗ A)) ⟨ c ⟩)
        ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)
      ⦂ B [ C ]ᵗ
preserve-β-gen {B = bodyTy}
    (⊢⦂∀ (⊢⟨⟩ V⊢ ((gen c) A≠★))) =
  ⊢ν (⊢reveal Z (generator-typed bodyTy _)
    (⊢⟨⟩ (fresh-delimiter-conceal (⊢shiftᶿ V⊢)) c))

preserve-β-reveal-∀ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
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
preserve-β-reveal-∀ {A = A} {B = B} {X = X}
    (⊢⦂∀ (⊢reveal α∈ (⊢↑-∀ c⊢) V⊢)) | refl =
  ⊢ν (⊢reveal Z (generator-typed B A)
    (⊢reveal (skip-typ (S α∈)) (exchange-reveal-∀ c⊢)
      (fresh-∀-entry-crossed V⊢)))

fresh-∀-region : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
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
  ⊢ν (⊢reveal Z (generator-typed _ _)
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

preserve-β-conceal-∀ : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
    {V : Term Θ Δ} {A : Ty (suc Δ)}
    {B : Ty (suc (suc Δ))} {C₀ : Ty Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
  → (Ψ ∖ X) ∋ α := C₀
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
preserve-β-conceal-∀ {A = A} {B = B} {X = X} step∈
    (⊢⦂∀ (⊢conceal {A = `∀ C} {C = R} slot∈ typed∈
      (⊢↓-∀ c⊢) V⊢))
    with anchor-lookup-unique typed∈ step∈
preserve-β-conceal-∀ {A = A} {B = B} {X = X} step∈
    (⊢⦂∀ (⊢conceal {A = `∀ C} slot∈ typed∈
      (⊢↓-∀ c⊢) V⊢)) | refl =
  ⊢conceal slot∈ step∈ exit⊢
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

preserve-blame-·₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ [] ⊢ blame · M ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-·₁ M⊢ = ⊢blame

preserve-blame-·₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ [] ⊢ V · blame ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-·₂ M⊢ = ⊢blame

preserve-blame-• : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {A : Ty Δ} {B : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ blame ⦂∀ B [ A ] ⦂ B [ A ]ᵗ
  → Ψ ∣ [] ⊢ blame ⦂ B [ A ]ᵗ
preserve-blame-• M⊢ = ⊢blame

preserve-blame-⟨⟩ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M : Term Θ Δ} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → Ψ ∣ [] ⊢ blame ⟨ c ⟩ ⦂ B
  → Ψ ∣ [] ⊢ blame ⦂ B
preserve-blame-⟨⟩ M⊢ = ⊢blame

preserve-blame-reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal} {A : Ty Δ}
  → Ψ ∣ [] ⊢ blame ↑[ X ≔ α ] c ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-reveal M⊢ = ⊢blame

preserve-blame-conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    {A : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ blame ↓[ X ≔ α ] c ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-conceal M⊢ = ⊢blame

preserve-blame-⊕₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M : Term Θ Δ} {op : Prim} {A : Ty Δ}
  → Ψ ∣ [] ⊢ blame ⊕[ op ] M ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-⊕₁ M⊢ = ⊢blame

preserve-blame-⊕₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V : Term Θ Δ} {op : Prim} {A : Ty Δ}
  → Ψ ∣ [] ⊢ V ⊕[ op ] blame ⦂ A
  → Ψ ∣ [] ⊢ blame ⦂ A
preserve-blame-⊕₂ M⊢ = ⊢blame

preserve-blame-ν : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {A B : Ty Δ}
  → Ψ ∣ [] ⊢ ν[ A ] blame ⦂ B
  → Ψ ∣ [] ⊢ blame ⦂ B
preserve-blame-ν M⊢ = ⊢blame

------------------------------------------------------------------------
-- Preservation cases: congruence rules
------------------------------------------------------------------------

preserve-ξ-·₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {L L′ M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ∣ [] ⊢ L′ ⦂ A ⇒ B
  → Ψ ∣ [] ⊢ L′ · M ⦂ B
preserve-ξ-·₁ M⊢ L′⊢ = ⊢· L′⊢ M⊢

preserve-ξ-·₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V M M′ : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ [] ⊢ V ⦂ A ⇒ B
  → Ψ ∣ [] ⊢ M′ ⦂ A
  → Ψ ∣ [] ⊢ V · M′ ⦂ B
preserve-ξ-·₂ V⊢ M′⊢ = ⊢· V⊢ M′⊢

preserve-ξ-• : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M M′ : Term Θ Δ} {A : Ty Δ} {B : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ M ⦂∀ B [ A ] ⦂ B [ A ]ᵗ
  → Ψ ∣ [] ⊢ M′ ⦂ `∀ B
  → Ψ ∣ [] ⊢ M′ ⦂∀ B [ A ] ⦂ B [ A ]ᵗ
preserve-ξ-• (⊢⦂∀ M⊢) M′⊢ = ⊢⦂∀ M′⊢

preserve-ξ-⟨⟩ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M M′ : Term Θ Δ} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → Ψ ∣ [] ⊢ M ⟨ c ⟩ ⦂ B
  → Ψ ∣ [] ⊢ M′ ⦂ A
  → Ψ ∣ [] ⊢ M′ ⟨ c ⟩ ⦂ B
preserve-ξ-⟨⟩ (⊢⟨⟩ M⊢ c) M′⊢ = ⊢⟨⟩ M′⊢ c

preserve-ξ-reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {M M′ : Term Θ (suc Δ)} {X : TyVar (suc Δ)}
    {α : TyVar Θ} {c : Reveal} {A : Ty (suc Δ)} {B C : Ty Δ}
  → Ψ ∋ α := C
  → ⊢↑[ X ⦂ wkᵗ X C ] c ⦂ A ↝ wkᵗ X B
  → Ψ ,typ[ X ≔ α ] ∣ [] ⊢ M′ ⦂ A
  → Ψ ∣ [] ⊢ M′ ↑[ X ≔ α ] c ⦂ B
preserve-ξ-reveal α∈ c⊢ M′⊢ = ⊢reveal α∈ c⊢ M′⊢

preserve-ξ-conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
    {M M′ : Term Θ Δ} {X : TyVar (suc Δ)}
    {α : TyVar Θ} {c : Conceal} {A C : Ty Δ}
    {B : Ty (suc Δ)}
  → Ψ ∋typ X ≔ α
  → (Ψ ∖ X) ∋ α := C
  → ⊢↓[ X ⦂ wkᵗ X C ] c ⦂ wkᵗ X A ↝ B
  → Ψ ∖ X ∣ [] ⊢ M′ ⦂ A
  → Ψ ∣ [] ⊢ M′ ↓[ X ≔ α ] c ⦂ B
preserve-ξ-conceal slot∈ α∈ c⊢ M′⊢ =
  ⊢conceal slot∈ α∈ c⊢ M′⊢

preserve-ξ-⊕₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {L L′ M : Term Θ Δ} {op : Prim}
  → Ψ ∣ [] ⊢ L ⊕[ op ] M ⦂ primResultTy op
  → Ψ ∣ [] ⊢ L′ ⦂ primArgTy op
  → Ψ ∣ [] ⊢ L′ ⊕[ op ] M ⦂ primResultTy op
preserve-ξ-⊕₁ (⊢⊕ op L⊢ M⊢) L′⊢ = ⊢⊕ op L′⊢ M⊢

preserve-ξ-⊕₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {V M M′ : Term Θ Δ} {op : Prim}
  → Ψ ∣ [] ⊢ V ⊕[ op ] M ⦂ primResultTy op
  → Ψ ∣ [] ⊢ M′ ⦂ primArgTy op
  → Ψ ∣ [] ⊢ V ⊕[ op ] M′ ⦂ primResultTy op
preserve-ξ-⊕₂ (⊢⊕ op V⊢ M⊢) M′⊢ = ⊢⊕ op V⊢ M′⊢

preserve-ξ-ν : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {A B : Ty Δ} {M M′ : Term (suc Θ) Δ}
  → Ψ ∣ [] ⊢ ν[ A ] M ⦂ B
  → Ψ ,:= A ∣ [] ⊢ M′ ⦂ B
  → Ψ ∣ [] ⊢ ν[ A ] M′ ⦂ B
preserve-ξ-ν (⊢ν M⊢) M′⊢ = ⊢ν M′⊢

------------------------------------------------------------------------
-- Preservation cases: straightforward region floats
------------------------------------------------------------------------

preserve-float-·₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {A B C : Ty Δ} {M : Term (suc Θ) Δ} {N : Term Θ Δ}
  → Ψ ∣ [] ⊢ (ν[ A ] M) · N ⦂ C
  → Ψ ∣ [] ⊢ ν[ A ] (M · shiftᶿ N) ⦂ C
preserve-float-·₁ (⊢· (⊢ν M⊢) N⊢) =
  ⊢ν (⊢· M⊢ (⊢shiftᶿ N⊢))

preserve-float-·₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {A B C : Ty Δ} {V : Term Θ Δ} {M : Term (suc Θ) Δ}
  → Ψ ∣ [] ⊢ V · (ν[ A ] M) ⦂ C
  → Ψ ∣ [] ⊢ ν[ A ] (shiftᶿ V · M) ⦂ C
preserve-float-·₂ (⊢· V⊢ (⊢ν M⊢)) =
  ⊢ν (⊢· (⊢shiftᶿ V⊢) M⊢)

preserve-float-• : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {A C : Ty Δ} {B : Ty (suc Δ)} {M : Term (suc Θ) Δ}
  → Ψ ∣ [] ⊢ (ν[ A ] M) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
  → Ψ ∣ [] ⊢ ν[ A ] (M ⦂∀ B [ C ]) ⦂ B [ C ]ᵗ
preserve-float-• (⊢⦂∀ (⊢ν M⊢)) = ⊢ν (⊢⦂∀ M⊢)

preserve-float-⟨⟩ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {A B C : Ty Δ} {M : Term (suc Θ) Δ} {μ : Env∼ Δ}
    {c : μ ⊢ B ∼ C}
  → Ψ ∣ [] ⊢ (ν[ A ] M) ⟨ c ⟩ ⦂ C
  → Ψ ∣ [] ⊢ ν[ A ] (M ⟨ c ⟩) ⦂ C
preserve-float-⟨⟩ (⊢⟨⟩ (⊢ν M⊢) c) = ⊢ν (⊢⟨⟩ M⊢ c)

preserve-float-⊕₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {A : Ty Δ} {M : Term (suc Θ) Δ} {N : Term Θ Δ} {op}
  → Ψ ∣ [] ⊢ (ν[ A ] M) ⊕[ op ] N ⦂ primResultTy op
  → Ψ ∣ [] ⊢ ν[ A ] (M ⊕[ op ] shiftᶿ N) ⦂ primResultTy op
preserve-float-⊕₁ (⊢⊕ op (⊢ν M⊢) N⊢) =
  ⊢ν (⊢⊕ op M⊢ (⊢shiftᶿ N⊢))

preserve-float-⊕₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {A : Ty Δ} {V : Term Θ Δ} {M : Term (suc Θ) Δ} {op}
  → Ψ ∣ [] ⊢ V ⊕[ op ] (ν[ A ] M) ⦂ primResultTy op
  → Ψ ∣ [] ⊢ ν[ A ] (shiftᶿ V ⊕[ op ] M) ⦂ primResultTy op
preserve-float-⊕₂ (⊢⊕ op V⊢ (⊢ν M⊢)) =
  ⊢ν (⊢⊕ op (⊢shiftᶿ V⊢) M⊢)

------------------------------------------------------------------------
-- Closed one-step preservation assembler
------------------------------------------------------------------------

preserve : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {M M′ : Term Θ Δ} {A}
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
preserve typing (β-conceal-⇒ Vᵥ Wᵥ) = {!!}
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
preserve typing@(⊢⦂∀ (⊢conceal slot∈ β∈ c⊢ V⊢))
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
preserve (⊢conceal slot∈ α∈ c⊢ M⊢) (ξ-conceal step) =
  preserve-ξ-conceal slot∈ α∈ c⊢ (preserve M⊢ step)
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
-- Resolved `β-reveal-∀` body-type regression
------------------------------------------------------------------------

-- The old rule's implicit `C` occurred only in its contractum.  The checked
-- refutation chose `ℕ` on the redex side and `𝔹` in the contractum.  The rule
-- now computes the source from the reveal shape and target, yielding `ℕ`.

forall-bad-Ψ : TyEnv (suc zero) zero
forall-bad-Ψ = ∅ ,:= ‵ `ℕ

forall-bad-V : Term (suc zero) (suc zero)
forall-bad-V = Λ ($ (κℕ 0))

forall-bad-V-⊢ : forall-bad-Ψ ,typ[ zero ≔ zero ] ∣ []
  ⊢ forall-bad-V ⦂ `∀ (‵ `ℕ)
forall-bad-V-⊢ = ⊢Λ (⊢$ (κℕ 0))

forall-bad-V-value : Value forall-bad-V
forall-bad-V-value = Λ ($ (κℕ 0))

forall-bad-B : Ty 1
forall-bad-B = ‵ `ℕ

forall-bad-C : Ty 2
forall-bad-C = ‵ `𝔹

forall-computed-C : Ty 2
forall-computed-C = ‵ `ℕ

forall-source-computes-ℕ :
  src↑ (suc zero) id↑
    (renameᵗ (extᵗ (punchIn zero)) forall-bad-B)
    ≡ forall-computed-C
forall-source-computes-ℕ = refl

forall-bad-delimiter-type : Ty 2
forall-bad-delimiter-type =
  wkᵗ (Fin.zero {n = 1}) (`∀ forall-bad-C)

forall-bad-redex : Term (suc zero) zero
forall-bad-redex =
  (forall-bad-V ↑[ zero ≔ zero ] `∀↑ id↑)
    ⦂∀ forall-bad-B [ ‵ `ℕ ]

forall-bad-redex-⊢ : forall-bad-Ψ ∣ [] ⊢ forall-bad-redex ⦂ ‵ `ℕ
forall-bad-redex-⊢ =
  ⊢⦂∀ (⊢reveal Z (⊢↑-∀ (⊢id↑ (‵ `ℕ))) forall-bad-V-⊢)

forall-bad-contractum : Term (suc zero) zero
forall-bad-contractum =
  ν[ ‵ `ℕ ]
    ((((shiftᶿ forall-bad-V
          ↓[ zero ≔ zero ] δ↓ forall-bad-delimiter-type)
        ⦂∀ swapTopᵗ (⇑ᵗ forall-bad-C) [ ＇ zero ])
      ↑[ suc zero ≔ suc zero ] id↑)
      ↑[ zero ≔ zero ] 〖 Fin.zero {n = 0} ↑ forall-bad-B 〗)

forall-bad-contractum-untypable :
  forall-bad-Ψ ∣ [] ⊢ forall-bad-contractum ⦂ ‵ `ℕ
  → ⊥
forall-bad-contractum-untypable
    (⊢ν (⊢reveal fresh∈ (⊢id↑ fresh-atom)
      (⊢reveal old∈ (⊢id↑ old-atom)
        ())))

forall-computed-contractum : Term (suc zero) zero
forall-computed-contractum =
  ν[ ‵ `ℕ ]
    ((((shiftᶿ forall-bad-V
          ↓[ zero ≔ zero ]
            δ↓ (wkᵗ zero (`∀ forall-computed-C)))
        ⦂∀ swapTopᵗ (⇑ᵗ forall-computed-C) [ ＇ zero ])
      ↑[ suc zero ≔ suc zero ] id↑)
      ↑[ zero ≔ zero ] 〖 Fin.zero {n = 0} ↑ forall-bad-B 〗)

forall-computed-step : forall-bad-Ψ ⊢ forall-bad-redex —→
  forall-computed-contractum
forall-computed-step = β-reveal-∀ (result-val forall-bad-V-value)

forall-bad-step-impossible :
  forall-bad-Ψ ⊢ forall-bad-redex —→ forall-bad-contractum
  → ⊥
forall-bad-step-impossible ()

------------------------------------------------------------------------
-- Resolved `β-conceal-∀` slot-dependent instantiation regression
------------------------------------------------------------------------

-- This was the fifth preservation obstruction: the instantiation is the
-- concealed variable itself.  The rule now resolves that variable to the
-- deleted view's recorded representation, allocates the fresh region there,
-- and uses the generated exit conceal to re-establish the ambient type.

conceal-var-Ψ : TyEnv (suc zero) (suc zero)
conceal-var-Ψ = (∅ ,:= ‵ `ℕ) ,typ[ zero ≔ zero ]

conceal-var-V : Term (suc zero) zero
conceal-var-V = Λ ($ (κℕ 0))

conceal-var-V-value : Value conceal-var-V
conceal-var-V-value = Λ ($ (κℕ 0))

conceal-var-V-⊢ : ∅ ,:= ‵ `ℕ ∣ [] ⊢ conceal-var-V ⦂ `∀ (‵ `ℕ)
conceal-var-V-⊢ = ⊢Λ (⊢$ (κℕ 0))

conceal-var-B : Ty 2
conceal-var-B = ‵ `ℕ

conceal-var-redex : Term (suc zero) (suc zero)
conceal-var-redex =
  (conceal-var-V ↓[ zero ≔ zero ] `∀↓ id↓)
    ⦂∀ conceal-var-B [ ＇ zero ]

conceal-var-redex-⊢ :
  conceal-var-Ψ ∣ [] ⊢ conceal-var-redex ⦂ ‵ `ℕ
conceal-var-redex-⊢ =
  ⊢⦂∀ (⊢conceal here-typ Z (⊢↓-∀ (⊢id↓ (‵ `ℕ)))
    conceal-var-V-⊢)

conceal-var-contractum : Term (suc zero) (suc zero)
conceal-var-contractum =
  (ν[ ‵ `ℕ ]
    (((shiftᶿ conceal-var-V ↓[ zero ≔ zero ]
          δ↓ (wkᵗ (Fin.zero {n = 0}) (`∀ (‵ `ℕ))))
        ⦂∀ swapTopᵗ (⇑ᵗ (‵ `ℕ)) [ ＇ zero ])
      ↑[ zero ≔ zero ] 〖 Fin.zero {n = 0} ↑ (‵ `ℕ) 〗))
    ↓[ zero ≔ zero ] id↓

conceal-var-step : conceal-var-Ψ ⊢ conceal-var-redex —→
  conceal-var-contractum
conceal-var-step = β-conceal-∀ Z (result-val conceal-var-V-value)

conceal-var-contractum-⊢ :
  conceal-var-Ψ ∣ [] ⊢ conceal-var-contractum ⦂ ‵ `ℕ
conceal-var-contractum-⊢ =
  preserve-β-conceal-∀ Z conceal-var-redex-⊢

------------------------------------------------------------------------
-- Resolved-view regression for `β-conceal-⇒`
------------------------------------------------------------------------

conceal-arrow-base : TyEnv (suc zero) zero
conceal-arrow-base = ∅ ,:= ‵ `ℕ

conceal-arrow-Ψ : TyEnv (suc (suc zero)) (suc zero)
conceal-arrow-Ψ =
  (conceal-arrow-base ,typ[ zero ≔ zero ]) ,:= ＇ zero

conceal-arrow-P : Ty zero
conceal-arrow-P = `∀ (‵ `ℕ)

conceal-arrow-V : Term (suc (suc zero)) zero
conceal-arrow-V = ƛ conceal-arrow-P ˙ ($ (κℕ 0))

conceal-arrow-V-value : Value conceal-arrow-V
conceal-arrow-V-value = ƛ conceal-arrow-P ˙ ($ (κℕ 0))

conceal-arrow-V-⊢ : conceal-arrow-base ,:= ‵ `ℕ ∣ [] ⊢
  conceal-arrow-V ⦂ conceal-arrow-P ⇒ ‵ `ℕ
conceal-arrow-V-⊢ = ⊢ƛ (⊢$ (κℕ 0))

conceal-arrow-W : Term (suc (suc zero)) (suc zero)
conceal-arrow-W =
  ( Λ ($ (κℕ 1)))
    ↑[ zero ≔ zero ] `∀↑ id↑

conceal-arrow-W-value : Value conceal-arrow-W
conceal-arrow-W-value =
  result-val (Λ ($ (κℕ 1))) ↑[ zero ≔ zero ] all

conceal-arrow-W-⊢ : conceal-arrow-Ψ ∣ [] ⊢
  conceal-arrow-W ⦂ `∀ (‵ `ℕ)
conceal-arrow-W-⊢ =
  ⊢reveal Z (⊢↑-∀ (⊢id↑ (‵ `ℕ))) (⊢Λ (⊢$ (κℕ 1)))

conceal-arrow-redex : Term (suc (suc zero)) (suc zero)
conceal-arrow-redex =
  (conceal-arrow-V ↓[ zero ≔ suc zero ] (`∀↑ id↑ ↦↓ id↓))
    · conceal-arrow-W

conceal-arrow-redex-⊢ : conceal-arrow-Ψ ∣ [] ⊢
  conceal-arrow-redex ⦂ ‵ `ℕ
conceal-arrow-redex-⊢ =
  ⊢·
    (⊢conceal (skip-visible-typ here-typ) (S Z)
      (⊢↓-⇒ (⊢↑-∀ (⊢id↑ (‵ `ℕ))) (⊢id↓ (‵ `ℕ)))
      conceal-arrow-V-⊢)
    conceal-arrow-W-⊢

conceal-arrow-contractum : Term (suc (suc zero)) (suc zero)
conceal-arrow-contractum =
  (conceal-arrow-V ·
    (conceal-arrow-W ↑[ zero ≔ suc zero ] `∀↑ id↑))
    ↓[ zero ≔ suc zero ] id↓

conceal-arrow-step : conceal-arrow-Ψ ⊢ conceal-arrow-redex —→
  conceal-arrow-contractum
conceal-arrow-step =
  β-conceal-⇒ (result-val conceal-arrow-V-value)
    conceal-arrow-W-value

conceal-arrow-contractum-⊢ :
  conceal-arrow-Ψ ∣ [] ⊢ conceal-arrow-contractum ⦂ ‵ `ℕ
conceal-arrow-contractum-⊢ =
  ⊢conceal (skip-visible-typ here-typ) (S Z) (⊢id↓ (‵ `ℕ))
    (⊢· conceal-arrow-V-⊢
      (⊢reveal (S Z) (⊢↑-∀ (⊢id↑ (‵ `ℕ)))
        (⊢reveal (skip-typ Z) (⊢↑-∀ (⊢id↑ (‵ `ℕ)))
          (⊢Λ (⊢$ (κℕ 1))))))

------------------------------------------------------------------------
-- Slot-dependent fresh-anchor obstruction for `float-reveal`
------------------------------------------------------------------------

-- Direction-audit record, stated without relying on the definitions below.
-- Let
--
--   Ψ₀ = ∅ ,:= ℕ
--   M  = (λ x : ＇X. 0) ↑[ X ≔ α ] (seal ↦↑ id↑).
--
-- At the concrete de Bruijn indices used below, the inner configuration is
--
--   ((Ψ₀ ,typ[ zero ≔ zero ]) ,:= ＇zero) ∣ [] ⊢
--     M ⦂ ＇zero ⇒ ℕ.
--
-- Consequently the closed redex and its operational step are exactly
--
--   Ψ₀ ∣ [] ⊢
--     (ν[ ＇zero ] M) ↑[ zero ≔ zero ] (seal ↦↑ id↑)
--       ⦂ ℕ ⇒ ℕ
--
--   Ψ₀ ⊢
--     (ν[ ＇zero ] M) ↑[ zero ≔ zero ] (seal ↦↑ id↑)
--       —→ ν[ ℕ ] (M ↑[ zero ≔ suc zero ] (seal ↦↑ id↑)).
--
-- Typing that contractum would make the outer and inner `seal` conversions
-- share one source.  The outer conversion forces it to `ℕ`, while the
-- retained inner conversion forces it to `＇(suc zero)` in `Ty 2`.  Thus the
-- precise failing obligation is `＇(suc zero) ≡ ℕ`, discharged below by
-- the empty pattern.  Commits 3ee5de8c and a18f75f4 recorded the checked
-- refutation of the resolving float.  Chunk U11 resolves it semantically by
-- deleting both delimiter-crossing ν floats: the displayed redex now has no
-- `float-reveal` step, so its region remains at the delimiter depth where it
-- was born.

------------------------------------------------------------------------
-- Historical strict-id regression
------------------------------------------------------------------------

bad-Ψ : TyEnv (suc (suc zero)) (suc (suc zero))
bad-Ψ =
  ∅ ,:= ‵ `ℕ ,:= ‵ `ℕ
    ,typ[ zero ≔ zero ] ,typ[ zero ≔ zero ]

bad-body-Ψ : TyEnv (suc (suc zero)) (suc (suc zero))
bad-body-Ψ =
  ∅ ,:= ‵ `ℕ ,:= ‵ `ℕ
    ,typ[ zero ≔ zero ] ,typ[ suc zero ≔ suc zero ]

bad-V : Term (suc (suc zero)) (suc (suc zero))
bad-V = ($ (κℕ 7)) ↓[ zero ≔ zero ] seal

bad-V-⊢ : bad-body-Ψ ∣ [] ⊢ bad-V ⦂ ＇ zero
bad-V-⊢ =
  ⊢conceal (skip-cross-typ here-typ) (skip-typ Z)
    ⊢seal (⊢$ (κℕ 7))

bad-inner : Term (suc (suc zero)) (suc (suc (suc zero)))
bad-inner = bad-V ↓[ zero ≔ zero ] id↓

bad-inner-⊢ :
  bad-Ψ ,typ[ suc (suc zero) ≔ suc zero ] ∣ []
    ⊢ bad-inner ⦂ ＇ suc zero
bad-inner-⊢ =
  ⊢conceal (skip-cross-typ here-typ) (skip-typ (skip-typ Z))
    (⊢id↓ (＇ suc zero)) bad-V-⊢

bad-redex : Term (suc (suc zero)) (suc (suc zero))
bad-redex = bad-inner ↑[ suc (suc zero) ≔ suc zero ] id↑

bad-redex-⊢ : bad-Ψ ∣ [] ⊢ bad-redex ⦂ ＇ suc zero
bad-redex-⊢ =
  ⊢reveal (skip-typ (skip-typ (S Z)))
    (⊢id↑ (＇ suc zero)) bad-inner-⊢

bad-V-canonical : CanonicalInterior bad-V
bad-V-canonical = sealed (result-val ($ (κℕ 7))) zero zero

bad-inner-value : Value bad-inner
bad-inner-value =
  result-val (canonical-value bad-V-canonical)
    ↓[ zero ≔ zero ] delimiter bad-V-canonical

bad-node-pair-mismatch :
  ¬ ((Fin.suc {n = 2} (Fin.suc {n = 1} (Fin.zero {n = 0}))
      ≡ Fin.zero {n = 2})
    × (Fin.suc {n = 1} (Fin.zero {n = 0}) ≡ Fin.zero {n = 1}))
bad-node-pair-mismatch (() , anchor-eq)

-- This was the preservation-refuting redex in commit c5ee0351.  With strict
-- `id-cancel`, the unequal (slot, anchor) pairs make it an adapter value.
bad-redex-value : Value bad-redex
bad-redex-value =
  result-val bad-inner-value ↑[ suc (suc zero) ≔ suc zero ]
    adapter (result-val (canonical-value bad-V-canonical))
      bad-node-pair-mismatch

constant-no-step : ∀ {Θ Δ} {Φ : TyEnv Θ Δ} {κ M′}
  → Φ ⊢ $ κ —→ M′
  → ⊥
constant-no-step ()

bad-V-no-step : ∀ {Φ : TyEnv 2 2} {M′}
  → Φ ⊢ bad-V —→ M′
  → ⊥
bad-V-no-step (ξ-conceal step) = constant-no-step step

bad-inner-no-step : ∀ {Φ : TyEnv 2 3} {M′}
  → Φ ⊢ bad-inner —→ M′
  → ⊥
bad-inner-no-step (ξ-conceal step) = bad-V-no-step step

bad-redex-no-step : ∀ {M′}
  → bad-Ψ ⊢ bad-redex —→ M′
  → ⊥
bad-redex-no-step (ξ-reveal step) = bad-inner-no-step step

------------------------------------------------------------------------
-- A region stranded between seal and unseal is an adapter value
------------------------------------------------------------------------

-- Delimiter-crossing floats can no longer produce this configuration, but
-- the unreachable typed fragment still classifies it as a value.  The region
-- and its sealed result stay intact at their birth depth.
stranded-Ψ : TyEnv 1 0
stranded-Ψ = ∅ ,:= ‵ `ℕ

stranded-seal : Term 2 1
stranded-seal = ($ (κℕ 7)) ↓[ zero ≔ suc zero ] seal

stranded-seal-value : Value stranded-seal
stranded-seal-value =
  result-val ($ (κℕ 7)) ↓[ zero ≔ suc zero ] sealᵥ

stranded-seal-⊢ :
  ((stranded-Ψ ,typ[ zero ≔ zero ]) ,:= ‵ `ℕ) ∣ [] ⊢
    stranded-seal ⦂ ＇ zero
stranded-seal-⊢ =
  ⊢conceal (skip-visible-typ here-typ) (S Z) ⊢seal (⊢$ (κℕ 7))

stranded-region : Term 1 1
stranded-region = ν[ ‵ `ℕ ] stranded-seal

stranded-region-result : Result stranded-region
stranded-region-result = result-ν (result-val stranded-seal-value)

stranded-region-⊢ :
  stranded-Ψ ,typ[ zero ≔ zero ] ∣ [] ⊢ stranded-region ⦂ ＇ zero
stranded-region-⊢ = ⊢ν stranded-seal-⊢

stranded-adapter : Term 1 0
stranded-adapter = stranded-region ↑[ zero ≔ zero ] unseal

stranded-adapter-value : Value stranded-adapter
stranded-adapter-value =
  stranded-region-result ↑[ zero ≔ zero ]
    adapter-region (result-val stranded-seal-value)

stranded-adapter-⊢ :
  stranded-Ψ ∣ [] ⊢ stranded-adapter ⦂ ‵ `ℕ
stranded-adapter-⊢ = ⊢reveal Z ⊢unseal stranded-region-⊢

stranded-seal-no-step : ∀ {M′}
  → ((stranded-Ψ ,typ[ zero ≔ zero ]) ,:= ‵ `ℕ) ⊢
      stranded-seal —→ M′
  → ⊥
stranded-seal-no-step (ξ-conceal step) = constant-no-step step

stranded-region-no-step : ∀ {M′}
  → stranded-Ψ ,typ[ zero ≔ zero ] ⊢ stranded-region —→ M′
  → ⊥
stranded-region-no-step (ξ-ν step) = stranded-seal-no-step step

stranded-adapter-no-step : ∀ {M′}
  → stranded-Ψ ⊢ stranded-adapter —→ M′
  → ⊥
stranded-adapter-no-step (ξ-reveal step) = stranded-region-no-step step

------------------------------------------------------------------------
-- Recorded anchors resolve the old loose conceal/reveal refutation
------------------------------------------------------------------------

loose-Ψ : TyEnv 2 0
loose-Ψ = ∅ ,:= ‵ `ℕ ,:= ‵ `𝔹

loose-V : Term 2 0
loose-V = $ (κℕ 7)

loose-V-⊢ : loose-Ψ ∣ [] ⊢ loose-V ⦂ ‵ `ℕ
loose-V-⊢ = ⊢$ (κℕ 7)

loose-inner : Term 2 1
loose-inner = loose-V ↓[ zero ≔ suc zero ] seal

loose-anchor-mismatch :
  loose-Ψ ,typ[ zero ≔ zero ] ∋typ zero ≔ suc zero
  → ⊥
loose-anchor-mismatch ()

loose-redex : Term 2 0
loose-redex = loose-inner ↑[ zero ≔ zero ] unseal

loose-step : loose-Ψ ⊢ loose-redex —→ loose-V
loose-step = conceal-reveal (result-val ($ (κℕ 7)))

loose-redex-untypable :
  loose-Ψ ∣ [] ⊢ loose-redex ⦂ ‵ `𝔹
  → ⊥
loose-redex-untypable
    (⊢reveal α∈ c⊢ (⊢conceal slot∈ β∈ d⊢ V⊢)) =
  loose-anchor-mismatch slot∈

------------------------------------------------------------------------
-- Arbitrary-context `β-reveal-⇒` obstruction
------------------------------------------------------------------------

open-R : Ty zero
open-R = ‵ `ℕ ⇒ ‵ `ℕ

open-Ψ : TyEnv (suc zero) zero
open-Ψ = ∅ ,:= open-R

open-Γ : TermCtx zero
open-Γ = ‵ `ℕ ∷ []

open-V : Term (suc zero) (suc zero)
open-V = ƛ ＇ zero ˙ $ (κℕ 0)

open-V-⊢ :
  open-Ψ ,typ[ zero ≔ zero ] ∣ [] ⊢ open-V ⦂ ＇ zero ⇒ ‵ `ℕ
open-V-⊢ = ⊢ƛ (⊢$ (κℕ 0))

open-V-value : Value open-V
open-V-value = ƛ ＇ zero ˙ $ (κℕ 0)

open-W : Term (suc zero) zero
open-W = ƛ ‵ `ℕ ˙ ` suc zero

open-W-⊢ : open-Ψ ∣ open-Γ ⊢ open-W ⦂ open-R
open-W-⊢ = ⊢ƛ (⊢` (S Z))

open-W-value : Value open-W
open-W-value = ƛ ‵ `ℕ ˙ ` suc zero

open-function : Term (suc zero) zero
open-function = open-V ↑[ zero ≔ zero ] (seal ↦↑ id↑)

open-function-⊢ :
  open-Ψ ∣ open-Γ ⊢ open-function ⦂ open-R ⇒ ‵ `ℕ
open-function-⊢ =
  ⊢reveal Z (⊢↑-⇒ ⊢seal (⊢id↑ (‵ `ℕ))) open-V-⊢

open-redex : Term (suc zero) zero
open-redex = open-function · open-W

open-redex-⊢ : open-Ψ ∣ open-Γ ⊢ open-redex ⦂ ‵ `ℕ
open-redex-⊢ = ⊢· open-function-⊢ open-W-⊢

open-contractum : Term (suc zero) zero
open-contractum =
  (open-V · (open-W ↓[ zero ≔ zero ] seal))
    ↑[ zero ≔ zero ] id↑

open-step : open-Ψ ⊢ open-redex —→ open-contractum
open-step = β-reveal-⇒ (result-val open-V-value) open-W-value

open-W-closed-impossible : ∀ {Φ : TyEnv (suc zero) zero} {A}
  → Φ ∣ [] ⊢ open-W ⦂ A
  → ⊥
open-W-closed-impossible (⊢ƛ (⊢` (S ())))

open-contractum-untypable :
  open-Ψ ∣ open-Γ ⊢ open-contractum ⦂ ‵ `ℕ
  → ⊥
open-contractum-untypable
    (⊢reveal α∈ c⊢
      (⊢· V⊢ (⊢conceal slot∈ β∈ d⊢ W⊢))) =
  open-W-closed-impossible W⊢

preserve-impossible :
  (∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ} {M M′ A}
    → Ψ ∣ Γ ⊢ M ⦂ A
    → Ψ ⊢ M —→ M′
    → Ψ ∣ Γ ⊢ M′ ⦂ A)
  → ⊥
preserve-impossible preserve =
  open-contractum-untypable (preserve open-redex-⊢ open-step)
