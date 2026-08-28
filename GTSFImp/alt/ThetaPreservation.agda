module alt.ThetaPreservation where

-- File Charter:
--   * Develops one-step preservation for closed configurations of the
--     Θ-indexed alternative calculus.  Substantial reduction cases have
--     named lemmas; straightforward cases are proved directly in `preserve`.
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
--   * The former type-variable-dependent `β-conceal-∀` obstruction is retained as
--     a resolved regression.  The contractum resolves its instantiation and
--     computed source in the ended view, then seals the result on exit.
--   * The former `β-conceal-⇒` counterexample's contractum remains a checked
--     positive instance.  Balanced end/begin extension now supplies the
--     general re-entry transport.
--   * The guarded `float-reveal` moves only entries that strengthen across
--     the crossing.  Its telescope exchange is justified by the weakening
--     round trip, without representation resolution.
--   * The dual `float-conceal` weakens its entry into the larger scope; an
--     exact end/ν telescope exchange carries the interior typing.
--   * Injection out of delimiters and restricted projection into reveal
--     preserve typing by ground weakening/strengthening and the checked
--     `expand↑`/`expand↓` typing lemmas.
--   * β-Λ preservation depends only on its body typing, so the same lexical
--     allocation transport covers both value and ν-prefixed Result bodies.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
  renaming (map to mapMaybe)
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
-- Substantial preservation cases
------------------------------------------------------------------------

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

preserve-float-reveal : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {A : Ty (suc Δ)} {A₀ B : Ty Δ} {M : Term (suc Θ) (suc Δ)}
    {Y : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
  → strengthenᵗ? Y A ≡ just A₀
  → Ψ ∣ [] ⊢ (ν[ A ] M) ↑[ Y ≔ α ] c ⦂ B
  → Ψ ∣ [] ⊢ ν[ A₀ ] (M ↑[ Y ≔ suc α ] c) ⦂ B
preserve-float-reveal {Θ = Θ} {Ψ = Ψ} {A₀ = A₀} {M = M}
    {Y = Y} {α = α} strengthens
    (⊢reveal {fresh = fresh} α-eq c⊢ (⊢ν M⊢)) =
  ⊢ν (⊢reveal (rep?-ν {Θ = Θ} {Ψ = Ψ} {B = A₀} {a = α} α-eq) c⊢
    (⊢unbracket-target unbracket-begin-ν source-M⊢))
  where
  source-M⊢ = subst≡
    (λ entry → ((Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) ,:= entry)
      ∣ [] ⊢ M ⦂ _)
    (strengthenᵗ?-sound strengthens) M⊢

preserve-float-conceal : ∀ {Θ Δ} {σ}
    {Ψ : TyEnv Θ (suc Δ) σ} {A : Ty Δ}
    {M : Term (suc Θ) Δ} {Y : TyVar (suc Δ)} {α : TyVar Θ}
    {c : Conceal} {B : Ty (suc Δ)}
  → Ψ ∣ [] ⊢ (ν[ A ] M) ↓[ Y ≔ α ] c ⦂ B
  → Ψ ∣ [] ⊢ ν[ wkᵗ Y A ] (M ↓[ Y ≔ suc α ] c) ⦂ B
preserve-float-conceal {Θ = Θ} {σ = σ} {Ψ = Ψ} {A = A}
    {Y = Y} {α = α}
    (⊢conceal tyVar-eq α-eq c⊢ (⊢ν M⊢)) =
  ⊢ν (⊢conceal shifted-tyVar shifted-rep c⊢
    (⊢unbracket-target exchange M⊢))
  where
  exchange = unbracket-end-ν tyVar-eq
  shifted-tyVar = trans (lookup-mapᵛ (mapMaybe Fin.suc) σ Y)
    (cong (mapMaybe Fin.suc) tyVar-eq)
  shifted-rep = trans (sym (rep?-unbracket exchange (suc α)))
    (rep?-ν {Θ = Θ} {Ψ = Ψ ,end[ Y ]} {B = A} {a = α} α-eq)

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

preserve-β-Λ : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ (suc Δ)} {B : Ty (suc Δ)} {C : Ty Δ}
  → Ψ ∣ [] ⊢ (Λ V) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
  → Ψ ∣ [] ⊢
      ν[ C ] (shiftᶿ V ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)
      ⦂ B [ C ]ᵗ
preserve-β-Λ {B = B} {C = C} (⊢⦂∀ (⊢Λ body V⊢)) =
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

preserve-β-reveal-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ (suc (suc Δ))} {B : Ty (suc Δ)}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
  → Result V
  → Ψ ∣ [] ⊢ (Λ V) ↑[ X ≔ α ] `∀↑ c ⦂ `∀ B
  → Ψ ∣ [] ⊢ Λ (V ↑[ suc X ≔ α ] c) ⦂ `∀ B
preserve-β-reveal-∀ {Θ = Θ} {Ψ = Ψ} {X = X} {α = α} Vʳ
    (⊢reveal {B = `∀ B} {C = C} α-eq (⊢↑-∀ c⊢)
      (⊢Λ body V⊢)) =
  ⊢Λ (body-reveal Vʳ)
    (⊢reveal (rep?-typ {Θ = Θ} {Ψ = Ψ} {α = α} {A = C} α-eq)
      conversion⊢
      (⊢begin-typ-exchange V⊢))
  where
  representation⊢ = subst≡
    (λ R → ⊢↑[ suc X ⦂ R ] _ ⦂ _ ↝ _)
    (resolve-wk-exchange X C) c⊢
  conversion⊢ = subst≡
    (λ T → ⊢↑[ suc X ⦂ wkᵗ (suc X) (⇑ᵗ C) ] _ ⦂ _ ↝ T)
    (wk-under-∀ X B) representation⊢

preserve-β-reveal-∀-any : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ (suc (suc Δ))} {A : Ty Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
  → Result V
  → Ψ ∣ [] ⊢ (Λ V) ↑[ X ≔ α ] `∀↑ c ⦂ A
  → Ψ ∣ [] ⊢ Λ (V ↑[ suc X ≔ α ] c) ⦂ A
preserve-β-reveal-∀-any {A = ＇ Y} Vʳ (⊢reveal α-eq () V⊢)
preserve-β-reveal-∀-any {A = ‵ ι} Vʳ (⊢reveal α-eq () V⊢)
preserve-β-reveal-∀-any {A = ★} Vʳ (⊢reveal α-eq () V⊢)
preserve-β-reveal-∀-any {A = A ⇒ B} Vʳ (⊢reveal α-eq () V⊢)
preserve-β-reveal-∀-any {A = `∀ B} Vʳ typing =
  preserve-β-reveal-∀ Vʳ typing

preserve-β-conceal-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {V : Term Θ (suc Δ)} {B : Ty (suc (suc Δ))}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
  → Result V
  → Ψ ∣ [] ⊢ (Λ V) ↓[ X ≔ α ] `∀↓ c ⦂ `∀ B
  → Ψ ∣ [] ⊢ Λ (V ↓[ suc X ≔ α ] c) ⦂ `∀ B
preserve-β-conceal-∀ {Θ = Θ} {Ψ = Ψ} {X = X} {α = α} Vʳ
    (⊢conceal {A = `∀ A} {C = C} tyVar-eq α-eq
      (⊢↓-∀ c⊢) (⊢Λ body V⊢)) =
  ⊢Λ (body-conceal Vʳ)
    (⊢conceal tyVar-eq target-rep conversion⊢
      (⊢end-typ-exchange V⊢))
  where
  target-rep = trans
    (sym (rep?-unbracket {Θ = Θ}
      {left = Ψ ,end[ X ] ,typ}
      {right = Ψ ,typ ,end[ suc X ]}
      unbracket-end-typ α))
    (rep?-typ {Θ = Θ} {Ψ = Ψ ,end[ X ]} {α = α} {A = C} α-eq)
  representation⊢ = subst≡
    (λ R → ⊢↓[ suc X ⦂ R ] _ ⦂ _ ↝ _)
    (resolve-wk-exchange X C) c⊢
  conversion⊢ = subst≡
    (λ S → ⊢↓[ suc X ⦂ wkᵗ (suc X) (⇑ᵗ C) ] _ ⦂ S ↝ _)
    (wk-under-∀ X A) representation⊢

preserve-β-conceal-∀-any : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {V : Term Θ (suc Δ)} {B : Ty (suc Δ)}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
  → Result V
  → Ψ ∣ [] ⊢ (Λ V) ↓[ X ≔ α ] `∀↓ c ⦂ B
  → Ψ ∣ [] ⊢ Λ (V ↓[ suc X ≔ α ] c) ⦂ B
preserve-β-conceal-∀-any {B = ＇ Y} Vʳ
    (⊢conceal tyVar-eq α-eq () V⊢)
preserve-β-conceal-∀-any {B = ‵ ι} Vʳ
    (⊢conceal tyVar-eq α-eq () V⊢)
preserve-β-conceal-∀-any {B = ★} Vʳ
    (⊢conceal tyVar-eq α-eq () V⊢)
preserve-β-conceal-∀-any {B = A ⇒ B} Vʳ
    (⊢conceal tyVar-eq α-eq () V⊢)
preserve-β-conceal-∀-any {B = `∀ B} Vʳ typing =
  preserve-β-conceal-∀ Vʳ typing

preserve-inject-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {Γ : TermCtx Δ} {V : Term Θ (suc Δ)}
    {Y : TyVar (suc Δ)} {γ : TyVar Θ}
    {μ : Env∼ (suc Δ)} {H : Ty (suc Δ)} {H₀ B C : Ty Δ}
    {T : Ty (suc Δ)} {fresh : γ ∉ᵛ σ}
  → (Hᵍ : Ground H)
  → (H∼★ : μ ⊢ H ∼★)
  → rep? Ψ γ ≡ just C
  → Ψ ,begin[ Y ≔ γ ]⟨ fresh ⟩ ∣ [] ⊢ V ⦂ H
  → (strengthens : strengthenᵗ? Y H ≡ just H₀)
  → ⊢↑[ Y ⦂ wkᵗ Y C ] id↑ ⦂ ★ ↝ T
  → T ≡ wkᵗ Y B
  → Ψ ∣ Γ ⊢ (V ↑[ Y ≔ γ ] expand↑ H id↑)
      ⟨ strengthenInjection Hᵍ H∼★ strengthens ⟩ ⦂ B
preserve-inject-reveal {B = ＇ X} Hᵍ H∼★ α-eq V⊢ strengthens
    (⊢id↑ ★) ()
preserve-inject-reveal {B = ‵ ι} Hᵍ H∼★ α-eq V⊢ strengthens
    (⊢id↑ ★) ()
preserve-inject-reveal {B = ★} Hᵍ H∼★ α-eq V⊢ strengthens
    (⊢id↑ ★) refl =
  ⊢⟨⟩
    (⊢reveal α-eq (expand↑-strengthen-typed strengthens) V⊢)
    (strengthenInjection Hᵍ H∼★ strengthens)
preserve-inject-reveal {B = A ⇒ B} Hᵍ H∼★ α-eq V⊢ strengthens
    (⊢id↑ ★) ()
preserve-inject-reveal {B = `∀ B} Hᵍ H∼★ α-eq V⊢ strengthens
    (⊢id↑ ★) ()

------------------------------------------------------------------------
-- Closed one-step preservation assembler
------------------------------------------------------------------------

preserve : ∀ {Θ Δ} {σ} {Ψ : TyEnv Θ Δ σ} {M M′ : Term Θ Δ} {A}
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ⊢ M —→ M′
  → Ψ ∣ [] ⊢ M′ ⦂ A
preserve (⊢⊕ addℕ (⊢$ _) (⊢$ _)) (δ-⊕ δ-add) = ⊢$ _
preserve (⊢⊕ and𝔹 (⊢$ _) (⊢$ _)) (δ-⊕ δ-and) = ⊢$ _
preserve (⊢· (⊢ƛ N⊢) V⊢) (β Vᵥ) = ⊢[] N⊢ V⊢
preserve (⊢⟨⟩ V⊢ (id a)) (β-id Vᵥ) = V⊢
preserve (⊢· (⊢⟨⟩ V⊢ (c ↦ d)) W⊢) (β-⇒ Vᵥ Wᵥ) =
  ⊢⟨⟩ (⊢· V⊢ (⊢⟨⟩ W⊢ c)) d
preserve (⊢⦂∀ (⊢⟨⟩ V⊢ (∀ᶜ c))) (β-∀ Vᵥ refl) =
  ⊢⟨⟩ (⊢⦂∀ V⊢) (c [ _ ]ᶜ)
preserve (⊢⟨⟩ V⊢ (_! ⦃ Gᵍ = Gᵍ ⦄ c)) (ground Vᵥ neq) =
  ⊢⟨⟩ (⊢⟨⟩ V⊢ c) ((idᵍ Gᵍ) !)
preserve (⊢⟨⟩ V⊢ (？_ ⦃ Gᵍ = Gᵍ ⦄ c)) (expand Vᵥ neq) =
  ⊢⟨⟩ (⊢⟨⟩ V⊢ (？ (idᵍ Gᵍ))) c
preserve
    (⊢conceal X-live α-eq (⊢id↓ ★)
      (⊢⟨⟩ V⊢ (_! ⦃ Gᵍ = Hᵍ ⦄
        ⦃ G∼★ = H∼★ ⦄ .(idᵍ Hᵍ))))
    (inject-conceal {X = X} Vᵥ) =
  ⊢⟨⟩
    (⊢conceal X-live α-eq (expand↓-typed (wkᵗ X _)) V⊢)
    (weakenInjection X Hᵍ H∼★)
preserve
    (⊢reveal α-eq c⊢
      (⊢⟨⟩ V⊢ (_! ⦃ Gᵍ = Hᵍ ⦄
        ⦃ G∼★ = H∼★ ⦄ .(idᵍ Hᵍ))))
    (inject-reveal {Y = Y} strengthens Vᵥ) =
  preserve-inject-reveal Hᵍ H∼★ α-eq V⊢ strengthens c⊢ refl
preserve
    (⊢⟨⟩ (⊢reveal α-eq (⊢id↑ ★) V⊢)
      (？_ ⦃ Gᵍ = Gᵍ ⦄ .(idᵍ Gᵍ)))
    (★-project-reveal {X = X} {G = G} Vʳ gate) =
  ⊢reveal α-eq (expand↑-typed (wkᵗ X G))
    (⊢⟨⟩ V⊢ (weakenConsistency X (？ (idᵍ Gᵍ))))
preserve (⊢⟨⟩ (⊢⟨⟩ V⊢ c) d) (tag-untag Vᵥ) = V⊢
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
preserve typing@(⊢⦂∀ (⊢Λ body V⊢)) (β-Λ Vʳ) =
  preserve-β-Λ typing
preserve typing@(⊢⦂∀ (⊢⟨⟩ V⊢ c)) (β-gen Vᵥ A≠★ safe) =
  preserve-β-gen typing
preserve (⊢⟨⟩ V⊢ ((inst c) B≠★)) (β-inst Vᵥ B≠★) =
  ⊢⟨⟩ (⊢⦂∀ V⊢) (c [ ★/0 ]ᶜ)
preserve typing (β-reveal-∀ Vʳ) =
  preserve-β-reveal-∀-any Vʳ typing
preserve typing (β-conceal-∀ Vʳ) =
  preserve-β-conceal-∀-any Vʳ typing
preserve (⊢Λ body M⊢) (ξ-Λ step) =
  ⊢Λ (ΛBody-stable body step) (preserve M⊢ step)
preserve (⊢· L⊢ M⊢) (ξ-·₁ step) =
  ⊢· (preserve L⊢ step) M⊢
preserve (⊢· V⊢ M⊢) (ξ-·₂ Vᵥ step) =
  ⊢· V⊢ (preserve M⊢ step)
preserve (⊢⦂∀ M⊢) (ξ-• step) = ⊢⦂∀ (preserve M⊢ step)
preserve (⊢⟨⟩ M⊢ c) (ξ-⟨⟩ step) = ⊢⟨⟩ (preserve M⊢ step) c
preserve typing (float-reveal strengthens result) =
  preserve-float-reveal strengthens typing
preserve typing (float-conceal result) = preserve-float-conceal typing
preserve (⊢reveal α∈ c⊢ M⊢) (ξ-reveal step) =
  ⊢reveal α∈ c⊢ (preserve M⊢ step)
preserve (⊢conceal tyVar∈ α∈ c⊢ M⊢) (ξ-conceal step) =
  ⊢conceal tyVar∈ α∈ c⊢ (preserve M⊢ step)
preserve (⊢⊕ op L⊢ M⊢) (ξ-⊕₁ step) =
  ⊢⊕ op (preserve L⊢ step) M⊢
preserve (⊢⊕ op V⊢ M⊢) (ξ-⊕₂ Vᵥ step) =
  ⊢⊕ op V⊢ (preserve M⊢ step)
preserve (⊢ν M⊢) (ξ-ν step) = ⊢ν (preserve M⊢ step)
preserve (⊢· (⊢ν M⊢) N⊢) (float-·₁ result) =
  ⊢ν (⊢· M⊢ (⊢shiftᶿ N⊢))
preserve (⊢· V⊢ (⊢ν M⊢)) (float-·₂ Vᵥ result) =
  ⊢ν (⊢· (⊢shiftᶿ V⊢) M⊢)
preserve (⊢⦂∀ (⊢ν M⊢)) (float-• result) = ⊢ν (⊢⦂∀ M⊢)
preserve (⊢⟨⟩ (⊢ν M⊢) c) (float-⟨⟩ result) =
  ⊢ν (⊢⟨⟩ M⊢ c)
preserve (⊢⊕ op (⊢ν M⊢) N⊢) (float-⊕₁ result) =
  ⊢ν (⊢⊕ op M⊢ (⊢shiftᶿ N⊢))
preserve (⊢⊕ op V⊢ (⊢ν M⊢)) (float-⊕₂ Vᵥ result) =
  ⊢ν (⊢⊕ op (⊢shiftᶿ V⊢) M⊢)

------------------------------------------------------------------------
-- Historical refutation records
------------------------------------------------------------------------

-- `β-reveal-∀`: the old rule chose its source body only in the contractum,
-- so the checked ℕ/𝔹 instance stepped to an untypable term.  Source
-- determinacy now computes ℕ from the redex, making that step impossible.
--
-- `β-conceal-∀`: the old type-variable-dependent instantiation lost the abstract
-- type variable.  The deterministic rule resolves it at the ended view and seals the
-- result on exit; the former instance is now preserved.
--
-- `β-conceal-⇒`: the former obstruction was precisely the missing re-entry
-- transport.  `⊢reenter` now supplies the balanced end/begin scope.
--
-- `float-reveal`/`float-conceal`: commits 3ee5de8c/a18f75f4 record the
-- resolving-float counterexample.  The restored reveal float is guarded by
-- strengthening; conceal remains absent.
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
