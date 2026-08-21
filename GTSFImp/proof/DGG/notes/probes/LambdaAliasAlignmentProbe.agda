module proof.DGG.notes.probes.LambdaAliasAlignmentProbe where

-- File Charter:
--   * Isolates the invariant obstruction in the concrete target store
--     produced by instantiating a target `Λ` value.
--   * Quantifies over every possible center embedding: no valid world can
--     align a source variable with the dynamic name while the newer target
--     alias remains unmatched.
--   * Uses only the live world interface and the concrete store geometry;
--     it does not depend on the abandoned TargetBindLift route.

open import Data.Empty using (⊥)
import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; refl; sym; trans)

open import Types using (Ty; TyVar; ★; ＇_; _⇒_; `∀)
open import TyStore using
  (TyStore; store-empty; store-bind; lookupStore)
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ)
import Conversion as Conv
open Conv using
  (Conv↑; unseal; seal; _↦↑_; join-both; ⊢↑-⇒ˣ;
   ⊢↑-unsealˣ; ⊢↓-sealˣ)
open import CastTerms using (Term; `_; ƛ_; Λ_; _⟨_⟩; _↑_)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX


fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
  → Fin.suc X ≡ Fin.suc Y
  → X ≡ Y
fin-suc-injective refl = refl


embedding-injective : ∀ {Δ Δ′}
    (η : Δ ↪ᵗ Δ′) {X Y : TyVar Δ}
  → toRenameᵗ η X ≡ toRenameᵗ η Y
  → X ≡ Y
embedding-injective empty {()}
embedding-injective (keep η) {Fin.zero} {Fin.zero} eq = refl
embedding-injective (keep η) {Fin.zero} {Fin.suc Y} ()
embedding-injective (keep η) {Fin.suc X} {Fin.zero} ()
embedding-injective (keep η) {Fin.suc X} {Fin.suc Y} eq =
  cong Fin.suc (embedding-injective η (fin-suc-injective eq))
embedding-injective (skip η) eq =
  embedding-injective η (fin-suc-injective eq)


zero≠suc : ∀ {n} {X : Fin.Fin n}
  → Fin.zero ≢ Fin.suc X
zero≠suc ()


variable≠star : ∀ {n} {X : Fin.Fin n}
  → _≢_ {A = Ty n} (＇ X) ★
variable≠star ()


suc-variable≠zero-variable : ∀ {n} {X : Fin.Fin n}
  → _≢_ {A = Ty (Nat.suc n)} (＇ Fin.suc X) (＇ Fin.zero)
suc-variable≠zero-variable ()


alias-name-alignment-impossible : ∀ {Δ}
    {W : CTX.World 1 2 Δ}
  → CTX.targetStoreʷ W
      ≡ store-bind (store-bind store-empty ★) (＇ Fin.zero)
  → toRenameᵗ (CTX.ηᴸʷ W) Fin.zero
      ≡ toRenameᵗ (CTX.ηᴿʷ W) (Fin.suc Fin.zero)
  → ⊥
alias-name-alignment-impossible {W = W} store-eq aligned-name
    with CTX.unmatchedTargetsDynamic (CTX.invariantsʷ W)
      Fin.zero alias-unmatched
  where
  alias-unmatched : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ W) Xᴸ
      ≢ toRenameᵗ (CTX.ηᴿʷ W) Fin.zero
  alias-unmatched Fin.zero aligned-alias =
    zero≠suc
      (embedding-injective (CTX.ηᴿʷ W)
        (trans (sym aligned-alias) aligned-name))
alias-name-alignment-impossible store-eq aligned-name | inj₁ dynamic
    rewrite store-eq = variable≠star dynamic
alias-name-alignment-impossible store-eq aligned-name
    | inj₂ (Fin.zero , entry , no-source) rewrite store-eq =
  suc-variable≠zero-variable entry
alias-name-alignment-impossible store-eq aligned-name
    | inj₂ (Fin.suc Fin.zero , entry , no-source) rewrite store-eq =
  no-source Fin.zero aligned-name


dynamic-name-rebase-impossible : ∀ {Δ}
    {W W′ : CTX.World 1 2 Δ}
  → CTX.targetStoreʷ W
      ≡ store-bind (store-bind store-empty ★) (＇ Fin.zero)
  → CTX.RebaseAt W W′ Fin.zero (Fin.suc Fin.zero)
  → ⊥
dynamic-name-rebase-impossible {W = W} {W′ = W′} store-eq rb =
  alias-name-alignment-impossible {W = W′}
    (trans (CTX.SameRuntime.targetStore-same
      (CTX.RebaseAt.sameRuntime {W = W} {W′ = W′} rb)) store-eq)
    (CTX.RebaseAt.pivotAligned {W = W} {W′ = W′} rb)


alias-reveal : Conv↑ 2
    (＇ Fin.zero ⇒ ＇ Fin.zero)
    (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
alias-reveal =
  seal Fin.zero (＇ (Fin.suc Fin.zero)) ↦↑
  unseal Fin.zero (＇ (Fin.suc Fin.zero))


name-reveal : Conv↑ 2
    (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
    (★ ⇒ ★)
name-reveal =
  seal (Fin.suc Fin.zero) ★ ↦↑
  unseal (Fin.suc Fin.zero) ★


post-body : Term 2
post-body = (ƛ (` 0) ↑ alias-reveal) ↑ name-reveal


post-body-relation-impossible : ∀ {Δ}
    {W : CTX.World 1 2 Δ} {γ : CTX.CtxImp W}
    {p : (＇ Fin.zero ⇒ ＇ Fin.zero) CTX.⊑ᵂ⟨ W ⟩ (★ ⇒ ★)}
  → CTX.targetStoreʷ W
      ≡ store-bind (store-bind store-empty ★) (＇ Fin.zero)
  → W CTI2.∣ γ ⊢² ƛ (` 0) ⊑ post-body ∶ p
  → ⊥
post-body-relation-impossible store-eq
    (CTI2.⊑reveal² mono
      (CTX.rebase-varᴿ {Xᴸ = Fin.zero} rb) same
      (Conv.⊢↑-⇒ˣ Conv.join-both
        (Conv.⊢↓-sealˣ name-entry)
        (Conv.⊢↑-unsealˣ name-entry′)) rel q) =
  dynamic-name-rebase-impossible store-eq rb


smart-target-store-same : ∀ {Δ Δᵐ}
    {W : CTX.World 0 2 Δ}
    {Wᵐ : CTX.World 1 2 Δᵐ}
  → CTX.SmartCommaLiftᴸ W Wᵐ
  → CTX.targetStoreʷ Wᵐ ≡ CTX.targetStoreʷ W
smart-target-store-same (CTX.smart-fresh-behind guard) =
  CTX.SmartFreshBehindGuard.targetStore-same guard
smart-target-store-same (CTX.smart-merge-alias guard) =
  CTX.SmartAliasMergeGuard.targetStore-same guard


whole-post-relation-impossible : ∀ {Δ}
    {W : CTX.World 0 2 Δ} {γ : CTX.CtxImp W}
    {p : (`∀ (＇ Fin.zero ⇒ ＇ Fin.zero))
      CTX.⊑ᵂ⟨ W ⟩ (★ ⇒ ★)}
  → CTX.targetStoreʷ W
      ≡ store-bind (store-bind store-empty ★) (＇ Fin.zero)
  → W CTI2.∣ γ ⊢² Λ (ƛ (` 0)) ⊑ post-body ∶ p
  → ⊥
whole-post-relation-impossible store-eq
    (CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ body q) =
  post-body-relation-impossible store-eq body
whole-post-relation-impossible store-eq
    (CTI2.Λ⊑²-smart-comma
      Anv zero∈A smart liftγ vV target⊢ body q) =
  post-body-relation-impossible
    (trans (smart-target-store-same smart) store-eq) body
whole-post-relation-impossible store-eq
    (CTI2.⊑reveal² mono CTX.rebase-idᴿ same
      (Conv.⊢↑-⇒ˣ Conv.join-none () valid) body q)
whole-post-relation-impossible store-eq
    (CTI2.⊑reveal² mono
      (CTX.rebase-varᴿ {Xᴸ = ()} rb) same valid body q)


post-body-cast-relation-impossible : ∀ {Δ}
    {W : CTX.World 1 2 Δ} {γ : CTX.CtxImp W}
    {μ : Env∼ 2} {c : μ ⊢ (★ ⇒ ★) ∼ (★ ⇒ ★)}
    {p : (＇ Fin.zero ⇒ ＇ Fin.zero) CTX.⊑ᵂ⟨ W ⟩ (★ ⇒ ★)}
  → CTX.targetStoreʷ W
      ≡ store-bind (store-bind store-empty ★) (＇ Fin.zero)
  → W CTI2.∣ γ ⊢² ƛ (` 0) ⊑ post-body ⟨ c ⟩ ∶ p
  → ⊥
post-body-cast-relation-impossible store-eq
    (CTI2.⊑cast² c body q) =
  post-body-relation-impossible store-eq body


whole-post-cast-relation-impossible : ∀ {Δ}
    {W : CTX.World 0 2 Δ} {γ : CTX.CtxImp W}
    {μ : Env∼ 2} {c : μ ⊢ (★ ⇒ ★) ∼ (★ ⇒ ★)}
    {p : (`∀ (＇ Fin.zero ⇒ ＇ Fin.zero))
      CTX.⊑ᵂ⟨ W ⟩ (★ ⇒ ★)}
  → CTX.targetStoreʷ W
      ≡ store-bind (store-bind store-empty ★) (＇ Fin.zero)
  → W CTI2.∣ γ ⊢² Λ (ƛ (` 0)) ⊑ post-body ⟨ c ⟩ ∶ p
  → ⊥
whole-post-cast-relation-impossible store-eq
    (CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ body q) =
  post-body-cast-relation-impossible store-eq body
whole-post-cast-relation-impossible store-eq
    (CTI2.Λ⊑²-smart-comma
      Anv zero∈A smart liftγ vV target⊢ body q) =
  post-body-cast-relation-impossible
    (trans (smart-target-store-same smart) store-eq) body
whole-post-cast-relation-impossible store-eq
    (CTI2.⊑cast² c body q) =
  whole-post-relation-impossible store-eq body
