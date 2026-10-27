module Denot.Meta where

-- File Charter:
--   * The public statements of the syntactic layer of the denotational
--     proof of the dynamic gradual guarantee
--     (notes/denotational-dgg.md, Section 7a):
--       eager-normal-form       `eager` puts a cast in eager normal form;
--       precision-in-imprecision two-context precision is contained in
--                                `Imprecision`;
--       elaboration-preserves-precision
--                                source term precision of closed programs
--                                is preserved by eager elaboration.
--   * Each is a thin wrapper around a theorem in `proof/Denot`.

open import Data.List using ([])
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Types
open import Consistency using (Env∼; _⊢_∼_)
import Imprecision as I
open import GradualTerms using (GTerm; _∣_⊢_⦂_)
open import GradualTermImprecision using (_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import Denot.EagerCast
open import Denot.Precision
open import Denot.CastPrecision
open import Denot.Elaborate
import proof.Denot.EagerCast as P-E
import proof.Denot.Precision as P-P
import proof.Denot.Elaboration as P-El
open import proof.Denot.SwapRename using (renameᵗ-id)
open import proof.DGG.CompilePreservesImprecision2 using (Grenameᵐ-id)

eager-normal-form : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B) → Eager (eager c)
eager-normal-form = P-E.eager-eager

precision-in-imprecision : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A : Ty Δ} {B : Ty Δ′}
  → Φ ⊢ A ⊑ B
  → impEnvᶜ Φ I.⊢ A ⊑ renameᵗ (P-P.embed Φ) B
precision-in-imprecision = P-P.forget

private
  closed-env : ∀ (μ : I.ImpEnv 0) → ∀ X → μ X ≡ impEnvᶜ [] X
  closed-env μ ()

  closed-ty : (B : Ty 0) → B ≡ renameᵗ (P-P.embed []) B
  closed-ty B = sym (trans (renameᵗ-cong B (λ ())) (renameᵗ-id B))

-- Closed programs related by source precision elaborate to cast terms
-- related by cast-calculus precision, whichever typing derivations they
-- are elaborated from.
elaboration-preserves-precision : ∀ {μ : I.ImpEnv 0} {M M′ : GTerm 0}
    {A B : Ty 0} {p : μ I.⊢ A ⊑ B}
  → μ ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p
  → (M⊢ : 0 ∣ [] ⊢ M ⦂ A)
  → (M′⊢ : 0 ∣ [] ⊢ M′ ⦂ B)
  → Σ[ q ∈ [] ⊢ A ⊑ B ]
      [] ∣ [] ⊢ compileᴱ M⊢ ⊑ compileᴱ M′⊢ ⦂ A ⊑ B ∶ q
elaboration-preserves-precision {μ = μ} {M′ = M′} {B = B} {p = p} M⊑ M⊢ M′⊢ =
  _ , P-El.elab-prec (closed-env μ) P-El.rel-[] M⊑
        (sym (Grenameᵐ-id M′)) (closed-ty B)
        (compileᴱ-elab M⊢) (compileᴱ-elab M′⊢)
