module proof.NuReductionDeterminism where

-- File Charter:
--   * Determinism and terminal-state infrastructure for Nu reduction.
--   * Proves that values and blame cannot step, that one-step reduction is
--     deterministic, and that a reduction tail is a prefix of any trace to a
--     terminal value or blame.
--   * The prefix lemmas are the trace-alignment boundary needed to iterate the
--     weak one-step imprecision simulation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import Coercions
open import NuTerms
open import NuReduction


pure-value-irreducible :
  ∀ {V N} →
  Value V →
  V —→ N →
  ⊥
pure-value-irreducible (ƛ N) ()
pure-value-irreducible (Λ vV) ()
pure-value-irreducible ($ κ) ()
pure-value-irreducible (() ⟨ G ! ⟩) blame-⟨⟩
pure-value-irreducible (() ⟨ seal A α ⟩) blame-⟨⟩
pure-value-irreducible (() ⟨ c ↦ d ⟩) blame-⟨⟩
pure-value-irreducible (() ⟨ `∀ c ⟩) blame-⟨⟩
pure-value-irreducible (() ⟨ gen A c ⟩) blame-⟨⟩

value-irreducible :
  ∀ {V χ N} →
  Value V →
  V —→[ χ ] N →
  ⊥
value-irreducible vV (pure-step V→N) =
  pure-value-irreducible vV V→N
value-irreducible (vV ⟨ G ! ⟩) (ξ-⟨⟩ V→N) =
  value-irreducible vV V→N
value-irreducible (vV ⟨ seal A α ⟩) (ξ-⟨⟩ V→N) =
  value-irreducible vV V→N
value-irreducible (vV ⟨ c ↦ d ⟩) (ξ-⟨⟩ V→N) =
  value-irreducible vV V→N
value-irreducible (vV ⟨ `∀ c ⟩) (ξ-⟨⟩ V→N) =
  value-irreducible vV V→N
value-irreducible (vV ⟨ gen A c ⟩) (ξ-⟨⟩ V→N) =
  value-irreducible vV V→N

blame-irreducible :
  ∀ {χ N} →
  blame —→[ χ ] N →
  ⊥
blame-irreducible (pure-step ())


pure-deterministic :
  ∀ {M N N′} →
  M —→ N →
  M —→ N′ →
  N ≡ N′
pure-deterministic δ-⊕ δ-⊕ = refl
pure-deterministic (β vV) (β vV′) = refl
pure-deterministic (β-Λ• vV) (β-Λ• vV′) = refl
pure-deterministic (β-∀• vV) (β-∀• vV′) = refl
pure-deterministic (β-gen• vV) (β-gen• vV′) = refl
pure-deterministic (β-id vV) (β-id vV′) = refl
pure-deterministic (β-seq vV) (β-seq vV′) = refl
pure-deterministic (β-↦ vV vW) (β-↦ vV′ vW′) = refl
pure-deterministic (β-inst vV) (β-inst vV′) = refl
pure-deterministic (tag-untag-ok vV) (tag-untag-ok vV′) = refl
pure-deterministic (tag-untag-ok vV)
  (tag-untag-bad vV′ G≠G) = ⊥-elim (G≠G refl)
pure-deterministic (tag-untag-bad vV G≠G)
  (tag-untag-ok vV′) = ⊥-elim (G≠G refl)
pure-deterministic (tag-untag-bad vV G≠H)
  (tag-untag-bad vV′ G≠H′) = refl
pure-deterministic (seal-unseal vV) (seal-unseal vV′) = refl
pure-deterministic blame-·₁ blame-·₁ = refl
pure-deterministic (blame-·₂ vV) (blame-·₂ vV′) = refl
pure-deterministic blame-• blame-• = refl
pure-deterministic blame-⟨⟩ blame-⟨⟩ = refl
pure-deterministic blame-⊕₁ blame-⊕₁ = refl
pure-deterministic (blame-⊕₂ vV) (blame-⊕₂ vV′) = refl


pure-full-deterministic :
  ∀ {M N N′ χ} →
  M —→ N →
  M —→[ χ ] N′ →
  (χ ≡ keep) × (N ≡ N′)
pure-full-deterministic M→N (pure-step M→N′) =
  refl , pure-deterministic M→N M→N′
pure-full-deterministic δ-⊕ (ξ-⊕₁ L→L′ shift) =
  ⊥-elim (value-irreducible ($ _) L→L′)
pure-full-deterministic δ-⊕ (ξ-⊕₂ vL shift M→M′) =
  ⊥-elim (value-irreducible ($ _) M→M′)
pure-full-deterministic (β vV) (ξ-·₁ L→L′ shift) =
  ⊥-elim (value-irreducible (ƛ _) L→L′)
pure-full-deterministic (β vV) (ξ-·₂ vL shift M→M′) =
  ⊥-elim (value-irreducible vV M→M′)
pure-full-deterministic (β-id vV) (ξ-⟨⟩ V→V′) =
  ⊥-elim (value-irreducible vV V→V′)
pure-full-deterministic (β-seq vV) (ξ-⟨⟩ V→V′) =
  ⊥-elim (value-irreducible vV V→V′)
pure-full-deterministic (β-↦ vV vW) (ξ-·₁ L→L′ shift) =
  ⊥-elim (value-irreducible (vV ⟨ _ ↦ _ ⟩) L→L′)
pure-full-deterministic (β-↦ vV vW) (ξ-·₂ vL shift W→W′) =
  ⊥-elim (value-irreducible vW W→W′)
pure-full-deterministic (β-inst vV) (ξ-⟨⟩ V→V′) =
  ⊥-elim (value-irreducible vV V→V′)
pure-full-deterministic (tag-untag-ok vV) (ξ-⟨⟩ V→V′) =
  ⊥-elim (value-irreducible (vV ⟨ _ ! ⟩) V→V′)
pure-full-deterministic (tag-untag-bad vV G≠H) (ξ-⟨⟩ V→V′) =
  ⊥-elim (value-irreducible (vV ⟨ _ ! ⟩) V→V′)
pure-full-deterministic (seal-unseal vV) (ξ-⟨⟩ V→V′) =
  ⊥-elim (value-irreducible (vV ⟨ seal _ _ ⟩) V→V′)
pure-full-deterministic blame-·₁ (ξ-·₁ L→L′ shift) =
  ⊥-elim (blame-irreducible L→L′)
pure-full-deterministic blame-·₁ (ξ-·₂ () shift M→M′)
pure-full-deterministic (blame-·₂ vV) (ξ-·₁ V→V′ shift) =
  ⊥-elim (value-irreducible vV V→V′)
pure-full-deterministic (blame-·₂ vV)
  (ξ-·₂ vV′ shift blame→N) = ⊥-elim (blame-irreducible blame→N)
pure-full-deterministic blame-⟨⟩ (ξ-⟨⟩ blame→N) =
  ⊥-elim (blame-irreducible blame→N)
pure-full-deterministic blame-⊕₁ (ξ-⊕₁ blame→N shift) =
  ⊥-elim (blame-irreducible blame→N)
pure-full-deterministic blame-⊕₁ (ξ-⊕₂ () shift M→M′)
pure-full-deterministic (blame-⊕₂ vV) (ξ-⊕₁ V→V′ shift) =
  ⊥-elim (value-irreducible vV V→V′)
pure-full-deterministic (blame-⊕₂ vV)
  (ξ-⊕₂ vV′ shift blame→N) = ⊥-elim (blame-irreducible blame→N)


step-deterministic :
  ∀ {M N N′ χ χ′} →
  M —→[ χ ] N →
  M —→[ χ′ ] N′ →
  (χ ≡ χ′) × (N ≡ N′)
step-deterministic (pure-step M→N) M→N′
  with pure-full-deterministic M→N M→N′
step-deterministic (pure-step M→N) M→N′ | refl , refl = refl , refl
step-deterministic M→N (pure-step M→N′)
  with pure-full-deterministic M→N′ M→N
step-deterministic M→N (pure-step M→N′) | refl , refl = refl , refl
step-deterministic (ν-step vV no•V) (ν-step vV′ no•V′) = refl , refl
step-deterministic (ν-step vV no•V) (ξ-ν V→V′) =
  ⊥-elim (value-irreducible vV V→V′)
step-deterministic (ν-step () no•V) blame-ν
step-deterministic (ξ-ν V→V′) (ν-step vV no•V) =
  ⊥-elim (value-irreducible vV V→V′)
step-deterministic (ξ-ν L→L′) (ξ-ν L→L′′)
  with step-deterministic L→L′ L→L′′
step-deterministic (ξ-ν L→L′) (ξ-ν L→L′′) | refl , refl =
  refl , refl
step-deterministic (ξ-ν blame→N) blame-ν =
  ⊥-elim (blame-irreducible blame→N)
step-deterministic blame-ν (ν-step () no•V)
step-deterministic blame-ν (ξ-ν blame→N) =
  ⊥-elim (blame-irreducible blame→N)
step-deterministic blame-ν blame-ν = refl , refl
step-deterministic (ξ-·₁ L→L′ shift) (ξ-·₁ L→L′′ shift′)
  with step-deterministic L→L′ L→L′′
step-deterministic (ξ-·₁ L→L′ shift) (ξ-·₁ L→L′′ shift′)
  | refl , refl = refl , refl
step-deterministic (ξ-·₁ V→V′ shift) (ξ-·₂ vV shift′ M→M′) =
  ⊥-elim (value-irreducible vV V→V′)
step-deterministic (ξ-·₂ vV shift M→M′) (ξ-·₁ V→V′ shift′) =
  ⊥-elim (value-irreducible vV V→V′)
step-deterministic (ξ-·₂ vV shift M→M′)
  (ξ-·₂ vV′ shift′ M→M′′)
  with step-deterministic M→M′ M→M′′
step-deterministic (ξ-·₂ vV shift M→M′)
  (ξ-·₂ vV′ shift′ M→M′′) | refl , refl = refl , refl
step-deterministic (ξ-⟨⟩ M→M′) (ξ-⟨⟩ M→M′′)
  with step-deterministic M→M′ M→M′′
step-deterministic (ξ-⟨⟩ M→M′) (ξ-⟨⟩ M→M′′) | refl , refl =
  refl , refl
step-deterministic (ξ-⊕₁ L→L′ shift) (ξ-⊕₁ L→L′′ shift′)
  with step-deterministic L→L′ L→L′′
step-deterministic (ξ-⊕₁ L→L′ shift) (ξ-⊕₁ L→L′′ shift′)
  | refl , refl = refl , refl
step-deterministic (ξ-⊕₁ V→V′ shift) (ξ-⊕₂ vV shift′ M→M′) =
  ⊥-elim (value-irreducible vV V→V′)
step-deterministic (ξ-⊕₂ vV shift M→M′) (ξ-⊕₁ V→V′ shift′) =
  ⊥-elim (value-irreducible vV V→V′)
step-deterministic (ξ-⊕₂ vV shift M→M′)
  (ξ-⊕₂ vV′ shift′ M→M′′)
  with step-deterministic M→M′ M→M′′
step-deterministic (ξ-⊕₂ vV shift M→M′)
  (ξ-⊕₂ vV′ shift′ M→M′′) | refl , refl = refl , refl


target-tail-prefix-value :
  ∀ {M N V χs ψs} →
  M —↠[ χs ] N →
  M —↠[ ψs ] V →
  Value V →
  ∃[ θs ] ((N —↠[ θs ] V) × (ψs ≡ χs ++ θs))
target-tail-prefix-value {ψs = ψs} ↠-refl M↠V vV =
  ψs , M↠V , refl
target-tail-prefix-value (↠-step M→L L↠N) ↠-refl vM =
  ⊥-elim (value-irreducible vM M→L)
target-tail-prefix-value (↠-step M→L L↠N)
  (↠-step M→L′ L′↠V) vV
  with step-deterministic M→L M→L′
target-tail-prefix-value (↠-step M→L L↠N)
  (↠-step M→L′ L′↠V) vV | refl , refl
  with target-tail-prefix-value L↠N L′↠V vV
target-tail-prefix-value (↠-step M→L L↠N)
  (↠-step M→L′ L′↠V) vV | refl , refl
  | θs , N↠V , ψs≡χs++θs =
    θs , N↠V , cong (_ ∷_) ψs≡χs++θs


source-blame-excludes-value :
  ∀ {M V χs ψs} →
  M —↠[ χs ] blame →
  M —↠[ ψs ] V →
  Value V →
  ⊥
source-blame-excludes-value M↠blame M↠V vV
  with target-tail-prefix-value M↠blame M↠V vV
source-blame-excludes-value M↠blame M↠V ()
  | θs , ↠-refl , trace-eq
source-blame-excludes-value M↠blame M↠V vV
  | θs , ↠-step blame→L L↠V , trace-eq =
    blame-irreducible blame→L

target-tail-prefix-blame :
  ∀ {M N χs ψs} →
  M —↠[ χs ] N →
  M —↠[ ψs ] blame →
  ∃[ θs ] ((N —↠[ θs ] blame) × (ψs ≡ χs ++ θs))
target-tail-prefix-blame {ψs = ψs} ↠-refl M↠blame =
  ψs , M↠blame , refl
target-tail-prefix-blame (↠-step M→L L↠N) ↠-refl =
  ⊥-elim (blame-irreducible M→L)
target-tail-prefix-blame (↠-step M→L L↠N)
  (↠-step M→L′ L′↠blame)
  with step-deterministic M→L M→L′
target-tail-prefix-blame (↠-step M→L L↠N)
  (↠-step M→L′ L′↠blame) | refl , refl
  with target-tail-prefix-blame L↠N L′↠blame
target-tail-prefix-blame (↠-step M→L L↠N)
  (↠-step M→L′ L′↠blame) | refl , refl
  | θs , N↠blame , ψs≡χs++θs =
    θs , N↠blame , cong (_ ∷_) ψs≡χs++θs
