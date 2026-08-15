module proof.DGG.notes.M5StructuralNameSourceCastCounterexampleScratch where

-- File Charter:
--   * Checks the source-cast premise-final obstruction for NS-4.
--   * Exhibits an inert source cast whose parent final imprecision exists
--     while the recursive premise final imprecision is refutable.

open import Relation.Nullary using (¬_)

open import Types
open import Imprecision using (idᵐ; _⊢_⊑_)
import Imprecision as I
open import Consistency using (idᶜ; _⊢_∼_; id; _!; _↦_)
import CastTerms as CT


ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ


source-pre : Ty 0
source-pre = ★ ⇒ ℕ₀


source-post : Ty 0
source-post = ℕ₀ ⇒ ℕ₀


ℕ-atom : Atom ℕ₀
ℕ-atom = ‵ `ℕ


ℕ! : idᶜ ⊢ ℕ₀ ∼ ★
ℕ! = _! (id ℕ-atom)


source-cast-counterexample :
  idᶜ ⊢ source-pre ∼ source-post
source-cast-counterexample = ℕ! ↦ id ℕ-atom


source-cast-counterexample-inert :
  CT.Inert source-cast-counterexample
source-cast-counterexample-inert = CT.fun


outer-q : idᵐ ⊢ source-post ⊑ source-post
outer-q = I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι


not-★⊑ℕ : ¬ (idᵐ ⊢ ★ ⊑ ℕ₀)
not-★⊑ℕ ()


no-premise-q :
  ¬ (idᵐ ⊢ source-pre ⊑ source-post)
no-premise-q (I.⇒⊑⇒ dom cod) = not-★⊑ℕ dom
