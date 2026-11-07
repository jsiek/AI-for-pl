module nu-cancel-id.Examples where

-- File Charter:
--   * EXAMPLE 5c of notes/CancelIdSketch.md (strong-rep-nu), typed and
--     run by hand-written derivations:
--
--       (ΛX. λx:X. (ΛY. λ_:Int. x) [Bool] 0) [Int] 3          : Int
--
--     This is the program that is STUCK with CancelId and Cancel-□ alone
--     (sketch §2); here Sink moves the `[ ⁺ , β ]` layer below the seal
--     and the run ends in Cancel-□.
--   * Unlike the sketch's named trace, the copy of `x` that Beta puts
--     under `ΛY` is wrapped in `crossΛ`'s hiding layer `[ ⁻ , 0 ]`, so
--     the run takes one more Sink and one more Id: 12 steps.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction

------------------------------------------------------------------------
-- The program
------------------------------------------------------------------------

∅ : Ctx
∅ = [] ∣ []

-- the body of ΛX, applied: ν Y:=Bool. ((ΛY. λ_:Int. x) Y)⟨id → id⟩ 0
B : Term
B = ν `𝔹 · (Λ (ƛ `ℕ ∙ ` 1)) ⟨ idᶜ ↦ idᶜ ⟩ · $ nat 0

-- ν X:=Int. ((ΛX. λx:X. B) X)⟨−X → +X⟩ 3
5c : Term
5c = ν `ℕ · (Λ (ƛ ` 0 ∙ B)) ⟨ seal ↦ unseal ⟩ · $ nat 3

⊢5c : ∅ ∣ [] ⊢ 5c ⦂ `ℕ
⊢5c = ⊢· (⊢ν s-ℕ (⊢Λ (⊢ƛ (s-var n-here) ⊢B))
              (c-fun (c-seal p-here) (c-unseal p-here))
              (r-⇒ r-ℕ r-ℕ))
         ⊢nat
  where
  ⊢B : underΛ ∅ ∣ ` 0 ∷ [] ⊢ B ⦂ ` 0
  ⊢B = ⊢· (⊢ν s-𝔹 (⊢Λ (⊢ƛ s-ℕ (⊢` (x-there x-here))))
              (c-fun (c-id r-ℕ) (c-id (r-var (s≤s (s≤s z≤n)))))
              (r-⇒ r-ℕ (r-var (s≤s z≤n))))
          ⊢nat

------------------------------------------------------------------------
-- The run
------------------------------------------------------------------------

0≢1 : 0 ≢ 1
0≢1 ()

-- the argument 3, sealed as X, and its copy under ΛY
W : Term
W = [ ⁻ , 0 ] $ nat 3 ⟨ seal ⟩

C : Term
C = [ ⁻ , 0 ] ([ ⁻ , 1 ] $ nat 3 ⟨ seal ⟩) ⟨ idᶜ ⟩

run-5c : ∅ ⊢ 5c —↠ $ nat 3 ⊣ ((pay `𝔹 ∷ pay `ℕ ∷ []) ∣ (false ∷ false ∷ []))
run-5c =
    ν `ℕ · (Λ (ƛ ` 0 ∙ B)) ⟨ seal ↦ unseal ⟩ · $ nat 3
  —→⟨ ξ-·₁ (tyβ s-ℕ (V-fun F-Λ) inst-Λ) ⟩
    [ ⁺ , 0 ] (ƛ ` 0 ∙ B) ⟨ seal ↦ unseal ⟩ · $ nat 3
  —→⟨ wrap (V-fun F-ƛ) V-$ ⟩
    [ ⁺ , 0 ] ((ƛ ` 0 ∙ B) · W) ⟨ unseal ⟩
  —→⟨ ξ-[] (β-ƛ (V-sealed (S-seal V-$))) ⟩
    [ ⁺ , 0 ] (ν `𝔹 · (Λ (ƛ `ℕ ∙ C)) ⟨ idᶜ ↦ idᶜ ⟩ · $ nat 0) ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-·₁ (tyβ s-𝔹 (V-fun F-Λ) inst-Λ)) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] (ƛ `ℕ ∙ C) ⟨ idᶜ ↦ idᶜ ⟩ · $ nat 0) ⟨ unseal ⟩
  —→⟨ ξ-[] (wrap (V-fun F-ƛ) V-$) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ] ((ƛ `ℕ ∙ C) · [ ⁻ , 0 ] $ nat 0 ⟨ idᶜ ⟩) ⟨ idᶜ ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (ξ-·₂ (V-fun F-ƛ) id-$)) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] ((ƛ `ℕ ∙ C) · $ nat 0) ⟨ idᶜ ⟩) ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (β-ƛ V-$)) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] C ⟨ idᶜ ⟩) ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (sink-seal 0≢1 V-$)) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ] ([ ⁻ , 1 ] ([ ⁻ , 0 ] $ nat 3 ⟨ idᶜ ⟩) ⟨ seal ⟩) ⟨ idᶜ ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (ξ-[] id-$)) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] ([ ⁻ , 1 ] $ nat 3 ⟨ seal ⟩) ⟨ idᶜ ⟩) ⟨ unseal ⟩
  —→⟨ ξ-[] (sink-seal 0≢1 V-$) ⟩
    [ ⁺ , 1 ] ([ ⁻ , 1 ] ([ ⁺ , 0 ] $ nat 3 ⟨ idᶜ ⟩) ⟨ seal ⟩) ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] id-$) ⟩
    [ ⁺ , 1 ] ([ ⁻ , 1 ] $ nat 3 ⟨ seal ⟩) ⟨ unseal ⟩
  —→⟨ cancel-□ V-$ ⟩
    $ nat 3
  ∎
