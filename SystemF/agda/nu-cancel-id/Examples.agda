module nu-cancel-id.Examples where

-- File Charter:
--   * EXAMPLES 5b AND 5c of notes/CancelIdSketch.md (strong-rep-nu),
--     typed at NAMED types and run, by hand-written derivations.
--   * 5c, `(ΛX. λx:X. (ΛY. λ_:Int. x) [Bool] 0) [Int] 3`, is stuck with
--     CancelId and Cancel-□ alone: an `idᶜ` reveal of Y sits between the
--     unseal of X and its seal.  Push moves the unseal through it.  The
--     copy of `x` that Beta puts under `ΛY` is wrapped in `crossΛ`'s
--     hiding layer `[ ⁻ , 0 ]`, which sinks below the seal and is
--     removed by Id.  12 steps.
--   * 5b, `((ΛX. λf:∀Y.Y→Y. f [X]) [Bool] (ΛZ. λz:Z. z)) false`, is the
--     program whose run broke named types under the first version's
--     Sink.  Here the argument stays `[ ⁺ , X ] (Y-sealed) ⟨ idᶜ ⟩`, and
--     the hide above it cancels with it: 11 steps, as in νF.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction

∅ : Ctx
∅ = [] ∣ []

0≢1 : 0 ≢ 1
0≢1 ()

------------------------------------------------------------------------
-- 5c
------------------------------------------------------------------------

-- the body of ΛX, applied: ν Y:=Bool. ((ΛY. λ_:Int. x) Y)⟨id → id⟩ 0
B5c : Term
B5c = ν `𝔹 · (Λ (ƛ `ℕ ∙ ` 1)) ⟨ idᶜ ↦ idᶜ ⟩ · $ nat 0

-- ν X:=Int. ((ΛX. λx:X. B) X)⟨−X → +X⟩ 3
ex5c : Term
ex5c = ν `ℕ · (Λ (ƛ ` 0 ∙ B5c)) ⟨ seal ↦ unseal ⟩ · $ nat 3

⊢ex5c : ∅ ∣ [] ⊢ ex5c ⦂ `ℕ
⊢ex5c = ⊢· (⊢ν s-ℕ (⊢Λ (⊢ƛ (s-var n-here) ⊢B))
                (s-⇒ (s-var n-here) (s-var n-here))
                (s-⇒ s-ℕ s-ℕ)
                (c-fun (c-seal p-here) (c-unseal p-here)))
           ⊢nat
  where
  -- names: X is 0; under ΛY, Y is 0 and X is 1
  ⊢B : underΛ ∅ ∣ ` 0 ∷ [] ⊢ B5c ⦂ ` 0
  ⊢B = ⊢· (⊢ν s-𝔹 (⊢Λ (⊢ƛ s-ℕ (⊢` (x-there x-here))))
              (s-⇒ s-ℕ (s-var (n-named n-here)))
              (s-⇒ s-ℕ (s-var (n-hidden n-here)))
              (c-fun (c-id r-ℕ) (c-id (r-var (s≤s (s≤s z≤n))))))
          ⊢nat

-- the argument 3, sealed as X, and its copy under ΛY
W5c : Term
W5c = [ ⁻ , 0 ] $ nat 3 ⟨ seal ⟩

C5c : Term
C5c = [ ⁻ , 0 ] ([ ⁻ , 1 ] $ nat 3 ⟨ seal ⟩) ⟨ idᶜ ⟩

run-5c : ∅ ⊢ ex5c —↠ $ nat 3 ⊣ ((pay `𝔹 ∷ pay `ℕ ∷ []) ∣ (false ∷ false ∷ []))
run-5c =
    ν `ℕ · (Λ (ƛ ` 0 ∙ B5c)) ⟨ seal ↦ unseal ⟩ · $ nat 3
  —→⟨ ξ-·₁ (tyβ s-ℕ (V-fun F-Λ) inst-Λ) ⟩
    [ ⁺ , 0 ] (ƛ ` 0 ∙ B5c) ⟨ seal ↦ unseal ⟩ · $ nat 3
  —→⟨ wrap (V-fun F-ƛ) V-$ ⟩
    [ ⁺ , 0 ] ((ƛ ` 0 ∙ B5c) · W5c) ⟨ unseal ⟩
  —→⟨ ξ-[] (β-ƛ (V-sealed (S-seal V-$))) ⟩
    [ ⁺ , 0 ] (ν `𝔹 · (Λ (ƛ `ℕ ∙ C5c)) ⟨ idᶜ ↦ idᶜ ⟩ · $ nat 0) ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-·₁ (tyβ s-𝔹 (V-fun F-Λ) inst-Λ)) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] (ƛ `ℕ ∙ C5c) ⟨ idᶜ ↦ idᶜ ⟩ · $ nat 0) ⟨ unseal ⟩
  —→⟨ ξ-[] (wrap (V-fun F-ƛ) V-$) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ] ((ƛ `ℕ ∙ C5c) · [ ⁻ , 0 ] $ nat 0 ⟨ idᶜ ⟩) ⟨ idᶜ ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (ξ-·₂ (V-fun F-ƛ) id-$)) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] ((ƛ `ℕ ∙ C5c) · $ nat 0) ⟨ idᶜ ⟩) ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (β-ƛ V-$)) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] C5c ⟨ idᶜ ⟩) ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (sink 0≢1 V-$)) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ] ([ ⁻ , 1 ] ([ ⁻ , 0 ] $ nat 3 ⟨ idᶜ ⟩) ⟨ seal ⟩) ⟨ idᶜ ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (ξ-[] id-$)) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] ([ ⁻ , 1 ] $ nat 3 ⟨ seal ⟩) ⟨ idᶜ ⟩) ⟨ unseal ⟩
  —→⟨ push (S-seal V-$) ⟩
    [ ⁺ , 0 ] ([ ⁺ , 1 ] ([ ⁻ , 1 ] $ nat 3 ⟨ seal ⟩) ⟨ unseal ⟩) ⟨ idᶜ ⟩
  —→⟨ ξ-[] (cancel-□ V-$) ⟩
    [ ⁺ , 0 ] $ nat 3 ⟨ idᶜ ⟩
  —→⟨ id-$ ⟩
    $ nat 3
  ∎

------------------------------------------------------------------------
-- 5b
------------------------------------------------------------------------

-- ΛZ. λz:Z. z
G5b : Term
G5b = Λ (ƛ ` 0 ∙ ` 0)

-- λf:(∀Y.Y→Y). ν Y:=X. (f Y)⟨−Y → +Y⟩
F5b : Term
F5b = ƛ `∀ (` 0 ⇒ ` 0) ∙ (ν (` 0) · ` 0 ⟨ seal ↦ unseal ⟩)

-- ν X:=Bool. ((ΛX. F) X)⟨(∀Y. id → id) → (−X → +X)⟩ (ΛZ. λz:Z. z) false
ex5b : Term
ex5b = ν `𝔹 · (Λ F5b) ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ unseal) ⟩
         · G5b · $ bool false

⊢ex5b : ∅ ∣ [] ⊢ ex5b ⦂ `𝔹
⊢ex5b = ⊢· (⊢· (⊢ν s-𝔹 (⊢Λ ⊢F) spC spB c₀) ⊢G) ⊢bool
  where
  sp00 : ∀ {Φ} → (true ∷ Φ) ⊢ ` 0 ⇒ ` 0 ⇝ ` 0 ⇒ ` 0
  sp00 = s-⇒ (s-var n-here) (s-var n-here)

  spC : (true ∷ []) ⊢ `∀ (` 0 ⇒ ` 0) ⇒ (` 0 ⇒ ` 0)
                    ⇝ `∀ (` 0 ⇒ ` 0) ⇒ (` 0 ⇒ ` 0)
  spC = s-⇒ (s-∀ sp00) sp00

  spB : (false ∷ []) ⊢ `∀ (` 0 ⇒ ` 0) ⇒ (`𝔹 ⇒ `𝔹)
                     ⇝ `∀ (` 0 ⇒ ` 0) ⇒ (`𝔹 ⇒ `𝔹)
  spB = s-⇒ (s-∀ sp00) (s-⇒ s-𝔹 s-𝔹)

  c₀ : (pay `𝔹 ∷ []) ∣ ⁺ , zero
         ⊢ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ unseal)
         ⦂ `∀ (` 0 ⇒ ` 0) ⇒ (` 0 ⇒ ` 0) ⟹ `∀ (` 0 ⇒ ` 0) ⇒ (`𝔹 ⇒ `𝔹)
  c₀ = c-fun (c-all (c-fun (c-id (r-var (s≤s z≤n)))
                           (c-id (r-var (s≤s z≤n)))))
             (c-fun (c-seal p-here) (c-unseal p-here))

  -- under ΛX, X is name 0; the inner ν reads Y:=X
  ⊢F : underΛ ∅ ∣ [] ⊢ F5b ⦂ `∀ (` 0 ⇒ ` 0) ⇒ (` 0 ⇒ ` 0)
  ⊢F = ⊢ƛ (s-∀ sp00)
          (⊢ν (s-var n-here) (⊢` x-here) sp00
              (s-⇒ (s-var (n-hidden n-here)) (s-var (n-hidden n-here)))
              (c-fun (c-seal p-here) (c-unseal p-here)))

  ⊢G : ∅ ∣ [] ⊢ G5b ⦂ `∀ (` 0 ⇒ ` 0)
  ⊢G = ⊢Λ (⊢ƛ (s-var n-here) (⊢` x-here))

-- α is cell 1 (X:=Bool), β is cell 0 (Y:=X)
L5b : Term
L5b = [ ⁻ , 1 ] (ƛ ` 0 ∙ ` 0) ⟨ idᶜ ↦ idᶜ ⟩

-- false, sealed as X, then as Y, then under the reveal of X
A5b : Term
A5b = [ ⁺ , 1 ] ([ ⁻ , 0 ] ([ ⁻ , 1 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩) ⟨ idᶜ ⟩

run-5b : ∅ ⊢ ex5b —↠ $ bool false
           ⊣ ((pay (` 0) ∷ pay `𝔹 ∷ []) ∣ (false ∷ false ∷ []))
run-5b =
    ν `𝔹 · (Λ F5b) ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ unseal) ⟩ · G5b · $ bool false
  —→⟨ ξ-·₁ (ξ-·₁ (tyβ s-𝔹 (V-fun F-Λ) inst-Λ)) ⟩
    [ ⁺ , 0 ] F5b ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ unseal) ⟩ · G5b · $ bool false
  —→⟨ ξ-·₁ (wrap (V-fun F-ƛ) (V-fun F-Λ)) ⟩
    [ ⁺ , 0 ] (F5b · [ ⁻ , 0 ] G5b ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ⟩) ⟨ seal ↦ unseal ⟩
      · $ bool false
  —→⟨ ξ-·₁ (ξ-[] (β-ƛ (V-fun (F-∀ (V-fun F-Λ))))) ⟩
    [ ⁺ , 0 ]
      (ν (` 0) · [ ⁻ , 0 ] G5b ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ⟩ ⟨ seal ↦ unseal ⟩)
    ⟨ seal ↦ unseal ⟩ · $ bool false
  —→⟨ ξ-·₁ (ξ-[] (tyβ (s-var n-here) (V-fun (F-∀ (V-fun F-Λ)))
                       (inst-∀ inst-Λ))) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] L5b ⟨ seal ↦ unseal ⟩) ⟨ seal ↦ unseal ⟩
      · $ bool false
  —→⟨ wrap (V-fun (F-↦ (V-fun (F-↦ (V-fun F-ƛ))))) V-$ ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ] L5b ⟨ seal ↦ unseal ⟩ · [ ⁻ , 1 ] $ bool false ⟨ seal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (wrap (V-fun (F-↦ (V-fun F-ƛ))) (V-sealed (S-seal V-$))) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ]
         (L5b · [ ⁻ , 0 ] ([ ⁻ , 1 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (wrap (V-fun F-ƛ) (V-sealed (S-seal (V-sealed
                                                (S-seal V-$)))))) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ] ([ ⁻ , 1 ] ((ƛ ` 0 ∙ ` 0) · A5b) ⟨ idᶜ ⟩) ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (ξ-[] (β-ƛ (V-sealed (S-rev (S-seal (V-sealed
                                                  (S-seal V-$)))))))) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] ([ ⁻ , 1 ] A5b ⟨ idᶜ ⟩) ⟨ unseal ⟩) ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (cancel-id (V-sealed (S-seal (V-sealed
                                          (S-seal V-$)))))) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ] ([ ⁻ , 0 ] ([ ⁻ , 1 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (cancel-□ (V-sealed (S-seal V-$))) ⟩
    [ ⁺ , 1 ] ([ ⁻ , 1 ] $ bool false ⟨ seal ⟩) ⟨ unseal ⟩
  —→⟨ cancel-□ V-$ ⟩
    $ bool false
  ∎
