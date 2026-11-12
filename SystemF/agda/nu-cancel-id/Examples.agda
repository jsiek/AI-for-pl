module nu-cancel-id.Examples where

-- File Charter:
--   * THE FIVE EXAMPLES of Design.md §7, each the elaboration of a
--     System F program, typed at NAMED types and run to a value.  5b and
--     5c are written by hand; 5a, 5d and 5e are generated from an
--     interpreter that follows Reduction.agda rule by rule.
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
--   * 5a discards its sealed argument and uses no boundary rule (11
--     steps).  5d's inverse pair carries arrow conversions, so CancelId
--     does not apply and Wraps take the argument through (17 steps).  5e
--     uses Swap, Sink, CancelId, Push and Cancel-□ (21 steps).
--   * Preservation types every state of every run; the last section
--     types their results.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction
open import nu-cancel-id.Preservation using (preservation*)

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
              (c-fun c-id c-id))
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
  c₀ = c-fun (c-all (c-fun c-id c-id))
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

------------------------------------------------------------------------
-- 5a
------------------------------------------------------------------------

-- ((ΛX. λf:(∀Y. Y → Bool). f [X]) [Bool] (ΛZ. λz:Z. true)) false:
-- the sealed argument is discarded, so no boundary rule fires.

-- λf:(∀Y. Y → Bool). ν Y:=X. (f Y)⟨−Y → id⟩
F5a : Term
F5a = ƛ `∀ (` 0 ⇒ `𝔹) ∙ ν (` 0) · ` 0 ⟨ seal ↦ idᶜ ⟩

-- λz:Z. true
K5a : Term
K5a = ƛ ` 0 ∙ $ bool true

-- ΛZ. λz:Z. true
G5a : Term
G5a = Λ K5a

ex5a : Term
ex5a = ν `𝔹 · (Λ F5a) ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ idᶜ) ⟩ · G5a · $ bool false

⊢ex5a : ∅ ∣ [] ⊢ ex5a ⦂ `𝔹
⊢ex5a =
  ⊢·
    (⊢·
       (⊢ν
          s-𝔹
          (⊢Λ
             (⊢ƛ
                (s-∀ (s-⇒ (s-var n-here) s-𝔹))
                (⊢ν
                   (s-var n-here)
                   (⊢` x-here)
                   (s-⇒ (s-var n-here) s-𝔹)
                   (s-⇒ (s-var (n-hidden n-here)) s-𝔹)
                   (c-fun (c-seal p-here) c-id))))
          (s-⇒ (s-∀ (s-⇒ (s-var n-here) s-𝔹)) (s-⇒ (s-var n-here) s-𝔹))
          (s-⇒ (s-∀ (s-⇒ (s-var n-here) s-𝔹)) (s-⇒ s-𝔹 s-𝔹))
          (c-fun (c-all (c-fun c-id c-id)) (c-fun (c-seal p-here) c-id)))
       (⊢Λ (⊢ƛ (s-var n-here) ⊢bool)))
    ⊢bool

-- the context at the end of the run
Γ5a : Ctx
Γ5a = (pay (` 0) ∷ pay `𝔹 ∷ []) ∣ (false ∷ false ∷ [])

run-5a : ∅ ⊢ ex5a —↠ $ bool true ⊣ Γ5a
run-5a =
    ν `𝔹 · (Λ F5a) ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ idᶜ) ⟩ · G5a · $ bool false
  —→⟨ ξ-·₁ (ξ-·₁ (tyβ s-𝔹 (V-fun F-Λ) inst-Λ)) ⟩
    [ ⁺ , 0 ] F5a ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ idᶜ) ⟩ · G5a · $ bool false
  —→⟨ ξ-·₁ (wrap (V-fun F-ƛ) (V-fun F-Λ)) ⟩
    [ ⁺ , 0 ] (F5a · [ ⁻ , 0 ] G5a ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ⟩) ⟨ seal ↦ idᶜ ⟩
      · $ bool false
  —→⟨ ξ-·₁ (ξ-[] (β-ƛ (V-fun (F-∀ (V-fun F-Λ))))) ⟩
    [ ⁺ , 0 ]
      (ν (` 0) · ([ ⁻ , 0 ] G5a ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ⟩) ⟨ seal ↦ idᶜ ⟩)
    ⟨ seal ↦ idᶜ ⟩
      · $ bool false
  —→⟨ ξ-·₁
        (ξ-[] (tyβ (s-var n-here) (V-fun (F-∀ (V-fun F-Λ))) (inst-∀ inst-Λ))) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ] ([ ⁻ , 1 ] K5a ⟨ idᶜ ↦ idᶜ ⟩) ⟨ seal ↦ idᶜ ⟩)
    ⟨ seal ↦ idᶜ ⟩
      · $ bool false
  —→⟨ wrap (V-fun (F-↦ (V-fun (F-↦ (V-fun F-ƛ))))) V-$ ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ] ([ ⁻ , 1 ] K5a ⟨ idᶜ ↦ idᶜ ⟩) ⟨ seal ↦ idᶜ ⟩
         · [ ⁻ , 1 ] $ bool false ⟨ seal ⟩)
    ⟨ idᶜ ⟩
  —→⟨ ξ-[] (wrap (V-fun (F-↦ (V-fun F-ƛ))) (V-sealed (S-seal V-$))) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ]
         ([ ⁻ , 1 ] K5a ⟨ idᶜ ↦ idᶜ ⟩
            · [ ⁻ , 0 ] ([ ⁻ , 1 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
       ⟨ idᶜ ⟩)
    ⟨ idᶜ ⟩
  —→⟨ ξ-[]
        (ξ-[] (wrap (V-fun F-ƛ) (V-sealed (S-seal (V-sealed (S-seal V-$)))))) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ]
         ([ ⁻ , 1 ]
            (K5a
               · [ ⁺ , 1 ]
                 ([ ⁻ , 0 ] ([ ⁻ , 1 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
               ⟨ idᶜ ⟩)
          ⟨ idᶜ ⟩)
       ⟨ idᶜ ⟩)
    ⟨ idᶜ ⟩
  —→⟨ ξ-[]
        (ξ-[]
           (ξ-[] (β-ƛ (V-sealed (S-rev (S-seal (V-sealed (S-seal V-$)))))))) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] ([ ⁻ , 1 ] $ bool true ⟨ idᶜ ⟩) ⟨ idᶜ ⟩) ⟨ idᶜ ⟩
  —→⟨ ξ-[] (ξ-[] id-$) ⟩
    [ ⁺ , 1 ] ([ ⁺ , 0 ] $ bool true ⟨ idᶜ ⟩) ⟨ idᶜ ⟩
  —→⟨ ξ-[] id-$ ⟩
    [ ⁺ , 1 ] $ bool true ⟨ idᶜ ⟩
  —→⟨ id-$ ⟩
    $ bool true
  ∎

------------------------------------------------------------------------
-- 5d
------------------------------------------------------------------------

-- ((ΛX. λx:X. λg:(Int → X) → Int → Int. g (λn:Int. x)) [Int]
--    5 (λh:Int → Int. h)) 0:
-- the layers `[ ⁻ , 0 ] [ ⁺ , 0 ]` carry `idᶜ ↦ idᶜ` and
-- `idᶜ ↦ unseal`, not `idᶜ`, so CancelId does not apply; three
-- Wraps take 0 through the tower, and Cancel-□ meets the seal.

-- ((id → +X) → (id → id)) → (id → id)
d5d : Conv
d5d = ((idᶜ ↦ unseal) ↦ (idᶜ ↦ idᶜ)) ↦ (idᶜ ↦ idᶜ)

-- λx:X. λg:(Int → X) → Int → Int. g (λn:Int. x)
F5d : Term
F5d = ƛ ` 0 ∙ ƛ (`ℕ ⇒ ` 0) ⇒ (`ℕ ⇒ `ℕ) ∙ ` 0 · (ƛ `ℕ ∙ ` 2)

-- λh:Int → Int. h
H5d : Term
H5d = ƛ `ℕ ⇒ `ℕ ∙ ` 0

-- the argument 5, sealed as X
W5d : Term
W5d = [ ⁻ , 0 ] $ nat 5 ⟨ seal ⟩

-- λn:Int. 5, with 5 sealed
N5d : Term
N5d = ƛ `ℕ ∙ W5d

ex5d : Term
ex5d = ν `ℕ · (Λ F5d) ⟨ seal ↦ d5d ⟩ · $ nat 5 · H5d · $ nat 0

⊢ex5d : ∅ ∣ [] ⊢ ex5d ⦂ `ℕ
⊢ex5d =
  ⊢·
    (⊢·
       (⊢·
          (⊢ν
             s-ℕ
             (⊢Λ
                (⊢ƛ
                   (s-var n-here)
                   (⊢ƛ
                      (s-⇒ (s-⇒ s-ℕ (s-var n-here)) (s-⇒ s-ℕ s-ℕ))
                      (⊢·
                         (⊢` x-here)
                         (⊢ƛ s-ℕ (⊢` (x-there (x-there x-here))))))))
             (s-⇒
                (s-var n-here)
                (s-⇒
                   (s-⇒ (s-⇒ s-ℕ (s-var n-here)) (s-⇒ s-ℕ s-ℕ))
                   (s-⇒ s-ℕ s-ℕ)))
             (s-⇒ s-ℕ (s-⇒ (s-⇒ (s-⇒ s-ℕ s-ℕ) (s-⇒ s-ℕ s-ℕ)) (s-⇒ s-ℕ s-ℕ)))
             (c-fun
                (c-seal p-here)
                (c-fun
                   (c-fun (c-fun c-id (c-unseal p-here)) (c-fun c-id c-id))
                   (c-fun c-id c-id))))
          ⊢nat)
       (⊢ƛ (s-⇒ s-ℕ s-ℕ) (⊢` x-here)))
    ⊢nat

-- the context at the end of the run
Γ5d : Ctx
Γ5d = (pay `ℕ ∷ []) ∣ (false ∷ [])

run-5d : ∅ ⊢ ex5d —↠ $ nat 5 ⊣ Γ5d
run-5d =
    ν `ℕ · (Λ F5d) ⟨ seal ↦ d5d ⟩ · $ nat 5 · H5d · $ nat 0
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (tyβ s-ℕ (V-fun F-Λ) inst-Λ))) ⟩
    [ ⁺ , 0 ] F5d ⟨ seal ↦ d5d ⟩ · $ nat 5 · H5d · $ nat 0
  —→⟨ ξ-·₁ (ξ-·₁ (wrap (V-fun F-ƛ) V-$)) ⟩
    [ ⁺ , 0 ] (F5d · W5d) ⟨ d5d ⟩ · H5d · $ nat 0
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-[] (β-ƛ (V-sealed (S-seal V-$))))) ⟩
    [ ⁺ , 0 ] (ƛ (`ℕ ⇒ ` 0) ⇒ (`ℕ ⇒ `ℕ) ∙ ` 0 · N5d) ⟨ d5d ⟩ · H5d · $ nat 0
  —→⟨ ξ-·₁ (wrap (V-fun F-ƛ) (V-fun F-ƛ)) ⟩
    [ ⁺ , 0 ]
      ((ƛ (`ℕ ⇒ ` 0) ⇒ (`ℕ ⇒ `ℕ) ∙ ` 0 · N5d)
         · [ ⁻ , 0 ] H5d ⟨ (idᶜ ↦ unseal) ↦ (idᶜ ↦ idᶜ) ⟩)
    ⟨ idᶜ ↦ idᶜ ⟩
      · $ nat 0
  —→⟨ ξ-·₁ (ξ-[] (β-ƛ (V-fun (F-↦ (V-fun F-ƛ))))) ⟩
    [ ⁺ , 0 ]
      ([ ⁻ , 0 ] H5d ⟨ (idᶜ ↦ unseal) ↦ (idᶜ ↦ idᶜ) ⟩ · N5d)
    ⟨ idᶜ ↦ idᶜ ⟩
      · $ nat 0
  —→⟨ ξ-·₁ (ξ-[] (wrap (V-fun F-ƛ) (V-fun F-ƛ))) ⟩
    [ ⁺ , 0 ]
      ([ ⁻ , 0 ] (H5d · [ ⁺ , 0 ] N5d ⟨ idᶜ ↦ unseal ⟩) ⟨ idᶜ ↦ idᶜ ⟩)
    ⟨ idᶜ ↦ idᶜ ⟩
      · $ nat 0
  —→⟨ ξ-·₁ (ξ-[] (ξ-[] (β-ƛ (V-fun (F-↦ (V-fun F-ƛ)))))) ⟩
    [ ⁺ , 0 ]
      ([ ⁻ , 0 ] ([ ⁺ , 0 ] N5d ⟨ idᶜ ↦ unseal ⟩) ⟨ idᶜ ↦ idᶜ ⟩)
    ⟨ idᶜ ↦ idᶜ ⟩
      · $ nat 0
  —→⟨ wrap (V-fun (F-↦ (V-fun (F-↦ (V-fun F-ƛ))))) V-$ ⟩
    [ ⁺ , 0 ]
      ([ ⁻ , 0 ] ([ ⁺ , 0 ] N5d ⟨ idᶜ ↦ unseal ⟩) ⟨ idᶜ ↦ idᶜ ⟩
         · [ ⁻ , 0 ] $ nat 0 ⟨ idᶜ ⟩)
    ⟨ idᶜ ⟩
  —→⟨ ξ-[] (ξ-·₂ (V-fun (F-↦ (V-fun (F-↦ (V-fun F-ƛ))))) id-$) ⟩
    [ ⁺ , 0 ]
      ([ ⁻ , 0 ] ([ ⁺ , 0 ] N5d ⟨ idᶜ ↦ unseal ⟩) ⟨ idᶜ ↦ idᶜ ⟩ · $ nat 0)
    ⟨ idᶜ ⟩
  —→⟨ ξ-[] (wrap (V-fun (F-↦ (V-fun F-ƛ))) V-$) ⟩
    [ ⁺ , 0 ]
      ([ ⁻ , 0 ]
         ([ ⁺ , 0 ] N5d ⟨ idᶜ ↦ unseal ⟩ · [ ⁺ , 0 ] $ nat 0 ⟨ idᶜ ⟩)
       ⟨ idᶜ ⟩)
    ⟨ idᶜ ⟩
  —→⟨ ξ-[] (ξ-[] (ξ-·₂ (V-fun (F-↦ (V-fun F-ƛ))) id-$)) ⟩
    [ ⁺ , 0 ]
      ([ ⁻ , 0 ] ([ ⁺ , 0 ] N5d ⟨ idᶜ ↦ unseal ⟩ · $ nat 0) ⟨ idᶜ ⟩)
    ⟨ idᶜ ⟩
  —→⟨ ξ-[] (ξ-[] (wrap (V-fun F-ƛ) V-$)) ⟩
    [ ⁺ , 0 ]
      ([ ⁻ , 0 ]
         ([ ⁺ , 0 ] (N5d · [ ⁻ , 0 ] $ nat 0 ⟨ idᶜ ⟩) ⟨ unseal ⟩)
       ⟨ idᶜ ⟩)
    ⟨ idᶜ ⟩
  —→⟨ ξ-[] (ξ-[] (ξ-[] (ξ-·₂ (V-fun F-ƛ) id-$))) ⟩
    [ ⁺ , 0 ] ([ ⁻ , 0 ] ([ ⁺ , 0 ] (N5d · $ nat 0) ⟨ unseal ⟩) ⟨ idᶜ ⟩) ⟨ idᶜ ⟩
  —→⟨ ξ-[] (ξ-[] (ξ-[] (β-ƛ V-$))) ⟩
    [ ⁺ , 0 ] ([ ⁻ , 0 ] ([ ⁺ , 0 ] W5d ⟨ unseal ⟩) ⟨ idᶜ ⟩) ⟨ idᶜ ⟩
  —→⟨ ξ-[] (ξ-[] (cancel-□ V-$)) ⟩
    [ ⁺ , 0 ] ([ ⁻ , 0 ] $ nat 5 ⟨ idᶜ ⟩) ⟨ idᶜ ⟩
  —→⟨ ξ-[] id-$ ⟩
    [ ⁺ , 0 ] $ nat 5 ⟨ idᶜ ⟩
  —→⟨ id-$ ⟩
    $ nat 5
  ∎

------------------------------------------------------------------------
-- 5e
------------------------------------------------------------------------

-- ((ΛX. λf:(∀Y. Y → Y). f [X]) [Bool]
--    (ΛZ. (ΛW. λz:Z. z) [Bool])) false:
-- the argument passes through the reveal of W, so Swap, Sink and
-- Id clear its hide of W; then the hide of X and its re-reveal are
-- separated by that reveal, and Swap brings them together for
-- CancelId.  Push carries each unseal through the reveal of W.

-- λf:(∀Y. Y → Y). ν Y:=X. (f Y)⟨−Y → +Y⟩
F5e : Term
F5e = ƛ `∀ (` 0 ⇒ ` 0) ∙ ν (` 0) · ` 0 ⟨ seal ↦ unseal ⟩

-- λz:Z. z, under ΛW
I5e : Term
I5e = ƛ ` 1 ∙ ` 0

-- ΛZ. ν W:=Bool. ((ΛW. λz:Z. z) W)⟨id → id⟩
G5e : Term
G5e = Λ (ν `𝔹 · (Λ I5e) ⟨ idᶜ ↦ idᶜ ⟩)

ex5e : Term
ex5e = ν `𝔹 · (Λ F5e) ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ unseal) ⟩ · G5e · $ bool false

⊢ex5e : ∅ ∣ [] ⊢ ex5e ⦂ `𝔹
⊢ex5e =
  ⊢·
    (⊢·
       (⊢ν
          s-𝔹
          (⊢Λ
             (⊢ƛ
                (s-∀ (s-⇒ (s-var n-here) (s-var n-here)))
                (⊢ν
                   (s-var n-here)
                   (⊢` x-here)
                   (s-⇒ (s-var n-here) (s-var n-here))
                   (s-⇒ (s-var (n-hidden n-here)) (s-var (n-hidden n-here)))
                   (c-fun (c-seal p-here) (c-unseal p-here)))))
          (s-⇒
             (s-∀ (s-⇒ (s-var n-here) (s-var n-here)))
             (s-⇒ (s-var n-here) (s-var n-here)))
          (s-⇒ (s-∀ (s-⇒ (s-var n-here) (s-var n-here))) (s-⇒ s-𝔹 s-𝔹))
          (c-fun
             (c-all (c-fun c-id c-id))
             (c-fun (c-seal p-here) (c-unseal p-here))))
       (⊢Λ
          (⊢ν
             s-𝔹
             (⊢Λ (⊢ƛ (s-var (n-named n-here)) (⊢` x-here)))
             (s-⇒ (s-var (n-named n-here)) (s-var (n-named n-here)))
             (s-⇒ (s-var (n-hidden n-here)) (s-var (n-hidden n-here)))
             (c-fun c-id c-id))))
    ⊢bool

-- the context at the end of the run
Γ5e : Ctx
Γ5e = (pay `𝔹 ∷ pay (` 0) ∷ pay `𝔹 ∷ []) ∣ (false ∷ false ∷ false ∷ [])

run-5e : ∅ ⊢ ex5e —↠ $ bool false ⊣ Γ5e
run-5e =
    ν `𝔹 · (Λ F5e) ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ unseal) ⟩ · G5e · $ bool false
  —→⟨ ξ-·₁ (ξ-·₁ (tyβ s-𝔹 (V-fun F-Λ) inst-Λ)) ⟩
    [ ⁺ , 0 ] F5e ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ↦ (seal ↦ unseal) ⟩ · G5e · $ bool false
  —→⟨ ξ-·₁ (wrap (V-fun F-ƛ) (V-fun F-Λ)) ⟩
    [ ⁺ , 0 ] (F5e · [ ⁻ , 0 ] G5e ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ⟩) ⟨ seal ↦ unseal ⟩
      · $ bool false
  —→⟨ ξ-·₁ (ξ-[] (β-ƛ (V-fun (F-∀ (V-fun F-Λ))))) ⟩
    [ ⁺ , 0 ]
      (ν (` 0) · ([ ⁻ , 0 ] G5e ⟨ ∀ᶜ (idᶜ ↦ idᶜ) ⟩) ⟨ seal ↦ unseal ⟩)
    ⟨ seal ↦ unseal ⟩
      · $ bool false
  —→⟨ ξ-·₁
        (ξ-[] (tyβ (s-var n-here) (V-fun (F-∀ (V-fun F-Λ))) (inst-∀ inst-Λ))) ⟩
    [ ⁺ , 1 ]
      ([ ⁺ , 0 ]
         ([ ⁻ , 1 ] (ν `𝔹 · (Λ I5e) ⟨ idᶜ ↦ idᶜ ⟩) ⟨ idᶜ ↦ idᶜ ⟩)
       ⟨ seal ↦ unseal ⟩)
    ⟨ seal ↦ unseal ⟩
      · $ bool false
  —→⟨ ξ-·₁ (ξ-[] (ξ-[] (ξ-[] (tyβ s-𝔹 (V-fun F-Λ) inst-Λ)))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ] ([ ⁺ , 0 ] I5e ⟨ idᶜ ↦ idᶜ ⟩) ⟨ idᶜ ↦ idᶜ ⟩)
       ⟨ seal ↦ unseal ⟩)
    ⟨ seal ↦ unseal ⟩
      · $ bool false
  —→⟨ wrap (V-fun (F-↦ (V-fun (F-↦ (V-fun (F-↦ (V-fun F-ƛ))))))) V-$ ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ] ([ ⁺ , 0 ] I5e ⟨ idᶜ ↦ idᶜ ⟩) ⟨ idᶜ ↦ idᶜ ⟩)
       ⟨ seal ↦ unseal ⟩
         · [ ⁻ , 2 ] $ bool false ⟨ seal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[]
        (wrap (V-fun (F-↦ (V-fun (F-↦ (V-fun F-ƛ))))) (V-sealed (S-seal V-$))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ] ([ ⁺ , 0 ] I5e ⟨ idᶜ ↦ idᶜ ⟩) ⟨ idᶜ ↦ idᶜ ⟩
            · [ ⁻ , 1 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[]
        (ξ-[]
           (wrap
              (V-fun (F-↦ (V-fun F-ƛ)))
              (V-sealed (S-seal (V-sealed (S-seal V-$)))))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ]
            ([ ⁺ , 0 ] I5e ⟨ idᶜ ↦ idᶜ ⟩
               · [ ⁺ , 2 ]
                 ([ ⁻ , 1 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
               ⟨ idᶜ ⟩)
          ⟨ idᶜ ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[]
        (ξ-[]
           (ξ-[]
              (wrap
                 (V-fun F-ƛ)
                 (V-sealed (S-rev (S-seal (V-sealed (S-seal V-$)))))))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ]
            ([ ⁺ , 0 ]
               (I5e
                  · [ ⁻ , 0 ]
                    ([ ⁺ , 2 ]
                       ([ ⁻ , 1 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
                     ⟨ idᶜ ⟩)
                  ⟨ idᶜ ⟩)
             ⟨ idᶜ ⟩)
          ⟨ idᶜ ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[]
        (ξ-[]
           (ξ-[]
              (ξ-[]
                 (ξ-·₂
                    (V-fun F-ƛ)
                    (swap (λ ()) (S-seal (V-sealed (S-seal V-$)))))))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ]
            ([ ⁺ , 0 ]
               (I5e
                  · [ ⁺ , 2 ]
                    ([ ⁻ , 0 ]
                       ([ ⁻ , 1 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
                     ⟨ idᶜ ⟩)
                  ⟨ idᶜ ⟩)
             ⟨ idᶜ ⟩)
          ⟨ idᶜ ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[]
        (ξ-[]
           (ξ-[]
              (ξ-[]
                 (ξ-·₂
                    (V-fun F-ƛ)
                    (ξ-[] (sink (λ ()) (V-sealed (S-seal V-$)))))))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ]
            ([ ⁺ , 0 ]
               (I5e
                  · [ ⁺ , 2 ]
                    ([ ⁻ , 1 ]
                       ([ ⁻ , 0 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ idᶜ ⟩)
                     ⟨ seal ⟩)
                  ⟨ idᶜ ⟩)
             ⟨ idᶜ ⟩)
          ⟨ idᶜ ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[]
        (ξ-[]
           (ξ-[] (ξ-[] (ξ-·₂ (V-fun F-ƛ) (ξ-[] (ξ-[] (sink (λ ()) V-$))))))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ]
            ([ ⁺ , 0 ]
               (I5e
                  · [ ⁺ , 2 ]
                    ([ ⁻ , 1 ]
                       ([ ⁻ , 2 ] ([ ⁻ , 0 ] $ bool false ⟨ idᶜ ⟩) ⟨ seal ⟩)
                     ⟨ seal ⟩)
                  ⟨ idᶜ ⟩)
             ⟨ idᶜ ⟩)
          ⟨ idᶜ ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (ξ-[] (ξ-[] (ξ-·₂ (V-fun F-ƛ) (ξ-[] (ξ-[] (ξ-[] id-$))))))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ]
            ([ ⁺ , 0 ]
               (I5e
                  · [ ⁺ , 2 ]
                    ([ ⁻ , 1 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
                  ⟨ idᶜ ⟩)
             ⟨ idᶜ ⟩)
          ⟨ idᶜ ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[]
        (ξ-[]
           (ξ-[]
              (ξ-[]
                 (β-ƛ (V-sealed (S-rev (S-seal (V-sealed (S-seal V-$))))))))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁻ , 2 ]
            ([ ⁺ , 0 ]
               ([ ⁺ , 2 ]
                  ([ ⁻ , 1 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
                ⟨ idᶜ ⟩)
             ⟨ idᶜ ⟩)
          ⟨ idᶜ ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (swap (λ ()) (S-rev (S-seal (V-sealed (S-seal V-$)))))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁺ , 0 ]
            ([ ⁻ , 2 ]
               ([ ⁺ , 2 ]
                  ([ ⁻ , 1 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
                ⟨ idᶜ ⟩)
             ⟨ idᶜ ⟩)
          ⟨ idᶜ ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[]
        (ξ-[] (ξ-[] (cancel-id (V-sealed (S-seal (V-sealed (S-seal V-$))))))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 1 ]
         ([ ⁺ , 0 ]
            ([ ⁻ , 1 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
          ⟨ idᶜ ⟩)
       ⟨ unseal ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (push (S-seal (V-sealed (S-seal V-$)))) ⟩
    [ ⁺ , 2 ]
      ([ ⁺ , 0 ]
         ([ ⁺ , 1 ]
            ([ ⁻ , 1 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ seal ⟩)
          ⟨ unseal ⟩)
       ⟨ idᶜ ⟩)
    ⟨ unseal ⟩
  —→⟨ ξ-[] (ξ-[] (cancel-□ (V-sealed (S-seal V-$)))) ⟩
    [ ⁺ , 2 ] ([ ⁺ , 0 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ idᶜ ⟩) ⟨ unseal ⟩
  —→⟨ push (S-seal V-$) ⟩
    [ ⁺ , 0 ] ([ ⁺ , 2 ] ([ ⁻ , 2 ] $ bool false ⟨ seal ⟩) ⟨ unseal ⟩) ⟨ idᶜ ⟩
  —→⟨ ξ-[] (cancel-□ V-$) ⟩
    [ ⁺ , 0 ] $ bool false ⟨ idᶜ ⟩
  —→⟨ id-$ ⟩
    $ bool false
  ∎

------------------------------------------------------------------------
-- Every state of every run is typed, by preservation; the results:
------------------------------------------------------------------------

⊢result-5c : ((pay `𝔹 ∷ pay `ℕ ∷ []) ∣ (false ∷ false ∷ [])) ∣ []
             ⊢ $ nat 3 ⦂ `ℕ
⊢result-5c = preservation* ⊢ex5c run-5c

⊢result-5b : ((pay (` 0) ∷ pay `𝔹 ∷ []) ∣ (false ∷ false ∷ [])) ∣ []
             ⊢ $ bool false ⦂ `𝔹
⊢result-5b = preservation* ⊢ex5b run-5b

⊢result-5a : Γ5a ∣ [] ⊢ $ bool true ⦂ `𝔹
⊢result-5a = preservation* ⊢ex5a run-5a

⊢result-5d : Γ5d ∣ [] ⊢ $ nat 5 ⦂ `ℕ
⊢result-5d = preservation* ⊢ex5d run-5d

⊢result-5e : Γ5e ∣ [] ⊢ $ bool false ⦂ `𝔹
⊢result-5e = preservation* ⊢ex5e run-5e
