module proof.DGG.CtxWeaken where

-- File Charter:
--   * WEAKENING BY TERM VARIABLES AT THE END OF THE CONTEXT:
--     `Δ ∣ Γ ⊢ M ⦂ A → Δ ∣ Γ ++ Γ′ ⊢ M ⦂ A`.  Appending at the end moves
--     no de Bruijn index, so the term is unchanged; under `Λ` the
--     appended part is shifted with the rest (`map-++`).
--   * Corollary `⊢closed`: a typing at the empty term context holds at
--     every term context.  Used by ImprecisionTypingProof for the
--     one-sided boundary rules, whose premise types a term-closed
--     interior at `[]` (TermImprecision's charter).

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Types using (Ty; ⇑ᵗ)
open import Ctx using (Ctxᵗ)
open import Terms

∋-++ : ∀ {Γ Γ′ x A} → Γ ∋ x ⦂ A → (Γ ++ Γ′) ∋ x ⦂ A
∋-++ here      = here
∋-++ (there x) = there (∋-++ x)

⊢-++ : ∀ {Δ Γ Γ′ M A} → Δ ∣ Γ ⊢ M ⦂ A → Δ ∣ Γ ++ Γ′ ⊢ M ⦂ A
⊢-++ (⊢` x) = ⊢` (∋-++ x)
⊢-++ ⊢$ = ⊢$
⊢-++ ⊢true = ⊢true
⊢-++ ⊢false = ⊢false
⊢-++ (⊢ƛ wA ⊢N) = ⊢ƛ wA (⊢-++ ⊢N)
⊢-++ (⊢· ⊢L ⊢M) = ⊢· (⊢-++ ⊢L) (⊢-++ ⊢M)
⊢-++ {Δ} {Γ} {Γ′} (⊢Λ {C = C} {N = N} v ⊢N) =
  ⊢Λ v (subst (λ Γ₀ → _ ∣ Γ₀ ⊢ N ⦂ C) (sym (map-++ ⇑ᵗ Γ Γ′))
              (⊢-++ {Γ′ = map ⇑ᵗ Γ′} ⊢N))
⊢-++ (⊢ν wA rA ⊢L mw ⊢c eq wB) = ⊢ν wA rA (⊢-++ ⊢L) mw ⊢c eq wB
⊢-++ (boundary mw ⊢M ⊢c eqᵢ eqₑ wB) = boundary mw ⊢M ⊢c eqᵢ eqₑ wB
⊢-++ (⊢cast ⊢M ⊢p len) = ⊢cast (⊢-++ ⊢M) ⊢p len
⊢-++ (⊢blame wA) = ⊢blame wA

⊢closed : ∀ {Δ Γ M A} → Δ ∣ [] ⊢ M ⦂ A → Δ ∣ Γ ⊢ M ⦂ A
⊢closed = ⊢-++
