{-# OPTIONS --allow-unsolved-metas #-}

module proof.CompileTermNarrowing where

-- File Charter:
--   * Compile monotonicity for source-level gradual term narrowing.
--   * States that compiling two source terms related by
--     `GradualTermNarrowing` yields target terms related by `TermNarrowing`.
--   * The theorem is currently a proof boundary: the remaining hole isolates
--     the needed compile-commutation/cast-composition work.

open import Data.List using ([])
open import Data.Product using (proj₁)

open import Types
open import Ctx using (CtxWf)
open import Compile using (compile)
open import GradualTerms
  using (GTerm)
  renaming
    ( ⊢` to ⊢ᴳ`
    ; ⊢$ to ⊢ᴳ$
    )
open import NarrowWiden using (CtxNrw)
open import Coercions using (Coercion)

open import GradualTermNarrowing
  using
    ( _∣_∣_⊢ᴳ_⊒_∶_⦂_⊒_
    ; gradual-term-typing-endpoints
    ; x⊒xᴳ
    ; κ⊒κᴳ
    ; gradual-term-narrowing-source-typing
    ; gradual-term-narrowing-target-typing
    ; srcCtxⁿ
    ; tgtCtxⁿ
    )
open import TermNarrowing
  using
    ( _∣_∣_⊢_⊒_∶_⦂_⊒_
    ; x⊒xᵗ
    ; κ⊒κᵗ
    )

variable
  Δ : TyCtx
  γ : CtxNrw
  A B : Ty
  p : Coercion
  M M′ : GTerm

compile-preserves-term-narrowing :
  (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
  (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
  (M⊒M′ : Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B) →
  let
    M⊢ = gradual-term-narrowing-source-typing M⊒M′
    M′⊢ = gradual-term-narrowing-target-typing M⊒M′
    N = proj₁ (compile srcΓ-wf M⊢)
    N′ = proj₁ (compile tgtΓ-wf M′⊢)
  in
  Δ ∣ [] ∣ γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ B
compile-preserves-term-narrowing srcΓ-wf tgtΓ-wf
    (x⊒xᴳ {typing = gradual-term-typing-endpoints (⊢ᴳ` x∈ˢ) (⊢ᴳ` x∈ᵗ)}
      pᶜ x∋p) =
  x⊒xᵗ pᶜ x∋p
compile-preserves-term-narrowing srcΓ-wf tgtΓ-wf
    (κ⊒κᴳ κ {typing = gradual-term-typing-endpoints (⊢ᴳ$ .κ) (⊢ᴳ$ .κ)}) =
  κ⊒κᵗ κ
compile-preserves-term-narrowing srcΓ-wf tgtΓ-wf M⊒M′ =
  {!!}
