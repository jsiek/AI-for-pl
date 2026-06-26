module proof.TermNarrowingProperties where

-- File Charter:
--   * Admissible rules and structural lemmas for term narrowing.
--   * Currently provides the two cambridge23 two-sided cast derived rules.
--   * Depends on the public definitions in `TermNarrowing` and `NarrowWiden`.

open import Types
open import Coercions
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing using
  (_∣_∣_⊢_⊒_∶_; ⊒cast+; ⊒cast-; cast+⊒; cast-⊒)

variable
  Δ : TyCtx
  σ : StoreNrw
  γ : CtxNrw
  A B : Ty
  p q r s t : Coercion
  M M′ : Term

------------------------------------------------------------------------
-- Derived cast rules
------------------------------------------------------------------------

-- cambridge23 states these with the side condition `q ⨾ s ≈ t ⨾ p`.
-- This formalization exposes the intermediate coercion `r`, matching the
-- displayed derivations and avoiding a dependency on general transitivity for
-- coercion equivalence.
-- The compact one-premise version should be derivable once coercion
-- equivalence has enough transitivity/reflexivity infrastructure to bridge
-- `q ⨾ s ≈ r` and `r ≈ t ⨾ p` from `q ⨾ s ≈ t ⨾ p`.

cast-⊒cast- : ∀ {M M′ p q r s t A B}
  → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
  → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
  → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q
    --------------------------------------
  → Δ ∣ σ ∣ γ ⊢ M ⟨ t ⟩ ⊒ M′ ⟨ s ⟩ ∶ p
cast-⊒cast- {p = p} {q = q} {r = r} {s = s} {t = t}
    q⨟s≈r r≈t⨟p M⊒M′ =
  cast-⊒ {p = p} {r = r} {t = t} r≈t⨟p
    (⊒cast- {q = q} {r = r} {s = s} q⨟s≈r M⊒M′)

cast+⊒cast+ : ∀ {M M′ p q r s t A B}
  → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
  → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
  → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p
    ------------------------------------------
  → Δ ∣ σ ∣ γ ⊢ M ⟨ - t ⟩ ⊒ M′ ⟨ - s ⟩ ∶ q
cast+⊒cast+ {p = p} {q = q} {r = r} {s = s} {t = t}
    q⨟s≈r r≈t⨟p M⊒M′ =
  ⊒cast+ {q = q} {r = r} {s = s} q⨟s≈r
    (cast+⊒ {p = p} {r = r} {t = t} r≈t⨟p M⊒M′)
