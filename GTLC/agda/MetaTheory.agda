module MetaTheory where

-- File Charter:
--   * Public metatheory statements/wrappers for GTLC.
--   * Exposes type safety (via compilation) and both gradual guarantees.

open import Agda.Builtin.List using ([])
open import Data.Product using (∃; ∃-syntax; _×_)
open import Data.Sum using (_⊎_)

open import Types
open import Contexts
open import GTLC
open import CastCalculus
open import Compile using (compile)
open import Contexts public using (_⊑ˢ_)
open import DynamicGradualGuaranteeDefinitions public

import proof.CastSafety as CastSafetyProof
import proof.TypeSafety as TypeSafetyProof
import proof.StaticGradualGuarantee as StaticGGProof
import proof.DynamicGradualGuarantee as DynamicGGProof

cast-type-safety
  : {M N : Termᶜ} {A : Ty}
  → [] ⊢ᶜ M ⦂ A
  → M —↠ᶜ N
  → (∃[ N′ ] (N —→ᶜ N′)) ⊎ Result N
cast-type-safety = CastSafetyProof.type-safetyᶜ

type-safety
  : {M : Term} {A : Ty} {N : Termᶜ}
  → (M⦂A : [] ⊢ M ⦂ A)
  → compile M⦂A —↠ᶜ N
  → (∃[ N′ ] (N —→ᶜ N′)) ⊎ Result N
type-safety = TypeSafetyProof.type-safety

static-gradual-guarantee
  : ∀ {Γ Γ′ M M′ A}
  → Γ ⊢ M ⦂ A
  → M′ ⊑ᵀ M
  → Γ ⊑ˢ Γ′
  → ∃[ A′ ] (Γ′ ⊢ M′ ⦂ A′) × (A′ ⊑ A)
static-gradual-guarantee = StaticGGProof.static-gradual-guarantee

dynamic-gradual-guarantee : ∀ {M M′} {A A′}
  → M ⊑ᵀ M′
  → [] ⊢ M ⦂ A
  → [] ⊢ M′ ⦂ A′
  → (∀ V′ → Valueᶜ V′
          → M′ ⇓ V′
          → ∃[ V ] Valueᶜ V × M ⇓ V
            × []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′)
    × (Diverges M′ → Diverges M)
    × (∀ V → Valueᶜ V
           → M ⇓ V
           → (∃[ V′ ] Valueᶜ V′ × M′ ⇓ V′
              × []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′)
             ⊎ Blames M′)
    × (Diverges M → DivergeOrBlame M′)
dynamic-gradual-guarantee = DynamicGGProof.dynamic-gradual-guarantee
