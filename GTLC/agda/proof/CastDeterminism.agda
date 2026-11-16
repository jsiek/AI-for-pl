module proof.CastDeterminism where

-- File Charter:
--   * Determinism of the cast calculus's one-step reduction, and its
--     consequence that a term reduces to at most one value.
--   * Used by denotational adequacy (proof/DenotAdequacy.agda) to give all
--     the elements of an argument set one common syntactic value.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong)

open import Coercions
open import CastCalculus

—→-deterministic : ∀ {M N N′} → M —→ N → M —→ N′ → N ≡ N′
-- operator position
—→-deterministic (ξ (□· M) s) (ξ (□· .M) s′) =
  cong (_· M) (—→-deterministic s s′)
—→-deterministic (ξ (□· M) s) (ξ (V ·□ vV) s′) =
  ⊥-elim (value-irreducible vV s)
—→-deterministic (ξ (□· M) s) (β-ƛ vV) = ⊥-elim (value-irreducible V-ƛ s)
—→-deterministic (ξ (□· M) s) (β-↦ vV vW) =
  ⊥-elim (value-irreducible (V-cast↦ vV) s)
—→-deterministic (ξ (□· M) s) (ξ-blame (□· .M)) =
  ⊥-elim (blame-irreducible s)
—→-deterministic (ξ (□· M) s) (ξ-blame (V ·□ vV)) =
  ⊥-elim (value-irreducible vV s)
-- argument position
—→-deterministic (ξ (V ·□ vV) s) (ξ (□· M) s′) =
  ⊥-elim (value-irreducible vV s′)
—→-deterministic (ξ (V ·□ vV) s) (ξ (.V ·□ vV′) s′) =
  cong (V ·_) (—→-deterministic s s′)
—→-deterministic (ξ (V ·□ vV) s) (β-ƛ vW) = ⊥-elim (value-irreducible vW s)
—→-deterministic (ξ (V ·□ vV) s) (β-↦ vV′ vW) =
  ⊥-elim (value-irreducible vW s)
—→-deterministic (ξ (V ·□ ()) s) (ξ-blame (□· M))
—→-deterministic (ξ (V ·□ vV) s) (ξ-blame (.V ·□ vV′)) =
  ⊥-elim (blame-irreducible s)
-- cast position
—→-deterministic (ξ cast□[ c ] s) (ξ cast□[ .c ] s′) =
  cong (cast_[ c ]) (—→-deterministic s s′)
—→-deterministic (ξ cast□[ c ] s) (β-id vV) = ⊥-elim (value-irreducible vV s)
—→-deterministic (ξ cast□[ c ] s) (β-seq vV) =
  ⊥-elim (value-irreducible vV s)
—→-deterministic (ξ cast□[ c ] s) (β-⊥ vV) = ⊥-elim (value-irreducible vV s)
—→-deterministic (ξ cast□[ c ] s) (β-proj-inj-ok vV) =
  ⊥-elim (value-irreducible (V-cast! vV) s)
—→-deterministic (ξ cast□[ c ] s) (β-proj-inj-bad vV G≢H) =
  ⊥-elim (value-irreducible (V-cast! vV) s)
—→-deterministic (ξ cast□[ c ] s) (ξ-blame cast□[ .c ]) =
  ⊥-elim (blame-irreducible s)
-- β-ƛ
—→-deterministic (β-ƛ vV) (ξ (□· M) s′) = ⊥-elim (value-irreducible V-ƛ s′)
—→-deterministic (β-ƛ vV) (ξ (V ·□ vV′) s′) =
  ⊥-elim (value-irreducible vV s′)
—→-deterministic (β-ƛ vV) (β-ƛ vV′) = refl
—→-deterministic (β-ƛ ()) (ξ-blame (V ·□ vV′))
-- β-id
—→-deterministic (β-id vV) (ξ cast□[ c ] s′) =
  ⊥-elim (value-irreducible vV s′)
—→-deterministic (β-id vV) (β-id vV′) = refl
—→-deterministic (β-id ()) (ξ-blame cast□[ c ])
-- β-seq
—→-deterministic (β-seq vV) (ξ cast□[ c ] s′) =
  ⊥-elim (value-irreducible vV s′)
—→-deterministic (β-seq vV) (β-seq vV′) = refl
—→-deterministic (β-seq ()) (ξ-blame cast□[ c ])
-- β-↦
—→-deterministic (β-↦ vV vW) (ξ (□· M) s′) =
  ⊥-elim (value-irreducible (V-cast↦ vV) s′)
—→-deterministic (β-↦ vV vW) (ξ (V ·□ vV′) s′) =
  ⊥-elim (value-irreducible vW s′)
—→-deterministic (β-↦ vV vW) (β-↦ vV′ vW′) = refl
—→-deterministic (β-↦ vV ()) (ξ-blame (V ·□ vV′))
-- β-⊥
—→-deterministic (β-⊥ vV) (ξ cast□[ c ] s′) =
  ⊥-elim (value-irreducible vV s′)
—→-deterministic (β-⊥ vV) (β-⊥ vV′) = refl
—→-deterministic (β-⊥ ()) (ξ-blame cast□[ c ])
-- β-proj-inj-ok
—→-deterministic (β-proj-inj-ok vV) (ξ cast□[ c ] s′) =
  ⊥-elim (value-irreducible (V-cast! vV) s′)
—→-deterministic (β-proj-inj-ok vV) (β-proj-inj-ok vV′) = refl
—→-deterministic (β-proj-inj-ok vV) (β-proj-inj-bad vV′ G≢G) =
  ⊥-elim (G≢G refl)
—→-deterministic (β-proj-inj-ok vV) (ξξ-blame {F = □· M} ())
—→-deterministic (β-proj-inj-ok vV) (ξξ-blame {F = W ·□ vW} ())
—→-deterministic (β-proj-inj-ok vV) (ξξ-blame {F = cast□[ c ]} ())
-- β-proj-inj-bad
—→-deterministic (β-proj-inj-bad vV G≢H) (ξ cast□[ c ] s′) =
  ⊥-elim (value-irreducible (V-cast! vV) s′)
—→-deterministic (β-proj-inj-bad vV G≢G) (β-proj-inj-ok vV′) =
  ⊥-elim (G≢G refl)
—→-deterministic (β-proj-inj-bad vV G≢H) (β-proj-inj-bad vV′ G≢H′) = refl
—→-deterministic (β-proj-inj-bad vV G≢H) (ξξ-blame {F = □· M} ())
—→-deterministic (β-proj-inj-bad vV G≢H) (ξξ-blame {F = W ·□ vW} ())
—→-deterministic (β-proj-inj-bad vV G≢H) (ξξ-blame {F = cast□[ c ]} ())
-- ξ-blame
—→-deterministic (ξ-blame (□· M)) (ξ (□· .M) s′) =
  ⊥-elim (blame-irreducible s′)
—→-deterministic (ξ-blame (□· M)) (ξ (V ·□ ()) s′)
—→-deterministic (ξ-blame (□· M)) (ξ-blame (□· .M)) = refl
—→-deterministic (ξ-blame (□· M)) (ξ-blame (V ·□ ()))
—→-deterministic (ξ-blame (V ·□ vV)) (ξ (□· M) s′) =
  ⊥-elim (value-irreducible vV s′)
—→-deterministic (ξ-blame (V ·□ vV)) (ξ (.V ·□ vV′) s′) =
  ⊥-elim (blame-irreducible s′)
—→-deterministic (ξ-blame (V ·□ vV)) (β-ƛ ())
—→-deterministic (ξ-blame (V ·□ vV)) (β-↦ vV′ ())
—→-deterministic (ξ-blame (V ·□ ())) (ξ-blame (□· M))
—→-deterministic (ξ-blame (V ·□ vV)) (ξ-blame (.V ·□ vV′)) = refl
—→-deterministic (ξ-blame cast□[ c ]) (ξ cast□[ .c ] s′) =
  ⊥-elim (blame-irreducible s′)
—→-deterministic (ξ-blame cast□[ c ]) (β-id ())
—→-deterministic (ξ-blame cast□[ c ]) (β-seq ())
—→-deterministic (ξ-blame cast□[ c ]) (β-⊥ ())
—→-deterministic (ξ-blame cast□[ c ]) (ξ-blame cast□[ .c ]) = refl

—↠-value-unique : ∀ {M V W}
  → Valueᶜ V
  → Valueᶜ W
  → M —↠ V
  → M —↠ W
  → V ≡ W
—↠-value-unique vV vW (_ ∎) (_ ∎) = refl
—↠-value-unique vV vW (_ ∎) (_ —→⟨ s′ ⟩ r′) =
  ⊥-elim (value-irreducible vV s′)
—↠-value-unique vV vW (_ —→⟨ s ⟩ r) (_ ∎) =
  ⊥-elim (value-irreducible vW s)
—↠-value-unique vV vW (_ —→⟨ s ⟩ r) (_ —→⟨ s′ ⟩ r′)
  with —→-deterministic s s′
—↠-value-unique vV vW (_ —→⟨ s ⟩ r) (_ —→⟨ s′ ⟩ r′)
  | refl = —↠-value-unique vV vW r r′
