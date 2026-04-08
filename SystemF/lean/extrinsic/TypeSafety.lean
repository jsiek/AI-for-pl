import extrinsic.Preservation

namespace Extrinsic

-- File Charter:
--   * Closed-term type safety wrapper for extrinsic System F.
--   * Packages `progress` and `preservation` into a single `Safety` witness.
--   * Re-exports multi-step preservation utilities for convenient use.

structure Safety (Δ : TyCtx) (M : Term) (A : Ty) : Type where
  progress_witness : Progress M
  preservation_step : ∀ {N : Term}, M —→ N → Δ ⊢ [] ⊢ N ⦂ A

noncomputable def typeSafety {Δ : TyCtx} {M : Term} {A : Ty} :
    Δ ⊢ [] ⊢ M ⦂ A → Safety Δ M A
  | hM => ⟨progress hM, fun s => preservation hM s⟩

noncomputable def typeSafety_multi {Δ : TyCtx} {M N : Term} {A : Ty} :
    Δ ⊢ [] ⊢ M ⦂ A → M —↠ N → Δ ⊢ [] ⊢ N ⦂ A :=
  multi_preservation

noncomputable def typeSafety_steps {Δ : TyCtx} {M : Term} {A : Ty} :
    Δ ⊢ [] ⊢ M ⦂ A →
    PProd (Progress M) (∀ {N : Term}, M —→ N → Δ ⊢ [] ⊢ N ⦂ A)
  | hM => ⟨progress hM, fun s => preservation hM s⟩

end Extrinsic
