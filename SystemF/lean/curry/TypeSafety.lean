import curry.Preservation

-- File Charter:
--   * Packages progress and preservation into a closed-term safety interface.
--   * Exposes one-step and multi-step type safety corollaries.
--   * Keeps type-safety wrappers lightweight over existing proofs.

namespace Curry

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

end Curry
