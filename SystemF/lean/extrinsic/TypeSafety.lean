import extrinsic.Preservation

namespace Extrinsic

structure Safety (Δ : TyCtx) (M : Term) (A : Ty) : Type where
  progress_witness : Progress M
  preservation_step : ∀ {N : Term}, M —→ N → HasType Δ [] N A

noncomputable def typeSafety {Δ : TyCtx} {M : Term} {A : Ty} :
    HasType Δ [] M A → Safety Δ M A
  | hM => ⟨progress hM, fun s => preservation hM s⟩

noncomputable def typeSafety_multi {Δ : TyCtx} {M N : Term} {A : Ty} :
    HasType Δ [] M A → M —↠ N → HasType Δ [] N A :=
  multi_preservation

noncomputable def typeSafety_steps {Δ : TyCtx} {M : Term} {A : Ty} :
    HasType Δ [] M A →
    PProd (Progress M) (∀ {N : Term}, M —→ N → HasType Δ [] N A)
  | hM => ⟨progress hM, fun s => preservation hM s⟩

end Extrinsic
