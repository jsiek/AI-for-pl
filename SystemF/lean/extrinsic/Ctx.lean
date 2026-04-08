import extrinsic.Types

namespace Extrinsic

-- File Charter:
--   * Context-level utilities for extrinsic System F.
--   * Contains lookup lemmas for mapped contexts.
--   * Defines context well-formedness helpers used across metatheory files.

def lookup_map_renameT :
  ∀ {Γ x A ρ},
    HasTypeVar Γ x A →
    HasTypeVar (List.map (renameT ρ) Γ) x (renameT ρ A)
  | _, _, _, _, .Z => .Z
  | _, _, _, _, .S h => .S (lookup_map_renameT h)

def lookup_map_substT :
  ∀ {Γ x A σ},
    HasTypeVar Γ x A →
    HasTypeVar (List.map (substT σ) Γ) x (substT σ A)
  | _, _, _, _, .Z => .Z
  | _, _, _, _, .S h => .S (lookup_map_substT h)

def lookup_map_inv :
  ∀ {Γ x B f},
    HasTypeVar (List.map f Γ) x B →
    Σ A, { hA : HasTypeVar Γ x A // B = f A }
  | [], _, _, _, h => by
      cases h
  | A :: Γ, 0, _, _, .Z =>
      ⟨A, ⟨.Z, rfl⟩⟩
  | A :: Γ, x + 1, B, f, .S h => by
      rcases lookup_map_inv (Γ := Γ) (x := x) (B := B) (f := f) h with ⟨A', ⟨hA', hEq⟩⟩
      exact ⟨A', ⟨.S hA', hEq⟩⟩

def CtxWf (Δ : TyCtx) (Γ : Ctx) : Type :=
  ∀ {x A}, HasTypeVar Γ x A → WfTy Δ A

def ctxWf_nil {Δ : TyCtx} : CtxWf Δ [] := by
  intro x A h
  cases h

def ctxWf_cons {Δ : TyCtx} {Γ : Ctx} {A : Ty}
    (hA : WfTy Δ A) (hΓ : CtxWf Δ Γ) : CtxWf Δ (A :: Γ) := by
  intro x B hx
  cases hx with
  | Z =>
      exact hA
  | S hx' =>
      exact hΓ hx'

end Extrinsic
