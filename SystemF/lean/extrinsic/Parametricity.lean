import extrinsic.LogicalRelation

namespace Extrinsic

axiom compat_app :
  ∀ {Γ A B} (L M : Term),
    LogicalRel Γ (.fn A B) L L →
    LogicalRel Γ A M M →
    LogicalRel Γ B (.app L M) (.app L M)

axiom compat_true :
  ∀ {Γ}, LogicalRel Γ .bool .ttrue .ttrue

axiom compat_suc :
  ∀ {Γ} (M : Term),
    LogicalRel Γ .nat M M →
    LogicalRel Γ .nat (.suc M) (.suc M)

axiom compat_case :
  ∀ {Γ A} (L M N : Term),
    LogicalRel Γ .nat L L →
    LogicalRel Γ A M M →
    LogicalRel (.nat :: Γ) A N N →
    LogicalRel Γ A (.natCase L M N) (.natCase L M N)

axiom compat_zero :
  ∀ {Γ}, LogicalRel Γ .nat .zero .zero

axiom compat_lam :
  ∀ {Γ A B} (N : Term),
    LogicalRel (A :: Γ) B N N →
    LogicalRel Γ (.fn A B) (.lam N) (.lam N)

axiom compat_false :
  ∀ {Γ}, LogicalRel Γ .bool .tfalse .tfalse

axiom compat_if :
  ∀ {Γ A} (L M N : Term),
    LogicalRel Γ .bool L L →
    LogicalRel Γ A M M →
    LogicalRel Γ A N N →
    LogicalRel Γ A (.ite L M N) (.ite L M N)

axiom compat_var :
  ∀ {Γ A x},
    HasTypeVar Γ x A →
    LogicalRel Γ A (.var x) (.var x)

axiom compat_tapp :
  ∀ {Γ A B} (M : Term),
    LogicalRel Γ (.all A) M M →
    LogicalRel Γ (substOneT A B) (.tapp M) (.tapp M)

axiom compat_tlam :
  ∀ {Γ A} (N : Term),
    LogicalRel (liftCtx Γ) A N N →
    LogicalRel Γ (.all A) (.tlam N) (.tlam N)

axiom fundamental :
  ∀ {Δ Γ A} (M : Term),
    HasType Δ Γ M A →
    LogicalRel Γ A M M

end Extrinsic
