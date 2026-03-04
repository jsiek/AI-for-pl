import Lambda

namespace Lambda

/-- Call-by-name one-step reduction (left congruence + beta). -/
inductive CbnStep : Term → Term → Type where
  | xi_app1 : ∀ {L L' M}, CbnStep L L' → CbnStep (.app L M) (.app L' M)
  | β_lam : ∀ {N W}, CbnStep (.app (.lam N) W) (single_subst N W)

infix:20 " —→ₙ " => CbnStep

/-- Multi-step closure of call-by-name one-step reduction. -/
inductive CbnMultiStep : Term → Term → Type where
  | refl (M : Term) : CbnMultiStep M M
  | step (L : Term) {M N : Term} :
      CbnStep L M → CbnMultiStep M N → CbnMultiStep L N

infix:20 " —↠ₙ " => CbnMultiStep

def cbn_multi_trans {M N L : Term} :
  CbnMultiStep M N → CbnMultiStep N L → CbnMultiStep M L
  | .refl _, ms2 => ms2
  | .step _ s ms1', ms2 => .step _ s (cbn_multi_trans ms1' ms2)

def cbn_appL_cong {L L' M : Term} :
  CbnMultiStep L L' → CbnMultiStep (.app L M) (.app L' M)
  | .refl _ => .refl _
  | .step _ r rs => .step _ (.xi_app1 r) (cbn_appL_cong rs)

end Lambda
