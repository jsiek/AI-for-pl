import Lambda

namespace Congruence

open Lambda

def appL_cong {L L' M : Term} : MultiStep L L' → MultiStep (.app L M) (.app L' M)
  | .refl _ => .refl _
  | .step _ r rs => .step _ (.xi_app1 r) (appL_cong rs)

def appR_cong {L M M' : Term} : MultiStep M M' → MultiStep (.app L M) (.app L M')
  | .refl _ => .refl _
  | .step _ r rs => .step _ (.xi_app2 r) (appR_cong rs)

def app_cong {L L' M M' : Term} :
  MultiStep L L' → MultiStep M M' → MultiStep (.app L M) (.app L' M') :=
  fun hL hM => multi_trans (appL_cong hL) (appR_cong hM)

def lam_cong {N N' : Term} : MultiStep N N' → MultiStep (.lam N) (.lam N')
  | .refl _ => .refl _
  | .step _ r rs => .step _ (.xi_lam r) (lam_cong rs)

end Congruence
