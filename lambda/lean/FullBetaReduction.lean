import Lambda

namespace Lambda

-------------------------------------------------------------------------------
-- 1. NEUTRAL & NORMAL TERMS
-------------------------------------------------------------------------------

mutual

inductive Neutral : Term → Type where
  | var : ∀ {i}, Neutral (.var i)
  | app : ∀ {L M}, Neutral L → Normal M → Neutral (.app L M)

inductive Normal : Term → Type where
  | neu : ∀ {M}, Neutral M → Normal M
  | lam : ∀ {N}, Normal N → Normal (.lam N)

end

-------------------------------------------------------------------------------
-- 2. FULL-BETA REDUCTION
-------------------------------------------------------------------------------

inductive Step : Term → Term → Type where
  | xi_lam : ∀ {N N'}, Step N N' → Step (.lam N) (.lam N')
  | xi_app1 : ∀ {L L' M}, Step L L' → Step (.app L M) (.app L' M)
  | xi_app2 : ∀ {L M M'}, Step M M' → Step (.app L M) (.app L M')
  | β_lam : ∀ {N W}, Step (.app (.lam N) W) (single_subst N W)

infix:20 " —→ " => Step

-------------------------------------------------------------------------------
-- 3. MULTI-STEP REDUCTION
-------------------------------------------------------------------------------

inductive MultiStep : Term → Term → Type where
  | refl (M : Term) : MultiStep M M
  | step (L : Term) {M N : Term} : Step L M → MultiStep M N → MultiStep L N

infix:20 " —↠ " => MultiStep

postfix:max " ∎" => MultiStep.refl
notation:2 L " —→⟨ " s " ⟩ " ms => MultiStep.step L s ms
notation:1 "begin " ms => ms

def multi_trans {M N L : Term} : (M —↠ N) → (N —↠ L) → (M —↠ L)
  | .refl _, ms2 => ms2
  | .step _ s ms1', ms2 => .step _ s (multi_trans ms1' ms2)

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

end Lambda
