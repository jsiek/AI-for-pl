module CBNBigStep where

open import Lambda
open import CBNReduction

------------------------------------------------------------------------
-- Big-step call-by-name evaluation
------------------------------------------------------------------------

infix 20 _⇓_

data _⇓_ : Term → Term → Set where
  ev-var : ∀ {i} → (′ i) ⇓ (′ i)
  ev-lam : ∀ {N} → (ƛ N) ⇓ (ƛ N)
  ev-app : ∀ {L M N V} → L ⇓ (ƛ N) → (N [ M ]) ⇓ V → (L · M) ⇓ V

eval-to-multistep : ∀ {M N}
  → M ⇓ N
    -------
  → M —↠ N
eval-to-multistep {M = ′ I} ev-var =
  let goal : (′ I) —↠ (′ I)
      goal = (′ I) ∎
  in goal
eval-to-multistep {M = ƛ N} ev-lam =
  let goal : (ƛ N) —↠ (ƛ N)
      goal = (ƛ N) ∎
  in goal
eval-to-multistep (ev-app {L} {M} {N} {V} HL HBODY) =
  let hL : L ⇓ (ƛ N)
      hL = HL

      hBody : (N [ M ]) ⇓ V
      hBody = HBODY
  in
    (L · M)
      —↠⟨ cbn-appL-cong (eval-to-multistep hL) ⟩
    ((ƛ N) · M)
      —→⟨ cbn-beta-lam ⟩
    N [ M ]
      —↠⟨ eval-to-multistep hBody ⟩
    V ∎

cbn-step-bigstep-value : ∀ {M N V}
  → M —→ N
  → N ⇓ V
  → Value V
    -------
  → M ⇓ V
cbn-step-bigstep-value {V = V} (cbn-xi-app1 {L} {L'} {M} S) (ev-app {N = N} HL HBODY) HVAL =
  let hStep : L —→ L'
      hStep = S

      hFun : L' ⇓ (ƛ N)
      hFun = HL

      hBody : (N [ M ]) ⇓ V
      hBody = HBODY

      hVal : Value V
      hVal = HVAL

      hRec : L ⇓ (ƛ N)
      hRec = cbn-step-bigstep-value hStep hFun v-lam

      goal : (L · M) ⇓ V
      goal = ev-app hRec hBody
  in goal
cbn-step-bigstep-value {V = V} (cbn-beta-lam {N = NB} {W = W}) HEV HVAL =
  let hEval : (NB [ W ]) ⇓ V
      hEval = HEV

      hVal : Value V
      hVal = HVAL

      goal : ((ƛ NB) · W) ⇓ V
      goal = ev-app ev-lam hEval
  in goal

eval-value : ∀ {M V} → M ⇓ V → Value V
eval-value ev-var = v-var
eval-value ev-lam = v-lam
eval-value (ev-app _ HBODY) = eval-value HBODY

value-eval : ∀ {V} → Value V → V ⇓ V
value-eval v-var = ev-var
value-eval v-lam = ev-lam

cbn-multistep-bigstep : ∀ {M N V} → M —↠ N → N ⇓ V → M ⇓ V
cbn-multistep-bigstep {M = M} {V = V} (cbn-refl _) HEV =
  let goal : M ⇓ V
      goal = HEV
  in goal
cbn-multistep-bigstep {V = V} (cbn-step M {M = M'} S MS) HEV =
  let hmid : M' ⇓ V
      hmid = cbn-multistep-bigstep MS HEV

      goal : M ⇓ V
      goal = cbn-step-bigstep-value S hmid (eval-value hmid)
  in goal

cbn-multistep-to-value-bigstep : ∀ {M V} → M —↠ V → Value V → M ⇓ V
cbn-multistep-to-value-bigstep {M = M} {V = V} HSTEPS HVAL =
  let hSteps : M —↠ V
      hSteps = HSTEPS

      hVal : Value V
      hVal = HVAL

      hEvalV : V ⇓ V
      hEvalV = value-eval hVal

      goal : M ⇓ V
      goal = cbn-multistep-bigstep hSteps hEvalV
  in goal
