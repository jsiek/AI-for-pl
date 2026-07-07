module proof.DGGBetaMediated where

-- File Charter:
--   * Mediated-store DGG helpers for application beta steps.
--   * Packages source function/argument catchup with sim-betaᵐ.
--   * Exported by proof.DynamicGradualGuaranteeMediated for the main DGG.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyLeftChanges-++
  )
open import proof.CatchupMediated using (catchup-lemmaᵐ)
open import proof.MediatedLeftInsertion using
  (left-changes-term-narrowingᵐ)
open import proof.MediationProperties using
  ( left-changes-transportᵐ
  ; fun-narrow-domain-dualᵐ-determined
  )
open import proof.LeftChangeNarrowingSeparated using
  ( applyTerms-preserves-RuntimeOK
  ; applyTys-⇒
  )
open import proof.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyTyCtxs-++
  ; applyTys-++
  ; ·₁-↠
  ; ·₂-↠
  ; ↠-trans
  )
open import proof.SimBetaMediated using (sim-betaᵐ)

------------------------------------------------------------------------
-- Application beta packaging
------------------------------------------------------------------------

mediated-dgg-beta-left-first :
  ∀ {ΔL ΔR ρ L R N′ V′ p q A A′ B B′} →
  RuntimeOK L →
  RuntimeOK R →
  No• R →
  Value V′ →
  (p↦qᶜ :
    ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
      ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-left-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {N′ = N′} {V′ = V′}
    {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    okL okR noR-ready vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  let
    χsL , WL , ΔL₁ ,
      vWL , noWL , L↠WL , ΔL₁≡ , ρL-corr ,
      leftL≡ , rightL≡ , pLᶜ , WL⊒ƛraw =
      catchup-lemmaᵐ okL (ƛ N′) L⊒ƛ

    corrL :
      StoreCorr (applyTyCtxs χsL ΔL) ΔR (applyLeftChanges χsL ρ)
    corrL =
      subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χsL ρ))
        ΔL₁≡
        ρL-corr

    WL⊒ƛ :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ WL ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ᵐ A′ ⇒ B′
    WL⊒ƛ =
      subst
        (λ C →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ WL ⊒ ƛ N′ ∶ p ↦ q ⦂ C ⊒ᵐ A′ ⇒ B′)
        (applyTys-⇒ χsL A B)
        WL⊒ƛraw

    p↦qᶜL :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ
        ⊢ p ↦ q ∶ᶜ applyTys χsL A ⇒ applyTys χsL B
          ⊒ᵐ A′ ⇒ B′
    p↦qᶜL =
      subst
        (λ C →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ
            ⊢ p ↦ q ∶ᶜ C ⊒ᵐ A′ ⇒ B′)
        (applyTys-⇒ χsL A B)
        pLᶜ

    R⊒V′L :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ applyTerms χsL R ⊒ V′
          ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
            ⦂ applyTys χsL A ⊒ᵐ A′
    R⊒V′L =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ applyTerms χsL R ⊒ V′
              ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
                ⦂ applyTys χsL A ⊒ᵐ A′)
        (sym ΔL₁≡)
        (left-changes-term-narrowingᵐ χsL corrL R⊒V′)

    χsR , WR , ΔL₂ ,
      vWR , noWR , R↠WR , ΔL₂≡ , ρR-corr ,
      leftR≡ , rightR≡ , pRᶜ , WR⊒V′raw =
      catchup-lemmaᵐ
        (applyTerms-preserves-RuntimeOK χsL okR)
        vV′
        R⊒V′L

    ρLR = applyLeftChanges χsR (applyLeftChanges χsL ρ)

    corrR :
      StoreCorr (applyTyCtxs χsR ΔL₁) ΔR ρLR
    corrR =
      subst (λ Δ → StoreCorr Δ ΔR ρLR) ΔL₂≡ ρR-corr

    WLF⊒ƛraw :
      applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR ∣ []
        ⊢ applyTerms χsR WL ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsR (applyTys χsL A ⇒ applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    WLF⊒ƛraw = left-changes-term-narrowingᵐ χsR corrR WL⊒ƛ

    WLF⊒ƛ :
      ΔL₂ ∣ ΔR ∣ ρLR ∣ []
        ⊢ applyTerms χsR WL ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsR (applyTys χsL A)
              ⇒ applyTys χsR (applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    WLF⊒ƛ =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρLR ∣ []
            ⊢ applyTerms χsR WL ⊒ ƛ N′ ∶ p ↦ q
              ⦂ applyTys χsR (applyTys χsL A)
                  ⇒ applyTys χsR (applyTys χsL B)
                ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₂≡)
        (subst
          (λ C →
            applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR ∣ []
              ⊢ applyTerms χsR WL ⊒ ƛ N′ ∶ p ↦ q
                ⦂ C ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR (applyTys χsL A) (applyTys χsL B))
          WLF⊒ƛraw)

    p↦qᶜLRraw :
      applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR
        ⊢ p ↦ q
          ∶ᶜ applyTys χsR (applyTys χsL A ⇒ applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    p↦qᶜLRraw = left-changes-transportᵐ χsR corrR p↦qᶜL

    p↦qᶜLR :
      ΔL₂ ∣ ΔR ∣ ρLR
        ⊢ p ↦ q
          ∶ᶜ applyTys χsR (applyTys χsL A)
              ⇒ applyTys χsR (applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    p↦qᶜLR =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρLR ⊢ p ↦ q
            ∶ᶜ applyTys χsR (applyTys χsL A)
                ⇒ applyTys χsR (applyTys χsL B)
              ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₂≡)
        (subst
          (λ C →
            applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR
              ⊢ p ↦ q ∶ᶜ C ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR (applyTys χsL A) (applyTys χsL B))
          p↦qᶜLRraw)

    pd-eq :
      fun-narrow-domain-dualᵐᶜ p↦qᶜLR
        ≡ fun-narrow-domain-dualᵐᶜ p↦qᶜ
    pd-eq = fun-narrow-domain-dualᵐ-determined p↦qᶜLR p↦qᶜ

    WR⊒V′ :
      ΔL₂ ∣ ΔR ∣ ρLR ∣ []
        ⊢ WR ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜLR
          ⦂ applyTys χsR (applyTys χsL A) ⊒ᵐ A′
    WR⊒V′ =
      subst
        (λ pd →
          ΔL₂ ∣ ΔR ∣ ρLR ∣ []
            ⊢ WR ⊒ V′ ∶ pd
              ⦂ applyTys χsR (applyTys χsL A) ⊒ᵐ A′)
        (sym pd-eq)
        WR⊒V′raw

    left-ready :
      L · R —↠[ χsL ] WL · applyTerms χsL R
    left-ready = ·₁-↠ noR-ready L↠WL

    right-ready :
      WL · applyTerms χsL R —↠[ χsR ] applyTerms χsR WL · WR
    right-ready = ·₂-↠ vWL noWL R↠WR

    tail =
      sim-betaᵐ
        WLF⊒ƛ
        (applyTerms-preserves-Value χsR vWL)
        (applyTerms-preserves-No• χsR noWL)
        p↦qᶜLR
        (fun-narrow-domain-dual-typingᵐᶜ p↦qᶜLR)
        WR⊒V′
        vWR
        noWR
        vV′
  in
  let
    χsT , N , ΔL′ , ρ′ ,
      tail-red , ΔT≡ , ρT≡ , N⊒N′[V′] = tail

    source-steps :
      L · R —↠[ (χsL ++ χsR) ++ χsT ] N
    source-steps = ↠-trans (↠-trans left-ready right-ready) tail-red

    ΔL′≡ :
      ΔL′ ≡ applyTyCtxs ((χsL ++ χsR) ++ χsT) ΔL
    ΔL′≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔL₂≡)
          (trans
            (cong (λ Δ → applyTyCtxs χsT (applyTyCtxs χsR Δ))
              ΔL₁≡)
            (sym
              (trans
                (applyTyCtxs-++ (χsL ++ χsR) χsT ΔL)
                (cong (applyTyCtxs χsT)
                  (applyTyCtxs-++ χsL χsR ΔL))))))

    ρ′≡ :
      ρ′ ≡ applyLeftChanges ((χsL ++ χsR) ++ χsT) ρ
    ρ′≡ =
      trans ρT≡
        (sym
          (trans
            (applyLeftChanges-++ (χsL ++ χsR) χsT ρ)
            (cong (applyLeftChanges χsT)
              (applyLeftChanges-++ χsL χsR ρ))))

    C≡ :
      applyTys χsT (applyTys χsR (applyTys χsL B)) ≡
        applyTys ((χsL ++ χsR) ++ χsT) B
    C≡ =
      sym
        (trans
          (applyTys-++ (χsL ++ χsR) χsT B)
          (cong (applyTys χsT) (applyTys-++ χsL χsR B)))
  in
  (χsL ++ χsR) ++ χsT ,
  N ,
  ΔL′ ,
  ρ′ ,
  _ ,
  _ ,
  _ ,
  source-steps ,
  ΔL′≡ ,
  ρ′≡ ,
  C≡ ,
  refl ,
  N⊒N′[V′]

mediated-dgg-beta-right-first :
  ∀ {ΔL ΔR ρ L R N′ V′ p q A A′ B B′} →
  Value L →
  No• L →
  RuntimeOK R →
  Value V′ →
  (p↦qᶜ :
    ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
      ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-right-first {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {N′ = N′} {V′ = V′}
    {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    vL noL okR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  let
    χsR , WR , ΔL₁ ,
      vWR , noWR , R↠WR , ΔL₁≡ , ρR-corr ,
      leftR≡ , rightR≡ , pRᶜ , WR⊒V′raw =
      catchup-lemmaᵐ okR vV′ R⊒V′

    ρR = applyLeftChanges χsR ρ

    corrR :
      StoreCorr (applyTyCtxs χsR ΔL) ΔR ρR
    corrR =
      subst (λ Δ → StoreCorr Δ ΔR ρR) ΔL₁≡ ρR-corr

    LF⊒ƛraw :
      applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR ∣ []
        ⊢ applyTerms χsR L ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsR (A ⇒ B) ⊒ᵐ A′ ⇒ B′
    LF⊒ƛraw = left-changes-term-narrowingᵐ χsR corrR L⊒ƛ

    LF⊒ƛ :
      ΔL₁ ∣ ΔR ∣ ρR ∣ []
        ⊢ applyTerms χsR L ⊒ ƛ N′ ∶ p ↦ q
          ⦂ applyTys χsR A ⇒ applyTys χsR B ⊒ᵐ A′ ⇒ B′
    LF⊒ƛ =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρR ∣ []
            ⊢ applyTerms χsR L ⊒ ƛ N′ ∶ p ↦ q
              ⦂ applyTys χsR A ⇒ applyTys χsR B ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₁≡)
        (subst
          (λ C →
            applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR ∣ []
              ⊢ applyTerms χsR L ⊒ ƛ N′ ∶ p ↦ q
                ⦂ C ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR A B)
          LF⊒ƛraw)

    p↦qᶜRraw :
      applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR
        ⊢ p ↦ q ∶ᶜ applyTys χsR (A ⇒ B) ⊒ᵐ A′ ⇒ B′
    p↦qᶜRraw = left-changes-transportᵐ χsR corrR p↦qᶜ

    p↦qᶜR :
      ΔL₁ ∣ ΔR ∣ ρR
        ⊢ p ↦ q ∶ᶜ applyTys χsR A ⇒ applyTys χsR B
          ⊒ᵐ A′ ⇒ B′
    p↦qᶜR =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρR
            ⊢ p ↦ q ∶ᶜ applyTys χsR A ⇒ applyTys χsR B
              ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₁≡)
        (subst
          (λ C →
            applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR
              ⊢ p ↦ q ∶ᶜ C ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR A B)
          p↦qᶜRraw)

    pd-eq :
      fun-narrow-domain-dualᵐᶜ p↦qᶜR
        ≡ fun-narrow-domain-dualᵐᶜ p↦qᶜ
    pd-eq = fun-narrow-domain-dualᵐ-determined p↦qᶜR p↦qᶜ

    WR⊒V′ :
      ΔL₁ ∣ ΔR ∣ ρR ∣ []
        ⊢ WR ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜR
          ⦂ applyTys χsR A ⊒ᵐ A′
    WR⊒V′ =
      subst
        (λ pd →
          ΔL₁ ∣ ΔR ∣ ρR ∣ []
            ⊢ WR ⊒ V′ ∶ pd ⦂ applyTys χsR A ⊒ᵐ A′)
        (sym pd-eq)
        WR⊒V′raw

    ready :
      L · R —↠[ χsR ] applyTerms χsR L · WR
    ready = ·₂-↠ vL noL R↠WR

    tail =
      sim-betaᵐ
        LF⊒ƛ
        (applyTerms-preserves-Value χsR vL)
        (applyTerms-preserves-No• χsR noL)
        p↦qᶜR
        (fun-narrow-domain-dual-typingᵐᶜ p↦qᶜR)
        WR⊒V′
        vWR
        noWR
        vV′
  in
  let
    χsT , N , ΔL′ , ρ′ ,
      tail-red , ΔT≡ , ρT≡ , N⊒N′[V′] = tail

    source-steps :
      L · R —↠[ χsR ++ χsT ] N
    source-steps = ↠-trans ready tail-red

    ΔL′≡ :
      ΔL′ ≡ applyTyCtxs (χsR ++ χsT) ΔL
    ΔL′≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔL₁≡)
          (sym (applyTyCtxs-++ χsR χsT ΔL)))

    ρ′≡ :
      ρ′ ≡ applyLeftChanges (χsR ++ χsT) ρ
    ρ′≡ = trans ρT≡ (sym (applyLeftChanges-++ χsR χsT ρ))

    C≡ :
      applyTys χsT (applyTys χsR B) ≡ applyTys (χsR ++ χsT) B
    C≡ = sym (applyTys-++ χsR χsT B)
  in
  χsR ++ χsT ,
  N ,
  ΔL′ ,
  ρ′ ,
  _ ,
  _ ,
  _ ,
  source-steps ,
  ΔL′≡ ,
  ρ′≡ ,
  C≡ ,
  refl ,
  N⊒N′[V′]

mediated-dgg-beta :
  ∀ {ΔL ΔR ρ L R N′ V′ p q A A′ B B′} →
  RuntimeOK (L · R) →
  Value V′ →
  (p↦qᶜ :
    ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ V′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
      ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ N′ [ V′ ] ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta (ok-no (no•-· noL noR))
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  mediated-dgg-beta-left-first
    (ok-no noL) (ok-no noR) noR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
mediated-dgg-beta (ok-·₁ okL noR)
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  mediated-dgg-beta-left-first
    okL (ok-no noR) noR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
mediated-dgg-beta (ok-·₂ vL noL okR)
    vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′ =
  mediated-dgg-beta-right-first
    vL noL okR vV′ p↦qᶜ p-domainᶜ L⊒ƛ R⊒V′
