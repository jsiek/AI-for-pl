module proof.DGGBetaCastMediated where

-- File Charter:
--   * Mediated-store DGG application packaging for target
--     beta-through-function-cast steps.
--   * Runs catchup on source application subterms, then delegates the
--     value/wrap core to `DGGBetaCastValueMediated`.
--   * Keeps the main `DynamicGradualGuaranteeMediated` module slim.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _++_)
open import Data.Product using
  (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyLeftChanges-++
  )
open import proof.CatchupMediated using (catchup-lemmaᵐ)
open import proof.LeftChangeNarrowingSeparated using
  ( applyTys-⇒
  ; applyTerms-preserves-RuntimeOK
  )
open import proof.MediatedLeftInsertion using
  (left-changes-term-narrowingᵐ)
open import proof.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyTys-++
  ; applyTyCtxs-++
  ; ↠-trans
  ; ·₁-↠
  ; ·₂-↠
  )

open import proof.DGGBetaCastValueMediated using
  (mediated-dgg-beta-cast-value)

------------------------------------------------------------------------
-- Application beta-cast packaging
------------------------------------------------------------------------

mediated-dgg-beta-cast-left-first :
  ∀ {ΔL ΔR ρ L R V′ W′ c d p q A A′ B B′} →
  RuntimeOK L →
  RuntimeOK R →
  No• R →
  Value V′ →
  Value W′ →
  (p↦qᶜ :
    ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ W′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
      ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-cast-left-first {ΔL = ΔL} {ΔR = ΔR}
    {ρ = ρ} {L = L} {R = R} {V′ = V′} {W′ = W′}
    {c = c} {d = d} {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    okL okR noR-ready vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  let
    χsL , WL , ΔL₁ ,
      vWL , noWL , L↠WL , ΔL₁≡ , ρL-corr ,
      leftL≡ , rightL≡ , pLᶜ , WL⊒V′cdraw =
      catchup-lemmaᵐ
        okL
        (vV′ ⟨ c ↦ d ⟩)
        L⊒V′cd

    corrL :
      StoreCorr (applyTyCtxs χsL ΔL) ΔR (applyLeftChanges χsL ρ)
    corrL =
      subst (λ Δ → StoreCorr Δ ΔR (applyLeftChanges χsL ρ))
        ΔL₁≡
        ρL-corr

    WL⊒V′cd :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ WL ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
          ⦂ applyTys χsL A ⇒ applyTys χsL B ⊒ᵐ A′ ⇒ B′
    WL⊒V′cd =
      subst
        (λ C₀ →
          ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ WL ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q ⦂ C₀ ⊒ᵐ A′ ⇒ B′)
        (applyTys-⇒ χsL A B)
        WL⊒V′cdraw

    R⊒W′L :
      ΔL₁ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
        ⊢ applyTerms χsL R ⊒ W′
          ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
            ⦂ applyTys χsL A ⊒ᵐ A′
    R⊒W′L =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ applyLeftChanges χsL ρ ∣ []
            ⊢ applyTerms χsL R ⊒ W′
              ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
                ⦂ applyTys χsL A ⊒ᵐ A′)
        (sym ΔL₁≡)
        (left-changes-term-narrowingᵐ χsL corrL R⊒W′)

    χsR , WR , ΔL₂ ,
      vWR , noWR , R↠WR , ΔL₂≡ , ρR-corr ,
      leftR≡ , rightR≡ , pRᶜ , WR⊒W′raw =
      catchup-lemmaᵐ
        (applyTerms-preserves-RuntimeOK χsL okR)
        vW′
        R⊒W′L

    ρLR = applyLeftChanges χsR (applyLeftChanges χsL ρ)

    corrR :
      StoreCorr (applyTyCtxs χsR ΔL₁) ΔR ρLR
    corrR =
      subst (λ Δ → StoreCorr Δ ΔR ρLR) ΔL₂≡ ρR-corr

    WLF⊒V′cdraw :
      applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR ∣ []
        ⊢ applyTerms χsR WL ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
          ⦂ applyTys χsR (applyTys χsL A ⇒ applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    WLF⊒V′cdraw =
      left-changes-term-narrowingᵐ χsR corrR WL⊒V′cd

    WLF⊒V′cd :
      ΔL₂ ∣ ΔR ∣ ρLR ∣ []
        ⊢ applyTerms χsR WL ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
          ⦂ applyTys χsR (applyTys χsL A)
              ⇒ applyTys χsR (applyTys χsL B)
            ⊒ᵐ A′ ⇒ B′
    WLF⊒V′cd =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρLR ∣ []
            ⊢ applyTerms χsR WL ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
              ⦂ applyTys χsR (applyTys χsL A)
                  ⇒ applyTys χsR (applyTys χsL B)
                ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₂≡)
        (subst
          (λ C₀ →
            applyTyCtxs χsR ΔL₁ ∣ ΔR ∣ ρLR ∣ []
              ⊢ applyTerms χsR WL ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
                ⦂ C₀ ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR (applyTys χsL A) (applyTys χsL B))
          WLF⊒V′cdraw)

    left-ready :
      L · R —↠[ χsL ] WL · applyTerms χsL R
    left-ready = ·₁-↠ noR-ready L↠WL

    right-ready :
      WL · applyTerms χsL R —↠[ χsR ] applyTerms χsR WL · WR
    right-ready = ·₂-↠ vWL noWL R↠WR

    tail =
      mediated-dgg-beta-cast-value
        (applyTerms-preserves-Value χsR vWL)
        (applyTerms-preserves-No• χsR noWL)
        vWR
        noWR
        vV′
        vW′
        WLF⊒V′cd
        pRᶜ
        WR⊒W′raw
  in
  let
    χsT , N , ΔL′ , ρ′ , C , D , r ,
      tail-red , ΔT≡ , ρT≡ , C≡ᵀ , D≡ᵀ , N⊒target = tail

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
      C ≡ applyTys ((χsL ++ χsR) ++ χsT) B
    C≡ =
      trans C≡ᵀ
        (sym
          (trans
            (applyTys-++ (χsL ++ χsR) χsT B)
            (cong (applyTys χsT) (applyTys-++ χsL χsR B))))
  in
  (χsL ++ χsR) ++ χsT ,
  N ,
  ΔL′ ,
  ρ′ ,
  C ,
  D ,
  r ,
  source-steps ,
  ΔL′≡ ,
  ρ′≡ ,
  C≡ ,
  D≡ᵀ ,
  N⊒target

mediated-dgg-beta-cast-right-first :
  ∀ {ΔL ΔR ρ L R V′ W′ c d p q A A′ B B′} →
  Value L →
  No• L →
  RuntimeOK R →
  Value V′ →
  Value W′ →
  (p↦qᶜ :
    ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ W′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
      ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-cast-right-first {ΔL = ΔL} {ΔR = ΔR}
    {ρ = ρ} {L = L} {R = R} {V′ = V′} {W′ = W′}
    {c = c} {d = d} {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    vL noL okR vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  let
    χsR , WR , ΔL₁ ,
      vWR , noWR , R↠WR , ΔL₁≡ , ρR-corr ,
      leftR≡ , rightR≡ , pRᶜ , WR⊒W′raw =
      catchup-lemmaᵐ
        okR
        vW′
        R⊒W′

    ρR = applyLeftChanges χsR ρ

    corrR :
      StoreCorr (applyTyCtxs χsR ΔL) ΔR ρR
    corrR =
      subst (λ Δ → StoreCorr Δ ΔR ρR) ΔL₁≡ ρR-corr

    LF⊒V′cdraw :
      applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR ∣ []
        ⊢ applyTerms χsR L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
          ⦂ applyTys χsR (A ⇒ B) ⊒ᵐ A′ ⇒ B′
    LF⊒V′cdraw = left-changes-term-narrowingᵐ χsR corrR L⊒V′cd

    LF⊒V′cd :
      ΔL₁ ∣ ΔR ∣ ρR ∣ []
        ⊢ applyTerms χsR L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
          ⦂ applyTys χsR A ⇒ applyTys χsR B ⊒ᵐ A′ ⇒ B′
    LF⊒V′cd =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρR ∣ []
            ⊢ applyTerms χsR L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
              ⦂ applyTys χsR A ⇒ applyTys χsR B ⊒ᵐ A′ ⇒ B′)
        (sym ΔL₁≡)
        (subst
          (λ C₀ →
            applyTyCtxs χsR ΔL ∣ ΔR ∣ ρR ∣ []
              ⊢ applyTerms χsR L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
                ⦂ C₀ ⊒ᵐ A′ ⇒ B′)
          (applyTys-⇒ χsR A B)
          LF⊒V′cdraw)

    ready :
      L · R —↠[ χsR ] applyTerms χsR L · WR
    ready = ·₂-↠ vL noL R↠WR

    tail =
      mediated-dgg-beta-cast-value
        (applyTerms-preserves-Value χsR vL)
        (applyTerms-preserves-No• χsR noL)
        vWR
        noWR
        vV′
        vW′
        LF⊒V′cd
        pRᶜ
        WR⊒W′raw
  in
  let
    χsT , N , ΔL′ , ρ′ , C , D , r ,
      tail-red , ΔT≡ , ρT≡ , C≡ᵀ , D≡ᵀ , N⊒target = tail

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
      C ≡ applyTys (χsR ++ χsT) B
    C≡ = trans C≡ᵀ (sym (applyTys-++ χsR χsT B))
  in
  χsR ++ χsT ,
  N ,
  ΔL′ ,
  ρ′ ,
  C ,
  D ,
  r ,
  source-steps ,
  ΔL′≡ ,
  ρ′≡ ,
  C≡ ,
  D≡ᵀ ,
  N⊒target

mediated-dgg-beta-cast :
  ∀ {ΔL ΔR ρ L R V′ W′ c d p q A A′ B B′} →
  RuntimeOK (L · R) →
  Value V′ →
  Value W′ →
  (p↦qᶜ :
    ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ᵐ A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ R ⊒ W′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ
      ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-cast (ok-no (no•-· noL noR))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-left-first
    (ok-no noL) (ok-no noR) noR
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₁ okL noR)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-left-first
    okL (ok-no noR) noR
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-no noR))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-left-first
    (ok-no noL) (ok-no noR) noR
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-• vV noV))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-• vV noV)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-·₁ okR₁ noR₂))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-·₁ okR₁ noR₂)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-·₂ vR₁ noR₁ okR₂))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-·₂ vR₁ noR₁ okR₂)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-ν okR))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-ν okR)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-⊕₁ okR₁ noR₂))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-⊕₁ okR₁ noR₂)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-⊕₂ vR₁ noR₁ okR₂))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-⊕₂ vR₁ noR₁ okR₂)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
mediated-dgg-beta-cast (ok-·₂ vL noL (ok-⟨⟩ okR))
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′ =
  mediated-dgg-beta-cast-right-first
    vL noL (ok-⟨⟩ okR)
    vV′ vW′ p↦qᶜ p-domainᶜ L⊒V′cd R⊒W′
