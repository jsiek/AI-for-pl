module proof.SimBetaMediated where

-- File Charter:
--   * The beta simulation over the mediated narrowing relation: the
--     source function position catches up to a lambda and the
--     application steps, transporting the relation across the
--     accumulated left store changes.
--   * Port of `proof.SimBetaSeparated.sim-beta`.  The statement sheds
--     the index rewriting: the old conclusion was at
--     `applyCoercions χs q`, forcing the applyCoercions-++ and
--     dual-commutation plumbing (and the approved
--     `left-change-fun-coercion-narrowing` postulate) through every
--     cast branch; the mediated conclusion keeps the original `q`,
--     since source store changes never touch a mediated index raw
--     (`left-changes-transportᵐ`).  The proof splits on the function
--     relation like the old proof; all branches are filled — the two
--     arrow cast branches recurse through catchup using the cast
--     constructors' own premises, and the exotic coercion shapes are
--     refuted locally by their own witnesses (no canonical-⇒/FunView
--     detour).

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NarrowWiden using
  (cross; dualⁿ; dualʷ; sealⁿ; _︔seal_; _？︔_; _∣_∣_⊢_∶_⊒_)
  renaming (_↦_ to _↦ⁿʷ_; gen to genⁿʷ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing
open import TermNarrowingSeparated using (ctx-entry)
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyLeftChanges-++
  )
open import proof.CatchupMediated using (catchup-lemmaᵐ)
open import proof.MediationProperties using
  ( left-changes-transportᵐ
  ; fun-narrow-domain-dual¹
  ; fun-narrow-domain-dual-typing¹
  ; fun-narrow-domain-dualᵐ-determined
  )
open import proof.MediatedLeftInsertion using
  (left-changes-term-narrowingᵐ)
open import proof.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyCoercions
  ; applyCoercions-++
  ; applyTys-++
  ; applyTyCtxs-++
  ; cast-↠
  ; ↠-trans
  ; ·₂-↠
  )
open import proof.LeftChangeNarrowingSeparated using
  ( dualʷ-involutive-raw
  ; applyTys-⇒
  ; no•-cast-inv
  )
open import proof.DGGSourceCastTailMediated using
  ( inner-seq-index-impossible
  ; plus-seq-cast-impossible
  )
  renaming
  ( mediated-source-cast-plus-tail to sim-betaᵐ-cast-plus-tail
  ; mediated-source-cast-minus-tail to sim-betaᵐ-cast-minus-tail
  )

-- The mediated substitution lemma for the beta body (open in the old
-- development as well).  Postulated with explicit approval
-- (2026-07-06); the substitution metatheory of the mediated relation
-- is its own work item.
postulate
  term-substitution-narrowingᵐ :
    ∀ {ΔL ΔR ρ N N′ V V′ p q A A′ B B′} →
    ΔL ∣ ΔR ∣ ρ ∣ ctx-entry A A′ p ∷ []
      ⊢ N ⊒ N′ ∶ q ⦂ B ⊒ᵐ B′ →
    ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ V ⊒ V′ ∶ p ⦂ A ⊒ᵐ A′ →
    ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ N [ V ] ⊒ N′ [ V′ ] ∶ q ⦂ B ⊒ᵐ B′

{-# TERMINATING #-}
sim-betaᵐ :
  ∀ {ΔL ΔR ρ WL NL WR VR p q A A′ B B′ μsim} →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ WL ⊒ ƛ NL ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  Value WL →
  No• WL →
  (p↦q-sim⊒ : μsim ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
                ∶ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′)) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dualᵐ p↦q-sim⊒ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ []
    ⊢ WR ⊒ VR ∶ fun-narrow-domain-dualᵐ p↦q-sim⊒ ⦂ A ⊒ᵐ A′ →
  Value WR →
  No• WR →
  Value VR →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ]
    (WL · WR —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ NL [ VR ] ∶ q ⦂ applyTys χs B ⊒ᵐ B′
sim-betaᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {WR = WR} {VR = VR}
    {A = A} {A′ = A′}
    (ƛ⊒ƛᵗ p↦qᶜ N⊒NL)
    (ƛ N) noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  let
    WR⊒VR′ =
      subst
        (λ pd → ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ WR ⊒ VR ∶ pd ⦂ A ⊒ᵐ A′)
        (fun-narrow-domain-dualᵐ-determined p↦q-sim⊒ p↦qᶜ)
        WR⊒VR
  in
  keep ∷ [] ,
  N [ WR ] ,
  ΔL ,
  ρ ,
  ↠-step (pure-step (β vWR)) ↠-refl ,
  refl ,
  refl ,
  term-substitution-narrowingᵐ N⊒NL WR⊒VR′
-- Source-cast branches.  The one-store cast evidence carried by the
-- mediated constructors makes the shape analysis local: the deriv
-- and witness in the premise refute the impossible coercion shapes
-- directly, where the old proof routed every shape through
-- canonical-⇒/FunView on the term typing.
--
-- cast+⊒ᵗ: the source term is V ⟨ narrowing-dual¹ s⊒ˡ ⟩ with
-- s ∶ (A ⇒ B) ⊒ C.  A source-typed narrowing witness at an arrow
-- source is either an arrow cross witness or refuted: the seq/gen/
-- seal shapes compute (through `normalᵃ`) to non-inert duals, so the
-- Value premise refutes them; the ？︔ seq shape is refuted by its
-- ★-sourced untag typing.
sim-betaᵐ
  (cast+⊒ᵗ {s = id X} qᶜ r⊒ (cast-id _ _ , cross ()) V⊒ƛ)
sim-betaᵐ (cast+⊒ᵗ {s = s₁ ︔ s₂} qᶜ r⊒ s⊒ˡ V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  ⊥-elim (plus-seq-cast-impossible s⊒ˡ vWL)
sim-betaᵐ (cast+⊒ᵗ {s = unseal α X} qᶜ r⊒ (_ , cross ()) V⊒ƛ)
sim-betaᵐ (cast+⊒ᵗ {s = inst X s} qᶜ r⊒ (_ , cross ()) V⊒ƛ)
sim-betaᵐ
    (cast+⊒ᵗ {s = gen X s} qᶜ r⊒ (s⊢ , genⁿʷ sⁿ) V⊒ƛ)
    (vV ⟨ () ⟩)
sim-betaᵐ (cast+⊒ᵗ {s = X !} qᶜ r⊒ (_ , cross ()) V⊒ƛ)
sim-betaᵐ
    (cast+⊒ᵗ {s = seal X α} qᶜ r⊒ (s⊢ , sealⁿ .X .α) V⊒ƛ)
    (vV ⟨ () ⟩)
-- Non-arrow inner-index shapes under an arrow source cast, refuted
-- through the inner ∶ᶜ evidence: the id shape has no witness at an
-- arrow endpoint, and the ？/unseal/inst/？︔ shapes force a
-- non-arrow mediated source (★, a seal variable, or a ∀), which the
-- structural MedTy of the arrow middle type refutes.  The ︔seal
-- shape's tail types at a seal variable, not the arrow target.
sim-betaᵐ
  (cast+⊒ᵗ {q = id X} (_ , _ , _ , _ , _ , (cast-id _ _ , cross ()))
    r⊒ s⊒ˡ V⊒ƛ)
sim-betaᵐ
    (cast+⊒ᵗ {q = q₁ ︔ q₂} qᶜ r⊒ (cast-fun _ _ , _) V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  ⊥-elim (inner-seq-index-impossible qᶜ)
sim-betaᵐ
  (cast+⊒ᵗ {q = X ？}
    (_ , _ , _ , _ , () , (cast-untag _ _ _ , _))
    r⊒ (cast-fun _ _ , _) V⊒ƛ)
sim-betaᵐ
  (cast+⊒ᵗ {q = unseal α X}
    (_ , _ , _ , _ , () , (cast-unseal _ _ _ , _))
    r⊒ (cast-fun _ _ , _) V⊒ƛ)
sim-betaᵐ
  (cast+⊒ᵗ {q = inst X q₁}
    (_ , _ , _ , _ , () , (cast-inst _ _ _ , _))
    r⊒ (cast-fun _ _ , _) V⊒ƛ)
sim-betaᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {NL = NL} {WR = WR}
    {VR = VR} {p = p} {q = q}
    {A = Aₒ} {A′ = AR} {B = Bₒ} {B′ = BR}
    (cast+⊒ᵗ {M = V} {q = pᵢ ↦ qᵢ} {s = cₛ ↦ dₛ}
      {C = AL ⇒ BL} {μ = μO} {η = ηC}
      qᶜ r⊒ s⊒ˡ@(cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ)) V⊒ƛ)
    (vV ⟨ i ⟩) (no•-⟨⟩ noV)
    p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  let
    stores = narrowing-store-corrᵐᶜ qᶜ

    cᵈ = proj₁ (dualʷ normalᵃ cʷ)
    dᵈ = proj₁ (dualⁿ normalᵃ dⁿ)

    -- The argument-position cast node at the inner domain.
    WR-c⊒VR :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ WR ⟨ cᵈ ⟩ ⊒ VR ∶ fun-narrow-domain-dualᵐᶜ qᶜ
          ⦂ AL ⊒ᵐ AR
    WR-c⊒VR =
      cast-⊒ᵗ
        (fun-narrow-domain-dual-typingᵐᶜ qᶜ)
        p-domainᶜ
        (fun-narrow-domain-dual-typing¹ (leftStore-wf stores) s⊒ˡ)
        WR⊒VR

    χsA , WRA , ΔLA , vWRA , noWRA , WR↠WRA , ΔLA≡ , ρA-corr ,
      leftA≡ , rightA≡ , pdᶜᴬ , WRA⊒VRᴬ =
      catchup-lemmaᵐ (ok-⟨⟩ (ok-no noWR)) vVR WR-c⊒VR

    ρA = applyLeftChanges χsA ρ

    corrA : StoreCorr (applyTyCtxs χsA ΔL) ΔR ρA
    corrA = subst (λ Δ → StoreCorr Δ ΔR ρA) ΔLA≡ ρA-corr

    -- Advance the function relation and the inner arrow evidence
    -- across the catchup's left store changes; the coercion indices
    -- are untouched (the point of the mediated relation).
    VA⊒ƛ :
      ΔLA ∣ ΔR ∣ ρA ∣ []
        ⊢ applyTerms χsA V ⊒ ƛ NL ∶ pᵢ ↦ qᵢ
          ⦂ applyTys χsA AL ⇒ applyTys χsA BL ⊒ᵐ AR ⇒ BR
    VA⊒ƛ =
      subst
        (λ C₀ →
          ΔLA ∣ ΔR ∣ ρA ∣ []
            ⊢ applyTerms χsA V ⊒ ƛ NL ∶ pᵢ ↦ qᵢ
              ⦂ C₀ ⊒ᵐ AR ⇒ BR)
        (applyTys-⇒ χsA AL BL)
        (subst
          (λ Δ →
            Δ ∣ ΔR ∣ ρA ∣ []
              ⊢ applyTerms χsA V ⊒ ƛ NL ∶ pᵢ ↦ qᵢ
                ⦂ applyTys χsA (AL ⇒ BL) ⊒ᵐ AR ⇒ BR)
          (sym ΔLA≡)
          (left-changes-term-narrowingᵐ χsA corrA V⊒ƛ))

    qᶜᴬ :
      ΔLA ∣ ΔR ∣ ρA
        ⊢ pᵢ ↦ qᵢ
          ∶ᶜ applyTys χsA AL ⇒ applyTys χsA BL ⊒ᵐ AR ⇒ BR
    qᶜᴬ =
      subst
        (λ C₀ →
          ΔLA ∣ ΔR ∣ ρA ⊢ pᵢ ↦ qᵢ ∶ᶜ C₀ ⊒ᵐ AR ⇒ BR)
        (applyTys-⇒ χsA AL BL)
        (subst
          (λ Δ →
            Δ ∣ ΔR ∣ ρA ⊢ pᵢ ↦ qᵢ
              ∶ᶜ applyTys χsA (AL ⇒ BL) ⊒ᵐ AR ⇒ BR)
          (sym ΔLA≡)
          (left-changes-transportᵐ χsA corrA qᶜ))

    pd-eq :
      fun-narrow-domain-dualᵐ qᶜᴬ ≡ fun-narrow-domain-dualᵐᶜ qᶜ
    pd-eq = fun-narrow-domain-dualᵐ-determined qᶜᴬ qᶜ

    p-domainᶜᴬ :
      ΔLA ∣ ΔR ∣ ρA
        ⊢ fun-narrow-domain-dualᵐ qᶜᴬ ∶ᶜ applyTys χsA AL ⊒ᵐ AR
    p-domainᶜᴬ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ ρA ⊢ pd ∶ᶜ applyTys χsA AL ⊒ᵐ AR)
        (sym pd-eq)
        pdᶜᴬ

    WRA⊒VR′ :
      ΔLA ∣ ΔR ∣ ρA ∣ []
        ⊢ WRA ⊒ VR ∶ fun-narrow-domain-dualᵐ qᶜᴬ
          ⦂ applyTys χsA AL ⊒ᵐ AR
    WRA⊒VR′ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ ρA ∣ []
            ⊢ WRA ⊒ VR ∶ pd ⦂ applyTys χsA AL ⊒ᵐ AR)
        (sym pd-eq)
        WRA⊒VRᴬ

    χsT , N , ΔLT , ρT , tail-red , ΔT≡ , ρT≡ , N⊒NL =
      sim-betaᵐ
        VA⊒ƛ
        (applyTerms-preserves-Value χsA vV)
        (applyTerms-preserves-No• χsA noV)
        qᶜᴬ
        p-domainᶜᴬ
        WRA⊒VR′
        vWRA
        noWRA
        vVR

    -- Reductions: β-↦, catchup on the casted argument, recursion
    -- tail — all under the codomain cast.
    head-red :
      (V ⟨ cᵈ ↦ dᵈ ⟩) · WR —↠[ keep ∷ [] ]
        (V · (WR ⟨ cᵈ ⟩)) ⟨ dᵈ ⟩
    head-red = ↠-step (pure-step (β-↦ vV vWR)) ↠-refl

    source-steps :
      (V ⟨ cᵈ ↦ dᵈ ⟩) · WR —↠[ (keep ∷ χsA) ++ χsT ]
        N ⟨ applyCoercions χsT (applyCoercions χsA dᵈ) ⟩
    source-steps =
      ↠-trans
        (↠-trans head-red (cast-↠ {c = dᵈ} (·₂-↠ vV noV WR↠WRA)))
        (cast-↠ {c = applyCoercions χsA dᵈ} tail-red)

    ΔLT-total≡ :
      ΔLT ≡ applyTyCtxs ((keep ∷ χsA) ++ χsT) ΔL
    ΔLT-total≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔLA≡)
          (sym (applyTyCtxs-++ χsA χsT ΔL)))

    ρT-total≡ :
      ρT ≡ applyLeftChanges ((keep ∷ χsA) ++ χsT) ρ
    ρT-total≡ =
      trans ρT≡ (sym (applyLeftChanges-++ χsA χsT ρ))

    μN , qᵢ⊒T = typed-term-narrowing-coercionᵐ N⊒NL

    ρT-corr : StoreCorr ΔLT ΔR ρT
    ρT-corr = narrowing-store-corrᵐᶜ {μ = μN} qᵢ⊒T

    N⊒NL′ :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⊒ NL [ VR ] ∶ qᵢ
          ⦂ applyTys (χsA ++ χsT) BL ⊒ᵐ BR
    N⊒NL′ =
      subst
        (λ X →
          ΔLT ∣ ΔR ∣ ρT ∣ [] ⊢ N ⊒ NL [ VR ] ∶ qᵢ ⦂ X ⊒ᵐ BR)
        (sym (applyTys-++ χsA χsT BL))
        N⊒NL

    N-tail :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ applyCoercions (χsA ++ χsT) dᵈ ⟩ ⊒ NL [ VR ]
          ∶ q ⦂ applyTys (χsA ++ χsT) Bₒ ⊒ᵐ BR
    N-tail =
      sim-betaᵐ-cast-plus-tail (χsA ++ χsT) {N = N} {Target = NL [ VR ]}
        ΔLT-total≡
        ρT-total≡
        ρT-corr
        (fun-narrow-codomainᵐᶜ qᶜ)
        (fun-narrow-codomainᵐ r⊒)
        (d⊢ , dⁿ)
        N⊒NL′
  in
  (keep ∷ χsA) ++ χsT ,
  N ⟨ applyCoercions χsT (applyCoercions χsA dᵈ) ⟩ ,
  ΔLT ,
  ρT ,
  source-steps ,
  ΔLT-total≡ ,
  ρT-total≡ ,
  subst
    (λ c₀ →
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ c₀ ⟩ ⊒ NL [ VR ]
          ∶ q ⦂ applyTys (χsA ++ χsT) Bₒ ⊒ᵐ BR)
    (applyCoercions-++ χsA χsT dᵈ)
    N-tail
--
-- cast-⊒ᵗ: the source term is V ⟨ s ⟩ with s ∶ A₀ ⊒ (A ⇒ B); the
-- value premise (Inert s) and the witness refute the non-arrow
-- shapes.
sim-betaᵐ
  (cast-⊒ᵗ {s = id X} qᶜ r⊒ (cast-id _ _ , cross ()) V⊒ƛ)
sim-betaᵐ (cast-⊒ᵗ {s = s₁ ︔ s₂} qᶜ r⊒ s⊒ˡ V⊒ƛ)
    (vV ⟨ () ⟩)
sim-betaᵐ (cast-⊒ᵗ {s = X ？} qᶜ r⊒ s⊒ˡ V⊒ƛ)
    (vV ⟨ () ⟩)
sim-betaᵐ (cast-⊒ᵗ {s = unseal α X} qᶜ r⊒ s⊒ˡ V⊒ƛ)
    (vV ⟨ () ⟩)
sim-betaᵐ (cast-⊒ᵗ {s = inst X s} qᶜ r⊒ s⊒ˡ V⊒ƛ)
    (vV ⟨ () ⟩)
-- Non-arrow inner-index shapes, refuted through the ⊒ᵐ evidence of
-- the cast premise exactly as in the cast+⊒ᵗ branch above.
sim-betaᵐ
  (cast-⊒ᵗ {r = id X} qᶜ
    (_ , _ , _ , _ , _ , (cast-id _ _ , cross ()))
    s⊒ˡ V⊒ƛ)
sim-betaᵐ
    (cast-⊒ᵗ {r = r₁ ︔ r₂} qᶜ r⊒ (cast-fun _ _ , _) V⊒ƛ)
    vWL noWL p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  ⊥-elim (inner-seq-index-impossible r⊒)
sim-betaᵐ
  (cast-⊒ᵗ {r = X ？} qᶜ
    (_ , _ , _ , _ , () , (cast-untag _ _ _ , _))
    (cast-fun _ _ , _) V⊒ƛ)
sim-betaᵐ
  (cast-⊒ᵗ {r = unseal α X} qᶜ
    (_ , _ , _ , _ , () , (cast-unseal _ _ _ , _))
    (cast-fun _ _ , _) V⊒ƛ)
sim-betaᵐ
  (cast-⊒ᵗ {r = inst X r₁} qᶜ
    (_ , _ , _ , _ , () , (cast-inst _ _ _ , _))
    (cast-fun _ _ , _) V⊒ƛ)
sim-betaᵐ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {NL = NL} {WR = WR}
    {VR = VR} {p = p} {q = q}
    {A = Aₒ} {A′ = AR} {B = Bₒ} {B′ = BR}
    (cast-⊒ᵗ {M = V} {r = pᵢ ↦ qᵢ} {s = cₛ ↦ dₛ}
      {A = AV ⇒ BV} {μ = μO} {η = ηC}
      qᶜ r⊒ s⊒ˡ@(cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ)) V⊒ƛ)
    (vV ⟨ i ⟩) (no•-⟨⟩ noV)
    p↦q-sim⊒ p-domainᶜ WR⊒VR vWR noWR vVR =
  let
    stores = narrowing-store-corrᵐᶜ qᶜ

    cᵈ = proj₁ (dualʷ normalᵃ cʷ)
    cᵈⁿ = proj₂ (dualʷ normalᵃ cʷ)

    -- The argument-position cast node, through the double dual: the
    -- source-side cast+⊒ᵗ node concludes at the dual of the dual of
    -- the domain factor, which is the domain factor itself.
    cᵈ⊒ˡ : ηC ∣ ΔL ∣ leftStore ρ ⊢ cᵈ ∶ AV ⊒ Aₒ
    cᵈ⊒ˡ =
      proj₁ (fun-narrow-domain-dual-typing¹ (leftStore-wf stores) s⊒ˡ) ,
      cᵈⁿ

    WR-c⊒VR :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ WR ⟨ cₛ ⟩ ⊒ VR ∶ fun-narrow-domain-dualᵐ r⊒
          ⦂ AV ⊒ᵐ AR
    WR-c⊒VR =
      subst
        (λ c₀ →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ WR ⟨ c₀ ⟩ ⊒ VR ∶ fun-narrow-domain-dualᵐ r⊒
              ⦂ AV ⊒ᵐ AR)
        (dualʷ-involutive-raw cʷ)
        (cast+⊒ᵗ
          p-domainᶜ
          (fun-narrow-domain-dual-typingᵐ r⊒)
          cᵈ⊒ˡ
          WR⊒VR)

    χsA , WRA , ΔLA , vWRA , noWRA , WR↠WRA , ΔLA≡ , ρA-corr ,
      leftA≡ , rightA≡ , pdᶜᴬ , WRA⊒VRᴬ =
      catchup-lemmaᵐ (ok-⟨⟩ (ok-no noWR)) vVR WR-c⊒VR

    ρA = applyLeftChanges χsA ρ

    corrA : StoreCorr (applyTyCtxs χsA ΔL) ΔR ρA
    corrA = subst (λ Δ → StoreCorr Δ ΔR ρA) ΔLA≡ ρA-corr

    VA⊒ƛ :
      ΔLA ∣ ΔR ∣ ρA ∣ []
        ⊢ applyTerms χsA V ⊒ ƛ NL ∶ pᵢ ↦ qᵢ
          ⦂ applyTys χsA AV ⇒ applyTys χsA BV ⊒ᵐ AR ⇒ BR
    VA⊒ƛ =
      subst
        (λ C₀ →
          ΔLA ∣ ΔR ∣ ρA ∣ []
            ⊢ applyTerms χsA V ⊒ ƛ NL ∶ pᵢ ↦ qᵢ
              ⦂ C₀ ⊒ᵐ AR ⇒ BR)
        (applyTys-⇒ χsA AV BV)
        (subst
          (λ Δ →
            Δ ∣ ΔR ∣ ρA ∣ []
              ⊢ applyTerms χsA V ⊒ ƛ NL ∶ pᵢ ↦ qᵢ
                ⦂ applyTys χsA (AV ⇒ BV) ⊒ᵐ AR ⇒ BR)
          (sym ΔLA≡)
          (left-changes-term-narrowingᵐ χsA corrA V⊒ƛ))

    r⊒ᴬ :
      μO ∣ ΔLA ∣ ΔR ∣ ρA
        ⊢ pᵢ ↦ qᵢ
          ∶ applyTys χsA AV ⇒ applyTys χsA BV ⊒ᵐ AR ⇒ BR
    r⊒ᴬ =
      subst
        (λ C₀ →
          μO ∣ ΔLA ∣ ΔR ∣ ρA ⊢ pᵢ ↦ qᵢ ∶ C₀ ⊒ᵐ AR ⇒ BR)
        (applyTys-⇒ χsA AV BV)
        (subst
          (λ Δ →
            μO ∣ Δ ∣ ΔR ∣ ρA ⊢ pᵢ ↦ qᵢ
              ∶ applyTys χsA (AV ⇒ BV) ⊒ᵐ AR ⇒ BR)
          (sym ΔLA≡)
          (left-changes-transportᵐ χsA corrA r⊒))

    pd-eq :
      fun-narrow-domain-dualᵐ r⊒ᴬ ≡ fun-narrow-domain-dualᵐ r⊒
    pd-eq = fun-narrow-domain-dualᵐ-determined r⊒ᴬ r⊒

    p-domainᶜᴬ :
      ΔLA ∣ ΔR ∣ ρA
        ⊢ fun-narrow-domain-dualᵐ r⊒ᴬ ∶ᶜ applyTys χsA AV ⊒ᵐ AR
    p-domainᶜᴬ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ ρA ⊢ pd ∶ᶜ applyTys χsA AV ⊒ᵐ AR)
        (sym pd-eq)
        pdᶜᴬ

    WRA⊒VR′ :
      ΔLA ∣ ΔR ∣ ρA ∣ []
        ⊢ WRA ⊒ VR ∶ fun-narrow-domain-dualᵐ r⊒ᴬ
          ⦂ applyTys χsA AV ⊒ᵐ AR
    WRA⊒VR′ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ ρA ∣ []
            ⊢ WRA ⊒ VR ∶ pd ⦂ applyTys χsA AV ⊒ᵐ AR)
        (sym pd-eq)
        WRA⊒VRᴬ

    χsT , N , ΔLT , ρT , tail-red , ΔT≡ , ρT≡ , N⊒NL =
      sim-betaᵐ
        VA⊒ƛ
        (applyTerms-preserves-Value χsA vV)
        (applyTerms-preserves-No• χsA noV)
        r⊒ᴬ
        p-domainᶜᴬ
        WRA⊒VR′
        vWRA
        noWRA
        vVR

    head-red :
      (V ⟨ cₛ ↦ dₛ ⟩) · WR —↠[ keep ∷ [] ]
        (V · (WR ⟨ cₛ ⟩)) ⟨ dₛ ⟩
    head-red = ↠-step (pure-step (β-↦ vV vWR)) ↠-refl

    source-steps :
      (V ⟨ cₛ ↦ dₛ ⟩) · WR —↠[ (keep ∷ χsA) ++ χsT ]
        N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
    source-steps =
      ↠-trans
        (↠-trans head-red (cast-↠ {c = dₛ} (·₂-↠ vV noV WR↠WRA)))
        (cast-↠ {c = applyCoercions χsA dₛ} tail-red)

    ΔLT-total≡ :
      ΔLT ≡ applyTyCtxs ((keep ∷ χsA) ++ χsT) ΔL
    ΔLT-total≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔLA≡)
          (sym (applyTyCtxs-++ χsA χsT ΔL)))

    ρT-total≡ :
      ρT ≡ applyLeftChanges ((keep ∷ χsA) ++ χsT) ρ
    ρT-total≡ =
      trans ρT≡ (sym (applyLeftChanges-++ χsA χsT ρ))

    μN , qᵢ⊒T = typed-term-narrowing-coercionᵐ N⊒NL

    ρT-corr : StoreCorr ΔLT ΔR ρT
    ρT-corr = narrowing-store-corrᵐᶜ {μ = μN} qᵢ⊒T

    qᵢ⊒′ :
      μN ∣ ΔLT ∣ ΔR ∣ ρT
        ⊢ qᵢ ∶ applyTys (χsA ++ χsT) BV ⊒ᵐ BR
    qᵢ⊒′ =
      subst
        (λ X → μN ∣ ΔLT ∣ ΔR ∣ ρT ⊢ qᵢ ∶ X ⊒ᵐ BR)
        (sym (applyTys-++ χsA χsT BV))
        qᵢ⊒T

    N⊒NL′ :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⊒ NL [ VR ] ∶ qᵢ
          ⦂ applyTys (χsA ++ χsT) BV ⊒ᵐ BR
    N⊒NL′ =
      subst
        (λ X →
          ΔLT ∣ ΔR ∣ ρT ∣ [] ⊢ N ⊒ NL [ VR ] ∶ qᵢ ⦂ X ⊒ᵐ BR)
        (sym (applyTys-++ χsA χsT BV))
        N⊒NL

    N-tail :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ applyCoercions (χsA ++ χsT) dₛ ⟩ ⊒ NL [ VR ]
          ∶ q ⦂ applyTys (χsA ++ χsT) Bₒ ⊒ᵐ BR
    N-tail =
      sim-betaᵐ-cast-minus-tail (χsA ++ χsT) {N = N} {Target = NL [ VR ]}
        ΔLT-total≡
        ρT-total≡
        ρT-corr
        (fun-narrow-codomainᵐᶜ qᶜ)
        (d⊢ , dⁿ)
        qᵢ⊒′
        N⊒NL′
  in
  (keep ∷ χsA) ++ χsT ,
  N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩ ,
  ΔLT ,
  ρT ,
  source-steps ,
  ΔLT-total≡ ,
  ρT-total≡ ,
  subst
    (λ c₀ →
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ c₀ ⟩ ⊒ NL [ VR ]
          ∶ q ⦂ applyTys (χsA ++ χsT) Bₒ ⊒ᵐ BR)
    (applyCoercions-++ χsA χsT dₛ)
    N-tail
