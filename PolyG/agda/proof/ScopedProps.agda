module proof.ScopedProps where

-- File Charter:
--   * Properties of the invariants of DenotInvariants.agda:
--       - a typed precision derivation is well scoped (⊑→WfPrec);
--       - Scoped is preserved by renaming, substitution of terms and
--         substitution of well-formed names, and by reduction
--         (Scoped-step, Scoped-steps);
--       - elaboration of a surface derivation is Scoped (elab-Scoped);
--       - closed precisions, grounds and terms are fixed by every name
--         substitution (closed-prec, closed-ground, closed-substᵀ).
--   * Consumed by proof/DenotAdequacy.agda and DenotationMeta.agda.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import Types
open import Terms
open import Reduction
open import proof.Determinism
  using (Plug; ≡-Plug; p-if; p-□·; p-app; p-letv; p-seal; p-unseal; p-is;
         p-inj; p-cast; p-inst)
open import GradualTerms
open import Compile
open import CompileInvariants
open import DenotInvariants
open import proof.TypeSubst using (substᵗ-wf-id)
open import proof.PrecisionProps
  using (WfRen; extₙ-wf; ↑ₙ-wf; substₙ-wf; substG-wf; substᵗ-wf;
         groundTy-wf; idᵖ-⊢; dynᵖ-⊢; meetL-⊢; meetR-⊢)
open import proof.CompileTyping
  using (≅-<; ≅-wf; ⤊-wf; ⊢ᴳ-wf; asFun-wf; asForall-wf)
open import proof.TermSubst using (cong₃)

------------------------------------------------------------------------
-- Typed precision derivations are well scoped
------------------------------------------------------------------------

⊑→WfPrec : ∀ {n p A B} → n ⊢ p ⦂ A ⊑ B → WfPrec n p
⊑→WfPrec ⊑★ = wfp★
⊑→WfPrec (⊑tag wfG p⊢) = wfptag wfG (⊑→WfPrec p⊢)
⊑→WfPrec (⊑‵ wfα) = wfp‵ wfα
⊑→WfPrec ⊑𝔹 = wfp𝔹
⊑→WfPrec (⊑⇒ p⊢ q⊢) = wfp⇒ (⊑→WfPrec p⊢) (⊑→WfPrec q⊢)
⊑→WfPrec (⊑∀ p⊢) = wfp∀ (⊑→WfPrec p⊢)

------------------------------------------------------------------------
-- Substituting well-formed names
------------------------------------------------------------------------

WfPrec-subst : ∀ {σ n m p} → WfRen σ n m → WfPrec n p
  → WfPrec m (substᵖ σ p)
WfPrec-subst σwf wfp★ = wfp★
WfPrec-subst σwf (wfptag wfG wfp) =
  wfptag (substG-wf σwf wfG) (WfPrec-subst σwf wfp)
WfPrec-subst σwf (wfp‵ {α = α} wfα) = wfp‵ (substₙ-wf α σwf wfα)
WfPrec-subst σwf wfp𝔹 = wfp𝔹
WfPrec-subst σwf (wfp⇒ wfp wfq) =
  wfp⇒ (WfPrec-subst σwf wfp) (WfPrec-subst σwf wfq)
WfPrec-subst σwf (wfp∀ wfp) = wfp∀ (WfPrec-subst (extₙ-wf σwf) wfp)

WfStack-subst : ∀ {σ n m cs} → WfRen σ n m → WfStack n cs
  → WfStack m (substˢ σ cs)
WfStack-subst σwf wfs[] = wfs[]
WfStack-subst σwf (wfs∷ wfp wfcs) =
  wfs∷ (WfPrec-subst σwf wfp) (WfStack-subst σwf wfcs)

Scoped-substᵀ : ∀ {σ n m M} → WfRen σ n m → Scoped n M
  → Scoped m (substᵀ σ M)
Scoped-substᵀ σwf sc` = sc`
Scoped-substᵀ σwf sc℧ = sc℧
Scoped-substᵀ σwf sctrue = sctrue
Scoped-substᵀ σwf scfalse = scfalse
Scoped-substᵀ σwf (scif sL sM sN) =
  scif (Scoped-substᵀ σwf sL) (Scoped-substᵀ σwf sM) (Scoped-substᵀ σwf sN)
Scoped-substᵀ σwf (scƛ wfA sM) =
  scƛ (substᵗ-wf σwf wfA) (Scoped-substᵀ σwf sM)
Scoped-substᵀ σwf (sc· sL sM) =
  sc· (Scoped-substᵀ σwf sL) (Scoped-substᵀ σwf sM)
Scoped-substᵀ σwf (scletv sM sN) =
  scletv (Scoped-substᵀ σwf sM) (Scoped-substᵀ σwf sN)
Scoped-substᵀ σwf (scseal {α = α} wfα sM) =
  scseal (substₙ-wf α σwf wfα) (Scoped-substᵀ σwf sM)
Scoped-substᵀ σwf (scunseal {α = α} wfα sM) =
  scunseal (substₙ-wf α σwf wfα) (Scoped-substᵀ σwf sM)
Scoped-substᵀ σwf (scis wfG sM) =
  scis (substG-wf σwf wfG) (Scoped-substᵀ σwf sM)
Scoped-substᵀ σwf (scinj wfG sM) =
  scinj (substG-wf σwf wfG) (Scoped-substᵀ σwf sM)
Scoped-substᵀ σwf (sccast wfp sM) =
  sccast (WfPrec-subst σwf wfp) (Scoped-substᵀ σwf sM)
Scoped-substᵀ σwf (scΛν wfcs sM) =
  scΛν (WfStack-subst (extₙ-wf σwf) wfcs)
       (Scoped-substᵀ (extₙ-wf σwf) sM)
Scoped-substᵀ σwf (scinst sM wfB sN) =
  scinst (Scoped-substᵀ σwf sM) (substᵗ-wf σwf wfB)
         (Scoped-substᵀ (extₙ-wf σwf) sN)

single-wf : ∀ {n s} → WfRen (singleₙ (tseal s)) (suc n) n
single-wf {i = zero} i<n = tt
single-wf {i = suc i} (s≤s i<n) = i<n

------------------------------------------------------------------------
-- Renaming and substituting term variables
------------------------------------------------------------------------

Scoped-rename : ∀ {n M} (r : Rename) → Scoped n M → Scoped n (rename r M)
Scoped-rename r sc` = sc`
Scoped-rename r sc℧ = sc℧
Scoped-rename r sctrue = sctrue
Scoped-rename r scfalse = scfalse
Scoped-rename r (scif sL sM sN) =
  scif (Scoped-rename r sL) (Scoped-rename r sM) (Scoped-rename r sN)
Scoped-rename r (scƛ wfA sM) = scƛ wfA (Scoped-rename (ext r) sM)
Scoped-rename r (sc· sL sM) = sc· (Scoped-rename r sL) (Scoped-rename r sM)
Scoped-rename r (scletv sM sN) =
  scletv (Scoped-rename r sM) (Scoped-rename (ext r) sN)
Scoped-rename r (scseal wfα sM) = scseal wfα (Scoped-rename r sM)
Scoped-rename r (scunseal wfα sM) = scunseal wfα (Scoped-rename r sM)
Scoped-rename r (scis wfG sM) = scis wfG (Scoped-rename r sM)
Scoped-rename r (scinj wfG sM) = scinj wfG (Scoped-rename r sM)
Scoped-rename r (sccast wfp sM) = sccast wfp (Scoped-rename r sM)
Scoped-rename r (scΛν wfcs sM) = scΛν wfcs (Scoped-rename r sM)
Scoped-rename r (scinst sM wfB sN) =
  scinst (Scoped-rename r sM) wfB (Scoped-rename (ext r) sN)

Scoped-exts : ∀ {n σ} → (∀ x → Scoped n (σ x)) → ∀ x → Scoped n (exts σ x)
Scoped-exts sσ zero = sc`
Scoped-exts sσ (suc x) = Scoped-rename suc (sσ x)

Scoped-⇑ˢ : ∀ {n σ} → (∀ x → Scoped n (σ x))
  → ∀ x → Scoped (suc n) (⇑ˢ σ x)
Scoped-⇑ˢ sσ x = Scoped-substᵀ ↑ₙ-wf (sσ x)

Scoped-subst : ∀ {n σ M} → (∀ x → Scoped n (σ x)) → Scoped n M
  → Scoped n (subst σ M)
Scoped-subst sσ (sc` {x = x}) = sσ x
Scoped-subst sσ sc℧ = sc℧
Scoped-subst sσ sctrue = sctrue
Scoped-subst sσ scfalse = scfalse
Scoped-subst sσ (scif sL sM sN) =
  scif (Scoped-subst sσ sL) (Scoped-subst sσ sM) (Scoped-subst sσ sN)
Scoped-subst sσ (scƛ wfA sM) = scƛ wfA (Scoped-subst (Scoped-exts sσ) sM)
Scoped-subst sσ (sc· sL sM) = sc· (Scoped-subst sσ sL) (Scoped-subst sσ sM)
Scoped-subst sσ (scletv sM sN) =
  scletv (Scoped-subst sσ sM) (Scoped-subst (Scoped-exts sσ) sN)
Scoped-subst sσ (scseal wfα sM) = scseal wfα (Scoped-subst sσ sM)
Scoped-subst sσ (scunseal wfα sM) = scunseal wfα (Scoped-subst sσ sM)
Scoped-subst sσ (scis wfG sM) = scis wfG (Scoped-subst sσ sM)
Scoped-subst sσ (scinj wfG sM) = scinj wfG (Scoped-subst sσ sM)
Scoped-subst sσ (sccast wfp sM) = sccast wfp (Scoped-subst sσ sM)
Scoped-subst sσ (scΛν wfcs sM) =
  scΛν wfcs (Scoped-subst (Scoped-⇑ˢ sσ) sM)
Scoped-subst sσ (scinst sM wfB sN) =
  scinst (Scoped-subst sσ sM) wfB
         (Scoped-subst (Scoped-exts (Scoped-⇑ˢ sσ)) sN)

Scoped-single : ∀ {n V} → Scoped n V → ∀ x → Scoped n (single V x)
Scoped-single sV zero = sV
Scoped-single sV (suc x) = sc`

------------------------------------------------------------------------
-- Stacks
------------------------------------------------------------------------

Scoped-stack : ∀ {n cs M} → WfStack n cs → Scoped n M
  → Scoped n (stack cs M)
Scoped-stack wfs[] sM = sM
Scoped-stack (wfs∷ wfp wfcs) sM = sccast wfp (Scoped-stack wfcs sM)

------------------------------------------------------------------------
-- Reduction preserves Scoped
------------------------------------------------------------------------

Scoped-step : ∀ {n Σ Σ′ M N} → Scoped n M → Σ ▷ M —→ Σ′ ▷ N → Scoped n N
Scoped-plug : ∀ {n Σ Σ′ F M N T}
  → Plug F M T → Scoped n T → Σ ▷ M —→ Σ′ ▷ N → Scoped n (plug F N)

Scoped-plug p-if (scif sL sM sN) s = scif (Scoped-step sL s) sM sN
Scoped-plug p-□· (sc· sL sM) s = sc· (Scoped-step sL s) sM
Scoped-plug p-app (sc· sV sM) s = sc· sV (Scoped-step sM s)
Scoped-plug p-letv (scletv sM sN) s = scletv (Scoped-step sM s) sN
Scoped-plug p-seal (scseal wfα sM) s = scseal wfα (Scoped-step sM s)
Scoped-plug p-unseal (scunseal wfα sM) s = scunseal wfα (Scoped-step sM s)
Scoped-plug p-is (scis wfG sM) s = scis wfG (Scoped-step sM s)
Scoped-plug p-inj (scinj wfG sM) s = scinj wfG (Scoped-step sM s)
Scoped-plug p-cast (sccast wfp sM) s = sccast wfp (Scoped-step sM s)
Scoped-plug p-inst (scinst sM wfB sN) s =
  scinst (Scoped-step sM s) wfB sN

Scoped-step sT (ξξ F eq refl s) = Scoped-plug (≡-Plug F eq) sT s
Scoped-step sM (ξξ-℧ F eq) = sc℧
Scoped-step (scletv sV sN) (β-letv v) = Scoped-subst (Scoped-single sV) sN
Scoped-step (scunseal wfα (scseal wfα′ sV)) (β-unseal v) = sV
Scoped-step (scis wfG sM) (β-is-yes v) = sctrue
Scoped-step (scis wfG sM) (β-is-no v G≢H) = scfalse
Scoped-step (scif sL sM sN) β-if-true = sM
Scoped-step (scif sL sM sN) β-if-false = sN
Scoped-step (sc· (scƛ wfA sM) sV) (β-ƛ v) =
  Scoped-subst (Scoped-single sV) sM
Scoped-step (sc· (sccast (wfp⇒ wfp wfq) sV) sW) (β-cast⇒ v w) =
  sccast wfq (sc· sV (sccast wfp sW))
Scoped-step (scinst (scΛν wfcs sM) wfB sN) β-inst =
  scletv (Scoped-substᵀ single-wf (Scoped-stack wfcs sM))
         (Scoped-substᵀ single-wf sN)
Scoped-step (sccast wfp sV) (β-id a v) = sV
Scoped-step (sccast (wfptag wfG wfp) sV) (β-tag-up v) =
  scinj wfG (sccast wfp sV)
Scoped-step (sccast (wfptag wfG wfp) (scinj wfH sV)) (β-tag-down v) =
  sccast wfp sV
Scoped-step (sccast wfp sV) (β-tag-down-℧ v G≢H) = sc℧
Scoped-step (sccast (wfp∀ wfp) (scΛν wfcs sM)) β-cast∀ =
  scΛν (wfs∷ wfp wfcs) sM

Scoped-steps : ∀ {n Σ Σ′ M N} → Scoped n M → Σ ▷ M —↠ Σ′ ▷ N
  → Scoped n N
Scoped-steps sM (M ∎) = sM
Scoped-steps sM (M —→⟨ s ⟩ M↠N) = Scoped-steps (Scoped-step sM s) M↠N

------------------------------------------------------------------------
-- Elaboration produces Scoped terms
------------------------------------------------------------------------

ascribe-Scoped : ∀ {n A B M} → WfTy n A → WfTy n B → Scoped n M
  → Scoped n (ascribe A B M)
ascribe-Scoped wfA wfB sM =
  sccast (⊑→WfPrec (dynᵖ-⊢ wfB)) (sccast (⊑→WfPrec (dynᵖ-⊢ wfA)) sM)

⇓-Scoped : ∀ {n G M} A → WfGround n G → Scoped n M
  → Scoped n (⇓ G A M)
⇓-Scoped (‵ α) wfG sM = sM
⇓-Scoped 𝔹 wfG sM = sM
⇓-Scoped ★ wfG sM =
  sccast (wfptag wfG (⊑→WfPrec (idᵖ-⊢ (groundTy-wf wfG)))) sM
⇓-Scoped (A ⇒ B) wfG sM = sM
⇓-Scoped (∀ν A) wfG sM = sM

elab-Scoped : ∀ {Δ Γ M A} → WfTyEnv Δ → WfCtx (tsize Δ) Γ
  → (d : Δ ∣ Γ ⊢ᴳ M ⦂ A) → Scoped (tsize Δ) (elab d)
elab-Scoped wfΔ wfΓ (⊢` x∈) = sc`
elab-Scoped wfΔ wfΓ (⊢⦂⦂ ⊢M A∼B wfB) =
  ascribe-Scoped (⊢ᴳ-wf wfΔ wfΓ ⊢M) wfB (elab-Scoped wfΔ wfΓ ⊢M)
elab-Scoped wfΔ wfΓ (⊢seal X≅A ⊢M B∼A) =
  scseal (≅-< X≅A)
    (ascribe-Scoped (⊢ᴳ-wf wfΔ wfΓ ⊢M) (≅-wf wfΔ X≅A)
       (elab-Scoped wfΔ wfΓ ⊢M))
elab-Scoped wfΔ wfΓ (⊢unseal {B = B} X≅A ⊢M B∼X) =
  scunseal (≅-< X≅A)
    (⇓-Scoped B (wfG‵ (≅-< X≅A)) (elab-Scoped wfΔ wfΓ ⊢M))
elab-Scoped wfΔ wfΓ (⊢is wfG ⊢M) =
  scis wfG (sccast (⊑→WfPrec (dynᵖ-⊢ (⊢ᴳ-wf wfΔ wfΓ ⊢M)))
                   (elab-Scoped wfΔ wfΓ ⊢M))
elab-Scoped wfΔ wfΓ ⊢true = sctrue
elab-Scoped wfΔ wfΓ ⊢false = scfalse
elab-Scoped wfΔ wfΓ (⊢if {A = A} ⊢L A∼𝔹 ⊢M ⊢N m) =
  scif (⇓-Scoped A wfG𝔹 (elab-Scoped wfΔ wfΓ ⊢L))
       (sccast (⊑→WfPrec (meetL-⊢ m wfBt wfBf)) (elab-Scoped wfΔ wfΓ ⊢M))
       (sccast (⊑→WfPrec (meetR-⊢ m wfBt wfBf)) (elab-Scoped wfΔ wfΓ ⊢N))
  where
  wfBt = ⊢ᴳ-wf wfΔ wfΓ ⊢M
  wfBf = ⊢ᴳ-wf wfΔ wfΓ ⊢N
elab-Scoped wfΔ wfΓ (⊢ƛ wfA ⊢M) =
  scƛ wfA (elab-Scoped wfΔ (wfc∷ wfA wfΓ) ⊢M)
elab-Scoped wfΔ wfΓ (⊢· {A = A} ⊢L shp ⊢M B∼A₁)
  with asFun-wf shp (⊢ᴳ-wf wfΔ wfΓ ⊢L)
elab-Scoped wfΔ wfΓ (⊢· {A = A} ⊢L shp ⊢M B∼A₁) | wfA₁ , wfA₂ =
  sc· (⇓-Scoped A wfG⇒ (elab-Scoped wfΔ wfΓ ⊢L))
      (ascribe-Scoped (⊢ᴳ-wf wfΔ wfΓ ⊢M) wfA₁ (elab-Scoped wfΔ wfΓ ⊢M))
elab-Scoped wfΔ wfΓ (⊢letv ⊢M ⊢N) =
  scletv (elab-Scoped wfΔ wfΓ ⊢M)
         (elab-Scoped wfΔ (wfc∷ (⊢ᴳ-wf wfΔ wfΓ ⊢M) wfΓ) ⊢N)
elab-Scoped wfΔ wfΓ (⊢Λν ⊢M) =
  scΛν wfs[] (elab-Scoped (wf-abs wfΔ) (⤊-wf wfΓ) ⊢M)
elab-Scoped wfΔ wfΓ (⊢inst {A = A} ⊢M shp wfB ⊢N wfC) =
  scinst (⇓-Scoped A wfG∀ (elab-Scoped wfΔ wfΓ ⊢M)) wfB
         (elab-Scoped (wf-known wfB wfΔ) (wfc∷ wfA₀ (⤊-wf wfΓ)) ⊢N)
  where
  wfA₀ = asForall-wf shp (⊢ᴳ-wf wfΔ wfΓ ⊢M)

------------------------------------------------------------------------
-- Closed labels, grounds and terms are fixed by name substitutions
------------------------------------------------------------------------

Fixes : NSubst → ℕ → Set
Fixes σ n = ∀ {i} → i < n → σ i ≡ tvar i

Fixes-ext : ∀ {σ n} → Fixes σ n → Fixes (extₙ σ) (suc n)
Fixes-ext eq {zero} i<n = refl
Fixes-ext eq {suc i} (s≤s i<n) = cong ⇑ₙ (eq i<n)

WfName-fix : ∀ {σ n} α → Fixes σ n → WfName n α → substₙ σ α ≡ α
WfName-fix (tvar i) eq i<n = eq i<n
WfName-fix (tseal s) eq tt = refl

WfGround-fix : ∀ {σ n G} → Fixes σ n → WfGround n G → substG σ G ≡ G
WfGround-fix eq (wfG‵ {α = α} wfα) = cong G‵ (WfName-fix α eq wfα)
WfGround-fix eq wfG𝔹 = refl
WfGround-fix eq wfG⇒ = refl
WfGround-fix eq wfG∀ = refl

WfPrec-fix : ∀ {σ n p} → Fixes σ n → WfPrec n p → substᵖ σ p ≡ p
WfPrec-fix eq wfp★ = refl
WfPrec-fix eq (wfptag wfG wfp) =
  cong₂ tag (WfGround-fix eq wfG) (WfPrec-fix eq wfp)
WfPrec-fix eq (wfp‵ {α = α} wfα) = cong ‵⊑ (WfName-fix α eq wfα)
WfPrec-fix eq wfp𝔹 = refl
WfPrec-fix eq (wfp⇒ wfp wfq) =
  cong₂ _⇒⊑_ (WfPrec-fix eq wfp) (WfPrec-fix eq wfq)
WfPrec-fix eq (wfp∀ wfp) = cong ∀⊑ (WfPrec-fix (Fixes-ext eq) wfp)

WfStack-fix : ∀ {σ n cs} → Fixes σ n → WfStack n cs → substˢ σ cs ≡ cs
WfStack-fix eq wfs[] = refl
WfStack-fix {cs = (d , p) ∷ cs} eq (wfs∷ wfp wfcs) =
  cong₂ (λ q cs′ → (d , q) ∷ cs′) (WfPrec-fix eq wfp) (WfStack-fix eq wfcs)

Scoped-fix : ∀ {σ n M} → Fixes σ n → Scoped n M → substᵀ σ M ≡ M
Scoped-fix eq sc` = refl
Scoped-fix eq sc℧ = refl
Scoped-fix eq sctrue = refl
Scoped-fix eq scfalse = refl
Scoped-fix eq (scif sL sM sN) =
  cong₃ if (Scoped-fix eq sL) (Scoped-fix eq sM) (Scoped-fix eq sN)
Scoped-fix eq (scƛ wfA sM) =
  cong₂ ƛ (substᵗ-wf-id eq wfA) (Scoped-fix eq sM)
Scoped-fix eq (sc· sL sM) = cong₂ _·_ (Scoped-fix eq sL) (Scoped-fix eq sM)
Scoped-fix eq (scletv sM sN) =
  cong₂ letv (Scoped-fix eq sM) (Scoped-fix eq sN)
Scoped-fix eq (scseal {α = α} wfα sM) =
  cong₂ seal (WfName-fix α eq wfα) (Scoped-fix eq sM)
Scoped-fix eq (scunseal {α = α} wfα sM) =
  cong₂ unseal (WfName-fix α eq wfα) (Scoped-fix eq sM)
Scoped-fix eq (scis wfG sM) =
  cong₂ is (WfGround-fix eq wfG) (Scoped-fix eq sM)
Scoped-fix eq (scinj wfG sM) =
  cong₂ inj (WfGround-fix eq wfG) (Scoped-fix eq sM)
Scoped-fix eq (sccast {d = d} wfp sM) =
  cong₂ (cast d) (WfPrec-fix eq wfp) (Scoped-fix eq sM)
Scoped-fix eq (scΛν wfcs sM) =
  cong₂ Λν (WfStack-fix (Fixes-ext eq) wfcs) (Scoped-fix (Fixes-ext eq) sM)
Scoped-fix eq (scinst sM wfB sN) =
  cong₃ inst (Scoped-fix eq sM) (substᵗ-wf-id eq wfB)
             (Scoped-fix (Fixes-ext eq) sN)

closed-prec : ∀ {σ p} → WfPrec 0 p → substᵖ σ p ≡ p
closed-prec = WfPrec-fix (λ ())

closed-ground : ∀ {σ G} → WfGround 0 G → substG σ G ≡ G
closed-ground = WfGround-fix (λ ())

closed-substᵀ : ∀ {σ M} → Scoped 0 M → substᵀ σ M ≡ M
closed-substᵀ = Scoped-fix (λ ())
