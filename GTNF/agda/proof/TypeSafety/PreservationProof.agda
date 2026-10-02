module proof.TypeSafety.PreservationProof where

-- File Charter:
--   * Proves preservation case by case over the reduction rules.
--   * Congruence cases make their recursive preservation calls; the
--     siblings a step shifts are re-typed by `⊢↑` (RepWeaken.shift-⊢).
--   * Also proves context well-formedness preservation (`step-alloc`:
--     only `TyBeta` allocates) and multi-step preservation.
--   * ONE HOLE IS LEFT, the `Inst` case: it is FALSE as GTNF stands
--     (proof/TypeSafety/notes/InstCloseCounterexample.agda).

open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_; length; map)
open import Data.List.Properties using (length-map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Types
open import Ctx
open import proof.Ctx
open import Conversion
open import Coercion
open import Terms
open import Boundary
open import Reduction
open import proof.TypeSafety.PreservationDef
open import proof.TypeSafety.PreservationSupport
open import proof.TypeSafety.RepWeaken
  using (shift-⊢; cross-Λ-⊢; coercion-renᴿ)
open import proof.TypeSafety.InstXTyping using (instX-⊢)
open import proof.TypeSafety.WrapDual using (preserve-Wrap)
open import proof.TypeSafety.MoveScope using (preserve-Merge)
open import proof.TypeSafety.Canonical using (≈-★-source)
open import proof.TypeSafety.ExitScope
  using (exitEnv-length; exit-tag-mode; toExt-sound)

------------------------------------------------------------------------
-- Support
------------------------------------------------------------------------

-- ONLY `TyBeta` ALLOCATES, and it carries the reading that makes the
-- created rep. var well formed.
step-alloc : ∀ {Δ M M′ δ} → WfCtx Δ → Δ ⊢ M -→ M′ ∣ δ → AllocWf δ Δ
step-alloc wfΔ (TyBeta v inst same) = aw-new (same-wfᴿ wfΔ same)
step-alloc wfΔ (Beta vW) = aw-none
step-alloc wfΔ (Wrap u vW rc ri rd sc) = aw-none
step-alloc wfΔ (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) = aw-none
step-alloc wfΔ (Id u b) = aw-none
step-alloc wfΔ (CastId v) = aw-none
step-alloc wfΔ (CastSeq v) = aw-none
step-alloc wfΔ (CastFun vV vW) = aw-none
step-alloc wfΔ (Inst v) = aw-none
step-alloc wfΔ (TagUntag v) = aw-none
step-alloc wfΔ (TagUntagBad v ne) = aw-none
step-alloc wfΔ (IdDyn v g) = aw-none
step-alloc wfΔ (IdDyn-var v ext ri rc same) = aw-none
step-alloc wfΔ (TagUntagBad-⟪⟫ v fresh) = aw-none
step-alloc wfΔ (BlameBotIntro v) = aw-none
step-alloc wfΔ Blame-·₁ = aw-none
step-alloc wfΔ (Blame-·₂ v) = aw-none
step-alloc wfΔ Blame-ν = aw-none
step-alloc wfΔ Blame-⟪⟫ = aw-none
step-alloc wfΔ Blame-cast = aw-none
step-alloc wfΔ (ξ-·₁ st) = step-alloc wfΔ st
step-alloc wfΔ (ξ-·₂ v st) = step-alloc wfΔ st
step-alloc wfΔ (ξ-ν st) = step-alloc wfΔ st
step-alloc wfΔ (ξ-⟪⟫ ri st) =
  aw-reps (interior-reps ri) (step-alloc (interior-wf wfΔ ri) st)
step-alloc wfΔ (ξ-cast st) = step-alloc wfΔ st

-- a coercion mentions no rep. var, so an allocation re-reads it as is
coercion-apply : ∀ {Δ μ p A B} {δ : Alloc}
  → AllocWf δ Δ
  → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B
  → apply δ Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B
coercion-apply aw-none ⊢p = ⊢p
coercion-apply (aw-new wR) ⊢p = coercion-renᴿ (repwk-alloc wR) ⊢p

length-apply : ∀ {Δ} {μ : ModeEnv} (δ : Alloc)
  → length μ ≡ length (names Δ)
  → length μ ≡ length (names (apply δ Δ))
length-apply none len = len
length-apply {Δ = Δ} (new R) len = trans len (sym (length-map suc (names Δ)))

ground-same : ∀ {η G} → GroundNV G → η ⊢ G ~ G
ground-same g-ℕ = same-ℕ
ground-same g-𝔹 = same-𝔹
ground-same g-⇒ = same-⇒ same-★ same-★
ground-same g-∀ = same-∀ same-★

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

preservation : Preservation-Statement
preservation wfΔ (⊢ν wA rA ⊢V mw ⊢c sameB wB) (TyBeta v inst same)
    with same-rep-unique rA same
preservation wfΔ (⊢ν wA rA ⊢V mw ⊢c sameB wB) (TyBeta v inst same)
    | refl =
  nu-outer mw (instX-⊢ wfΔ (same-wfᴿ wfΔ same) inst ⊢V) ⊢c sameB wB
preservation wfΔ ⊢M (Beta vW) = preserve-Beta cross-Λ-⊢ wfΔ ⊢M
preservation wfΔ ⊢M (Wrap u vW rc ri rd sc) =
  preserve-Wrap wfΔ u vW rc ri rd sc ⊢M
preservation wfΔ ⊢M (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) =
  preserve-Merge wfΔ ri r₁ r₂ r⋉ sc₁ sc₂ ⊢M
preservation wfΔ ⊢M (Id u b) = preserve-Id wfΔ u b ⊢M
preservation wfΔ (⊢cast ⊢V (⊢id wA) len) (CastId v) = ⊢V
preservation wfΔ (⊢cast ⊢V (⊢seq ⊢p ⊢q) len) (CastSeq v) =
  ⊢cast (⊢cast ⊢V ⊢p len) ⊢q len
preservation wfΔ (⊢· (⊢cast {μ = μ} ⊢V (⊢fun ⊢p ⊢q) len) ⊢W)
    (CastFun vV vW) =
  ⊢cast (⊢· ⊢V (⊢cast ⊢W ⊢p (trans (length-map flipᵐ μ) len))) ⊢q len
preservation wfΔ ⊢M (Inst v) = {!!}
preservation wfΔ (⊢cast (⊢cast ⊢V (⊢tag g) len) (⊢check g′) len′)
    (TagUntag v) = ⊢V
preservation wfΔ (⊢cast (⊢cast ⊢V (⊢tag ()) len) (⊢check-var tv md ok) len′)
    (TagUntag v)
preservation wfΔ (⊢cast (⊢cast ⊢V (⊢tag-var tv md ok) len) (⊢check ()) len′)
    (TagUntag v)
preservation wfΔ
    (⊢cast (⊢cast ⊢V (⊢tag-var tv md ok) len) (⊢check-var tv′ md′ ok′) len′)
    (TagUntag v) = ⊢V
preservation wfΔ ⊢M (TagUntagBad v ne) = ⊢blame (⊢ᵗ-of CtxWf-[] ⊢M)
preservation {Δ = Δ} wfΔ
    (boundary {Δᶜ = Δᶜ} mw (⊢cast {μ = μ} ⊢V (⊢tag g′) len)
       (conv-tail (conv-mid conv-id★)) sameᵢ sameₑ wE)
    (IdDyn {Θ = Θ} v g)
    with ≈-★-source {Δ = Δ} {Δ′ = Δᶜ} sameₑ
preservation {Δ = Δ} wfΔ
    (boundary {Δᶜ = Δᶜ} mw (⊢cast {μ = μ} ⊢V (⊢tag g′) len)
       (conv-tail (conv-mid conv-id★)) sameᵢ sameₑ wE)
    (IdDyn {Θ = Θ} v g)
    | refl =
  ⊢cast (boundary mw ⊢V (mkId-⊢ (ground-wf g))
           (_ , ground-same g , ground-same g)
           (_ , ground-same g , ground-same g) (ground-wf g))
        (⊢tag g) (exitEnv-length Θ μ (length (names Δ)))
preservation wfΔ
    (boundary mw (⊢cast ⊢V (⊢tag-var tv md ok) len)
       (conv-tail (conv-mid conv-id★)) sameᵢ sameₑ wE)
    (IdDyn v ())
preservation {Δ = Δ} wfΔ
    (boundary {Δᶜ = Δᶜ} mw@(bw wΔ (interior csᵢ) rc₀) (⊢cast {μ = μ} ⊢V ⊢tg len)
       (conv-tail (conv-mid conv-id★)) sameᵢ sameₑ wE)
    (IdDyn-var {Θ = Θ} v ext ri rc same)
    with ≈-★-source {Δ = Δ} {Δ′ = Δᶜ} sameₑ
       | interior-functional ri (bw-interior mw)
       | conversion-functional rc (bw-conversion mw)
preservation {Δ = Δ} wfΔ
    (boundary {Δᶜ = Δᶜ} mw@(bw wΔ (interior csᵢ) rc₀)
       (⊢cast {μ = μ} ⊢V (⊢tag ()) len)
       (conv-tail (conv-mid conv-id★)) sameᵢ sameₑ wE)
    (IdDyn-var {Θ = Θ} v ext ri rc same)
    | refl | refl | refl
preservation {Δ = Δ} wfΔ
    (boundary {Δᶜ = Δᶜ} mw@(bw wΔ (interior csᵢ) rc₀)
       (⊢cast {μ = μ} ⊢V (⊢tag-var tv md ok) len)
       (conv-tail (conv-mid conv-id★)) sameᵢ sameₑ wE)
    (IdDyn-var {Θ = Θ} v ext ri rc
       same@(` γ , same-var dᵢ , same-var dᶜ))
    | refl | refl | refl =
  ⊢cast (boundary mw ⊢V (conv-tail (conv-mid (conv-idv (γ , dᶜ)))) same
           (` γ , same-var dΔ , same-var dᶜ) (wf-var (γ , dΔ)))
        (⊢tag-var (γ , dΔ)
           (exit-tag-mode csᵢ (name-fn (bw-interior-wf mw)) len md dᵢ ext)
           ok)
        (exitEnv-length Θ μ (length (names Δ)))
  where
  dΔ = toExt-sound csᵢ dᵢ ext
preservation wfΔ ⊢M (TagUntagBad-⟪⟫ v fresh) = ⊢blame (⊢ᵗ-of CtxWf-[] ⊢M)
preservation wfΔ ⊢M (BlameBotIntro v) = ⊢blame (⊢ᵗ-of CtxWf-[] ⊢M)
preservation wfΔ ⊢M Blame-·₁ = ⊢blame (⊢ᵗ-of CtxWf-[] ⊢M)
preservation wfΔ ⊢M (Blame-·₂ v) = ⊢blame (⊢ᵗ-of CtxWf-[] ⊢M)
preservation wfΔ ⊢M Blame-ν = ⊢blame (⊢ᵗ-of CtxWf-[] ⊢M)
preservation wfΔ ⊢M Blame-⟪⟫ = ⊢blame (⊢ᵗ-of CtxWf-[] ⊢M)
preservation wfΔ ⊢M Blame-cast = ⊢blame (⊢ᵗ-of CtxWf-[] ⊢M)
preservation wfΔ (⊢· ⊢L ⊢M) (ξ-·₁ st)
    with preservation wfΔ ⊢L st
preservation wfΔ (⊢· ⊢L ⊢M) (ξ-·₁ st) | ⊢L′ =
  ⊢· ⊢L′ (⊢↑ shift-⊢ (step-alloc wfΔ st) ⊢M)
preservation wfΔ (⊢· ⊢L ⊢M) (ξ-·₂ v st)
    with preservation wfΔ ⊢M st
preservation wfΔ (⊢· ⊢L ⊢M) (ξ-·₂ v st) | ⊢M′ =
  ⊢· (⊢↑ shift-⊢ (step-alloc wfΔ st) ⊢L) ⊢M′
preservation wfΔ (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st)
    with preservation wfΔ ⊢L st
preservation wfΔ (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) | ⊢L′ =
  nu-apply (step-alloc wfΔ st) wA rA ⊢L′ mw ⊢c same wB
preservation wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
    (ξ-⟪⟫ ri st) with interior-functional ri (bw-interior mw)
preservation wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
    (ξ-⟪⟫ ri st) | refl with preservation (bw-interior-wf mw) ⊢M st
preservation wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
    (ξ-⟪⟫ ri st) | refl | ⊢M′ =
  boundary-apply
    (aw-reps (interior-reps ri) (step-alloc (bw-interior-wf mw) st))
    mw ⊢M′ ⊢c sameᵢ sameₑ wE
preservation wfΔ (⊢cast ⊢M ⊢p len) (ξ-cast st)
    with preservation wfΔ ⊢M st
preservation wfΔ (⊢cast {μ = μ} ⊢M ⊢p len) (ξ-cast {δ = δ} st) | ⊢M′ =
  ⊢cast ⊢M′ (coercion-apply (step-alloc wfΔ st) ⊢p)
        (length-apply {μ = μ} δ len)

preservation-wf : PreservationWf-Statement
preservation-wf wfΔ ⊢M (TyBeta v inst same) =
  alloc-wf wfΔ (same-wfᴿ wfΔ same)
preservation-wf wfΔ ⊢M (Beta vW) = wfΔ
preservation-wf wfΔ ⊢M (Wrap u vW rc ri rd sc) = wfΔ
preservation-wf wfΔ ⊢M (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) = wfΔ
preservation-wf wfΔ ⊢M (Id u b) = wfΔ
preservation-wf wfΔ ⊢M (CastId v) = wfΔ
preservation-wf wfΔ ⊢M (CastSeq v) = wfΔ
preservation-wf wfΔ ⊢M (CastFun vV vW) = wfΔ
preservation-wf wfΔ ⊢M (Inst v) = wfΔ
preservation-wf wfΔ ⊢M (TagUntag v) = wfΔ
preservation-wf wfΔ ⊢M (TagUntagBad v ne) = wfΔ
preservation-wf wfΔ ⊢M (IdDyn v g) = wfΔ
preservation-wf wfΔ ⊢M (IdDyn-var v ext ri rc same) = wfΔ
preservation-wf wfΔ ⊢M (TagUntagBad-⟪⟫ v fresh) = wfΔ
preservation-wf wfΔ ⊢M (BlameBotIntro v) = wfΔ
preservation-wf wfΔ ⊢M Blame-·₁ = wfΔ
preservation-wf wfΔ ⊢M (Blame-·₂ v) = wfΔ
preservation-wf wfΔ ⊢M Blame-ν = wfΔ
preservation-wf wfΔ ⊢M Blame-⟪⟫ = wfΔ
preservation-wf wfΔ ⊢M Blame-cast = wfΔ
preservation-wf wfΔ (⊢· ⊢L ⊢M) (ξ-·₁ st) =
  preservation-wf wfΔ ⊢L st
preservation-wf wfΔ (⊢· ⊢L ⊢M) (ξ-·₂ v st) =
  preservation-wf wfΔ ⊢M st
preservation-wf wfΔ (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) =
  preservation-wf wfΔ ⊢L st
preservation-wf wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE) (ξ-⟪⟫ ri st) =
  apply-wf wfΔ
    (aw-reps (interior-reps ri) (step-alloc (interior-wf wfΔ ri) st))
preservation-wf wfΔ (⊢cast ⊢M ⊢p len) (ξ-cast st) =
  preservation-wf wfΔ ⊢M st

preservation* : Preservation*-Statement
preservation* wfΔ ⊢M done = ⊢M
preservation* wfΔ ⊢M (st then sts) =
  preservation* (preservation-wf wfΔ ⊢M st)
                (preservation wfΔ ⊢M st) sts
