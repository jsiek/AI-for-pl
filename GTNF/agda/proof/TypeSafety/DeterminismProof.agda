module proof.TypeSafety.DeterminismProof where

-- File Charter:
--   * Proves GTNF determinism by cases on the first step, then the second.
--   * Congruence/congruence overlaps make their recursive calls here.
--   * The module is parameterized once by irreducibility, used to dismiss
--     root/frame and left/right evaluation-order overlaps.
--   * The carried readings are identified by `interior-functional` and
--     `conversion-functional`, the carried spellings by
--     `sameConv-src-unique` (Wrap, Merge) and `unique-lookup` (IdDyn-var),
--     and `InstX` is a function (`instX-det`).

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Maybe using (just)

open import Types
open import Ctx
open import proof.Ctx
open import Conversion
open import Coercion
open import Terms
open import Boundary
open import TermSubst
open import Reduction
open import TypeSafety
open import proof.TypeSafety.DeterminismDef

module Impl (irreducible : Irreducible) where

  value-no-step = proj₁ irreducible
  blame-no-step = proj₂ irreducible

  value-not-blame : ∀ {ℓ} → Value (blame ℓ) → ⊥
  value-not-blame (V-simple ())

  instX-det : ∀ {V N N′} → InstX V N → InstX V N′ → N ≡ N′
  instX-det (inst-Λ v) (inst-Λ v′) = refl
  instX-det (inst-gen w) (inst-gen w′) = refl
  instX-det (inst-∀ w i) (inst-∀ w′ i′)
    with instX-det i i′
  instX-det (inst-∀ w i) (inst-∀ w′ i′) | refl = refl
  instX-det (inst-⟪⟫ u i) (inst-⟪⟫ u′ i′)
    with instX-det i i′
  instX-det (inst-⟪⟫ u i) (inst-⟪⟫ u′ i′) | refl = refl

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  det : Determinism-Statement

  -- TyBeta
  det ⊢M (TyBeta v inst same) (TyBeta v′ inst′ same′)
    with same-rep-unique same same′ | instX-det inst inst′
  det ⊢M (TyBeta v inst same) (TyBeta v′ inst′ same′) | refl | refl =
    refl , refl
  det ⊢M (TyBeta v inst same) (ξ-ν st) = ⊥-elim (value-no-step v st)
  det ⊢M (TyBeta v inst same) Blame-ν = ⊥-elim (value-not-blame v)

  -- Beta
  det ⊢M (Beta vW) (Beta vW′) = refl , refl
  det ⊢M (Beta vW) (ξ-·₁ st) = ⊥-elim (value-no-step (V-simple S-ƛ) st)
  det ⊢M (Beta vW) (ξ-·₂ v st) = ⊥-elim (value-no-step vW st)
  det ⊢M (Beta vW) (Blame-·₂ v) = ⊥-elim (value-not-blame vW)

  -- Wrap: the dual's spelling is pinned by `sameConv-src-unique`
  det (⊢· (boundary mwΘ _ _ _ _ _) _)
      (Wrap u vW rc ri rd sc) (Wrap u′ vW′ rc′ ri′ rd′ sc′)
    with conversion-functional rc rc′ | interior-functional ri ri′
  det (⊢· (boundary mwΘ _ _ _ _ _) _)
      (Wrap u vW rc ri rd sc) (Wrap u′ vW′ rc′ ri′ rd′ sc′)
    | refl | refl with conversion-functional rd rd′
  det (⊢· (boundary mwΘ _ _ _ _ _) _)
      (Wrap u vW rc ri rd sc) (Wrap u′ vW′ rc′ ri′ rd′ sc′)
    | refl | refl | refl
    with sameConv-src-unique
           (dual-unique (name-fn (bw-exterior mwΘ)) ri rd) sc sc′
  det (⊢· (boundary mwΘ _ _ _ _ _) _)
      (Wrap u vW rc ri rd sc) (Wrap u′ vW′ rc′ ri′ rd′ sc′)
    | refl | refl | refl | refl = refl , refl
  det ⊢M (Wrap u vW rc ri rd sc) (ξ-·₁ st) =
    ⊥-elim (value-no-step (V-⟪⟫ u I-fun) st)
  det ⊢M (Wrap u vW rc ri rd sc) (ξ-·₂ v st) = ⊥-elim (value-no-step vW st)
  det ⊢M (Wrap u vW rc ri rd sc) (Blame-·₂ v) = ⊥-elim (value-not-blame vW)

  -- Merge: the readings are functions of the scopes, and the two carried
  -- spellings are pinned at the merged conversion context
  det (boundary mwΘ₂ _ _ _ _ _)
      (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) (Merge v′ ri′ r₁′ r₂′ r⋉′ sc₁′ sc₂′)
    with interior-functional ri ri′
  det (boundary mwΘ₂ _ _ _ _ _)
      (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) (Merge v′ ri′ r₁′ r₂′ r⋉′ sc₁′ sc₂′)
    | refl
    with conversion-functional r₁ r₁′ | conversion-functional r₂ r₂′
       | conversion-functional r⋉ r⋉′
  det (boundary mwΘ₂ _ _ _ _ _)
      (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) (Merge v′ ri′ r₁′ r₂′ r⋉′ sc₁′ sc₂′)
    | refl | refl | refl | refl
    with sameConv-src-unique
           (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sc₁ sc₁′
       | sameConv-src-unique
           (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sc₂ sc₂′
  det (boundary mwΘ₂ _ _ _ _ _)
      (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) (Merge v′ ri′ r₁′ r₂′ r⋉′ sc₁′ sc₂′)
    | refl | refl | refl | refl | refl | refl = refl , refl
  det ⊢M (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) (Id () b)
  det ⊢M (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) (ξ-⟪⟫ ri′ st) =
    ⊥-elim (value-no-step v st)

  -- Id
  det ⊢M (Id u b) (Id u′ b′) = refl , refl
  det ⊢M (Id () b) (Merge v ri r₁ r₂ r⋉ sc₁ sc₂)
  det ⊢M (Id u ()) (IdDyn v g)
  det ⊢M (Id u ()) (IdDyn-var v ext ri rc same)
  det ⊢M (Id () b) Blame-⟪⟫
  det ⊢M (Id u b) (ξ-⟪⟫ ri st) = ⊥-elim (value-no-step (V-simple u) st)

  -- the cast rules
  det ⊢M (CastId v) (CastId v′) = refl , refl
  det ⊢M (CastId v) Blame-cast = ⊥-elim (value-not-blame v)
  det ⊢M (CastId v) (ξ-cast st) = ⊥-elim (value-no-step v st)

  det ⊢M (CastSeq v) (CastSeq v′) = refl , refl
  det ⊢M (CastSeq v) Blame-cast = ⊥-elim (value-not-blame v)
  det ⊢M (CastSeq v) (ξ-cast st) = ⊥-elim (value-no-step v st)

  det ⊢M (CastFun vV vW) (CastFun vV′ vW′) = refl , refl
  det ⊢M (CastFun vV vW) (Blame-·₂ v) = ⊥-elim (value-not-blame vW)
  det ⊢M (CastFun vV vW) (ξ-·₁ st) =
    ⊥-elim (value-no-step (V-simple (S-cast vV I-↦)) st)
  det ⊢M (CastFun vV vW) (ξ-·₂ v st) = ⊥-elim (value-no-step vW st)

  det ⊢M (Inst v) (Inst v′) = refl , refl
  det ⊢M (Inst v) Blame-cast = ⊥-elim (value-not-blame v)
  det ⊢M (Inst v) (ξ-cast st) = ⊥-elim (value-no-step v st)

  det ⊢M (TagUntag v) (TagUntag v′) = refl , refl
  det ⊢M (TagUntag v) (TagUntagBad v′ ne) = ⊥-elim (ne refl)
  det ⊢M (TagUntag v) (ξ-cast st) =
    ⊥-elim (value-no-step (V-simple (S-cast v I-tag)) st)

  det ⊢M (TagUntagBad v ne) (TagUntag v′) = ⊥-elim (ne refl)
  det ⊢M (TagUntagBad v ne) (TagUntagBad v′ ne′) = refl , refl
  det ⊢M (TagUntagBad v ne) (ξ-cast st) =
    ⊥-elim (value-no-step (V-simple (S-cast v I-tag)) st)

  det ⊢M (IdDyn v g) (IdDyn v′ g′) = refl , refl
  det ⊢M (IdDyn v ()) (IdDyn-var v′ ext ri rc same)
  det ⊢M (IdDyn v g) (Id u ())
  det ⊢M (IdDyn v g) (ξ-⟪⟫ ri st) =
    ⊥-elim (value-no-step (V-simple (S-cast v I-tag)) st)

  -- the moved name's two spellings are functions of the scope
  det (boundary mw _ _ _ _ _)
      (IdDyn-var v ext ri rc (_ , same-var dᵢ , same-var dᶜ))
      (IdDyn-var v′ ext′ ri′ rc′ (_ , same-var dᵢ′ , same-var dᶜ′))
    with interior-functional ri ri′ | conversion-functional rc rc′
  det (boundary mw _ _ _ _ _)
      (IdDyn-var v ext ri rc (_ , same-var dᵢ , same-var dᶜ))
      (IdDyn-var v′ ext′ ri′ rc′ (_ , same-var dᵢ′ , same-var dᶜ′))
    | refl | refl with ∋ˡ-det dᵢ dᵢ′ | just-inj (trans (sym ext) ext′)
  det (boundary mw _ _ _ _ _)
      (IdDyn-var v ext ri rc (_ , same-var dᵢ , same-var dᶜ))
      (IdDyn-var v′ ext′ ri′ rc′ (_ , same-var dᵢ′ , same-var dᶜ′))
    | refl | refl | refl | refl
    with unique-lookup (conversion-unique (name-fn (bw-exterior mw)) rc)
                       dᶜ dᶜ′
  det (boundary mw _ _ _ _ _)
      (IdDyn-var v ext ri rc (_ , same-var dᵢ , same-var dᶜ))
      (IdDyn-var v′ ext′ ri′ rc′ (_ , same-var dᵢ′ , same-var dᶜ′))
    | refl | refl | refl | refl | refl = refl , refl
  det ⊢M (IdDyn-var v ext ri rc same) (IdDyn v′ ())
  det ⊢M (IdDyn-var v ext ri rc same) (Id u ())
  det ⊢M (IdDyn-var v ext ri rc same) (ξ-⟪⟫ ri′ st) =
    ⊥-elim (value-no-step (V-simple (S-cast v I-tag)) st)

  det ⊢M (TagUntagBad-⟪⟫ v fresh) (TagUntagBad-⟪⟫ v′ fresh′) = refl , refl
  det ⊢M (TagUntagBad-⟪⟫ v fresh) (ξ-cast st) =
    ⊥-elim (value-no-step (V-fresh v fresh) st)

  det ⊢M (BlameBotIntro v) (BlameBotIntro v′) = refl , refl
  det ⊢M (BlameBotIntro v) Blame-cast = ⊥-elim (value-not-blame v)
  det ⊢M (BlameBotIntro v) (ξ-cast st) = ⊥-elim (value-no-step v st)

  -- blame, one rule per frame
  det ⊢M Blame-·₁ Blame-·₁ = refl , refl
  det ⊢M Blame-·₁ (Blame-·₂ v) = ⊥-elim (value-not-blame v)
  det ⊢M Blame-·₁ (ξ-·₁ st) = ⊥-elim (blame-no-step st)
  det ⊢M Blame-·₁ (ξ-·₂ v st) = ⊥-elim (value-not-blame v)

  det ⊢M (Blame-·₂ v) (Beta vW) = ⊥-elim (value-not-blame vW)
  det ⊢M (Blame-·₂ v) (Wrap u vW rc ri rd sc) = ⊥-elim (value-not-blame vW)
  det ⊢M (Blame-·₂ v) (CastFun vV vW) = ⊥-elim (value-not-blame vW)
  det ⊢M (Blame-·₂ v) Blame-·₁ = ⊥-elim (value-not-blame v)
  det ⊢M (Blame-·₂ v) (Blame-·₂ v′) = refl , refl
  det ⊢M (Blame-·₂ v) (ξ-·₁ st) = ⊥-elim (value-no-step v st)
  det ⊢M (Blame-·₂ v) (ξ-·₂ v′ st) = ⊥-elim (blame-no-step st)

  det ⊢M Blame-ν (TyBeta v inst same) = ⊥-elim (value-not-blame v)
  det ⊢M Blame-ν Blame-ν = refl , refl
  det ⊢M Blame-ν (ξ-ν st) = ⊥-elim (blame-no-step st)

  det ⊢M Blame-⟪⟫ (Id () b)
  det ⊢M Blame-⟪⟫ Blame-⟪⟫ = refl , refl
  det ⊢M Blame-⟪⟫ (ξ-⟪⟫ ri st) = ⊥-elim (blame-no-step st)

  det ⊢M Blame-cast (CastId v) = ⊥-elim (value-not-blame v)
  det ⊢M Blame-cast (CastSeq v) = ⊥-elim (value-not-blame v)
  det ⊢M Blame-cast (Inst v) = ⊥-elim (value-not-blame v)
  det ⊢M Blame-cast (BlameBotIntro v) = ⊥-elim (value-not-blame v)
  det ⊢M Blame-cast Blame-cast = refl , refl
  det ⊢M Blame-cast (ξ-cast st) = ⊥-elim (blame-no-step st)

  -- the congruences: the sibling shift is a function of the store change
  det (⊢· ⊢L ⊢M) (ξ-·₁ st) (ξ-·₁ st′) with det ⊢L st st′
  det (⊢· ⊢L ⊢M) (ξ-·₁ st) (ξ-·₁ st′) | refl , refl = refl , refl
  det ⊢M (ξ-·₁ st) (Beta vW) = ⊥-elim (value-no-step (V-simple S-ƛ) st)
  det ⊢M (ξ-·₁ st) (Wrap u vW rc ri rd sc) =
    ⊥-elim (value-no-step (V-⟪⟫ u I-fun) st)
  det ⊢M (ξ-·₁ st) (CastFun vV vW) =
    ⊥-elim (value-no-step (V-simple (S-cast vV I-↦)) st)
  det ⊢M (ξ-·₁ st) Blame-·₁ = ⊥-elim (blame-no-step st)
  det ⊢M (ξ-·₁ st) (Blame-·₂ v) = ⊥-elim (value-no-step v st)
  det ⊢M (ξ-·₁ st) (ξ-·₂ v st′) = ⊥-elim (value-no-step v st)

  det (⊢· ⊢L ⊢M) (ξ-·₂ v st) (ξ-·₂ v′ st′) with det ⊢M st st′
  det (⊢· ⊢L ⊢M) (ξ-·₂ v st) (ξ-·₂ v′ st′) | refl , refl = refl , refl
  det ⊢M (ξ-·₂ v st) (Beta vW) = ⊥-elim (value-no-step vW st)
  det ⊢M (ξ-·₂ v st) (Wrap u vW rc ri rd sc) = ⊥-elim (value-no-step vW st)
  det ⊢M (ξ-·₂ v st) (CastFun vV vW) = ⊥-elim (value-no-step vW st)
  det ⊢M (ξ-·₂ v st) Blame-·₁ = ⊥-elim (value-not-blame v)
  det ⊢M (ξ-·₂ v st) (Blame-·₂ v′) = ⊥-elim (blame-no-step st)
  det ⊢M (ξ-·₂ v st) (ξ-·₁ st′) = ⊥-elim (value-no-step v st′)

  det (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) (ξ-ν st′)
      with det ⊢L st st′
  det (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) (ξ-ν st′) | refl , refl =
    refl , refl
  det ⊢M (ξ-ν st) (TyBeta v inst same) = ⊥-elim (value-no-step v st)
  det ⊢M (ξ-ν st) Blame-ν = ⊥-elim (blame-no-step st)

  det (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
      (ξ-⟪⟫ ri st) (ξ-⟪⟫ ri′ st′)
      with interior-functional ri (bw-interior mw)
         | interior-functional ri′ (bw-interior mw)
  det (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
      (ξ-⟪⟫ ri st) (ξ-⟪⟫ ri′ st′) | refl | refl with det ⊢M st st′
  det (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
      (ξ-⟪⟫ ri st) (ξ-⟪⟫ ri′ st′) | refl | refl | refl , refl =
    refl , refl
  det ⊢M (ξ-⟪⟫ ri st) (Merge v ri′ r₁ r₂ r⋉ sc₁ sc₂) =
    ⊥-elim (value-no-step v st)
  det ⊢M (ξ-⟪⟫ ri st) (Id u b) = ⊥-elim (value-no-step (V-simple u) st)
  det ⊢M (ξ-⟪⟫ ri st) (IdDyn v g) =
    ⊥-elim (value-no-step (V-simple (S-cast v I-tag)) st)
  det ⊢M (ξ-⟪⟫ ri st) (IdDyn-var v ext ri′ rc same) =
    ⊥-elim (value-no-step (V-simple (S-cast v I-tag)) st)
  det ⊢M (ξ-⟪⟫ ri st) Blame-⟪⟫ = ⊥-elim (blame-no-step st)

  det (⊢cast ⊢M ⊢p len) (ξ-cast st) (ξ-cast st′) with det ⊢M st st′
  det (⊢cast ⊢M ⊢p len) (ξ-cast st) (ξ-cast st′) | refl , refl =
    refl , refl
  det ⊢M (ξ-cast st) (CastId v) = ⊥-elim (value-no-step v st)
  det ⊢M (ξ-cast st) (CastSeq v) = ⊥-elim (value-no-step v st)
  det ⊢M (ξ-cast st) (Inst v) = ⊥-elim (value-no-step v st)
  det ⊢M (ξ-cast st) (TagUntag v) =
    ⊥-elim (value-no-step (V-simple (S-cast v I-tag)) st)
  det ⊢M (ξ-cast st) (TagUntagBad v ne) =
    ⊥-elim (value-no-step (V-simple (S-cast v I-tag)) st)
  det ⊢M (ξ-cast st) (TagUntagBad-⟪⟫ v fresh) =
    ⊥-elim (value-no-step (V-fresh v fresh) st)
  det ⊢M (ξ-cast st) (BlameBotIntro v) = ⊥-elim (value-no-step v st)
  det ⊢M (ξ-cast st) Blame-cast = ⊥-elim (blame-no-step st)
