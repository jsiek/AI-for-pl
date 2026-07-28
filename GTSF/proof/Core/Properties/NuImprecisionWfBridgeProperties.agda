module proof.Core.Properties.NuImprecisionWfBridgeProperties where

-- File Charter:
--   * Canonical bridge between legacy and well-formed indexed type imprecision.
--   * Forgets indexed derivations, reconstructs indexed derivations from
--     well-formed legacy ones, and supplies the target lifting and target-drop
--     support required by source-only `ν`.
--   * Contains no endpoint-MLB selection, cast typing, term relation, or
--     simulation result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Nat.Base using (s<s)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import Types
import Imprecision as Imp
open import Imprecision using (idᵢ; ⇑ᵢ)
open import ImprecisionWf
import proof.Core.Properties.ImprecisionProperties as ImpProps
open import proof.Core.Properties.ImprecisionProperties using
  ( no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star
  ; no-⇑ᴸᵢ-zero-left
  ; un⇑ᵢ-ˣ∈
  ; un⇑ᵢ-★∈
  ; un⇑ᴸᵢ-ˣ∈
  ; ⇑ᵢ-ˣ∈
  ; ⇑ᵢ-★∈
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties
  using
  ( ∀ᵢᶜ
  ; νᵢᶜ
  ; no-⇑ᴸᵢ-zero-star
  ; rename-assm²ᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²-★⇑ᵢ
  ; un⇑ᴸᵢ-★∈
  ; ⇑ᴸᵢ-ˣ∈
  ; ⇑ᴸᵢ-★∈
  ; ⊑-renameᵗ²ᵢ
  )
open import proof.Core.Properties.TypeProperties using
  ( occurs-zero-rename-ext
  ; rename-raise-ext
  ; renameᵗ-ext-suc-comm
  ; renameᵗ-id
  )

⊑-renameᵗ²-oldᵢ :
  ∀ {Φ Ψ ρ σ A B} →
  (∀ {a} → a ∈ Φ → rename-assm²ᵢ ρ σ a ∈ Ψ) →
  Imp._⊢_⊑_ Φ A B →
  Imp._⊢_⊑_ Ψ (renameᵗ ρ A) (renameᵗ σ B)
⊑-renameᵗ²-oldᵢ h Imp.id★ = Imp.id★
⊑-renameᵗ²-oldᵢ h (Imp.idˣ x∈) = Imp.idˣ (h x∈)
⊑-renameᵗ²-oldᵢ h Imp.idι = Imp.idι
⊑-renameᵗ²-oldᵢ h (p Imp.↦ q) =
  ⊑-renameᵗ²-oldᵢ h p Imp.↦ ⊑-renameᵗ²-oldᵢ h q
⊑-renameᵗ²-oldᵢ h (Imp.∀ⁱ p) =
  Imp.∀ⁱ (⊑-renameᵗ²-oldᵢ (rename-assm²-⇑ᵢ h) p)
⊑-renameᵗ²-oldᵢ h (Imp.tag ι) = Imp.tag ι
⊑-renameᵗ²-oldᵢ h (Imp.tag p ⇛ q) =
  Imp.tag (⊑-renameᵗ²-oldᵢ h p) ⇛ ⊑-renameᵗ²-oldᵢ h q
⊑-renameᵗ²-oldᵢ h (Imp.tagˣ x∈) = Imp.tagˣ (h x∈)
⊑-renameᵗ²-oldᵢ {ρ = ρ} {σ = σ} h
    (Imp.ν {A = A} {B = B} safe occA p) =
  Imp.ν (Imp.renameNonVar (extᵗ ρ) safe)
    (trans (occurs-zero-rename-ext ρ A) occA)
    (subst
      (λ B′ →
        Imp._⊢_⊑_ ((zero ˣ⊑★) ∷ ⇑ᵢ _)
          (renameᵗ (extᵗ ρ) A) B′)
      (renameᵗ-ext-suc-comm σ B)
      (⊑-renameᵗ²-oldᵢ
        {ρ = extᵗ ρ}
        {σ = extᵗ σ}
        (rename-assm²-★⇑ᵢ h)
        p))

rename-assm²-⇑ᴸ-to-⇑ᵢ :
  ∀ {Φ a} →
  a ∈ νᵢᶜ Φ →
  rename-assm²ᵢ (λ X → X) suc a ∈ (zero ˣ⊑★) ∷ ⇑ᵢ Φ
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = zero ˣ⊑★} (here refl) = here refl
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star a∈)
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = suc X ˣ⊑★} (here ())
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = suc X ˣ⊑★} (there a∈) =
  there (⇑ᵢ-★∈ (un⇑ᴸᵢ-★∈ a∈))
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = zero ˣ⊑ˣ Y} (here ())
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = zero ˣ⊑ˣ Y} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left a∈)
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = suc X ˣ⊑ˣ Y} (here ())
rename-assm²-⇑ᴸ-to-⇑ᵢ {a = suc X ˣ⊑ˣ Y} (there a∈) =
  there (⇑ᵢ-ˣ∈ (un⇑ᴸᵢ-ˣ∈ a∈))

⊑-target-liftνᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ⊢ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
⊑-target-liftνᵢ {Φ = Φ} {A = A} {B = B} p =
  subst
    (λ A′ →
      ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) ∣ _ ⊢ A′ ⊑ ⇑ᵗ B ⊣ _)
    (renameᵗ-id A)
    (⊑-renameᵗ²ᵢ
      {ρ = λ X → X}
      {σ = suc}
      rename-assm²-⇑ᴸ-to-⇑ᵢ
      (λ X<Δ → X<Δ)
      (λ Y<Δ → s<s Y<Δ)
      p)

old-target-liftᵢ :
  ∀ {Φ A B} →
  Imp._⊢_⊑_ (νᵢᶜ Φ) A B →
  Imp._⊢_⊑_ ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) A (⇑ᵗ B)
old-target-liftᵢ {Φ = Φ} {A = A} {B = B} p =
  subst
    (λ A′ → Imp._⊢_⊑_ ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) A′ (⇑ᵗ B))
    (renameᵗ-id A)
    (⊑-renameᵗ²-oldᵢ {ρ = λ X → X} {σ = suc}
      rename-assm²-⇑ᴸ-to-⇑ᵢ p)

⊑-forgetᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Imp._⊢_⊑_ Φ A B
⊑-forgetᵢ id★ = Imp.id★
⊑-forgetᵢ (idˣ x∈ X<Δᴸ Y<Δᴿ) = Imp.idˣ x∈
⊑-forgetᵢ idι = Imp.idι
⊑-forgetᵢ (p ↦ q) = ⊑-forgetᵢ p Imp.↦ ⊑-forgetᵢ q
⊑-forgetᵢ (∀ⁱ p) = Imp.∀ⁱ (⊑-forgetᵢ p)
⊑-forgetᵢ (tag ι) = Imp.tag ι
⊑-forgetᵢ (tag p ⇛ q) = Imp.tag (⊑-forgetᵢ p) ⇛ ⊑-forgetᵢ q
⊑-forgetᵢ (tagˣ x∈ X<Δᴸ) = Imp.tagˣ x∈
⊑-forgetᵢ (ν safe occA p) =
  Imp.ν safe occA (old-target-liftᵢ (⊑-forgetᵢ p))

record DropTargetCtxᵢ (k : TyVar) (Φ Ψ : ImpCtx) : Set where
  field
    drop-varᵗᵢ :
      ∀ {X Y} →
      (X ˣ⊑ˣ raiseVarFrom k Y) ∈ Φ →
      (X ˣ⊑ˣ Y) ∈ Ψ

    drop-starᵗᵢ :
      ∀ {X} →
      (X ˣ⊑★) ∈ Φ →
      (X ˣ⊑★) ∈ Ψ

open DropTargetCtxᵢ

drop-target-∀ᵢ :
  ∀ {k Φ Ψ} →
  DropTargetCtxᵢ k Φ Ψ →
  DropTargetCtxᵢ (suc k) (∀ᵢᶜ Φ) (∀ᵢᶜ Ψ)
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = zero} {Y = zero} (here refl) =
  here refl
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = zero} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = zero} {Y = suc Y} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = suc X} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-target-∀ᵢ drop .drop-varᵗᵢ {X = suc X} {Y = suc Y} (there x∈) =
  there (⇑ᵢ-ˣ∈ (drop-varᵗᵢ drop (un⇑ᵢ-ˣ∈ x∈)))
drop-target-∀ᵢ drop .drop-starᵗᵢ (here ())
drop-target-∀ᵢ drop .drop-starᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-target-∀ᵢ drop .drop-starᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᵢ-★∈ (drop-starᵗᵢ drop (un⇑ᵢ-★∈ x∈)))

drop-target-νᵢ :
  ∀ {k Φ Ψ} →
  DropTargetCtxᵢ k Φ Ψ →
  DropTargetCtxᵢ k (νᵢᶜ Φ) (νᵢᶜ Ψ)
drop-target-νᵢ drop .drop-varᵗᵢ (here ())
drop-target-νᵢ drop .drop-varᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-target-νᵢ drop .drop-varᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ (drop-varᵗᵢ drop (un⇑ᴸᵢ-ˣ∈ x∈)))
drop-target-νᵢ drop .drop-starᵗᵢ (here refl) = here refl
drop-target-νᵢ drop .drop-starᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x∈)
drop-target-νᵢ drop .drop-starᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-★∈ (drop-starᵗᵢ drop (un⇑ᴸᵢ-★∈ x∈)))

drop-target-zeroᵢ :
  ∀ {Φ} →
  DropTargetCtxᵢ zero ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) (νᵢᶜ Φ)
drop-target-zeroᵢ .drop-varᵗᵢ (here ())
drop-target-zeroᵢ .drop-varᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-target-zeroᵢ .drop-varᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ (un⇑ᵢ-ˣ∈ x∈))
drop-target-zeroᵢ .drop-starᵗᵢ (here refl) = here refl
drop-target-zeroᵢ .drop-starᵗᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-target-zeroᵢ .drop-starᵗᵢ {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-★∈ (un⇑ᵢ-★∈ x∈))

mutual
  drop-targetᵢ :
    ∀ {k Φ Ψ Δᴸ Δᴿ A B} →
    WfTy Δᴿ B →
    DropTargetCtxᵢ k Φ Ψ →
    Φ ∣ Δᴸ ⊢ A ⊑ renameᵗ (raiseVarFrom k) B ⊣ suc Δᴿ →
    Ψ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
  drop-targetᵢ wf★ drop id★ = id★
  drop-targetᵢ (wfVar Y<Δ) drop (idˣ x∈ X<Δ _) =
    idˣ (drop-varᵗᵢ drop x∈) X<Δ Y<Δ
  drop-targetᵢ wfBase drop idι = idι
  drop-targetᵢ (wf⇒ hA hB) drop (p ↦ q) =
    drop-targetᵢ hA drop p ↦ drop-targetᵢ hB drop q
  drop-targetᵢ {k = k} (wf∀ {A = B} hB) drop (∀ⁱ p)
      rewrite rename-raise-ext k B =
    ∀ⁱ (drop-targetᵢ hB (drop-target-∀ᵢ drop) p)
  drop-targetᵢ wf★ drop (tag ι) = tag ι
  drop-targetᵢ wf★ drop (tag p ⇛ q) =
    tag (drop-targetᵢ wf★ drop p) ⇛ drop-targetᵢ wf★ drop q
  drop-targetᵢ wf★ drop (tagˣ x∈ X<Δ) =
    tagˣ (drop-starᵗᵢ drop x∈) X<Δ
  drop-targetᵢ hB drop (ν safe occ p) =
    ν safe occ (drop-targetᵢ hB (drop-target-νᵢ drop) p)

old⊑→wfᵢ :
  ∀ {Δ Φ A B} →
  ImpProps.WfImpCtx Δ Φ →
  Imp._⊢_⊑_ Φ A B →
  Φ ∣ Δ ⊢ A ⊑ B ⊣ Δ
old⊑→wfᵢ hΦ Imp.id★ = id★
old⊑→wfᵢ hΦ (Imp.idˣ x∈) =
  idˣ x∈ (proj₁ (hΦ x∈)) (proj₂ (hΦ x∈))
old⊑→wfᵢ hΦ Imp.idι = idι
old⊑→wfᵢ hΦ (p Imp.↦ q) = old⊑→wfᵢ hΦ p ↦ old⊑→wfᵢ hΦ q
old⊑→wfᵢ hΦ (Imp.∀ⁱ p) =
  ∀ⁱ (old⊑→wfᵢ (ImpProps.∀ᵢ-wf hΦ) p)
old⊑→wfᵢ hΦ (Imp.tag ι) = tag ι
old⊑→wfᵢ hΦ (Imp.tag p ⇛ q) =
  tag (old⊑→wfᵢ hΦ p) ⇛ old⊑→wfᵢ hΦ q
old⊑→wfᵢ hΦ (Imp.tagˣ x∈) = tagˣ x∈ (hΦ x∈)
old⊑→wfᵢ hΦ r@(Imp.ν safe occ p) =
  ν safe occ
    (drop-targetᵢ
      (ImpProps.⊑-tgt-wf hΦ r)
      drop-target-zeroᵢ
      (old⊑→wfᵢ (ImpProps.νᵢ-wf hΦ) p))

old⊑→wf-idᵢ :
  ∀ {Δ A B} →
  Imp._⊢_⊑_ (idᵢ Δ) A B →
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ
old⊑→wf-idᵢ {Δ = Δ} = old⊑→wfᵢ (ImpProps.idᵢ-wf Δ)
