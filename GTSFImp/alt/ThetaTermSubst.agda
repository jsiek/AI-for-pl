module alt.ThetaTermSubst where

-- File Charter:
--   * Proves typing preservation for parallel term renaming and
--     regular-context injection renaming in the Θ-indexed calculus.
--   * Defines the action of regular-context injections on binder telescopes
--     and proves typing preservation for the general term action
--     `renameᵗᵐ` from alt.ThetaReduction.
--   * Historically, conceal pinned its conclusion telescope to a final
--     `,typ` entry.  Total slot deletion plus opaque anchors remove that
--     obstruction; this file now supplies literal Λ weakening, PLFA term
--     substitution, anchor shifting, and their deletion algebra.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import TermCtx
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

private
  variable
    Θ Θ′ : AnchorCtx
    Δ Δ′ : TyCtx
    Ψ Ψ′ : TyEnv Θ Δ
    Γ Γ′ : TermCtx Δ
    A B C : Ty Δ
    L M N : Term Θ Δ

------------------------------------------------------------------------
-- Injection identities used by telescope and conversion transport
------------------------------------------------------------------------

toRename-keep-eq : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) X
  → toRenameᵗ (keep ρ) X ≡ extᵗ (toRenameᵗ ρ) X
toRename-keep-eq ρ zero = refl
toRename-keep-eq ρ (suc X) = refl

toRename-id-eq : ∀ {Δ} (X : TyVar Δ)
  → toRenameᵗ id↪ᵗ X ≡ X
toRename-id-eq {zero} ()
toRename-id-eq {suc Δ} zero = refl
toRename-id-eq {suc Δ} (suc X) = cong suc (toRename-id-eq X)

toRename-wk-eq : ∀ {Δ} (X : TyVar Δ)
  → toRenameᵗ wk↪ᵗ X ≡ suc X
toRename-wk-eq X = cong suc (toRename-id-eq X)

renameᵗ-wk-eq : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (toRenameᵗ wk↪ᵗ) A ≡ ⇑ᵗ A
renameᵗ-wk-eq A = renameᵗ-cong A toRename-wk-eq

delete-insert↪ᵗ : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ))
  → delete↪ᵗ (insert↪ᵗ ρ Y) Y ≡ ρ
delete-insert↪ᵗ ρ zero = refl
delete-insert↪ᵗ (keep ρ) (suc Y) =
  cong keep (delete-insert↪ᵗ ρ Y)
delete-insert↪ᵗ (skip ρ) (suc Y) =
  cong skip (delete-insert↪ᵗ ρ (suc Y))

insert-punchIn : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ)) (X : TyVar Δ)
  → toRenameᵗ (insert↪ᵗ ρ Y) (punchIn Y X)
    ≡ punchIn (toRenameᵗ (insert↪ᵗ ρ Y) Y) (toRenameᵗ ρ X)
insert-punchIn ρ zero X = refl
insert-punchIn (keep ρ) (suc Y) zero = refl
insert-punchIn (keep ρ) (suc Y) (suc X) =
  cong suc (insert-punchIn ρ Y X)
insert-punchIn (skip ρ) (suc Y) X =
  cong suc (insert-punchIn ρ (suc Y) X)

delete-punchIn : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (X : TyVar Δ)
  → toRenameᵗ ρ (punchIn Y X)
    ≡ punchIn (toRenameᵗ ρ Y) (toRenameᵗ (delete↪ᵗ ρ Y) X)
delete-punchIn (keep ρ) zero X = refl
delete-punchIn (keep (keep ρ)) (suc Y) zero = refl
delete-punchIn (keep (keep ρ)) (suc Y) (suc X) =
  cong suc (delete-punchIn (keep ρ) Y X)
delete-punchIn (keep (skip ρ)) (suc Y) zero = refl
delete-punchIn (keep (skip ρ)) (suc Y) (suc X) =
  cong suc (delete-punchIn (skip ρ) Y X)
delete-punchIn (skip (keep ρ)) Y X =
  cong suc (delete-punchIn (keep ρ) Y X)
delete-punchIn (skip (skip ρ)) Y X =
  cong suc (delete-punchIn (skip ρ) Y X)

delete-keep-suc : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ))
  → delete↪ᵗ (keep ρ) (suc Y) ≡ keep (delete↪ᵗ ρ Y)
delete-keep-suc ρ Y = refl

delete-skip : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ))
  → delete↪ᵗ (skip ρ) Y ≡ skip (delete↪ᵗ ρ Y)
delete-skip ρ Y = refl

rename-insert-wk : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (insert↪ᵗ ρ Y)) (wkᵗ Y A)
    ≡ wkᵗ (toRenameᵗ (insert↪ᵗ ρ Y) Y)
        (renameᵗ (toRenameᵗ ρ) A)
rename-insert-wk ρ Y A =
  trans (renameᵗ-comp (punchIn Y)
           (toRenameᵗ (insert↪ᵗ ρ Y)) A)
    (trans (renameᵗ-cong A (insert-punchIn ρ Y))
      (sym (renameᵗ-comp (toRenameᵗ ρ)
        (punchIn (toRenameᵗ (insert↪ᵗ ρ Y) Y)) A)))

rename-delete-wk : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ ρ) (wkᵗ Y A)
    ≡ wkᵗ (toRenameᵗ ρ Y)
        (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) A)
rename-delete-wk ρ Y A =
  trans (renameᵗ-comp (punchIn Y) (toRenameᵗ ρ) A)
    (trans (renameᵗ-cong A (delete-punchIn ρ Y))
      (sym (renameᵗ-comp (toRenameᵗ (delete↪ᵗ ρ Y))
        (punchIn (toRenameᵗ ρ Y)) A)))

------------------------------------------------------------------------
-- Executable strengthening algebra
------------------------------------------------------------------------

fin-suc-injective : ∀ {n} {X Y : TyVar n}
  → suc X ≡ suc Y
  → X ≡ Y
fin-suc-injective refl = refl

punchIn≢ : ∀ {Δ} (Y : TyVar (suc Δ)) (X : TyVar Δ)
  → Y ≢ punchIn Y X
punchIn≢ zero X ()
punchIn≢ (suc Y) zero ()
punchIn≢ (suc Y) (suc X) eq =
  punchIn≢ Y X (fin-suc-injective eq)

punchOut-punchIn : ∀ {Δ} (Y : TyVar (suc Δ)) (X : TyVar Δ)
    (Y≢X : Y ≢ punchIn Y X)
  → punchOut Y (punchIn Y X) Y≢X ≡ X
punchOut-punchIn zero X Y≢X = refl
punchOut-punchIn (suc Y) zero Y≢X = refl
punchOut-punchIn (suc Y) (suc X) Y≢X =
  cong suc (punchOut-punchIn Y X _)

ext-punchIn-eq : ∀ {Δ} (Y : TyVar (suc Δ)) X
  → extᵗ (punchIn Y) X ≡ punchIn (suc Y) X
ext-punchIn-eq Y zero = refl
ext-punchIn-eq Y (suc X) = refl

strengthen-wk : ∀ {Δ} (Y : TyVar (suc Δ)) (A : Ty Δ)
  → strengthenᵗ? Y (wkᵗ Y A) ≡ just A
strengthen-wk Y (＇ X) with Y ≟ punchIn Y X
strengthen-wk Y (＇ X) | yes Y≡X = ⊥-elim (punchIn≢ Y X Y≡X)
strengthen-wk Y (＇ X) | no Y≢X
    rewrite punchOut-punchIn Y X Y≢X =
  refl
strengthen-wk Y (‵ ι) = refl
strengthen-wk Y ★ = refl
strengthen-wk Y (A ⇒ B)
    rewrite strengthen-wk Y A | strengthen-wk Y B =
  refl
strengthen-wk Y (`∀ A)
    rewrite renameᵗ-cong A (ext-punchIn-eq Y)
      | strengthen-wk (suc Y) A =
  refl

∖-:=wk : ∀ {Θ Δ} (Ψ : TyEnv Θ (suc Δ))
    (Y : TyVar (suc Δ)) (A : Ty Δ)
  → (Ψ ,:= wkᵗ Y A) ∖ Y ≡ (Ψ ∖ Y) ,:= A
∖-:=wk Ψ Y A rewrite strengthen-wk Y A = refl

∖-opaque : ∀ {Θ Δ} (Ψ : TyEnv Θ (suc Δ))
    (Y : TyVar (suc Δ))
  → (Ψ ,opaque) ∖ Y ≡ (Ψ ∖ Y) ,opaque
∖-opaque Ψ Y = refl

∖-typ-zero-suc : ∀ {Θ Δ} (Ψ : TyEnv Θ (suc Δ))
    (Y : TyVar (suc Δ))
  → (Ψ ,typ[ zero ]) ∖ suc Y ≡ (Ψ ∖ Y) ,typ[ zero ]
∖-typ-zero-suc Ψ Y = refl

∖-typ-here : ∀ {Θ Δ} (Ψ : TyEnv Θ Δ) (Y : TyVar (suc Δ))
  → (Ψ ,typ[ Y ]) ∖ Y ≡ Ψ
∖-typ-here {Δ = zero} Ψ zero = refl
∖-typ-here {Δ = suc Δ} Ψ Y with Y ≟ Y
∖-typ-here {Δ = suc Δ} Ψ Y | yes refl = refl
∖-typ-here {Δ = suc Δ} Ψ Y | no Y≢Y = ⊥-elim (Y≢Y refl)

punchOut-proof : ∀ {n} (Y X : TyVar (suc n))
    (p q : Y ≢ X)
  → punchOut Y X p ≡ punchOut Y X q
punchOut-proof zero zero p q = ⊥-elim (p refl)
punchOut-proof zero (suc X) p q = refl
punchOut-proof (suc Y) zero p q = refl
punchOut-proof {n = suc n} (suc Y) (suc X) p q =
  cong suc (punchOut-proof Y X _ _)

∖-typ-other : ∀ {Θ Δ} (Ψ : TyEnv Θ (suc Δ))
    (X Y : TyVar (suc (suc Δ)))
    (X≢Y : X ≢ Y) (Y≢X : Y ≢ X)
  → (Ψ ,typ[ X ]) ∖ Y
    ≡ (Ψ ∖ punchOut X Y X≢Y) ,typ[ punchOut Y X Y≢X ]
∖-typ-other Ψ X Y X≢Y Y≢X with X ≟ Y
∖-typ-other Ψ X .X X≢Y Y≢X | yes refl = ⊥-elim (X≢Y refl)
∖-typ-other Ψ X Y X≢Y Y≢X | no X≢Y′
    rewrite punchOut-proof X Y X≢Y′ X≢Y
      | punchOut-proof Y X (λ Y≡X → X≢Y′ (sym Y≡X)) Y≢X =
  refl

toRenameᵗ-injective : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
  → ∀ {X Y} → toRenameᵗ ρ X ≡ toRenameᵗ ρ Y → X ≡ Y
toRenameᵗ-injective empty {()}
toRenameᵗ-injective (keep ρ) {zero} {zero} eq = refl
toRenameᵗ-injective (keep ρ) {zero} {suc Y} ()
toRenameᵗ-injective (keep ρ) {suc X} {zero} ()
toRenameᵗ-injective (keep ρ) {suc X} {suc Y} eq =
  cong suc (toRenameᵗ-injective ρ (fin-suc-injective eq))
toRenameᵗ-injective (skip ρ) eq =
  toRenameᵗ-injective ρ (fin-suc-injective eq)

rename-punchOut : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y X : TyVar (suc Δ)) (Y≢X : Y ≢ X)
    (ρY≢ρX : toRenameᵗ ρ Y ≢ toRenameᵗ ρ X)
  → toRenameᵗ (delete↪ᵗ ρ Y) (punchOut Y X Y≢X)
    ≡ punchOut (toRenameᵗ ρ Y) (toRenameᵗ ρ X) ρY≢ρX
rename-punchOut (keep ρ) zero zero Y≢X ρY≢ρX =
  ⊥-elim (Y≢X refl)
rename-punchOut (keep ρ) zero (suc X) Y≢X ρY≢ρX = refl
rename-punchOut {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (keep ρ)) (suc Y) zero Y≢X ρY≢ρX
    rewrite delete-keep-suc (keep ρ) Y =
  refl
rename-punchOut {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (keep ρ)) (suc Y) (suc X) Y≢X ρY≢ρX
    rewrite delete-keep-suc (keep ρ) Y =
  cong suc (rename-punchOut (keep ρ) Y X
    (λ eq → Y≢X (cong suc eq))
    (λ eq → ρY≢ρX (cong suc eq)))
rename-punchOut {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (skip ρ)) (suc Y) zero Y≢X ρY≢ρX
    rewrite delete-keep-suc (skip ρ) Y =
  refl
rename-punchOut {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (skip ρ)) (suc Y) (suc X) Y≢X ρY≢ρX
    rewrite delete-keep-suc (skip ρ) Y =
  cong suc (rename-punchOut (skip ρ) Y X
    (λ eq → Y≢X (cong suc eq))
    (λ eq → ρY≢ρX (cong suc eq)))
rename-punchOut (skip (keep ρ)) Y X Y≢X ρY≢ρX
    rewrite delete-skip (keep ρ) Y =
  cong suc (rename-punchOut (keep ρ) Y X Y≢X
    (λ eq → ρY≢ρX (cong suc eq)))
rename-punchOut (skip (skip ρ)) Y X Y≢X ρY≢ρX
    rewrite delete-skip (skip ρ) Y =
  cong suc (rename-punchOut (skip ρ) Y X Y≢X
    (λ eq → ρY≢ρX (cong suc eq)))

delete-delete↪ᵗ : ∀ {Δ Δ′} (ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′))
    (X Y : TyVar (suc (suc Δ)))
    (X≢Y : X ≢ Y) (Y≢X : Y ≢ X)
  → delete↪ᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y)
    ≡ delete↪ᵗ (delete↪ᵗ ρ Y) (punchOut Y X Y≢X)
delete-delete↪ᵗ (keep ρ) zero zero X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ (keep ρ) zero (suc Y) X≢Y Y≢X = refl
delete-delete↪ᵗ (keep ρ) (suc X) zero X≢Y Y≢X = refl
delete-delete↪ᵗ {Δ′ = zero} (keep (keep empty))
    (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = zero} {Δ′ = suc Δ′}
    (keep (keep ρ)) (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = zero} {Δ′ = suc Δ′}
    (keep (skip ρ)) (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (keep ρ)) (suc X) (suc Y) X≢Y Y≢X
    rewrite delete-keep-suc (keep ρ) X
      | delete-keep-suc (keep ρ) Y
      | delete-keep-suc (delete↪ᵗ (keep ρ) X)
          (punchOut X Y (λ eq → X≢Y (cong suc eq)))
      | delete-keep-suc (delete↪ᵗ (keep ρ) Y)
          (punchOut Y X (λ eq → Y≢X (cong suc eq))) =
  cong keep (delete-delete↪ᵗ (keep ρ) X Y
    (λ eq → X≢Y (cong suc eq))
    (λ eq → Y≢X (cong suc eq)))
delete-delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (skip ρ)) (suc X) (suc Y) X≢Y Y≢X
    rewrite delete-keep-suc (skip ρ) X
      | delete-keep-suc (skip ρ) Y
      | delete-keep-suc (delete↪ᵗ (skip ρ) X)
          (punchOut X Y (λ eq → X≢Y (cong suc eq)))
      | delete-keep-suc (delete↪ᵗ (skip ρ) Y)
          (punchOut Y X (λ eq → Y≢X (cong suc eq))) =
  cong keep (delete-delete↪ᵗ (skip ρ) X Y
    (λ eq → X≢Y (cong suc eq))
    (λ eq → Y≢X (cong suc eq)))
delete-delete↪ᵗ (skip ρ) zero zero X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ′ = suc Δ′}
    (skip (keep ρ)) zero (suc Y) X≢Y Y≢X
    rewrite delete-skip (keep ρ) zero
      | delete-skip (keep ρ) (suc Y)
      | delete-skip (delete↪ᵗ (keep ρ) zero) Y
      | delete-skip (delete↪ᵗ (keep ρ) (suc Y)) zero =
  cong skip (delete-delete↪ᵗ (keep ρ) zero (suc Y) X≢Y Y≢X)
delete-delete↪ᵗ {Δ′ = suc Δ′}
    (skip (skip ρ)) zero (suc Y) X≢Y Y≢X
    rewrite delete-skip (skip ρ) zero
      | delete-skip (skip ρ) (suc Y)
      | delete-skip (delete↪ᵗ (skip ρ) zero) Y
      | delete-skip (delete↪ᵗ (skip ρ) (suc Y)) zero =
  cong skip (delete-delete↪ᵗ (skip ρ) zero (suc Y) X≢Y Y≢X)
delete-delete↪ᵗ {Δ′ = suc Δ′}
    (skip (keep ρ)) (suc X) zero X≢Y Y≢X
    rewrite delete-skip (keep ρ) (suc X)
      | delete-skip (keep ρ) zero
      | delete-skip (delete↪ᵗ (keep ρ) (suc X)) zero
      | delete-skip (delete↪ᵗ (keep ρ) zero) X =
  cong skip (delete-delete↪ᵗ (keep ρ) (suc X) zero X≢Y Y≢X)
delete-delete↪ᵗ {Δ′ = suc Δ′}
    (skip (skip ρ)) (suc X) zero X≢Y Y≢X
    rewrite delete-skip (skip ρ) (suc X)
      | delete-skip (skip ρ) zero
      | delete-skip (delete↪ᵗ (skip ρ) (suc X)) zero
      | delete-skip (delete↪ᵗ (skip ρ) zero) X =
  cong skip (delete-delete↪ᵗ (skip ρ) (suc X) zero X≢Y Y≢X)
delete-delete↪ᵗ {Δ = zero} {Δ′ = suc Δ′}
    (skip (keep ρ)) (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = zero} {Δ′ = suc Δ′}
    (skip (skip ρ)) (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′}
    (skip (keep ρ)) (suc X) (suc Y) X≢Y Y≢X
    rewrite delete-skip (keep ρ) (suc X)
      | delete-skip (keep ρ) (suc Y)
      | delete-skip (delete↪ᵗ (keep ρ) (suc X))
          (suc (punchOut X Y (λ eq → X≢Y (cong suc eq))))
      | delete-skip (delete↪ᵗ (keep ρ) (suc Y))
          (suc (punchOut Y X (λ eq → Y≢X (cong suc eq)))) =
  cong skip (delete-delete↪ᵗ (keep ρ) (suc X) (suc Y) X≢Y Y≢X)
delete-delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′}
    (skip (skip ρ)) (suc X) (suc Y) X≢Y Y≢X
    rewrite delete-skip (skip ρ) (suc X)
      | delete-skip (skip ρ) (suc Y)
      | delete-skip (delete↪ᵗ (skip ρ) (suc X))
          (suc (punchOut X Y (λ eq → X≢Y (cong suc eq))))
      | delete-skip (delete↪ᵗ (skip ρ) (suc Y))
          (suc (punchOut Y X (λ eq → Y≢X (cong suc eq)))) =
  cong skip (delete-delete↪ᵗ (skip ρ) (suc X) (suc Y) X≢Y Y≢X)

strengthen-rename : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (A : Ty (suc Δ))
  → strengthenᵗ? (toRenameᵗ ρ Y) (renameᵗ (toRenameᵗ ρ) A)
    ≡ map (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)))
        (strengthenᵗ? Y A)
strengthen-rename ρ Y (＇ X)
    with Y ≟ X | toRenameᵗ ρ Y ≟ toRenameᵗ ρ X
strengthen-rename ρ Y (＇ .Y) | yes refl | yes refl = refl
strengthen-rename ρ Y (＇ .Y) | yes refl | no Y≢Y =
  ⊥-elim (Y≢Y refl)
strengthen-rename ρ Y (＇ X) | no Y≢X | yes eq =
  ⊥-elim (Y≢X (toRenameᵗ-injective ρ eq))
strengthen-rename ρ Y (＇ X) | no Y≢X | no ρY≢ρX =
  cong just
    (cong ＇_ (sym (rename-punchOut ρ Y X Y≢X ρY≢ρX)))
strengthen-rename ρ Y (‵ ι) = refl
strengthen-rename ρ Y ★ = refl
strengthen-rename ρ Y (A ⇒ B)
    with strengthenᵗ? Y A
       | strengthenᵗ? (toRenameᵗ ρ Y) (renameᵗ (toRenameᵗ ρ) A)
       | strengthen-rename ρ Y A
strengthen-rename ρ Y (A ⇒ B) | nothing | .nothing | refl = refl
strengthen-rename ρ Y (A ⇒ B) | just A′
    | .(just (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) A′)) | refl
    with strengthenᵗ? Y B
       | strengthenᵗ? (toRenameᵗ ρ Y) (renameᵗ (toRenameᵗ ρ) B)
       | strengthen-rename ρ Y B
strengthen-rename ρ Y (A ⇒ B) | just A′
    | .(just (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) A′)) | refl
    | nothing | .nothing | refl = refl
strengthen-rename ρ Y (A ⇒ B) | just A′
    | .(just (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) A′)) | refl
    | just B′
    | .(just (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) B′)) | refl =
  refl
strengthen-rename ρ Y (`∀ A)
    rewrite delete-keep-suc ρ Y
      | sym (renameᵗ-cong A (toRename-keep-eq ρ))
    with strengthenᵗ? (suc Y) A
       | strengthenᵗ? (toRenameᵗ (keep ρ) (suc Y))
           (renameᵗ (toRenameᵗ (keep ρ)) A)
       | strengthen-rename (keep ρ) (suc Y) A
strengthen-rename ρ Y (`∀ A) | nothing | .nothing | refl = refl
strengthen-rename ρ Y (`∀ A) | just A′
    | .(just (renameᵗ (toRenameᵗ (keep (delete↪ᵗ ρ Y))) A′))
    | refl =
  cong just
    (cong `∀ (renameᵗ-cong A′
      (toRename-keep-eq (delete↪ᵗ ρ Y))))

------------------------------------------------------------------------
-- Conversion typing under regular-context injections
------------------------------------------------------------------------

renameAtom : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ}
  → Atom A
  → Atom (renameᵗ ρ A)
renameAtom ρ (＇ X) = ＇ ρ X
renameAtom ρ (‵ ι) = ‵ ι
renameAtom ρ ★ = ★

mutual
  rename-⊢↑ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
      {X : TyVar Δ} {R A B : Ty Δ} {c : Reveal}
    → ⊢↑[ X ⦂ R ] c ⦂ A ↝ B
    → ⊢↑[ ρ X ⦂ renameᵗ ρ R ] c
        ⦂ renameᵗ ρ A ↝ renameᵗ ρ B
  rename-⊢↑ ρ ⊢unseal = ⊢unseal
  rename-⊢↑ ρ (⊢↑-⇒ c⊢ d⊢) =
    ⊢↑-⇒ (rename-⊢↓ ρ c⊢) (rename-⊢↑ ρ d⊢)
  rename-⊢↑ ρ (⊢↑-∀ {R = R} c⊢) =
    ⊢↑-∀
      (subst≡
        (λ R′ → ⊢↑[ suc _ ⦂ R′ ] _ ⦂ _ ↝ _)
        (renameᵗ-shift ρ R)
        (rename-⊢↑ (extᵗ ρ) c⊢))
  rename-⊢↑ ρ (⊢id↑ a) = ⊢id↑ (renameAtom ρ a)

  rename-⊢↓ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
      {X : TyVar Δ} {R A B : Ty Δ} {c : Conceal}
    → ⊢↓[ X ⦂ R ] c ⦂ A ↝ B
    → ⊢↓[ ρ X ⦂ renameᵗ ρ R ] c
        ⦂ renameᵗ ρ A ↝ renameᵗ ρ B
  rename-⊢↓ ρ ⊢seal = ⊢seal
  rename-⊢↓ ρ (⊢↓-⇒ c⊢ d⊢) =
    ⊢↓-⇒ (rename-⊢↑ ρ c⊢) (rename-⊢↓ ρ d⊢)
  rename-⊢↓ ρ (⊢↓-∀ {R = R} c⊢) =
    ⊢↓-∀
      (subst≡
        (λ R′ → ⊢↓[ suc _ ⦂ R′ ] _ ⦂ _ ↝ _)
        (renameᵗ-shift ρ R)
        (rename-⊢↓ (extᵗ ρ) c⊢))
  rename-⊢↓ ρ (⊢id↓ a) = ⊢id↓ (renameAtom ρ a)

------------------------------------------------------------------------
-- Term-variable renaming preserves typing
------------------------------------------------------------------------

ext-∋ : ∀ {Δ} {Γ Γ′ : TermCtx Δ} {ρ : Rename} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
  → ∀ {x B} → A ∷ Γ ∋ x ⦂ B → A ∷ Γ′ ∋ ext ρ x ⦂ B
ext-∋ hρ Z = Z
ext-∋ hρ (S x∈) = S (hρ x∈)

lookup-renameCtx-inv : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {Γ : TermCtx Δ} {x A}
  → renameCtx ρ Γ ∋ x ⦂ A
  → ∃[ B ] (Γ ∋ x ⦂ B × renameᵗ ρ B ≡ A)
lookup-renameCtx-inv {Γ = B ∷ Γ} Z = B , Z , refl
lookup-renameCtx-inv {Γ = C ∷ Γ} (S x∈)
    with lookup-renameCtx-inv x∈
lookup-renameCtx-inv {Γ = C ∷ Γ} (S x∈) | B , B∈ , refl =
  B , S B∈ , refl

renameCtx-∋ : ∀ {Δ Δ′} {ρᵗ : Δ ⇒ʳ Δ′}
    {Γ Γ′ : TermCtx Δ} {ρ : Rename}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → ∀ {x A}
  → renameCtx ρᵗ Γ ∋ x ⦂ A
  → renameCtx ρᵗ Γ′ ∋ ρ x ⦂ A
renameCtx-∋ hρ x∈ with lookup-renameCtx-inv x∈
renameCtx-∋ {ρᵗ = ρᵗ} hρ x∈ | B , B∈ , refl =
  renameᵗ-∋ ρᵗ (hρ B∈)

⊢rename : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ Γ′ : TermCtx Δ}
    {ρ : Rename} {M : Term Θ Δ} {B : Ty Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → Ψ ∣ Γ ⊢ M ⦂ B
  → Ψ ∣ Γ′ ⊢ rename ρ M ⦂ B
⊢rename hρ (⊢` x∈) = ⊢` (hρ x∈)
⊢rename hρ (⊢ƛ M⊢) = ⊢ƛ (⊢rename (ext-∋ hρ) M⊢)
⊢rename hρ (⊢· L⊢ M⊢) =
  ⊢· (⊢rename hρ L⊢) (⊢rename hρ M⊢)
⊢rename hρ (⊢Λ M⊢) = ⊢Λ (⊢rename (renameCtx-∋ hρ) M⊢)
⊢rename hρ (⊢⦂∀ L⊢) = ⊢⦂∀ (⊢rename hρ L⊢)
⊢rename hρ (⊢$ κ) = ⊢$ κ
⊢rename hρ (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢rename hρ L⊢) (⊢rename hρ M⊢)
⊢rename hρ (⊢⟨⟩ M⊢ c) = ⊢⟨⟩ (⊢rename hρ M⊢) c
⊢rename hρ (⊢ν M⊢) = ⊢ν M⊢
⊢rename hρ (⊢reveal α∈ c⊢ M⊢) = ⊢reveal α∈ c⊢ M⊢
⊢rename hρ (⊢conceal α∈ c⊢ M⊢) = ⊢conceal α∈ c⊢ M⊢
⊢rename hρ ⊢blame = ⊢blame

⊢rename-suc : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Ψ ∣ B ∷ Γ ⊢ rename suc M ⦂ A
⊢rename-suc M⊢ = ⊢rename (λ x∈ → S x∈) M⊢

------------------------------------------------------------------------
-- Regular-context injections act on binder telescopes
------------------------------------------------------------------------

emptyTyEnv : ∀ {Θ} (Δ : TyCtx) → TyEnv Θ zero → TyEnv Θ Δ
emptyTyEnv zero Ψ = Ψ
emptyTyEnv (suc Δ) Ψ = emptyTyEnv Δ Ψ ,typ[ zero ]

renameTyEnv : ∀ {Θ Δ Δ′}
  → Δ ↪ᵗ Δ′
  → TyEnv Θ Δ
  → TyEnv Θ Δ′
renameTyEnv {Δ′ = Δ′} ρ ∅ = emptyTyEnv Δ′ ∅
renameTyEnv ρ (Ψ ,:= A) =
  renameTyEnv ρ Ψ ,:= renameᵗ (toRenameᵗ ρ) A
renameTyEnv ρ (Ψ ,opaque) = renameTyEnv ρ Ψ ,opaque
renameTyEnv (keep ρ) (Ψ ,typ[ Y ]) =
  renameTyEnv (delete↪ᵗ (keep ρ) Y) Ψ
    ,typ[ toRenameᵗ (keep ρ) Y ]
renameTyEnv (skip ρ) (Ψ ,typ[ Y ]) =
  renameTyEnv (delete↪ᵗ (skip ρ) Y) Ψ
    ,typ[ toRenameᵗ (skip ρ) Y ]

renameTyEnv-insert : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Ψ : TyEnv Θ Δ) (Y : TyVar (suc Δ))
  → renameTyEnv (insert↪ᵗ ρ Y) (Ψ ,typ[ Y ])
    ≡ renameTyEnv ρ Ψ ,typ[ toRenameᵗ (insert↪ᵗ ρ Y) Y ]
renameTyEnv-insert ρ Ψ zero = refl
renameTyEnv-insert (keep ρ) Ψ (suc Y)
    rewrite delete-insert↪ᵗ ρ Y =
  refl
renameTyEnv-insert (skip ρ) Ψ (suc Y)
    rewrite delete-insert↪ᵗ ρ (suc Y) =
  refl

rename-∋:= : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {Ψ : TyEnv Θ Δ} {α : TyVar Θ} {A : Ty Δ}
  → Ψ ∋ α := A
  → renameTyEnv ρ Ψ ∋ α := renameᵗ (toRenameᵗ ρ) A
rename-∋:= ρ Z = Z
rename-∋:= ρ (S α∈) = S (rename-∋:= ρ α∈)
rename-∋:= ρ (skip-opaque α∈) = skip-opaque (rename-∋:= ρ α∈)
rename-∋:= (keep ρ) (skip-typ {Ψ = Ψ} {A = A} {Y = Y} α∈) =
  subst≡
    (λ C → renameTyEnv (keep ρ) (Ψ ,typ[ Y ]) ∋ _ := C)
    (sym (rename-delete-wk (keep ρ) Y A))
    (skip-typ (rename-∋:= (delete↪ᵗ (keep ρ) Y) α∈))
rename-∋:= (skip ρ) (skip-typ {Ψ = Ψ} {A = A} {Y = Y} α∈) =
  subst≡
    (λ C → renameTyEnv (skip ρ) (Ψ ,typ[ Y ]) ∋ _ := C)
    (sym (rename-delete-wk (skip ρ) Y A))
    (skip-typ (rename-∋:= (delete↪ᵗ (skip ρ) Y) α∈))

renameTyEnv-typ : ∀ {Θ Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Ψ : TyEnv Θ Δ) (X : TyVar (suc Δ))
  → renameTyEnv ρ (Ψ ,typ[ X ])
    ≡ renameTyEnv (delete↪ᵗ ρ X) Ψ ,typ[ toRenameᵗ ρ X ]
renameTyEnv-typ (keep ρ) Ψ X = refl
renameTyEnv-typ (skip ρ) Ψ X = refl

renameTyEnv-∖-typ-other : ∀ {Θ Δ Δ′}
    (ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′))
    (Ψ : TyEnv Θ (suc Δ)) (X Y : TyVar (suc (suc Δ)))
    (X≢Y : X ≢ Y) (Y≢X : Y ≢ X)
  → renameTyEnv (delete↪ᵗ ρ X) Ψ
      ∖ toRenameᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y)
    ≡ renameTyEnv
        (delete↪ᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
        (Ψ ∖ punchOut X Y X≢Y)
  → (renameTyEnv (delete↪ᵗ ρ X) Ψ
       ∖ toRenameᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
      ,typ[ toRenameᵗ (delete↪ᵗ ρ Y) (punchOut Y X Y≢X) ]
    ≡ renameTyEnv (delete↪ᵗ ρ Y)
        ((Ψ ∖ punchOut X Y X≢Y)
          ,typ[ punchOut Y X Y≢X ])
renameTyEnv-∖-typ-other ρ Ψ X Y X≢Y Y≢X ih
    rewrite ih
      | delete-delete↪ᵗ ρ X Y X≢Y Y≢X
      | renameTyEnv-typ (delete↪ᵗ ρ Y)
          (Ψ ∖ punchOut X Y X≢Y) (punchOut Y X Y≢X) =
  refl

no-typ-case : ∀ {Θ Δ Δ′}
    (ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′))
    (Ψ : TyEnv Θ (suc Δ)) (X Y : TyVar (suc (suc Δ)))
    (X≢Y : X ≢ Y)
  → renameTyEnv (delete↪ᵗ ρ X) Ψ
      ∖ toRenameᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y)
    ≡ renameTyEnv
        (delete↪ᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
        (Ψ ∖ punchOut X Y X≢Y)
  → renameTyEnv ρ (Ψ ,typ[ X ]) ∖ toRenameᵗ ρ Y
    ≡ renameTyEnv (delete↪ᵗ ρ Y)
        ((Ψ ∖ punchOut X Y X≢Y)
          ,typ[ punchOut Y X (λ eq → X≢Y (sym eq)) ])
no-typ-case ρ Ψ X Y X≢Y ih =
  trans
    (cong (λ Ψ′ → Ψ′ ∖ toRenameᵗ ρ Y)
      (renameTyEnv-typ ρ Ψ X))
    (trans
      (∖-typ-other (renameTyEnv (delete↪ᵗ ρ X) Ψ)
        (toRenameᵗ ρ X) (toRenameᵗ ρ Y) ρX≢ρY ρY≢ρX)
      (trans
        (cong₂ (λ Ψ′ Z → Ψ′ ,typ[ Z ])
          (cong (λ Z → renameTyEnv (delete↪ᵗ ρ X) Ψ ∖ Z)
            (sym (rename-punchOut ρ X Y X≢Y ρX≢ρY)))
          (sym (rename-punchOut ρ Y X Y≢X ρY≢ρX)))
        (trans
          (renameTyEnv-∖-typ-other ρ Ψ X Y X≢Y Y≢X ih)
          (cong (renameTyEnv (delete↪ᵗ ρ Y))
            (cong (λ Z → (Ψ ∖ punchOut X Y X≢Y) ,typ[ Z ])
              (punchOut-proof Y X Y≢X
                (λ eq → X≢Y (sym eq))))))))
  where
  Y≢X = λ eq → X≢Y (sym eq)
  ρX≢ρY = λ eq → X≢Y (toRenameᵗ-injective ρ eq)
  ρY≢ρX = λ eq → Y≢X (toRenameᵗ-injective ρ eq)

renameTyEnv-∖ : ∀ {Θ Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Ψ : TyEnv Θ (suc Δ)) (Y : TyVar (suc Δ))
  → renameTyEnv ρ Ψ ∖ toRenameᵗ ρ Y
    ≡ renameTyEnv (delete↪ᵗ ρ Y) (Ψ ∖ Y)
renameTyEnv-∖ {Δ = zero} (keep ρ) (Ψ ,typ[ zero ]) zero
    rewrite ∖-typ-here (renameTyEnv ρ Ψ) zero
      | ∖-typ-here Ψ zero =
  refl
renameTyEnv-∖ {Δ = zero} (skip ρ) (Ψ ,typ[ zero ]) zero
    rewrite ∖-typ-here (renameTyEnv (delete↪ᵗ (skip ρ) zero) Ψ)
              (toRenameᵗ (skip ρ) zero)
      | ∖-typ-here Ψ zero =
  refl
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = zero} (keep ()) Ψ Y
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = zero} (skip ()) Ψ Y
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(keep (keep η)) (Ψ ,typ[ X ]) Y with X ≟ Y
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(keep (keep η)) (Ψ ,typ[ .Y ]) Y | yes refl
    rewrite ∖-typ-here (renameTyEnv (delete↪ᵗ ρ Y) Ψ)
              (toRenameᵗ ρ Y) =
  refl
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(keep (keep η)) (Ψ ,typ[ X ]) Y | no X≢Y =
  no-typ-case ρ Ψ X Y X≢Y
    (renameTyEnv-∖ (delete↪ᵗ ρ X) Ψ (punchOut X Y X≢Y))
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(keep (skip η)) (Ψ ,typ[ X ]) Y with X ≟ Y
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(keep (skip η)) (Ψ ,typ[ .Y ]) Y | yes refl
    rewrite ∖-typ-here (renameTyEnv (delete↪ᵗ ρ Y) Ψ)
              (toRenameᵗ ρ Y) =
  refl
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(keep (skip η)) (Ψ ,typ[ X ]) Y | no X≢Y =
  no-typ-case ρ Ψ X Y X≢Y
    (renameTyEnv-∖ (delete↪ᵗ ρ X) Ψ (punchOut X Y X≢Y))
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(skip (keep η)) (Ψ ,typ[ X ]) Y with X ≟ Y
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(skip (keep η)) (Ψ ,typ[ .Y ]) Y | yes refl
    rewrite ∖-typ-here (renameTyEnv (delete↪ᵗ ρ Y) Ψ)
              (toRenameᵗ ρ Y) =
  refl
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(skip (keep η)) (Ψ ,typ[ X ]) Y | no X≢Y =
  no-typ-case ρ Ψ X Y X≢Y
    (renameTyEnv-∖ (delete↪ᵗ ρ X) Ψ (punchOut X Y X≢Y))
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(skip (skip η)) (Ψ ,typ[ X ]) Y with X ≟ Y
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(skip (skip η)) (Ψ ,typ[ .Y ]) Y | yes refl
    rewrite ∖-typ-here (renameTyEnv (delete↪ᵗ ρ Y) Ψ)
              (toRenameᵗ ρ Y) =
  refl
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    ρ@(skip (skip η)) (Ψ ,typ[ X ]) Y | no X≢Y =
  no-typ-case ρ Ψ X Y X≢Y
    (renameTyEnv-∖ (delete↪ᵗ ρ X) Ψ (punchOut X Y X≢Y))
renameTyEnv-∖ ρ (Ψ ,:= A) Y
    with strengthenᵗ? Y A
       | strengthenᵗ? (toRenameᵗ ρ Y) (renameᵗ (toRenameᵗ ρ) A)
       | strengthen-rename ρ Y A
renameTyEnv-∖ ρ (Ψ ,:= A) Y | nothing | .nothing | refl =
  cong _,opaque (renameTyEnv-∖ ρ Ψ Y)
renameTyEnv-∖ ρ (Ψ ,:= A) Y | just C
    | .(just (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) C)) | refl =
  cong₂ _,:=_ (renameTyEnv-∖ ρ Ψ Y) refl
renameTyEnv-∖ ρ (Ψ ,opaque) Y =
  cong _,opaque (renameTyEnv-∖ ρ Ψ Y)

------------------------------------------------------------------------
-- Alternative targets for regular-context renaming
------------------------------------------------------------------------

-- The canonical target `renameTyEnv ρ Ψ` is convenient for arbitrary
-- injections.  Λ descent needs the literal target `Ψ ,typ[ zero ]` for
-- weakening at zero.  This relation records both choices and is stable under
-- the telescope extensions and deletions used by the typing rules.

data RenameTarget : ∀ {Θ Δ Δ′}
    (ρ : Δ ↪ᵗ Δ′) → TyEnv Θ Δ → TyEnv Θ Δ′ → Set where
  canonical-target : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ}
      --------------------------------------------------
    → RenameTarget ρ Ψ (renameTyEnv ρ Ψ)

  literal-wk-target : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      -------------------------------------------
    → RenameTarget wk↪ᵗ Ψ (Ψ ,typ[ zero ])

  target-typ : ∀ {Θ Δ Δ′}
      {ρ : suc Δ ↪ᵗ suc Δ′} {Ψ : TyEnv Θ Δ}
      {Φ : TyEnv Θ Δ′} (X : TyVar (suc Δ))
    → RenameTarget (delete↪ᵗ ρ X) Ψ Φ
      --------------------------------------------------------------
    → RenameTarget ρ (Ψ ,typ[ X ])
        (Φ ,typ[ toRenameᵗ ρ X ])

  target-:= : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′} {A : Ty Δ}
    → RenameTarget ρ Ψ Φ
      --------------------------------------------------
    → RenameTarget ρ (Ψ ,:= A)
        (Φ ,:= renameᵗ (toRenameᵗ ρ) A)

  target-opaque : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
    → RenameTarget ρ Ψ Φ
      -----------------------------------------------
    → RenameTarget ρ (Ψ ,opaque) (Φ ,opaque)

delete-id↪ᵗ : ∀ {Δ} (Y : TyVar (suc Δ))
  → delete↪ᵗ id↪ᵗ Y ≡ id↪ᵗ
delete-id↪ᵗ {Δ = zero} zero = refl
delete-id↪ᵗ {Δ = suc Δ} zero = refl
delete-id↪ᵗ {Δ = suc Δ} (suc Y) = cong keep (delete-id↪ᵗ Y)

delete-wk↪ᵗ : ∀ {Δ} (Y : TyVar (suc Δ))
  → delete↪ᵗ wk↪ᵗ Y ≡ wk↪ᵗ
delete-wk↪ᵗ Y = cong skip (delete-id↪ᵗ Y)

∖-literal-wk : ∀ {Θ Δ} (Ψ : TyEnv Θ (suc Δ))
    (Y : TyVar (suc Δ))
  → (Ψ ,typ[ zero ]) ∖ toRenameᵗ wk↪ᵗ Y
    ≡ (Ψ ∖ Y) ,typ[ zero ]
∖-literal-wk Ψ Y rewrite toRename-id-eq Y = refl

renameTarget-delete-typ : ∀ {Θ Δ Δ′}
    {ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′)}
    {Ψ : TyEnv Θ (suc Δ)} {Φ : TyEnv Θ (suc Δ′)}
    (X Y : TyVar (suc (suc Δ)))
    (X≢Y : X ≢ Y) (Y≢X : Y ≢ X)
  → RenameTarget (delete↪ᵗ ρ X) Ψ Φ
  → RenameTarget
      (delete↪ᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
      (Ψ ∖ punchOut X Y X≢Y)
      (Φ ∖ toRenameᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
  → RenameTarget (delete↪ᵗ ρ Y)
      ((Ψ ,typ[ X ]) ∖ Y)
      ((Φ ,typ[ toRenameᵗ ρ X ]) ∖ toRenameᵗ ρ Y)
renameTarget-delete-typ {ρ = ρ} {Ψ = Ψ} {Φ = Φ}
    X Y X≢Y Y≢X target deleted-target =
  subst≡
    (λ Ψ′ → RenameTarget (delete↪ᵗ ρ Y) Ψ′
      ((Φ ,typ[ toRenameᵗ ρ X ]) ∖ toRenameᵗ ρ Y))
    (sym source-env-eq)
    (subst≡
      (λ Φ′ → RenameTarget (delete↪ᵗ ρ Y)
        ((Ψ ∖ source-Y) ,typ[ source-X ]) Φ′)
      (sym target-env-eq) retained-target)
  where
  source-Y = punchOut X Y X≢Y
  source-X = punchOut Y X Y≢X
  target-X≢Y = λ eq → X≢Y (toRenameᵗ-injective ρ eq)
  target-Y≢X = λ eq → Y≢X (toRenameᵗ-injective ρ eq)
  target-Y = punchOut (toRenameᵗ ρ X) (toRenameᵗ ρ Y) target-X≢Y
  target-X = punchOut (toRenameᵗ ρ Y) (toRenameᵗ ρ X) target-Y≢X

  source-env-eq = ∖-typ-other Ψ X Y X≢Y Y≢X
  target-env-eq = ∖-typ-other Φ (toRenameᵗ ρ X)
    (toRenameᵗ ρ Y) target-X≢Y target-Y≢X

  deleted-injection-eq = delete-delete↪ᵗ ρ X Y X≢Y Y≢X
  deleted-target-env-eq = cong (Φ ∖_)
    (rename-punchOut ρ X Y X≢Y target-X≢Y)

  normalized-deleted-target =
    subst≡
      (λ η → RenameTarget η (Ψ ∖ source-Y)
        (Φ ∖ toRenameᵗ (delete↪ᵗ ρ X) source-Y))
      deleted-injection-eq deleted-target

  underlying-target =
    subst≡
      (λ Φ′ → RenameTarget
        (delete↪ᵗ (delete↪ᵗ ρ Y) source-X)
        (Ψ ∖ source-Y) Φ′)
      deleted-target-env-eq normalized-deleted-target

  retained-target₀ = target-typ source-X underlying-target

  retained-slot-eq = rename-punchOut ρ Y X Y≢X target-Y≢X

  retained-target =
    subst≡
      (λ Z → RenameTarget (delete↪ᵗ ρ Y)
        ((Ψ ∖ source-Y) ,typ[ source-X ])
        ((Φ ∖ target-Y) ,typ[ Z ]))
      retained-slot-eq retained-target₀

renameTarget-delete : ∀ {Θ Δ Δ′} {ρ : suc Δ ↪ᵗ suc Δ′}
    {Ψ : TyEnv Θ (suc Δ)} {Φ : TyEnv Θ (suc Δ′)}
  → RenameTarget ρ Ψ Φ
  → (Y : TyVar (suc Δ))
  → RenameTarget (delete↪ᵗ ρ Y) (Ψ ∖ Y)
      (Φ ∖ toRenameᵗ ρ Y)
renameTarget-delete {ρ = ρ} {Ψ = Ψ} canonical-target Y =
  subst≡
    (λ Φ′ → RenameTarget (delete↪ᵗ ρ Y) (Ψ ∖ Y) Φ′)
    (sym (renameTyEnv-∖ ρ Ψ Y)) canonical-target
renameTarget-delete {Ψ = Ψ} literal-wk-target Y =
  subst≡
    (λ Φ′ → RenameTarget (delete↪ᵗ wk↪ᵗ Y) (Ψ ∖ Y) Φ′)
    (sym (∖-literal-wk Ψ Y))
    (subst≡
      (λ η → RenameTarget η (Ψ ∖ Y) ((Ψ ∖ Y) ,typ[ zero ]))
      (sym (delete-wk↪ᵗ Y)) literal-wk-target)
renameTarget-delete {Δ = suc Δ} {Δ′ = zero} {ρ = keep ()} target Y
renameTarget-delete {Δ = suc Δ} {Δ′ = zero} {ρ = skip ()} target Y
renameTarget-delete {ρ = ρ} {Ψ = Ψ ,typ[ X ]}
    {Φ = Φ ,typ[ .(toRenameᵗ ρ X) ]} (target-typ .X target) Y
    with X ≟ Y
renameTarget-delete {ρ = ρ} {Ψ = Ψ ,typ[ .Y ]}
    {Φ = Φ ,typ[ .(toRenameᵗ ρ Y) ]} (target-typ .Y target) Y
    | yes refl
    rewrite ∖-typ-here Ψ Y
      | ∖-typ-here Φ (toRenameᵗ ρ Y) =
  target
renameTarget-delete {Δ = zero} {ρ = ρ} {Ψ = Ψ ,typ[ zero ]}
    {Φ = Φ ,typ[ .(toRenameᵗ ρ zero) ]} (target-typ .zero target)
    zero | no zero≢zero =
  ⊥-elim (zero≢zero refl)
renameTarget-delete {Δ = suc Δ} {Δ′ = zero} {ρ = keep ()}
    {Ψ = Ψ ,typ[ X ]} (target-typ .X target) Y | no X≢Y
renameTarget-delete {Δ = suc Δ} {Δ′ = zero} {ρ = skip ()}
    {Ψ = Ψ ,typ[ X ]} (target-typ .X target) Y | no X≢Y
renameTarget-delete {Δ = suc Δ} {Δ′ = suc Δ′} {ρ = ρ}
    {Ψ = Ψ ,typ[ X ]}
    {Φ = Φ ,typ[ .(toRenameᵗ ρ X) ]} (target-typ .X target) Y
    | no X≢Y =
  renameTarget-delete-typ X Y X≢Y (λ eq → X≢Y (sym eq)) target
    (renameTarget-delete target (punchOut X Y X≢Y))
renameTarget-delete {ρ = ρ} (target-:= {A = A} target) Y
    with strengthenᵗ? Y A
       | strengthenᵗ? (toRenameᵗ ρ Y) (renameᵗ (toRenameᵗ ρ) A)
       | strengthen-rename ρ Y A
renameTarget-delete (target-:= target) Y
    | nothing | .nothing | refl =
  target-opaque (renameTarget-delete target Y)
renameTarget-delete {ρ = ρ} (target-:= target) Y
    | just A′
    | .(just (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) A′)) | refl =
  target-:= (renameTarget-delete target Y)
renameTarget-delete (target-opaque target) Y =
  target-opaque (renameTarget-delete target Y)

renameTarget-insert : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
  → RenameTarget ρ Ψ Φ
  → (Y : TyVar (suc Δ))
  → RenameTarget (insert↪ᵗ ρ Y) (Ψ ,typ[ Y ])
      (Φ ,typ[ toRenameᵗ (insert↪ᵗ ρ Y) Y ])
renameTarget-insert {ρ = ρ} {Ψ = Ψ} {Φ = Φ} target Y =
  target-typ Y
    (subst≡ (λ η → RenameTarget η Ψ Φ)
      (sym (delete-insert↪ᵗ ρ Y)) target)

renameTarget-∋:= : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
    {α : TyVar Θ} {A : Ty Δ}
  → RenameTarget ρ Ψ Φ
  → Ψ ∋ α := A
  → Φ ∋ α := renameᵗ (toRenameᵗ ρ) A
renameTarget-∋:= {ρ = ρ} canonical-target α∈ = rename-∋:= ρ α∈
renameTarget-∋:= {A = A} literal-wk-target α∈ =
  subst≡ (λ C → _ ∋ _ := C) (sym (renameᵗ-wk-eq A))
    (skip-typ α∈)
renameTarget-∋:= {ρ = ρ} (target-typ X target)
    (skip-typ {A = A} α∈) =
  subst≡ (λ C → _ ∋ _ := C)
    (sym (rename-delete-wk ρ X A))
    (skip-typ (renameTarget-∋:= target α∈))
renameTarget-∋:= (target-:= target) Z = Z
renameTarget-∋:= (target-:= target) (S α∈) =
  S (renameTarget-∋:= target α∈)
renameTarget-∋:= (target-opaque target) (skip-opaque α∈) =
  skip-opaque (renameTarget-∋:= target α∈)

------------------------------------------------------------------------
-- Type-variable renaming preserves typing
------------------------------------------------------------------------

renameCtx-keep-shift : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Γ : TermCtx Δ)
  → renameCtx (toRenameᵗ (keep ρ)) (renameCtx suc Γ)
    ≡ renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
renameCtx-keep-shift ρ [] = refl
renameCtx-keep-shift ρ (A ∷ Γ) =
  cong₂ _∷_
    (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
      (renameᵗ-shift (toRenameᵗ ρ) A))
    (renameCtx-keep-shift ρ Γ)

rename-open↪ᵗ : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (C : Ty (suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ ρ) (C [ A ]ᵗ)
    ≡ renameᵗ (toRenameᵗ (keep ρ)) C
        [ renameᵗ (toRenameᵗ ρ) A ]ᵗ
rename-open↪ᵗ ρ C A =
  trans (renameᵗ-subst (toRenameᵗ ρ) (singleSubᵗ A) C)
    (trans (substᵗ-cong C env-eq)
      (sym (substᵗ-rename
        (singleSubᵗ (renameᵗ (toRenameᵗ ρ) A))
        (toRenameᵗ (keep ρ)) C)))
  where
  env-eq : ∀ X
    → renameᵗ (toRenameᵗ ρ) (singleSubᵗ A X)
      ≡ singleSubᵗ (renameᵗ (toRenameᵗ ρ) A)
          (toRenameᵗ (keep ρ) X)
  env-eq zero = refl
  env-eq (suc X) = refl

⊢renameᵗᵐ : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ (toRenameᵗ ρ) A
⊢renameᵗᵐ (⊢` x∈) = ⊢` (renameᵗ-∋ _ x∈)
⊢renameᵗᵐ (⊢ƛ M⊢) = ⊢ƛ (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ (⊢· L⊢ M⊢) =
  ⊢· (⊢renameᵗᵐ L⊢) (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ {ρ = ρ} {Ψ = Ψ} {Γ = Γ} (⊢Λ {A = A} M⊢) =
  ⊢Λ body⊢
  where
  renamed-body⊢ = ⊢renameᵗᵐ M⊢

  body-context⊢ =
    subst≡
      (λ Γ′ → renameTyEnv ρ Ψ ,typ[ zero ] ∣ Γ′
        ⊢ renameᵗᵐ (keep ρ) _ ⦂ _)
      (renameCtx-keep-shift ρ Γ) renamed-body⊢

  body⊢ =
    subst≡
      (λ B → renameTyEnv ρ Ψ ,typ[ zero ] ∣
        renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
          ⊢ renameᵗᵐ (keep ρ) _ ⦂ B)
      (renameᵗ-cong A (toRename-keep-eq ρ)) body-context⊢
⊢renameᵗᵐ {Δ′ = Δ′} {ρ = ρ} {Ψ = Ψ} {Γ = Γ}
    {M = L ⦂∀ C [ A ]} (⊢⦂∀ L⊢) =
  subst≡
    (λ B → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ L ⦂∀ renameᵗ (toRenameᵗ (keep ρ)) C
        [ renameᵗ (toRenameᵗ ρ) A ] ⦂ B)
    result-eq (⊢⦂∀ body⊢)
  where
  body-eq = renameᵗ-cong C (toRename-keep-eq ρ)

  body⊢ =
    subst≡
      (λ B → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
        ⊢ renameᵗᵐ ρ L ⦂ `∀ B)
      (sym body-eq) (⊢renameᵗᵐ L⊢)

  result-eq = sym (rename-open↪ᵗ ρ C A)
⊢renameᵗᵐ {ρ = ρ} (⊢$ κ) =
  subst≡ (λ A → _ ∣ _ ⊢ $ κ ⦂ A)
    (constTy-renameᵗ (toRenameᵗ ρ) κ) (⊢$ κ)
⊢renameᵗᵐ (⊢⊕ addℕ L⊢ M⊢) =
  ⊢⊕ addℕ (⊢renameᵗᵐ L⊢) (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ (⊢⊕ and𝔹 L⊢ M⊢) =
  ⊢⊕ and𝔹 (⊢renameᵗᵐ L⊢) (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ {ρ = ρ} (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢renameᵗᵐ M⊢) (renameᵐᶜ ρ c)
⊢renameᵗᵐ (⊢ν M⊢) = ⊢ν (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ {ρ = ρ}
    (⊢reveal {A = A} {B = B} {C = C} {Y = Y} α∈ c⊢ M⊢) =
  ⊢reveal (rename-∋:= ρ α∈) conversion⊢ body⊢
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y

  body⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∣ [] ⊢ renameᵗᵐ ρ⁺ _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) A)
      (renameTyEnv-insert ρ _ Y) (⊢renameᵗᵐ M⊢)

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↑[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) A
        ↝ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y B))
      (rename-insert-wk ρ Y C)
      (rename-⊢↑ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ B′ →
        ⊢↑[ Y′ ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ ρ) C) ] _
          ⦂ renameᵗ (toRenameᵗ ρ⁺) A ↝ B′)
      (rename-insert-wk ρ Y B) conversion-representation⊢
⊢renameᵗᵐ {ρ = ρ⁺@(keep ρ)} {Ψ = Ψ}
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} α∈ c⊢ M⊢) =
  ⊢conceal lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  env-eq = renameTyEnv-∖ ρ⁺ Ψ Y

  lookup⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∋ _ := renameᵗ (toRenameᵗ deleted) C)
      (sym env-eq) (rename-∋:= deleted α∈)

  body⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∣ [] ⊢ renameᵗᵐ deleted _
        ⦂ renameᵗ (toRenameᵗ deleted) A)
      (sym env-eq) (⊢renameᵗᵐ M⊢)

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↓[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
        ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y C)
      (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ A′ → ⊢↓[ Y′
          ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
        ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢renameᵗᵐ {ρ = ρ⁺@(skip ρ)} {Ψ = Ψ}
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} α∈ c⊢ M⊢) =
  ⊢conceal lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  env-eq = renameTyEnv-∖ ρ⁺ Ψ Y

  lookup⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∋ _ := renameᵗ (toRenameᵗ deleted) C)
      (sym env-eq) (rename-∋:= deleted α∈)

  body⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∣ [] ⊢ renameᵗᵐ deleted _
        ⦂ renameᵗ (toRenameᵗ deleted) A)
      (sym env-eq) (⊢renameᵗᵐ M⊢)

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↓[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
        ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y C)
      (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ A′ → ⊢↓[ Y′
          ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
        ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢renameᵗᵐ ⊢blame = ⊢blame

⊢renameᵗᵐ-target : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → RenameTarget ρ Ψ Φ
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ (toRenameᵗ ρ) A
⊢renameᵗᵐ-target target (⊢` x∈) = ⊢` (renameᵗ-∋ _ x∈)
⊢renameᵗᵐ-target target (⊢ƛ M⊢) =
  ⊢ƛ (⊢renameᵗᵐ-target target M⊢)
⊢renameᵗᵐ-target target (⊢· L⊢ M⊢) =
  ⊢· (⊢renameᵗᵐ-target target L⊢)
    (⊢renameᵗᵐ-target target M⊢)
⊢renameᵗᵐ-target {ρ = ρ} {Φ = Φ} {Γ = Γ}
    target (⊢Λ {A = A} M⊢) =
  ⊢Λ body⊢
  where
  renamed-body⊢ = ⊢renameᵗᵐ-target (target-typ zero target) M⊢

  body-context⊢ =
    subst≡
      (λ Γ′ → Φ ,typ[ zero ] ∣ Γ′
        ⊢ renameᵗᵐ (keep ρ) _ ⦂ _)
      (renameCtx-keep-shift ρ Γ) renamed-body⊢

  body⊢ =
    subst≡
      (λ B → Φ ,typ[ zero ] ∣
        renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
          ⊢ renameᵗᵐ (keep ρ) _ ⦂ B)
      (renameᵗ-cong A (toRename-keep-eq ρ)) body-context⊢
⊢renameᵗᵐ-target {ρ = ρ} {Φ = Φ} {Γ = Γ}
    {M = L ⦂∀ C [ A ]} target (⊢⦂∀ L⊢) =
  subst≡
    (λ B → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ L ⦂∀ renameᵗ (toRenameᵗ (keep ρ)) C
        [ renameᵗ (toRenameᵗ ρ) A ] ⦂ B)
    result-eq (⊢⦂∀ body⊢)
  where
  body-eq = renameᵗ-cong C (toRename-keep-eq ρ)

  body⊢ =
    subst≡
      (λ B → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
        ⊢ renameᵗᵐ ρ L ⦂ `∀ B)
      (sym body-eq) (⊢renameᵗᵐ-target target L⊢)

  result-eq = sym (rename-open↪ᵗ ρ C A)
⊢renameᵗᵐ-target {ρ = ρ} target (⊢$ κ) =
  subst≡ (λ A → _ ∣ _ ⊢ $ κ ⦂ A)
    (constTy-renameᵗ (toRenameᵗ ρ) κ) (⊢$ κ)
⊢renameᵗᵐ-target target (⊢⊕ addℕ L⊢ M⊢) =
  ⊢⊕ addℕ (⊢renameᵗᵐ-target target L⊢)
    (⊢renameᵗᵐ-target target M⊢)
⊢renameᵗᵐ-target target (⊢⊕ and𝔹 L⊢ M⊢) =
  ⊢⊕ and𝔹 (⊢renameᵗᵐ-target target L⊢)
    (⊢renameᵗᵐ-target target M⊢)
⊢renameᵗᵐ-target {ρ = ρ} target (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢renameᵗᵐ-target target M⊢) (renameᵐᶜ ρ c)
⊢renameᵗᵐ-target target (⊢ν M⊢) =
  ⊢ν (⊢renameᵗᵐ-target (target-:= target) M⊢)
⊢renameᵗᵐ-target {ρ = ρ} {Φ = Φ}
    target
    (⊢reveal {A = A} {B = B} {C = C} {Y = Y} α∈ c⊢ M⊢) =
  ⊢reveal (renameTarget-∋:= target α∈) conversion⊢ body⊢
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y

  body⊢ = ⊢renameᵗᵐ-target (renameTarget-insert target Y) M⊢

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↑[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) A
        ↝ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y B))
      (rename-insert-wk ρ Y C)
      (rename-⊢↑ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ B′ →
        ⊢↑[ Y′ ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ ρ) C) ] _
          ⦂ renameᵗ (toRenameᵗ ρ⁺) A ↝ B′)
      (rename-insert-wk ρ Y B) conversion-representation⊢
⊢renameᵗᵐ-target {ρ = ρ⁺@(keep ρ)} {Ψ = Ψ}
    target
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} α∈ c⊢ M⊢) =
  ⊢conceal lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  deleted-target = renameTarget-delete target Y

  lookup⊢ = renameTarget-∋:= deleted-target α∈
  body⊢ = ⊢renameᵗᵐ-target deleted-target M⊢

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↓[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
        ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y C)
      (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ A′ → ⊢↓[ Y′
          ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
        ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢renameᵗᵐ-target {ρ = ρ⁺@(skip ρ)} {Ψ = Ψ}
    target
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} α∈ c⊢ M⊢) =
  ⊢conceal lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  deleted-target = renameTarget-delete target Y

  lookup⊢ = renameTarget-∋:= deleted-target α∈
  body⊢ = ⊢renameᵗᵐ-target deleted-target M⊢

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↓[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
        ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y C)
      (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ A′ → ⊢↓[ Y′
          ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
        ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢renameᵗᵐ-target target ⊢blame = ⊢blame

------------------------------------------------------------------------
-- Literal regular-context weakening at zero
------------------------------------------------------------------------

renameCtx-wk-eq : ∀ {Δ} (Γ : TermCtx Δ)
  → renameCtx (toRenameᵗ wk↪ᵗ) Γ ≡ renameCtx suc Γ
renameCtx-wk-eq [] = refl
renameCtx-wk-eq (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-wk-eq A) (renameCtx-wk-eq Γ)

⊢weakenᵗᵐ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Ψ ,typ[ zero ] ∣ renameCtx suc Γ
      ⊢ weakenᵗᵐ zero M ⦂ ⇑ᵗ A
⊢weakenᵗᵐ {Ψ = Ψ} {Γ = Γ} {M = M} {A = A} M⊢ =
  subst≡
    (λ B → Ψ ,typ[ zero ] ∣ renameCtx suc Γ
      ⊢ weakenᵗᵐ zero M ⦂ B)
    (renameᵗ-wk-eq A)
    (subst≡
      (λ Γ′ → Ψ ,typ[ zero ] ∣ Γ′
        ⊢ weakenᵗᵐ zero M ⦂ renameᵗ (toRenameᵗ wk↪ᵗ) A)
      (renameCtx-wk-eq Γ)
      (⊢renameᵗᵐ-target literal-wk-target M⊢))

------------------------------------------------------------------------
-- Parallel and single term substitution
------------------------------------------------------------------------

exts-∋ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ Γ′ : TermCtx Δ}
    {σ : Subst Θ Δ} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Ψ ∣ Γ′ ⊢ σ x ⦂ B)
  → ∀ {x B}
  → A ∷ Γ ∋ x ⦂ B
  → Ψ ∣ A ∷ Γ′ ⊢ exts σ x ⦂ B
exts-∋ σ⊢ Z = ⊢` Z
exts-∋ σ⊢ (S x∈) = ⊢rename-suc (σ⊢ x∈)

liftˢ-∋ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ Γ′ : TermCtx Δ}
    {σ : Subst Θ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Ψ ∣ Γ′ ⊢ σ x ⦂ A)
  → ∀ {x A}
  → renameCtx suc Γ ∋ x ⦂ A
  → Ψ ,typ[ zero ] ∣ renameCtx suc Γ′ ⊢ liftˢ σ x ⦂ A
liftˢ-∋ σ⊢ x∈ with lookup-renameCtx-inv x∈
liftˢ-∋ σ⊢ x∈ | B , B∈ , refl = ⊢weakenᵗᵐ (σ⊢ B∈)

⊢subst : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ Γ′ : TermCtx Δ}
    {σ : Subst Θ Δ} {M : Term Θ Δ} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Ψ ∣ Γ′ ⊢ σ x ⦂ B)
  → Ψ ∣ Γ ⊢ M ⦂ A
    --------------------------
  → Ψ ∣ Γ′ ⊢ subst σ M ⦂ A
⊢subst σ⊢ (⊢` x∈) = σ⊢ x∈
⊢subst σ⊢ (⊢ƛ M⊢) = ⊢ƛ (⊢subst (exts-∋ σ⊢) M⊢)
⊢subst σ⊢ (⊢· L⊢ M⊢) =
  ⊢· (⊢subst σ⊢ L⊢) (⊢subst σ⊢ M⊢)
⊢subst σ⊢ (⊢Λ M⊢) = ⊢Λ (⊢subst (liftˢ-∋ σ⊢) M⊢)
⊢subst σ⊢ (⊢⦂∀ L⊢) = ⊢⦂∀ (⊢subst σ⊢ L⊢)
⊢subst σ⊢ (⊢$ κ) = ⊢$ κ
⊢subst σ⊢ (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢subst σ⊢ L⊢) (⊢subst σ⊢ M⊢)
⊢subst σ⊢ (⊢⟨⟩ M⊢ c) = ⊢⟨⟩ (⊢subst σ⊢ M⊢) c
⊢subst σ⊢ (⊢ν M⊢) = ⊢ν M⊢
⊢subst σ⊢ (⊢reveal α∈ c⊢ M⊢) = ⊢reveal α∈ c⊢ M⊢
⊢subst σ⊢ (⊢conceal α∈ c⊢ M⊢) = ⊢conceal α∈ c⊢ M⊢
⊢subst σ⊢ ⊢blame = ⊢blame

⊢[] : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M N : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ A ∷ Γ ⊢ M ⦂ B
  → Ψ ∣ Γ ⊢ N ⦂ A
    ---------------------
  → Ψ ∣ Γ ⊢ M [ N ] ⦂ B
⊢[] {Θ = Θ} {Ψ = Ψ} {Γ = Γ} {N = N} {A = A} M⊢ N⊢ =
  ⊢subst single⊢ M⊢
  where
  single⊢ : ∀ {x C}
    → A ∷ Γ ∋ x ⦂ C
    → Ψ ∣ Γ ⊢ singleSub N x ⦂ C
  single⊢ Z = N⊢
  single⊢ (S x∈) = ⊢` x∈

------------------------------------------------------------------------
-- Anchor renaming and visible/opaque weakening
------------------------------------------------------------------------

data AnchorTarget : ∀ {Θ Θ′ Δ} (ρ : TyVar Θ → TyVar Θ′)
    → TyEnv Θ Δ → TyEnv Θ′ Δ → Set where
  visible-shift-target : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {B : Ty Δ}
      -----------------------------------------
    → AnchorTarget suc Ψ (Ψ ,:= B)

  opaque-shift-target : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      --------------------------------------
    → AnchorTarget suc Ψ (Ψ ,opaque)

  anchor-target-typ : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
      (Y : TyVar (suc Δ))
    → AnchorTarget ρ Ψ Φ
      --------------------------------------------------
    → AnchorTarget ρ (Ψ ,typ[ Y ]) (Φ ,typ[ Y ])

  anchor-target-:= : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ} {A : Ty Δ}
    → AnchorTarget ρ Ψ Φ
      -----------------------------------------------
    → AnchorTarget (extᵗ ρ) (Ψ ,:= A) (Φ ,:= A)

  anchor-target-opaque : ∀ {Θ Θ′ Δ}
      {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
    → AnchorTarget ρ Ψ Φ
      ----------------------------------------------------
    → AnchorTarget (extᵗ ρ) (Ψ ,opaque) (Φ ,opaque)

anchorTarget-delete : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ (suc Δ)} {Φ : TyEnv Θ′ (suc Δ)}
  → AnchorTarget ρ Ψ Φ
  → (Y : TyVar (suc Δ))
  → AnchorTarget ρ (Ψ ∖ Y) (Φ ∖ Y)
anchorTarget-delete (visible-shift-target {B = B}) Y
    with strengthenᵗ? Y B
anchorTarget-delete visible-shift-target Y | just B′ =
  visible-shift-target
anchorTarget-delete visible-shift-target Y | nothing =
  opaque-shift-target
anchorTarget-delete opaque-shift-target Y = opaque-shift-target
anchorTarget-delete {Ψ = Ψ ,typ[ X ]} {Φ = Φ ,typ[ .X ]}
    (anchor-target-typ .X target) Y with X ≟ Y
anchorTarget-delete {Ψ = Ψ ,typ[ .Y ]} {Φ = Φ ,typ[ .Y ]}
    (anchor-target-typ .Y target) Y | yes refl
    rewrite ∖-typ-here Ψ Y | ∖-typ-here Φ Y =
  target
anchorTarget-delete {Δ = zero} {Ψ = Ψ ,typ[ zero ]}
    {Φ = Φ ,typ[ zero ]} (anchor-target-typ .zero target) zero
    | no zero≢zero =
  ⊥-elim (zero≢zero refl)
anchorTarget-delete {Δ = suc Δ} {Ψ = Ψ ,typ[ X ]}
    {Φ = Φ ,typ[ .X ]} (anchor-target-typ .X target) Y
    | no X≢Y
    rewrite ∖-typ-other Ψ X Y X≢Y (λ eq → X≢Y (sym eq))
      | ∖-typ-other Φ X Y X≢Y (λ eq → X≢Y (sym eq)) =
  anchor-target-typ (punchOut Y X (λ eq → X≢Y (sym eq)))
    (anchorTarget-delete target (punchOut X Y X≢Y))
anchorTarget-delete (anchor-target-:= {A = A} target) Y
    with strengthenᵗ? Y A
anchorTarget-delete (anchor-target-:= target) Y | just A′ =
  anchor-target-:= (anchorTarget-delete target Y)
anchorTarget-delete (anchor-target-:= target) Y | nothing =
  anchor-target-opaque (anchorTarget-delete target Y)
anchorTarget-delete (anchor-target-opaque target) Y =
  anchor-target-opaque (anchorTarget-delete target Y)

anchorTarget-∋:= : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
    {α : TyVar Θ} {A : Ty Δ}
  → AnchorTarget ρ Ψ Φ
  → Ψ ∋ α := A
  → Φ ∋ ρ α := A
anchorTarget-∋:= visible-shift-target α∈ = S α∈
anchorTarget-∋:= opaque-shift-target α∈ = skip-opaque α∈
anchorTarget-∋:= (anchor-target-typ Y target) (skip-typ α∈) =
  skip-typ (anchorTarget-∋:= target α∈)
anchorTarget-∋:= (anchor-target-:= target) Z = Z
anchorTarget-∋:= (anchor-target-:= target) (S α∈) =
  S (anchorTarget-∋:= target α∈)
anchorTarget-∋:= (anchor-target-opaque target) (skip-opaque α∈) =
  skip-opaque (anchorTarget-∋:= target α∈)

⊢renameᶿ-target : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → AnchorTarget ρ Ψ Φ
  → Ψ ∣ Γ ⊢ M ⦂ A
    ----------------------------
  → Φ ∣ Γ ⊢ renameᶿ ρ M ⦂ A
⊢renameᶿ-target target (⊢` x∈) = ⊢` x∈
⊢renameᶿ-target target (⊢ƛ M⊢) =
  ⊢ƛ (⊢renameᶿ-target target M⊢)
⊢renameᶿ-target target (⊢· L⊢ M⊢) =
  ⊢· (⊢renameᶿ-target target L⊢) (⊢renameᶿ-target target M⊢)
⊢renameᶿ-target target (⊢Λ M⊢) =
  ⊢Λ (⊢renameᶿ-target (anchor-target-typ zero target) M⊢)
⊢renameᶿ-target target (⊢⦂∀ L⊢) =
  ⊢⦂∀ (⊢renameᶿ-target target L⊢)
⊢renameᶿ-target target (⊢$ κ) = ⊢$ κ
⊢renameᶿ-target target (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢renameᶿ-target target L⊢)
    (⊢renameᶿ-target target M⊢)
⊢renameᶿ-target target (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢renameᶿ-target target M⊢) c
⊢renameᶿ-target target (⊢ν M⊢) =
  ⊢ν (⊢renameᶿ-target (anchor-target-:= target) M⊢)
⊢renameᶿ-target target (⊢reveal α∈ c⊢ M⊢) =
  ⊢reveal (anchorTarget-∋:= target α∈) c⊢
    (⊢renameᶿ-target (anchor-target-typ _ target) M⊢)
⊢renameᶿ-target target (⊢conceal {Y = Y} α∈ c⊢ M⊢) =
  ⊢conceal (anchorTarget-∋:= deleted-target α∈) c⊢
    (⊢renameᶿ-target deleted-target M⊢)
  where
  deleted-target = anchorTarget-delete target Y
⊢renameᶿ-target target ⊢blame = ⊢blame

⊢shiftᶿ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
    ---------------------------
  → Ψ ,:= B ∣ Γ ⊢ shiftᶿ M ⦂ A
⊢shiftᶿ M⊢ = ⊢renameᶿ-target visible-shift-target M⊢

⊢weaken-opaque : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
    ------------------------------
  → Ψ ,opaque ∣ Γ ⊢ shiftᶿ M ⦂ A
⊢weaken-opaque M⊢ = ⊢renameᶿ-target opaque-shift-target M⊢

------------------------------------------------------------------------
-- Opaque-to-visible monotonicity
------------------------------------------------------------------------

infix 4 _⊑ᵒ_
data _⊑ᵒ_ : ∀ {Θ Δ} → TyEnv Θ Δ → TyEnv Θ Δ → Set where
  mono-∅ :
      -------
      ∅ ⊑ᵒ ∅

  mono-typ : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
      {Y : TyVar (suc Δ)}
    → Ψ ⊑ᵒ Φ
      ----------------------------------
    → (Ψ ,typ[ Y ]) ⊑ᵒ (Φ ,typ[ Y ])

  mono-:= : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ} {A : Ty Δ}
    → Ψ ⊑ᵒ Φ
      --------------------------
    → (Ψ ,:= A) ⊑ᵒ (Φ ,:= A)

  mono-opaque : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
    → Ψ ⊑ᵒ Φ
      -------------------------------
    → (Ψ ,opaque) ⊑ᵒ (Φ ,opaque)

  mono-visible : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ} {A : Ty Δ}
    → Ψ ⊑ᵒ Φ
      ---------------------------
    → (Ψ ,opaque) ⊑ᵒ (Φ ,:= A)

opaque-refl : ∀ {Θ Δ} (Ψ : TyEnv Θ Δ) → Ψ ⊑ᵒ Ψ
opaque-refl ∅ = mono-∅
opaque-refl (Ψ ,typ[ Y ]) = mono-typ (opaque-refl Ψ)
opaque-refl (Ψ ,:= A) = mono-:= (opaque-refl Ψ)
opaque-refl (Ψ ,opaque) = mono-opaque (opaque-refl Ψ)

opaque-delete : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ (suc Δ)}
  → Ψ ⊑ᵒ Φ
  → (Y : TyVar (suc Δ))
  → (Ψ ∖ Y) ⊑ᵒ (Φ ∖ Y)
opaque-delete {Ψ = Ψ ,typ[ X ]} {Φ = Φ ,typ[ .X ]}
    (mono-typ relation) Y with X ≟ Y
opaque-delete {Ψ = Ψ ,typ[ .Y ]} {Φ = Φ ,typ[ .Y ]}
    (mono-typ relation) Y | yes refl
    rewrite ∖-typ-here Ψ Y | ∖-typ-here Φ Y =
  relation
opaque-delete {Δ = zero} {Ψ = Ψ ,typ[ zero ]}
    {Φ = Φ ,typ[ zero ]} (mono-typ relation) zero | no zero≢zero =
  ⊥-elim (zero≢zero refl)
opaque-delete {Δ = suc Δ} {Ψ = Ψ ,typ[ X ]}
    {Φ = Φ ,typ[ .X ]} (mono-typ relation) Y | no X≢Y
    rewrite ∖-typ-other Ψ X Y X≢Y (λ eq → X≢Y (sym eq))
      | ∖-typ-other Φ X Y X≢Y (λ eq → X≢Y (sym eq)) =
  mono-typ (opaque-delete relation (punchOut X Y X≢Y))
opaque-delete (mono-:= {A = A} relation) Y with strengthenᵗ? Y A
opaque-delete (mono-:= relation) Y | just A′ =
  mono-:= (opaque-delete relation Y)
opaque-delete (mono-:= relation) Y | nothing =
  mono-opaque (opaque-delete relation Y)
opaque-delete (mono-opaque relation) Y =
  mono-opaque (opaque-delete relation Y)
opaque-delete (mono-visible {A = A} relation) Y with strengthenᵗ? Y A
opaque-delete (mono-visible relation) Y | just A′ =
  mono-visible (opaque-delete relation Y)
opaque-delete (mono-visible relation) Y | nothing =
  mono-opaque (opaque-delete relation Y)

opaque-∋:= : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
    {α : TyVar Θ} {A : Ty Δ}
  → Ψ ⊑ᵒ Φ
  → Ψ ∋ α := A
  → Φ ∋ α := A
opaque-∋:= mono-∅ ()
opaque-∋:= (mono-typ relation) (skip-typ α∈) =
  skip-typ (opaque-∋:= relation α∈)
opaque-∋:= (mono-:= relation) Z = Z
opaque-∋:= (mono-:= relation) (S α∈) =
  S (opaque-∋:= relation α∈)
opaque-∋:= (mono-opaque relation) (skip-opaque α∈) =
  skip-opaque (opaque-∋:= relation α∈)
opaque-∋:= (mono-visible relation) (skip-opaque α∈) =
  S (opaque-∋:= relation α∈)

⊢opaque-monotone : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
    {Γ : TermCtx Δ} {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ⊑ᵒ Φ
  → Ψ ∣ Γ ⊢ M ⦂ A
    -----------------
  → Φ ∣ Γ ⊢ M ⦂ A
⊢opaque-monotone relation (⊢` x∈) = ⊢` x∈
⊢opaque-monotone relation (⊢ƛ M⊢) =
  ⊢ƛ (⊢opaque-monotone relation M⊢)
⊢opaque-monotone relation (⊢· L⊢ M⊢) =
  ⊢· (⊢opaque-monotone relation L⊢)
    (⊢opaque-monotone relation M⊢)
⊢opaque-monotone relation (⊢Λ M⊢) =
  ⊢Λ (⊢opaque-monotone (mono-typ relation) M⊢)
⊢opaque-monotone relation (⊢⦂∀ L⊢) =
  ⊢⦂∀ (⊢opaque-monotone relation L⊢)
⊢opaque-monotone relation (⊢$ κ) = ⊢$ κ
⊢opaque-monotone relation (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢opaque-monotone relation L⊢)
    (⊢opaque-monotone relation M⊢)
⊢opaque-monotone relation (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢opaque-monotone relation M⊢) c
⊢opaque-monotone relation (⊢ν M⊢) =
  ⊢ν (⊢opaque-monotone (mono-:= relation) M⊢)
⊢opaque-monotone relation (⊢reveal α∈ c⊢ M⊢) =
  ⊢reveal (opaque-∋:= relation α∈) c⊢
    (⊢opaque-monotone (mono-typ relation) M⊢)
⊢opaque-monotone relation (⊢conceal {Y = Y} α∈ c⊢ M⊢) =
  ⊢conceal (opaque-∋:= deleted-relation α∈) c⊢
    (⊢opaque-monotone deleted-relation M⊢)
  where
  deleted-relation = opaque-delete relation Y
⊢opaque-monotone relation ⊢blame = ⊢blame

⊢opaque-visible : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term (suc Θ) Δ} {A B : Ty Δ}
  → Ψ ,opaque ∣ Γ ⊢ M ⦂ A
    -----------------------
  → Ψ ,:= B ∣ Γ ⊢ M ⦂ A
⊢opaque-visible {Ψ = Ψ} M⊢ =
  ⊢opaque-monotone (mono-visible (opaque-refl Ψ)) M⊢

∋:=-shift : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {α : TyVar Θ} {A B : Ty Δ}
  → Ψ ∋ α := A
  → (Ψ ,:= B) ∋ suc α := A
∋:=-shift = S
