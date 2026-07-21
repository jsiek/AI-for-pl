module proof.NuImprecisionSourceCastSequenceMidpointCounterexample where

-- File Charter:
--   * Isolates the strongest raw source-sequence midpoint obstruction.
--   * Builds coherent/exclusive endpoints and a typed two-seal narrowing
--     whose intermediate name has no imprecision path to the target star.
--   * Proves that the example cannot satisfy `SealModeStore★`, explaining
--     why it does not refute the complete source-runtime boundary.
--   * Contains no postulates, holes, or permissive options.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
import NarrowWiden as NW

open import Coercions using
  ( ModeEnv
  ; instᵈ
  ; sealModeAllowed
  ; tag-or-idᵈ
  ; _︔_
  )
open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero; s<s; z<s)
open import Data.Product using (_×_; _,_)
open import Imprecision using (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; tag_
  ; tagˣ
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuStore using (StoreWf; unique)
open import NuTermImprecision using
  ( StoreImp
  ; correspondence-linked
  ; correspondence-stored
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import Types using
  ( Store
  ; Ty
  ; TyCtx
  ; TyVar
  ; WfTy
  ; `ℕ
  ; wfBase
  ; wfVar
  ; ★
  ; ‵_
  ; ＇_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-inst
  ; cast-tag-or-id
  )
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent; world-coherent)


seal-enabled-store-entry-star :
  ∀ {μ : ModeEnv} {Δ : TyCtx} {Σ : Store} {α : TyVar} {X : Ty} →
  StoreWf Δ Σ →
  SealModeStore★ μ Σ →
  sealModeAllowed (μ α) ≡ true →
  (α , X) ∈ Σ →
  X ≡ ★
seal-enabled-store-entry-star wfΣ seal★ seal-ok αX∈Σ =
  unique wfΣ αX∈Σ (seal★ _ seal-ok)


private
  Δᴸ : TyCtx
  Δᴸ = suc (suc zero)

  Δᴿ : TyCtx
  Δᴿ = zero

  δ : TyVar
  δ = zero

  α : TyVar
  α = suc zero

  Nat : Ty
  Nat = ‵ `ℕ

  Φ : ImpCtx
  Φ = (α ˣ⊑★) ∷ []

  μ : ModeEnv
  μ = instᵈ (instᵈ tag-or-idᵈ)

  ρ : StoreImp Φ Δᴸ Δᴿ
  ρ =
    store-left α (＇ δ) (wfVar z<s) ∷
    store-left δ Nat wfBase ∷ []

  s : C.Coercion
  s = C.seal Nat δ

  t : C.Coercion
  t = C.seal (＇ δ) α

  c : C.Coercion
  c = s ︔ t

  cast-mode : CastMode μ
  cast-mode = cast-inst (cast-inst cast-tag-or-id)

  exclusive : SourceNameExclusive Φ
  exclusive (here refl) (here ())
  exclusive (here refl) (there ())
  exclusive (there ()) match∈

  coherent : WorldCoherent ρ
  coherent =
    world-coherent
      (λ match∈ left∈ ())
      λ { (correspondence-stored (here ()))
        ; (correspondence-stored (there (here ())))
        ; (correspondence-stored (there (there ())))
        ; (correspondence-linked (here ()))
        ; (correspondence-linked (there (here ())))
        ; (correspondence-linked (there (there ())))
        }

  source-store-wf : StoreWf Δᴸ (leftStoreⁱ ρ)
  source-store-wf =
    record
      { at = record
          { bound = λ
              { (here refl) → s<s z<s
              ; (there (here refl)) → z<s
              ; (there (there ()))
              }
          ; wfTy = λ
              { (here refl) → wfVar z<s
              ; (there (here refl)) → wfBase
              ; (there (there ()))
              }
          }
      ; unique = λ
          { (here refl) (here refl) → refl
          ; (here refl) (there (here ()))
          ; (there (here ())) (here refl)
          ; (there (here refl)) (there (here refl)) → refl
          ; (there (there ())) right∈
          }
      }

  sequence-narrowing :
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ Nat ⊒ ＇ α
  sequence-narrowing =
    C.cast-seq
      (C.cast-seal wfBase (there (here refl)) refl)
      (C.cast-seal (wfVar z<s) (here refl) refl) ,
    NW.strict-seal Nat δ NW.︔seal α

  source-endpoint : Φ ∣ Δᴸ ⊢ Nat ⊑ ★ ⊣ Δᴿ
  source-endpoint = tag `ℕ

  result-endpoint : Φ ∣ Δᴸ ⊢ ＇ α ⊑ ★ ⊣ Δᴿ
  result-endpoint = tagˣ (here refl) (s<s z<s)

  no-midpoint : Φ ∣ Δᴸ ⊢ ＇ δ ⊑ ★ ⊣ Δᴿ → ⊥
  no-midpoint (tagˣ (here ()) δ<)
  no-midpoint (tagˣ (there ()) δ<)

  no-seal-mode-store : SealModeStore★ μ (leftStoreⁱ ρ) → ⊥
  no-seal-mode-store seal★ with seal★ δ refl
  no-seal-mode-store seal★ | here ()
  no-seal-mode-store seal★ | there (here ())
  no-seal-mode-store seal★ | there (there ())


source-cast-sequence-midpoint-obstruction :
  CastMode μ ×
  SourceNameExclusive Φ ×
  WorldCoherent ρ ×
  StoreWf Δᴸ (leftStoreⁱ ρ) ×
  (μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ Nat ⊒ ＇ α) ×
  (Φ ∣ Δᴸ ⊢ Nat ⊑ ★ ⊣ Δᴿ) ×
  (Φ ∣ Δᴸ ⊢ ＇ α ⊑ ★ ⊣ Δᴿ) ×
  ((Φ ∣ Δᴸ ⊢ ＇ δ ⊑ ★ ⊣ Δᴿ) → ⊥) ×
  (SealModeStore★ μ (leftStoreⁱ ρ) → ⊥)
source-cast-sequence-midpoint-obstruction =
  cast-mode ,
  exclusive ,
  coherent ,
  source-store-wf ,
  sequence-narrowing ,
  source-endpoint ,
  result-endpoint ,
  no-midpoint ,
  no-seal-mode-store
