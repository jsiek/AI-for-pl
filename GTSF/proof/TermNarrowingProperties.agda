module proof.TermNarrowingProperties where

-- File Charter:
--   * Admissible rules and structural lemmas for term narrowing.
--   * Provides the cambridge23 two-sided cast derived rules and source-shape
--     exclusion lemmas for value-target narrowing.
--   * Depends on the public definitions in `TermNarrowing` and `NarrowWiden`.

open import Data.Empty using (⊥)
open import Data.Nat using (suc)

open import Types
open import Coercions
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing using
  ( _∣_∣_⊢_⊒_∶_
  ; extend
  ; split
  ; ⊒blame
  ; x⊒x
  ; ƛ⊒ƛ
  ; ·⊒·
  ; Λ⊒Λ
  ; ⊒Λ
  ; ⊒⟨ν⟩
  ; α⊒α
  ; ⊒α
  ; ν⊒ν
  ; ⊒ν
  ; ν⊒
  ; κ⊒κ
  ; ⊕⊒⊕
  ; ⊒cast+
  ; ⊒cast-
  ; cast+⊒
  ; cast-⊒
  )

variable
  Δ : TyCtx
  σ : StoreNrw
  γ : CtxNrw
  A B : Ty
  p q r s t : Coercion
  M M′ : Term

------------------------------------------------------------------------
-- Derived cast rules
------------------------------------------------------------------------

-- cambridge23 states these with the side condition `q ⨾ s ≈ t ⨾ p`.
-- This formalization exposes the intermediate coercion `r`, matching the
-- displayed derivations and avoiding a dependency on general transitivity for
-- coercion equivalence.
-- The compact one-premise version should be derivable once coercion
-- equivalence has enough transitivity/reflexivity infrastructure to bridge
-- `q ⨾ s ≈ r` and `r ≈ t ⨾ p` from `q ⨾ s ≈ t ⨾ p`.

cast-⊒cast- : ∀ {M M′ p q r s t A B Ap Bp Aq Bq}
  → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ Ap ⊒ Bp
  → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ Aq ⊒ Bq
  → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
  → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
  → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q
    --------------------------------------
  → Δ ∣ σ ∣ γ ⊢ M ⟨ t ⟩ ⊒ M′ ⟨ s ⟩ ∶ p
cast-⊒cast- {p = p} {q = q} {r = r} {s = s} {t = t}
    pᶜ qᶜ q⨟s≈r r≈t⨟p M⊒M′ =
  cast-⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p
    (⊒cast- {q = q} {r = r} {s = s} qᶜ q⨟s≈r M⊒M′)

cast+⊒cast+ : ∀ {M M′ p q r s t A B Ap Bp Aq Bq}
  → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ Ap ⊒ Bp
  → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ Aq ⊒ Bq
  → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
  → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
  → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p
    ------------------------------------------
  → Δ ∣ σ ∣ γ ⊢ M ⟨ - t ⟩ ⊒ M′ ⟨ - s ⟩ ∶ q
cast+⊒cast+ {p = p} {q = q} {r = r} {s = s} {t = t}
    pᶜ qᶜ q⨟s≈r r≈t⨟p M⊒M′ =
  ⊒cast+ {q = q} {r = r} {s = s} qᶜ q⨟s≈r
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒M′)

------------------------------------------------------------------------
-- Source-shape exclusions
------------------------------------------------------------------------

data RuntimeTypeApp : Term → Set where
  runtime-• : ∀ {L} → RuntimeTypeApp (L •)

renameᵗᵐ-preserves-RuntimeTypeApp :
  ∀ ρ {M} →
  RuntimeTypeApp M →
  RuntimeTypeApp (renameᵗᵐ ρ M)
renameᵗᵐ-preserves-RuntimeTypeApp ρ runtime-• =
  runtime-•

open-preserves-RuntimeTypeApp :
  ∀ {M α β} →
  RuntimeTypeApp (M [ α ]ᵀ) →
  RuntimeTypeApp (M [ β ]ᵀ)
open-preserves-RuntimeTypeApp {M = ` x} ()
open-preserves-RuntimeTypeApp {M = ƛ M} ()
open-preserves-RuntimeTypeApp {M = L · M} ()
open-preserves-RuntimeTypeApp {M = Λ M} ()
open-preserves-RuntimeTypeApp {M = M •} runtime-• =
  runtime-•
open-preserves-RuntimeTypeApp {M = ν A L c} ()
open-preserves-RuntimeTypeApp {M = $ κ} ()
open-preserves-RuntimeTypeApp {M = L ⊕[ op ] M} ()
open-preserves-RuntimeTypeApp {M = M ⟨ c ⟩} ()
open-preserves-RuntimeTypeApp {M = blame} ()

runtime-type-app-source-no-value-target :
  ∀ {Δ σ γ M V p} →
  RuntimeTypeApp M →
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  ⊥
runtime-type-app-source-no-value-target app vV (extend qᶜ pαᶜ M⊒V) =
  runtime-type-app-source-no-value-target app vV M⊒V
runtime-type-app-source-no-value-target app vV
    (split {N = N} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ M⊒V) =
  runtime-type-app-source-no-value-target
    (open-preserves-RuntimeTypeApp {M = N} {α = αᵢ} {β = α} app)
    vV
    M⊒V
runtime-type-app-source-no-value-target app () (⊒blame pᶜ)
runtime-type-app-source-no-value-target app () (x⊒x pᶜ x∋p)
runtime-type-app-source-no-value-target () vV (ƛ⊒ƛ p↦qᶜ N⊒N′)
runtime-type-app-source-no-value-target () vV (·⊒· qᶜ L⊒L′ M⊒M′)
runtime-type-app-source-no-value-target () (Λ vV) (Λ⊒Λ allᶜ vV₁ V⊒V′)
runtime-type-app-source-no-value-target app (Λ vV) (⊒Λ pᶜ N⊒V′) =
  runtime-type-app-source-no-value-target
    (renameᵗᵐ-preserves-RuntimeTypeApp suc app)
    vV
    N⊒V′
runtime-type-app-source-no-value-target app (vV ⟨ i ⟩)
    (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s) =
  runtime-type-app-source-no-value-target
    (renameᵗᵐ-preserves-RuntimeTypeApp suc app)
    (vV ⟨ sᵢ ⟩)
    N⊒V′s
runtime-type-app-source-no-value-target () vV (α⊒α qᶜ pαᶜ L⊒L′)
runtime-type-app-source-no-value-target app () (⊒α pαᶜ L⊒L′)
runtime-type-app-source-no-value-target () vV (ν⊒ν pᶜ qᶜ N⊒N′)
runtime-type-app-source-no-value-target app () (⊒ν pᶜ N⊒N′)
runtime-type-app-source-no-value-target () vV (ν⊒ pᶜ N⊒N′)
runtime-type-app-source-no-value-target () ($ κ) (κ⊒κ .κ)
runtime-type-app-source-no-value-target () vV (⊕⊒⊕ M⊒M′ N⊒N′)
runtime-type-app-source-no-value-target app (vV ⟨ i ⟩)
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  runtime-type-app-source-no-value-target app vV M⊒M′
runtime-type-app-source-no-value-target app (vV ⟨ i ⟩)
    (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  runtime-type-app-source-no-value-target app vV M⊒M′
runtime-type-app-source-no-value-target () vV (cast+⊒ pᶜ r≈t⨟p M⊒M′)
runtime-type-app-source-no-value-target () vV (cast-⊒ pᶜ r≈t⨟p M⊒M′)

type-app-source-no-value-target :
  ∀ {Δ σ γ L V p} →
  Value V →
  Δ ∣ σ ∣ γ ⊢ L • ⊒ V ∶ p →
  ⊥
type-app-source-no-value-target =
  runtime-type-app-source-no-value-target runtime-•

data NeutralSource : Term → Set where
  neutral-` : ∀ {x} → NeutralSource (` x)
  neutral-· : ∀ {L M} → NeutralSource (L · M)
  neutral-⊕ : ∀ {L op M} → NeutralSource (L ⊕[ op ] M)
  neutral-blame : NeutralSource blame

renameᵗᵐ-preserves-NeutralSource :
  ∀ ρ {M} →
  NeutralSource M →
  NeutralSource (renameᵗᵐ ρ M)
renameᵗᵐ-preserves-NeutralSource ρ neutral-` =
  neutral-`
renameᵗᵐ-preserves-NeutralSource ρ neutral-· =
  neutral-·
renameᵗᵐ-preserves-NeutralSource ρ neutral-⊕ =
  neutral-⊕
renameᵗᵐ-preserves-NeutralSource ρ neutral-blame =
  neutral-blame

open-preserves-NeutralSource :
  ∀ {M α β} →
  NeutralSource (M [ α ]ᵀ) →
  NeutralSource (M [ β ]ᵀ)
open-preserves-NeutralSource {M = ` x} neutral-` =
  neutral-`
open-preserves-NeutralSource {M = ƛ M} ()
open-preserves-NeutralSource {M = L · M} neutral-· =
  neutral-·
open-preserves-NeutralSource {M = Λ M} ()
open-preserves-NeutralSource {M = M •} ()
open-preserves-NeutralSource {M = ν A L c} ()
open-preserves-NeutralSource {M = $ κ} ()
open-preserves-NeutralSource {M = L ⊕[ op ] M} neutral-⊕ =
  neutral-⊕
open-preserves-NeutralSource {M = M ⟨ c ⟩} ()
open-preserves-NeutralSource {M = blame} neutral-blame =
  neutral-blame

neutral-source-no-value-target :
  ∀ {Δ σ γ M V p} →
  NeutralSource M →
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  ⊥
neutral-source-no-value-target neu vV (extend qᶜ pαᶜ M⊒V) =
  neutral-source-no-value-target neu vV M⊒V
neutral-source-no-value-target neu vV
    (split {N = N} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ M⊒V) =
  neutral-source-no-value-target
    (open-preserves-NeutralSource {M = N} {α = αᵢ} {β = α} neu)
    vV
    M⊒V
neutral-source-no-value-target neu () (⊒blame pᶜ)
neutral-source-no-value-target neutral-` () (x⊒x pᶜ x∋p)
neutral-source-no-value-target () vV (ƛ⊒ƛ p↦qᶜ N⊒N′)
neutral-source-no-value-target neutral-· () (·⊒· qᶜ L⊒L′ M⊒M′)
neutral-source-no-value-target () (Λ vV) (Λ⊒Λ allᶜ vV₁ V⊒V′)
neutral-source-no-value-target neu (Λ vV) (⊒Λ pᶜ N⊒V′) =
  neutral-source-no-value-target
    (renameᵗᵐ-preserves-NeutralSource suc neu)
    vV
    N⊒V′
neutral-source-no-value-target neu (vV ⟨ i ⟩)
    (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s) =
  neutral-source-no-value-target
    (renameᵗᵐ-preserves-NeutralSource suc neu)
    (vV ⟨ sᵢ ⟩)
    N⊒V′s
neutral-source-no-value-target () vV (α⊒α qᶜ pαᶜ L⊒L′)
neutral-source-no-value-target neu () (⊒α pαᶜ L⊒L′)
neutral-source-no-value-target () vV (ν⊒ν pᶜ qᶜ N⊒N′)
neutral-source-no-value-target neu () (⊒ν pᶜ N⊒N′)
neutral-source-no-value-target () vV (ν⊒ pᶜ N⊒N′)
neutral-source-no-value-target () ($ κ) (κ⊒κ .κ)
neutral-source-no-value-target neutral-⊕ () (⊕⊒⊕ M⊒M′ N⊒N′)
neutral-source-no-value-target neu (vV ⟨ i ⟩)
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  neutral-source-no-value-target neu vV M⊒M′
neutral-source-no-value-target neu (vV ⟨ i ⟩)
    (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  neutral-source-no-value-target neu vV M⊒M′
neutral-source-no-value-target () vV (cast+⊒ pᶜ r≈t⨟p M⊒M′)
neutral-source-no-value-target () vV (cast-⊒ pᶜ r≈t⨟p M⊒M′)
