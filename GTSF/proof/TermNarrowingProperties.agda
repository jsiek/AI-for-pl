module proof.TermNarrowingProperties where

-- File Charter:
--   * Admissible rules and structural lemmas for term narrowing.
--   * Provides the cambridge23 two-sided cast derived rules and source-shape
--     exclusion lemmas for value-target narrowing.
--   * Depends on the public definitions in `TermNarrowing` and `NarrowWiden`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; zero)

open import Types
open import Coercions
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TypeCheck using (inert?; value?)
open import TermNarrowing using
  ( ⇑ᵍ
  ; _∣_∣_⊢_⊒_∶_
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
open import proof.NuTermProperties using (renameᵗᵐ-preserves-Value)

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
-- Value reflection
------------------------------------------------------------------------

inert?-none-no-inert :
  ∀ {c} →
  inert? c ≡ nothing →
  Inert c →
  ⊥
inert?-none-no-inert {c = id A} refl ()
inert?-none-no-inert {c = c ︔ d} refl ()
inert?-none-no-inert {c = c ↦ d} () (c ↦ d)
inert?-none-no-inert {c = `∀ c} () (`∀ c)
inert?-none-no-inert {c = G !} () (G !)
inert?-none-no-inert {c = G ？} refl ()
inert?-none-no-inert {c = seal A α} () (seal A α)
inert?-none-no-inert {c = unseal α A} refl ()
inert?-none-no-inert {c = gen A c} () (gen A c)
inert?-none-no-inert {c = inst B c} refl ()

value?-none-no-value :
  ∀ {M} →
  value? M ≡ nothing →
  Value M →
  ⊥
value?-none-no-value {M = ` x} refl ()
value?-none-no-value {M = ƛ M} () (ƛ M)
value?-none-no-value {M = L · M} refl ()
value?-none-no-value {M = Λ M} eq (Λ vM)
    with value? M in valueM≡
value?-none-no-value {M = Λ M} () (Λ vM) | just vM′
value?-none-no-value {M = Λ M} refl (Λ vM) | nothing =
  value?-none-no-value valueM≡ vM
value?-none-no-value {M = M •} refl ()
value?-none-no-value {M = ν A L c} refl ()
value?-none-no-value {M = $ κ} () ($ κ)
value?-none-no-value {M = L ⊕[ op ] M} refl ()
value?-none-no-value {M = M ⟨ c ⟩} eq (vM ⟨ i ⟩)
    with value? M in valueM≡ | inert? c in inertc≡
value?-none-no-value {M = M ⟨ c ⟩} () (vM ⟨ i ⟩)
    | just vM′ | just i′
value?-none-no-value {M = M ⟨ c ⟩} refl (vM ⟨ i ⟩)
    | nothing | inert =
  value?-none-no-value valueM≡ vM
value?-none-no-value {M = M ⟨ c ⟩} refl (vM ⟨ i ⟩)
    | just vM′ | nothing =
  inert?-none-no-inert inertc≡ i
value?-none-no-value {M = blame} refl ()

renameᶜ-reflects-Inert :
  ∀ ρ {c} →
  Inert (renameᶜ ρ c) →
  Inert c
renameᶜ-reflects-Inert ρ {c = id A} ()
renameᶜ-reflects-Inert ρ {c = c ︔ d} ()
renameᶜ-reflects-Inert ρ {c = c ↦ d} (c′ ↦ d′) =
  c ↦ d
renameᶜ-reflects-Inert ρ {c = `∀ c} (`∀ c′) =
  `∀ c
renameᶜ-reflects-Inert ρ {c = G !} (G′ !) =
  G !
renameᶜ-reflects-Inert ρ {c = G ？} ()
renameᶜ-reflects-Inert ρ {c = seal A α} (seal A′ α′) =
  seal A α
renameᶜ-reflects-Inert ρ {c = unseal α A} ()
renameᶜ-reflects-Inert ρ {c = gen A c} (gen A′ c′) =
  gen A c
renameᶜ-reflects-Inert ρ {c = inst B c} ()

renameᵗᵐ-reflects-Value :
  ∀ ρ {M} →
  Value (renameᵗᵐ ρ M) →
  Value M
renameᵗᵐ-reflects-Value ρ {M = ` x} ()
renameᵗᵐ-reflects-Value ρ {M = ƛ M} (ƛ M′) =
  ƛ M
renameᵗᵐ-reflects-Value ρ {M = L · M} ()
renameᵗᵐ-reflects-Value ρ {M = Λ M} (Λ vM) =
  Λ (renameᵗᵐ-reflects-Value (extᵗ ρ) vM)
renameᵗᵐ-reflects-Value ρ {M = M •} ()
renameᵗᵐ-reflects-Value ρ {M = ν A L c} ()
renameᵗᵐ-reflects-Value ρ {M = $ κ} ($ .κ) =
  $ κ
renameᵗᵐ-reflects-Value ρ {M = L ⊕[ op ] M} ()
renameᵗᵐ-reflects-Value ρ {M = M ⟨ c ⟩} (vM ⟨ i ⟩) =
  renameᵗᵐ-reflects-Value ρ vM ⟨ renameᶜ-reflects-Inert ρ i ⟩
renameᵗᵐ-reflects-Value ρ {M = blame} ()

rerenameᵗᵐ-preserves-Value :
  ∀ ρ ρ′ {M} →
  Value (renameᵗᵐ ρ M) →
  Value (renameᵗᵐ ρ′ M)
rerenameᵗᵐ-preserves-Value ρ ρ′ vM =
  renameᵗᵐ-preserves-Value ρ′ (renameᵗᵐ-reflects-Value ρ vM)

open-preserves-Value :
  ∀ {M α β} →
  Value (M [ α ]ᵀ) →
  Value (M [ β ]ᵀ)
open-preserves-Value {M = M} {α = α} {β = β} vM =
  rerenameᵗᵐ-preserves-Value (singleRenameᵗ α) (singleRenameᵗ β) vM

data LambdaSource : Term → Set where
  lambda-source : ∀ {M} → LambdaSource (Λ M)

data LambdaBodyValue : Term → Set where
  lambda-body-value : ∀ {M} → Value M → LambdaBodyValue (Λ M)

renameᵗᵐ-preserves-LambdaSource :
  ∀ ρ {M} →
  LambdaSource M →
  LambdaSource (renameᵗᵐ ρ M)
renameᵗᵐ-preserves-LambdaSource ρ lambda-source =
  lambda-source

open-preserves-LambdaSource :
  ∀ {M α β} →
  LambdaSource (M [ α ]ᵀ) →
  LambdaSource (M [ β ]ᵀ)
open-preserves-LambdaSource {M = ` x} ()
open-preserves-LambdaSource {M = ƛ M} ()
open-preserves-LambdaSource {M = L · M} ()
open-preserves-LambdaSource {M = Λ M} lambda-source =
  lambda-source
open-preserves-LambdaSource {M = M •} ()
open-preserves-LambdaSource {M = ν A L c} ()
open-preserves-LambdaSource {M = $ κ} ()
open-preserves-LambdaSource {M = L ⊕[ op ] M} ()
open-preserves-LambdaSource {M = M ⟨ c ⟩} ()
open-preserves-LambdaSource {M = blame} ()

open-preserves-LambdaBodyValue :
  ∀ {M α β} →
  LambdaBodyValue (M [ α ]ᵀ) →
  LambdaBodyValue (M [ β ]ᵀ)
open-preserves-LambdaBodyValue {M = ` x} ()
open-preserves-LambdaBodyValue {M = ƛ M} ()
open-preserves-LambdaBodyValue {M = L · M} ()
open-preserves-LambdaBodyValue {M = Λ M} {α = α} {β = β}
    (lambda-body-value vM) =
  lambda-body-value
    (rerenameᵗᵐ-preserves-Value
      (extᵗ (singleRenameᵗ α))
      (extᵗ (singleRenameᵗ β))
      vM)
open-preserves-LambdaBodyValue {M = M •} ()
open-preserves-LambdaBodyValue {M = ν A L c} ()
open-preserves-LambdaBodyValue {M = $ κ} ()
open-preserves-LambdaBodyValue {M = L ⊕[ op ] M} ()
open-preserves-LambdaBodyValue {M = M ⟨ c ⟩} ()
open-preserves-LambdaBodyValue {M = blame} ()

renameᵗᵐ-reflects-LambdaBodyValue :
  ∀ ρ {M} →
  LambdaBodyValue (renameᵗᵐ ρ M) →
  LambdaBodyValue M
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = ` x} ()
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = ƛ M} ()
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = L · M} ()
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = Λ M}
    (lambda-body-value vM) =
  lambda-body-value (renameᵗᵐ-reflects-Value (extᵗ ρ) vM)
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = M •} ()
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = ν A L c} ()
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = $ κ} ()
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = L ⊕[ op ] M} ()
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = M ⟨ c ⟩} ()
renameᵗᵐ-reflects-LambdaBodyValue ρ {M = blame} ()

lambda-source-value-target-body-value :
  ∀ {Δ σ γ M V p} →
  LambdaSource M →
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  LambdaBodyValue M
lambda-source-value-target-body-value src vV (extend qᶜ pαᶜ M⊒V) =
  lambda-source-value-target-body-value src vV M⊒V
lambda-source-value-target-body-value src vV
    (split {N = N} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ M⊒V) =
  open-preserves-LambdaBodyValue {M = N} {α = α} {β = αᵢ}
    (lambda-source-value-target-body-value
      (open-preserves-LambdaSource {M = N} {α = αᵢ} {β = α} src)
      vV
      M⊒V)
lambda-source-value-target-body-value src () (⊒blame pᶜ)
lambda-source-value-target-body-value src () (x⊒x pᶜ x∋p)
lambda-source-value-target-body-value () vV (ƛ⊒ƛ p↦qᶜ N⊒N′)
lambda-source-value-target-body-value () vV (·⊒· qᶜ L⊒L′ M⊒M′)
lambda-source-value-target-body-value lambda-source (Λ vV)
    (Λ⊒Λ allᶜ vM M⊒V) =
  lambda-body-value vM
lambda-source-value-target-body-value src (Λ vV) (⊒Λ pᶜ N⊒V′) =
  renameᵗᵐ-reflects-LambdaBodyValue suc
    (lambda-source-value-target-body-value
      (renameᵗᵐ-preserves-LambdaSource suc src)
      vV
      N⊒V′)
lambda-source-value-target-body-value src (vV ⟨ i ⟩)
    (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s) =
  renameᵗᵐ-reflects-LambdaBodyValue suc
    (lambda-source-value-target-body-value
      (renameᵗᵐ-preserves-LambdaSource suc src)
      (vV ⟨ sᵢ ⟩)
      N⊒V′s)
lambda-source-value-target-body-value () vV (α⊒α qᶜ pαᶜ L⊒L′)
lambda-source-value-target-body-value src () (⊒α pαᶜ L⊒L′)
lambda-source-value-target-body-value () vV (ν⊒ν pᶜ qᶜ N⊒N′)
lambda-source-value-target-body-value src () (⊒ν pᶜ N⊒N′)
lambda-source-value-target-body-value () vV (ν⊒ pᶜ N⊒N′)
lambda-source-value-target-body-value () ($ κ) (κ⊒κ .κ)
lambda-source-value-target-body-value () vV (⊕⊒⊕ M⊒M′ N⊒N′)
lambda-source-value-target-body-value src (vV ⟨ i ⟩)
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  lambda-source-value-target-body-value src vV M⊒M′
lambda-source-value-target-body-value src (vV ⟨ i ⟩)
    (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  lambda-source-value-target-body-value src vV M⊒M′
lambda-source-value-target-body-value () vV
    (cast+⊒ pᶜ r≈t⨟p M⊒M′)
lambda-source-value-target-body-value () vV
    (cast-⊒ pᶜ r≈t⨟p M⊒M′)

lambda-source-value-target-source-value :
  ∀ {Δ σ γ M V p} →
  Value V →
  Δ ∣ σ ∣ γ ⊢ Λ M ⊒ V ∶ p →
  Value M
lambda-source-value-target-source-value vV M⊒V
    with lambda-source-value-target-body-value lambda-source vV M⊒V
lambda-source-value-target-source-value vV M⊒V
    | lambda-body-value vM =
  vM

------------------------------------------------------------------------
-- Source-shape exclusions
------------------------------------------------------------------------

data NuSource : Term → Set where
  nu-source : ∀ {A L c} → NuSource (ν A L c)

renameᵗᵐ-preserves-NuSource :
  ∀ ρ {M} →
  NuSource M →
  NuSource (renameᵗᵐ ρ M)
renameᵗᵐ-preserves-NuSource ρ nu-source =
  nu-source

open-preserves-NuSource :
  ∀ {M α β} →
  NuSource (M [ α ]ᵀ) →
  NuSource (M [ β ]ᵀ)
open-preserves-NuSource {M = ` x} ()
open-preserves-NuSource {M = ƛ M} ()
open-preserves-NuSource {M = L · M} ()
open-preserves-NuSource {M = Λ M} ()
open-preserves-NuSource {M = M •} ()
open-preserves-NuSource {M = ν A L c} nu-source =
  nu-source
open-preserves-NuSource {M = $ κ} ()
open-preserves-NuSource {M = L ⊕[ op ] M} ()
open-preserves-NuSource {M = M ⟨ c ⟩} ()
open-preserves-NuSource {M = blame} ()

data CastSource : Term → Set where
  cast-source : ∀ {M c} → CastSource (M ⟨ c ⟩)

renameᵗᵐ-preserves-CastSource :
  ∀ ρ {M} →
  CastSource M →
  CastSource (renameᵗᵐ ρ M)
renameᵗᵐ-preserves-CastSource ρ cast-source =
  cast-source

open-preserves-CastSource :
  ∀ {M α β} →
  CastSource (M [ α ]ᵀ) →
  CastSource (M [ β ]ᵀ)
open-preserves-CastSource {M = ` x} ()
open-preserves-CastSource {M = ƛ M} ()
open-preserves-CastSource {M = L · M} ()
open-preserves-CastSource {M = Λ M} ()
open-preserves-CastSource {M = M •} ()
open-preserves-CastSource {M = ν A L c} ()
open-preserves-CastSource {M = $ κ} ()
open-preserves-CastSource {M = L ⊕[ op ] M} ()
open-preserves-CastSource {M = M ⟨ c ⟩} cast-source =
  cast-source
open-preserves-CastSource {M = blame} ()

data CastSourceValueTarget :
  ∀ {Δ σ γ M V p} →
  CastSource M →
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  Set₁ where

  csvt-extend :
    ∀ {Δ σ γ M N′ p q A B C D α}
      {src : CastSource M}
      {vV : Value (N′ [ α ]ᵀ)}
      {qᶜ : Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A}
      {pαᶜ : Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ)
        ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D}
      {M⊒V : Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ
        ⊢ M ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ}
    → CastSourceValueTarget src vV M⊒V
    → CastSourceValueTarget src vV (extend qᶜ pαᶜ M⊒V)

  csvt-split :
    ∀ {Δ σ γ N N′ p q A C D α αᵢ}
      {src : CastSource (N [ αᵢ ]ᵀ)}
      {vV : Value (N′ [ α ]ᵀ)}
      {qᶜ : Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
        ⊢ q ∶ᶜ ★ ⊒ A}
      {pαᶜ : Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
        ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D}
      {M⊒V : Δ ∣ (α ꞉ q) ∷ σ ∣ γ
        ⊢ N [ α ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ}
    → CastSourceValueTarget
        (open-preserves-CastSource {M = N} {α = αᵢ} {β = α} src)
        vV
        M⊒V
    → CastSourceValueTarget src vV (split qᶜ pαᶜ M⊒V)

  csvt-⊒Λ :
    ∀ {Δ σ γ A B N V′ p}
      {src : CastSource N}
      {vV : Value V′}
      {pᶜ : Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B}
      {N⊒V′ : suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p}
    → CastSourceValueTarget
        (renameᵗᵐ-preserves-CastSource suc src)
        vV
        N⊒V′
    → CastSourceValueTarget src (Λ vV) (⊒Λ pᶜ N⊒V′)

  csvt-⊒⟨ν⟩ :
    ∀ {Δ σ γ A B N V′ p s}
      {src : CastSource N}
      {vV : Value V′}
      {pᶜ : Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B}
      {sᵢ : Inert s}
      {i : Inert (gen A s)}
      {N⊒V′s : suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ ⇑ᵗᵐ N ⊒ V′ ⟨ s ⟩ ∶ p}
    → CastSourceValueTarget
        (renameᵗᵐ-preserves-CastSource suc src)
        (vV ⟨ sᵢ ⟩)
        N⊒V′s
    → CastSourceValueTarget src (vV ⟨ i ⟩)
        (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s)

  csvt-⊒cast+ :
    ∀ {Δ σ γ M M′ q r s A B C D}
      {src : CastSource M}
      {vV : Value M′}
      {i : Inert (- s)}
      {qᶜ : Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D}
      {q⨟s≈r : Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B}
      {M⊒M′ : Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r}
    → CastSourceValueTarget src vV M⊒M′
    → CastSourceValueTarget src (vV ⟨ i ⟩)
        (⊒cast+ qᶜ q⨟s≈r M⊒M′)

  csvt-⊒cast- :
    ∀ {Δ σ γ M M′ q r s A B C D}
      {src : CastSource M}
      {vV : Value M′}
      {i : Inert s}
      {qᶜ : Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D}
      {q⨟s≈r : Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B}
      {M⊒M′ : Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q}
    → CastSourceValueTarget src vV M⊒M′
    → CastSourceValueTarget src (vV ⟨ i ⟩)
        (⊒cast- qᶜ q⨟s≈r M⊒M′)

  csvt-cast+⊒ :
    ∀ {Δ σ γ M M′ p r t A B C D}
      {vV : Value M′}
      {pᶜ : Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D}
      {r≈t⨟p : Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B}
      {M⊒M′ : Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p}
    → CastSourceValueTarget cast-source vV
        (cast+⊒ pᶜ r≈t⨟p M⊒M′)

  csvt-cast-⊒ :
    ∀ {Δ σ γ M M′ p r t A B C D}
      {vV : Value M′}
      {pᶜ : Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D}
      {r≈t⨟p : Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B}
      {M⊒M′ : Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r}
    → CastSourceValueTarget cast-source vV
        (cast-⊒ pᶜ r≈t⨟p M⊒M′)

cast-source-value-target-inversion :
  ∀ {Δ σ γ M V p} →
  (src : CastSource M) →
  (vV : Value V) →
  (M⊒V : Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p) →
  CastSourceValueTarget src vV M⊒V
cast-source-value-target-inversion src vV (extend qᶜ pαᶜ M⊒V) =
  csvt-extend (cast-source-value-target-inversion src vV M⊒V)
cast-source-value-target-inversion src vV
    (split {N = N} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ M⊒V) =
  csvt-split
    (cast-source-value-target-inversion
      (open-preserves-CastSource {M = N} {α = αᵢ} {β = α} src)
      vV
      M⊒V)
cast-source-value-target-inversion src () (⊒blame pᶜ)
cast-source-value-target-inversion src () (x⊒x pᶜ x∋p)
cast-source-value-target-inversion () vV (ƛ⊒ƛ p↦qᶜ N⊒N′)
cast-source-value-target-inversion () vV (·⊒· qᶜ L⊒L′ M⊒M′)
cast-source-value-target-inversion () (Λ vV)
    (Λ⊒Λ allᶜ vV₁ V⊒V′)
cast-source-value-target-inversion src (Λ vV) (⊒Λ pᶜ N⊒V′) =
  csvt-⊒Λ
    (cast-source-value-target-inversion
      (renameᵗᵐ-preserves-CastSource suc src)
      vV
      N⊒V′)
cast-source-value-target-inversion src (vV ⟨ i ⟩)
    (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s) =
  csvt-⊒⟨ν⟩
    (cast-source-value-target-inversion
      (renameᵗᵐ-preserves-CastSource suc src)
      (vV ⟨ sᵢ ⟩)
      N⊒V′s)
cast-source-value-target-inversion () vV (α⊒α qᶜ pαᶜ L⊒L′)
cast-source-value-target-inversion src () (⊒α pαᶜ L⊒L′)
cast-source-value-target-inversion () vV (ν⊒ν pᶜ qᶜ N⊒N′)
cast-source-value-target-inversion src () (⊒ν pᶜ N⊒N′)
cast-source-value-target-inversion () vV (ν⊒ pᶜ N⊒N′)
cast-source-value-target-inversion () ($ κ) (κ⊒κ .κ)
cast-source-value-target-inversion () vV (⊕⊒⊕ M⊒M′ N⊒N′)
cast-source-value-target-inversion src (vV ⟨ i ⟩)
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  csvt-⊒cast+
    (cast-source-value-target-inversion src vV M⊒M′)
cast-source-value-target-inversion src (vV ⟨ i ⟩)
    (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  csvt-⊒cast-
    (cast-source-value-target-inversion src vV M⊒M′)
cast-source-value-target-inversion cast-source vV
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  csvt-cast+⊒
cast-source-value-target-inversion cast-source vV
    (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  csvt-cast-⊒

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
