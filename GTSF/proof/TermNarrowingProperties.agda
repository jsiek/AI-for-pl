module proof.TermNarrowingProperties where

-- File Charter:
--   * Admissible rules and structural lemmas for term narrowing.
--   * Provides the cambridge23 two-sided cast derived rules and source-shape
--     exclusion lemmas for value-target narrowing.
--   * Depends on the public definitions in `TermNarrowing` and `NarrowWiden`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
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
open import proof.NuTermProperties
  using (renameᵗᵐ-preserves-Value; renameᵗᵐ-reflects-Value)
open import proof.ReductionProperties using
  ( CatchupSafe
  ; safe-value
  ; safe-ν
  ; safe-cast
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

data NuSourceValueTarget :
  ∀ {Δ σ γ M V p} →
  NuSource M →
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  Set₁ where

  nsvt-extend :
    ∀ {Δ σ γ M N′ p q A B C D α}
      {src : NuSource M}
      {vV : Value (N′ [ α ]ᵀ)}
      {qᶜ : Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A}
      {pαᶜ : Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ)
        ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D}
      {M⊒V : Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ
        ⊢ M ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ}
    → NuSourceValueTarget src vV M⊒V
    → NuSourceValueTarget src vV (extend qᶜ pαᶜ M⊒V)

  nsvt-split :
    ∀ {Δ σ γ N N′ p q A C D α αᵢ}
      {src : NuSource (N [ αᵢ ]ᵀ)}
      {vV : Value (N′ [ α ]ᵀ)}
      {qᶜ : Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
        ⊢ q ∶ᶜ ★ ⊒ A}
      {pαᶜ : Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
        ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D}
      {M⊒V : Δ ∣ (α ꞉ q) ∷ σ ∣ γ
        ⊢ N [ α ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ}
    → NuSourceValueTarget
        (open-preserves-NuSource {M = N} {α = αᵢ} {β = α} src)
        vV
        M⊒V
    → NuSourceValueTarget src vV (split qᶜ pαᶜ M⊒V)

  nsvt-⊒Λ :
    ∀ {Δ σ γ A B N V′ p}
      {src : NuSource N}
      {vV : Value V′}
      {pᶜ : Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B}
      {N⊒V′ : suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p}
    → NuSourceValueTarget
        (renameᵗᵐ-preserves-NuSource suc src)
        vV
        N⊒V′
    → NuSourceValueTarget src (Λ vV) (⊒Λ pᶜ N⊒V′)

  nsvt-⊒⟨ν⟩ :
    ∀ {Δ σ γ A B N V′ p s}
      {src : NuSource N}
      {vV : Value V′}
      {pᶜ : Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B}
      {sᵢ : Inert s}
      {i : Inert (gen A s)}
      {N⊒V′s : suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ ⇑ᵗᵐ N ⊒ V′ ⟨ s ⟩ ∶ p}
    → NuSourceValueTarget
        (renameᵗᵐ-preserves-NuSource suc src)
        (vV ⟨ sᵢ ⟩)
        N⊒V′s
    → NuSourceValueTarget src (vV ⟨ i ⟩)
        (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s)

  nsvt-⊒cast+ :
    ∀ {Δ σ γ M M′ q r s A B C D}
      {src : NuSource M}
      {vV : Value M′}
      {i : Inert (- s)}
      {qᶜ : Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D}
      {q⨟s≈r : Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B}
      {M⊒M′ : Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r}
    → NuSourceValueTarget src vV M⊒M′
    → NuSourceValueTarget src (vV ⟨ i ⟩)
        (⊒cast+ qᶜ q⨟s≈r M⊒M′)

  nsvt-⊒cast- :
    ∀ {Δ σ γ M M′ q r s A B C D}
      {src : NuSource M}
      {vV : Value M′}
      {i : Inert s}
      {qᶜ : Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D}
      {q⨟s≈r : Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B}
      {M⊒M′ : Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q}
    → NuSourceValueTarget src vV M⊒M′
    → NuSourceValueTarget src (vV ⟨ i ⟩)
        (⊒cast- qᶜ q⨟s≈r M⊒M′)

  nsvt-ν⊒ :
    ∀ {Δ σ γ N N′ p A B}
      {vV : Value N′}
      {pᶜ : Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B}
      {N⊒N′ : suc Δ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ N ⊒ ⇑ᵗᵐ N′ ∶ ⇑ᶜ p}
    → NuSourceValueTarget nu-source vV (ν⊒ pᶜ N⊒N′)

nu-source-value-target-inversion :
  ∀ {Δ σ γ M V p} →
  (src : NuSource M) →
  (vV : Value V) →
  (M⊒V : Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p) →
  NuSourceValueTarget src vV M⊒V
nu-source-value-target-inversion src vV (extend qᶜ pαᶜ M⊒V) =
  nsvt-extend (nu-source-value-target-inversion src vV M⊒V)
nu-source-value-target-inversion src vV
    (split {N = N} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ M⊒V) =
  nsvt-split
    (nu-source-value-target-inversion
      (open-preserves-NuSource {M = N} {α = αᵢ} {β = α} src)
      vV
      M⊒V)
nu-source-value-target-inversion src () (⊒blame pᶜ)
nu-source-value-target-inversion src () (x⊒x pᶜ x∋p)
nu-source-value-target-inversion () vV (ƛ⊒ƛ p↦qᶜ N⊒N′)
nu-source-value-target-inversion () vV (·⊒· qᶜ L⊒L′ M⊒M′)
nu-source-value-target-inversion () (Λ vV)
    (Λ⊒Λ allᶜ vV₁ V⊒V′)
nu-source-value-target-inversion src (Λ vV) (⊒Λ pᶜ N⊒V′) =
  nsvt-⊒Λ
    (nu-source-value-target-inversion
      (renameᵗᵐ-preserves-NuSource suc src)
      vV
      N⊒V′)
nu-source-value-target-inversion src (vV ⟨ i ⟩)
    (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s) =
  nsvt-⊒⟨ν⟩
    (nu-source-value-target-inversion
      (renameᵗᵐ-preserves-NuSource suc src)
      (vV ⟨ sᵢ ⟩)
      N⊒V′s)
nu-source-value-target-inversion src () (α⊒α qᶜ pαᶜ L⊒L′)
nu-source-value-target-inversion src () (⊒α pαᶜ L⊒L′)
nu-source-value-target-inversion src () (ν⊒ν pᶜ qᶜ N⊒N′)
nu-source-value-target-inversion src () (⊒ν pᶜ N⊒N′)
nu-source-value-target-inversion nu-source vV (ν⊒ pᶜ N⊒N′) =
  nsvt-ν⊒
nu-source-value-target-inversion () ($ κ) (κ⊒κ .κ)
nu-source-value-target-inversion () vV (⊕⊒⊕ M⊒M′ N⊒N′)
nu-source-value-target-inversion src (vV ⟨ i ⟩)
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  nsvt-⊒cast+
    (nu-source-value-target-inversion src vV M⊒M′)
nu-source-value-target-inversion src (vV ⟨ i ⟩)
    (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  nsvt-⊒cast-
    (nu-source-value-target-inversion src vV M⊒M′)
nu-source-value-target-inversion () vV
    (cast+⊒ pᶜ r≈t⨟p M⊒M′)
nu-source-value-target-inversion () vV
    (cast-⊒ pᶜ r≈t⨟p M⊒M′)

data NuSourceBase : Set₁ where
  nu-base :
    ∀ {Δ σ γ N N′ p A B}
    → Value N′
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B
    → suc Δ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ N ⊒ ⇑ᵗᵐ N′ ∶ ⇑ᶜ p
    → NuSourceBase

nu-source-value-target-base :
  ∀ {Δ σ γ M V p src vV M⊒V} →
  NuSourceValueTarget {Δ} {σ} {γ} {M} {V} {p} src vV M⊒V →
  NuSourceBase
nu-source-value-target-base (nsvt-extend hist) =
  nu-source-value-target-base hist
nu-source-value-target-base (nsvt-split hist) =
  nu-source-value-target-base hist
nu-source-value-target-base (nsvt-⊒Λ hist) =
  nu-source-value-target-base hist
nu-source-value-target-base (nsvt-⊒⟨ν⟩ hist) =
  nu-source-value-target-base hist
nu-source-value-target-base (nsvt-⊒cast+ hist) =
  nu-source-value-target-base hist
nu-source-value-target-base (nsvt-⊒cast- hist) =
  nu-source-value-target-base hist
nu-source-value-target-base
    (nsvt-ν⊒ {vV = vV} {pᶜ = pᶜ} {N⊒N′ = N⊒N′}) =
  nu-base vV pᶜ N⊒N′

data NuSourceBaseEmpty : Set₁ where
  nu-base-empty :
    ∀ {Δ σ N N′ p A B}
    → Value N′
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B
    → suc Δ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ ∣ []
        ⊢ N ⊒ ⇑ᵗᵐ N′ ∶ ⇑ᶜ p
    → NuSourceBaseEmpty

nu-source-value-target-base-empty :
  ∀ {Δ σ M V p src vV M⊒V} →
  NuSourceValueTarget {Δ} {σ} {[]} {M} {V} {p} src vV M⊒V →
  NuSourceBaseEmpty
nu-source-value-target-base-empty (nsvt-extend hist) =
  nu-source-value-target-base-empty hist
nu-source-value-target-base-empty (nsvt-split hist) =
  nu-source-value-target-base-empty hist
nu-source-value-target-base-empty (nsvt-⊒Λ hist) =
  nu-source-value-target-base-empty hist
nu-source-value-target-base-empty (nsvt-⊒⟨ν⟩ hist) =
  nu-source-value-target-base-empty hist
nu-source-value-target-base-empty (nsvt-⊒cast+ hist) =
  nu-source-value-target-base-empty hist
nu-source-value-target-base-empty (nsvt-⊒cast- hist) =
  nu-source-value-target-base-empty hist
nu-source-value-target-base-empty
    (nsvt-ν⊒ {vV = vV} {pᶜ = pᶜ} {N⊒N′ = N⊒N′}) =
  nu-base-empty vV pᶜ N⊒N′

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

data CastSourceBase : Set₁ where
  cast-base+ :
    ∀ {Δ σ γ M M′ p r t A B C D}
    → Value M′
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D
    → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p
    → CastSourceBase

  cast-base- :
    ∀ {Δ σ γ M M′ p r t A B C D}
    → Value M′
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D
    → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r
    → CastSourceBase

cast-source-value-target-base :
  ∀ {Δ σ γ M V p src vV M⊒V} →
  CastSourceValueTarget {Δ} {σ} {γ} {M} {V} {p} src vV M⊒V →
  CastSourceBase
cast-source-value-target-base (csvt-extend hist) =
  cast-source-value-target-base hist
cast-source-value-target-base (csvt-split hist) =
  cast-source-value-target-base hist
cast-source-value-target-base (csvt-⊒Λ hist) =
  cast-source-value-target-base hist
cast-source-value-target-base (csvt-⊒⟨ν⟩ hist) =
  cast-source-value-target-base hist
cast-source-value-target-base (csvt-⊒cast+ hist) =
  cast-source-value-target-base hist
cast-source-value-target-base (csvt-⊒cast- hist) =
  cast-source-value-target-base hist
cast-source-value-target-base
    (csvt-cast+⊒ {vV = vV} {pᶜ = pᶜ}
      {r≈t⨟p = r≈t⨟p} {M⊒M′ = M⊒M′}) =
  cast-base+ vV pᶜ r≈t⨟p M⊒M′
cast-source-value-target-base
    (csvt-cast-⊒ {vV = vV} {pᶜ = pᶜ}
      {r≈t⨟p = r≈t⨟p} {M⊒M′ = M⊒M′}) =
  cast-base- vV pᶜ r≈t⨟p M⊒M′

data CastSourceBaseEmpty : Set₁ where
  cast-base-empty+ :
    ∀ {Δ σ M M′ p r t A B C D}
    → Value M′
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D
    → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
    → Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p
    → CastSourceBaseEmpty

  cast-base-empty- :
    ∀ {Δ σ M M′ p r t A B C D}
    → Value M′
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D
    → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
    → Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ r
    → CastSourceBaseEmpty

cast-source-value-target-base-empty :
  ∀ {Δ σ M V p src vV M⊒V} →
  CastSourceValueTarget {Δ} {σ} {[]} {M} {V} {p} src vV M⊒V →
  CastSourceBaseEmpty
cast-source-value-target-base-empty (csvt-extend hist) =
  cast-source-value-target-base-empty hist
cast-source-value-target-base-empty (csvt-split hist) =
  cast-source-value-target-base-empty hist
cast-source-value-target-base-empty (csvt-⊒Λ hist) =
  cast-source-value-target-base-empty hist
cast-source-value-target-base-empty (csvt-⊒⟨ν⟩ hist) =
  cast-source-value-target-base-empty hist
cast-source-value-target-base-empty (csvt-⊒cast+ hist) =
  cast-source-value-target-base-empty hist
cast-source-value-target-base-empty (csvt-⊒cast- hist) =
  cast-source-value-target-base-empty hist
cast-source-value-target-base-empty
    (csvt-cast+⊒ {vV = vV} {pᶜ = pᶜ}
      {r≈t⨟p = r≈t⨟p} {M⊒M′ = M⊒M′}) =
  cast-base-empty+ vV pᶜ r≈t⨟p M⊒M′
cast-source-value-target-base-empty
    (csvt-cast-⊒ {vV = vV} {pᶜ = pᶜ}
      {r≈t⨟p = r≈t⨟p} {M⊒M′ = M⊒M′}) =
  cast-base-empty- vV pᶜ r≈t⨟p M⊒M′

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

data NoActiveTypeApp : Term → Set where
  no-active-` : ∀ {x} → NoActiveTypeApp (` x)
  no-active-ƛ : ∀ {M} → NoActiveTypeApp (ƛ M)
  no-active-· :
    ∀ {L M} →
    NoActiveTypeApp L →
    NoActiveTypeApp M →
    NoActiveTypeApp (L · M)
  no-active-Λ : ∀ {M} → NoActiveTypeApp (Λ M)
  no-active-ν :
    ∀ {A L c} →
    NoActiveTypeApp L →
    NoActiveTypeApp (ν A L c)
  no-active-$ : ∀ {κ} → NoActiveTypeApp ($ κ)
  no-active-⊕ :
    ∀ {L op M} →
    NoActiveTypeApp L →
    NoActiveTypeApp M →
    NoActiveTypeApp (L ⊕[ op ] M)
  no-active-⟨⟩ :
    ∀ {M c} →
    NoActiveTypeApp M →
    NoActiveTypeApp (M ⟨ c ⟩)
  no-active-blame : NoActiveTypeApp blame

renameᵗᵐ-preserves-NoActiveTypeApp :
  ∀ ρ {M} →
  NoActiveTypeApp M →
  NoActiveTypeApp (renameᵗᵐ ρ M)
renameᵗᵐ-preserves-NoActiveTypeApp ρ no-active-` = no-active-`
renameᵗᵐ-preserves-NoActiveTypeApp ρ no-active-ƛ = no-active-ƛ
renameᵗᵐ-preserves-NoActiveTypeApp ρ (no-active-· noL noM) =
  no-active-·
    (renameᵗᵐ-preserves-NoActiveTypeApp ρ noL)
    (renameᵗᵐ-preserves-NoActiveTypeApp ρ noM)
renameᵗᵐ-preserves-NoActiveTypeApp ρ no-active-Λ = no-active-Λ
renameᵗᵐ-preserves-NoActiveTypeApp ρ (no-active-ν noL) =
  no-active-ν (renameᵗᵐ-preserves-NoActiveTypeApp ρ noL)
renameᵗᵐ-preserves-NoActiveTypeApp ρ no-active-$ = no-active-$
renameᵗᵐ-preserves-NoActiveTypeApp ρ (no-active-⊕ noL noM) =
  no-active-⊕
    (renameᵗᵐ-preserves-NoActiveTypeApp ρ noL)
    (renameᵗᵐ-preserves-NoActiveTypeApp ρ noM)
renameᵗᵐ-preserves-NoActiveTypeApp ρ (no-active-⟨⟩ noM) =
  no-active-⟨⟩ (renameᵗᵐ-preserves-NoActiveTypeApp ρ noM)
renameᵗᵐ-preserves-NoActiveTypeApp ρ no-active-blame =
  no-active-blame

renameᵗᵐ-reflects-NoActiveTypeApp :
  ∀ ρ {M} →
  NoActiveTypeApp (renameᵗᵐ ρ M) →
  NoActiveTypeApp M
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = ` x} noM = no-active-`
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = ƛ M} noM = no-active-ƛ
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = L · M}
    (no-active-· noL noM) =
  no-active-·
    (renameᵗᵐ-reflects-NoActiveTypeApp ρ noL)
    (renameᵗᵐ-reflects-NoActiveTypeApp ρ noM)
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = Λ M} noM = no-active-Λ
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = M •} ()
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = ν A L c} (no-active-ν noL) =
  no-active-ν (renameᵗᵐ-reflects-NoActiveTypeApp ρ noL)
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = $ κ} noM = no-active-$
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = L ⊕[ op ] M}
    (no-active-⊕ noL noM) =
  no-active-⊕
    (renameᵗᵐ-reflects-NoActiveTypeApp ρ noL)
    (renameᵗᵐ-reflects-NoActiveTypeApp ρ noM)
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = M ⟨ c ⟩}
    (no-active-⟨⟩ noM) =
  no-active-⟨⟩ (renameᵗᵐ-reflects-NoActiveTypeApp ρ noM)
renameᵗᵐ-reflects-NoActiveTypeApp ρ {M = blame} noM =
  no-active-blame

open-preserves-NoActiveTypeApp :
  ∀ {M α β} →
  NoActiveTypeApp (M [ α ]ᵀ) →
  NoActiveTypeApp (M [ β ]ᵀ)
open-preserves-NoActiveTypeApp {M = M} {α = α} {β = β} noM =
  renameᵗᵐ-preserves-NoActiveTypeApp (singleRenameᵗ β)
    (renameᵗᵐ-reflects-NoActiveTypeApp (singleRenameᵗ α) noM)

value-target-source-no-active :
  ∀ {Δ σ γ M V p} →
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  NoActiveTypeApp M
value-target-source-no-active vV (extend qᶜ pαᶜ M⊒V) =
  value-target-source-no-active vV M⊒V
value-target-source-no-active vV
    (split {N = N} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ M⊒V) =
  open-preserves-NoActiveTypeApp {M = N} {α = α} {β = αᵢ}
    (value-target-source-no-active vV M⊒V)
value-target-source-no-active () (⊒blame pᶜ)
value-target-source-no-active () (x⊒x pᶜ x∋p)
value-target-source-no-active vV (ƛ⊒ƛ p↦qᶜ N⊒N′) =
  no-active-ƛ
value-target-source-no-active () (·⊒· qᶜ L⊒L′ M⊒M′)
value-target-source-no-active (Λ vV) (Λ⊒Λ allᶜ vV₁ V⊒V′) =
  no-active-Λ
value-target-source-no-active (Λ vV) (⊒Λ pᶜ N⊒V′) =
  renameᵗᵐ-reflects-NoActiveTypeApp suc
    (value-target-source-no-active vV N⊒V′)
value-target-source-no-active (vV ⟨ i ⟩) (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s) =
  renameᵗᵐ-reflects-NoActiveTypeApp suc
    (value-target-source-no-active (vV ⟨ sᵢ ⟩) N⊒V′s)
value-target-source-no-active () (α⊒α qᶜ pαᶜ L⊒L′)
value-target-source-no-active () (⊒α pαᶜ L⊒L′)
value-target-source-no-active () (ν⊒ν pᶜ qᶜ N⊒N′)
value-target-source-no-active () (⊒ν pᶜ N⊒N′)
value-target-source-no-active vV (ν⊒ pᶜ N⊒N′) =
  no-active-ν
    (value-target-source-no-active
      (renameᵗᵐ-preserves-Value suc vV)
      N⊒N′)
value-target-source-no-active ($ κ) (κ⊒κ .κ) =
  no-active-$
value-target-source-no-active () (⊕⊒⊕ M⊒M′ N⊒N′)
value-target-source-no-active (vV ⟨ i ⟩)
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  value-target-source-no-active vV M⊒M′
value-target-source-no-active (vV ⟨ i ⟩)
    (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  value-target-source-no-active vV M⊒M′
value-target-source-no-active vV (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  no-active-⟨⟩ (value-target-source-no-active vV M⊒M′)
value-target-source-no-active vV (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  no-active-⟨⟩ (value-target-source-no-active vV M⊒M′)

renameᵗᵐ-preserves-CatchupSafe :
  ∀ ρ {M} →
  CatchupSafe M →
  CatchupSafe (renameᵗᵐ ρ M)
renameᵗᵐ-preserves-CatchupSafe ρ (safe-value vV) =
  safe-value (renameᵗᵐ-preserves-Value ρ vV)
renameᵗᵐ-preserves-CatchupSafe ρ (safe-ν safeL) =
  safe-ν (renameᵗᵐ-preserves-CatchupSafe ρ safeL)
renameᵗᵐ-preserves-CatchupSafe ρ (safe-cast safeM) =
  safe-cast (renameᵗᵐ-preserves-CatchupSafe ρ safeM)

renameᵗᵐ-reflects-CatchupSafe :
  ∀ ρ {M} →
  CatchupSafe (renameᵗᵐ ρ M) →
  CatchupSafe M
renameᵗᵐ-reflects-CatchupSafe ρ {M = ` x} (safe-value ())
renameᵗᵐ-reflects-CatchupSafe ρ {M = ƛ M} safeM =
  safe-value (ƛ M)
renameᵗᵐ-reflects-CatchupSafe ρ {M = L · M} (safe-value ())
renameᵗᵐ-reflects-CatchupSafe ρ {M = Λ M} (safe-value (Λ vM)) =
  safe-value (Λ (renameᵗᵐ-reflects-Value (extᵗ ρ) vM))
renameᵗᵐ-reflects-CatchupSafe ρ {M = M •} (safe-value ())
renameᵗᵐ-reflects-CatchupSafe ρ {M = ν A L c} (safe-value ())
renameᵗᵐ-reflects-CatchupSafe ρ {M = ν A L c} (safe-ν safeL) =
  safe-ν (renameᵗᵐ-reflects-CatchupSafe ρ safeL)
renameᵗᵐ-reflects-CatchupSafe ρ {M = $ κ} safeM =
  safe-value ($ κ)
renameᵗᵐ-reflects-CatchupSafe ρ {M = L ⊕[ op ] M} (safe-value ())
renameᵗᵐ-reflects-CatchupSafe ρ {M = M ⟨ c ⟩} (safe-value vM) =
  safe-value (renameᵗᵐ-reflects-Value ρ vM)
renameᵗᵐ-reflects-CatchupSafe ρ {M = M ⟨ c ⟩} (safe-cast safeM) =
  safe-cast (renameᵗᵐ-reflects-CatchupSafe ρ safeM)
renameᵗᵐ-reflects-CatchupSafe ρ {M = blame} (safe-value ())

open-preserves-CatchupSafe :
  ∀ {M α β} →
  CatchupSafe (M [ α ]ᵀ) →
  CatchupSafe (M [ β ]ᵀ)
open-preserves-CatchupSafe {M = M} {α = α} {β = β} safeM =
  renameᵗᵐ-preserves-CatchupSafe (singleRenameᵗ β)
    (renameᵗᵐ-reflects-CatchupSafe (singleRenameᵗ α) safeM)

value-target-source-safe :
  ∀ {Δ σ γ M V p} →
  Value V →
  Δ ∣ σ ∣ γ ⊢ M ⊒ V ∶ p →
  CatchupSafe M
value-target-source-safe vV (extend qᶜ pαᶜ M⊒V) =
  value-target-source-safe vV M⊒V
value-target-source-safe vV
    (split {N = N} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ M⊒V) =
  open-preserves-CatchupSafe {M = N} {α = α} {β = αᵢ}
    (value-target-source-safe vV M⊒V)
value-target-source-safe () (⊒blame pᶜ)
value-target-source-safe () (x⊒x pᶜ x∋p)
value-target-source-safe vV (ƛ⊒ƛ p↦qᶜ N⊒N′) =
  safe-value (ƛ _)
value-target-source-safe () (·⊒· qᶜ L⊒L′ M⊒M′)
value-target-source-safe (Λ vV) (Λ⊒Λ allᶜ vM M⊒V′) =
  safe-value (Λ vM)
value-target-source-safe (Λ vV) (⊒Λ pᶜ N⊒V′) =
  renameᵗᵐ-reflects-CatchupSafe suc
    (value-target-source-safe vV N⊒V′)
value-target-source-safe (vV ⟨ i ⟩) (⊒⟨ν⟩ pᶜ sᵢ N⊒V′s) =
  renameᵗᵐ-reflects-CatchupSafe suc
    (value-target-source-safe (vV ⟨ sᵢ ⟩) N⊒V′s)
value-target-source-safe () (α⊒α qᶜ pαᶜ L⊒L′)
value-target-source-safe () (⊒α pαᶜ L⊒L′)
value-target-source-safe () (ν⊒ν pᶜ qᶜ N⊒N′)
value-target-source-safe () (⊒ν pᶜ N⊒N′)
value-target-source-safe vV (ν⊒ pᶜ N⊒N′) =
  safe-ν
    (value-target-source-safe
      (renameᵗᵐ-preserves-Value suc vV)
      N⊒N′)
value-target-source-safe ($ κ) (κ⊒κ .κ) =
  safe-value ($ κ)
value-target-source-safe () (⊕⊒⊕ M⊒M′ N⊒N′)
value-target-source-safe (vV ⟨ i ⟩)
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  value-target-source-safe vV M⊒M′
value-target-source-safe (vV ⟨ i ⟩)
    (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  value-target-source-safe vV M⊒M′
value-target-source-safe vV (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  safe-cast (value-target-source-safe vV M⊒M′)
value-target-source-safe vV (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  safe-cast (value-target-source-safe vV M⊒M′)

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

data ShiftedSourceRemainder :
  ∀ {Δ σ γ N V p} →
  Value V →
  Δ ∣ σ ∣ γ ⊢ ⇑ᵗᵐ N ⊒ V ∶ p →
  Set₁ where

  remainder-nu :
    ∀ {Δ σ γ A L c V p}
      {vV : Value V}
      {N⊒V : Δ ∣ σ ∣ γ
        ⊢ ⇑ᵗᵐ (ν A L c) ⊒ V ∶ p}
    → NuSourceValueTarget
        (renameᵗᵐ-preserves-NuSource suc nu-source)
        vV
        N⊒V
    → ShiftedSourceRemainder vV N⊒V

  remainder-cast :
    ∀ {Δ σ γ M c V p}
      {vV : Value V}
      {N⊒V : Δ ∣ σ ∣ γ
        ⊢ ⇑ᵗᵐ (M ⟨ c ⟩) ⊒ V ∶ p}
    → CastSourceValueTarget
        (renameᵗᵐ-preserves-CastSource suc cast-source)
        vV
        N⊒V
    → ShiftedSourceRemainder vV N⊒V

shifted-source-remainder :
  ∀ {Δ σ γ V p} N →
  value? N ≡ nothing →
  (vV : Value V) →
  (N⊒V : Δ ∣ σ ∣ γ ⊢ ⇑ᵗᵐ N ⊒ V ∶ p) →
  ShiftedSourceRemainder vV N⊒V
shifted-source-remainder (` x) refl vV N⊒V =
  ⊥-elim (neutral-source-no-value-target neutral-` vV N⊒V)
shifted-source-remainder (ƛ M) () vV N⊒V
shifted-source-remainder (L · M) refl vV N⊒V =
  ⊥-elim (neutral-source-no-value-target neutral-· vV N⊒V)
shifted-source-remainder (Λ M) eq vV N⊒V
    with value? M in valueM≡
shifted-source-remainder (Λ M) () vV N⊒V | just vM
shifted-source-remainder (Λ M) refl vV N⊒V | nothing =
  ⊥-elim
    (value?-none-no-value valueM≡
      (renameᵗᵐ-reflects-Value (extᵗ suc)
        (lambda-source-value-target-source-value vV N⊒V)))
shifted-source-remainder (M •) refl vV N⊒V =
  ⊥-elim (type-app-source-no-value-target vV N⊒V)
shifted-source-remainder (ν A L c) refl vV N⊒V =
  remainder-nu
    (nu-source-value-target-inversion
      (renameᵗᵐ-preserves-NuSource suc nu-source)
      vV
      N⊒V)
shifted-source-remainder ($ κ) () vV N⊒V
shifted-source-remainder (L ⊕[ op ] M) refl vV N⊒V =
  ⊥-elim (neutral-source-no-value-target neutral-⊕ vV N⊒V)
shifted-source-remainder (M ⟨ c ⟩) eq vV N⊒V
    with value? M | inert? c
shifted-source-remainder (M ⟨ c ⟩) () vV N⊒V
    | just vM | just i
shifted-source-remainder (M ⟨ c ⟩) refl vV N⊒V
    | just vM | nothing =
  remainder-cast
    (cast-source-value-target-inversion
      (renameᵗᵐ-preserves-CastSource suc cast-source)
      vV
      N⊒V)
shifted-source-remainder (M ⟨ c ⟩) refl vV N⊒V
    | nothing | inert =
  remainder-cast
    (cast-source-value-target-inversion
      (renameᵗᵐ-preserves-CastSource suc cast-source)
      vV
      N⊒V)
shifted-source-remainder blame refl vV N⊒V =
  ⊥-elim (neutral-source-no-value-target neutral-blame vV N⊒V)
