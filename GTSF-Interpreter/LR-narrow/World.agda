module LR-narrow.World where

-- File Charter:
--   * Defines Kripke worlds with imprecise-left/precise-right seal atoms.
--   * Interprets static type contexts and imprecision assumptions using
--     concrete runtime type-name environments.
--   * Defines paired and precise-right binder extensions for `∀ⁱ` and `ν`.
--   * Does not depend on the retired interpreter simulation hierarchy.

open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  )
open import Interpreter using
  ( SealName
  ; TypeEnvironment
  ; lookup
  ; seal-name
  )
import Interpreter as I
open import LR-narrow.Atoms
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
open import Typing.InterpreterSemanticTypingCore using
  ( AllocationRepresentation
  ; SemanticType
  ; TypeEnvironmentLength
  ; ValueTyping
  ; WorldExtension
  ; WorldTyping
  ; dynamic-type
  ; world-extension-allocate
  ; world-extension-refl
  )
open import Types using (TyCtx)

data SealBinding : Set₁ where
  paired-seal :
    SealName → SealName →
    SemanticType → SemanticType →
    (R : StepIndexedRelation) → DownwardClosed R →
    SealBinding

  right-dynamic-seal :
    SealName → SemanticType →
    (R : StepIndexedRelation) → DownwardClosed R →
    SealBinding

infix 4 _∋_↔_∶_

data _∋_↔_∶_ : List SealBinding
  → SealName → SealName → StepIndexedRelation → Set₁ where
  paired-here : ∀ {αᴵ αᴾ Aᴵ Aᴾ entries}
      {R : StepIndexedRelation} {down : DownwardClosed R}
    → (paired-seal αᴵ αᴾ Aᴵ Aᴾ R down ∷ entries)
        ∋ αᴵ ↔ αᴾ ∶ R

  paired-there : ∀ {entry entries α α′ R}
    → entries ∋ α ↔ α′ ∶ R
    → (entry ∷ entries) ∋ α ↔ α′ ∶ R

PairedLeftFresh : SealName → List SealBinding → Set₁
PairedLeftFresh α entries =
  ∀ {α′ R} → entries ∋ α ↔ α′ ∶ R → ⊥

PairedRightFresh : SealName → List SealBinding → Set₁
PairedRightFresh α′ entries =
  ∀ {α R} → entries ∋ α ↔ α′ ∶ R → ⊥

data BindingsUnique : List SealBinding → Set₁ where
  bindings-unique-empty : BindingsUnique []

  bindings-unique-paired : ∀ {α α′ A A′ entries}
      {R : StepIndexedRelation} {down : DownwardClosed R}
    → PairedLeftFresh α entries
    → PairedRightFresh α′ entries
    → BindingsUnique entries
    → BindingsUnique (paired-seal α α′ A A′ R down ∷ entries)

  bindings-unique-right-dynamic : ∀ {α A entries}
      {R : StepIndexedRelation} {down : DownwardClosed R}
    → BindingsUnique entries
    → BindingsUnique (right-dynamic-seal α A R down ∷ entries)

infix 4 _∋★↔_∶_

data _∋★↔_∶_ : List SealBinding
  → SealName → StepIndexedRelation → Set₁ where
  right-dynamic-here : ∀ {α A entries}
      {R : StepIndexedRelation} {down : DownwardClosed R}
    → (right-dynamic-seal α A R down ∷ entries) ∋★↔ α ∶ R

  right-dynamic-there : ∀ {entry entries α R}
    → entries ∋★↔ α ∶ R
    → (entry ∷ entries) ∋★↔ α ∶ R

data BindingsValid
    (Wᴵ Wᴾ : I.World) : List SealBinding → Set₁ where
  []-valid : BindingsValid Wᴵ Wᴾ []

  paired-valid : ∀ {αᴵ αᴾ Aᴵ Aᴾ entries}
      {R : StepIndexedRelation} {down : DownwardClosed R}
    → AllocationRepresentation Wᴵ αᴵ Aᴵ
    → AllocationRepresentation Wᴾ αᴾ Aᴾ
    → (∀ {n Vᴵ Vᴾ}
        → R n Vᴵ Vᴾ
        → ValueTyping Wᴵ Vᴵ Aᴵ × ValueTyping Wᴾ Vᴾ Aᴾ)
    → BindingsValid Wᴵ Wᴾ entries
    → BindingsValid Wᴵ Wᴾ
        (paired-seal αᴵ αᴾ Aᴵ Aᴾ R down ∷ entries)

  right-dynamic-valid : ∀ {α A entries}
      {R : StepIndexedRelation} {down : DownwardClosed R}
    → AllocationRepresentation Wᴾ α A
    → (∀ {n Vᴵ Vᴾ}
        → R n Vᴵ Vᴾ
        → ValueTyping Wᴵ Vᴵ dynamic-type × ValueTyping Wᴾ Vᴾ A)
    → BindingsValid Wᴵ Wᴾ entries
    → BindingsValid Wᴵ Wᴾ
        (right-dynamic-seal α A R down ∷ entries)

record World : Set₁ where
  constructor world
  field
    left-world : I.World
    right-world : I.World
    left-world-typed : WorldTyping left-world
    right-world-typed : WorldTyping right-world
    bindings : List SealBinding
    bindings-valid : BindingsValid left-world right-world bindings
    bindings-unique : BindingsUnique bindings

open World public

infix 4 _⊆ᵇ_

data _⊆ᵇ_ : List SealBinding → List SealBinding → Set₁ where
  bindings-empty : ∀ {future}
    → [] ⊆ᵇ future

  bindings-keep : ∀ {entry current future}
    → current ⊆ᵇ future
    → (entry ∷ current) ⊆ᵇ (entry ∷ future)

  bindings-drop : ∀ {entry current future}
    → current ⊆ᵇ future
    → current ⊆ᵇ (entry ∷ future)

bindings-⊆-refl : ∀ {entries} → entries ⊆ᵇ entries
bindings-⊆-refl {entries = []} = bindings-empty
bindings-⊆-refl {entries = entry ∷ entries} =
  bindings-keep bindings-⊆-refl

bindings-⊆-trans : ∀ {xs ys zs}
  → xs ⊆ᵇ ys
  → ys ⊆ᵇ zs
  → xs ⊆ᵇ zs
bindings-⊆-trans bindings-empty ys⊆zs = bindings-empty
bindings-⊆-trans (bindings-keep xs⊆ys) (bindings-keep ys⊆zs) =
  bindings-keep (bindings-⊆-trans xs⊆ys ys⊆zs)
bindings-⊆-trans (bindings-keep xs⊆ys) (bindings-drop ys⊆zs) =
  bindings-drop (bindings-⊆-trans (bindings-keep xs⊆ys) ys⊆zs)
bindings-⊆-trans (bindings-drop xs⊆ys) (bindings-keep ys⊆zs) =
  bindings-drop (bindings-⊆-trans xs⊆ys ys⊆zs)
bindings-⊆-trans (bindings-drop xs⊆ys) (bindings-drop ys⊆zs) =
  bindings-drop (bindings-⊆-trans (bindings-drop xs⊆ys) ys⊆zs)

paired-binding-weaken : ∀ {current future α α′ R}
  → current ⊆ᵇ future
  → current ∋ α ↔ α′ ∶ R
  → future ∋ α ↔ α′ ∶ R
paired-binding-weaken bindings-empty ()
paired-binding-weaken (bindings-keep current⊆future) paired-here =
  paired-here
paired-binding-weaken (bindings-keep current⊆future)
    (paired-there binding) =
  paired-there (paired-binding-weaken current⊆future binding)
paired-binding-weaken (bindings-drop current⊆future) binding =
  paired-there (paired-binding-weaken current⊆future binding)

infix 4 _⊒_

record _⊒_ (future current : World) : Set₁ where
  constructor future-world
  field
    left-future :
      WorldExtension (left-world current) (left-world future)
    right-future :
      WorldExtension (right-world current) (right-world future)
    bindings-future : bindings current ⊆ᵇ bindings future

open _⊒_ public

world-⊒-refl : ∀ {w} → w ⊒ w
world-⊒-refl =
  future-world world-extension-refl world-extension-refl bindings-⊆-refl

unary-extension-trans : ∀ {W U T}
  → WorldExtension W U
  → WorldExtension U T
  → WorldExtension W T
unary-extension-trans W≤U world-extension-refl = W≤U
unary-extension-trans W≤U (world-extension-allocate U≤T) =
  world-extension-allocate (unary-extension-trans W≤U U≤T)

world-⊒-trans : ∀ {w₁ w₂ w₃}
  → w₃ ⊒ w₂
  → w₂ ⊒ w₁
  → w₃ ⊒ w₁
world-⊒-trans w₃⊒w₂ w₂⊒w₁ =
  future-world
    (unary-extension-trans
      (left-future w₂⊒w₁) (left-future w₃⊒w₂))
    (unary-extension-trans
      (right-future w₂⊒w₁) (right-future w₃⊒w₂))
    (bindings-⊆-trans
      (bindings-future w₂⊒w₁) (bindings-future w₃⊒w₂))

data AssumptionsValid
    (w : World) (θᴵ θᴾ : TypeEnvironment) :
    (Φ : ImpCtx) → AtomEnvironment Φ → Set₁ where
  []-valid : AssumptionsValid w θᴵ θᴾ [] []ᵃ

  paired-valid : ∀ {X Y Φ α α′}
      {a : Atom (X ˣ⊑ˣ Y)} {ρ : AtomEnvironment Φ}
    → lookup θᴾ X ≡ just (seal-name α′)
    → lookup θᴵ Y ≡ just (seal-name α)
    → bindings w ∋ α ↔ α′ ∶ relation a
    → AssumptionsValid w θᴵ θᴾ Φ ρ
    → AssumptionsValid w θᴵ θᴾ ((X ˣ⊑ˣ Y) ∷ Φ) (a ∷ᵃ ρ)

  right-dynamic-assumption-valid : ∀ {X Φ α}
      {a : Atom (X ˣ⊑★)} {ρ : AtomEnvironment Φ}
    → lookup θᴾ X ≡ just (seal-name α)
    → bindings w ∋★↔ α ∶ relation a
    → AssumptionsValid w θᴵ θᴾ Φ ρ
    → AssumptionsValid w θᴵ θᴾ ((X ˣ⊑★) ∷ Φ) (a ∷ᵃ ρ)

record Interpretation
    {Φ : ImpCtx} {Δᴾ Δᴵ : TyCtx}
    (w : World) : Set₁ where
  constructor interpretation
  field
    left-types : TypeEnvironment
    right-types : TypeEnvironment
    left-length : TypeEnvironmentLength Δᴵ left-types
    right-length : TypeEnvironmentLength Δᴾ right-types
    left-scoped : TypeEnvironmentScoped (left-world w) left-types
    right-scoped : TypeEnvironmentScoped (right-world w) right-types
    atoms : AtomEnvironment Φ
    assumptions-valid :
      AssumptionsValid w left-types right-types Φ atoms

open Interpretation public

infix 4 _⊒ⁱ_

record _⊒ⁱ_
    {Φ : ImpCtx} {Δᴾ Δᴵ : TyCtx}
    {future current : World}
    (futureᵢ : Interpretation {Φ} {Δᴾ} {Δᴵ} future)
    (currentᵢ : Interpretation {Φ} {Δᴾ} {Δᴵ} current) : Set₁ where
  constructor future-interpretation
  field
    world-future : future ⊒ current
    left-types-preserved : left-types futureᵢ ≡ left-types currentᵢ
    right-types-preserved : right-types futureᵢ ≡ right-types currentᵢ
    atoms-preserved : atoms futureᵢ ≡ atoms currentᵢ

open _⊒ⁱ_ public

record PairedBinderExtension
    {Φ : ImpCtx} {Δᴾ Δᴵ : TyCtx} {current : World}
    (currentᵢ : Interpretation {Φ} {Δᴾ} {Δᴵ} current) : Set₁ where
  constructor paired-binder-extension
  field
    paired-future : World
    paired-future-world : paired-future ⊒ current
    paired-left-seal : SealName
    paired-right-seal : SealName
    paired-left-fresh :
      PairedLeftFresh paired-left-seal (bindings current)
    paired-right-fresh :
      PairedRightFresh paired-right-seal (bindings current)
    paired-head-atom : Atom (zero ˣ⊑ˣ zero)
    paired-body-interpretation :
      Interpretation
        {(zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ}
        {suc Δᴾ} {suc Δᴵ} paired-future
    paired-left-types :
      left-types paired-body-interpretation ≡
      seal-name paired-left-seal ∷ left-types currentᵢ
    paired-right-types :
      right-types paired-body-interpretation ≡
      seal-name paired-right-seal ∷ right-types currentᵢ
    paired-atoms :
      atoms paired-body-interpretation ≡
      paired-head-atom ∷ᵃ lift-both-atoms (atoms currentᵢ)

open PairedBinderExtension public

record RightBinderExtension
    {Φ : ImpCtx} {Δᴾ Δᴵ : TyCtx} {current : World}
    (currentᵢ : Interpretation {Φ} {Δᴾ} {Δᴵ} current) : Set₁ where
  constructor right-binder-extension
  field
    right-future-world : World
    right-future-extension : right-future-world ⊒ current
    right-binder-seal : SealName
    right-head-atom : Atom (zero ˣ⊑★)
    right-body-interpretation :
      Interpretation
        {(zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ}
        {suc Δᴾ} {Δᴵ} right-future-world
    right-binder-types :
      right-types right-body-interpretation ≡
      seal-name right-binder-seal ∷ right-types currentᵢ
    right-left-types-preserved :
      left-types right-body-interpretation ≡ left-types currentᵢ
    right-binder-atoms :
      atoms right-body-interpretation ≡
      right-head-atom ∷ᵃ lift-right-atoms (atoms currentᵢ)

open RightBinderExtension public
