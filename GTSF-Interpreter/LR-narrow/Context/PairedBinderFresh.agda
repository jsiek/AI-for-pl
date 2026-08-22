module LR-narrow.Context.PairedBinderFresh where

-- File Charter:
--   * Constructs a generative paired binder extension for an arbitrary
--     downward-closed, type-respecting semantic atom.
--   * Allocates one fresh seal in each runtime world and lifts the existing
--     interpretation below the new paired assumption.
--   * Exports exactly the fresh paired-extension constructor.

open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import ImprecisionWf using (_ˣ⊑ˣ_; ⇑ᵢ)
open import Interpreter using
  ( SealName
  ; Value
  ; allocate
  ; freshSealName
  ; seal-name
  )
open import LR-narrow.Atoms
open import LR-narrow.World
import LR-narrow.World as LRW
open import Narrowing.InterpreterWorldNarrowing using
  ( Allocated
  ; TypeEnvironmentScoped
  ; allocated
  ; seal-scoped
  ; _∷-scoped_
  )
open import Typing.InterpreterSemanticTyping using
  ( AllocationRepresentation
  ; ValueTyping
  ; WorldExtension
  ; WorldTyping
  ; allocation-preserves-world-typing
  ; allocation-representation
  ; allocation-representation-world-weaken
  ; fresh-seal-is-allocated
  ; fresh-seal-is-unallocated
  ; length-cons
  ; runtime-context
  ; semantic-value-world-weaken
  ; store-empty
  ; type-environment-scope-world-weaken
  ; world-extension-allocate
  ; world-extension-refl
  ; ⟦_⟧[_]
  )
open import Types using (Ty; TyCtx; WfTy)

private
  bindings-valid-weaken : ∀ {Wᴵ Wᴾ Uᴵ Uᴾ entries}
    → (Wᴵ≤Uᴵ : WorldExtension Wᴵ Uᴵ)
    → WorldTyping Uᴵ
    → (Wᴾ≤Uᴾ : WorldExtension Wᴾ Uᴾ)
    → WorldTyping Uᴾ
    → BindingsValid Wᴵ Wᴾ entries
    → BindingsValid Uᴵ Uᴾ entries
  bindings-valid-weaken Wᴵ≤Uᴵ Uᴵ⊢ Wᴾ≤Uᴾ Uᴾ⊢ LRW.[]-valid =
    LRW.[]-valid
  bindings-valid-weaken Wᴵ≤Uᴵ Uᴵ⊢ Wᴾ≤Uᴾ Uᴾ⊢
      (LRW.paired-valid left-rep right-rep values-valid rest-valid) =
    LRW.paired-valid
      (allocation-representation-world-weaken Wᴵ≤Uᴵ left-rep)
      (allocation-representation-world-weaken Wᴾ≤Uᴾ right-rep)
      (λ related →
        semantic-value-world-weaken Wᴵ≤Uᴵ Uᴵ⊢
          (proj₁ (values-valid related)) ,
        semantic-value-world-weaken Wᴾ≤Uᴾ Uᴾ⊢
          (proj₂ (values-valid related)))
      (bindings-valid-weaken Wᴵ≤Uᴵ Uᴵ⊢ Wᴾ≤Uᴾ Uᴾ⊢ rest-valid)
  bindings-valid-weaken Wᴵ≤Uᴵ Uᴵ⊢ Wᴾ≤Uᴾ Uᴾ⊢
      (LRW.right-dynamic-valid right-rep values-valid rest-valid) =
    LRW.right-dynamic-valid
      (allocation-representation-world-weaken Wᴾ≤Uᴾ right-rep)
      (λ related →
        semantic-value-world-weaken Wᴵ≤Uᴵ Uᴵ⊢
          (proj₁ (values-valid related)) ,
        semantic-value-world-weaken Wᴾ≤Uᴾ Uᴾ⊢
          (proj₂ (values-valid related)))
      (bindings-valid-weaken Wᴵ≤Uᴵ Uᴵ⊢ Wᴾ≤Uᴾ Uᴾ⊢ rest-valid)

  paired-binding-left-allocated : ∀ {Wᴵ Wᴾ entries αᴵ αᴾ R}
    → BindingsValid Wᴵ Wᴾ entries
    → entries ∋ αᴵ ↔ αᴾ ∶ R
    → Allocated Wᴵ αᴵ
  paired-binding-left-allocated
      (LRW.paired-valid
        (allocation-representation A θ present eq) right-rep
        values-valid rest-valid)
      paired-here =
    allocated present
  paired-binding-left-allocated
      (LRW.paired-valid left-rep right-rep values-valid rest-valid)
      (paired-there binding) =
    paired-binding-left-allocated rest-valid binding
  paired-binding-left-allocated
      (LRW.right-dynamic-valid right-rep values-valid rest-valid)
      (paired-there binding) =
    paired-binding-left-allocated rest-valid binding

  paired-binding-right-allocated : ∀ {Wᴵ Wᴾ entries αᴵ αᴾ R}
    → BindingsValid Wᴵ Wᴾ entries
    → entries ∋ αᴵ ↔ αᴾ ∶ R
    → Allocated Wᴾ αᴾ
  paired-binding-right-allocated
      (LRW.paired-valid left-rep
        (allocation-representation A θ present eq)
        values-valid rest-valid)
      paired-here =
    allocated present
  paired-binding-right-allocated
      (LRW.paired-valid left-rep right-rep values-valid rest-valid)
      (paired-there binding) =
    paired-binding-right-allocated rest-valid binding
  paired-binding-right-allocated
      (LRW.right-dynamic-valid right-rep values-valid rest-valid)
      (paired-there binding) =
    paired-binding-right-allocated rest-valid binding

  lift-assumptions-paired : ∀
      {current future θᴵ θᴾ Xᴵ Xᴾ Φ ρ}
    → (∀ {αᴵ αᴾ R}
        → bindings current ∋ αᴵ ↔ αᴾ ∶ R
        → bindings future ∋ αᴵ ↔ αᴾ ∶ R)
    → (∀ {α R}
        → bindings current ∋★↔ α ∶ R
        → bindings future ∋★↔ α ∶ R)
    → AssumptionsValid current θᴵ θᴾ Φ ρ
    → AssumptionsValid future (Xᴵ ∷ θᴵ) (Xᴾ ∷ θᴾ)
        (⇑ᵢ Φ) (lift-both-atoms ρ)
  lift-assumptions-paired paired-weaken dynamic-weaken LRW.[]-valid =
    LRW.[]-valid
  lift-assumptions-paired paired-weaken dynamic-weaken
      (LRW.paired-valid right-name left-name binding rest-valid) =
    LRW.paired-valid right-name left-name (paired-weaken binding)
      (lift-assumptions-paired paired-weaken dynamic-weaken rest-valid)
  lift-assumptions-paired paired-weaken dynamic-weaken
      (LRW.right-dynamic-assumption-valid
        right-name binding rest-valid) =
    LRW.right-dynamic-assumption-valid right-name
      (dynamic-weaken binding)
      (lift-assumptions-paired paired-weaken dynamic-weaken rest-valid)

fresh-paired-binder-extension : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {current : World}
    (I : Interpretation {Φ} {Δᴾ} {Δᴵ} current)
    (Aᴵ Aᴾ : Ty)
  → WfTy Δᴵ Aᴵ
  → WfTy Δᴾ Aᴾ
  → (a : Atom (zero ˣ⊑ˣ zero))
  → (∀ {n Vᴵ Vᴾ}
      → relation a n Vᴵ Vᴾ
      → ValueTyping
          (allocate (left-world current) Aᴵ (left-types I)) Vᴵ
          ⟦ Aᴵ ⟧[ left-types I ]
        × ValueTyping
          (allocate (right-world current) Aᴾ (right-types I)) Vᴾ
          ⟦ Aᴾ ⟧[ right-types I ])
  → PairedBinderExtension I
fresh-paired-binder-extension {Φ} {Δᴾ} {Δᴵ} {current}
    I Aᴵ Aᴾ hAᴵ hAᴾ a relation-typed =
  paired-binder-extension
    future growth left-seal right-seal left-fresh right-fresh a
    body-interpretation refl refl refl
  where
  left-extension : WorldExtension (left-world current)
    (allocate (left-world current) Aᴵ (left-types I))
  left-extension = world-extension-allocate world-extension-refl

  right-extension : WorldExtension (right-world current)
    (allocate (right-world current) Aᴾ (right-types I))
  right-extension = world-extension-allocate world-extension-refl

  left-future-typed :
    WorldTyping
      (allocate (left-world current) Aᴵ (left-types I))
  left-future-typed =
    allocation-preserves-world-typing (left-world-typed current)
      (runtime-context (left-length I) (left-scoped I) store-empty) hAᴵ

  right-future-typed :
    WorldTyping
      (allocate (right-world current) Aᴾ (right-types I))
  right-future-typed =
    allocation-preserves-world-typing (right-world-typed current)
      (runtime-context (right-length I) (right-scoped I) store-empty) hAᴾ

  left-seal : SealName
  left-seal = freshSealName (left-world current)

  right-seal : SealName
  right-seal = freshSealName (right-world current)

  left-fresh : PairedLeftFresh left-seal (bindings current)
  left-fresh binding =
    fresh-seal-is-unallocated (left-world-typed current)
      (paired-binding-left-allocated (bindings-valid current) binding)

  right-fresh : PairedRightFresh right-seal (bindings current)
  right-fresh binding =
    fresh-seal-is-unallocated (right-world-typed current)
      (paired-binding-right-allocated (bindings-valid current) binding)

  old-bindings-valid :
    BindingsValid
      (allocate (left-world current) Aᴵ (left-types I))
      (allocate (right-world current) Aᴾ (right-types I))
      (bindings current)
  old-bindings-valid =
    bindings-valid-weaken left-extension left-future-typed
      right-extension right-future-typed (bindings-valid current)

  future : World
  future =
    world
      (allocate (left-world current) Aᴵ (left-types I))
      (allocate (right-world current) Aᴾ (right-types I))
      left-future-typed right-future-typed
      (paired-seal left-seal right-seal
        ⟦ Aᴵ ⟧[ left-types I ] ⟦ Aᴾ ⟧[ right-types I ]
        (relation a) (relation-downward a) ∷ bindings current)
      (LRW.paired-valid
        (allocation-representation Aᴵ (left-types I)
          (here refl) refl)
        (allocation-representation Aᴾ (right-types I)
          (here refl) refl)
        relation-typed old-bindings-valid)
      (bindings-unique-paired left-fresh right-fresh
        (bindings-unique current))

  growth : future ⊒ current
  growth =
    future-world left-extension right-extension
      (bindings-drop bindings-⊆-refl)

  body-interpretation :
    Interpretation
      {(zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ}
      {suc Δᴾ} {suc Δᴵ} future
  body-interpretation =
    interpretation
      (seal-name left-seal ∷ left-types I)
      (seal-name right-seal ∷ right-types I)
      (length-cons (left-length I))
      (length-cons (right-length I))
      (seal-scoped fresh-seal-is-allocated ∷-scoped
        type-environment-scope-world-weaken left-extension (left-scoped I))
      (seal-scoped fresh-seal-is-allocated ∷-scoped
        type-environment-scope-world-weaken right-extension (right-scoped I))
      (a ∷ᵃ lift-both-atoms (atoms I))
      (LRW.paired-valid refl refl paired-here
        (lift-assumptions-paired paired-there right-dynamic-there
          (assumptions-valid I)))
