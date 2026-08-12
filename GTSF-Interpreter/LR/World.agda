module LR.World where

-- File Charter:
--   * Defines proof-relevant Kripke worlds for the interpreter logical
--     relation.
--   * A world pairs two typed allocation worlds with persistent atomic
--     relations assigned to linked nominal seals.
--   * Defines reflexive and transitive future-world extension without an
--     interpreter execution or small-step reduction dependency.

open import Data.List using (List; []; _∷_)

open import Interpreter using (SealName)
import Interpreter as I
open import LR.Atoms
open import Typing.InterpreterSemanticTypingCore using
  ( AllocationRepresentation
  ; WorldExtension
  ; WorldTyping
  ; world-extension-allocate
  ; world-extension-refl
  )

record SealAtom : Set₁ where
  constructor seal-atom
  field
    left-name : SealName
    right-name : SealName
    semantic-atom : Atom

open SealAtom public

data AtomsValid (W W′ : I.World) : List SealAtom → Set₁ where
  []-valid :
    AtomsValid W W′ []

  _∷-valid_ : ∀ {e es}
    → AllocationRepresentation W
        (left-name e) (left-type (semantic-atom e))
    → AllocationRepresentation W′
        (right-name e) (right-type (semantic-atom e))
    → AtomsValid W W′ es
    → AtomsValid W W′ (e ∷ es)

record World : Set₁ where
  constructor world
  field
    left-world : I.World
    right-world : I.World
    left-world-typed : WorldTyping left-world
    right-world-typed : WorldTyping right-world
    atoms : List SealAtom
    atoms-valid : AtomsValid left-world right-world atoms

open World public

infix 4 _⊆ᵃ_

data _⊆ᵃ_ : List SealAtom → List SealAtom → Set₁ where
  atoms-empty : ∀ {es}
    → [] ⊆ᵃ es

  atoms-keep : ∀ {e es fs}
    → es ⊆ᵃ fs
    → (e ∷ es) ⊆ᵃ (e ∷ fs)

  atoms-drop : ∀ {e es fs}
    → es ⊆ᵃ fs
    → es ⊆ᵃ (e ∷ fs)

atoms-⊆-refl : ∀ {es} → es ⊆ᵃ es
atoms-⊆-refl {es = []} = atoms-empty
atoms-⊆-refl {es = e ∷ es} = atoms-keep atoms-⊆-refl

atoms-⊆-trans : ∀ {es fs gs}
  → es ⊆ᵃ fs
  → fs ⊆ᵃ gs
  → es ⊆ᵃ gs
atoms-⊆-trans atoms-empty fs⊆gs = atoms-empty
atoms-⊆-trans (atoms-keep es⊆fs) (atoms-keep fs⊆gs) =
  atoms-keep (atoms-⊆-trans es⊆fs fs⊆gs)
atoms-⊆-trans (atoms-keep es⊆fs) (atoms-drop fs⊆gs) =
  atoms-drop (atoms-⊆-trans (atoms-keep es⊆fs) fs⊆gs)
atoms-⊆-trans (atoms-drop es⊆fs) (atoms-keep fs⊆gs) =
  atoms-drop (atoms-⊆-trans es⊆fs fs⊆gs)
atoms-⊆-trans (atoms-drop es⊆fs) (atoms-drop fs⊆gs) =
  atoms-drop (atoms-⊆-trans (atoms-drop es⊆fs) fs⊆gs)

infix 4 _⊋_

record _⊋_ (future current : World) : Set₁ where
  constructor future-world
  field
    left-future :
      WorldExtension (left-world current) (left-world future)
    right-future :
      WorldExtension (right-world current) (right-world future)
    atoms-future : atoms current ⊆ᵃ atoms future

open _⊋_ public

world-⊋-refl : ∀ {w} → w ⊋ w
world-⊋-refl =
  future-world world-extension-refl world-extension-refl atoms-⊆-refl

unary-extension-trans : ∀ {W U T}
  → WorldExtension W U
  → WorldExtension U T
  → WorldExtension W T
unary-extension-trans W≤U world-extension-refl = W≤U
unary-extension-trans W≤U (world-extension-allocate U≤T) =
  world-extension-allocate (unary-extension-trans W≤U U≤T)

world-⊋-trans : ∀ {w₁ w₂ w₃}
  → w₃ ⊋ w₂
  → w₂ ⊋ w₁
  → w₃ ⊋ w₁
world-⊋-trans w₃⊋w₂ w₂⊋w₁ =
  future-world
    (unary-extension-trans
      (left-future w₂⊋w₁) (left-future w₃⊋w₂))
    (unary-extension-trans
      (right-future w₂⊋w₁) (right-future w₃⊋w₂))
    (atoms-⊆-trans (atoms-future w₂⊋w₁) (atoms-future w₃⊋w₂))

infix 4 _∋_↔_∶_

data _∋_↔_∶_ : List SealAtom
  → SealName → SealName → Atom → Set₁ where
  seal-atom-here : ∀ {e es}
    → (e ∷ es) ∋ left-name e ↔ right-name e ∶ semantic-atom e

  seal-atom-there : ∀ {e es α α′ a}
    → es ∋ α ↔ α′ ∶ a
    → (e ∷ es) ∋ α ↔ α′ ∶ a
