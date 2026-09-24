# One representation, two ordinary spellings: a worked `boundary`

This is a machine-derived instance of `Terms.agda` §4's `boundary` rule and of
`notes/notes.md`'s “One representation, two ordinary spellings.”  Every
state number, numeral, de Bruijn index, context, type, representation, and
named rendering below was normalized by a temporary Agda probe.  None of the
scope bookkeeping was done by hand.

## 1. A reached boundary

The example is `Examples.agda` §5a's closed program, rendered with names:

    E₀ᴮ = ((((ΛX. (λx:(∀Y. (Y⇒Y)). (ΛY. (λy:ℕ. x [Y])))) [ℕ] · (ΛZ. (λx:Z. x))) [𝔹] · 0) · true)

Its raw de Bruijn term is:

    (((((Λ (ƛ (`∀ (` 0 ⇒ ` 0)) ∙
               Λ (ƛ `ℕ ∙ ((` 1) ·[ ` 0 ⇒ ` 0 , ` 0 ]))))
         ·[ (`∀ (` 0 ⇒ ` 0)) ⇒ `∀ (`ℕ ⇒ (` 0 ⇒ ` 0)) , `ℕ ])
        · Λ (ƛ ` 0 ∙ ` 0))
       ·[ `ℕ ⇒ (` 0 ⇒ ` 0) , `𝔹 ])
      · $ 0) · `true

The evaluator's transition from state `7` to state `8` creates the boundary
used below.  These are whole terms; reduction is vertical.

    Ξ = [α := 𝔹 , β := ℕ]
    (((((ΛZ. (λx:Z. x)) ⟪ ↓Y , (∀Y. (id Y ↦ id Y)) ⟫) ⟪ ↓X , (∀Z. (id Z ↦ id Z)) ⟫) [X] ⟪ ↥X , ↥Y , (seal X ↦ unseal X) ⟫) · true)
    │
    │ TyPeelR-⟪⟫
    ▼
    Ξ = [α := β , β := 𝔹 , γ := ℕ]
    (((((ΛX′. (λx:X′. x)) ⟪ ↓X , ↓Z , (∀Z. (id Z ↦ id Z)) ⟫) [X] ⟪ ↥X , ↓Y , (seal X ↦ unseal X) ⟫) ⟪ ↥Y , ↥Z , (seal Y ↦ unseal Y) ⟫) · true)

The same transition in raw Agda syntax is:

    (((((Λ (ƛ ` 0 ∙ ` 0))
          ⟪ unbind 0 1 ∷ [] , `∀ (id (` 0) ↦ id (` 0)) ⟫)
         ⟪ unbind 0 0 ∷ [] , `∀ (id (` 0) ↦ id (` 0)) ⟫)
        ·[ (` 0) ⇒ (` 0) , ` 0 ])
       ⟪ bind 1 1 ∷ bind 0 0 ∷ [] , seal 0 ↦ unseal 0 ⟫)
      · `true)
    │
    │ TyPeelR-⟪⟫
    ▼
    (((((Λ (ƛ ` 0 ∙ ` 0))
          ⟪ unbind 0 2 ∷ unbind 0 0 ∷ [] ,
             `∀ (id (` 0) ↦ id (` 0)) ⟫)
         ·[ (` 0) ⇒ (` 0) , ` 0 ])
        ⟪ unbind 1 1 ∷ bind 0 0 ∷ [] , seal 0 ↦ unseal 0 ⟫)
       ⟪ bind 1 2 ∷ bind 0 1 ∷ [] , seal 0 ↦ unseal 0 ⟫)
      · `true)

## 2. The boundary and its three name maps

The probe descended through the function frame and the enclosing boundary's
interior reading (`root.fun.body`).  The focused boundary is:

    (((ΛX′. (λx:X′. x)) ⟪ ↓X , ↓Z , (∀Z. (id Z ↦ id Z)) ⟫) [X]
      ⟪ ↥X , ↓Y , (seal X ↦ unseal X) ⟫)

In raw syntax its body, scope, and conversion are:

    M = ((Λ (ƛ ` 0 ∙ ` 0))
          ⟪ unbind 0 2 ∷ unbind 0 0 ∷ [] ,
             `∀ (id (` 0) ↦ id (` 0)) ⟫)
         ·[ (` 0) ⇒ (` 0) , ` 0 ]

    Θ = unbind 1 1 ∷ bind 0 0 ∷ []
    c = seal 0 ↦ unseal 0

The list is head-last, so `Θ` acts as `↥X` and then `↓Y`.  All three
contexts have the one store

    reps = bindR (` 0) ∷ bindR `𝔹 ∷ bindR `ℕ ∷ []
    Ξ    = [α := β , β := 𝔹 , γ := ℕ]

Only their name maps differ:

| reading | raw `names` | rendered name map |
|---|---|---|
| exterior `Δ` | `1 ∷ 2 ∷ []` | `Y↦β , Z↦γ` |
| interior `Δᵢ` | `0 ∷ 2 ∷ []` | `X↦α , Z↦γ` |
| conversion `Δᶜ` | `0 ∷ 1 ∷ 2 ∷ []` | `X↦α , Y↦β , Z↦γ` |

Starting from `[1,2]`, `bind 0 0` inserts `0` at the front, producing
`[0,1,2]`.  The interior reading then performs `unbind 1 1` and deletes the
middle `1`, producing `[0,2]`.  The conversion reading skips that unbind and
therefore remains `[0,1,2]`.

## 3. The actual `boundary` instance

Agda inferred the four ordinary endpoint types as follows:

| metavariable | raw type | named in its own context |
|---|---|---|
| `Bᵢ` in `Δᵢ` | `` ` 0 ⇒ ` 0 `` | `X⇒X` |
| `Cᵢ` in `Δᶜ` | `` ` 0 ⇒ ` 0 `` | `X⇒X` |
| `Cₑ` in `Δᶜ` | `` ` 1 ⇒ ` 1 `` | `Y⇒Y` |
| `Bₑ` in `Δ` | `` ` 0 ⇒ ` 0 `` | `Y⇒Y` |

The six premises of this occurrence of `boundary` are:

1. `BoundaryWf Δ (unbind 1 1 ∷ bind 0 0 ∷ []) Δᵢ Δᶜ`.
2. ``Δᵢ ∣ [] ⊢ M ⦂ (` 0 ⇒ ` 0)``.
3. ``Δᶜ ⊢ seal 0 ↦ unseal 0 ∶ (` 0 ⇒ ` 0) ⇝ (` 1 ⇒ ` 1)``.
4. ``Δᵢ ⊢ (` 0 ⇒ ` 0) ≈ (` 0 ⇒ ` 0) ⊣ Δᶜ``.
5. ``Δ ⊢ (` 0 ⇒ ` 0) ≈ (` 1 ⇒ ` 1) ⊣ Δᶜ``.
6. ``Δ ⊢ᵗ (` 0 ⇒ ` 0)``.

Here are the two `≈` premises with their existential witnesses exposed:

| premise | left ordinary spelling | one representation `R` | right ordinary spelling |
|---|---|---|---|
| interior | `Δᵢ`: raw `` `0⇒`0 `` = `X⇒X` | raw `` `0⇒`0 `` = `α⇒α` | `Δᶜ`: raw `` `0⇒`0 `` = `X⇒X` |
| exterior | `Δ`: raw `` `0⇒`0 `` = `Y⇒Y` | raw `` `1⇒`1 `` = `β⇒β` | `Δᶜ`: raw `` `1⇒`1 `` = `Y⇒Y` |

Thus the named instance reads:

    Δᵢ ∣ [] ⊢ M : X⇒X
    Δᶜ ⊢ seal X ↦ unseal X : (X⇒X) ⇝ (Y⇒Y)
    Δᵢ ⊢ X⇒X ≈ X⇒X ⊣ Δᶜ       through α⇒α
    Δ  ⊢ Y⇒Y ≈ Y⇒Y ⊣ Δᶜ       through β⇒β
    Δ  ⊢ᵗ Y⇒Y
    ──────────────────────────────────────────────
    Δ ∣ [] ⊢ M ⟪ ↥X , ↓Y , seal X ↦ unseal X ⟫ : Y⇒Y

The exterior `Y` is position `0` in `names Δ` but position `1` in
`names Δᶜ`.  The preceding `↥X` inserted `X` in front of it; `↓Y` removes
`Y` only from the interior because the conversion reading skips unbinds.
This is exactly why premise 5 relates raw `` `0⇒`0 `` to raw `` `1⇒`1 ``.

## 4. “In scope in both” is not raw equality

The concrete bad shortcut is to read exterior ``Bₑ = (` 0 ⇒ ` 0)`` directly
in either other map:

    names Δᵢ ⊢ (` 0 ⇒ ` 0) ~ (` 0 ⇒ ` 0) = α⇒α
    names Δᶜ ⊢ (` 0 ⇒ ` 0) ~ (` 0 ⇒ ` 0) = α⇒α

Both judgments are well formed, but both say `X⇒X`, not the required
`Y⇒Y` with representation `β⇒β` (raw `` `1⇒`1 ``).  Requiring the named
`Y` to be in scope in both `Δ` and `Δᶜ` yields the correct raw spellings
`0` and `1`; comparing raw syntax would silently select `X` on the right.

## 5. Contrast: only two maps in the smaller `Q₀` run

The smaller closed program

    Q₀ = ((ΛX. (λx:X. ((ΛY. (λy:ℕ. x)) [ℕ] · 0))) [ℕ] · 7)

has raw term:

    (((Λ (ƛ ` 0 ∙
           (((Λ (ƛ `ℕ ∙ ` 1)) ·[ `ℕ ⇒ ` 1 , `ℕ ]) · $ 0)))
       ·[ ` 0 ⇒ ` 0 , `ℕ ])
      · $ 7)

It reaches at state `1` the boundary

    ((λx:X. ((ΛY. (λy:ℕ. x)) [ℕ] · 0))
      ⟪ ↥X , (seal X ↦ unseal X) ⟫)

Its raw boundary is:

    (ƛ ` 0 ∙ (((Λ (ƛ `ℕ ∙ ` 1)) ·[ `ℕ ⇒ ` 1 , `ℕ ]) · $ 0))
      ⟪ bind 0 0 ∷ [] , seal 0 ↦ unseal 0 ⟫

Its raw maps are `names Δ = []` and
`names Δᵢ = names Δᶜ = 0 ∷ []`.  With no unbind to skip, the interior and
conversion readings coincide.  This is why `Q₀` is useful as a contrast
but not as the main three-map example.
