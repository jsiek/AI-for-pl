
# Narrowing/Widening: endpoints determine coercions

    Φ ∣ Δ ⊢ s ∶ A ⊒ B →
    Φ ∣ Δ ⊢ t ∶ A ⊒ B →
    s ≡ t

# Term narrowing is reflexive

# Reflexive term narrowing is preserved by reduction

# Narrowing/Widening implies Coercion typing

# Define narrowing equality as endpoint equality

p ≈ₙ q

just means p and q have the same endpoints

# Use Agda variables to remove implicit parameters in definitions

Especially term narrowing


# r/p distinction

The narrowing between terms should only be "casts", no sealing/unsealing
of global type variables, only those introduced by gen/inst.
