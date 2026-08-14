# NS-4 stage 1p resister: safe-inst residual cast classifier

Status: open.

The target-only builder is blocked in the `cast-safe` / `safe-inst` branch of
the new `SpineTyped` cast-frame invariant.

The branch starts from a generated safe-inst frame:

```agda
cast-frame ((inst c) B≢★) ▻ⁱ spine
```

and `structural-target-inst-step` exposes the strictly smaller child:

```agda
name-type-app-frame (applyBody (bind ★) A) Fin.zero refl refl ▻ⁱ
type-transport-frame (applyBody-open-zero A) ▻ⁱ
reveal-frame (〖 Fin.zero , ★ ↑ A 〗) ▻ⁱ
type-transport-frame
  (trans (replace-zero-open A ★)
    (sym (renameᵗ-wk-eq (A [ ★ ]ᵗ)))) ▻ⁱ
cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
type-transport-frame (renameᵗ-wk-eq B) ▻ⁱ
mapInstantiationSpine (bind ★) spine
```

After stage 1p's classifier change, the generated residual frame needs:

```agda
CastFrameClass (↑ᶜ (close-instᶜ c))
```

The supervisor-approved two-way classifier is enough for root/provenance casts
and for the generated `∀ᶜ d` opening cast:

```agda
cast-inert : Inert c  -> CastFrameClass c
cast-safe  : GenSafe c -> CastFrameClass c
```

but it is not enough for this residual. A direct attempt to prove the standard
candidate

```agda
close-inst-safe :
  (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B) ->
  {{Anv : NonVar A}} ->
  {{z∈A : Fin.zero ∈ᵗ A}} ->
  B ≢ ★ ->
  GenSafe (close-instᶜ c)
```

fails for the nested `gen_` branch. The required `safe-gen` premise after
closing would need:

```agda
substᵗ (singleSubᵗ ★) A₀ ≢ ★
```

from only:

```agda
A₀ ≢ ★
```

That implication is false at the available statement strength: `A₀ = ＇ zero`
is non-star before closing, but closes to `★`.

So the safe-inst residual is not uniformly classifiable as `Inert` or
`GenSafe` from the current generated evidence. The builder needs one of:

1. a third internal `CastFrameClass` case carrying value-cast progress evidence
   for generated residual frames;
2. a specialized safe-inst child builder that uses the live `cast-value-progress`
   / preservation stack instead of the two-way classifier for
   `↑ᶜ (close-instᶜ c)`; or
3. a stronger generated residual side condition excluding the closing variable
   from the source of nested `gen_` casts.

Option 3 would be a semantic restriction and should not be introduced as a
proof-local change. Options 1 or 2 preserve the current reduction relation and
match the type-safety route already used for value typing through steps.
