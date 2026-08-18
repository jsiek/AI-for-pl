# T2 proposal: target-wrapper replay endpoints

Date: 2026-08-17

Status: stopped.

The three target-wrapper replay residuals in
`proof/DGG/SimCastLayerInversion.agda` cannot be implemented from their current
statement evidence by a single CTI2 wrapper replay.  In each case the CTI2
constructor is available, but its conclusion endpoint

```agda
r : A ⊑ᵂ⟨ W ⟩ C
```

is not derivable from the supplied premise endpoint and wrapper evidence.
Leaving this endpoint as `_` produces the three unsolved metas at the replay
pair witnesses.

## `TargetValueCastReplayᵀ`

The statement supplies

```agda
p : A ⊑ᵂ⟨ W ⟩ D
c′ : ν′ ⊢ D ∼ C
Value (V′ ⟨ c′ ⟩)
W ∣ γ ⊢² V ⊑ V′ ∶ p
```

and asks for `A ⊑ᵂ⟨ W ⟩ C`.  Pattern matching on the target value exposes
`Inert c′`, but an inert function cast may narrow the target domain.

Concrete shape:

```agda
A = ‵ `𝔹 ⇒ ‵ `𝔹
D = ★ ⇒ ★
C = ‵ `ℕ ⇒ ★
p = ⇒⊑⇒ ι⊑★ ι⊑★
c′ = (‵ `ℕ ∼ ★) ↦ (★ ∼ ★)
```

Here `Value (V′ ⟨ c′ ⟩)` is available by the `fun` inert constructor, but the
required endpoint would need `‵ `𝔹 ⊑ ‵ `ℕ` in the function domain.  No
imprecision constructor derives that.  Therefore

```agda
_ , CTI2.⊑cast² c′ rel _
```

cannot be completed without either a stronger premise endpoint or a narrower
replay statement.

Diagram:

    V                         V′
    |                         |
    | 0 steps                 | target inert cast
    v                         v
    V            ?⊑           V′ ⟨ c′ ⟩

The missing horizontal witness is `A ⊑ᵂ⟨ W ⟩ C`.

## `TargetValueRevealReplayᵀ`

The statement supplies the target reveal boundary premises

```agda
mono : ImpEnvMono W W′
rb   : RebaseAtᴿ W W′ Xᴿ?
sc   : SameCtx γ γ′
c′⊢  : targetStoreʷ W ⊢↑[ Xᴿ? ] c′
p    : A ⊑ᵂ⟨ W′ ⟩ D
```

and asks for `A ⊑ᵂ⟨ W ⟩ C` when `c′ : Conv↑ Δᴿ D C`.
For a value reveal, `c′` is `fun` or `all`.  In the function case the domain
component can unseal a target variable:

```agda
D = ＇ Xᴿ ⇒ ★
C = R′ ⇒ ★
```

The premise endpoint can relate a source variable to `＇ Xᴿ` in `W′`, while the
conclusion endpoint would need the same source type related to `R′` in `W`.
`rb` and `c′⊢` record the target boundary and store representation, but CTI2
type imprecision has no constructor that turns a variable endpoint into an
arbitrary representation endpoint.  The CTI2 replay

```agda
_ , CTI2.⊑reveal² mono rb sc c′⊢ rel _
```

therefore lacks a derivable final endpoint.

Diagram:

    V                         V′
    |                         |
    | 0 steps                 | target reveal value wrapper
    v                         v
    V            ?⊑           V′ ↑ c′

The missing horizontal witness is `A ⊑ᵂ⟨ W ⟩ C`.

## `TargetValueConcealReplayᵀ`

The statement supplies

```agda
mono : ImpEnvMono W W′
rb   : RebaseAtᴿ W′ W Xᴿ?
sc   : SameCtx γ γ′
c′⊢  : targetStoreʷ W ⊢↓[ Xᴿ? ] c′
p    : A ⊑ᵂ⟨ W′ ⟩ D
```

and asks for `A ⊑ᵂ⟨ W ⟩ C` when `c′ : Conv↓ Δᴿ D C`.
For the seal value case,

```agda
c′ = seal Xᴿ R′
D = R′
C = ＇ Xᴿ
```

the premise may be an ordinary representation endpoint, for example
`‵ `ℕ ⊑ᵂ⟨ W′ ⟩ ‵ `ℕ`, but the conclusion would require
`‵ `ℕ ⊑ᵂ⟨ W ⟩ ＇ Xᴿ`.  CTI2 type imprecision has no base-to-variable rule, and
the supplied boundary premises do not add one.  Thus

```agda
_ , CTI2.⊑conceal² mono rb sc c′⊢ rel _
```

also cannot be completed as stated.

Diagram:

    V                         V′
    |                         |
    | 0 steps                 | target conceal value wrapper
    v                         v
    V            ?⊑           V′ ↓ c′

The missing horizontal witness is `A ⊑ᵂ⟨ W ⟩ C`.

## Proposed repair surface

Do not synthesize endpoint witnesses inside these replay residuals.  Instead,
either:

1. pass the already-derived conclusion endpoint into each replay residual, so
   the replay is purely `CTI2.⊑cast²`, `CTI2.⊑reveal²`, or `CTI2.⊑conceal²`;
   or
2. narrow the replay statements to the specific value-wrapper cases whose
   endpoint is derivable from existing local witnesses.

The current statements are too broad for derive-not-synthesize replay.
