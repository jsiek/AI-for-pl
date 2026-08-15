# NS-4 stage 1y termination measure

Date: 2026-08-15

Status: implementation note.

The worker uses the lexicographic tuple

```text
(pendingCastMass vV spine,
 pendingRank.nameFrames vV spine,
 pendingRank.expPotential vV spine,
 pendingRank.spineLength vV spine,
 phaseDerivSize phase rel)
```

where `derivSize` is the structural size of the `W ∣ γ ⊢² M ⊑ V ∶ p`
derivation, weighted so every unary source wrapper adds two.  The worker uses
two phases for the last component:

```text
phaseDerivSize spine-phase rel = suc (derivSize rel)
phaseDerivSize name-phase rel  = derivSize rel
```

The general-spine-to-name handoff on
`name-type-app-frame B X refl refl ▻ⁱ spine` preserves mass, rank, and
`derivSize`, but strictly decreases the phase-adjusted final component from
`suc (derivSize rel)` to `derivSize rel`.  Equal source wrappers preserve mass
and rank, switch back to `spine-phase`, and still strictly decrease the final
component because `derivSize` of the wrapper is `suc (suc (derivSize prem))`.
Strict target-shape cases decrease either `pendingCastMass` or `pendingRank`;
when one of those earlier components decreases, the final component may reset.

## Recursive call-site table

| Site | Child state | Strict component |
| --- | --- | --- |
| general spine name-frame dispatch | same value/relation, name worker phase | `phaseDerivSize` decreases from `spine-phase` to `name-phase` |
| `type-transport-frame` spine case | same value, tail spine, transported relation | `pendingRank.spineLength` decreases by `type-frame-rank-decreases` |
| inert `cast-frame` spine case | casted value, tail spine, absorbed relation | `pendingRank.spineLength` decreases by `cast-frame-rank-decreases` |
| safe function `cast-frame` spine case | function-casted value, tail spine | `pendingRank.spineLength` decreases by `cast-frame-rank-decreases` |
| safe forall `cast-frame` spine case | forall-casted value, tail spine | `pendingRank.spineLength` decreases by `cast-frame-rank-decreases` |
| safe gen `cast-frame` spine case | gen-casted value, tail spine | `pendingRank.spineLength` decreases by `cast-frame-rank-decreases` |
| residual `cast-frame` tail continuation | residual stop value and supplied child spine | `pendingCastMass` decreases by the `residual-tail-child` contract |
| safe inst `cast-frame` spine case | renamed value and generated safe-inst child spine | `pendingCastMass` decreases by `inst-primary-decreases` |
| reveal frame, value outcome | revealed child value and tail spine | `pendingRank.expPotential`/length decreases by `reveal-frame-value-rank-decreases-any` |
| reveal frame, identity keep | same value and `mapInstantiationSpine keep spine` | `pendingRank.expPotential`/length decreases by `reveal-frame-id-rank-decreases` |
| reveal frame, conceal/reveal keep | inner value and `mapInstantiationSpine keep spine` | `pendingRank.expPotential` decreases by `reveal-frame-conceal-rank-decreases` |
| conceal frame, value outcome | concealed child value and tail spine | `pendingRank.expPotential`/length decreases by `conceal-frame-value-rank-decreases-any` |
| conceal frame, identity keep | same value and `mapInstantiationSpine keep spine` | `pendingRank.expPotential`/length decreases by `conceal-frame-id-rank-decreases` |
| source `cast⊑²` equal case | premise derivation, same target value and name spine | `phaseDerivSize`: `suc (derivSize prem) < suc (suc (derivSize prem))` |
| source plain `Λ⊑²` equal case | premise derivation, same target value and name spine | `phaseDerivSize`: `suc (derivSize prem) < suc (suc (derivSize prem))` |
| source smart `Λ⊑²-smart-comma` equal case | premise derivation, same target value and name spine | `phaseDerivSize`: `suc (derivSize prem) < suc (suc (derivSize prem))` |
| source `reveal⊑²` equal case | premise derivation, same target value and name spine | `phaseDerivSize`: `suc (derivSize prem) < suc (suc (derivSize prem))` |
| source `conceal⊑²` equal case | premise derivation, same target value and name spine | `phaseDerivSize`: `suc (derivSize prem) < suc (suc (derivSize prem))` |
| strict `Λ` target case | strict-surface child value and `lambda-child-spine` | `pendingRank.nameFrames`/rank decreases by `lambda-rank-decreases` |
| strict `∀` cast target case | same inner value and `all-cast-child-spine` | `pendingCastMass` decreases by `all-primary-decreases-at` |
| strict gen target case | renamed child value and `gen-child-spine` | `pendingCastMass` decreases by `gen-primary-decreases` |
| strict reveal target case | renamed child value and `reveal-child-spine` | `pendingRank.nameFrames`/rank decreases by `reveal-rank-decreases` |
| strict conceal target case | renamed child value and `conceal-child-spine` | `pendingRank.nameFrames`/rank decreases by `conceal-rank-decreases` |

Every recursive call receives the caller-derived child accessibility proof by
pattern matching the caller proof as `WF.acc smaller` and passing `smaller` the
site-specific strict-decrease proof.  No recursive branch rebuilds accessibility
with fresh well-founded access.
