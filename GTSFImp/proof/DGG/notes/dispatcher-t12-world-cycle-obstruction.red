Dispatcher T12 peel world-cycle obstruction
============================================

Date: 2026-08-19

Status: proposal note only.  No relation definition was changed.

The approved `PairedConcealRevealPeelᵀ` and
`SourceOnlyConcealRevealPeelᵀ` statements are well formed, but direct
inversion of the migrated `⊢²` relation does not prove them.  The obstruction
is now independent of the removed partner premise.


Paired inversion
----------------

Inverting the exact synchronized source/target term first exposes
`reveal⊑reveal²`; inverting its premise exposes `conceal⊑conceal²` (or the
specialized packaged row in the `seal ★` cell).  In the ordinary paired cell
the payload has the following worlds:

```agda
outer-rebase : RebaseAt W Wmid Xᴸ Xᴿ
inner-rebase : RebaseAt Wcore Wmid Xᴸ Xᴿ
payload      : Wcore ∣ γcore ⊢² V₀ ⊑ V₀′ ∶ pcore
goal         : W     ∣ γ     ⊢² V₀ ⊑ V₀′ ∶ q
```

The two `RebaseAt` values have a common destination; they are not inverse
rebases.  `RebaseAt` freezes the target embedding and the source embedding
away from `Xᴸ`, but deliberately leaves the source-pivot embedding in each
origin unconstrained.  Consequently neither `Wcore ≡ W` nor an existing
`EnvDecay Wcore W` follows.

The minimal attempted clause was:

```agda
paired-conceal-reveal-peel vV vV′
    (reveal⊑reveal² mono outer-rebase sc c⊢ c′⊢
      (conceal⊑conceal² partner monoᵖ inner-rebase scᵖ
        c₀⊢ c₀′⊢ payload qᵖ)
      q)
    (pure-step (conceal-reveal _))
    (pure-step (conceal-reveal _)) = payload
```

Agda rejects the right-hand side because `Wcore != W`.  Retargeting changes
only the proof index in one fixed world and therefore does not repair this
mismatch.

Diagram:

    (V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R   ⊑   (V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′
                    |                                      |
                    | 1                                    | 1
                    v                                      v
                   V₀                  ⊑                  V₀′

The top relation is in `W`, while inversion supplies the requested bottom
payload only in `Wcore`.


Source-only inversion
---------------------

The source-only statement has the same geometry.  `reveal⊑²` exposes a
premise in `Wmid`; its source conceal constructor exposes the payload in
`Wcore`.  The supplied target keep step fixes the target term shape but carries
no world transport, so it cannot turn the payload into a relation in `W`.


Required decision
-----------------

One of the following new major interfaces is required before these peels can
be inhabited:

1. strengthen each peel with an explicit transport from the payload world to
   the outer world (including context and imprecision-index transport); or
2. tighten the synchronized relation rules so the two rebases determine the
   same origin, which is a change to the live relation and therefore requires
   explicit user permission; or
3. restate the dispatcher continuation to consume the payload in its actual
   premise world and perform wrapper replay before returning to the outer
   world.

The current `RestatedDispatcherKeepOutcomesᵀ` also has no field applicable
to the plain target-only heads `⊑reveal²` and `⊑conceal²`: those rows have a
plain source value, whereas every approved continuation requires a matching
source wrapper.  That independent surface gap remains recorded in
`t1-direct-target-frame-certificate-proposal.red`.

Accordingly the target reveal/conceal, source conceal, and paired
reveal/conceal dispatcher residuals remain live.  Implementing a world-cycle
transport theorem or changing either approved statement here would exceed the
decided set, so this pass stops those rows at this proposal note.
