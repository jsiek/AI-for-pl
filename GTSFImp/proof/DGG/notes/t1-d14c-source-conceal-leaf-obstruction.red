T1 D14(c) source-conceal leaf obstruction
==========================================

Status: option (c) stopped; fall back to option (b).

The attempted private dispatcher was indexed by the existing
`SourceΛReplayStack`.  Its root call used `source-Λ-stack-id`, and the two
source-`Λ` heads extended the stack with `source-Λ-stack-plain` or
`source-Λ-stack-smart`.  This reaches a genuine uncovered leaf when the body
value of a source `Λ` is itself a source conceal value.


Exact leaf
----------

After one or more `Λ` frames, let the current source be `U ↓ c`, with
`Value U` and `ConcealValue c`.  The `conceal⊑²` head at a target identity
conceal supplies:

```agda
partner-before :
  CTI2.SourceConcealPartnerOK Wᵖ U c Xᴿ? (N ↓ id↓ B)

prem :
  Wᵖ ∣ γᵖ ⊢² U ⊑ N ↓ id↓ B ∶ p

step :
  (N ↓ id↓ B) —→[ keep ] N
```

The source is a value because `c` may be `seal X R`, a function conceal, or a
universal conceal.  Therefore this leaf is admitted by both `Value` and the
source-`Λ` constructors; it is not excluded by the value-dispatcher premise.

Recursing on `prem` can produce the stripped body relation

```agda
body-after : Wᵖ ∣ γᵖ ⊢² U ⊑ N ∶ p
```

but replaying the source conceal requires the differently indexed premise

```agda
partner-after :
  CTI2.SourceConcealPartnerOK Wᵖ U c Xᴿ? N
```

The square is:

$$
\begin{array}{ccc}
U \downarrow c & \sqsubseteq & N \downarrow \mathsf{id} \\
\downarrow^{0} & & \downarrow^{1} \\
U \downarrow c & \sqsubseteq & N
\end{array}
$$

For `c = seal X R`, `SourceConcealPartnerOK` contains `SealPartnerOK`, which
examines the target's top-tag shape.  Thus `partner-before` cannot be retargeted
definitionally.  In particular, its `plain-target` case is available for the
outer identity-conceal term, while the reduct `N` may be top-tagged.


Why the existing stack glue does not close the leaf
----------------------------------------------------

`SourceΛReplayStack` has frames only for `Λ⊑²` and
`Λ⊑²-smart-comma`.  It has no source-conceal frame.  Consequently:

- `source-Λ-stack-replay-here` can close `body-after` to the root only after
  the local `U ↓ c ⊑ N` relation has been rebuilt;
- `source-Λ-stack-unlift-plan` has the same prerequisite after a structural
  target plan;
- the proven non-`Λ` keep theorem applies only to bare term lambdas and
  constants, not to `U ↓ c`;
- the T12 identity-conceal continuations require a source `id↓` step and do
  not apply to a source conceal value (`id↓` is not a `ConcealValue`).

Adding a source-conceal frame to the replay stack or a general partner
transport would be a new major surface beyond D14(c).  Therefore the existing
hereditary `SourceΛReplayStack` strategy is insufficient at this reachable
leaf, and the ordered strategy proceeds to the approved generalized recursive
option (b).


Fallback (b) result
-------------------

The generalized recursive conceal proof reaches the same pinned clause during
its full induction on the `⊢²` derivation:

```agda
recursive-source-value-target-conceal-keep vP vN
    (CTI2.conceal⊑² partner-before mono rb sc c⊢ prem q)
    (pure-step (id-conceal vN′)) finalV =
  -- the recursive call on prem supplies body-after
  -- rebuilding conceal⊑² requires partner-after
```

The clause is recursive on the strict derivation premise `prem`, so termination
is not the issue.  All non-seal source conceals can rebuild their endpoint
predicate with `fun-conceal-target`, `all-conceal-target`, or
`id-conceal-target`.  The `seal-partner-ok` case is blocked because its
`SealPartnerOK` evidence is target-term indexed.

A temporary no-hole Agda 2.8 check tried the only possible definitional reuse:

```agda
source-conceal-id-partner-retarget partner = partner
```

at the exact type

```agda
CTI2.SourceConcealPartnerOK W U c Xᴿ? (N ↓ id↓ B)
  → CTI2.SourceConcealPartnerOK W U c Xᴿ? N
```

Agda rejected it with:

```text
N ↓ id↓ B != N of type Term Δᴿ
when checking that the expression partner has type
CTI2.SourceConcealPartnerOK W U c Xᴿ? N
```

The temporary failing probe was deleted after capturing this diagnostic.
There is no current named theorem that supplies this transport.  Proving one
for the `seal` case is the D15 partner-evidence work, not part of the decided
D14(b) theorem.  Per the ordered strategy, fallback (b) stops here and option
(a) is not attempted.  Items 4 and 5 remain downstream of the incomplete keep
story and are not started.
