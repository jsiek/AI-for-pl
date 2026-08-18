T1 D14(c)/(b) retry on the D15-migrated conceal heads
=======================================================

Status: the hereditary routing glue checks for the migrated target-independent
heads.  Both (c) and (b) remain conditional on three narrow endpoint rows.

Checked companion:

`proof/DGG/notes/probes/T1D14OptionsProbe.agda`


Migrated (c) outcome
--------------------

The probe now implements the `SourceΛReplayStack` descent rather than merely
stating it.  The worker starts at `source-Λ-stack-id`, extends the stack through
`Λ⊑²` and `Λ⊑²-smart-comma`, recursively handles source value wrappers with a
fresh local stack, and closes each local result with
`source-Λ-stack-replay-here`.

The checked inhabitants are:

```agda
source-Λ-stack-target-reveal-keep :
  SourceConcealTargetIdResidualsᵀ
  → SourceΛStackTargetRevealKeepᵀ

source-Λ-stack-target-conceal-keep :
  SourceConcealTargetIdResidualsᵀ
  → SourceΛStackTargetConcealKeepᵀ
```

The migrated source-star head is no longer blocked.  Given the recursively
stripped body relation, the exact replay is checked as:

```agda
CTI2.conceal⊑²-seal-star-open
  no-target mono rb sc c⊢ body-after q
```

`no-target : NoTargetOccupantAtSource Wᵖ X` is independent of the target term,
so the target identity step does not change it.

The target-insensitive `SourceConcealOK` constructors also replay directly:

- `fun-conceal-ok`;
- `all-conceal-ok`;
- `id-conceal-ok`.

This split is checked by `source-conceal-ok-target-id-view` and its reveal
analogue.  The old target-term-indexed `SourceConcealPartnerOK` is therefore no
longer the first migrated obstruction.


Migrated non-★ seal residual
----------------------------

The remaining migrated constructor is:

```agda
CTI2.seal-nonstar-plain-ok :
  NonStar R
  → NotTopTag M′
  → SourceConcealOK W P (seal X R) Xᴿ? M′
```

At a target identity-conceal keep step it supplies:

```agda
Rns : NonStar R
before-not-top : NotTopTag (N ↓ id↓ B)
```

Replaying the source conceal after the recursive call requires:

```agda
after-not-top : NotTopTag N
```

`before-not-top` is always constructible with `CTI2.not-↓`, even when `N` is a
top tag.  Therefore it cannot be transported to `after-not-top`.  The square
is:

$$
\begin{array}{ccc}
P \downarrow \mathsf{seal}\ X\ R
  & \sqsubseteq & N \downarrow \mathsf{id} \\
\downarrow^{0} & & \downarrow^{1} \\
P \downarrow \mathsf{seal}\ X\ R
  & \sqsubseteq & N
\end{array}
$$

This is witnessed in the checked live-relation counterexample module
`proof/DGG/ExtraCastRight2Counterexample.agda`:

```agda
repaired-source-seal-value
repaired-target-tag-value
repaired-seal-id-conceal²
repaired-target-id-conceal-step
repaired-seal²-empty
```

The source is a non-★ sealed value, the target identity conceal hides an inert
top tag, and `repaired-seal²-empty` proves that the required post-step relation
to that tag has no inhabitant.  Thus `migrated-nonstar-endpoint` is not merely
missing infrastructure; it has no uniform implementation for the current
relation.

The same classifier loss occurs through a target identity reveal.  The probe
names only the missing endpoint facts:

```agda
migrated-nonstar-endpoint : ... → NotTopTag N
migrated-nonstar-reveal-endpoint : ... → NotTopTag N
```

No broad keep theorem or arbitrary partner transport is assumed.


Legacy residual
---------------

The D15 migration retained `conceal⊑²` and `SourceConcealPartnerOK`.  A total
theorem over `_⊢²_` must still cover that constructor even if a particular
fresh construction path emits only the new heads.  Its seal case still asks
for the old endpoint transport:

```agda
SealPartnerOK W X P R Xᴿ? (N ↓ id↓ B)
  → SealPartnerOK W X P R Xᴿ? N
```

The conditional worker isolates this as `legacy-seal-endpoint`, plus the
identity-reveal analogue `legacy-seal-reveal-endpoint`.  The legacy
function/universal/identity conceal cases replay without a residual.


Target `conceal-reveal` residual
--------------------------------

The target reveal worker additionally exposes the one remaining non-identity
keep row as `target-conceal-reveal-endpoint`.  It is the exact stack-indexed
obligation from

```agda
W ∣ γ ⊢² M ⊑ (N ↓ seal X R) ↑ unseal X R ∶ q
```

to the root relation ending at `N`.  It is deliberately not widened into a
general target-step theorem.  The existing synchronized T12 continuation
surface is a candidate implementation input for this row, but the total row
has not been derived here.


Fallback (b) outcome
--------------------

The generalized keep theorem was retried after (c) reached the migrated
non-★ classifier residual.  Its recursive proof has exactly the same endpoint
requirements.  This is checked, rather than inferred, by instantiating the
hereditary worker at `source-Λ-stack-id`:

```agda
recursive-source-value-target-reveal-keep-with-residuals :
  SourceConcealTargetIdResidualsᵀ
  → RecursiveSourceValueTargetRevealKeepᵀ

recursive-source-value-target-conceal-keep-with-residuals :
  SourceConcealTargetIdResidualsᵀ
  → RecursiveSourceValueTargetConcealKeepᵀ
```

Thus (b) does not bypass the classifier loss.  Termination and Λ routing are
both discharged; the residuals are logical endpoint obligations.


Focused gate
------------

The companion checks under Agda 2.8 with `--safe`, with no postulates, holes,
or pragmas.
