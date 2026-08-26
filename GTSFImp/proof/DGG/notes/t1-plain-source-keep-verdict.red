T1 plain-source target keep verdict
===================================

Status: UNRESOLVED as of 2026-08-17.

Checked probe:

`proof/DGG/notes/probes/T1PlainSourceKeepProbe.agda`

The probe is standalone `--safe` and contains no holes, postulates, or pragmas.
It does not import into `All.agda`.


What checked
------------

The T10 Probe 3 counterexample does not directly refute the plain-source
instance.  Its source endpoint has the shape
`(V ↓ seal X R) ↑ unseal X R`, and the probe checks that an `unseal` reveal is
neither a bare value nor a `Value`:

`unseal-reveal-not-bare-value`

`unseal-reveal-not-value`

The probe also checks the direct top-wrapper facts needed by the plain-source
attempt:

`sameCtx-eq`

`sameCtx-transport`

`plain-source-to-target-var-empty`

The last fact says that if the left term is a bare value, then a relation whose
right endpoint type is a target variable is underivable.  This rules out the
direct target-only `unseal` keep row when the relation head is actually
`⊑reveal²`: its premise would have to relate the same bare source to a
target-sealed term at right type `＇ X`.

For non-`Λ` bare source values, the narrow keep theorem does check for both
target reveal and target conceal:

`NonΛSourceTargetRevealKeepᵀ`

`nonΛ-source-target-reveal-keep`

`NonΛSourceTargetConcealKeepᵀ`

`nonΛ-source-target-conceal-keep`

This covers bare term lambdas and constants.  It also proves that the ordinary
identity target wrapper rows can be stripped after collapsing `SameCtx` to
propositional equality via uniqueness of type-imprecision evidence.


Reveal verdict
--------------

Verdict: UNRESOLVED for the full plain-source theorem.

The direct `⊑reveal²` head is handled by the checked
`plain-source-to-target-var-empty` inversion.  The unresolved cases are the
source type-abstraction base heads:

`Λ⊑²`

`Λ⊑²-smart-comma`

Those rules can relate a top-level plain source `Λ V` to an arbitrary target
term, including `N ↑ c′`.  After the target keep step, rebuilding the outer
`Λ` relation requires a recursive/replay theorem for the body value `V` under
the lifted or smart-comma world.  The current probe does not establish that
generalized theorem.

So the proposed reveal certificate is not replaced by a checked theorem in this
run.


Conceal verdict
---------------

Verdict: UNRESOLVED for the full plain-source theorem.

For non-`Λ` bare source values, target `id↓` keep strips successfully.  The
full theorem again reaches the source type-abstraction base heads:

`Λ⊑²`

`Λ⊑²-smart-comma`

The natural recursive proof has to strip `N ↓ id↓ B` in the body relation.
When the body proof crosses a source-conceal wrapper, the available
`SourceConcealPartnerOK` evidence is indexed by the old target term
`N ↓ id↓ B`; it is not automatically evidence for the stripped target `N`.
No checked transport for that partner evidence was found in this run.

So the proposed conceal certificate is not replaced by a checked theorem in
this run.


Dispatcher consequence
----------------------

No dispatcher work was done.

Because neither full plain-source theorem is checked, the certificates from
`t1-direct-target-frame-certificate-proposal.red` remain the conservative ask.
The current target-frame helper functions pass the post-child `frame-rel`, the
target keep step, and the final value to their caller-supplied `keep-cont`.
If the certificate route is kept, that caller-side continuation is the place
that can supply any extra local replay or partner-transport evidence.  The
plain target-frame helper itself only has the rebuilt frame relation and the
target step; the probe did not establish enough evidence for it to synthesize
the full plain-source result internally.
