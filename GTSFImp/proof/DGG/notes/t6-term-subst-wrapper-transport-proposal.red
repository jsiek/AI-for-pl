CTI2 term substitution wrapper transport gap
===========================================

Context
-------

D8a approved the direct CTI2 parallel term-substitution family:

```
record TermSubstRel {DELTA^L DELTA^R DELTA}
    (W : World DELTA^L DELTA^R DELTA)
    (gamma delta : CtxImp W)
    (sigma^L : CastTerms.Subst DELTA^L)
    (sigma^R : CastTerms.Subst DELTA^R) : Set where
  field
    lookup : forall {x A B} {p : A sqsubseteq^W<W> B}
      -> gamma contains^W x : ctx-imp A B p
      -> W | delta |-2 sigma^L x sqsubseteq sigma^R x : p
```

and the main theorem:

```
|-2-term-subst :
  TermSubstRel W gamma delta sigma^L sigma^R
  -> W | gamma |-2 M sqsubseteq M' : p
  -> W | delta |-2 subst sigma^L M sqsubseteq subst sigma^R M' : p
```

The structural cases whose recursive premises remain at the same world and
same context shape are routine.  The first non-routine case is a wrapper rule,
for example `sqsubseteq-reveal2`.

Blocked case
------------

The constructor has the following shape, suppressing irrelevant type indices:

```
sqsubseteq-reveal2 :
  ImpEnvMono W W'
  -> RebaseAt^R W W' X^R?
  -> SameCtx gamma gamma'
  -> targetStore^W W |-up[ X^R? ] c'
  -> W' | gamma' |-2 M sqsubseteq M' : p
  -> q
  -> W | gamma |-2 M sqsubseteq M' up c' : q
```

After applying term substitution to the conclusion, the same constructor can
reuse the `ImpEnvMono`, `RebaseAt^R`, conversion typing, and result witness
unchanged.  But the recursive premise now requires a substitution relation at
the rebased world and rebased context:

```
delta' : CtxImp W'
SameCtx delta delta'
TermSubstRel W' gamma' delta' sigma^L sigma^R
```

For each variable lookup in `gamma'`, `SameCtx gamma gamma'` only recovers the
same source and target types at the same de Bruijn index, with a different
world-imprecision witness:

```
gamma  contains^W  x : ctx-imp A B p_old
gamma' contains^W' x : ctx-imp A B p_new
```

The D8a environment gives only:

```
W | delta |-2 sigma^L x sqsubseteq sigma^R x : p_old
```

The induction needs:

```
W' | delta' |-2 sigma^L x sqsubseteq sigma^R x : p_new
```

This is not a definitional transport.  It needs a separate CTI2 transport lemma
through the wrapper's world evidence and `SameCtx`:

```
|-2-rebase-samectx-transport^R :
  ImpEnvMono W W'
  -> RebaseAt^R W W' X^R?
  -> SameCtx delta delta'
  -> W | delta |-2 P sqsubseteq Q : p_old
  -> W' | delta' |-2 P sqsubseteq Q : p_new
```

with analogous source, matched-source-target, tag-rebase, and seal-partner
variants.  Existing wrapper constructors add or remove visible conversion terms
around a related pair; they do not provide a pure term-preserving transport
from `W` to `W'`.

Affected CTI2 constructors
--------------------------

The same missing environment transport appears in each wrapper case whose
recursive premise is under a different world/context:

- `sqsubseteq-reveal2`
- `sqsubseteq-conceal2`
- `reveal-sqsubseteq2`
- `conceal-sqsubseteq2`
- `reveal-sqsubseteq-reveal2`
- `conceal-sqsubseteq-conceal2`
- `packaged-seal-star2`

`packaged-seal-star2` needs the transport twice, once for each recursive
premise.

Secondary obligations
---------------------

The `blame-sqsubseteq2` case also needs ordinary lookup inversion from
`tgtCtx^W gamma` back to CTI2 context lookup in order to build the target-side
`SubstWf` for `typing-subst`.  That lookup inversion is local and structural;
it is not the blocker.

The type-binder cases (`Lambda-sqsubseteq-Lambda2`, `Lambda-sqsubseteq2`, and
`Lambda-sqsubseteq2-smart-comma`) need lift lemmas for substitution images, for
example:

```
W | delta |-2 P sqsubseteq Q : p
  -> liftWorldBoth X W | delta_both
       |-2 shiftTyTerm P sqsubseteq shiftTyTerm Q : liftBoth p

W | delta |-2 P sqsubseteq Q : p
  -> liftWorldLeft X W | delta_left
       |-2 shiftTyTerm P sqsubseteq Q : liftLeft p
```

Those lemmas are part of the binder support for D8a, but once they recurse into
the same wrapper constructors they hit the same pure wrapper-transport
obligation above.

Proposed repair surface
-----------------------

Do not strengthen `TermSubstRel` silently: the approved D8a statement is the
right direct theorem, but it assumes substitution images can be reused inside
wrapper premises.  Add and prove a small, explicit family of pure CTI2 transport
lemmas for the wrapper evidence first, then use those lemmas to map
`TermSubstRel W gamma delta sigma^L sigma^R` to the rebased
`TermSubstRel W' gamma' delta' sigma^L sigma^R` needed by the recursive call.

Until that transport family is approved, the D8a central induction cannot be
completed without adding a new major lemma beyond the approved substitution
family.
