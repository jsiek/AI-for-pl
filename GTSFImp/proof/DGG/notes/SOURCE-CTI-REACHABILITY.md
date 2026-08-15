# Source reachability of the CTI projection mismatch

## Question

Can a related pair of closed gradual source terms compile and reduce to the
abstract CTI counterexample in `ProjectionMismatchStarRepScratch.agda`?

The bad runtime fragment is

$$
\left((0\langle \mathbb{N}!\rangle)\mathbin{\downarrow}
  \operatorname{seal}X\,\star\right)
\quad\sqsubseteq\quad
0\langle \mathbb{N}!\rangle\langle Y?\rangle .
$$

The left side is a value. The right side blames because the projection checks
the unrelated tag `Y` against `\mathbb{N}`.

The counterexample world also assumes that source `X` and target `Y` occupy
the same center while that center is marked `X \sqsubseteq \star`. Source
imprecision does not introduce such a cell at a pair of binders. The checked
binder cases are

$$
\begin{array}{c|c|c}
\text{source form} & \text{target form} & \text{fresh world cell} \\
\hline
\Lambda X & \Lambda Y & (X,Y;\;X\sqsubseteq X) \\
\Lambda X & N'          & (X,-;\;X\sqsubseteq\star).
\end{array}
$$

Thus a dynamic cell initially has no target occupant. If a later target-side
generation is aligned with it, that runtime transition—not a matched
`\Lambda`—must justify the alignment and preserve the generated cast wrappers.
More importantly, under the matched-binder environment the judgment

$$
X \sqsubseteq \star
$$

is empty, whereas it is immediate under the source-only binder environment.
So matched source and target type variables can be used only through
variable-to-variable imprecision in the source derivation.

## A closed related source pair

`SourceLegScratch.agda` defines the following pair, using named variables
here instead of the mechanization's de Bruijn indices:

$$
\begin{aligned}
P ={}&
(\lambda g : \forall X.\,X\to X.\;
   ((\Lambda X.\,\lambda x:X.\,g[X]\,x)[\star])\,0)
\\[-1mm]&\qquad
(\Lambda X.\,\lambda x:X.\,x),
\\[1mm]
Q ={}&
(\lambda g : \forall X.\,X\to X.\;
   (\lambda x:\star.\,g[\star]\,x)\,0)
\\[-1mm]&\qquad
(\lambda x:\star.\,x).
\end{aligned}
$$

The repaired scratch checks all of the following:

- `P` and `Q` are closed and have result type `\star`.
- `P \sqsubseteq Q` in gradual source-term imprecision.
- The proof-erased executable compiler mirrors for `P` and `Q` evaluate to
  values, and their cast/type skeletons equal those of the ordinary compiler.
- The target execution reaches a generated-name projection.

Immediately before that projection, the actual target value is not merely
`0\langle\mathbb{N}!\rangle`. It is

$$
N_Y =
\left((0\langle\mathbb{N}!\rangle)
  \mathbin{\downarrow}\operatorname{seal}Y\,\star\right)
\langle Y!\rangle .
$$

The remaining target context applies `Y?` and then unseals `Y`:

$$
N_Y\langle Y?\rangle
  \mathbin{\uparrow}\operatorname{unseal}Y\,\star .
$$

`SourceReachabilityResultScratch.agda` checks the corresponding
`CatchupCast` witness and this exact reduction:

$$
\begin{aligned}
&N_Y\langle Y?\rangle
  \mathbin{\uparrow}\operatorname{unseal}Y\,\star
\\
&\quad\longrightarrow
\left((0\langle\mathbb{N}!\rangle)
  \mathbin{\downarrow}\operatorname{seal}Y\,\star\right)
  \mathbin{\uparrow}\operatorname{unseal}Y\,\star
\\
&\quad\longrightarrow 0\langle\mathbb{N}!\rangle .
\end{aligned}
$$

Thus this related source pair reaches the critical projection shape, but the
matching `Y!` provenance is still present and the projection cannot mistake
the inner `\mathbb{N}!` tag for its input tag.

The executable compiled mirror for `P` contains an additional inert universal
identity cast, so it is not definitionally the simplified precise checkpoint
in `InitialPairScratch.agda`. Its complete evaluator trace nevertheless returns
a value. In the simplified CTI checkpoint, the corresponding nested seals
cancel in allocation order:

$$
\begin{aligned}
&\left(
  \left((0\langle\mathbb{N}!\rangle)
    \mathbin{\downarrow}\operatorname{seal}X_1\,\star\right)
    \mathbin{\downarrow}\operatorname{seal}X_0\,X_1
  \right)
  \mathbin{\uparrow}\operatorname{unseal}X_0\,X_1
  \mathbin{\uparrow}\operatorname{unseal}X_1\,\star
\\
&\quad\longrightarrow
\left((0\langle\mathbb{N}!\rangle)
  \mathbin{\downarrow}\operatorname{seal}X_1\,\star\right)
  \mathbin{\uparrow}\operatorname{unseal}X_1\,\star
\\
&\quad\longrightarrow 0\langle\mathbb{N}!\rangle .
\end{aligned}
$$

## Forcing the target to blame

The target identity can be replaced by a dynamic function that ignores its
argument and independently manufactures a tagged natural:

$$
d_{\mathrm{bad}}
= \lambda x:\star.\;(\lambda z:\star.\,z)\,0.
$$

Replacing the final `(\lambda x:\star.\,x)` in `Q` by
`d_{\mathrm{bad}}` produces a closed, well-typed target program. The scratch
checks that its executable compiled mirror reaches blame and has the same
cast/type skeleton as the ordinary compiler output. Operationally, the
generalized function receives a value tagged with `Y!`, discards it, returns a
value tagged with `\mathbb{N}!`, and then fails the generated `Y?` projection.

This is not a DGG counterexample. The scratch also checks that there is no
source-imprecision derivation

$$
\Lambda X.\,\lambda x:X.\,x
\quad\sqsubseteq\quad
d_{\mathrm{bad}}.
$$

Inverting the only possible universal-to-dynamic-function rule leaves the
impossible body judgment

$$
x \sqsubseteq (\lambda z:\star.\,z)\,0.
$$

It then refutes the proposed closed judgment `P \sqsubseteq Q_bad` by
inverting the outer application and applying that result to its argument
premise. Source imprecision therefore rejects exactly the value-flow change
needed to expose the mismatched projection.

## Invariant exposed by the failed construction

The experiment supports three connected source invariants.

1. **Binder-match provenance.** Matched `\Lambda` binders create an
   `X\sqsubseteq X` cell. An `X\sqsubseteq\star` cell is created only by a
   source-only binder and initially has no target variable. The abstract bad
   world has both an aligned target variable and the dynamic mark, so it
   already represents a later runtime alignment whose origin has been erased.

   The runtime development can *decay* a matched cell's current world mark from
   `X\sqsubseteq X` to `X\sqsubseteq\star`. Decay transports the original
   variable-to-variable derivations; it does not turn a matched source use into
   a source-level `X\sqsubseteq\star` use. Because the CTI records only the
   current mark, a later CTI constructor can incorrectly treat that decayed
   mark as fresh permission to form a star matchup. The relation must retain
   the pre-decay occurrence/binder provenance as well as the current mark.

2. **Value-flow provenance.** A generated projection `Y?` may inspect only a
   value whose path through the related source terms supplies the matching
   `Y!`, or a residual projection justified after cancellation of such a
   matching pair. An unrelated `\mathbb{N}!` can be returned only by changing
   the target body in a way that breaks source-term imprecision.

3. **Allocation-order provenance.** In the precise execution, the name whose
   store representation is `\star` is the inner, source-only allocation. The
   source name aligned with target `Y` is the outer allocation and has that
   inner name as its representation. Relating the inner source name directly
   to `Y` would cross the order-preserving world embeddings. The checked
   `SourceStarProbe.agda` refutes that crossing in the representative
   two-allocation world.

The unrestricted CTI rule `\sqsubseteq\mathrm{cast}^{2}` forgets the first two
invariants: after decay it can treat the current mark as fresh star-use
permission and append `Y?` using only endpoint type obligations. A manually
assembled CTI world can also omit the allocation history needed to recover the
third invariant.

## Proposed strengthening of CTI

The CTI should distinguish a world's current approximation from the evidence
that authorized each type-variable use. A world cell needs at least the
following provenance.

- **Birth origin:** either `matched`, introduced by source
  `\Lambda\sqsubseteq\Lambda`, or `source-only`, introduced by
  `\Lambda\sqsubseteq N'`.
- **Current mark:** `X\sqsubseteq X` or `X\sqsubseteq\star`, together with the
  decay history from the birth mark. This is operational approximation data,
  not by itself permission to derive a new source `X\sqsubseteq\star` use.
- **Use capability:** matched birth authorizes variable-to-variable uses even
  after decay; source-only birth authorizes source-variable-to-star uses. This
  evidence should be carried by the type and term imprecision derivations
  rather than reconstructed from the current mark.
- **Occupancy and allocation ancestry:** a source-only cell initially has no
  target occupant. Adding or aligning a target variable must record the target
  allocation, the order-preserving embedding facts, and the related store
  representations.
- **Cast ancestry:** runtime alignment must record the matching generated
  injection/projection path, or the residual path left after a matching pair
  has cancelled.

The intended state distinctions are therefore

$$
\begin{aligned}
&\operatorname{matched}(X,Y;X\sqsubseteq X)
  \longrightarrow
  \operatorname{matched}(X,Y;X\sqsubseteq\star),
\\
&\operatorname{sourceOnly}(X,-;X\sqsubseteq\star)
  \longrightarrow
  \operatorname{runtimeAligned}(X,Y;X\sqsubseteq\star,\pi),
\end{aligned}
$$

where the first transition is decay and preserves matched-use capability,
while `\pi` in the second transition is the allocation and cast provenance
that eventually yields `CatchupCast`. The two states on the right have the
same current mark but must not support the same CTI constructors.

This suggests the following rule changes.

1. `\Lambda\sqsubseteq\Lambda` mints matched birth and matched-use evidence;
   `\Lambda\sqsubseteq N'` mints source-only birth and star-use evidence, with
   no target occupant.
2. World decay changes only the current mark. It transports existing use
   evidence and cannot manufacture star-use evidence for a matched binder.
3. `RebaseAt` and smart alias merging may turn a source-only cell into a
   runtime-aligned cell only when they also produce allocation-order,
   store-representation, and cast-ancestry witnesses.
4. `\mathrm{cast}\sqsubseteq\mathrm{cast}^{2}` must relate the consistency
   derivations or their cast directions/shapes, not merely their source and
   target types.
5. `\sqsubseteq\mathrm{cast}^{2}` may add a target projection only from a
   runtime-aligned witness showing a matching target injection, or from
   recursive post-cancellation provenance. The symmetric
   `\mathrm{cast}\sqsubseteq^{2}` rule needs the corresponding source-side
   condition.
6. A target cast column exposed by inversion must carry `CatchupColumn`; its
   head projection then yields `CatchupCast` rather than requiring callers to
   assume it independently.

The required validation theorem has two stages. Compilation should map every
source-term imprecision derivation to the strengthened CTI and mint all birth
and use evidence. Related reduction should preserve that evidence while adding
only justified runtime-alignment and cast-ancestry witnesses. Erasing the
provenance fields may recover the present CTI, but the catch-up and simulation
lemmas should consume the strengthened judgment.

## Conclusion and next theorem

No source-level counterexample was obtained. The strongest constructed target
that really blames is well typed but provably not source-related to the
returning precise program. The strongest genuinely source-related pair reaches
the projection with a checked `CatchupCast` witness and both sides return.

This is evidence, not yet a general preservation theorem. The next sound step
is to prove that source imprecision plus compilation and related reduction
preserve a provenance-indexed CTI judgment. Its world component must remember
whether a cell came from matched binders or from a one-sided binder followed by
runtime alignment, while its use evidence remains tied to the source
derivation. Proving the compilation and reduction preservation stages above
would establish that `CatchupCast` is semantic provenance inherited from the
source, rather than an ad hoc premise added only to close `ExtraCastRight`.
