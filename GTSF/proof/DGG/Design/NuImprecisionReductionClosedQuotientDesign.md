# Smaller term imprecision up to reduction

This note sketches a candidate replacement for the quotient-sensitive part of
term imprecision.  It is a design hypothesis, not yet a proposed change to the
live relation.  The main question is whether bilateral catch-up can keep
quotient imprecision confined between one paired narrowing and its matching
paired widening.

The presentation suppresses type well-formedness, term typing, value
conditions, cast modes, store conditions, and routine transport through store
changes.  Those premises remain necessary in Agda, but they do not determine
the quotient structure under discussion.

Throughout the diagrams, the less precise term is on the left and the more
precise term is on the right.

## Type indices

Ordinary type imprecision is written

$$
A \mathrel{\sqsubseteq_p} A'.
$$

The index records whether corresponding universal quantifiers are matched or
whether a universal quantifier occurs only on the less precise side.  The two
important index forms are

$$
\forall^{\,i} p
\qquad\text{and}\qquad
\nu p.
$$

Imprecision modulo permutation of adjacent universal quantifiers is written

$$
D \mathrel{\sqsubseteq^\forall_q} D'.
$$

It has one definition:

$$
\frac{
  D \approx_\forall C
  \qquad
  C \mathrel{\sqsubseteq_p} C'
  \qquad
  C' \approx_\forall D'
}{
  D \mathrel{\sqsubseteq^\forall_{
    [\,D\approx_\forall C,\;p,\;C'\approx_\forall D'\,]}} D'
}.
$$

Thus quotient imprecision does not identify arbitrary types.  It exposes an
ordinary imprecision derivation between two selected representatives and
permits only `∀`-permutation on either side of it.

## The two term judgments

The public, ordinary judgment is

$$
M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'.
$$

The auxiliary quotient judgment is

$$
N \mathrel{\sqsubseteq^\forall_q} N'
  : D \mathrel{\sqsubseteq^\forall} D'.
$$

The ordinary judgment is used in theorem statements, contexts,
substitution, and structural congruence.  The quotient judgment is a temporary
state with exactly one introduction rule.  It is not a second general-purpose
term relation.

## Ordinary structural rules

The familiar syntax-directed rules remain in the ordinary judgment.  The
representative function rules are

$$
\frac{
  N \mathrel{\sqsubseteq_{p_B}} N'
  \text{ under }
  x : A \mathrel{\sqsubseteq_{p_A}} A'
}{
  \lambda x.\,N
  \mathrel{\sqsubseteq_{p_A\to p_B}}
  \lambda x.\,N'
}.
$$

$$
\frac{
  L \mathrel{\sqsubseteq_{p_A\to p_B}} L'
  \qquad
  M \mathrel{\sqsubseteq_{p_A}} M'
}{
  L\,M \mathrel{\sqsubseteq_{p_B}} L'\,M'
}.
$$

Variables, blame, constants, and primitive operations retain their ordinary
rules as well.  In particular, application consumes only ordinary premises.

The polymorphic rules also remain ordinary.  Their essential index changes
are:

$$
\frac{
  V \mathrel{\sqsubseteq_p} V'
}{
  \Lambda V
  \mathrel{\sqsubseteq_{\forall^{\,i}p}}
  \Lambda V'
}
\qquad
\frac{
  V \mathrel{\sqsubseteq_p} N'
}{
  \Lambda V
  \mathrel{\sqsubseteq_{\nu p}}
  N'
}.
$$

Matched type application removes a matched index, whereas source-only type
application removes a source-only index:

$$
\frac{
  L \mathrel{\sqsubseteq_{\forall^{\,i}p}} L'
}{
  L\,\bullet \mathrel{\sqsubseteq_p} L'\,\bullet
}
\qquad
\frac{
  L \mathrel{\sqsubseteq_{\nu p}} N'
}{
  L\,\bullet \mathrel{\sqsubseteq_p} N'
}.
$$

The `ν` term follows the same discipline:

$$
\frac{
  N \mathrel{\sqsubseteq_{\forall^{\,i}q}} N'
}{
  \nu A\,N\,s
  \mathrel{\sqsubseteq_p}
  \nu A'\,N'\,s'
}
\qquad
\frac{
  N \mathrel{\sqsubseteq_{\nu q}} N'
}{
  \nu A\,N\,s
  \mathrel{\sqsubseteq_p}
  N'
}.
$$

The omitted equations apply the selected type instantiations to the inner
index.  What matters here is that a matched `ν` rule can consume only
`∀ⁱ`, while a source-only `ν` rule can consume only `ν`.  A derivation cannot
silently remove on the left a universal quantifier that was matched with a
universal quantifier on the right.

The existing target-only type-application and `ν` cases remain ordinary too.
None of the polymorphic rules accepts or produces quotient term imprecision.

## Ordinary cast and conversion rules

One-sided casts remain ordinary whenever their type-imprecision triangle
commutes.  Schematically, a source cast uses

$$
\begin{array}{ccc}
A & \mathrel{\sqsubseteq_p} & A'\\
\downarrow c & & \Vert\\
B & \mathrel{\sqsubseteq_r} & A'
\end{array}
\qquad\Longrightarrow\qquad
M\langle c\rangle
\mathrel{\sqsubseteq_r}
M'.
$$

A target cast uses the mirror-image triangle:

$$
\begin{array}{ccc}
A & \mathrel{\sqsubseteq_p} & A'\\
\Vert & & \downarrow c'\\
A & \mathrel{\sqsubseteq_r} & B'
\end{array}
\qquad\Longrightarrow\qquad
M
\mathrel{\sqsubseteq_r}
M'\langle c'\rangle.
$$

These schemas cover both narrowing and widening; the direction of shape
composition records which side of the triangle is traversed first.
Reveal and conceal conversions likewise stay ordinary and update the ordinary
index by the corresponding source or target type substitution.

Paired casts also preserve the ordinary judgment when both the upper and
lower horizontal edges are ordinary:

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  \qquad
  \begin{array}{ccc}
  A & \mathrel{\sqsubseteq_p} & A'\\
  \downarrow c & & \downarrow c'\\
  B & \mathrel{\sqsubseteq_r} & B'
  \end{array}
}{
  M\langle c\rangle
  \mathrel{\sqsubseteq_r}
  M'\langle c'\rangle
}.
$$

This paired rule includes the reveal, conceal, conversion, and ordinary
widening cases already required by the live proof.  It does not cover a
bottom edge that exists only modulo `∀`-permutation.

## The only quotient introduction

The quotient judgment has exactly one constructor.  It places one narrowing
cast around each side of an ordinary-related pair:

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  \qquad
  \begin{array}{ccc}
  A & \mathrel{\sqsubseteq_p} & A'\\
  \downarrow d & & \downarrow d'\\
  D & \mathrel{\sqsubseteq^\forall_q} & D'
  \end{array}
  \qquad
  d,d' \text{ are narrowing}
}{
  M\langle d\rangle
  \mathrel{\sqsubseteq^\forall_q}
  M'\langle d'\rangle
}.
$$

The square includes the existing composition condition

$$
\operatorname{shape}(d)
\mathbin{;}\lfloor p\rfloor
\mathrel{\cong^\forall_q}
\mathbin{;}\operatorname{shape}(d').
$$

That condition says that both paths through the square have the same
imprecision shape after moving to the representatives stored in `q`.

The premise is deliberately ordinary.  Therefore this rule cannot put a
second paired narrowing around an already quotient-related term.

## Closing the quotient

A paired widening returns immediately to the ordinary judgment:

$$
\frac{
  N \mathrel{\sqsubseteq^\forall_q} N'
  \qquad
  \begin{array}{ccc}
  D & \mathrel{\sqsubseteq^\forall_q} & D'\\
  \downarrow u & & \downarrow u'\\
  A & \mathrel{\sqsubseteq_p} & A'
  \end{array}
  \qquad
  u,u' \text{ are widening}
  \qquad
  u,u' \text{ are operationally compatible}
}{
  N\langle u\rangle
  \mathrel{\sqsubseteq_p}
  N'\langle u'\rangle
}.
$$

The corresponding composition condition is

$$
\operatorname{shape}(u)
\mathbin{;}\lfloor p\rfloor
\mathrel{\cong^\forall_q}
\mathbin{;}\operatorname{shape}(u').
$$

Operational compatibility is not merely another typing premise.  It is the
semantic promise that active behavior on either widening can be joined at the
ordinary representative index.  Function and universal widenings require
this promise recursively.  An active `inst` may allocate and therefore needs
the allocation-aware target-tail argument already isolated in the DGG proof.

This compatibility condition must be justified by catch-up lemmas.  It must
not be weakened merely to make the term rule constructible.

## Rules deliberately absent

There is no quotient rule for application:

$$
\frac{
  L \mathrel{\sqsubseteq^\forall} L'
  \qquad
  M \mathrel{\sqsubseteq^\forall} M'
}{
  L\,M \mathrel{\sqsubseteq^\forall} L'\,M'
}
\quad\text{is not a rule.}
$$

There is likewise no quotient rule for lambda abstraction, type abstraction,
type application, `ν`, arbitrary paired casts, or substitution.  In
particular, none of the following is present:

$$
\begin{aligned}
&\text{a finite narrowing spine},\\
&\text{a quotient-to-quotient cast square},\\
&\text{a fused down/application/up rule},\\
&\text{a rule specialized to two, three, or more function casts}.
\end{aligned}
$$

By inversion, every quotient-related term has exactly the form

$$
M\langle d\rangle
\mathrel{\sqsubseteq^\forall_q}
M'\langle d'\rangle
$$

for an ordinary derivation `M ⊑ M'` and one paired narrowing.  A quotient
index is therefore a scoped intermediate state:

$$
\text{ordinary}
\;\longrightarrow\;
\text{one open quotient boundary}
\;\longrightarrow\;
\text{ordinary}.
$$

## Bilateral reduction closure

The smaller relation is intended to be used up to reduction, rather than to
relate the immediate reduct after every leading step.  Its reduction closure
is

$$
M \mathrel{\sqsubseteq^{\twoheadrightarrow}_p} M'
\quad\text{if}\quad
\exists N,N'.\;
M \longrightarrow^* N
\;\land\;
M' \longrightarrow^* N'
\;\land\;
N \mathrel{\sqsubseteq_p} N'.
$$

For a source-leading step, the desired simulation conclusion is stated
directly as

$$
\begin{aligned}
M \mathrel{\sqsubseteq_p} M'
\;\land\;
M \longrightarrow M_1
\quad\Longrightarrow\quad
\exists N,N'.\;&
M_1 \longrightarrow^* N\\
&{}\land M' \longrightarrow^* N'\\
&{}\land N \mathrel{\sqsubseteq_p} N'.
\end{aligned}
$$

The square has this shape:

$$
\begin{array}{ccccc}
M & \mathrel{\sqsubseteq_p} & M'\\
\downarrow & & \Big\Downarrow^{*}\\
M_1 & & N'\\
\Big\Downarrow^{*} & & \Big\Downarrow^{0}\\
N & \mathrel{\sqsubseteq_p} & N'
\end{array}
$$

For a target-leading step, both the source catch-up and the target tail may be
nonempty:

$$
\begin{aligned}
M \mathrel{\sqsubseteq_p} M'
\;\land\;
M' \longrightarrow M'_1
\quad\Longrightarrow\quad
\exists N,N'.\;&
M \longrightarrow^* N\\
&{}\land M'_1 \longrightarrow^* N'\\
&{}\land N \mathrel{\sqsubseteq_p} N'.
\end{aligned}
$$

$$
\begin{array}{ccccc}
M & \mathrel{\sqsubseteq_p} & M'\\
\Big\Downarrow^{*} & & \downarrow\\
N & & M'_1\\
\Big\Downarrow^{0} & & \Big\Downarrow^{*}\\
N & \mathrel{\sqsubseteq_p} & N'
\end{array}
$$

The extra reduction below the leading step is what may eliminate an
application containing an open quotient boundary before the final horizontal
relation is required.

## Function-cast beta

The leading reduction for a function cast is

$$
(V\langle c\mapsto d\rangle)\,W
\longrightarrow
(V\,(W\langle c\rangle))\langle d\rangle.
$$

The live fused rule relates the immediate terms on the right by allowing the
quotient argument inside application.  The smaller design does not try to
draw that horizontal edge.  It continues reducing both sides and asks only
for an ordinary horizontal edge at a later join.

The checked two-function example uses paired casts of opposite polarity:

$$
\bigl(
  (\lambda x.\,x)
    \langle u\mapsto d\rangle
    \langle d\mapsto u\rangle
\bigr)\,W
\longrightarrow^*
W\langle d\rangle\langle u\rangle
 \langle d\rangle\langle u\rangle.
$$

The target follows the corresponding primed path:

$$
\bigl(
  (\lambda x.\,x)
    \langle u'\mapsto d'\rangle
    \langle d'\mapsto u'\rangle
\bigr)\,W'
\longrightarrow^*
W'\langle d'\rangle\langle u'\rangle
  \langle d'\rangle\langle u'\rangle.
$$

If `W ⊑ W'` is ordinary, the bottom relation is built by opening and closing
one boundary twice:

$$
\begin{aligned}
W
&\mathrel{\sqsubseteq} W'\\
W\langle d\rangle
&\mathrel{\sqsubseteq^\forall}
W'\langle d'\rangle\\
W\langle d\rangle\langle u\rangle
&\mathrel{\sqsubseteq}
W'\langle d'\rangle\langle u'\rangle\\
W\langle d\rangle\langle u\rangle\langle d\rangle
&\mathrel{\sqsubseteq^\forall}
W'\langle d'\rangle\langle u'\rangle\langle d'\rangle\\
W\langle d\rangle\langle u\rangle
 \langle d\rangle\langle u\rangle
&\mathrel{\sqsubseteq}
W'\langle d'\rangle\langle u'\rangle
 \langle d'\rangle\langle u'\rangle.
\end{aligned}
$$

Thus additional reachable function casts do not automatically demand longer
narrowing spines.  In this example each new quotient boundary is opened only
after the preceding one has closed.

## Why the same-polarity stress test is not a simulation square

Two same-polarity function casts can reduce to a prefix with two consecutive
narrowings:

$$
W\langle d_2\rangle\langle d_1\rangle.
$$

A finite-spine relation can describe such a prefix in isolation.  The
one-boundary relation cannot.  That fact initially looked like a
counterexample.

However, the chosen source and target intermediate types differed by an
adjacent `∀` permutation.  In the representative instance,

$$
\neg\Bigl(
  \forall X.\,\forall Y.\,X\to Y
  \mathrel{\sqsubseteq}
  \forall Y.\,\forall X.\,X\to Y
\Bigr).
$$

They are related only by quotient imprecision:

$$
\forall X.\,\forall Y.\,X\to Y
\mathrel{\sqsubseteq^\forall}
\forall Y.\,\forall X.\,X\to Y.
$$

Consequently, constructing the second same-polarity function cast would
already require a quotient-to-quotient cast rule at the top of the proposed
simulation square.  The top terms are not ordinarily related, so their common
reduction endpoint cannot refute the smaller relation.

The useful lesson is a reachability condition: a stress test counts only when
its top row is derivable by the proposed public relation.  An isolated
reduct that needs a larger auxiliary relation is only an expressiveness
example for that larger relation.

## Cast-sequence reduction

The source sequence rule has the form

$$
V\langle (G\,?);g\rangle
\longrightarrow
V\langle G\,?\rangle\langle g\rangle.
$$

In the reachable quotient case, the whole sequence need not become a
two-element narrowing spine.  The active untag prefix is absorbed by an
ordinary one-sided cast rule, leaving exactly one paired narrowing:

$$
\begin{aligned}
V &\mathrel{\sqsubseteq} V'\\
V\langle G\,?\rangle
  &\mathrel{\sqsubseteq} V'\\
V\langle G\,?\rangle\langle g\rangle
  &\mathrel{\sqsubseteq^\forall}
    V'\langle g'\rangle\\
\bigl(V\langle G\,?\rangle\langle g\rangle\bigr)
  \langle u\rangle
  &\mathrel{\sqsubseteq}
    \bigl(V'\langle g'\rangle\bigr)\langle u'\rangle.
\end{aligned}
$$

The strict source `β-seq` proof already performs this factorization.  Its
seal-tail alternative is impossible in the relevant narrowing case.  The
remaining target sequence root occurs in the closing widening and belongs to
target-tail resumption; it is not evidence for a finite narrowing spine.

## Substitution boundary

Only the ordinary relation has a substitution theorem:

$$
\frac{
  N \mathrel{\sqsubseteq_{p_B}} N'
  \text{ under }
  x : A \mathrel{\sqsubseteq_{p_A}} A'
  \qquad
  W \mathrel{\sqsubseteq_{p_A}} W'
}{
  N[W/x]
  \mathrel{\sqsubseteq_{p_B}}
  N'[W'/x]
}.
$$

There is intentionally no substitution theorem whose argument premise is
quotient imprecision.  The operational hypothesis must therefore ensure that
the paired widening closes the quotient before an ordinary substitution
lemma is needed.

The checked two-function example verifies substitution through an arbitrary
related body after both down/up round trips have closed.  It does not yet
prove that every function-cast beta case reaches such a closed argument before
substitution.  That is the decisive `sim-beta-cast` obligation.

The GTLC proof suggests the right proof shape: peel the function cast, catch up
the casted argument, recurse on the underlying function application, and
restore the result cast.  In GTSF, the recursion must additionally transport
an active `inst` through any allocation before using the closing widening.

## Proposed proof interface

The design should be accepted only if the following source and target
simulation statements can be proved using the two term judgments above:

$$
\begin{aligned}
M \mathrel{\sqsubseteq_p} M'
\;\land\;
M \longrightarrow M_1
\quad\Longrightarrow\quad
\exists N,N'.\;&
M_1 \longrightarrow^* N\\
&{}\land M' \longrightarrow^* N'\\
&{}\land N \mathrel{\sqsubseteq_p} N',
\end{aligned}
$$

$$
\begin{aligned}
M \mathrel{\sqsubseteq_p} M'
\;\land\;
M' \longrightarrow M'_1
\quad\Longrightarrow\quad
\exists N,N'.\;&
M \longrightarrow^* N\\
&{}\land M'_1 \longrightarrow^* N'\\
&{}\land N \mathrel{\sqsubseteq_p} N'.
\end{aligned}
$$

The store-changing version replaces the displayed terms, types, and indices
by their transported forms.  It should not change where quotient imprecision
may occur.

The critical supporting results are:

1. inversion showing that every quotient term has one ordinary base and one
   paired narrowing;
2. source and target typing projections for both judgments;
3. factorization of narrowing cast sequences into an ordinary prefix and one
   quotient-producing tail;
4. allocation-aware catch-up for a quotient closing widening whose target
   performs `inst`;
5. function-cast beta simulation following the GTLC peel/catch-up/recurse/
   restore pattern;
6. ordinary substitution after the recursive catch-up has closed the
   quotient.

## Decision criterion

The current evidence supports the one-boundary hypothesis:

- the alternating two-function-cast example is derivable and reaches an
  ordinary-related endpoint;
- the endpoint can be substituted into arbitrary ordinarily related bodies;
- the reachable source cast-sequence case factors to one boundary;
- the apparent two-narrowing counterexample has no derivable ordinary top
  row.

The hypothesis is not proved.  The active target `inst` path and the general
function-cast beta case remain open.

If those proofs succeed, the live quotient application rules and
`down·up⊑down·upᵀ` should be derived or removed, not retained as primitive
shortcuts.  If a derivable ordinary top row is found whose reductions can join
only with quotient imprecision trapped under application or substitution,
that will be a genuine counterexample.  Only then should the larger
compositional quotient relation, finite spines, or quotient congruence be
reconsidered.
