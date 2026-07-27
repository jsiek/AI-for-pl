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

Variables are related according to the ordinary imprecision index stored in
the term context:

$$
\frac{
  x : A \mathrel{\sqsubseteq_p} A' \in \Gamma
}{
  x \mathrel{\sqsubseteq_p} x
  : A \mathrel{\sqsubseteq} A'
}.
$$

Blame on the less precise side is related to every target term at the indexed
target type:

$$
\frac{}{
  \mathsf{blame}
  \mathrel{\sqsubseteq_p}
  M'
  : A \mathrel{\sqsubseteq} A'
}.
$$

The suppressed premise checks that `M'` has type `A'`.

Natural-number constants are related only to the same constant:

$$
\frac{}{
  \kappa_{\mathbb N}(n)
  \mathrel{\sqsubseteq_{\mathsf{id}_{\mathbb N}}}
  \kappa_{\mathbb N}(n)
  : \mathbb N \mathrel{\sqsubseteq} \mathbb N
}.
$$

The primitive addition rule is structural at the identity index:

$$
\frac{
  L
  \mathrel{\sqsubseteq_{\mathsf{id}_{\mathbb N}}}
  L'
  \qquad
  M
  \mathrel{\sqsubseteq_{\mathsf{id}_{\mathbb N}}}
  M'
}{
  L \mathbin{\oplus} M
  \mathrel{\sqsubseteq_{\mathsf{id}_{\mathbb N}}}
  L' \mathbin{\oplus} M'
  : \mathbb N \mathrel{\sqsubseteq} \mathbb N
}.
$$

In particular, application and primitive operations consume only ordinary
premises.

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

The `ν` term follows the same discipline.  To display its index equations,
write `↑A` for the weakening of `A` under the freshly allocated type
variable, and write `lift` for the corresponding extension of an outer
imprecision index.  The symbol `≐` below denotes the proof-relevant index
compatibility judgment implemented in Agda, not propositional equality.

In the matched case, the selected source and target types are themselves
ordinarily related:

$$
\frac{
  A \mathrel{\sqsubseteq_{p_A}} A'
  \qquad
  N \mathrel{\sqsubseteq_{\forall^{\,i}q}} N'
  \qquad
  q[
    0 \mapsto {\uparrow A}
    \mathrel{\sqsubseteq_{\operatorname{lift}(p_A)}}
    {\uparrow A'} \leftarrow 0
  ]^P
  \doteq
  \operatorname{lift}_{\forall}(p)
}{
  \nu A\,N\,s
  \mathrel{\sqsubseteq_p}
  \nu A'\,N'\,s'
}
.
$$

In the source-only case, instantiating the source-only index must produce the
lift of the result index:

$$
\frac{
  N \mathrel{\sqsubseteq_{\nu q}} N'
  \qquad
  q[0 \mapsto {\uparrow A}]^L
  \doteq
  \operatorname{lift}_{\nu}^{L}(p)
}{
  \nu A\,N\,s
  \mathrel{\sqsubseteq_p}
  N'
}
.
$$

There is no target-only `ν` rule.  The tempting rule would require both a
pre-allocation index and an independently opened body index:

$$
\begin{aligned}
q &: \Phi \mathbin{;} \Delta_L
  \vdash B \mathrel{\sqsubseteq} \forall C'
  \dashv \Delta_R,\\
r &: \mathord{\uparrow_R}\Phi \mathbin{;} \Delta_L
  \vdash B \mathrel{\sqsubseteq} C'
  \dashv \operatorname{suc}(\Delta_R).
\end{aligned}
$$

These two premises are inconsistent:

$$
\neg\!\left(
  \bigl(\Phi \mathbin{;} \Delta_L
    \vdash B \mathrel{\sqsubseteq} \forall C'
    \dashv \Delta_R\bigr)
  \mathbin{\land}
  \bigl(\mathord{\uparrow_R}\Phi \mathbin{;} \Delta_L
    \vdash B \mathrel{\sqsubseteq} C'
    \dashv \operatorname{suc}(\Delta_R)\bigr)
\right).
$$

Right-lifting the first index puts the unchanged source type below
`∀` applied to the uniformly lifted target body.  Pairing that index with the
second would put one common source below both the target body and an extra
universal over its uniformly lifted copy.  Exhaustive inversion of type
imprecision rules this out.  Consequently neither a result-index equation

$$
r[0 \mapsto {\uparrow A}]^R
\doteq
\operatorname{lift}^{R}(p)
$$

nor a target reveal conversion from `C'` to `↑B'` can make the case
inhabited: the contradiction already uses only `q` and `r`.

The same obstruction excludes the target-only type-application rule and the
cast-specialized target-only `ν` rule, because both require the same pair of
indices.  Actual target-only allocation is instead handled by the
up-to-reduction conclusion.  The top relation remains at the target
instantiation, the target takes its whole administrative tail,

$$
V'\langle\mathsf{inst}\ B\ s\rangle
\longrightarrow
\nu\,\star\,V'\,s
\longrightarrow
\bigl((\mathord{\uparrow}V')\,\bullet\bigr)\langle s\rangle
\longrightarrow^{*}
W',
$$

and ordinary imprecision is required only between the source catch-up result
and `W'`.  No horizontal edge is asserted at the transient target `ν` or
runtime-bullet states.

The evidence retained across this target trace should be a creation square,
not an independently opened index.  In the directly matched case its
essential form is

$$
\begin{aligned}
W &\mathrel{\sqsubseteq_q} W'
  : D \mathrel{\sqsubseteq} C',\\
\Lambda W &\mathrel{\sqsubseteq_{\forall^{\,i}q}} \Lambda W',\\
\mathsf{inst}\ B'\ s
  &: \forall C' \longrightarrow B',\\
\left\lfloor \forall^{\,i}q \right\rfloor
  \mathbin{;}
\left\lfloor \mathsf{inst}\ B'\ s \right\rfloor
  &\mathrel{\cong}
\left\lfloor p \right\rfloor,
\end{aligned}
$$

where `p` is necessarily source-only at its outer universal.  A
proof-relevant version of this square should retain the matched body
imprecision, the target conversion, the final source-only index, and the
right-allocation store lineage.  It should not manufacture

$$
B \mathrel{\sqsubseteq_r} C'
$$

after allocation.  The existing live `Λ⊑instβᵀ` constructor carries most of
this provenance, but it also carries arbitrary endpoint renaming, store
embedding, endpoint equalities, closure evidence, and the final
post-administration horizontal edge.

### Checked target-instantiation creation test

The focused test starts from the valid ordinary top row

$$
\Lambda(\lambda x.x)
\mathrel{\sqsubseteq}
\Lambda(\lambda x.x)
\left\langle
  \mathsf{inst}\ (\star\to\star)\
  \bigl(
    \mathsf{seal}\ \star\ 0
    \to
    \mathsf{unseal}\ 0\ \star
  \bigr)
\right\rangle
:
\forall\alpha.(\alpha\to\alpha)
\mathrel{\sqsubseteq}
\star\to\star .
$$

The source takes zero steps.  The target takes the complete administrative
trace

$$
\begin{aligned}
&\Lambda(\lambda x.x)
\left\langle
  \mathsf{inst}\ (\star\to\star)\
  \bigl(
    \mathsf{seal}\ \star\ 0
    \to
    \mathsf{unseal}\ 0\ \star
  \bigr)
\right\rangle
\\
&\quad\longrightarrow
\nu\,\star\,\Lambda(\lambda x.x)\
  \bigl(
    \mathsf{seal}\ \star\ 0
    \to
    \mathsf{unseal}\ 0\ \star
  \bigr)
\\
&\quad\longrightarrow
\bigl((\mathord{\uparrow}\Lambda(\lambda x.x))\,\bullet\bigr)
\left\langle
  \mathsf{seal}\ \star\ 0
  \to
  \mathsf{unseal}\ 0\ \star
\right\rangle
\\
&\quad\longrightarrow
(\lambda x.x)
\left\langle
  \mathsf{seal}\ \star\ 0
  \to
  \mathsf{unseal}\ 0\ \star
\right\rangle .
\end{aligned}
$$

Thus up-to-reduction removes every transient target-only `ν` or
runtime-bullet edge.  It still leaves the final value row

$$
\Lambda(\lambda x.x)
\mathrel{\sqsubseteq}
(\lambda x.x)
\left\langle
  \mathsf{seal}\ \star\ 0
  \to
  \mathsf{unseal}\ 0\ \star
\right\rangle .
$$

The ordinary source-only-lambda rule followed by an ordinary target-cast rule
cannot derive this row.  That factorization would first require

$$
(0 \mathrel{\sqsubseteq} \star)\mathbin{;}
1
\vdash
(\alpha\to\alpha)
\mathrel{\sqsubseteq}
(\alpha\to\alpha)
\dashv
1 .
$$

The source-only assumption relates the source variable to `★`, not to the
fresh target seal.  Exhaustive inversion reaches the impossible variable
judgment

$$
(0 \mathrel{\sqsubseteq} \star)\mathbin{;}
1
\vdash
\alpha
\mathrel{\sqsubseteq}
\alpha
\dashv
1 .
$$

The strict
[`NuImprecisionTargetInstantiationCreationExamples.agda`](../../Quotient/NuImprecisionTargetInstantiationCreationExamples.agda)
checks all three parts of this result:

1. the initial ordinary term-imprecision derivation;
2. the complete target allocation trace; and
3. the impossibility of the opened structural body index.

The same module constructs
[`TargetInstantiationCreation`](../../Quotient/NuImprecisionTargetInstantiationCreationDef.agda),
which contains the matched body relation, target instantiation typing,
creation equation, and store lifts into the final right-extended world.  It
does so without constructing the fused final term-imprecision edge.

This determines the limit of up-to-reduction.  The large live constructor can
be decomposed, but the semantic creation case cannot simply disappear while
`WeakOneStepResult` and the public DGG theorem still demand ordinary term
imprecision between the final values.  The smallest conservative replacement
is an exact creation constructor whose sole premise is the checked creation
residual.  General renaming, store embedding, and endpoint transport should
then be proved as separate admissibility lemmas instead of being fields of the
constructor.  Removing even that exact creation case would require changing
the simulation conclusion to a creation-saturated relation; that merely moves
the same semantic case out of ordinary term imprecision.

### Candidate exact creation rule

The proposed constructor has the following mathematically relevant premises.
First, before allocation the bodies are related under a matched binder:

$$
((0\mathrel{\sqsubseteq}0)::\mathord{\uparrow}\Phi)\mathbin{;}\operatorname{suc}(\Delta_L)\mathbin{;}\operatorname{suc}(\Delta_R)\mathbin{;}\rho_{\forall}\ \vdash\ W\mathrel{\sqsubseteq_q}W' : D\mathrel{\sqsubseteq}C .
$$

The target has an inert widening instantiation:

$$
\mathsf{inst}\ B\ s : \forall C\longrightarrow B .
$$

The matched universal index and the target instantiation shape compose to the
outer source-only index:

$$
\left\lfloor\forall^{\,i}q\right\rfloor\mathbin{;}\left\lfloor\mathsf{inst}\ B\ s\right\rfloor\mathrel{\cong}\left\lfloor p\right\rfloor .
$$

Here the outer index has the required source-only universal:

$$
p : \Phi\mathbin{;}\Delta_L\ \vdash\ \forall D\mathrel{\sqsubseteq}B\ \dashv\Delta_R .
$$

The matched body store and final right-only store must arise from the same
pre-allocation store:

$$
\rho_0\mathrel{\preccurlyeq}\rho^+,\qquad \rho_0\xrightarrow{\,0\mathrel{\sqsubseteq}0\,}\rho_{\forall},\qquad \rho^+\xrightarrow{\,\mathord{\uparrow_R}\,}\rho_R^+ .
$$

Then the exact post-allocation conclusion is:

$$
\mathord{\uparrow_R}\Phi\mathbin{;}\Delta_L\mathbin{;}\operatorname{suc}(\Delta_R)\mathbin{;}(\mathsf{right}\ 0\ \star)::\rho_R^+\ \vdash\ \Lambda W\mathrel{\sqsubseteq_{\mathord{\uparrow_R}p}}W'\langle s\rangle : \forall D\mathrel{\sqsubseteq}\mathord{\uparrow}B .
$$

The Agda constructor must also receive the routine value, no-bullet, cast-mode,
and endpoint-typing evidence needed by the intrinsically indexed judgment.
Unlike `Λ⊑instβᵀ`, it should not receive arbitrary renamings, an arbitrary
store embedding, endpoint equalities, closure witnesses, or an arbitrary final
index. Those operations should be admissibility lemmas over this exact rule.

Thus a matched `ν` rule can consume only `∀ⁱ`, while a source-only `ν` rule
can consume only `ν`.  A derivation cannot silently remove on the left a
universal quantifier that was matched with a universal quantifier on the
right.  Both rules remain in the ordinary judgment; neither accepts or
produces quotient term imprecision.

## Ordinary cast and conversion rules

Write `⌊p⌋` for the structural shape of an ordinary type-imprecision index
and `⌊c⌋` for the imprecision shape of a cast.  The judgment

$$
s_1 \mathbin{;} s_2 \mathrel{\cong} s_3
$$

means that the two imprecision shapes on the left compose to the shape on the
right.  It is a proof-relevant structural composition judgment.

The four one-sided cast rules use different composition equations according
to the side of the cast and its polarity.

A source narrowing cast has the equation

$$
\lfloor c\rfloor
\mathbin{;}\lfloor p\rfloor
\mathrel{\cong}
\lfloor q\rfloor:
$$

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{narrow}(c:A\Rightarrow B)
  \qquad
  B \mathrel{\sqsubseteq_q} A'
  \qquad
  \lfloor c\rfloor
    \mathbin{;}\lfloor p\rfloor
    \mathrel{\cong}\lfloor q\rfloor
}{
  M\langle c\rangle
  \mathrel{\sqsubseteq_q}
  M'
  : B \mathrel{\sqsubseteq} A'
}.
$$

A source widening cast has the equation

$$
\lfloor c\rfloor
\mathbin{;}\lfloor q\rfloor
\mathrel{\cong}
\lfloor p\rfloor:
$$

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{widen}(c:A\Rightarrow B)
  \qquad
  B \mathrel{\sqsubseteq_q} A'
  \qquad
  \lfloor c\rfloor
    \mathbin{;}\lfloor q\rfloor
    \mathrel{\cong}\lfloor p\rfloor
}{
  M\langle c\rangle
  \mathrel{\sqsubseteq_q}
  M'
  : B \mathrel{\sqsubseteq} A'
}.
$$

A target narrowing cast has the equation

$$
\lfloor q\rfloor
\mathbin{;}\lfloor c'\rfloor
\mathrel{\cong}
\lfloor p\rfloor:
$$

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{narrow}(c':A'\Rightarrow B')
  \qquad
  A \mathrel{\sqsubseteq_q} B'
  \qquad
  \lfloor q\rfloor
    \mathbin{;}\lfloor c'\rfloor
    \mathrel{\cong}\lfloor p\rfloor
}{
  M
  \mathrel{\sqsubseteq_q}
  M'\langle c'\rangle
  : A \mathrel{\sqsubseteq} B'
}.
$$

A target widening cast has the equation

$$
\lfloor p\rfloor
\mathbin{;}\lfloor c'\rfloor
\mathrel{\cong}
\lfloor q\rfloor:
$$

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{widen}(c':A'\Rightarrow B')
  \qquad
  A \mathrel{\sqsubseteq_q} B'
  \qquad
  \lfloor p\rfloor
    \mathbin{;}\lfloor c'\rfloor
    \mathrel{\cong}\lfloor q\rfloor
}{
  M
  \mathrel{\sqsubseteq_q}
  M'\langle c'\rangle
  : A \mathrel{\sqsubseteq} B'
}.
$$

Reveal and conceal conversions replace the shape-composition equation by an
index-substitution equation.  The source reveal and conceal rules are

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{reveal}_L
    (c:A\Rightarrow B;\alpha\mapsto X)
  \qquad
  B \mathrel{\sqsubseteq_q} A'
  \qquad
  p[\alpha\mapsto X]^L \doteq q
}{
  M\langle c\rangle
  \mathrel{\sqsubseteq_q}
  M'
  : B \mathrel{\sqsubseteq} A'
},
$$

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{conceal}_L
    (c:A\Rightarrow B;\alpha\mapsto X)
  \qquad
  B \mathrel{\sqsubseteq_q} A'
  \qquad
  q[\alpha\mapsto X]^L \doteq p
}{
  M\langle c\rangle
  \mathrel{\sqsubseteq_q}
  M'
  : B \mathrel{\sqsubseteq} A'
}.
$$

The target reveal and conceal rules are

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{reveal}_R
    (c':A'\Rightarrow B';\beta\mapsto X')
  \qquad
  A \mathrel{\sqsubseteq_q} B'
  \qquad
  p[\beta\mapsto X']^R \doteq q
}{
  M
  \mathrel{\sqsubseteq_q}
  M'\langle c'\rangle
  : A \mathrel{\sqsubseteq} B'
},
$$

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{conceal}_R
    (c':A'\Rightarrow B';\beta\mapsto X')
  \qquad
  A \mathrel{\sqsubseteq_q} B'
  \qquad
  q[\beta\mapsto X']^R \doteq p
}{
  M
  \mathrel{\sqsubseteq_q}
  M'\langle c'\rangle
  : A \mathrel{\sqsubseteq} B'
}.
$$

Paired reveal uses the ordinary relation between the two selected store
types as part of one simultaneous index substitution:

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{reveal}_L
    (c:A\Rightarrow B;\alpha\mapsto X)
  \qquad
  \operatorname{reveal}_R
    (c':A'\Rightarrow B';\beta\mapsto X')
  \qquad
  X \mathrel{\sqsubseteq_{p_X}} X'
  \qquad
  B \mathrel{\sqsubseteq_q} B'
  \qquad
  p[
    \alpha\mapsto X
    \mathrel{\sqsubseteq_{p_X}}
    X'\leftarrow\beta
  ]^P
  \doteq q
}{
  M\langle c\rangle
  \mathrel{\sqsubseteq_q}
  M'\langle c'\rangle
  : B \mathrel{\sqsubseteq} B'
}.
$$

Paired conceal reverses that index-substitution equation:

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{conceal}_L
    (c:A\Rightarrow B;\alpha\mapsto X)
  \qquad
  \operatorname{conceal}_R
    (c':A'\Rightarrow B';\beta\mapsto X')
  \qquad
  X \mathrel{\sqsubseteq_{p_X}} X'
  \qquad
  B \mathrel{\sqsubseteq_q} B'
  \qquad
  q[
    \alpha\mapsto X
    \mathrel{\sqsubseteq_{p_X}}
    X'\leftarrow\beta
  ]^P
  \doteq p
}{
  M\langle c\rangle
  \mathrel{\sqsubseteq_q}
  M'\langle c'\rangle
  : B \mathrel{\sqsubseteq} B'
}.
$$

Finally, an ordinary paired widening requires both paths to have one common
composite shape, as well as operational compatibility:

$$
\frac{
  M \mathrel{\sqsubseteq_p} M'
  : A \mathrel{\sqsubseteq} A'
  \qquad
  \operatorname{widen}(c:A\Rightarrow B)
  \qquad
  \operatorname{widen}(c':A'\Rightarrow B')
  \qquad
  B \mathrel{\sqsubseteq_q} B'
  \qquad
  \lfloor c\rfloor
    \mathbin{;}\lfloor q\rfloor
    \mathrel{\cong} t
  \qquad
  \lfloor p\rfloor
    \mathbin{;}\lfloor c'\rfloor
    \mathrel{\cong} t
  \qquad
  \operatorname{compatible}(c,c';p,q)
}{
  M\langle c\rangle
  \mathrel{\sqsubseteq_q}
  M'\langle c'\rangle
  : B \mathrel{\sqsubseteq} B'
}.
$$

All these rules remain ordinary because their conclusions carry ordinary type
imprecision.  The paired widening rule does not cover a lower horizontal edge
that exists only modulo `∀`-permutation; that case belongs to quotient
closing below.

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
  \qquad
  \lfloor d\rfloor
    \mathbin{;}\lfloor p\rfloor
    \mathrel{\cong^\forall_q}
    \mathbin{;}\lfloor d'\rfloor
}{
  M\langle d\rangle
  \mathrel{\sqsubseteq^\forall_q}
  M'\langle d'\rangle
}.
$$

The final premise says that both paths through the square have the same
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
  \qquad
  \lfloor u\rfloor
    \mathbin{;}\lfloor p\rfloor
    \mathrel{\cong^\forall_q}
    \mathbin{;}\lfloor u'\rfloor
}{
  N\langle u\rangle
  \mathrel{\sqsubseteq_p}
  N'\langle u'\rangle
}.
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
