# Compositional quotient design

This note records the quotient-relation prototype in
`proof.Quotient.NuImprecisionCompositionalQuotientDef`.  It is deliberately
separate from the live relation in `QuotientedTermImprecision`: the examples
should expose an inadequate rule before the DGG proof depends on it.

## Problem with the current presentation

The current quotient relation combines two different ideas:

1. two casts may pass through different but `∀`-permuted intermediate types;
2. quotient-related terms may occur inside larger terms.

The paired-downcast rules implement the first idea.  The application rules
partially implement the second, but only when the function is already
quotient-related and the argument starts from ordinary imprecision before one
new pair of downcasts.  They cannot directly consume a quotient-related
argument, so a second function cast exposes the same missing case again:

$$
\begin{aligned}
  ((V\langle c_1\mapsto d_1\rangle)
       \langle c_2\mapsto d_2\rangle)\,W
  &\longrightarrow
  ((V\langle c_1\mapsto d_1\rangle)
       (W\langle c_2\rangle))\langle d_2\rangle\\
  &\longrightarrow
  (V((W\langle c_2\rangle)\langle c_1\rangle))
       \langle d_1\rangle\langle d_2\rangle .
\end{aligned}
$$

Adding another rule for exactly two downcasts and two upcasts would merely
move this boundary to three casts.

## Finite narrowing spines

The prototype first isolates the repeated structure.  A judgment

$$
  \mathsf{NarrowingSpine}\;\Delta\;\Sigma\;
  M\;A\;N\;B\;s
$$

states that `N` is obtained from `M` by one or more narrowing casts, starting
at `A`, ending at `B`, and having total imprecision shape `s`.

The first cast forms a spine:

$$
  M : A
  \quad
  d : A \mathbin{\trianglerighteq} B
  \quad
  \mathsf{shape}(d)=s
  \quad\Longrightarrow\quad
  \mathsf{NarrowingSpine}\;M\;A\;(M\langle d\rangle)\;B\;s .
$$

A cast extends a spine when its shape composes with the accumulated shape:

$$
  \begin{aligned}
  &\mathsf{NarrowingSpine}\;M\;A\;N\;B\;s,\\
  &d : B \mathbin{\trianglerighteq} C,\qquad
    \mathsf{shape}(d)=t,\qquad t;s \simeq u
  \end{aligned}
  \quad\Longrightarrow\quad
  \mathsf{NarrowingSpine}\;M\;A\;(N\langle d\rangle)\;C\;u .
$$

Thus one quotient boundary square accounts for the total shapes of both
spines, independent of their lengths.

## Graded quotient term imprecision

The prototype quotient judgment has a form index:

$$
  \Phi;\Delta_L;\Delta_R;\rho;\gamma
  \vdash^{\,c}_{g}
  M \sqsubseteq M' : A \sqsubseteq^p A' \triangleright q ,
$$

where

$$
  g ::= \mathsf{cast\text{-}spine}\mid\mathsf{application}.
$$

There are three central rules.

Ordinary imprecision embeds at the exact quotient index:

$$
  M \sqsubseteq M' : A \sqsubseteq A' \triangleright p
  \quad\Longrightarrow\quad
  M \sqsubseteq^{p}_{\mathsf{cast\text{-}spine}} M'
  : A \sqsubseteq^p A'
  \triangleright
  [\mathsf{refl},p,\mathsf{refl}] .
$$

Paired finite narrowing spines introduce a quotient boundary:

$$
  \begin{aligned}
  &M \sqsubseteq M' : A \sqsubseteq A' \triangleright p,\\
  &\mathsf{NarrowingSpine}\;M\;A\;N\;D\;s,\\
  &\mathsf{NarrowingSpine}\;M'\;A'\;N'\;D'\;s',\\
  &s;\lfloor p\rfloor \simeq^p q;s'
  \end{aligned}
  \quad\Longrightarrow\quad
  N \sqsubseteq^{p}_{\mathsf{cast\text{-}spine}} N'
  : D \sqsubseteq^p D' \triangleright q .
$$

Application is symmetric in its premises:

$$
  \begin{aligned}
  &L \sqsubseteq^p L'
    : C\to B \sqsubseteq^p C'\to B' \triangleright q_C\to q_B,\\
  &M \sqsubseteq^p M'
    : C \sqsubseteq^p C' \triangleright q_C
  \end{aligned}
  \quad\Longrightarrow\quad
  L\,M \sqsubseteq^p_{\mathsf{application}} L'\,M'
  : B \sqsubseteq^p B' \triangleright q_B .
$$

In particular, the argument may itself be an application derivation or an
arbitrarily long paired narrowing spine.

The grade prevents this new congruence from silently entering existing
value-only proofs.  The prototype checks:

$$
  M \sqsubseteq^p_{\mathsf{application}} M'
  \quad\Longrightarrow\quad
  \neg\mathsf{Value}(M)
  \quad\text{and}\quad
  \neg\mathsf{Value}(M').
$$

A cast-spine leaf may still contain an ordinary application, but inversion
then returns to the existing ordinary relation instead of exposing a new
quotient application case.

## Closing the quotient

A quotient-closing widening retains two independent facts:

1. its quotient boundary square;
2. hereditary compatibility after transporting the widening shapes through
   the chosen quotient representatives.

The second fact is represented by
`QuotientWideningCompatible`.  It does not pretend that a nontrivial quotient
index is an ordinary imprecision derivation.  Instead, if

$$
  q=[D\approx_{\forall}C,\;r,\;C'\approx_{\forall}D'],
$$

then it transports the two widening shapes to the representatives and stores
ordinary hereditary compatibility at `r`.

After the first quotient-closing widening, further paired casts use the
ordinary structured relation.  Consequently the two-function-cast residual
is derived by four reusable steps:

$$
\begin{aligned}
  &(W\langle c_2\rangle)\langle c_1\rangle
       \sqsubseteq^p
    (W'\langle c'_2\rangle)\langle c'_1\rangle,\\
  &V((W\langle c_2\rangle)\langle c_1\rangle)
       \sqsubseteq^p
    V'((W'\langle c'_2\rangle)\langle c'_1\rangle),\\
  &(V((W\langle c_2\rangle)\langle c_1\rangle))
       \langle d_1\rangle
       \sqsubseteq
    (V'((W'\langle c'_2\rangle)\langle c'_1\rangle))
       \langle d'_1\rangle,\\
  &((V((W\langle c_2\rangle)\langle c_1\rangle))
       \langle d_1\rangle)\langle d_2\rangle
       \sqsubseteq
    ((V'((W'\langle c'_2\rangle)\langle c'_1\rangle))
       \langle d'_1\rangle)\langle d'_2\rangle .
\end{aligned}
$$

The last derivation is checked by `two-function-cast-residual`.

## Checked examples

`proof.Quotient.NuImprecisionCompositionalQuotientExamples` checks:

- exact ordinary embedding;
- left-nested application, where an application result is used as a function;
- right-nested application, where an application result is used as an
  argument;
- closing an application-derived quotient term with a widening;
- one paired downcast through the incomparable `D` and `E` lower bounds;
- two paired downcasts through the same nontrivial quotient boundary;
- a quotient-related function consuming that two-cast quotient argument;
- closing the nontrivial `E ≈∀ D` quotient through transported
  representative widening shapes;
- the full residual shape after two successive function-cast reductions.

Run the focused suite with:

```text
make quotient-design-check
```

## Remaining design obligation

The finite-spine rule starts from an ordinary term-imprecision leaf.  It
handles the repeated function-cast family above, but it does not yet place a
new narrowing spine around an arbitrary quotient application.  Supporting
that operation requires a quotient-to-quotient cast square with permutation
transport at both endpoints.

Before replacing the live relation, the next checkpoint is therefore:

1. prove typing projections for both prototype judgments;
2. restate the terminal/value inversion lemmas using the form index;
3. decide whether DGG reduction ever needs a narrowing spine around an
   application-derived quotient term;
4. if it does, define and test the two-sided quotient cast square;
5. derive the existing one-cast application rules and
   `down·up⊑down·upᵀ` from the compositional presentation.
