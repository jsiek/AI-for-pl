# Dynamic gradual guarantee via Nu-term imprecision

## Checked definition boundary

The compiler monotonicity theorem produces `QuotientedTermImprecision`, and
the public DGG statement uses that same relation. The relation has checked
source- and target-typing projections.

### Reveal and conceal provenance

The one-sided `conv↑` and `conv↓` rules no longer accept every structural
conversion. They use `RevealConversion` and `ConcealConversion`. Each
derivation records one seal name `α` and one sealed type `C`, and permits
exactly:

- identity at variables and atomic types;
- unseal or seal at `α` and `C`;
- contravariant conceal/reveal through arrows;
- the corresponding shifted provenance beneath `∀`.

In nominal notation, the essential clauses are

\[
\begin{aligned}
  \mathsf{reveal}_{\alpha,C}(\alpha) &= \mathsf{unseal}\;\alpha\;C,\\
  \mathsf{reveal}_{\alpha,C}(X) &= \mathsf{id}\;X,\\
  \mathsf{reveal}_{\alpha,C}(A\to B)
    &= \mathsf{conceal}_{\alpha,C}(A)
       \to \mathsf{reveal}_{\alpha,C}(B),\\
  \mathsf{reveal}_{\alpha,C}(\forall X.A)
    &= \forall X.\mathsf{reveal}_{\alpha,C}(A),
\end{aligned}
\]

with the dual clauses for conceal. The mechanized `∀` clause shifts the
de Bruijn name and sealed type.

Atomic identity deliberately remains legal when its *current* variable name
equals the recorded seal name. This is required after opening a binder: a
variable that was distinct from the seal before opening can collide with it,
but the coercion must remain `id`.

The checked renaming theorems are

\[
\begin{aligned}
  \mathsf{renameReveal}&:
    \mathsf{RevealConversion}(\mu,\alpha,C,c,A,B)
    \Longrightarrow
    \mathsf{RevealConversion}(\nu,\rho\alpha,\rho C,
      \rho c,\rho A,\rho B),\\
  \mathsf{renameConceal}&:
    \mathsf{ConcealConversion}(\mu,\alpha,C,c,A,B)
    \Longrightarrow
    \mathsf{ConcealConversion}(\nu,\rho\alpha,\rho C,
      \rho c,\rho A,\rho B),
\end{aligned}
\]

assuming the type renaming and mode renaming are well formed. Their
single-variable opening corollaries are `open-reveal-conversion` and
`open-conceal-conversion`.

### Paired conversions

The quotiented relation has a paired-conversion judgment

\[
  \mathsf{PairedConversion}
    (\Phi,\Delta_L,\Delta_R,\rho,c,c',p,q),
\]

where `p` relates the input types and `q` relates the output types. A paired
reveal or conceal must refer to one `StoreCorresponds` witness. The witness
may come from a physical `store-matched` entry or a correspondence-only link
when the two stores allocated permuted binders in different orders. The
generic term rule is

\[
  \frac{M \sqsubseteq_p M' \qquad c \mathrel{\sim_{p,q}} c'}
       {M\langle c\rangle \sqsubseteq_q M'\langle c'\rangle}.
\]

The old special states that combined runtime-bullet instantiation and reveal
casts have been removed. Matched allocation now produces a bare `α⊑αᵀ`
derivation and then applies the paired-conversion rule. Left-only allocation
produces `α⊑ᵀ` and then applies the one-sided reveal rule.

### Right-only lifting

Right-only `ν` and `ν ★` states use a repaired context transformation:

\[
\begin{aligned}
  \Uparrow_R(X\mathrel{\sqsubseteq}\star)
    &= X\mathrel{\sqsubseteq}\star,\\
  \Uparrow_R(X\mathrel{\sqsubseteq}Y)
    &= X\mathrel{\sqsubseteq}(Y+1).
\end{aligned}
\]

Thus right-only lifting uses `⇑ᴿᵢ Φ`, with no invented fresh assumption.
The checked theorem `⊑-target-lift-rightᵢ` states

\[
  \Phi;\Delta_L;\Delta_R\vdash A\sqsubseteq B
  \Longrightarrow
  \Uparrow_R\Phi;\Delta_L;\Delta_R+1
    \vdash A\sqsubseteq\uparrow B.
\]

The former rule used `(0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ`: it incremented the target context,
shifted the source assumptions, and introduced an unrelated fresh assumption.

## Checked operational lemmas

The following allocation lemmas are checked in
`proof.Catchup.Simulation.NuImprecisionSimulation`:

- `matched-ν↑-allocation`;
- `left-ν↑-allocation`;
- `matched-νcast-allocation`;
- `left-νcast-allocation`.

The first two handle reveal conversions. The last two restore the `ν ★`
path produced by `β-inst`. The matched `ν ★` proof applies the target
widening first and the source widening second. It derives the intermediate
bridge

\[
  \widehat\Phi;\Delta_L+1;\Delta_R+1
    \vdash C \sqsubseteq \uparrow B'.
\]

internally by embedding the target widening into indexed type imprecision and
composing it on the right of the body relation. Thus callers do not supply the
bridge, and no generic paired-widening rule is needed. The left-only proof
needs no bridge: its body derivation and lifted result relation are exactly the
input and output indices of the source widening rule.

`post-allocation-β-Λ•` checks

\[
  ((\uparrow(\Lambda X.V))\;\bullet)\langle s\rangle
    \longrightarrow V\langle s\rangle.
\]

Its proof uses `open0-ext-suc-cancelᵐ`. The module also checks
`post-β-inst`, `post-β-gen•`, `post-β-∀-reveal`, and
`post-β-∀-conceal`.

The `β-∀•` lemmas are significant. If

\[
  c : \mathsf{RevealConversion}
    (\mathsf{ext}\,\mu,\alpha+1,\uparrow C,A,B),
\]

then

\[
  c[\alpha] :
  \mathsf{RevealConversion}(\mu,\alpha,C,A[\alpha],B[\alpha]),
\]

and similarly for conceal. This is a provenance theorem, not an equation
claiming that `c[α]` is a freshly recomputed `reveal`.

The indexed opening theorem `⊑-open∀ᵢ` states

\[
  \frac{
    (\alpha\sqsubseteq\beta)\in\Phi
    \qquad
    (0\sqsubseteq0)::\Uparrow\Phi;
      \Delta_L+1;\Delta_R+1\vdash A\sqsubseteq B
  }{
    \Phi;\Delta_L;\Delta_R
      \vdash A[\alpha]\sqsubseteq B[\beta]
  }.
\]

`paired-β-∀-reveal` and `paired-β-∀-conceal` combine this theorem with
conversion opening. They check both `β-∀•` steps and reconstruct
`PairedConversion` for the opened coercions and opened input/output indices.

## Trace evidence

`NuExamplesFresh` records full rule-name traces for the polymorphic identity
pair.

| Program | Reduction-rule sequence | Result |
|---|---|---|
| `polyIdNat-app` | allocation, `β-Λ•`, `β-↦`, term β, seal/unseal | `7` |
| `polyIdDyn-app` | allocation, `β-Λ•`, `β-seq`, `β-id`, `β-↦`, term β, seal/unseal | tagged `7` |
| `tag-mismatch` | `β-seq`, `β-id`, failed tag/untag | blame |

The two related executions are not lockstep. Tag-side administrative casts
add steps before the executions rejoin.

The checked `program-via-D` and `program-via-E` traces in
`proof.EndpointMLB.Core.MLBRouteOperationalExperiment` show a stronger difference. One route
performs `β-inst`, a nested allocation, and then an outer allocation; the
other performs the outer allocation before `β-inst` and the nested
allocation. A simulation must tolerate differently ordered allocations under
casts and `ν`.

`ReductionTrace` is the reusable rule-name view of evaluator traces.

## Simulation-up-to boundary

The checked facts support an administrative up-to closure containing
`β-Λ•`, `β-∀•`, `β-gen•`, `β-id`, and `β-seq`. These rules expose
or reassociate compiled casts without term substitution or an observable tag
decision.

The closure should initially exclude:

- `β-↦` and term β, which need application and substitution invariants;
- `β-inst` together with `ν ★` allocation, because allocation changes the
  store and therefore belongs in the separate allocation closure already
  checked by `matched-νcast-allocation` and `left-νcast-allocation`;
- tag/untag, which may produce a value or blame;
- seal/unseal, until store-name coherence is explicit at that proof point.

The closure itself has not been added. Its soundness theorem is the useful
proof target.

## Next proof boundary

The two earlier focused obligations are discharged. The next boundary is at
the term-relation level: use `paired-β-∀-reveal` and
`paired-β-∀-conceal` after exposing the bare relation between `V •` and
`V′ •`, then include that reconstruction in the administrative up-to
soundness theorem. The adjacent `β-gen•` case must transport the narrowing
coercion around this opened paired conversion. This work no longer requires a
change to reveal/conceal or indexed type-imprecision.
