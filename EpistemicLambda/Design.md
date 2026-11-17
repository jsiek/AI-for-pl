# Epistemic Semantics for Lambda Calculus with Mutable References

## 1. Running example first

The repository's `STLCRef` has natural numbers rather than Booleans. Represent
`false` by `0`, `true` by `1`, and define a toggle on those two states by

```text
flip = lambda n:nat. case n [zero => 1 | suc => 0]
```

Write `let x = M in N` for `(lambda x:A. N) M` and write sequencing
`M; N` for `let z = M in N` when `M : unit` and `z` is not free in `N`.
The typed version of the running example is:

```text
e1 = let x = ref(1) in
       lambda y:unit. x := flip(!x); !x

e2 = let x = ref(0) in
       lambda y:unit. x := flip(!x); flip(!x)
```

Both terms have type `unit => nat`. Assignment returns `unit` in `STLCRef`, so
the sequencing abbreviation applies directly.

Let the fresh locations allocated by the two evaluations be `k1` and `k2`.
After evaluating the outer `let`s, the configurations differ internally:

```text
e1:  <lambda y. k1 := flip(!k1); !k1,      [k1 |-> 1]>
e2:  <lambda y. k2 := flip(!k2); flip(!k2), [k2 |-> 0]>
```

The context has the two returned functions, but it has neither `k1` nor `k2`.
Calling either function repeatedly produces the same public trace:

```text
context action       e1 result / hidden cell       e2 result / hidden cell
--------------------------------------------------------------------------
call unit            0 / 0                         0 / 1
call unit            1 / 1                         1 / 0
call unit            0 / 0                         0 / 1
...
```

The heap contents never agree. What agrees is every interaction available to
the context. A semantics that makes all heap propositions public therefore
distinguishes too much.

The desired relation pairs the two hidden states by phase:

```text
R0 = ([k1 |-> 1], f1)  ~  ([k2 |-> 0], f2)
             | call unit                 | call unit
             v                           v
R1 = ([k1 |-> 0], f1)  ~  ([k2 |-> 1], f2)   output 0
             | call unit                 | call unit
             v                           v
R0 = ([k1 |-> 1], f1)  ~  ([k2 |-> 0], f2)   output 1
```

This example rules out both raw state-transformer equality and any proposal
that merely renames fresh locations: renaming can pair `k1` with `k2`, but it
cannot turn `1` into `0`. The relation must hide, or relationally
interpret, the contents of private cells.

## 2. Source calculus

The source language is the mechanized `STLCRef` calculus. In expository syntax,
its types and terms are:

$$
\begin{aligned}
A,B &::= \mathsf{nat} \mid \mathsf{unit} \mid A \Rightarrow B
       \mid \mathsf{ref}\;A \\
M,N &::= x \mid \lambda x:A.M \mid M\;N \mid 0 \mid \mathsf{suc}\;M \\
    &\quad\mid \mathsf{case}\;M\;[\mathsf{zero}\Rightarrow N
       \mid \mathsf{suc}\Rightarrow N'] \\
    &\quad\mid \mathsf{unit} \mid \mathsf{ref}\;M \mid {!M}
       \mid M := N \mid \mathsf{loc}\;k.
\end{aligned}
$$

Source programs never contain `loc k`; locations arise only at runtime. A
store is a finite list of terms, and the store typing assigns a type to each
location. The public development defines typing

$$
\Gamma \mid \Sigma \vdash M : A
$$

and deterministic small-step reduction on configurations

$$
(M,\mu) \longrightarrow (N,\mu').
$$

The dynamic rules allocate at `length mu`, read by list lookup, and update by
list position. Values are lambdas, numerals, `unit`, and locations. Assignment
returns `unit`.

For a closed, well-typed ground program, define its observation to be:

- `returns n` if a `nat` program terminates at numeral `n`;
- `returns unit` if a `unit` program terminates;
- `diverges` if it has an infinite reduction sequence.

Type safety rules out stuck closed programs. General references still permit
divergence without a recursive term constructor. For example, allocate
`r : ref (unit => unit)`, assign `lambda u. (!r) u` to `r`, and then call
`(!r) unit`.

For closed terms `M,N : A`, define `M ≃ctx N` if every well-typed closing
context `C` whose result type is `nat` or `unit` gives `C[M]` and `C[N]` the
same observation. Thus exact natural-number results, termination at `unit`,
and termination versus divergence are observable. Heap size, allocation time,
and the numeric representation of a location are not observations.

## 3. What transfers from *Logics for Epistemic Programs*

Baltag and Moss separate four semantic objects:

1. A **state model** has states, an accessibility relation for each agent, and
   a valuation of objective atoms.
2. An **epistemic proposition** selects a set of states in every state model.
3. An **action model** has simple actions, agent-indexed accessibility between
   actions, and a precondition for each action.
4. A **program model** designates one or more actions in an action model.

Here an **objective atom** is just a primitive yes/no fact attached to a
world. It is called objective to distinguish the fact itself from facts about
the observer's knowledge. In the paper's coin example, `heads` is an objective
atom. At a world where the coin is heads, `heads` is true whether or not the
observer knows it. The formula `K heads` is different: it is true only if
`heads` holds at every world the observer considers possible.

For `STLCRef`, tempting atoms include:

```text
returned(0)       the current boundary result is 0
returned(unit)    the current boundary result is unit
cell(k,0)         location k currently contains 0
has-key(k)        the observer has received location k
```

The choice matters because ordinary Kripke bisimulation requires related
worlds to agree on every objective atom, even on atoms the observer does not
know. In the running example, the actual left world satisfies `cell(k1,1)` and
the actual right world satisfies `cell(k2,0)`. If raw facts about private cells
are atoms, the two initial worlds fail the atomic clause of bisimulation before
we even consider their matching call behavior.

Our provisional choice is therefore a small, capability-sensitive atom
vocabulary indexed by the current public interface `K`:

- ground results at the public boundary;
- possession of keys that have crossed the boundary;
- `cell(k,n)` only when `k` belongs to `K`, meaning that the observer possesses
  that key.

Function behavior and divergence are not one-step atoms. They are observed by
interaction: call the function and see whether it returns, what ground result
it returns, and which new capability it discloses. An equivalent and perhaps
cleaner formalization is to put these observations on transition labels and
use no separate atoms beyond terminal ground results. Milestones 1 and 2 will
compare these two presentations.

The update product pairs a possible input state `w` with a possible action
`a`, provided `w` satisfies the precondition of `a`. Accessibility in the
updated model is the pointwise product of state accessibility and action
accessibility. A program model induces both an updated state model and a
relation connecting before-states to after-states.

Three ideas are especially relevant here:

- **Programs denote structured updates, not bare state functions.** This leaves
  room to record what an observer can and cannot distinguish about an action.
- **Possible state and possible action are combined by product update.** This
  resembles composing uncertainty about a private heap with uncertainty about
  a computation performed on it.
- **Bisimulation is the semantic equality candidate.** In the paper,
  bisimulation agrees on atoms and matches every accessible alternative in
  both directions; suitable updates preserve it.

The paper's action models are nevertheless not immediately a semantics of
mutable references. Their update product inherits the old valuation: a
successful action changes information but not objective facts. Assignment is
an *ontic* change. We need a fact-changing heap transition. The provisional
design uses action postconditions for mutation and a separate nominal
world-extension operation for allocation.

## 4. Proposed epistemic interaction model

Treat the surrounding program as the distinguished observer `O`. A pointed
world contains at least

$$
w = (s, r, K),
$$

where `s` is the finite heap, `r` is the value currently exposed at the
boundary, and `K` is the finite set of location keys disclosed to `O`.
Locations reached by dereferencing disclosed keys must be included as
observable; this is essential because keys can themselves be stored in cells.
A returned function is instead an opaque callable handle. Its captured
locations do not become observable merely because they occur in its closure;
only the results of calling it can disclose further keys.

An action model for computation should contain:

$$
A=(E,\approx_O,\mathit{pre},\mathit{post},\mathit{out}).
$$

- `E` is a set of possible computational events.
- `a approx_O a'` means that the observer cannot distinguish which event
  occurred from the public interaction so far.
- `pre(a)` says when the event may run.
- `post(a,w)` produces the new heap for ordinary mutations. In the provisional
  design, fresh allocation is factored through nominal world extension as
  explained in Section 10.
- `out(a,w)` describes the boundary observation: natural-number or unit
  result, disclosed key, or returned function handle. Divergence is the
  absence of a finite return after an interaction, not a single event.

The fact-changing product update has worlds

$$
W \otimes A
= \{(w,a) \mid w \models \mathit{pre}(a)\},
$$

with objective atoms evaluated in `post(a,w)`, not copied from `w`. Its
observer accessibility is

$$
(w,a) \sim_O (w',a')
\quad\text{if}\quad
w \sim_O w',\; a \approx_O a',
\text{ and their boundary observations agree}.
$$

Nominal allocation extends the disclosed-name interface only when the new key
escapes. For

```text
let x = ref(0) in lambda y:unit. ...x...
```

the key for `x` supports the returned closure internally but is not added to
`K`. For

```text
ref(0)
```

the result is the key itself, so the new key is added to `K`; subsequent
dereference and assignment are actions available to the observer.

This is not yet a compositional denotation of lambda terms. It is the target
shape for an operational epistemic model from which to discover the right
notion of morphism and composition.

## 5. Why accessibility cannot be defined by raw visible heaps alone

Suppose `K` contains a returned function but no locations. A projection that
simply deletes heap cells not reachable by following syntactic keys makes both
heaps in the running example look empty. That correctly hides the initial bit,
but it says nothing about what happens when the function is called.

The observer's indistinguishability must therefore be interactive and
higher-order:

- related natural numbers are equal, and `unit` is related to `unit`;
- related public keys permit related reads and writes;
- related functions turn related arguments and related private worlds into
  related results and successor worlds;
- freshly disclosed keys extend the relation between worlds.

This is close to a Kripke logical relation parameterized by a relation between
heaps, and also close to environmental bisimulation or game semantics. The
epistemic reading is that a world relation specifies which private
implementations remain possible after each public interaction.

For the running example, the world relation contains

```text
([k1 |-> 1], [k2 |-> 0])
([k1 |-> 0], [k2 |-> 1])
```

and relates the two closures. A call in either related world returns the same
natural number and moves to the other related world. No atom mentioning the
private contents is admissible at the public interface.

## 6. Three candidate designs, tested on the example

### Candidate A. Capability-indexed epistemic bisimulation

Worlds are heaps plus disclosed capabilities. Within one model, observer
accessibility connects the implementations compatible with the observer's
history. Across two pointed models, bisimulation is the greatest relation that
matches every interaction available through the disclosed capabilities.

On `e1` and `e2`, the inaccessible cells may contain opposite bits, while the
two closure-call events match and return equal naturals. Thus the two pointed
models are bisimilar.

This is the best first experiment: it stays close to the paper, makes the
observer and hidden information explicit, and can initially be defined from a
labeled transition system.

Risk: if accessibility is defined as contextual indistinguishability, full
abstraction becomes circular. It must instead have a syntax-independent,
coinductive definition with a separately proved definability theorem.

### Candidate B. Nominal possible worlds plus a Kripke logical relation

World extension allocates fresh related locations, and a world records a
partial correspondence between the two heaps together with a relation on the
contents of paired cells.

On `e1` and `e2`, the world pairs `k1` with `k2` and assigns the private cell
the invariant `left bit = flip(right bit)`. The functions preserve this
invariant and return equal results.

This directly expresses the example and fits the unforgeability of keys.
However, it usually yields a proof technique for contextual equivalence before
it yields a canonical denotational equality.

### Candidate C. Nominal game semantics

The context and term are Opponent and Player. Calls, returns, reads, writes,
and fresh-name disclosures form plays; private store operations do not appear
as independent public moves.

On `e1` and `e2`, both strategies expose exactly the trace

```text
call unit, 0, call unit, 1, call unit, 0, ...
```

while the complementary private bits remain internal. Hence the strategies
agree even though the raw store transformers do not.

This route has the strongest precedent for full abstraction with general
references, but it imports substantially more machinery. It should be the
comparison target and possible eventual denotational model, not the first
formalization step.

## 7. Conjectured theorem shape

Let `I(e)` be the pointed epistemic interaction model generated by a closed
term `e`, and let `approx_epi` be its capability-respecting bisimilarity. The
target theorem is

$$
I(e_1) \approx_{epi} I(e_2)
\quad\text{if and only if}\quad
e_1 \simeq_{ctx} e_2.
$$

The two directions should be separated:

- **Soundness:** if `I(e1) approx_epi I(e2)` then every closing context has the
  same ground result or divergence. This should follow from
  congruence/compositionality plus adequacy.
- **Completeness:** if every closing context has the same observation then the
  interaction models are bisimilar. This requires showing that every semantic
  distinction can be implemented by a context, or choosing a quotient/model
  whose distinctions are already definable.

The second direction is where higher-order store, fresh names, and the choice
of admissible atoms become decisive.

## 8. Proposed research sequence

### Milestone 1. Ground store, first-order boundary

Restrict cells to natural numbers and returned values to natural numbers,
`unit`, or keys. Define a typed, small-step labeled transition system where
labels are the observer's legal operations. Define capability-indexed
bisimulation and prove fresh-name and private-garbage equivalences.

**Status (2026-09-14): complete for the stated first-order boundary.** The
Agda development in [`agda/`](agda/README.md) uses these concrete defaults:

- source evaluation and allocation are silent and are summarized before the
  observer boundary;
- public labels are exact natural-number return, `unit` return, key return,
  read, and write;
- concrete location numbers never occur in labels;
- `KeyCorrespondence` relates the one disclosed source key to the one
  disclosed target key, even when their numeric locations differ; and
- bisimulation is termination-sensitive and matches every public action in
  both directions.

For example, the correspondence maps location `0` in store `[0]` to location
`1` in store `[0, 0]`. A read through either public key returns `0`; after the
observer writes `7` through both keys, a read through either returns `7`.
Thus the location names and the extra private cell are invisible, while the
behavior available through the disclosed keys agrees.

The checked examples establish:

1. `let x = ref 0 in unit` is bisimilar to `unit`;
2. allocating the same public cell at different numeric addresses is
   bisimilar through `KeyCorrespondence`;
3. the correspondence survives arbitrary matching writes;
4. returning `0` is not bisimilar to returning `1`; and
5. returning `unit` is not bisimilar to the abstract divergent state.

The final example deliberately uses an abstract divergent observer state.
Connecting a particular infinite `STLCRef` reduction to that state requires a
coinductive divergence predicate and is separate from the finite multistep
execution relation currently imported from `STLCRef`. Multiple disclosed keys
and returned functions remain Milestones 2 and 3.

### Milestone 2. Returned functions with private natural-number cells

Add function handles and `call`/`return` labels. Prove the exact `e1`/`e2`
example by a two-state coinductive relation. This is the first point where a
purely heap-projection account fails and interaction becomes necessary.

### Milestone 3. General references and key disclosure

Allow cells to contain functions and keys. Add nominal world extension and
operational reachability through disclosed keys. Keep functions opaque except
for calls. Test aliasing, private-key escape, storing a private key in a public
cell, and callbacks that re-enter the term.

### Milestone 4. Product-update presentation

Factor the transition model into epistemic state models and fact-changing
action models. Prove that product update preserves the chosen bisimulation.
Only keep the epistemic formulation if this factorization clarifies
composition or proof.

### Milestone 5. Full abstraction

Prove adequacy and congruence first. Then attempt definability/completeness for
`STLCRef`. If direct definability fails, compare the model against nominal game
semantics and identify the extra semantic observations that must be quotiented
away.

## 9. Immediate test suite

Every proposed semantics should decide these concrete pairs correctly:

1. **Fresh-name irrelevance:** `ref(0)` is unchanged by the particular fresh
   address chosen, up to renaming of disclosed keys.
2. **Hidden initialization:** the running `e1` and `e2` are equivalent.
3. **Key escape breaks hiding:** `let x = ref(0) in x` exposes the cell, so a
   context can read and overwrite it.
4. **Aliasing is observable:** compare these terms of type
   `nat => ref nat`:

   ```text
   same = let x = ref(0) in lambda n:nat. x

   separate = let x = ref(0) in
                let y = ref(0) in
                  lambda n:nat. case n [zero => x | suc => y]
   ```

   A context calls the returned function at `0` and `1`, writes `1` through
   the first resulting key, and reads through the second. It obtains `1` from
   `same` and `0` from `separate`.
5. **Private garbage is irrelevant:** `let x = ref(0) in unit` is equivalent
   to `unit` because allocation itself is not observable.
6. **Higher-order leakage:** returning a function that later returns `x`
   eventually discloses the formerly private key.
7. **Stored callbacks:** a public operation that invokes a function stored in a
   private cell must expose only the callback interaction, not the cell itself.
8. **Divergence is observable:** `unit` differs from a closed program of type
   `unit` that stores a self-calling function in a reference and invokes it.

## 10. Resolved choices and fresh allocation

The current design choices are:

- use the mechanized, typed `STLCRef` language;
- observe exact natural-number results, termination at `unit`, and divergence;
- do not observe allocation count, allocation timing, or numeric addresses;
- use one observer, representing the surrounding program context;
- initially use only boundary and possessed-capability atoms, or equivalently
  put those observations on interaction labels.

The remaining representation issue about allocation is where to perform the
operation that creates a fresh key.

Consider evaluating `ref(0)`. In the current operational semantics, a heap of
length three allocates numeric location `3`. A denotational event cannot simply
say "allocate location 3," because the same event run in a heap of length ten
needs a different location. More importantly, the numbers `3` and `10` are not
observable identities. A context can test aliasing by using the keys, but it
cannot inspect their numeric representation.

There are two possible semantic organizations.

### Allocation inside action postconditions

Give the allocation event a world-dependent postcondition:

$$
\mathit{post}(\mathsf{alloc}\;0,w)
= w[k \mapsto 0]
\quad\text{where }k\text{ is fresh for }w.
$$

The action model itself then performs both heap change and information change.
To compose two allocations, the second postcondition runs on the world
produced by the first. This is compact, but `k` is not a canonical choice. The
whole construction must be equivariant and quotient worlds by permutations of
fresh locations. Otherwise two implementations that choose different fresh
numbers have different denotations.

On `let x = ref(0) in unit`, this approach first creates a world containing a
new cell and then must quotient that private, unreachable cell away to obtain
the same denotation as `unit`.

### Allocation as nominal world extension

Separate state evolution from epistemic update. A nominal world-extension
operation produces

$$
w \mathbin{\oplus} (k \mapsto 0)
$$

for an arbitrary fresh `k`, with all fresh choices identified up to location
permutation. The epistemic action then records whether the key crosses the
boundary:

- in `let x = ref(0) in unit`, `k` stays private and the new cell is
  observational garbage;
- in `ref(0)`, `k` is returned, so the observer's capability interface grows
  with a new abstract key.

The provisional choice is the second organization. We can reuse `STLCRef`'s
existing reduction to compute concrete heap changes, then abstract numeric
locations using a partial correspondence between heaps. The epistemic layer
tracks only the observer's uncertainty and capability disclosure. This keeps
fresh-name generation out of the first product-update definition and directly
enforces the decision that allocation count and timing are unobservable.

Assignment remains an ordinary heap transition. For example, if the observer
possesses `k`, the transition for `k := 1` changes the related heaps at the
locations represented by `k`; the epistemic layer records that the observer
can subsequently establish the atom `cell(k,1)` by dereferencing it.

## 11. Sources and nearby semantic precedents

- Alexandru Baltag and Lawrence S. Moss,
  [*Logics for Epistemic Programs*](https://link.springer.com/article/10.1023/B%3ASYNT.0000024912.56773.5e),
  *Synthese* 139, 165--224, 2004. The present proposal borrows state models,
  action/program models, product update, and bisimulation, while adding
  fact-changing postconditions and fresh names.
- Andrew Pitts and Ian Stark,
  [*Operational Reasoning for Functions with Local State*](https://homepages.inf.ed.ac.uk/stark/operfl.html),
  1998. Its heap-relation-indexed reasoning is a close precedent for the
  relational worlds needed by the running example.
- Nikos Tzevelekos,
  [*Full Abstraction for Nominal General References*](https://arxiv.org/abs/0907.4477),
  *Logical Methods in Computer Science* 5(3), 2009. This is the main comparison
  point for fresh names, higher-order store, and full abstraction.
- Andrzej S. Murawski and Nikos Tzevelekos,
  [*Game Semantics for Good General References*](https://www.cs.ox.ac.uk/andrzej.murawski/papers/lics11.pdf),
  LICS 2011. It explains why exposing the full functional store in semantic
  interactions jeopardizes full abstraction.
