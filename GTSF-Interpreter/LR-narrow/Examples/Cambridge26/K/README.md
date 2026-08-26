# Independent-binder K examples

The K suite extends the identity-heavy Cambridge26 catalogue with the four
precision vertices

- `PolyK = ∀X. ∀Y. X → Y → X`;
- `X-dynamic-K = ∀Y. ★ → Y → ★`;
- `Y-dynamic-K = ∀X. X → ★ → X`; and
- `DynK = ★ → ★ → ★`.

`Common.agda` defines casts for each edge of this square. Consequently the
two type abstractions can be instantiated or generalized independently.

- Examples 1--5 check the four edges and diagonal of the precision lattice.
- Examples 6--9 add one-sided casted forms analogous to the identity cases.
- Examples 10--11 check separate X-only and Y-only round trips.
- Examples 12--13 reach the fully dynamic vertex in both possible orders.
- Examples 14--15 apply the partially dynamic terms. Making X dynamic makes
  K's result dynamic; making only the discarded Y argument dynamic leaves the
  result at `Nat`.
- Examples 16--17 apply the two fully dynamic cast orders.
- Examples 18--19 return from the fully dynamic vertex along both orders.
- Example 20 directly generalizes raw dynamic K to `PolyK`, without first
  descending from polymorphic K or immediately applying the result.

The raw terms `K-X-dynamic` and `K-Y-dynamic` are equal after erasing lambda
annotations. Their distinct checked endpoint types retain which binder is
dynamic. This is expected for the extrinsic `NuTerms` syntax.
