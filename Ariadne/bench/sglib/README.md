# sglib (vendored)

Unmodified files from https://github.com/Marian-Vittek/sglib at commit
`cf92b44ed84deb03412b92d3586e61dc971eeb82` (2023-10-05), MIT license
(`LICENSE`).

| File | Upstream path | SHA-256 |
|------|---------------|---------|
| `sglib.h` | `sglib.h` | `d2d10e60c1eb6b73c12bb34148739493a99b3b7590f57a6beff756f333647a36` |
| `LICENSE` | `LICENSE` | `2966d5d17b0a308e00ac20f3ef2d944cc73d2d474320ee7902b2b9323bb75a5f` |
| `dllist.c` | `samples/dllist.c` | `91afc4bb0e2becb23cf99b728723f8f2468aaa8e2156452e4b48204122023dd8` |
| `selftest.c` | `samples/selftest.c` | `79dcfe9beeec96a695c22faa831690543ebdb729ea5653cd5bbfcea9ed271707` |
| `rbtree.c` | `samples/rbtree.c` | `54cacc23380f789d75a4fd681ef6387e1d4100518735c617c486c4976f2196b6` |

`selftest.c` is sglib's self-test: it calls every documented function
and macro and checks the results with `assert`.  `../selftest/` builds
and runs it with a fixed seed under the sanitizers.  `rbtree.c` is the
red-black tree sample, vendored with it for the RB-tree benchmark.
