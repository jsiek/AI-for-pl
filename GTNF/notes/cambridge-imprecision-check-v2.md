# The cambridge26 pairs against the updated `⊢²`

Status: paper check, 2026-10-02.  The left program is the more precise
program.  This check uses the updated §12.2–§12.3 rules, including D13–D16,
and the simulation directions of §9.7.

| pair | forward ok? | backward ok? | decisions exercised | finding |
|---|---:|---:|---|---|
| Cf | yes | yes | D11, D12, D15, D16 | old blocks remain valid |
| Cg | yes | yes | D11, D12, D14–D16 | the right-led block now uses `∀⊑⟪+⟫` at `X⊑★` |
| Ch | yes | yes | D12, D14, D16 | the right-led P3 block uses `ϱˡ` |
| Ce | yes | yes | D11, D12, D16 | old blocks remain valid |
| C2 | yes | yes | D11, D12, D14–D16 | the right-led gen-value block and B6/B7 now follow literally |
| C5 | yes | yes | — | no world extension |
| C6 | yes | yes | D11, D12, D16 | the left allocation stays unpaired |
| C8 | yes | yes | D12, D16 | matched `TyBeta`s move a lexical pair to `ϱᵍ` |
| C10 | yes | yes | D11, D12, D16 | the left allocation stays unpaired |
| C12 | yes | yes | D11–D16 | D13 supplies two right partners |
| C13 | yes | yes | D11–D13, D15, D16 | D13 supplies two right partners |
| C14 | yes | yes | D11–D13, D15, D16 | D13 supplies three right partners |
| C16 | yes | yes | D11, D12, D15, D16 | all allocated rep. vars are left-only |
| C16b | yes | yes | D11, D12, D15, D16 | all allocated rep. vars are left-only |
| C17 | yes | yes | D11, D12, D15, D16 | two left-only allocations |
| C18 | yes | yes | D11, D12, D15, D16 | two lexical pairs become two global pairs |
| C18b | yes | yes | D11, D12, D15, D16 | two `X⊑★` names rejoin with their marks |
| C19 | yes | yes | D11, D12, D15, D16 | `βᴸ:=αᴸ` remains unpaired |
| C22 | yes | yes | D12, D16 | reflexive lexical/global transfer |
| C23a | yes | yes | D11, D12, D15, D16 | unrestricted final-world `W[δ ∥ δ′]` is necessary |
| C23b | yes | yes | D11, D12, D15, D16 | opposite boundary orders still rejoin |
| CJ | yes | yes | — | no world extension |
| M1 = C12-R `⊑` Cf-R | yes | yes | D11–D13, D15, D16 | `ϱ` is one-to-one |
| M4 = C12-R `⊑` R3 | **no** | **no** | D11–D16 in the post-`Beta` suffix | initial application components have unrelated types; the suffix keeps `ϱ` one-to-one |
| M2 = C12-R `⊑` Cg-R | yes | yes | D11–D16 | `ϱ` is one-to-one |

## Reading the blocks

`L_i` and `R_j` mean state `i` of the named rendered run, with the initial
state numbered `0`.  A schedule `(i,j)` is therefore a synchronized block
whose two terms are exactly the corresponding states in
`cambridge-traces.md`.  For M4, `E_i` is state `i` of the rendered `ex1`
run; its terms are reproduced where they matter.

For every schedule below, the outer-rule derivation and the displayed terms
are the blocks of the first check unless this note prints a replacement.
Thus a reference such as “first-check B2” points to that complete block,
including its verbatim states and outer rules; it is not a new abbreviation
for a different derivation.

The backward ledger is read as follows.  `B0–B2 ⇝ B3` says that from any
of B0, B1, or B2 the right's next single step can be followed by zero or more
steps on both sides to B3.  When adjacent blocks both advance the right, the
entry is simply `Bi ⇝ B(i+1)`.  These entries cover every right step whose
source is a related block.  Steps taken during catch-up need not themselves
end in a related configuration, exactly as §9.7 permits.

For worlds, write `aᴸ_ΛY` for the abstract rep. var bound by the left
`ΛY`, `uᴸ_νX` for the rep. var bound by the left `ν X`, and similarly
on the right.  Rendered `α`, `β`, and `γ` are store rep. vars created by
`TyBeta`; superscripts distinguish the runs.  A rule premise under matched
`Λ` or `ν` binders records its pair in `ϱˡ`.  Once matched `TyBeta`s run,
the corresponding store pair is in `ϱᵍ`.  An unmatched allocation adds no
pair.  Every listed pair satisfies D13: each right rep. var occurs in at most
one pair.  Because `ϱᵍ` only grows, a global pair first listed at Bi persists
through every later block of that pair.  Lexical pairs exist only in the
named binder premises; outside those premises `ϱˡ` is empty.  A left-only
name is always marked `X⊑★`; a right-only name has no mark constraint.

## The 22 cambridge26 pairs

### Cf

Forward blocks are first-check Cf B0–B5, with schedule
`(0,0), (1,1), (2,3), (3,5), (4,10), (5,11)`.  Their outer rules are
unchanged.

World audit: B0 has `ϱˡ = {(uᴸ_νX,uᴿ_νX)}` in the `ν⊑ν` premise; the
left `ΛY` is one-sided.  At B1 the matched `TyBeta`s replace that relevant
lexical alignment by `ϱᵍ = {(αᴸ:=ℕ,αᴿ:=ℕ)}`.  The boundary name is
both-sided at `X⊑★`; each right-only `−X` premise leaves it left-only at
that same mark, and `+X` rejoins through the global pair.  B4's final interior
world has no name.  Names name paired rep. vars, `ℕ ⊑ ℕ`, and no right rep.
var has two left partners.  D15 makes every multi-entry premise well formed
without inspecting transient entry prefixes.

Backward: `B0 ⇝ B1 ⇝ B2 ⇝ B3 ⇝ B4 ⇝ B5`.  No extra block is
needed.

### Cg

The left-led forward blocks remain first-check Cg B0–B5, with schedule
`(0,0), (1,2), (2,6), (3,8), (4,13), (5,16)`.  The updated rules also make
the formerly failing right-led block derivable:

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   [X0] ·⊑·, ν⊑, ⊑cast, ∀⊑⟪+⟫ at mark X⊑★;
   the premise uses ⊑cast and ⊑⟪⟫ for the right's −X.
```

In X0, the shared name is the left `ΛY` name and the right boundary `X`,
both-sided at `X⊑★`.  The pair is
`ϱˡ = {(aᴸ_ΛY,αᴿ:=★)}`: the left member is abstract and the right
member has representation `★`, exactly the second well-formedness clause of
§12.2.  The left-only `ν X:=ℕ` rep. var is unpaired.  After the left
`TyBeta`, X0's lexical pair becomes
`ϱᵍ = {(αᴸ:=ℕ,αᴿ:=★)}` in B1.  B1–B4 retain the `X⊑★`
mark through every unbind and rejoin.  All final interior worlds satisfy
`ℕ ⊑ ★` and D13.

Backward from the main schedule is `B0 ⇝ B1 ⇝ B2 ⇝ B3 ⇝ B4 ⇝ B5`.
Alternatively, after B0's right `Inst`, the right may finish `TyBeta` to X0;
from X0 its `CastFun` step is followed by the left `TyBeta, Wrap` and the
right's remaining `CastId, Wrap, CastFun` to B2.  Thus D14 covers the
right-led route as well as the left-led one.

### Ch

Forward blocks are first-check Ch B0–B5, schedule
`(0,0), (1,2), (2,5), (3,6), (4,7), (5,10)`.  B0's `Λ⊑Λ` premise has
`ϱˡ = {(aᴸ_ΛY,aᴿ_ΛX)}`; the left `ν` is one-sided.  The optional
right-led `(0,2)` block is design P3's `∀⊑⟪+⟫` block and replaces the
right abstract member by `αᴿ:=★`:

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
```

There `X` is both-sided at `X⊑X` and
`ϱˡ = {(aᴸ_ΛY,αᴿ:=★)}`.  This is the D16 case that was not
type-correct when `ϱ` ranged only over stores.  At B1 the pair is global,
`{(αᴸ:=ℕ,αᴿ:=★)}`.  Names name that pair, the pair agrees by
`ℕ ⊑ ★`, and D13 holds.

Backward is `B0 ⇝ B1 ⇝ B2 ⇝ B3 ⇝ B4 ⇝ B5`; the optional
right-led block catches to B2 after its first `CastFun`.  No new rule beyond
`∀⊑⟪+⟫` is needed.

### Ce

Forward blocks are first-check Ce B0–B5, schedule
`(0,0), (1,0), (2,0), (3,1), (4,1), (5,1)`.  The left `Λ` and `ν`
binders are one-sided; hence `ϱˡ = ϱᵍ = ∅`.  After `TyBeta`, `X` is
left-only at `X⊑★` and `αᴸ:=ℕ` is unpaired.  Every final interior
world either has that left-only name or drops it, so both well-formedness
clauses and D13 hold.

Backward: `B0–B2 ⇝ B3`; the right is a value from B3 onward.

### C2

The left-led blocks remain first-check C2 B0–B11, schedule
`(0,0), (1,2), (2,5), (3,6), (4,7), (5,8), (6,9), (7,10),
(8,11), (9,12), (10,13), (11,16)`.  The updated D14 right-led block is:

```
L  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   [X0] ·⊑·, ν⊑, ⊑cast, ∀⊑⟪+⟫ for the left gen-cast ∀-value.
```

If `V = (λx:★.x)⟨gen Y.(Y!→Y?ℓ0)⟩`, then the premise is the
same gen wrapper on both sides after `inst_Y(V)`, so it follows by
`cast⊑cast` and `⟪⟫⊑⟪⟫`.  Its name is both-sided at `X⊑X`, and
`ϱˡ = {(aᴸ_genY,αᴿ:=★)}`.  After the left `TyBeta`, B1 has
`ϱᵍ = {(αᴸ:=ℕ,αᴿ:=★)}`.

C2 B6 and B7 are now literal applications of D15:

```
L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B6] the final interior world of (−X,+X) ∥ (−X,+X) is checked.

L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩) ⟨id(X)⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨id(X)⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B7] the rejoined name keeps the mark chosen at B1.
```

Only the final interior world is read.  It has one both-sided `X`, names
`(αᴸ,αᴿ)`, and is well formed; no transient left-only `X` is required to
carry a newly chosen mark.  All other blocks retain this global pair and
either keep, hide, rejoin, or drop `X` symmetrically.

Backward is adjacent throughout: `B0 ⇝ ··· ⇝ B11`.  From X0, the
right's first `CastFun` is followed by the left `TyBeta, Wrap` and right
`CastId, Wrap` to B2.

### C5

Forward blocks are first-check C5 B0–B4, schedule
`(0,0), (1,0), (2,0), (3,0), (4,1)`.  No rule enters a type binder or a
boundary, so both parts of `ϱ` and the name center are empty in every block.
Backward is `B0–B3 ⇝ B4`.

### C6

Forward blocks are first-check C6 B0–B5, schedule
`(0,0), (1,0), (2,0), (3,0), (4,0), (5,1)`.  In B0 the left `ν` and
`Λ` are one-sided, so `ϱˡ=∅`; after B0, `αᴸ:=ℕ` is an unpaired
store rep. var and `ϱᵍ=∅`.  Boundary `X` is left-only at `X⊑★` until
it is dropped.  World well-formedness is therefore immediate.  Backward is
`B0–B4 ⇝ B5`.

### C8

Forward blocks are first-check C8 B0–B5, schedule
`(0,0), (1,1), (2,2), (3,3), (4,4), (5,6)`.  B0's `ν⊑ν` and
`Λ⊑Λ` premises pair their respective binder rep. vars in `ϱˡ`.  The
matched `TyBeta`s leave only `ϱᵍ={(αᴸ:=ℕ,αᴿ:=★)}` at B1.
The sole name is both-sided at `X⊑X`; it names that pair, and the pair
agrees by `ℕ ⊑ ★`.  Both unbinds drop it.  Backward is adjacent through
B4; B4's right `IdDyn` and remaining `Id` catch to B5.

### C10

Forward blocks are first-check C10 B0–B10, schedule
`(0,0), (1,0), (2,0), (3,0), (4,0), (5,0), (6,1), (7,1),
(8,1), (9,1), (10,1)`.  The left `Λ` and the `ν` introduced by `Inst` are
one-sided.  Thus `ϱˡ=∅`; after `TyBeta`, `αᴸ:=★` is unpaired and
`ϱᵍ=∅`.  Every `X` is left-only at `X⊑★`, and each closed
multi-entry boundary has a well-formed final world.  Backward is `B0–B5 ⇝
B6`; the right is a value thereafter.

### C12

The forward schedule remains first-check C12 B0–B5,
`(0,0), (1,3), (2,4), (3,11), (4,18), (5,19)`, but B1 is now
derivable rather than conditional:

```
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩) 5)
   [B1] ·⊑·, ⟪⟫⊑⟪⟫, ⊑cast, ⊑⟪⟫, ⊑cast, ⊑⟪⟫, ƛ⊑ƛ.
```

The left `X` and right `Y` are one center name `c`, both-sided at `c⊑★`.
The inner right `+X` rejoins `c`.  The complete store relation is

```
ϱᵍ = { (αᴸ:=ℕ, βᴿ:=ℕ), (αᴸ:=ℕ, αᴿ:=★) }
ϱˡ = ∅.
```

Provenance: `αᴸ` is created when the left source `ν X:=ℕ` takes
`TyBeta`; `αᴿ` is created by the right `Inst`/`TyBeta` opening `ΛY` at
`★`; `βᴿ` is created when the right source `ν` takes `TyBeta` at `ℕ`.
Before those steps, the matching source `ν`s and the two core `Λ`s supply
the corresponding binder-local pairs in `ϱˡ`.

Both right rep. vars have the unique left partner `αᴸ`; the left rep. var
has two right partners, as D13 permits.  Both pairs agree (`ℕ⊑ℕ` and
`ℕ⊑★`), and every both-sided spelling of `c` names one of those pairs.
B2–B4 use the same `ϱᵍ`; D15 lets `c` go left-only and rejoin twice while
keeping `c⊑★`.  Their final interior worlds, not entry prefixes, are well
formed.

The useful right-led extra block is the one already printed in the first
check after the right's first `Inst, TyBeta`.  Its `ν⊑ν` premise pairs the
still-enclosing source `ν`s in `ϱˡ`, while `∀⊑⟪+⟫` adds
`(aᴸ_ΛY,αᴿ:=★)` to `ϱˡ`.  If the right then takes its source
`TyBeta` and the left takes its `TyBeta`, B1 results and both pairs become
global.  Thus backward is `B0 ⇝ B1 ⇝ B2 ⇝ B3 ⇝ B4 ⇝ B5`; the
extra block also catches to B1.  No synchronization avoidance is needed.

### C13

Forward blocks are first-check C13 B0–B5, schedule
`(0,0), (1,4), (2,7), (3,14), (4,21), (5,24)`.  Replace every old
“under F3” qualification by the updated world

```
ϱᵍ = { (αᴸ:=ℕ, αᴿ:=★), (αᴸ:=ℕ, βᴿ:=★) }.
```

Here `αᴸ` comes from the left source `ν`; `αᴿ` and `βᴿ` come from the
first and second right `Inst`/`TyBeta` pairs, respectively.  At B0 the
left and right core `Λ`s are paired in `ϱˡ`; the left source `ν` is
one-sided.  The catch-up allocations replace that binder alignment by the
two displayed global pairs.

The outer right `Y` and the left `X` form one both-sided center name at
`X⊑★`; the inner right `X` rejoins it.  Each right rep. var has one left
partner, both pairs agree by `ℕ⊑★`, and `ϱˡ=∅` after the
allocations.  B2–B4 retain the mark across every D15 hide/rejoin.  At B0 the
core `Λ⊑Λ` pair is lexical; the right's two `Inst`/`TyBeta` catch-up steps
and the left `TyBeta` turn its needed alignments into the two global pairs
above.

Backward is adjacent, `B0 ⇝ ··· ⇝ B5`: after B0's first right `Inst`,
the right may take the remaining three allocation steps and the left may take
its one `TyBeta` to B1.  No extra related block is required.

### C14

Forward blocks are first-check C14 B0–B5, schedule
`(0,0), (1,5), (2,6), (3,19), (4,32), (5,33)`.  B1 now has

```
ϱᵍ = { (αᴸ:=ℕ, γᴿ:=ℕ),
       (αᴸ:=ℕ, βᴿ:=★),
       (αᴸ:=ℕ, αᴿ:=★) }.
```

Here `αᴸ` comes from the left source `ν`; `αᴿ` and `βᴿ` come from the
first and second right `Inst`/`TyBeta` pairs; `γᴿ` comes from the right
source `ν` at `ℕ`.  At B0 the matching source `ν`s and core `Λ`s supply
the relevant pairs in `ϱˡ`; the five allocation steps replace those
alignments by the three displayed global pairs.

The left `X` and right outer `Z` are the both-sided name `c` at `c⊑★`;
right `+Y^β` and `+X^α` both rejoin `c`.  The three pairs agree, and
each right rep. var has exactly one left partner.  B2–B4 use D15 repeatedly:
`c` keeps its original mark through both right-only unbind/rejoin sequences.
At B0 the matching source `ν` and core `Λ` premises contribute lexical
pairs; the five allocation steps turn the needed alignments into the three
global pairs above.

Backward is `B0 ⇝ B1 ⇝ B2 ⇝ B3 ⇝ B4 ⇝ B5`.  The first right
`Inst` may be followed during catch-up by its remaining allocation steps and
the left `TyBeta`, so every right step from a related block is covered.

### C16

Forward blocks are first-check C16 B0–B11, schedule
`(0,0), (1,0), (2,0), (3,0), (4,0), (5,1), (6,1), (7,1),
(8,1), (9,1), (10,1), (11,1)`.  The left `ν` and gen binder are
one-sided: `ϱˡ=∅`; `αᴸ:=ℕ` is unpaired, so `ϱᵍ=∅`.  Every
visible or recreated `X` is left-only at `X⊑★`.  In B4–B8, `+X^αᴸ`
after an unbind creates a new left-only name because there is no right
partner; all final interior worlds are well formed.  Backward is `B0–B4 ⇝
B5`; the right is a value thereafter.

### C16b

Forward blocks are first-check C16b B0–B16, schedule
`(0,0), (1,0), (2,0), (3,0), (4,0), (5,0), (6,0), (7,0),
(8,1), (9,1), (10,1), (11,1), (12,1), (13,1), (14,1), (15,1),
(16,1)`.  As in C16, every binder and allocation is left-only:
`ϱˡ=ϱᵍ=∅`, `αᴸ:=★` is unpaired, and all `X` names have
`X⊑★`.  D15 validates the same multi-entry final worlds as C16.
Backward is `B0–B7 ⇝ B8`.

### C17

Forward blocks are first-check C17 B0–B9, schedule
`(0,0), (1,0), (2,0), (3,0), (4,0), (5,1), (6,1), (7,2),
(8,2), (9,2)`.  Both left `ν`s and both left `Λ`s are one-sided.
Consequently `ϱˡ=ϱᵍ=∅`; `αᴸ:=ℕ` and `βᴸ:=ℕ` are
unpaired.  Boundary names `X` and `Y` are left-only at `X⊑★` and
`Y⊑★`; the two-entry `+Y,+X` and `−X,−Y` premises have well-formed
final worlds.  Backward is `B0–B4 ⇝ B5` for the first right `Beta` and
`B5–B6 ⇝ B7` for the second.

### C18

Forward blocks are first-check C18 B0–B9, schedule
`(0,0), (1,2), (2,4), (3,5), (4,8), (5,9), (6,12),
(7,13), (8,14), (9,17)`.  B0 relates the two core `Λ` binders
lexically.  After the first catch-up, B1 has
`ϱᵍ={(αᴸ:=ℕ,αᴿ:=★)}` and a lexical pair for the still
uninstantiated second `Λ`.  B2 has
`ϱᵍ={(αᴸ:=ℕ,αᴿ:=★),(βᴸ:=ℕ,βᴿ:=★)}` and no
remaining lexical pair.  `X` and `Y` are both-sided at `X⊑X` and `Y⊑Y`;
each names its global pair, both pairs agree, and D13 holds.

Backward is adjacent through B9.  Each right `Inst` is followed by its
`TyBeta` and the matching left `TyBeta`, transferring the corresponding
lexical pair to `ϱᵍ` as D16 requires.

### C18b

Forward blocks are first-check C18b B0–B9, schedule
`(0,0), (1,1), (2,2), (3,4), (4,6), (5,8), (6,10),
(7,12), (8,17), (9,18)`.  B0's two `ν⊑ν` premises supply two lexical
pairs.  They become
`ϱᵍ={(αᴸ:=ℕ,αᴿ:=ℕ),(βᴸ:=ℕ,βᴿ:=ℕ)}` at B2.
Both names are `X⊑★`/`Y⊑★`, chosen at their binders because the
right gen body sees `★`.  In B5 and B7 the right `+X,+Y` entries rejoin the
same names through the two global pairs; D15 preserves both marks and checks
only the final world.  Names name paired rep. vars, both pairs agree, and D13
holds.  Backward is adjacent through B9.

### C19

Forward blocks are first-check C19 B0–B10, schedule
`(0,0), (1,0), (2,0), (3,1), (4,1), (5,1), (6,1), (7,2),
(8,2), (9,2), (10,2)`.  All `Λ` and `ν` binders are left-only, so
`ϱˡ=ϱᵍ=∅`.  The store has unpaired `αᴸ:=ℕ` and later
`βᴸ:=αᴸ`; the latter is still a left store rep. var, not a pair.
`X` and `Y` are left-only at `X⊑★` and `Y⊑★`.  All multi-entry
boundaries end in a well-formed world.  Backward is `B0–B2 ⇝ B3` for the
first right `Beta`, and `B3–B6 ⇝ B7` for the second.

### C22

Forward blocks are first-check C22 B0–B5, schedule
`(0,0), (1,1), (2,2), (3,3), (4,4), (5,5)`.  B0 pairs the matching `ν`
and `Λ` binder rep. vars in `ϱˡ`; B1 replaces the used lexical
alignment with `ϱᵍ={(αᴸ:=ℕ,αᴿ:=ℕ)}`.  `X` is both-sided at
`X⊑X`, names that pair, and is dropped by the matched unbinds.  Backward is
adjacent through B5.

### C23a

Forward blocks are first-check C23a B0–B9, schedule
`(0,0), (1,2), (2,3), (3,3), (4,4), (5,10), (6,11),
(7,16), (8,17), (9,22)`.  At B0, the binder alignment that the right
`Inst` consumes is lexical; the still-enclosing matched `ν`s have their own
lexical pair.  B1 has
`ϱᵍ={(αᴸ:=ℕ,αᴿ:=★)}` plus the surviving `ν` pair in
`ϱˡ`.  B2 has
`ϱᵍ={(αᴸ:=ℕ,αᴿ:=★),(βᴸ:=ℕ,βᴿ:=ℕ)}` and
`ϱˡ=∅`.

Choose the `X` mark at B1 to be `X⊑★`, not the first check's
unnecessarily strong `X⊑X`; B3 makes `X` left-only before the right `+X`
rejoins it, so D11/D15 require the earlier `X⊑★` choice.  Choose `Y⊑Y`.
Both choices derive all the same type comparisons.

The decisive unrestricted block is unchanged verbatim:

```
L  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+Y^β] ([+X^α] (λx:Y. ([−X^α] 42⟨ℕ!⟩^[Y:X∼X] ⟨−X⟩)) ⟨id(Y) → +X⟩)⟨id(Y) → id(★)⟩^[Y:X∼X] ⟨−Y → id(★)⟩) 69)
   [B5] ·⊑·, ⟪⟫⊑⟪⟫, ⊑cast, ⊑⟪⟫, ƛ⊑ƛ,
   then W[(−X,−Y) ∥ (−X)].
```

The final interior world has `X` dropped and `Y` right-only; right-only names
carry no left-only mark condition.  Every both-sided name outside names one
of the two global pairs, and both pairs agree.  Restricting
`W[(−X,−Y) ∥ (−X)]` to forbid the left-only unbind would reject B5
and B7.  D15 instead checks only this final, well-formed world.

Backward: `B0 ⇝ B1 ⇝ B2`; because B2→B3 advances only the left,
`B2–B3 ⇝ B4`; then `B4 ⇝ B5 ⇝ B6 ⇝ B7 ⇝ B8 ⇝ B9`.

### C23b

Forward blocks are first-check C23b B0–B9, schedule
`(0,0), (1,1), (2,3), (3,3), (4,4), (5,9), (6,10),
(7,16), (8,19), (9,20)`.  B1 has
`ϱᵍ={(αᴸ:=ℕ,αᴿ:=ℕ)}` and a lexical alignment for the
remaining left `ν`/right `Λ` catch-up.  B2 has
`ϱᵍ={(αᴸ:=ℕ,αᴿ:=ℕ),(βᴸ:=ℕ,βᴿ:=★)}` and
no lexical pair.  `X` is both-sided at `X⊑X`; `Y` is initially left-only
at `Y⊑★`, then right `+Y` rejoins it through `(βᴸ,βᴿ)` and keeps
that mark.  The opposite boundary orders remove the same two names, so all
final interior worlds are well formed.  Backward is `B0 ⇝ B1 ⇝ B2`,
`B2–B3 ⇝ B4`, and then adjacent through B9.

### CJ

Forward blocks are first-check CJ B0–B5, schedule
`(0,0), (1,0), (2,1), (3,1), (4,1), (5,2)`.  No binder or boundary rule
is used, hence names, `ϱˡ`, and `ϱᵍ` are empty.  Backward is
`B0–B1 ⇝ B2` for `TagUntagBad`, and `B2–B4 ⇝ B5` for `Blame`.

## Mirror pairs

Let `A_i` be C12-R state `i`, `F_i` Cf-R state `i`, and `G_i` Cg-R
state `i` in `cambridge-traces.md`.  Those references preserve the rendered
terms verbatim and distinguish same-printed allocation names by run.

### M1 = C12-R `⊑` Cf-R

The forward schedule, one block for every left step, is

```
(A0,F0) (A1,F0) (A2,F0) (A3,F1) (A4,F2)
(A5,F3) (A6,F4) (A7,F4) (A8,F4) (A9,F4)
(A10,F4) (A11,F5) (A12,F6) (A13,F6) (A14,F6)
(A15,F7) (A16,F8) (A17,F9) (A18,F10) (A19,F11)
```

Outer-rule spines: `(A0,F0)` is `·⊑·`, `ν⊑ν`, `cast⊑cast` for the
two gen casts, `cast⊑` for the left inst cast, then `Λ⊑`.  `(A1,F0)`
replaces that last part by `cast⊑`, `ν⊑`, `Λ⊑`; `(A2,F0)` replaces
the inner `ν⊑` by `⟪⟫⊑`.  `(A3,F1)` is printed below.  From
`(A4,F2)` through `(A10,F4)`, the outer paired gen boundaries use
`⟪⟫⊑⟪⟫`; casts use `cast⊑cast`/`cast⊑`, applications use `·⊑·`, and
the extra Inst boundary always uses `⟪⟫⊑`.  `(A11,F5)` through
`(A18,F10)` have the same outer paired boundary and gen-cast spine,
with the extra left boundary entries discharged by `⟪⟫⊑`.  The final
block is `κ⊑κ`.

The allocation block is:

```
L  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5)
   [A3,F1] ·⊑·, ⟪⟫⊑⟪⟫ for the outer names, cast⊑cast for gen,
   and ⟪⟫⊑ for the left Inst boundary.
```

The left `Y` and right `X` are one both-sided name `c` at `c⊑★`, with
`ϱᵍ={(βᴸ:=ℕ,αᴿ:=ℕ)}`.  The left inner `X` is left-only at
`X⊑★`; its `αᴸ:=★` is unpaired.  Initially the outer matched
source `ν`s contribute `ϱˡ={(uᴸ_ν,uᴿ_ν)}`; the left-only `Inst`
`ν` contributes no pair.  `(A1,F0)` still has only the outer lexical pair;
`(A2,F0)` additionally has the unpaired store rep. var `αᴸ:=★`.  After
A3/F1 only the displayed global pair and that unpaired left store rep. var
are present.  The two gen unbinds match; all later left-only inner entries
create, hide, or drop only the left `X`.  Every final world is well formed,
and `ϱ` is one-to-one.  There is no right-only name in any block.

For backward simulation, from `(A0,F0)`, `(A1,F0)`, or `(A2,F0)`, the
right `TyBeta` is followed by enough left allocation steps to reach
`(A3,F1)`.  Thereafter each next right step catches to the next scheduled
block whose right index increases; runs of equal `F` index catch to the first
later such block.  No extra block is needed.

### M4 = C12-R `⊑` R3 = `ex1`

The claimed pair is not initially in `⊢²`.  The concrete initial block is:

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x))⟨inst Z. (Z?ℓ0 → Z!)⟩^[]⟨gen X′. (X′! → X′?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
R  ((λx:★→★. (x 5⟨ℕ!⟩^[])) (ΛX. (λx:X. x))⟨inst Y. (Y?ℓ0 → Y!)⟩^[])
```

Both terms are applications, so the only possible outer rule is `·⊑·`.
Its function premise would have to establish

```
ℕ→ℕ ⊑ (★→★)→★,
```

whose domain premise is exactly `ℕ ⊑ ★→★`.  No clause of type
imprecision derives that premise.  Cast, boundary, `ν⊑`, and
`∀⊑⟪+⟫` cannot change the outer application decomposition.  Hence no
alternative synchronization relates the initial states, and neither
simulation starts.

After the right takes `Inst, TyBeta, Beta`, its state is

```
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
```

The left initial state is related to this suffix state: `·⊑·`, `ν⊑`,
`∀⊑⟪+⟫`, and cast rules apply.  At that first suffix block,
`ϱˡ={(aᴸ_ΛY,αᴿ:=★)}` pairs the left abstract rep. var with the right
store rep. var.  After the left `Inst`/`TyBeta`, D16 replaces it by the
one-to-one global pair `ϱᵍ={(αᴸ:=★,αᴿ:=★)}`.  The left source `[ℕ]`
allocation `βᴸ:=ℕ`, its `+Y^β`, and the gen unbind are left-only at
`Y⊑★`.  Thus the world claim in §12.6 is true for the post-`Beta`
suffix, but it does not establish the pair of complete runs.

The smallest test-level repair would replace R3 by the direct-application
program `Ch-R`; its first two steps reach the actual post-`Beta` suffix shown
above.  The smallest relation-level repair would add a weak administrative
closure admitting that initial right `Inst, TyBeta, Beta` prefix.  This note
adopts neither.

### M2 = C12-R `⊑` Cg-R

The forward schedule is

```
(A0,G0) (A1,G0) (A2,G0) (A3,G2) (A4,G5)
(A5,G6) (A6,G7) (A7,G7) (A8,G7) (A9,G7)
(A10,G7) (A11,G8) (A12,G9) (A13,G9) (A14,G9)
(A15,G10) (A16,G11) (A17,G12) (A18,G13) (A19,G16)
```

Outer-rule spines: `(A0,G0)` is `·⊑·`, `ν⊑`, `⊑cast` for the
right inst cast, `cast⊑cast` for gen/gen, `cast⊑` for the left inst
cast, then `Λ⊑`.  `(A1,G0)` and `(A2,G0)` replace the left inst-cast
tail by respectively `ν⊑` and `⟪⟫⊑`.  `(A3,G2)` is printed below.
From `(A4,G5)` through `(A10,G7)`, the paired gen boundaries use
`⟪⟫⊑⟪⟫`, the left Inst boundary uses `⟪⟫⊑`, and the remaining
spine consists of the displayed cast and application rules.  From
`(A11,G8)` through `(A18,G13)`, the same boundary rules surround the
matched gen tail.  `(A19,G16)` is `⊑cast`.

The allocation block is:

```
L  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   [A3,G2] ·⊑·, ⊑cast, ⟪⟫⊑⟪⟫ for the gen boundaries,
   and ⟪⟫⊑ for the left Inst boundary.
```

The left `Y` and right `X` are one both-sided name at `X⊑★`, with
`ϱᵍ={(βᴸ:=ℕ,αᴿ:=★)}`.  The left inner `X` is left-only
at `X⊑★`, and `αᴸ:=★` is unpaired.  The optional right-led extra block
`X2=(A2,G2)` is derivable by `·⊑·`, `ν⊑`, `⊑cast`, and
`∀⊑⟪+⟫`: it has
`ϱˡ={(uᴸ_νY,αᴿ:=★)}` for the binder that the left source `ν`
will instantiate.  The left source `TyBeta` turns that lexical pair into
the displayed global pair.  The two gen unbinds match, every paired
representation agrees by `ℕ⊑★`, and `ϱ` remains one-to-one.  There is no
right-only name in any block.  Before X2, `(A0,G0)` and `(A1,G0)` have no
pair; `(A2,G0)` has only the unpaired left store rep. var `αᴸ:=★`.

Backward: from any of `(A0,G0)`, `(A1,G0)`, or `(A2,G0)`, the right's
`Inst` can be followed by its `TyBeta` and the remaining left allocations to
`(A3,G2)`.  From there, each right step catches to the next block with a
larger `G` index; equal-index runs are skipped during catch-up.  No extra
block is required, although X2 exposes the D14 route directly.

## Findings

1. **M4 fails before any world is created.**  On the concrete initial terms
   above, `·⊑·` requires `ℕ→ℕ ⊑ (★→★)→★`, hence the
   impossible premise `ℕ ⊑ ★→★`.  No synchronization avoids an
   initial relation.  After R3's `Inst, TyBeta, Beta`, the suffix is
   derivable and its `ϱ` is one-to-one.  The smallest test fix is to use
   the direct-application program `Ch-R` instead of R3; `Ch-R` reaches the
   displayed suffix in two steps.  The smallest relation fix is an explicit
   weak administrative closure.  Neither fix is adopted.

2. **D14 settles both former rule gaps.**  Cg's right-led block uses
   `∀⊑⟪+⟫` with mark `X⊑★`; C2's uses the same rule with a left
   gen-cast ∀-value.  Ch/design-P3 records the needed abstract/store pair
   in `ϱˡ`, so D16 makes the rule's premise well formed.

3. **D15 settles the multi-entry ambiguity.**  C2 B6/B7 check only the final
   interior world and retain the binder's earlier mark.  The same reading
   validates Cf, C12–C14, C18b, C23a, and C23b; no transient prefix world is
   a premise.

4. **D13 settles C12, C13, and C14.**  Their formerly failing blocks need
   respectively two, two, and three right partners for one left store rep.
   var.  Each right rep. var still has one left partner, all pairs agree,
   and every rejoin is unique from the right.  M1 and M2 remain one-to-one;
   M4's derivable suffix also remains one-to-one.

5. **C23a confirms that `W[δ ∥ δ′]` must remain unrestricted.**  In B5
   and B7, `W[(−X,−Y) ∥ (−X)]` leaves `Y` right-only.  Its final
   world is well formed, but a ban on a left-only unbind of a shared name
   would reject the block.  The one-sided `Merge` producer identified as F4
   in the first check is therefore real.
