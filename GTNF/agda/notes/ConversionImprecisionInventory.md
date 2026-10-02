# Conversion-imprecision inventory for the 28 pairs

This is the data check for D17.  It uses the synchronized blocks in
`GTNF/design.md` §12.4 and
`GTNF/notes/cambridge-imprecision-check-v2.md`.  The left conversion is
always the more precise one.

The smallest non-candidate block is C23a B3:

`−X → (−Y → +X) ⊑ id(★) → (−Y → id(★))`.

Its domain needs `seal X ⊑ id(★)` and its final codomain needs
`unseal X ⊑ id(★)`.  In that conversion world, `Y` is both-sided at
`Y⊑Y`, while `X` is left-only at `X⊑★`.  C23b B0 supplies the other
extension:

`∀Z.(−Y → (id(Z) → +Y)) ⊑ −X → (id(★) → +X)`.

The universal is opened under a left-only `Z⊑★`; the ν-bound `Y` and
`X` are one both-sided center name.

## Notation

- `rX = −X → +X`.
- `oXY = −X → (id(Y) → +X)`.
- `mXY = −X → (−Y → +X)`.
- `qA,Y = id(A) → (−Y → id(A))`.
- `kYX = −Y → +X`.
- `N(m; α,β)` is a ν-conversion world.  The TyBetaBoundary conversion
  contexts contain one fresh both-sided name at mark `m`; the ν-bound
  rep. vars `(α,β)` are in `ϱˡ`.
- `B(names; ϱᵍ)` is a matched-boundary conversion world.  Its contexts
  are the union of names live anywhere along each boundary.  Continuing
  names retain their marks; new names join exactly through `ϱᵍ ∪ ϱˡ`.
- `struct` means only the candidate `id`, arrow, matched universal,
  matched seal/unseal, and chain clauses are used.  `seal★`, `unseal★`,
  and `∀L` name the three extensions above.

Repeated occurrences of the same syntactic pair are grouped, but every
block containing a matched ν or matched boundary is named.

## P1–P6

| pair | matched conversion pairs and blocks | conversion world | clauses |
|---|---|---|---|
| P1 | initial ν: `rX ⊑ rX`; first boundaries: `rX ⊑ rX`; Wrap/Beta: `+X ⊑ +X`, `−X ⊑ −X`; Merge: `id(ℕ) ⊑ id(★)` | ν: `N(X⊑X; uᴸν,uᴿν)`; boundaries: `B(X:X⊑X; (αᴸ:=ℕ,αᴿ:=★))` | struct |
| P2 | none: its ν and every boundary are left-only | no conversion world premise | — |
| P3 | after the left catches up: `rX ⊑ rX`, then `+X ⊑ +X`, `−X ⊑ −X`, and `id(ℕ) ⊑ id(★)` | `B(X:X⊑X; (αᴸ:=ℕ,αᴿ:=★))` | struct |
| P4 | initial ν: `rX ⊑ rX`; matched boundaries through both Merge blocks: `rX ⊑ rX`, `+X ⊑ +X`, `−X ⊑ −X`, final `id(ℕ) ⊑ id(ℕ)` even when `δ ≠ δ′` | ν: `N(X⊑X; uᴸν,uᴿν)`; boundaries: `B(X:X⊑★; (αᴸ:=ℕ,αᴿ:=ℕ))`; conversion contexts retain `X` through right unbind/rebind | struct |
| P5 | none: the ν and boundaries on the left are one-sided | no conversion world premise | — |
| P6 | initial ν and post-TyBeta boundary: `−X → id(ℕ) ⊑ −X → id(★)`; final boundary: `id(ℕ) ⊑ id(★)` | ν: `N(X⊑X; uᴸν,uᴿν)`; boundaries: `B(X:X⊑X; (αᴸ:=𝔹,αᴿ:=𝔹))` | struct (`seal`, arrow, `id`) |

## The 22 Cambridge pairs

| pair | matched conversion pairs and blocks | conversion world | clauses |
|---|---|---|---|
| Cf | B0 ν `rX ⊑ rX`; B1 `rX ⊑ rX`; B2–B3 `+X ⊑ +X` and `−X ⊑ −X`; B4 `id(ℕ) ⊑ id(ℕ)` with different boundary lists | ν: `N(X⊑X; uᴸν,uᴿν)`; B1–B4: `B(X:X⊑★; (αᴸ:=ℕ,αᴿ:=ℕ))` | struct |
| Cg | B1 `rX ⊑ rX`; B2–B3 `+X ⊑ +X`, `−X ⊑ −X`; B4 `id(ℕ) ⊑ id(★)` | `B(X:X⊑★; (αᴸ:=ℕ,αᴿ:=★))` | struct |
| Ch | B1 `rX ⊑ rX`; B2–B3 `+X ⊑ +X`, `−X ⊑ −X`; B4 `id(ℕ) ⊑ id(★)` | `B(X:X⊑X; (αᴸ:=ℕ,αᴿ:=★))` | struct |
| Ce | none: all ν/boundary uses are left-only | no conversion world premise | — |
| C2 | B1–B9: `rX ⊑ rX`, `id(★)→id(★) ⊑ id(★)→id(★)`, `+X ⊑ +X`, `−X ⊑ −X`, and `id(X) ⊑ id(X)`; B10 `id(ℕ) ⊑ id(★)` | `B(X:X⊑X; (αᴸ:=ℕ,αᴿ:=★))`; conversion contexts retain `X` across every multi-entry boundary | struct |
| C5 | none | no conversion world premise | — |
| C6 | none: its ν and boundary are left-only | no conversion world premise | — |
| C8 | B0 ν `rX ⊑ rX`; B1–B3 `rX`, `+X`, and `−X` against themselves; B4 `id(ℕ) ⊑ id(★)` | ν: `N(X⊑X; uᴸν,uᴿν)`; boundaries: `B(X:X⊑X; (αᴸ:=ℕ,αᴿ:=★))` | struct |
| C10 | none: the allocation and all boundaries are left-only | no conversion world premise | — |
| C12 | B0 ν `rX ⊑ rX`; B1 `rX ⊑ rY`; B2–B3 `+X ⊑ +Y`, `−X ⊑ −Y`; B4 `id(ℕ) ⊑ id(ℕ)` despite the longer right boundary | ν: `N(X⊑X; uᴸν,uᴿν)`; boundaries: one center `c:X⊑★`, with `ϱᵍ={(αᴸ:=ℕ,βᴿ:=ℕ),(αᴸ:=ℕ,αᴿ:=★)}`; right `X` and `Y` both join `c` | struct |
| C13 | B1 `rX ⊑ rY`; B2–B3 `+X ⊑ +Y`, `−X ⊑ −Y`; B4 `id(ℕ) ⊑ id(★)` | one center `c:X⊑★`, with `ϱᵍ={(αᴸ:=ℕ,αᴿ:=★),(αᴸ:=ℕ,βᴿ:=★)}` | struct |
| C14 | B0 ν `rX ⊑ rX`; B1 `rX ⊑ rZ`; B2–B3 `+X ⊑ +Z`, `−X ⊑ −Z`; B4 `id(ℕ) ⊑ id(ℕ)` | ν: `N(X⊑X; uᴸν,uᴿν)`; boundary center `c:X⊑★`, with `(αᴸ:=ℕ)` paired globally with `γᴿ:=ℕ`, `βᴿ:=★`, and `αᴿ:=★` | struct |
| C16 | none: all boundaries are left-only | no conversion world premise | — |
| C16b | none: its ν and all boundaries are left-only | no conversion world premise | — |
| C17 | none: both νs and all boundaries are left-only | no conversion world premise | — |
| C18 | B1 `∀Y.oXY ⊑ ∀Y.oXY`; B2 `qℕ,Y ⊑ q★,Y` and `oXY ⊑ oXY`; B3 `mXY ⊑ mXY`; B4–B7 `kYX`, `+X`, `−X`, and `−Y` against themselves; B8 `id(ℕ) ⊑ id(★)` | `B(X:X⊑X,Y:Y⊑Y; ϱᵍ={(αᴸ:=ℕ,αᴿ:=★),(βᴸ:=ℕ,βᴿ:=★)})`; the matched `∀` adds its abstract pair to `ϱˡ` at `Y⊑Y` | struct |
| C18b | B0 two ν pairs: `qℕ,X ⊑ qℕ,X` and `∀Z.oYZ ⊑ ∀Z.oYZ`; B1 repeats the remaining ν pair and matches `∀Y.oXY`; B2–B7 match `qℕ,Y`, `oXY`, `mXY`, `kYX`, `+X`, `−X`, and `−Y` with themselves; B8 `id(ℕ) ⊑ id(ℕ)` | ν names use `X⊑X`; boundary names are `X⊑★`, `Y⊑★`, with `ϱᵍ={(αᴸ:=ℕ,αᴿ:=ℕ),(βᴸ:=ℕ,βᴿ:=ℕ)}`; matched universals add an `X⊑X` lexical pair | struct |
| C19 | none: both νs and every boundary are left-only | no conversion world premise | — |
| C22 | B0 ν `rX ⊑ rX`; B1–B3 `rX`, `+X`, and `−X` against themselves; B4 `id(ℕ) ⊑ id(ℕ)` | ν: `N(X⊑X; uᴸν,uᴿν)`; boundaries: `B(X:X⊑X; (αᴸ:=ℕ,αᴿ:=ℕ))` | struct |
| C23a | B0–B1 matched νs use `qℕ,X ⊑ q★,X` and `qℕ,Y ⊑ q★,Y`; B1 also `∀Y.oXY ⊑ ∀Y.oXY`; B2 repeats `qℕ,Y ⊑ q★,Y` and `oXY ⊑ oXY`; B3 `mXY ⊑ q★,Y`; B4–B5 `kYX ⊑ −Y→id(★)` and `−X ⊑ id(★)` where the shorter right boundary omits `X`; B6–B7 `+X ⊑ id(★)` plus the remaining matched `−X`/`−Y`; B8 `id(ℕ) ⊑ id(★)` | `X:X⊑★`, `Y:Y⊑Y`; `ϱᵍ={(αᴸ:=ℕ,αᴿ:=★),(βᴸ:=ℕ,βᴿ:=ℕ)}`.  In B3–B4 the outer conversion world has `Y` both-sided and `X` left-only; B5 rejoins `X`; B8 leaves `Y` right-only in the final term interior but the conversion context still contains every boundary name | struct + `seal★` + `unseal★` |
| C23b | B0 matched ν and B1 matched `X` boundary: `∀Z.oYZ ⊑ −X→(id(★)→+X)`; B2 `oXY ⊑ −X→(id(★)→+X)`; B3 `mXY ⊑ −X→(id(★)→+X)`; B4–B5 `kYX ⊑ id(★)→+X`; B4–B7 also match the surviving `−X` conversions; B6 additionally `−Y ⊑ id(★)`; B6–B7 `+X ⊑ +X`; B8 `id(ℕ) ⊑ id(ℕ)` | `X:X⊑X`, `Y:Y⊑★`; `ϱᵍ={(αᴸ:=ℕ,αᴿ:=ℕ),(βᴸ:=ℕ,βᴿ:=★)}` after catch-up.  For B0/B1, `∀L` adds left-only `Z:X⊑★`; in B2–B6, omitted right layers leave `Y` left-only at `X⊑★` until its right bind rejoins it | struct + `∀L` + `seal★` |
| CJ | none: no ν or boundary rule occurs | no conversion world premise | — |

## Result

The candidate clauses cover every matched pair except exactly these three
structural extensions:

1. `seal X ⊑ id(★)` when the left name has mark `X⊑★` (C23a B3 and
   C23b B3/B6).
2. `unseal X ⊑ id(★)` under the same condition (C23a B3–B7).
3. `∀c ⊑ g′` when `c ⊑ ⌞g′⌟` under a left-only `X⊑★` binder
   (C23b B0/B1).
