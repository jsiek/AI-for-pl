# P' Trace

Checked scratch: `PPrimeTraceScratch.agda`

Command used:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 PPrimeTraceScratch.agda
```

Result: the checked closed program returns a value. It does not blame and does
not get stuck. The runtime route is the seal route:

```text
((d ↓ seal α ★) ↓ seal β (＇ α))
```

followed by the matching `unseal β (＇ α)` and `unseal α ★`.

The counterfactual variable projection route would blame:

```text
(0 ⟨ idℕ ! ⟩) ⟨ ？ (id (＇ α)) ⟩ —→ blame
```

That route is checked separately in `bad-variable-projection-blames`, but it is
not the route produced by the compiled well-typed P'.

## Source term used

The literal source sketch

```text
(ΛX. ((ΛY. λx:Y. x) [X]) d) [★]   with d : ★
```

is not directly typable as a `GradualTerms` term in this development:

- `⊢Λ` has a value restriction, while the outer body is an application.
- Under the outer type binder, `d : ★` cannot be passed to a function expecting
  `X`, because plain source typing uses `_∼_ = idᶜ ⊢_∼_`, and
  `idᶜ ⊢ ＇ 0 ∼ ★` is not derivable.

The closest checked closed program is:

```text
P' =
  ((ΛX. λd:X. ((ΛY. λx:Y. x) [X]) d) [★]) 0
```

where the final application uses source consistency

```text
★∼ℕ = ？ (id (‵ `ℕ))
```

so the compiled numeric argument enters the dynamic boundary as:

```text
0 ⟨ id (‵ `ℕ) ! ⟩
```

The scratch records this as `P′ᴳ`, `P′⊢ᴳ`, and `P′ᶜ`.

## Checked gates

The scratch proves:

```agda
P′-skeleton-gate = refl
P′-eval-is-value = refl
P′-eval-allocations = refl
P′-eval-tags = refl
two-seal-route = ...
bad-variable-projection-blames = ...
```

The evaluator allocation summary is:

```text
step 0: allocate α with representation ★
step 3: allocate β with representation ＇ α
```

The variable-ground tag summary is empty: no compiled `＇ α !` tag is produced
on this route.

## Cast and conversion forms

The relevant constructor forms are:

```text
final dynamic argument boundary:
  source proof       ★∼ℕ = ？ (id (‵ `ℕ))
  compiled argument  sym-screen ★∼ℕ = id (‵ `ℕ) !

inner application:
  source proof       id (＇ 0)
  compiled argument  id (＇ 0)
  after allocation   id (＇ α)      -- Agda: id (＇ 1) after β is fresh 0

outer [★] β-Λ conversion:
  〖 α , ★ ↑ (X ⇒ X) 〗
    = seal α ★ ↦↑ unseal α ★

inner [α] β-Λ conversion:
  〖 β , ＇ α ↑ (Y ⇒ Y) 〗
    = seal β (＇ α) ↦↑ unseal β (＇ α)
```

No actual compiled step constructs `？ (id (＇ α))`.

## Reduction trace

Let:

```text
ℕ! = id (‵ `ℕ) !
```

After compilation, the relevant target shape is:

```text
(((Λ (λ d:X. (((Λ (λ x:Y. x)) [X]) (d ⟨ id X ⟩)))) [★])
  (0 ⟨ ℕ! ⟩))
```

The step sequence is:

```text
1. Outer [★] type application:
   allocate α ↦ ★

   ((λ d:α. ((ΛY. λx:Y. x) [α]) (d ⟨ id α ⟩))
      ↑ (seal α ★ ↦↑ unseal α ★))
     (0 ⟨ ℕ! ⟩)

2. Function reveal application:

   ((λ d:α. ((ΛY. λx:Y. x) [α]) (d ⟨ id α ⟩))
      (0 ⟨ ℕ! ⟩ ↓ seal α ★))
     ↑ unseal α ★

3. Term β:

   (((ΛY. λx:Y. x) [α])
      ((0 ⟨ ℕ! ⟩ ↓ seal α ★) ⟨ id α ⟩))
     ↑ unseal α ★

4. Inner [α] type application:
   allocate β ↦ ＇ α

   (((λ x:β. x) ↑ (seal β (＇ α) ↦↑ unseal β (＇ α)))
      ((0 ⟨ ℕ! ⟩ ↓ seal α ★) ⟨ id α ⟩))
     ↑ unseal α ★

5. The inner application's argument cast is identity, not projection:

   (((λ x:β. x) ↑ (seal β (＇ α) ↦↑ unseal β (＇ α)))
      (0 ⟨ ℕ! ⟩ ↓ seal α ★))
     ↑ unseal α ★

6. Inner function reveal application:

   (((λ x:β. x)
      ((0 ⟨ ℕ! ⟩ ↓ seal α ★) ↓ seal β (＇ α)))
      ↑ unseal β (＇ α))
     ↑ unseal α ★

7. Term β:

   (((0 ⟨ ℕ! ⟩ ↓ seal α ★) ↓ seal β (＇ α))
      ↑ unseal β (＇ α))
     ↑ unseal α ★

8. Peel β:

   (0 ⟨ ℕ! ⟩ ↓ seal α ★) ↑ unseal α ★

9. Peel α:

   0 ⟨ ℕ! ⟩
```

The final term is an inert dynamic value, namely the ℕ-tagged zero.

## Fresh-name `Env∼` mode

The plain `β-Λ` type-application path allocates with a store change `bind A`.
For consistency environments, this is `extᵐ`, so the fresh name is reflexive:

```agda
extᵐ idᶜ zero = X∼X
```

The scratch records:

```agda
plain-β-mode = refl
plain-β-no-X∼★ ()
plain-β-no-★∼X ()
```

So at a plain `β-Λ` fresh name, neither variable-ground injection nor
variable-ground projection is dischargeable.

By contrast:

```agda
instᵐ idᶜ zero = X∼★
genᵐ  idᶜ zero = ★∼X
```

At `instᵐ`, `＇ α ∼★` is dischargeable, giving `id (＇ α) !`. At `genᵐ`,
`★∼ ＇ α` is dischargeable, giving `？ (id (＇ α))`. The compiled P' path uses
plain `β-Λ`, so it gets seal/unseal conversions instead of either variable
tag/untag consistency cast.
