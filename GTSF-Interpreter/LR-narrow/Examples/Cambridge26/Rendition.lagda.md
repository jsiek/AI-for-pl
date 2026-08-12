# Cambridge26 examples: checked LR-narrow rendition

```agda
module LR-narrow.Examples.Cambridge26.Rendition where

-- File Charter:
--   * Gives a literate, textual rendition of every Cambridge26 encoding.
--   * Names every typing, coercion-typing, and narrowing step.
--   * Imports the pretty-printed strings obtained from the checked ASTs.
--   * States LR membership explicitly and records the direct proof for
--     Example 5; it does not assume missing fundamental-theorem cases.

open import LR-narrow.Examples.Cambridge26.Renderings public
import LR-narrow.Examples.Cambridge26.K.Renderings as KRenderings
```

This catalogue is generated from the checked terms, endpoint typings, and
canonical narrowing derivations in the sibling example modules. Lambda
annotations come from `Pretty.TypedTerms`; the raw term AST does not retain
them. The displayed orientation follows `cambridge26.lagda.md`:

    imprecise endpoint  ⊒  precise endpoint : narrowing coercion.

Internally `ClosedExample` stores its terms and types in this displayed order.
Its relation index remains the source-to-target proof
`precise-type ⊑ imprecise-type`, because that is the orientation of
`ImprecisionWf`; its checked narrowing derivation has the displayed direction.
Lines headed by `—→` or `—↠` reproduce reduced
states displayed in the Cambridge notes. The final inference in each example
is the direct logical-relation goal `Membership example`. Example 5 discharges
this goal directly as `Example05.example-membership`; the remaining examples
do not assume an unfinished fundamental theorem.

## Rule names

Typing steps use the actual `NuTerms` constructors:

- `[TYPE-VAR]` = `⊢``
- `[TYPE-LAM]` = `⊢ƛ`
- `[TYPE-APP]` = `⊢·`
- `[TYPE-TLAM]` = `⊢Λ`
- `[TYPE-NU]` = `⊢ν`
- `[TYPE-CONST]` = `⊢$`
- `[TYPE-CAST]` = `⊢⟨⟩`

Coercion typing uses `[CAST-ID]`, `[CAST-FUN]`, `[CAST-TAG]`,
`[CAST-UNTAG]`, `[CAST-SEAL]`, `[CAST-UNSEAL]`, `[CAST-GEN]`, and
`[CAST-INST]`. Checked type-narrowing trees use `[N-*]`; their mutually
defined contravariant premises use `[W-*]`. For example, `[N-FUN]` has a
widening domain premise and a narrowing codomain premise, while `[N-GEN]`
introduces an `α := ★` context entry.
The separately stored type-imprecision witnesses use
the corresponding constructors
`[IMP-ID★]`, `[IMP-ID-VAR]`, `[IMP-ID-BASE]`, `[IMP-FUN]`, `[IMP-ALL]`,
`[IMP-TAG-BASE]`, `[IMP-TAG-VAR]`, and `[IMP-NU]` from `ImprecisionWf`.
The checked example record contains both proofs; rendering never recompiles
one from the other.

`[LR-OBLIGATION]` means the proposition

    TermRelation p I k [] [] imprecise-term precise-term

for arbitrary initial interpretation `I` and index `k`.

`[LR-PROVED]` marks the same proposition when the corresponding example
module exports a checked inhabitant.

## Shared checked derivations

The following derived names abbreviate recurrent trees. Every premise and
conclusion occupies its own line; each horizontal line carries the rule that
produces the conclusion beneath it.

    x : A ⊢ x : A
    --------------------------- [TYPE-LAM]
    ⊢ λx : A. x : A → A

    X; x : X ⊢ x : X
    --------------------------- [TYPE-LAM]
    X ⊢ λx : X. x : X → X
    --------------------------- [TYPE-TLAM]
    ⊢ ΛX. λx : X. x : ∀X. X → X

    α := ★ ⊢ α! → α? : (★ → ★) ⇒ (α → α)
                                                       [CAST-TAG, CAST-UNTAG,
                                                        CAST-FUN]
    ⊢ ν α := ★ . α! → α?
        : (★ → ★) ⇒ ∀X. X → X                 [CAST-GEN, C-GEN-ID]

    α := ★ ⊢ α ♯ → α ♭ : (α → α) ⇒ (★ → ★)
                                                       [CAST-SEAL, CAST-UNSEAL,
                                                        CAST-FUN]
    ⊢ ν̅ α := ★ . α ♯ → α ♭
        : (∀X. X → X) ⇒ (★ → ★)                 [CAST-INST, C-INST-ID]

    ⊢ 0 : Nat                                          [TYPE-CONST]
    ⊢ 0 ⟨Nat!⟩ : ★                                     [CAST-TAG, TYPE-CAST,
                                                        D-NAT★]

    ⊢ ΛX. ΛY. λx : X. λy : Y. x : ∀X. ∀Y. X → Y → X
                                                       [TYPE-VAR, TYPE-LAM,
                                                        TYPE-LAM, TYPE-TLAM,
                                                        TYPE-TLAM, D-K]
    ⊢ λx : ★. λy : ★. x : ★ → ★ → ★              [TYPE-VAR, TYPE-LAM,
                                                        TYPE-LAM, D-K★]

The recurrent checked narrowing trees are printed below. A contravariant
function-domain premise is genuinely a widening judgment, hence its `⊑`;
all other lines are narrowing judgments. Every line includes the active
type/seal context.

    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → α : α! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ ★ → ★ ⊒ ∀X. X → X : ν α := ★ . α! → α?

    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?

    -------------------------------- [W-TAG]
    ∅ ⊢ Nat ⊑ ★ : Nat!
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    -------------------------------- [N-FUN]
    ∅ ⊢ ★ → ★ ⊒ Nat → Nat : Nat! → Nat?

    -------------------------------- [N-ID-BASE]
    ∅ ⊢ Nat ⊒ Nat : id[Nat]

    -------------------------------- [N-ID★]
    ∅ ⊢ ★ ⊒ ★ : id[★]

    -------------------------------- [W-ID-VAR]
    X ⊢ X ⊑ X : id[X]
    -------------------------------- [N-ID-VAR]
    X ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X ⊢ X → X ⊒ X → X : id[X] → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ ∀X. X → X ⊒ ∀X. X → X : ∀X. id[X] → id[X]

## Labeled programs

### Program (a)

    (ν α := Nat. (ΛX. λx : X. x) @ α
       ⟨α ♯ → α ♭⟩) 0

    ⊢ ΛX. λx : X. x : ∀X. X → X                    [D-ID]
    ⊢ ν α := Nat. ... : Nat → Nat                  [CAST-SEAL,
                                                        CAST-UNSEAL,
                                                        CAST-FUN, TYPE-NU]
    ⊢ (...) 0 : Nat                                     [TYPE-CONST,
                                                        TYPE-APP]

### Program (b)

    (ν α := Nat. (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
       @ α ⟨α ♯ → α ♭⟩) 0

    ⊢ λx : ★. x : ★ → ★                                [D-ID★]
    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩ : ∀X. X → X
                                                       [C-GEN-ID, TYPE-CAST]
    ⊢ ν α := Nat. ... : Nat → Nat                  [TYPE-NU]
    ⊢ (...) 0 : Nat                                     [TYPE-CONST,
                                                        TYPE-APP]

### Program (c)

    (ν α := Nat. (λx : ★. 0 ⟨Nat!⟩)
       ⟨ν α := ★ . α! → α?⟩
       @ α ⟨α ♯ → α ♭⟩) 0

    ⊢ 0 ⟨Nat!⟩ : ★                                     [D-NAT★]
    ⊢ λx : ★. 0 ⟨Nat!⟩ : ★ → ★                       [TYPE-LAM]
    ⊢ (...) ⟨ν α := ★ . α! → α?⟩ : ∀X. X → X       [C-GEN-ID,
                                                        TYPE-CAST]
    ⊢ ν α := Nat. ... : Nat → Nat                  [TYPE-NU]
    ⊢ (...) 0 : Nat                                     [TYPE-CONST,
                                                        TYPE-APP]

### Program (d)

    (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
      ⟨ν̅ α := ★ . α ♯ → α ♭⟩ (0 ⟨Nat!⟩)

    ⊢ λx : ★. x : ★ → ★                            [D-ID★]
    ⊢ (...) ⟨ν α := ★ . ...⟩ : ∀X. X → X              [C-GEN-ID,
                                                        TYPE-CAST]
    ⊢ (...) ⟨ν̅ α := ★ . ...⟩ : ★ → ★                    [C-INST-ID,
                                                        TYPE-CAST]
    ⊢ 0 ⟨Nat!⟩ : ★                                     [D-NAT★]
    ⊢ (...) (0 ⟨Nat!⟩) : ★                             [TYPE-APP]

## Labeled relations

### Relation (e)

    ⊢ λx : ★. x : ★ → ★
    ⊢ ΛX. λx : X. x : ∀X. X → X
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → α : α! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ ★ → ★ ⊒ ∀X. X → X : ν α := ★ . α! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ λx : ★. x ⊒ ΛX. λx : X. x : ν α := ★ . α! → α?

### Relation (f)

    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩ : ∀X. X → X
    ⊢ ΛX. λx : X. x : ∀X. X → X
    -------------------------------- [W-ID-VAR]
    X ⊢ X ⊑ X : id[X]
    -------------------------------- [N-ID-VAR]
    X ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X ⊢ X → X ⊒ X → X : id[X] → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ ∀X. X → X ⊒ ∀X. X → X : ∀X. id[X] → id[X]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
      ⊒ ΛX. λx : X. x : ∀X. id[X] → id[X]

### Relation (g), corrected

The note prints the imprecise endpoint at universal type after an
instantiation cast. That cast actually produces `★ → ★`.

    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩ : ★ → ★
    ⊢ ΛX. λx : X. x : ∀X. X → X
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → α : α! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ ★ → ★ ⊒ ∀X. X → X : ν α := ★ . α! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
      ⊒ ΛX. λx : X. x : ν α := ★ . α! → α?

The additional reduced states displayed in Cambridge26 are:

    (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
      ⟨ν̅ α := ★ . α ♯ → α ♭⟩
    —→ ν α := ★. ((λx : ★. x) ⟨ν α := ★ . α! → α?⟩)
         @ α ⟨α ♯ → α ♭⟩
    —→ (λx : ★. x) ⟨α! → α?⟩ ⟨α ♯ → α ♭⟩

## Numbered examples

### Example 1

    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩ : ★ → ★
    ⊢ ΛX. λx : X. x : ∀X. X → X
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → α : α! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ ★ → ★ ⊒ ∀X. X → X : ν α := ★ . α! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
      ⊒ ΛX. λx : X. x : ν α := ★ . α! → α?

    —→ ν α := ★. ((λx : ★. x) ⟨ν α := ★ . α! → α?⟩)
         @ α ⟨α ♯ → α ♭⟩
    —→ (λx : ★. x) ⟨α! → α?⟩ ⟨α ♯ → α ♭⟩

### Example 2

    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩ : ★ → ★
    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩ : ∀X. X → X
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → α : α! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ ★ → ★ ⊒ ∀X. X → X : ν α := ★ . α! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
      ⊒ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
      : ν α := ★ . α! → α?

    —→ ν α := ★. ((λx : ★. x) ⟨ν α := ★ . α! → α?⟩)
         @ α ⟨α ♯ → α ♭⟩
    —→ (λx : ★. x) ⟨α! → α?⟩ ⟨α ♯ → α ♭⟩

### Example 3

The open `extend` state in the note is closed here by the compiled type
application.

    ⊢ λx : ★. x : ★ → ★
    ⊢ ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩ : Nat → Nat
    -------------------------------- [W-TAG]
    ∅ ⊢ Nat ⊑ ★ : Nat!
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    -------------------------------- [N-FUN]
    ∅ ⊢ ★ → ★ ⊒ Nat → Nat : Nat! → Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ λx : ★. x
      ⊒ ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩ : Nat! → Nat?

### Example 4

    ⊢ (ΛX. λx : X. x) ⟨ν̅ α := ★ . α ♯ → α ♭⟩
      : ★ → ★
    ⊢ ΛX. λx : X. x : ∀X. X → X
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → α : α! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ ★ → ★ ⊒ ∀X. X → X : ν α := ★ . α! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. λx : X. x) ⟨ν̅ α := ★ . α ♯ → α ♭⟩
      ⊒ ΛX. λx : X. x : ν α := ★ . α! → α?

    —→ ν α := ★. (ΛX. λx : X. x) @ α
         ⟨α ♯ → α ♭⟩
    —→ (λx : α. x) ⟨α ♯ → α ♭⟩

There is no `[split]` step: physical seal pairing is recorded in the world.

### Example 5

    ⊢ (λx : ★. x) ((λx : ★. x) ⟨(★ → ★)!⟩) : ★
    ⊢ (λx : Nat. x) ⟨Nat? → Nat!⟩
        ((λx : ★. x) ⟨(★ → ★)!⟩) : ★
    -------------------------------- [N-ID★]
    ∅ ⊢ ★ ⊒ ★ : id[★]
    ------------------------------------------------------ [LR-PROVED]
    ⊢ (λx : ★. x) ((λx : ★. x) ⟨(★ → ★)!⟩)
      ⊒ (λx : Nat. x) ⟨Nat? → Nat!⟩
          ((λx : ★. x) ⟨(★ → ★)!⟩) : id[★]

The failing side has the reduction states

    ((λx : Nat. x) ⟨Nat? → Nat!⟩)
      ((λx : ★. x) ⟨(★ → ★)!⟩)
    —→ ((λx : Nat. x)
          (((λx : ★. x) ⟨(★ → ★)!⟩) ⟨Nat?⟩)) ⟨Nat!⟩
    —→ blame

The tagged function replaces the unavailable second-base-type constant while
preserving the intended ground-tag mismatch.

The proof is `Example05.example-membership`. It observes that both sides time
out below fuel 3, the precise side blames at every fuel from 3 onward, and the
imprecise side returns at every fuel from 3 onward. Therefore only the blame
alternative of `ComputationsRelated.backward-return` is needed.

### Example 6

    ⊢ (λx : ★. x) ((λx : ★. x) ⟨(★ → ★)!⟩) : ★
    ⊢ (ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) ⟨Nat? → Nat!⟩
        ((λx : ★. x) ⟨(★ → ★)!⟩) : ★
    -------------------------------- [N-ID★]
    ∅ ⊢ ★ ⊒ ★ : id[★]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) ((λx : ★. x) ⟨(★ → ★)!⟩)
      ⊒ (ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩) ⟨Nat? → Nat!⟩
          ((λx : ★. x) ⟨(★ → ★)!⟩) : id[★]

After opening the precise type application, its failing side contains

    ((λx : α. x) ⟨α ♯ → α ♭⟩ ⟨Nat? → Nat!⟩)
      ((λx : ★. x) ⟨(★ → ★)!⟩)
    —↠ ((λx : α. x) ⟨α ♯ → α ♭⟩
          (((λx : ★. x) ⟨(★ → ★)!⟩) ⟨Nat?⟩)) ⟨Nat!⟩
    —→ blame

### Example 7

    ⊢ ν α := Nat. (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        @ α ⟨α ♯ → α ♭⟩ : Nat → Nat
    ⊢ ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩ : Nat → Nat
    -------------------------------- [W-ID-BASE]
    ∅ ⊢ Nat ⊑ Nat : id[Nat]
    -------------------------------- [N-ID-BASE]
    ∅ ⊢ Nat ⊒ Nat : id[Nat]
    -------------------------------- [N-FUN]
    ∅ ⊢ Nat → Nat ⊒ Nat → Nat : id[Nat] → id[Nat]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ ν α := Nat. (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        @ α ⟨α ♯ → α ♭⟩
      ⊒ ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩ : id[Nat] → id[Nat]

Both sides open their compiled type applications; the next aligned state is

    α := Nat ⊢
      (λx : ★. x) ⟨α! → α?⟩ ⟨α ♯ → α ♭⟩
      ⊒ (λx : α. x) ⟨α ♯ → α ♭⟩
      : id[Nat] → id[Nat]

### Example 8

    ⊢ (ν α := ★. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) (0 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ν α := ★. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) (0 ⟨Nat!⟩)
      ⊒ (ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩) 0 : Nat?

The reduced terms retained from the note are

    α := (★ ⊒ Nat : Nat?) ⊢
      (λx : α. x) ⟨α ♯ → α ♭⟩ (0 ⟨Nat!⟩)
      ⊒ (λx : α. x) ⟨α ♯ → α ♭⟩ 0 : Nat?
    —↠ 0 ⟨Nat!⟩ ⊒ 0 : Nat?

### Example 9

    ⊢ (λx : ★. x) (0 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) (0 ⟨Nat!⟩)
      ⊒ (ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩) 0 : Nat?

    —↠ 0 ⟨Nat!⟩ ⊒ 0 : Nat?

### Example 10

    ⊢ (λx : ★. x) (0 ⟨Nat!⟩) : ★
    ⊢ (ΛX. λx : X. x) ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        (0 ⟨Nat!⟩) : ★
    -------------------------------- [N-ID★]
    ∅ ⊢ ★ ⊒ ★ : id[★]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) (0 ⟨Nat!⟩)
      ⊒ (ΛX. λx : X. x) ⟨ν̅ α := ★ . α ♯ → α ♭⟩
          (0 ⟨Nat!⟩) : id[★]

    —↠ 0 ⟨Nat!⟩ ⊒ 0 ⟨Nat!⟩ : id[★]

### Example 11

    ⊢ (ΛX. λx : X. x) ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        (0 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. λx : X. x) ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        (0 ⟨Nat!⟩)
      ⊒ (ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩) 0 : Nat?

    —↠ 0 ⟨Nat!⟩ ⊒ 0 : Nat?

### Example 12

    ⊢ (ν α := Nat. (ΛX. λx : X. x)
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        ⟨ν α := ★ . α! → α?⟩ @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    ⊢ (ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    -------------------------------- [N-ID-BASE]
    ∅ ⊢ Nat ⊒ Nat : id[Nat]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ν α := Nat. (ΛX. λx : X. x)
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        ⟨ν α := ★ . α! → α?⟩ @ α
        ⟨α ♯ → α ♭⟩) 0
      ⊒ (ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩) 0 : id[Nat]

    —↠ 0 ⊒ 0 : id[Nat]

### Example 13

    ⊢ (ΛX. λx : X. x) ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩ (0 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. λx : X. x) ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩ (0 ⟨Nat!⟩)
      ⊒ (ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩) 0 : Nat?

    —↠ 0 ⟨Nat!⟩ ⊒ 0 : Nat?

### Example 14

    ⊢ (ν α := Nat. (ΛX. λx : X. x)
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        ⟨ν α := ★ . α! → α?⟩ @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    ⊢ (ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    -------------------------------- [N-ID-BASE]
    ∅ ⊢ Nat ⊒ Nat : id[Nat]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ν α := Nat. (ΛX. λx : X. x)
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
        ⟨ν α := ★ . α! → α?⟩ @ α
        ⟨α ♯ → α ♭⟩) 0
      ⊒ (ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩) 0 : id[Nat]

    —↠ 0 ⊒ 0 : id[Nat]

### Example 15

    ⊢ (ν α := Nat. (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        @ α ⟨α ♯ → α ♭⟩) 0 : Nat
    ⊢ (ν α := Nat. (ΛX. λx : X. x) @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    -------------------------------- [N-ID-BASE]
    ∅ ⊢ Nat ⊒ Nat : id[Nat]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ν α := Nat. (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        @ α ⟨α ♯ → α ♭⟩) 0
      ⊒ (ν α := Nat. (ΛX. λx : X. x) @ α
          ⟨α ♯ → α ♭⟩) 0 : id[Nat]

    —↠ 0 ⊒ 0 : id[Nat]

### Example 16

    ⊢ (λx : ★. x) (0 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat. (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        @ α ⟨α ♯ → α ♭⟩) 0 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) (0 ⟨Nat!⟩)
      ⊒ (ν α := Nat. (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
          @ α ⟨α ♯ → α ♭⟩) 0 : Nat?

    —↠ 0 ⟨Nat!⟩ ⊒ 0 : Nat?

### Example 17

    ⊢ (λx : ★. λy : ★. x) (42 ⟨Nat!⟩) (69 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat.
        (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
          ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
        ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. λy : ★. x) (42 ⟨Nat!⟩) (69 ⟨Nat!⟩)
      ⊒ (ν α := Nat.
          (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
            ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
          ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat?

    —↠ 42 ⟨Nat!⟩ ⊒ 42 : Nat?

The checked endpoint includes both applications; the heading in the original
note omits the second one although its trace subsequently uses `69`.

### Example 18

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ν̅ β := ★ .
          α ♯ → β ♯ → α ♭⟩
        (42 ⟨Nat!⟩) (69 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat.
        (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
          ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
        ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ν̅ β := ★ .
          α ♯ → β ♯ → α ♭⟩
        (42 ⟨Nat!⟩) (69 ⟨Nat!⟩)
      ⊒ (ν α := Nat.
          (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
            ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
          ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat?

    —↠ 42 ⟨Nat!⟩ ⊒ 42 : Nat?

### Example 18b

    ⊢ (ν α := Nat.
        (ν β := Nat. (λx : ★. λy : ★. x)
          ⟨ν α := ★ . ν β := ★ .
            α! → β! → α?⟩ @ β
          ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
        ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat
    ⊢ (ν α := Nat.
        (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
          ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
        ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat
    -------------------------------- [N-ID-BASE]
    ∅ ⊢ Nat ⊒ Nat : id[Nat]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ν α := Nat.
        (ν β := Nat. (λx : ★. λy : ★. x)
          ⟨ν α := ★ . ν β := ★ .
            α! → β! → α?⟩ @ β
          ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
        ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69
      ⊒ (ν α := Nat.
          (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
            ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
          ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : id[Nat]

    —↠ 42 ⊒ 42 : id[Nat]

### Example 19

    ⊢ (λx : ★. (λy : ★. y) x) (0 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat.
        (ΛX. λx : X. (ν β := X. (ΛY. λy : Y. y) @ β
          ⟨β ♯ → β ♭⟩) x) @ α
        ⟨α ♯ → α ♭⟩) 0 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. (λy : ★. y) x) (0 ⟨Nat!⟩)
      ⊒ (ν α := Nat.
          (ΛX. λx : X. (ν β := X. (ΛY. λy : Y. y) @ β
            ⟨β ♯ → β ♭⟩) x) @ α
          ⟨α ♯ → α ♭⟩) 0 : Nat?

    —↠ 0 ⟨Nat!⟩ ⊒ 0 : Nat?

### Example 20

    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩ : ★ → ★
    ⊢ ΛX. λx : X. x : ∀X. X → X
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → α : α! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ ★ → ★ ⊒ ∀X. X → X : ν α := ★ . α! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
      ⊒ ΛX. λx : X. x : ν α := ★ . α! → α?

### Example 21

    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩ : ★ → ★
    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩ : ∀X. X → X
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → α : α! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ ★ → ★ ⊒ ∀X. X → X : ν α := ★ . α! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
        ⟨ν̅ α := ★ . α ♯ → α ♭⟩
      ⊒ (λx : ★. x) ⟨ν α := ★ . α! → α?⟩
      : ν α := ★ . α! → α?

Again, there is no core `[split]` or `[extend]` rule.

### Example 22

This example has two type-imprecision derivations and no term endpoints.

First derivation:

    -------------------------------- [W-TAG]
    α := ★, X ⊢ α ⊑ ★ : α!
    -------------------------------- [W-ID-VAR]
    α := ★, X ⊢ X ⊑ X : id[X]
    -------------------------------- [N-UNTAG]
    α := ★, X ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ X → ★ ⊒ X → α : id[X] → α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ ★ → X → ★ ⊒ α → X → α
      : α! → id[X] → α?
    -------------------------------- [N-ALL]
    α := ★ ⊢ ∀X. ★ → X → ★ ⊒ ∀X. α → X → α
      : ∀X. α! → id[X] → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ ∀X. ★ → X → ★ ⊒ ∀X. ∀Y. X → Y → X
      : ν α := ★ . ∀X. α! → id[X] → α?

Second derivation:

    -------------------------------- [W-ID-VAR]
    X, α := ★ ⊢ X ⊑ X : id[X]
    -------------------------------- [W-TAG]
    X, α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-ID-VAR]
    X, α := ★ ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ ★ → X ⊒ α → X : α! → id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ X → ★ → X ⊒ X → α → X
      : id[X] → α! → id[X]
    -------------------------------- [N-GEN]
    X ⊢ X → ★ → X ⊒ ∀Y. X → Y → X
      : ν α := ★ . id[X] → α! → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ ∀X. X → ★ → X ⊒ ∀X. ∀Y. X → Y → X
      : ∀X. ν α := ★ . id[X] → α! → id[X]

Both trees are checked by `poly-k-to-dynamic-first` and
`poly-k-to-dynamic-second` in `Common.agda`.

## Independent-binder K examples

The K suite makes the two type abstractions independently gradual. Its four
vertices are:

    PP = ∀X. ∀Y. X → Y → X
    XD = ∀X. ★ → X → ★
    YD = ∀X. X → ★ → X
    DD = ★ → ★ → ★

Here `XD` means that K's result-producing `X` binder is dynamic; `YD` means
that only the discarded-argument `Y` binder is dynamic.

### Shared K cast derivations

Each derived cast name expands to the following named coercion-typing steps.

    α ♯                                           [CAST-SEAL]
    id[X]                                          [CAST-ID]
    α ♭                                           [CAST-UNSEAL]
    α ♯ → id[X] → α ♭                     [CAST-FUN, CAST-FUN]
    ∀X. α ♯ → id[X] → α ♭                 [CAST-ALL]
    ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭
                                                    [CAST-INST, K-INST-X]

    α!                                             [CAST-TAG]
    id[X]                                          [CAST-ID]
    α?                                             [CAST-UNTAG]
    α! → id[X] → α?                         [CAST-FUN, CAST-FUN]
    ∀X. α! → id[X] → α?                     [CAST-ALL]
    ν α := ★ . ∀X. α! → id[X] → α?
                                                     [CAST-GEN, K-GEN-X]

    id[X]                                          [CAST-ID]
    α ♯                                           [CAST-SEAL]
    id[X]                                          [CAST-ID]
    id[X] → α ♯ → id[X]                   [CAST-FUN, CAST-FUN]
    ν̅ α := ★ .
      id[X] → α ♯ → id[X]                      [CAST-INST]
    ∀X. ν̅ α := ★ . ...                 [CAST-ALL, K-INST-Y]

    id[X]                                          [CAST-ID]
    α!                                             [CAST-TAG]
    id[X]                                          [CAST-ID]
    id[X] → α! → id[X]                       [CAST-FUN, CAST-FUN]
    ν α := ★ .
      id[X] → α! → id[X]                          [CAST-GEN]
    ∀X. ν α := ★ . ...                  [CAST-ALL, K-GEN-Y]

After one binder is already dynamic, the remaining edge casts are:

    id[★] → α ♯ → id[★]                     [CAST-ID, CAST-SEAL,
                                                     CAST-ID, CAST-FUN,
                                                     CAST-FUN]
    ν̅ α := ★ . id[★] → α ♯ → id[★]
                                                [CAST-INST, K-INST-Y-AFTER-X]

    id[★] → α! → id[★]                         [CAST-ID, CAST-TAG,
                                                     CAST-ID, CAST-FUN,
                                                     CAST-FUN]
    ν α := ★ . id[★] → α! → id[★]
                                                   [CAST-GEN, K-GEN-Y-AFTER-X]

    α ♯ → id[★] → α ♭                     [CAST-SEAL, CAST-ID,
                                                     CAST-UNSEAL,
                                                     CAST-FUN, CAST-FUN]
    ν̅ α := ★ . α ♯ → id[★] → α ♭
                                                [CAST-INST, K-INST-X-AFTER-Y]

    α! → id[★] → α?                         [CAST-TAG, CAST-ID,
                                                     CAST-UNTAG,
                                                     CAST-FUN, CAST-FUN]
    ν α := ★ . α! → id[★] → α?
                                                   [CAST-GEN, K-GEN-X-AFTER-Y]

The narrowing square itself, including the coercions, is

    -------------------------------- [W-TAG]
    α := ★, X ⊢ α ⊑ ★ : α!
    -------------------------------- [W-ID-VAR]
    α := ★, X ⊢ X ⊑ X : id[X]
    -------------------------------- [N-UNTAG]
    α := ★, X ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ X → ★ ⊒ X → α : id[X] → α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ ★ → X → ★ ⊒ α → X → α
      : α! → id[X] → α?
    -------------------------------- [N-ALL]
    α := ★ ⊢ XD ⊒ ∀X. α → X → α : ∀X. α! → id[X] → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ XD ⊒ PP : ν α := ★ . ∀X. α! → id[X] → α?
                                      [poly-k-to-dynamic-first-narrowing]
    -------------------------------- [W-ID-VAR]
    X, α := ★ ⊢ X ⊑ X : id[X]
    -------------------------------- [W-TAG]
    X, α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-ID-VAR]
    X, α := ★ ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ ★ → X ⊒ α → X : α! → id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ X → ★ → X ⊒ X → α → X
      : id[X] → α! → id[X]
    -------------------------------- [N-GEN]
    X ⊢ X → ★ → X ⊒ ∀Y. X → Y → X
      : ν α := ★ . id[X] → α! → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ YD ⊒ PP : ∀X. ν α := ★ . id[X] → α! → id[X]
                                      [poly-k-to-dynamic-second-narrowing]
    -------------------------------- [W-ID★]
    α := ★ ⊢ ★ ⊑ ★ : id[★]
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-ID★]
    α := ★ ⊢ ★ ⊒ ★ : id[★]
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → ★ : α! → id[★]
    -------------------------------- [N-FUN]
    α := ★ ⊢ DD ⊒ ★ → α → ★ : id[★] → α! → id[★]
    -------------------------------- [N-GEN]
    ∅ ⊢ DD ⊒ XD : ν α := ★ . id[★] → α! → id[★]
                                      [X-dynamic-to-dynamic-narrowing]
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [W-ID★]
    α := ★ ⊢ ★ ⊑ ★ : id[★]
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ ★ → α : id[★] → α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ DD ⊒ α → ★ → α : α! → id[★] → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ DD ⊒ YD : ν α := ★ . α! → id[★] → α?
                                      [Y-dynamic-to-dynamic-narrowing]
    -------------------------------- [W-TAG]
    α := ★, β := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [W-TAG]
    α := ★, β := ★ ⊢ β ⊑ ★ : β!
    -------------------------------- [N-UNTAG]
    α := ★, β := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★, β := ★ ⊢ ★ → ★ ⊒ β → α : β! → α?
    -------------------------------- [N-FUN]
    α := ★, β := ★ ⊢ DD ⊒ α → β → α : α! → β! → α?
    -------------------------------- [N-GEN]
    α := ★ ⊢ DD ⊒ ∀X. α → X → α
      : ν β := ★ . α! → β! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ DD ⊒ PP : ν α := ★ . ν β := ★ . α! → β! → α?
                                      [poly-k-to-dynamic-narrowing]

Each following block is a line-wrapped rendition of the corresponding checked
`KRenderings.exampleNN` value. The four abbreviations above replace their
fully expanded types only to keep the catalogue readable.

### K Example 1: raw `XD ⊒ PP`

    ⊢ ΛX. λx : ★. λy : X. x : XD
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-TAG]
    α := ★, X ⊢ α ⊑ ★ : α!
    -------------------------------- [W-ID-VAR]
    α := ★, X ⊢ X ⊑ X : id[X]
    -------------------------------- [N-UNTAG]
    α := ★, X ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ X → ★ ⊒ X → α : id[X] → α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ ★ → X → ★ ⊒ α → X → α
      : α! → id[X] → α?
    -------------------------------- [N-ALL]
    α := ★ ⊢ XD ⊒ ∀X. α → X → α : ∀X. α! → id[X] → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ XD ⊒ PP : ν α := ★ . ∀X. α! → id[X] → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ ΛX. λx : ★. λy : X. x
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ν α := ★ . ∀X. α! → id[X] → α?

### K Example 2: raw `YD ⊒ PP`

    ⊢ ΛX. λx : X. λy : ★. x : YD
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-ID-VAR]
    X, α := ★ ⊢ X ⊑ X : id[X]
    -------------------------------- [W-TAG]
    X, α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-ID-VAR]
    X, α := ★ ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ ★ → X ⊒ α → X : α! → id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ X → ★ → X ⊒ X → α → X
      : id[X] → α! → id[X]
    -------------------------------- [N-GEN]
    X ⊢ X → ★ → X ⊒ ∀Y. X → Y → X
      : ν α := ★ . id[X] → α! → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ YD ⊒ PP : ∀X. ν α := ★ . id[X] → α! → id[X]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ ΛX. λx : X. λy : ★. x
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ∀X. ν α := ★ . id[X] → α! → id[X]

The restored lambda annotations make the two raw gradual K terms visibly
different.

### K Example 3: raw `DD ⊒ XD`

    ⊢ λx : ★. λy : ★. x : DD
    ⊢ ΛX. λx : ★. λy : X. x : XD
    -------------------------------- [W-ID★]
    α := ★ ⊢ ★ ⊑ ★ : id[★]
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-ID★]
    α := ★ ⊢ ★ ⊒ ★ : id[★]
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ α → ★ : α! → id[★]
    -------------------------------- [N-FUN]
    α := ★ ⊢ DD ⊒ ★ → α → ★ : id[★] → α! → id[★]
    -------------------------------- [N-GEN]
    ∅ ⊢ DD ⊒ XD : ν α := ★ . id[★] → α! → id[★]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ λx : ★. λy : ★. x
      ⊒ ΛX. λx : ★. λy : X. x
      : ν α := ★ . id[★] → α! → id[★]

### K Example 4: raw `DD ⊒ YD`

    ⊢ λx : ★. λy : ★. x : DD
    ⊢ ΛX. λx : X. λy : ★. x : YD
    -------------------------------- [W-TAG]
    α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [W-ID★]
    α := ★ ⊢ ★ ⊑ ★ : id[★]
    -------------------------------- [N-UNTAG]
    α := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ ★ → ★ ⊒ ★ → α : id[★] → α?
    -------------------------------- [N-FUN]
    α := ★ ⊢ DD ⊒ α → ★ → α : α! → id[★] → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ DD ⊒ YD : ν α := ★ . α! → id[★] → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ λx : ★. λy : ★. x
      ⊒ ΛX. λx : X. λy : ★. x
      : ν α := ★ . α! → id[★] → α?

### K Example 5: raw diagonal `DD ⊒ PP`

    ⊢ λx : ★. λy : ★. x : DD
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-TAG]
    α := ★, β := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [W-TAG]
    α := ★, β := ★ ⊢ β ⊑ ★ : β!
    -------------------------------- [N-UNTAG]
    α := ★, β := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★, β := ★ ⊢ ★ → ★ ⊒ β → α : β! → α?
    -------------------------------- [N-FUN]
    α := ★, β := ★ ⊢ DD ⊒ α → β → α : α! → β! → α?
    -------------------------------- [N-GEN]
    α := ★ ⊢ DD ⊒ ∀X. α → X → α
      : ν β := ★ . α! → β! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ DD ⊒ PP : ν α := ★ . ν β := ★ . α! → β! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ λx : ★. λy : ★. x
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ν α := ★ . ν β := ★ . α! → β! → α?

### K Example 6: instantiate only X

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩ : XD
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-TAG]
    α := ★, X ⊢ α ⊑ ★ : α!
    -------------------------------- [W-ID-VAR]
    α := ★, X ⊢ X ⊑ X : id[X]
    -------------------------------- [N-UNTAG]
    α := ★, X ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ X → ★ ⊒ X → α : id[X] → α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ ★ → X → ★ ⊒ α → X → α
      : α! → id[X] → α?
    -------------------------------- [N-ALL]
    α := ★ ⊢ XD ⊒ ∀X. α → X → α : ∀X. α! → id[X] → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ XD ⊒ PP : ν α := ★ . ∀X. α! → id[X] → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ν α := ★ . ∀X. α! → id[X] → α?

### K Example 7: instantiate only Y

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ .
          id[X] → α ♯ → id[X]⟩ : YD
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-ID-VAR]
    X, α := ★ ⊢ X ⊑ X : id[X]
    -------------------------------- [W-TAG]
    X, α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-ID-VAR]
    X, α := ★ ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ ★ → X ⊒ α → X : α! → id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ X → ★ → X ⊒ X → α → X
      : id[X] → α! → id[X]
    -------------------------------- [N-GEN]
    X ⊢ X → ★ → X ⊒ ∀Y. X → Y → X
      : ν α := ★ . id[X] → α! → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ YD ⊒ PP : ∀X. ν α := ★ . id[X] → α! → id[X]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ∀X. ν α := ★ . id[X] → α! → id[X]

### K Example 8: generalize and re-instantiate X

    ⊢ (ΛX. λx : ★. λy : X. x)
        ⟨ν α := ★ . ∀X. α! → id[X] → α?⟩
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩ : XD
    ⊢ (ΛX. λx : ★. λy : X. x)
        ⟨ν α := ★ . ∀X. α! → id[X] → α?⟩ : PP
    -------------------------------- [W-TAG]
    α := ★, X ⊢ α ⊑ ★ : α!
    -------------------------------- [W-ID-VAR]
    α := ★, X ⊢ X ⊑ X : id[X]
    -------------------------------- [N-UNTAG]
    α := ★, X ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ X → ★ ⊒ X → α : id[X] → α?
    -------------------------------- [N-FUN]
    α := ★, X ⊢ ★ → X → ★ ⊒ α → X → α
      : α! → id[X] → α?
    -------------------------------- [N-ALL]
    α := ★ ⊢ XD ⊒ ∀X. α → X → α : ∀X. α! → id[X] → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ XD ⊒ PP : ν α := ★ . ∀X. α! → id[X] → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. λx : ★. λy : X. x)
        ⟨ν α := ★ . ∀X. α! → id[X] → α?⟩
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
      ⊒ (ΛX. λx : ★. λy : X. x)
          ⟨ν α := ★ . ∀X. α! → id[X] → α?⟩
      : ν α := ★ . ∀X. α! → id[X] → α?

### K Example 9: generalize and re-instantiate Y

    ⊢ (ΛX. λx : X. λy : ★. x)
        ⟨∀X. ν α := ★ . id[X] → α! → id[X]⟩
        ⟨∀X. ν̅ α := ★ .
          id[X] → α ♯ → id[X]⟩ : YD
    ⊢ (ΛX. λx : X. λy : ★. x)
        ⟨∀X. ν α := ★ . id[X] → α! → id[X]⟩ : PP
    -------------------------------- [W-ID-VAR]
    X, α := ★ ⊢ X ⊑ X : id[X]
    -------------------------------- [W-TAG]
    X, α := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [N-ID-VAR]
    X, α := ★ ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ ★ → X ⊒ α → X : α! → id[X]
    -------------------------------- [N-FUN]
    X, α := ★ ⊢ X → ★ → X ⊒ X → α → X
      : id[X] → α! → id[X]
    -------------------------------- [N-GEN]
    X ⊢ X → ★ → X ⊒ ∀Y. X → Y → X
      : ν α := ★ . id[X] → α! → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ YD ⊒ PP : ∀X. ν α := ★ . id[X] → α! → id[X]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. λx : X. λy : ★. x)
        ⟨∀X. ν α := ★ . id[X] → α! → id[X]⟩
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
      ⊒ (ΛX. λx : X. λy : ★. x)
          ⟨∀X. ν α := ★ . id[X] → α! → id[X]⟩
      : ∀X. ν α := ★ . id[X] → α! → id[X]

### K Example 10: X-only round trip

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
        ⟨ν α := ★ . ∀X. α! → id[X] → α?⟩ : PP
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ X ⊑ X : id[X]
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ Y ⊑ Y : id[Y]
    -------------------------------- [N-ID-VAR]
    X, Y ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ Y → X ⊒ Y → X : id[Y] → id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ X → Y → X ⊒ X → Y → X : id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    X ⊢ ∀Y. X → Y → X ⊒ ∀Y. X → Y → X
      : ∀Y. id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ PP ⊒ PP : ∀X. ∀Y. id[X] → id[Y] → id[X]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
        ⟨ν α := ★ . ∀X. α! → id[X] → α?⟩
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ∀X. ∀Y. id[X] → id[Y] → id[X]

### K Example 11: Y-only round trip

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
        ⟨∀X. ν α := ★ . id[X] → α! → id[X]⟩ : PP
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ X ⊑ X : id[X]
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ Y ⊑ Y : id[Y]
    -------------------------------- [N-ID-VAR]
    X, Y ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ Y → X ⊒ Y → X : id[Y] → id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ X → Y → X ⊒ X → Y → X : id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    X ⊢ ∀Y. X → Y → X ⊒ ∀Y. X → Y → X
      : ∀Y. id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ PP ⊒ PP : ∀X. ∀Y. id[X] → id[Y] → id[X]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
        ⟨∀X. ν α := ★ . id[X] → α! → id[X]⟩
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ∀X. ∀Y. id[X] → id[Y] → id[X]

### K Example 12: instantiate X, then Y

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
        ⟨ν̅ α := ★ . id[★] → α ♯ → id[★]⟩ : DD
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-TAG]
    α := ★, β := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [W-TAG]
    α := ★, β := ★ ⊢ β ⊑ ★ : β!
    -------------------------------- [N-UNTAG]
    α := ★, β := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★, β := ★ ⊢ ★ → ★ ⊒ β → α : β! → α?
    -------------------------------- [N-FUN]
    α := ★, β := ★ ⊢ DD ⊒ α → β → α : α! → β! → α?
    -------------------------------- [N-GEN]
    α := ★ ⊢ DD ⊒ ∀X. α → X → α
      : ν β := ★ . α! → β! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ DD ⊒ PP : ν α := ★ . ν β := ★ . α! → β! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
        ⟨ν̅ α := ★ . id[★] → α ♯ → id[★]⟩
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ν α := ★ . ν β := ★ . α! → β! → α?

### K Example 13: instantiate Y, then X

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
        ⟨ν̅ α := ★ . α ♯ → id[★] → α ♭⟩ : DD
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-TAG]
    α := ★, β := ★ ⊢ α ⊑ ★ : α!
    -------------------------------- [W-TAG]
    α := ★, β := ★ ⊢ β ⊑ ★ : β!
    -------------------------------- [N-UNTAG]
    α := ★, β := ★ ⊢ ★ ⊒ α : α?
    -------------------------------- [N-FUN]
    α := ★, β := ★ ⊢ ★ → ★ ⊒ β → α : β! → α?
    -------------------------------- [N-FUN]
    α := ★, β := ★ ⊢ DD ⊒ α → β → α : α! → β! → α?
    -------------------------------- [N-GEN]
    α := ★ ⊢ DD ⊒ ∀X. α → X → α
      : ν β := ★ . α! → β! → α?
    -------------------------------- [N-GEN]
    ∅ ⊢ DD ⊒ PP : ν α := ★ . ν β := ★ . α! → β! → α?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
        ⟨ν̅ α := ★ . α ♯ → id[★] → α ♭⟩
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ν α := ★ . ν β := ★ . α! → β! → α?

### K Example 14: dynamic X, precise Y

    ⊢ (ν α := Nat. (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩ @ α
        ⟨id[★] → α ♯ → id[★]⟩)
        (42 ⟨Nat!⟩) 69 : ★
    ⊢ (ν α := Nat.
        (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
          ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
        ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ν α := Nat. (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩ @ α
        ⟨id[★] → α ♯ → id[★]⟩) (42 ⟨Nat!⟩) 69
      ⊒ (ν α := Nat.
          (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
            ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
          ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat?

### K Example 15: precise X, dynamic Y

    ⊢ (ν α := Nat. (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ .
          id[X] → α ♯ → id[X]⟩ @ α
        ⟨α ♯ → id[★] → α ♭⟩)
        42 (69 ⟨Nat!⟩) : Nat
    ⊢ (ν α := Nat.
        (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
          ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
        ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat
    -------------------------------- [N-ID-BASE]
    ∅ ⊢ Nat ⊒ Nat : id[Nat]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ν α := Nat. (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ .
          id[X] → α ♯ → id[X]⟩ @ α
        ⟨α ♯ → id[★] → α ♭⟩) 42 (69 ⟨Nat!⟩)
      ⊒ (ν α := Nat.
          (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
            ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
          ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : id[Nat]

Thus changing only Y's precision does not change the result type of K.

### K Example 16: apply X-then-Y dynamic K

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
        ⟨ν̅ α := ★ . id[★] → α ♯ → id[★]⟩
        (42 ⟨Nat!⟩) (69 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat.
        (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
          ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
        ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
        ⟨ν̅ α := ★ . id[★] → α ♯ → id[★]⟩
        (42 ⟨Nat!⟩) (69 ⟨Nat!⟩)
      ⊒ (ν α := Nat.
          (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
            ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
          ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat?

### K Example 17: apply Y-then-X dynamic K

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
        ⟨ν̅ α := ★ . α ♯ → id[★] → α ♭⟩
        (42 ⟨Nat!⟩) (69 ⟨Nat!⟩) : ★
    ⊢ (ν α := Nat.
        (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
          ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
        ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat
    -------------------------------- [N-UNTAG]
    ∅ ⊢ ★ ⊒ Nat : Nat?
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
        ⟨ν̅ α := ★ . α ♯ → id[★] → α ♭⟩
        (42 ⟨Nat!⟩) (69 ⟨Nat!⟩)
      ⊒ (ν α := Nat.
          (ν β := Nat. (ΛX. ΛY. λx : X. λy : Y. x) @ β
            ⟨∀X. β ♯ → id[X] → β ♭⟩) @ α
          ⟨id[Nat] → α ♯ → id[Nat]⟩) 42 69 : Nat?

### K Example 18: complete X-then-Y round trip

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
        ⟨ν̅ α := ★ . id[★] → α ♯ → id[★]⟩
        ⟨ν α := ★ . id[★] → α! → id[★]⟩
        ⟨ν α := ★ . ∀X. α! → id[X] → α?⟩ : PP
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ X ⊑ X : id[X]
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ Y ⊑ Y : id[Y]
    -------------------------------- [N-ID-VAR]
    X, Y ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ Y → X ⊒ Y → X : id[Y] → id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ X → Y → X ⊒ X → Y → X : id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    X ⊢ ∀Y. X → Y → X ⊒ ∀Y. X → Y → X
      : ∀Y. id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ PP ⊒ PP : ∀X. ∀Y. id[X] → id[Y] → id[X]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨ν̅ α := ★ . ∀X. α ♯ → id[X] → α ♭⟩
        ⟨ν̅ α := ★ . id[★] → α ♯ → id[★]⟩
        ⟨ν α := ★ . id[★] → α! → id[★]⟩
        ⟨ν α := ★ . ∀X. α! → id[X] → α?⟩
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ∀X. ∀Y. id[X] → id[Y] → id[X]

### K Example 19: complete Y-then-X round trip

    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
        ⟨ν̅ α := ★ . α ♯ → id[★] → α ♭⟩
        ⟨ν α := ★ . α! → id[★] → α?⟩
        ⟨∀X. ν α := ★ . id[X] → α! → id[X]⟩ : PP
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ X ⊑ X : id[X]
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ Y ⊑ Y : id[Y]
    -------------------------------- [N-ID-VAR]
    X, Y ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ Y → X ⊒ Y → X : id[Y] → id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ X → Y → X ⊒ X → Y → X : id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    X ⊢ ∀Y. X → Y → X ⊒ ∀Y. X → Y → X
      : ∀Y. id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ PP ⊒ PP : ∀X. ∀Y. id[X] → id[Y] → id[X]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (ΛX. ΛY. λx : X. λy : Y. x)
        ⟨∀X. ν̅ α := ★ . id[X] → α ♯ → id[X]⟩
        ⟨ν̅ α := ★ . α ♯ → id[★] → α ♭⟩
        ⟨ν α := ★ . α! → id[★] → α?⟩
        ⟨∀X. ν α := ★ . id[X] → α! → id[X]⟩
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ∀X. ∀Y. id[X] → id[Y] → id[X]

### K Example 20: generalize raw dynamic K

    ⊢ (λx : ★. λy : ★. x)
        ⟨ν α := ★ . ν β := ★ . α! → β! → α?⟩ : PP
    ⊢ ΛX. ΛY. λx : X. λy : Y. x : PP
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ X ⊑ X : id[X]
    -------------------------------- [W-ID-VAR]
    X, Y ⊢ Y ⊑ Y : id[Y]
    -------------------------------- [N-ID-VAR]
    X, Y ⊢ X ⊒ X : id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ Y → X ⊒ Y → X : id[Y] → id[X]
    -------------------------------- [N-FUN]
    X, Y ⊢ X → Y → X ⊒ X → Y → X : id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    X ⊢ ∀Y. X → Y → X ⊒ ∀Y. X → Y → X
      : ∀Y. id[X] → id[Y] → id[X]
    -------------------------------- [N-ALL]
    ∅ ⊢ PP ⊒ PP : ∀X. ∀Y. id[X] → id[Y] → id[X]
    ------------------------------------------------------ [LR-OBLIGATION]
    ⊢ (λx : ★. λy : ★. x)
        ⟨ν α := ★ . ν β := ★ . α! → β! → α?⟩
      ⊒ ΛX. ΛY. λx : X. λy : Y. x
      : ∀X. ∀Y. id[X] → id[Y] → id[X]

## Status of `split` and `extend`

The rendition deliberately assigns names only to operations that belong to
the current design:

    allocate a fresh paired seal binding                    [WORLD-PAIRED-EXTENSION]
    preserve an interpretation in a larger world            [WORLD-FUTURE]

The original `[split]` annotations should elaborate to the first operation.
The original `[extend]` annotations should elaborate to the second. Neither
changes the live type-imprecision proof, and neither is a constructor of
`ValueNarrowing`.
