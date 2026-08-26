# GTSF syntax pretty printers

`Pretty` is a general utility namespace alongside `LR` and `LR-narrow`. It
does not depend on either logical relation.

- `Strings.agda` provides string composition, generated names, and safe
  de Bruijn-name lookup.
- `Types.agda` renders types with right-associative arrows and named `∀`
  binders.
- `Coercions.agda` renders every coercion constructor. A `gen`/`inst` binder
  records the fresh assignment `α := ★`; its raw type argument is endpoint
  metadata for the whole coercion and is therefore not printed as a binder
  annotation. Bound seal/unseal actions print as `α ♯` and `α ♭` because the
  assignment in the enclosing binder already fixes their type.
- `Narrowings.agda` renders the complete checked narrowing proof tree. Every
  judgment carries its active type/seal context, and contravariant premises
  are rendered as widening judgments rather than silently flattened.
- `Terms.agda` renders every `NuTerms.Term` constructor with precedence-aware
  parentheses. A compiled type application is displayed as
  `ν α := A. L @ α ⟨c⟩`.
- `TypedTerms.agda` renders from a typing derivation and therefore restores
  the type annotation erased from each raw lambda node.
- `PrettyAll.agda` is the aggregate check.

Type-variable lookup and printed seal freshness are deliberately separate.
The former follows the term's de Bruijn context. The latter is a printing-only
name supply, so nested `ν` terms receive distinct names without shifting the
meaning of free type variables in the polymorphic value being instantiated.

`LR-narrow/Examples/Cambridge26/Renderings.agda` applies the printer directly
to the checked example records, and `Rendition.lagda.md` presents those
renderings with named derivation steps.
