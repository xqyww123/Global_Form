# global_form

In a locale, everything you note is stored globally with the assumptions of the locale as
premises: a theorem `th` noted in `locale L = fixes S assumes "A S"` becomes `L ?S ⟹ th`. That is
right for a theorem that depends on the assumptions. It is a burden for a tool whose results never
depend on them, such as a datatype package: every rule of a datatype defined inside the locale
gets a premise `L ?S` whose `?S` occurs nowhere else in the rule.

This feature adds one ML operation that runs a piece of local theory construction with the
assumptions of the context taken away, so that its results are stored as in a theory target:

```ML
Local_Theory.global_form_result :
  (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory

Local_Theory.global_form :
  (local_theory -> local_theory) -> local_theory -> local_theory
```

This package changes Isabelle2026 only. It has no Isar command: it is for authors of ML tools.

## What it does

`Local_Theory.global_form f lthy` runs `f` on `lthy` with the assumptions removed from every level
of the local theory, and puts them back afterwards. While `f` runs:

- Theorems that `f` notes are stored without the assumptions as premises. Fixed variables are
  generalised as usual.
- Proofs that `f` forks are stated without the assumptions.
- Definitions stay: a locale's `defines` and earlier `Local_Theory.define` are still unfolded in
  the results.
- Contexts made from `lthy` inside `f`, including those of forked or lazy proofs that finish
  later, have no assumptions either.

In a theory target there is nothing to remove, and `global_form f` behaves as `f`.

For example, in the locale `L` above:

```ML
Local_Theory.global_form
  (Local_Theory.note ((\<^binding>\<open>b\<close>, []), @{thms refl [of S]}) #> #2)
```

stores `L.b: ?S = ?S`. Without `global_form` it would be `L ?S ⟹ ?S = ?S`.

## What `f` must respect

`f` must not use the assumptions: neither the assumed facts of the context nor theorems that
depend on them. The facts are still in the context, and a theorem proved from one still carries
the assumption as a hypothesis. When `f` notes such a theorem, or proves it in a forked proof,
Isabelle raises one of its own errors (`generalize: variable free in assumptions`,
`forall_intr: variable ... free in assumptions`, `Undeclared hyps`, or `bad hyps`); the error of a
forked proof appears when that proof is joined. `global_form` adds no check of its own. One case
goes unnoticed: a theorem that `f` passes inside a declaration (`Local_Theory.declaration`), when
its hypothesis mentions no fixed variable, is stored with the hypothesis.

A theorem with such a hypothesis that `f` only returns, through `global_form_result`, is an
ordinary local theorem again once the assumptions are back.

A context that `f` builds from scratch, for example with `Locale.init`, still has the assumptions.
Exporting between it and the contexts of `f` fails with `Outer context disagrees on assumption`.

## Sources

The Isabelle sources a version of this package was made from, with this feature and the ones it is
built on, are a tag of [isabelle-patched](https://github.com/xqyww123/isabelle-patched) named
`<Isabelle release>/global_form/<m>`, where `<m>` is the last number of the package's version:
version `2026.0.1` was made from `Isabelle2026/global_form/1`.
