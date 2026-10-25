# Lean formalization

This is one Lake project for the dependence-implication research project,
pinned to Lean **4.35.0** and mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
Question-specific modules are added through pull requests.

```text
DepDis.lean             Library entry point
Check.lean              Axiom dependencies of principal results
DepDis/Common/          Shared definitions and lemmas
DepDis/<question-id>/   Modules for an accepted question
```

The [Q1 formalization](DepDis/Q1/README.md) proves co-r.e.-completeness
of finite and unrestricted implication, the restricted fixed-consequent
hardness result, and the failure of computable counterteam-size bounds.
Import it with `import DepDis.Q1`; its declaration names use the `DepDis`
namespace. The detailed README maps the main results to their modules.

Import accepted modules from `DepDis.lean`. Add principal theorem checks
to `Check.lean` using `#print axioms DepDis.YourTheorem`.
The project's audit accepts only `propext`, `Classical.choice`, and
`Quot.sound`.

From this directory:

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

For the combined PDF build and axiom audit, run from the repository root:

```sh
./scripts/check.sh
```

If a contribution adds dependencies, record them in `lakefile.toml` and
commit the generated `lake-manifest.json`. The toolchain file is the
source of the Lean version used locally and in CI.

Question pages and the README summary record the extent of each
formalization and its separate human review.
