# Dependence Implication

The main purpose of this project is to explore new ways to organize
theoretical research. It focuses on implication between
disjunctions of dependencies.

Questions, partial results, proofs, and formalizations are contributed
through pull requests and collected into a shared manuscript.

## Questions

Questions and subquestions are proposed through pull requests; see
[Contributing](CONTRIBUTING.md).

| Question | Solved | Human-checked solution | Formalized | Human-checked formalization |
| --- | --- | --- | --- | --- |
| [Q1: Complexity of implication for disjunctions of dependence atoms](questions/Q1.md) | yes | no | yes | no |
| &emsp;↳ [Q1.1: Syntactic restrictions for decidable implication](questions/Q1.1.md) | no | no | no | no |
| &emsp;↳ [Q1.2: Syntactic restrictions for PTIME implication](questions/Q1.2.md) | no | no | no | no |

All four status fields use `yes`, `no`, or `partially`. A question's page in
[`questions/`](questions/) records its precise statement, subquestions,
links to contributions, and details of any partial result or review.
The statuses describe what is available in this repository.

`Solved` records whether the question has been answered, including a
negative answer such as undecidability. `Formalized` records the coverage
of machine-checked proofs. The human-check fields record separate human
reviews; automated checks do not change them.

## Contribute

Open a pull request with:

1. **Question:** state a new question, identify an existing one, or name
   the shared part being improved, such as `preamble.tex`.
2. **Additional information (optional):** add a result, explanation,
   assumptions, sources, or a connection to another question.

New questions and subquestions are welcome. Question identifiers and their
placement are agreed in the PR discussion. Read the short
[contribution guide](CONTRIBUTING.md) for file placement and status updates.
Contributions to shared macros, notation, and other project components
are welcome through the same PR process.

## Student projects and ongoing work

BSc/MSc students are especially welcome. Coordinating ongoing work can be
especially helpful when developing a thesis or research project, providing
an agreed scope and time to explore it. The same arrangement is available
to every contributor.

Contributors can agree on a focused question or task and an approximate
working period in the PR discussion. The scope, contributor, and preliminary
working period are recorded on the question's page.

Please coordinate with the listed contributor before undertaking substantial 
overlapping work or submitting a complete solution to the agreed question. 
Comments, review, and supporting contributions are welcome.

## Manuscript and conceptual map

- [Manuscript PDF](output/pdf/paper.pdf), assembled by [`main.tex`](main.tex).
- [Conceptual map PDF](output/pdf/conceptual-map.pdf), assembled by
  [`conceptual-map/main.tex`](conceptual-map/main.tex).

Both documents start as empty project frameworks. Accepted text fragments
can be included in the manuscript using `\input{...}`.

```text
main.tex                  Shared manuscript
preamble.tex              Shared TeX packages and environments
questions/                Question statements, subquestions, and statuses
ai-tex/<id>/              AI-generated research notes
human-tex/<id>/           Human-authored notes
conceptual-map/           Concepts, results, and connections across questions
lean/                     One Lean project with shared and question modules
output/pdf/               Compiled manuscript and conceptual map
```

Human-authored roughly means that a human takes authorship and responsibility for
the content. 

## Build and check

The project uses `pdflatex`, Python 3, and Lean **4.35.0** through `elan`.

```sh
(cd lean && lake exe cache get)  # Download compiled mathlib dependencies
./scripts/build-pdfs.sh    # Rebuild both PDFs
./scripts/check.sh         # Build PDFs, build Lean, and run listed axiom audits
```

GitHub Actions runs the checks on pull requests and pushes to `main`, and
provides the built PDFs as workflow artifacts. LaTeX auxiliaries and local
Lean caches are ignored by Git.

The Lean project includes the Q1 formalization. See
[`lean/README.md`](lean/README.md) for its organization and build instructions.

## License

The project is distributed under the [MIT License](LICENSE).
