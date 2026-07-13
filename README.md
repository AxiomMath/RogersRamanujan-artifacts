[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# Artifacts for "Formalized $q$-series: The Rogers-Ramanujan Identities and Beyond"

These files accompany the arXiv paper
[arXiv:2607.01544](https://arxiv.org/abs/2607.01544).

These artifacts were produced during the development of the `RogersRamanujan` library, so some of them may no longer compile with the current version. In that case, we provide manually updated versions of the artifacts with `updated` in their filenames. These updated versions are not listed separately below.

## Jacobi Triple Product

- Input:
  - A draft version of DiscreteEval.lean (*not provided*)
  - A draft version of QTheory.lean (*not provided*)
  - A draft version of TruncPoly.lean (*not provided*)
  - [chapter9.tex](jacobi-triple-product/chapter9.tex): A tex facsimile of Chapter 9 of *Analytic Number Theory for Undergraduates.* by H. H. Chan (2009).
  - [problem.lean](jacobi-triple-product/problem.lean): A formal statement of the Jacobi Triple Product identity without proof.
- Environment: Lean 4.26.0 with mathlib 4.26.0
- Output:
  - [solution.lean](jacobi-triple-product/solution.lean): A formal proof of the Jacobi Triple Product identity, matching `problem.lean`.

## Limit of topologically nilpotent elements

The limit of a sequence of topologically nilpotent elements is also topologically nilpotent.

- Input:
  - [problem.lean](limit-topologically-nilpotent/problem.lean): A formal statement of the question without proof.
- Environment: Lean 4.28.0 with mathlib 4.28.0 and the RogersRamanujan library
- Output:
  - [solution.lean](limit-topologically-nilpotent/solution.lean): A formal proof of the question, matching `problem.lean`.

## Finding an open subring in a non-archimedean ring

We propose the general shape of a canonical open subring in a non-archimedean ring and ask whether that construction is valid in general, and the answer was no.

- Input:
  - [problem.lean](prescribed-open/problem.lean): A formal statement of the question without proof, presented in the negative.
- Environment: Lean 4.28.0 with mathlib 4.28.0
- Output:
  - [solution.lean](prescribed-open/solution.lean): A formal proof of the negative, matching `problem.lean`.

## Pentagonal Number Theorem

- Input:
  - [task.md](pentagonal-number-theorem/task.md): A simple description of the task.
- Environment: Lean 4.30.0 with mathlib 4.30.0 and the RogersRamanujan library
- Output:
  - [problem.lean](pentagonal-number-theorem/problem.lean): A formal statement of the task.
  - [solution.lean](pentagonal-number-theorem/solution.lean): A formal proof of the task, matching `problem.lean`.

## Jacobi's Identity

- Input:
  - [task.md](jacobi-identity/task.md): A simple description of the task.
- Environment: Lean 4.30.0 with mathlib 4.30.0 and the RogersRamanujan library
- Output:
  - [problem.lean](jacobi-identity/problem.lean): A formal statement of the task.
  - [solution.lean](jacobi-identity/solution.lean): A formal proof of the task, matching `problem.lean`.

## q-Pfaff–Saalschütz Theorem

- Input:
  - [problem.lean](pfaff-saalschuetz/problem.lean): A formal statement of the task.
- Environment: Lean 4.31.0 with mathlib 4.31.0
- Output:
  - [solution.lean](pfaff-saalschuetz/solution.lean): A formal proof of the task, matching `problem.lean`.
