# Prime-star spectra in Lean 4

This repository contains the Lean 4 formalization accompanying
*Prime-Star Localization and Second-Order Spectra of Finite Divisibility
Cover Graphs*.

For a finite set `S` of deleted primes, let `A_{S,X}` be the adjacency matrix
of the graph on positive integers at most `X` that avoid `S`, with an edge
between `n` and `np` whenever `p ∉ S` is prime. If `a` is an allowed centre,
`j(a)` is its arithmetic rank, and

```text
P_S(X) = sum_{p ≤ X, p ∉ S} 1 / (p - 1),
```

the selected theorem proves, uniformly for
`a ≤ (log X)^(1/2 - ε)`, that

```text
lambda_{j(a)}(A_{S,X})^2
  = pi_S(X / a) + 4 * P_S(X) + c(a) + o(1).
```

Here `c(a)` is the explicit correction
`sum_{q | a, q prime} (q - 5) / (q - 1)`. The development also formalizes
the equivalent constant-layer form involving the prime Meissel–Mertens
constant, the finite star decomposition, spectral matching, first-exit
resolvent identities, eigenvector localization, and centre–shell adjacency
evolution.

## Palomar statement surface

- [`PrimeCoverChallenge.lean`](PrimeCoverChallenge.lean) is the compact,
  Mathlib-only statement surface.
- [`PrimeCoverSolution.lean`](PrimeCoverSolution.lean) connects the same
  declaration to the full proof development in [`PrimeStar/`](PrimeStar/).
- [`prime-cover-comparator.json`](prime-cover-comparator.json) selects
  `PrimeStar.palomar_uniform_finite_prime_sum` and its finite-prime-sum
  definition for Comparator and NanoDa checking.
- [`formalization.yaml`](formalization.yaml) records authorship, provenance,
  theorem alignment, automation, and the permitted axiom footprint.
- [`SOURCE_PROVENANCE.md`](SOURCE_PROVENANCE.md) records the substantive
  development boundary and the pinned analytic dependency.

For a Palomar submission from this repository, the selected project path is
the repository root and the Comparator configuration path is
`prime-cover-comparator.json`.

## Reproducibility

The project is pinned to Lean/mathlib `v4.32.2` and
`PrimeNumberTheoremAnd` commit
`7715064f690d0689f30889846f4e2c5e7ec0c47e`.

```bash
lake exe cache get
lake build
lake build PrimeCoverChallenge PrimeCoverSolution
lake build PrimeStar.Main PrimeStar.Audit
```

The selected public theorem has no `sorry`, `admit`, or project axiom. Its
reported axiom footprint is limited to `propext`, `Classical.choice`, and
`Quot.sound`.

## Paper

- Zenodo v1.1: <https://doi.org/10.5281/zenodo.22163492>
- SSRN: <https://doi.org/10.2139/ssrn.7364645>

## Submission

Palomar submissions use the official form at
<https://submit.palomar-registry.org/> and identify an exact public GitHub
commit. Registration is a later, separate author decision after Palomar's
review.

## License

The Lean source in this repository is licensed under the
[Apache License 2.0](LICENSE). The accompanying paper is distributed under
CC BY 4.0 through Zenodo.
