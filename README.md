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

the selected theorem surface proves, uniformly for
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

Its root-centred specialization is the paper's most readable headline:

```text
largest_eigenvalue(A_X)^2
  = pi(X) + 4 * sum_{p ≤ X} 1 / (p - 1) + o(1).
```

The same selected surface also exposes the paper's explicit-frequency
centre--shell dynamics.  Uniformly in the logarithmic window, the prime-star
centre evolves as the corresponding two-level oscillation at frequency

```text
sqrt (pi_S(X / a) + first_exit_correction(S, a, X)),
```

up to an explicit sum of the eigenvector-localization error and the phase
error supplied by the finite Feshbach remainder.

## Palomar statement surface

- [`PrimeCoverChallenge.lean`](PrimeCoverChallenge.lean) is the single compact,
  Mathlib-only v2 statement surface.  It contains the general uniform
  eigenvalue theorem, its undeleted root specialization, and the
  explicit-frequency dynamics theorem.
- [`PrimeCoverSolution.lean`](PrimeCoverSolution.lean) connects the same
  declaration to the full proof development in [`PrimeStar/`](PrimeStar/).
- [`prime-cover-comparator.json`](prime-cover-comparator.json) selects all three
  advertised declarations and their visible finite-prime-sum, star-state,
  evolution, frequency, and error definitions for Comparator and NanoDa
  checking.
- [`formalization.yaml`](formalization.yaml) records authorship, provenance,
  theorem alignment, automation, and the permitted axiom footprint.
- [`SOURCE_PROVENANCE.md`](SOURCE_PROVENANCE.md) records the substantive
  development boundary and the pinned analytic dependency.

For a Palomar submission from this repository, the selected project path is
the repository root and the Comparator configuration path is
`prime-cover-comparator.json`.

## Reproducibility

The project is pinned to Lean `v4.32.0`, Mathlib commit
`3dffaf2f18b47d11948f6390838ea6f2ae662aaf`, and
`PrimeNumberTheoremAnd` commit
`7715064f690d0689f30889846f4e2c5e7ec0c47e`.

```bash
lake exe cache get
lake build
lake build PrimeCoverChallenge PrimeCoverSolution
lake build PrimeStar.Main PrimeStar.Audit
```

The selected public theorems have no `sorry`, `admit`, or project axiom. Their
reported axiom footprint is limited to `propext`, `Classical.choice`, and
`Quot.sound`.

The development also exports the supporting logarithmic-window localization,
hub-mass, inverse-participation, and exact-eigenfrequency results.  When
registered, this v2 Challenge is intended to supersede the v1 statement
surface as the current Palomar version; the registered v1 record remains an
immutable historical version.

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
