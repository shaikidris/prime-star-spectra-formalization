# Source provenance

The submitted repository contains the substantive formalization. It is not a
thin wrapper around another Lean project.

| Role | Repository | Commit |
|---|---|---|
| Imported analytic dependency | [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | `7715064f690d0689f30889846f4e2c5e7ec0c47e` |

The mathematical statement formalized by the selected Comparator declaration
is the finite-prime-sum form of Theorem 9.6 of the CC BY 4.0 preprint
[Prime-Star Localization and Second-Order Spectra of Finite Divisibility Cover Graphs](https://doi.org/10.5281/zenodo.22163492),
also available as [SSRN 7364645](https://doi.org/10.2139/ssrn.7364645).
The formal development proves the exact partial-fraction and prime-Mertens
bridge from that finite sum to the theorem's `4 log log X + 4 kappa_S` form.

Mathlib and all transitive Git dependencies are pinned in
[`lake-manifest.json`](lake-manifest.json). Their exact revisions are build
inputs rather than alternative substantive formalizations.
