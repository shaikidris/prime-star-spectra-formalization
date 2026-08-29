# Source provenance

The submitted repository contains the substantive formalization. It is not a
thin wrapper around another Lean project.

| Role | Repository | Commit |
|---|---|---|
| Authoritative substantive source | [shaikidris/prime-star-spectra-formalization](https://github.com/shaikidris/prime-star-spectra-formalization) | `e40d375396f2965757600d7e0351ccdb69423c9b` |
| Palomar-compatible Mathlib dependency | [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | `3dffaf2f18b47d11948f6390838ea6f2ae662aaf` |
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

The Palomar compatibility port changes the Lean toolchain and Mathlib dependency
pins. Its Challenge/Solution adapter also uses the same explicit named adjacency
decision instance on both sides so Comparator sees definitionally identical
constants. The selected mathematical statement, substantive proof modules, and
Comparator selection are unchanged from the authoritative substantive source
commit above.
