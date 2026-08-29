import Lake

open Lake DSL

package primeStarFormalization where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @
    "7715064f690d0689f30889846f4e2c5e7ec0c47e"

-- Keep the root mathlib pin last so its transitive dependency revisions win.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "3dffaf2f18b47d11948f6390838ea6f2ae662aaf"

@[default_target]
lean_lib PrimeStar where
  globs := #[
    .one `PrimeStar,
    .submodules `PrimeStar
  ]

/-- Small Challenge/Solution surface used by Palomar Comparator. -/
lean_lib PrimeCoverPalomar where
  globs := #[
    .one `PrimeCoverChallenge,
    .one `PrimeCoverSolution
  ]
