import PrimeStar.AnalyticInputs
import PrimeStar.ConstantEvaluation
import PrimeStar.ActualFiniteCorrection
import PrimeStar.SmallPrimeLowerBound
import PrimeStar.SqrtCutoff
import PrimeStar.SqrtResidual
import PrimeStar.FirstExitSupport
import PrimeStar.FirstExitCompression
import PrimeStar.Localization
import PrimeStar.DegreeIsolation
import PrimeStar.FeshbachDegreeGap
import PrimeStar.FixedCenterIsolation
import PrimeStar.FixedCenterDegreeRatios
import PrimeStar.PrimeLogIncrement
import PrimeStar.FixedCenterCorrectionEvaluation
import PrimeStar.FixedCenterUpStarEvaluation
import PrimeStar.FixedCenterRemainderAssembly
import PrimeStar.FixedCenterFiniteRemainder
import PrimeStar.FixedCenterRemainderRate
import PrimeStar.FixedCenterUniformUpStar
import PrimeStar.FixedCenterNonlinearTail
import PrimeStar.FixedCenterConstantLayer
import PrimeStar.FixedCenterCorrectionBridge
import PrimeStar.FixedCenterRankedConstantLayer
import PrimeStar.LogarithmicWindow
import PrimeStar.LogarithmicWindowSpectral
import PrimeStar.LogarithmicWindowSourceNorm
import PrimeStar.LogarithmicWindowSourceArithmetic
import PrimeStar.LogarithmicWindowSourceResolvent
import PrimeStar.LogarithmicWindowFeshbachRemainder
import PrimeStar.LogarithmicWindowCorrectionArithmetic
import PrimeStar.LogarithmicWindowUpRatio
import PrimeStar.LogarithmicWindowNonlinearTail
import PrimeStar.LogarithmicWindowDownCorrection
import PrimeStar.LogarithmicWindowConstantLayer
import PrimeStar.FinitePrimeSumHeadline
import PrimeStar.LogarithmicWindowLocalization
import PrimeStar.BipartiteSymmetry
import PrimeStar.LogarithmicWindowDynamics
import PrimeStar.FiniteRemainderAssembly
import PrimeStar.CanonicalFirstExitBlocks
import PrimeStar.AdjacencyEvolution

/-!
# Public formalization surface

The current public surface closes the exact finite large-prime star
decomposition, its associated `±√d` adjacency eigenvectors,
spectral-matching and simplicity interfaces under explicit gap hypotheses, the
reusable isolated-mode comparison, the exact first-exit support and
non-isolated star-block decomposition, the
actual-graph up/down-star resolvent identities, the finite Schur/first-exit
algebra, exact prime-counting degree identities, Chebyshev upper bounds, and
the tuned weighted-Schur interface for the residual graph.  The residual row
is reduced exactly to an Abel prime integral and an elementary divisor bound.
Chebyshev's explicit estimate closes that varying-exponent integral at the tuned scale,
and hence gives the uniform residual operator-norm bound below the square
cutoff. The matching finite lower bound from the induced root star, the
actual-graph finite-correction bound with explicit spectral-error inputs, and
the exact finite-deletion and convergent constant algebra are also public.
The residual norm is available at the literal integer square-root cutoff, and
the finite hub-mass localization consequence of star-mode closeness is
formalized. Arithmetic star centres have canonical ordered reference indices;
square-root gaps between their finite star degrees now imply the exact ordered
spectral-separation premise used by matching; the actual shifted-complement
inequality, normalized actual-eigenvector Schur
equation, vector-level source-weighted replacement, and preferred finite
remainder theorem without `hdisp`, `herr`, or an artificial perturbed map are
public. Finite continuous-time adjacency evolution and its centre--shell and
frequency-replacement estimates are also formalized. The quantitative PNT and
prime-Mertens inputs are imported from `PrimeNumberTheoremAnd` and adapted to
the counting and limit interfaces used here. For every fixed positive
arithmetic centre, the quantitative PNT now gives an explicit eventual
square-root star-degree gap of order `sqrt (X / log X)` from zero and from
every other nonempty star. That gap and the literal square-cutoff residual
bound are assembled into a matched simple eigenpair, a second-order
displacement bound of order `eta^2 / gamma`, and the fixed-centre finite
remainder estimate with an explicit `C_c / log X` majorant.
For any two fixed positive arithmetic centres, the actual square-cutoff
degree ratio is also proved to converge to the quotient of their centres; in
particular the fixed up/down ratios converge to `1/q` and `q`.
The uniform constant layer is also exported in the manuscript headline form
using the literal finite sum `∑_{p ≤ X, p ∉ S} 1 / (p - 1)`.

This module is the aggregate public import boundary. It exports both the
canonical finite comparison inequality consumed by Theorem 8.7 and its
eventual fixed-centre specialization with an explicit `C_c / log X` error.
It also evaluates the limiting up-star correction by prime Mertens and the
limiting down-star sum as the centre constant. The moving up-star ratios are
compared uniformly with their PNT model, and the nonlinear tail is summed
with a `1/q^2` majorant. The canonical graph correction is identified exactly
with this arithmetic correction. Hence the fixed-centre constant layer of
Corollary 8.9 is public both in matched-eigenpair form and at the full
adjacency eigenvalue occupying the same ordered slot as the centre's exact
positive reference-star mode. A positive-inertia count now identifies that
slot with the manuscript's arithmetic rank `j(a)`, including the possible
multiplicity of repeated star degrees. The exact Section 9 window predicate,
the uniform scalar absorption `a^2 / log X = o(1)`, and the ordered spectral
assemblies of Theorems 9.5--9.6 are public. The latter consume two explicit
uniform predicates rather than diagonalizing the fixed-centre theorem: degree
uniqueness plus the source-weighted `C * a^2 / log X` remainder, and the
uniform evaluation of the moving actual correction. Quantitative PNT now
closes the moving degree-uniqueness predicate and, more strongly, gives the
ordered large-prime spectral gap
`(96 * (a + 1))^-1 * sqrt (X / (a * log X))`. Exact norm-square formulas for
the canonical up/down local resolvent blocks are also public. Their orthogonal
direct-sum estimate gives `||R_U b||^2 <= 80000000 * a / sqrt X`, and the
source-weighted Feshbach assembly proves the ordered `C * a^2 / log X`
remainder uniformly on the full logarithmic centre window. A uniform PNT
comparison controls the moving up-star linear term, a dependent-family
Tannery argument controls its nonlinear tail, and the finitely supported
down-star correction converges uniformly after aggregation over prime
divisors. These results evaluate the moving actual correction and close
Theorem 9.6 at the manuscript's prescribed ordered eigenvalue. The same
ordered gap and residual scales now orient the corresponding full-adjacency
eigenvector toward its exact positive star mode with the finite error
`4 * eta / (gamma - 2 * eta)`. Hub mass and inverse participation follow
uniformly on the logarithmic window. An exact parity-sign involution
anticommutes with prime-cover adjacency, supplies the negative partner, and
upgrades the paired localization to centre--shell adjacency evolution at the
exact ordered eigenfrequency, uniformly for all real times.
-/

namespace PrimeStar

-- The public declarations are defined in the imported production modules;
-- this module fixes their aggregate import boundary.

end PrimeStar
