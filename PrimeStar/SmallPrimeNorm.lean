import PrimeStar.FirstExit
import PrimeStar.PrimeCountingDegree
import PrimeStar.WeightedSchur

/-!
# Quantitative interface for the residual small-prime graph

The generic weighted Schur estimate is specialized here to the residual
adjacency matrix.  The hypotheses remain a literal finite weighted-row
inequality, so no prime number theorem or Mertens estimate is hidden in the
operator statement.
-/

namespace PrimeStar

open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

/-- Local decidability for residual adjacency in operator-norm estimates. -/
local instance smallPrimeNormDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The `X`-dependent exponent used in the paper's optimized power weight. -/
def tunedSchurExponent (Y : ℝ) : ℝ :=
  1 / 2 - Real.log (Real.log Y) / (2 * Real.log Y)

/-- The target scale produced by the optimized power weight. -/
def tunedSchurScale (Y : ℝ) : ℝ :=
  √Y / √(Real.log Y)

/-- Power weight on the positive integer vertices. -/
def smallPrimePowerWeight (Y : ℝ) {S : Finset ℕ} {X : ℕ}
    (n : Vertex S X) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-tunedSchurExponent Y)

theorem smallPrimePowerWeight_pos (Y : ℝ) {S : Finset ℕ} {X : ℕ}
    (n : Vertex S X) : 0 < smallPrimePowerWeight Y n := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast Vertex.coe_pos n) _

theorem tunedSchurScale_nonneg (Y : ℝ) :
    0 ≤ tunedSchurScale Y := by
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The weighted adjacency row is exactly the weight sum over residual
neighbours. -/
theorem smallPrime_adjMatrix_weightedRow
    {S : Finset ℕ} {X Y : ℕ} (w : Vertex S X → ℝ) (n : Vertex S X) :
    ∑ v, (smallPrimeGraph S X Y).adjMatrix ℝ n v * w v =
      ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n, w v := by
  change Matrix.mulVec ((smallPrimeGraph S X Y).adjMatrix ℝ) w n = _
  rw [SimpleGraph.adjMatrix_mulVec_apply]

/-- A literal finite weighted-row estimate controls the Euclidean operator
norm of the residual adjacency matrix. -/
theorem smallPrimeGraph_l2_opNorm_le_of_weightedRow
    {S : Finset ℕ} {X Y : ℕ} (w : Vertex S X → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hw : ∀ n, 0 < w n)
    (hrow : ∀ n,
      ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n, w v ≤ C * w n) :
    ‖(smallPrimeGraph S X Y).adjMatrix ℝ‖ ≤ C := by
  apply weightedSchur_l2_opNorm_le
      ((smallPrimeGraph S X Y).adjMatrix ℝ) w C hC
  · intro i j
    simp only [SimpleGraph.adjMatrix_apply]
    split <;> positivity
  · intro i j
    simp only [SimpleGraph.adjMatrix_apply]
    have hadj := (smallPrimeGraph S X Y).adj_comm i j
    split_ifs <;> tauto
  · exact hw
  · intro n
    rw [smallPrime_adjMatrix_weightedRow]
    exact hrow n

/-- The same Schur constant controls the first-exit source obtained by
applying the residual adjacency to a normalized prime-star mode. -/
theorem norm_smallPrime_apply_normalizedStarMode_le_of_weightedRow
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε C : ℝ}
    (w : Vertex S X → ℝ)
    (hC : 0 ≤ C) (hw : ∀ n, 0 < w n)
    (hrow : ∀ n,
      ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n, w v ≤ C * w n)
    (hd : 0 < largePrimeStarDegree S X Y c) :
    ‖Matrix.toEuclideanCLM (n := Vertex S X) (𝕜 := ℝ)
        ((smallPrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeNormalizedStarMode S X Y c ε)‖ ≤ C := by
  calc
    ‖Matrix.toEuclideanCLM (n := Vertex S X) (𝕜 := ℝ)
        ((smallPrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeNormalizedStarMode S X Y c ε)‖ ≤
        ‖(smallPrimeGraph S X Y).adjMatrix ℝ‖ *
          ‖largePrimeNormalizedStarMode S X Y c ε‖ := by
            exact (Matrix.toEuclideanCLM (n := Vertex S X) (𝕜 := ℝ)
              ((smallPrimeGraph S X Y).adjMatrix ℝ)).le_opNorm _
    _ ≤ C * ‖largePrimeNormalizedStarMode S X Y c ε‖ := by
          gcongr
          exact smallPrimeGraph_l2_opNorm_le_of_weightedRow w C hC hw hrow
    _ = C := by rw [norm_largePrimeNormalizedStarMode hd, mul_one]

/-- Literal tuned-power-weight specialization.  Its only quantitative
hypothesis is the finite row estimate that the elementary prime-sum and
divisor-counting argument must establish. -/
theorem smallPrimeGraph_l2_opNorm_le_tuned
    {S : Finset ℕ} {X Y : ℕ} {K : ℝ}
    (_hY : 1 < (Y : ℝ)) (hK : 0 ≤ K)
    (hrow : ∀ n,
      ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n,
          smallPrimePowerWeight (Y : ℝ) v ≤
        (K * tunedSchurScale (Y : ℝ)) *
          smallPrimePowerWeight (Y : ℝ) n) :
    ‖(smallPrimeGraph S X Y).adjMatrix ℝ‖ ≤
      K * tunedSchurScale (Y : ℝ) := by
  apply smallPrimeGraph_l2_opNorm_le_of_weightedRow
      (smallPrimePowerWeight (Y : ℝ)) (K * tunedSchurScale (Y : ℝ))
  · exact mul_nonneg hK (tunedSchurScale_nonneg (Y : ℝ))
  · exact smallPrimePowerWeight_pos (Y : ℝ)
  · exact hrow

/-- The tuned Schur estimate also controls the normalized first-exit source. -/
theorem norm_smallPrime_apply_normalizedStarMode_le_tuned
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε K : ℝ}
    (_hY : 1 < (Y : ℝ)) (hK : 0 ≤ K)
    (hrow : ∀ n,
      ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n,
          smallPrimePowerWeight (Y : ℝ) v ≤
        (K * tunedSchurScale (Y : ℝ)) *
          smallPrimePowerWeight (Y : ℝ) n)
    (hd : 0 < largePrimeStarDegree S X Y c) :
    ‖Matrix.toEuclideanCLM (n := Vertex S X) (𝕜 := ℝ)
        ((smallPrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeNormalizedStarMode S X Y c ε)‖ ≤
      K * tunedSchurScale (Y : ℝ) := by
  exact norm_smallPrime_apply_normalizedStarMode_le_of_weightedRow
    (smallPrimePowerWeight (Y : ℝ))
    (mul_nonneg hK (tunedSchurScale_nonneg (Y : ℝ)))
    (smallPrimePowerWeight_pos (Y : ℝ)) hrow hd

end

end PrimeStar
