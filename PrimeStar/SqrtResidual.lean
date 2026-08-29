import PrimeStar.FirstExit
import PrimeStar.SqrtCutoff
import PrimeStar.TunedPrimeSumBounds

/-!
# Residual norm at the literal integer square-root cutoff

The elementary Schur estimate was first proved under the convenient ambient
hypothesis `X ≤ Y²`.  At the manuscript cutoff `Y = Nat.sqrt X` this need not
hold.  This file compares the residual graph at `Y` with the one at `Y + 1`,
where the square bound does hold, and therefore supplies the literal cutoff
wrapper without changing the graph used in the manuscript.
-/

namespace PrimeStar

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

local instance sqrtResidualSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Increasing the residual-prime cutoff only adds edges. -/
theorem smallPrimeGraph_mono
    {S : Finset ℕ} {X Y Z : ℕ} (hYZ : Y ≤ Z) :
    smallPrimeGraph S X Y ≤ smallPrimeGraph S X Z := by
  intro m n hmn
  obtain ⟨p, hp, hpS, hpY, hmul⟩ :=
    smallPrimeGraph_adj_iff_smallPrimeAdj.mp hmn
  exact smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
    ⟨p, hp, hpS, hpY.trans hYZ, hmul⟩

/-- A nonnegative weighted row sum is monotone in the residual cutoff. -/
theorem sum_smallPrime_neighborFinset_mono
    {S : Finset ℕ} {X Y Z : ℕ} (hYZ : Y ≤ Z)
    (w : Vertex S X → ℝ) (hw : ∀ v, 0 ≤ w v)
    (n : Vertex S X) :
    ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n, w v ≤
      ∑ v ∈ (smallPrimeGraph S X Z).neighborFinset n, w v := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv ⊢
    exact smallPrimeGraph_mono hYZ hv
  · intro v _hv _hvnot
    exact hw v

/-- Transfer the elementary weighted-Schur bound from a larger residual
cutoff `Z` to any smaller cutoff `Y`. -/
theorem smallPrimeGraph_l2_opNorm_le_elementaryBound_of_le
    {S : Finset ℕ} {X Y Z : ℕ}
    (hYZ : Y ≤ Z) (hXZ : X ≤ Z ^ 2)
    (hlogZ : 0 < Real.log (Z : ℝ)) :
    ‖(smallPrimeGraph S X Y).adjMatrix ℝ‖ ≤
      elementarySmallPrimeRowBound Z := by
  apply smallPrimeGraph_l2_opNorm_le_of_weightedRow
    (smallPrimePowerWeight (Z : ℝ))
    (elementarySmallPrimeRowBound Z)
    (elementarySmallPrimeRowBound_nonneg Z)
    (smallPrimePowerWeight_pos (Z : ℝ))
  intro n
  exact (sum_smallPrime_neighborFinset_mono hYZ
      (smallPrimePowerWeight (Z : ℝ))
      (fun v ↦ (smallPrimePowerWeight_pos (Z : ℝ) v).le) n).trans
    (smallPrimePowerWeight_row_le_elementaryBound hXZ hlogZ n)

/-- Finite literal-cutoff wrapper: the graph is cut at `Nat.sqrt X`, while
the harmless scalar majorant is evaluated at `Nat.sqrt X + 1`. -/
theorem sqrtCutoff_smallPrimeGraph_l2_opNorm_le_elementaryBound
    {S : Finset ℕ} {X : ℕ}
    (hlog : 0 < Real.log ((Nat.sqrt X + 1 : ℕ) : ℝ)) :
    ‖(smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ‖ ≤
      elementarySmallPrimeRowBound (Nat.sqrt X + 1) := by
  apply smallPrimeGraph_l2_opNorm_le_elementaryBound_of_le
    (Nat.le_succ (Nat.sqrt X)) ?_ hlog
  have hcut := (sqrtCutoff_condition X).le
  simpa [pow_two] using hcut

/-- The natural function `X ↦ Nat.sqrt X + 1` tends to infinity. -/
theorem tendsto_sqrt_add_one_atTop :
    Tendsto (fun X : ℕ ↦ Nat.sqrt X + 1) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b ^ 2)] with X hX
  have hb : b ≤ Nat.sqrt X := Nat.le_sqrt'.2 hX
  omega

/-- Final literal square-root residual-norm theorem.  It has the same tuned
scale as the earlier square-cutoff theorem, evaluated at the adjacent integer
`Nat.sqrt X + 1`. -/
theorem eventually_sqrtCutoff_smallPrimeGraph_l2_opNorm_le_tuned :
    ∀ᶠ X : ℕ in atTop, ∀ S : Finset ℕ,
      ‖(smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ‖ ≤
        (12 * Real.log 4 + 2 / Real.log 2 + 16) *
          tunedSchurScale ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
  have hlog :
      ∀ᶠ Z : ℕ in atTop, 0 < Real.log (Z : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop 0)
  have hrow := eventually_elementarySmallPrimeRowBound_le_tuned
  filter_upwards [tendsto_sqrt_add_one_atTop.eventually hlog,
    tendsto_sqrt_add_one_atTop.eventually hrow] with X hlogX hrowX
  intro S
  exact
    (sqrtCutoff_smallPrimeGraph_l2_opNorm_le_elementaryBound hlogX).trans hrowX

end

end PrimeStar
