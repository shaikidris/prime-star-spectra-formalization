import PrimeStar.FixedCenterNonlinearTail
import PrimeStar.FixedCenterRemainderRate

/-!
# Fixed-centre constant layer

This module assembles the moving up-star head--tail analysis with the finite
down-star limit.  The resulting arithmetic correction is the constant layer
appearing in Corollary 8.9.
-/

namespace PrimeStar

open Filter Topology Asymptotics
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1200000

/-- Once the actual ratios stay away from `1`, the up-star correction splits
exactly into its linear and nonlinear parts. -/
theorem eventually_fixedCenterActualUpCorrection_eq
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      fixedCenterActualUpCorrection S c X =
        4 * fixedCenterActualUpLinear S c X +
          4 * fixedCenterActualUpQuadratic S c X := by
  filter_upwards [eventually_fixedCenterActualUpRatio_le_three_quarters S hS hc]
      with X hcap
  let Q := (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S)
  rw [fixedCenterActualUpCorrection, fixedCenterActualUpLinear,
    fixedCenterActualUpQuadratic]
  calc
    (∑ q ∈ Q, upStarCorrection (fixedCenterActualUpRatio S c X q)) =
        ∑ q ∈ Q, (4 * fixedCenterActualUpRatio S c X q +
          4 * (fixedCenterActualUpRatio S c X q) ^ 2 /
            (1 - fixedCenterActualUpRatio S c X q)) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply upStarCorrection_eq_linear_add_quadratic
      linarith [hcap q hq]
    _ = 4 * (∑ q ∈ Q, fixedCenterActualUpRatio S c X q) +
        4 * (∑ q ∈ Q, (fixedCenterActualUpRatio S c X q) ^ 2 /
          (1 - fixedCenterActualUpRatio S c X q)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      simp only [mul_div_assoc]

/-- The actual moving up-star correction has the predicted Mertens plus
nonlinear constant. -/
theorem fixedCenterActualUpCorrection_sub_logLog_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    Tendsto
      (fun X : ℕ ↦ fixedCenterActualUpCorrection S c X -
        4 * Real.log (Real.log (X : ℝ)))
      atTop (𝓝 (4 * primeStarKappa meisselMertensConstant S)) := by
  have hlinearDiff := fixedCenterActualUpLinear_sub_model_tendsto_zero S hS hc
  have hlinearModel := fixedCenterUpLinearModel_sub_logLog_tendsto S hc
  have hlinear : Tendsto
      (fun X : ℕ ↦ fixedCenterActualUpLinear S c X -
        Real.log (Real.log (X : ℝ)))
      atTop (𝓝 (meisselMertensConstant - deletedPrimeReciprocalMass S)) := by
    have h := hlinearDiff.add hlinearModel
    convert h using 1 <;> ring
  have hquadratic := fixedCenterActualUpQuadratic_tendsto S hS hc
  have hsum := (hlinear.const_mul 4).add (hquadratic.const_mul 4)
  have hlimit :
      4 * (meisselMertensConstant - deletedPrimeReciprocalMass S) +
          4 * nonlinearPrimeConstant S =
        4 * primeStarKappa meisselMertensConstant S := by
    rw [primeStarKappa]
    ring
  rw [hlimit] at hsum
  apply hsum.congr'
  filter_upwards [eventually_fixedCenterActualUpCorrection_eq S hS hc] with X hX
  rw [hX]
  ring

/-- The complete actual first-exit correction at a fixed centre. -/
def fixedCenterActualCorrection (S : Finset ℕ) (c X : ℕ) : ℝ :=
  fixedCenterActualUpCorrection S c X + fixedCenterActualDownCorrection S c X

/-- The complete actual correction has the constant layer from Corollary
8.9. -/
theorem fixedCenterActualCorrection_sub_logLog_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    Tendsto
      (fun X : ℕ ↦ fixedCenterActualCorrection S c X -
        4 * Real.log (Real.log (X : ℝ)))
      atTop (𝓝 (4 * primeStarKappa meisselMertensConstant S +
        centerPrimeCorrection c)) := by
  have hup := fixedCenterActualUpCorrection_sub_logLog_tendsto S hS hc
  have hdown := fixedCenterActualDownCorrection_tendsto S hS hc
  have h := hup.add hdown
  convert h using 1
  · funext X
    rw [fixedCenterActualCorrection]
    ring

end

end PrimeStar
