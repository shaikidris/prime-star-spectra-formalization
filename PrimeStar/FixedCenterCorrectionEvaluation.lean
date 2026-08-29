import PrimeStar.ConstantEvaluation
import PrimeStar.FixedCenterDegreeRatios

/-!
# Fixed-centre evaluation of the actual first-exit correction

This module defines the arithmetic up- and down-star corrections attached to
a fixed centre.  The up ratio is explicitly truncated when the putative centre
`c * q` lies beyond the square-root boundary; the raw difference of prime
counts is negative there and is not a graph degree.

The finite down-star family is evaluated here.  The growing up-star family is
handled separately by a head--tail estimate.
-/

namespace PrimeStar

open Filter Topology
open scoped BigOperators

noncomputable section

/-- The actual arithmetic ratio of the up-star at `c * q` to the star at `c`.
It is zero once `c * q` lies beyond the square-root boundary, exactly as in the
finite graph. -/
def fixedCenterActualUpRatio (S : Finset ℕ) (c X q : ℕ) : ℝ :=
  if c * q ≤ Nat.sqrt X then
    fixedCenterArithmeticDegree S (c * q) X /
      fixedCenterArithmeticDegree S c X
  else 0

/-- The growing up-star correction at a fixed arithmetic centre. -/
def fixedCenterActualUpCorrection (S : Finset ℕ) (c X : ℕ) : ℝ :=
  ∑ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
    upStarCorrection (fixedCenterActualUpRatio S c X q)

/-- The finite down-star correction at a fixed arithmetic centre. -/
def fixedCenterActualDownCorrection (S : Finset ℕ) (c X : ℕ) : ℝ :=
  ∑ q ∈ c.primeFactors,
    downStarCorrection
      (fixedCenterArithmeticDegree S (c / q) X /
        fixedCenterArithmeticDegree S c X)

theorem continuousAt_downStarCorrection {s : ℝ} (hs : s ≠ 1) :
    ContinuousAt downStarCorrection s := by
  unfold downStarCorrection
  exact (continuousAt_const.sub continuousAt_id).div
    (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hs.symm)

/-- Every fixed down-star local term converges to its limiting local model. -/
theorem fixedCenter_downStarCorrection_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c q : ℕ} (hc : 0 < c) (hq : q ∈ c.primeFactors) :
    Tendsto
      (fun X : ℕ ↦ downStarCorrection
        (fixedCenterArithmeticDegree S (c / q) X /
          fixedCenterArithmeticDegree S c X))
      atTop (𝓝 (downStarCorrection (q : ℝ))) := by
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hratio := fixedCenter_downArithmeticDegreeRatio_tendsto S hS hc
    hqPrime.pos (Nat.dvd_of_mem_primeFactors hq)
  exact (continuousAt_downStarCorrection
    (by exact_mod_cast hqPrime.ne_one)).tendsto.comp hratio

/-- The actual finite down-star correction tends to the centre-dependent
constant `c(c)` from Corollary 8.9. -/
theorem fixedCenterActualDownCorrection_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    Tendsto (fixedCenterActualDownCorrection S c) atTop
      (𝓝 (centerPrimeCorrection c)) := by
  have hsum : Tendsto
      (fun X : ℕ ↦ ∑ q ∈ c.primeFactors,
        downStarCorrection
          (fixedCenterArithmeticDegree S (c / q) X /
            fixedCenterArithmeticDegree S c X))
      atTop (𝓝 (∑ q ∈ c.primeFactors, downStarCorrection (q : ℝ))) :=
    tendsto_finsetSum c.primeFactors fun q hq ↦
    fixedCenter_downStarCorrection_tendsto S hS hc hq
  have hlimit : (∑ q ∈ c.primeFactors, downStarCorrection (q : ℝ)) =
      centerPrimeCorrection c := by
    rw [← sum_downStarCorrection_univ_eq_centerPrimeCorrection]
    exact Finset.sum_subtype c.primeFactors (fun _ ↦ Iff.rfl) _
  rw [hlimit] at hsum
  unfold fixedCenterActualDownCorrection
  exact hsum

end

end PrimeStar
