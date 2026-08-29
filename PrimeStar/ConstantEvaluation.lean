import PrimeStar.AnalyticInputs

/-!
# Evaluation of the limiting first-exit correction

This module combines the imported prime-reciprocal Mertens theorem with the
convergent nonlinear prime correction and identifies the finite down-star
sum with the centre-dependent constant. The remaining bridge to Corollary 8.9
is the comparison between the actual finite degree ratios and these limiting
local ratios.
-/

namespace PrimeStar

open Filter Topology
open scoped BigOperators

noncomputable section

/-- The limiting up-star correction has constant term `4 * kappa_S` after
subtracting `4 * log log N`. -/
theorem tendsto_finiteLimitingUpStarCorrection_sub_log
    (S : Finset ℕ) :
    Tendsto
      (fun N : ℕ ↦ finiteLimitingUpStarCorrection S N -
        4 * Real.log (Real.log (N : ℝ)))
      atTop (𝓝 (4 * primeStarKappa meisselMertensConstant S)) := by
  have hM := allowedPrimeMertensAsymptotic_meisselMertensConstant S
  have hN := tendsto_finiteNonlinearPrimeCorrection S
  have hsum := hM.const_mul 4 |>.add (hN.const_mul 4)
  have hsum' : Tendsto
      (fun N : ℕ ↦ 4 * (allowedPrimeReciprocalSum S N -
        Real.log (Real.log (N : ℝ))) +
        4 * finiteNonlinearPrimeCorrection S N)
      atTop (𝓝 (4 * primeStarKappa meisselMertensConstant S)) := by
    convert hsum using 1
    · simp [primeStarKappa]
      ring
  apply hsum'.congr'
  filter_upwards with N
  rw [finiteLimitingUpStarCorrection_eq]
  ring

/-- The sum of the limiting down-star local corrections is exactly the
centre-dependent constant `c(a)` from the manuscript. -/
theorem sum_downStarCorrection_univ_eq_centerPrimeCorrection (c : ℕ) :
    (∑ q : {q : ℕ // q ∈ c.primeFactors},
      downStarCorrection (q : ℝ)) = centerPrimeCorrection c := by
  rw [centerPrimeCorrection]
  symm
  calc
    (∑ q ∈ c.primeFactors, ((q : ℝ) - 5) / ((q : ℝ) - 1)) =
        ∑ q : {q : ℕ // q ∈ c.primeFactors},
          (((q : ℕ) : ℝ) - 5) / (((q : ℕ) : ℝ) - 1) := by
            exact Finset.sum_subtype c.primeFactors (fun _ ↦ Iff.rfl) _
    _ = ∑ q : {q : ℕ // q ∈ c.primeFactors},
        downStarCorrection (q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q _hq
      symm
      apply downStarCorrection_eq_centerTerm
      exact_mod_cast (Nat.Prime.ne_one (Nat.prime_of_mem_primeFactors q.property))

end

end PrimeStar
