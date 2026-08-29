import PrimeStar.LogarithmicWindowConstantLayer

/-!
# Finite-prime-sum form of the constant layer

This file aligns the public theorem with the elementary finite-sum form used
in the manuscript's abstract.  It proves that the allowed-prime sum
`sum_{p ≤ N, p ∉ S} 1 / (p - 1)` differs from `log log N` by `κ_S`, and then
repackages the uniform logarithmic-window spectral theorem with that finite
sum in place of `log log X + κ_S`.
-/

namespace PrimeStar

open Filter Topology
open scoped BigOperators

noncomputable section

/-- The finite sum `∑_{p ≤ N, p ∉ S} 1 / (p - 1)` over allowed primes. -/
def finiteAllowedPrimeInvSubOneSum (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S), ((p : ℝ) - 1)⁻¹

/-- Exact partial-fraction decomposition of the finite headline sum. -/
theorem finiteAllowedPrimeInvSubOneSum_eq
    (S : Finset ℕ) (N : ℕ) :
    finiteAllowedPrimeInvSubOneSum S N =
      allowedPrimeReciprocalSum S N + finiteNonlinearPrimeCorrection S N := by
  rw [finiteAllowedPrimeInvSubOneSum, allowedPrimeReciprocalSum,
    finiteNonlinearPrimeCorrection]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime : p.Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hpPrime.ne_one
  field_simp [hp0, sub_ne_zero.mpr hp1]
  ring

/-- The finite headline sum has constant term `κ_S`. -/
theorem tendsto_finiteAllowedPrimeInvSubOneSum_sub_log
    (S : Finset ℕ) :
    Tendsto
      (fun N : ℕ ↦ finiteAllowedPrimeInvSubOneSum S N -
        Real.log (Real.log (N : ℝ)))
      atTop (𝓝 (primeStarKappa meisselMertensConstant S)) := by
  have hM := allowedPrimeMertensAsymptotic_meisselMertensConstant S
  have hN := tendsto_finiteNonlinearPrimeCorrection S
  have hsum := hM.add hN
  apply hsum.congr'
  filter_upwards with N
  rw [finiteAllowedPrimeInvSubOneSum_eq]
  ring

/-- Theorem 9.6 in the manuscript's finite-prime-sum form.

Uniformly for allowed centres in the logarithmic window, the squared ordered
eigenvalue equals `π_S(X/a) + 4 ∑_{p ≤ X, p ∉ S} 1/(p-1) + c(a) + o(1)`.
-/
theorem eventually_logarithmicWindow_ranked_finitePrimeSum_proved
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
        (largePrimePositiveStarOrderedIndex a
            (sqrtCutoff_condition X) haY hd).1 + 1 = arithmeticCenterRank a ∧
          |(arithmeticStarFullEigenvalue a haY hd)^2 -
              (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
              4 * finiteAllowedPrimeInvSubOneSum S X -
              centerPrimeCorrection (a : ℕ)| < δ := by
  intro δ hδ
  have hconstant := eventually_logarithmicWindow_ranked_constantLayer_proved
    S hS hε (δ / 2) (by positivity)
  have hsum := (tendsto_finiteAllowedPrimeInvSubOneSum_sub_log S).eventually
    (Metric.ball_mem_nhds _ (show 0 < δ / 8 by positivity))
  filter_upwards [hconstant, hsum] with X hconstantX hsumX
  intro a ha
  obtain ⟨haY, hd, hrank, hbound⟩ := hconstantX a ha
  refine ⟨haY, hd, hrank, ?_⟩
  have hsumBound :
      |(finiteAllowedPrimeInvSubOneSum S X -
          Real.log (Real.log (X : ℝ))) -
        primeStarKappa meisselMertensConstant S| < δ / 8 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hsumX
  have hidentity :
      (arithmeticStarFullEigenvalue a haY hd)^2 -
          (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
          4 * finiteAllowedPrimeInvSubOneSum S X -
          centerPrimeCorrection (a : ℕ) =
        (((arithmeticStarFullEigenvalue a haY hd)^2 -
            (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            4 * Real.log (Real.log (X : ℝ))) -
            (4 * primeStarKappa meisselMertensConstant S +
              centerPrimeCorrection (a : ℕ)) -
          4 * ((finiteAllowedPrimeInvSubOneSum S X -
            Real.log (Real.log (X : ℝ))) -
            primeStarKappa meisselMertensConstant S) := by ring
  rw [hidentity]
  calc
    _ ≤ |(((arithmeticStarFullEigenvalue a haY hd)^2 -
          (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
          4 * Real.log (Real.log (X : ℝ))) -
          (4 * primeStarKappa meisselMertensConstant S +
            centerPrimeCorrection (a : ℕ))| +
        |4 * ((finiteAllowedPrimeInvSubOneSum S X -
          Real.log (Real.log (X : ℝ))) -
          primeStarKappa meisselMertensConstant S)| := abs_sub _ _
    _ < δ / 2 + 4 * (δ / 8) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      exact add_lt_add hbound (mul_lt_mul_of_pos_left hsumBound (by norm_num))
    _ = δ := by ring

end

end PrimeStar
