import PrimeStar.ConstantLayer
import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime

/-!
# External analytic inputs

This module adapts the quantitative prime-number and prime-Mertens theorems
from `PrimeNumberTheoremAnd` to the interfaces used by `PrimeStar`.
-/

namespace PrimeStar

open Filter Topology
open scoped Nat.Prime
open scoped BigOperators

noncomputable section

/-- The prime-Mertens theorem in the natural-number interface used by the
prime-star constant layer. -/
theorem primeMertensAsymptotic_meisselMertensConstant :
    PrimeMertensAsymptotic meisselMertensConstant := by
  have h := RS_prime.mertens_second_theorem.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards with N
  simp only [Function.comp_apply, Nat.floor_natCast, primeReciprocalSum,
    Nat.primesLE_eq_filter_range]
  rw [show Finset.Iic N = Finset.range (N + 1) by ext p; simp]
  simp [one_div]

/-- Prime Mertens after deleting any fixed finite set of primes. -/
theorem allowedPrimeMertensAsymptotic_meisselMertensConstant (S : Finset ℕ) :
    Tendsto
      (fun N : ℕ ↦
        allowedPrimeReciprocalSum S N - Real.log (Real.log (N : ℝ)))
      atTop
      (nhds (meisselMertensConstant - deletedPrimeReciprocalMass S)) :=
  primeMertensAsymptotic_meisselMertensConstant.allowed S

/-- The prime-counting error has the quantitative scale required by the
prime-star degree comparisons. -/
theorem primeCounting_sub_main_isBigO_real :
    (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =O[atTop]
      (fun x : ℝ ↦ x / Real.log x ^ 2) := by
  have hinvLog :
      (fun x : ℝ ↦ (Real.log x)⁻¹) =O[atTop] (fun _x : ℝ ↦ (1 : ℝ)) :=
    (Real.tendsto_log_atTop.inv_tendsto_atTop).isBigO_one ℝ
  have hboundary :
      (fun x : ℝ ↦ (Chebyshev.theta x - x) / Real.log x) =O[atTop]
        (fun x : ℝ ↦ x / Real.log x ^ 2) := by
    simpa only [Pi.sub_apply, id_eq, div_eq_mul_inv, mul_one] using
      RS_prime.pntBigO.mul hinvLog
  apply (hboundary.add Chebyshev.integral_theta_div_log_sq_isBigO).congr'
    _ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [← _root_.pi, RS_prime.eq_417 hx]
  ring

/-- Real-cutoff form of the PNT error at little-o scale. -/
theorem primeCounting_sub_main_isLittleO_real :
    (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =o[atTop]
      (fun x : ℝ ↦ x / Real.log x) := by
  apply primeCounting_sub_main_isBigO_real.trans_isLittleO
  have h := (Asymptotics.isBigO_refl
    (fun x : ℝ ↦ x / Real.log x) atTop).mul_isLittleO
      Real.inv_log_isLittleO_one
  simpa only [div_eq_mul_inv, pow_two, mul_inv_rev, mul_assoc, mul_one] using h

/-- Prime counting at a real cutoff is asymptotic to `x / log x`. -/
theorem primeCounting_floor_isEquivalent_main_real :
    Asymptotics.IsEquivalent atTop
      (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ))
      (fun x : ℝ ↦ x / Real.log x) := by
  exact Asymptotics.IsLittleO.isEquivalent primeCounting_sub_main_isLittleO_real

/-- Natural-number form of the quantitative prime-counting estimate consumed
by the prime-star package. -/
theorem primeCounting_sub_main_isBigO :
    (fun N : ℕ ↦ (Nat.primeCounting N : ℝ) -
      (N : ℝ) / Real.log (N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  simpa using primeCounting_sub_main_isBigO_real.natCast_atTop

/-- The quantitative PNT error is little-o of its main term. -/
theorem primeCounting_sub_main_isLittleO :
    (fun N : ℕ ↦ (Nat.primeCounting N : ℝ) -
      (N : ℝ) / Real.log (N : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ)) := by
  apply primeCounting_sub_main_isBigO.trans_isLittleO
  have hreal :
      (fun x : ℝ ↦ x / Real.log x ^ 2) =o[atTop]
        (fun x : ℝ ↦ x / Real.log x) := by
    have h := (Asymptotics.isBigO_refl
      (fun x : ℝ ↦ x / Real.log x) atTop).mul_isLittleO
      Real.inv_log_isLittleO_one
    simpa only [div_eq_mul_inv, pow_two, mul_inv_rev, mul_assoc, mul_one] using h
  simpa using hreal.natCast_atTop

/-- Natural-number prime counting is asymptotic to `N / log N`. -/
theorem primeCounting_isEquivalent_main :
    Asymptotics.IsEquivalent atTop
      (fun N : ℕ ↦ (Nat.primeCounting N : ℝ))
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ)) := by
  exact Asymptotics.IsLittleO.isEquivalent primeCounting_sub_main_isLittleO

end

end PrimeStar
