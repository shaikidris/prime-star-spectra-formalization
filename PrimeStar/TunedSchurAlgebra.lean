import PrimeStar.SmallPrimeNorm

/-!
# Algebra of the tuned Schur exponent

This file proves the exact balance identities behind the `X`-dependent power
weight. It contains no prime-counting estimate.
-/

namespace PrimeStar

noncomputable section

/-- Once `log Y > 1`, the tuned exponent lies below `1 / 2`. -/
theorem tunedSchurExponent_lt_half {Y : ℝ} (hY : 1 < Real.log Y) :
    tunedSchurExponent Y < 1 / 2 := by
  rw [tunedSchurExponent]
  have hlogY : 0 < Real.log Y := zero_lt_one.trans hY
  have hloglogY : 0 < Real.log (Real.log Y) := Real.log_pos hY
  have hden : 0 < 2 * Real.log Y := mul_pos (by norm_num) hlogY
  exact sub_lt_self _ (div_pos hloglogY hden)

/-- The tuned exponent is nonnegative whenever `log Y` is positive. -/
theorem tunedSchurExponent_nonneg {Y : ℝ} (hY : 0 < Real.log Y) :
    0 ≤ tunedSchurExponent Y := by
  rw [tunedSchurExponent]
  have hloglog : Real.log (Real.log Y) ≤ Real.log Y :=
    Real.log_le_self hY.le
  have hden : 0 < 2 * Real.log Y := mul_pos (by norm_num) hY
  rw [sub_nonneg, div_le_iff₀ hden]
  nlinarith

/-- The tuned exponent makes `Y ^ theta` exactly equal to the target Schur
scale. -/
theorem rpow_tunedSchurExponent_eq_scale {Y : ℝ} (hYpos : 0 < Y)
    (hY : 1 < Real.log Y) :
    Y ^ tunedSchurExponent Y = tunedSchurScale Y := by
  have hlogY : 0 < Real.log Y := zero_lt_one.trans hY
  rw [tunedSchurExponent, tunedSchurScale, Real.rpow_def_of_pos hYpos,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hYpos, Real.rpow_def_of_pos hlogY]
  have harg :
      Real.log Y * (1 / 2 - Real.log (Real.log Y) / (2 * Real.log Y)) =
        Real.log Y * (1 / 2) - Real.log (Real.log Y) * (1 / 2) := by
    field_simp
  rw [harg, Real.exp_sub]

/-- The outgoing prime-sum scale is balanced by the same tuned exponent. -/
theorem rpow_one_sub_tunedSchurExponent_div_log_eq_scale {Y : ℝ}
    (hYpos : 0 < Y) (hY : 1 < Real.log Y) :
    Y ^ (1 - tunedSchurExponent Y) / Real.log Y = tunedSchurScale Y := by
  have hlogY : 0 < Real.log Y := zero_lt_one.trans hY
  have hsqrtlog : 0 < √(Real.log Y) := Real.sqrt_pos.2 hlogY
  have hpow :
      Y ^ (1 - tunedSchurExponent Y) = √Y * √(Real.log Y) := by
    rw [tunedSchurExponent, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos hYpos, Real.rpow_def_of_pos hYpos,
      Real.rpow_def_of_pos hlogY, ← Real.exp_add]
    apply congrArg Real.exp
    field_simp
    ring
  rw [hpow, tunedSchurScale]
  have hsq : √(Real.log Y) * √(Real.log Y) = Real.log Y :=
    Real.mul_self_sqrt hlogY.le
  calc
    √Y * √(Real.log Y) / Real.log Y =
        √Y * √(Real.log Y) / (√(Real.log Y) * √(Real.log Y)) := by rw [hsq]
    _ = √Y / √(Real.log Y) := by field_simp

end

end PrimeStar
