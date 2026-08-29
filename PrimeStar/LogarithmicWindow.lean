import PrimeStar.FixedCenterCorrectionBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The logarithmic growing-centre window

This module fixes the quantifiers used in Section 9 of the manuscript and
closes the scalar absorption at the end of that argument.  It deliberately
does not obtain the uniform spectral estimate by diagonalizing the
fixed-centre theorem: the required source-weighted Feshbach bounds must be
uniform before this module can consume them.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

/-- A natural centre lies in the manuscript's logarithmic window. -/
def InLogarithmicCenterWindow (ε : ℝ) (X a : ℕ) : Prop :=
  0 < a ∧ (a : ℝ) ≤ Real.log (X : ℝ) ^ (1 / 2 - ε)

/-- Every centre in a positive logarithmic window eventually lies below the
literal square-root cutoff.  This supplies the geometric side condition used
by the large-prime star decomposition uniformly in the moving centre. -/
theorem eventually_center_le_natSqrt_on_logarithmicWindow
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a → a ≤ Nat.sqrt X := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) :=
    hlogTop.eventually (Ici_mem_atTop 1)
  filter_upwards [hlogOne] with X hL a ha
  let L : ℝ := Real.log (X : ℝ)
  have hXpos : (0 : ℝ) < X := by
    by_contra h
    have hX0 : (X : ℝ) = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    rw [hX0, Real.log_zero] at hL
    linarith
  have hExp : 1 / 2 - ε ≤ (1 / 2 : ℝ) := by linarith
  have hpow : L ^ (1 / 2 - ε) ≤ L ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL hExp
  have haSqrtL : (a : ℝ) ≤ √L := by
    rw [Real.sqrt_eq_rpow]
    exact ha.2.trans hpow
  have hLX : L ≤ (X : ℝ) := by
    dsimp [L]
    exact (Real.log_le_sub_one_of_pos hXpos).trans (by linarith)
  have hSqrt : √L ≤ √(X : ℝ) := Real.sqrt_le_sqrt hLX
  have haSqrtX : (a : ℝ) ≤ √(X : ℝ) := haSqrtL.trans hSqrt
  have haSqR : (a : ℝ) ^ 2 ≤ (X : ℝ) := by
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have hs0 : 0 ≤ √(X : ℝ) := Real.sqrt_nonneg _
    have hsquare := (sq_le_sq₀ ha0 hs0).2 haSqrtX
    simpa [Real.sq_sqrt (le_of_lt hXpos)] using hsquare
  apply Nat.le_sqrt'.2
  exact_mod_cast haSqR

/-- Inside the logarithmic window, the scalar remainder `a^2 / log X` is
bounded by the negative power `(log X)^(-2 ε)`. -/
theorem center_sq_div_log_le_rpow_neg_two
    {ε : ℝ} {X a : ℕ}
    (hX : 1 < X) (ha : InLogarithmicCenterWindow ε X a) :
    (a : ℝ) ^ 2 / Real.log (X : ℝ) ≤
      Real.log (X : ℝ) ^ (-2 * ε) := by
  let L : ℝ := Real.log (X : ℝ)
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hX)
  have ha0 : 0 ≤ (a : ℝ) := by positivity
  have hpow0 : 0 ≤ L ^ (1 / 2 - ε) := Real.rpow_nonneg hL.le _
  have ha2 : (a : ℝ) ^ 2 ≤ (L ^ (1 / 2 - ε)) ^ 2 :=
    (sq_le_sq₀ ha0 hpow0).2 ha.2
  have hpowEq : (L ^ (1 / 2 - ε)) ^ 2 = L ^ (1 - 2 * ε) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
    congr 1
    ring
  rw [hpowEq] at ha2
  calc
    (a : ℝ) ^ 2 / Real.log (X : ℝ) = (a : ℝ) ^ 2 / L := rfl
    _ ≤ L ^ (1 - 2 * ε) / L := by
      exact div_le_div_of_nonneg_right ha2 hL.le
    _ = L ^ (-2 * ε) := by
      rw [← Real.rpow_sub_one hL.ne']
      congr 1
      ring

/-- The manuscript's scalar `a^2 / log X` error tends uniformly to zero on
`a ≤ (log X)^(1/2-ε)`.  This is the final absorption used after the uniform
source-weighted spectral estimate has been proved. -/
theorem eventually_center_sq_div_log_lt_on_logarithmicWindow
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        (a : ℝ) ^ 2 / Real.log (X : ℝ) < δ := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto
      (fun X : ℕ ↦ Real.log (X : ℝ) ^ (-2 * ε)) atTop (𝓝 0) :=
    by
      simpa only [Function.comp_def, neg_mul] using
        (tendsto_rpow_neg_atTop (show 0 < 2 * ε by positivity)).comp hlogTop
  have hsmall : ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ^ (-2 * ε) < δ :=
    (tendsto_order.1 hpow).2 δ hδ
  filter_upwards [hsmall, eventually_ge_atTop 2] with X hsmallX hX
  intro a ha
  exact (center_sq_div_log_le_rpow_neg_two (by omega) ha).trans_lt hsmallX

/-- Uniform-error assembly for the logarithmic window.  Any concrete
spectral defect bounded by `C * a^2 / log X` is uniformly `o(1)` there. -/
theorem eventually_abs_lt_on_logarithmicWindow_of_sq_div_log_bound
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (E : ℕ → ℕ → ℝ)
    (hE : ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
      |E X a| ≤ C * ((a : ℝ) ^ 2 / Real.log (X : ℝ))) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a → |E X a| < δ := by
  intro δ hδ
  by_cases hC0 : C = 0
  · filter_upwards [hE] with X hEX
    intro a ha
    have hz : |E X a| ≤ 0 := by simpa [hC0] using hEX a ha
    exact lt_of_le_of_lt hz hδ
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hsmall := eventually_center_sq_div_log_lt_on_logarithmicWindow
      hε (div_pos hδ hCpos)
    filter_upwards [hE, hsmall] with X hEX hsmallX
    intro a ha
    have hbound := hEX a ha
    have hratio := hsmallX a ha
    calc
      |E X a| ≤ C * ((a : ℝ) ^ 2 / Real.log (X : ℝ)) := hbound
      _ < C * (δ / C) := mul_lt_mul_of_pos_left hratio hCpos
      _ = δ := by field_simp

end

end PrimeStar
