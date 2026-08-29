import PrimeStar.AnalyticInputs

/-!
# The moving logarithmic prime increment

The linear part of the up-star correction contains

`sum_{p <= Y} log p / (p * (L - log p))`.

This file evaluates that moving sum by the Abel-summation identity already
available in `PrimeNumberTheoremAnd`.  The bounded error in Mertens' first
theorem contributes only `O(1 / (L - log Y))`; the main integral is explicit.
-/

namespace PrimeStar

open Filter Topology
open scoped BigOperators

noncomputable section

/-- The logarithmic increment in the moving up-star main model. -/
def primeLogIncrement (L : ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE Y,
    Real.log (p : ℝ) / ((p : ℝ) * (L - Real.log (p : ℝ)))

/-- The reciprocal logarithmic denominator used in partial summation. -/
def reciprocalLogGap (L : ℝ) : ℝ → ℝ :=
  (fun t : ℝ ↦ L - Real.log t)⁻¹

theorem hasDerivAt_reciprocalLogGap
    {L t : ℝ} (ht : 0 < t) (hgap : L - Real.log t ≠ 0) :
    HasDerivAt (reciprocalLogGap L)
      (1 / (t * (L - Real.log t) ^ 2)) t := by
  have hinner := (Real.hasDerivAt_log ht.ne').const_sub L
  have hinv := hinner.inv hgap
  have hcoef : - -t⁻¹ / (L - Real.log t) ^ 2 =
      (t * (L - Real.log t) ^ 2)⁻¹ := by
    field_simp [ht.ne', hgap]
  rw [hcoef] at hinv
  rw [show reciprocalLogGap L =
    (fun x : ℝ ↦ L - Real.log x)⁻¹ by rfl, one_div]
  exact hinv

/-- The prime-supported weight whose partial sums occur in Mertens' first
theorem. -/
def primeLogWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0

@[simp] theorem primeLogWeight_zero : primeLogWeight 0 = 0 := by
  simp [primeLogWeight]

@[simp] theorem primeLogWeight_one : primeLogWeight 1 = 0 := by
  simp [primeLogWeight]

theorem sum_Icc_primeLogWeight_eq (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n) =
      ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime,
        Real.log (p : ℝ) / (p : ℝ) := by
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
  simp only [primeLogWeight_zero, zero_add]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [primeLogWeight]

/-- Exact Abel-summation identity for the logarithmic prime increment. -/
theorem primeLogIncrement_partialSummation
    {L : ℝ} {Y : ℕ} (hY : 2 ≤ Y)
    (hgap : Real.log (Y : ℝ) < L) :
    primeLogIncrement L Y =
      reciprocalLogGap L (Y : ℝ) *
          (Real.log (Y : ℝ) + Mertens.E₁p (Y : ℝ)) -
        ∫ t in Set.Ioc 2 (Y : ℝ),
          (1 / (t * (L - Real.log t) ^ 2)) *
            (Real.log t + Mertens.E₁p t) := by
  let f : ℝ → ℝ := reciprocalLogGap L
  have hdiff : ∀ t ∈ Set.Icc 2 (Y : ℝ), DifferentiableAt ℝ f t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hlog : Real.log t ≤ Real.log (Y : ℝ) :=
      Real.log_le_log ht0 ht.2
    exact (hasDerivAt_reciprocalLogGap (L := L) ht0
      (by linarith)).differentiableAt
  have hint : MeasureTheory.IntegrableOn (deriv f)
      (Set.Icc 2 (Y : ℝ)) := by
    let g : ℝ → ℝ := fun t ↦ 1 / (t * (L - Real.log t) ^ 2)
    have hg : MeasureTheory.IntegrableOn g (Set.Icc 2 (Y : ℝ)) := by
      apply ContinuousOn.integrableOn_Icc
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
      have hlog : Real.log t ≤ Real.log (Y : ℝ) :=
        Real.log_le_log ht0 ht.2
      dsimp only [g]
      have hgapNe : L - Real.log t ≠ 0 := by linarith [hgap, hlog]
      have hden : t * (L - Real.log t) ^ 2 ≠ 0 :=
        mul_ne_zero ht0.ne' (pow_ne_zero 2 hgapNe)
      exact (continuousAt_const.div
        (continuousAt_id.mul
          ((continuousAt_const.sub (Real.continuousAt_log ht0.ne')).pow 2))
        hden).continuousWithinAt
    apply MeasureTheory.IntegrableOn.congr_fun hg _ measurableSet_Icc
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hlog : Real.log t ≤ Real.log (Y : ℝ) :=
      Real.log_le_log ht0 ht.2
    dsimp only [f, g]
    exact (hasDerivAt_reciprocalLogGap (L := L) ht0
      (by linarith [hgap, hlog])).deriv.symm
  have hab := sum_mul_eq_sub_integral_mul₁ primeLogWeight
    primeLogWeight_zero primeLogWeight_one (Y : ℝ) hdiff hint
  have hfloor : ⌊(Y : ℝ)⌋₊ = Y := Nat.floor_natCast Y
  have hsumY : (∑ k ∈ Finset.Icc 0 Y, primeLogWeight k) =
      Real.log (Y : ℝ) + Mertens.E₁p (Y : ℝ) := by
    calc
      (∑ k ∈ Finset.Icc 0 Y, primeLogWeight k) =
          ∑ p ∈ Finset.Ioc 0 Y with p.Prime,
            Real.log (p : ℝ) / (p : ℝ) := by
        simpa only [Nat.floor_natCast] using
          sum_Icc_primeLogWeight_eq (Y : ℝ)
      _ = Real.log (Y : ℝ) + Mertens.E₁p (Y : ℝ) := by
        simpa only [Nat.floor_natCast] using
          Mertens.sum_log_prime_div_eq (Y : ℝ)
  have hsumt : ∀ t : ℝ,
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogWeight k) =
        Real.log t + Mertens.E₁p t := by
    intro t
    rw [sum_Icc_primeLogWeight_eq]
    exact Mertens.sum_log_prime_div_eq t
  rw [hfloor, hsumY] at hab
  simp_rw [hsumt] at hab
  have hderivEq : ∀ t ∈ Set.Ioc 2 (Y : ℝ),
      deriv f t = 1 / (t * (L - Real.log t) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1.le
    have hlog : Real.log t ≤ Real.log (Y : ℝ) :=
      Real.log_le_log ht0 ht.2
    exact (hasDerivAt_reciprocalLogGap (L := L) ht0
      (by linarith [hgap, hlog])).deriv
  have hintEq :
      (∫ t in Set.Ioc 2 (Y : ℝ),
          deriv f t * (Real.log t + Mertens.E₁p t)) =
        ∫ t in Set.Ioc 2 (Y : ℝ),
          (1 / (t * (L - Real.log t) ^ 2)) *
            (Real.log t + Mertens.E₁p t) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro t ht
    change deriv f t * (Real.log t + Mertens.E₁p t) = _
    rw [hderivEq t ht]
  rw [hintEq] at hab
  have hleft :
      (∑ k ∈ Finset.Icc 0 Y, f (k : ℝ) * primeLogWeight k) =
        primeLogIncrement L Y := by
    rw [primeLogIncrement, Nat.primesLE_eq_filter_range]
    rw [show Finset.range (Y + 1) = Finset.Icc 0 Y by ext n; simp]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [primeLogWeight, f, reciprocalLogGap]
    split_ifs with hp
    · simp only [Pi.inv_apply, div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  rw [hleft] at hab
  simpa only [f] using hab

/-- The elementary integral underlying the endpoint constant. -/
theorem integral_reciprocal_log_gap
    {L B : ℝ} (hB : 2 ≤ B) (hgap : Real.log B < L) :
    ∫ t in 2..B, 1 / (t * (L - Real.log t)) =
      Real.log ((L - Real.log 2) / (L - Real.log B)) := by
  let F : ℝ → ℝ := -Real.log ∘ fun t ↦ L - Real.log t
  have hF : ∀ t ∈ Set.uIcc 2 B,
      HasDerivAt F (1 / (t * (L - Real.log t))) t := by
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hlog : Real.log t ≤ Real.log B := Real.log_le_log ht0 ht.2
    have hinner := (Real.hasDerivAt_log ht0.ne').const_sub L
    have hinnerPos : 0 < L - Real.log t := by linarith
    have hcomp := (Real.hasDerivAt_log hinnerPos.ne').comp t hinner |>.neg
    have hcoef : -((L - Real.log t)⁻¹ * (-t⁻¹)) =
        1 / (t * (L - Real.log t)) := by
      field_simp [ht0.ne', hinnerPos.ne']
    rw [hcoef] at hcomp
    exact hcomp
  have hExplicitInt : IntervalIntegrable
      (fun t : ℝ ↦ 1 / (t * (L - Real.log t)))
      MeasureTheory.volume 2 B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hlog : Real.log t ≤ Real.log B := Real.log_le_log ht0 ht.2
    have hgapNe : L - Real.log t ≠ 0 := by linarith
    have hden : t * (L - Real.log t) ≠ 0 := mul_ne_zero ht0.ne' hgapNe
    exact (continuousAt_const.div
      (continuousAt_id.mul
        (continuousAt_const.sub (Real.continuousAt_log ht0.ne')))
      hden).continuousWithinAt
  have hDerivInt : IntervalIntegrable (deriv F)
      MeasureTheory.volume 2 B := by
    exact hExplicitInt.congr fun t ht ↦
      (hF t (Set.uIoc_subset_uIcc ht)).deriv.symm
  calc
    (∫ t in 2..B, 1 / (t * (L - Real.log t))) = F B - F 2 := by
      calc
        (∫ t in 2..B, 1 / (t * (L - Real.log t))) =
            ∫ t in 2..B, deriv F t := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact (hF t ht).deriv.symm
        _ = F B - F 2 :=
          intervalIntegral.integral_deriv_eq_sub
            (fun t ht ↦ (hF t ht).differentiableAt) hDerivInt
    _ = Real.log ((L - Real.log 2) / (L - Real.log B)) := by
      dsimp only [F, Function.comp_apply]
      have htwo : 0 < L - Real.log 2 := by
        have hlogTwo : Real.log 2 ≤ Real.log B :=
          Real.log_le_log (by norm_num) hB
        linarith
      have hBpos : 0 < L - Real.log B := by linarith
      rw [Real.log_div htwo.ne' hBpos.ne']
      change -Real.log (L - Real.log B) - -Real.log (L - Real.log 2) = _
      ring

/-- Integration by parts separates the bounded Mertens error from the
explicit logarithmic integral. -/
theorem primeLogMain_partialIntegration
    {L B : ℝ} (hB : 2 ≤ B) (hgap : Real.log B < L) :
    reciprocalLogGap L B * Real.log B -
        ∫ t in Set.Ioc 2 B,
          (1 / (t * (L - Real.log t) ^ 2)) * Real.log t =
      Real.log ((L - Real.log 2) / (L - Real.log B)) +
        reciprocalLogGap L 2 * Real.log 2 := by
  let f : ℝ → ℝ := reciprocalLogGap L
  let fp : ℝ → ℝ := fun t ↦ 1 / (t * (L - Real.log t) ^ 2)
  let g : ℝ → ℝ := Real.log
  let gp : ℝ → ℝ := fun t ↦ 1 / t
  have hf : ∀ t ∈ Set.uIcc 2 B, HasDerivAt f (fp t) t := by
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hlog : Real.log t ≤ Real.log B := Real.log_le_log ht0 ht.2
    exact hasDerivAt_reciprocalLogGap ht0 (by linarith)
  have hg : ∀ t ∈ Set.uIcc 2 B, HasDerivAt g (gp t) t := by
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    simpa only [g, gp, one_div] using Real.hasDerivAt_log ht0.ne'
  have hfp : IntervalIntegrable fp MeasureTheory.volume 2 B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hlog : Real.log t ≤ Real.log B := Real.log_le_log ht0 ht.2
    have hgapNe : L - Real.log t ≠ 0 := by linarith
    have hden : t * (L - Real.log t) ^ 2 ≠ 0 :=
      mul_ne_zero ht0.ne' (pow_ne_zero 2 hgapNe)
    dsimp only [fp]
    exact (continuousAt_const.div
      (continuousAt_id.mul
        ((continuousAt_const.sub (Real.continuousAt_log ht0.ne')).pow 2))
      hden).continuousWithinAt
  have hgp : IntervalIntegrable gp MeasureTheory.volume 2 B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    dsimp only [gp]
    exact (continuousAt_const.div continuousAt_id ht0.ne').continuousWithinAt
  have hfc : ContinuousOn f (Set.uIcc 2 B) := fun t ht ↦
    (hf t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.uIcc 2 B) := fun t ht ↦
    (hg t ht).continuousAt.continuousWithinAt
  have hprod1 : IntervalIntegrable (fun t ↦ fp t * g t)
      MeasureTheory.volume 2 B := hfp.mul_continuousOn hgc
  have hprod2 : IntervalIntegrable (fun t ↦ f t * gp t)
      MeasureTheory.volume 2 B := hgp.continuousOn_mul hfc
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hf hg hfp hgp
  have hsetFp :
      (∫ t in Set.Ioc 2 B, fp t * g t) = ∫ t in 2..B, fp t * g t := by
    rw [intervalIntegral.integral_of_le hB]
  have hmainInt : (∫ t in 2..B, f t * gp t) =
      Real.log ((L - Real.log 2) / (L - Real.log B)) := by
    simpa only [f, gp, reciprocalLogGap, Pi.inv_apply, one_div,
      div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      integral_reciprocal_log_gap hB hgap
  rw [intervalIntegral.integral_add hprod1 hprod2, ← hsetFp, hmainInt] at hibp
  dsimp only [f, fp, g, gp] at hibp ⊢
  linarith

/-- Explicit bound for replacing the moving prime sum by its elementary
endpoint integral.  The constant is deliberately coarse; only its decay is
used later. -/
theorem abs_primeLogIncrement_sub_logRatio_le
    {L : ℝ} {Y : ℕ} (hY : 2 ≤ Y)
    (hgap : Real.log (Y : ℝ) < L) :
    |primeLogIncrement L Y -
        Real.log ((L - Real.log 2) / (L - Real.log (Y : ℝ)))| ≤
      (2 * (Real.log 4 + 4) + Real.log 2) /
        (L - Real.log (Y : ℝ)) := by
  let B : ℝ := Y
  let f : ℝ → ℝ := reciprocalLogGap L
  let fp : ℝ → ℝ := fun t ↦ 1 / (t * (L - Real.log t) ^ 2)
  let C : ℝ := Real.log 4 + 4
  have hB : 2 ≤ B := by dsimp only [B]; exact_mod_cast hY
  have hgapB : Real.log B < L := by simpa only [B] using hgap
  have hf : ∀ t ∈ Set.uIcc 2 B, HasDerivAt f (fp t) t := by
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hlog : Real.log t ≤ Real.log B := Real.log_le_log ht0 ht.2
    exact hasDerivAt_reciprocalLogGap ht0 (by linarith)
  have hfp : IntervalIntegrable fp MeasureTheory.volume 2 B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hlog : Real.log t ≤ Real.log B := Real.log_le_log ht0 ht.2
    have hgapNe : L - Real.log t ≠ 0 := by linarith
    have hden : t * (L - Real.log t) ^ 2 ≠ 0 :=
      mul_ne_zero ht0.ne' (pow_ne_zero 2 hgapNe)
    dsimp only [fp]
    exact (continuousAt_const.div
      (continuousAt_id.mul
        ((continuousAt_const.sub (Real.continuousAt_log ht0.ne')).pow 2))
      hden).continuousWithinAt
  have hE (t : ℝ) (ht : 1 ≤ t) : |Mertens.E₁p t| ≤ C := by
    simpa only [C, Mertens.E₁p] using Mertens.sum_log_prime_div_eq_log ht
  have hlogInt : MeasureTheory.IntegrableOn
      (fun t ↦ fp t * Real.log t) (Set.Ioc 2 B) := by
    have hfpSet := (intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mp hfp
    have h := hfpSet.bdd_mul Real.measurable_log.aestronglyMeasurable
      (show ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioc 2 B),
          ‖Real.log t‖ ≤ Real.log B by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg
          (Real.log_nonneg (by linarith [ht.1]))]
        exact Real.log_le_log (by linarith [ht.1]) ht.2)
    change MeasureTheory.Integrable (fun t ↦ fp t * Real.log t)
      (MeasureTheory.volume.restrict (Set.Ioc 2 B))
    simpa only [mul_comm] using h
  have hErrInt : MeasureTheory.IntegrableOn
      (fun t ↦ fp t * Mertens.E₁p t) (Set.Ioc 2 B) := by
    have hfpSet := (intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mp hfp
    have h := hfpSet.bdd_mul
      (Measurable.aestronglyMeasurable (by fun_prop))
      (show ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioc 2 B),
          ‖Mertens.E₁p t‖ ≤ C by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        simpa only [Real.norm_eq_abs] using hE t (by linarith [ht.1]))
    change MeasureTheory.Integrable (fun t ↦ fp t * Mertens.E₁p t)
      (MeasureTheory.volume.restrict (Set.Ioc 2 B))
    simpa only [mul_comm] using h
  have hsplit :
      (∫ t in Set.Ioc 2 B, fp t * (Real.log t + Mertens.E₁p t)) =
        (∫ t in Set.Ioc 2 B, fp t * Real.log t) +
          ∫ t in Set.Ioc 2 B, fp t * Mertens.E₁p t := by
    rw [← MeasureTheory.integral_add hlogInt hErrInt]
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro t _ht
    ring
  have hpartial := primeLogIncrement_partialSummation hY hgap
  change primeLogIncrement L Y =
      f B * (Real.log B + Mertens.E₁p B) -
        ∫ t in Set.Ioc 2 B, fp t * (Real.log t + Mertens.E₁p t) at hpartial
  rw [hsplit] at hpartial
  have hmain := primeLogMain_partialIntegration hB hgapB
  change f B * Real.log B -
      (∫ t in Set.Ioc 2 B, fp t * Real.log t) =
        Real.log ((L - Real.log 2) / (L - Real.log B)) +
          f 2 * Real.log 2 at hmain
  have hid : primeLogIncrement L Y -
        Real.log ((L - Real.log 2) / (L - Real.log B)) =
      f B * Mertens.E₁p B -
        (∫ t in Set.Ioc 2 B, fp t * Mertens.E₁p t) +
          f 2 * Real.log 2 := by
    linarith
  have hgapPos : 0 < L - Real.log B := by linarith
  have htwoLog : Real.log 2 ≤ Real.log B :=
    Real.log_le_log (by norm_num) hB
  have hgapTwo : 0 < L - Real.log 2 := by linarith
  have hfB : f B = 1 / (L - Real.log B) := by
    simp [f, reciprocalLogGap]
  have hf2 : f 2 = 1 / (L - Real.log 2) := by
    simp [f, reciprocalLogGap]
  have hfB0 : 0 ≤ f B := by rw [hfB]; positivity
  have hf20 : 0 ≤ f 2 := by rw [hf2]; positivity
  have hf2le : f 2 ≤ f B := by
    rw [hf2, hfB]
    exact one_div_le_one_div_of_le hgapPos (by linarith)
  have htermB : |f B * Mertens.E₁p B| ≤ C * f B := by
    rw [abs_mul, abs_of_nonneg hfB0]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hE B (by linarith)) hfB0
  have hfpIntegral : (∫ t in 2..B, fp t) = f B - f 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hf hfp
  have hErrIntegral :
      |∫ t in Set.Ioc 2 B, fp t * Mertens.E₁p t| ≤ C * (f B - f 2) := by
    rw [show (∫ t in Set.Ioc 2 B, fp t * Mertens.E₁p t) =
        ∫ t in 2..B, fp t * Mertens.E₁p t by
      rw [intervalIntegral.integral_of_le hB]]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le hB
      (f := fun t ↦ fp t * Mertens.E₁p t)
      (g := fun t ↦ C * fp t) ?_ (hfp.const_mul C)
    · rw [Real.norm_eq_abs] at hbound
      rw [intervalIntegral.integral_const_mul, hfpIntegral] at hbound
      exact hbound
    · filter_upwards with t
      intro ht
      rw [Real.norm_eq_abs, abs_mul]
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1.le
      have hlog : Real.log t ≤ Real.log B := Real.log_le_log ht0 ht.2
      have hfp0 : 0 ≤ fp t := by
        dsimp only [fp]
        positivity
      rw [abs_of_nonneg hfp0]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hE t (by linarith [ht.1])) hfp0
  have hboundary : |f 2 * Real.log 2| ≤ Real.log 2 * f B := by
    rw [abs_mul, abs_of_nonneg hf20, abs_of_nonneg (Real.log_nonneg (by norm_num))]
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  rw [hid]
  calc
    |f B * Mertens.E₁p B -
        (∫ t in Set.Ioc 2 B, fp t * Mertens.E₁p t) +
          f 2 * Real.log 2| ≤
        |f B * Mertens.E₁p B| +
          |∫ t in Set.Ioc 2 B, fp t * Mertens.E₁p t| +
            |f 2 * Real.log 2| := by
      calc
        |_ + _| ≤ |f B * Mertens.E₁p B -
            (∫ t in Set.Ioc 2 B, fp t * Mertens.E₁p t)| +
              |f 2 * Real.log 2| := by
                simpa only [Real.norm_eq_abs] using
                  norm_add_le
                    (f B * Mertens.E₁p B -
                      (∫ t in Set.Ioc 2 B, fp t * Mertens.E₁p t))
                    (f 2 * Real.log 2)
        _ ≤ (|f B * Mertens.E₁p B| +
              |∫ t in Set.Ioc 2 B, fp t * Mertens.E₁p t|) +
                |f 2 * Real.log 2| := by gcongr; exact abs_sub _ _
    _ ≤ C * f B + C * (f B - f 2) + Real.log 2 * f B := by
      gcongr
    _ ≤ (2 * C + Real.log 2) * f B := by
      have hC0 : 0 ≤ C := by dsimp only [C]; positivity
      nlinarith
    _ = (2 * (Real.log 4 + 4) + Real.log 2) /
          (L - Real.log (Y : ℝ)) := by
      rw [hfB]
      dsimp only [C, B]
      ring

/-! ## The square-root endpoint -/

/-- The integer square root, cast to the reals, is asymptotic to the real
square root. -/
theorem natSqrtCast_isEquivalent_realSqrt :
    Asymptotics.IsEquivalent atTop
      (fun X : ℕ ↦ (Nat.sqrt X : ℝ))
      (fun X : ℕ ↦ Real.sqrt (X : ℝ)) := by
  apply Asymptotics.IsLittleO.isEquivalent
  rw [Asymptotics.isLittleO_iff]
  intro eps heps
  have hsqrt : Tendsto (fun X : ℕ ↦ Real.sqrt (X : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ X : ℕ in atTop,
      1 ≤ eps * Real.sqrt (X : ℝ) :=
    (hsqrt.eventually_ge_atTop (1 / eps)).mono fun X hX ↦ by
      have heps0 : eps ≠ 0 := ne_of_gt heps
      calc
        1 = eps * (1 / eps) := by field_simp
        _ ≤ eps * Real.sqrt (X : ℝ) :=
          mul_le_mul_of_nonneg_left hX heps.le
  filter_upwards [hlarge] with X hX
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hlo := Real.nat_sqrt_le_real_sqrt (a := X)
  have hhi := Real.real_sqrt_lt_nat_sqrt_succ (a := X)
  have hdiff : |(Nat.sqrt X : ℝ) - Real.sqrt (X : ℝ)| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hdiff.trans hX

/-- Taking logarithms preserves the square-root asymptotic. -/
theorem log_natSqrt_isEquivalent_halfLog :
    Asymptotics.IsEquivalent atTop
      (fun X : ℕ ↦ Real.log (Nat.sqrt X : ℝ))
      (fun X : ℕ ↦ Real.log (X : ℝ) / 2) := by
  have hsqrtTop : Tendsto (fun X : ℕ ↦ Real.sqrt (X : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := natSqrtCast_isEquivalent_realSqrt.log hsqrtTop
  simpa only [Real.log_sqrt (Nat.cast_nonneg _)] using hlog

/-- The logarithm of the integer square root has limiting ratio `1 / 2`
against `log X`. -/
theorem log_natSqrt_div_log_tendsto_half :
    Tendsto
      (fun X : ℕ ↦ Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden : Asymptotics.IsEquivalent atTop
      (fun X : ℕ ↦ Real.log (X : ℝ))
      (fun X : ℕ ↦ Real.log (X : ℝ)) := Asymptotics.IsEquivalent.refl
  have hdiv := log_natSqrt_isEquivalent_halfLog.div hden
  have hconst : (fun X : ℕ ↦
      (Real.log (X : ℝ) / 2) / Real.log (X : ℝ)) =ᶠ[atTop]
      (fun _ : ℕ ↦ (1 / 2 : ℝ)) := by
    filter_upwards [hlogTop.eventually_ne_atTop 0] with X hX
    field_simp
  have hdiv' : Asymptotics.IsEquivalent atTop
      (fun X : ℕ ↦ Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ))
      (fun _ : ℕ ↦ (1 / 2 : ℝ)) := hdiv.congr_right hconst
  exact (Asymptotics.isEquivalent_const_iff_tendsto (by norm_num)).mp hdiv'

/-- The logarithmic scale relevant to a fixed centre `c`. -/
def fixedCenterLogScale (c X : ℕ) : ℝ :=
  Real.log (X : ℝ) - Real.log (c : ℝ)

/-- At the square-root endpoint, the quotient in the Abel main term tends
to `2`. -/
theorem fixedCenter_logEndpointRatio_tendsto
    {c : ℕ} (hc : 0 < c) :
    Tendsto
      (fun X : ℕ ↦
        (fixedCenterLogScale c X - Real.log 2) /
          (fixedCenterLogScale c X - Real.log (Nat.sqrt X : ℝ)))
      atTop (𝓝 2) := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcTerm : Tendsto
      (fun X : ℕ ↦ Real.log (c : ℝ) / Real.log (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogTop
  have htwoTerm : Tendsto
      (fun X : ℕ ↦ Real.log 2 / Real.log (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogTop
  have hnum : Tendsto
      (fun X : ℕ ↦
        (fixedCenterLogScale c X - Real.log 2) / Real.log (X : ℝ))
      atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := (hone.sub hcTerm).sub htwoTerm
    norm_num at h
    refine h.congr' ?_
    filter_upwards [hlogTop.eventually_ne_atTop 0] with X hX
    field_simp [fixedCenterLogScale, hX]
    rfl
  have hden : Tendsto
      (fun X : ℕ ↦
        (fixedCenterLogScale c X - Real.log (Nat.sqrt X : ℝ)) /
          Real.log (X : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := (hone.sub hcTerm).sub log_natSqrt_div_log_tendsto_half
    norm_num at h
    refine h.congr' ?_
    filter_upwards [hlogTop.eventually_ne_atTop 0] with X hX
    field_simp [fixedCenterLogScale, hX]
    rfl
  have hraw := hnum.div hden (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hfun :
      ((fun X : ℕ ↦ (fixedCenterLogScale c X - Real.log 2) / Real.log (X : ℝ)) /
          fun X : ℕ ↦
            (fixedCenterLogScale c X - Real.log (Nat.sqrt X : ℝ)) /
              Real.log (X : ℝ)) =ᶠ[atTop]
        fun X : ℕ ↦
          (fixedCenterLogScale c X - Real.log 2) /
            (fixedCenterLogScale c X - Real.log (Nat.sqrt X : ℝ)) := by
    filter_upwards [hlogTop.eventually_ne_atTop 0] with X hX
    simp only [Pi.div_apply]
    field_simp [hX]
  have h := hraw.congr' hfun
  simpa using h

/-- The denominator in the moving endpoint formula tends to infinity. -/
theorem fixedCenter_logGap_tendsto_atTop
    {c : ℕ} (hc : 0 < c) :
    Tendsto
      (fun X : ℕ ↦
        fixedCenterLogScale c X - Real.log (Nat.sqrt X : ℝ))
      atTop atTop := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcTerm : Tendsto
      (fun X : ℕ ↦ Real.log (c : ℝ) / Real.log (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogTop
  have hdenNorm : Tendsto
      (fun X : ℕ ↦
        (fixedCenterLogScale c X - Real.log (Nat.sqrt X : ℝ)) /
          Real.log (X : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := (hone.sub hcTerm).sub log_natSqrt_div_log_tendsto_half
    norm_num at h
    refine h.congr' ?_
    filter_upwards [hlogTop.eventually_ne_atTop 0] with X hX
    field_simp [fixedCenterLogScale, hX]
    rfl
  have hprod := hdenNorm.pos_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 2) hlogTop
  apply hprod.congr'
  filter_upwards [hlogTop.eventually_ne_atTop 0] with X hX
  field_simp [hX]

/-- The moving logarithmic prime increment at the square-root endpoint tends
to `log 2`. -/
theorem fixedCenter_primeLogIncrement_tendsto_log_two
    {c : ℕ} (hc : 0 < c) :
    Tendsto
      (fun X : ℕ ↦
        primeLogIncrement (fixedCenterLogScale c X) (Nat.sqrt X))
      atTop (𝓝 (Real.log 2)) := by
  let endpoint : ℕ → ℝ := fun X ↦
    Real.log ((fixedCenterLogScale c X - Real.log 2) /
      (fixedCenterLogScale c X - Real.log (Nat.sqrt X : ℝ)))
  let bound : ℕ → ℝ := fun X ↦
    (2 * (Real.log 4 + 4) + Real.log 2) /
      (fixedCenterLogScale c X - Real.log (Nat.sqrt X : ℝ))
  have hgapTop := fixedCenter_logGap_tendsto_atTop hc
  have hratio := fixedCenter_logEndpointRatio_tendsto hc
  have hendpoint : Tendsto endpoint atTop (𝓝 (Real.log 2)) := by
    exact (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hratio
  have hbound : Tendsto bound atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hgapTop
  have hsqrtTop : Tendsto (fun X : ℕ ↦ Real.sqrt (X : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtNatCast : Tendsto (fun X : ℕ ↦ (Nat.sqrt X : ℝ)) atTop atTop :=
    natSqrtCast_isEquivalent_realSqrt.symm.tendsto_atTop hsqrtTop
  have hY : ∀ᶠ X : ℕ in atTop, 2 ≤ Nat.sqrt X := by
    filter_upwards [hsqrtNatCast.eventually_ge_atTop 2] with X hX
    exact_mod_cast hX
  have hgap : ∀ᶠ X : ℕ in atTop,
      Real.log (Nat.sqrt X : ℝ) < fixedCenterLogScale c X := by
    filter_upwards [hgapTop.eventually_gt_atTop 0] with X hX
    linarith
  have hdiff : Tendsto
      (fun X : ℕ ↦
        primeLogIncrement (fixedCenterLogScale c X) (Nat.sqrt X) - endpoint X)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hY, hgap] with X hYX hgapX
    have h := abs_primeLogIncrement_sub_logRatio_le hYX hgapX
    simp only [Real.norm_eq_abs, endpoint, bound]
    exact h
  have hsum := hdiff.add hendpoint
  convert hsum using 1
  · funext X
    dsimp only [endpoint]
    ring
  · norm_num

end

end PrimeStar
