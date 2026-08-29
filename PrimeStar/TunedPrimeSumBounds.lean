import PrimeStar.PrimePowerSum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Scalar bounds for the tuned Schur weight

This module closes the elementary incoming-divisor contribution at the tuned
scale and prepares the real-variable estimates used for the outgoing Abel
integral. No prime number theorem is used.
-/

namespace PrimeStar

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Local decidability for residual adjacency in tuned prime-sum bounds. -/
local instance tunedPrimeSumDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

private theorem sum_primeIndicator_Icc (m : ℕ) :
    ∑ k ∈ Finset.Icc 0 m, (if k.Prime then (1 : ℝ) else 0) =
      Nat.primeCounting m := by
  rw [← Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_eq_filter_Icc_zero, Finset.card_eq_sum_ones]
  simp

/-- The elementary counting bound used on the lower half of the Abel
integral.  It deliberately counts every integer, not only the primes. -/
theorem primeCounting_floor_le_add_one (t : ℝ) (ht : 0 ≤ t) :
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ t + 1 := by
  have hcard : Nat.primeCounting ⌊t⌋₊ ≤ ⌊t⌋₊ + 1 := by
    rw [← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_eq_filter_range]
    simpa using Finset.card_filter_le (Finset.range (⌊t⌋₊ + 1)) Nat.Prime
  calc
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (⌊t⌋₊ + 1 : ℕ) := by exact_mod_cast hcard
    _ = (⌊t⌋₊ : ℝ) + 1 := by norm_num
    _ ≤ t + 1 := by
      gcongr
      exact Nat.floor_le ht

/-- A convenient explicit antiderivative bound on the lower half of the Abel
integral. -/
theorem integral_rpow_neg_three_eighths_le {b : ℝ} (_hb : 2 ≤ b) :
    (∫ t in (2 : ℝ)..b, t ^ (-3 / 8 : ℝ)) ≤
      (8 / 5 : ℝ) * b ^ (5 / 8 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -3 / 8))]
  have hpow : 0 ≤ (2 : ℝ) ^ (5 / 8 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hden : (-3 / 8 : ℝ) + 1 = 5 / 8 := by norm_num
  rw [hden]
  nlinarith

/-- On a positive interval, the variable-exponent integral is controlled by
its upper endpoint as soon as the exponent is at most one half. -/
theorem integral_rpow_neg_le_two_mul_upper
    {a b θ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (_hθnonneg : 0 ≤ θ) (hθhalf : θ ≤ 1 / 2) :
    (∫ t in a..b, t ^ (-θ)) ≤ 2 * b ^ (1 - θ) := by
  have hθone : θ < 1 := lt_of_le_of_lt hθhalf (by norm_num)
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -θ))]
  have hden : 0 < 1 - θ := sub_pos.mpr hθone
  have haPow : 0 ≤ a ^ (1 - θ) := Real.rpow_nonneg ha.le _
  have hbPow : 0 ≤ b ^ (1 - θ) :=
    Real.rpow_nonneg (ha.le.trans hab) _
  rw [show -θ + 1 = 1 - θ by ring]
  apply (div_le_iff₀ hden).2
  nlinarith

/-- A second explicit antiderivative bound for the square-root error in the
Chebyshev estimate. -/
theorem integral_rpow_neg_seven_eighths_le {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, t ^ (-7 / 8 : ℝ)) ≤
      8 * b ^ (1 / 8 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -7 / 8))]
  have haPow : 0 ≤ a ^ (1 / 8 : ℝ) := Real.rpow_nonneg ha _
  have hbPow : 0 ≤ b ^ (1 / 8 : ℝ) :=
    Real.rpow_nonneg (ha.trans hab) _
  have hden : (-7 / 8 : ℝ) + 1 = 1 / 8 := by norm_num
  rw [hden]
  nlinarith

/-- The tuned exponent eventually stays in the compact interval
`[3 / 8, 1 / 2]`. -/
theorem eventually_tunedSchurExponent_mem :
    ∀ᶠ Y : ℕ in atTop,
      (3 / 8 : ℝ) ≤ tunedSchurExponent (Y : ℝ) ∧
        tunedSchurExponent (Y : ℝ) ≤ 1 / 2 := by
  have hratioReal :=
    (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).bound
      (by norm_num : (0 : ℝ) < 1 / 4)
  have hratioNat := tendsto_natCast_atTop_atTop.eventually hratioReal
  have hlogY : ∀ᶠ Y : ℕ in atTop, 1 < Real.log (Y : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop 1)
  filter_upwards [hratioNat, hlogY] with Y hratio hlogY
  have hlogpos : 0 < Real.log (Y : ℝ) := zero_lt_one.trans hlogY
  have hloglogpos : 0 ≤ Real.log (Real.log (Y : ℝ)) :=
    Real.log_nonneg hlogY.le
  have hratio' :
      Real.log (Real.log (Y : ℝ)) ≤ (1 / 4 : ℝ) * Real.log (Y : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hloglogpos,
      abs_of_nonneg hlogpos.le, id] using hratio
  constructor
  · rw [tunedSchurExponent]
    have hden : 0 < 2 * Real.log (Y : ℝ) := mul_pos (by norm_num) hlogpos
    have hdiv :
        Real.log (Real.log (Y : ℝ)) / (2 * Real.log (Y : ℝ)) ≤ 1 / 8 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith
  · exact (tunedSchurExponent_lt_half hlogY).le

/-- The explicit Chebyshev estimate, rewritten uniformly on the upper half
`[√Y, Y]` of the Abel integral. -/
theorem primeCounting_floor_le_on_sqrt_interval
    {Y t : ℝ} (hY : 1 < Y) (hst : √Y ≤ t) :
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
      (4 * Real.log 4 / Real.log Y) * t + √t := by
  have hYpos : 0 < Y := zero_lt_one.trans hY
  have hsqrtpos : 0 < √Y := Real.sqrt_pos.2 hYpos
  have htpos : 0 < t := hsqrtpos.trans_le hst
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have htone : 1 < t := by
    have honeSqrt : (1 : ℝ) < √Y :=
      (Real.lt_sqrt (by norm_num)).2 (by simpa using hY)
    exact honeSqrt.trans_le hst
  have hlogt : 0 < Real.log t := Real.log_pos htone
  have hlogLower : Real.log Y / 2 ≤ Real.log t := by
    calc
      Real.log Y / 2 = Real.log √Y := by
        rw [Real.log_sqrt hYpos.le]
      _ ≤ Real.log t := Real.log_le_log hsqrtpos hst
  have hfrac : 2 / Real.log t ≤ 4 / Real.log Y := by
    rw [div_le_div_iff₀ hlogt hlogY]
    nlinarith
  calc
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤
        Real.log 4 * t / Real.log √t + √t :=
      Chebyshev.pi_le_log4_mul_div htone
    _ = (2 * Real.log 4 / Real.log t) * t + √t := by
      rw [Real.log_sqrt htpos.le]
      field_simp
    _ ≤ (4 * Real.log 4 / Real.log Y) * t + √t := by
      have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hcoef :
          2 * Real.log 4 / Real.log t ≤ 4 * Real.log 4 / Real.log Y := by
        calc
          2 * Real.log 4 / Real.log t =
              (2 / Real.log t) * Real.log 4 := by ring
          _ ≤ (4 / Real.log Y) * Real.log 4 := by gcongr
          _ = 4 * Real.log 4 / Real.log Y := by ring
      gcongr

/-- Pointwise lower-half estimate for the Abel integrand. -/
theorem abelPrimeIntegrand_le_lower
    {t θ : ℝ} (ht : 2 ≤ t) (hθ : 3 / 8 ≤ θ) :
    t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊ ≤
      2 * t ^ (-3 / 8 : ℝ) := by
  have htpos : 0 < t := by linarith
  have htone : 1 ≤ t := by linarith
  have hpi : (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ 2 * t := by
    calc
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ t + 1 :=
        primeCounting_floor_le_add_one t htpos.le
      _ ≤ 2 * t := by linarith
  calc
    t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊ ≤
        t ^ (-θ - 1) * (2 * t) := by
      gcongr
    _ = 2 * t ^ (-θ) := by
      calc
        t ^ (-θ - 1) * (2 * t) =
            2 * (t ^ (-θ - 1) * t) := by ring
        _ = 2 * (t ^ (-θ - 1) * t ^ (1 : ℝ)) := by
          rw [Real.rpow_one]
        _ = 2 * t ^ ((-θ - 1) + 1) := by
          rw [Real.rpow_add htpos]
        _ = 2 * t ^ (-θ) := by ring_nf
    _ ≤ 2 * t ^ (-3 / 8 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le htone (by linarith)) (by norm_num)

/-- Pointwise upper-half estimate for the Abel integrand. -/
theorem abelPrimeIntegrand_le_upper
    {Y t θ : ℝ} (hY : 1 < Y) (hst : √Y ≤ t)
    (hθ : 3 / 8 ≤ θ) :
    t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊ ≤
      (4 * Real.log 4 / Real.log Y) * t ^ (-θ) +
        t ^ (-7 / 8 : ℝ) := by
  have hYpos : 0 < Y := zero_lt_one.trans hY
  have htpos : 0 < t := (Real.sqrt_pos.2 hYpos).trans_le hst
  have htone : 1 ≤ t := by
    have honeSqrt : (1 : ℝ) < √Y :=
      (Real.lt_sqrt (by norm_num)).2 (by simpa using hY)
    exact (honeSqrt.trans_le hst).le
  calc
    t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊ ≤
        t ^ (-θ - 1) *
          ((4 * Real.log 4 / Real.log Y) * t + √t) := by
      gcongr
      exact primeCounting_floor_le_on_sqrt_interval hY hst
    _ = (4 * Real.log 4 / Real.log Y) * t ^ (-θ) +
        t ^ (-θ - 1 / 2) := by
      rw [Real.sqrt_eq_rpow]
      have hmulOne : t ^ (-θ - 1) * t = t ^ (-θ) := by
        calc
          t ^ (-θ - 1) * t = t ^ (-θ - 1) * t ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = t ^ ((-θ - 1) + 1) := by rw [Real.rpow_add htpos]
          _ = t ^ (-θ) := by ring_nf
      have hmulHalf :
          t ^ (-θ - 1) * t ^ (1 / 2 : ℝ) = t ^ (-θ - 1 / 2) := by
        rw [← Real.rpow_add htpos]
        congr 1
        ring
      have hfirst :
          t ^ (-θ - 1) * (4 * Real.log 4 / Real.log Y * t) =
            (4 * Real.log 4 / Real.log Y) * t ^ (-θ) := by
        calc
          t ^ (-θ - 1) * (4 * Real.log 4 / Real.log Y * t) =
              (4 * Real.log 4 / Real.log Y) *
                (t ^ (-θ - 1) * t) := by ring
          _ = (4 * Real.log 4 / Real.log Y) * t ^ (-θ) := by rw [hmulOne]
      rw [mul_add, hfirst, hmulHalf]
    _ ≤ (4 * Real.log 4 / Real.log Y) * t ^ (-θ) +
        t ^ (-7 / 8 : ℝ) := by
      have hexp : -θ - 1 / 2 ≤ (-7 / 8 : ℝ) := by linarith
      have hrpow : t ^ (-θ - 1 / 2) ≤ t ^ (-7 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le htone hexp
      linarith

/-- The Abel step integrand is interval-integrable on every positive compact
interval.  This is a direct use of the step-function integrability theorem
underlying Abel summation in mathlib. -/
theorem abelPrimeIntegrand_intervalIntegrable
    {a b θ : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ ↦ t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊)
      MeasureTheory.volume a b := by
  have hg : MeasureTheory.IntegrableOn (fun t : ℝ ↦ t ^ (-θ - 1))
      (Set.Icc a b) := by
    exact ContinuousOn.integrableOn_Icc fun t ht ↦
      (Real.continuousAt_rpow_const t (-θ - 1)
        (Or.inl (by linarith [ht.1]))).continuousWithinAt
  have hstep := integrableOn_mul_sum_Icc
    (c := fun k : ℕ ↦ if k.Prime then (1 : ℝ) else 0)
    (m := 0) ha.le hg
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  refine hstep.congr_fun ?_ measurableSet_Icc
  intro t ht
  change t ^ (-θ - 1) *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then (1 : ℝ) else 0)) =
    t ^ (-θ - 1) * (Nat.primeCounting ⌊t⌋₊ : ℝ)
  rw [sum_primeIndicator_Icc]

/-- Explicit two-piece bound for the Abel integral. -/
theorem abelPrimeIntegral_le
    {Y θ : ℝ} (hY : 4 ≤ Y)
    (hθlow : 3 / 8 ≤ θ) (hθhigh : θ ≤ 1 / 2) :
    (∫ t in Set.Ioc (2 : ℝ) Y,
        t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊) ≤
      (16 / 5 : ℝ) * Y ^ (5 / 16 : ℝ) +
        (8 * Real.log 4 / Real.log Y) * Y ^ (1 - θ) +
        8 * Y ^ (1 / 8 : ℝ) := by
  have hYpos : 0 < Y := by linarith
  have hYone : 1 < Y := by linarith
  have htwoY : (2 : ℝ) ≤ Y := by linarith
  have htwoSqrt : (2 : ℝ) ≤ √Y :=
    (Real.le_sqrt (by norm_num) hYpos.le).2 (by norm_num; linarith)
  have hsqrtY : √Y ≤ Y := by
    rw [Real.sqrt_le_left hYpos.le]
    nlinarith
  let f : ℝ → ℝ := fun t ↦
    t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊
  let g₁ : ℝ → ℝ := fun t ↦ 2 * t ^ (-3 / 8 : ℝ)
  let g₂ : ℝ → ℝ := fun t ↦
    (4 * Real.log 4 / Real.log Y) * t ^ (-θ) + t ^ (-7 / 8 : ℝ)
  have hf₁ : IntervalIntegrable f MeasureTheory.volume 2 √Y := by
    exact abelPrimeIntegrand_intervalIntegrable (by norm_num) htwoSqrt
  have hf₂ : IntervalIntegrable f MeasureTheory.volume √Y Y := by
    exact abelPrimeIntegrand_intervalIntegrable (Real.sqrt_pos.2 hYpos) hsqrtY
  have hg₁ : IntervalIntegrable g₁ MeasureTheory.volume 2 √Y := by
    exact (intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -3 / 8)).const_mul 2
  have hg₂ : IntervalIntegrable g₂ MeasureTheory.volume √Y Y := by
    exact ((intervalIntegral.intervalIntegrable_rpow'
      (by linarith : (-1 : ℝ) < -θ)).const_mul
        (4 * Real.log 4 / Real.log Y)).add
      (intervalIntegral.intervalIntegrable_rpow'
        (by norm_num : (-1 : ℝ) < -7 / 8))
  have hlow :
      (∫ t in (2 : ℝ)..√Y, f t) ≤
        (16 / 5 : ℝ) * Y ^ (5 / 16 : ℝ) := by
    calc
      (∫ t in (2 : ℝ)..√Y, f t) ≤ ∫ t in (2 : ℝ)..√Y, g₁ t := by
        apply intervalIntegral.integral_mono_on htwoSqrt hf₁ hg₁
        intro t ht
        exact abelPrimeIntegrand_le_lower ht.1 hθlow
      _ = 2 * ∫ t in (2 : ℝ)..√Y, t ^ (-3 / 8 : ℝ) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ 2 * ((8 / 5 : ℝ) * (√Y) ^ (5 / 8 : ℝ)) := by
        gcongr
        exact integral_rpow_neg_three_eighths_le htwoSqrt
      _ = (16 / 5 : ℝ) * Y ^ (5 / 16 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hYpos.le]
        norm_num
        ring
  have hhigh :
      (∫ t in √Y..Y, f t) ≤
        (8 * Real.log 4 / Real.log Y) * Y ^ (1 - θ) +
          8 * Y ^ (1 / 8 : ℝ) := by
    calc
      (∫ t in √Y..Y, f t) ≤ ∫ t in √Y..Y, g₂ t := by
        apply intervalIntegral.integral_mono_on hsqrtY hf₂ hg₂
        intro t ht
        exact abelPrimeIntegrand_le_upper hYone ht.1 hθlow
      _ = (4 * Real.log 4 / Real.log Y) *
            (∫ t in √Y..Y, t ^ (-θ)) +
          ∫ t in √Y..Y, t ^ (-7 / 8 : ℝ) := by
        rw [intervalIntegral.integral_add,
          intervalIntegral.integral_const_mul]
        · exact (intervalIntegral.intervalIntegrable_rpow'
            (by linarith : (-1 : ℝ) < -θ)).const_mul _
        · exact intervalIntegral.intervalIntegrable_rpow'
            (by norm_num : (-1 : ℝ) < -7 / 8)
      _ ≤ (4 * Real.log 4 / Real.log Y) *
            (2 * Y ^ (1 - θ)) + 8 * Y ^ (1 / 8 : ℝ) := by
        have hcoef : 0 ≤ 4 * Real.log 4 / Real.log Y := by
          exact div_nonneg
            (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
            (Real.log_pos hYone).le
        have hmain :
            (∫ t in √Y..Y, t ^ (-θ)) ≤ 2 * Y ^ (1 - θ) :=
          integral_rpow_neg_le_two_mul_upper
            (Real.sqrt_pos.2 hYpos) hsqrtY (by linarith) hθhigh
        have herr :
            (∫ t in √Y..Y, t ^ (-7 / 8 : ℝ)) ≤
              8 * Y ^ (1 / 8 : ℝ) :=
          integral_rpow_neg_seven_eighths_le (Real.sqrt_nonneg Y) hsqrtY
        exact add_le_add (mul_le_mul_of_nonneg_left hmain hcoef) herr
      _ = (8 * Real.log 4 / Real.log Y) * Y ^ (1 - θ) +
          8 * Y ^ (1 / 8 : ℝ) := by ring
  have hsetInterval :
      (∫ t in Set.Ioc (2 : ℝ) Y, f t) = ∫ t in (2 : ℝ)..Y, f t := by
    have h := intervalIntegral.intervalIntegral_eq_integral_uIoc
      f (2 : ℝ) Y MeasureTheory.volume
    simpa [if_pos htwoY, Set.uIoc_of_le htwoY] using h.symm
  change (∫ t in Set.Ioc (2 : ℝ) Y, f t) ≤ _
  rw [hsetInterval, ← intervalIntegral.integral_add_adjacent_intervals hf₁ hf₂]
  linarith

/-- The outgoing prime-power sum is bounded at the tuned Schur scale, with an
explicit absolute constant.  This uses only Abel summation and Chebyshev's
elementary upper bound for the prime-counting function. -/
theorem outgoingPrimePowerSum_le_tuned
    {Y : ℕ} (hY : 4 ≤ Y) (hlogY : 1 < Real.log (Y : ℝ))
    (hθmem : (3 / 8 : ℝ) ≤ tunedSchurExponent (Y : ℝ) ∧
      tunedSchurExponent (Y : ℝ) ≤ 1 / 2) :
    outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) ≤
      (12 * Real.log 4 + 13) * tunedSchurScale (Y : ℝ) := by
  let y : ℝ := Y
  let θ : ℝ := tunedSchurExponent y
  have hyfour : (4 : ℝ) ≤ y := by
    change (4 : ℝ) ≤ (Y : ℝ)
    exact_mod_cast hY
  have hypos : 0 < y := by linarith
  have hyone : 1 < y := by linarith
  have hygeone : 1 ≤ y := hyone.le
  have hθlow : (3 / 8 : ℝ) ≤ θ := hθmem.1
  have hθhigh : θ ≤ 1 / 2 := hθmem.2
  have hθnonneg : 0 ≤ θ := by linarith
  have hθone : θ ≤ 1 := hθhigh.trans (by norm_num)
  have hsqrtY : √y ≤ y := by
    rw [Real.sqrt_le_left hypos.le]
    nlinarith
  have hscalePow : y ^ θ = tunedSchurScale y :=
    rpow_tunedSchurExponent_eq_scale hypos hlogY
  have hmainScale : y ^ (1 - θ) / Real.log y = tunedSchurScale y :=
    rpow_one_sub_tunedSchurExponent_div_log_eq_scale hypos hlogY
  have hsmallFive : y ^ (5 / 16 : ℝ) ≤ tunedSchurScale y := by
    rw [← hscalePow]
    exact Real.rpow_le_rpow_of_exponent_le hygeone (by linarith)
  have hsmallOne : y ^ (1 / 8 : ℝ) ≤ tunedSchurScale y := by
    rw [← hscalePow]
    exact Real.rpow_le_rpow_of_exponent_le hygeone (by linarith)
  have hpoint := abelPrimeIntegrand_le_upper
    (Y := y) (t := y) (hθ := hθlow) hyone hsqrtY
  have hendpointRaw :
      y ^ (-θ) * Nat.primeCounting Y ≤
        (4 * Real.log 4 / Real.log y) * y ^ (1 - θ) +
          y ^ (1 / 8 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hpoint hypos.le
    have hleftPow : y * y ^ (-θ - 1) = y ^ (-θ) := by
      calc
        y * y ^ (-θ - 1) = y ^ (1 : ℝ) * y ^ (-θ - 1) := by rw [Real.rpow_one]
        _ = y ^ ((1 : ℝ) + (-θ - 1)) := by rw [Real.rpow_add hypos]
        _ = y ^ (-θ) := by ring_nf
    have hmainPow : y * y ^ (-θ) = y ^ (1 - θ) := by
      calc
        y * y ^ (-θ) = y ^ (1 : ℝ) * y ^ (-θ) := by rw [Real.rpow_one]
        _ = y ^ ((1 : ℝ) + (-θ)) := by rw [Real.rpow_add hypos]
        _ = y ^ (1 - θ) := by ring_nf
    have herrPow : y * y ^ (-7 / 8 : ℝ) = y ^ (1 / 8 : ℝ) := by
      calc
        y * y ^ (-7 / 8 : ℝ) = y ^ (1 : ℝ) * y ^ (-7 / 8 : ℝ) := by
          rw [Real.rpow_one]
        _ = y ^ ((1 : ℝ) + (-7 / 8 : ℝ)) := by rw [Real.rpow_add hypos]
        _ = y ^ (1 / 8 : ℝ) := by norm_num
    rw [show ⌊y⌋₊ = Y by simp [y]] at hmul
    change y * (y ^ (-θ - 1) * Nat.primeCounting Y) ≤ _ at hmul
    rw [← mul_assoc, hleftPow, mul_add] at hmul
    have hmainReorder :
        y * ((4 * Real.log 4 / Real.log y) * y ^ (-θ)) =
          (4 * Real.log 4 / Real.log y) * y ^ (1 - θ) := by
      calc
        y * ((4 * Real.log 4 / Real.log y) * y ^ (-θ)) =
            (4 * Real.log 4 / Real.log y) * (y * y ^ (-θ)) := by ring
        _ = _ := by rw [hmainPow]
    rw [hmainReorder, herrPow] at hmul
    exact hmul
  have hendpoint :
      y ^ (-θ) * Nat.primeCounting Y ≤
        (4 * Real.log 4 + 1) * tunedSchurScale y := by
    calc
      y ^ (-θ) * Nat.primeCounting Y ≤
          (4 * Real.log 4 / Real.log y) * y ^ (1 - θ) +
            y ^ (1 / 8 : ℝ) := hendpointRaw
      _ = 4 * Real.log 4 *
            (y ^ (1 - θ) / Real.log y) + y ^ (1 / 8 : ℝ) := by ring
      _ ≤ 4 * Real.log 4 * tunedSchurScale y + tunedSchurScale y := by
        rw [hmainScale]
        gcongr
      _ = (4 * Real.log 4 + 1) * tunedSchurScale y := by ring
  let R : ℝ :=
    (16 / 5 : ℝ) * y ^ (5 / 16 : ℝ) +
      (8 * Real.log 4 / Real.log y) * y ^ (1 - θ) +
      8 * y ^ (1 / 8 : ℝ)
  have hIntegral :
      (∫ t in Set.Ioc (2 : ℝ) y,
          t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊) ≤ R := by
    exact abelPrimeIntegral_le hyfour hθlow hθhigh
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hRscale : R ≤ (8 * Real.log 4 + 12) * tunedSchurScale y := by
    dsimp [R]
    calc
      (16 / 5 : ℝ) * y ^ (5 / 16 : ℝ) +
            (8 * Real.log 4 / Real.log y) * y ^ (1 - θ) +
            8 * y ^ (1 / 8 : ℝ) ≤
          (16 / 5 : ℝ) * tunedSchurScale y +
            8 * Real.log 4 * tunedSchurScale y +
            8 * tunedSchurScale y := by
        have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        have hmainEq :
            (8 * Real.log 4 / Real.log y) * y ^ (1 - θ) =
              8 * Real.log 4 * tunedSchurScale y := by
          rw [← hmainScale]
          ring
        rw [hmainEq]
        gcongr
      _ ≤ (8 * Real.log 4 + 12) * tunedSchurScale y := by
        have hscaleNonneg : 0 ≤ tunedSchurScale y := by
          rw [← hscalePow]
          exact Real.rpow_nonneg hypos.le _
        nlinarith
  have hthetaIntegral :
      θ * (∫ t in Set.Ioc (2 : ℝ) y,
          t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊) ≤
        (8 * Real.log 4 + 12) * tunedSchurScale y := by
    have hmul := mul_le_mul_of_nonneg_left hIntegral hθnonneg
    have hthetaR : θ * R ≤ R := by
      exact mul_le_of_le_one_left hRnonneg hθone
    exact hmul.trans (hthetaR.trans hRscale)
  rw [outgoingPrimePowerSum_eq_abel (by omega : 2 ≤ Y) θ]
  change y ^ (-θ) * Nat.primeCounting Y +
      θ * (∫ t in Set.Ioc (2 : ℝ) y,
        t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊) ≤ _
  calc
    _ ≤ (4 * Real.log 4 + 1) * tunedSchurScale y +
        (8 * Real.log 4 + 12) * tunedSchurScale y :=
      add_le_add hendpoint hthetaIntegral
    _ = (12 * Real.log 4 + 13) * tunedSchurScale y := by ring

/-- Eventual threshold form of `outgoingPrimePowerSum_le_tuned`. -/
theorem eventually_outgoingPrimePowerSum_le_tuned :
    ∀ᶠ Y : ℕ in atTop,
      outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) ≤
        (12 * Real.log 4 + 13) * tunedSchurScale (Y : ℝ) := by
  have hY : ∀ᶠ Y : ℕ in atTop, 4 ≤ Y := eventually_atTop.2 ⟨4, fun _ h ↦ h⟩
  have hlogY : ∀ᶠ Y : ℕ in atTop, 1 < Real.log (Y : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop 1)
  filter_upwards [hY, hlogY, eventually_tunedSchurExponent_mem]
    with Y hY hlogY hθmem
  exact outgoingPrimePowerSum_le_tuned hY hlogY hθmem

/-- The elementary logarithmic comparison needed to absorb the incoming
divisor count holds eventually on natural cutoffs. -/
theorem eventually_log_rpow_three_halves_le_quarter :
    ∀ᶠ Y : ℕ in atTop,
      Real.log (Y : ℝ) ^ (3 / 2 : ℝ) ≤ (Y : ℝ) ^ (1 / 4 : ℝ) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).bound
      (c := 1) one_pos
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_atTop.2 ⟨1, fun _ h ↦ h⟩] with Y hY hYone
  have hlog : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hYone)
  have hlogpow : 0 ≤ Real.log (Y : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hlog _
  simpa [Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg hlogpow,
    Real.norm_rpow_of_nonneg (Nat.cast_nonneg Y)] using hY

/-- A pointwise growth hypothesis converts the logarithmic divisor factor to
the tuned Schur scale. -/
theorem log_mul_quarter_rpow_le_tunedSchurScale
    {Y : ℝ} (hY : 1 < Y) (hlogGrowth :
      Real.log Y ^ (3 / 2 : ℝ) ≤ Y ^ (1 / 4 : ℝ)) :
    Real.log Y * Y ^ (1 / 4 : ℝ) ≤ tunedSchurScale Y := by
  have hYpos : 0 < Y := zero_lt_one.trans hY
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hsqrtlog : 0 < √(Real.log Y) := Real.sqrt_pos.2 hlog
  rw [tunedSchurScale, le_div_iff₀ hsqrtlog]
  calc
    Real.log Y * Y ^ (1 / 4 : ℝ) * √(Real.log Y) =
        Real.log Y ^ (3 / 2 : ℝ) * Y ^ (1 / 4 : ℝ) := by
      calc
        Real.log Y * Y ^ (1 / 4 : ℝ) * √(Real.log Y) =
            (Real.log Y * √(Real.log Y)) * Y ^ (1 / 4 : ℝ) := by ring
        _ = Real.log Y ^ (3 / 2 : ℝ) * Y ^ (1 / 4 : ℝ) := by
          congr 1
          rw [Real.sqrt_eq_rpow]
          calc
            Real.log Y * Real.log Y ^ (1 / 2 : ℝ) =
                Real.log Y ^ (1 : ℝ) * Real.log Y ^ (1 / 2 : ℝ) := by
              rw [Real.rpow_one]
            _ = Real.log Y ^ (3 / 2 : ℝ) := by
              rw [← Real.rpow_add hlog]
              norm_num
    _ ≤ Y ^ (1 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) := by
      gcongr
    _ = √Y := by
      rw [← Real.rpow_add hYpos, Real.sqrt_eq_rpow]
      norm_num

/-- The elementary incoming-divisor majorant is eventually bounded by an
absolute multiple of the tuned Schur scale. -/
theorem incomingPrimeDivisorMajorant_le_tuned
    {Y : ℕ} (hY : 1 < (Y : ℝ))
    (hlogY : 1 < Real.log (Y : ℝ))
    (hlogGrowth : Real.log (Y : ℝ) ^ (3 / 2 : ℝ) ≤
      (Y : ℝ) ^ (1 / 4 : ℝ)) :
    (Nat.log 2 (Y ^ 2) : ℝ) *
          (√(Y : ℝ)) ^ tunedSchurExponent (Y : ℝ) +
        3 * (Y : ℝ) ^ tunedSchurExponent (Y : ℝ) ≤
      (2 / Real.log 2 + 3) * tunedSchurScale (Y : ℝ) := by
  let y : ℝ := Y
  let θ : ℝ := tunedSchurExponent y
  have hypos : 0 < y := zero_lt_one.trans hY
  have hyone : 1 ≤ y := hY.le
  have hlogy : 0 < Real.log y := Real.log_pos hY
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hθle : θ ≤ 1 / 2 := by
    exact (tunedSchurExponent_lt_half hlogY).le
  have hsqrtPower : (√y) ^ θ ≤ y ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hypos)]
    apply Real.rpow_le_rpow_of_exponent_le hyone
    nlinarith
  have hnatlog : (Nat.log 2 (Y ^ 2) : ℝ) ≤ 2 * Real.log y / Real.log 2 := by
    calc
      (Nat.log 2 (Y ^ 2) : ℝ) ≤ Real.logb 2 (Y ^ 2) :=
        by
          convert Real.natLog_le_logb (Y ^ 2) 2 using 1
          norm_num
      _ = 2 * Real.logb 2 Y := by
        simpa [y] using Real.logb_pow (2 : ℝ) (Y : ℝ) 2
      _ = 2 * Real.log y / Real.log 2 := by
        simp [Real.logb, y]
        ring
  have hfirst :
      (Nat.log 2 (Y ^ 2) : ℝ) * (√y) ^ θ ≤
        (2 / Real.log 2) * tunedSchurScale y := by
    calc
      (Nat.log 2 (Y ^ 2) : ℝ) * (√y) ^ θ ≤
          (2 * Real.log y / Real.log 2) * y ^ (1 / 4 : ℝ) := by
        gcongr
      _ = (2 / Real.log 2) *
          (Real.log y * y ^ (1 / 4 : ℝ)) := by ring
      _ ≤ (2 / Real.log 2) * tunedSchurScale y := by
        gcongr
        exact log_mul_quarter_rpow_le_tunedSchurScale hY hlogGrowth
  have hsecond :
      3 * y ^ θ = 3 * tunedSchurScale y := by
    change 3 * y ^ tunedSchurExponent y = 3 * tunedSchurScale y
    rw [rpow_tunedSchurExponent_eq_scale hypos hlogY]
  change (Nat.log 2 (Y ^ 2) : ℝ) * (√y) ^ θ + 3 * y ^ θ ≤ _
  rw [hsecond]
  nlinarith

/-- Eventual, threshold-form version of
`incomingPrimeDivisorMajorant_le_tuned`. -/
theorem eventually_incomingPrimeDivisorMajorant_le_tuned :
    ∀ᶠ Y : ℕ in atTop,
      (Nat.log 2 (Y ^ 2) : ℝ) *
            (√(Y : ℝ)) ^ tunedSchurExponent (Y : ℝ) +
          3 * (Y : ℝ) ^ tunedSchurExponent (Y : ℝ) ≤
        (2 / Real.log 2 + 3) * tunedSchurScale (Y : ℝ) := by
  have hY : ∀ᶠ Y : ℕ in atTop, 1 < (Y : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop 1)
  have hlogY : ∀ᶠ Y : ℕ in atTop, 1 < Real.log (Y : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop 1)
  filter_upwards [hY, hlogY, eventually_log_rpow_three_halves_le_quarter]
    with Y hY hlogY hgrowth
  exact incomingPrimeDivisorMajorant_le_tuned hY hlogY hgrowth

/-- The complete explicit weighted-row majorant is eventually at the tuned
Schur scale. -/
theorem eventually_elementarySmallPrimeRowBound_le_tuned :
    ∀ᶠ Y : ℕ in atTop,
      elementarySmallPrimeRowBound Y ≤
        (12 * Real.log 4 + 2 / Real.log 2 + 16) *
          tunedSchurScale (Y : ℝ) := by
  filter_upwards [eventually_outgoingPrimePowerSum_le_tuned,
    eventually_incomingPrimeDivisorMajorant_le_tuned]
    with Y hout hin
  rw [elementarySmallPrimeRowBound]
  calc
    outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) +
          (Nat.log 2 (Y ^ 2) : ℝ) *
              (√(Y : ℝ)) ^ tunedSchurExponent (Y : ℝ) +
            3 * (Y : ℝ) ^ tunedSchurExponent (Y : ℝ) =
        outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) +
          ((Nat.log 2 (Y ^ 2) : ℝ) *
              (√(Y : ℝ)) ^ tunedSchurExponent (Y : ℝ) +
            3 * (Y : ℝ) ^ tunedSchurExponent (Y : ℝ)) := by ring
    _ ≤
        (12 * Real.log 4 + 13) * tunedSchurScale (Y : ℝ) +
          (2 / Real.log 2 + 3) * tunedSchurScale (Y : ℝ) :=
      add_le_add hout hin
    _ = (12 * Real.log 4 + 2 / Real.log 2 + 16) *
          tunedSchurScale (Y : ℝ) := by ring

/-- Final Stage 6A operator theorem: below the square cutoff, the residual
small-prime adjacency has the sharp elementary tuned-scale norm bound,
uniformly in the deleted-prime set and ambient cutoff. -/
theorem eventually_smallPrimeGraph_l2_opNorm_le_tuned :
    ∀ᶠ Y : ℕ in atTop, ∀ (S : Finset ℕ) (X : ℕ), X ≤ Y ^ 2 →
      ‖(smallPrimeGraph S X Y).adjMatrix ℝ‖ ≤
        (12 * Real.log 4 + 2 / Real.log 2 + 16) *
          tunedSchurScale (Y : ℝ) := by
  have hlogY : ∀ᶠ Y : ℕ in atTop, 0 < Real.log (Y : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hlogY, eventually_elementarySmallPrimeRowBound_le_tuned]
    with Y hlogY hrow
  intro S X hXY
  exact (smallPrimeGraph_l2_opNorm_le_elementaryBound hXY hlogY).trans hrow

end

end PrimeStar
