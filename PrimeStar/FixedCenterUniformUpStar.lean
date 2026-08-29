import PrimeStar.FixedCenterUpStarEvaluation

/-!
# Uniform fixed-centre up-star comparison

This module supplies the head--tail estimate missing from the pointwise
fixed-label degree-ratio limits.  The centre and deletion set are fixed while
the prime label ranges through the square-root window.
-/

namespace PrimeStar

open Filter Topology Asymptotics
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2000000

/-- A convenient exact form of the elementary perturbation estimate for a
quotient.  It is used with `N / D` the actual degree ratio and `m / M` its PNT
main-term model. -/
theorem abs_div_sub_div_le
    {N D m M eN eD : ℝ} (hD : 0 < D) (hM : 0 < M)
    (heN : |N - m| ≤ eN) (heD : |D - M| ≤ eD) :
    |N / D - m / M| ≤ eN / D + |m / M| * eD / D := by
  have hD0 : D ≠ 0 := hD.ne'
  have hM0 : M ≠ 0 := hM.ne'
  have hid : N / D - m / M =
      (N - m) / D - (m / M) * ((D - M) / D) := by
    field_simp [hD0, hM0]
    ring
  rw [hid]
  calc
    |(N - m) / D - (m / M) * ((D - M) / D)| ≤
        |(N - m) / D| + |(m / M) * ((D - M) / D)| := abs_sub _ _
    _ = |N - m| / D + |m / M| * (|D - M| / D) := by
      rw [abs_div, abs_of_pos hD, abs_mul, abs_div, abs_of_pos hM,
        abs_div, abs_of_pos hD]
    _ ≤ eN / D + |m / M| * (eD / D) := by
      gcongr
    _ = eN / D + |m / M| * eD / D := by ring

/-- For a fixed centre, the square-root endpoint eventually lies between one
third and two thirds of the logarithmic centre scale. -/
theorem eventually_fixedCenter_logSqrt_between
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      fixedCenterLogScale c X / 3 ≤ Real.log (Nat.sqrt X : ℝ) ∧
        Real.log (Nat.sqrt X : ℝ) ≤ 2 * fixedCenterLogScale c X / 3 := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcTerm : Tendsto
      (fun X : ℕ ↦ Real.log (c : ℝ) / Real.log (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogTop
  have hscale : Tendsto
      (fun X : ℕ ↦ fixedCenterLogScale c X / Real.log (X : ℝ))
      atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := hone.sub hcTerm
    norm_num at h
    refine h.congr' ?_
    filter_upwards [hlogTop.eventually_ne_atTop 0] with X hX
    change 1 - Real.log (c : ℝ) / Real.log (X : ℝ) =
      fixedCenterLogScale c X / Real.log (X : ℝ)
    rw [fixedCenterLogScale]
    field_simp [hX]
  have hratio := log_natSqrt_div_log_tendsto_half.div hscale
    (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at hratio
  have hratio' : Tendsto
      (fun X : ℕ ↦ Real.log (Nat.sqrt X : ℝ) /
        fixedCenterLogScale c X) atTop (𝓝 (1 / 2 : ℝ)) := by
    apply hratio.congr'
    filter_upwards [hlogTop.eventually_ne_atTop 0,
      hscale.eventually (isOpen_ne.mem_nhds (by norm_num : (1 : ℝ) ≠ 0))] with
        X hlogX hscaleX
    have hL : fixedCenterLogScale c X ≠ 0 := by
      intro hzero
      have : fixedCenterLogScale c X / Real.log (X : ℝ) = 0 := by simp [hzero]
      exact hscaleX (this.trans (by norm_num))
    change (Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ)) /
        (fixedCenterLogScale c X / Real.log (X : ℝ)) =
      Real.log (Nat.sqrt X : ℝ) / fixedCenterLogScale c X
    field_simp [hlogX, hL]
  filter_upwards [hratio'.eventually
      (isOpen_Ioo.mem_nhds (show (1 / 2 : ℝ) ∈ Set.Ioo (1 / 3) (2 / 3) by norm_num)),
    (fixedCenterLogScale_tendsto_atTop (c := c)).eventually_gt_atTop 0] with X hX hL
  constructor
  · simpa [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hL).mp hX.1.le
  · have h := (div_le_iff₀ hL).mp hX.2.le
    nlinarith

/-- The square-root endpoint is eventually positive and dominates every
fixed centre. -/
theorem eventually_fixedCenter_le_natSqrt {c : ℕ} :
    ∀ᶠ X : ℕ in atTop, c ≤ Nat.sqrt X := by
  filter_upwards [eventually_ge_atTop (c ^ 2)] with X hX
  exact Nat.le_sqrt'.2 hX

/-- The fixed-centre logarithmic scale is eventually comparable with
`log X`.  The upper bound is exact once `c ≥ 1`; only the lower bound is
asymptotic. -/
theorem eventually_fixedCenter_logScale_between_log
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) / 2 ≤ fixedCenterLogScale c X ∧
        fixedCenterLogScale c X ≤ Real.log (X : ℝ) := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcLogNonneg : 0 ≤ Real.log (c : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hc)
  filter_upwards [hlogTop.eventually_ge_atTop (2 * Real.log (c : ℝ))] with X hX
  constructor
  · rw [fixedCenterLogScale]
    linarith
  · rw [fixedCenterLogScale]
    linarith

/-- Uniform PNT comparison of the actual up-star ratio with the moving main
model.  The deliberately generous constant is immaterial; the important
point is the summable shape `1 / (q log X) + c / sqrt X`, uniform through the
growing square-root prime window. -/
theorem exists_fixedCenterActualUpRatio_sub_model_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℕ in atTop,
      ∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
        |fixedCenterActualUpRatio S c X q -
            fixedCenterUpRatioModel c q X| ≤
          K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (c : ℝ) / (Nat.sqrt X : ℝ)) := by
  obtain ⟨C, hC, hPNT⟩ := exists_realPrimeCounting_error_bound
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hPNT
  have hPi := eventually_allowedPrimeCount_le
    (S := (∅ : Finset ℕ)) (ε := 1) zero_lt_one
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 hPi
  let B : ℝ := Real.log 4 + 1
  let K : ℝ := 200 * (C + B + 1) * (c + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by
    dsimp [K]
    have hcR : (0 : ℝ) < c + 1 := by positivity
    positivity
  refine ⟨K, hK, ?_⟩
  have hsqrtCastTop : Tendsto (fun X : ℕ ↦ (Nat.sqrt X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop
  filter_upwards [
      hsqrtCastTop.eventually_ge_atTop (max (max x₀ x₁) (Real.exp 1)),
      eventually_finset_le_nat_sqrt S,
      eventually_fixedCenterArithmeticDegree_ge_half_main S hS hc,
      eventually_fixedCenter_logSqrt_between hc,
      eventually_fixedCenter_logScale_between_log hc,
      eventually_fixedCenter_le_natSqrt (c := c),
      eventually_ge_atTop 4] with X hYlarge hSY hDlower hlogY hlogL hcY hX
  intro q hq
  have hqMem := (Finset.mem_filter.mp hq).1
  have hqPrime : q.Prime := (Nat.mem_primesLE.mp hqMem).2
  have hqLeY : q ≤ Nat.sqrt X := (Nat.mem_primesLE.mp hqMem).1
  have hqPos : 0 < q := hqPrime.pos
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPos
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hYR : (0 : ℝ) < Nat.sqrt X := by
    exact (Real.exp_pos 1).trans_le ((le_max_right _ _).trans hYlarge)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogYpos : 0 < Real.log (Nat.sqrt X : ℝ) := by
    have hexp : Real.exp 1 ≤ (Nat.sqrt X : ℝ) :=
      le_trans (le_max_right _ _) hYlarge
    have : (1 : ℝ) < Nat.sqrt X :=
      (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hexp
    exact Real.log_pos this
  have hLpos : 0 < fixedCenterLogScale c X :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.log (X : ℝ) / 2) hlogL.1
  have hlogq : Real.log (q : ℝ) ≤ Real.log (Nat.sqrt X : ℝ) :=
    Real.log_le_log hqR (by exact_mod_cast hqLeY)
  have hgapThird : fixedCenterLogScale c X / 3 ≤
      fixedCenterLogScale c X - Real.log (q : ℝ) := by
    linarith [hlogY.2, hlogq]
  have hgap : Real.log (q : ℝ) < fixedCenterLogScale c X := by
    linarith
  have hmodelPos : 0 ≤ fixedCenterUpRatioModel c q X := by
    unfold fixedCenterUpRatioModel
    positivity
  have hmodelLe : fixedCenterUpRatioModel c q X ≤ 3 / (q : ℝ) := by
    unfold fixedCenterUpRatioModel
    rw [div_le_iff₀ (mul_pos hqR (lt_of_lt_of_le (by positivity) hgapThird))]
    field_simp [hqR.ne']
    nlinarith [hgapThird]
  by_cases hcut : c * q ≤ Nat.sqrt X
  · let y : ℝ := Nat.sqrt X
    let t : ℝ := (X : ℝ) / (c : ℝ)
    let tq : ℝ := (X : ℝ) / ((c : ℝ) * (q : ℝ))
    let L : ℝ := fixedCenterLogScale c X
    let D : ℝ := fixedCenterArithmeticDegree S c X
    let N : ℝ := fixedCenterArithmeticDegree S (c * q) X
    let M : ℝ := pntMainReal t
    let m : ℝ := pntMainReal tq
    have hcqPos : 0 < c * q := Nat.mul_pos hc hqPos
    have hySq : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    have hcqY : (c * q) * Nat.sqrt X ≤ X :=
      (Nat.mul_le_mul_right (Nat.sqrt X) hcut).trans hySq
    have hcY' : c * Nat.sqrt X ≤ X := by
      have hcLe : c ≤ c * q := Nat.le_mul_of_pos_right c hqPos
      exact (Nat.mul_le_mul_right (Nat.sqrt X) hcLe).trans hcqY
    have hYqNat : Nat.sqrt X ≤ X / (c * q) :=
      (Nat.le_div_iff_mul_le hcqPos).2 (by simpa [mul_comm] using hcqY)
    have hYcNat : Nat.sqrt X ≤ X / c :=
      (Nat.le_div_iff_mul_le hc).2 (by simpa [mul_comm] using hcY')
    have hYtq : y ≤ tq := by
      dsimp [y, tq]
      rw [le_div_iff₀ (mul_pos hcR hqR)]
      exact_mod_cast (show Nat.sqrt X * (c * q) ≤ X by simpa [mul_comm] using hcqY)
    have hYt : y ≤ t := by
      dsimp [y, t]
      rw [le_div_iff₀ hcR]
      exact_mod_cast (show Nat.sqrt X * c ≤ X by simpa [mul_comm] using hcY')
    have hx₀Y : x₀ ≤ y :=
      (le_max_left x₀ x₁).trans (le_max_left (max x₀ x₁) (Real.exp 1)) |>.trans hYlarge
    have hx₁Y : x₁ ≤ y :=
      (le_max_right x₀ x₁).trans (le_max_left (max x₀ x₁) (Real.exp 1)) |>.trans hYlarge
    have hPNTy := hx₀ y hx₀Y
    have hPNTt := hx₀ t (hx₀Y.trans hYt)
    have hPNTtq := hx₀ tq (hx₀Y.trans hYtq)
    have hPiY := hx₁ y hx₁Y
    have hfloorT : ⌊t⌋₊ = X / c := by
      dsimp [t]
      exact natFloor_real_div_eq_div X c
    have hfloorTq : ⌊tq⌋₊ = X / (c * q) := by
      dsimp [tq]
      simpa only [Nat.cast_mul] using natFloor_real_div_eq_div X (c * q)
    have hfloorY : ⌊y⌋₊ = Nat.sqrt X := by simp [y]
    rw [hfloorT] at hPNTt
    rw [hfloorTq] at hPNTtq
    rw [hfloorY] at hPNTy hPiY
    have hDEq := fixedCenterArithmeticDegree_eq_primeDegree_of_endpoints
      S hS hSY hYcNat
    have hNEq := fixedCenterArithmeticDegree_eq_primeDegree_of_endpoints
      S hS hSY hYqNat
    have hlogt : Real.log t = L := by
      dsimp [t, L]
      exact log_div_eq_fixedCenterLogScale hc (show 0 < X by omega)
    have hlogtq : Real.log tq = L - Real.log (q : ℝ) := by
      dsimp [tq, L]
      have hX0 : (X : ℝ) ≠ 0 := hXR.ne'
      have hc0 : (c : ℝ) ≠ 0 := hcR.ne'
      have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
      rw [Real.log_div hX0 (mul_ne_zero hc0 hq0), Real.log_mul hc0 hq0,
        fixedCenterLogScale]
      ring
    have hMpos : 0 < M := by
      dsimp [M, pntMainReal]
      rw [hlogt]
      positivity
    have hDpos : 0 < D := by
      dsimp [D]
      have hmainPos : 0 < (c : ℝ)⁻¹ *
          ((X : ℝ) / Real.log (X : ℝ)) := by positivity
      linarith [hDlower]
    have hPiYbound : (Nat.primeCounting (Nat.sqrt X) : ℝ) ≤
        B * y / Real.log y := by
      simpa [B, y] using hPiY
    have hErrT : |(Nat.primeCounting (X / c) : ℝ) - M| ≤
        C * t / L ^ 2 := by simpa [M, pntMainReal, hlogt] using hPNTt
    have hErrTq : |(Nat.primeCounting (X / (c * q)) : ℝ) - m| ≤
        9 * C * tq / L ^ 2 := by
      have hlogtqPos : 0 < Real.log tq := by rw [hlogtq]; linarith
      have hdenSq : (L / 3) ^ 2 ≤ Real.log tq ^ 2 := by
        rw [hlogtq]
        nlinarith [hgapThird]
      have htqNonneg : 0 ≤ tq := le_trans (by positivity) hYtq
      have hraw := hPNTtq
      rw [show Real.log tq = L - Real.log (q : ℝ) from hlogtq] at hraw
      calc
        |(Nat.primeCounting (X / (c * q)) : ℝ) - m| ≤
            C * tq / Real.log tq ^ 2 := by simpa [m, pntMainReal] using hPNTtq
        _ ≤ 9 * C * tq / L ^ 2 := by
          have hL2 : 0 < L ^ 2 := sq_pos_of_pos hLpos
          have hlog2 : 0 < Real.log tq ^ 2 := sq_pos_of_pos hlogtqPos
          rw [div_le_div_iff₀ hlog2 hL2]
          have hscale : L ^ 2 ≤ 9 * Real.log tq ^ 2 := by
            nlinarith [hdenSq]
          calc
            C * tq * L ^ 2 ≤ C * tq * (9 * Real.log tq ^ 2) := by
              exact mul_le_mul_of_nonneg_left hscale (mul_nonneg hC.le htqNonneg)
            _ = 9 * C * tq * Real.log tq ^ 2 := by ring
    have hEN : |N - m| ≤ 9 * C * tq / L ^ 2 + B * y / Real.log y := by
      rw [show N = (Nat.primeCounting (X / (c * q)) : ℝ) -
          (Nat.primeCounting (Nat.sqrt X) : ℝ) by simpa [N] using hNEq]
      calc
        |((Nat.primeCounting (X / (c * q)) : ℝ) -
              (Nat.primeCounting (Nat.sqrt X) : ℝ)) - m| =
            |((Nat.primeCounting (X / (c * q)) : ℝ) - m) -
              (Nat.primeCounting (Nat.sqrt X) : ℝ)| := by ring
        _ ≤
            |(Nat.primeCounting (X / (c * q)) : ℝ) - m| +
              |(Nat.primeCounting (Nat.sqrt X) : ℝ)| := abs_sub _ _
        _ ≤ 9 * C * tq / L ^ 2 + B * y / Real.log y := by
          rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.primeCounting (Nat.sqrt X) : ℝ))]
          exact add_le_add hErrTq hPiYbound
    have hED : |D - M| ≤ C * t / L ^ 2 + B * y / Real.log y := by
      rw [show D = (Nat.primeCounting (X / c) : ℝ) -
          (Nat.primeCounting (Nat.sqrt X) : ℝ) by simpa [D] using hDEq]
      calc
        |((Nat.primeCounting (X / c) : ℝ) -
              (Nat.primeCounting (Nat.sqrt X) : ℝ)) - M| =
            |((Nat.primeCounting (X / c) : ℝ) - M) -
              (Nat.primeCounting (Nat.sqrt X) : ℝ)| := by ring
        _ ≤
            |(Nat.primeCounting (X / c) : ℝ) - M| +
              |(Nat.primeCounting (Nat.sqrt X) : ℝ)| := abs_sub _ _
        _ ≤ C * t / L ^ 2 + B * y / Real.log y := by
          rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.primeCounting (Nat.sqrt X) : ℝ))]
          exact add_le_add hErrT hPiYbound
    have hratio := abs_div_sub_div_le hDpos hMpos hEN hED
    have hmodelEq : m / M = fixedCenterUpRatioModel c q X := by
      dsimp [m, M, tq, t]
      exact pntMainReal_ratio_eq_upRatioModel hc hqPos (show 0 < X by omega) hgap
    rw [hmodelEq, abs_of_nonneg hmodelPos] at hratio
    rw [fixedCenterActualUpRatio, if_pos hcut]
    change |N / D - fixedCenterUpRatioModel c q X| ≤ _
    -- The remaining estimates use `D ≥ X/(2c log X)`, the logarithmic
    -- comparisons above, and `Y² ≤ X`.
    have hDcoarse : (X : ℝ) /
        (2 * (c : ℝ) * Real.log (X : ℝ)) ≤ D := by
      dsimp [D]
      have hc0 : (c : ℝ) ≠ 0 := hcR.ne'
      have : (1 / 2 : ℝ) * ((c : ℝ)⁻¹ *
          ((X : ℝ) / Real.log (X : ℝ))) =
          (X : ℝ) / (2 * (c : ℝ) * Real.log (X : ℝ)) := by
        field_simp [hc0, hlogX.ne']
      exact this ▸ hDlower
    have hySqR : y ^ 2 ≤ (X : ℝ) := by
      dsimp [y]
      simpa [pow_two] using (show
        (Nat.sqrt X : ℝ) * (Nat.sqrt X : ℝ) ≤ (X : ℝ) by exact_mod_cast hySq)
    have htEq : t = (X : ℝ) / (c : ℝ) := rfl
    have htqEq : tq = t / (q : ℝ) := by
      dsimp [tq, t]
      field_simp
    have hInvD : 1 / D ≤
        2 * (c : ℝ) * Real.log (X : ℝ) / (X : ℝ) := by
      have hcoarsePos : 0 < (X : ℝ) /
          (2 * (c : ℝ) * Real.log (X : ℝ)) := by positivity
      have hinv := one_div_le_one_div_of_le hcoarsePos hDcoarse
      calc
        1 / D ≤ 1 / ((X : ℝ) /
            (2 * (c : ℝ) * Real.log (X : ℝ))) := hinv
        _ = 2 * (c : ℝ) * Real.log (X : ℝ) / (X : ℝ) := by
          field_simp
    have hLlower : Real.log (X : ℝ) / 2 ≤ L := by simpa [L] using hlogL.1
    have hLupper : L ≤ Real.log (X : ℝ) := by simpa [L] using hlogL.2
    have hlogYlower : L / 3 ≤ Real.log y := by simpa [L, y] using hlogY.1
    have hboundary : (B * y / Real.log y) / D ≤
        12 * B * (c : ℝ) / y := by
      have hbyNonneg : 0 ≤ B * y / Real.log y := by positivity
      calc
        (B * y / Real.log y) / D =
            (B * y / Real.log y) * (1 / D) := by ring
        _ ≤ (B * y / Real.log y) *
            (2 * (c : ℝ) * Real.log (X : ℝ) / (X : ℝ)) := by gcongr
        _ ≤ 12 * B * (c : ℝ) * y / (X : ℝ) := by
          have hlogRatio : Real.log (X : ℝ) ≤ 6 * Real.log y := by
            linarith [hLlower, hlogYlower]
          have hratioLog : Real.log (X : ℝ) / Real.log y ≤ 6 :=
            (div_le_iff₀ hlogYpos).2 (by simpa using hlogRatio)
          calc
            (B * y / Real.log y) *
                (2 * (c : ℝ) * Real.log (X : ℝ) / (X : ℝ)) =
              (2 * B * (c : ℝ) * y / (X : ℝ)) *
                (Real.log (X : ℝ) / Real.log y) := by ring
            _ ≤ (2 * B * (c : ℝ) * y / (X : ℝ)) * 6 := by
              gcongr
            _ = 12 * B * (c : ℝ) * y / (X : ℝ) := by ring
        _ ≤ 12 * B * (c : ℝ) / y := by
          rw [div_le_div_iff₀ hXR hYR]
          convert mul_le_mul_of_nonneg_left hySqR
            (by positivity : 0 ≤ 12 * B * (c : ℝ)) using 1 <;> ring
    have hPntQ : (9 * C * tq / L ^ 2) / D ≤
        72 * C / ((q : ℝ) * Real.log (X : ℝ)) := by
      calc
        (9 * C * tq / L ^ 2) / D =
            (9 * C * tq / L ^ 2) * (1 / D) := by ring
        _ ≤ (9 * C * tq / L ^ 2) *
            (2 * (c : ℝ) * Real.log (X : ℝ) / (X : ℝ)) := by
              gcongr <;> positivity
        _ = 18 * C * Real.log (X : ℝ) /
            ((q : ℝ) * L ^ 2) := by
              rw [htqEq, htEq]
              field_simp
              ring
        _ ≤ 72 * C / ((q : ℝ) * Real.log (X : ℝ)) := by
          have hlogLe : Real.log (X : ℝ) ≤ 2 * L := by linarith
          have hLsq : Real.log (X : ℝ) ^ 2 ≤ 4 * L ^ 2 := by
            have hsquare : Real.log (X : ℝ) ^ 2 ≤ (2 * L) ^ 2 :=
              (sq_le_sq₀ hlogX.le (mul_nonneg (by norm_num) hLpos.le)).2 hlogLe
            convert hsquare using 1 <;> ring
          rw [div_le_div_iff₀ (mul_pos hqR (sq_pos_of_pos hLpos))
            (mul_pos hqR hlogX)]
          convert mul_le_mul_of_nonneg_left hLsq
            (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 18) hC.le) hqR.le)
            using 1 <;> ring
    have hPnt0 : (C * t / L ^ 2) / D ≤
        8 * C / Real.log (X : ℝ) := by
      calc
        (C * t / L ^ 2) / D = (C * t / L ^ 2) * (1 / D) := by ring
        _ ≤ (C * t / L ^ 2) *
            (2 * (c : ℝ) * Real.log (X : ℝ) / (X : ℝ)) := by
              gcongr <;> positivity
        _ = 2 * C * Real.log (X : ℝ) / L ^ 2 := by
              rw [htEq]
              field_simp
        _ ≤ 8 * C / Real.log (X : ℝ) := by
          have hlogLe : Real.log (X : ℝ) ≤ 2 * L := by linarith
          have hLsq : Real.log (X : ℝ) ^ 2 ≤ 4 * L ^ 2 := by
            have hsquare : Real.log (X : ℝ) ^ 2 ≤ (2 * L) ^ 2 :=
              (sq_le_sq₀ hlogX.le (mul_nonneg (by norm_num) hLpos.le)).2 hlogLe
            convert hsquare using 1 <;> ring
          rw [div_le_div_iff₀ (sq_pos_of_pos hLpos) hlogX]
          convert mul_le_mul_of_nonneg_left hLsq
            (mul_nonneg (by positivity : (0 : ℝ) ≤ 2) hC.le) using 1 <;> ring
    have hnumQ :
        (9 * C * tq / L ^ 2 + B * y / Real.log y) / D ≤
          72 * C / ((q : ℝ) * Real.log (X : ℝ)) +
            12 * B * (c : ℝ) / y := by
      rw [add_div]
      exact add_le_add hPntQ hboundary
    have hnum0 :
        (C * t / L ^ 2 + B * y / Real.log y) / D ≤
          8 * C / Real.log (X : ℝ) + 12 * B * (c : ℝ) / y := by
      rw [add_div]
      exact add_le_add hPnt0 hboundary
    have hmodelTerm :
        fixedCenterUpRatioModel c q X *
              (C * t / L ^ 2 + B * y / Real.log y) / D ≤
          (3 / (q : ℝ)) *
            (8 * C / Real.log (X : ℝ) + 12 * B * (c : ℝ) / y) := by
      calc
        fixedCenterUpRatioModel c q X *
              (C * t / L ^ 2 + B * y / Real.log y) / D =
            fixedCenterUpRatioModel c q X *
              ((C * t / L ^ 2 + B * y / Real.log y) / D) := by ring
        _ ≤ (3 / (q : ℝ)) *
            (8 * C / Real.log (X : ℝ) + 12 * B * (c : ℝ) / y) :=
          mul_le_mul hmodelLe hnum0 (by positivity) (by positivity)
    calc
      |N / D - fixedCenterUpRatioModel c q X| ≤
          (9 * C * tq / L ^ 2 + B * y / Real.log y) / D +
            fixedCenterUpRatioModel c q X *
              (C * t / L ^ 2 + B * y / Real.log y) / D := hratio
      _ ≤ (72 * C / ((q : ℝ) * Real.log (X : ℝ)) +
            12 * B * (c : ℝ) / y) +
          (3 / (q : ℝ)) *
            (8 * C / Real.log (X : ℝ) + 12 * B * (c : ℝ) / y) := by
              exact add_le_add hnumQ hmodelTerm
      _ ≤ K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (c : ℝ) / (Nat.sqrt X : ℝ)) := by
          have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqPrime.one_le
          have hqInv : 0 ≤ 1 / (q : ℝ) := by positivity
          have hqInvLe : 1 / (q : ℝ) ≤ 1 := by
            exact (div_le_one hqR).2 hqOne
          have hA : 0 ≤ 1 / ((q : ℝ) * Real.log (X : ℝ)) := by positivity
          have hE : 0 ≤ (c : ℝ) / y := by positivity
          have hfirst :
              72 * C / ((q : ℝ) * Real.log (X : ℝ)) +
                  12 * B * (c : ℝ) / y +
                  (3 / (q : ℝ)) *
                    (8 * C / Real.log (X : ℝ) + 12 * B * (c : ℝ) / y) =
                96 * C * (1 / ((q : ℝ) * Real.log (X : ℝ))) +
                  (12 * B + 36 * B / (q : ℝ)) * ((c : ℝ) / y) := by
            ring
          rw [hfirst]
          have hcoefE : 12 * B + 36 * B / (q : ℝ) ≤ 48 * B := by
            have h36 : 36 * B / (q : ℝ) ≤ 36 * B := by
              calc
                36 * B / (q : ℝ) = (36 * B) * (1 / (q : ℝ)) := by ring
                _ ≤ (36 * B) * 1 :=
                  mul_le_mul_of_nonneg_left hqInvLe
                    (mul_nonneg (by norm_num) hB.le)
                _ = 36 * B := by ring
            linarith
          have hcoeffC : 96 * C ≤ K := by
            have hpre : 96 * C ≤ 200 * (C + B + 1) := by
              calc
                96 * C ≤ 200 * C :=
                  mul_le_mul_of_nonneg_right (by norm_num) hC.le
                _ ≤ 200 * C + 200 * (B + 1) :=
                  le_add_of_nonneg_right (mul_nonneg (by norm_num) (by linarith [hB.le]))
                _ = 200 * (C + B + 1) := by ring
            have hcOne : (1 : ℝ) ≤ (c : ℝ) + 1 := by nlinarith [hcR.le]
            have hmult := mul_le_mul_of_nonneg_left hcOne
              (by positivity : 0 ≤ 200 * (C + B + 1))
            exact hpre.trans (by simpa [K] using hmult)
          have hcoeffB : 48 * B ≤ K := by
            have hpre : 48 * B ≤ 200 * (C + B + 1) := by
              calc
                48 * B ≤ 200 * B :=
                  mul_le_mul_of_nonneg_right (by norm_num) hB.le
                _ ≤ 200 * B + 200 * (C + 1) :=
                  le_add_of_nonneg_right (mul_nonneg (by norm_num) (by linarith [hC.le]))
                _ = 200 * (C + B + 1) := by ring
            have hcOne : (1 : ℝ) ≤ (c : ℝ) + 1 := by nlinarith [hcR.le]
            have hmult := mul_le_mul_of_nonneg_left hcOne
              (by positivity : 0 ≤ 200 * (C + B + 1))
            exact hpre.trans (by simpa [K] using hmult)
          calc
            96 * C * (1 / ((q : ℝ) * Real.log (X : ℝ))) +
                (12 * B + 36 * B / (q : ℝ)) * ((c : ℝ) / y) ≤
                96 * C * (1 / ((q : ℝ) * Real.log (X : ℝ))) +
                  48 * B * ((c : ℝ) / y) := by gcongr
            _ ≤ K * (1 / ((q : ℝ) * Real.log (X : ℝ))) +
                  K * ((c : ℝ) / y) := add_le_add
              (mul_le_mul_of_nonneg_right hcoeffC hA)
              (mul_le_mul_of_nonneg_right hcoeffB hE)
            _ = K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
                (c : ℝ) / (Nat.sqrt X : ℝ)) := by
              dsimp [y]
              ring
  · rw [fixedCenterActualUpRatio, if_neg hcut, zero_sub, abs_neg,
      abs_of_nonneg hmodelPos]
    have hcqGt : Nat.sqrt X < c * q := Nat.lt_of_not_ge hcut
    have hqLower : (Nat.sqrt X : ℝ) < (c : ℝ) * (q : ℝ) := by exact_mod_cast hcqGt
    have hrecip : 3 / (q : ℝ) ≤ 3 * (c : ℝ) / (Nat.sqrt X : ℝ) := by
      rw [div_le_div_iff₀ hqR hYR]
      nlinarith [hcR.le, hqLower]
    calc
      fixedCenterUpRatioModel c q X ≤ 3 / (q : ℝ) := hmodelLe
      _ ≤ 3 * (c : ℝ) / (Nat.sqrt X : ℝ) := hrecip
      _ ≤ K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (c : ℝ) / (Nat.sqrt X : ℝ)) := by
        have h1 : 0 ≤ 1 / ((q : ℝ) * Real.log (X : ℝ)) := by positivity
        have h2 : 0 ≤ (c : ℝ) / (Nat.sqrt X : ℝ) := by positivity
        have hsum : 0 ≤ 1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (c : ℝ) / (Nat.sqrt X : ℝ) := add_nonneg h1 h2
        have hKthree : 3 ≤ K := by
          have hbase : 3 ≤ 200 * (C + B + 1) := by nlinarith [hC.le, hB.le]
          have hcOne : (1 : ℝ) ≤ (c : ℝ) + 1 := by nlinarith [hcR.le]
          have hmult := mul_le_mul_of_nonneg_left hcOne
            (by positivity : 0 ≤ 200 * (C + B + 1))
          exact hbase.trans (by simpa [K] using hmult)
        calc
          3 * (c : ℝ) / (Nat.sqrt X : ℝ) ≤
              3 * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
                (c : ℝ) / (Nat.sqrt X : ℝ)) := by
            have htail : (c : ℝ) / (Nat.sqrt X : ℝ) ≤
                1 / ((q : ℝ) * Real.log (X : ℝ)) +
                  (c : ℝ) / (Nat.sqrt X : ℝ) := le_add_of_nonneg_left h1
            simpa only [mul_div_assoc] using
              (mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 3))
          _ ≤ K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
                (c : ℝ) / (Nat.sqrt X : ℝ)) :=
            mul_le_mul_of_nonneg_right hKthree hsum

/-- The reciprocal-prime mass through the square-root endpoint is negligible
after division by `log X`. -/
theorem allowedPrimeReciprocalSum_natSqrt_div_log_tendsto_zero
    (S : Finset ℕ) :
    Tendsto
      (fun X : ℕ ↦ allowedPrimeReciprocalSum S (Nat.sqrt X) /
        Real.log (X : ℝ)) atTop (𝓝 0) := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hoffset := allowedPrimeReciprocalSum_natSqrt_sub_logLog_tendsto S
  have hoffsetDiv : Tendsto
      (fun X : ℕ ↦
        (allowedPrimeReciprocalSum S (Nat.sqrt X) -
          Real.log (Real.log (X : ℝ))) / Real.log (X : ℝ))
      atTop (𝓝 0) := hoffset.div_atTop hlogTop
  have hloglogDiv : Tendsto
      (fun X : ℕ ↦ Real.log (Real.log (X : ℝ)) /
        Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogTop
  have h := hoffsetDiv.add hloglogDiv
  convert h using 1
  · funext X
    ring
  · norm_num

/-- The number of allowed primes through the square-root endpoint is
`o(sqrt X)`. -/
theorem allowedPrimeCount_natSqrt_div_tendsto_zero (S : Finset ℕ) :
    Tendsto
      (fun X : ℕ ↦ (allowedPrimeCount S (Nat.sqrt X) : ℝ) /
        (Nat.sqrt X : ℝ)) atTop (𝓝 0) := by
  have hsqrtTop : Tendsto (fun X : ℕ ↦ (Nat.sqrt X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop
  have hupper := eventually_allowedPrimeCount_le
    (S := S) (ε := 1) zero_lt_one
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hupper
  have hinvLog : Tendsto
      (fun X : ℕ ↦ (Real.log 4 + 1) /
        Real.log (Nat.sqrt X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hsqrtTop)
  refine squeeze_zero' ?_ ?_ hinvLog
  · filter_upwards with X
    positivity
  filter_upwards [hsqrtTop.eventually_ge_atTop (max x₀ 2)] with X hX
  have hYpos : (0 : ℝ) < Nat.sqrt X :=
    lt_of_lt_of_le (by norm_num) ((le_max_right x₀ 2).trans hX)
  have hcount := hx₀ (Nat.sqrt X : ℝ) ((le_max_left x₀ 2).trans hX)
  simp only [Nat.floor_natCast] at hcount
  rw [div_le_iff₀ hYpos]
  calc
    (allowedPrimeCount S (Nat.sqrt X) : ℝ) ≤
        (Real.log 4 + 1) * (Nat.sqrt X : ℝ) /
          Real.log (Nat.sqrt X : ℝ) := hcount
    _ = ((Real.log 4 + 1) / Real.log (Nat.sqrt X : ℝ)) *
        (Nat.sqrt X : ℝ) := by ring

/-- The summed linear actual-to-model error tends to zero. -/
theorem fixedCenterActualUpLinear_sub_model_tendsto_zero
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    Tendsto
      (fun X : ℕ ↦ fixedCenterActualUpLinear S c X -
        fixedCenterUpLinearModel S c X) atTop (𝓝 0) := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_fixedCenterActualUpRatio_sub_model_bound S hS hc
  let majorant : ℕ → ℝ := fun X ↦
    K * (allowedPrimeReciprocalSum S (Nat.sqrt X) /
        Real.log (X : ℝ) +
      (allowedPrimeCount S (Nat.sqrt X) : ℝ) *
        ((c : ℝ) / (Nat.sqrt X : ℝ)))
  have hmajorant : Tendsto majorant atTop (𝓝 0) := by
    have hrecip := allowedPrimeReciprocalSum_natSqrt_div_log_tendsto_zero S
    have hcount := (allowedPrimeCount_natSqrt_div_tendsto_zero S).mul_const (c : ℝ)
    have hcount' : Tendsto
        (fun X : ℕ ↦ (allowedPrimeCount S (Nat.sqrt X) : ℝ) *
          ((c : ℝ) / (Nat.sqrt X : ℝ))) atTop (𝓝 0) := by
      convert hcount using 1
      · funext X
        ring
      · norm_num
    simpa only [majorant, mul_zero, add_zero] using
      (hrecip.add hcount').const_mul K
  refine squeeze_zero_norm' ?_ hmajorant
  filter_upwards [hratio,
    eventually_ge_atTop 4] with X hratioX hX
  let Q := (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hYpos : (0 : ℝ) < Nat.sqrt X := by
    have : 1 ≤ Nat.sqrt X := Nat.le_sqrt'.2 (by omega : 1 ^ 2 ≤ X)
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
  have hsumAbs :
      ∑ q ∈ Q, |fixedCenterActualUpRatio S c X q -
          fixedCenterUpRatioModel c q X| ≤ majorant X := by
    calc
      ∑ q ∈ Q, |fixedCenterActualUpRatio S c X q -
          fixedCenterUpRatioModel c q X| ≤
        ∑ q ∈ Q, K *
          (1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (c : ℝ) / (Nat.sqrt X : ℝ)) := by
              apply Finset.sum_le_sum
              intro q hq
              exact hratioX q hq
      _ = majorant X := by
        have hrecipSum : (∑ q ∈ Q,
            (1 : ℝ) / ((q : ℝ) * Real.log (X : ℝ))) =
            allowedPrimeReciprocalSum S (Nat.sqrt X) /
              Real.log (X : ℝ) := by
          rw [allowedPrimeReciprocalSum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro q _hq
          rw [one_div, mul_inv_rev, div_eq_mul_inv]
          ring
        have hconstSum : (∑ _q ∈ Q, (c : ℝ) / (Nat.sqrt X : ℝ)) =
            (allowedPrimeCount S (Nat.sqrt X) : ℝ) *
              ((c : ℝ) / (Nat.sqrt X : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp only [Q, allowedPrimeCount]
        rw [show (∑ q ∈ Q, K *
            (1 / ((q : ℝ) * Real.log (X : ℝ)) +
              (c : ℝ) / (Nat.sqrt X : ℝ))) =
            K * ((∑ q ∈ Q, (1 : ℝ) / ((q : ℝ) * Real.log (X : ℝ))) +
              ∑ _q ∈ Q, (c : ℝ) / (Nat.sqrt X : ℝ)) by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]]
        rw [hrecipSum, hconstSum]
  change ‖fixedCenterActualUpLinear S c X -
      fixedCenterUpLinearModel S c X‖ ≤ majorant X
  rw [Real.norm_eq_abs, fixedCenterActualUpLinear, fixedCenterUpLinearModel,
    ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans hsumAbs

/-! ## Nonlinear dominated convergence -/

/-- A fixed actual up-star ratio has the expected reciprocal-prime limit. -/
theorem fixedCenterActualUpRatio_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c q : ℕ} (hc : 0 < c) (hq : 0 < q) :
    Tendsto (fun X : ℕ ↦ fixedCenterActualUpRatio S c X q)
      atTop (𝓝 ((q : ℝ)⁻¹)) := by
  have hraw := fixedCenter_upArithmeticDegreeRatio_tendsto S hS hc hq
  apply hraw.congr'
  filter_upwards [eventually_ge_atTop ((c * q) ^ 2)] with X hX
  have hcut : c * q ≤ Nat.sqrt X := Nat.le_sqrt'.2 hX
  simp [fixedCenterActualUpRatio, hcut]

/-- The actual nonlinear summand, extended by zero outside the current
allowed prime window. -/
def fixedCenterActualUpNonlinearTerm
    (S : Finset ℕ) (c X n : ℕ) : ℝ :=
  if n.Prime ∧ n ∉ S ∧ n ≤ Nat.sqrt X then
    (fixedCenterActualUpRatio S c X n) ^ 2 /
      (1 - fixedCenterActualUpRatio S c X n)
  else 0

theorem fixedCenterActualUpQuadratic_eq_tsum
    (S : Finset ℕ) (c X : ℕ) :
    fixedCenterActualUpQuadratic S c X =
      ∑' n : ℕ, fixedCenterActualUpNonlinearTerm S c X n := by
  let Q := (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S)
  have hsupp : Function.support (fixedCenterActualUpNonlinearTerm S c X) ⊆ Q := by
    intro n hn
    simp only [Function.mem_support] at hn
    by_contra hnQ
    have hnot : ¬(n.Prime ∧ n ∉ S ∧ n ≤ Nat.sqrt X) := by
      intro h
      apply hnQ
      simp [Q, Nat.mem_primesLE, h]
    exact hn (by simp [fixedCenterActualUpNonlinearTerm, hnot])
  rw [fixedCenterActualUpQuadratic, tsum_eq_sum' hsupp]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  have hnPrime : n.Prime := (Nat.mem_primesLE.mp hn'.1).2
  have hnLe : n ≤ Nat.sqrt X := (Nat.mem_primesLE.mp hn'.1).1
  simp [fixedCenterActualUpNonlinearTerm, hnPrime, hn'.2, hnLe]

/-- Pointwise convergence of the actual nonlinear summand to the limiting
prime-supported summand. -/
theorem fixedCenterActualUpNonlinearTerm_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) (n : ℕ) :
    Tendsto (fun X : ℕ ↦ fixedCenterActualUpNonlinearTerm S c X n)
      atTop (𝓝 (nonlinearPrimeTerm S n)) := by
  by_cases hnPrime : n.Prime
  · by_cases hnS : n ∈ S
    · simp [fixedCenterActualUpNonlinearTerm, nonlinearPrimeTerm, hnPrime, hnS]
    · have hnPos := hnPrime.pos
      have hratio := fixedCenterActualUpRatio_tendsto S hS hc hnPos
      have hinvNe : (n : ℝ)⁻¹ ≠ 1 := by
        rw [inv_ne_one]
        exact_mod_cast hnPrime.ne_one
      have hcont : ContinuousAt (fun r : ℝ ↦ r ^ 2 / (1 - r)) (n : ℝ)⁻¹ := by
        exact (continuousAt_id.pow 2).div
          (continuousAt_const.sub continuousAt_id)
          (sub_ne_zero.mpr hinvNe.symm)
      have hlim := hcont.tendsto.comp hratio
      have hvalue : ((n : ℝ)⁻¹) ^ 2 / (1 - (n : ℝ)⁻¹) =
          nonlinearPrimeTerm S n := by
        rw [nonlinearPrimeTerm, if_pos ⟨hnPrime, hnS⟩]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnPos.ne'
        have hn1 : (n : ℝ) ≠ 1 := by exact_mod_cast hnPrime.ne_one
        field_simp [hn0, hn1]
      rw [hvalue] at hlim
      apply hlim.congr'
      filter_upwards [eventually_ge_atTop (n ^ 2)] with X hX
      have hnLe : n ≤ Nat.sqrt X := Nat.le_sqrt'.2 hX
      simp [fixedCenterActualUpNonlinearTerm, hnPrime, hnS, hnLe]
  · simp [fixedCenterActualUpNonlinearTerm, nonlinearPrimeTerm, hnPrime]

/-
/-- The actual nonlinear summands admit an eventually uniform summable
`1/n^2` majorant. -/
theorem exists_fixedCenterActualUpNonlinearTerm_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ Summable (fun n : ℕ ↦ A / (n : ℝ) ^ 2) ∧
      ∀ᶠ X : ℕ in atTop, ∀ n : ℕ,
        ‖fixedCenterActualUpNonlinearTerm S c X n‖ ≤ A / (n : ℝ) ^ 2 := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_fixedCenterActualUpRatio_sub_model_bound S hS hc
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, 4 * (2 * K + 3) < Q :=
    exists_nat_gt (4 * (2 * K + 3))
  let A : ℝ := 4 * (Q : ℝ) ^ 2
  have hQpos : 0 < Q := by
    have : (0 : ℝ) < Q := lt_of_lt_of_le
      (by positivity : (0 : ℝ) < 4 * (2 * K + 3)) hQ.le
    exact_mod_cast this
  have hA : 0 < A := by dsimp [A]; positivity
  have hsum : Summable (fun n : ℕ ↦ A / (n : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left A
  refine ⟨A, hA, hsum, ?_⟩
  have hheadPoint : ∀ n ∈ Finset.range Q, n.Prime →
      ∀ᶠ X : ℕ in atTop,
        fixedCenterActualUpRatio S c X n ≤ (3 / 4 : ℝ) := by
    intro n hnQ hnPrime
    have hlim := fixedCenterActualUpRatio_tendsto S hS hc hnPrime.pos
    have hlt : (n : ℝ)⁻¹ < (3 / 4 : ℝ) := by
      have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hnPrime.two_le
      have hinv : (n : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
        rw [inv_le_comm₀ (by norm_num) (by positivity)]
        nlinarith
      linarith
    exact hlim.eventually (isOpen_Iio.mem_nhds hlt) |>.mono fun _ h ↦ h.le
  have hhead : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.range Q, n.Prime →
        fixedCenterActualUpRatio S c X n ≤ (3 / 4 : ℝ) := by
    have hall : ∀ n ∈ Finset.range Q,
        ∀ᶠ X : ℕ in atTop, n.Prime →
          fixedCenterActualUpRatio S c X n ≤ (3 / 4 : ℝ) := by
      intro n hn
      by_cases hp : n.Prime
      · exact (hheadPoint n hn hp).mono fun _ h _ ↦ h
      · exact Filter.Eventually.of_forall fun _ h ↦ (hp h).elim
    exact Filter.eventually_all.2 hall
  filter_upwards [hratio, hhead,
      eventually_fixedCenterArithmeticDegree_ge_half_main S hS hc,
      eventually_ge_atTop 4] with X hratioX hheadX hDlower hX
  intro n
  by_cases hsupp : n.Prime ∧ n ∉ S ∧ n ≤ Nat.sqrt X
  · have hnPrime := hsupp.1
    have hnAllowed : n ∈
        (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S) := by
      simp [Nat.mem_primesLE, hsupp]
    have hnPos := hnPrime.pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hYR : (0 : ℝ) < Nat.sqrt X := by
      have : 1 ≤ Nat.sqrt X := hnPrime.one_le.trans hsupp.2.2
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
    have hlogX : 1 ≤ Real.log (X : ℝ) := by
      have hx : (Real.exp 1 : ℝ) ≤ X := by
        have : (4 : ℝ) ≤ X := by exact_mod_cast hX
        exact (by norm_num : Real.exp 1 ≤ (4 : ℝ)).trans this
      rw [← Real.exp_le_exp]
      simpa using hx
    have hDpos : 0 < fixedCenterArithmeticDegree S c X := by
      have hmainPos : 0 < (c : ℝ)⁻¹ *
          ((X : ℝ) / Real.log (X : ℝ)) := by positivity
      linarith [hDlower]
    have hrNonneg : 0 ≤ fixedCenterActualUpRatio S c X n := by
      by_cases hcut : c * n ≤ Nat.sqrt X
      · have hcnPos : 0 < c * n := Nat.mul_pos hc hnPos
        have hySq : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sq_sqrt_le X
        have hcnY : (c * n) * Nat.sqrt X ≤ X :=
          (Nat.mul_le_mul_right (Nat.sqrt X) hcut).trans hySq
        have hYdiv : Nat.sqrt X ≤ X / (c * n) :=
          (Nat.le_div_iff_mul_le hcnPos).2 hcnY
        have hmono := allowedPrimeCount_mono (S := S) hYdiv
        rw [fixedCenterActualUpRatio, if_pos hcut]
        unfold fixedCenterArithmeticDegree
        have hnum : 0 ≤
            (allowedPrimeCount S (X / (c * n)) : ℝ) -
              (allowedPrimeCount S (Nat.sqrt X) : ℝ) := by exact_mod_cast hmono
        positivity
      · simp [fixedCenterActualUpRatio, hcut]
    have htermNonneg : 0 ≤ fixedCenterActualUpNonlinearTerm S c X n := by
      rw [fixedCenterActualUpNonlinearTerm, if_pos hsupp]
      by_cases hden : fixedCenterActualUpRatio S c X n < 1
      · positivity
      · -- This branch is ruled out below by either the finite-head or tail cap.
        simp only
        have : False := by
          by_cases hnQ : n < Q
          · have := hheadX n (Finset.mem_range.2 hnQ) hnPrime
            linarith
          · have hnQ' : Q ≤ n := Nat.le_of_not_gt hnQ
            have hcut : c * n ≤ Nat.sqrt X := by
              by_contra hnot
              simp [fixedCenterActualUpRatio, hnot] at hden
            have hcOverY : (c : ℝ) / (Nat.sqrt X : ℝ) ≤ (n : ℝ)⁻¹ := by
              rw [div_le_inv₀ hc.le hnR.le]
              exact_mod_cast hcut
            have hErr := hratioX n hnAllowed
            have hmodelLe : fixedCenterUpRatioModel c n X ≤ 3 / (n : ℝ) := by
              have hL := eventually_fixedCenter_logSqrt_between hc
              -- All scale hypotheses were already used inside `hratioX`; a
              -- direct consequence is obtained by adding the error bound.
              have hdiff : fixedCenterActualUpRatio S c X n -
                  fixedCenterUpRatioModel c n X ≤
                    |fixedCenterActualUpRatio S c X n -
                      fixedCenterUpRatioModel c n X| := le_abs_self _
              have hmodelNonneg : 0 ≤ fixedCenterUpRatioModel c n X := by
                by_contra hneg
                have : fixedCenterActualUpRatio S c X n < 1 := by
                  calc
                    fixedCenterActualUpRatio S c X n ≤
                        fixedCenterUpRatioModel c n X +
                          |fixedCenterActualUpRatio S c X n -
                            fixedCenterUpRatioModel c n X| := by linarith
                    _ ≤ fixedCenterUpRatioModel c n X +
                        K * (1 / ((n : ℝ) * Real.log (X : ℝ)) +
                          (c : ℝ) / (Nat.sqrt X : ℝ)) := by gcongr
                    _ < 1 := by
                      have hKQ : 4 * (2 * K + 3) < (n : ℝ) :=
                        hQ.trans_le (by exact_mod_cast hnQ')
                      have hrecipLog : 1 / ((n : ℝ) * Real.log (X : ℝ)) ≤
                          (n : ℝ)⁻¹ := by
                        rw [one_div, mul_inv_rev]
                        gcongr
                        exact inv_le_one₀.mpr hlogX
                      nlinarith [hK, hcOverY, hrecipLog]
                exact (not_lt_of_ge (le_of_not_gt hden)) this
              exact le_of_not_gt hneg
            have hrecipLog : 1 / ((n : ℝ) * Real.log (X : ℝ)) ≤
                (n : ℝ)⁻¹ := by
              rw [one_div, mul_inv_rev]
              gcongr
              exact inv_le_one₀.mpr hlogX
            have hactualLe : fixedCenterActualUpRatio S c X n ≤
                (2 * K + 3) / (n : ℝ) := by
              calc
                fixedCenterActualUpRatio S c X n ≤
                    fixedCenterUpRatioModel c n X +
                      |fixedCenterActualUpRatio S c X n -
                        fixedCenterUpRatioModel c n X| := by linarith [le_abs_self
                          (fixedCenterActualUpRatio S c X n -
                            fixedCenterUpRatioModel c n X)]
                _ ≤ 3 / (n : ℝ) +
                    K * (1 / ((n : ℝ) * Real.log (X : ℝ)) +
                      (c : ℝ) / (Nat.sqrt X : ℝ)) := add_le_add hmodelLe hErr
                _ ≤ (2 * K + 3) / (n : ℝ) := by
                  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
                  nlinarith [hK, hnR.le, hcOverY, hrecipLog]
            have hsmall : (2 * K + 3) / (n : ℝ) < 1 / 4 := by
              rw [div_lt_iff₀ hnR]
              nlinarith [hQ.trans_le (by exact_mod_cast hnQ')]
            linarith
        exact this.elim
    rw [Real.norm_eq_abs, abs_of_nonneg htermNonneg]
    rw [fixedCenterActualUpNonlinearTerm, if_pos hsupp]
    by_cases hnQ : n < Q
    · have hrLe := hheadX n (Finset.mem_range.2 hnQ) hnPrime
      have hden : 1 / 4 ≤ 1 - fixedCenterActualUpRatio S c X n := by linarith
      have hnLeQ : (n : ℝ) ≤ Q := by exact_mod_cast (Nat.le_of_lt hnQ)
      have hAQ : 4 ≤ A / (n : ℝ) ^ 2 := by
        dsimp [A]
        rw [le_div_iff₀ (sq_pos_of_pos hnR)]
        nlinarith [sq_le_sq₀ hnR.le (by positivity : (0 : ℝ) ≤ Q) hnLeQ]
      calc
        fixedCenterActualUpRatio S c X n ^ 2 /
              (1 - fixedCenterActualUpRatio S c X n) ≤ 4 := by
          rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hden)]
          nlinarith [hrNonneg, hrLe]
        _ ≤ A / (n : ℝ) ^ 2 := hAQ
    · have hnQ' : Q ≤ n := Nat.le_of_not_gt hnQ
      by_cases hcut : c * n ≤ Nat.sqrt X
      · have hcOverY : (c : ℝ) / (Nat.sqrt X : ℝ) ≤ (n : ℝ)⁻¹ := by
          rw [div_le_inv₀ hc.le hnR.le]
          exact_mod_cast hcut
        have hErr := hratioX n hnAllowed
        have hLpos : 0 < fixedCenterLogScale c X := by
          have hlogc : 0 ≤ Real.log (c : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hc)
          rw [fixedCenterLogScale]
          have : Real.log (c : ℝ) < Real.log (X : ℝ) := by
            apply Real.strictMonoOn_log
            · exact_mod_cast hc
            · positivity
            · exact_mod_cast (hc.trans_le (hc.mul_le_mul_right hnPrime.one_le) |>.trans hcut |>.trans
                (Nat.sqrt_le X))
          linarith
        have hlogn : Real.log (n : ℝ) ≤ Real.log (Nat.sqrt X : ℝ) :=
          Real.log_le_log hnR (by exact_mod_cast hsupp.2.2)
        have hlogSqrt : Real.log (Nat.sqrt X : ℝ) ≤
            2 * fixedCenterLogScale c X / 3 := by
          -- Recover this endpoint comparison directly from the large `X`
          -- hypotheses encoded in the uniform ratio theorem.
          have hbetween := eventually_fixedCenter_logSqrt_between hc
          have hnow : Real.log (Nat.sqrt X : ℝ) < fixedCenterLogScale c X := by
            have hcN : c * n ≤ Nat.sqrt X := hcut
            have hcNpos : 0 < c * n := Nat.mul_pos hc hnPos
            have : c * n < X := (hcut.trans (Nat.sqrt_le X)).lt_of_ne
              (by intro heq; omega)
            exact Real.strictMonoOn_log (by exact_mod_cast hcNpos)
              (by exact_mod_cast (show 0 < X by omega)) (by exact_mod_cast this)
          linarith
        have hmodelLe : fixedCenterUpRatioModel c n X ≤ 3 / (n : ℝ) := by
          unfold fixedCenterUpRatioModel
          have hden : 0 < fixedCenterLogScale c X - Real.log (n : ℝ) := by
            linarith
          rw [div_le_iff₀ (mul_pos hnR hden)]
          nlinarith [hlogn, hlogSqrt]
        have hrecipLog : 1 / ((n : ℝ) * Real.log (X : ℝ)) ≤
            (n : ℝ)⁻¹ := by
          rw [one_div, mul_inv_rev]
          gcongr
          exact inv_le_one₀.mpr hlogX
        have hrLe : fixedCenterActualUpRatio S c X n ≤
            (2 * K + 3) / (n : ℝ) := by
          calc
            fixedCenterActualUpRatio S c X n ≤
                fixedCenterUpRatioModel c n X +
                  |fixedCenterActualUpRatio S c X n -
                    fixedCenterUpRatioModel c n X| := by
                      linarith [le_abs_self (fixedCenterActualUpRatio S c X n -
                        fixedCenterUpRatioModel c n X)]
            _ ≤ 3 / (n : ℝ) +
                K * (1 / ((n : ℝ) * Real.log (X : ℝ)) +
                  (c : ℝ) / (Nat.sqrt X : ℝ)) := add_le_add hmodelLe hErr
            _ ≤ (2 * K + 3) / (n : ℝ) := by
              rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
              nlinarith [hK, hnR.le, hcOverY, hrecipLog]
        have hrQuarter : fixedCenterActualUpRatio S c X n < 1 / 4 := by
          calc
            fixedCenterActualUpRatio S c X n ≤ (2 * K + 3) / (n : ℝ) := hrLe
            _ < 1 / 4 := by
              rw [div_lt_iff₀ hnR]
              nlinarith [hQ.trans_le (by exact_mod_cast hnQ')]
        have hden : 1 / 2 ≤ 1 - fixedCenterActualUpRatio S c X n := by linarith
        calc
          fixedCenterActualUpRatio S c X n ^ 2 /
                (1 - fixedCenterActualUpRatio S c X n) ≤
              2 * ((2 * K + 3) / (n : ℝ)) ^ 2 := by
            rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden)]
            nlinarith [sq_le_sq₀ hrNonneg hrLe.le]
          _ ≤ A / (n : ℝ) ^ 2 := by
            dsimp [A]
            rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hnR) (sq_pos_of_pos hnR)]
            nlinarith [hQ.trans_le (by exact_mod_cast hnQ')]
      · simp [fixedCenterActualUpRatio, hcut]
  · simp [fixedCenterActualUpNonlinearTerm, hsupp]
-/

end

end PrimeStar
