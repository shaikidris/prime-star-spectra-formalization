import PrimeStar.LogarithmicWindowCorrectionArithmetic

/-!
# Uniform actual up-star ratios on the logarithmic centre window

The quantitative PNT is applied simultaneously to the centre degree and to
every up-star degree through the square-root prime window.  The resulting
error is summable over the prime labels and is uniform in the moving centre.
-/

namespace PrimeStar

open Filter Topology Asymptotics
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 3000000

/-- In the full square-root prime window the moving PNT ratio model is
nonnegative and bounded by `3 / q`, uniformly in the logarithmic centre
window. -/
theorem eventually_logarithmicWindowUpRatioModel_bounds
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        ∀ q ∈ Nat.primesLE (Nat.sqrt X),
          0 ≤ fixedCenterUpRatioModel a q X ∧
            fixedCenterUpRatioModel a q X ≤ 3 / (q : ℝ) := by
  filter_upwards [eventually_logarithmicWindow_logSqrt_gap_bounds hε,
      eventually_logarithmicWindow_logScale_between hε,
      eventually_ge_atTop 4] with X hlogY hlogL hX
  intro a ha q hq
  have hqPrime : q.Prime := (Nat.mem_primesLE.mp hq).2
  have hqLeY : q ≤ Nat.sqrt X := (Nat.mem_primesLE.mp hq).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hLpos : 0 < fixedCenterLogScale a X :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 11 * Real.log (X : ℝ) / 12)
      (hlogL a ha).1
  have hlogq : Real.log (q : ℝ) ≤ Real.log (Nat.sqrt X : ℝ) :=
    Real.log_le_log hqR (by exact_mod_cast hqLeY)
  have hgapThird : Real.log (X : ℝ) / 3 ≤
      fixedCenterLogScale a X - Real.log (q : ℝ) :=
    (hlogY a ha).2.2.trans (sub_le_sub_left hlogq _)
  have hgap : Real.log (q : ℝ) < fixedCenterLogScale a X := by linarith
  constructor
  · unfold fixedCenterUpRatioModel
    positivity
  · unfold fixedCenterUpRatioModel
    rw [div_le_iff₀ (mul_pos hqR (lt_of_lt_of_le (by positivity) hgapThird))]
    have hLupper := (hlogL a ha).2
    field_simp [hqR.ne']
    nlinarith

/-- Uniform PNT comparison of every actual up-star ratio with its moving
main-term model.  The constant is independent of both the scale and the
centre in the logarithmic window. -/
theorem exists_logarithmicWindowActualUpRatio_sub_model_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
          |fixedCenterActualUpRatio S (a : ℕ) X q -
              fixedCenterUpRatioModel (a : ℕ) q X| ≤
            K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
              (a : ℝ) / (Nat.sqrt X : ℝ)) := by
  obtain ⟨C, hC, hPNT⟩ := exists_realPrimeCounting_error_bound
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hPNT
  have hPi := eventually_allowedPrimeCount_le
    (S := (∅ : Finset ℕ)) (ε := 1) zero_lt_one
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 hPi
  let B : ℝ := Real.log 4 + 1
  let K : ℝ := 2000 * (C + B + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hsqrtCastTop : Tendsto (fun X : ℕ ↦ (Nat.sqrt X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop
  filter_upwards [
      hsqrtCastTop.eventually_ge_atTop (max (max x₀ x₁) (Real.exp 1)),
      eventually_finset_le_nat_sqrt S,
      eventually_logarithmicWindow_largePrimeStarDegree_ge S hS hε,
      eventually_logarithmicWindow_logSqrt_gap_bounds hε,
      eventually_logarithmicWindow_logScale_between hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε,
      eventually_ge_atTop 4] with
      X hYlarge hSY hDlower hlogY hlogL hcenter hX
  intro a ha q hq
  let A : ℕ := (a : ℕ)
  have hqMem := (Finset.mem_filter.mp hq).1
  have hqPrime : q.Prime := (Nat.mem_primesLE.mp hqMem).2
  have hqLeY : q ≤ Nat.sqrt X := (Nat.mem_primesLE.mp hqMem).1
  have hqPos : 0 < q := hqPrime.pos
  have hAPos : 0 < A := Vertex.coe_pos a
  have hAR : (0 : ℝ) < A := by exact_mod_cast hAPos
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
  have hlogYX := hlogY a ha
  have hlogLX := hlogL a ha
  have hLpos : 0 < fixedCenterLogScale A X :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 11 * Real.log (X : ℝ) / 12)
      hlogLX.1
  have hlogq : Real.log (q : ℝ) ≤ Real.log (Nat.sqrt X : ℝ) :=
    Real.log_le_log hqR (by exact_mod_cast hqLeY)
  have hgapThird : Real.log (X : ℝ) / 3 ≤
      fixedCenterLogScale A X - Real.log (q : ℝ) :=
    hlogYX.2.2.trans (sub_le_sub_left hlogq _)
  have hgap : Real.log (q : ℝ) < fixedCenterLogScale A X := by
    linarith
  have hmodelPos : 0 ≤ fixedCenterUpRatioModel A q X := by
    unfold fixedCenterUpRatioModel
    positivity
  have hmodelLe : fixedCenterUpRatioModel A q X ≤ 3 / (q : ℝ) := by
    unfold fixedCenterUpRatioModel
    rw [div_le_iff₀ (mul_pos hqR (lt_of_lt_of_le (by positivity) hgapThird))]
    have hLupper := hlogLX.2
    field_simp [hqR.ne']
    nlinarith
  by_cases hcut : A * q ≤ Nat.sqrt X
  · let y : ℝ := Nat.sqrt X
    let t : ℝ := (X : ℝ) / (A : ℝ)
    let tq : ℝ := (X : ℝ) / ((A : ℝ) * (q : ℝ))
    let L : ℝ := fixedCenterLogScale A X
    let D : ℝ := fixedCenterArithmeticDegree S A X
    let N : ℝ := fixedCenterArithmeticDegree S (A * q) X
    let M : ℝ := pntMainReal t
    let m : ℝ := pntMainReal tq
    have hAqPos : 0 < A * q := Nat.mul_pos hAPos hqPos
    have hySq : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    have hAqY : (A * q) * Nat.sqrt X ≤ X :=
      (Nat.mul_le_mul_right (Nat.sqrt X) hcut).trans hySq
    have hAY' : A * Nat.sqrt X ≤ X := by
      have hALe : A ≤ A * q := Nat.le_mul_of_pos_right A hqPos
      exact (Nat.mul_le_mul_right (Nat.sqrt X) hALe).trans hAqY
    have hYqNat : Nat.sqrt X ≤ X / (A * q) :=
      (Nat.le_div_iff_mul_le hAqPos).2 (by simpa [mul_comm] using hAqY)
    have hYcNat : Nat.sqrt X ≤ X / A :=
      (Nat.le_div_iff_mul_le hAPos).2 (by simpa [mul_comm] using hAY')
    have hYtq : y ≤ tq := by
      dsimp [y, tq]
      rw [le_div_iff₀ (mul_pos hAR hqR)]
      exact_mod_cast (show Nat.sqrt X * (A * q) ≤ X by simpa [mul_comm] using hAqY)
    have hYt : y ≤ t := by
      dsimp [y, t]
      rw [le_div_iff₀ hAR]
      exact_mod_cast (show Nat.sqrt X * A ≤ X by simpa [mul_comm] using hAY')
    have hx₀Y : x₀ ≤ y :=
      (le_max_left x₀ x₁).trans (le_max_left (max x₀ x₁) (Real.exp 1)) |>.trans hYlarge
    have hx₁Y : x₁ ≤ y :=
      (le_max_right x₀ x₁).trans (le_max_left (max x₀ x₁) (Real.exp 1)) |>.trans hYlarge
    have hPNTy := hx₀ y hx₀Y
    have hPNTt := hx₀ t (hx₀Y.trans hYt)
    have hPNTtq := hx₀ tq (hx₀Y.trans hYtq)
    have hPiY := hx₁ y hx₁Y
    have hfloorT : ⌊t⌋₊ = X / A := by
      dsimp [t]
      exact natFloor_real_div_eq_div X A
    have hfloorTq : ⌊tq⌋₊ = X / (A * q) := by
      dsimp [tq]
      simpa only [Nat.cast_mul] using natFloor_real_div_eq_div X (A * q)
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
      exact log_div_eq_fixedCenterLogScale hAPos (show 0 < X by omega)
    have hlogtq : Real.log tq = L - Real.log (q : ℝ) := by
      dsimp [tq, L]
      have hX0 : (X : ℝ) ≠ 0 := hXR.ne'
      have hA0 : (A : ℝ) ≠ 0 := hAR.ne'
      have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
      rw [Real.log_div hX0 (mul_ne_zero hA0 hq0), Real.log_mul hA0 hq0,
        fixedCenterLogScale]
      ring
    have hMpos : 0 < M := by
      dsimp [M, pntMainReal]
      rw [hlogt]
      positivity
    have hDpos : 0 < D := by
      dsimp [D]
      have hdegree := hDlower a ha
      have hcast := largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree
        hS a (hcenter A ha) hYcNat
      rw [hcast] at hdegree
      have hmainPos : 0 < (X : ℝ) /
          (16 * (A : ℝ) * Real.log (X : ℝ)) := by positivity
      exact hmainPos.trans_le hdegree
    have hPiYbound : (Nat.primeCounting (Nat.sqrt X) : ℝ) ≤
        B * y / Real.log y := by
      simpa [B, y] using hPiY
    have hErrT : |(Nat.primeCounting (X / A) : ℝ) - M| ≤
        C * t / L ^ 2 := by simpa [M, pntMainReal, hlogt] using hPNTt
    have hErrTq : |(Nat.primeCounting (X / (A * q)) : ℝ) - m| ≤
        12 * C * tq / L ^ 2 := by
      have hlogtqPos : 0 < Real.log tq := by rw [hlogtq]; linarith
      have hdenSq : (Real.log (X : ℝ) / 3) ^ 2 ≤ Real.log tq ^ 2 := by
        rw [hlogtq]
        nlinarith [hgapThird]
      have htqNonneg : 0 ≤ tq := le_trans (by positivity) hYtq
      have hX2 : 0 < Real.log (X : ℝ) ^ 2 := sq_pos_of_pos hlogX
      calc
        |(Nat.primeCounting (X / (A * q)) : ℝ) - m| ≤
            C * tq / Real.log tq ^ 2 := by simpa [m, pntMainReal] using hPNTtq
        _ ≤ 9 * C * tq / Real.log (X : ℝ) ^ 2 := by
          have hlog2 : 0 < Real.log tq ^ 2 := sq_pos_of_pos hlogtqPos
          rw [div_le_div_iff₀ hlog2 hX2]
          have hscale : Real.log (X : ℝ) ^ 2 ≤ 9 * Real.log tq ^ 2 := by
            nlinarith [hdenSq]
          calc
            C * tq * Real.log (X : ℝ) ^ 2 ≤
                C * tq * (9 * Real.log tq ^ 2) := by
              exact mul_le_mul_of_nonneg_left hscale (mul_nonneg hC.le htqNonneg)
            _ = 9 * C * tq * Real.log tq ^ 2 := by ring
        _ ≤ 12 * C * tq / L ^ 2 := by
          have hL2 : 0 < L ^ 2 := sq_pos_of_pos hLpos
          have hscale : L ^ 2 ≤ Real.log (X : ℝ) ^ 2 :=
            (sq_le_sq₀ hLpos.le hlogX.le).2 hlogLX.2
          rw [div_le_div_iff₀ hX2 hL2]
          have hct : 0 ≤ C * tq := mul_nonneg hC.le htqNonneg
          nlinarith [mul_le_mul_of_nonneg_left hscale hct]
    have hEN : |N - m| ≤ 12 * C * tq / L ^ 2 + B * y / Real.log y := by
      rw [show N = (Nat.primeCounting (X / (A * q)) : ℝ) -
          (Nat.primeCounting (Nat.sqrt X) : ℝ) by simpa [N] using hNEq]
      calc
        |((Nat.primeCounting (X / (A * q)) : ℝ) -
              (Nat.primeCounting (Nat.sqrt X) : ℝ)) - m| =
            |((Nat.primeCounting (X / (A * q)) : ℝ) - m) -
              (Nat.primeCounting (Nat.sqrt X) : ℝ)| := by ring
        _ ≤ |(Nat.primeCounting (X / (A * q)) : ℝ) - m| +
              |(Nat.primeCounting (Nat.sqrt X) : ℝ)| := abs_sub _ _
        _ ≤ 12 * C * tq / L ^ 2 + B * y / Real.log y := by
          rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.primeCounting (Nat.sqrt X) : ℝ))]
          exact add_le_add hErrTq hPiYbound
    have hED : |D - M| ≤ C * t / L ^ 2 + B * y / Real.log y := by
      rw [show D = (Nat.primeCounting (X / A) : ℝ) -
          (Nat.primeCounting (Nat.sqrt X) : ℝ) by simpa [D] using hDEq]
      calc
        |((Nat.primeCounting (X / A) : ℝ) -
              (Nat.primeCounting (Nat.sqrt X) : ℝ)) - M| =
            |((Nat.primeCounting (X / A) : ℝ) - M) -
              (Nat.primeCounting (Nat.sqrt X) : ℝ)| := by ring
        _ ≤ |(Nat.primeCounting (X / A) : ℝ) - M| +
              |(Nat.primeCounting (Nat.sqrt X) : ℝ)| := abs_sub _ _
        _ ≤ C * t / L ^ 2 + B * y / Real.log y := by
          rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.primeCounting (Nat.sqrt X) : ℝ))]
          exact add_le_add hErrT hPiYbound
    have hratio := abs_div_sub_div_le hDpos hMpos hEN hED
    have hmodelEq : m / M = fixedCenterUpRatioModel A q X := by
      dsimp [m, M, tq, t]
      exact pntMainReal_ratio_eq_upRatioModel hAPos hqPos
        (show 0 < X by omega) hgap
    rw [hmodelEq, abs_of_nonneg hmodelPos] at hratio
    rw [fixedCenterActualUpRatio, if_pos hcut]
    change |N / D - fixedCenterUpRatioModel A q X| ≤ _
    have hDcoarse : (X : ℝ) /
        (16 * (A : ℝ) * Real.log (X : ℝ)) ≤ D := by
      dsimp [D]
      have hdegree := hDlower a ha
      have hcast := largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree
        hS a (hcenter A ha) hYcNat
      rw [hcast] at hdegree
      exact hdegree
    have hySqR : y ^ 2 ≤ (X : ℝ) := by
      dsimp [y]
      simpa [pow_two] using (show
        (Nat.sqrt X : ℝ) * (Nat.sqrt X : ℝ) ≤ (X : ℝ) by exact_mod_cast hySq)
    have htEq : t = (X : ℝ) / (A : ℝ) := rfl
    have htqEq : tq = t / (q : ℝ) := by
      dsimp [tq, t]
      field_simp
    have hInvD : 1 / D ≤
        16 * (A : ℝ) * Real.log (X : ℝ) / (X : ℝ) := by
      have hcoarsePos : 0 < (X : ℝ) /
          (16 * (A : ℝ) * Real.log (X : ℝ)) := by positivity
      have hinv := one_div_le_one_div_of_le hcoarsePos hDcoarse
      calc
        1 / D ≤ 1 / ((X : ℝ) /
            (16 * (A : ℝ) * Real.log (X : ℝ))) := hinv
        _ = 16 * (A : ℝ) * Real.log (X : ℝ) / (X : ℝ) := by
          field_simp
    have hboundary : (B * y / Real.log y) / D ≤
        48 * B * (A : ℝ) / y := by
      have hbyNonneg : 0 ≤ B * y / Real.log y := by positivity
      calc
        (B * y / Real.log y) / D =
            (B * y / Real.log y) * (1 / D) := by ring
        _ ≤ (B * y / Real.log y) *
            (16 * (A : ℝ) * Real.log (X : ℝ) / (X : ℝ)) := by gcongr
        _ ≤ 48 * B * (A : ℝ) * y / (X : ℝ) := by
          have hlogRatio : Real.log (X : ℝ) / Real.log y ≤ 3 :=
            (div_le_iff₀ hlogYpos).2 (by simpa [y] using
              (show Real.log (X : ℝ) ≤ 3 * Real.log (Nat.sqrt X : ℝ) by
                linarith [hlogYX.1]))
          calc
            (B * y / Real.log y) *
                (16 * (A : ℝ) * Real.log (X : ℝ) / (X : ℝ)) =
              (16 * B * (A : ℝ) * y / (X : ℝ)) *
                (Real.log (X : ℝ) / Real.log y) := by ring
            _ ≤ (16 * B * (A : ℝ) * y / (X : ℝ)) * 3 := by gcongr
            _ = 48 * B * (A : ℝ) * y / (X : ℝ) := by ring
        _ ≤ 48 * B * (A : ℝ) / y := by
          rw [div_le_div_iff₀ hXR hYR]
          convert mul_le_mul_of_nonneg_left hySqR
            (by positivity : 0 ≤ 48 * B * (A : ℝ)) using 1
          all_goals ring
    have hPntQ : (12 * C * tq / L ^ 2) / D ≤
        768 * C / ((q : ℝ) * Real.log (X : ℝ)) := by
      calc
        (12 * C * tq / L ^ 2) / D =
            (12 * C * tq / L ^ 2) * (1 / D) := by ring
        _ ≤ (12 * C * tq / L ^ 2) *
            (16 * (A : ℝ) * Real.log (X : ℝ) / (X : ℝ)) := by
              gcongr
        _ = 192 * C * Real.log (X : ℝ) /
            ((q : ℝ) * L ^ 2) := by
              rw [htqEq, htEq]
              field_simp
              ring
        _ ≤ 768 * C / ((q : ℝ) * Real.log (X : ℝ)) := by
          have hlogLe : Real.log (X : ℝ) ≤ 2 * L := by linarith [hlogLX.1]
          have hLsq : Real.log (X : ℝ) ^ 2 ≤ 4 * L ^ 2 := by
            have hsquare : Real.log (X : ℝ) ^ 2 ≤ (2 * L) ^ 2 :=
              (sq_le_sq₀ hlogX.le (mul_nonneg (by norm_num) hLpos.le)).2 hlogLe
            convert hsquare using 1
            all_goals ring
          rw [div_le_div_iff₀ (mul_pos hqR (sq_pos_of_pos hLpos))
            (mul_pos hqR hlogX)]
          convert mul_le_mul_of_nonneg_left hLsq
            (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 192) hC.le) hqR.le)
            using 1 <;> ring
    have hPnt0 : (C * t / L ^ 2) / D ≤
        64 * C / Real.log (X : ℝ) := by
      calc
        (C * t / L ^ 2) / D = (C * t / L ^ 2) * (1 / D) := by ring
        _ ≤ (C * t / L ^ 2) *
            (16 * (A : ℝ) * Real.log (X : ℝ) / (X : ℝ)) := by
              gcongr
        _ = 16 * C * Real.log (X : ℝ) / L ^ 2 := by
              rw [htEq]
              field_simp
        _ ≤ 64 * C / Real.log (X : ℝ) := by
          have hlogLe : Real.log (X : ℝ) ≤ 2 * L := by linarith [hlogLX.1]
          have hLsq : Real.log (X : ℝ) ^ 2 ≤ 4 * L ^ 2 := by
            have hsquare : Real.log (X : ℝ) ^ 2 ≤ (2 * L) ^ 2 :=
              (sq_le_sq₀ hlogX.le (mul_nonneg (by norm_num) hLpos.le)).2 hlogLe
            convert hsquare using 1
            all_goals ring
          rw [div_le_div_iff₀ (sq_pos_of_pos hLpos) hlogX]
          convert mul_le_mul_of_nonneg_left hLsq
            (mul_nonneg (by positivity : (0 : ℝ) ≤ 16) hC.le) using 1 <;> ring
    have hnumQ :
        (12 * C * tq / L ^ 2 + B * y / Real.log y) / D ≤
          768 * C / ((q : ℝ) * Real.log (X : ℝ)) +
            48 * B * (A : ℝ) / y := by
      rw [add_div]
      exact add_le_add hPntQ hboundary
    have hnum0 :
        (C * t / L ^ 2 + B * y / Real.log y) / D ≤
          64 * C / Real.log (X : ℝ) + 48 * B * (A : ℝ) / y := by
      rw [add_div]
      exact add_le_add hPnt0 hboundary
    have hmodelTerm :
        fixedCenterUpRatioModel A q X *
              (C * t / L ^ 2 + B * y / Real.log y) / D ≤
          (3 / (q : ℝ)) *
            (64 * C / Real.log (X : ℝ) + 48 * B * (A : ℝ) / y) := by
      calc
        fixedCenterUpRatioModel A q X *
              (C * t / L ^ 2 + B * y / Real.log y) / D =
            fixedCenterUpRatioModel A q X *
              ((C * t / L ^ 2 + B * y / Real.log y) / D) := by ring
        _ ≤ (3 / (q : ℝ)) *
            (64 * C / Real.log (X : ℝ) + 48 * B * (A : ℝ) / y) :=
          mul_le_mul hmodelLe hnum0 (by positivity) (by positivity)
    calc
      |N / D - fixedCenterUpRatioModel A q X| ≤
          (12 * C * tq / L ^ 2 + B * y / Real.log y) / D +
            fixedCenterUpRatioModel A q X *
              (C * t / L ^ 2 + B * y / Real.log y) / D := hratio
      _ ≤ (768 * C / ((q : ℝ) * Real.log (X : ℝ)) +
            48 * B * (A : ℝ) / y) +
          (3 / (q : ℝ)) *
            (64 * C / Real.log (X : ℝ) + 48 * B * (A : ℝ) / y) := by
              exact add_le_add hnumQ hmodelTerm
      _ ≤ K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (A : ℝ) / (Nat.sqrt X : ℝ)) := by
          have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqPrime.one_le
          have hqInvLe : 1 / (q : ℝ) ≤ 1 := (div_le_one hqR).2 hqOne
          have hfirst :
              768 * C / ((q : ℝ) * Real.log (X : ℝ)) +
                  48 * B * (A : ℝ) / y +
                  (3 / (q : ℝ)) *
                    (64 * C / Real.log (X : ℝ) + 48 * B * (A : ℝ) / y) =
                960 * C * (1 / ((q : ℝ) * Real.log (X : ℝ))) +
                  (48 * B + 144 * B / (q : ℝ)) * ((A : ℝ) / y) := by ring
          rw [hfirst]
          have hcoefE : 48 * B + 144 * B / (q : ℝ) ≤ 192 * B := by
            calc
              48 * B + 144 * B / (q : ℝ) ≤ 48 * B + 144 * B := by
                gcongr
                simpa [div_eq_mul_inv, mul_assoc] using
                  (mul_le_mul_of_nonneg_left hqInvLe (by positivity : 0 ≤ 144 * B))
              _ = 192 * B := by ring
          have hcoeffC : 960 * C ≤ K := by
            dsimp [K]
            nlinarith [hC.le, hB.le]
          have hcoeffB : 192 * B ≤ K := by
            dsimp [K]
            nlinarith [hC.le, hB.le]
          calc
            960 * C * (1 / ((q : ℝ) * Real.log (X : ℝ))) +
                (48 * B + 144 * B / (q : ℝ)) * ((A : ℝ) / y) ≤
                960 * C * (1 / ((q : ℝ) * Real.log (X : ℝ))) +
                  192 * B * ((A : ℝ) / y) := by gcongr
            _ ≤ K * (1 / ((q : ℝ) * Real.log (X : ℝ))) +
                  K * ((A : ℝ) / y) := add_le_add
              (mul_le_mul_of_nonneg_right hcoeffC (by positivity))
              (mul_le_mul_of_nonneg_right hcoeffB (by positivity))
            _ = K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
                (A : ℝ) / (Nat.sqrt X : ℝ)) := by dsimp [y]; ring
  · rw [fixedCenterActualUpRatio, if_neg hcut, zero_sub, abs_neg,
      abs_of_nonneg hmodelPos]
    have hAqGt : Nat.sqrt X < A * q := Nat.lt_of_not_ge hcut
    have hqLower : (Nat.sqrt X : ℝ) < (A : ℝ) * (q : ℝ) := by exact_mod_cast hAqGt
    have hrecip : 3 / (q : ℝ) ≤ 3 * (A : ℝ) / (Nat.sqrt X : ℝ) := by
      rw [div_le_div_iff₀ hqR hYR]
      nlinarith [hAR.le, hqLower]
    calc
      fixedCenterUpRatioModel A q X ≤ 3 / (q : ℝ) := hmodelLe
      _ ≤ 3 * (A : ℝ) / (Nat.sqrt X : ℝ) := hrecip
      _ ≤ K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (A : ℝ) / (Nat.sqrt X : ℝ)) := by
        have hsum : 0 ≤ 1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (A : ℝ) / (Nat.sqrt X : ℝ) := by positivity
        have hKthree : 3 ≤ K := by dsimp [K]; nlinarith [hC.le, hB.le]
        calc
          3 * (A : ℝ) / (Nat.sqrt X : ℝ) ≤
              3 * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
                (A : ℝ) / (Nat.sqrt X : ℝ)) := by
            have hz : 0 ≤ 1 / ((q : ℝ) * Real.log (X : ℝ)) := by positivity
            have hi : (A : ℝ) / (Nat.sqrt X : ℝ) ≤
                1 / ((q : ℝ) * Real.log (X : ℝ)) +
                  (A : ℝ) / (Nat.sqrt X : ℝ) := by linarith
            calc
              3 * (A : ℝ) / (Nat.sqrt X : ℝ) =
                  3 * ((A : ℝ) / (Nat.sqrt X : ℝ)) := by ring
              _ ≤ 3 * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
                    (A : ℝ) / (Nat.sqrt X : ℝ)) :=
                mul_le_mul_of_nonneg_left hi (by norm_num)
          _ ≤ K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
                (A : ℝ) / (Nat.sqrt X : ℝ)) :=
            mul_le_mul_of_nonneg_right hKthree hsum

/-- The endpoint-prime count multiplied by a moving centre is negligible
after normalization by the square-root endpoint. -/
theorem eventually_logarithmicWindow_count_mul_center_div_sqrt_lt
    (S : Finset ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        (allowedPrimeCount S (Nat.sqrt X) : ℝ) *
          ((a : ℝ) / (Nat.sqrt X : ℝ)) < δ := by
  have hsmall := eventually_center_sq_div_log_lt_on_logarithmicWindow
    hε (show 0 < δ / 12 by positivity)
  filter_upwards [eventually_allowedPrimeCount_natSqrt_le_twelve_sqrt_div_log S,
      hsmall, eventually_ge_atTop 4] with X hcount hsmallX hX
  intro a ha
  have hYpos : (0 : ℝ) < Nat.sqrt X := by
    exact_mod_cast (Nat.sqrt_pos.2 (by omega : 0 < X))
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have haOne : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
  have haSq : (a : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
  calc
    (allowedPrimeCount S (Nat.sqrt X) : ℝ) *
          ((a : ℝ) / (Nat.sqrt X : ℝ)) ≤
        (12 * ((Nat.sqrt X : ℝ) / Real.log (X : ℝ))) *
          ((a : ℝ) / (Nat.sqrt X : ℝ)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 12 * (a : ℝ) / Real.log (X : ℝ) := by
      field_simp [hYpos.ne']
    _ ≤ 12 * ((a : ℝ) ^ 2 / Real.log (X : ℝ)) := by
      calc
        12 * (a : ℝ) / Real.log (X : ℝ) =
            12 * ((a : ℝ) / Real.log (X : ℝ)) := by ring
        _ ≤ 12 * ((a : ℝ) ^ 2 / Real.log (X : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right haSq hlogX.le)
            (by norm_num : (0 : ℝ) ≤ 12)
    _ < 12 * (δ / 12) := mul_lt_mul_of_pos_left (hsmallX a ha) (by norm_num)
    _ = δ := by ring

/-- The sum of actual up-star degree ratios differs uniformly by `o(1)` from
the moving PNT model throughout the logarithmic centre window. -/
theorem eventually_logarithmicWindow_actualUpLinear_sub_model_close
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        |fixedCenterActualUpLinear S (a : ℕ) X -
          fixedCenterUpLinearModel S (a : ℕ) X| < δ := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_logarithmicWindowActualUpRatio_sub_model_bound S hS hε
  have hrecipT := allowedPrimeReciprocalSum_natSqrt_div_log_tendsto_zero S
  have hrecipAbs : Tendsto
      (fun X : ℕ ↦
        |allowedPrimeReciprocalSum S (Nat.sqrt X) /
          Real.log (X : ℝ)|) atTop (𝓝 0) := by simpa using hrecipT.abs
  have hrecipSmall : ∀ᶠ X : ℕ in atTop,
      |allowedPrimeReciprocalSum S (Nat.sqrt X) /
        Real.log (X : ℝ)| < δ / (2 * K) :=
    (tendsto_order.1 hrecipAbs).2 (δ / (2 * K)) (by positivity)
  have hcountSmall := eventually_logarithmicWindow_count_mul_center_div_sqrt_lt
    S hε (show 0 < δ / (2 * K) by positivity)
  filter_upwards [hratio, hrecipSmall, hcountSmall,
      eventually_ge_atTop 4] with X hratioX hrecipX hcountX hX
  intro a ha
  let Q := (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hYpos : (0 : ℝ) < Nat.sqrt X := by
    exact_mod_cast (Nat.sqrt_pos.2 (by omega : 0 < X))
  have hrecipNonneg : 0 ≤ allowedPrimeReciprocalSum S (Nat.sqrt X) /
      Real.log (X : ℝ) := by
    apply div_nonneg
    · unfold allowedPrimeReciprocalSum
      exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (by positivity)
    · exact hlogX.le
  have hrecipSmall' : allowedPrimeReciprocalSum S (Nat.sqrt X) /
      Real.log (X : ℝ) < δ / (2 * K) := by
    rw [← abs_of_nonneg hrecipNonneg]
    exact hrecipX
  have hcountSmall' := hcountX (a : ℕ) ha
  have hsumAbs :
      ∑ q ∈ Q, |fixedCenterActualUpRatio S (a : ℕ) X q -
          fixedCenterUpRatioModel (a : ℕ) q X| ≤
        K * (allowedPrimeReciprocalSum S (Nat.sqrt X) /
            Real.log (X : ℝ) +
          (allowedPrimeCount S (Nat.sqrt X) : ℝ) *
            ((a : ℝ) / (Nat.sqrt X : ℝ))) := by
    calc
      ∑ q ∈ Q, |fixedCenterActualUpRatio S (a : ℕ) X q -
          fixedCenterUpRatioModel (a : ℕ) q X| ≤
        ∑ q ∈ Q, K *
          (1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (a : ℝ) / (Nat.sqrt X : ℝ)) := by
              apply Finset.sum_le_sum
              intro q hq
              exact hratioX a ha q hq
      _ = K * (allowedPrimeReciprocalSum S (Nat.sqrt X) /
            Real.log (X : ℝ) +
          (allowedPrimeCount S (Nat.sqrt X) : ℝ) *
            ((a : ℝ) / (Nat.sqrt X : ℝ))) := by
        have hrecipSum : (∑ q ∈ Q,
            (1 : ℝ) / ((q : ℝ) * Real.log (X : ℝ))) =
            allowedPrimeReciprocalSum S (Nat.sqrt X) /
              Real.log (X : ℝ) := by
          rw [allowedPrimeReciprocalSum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro q _hq
          rw [one_div, mul_inv_rev, div_eq_mul_inv]
          ring
        have hconstSum : (∑ _q ∈ Q, (a : ℝ) / (Nat.sqrt X : ℝ)) =
            (allowedPrimeCount S (Nat.sqrt X) : ℝ) *
              ((a : ℝ) / (Nat.sqrt X : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp only [Q, allowedPrimeCount]
        rw [show (∑ q ∈ Q, K *
            (1 / ((q : ℝ) * Real.log (X : ℝ)) +
              (a : ℝ) / (Nat.sqrt X : ℝ))) =
            K * ((∑ q ∈ Q, (1 : ℝ) / ((q : ℝ) * Real.log (X : ℝ))) +
              ∑ _q ∈ Q, (a : ℝ) / (Nat.sqrt X : ℝ)) by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]]
        rw [hrecipSum, hconstSum]
  have hmajorant : K *
      (allowedPrimeReciprocalSum S (Nat.sqrt X) / Real.log (X : ℝ) +
        (allowedPrimeCount S (Nat.sqrt X) : ℝ) *
          ((a : ℝ) / (Nat.sqrt X : ℝ))) < δ := by
    calc
      K * (_ + _) < K * (δ / (2 * K) + δ / (2 * K)) :=
        mul_lt_mul_of_pos_left (add_lt_add hrecipSmall' hcountSmall') hK
      _ = δ := by field_simp [hK.ne']; ring
  rw [fixedCenterActualUpLinear, fixedCenterUpLinearModel,
    ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans_lt (hsumAbs.trans_lt hmajorant)

/-- A coarser ratio estimate, uniform also in a moving prime label. -/
theorem exists_logarithmicWindowActualUpRatio_sub_inv_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
          |fixedCenterActualUpRatio S (a : ℕ) X q - (q : ℝ)⁻¹| ≤
            K * ((Real.log (X : ℝ))⁻¹ +
              (a : ℝ) / (Nat.sqrt X : ℝ)) := by
  obtain ⟨K₀, hK₀, hratio⟩ :=
    exists_logarithmicWindowActualUpRatio_sub_model_bound S hS hε
  let K : ℝ := K₀ + 3
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  filter_upwards [hratio, eventually_logarithmicWindow_logSqrt_gap_bounds hε,
      eventually_ge_atTop 4] with X hratioX hlogY hX
  intro a ha q hq
  have hqData := Finset.mem_filter.mp hq
  have hqPrime : q.Prime := (Nat.mem_primesLE.mp hqData.1).2
  have hqY : q ≤ Nat.sqrt X := (Nat.mem_primesLE.mp hqData.1).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogq : Real.log (q : ℝ) ≤ Real.log (Nat.sqrt X : ℝ) :=
    Real.log_le_log hqR (by exact_mod_cast hqY)
  have hgap : Real.log (X : ℝ) / 3 ≤
      fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ) :=
    (hlogY (a : ℕ) ha).2.2.trans (sub_le_sub_left hlogq _)
  have hdenPos : 0 < (q : ℝ) *
      (fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ)) :=
    mul_pos hqR (by linarith)
  have hmodelEq :
      fixedCenterUpRatioModel (a : ℕ) q X - (q : ℝ)⁻¹ =
        Real.log (q : ℝ) /
          ((q : ℝ) * (fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ))) := by
    simp only [fixedCenterUpRatioModel]
    have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
    have hden0 : fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ) ≠ 0 := by
      linarith
    field_simp [hq0, hden0]
    ring
  have hlogqNonneg : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hqPrime.one_le)
  have hlogqLe : Real.log (q : ℝ) ≤ (q : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hqR]
  have hmodelBound :
      |fixedCenterUpRatioModel (a : ℕ) q X - (q : ℝ)⁻¹| ≤
        3 * (Real.log (X : ℝ))⁻¹ := by
    rw [hmodelEq, abs_of_nonneg (div_nonneg hlogqNonneg hdenPos.le)]
    rw [div_le_iff₀ hdenPos]
    have hmul := mul_le_mul hlogqLe hgap (by positivity) hqR.le
    field_simp [hlogX.ne']
    nlinarith
  have hraw := hratioX a ha q hq
  have hqInv : (q : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast hqPrime.one_le)
  have hrecip : 1 / ((q : ℝ) * Real.log (X : ℝ)) ≤
      (Real.log (X : ℝ))⁻¹ := by
    rw [one_div, mul_inv_rev]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hqInv (inv_nonneg.mpr hlogX.le)
  calc
    |fixedCenterActualUpRatio S (a : ℕ) X q - (q : ℝ)⁻¹| ≤
        |fixedCenterActualUpRatio S (a : ℕ) X q -
          fixedCenterUpRatioModel (a : ℕ) q X| +
        |fixedCenterUpRatioModel (a : ℕ) q X - (q : ℝ)⁻¹| := abs_sub_le _ _ _
    _ ≤ K₀ * ((Real.log (X : ℝ))⁻¹ +
          (a : ℝ) / (Nat.sqrt X : ℝ)) +
        3 * (Real.log (X : ℝ))⁻¹ :=
      add_le_add (hraw.trans (mul_le_mul_of_nonneg_left
        (by simpa only [add_comm] using
          add_le_add_right hrecip ((a : ℝ) / (Nat.sqrt X : ℝ))) hK₀.le)) hmodelBound
    _ ≤ K * ((Real.log (X : ℝ))⁻¹ +
          (a : ℝ) / (Nat.sqrt X : ℝ)) := by
      dsimp [K]
      have hx : 0 ≤ (Real.log (X : ℝ))⁻¹ := inv_nonneg.mpr hlogX.le
      have hy : 0 ≤ (a : ℝ) / (Nat.sqrt X : ℝ) := by positivity
      nlinarith

end

end PrimeStar
