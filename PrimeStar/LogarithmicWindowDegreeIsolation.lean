import PrimeStar.LogarithmicWindow

/-!
# Degree isolation on the logarithmic centre window

This module turns the quantitative prime-number theorem into the uniform
degree uniqueness consumed by the ordered logarithmic-window spectral
assembly.  The deletion set and the positive window loss are fixed; the
centre varies with the ambient cutoff.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

/-- On a positive interval lying beyond `exp 2`, the PNT main term grows at
least at the reciprocal-logarithmic rate used in the adjacent-centre gap. -/
theorem pntMainReal_gap_ge
    {y x U : ℝ}
    (hy : 0 < y) (hyx : y ≤ x) (hxU : x ≤ U)
    (hlogy : 2 ≤ Real.log y) :
    (1 / (2 * Real.log U)) * (x - y) ≤
      pntMainReal x - pntMainReal y := by
  have hx : 0 < x := hy.trans_le hyx
  have hU : 0 < U := hx.trans_le hxU
  have hlogxPos : 0 < Real.log x := by
    exact (show 0 < Real.log y by linarith).trans_le (Real.log_le_log hy hyx)
  have hlogxU : Real.log x ≤ Real.log U := Real.log_le_log hx hxU
  have hlogGap : Real.log x - Real.log y ≤ (x - y) / y := by
    calc
      Real.log x - Real.log y = Real.log (x / y) := by
        rw [Real.log_div hx.ne' hy.ne']
      _ ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
      _ = (x - y) / y := by field_simp [hy.ne']
  have hyGap : y * (Real.log x - Real.log y) ≤ x - y := by
    have := mul_le_mul_of_nonneg_left hlogGap hy.le
    field_simp [hy.ne'] at this
    simpa [mul_sub] using this
  have hnum : (Real.log y / 2) * (x - y) ≤
      Real.log y * x - Real.log x * y := by
    nlinarith [hyGap, hlogy, hyx]
  have hfirst : (x - y) / (2 * Real.log U) ≤
      (x - y) / (2 * Real.log x) := by
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hyx)
      (by positivity) (by nlinarith)
  calc
    (1 / (2 * Real.log U)) * (x - y) =
        (x - y) / (2 * Real.log U) := by ring
    _ ≤ (x - y) / (2 * Real.log x) := hfirst
    _ = ((Real.log y / 2) * (x - y)) /
        (Real.log x * Real.log y) := by
          field_simp [hlogxPos.ne', (show Real.log y ≠ 0 by linarith)]
    _ ≤ (Real.log y * x - Real.log x * y) /
        (Real.log x * Real.log y) := by
          exact div_le_div_of_nonneg_right hnum (mul_nonneg hlogxPos.le (by linarith))
    _ = pntMainReal x - pntMainReal y := by
      unfold pntMainReal
      field_simp [hlogxPos.ne', (show Real.log y ≠ 0 by linarith)]

/-- Any fixed multiple of `a + 1` is eventually smaller than `log X`,
uniformly on the logarithmic centre window. -/
theorem eventually_mul_center_succ_lt_log_on_logarithmicWindow
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        K * ((a : ℝ) + 1) < Real.log (X : ℝ) := by
  let δ : ℝ := 1 / (4 * (K + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hcenter := eventually_center_sq_div_log_lt_on_logarithmicWindow hε hδ
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ))⁻¹) atTop (𝓝 0) :=
    hlogTop.inv_tendsto_atTop
  have hinvSmall : ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ))⁻¹ < δ :=
    (tendsto_order.1 hinv).2 δ hδ
  filter_upwards [hcenter, hinvSmall, hlogTop.eventually_gt_atTop 0]
      with X hcenterX hinvX hlogX
  intro a ha
  have haOne : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
  have haa : (a : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
  have haDiv : (a : ℝ) / Real.log (X : ℝ) < δ := by
    exact (div_le_div_of_nonneg_right haa hlogX.le).trans_lt (hcenterX a ha)
  have honeDiv : 1 / Real.log (X : ℝ) < δ := by
    simpa [one_div] using hinvX
  have hratio : ((a : ℝ) + 1) / Real.log (X : ℝ) < 2 * δ := by
    rw [add_div]
    linarith
  have hcoef : K * (2 * δ) < 1 := by
    dsimp [δ]
    have hden : 0 < K + 1 := by positivity
    field_simp [hden.ne']
    nlinarith
  have : K * (((a : ℝ) + 1) / Real.log (X : ℝ)) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hratio.le hK) hcoef
  have hdiv : K * ((a : ℝ) + 1) / Real.log (X : ℝ) < 1 := by
    simpa [mul_div_assoc] using this
  exact (div_lt_one hlogX).mp hdiv

/-- A logarithmic-window centre has one full integer of room below the
square-root cutoff. -/
theorem eventually_center_succ_le_natSqrt_on_logarithmicWindow
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a → a + 1 ≤ Nat.sqrt X := by
  have hcenter := eventually_center_sq_div_log_lt_on_logarithmicWindow
    (ε := ε) (δ := 1 / 4) hε (by norm_num)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfourLog : ∀ᶠ X : ℕ in atTop,
      4 * Real.log (X : ℝ) ≤ (X : ℝ) := by
    have h := (Real.isLittleO_log_id_atTop.comp_tendsto
      tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [h, eventually_ge_atTop 2] with X hX hXtwo
    simp only [Function.comp_apply, id_eq, Real.norm_eq_abs] at hX
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X from by omega))),
      abs_of_nonneg (by positivity)] at hX
    nlinarith
  filter_upwards [hcenter, hfourLog, hlogTop.eventually_gt_atTop 0]
      with X hcenterX hfourX hlogX
  intro a ha
  have haOne : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
  have haSq : (a : ℝ) ^ 2 < Real.log (X : ℝ) / 4 := by
    have := hcenterX a ha
    rw [div_lt_iff₀ hlogX] at this
    nlinarith
  have hsuccSq : ((a + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (a : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have hnat : (a + 1) ^ 2 ≤ X := by
    have hreal : ((a + 1 : ℕ) : ℝ) ^ 2 ≤ (X : ℝ) := by
      exact hsuccSq.trans (le_of_lt (by nlinarith [haSq, hfourX]))
    exact_mod_cast hreal
  exact Nat.le_sqrt'.2 hnat

/-- Uniform local PNT upper bound at a moving logarithmic-window
denominator.  The coarse constant `12` is sufficient for converting the
adjacent count gap into a square-root star-frequency gap. -/
theorem eventually_logarithmicWindow_allowedPrimeCount_div_le_twelve_main
    (S : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        (allowedPrimeCount S (X / a) : ℝ) ≤
          12 * ((X : ℝ) / ((a : ℝ) * Real.log (X : ℝ))) := by
  obtain ⟨N₀, hcount⟩ := eventually_atTop.1
    (eventually_allowedPrimeCount_nat_le_four_main S)
  have hsqrtTop : Tendsto (fun X : ℕ ↦ (Nat.sqrt X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop
  have hratio : ∀ᶠ X : ℕ in atTop,
      (1 / 3 : ℝ) <
        Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) :=
    (log_natSqrt_div_log_tendsto_half.eventually
      (isOpen_Ioi.mem_nhds (by norm_num : (1 / 3 : ℝ) < 1 / 2)))
  filter_upwards [eventually_center_le_natSqrt_on_logarithmicWindow hε,
      hsqrtTop.eventually_ge_atTop N₀, hratio, eventually_ge_atTop 4]
      with X hcenter hYlarge hratioX hX
  intro a ha
  have haPos : 0 < a := ha.1
  have haR : (0 : ℝ) < a := by exact_mod_cast haPos
  have hLpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have haY : a ≤ Nat.sqrt X := hcenter a ha
  have hYX : Nat.sqrt X ≤ X / a := by
    apply (Nat.le_div_iff_mul_le haPos).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hYlargeNat : N₀ ≤ Nat.sqrt X := by
    exact_mod_cast hYlarge
  have hcountXa := hcount (X / a) (hYlargeNat.trans hYX)
  have hlogLower : Real.log (X : ℝ) / 3 ≤ Real.log (X / a : ℕ) := by
    have hsqrtPos : (0 : ℝ) < Nat.sqrt X := by
      exact_mod_cast (show 0 < Nat.sqrt X by omega)
    have hsqrtLog : Real.log (X : ℝ) / 3 <
        Real.log (Nat.sqrt X : ℝ) := by
      rw [lt_div_iff₀ hLpos] at hratioX
      linarith
    exact hsqrtLog.le.trans
      (Real.log_le_log hsqrtPos (by exact_mod_cast hYX))
  have hlogNPos : 0 < Real.log (X / a : ℕ) :=
    lt_of_lt_of_le (by linarith : 0 < Real.log (X : ℝ) / 3) hlogLower
  have hcastDiv : ((X / a : ℕ) : ℝ) ≤ (X : ℝ) / (a : ℝ) :=
    Nat.cast_div_le
  calc
    (allowedPrimeCount S (X / a) : ℝ) ≤
        4 * (((X / a : ℕ) : ℝ) / Real.log (X / a : ℕ)) := hcountXa
    _ ≤ 4 * (((X : ℝ) / (a : ℝ)) / Real.log (X / a : ℕ)) := by
      gcongr
    _ ≤ 4 * (((X : ℝ) / (a : ℝ)) /
        (Real.log (X : ℝ) / 3)) := by
      gcongr
    _ = 12 * ((X : ℝ) / ((a : ℝ) * Real.log (X : ℝ))) := by
      field_simp [haR.ne', hLpos.ne']
      ring

/-- Quantitative PNT gives a uniform lower bound for every adjacent
denominator interval seen by a logarithmic-window centre.  Finite prime
deletion cancels because both endpoints eventually lie beyond the deleted
set. -/
theorem eventually_logarithmicWindow_allowedPrimeCount_adjacent_gap_ge
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        (X : ℝ) /
              (4 * (a : ℝ) * ((a + 1 : ℕ) : ℝ) * Real.log (X : ℝ)) ≤
          (allowedPrimeCount S (X / a) : ℝ) -
            (allowedPrimeCount S (X / (a + 1)) : ℝ) := by
  obtain ⟨C, hC, hPNT⟩ := exists_realPrimeCounting_error_bound
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hPNT
  have hsqrtTop : Tendsto (fun X : ℕ ↦ (Nat.sqrt X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop
  have hratio : ∀ᶠ X : ℕ in atTop,
      (1 / 3 : ℝ) <
        Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) :=
    (log_natSqrt_div_log_tendsto_half.eventually
      (isOpen_Ioi.mem_nhds (by norm_num : (1 / 3 : ℝ) < 1 / 2)))
  have hlinear := eventually_mul_center_succ_lt_log_on_logarithmicWindow
    hε (show 0 ≤ 72 * C by positivity)
  filter_upwards [eventually_center_succ_le_natSqrt_on_logarithmicWindow hε,
      eventually_finset_le_nat_sqrt S,
      hsqrtTop.eventually_ge_atTop (max x₀ (Real.exp 2)), hratio, hlinear,
      eventually_ge_atTop 4]
      with X hsucc hSX hYlarge hratioX hlinearX hX
  intro a ha
  let L : ℝ := Real.log (X : ℝ)
  let x : ℝ := (X : ℝ) / (a : ℝ)
  let y : ℝ := (X : ℝ) / ((a + 1 : ℕ) : ℝ)
  have haPos : 0 < a := ha.1
  have haR : (0 : ℝ) < a := by exact_mod_cast haPos
  have ha1R : (0 : ℝ) < (a + 1 : ℕ) := by positivity
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have haY : a + 1 ≤ Nat.sqrt X := hsucc a ha
  have hYX : Nat.sqrt X ≤ X / (a + 1) := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos a)).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hYy : (Nat.sqrt X : ℝ) ≤ y := by
    dsimp [y]
    rw [le_div_iff₀ ha1R]
    exact_mod_cast (show Nat.sqrt X * (a + 1) ≤ X from
      (Nat.mul_le_mul_left (Nat.sqrt X) haY).trans (Nat.sqrt_le X))
  have hyLarge : x₀ ≤ y := (le_max_left _ _).trans hYlarge |>.trans hYy
  have hxLarge : x₀ ≤ x := by
    have hyx : y ≤ x := by
      dsimp [x, y]
      exact div_le_div_of_nonneg_left hXpos.le haR
        (by exact_mod_cast (Nat.le_succ a))
    exact hyLarge.trans hyx
  have hlogYtwo : 2 ≤ Real.log y := by
    have hexpY : Real.exp 2 ≤ y :=
      (le_max_right _ _).trans hYlarge |>.trans hYy
    have hlogMon := Real.log_le_log (Real.exp_pos 2) hexpY
    simpa using hlogMon
  have hexpY : Real.exp 2 ≤ y :=
    (le_max_right _ _).trans hYlarge |>.trans hYy
  have hyPos : 0 < y := (Real.exp_pos 2).trans_le hexpY
  have hyx : y ≤ x := by
    dsimp [x, y]
    exact div_le_div_of_nonneg_left hXpos.le haR
      (by exact_mod_cast (Nat.le_succ a))
  have hxLeX : x ≤ (X : ℝ) := by
    dsimp [x]
    exact (div_le_iff₀ haR).2 (by nlinarith [show (1 : ℝ) ≤ a by exact_mod_cast haPos])
  have hmain := pntMainReal_gap_ge hyPos hyx hxLeX hlogYtwo
  have hlogyLower : L / 3 ≤ Real.log y := by
    have hlogSqrt : L / 3 < Real.log (Nat.sqrt X : ℝ) := by
      have := hratioX
      rw [lt_div_iff₀ hLpos] at this
      dsimp [L] at this ⊢
      linarith
    exact hlogSqrt.le.trans (Real.log_le_log
      (lt_of_lt_of_le (Real.exp_pos 2) ((le_max_right _ _).trans hYlarge)) hYy)
  have hlogxLower : L / 3 ≤ Real.log x :=
    hlogyLower.trans (Real.log_le_log hyPos hyx)
  have hlogyPos : 0 < Real.log y := by linarith
  have hlogxPos : 0 < Real.log x := hlogyPos.trans_le
    (Real.log_le_log hyPos hyx)
  have hxBound : x / Real.log x ^ 2 ≤
      9 * ((X : ℝ) / ((a : ℝ) * L ^ 2)) := by
    have hxNum : x ≤ (X : ℝ) / (a : ℝ) := by rfl
    have hden : (L / 3) ^ 2 ≤ Real.log x ^ 2 :=
      (sq_le_sq₀ (by positivity) hlogxPos.le).2 hlogxLower
    calc
      x / Real.log x ^ 2 ≤ ((X : ℝ) / (a : ℝ)) / Real.log x ^ 2 := by gcongr
      _ ≤ ((X : ℝ) / (a : ℝ)) / (L / 3) ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 9 * ((X : ℝ) / ((a : ℝ) * L ^ 2)) := by
        field_simp [haR.ne', hLpos.ne']
        ring
  have hyBound : y / Real.log y ^ 2 ≤
      9 * ((X : ℝ) / ((a : ℝ) * L ^ 2)) := by
    have hden : (L / 3) ^ 2 ≤ Real.log y ^ 2 :=
      (sq_le_sq₀ (by positivity) hlogyPos.le).2 hlogyLower
    calc
      y / Real.log y ^ 2 ≤ x / Real.log y ^ 2 := by gcongr
      _ ≤ ((X : ℝ) / (a : ℝ)) / Real.log y ^ 2 := by gcongr
      _ ≤ ((X : ℝ) / (a : ℝ)) / (L / 3) ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 9 * ((X : ℝ) / ((a : ℝ) * L ^ 2)) := by
        field_simp [haR.ne', hLpos.ne']
        ring
  have herrx := hx₀ x hxLarge
  have herry := hx₀ y hyLarge
  have herrx' : |(Nat.primeCounting (X / a) : ℝ) - pntMainReal x| ≤
      9 * C * ((X : ℝ) / ((a : ℝ) * L ^ 2)) := by
    calc
      |(Nat.primeCounting (X / a) : ℝ) - pntMainReal x| ≤
          C * x / Real.log x ^ 2 := by simpa [x, Nat.floor_div_eq_div] using herrx
      _ = C * (x / Real.log x ^ 2) := by ring
      _ ≤ C * (9 * ((X : ℝ) / ((a : ℝ) * L ^ 2))) := by gcongr
      _ = 9 * C * ((X : ℝ) / ((a : ℝ) * L ^ 2)) := by ring
  have herry' : |(Nat.primeCounting (X / (a + 1)) : ℝ) - pntMainReal y| ≤
      9 * C * ((X : ℝ) / ((a : ℝ) * L ^ 2)) := by
    have hfloorY : ⌊y⌋₊ = X / (a + 1) := by
      dsimp [y]
      simpa using (Nat.floor_div_eq_div (K := ℝ) X (a + 1))
    calc
      |(Nat.primeCounting (X / (a + 1)) : ℝ) - pntMainReal y| ≤
          C * y / Real.log y ^ 2 := by simpa [hfloorY] using herry
      _ = C * (y / Real.log y ^ 2) := by ring
      _ ≤ C * (9 * ((X : ℝ) / ((a : ℝ) * L ^ 2))) := by gcongr
      _ = 9 * C * ((X : ℝ) / ((a : ℝ) * L ^ 2)) := by ring
  have hcost :
      18 * C * ((X : ℝ) / ((a : ℝ) * L ^ 2)) <
        (1 / (4 * L)) * (x - y) := by
    have hlinearNow : 72 * C * ((a : ℝ) + 1) < L := hlinearX a ha
    have hxyEq : x - y =
        (X : ℝ) / ((a : ℝ) * ((a : ℝ) + 1)) := by
      dsimp [x, y]
      push_cast
      field_simp [haR.ne']
      ring
    rw [hxyEq]
    have ha1pos : 0 < (a : ℝ) + 1 := by positivity
    field_simp [haR.ne', ha1pos.ne', hLpos.ne']
    nlinarith
  have hprimeGap :
      (1 / (4 * L)) * (x - y) ≤
        (Nat.primeCounting (X / a) : ℝ) -
          (Nat.primeCounting (X / (a + 1)) : ℝ) := by
    have hmain' : (1 / (2 * L)) * (x - y) ≤
        pntMainReal x - pntMainReal y := by simpa [L] using hmain
    have hxLower := neg_le_of_abs_le herrx'
    have hyUpper := le_of_abs_le herry'
    have hhalfEq :
        (1 / (2 * L)) * (x - y) =
          2 * ((1 / (4 * L)) * (x - y)) := by
      field_simp [hLpos.ne']
      ring
    rw [hhalfEq] at hmain'
    linarith
  have hSN : ∀ p ∈ S, p ≤ X / (a + 1) := fun p hp ↦
    (hSX p hp).trans hYX
  have hdelete := allowedPrimeCount_fixedDenominator_gap_eq
    hS haPos (Nat.lt_succ_self a) hSN
  have hallowedR :
      (1 / (4 * L)) * (x - y) ≤
        (allowedPrimeCount S (X / a) : ℝ) -
          (allowedPrimeCount S (X / (a + 1)) : ℝ) := by
    rw [hdelete]
    exact hprimeGap
  have hxyEq : x - y =
      (X : ℝ) / ((a : ℝ) * ((a : ℝ) + 1)) := by
    dsimp [x, y]
    push_cast
    field_simp [haR.ne']
    ring
  calc
    (X : ℝ) /
          (4 * (a : ℝ) * ((a + 1 : ℕ) : ℝ) * Real.log (X : ℝ)) =
        (1 / (4 * L)) * (x - y) := by
          rw [hxyEq]
          dsimp [L]
          push_cast
          field_simp [haR.ne', hLpos.ne']
    _ ≤ _ := hallowedR

/-- In particular, every adjacent denominator interval in the logarithmic
window contains an allowed prime. -/
theorem eventually_logarithmicWindow_allowedPrimeCount_adjacent_lt
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        allowedPrimeCount S (X / (a + 1)) < allowedPrimeCount S (X / a) := by
  filter_upwards [eventually_logarithmicWindow_allowedPrimeCount_adjacent_gap_ge
      S hS hε, eventually_ge_atTop 4] with X hgap hX
  intro a ha
  have haPos : (0 : ℝ) < a := by exact_mod_cast ha.1
  have ha1Pos : (0 : ℝ) < (a + 1 : ℕ) := by positivity
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hleft : 0 < (X : ℝ) /
      (4 * (a : ℝ) * ((a + 1 : ℕ) : ℝ) * Real.log (X : ℝ)) := by
    positivity
  have hcast :
      (allowedPrimeCount S (X / (a + 1)) : ℝ) <
        (allowedPrimeCount S (X / a) : ℝ) := by
    linarith [hgap a ha]
  exact_mod_cast hcast

/-- Uniform uniqueness of every nonempty large-prime star degree whose centre
lies in the logarithmic window. -/
theorem eventually_logarithmicWindow_largePrimeStarDegree_unique
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ b : Vertex S X, (b : ℕ) ≤ Nat.sqrt X →
          0 < largePrimeStarDegree S X (Nat.sqrt X) b →
          largePrimeStarDegree S X (Nat.sqrt X) b =
            largePrimeStarDegree S X (Nat.sqrt X) a → b = a := by
  filter_upwards [eventually_logarithmicWindow_allowedPrimeCount_adjacent_lt
      S hS hε,
    eventually_center_succ_le_natSqrt_on_logarithmicWindow hε]
      with X hadj hsucc
  intro a ha b hbY _hbd hdeg
  have haY : (a : ℕ) ≤ Nat.sqrt X := (Nat.le_succ _).trans (hsucc (a : ℕ) ha)
  have hYX (v : Vertex S X) (hv : (v : ℕ) ≤ Nat.sqrt X) :
      Nat.sqrt X ≤ X / (v : ℕ) := by
    apply (Nat.le_div_iff_mul_le (Vertex.coe_pos v)).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) hv).trans (Nat.sqrt_le X)
  have hdiff := largePrimeStarDegree_sub_eq_allowedPrimeCount_gap
    hS a b haY hbY (hYX a haY) (hYX b hbY)
  have hcountEqR :
      (allowedPrimeCount S (X / (a : ℕ)) : ℝ) =
        (allowedPrimeCount S (X / (b : ℕ)) : ℝ) := by
    rw [hdeg] at hdiff
    linarith
  have hcountEq :
      allowedPrimeCount S (X / (a : ℕ)) =
        allowedPrimeCount S (X / (b : ℕ)) := by
    exact_mod_cast hcountEqR
  apply Subtype.ext
  apply Fin.ext
  by_contra hab
  have habNat : (a : ℕ) ≠ (b : ℕ) := by
    intro h
    exact hab h.symm
  rcases lt_or_gt_of_ne habNat with hablt | habgt
  · have hstrict := hadj (a : ℕ) ha
    have hsuccLe : (a : ℕ) + 1 ≤ (b : ℕ) := by omega
    have hdiv : X / (b : ℕ) ≤ X / ((a : ℕ) + 1) :=
      Nat.div_le_div_left hsuccLe (Nat.succ_pos (a : ℕ))
    have hmono := allowedPrimeCount_mono (S := S) hdiv
    rw [← hcountEq] at hmono
    omega
  · have hbWindow : InLogarithmicCenterWindow ε X (b : ℕ) := by
      refine ⟨Vertex.coe_pos b, ?_⟩
      exact (by exact_mod_cast habgt.le : ((b : ℕ) : ℝ) ≤ (a : ℕ)).trans ha.2
    have hstrict := hadj (b : ℕ) hbWindow
    have hsuccLe : (b : ℕ) + 1 ≤ (a : ℕ) := by omega
    have hdiv : X / (a : ℕ) ≤ X / ((b : ℕ) + 1) :=
      Nat.div_le_div_left hsuccLe (Nat.succ_pos (b : ℕ))
    have hmono := allowedPrimeCount_mono (S := S) hdiv
    rw [hcountEq] at hmono
    omega

end

end PrimeStar
