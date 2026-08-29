import PrimeStar.LogarithmicWindowFeshbachRemainder
import PrimeStar.FixedCenterConstantLayer

/-!
# Arithmetic evaluation on the logarithmic centre window

This module proves the arithmetic input still missing from Theorem 9.6.  The
centre may vary with `X`, subject to
`a ≤ (log X)^(1/2-ε)`.  All estimates are therefore uniform in the centre;
none is obtained by diagonalizing the fixed-centre limit.
-/

namespace PrimeStar

open Filter Topology Asymptotics
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2000000

/-- Uniformly on the logarithmic centre window, the logarithm of the centre
is negligible compared with `log X`. -/
theorem eventually_logarithmicWindow_log_center_le_twelfth
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        Real.log (a : ℝ) ≤ Real.log (X : ℝ) / 12 := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmallReal :=
    Real.isLittleO_log_id_atTop.bound
      (by norm_num : (0 : ℝ) < 1 / 12)
  have hsmall : ∀ᶠ X : ℕ in atTop,
      Real.log (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) / 12 := by
    filter_upwards [hlogTop.eventually hsmallReal,
      hlogTop.eventually_gt_atTop 1] with X hX hL
    have hloglog : 0 ≤ Real.log (Real.log (X : ℝ)) :=
      Real.log_nonneg hL.le
    have hlog : 0 ≤ Real.log (X : ℝ) := le_trans (by norm_num) hL.le
    have h := hX
    simp only [Real.norm_eq_abs, abs_of_nonneg hloglog,
      abs_of_nonneg hlog, id] at h
    convert h using 1
    all_goals ring
  filter_upwards [hsmall, hlogTop.eventually_ge_atTop 1] with X hsmallX hL
  intro a ha
  have haPos : (0 : ℝ) < a := by exact_mod_cast ha.1
  have hpow : Real.log (X : ℝ) ^ (1 / 2 - ε) ≤
      Real.log (X : ℝ) := by
    have hexp : 1 / 2 - ε ≤ (1 : ℝ) := by linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hL hexp
  have haL : (a : ℝ) ≤ Real.log (X : ℝ) := ha.2.trans hpow
  have hloga : Real.log (a : ℝ) ≤ Real.log (Real.log (X : ℝ)) :=
    Real.log_le_log haPos haL
  exact hloga.trans hsmallX

/-- The moving logarithmic scale is uniformly comparable with `log X` on the
whole logarithmic centre window. -/
theorem eventually_logarithmicWindow_logScale_between
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        11 * Real.log (X : ℝ) / 12 ≤ fixedCenterLogScale a X ∧
          fixedCenterLogScale a X ≤ Real.log (X : ℝ) := by
  filter_upwards [eventually_logarithmicWindow_log_center_le_twelfth hε]
      with X hcenter
  intro a ha
  have haLogNonneg : 0 ≤ Real.log (a : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ha.1)
  have hsmall := hcenter a ha
  rw [fixedCenterLogScale]
  constructor <;> linarith

/-- The integer square-root endpoint and the moving centre scale leave a
uniform logarithmic gap. -/
theorem eventually_logarithmicWindow_logSqrt_gap_bounds
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        Real.log (X : ℝ) / 3 ≤ Real.log (Nat.sqrt X : ℝ) ∧
          Real.log (Nat.sqrt X : ℝ) ≤ 7 * Real.log (X : ℝ) / 12 ∧
          Real.log (X : ℝ) / 3 ≤
            fixedCenterLogScale a X - Real.log (Nat.sqrt X : ℝ) := by
  have hsqrtStrict : ∀ᶠ X : ℕ in atTop,
      (1 / 3 : ℝ) <
          Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) ∧
        Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) < 7 / 12 :=
    log_natSqrt_div_log_tendsto_half.eventually
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hsqrt : ∀ᶠ X : ℕ in atTop,
      (1 / 3 : ℝ) ≤
          Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) ∧
        Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) ≤ 7 / 12 :=
    hsqrtStrict.mono fun _ h ↦ ⟨h.1.le, h.2.le⟩
  filter_upwards [hsqrt, eventually_logarithmicWindow_logScale_between hε,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
      with X hsqrtX hscale hlogX
  intro a ha
  have hlogX' : 0 < Real.log (X : ℝ) := by
    simpa [Function.comp_apply] using hlogX
  have hsqrtLower := (le_div_iff₀ hlogX').mp hsqrtX.1
  have hsqrtUpper := (div_le_iff₀ hlogX').mp hsqrtX.2
  have hscaleX := hscale a ha
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The logarithm of a moving centre, divided by `log X`, tends uniformly to
zero on the logarithmic window. -/
theorem eventually_logarithmicWindow_log_center_div_log_lt
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        Real.log (a : ℝ) / Real.log (X : ℝ) < δ := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun X : ℕ ↦ Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogTop
  have hsmall : ∀ᶠ X : ℕ in atTop,
      Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) < δ :=
    (tendsto_order.1 hratio).2 δ hδ
  filter_upwards [hsmall, hlogTop.eventually_gt_atTop 1] with X hsmallX hL
  intro a ha
  have haPos : (0 : ℝ) < a := by exact_mod_cast ha.1
  have hpow : Real.log (X : ℝ) ^ (1 / 2 - ε) ≤
      Real.log (X : ℝ) := by
    have hexp : 1 / 2 - ε ≤ (1 : ℝ) := by linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hL.le hexp
  have haL : (a : ℝ) ≤ Real.log (X : ℝ) := ha.2.trans hpow
  have hloga : Real.log (a : ℝ) ≤ Real.log (Real.log (X : ℝ)) :=
    Real.log_le_log haPos haL
  exact (div_le_div_of_nonneg_right hloga (le_trans (by norm_num) hL.le)).trans_lt hsmallX

/-- The explicit endpoint ratio in Abel summation tends uniformly to `2` on
the logarithmic centre window. -/
theorem eventually_logarithmicWindow_endpointRatio_close
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        |(fixedCenterLogScale a X - Real.log 2) /
            (fixedCenterLogScale a X - Real.log (Nat.sqrt X : ℝ)) - 2| < δ := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto
      (fun X : ℕ ↦
        |Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) - 1 / 2|)
      atTop (𝓝 0) := by
    simpa using (log_natSqrt_div_log_tendsto_half.sub_const (1 / 2)).abs
  have htwo : Tendsto (fun X : ℕ ↦ Real.log 2 / Real.log (X : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlogTop
  have hsqrtSmall : ∀ᶠ X : ℕ in atTop,
      |Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) - 1 / 2| < δ / 12 :=
    (tendsto_order.1 hsqrt).2 (δ / 12) (by positivity)
  have hcenterSmall := eventually_logarithmicWindow_log_center_div_log_lt
    hε (show 0 < δ / 12 by positivity)
  have htwoSmall : ∀ᶠ X : ℕ in atTop,
      Real.log 2 / Real.log (X : ℝ) < δ / 12 :=
    (tendsto_order.1 htwo).2 (δ / 12) (by positivity)
  filter_upwards [hsqrtSmall, hcenterSmall, htwoSmall,
      eventually_logarithmicWindow_logSqrt_gap_bounds hε,
      hlogTop.eventually_gt_atTop 1] with X hsqrtX hcenterX htwoX hgap hL
  intro a ha
  let L : ℝ := Real.log (X : ℝ)
  let U : ℝ := fixedCenterLogScale a X
  let Ylog : ℝ := Real.log (Nat.sqrt X : ℝ)
  have hden : 0 < U - Ylog := by
    dsimp [U, Ylog, L]
    linarith [hgap a ha |>.2.2]
  have hcenter := hcenterX a ha
  have hcenterNonneg : 0 ≤ Real.log (a : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ha.1)
  have hcenterAbs : |Real.log (a : ℝ) / L| < δ / 12 := by
    rw [abs_of_nonneg (div_nonneg hcenterNonneg (by dsimp [L]; linarith))]
    simpa [L] using hcenter
  have htwoAbs : |Real.log 2 / L| < δ / 12 := by
    rw [abs_of_nonneg (div_nonneg (Real.log_nonneg (by norm_num))
      (by dsimp [L]; linarith))]
    simpa [L] using htwoX
  have hnumNorm :
      |(2 * Ylog - U - Real.log 2) / L| < δ / 3 := by
    have hrewrite : (2 * Ylog - U - Real.log 2) / L =
        2 * (Ylog / L - 1 / 2) + Real.log (a : ℝ) / L - Real.log 2 / L := by
      dsimp [U, Ylog, L]
      rw [fixedCenterLogScale]
      field_simp [ne_of_gt hL]
      ring
    rw [hrewrite]
    calc
      |2 * (Ylog / L - 1 / 2) + Real.log (a : ℝ) / L - Real.log 2 / L| ≤
          2 * |Ylog / L - 1 / 2| + |Real.log (a : ℝ) / L| +
            |Real.log 2 / L| := by
              calc
                |_ - _| ≤ |2 * (Ylog / L - 1 / 2) + Real.log (a : ℝ) / L| +
                    |Real.log 2 / L| := abs_sub _ _
                _ ≤ (|2 * (Ylog / L - 1 / 2)| +
                      |Real.log (a : ℝ) / L|) + |Real.log 2 / L| := by
                        gcongr
                        exact abs_add_le _ _
                _ = 2 * |Ylog / L - 1 / 2| + |Real.log (a : ℝ) / L| +
                    |Real.log 2 / L| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
      _ < 2 * (δ / 12) + δ / 12 + δ / 12 := by
        exact add_lt_add (add_lt_add (mul_lt_mul_of_pos_left hsqrtX (by norm_num))
          hcenterAbs) htwoAbs
      _ = δ / 3 := by ring
  have hnum : |2 * Ylog - U - Real.log 2| < δ * (L / 3) := by
    have hL0 : 0 < L := by dsimp [L]; linarith
    have hmul := mul_lt_mul_of_pos_right hnumNorm hL0
    rw [abs_div, abs_of_pos hL0, div_mul_cancel₀ _ hL0.ne'] at hmul
    nlinarith
  have hgapLower : L / 3 ≤ U - Ylog := by
    dsimp [U, Ylog, L]
    exact hgap a ha |>.2.2
  have hratio :
      |(U - Real.log 2) / (U - Ylog) - 2| =
        |2 * Ylog - U - Real.log 2| / (U - Ylog) := by
    rw [show (U - Real.log 2) / (U - Ylog) - 2 =
        (2 * Ylog - U - Real.log 2) / (U - Ylog) by
      field_simp [hden.ne']
      ring]
    rw [abs_div, abs_of_pos hden]
  rw [hratio]
  apply (div_lt_iff₀ hden).2
  exact hnum.trans_le (mul_le_mul_of_nonneg_left hgapLower hδ.le)

/-- The logarithmic prime increment keeps its `log 2` limit uniformly when
the centre moves in the logarithmic window. -/
theorem eventually_logarithmicWindow_allowedPrimeLogIncrement_close
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        |allowedPrimeLogIncrement S (fixedCenterLogScale a X) (Nat.sqrt X) -
          Real.log 2| < δ := by
  let C : ℝ := 2 * (Real.log 4 + 4) + Real.log 2
  let D : ℝ := ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    apply Finset.sum_nonneg
    intro p hp
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_le
    positivity
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hboundT : Tendsto (fun X : ℕ ↦ 3 * C / Real.log (X : ℝ))
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.div_atTop hlogTop).const_mul 3 using 1 <;> ring
  have hboundSmall : ∀ᶠ X : ℕ in atTop,
      3 * C / Real.log (X : ℝ) < δ / 4 :=
    (tendsto_order.1 hboundT).2 (δ / 4) (by positivity)
  have hdeletedT : Tendsto (fun X : ℕ ↦ 3 * D / Real.log (X : ℝ))
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.div_atTop hlogTop).const_mul 3 using 1 <;> ring
  have hdeletedSmall : ∀ᶠ X : ℕ in atTop,
      3 * D / Real.log (X : ℝ) < δ / 4 :=
    (tendsto_order.1 hdeletedT).2 (δ / 4) (by positivity)
  have hlogTarget : {x : ℝ | |Real.log x - Real.log 2| < δ / 4} ∈ 𝓝 (2 : ℝ) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ |Real.log x - Real.log 2|) 2 :=
      ((Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).sub
        continuousAt_const).abs
    exact hcont (Iio_mem_nhds (by simp; positivity))
  rcases Metric.mem_nhds_iff.mp hlogTarget with ⟨η, hη, hηsub⟩
  have hendpoint := eventually_logarithmicWindow_endpointRatio_close hε hη
  have hY : ∀ᶠ X : ℕ in atTop, 2 ≤ Nat.sqrt X := by
    filter_upwards [tendsto_natSqrt_atTop.eventually_ge_atTop 2] with X hX
    exact hX
  filter_upwards [hboundSmall, hdeletedSmall, hendpoint,
      eventually_logarithmicWindow_logSqrt_gap_bounds hε,
      eventually_finset_le_nat_sqrt S, hY,
      hlogTop.eventually_gt_atTop 1] with
      X hboundX hdeletedX hendpointX hgap hSY hY2 hL
  intro a ha
  let L : ℝ := Real.log (X : ℝ)
  let U : ℝ := fixedCenterLogScale a X
  let Ylog : ℝ := Real.log (Nat.sqrt X : ℝ)
  let R : ℝ := (U - Real.log 2) / (U - Ylog)
  have hgapX := hgap a ha
  have hden : 0 < U - Ylog := by dsimp [U, Ylog, L]; linarith [hgapX.2.2]
  have hlogApprox : |Real.log R - Real.log 2| < δ / 4 := by
    apply hηsub
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [R, U, Ylog] using hendpointX a ha
  have hprimeApprox :
      |primeLogIncrement U (Nat.sqrt X) - Real.log R| < δ / 4 := by
    have hraw := abs_primeLogIncrement_sub_logRatio_le hY2 (sub_pos.mp hden)
    have hbound : C / (U - Ylog) ≤ 3 * C / L := by
      have hLpos : 0 < L := by dsimp [L]; linarith
      have hgapLower : L / 3 ≤ U - Ylog := by
        simpa [L, U, Ylog] using hgapX.2.2
      rw [div_le_div_iff₀ hden hLpos]
      nlinarith [hC.le, hgapLower]
    exact hraw.trans_lt (hbound.trans_lt (by simpa [C, L] using hboundX))
  have hdeleted :
      |∑ p ∈ S, Real.log (p : ℝ) /
          ((p : ℝ) * (U - Real.log (p : ℝ)))| < δ / 4 := by
    have hterm : ∀ p ∈ S,
        0 ≤ Real.log (p : ℝ) /
          ((p : ℝ) * (U - Real.log (p : ℝ))) ∧
        Real.log (p : ℝ) /
            ((p : ℝ) * (U - Real.log (p : ℝ))) ≤
          (3 / L) * (Real.log (p : ℝ) / (p : ℝ)) := by
      intro p hp
      have hpPrime := hS p hp
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hpY : p ≤ Nat.sqrt X := hSY p hp
      have hlogp : Real.log (p : ℝ) ≤ Ylog := by
        exact Real.log_le_log hpPos (by exact_mod_cast hpY)
      have hlocalGap : L / 3 ≤ U - Real.log (p : ℝ) :=
        hgapX.2.2.trans (sub_le_sub_left hlogp U)
      have hlocalPos : 0 < U - Real.log (p : ℝ) :=
        lt_of_lt_of_le (by positivity : 0 < L / 3) hlocalGap
      have hlogpNonneg : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
      constructor
      · positivity
      · rw [div_le_iff₀ (mul_pos hpPos hlocalPos)]
        have hLpos : 0 < L := by dsimp [L]; linarith
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
        field_simp [hpPos.ne', hLpos.ne']
        nlinarith
    have hsumNonneg : 0 ≤ ∑ p ∈ S, Real.log (p : ℝ) /
        ((p : ℝ) * (U - Real.log (p : ℝ))) :=
      Finset.sum_nonneg fun p hp ↦ (hterm p hp).1
    rw [abs_of_nonneg hsumNonneg]
    calc
      (∑ p ∈ S, Real.log (p : ℝ) /
          ((p : ℝ) * (U - Real.log (p : ℝ)))) ≤
          ∑ p ∈ S, (3 / L) * (Real.log (p : ℝ) / (p : ℝ)) :=
            Finset.sum_le_sum fun p hp ↦ (hterm p hp).2
      _ = 3 * D / L := by
        dsimp [D]
        rw [← Finset.mul_sum]
        ring
      _ < δ / 4 := by simpa [L] using hdeletedX
  have hsplit := allowedPrimeLogIncrement_eq_sub S U (Nat.sqrt X) hS hSY
    (fun p hp ↦ by
      have hpPrime := hS p hp
      have hpY : p ≤ Nat.sqrt X := hSY p hp
      have hlogp : Real.log (p : ℝ) ≤ Ylog :=
        Real.log_le_log (by exact_mod_cast hpPrime.pos) (by exact_mod_cast hpY)
      dsimp [U, Ylog]
      linarith [hgapX.2.2])
  rw [hsplit]
  calc
    |(primeLogIncrement U (Nat.sqrt X) -
          ∑ p ∈ S, Real.log (p : ℝ) /
            ((p : ℝ) * (U - Real.log (p : ℝ)))) - Real.log 2| ≤
        |primeLogIncrement U (Nat.sqrt X) - Real.log R| +
          |Real.log R - Real.log 2| +
          |∑ p ∈ S, Real.log (p : ℝ) /
            ((p : ℝ) * (U - Real.log (p : ℝ)))| := by
              calc
                |_ - _| ≤ |primeLogIncrement U (Nat.sqrt X) - Real.log 2| +
                    |∑ p ∈ S, Real.log (p : ℝ) /
                      ((p : ℝ) * (U - Real.log (p : ℝ)))| := by
                        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
                          using abs_sub
                            (primeLogIncrement U (Nat.sqrt X) - Real.log 2)
                            (∑ p ∈ S, Real.log (p : ℝ) /
                              ((p : ℝ) * (U - Real.log (p : ℝ))))
                _ ≤ (|primeLogIncrement U (Nat.sqrt X) - Real.log R| +
                      |Real.log R - Real.log 2|) +
                    |∑ p ∈ S, Real.log (p : ℝ) /
                      ((p : ℝ) * (U - Real.log (p : ℝ)))| := by
                        gcongr
                        exact abs_sub_le _ _ _
    _ < δ / 4 + δ / 4 + δ / 4 :=
      add_lt_add (add_lt_add hprimeApprox hlogApprox) hdeleted
    _ < δ := by linarith

/-- Uniform Mertens evaluation of the moving up-star linear model. -/
theorem eventually_logarithmicWindow_upLinearModel_close
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        |(fixedCenterUpLinearModel S a X -
            Real.log (Real.log (X : ℝ))) -
          (meisselMertensConstant - deletedPrimeReciprocalMass S)| < δ := by
  have hrecip := allowedPrimeReciprocalSum_natSqrt_sub_logLog_tendsto S
  have hrecipAbs : Tendsto
      (fun X : ℕ ↦
        |(allowedPrimeReciprocalSum S (Nat.sqrt X) -
            Real.log (Real.log (X : ℝ))) -
          (meisselMertensConstant - deletedPrimeReciprocalMass S - Real.log 2)|)
      atTop (𝓝 0) := by
    have h := hrecip.sub_const
      (meisselMertensConstant - deletedPrimeReciprocalMass S - Real.log 2)
    norm_num at h
    simpa using h.abs
  have hrecipSmall : ∀ᶠ X : ℕ in atTop,
      |(allowedPrimeReciprocalSum S (Nat.sqrt X) -
          Real.log (Real.log (X : ℝ))) -
        (meisselMertensConstant - deletedPrimeReciprocalMass S - Real.log 2)| <
          δ / 2 :=
    (tendsto_order.1 hrecipAbs).2 (δ / 2) (by positivity)
  have hincrement := eventually_logarithmicWindow_allowedPrimeLogIncrement_close
    S hS hε (show 0 < δ / 2 by positivity)
  filter_upwards [hrecipSmall, hincrement,
      eventually_logarithmicWindow_logSqrt_gap_bounds hε,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0] with
      X hrecipX hincrementX hgap hlogX
  intro a ha
  have hgapX := hgap a ha
  have hlogX' : 0 < Real.log (X : ℝ) := by
    simpa [Function.comp_apply] using hlogX
  have hmodel := fixedCenterUpLinearModel_eq S (c := a) (X := X) (by
    linarith [hgapX.2.2, hlogX'])
  rw [hmodel]
  calc
    |(allowedPrimeReciprocalSum S (Nat.sqrt X) +
          allowedPrimeLogIncrement S (fixedCenterLogScale a X) (Nat.sqrt X) -
          Real.log (Real.log (X : ℝ))) -
        (meisselMertensConstant - deletedPrimeReciprocalMass S)| =
      |((allowedPrimeReciprocalSum S (Nat.sqrt X) -
            Real.log (Real.log (X : ℝ))) -
          (meisselMertensConstant - deletedPrimeReciprocalMass S - Real.log 2)) +
        (allowedPrimeLogIncrement S (fixedCenterLogScale a X) (Nat.sqrt X) -
          Real.log 2)| := by ring
    _ ≤ |(allowedPrimeReciprocalSum S (Nat.sqrt X) -
            Real.log (Real.log (X : ℝ))) -
          (meisselMertensConstant - deletedPrimeReciprocalMass S - Real.log 2)| +
        |allowedPrimeLogIncrement S (fixedCenterLogScale a X) (Nat.sqrt X) -
          Real.log 2| := abs_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add hrecipX (hincrementX a ha)
    _ = δ := by ring

end

end PrimeStar
