import PrimeStar.FixedCenterCorrectionEvaluation
import PrimeStar.PrimeLogIncrement

/-!
# Evaluation of the actual fixed-centre up-star correction

This module compares the growing arithmetic up-star sum with the limiting
model `4 log log X + 4 κ_S`.  The linear prime-reciprocal part is matched to
Mertens plus the logarithmic increment already evaluated in
`PrimeLogIncrement`.  The quadratic remainder is handled by a uniform
head--tail estimate with a `1/q^2` majorant.

The argument is for a fixed arithmetic centre.  Uniformity in a growing
centre is a separate theorem.
-/

namespace PrimeStar

open Filter Topology Asymptotics
open scoped BigOperators

noncomputable section

/-- The PNT main term at a natural cutoff. -/
def pntMain (n : ℕ) : ℝ :=
  (n : ℝ) / Real.log (n : ℝ)

theorem exists_primeCounting_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      |(Nat.primeCounting n : ℝ) - pntMain n| ≤
        C * (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := primeCounting_sub_main_isBigO.bound
  refine ⟨max C 1, by positivity, ?_⟩
  filter_upwards [hC, eventually_gt_atTop 2] with n hn hn2
  have hn1 : (1 : ℝ) < n :=
    lt_trans (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn2)
  have hscale : 0 ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale] at hn
  calc
    |(Nat.primeCounting n : ℝ) - pntMain n| ≤
        C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) := hn
    _ ≤ max C 1 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) := by gcongr; exact le_max_left C 1
    _ = max C 1 * (n : ℝ) / Real.log (n : ℝ) ^ 2 := by ring

/-- The local main-term model for an up-star ratio at label `q`. -/
def fixedCenterUpRatioModel (c q X : ℕ) : ℝ :=
  let L := fixedCenterLogScale c X
  L / ((q : ℝ) * (L - Real.log (q : ℝ)))

/-- The full moving main-model sum through the square-root endpoint.  Unlike
the actual graph ratio, this model is not truncated at `c * q ≤ sqrt X`; the
extra labels form an explicitly vanishing endpoint tail. -/
def fixedCenterUpLinearModel (S : Finset ℕ) (c X : ℕ) : ℝ :=
  ∑ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
    fixedCenterUpRatioModel c q X

/-- Allowed-prime truncation of the logarithmic increment. -/
def allowedPrimeLogIncrement (S : Finset ℕ) (L : ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE Y).filter (fun p ↦ p ∉ S),
    Real.log (p : ℝ) / ((p : ℝ) * (L - Real.log (p : ℝ)))

/-- The deleted-prime part of the logarithmic increment. -/
def deletedPrimeLogIncrement (S : Finset ℕ) (L : ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE Y).filter (fun p ↦ p ∈ S),
    Real.log (p : ℝ) / ((p : ℝ) * (L - Real.log (p : ℝ)))

theorem allowedPrimeLogIncrement_add_deleted
    (S : Finset ℕ) (L : ℝ) (Y : ℕ) :
    allowedPrimeLogIncrement S L Y + deletedPrimeLogIncrement S L Y =
      primeLogIncrement L Y := by
  rw [allowedPrimeLogIncrement, deletedPrimeLogIncrement, primeLogIncrement]
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not
      (s := Nat.primesLE Y) (p := fun p ↦ p ∉ S)
      (f := fun p ↦
        Real.log (p : ℝ) / ((p : ℝ) * (L - Real.log (p : ℝ)))))

/-- The moving model splits exactly into the reciprocal Mertens sum and the
logarithmic increment. -/
theorem fixedCenterUpLinearModel_eq
    (S : Finset ℕ) {c X : ℕ}
    (hgap : Real.log (Nat.sqrt X : ℝ) < fixedCenterLogScale c X) :
    fixedCenterUpLinearModel S c X =
      allowedPrimeReciprocalSum S (Nat.sqrt X) +
        allowedPrimeLogIncrement S (fixedCenterLogScale c X) (Nat.sqrt X) := by
  rw [fixedCenterUpLinearModel, allowedPrimeReciprocalSum,
    allowedPrimeLogIncrement]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hqMem := (Finset.mem_filter.mp hq).1
  have hqPrime : q.Prime := (Nat.mem_primesLE.mp hqMem).2
  have hqLe : q ≤ Nat.sqrt X := (Nat.mem_primesLE.mp hqMem).1
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hlogLe : Real.log (q : ℝ) ≤ Real.log (Nat.sqrt X : ℝ) :=
    Real.log_le_log hqPos (by exact_mod_cast hqLe)
  have hden : fixedCenterLogScale c X - Real.log (q : ℝ) ≠ 0 := by
    linarith
  rw [fixedCenterUpRatioModel]
  field_simp [hqPos.ne', hden]
  ring

theorem fixedCenterLogScale_tendsto_atTop {c : ℕ} :
    Tendsto (fixedCenterLogScale c) atTop atTop := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  change Tendsto (fun X : ℕ ↦ Real.log (X : ℝ) - Real.log (c : ℝ)) atTop atTop
  simpa only [sub_eq_add_neg] using
    tendsto_atTop_add_const_right atTop (-Real.log (c : ℝ)) hlogTop

/-- A fixed deleted prime contributes vanishing mass to the moving logarithmic
increment. -/
theorem fixedCenter_deletedPrimeLogTerm_tendsto_zero
    {c p : ℕ} (hp : 0 < p) :
    Tendsto
      (fun X : ℕ ↦ Real.log (p : ℝ) /
        ((p : ℝ) * (fixedCenterLogScale c X - Real.log (p : ℝ))))
      atTop (𝓝 0) := by
  have hgap : Tendsto
      (fun X : ℕ ↦ (p : ℝ) *
        (fixedCenterLogScale c X - Real.log (p : ℝ))) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-Real.log (p : ℝ))
      (fixedCenterLogScale_tendsto_atTop (c := c))
    exact h.const_mul_atTop (by exact_mod_cast hp)
  exact tendsto_const_nhds.div_atTop hgap

/-- Finite deletion changes the moving logarithmic increment by `o(1)`. -/
theorem fixedCenter_deletedPrimeLogIncrement_tendsto_zero
    (S : Finset ℕ) {c : ℕ} :
    Tendsto
      (fun X : ℕ ↦ deletedPrimeLogIncrement S
        (fixedCenterLogScale c X) (Nat.sqrt X))
      atTop (𝓝 0) := by
  let deletedMass : ℕ → ℝ := fun X ↦
    ∑ p ∈ S.filter Nat.Prime,
      Real.log (p : ℝ) /
        ((p : ℝ) * (fixedCenterLogScale c X - Real.log (p : ℝ)))
  have hmass : Tendsto deletedMass atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun X : ℕ ↦ ∑ p ∈ S.filter Nat.Prime,
          Real.log (p : ℝ) /
            ((p : ℝ) * (fixedCenterLogScale c X - Real.log (p : ℝ))))
        atTop (𝓝 (∑ _p ∈ S.filter Nat.Prime, (0 : ℝ))) :=
      tendsto_finsetSum (S.filter Nat.Prime) fun p hp ↦
        fixedCenter_deletedPrimeLogTerm_tendsto_zero
          (Nat.Prime.pos (Finset.mem_filter.mp hp).2)
    simpa only [Finset.sum_const_zero, deletedMass] using hsum
  apply hmass.congr'
  filter_upwards [eventually_finset_le_nat_sqrt S] with X hSX
  change
    (∑ p ∈ S.filter Nat.Prime,
      Real.log (p : ℝ) /
        ((p : ℝ) * (fixedCenterLogScale c X - Real.log (p : ℝ)))) =
      ∑ p ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun p ↦ p ∈ S),
        Real.log (p : ℝ) /
          ((p : ℝ) * (fixedCenterLogScale c X - Real.log (p : ℝ)))
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨hpS, hpPrime⟩
      exact ⟨⟨hSX p hpS, hpPrime⟩, hpS⟩
    · rintro ⟨⟨_hpY, hpPrime⟩, hpS⟩
      exact ⟨hpS, hpPrime⟩
  · intro p _hp
    rfl

/-- The allowed moving logarithmic increment has the same `log 2` limit as
the full prime sum. -/
theorem fixedCenter_allowedPrimeLogIncrement_tendsto_log_two
    (S : Finset ℕ) {c : ℕ} (hc : 0 < c) :
    Tendsto
      (fun X : ℕ ↦ allowedPrimeLogIncrement S
        (fixedCenterLogScale c X) (Nat.sqrt X))
      atTop (𝓝 (Real.log 2)) := by
  have hfull := fixedCenter_primeLogIncrement_tendsto_log_two hc
  have hdeleted := fixedCenter_deletedPrimeLogIncrement_tendsto_zero S (c := c)
  have h := hfull.sub hdeleted
  norm_num at h
  refine h.congr' ?_
  filter_upwards with X
  have hsplit := allowedPrimeLogIncrement_add_deleted S
    (fixedCenterLogScale c X) (Nat.sqrt X)
  linarith

theorem tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop]
  intro N
  filter_upwards [eventually_ge_atTop (N ^ 2)] with X hX
  exact Nat.le_sqrt'.2 hX

/-- The Mertens logarithm at the square-root endpoint differs from the one at
`X` by `-log 2`. -/
theorem logLog_natSqrt_sub_logLog_tendsto_neg_log_two :
    Tendsto
      (fun X : ℕ ↦ Real.log (Real.log (Nat.sqrt X : ℝ)) -
        Real.log (Real.log (X : ℝ)))
      atTop (𝓝 (-Real.log 2)) := by
  have hratio := log_natSqrt_div_log_tendsto_half
  have hlogRatio : Tendsto
      (fun X : ℕ ↦ Real.log
        (Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ)))
      atTop (𝓝 (Real.log (1 / 2 : ℝ))) :=
    (Real.continuousAt_log (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto.comp hratio
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtLogTop : Tendsto
      (fun X : ℕ ↦ Real.log (Nat.sqrt X : ℝ)) atTop atTop :=
    log_natSqrt_isEquivalent_halfLog.symm.tendsto_atTop
      (hlogTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hlimit : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlimit] at hlogRatio
  refine hlogRatio.congr' ?_
  filter_upwards [hlogTop.eventually_gt_atTop 0,
    hsqrtLogTop.eventually_gt_atTop 0] with X hX hY
  rw [Real.log_div hY.ne' hX.ne']

/-- Prime Mertens at the square-root endpoint, rewritten against `log log X`.
-/
theorem allowedPrimeReciprocalSum_natSqrt_sub_logLog_tendsto
    (S : Finset ℕ) :
    Tendsto
      (fun X : ℕ ↦ allowedPrimeReciprocalSum S (Nat.sqrt X) -
        Real.log (Real.log (X : ℝ)))
      atTop (𝓝 (meisselMertensConstant - deletedPrimeReciprocalMass S -
        Real.log 2)) := by
  have hmertens :=
    allowedPrimeMertensAsymptotic_meisselMertensConstant S |>.comp
      tendsto_natSqrt_atTop
  have hoffset := logLog_natSqrt_sub_logLog_tendsto_neg_log_two
  have h := hmertens.add hoffset
  convert h using 1
  · funext X
    dsimp only [Function.comp_apply]
    ring
  · ring

/-- The full moving linear model has the constant predicted by Mertens. -/
theorem fixedCenterUpLinearModel_sub_logLog_tendsto
    (S : Finset ℕ) {c : ℕ} (hc : 0 < c) :
    Tendsto
      (fun X : ℕ ↦ fixedCenterUpLinearModel S c X -
        Real.log (Real.log (X : ℝ)))
      atTop (𝓝 (meisselMertensConstant - deletedPrimeReciprocalMass S)) := by
  have hrecip := allowedPrimeReciprocalSum_natSqrt_sub_logLog_tendsto S
  have hincr := fixedCenter_allowedPrimeLogIncrement_tendsto_log_two S hc
  have hsum := hrecip.add hincr
  have hsum' : Tendsto
      (fun X : ℕ ↦ allowedPrimeReciprocalSum S (Nat.sqrt X) -
        Real.log (Real.log (X : ℝ)) +
          allowedPrimeLogIncrement S (fixedCenterLogScale c X) (Nat.sqrt X))
      atTop (𝓝 (meisselMertensConstant - deletedPrimeReciprocalMass S)) := by
    convert hsum using 1 <;> ring
  have hgap := fixedCenter_logGap_tendsto_atTop hc
  refine hsum'.congr' ?_
  filter_upwards [hgap.eventually_gt_atTop 0] with X hX
  have hmodel := fixedCenterUpLinearModel_eq S (c := c) (X := X) (by linarith)
  rw [hmodel]
  ring

theorem upStarCorrection_eq_linear_add_quadratic
    {r : ℝ} (hr : r ≠ 1) :
    upStarCorrection r = 4 * r + 4 * r ^ 2 / (1 - r) := by
  rw [upStarCorrection]
  have hden : 1 - r ≠ 0 := sub_ne_zero.mpr hr.symm
  field_simp [hden]
  ring

theorem continuousAt_upStarCorrection {r : ℝ} (hr : r ≠ 1) :
    ContinuousAt upStarCorrection r := by
  unfold upStarCorrection
  exact (continuousAt_const.mul continuousAt_id).div
    (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hr.symm)

theorem eventually_fixedCenterArithmeticDegree_ge_half_main
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      (1 / 2 : ℝ) * ((c : ℝ)⁻¹ * ((X : ℝ) / Real.log (X : ℝ))) ≤
        fixedCenterArithmeticDegree S c X := by
  have heq := fixedCenterArithmeticDegree_isEquivalent_main S hS hc
  have hmainPos :
      ∀ᶠ X : ℕ in atTop, 0 < (c : ℝ)⁻¹ * ((X : ℝ) / Real.log (X : ℝ)) := by
    have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
    filter_upwards [pntMain_tendsto_atTop.eventually (eventually_gt_atTop 0)] with X hX
    positivity
  have hdiv :
      Tendsto
        (fun X : ℕ ↦ fixedCenterArithmeticDegree S c X /
          ((c : ℝ)⁻¹ * ((X : ℝ) / Real.log (X : ℝ))))
        atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (by
      filter_upwards [hmainPos] with X hX
      exact hX.ne')).mp heq
  filter_upwards [hdiv.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hmainPos] with X hratio hpos
  exact (lt_div_iff₀ hpos).mp hratio |>.le

/-- The linear part of the actual up-star correction. -/
def fixedCenterActualUpLinear (S : Finset ℕ) (c X : ℕ) : ℝ :=
  ∑ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
    fixedCenterActualUpRatio S c X q

/-- The quadratic remainder of the actual up-star correction. -/
def fixedCenterActualUpQuadratic (S : Finset ℕ) (c X : ℕ) : ℝ :=
  ∑ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
    (fixedCenterActualUpRatio S c X q) ^ 2 /
      (1 - fixedCenterActualUpRatio S c X q)

theorem log_div_eq_fixedCenterLogScale
    {c X : ℕ} (hc : 0 < c) (hX : 0 < X) :
    Real.log ((X : ℝ) / (c : ℝ)) = fixedCenterLogScale c X := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  rw [Real.log_div hXR hcR, fixedCenterLogScale]

theorem fixedCenterUpRatioModel_eq_reciprocal_add
    {c q X : ℕ} (hc : 0 < c) (hX : 0 < X)
    (hq0 : 0 < q) (hgap : Real.log (q : ℝ) < fixedCenterLogScale c X) :
    fixedCenterUpRatioModel c q X =
      (q : ℝ)⁻¹ +
        Real.log (q : ℝ) /
          ((q : ℝ) * (fixedCenterLogScale c X - Real.log (q : ℝ))) := by
  unfold fixedCenterUpRatioModel
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hden : fixedCenterLogScale c X - Real.log (q : ℝ) ≠ 0 :=
    sub_ne_zero.mpr hgap.ne'
  field_simp [hqR, hden]
  ring

theorem allowedPrimeLogIncrement_eq_sub
    (S : Finset ℕ) (L : ℝ) (Y : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hY : ∀ p ∈ S, p ≤ Y)
    (hgap : ∀ p ∈ S, Real.log (p : ℝ) < L) :
    allowedPrimeLogIncrement S L Y =
      primeLogIncrement L Y -
        ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) * (L - Real.log (p : ℝ))) := by
  unfold allowedPrimeLogIncrement primeLogIncrement
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := Nat.primesLE Y)
      (p := fun p ↦ p ∉ S)
      (f := fun p ↦ Real.log (p : ℝ) / ((p : ℝ) * (L - Real.log (p : ℝ))))
  have hdel :
      ∑ p ∈ (Nat.primesLE Y).filter (fun p ↦ ¬p ∉ S),
          Real.log (p : ℝ) / ((p : ℝ) * (L - Real.log (p : ℝ))) =
        ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) * (L - Real.log (p : ℝ))) := by
    simp only [not_not]
    have hset :
        (Nat.primesLE Y).filter (fun p ↦ p ∈ S) = S := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨_, hpP⟩, hpS⟩
        exact hpS
      · intro hpS
        exact ⟨⟨hY p hpS, hS p hpS⟩, hpS⟩
    rw [hset]
  rw [← hsplit, hdel]
  abel

/-! ## Uniform comparison with the actual degree ratios -/

/-- The PNT main term at a real cutoff. -/
def pntMainReal (x : ℝ) : ℝ := x / Real.log x

/-- A pointwise form of the quantitative PNT, uniform for all sufficiently
large real cutoffs. -/
theorem exists_realPrimeCounting_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - pntMainReal x| ≤
        C * x / Real.log x ^ 2 := by
  obtain ⟨C, hC⟩ := primeCounting_sub_main_isBigO_real.bound
  refine ⟨max C 1, by positivity, ?_⟩
  filter_upwards [hC, eventually_gt_atTop 2] with x hx hx2
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ x / Real.log x ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale] at hx
  calc
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - pntMainReal x| ≤
        C * (x / Real.log x ^ 2) := hx
    _ ≤ max C 1 * (x / Real.log x ^ 2) := by
      gcongr
      exact le_max_left C 1
    _ = max C 1 * x / Real.log x ^ 2 := by ring

/-- Once the deletion set lies below both endpoints, it cancels exactly from
the square-cutoff degree. -/
theorem fixedCenterArithmeticDegree_eq_primeDegree_of_endpoints
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {d X : ℕ} (hSY : ∀ p ∈ S, p ≤ Nat.sqrt X)
    (hYd : Nat.sqrt X ≤ X / d) :
    fixedCenterArithmeticDegree S d X =
      (Nat.primeCounting (X / d) : ℝ) -
        (Nat.primeCounting (Nat.sqrt X) : ℝ) := by
  have hSd : ∀ p ∈ S, p ≤ X / d := fun p hp ↦ (hSY p hp).trans hYd
  have htop := allowedPrimeCount_add_card_eq_primeCounting hS hSd
  have hbottom := allowedPrimeCount_add_card_eq_primeCounting hS hSY
  have htopR :
      (allowedPrimeCount S (X / d) : ℝ) + (S.card : ℝ) =
        (Nat.primeCounting (X / d) : ℝ) := by exact_mod_cast htop
  have hbottomR :
      (allowedPrimeCount S (Nat.sqrt X) : ℝ) + (S.card : ℝ) =
        (Nat.primeCounting (Nat.sqrt X) : ℝ) := by exact_mod_cast hbottom
  unfold fixedCenterArithmeticDegree
  linarith

theorem natFloor_real_div_eq_div (X d : ℕ) :
    ⌊(X : ℝ) / (d : ℝ)⌋₊ = X / d := by
  exact Nat.floor_div_eq_div X d

/-- The real PNT main-term ratio is exactly the moving model. -/
theorem pntMainReal_ratio_eq_upRatioModel
    {c q X : ℕ} (hc : 0 < c) (hq : 0 < q) (hX : 0 < X)
    (hgap : Real.log (q : ℝ) < fixedCenterLogScale c X) :
    pntMainReal ((X : ℝ) / ((c : ℝ) * (q : ℝ))) /
        pntMainReal ((X : ℝ) / (c : ℝ)) =
      fixedCenterUpRatioModel c q X := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hlog0 : Real.log ((X : ℝ) / (c : ℝ)) =
      fixedCenterLogScale c X := by
    rw [Real.log_div hXR hcR, fixedCenterLogScale]
  have hlogq : Real.log ((X : ℝ) / ((c : ℝ) * (q : ℝ))) =
      fixedCenterLogScale c X - Real.log (q : ℝ) := by
    rw [Real.log_div hXR (mul_ne_zero hcR hqR), Real.log_mul hcR hqR,
      fixedCenterLogScale]
    ring
  have hqOne : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq.ne')
  have hL0 : fixedCenterLogScale c X ≠ 0 := by
    exact ne_of_gt ((Real.log_nonneg hqOne).trans_lt hgap)
  have hLq : fixedCenterLogScale c X - Real.log (q : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hgap)
  unfold pntMainReal fixedCenterUpRatioModel
  rw [hlog0, hlogq]
  field_simp [hcR, hqR, hXR, hL0, hLq]

end

end PrimeStar
