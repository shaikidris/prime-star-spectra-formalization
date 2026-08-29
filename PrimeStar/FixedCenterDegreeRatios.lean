import PrimeStar.FixedCenterIsolation

/-!
# Fixed-centre large-prime degree ratios

This module compares the literal square-cutoff star-degree formula at two
fixed arithmetic centres.  It proves the pointwise PNT limits used by the
up-star and down-star terms of the finite remainder.

These pointwise limits do not by themselves evaluate the growing sum over all
up-star labels.  That later step requires a uniform head--tail estimate.
-/

namespace PrimeStar

open Filter Topology Asymptotics

noncomputable section

/-- The real-valued square-cutoff degree formula at the fixed arithmetic
centre `c`.  Eventually this is the actual large-prime star degree of every
vertex whose underlying natural number is `c`. -/
def fixedCenterArithmeticDegree (S : Finset ℕ) (c X : ℕ) : ℝ :=
  (allowedPrimeCount S (X / c) : ℝ) -
    (allowedPrimeCount S (Nat.sqrt X) : ℝ)

theorem pntMain_tendsto_atTop :
    Tendsto (fun X : ℕ ↦ (X : ℝ) / Real.log (X : ℝ)) atTop atTop := by
  have hp : Tendsto (fun X : ℕ ↦ (Nat.primeCounting X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  exact primeCounting_isEquivalent_main.tendsto_atTop hp

theorem one_isLittleO_pntMain :
    (fun _X : ℕ ↦ (1 : ℝ)) =o[atTop]
      (fun X : ℕ ↦ (X : ℝ) / Real.log (X : ℝ)) := by
  rw [Asymptotics.isLittleO_one_left_iff]
  exact tendsto_norm_atTop_atTop.comp pntMain_tendsto_atTop

theorem real_sqrt_isLittleO_div_log :
    Real.sqrt =o[atTop] (fun x : ℝ ↦ x / Real.log x) := by
  have hsqrtLogSq :
      Real.sqrt =o[atTop] (fun x : ℝ ↦ x / Real.log x ^ 2) := by
    apply Asymptotics.isLittleO_mul_iff_isLittleO_div _ |>.mp
    · conv => arg 2; ext; rw [mul_comm]
      apply Asymptotics.isLittleO_mul_iff_isLittleO_div _ |>.mpr
      · simp_rw [Real.div_sqrt, Real.sqrt_eq_rpow, ← Real.rpow_two]
        apply isLittleO_log_rpow_rpow_atTop _ (by norm_num)
      filter_upwards [eventually_gt_atTop 0] with x hx
      exact Real.sqrt_ne_zero'.mpr hx
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact pow_ne_zero _
      (Real.log_ne_zero.mpr ⟨by linarith, by linarith, by linarith⟩)
  have hscale :
      (fun x : ℝ ↦ x / Real.log x ^ 2) =o[atTop]
        (fun x : ℝ ↦ x / Real.log x) := by
    have h := (Asymptotics.isBigO_refl
      (fun x : ℝ ↦ x / Real.log x) atTop).mul_isLittleO
        Real.inv_log_isLittleO_one
    simpa only [div_eq_mul_inv, pow_two, mul_inv_rev, mul_assoc, mul_one] using h
  exact hsqrtLogSq.trans hscale

theorem natSqrtCast_isLittleO_pntMain :
    (fun X : ℕ ↦ (Nat.sqrt X : ℝ)) =o[atTop]
      (fun X : ℕ ↦ (X : ℝ) / Real.log (X : ℝ)) := by
  have hreal := real_sqrt_isLittleO_div_log.natCast_atTop
  have hbound :
      (fun X : ℕ ↦ (Nat.sqrt X : ℝ)) =O[atTop]
        (fun X : ℕ ↦ Real.sqrt (X : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with X
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
    exact Real.nat_sqrt_le_real_sqrt
  have hreal' : (fun X : ℕ ↦ Real.sqrt (X : ℝ)) =o[atTop]
      (fun X : ℕ ↦ (X : ℝ) / Real.log (X : ℝ)) := hreal
  exact hbound.trans_isLittleO hreal'

theorem primeCounting_sqrt_isLittleO_pntMain :
    (fun X : ℕ ↦ (Nat.primeCounting (Nat.sqrt X) : ℝ)) =o[atTop]
      (fun X : ℕ ↦ (X : ℝ) / Real.log (X : ℝ)) := by
  have hbound :
      (fun X : ℕ ↦ (Nat.primeCounting (Nat.sqrt X) : ℝ)) =O[atTop]
        (fun X : ℕ ↦ (Nat.sqrt X : ℝ) + 1) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with X
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul]
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range]
    have hNat :
        (Finset.filter Nat.Prime (Finset.range (Nat.sqrt X + 1))).card ≤
          Nat.sqrt X + 1 := by
      simpa only [Finset.card_range] using
        (Finset.card_filter_le (Finset.range (Nat.sqrt X + 1)) Nat.Prime)
    exact_mod_cast hNat
  have hsmall :
      (fun X : ℕ ↦ (Nat.sqrt X : ℝ) + 1) =o[atTop]
        (fun X : ℕ ↦ (X : ℝ) / Real.log (X : ℝ)) :=
    natSqrtCast_isLittleO_pntMain.add one_isLittleO_pntMain
  exact hbound.trans_isLittleO hsmall

theorem primeDegree_isEquivalent_main (c : ℕ) (hc : 0 < c) :
    (fun X : ℕ ↦ (Nat.primeCounting (X / c) : ℝ) -
      (Nat.primeCounting (Nat.sqrt X) : ℝ)) ~[atTop]
      (fun X : ℕ ↦ (c : ℝ)⁻¹ *
        ((X : ℝ) / Real.log (X : ℝ))) := by
  have hlead := primeCounting_div_const_isEquivalent c hc
  have hcR : ((c : ℝ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hc.ne')
  have hboundary := IsLittleO.const_mul_right hcR
    primeCounting_sqrt_isLittleO_pntMain
  exact hlead.sub_isLittleO hboundary

/-- Every member of a fixed finite set eventually lies below the square-root
cutoff. -/
theorem eventually_finset_le_nat_sqrt (S : Finset ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ p ∈ S, p ≤ Nat.sqrt X := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
      filter_upwards [ih, eventually_ge_atTop (p ^ 2)] with X hSX hpX
      intro q hq
      simp only [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact Nat.le_sqrt'.2 hpX
      · exact hSX q hq

/-- Finite deletion cancels exactly from the fixed-centre square-cutoff degree
once both endpoints contain the deletion set. -/
theorem eventually_fixedCenterArithmeticDegree_eq_primeDegree
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    (fun X : ℕ ↦ fixedCenterArithmeticDegree S c X) =ᶠ[atTop]
      (fun X : ℕ ↦ (Nat.primeCounting (X / c) : ℝ) -
        (Nat.primeCounting (Nat.sqrt X) : ℝ)) := by
  filter_upwards [eventually_finset_le_nat_div S hc,
    eventually_finset_le_nat_sqrt S] with X hdiv hsqrt
  have htop := allowedPrimeCount_add_card_eq_primeCounting hS hdiv
  have hbottom := allowedPrimeCount_add_card_eq_primeCounting hS hsqrt
  have htopR :
      (allowedPrimeCount S (X / c) : ℝ) + (S.card : ℝ) =
        (Nat.primeCounting (X / c) : ℝ) := by
    exact_mod_cast htop
  have hbottomR :
      (allowedPrimeCount S (Nat.sqrt X) : ℝ) + (S.card : ℝ) =
        (Nat.primeCounting (Nat.sqrt X) : ℝ) := by
    exact_mod_cast hbottom
  dsimp [fixedCenterArithmeticDegree]
  linarith

theorem fixedCenterArithmeticDegree_isEquivalent_main
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    (fun X : ℕ ↦ fixedCenterArithmeticDegree S c X) ~[atTop]
      (fun X : ℕ ↦ (c : ℝ)⁻¹ *
        ((X : ℝ) / Real.log (X : ℝ))) := by
  exact (primeDegree_isEquivalent_main c hc).congr_left
    (eventually_fixedCenterArithmeticDegree_eq_primeDegree S hS hc).symm

/-- Ratio law for any two fixed arithmetic centres. -/
theorem fixedCenterArithmeticDegree_ratio_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    Tendsto
      (fun X : ℕ ↦ fixedCenterArithmeticDegree S d X /
        fixedCenterArithmeticDegree S c X)
      atTop (𝓝 ((c : ℝ) / (d : ℝ))) := by
  have hratio := (fixedCenterArithmeticDegree_isEquivalent_main S hS hd).div
    (fixedCenterArithmeticDegree_isEquivalent_main S hS hc)
  have hmainPos :
      ∀ᶠ X : ℕ in atTop, 0 < (X : ℝ) / Real.log (X : ℝ) :=
    pntMain_tendsto_atTop.eventually (eventually_gt_atTop 0)
  have hmodel :
      (fun X : ℕ ↦ ((d : ℝ)⁻¹ *
          ((X : ℝ) / Real.log (X : ℝ))) /
        ((c : ℝ)⁻¹ * ((X : ℝ) / Real.log (X : ℝ)))) =ᶠ[atTop]
      (fun _X : ℕ ↦ (c : ℝ) / (d : ℝ)) := by
    filter_upwards [hmainPos] with X hX
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    let M : ℝ := (X : ℝ) / Real.log (X : ℝ)
    change ((d : ℝ)⁻¹ * M) / ((c : ℝ)⁻¹ * M) =
      (c : ℝ) / (d : ℝ)
    have hM : M ≠ 0 := by
      dsimp [M]
      exact hX.ne'
    field_simp [hM, hcR, hdR]
  have hconst := hratio.congr_right hmodel
  exact (isEquivalent_const_iff_tendsto (div_ne_zero
    (by exact_mod_cast hc.ne') (by exact_mod_cast hd.ne'))).mp hconst

/-- Fixed up-star ratios converge to `1/q`. -/
theorem fixedCenter_upArithmeticDegreeRatio_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c q : ℕ} (hc : 0 < c) (hq : 0 < q) :
    Tendsto
      (fun X : ℕ ↦ fixedCenterArithmeticDegree S (c * q) X /
        fixedCenterArithmeticDegree S c X)
      atTop (𝓝 ((q : ℝ)⁻¹)) := by
  have h := fixedCenterArithmeticDegree_ratio_tendsto S hS hc (Nat.mul_pos hc hq)
  convert h using 1
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Nat.cast_mul]
  field_simp

/-- Fixed down-star ratios converge to `q` when `q` divides the centre. -/
theorem fixedCenter_downArithmeticDegreeRatio_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c q : ℕ} (hc : 0 < c) (hq : 0 < q) (hqc : q ∣ c) :
    Tendsto
      (fun X : ℕ ↦ fixedCenterArithmeticDegree S (c / q) X /
        fixedCenterArithmeticDegree S c X)
      atTop (𝓝 (q : ℝ)) := by
  have hqle : q ≤ c := Nat.le_of_dvd hc hqc
  have hdivPos : 0 < c / q := Nat.div_pos hqle hq
  have h := fixedCenterArithmeticDegree_ratio_tendsto S hS hc hdivPos
  have hdivR : ((c / q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdivPos.ne'
  have hlimit : (c : ℝ) / ((c / q : ℕ) : ℝ) = (q : ℝ) := by
    rw [div_eq_iff hdivR]
    have hnat : c = q * (c / q) := by
      simpa [mul_comm] using (Nat.div_mul_cancel hqc).symm
    exact_mod_cast hnat
  simpa only [hlimit] using h

/-- The arithmetic formula is eventually the graph's actual large-prime star
degree at every representative of the fixed centre. -/
theorem eventually_fixedCenterArithmeticDegree_eq_largePrimeStarDegree
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (_hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X, (a : ℕ) = c →
      fixedCenterArithmeticDegree S c X =
        (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
  filter_upwards [eventually_ge_atTop (c ^ 2)] with X hX
  intro a haVal
  have haY : (a : ℕ) ≤ Nat.sqrt X := by
    rw [haVal]
    exact Nat.le_sqrt'.2 hX
  have hYXa : Nat.sqrt X ≤ X / (a : ℕ) := by
    apply (Nat.le_div_iff_mul_le (Vertex.coe_pos a)).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hcount := allowedPrimeCount_mono (S := S) hYXa
  rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS a haY hYXa,
    Nat.cast_sub hcount, haVal]
  rfl

end

end PrimeStar
