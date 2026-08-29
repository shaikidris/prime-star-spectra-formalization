import PrimeStar.FixedCenterUniformUpStar
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Nonlinear fixed-centre up-star tail

This module upgrades the uniform linear comparison to the nonlinear summand
`r^2 / (1 - r)`.  The proof uses a finite-head / summable-tail split and
Tannery's theorem.
-/

namespace PrimeStar

open Filter Topology Asymptotics
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1200000

/-- A finite family of eventual statements holds eventually simultaneously. -/
theorem eventually_forall_mem_finset
    {α ι : Type*} [Preorder α] [DecidableEq ι] (s : Finset ι)
    (P : α → ι → Prop) (h : ∀ i ∈ s, ∀ᶠ a : α in atTop, P a i) :
    ∀ᶠ a : α in atTop, ∀ i ∈ s, P a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiEv : ∀ᶠ a : α in atTop, P a i := h i (Finset.mem_insert_self i s)
      have hsEv : ∀ᶠ a : α in atTop, ∀ j ∈ s, P a j :=
        ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
      filter_upwards [hiEv, hsEv] with a hai has
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hai
      · exact has j hj

/-- In the full square-root prime window the moving PNT model is positive and
bounded by `3/q`, eventually for a fixed centre. -/
theorem eventually_fixedCenterUpRatioModel_bounds
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      ∀ q ∈ Nat.primesLE (Nat.sqrt X),
        0 ≤ fixedCenterUpRatioModel c q X ∧
          fixedCenterUpRatioModel c q X ≤ 3 / (q : ℝ) := by
  filter_upwards [eventually_fixedCenter_logSqrt_between hc,
      eventually_fixedCenter_logScale_between_log hc,
      eventually_ge_atTop 4] with X hlogY hlogL hX
  intro q hq
  have hqPrime : q.Prime := (Nat.mem_primesLE.mp hq).2
  have hqLeY : q ≤ Nat.sqrt X := (Nat.mem_primesLE.mp hq).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hLpos : 0 < fixedCenterLogScale c X :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.log (X : ℝ) / 2) hlogL.1
  have hlogq : Real.log (q : ℝ) ≤ Real.log (Nat.sqrt X : ℝ) :=
    Real.log_le_log hqR (by exact_mod_cast hqLeY)
  have hgapThird : fixedCenterLogScale c X / 3 ≤
      fixedCenterLogScale c X - Real.log (q : ℝ) := by
    linarith [hlogY.2, hlogq]
  have hgap : Real.log (q : ℝ) < fixedCenterLogScale c X := by linarith
  constructor
  · unfold fixedCenterUpRatioModel
    positivity
  · unfold fixedCenterUpRatioModel
    rw [div_le_iff₀ (mul_pos hqR (lt_of_lt_of_le (by positivity) hgapThird))]
    field_simp [hqR.ne']
    nlinarith [hgapThird]

/-- The actual degree ratio is nonnegative whenever the centre degree is
positive. -/
theorem fixedCenterActualUpRatio_nonneg
    (S : Finset ℕ) {c X q : ℕ} (hc : 0 < c) (hq : 0 < q)
    (hD : 0 < fixedCenterArithmeticDegree S c X) :
    0 ≤ fixedCenterActualUpRatio S c X q := by
  by_cases hcut : c * q ≤ Nat.sqrt X
  · have hcqPos : 0 < c * q := Nat.mul_pos hc hq
    have hySq : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    have hcqY : (c * q) * Nat.sqrt X ≤ X :=
      (Nat.mul_le_mul_right (Nat.sqrt X) hcut).trans hySq
    have hYdiv : Nat.sqrt X ≤ X / (c * q) :=
      (Nat.le_div_iff_mul_le hcqPos).2 (by simpa [mul_comm] using hcqY)
    have hmono := allowedPrimeCount_mono (S := S) hYdiv
    rw [fixedCenterActualUpRatio, if_pos hcut]
    unfold fixedCenterArithmeticDegree
    have hmonoR : (allowedPrimeCount S (Nat.sqrt X) : ℝ) ≤
        (allowedPrimeCount S (X / (c * q)) : ℝ) := by exact_mod_cast hmono
    have hnum : 0 ≤
        (allowedPrimeCount S (X / (c * q)) : ℝ) -
          (allowedPrimeCount S (Nat.sqrt X) : ℝ) := by linarith
    positivity
  · simp [fixedCenterActualUpRatio, hcut]

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
    have hRpos : (0 : ℝ) < 4 * (2 * K + 3) := by positivity
    have : (0 : ℝ) < Q := hRpos.trans hQ
    exact_mod_cast this
  have hA : 0 < A := by dsimp [A]; positivity
  have hsum : Summable (fun n : ℕ ↦ A / (n : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left A
  refine ⟨A, hA, hsum, ?_⟩
  have hheadPoint : ∀ n ∈ Finset.range Q, n.Prime →
      ∀ᶠ X : ℕ in atTop,
        fixedCenterActualUpRatio S c X n ≤ (3 / 4 : ℝ) := by
    intro n _hnQ hnPrime
    have hlim := fixedCenterActualUpRatio_tendsto S hS hc hnPrime.pos
    have hlt : (n : ℝ)⁻¹ < (3 / 4 : ℝ) := by
      have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hnPrime.two_le
      have hinv : (n : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
        simpa only [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hnTwo)
      linarith
    exact hlim.eventually (isOpen_Iio.mem_nhds hlt) |>.mono fun _ h ↦ h.le
  have hhead : ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.range Q, n.Prime →
        fixedCenterActualUpRatio S c X n ≤ (3 / 4 : ℝ) := by
    apply eventually_forall_mem_finset (Finset.range Q)
      (fun X n ↦ n.Prime → fixedCenterActualUpRatio S c X n ≤ (3 / 4 : ℝ))
    intro n hn
    by_cases hp : n.Prime
    · exact (hheadPoint n hn hp).mono fun _ h _ ↦ h
    · exact Filter.Eventually.of_forall fun _ hpn ↦ (hp hpn).elim
  filter_upwards [hratio, eventually_fixedCenterUpRatioModel_bounds hc, hhead,
      eventually_fixedCenterArithmeticDegree_ge_half_main S hS hc,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
      eventually_ge_atTop 4] with X hratioX hmodelX hheadX hDlower hlogX hX
  intro n
  by_cases hsupp : n.Prime ∧ n ∉ S ∧ n ≤ Nat.sqrt X
  · have hnPrime := hsupp.1
    have hnPos := hnPrime.pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hnAllowed : n ∈
        (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S) := by
      simp [Nat.mem_primesLE, hsupp]
    by_cases hcut : c * n ≤ Nat.sqrt X
    · have hYpos : (0 : ℝ) < Nat.sqrt X := by
        have : 1 ≤ Nat.sqrt X := hnPrime.one_le.trans hsupp.2.2
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
      have hmainPos : 0 < (c : ℝ)⁻¹ *
          ((X : ℝ) / Real.log (X : ℝ)) := by positivity
      have hDpos : 0 < fixedCenterArithmeticDegree S c X := by
        linarith [hDlower]
      have hrNonneg := fixedCenterActualUpRatio_nonneg S hc hnPos hDpos
      have hErr := hratioX n hnAllowed
      have hmodelLe := (hmodelX n (Finset.mem_filter.mp hnAllowed).1).2
      have hcOverY : (c : ℝ) / (Nat.sqrt X : ℝ) ≤ (n : ℝ)⁻¹ := by
        rw [div_le_iff₀ hYpos]
        have hcutR : (c : ℝ) * (n : ℝ) ≤ (Nat.sqrt X : ℝ) := by
          exact_mod_cast hcut
        calc
          (c : ℝ) ≤ (Nat.sqrt X : ℝ) / (n : ℝ) :=
            (le_div_iff₀ hnR).2 hcutR
          _ = (n : ℝ)⁻¹ * (Nat.sqrt X : ℝ) := by
            rw [div_eq_mul_inv]
            ring
      have hrecipLog : 1 / ((n : ℝ) * Real.log (X : ℝ)) ≤
          (n : ℝ)⁻¹ := by
        have hlogX' : 1 ≤ Real.log (X : ℝ) := by
          simpa [Function.comp_apply] using hlogX
        have hinvLog : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ hlogX'
        calc
          1 / ((n : ℝ) * Real.log (X : ℝ)) =
              (n : ℝ)⁻¹ * (Real.log (X : ℝ))⁻¹ := by rw [one_div, mul_inv_rev]; ring
          _ ≤ (n : ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hinvLog (inv_nonneg.mpr hnR.le)
          _ = (n : ℝ)⁻¹ := by ring
      have hErrSimple :
          |fixedCenterActualUpRatio S c X n - fixedCenterUpRatioModel c n X| ≤
            2 * K * (n : ℝ)⁻¹ := by
        calc
          |fixedCenterActualUpRatio S c X n - fixedCenterUpRatioModel c n X| ≤
              K * (1 / ((n : ℝ) * Real.log (X : ℝ)) +
                (c : ℝ) / (Nat.sqrt X : ℝ)) := hErr
          _ ≤ K * ((n : ℝ)⁻¹ + (n : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left (add_le_add hrecipLog hcOverY) hK.le
          _ = 2 * K * (n : ℝ)⁻¹ := by ring
      have hrLe : fixedCenterActualUpRatio S c X n ≤
          (2 * K + 3) / (n : ℝ) := by
        calc
          fixedCenterActualUpRatio S c X n ≤
              fixedCenterUpRatioModel c n X +
                |fixedCenterActualUpRatio S c X n -
                  fixedCenterUpRatioModel c n X| := by
                    linarith [le_abs_self (fixedCenterActualUpRatio S c X n -
                      fixedCenterUpRatioModel c n X)]
          _ ≤ 3 / (n : ℝ) + 2 * K * (n : ℝ)⁻¹ :=
            add_le_add hmodelLe hErrSimple
          _ = (2 * K + 3) / (n : ℝ) := by
            rw [div_eq_mul_inv]
            ring
      have htermNonneg : 0 ≤ fixedCenterActualUpNonlinearTerm S c X n := by
        rw [fixedCenterActualUpNonlinearTerm, if_pos hsupp]
        by_cases hnQ : n < Q
        · have hrCap := hheadX n (Finset.mem_range.2 hnQ) hnPrime
          have hden : 0 < 1 - fixedCenterActualUpRatio S c X n := by linarith
          positivity
        · have hnQ' : Q ≤ n := Nat.le_of_not_gt hnQ
          have hquarter : fixedCenterActualUpRatio S c X n < 1 / 4 := by
            have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hnQ'
            calc
              fixedCenterActualUpRatio S c X n ≤ (2 * K + 3) / (n : ℝ) := hrLe
              _ < 1 / 4 := by
                rw [div_lt_iff₀ hnR]
                nlinarith [hQ.trans_le hQn]
          have hden : 0 < 1 - fixedCenterActualUpRatio S c X n := by linarith
          positivity
      rw [Real.norm_eq_abs, abs_of_nonneg htermNonneg,
        fixedCenterActualUpNonlinearTerm, if_pos hsupp]
      by_cases hnQ : n < Q
      · have hrCap := hheadX n (Finset.mem_range.2 hnQ) hnPrime
        have hden : 1 / 4 ≤ 1 - fixedCenterActualUpRatio S c X n := by linarith
        have hnLeQ : (n : ℝ) ≤ Q := by exact_mod_cast (Nat.le_of_lt hnQ)
        have hAQ : 4 ≤ A / (n : ℝ) ^ 2 := by
          dsimp [A]
          rw [le_div_iff₀ (sq_pos_of_pos hnR)]
          have hnSq : (n : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 :=
            (sq_le_sq₀ hnR.le (by positivity)).2 hnLeQ
          nlinarith
        calc
          fixedCenterActualUpRatio S c X n ^ 2 /
                (1 - fixedCenterActualUpRatio S c X n) ≤ 4 := by
            rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hden)]
            have hrsq : fixedCenterActualUpRatio S c X n ^ 2 ≤ (3 / 4 : ℝ) ^ 2 :=
              (sq_le_sq₀ hrNonneg (by norm_num)).2 hrCap
            nlinarith
          _ ≤ A / (n : ℝ) ^ 2 := hAQ
      · have hnQ' : Q ≤ n := Nat.le_of_not_gt hnQ
        have hquarter : fixedCenterActualUpRatio S c X n < 1 / 4 := by
          have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hnQ'
          calc
            fixedCenterActualUpRatio S c X n ≤ (2 * K + 3) / (n : ℝ) := hrLe
            _ < 1 / 4 := by
              rw [div_lt_iff₀ hnR]
              nlinarith [hQ.trans_le hQn]
        have hden : 1 / 2 ≤ 1 - fixedCenterActualUpRatio S c X n := by linarith
        calc
          fixedCenterActualUpRatio S c X n ^ 2 /
                (1 - fixedCenterActualUpRatio S c X n) ≤
              2 * ((2 * K + 3) / (n : ℝ)) ^ 2 := by
            rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden)]
            have hrsq : fixedCenterActualUpRatio S c X n ^ 2 ≤
                ((2 * K + 3) / (n : ℝ)) ^ 2 :=
              (sq_le_sq₀ hrNonneg (by positivity)).2 hrLe
            nlinarith
          _ ≤ A / (n : ℝ) ^ 2 := by
            have heq : 2 * ((2 * K + 3) / (n : ℝ)) ^ 2 =
                (2 * (2 * K + 3) ^ 2) / (n : ℝ) ^ 2 := by
              rw [div_pow]
              ring
            rw [heq]
            have hRpos : 0 < 2 * K + 3 := by positivity
            have hRQ : 2 * K + 3 < (Q : ℝ) := by nlinarith [hQ]
            have hsq : (2 * K + 3) ^ 2 ≤ (Q : ℝ) ^ 2 :=
              (sq_le_sq₀ hRpos.le (by positivity)).2 hRQ.le
            have hcoef : 2 * (2 * K + 3) ^ 2 ≤ A := by
              dsimp [A]
              nlinarith [hsq]
            exact div_le_div_of_nonneg_right hcoef (sq_nonneg (n : ℝ))
    · simp [fixedCenterActualUpNonlinearTerm, hsupp,
        fixedCenterActualUpRatio, hcut]
      exact div_nonneg hA.le (sq_nonneg (n : ℝ))
  · simp [fixedCenterActualUpNonlinearTerm, hsupp]
    exact div_nonneg hA.le (sq_nonneg (n : ℝ))

/-- The nonlinear part of the actual up-star correction converges to the
prime-supported nonlinear constant. -/
theorem fixedCenterActualUpQuadratic_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    Tendsto (fun X : ℕ ↦ fixedCenterActualUpQuadratic S c X)
      atTop (𝓝 (nonlinearPrimeConstant S)) := by
  obtain ⟨A, _hA, hsum, hbound⟩ :=
    exists_fixedCenterActualUpNonlinearTerm_bound S hS hc
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun X n ↦ fixedCenterActualUpNonlinearTerm S c X n)
    (g := nonlinearPrimeTerm S)
    (bound := fun n : ℕ ↦ A / (n : ℝ) ^ 2)
    hsum
    (fixedCenterActualUpNonlinearTerm_tendsto S hS hc)
    hbound
  simpa only [fixedCenterActualUpQuadratic_eq_tsum, nonlinearPrimeConstant] using ht

/-- All actual ratios in the moving up-star window are eventually bounded
away from the pole at `1`. -/
theorem eventually_fixedCenterActualUpRatio_le_three_quarters
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      ∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
        fixedCenterActualUpRatio S c X q ≤ (3 / 4 : ℝ) := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_fixedCenterActualUpRatio_sub_model_bound S hS hc
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, 4 * (2 * K + 3) < Q :=
    exists_nat_gt (4 * (2 * K + 3))
  have hheadPoint : ∀ q ∈ Finset.range Q, q.Prime →
      ∀ᶠ X : ℕ in atTop,
        fixedCenterActualUpRatio S c X q ≤ (3 / 4 : ℝ) := by
    intro q _hqQ hqPrime
    have hlim := fixedCenterActualUpRatio_tendsto S hS hc hqPrime.pos
    have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hqPrime.two_le
    have hhalf : (q : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hqTwo)
    have hlt : (q : ℝ)⁻¹ < (3 / 4 : ℝ) := hhalf.trans_lt (by norm_num)
    exact hlim.eventually (isOpen_Iio.mem_nhds hlt) |>.mono fun _ h ↦ h.le
  have hhead : ∀ᶠ X : ℕ in atTop,
      ∀ q ∈ Finset.range Q, q.Prime →
        fixedCenterActualUpRatio S c X q ≤ (3 / 4 : ℝ) := by
    apply eventually_forall_mem_finset (Finset.range Q)
      (fun X q ↦ q.Prime → fixedCenterActualUpRatio S c X q ≤ (3 / 4 : ℝ))
    intro q hq
    by_cases hp : q.Prime
    · exact (hheadPoint q hq hp).mono fun _ h _ ↦ h
    · exact Filter.Eventually.of_forall fun _ hp' ↦ (hp hp').elim
  filter_upwards [hratio, eventually_fixedCenterUpRatioModel_bounds hc, hhead,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with X hratioX hmodelX hheadX hlogX
  intro q hq
  have hqMem := (Finset.mem_filter.mp hq).1
  have hqPrime : q.Prime := (Nat.mem_primesLE.mp hqMem).2
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  by_cases hcut : c * q ≤ Nat.sqrt X
  · by_cases hqQ : q < Q
    · exact hheadX q (Finset.mem_range.2 hqQ) hqPrime
    · have hQq : (Q : ℝ) ≤ q := by exact_mod_cast Nat.le_of_not_gt hqQ
      have hYpos : (0 : ℝ) < Nat.sqrt X := by
        have : 1 ≤ Nat.sqrt X := hqPrime.one_le.trans (Nat.mem_primesLE.mp hqMem).1
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
      have hcOverY : (c : ℝ) / (Nat.sqrt X : ℝ) ≤ (q : ℝ)⁻¹ := by
        rw [div_le_iff₀ hYpos]
        have hcutR : (c : ℝ) * (q : ℝ) ≤ (Nat.sqrt X : ℝ) := by
          exact_mod_cast hcut
        calc
          (c : ℝ) ≤ (Nat.sqrt X : ℝ) / (q : ℝ) :=
            (le_div_iff₀ hqR).2 hcutR
          _ = (q : ℝ)⁻¹ * (Nat.sqrt X : ℝ) := by
            rw [div_eq_mul_inv]
            ring
      have hlogX' : 1 ≤ Real.log (X : ℝ) := by
        simpa [Function.comp_apply] using hlogX
      have hrecipLog : 1 / ((q : ℝ) * Real.log (X : ℝ)) ≤ (q : ℝ)⁻¹ := by
        have hinvLog : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ hlogX'
        calc
          1 / ((q : ℝ) * Real.log (X : ℝ)) =
              (q : ℝ)⁻¹ * (Real.log (X : ℝ))⁻¹ := by
                rw [one_div, mul_inv_rev]
                ring
          _ ≤ (q : ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hinvLog (inv_nonneg.mpr hqR.le)
          _ = (q : ℝ)⁻¹ := by ring
      have hErr := hratioX q hq
      have hmodelLe := (hmodelX q hqMem).2
      have hErrSimple :
          |fixedCenterActualUpRatio S c X q - fixedCenterUpRatioModel c q X| ≤
            2 * K * (q : ℝ)⁻¹ := by
        calc
          |fixedCenterActualUpRatio S c X q - fixedCenterUpRatioModel c q X| ≤
              K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
                (c : ℝ) / (Nat.sqrt X : ℝ)) := hErr
          _ ≤ K * ((q : ℝ)⁻¹ + (q : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left (add_le_add hrecipLog hcOverY) hK.le
          _ = 2 * K * (q : ℝ)⁻¹ := by ring
      have hrLe : fixedCenterActualUpRatio S c X q ≤
          (2 * K + 3) / (q : ℝ) := by
        calc
          fixedCenterActualUpRatio S c X q ≤
              fixedCenterUpRatioModel c q X +
                |fixedCenterActualUpRatio S c X q -
                  fixedCenterUpRatioModel c q X| := by
                    linarith [le_abs_self (fixedCenterActualUpRatio S c X q -
                      fixedCenterUpRatioModel c q X)]
          _ ≤ 3 / (q : ℝ) + 2 * K * (q : ℝ)⁻¹ :=
            add_le_add hmodelLe hErrSimple
          _ = (2 * K + 3) / (q : ℝ) := by
            rw [div_eq_mul_inv]
            ring
      have hquarter : (2 * K + 3) / (q : ℝ) < 1 / 4 := by
        rw [div_lt_iff₀ hqR]
        nlinarith [hQ.trans_le hQq]
      exact hrLe.trans hquarter.le |>.trans (by norm_num)
  · simp [fixedCenterActualUpRatio, hcut]
    norm_num

end

end PrimeStar
