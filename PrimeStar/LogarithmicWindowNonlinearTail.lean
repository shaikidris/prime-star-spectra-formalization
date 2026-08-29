import PrimeStar.LogarithmicWindowUpRatio
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Uniform nonlinear up-star tail on the logarithmic window

The centre now moves with the scale.  We therefore package all admissible
scale--centre pairs into one directed family and apply Tannery's theorem to
that family.  This is the uniform head--tail step missing from the fixed-centre
constant-layer argument.
-/

namespace PrimeStar

open Filter Topology Asymptotics
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 3000000

/-- A scale together with one allowed vertex at that scale. -/
abbrev LogarithmicWindowPoint (S : Finset ℕ) :=
  Σ X : ℕ, Vertex S X

/-- The filter which sends the scale of a scale--centre pair to infinity. -/
def logarithmicWindowPointFilter (S : Finset ℕ) :
    Filter (LogarithmicWindowPoint S) :=
  Filter.comap (fun z ↦ z.1) atTop

/-- Outside the prescribed window we use the limiting summand.  Consequently
convergence along `logarithmicWindowPointFilter` is exactly a uniform statement
over all centres which are inside the window. -/
def logarithmicWindowActualUpNonlinearTerm
    (S : Finset ℕ) (ε : ℝ) (z : LogarithmicWindowPoint S) (n : ℕ) : ℝ :=
  by
    classical
    exact if InLogarithmicCenterWindow ε z.1 (z.2 : ℕ) then
      fixedCenterActualUpNonlinearTerm S (z.2 : ℕ) z.1 n
    else nonlinearPrimeTerm S n

/-- Every actual up-star ratio stays uniformly away from its pole at `1`. -/
theorem eventually_logarithmicWindow_actualUpRatio_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
          fixedCenterActualUpRatio S (a : ℕ) X q ≤ (199 / 200 : ℝ) := by
  filter_upwards [eventually_logarithmicWindow_canonicalUpDegreeRatio_le S hS hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε] with X hcap hcenter
  intro a ha q hq
  have hcenterMul : (a : ℕ) * Nat.sqrt X ≤ X :=
    (Nat.mul_le_mul_right (Nat.sqrt X) (hcenter (a : ℕ) ha)).trans (Nat.sqrt_le X)
  have hqCanonical : q ∈ canonicalUpPrimeLabels S X (Nat.sqrt X) a := by
    rw [canonicalUpPrimeLabels_eq_allowedPrimeSet hcenterMul]
    exact hq
  let qi : CanonicalUpIndex S X (Nat.sqrt X) a := ⟨q, hqCanonical⟩
  have h := hcap a ha qi
  rw [canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio hS a
    (hcenter (a : ℕ) ha) qi] at h
  exact h

/-- A fixed prime label has the reciprocal-prime limit uniformly over all
centres in the logarithmic window. -/
theorem eventually_logarithmicWindow_actualUpRatio_fixedLabel_close
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {q : ℕ} (hqPrime : q.Prime) (hqS : q ∉ S) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        |fixedCenterActualUpRatio S (a : ℕ) X q - (q : ℝ)⁻¹| < δ := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_logarithmicWindowActualUpRatio_sub_model_bound S hS hε
  have hlogInv : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ))⁻¹) atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hlogSmall : ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ))⁻¹ < δ / (4 * (K + 1) * ((q : ℝ) + 1) *
        (|Real.log (q : ℝ)| + 1)) :=
    (tendsto_order.1 hlogInv).2 _ (by positivity)
  have hcenterSmall0 :=
    eventually_logarithmicWindow_count_mul_center_div_sqrt_lt
      (∅ : Finset ℕ) hε (show 0 < δ / (4 * (K + 1)) by positivity)
  filter_upwards [hratio, hlogSmall, hcenterSmall0,
      eventually_logarithmicWindow_logSqrt_gap_bounds hε,
      eventually_logarithmicWindow_logScale_between hε,
      tendsto_natSqrt_atTop.eventually_ge_atTop q,
      tendsto_natSqrt_atTop.eventually_ge_atTop 2,
      eventually_ge_atTop 4] with
      X hratioX hlogX hcenterX hlogY hlogL hqY htwoY hX
  intro a ha
  have hqmem : q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun r ↦ r ∉ S) := by
    simp [Nat.mem_primesLE, hqPrime, hqS, hqY]
  have hratioBound := hratioX a ha q hqmem
  have hcountOne : (1 : ℝ) ≤ allowedPrimeCount (∅ : Finset ℕ) (Nat.sqrt X) := by
    have htwoMem : 2 ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun p ↦ p ∉ (∅ : Finset ℕ)) := by
      simp [Nat.mem_primesLE, Nat.prime_two, htwoY]
    exact_mod_cast Finset.one_le_card.mpr ⟨2, htwoMem⟩
  have hYpos : (0 : ℝ) < Nat.sqrt X := by exact_mod_cast (show 0 < Nat.sqrt X by omega)
  have haOverY : (a : ℝ) / (Nat.sqrt X : ℝ) < δ / (4 * (K + 1)) := by
    have hnonneg : 0 ≤ (a : ℝ) / (Nat.sqrt X : ℝ) := by positivity
    exact (le_mul_of_one_le_left hnonneg hcountOne).trans_lt (hcenterX (a : ℕ) ha)
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hgap : Real.log (X : ℝ) / 3 ≤
      fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ) := by
    have hlogq : Real.log (q : ℝ) ≤ Real.log (Nat.sqrt X : ℝ) :=
      Real.log_le_log hqR (by exact_mod_cast hqY)
    exact (hlogY (a : ℕ) ha).2.2.trans (sub_le_sub_left hlogq _)
  have hmodelDiff :
      |fixedCenterUpRatioModel (a : ℕ) q X - (q : ℝ)⁻¹| =
        |Real.log (q : ℝ)| /
          ((q : ℝ) * (fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ))) := by
    have hden : fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ) ≠ 0 := by
      linarith
    have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
    have halg :
        fixedCenterUpRatioModel (a : ℕ) q X - (q : ℝ)⁻¹ =
          Real.log (q : ℝ) /
            ((q : ℝ) * (fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ))) := by
      simp only [fixedCenterUpRatioModel]
      field_simp [hq0, hden]
      ring
    rw [halg, abs_div, abs_mul, abs_of_pos hqR, abs_of_pos (by linarith :
      0 < fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ))]
  have hmodelSmall :
      |fixedCenterUpRatioModel (a : ℕ) q X - (q : ℝ)⁻¹| < δ / 2 := by
    rw [hmodelDiff]
    have hdenLower : (q : ℝ) * (Real.log (X : ℝ) / 3) ≤
        (q : ℝ) * (fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hgap hqR.le
    have hdenPos : 0 < (q : ℝ) *
        (fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ)) :=
      mul_pos hqR (by linarith)
    have hrough : |Real.log (q : ℝ)| /
        ((q : ℝ) * (fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ))) ≤
        3 * |Real.log (q : ℝ)| * (Real.log (X : ℝ))⁻¹ := by
      rw [div_eq_mul_inv]
      have hinv :
          ((q : ℝ) * (fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ)))⁻¹ ≤
            ((q : ℝ) * (Real.log (X : ℝ) / 3))⁻¹ := by
        simpa only [one_div] using
          (one_div_le_one_div_of_le
            (by positivity : (0 : ℝ) < (q : ℝ) * (Real.log (X : ℝ) / 3))
            hdenLower)
      calc
        |Real.log (q : ℝ)| *
            ((q : ℝ) * (fixedCenterLogScale (a : ℕ) X - Real.log (q : ℝ)))⁻¹ ≤
          |Real.log (q : ℝ)| * ((q : ℝ) * (Real.log (X : ℝ) / 3))⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
        _ = 3 * |Real.log (q : ℝ)| * (q : ℝ)⁻¹ *
              (Real.log (X : ℝ))⁻¹ := by
          field_simp [hqR.ne', hlogXpos.ne']
        _ ≤ 3 * |Real.log (q : ℝ)| * (Real.log (X : ℝ))⁻¹ := by
          have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqPrime.one_le
          have hqinv : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hqOne
          calc
            3 * |Real.log (q : ℝ)| * (q : ℝ)⁻¹ *
                (Real.log (X : ℝ))⁻¹ =
              (3 * |Real.log (q : ℝ)| * (Real.log (X : ℝ))⁻¹) *
                (q : ℝ)⁻¹ := by ring
            _ ≤ (3 * |Real.log (q : ℝ)| * (Real.log (X : ℝ))⁻¹) * 1 :=
              mul_le_mul_of_nonneg_left hqinv (by positivity)
            _ = 3 * |Real.log (q : ℝ)| * (Real.log (X : ℝ))⁻¹ := by ring
    have hKone : (1 : ℝ) ≤ K + 1 := by linarith
    have hqThree : (3 : ℝ) ≤ (q : ℝ) + 1 := by
      exact_mod_cast (Nat.add_le_add_right hqPrime.two_le 1)
    have hprod : (3 : ℝ) ≤ (K + 1) * ((q : ℝ) + 1) := by
      calc
        (3 : ℝ) = 1 * 3 := by ring
        _ ≤ (K + 1) * ((q : ℝ) + 1) :=
          mul_le_mul hKone hqThree (by norm_num) (by positivity)
    let D : ℝ := 4 * (K + 1) * ((q : ℝ) + 1) *
      (|Real.log (q : ℝ)| + 1)
    have hDpos : 0 < D := by dsimp [D]; positivity
    have hcoef : 6 * |Real.log (q : ℝ)| ≤ D := by
      calc
        6 * |Real.log (q : ℝ)| ≤ 12 * (|Real.log (q : ℝ)| + 1) := by
          nlinarith [abs_nonneg (Real.log (q : ℝ))]
        _ = 4 * 3 * (|Real.log (q : ℝ)| + 1) := by ring
        _ ≤ 4 * ((K + 1) * ((q : ℝ) + 1)) *
              (|Real.log (q : ℝ)| + 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod (by norm_num)) (by positivity)
        _ = D := by dsimp [D]; ring
    have hDsmall : D * (Real.log (X : ℝ))⁻¹ < δ := by
      calc
        D * (Real.log (X : ℝ))⁻¹ < D * (δ / D) := by
          exact mul_lt_mul_of_pos_left hlogX hDpos
        _ = δ := by field_simp [hDpos.ne']
    have hcoefSmall : 6 * |Real.log (q : ℝ)| *
        (Real.log (X : ℝ))⁻¹ < δ :=
      (mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr hlogXpos.le)).trans_lt hDsmall
    exact hrough.trans_lt (by nlinarith)
  have hratioSmall :
      |fixedCenterActualUpRatio S (a : ℕ) X q -
        fixedCenterUpRatioModel (a : ℕ) q X| < δ / 2 := by
    calc
      |fixedCenterActualUpRatio S (a : ℕ) X q -
          fixedCenterUpRatioModel (a : ℕ) q X| ≤
        K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
          (a : ℝ) / (Nat.sqrt X : ℝ)) := hratioBound
      _ < δ / 2 := by
        have hrecip : 1 / ((q : ℝ) * Real.log (X : ℝ)) <
            δ / (4 * (K + 1)) := by
          rw [one_div, mul_inv_rev]
          have hqinv : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hqPrime.one_le)
          calc
            (Real.log (X : ℝ))⁻¹ * (q : ℝ)⁻¹ ≤
                (Real.log (X : ℝ))⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left hqinv (inv_nonneg.mpr hlogXpos.le)
            _ = (Real.log (X : ℝ))⁻¹ := by ring
            _ < δ / (4 * (K + 1)) := by
              have hdenLe : 4 * (K + 1) ≤
                  4 * (K + 1) * ((q : ℝ) + 1) *
                    (|Real.log (q : ℝ)| + 1) := by
                have hqFactor : (1 : ℝ) ≤ (q : ℝ) + 1 := by nlinarith [hqR]
                have hlogFactor : (1 : ℝ) ≤ |Real.log (q : ℝ)| + 1 := by
                  linarith [abs_nonneg (Real.log (q : ℝ))]
                calc
                  4 * (K + 1) = 4 * (K + 1) * 1 * 1 := by ring
                  _ ≤ 4 * (K + 1) * ((q : ℝ) + 1) *
                      (|Real.log (q : ℝ)| + 1) := by
                    gcongr
              exact hlogX.trans_le
                (div_le_div_of_nonneg_left hδ.le (by positivity) hdenLe)
        have hsum : 1 / ((q : ℝ) * Real.log (X : ℝ)) +
            (a : ℝ) / (Nat.sqrt X : ℝ) < δ / (2 * (K + 1)) := by
          calc
            1 / ((q : ℝ) * Real.log (X : ℝ)) +
                (a : ℝ) / (Nat.sqrt X : ℝ) <
              δ / (4 * (K + 1)) + δ / (4 * (K + 1)) :=
                add_lt_add hrecip haOverY
            _ = δ / (2 * (K + 1)) := by
              field_simp [show 0 < K + 1 by linarith]
              norm_num
        have hKfrac : K / (K + 1) < 1 := by
          rw [div_lt_one (by linarith : 0 < K + 1)]
          linarith
        calc
          K * (1 / ((q : ℝ) * Real.log (X : ℝ)) +
              (a : ℝ) / (Nat.sqrt X : ℝ)) < K * (δ / (2 * (K + 1))) :=
            mul_lt_mul_of_pos_left hsum hK
          _ = (δ / 2) * (K / (K + 1)) := by
            field_simp [show 0 < K + 1 by linarith]
          _ < δ / 2 := by
            simpa only [mul_one] using mul_lt_mul_of_pos_left hKfrac (by positivity : 0 < δ / 2)
  calc
    |fixedCenterActualUpRatio S (a : ℕ) X q - (q : ℝ)⁻¹| =
        |(fixedCenterActualUpRatio S (a : ℕ) X q -
          fixedCenterUpRatioModel (a : ℕ) q X) +
          (fixedCenterUpRatioModel (a : ℕ) q X - (q : ℝ)⁻¹)| := by ring
    _ ≤
        |fixedCenterActualUpRatio S (a : ℕ) X q -
          fixedCenterUpRatioModel (a : ℕ) q X| +
        |fixedCenterUpRatioModel (a : ℕ) q X - (q : ℝ)⁻¹| := abs_add_le _ _
    _ < δ := by nlinarith [hratioSmall, hmodelSmall]

/-- The nonlinear summands admit one summable `1/n²` majorant, uniformly in
both the scale and every centre in the logarithmic window. -/
theorem exists_logarithmicWindowActualUpNonlinearTerm_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 2 ≤ A ∧ Summable (fun n : ℕ ↦ A / (n : ℝ) ^ 2) ∧
      ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
        InLogarithmicCenterWindow ε X (a : ℕ) → ∀ n : ℕ,
          ‖fixedCenterActualUpNonlinearTerm S (a : ℕ) X n‖ ≤
            A / (n : ℝ) ^ 2 := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_logarithmicWindowActualUpRatio_sub_model_bound S hS hε
  let C : ℝ := 2 * K + 3
  let A : ℝ := 200 * C ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hsum : Summable (fun n : ℕ ↦ A / (n : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left A
  have hAtwo : (2 : ℝ) ≤ A := by
    dsimp [A, C]
    nlinarith [sq_nonneg (2 * K + 3)]
  refine ⟨A, hAtwo, hsum, ?_⟩
  filter_upwards [hratio, eventually_logarithmicWindowUpRatioModel_bounds hε,
      eventually_logarithmicWindow_actualUpRatio_le S hS hε,
      eventually_logarithmicWindow_largePrimeStarDegree_ge S hS hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
      eventually_ge_atTop 4] with
      X hratioX hmodelX hcapX hdegreeX hcenterX hlogX hX
  intro a ha n
  by_cases hsupp : n.Prime ∧ n ∉ S ∧ n ≤ Nat.sqrt X
  · have hnPrime := hsupp.1
    have hnPos := hnPrime.pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hnAllowed : n ∈
        (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S) := by
      simp [Nat.mem_primesLE, hsupp]
    by_cases hcut : (a : ℕ) * n ≤ Nat.sqrt X
    · have hYpos : (0 : ℝ) < Nat.sqrt X := by
        exact_mod_cast (show 0 < Nat.sqrt X by omega)
      have hmodel := (hmodelX (a : ℕ) ha n
        (Finset.mem_filter.mp hnAllowed).1)
      have hErr := hratioX a ha n hnAllowed
      have haOverY : (a : ℝ) / (Nat.sqrt X : ℝ) ≤ (n : ℝ)⁻¹ := by
        rw [div_le_iff₀ hYpos]
        have hcutR : (a : ℝ) * (n : ℝ) ≤ (Nat.sqrt X : ℝ) := by
          exact_mod_cast hcut
        calc
          (a : ℝ) ≤ (Nat.sqrt X : ℝ) / (n : ℝ) :=
            (le_div_iff₀ hnR).2 hcutR
          _ = (n : ℝ)⁻¹ * (Nat.sqrt X : ℝ) := by
            rw [div_eq_mul_inv]
            ring
      have hrecipLog : 1 / ((n : ℝ) * Real.log (X : ℝ)) ≤ (n : ℝ)⁻¹ := by
        have hlogOne : 1 ≤ Real.log (X : ℝ) := by
          simpa [Function.comp_apply] using hlogX
        have hinvLog : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ hlogOne
        calc
          1 / ((n : ℝ) * Real.log (X : ℝ)) =
              (n : ℝ)⁻¹ * (Real.log (X : ℝ))⁻¹ := by
                simp only [one_div, mul_inv_rev]
                ring
          _ ≤ (n : ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hinvLog (inv_nonneg.mpr hnR.le)
          _ = (n : ℝ)⁻¹ := by ring
      have hErrSimple :
          |fixedCenterActualUpRatio S (a : ℕ) X n -
              fixedCenterUpRatioModel (a : ℕ) n X| ≤
            2 * K * (n : ℝ)⁻¹ := by
        calc
          _ ≤ K * (1 / ((n : ℝ) * Real.log (X : ℝ)) +
              (a : ℝ) / (Nat.sqrt X : ℝ)) := hErr
          _ ≤ K * ((n : ℝ)⁻¹ + (n : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left (add_le_add hrecipLog haOverY) hK.le
          _ = 2 * K * (n : ℝ)⁻¹ := by ring
      let r := fixedCenterActualUpRatio S (a : ℕ) X n
      have haY := hcenterX (a : ℕ) ha
      have hYXa : Nat.sqrt X ≤ X / (a : ℕ) := by
        apply (Nat.le_div_iff_mul_le (Vertex.coe_pos a)).2
        simpa [mul_comm] using
          (Nat.mul_le_mul_right (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
      have hdegreeEq := largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree
        hS a haY hYXa
      have hDpos : 0 < fixedCenterArithmeticDegree S (a : ℕ) X := by
        rw [← hdegreeEq]
        have hlower := hdegreeX a ha
        have hnum : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
        have hdenom : 0 < 16 * (a : ℝ) * Real.log (X : ℝ) := by
          have haPos : (0 : ℝ) < a := by exact_mod_cast Vertex.coe_pos a
          have hlogPos : 0 < Real.log (X : ℝ) := lt_of_lt_of_le zero_lt_one hlogX
          positivity
        exact (div_pos hnum hdenom).trans_le hlower
      have hrNonneg : 0 ≤ r :=
        fixedCenterActualUpRatio_nonneg S (Vertex.coe_pos a) hnPos hDpos
      have hrAbs : |r| ≤ C / (n : ℝ) := by
        have hrUpper : r ≤ fixedCenterUpRatioModel (a : ℕ) n X +
            |r - fixedCenterUpRatioModel (a : ℕ) n X| := by
          linarith [le_abs_self (r - fixedCenterUpRatioModel (a : ℕ) n X)]
        rw [abs_le]
        constructor
        · have hleft : -(C / (n : ℝ)) ≤ 0 :=
            neg_nonpos.mpr (div_nonneg hC.le hnR.le)
          exact hleft.trans hrNonneg
        · calc
            r ≤ fixedCenterUpRatioModel (a : ℕ) n X +
                |r - fixedCenterUpRatioModel (a : ℕ) n X| := hrUpper
            _ ≤ 3 / (n : ℝ) + 2 * K * (n : ℝ)⁻¹ :=
              add_le_add hmodel.2 hErrSimple
            _ = C / (n : ℝ) := by dsimp [C]; rw [div_eq_mul_inv]; ring
      have hrCap : r ≤ (199 / 200 : ℝ) := hcapX a ha n hnAllowed
      have hden : (1 / 200 : ℝ) ≤ |1 - r| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      rw [Real.norm_eq_abs, fixedCenterActualUpNonlinearTerm, if_pos hsupp,
        abs_div, abs_pow]
      have hdenPos : 0 < |1 - r| := (by norm_num : (0 : ℝ) < 1 / 200).trans_le hden
      calc
        |r| ^ 2 / |1 - r| ≤ |r| ^ 2 / (1 / 200 : ℝ) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
        _ = 200 * |r| ^ 2 := by ring
        _ ≤ 200 * (C / (n : ℝ)) ^ 2 := by
          gcongr
        _ = A / (n : ℝ) ^ 2 := by
          dsimp [A]
          rw [div_pow]
          ring
    · simp [fixedCenterActualUpNonlinearTerm, hsupp,
        fixedCenterActualUpRatio, hcut]
      exact div_nonneg hA.le (sq_nonneg (n : ℝ))
  · simp [fixedCenterActualUpNonlinearTerm, hsupp]
    exact div_nonneg hA.le (sq_nonneg (n : ℝ))

/-- The actual ratio inside the moving window, extended by its limiting value
outside that window. -/
def logarithmicWindowActualUpRatioTerm
    (S : Finset ℕ) (ε : ℝ) (q : ℕ) (z : LogarithmicWindowPoint S) : ℝ := by
  classical
  exact if InLogarithmicCenterWindow ε z.1 (z.2 : ℕ) then
    fixedCenterActualUpRatio S (z.2 : ℕ) z.1 q
  else (q : ℝ)⁻¹

theorem logarithmicWindowActualUpRatioTerm_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hqPrime : q.Prime) (hqS : q ∉ S) :
    Tendsto (logarithmicWindowActualUpRatioTerm S ε q)
      (logarithmicWindowPointFilter S) (nhds (q : ℝ)⁻¹) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hclose := eventually_logarithmicWindow_actualUpRatio_fixedLabel_close
    S hS hε hδ hqPrime hqS
  rw [logarithmicWindowPointFilter, Filter.eventually_comap]
  filter_upwards [hclose] with X hX
  intro z hz
  rcases z with ⟨X', a⟩
  simp only at hz
  subst X'
  by_cases ha : InLogarithmicCenterWindow ε X (a : ℕ)
  · simpa [logarithmicWindowActualUpRatioTerm, ha, Real.dist_eq] using hX a ha
  · simp [logarithmicWindowActualUpRatioTerm, ha, hδ]

theorem logarithmicWindowActualUpNonlinearTerm_tendsto
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Tendsto (fun z ↦ logarithmicWindowActualUpNonlinearTerm S ε z n)
      (logarithmicWindowPointFilter S) (nhds (nonlinearPrimeTerm S n)) := by
  by_cases hnPrime : n.Prime
  · by_cases hnS : n ∈ S
    · simpa [logarithmicWindowActualUpNonlinearTerm,
        fixedCenterActualUpNonlinearTerm, nonlinearPrimeTerm, hnPrime, hnS] using
          (tendsto_const_nhds : Tendsto (fun _ : LogarithmicWindowPoint S ↦ (0 : ℝ))
            (logarithmicWindowPointFilter S) (nhds 0))
    · have hratio := logarithmicWindowActualUpRatioTerm_tendsto
        S hS hε hnPrime hnS
      have hinvNe : (n : ℝ)⁻¹ ≠ 1 := by
        rw [inv_ne_one]
        exact_mod_cast hnPrime.ne_one
      have hcont : ContinuousAt (fun r : ℝ ↦ r ^ 2 / (1 - r)) (n : ℝ)⁻¹ :=
        (continuousAt_id.pow 2).div (continuousAt_const.sub continuousAt_id)
          (sub_ne_zero.mpr hinvNe.symm)
      have hlim := hcont.tendsto.comp hratio
      have hvalue : ((n : ℝ)⁻¹) ^ 2 / (1 - (n : ℝ)⁻¹) =
          nonlinearPrimeTerm S n := by
        rw [nonlinearPrimeTerm, if_pos ⟨hnPrime, hnS⟩]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnPrime.pos.ne'
        have hn1 : (n : ℝ) ≠ 1 := by exact_mod_cast hnPrime.ne_one
        field_simp [hn0, hn1]
      rw [hvalue] at hlim
      apply hlim.congr'
      show ∀ᶠ z : LogarithmicWindowPoint S in logarithmicWindowPointFilter S,
        ((fun r : ℝ ↦ r ^ 2 / (1 - r)) ∘
          logarithmicWindowActualUpRatioTerm S ε n) z =
            logarithmicWindowActualUpNonlinearTerm S ε z n
      rw [logarithmicWindowPointFilter, Filter.eventually_comap]
      filter_upwards [tendsto_natSqrt_atTop.eventually_ge_atTop n] with X hnX
      intro z hz
      rcases z with ⟨X', a⟩
      simp only at hz
      subst X'
      by_cases ha : InLogarithmicCenterWindow ε X (a : ℕ)
      · simp [logarithmicWindowActualUpNonlinearTerm,
          logarithmicWindowActualUpRatioTerm, fixedCenterActualUpNonlinearTerm,
          ha, hnPrime, hnS, hnX]
      · simpa [logarithmicWindowActualUpNonlinearTerm,
          logarithmicWindowActualUpRatioTerm, ha] using hvalue
  · simpa [logarithmicWindowActualUpNonlinearTerm,
      fixedCenterActualUpNonlinearTerm, nonlinearPrimeTerm, hnPrime] using
        (tendsto_const_nhds : Tendsto (fun _ : LogarithmicWindowPoint S ↦ (0 : ℝ))
          (logarithmicWindowPointFilter S) (nhds 0))

/-- The nonlinear actual up-star correction converges uniformly throughout
the logarithmic centre window. -/
theorem eventually_logarithmicWindow_actualUpQuadratic_close
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        |fixedCenterActualUpQuadratic S (a : ℕ) X - nonlinearPrimeConstant S| < δ := by
  obtain ⟨A, hA2, hsum, hbound⟩ :=
    exists_logarithmicWindowActualUpNonlinearTerm_bound S hS hε
  have hdom : ∀ᶠ z : LogarithmicWindowPoint S in logarithmicWindowPointFilter S,
      ∀ n : ℕ, ‖logarithmicWindowActualUpNonlinearTerm S ε z n‖ ≤ A / (n : ℝ)^2 := by
    rw [logarithmicWindowPointFilter, Filter.eventually_comap]
    filter_upwards [hbound] with X hX
    intro z hz n
    rcases z with ⟨X', a⟩
    simp only at hz
    subst X'
    by_cases ha : InLogarithmicCenterWindow ε X (a : ℕ)
    · simpa [logarithmicWindowActualUpNonlinearTerm, ha] using hX a ha n
    · rw [logarithmicWindowActualUpNonlinearTerm]
      simp only [ha, if_false, Real.norm_eq_abs,
        abs_of_nonneg (nonlinearPrimeTerm_nonneg S n)]
      exact (nonlinearPrimeTerm_le_two_div_sq S n).trans
        (by
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right hA2 (inv_nonneg.mpr (sq_nonneg (n : ℝ))))
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun z n ↦ logarithmicWindowActualUpNonlinearTerm S ε z n)
    (g := nonlinearPrimeTerm S)
    (bound := fun n : ℕ ↦ A / (n : ℝ)^2)
    hsum (logarithmicWindowActualUpNonlinearTerm_tendsto S hS hε) hdom
  rw [Metric.tendsto_nhds] at ht
  have hev := ht δ hδ
  rw [logarithmicWindowPointFilter, Filter.eventually_comap] at hev
  filter_upwards [hev] with X hX
  intro a ha
  have hz := hX ⟨X, a⟩ rfl
  simpa [logarithmicWindowActualUpNonlinearTerm, ha,
    fixedCenterActualUpQuadratic_eq_tsum, nonlinearPrimeConstant,
    Real.dist_eq] using hz

end

end PrimeStar
