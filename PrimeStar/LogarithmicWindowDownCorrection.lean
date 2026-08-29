import PrimeStar.LogarithmicWindowNonlinearTail

namespace PrimeStar

open Filter Topology
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 3000000

theorem downStarCorrection_inv_sub_bound
    {r : ℝ} {q : ℕ} (hr : 0 < r) (hrCap : r ≤ 199 / 200)
    (hq : q.Prime) :
    |downStarCorrection r⁻¹ - downStarCorrection (q : ℝ)| ≤
      1600 * |r - (q : ℝ)⁻¹| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hrOne : r ≠ 1 := by linarith
  have hqOne : (q : ℝ) ≠ 1 := by exact_mod_cast hq.ne_one
  have halg : downStarCorrection r⁻¹ - downStarCorrection (q : ℝ) =
      -4 * (r - (q : ℝ)⁻¹) / ((1-r) * (1-(q : ℝ)⁻¹)) := by
    unfold downStarCorrection
    field_simp [hr.ne', hrOne, hqR.ne', hqOne]
    ring
  rw [halg, abs_div, abs_mul, abs_mul]
  norm_num
  have hrDen : (1 / 200 : ℝ) ≤ |1-r| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hqInv : (q : ℝ)⁻¹ ≤ 1/2 := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hqTwo)
  have hqDen : (1/2 : ℝ) ≤ |1-(q : ℝ)⁻¹| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hden : (1/400 : ℝ) ≤ |1-r| * |1-(q : ℝ)⁻¹| := by
    calc
      (1/400 : ℝ) = (1/200 : ℝ) * (1/2 : ℝ) := by norm_num
      _ ≤ |1-r| * |1-(q : ℝ)⁻¹| :=
        mul_le_mul hrDen hqDen (by norm_num) (abs_nonneg _)
  have hdenPos : 0 < |1-r| * |1-(q : ℝ)⁻¹| :=
    (by norm_num : (0:ℝ)<1/400).trans_le hden
  rw [div_le_iff₀ hdenPos]
  nlinarith [abs_nonneg (r-(q:ℝ)⁻¹)]

theorem downStarCorrection_eq_alt (q : ℝ) :
    downStarCorrection q = (q-5)/(q-1) := by
  unfold downStarCorrection
  rw [show q-5 = -(5-q) by ring, show q-1 = -(1-q) by ring,
    neg_div_neg_eq]

theorem eventually_logarithmicWindow_actualDownCorrection_close
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        |fixedCenterActualDownCorrection S (a : ℕ) X -
          centerPrimeCorrection (a : ℕ)| < δ := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_logarithmicWindowActualUpRatio_sub_inv_bound S hS hε
  have hsquare := eventually_center_sq_div_log_lt_on_logarithmicWindow
    hε (show 0 < δ/(6400*(K+1)) by positivity)
  have hend := eventually_logarithmicWindow_count_mul_center_div_sqrt_lt
    (∅ : Finset ℕ) hε (show 0 < δ/(6400*(K+1)) by positivity)
  filter_upwards [hratio, hsquare, hend,
      eventually_logarithmicWindow_actualUpRatio_le S hS hε,
      eventually_logarithmicWindow_canonicalDownDegreeRatio_ge S hS hε,
      eventually_logarithmicWindow_largePrimeStarDegree_ge S hS hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε,
      eventually_ge_atTop 4] with
      X hratioX hsquareX hendX hcapX hdownX hdegreeX hcenterX hX
  intro a ha
  have haY := hcenterX (a : ℕ) ha
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hYpos : (0:ℝ) < Nat.sqrt X := by
    exact_mod_cast (Nat.sqrt_pos.2 (by omega : 0 < X))
  have hscalePos : 0 < (X:ℝ)/(16*(a:ℝ)*Real.log (X:ℝ)) := by
    have haPos : (0:ℝ)<a := by exact_mod_cast Vertex.coe_pos a
    positivity
  have hdaPos : 0 < (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) :=
    hscalePos.trans_le (hdegreeX a ha)
  have hterm : ∀ q ∈ (a : ℕ).primeFactors,
      |downStarCorrection
          (fixedCenterArithmeticDegree S ((a : ℕ)/q) X /
            fixedCenterArithmeticDegree S (a : ℕ) X) -
        downStarCorrection (q : ℝ)| ≤
          1600*K*((Real.log (X:ℝ))⁻¹ +
            (a:ℝ)/(Nat.sqrt X:ℝ)) := by
    intro q hq
    let qi : CanonicalDownIndex a := ⟨q,hq⟩
    let b : Vertex S X := canonicalDownTarget a qi
    have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hbLe : (b:ℕ) ≤ (a:ℕ) := Nat.div_le_self _ _
    have hbLeR : (b:ℝ) ≤ (a:ℝ) := by exact_mod_cast hbLe
    have hb : InLogarithmicCenterWindow ε X (b:ℕ) :=
      ⟨Vertex.coe_pos b, hbLeR.trans ha.2⟩
    have hqS : q ∉ S := by
      intro hmem
      exact a.2.2 q hmem (Nat.dvd_of_mem_primeFactors hq)
    have hqY : q ≤ Nat.sqrt X :=
      (Nat.le_of_mem_primeFactors hq).trans haY
    have hqAllowed : q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun p ↦ p ∉ S) := by
      simp [Nat.mem_primesLE, hqPrime, hqS, hqY]
    let r := fixedCenterActualUpRatio S (b:ℕ) X q
    have hrBound := hratioX b hb q hqAllowed
    have hrCap : r ≤ 199/200 := hcapX b hb q hqAllowed
    have hdbRatio := hdownX a ha qi
    have hdbPos : 0 < (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ) := by
      have hp : 0 < (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ) /
          (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
        simpa [b] using (by
          exact (by norm_num : (0:ℝ)<201/200).trans_le hdbRatio)
      rcases (div_pos_iff.mp hp) with hpos | hneg
      · exact hpos.1
      · linarith [hneg.2, hdaPos]
    have hcenterMul : (a:ℕ)*Nat.sqrt X ≤ X :=
      (Nat.mul_le_mul_right (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
    have hbY : (b:ℕ) ≤ Nat.sqrt X := hbLe.trans haY
    have hbMul : (b:ℕ)*Nat.sqrt X ≤ X :=
      (Nat.mul_le_mul_right (Nat.sqrt X) hbLe).trans hcenterMul
    have hdaEq := largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree
      hS a haY ((Nat.le_div_iff_mul_le (Vertex.coe_pos a)).2
        (by simpa [mul_comm] using hcenterMul))
    have hdbEq := largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree
      hS b hbY ((Nat.le_div_iff_mul_le (Vertex.coe_pos b)).2
        (by simpa [mul_comm] using hbMul))
    have hcut : (b:ℕ)*q ≤ Nat.sqrt X := by
      rw [canonicalDownTarget_mul_coe a qi]
      exact haY
    have hrEq : r =
        fixedCenterArithmeticDegree S (a:ℕ) X /
          fixedCenterArithmeticDegree S ((a:ℕ)/q) X := by
      dsimp [r, b, qi]
      rw [fixedCenterActualUpRatio, if_pos hcut]
      rw [canonicalDownTarget_mul_coe a ⟨q, hq⟩]
      rfl
    have hDaPos : 0 < fixedCenterArithmeticDegree S (a:ℕ) X := by
      rw [← hdaEq]
      exact hdaPos
    have hDbPos : 0 < fixedCenterArithmeticDegree S ((a:ℕ)/q) X := by
      change 0 < fixedCenterArithmeticDegree S (b:ℕ) X
      rw [← hdbEq]
      exact hdbPos
    have hrecip :
        fixedCenterArithmeticDegree S ((a:ℕ)/q) X /
            fixedCenterArithmeticDegree S (a:ℕ) X = r⁻¹ := by
      rw [hrEq]
      field_simp [hDaPos.ne', hDbPos.ne']
    rw [hrecip]
    have hrPos : 0 < r := by rw [hrEq]; positivity
    have hlocal : |downStarCorrection r⁻¹-downStarCorrection (q:ℝ)| ≤
        1600*K*((Real.log (X:ℝ))⁻¹+(b:ℝ)/(Nat.sqrt X:ℝ)) := by
      calc
        _ ≤ 1600*|r-(q:ℝ)⁻¹| :=
          downStarCorrection_inv_sub_bound hrPos hrCap hqPrime
        _ ≤ 1600*(K*((Real.log (X:ℝ))⁻¹+(b:ℝ)/(Nat.sqrt X:ℝ))) :=
          mul_le_mul_of_nonneg_left hrBound (by norm_num)
        _ = _ := by ring
    exact hlocal.trans (by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hK.le)
      exact add_le_add (le_refl _) (div_le_div_of_nonneg_right hbLeR hYpos.le))
  rw [fixedCenterActualDownCorrection, centerPrimeCorrection,
    ← Finset.sum_sub_distrib]
  simp_rw [← downStarCorrection_eq_alt]
  let f : ℕ → ℝ := fun q ↦
    downStarCorrection
      (fixedCenterArithmeticDegree S ((a : ℕ)/q) X /
        fixedCenterArithmeticDegree S (a : ℕ) X) -
      downStarCorrection (q : ℝ)
  change |∑ q ∈ (a:ℕ).primeFactors, f q| < δ
  calc
    |∑ q ∈ (a:ℕ).primeFactors, f q| ≤ ∑ q ∈ (a:ℕ).primeFactors, |f q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ (a:ℕ).primeFactors,
        1600*K*((Real.log (X:ℝ))⁻¹+(a:ℝ)/(Nat.sqrt X:ℝ)) :=
      Finset.sum_le_sum fun q hq ↦ by
        simpa [f] using hterm q hq
    _ < δ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcardA : ((a:ℕ).primeFactors.card:ℝ) ≤ 2*(a:ℝ) := by
        have hc : (a:ℕ).primeFactors.card ≤ (Finset.range ((a:ℕ)+1)).card :=
          Finset.card_le_card (fun q hq ↦
            Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_mem_primeFactors hq)))
        have haOne : 1 ≤ (a:ℕ) := ha.1
        have hc' : (a:ℕ).primeFactors.card ≤ (a:ℕ)+1 := by simpa using hc
        exact_mod_cast (hc'.trans (by omega : (a:ℕ)+1 ≤ 2*(a:ℕ)))
      have hcardPi : ((a:ℕ).primeFactors.card:ℝ) ≤
          allowedPrimeCount (∅:Finset ℕ) (Nat.sqrt X) := by
        exact_mod_cast (Finset.card_le_card fun q hq ↦ by
          simp [Nat.mem_primesLE,
            Nat.prime_of_mem_primeFactors hq,
            (Nat.le_of_mem_primeFactors hq).trans haY])
      have hfirst : ((a:ℕ).primeFactors.card:ℝ)*(Real.log (X:ℝ))⁻¹ <
          δ/(3200*(K+1)) := by
        calc
          _ ≤ 2*((a:ℝ)^2/Real.log (X:ℝ)) := by
            rw [div_eq_mul_inv]
            have haOne : (1:ℝ) ≤ a := by exact_mod_cast ha.1
            have haSq : (a:ℝ) ≤ (a:ℝ)^2 := by nlinarith
            have hcardSq : ((a:ℕ).primeFactors.card:ℝ) ≤ 2*(a:ℝ)^2 :=
              hcardA.trans (mul_le_mul_of_nonneg_left haSq (by norm_num))
            calc
              ((a:ℕ).primeFactors.card:ℝ) * (Real.log (X:ℝ))⁻¹ ≤
                  (2*(a:ℝ)^2) * (Real.log (X:ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_right hcardSq
                  (inv_nonneg.mpr hlogX.le)
              _ = 2 * ((a:ℝ)^2 * (Real.log (X:ℝ))⁻¹) := by ring
          _ < 2*(δ/(6400*(K+1))) :=
            mul_lt_mul_of_pos_left (hsquareX (a:ℕ) ha) (by norm_num)
          _ = δ/(3200*(K+1)) := by
            field_simp [show 0<K+1 by linarith]
            norm_num
      have hsecond : ((a:ℕ).primeFactors.card:ℝ)*
          ((a:ℝ)/(Nat.sqrt X:ℝ)) < δ/(6400*(K+1)) := by
        exact (mul_le_mul_of_nonneg_right hcardPi (by positivity)).trans_lt
          (hendX (a:ℕ) ha)
      have hsum : ((a:ℕ).primeFactors.card:ℝ)*
          ((Real.log (X:ℝ))⁻¹+(a:ℝ)/(Nat.sqrt X:ℝ)) <
            3*δ/(6400*(K+1)) := by
        calc
          _ = ((a:ℕ).primeFactors.card:ℝ)*(Real.log (X:ℝ))⁻¹ +
              ((a:ℕ).primeFactors.card:ℝ)*((a:ℝ)/(Nat.sqrt X:ℝ)) := by ring
          _ < δ/(3200*(K+1)) + δ/(6400*(K+1)) :=
            add_lt_add hfirst hsecond
          _ = 3*δ/(6400*(K+1)) := by
            field_simp [show 0<K+1 by linarith]
            norm_num
      have hratioK : K/(K+1) < 1 := by
        rw [div_lt_one (by linarith : 0<K+1)]
        linarith
      calc
        ((a:ℕ).primeFactors.card:ℝ) *
            (1600*K*((Real.log (X:ℝ))⁻¹+(a:ℝ)/(Nat.sqrt X:ℝ))) =
          1600*K*(((a:ℕ).primeFactors.card:ℝ)*
            ((Real.log (X:ℝ))⁻¹+(a:ℝ)/(Nat.sqrt X:ℝ))) := by ring
        _ < 1600*K*(3*δ/(6400*(K+1))) :=
          mul_lt_mul_of_pos_left hsum (by positivity)
        _ = (3*δ/4)*(K/(K+1)) := by
          field_simp [show 0<K+1 by linarith]
          ring
        _ < 3*δ/4 := by
          simpa only [mul_one] using
            mul_lt_mul_of_pos_left hratioK (by positivity : 0<3*δ/4)
        _ < δ := by nlinarith

end

end PrimeStar
