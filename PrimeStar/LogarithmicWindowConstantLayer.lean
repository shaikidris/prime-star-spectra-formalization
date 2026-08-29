import PrimeStar.LogarithmicWindowDownCorrection
import PrimeStar.LogarithmicWindowSpectral

namespace PrimeStar

open Filter Topology
open scoped BigOperators

noncomputable section

theorem eventually_logarithmicWindow_actualUpCorrection_eq
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        fixedCenterActualUpCorrection S (a : ℕ) X =
          4*fixedCenterActualUpLinear S (a : ℕ) X +
          4*fixedCenterActualUpQuadratic S (a : ℕ) X := by
  filter_upwards [eventually_logarithmicWindow_actualUpRatio_le S hS hε]
      with X hcap
  intro a ha
  let Q := (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S)
  rw [fixedCenterActualUpCorrection, fixedCenterActualUpLinear,
    fixedCenterActualUpQuadratic]
  calc
    (∑ q ∈ Q, upStarCorrection (fixedCenterActualUpRatio S (a:ℕ) X q)) =
      ∑ q ∈ Q, (4*fixedCenterActualUpRatio S (a:ℕ) X q +
        4*(fixedCenterActualUpRatio S (a:ℕ) X q)^2 /
          (1-fixedCenterActualUpRatio S (a:ℕ) X q)) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply upStarCorrection_eq_linear_add_quadratic
      linarith [hcap a ha q hq]
    _ = 4 * (∑ q ∈ Q, fixedCenterActualUpRatio S (a:ℕ) X q) +
        4 * (∑ q ∈ Q, (fixedCenterActualUpRatio S (a:ℕ) X q) ^ 2 /
          (1 - fixedCenterActualUpRatio S (a:ℕ) X q)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      simp only [mul_div_assoc]
    _ = _ := by rfl

/-- The formerly open arithmetic predicate in Theorem 9.6. -/
theorem logarithmicWindowCorrectionEvaluation_proved
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    LogarithmicWindowCorrectionEvaluation S ε := by
  intro δ hδ
  have hlinActual := eventually_logarithmicWindow_actualUpLinear_sub_model_close
    S hS hε (show 0 < δ/32 by positivity)
  have hlinModel := eventually_logarithmicWindow_upLinearModel_close
    S hS hε (show 0 < δ/32 by positivity)
  have hquad := eventually_logarithmicWindow_actualUpQuadratic_close
    S hS hε (show 0 < δ/32 by positivity)
  have hdown := eventually_logarithmicWindow_actualDownCorrection_close
    S hS hε (show 0 < δ/4 by positivity)
  filter_upwards [hlinActual, hlinModel, hquad, hdown,
      eventually_logarithmicWindow_actualUpCorrection_eq S hS hε] with
      X hlinActualX hlinModelX hquadX hdownX hsplitX
  intro a ha
  have hla := hlinActualX a ha
  have hlm := hlinModelX (a:ℕ) ha
  have hq := hquadX a ha
  have hd := hdownX a ha
  have hs := hsplitX a ha
  rw [fixedCenterActualCorrection, hs, primeStarKappa]
  have hlinear :
      |(fixedCenterActualUpLinear S (a:ℕ) X -
          Real.log (Real.log (X:ℝ))) -
        (meisselMertensConstant-deletedPrimeReciprocalMass S)| < δ/16 := by
    calc
      _ = |(fixedCenterActualUpLinear S (a:ℕ) X-
              fixedCenterUpLinearModel S (a:ℕ) X) +
            ((fixedCenterUpLinearModel S (a:ℕ) X-
              Real.log (Real.log (X:ℝ))) -
              (meisselMertensConstant-deletedPrimeReciprocalMass S))| := by ring_nf
      _ ≤ |fixedCenterActualUpLinear S (a:ℕ) X-
              fixedCenterUpLinearModel S (a:ℕ) X| +
            |(fixedCenterUpLinearModel S (a:ℕ) X-
              Real.log (Real.log (X:ℝ))) -
              (meisselMertensConstant-deletedPrimeReciprocalMass S)| := abs_add_le _ _
      _ < δ/32+δ/32 := add_lt_add hla hlm
      _ = δ/16 := by ring_nf
  calc
    |((4*fixedCenterActualUpLinear S (a:ℕ) X+
          4*fixedCenterActualUpQuadratic S (a:ℕ) X+
          fixedCenterActualDownCorrection S (a:ℕ) X -
          4*Real.log (Real.log (X:ℝ))) -
        (4*(meisselMertensConstant-deletedPrimeReciprocalMass S+
              nonlinearPrimeConstant S)+centerPrimeCorrection (a:ℕ)))| =
      |4*((fixedCenterActualUpLinear S (a:ℕ) X-
          Real.log (Real.log (X:ℝ)))-
          (meisselMertensConstant-deletedPrimeReciprocalMass S)) +
        4*(fixedCenterActualUpQuadratic S (a:ℕ) X-
          nonlinearPrimeConstant S) +
        (fixedCenterActualDownCorrection S (a:ℕ) X-
          centerPrimeCorrection (a:ℕ))| := by ring_nf
    _ ≤ 4*|((fixedCenterActualUpLinear S (a:ℕ) X-
          Real.log (Real.log (X:ℝ)))-
          (meisselMertensConstant-deletedPrimeReciprocalMass S))| +
        4*|fixedCenterActualUpQuadratic S (a:ℕ) X-
          nonlinearPrimeConstant S| +
        |fixedCenterActualDownCorrection S (a:ℕ) X-
          centerPrimeCorrection (a:ℕ)| := by
      calc
        _ ≤ |4*((fixedCenterActualUpLinear S (a:ℕ) X-
              Real.log (Real.log (X:ℝ)))-
              (meisselMertensConstant-deletedPrimeReciprocalMass S)) +
            4*(fixedCenterActualUpQuadratic S (a:ℕ) X-
              nonlinearPrimeConstant S)| +
            |fixedCenterActualDownCorrection S (a:ℕ) X-
              centerPrimeCorrection (a:ℕ)| := abs_add_le _ _
        _ ≤ (|4*((fixedCenterActualUpLinear S (a:ℕ) X-
              Real.log (Real.log (X:ℝ)))-
              (meisselMertensConstant-deletedPrimeReciprocalMass S))| +
            |4*(fixedCenterActualUpQuadratic S (a:ℕ) X-
              nonlinearPrimeConstant S)|) +
            |fixedCenterActualDownCorrection S (a:ℕ) X-
              centerPrimeCorrection (a:ℕ)| :=
          add_le_add (abs_add_le _ _) (le_refl _)
        _ = _ := by simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ)≤4)]
    _ < 4*(δ/16)+4*(δ/32)+δ/4 := by
      exact add_lt_add (add_lt_add (mul_lt_mul_of_pos_left hlinear (by norm_num))
        (mul_lt_mul_of_pos_left hq (by norm_num))) hd
    _ < δ := by nlinarith

/-- Theorem 9.6 at the manuscript's prescribed ordered eigenvalue, with no
remaining arithmetic-evaluation premise. -/
theorem eventually_logarithmicWindow_ranked_constantLayer_proved
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
        (largePrimePositiveStarOrderedIndex a
            (sqrtCutoff_condition X) haY hd).1 + 1 = arithmeticCenterRank a ∧
          |((arithmeticStarFullEigenvalue a haY hd^2-
              (allowedPrimeCount S (X/(a:ℕ)):ℝ))-
            4*Real.log (Real.log (X:ℝ)))-
            (4*primeStarKappa meisselMertensConstant S+
              centerPrimeCorrection (a:ℕ))| < δ :=
  eventually_logarithmicWindow_ranked_constantLayer_of_remainder
    S hS hε (logarithmicWindowFeshbachRemainderConstant_nonneg)
    (logarithmicWindowOrderedRemainderBound S hS hε)
    (logarithmicWindowCorrectionEvaluation_proved S hS hε)

end

end PrimeStar
