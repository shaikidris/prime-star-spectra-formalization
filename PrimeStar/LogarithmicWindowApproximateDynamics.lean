import PrimeStar.LogarithmicWindowDynamics
import PrimeStar.LogarithmicWindowFeshbachRemainder

/-!
# Arithmetic-frequency dynamics on the logarithmic window

The exact-frequency centre--shell evolution is already uniform for all real
times.  This module replaces that exact eigenfrequency by the explicit
first-exit frequency

`sqrt (pi_S (X / a) + fixedCenterActualCorrection S a X)`.

The additional phase error is the source-weighted Feshbach remainder divided
by the sum of the two positive frequencies.  This is the standalone formal
counterpart of the second estimate in manuscript Corollary 9.9.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

/-- The explicit first-exit approximation to the ordered eigenfrequency. -/
def logarithmicWindowApproximateFrequency
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) : ℝ :=
  Real.sqrt ((allowedPrimeCount S (X / (a : ℕ)) : ℝ) +
    fixedCenterActualCorrection S (a : ℕ) X)

/-- Uniform positivity and square-to-frequency conversion for the explicit
first-exit frequency.  The denominator is retained exactly rather than
replaced by its asymptotic lower bound. -/
theorem eventually_logarithmicWindow_actualCorrection_frequency_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
          let lam := arithmeticStarFullEigenvalue a haY hd
          let F := (allowedPrimeCount S (X / (a : ℕ)) : ℝ) +
            fixedCenterActualCorrection S (a : ℕ) X
          0 < lam ∧ 0 < F ∧
            |lam - Real.sqrt F| ≤
              (logarithmicWindowFeshbachRemainderConstant *
                  ((a : ℝ) ^ 2 / Real.log (X : ℝ))) /
                (lam + Real.sqrt F) := by
  classical
  let C := logarithmicWindowFeshbachRemainderConstant
  have hC : 0 < C := by
    dsimp [C, logarithmicWindowFeshbachRemainderConstant]
    positivity
  have hsmallError :=
    eventually_center_sq_div_log_lt_on_logarithmicWindow hε
      (show 0 < 1 / (2 * C) by positivity)
  filter_upwards [
      eventually_logarithmicWindow_feshbachScaleBundle hε,
      eventually_logarithmicWindow_zeroDegreeGap S hS hε,
      eventually_logarithmicWindow_otherStarDegreeGap S hS hε,
      eventually_sqrtCutoff_smallPrime_apply_le_tuned,
      logarithmicWindowOrderedRemainderBound S hS hε,
      hsmallError,
      eventually_ge_atTop 4]
      with X hscales hzeroX hdegreeX hresidual hremX hsmallX hX
  intro a ha haY hd
  let Y : ℕ := Nat.sqrt X
  let mu : ℝ := √(largePrimeStarDegree S X Y a : ℝ)
  let gamma : ℝ := logarithmicWindowDegreeGapScale (a : ℕ) X
  let eta : ℝ := sqrtCutoffResidualScale X
  let lam : ℝ := arithmeticStarFullEigenvalue a haY hd
  let F : ℝ := (allowedPrimeCount S (X / (a : ℕ)) : ℝ) +
    fixedCenterActualCorrection S (a : ℕ) X
  let E : ℝ := C * ((a : ℝ) ^ 2 / Real.log (X : ℝ))
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  obtain ⟨heta, hlarge, _hR2, _hR2small, _hAsmall, _hetaR2⟩ :=
    hscales (a : ℕ) ha
  have hzero : gamma ≤ mu := by
    simpa [gamma, mu, Y] using hzeroX a ha
  have hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ a →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |mu - √(largePrimeStarDegree S X Y b : ℝ)| := by
    intro b hbY hba hbd
    simpa [gamma, mu, Y] using
      hdegreeX a ha b (by simpa [Y] using hbY) hba hbd
  have hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖ := by
    intro x
    simpa [Y, eta, sqrtCutoffResidualScale,
      sqrtCutoffResidualConstant] using hresidual S x
  have hgamma : 0 < gamma :=
    lt_of_lt_of_le (mul_pos (by norm_num) heta) hlarge
  have hsmall : 2 * eta < gamma := by nlinarith
  have hmatch := primeCover_ordered_arithmeticStarEigenpair_withOverlap_of_degreeGap
    a (sqrtCutoff_condition X) haY hd gamma eta hgamma.le hzero hdegree hH hsmall
  have hnear : |lam - mu| ≤ eta := by
    simpa [lam, mu, Y, arithmeticStarFullEigenvalue] using hmatch.2.2.2.1
  have hmuOne : (1 : ℝ) ≤ mu := by
    have hdegreeOne : (1 : ℝ) ≤
        (largePrimeStarDegree S X Y a : ℝ) := by exact_mod_cast hd
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hdegreeOne
  have hetaMu : 16 * eta ≤ mu := hlarge.trans hzero
  have hlamLower : (15 / 16 : ℝ) ≤ lam := by
    have hleft := (abs_le.mp hnear).1
    nlinarith
  have hlam : 0 < lam := lt_of_lt_of_le (by norm_num) hlamLower
  obtain ⟨haY', hd', hrem⟩ := hremX a ha
  have hhaY : haY' = haY := Subsingleton.elim _ _
  subst haY'
  have hhd : hd' = hd := Subsingleton.elim _ _
  subst hd'
  have hrem' : |lam ^ 2 - F| ≤ E := by
    dsimp [lam, F, E, C]
    convert hrem using 1 <;> ring
  have hratio := hsmallX (a : ℕ) ha
  have hEhalf : E < 1 / 2 := by
    calc
      E < C * (1 / (2 * C)) := by
        dsimp [E]
        exact mul_lt_mul_of_pos_left hratio hC
      _ = 1 / 2 := by field_simp [hC.ne']
  have hlamSq : 1 / 2 < lam ^ 2 := by
    nlinarith [sq_nonneg (lam - 15 / 16)]
  have hF : 0 < F := by
    have hupper := (abs_le.mp hrem').2
    linarith
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  refine ⟨hlam, hF, ?_⟩
  exact abs_sub_sqrt_le_of_abs_sq_sub_le hlam hF.le hE hrem'

/-- Corollary 9.9, approximate-frequency half, as one exported theorem.

The explicit first-exit correction determines the coherent centre--shell
phase.  The estimate is finite and uniform over all centres in the
logarithmic window; the manuscript's time scale follows by inserting the
proved lower bound for the positive star frequency. -/
theorem eventually_logarithmicWindow_starPair_dynamics_with_actualCorrection
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
          (sigma : ℝ),
          sigma ^ 2 = 1 ∧
          0 ≤ (allowedPrimeCount S (X / (a : ℕ)) : ℝ) +
            fixedCenterActualCorrection S (a : ℕ) X ∧
          ∀ t : ℝ,
            ‖primeCoverAdjacencyEvolution S X t
                  (normalizedPairCentre
                    (complexifyEuclidean
                      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
                    (complexifyEuclidean
                      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1)))) -
                ((Real.cos
                    (logarithmicWindowApproximateFrequency S X a * t) : ℂ) •
                    normalizedPairCentre
                      (complexifyEuclidean
                        (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
                      (complexifyEuclidean
                        (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1))) -
                  (Complex.I * Real.sin
                    (logarithmicWindowApproximateFrequency S X a * t)) •
                    normalizedPairShell
                      (complexifyEuclidean
                        (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
                      (complexifyEuclidean
                        (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1))))‖ ≤
              4 * logarithmicWindowLocalizationBound (a : ℕ) X +
                2 * |t| *
                  ((logarithmicWindowFeshbachRemainderConstant *
                      ((a : ℝ) ^ 2 / Real.log (X : ℝ))) /
                    (arithmeticStarFullEigenvalue a haY hd +
                      logarithmicWindowApproximateFrequency S X a)) := by
  filter_upwards [eventually_logarithmicWindow_starPair_dynamics S hS hε,
      eventually_logarithmicWindow_actualCorrection_frequency_bound S hS hε]
      with X hdynamics hfrequency
  intro a ha
  obtain ⟨haY, hd, sigma, hsigma, hexact⟩ := hdynamics a ha
  obtain ⟨_hlam, hF, hfreq⟩ := hfrequency a ha haY hd
  refine ⟨haY, hd, sigma, hsigma, hF.le, ?_⟩
  intro t
  let centre := normalizedPairCentre
    (complexifyEuclidean
      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
    (complexifyEuclidean
      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1)))
  let shell := normalizedPairShell
    (complexifyEuclidean
      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
    (complexifyEuclidean
      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1)))
  let lam := arithmeticStarFullEigenvalue a haY hd
  let hat := logarithmicWindowApproximateFrequency S X a
  let exactOsc := (Real.cos (lam * t) : ℂ) • centre -
    (Complex.I * Real.sin (lam * t)) • shell
  let approxOsc := (Real.cos (hat * t) : ℂ) • centre -
    (Complex.I * Real.sin (hat * t)) • shell
  have hcentre : ‖centre‖ ≤ 1 := by
    dsimp [centre]
    exact (norm_normalizedPairCentre_largePrimeStarModes hd).le
  have hshell : ‖shell‖ ≤ 1 := by
    dsimp [shell]
    exact (norm_normalizedPairShell_largePrimeStarModes hd).le
  have hphase : ‖exactOsc - approxOsc‖ ≤ 2 * |t| * |lam - hat| := by
    dsimp [exactOsc, approxOsc]
    exact norm_centreShellOscillation_sub_le centre shell lam hat t hcentre hshell
  have hphase' : ‖exactOsc - approxOsc‖ ≤
      2 * |t| *
        ((logarithmicWindowFeshbachRemainderConstant *
            ((a : ℝ) ^ 2 / Real.log (X : ℝ))) /
          (lam + hat)) := by
    exact hphase.trans (mul_le_mul_of_nonneg_left hfreq (by positivity))
  change ‖primeCoverAdjacencyEvolution S X t centre - approxOsc‖ ≤ _
  exact (norm_sub_le_norm_sub_add_norm_sub _ exactOsc approxOsc).trans
    (add_le_add (by simpa [centre, shell, lam, exactOsc] using hexact t) hphase')

end

end PrimeStar
