import PrimeStar.LogarithmicWindowFeshbachRemainder
import PrimeStar.Localization

/-!
# Uniform eigenvector localization on the logarithmic centre window

The ordered full-adjacency eigenvector is defined only up to sign.  This file
orients it toward the positive normalized large-prime star mode and bounds the
distance by the ratio of the square-cutoff residual scale to the uniform
ordered star gap.  Hub-mass and inverse-participation consequences then follow
from the finite localization lemmas.
-/

namespace PrimeStar

open Filter Topology
open scoped InnerProductSpace

noncomputable section

local instance logarithmicWindowLocalizationLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

local instance logarithmicWindowLocalizationSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj := Classical.decRel _

local instance logarithmicWindowLocalizationPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

/-- The finite displacement scale supplied by the square-cutoff residual and
the ordered star-frequency gap. -/
def logarithmicWindowLocalizationBound (a X : ℕ) : ℝ :=
  4 * sqrtCutoffResidualScale X /
    (logarithmicWindowDegreeGapScale a X -
      2 * sqrtCutoffResidualScale X)

/-- Uniform oriented localization of the ordered full-adjacency eigenvector
about its exact positive large-prime star mode.  This is the finite,
constant-explicit form of the manuscript estimate
`O(a^(3/2) * X^(-1/4))`. -/
theorem eventually_logarithmicWindow_orientedEigenvector_localization
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
          (sigma : ℝ),
          sigma ^ 2 = 1 ∧
          ‖sigma • arithmeticStarFullEigenvector a haY hd -
              largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1‖ ≤
            logarithmicWindowLocalizationBound (a : ℕ) X := by
  filter_upwards [
      eventually_logarithmicWindow_feshbachScaleBundle hε,
      eventually_logarithmicWindow_zeroDegreeGap S hS hε,
      eventually_logarithmicWindow_otherStarDegreeGap S hS hε,
      eventually_logarithmicWindow_largePrimeStarDegree_ge S hS hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε,
      eventually_sqrtCutoff_smallPrime_apply_le_tuned,
      eventually_ge_atTop 4]
      with X hscales hzeroX hdegreeX hdegreeLower hcenter hresidual hX
  intro a ha
  let Y : ℕ := Nat.sqrt X
  let mu : ℝ := √(largePrimeStarDegree S X Y a : ℝ)
  let gamma : ℝ := logarithmicWindowDegreeGapScale (a : ℕ) X
  let eta : ℝ := sqrtCutoffResidualScale X
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let hH : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have haY : (a : ℕ) ≤ Y := by simpa [Y] using hcenter (a : ℕ) ha
  have hd : 0 < largePrimeStarDegree S X Y a := by
    have hlower := hdegreeLower a ha
    have haPos : (0 : ℝ) < (a : ℕ) := by
      exact_mod_cast Vertex.coe_pos a
    have hlog : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hpos : 0 < (X : ℝ) /
        ((16 * (a : ℝ)) * Real.log (X : ℝ)) := by positivity
    have : 0 < (largePrimeStarDegree S X Y a : ℝ) := by
      simpa [Y] using hpos.trans_le hlower
    exact_mod_cast this
  have hzero : gamma ≤ mu := by simpa [gamma, mu, Y] using hzeroX a ha
  have hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ a →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |mu - √(largePrimeStarDegree S X Y b : ℝ)| := by
    intro b hbY hba hbd
    simpa [gamma, mu, Y] using
      hdegreeX a ha b (by simpa [Y] using hbY) hba hbd
  have hHbound : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖H x‖ ≤ eta * ‖x‖ := by
    intro x
    simpa [H, Y, eta, sqrtCutoffResidualScale,
      sqrtCutoffResidualConstant] using hresidual S x
  obtain ⟨heta, hlarge, _hR2, _hR2small, _hAsmall, _hetaR2⟩ :=
    hscales (a : ℕ) ha
  have heta' : 0 < eta := by simpa [eta] using heta
  have hgamma : 0 < gamma :=
    lt_of_lt_of_le (mul_pos (by norm_num) heta') hlarge
  have hgamma' : 0 < gamma - 2 * eta := by nlinarith
  let i := largePrimePositiveStarOrderedIndex a
    (sqrtCutoff_condition X) haY hd
  let lam := (hL.add hH).eigenvalues rfl i
  let v := (hL.add hH).eigenvectorBasis rfl i
  obtain ⟨hv, hAv, _hoverlap, hnear, _hsimple⟩ :=
    primeCover_ordered_arithmeticStarEigenpair_withOverlap_of_degreeGap
      a (sqrtCutoff_condition X) haY hd gamma eta hgamma.le hzero hdegree
        hHbound (by nlinarith)
  have hsplit : Matrix.toEuclideanLin
      ((primeCoverGraph S X).adjMatrix ℝ) = L + H :=
    primeCover_toEuclideanLin_eq_large_add_small S X Y
  have hAv' : (L + H) v = lam • v := by simpa [hsplit] using hAv
  have hu : ‖largePrimeNormalizedStarMode S X Y a 1‖ = 1 :=
    norm_largePrimeNormalizedStarMode hd
  have hLu : L (largePrimeNormalizedStarMode S X Y a 1) =
      mu • largePrimeNormalizedStarMode S X Y a 1 := by
    simpa [L, mu] using
      (largePrime_toEuclideanLin_normalizedStarMode
        (sqrtCutoff_condition X) haY (by norm_num : (1 : ℝ) ^ 2 = 1))
  have hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ⟪largePrimeNormalizedStarMode S X Y a 1, x⟫_ℝ = 0 →
      (gamma - 2 * eta) * ‖x‖ ≤ ‖L x - mu • x‖ := by
    intro x hx
    have hg := largePrime_complementGap_of_degreeGap
      a (sqrtCutoff_condition X) haY hd gamma eta hgamma.le hzero hdegree
        hHbound x hx
    simpa [L, mu, norm_sub_rev] using hg
  obtain ⟨sigma, hsigma, hdist⟩ :=
    exists_sign_eigenvector_displacement_le_of_isolated_mode
      L H (largePrimeNormalizedStarMode S X Y a 1) v mu lam
        (gamma - 2 * eta) eta hgamma' hu hv hLu hAv' hgap hHbound hnear
  refine ⟨haY, hd, sigma, hsigma, ?_⟩
  simpa [arithmeticStarFullEigenvector, Y, L, H, hL, hH, i, v,
    logarithmicWindowLocalizationBound, gamma, eta] using hdist

/-- Uniform hub-mass consequence at the same oriented ordered eigenvector. -/
theorem eventually_logarithmicWindow_hubMass_localization
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
          (sigma : ℝ),
          sigma ^ 2 = 1 ∧
          |((sigma • arithmeticStarFullEigenvector a haY hd) a) ^ 2 - 1 / 2| ≤
            2 * logarithmicWindowLocalizationBound (a : ℕ) X := by
  filter_upwards [eventually_logarithmicWindow_orientedEigenvector_localization
      S hS hε] with X hX
  intro a ha
  obtain ⟨haY, hd, sigma, hsigma, hclose⟩ := hX a ha
  refine ⟨haY, hd, sigma, hsigma, ?_⟩
  have hv : ‖sigma • arithmeticStarFullEigenvector a haY hd‖ = 1 := by
    have hsigmaAbs : |sigma| = 1 := by
      rcases sq_eq_one_iff.mp hsigma with h | h <;> rw [h] <;> norm_num
    rw [norm_smul, Real.norm_eq_abs, hsigmaAbs,
      norm_arithmeticStarFullEigenvector,
      one_mul]
  exact (hubMass_localization_of_close_starMode
    (by norm_num : (1 : ℝ) ^ 2 = 1) hd _ hv).trans
      (mul_le_mul_of_nonneg_left hclose (by norm_num))

/-- Uniform inverse-participation consequence.  The reference value is
`1/4 + 1/(4d_a)`, hence tends to `1/4` as the star degree grows. -/
theorem eventually_logarithmicWindow_inverseParticipationRatio_localization
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
          (sigma : ℝ),
          sigma ^ 2 = 1 ∧
          |inverseParticipationRatio
                (sigma • arithmeticStarFullEigenvector a haY hd) -
              (1 / 4 + 1 /
                (4 * largePrimeStarDegree S X (Nat.sqrt X) a))| ≤
            4 * logarithmicWindowLocalizationBound (a : ℕ) X := by
  filter_upwards [eventually_logarithmicWindow_orientedEigenvector_localization
      S hS hε] with X hX
  intro a ha
  obtain ⟨haY, hd, sigma, hsigma, hclose⟩ := hX a ha
  refine ⟨haY, hd, sigma, hsigma, ?_⟩
  have hv : ‖sigma • arithmeticStarFullEigenvector a haY hd‖ = 1 := by
    have hsigmaAbs : |sigma| = 1 := by
      rcases sq_eq_one_iff.mp hsigma with h | h <;> rw [h] <;> norm_num
    rw [norm_smul, Real.norm_eq_abs, hsigmaAbs,
      norm_arithmeticStarFullEigenvector,
      one_mul]
  exact (inverseParticipationRatio_localization_of_close_starMode
    (by norm_num : (1 : ℝ) ^ 2 = 1) hd _ hv).trans
      (mul_le_mul_of_nonneg_left hclose (by norm_num))

end

end PrimeStar
