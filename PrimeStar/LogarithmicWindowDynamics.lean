import PrimeStar.LogarithmicWindowLocalization
import PrimeStar.BipartiteSymmetry

/-!
# Uniform centre--shell dynamics on the logarithmic window

Bipartite symmetry turns the oriented positive ordered eigenvector into its
negative partner without a second perturbation argument.  The finite paired
evolution theorem then yields a uniform-in-time centre--shell oscillation at
the exact ordered eigenfrequency.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

local instance logarithmicWindowDynamicsPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

/-- Negative partner of an oriented ordered eigenvector, obtained from the
exact bipartite sign symmetry. -/
def arithmeticStarPairedNegativeEigenvector
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (haY : (a : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
    (sigma : ℝ) : EuclideanSpace ℝ (Vertex S X) :=
  primeCoverParitySign a •
    primeCoverSignFlip (sigma • arithmeticStarFullEigenvector a haY hd)

theorem arithmeticStarPairedNegativeEigenvector_eigenvector
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (haY : (a : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
    (sigma : ℝ) :
    Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
        (arithmeticStarPairedNegativeEigenvector a haY hd sigma) =
      (-arithmeticStarFullEigenvalue a haY hd) •
        arithmeticStarPairedNegativeEigenvector a haY hd sigma := by
  have hbase := primeCoverAdjacency_arithmeticStarFullEigenvector a haY hd
  have hplus : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
        (sigma • arithmeticStarFullEigenvector a haY hd) =
      arithmeticStarFullEigenvalue a haY hd •
        (sigma • arithmeticStarFullEigenvector a haY hd) := by
    rw [map_smul, hbase]
    module
  rw [arithmeticStarPairedNegativeEigenvector, map_smul,
    primeCoverSignFlip_eigenvector _ _ hplus]
  module

theorem arithmeticStarPairedNegativeEigenvector_close
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (haY : (a : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
    (sigma eps : ℝ)
    (hclose : ‖sigma • arithmeticStarFullEigenvector a haY hd -
      largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1‖ ≤ eps) :
    ‖arithmeticStarPairedNegativeEigenvector a haY hd sigma -
        largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1)‖ ≤ eps := by
  let s := primeCoverParitySign a
  let vplus := sigma • arithmeticStarFullEigenvector a haY hd
  let uplus := largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1
  let uminus := largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1)
  have hsSq : s ^ 2 = 1 := primeCoverParitySign_sq a
  have hsAbs : |s| = 1 := by
    rcases sq_eq_one_iff.mp hsSq with h | h <;> rw [h] <;> norm_num
  have hstar : primeCoverSignFlip uplus = s • uminus := by
    simpa [s, uplus, uminus] using
      (primeCoverSignFlip_largePrimeNormalizedStarMode_pos
        (S := S) (X := X) (Y := Nat.sqrt X) (c := a))
  have hdiff :
      arithmeticStarPairedNegativeEigenvector a haY hd sigma - uminus =
        s • primeCoverSignFlip (vplus - uplus) := by
    rw [primeCoverSignFlip_sub, smul_sub, hstar]
    dsimp [arithmeticStarPairedNegativeEigenvector, s, vplus]
    have hss : primeCoverParitySign a * primeCoverParitySign a = 1 := by
      simpa [pow_two] using primeCoverParitySign_sq a
    rw [smul_smul, hss, one_smul]
  rw [hdiff, norm_smul, Real.norm_eq_abs, hsAbs,
    norm_primeCoverSignFlip, one_mul]
  exact hclose

/-- Uniform exact-frequency centre--shell dynamics on the logarithmic centre
window. -/
theorem eventually_logarithmicWindow_starPair_dynamics
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
          (sigma : ℝ),
          sigma ^ 2 = 1 ∧
          ∀ t : ℝ,
            ‖primeCoverAdjacencyEvolution S X t
                  (normalizedPairCentre
                    (complexifyEuclidean
                      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
                    (complexifyEuclidean
                      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1)))) -
                ((Real.cos (arithmeticStarFullEigenvalue a haY hd * t) : ℂ) •
                    normalizedPairCentre
                      (complexifyEuclidean
                        (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
                      (complexifyEuclidean
                        (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1))) -
                  (Complex.I *
                      Real.sin (arithmeticStarFullEigenvalue a haY hd * t)) •
                    normalizedPairShell
                      (complexifyEuclidean
                        (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
                      (complexifyEuclidean
                        (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1))))‖ ≤
              4 * logarithmicWindowLocalizationBound (a : ℕ) X := by
  filter_upwards [eventually_logarithmicWindow_orientedEigenvector_localization
      S hS hε] with X hX
  intro a ha
  obtain ⟨haY, hd, sigma, hsigma, hclosePlus⟩ := hX a ha
  refine ⟨haY, hd, sigma, hsigma, ?_⟩
  intro t
  let vplus := sigma • arithmeticStarFullEigenvector a haY hd
  let vminus := arithmeticStarPairedNegativeEigenvector a haY hd sigma
  let lam := arithmeticStarFullEigenvalue a haY hd
  have hbase := primeCoverAdjacency_arithmeticStarFullEigenvector a haY hd
  have hplus : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) vplus =
      lam • vplus := by
    dsimp [vplus, lam]
    rw [map_smul, hbase]
    module
  have hminus : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) vminus =
      (-lam) • vminus := by
    simpa [vminus, lam] using
      arithmeticStarPairedNegativeEigenvector_eigenvector a haY hd sigma
  have hcloseMinus : ‖vminus -
      largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1)‖ ≤
      logarithmicWindowLocalizationBound (a : ℕ) X := by
    exact arithmeticStarPairedNegativeEigenvector_close a haY hd sigma _ hclosePlus
  have hboundNonneg : 0 ≤ logarithmicWindowLocalizationBound (a : ℕ) X :=
    (norm_nonneg _).trans hclosePlus
  simpa [vplus, vminus, lam] using
    primeCoverAdjacencyEvolution_starPair_localization
      vplus vminus lam t (logarithmicWindowLocalizationBound (a : ℕ) X)
        hd hplus hminus hboundNonneg hclosePlus hcloseMinus

end

end PrimeStar
