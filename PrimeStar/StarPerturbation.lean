import PrimeStar.IsolatedMode
import PrimeStar.SpectralMatching
import PrimeStar.StarSpectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# The small-prime perturbation on a large-prime star

The prime-cover adjacency splits into its large-prime star forest and the
remaining small-prime graph.  No remaining edge has both endpoints in one
closed large-prime star.  Consequently every signed star mode has zero
first-order quadratic interaction with the small-prime adjacency operator.
-/

namespace PrimeStar

noncomputable section

open scoped InnerProductSpace

/-- Local decidability for prime-cover adjacency in the perturbation split. -/
local instance primeCoverPerturbationDecidableAdj (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- Local decidability for large-prime adjacency in the perturbation split. -/
local instance largePrimePerturbationDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The prime-cover edges left after deleting the large-prime star forest. -/
def smallPrimeGraph (S : Finset ℕ) (X Y : ℕ) : SimpleGraph (Vertex S X) :=
  primeCoverGraph S X \ largePrimeGraph S X Y

/-- Local decidability for residual adjacency in the perturbation split. -/
local instance smallPrimePerturbationDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

@[simp]
theorem smallPrimeGraph_adj {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X} :
    (smallPrimeGraph S X Y).Adj m n ↔
      PrimeCoverAdj m n ∧ ¬LargePrimeAdj S Y m n := by
  exact SimpleGraph.sdiff_adj _ _ _ _

/-- Two distinct children of one prime star cannot themselves differ by one
prime multiplication. -/
theorem not_primeCoverAdj_of_same_largePrime_parent
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hcv : IsLargePrimeChild S Y c v) (hcw : IsLargePrimeChild S Y c w) :
    ¬PrimeCoverAdj v w := by
  rintro ⟨r, hr, _hrS, hvw | hwv⟩
  · obtain ⟨p, hp, _hpS, _hYp, hcp⟩ := hcv
    obtain ⟨q, hq, _hqS, _hYq, hcq⟩ := hcw
    have hprq : p * r = q := by
      apply Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos c)
      calc
        (c : ℕ) * (p * r) = ((c : ℕ) * p) * r := by simp [Nat.mul_assoc]
        _ = (v : ℕ) * r := by rw [hcp]
        _ = (w : ℕ) := hvw
        _ = (c : ℕ) * q := hcq.symm
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp ⟨r, hprq.symm⟩
    have hprp : p * r = p := hprq.trans hpq.symm
    have hr1 : r = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (by simpa using hprp)
    exact hr.ne_one hr1
  · obtain ⟨p, hp, _hpS, _hYp, hcp⟩ := hcv
    obtain ⟨q, hq, _hqS, _hYq, hcq⟩ := hcw
    have hqrp : q * r = p := by
      apply Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos c)
      calc
        (c : ℕ) * (q * r) = ((c : ℕ) * q) * r := by simp [Nat.mul_assoc]
        _ = (w : ℕ) * r := by rw [hcq]
        _ = (v : ℕ) := hwv
        _ = (c : ℕ) * p := hcp.symm
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp ⟨r, hqrp.symm⟩
    have hqrq : q * r = q := hqrp.trans hqp.symm
    have hr1 : r = 1 := Nat.eq_of_mul_eq_mul_left hq.pos (by simpa using hqrq)
    exact hr.ne_one hr1

/-- The residual small-prime graph has no edge wholly contained in one closed
large-prime star support. -/
theorem not_smallPrimeGraph_adj_on_largePrimeStarSupport
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ largePrimeStarSupport S X Y c)
    (hw : w ∈ largePrimeStarSupport S X Y c) :
    ¬(smallPrimeGraph S X Y).Adj v w := by
  intro hsmall
  have hprime : PrimeCoverAdj v w := (smallPrimeGraph_adj.mp hsmall).1
  have hnlarge : ¬LargePrimeAdj S Y v w := (smallPrimeGraph_adj.mp hsmall).2
  rw [mem_largePrimeStarSupport] at hv hw
  apply hnlarge
  rcases hv with hvc | hcv
  · rcases hw with hwc | hcw
    · exact False.elim
        ((not_primeCoverAdj_self c) (by simpa [hvc, hwc] using hprime))
    · simpa [hvc] using hcw
  · rcases hw with hwc | hcw
    · simpa [hwc] using largePrimeAdj_symm hcv
    · exact False.elim
        (not_primeCoverAdj_of_same_largePrime_parent
          (isLargePrimeChild_of_largePrimeAdj_of_le hc hcv)
          (isLargePrimeChild_of_largePrimeAdj_of_le hc hcw) hprime)

/-- In Euclidean coordinates, the small-prime adjacency has zero quadratic
form on every signed mode of a lower large-prime star. -/
theorem real_inner_smallPrime_signedStarVector_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hc : (c : ℕ) ≤ Y) :
    ⟪WithLp.toLp 2 (largePrimeSignedStarVector S X Y c ε),
      Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
        (WithLp.toLp 2 (largePrimeSignedStarVector S X Y c ε))⟫_ℝ = 0 := by
  rw [Matrix.toLpLin_toLp 2 2, PiLp.inner_apply]
  simp only [Matrix.toLin'_apply]
  apply Finset.sum_eq_zero
  intro v _hv
  rw [Real.inner_apply, Matrix.mulVec_apply_eq_sum]
  by_cases hv0 : largePrimeSignedStarVector S X Y c ε v = 0
  · simp [hv0]
  have hvsupp : v ∈ largePrimeStarSupport S X Y c := by
    by_contra hvout
    exact hv0 (largePrimeSignedStarVector_eq_zero_of_not_mem hvout)
  apply mul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro w _hw
  by_cases hw0 : largePrimeSignedStarVector S X Y c ε w = 0
  · simp [hw0]
  have hwsupp : w ∈ largePrimeStarSupport S X Y c := by
    by_contra hwout
    exact hw0 (largePrimeSignedStarVector_eq_zero_of_not_mem hwout)
  have hnot := not_smallPrimeGraph_adj_on_largePrimeStarSupport hc hvsupp hwsupp
  have hentry : (smallPrimeGraph S X Y).adjMatrix ℝ v w = 0 := by
    rw [SimpleGraph.adjMatrix_apply, if_neg hnot]
  rw [hentry, zero_mul]

/-- The full adjacency matrix is the disjoint sum of the large-prime and
small-prime adjacency matrices. -/
theorem primeCover_adjMatrix_eq_large_add_small
    (S : Finset ℕ) (X Y : ℕ) :
    (primeCoverGraph S X).adjMatrix ℝ =
      (largePrimeGraph S X Y).adjMatrix ℝ +
        (smallPrimeGraph S X Y).adjMatrix ℝ := by
  ext v w
  by_cases hp : PrimeCoverAdj v w
  · by_cases hl : LargePrimeAdj S Y v w
    · simp [SimpleGraph.adjMatrix_apply, hp, hl, smallPrimeGraph_adj]
    · simp [SimpleGraph.adjMatrix_apply, hp, hl, smallPrimeGraph_adj]
  · have hnl : ¬LargePrimeAdj S Y v w := by
      intro hl
      exact hp ((largePrimeGraph_le_primeCoverGraph S X Y) hl)
    simp [SimpleGraph.adjMatrix_apply, hp, hnl, smallPrimeGraph_adj]

/-- The Euclidean adjacency operator of the prime-cover graph is exactly the
sum of its large-prime star forest and small-prime remainder operators. -/
theorem primeCover_toEuclideanLin_eq_large_add_small
    (S : Finset ℕ) (X Y : ℕ) :
    Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) =
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) +
        Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) := by
  rw [primeCover_adjMatrix_eq_large_add_small, map_add]

/-- The Euclidean version of the unnormalized signed star mode. -/
def largePrimeEuclideanStarVector
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) (ε : ℝ) :
    EuclideanSpace ℝ (Vertex S X) :=
  WithLp.toLp 2 (largePrimeSignedStarVector S X Y c ε)

/-- The normalized Euclidean signed star mode. -/
def largePrimeNormalizedStarMode
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) (ε : ℝ) :
    EuclideanSpace ℝ (Vertex S X) :=
  NormedSpace.normalize (largePrimeEuclideanStarVector S X Y c ε)

/-- The unnormalized Euclidean star vector satisfies the same exact
large-prime adjacency eigenvector equation as its coordinate function. -/
theorem largePrime_toEuclideanLin_signedStarVector
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hε : ε ^ 2 = 1) :
    Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeEuclideanStarVector S X Y c ε) =
      (ε * √(largePrimeStarDegree S X Y c : ℝ)) •
        largePrimeEuclideanStarVector S X Y c ε := by
  rw [largePrimeEuclideanStarVector, Matrix.toLpLin_toLp 2 2]
  congr 1
  exact largePrime_adjMatrix_mulVec_signedStarVector hcut hc hε

/-- A nonempty normalized star mode has unit norm. -/
theorem norm_largePrimeNormalizedStarMode
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hd : 0 < largePrimeStarDegree S X Y c) :
    ‖largePrimeNormalizedStarMode S X Y c ε‖ = 1 := by
  apply NormedSpace.norm_normalize
  rw [largePrimeEuclideanStarVector, ne_eq, WithLp.toLp_eq_zero]
  exact largePrimeSignedStarVector_ne_zero hd

/-- Normalizing a nonempty signed star preserves its exact eigenvector
equation. -/
theorem largePrime_toEuclideanLin_normalizedStarMode
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hε : ε ^ 2 = 1) :
    Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeNormalizedStarMode S X Y c ε) =
      (ε * √(largePrimeStarDegree S X Y c : ℝ)) •
        largePrimeNormalizedStarMode S X Y c ε := by
  rw [largePrimeNormalizedStarMode, NormedSpace.normalize]
  simp only [map_smul]
  rw [largePrime_toEuclideanLin_signedStarVector hcut hc hε]
  simp only [smul_smul]
  congr 1
  ring

/-- The normalized Stage 2 star mode satisfies the first-order cancellation
hypothesis of the isolated-mode comparison. -/
theorem real_inner_smallPrime_normalizedStarMode_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hc : (c : ℕ) ≤ Y) :
    ⟪largePrimeNormalizedStarMode S X Y c ε,
      Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeNormalizedStarMode S X Y c ε)⟫_ℝ = 0 := by
  rw [largePrimeNormalizedStarMode, NormedSpace.normalize]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  have hzero :
      ⟪largePrimeEuclideanStarVector S X Y c ε,
        Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeEuclideanStarVector S X Y c ε)⟫_ℝ = 0 := by
    simpa [largePrimeEuclideanStarVector] using
      real_inner_smallPrime_signedStarVector_eq_zero hc
  rw [hzero]
  simp

/-- An eigenpair of the full prime-cover adjacency obeys the exact scalar
block equation at every normalized nonempty large-prime star mode. -/
theorem primeCover_scalarEquation_at_normalizedStarMode
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε μ lam : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hε : ε ^ 2 = 1)
    (hμ : μ = ε * √(largePrimeStarDegree S X Y c : ℝ))
    (v : EuclideanSpace ℝ (Vertex S X))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v) :
    (lam - μ) * ⟪largePrimeNormalizedStarMode S X Y c ε, v⟫_ℝ =
      ⟪Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c ε),
        orthogonalRemainder (largePrimeNormalizedStarMode S X Y c ε) v⟫_ℝ := by
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hL : L.IsSymmetric := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hH : H.IsSymmetric := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hLu : L (largePrimeNormalizedStarMode S X Y c ε) =
      μ • largePrimeNormalizedStarMode S X Y c ε := by
    rw [hμ]
    exact largePrime_toEuclideanLin_normalizedStarMode hcut hc hε
  have hsplit : (L + H) v = lam • v := by
    dsimp [L, H]
    rw [← LinearMap.add_apply, ← map_add, ← primeCover_adjMatrix_eq_large_add_small]
    exact hAv
  exact isolatedMode_scalarEquation L H
    (largePrimeNormalizedStarMode S X Y c ε) v μ lam hL hH hLu hsplit
    (real_inner_smallPrime_normalizedStarMode_eq_zero hc)

/-- Concrete Stage 3 consumer.  Once the matched full eigenvector and the
reduced complement gap are supplied, the normalized prime-star mode inherits
the universal second-order displacement and localization constants. -/
theorem primeCover_isolatedStarComparison
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε μ lam γ : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hε : ε ^ 2 = 1) (hd : 0 < largePrimeStarDegree S X Y c)
    (hμ : μ = ε * √(largePrimeStarDegree S X Y c : ℝ))
    (v : EuclideanSpace ℝ (Vertex S X))
    (hv : ‖v‖ = 1)
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (hα : 0 < ⟪largePrimeNormalizedStarMode S X Y c ε, v⟫_ℝ)
    (hγ : 0 < γ)
    (hb : ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeNormalizedStarMode S X Y c ε)‖ ≤ γ / 4)
    (T : EuclideanSpace ℝ (Vertex S X) →L[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (hT : T (orthogonalRemainder
        (largePrimeNormalizedStarMode S X Y c ε) v) =
      ⟪largePrimeNormalizedStarMode S X Y c ε, v⟫_ℝ •
        Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c ε))
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ⟪largePrimeNormalizedStarMode S X Y c ε, x⟫_ℝ = 0 →
        (γ / 2) * ‖x‖ ≤ ‖T x‖) :
    |lam - μ| ≤
        2 * ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c ε)‖ ^ 2 / γ ∧
      ‖v - largePrimeNormalizedStarMode S X Y c ε‖ ≤
        3 * ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c ε)‖ / γ := by
  apply isolatedModeComparison T
    (largePrimeNormalizedStarMode S X Y c ε) v
    (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
      (largePrimeNormalizedStarMode S X Y c ε)) μ lam γ hγ
    (norm_largePrimeNormalizedStarMode hd) hv hα hb
  · exact primeCover_scalarEquation_at_normalizedStarMode hcut hc hε hμ v hAv
  · exact hT
  · exact hgap

/-- An isolated nonempty prime star determines an actual matched eigenvalue
of the full prime-cover adjacency.  The output uses the ordered eigenvalue
list supplied by the finite-dimensional spectral theorem, includes its
canonical eigenvector, and proves that its eigenspace is one-dimensional. -/
theorem primeCover_exists_simple_matchedStarEigenpair
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε mu gamma eta : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hε : ε ^ 2 = 1) (hd : 0 < largePrimeStarDegree S X Y c)
    (hmu : mu = ε * √(largePrimeStarDegree S X Y c : ℝ))
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ⟪largePrimeNormalizedStarMode S X Y c ε, x⟫_ℝ = 0 →
        gamma * ‖x‖ ≤
          ‖Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x - mu • x‖)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤ eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
    let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    ∃ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))),
      |(hL.add hHs).eigenvalues rfl i - mu| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace (L + H) ((hL.add hHs).eigenvalues rfl i)) = 1 ∧
      Module.End.HasEigenvector (L + H) ((hL.add hHs).eigenvalues rfl i)
        ((hL.add hHs).eigenvectorBasis rfl i) := by
  dsimp only
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hLu : L (largePrimeNormalizedStarMode S X Y c ε) =
      mu • largePrimeNormalizedStarMode S X Y c ε := by
    rw [hmu]
    exact largePrime_toEuclideanLin_normalizedStarMode hcut hc hε
  obtain ⟨i, hi, hsimple⟩ :=
    exists_simple_eigenvalue_near_of_isolated_mode L H hL hHs
      (largePrimeNormalizedStarMode S X Y c ε) mu gamma eta
      (norm_largePrimeNormalizedStarMode hd) hLu hgap hH hsmall
  exact ⟨i, hi, hsimple, (hL.add hHs).hasEigenvector_eigenvectorBasis rfl i⟩

/-- Ordered-spectrum prime-cover wrapper.  Scalar separation of one ordered
large-prime eigenvalue, together with a residual norm bound, produces a
nearby simple eigenvalue of the full graph. -/
theorem primeCover_exists_simple_orderedEigenpair
    {S : Finset ℕ} {X Y : ℕ}
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))))
    (gamma eta : ℝ)
    (hgamma : 0 ≤ gamma)
    (hsep : ∀ j :
        Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))), j ≠ i →
      gamma ≤
        |(Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl j -
          (Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl i|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
    let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    ∃ k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))),
      |(hL.add hHs).eigenvalues rfl k - hL.eigenvalues rfl i| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace (L + H)
          ((hL.add hHs).eigenvalues rfl k)) = 1 := by
  dsimp only
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  apply exists_simple_eigenvalue_near_of_separated_ordered_mode
    L H hL hHs i gamma eta hgamma
  · exact hsep
  · exact hH
  · exact hsmall

/-- Ordered-spectrum prime-cover wrapper that preserves the prescribed
index.  This is the form needed to identify the arithmetic centre with the
manuscript's ordered eigenvalue rather than merely with some nearby simple
eigenvalue. -/
theorem primeCover_simple_orderedEigenpair
    {S : Finset ℕ} {X Y : ℕ}
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))))
    (gamma eta : ℝ)
    (hgamma : 0 ≤ gamma)
    (hsep : ∀ j :
        Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))), j ≠ i →
      gamma ≤
        |(Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl j -
          (Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl i|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
    let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    |(hL.add hHs).eigenvalues rfl i - hL.eigenvalues rfl i| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace (L + H)
          ((hL.add hHs).eigenvalues rfl i)) = 1 := by
  dsimp only
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  exact simple_orderedEigenvalue_near_of_separated_ordered_mode
    L H hL hHs i gamma eta hgamma hsep hH hsmall

end

end PrimeStar
