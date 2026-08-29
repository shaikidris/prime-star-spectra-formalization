import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A finite weighted Schur estimate

This file proves the finite symmetric weighted Schur test used for the
small-prime adjacency matrix.  The statement is independent of arithmetic.
-/

namespace PrimeStar

open scoped Matrix.Norms.L2Operator RealInnerProductSpace InnerProductSpace

noncomputable section

lemma weighted_two_mul_abs_le {a b u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    2 * |a * b| ≤ a ^ 2 * (v / u) + b ^ 2 * (u / v) := by
  have huv : 0 < u * v := mul_pos hu hv
  have hsq : 0 ≤ (|a| * v - |b| * u) ^ 2 := sq_nonneg _
  have hab : |a * b| = |a| * |b| := abs_mul a b
  rw [hab]
  rw [show a ^ 2 * (v / u) + b ^ 2 * (u / v) =
      (a ^ 2 * v ^ 2 + b ^ 2 * u ^ 2) / (u * v) by
    field_simp]
  apply (le_div_iff₀ huv).2
  nlinarith [sq_abs a, sq_abs b]

variable {ι : Type*} [Fintype ι]

/-- Quadratic-form version of the finite weighted Schur test. -/
theorem abs_dotProduct_mulVec_le_of_weighted_row
    (A : Matrix ι ι ℝ) (w x : ι → ℝ) (C : ℝ)
    (hA0 : ∀ i j, 0 ≤ A i j)
    (hAsymm : ∀ i j, A i j = A j i)
    (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, A i j * w j ≤ C * w i) :
    |dotProduct x (Matrix.mulVec A x)| ≤ C * ∑ i, (x i) ^ 2 := by
  let Q : ℝ := ∑ i, ∑ j, A i j * |x i * x j|
  let R : ℝ := ∑ i, ∑ j, A i j * ((x i) ^ 2 * (w j / w i))
  have habssum : |dotProduct x (Matrix.mulVec A x)| ≤ Q := by
    change |∑ i, x i * (∑ j, A i j * x j)| ≤ Q
    simp_rw [Finset.mul_sum]
    have houter : |∑ i, ∑ j, x i * (A i j * x j)| ≤
        ∑ i, |∑ j, x i * (A i j * x j)| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun i ↦ ∑ j, x i * (A i j * x j)) Finset.univ
    refine houter.trans ?_
    apply Finset.sum_le_sum
    intro i _hi
    have hinner : |∑ j, x i * (A i j * x j)| ≤
        ∑ j, |x i * (A i j * x j)| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun j ↦ x i * (A i j * x j)) Finset.univ
    refine hinner.trans ?_
    apply Finset.sum_le_sum
    intro j _hj
    simp [abs_mul, abs_of_nonneg (hA0 i j), mul_left_comm]
  have hpair :
      2 * Q ≤
        R + ∑ i, ∑ j, A i j * ((x j) ^ 2 * (w i / w j)) := by
    dsimp only [Q, R]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _hj
    have hyoung := weighted_two_mul_abs_le (a := x i) (b := x j) (hw i) (hw j)
    have hnonneg := hA0 i j
    nlinarith
  have hswap :
      (∑ i, ∑ j, A i j * ((x j) ^ 2 * (w i / w j))) = R := by
    dsimp only [R]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hAsymm j i]
  have hQR : Q ≤ R := by
    rw [hswap] at hpair
    linarith
  have hR : R ≤ C * ∑ i, (x i) ^ 2 := by
    dsimp only [R]
    calc
      (∑ i, ∑ j, A i j * ((x i) ^ 2 * (w j / w i))) =
          ∑ i, ((x i) ^ 2 / w i) * (∑ j, A i j * w j) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            field_simp
      _ ≤ ∑ i, ((x i) ^ 2 / w i) * (C * w i) := by
            apply Finset.sum_le_sum
            intro i _hi
            exact mul_le_mul_of_nonneg_left (hrow i) (div_nonneg (sq_nonneg _) (hw i).le)
      _ = C * ∑ i, (x i) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            field_simp [(hw i).ne']
  exact habssum.trans (hQR.trans hR)

variable [DecidableEq ι]

/-- Finite symmetric weighted Schur test for the Euclidean operator norm. -/
theorem weightedSchur_l2_opNorm_le
    (A : Matrix ι ι ℝ) (w : ι → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hA0 : ∀ i j, 0 ≤ A i j)
    (hAsymm : ∀ i j, A i j = A j i)
    (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, A i j * w j ≤ C * w i) :
    ‖A‖ ≤ C := by
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
  have hTsymm :
      (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι).IsSymmetric := by
    change (Matrix.toEuclideanLin A).IsSymmetric
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext fun i j ↦ hAsymm j i
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  rw [T.norm_eq_iSup_rayleighQuotient hTsymm]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx, hC]
  · rw [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply]
    have hquad := abs_dotProduct_mulVec_le_of_weighted_row A w
      (fun i ↦ x i) C hA0 hAsymm hw hrow
    have hinterReal : ⟪T x, x⟫_ℝ =
        dotProduct (fun i ↦ x i) (Matrix.mulVec A (fun i ↦ x i)) := by
      rw [real_inner_comm]
      simpa [T] using Matrix.inner_toEuclideanCLM A x x
    simp only [RCLike.re_to_real]
    rw [hinterReal]
    rw [abs_div, abs_of_nonneg (sq_nonneg ‖x‖)]
    apply (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))).2
    rw [EuclideanSpace.real_norm_sq_eq]
    nlinarith

/-- Compressing an operator on both sides by a contraction cannot increase
its norm.  This is the abstract complement-norm step used after the Schur
bound. -/
theorem norm_compression_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P T : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) :
    ‖P.comp (T.comp P)‖ ≤ ‖T‖ := by
  calc
    ‖P.comp (T.comp P)‖ ≤ ‖P‖ * ‖T.comp P‖ := P.opNorm_comp_le (T.comp P)
    _ ≤ 1 * (‖T‖ * ‖P‖) := by
      gcongr
      exact T.opNorm_comp_le P
    _ ≤ 1 * (‖T‖ * 1) := by
      gcongr
    _ = ‖T‖ := by ring

end

end PrimeStar
