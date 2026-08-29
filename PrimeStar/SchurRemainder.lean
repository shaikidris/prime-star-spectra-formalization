import PrimeStar.IsolatedMode

/-!
# Exact finite Schur remainder

This file records the finite algebra between the isolated-mode scalar equation
and the analytic estimates used later in the paper.  No spectral-existence or
prime-counting theorem is used here.
-/

namespace PrimeStar

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If the orthogonal component is obtained by applying a reduced inverse to
the first-exit vector, the Stage 3 scalar equation becomes the exact
one-dimensional Schur equation. -/
theorem schurScalarEquation_of_inverseAction
    (R : E →ₗ[ℝ] E) (u v b : E) (μ lam : ℝ)
    (hα : ⟪u, v⟫_ℝ ≠ 0)
    (hscalar : (lam - μ) * ⟪u, v⟫_ℝ =
      ⟪b, orthogonalRemainder u v⟫_ℝ)
    (hinv : orthogonalRemainder u v = ⟪u, v⟫_ℝ • R b) :
    lam - μ = ⟪b, R b⟫_ℝ := by
  rw [hinv, real_inner_smul_right] at hscalar
  have hzero : ((lam - μ) - ⟪b, R b⟫_ℝ) * ⟪u, v⟫_ℝ = 0 := by
    nlinarith
  have := (mul_eq_zero.mp hzero).resolve_right hα
  linarith

/-- A literal reduced operator and a left inverse supply the inverse action
used by `schurScalarEquation_of_inverseAction`. -/
theorem schurScalarEquation_of_leftInverse
    (T R : E →ₗ[ℝ] E) (u v b : E) (μ lam : ℝ)
    (hα : ⟪u, v⟫_ℝ ≠ 0)
    (hscalar : (lam - μ) * ⟪u, v⟫_ℝ =
      ⟪b, orthogonalRemainder u v⟫_ℝ)
    (hreduced : T (orthogonalRemainder u v) = ⟪u, v⟫_ℝ • b)
    (hleft : ∀ x : E, R (T x) = x) :
    lam - μ = ⟪b, R b⟫_ℝ := by
  apply schurScalarEquation_of_inverseAction R u v b μ lam hα hscalar
  have h := congrArg R hreduced
  rw [map_smul, hleft] at h
  exact h

/-- With no first-exit coupling, the exact Schur equation has no
displacement. -/
theorem schurScalarEquation_zero_coupling
    (u v : E) (μ lam : ℝ)
    (hα : ⟪u, v⟫_ℝ ≠ 0)
    (hscalar : (lam - μ) * ⟪u, v⟫_ℝ =
      ⟪(0 : E), orthogonalRemainder u v⟫_ℝ) :
    lam = μ := by
  have hzero : (lam - μ) * ⟪u, v⟫_ℝ = 0 := by simpa using hscalar
  have := (mul_eq_zero.mp hzero).resolve_right hα
  linarith

/-- Exact algebraic remainder after converting an eigenvalue displacement to
a squared-eigenvalue correction. -/
theorem squaredCorrection_identity
    (lam μ primeCount boundary rho err correction : ℝ)
    (hdisp : lam - μ = rho + err)
    (hdegree : μ ^ 2 = primeCount - boundary)
    (hmain : 2 * μ * rho - boundary = correction) :
    (lam ^ 2 - primeCount) - correction =
      2 * μ * err + (lam - μ) ^ 2 := by
  have hlam : lam = μ + rho + err := by linarith
  have hprime : primeCount = μ ^ 2 + boundary := by linarith
  rw [hlam, hprime, ← hmain]
  ring

/-- An explicit finite error bound.  Later analytic stages only need to
provide bounds for the Schur-replacement error `err` and the total
displacement `lam - μ`. -/
theorem abs_squaredCorrection_le
    (lam μ primeCount boundary rho err correction eta D : ℝ)
    (hD : 0 ≤ D)
    (hdisp : lam - μ = rho + err)
    (hdegree : μ ^ 2 = primeCount - boundary)
    (hmain : 2 * μ * rho - boundary = correction)
    (herr : |err| ≤ eta) (hshift : |lam - μ| ≤ D) :
    |(lam ^ 2 - primeCount) - correction| ≤
      2 * |μ| * eta + D ^ 2 := by
  rw [squaredCorrection_identity lam μ primeCount boundary rho err correction
    hdisp hdegree hmain]
  calc
    |2 * μ * err + (lam - μ) ^ 2| ≤
        |2 * μ * err| + |(lam - μ) ^ 2| := abs_add_le _ _
    _ = 2 * |μ| * |err| + |lam - μ| ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow]
    _ ≤ 2 * |μ| * eta + D ^ 2 := by
      have hcoeff : 0 ≤ 2 * |μ| := mul_nonneg (by norm_num) (abs_nonneg μ)
      have hfirst : 2 * |μ| * |err| ≤ 2 * |μ| * eta :=
        mul_le_mul_of_nonneg_left herr hcoeff
      have hsq : |lam - μ| ^ 2 ≤ D ^ 2 := by nlinarith [abs_nonneg (lam - μ)]
      linarith

/-- A resolvent identity with contraction at most one half controls the
perturbed inverse on its source vector. -/
theorem norm_perturbedResolvent_apply_le
    (R T Rpert : E →ₗ[ℝ] E) (b : E) (alpha : ℝ)
    (hident : Rpert b = R b + R (T (Rpert b)))
    (hRT : ∀ x : E, ‖R (T x)‖ ≤ alpha * ‖x‖)
    (halpha : alpha ≤ 1 / 2) :
    ‖Rpert b‖ ≤ 2 * ‖R b‖ := by
  have hmain : ‖Rpert b‖ ≤ ‖R b‖ + alpha * ‖Rpert b‖ := by
    calc
      ‖Rpert b‖ = ‖R b + R (T (Rpert b))‖ := congrArg norm hident
      _ ≤ ‖R b‖ + ‖R (T (Rpert b))‖ := norm_add_le _ _
      _ ≤ ‖R b‖ + alpha * ‖Rpert b‖ :=
        add_le_add (le_refl _) (hRT (Rpert b))
  have hnorm : 0 ≤ ‖Rpert b‖ := norm_nonneg _
  have hrnorm : 0 ≤ ‖R b‖ := norm_nonneg _
  nlinarith

/-- Abstract form of the star-union resolvent replacement in Lemma 8.6.  The
identity is exact; the two norm hypotheses expose the numerical gap payment. -/
theorem abs_quadraticForm_resolventReplacement_le
    (R T Rpert : E →ₗ[ℝ] E) (b : E) (tau alpha : ℝ)
    (hR : R.IsSymmetric)
    (hident : Rpert b = R b + R (T (Rpert b)))
    (hRT : ∀ x : E, ‖R (T x)‖ ≤ alpha * ‖x‖)
    (hT : ∀ x : E, ‖T x‖ ≤ tau * ‖x‖)
    (htau : 0 ≤ tau) (halpha : alpha ≤ 1 / 2) :
    |⟪b, Rpert b⟫_ℝ - ⟪b, R b⟫_ℝ| ≤
      2 * tau * ‖R b‖ ^ 2 := by
  have hpert := norm_perturbedResolvent_apply_le R T Rpert b alpha
    hident hRT halpha
  have hdiff : Rpert b - R b = R (T (Rpert b)) := by
    calc
      Rpert b - R b = (R b + R (T (Rpert b))) - R b :=
        congrArg (fun z ↦ z - R b) hident
      _ = R (T (Rpert b)) := by abel
  calc
    |⟪b, Rpert b⟫_ℝ - ⟪b, R b⟫_ℝ| =
        |⟪b, Rpert b - R b⟫_ℝ| := by rw [inner_sub_right]
    _ = |⟪R b, T (Rpert b)⟫_ℝ| := by rw [hdiff, ← hR b (T (Rpert b))]
    _ ≤ ‖R b‖ * ‖T (Rpert b)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖R b‖ * (tau * ‖Rpert b‖) := by
      gcongr
      exact hT (Rpert b)
    _ ≤ ‖R b‖ * (tau * (2 * ‖R b‖)) := by
      gcongr
    _ = 2 * tau * ‖R b‖ ^ 2 := by ring

/-- Vector-level form of the source-weighted replacement estimate.  Unlike
`abs_quadraticForm_resolventReplacement_le`, this statement does not ask for
an auxiliary linear operator whose value at `b` is the perturbed solution.
It applies directly to the normalized orthogonal component of an actual
eigenvector. -/
theorem abs_quadraticForm_vectorReplacement_le
    (R T : E →ₗ[ℝ] E) (b x : E) (tau alpha : ℝ)
    (hR : R.IsSymmetric)
    (hident : x = R b + R (T x))
    (hRT : ∀ y : E, ‖R (T y)‖ ≤ alpha * ‖y‖)
    (hT : ∀ y : E, ‖T y‖ ≤ tau * ‖y‖)
    (htau : 0 ≤ tau) (halpha : alpha ≤ 1 / 2) :
    |⟪b, x⟫_ℝ - ⟪b, R b⟫_ℝ| ≤
      2 * tau * ‖R b‖ ^ 2 := by
  have hx : ‖x‖ ≤ 2 * ‖R b‖ := by
    have hmain : ‖x‖ ≤ ‖R b‖ + alpha * ‖x‖ := by
      calc
        ‖x‖ = ‖R b + R (T x)‖ := congrArg norm hident
        _ ≤ ‖R b‖ + ‖R (T x)‖ := norm_add_le _ _
        _ ≤ ‖R b‖ + alpha * ‖x‖ :=
          add_le_add (le_refl _) (hRT x)
    nlinarith [norm_nonneg x, norm_nonneg (R b)]
  have hdiff : x - R b = R (T x) := by
    calc
      x - R b = (R b + R (T x)) - R b :=
        congrArg (fun z ↦ z - R b) hident
      _ = R (T x) := by abel
  calc
    |⟪b, x⟫_ℝ - ⟪b, R b⟫_ℝ| = |⟪b, x - R b⟫_ℝ| := by
      rw [inner_sub_right]
    _ = |⟪R b, T x⟫_ℝ| := by rw [hdiff, ← hR b (T x)]
    _ ≤ ‖R b‖ * ‖T x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖R b‖ * (tau * ‖x‖) := by
      gcongr
      exact hT x
    _ ≤ ‖R b‖ * (tau * (2 * ‖R b‖)) := by gcongr
    _ = 2 * tau * ‖R b‖ ^ 2 := by ring

end PrimeStar
