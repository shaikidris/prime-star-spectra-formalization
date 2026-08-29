import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Isolated-mode comparison

This file isolates the finite-dimensional algebra used after matching an
eigenvalue to a normalized reference mode.  Vanishing first order gives an
exact scalar block equation; a lower bound on the reduced operator then gives
the second-order eigenvalue displacement and eigenvector localization bounds.
-/

namespace PrimeStar

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The part of `v` orthogonal to the direction of `u`. -/
def orthogonalRemainder (u v : E) : E :=
  v - ⟪u, v⟫_ℝ • u

/-- The orthogonal-remainder construction as a linear map in its second
argument. -/
def modeOrthogonalProjection (u : E) : E →ₗ[ℝ] E where
  toFun v := orthogonalRemainder u v
  map_add' x y := by
    simp [orthogonalRemainder, inner_add_right, add_smul]
    abel
  map_smul' a x := by
    simp [orthogonalRemainder, real_inner_smul_right, smul_sub, smul_smul]

@[simp]
theorem modeOrthogonalProjection_apply (u v : E) :
    modeOrthogonalProjection u v = orthogonalRemainder u v :=
  rfl

theorem orthogonalRemainder_add_projection (u v : E) :
    ⟪u, v⟫_ℝ • u + orthogonalRemainder u v = v := by
  simp [orthogonalRemainder]

/-- For a unit reference vector, the remainder is orthogonal to it. -/
theorem inner_orthogonalRemainder (u v : E) (hu : ‖u‖ = 1) :
    ⟪u, orthogonalRemainder u v⟫_ℝ = 0 := by
  rw [orthogonalRemainder, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hu]
  norm_num

/-- Orthogonal projection away from a unit vector is contractive. -/
theorem norm_orthogonalRemainder_le (u v : E) (hu : ‖u‖ = 1) :
    ‖orthogonalRemainder u v‖ ≤ ‖v‖ := by
  have horth :
      ⟪⟪u, v⟫_ℝ • u, orthogonalRemainder u v⟫_ℝ = 0 := by
    rw [real_inner_smul_left, inner_orthogonalRemainder u v hu, mul_zero]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  rw [orthogonalRemainder_add_projection u v] at hpyth
  have hsquare : ‖orthogonalRemainder u v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [sq_nonneg ‖⟪u, v⟫_ℝ • u‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

/-- Pythagoras for the orthogonal remainder of two unit vectors. -/
theorem norm_orthogonalRemainder_sq (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖orthogonalRemainder u v‖ ^ 2 = 1 - ⟪u, v⟫_ℝ ^ 2 := by
  have horth : ⟪⟪u, v⟫_ℝ • u, orthogonalRemainder u v⟫_ℝ = 0 := by
    rw [real_inner_smul_left, inner_orthogonalRemainder u v hu, mul_zero]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  rw [orthogonalRemainder_add_projection u v, norm_smul, Real.norm_eq_abs, hu, mul_one,
    hv] at hpyth
  have habs : |⟪u, v⟫_ℝ| ^ 2 = ⟪u, v⟫_ℝ ^ 2 := sq_abs _
  nlinarith

/-- Once two unit vectors are oriented to have nonnegative inner product,
their distance is at most twice the norm of the component orthogonal to the
reference vector. -/
theorem norm_sub_le_two_norm_orthogonalRemainder_of_inner_nonneg
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hinner : 0 ≤ ⟪u, v⟫_ℝ) :
    ‖v - u‖ ≤ 2 * ‖orthogonalRemainder u v‖ := by
  have hinnerUpper : ⟪u, v⟫_ℝ ≤ 1 := by
    have h := abs_real_inner_le_norm u v
    rw [hu, hv, mul_one] at h
    exact le_trans (le_abs_self _) h
  have hw := norm_orthogonalRemainder_sq u v hu hv
  have hdist : ‖v - u‖ ^ 2 = 2 - 2 * ⟪u, v⟫_ℝ := by
    rw [norm_sub_sq_real, hu, hv, real_inner_comm]
    ring
  have hsq : ‖v - u‖ ^ 2 ≤ (2 * ‖orthogonalRemainder u v‖) ^ 2 := by
    rw [hdist, mul_pow, hw]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num) (norm_nonneg _))).mp hsq

/-- A normalized eigenvector near an isolated reference mode can be oriented
by a sign so that its displacement is controlled by the perturbation-to-gap
ratio.  This is the sign-invariant form used for real symmetric eigenspaces. -/
theorem exists_sign_eigenvector_displacement_le_of_isolated_mode
    (L H : E →ₗ[ℝ] E) (u v : E) (mu lam gamma eta : ℝ)
    (hgamma : 0 < gamma)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hLu : L u = mu • u)
    (hAv : (L + H) v = lam • v)
    (hgap : ∀ x : E, ⟪u, x⟫_ℝ = 0 →
      gamma * ‖x‖ ≤ ‖L x - mu • x‖)
    (hH : ∀ x : E, ‖H x‖ ≤ eta * ‖x‖)
    (hnear : |lam - mu| ≤ eta) :
    ∃ sigma : ℝ, sigma ^ 2 = 1 ∧
      ‖sigma • v - u‖ ≤ 4 * eta / gamma := by
  let w := orthogonalRemainder u v
  have hwgap : gamma * ‖w‖ ≤ ‖L w - mu • w‖ :=
    hgap w (inner_orthogonalRemainder u v hu)
  have hid : L w - mu • w = (lam - mu) • v - H v := by
    have hLv : L v = lam • v - H v := by
      rw [eq_sub_iff_add_eq]
      exact hAv
    dsimp [w]
    rw [orthogonalRemainder, map_sub, map_smul, hLu]
    rw [hLv]
    module
  have hwupper : ‖L w - mu • w‖ ≤ 2 * eta := by
    rw [hid]
    calc
      ‖(lam - mu) • v - H v‖ ≤
          ‖(lam - mu) • v‖ + ‖H v‖ := norm_sub_le _ _
      _ ≤ |lam - mu| * ‖v‖ + eta * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact hH v
      _ ≤ 2 * eta := by rw [hv, mul_one, mul_one]; linarith
  have hw : ‖w‖ ≤ 2 * eta / gamma := by
    apply (le_div_iff₀ hgamma).2
    simpa [mul_comm] using hwgap.trans hwupper
  by_cases hsign : 0 ≤ ⟪u, v⟫_ℝ
  · refine ⟨1, by norm_num, ?_⟩
    rw [one_smul]
    calc
      ‖v - u‖ ≤ 2 * ‖w‖ :=
        norm_sub_le_two_norm_orthogonalRemainder_of_inner_nonneg u v hu hv hsign
      _ ≤ 2 * (2 * eta / gamma) := by gcongr
      _ = 4 * eta / gamma := by ring
  · refine ⟨-1, by norm_num, ?_⟩
    have hvneg : ‖-v‖ = 1 := by simpa using hv
    have hinnerNeg : 0 ≤ ⟪u, -v⟫_ℝ := by
      rw [inner_neg_right]
      linarith
    have hwneg : ‖orthogonalRemainder u (-v)‖ = ‖w‖ := by
      rw [orthogonalRemainder, inner_neg_right]
      dsimp [w]
      rw [orthogonalRemainder]
      have : -v - (-⟪u, v⟫_ℝ) • u =
          -(v - ⟪u, v⟫_ℝ • u) := by module
      rw [this, norm_neg]
    simp only [neg_one_smul]
    calc
      ‖-v - u‖ ≤ 2 * ‖orthogonalRemainder u (-v)‖ :=
        norm_sub_le_two_norm_orthogonalRemainder_of_inner_nonneg
          u (-v) hu hvneg hinnerNeg
      _ = 2 * ‖w‖ := by rw [hwneg]
      _ ≤ 2 * (2 * eta / gamma) := by gcongr
      _ = 4 * eta / gamma := by ring

/-- Symmetric eigenpair equations and vanishing first order imply the exact
one-dimensional block equation. -/
theorem isolatedMode_scalarEquation
    (L H : E →ₗ[ℝ] E) (u v : E) (μ lam : ℝ)
    (hL : L.IsSymmetric) (hH : H.IsSymmetric)
    (hLu : L u = μ • u) (hAv : (L + H) v = lam • v)
    (hfirst : ⟪u, H u⟫_ℝ = 0) :
    (lam - μ) * ⟪u, v⟫_ℝ =
      ⟪H u, orthogonalRemainder u v⟫_ℝ := by
  have heig := congrArg (fun z : E ↦ ⟪u, z⟫_ℝ) hAv
  simp only [LinearMap.add_apply, inner_add_right, real_inner_smul_right] at heig
  have hLuv : ⟪u, L v⟫_ℝ = μ * ⟪u, v⟫_ℝ := by
    rw [← hL u v, hLu, real_inner_smul_left]
  have hHuv : ⟪u, H v⟫_ℝ = ⟪H u, v⟫_ℝ := (hH u v).symm
  have hfirst' : ⟪H u, u⟫_ℝ = 0 := by
    rw [hH u u]
    exact hfirst
  have hrem :
      ⟪H u, orthogonalRemainder u v⟫_ℝ = ⟪H u, v⟫_ℝ := by
    rw [orthogonalRemainder, inner_sub_right, real_inner_smul_right, hfirst', mul_zero,
      sub_zero]
  rw [hLuv, hHuv] at heig
  rw [hrem]
  linarith

/-- A lower spectral-gap bound on the reduced operator controls the
orthogonal remainder. -/
theorem norm_orthogonalRemainder_le_of_reducedGap
    (T : E →L[ℝ] E) (u v b : E) (γ : ℝ)
    (hγ : 0 < γ) (hu : ‖u‖ = 1) (hα : 0 < ⟪u, v⟫_ℝ)
    (hT : T (orthogonalRemainder u v) = ⟪u, v⟫_ℝ • b)
    (hgap : ∀ x : E, ⟪u, x⟫_ℝ = 0 → (γ / 2) * ‖x‖ ≤ ‖T x‖) :
    ‖orthogonalRemainder u v‖ ≤
      2 * ⟪u, v⟫_ℝ * ‖b‖ / γ := by
  have h := hgap (orthogonalRemainder u v) (inner_orthogonalRemainder u v hu)
  rw [hT, norm_smul, Real.norm_eq_abs, abs_of_pos hα] at h
  apply (le_div_iff₀ hγ).2
  nlinarith

/-- The scalar block equation and the complement estimate force a
second-order eigenvalue displacement. -/
theorem eigenvalue_displacement_le_of_blockEquations
    (u v b : E) (μ lam γ : ℝ)
    (_hγ : 0 < γ) (hα : 0 < ⟪u, v⟫_ℝ)
    (hscalar : (lam - μ) * ⟪u, v⟫_ℝ =
      ⟪b, orthogonalRemainder u v⟫_ℝ)
    (hrem : ‖orthogonalRemainder u v‖ ≤
      2 * ⟪u, v⟫_ℝ * ‖b‖ / γ) :
    |lam - μ| ≤ 2 * ‖b‖ ^ 2 / γ := by
  have hinner := abs_real_inner_le_norm b (orthogonalRemainder u v)
  have hmul : |lam - μ| * ⟪u, v⟫_ℝ ≤
      ‖b‖ * ‖orthogonalRemainder u v‖ := by
    calc
      |lam - μ| * ⟪u, v⟫_ℝ = |(lam - μ) * ⟪u, v⟫_ℝ| := by
        rw [abs_mul, abs_of_pos hα]
      _ = |⟪b, orthogonalRemainder u v⟫_ℝ| := by rw [hscalar]
      _ ≤ ‖b‖ * ‖orthogonalRemainder u v‖ := hinner
  have hmul' : |lam - μ| * ⟪u, v⟫_ℝ ≤
      (2 * ‖b‖ ^ 2 / γ) * ⟪u, v⟫_ℝ := by
    calc
      |lam - μ| * ⟪u, v⟫_ℝ ≤ ‖b‖ * ‖orthogonalRemainder u v‖ := hmul
      _ ≤ ‖b‖ * (2 * ⟪u, v⟫_ℝ * ‖b‖ / γ) :=
        mul_le_mul_of_nonneg_left hrem (norm_nonneg b)
      _ = (2 * ‖b‖ ^ 2 / γ) * ⟪u, v⟫_ℝ := by ring
  nlinarith

/-- The normalized phase convention and the complement estimate give the
constant `3` localization bound used in the paper. -/
theorem eigenvector_displacement_le_of_remainder
    (u v b : E) (γ : ℝ)
    (hγ : 0 < γ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hα : 0 < ⟪u, v⟫_ℝ)
    (hb : ‖b‖ ≤ γ / 4)
    (hrem : ‖orthogonalRemainder u v‖ ≤
      2 * ⟪u, v⟫_ℝ * ‖b‖ / γ) :
    ‖v - u‖ ≤ 3 * ‖b‖ / γ := by
  let α := ⟪u, v⟫_ℝ
  let w := orthogonalRemainder u v
  have hα0 : 0 ≤ α := hα.le
  have hα1 : α ≤ 1 := by
    have h := abs_real_inner_le_norm u v
    rw [hu, hv, mul_one] at h
    exact le_trans (le_abs_self α) h
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg b
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hw : ‖w‖ ≤ 2 * α * ‖b‖ / γ := hrem
  have hbg : 2 * ‖b‖ / γ ≤ 1 / 2 := by
    apply (div_le_iff₀ hγ).2
    nlinarith
  have hw_half : ‖w‖ ≤ 1 / 2 := by
    calc
      ‖w‖ ≤ 2 * α * ‖b‖ / γ := hw
      _ ≤ 2 * ‖b‖ / γ := by
        apply (div_le_div_iff_of_pos_right hγ).2
        nlinarith
      _ ≤ 1 / 2 := hbg
  have hw_sq : ‖w‖ ^ 2 = 1 - α ^ 2 :=
    norm_orthogonalRemainder_sq u v hu hv
  have hphase : 1 - α ≤ ‖w‖ ^ 2 := by
    nlinarith
  have hw_sq_le : ‖w‖ ^ 2 ≤ ‖w‖ / 2 := by
    nlinarith
  have hdecomp : v - u = w + (α - 1) • u := by
    change v - u = orthogonalRemainder u v + (⟪u, v⟫_ℝ - 1) • u
    calc
      v - u = (⟪u, v⟫_ℝ • u + orthogonalRemainder u v) - u := by
        rw [orthogonalRemainder_add_projection]
      _ = orthogonalRemainder u v + (⟪u, v⟫_ℝ - 1) • u := by
        rw [sub_smul, one_smul]
        abel
  have hdist : ‖v - u‖ ≤ ‖w‖ + (1 - α) := by
    rw [hdecomp]
    calc
      ‖w + (α - 1) • u‖ ≤ ‖w‖ + ‖(α - 1) • u‖ := norm_add_le _ _
      _ = ‖w‖ + (1 - α) := by
        rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_nonpos]
        · ring
        · linarith
  have hdist_w : ‖v - u‖ ≤ 3 * ‖w‖ / 2 := by
    calc
      ‖v - u‖ ≤ ‖w‖ + (1 - α) := hdist
      _ ≤ ‖w‖ + ‖w‖ ^ 2 := by linarith
      _ ≤ 3 * ‖w‖ / 2 := by nlinarith
  calc
    ‖v - u‖ ≤ 3 * ‖w‖ / 2 := hdist_w
    _ ≤ 3 * (2 * α * ‖b‖ / γ) / 2 := by gcongr
    _ = 3 * α * ‖b‖ / γ := by ring
    _ ≤ 3 * ‖b‖ / γ := by
      exact (div_le_div_iff_of_pos_right hγ).2 (by nlinarith)

/-- The complete block-equation comparison: a reduced spectral gap and
vanishing-first-order scalar equation imply the paper's constants `2` and
`3`. -/
theorem isolatedModeComparison
    (T : E →L[ℝ] E) (u v b : E) (μ lam γ : ℝ)
    (hγ : 0 < γ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hα : 0 < ⟪u, v⟫_ℝ) (hb : ‖b‖ ≤ γ / 4)
    (hscalar : (lam - μ) * ⟪u, v⟫_ℝ =
      ⟪b, orthogonalRemainder u v⟫_ℝ)
    (hT : T (orthogonalRemainder u v) = ⟪u, v⟫_ℝ • b)
    (hgap : ∀ x : E, ⟪u, x⟫_ℝ = 0 → (γ / 2) * ‖x‖ ≤ ‖T x‖) :
    |lam - μ| ≤ 2 * ‖b‖ ^ 2 / γ ∧ ‖v - u‖ ≤ 3 * ‖b‖ / γ := by
  have hrem := norm_orthogonalRemainder_le_of_reducedGap T u v b γ hγ hu hα hT hgap
  exact ⟨eigenvalue_displacement_le_of_blockEquations u v b μ lam γ hγ hα hscalar hrem,
    eigenvector_displacement_le_of_remainder u v b γ hγ hu hv hα hb hrem⟩

end PrimeStar
