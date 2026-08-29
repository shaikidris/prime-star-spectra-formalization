import PrimeStar.FiniteResolvent

/-!
# Boundary/interior reassembly

This file formalizes the finite-dimensional source-weighted estimate behind
Lemma 8.4.  A distinguished boundary mode is coupled to an interior block.
The remaining boundary component is controlled by its shifted gap, while the
interior equation is solved by the literal finite resolvent.  The result
compares the exact scalar displacement with the interior quadratic form at a
reference energy.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Source-weighted boundary/interior Feshbach estimate.  The vectors `xB`
and `z` are respectively the boundary-orthogonal and interior components of
the normalized eigenvector.  The conclusion includes both the boundary-mode
mixing error and the exact first-resolvent energy replacement. -/
theorem boundaryInterior_quadraticFormReplacement
    (LB C K J : E →ₗ[ℝ] E) (b xB z : E)
    (lam mu gammaB gammaLam gammaMu eta : ℝ)
    (hgammaB : 0 < gammaB) (hgammaLam : 0 < gammaLam)
    (hgammaMu : 0 < gammaMu) (heta : 0 ≤ eta)
    (hgapLam : ∀ x : E, gammaLam * ‖x‖ ≤ ‖lam • x - C x‖)
    (hgapMu : ∀ x : E, gammaMu * ‖x‖ ≤ ‖mu • x - C x‖)
    (hC : C.IsSymmetric)
    (hboundaryGap : gammaB * ‖xB‖ ≤ ‖lam • xB - LB xB‖)
    (hboundary : lam • xB - LB xB = J z)
    (hinterior : lam • z - C z = b + K xB)
    (hK : ∀ x : E, ‖K x‖ ≤ eta * ‖x‖)
    (hJ : ∀ x : E, ‖J x‖ ≤ eta * ‖x‖)
    (hsmall : gammaB⁻¹ * eta * gammaLam⁻¹ * eta ≤ 1 / 2) :
    let Rlam := finiteResolventOfGap C lam gammaLam hgammaLam hgapLam
    let Rmu := finiteResolventOfGap C mu gammaMu hgammaMu hgapMu
    |⟪b, z⟫_ℝ - ⟪b, Rmu b⟫_ℝ| ≤
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
        |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖ := by
  dsimp only
  let Rlam := finiteResolventOfGap C lam gammaLam hgammaLam hgapLam
  let Rmu := finiteResolventOfGap C mu gammaMu hgammaMu hgapMu
  change |⟪b, z⟫_ℝ - ⟪b, Rmu b⟫_ℝ| ≤
    2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
      |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖
  have hgammaBinv : 0 ≤ gammaB⁻¹ := inv_nonneg.mpr hgammaB.le
  have hgammaLaminv : 0 ≤ gammaLam⁻¹ := inv_nonneg.mpr hgammaLam.le
  have hRlamBound (x : E) : ‖Rlam x‖ ≤ gammaLam⁻¹ * ‖x‖ :=
    norm_finiteResolventOfGap_apply_le C lam gammaLam hgammaLam hgapLam x
  have hz : z = Rlam b + Rlam (K xB) := by
    calc
      z = Rlam (lam • z - C z) :=
        (finiteResolventOfGap_shift_apply
          C lam gammaLam hgammaLam hgapLam z).symm
      _ = Rlam (b + K xB) := by rw [hinterior]
      _ = Rlam b + Rlam (K xB) := by rw [map_add]
  have hboundaryNorm : gammaB * ‖xB‖ ≤ eta * ‖z‖ := by
    calc
      gammaB * ‖xB‖ ≤ ‖lam • xB - LB xB‖ := hboundaryGap
      _ = ‖J z‖ := by rw [hboundary]
      _ ≤ eta * ‖z‖ := hJ z
  have hxbz : ‖xB‖ ≤ gammaB⁻¹ * eta * ‖z‖ := by
    calc
      ‖xB‖ ≤ (eta * ‖z‖) / gammaB := by
        apply (le_div_iff₀ hgammaB).2
        simpa [mul_comm] using hboundaryNorm
      _ = gammaB⁻¹ * eta * ‖z‖ := by
        rw [div_eq_mul_inv]
        ring
  have hzNorm : ‖z‖ ≤ ‖Rlam b‖ + gammaLam⁻¹ * eta * ‖xB‖ := by
    calc
      ‖z‖ = ‖Rlam b + Rlam (K xB)‖ := congrArg norm hz
      _ ≤ ‖Rlam b‖ + ‖Rlam (K xB)‖ := norm_add_le _ _
      _ ≤ ‖Rlam b‖ + gammaLam⁻¹ * ‖K xB‖ :=
        by
          simpa [add_comm] using
            (add_le_add_left (hRlamBound (K xB)) ‖Rlam b‖)
      _ ≤ ‖Rlam b‖ + gammaLam⁻¹ * (eta * ‖xB‖) := by
        gcongr
        exact hK xB
      _ = ‖Rlam b‖ + gammaLam⁻¹ * eta * ‖xB‖ := by ring
  have hxbMain : ‖xB‖ ≤
      gammaB⁻¹ * eta * ‖Rlam b‖ +
        (gammaB⁻¹ * eta * gammaLam⁻¹ * eta) * ‖xB‖ := by
    calc
      ‖xB‖ ≤ gammaB⁻¹ * eta * ‖z‖ := hxbz
      _ ≤ gammaB⁻¹ * eta *
          (‖Rlam b‖ + gammaLam⁻¹ * eta * ‖xB‖) := by
        gcongr
      _ = gammaB⁻¹ * eta * ‖Rlam b‖ +
          (gammaB⁻¹ * eta * gammaLam⁻¹ * eta) * ‖xB‖ := by
        ring
  have hxb : ‖xB‖ ≤ 2 * (gammaB⁻¹ * eta) * ‖Rlam b‖ := by
    nlinarith [norm_nonneg xB, norm_nonneg (Rlam b),
      mul_nonneg hgammaBinv heta]
  have hRlamSym : Rlam.IsSymmetric :=
    finiteResolventOfGap_isSymmetric C lam gammaLam hgammaLam hgapLam hC
  have hboundaryError :
      |⟪b, z⟫_ℝ - ⟪b, Rlam b⟫_ℝ| ≤
        2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 := by
    have hinner :
        ⟪b, z⟫_ℝ - ⟪b, Rlam b⟫_ℝ =
          ⟪Rlam b, K xB⟫_ℝ := by
      calc
        ⟪b, z⟫_ℝ - ⟪b, Rlam b⟫_ℝ =
            ⟪b, Rlam (K xB)⟫_ℝ := by
          rw [hz, inner_add_right]
          ring
        _ = ⟪Rlam b, K xB⟫_ℝ := (hRlamSym b (K xB)).symm
    rw [hinner]
    calc
      |⟪Rlam b, K xB⟫_ℝ| ≤ ‖Rlam b‖ * ‖K xB‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖Rlam b‖ * (eta * ‖xB‖) := by gcongr; exact hK xB
      _ ≤ ‖Rlam b‖ *
          (eta * (2 * (gammaB⁻¹ * eta) * ‖Rlam b‖)) := by gcongr
      _ = 2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 := by ring
  have henergy := abs_inner_finiteResolventOfGap_sub_le
    C lam mu gammaLam gammaMu hgammaLam hgammaMu hgapLam hgapMu hC b
  calc
    |⟪b, z⟫_ℝ - ⟪b, Rmu b⟫_ℝ| ≤
        |⟪b, z⟫_ℝ - ⟪b, Rlam b⟫_ℝ| +
          |⟪b, Rlam b⟫_ℝ - ⟪b, Rmu b⟫_ℝ| := by
      exact _root_.abs_sub_le _ _ _
    _ ≤ 2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
        |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖ :=
      add_le_add hboundaryError henergy

end

end PrimeStar
