import PrimeStar.SpectralMatching

/-!
# Finite-dimensional resolvents from a lower gap

The paper repeatedly uses the elementary implication

`gamma * ‖x‖ ≤ ‖T x‖`, `gamma > 0`

for a finite-dimensional endomorphism `T`: the operator is invertible, its
inverse has norm at most `gamma⁻¹`, and symmetry passes to the inverse.  This
file packages that implication without adding a spectral or analytic axiom.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A positive lower norm bound makes an endomorphism injective. -/
theorem injective_of_lowerBound
    (T : E →ₗ[ℝ] E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : E, gamma * ‖x‖ ≤ ‖T x‖) : Function.Injective T := by
  intro x y hxy
  have hzero : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hbound := hlower (x - y)
  rw [hzero, norm_zero] at hbound
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The inverse of a finite-dimensional endomorphism supplied with a positive
lower norm bound. -/
def inverseOfLowerBound
    (T : E →ₗ[ℝ] E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : E, gamma * ‖x‖ ≤ ‖T x‖) : E →ₗ[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo T
    (injective_of_lowerBound T gamma hgamma hlower)).symm.toLinearMap

@[simp]
theorem inverseOfLowerBound_apply_shift
    (T : E →ₗ[ℝ] E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : E, gamma * ‖x‖ ≤ ‖T x‖) (x : E) :
    inverseOfLowerBound T gamma hgamma hlower (T x) = x := by
  unfold inverseOfLowerBound
  exact (LinearEquiv.ofInjectiveEndo T
    (injective_of_lowerBound T gamma hgamma hlower)).symm_apply_apply x

@[simp]
theorem shift_apply_inverseOfLowerBound
    (T : E →ₗ[ℝ] E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : E, gamma * ‖x‖ ≤ ‖T x‖) (x : E) :
    T (inverseOfLowerBound T gamma hgamma hlower x) = x := by
  unfold inverseOfLowerBound
  exact (LinearEquiv.ofInjectiveEndo T
    (injective_of_lowerBound T gamma hgamma hlower)).apply_symm_apply x

/-- Source-weighted norm estimate for the inverse constructed from the gap. -/
theorem norm_inverseOfLowerBound_apply_le
    (T : E →ₗ[ℝ] E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : E, gamma * ‖x‖ ≤ ‖T x‖) (x : E) :
    ‖inverseOfLowerBound T gamma hgamma hlower x‖ ≤ gamma⁻¹ * ‖x‖ := by
  have h := hlower (inverseOfLowerBound T gamma hgamma hlower x)
  rw [shift_apply_inverseOfLowerBound] at h
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hgamma).2
  simpa [mul_comm] using h

/-- The inverse of a symmetric finite-dimensional endomorphism is symmetric. -/
theorem inverseOfLowerBound_isSymmetric
    (T : E →ₗ[ℝ] E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : E, gamma * ‖x‖ ≤ ‖T x‖)
    (hT : T.IsSymmetric) :
    (inverseOfLowerBound T gamma hgamma hlower).IsSymmetric := by
  intro x y
  let R := inverseOfLowerBound T gamma hgamma hlower
  calc
    ⟪R x, y⟫_ℝ = ⟪R x, T (R y)⟫_ℝ := by
      rw [shift_apply_inverseOfLowerBound]
    _ = ⟪T (R x), R y⟫_ℝ := (hT (R x) (R y)).symm
    _ = ⟪x, R y⟫_ℝ := by
      rw [shift_apply_inverseOfLowerBound]

/-- The shifted operator `mu I - C`. -/
def shiftedEndomorphism (C : E →ₗ[ℝ] E) (mu : ℝ) : E →ₗ[ℝ] E :=
  mu • LinearMap.id - C

@[simp]
theorem shiftedEndomorphism_apply (C : E →ₗ[ℝ] E) (mu : ℝ) (x : E) :
    shiftedEndomorphism C mu x = mu • x - C x := by
  simp [shiftedEndomorphism]

/-- A lower spectral gap for `mu - C` produces its literal finite resolvent. -/
def finiteResolventOfGap
    (C : E →ₗ[ℝ] E) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : E, gamma * ‖x‖ ≤ ‖mu • x - C x‖) : E →ₗ[ℝ] E :=
  inverseOfLowerBound (shiftedEndomorphism C mu) gamma hgamma (by
    intro x
    simpa using hgap x)

@[simp]
theorem finiteResolventOfGap_shift_apply
    (C : E →ₗ[ℝ] E) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : E, gamma * ‖x‖ ≤ ‖mu • x - C x‖) (x : E) :
    finiteResolventOfGap C mu gamma hgamma hgap (mu • x - C x) = x := by
  exact inverseOfLowerBound_apply_shift
    (shiftedEndomorphism C mu) gamma hgamma (by
      intro y
      simpa using hgap y) x

@[simp]
theorem finiteResolventOfGap_apply_inverse
    (C : E →ₗ[ℝ] E) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : E, gamma * ‖x‖ ≤ ‖mu • x - C x‖) (x : E) :
    mu • finiteResolventOfGap C mu gamma hgamma hgap x -
        C (finiteResolventOfGap C mu gamma hgamma hgap x) = x := by
  exact shift_apply_inverseOfLowerBound
    (shiftedEndomorphism C mu) gamma hgamma (by
      intro y
      simpa using hgap y) x

theorem norm_finiteResolventOfGap_apply_le
    (C : E →ₗ[ℝ] E) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : E, gamma * ‖x‖ ≤ ‖mu • x - C x‖) (x : E) :
    ‖finiteResolventOfGap C mu gamma hgamma hgap x‖ ≤ gamma⁻¹ * ‖x‖ := by
  exact norm_inverseOfLowerBound_apply_le
    (shiftedEndomorphism C mu) gamma hgamma (by
      intro y
      simpa using hgap y) x

theorem finiteResolventOfGap_isSymmetric
    (C : E →ₗ[ℝ] E) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : E, gamma * ‖x‖ ≤ ‖mu • x - C x‖)
    (hC : C.IsSymmetric) :
    (finiteResolventOfGap C mu gamma hgamma hgap).IsSymmetric := by
  apply inverseOfLowerBound_isSymmetric
  intro x y
  simp only [shiftedEndomorphism_apply, inner_sub_right, inner_sub_left,
    real_inner_smul_right, real_inner_smul_left]
  rw [hC]

/-- First resolvent identity, pointwise and with both inverses constructed
from positive lower gaps. -/
theorem finiteResolventOfGap_sub_apply
    (C : E →ₗ[ℝ] E) (lam mu gammaLam gammaMu : ℝ)
    (hgammaLam : 0 < gammaLam) (hgammaMu : 0 < gammaMu)
    (hgapLam : ∀ x : E, gammaLam * ‖x‖ ≤ ‖lam • x - C x‖)
    (hgapMu : ∀ x : E, gammaMu * ‖x‖ ≤ ‖mu • x - C x‖)
    (b : E) :
    finiteResolventOfGap C lam gammaLam hgammaLam hgapLam b -
        finiteResolventOfGap C mu gammaMu hgammaMu hgapMu b =
      (mu - lam) •
        finiteResolventOfGap C lam gammaLam hgammaLam hgapLam
          (finiteResolventOfGap C mu gammaMu hgammaMu hgapMu b) := by
  let Rlam := finiteResolventOfGap C lam gammaLam hgammaLam hgapLam
  let Rmu := finiteResolventOfGap C mu gammaMu hgammaMu hgapMu
  have hRlamShift (x : E) : Rlam (lam • x - C x) = x := by
    exact finiteResolventOfGap_shift_apply C lam gammaLam hgammaLam hgapLam x
  have hRmuInv : mu • Rmu b - C (Rmu b) = b := by
    exact finiteResolventOfGap_apply_inverse C mu gammaMu hgammaMu hgapMu b
  have hsource :
      b - (lam • Rmu b - C (Rmu b)) = (mu - lam) • Rmu b := by
    calc
      b - (lam • Rmu b - C (Rmu b)) =
          (mu • Rmu b - C (Rmu b)) -
            (lam • Rmu b - C (Rmu b)) := by rw [hRmuInv]
      _ = mu • Rmu b - lam • Rmu b := by abel
      _ = (mu - lam) • Rmu b := by rw [sub_smul]
  calc
    Rlam b - Rmu b = Rlam b - Rlam (lam • Rmu b - C (Rmu b)) := by
      rw [hRlamShift]
    _ = Rlam (b - (lam • Rmu b - C (Rmu b))) :=
      (map_sub Rlam b (lam • Rmu b - C (Rmu b))).symm
    _ = Rlam ((mu - lam) • Rmu b) := by rw [hsource]
    _ = (mu - lam) • Rlam (Rmu b) := by rw [map_smul]

/-- Source-weighted scalar consequence of the first resolvent identity. -/
theorem abs_inner_finiteResolventOfGap_sub_le
    (C : E →ₗ[ℝ] E) (lam mu gammaLam gammaMu : ℝ)
    (hgammaLam : 0 < gammaLam) (hgammaMu : 0 < gammaMu)
    (hgapLam : ∀ x : E, gammaLam * ‖x‖ ≤ ‖lam • x - C x‖)
    (hgapMu : ∀ x : E, gammaMu * ‖x‖ ≤ ‖mu • x - C x‖)
    (hC : C.IsSymmetric)
    (b : E) :
    |⟪b, finiteResolventOfGap C lam gammaLam hgammaLam hgapLam b⟫_ℝ -
        ⟪b, finiteResolventOfGap C mu gammaMu hgammaMu hgapMu b⟫_ℝ| ≤
      |lam - mu| *
        ‖finiteResolventOfGap C lam gammaLam hgammaLam hgapLam b‖ *
        ‖finiteResolventOfGap C mu gammaMu hgammaMu hgapMu b‖ := by
  let Rlam := finiteResolventOfGap C lam gammaLam hgammaLam hgapLam
  let Rmu := finiteResolventOfGap C mu gammaMu hgammaMu hgapMu
  have hRlam : Rlam.IsSymmetric :=
    finiteResolventOfGap_isSymmetric C lam gammaLam hgammaLam hgapLam hC
  rw [← inner_sub_right, finiteResolventOfGap_sub_apply]
  rw [real_inner_smul_right, abs_mul, abs_sub_comm]
  calc
    |lam - mu| * |⟪b, Rlam (Rmu b)⟫_ℝ| =
        |lam - mu| * |⟪Rlam b, Rmu b⟫_ℝ| := by
      rw [← hRlam b (Rmu b)]
    _ ≤ |lam - mu| * (‖Rlam b‖ * ‖Rmu b‖) := by
      gcongr
      exact abs_real_inner_le_norm (Rlam b) (Rmu b)
    _ = |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖ := by ring

/-- The exact effective interaction obtained by eliminating a complementary
block at energy `lam` and comparing the surviving block with the reference
energy `mu`. -/
def feshbachEffectiveInteraction
    (K RW J : E →ₗ[ℝ] E) (mu lam : ℝ) : E →ₗ[ℝ] E :=
  (mu - lam) • LinearMap.id + K.comp (RW.comp J)

@[simp]
theorem feshbachEffectiveInteraction_apply
    (K RW J : E →ₗ[ℝ] E) (mu lam : ℝ) (x : E) :
    feshbachEffectiveInteraction K RW J mu lam x =
      (mu - lam) • x + K (RW (J x)) := by
  simp [feshbachEffectiveInteraction]

/-- Exact two-block Feshbach identity.  The `W` equation is solved by `RW`;
the `U` equation is then rewritten at the reference energy `mu` and inverted
by `R`. -/
theorem feshbachReducedVectorIdentity
    (L K RW J R : E →ₗ[ℝ] E) (b xU xW : E) (mu lam : ℝ)
    (hRleft : ∀ y : E, R (mu • y - L y) = y)
    (hW : xW = RW (J xU))
    (hU : lam • xU - L xU - K xW = b) :
    xU = R b + R (feshbachEffectiveInteraction K RW J mu lam xU) := by
  have hshift : mu • xU - L xU =
      b + feshbachEffectiveInteraction K RW J mu lam xU := by
    rw [feshbachEffectiveInteraction_apply, ← hW]
    rw [← hU]
    module
  calc
    xU = R (mu • xU - L xU) := (hRleft xU).symm
    _ = R (b + feshbachEffectiveInteraction K RW J mu lam xU) := by
      rw [hshift]
    _ = R b + R (feshbachEffectiveInteraction K RW J mu lam xU) := by
      rw [map_add]

/-- Pointwise norm bound for the exact effective interaction. -/
theorem norm_feshbachEffectiveInteraction_apply_le
    (K RW J : E →ₗ[ℝ] E) (mu lam kappa omega jappa : ℝ)
    (hkappa : 0 ≤ kappa) (homega : 0 ≤ omega) (hjappa : 0 ≤ jappa)
    (hK : ∀ x : E, ‖K x‖ ≤ kappa * ‖x‖)
    (hRW : ∀ x : E, ‖RW x‖ ≤ omega * ‖x‖)
    (hJ : ∀ x : E, ‖J x‖ ≤ jappa * ‖x‖)
    (x : E) :
    ‖feshbachEffectiveInteraction K RW J mu lam x‖ ≤
      (|mu - lam| + kappa * omega * jappa) * ‖x‖ := by
  rw [feshbachEffectiveInteraction_apply]
  calc
    ‖(mu - lam) • x + K (RW (J x))‖ ≤
        ‖(mu - lam) • x‖ + ‖K (RW (J x))‖ := norm_add_le _ _
    _ ≤ |mu - lam| * ‖x‖ + kappa * ‖RW (J x)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      exact hK _
    _ ≤ |mu - lam| * ‖x‖ + kappa * (omega * ‖J x‖) := by
      gcongr
      exact hRW _
    _ ≤ |mu - lam| * ‖x‖ + kappa * (omega * (jappa * ‖x‖)) := by
      gcongr
      exact hJ _
    _ = (|mu - lam| + kappa * omega * jappa) * ‖x‖ := by ring

/-- Composing the effective interaction with a pointwise-bounded reference
resolvent gives the contraction certificate used in Lemma 8.6. -/
theorem norm_resolvent_feshbachEffectiveInteraction_apply_le
    (R K RW J : E →ₗ[ℝ] E)
    (mu lam rbound kappa omega jappa : ℝ)
    (hrbound : 0 ≤ rbound) (hkappa : 0 ≤ kappa)
    (homega : 0 ≤ omega) (hjappa : 0 ≤ jappa)
    (hR : ∀ x : E, ‖R x‖ ≤ rbound * ‖x‖)
    (hK : ∀ x : E, ‖K x‖ ≤ kappa * ‖x‖)
    (hRW : ∀ x : E, ‖RW x‖ ≤ omega * ‖x‖)
    (hJ : ∀ x : E, ‖J x‖ ≤ jappa * ‖x‖)
    (x : E) :
    ‖R (feshbachEffectiveInteraction K RW J mu lam x)‖ ≤
      (rbound * (|mu - lam| + kappa * omega * jappa)) * ‖x‖ := by
  calc
    ‖R (feshbachEffectiveInteraction K RW J mu lam x)‖ ≤
        rbound * ‖feshbachEffectiveInteraction K RW J mu lam x‖ := hR _
    _ ≤ rbound *
        ((|mu - lam| + kappa * omega * jappa) * ‖x‖) := by
      gcongr
      exact norm_feshbachEffectiveInteraction_apply_le K RW J mu lam
        kappa omega jappa hkappa homega hjappa hK hRW hJ x
    _ = (rbound * (|mu - lam| + kappa * omega * jappa)) * ‖x‖ := by
      ring

end

end PrimeStar
