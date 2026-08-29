import PrimeStar.IsolatedMode
import PrimeStar.OrderedEigenvaluePerturbation
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Finite spectral matching and simplicity

This file supplies the smallest spectral-theorem layer needed to pass from an
exact isolated mode of a symmetric reference operator to a matched simple
eigenvalue of a symmetric perturbation.  It deliberately avoids developing a
general Weyl-inequality API.
-/

namespace PrimeStar

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

/-- Scalar separation of the ordered eigenvalues gives the two-sided
operator gap on the orthogonal complement of the corresponding canonical
eigenvector. -/
theorem isolatedModeGap_of_eigenvalueSeparation
    [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] E) (hL : L.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (hsep : ∀ j : Fin (Module.finrank ℝ E), j ≠ i →
      gamma ≤ |hL.eigenvalues rfl j - hL.eigenvalues rfl i|)
    (x : E)
    (hxi : ⟪hL.eigenvectorBasis rfl i, x⟫_ℝ = 0) :
    gamma * ‖x‖ ≤
      ‖L x - hL.eigenvalues rfl i • x‖ := by
  let b := hL.eigenvectorBasis rfl
  let ev := hL.eigenvalues rfl
  let y := L x - ev i • x
  have hcoeffi : b.repr x i = 0 := by
    rw [b.repr_apply_apply]
    exact hxi
  have hycoeff : ∀ j, b.repr y j = (ev j - ev i) * b.repr x j := by
    intro j
    have hdiag := hL.eigenvectorBasis_apply_self_apply rfl x j
    change b.repr (L x) j = ev j * b.repr x j at hdiag
    dsimp [y]
    rw [map_sub, map_smul]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hdiag]
    ring
  have hsum :
      gamma ^ 2 * ∑ j, (b.repr x j) ^ 2 ≤
        ∑ j, ((ev j - ev i) * b.repr x j) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hji : j = i
    · subst j
      simp [hcoeffi]
    · have hgapAbs := hsep j hji
      have hgapSq : gamma ^ 2 ≤ (ev j - ev i) ^ 2 := by
        calc
          gamma ^ 2 ≤ |ev j - ev i| ^ 2 :=
            (sq_le_sq₀ hgamma (abs_nonneg _)).2 hgapAbs
          _ = (ev j - ev i) ^ 2 := sq_abs _
      calc
        gamma ^ 2 * (b.repr x j) ^ 2 ≤
            (ev j - ev i) ^ 2 * (b.repr x j) ^ 2 :=
          mul_le_mul_of_nonneg_right hgapSq (sq_nonneg _)
        _ = ((ev j - ev i) * b.repr x j) ^ 2 := by ring
  have hsq :
      (gamma * ‖x‖) ^ 2 ≤ ‖y‖ ^ 2 := by
    calc
      (gamma * ‖x‖) ^ 2 =
          gamma ^ 2 * ∑ j, (b.repr x j) ^ 2 := by
            rw [mul_pow, ← b.repr.norm_map x,
              EuclideanSpace.real_norm_sq_eq]
      _ ≤ ∑ j, ((ev j - ev i) * b.repr x j) ^ 2 := hsum
      _ = ∑ j, (b.repr y j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hycoeff]
      _ = ‖b.repr y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      _ = ‖y‖ ^ 2 := by rw [b.repr.norm_map]
  have hleft : 0 ≤ gamma * ‖x‖ :=
    mul_nonneg hgamma (norm_nonneg x)
  have hright := norm_nonneg y
  nlinarith

/-- A unit approximate eigenvector of a real symmetric finite-dimensional
operator lies within its residual norm of an actual eigenvalue. -/
theorem exists_eigenvalue_near_of_residual
    [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (u : E) (mu : ℝ)
    (hu : ‖u‖ = 1) :
    ∃ i : Fin (Module.finrank ℝ E),
      |hA.eigenvalues rfl i - mu| ≤ ‖A u - mu • u‖ := by
  let n := Module.finrank ℝ E
  let b := hA.eigenvectorBasis (n := n) rfl
  let c : EuclideanSpace ℝ (Fin n) := b.repr u
  let r : E := A u - mu • u
  have hu0 : u ≠ 0 := by
    intro huz
    simp [huz] at hu
  have hc0 : c ≠ 0 := by
    intro hc
    apply hu0
    apply b.repr.injective
    simpa [c] using hc
  have hcex : ∃ i : Fin n, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply hc0
    ext i
    simpa using h i
  have hrcoord (i : Fin n) :
      b.repr r i = (hA.eigenvalues rfl i - mu) * c i := by
    dsimp [r, c]
    simp only [map_sub, map_smul]
    change b.repr (A u) i - mu * b.repr u i =
      (hA.eigenvalues rfl i - mu) * b.repr u i
    rw [show b.repr (A u) i = hA.eigenvalues rfl i * b.repr u i by
      simpa [b] using hA.eigenvectorBasis_apply_self_apply (hn := rfl) u i]
    ring
  have hcnorm : ∑ i, ‖c i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, show ‖c‖ = ‖u‖ by simp [c, b], hu]
    norm_num
  have hrnorm : ∑ i, ‖b.repr r i‖ ^ 2 = ‖r‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, show ‖b.repr r‖ = ‖r‖ by simp [b]]
  by_contra hnear
  push Not at hnear
  have hterm (i : Fin n) :
      ‖r‖ ^ 2 * ‖c i‖ ^ 2 ≤ ‖b.repr r i‖ ^ 2 := by
    rw [hrcoord, norm_mul, Real.norm_eq_abs]
    have hi := hnear i
    change ‖r‖ < |hA.eigenvalues rfl i - mu| at hi
    rw [mul_pow]
    gcongr
    simpa [Real.norm_eq_abs] using hi.le
  obtain ⟨i0, hi0⟩ := hcex
  have hstrict : ‖r‖ ^ 2 * ‖c i0‖ ^ 2 < ‖b.repr r i0‖ ^ 2 := by
    rw [hrcoord, norm_mul, Real.norm_eq_abs]
    have hi := hnear i0
    change ‖r‖ < |hA.eigenvalues rfl i0 - mu| at hi
    have hci : 0 < ‖c i0‖ := norm_pos_iff.mpr hi0
    rw [mul_pow]
    exact mul_lt_mul_of_pos_right
      ((sq_lt_sq₀ (norm_nonneg r) (abs_nonneg _)).mpr hi) (sq_pos_of_pos hci)
  have hsum :
      ∑ i, ‖r‖ ^ 2 * ‖c i‖ ^ 2 < ∑ i, ‖b.repr r i‖ ^ 2 := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hterm i
    · exact ⟨i0, Finset.mem_univ _, hstrict⟩
  rw [← Finset.mul_sum, hcnorm, mul_one, hrnorm] at hsum
  exact lt_irrefl _ hsum

/-- If the inner-product coordinate along `u` has trivial kernel on an
eigenspace, then that eigenspace has dimension at most one. -/
theorem eigenspace_finrank_le_one_of_inner_kernel
    (A : E →ₗ[ℝ] E) (u : E) (lam : ℝ)
    (hker : ∀ x : E, x ∈ Module.End.eigenspace A lam →
      ⟪u, x⟫_ℝ = 0 → x = 0) :
    Module.finrank ℝ (Module.End.eigenspace A lam) ≤ 1 := by
  let f : Module.End.eigenspace A lam →ₗ[ℝ] ℝ :=
    (innerSL ℝ u).toLinearMap.domRestrict (Module.End.eigenspace A lam)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hker (x - y)
    · exact Submodule.sub_mem _ x.property y.property
    · change f (x - y) = 0
      rw [map_sub, hxy, sub_self]
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  simpa using hdim

/-- A two-sided gap around a reference mode makes every sufficiently nearby
eigenspace of `L + H` at most one-dimensional. -/
theorem eigenspace_finrank_le_one_of_isolated_mode
    (L H : E →ₗ[ℝ] E) (u : E) (mu lam gamma eta : ℝ)
    (hgap : ∀ x : E, ⟪u, x⟫_ℝ = 0 →
      gamma * ‖x‖ ≤ ‖L x - mu • x‖)
    (hH : ∀ x : E, ‖H x‖ ≤ eta * ‖x‖)
    (hnear : |lam - mu| + eta < gamma) :
    Module.finrank ℝ (Module.End.eigenspace (L + H) lam) ≤ 1 := by
  apply eigenspace_finrank_le_one_of_inner_kernel (L + H) u lam
  intro x hx hux
  have heig : (L + H) x = lam • x :=
    Module.End.mem_eigenspace_iff.mp hx
  have hid : L x - mu • x = (lam - mu) • x - H x := by
    rw [LinearMap.add_apply] at heig
    calc
      L x - mu • x = (L x + H x) - mu • x - H x := by abel
      _ = lam • x - mu • x - H x := by rw [heig]
      _ = (lam - mu) • x - H x := by rw [sub_smul]
  have hlower := hgap x hux
  have hupper : ‖L x - mu • x‖ ≤ (|lam - mu| + eta) * ‖x‖ := by
    rw [hid]
    calc
      ‖(lam - mu) • x - H x‖ ≤ ‖(lam - mu) • x‖ + ‖H x‖ := norm_sub_le _ _
      _ ≤ |lam - mu| * ‖x‖ + eta * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact hH x
      _ = (|lam - mu| + eta) * ‖x‖ := by ring
  have hxnorm : ‖x‖ = 0 := by
    by_contra hx0
    have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
    have : gamma * ‖x‖ < gamma * ‖x‖ :=
      lt_of_le_of_lt hlower (lt_of_le_of_lt hupper
        (mul_lt_mul_of_pos_right hnear hxpos))
    exact lt_irrefl _ this
  exact norm_eq_zero.mp hxnorm

/-- Residual matching plus a two-sided isolated-mode gap produces an actual
simple eigenvalue of `L + H` near `mu`. -/
theorem exists_simple_eigenvalue_near_of_isolated_mode
    [FiniteDimensional ℝ E]
    (L H : E →ₗ[ℝ] E) (hL : L.IsSymmetric) (hHsymm : H.IsSymmetric)
    (u : E) (mu gamma eta : ℝ)
    (hu : ‖u‖ = 1) (hLu : L u = mu • u)
    (hgap : ∀ x : E, ⟪u, x⟫_ℝ = 0 →
      gamma * ‖x‖ ≤ ‖L x - mu • x‖)
    (hH : ∀ x : E, ‖H x‖ ≤ eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    ∃ i : Fin (Module.finrank ℝ E),
      |(hL.add hHsymm).eigenvalues rfl i - mu| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace (L + H) ((hL.add hHsymm).eigenvalues rfl i)) = 1 := by
  let hA := hL.add hHsymm
  obtain ⟨i, hi⟩ := exists_eigenvalue_near_of_residual (L + H) hA u mu hu
  have hres : ‖(L + H) u - mu • u‖ ≤ eta := by
    rw [LinearMap.add_apply, hLu, add_sub_cancel_left]
    simpa [hu] using hH u
  have hinear : |hA.eigenvalues rfl i - mu| ≤ eta := hi.trans hres
  refine ⟨i, hinear, ?_⟩
  have hle : Module.finrank ℝ
      (Module.End.eigenspace (L + H) (hA.eigenvalues rfl i)) ≤ 1 :=
    eigenspace_finrank_le_one_of_isolated_mode L H u mu
      (hA.eigenvalues rfl i) gamma eta hgap hH
      (calc
        |hA.eigenvalues rfl i - mu| + eta ≤ eta + eta :=
          add_le_add hinear (le_refl eta)
        _ = 2 * eta := by ring
        _ < gamma := hsmall)
  have hge : 1 ≤ Module.finrank ℝ
      (Module.End.eigenspace (L + H) (hA.eigenvalues rfl i)) := by
    rw [Submodule.one_le_finrank_iff]
    exact Module.End.hasEigenvalue_iff.mp (hA.hasEigenvalue_eigenvalues rfl i)
  exact Nat.le_antisymm hle hge

/-- Ordered-eigenvalue version of the simple matching theorem.  Instead of an
opaque operator-gap hypothesis, it assumes scalar separation of one entry in
the ordered spectrum of the symmetric reference operator. -/
theorem exists_simple_eigenvalue_near_of_separated_ordered_mode
    [FiniteDimensional ℝ E]
    (L H : E →ₗ[ℝ] E) (hL : L.IsSymmetric) (hHsymm : H.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) (gamma eta : ℝ)
    (hgamma : 0 ≤ gamma)
    (hsep : ∀ j : Fin (Module.finrank ℝ E), j ≠ i →
      gamma ≤ |hL.eigenvalues rfl j - hL.eigenvalues rfl i|)
    (hH : ∀ x : E, ‖H x‖ ≤ eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    ∃ k : Fin (Module.finrank ℝ E),
      |(hL.add hHsymm).eigenvalues rfl k - hL.eigenvalues rfl i| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace (L + H)
          ((hL.add hHsymm).eigenvalues rfl k)) = 1 := by
  apply exists_simple_eigenvalue_near_of_isolated_mode
    L H hL hHsymm (hL.eigenvectorBasis rfl i)
      (hL.eigenvalues rfl i) gamma eta
  · exact (hL.eigenvectorBasis rfl).orthonormal.norm_eq_one i
  · exact hL.apply_eigenvectorBasis rfl i
  · intro x hxi
    exact isolatedModeGap_of_eigenvalueSeparation
      L hL i gamma hgamma hsep x hxi
  · exact hH
  · exact hsmall

/-- The ordered-index strengthening of
`exists_simple_eigenvalue_near_of_separated_ordered_mode`.  The ordered Weyl
bound fixes the matched eigenvalue at the same index `i`; the isolated-mode
gap then proves that this prescribed entry is simple. -/
theorem simple_orderedEigenvalue_near_of_separated_ordered_mode
    [FiniteDimensional ℝ E]
    (L H : E →ₗ[ℝ] E) (hL : L.IsSymmetric) (hHsymm : H.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) (gamma eta : ℝ)
    (hgamma : 0 ≤ gamma)
    (hsep : ∀ j : Fin (Module.finrank ℝ E), j ≠ i →
      gamma ≤ |hL.eigenvalues rfl j - hL.eigenvalues rfl i|)
    (hH : ∀ x : E, ‖H x‖ ≤ eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    |(hL.add hHsymm).eigenvalues rfl i - hL.eigenvalues rfl i| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace (L + H)
          ((hL.add hHsymm).eigenvalues rfl i)) = 1 := by
  have hnear := abs_orderedEigenvalue_add_sub_le L H hL hHsymm i eta hH
  refine ⟨hnear, ?_⟩
  have hle : Module.finrank ℝ
      (Module.End.eigenspace (L + H)
        ((hL.add hHsymm).eigenvalues rfl i)) ≤ 1 :=
    eigenspace_finrank_le_one_of_isolated_mode L H
      (hL.eigenvectorBasis rfl i) (hL.eigenvalues rfl i)
      ((hL.add hHsymm).eigenvalues rfl i) gamma eta
      (fun x hxi ↦ isolatedModeGap_of_eigenvalueSeparation
        L hL i gamma hgamma hsep x hxi)
      hH
      (calc
        |(hL.add hHsymm).eigenvalues rfl i - hL.eigenvalues rfl i| + eta ≤
            eta + eta := add_le_add hnear (le_refl eta)
        _ = 2 * eta := by ring
        _ < gamma := hsmall)
  have hge : 1 ≤ Module.finrank ℝ
      (Module.End.eigenspace (L + H)
        ((hL.add hHsymm).eigenvalues rfl i)) := by
    rw [Submodule.one_le_finrank_iff]
    exact Module.End.hasEigenvalue_iff.mp
      ((hL.add hHsymm).hasEigenvalue_eigenvalues rfl i)
  exact Nat.le_antisymm hle hge

end

end PrimeStar
