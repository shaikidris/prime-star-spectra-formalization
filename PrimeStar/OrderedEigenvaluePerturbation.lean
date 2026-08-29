import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Interval.Finset.Fin

/-!
# Ordered eigenvalues under a symmetric perturbation

This file proves the finite-dimensional ordered Weyl bound needed to retain
the manuscript's prescribed eigenvalue index.  The proof is the standard
dimension-intersection/min--max argument, written directly in the ordered
eigenbases supplied by mathlib.
-/

namespace PrimeStar

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

/-- Span of the ordered eigenvectors with indices at most `i`. -/
def orderedEigenPrefix [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) : Submodule ℝ E :=
  Submodule.span ℝ
    (Set.range fun j : ↥(Finset.Iic i) ↦ hT.eigenvectorBasis rfl j.1)

/-- Span of the ordered eigenvectors with indices at least `i`. -/
def orderedEigenSuffix [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) : Submodule ℝ E :=
  Submodule.span ℝ
    (Set.range fun j : ↥(Finset.Ici i) ↦ hT.eigenvectorBasis rfl j.1)

theorem finrank_orderedEigenPrefix [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) :
    Module.finrank ℝ (orderedEigenPrefix T hT i) = i.1 + 1 := by
  rw [orderedEigenPrefix, finrank_span_eq_card]
  · calc
      Fintype.card ↥(Finset.Iic i) = (Finset.Iic i).card := Fintype.card_coe _
      _ = i.1 + 1 := Fin.card_Iic i
  · exact (hT.eigenvectorBasis rfl).orthonormal.linearIndependent.comp
      (fun j : ↥(Finset.Iic i) ↦ j.1) Subtype.val_injective

theorem finrank_orderedEigenSuffix [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) :
    Module.finrank ℝ (orderedEigenSuffix T hT i) = Module.finrank ℝ E - i.1 := by
  rw [orderedEigenSuffix, finrank_span_eq_card]
  · calc
      Fintype.card ↥(Finset.Ici i) = (Finset.Ici i).card := Fintype.card_coe _
      _ = Module.finrank ℝ E - i.1 := Fin.card_Ici i
  · exact (hT.eigenvectorBasis rfl).orthonormal.linearIndependent.comp
      (fun j : ↥(Finset.Ici i) ↦ j.1) Subtype.val_injective

/-- A prefix of one ordered eigenbasis and the complementary suffix of
another have a nonzero intersection. -/
theorem exists_nonzero_mem_orderedEigenPrefix_inf_orderedEigenSuffix
    [FiniteDimensional ℝ E]
    (A L : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (hL : L.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ x : E, x ≠ 0 ∧
      x ∈ orderedEigenPrefix A hA i ∧ x ∈ orderedEigenSuffix L hL i := by
  let U := orderedEigenPrefix A hA i
  let W := orderedEigenSuffix L hL i
  have hsum : Module.finrank ℝ E < Module.finrank ℝ U + Module.finrank ℝ W := by
    rw [show Module.finrank ℝ U = i.1 + 1 by
      simpa [U] using finrank_orderedEigenPrefix A hA i,
      show Module.finrank ℝ W = Module.finrank ℝ E - i.1 by
        simpa [W] using finrank_orderedEigenSuffix L hL i]
    have hi : i.1 < Module.finrank ℝ E := i.2
    omega
  have hnot : ¬ Disjoint U W := by
    intro hdis
    exact (not_le_of_gt hsum) (Submodule.finrank_add_finrank_le_of_disjoint hdis)
  rw [Submodule.disjoint_def] at hnot
  push Not at hnot
  obtain ⟨x, hxU, hxW, hx0⟩ := hnot
  exact ⟨x, hx0, hxU, hxW⟩

/-- Spectral-coordinate expansion of the quadratic form of a symmetric
operator. -/
theorem real_inner_apply_eq_sum_eigenvalues [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (x : E) :
    ⟪x, T x⟫_ℝ =
      ∑ j, hT.eigenvalues rfl j * (hT.eigenvectorBasis rfl).repr x j ^ 2 := by
  let b := hT.eigenvectorBasis rfl
  calc
    ⟪x, T x⟫_ℝ = ∑ j, ⟪x, b j⟫_ℝ * ⟪b j, T x⟫_ℝ :=
      (b.sum_inner_mul_inner x (T x)).symm
    _ = ∑ j, hT.eigenvalues rfl j * b.repr x j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      have hcoord := hT.eigenvectorBasis_apply_self_apply rfl x j
      change b.repr (T x) j = hT.eigenvalues rfl j * b.repr x j at hcoord
      have hxinner : ⟪x, b j⟫_ℝ = b.repr x j := by
        rw [real_inner_comm]
        exact (b.repr_apply_apply x j).symm
      have hTxinner : ⟪b j, T x⟫_ℝ = b.repr (T x) j :=
        (b.repr_apply_apply (T x) j).symm
      rw [hxinner, hTxinner, hcoord]
      ring

theorem orderedEigenPrefix_repr_eq_zero_of_lt [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (i k : Fin (Module.finrank ℝ E)) (x : E)
    (hx : x ∈ orderedEigenPrefix T hT i) (hik : i < k) :
    (hT.eigenvectorBasis rfl).repr x k = 0 := by
  rw [orderedEigenPrefix, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  simp only [map_sum, map_smul]
  rw [WithLp.ofLp_sum]
  simp only [PiLp.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j _hj
  rw [(hT.eigenvectorBasis rfl).repr_self]
  have hjk : (j.1 : Fin (Module.finrank ℝ E)) ≠ k := by
    intro h
    have : k ≤ i := by simpa [h] using j.2
    exact (not_le_of_gt hik) this
  simp [hjk]

theorem orderedEigenSuffix_repr_eq_zero_of_lt [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (i k : Fin (Module.finrank ℝ E)) (x : E)
    (hx : x ∈ orderedEigenSuffix T hT i) (hki : k < i) :
    (hT.eigenvectorBasis rfl).repr x k = 0 := by
  rw [orderedEigenSuffix, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  simp only [map_sum, map_smul]
  rw [WithLp.ofLp_sum]
  simp only [PiLp.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j _hj
  rw [(hT.eigenvectorBasis rfl).repr_self]
  have hjk : (j.1 : Fin (Module.finrank ℝ E)) ≠ k := by
    intro h
    have : i ≤ k := by simpa [h] using j.2
    exact (not_le_of_gt hki) this
  simp [hjk]

theorem eigenvalue_mul_norm_sq_le_real_inner_apply_of_mem_orderedEigenPrefix
    [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) (x : E)
    (hx : x ∈ orderedEigenPrefix T hT i) :
    hT.eigenvalues rfl i * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ := by
  let b := hT.eigenvectorBasis rfl
  let ev := hT.eigenvalues rfl
  have hmono := hT.eigenvalues_antitone rfl
  have hsum :
      ∑ j, ev i * b.repr x j ^ 2 ≤ ∑ j, ev j * b.repr x j ^ 2 := by
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hji : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hmono hji) (sq_nonneg _)
    · have hij : i < j := lt_of_not_ge hji
      have hz := orderedEigenPrefix_repr_eq_zero_of_lt T hT i j x hx hij
      simp [b, hz]
  rw [real_inner_apply_eq_sum_eigenvalues T hT x]
  calc
    ev i * ‖x‖ ^ 2 = ∑ j, ev i * b.repr x j ^ 2 := by
      rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq, b.repr.norm_map]
    _ ≤ ∑ j, ev j * b.repr x j ^ 2 := hsum

theorem real_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_orderedEigenSuffix
    [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) (x : E)
    (hx : x ∈ orderedEigenSuffix T hT i) :
    ⟪x, T x⟫_ℝ ≤ hT.eigenvalues rfl i * ‖x‖ ^ 2 := by
  let b := hT.eigenvectorBasis rfl
  let ev := hT.eigenvalues rfl
  have hmono := hT.eigenvalues_antitone rfl
  have hsum :
      ∑ j, ev j * b.repr x j ^ 2 ≤ ∑ j, ev i * b.repr x j ^ 2 := by
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hij : i ≤ j
    · exact mul_le_mul_of_nonneg_right (hmono hij) (sq_nonneg _)
    · have hji : j < i := lt_of_not_ge hij
      have hz := orderedEigenSuffix_repr_eq_zero_of_lt T hT i j x hx hji
      simp [b, hz]
  rw [real_inner_apply_eq_sum_eigenvalues T hT x]
  calc
    ∑ j, ev j * b.repr x j ^ 2 ≤ ∑ j, ev i * b.repr x j ^ 2 := hsum
    _ = ev i * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq, b.repr.norm_map]

theorem abs_real_inner_apply_le_of_opNormBound
    (H : E →ₗ[ℝ] E) (eta : ℝ)
    (hH : ∀ x : E, ‖H x‖ ≤ eta * ‖x‖) (x : E) :
    |⟪x, H x⟫_ℝ| ≤ eta * ‖x‖ ^ 2 := by
  calc
    |⟪x, H x⟫_ℝ| ≤ ‖x‖ * ‖H x‖ := abs_real_inner_le_norm x (H x)
    _ ≤ ‖x‖ * (eta * ‖x‖) :=
      mul_le_mul_of_nonneg_left (hH x) (norm_nonneg x)
    _ = eta * ‖x‖ ^ 2 := by ring

/-- Ordered Weyl comparison for a real symmetric perturbation. -/
theorem abs_orderedEigenvalue_add_sub_le
    [FiniteDimensional ℝ E]
    (L H : E →ₗ[ℝ] E) (hL : L.IsSymmetric) (hHsymm : H.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) (eta : ℝ)
    (hH : ∀ x : E, ‖H x‖ ≤ eta * ‖x‖) :
    |(hL.add hHsymm).eigenvalues rfl i - hL.eigenvalues rfl i| ≤ eta := by
  let A := L + H
  let hA : A.IsSymmetric := hL.add hHsymm
  have hupper : hA.eigenvalues rfl i ≤ hL.eigenvalues rfl i + eta := by
    obtain ⟨x, hx0, hxA, hxL⟩ :=
      exists_nonzero_mem_orderedEigenPrefix_inf_orderedEigenSuffix A L hA hL i
    have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
    have hAlo :=
      eigenvalue_mul_norm_sq_le_real_inner_apply_of_mem_orderedEigenPrefix
        A hA i x hxA
    have hLhi :=
      real_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_orderedEigenSuffix
        L hL i x hxL
    have hHabs := abs_real_inner_apply_le_of_opNormBound H eta hH x
    have hHhi : ⟪x, H x⟫_ℝ ≤ eta * ‖x‖ ^ 2 :=
      (le_abs_self _).trans hHabs
    have hsplit : ⟪x, A x⟫_ℝ = ⟪x, L x⟫_ℝ + ⟪x, H x⟫_ℝ := by
      simp [A, inner_add_right]
    rw [hsplit] at hAlo
    have hmul : hA.eigenvalues rfl i * ‖x‖ ^ 2 ≤
        (hL.eigenvalues rfl i + eta) * ‖x‖ ^ 2 := by
      calc
        hA.eigenvalues rfl i * ‖x‖ ^ 2 ≤
            ⟪x, L x⟫_ℝ + ⟪x, H x⟫_ℝ := hAlo
        _ ≤ hL.eigenvalues rfl i * ‖x‖ ^ 2 + eta * ‖x‖ ^ 2 :=
          add_le_add hLhi hHhi
        _ = (hL.eigenvalues rfl i + eta) * ‖x‖ ^ 2 := by ring
    nlinarith
  have hlower : hL.eigenvalues rfl i - eta ≤ hA.eigenvalues rfl i := by
    obtain ⟨x, hx0, hxL, hxA⟩ :=
      exists_nonzero_mem_orderedEigenPrefix_inf_orderedEigenSuffix L A hL hA i
    have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
    have hLlo :=
      eigenvalue_mul_norm_sq_le_real_inner_apply_of_mem_orderedEigenPrefix
        L hL i x hxL
    have hAhi :=
      real_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_orderedEigenSuffix
        A hA i x hxA
    have hHabs := abs_real_inner_apply_le_of_opNormBound H eta hH x
    have hHlo : -(eta * ‖x‖ ^ 2) ≤ ⟪x, H x⟫_ℝ :=
      (neg_le_neg hHabs).trans (neg_abs_le _)
    have hsplit : ⟪x, A x⟫_ℝ = ⟪x, L x⟫_ℝ + ⟪x, H x⟫_ℝ := by
      simp [A, inner_add_right]
    rw [hsplit] at hAhi
    have hmul : (hL.eigenvalues rfl i - eta) * ‖x‖ ^ 2 ≤
        hA.eigenvalues rfl i * ‖x‖ ^ 2 := by
      calc
        (hL.eigenvalues rfl i - eta) * ‖x‖ ^ 2 =
            hL.eigenvalues rfl i * ‖x‖ ^ 2 - eta * ‖x‖ ^ 2 := by ring
        _ ≤ ⟪x, L x⟫_ℝ + ⟪x, H x⟫_ℝ := by linarith
        _ ≤ hA.eigenvalues rfl i * ‖x‖ ^ 2 := hAhi
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- The numerical value of an index in a decreasing finite list is the number
of strictly larger entries, provided the selected value occurs only once.
This isolates the purely ordered-list part of arithmetic eigenvalue
indexing. -/
theorem orderedIndex_val_eq_card_filter_gt
    {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (i : Fin n)
    (hi : ∀ j, f j = f i → j = i) :
    i.1 = (Finset.univ.filter fun j ↦ f i < f j).card := by
  have hset : (Finset.univ.filter fun j ↦ f i < f j) = Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iio]
    constructor
    · intro hgt
      by_contra hnot
      have hij : i ≤ j := le_of_not_gt hnot
      exact (not_lt_of_ge (hf hij)) hgt
    · intro hji
      have hle : f i ≤ f j := hf hji.le
      exact lt_of_le_of_ne hle (fun heq ↦ hji.ne (hi j heq.symm))
  rw [hset]
  simp

end

end PrimeStar
