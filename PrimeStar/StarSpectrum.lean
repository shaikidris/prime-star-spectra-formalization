import PrimeStar.StarComponents
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Exact spectrum carried by a large-prime star

For a lower centre `c`, let `d` be the number of its large-prime leaves.  The
signed vector with centre coordinate `√d`, leaf coordinates `ε`, and zero
elsewhere is an adjacency eigenvector with eigenvalue `ε√d` whenever
`ε² = 1`.  The specializations `ε = 1` and `ε = -1` give the two nonzero
eigenvalues of the star block.
-/

namespace PrimeStar

noncomputable section

/-- Local decidability for large-prime adjacency in spectral calculations. -/
local instance largePrimeSpectrumDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The number of leaves attached to a large-prime centre. -/
def largePrimeStarDegree (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) : ℕ :=
  (largePrimeLeaves S X Y c).card

@[simp]
theorem largePrimeStarDegree_eq_degree {S : Finset ℕ} {X Y : ℕ}
    {c : Vertex S X} :
    largePrimeStarDegree S X Y c = (largePrimeGraph S X Y).degree c :=
  rfl

/-- Degree zero is exactly the isolated-centre case. -/
theorem largePrimeStarDegree_eq_zero_iff {S : Finset ℕ} {X Y : ℕ}
    {c : Vertex S X} :
    largePrimeStarDegree S X Y c = 0 ↔
      (largePrimeGraph S X Y).IsIsolated c := by
  rw [largePrimeStarDegree_eq_degree, SimpleGraph.degree_eq_zero]

/-- The unnormalized signed mode on one closed large-prime star. -/
def largePrimeSignedStarVector (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (ε : ℝ) : Vertex S X → ℝ :=
  fun v ↦
    if v = c then √(largePrimeStarDegree S X Y c : ℝ)
    else if v ∈ largePrimeLeaves S X Y c then ε else 0

@[simp]
theorem largePrimeSignedStarVector_center {S : Finset ℕ} {X Y : ℕ}
    (c : Vertex S X) (ε : ℝ) :
    largePrimeSignedStarVector S X Y c ε c =
      √(largePrimeStarDegree S X Y c : ℝ) := by
  simp [largePrimeSignedStarVector]

theorem largePrimeSignedStarVector_leaf {S : Finset ℕ} {X Y : ℕ}
    {c v : Vertex S X} {ε : ℝ} (hv : v ∈ largePrimeLeaves S X Y c) :
    largePrimeSignedStarVector S X Y c ε v = ε := by
  have hvc : v ≠ c := by
    intro h
    subst v
    exact (largePrimeGraph S X Y).notMem_neighborFinset_self c hv
  simp [largePrimeSignedStarVector, hvc, hv]

theorem largePrimeSignedStarVector_eq_zero_of_not_mem {S : Finset ℕ} {X Y : ℕ}
    {c v : Vertex S X} {ε : ℝ}
    (hv : v ∉ largePrimeStarSupport S X Y c) :
    largePrimeSignedStarVector S X Y c ε v = 0 := by
  have hvc : v ≠ c := by
    intro h
    apply hv
    simp [largePrimeStarSupport, h]
  have hvleaf : v ∉ largePrimeLeaves S X Y c := by
    intro h
    apply hv
    simp [largePrimeStarSupport, h]
  simp [largePrimeSignedStarVector, hvc, hvleaf]

/-- The signed star vector is an exact adjacency eigenvector equation.  This
statement includes the zero vector when the star is empty; the subsequent
`HasEigenvector` theorem imposes positive degree. -/
theorem largePrime_adjMatrix_mulVec_signedStarVector {S : Finset ℕ} {X Y : ℕ}
    {c : Vertex S X} {ε : ℝ} (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hε : ε ^ 2 = 1) :
    Matrix.mulVec ((largePrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeSignedStarVector S X Y c ε) =
      (ε * √(largePrimeStarDegree S X Y c : ℝ)) •
        largePrimeSignedStarVector S X Y c ε := by
  funext v
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  by_cases hvc : v = c
  · subst v
    change (∑ u ∈ largePrimeLeaves S X Y c,
      largePrimeSignedStarVector S X Y c ε u) = _
    have hsum :
        (∑ u ∈ largePrimeLeaves S X Y c,
            largePrimeSignedStarVector S X Y c ε u) =
          (largePrimeStarDegree S X Y c : ℝ) * ε := by
      calc
        _ = ∑ _u ∈ largePrimeLeaves S X Y c, ε := by
          apply Finset.sum_congr rfl
          intro u hu
          exact largePrimeSignedStarVector_leaf hu
        _ = (largePrimeStarDegree S X Y c : ℝ) * ε := by
          simp [largePrimeStarDegree]
    rw [hsum]
    simp only [largePrimeSignedStarVector_center, Pi.smul_apply, smul_eq_mul]
    calc
      (largePrimeStarDegree S X Y c : ℝ) * ε =
          ε * (largePrimeStarDegree S X Y c : ℝ) := by ring
      _ = ε * (√(largePrimeStarDegree S X Y c : ℝ)) ^ 2 := by
        rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      _ = ε * (√(largePrimeStarDegree S X Y c : ℝ) *
          √(largePrimeStarDegree S X Y c : ℝ)) := by ring
      _ = ε * √(largePrimeStarDegree S X Y c : ℝ) *
          √(largePrimeStarDegree S X Y c : ℝ) := by ring
  · by_cases hvleaf : v ∈ largePrimeLeaves S X Y c
    · rw [largePrime_neighborFinset_leaf hcut hc hvleaf]
      simp only [Finset.sum_singleton, largePrimeSignedStarVector_center,
        largePrimeSignedStarVector_leaf hvleaf, Pi.smul_apply, smul_eq_mul]
      calc
        √(largePrimeStarDegree S X Y c : ℝ) =
            1 * √(largePrimeStarDegree S X Y c : ℝ) := by ring
        _ = ε ^ 2 * √(largePrimeStarDegree S X Y c : ℝ) := by rw [hε]
        _ = ε * √(largePrimeStarDegree S X Y c : ℝ) * ε := by ring
    · have hvout : v ∉ largePrimeStarSupport S X Y c := by
        simp [largePrimeStarSupport, hvc, hvleaf]
      have hzero :
          ∀ u ∈ (largePrimeGraph S X Y).neighborFinset v,
            largePrimeSignedStarVector S X Y c ε u = 0 := by
        intro u hu
        apply largePrimeSignedStarVector_eq_zero_of_not_mem
        intro husupp
        have huv : LargePrimeAdj S Y u v := by
          exact largePrimeAdj_symm (by simpa using hu)
        exact hvout (largePrimeStarSupport_closed hcut hc husupp huv)
      rw [Finset.sum_eq_zero hzero]
      simp [largePrimeSignedStarVector_eq_zero_of_not_mem hvout]

/-- A nonempty star has a nonzero signed star vector. -/
theorem largePrimeSignedStarVector_ne_zero {S : Finset ℕ} {X Y : ℕ}
    {c : Vertex S X} {ε : ℝ} (hd : 0 < largePrimeStarDegree S X Y c) :
    largePrimeSignedStarVector S X Y c ε ≠ 0 := by
  intro hzero
  have hc0 := congrFun hzero c
  simp only [largePrimeSignedStarVector_center, Pi.zero_apply] at hc0
  have hsqrt : 0 < √(largePrimeStarDegree S X Y c : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hd)
  exact hsqrt.ne' hc0

/-- The exact signed star equation as a formal linear-map eigenvector. -/
theorem largePrime_hasEigenvector_signedStar {S : Finset ℕ} {X Y : ℕ}
    {c : Vertex S X} {ε : ℝ} (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hε : ε ^ 2 = 1) (hd : 0 < largePrimeStarDegree S X Y c) :
    Module.End.HasEigenvector
      (((largePrimeGraph S X Y).adjMatrix ℝ).mulVecLin :
        Module.End ℝ (Vertex S X → ℝ))
      (ε * √(largePrimeStarDegree S X Y c : ℝ))
      (largePrimeSignedStarVector S X Y c ε) := by
  rw [Module.End.hasEigenvector_iff]
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    simpa [Matrix.mulVecLin_apply] using
      largePrime_adjMatrix_mulVec_signedStarVector hcut hc hε
  · exact largePrimeSignedStarVector_ne_zero hd

/-- The positive star mode has eigenvalue `√d`. -/
theorem largePrime_hasEigenvector_star_pos {S : Finset ℕ} {X Y : ℕ}
    {c : Vertex S X} (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c) :
    Module.End.HasEigenvector
      (((largePrimeGraph S X Y).adjMatrix ℝ).mulVecLin :
        Module.End ℝ (Vertex S X → ℝ))
      (√(largePrimeStarDegree S X Y c : ℝ))
      (largePrimeSignedStarVector S X Y c 1) := by
  simpa using
    largePrime_hasEigenvector_signedStar hcut hc (ε := (1 : ℝ)) (by norm_num) hd

/-- The negative star mode has eigenvalue `-√d`. -/
theorem largePrime_hasEigenvector_star_neg {S : Finset ℕ} {X Y : ℕ}
    {c : Vertex S X} (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c) :
    Module.End.HasEigenvector
      (((largePrimeGraph S X Y).adjMatrix ℝ).mulVecLin :
        Module.End ℝ (Vertex S X → ℝ))
      (-√(largePrimeStarDegree S X Y c : ℝ))
      (largePrimeSignedStarVector S X Y c (-1)) := by
  simpa using
    largePrime_hasEigenvector_signedStar hcut hc (ε := (-1 : ℝ)) (by norm_num) hd

end

end PrimeStar
