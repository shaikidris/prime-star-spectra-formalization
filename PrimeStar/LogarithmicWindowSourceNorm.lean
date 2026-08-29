import PrimeStar.LogarithmicWindowDegreeGap
import PrimeStar.CanonicalFirstExitBlocks

set_option maxHeartbeats 1000000

/-!
# Source-weighted local resolvent norms

These exact identities are the local input for the uniform estimate
`\|R_U b\|^2 \ll a / sqrt X`.  They retain the direction of the first-exit
source and therefore avoid the losses from a global resolvent norm.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

/-- Exact norm square of one full up-star resolvent block. -/
theorem norm_actualUpStarResolvent_sq
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X} {mu c0 : ℝ}
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    ‖actualUpStarResolvent S X Y target mu c0‖ ^ 2 =
      (mu ^ 4 + 6 * mu ^ 2 * (largePrimeStarDegree S X Y target : ℝ) +
          (largePrimeStarDegree S X Y target : ℝ) ^ 2) /
        (2 * mu ^ 2 *
          (mu ^ 2 - (largePrimeStarDegree S X Y target : ℝ)) ^ 2) := by
  let d : ℝ := largePrimeStarDegree S X Y target
  rw [← real_inner_self_eq_norm_sq, actualUpStarResolvent,
    largePrimeStarDataVector_inner]
  have hsum :
      (∑ _v ∈ largePrimeLeaves S X Y target,
        (2 * c0 / (mu ^ 2 - d)) * (2 * c0 / (mu ^ 2 - d))) =
        d * ((2 * c0 / (mu ^ 2 - d)) * (2 * c0 / (mu ^ 2 - d))) := by
    simp [d, largePrimeStarDegree]
  rw [hsum]
  dsimp only [d]
  have hden0 : mu ^ 2 - (largePrimeStarDegree S X Y target : ℝ) ≠ 0 :=
    sub_ne_zero.mpr hden
  field_simp [hmu, hden0]
  rw [hc0]
  ring

/-- Ratio form of the up-star norm identity. -/
theorem norm_actualUpStarResolvent_sq_ratio
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X} {mu c0 : ℝ}
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    ‖actualUpStarResolvent S X Y target mu c0‖ ^ 2 =
      (1 + 6 * ((largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) +
          ((largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) ^ 2) /
        (2 * mu ^ 2 *
          (1 - (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) ^ 2) := by
  rw [norm_actualUpStarResolvent_sq hmu hden hc0]
  have hmu2 : mu ^ 2 ≠ 0 := pow_ne_zero 2 hmu
  have hden0 : mu ^ 2 - (largePrimeStarDegree S X Y target : ℝ) ≠ 0 :=
    sub_ne_zero.mpr hden
  field_simp [hmu2, hden0]

/-- Exact ratio-form norm square of one partial-leaf down-star resolvent
block.  The selected leaf count is the boundary degree `mu^2`. -/
theorem norm_actualDownStarResolvent_sq_ratio
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X}
    {P : Finset (Vertex S X)} {mu c0 : ℝ}
    (hP : P ⊆ largePrimeLeaves S X Y target)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    ‖actualDownStarResolvent S X Y target P mu c0‖ ^ 2 =
      (((largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) ^ 2 -
          2 * ((largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) + 9) /
        (2 * mu ^ 2 *
          (1 - (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) ^ 2) := by
  let d : ℝ := largePrimeStarDegree S X Y target
  rw [← real_inner_self_eq_norm_sq, actualDownStarResolvent,
    largePrimeStarDataVector_inner]
  have hsum :
      (∑ v ∈ largePrimeLeaves S X Y target,
        (2 * c0 / (mu ^ 2 - d) + if v ∈ P then c0 / mu ^ 2 else 0) *
          (2 * c0 / (mu ^ 2 - d) + if v ∈ P then c0 / mu ^ 2 else 0)) =
        d * (2 * c0 / (mu ^ 2 - d)) ^ 2 +
          P.card * (2 * (2 * c0 / (mu ^ 2 - d)) * (c0 / mu ^ 2) +
            (c0 / mu ^ 2) ^ 2) := by
    have hPfilter :
        (largePrimeLeaves S X Y target).filter (fun v ↦ v ∈ P) = P := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · exact fun h ↦ h.2
      · intro hv
        exact ⟨hP hv, hv⟩
    calc
      _ = ∑ v ∈ largePrimeLeaves S X Y target,
          ((2 * c0 / (mu ^ 2 - d)) ^ 2 +
            if v ∈ P then
              2 * (2 * c0 / (mu ^ 2 - d)) * (c0 / mu ^ 2) +
                (c0 / mu ^ 2) ^ 2 else 0) := by
            apply Finset.sum_congr rfl
            intro v _
            by_cases hv : v ∈ P <;> simp [hv] <;> ring
      _ = d * (2 * c0 / (mu ^ 2 - d)) ^ 2 +
          P.card * (2 * (2 * c0 / (mu ^ 2 - d)) * (c0 / mu ^ 2) +
            (c0 / mu ^ 2) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_ite, hPfilter]
            simp [d, largePrimeStarDegree]
            ring
  rw [hsum, hcard]
  dsimp only [d]
  have hmu2 : mu ^ 2 ≠ 0 := pow_ne_zero 2 hmu
  have hden0 : mu ^ 2 - (largePrimeStarDegree S X Y target : ℝ) ≠ 0 :=
    sub_ne_zero.mpr hden
  field_simp [hmu, hmu2, hden0]
  rw [hc0]
  ring

/-- A down-star whose degree ratio is at least two has a uniformly bounded
source-resolvent norm. -/
theorem norm_actualDownStarResolvent_sq_le
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X}
    {P : Finset (Vertex S X)} {mu c0 : ℝ}
    (hP : P ⊆ largePrimeLeaves S X Y target)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2)
    (hratio : 2 ≤ (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) :
    ‖actualDownStarResolvent S X Y target P mu c0‖ ^ 2 ≤
      9 / (2 * mu ^ 2) := by
  rw [norm_actualDownStarResolvent_sq_ratio hP hcard hmu hden hc0]
  let s : ℝ := (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2
  have hmuSq : 0 < mu ^ 2 := sq_pos_of_ne_zero hmu
  have hdenSq : 0 < (1 - s) ^ 2 := sq_pos_of_ne_zero (by
    intro hs
    apply hden
    have hmuSq0 : mu ^ 2 ≠ 0 := hmuSq.ne'
    have hs1 : s = 1 := by linarith
    dsimp [s] at hs1
    exact ((div_eq_one_iff_eq hmuSq0).mp hs1).symm)
  have hpoly : s ^ 2 - 2 * s + 9 ≤ 9 * (1 - s) ^ 2 := by
    dsimp [s] at hratio ⊢
    nlinarith [sq_nonneg (s - 2)]
  dsimp [s] at hdenSq hpoly ⊢
  exact (div_le_div_iff₀ (mul_pos (by positivity) hdenSq)
    (mul_pos (by positivity) hmuSq)).2 (by nlinarith)

/-- A canonical up-star whose degree ratio stays below `199/200` has a
uniform local source-resolvent bound.  The deliberately round constant keeps
the later direct-sum estimate elementary. -/
theorem norm_actualUpStarResolvent_sq_le_of_ratio
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X} {mu c0 : ℝ}
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2)
    (hratio0 : 0 ≤ (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2)
    (hratio : (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2 ≤ 199 / 200) :
    ‖actualUpStarResolvent S X Y target mu c0‖ ^ 2 ≤
      200000 / mu ^ 2 := by
  rw [norm_actualUpStarResolvent_sq_ratio hmu hden hc0]
  let r : ℝ := (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2
  have hmuSq : 0 < mu ^ 2 := sq_pos_of_ne_zero hmu
  have hgap : 1 / 200 ≤ 1 - r := by dsimp [r] at hratio ⊢; linarith
  have hgapSq : (1 / 200 : ℝ) ^ 2 ≤ (1 - r) ^ 2 := by nlinarith
  have hpoly : 1 + 6 * r + r ^ 2 ≤ 8 := by
    dsimp [r] at hratio0 hratio ⊢
    nlinarith [sq_nonneg (r - 1)]
  have hdenPos : 0 < 2 * mu ^ 2 * (1 - r) ^ 2 := by
    have : 0 < (1 - r) ^ 2 := lt_of_lt_of_le (by norm_num) hgapSq
    positivity
  have hrightPos : 0 < mu ^ 2 := hmuSq
  dsimp [r] at hpoly hdenPos hgapSq ⊢
  apply (div_le_div_iff₀ hdenPos hrightPos).2
  nlinarith

/-- A canonical down-star whose degree ratio stays above `201/200` has a
uniform local source-resolvent bound. -/
theorem norm_actualDownStarResolvent_sq_le_of_ratio
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X}
    {P : Finset (Vertex S X)} {mu c0 : ℝ}
    (hP : P ⊆ largePrimeLeaves S X Y target)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2)
    (hratio : 201 / 200 ≤
      (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) :
    ‖actualDownStarResolvent S X Y target P mu c0‖ ^ 2 ≤
      200000 / mu ^ 2 := by
  rw [norm_actualDownStarResolvent_sq_ratio hP hcard hmu hden hc0]
  let s : ℝ := (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2
  have hmuSq : 0 < mu ^ 2 := sq_pos_of_ne_zero hmu
  have hgap : 1 / 200 ≤ s - 1 := by dsimp [s] at hratio ⊢; linarith
  have hgapSq : (1 / 200 : ℝ) ^ 2 ≤ (1 - s) ^ 2 := by nlinarith
  have hrewrite : s ^ 2 - 2 * s + 9 = (1 - s) ^ 2 + 8 := by ring
  have hdenPos : 0 < 2 * mu ^ 2 * (1 - s) ^ 2 := by
    have : 0 < (1 - s) ^ 2 := lt_of_lt_of_le (by norm_num) hgapSq
    positivity
  dsimp [s] at hdenPos hgapSq hrewrite ⊢
  apply (div_le_div_iff₀ hdenPos hmuSq).2
  rw [hrewrite]
  nlinarith

/-- Canonical local resolvents belonging to distinct first-exit labels are
orthogonal.  This is the Pythagorean input which prevents a loss by the
number of prime labels. -/
theorem inner_canonicalExitResolvent_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu c0 : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    {i j : CanonicalExitIndex S X Y c} (hij : i ≠ j) :
    ⟪canonicalExitResolvent hS c mu c0 i,
      canonicalExitResolvent hS c mu c0 j⟫_ℝ = 0 := by
  have hdisj := disjoint_canonicalExitTarget_starSupport hS hcut hc hij
  rcases i with q | q <;> rcases j with r | r
  · simpa [canonicalExitResolvent, actualUpStarResolvent] using
      (inner_largePrimeStarDataVector_eq_zero_of_disjoint
        (c := canonicalUpTarget hS c q) (k := canonicalUpTarget hS c r)
        _ _ _ _ hdisj)
  · simpa [canonicalExitResolvent, actualUpStarResolvent,
      actualDownStarResolvent] using
      (inner_largePrimeStarDataVector_eq_zero_of_disjoint
        (c := canonicalUpTarget hS c q) (k := canonicalDownTarget c r)
        _ _ _ _ hdisj)
  · simpa [canonicalExitResolvent, actualUpStarResolvent,
      actualDownStarResolvent] using
      (inner_largePrimeStarDataVector_eq_zero_of_disjoint
        (c := canonicalDownTarget c q) (k := canonicalUpTarget hS c r)
        _ _ _ _ hdisj)
  · simpa [canonicalExitResolvent, actualDownStarResolvent] using
      (inner_largePrimeStarDataVector_eq_zero_of_disjoint
        (c := canonicalDownTarget c q) (k := canonicalDownTarget c r)
        _ _ _ _ hdisj)

/-- Exact Pythagorean identity for the canonical direct sum of local
resolvents. -/
theorem norm_sum_canonicalExitResolvent_sq
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu c0 : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y) :
    ‖∑ i : CanonicalExitIndex S X Y c,
        canonicalExitResolvent hS c mu c0 i‖ ^ 2 =
      ∑ i : CanonicalExitIndex S X Y c,
        ‖canonicalExitResolvent hS c mu c0 i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, inner_sum]
  calc
    (∑ j : CanonicalExitIndex S X Y c,
        ⟪∑ i : CanonicalExitIndex S X Y c,
          canonicalExitResolvent hS c mu c0 i,
          canonicalExitResolvent hS c mu c0 j⟫_ℝ) =
        ∑ j : CanonicalExitIndex S X Y c,
          ‖canonicalExitResolvent hS c mu c0 j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [sum_inner]
      rw [Finset.sum_eq_single j]
      · exact real_inner_self_eq_norm_sq _
      · intro i _hi hij
        exact inner_canonicalExitResolvent_eq_zero hS hcut hc hij
      · simp
    _ = _ := rfl

end

end PrimeStar
