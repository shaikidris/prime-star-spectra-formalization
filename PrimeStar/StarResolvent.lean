import PrimeStar.SchurRemainder

/-!
# Exact local star resolvents

The centre/symmetric-leaf reduction of a star is two-dimensional.  This file
formalizes the two inverse actions and quadratic forms appearing in Lemma 8.2,
then sums them into the finite correction used before asymptotic evaluation.
-/

namespace PrimeStar

noncomputable section

/-- The shifted two-level star operator `μI-L` in centre/symmetric-leaf
coordinates, with star ratio `t²`. -/
def twoLevelStarShift (μ t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (μ * (x.1 - t * x.2), μ * (x.2 - t * x.1))

/-- First-exit coordinates for a full up-star.  The scalar `c` is the centre
normalization and satisfies `c²=1/2` in the paper. -/
def upStarFirstExit (c t : ℝ) : ℝ × ℝ :=
  (c, c * t)

/-- Explicit inverse image of `upStarFirstExit` under `twoLevelStarShift`. -/
def upStarResolventVector (μ c t : ℝ) : ℝ × ℝ :=
  (c * (1 + t ^ 2) / (μ * (1 - t ^ 2)),
    c * (2 * t) / (μ * (1 - t ^ 2)))

theorem twoLevelStarShift_upStarResolventVector
    (μ c t : ℝ) (hμ : μ ≠ 0) (ht : t ^ 2 ≠ 1) :
    twoLevelStarShift μ t (upStarResolventVector μ c t) =
      upStarFirstExit c t := by
  apply Prod.ext <;> simp only [twoLevelStarShift, upStarResolventVector,
    upStarFirstExit]
  all_goals (field_simp [hμ, sub_ne_zero.mpr ht]; ring)

/-- Exact up-star quadratic form.  Writing `r=t²` gives
`(1+3r)/(1-r)`. -/
theorem upStar_quadraticForm
    (μ c t : ℝ) (hμ : μ ≠ 0) (ht : t ^ 2 ≠ 1)
    (hc : c ^ 2 = 1 / 2) :
    2 * μ *
        (upStarFirstExit c t).1 * (upStarResolventVector μ c t).1 +
      2 * μ *
        (upStarFirstExit c t).2 * (upStarResolventVector μ c t).2 =
      (1 + 3 * t ^ 2) / (1 - t ^ 2) := by
  simp only [upStarFirstExit, upStarResolventVector]
  field_simp [hμ, sub_ne_zero.mpr ht]
  nlinarith

/-- First-exit coordinates of the centre and symmetric-leaf component of a
down-star. -/
def downStarFirstExit (c t : ℝ) : ℝ × ℝ :=
  (c, c / t)

/-- Explicit inverse image of the two-level part of `downStarFirstExit`. -/
def downStarResolventVector (μ c t : ℝ) : ℝ × ℝ :=
  (2 * c / (μ * (1 - t ^ 2)),
    c * (t ^ 2 + 1) / (t * μ * (1 - t ^ 2)))

theorem twoLevelStarShift_downStarResolventVector
    (μ c t : ℝ) (hμ : μ ≠ 0) (ht0 : t ≠ 0) (ht : t ^ 2 ≠ 1) :
    twoLevelStarShift μ t (downStarResolventVector μ c t) =
      downStarFirstExit c t := by
  apply Prod.ext <;> simp only [twoLevelStarShift, downStarResolventVector,
    downStarFirstExit]
  all_goals (field_simp [hμ, ht0, sub_ne_zero.mpr ht]; ring)

/-- Exact down-star quadratic form, including an orthogonal kernel component
of amplitude `k`.  Writing `s=t²` gives `(5-s)/(1-s)`. -/
theorem downStar_quadraticForm
    (μ c t k : ℝ) (hμ : μ ≠ 0) (ht0 : t ≠ 0) (ht : t ^ 2 ≠ 1)
    (hc : c ^ 2 = 1 / 2)
    (hk : k ^ 2 = (t ^ 2 - 1) / (2 * t ^ 2)) :
    2 * μ *
      ((downStarFirstExit c t).1 * (downStarResolventVector μ c t).1 +
       (downStarFirstExit c t).2 * (downStarResolventVector μ c t).2 +
       k * (k / μ)) =
      (5 - t ^ 2) / (1 - t ^ 2) := by
  simp only [downStarFirstExit, downStarResolventVector]
  field_simp [hμ, ht0, sub_ne_zero.mpr ht] at hk ⊢
  nlinarith

/-- The local correction left after removing the leading `1` from an
up-star block. -/
def upStarCorrection (r : ℝ) : ℝ :=
  4 * r / (1 - r)

/-- The complete local down-star correction. -/
def downStarCorrection (s : ℝ) : ℝ :=
  (5 - s) / (1 - s)

/-- The explicit finite direct-sum correction in Theorem 8.7. -/
def finiteStarCorrection {ι κ : Type*} (U : Finset ι) (D : Finset κ)
    (r : ι → ℝ) (s : κ → ℝ) : ℝ :=
  ∑ q ∈ U, upStarCorrection (r q) +
    ∑ q ∈ D, downStarCorrection (s q)

/-- Summing the evaluated local resolvent blocks cancels one leading unit for
each up-star. -/
theorem finiteStarCorrection_eq
    {ι κ : Type*}
    (U : Finset ι) (D : Finset κ) (r : ι → ℝ) (s : κ → ℝ)
    (upValue : ι → ℝ) (downValue : κ → ℝ)
    (hup : ∀ q ∈ U, upValue q = 1 + upStarCorrection (r q))
    (hdown : ∀ q ∈ D, downValue q = downStarCorrection (s q)) :
    (∑ q ∈ U, upValue q) + (∑ q ∈ D, downValue q) - U.card =
      finiteStarCorrection U D r s := by
  rw [finiteStarCorrection]
  have hu : (∑ q ∈ U, upValue q) =
      (U.card : ℝ) + ∑ q ∈ U, upStarCorrection (r q) := by
    calc
      (∑ q ∈ U, upValue q) =
          ∑ q ∈ U, (1 + upStarCorrection (r q)) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hup q hq
      _ = (U.card : ℝ) + ∑ q ∈ U, upStarCorrection (r q) := by simp [Finset.sum_add_distrib]
  have hd : (∑ q ∈ D, downValue q) =
      ∑ q ∈ D, downStarCorrection (s q) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact hdown q hq
  rw [hu, hd]
  ring

end

end PrimeStar
