import PrimeStar.ActualStarResolvent
import PrimeStar.StarResolvent

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

/-- Local decidability for degree normalization in the actual graph blocks. -/
local instance actualFiniteCorrectionLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Exact finite direct-sum assembly of the local up/down quadratic forms.
Pairwise disjoint closed star supports kill every off-diagonal inner-product
term; this is the algebraic content of the manuscript's `hstar` certificate. -/
theorem inner_actualFiniteBlockSums_eq
    {S : Finset ℕ} {X Y : ℕ} {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (U : Finset ι) (D : Finset κ)
    (upTarget : ι → Vertex S X) (downTarget : κ → Vertex S X)
    (downLeaves : κ → Finset (Vertex S X))
    (mu c0 : ℝ)
    (hUU : ∀ q ∈ U, ∀ r ∈ U, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (upTarget r)))
    (hUD : ∀ q ∈ U, ∀ r ∈ D,
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (downTarget r)))
    (hDD : ∀ q ∈ D, ∀ r ∈ D, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (downTarget q))
        (largePrimeStarSupport S X Y (downTarget r))) :
    ⟪(∑ q ∈ U, actualUpStarFirstExit S X Y (upTarget q) mu c0) +
        (∑ q ∈ D,
          actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0),
      (∑ q ∈ U, actualUpStarResolvent S X Y (upTarget q) mu c0) +
        (∑ q ∈ D,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0)⟫_ℝ =
      (∑ q ∈ U,
        ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
          actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
      (∑ q ∈ D,
        ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ) := by
  have hUpUp :
      ⟪∑ q ∈ U, actualUpStarFirstExit S X Y (upTarget q) mu c0,
        ∑ q ∈ U, actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ =
        ∑ q ∈ U,
          ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
            actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_eq_single q]
    · intro r hr hrq
      exact inner_actualUpFirstExit_actualUpResolvent_eq_zero
        (hUU q hq r hr (Ne.symm hrq)).symm
    · intro hqU
      exact False.elim (hqU hq)
  have hUpDown :
      ⟪∑ q ∈ U, actualUpStarFirstExit S X Y (upTarget q) mu c0,
        ∑ r ∈ D,
          actualDownStarResolvent S X Y (downTarget r) (downLeaves r) mu c0⟫_ℝ =
        0 := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro q hq
    exact inner_actualUpFirstExit_actualDownResolvent_eq_zero
      (hUD q hq r hr)
  have hDownUp :
      ⟪∑ q ∈ D,
          actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
        ∑ r ∈ U, actualUpStarResolvent S X Y (upTarget r) mu c0⟫_ℝ =
        0 := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro q hq
    exact inner_actualDownFirstExit_actualUpResolvent_eq_zero
      (hUD r hr q hq).symm
  have hDownDown :
      ⟪∑ q ∈ D,
          actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
        ∑ q ∈ D,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ =
        ∑ q ∈ D,
          ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
            actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_eq_single q]
    · intro r hr hrq
      exact inner_actualDownFirstExit_actualDownResolvent_eq_zero
        (hDD q hq r hr (Ne.symm hrq)).symm
    · intro hqD
      exact False.elim (hqD hq)
  rw [inner_add_left, inner_add_right, inner_add_right,
    hUpUp, hUpDown, hDownUp, hDownDown, add_zero, zero_add]

theorem actualFiniteStarCorrection_eq
    {S : Finset ℕ} {X Y : ℕ} {ι κ : Type*}
    (U : Finset ι) (D : Finset κ)
    (upTarget : ι → Vertex S X) (downTarget : κ → Vertex S X)
    (downLeaves : κ → Finset (Vertex S X))
    (mu c0 : ℝ)
    (hmu : mu ≠ 0) (hc0 : c0 ^ 2 = 1 / 2)
    (hupden : ∀ q ∈ U,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (upTarget q) : ℝ))
    (hdownLeaves : ∀ q ∈ D,
      downLeaves q ⊆ largePrimeLeaves S X Y (downTarget q))
    (hdownCard : ∀ q ∈ D, ((downLeaves q).card : ℝ) = mu ^ 2)
    (hdownden : ∀ q ∈ D,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (downTarget q) : ℝ)) :
    (∑ q ∈ U, 2 * mu *
        ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
          actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
      (∑ q ∈ D, 2 * mu *
        ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ) -
      U.card =
      finiteStarCorrection U D
        (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2) := by
  apply finiteStarCorrection_eq
  · intro q hq
    rw [actualUpStar_quadraticForm_ratio hmu (hupden q hq) hc0]
    rw [upStarCorrection]
    have hmu2 : mu ^ 2 ≠ 0 := pow_ne_zero 2 hmu
    have hden := hupden q hq
    field_simp [hmu2, sub_ne_zero.mpr hden]
    ring
  · intro q hq
    exact actualDownStar_quadraticForm_ratio
      (hdownLeaves q hq) (hdownCard q hq) hmu (hdownden q hq) hc0

theorem actualFinitePrimeStarRemainder_bound
    {S : Finset ℕ} {X Y : ℕ} {ι κ : Type*}
    (U : Finset ι) (Dset : Finset κ)
    (upTarget : ι → Vertex S X) (downTarget : κ → Vertex S X)
    (downLeaves : κ → Finset (Vertex S X))
    (lam mu primeCount boundary err eta shiftBound c0 : ℝ)
    (hmu : mu ≠ 0) (hc0 : c0 ^ 2 = 1 / 2)
    (hupden : ∀ q ∈ U,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (upTarget q) : ℝ))
    (hdownLeaves : ∀ q ∈ Dset,
      downLeaves q ⊆ largePrimeLeaves S X Y (downTarget q))
    (hdownCard : ∀ q ∈ Dset, ((downLeaves q).card : ℝ) = mu ^ 2)
    (hdownden : ∀ q ∈ Dset,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (downTarget q) : ℝ))
    (hboundary : boundary = U.card)
    (hdegree : mu ^ 2 = primeCount - boundary)
    (hdisp : lam - mu =
      (∑ q ∈ U,
        ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
          actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
      (∑ q ∈ Dset,
        ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ) + err)
    (herr : |err| ≤ eta) (hshift : |lam - mu| ≤ shiftBound)
    (hshift0 : 0 ≤ shiftBound) :
    |(lam ^ 2 - primeCount) -
      finiteStarCorrection U Dset
        (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2)| ≤
      2 * |mu| * eta + shiftBound ^ 2 := by
  let rho :=
    (∑ q ∈ U,
      ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
        actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
    (∑ q ∈ Dset,
      ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
        actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ)
  apply abs_squaredCorrection_le lam mu primeCount boundary rho err
    (finiteStarCorrection U Dset
      (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
      (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2))
    eta shiftBound hshift0
  · simpa [rho, add_assoc] using hdisp
  · exact hdegree
  · rw [hboundary]
    have hactual := actualFiniteStarCorrection_eq U Dset upTarget downTarget
      downLeaves mu c0 hmu hc0 hupden hdownLeaves hdownCard hdownden
    have hactualDegree :
        (∑ q ∈ U, 2 * mu *
            ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
              actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
          (∑ q ∈ Dset, 2 * mu *
            ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
              actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ) -
          U.card =
          finiteStarCorrection U Dset
            (fun q ↦ ((largePrimeGraph S X Y).degree (upTarget q) : ℝ) / mu ^ 2)
            (fun q ↦ ((largePrimeGraph S X Y).degree (downTarget q) : ℝ) /
              mu ^ 2) := by
      simpa only [largePrimeStarDegree_eq_degree] using hactual
    dsimp [rho]
    rw [← hactualDegree]
    rw [mul_add]
    rw [Finset.mul_sum, Finset.mul_sum]
  · exact herr
  · exact hshift

end

end PrimeStar
