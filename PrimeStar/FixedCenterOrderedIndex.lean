import PrimeStar.FixedCenterRemainderAssembly
import PrimeStar.StarInertia

/-!
# Fixed-centre arithmetic rank

The manuscript numbers the allowed arithmetic centres increasingly.  This
module identifies that one-based rank with the ordered eigenvalue slot used
by the fixed-centre spectral construction.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

/-- One-based arithmetic rank of a vertex among the allowed positive
integers in the finite graph. -/
def arithmeticCenterRank {S : Finset ℕ} {X : ℕ} (a : Vertex S X) : ℕ :=
  (Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (a : ℕ)).card + 1

theorem arithmeticCenterRank_pos
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X) :
    0 < arithmeticCenterRank a := by
  simp [arithmeticCenterRank]

/-- For a fixed centre, the canonical large-prime positive-star slot is
eventually exactly the manuscript's arithmetic centre rank (with Lean's
ordered eigenvalue index written zero-based). -/
theorem eventually_fixedCenter_largePrimeOrderedIndex_eq_arithmeticRank
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      ∀ (haY : (a : ℕ) ≤ Nat.sqrt X)
        (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
      (largePrimePositiveStarOrderedIndex a
          (sqrtCutoff_condition X) haY hd).1 + 1 =
        arithmeticCenterRank a := by
  filter_upwards [eventually_fixedCenter_gap_residual_bundle S hS hc]
    with X hbundle
  intro a ha haY hd
  obtain ⟨_haY', _hd', _hzero, hdegree, _hH, heta, hlarge⟩ := hbundle a ha
  have hgammaPos : 0 < fixedCenterGapScale c X := by
    have : 0 < 16 * sqrtCutoffResidualScale X := mul_pos (by norm_num) heta
    exact this.trans_le hlarge
  have huniq : ∀ b : Vertex S X, (b : ℕ) ≤ Nat.sqrt X →
      0 < largePrimeStarDegree S X (Nat.sqrt X) b →
      largePrimeStarDegree S X (Nat.sqrt X) b =
        largePrimeStarDegree S X (Nat.sqrt X) a → b = a := by
    intro b hbY hbd hba
    by_contra hne
    have hgap := hdegree b hbY hne hbd
    rw [hba, sub_self, abs_zero] at hgap
    exact (not_lt_of_ge hgap) hgammaPos
  rw [largePrimePositiveStarOrderedIndex_val_eq_arithmeticRank
    hS a (sqrtCutoff_condition X) haY hd huniq]
  rfl

end

end PrimeStar
