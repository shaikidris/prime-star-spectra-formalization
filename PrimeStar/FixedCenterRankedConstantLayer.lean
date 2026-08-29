import PrimeStar.FixedCenterCorrectionBridge
import PrimeStar.FixedCenterOrderedIndex

/-!
# The fixed-centre expansion at the manuscript's ordered eigenvalue

This module combines the centre-labelled constant layer with the positive
inertia count.  Thus the eigenvalue controlled by the expansion is the
ordered eigenvalue whose one-based slot is the arithmetic rank of the
centre.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

local instance fixedCenterRankedLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

local instance fixedCenterRankedSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj := Classical.decRel _

/-- Fixed-centre constant layer at the manuscript's prescribed ordered
eigenvalue `lambda_j`, with `j` identified as the one-based arithmetic rank
of the centre. -/
theorem eventually_fixedCenter_ranked_constantLayer
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
        (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
      let L := Matrix.toEuclideanLin
        ((largePrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
      let H := Matrix.toEuclideanLin
        ((smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
      let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        ((largePrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
      let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        ((smallPrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
      let i := largePrimePositiveStarOrderedIndex a
        (sqrtCutoff_condition X) haY hd
      let lam := (hL.add hHs).eigenvalues rfl i
      i.1 + 1 = arithmeticCenterRank a ∧
        |((lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
              4 * Real.log (Real.log (X : ℝ))) -
            (4 * primeStarKappa meisselMertensConstant S +
              centerPrimeCorrection c)| < ε := by
  filter_upwards [eventually_fixedCenter_ordered_constantLayer S hS hc hε,
    eventually_fixedCenter_largePrimeOrderedIndex_eq_arithmeticRank S hS hc]
    with X hconstant hrank
  intro a ha
  obtain ⟨haY, hd, hbound⟩ := hconstant a ha
  refine ⟨haY, hd, ?_⟩
  dsimp only at hbound ⊢
  exact ⟨hrank a ha haY hd, hbound⟩

end

end PrimeStar
