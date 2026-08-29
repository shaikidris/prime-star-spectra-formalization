import PrimeStar.FixedCenterConstantLayer

/-!
# Bridge from canonical graph blocks to the arithmetic correction

At the square-root cutoff, the canonical first-exit correction in the finite
spectral theorem is exactly the arithmetic correction evaluated by the
fixed-centre head--tail argument.  This module records that finite identity.
-/

namespace PrimeStar

open Filter Topology
open scoped BigOperators InnerProductSpace

noncomputable section

local instance fixedCenterCorrectionBridgePrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

local instance fixedCenterCorrectionBridgeLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

local instance fixedCenterCorrectionBridgeSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj := Classical.decRel _

/-- A large-prime star degree, viewed in `ℝ`, is the corresponding arithmetic
degree whenever its centre is below the cutoff and its whole large-prime
range is nonempty. -/
theorem largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (b : Vertex S X) (hbY : (b : ℕ) ≤ Nat.sqrt X)
    (hYXb : Nat.sqrt X ≤ X / (b : ℕ)) :
    (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ) =
      fixedCenterArithmeticDegree S (b : ℕ) X := by
  have hcount := allowedPrimeCount_mono (S := S) hYXb
  rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS b hbY hYXb,
    Nat.cast_sub hcount]
  unfold fixedCenterArithmeticDegree
  rfl

/-- The canonical up-block degree ratio is the actual arithmetic up ratio at
the square-root cutoff. -/
theorem canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : Vertex S X) (haY : (a : ℕ) ≤ Nat.sqrt X)
    (q : CanonicalUpIndex S X (Nat.sqrt X) a) :
    (largePrimeStarDegree S X (Nat.sqrt X)
        (canonicalUpTarget hS a q) : ℝ) /
        (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) =
      fixedCenterActualUpRatio S (a : ℕ) X q := by
  have hqdata := Finset.mem_filter.mp q.property
  have hqPrime : (q : ℕ).Prime := (Nat.mem_primesLE.mp hqdata.1).2
  have hqY : (q : ℕ) ≤ Nat.sqrt X := (Nat.mem_primesLE.mp hqdata.1).1
  have hcut : X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := Nat.lt_succ_sqrt X
  have hcenterMul : (a : ℕ) * Nat.sqrt X ≤ X :=
    (Nat.mul_le_mul_right (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hYcenter : Nat.sqrt X ≤ X / (a : ℕ) :=
    (Nat.le_div_iff_mul_le (Vertex.coe_pos a)).2
      (by simpa [Nat.mul_comm] using hcenterMul)
  have hcenterDegree :=
    largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree hS a haY hYcenter
  by_cases htargetY : (a : ℕ) * (q : ℕ) ≤ Nat.sqrt X
  · have htargetCoe :
        (canonicalUpTarget hS a q : ℕ) = (a : ℕ) * (q : ℕ) :=
      canonicalUpTarget_coe hS a q
    have htargetMul :
        (canonicalUpTarget hS a q : ℕ) * Nat.sqrt X ≤ X := by
      rw [htargetCoe]
      exact (Nat.mul_le_mul_right (Nat.sqrt X) htargetY).trans (Nat.sqrt_le X)
    have hYtarget : Nat.sqrt X ≤
        X / (canonicalUpTarget hS a q : ℕ) :=
      (Nat.le_div_iff_mul_le (Vertex.coe_pos (canonicalUpTarget hS a q))).2
        (by simpa [Nat.mul_comm] using htargetMul)
    have htargetDegree :=
      largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree hS
        (canonicalUpTarget hS a q) (by simpa only [htargetCoe] using htargetY) hYtarget
    rw [fixedCenterActualUpRatio, if_pos htargetY, htargetDegree, htargetCoe,
      hcenterDegree]
  · have htargetAbove : Nat.sqrt X < (canonicalUpTarget hS a q : ℕ) := by
      rw [canonicalUpTarget_coe]
      exact Nat.lt_of_not_ge htargetY
    have hiso := canonicalUpTarget_isIsolated_of_cutoff_lt
      haY hcut hqPrime hqY (canonicalUpTarget_coe hS a q).symm htargetAbove
    have hdegreeZero : largePrimeStarDegree S X (Nat.sqrt X)
        (canonicalUpTarget hS a q) = 0 :=
      largePrimeStarDegree_eq_zero_iff.mpr hiso
    rw [fixedCenterActualUpRatio, if_neg htargetY, hdegreeZero]
    simp

/-- The canonical down-block degree ratio is the actual arithmetic down ratio
at the square-root cutoff. -/
theorem canonicalDownDegreeRatio_eq_fixedCenterActualDownRatio
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : Vertex S X) (haY : (a : ℕ) ≤ Nat.sqrt X)
    (q : CanonicalDownIndex a) :
    (largePrimeStarDegree S X (Nat.sqrt X)
        (canonicalDownTarget a q) : ℝ) /
        (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) =
      fixedCenterArithmeticDegree S ((a : ℕ) / q) X /
        fixedCenterArithmeticDegree S (a : ℕ) X := by
  have hqPrime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.property
  have hqPos : 0 < (q : ℕ) := hqPrime.pos
  have hqDvd : (q : ℕ) ∣ (a : ℕ) := Nat.dvd_of_mem_primeFactors q.property
  have htargetCoe :
      (canonicalDownTarget a q : ℕ) = (a : ℕ) / (q : ℕ) := rfl
  have htargetLe : (canonicalDownTarget a q : ℕ) ≤ (a : ℕ) := by
    rw [htargetCoe]
    exact Nat.div_le_self (a : ℕ) (q : ℕ)
  have htargetY : (canonicalDownTarget a q : ℕ) ≤ Nat.sqrt X :=
    htargetLe.trans haY
  have hcenterMul : (a : ℕ) * Nat.sqrt X ≤ X :=
    (Nat.mul_le_mul_right (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have htargetMul :
      (canonicalDownTarget a q : ℕ) * Nat.sqrt X ≤ X :=
    (Nat.mul_le_mul_right (Nat.sqrt X) htargetLe).trans hcenterMul
  have hYcenter : Nat.sqrt X ≤ X / (a : ℕ) :=
    (Nat.le_div_iff_mul_le (Vertex.coe_pos a)).2
      (by simpa [Nat.mul_comm] using hcenterMul)
  have hYtarget : Nat.sqrt X ≤ X / (canonicalDownTarget a q : ℕ) :=
    (Nat.le_div_iff_mul_le (Vertex.coe_pos (canonicalDownTarget a q))).2
      (by simpa [Nat.mul_comm] using htargetMul)
  have hcenterDegree :=
    largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree hS a haY hYcenter
  have htargetDegree :=
    largePrimeStarDegree_cast_eq_fixedCenterArithmeticDegree hS
      (canonicalDownTarget a q) htargetY hYtarget
  rw [htargetDegree, htargetCoe, hcenterDegree]

/-- At the square-root cutoff, the canonical graph correction in the finite
remainder theorem is literally the actual arithmetic correction. -/
theorem canonicalFiniteStarCorrection_eq_fixedCenterActualCorrection
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : Vertex S X) (haY : (a : ℕ) ≤ Nat.sqrt X) :
    let mu := √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)
    finiteStarCorrection
        (Finset.univ : Finset (CanonicalUpIndex S X (Nat.sqrt X) a))
        (Finset.univ : Finset (CanonicalDownIndex a))
        (fun q ↦
          (largePrimeStarDegree S X (Nat.sqrt X)
              (canonicalUpTarget hS a q) : ℝ) / mu ^ 2)
        (fun q ↦
          (largePrimeStarDegree S X (Nat.sqrt X)
              (canonicalDownTarget a q) : ℝ) / mu ^ 2) =
      fixedCenterActualCorrection S (a : ℕ) X := by
  dsimp only
  have hcenterMul : (a : ℕ) * Nat.sqrt X ≤ X :=
    (Nat.mul_le_mul_right (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hYcenter : Nat.sqrt X ≤ X / (a : ℕ) :=
    (Nat.le_div_iff_mul_le (Vertex.coe_pos a)).2
      (by simpa [Nat.mul_comm] using hcenterMul)
  have hmuSq :
      (√(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)) ^ 2 =
        (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [finiteStarCorrection, fixedCenterActualCorrection,
    fixedCenterActualUpCorrection, fixedCenterActualDownCorrection]
  have hup :
      (∑ q : CanonicalUpIndex S X (Nat.sqrt X) a,
        upStarCorrection
          ((largePrimeStarDegree S X (Nat.sqrt X)
              (canonicalUpTarget hS a q) : ℝ) /
            (√(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)) ^ 2)) =
        ∑ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
          upStarCorrection (fixedCenterActualUpRatio S (a : ℕ) X q) := by
    calc
      (∑ q : CanonicalUpIndex S X (Nat.sqrt X) a,
          upStarCorrection
            ((largePrimeStarDegree S X (Nat.sqrt X)
                (canonicalUpTarget hS a q) : ℝ) /
              (√(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)) ^ 2)) =
          ∑ q : CanonicalUpIndex S X (Nat.sqrt X) a,
            upStarCorrection (fixedCenterActualUpRatio S (a : ℕ) X q) := by
        apply Finset.sum_congr rfl
        intro q _hq
        congr 1
        rw [hmuSq]
        exact canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio hS a haY q
      _ = ∑ q ∈ canonicalUpPrimeLabels S X (Nat.sqrt X) a,
          upStarCorrection (fixedCenterActualUpRatio S (a : ℕ) X q) := by
        symm
        exact Finset.sum_subtype _ (fun _ ↦ Iff.rfl) _
      _ = ∑ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
          upStarCorrection (fixedCenterActualUpRatio S (a : ℕ) X q) := by
        rw [canonicalUpPrimeLabels_eq_allowedPrimeSet hcenterMul]
  have hdown :
      (∑ q : CanonicalDownIndex a,
        downStarCorrection
          ((largePrimeStarDegree S X (Nat.sqrt X)
              (canonicalDownTarget a q) : ℝ) /
            (√(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)) ^ 2)) =
        ∑ q ∈ (a : ℕ).primeFactors,
          downStarCorrection
            (fixedCenterArithmeticDegree S ((a : ℕ) / q) X /
              fixedCenterArithmeticDegree S (a : ℕ) X) := by
    calc
      (∑ q : CanonicalDownIndex a,
          downStarCorrection
            ((largePrimeStarDegree S X (Nat.sqrt X)
                (canonicalDownTarget a q) : ℝ) /
              (√(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)) ^ 2)) =
          ∑ q : CanonicalDownIndex a,
            downStarCorrection
              (fixedCenterArithmeticDegree S ((a : ℕ) / q) X /
                fixedCenterArithmeticDegree S (a : ℕ) X) := by
        apply Finset.sum_congr rfl
        intro q _hq
        congr 1
        rw [hmuSq]
        exact canonicalDownDegreeRatio_eq_fixedCenterActualDownRatio hS a haY q
      _ = ∑ q ∈ (a : ℕ).primeFactors,
          downStarCorrection
            (fixedCenterArithmeticDegree S ((a : ℕ) / q) X /
              fixedCenterArithmeticDegree S (a : ℕ) X) := by
        symm
        exact Finset.sum_subtype _ (fun _ ↦ Iff.rfl) _
  rw [hup, hdown]

/-- The fixed-centre spectral remainder can be stated directly with the
actual arithmetic correction, rather than the isomorphic canonical block
sum. -/
theorem eventually_fixedCenter_exists_actualCorrection_logBound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      ∃ (lam : ℝ) (v : EuclideanSpace ℝ (Vertex S X)),
        ‖v‖ = 1 ∧
        Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v ∧
        (⟪largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1, v⟫_ℝ ≠ 0) ∧
        |lam - √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)| ≤
          10 * (sqrtCutoffResidualScale X ^ 2 / fixedCenterGapScale c X) ∧
        Module.finrank ℝ
          (Module.End.eigenspace
            (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)) lam) = 1 ∧
        |(lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            fixedCenterActualCorrection S c X| ≤
          fixedCenterFiniteRemainderRateConstant c / Real.log (X : ℝ) := by
  filter_upwards [eventually_fixedCenter_exists_finiteRemainder_logBound S hS hc,
    eventually_fixedCenter_le_natSqrt (c := c)] with X hfinite hcY
  intro a ha
  obtain ⟨lam, v, hv, hAv, halpha, hsharp, hsimple, hrem⟩ := hfinite a ha
  have haY : (a : ℕ) ≤ Nat.sqrt X := by simpa only [ha] using hcY
  have hbridge := canonicalFiniteStarCorrection_eq_fixedCenterActualCorrection hS a haY
  refine ⟨lam, v, hv, hAv, halpha, hsharp, hsimple, ?_⟩
  dsimp only at hrem hbridge
  rw [hbridge] at hrem
  simpa only [ha] using hrem

/-- Ordered-index form of the fixed-centre spectral remainder.  The scalar is
the full adjacency eigenvalue at the same ordered slot as the centre's exact
positive large-prime star mode. -/
theorem eventually_fixedCenter_ordered_actualCorrection_logBound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
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
      |(lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
          fixedCenterActualCorrection S c X| ≤
        fixedCenterFiniteRemainderRateConstant c / Real.log (X : ℝ) := by
  filter_upwards [eventually_fixedCenter_ordered_finiteRemainder_logBound S hS hc,
    eventually_fixedCenter_le_natSqrt (c := c)] with X hfinite hcY
  intro a ha
  obtain ⟨haY, hd, hrem⟩ := hfinite a ha
  refine ⟨haY, hd, ?_⟩
  have hbridge := canonicalFiniteStarCorrection_eq_fixedCenterActualCorrection hS a haY
  dsimp only at hrem hbridge ⊢
  rw [hbridge] at hrem
  simpa only [ha] using hrem

/-- Fixed-centre constant-layer form of Corollary 8.9.  The conclusion is an
eventual epsilon formulation of the `o(1)` remainder and retains the matched
simple eigenpair supplied by the finite spectral theorem. -/
theorem eventually_fixedCenter_exists_constantLayer
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      ∃ (lam : ℝ) (v : EuclideanSpace ℝ (Vertex S X)),
        ‖v‖ = 1 ∧
        Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v ∧
        (⟪largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1, v⟫_ℝ ≠ 0) ∧
        Module.finrank ℝ
          (Module.End.eigenspace
            (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)) lam) = 1 ∧
        |((lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
              4 * Real.log (Real.log (X : ℝ))) -
            (4 * primeStarKappa meisselMertensConstant S +
              centerPrimeCorrection c)| < ε := by
  let C : ℝ := 4 * primeStarKappa meisselMertensConstant S +
    centerPrimeCorrection c
  have hcorr := fixedCenterActualCorrection_sub_logLog_tendsto S hS hc
  have hcorr0 : Tendsto
      (fun X : ℕ ↦
        (fixedCenterActualCorrection S c X -
          4 * Real.log (Real.log (X : ℝ))) - C)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
    have h := hcorr.sub hconst
    simpa only [C, sub_self] using h
  have hcorrAbs : Tendsto
      (fun X : ℕ ↦
        |(fixedCenterActualCorrection S c X -
          4 * Real.log (Real.log (X : ℝ))) - C|)
      atTop (𝓝 0) := by
    simpa using hcorr0.abs
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrate : Tendsto
      (fun X : ℕ ↦ fixedCenterFiniteRemainderRateConstant c /
        Real.log (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogTop
  have hhalf : 0 < ε / 2 := by linarith
  have hcorrSmall : ∀ᶠ X : ℕ in atTop,
      |(fixedCenterActualCorrection S c X -
          4 * Real.log (Real.log (X : ℝ))) - C| < ε / 2 :=
    (tendsto_order.1 hcorrAbs).2 (ε / 2) hhalf
  have hrateSmall : ∀ᶠ X : ℕ in atTop,
      fixedCenterFiniteRemainderRateConstant c / Real.log (X : ℝ) < ε / 2 :=
    (tendsto_order.1 hrate).2 (ε / 2) hhalf
  filter_upwards [eventually_fixedCenter_exists_actualCorrection_logBound S hS hc,
    hcorrSmall, hrateSmall] with X hfinite hcorrX hrateX
  intro a ha
  obtain ⟨lam, v, hv, hAv, halpha, _hsharp, hsimple, hrem⟩ := hfinite a ha
  refine ⟨lam, v, hv, hAv, halpha, hsimple, ?_⟩
  change |((lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
      4 * Real.log (Real.log (X : ℝ))) - C| < ε
  calc
    |((lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
        4 * Real.log (Real.log (X : ℝ))) - C| =
        |((lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            fixedCenterActualCorrection S c X) +
          ((fixedCenterActualCorrection S c X -
            4 * Real.log (Real.log (X : ℝ))) - C)| := by ring
    _ ≤ |(lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            fixedCenterActualCorrection S c X| +
          |(fixedCenterActualCorrection S c X -
            4 * Real.log (Real.log (X : ℝ))) - C| := abs_add_le _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt (hrem.trans hrateX.le) hcorrX
    _ = ε := by ring

/-- Prescribed ordered-index form of the fixed-centre constant layer.  This
removes the existential eigenvalue from Corollary 8.9: the displayed scalar
is the full adjacency eigenvalue at the centre's ordered large-prime star
slot. -/
theorem eventually_fixedCenter_ordered_constantLayer
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
      |((lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            4 * Real.log (Real.log (X : ℝ))) -
          (4 * primeStarKappa meisselMertensConstant S +
            centerPrimeCorrection c)| < ε := by
  let C : ℝ := 4 * primeStarKappa meisselMertensConstant S +
    centerPrimeCorrection c
  have hcorr := fixedCenterActualCorrection_sub_logLog_tendsto S hS hc
  have hcorr0 : Tendsto
      (fun X : ℕ ↦
        (fixedCenterActualCorrection S c X -
          4 * Real.log (Real.log (X : ℝ))) - C)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
    have h := hcorr.sub hconst
    simpa only [C, sub_self] using h
  have hcorrAbs : Tendsto
      (fun X : ℕ ↦
        |(fixedCenterActualCorrection S c X -
          4 * Real.log (Real.log (X : ℝ))) - C|)
      atTop (𝓝 0) := by
    simpa using hcorr0.abs
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrate : Tendsto
      (fun X : ℕ ↦ fixedCenterFiniteRemainderRateConstant c /
        Real.log (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogTop
  have hhalf : 0 < ε / 2 := by linarith
  have hcorrSmall : ∀ᶠ X : ℕ in atTop,
      |(fixedCenterActualCorrection S c X -
          4 * Real.log (Real.log (X : ℝ))) - C| < ε / 2 :=
    (tendsto_order.1 hcorrAbs).2 (ε / 2) hhalf
  have hrateSmall : ∀ᶠ X : ℕ in atTop,
      fixedCenterFiniteRemainderRateConstant c / Real.log (X : ℝ) < ε / 2 :=
    (tendsto_order.1 hrate).2 (ε / 2) hhalf
  filter_upwards [eventually_fixedCenter_ordered_actualCorrection_logBound S hS hc,
    hcorrSmall, hrateSmall] with X hfinite hcorrX hrateX
  intro a ha
  obtain ⟨haY, hd, hrem⟩ := hfinite a ha
  refine ⟨haY, hd, ?_⟩
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
  change |((lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
      4 * Real.log (Real.log (X : ℝ))) - C| < ε
  change |(lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
      fixedCenterActualCorrection S c X| ≤
    fixedCenterFiniteRemainderRateConstant c / Real.log (X : ℝ) at hrem
  calc
    |((lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
        4 * Real.log (Real.log (X : ℝ))) - C| =
        |((lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
          fixedCenterActualCorrection S c X) +
        ((fixedCenterActualCorrection S c X -
          4 * Real.log (Real.log (X : ℝ))) - C)| := by ring
    _ ≤ |(lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
          fixedCenterActualCorrection S c X| +
        |(fixedCenterActualCorrection S c X -
          4 * Real.log (Real.log (X : ℝ))) - C| := abs_add_le _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt (hrem.trans hrateX.le) hcorrX
    _ = ε := by ring

end

end PrimeStar
