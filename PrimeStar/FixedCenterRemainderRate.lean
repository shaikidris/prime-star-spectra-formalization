import PrimeStar.FixedCenterFiniteRemainder

namespace PrimeStar

open Filter Topology
open scoped InnerProductSpace

noncomputable section

local instance fixedCenterRatePrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

local instance fixedCenterRateLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

local instance fixedCenterRateSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj := Classical.decRel _

def fixedCenterRemainderRatioConstant (c : ℕ) : ℝ :=
  16 * sqrtCutoffResidualConstant ^ 4 /
    fixedCenterDegreeGapConstant c ^ 2

theorem eventually_fixedCenter_residualFourth_div_gapSq_le
    (c : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      sqrtCutoffResidualScale X ^ 4 / fixedCenterGapScale c X ^ 2 ≤
        fixedCenterRemainderRatioConstant c / Real.log (X : ℝ) := by
  filter_upwards [eventually_ge_atTop 2] with X hX
  let x : ℝ := X
  let y : ℝ := (Nat.sqrt X + 1 : ℕ)
  let K := sqrtCutoffResidualConstant
  let k := fixedCenterDegreeGapConstant c
  have hx : 1 < x := by dsimp [x]; exact_mod_cast hX
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hsqrtOne : (1 : ℝ) ≤ √x := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by dsimp [x]; exact_mod_cast (show 1 ≤ X from (by omega)))
  have hy : 0 < y := by dsimp [y]; positivity
  have hyupper : y ≤ 2 * √x := by
    dsimp [x, y]
    push_cast
    have hsqrtNat := Real.nat_sqrt_le_real_sqrt (a := X)
    linarith
  have hlog : Real.log x / 2 ≤ Real.log y := by
    have hsqrtPos : 0 < √x := Real.sqrt_pos.2 (by positivity)
    have hlt : √x < y := by
      dsimp [x, y]
      simpa [Nat.cast_add, Nat.cast_one] using
        (Real.real_sqrt_lt_nat_sqrt_succ (a := X))
    have hmono := Real.strictMonoOn_log.monotoneOn hsqrtPos hy hlt.le
    rw [Real.log_sqrt hx0] at hmono
    exact hmono
  have htuned := tunedSchurScale_sq_le_four_sqrt_div_log hx hy hyupper hlog
  have hK : 0 ≤ K := sqrtCutoffResidualConstant_pos.le
  have hk : 0 < k := fixedCenterDegreeGapConstant_pos c
  have hmain : 0 < x / Real.log x := div_pos (by positivity) hlogx
  have hsqrtSq : (√x) ^ 2 = x := Real.sq_sqrt hx0
  have heta4 : sqrtCutoffResidualScale X ^ 4 ≤
      16 * K ^ 4 * (x / Real.log x ^ 2) := by
    calc
      sqrtCutoffResidualScale X ^ 4 = K ^ 4 * tunedSchurScale y ^ 4 := by
        simp [sqrtCutoffResidualScale, K, y]
        ring
      _ = K ^ 4 * (tunedSchurScale y ^ 2) ^ 2 := by ring
      _ ≤ K ^ 4 * (4 * √x / Real.log x) ^ 2 := by gcongr
      _ = 16 * K ^ 4 * (x / Real.log x ^ 2) := by
        have hnumSq : (4 * √x) ^ 2 = 16 * x := by
          rw [mul_pow, hsqrtSq]
          norm_num
        rw [div_pow, hnumSq]
        ring
  have hgammaSq : fixedCenterGapScale c X ^ 2 = k ^ 2 * (x / Real.log x) := by
    dsimp [fixedCenterGapScale, k, x]
    rw [mul_pow, Real.sq_sqrt hmain.le]
  rw [hgammaSq]
  calc
    sqrtCutoffResidualScale X ^ 4 / (k ^ 2 * (x / Real.log x)) ≤
        (16 * K ^ 4 * (x / Real.log x ^ 2)) /
          (k ^ 2 * (x / Real.log x)) := by
            gcongr
    _ = fixedCenterRemainderRatioConstant c / Real.log (X : ℝ) := by
      dsimp [fixedCenterRemainderRatioConstant, K, k, x]
      field_simp

def fixedCenterFiniteRemainderRateConstant (c : ℕ) : ℝ :=
  (1408 / fixedCenterDegreeGapConstant c + 100) *
    fixedCenterRemainderRatioConstant c

theorem eventually_fixedCenter_finiteRemainderMajorant_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      let mu := √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)
      704 * |mu| *
          (sqrtCutoffResidualScale X ^ 4 / fixedCenterGapScale c X ^ 3) +
        100 * (sqrtCutoffResidualScale X ^ 4 / fixedCenterGapScale c X ^ 2) ≤
      fixedCenterFiniteRemainderRateConstant c / Real.log (X : ℝ) := by
  filter_upwards [eventually_fixedCenter_residualFourth_div_gapSq_le c,
    eventually_sqrtCutoff_largePrimeStarDegree_le_four_main S hS,
    eventually_fixedCenter_gap_residual_bundle S hS hc,
    eventually_ge_atTop 2] with X hrate hupper hbundle hX
  intro a ha
  dsimp only
  obtain ⟨haY, hd, hzero, _hdegree, _hH, _heta, _hlarge⟩ := hbundle a ha
  let mu := √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)
  let gamma := fixedCenterGapScale c X
  let eta := sqrtCutoffResidualScale X
  let k := fixedCenterDegreeGapConstant c
  let M := (X : ℝ) / Real.log (X : ℝ)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hM : 0 < M := by dsimp [M]; positivity
  have hk : 0 < k := fixedCenterDegreeGapConstant_pos c
  have hgamma : 0 < gamma := by
    dsimp [gamma, fixedCenterGapScale, k, M]
    positivity
  have hmu0 : 0 ≤ mu := Real.sqrt_nonneg _
  have hmuSq : mu ^ 2 = (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
    dsimp [mu]
    rw [Real.sq_sqrt]
    positivity
  have hupperA := hupper a haY
  have hmuUpper : mu ≤ 2 * √M := by
    apply (sq_le_sq₀ hmu0 (by positivity)).mp
    rw [hmuSq, mul_pow, Real.sq_sqrt hM.le]
    norm_num
    exact hupperA
  have hgammaEq : gamma = k * √M := by
    rfl
  have hmuRatio : |mu| / gamma ≤ 2 / k := by
    rw [abs_of_nonneg hmu0, div_le_iff₀ hgamma]
    calc
      mu ≤ 2 * √M := hmuUpper
      _ = (2 / k) * gamma := by
        rw [hgammaEq]
        field_simp
  have hrate' : eta ^ 4 / gamma ^ 2 ≤
      fixedCenterRemainderRatioConstant c / Real.log (X : ℝ) := by
    simpa [eta, gamma] using hrate
  have hrateNonneg : 0 ≤ fixedCenterRemainderRatioConstant c /
      Real.log (X : ℝ) := by
    dsimp [fixedCenterRemainderRatioConstant]
    positivity
  have hratioNonneg : 0 ≤ |mu| / gamma := by positivity
  have hterm : |mu| * (eta ^ 4 / gamma ^ 3) ≤
      (2 / k) *
        (fixedCenterRemainderRatioConstant c / Real.log (X : ℝ)) := by
    calc
      |mu| * (eta ^ 4 / gamma ^ 3) =
          (|mu| / gamma) * (eta ^ 4 / gamma ^ 2) := by field_simp
      _ ≤ (2 / k) *
          (fixedCenterRemainderRatioConstant c / Real.log (X : ℝ)) := by
            gcongr
  change 704 * |mu| * (eta ^ 4 / gamma ^ 3) +
      100 * (eta ^ 4 / gamma ^ 2) ≤ _
  have hterm704 : 704 * |mu| * (eta ^ 4 / gamma ^ 3) ≤
      704 * ((2 / k) *
        (fixedCenterRemainderRatioConstant c / Real.log (X : ℝ))) := by
    calc
      704 * |mu| * (eta ^ 4 / gamma ^ 3) =
          704 * (|mu| * (eta ^ 4 / gamma ^ 3)) := by ring
      _ ≤ 704 * ((2 / k) *
          (fixedCenterRemainderRatioConstant c / Real.log (X : ℝ))) := by
            gcongr
  have hterm100 : 100 * (eta ^ 4 / gamma ^ 2) ≤
      100 * (fixedCenterRemainderRatioConstant c / Real.log (X : ℝ)) := by
    gcongr
  calc
    704 * |mu| * (eta ^ 4 / gamma ^ 3) +
        100 * (eta ^ 4 / gamma ^ 2) ≤
      704 * ((2 / k) *
          (fixedCenterRemainderRatioConstant c / Real.log (X : ℝ))) +
        100 * (fixedCenterRemainderRatioConstant c / Real.log (X : ℝ)) :=
      add_le_add hterm704 hterm100
    _ = fixedCenterFiniteRemainderRateConstant c / Real.log (X : ℝ) := by
      dsimp [fixedCenterFiniteRemainderRateConstant, k]
      ring

/-- Fixed-centre `O(1 / log X)` form of the finite first-exit remainder.
This is the formal error-term layer of the manuscript's Theorem 8.7; the
subsequent prime-Mertens evaluation of the finite correction is separate. -/
theorem eventually_fixedCenter_exists_finiteRemainder_logBound
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
        (let mu := √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)
         |(lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            finiteStarCorrection
              (Finset.univ : Finset (CanonicalUpIndex S X (Nat.sqrt X) a))
              (Finset.univ : Finset (CanonicalDownIndex a))
              (fun q ↦
                (largePrimeStarDegree S X (Nat.sqrt X)
                    (canonicalUpTarget hS a q) : ℝ) / mu ^ 2)
              (fun q ↦
                (largePrimeStarDegree S X (Nat.sqrt X)
                    (canonicalDownTarget a q) : ℝ) / mu ^ 2)| ≤
            fixedCenterFiniteRemainderRateConstant c /
              Real.log (X : ℝ)) := by
  filter_upwards [eventually_fixedCenter_exists_finiteRemainder_bound S hS hc,
    eventually_fixedCenter_finiteRemainderMajorant_le S hS hc] with
      X hfinite hmajorant
  intro a ha
  obtain ⟨lam, v, hv, hAv, halpha, hsharp, hsimple, hrem⟩ := hfinite a ha
  refine ⟨lam, v, hv, hAv, halpha, hsharp, hsimple, ?_⟩
  exact hrem.trans (hmajorant a ha)

/-- Prescribed ordered-index form of the fixed-centre finite remainder.  The
eigenvalue is the ordered full-graph entry at the exact positive star index
selected by the centre, not an existential nearby eigenvalue. -/
theorem eventually_fixedCenter_ordered_finiteRemainder_logBound
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
      let mu := √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)
      |(lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
          finiteStarCorrection
            (Finset.univ : Finset (CanonicalUpIndex S X (Nat.sqrt X) a))
            (Finset.univ : Finset (CanonicalDownIndex a))
            (fun q ↦
              (largePrimeStarDegree S X (Nat.sqrt X)
                  (canonicalUpTarget hS a q) : ℝ) / mu ^ 2)
            (fun q ↦
              (largePrimeStarDegree S X (Nat.sqrt X)
                  (canonicalDownTarget a q) : ℝ) / mu ^ 2)| ≤
        fixedCenterFiniteRemainderRateConstant c / Real.log (X : ℝ) := by
  filter_upwards [eventually_fixedCenter_gap_residual_bundle S hS hc,
    eventually_fixedCenter_finiteRemainderMajorant_le S hS hc] with
      X hbundle hmajorant
  intro a ha
  obtain ⟨haY, hd, hzero, hdegree, hH, heta, hlarge⟩ := hbundle a ha
  refine ⟨haY, hd, ?_⟩
  have hgamma : 0 ≤ fixedCenterGapScale c X := by linarith
  have hsmall : 2 * sqrtCutoffResidualScale X < fixedCenterGapScale c X := by
    linarith
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
  let v := (hL.add hHs).eigenvectorBasis rfl i
  obtain ⟨_hv, hAv, halpha, hnear, _hsimple⟩ :=
    primeCover_ordered_arithmeticStarEigenpair_withOverlap_of_degreeGap
      a (sqrtCutoff_condition X) haY hd
      (fixedCenterGapScale c X) (sqrtCutoffResidualScale X)
      hgamma hzero hdegree hH hsmall
  have hsharp := primeCover_fixedCenter_shift_le_ten
    (sqrtCutoff_condition X) haY hd heta hlarge hzero hdegree
    v hAv halpha hH hnear
  have hnearCrude : |lam - √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)| ≤
      sqrtCutoffResidualScale X := hsharp.trans (by
    have hgapPos : 0 < fixedCenterGapScale c X := by linarith
    calc
      10 * (sqrtCutoffResidualScale X ^ 2 / fixedCenterGapScale c X) =
          (10 * sqrtCutoffResidualScale X ^ 2) /
            fixedCenterGapScale c X := by ring
      _ ≤ sqrtCutoffResidualScale X :=
        (div_le_iff₀ hgapPos).2 (by nlinarith))
  have hfinite := primeCover_fixedCenter_finiteRemainder_bound
    hS (Nat.sqrt_le X) (sqrtCutoff_condition X) haY hd heta hlarge
    hzero hdegree v hAv halpha hH hnearCrude
  dsimp only at hfinite ⊢
  exact hfinite.trans (hmajorant a ha)

end

end PrimeStar
