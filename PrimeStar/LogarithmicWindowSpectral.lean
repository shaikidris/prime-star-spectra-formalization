import PrimeStar.LogarithmicWindowDegreeIsolation
import PrimeStar.FixedCenterOrderedIndex

/-!
# Spectral assembly on the logarithmic centre window

This module records the exact quantifier structure of Theorems 9.5--9.6.
It does not diagonalize a fixed-centre theorem over a moving centre.  Instead
it consumes the two genuinely uniform outputs of the three-block argument:
uniqueness of the moving reference-star degree and a remainder bound of size
`C * a^2 / log X` at the actual ordered spectral slot.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

local instance logarithmicWindowSpectralLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

local instance logarithmicWindowSpectralSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj := Classical.decRel _

local instance logarithmicWindowSpectralPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

/-- The full adjacency eigenvalue at the same ordered slot as the exact
positive large-prime star mode centred at `a`. -/
def arithmeticStarFullEigenvalue
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (haY : (a : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a) : ℝ :=
  let L := Matrix.toEuclideanLin
    ((largePrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin
    ((smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
  let hH : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
  let i := largePrimePositiveStarOrderedIndex a
    (sqrtCutoff_condition X) haY hd
  (hL.add hH).eigenvalues rfl i

/-- A normalized full-adjacency eigenvector at the same ordered slot as the
positive large-prime star mode centred at `a`.  Its sign is intentionally not
fixed; localization statements orient it by an existential factor
`sigma ∈ {±1}`. -/
def arithmeticStarFullEigenvector
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (haY : (a : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a) :
    EuclideanSpace ℝ (Vertex S X) :=
  let L := Matrix.toEuclideanLin
    ((largePrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin
    ((smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
  let hH : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
  let i := largePrimePositiveStarOrderedIndex a
    (sqrtCutoff_condition X) haY hd
  (hL.add hH).eigenvectorBasis rfl i

@[simp]
theorem norm_arithmeticStarFullEigenvector
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (haY : (a : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a) :
    ‖arithmeticStarFullEigenvector a haY hd‖ = 1 := by
  simp [arithmeticStarFullEigenvector]

theorem primeCoverAdjacency_arithmeticStarFullEigenvector
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (haY : (a : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a) :
    Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
        (arithmeticStarFullEigenvector a haY hd) =
      arithmeticStarFullEigenvalue a haY hd •
        arithmeticStarFullEigenvector a haY hd := by
  let L := Matrix.toEuclideanLin
    ((largePrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin
    ((smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
  let hH : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
  let i := largePrimePositiveStarOrderedIndex a
    (sqrtCutoff_condition X) haY hd
  rw [primeCover_toEuclideanLin_eq_large_add_small S X (Nat.sqrt X)]
  simpa [arithmeticStarFullEigenvalue, arithmeticStarFullEigenvector,
    L, H, hL, hH, i] using (hL.add hH).apply_eigenvectorBasis rfl i

/-- Uniform uniqueness of the moving large-prime star degree. -/
def LogarithmicWindowDegreeUnique
    (S : Finset ℕ) (ε : ℝ) : Prop :=
  ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
    InLogarithmicCenterWindow ε X (a : ℕ) →
      ∀ b : Vertex S X, (b : ℕ) ≤ Nat.sqrt X →
        0 < largePrimeStarDegree S X (Nat.sqrt X) b →
        largePrimeStarDegree S X (Nat.sqrt X) b =
          largePrimeStarDegree S X (Nat.sqrt X) a → b = a

/-- Quantitative PNT discharges the uniform degree-uniqueness interface. -/
theorem logarithmicWindowDegreeUnique
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    LogarithmicWindowDegreeUnique S ε :=
  eventually_logarithmicWindow_largePrimeStarDegree_unique S hS hε

/-- Uniform `a^2 / log X` comparison with the actual finite first-exit
correction.  This is the formal output required from Lemmas 9.1--9.4. -/
def LogarithmicWindowOrderedRemainderBound
    (S : Finset ℕ) (ε C : ℝ) : Prop :=
  ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
    InLogarithmicCenterWindow ε X (a : ℕ) →
      ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
        (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
      |(arithmeticStarFullEigenvalue a haY hd ^ 2 -
          (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
        fixedCenterActualCorrection S (a : ℕ) X| ≤
          C * ((a : ℝ) ^ 2 / Real.log (X : ℝ))

/-- Uniform evaluation of the actual finite correction. -/
def LogarithmicWindowCorrectionEvaluation
    (S : Finset ℕ) (ε : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
    InLogarithmicCenterWindow ε X (a : ℕ) →
      |(fixedCenterActualCorrection S (a : ℕ) X -
          4 * Real.log (Real.log (X : ℝ))) -
        (4 * primeStarKappa meisselMertensConstant S +
          centerPrimeCorrection (a : ℕ))| < δ

/-- Theorem 9.5 at the manuscript's prescribed ordered eigenvalue.  The
selected zero-based spectral index is also identified with the one-based
arithmetic rank `j(a)`. -/
theorem eventually_logarithmicWindow_ranked_actualCorrection
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (huniq : LogarithmicWindowDegreeUnique S ε)
    (hrem : LogarithmicWindowOrderedRemainderBound S ε C) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
        (largePrimePositiveStarOrderedIndex a
            (sqrtCutoff_condition X) haY hd).1 + 1 =
            arithmeticCenterRank a ∧
          |(arithmeticStarFullEigenvalue a haY hd ^ 2 -
              (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            fixedCenterActualCorrection S (a : ℕ) X| < δ := by
  intro δ hδ
  by_cases hCzero : C = 0
  · filter_upwards [huniq, hrem] with X huniqX hremX
    intro a ha
    obtain ⟨haY, hd, hbound⟩ := hremX a ha
    refine ⟨haY, hd, ?_, ?_⟩
    · have hrank := largePrimePositiveStarOrderedIndex_val_eq_arithmeticRank
        hS a (sqrtCutoff_condition X) haY hd (huniqX a ha)
      simpa [arithmeticCenterRank] using congrArg (fun n : ℕ ↦ n + 1) hrank
    · have hzero :
          |(arithmeticStarFullEigenvalue a haY hd ^ 2 -
              (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            fixedCenterActualCorrection S (a : ℕ) X| ≤ 0 := by
        simpa [hCzero] using hbound
      exact hzero.trans_lt hδ
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hsmall := eventually_center_sq_div_log_lt_on_logarithmicWindow
      hε (div_pos hδ hCpos)
    filter_upwards [huniq, hrem, hsmall] with X huniqX hremX hsmallX
    intro a ha
    obtain ⟨haY, hd, hbound⟩ := hremX a ha
    refine ⟨haY, hd, ?_, ?_⟩
    · have hrank := largePrimePositiveStarOrderedIndex_val_eq_arithmeticRank
        hS a (sqrtCutoff_condition X) haY hd (huniqX a ha)
      simpa [arithmeticCenterRank] using congrArg (fun n : ℕ ↦ n + 1) hrank
    · calc
        |(arithmeticStarFullEigenvalue a haY hd ^ 2 -
              (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            fixedCenterActualCorrection S (a : ℕ) X| ≤
            C * ((a : ℝ) ^ 2 / Real.log (X : ℝ)) := hbound
        _ < C * (δ / C) :=
          mul_lt_mul_of_pos_left (hsmallX (a : ℕ) ha) hCpos
        _ = δ := by field_simp

/-- Theorem 9.6 at the prescribed ordered eigenvalue.  This is the
triangle-inequality assembly of Theorem 9.5 with uniform evaluation of the
actual finite correction. -/
theorem eventually_logarithmicWindow_ranked_constantLayer
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (huniq : LogarithmicWindowDegreeUnique S ε)
    (hrem : LogarithmicWindowOrderedRemainderBound S ε C)
    (hcorr : LogarithmicWindowCorrectionEvaluation S ε) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
        (largePrimePositiveStarOrderedIndex a
            (sqrtCutoff_condition X) haY hd).1 + 1 =
            arithmeticCenterRank a ∧
          |((arithmeticStarFullEigenvalue a haY hd ^ 2 -
                (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
              4 * Real.log (Real.log (X : ℝ))) -
            (4 * primeStarKappa meisselMertensConstant S +
              centerPrimeCorrection (a : ℕ))| < δ := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  have hspectral := eventually_logarithmicWindow_ranked_actualCorrection
    S hS hε hC huniq hrem (δ / 2) hhalf
  have harithmetic := hcorr (δ / 2) hhalf
  filter_upwards [hspectral, harithmetic] with X hspectralX harithmeticX
  intro a ha
  obtain ⟨haY, hd, hrank, hspectralBound⟩ := hspectralX a ha
  refine ⟨haY, hd, hrank, ?_⟩
  have harithmeticBound := harithmeticX a ha
  calc
    |((arithmeticStarFullEigenvalue a haY hd ^ 2 -
          (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
        4 * Real.log (Real.log (X : ℝ))) -
      (4 * primeStarKappa meisselMertensConstant S +
        centerPrimeCorrection (a : ℕ))| =
      |((arithmeticStarFullEigenvalue a haY hd ^ 2 -
            (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
          fixedCenterActualCorrection S (a : ℕ) X) +
        ((fixedCenterActualCorrection S (a : ℕ) X -
            4 * Real.log (Real.log (X : ℝ))) -
          (4 * primeStarKappa meisselMertensConstant S +
            centerPrimeCorrection (a : ℕ)))| := by ring
    _ ≤ |(arithmeticStarFullEigenvalue a haY hd ^ 2 -
            (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
          fixedCenterActualCorrection S (a : ℕ) X| +
        |(fixedCenterActualCorrection S (a : ℕ) X -
            4 * Real.log (Real.log (X : ℝ))) -
          (4 * primeStarKappa meisselMertensConstant S +
            centerPrimeCorrection (a : ℕ))| := abs_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add hspectralBound harithmeticBound
    _ = δ := by ring

/-- The ordered form of Theorem 9.5 after discharging moving degree
uniqueness by quantitative PNT. -/
theorem eventually_logarithmicWindow_ranked_actualCorrection_of_remainder
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hrem : LogarithmicWindowOrderedRemainderBound S ε C) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
        (largePrimePositiveStarOrderedIndex a
            (sqrtCutoff_condition X) haY hd).1 + 1 =
            arithmeticCenterRank a ∧
          |(arithmeticStarFullEigenvalue a haY hd ^ 2 -
              (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            fixedCenterActualCorrection S (a : ℕ) X| < δ :=
  eventually_logarithmicWindow_ranked_actualCorrection S hS hε hC
    (logarithmicWindowDegreeUnique S hS hε) hrem

/-- The ordered form of Theorem 9.6 after discharging moving degree
uniqueness by quantitative PNT. -/
theorem eventually_logarithmicWindow_ranked_constantLayer_of_remainder
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hrem : LogarithmicWindowOrderedRemainderBound S ε C)
    (hcorr : LogarithmicWindowCorrectionEvaluation S ε) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
        (largePrimePositiveStarOrderedIndex a
            (sqrtCutoff_condition X) haY hd).1 + 1 =
            arithmeticCenterRank a ∧
          |((arithmeticStarFullEigenvalue a haY hd ^ 2 -
                (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
              4 * Real.log (Real.log (X : ℝ))) -
            (4 * primeStarKappa meisselMertensConstant S +
              centerPrimeCorrection (a : ℕ))| < δ :=
  eventually_logarithmicWindow_ranked_constantLayer S hS hε hC
    (logarithmicWindowDegreeUnique S hS hε) hrem hcorr

end

end PrimeStar
