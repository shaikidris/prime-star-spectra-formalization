import PrimeStar.CanonicalFirstExitBlocks
import PrimeStar.DegreeIsolation
import PrimeStar.SqrtResidual

/-!
# Degree gaps and coordinate compressions

This file is the finite transfer layer between isolation of one large-prime
star and the coordinate-compressed gaps used by the Feshbach argument.  The
generic lemma below records the only functional-analytic point: a coordinate
subspace that is invariant under the reference operator inherits its gap,
up to the perturbation norm.  No prime-counting asymptotic is used here.
-/

namespace PrimeStar

open Filter
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

local instance feshbachDegreeGapPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) : DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

local instance feshbachDegreeGapLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) : DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance feshbachDegreeGapSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) : DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

set_option maxHeartbeats 1200000

/-- A Euclidean adjacency operator is pointwise bounded by the matrix
`L²`-operator norm used by the Schur estimates. -/
theorem norm_toEuclideanLin_apply_le_matrixNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M x‖ ≤ ‖M‖ * ‖x‖
  exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M).le_opNorm x

/-- Pointwise residual-norm form of the literal square-root-cutoff Schur
bound.  This is the `eta` input consumed by the degree-gap wrappers. -/
theorem eventually_sqrtCutoff_smallPrime_apply_le_tuned :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ (S : Finset ℕ)
      (x : EuclideanSpace ℝ (Vertex S X)),
      ‖Matrix.toEuclideanLin
          ((smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ) x‖ ≤
        ((12 * Real.log 4 + 2 / Real.log 2 + 16) *
          tunedSchurScale ((Nat.sqrt X + 1 : ℕ) : ℝ)) * ‖x‖ := by
  filter_upwards [eventually_sqrtCutoff_smallPrimeGraph_l2_opNorm_le_tuned]
    with X hX
  intro S x
  exact (norm_toEuclideanLin_apply_le_matrixNorm
    ((smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ) x).trans
      (mul_le_mul_of_nonneg_right (hX S) (norm_nonneg x))

/-- Exact finite Chebyshev lower certificate for one large-prime star degree.
It pays only the finite deletion and the lower cutoff boundary. -/
theorem chebyshevLower_sub_boundary_le_largePrimeStarDegree
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hS : ∀ p ∈ S, p.Prime) (hc : (c : ℕ) ≤ Y)
    (hYXc : Y ≤ X / (c : ℕ)) :
    (((X / (c : ℕ) : ℕ) : ℝ) * Real.log 2 -
          Real.log ((X / (c : ℕ) : ℕ) + 1)) /
          Real.log (X / (c : ℕ) : ℕ) -
        (S.card : ℝ) - (allowedPrimeCount S Y : ℝ) ≤
      (largePrimeStarDegree S X Y c : ℝ) := by
  let N := X / (c : ℕ)
  have hallowedLe : allowedPrimeCount S N ≤ Nat.primeCounting N :=
    allowedPrimeCount_le_primeCounting S N
  have hdeleted : Nat.primeCounting N - allowedPrimeCount S N ≤ S.card :=
    primeCounting_sub_allowedPrimeCount_le_card S N
  have hallowedLower :
      (Nat.primeCounting N : ℝ) - (S.card : ℝ) ≤
        (allowedPrimeCount S N : ℝ) := by
    have hcast : ((Nat.primeCounting N - allowedPrimeCount S N : ℕ) : ℝ) ≤
        (S.card : ℝ) := by exact_mod_cast hdeleted
    rw [Nat.cast_sub hallowedLe] at hcast
    linarith
  have hcheb :
      ((N : ℝ) * Real.log 2 - Real.log (N + 1)) / Real.log N ≤
        (Nat.primeCounting N : ℝ) := Chebyshev.pi_ge N
  have hcount := allowedPrimeCount_mono (S := S) hYXc
  have hdegree : (largePrimeStarDegree S X Y c : ℝ) =
      (allowedPrimeCount S N : ℝ) - (allowedPrimeCount S Y : ℝ) := by
    rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS c hc hYXc,
      Nat.cast_sub hcount]
  dsimp [N] at hallowedLower hcheb hdegree ⊢
  rw [hdegree]
  linarith

/-- Square-root form of the finite Chebyshev certificate.  Positivity of its
left side is a purely real-analytic eventual estimate; no PNT is needed. -/
theorem sqrt_chebyshevLower_sub_boundary_le_sqrt_largePrimeStarDegree
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hS : ∀ p ∈ S, p.Prime) (hc : (c : ℕ) ≤ Y)
    (hYXc : Y ≤ X / (c : ℕ)) :
    Real.sqrt
        ((((X / (c : ℕ) : ℕ) : ℝ) * Real.log 2 -
              Real.log ((X / (c : ℕ) : ℕ) + 1)) /
              Real.log (X / (c : ℕ) : ℕ) -
            (S.card : ℝ) - (allowedPrimeCount S Y : ℝ)) ≤
      Real.sqrt (largePrimeStarDegree S X Y c : ℝ) := by
  exact Real.sqrt_le_sqrt
    (chebyshevLower_sub_boundary_le_largePrimeStarDegree c hS hc hYXc)

/-- A coordinate compression of an invariant reference subspace inherits a
two-sided gap.  The factor `1 / 2` is a harmless consequence of estimating the
range and kernel coordinates separately; it avoids any hidden spectral
theorem in this wiring lemma. -/
theorem coordinateCompression_gap_of_invariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι)
    (L H : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (mu gamma eta : ℝ)
    (hgamma : 0 ≤ gamma) (heta : 0 ≤ eta)
    (hinvariant : ∀ x,
      euclideanCoordinateProjection F
          (L (euclideanCoordinateProjection F x)) =
        L (euclideanCoordinateProjection F x))
    (hgap : ∀ x,
      gamma * ‖euclideanCoordinateProjection F x‖ ≤
        ‖mu • euclideanCoordinateProjection F x -
          L (euclideanCoordinateProjection F x)‖)
    (hH : ∀ x, ‖H x‖ ≤ eta * ‖x‖)
    (x : EuclideanSpace ℝ ι) :
    (min gamma |mu| / 2 - eta) * ‖x‖ ≤
      ‖mu • x -
        euclideanCoordinateProjection F
          ((L + H) (euclideanCoordinateProjection F x))‖ := by
  let P := euclideanCoordinateProjection F
  let Q := euclideanCoordinateComplementProjection F
  let y := P x
  let z := Q x
  let r := mu • x - P (L y)
  let s := mu • x - P ((L + H) y)
  have hPy : P y = y := by
    dsimp [P, y]
    exact euclideanCoordinateProjection_idem F x
  have hQz : Q z = z := by
    dsimp [Q, z]
    exact euclideanCoordinateComplementProjection_idem F x
  have hPz : P z = 0 := by
    ext i
    by_cases hi : i ∈ F <;> simp [P, z, Q, hi]
  have hQy : Q y = 0 := by
    ext i
    by_cases hi : i ∈ F <;> simp [P, y, Q, hi]
  have hxy : y + z = x := by
    dsimp [y, z, P, Q]
    exact euclideanCoordinateProjection_add_complement F x
  have hPLy : P (L y) = L y := by
    simpa [P, y] using hinvariant x
  have hPr : P r = mu • y - L y := by
    dsimp [r]
    rw [map_sub, map_smul]
    change mu • P x - P (P (L y)) = mu • y - L y
    rw [show P x = y by rfl]
    have hPP : P (P (L y)) = P (L y) := by
      dsimp [P]
      exact euclideanCoordinateProjection_idem F (L y)
    rw [hPP, hPLy]
  have hQr : Q r = mu • z := by
    dsimp [r]
    rw [map_sub, map_smul]
    change mu • Q x - Q (P (L y)) = mu • z
    rw [show Q x = z by rfl]
    have hQP : Q (P (L y)) = 0 := by
      ext i
      by_cases hi : i ∈ F <;> simp [P, Q, hi]
    rw [hQP, sub_zero]
  have hy : gamma * ‖y‖ ≤ ‖r‖ := by
    calc
      gamma * ‖y‖ ≤ ‖mu • y - L y‖ := by simpa [y, P] using hgap x
      _ = ‖P r‖ := by rw [hPr]
      _ ≤ ‖r‖ := norm_euclideanCoordinateProjection_le F r
  have hz : |mu| * ‖z‖ ≤ ‖r‖ := by
    calc
      |mu| * ‖z‖ = ‖mu • z‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖Q r‖ := by rw [hQr]
      _ ≤ ‖r‖ := norm_euclideanCoordinateComplementProjection_le F r
  have hminGamma : min gamma |mu| * ‖y‖ ≤ ‖r‖ := by
    exact (mul_le_mul_of_nonneg_right (min_le_left gamma |mu|)
      (norm_nonneg y)).trans hy
  have hminMu : min gamma |mu| * ‖z‖ ≤ ‖r‖ := by
    exact (mul_le_mul_of_nonneg_right (min_le_right gamma |mu|)
      (norm_nonneg z)).trans hz
  have hmin0 : 0 ≤ min gamma |mu| := le_min hgamma (abs_nonneg mu)
  have href : (min gamma |mu| / 2) * ‖x‖ ≤ ‖r‖ := by
    have hxnorm : ‖x‖ ≤ ‖y‖ + ‖z‖ := by
      rw [← hxy]
      exact norm_add_le y z
    have hsum : min gamma |mu| * (‖y‖ + ‖z‖) ≤ 2 * ‖r‖ := by
      rw [mul_add]
      linarith
    have hscaled : min gamma |mu| * ‖x‖ ≤ 2 * ‖r‖ :=
      (mul_le_mul_of_nonneg_left hxnorm hmin0).trans hsum
    linarith
  have hrs : r = s + P (H y) := by
    dsimp [r, s]
    rw [map_add]
    abel
  have hpert : ‖P (H y)‖ ≤ eta * ‖x‖ := by
    calc
      ‖P (H y)‖ ≤ ‖H y‖ := by
        dsimp [P]
        exact norm_euclideanCoordinateProjection_le F (H y)
      _ ≤ eta * ‖y‖ := hH y
      _ ≤ eta * ‖x‖ := mul_le_mul_of_nonneg_left
        (by
          dsimp [y, P]
          exact norm_euclideanCoordinateProjection_le F x) heta
  have hrupper : ‖r‖ ≤ ‖s‖ + eta * ‖x‖ := by
    rw [hrs]
    exact (norm_add_le s (P (H y))).trans (add_le_add_right hpert ‖s‖)
  change (min gamma |mu| / 2 - eta) * ‖x‖ ≤ ‖s‖
  nlinarith [norm_nonneg x]

/-- A finite coordinate set is closed under the large-prime star forest. -/
def LargePrimeClosed
    {S : Finset ℕ} {X Y : ℕ} (F : Finset (Vertex S X)) : Prop :=
  ∀ ⦃v w : Vertex S X⦄, v ∈ F → LargePrimeAdj S Y v w → w ∈ F

/-- Large-prime adjacency preserves vectors supported on any closed coordinate
set.  This is the graph-theoretic input required by
`coordinateCompression_gap_of_invariant`. -/
theorem largePrime_toEuclideanLin_preserves_closedSupport
    {S : Finset ℕ} {X Y : ℕ} {F : Finset (Vertex S X)}
    (hF : LargePrimeClosed (S := S) (X := X) (Y := Y) F)
    (x : EuclideanSpace ℝ (Vertex S X))
    (hx : ∀ v, v ∉ F → x v = 0) {v : Vertex S X} (hv : v ∉ F) :
    Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x v = 0 := by
  rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
  change ((largePrimeGraph S X Y).adjMatrix ℝ).mulVec
      (fun w ↦ x w) v = 0
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  apply Finset.sum_eq_zero
  intro w hw
  have hvw : LargePrimeAdj S Y v w := by simpa using hw
  have hwout : w ∉ F := by
    intro hwF
    exact hv (hF hwF (largePrimeAdj_symm hvw))
  exact hx w hwout

/-- The coordinate projection onto a closed union of large-prime components
commutes with the reference adjacency on its range. -/
theorem largePrime_coordinateProjection_invariant
    {S : Finset ℕ} {X Y : ℕ} {F : Finset (Vertex S X)}
    (hF : LargePrimeClosed (S := S) (X := X) (Y := Y) F)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    euclideanCoordinateProjection F
        (Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
          (euclideanCoordinateProjection F x)) =
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (euclideanCoordinateProjection F x) := by
  ext v
  by_cases hv : v ∈ F
  · simp [euclideanCoordinateProjection_apply, hv]
  · rw [euclideanCoordinateProjection_apply, if_neg hv]
    exact (largePrime_toEuclideanLin_preserves_closedSupport hF _
      (fun w hw ↦ by simp [euclideanCoordinateProjection_apply, hw]) hv).symm

/-- Degree isolation and a residual norm imply a literal gap for the
large-prime reference operator.  The two copies of `eta` pay first for the
full prime-cover perturbation and then for returning to the reference
operator. -/
theorem largePrime_complementGap_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X))
    (hx : ⟪largePrimeNormalizedStarMode S X Y c 1, x⟫_ℝ = 0) :
    (gamma - 2 * eta) * ‖x‖ ≤
      ‖√(largePrimeStarDegree S X Y c : ℝ) • x -
        Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x‖ := by
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  have hfull := primeCover_shiftedComplementGap_arithmeticStar_of_degreeGap
    c hcut hc hd gamma eta mu hgamma hzeroGap hdegree hH x hx
  have hsplit : A = L + H := by
    exact primeCover_toEuclideanLin_eq_large_add_small S X Y
  have hupper : ‖A x - mu • x‖ ≤ ‖mu • x - L x‖ + eta * ‖x‖ := by
    rw [hsplit, LinearMap.add_apply]
    calc
      ‖L x + H x - mu • x‖ = ‖-(mu • x - L x) + H x‖ := by
        congr 1
        module
      _ ≤ ‖-(mu • x - L x)‖ + ‖H x‖ := norm_add_le _ _
      _ ≤ ‖mu • x - L x‖ + eta * ‖x‖ := by
        rw [norm_neg]
        gcongr
        exact hH x
  dsimp [mu, A, L, H] at hfull hupper ⊢
  rw [sub_self, abs_zero, sub_zero] at hfull
  linarith

/-- The canonical first-exit large-prime compression inherits the arithmetic
degree gap.  This discharges the `hgapU` premise of the finite Feshbach
wrapper, up to an explicit harmless loss in the constant. -/
theorem firstExitLargePrimeCompression_gap_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma) (hgammaEta : 0 ≤ gamma - 2 * eta)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    (min (gamma - 2 * eta)
        |√(largePrimeStarDegree S X Y c : ℝ)| / 2) * ‖x‖ ≤
      ‖√(largePrimeStarDegree S X Y c : ℝ) • x -
        firstExitLargePrimeCompressionOperator S X Y c x‖ := by
  let F := firstExitCompressionSupport S X Y c
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let P := euclideanCoordinateProjection F
  have hclosed : LargePrimeClosed (S := S) (X := X) (Y := Y) F := by
    intro v w hv hvw
    exact firstExitCompressionSupport_closed_under_largePrimeAdj hcut hv hvw
  have horth (z : EuclideanSpace ℝ (Vertex S X)) :
      ⟪largePrimeNormalizedStarMode S X Y c 1, P z⟫_ℝ = 0 := by
    let PB := primeStarBoundaryProjection S X Y c
    have hPB : PB.IsSymmetric :=
      euclideanCoordinateProjection_isSymmetric
        (largePrimeStarSupport S X Y c)
    calc
      ⟪largePrimeNormalizedStarMode S X Y c 1, P z⟫_ℝ =
          ⟪PB (largePrimeNormalizedStarMode S X Y c 1), P z⟫_ℝ := by
            rw [primeStarBoundaryProjection_normalizedStarMode]
      _ = ⟪largePrimeNormalizedStarMode S X Y c 1, PB (P z)⟫_ℝ := hPB _ _
      _ = 0 := by
        have hreverse := primeStarBoundaryProjection_firstExit_eq_zero
          (S := S) (X := X) (Y := Y) (c := c) hcut hc z
        have hzero : PB (P z) = 0 := by
          simpa [PB, P, F, firstExitCompressionProjection] using hreverse
        rw [hzero, inner_zero_right]
  have hgap (z : EuclideanSpace ℝ (Vertex S X)) :
      (gamma - 2 * eta) * ‖P z‖ ≤
        ‖√(largePrimeStarDegree S X Y c : ℝ) • P z - L (P z)‖ := by
    exact largePrime_complementGap_of_degreeGap c hcut hc hd gamma eta hgamma
      hzeroGap hdegree hH (P z) (horth z)
  have hzero : ∀ z : EuclideanSpace ℝ (Vertex S X), ‖(0 :
      EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ] EuclideanSpace ℝ (Vertex S X)) z‖ ≤
        0 * ‖z‖ := by simp
  have hresult := coordinateCompression_gap_of_invariant F L 0
    (√(largePrimeStarDegree S X Y c : ℝ)) (gamma - 2 * eta) 0
    hgammaEta (le_refl 0)
    (largePrime_coordinateProjection_invariant hclosed) hgap hzero x
  simpa [F, L, P, firstExitLargePrimeCompressionOperator,
    firstExitCompressionProjection] using hresult

/-- A vector supported on coordinates disjoint from the target star is
orthogonal to its normalized star mode. -/
theorem inner_normalizedStar_coordinateProjection_eq_zero_of_disjoint
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    {F : Finset (Vertex S X)}
    (hdisj : Disjoint (largePrimeStarSupport S X Y c) F)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    ⟪largePrimeNormalizedStarMode S X Y c 1,
      euclideanCoordinateProjection F x⟫_ℝ = 0 := by
  let PB := primeStarBoundaryProjection S X Y c
  let P := euclideanCoordinateProjection F
  have hPB : PB.IsSymmetric :=
    euclideanCoordinateProjection_isSymmetric
      (largePrimeStarSupport S X Y c)
  calc
    ⟪largePrimeNormalizedStarMode S X Y c 1, P x⟫_ℝ =
        ⟪PB (largePrimeNormalizedStarMode S X Y c 1), P x⟫_ℝ := by
          rw [primeStarBoundaryProjection_normalizedStarMode]
    _ = ⟪largePrimeNormalizedStarMode S X Y c 1, PB (P x)⟫_ℝ := hPB _ _
    _ = 0 := by
      have hz := euclideanCoordinateProjection_comp_eq_zero_of_disjoint
        hdisj x
      have hzero : PB (P x) = 0 := by
        simpa [PB, P, primeStarBoundaryProjection] using hz
      rw [hzero, inner_zero_right]

/-- Removing one closed large-prime star leaves another closed union of
large-prime components. -/
theorem largePrimeStarComplement_closed
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y) :
    LargePrimeClosed (S := S) (X := X) (Y := Y)
      (Finset.univ \ largePrimeStarSupport S X Y c) := by
  intro v w hv hvw
  rw [Finset.mem_sdiff] at hv ⊢
  refine ⟨Finset.mem_univ w, ?_⟩
  intro hwB
  have hvB := largePrimeStarSupport_closed hcut hc hwB
    (largePrimeAdj_symm hvw)
  exact hv.2 hvB

/-- The remaining `W` coordinates are a union of complete large-prime
components. -/
theorem firstExitComplementSupport_closed
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y) :
    LargePrimeClosed (S := S) (X := X) (Y := Y)
      (firstExitComplementSupport S X Y c) := by
  intro v w hv hvw
  rw [firstExitComplementSupport, Finset.mem_sdiff] at hv ⊢
  refine ⟨Finset.mem_univ w, ?_⟩
  intro hwUnion
  rcases Finset.mem_union.mp hwUnion with hwB | hwU
  · have hvB := largePrimeStarSupport_closed hcut hc hwB
      (largePrimeAdj_symm hvw)
    exact hv.2 (Finset.mem_union_left _ hvB)
  · have hvU := firstExitCompressionSupport_closed_under_largePrimeAdj
      hcut hwU (largePrimeAdj_symm hvw)
    exact hv.2 (Finset.mem_union_right _ hvU)

/-- The coordinate complement of a star support is the interior projection
used in the Feshbach split. -/
theorem coordinateProjection_starComplement_eq_interior
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} :
    euclideanCoordinateProjection
        (Finset.univ \ largePrimeStarSupport S X Y c) =
      primeStarInteriorProjection S X Y c := by
  apply LinearMap.ext
  intro x
  ext v
  by_cases hv : v ∈ largePrimeStarSupport S X Y c <;>
    simp [primeStarInteriorProjection, hv]

/-- The interior prime-cover compression inherits the same arithmetic
degree gap, after paying the residual norm once more. -/
theorem primeStarInterior_gap_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma) (hgammaEta : 0 ≤ gamma - 2 * eta)
    (heta : 0 ≤ eta)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    (min (gamma - 2 * eta)
          |√(largePrimeStarDegree S X Y c : ℝ)| / 2 - eta) * ‖x‖ ≤
      ‖√(largePrimeStarDegree S X Y c : ℝ) • x -
        primeStarInteriorPrimeCoverOperator S X Y c x‖ := by
  let F := Finset.univ \ largePrimeStarSupport S X Y c
  let P := euclideanCoordinateProjection F
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hclosed : LargePrimeClosed (S := S) (X := X) (Y := Y) F := by
    exact largePrimeStarComplement_closed hcut hc
  have hgap (z : EuclideanSpace ℝ (Vertex S X)) :
      (gamma - 2 * eta) * ‖P z‖ ≤
        ‖√(largePrimeStarDegree S X Y c : ℝ) • P z - L (P z)‖ := by
    apply largePrime_complementGap_of_degreeGap c hcut hc hd gamma eta hgamma
      hzeroGap hdegree hH
    apply inner_normalizedStar_coordinateProjection_eq_zero_of_disjoint
    rw [Finset.disjoint_left]
    intro v hvB hvF
    exact (Finset.mem_sdiff.mp hvF).2 hvB
  have hresult := coordinateCompression_gap_of_invariant F L H
    (√(largePrimeStarDegree S X Y c : ℝ)) (gamma - 2 * eta) eta
    hgammaEta heta (largePrime_coordinateProjection_invariant hclosed)
    hgap hH x
  have hP : P = primeStarInteriorProjection S X Y c := by
    exact coordinateProjection_starComplement_eq_interior
  have hsplit : L + H =
      Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) := by
    exact (primeCover_toEuclideanLin_eq_large_add_small S X Y).symm
  simpa [P, F, hP, L, H, hsplit, primeStarInteriorPrimeCoverOperator] using hresult

/-- The `W`-block of the first-exit Feshbach decomposition inherits the same
degree gap and residual-norm loss. -/
theorem firstExitComplement_gap_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma) (hgammaEta : 0 ≤ gamma - 2 * eta)
    (heta : 0 ≤ eta)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    (min (gamma - 2 * eta)
          |√(largePrimeStarDegree S X Y c : ℝ)| / 2 - eta) * ‖x‖ ≤
      ‖√(largePrimeStarDegree S X Y c : ℝ) • x -
        firstExitComplementPrimeCoverOperator S X Y c x‖ := by
  let F := firstExitComplementSupport S X Y c
  let P := euclideanCoordinateProjection F
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hclosed : LargePrimeClosed (S := S) (X := X) (Y := Y) F := by
    exact firstExitComplementSupport_closed hcut hc
  have hgap (z : EuclideanSpace ℝ (Vertex S X)) :
      (gamma - 2 * eta) * ‖P z‖ ≤
        ‖√(largePrimeStarDegree S X Y c : ℝ) • P z - L (P z)‖ := by
    apply largePrime_complementGap_of_degreeGap c hcut hc hd gamma eta hgamma
      hzeroGap hdegree hH
    exact inner_normalizedStar_coordinateProjection_eq_zero_of_disjoint
      disjoint_boundary_firstExitComplementSupport z
  have hresult := coordinateCompression_gap_of_invariant F L H
    (√(largePrimeStarDegree S X Y c : ℝ)) (gamma - 2 * eta) eta
    hgammaEta heta (largePrime_coordinateProjection_invariant hclosed)
    hgap hH x
  have hsplit : L + H =
      Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) := by
    exact (primeCover_toEuclideanLin_eq_large_add_small S X Y).symm
  simpa [F, P, L, H, hsplit, firstExitComplementPrimeCoverOperator,
    firstExitComplementProjection] using hresult

/-- The residual small-prime adjacency has zero compression to one closed
large-prime star. -/
theorem primeStarBoundaryProjection_smallPrime_eq_zero_of_supported
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X))
    (hx : primeStarBoundaryProjection S X Y c x = x) :
    primeStarBoundaryProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x) = 0 := by
  ext v
  by_cases hvB : v ∈ largePrimeStarSupport S X Y c
  · simp only [primeStarBoundaryProjection_apply, if_pos hvB]
    rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
    change ((smallPrimeGraph S X Y).adjMatrix ℝ).mulVec
      (fun w ↦ x w) v = 0
    rw [Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro w _hw
    by_cases hwB : w ∈ largePrimeStarSupport S X Y c
    · have hnot := not_smallPrimeGraph_adj_on_largePrimeStarSupport hc hvB hwB
      rw [SimpleGraph.adjMatrix_apply, if_neg hnot, zero_mul]
    · have hxw := congrFun (congrArg WithLp.ofLp hx) w
      simp [primeStarBoundaryProjection_apply, hwB] at hxw
      rw [← hxw]
      simp
  · simp [primeStarBoundaryProjection_apply, hvB]

/-- On a vector supported in the target star, the boundary prime-cover block
is exactly the large-prime adjacency. -/
theorem primeStarBoundaryPrimeCoverOperator_eq_largePrime_of_supported
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X))
    (hx : primeStarBoundaryProjection S X Y c x = x) :
    primeStarBoundaryPrimeCoverOperator S X Y c x =
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x := by
  let PB := primeStarBoundaryProjection S X Y c
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hclosed : LargePrimeClosed (S := S) (X := X) (Y := Y)
      (largePrimeStarSupport S X Y c) := by
    intro v w hv hvw
    exact largePrimeStarSupport_closed hcut hc hv hvw
  have hPL : PB (L x) = L x := by
    have hinv := largePrime_coordinateProjection_invariant hclosed x
    change PB (L (PB x)) = L (PB x) at hinv
    rw [hx] at hinv
    exact hinv
  have hPH : PB (H x) = 0 := by
    exact primeStarBoundaryProjection_smallPrime_eq_zero_of_supported hc x hx
  change PB (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
      (PB x)) = L x
  rw [primeCover_toEuclideanLin_eq_large_add_small, hx,
    LinearMap.add_apply, map_add, hPL, hPH, add_zero]

/-- The normalized boundary remainder is orthogonal to the positive target
star mode. -/
theorem inner_normalizedPrimeStarBoundaryRemainder_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hd : 0 < largePrimeStarDegree S X Y c)
    (v : EuclideanSpace ℝ (Vertex S X))
    (halpha : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0) :
    ⟪largePrimeNormalizedStarMode S X Y c 1,
      normalizedPrimeStarBoundaryRemainder S X Y c v⟫_ℝ = 0 := by
  let u := largePrimeNormalizedStarMode S X Y c 1
  let alpha := ⟪u, v⟫_ℝ
  let PB := primeStarBoundaryProjection S X Y c
  have hPB : PB.IsSymmetric :=
    euclideanCoordinateProjection_isSymmetric
      (largePrimeStarSupport S X Y c)
  have hPBu : PB u = u := primeStarBoundaryProjection_normalizedStarMode
  have huu : ⟪u, u⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_largePrimeNormalizedStarMode hd]
    norm_num
  change ⟪u, PB (alpha⁻¹ • v) - u⟫_ℝ = 0
  rw [inner_sub_right]
  have hfirst : ⟪u, PB (alpha⁻¹ • v)⟫_ℝ = 1 := by
    calc
      ⟪u, PB (alpha⁻¹ • v)⟫_ℝ = ⟪PB u, alpha⁻¹ • v⟫_ℝ := (hPB u _).symm
      _ = ⟪u, alpha⁻¹ • v⟫_ℝ := by rw [hPBu]
      _ = alpha⁻¹ * alpha := by rw [real_inner_smul_right]
      _ = 1 := inv_mul_cancel₀ halpha
  rw [hfirst, huu, sub_self]

/-- The boundary gap consumed by Lemma 8.4 follows from the same degree-gap
family, residual norm, and actual eigenvalue displacement. -/
theorem primeStarBoundary_gap_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta lam : ℝ) (hgamma : 0 ≤ gamma)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (v : EuclideanSpace ℝ (Vertex S X))
    (halpha : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0) :
    (gamma - 2 * eta -
        |lam - √(largePrimeStarDegree S X Y c : ℝ)|) *
        ‖normalizedPrimeStarBoundaryRemainder S X Y c v‖ ≤
      ‖lam • normalizedPrimeStarBoundaryRemainder S X Y c v -
        primeStarBoundaryPrimeCoverOperator S X Y c
          (normalizedPrimeStarBoundaryRemainder S X Y c v)‖ := by
  let xB := normalizedPrimeStarBoundaryRemainder S X Y c v
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  have hxB : primeStarBoundaryProjection S X Y c xB = xB :=
    primeStarBoundaryProjection_normalizedBoundaryRemainder v
  have horth : ⟪largePrimeNormalizedStarMode S X Y c 1, xB⟫_ℝ = 0 :=
    inner_normalizedPrimeStarBoundaryRemainder_eq_zero hd v halpha
  have href := largePrime_complementGap_of_degreeGap c hcut hc hd gamma eta
    hgamma hzeroGap hdegree hH xB horth
  have hLB : primeStarBoundaryPrimeCoverOperator S X Y c xB = L xB :=
    primeStarBoundaryPrimeCoverOperator_eq_largePrime_of_supported hcut hc xB hxB
  have hupper : ‖mu • xB - L xB‖ ≤
      ‖lam • xB - primeStarBoundaryPrimeCoverOperator S X Y c xB‖ +
        |lam - mu| * ‖xB‖ := by
    rw [hLB]
    have hid : mu • xB - L xB =
        (lam • xB - L xB) + (mu - lam) • xB := by module
    rw [hid]
    calc
      ‖(lam • xB - L xB) + (mu - lam) • xB‖ ≤
          ‖lam • xB - L xB‖ + ‖(mu - lam) • xB‖ := norm_add_le _ _
      _ = ‖lam • xB - L xB‖ + |lam - mu| * ‖xB‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
  dsimp [xB, mu, L] at href hupper ⊢
  linarith

/-- Changing the spectral parameter costs exactly its scalar displacement in
any two-sided operator gap. -/
theorem shifted_gap_of_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E →ₗ[ℝ] E) (mu lam gamma : ℝ)
    (hgap : ∀ x : E, gamma * ‖x‖ ≤ ‖mu • x - C x‖)
    (x : E) :
    (gamma - |lam - mu|) * ‖x‖ ≤ ‖lam • x - C x‖ := by
  have hupper : ‖mu • x - C x‖ ≤
      ‖lam • x - C x‖ + |lam - mu| * ‖x‖ := by
    have hid : mu • x - C x =
        (lam • x - C x) + (mu - lam) • x := by module
    rw [hid]
    calc
      ‖(lam • x - C x) + (mu - lam) • x‖ ≤
          ‖lam • x - C x‖ + ‖(mu - lam) • x‖ := norm_add_le _ _
      _ = ‖lam • x - C x‖ + |lam - mu| * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
  linarith [hgap x]

/-- Degree isolation produces a concrete normalized prime-cover eigenvector
with nonzero target-star coordinate.  Thus the matched eigenpair and the
crude displacement bound are consequences, not additional hypotheses. -/
theorem primeCover_exists_simple_arithmeticStarEigenpair_withOverlap_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    ∃ (lam : ℝ) (v : EuclideanSpace ℝ (Vertex S X)),
      ‖v‖ = 1 ∧
      Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v ∧
      ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0 ∧
      |lam - √(largePrimeStarDegree S X Y c : ℝ)| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace
          (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)) lam) = 1 := by
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let i := largePrimePositiveStarOrderedIndex c hcut hc hd
  obtain ⟨hk, hsimple⟩ :=
    primeCover_simple_arithmeticStarEigenpair_of_degreeGap
      c hcut hc hd gamma eta hgamma hzeroGap hdegree hH hsmall
  let lam := (hL.add hHs).eigenvalues rfl i
  let v := (hL.add hHs).eigenvectorBasis rfl i
  have hvnorm : ‖v‖ = 1 :=
    (hL.add hHs).eigenvectorBasis rfl |>.orthonormal.norm_eq_one i
  have hLv : (L + H) v = lam • v := by
    exact (hL.add hHs).apply_eigenvectorBasis rfl i
  have hsplit : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) = L + H :=
    primeCover_toEuclideanLin_eq_large_add_small S X Y
  have hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v =
      lam • v := by simpa [hsplit] using hLv
  have hnear : |lam - √(largePrimeStarDegree S X Y c : ℝ)| ≤ eta := by
    simpa [lam, i, hL, hHs, L, H] using hk
  have hoverlap : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0 := by
    intro hzero
    have hgap := primeCover_shiftedComplementGap_arithmeticStar_of_degreeGap
      c hcut hc hd gamma eta lam hgamma hzeroGap hdegree hH v hzero
    rw [hAv, sub_self, norm_zero, hvnorm, mul_one] at hgap
    linarith
  have hsimple' : Module.finrank ℝ
      (Module.End.eigenspace
        (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)) lam) = 1 := by
    rw [hsplit]
    simpa [lam, i, hL, hHs, L, H] using hsimple
  exact ⟨lam, v, hvnorm, hAv, hoverlap, hnear, hsimple'⟩

/-- Prescribed-index version of
`primeCover_exists_simple_arithmeticStarEigenpair_withOverlap_of_degreeGap`.
The eigenvalue and eigenvector are the ordered spectral entries at the
large-prime star index selected by `c`. -/
theorem primeCover_ordered_arithmeticStarEigenpair_withOverlap_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
    let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    let i := largePrimePositiveStarOrderedIndex c hcut hc hd
    let lam := (hL.add hHs).eigenvalues rfl i
    let v := (hL.add hHs).eigenvectorBasis rfl i
    ‖v‖ = 1 ∧
      Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v ∧
      ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0 ∧
      |lam - √(largePrimeStarDegree S X Y c : ℝ)| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace
          (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)) lam) = 1 := by
  dsimp only
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let i := largePrimePositiveStarOrderedIndex c hcut hc hd
  let lam := (hL.add hHs).eigenvalues rfl i
  let v := (hL.add hHs).eigenvectorBasis rfl i
  obtain ⟨hnear, hsimple⟩ :=
    primeCover_simple_arithmeticStarEigenpair_of_degreeGap
      c hcut hc hd gamma eta hgamma hzeroGap hdegree hH hsmall
  have hvnorm : ‖v‖ = 1 :=
    (hL.add hHs).eigenvectorBasis rfl |>.orthonormal.norm_eq_one i
  have hLv : (L + H) v = lam • v :=
    (hL.add hHs).apply_eigenvectorBasis rfl i
  have hsplit : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) = L + H :=
    primeCover_toEuclideanLin_eq_large_add_small S X Y
  have hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v =
      lam • v := by simpa [hsplit] using hLv
  have hnear' : |lam - √(largePrimeStarDegree S X Y c : ℝ)| ≤ eta := by
    simpa [lam, i, hL, hHs, L, H] using hnear
  have hoverlap : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0 := by
    intro hzero
    have hgap := primeCover_shiftedComplementGap_arithmeticStar_of_degreeGap
      c hcut hc hd gamma eta lam hgamma hzeroGap hdegree hH v hzero
    rw [hAv, sub_self, norm_zero, hvnorm, mul_one] at hgap
    linarith
  have hsimple' : Module.finrank ℝ
      (Module.End.eigenspace
        (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)) lam) = 1 := by
    rw [hsplit]
    simpa [lam, i, hL, hHs, L, H] using hsimple
  exact ⟨hvnorm, hAv, hoverlap, hnear', hsimple'⟩

/-- Canonical finite remainder comparison with every Feshbach operator gap
derived from one arithmetic degree-gap family.  Compared with
`actualFinitePrimeStarRemainder_canonical`, this wrapper exposes no
`gammaB`, `gammaLam`, `gammaMu`, `gammaU`, or `gammaW` hypothesis.  The two
remaining scalar contraction inequalities and the matched eigenpair are
kept visible because their asymptotic instantiation is a separate step. -/
theorem actualFinitePrimeStarRemainder_canonical_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (v : EuclideanSpace ℝ (Vertex S X))
    (lam shiftBound gamma eta : ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (hlower : Y * Y ≤ X) (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hgamma : 0 ≤ gamma) (heta : 0 ≤ eta)
    (hgammaEta : 0 ≤ gamma - 2 * eta)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halphaMode : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hgapPos : 0 <
      min (gamma - 2 * eta)
          |√(largePrimeStarDegree S X Y c : ℝ)| / 2 - eta -
        |lam - √(largePrimeStarDegree S X Y c : ℝ)|)
    (hsmallBoundary :
      (gamma - 2 * eta -
          |lam - √(largePrimeStarDegree S X Y c : ℝ)|)⁻¹ * eta *
        (min (gamma - 2 * eta)
            |√(largePrimeStarDegree S X Y c : ℝ)| / 2 - eta -
          |lam - √(largePrimeStarDegree S X Y c : ℝ)|)⁻¹ * eta ≤ 1 / 2)
    (hsmallUW :
      (min (gamma - 2 * eta)
          |√(largePrimeStarDegree S X Y c : ℝ)| / 2)⁻¹ *
        (eta *
          (min (gamma - 2 * eta)
              |√(largePrimeStarDegree S X Y c : ℝ)| / 2 - eta)⁻¹ * eta) ≤
        1 / 2)
    (hshift :
      |lam - √(largePrimeStarDegree S X Y c : ℝ)| ≤ shiftBound)
    (hshift0 : 0 ≤ shiftBound) :
    let mu := √(largePrimeStarDegree S X Y c : ℝ)
    let gammaU := min (gamma - 2 * eta) |mu| / 2
    let gammaMu := gammaU - eta
    let gammaLam := gammaMu - |lam - mu|
    let gammaW := gammaMu
    let gammaB := gamma - 2 * eta - |lam - mu|
    let b := normalizedPrimeStarFirstExit S X Y c
    let Rlam := primeStarInteriorResolventOfGap
      S X Y c lam gammaLam (by
        dsimp [gammaLam, gammaMu, gammaU, mu]
        exact hgapPos)
        (fun x ↦ shifted_gap_of_gap
          (primeStarInteriorPrimeCoverOperator S X Y c) mu lam gammaMu
          (primeStarInterior_gap_of_degreeGap c hcut hc hd gamma eta hgamma
            hgammaEta heta hzeroGap hdegree hH) x)
    let Rmu := primeStarInteriorResolventOfGap
      S X Y c mu gammaMu (by
        dsimp [gammaMu, gammaU, mu]
        exact lt_of_lt_of_le hgapPos
          (sub_le_self _
            (abs_nonneg (lam - √(largePrimeStarDegree S X Y c : ℝ)))) )
        (primeStarInterior_gap_of_degreeGap c hcut hc hd gamma eta hgamma
          hgammaEta heta hzeroGap hdegree hH)
    let RU := firstExitLargePrimeResolventOfGap
      S X Y c mu gammaU (by
        dsimp [gammaU, mu]
        calc
          0 < min (gamma - 2 * eta)
                |√(largePrimeStarDegree S X Y c : ℝ)| / 2 - eta -
              |lam - √(largePrimeStarDegree S X Y c : ℝ)| := hgapPos
          _ ≤ min (gamma - 2 * eta)
                |√(largePrimeStarDegree S X Y c : ℝ)| / 2 := by
              linarith [heta,
                abs_nonneg (lam - √(largePrimeStarDegree S X Y c : ℝ))])
        (firstExitLargePrimeCompression_gap_of_degreeGap c hcut hc hd gamma eta
          hgamma hgammaEta hzeroGap hdegree hH)
    let errBound :=
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
        |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖ +
      2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2
    |(lam ^ 2 - (allowedPrimeCount S (X / (c : ℕ)) : ℝ)) -
      finiteStarCorrection
        (Finset.univ : Finset (CanonicalUpIndex S X Y c))
        (Finset.univ : Finset (CanonicalDownIndex c))
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ) /
          mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ) /
          mu ^ 2)| ≤
      2 * |mu| * errBound + shiftBound ^ 2 := by
  dsimp only
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let gammaU := min (gamma - 2 * eta) |mu| / 2
  let gammaMu := gammaU - eta
  let gammaLam := gammaMu - |lam - mu|
  let gammaW := gammaMu
  let gammaB := gamma - 2 * eta - |lam - mu|
  have hgammaLam : 0 < gammaLam := by simpa [gammaLam, gammaMu, gammaU, mu] using hgapPos
  have hgammaMu : 0 < gammaMu := lt_of_lt_of_le hgammaLam (by
    dsimp [gammaLam]
    linarith [abs_nonneg (lam - mu)])
  have hgammaW : 0 < gammaW := by simpa [gammaW] using hgammaMu
  have hgammaU : 0 < gammaU := lt_of_lt_of_le hgammaMu (by
    dsimp [gammaMu]
    linarith)
  have hgammaB : 0 < gammaB := by
    have hmin := min_le_left (gamma - 2 * eta) |mu|
    dsimp [gammaLam, gammaMu, gammaU, gammaB] at hgammaLam ⊢
    linarith
  have hgapMu : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaMu * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖ := by
    intro x
    simpa [gammaMu, gammaU, mu] using
      (primeStarInterior_gap_of_degreeGap c hcut hc hd gamma eta hgamma
        hgammaEta heta hzeroGap hdegree hH x)
  have hgapLam : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaLam * ‖x‖ ≤
        ‖lam • x - primeStarInteriorPrimeCoverOperator S X Y c x‖ := by
    intro x
    exact shifted_gap_of_gap
      (primeStarInteriorPrimeCoverOperator S X Y c) mu lam gammaMu hgapMu x
  have hgapU : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaU * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖ := by
    intro x
    simpa [gammaU, mu] using
      (firstExitLargePrimeCompression_gap_of_degreeGap c hcut hc hd gamma eta
        hgamma hgammaEta hzeroGap hdegree hH x)
  have hgapW : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaW * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖ := by
    intro x
    simpa [gammaW, gammaMu, gammaU, mu] using
      (firstExitComplement_gap_of_degreeGap c hcut hc hd gamma eta hgamma
        hgammaEta heta hzeroGap hdegree hH x)
  have hboundaryGap : gammaB *
        ‖normalizedPrimeStarBoundaryRemainder S X Y c v‖ ≤
      ‖lam • normalizedPrimeStarBoundaryRemainder S X Y c v -
        primeStarBoundaryPrimeCoverOperator S X Y c
          (normalizedPrimeStarBoundaryRemainder S X Y c v)‖ := by
    simpa [gammaB, mu] using
      (primeStarBoundary_gap_of_degreeGap c hcut hc hd gamma eta lam hgamma
        hzeroGap hdegree hH v halphaMode)
  have hresult := actualFinitePrimeStarRemainder_canonical
    v lam mu shiftBound gammaB gammaLam gammaMu gammaU gammaW eta
    hS hlower hcut hc hd rfl hAv halphaMode
    hgammaB hgammaLam hgammaMu hgammaU hgammaW heta
    hgapLam hgapMu hgapU hgapW hboundaryGap hH
    (by simpa [gammaB, gammaLam, gammaMu, gammaU, mu] using hsmallBoundary)
    (by simpa [gammaU, gammaW, gammaMu, mu] using hsmallUW)
    (by simpa [mu] using hshift) hshift0
  simpa [mu, gammaU, gammaMu, gammaLam, gammaW, gammaB] using hresult

end

end PrimeStar
