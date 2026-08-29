import PrimeStar.ActualFiniteCorrection
import PrimeStar.BoundaryReassembly
import PrimeStar.CoordinateFeshbach

/-!
# Assembly of the finite prime-star remainder

The earlier scalar remainder theorem exposed two hypotheses named `hdisp` and
`herr`.  This file derives both from the actual prime-cover eigenpair, a
reduced inverse action on the first-exit source, and the source-weighted
resolvent replacement of Lemma 8.6.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

local instance finiteRemainderLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance finiteRemainderSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance finiteRemainderPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- The normalized first-exit source attached to the positive star at `c`. -/
def normalizedPrimeStarFirstExit
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) :=
  Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
    (largePrimeNormalizedStarMode S X Y c 1)

/-- Normalization does not enlarge the coordinate support of a signed star
mode. -/
theorem largePrimeNormalizedStarMode_eq_zero_of_not_mem
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X} {eps : ℝ}
    (hv : v ∉ largePrimeStarSupport S X Y c) :
    largePrimeNormalizedStarMode S X Y c eps v = 0 := by
  rw [largePrimeNormalizedStarMode, NormedSpace.normalize]
  simp [largePrimeEuclideanStarVector,
    largePrimeSignedStarVector_eq_zero_of_not_mem hv]

/-- The normalized first-exit source vanishes outside its exact arithmetic
first-exit support. -/
theorem normalizedPrimeStarFirstExit_eq_zero_of_not_mem
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X}
    (hv : v ∉ smallPrimeFirstExitSupport S X Y c) :
    normalizedPrimeStarFirstExit S X Y c v = 0 := by
  rw [normalizedPrimeStarFirstExit, Matrix.toLpLin_toLp 2 2]
  exact smallPrime_mulVec_eq_zero_of_not_mem_firstExitSupport_of_supported
    (fun w ↦ largePrimeNormalizedStarMode S X Y c 1 w)
    (fun w hw ↦ largePrimeNormalizedStarMode_eq_zero_of_not_mem hw) hv

/-- At a first-exit coordinate, the normalized source equals the star-mode
coordinate at its unique residual neighbour in the original star. -/
theorem normalizedPrimeStarFirstExit_apply_eq_starMode_neighbor
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hw : w ∈ largePrimeStarSupport S X Y c)
    (hwv : (smallPrimeGraph S X Y).Adj w v) :
    normalizedPrimeStarFirstExit S X Y c v =
      largePrimeNormalizedStarMode S X Y c 1 w := by
  rw [normalizedPrimeStarFirstExit, Matrix.toLpLin_toLp 2 2]
  change ((smallPrimeGraph S X Y).adjMatrix ℝ).mulVec
      (fun z ↦ largePrimeNormalizedStarMode S X Y c 1 z) v = _
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  apply Finset.sum_eq_single w
  · intro z hz hzw
    by_cases hzStar : z ∈ largePrimeStarSupport S X Y c
    · have hzv : (smallPrimeGraph S X Y).Adj z v := by
        exact (smallPrimeGraph S X Y).adj_comm z v |>.mpr (by simpa using hz)
      have hEq := unique_smallPrime_neighbor_in_largePrimeStar
        hcut hc hzStar hw hzv hwv
      exact False.elim (hzw hEq)
    · exact largePrimeNormalizedStarMode_eq_zero_of_not_mem hzStar
  · intro hwNot
    exact False.elim (hwNot (by
      simpa using ((smallPrimeGraph S X Y).adj_comm v w |>.mpr hwv)))

/-- Every leaf coordinate of the positive normalized star mode is the centre
coordinate divided by the star eigenvalue. -/
theorem largePrimeNormalizedStarMode_leaf_eq_center_div_sqrt
    {S : Finset ℕ} {X Y : ℕ} {c w : Vertex S X}
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hw : w ∈ largePrimeLeaves S X Y c) :
    largePrimeNormalizedStarMode S X Y c 1 w =
      largePrimeNormalizedStarMode S X Y c 1 c /
        √(largePrimeStarDegree S X Y c : ℝ) := by
  let x := largePrimeEuclideanStarVector S X Y c 1
  have hsqrt0 : √(largePrimeStarDegree S X Y c : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  rw [largePrimeNormalizedStarMode, NormedSpace.normalize]
  change ‖x‖⁻¹ * largePrimeSignedStarVector S X Y c 1 w =
    (‖x‖⁻¹ * largePrimeSignedStarVector S X Y c 1 c) /
      √(largePrimeStarDegree S X Y c : ℝ)
  rw [largePrimeSignedStarVector_leaf hw,
    largePrimeSignedStarVector_center]
  field_simp [hsqrt0]

/-- The normalized first-exit source belongs to the canonical first-exit
coordinate compression.  This discharges the support premise of the literal
graph-level Feshbach theorem. -/
theorem firstExitCompressionProjection_normalizedPrimeStarFirstExit
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) :
    firstExitCompressionProjection S X Y c
        (normalizedPrimeStarFirstExit S X Y c) =
      normalizedPrimeStarFirstExit S X Y c := by
  ext v
  rw [firstExitCompressionProjection_apply]
  by_cases hv : v ∈ firstExitCompressionSupport S X Y c
  · simp [hv]
  · have hvExit : v ∉ smallPrimeFirstExitSupport S X Y c := by
      intro hvExit
      exact hv (smallPrimeFirstExitSupport_subset_firstExitCompressionSupport
        hcut hvExit)
    rw [if_neg hv, normalizedPrimeStarFirstExit_eq_zero_of_not_mem hvExit]

/-- The normalized signed star mode belongs to its closed-star coordinate
space. -/
theorem primeStarBoundaryProjection_normalizedStarMode
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {eps : ℝ} :
    primeStarBoundaryProjection S X Y c
        (largePrimeNormalizedStarMode S X Y c eps) =
      largePrimeNormalizedStarMode S X Y c eps := by
  ext v
  rw [primeStarBoundaryProjection_apply]
  by_cases hv : v ∈ largePrimeStarSupport S X Y c
  · simp [hv]
  · rw [if_neg hv, largePrimeNormalizedStarMode_eq_zero_of_not_mem hv]

@[simp]
theorem primeStarInteriorProjection_normalizedStarMode
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {eps : ℝ} :
    primeStarInteriorProjection S X Y c
        (largePrimeNormalizedStarMode S X Y c eps) = 0 := by
  ext v
  rw [primeStarInteriorProjection_apply]
  by_cases hv : v ∈ largePrimeStarSupport S X Y c
  · simp [hv]
  · rw [if_neg hv, largePrimeNormalizedStarMode_eq_zero_of_not_mem hv]
    simp

/-- The normalized first-exit source has no coordinate in the original
boundary star. -/
theorem primeStarBoundaryProjection_normalizedPrimeStarFirstExit
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y) :
    primeStarBoundaryProjection S X Y c
        (normalizedPrimeStarFirstExit S X Y c) = 0 := by
  rw [← firstExitCompressionProjection_normalizedPrimeStarFirstExit hcut]
  exact primeStarBoundaryProjection_firstExit_eq_zero hcut hc _

/-- Equivalently, the normalized first-exit source lies in the coordinate
interior of the original star. -/
theorem primeStarInteriorProjection_normalizedPrimeStarFirstExit
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y) :
    primeStarInteriorProjection S X Y c
        (normalizedPrimeStarFirstExit S X Y c) =
      normalizedPrimeStarFirstExit S X Y c :=
  primeStarInteriorProjection_eq_of_boundary_eq_zero
    (primeStarBoundaryProjection_normalizedPrimeStarFirstExit hcut hc)

/-- The literal boundary-to-interior source produced by the positive star
mode is exactly the normalized arithmetic first-exit vector. -/
theorem primeStarToInterior_normalizedStarMode_eq_firstExit
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y) :
    primeStarToInteriorPrimeCoverOperator S X Y c
        (largePrimeNormalizedStarMode S X Y c 1) =
      normalizedPrimeStarFirstExit S X Y c := by
  let u := largePrimeNormalizedStarMode S X Y c 1
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  let PI := primeStarInteriorProjection S X Y c
  change PI (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
    (primeStarBoundaryProjection S X Y c u)) = _
  rw [primeStarBoundaryProjection_normalizedStarMode]
  rw [primeCover_toEuclideanLin_eq_large_add_small]
  change PI (L u + H u) = _
  rw [map_add, largePrime_toEuclideanLin_normalizedStarMode
    hcut hc (by norm_num : (1 : ℝ) ^ 2 = 1)]
  rw [map_smul, primeStarInteriorProjection_normalizedStarMode, smul_zero,
    zero_add]
  exact primeStarInteriorProjection_normalizedPrimeStarFirstExit hcut hc

/-- Boundary-orthogonal component of an actual eigenvector after normalizing
its positive-star coordinate to one. -/
def normalizedPrimeStarBoundaryRemainder
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (v : EuclideanSpace ℝ (Vertex S X)) :
    EuclideanSpace ℝ (Vertex S X) :=
  let u := largePrimeNormalizedStarMode S X Y c 1
  let alpha := ⟪u, v⟫_ℝ
  primeStarBoundaryProjection S X Y c (alpha⁻¹ • v) - u

/-- Interior component of the same normalized actual eigenvector. -/
def normalizedPrimeStarInteriorRemainder
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (v : EuclideanSpace ℝ (Vertex S X)) :
    EuclideanSpace ℝ (Vertex S X) :=
  let u := largePrimeNormalizedStarMode S X Y c 1
  let alpha := ⟪u, v⟫_ℝ
  primeStarInteriorProjection S X Y c (alpha⁻¹ • v)

theorem primeStarBoundaryProjection_normalizedBoundaryRemainder
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (v : EuclideanSpace ℝ (Vertex S X)) :
    primeStarBoundaryProjection S X Y c
        (normalizedPrimeStarBoundaryRemainder S X Y c v) =
      normalizedPrimeStarBoundaryRemainder S X Y c v := by
  let u := largePrimeNormalizedStarMode S X Y c 1
  let alpha := ⟪u, v⟫_ℝ
  change primeStarBoundaryProjection S X Y c
      (primeStarBoundaryProjection S X Y c (alpha⁻¹ • v) - u) =
    primeStarBoundaryProjection S X Y c (alpha⁻¹ • v) - u
  rw [map_sub, primeStarBoundaryProjection_idem,
    primeStarBoundaryProjection_normalizedStarMode]

theorem primeStarInteriorProjection_normalizedInteriorRemainder
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (v : EuclideanSpace ℝ (Vertex S X)) :
    primeStarInteriorProjection S X Y c
        (normalizedPrimeStarInteriorRemainder S X Y c v) =
      normalizedPrimeStarInteriorRemainder S X Y c v := by
  let u := largePrimeNormalizedStarMode S X Y c 1
  let alpha := ⟪u, v⟫_ℝ
  change primeStarInteriorProjection S X Y c
      (primeStarInteriorProjection S X Y c (alpha⁻¹ • v)) =
    primeStarInteriorProjection S X Y c (alpha⁻¹ • v)
  exact euclideanCoordinateComplementProjection_idem _ _

/-- Exact boundary/interior decomposition of the star-normalized actual
eigenvector. -/
theorem normalizedPrimeStar_boundary_add_interior
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (v : EuclideanSpace ℝ (Vertex S X)) :
    let u := largePrimeNormalizedStarMode S X Y c 1
    let alpha := ⟪u, v⟫_ℝ
    alpha⁻¹ • v = u + normalizedPrimeStarBoundaryRemainder S X Y c v +
      normalizedPrimeStarInteriorRemainder S X Y c v := by
  dsimp only
  let y := (⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ)⁻¹ • v
  have hsplit := euclideanCoordinateProjection_add_complement
    (largePrimeStarSupport S X Y c) y
  change y = largePrimeNormalizedStarMode S X Y c 1 +
      (primeStarBoundaryProjection S X Y c y -
        largePrimeNormalizedStarMode S X Y c 1) +
      primeStarInteriorProjection S X Y c y
  calc
    y = primeStarBoundaryProjection S X Y c y +
        primeStarInteriorProjection S X Y c y := hsplit.symm
    _ = largePrimeNormalizedStarMode S X Y c 1 +
        (primeStarBoundaryProjection S X Y c y -
          largePrimeNormalizedStarMode S X Y c 1) +
        primeStarInteriorProjection S X Y c y := by abel

/-- Exact scalar equation with the actual coordinate-interior component. -/
theorem primeCover_schurEquation_at_interiorRemainder
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {lam mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (v : EuclideanSpace ℝ (Vertex S X))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halpha : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0) :
    lam - mu =
      ⟪normalizedPrimeStarFirstExit S X Y c,
        normalizedPrimeStarInteriorRemainder S X Y c v⟫_ℝ := by
  let u := largePrimeNormalizedStarMode S X Y c 1
  let b := normalizedPrimeStarFirstExit S X Y c
  let alpha := ⟪u, v⟫_ℝ
  let y := alpha⁻¹ • v
  let z := normalizedPrimeStarInteriorRemainder S X Y c v
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))
  have hAu : A u = mu • u + b := by
    change A u = mu • u + H u
    rw [show A = L + H by exact primeCover_toEuclideanLin_eq_large_add_small S X Y]
    rw [LinearMap.add_apply,
      largePrime_toEuclideanLin_normalizedStarMode
        hcut hc (by norm_num : (1 : ℝ) ^ 2 = 1)]
    rw [hmuval]
    simp [u]
  have hAy : A y = lam • y := by
    change A (alpha⁻¹ • v) = lam • (alpha⁻¹ • v)
    rw [map_smul, hAv, smul_smul, smul_smul]
    congr 1
    ring
  have huy : ⟪u, y⟫_ℝ = 1 := by
    change ⟪u, alpha⁻¹ • v⟫_ℝ = 1
    rw [real_inner_smul_right]
    exact inv_mul_cancel₀ halpha
  have hby : ⟪b, y⟫_ℝ = ⟪b, z⟫_ℝ := by
    let PI := primeStarInteriorProjection S X Y c
    have hPI : PI.IsSymmetric :=
      euclideanCoordinateComplementProjection_isSymmetric
        (largePrimeStarSupport S X Y c)
    change ⟪b, y⟫_ℝ = ⟪b, PI y⟫_ℝ
    calc
      ⟪b, y⟫_ℝ = ⟪PI b, y⟫_ℝ := by
        rw [primeStarInteriorProjection_normalizedPrimeStarFirstExit hcut hc]
      _ = ⟪b, PI y⟫_ℝ := hPI b y
  have hleft : ⟪u, A y⟫_ℝ = lam := by
    rw [hAy, real_inner_smul_right, huy, mul_one]
  have hright : ⟪u, A y⟫_ℝ = mu + ⟪b, z⟫_ℝ := by
    calc
      ⟪u, A y⟫_ℝ = ⟪A u, y⟫_ℝ := (hA u y).symm
      _ = ⟪mu • u + b, y⟫_ℝ := by rw [hAu]
      _ = mu * ⟪u, y⟫_ℝ + ⟪b, y⟫_ℝ := by
        rw [inner_add_left, real_inner_smul_left]
      _ = mu + ⟪b, z⟫_ℝ := by rw [huy, hby]; ring
  rw [hleft] at hright
  linarith

/-- Literal interior block equation for the actual star-normalized
eigenvector. -/
theorem normalizedPrimeStarInteriorRemainder_equation
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {lam : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (v : EuclideanSpace ℝ (Vertex S X))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v) :
    let xB := normalizedPrimeStarBoundaryRemainder S X Y c v
    let z := normalizedPrimeStarInteriorRemainder S X Y c v
    let b := normalizedPrimeStarFirstExit S X Y c
    lam • z - primeStarInteriorPrimeCoverOperator S X Y c z =
      b + primeStarToInteriorPrimeCoverOperator S X Y c xB := by
  dsimp only
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  let PB := primeStarBoundaryProjection S X Y c
  let PI := primeStarInteriorProjection S X Y c
  let u := largePrimeNormalizedStarMode S X Y c 1
  let alpha := ⟪u, v⟫_ℝ
  let y := alpha⁻¹ • v
  let xB := normalizedPrimeStarBoundaryRemainder S X Y c v
  let z := normalizedPrimeStarInteriorRemainder S X Y c v
  let b := normalizedPrimeStarFirstExit S X Y c
  have hy : y = u + xB + z := normalizedPrimeStar_boundary_add_interior v
  have hAy : A y = lam • y := by
    change A (alpha⁻¹ • v) = lam • (alpha⁻¹ • v)
    rw [map_smul, hAv, smul_smul, smul_smul]
    congr 1
    ring
  have hPBx : PB xB = xB :=
    primeStarBoundaryProjection_normalizedBoundaryRemainder v
  have hPIz : PI z = z :=
    primeStarInteriorProjection_normalizedInteriorRemainder v
  have hsource : primeStarToInteriorPrimeCoverOperator S X Y c u = b :=
    primeStarToInterior_normalizedStarMode_eq_firstExit hcut hc
  have hproj : lam • z = PI (A y) := by
    calc
      lam • z = PI (lam • y) := by rw [map_smul]; rfl
      _ = PI (A y) := by rw [hAy]
  change lam • z - PI (A (PI z)) = b + PI (A (PB xB))
  rw [hPIz, hPBx, hproj, hy, map_add, map_add, map_add]
  rw [map_add]
  have hPIAu : PI (A u) = b := by
    calc
      PI (A u) = PI (A (PB u)) := by
        rw [primeStarBoundaryProjection_normalizedStarMode]
      _ = b := hsource
  rw [hPIAu]
  abel

/-- Literal boundary-orthogonal block equation for the actual
star-normalized eigenvector.  The scalar component of the reverse coupling
is removed by the unit-mode orthogonal projection. -/
theorem normalizedPrimeStarBoundaryRemainder_equation
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {lam mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (v : EuclideanSpace ℝ (Vertex S X))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halpha : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0) :
    let u := largePrimeNormalizedStarMode S X Y c 1
    let xB := normalizedPrimeStarBoundaryRemainder S X Y c v
    let z := normalizedPrimeStarInteriorRemainder S X Y c v
    lam • xB - primeStarBoundaryPrimeCoverOperator S X Y c xB =
      modeOrthogonalProjection u
        (primeStarFromInteriorPrimeCoverOperator S X Y c z) := by
  dsimp only
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  let PB := primeStarBoundaryProjection S X Y c
  let PI := primeStarInteriorProjection S X Y c
  let u := largePrimeNormalizedStarMode S X Y c 1
  let b := normalizedPrimeStarFirstExit S X Y c
  let alpha := ⟪u, v⟫_ℝ
  let y := alpha⁻¹ • v
  let xB := normalizedPrimeStarBoundaryRemainder S X Y c v
  let z := normalizedPrimeStarInteriorRemainder S X Y c v
  let LB := primeStarBoundaryPrimeCoverOperator S X Y c
  let J := primeStarFromInteriorPrimeCoverOperator S X Y c
  have hy : y = u + xB + z := normalizedPrimeStar_boundary_add_interior v
  have hAy : A y = lam • y := by
    change A (alpha⁻¹ • v) = lam • (alpha⁻¹ • v)
    rw [map_smul, hAv, smul_smul, smul_smul]
    congr 1
    ring
  have hPBu : PB u = u := primeStarBoundaryProjection_normalizedStarMode
  have hPBx : PB xB = xB :=
    primeStarBoundaryProjection_normalizedBoundaryRemainder v
  have hPIz : PI z = z :=
    primeStarInteriorProjection_normalizedInteriorRemainder v
  have hPBz : PB z = 0 := by
    rw [← hPIz]
    exact primeStarBoundaryProjection_interior_eq_zero _
  have hPBy : PB y = u + xB := by
    change PB y = u + (PB y - u)
    abel
  have hPBAu : PB (A u) = mu • u := by
    have hsource :
        primeStarToInteriorPrimeCoverOperator S X Y c u = b :=
      primeStarToInterior_normalizedStarMode_eq_firstExit hcut hc
    have hAu : A u = mu • u + b := by
      let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
      let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
      change A u = mu • u + H u
      rw [show A = L + H by
        exact primeCover_toEuclideanLin_eq_large_add_small S X Y]
      rw [LinearMap.add_apply,
        largePrime_toEuclideanLin_normalizedStarMode
          hcut hc (by norm_num : (1 : ℝ) ^ 2 = 1)]
      rw [hmuval]
      simp [u]
    rw [hAu, map_add, map_smul, hPBu,
      primeStarBoundaryProjection_normalizedPrimeStarFirstExit hcut hc,
      add_zero]
  have hproj : PB (A y) = lam • PB y := by
    rw [hAy, map_smul]
  have hblock : mu • u + LB xB + J z = lam • (u + xB) := by
    change mu • u + PB (A (PB xB)) + PB (A (PI z)) =
      lam • (u + xB)
    rw [hPBx, hPIz, ← hPBAu]
    calc
      PB (A u) + PB (A xB) + PB (A z) = PB (A (u + xB + z)) := by
        rw [map_add, map_add, map_add, map_add]
      _ = PB (A y) := by rw [← hy]
      _ = lam • PB y := hproj
      _ = lam • (u + xB) := by rw [hPBy]
  have hraw : lam • xB - LB xB = J z - (lam - mu) • u := by
    have hJexpr : J z = lam • (u + xB) - (mu • u + LB xB) := by
      calc
        J z = (mu • u + LB xB + J z) - (mu • u + LB xB) := by abel
        _ = lam • (u + xB) - (mu • u + LB xB) := by rw [hblock]
    rw [hJexpr, smul_add, sub_smul]
    abel
  have hscalar : lam - mu = ⟪b, z⟫_ℝ :=
    primeCover_schurEquation_at_interiorRemainder
      hcut hc hmuval v hAv halpha
  have hPB : PB.IsSymmetric :=
    euclideanCoordinateProjection_isSymmetric
      (largePrimeStarSupport S X Y c)
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))
  have huz : ⟪u, z⟫_ℝ = 0 := by
    calc
      ⟪u, z⟫_ℝ = ⟪PB u, z⟫_ℝ := by rw [hPBu]
      _ = ⟪u, PB z⟫_ℝ := hPB u z
      _ = 0 := by rw [hPBz]; simp
  have hAu : A u = mu • u + b := by
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
    change A u = mu • u + H u
    rw [show A = L + H by exact primeCover_toEuclideanLin_eq_large_add_small S X Y]
    rw [LinearMap.add_apply,
      largePrime_toEuclideanLin_normalizedStarMode
        hcut hc (by norm_num : (1 : ℝ) ^ 2 = 1)]
    rw [hmuval]
    simp [u]
  have huJ : ⟪u, J z⟫_ℝ = ⟪b, z⟫_ℝ := by
    change ⟪u, PB (A (PI z))⟫_ℝ = ⟪b, z⟫_ℝ
    calc
      ⟪u, PB (A (PI z))⟫_ℝ = ⟪PB u, A (PI z)⟫_ℝ :=
        (hPB u (A (PI z))).symm
      _ = ⟪u, A z⟫_ℝ := by rw [hPBu, hPIz]
      _ = ⟪A u, z⟫_ℝ := (hA u z).symm
      _ = ⟪mu • u + b, z⟫_ℝ := by rw [hAu]
      _ = ⟪b, z⟫_ℝ := by
        rw [inner_add_left, real_inner_smul_left, huz, mul_zero, zero_add]
  change lam • xB - LB xB = modeOrthogonalProjection u (J z)
  rw [hraw, modeOrthogonalProjection_apply, orthogonalRemainder, huJ, ← hscalar]

/-- Graph-level Lemma 8.4: the actual eigenvalue displacement is compared
with the coordinate-interior resolvent at the reference star energy.  All
finite graph identities are discharged; only explicit quantitative gaps and
the small-prime norm estimate remain as premises. -/
theorem primeCover_eigenvalue_interiorResolventReplacement
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {lam mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (v : EuclideanSpace ℝ (Vertex S X))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halpha : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (gammaB gammaLam gammaMu eta : ℝ)
    (hgammaB : 0 < gammaB) (hgammaLam : 0 < gammaLam)
    (hgammaMu : 0 < gammaMu) (heta : 0 ≤ eta)
    (hgapLam : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaLam * ‖x‖ ≤
        ‖lam • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hgapMu : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaMu * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hboundaryGap : gammaB *
        ‖normalizedPrimeStarBoundaryRemainder S X Y c v‖ ≤
      ‖lam • normalizedPrimeStarBoundaryRemainder S X Y c v -
        primeStarBoundaryPrimeCoverOperator S X Y c
          (normalizedPrimeStarBoundaryRemainder S X Y c v)‖)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmall : gammaB⁻¹ * eta * gammaLam⁻¹ * eta ≤ 1 / 2) :
    let b := normalizedPrimeStarFirstExit S X Y c
    let z := normalizedPrimeStarInteriorRemainder S X Y c v
    let Rlam := primeStarInteriorResolventOfGap
      S X Y c lam gammaLam hgammaLam hgapLam
    let Rmu := primeStarInteriorResolventOfGap
      S X Y c mu gammaMu hgammaMu hgapMu
    |(lam - mu) - ⟪b, Rmu b⟫_ℝ| ≤
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
        |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖ := by
  dsimp only
  let u := largePrimeNormalizedStarMode S X Y c 1
  let b := normalizedPrimeStarFirstExit S X Y c
  let xB := normalizedPrimeStarBoundaryRemainder S X Y c v
  let z := normalizedPrimeStarInteriorRemainder S X Y c v
  let LB := primeStarBoundaryPrimeCoverOperator S X Y c
  let C := primeStarInteriorPrimeCoverOperator S X Y c
  let K := primeStarToInteriorPrimeCoverOperator S X Y c
  let Jfull := primeStarFromInteriorPrimeCoverOperator S X Y c
  let J := (modeOrthogonalProjection u).comp Jfull
  let Rlam := finiteResolventOfGap C lam gammaLam hgammaLam hgapLam
  let Rmu := finiteResolventOfGap C mu gammaMu hgammaMu hgapMu
  change |(lam - mu) - ⟪b, Rmu b⟫_ℝ| ≤
    2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
      |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖
  have hu : ‖u‖ = 1 := norm_largePrimeNormalizedStarMode hd
  have hboundary : lam • xB - LB xB = J z := by
    exact normalizedPrimeStarBoundaryRemainder_equation
      hcut hc hmuval v hAv halpha
  have hinterior : lam • z - C z = b + K xB := by
    exact normalizedPrimeStarInteriorRemainder_equation hcut hc v hAv
  have hK : ∀ x : EuclideanSpace ℝ (Vertex S X), ‖K x‖ ≤ eta * ‖x‖ := by
    intro x
    exact norm_primeStarToInteriorPrimeCoverOperator_le hcut hc eta heta hH x
  have hJfull : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Jfull x‖ ≤ eta * ‖x‖ := by
    intro x
    exact norm_primeStarFromInteriorPrimeCoverOperator_le hcut hc eta heta hH x
  have hJ : ∀ x : EuclideanSpace ℝ (Vertex S X), ‖J x‖ ≤ eta * ‖x‖ := by
    intro x
    calc
      ‖J x‖ = ‖orthogonalRemainder u (Jfull x)‖ := rfl
      _ ≤ ‖Jfull x‖ := norm_orthogonalRemainder_le u (Jfull x) hu
      _ ≤ eta * ‖x‖ := hJfull x
  have hreplace := boundaryInterior_quadraticFormReplacement
    LB C K J b xB z lam mu gammaB gammaLam gammaMu eta
      hgammaB hgammaLam hgammaMu heta hgapLam hgapMu
      (primeStarInteriorPrimeCoverOperator_isSymmetric S X Y c)
      hboundaryGap hboundary hinterior hK hJ hsmall
  have hscalar : lam - mu = ⟪b, z⟫_ℝ :=
    primeCover_schurEquation_at_interiorRemainder
      hcut hc hmuval v hAv halpha
  calc
    |(lam - mu) - ⟪b, Rmu b⟫_ℝ| =
        |⟪b, z⟫_ℝ - ⟪b, Rmu b⟫_ℝ| := by rw [hscalar]
    _ ≤ 2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
        |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖ := hreplace

/-- Literal normalized-source form of Proposition 8.1.  No asymptotic input
is used: the source is exactly the sum of its selected-star coordinate blocks
and its large-prime-isolated block. -/
theorem normalizedPrimeStarFirstExit_eq_sum_firstExitBlocks
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) :
    normalizedPrimeStarFirstExit S X Y c =
      (∑ k ∈ firstExitLowerCenters S X Y c,
        restrictEuclideanToFinset (largePrimeStarSupport S X Y k)
          (normalizedPrimeStarFirstExit S X Y c)) +
      restrictEuclideanToFinset (firstExitIsolatedVertices S X Y c)
        (normalizedPrimeStarFirstExit S X Y c) := by
  exact euclidean_eq_sum_firstExitStarBlocks_add_isolatedBlock hcut _
    (fun v hv ↦ normalizedPrimeStarFirstExit_eq_zero_of_not_mem hv)

/-- The exact direct-sum inverse vector for a source supported on the
first-exit compression. Non-isolated blocks use the arbitrary actual-star
inverse; the isolated block is divided by `mu`. -/
def firstExitStarResolventVector
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) (mu : ℝ)
    (b : EuclideanSpace ℝ (Vertex S X)) :
    EuclideanSpace ℝ (Vertex S X) :=
  (∑ k ∈ firstExitLowerCenters S X Y c,
    largePrimeStarResolventOfVector S X Y k mu
      (restrictEuclideanToFinset (largePrimeStarSupport S X Y k) b)) +
  mu⁻¹ • restrictEuclideanToFinset (firstExitIsolatedVertices S X Y c) b

/-- The canonical first-exit direct-sum vector is an exact inverse of
`mu - L` on every source supported by the first-exit set. -/
theorem firstExitStar_shift_resolventVector
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu : ℝ}
    (b : EuclideanSpace ℝ (Vertex S X))
    (hcut : X < (Y + 1) * (Y + 1)) (hmu : mu ≠ 0)
    (hden : ∀ k ∈ firstExitLowerCenters S X Y c,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y k : ℝ))
    (hb : ∀ v, v ∉ smallPrimeFirstExitSupport S X Y c → b v = 0) :
    mu • firstExitStarResolventVector S X Y c mu b -
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (firstExitStarResolventVector S X Y c mu b) = b := by
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let C := firstExitLowerCenters S X Y c
  let block := fun k : Vertex S X ↦
    restrictEuclideanToFinset (largePrimeStarSupport S X Y k) b
  let resolvent := fun k : Vertex S X ↦
    largePrimeStarResolventOfVector S X Y k mu (block k)
  let isolated :=
    restrictEuclideanToFinset (firstExitIsolatedVertices S X Y c) b
  have hblock (k : Vertex S X) (hk : k ∈ C) :
      mu • resolvent k - L (resolvent k) = block k := by
    apply largePrimeStar_shift_resolventOfVector (block k) hcut
      (mem_firstExitLowerCenters.mp hk).1 hmu (hden k hk)
    intro v hv
    simp [block, restrictEuclideanToFinset_apply, hv]
  have hsum :
      mu • (∑ k ∈ C, resolvent k) - L (∑ k ∈ C, resolvent k) =
        ∑ k ∈ C, block k := by
    rw [Finset.smul_sum, map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact hblock k hk
  have hisolated :
      mu • (mu⁻¹ • isolated) - L (mu⁻¹ • isolated) = isolated := by
    rw [map_smul]
    have hLiso : L isolated = 0 := by
      exact largePrime_toEuclideanLin_firstExitIsolatedBlock_eq_zero b
    rw [hLiso, smul_zero, sub_zero, smul_smul]
    field_simp [hmu]
    simp
  have hdecomp : b = (∑ k ∈ C, block k) + isolated := by
    simpa [C, block, isolated] using
      (euclidean_eq_sum_firstExitStarBlocks_add_isolatedBlock hcut b hb)
  change mu • ((∑ k ∈ C, resolvent k) + mu⁻¹ • isolated) -
      L ((∑ k ∈ C, resolvent k) + mu⁻¹ • isolated) = b
  rw [smul_add, map_add]
  calc
    (mu • ∑ k ∈ C, resolvent k) + mu • (mu⁻¹ • isolated) -
        (L (∑ k ∈ C, resolvent k) + L (mu⁻¹ • isolated)) =
        (mu • (∑ k ∈ C, resolvent k) - L (∑ k ∈ C, resolvent k)) +
          (mu • (mu⁻¹ • isolated) - L (mu⁻¹ • isolated)) := by abel
    _ = (∑ k ∈ C, block k) + isolated := by rw [hsum, hisolated]
    _ = b := hdecomp.symm

/-- The explicit direct-sum resolvent vector is supported on the canonical
first-exit compression. -/
theorem firstExitStarResolventVector_eq_zero_of_not_mem
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu : ℝ}
    (b : EuclideanSpace ℝ (Vertex S X))
    {v : Vertex S X}
    (hv : v ∉ firstExitCompressionSupport S X Y c) :
    firstExitStarResolventVector S X Y c mu b v = 0 := by
  classical
  have hblock : ∀ k ∈ firstExitLowerCenters S X Y c,
      largePrimeStarResolventOfVector S X Y k mu
          (restrictEuclideanToFinset (largePrimeStarSupport S X Y k) b) v = 0 := by
    intro k hk
    have hvStar : v ∉ largePrimeStarSupport S X Y k := by
      intro hvk
      apply hv
      apply Finset.mem_union_left
      exact mem_largePrimeStarUnionSupport.mpr ⟨k, hk, hvk⟩
    have hvk : v ≠ k := by
      intro hvk
      subst v
      exact hvStar (by simp [largePrimeStarSupport])
    have hvleaf : v ∉ largePrimeLeaves S X Y k := by
      intro hvleaf
      exact hvStar (by simp [largePrimeStarSupport, hvleaf])
    unfold largePrimeStarResolventOfVector
    exact largePrimeStarDataVector_outside _ _ hvk hvleaf
  have hvIso : v ∉ firstExitIsolatedVertices S X Y c := by
    intro hvI
    exact hv (Finset.mem_union_right _ hvI)
  have hsum :
      ((∑ k ∈ firstExitLowerCenters S X Y c,
        largePrimeStarResolventOfVector S X Y k mu
          (restrictEuclideanToFinset (largePrimeStarSupport S X Y k) b)) :
          EuclideanSpace ℝ (Vertex S X)) v = 0 := by
    change EuclideanSpace.projₗ v
      (∑ k ∈ firstExitLowerCenters S X Y c,
        largePrimeStarResolventOfVector S X Y k mu
          (restrictEuclideanToFinset (largePrimeStarSupport S X Y k) b)) = 0
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro k hk
    exact hblock k hk
  unfold firstExitStarResolventVector
  simp only [PiLp.add_apply, PiLp.smul_apply]
  rw [hsum]
  simp [restrictEuclideanToFinset_apply, hvIso]

/-- The inverse constructed from the compression gap agrees exactly with the
explicit direct sum of the individual star inverses and the isolated block. -/
theorem firstExitLargePrimeResolventOfGap_apply_eq_firstExitStarResolventVector
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu gamma : ℝ}
    (b : EuclideanSpace ℝ (Vertex S X))
    (hcut : X < (Y + 1) * (Y + 1)) (hmu : mu ≠ 0)
    (hden : ∀ k ∈ firstExitLowerCenters S X Y c,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y k : ℝ))
    (hb : ∀ v, v ∉ smallPrimeFirstExitSupport S X Y c → b v = 0)
    (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖) :
    firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap b =
      firstExitStarResolventVector S X Y c mu b := by
  let x := firstExitStarResolventVector S X Y c mu b
  have hxSupport : ∀ v,
      v ∉ firstExitCompressionSupport S X Y c → x v = 0 := by
    intro v hv
    exact firstExitStarResolventVector_eq_zero_of_not_mem b hv
  have hsolveFull :
      mu • x -
          Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x = b := by
    exact firstExitStar_shift_resolventVector b hcut hmu hden hb
  have hcompression :
      firstExitLargePrimeCompressionOperator S X Y c x =
        Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x :=
    firstExitLargePrimeCompressionOperator_eq_of_supported hcut x hxSupport
  have hsolve :
      mu • x - firstExitLargePrimeCompressionOperator S X Y c x = b := by
    rw [hcompression]
    exact hsolveFull
  calc
    firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap b =
        firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap
          (mu • x - firstExitLargePrimeCompressionOperator S X Y c x) := by
            rw [hsolve]
    _ = x := firstExitLargePrimeResolventOfGap_shift_apply
      S X Y c mu gamma hgamma hgap x

/-- The actual eigenvector remainder, divided by its nonzero coordinate in
the reference star direction.  This is the perturbed reduced solution that
appears in the Schur equation; defining it directly avoids introducing an
artificial linear map with one prescribed value. -/
def normalizedPrimeStarEigenRemainder
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (v : EuclideanSpace ℝ (Vertex S X)) :
    EuclideanSpace ℝ (Vertex S X) :=
  (⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ)⁻¹ •
    orthogonalRemainder (largePrimeNormalizedStarMode S X Y c 1) v

/-- Coordinate part of the actual normalized eigenvector remainder lying in
the canonical first-exit compression. -/
def normalizedPrimeStarFirstExitCompressionPart
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (v : EuclideanSpace ℝ (Vertex S X)) :
    EuclideanSpace ℝ (Vertex S X) :=
  restrictEuclideanToFinset (firstExitCompressionSupport S X Y c)
    (normalizedPrimeStarEigenRemainder S X Y c v)

/-- The exact scalar Schur equation written with the actual normalized
eigenvector remainder. -/
theorem primeCover_schurEquation_at_actualEigenRemainder
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {lam mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (v : EuclideanSpace ℝ (Vertex S X))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halpha : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0) :
    lam - mu =
      ⟪normalizedPrimeStarFirstExit S X Y c,
        normalizedPrimeStarEigenRemainder S X Y c v⟫_ℝ := by
  have hscalar := primeCover_scalarEquation_at_normalizedStarMode
    (S := S) (X := X) (Y := Y) (c := c)
    hcut hc (by norm_num : (1 : ℝ) ^ 2 = 1) (by simpa using hmuval) v hAv
  rw [normalizedPrimeStarEigenRemainder, real_inner_smul_right]
  change lam - mu =
    (⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ)⁻¹ *
      ⟪Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c 1),
        orthogonalRemainder (largePrimeNormalizedStarMode S X Y c 1) v⟫_ℝ
  rw [← hscalar]
  field_simp [halpha]

/-- Exact Schur equation after projecting the actual normalized eigenvector
remainder to the canonical first-exit compression. The projection loses no
quadratic-form information because the first-exit source is supported there.
-/
theorem primeCover_schurEquation_at_firstExitCompressionPart
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {lam mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (v : EuclideanSpace ℝ (Vertex S X))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halpha : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0) :
    lam - mu =
      ⟪normalizedPrimeStarFirstExit S X Y c,
        normalizedPrimeStarFirstExitCompressionPart S X Y c v⟫_ℝ := by
  rw [primeCover_schurEquation_at_actualEigenRemainder
    hcut hc hmuval v hAv halpha]
  symm
  apply inner_restrictEuclideanToFinset_right_of_supported
  intro w hw
  apply normalizedPrimeStarFirstExit_eq_zero_of_not_mem
  intro hwExit
  exact hw (smallPrimeFirstExitSupport_subset_firstExitCompressionSupport
    hcut hwExit)

/-- Lemma 8.6 applied directly to the actual normalized eigenvector
remainder. -/
theorem normalizedPrimeStarEigenRemainder_resolventReplacement
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (v : EuclideanSpace ℝ (Vertex S X))
    (R T : EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (rho tau alpha : ℝ)
    (hR : R.IsSymmetric)
    (hident : normalizedPrimeStarEigenRemainder S X Y c v =
      R (normalizedPrimeStarFirstExit S X Y c) +
        R (T (normalizedPrimeStarEigenRemainder S X Y c v)))
    (hRT : ∀ x, ‖R (T x)‖ ≤ alpha * ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ tau * ‖x‖)
    (htau : 0 ≤ tau) (halpha : alpha ≤ 1 / 2)
    (hstar : ⟪normalizedPrimeStarFirstExit S X Y c,
        R (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ = rho) :
    |⟪normalizedPrimeStarFirstExit S X Y c,
        normalizedPrimeStarEigenRemainder S X Y c v⟫_ℝ - rho| ≤
      2 * tau * ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 := by
  rw [← hstar]
  exact abs_quadraticForm_vectorReplacement_le
    R T (normalizedPrimeStarFirstExit S X Y c)
      (normalizedPrimeStarEigenRemainder S X Y c v)
      tau alpha hR hident hRT hT htau halpha

/-- Lemma 8.6 on the realizable `U`-coordinate part of the actual normalized
eigenvector remainder. -/
theorem normalizedPrimeStarFirstExitCompressionPart_resolventReplacement
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (v : EuclideanSpace ℝ (Vertex S X))
    (R T : EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (rho tau alpha : ℝ)
    (hR : R.IsSymmetric)
    (hident : normalizedPrimeStarFirstExitCompressionPart S X Y c v =
      R (normalizedPrimeStarFirstExit S X Y c) +
        R (T (normalizedPrimeStarFirstExitCompressionPart S X Y c v)))
    (hRT : ∀ x, ‖R (T x)‖ ≤ alpha * ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ tau * ‖x‖)
    (htau : 0 ≤ tau) (halpha : alpha ≤ 1 / 2)
    (hstar : ⟪normalizedPrimeStarFirstExit S X Y c,
        R (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ = rho) :
    |⟪normalizedPrimeStarFirstExit S X Y c,
        normalizedPrimeStarFirstExitCompressionPart S X Y c v⟫_ℝ - rho| ≤
      2 * tau * ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 := by
  rw [← hstar]
  exact abs_quadraticForm_vectorReplacement_le
    R T (normalizedPrimeStarFirstExit S X Y c)
      (normalizedPrimeStarFirstExitCompressionPart S X Y c v)
      tau alpha hR hident hRT hT htau halpha

/-- Lemma 8.6 from literal two-block equations.  The exact replacement
identity and both operator certificates are derived from the `U` equation,
the solved `W` equation, and pointwise bounds for their four block maps. -/
theorem normalizedPrimeStarFirstExitCompressionPart_feshbachReplacement
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (v : EuclideanSpace ℝ (Vertex S X))
    (L K RW J R : EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (xW : EuclideanSpace ℝ (Vertex S X))
    (rho mu lam rbound kappa omega jappa : ℝ)
    (hrbound : 0 ≤ rbound) (hkappa : 0 ≤ kappa)
    (homega : 0 ≤ omega) (hjappa : 0 ≤ jappa)
    (hR : R.IsSymmetric)
    (hRleft : ∀ y, R (mu • y - L y) = y)
    (hW : xW = RW (J
      (normalizedPrimeStarFirstExitCompressionPart S X Y c v)))
    (hU : lam • normalizedPrimeStarFirstExitCompressionPart S X Y c v -
        L (normalizedPrimeStarFirstExitCompressionPart S X Y c v) - K xW =
      normalizedPrimeStarFirstExit S X Y c)
    (hRbound : ∀ x, ‖R x‖ ≤ rbound * ‖x‖)
    (hK : ∀ x, ‖K x‖ ≤ kappa * ‖x‖)
    (hRW : ∀ x, ‖RW x‖ ≤ omega * ‖x‖)
    (hJ : ∀ x, ‖J x‖ ≤ jappa * ‖x‖)
    (hsmall : rbound * (|mu - lam| + kappa * omega * jappa) ≤ 1 / 2)
    (hstar : ⟪normalizedPrimeStarFirstExit S X Y c,
        R (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ = rho) :
    |⟪normalizedPrimeStarFirstExit S X Y c,
        normalizedPrimeStarFirstExitCompressionPart S X Y c v⟫_ℝ - rho| ≤
      2 * (|mu - lam| + kappa * omega * jappa) *
        ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 := by
  let T := feshbachEffectiveInteraction K RW J mu lam
  let tau := |mu - lam| + kappa * omega * jappa
  let alpha := rbound * tau
  have hident : normalizedPrimeStarFirstExitCompressionPart S X Y c v =
      R (normalizedPrimeStarFirstExit S X Y c) +
        R (T (normalizedPrimeStarFirstExitCompressionPart S X Y c v)) := by
    exact feshbachReducedVectorIdentity L K RW J R
      (normalizedPrimeStarFirstExit S X Y c)
      (normalizedPrimeStarFirstExitCompressionPart S X Y c v) xW
      mu lam hRleft hW hU
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  have hT : ∀ x, ‖T x‖ ≤ tau * ‖x‖ := by
    intro x
    exact norm_feshbachEffectiveInteraction_apply_le K RW J mu lam
      kappa omega jappa hkappa homega hjappa hK hRW hJ x
  have hRT : ∀ x, ‖R (T x)‖ ≤ alpha * ‖x‖ := by
    intro x
    exact norm_resolvent_feshbachEffectiveInteraction_apply_le
      R K RW J mu lam rbound kappa omega jappa hrbound hkappa
        homega hjappa hRbound hK hRW hJ x
  exact normalizedPrimeStarFirstExitCompressionPart_resolventReplacement
    c v R T rho tau alpha hR hident hRT hT htau hsmall hstar

/-- Lemma 8.6 with every structural operator specialized to the actual
prime-cover graph and the normalized arithmetic first-exit source.  The
remaining premises are precisely the three quantitative shifted gaps, the
small-prime operator bound, and the contraction inequality. -/
theorem normalizedPrimeStarFirstExit_graphQuadraticFormReplacement
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (mu gammaI gammaU gammaW eta : ℝ) (hmu : mu ≠ 0)
    (hgammaI : 0 < gammaI) (hgammaU : 0 < gammaU)
    (hgammaW : 0 < gammaW) (heta : 0 ≤ eta)
    (hgapI : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaI * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hgapU : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaU * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖)
    (hgapW : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaW * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmall : gammaU⁻¹ * (eta * gammaW⁻¹ * eta) ≤ 1 / 2) :
    let b := normalizedPrimeStarFirstExit S X Y c
    let z := primeStarInteriorResolventOfGap
      S X Y c mu gammaI hgammaI hgapI b
    let RU := firstExitLargePrimeResolventOfGap
      S X Y c mu gammaU hgammaU hgapU
    |⟪b, z⟫_ℝ - ⟪b, RU b⟫_ℝ| ≤
      2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2 := by
  dsimp only
  exact primeStarInteriorResolvent_quadraticFormReplacement
    hS hcut hc mu gammaI gammaU gammaW eta hmu hgammaI hgammaU
      hgammaW heta hgapI hgapU hgapW hH hsmall
      (normalizedPrimeStarFirstExit S X Y c)
      (firstExitCompressionProjection_normalizedPrimeStarFirstExit hcut)

/-- The finite remainder theorem with the displacement and scalar error
derived from an actual reduced resolvent.  The only replacement premise is
the scalar quadratic-form comparison produced by Lemma 8.6. -/
theorem actualFinitePrimeStarRemainder_of_reducedResolvent
    {S : Finset ℕ} {X Y : ℕ} {ι κ : Type*}
    (U : Finset ι) (Dset : Finset κ)
    (upTarget : ι → Vertex S X) (downTarget : κ → Vertex S X)
    (downLeaves : κ → Finset (Vertex S X))
    (c : Vertex S X)
    (v : EuclideanSpace ℝ (Vertex S X))
    (Rpert : EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (lam mu primeCount boundary eta shiftBound c0 : ℝ)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halpha : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (hinv : orthogonalRemainder (largePrimeNormalizedStarMode S X Y c 1) v =
      ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ •
        Rpert (normalizedPrimeStarFirstExit S X Y c))
    (hc0 : c0 ^ 2 = 1 / 2)
    (hupden : ∀ q ∈ U,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (upTarget q) : ℝ))
    (hdownLeaves : ∀ q ∈ Dset,
      downLeaves q ⊆ largePrimeLeaves S X Y (downTarget q))
    (hdownCard : ∀ q ∈ Dset, ((downLeaves q).card : ℝ) = mu ^ 2)
    (hdownden : ∀ q ∈ Dset,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (downTarget q) : ℝ))
    (hboundary : boundary = U.card)
    (hdegree : mu ^ 2 = primeCount - boundary)
    (hreplace :
      |⟪normalizedPrimeStarFirstExit S X Y c,
          Rpert (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ -
        ((∑ q ∈ U,
          ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
            actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
        (∑ q ∈ Dset,
          ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
            actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ))| ≤ eta)
    (hshift : |lam - mu| ≤ shiftBound) (hshift0 : 0 ≤ shiftBound) :
    |(lam ^ 2 - primeCount) -
      finiteStarCorrection U Dset
        (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2)| ≤
      2 * |mu| * eta + shiftBound ^ 2 := by
  have hmu : mu ≠ 0 := by
    rw [hmuval]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hschur : lam - mu =
      ⟪normalizedPrimeStarFirstExit S X Y c,
        Rpert (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ := by
    simpa [normalizedPrimeStarFirstExit] using
      (primeCover_schurEquation_at_normalizedStarMode
        (S := S) (X := X) (Y := Y) (c := c)
        hcut hc (by norm_num : (1 : ℝ) ^ 2 = 1) (by simpa using hmuval)
        Rpert v hAv halpha hinv)
  let rho :=
    (∑ q ∈ U,
      ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
        actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
    (∑ q ∈ Dset,
      ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
        actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ)
  let err :=
    ⟪normalizedPrimeStarFirstExit S X Y c,
      Rpert (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ - rho
  have hdisp : lam - mu = rho + err := by
    dsimp [err]
    rw [hschur]
    ring
  have herr : |err| ≤ eta := by
    simpa [err, rho] using hreplace
  exact actualFinitePrimeStarRemainder_bound U Dset upTarget downTarget
    downLeaves lam mu primeCount boundary err eta shiftBound c0 hmu hc0
    hupden hdownLeaves hdownCard hdownden hboundary hdegree
    (by simpa [rho] using hdisp) herr hshift hshift0

/-- Source-weighted form of Lemma 8.6 on the actual normalized first-exit
vector.  The exact resolvent identity and operator bounds imply the sole
quadratic-form premise consumed by the finite remainder theorem. -/
theorem normalizedPrimeStarFirstExit_resolventReplacement
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (R T Rpert : EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (rho tau alpha : ℝ)
    (hR : R.IsSymmetric)
    (hident : Rpert (normalizedPrimeStarFirstExit S X Y c) =
      R (normalizedPrimeStarFirstExit S X Y c) +
        R (T (Rpert (normalizedPrimeStarFirstExit S X Y c))))
    (hRT : ∀ x, ‖R (T x)‖ ≤ alpha * ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ tau * ‖x‖)
    (htau : 0 ≤ tau) (halpha : alpha ≤ 1 / 2)
    (hstar : ⟪normalizedPrimeStarFirstExit S X Y c,
        R (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ = rho) :
    |⟪normalizedPrimeStarFirstExit S X Y c,
        Rpert (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ - rho| ≤
      2 * tau * ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 := by
  rw [← hstar]
  exact abs_quadraticForm_resolventReplacement_le
    R T Rpert (normalizedPrimeStarFirstExit S X Y c)
      tau alpha hR hident hRT hT htau halpha

/-- Fully assembled finite remainder interface consumed by Theorem 8.7. The source-weighted
resolvent identity discharges both the former displacement hypothesis and
the former scalar error hypothesis. -/
theorem actualFinitePrimeStarRemainder_of_sourceWeightedResolvent
    {S : Finset ℕ} {X Y : ℕ} {ι κ : Type*}
    (U : Finset ι) (Dset : Finset κ)
    (upTarget : ι → Vertex S X) (downTarget : κ → Vertex S X)
    (downLeaves : κ → Finset (Vertex S X))
    (c : Vertex S X) (v : EuclideanSpace ℝ (Vertex S X))
    (R T Rpert : EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (lam mu primeCount boundary tau alpha shiftBound c0 : ℝ)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halphaMode : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (hinv : orthogonalRemainder (largePrimeNormalizedStarMode S X Y c 1) v =
      ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ •
        Rpert (normalizedPrimeStarFirstExit S X Y c))
    (hc0 : c0 ^ 2 = 1 / 2)
    (hupden : ∀ q ∈ U,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (upTarget q) : ℝ))
    (hdownLeaves : ∀ q ∈ Dset,
      downLeaves q ⊆ largePrimeLeaves S X Y (downTarget q))
    (hdownCard : ∀ q ∈ Dset, ((downLeaves q).card : ℝ) = mu ^ 2)
    (hdownden : ∀ q ∈ Dset,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (downTarget q) : ℝ))
    (hboundary : boundary = U.card)
    (hdegree : mu ^ 2 = primeCount - boundary)
    (hR : R.IsSymmetric)
    (hident : Rpert (normalizedPrimeStarFirstExit S X Y c) =
      R (normalizedPrimeStarFirstExit S X Y c) +
        R (T (Rpert (normalizedPrimeStarFirstExit S X Y c))))
    (hRT : ∀ x, ‖R (T x)‖ ≤ alpha * ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ tau * ‖x‖)
    (htau : 0 ≤ tau) (halpha : alpha ≤ 1 / 2)
    (hstar : ⟪normalizedPrimeStarFirstExit S X Y c,
        R (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ =
      (∑ q ∈ U,
        ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
          actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
      (∑ q ∈ Dset,
        ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ))
    (hshift : |lam - mu| ≤ shiftBound) (hshift0 : 0 ≤ shiftBound) :
    |(lam ^ 2 - primeCount) -
      finiteStarCorrection U Dset
        (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2)| ≤
      4 * |mu| * tau *
          ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 +
        shiftBound ^ 2 := by
  let eta := 2 * tau * ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2
  have hresult := actualFinitePrimeStarRemainder_of_reducedResolvent
    U Dset upTarget downTarget downLeaves c v Rpert
      lam mu primeCount boundary eta shiftBound c0 hcut hc hd hmuval hAv
      halphaMode hinv hc0 hupden hdownLeaves hdownCard hdownden
      hboundary hdegree
      (normalizedPrimeStarFirstExit_resolventReplacement
        c R T Rpert _ tau alpha hR hident hRT hT htau halpha hstar)
      hshift hshift0
  have hcoeff :
      2 * |mu| * eta =
        4 * |mu| * tau * ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 := by
    dsimp [eta]
    ring
  rw [← hcoeff]
  exact hresult

/-- Preferred finite remainder interface consumed by Theorem 8.7. The Schur variable is the actual
normalized orthogonal component of the matched prime-cover eigenvector, so
neither `hdisp`, `herr`, nor an auxiliary perturbed-resolvent map is exposed
as a hypothesis.  What remains visible is precisely the reduced resolvent
identity, its source-weighted norm certificates, and the exact local-star
quadratic form. -/
theorem actualFinitePrimeStarRemainder_of_actualEigenRemainder
    {S : Finset ℕ} {X Y : ℕ} {ι κ : Type*}
    (U : Finset ι) (Dset : Finset κ)
    (upTarget : ι → Vertex S X) (downTarget : κ → Vertex S X)
    (downLeaves : κ → Finset (Vertex S X))
    (c : Vertex S X) (v : EuclideanSpace ℝ (Vertex S X))
    (R T : EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (lam mu primeCount boundary tau alpha shiftBound c0 : ℝ)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halphaMode : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (hc0 : c0 ^ 2 = 1 / 2)
    (hupden : ∀ q ∈ U,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (upTarget q) : ℝ))
    (hdownLeaves : ∀ q ∈ Dset,
      downLeaves q ⊆ largePrimeLeaves S X Y (downTarget q))
    (hdownCard : ∀ q ∈ Dset, ((downLeaves q).card : ℝ) = mu ^ 2)
    (hdownden : ∀ q ∈ Dset,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (downTarget q) : ℝ))
    (hboundary : boundary = U.card)
    (hdegree : mu ^ 2 = primeCount - boundary)
    (hR : R.IsSymmetric)
    (hident : normalizedPrimeStarEigenRemainder S X Y c v =
      R (normalizedPrimeStarFirstExit S X Y c) +
        R (T (normalizedPrimeStarEigenRemainder S X Y c v)))
    (hRT : ∀ x, ‖R (T x)‖ ≤ alpha * ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ tau * ‖x‖)
    (htau : 0 ≤ tau) (halpha : alpha ≤ 1 / 2)
    (hstar : ⟪normalizedPrimeStarFirstExit S X Y c,
        R (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ =
      (∑ q ∈ U,
        ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
          actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
      (∑ q ∈ Dset,
        ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ))
    (hshift : |lam - mu| ≤ shiftBound) (hshift0 : 0 ≤ shiftBound) :
    |(lam ^ 2 - primeCount) -
      finiteStarCorrection U Dset
        (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2)| ≤
      4 * |mu| * tau *
          ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 +
        shiftBound ^ 2 := by
  let rho :=
    (∑ q ∈ U,
      ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
        actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
    (∑ q ∈ Dset,
      ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
        actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ)
  let err :=
    ⟪normalizedPrimeStarFirstExit S X Y c,
      normalizedPrimeStarEigenRemainder S X Y c v⟫_ℝ - rho
  have hschur : lam - mu =
      ⟪normalizedPrimeStarFirstExit S X Y c,
        normalizedPrimeStarEigenRemainder S X Y c v⟫_ℝ :=
    primeCover_schurEquation_at_actualEigenRemainder
      hcut hc hmuval v hAv halphaMode
  have hdisp : lam - mu = rho + err := by
    dsimp [err]
    rw [hschur]
    ring
  have herr : |err| ≤
      2 * tau * ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 := by
    simpa [err, rho] using
      (normalizedPrimeStarEigenRemainder_resolventReplacement
        c v R T rho tau alpha hR hident hRT hT htau halpha hstar)
  have hmu : mu ≠ 0 := by
    rw [hmuval]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hresult := actualFinitePrimeStarRemainder_bound
    U Dset upTarget downTarget downLeaves
      lam mu primeCount boundary err
      (2 * tau * ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2)
      shiftBound c0 hmu hc0 hupden hdownLeaves hdownCard hdownden
      hboundary hdegree (by simpa [rho] using hdisp) herr hshift hshift0
  convert hresult using 1 <;> ring

/-- Block-assembled finite remainder interface consumed by Theorem 8.7. The scalar `hstar`
certificate is replaced by literal vector decompositions of the normalized
first-exit source and its reduced resolvent. Pairwise-disjoint arithmetic star
supports discharge every cross term through
`inner_actualFiniteBlockSums_eq`. -/
theorem actualFinitePrimeStarRemainder_of_actualEigenRemainder_blocks
    {S : Finset ℕ} {X Y : ℕ} {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (U : Finset ι) (Dset : Finset κ)
    (upTarget : ι → Vertex S X) (downTarget : κ → Vertex S X)
    (downLeaves : κ → Finset (Vertex S X))
    (c : Vertex S X) (v : EuclideanSpace ℝ (Vertex S X))
    (R T : EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (lam mu primeCount boundary tau alpha shiftBound c0 : ℝ)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halphaMode : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (hc0 : c0 ^ 2 = 1 / 2)
    (hupden : ∀ q ∈ U,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (upTarget q) : ℝ))
    (hdownLeaves : ∀ q ∈ Dset,
      downLeaves q ⊆ largePrimeLeaves S X Y (downTarget q))
    (hdownCard : ∀ q ∈ Dset, ((downLeaves q).card : ℝ) = mu ^ 2)
    (hdownden : ∀ q ∈ Dset,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (downTarget q) : ℝ))
    (hboundary : boundary = U.card)
    (hdegree : mu ^ 2 = primeCount - boundary)
    (hR : R.IsSymmetric)
    (hident : normalizedPrimeStarEigenRemainder S X Y c v =
      R (normalizedPrimeStarFirstExit S X Y c) +
        R (T (normalizedPrimeStarEigenRemainder S X Y c v)))
    (hRT : ∀ x, ‖R (T x)‖ ≤ alpha * ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ tau * ‖x‖)
    (htau : 0 ≤ tau) (halpha : alpha ≤ 1 / 2)
    (hsource : normalizedPrimeStarFirstExit S X Y c =
      (∑ q ∈ U, actualUpStarFirstExit S X Y (upTarget q) mu c0) +
      (∑ q ∈ Dset,
        actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0))
    (hresolvent : R (normalizedPrimeStarFirstExit S X Y c) =
      (∑ q ∈ U, actualUpStarResolvent S X Y (upTarget q) mu c0) +
      (∑ q ∈ Dset,
        actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0))
    (hUU : ∀ q ∈ U, ∀ r ∈ U, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (upTarget r)))
    (hUD : ∀ q ∈ U, ∀ r ∈ Dset,
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (downTarget r)))
    (hDD : ∀ q ∈ Dset, ∀ r ∈ Dset, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (downTarget q))
        (largePrimeStarSupport S X Y (downTarget r)))
    (hshift : |lam - mu| ≤ shiftBound) (hshift0 : 0 ≤ shiftBound) :
    |(lam ^ 2 - primeCount) -
      finiteStarCorrection U Dset
        (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2)| ≤
      4 * |mu| * tau *
          ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 +
        shiftBound ^ 2 := by
  have hstar : ⟪normalizedPrimeStarFirstExit S X Y c,
      R (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ =
      (∑ q ∈ U,
        ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
          actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
      (∑ q ∈ Dset,
        ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ) := by
    rw [hresolvent, hsource]
    exact inner_actualFiniteBlockSums_eq U Dset upTarget downTarget
      downLeaves mu c0 hUU hUD hDD
  exact actualFinitePrimeStarRemainder_of_actualEigenRemainder
    U Dset upTarget downTarget downLeaves c v R T
      lam mu primeCount boundary tau alpha shiftBound c0
      hcut hc hd hmuval hAv halphaMode hc0 hupden hdownLeaves hdownCard
      hdownden hboundary hdegree hR hident hRT hT htau halpha hstar
      hshift hshift0

/-- Preferred compressed finite remainder interface consumed by Theorem 8.7. In contrast with
`actualFinitePrimeStarRemainder_of_actualEigenRemainder_blocks`, the
reduced-resolvent identity is required only for the coordinate part of the
actual eigenvector remainder lying in the canonical first-exit compression.
This is the component that occurs in the exact scalar Schur equation, and is
therefore the realizable `U`-space unknown in the Feshbach reduction. -/
theorem actualFinitePrimeStarRemainder_of_firstExitCompressionPart_blocks
    {S : Finset ℕ} {X Y : ℕ} {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (U : Finset ι) (Dset : Finset κ)
    (upTarget : ι → Vertex S X) (downTarget : κ → Vertex S X)
    (downLeaves : κ → Finset (Vertex S X))
    (c : Vertex S X) (v : EuclideanSpace ℝ (Vertex S X))
    (R T : EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X))
    (lam mu primeCount boundary tau alpha shiftBound c0 : ℝ)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halphaMode : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (hc0 : c0 ^ 2 = 1 / 2)
    (hupden : ∀ q ∈ U,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (upTarget q) : ℝ))
    (hdownLeaves : ∀ q ∈ Dset,
      downLeaves q ⊆ largePrimeLeaves S X Y (downTarget q))
    (hdownCard : ∀ q ∈ Dset, ((downLeaves q).card : ℝ) = mu ^ 2)
    (hdownden : ∀ q ∈ Dset,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (downTarget q) : ℝ))
    (hboundary : boundary = U.card)
    (hdegree : mu ^ 2 = primeCount - boundary)
    (hR : R.IsSymmetric)
    (hident : normalizedPrimeStarFirstExitCompressionPart S X Y c v =
      R (normalizedPrimeStarFirstExit S X Y c) +
        R (T (normalizedPrimeStarFirstExitCompressionPart S X Y c v)))
    (hRT : ∀ x, ‖R (T x)‖ ≤ alpha * ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ tau * ‖x‖)
    (htau : 0 ≤ tau) (halpha : alpha ≤ 1 / 2)
    (hsource : normalizedPrimeStarFirstExit S X Y c =
      (∑ q ∈ U, actualUpStarFirstExit S X Y (upTarget q) mu c0) +
      (∑ q ∈ Dset,
        actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0))
    (hresolvent : R (normalizedPrimeStarFirstExit S X Y c) =
      (∑ q ∈ U, actualUpStarResolvent S X Y (upTarget q) mu c0) +
      (∑ q ∈ Dset,
        actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0))
    (hUU : ∀ q ∈ U, ∀ r ∈ U, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (upTarget r)))
    (hUD : ∀ q ∈ U, ∀ r ∈ Dset,
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (downTarget r)))
    (hDD : ∀ q ∈ Dset, ∀ r ∈ Dset, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (downTarget q))
        (largePrimeStarSupport S X Y (downTarget r)))
    (hshift : |lam - mu| ≤ shiftBound) (hshift0 : 0 ≤ shiftBound) :
    |(lam ^ 2 - primeCount) -
      finiteStarCorrection U Dset
        (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2)| ≤
      4 * |mu| * tau *
          ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 +
        shiftBound ^ 2 := by
  have hstar : ⟪normalizedPrimeStarFirstExit S X Y c,
      R (normalizedPrimeStarFirstExit S X Y c)⟫_ℝ =
      (∑ q ∈ U,
        ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
          actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
      (∑ q ∈ Dset,
        ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ) := by
    rw [hresolvent, hsource]
    exact inner_actualFiniteBlockSums_eq U Dset upTarget downTarget
      downLeaves mu c0 hUU hUD hDD
  let rho :=
    (∑ q ∈ U,
      ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
        actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
    (∑ q ∈ Dset,
      ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
        actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ)
  let err :=
    ⟪normalizedPrimeStarFirstExit S X Y c,
      normalizedPrimeStarFirstExitCompressionPart S X Y c v⟫_ℝ - rho
  have hschur : lam - mu =
      ⟪normalizedPrimeStarFirstExit S X Y c,
        normalizedPrimeStarFirstExitCompressionPart S X Y c v⟫_ℝ :=
    primeCover_schurEquation_at_firstExitCompressionPart
      hcut hc hmuval v hAv halphaMode
  have hdisp : lam - mu = rho + err := by
    dsimp [err]
    rw [hschur]
    ring
  have herr : |err| ≤
      2 * tau * ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 := by
    simpa [err, rho] using
      (normalizedPrimeStarFirstExitCompressionPart_resolventReplacement
        c v R T rho tau alpha hR hident hRT hT htau halpha hstar)
  have hmu : mu ≠ 0 := by
    rw [hmuval]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hresult := actualFinitePrimeStarRemainder_bound
    U Dset upTarget downTarget downLeaves
      lam mu primeCount boundary err
      (2 * tau * ‖R (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2)
      shiftBound c0 hmu hc0 hupden hdownLeaves hdownCard hdownden
      hboundary hdegree (by simpa [rho] using hdisp) herr hshift hshift0
  convert hresult using 1 <;> ring

/-- Fully graph-instantiated finite comparison consumed by Theorem 8.7. The actual eigenpair,
boundary/interior Feshbach estimate, and `U/W` source-weighted replacement
derive the scalar displacement and error consumed by
`actualFinitePrimeStarRemainder_bound`; neither `hdisp` nor `herr` appears as
a premise.  The remaining block premises are exact arithmetic identities for
the canonical first-exit direct sum. -/
theorem actualFinitePrimeStarRemainder_of_graphGaps_blocks
    {S : Finset ℕ} {X Y : ℕ} {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (U : Finset ι) (Dset : Finset κ)
    (upTarget : ι → Vertex S X) (downTarget : κ → Vertex S X)
    (downLeaves : κ → Finset (Vertex S X))
    (c : Vertex S X) (v : EuclideanSpace ℝ (Vertex S X))
    (lam mu primeCount boundary shiftBound c0 : ℝ)
    (gammaB gammaLam gammaMu gammaU gammaW eta : ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halphaMode : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (hgammaB : 0 < gammaB) (hgammaLam : 0 < gammaLam)
    (hgammaMu : 0 < gammaMu) (hgammaU : 0 < gammaU)
    (hgammaW : 0 < gammaW) (heta : 0 ≤ eta)
    (hgapLam : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaLam * ‖x‖ ≤
        ‖lam • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hgapMu : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaMu * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hgapU : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaU * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖)
    (hgapW : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaW * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖)
    (hboundaryGap : gammaB *
        ‖normalizedPrimeStarBoundaryRemainder S X Y c v‖ ≤
      ‖lam • normalizedPrimeStarBoundaryRemainder S X Y c v -
        primeStarBoundaryPrimeCoverOperator S X Y c
          (normalizedPrimeStarBoundaryRemainder S X Y c v)‖)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmallBoundary : gammaB⁻¹ * eta * gammaLam⁻¹ * eta ≤ 1 / 2)
    (hsmallUW : gammaU⁻¹ * (eta * gammaW⁻¹ * eta) ≤ 1 / 2)
    (hc0 : c0 ^ 2 = 1 / 2)
    (hupden : ∀ q ∈ U,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (upTarget q) : ℝ))
    (hdownLeaves : ∀ q ∈ Dset,
      downLeaves q ⊆ largePrimeLeaves S X Y (downTarget q))
    (hdownCard : ∀ q ∈ Dset, ((downLeaves q).card : ℝ) = mu ^ 2)
    (hdownden : ∀ q ∈ Dset,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (downTarget q) : ℝ))
    (hboundary : boundary = U.card)
    (hdegree : mu ^ 2 = primeCount - boundary)
    (hsource : normalizedPrimeStarFirstExit S X Y c =
      (∑ q ∈ U, actualUpStarFirstExit S X Y (upTarget q) mu c0) +
      (∑ q ∈ Dset,
        actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0))
    (hresolvent :
      firstExitLargePrimeResolventOfGap
          S X Y c mu gammaU hgammaU hgapU
          (normalizedPrimeStarFirstExit S X Y c) =
        (∑ q ∈ U, actualUpStarResolvent S X Y (upTarget q) mu c0) +
        (∑ q ∈ Dset,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0))
    (hUU : ∀ q ∈ U, ∀ r ∈ U, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (upTarget r)))
    (hUD : ∀ q ∈ U, ∀ r ∈ Dset,
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (downTarget r)))
    (hDD : ∀ q ∈ Dset, ∀ r ∈ Dset, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (downTarget q))
        (largePrimeStarSupport S X Y (downTarget r)))
    (hshift : |lam - mu| ≤ shiftBound) (hshift0 : 0 ≤ shiftBound) :
    let b := normalizedPrimeStarFirstExit S X Y c
    let Rlam := primeStarInteriorResolventOfGap
      S X Y c lam gammaLam hgammaLam hgapLam
    let Rmu := primeStarInteriorResolventOfGap
      S X Y c mu gammaMu hgammaMu hgapMu
    let RU := firstExitLargePrimeResolventOfGap
      S X Y c mu gammaU hgammaU hgapU
    let errBound :=
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
        |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖ +
      2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2
    |(lam ^ 2 - primeCount) -
      finiteStarCorrection U Dset
        (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2)| ≤
      2 * |mu| * errBound + shiftBound ^ 2 := by
  dsimp only
  let b := normalizedPrimeStarFirstExit S X Y c
  let Rlam := primeStarInteriorResolventOfGap
    S X Y c lam gammaLam hgammaLam hgapLam
  let Rmu := primeStarInteriorResolventOfGap
    S X Y c mu gammaMu hgammaMu hgapMu
  let RU := firstExitLargePrimeResolventOfGap
    S X Y c mu gammaU hgammaU hgapU
  let err84 := 2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
    |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖
  let err86 := 2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2
  let rho :=
    (∑ q ∈ U,
      ⟪actualUpStarFirstExit S X Y (upTarget q) mu c0,
        actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
    (∑ q ∈ Dset,
      ⟪actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0,
        actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0⟫_ℝ)
  change |(lam ^ 2 - primeCount) -
      finiteStarCorrection U Dset
        (fun q ↦ (largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2)| ≤
    2 * |mu| * (err84 + err86) + shiftBound ^ 2
  have hstar : ⟪b, RU b⟫_ℝ = rho := by
    dsimp [b, RU, rho]
    rw [hresolvent, hsource]
    exact inner_actualFiniteBlockSums_eq U Dset upTarget downTarget
      downLeaves mu c0 hUU hUD hDD
  have h84 : |(lam - mu) - ⟪b, Rmu b⟫_ℝ| ≤ err84 := by
    exact primeCover_eigenvalue_interiorResolventReplacement
      hcut hc hd hmuval v hAv halphaMode gammaB gammaLam gammaMu eta
        hgammaB hgammaLam hgammaMu heta hgapLam hgapMu hboundaryGap hH
        hsmallBoundary
  have hmu : mu ≠ 0 := by
    rw [hmuval]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have h86 : |⟪b, Rmu b⟫_ℝ - ⟪b, RU b⟫_ℝ| ≤ err86 := by
    exact normalizedPrimeStarFirstExit_graphQuadraticFormReplacement
      hS hcut hc mu gammaMu gammaU gammaW eta hmu hgammaMu hgammaU
        hgammaW heta hgapMu hgapU hgapW hH hsmallUW
  let err := (lam - mu) - rho
  have herr : |err| ≤ err84 + err86 := by
    dsimp [err]
    rw [← hstar]
    exact (_root_.abs_sub_le _ _ _).trans (add_le_add h84 h86)
  have hdisp : lam - mu = rho + err := by
    dsimp [err]
    ring
  exact actualFinitePrimeStarRemainder_bound
    U Dset upTarget downTarget downLeaves
      lam mu primeCount boundary err (err84 + err86) shiftBound c0
      hmu hc0 hupden hdownLeaves hdownCard hdownden hboundary hdegree
      (by simpa [rho] using hdisp) herr hshift hshift0

end

end PrimeStar
