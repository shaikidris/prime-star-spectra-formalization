import PrimeStar.FiniteResolvent
import PrimeStar.FirstExitCompression
import PrimeStar.SchurRemainder

/-!
# Coordinate projections for the prime-star Feshbach split

The first-exit space is a literal coordinate subspace of the finite vertex
space.  This file turns coordinate restriction into a linear projection and
translates Lemma 8.5's entrywise graph statements into operator identities.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

local instance coordinateFeshbachPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

local instance coordinateFeshbachLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance coordinateFeshbachSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Orthogonal coordinate projection onto a finite set of Euclidean
coordinates. -/
def euclideanCoordinateProjection
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Finset ι) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i ↦ if i ∈ F then x i else 0)
  map_add' x y := by
    ext i
    by_cases hi : i ∈ F <;> simp [hi]
  map_smul' a x := by
    ext i
    by_cases hi : i ∈ F <;> simp [hi]

@[simp]
theorem euclideanCoordinateProjection_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (x : EuclideanSpace ℝ ι) (i : ι) :
    euclideanCoordinateProjection F x i = if i ∈ F then x i else 0 :=
  rfl

@[simp]
theorem euclideanCoordinateProjection_idem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (x : EuclideanSpace ℝ ι) :
    euclideanCoordinateProjection F (euclideanCoordinateProjection F x) =
      euclideanCoordinateProjection F x := by
  ext i
  by_cases hi : i ∈ F <;> simp [hi]

/-- The coordinate projection is symmetric for the Euclidean inner product. -/
theorem euclideanCoordinateProjection_isSymmetric
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Finset ι) :
    (euclideanCoordinateProjection F).IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, euclideanCoordinateProjection_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hiF : i ∈ F <;> simp [hiF]

theorem norm_euclideanCoordinateProjection_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (x : EuclideanSpace ℝ ι) :
    ‖euclideanCoordinateProjection F x‖ ≤ ‖x‖ := by
  have hsquare : ‖euclideanCoordinateProjection F x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _hi
    by_cases hiF : i ∈ F
    · simp [hiF]
    · simp [hiF, sq_nonneg]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

@[simp]
theorem euclideanCoordinateProjection_comp_eq_zero_of_disjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F G : Finset ι} (hFG : Disjoint F G)
    (x : EuclideanSpace ℝ ι) :
    euclideanCoordinateProjection F (euclideanCoordinateProjection G x) = 0 := by
  ext i
  by_cases hiF : i ∈ F
  · have hiG : i ∉ G := by
      intro hiG
      exact (Finset.disjoint_left.mp hFG) hiF hiG
    simp [hiF, hiG]
  · simp [hiF]

/-- Complementary coordinate projection. -/
def euclideanCoordinateComplementProjection
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Finset ι) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.id - euclideanCoordinateProjection F

@[simp]
theorem euclideanCoordinateComplementProjection_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (x : EuclideanSpace ℝ ι) (i : ι) :
    euclideanCoordinateComplementProjection F x i =
      if i ∈ F then 0 else x i := by
  by_cases hi : i ∈ F <;>
    simp [euclideanCoordinateComplementProjection, hi]

theorem euclideanCoordinateComplementProjection_isSymmetric
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Finset ι) :
    (euclideanCoordinateComplementProjection F).IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, euclideanCoordinateComplementProjection_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hiF : i ∈ F <;> simp [hiF, mul_comm]

theorem norm_euclideanCoordinateComplementProjection_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (x : EuclideanSpace ℝ ι) :
    ‖euclideanCoordinateComplementProjection F x‖ ≤ ‖x‖ := by
  have hsquare : ‖euclideanCoordinateComplementProjection F x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _hi
    by_cases hiF : i ∈ F
    · simp [hiF, sq_nonneg]
    · simp [hiF]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

@[simp]
theorem euclideanCoordinateComplementProjection_idem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (x : EuclideanSpace ℝ ι) :
    euclideanCoordinateComplementProjection F
        (euclideanCoordinateComplementProjection F x) =
      euclideanCoordinateComplementProjection F x := by
  ext i
  by_cases hi : i ∈ F <;> simp [hi]

theorem euclideanCoordinateProjection_add_complement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (x : EuclideanSpace ℝ ι) :
    euclideanCoordinateProjection F x +
      euclideanCoordinateComplementProjection F x = x := by
  simp [euclideanCoordinateComplementProjection]

/-- For symmetric operators and symmetric coordinate projections, equality of
one off-diagonal block implies equality of its transposed block. -/
theorem reverseBlock_eq_of_forwardBlock_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q A H : E →ₗ[ℝ] E)
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hforward : P.comp (A.comp Q) = P.comp (H.comp Q)) :
    Q.comp (A.comp P) = Q.comp (H.comp P) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  calc
    ⟪y, Q (A (P x))⟫_ℝ = ⟪Q y, A (P x)⟫_ℝ := (hQ _ _).symm
    _ = ⟪A (Q y), P x⟫_ℝ := (hA _ _).symm
    _ = ⟪P (A (Q y)), x⟫_ℝ := (hP _ _).symm
    _ = ⟪P (H (Q y)), x⟫_ℝ := by
      rw [show P (A (Q y)) = P (H (Q y)) by
        exact LinearMap.congr_fun hforward y]
    _ = ⟪H (Q y), P x⟫_ℝ := hP _ _
    _ = ⟪Q y, H (P x)⟫_ℝ := hH _ _
    _ = ⟪y, Q (H (P x))⟫_ℝ := hQ _ _

/-- Coordinate projection onto the canonical first-exit star union. -/
def firstExitCompressionProjection
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  euclideanCoordinateProjection (firstExitCompressionSupport S X Y c)

@[simp]
theorem firstExitCompressionProjection_apply
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (x : EuclideanSpace ℝ (Vertex S X)) (v : Vertex S X) :
    firstExitCompressionProjection S X Y c x v =
      if v ∈ firstExitCompressionSupport S X Y c then x v else 0 :=
  rfl

/-- Coordinate projection onto the original closed large-prime star. -/
def primeStarBoundaryProjection
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  euclideanCoordinateProjection (largePrimeStarSupport S X Y c)

/-- Coordinates outside both the original boundary star and the canonical
first-exit compression. -/
def firstExitComplementSupport
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) : Finset (Vertex S X) :=
  Finset.univ \ (largePrimeStarSupport S X Y c ∪
    firstExitCompressionSupport S X Y c)

/-- Coordinate projection onto the remaining `W` sector. -/
def firstExitComplementProjection
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  euclideanCoordinateProjection (firstExitComplementSupport S X Y c)

@[simp]
theorem primeStarBoundaryProjection_apply
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (x : EuclideanSpace ℝ (Vertex S X)) (v : Vertex S X) :
    primeStarBoundaryProjection S X Y c x v =
      if v ∈ largePrimeStarSupport S X Y c then x v else 0 :=
  rfl

@[simp]
theorem primeStarBoundaryProjection_idem
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    primeStarBoundaryProjection S X Y c
        (primeStarBoundaryProjection S X Y c x) =
      primeStarBoundaryProjection S X Y c x :=
  euclideanCoordinateProjection_idem _ _

@[simp]
theorem firstExitComplementProjection_apply
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (x : EuclideanSpace ℝ (Vertex S X)) (v : Vertex S X) :
    firstExitComplementProjection S X Y c x v =
      if v ∈ firstExitComplementSupport S X Y c then x v else 0 :=
  rfl

/-- Boundary, first-exit, and remaining-interior coordinates form an exact
partition of the ambient finite vertex space. -/
theorem boundary_add_firstExit_add_complement
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    primeStarBoundaryProjection S X Y c x +
        firstExitCompressionProjection S X Y c x +
      firstExitComplementProjection S X Y c x = x := by
  have hdisj := disjoint_firstExitCompressionSupport_largePrimeStarSupport
    (S := S) (X := X) (Y := Y) (c := c) hcut hc
  ext v
  by_cases hvB : v ∈ largePrimeStarSupport S X Y c
  · have hvU : v ∉ firstExitCompressionSupport S X Y c := by
      intro hvU
      exact (Finset.disjoint_left.mp hdisj) hvU hvB
    have hvW : v ∉ firstExitComplementSupport S X Y c := by
      simp [firstExitComplementSupport, hvB]
    simp [hvB, hvU, hvW]
  · by_cases hvU : v ∈ firstExitCompressionSupport S X Y c
    · have hvW : v ∉ firstExitComplementSupport S X Y c := by
        simp [firstExitComplementSupport, hvU]
      simp [hvB, hvU, hvW]
    · have hvW : v ∈ firstExitComplementSupport S X Y c := by
        simp [firstExitComplementSupport, hvB, hvU]
      simp [hvB, hvU, hvW]

@[simp]
theorem firstExitCompressionProjection_boundary_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitCompressionProjection S X Y c
      (primeStarBoundaryProjection S X Y c x) = 0 := by
  have hdisj := disjoint_firstExitCompressionSupport_largePrimeStarSupport
    (S := S) (X := X) (Y := Y) (c := c) hcut hc
  ext v
  by_cases hvU : v ∈ firstExitCompressionSupport S X Y c
  · have hvB : v ∉ largePrimeStarSupport S X Y c := by
      intro hvB
      exact (Finset.disjoint_left.mp hdisj) hvU hvB
    simp [hvU, hvB]
  · simp [hvU]

@[simp]
theorem primeStarBoundaryProjection_firstExit_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    primeStarBoundaryProjection S X Y c
      (firstExitCompressionProjection S X Y c x) = 0 := by
  have hdisj := disjoint_firstExitCompressionSupport_largePrimeStarSupport
    (S := S) (X := X) (Y := Y) (c := c) hcut hc
  ext v
  by_cases hvB : v ∈ largePrimeStarSupport S X Y c
  · have hvU : v ∉ firstExitCompressionSupport S X Y c := by
      intro hvU
      exact (Finset.disjoint_left.mp hdisj) hvU hvB
    simp [hvB, hvU]
  · simp [hvB]

theorem disjoint_boundary_firstExitComplementSupport
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} :
    Disjoint (largePrimeStarSupport S X Y c)
      (firstExitComplementSupport S X Y c) := by
  rw [Finset.disjoint_left]
  intro v hvB hvW
  exact (Finset.mem_sdiff.mp hvW).2 (Finset.mem_union_left _ hvB)

theorem disjoint_firstExitCompression_complementSupport
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} :
    Disjoint (firstExitCompressionSupport S X Y c)
      (firstExitComplementSupport S X Y c) := by
  rw [Finset.disjoint_left]
  intro v hvU hvW
  exact (Finset.mem_sdiff.mp hvW).2 (Finset.mem_union_right _ hvU)

/-- Interior projection after deleting the original boundary star. -/
def primeStarInteriorProjection
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  euclideanCoordinateComplementProjection
    (largePrimeStarSupport S X Y c)

@[simp]
theorem primeStarInteriorProjection_apply
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (x : EuclideanSpace ℝ (Vertex S X)) (v : Vertex S X) :
    primeStarInteriorProjection S X Y c x v =
      if v ∈ largePrimeStarSupport S X Y c then 0 else x v := by
  exact euclideanCoordinateComplementProjection_apply _ _ _

@[simp]
theorem primeStarBoundaryProjection_interior_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    primeStarBoundaryProjection S X Y c
      (primeStarInteriorProjection S X Y c x) = 0 := by
  ext v
  by_cases hvB : v ∈ largePrimeStarSupport S X Y c <;> simp [hvB]

theorem primeStarInteriorProjection_eq_of_boundary_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    {x : EuclideanSpace ℝ (Vertex S X)}
    (hx : primeStarBoundaryProjection S X Y c x = 0) :
    primeStarInteriorProjection S X Y c x = x := by
  ext v
  by_cases hvB : v ∈ largePrimeStarSupport S X Y c
  · have hxv := congrFun (congrArg WithLp.ofLp hx) v
    simp [hvB] at hxv
    simp [hvB, hxv]
  · simp [hvB]

theorem primeStarInteriorProjection_eq_firstExit_add_complement
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    primeStarInteriorProjection S X Y c x =
      firstExitCompressionProjection S X Y c x +
        firstExitComplementProjection S X Y c x := by
  ext v
  by_cases hvB : v ∈ largePrimeStarSupport S X Y c
  · have hvU : v ∉ firstExitCompressionSupport S X Y c := by
      intro hvU
      exact (Finset.disjoint_left.mp
        (disjoint_firstExitCompressionSupport_largePrimeStarSupport hcut hc))
          hvU hvB
    have hvW : v ∉ firstExitComplementSupport S X Y c := by
      simp [firstExitComplementSupport, hvB]
    simp [hvB, hvU, hvW]
  · by_cases hvU : v ∈ firstExitCompressionSupport S X Y c
    · have hvW : v ∉ firstExitComplementSupport S X Y c := by
        simp [firstExitComplementSupport, hvU]
      simp [hvB, hvU, hvW]
    · have hvW : v ∈ firstExitComplementSupport S X Y c := by
        simp [firstExitComplementSupport, hvB, hvU]
      simp [hvB, hvU, hvW]

@[simp]
theorem firstExitCompressionProjection_interior
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitCompressionProjection S X Y c
      (primeStarInteriorProjection S X Y c x) =
        firstExitCompressionProjection S X Y c x := by
  have hdisj := disjoint_firstExitCompressionSupport_largePrimeStarSupport
    (S := S) (X := X) (Y := Y) (c := c) hcut hc
  ext v
  by_cases hvU : v ∈ firstExitCompressionSupport S X Y c
  · have hvB : v ∉ largePrimeStarSupport S X Y c := by
      intro hvB
      exact (Finset.disjoint_left.mp hdisj) hvU hvB
    simp [hvU, hvB]
  · simp [hvU]

@[simp]
theorem firstExitComplementProjection_interior
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitComplementProjection S X Y c
      (primeStarInteriorProjection S X Y c x) =
        firstExitComplementProjection S X Y c x := by
  ext v
  by_cases hvW : v ∈ firstExitComplementSupport S X Y c
  · have hvB : v ∉ largePrimeStarSupport S X Y c := by
      exact fun hvB ↦ (Finset.mem_sdiff.mp hvW).2
        (Finset.mem_union_left _ hvB)
    simp [hvW, hvB]
  · simp [hvW]

@[simp]
theorem firstExitCompressionProjection_complement_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitCompressionProjection S X Y c
      (firstExitComplementProjection S X Y c x) = 0 := by
  exact euclideanCoordinateProjection_comp_eq_zero_of_disjoint
    disjoint_firstExitCompression_complementSupport x

@[simp]
theorem firstExitComplementProjection_compression_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitComplementProjection S X Y c
      (firstExitCompressionProjection S X Y c x) = 0 := by
  exact euclideanCoordinateProjection_comp_eq_zero_of_disjoint
    disjoint_firstExitCompression_complementSupport.symm x

@[simp]
theorem firstExitCompressionProjection_idem
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitCompressionProjection S X Y c
      (firstExitCompressionProjection S X Y c x) =
        firstExitCompressionProjection S X Y c x :=
  euclideanCoordinateProjection_idem _ _

@[simp]
theorem firstExitComplementProjection_idem
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitComplementProjection S X Y c
      (firstExitComplementProjection S X Y c x) =
        firstExitComplementProjection S X Y c x :=
  euclideanCoordinateProjection_idem _ _

@[simp]
theorem firstExitCompressionComplementProjection_on_W
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    euclideanCoordinateComplementProjection
        (firstExitCompressionSupport S X Y c)
        (firstExitComplementProjection S X Y c x) =
      firstExitComplementProjection S X Y c x := by
  ext v
  by_cases hvW : v ∈ firstExitComplementSupport S X Y c
  · have hvU : v ∉ firstExitCompressionSupport S X Y c := by
      intro hvU
      exact (Finset.disjoint_left.mp
        disjoint_firstExitCompression_complementSupport) hvU hvW
    simp [hvW, hvU]
  · simp [hvW]

/-- On the first-exit coordinate space, compressing the full adjacency is
exactly the same as compressing the large-prime star forest. -/
theorem firstExitCompression_primeCover_eq_largePrime
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitCompressionProjection S X Y c
        (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
          (firstExitCompressionProjection S X Y c x)) =
      firstExitCompressionProjection S X Y c
        (Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
          (firstExitCompressionProjection S X Y c x)) := by
  ext v
  by_cases hv : v ∈ firstExitCompressionSupport S X Y c
  · simp only [firstExitCompressionProjection_apply, if_pos hv]
    rw [Matrix.toLpLin_toLp 2 2, Matrix.toLpLin_toLp 2 2]
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro w _hw
    by_cases hwF : w ∈ firstExitCompressionSupport S X Y c
    · rw [primeCover_adjMatrix_eq_largePrime_on_firstExitCompressionSupport
        hS hcut hc hv hwF]
    · simp [firstExitCompressionProjection_apply, hwF]
  · simp [firstExitCompressionProjection_apply, hv]

/-- Across the first-exit boundary, the full adjacency block is exactly the
small-prime block. -/
theorem firstExitCompression_boundary_primeCover_eq_smallPrime
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitCompressionProjection S X Y c
        (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
          (euclideanCoordinateComplementProjection
            (firstExitCompressionSupport S X Y c) x)) =
      firstExitCompressionProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (euclideanCoordinateComplementProjection
            (firstExitCompressionSupport S X Y c) x)) := by
  ext v
  by_cases hv : v ∈ firstExitCompressionSupport S X Y c
  · simp only [firstExitCompressionProjection_apply, if_pos hv]
    rw [Matrix.toLpLin_toLp 2 2, Matrix.toLpLin_toLp 2 2]
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro w _hw
    by_cases hwF : w ∈ firstExitCompressionSupport S X Y c
    · simp [euclideanCoordinateComplementProjection_apply, hwF]
    · rw [show (primeCoverGraph S X).adjMatrix ℝ v w =
          (smallPrimeGraph S X Y).adjMatrix ℝ v w by
        have hp := primeCover_boundarySubmatrix_eq_smallPrime
          (S := S) (X := X) (Y := Y) (c := c)
          (fun _ : Unit ↦ v) (fun _ : Unit ↦ w) hcut
          (fun _ ↦ hv) (fun _ ↦ hwF)
        exact congrFun (congrFun hp ()) ()]
  · simp [firstExitCompressionProjection_apply, hv]

/-- The literal large-prime direct-sum operator on the canonical first-exit
compression, extended by zero to the ambient vertex space. -/
def firstExitLargePrimeCompressionOperator
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  let P := firstExitCompressionProjection S X Y c
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  P.comp (L.comp P)

@[simp]
theorem firstExitLargePrimeCompressionOperator_apply
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitLargePrimeCompressionOperator S X Y c x =
      firstExitCompressionProjection S X Y c
        (Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
          (firstExitCompressionProjection S X Y c x)) :=
  rfl

/-- A vector supported on the canonical first-exit compression is fixed by
the corresponding coordinate projection. -/
theorem firstExitCompressionProjection_eq_of_supported
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (x : EuclideanSpace ℝ (Vertex S X))
    (hx : ∀ v, v ∉ firstExitCompressionSupport S X Y c → x v = 0) :
    firstExitCompressionProjection S X Y c x = x := by
  ext v
  by_cases hv : v ∈ firstExitCompressionSupport S X Y c
  · simp [firstExitCompressionProjection_apply, hv]
  · simp [firstExitCompressionProjection_apply, hv, hx v hv]

/-- Large-prime adjacency preserves the canonical first-exit compression. -/
theorem largePrime_toEuclideanLin_eq_zero_outside_firstExitCompression
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (x : EuclideanSpace ℝ (Vertex S X))
    (hx : ∀ v, v ∉ firstExitCompressionSupport S X Y c → x v = 0)
    {v : Vertex S X} (hv : v ∉ firstExitCompressionSupport S X Y c) :
    Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x v = 0 := by
  rw [Matrix.toLpLin_toLp 2 2]
  rw [Matrix.toLin'_apply]
  change ((largePrimeGraph S X Y).adjMatrix ℝ).mulVec
      (fun w ↦ x w) v = 0
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  apply Finset.sum_eq_zero
  intro w hw
  have hvw : LargePrimeAdj S Y v w := by simpa using hw
  have hwout : w ∉ firstExitCompressionSupport S X Y c := by
    intro hwC
    exact hv (firstExitCompressionSupport_closed_under_largePrimeAdj
      hcut hwC (largePrimeAdj_symm hvw))
  exact hx w hwout

/-- On a vector already supported in the canonical first-exit compression,
the compressed large-prime operator is the literal large-prime adjacency. -/
theorem firstExitLargePrimeCompressionOperator_eq_of_supported
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (x : EuclideanSpace ℝ (Vertex S X))
    (hx : ∀ v, v ∉ firstExitCompressionSupport S X Y c → x v = 0) :
    firstExitLargePrimeCompressionOperator S X Y c x =
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x := by
  rw [firstExitLargePrimeCompressionOperator_apply,
    firstExitCompressionProjection_eq_of_supported x hx]
  apply firstExitCompressionProjection_eq_of_supported
  intro v hv
  exact largePrime_toEuclideanLin_eq_zero_outside_firstExitCompression
    hcut x hx hv

/-- Prime-cover adjacency compressed to the complement of the original
boundary star. -/
def primeStarInteriorPrimeCoverOperator
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  let P := primeStarInteriorProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  P.comp (A.comp P)

/-- Prime-cover adjacency compressed to the original closed star. -/
def primeStarBoundaryPrimeCoverOperator
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  let P := primeStarBoundaryProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  P.comp (A.comp P)

/-- Coupling from the original boundary star into its coordinate interior. -/
def primeStarToInteriorPrimeCoverOperator
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  let PB := primeStarBoundaryProjection S X Y c
  let PI := primeStarInteriorProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  PI.comp (A.comp PB)

/-- Coupling from the coordinate interior back into the original boundary
star. -/
def primeStarFromInteriorPrimeCoverOperator
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  let PB := primeStarBoundaryProjection S X Y c
  let PI := primeStarInteriorProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  PB.comp (A.comp PI)

/-- The boundary-to-interior block of the full adjacency is exactly the
corresponding block of the small-prime remainder. -/
theorem primeStarToInteriorPrimeCoverOperator_eq_smallPrime
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    primeStarToInteriorPrimeCoverOperator S X Y c x =
      primeStarInteriorProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (primeStarBoundaryProjection S X Y c x)) := by
  ext v
  by_cases hvB : v ∈ largePrimeStarSupport S X Y c
  · simp [primeStarToInteriorPrimeCoverOperator,
      primeStarInteriorProjection_apply, hvB]
  · simp only [primeStarToInteriorPrimeCoverOperator,
      LinearMap.comp_apply, primeStarInteriorProjection_apply, if_neg hvB]
    rw [Matrix.toLpLin_toLp 2 2, Matrix.toLpLin_toLp 2 2]
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro w _hw
    by_cases hwB : w ∈ largePrimeStarSupport S X Y c
    · simp only [primeStarBoundaryProjection_apply, if_pos hwB]
      have hnotLarge : ¬LargePrimeAdj S Y v w := by
        intro hvw
        have hwv : LargePrimeAdj S Y w v := largePrimeAdj_symm hvw
        exact hvB (largePrimeStarSupport_closed hcut hc hwB hwv)
      by_cases hp : PrimeCoverAdj v w
      · simp [SimpleGraph.adjMatrix_apply, hp, hnotLarge, smallPrimeGraph_adj]
      · simp [SimpleGraph.adjMatrix_apply, hp, smallPrimeGraph_adj]
    · simp [primeStarBoundaryProjection_apply, hwB]

/-- By symmetry, the reverse boundary block is also exactly small-prime. -/
theorem primeStarFromInteriorPrimeCoverOperator_eq_smallPrime
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    primeStarFromInteriorPrimeCoverOperator S X Y c x =
      primeStarBoundaryProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (primeStarInteriorProjection S X Y c x)) := by
  let PB := primeStarBoundaryProjection S X Y c
  let PI := primeStarInteriorProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hPB : PB.IsSymmetric :=
    euclideanCoordinateProjection_isSymmetric
      (largePrimeStarSupport S X Y c)
  have hPI : PI.IsSymmetric :=
    euclideanCoordinateComplementProjection_isSymmetric
      (largePrimeStarSupport S X Y c)
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))
  have hH : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hforward : PI.comp (A.comp PB) = PI.comp (H.comp PB) := by
    apply LinearMap.ext
    intro y
    exact primeStarToInteriorPrimeCoverOperator_eq_smallPrime hcut hc y
  have hreverse := reverseBlock_eq_of_forwardBlock_eq
    PI PB A H hPI hPB hA hH hforward
  exact LinearMap.congr_fun hreverse x

theorem norm_primeStarToInteriorPrimeCoverOperator_le
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    ‖primeStarToInteriorPrimeCoverOperator S X Y c x‖ ≤ eta * ‖x‖ := by
  rw [primeStarToInteriorPrimeCoverOperator_eq_smallPrime hcut hc]
  calc
    ‖primeStarInteriorProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (primeStarBoundaryProjection S X Y c x))‖ ≤
        ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (primeStarBoundaryProjection S X Y c x)‖ :=
      norm_euclideanCoordinateComplementProjection_le
        (largePrimeStarSupport S X Y c) _
    _ ≤ eta * ‖primeStarBoundaryProjection S X Y c x‖ := hH _
    _ ≤ eta * ‖x‖ := mul_le_mul_of_nonneg_left
      (norm_euclideanCoordinateProjection_le
        (largePrimeStarSupport S X Y c) x) heta

theorem norm_primeStarFromInteriorPrimeCoverOperator_le
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    ‖primeStarFromInteriorPrimeCoverOperator S X Y c x‖ ≤ eta * ‖x‖ := by
  rw [primeStarFromInteriorPrimeCoverOperator_eq_smallPrime hcut hc]
  calc
    ‖primeStarBoundaryProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (primeStarInteriorProjection S X Y c x))‖ ≤
        ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (primeStarInteriorProjection S X Y c x)‖ :=
      norm_euclideanCoordinateProjection_le _ _
    _ ≤ eta * ‖primeStarInteriorProjection S X Y c x‖ := hH _
    _ ≤ eta * ‖x‖ := mul_le_mul_of_nonneg_left
      (norm_euclideanCoordinateComplementProjection_le
        (largePrimeStarSupport S X Y c) x) heta

/-- `W`-to-`W` block of the interior prime-cover adjacency. -/
def firstExitComplementPrimeCoverOperator
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  let P := firstExitComplementProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  P.comp (A.comp P)

/-- Coupling from the first-exit `U` sector into `W`. -/
def firstExitToComplementPrimeCoverOperator
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  let PU := firstExitCompressionProjection S X Y c
  let PW := firstExitComplementProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  PW.comp (A.comp PU)

/-- Coupling from `W` back into the first-exit `U` sector. -/
def firstExitFromComplementPrimeCoverOperator
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  let PU := firstExitCompressionProjection S X Y c
  let PW := firstExitComplementProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  PU.comp (A.comp PW)

theorem firstExitFromComplementPrimeCoverOperator_eq_smallPrime
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitFromComplementPrimeCoverOperator S X Y c x =
      firstExitCompressionProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (firstExitComplementProjection S X Y c x)) := by
  change firstExitCompressionProjection S X Y c
      (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
        (firstExitComplementProjection S X Y c x)) = _
  have h := firstExitCompression_boundary_primeCover_eq_smallPrime
    (S := S) (X := X) (Y := Y) (c := c) hcut
      (firstExitComplementProjection S X Y c x)
  rw [firstExitCompressionComplementProjection_on_W] at h
  exact h

theorem firstExitToComplementPrimeCoverOperator_eq_smallPrime
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitToComplementPrimeCoverOperator S X Y c x =
      firstExitComplementProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (firstExitCompressionProjection S X Y c x)) := by
  let PU := firstExitCompressionProjection S X Y c
  let PW := firstExitComplementProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  have hPU : PU.IsSymmetric :=
    euclideanCoordinateProjection_isSymmetric
      (firstExitCompressionSupport S X Y c)
  have hPW : PW.IsSymmetric :=
    euclideanCoordinateProjection_isSymmetric
      (firstExitComplementSupport S X Y c)
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))
  have hH : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hforward : PU.comp (A.comp PW) = PU.comp (H.comp PW) := by
    apply LinearMap.ext
    intro y
    exact firstExitFromComplementPrimeCoverOperator_eq_smallPrime hcut y
  have hreverse := reverseBlock_eq_of_forwardBlock_eq
    PU PW A H hPU hPW hA hH hforward
  exact LinearMap.congr_fun hreverse x

theorem norm_firstExitFromComplementPrimeCoverOperator_le
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (eta : ℝ) (heta : 0 ≤ eta)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    ‖firstExitFromComplementPrimeCoverOperator S X Y c x‖ ≤ eta * ‖x‖ := by
  rw [firstExitFromComplementPrimeCoverOperator_eq_smallPrime hcut]
  calc
    ‖firstExitCompressionProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (firstExitComplementProjection S X Y c x))‖ ≤
        ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (firstExitComplementProjection S X Y c x)‖ :=
      norm_euclideanCoordinateProjection_le _ _
    _ ≤ eta * ‖firstExitComplementProjection S X Y c x‖ := hH _
    _ ≤ eta * ‖x‖ := mul_le_mul_of_nonneg_left
      (norm_euclideanCoordinateProjection_le _ _) heta

theorem norm_firstExitToComplementPrimeCoverOperator_le
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (eta : ℝ) (heta : 0 ≤ eta)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    ‖firstExitToComplementPrimeCoverOperator S X Y c x‖ ≤ eta * ‖x‖ := by
  rw [firstExitToComplementPrimeCoverOperator_eq_smallPrime hcut]
  calc
    ‖firstExitComplementProjection S X Y c
        (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (firstExitCompressionProjection S X Y c x))‖ ≤
        ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (firstExitCompressionProjection S X Y c x)‖ :=
      norm_euclideanCoordinateProjection_le _ _
    _ ≤ eta * ‖firstExitCompressionProjection S X Y c x‖ := hH _
    _ ≤ eta * ‖x‖ := mul_le_mul_of_nonneg_left
      (norm_euclideanCoordinateProjection_le _ _) heta

theorem primeStarInteriorPrimeCoverOperator_isSymmetric
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    (primeStarInteriorPrimeCoverOperator S X Y c).IsSymmetric := by
  let P := primeStarInteriorProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  have hP : P.IsSymmetric :=
    euclideanCoordinateComplementProjection_isSymmetric
      (largePrimeStarSupport S X Y c)
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))
  intro x y
  change ⟪P (A (P x)), y⟫_ℝ = ⟪x, P (A (P y))⟫_ℝ
  calc
    ⟪P (A (P x)), y⟫_ℝ = ⟪A (P x), P y⟫_ℝ := hP _ _
    _ = ⟪P x, A (P y)⟫_ℝ := hA _ _
    _ = ⟪x, P (A (P y))⟫_ℝ := hP _ _

theorem firstExitComplementPrimeCoverOperator_isSymmetric
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    (firstExitComplementPrimeCoverOperator S X Y c).IsSymmetric := by
  let P := firstExitComplementProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  have hP : P.IsSymmetric :=
    euclideanCoordinateProjection_isSymmetric
      (firstExitComplementSupport S X Y c)
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))
  intro x y
  change ⟪P (A (P x)), y⟫_ℝ = ⟪x, P (A (P y))⟫_ℝ
  calc
    ⟪P (A (P x)), y⟫_ℝ = ⟪A (P x), P y⟫_ℝ := hP _ _
    _ = ⟪P x, A (P y)⟫_ℝ := hA _ _
    _ = ⟪x, P (A (P y))⟫_ℝ := hP _ _

/-- Interior resolvent at energy `mu`, constructed from the two-sided
interior gap of Lemma 8.3. -/
def primeStarInteriorResolventOfGap
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  finiteResolventOfGap (primeStarInteriorPrimeCoverOperator S X Y c)
    mu gamma hgamma hgap

/-- Complement resolvent used to eliminate `W`. -/
def firstExitComplementResolventOfGap
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  finiteResolventOfGap (firstExitComplementPrimeCoverOperator S X Y c)
    mu gamma hgamma hgap

@[simp]
theorem primeStarInteriorResolventOfGap_apply_inverse
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    mu • primeStarInteriorResolventOfGap S X Y c mu gamma hgamma hgap x -
        primeStarInteriorPrimeCoverOperator S X Y c
          (primeStarInteriorResolventOfGap S X Y c mu gamma hgamma hgap x) = x := by
  exact finiteResolventOfGap_apply_inverse _ _ _ _ _ x

theorem primeStarInteriorResolventOfGap_mem_interior
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hmu : mu ≠ 0) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (b : EuclideanSpace ℝ (Vertex S X))
    (hb : primeStarBoundaryProjection S X Y c b = 0) :
    primeStarInteriorProjection S X Y c
        (primeStarInteriorResolventOfGap S X Y c mu gamma hgamma hgap b) =
      primeStarInteriorResolventOfGap S X Y c mu gamma hgamma hgap b := by
  let z := primeStarInteriorResolventOfGap S X Y c mu gamma hgamma hgap b
  let PB := primeStarBoundaryProjection S X Y c
  have hsolve : mu • z - primeStarInteriorPrimeCoverOperator S X Y c z = b :=
    primeStarInteriorResolventOfGap_apply_inverse
      S X Y c mu gamma hgamma hgap b
  have hBC : PB (primeStarInteriorPrimeCoverOperator S X Y c z) = 0 := by
    change PB (primeStarInteriorProjection S X Y c
      (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
        (primeStarInteriorProjection S X Y c z))) = 0
    exact primeStarBoundaryProjection_interior_eq_zero _
  have hPB := congrArg PB hsolve
  have hmuPB : mu • PB z = 0 := by
    rw [map_sub, map_smul, hBC, sub_zero, hb] at hPB
    exact hPB
  have hPB0 : PB z = 0 := (smul_eq_zero.mp hmuPB).resolve_left hmu
  exact primeStarInteriorProjection_eq_of_boundary_eq_zero hPB0

@[simp]
theorem firstExitComplementResolventOfGap_shift_apply
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitComplementResolventOfGap S X Y c mu gamma hgamma hgap
        (mu • x - firstExitComplementPrimeCoverOperator S X Y c x) = x := by
  exact finiteResolventOfGap_shift_apply _ _ _ _ _ x

theorem norm_firstExitComplementResolventOfGap_apply_le
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    ‖firstExitComplementResolventOfGap S X Y c mu gamma hgamma hgap x‖ ≤
      gamma⁻¹ * ‖x‖ := by
  exact norm_finiteResolventOfGap_apply_le _ _ _ _ _ x

/-- Exact `U/W` equations for the resolvent of the interior prime-cover
operator.  This is the literal block algebra in Lemma 8.5. -/
theorem primeStarInteriorResolvent_blockEquations
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (mu : ℝ) (z b : EuclideanSpace ℝ (Vertex S X))
    (hzInterior : primeStarInteriorProjection S X Y c z = z)
    (hbU : firstExitCompressionProjection S X Y c b = b)
    (hsolve : mu • z -
        primeStarInteriorPrimeCoverOperator S X Y c z = b) :
    let xU := firstExitCompressionProjection S X Y c z
    let xW := firstExitComplementProjection S X Y c z
    mu • xU - firstExitLargePrimeCompressionOperator S X Y c xU -
        firstExitFromComplementPrimeCoverOperator S X Y c xW = b ∧
      mu • xW - firstExitComplementPrimeCoverOperator S X Y c xW =
        firstExitToComplementPrimeCoverOperator S X Y c xU := by
  dsimp only
  let PU := firstExitCompressionProjection S X Y c
  let PW := firstExitComplementProjection S X Y c
  let PI := primeStarInteriorProjection S X Y c
  let A := Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  have hzsplit : z = PU z + PW z := by
    have h := primeStarInteriorProjection_eq_firstExit_add_complement
      hcut hc z
    rw [hzInterior] at h
    exact h
  have hCU : PU (primeStarInteriorPrimeCoverOperator S X Y c z) = PU (A z) := by
    change PU (PI (A (PI z))) = PU (A z)
    rw [hzInterior]
    exact firstExitCompressionProjection_interior hcut hc (A z)
  have hCW : PW (primeStarInteriorPrimeCoverOperator S X Y c z) = PW (A z) := by
    change PW (PI (A (PI z))) = PW (A z)
    rw [hzInterior]
    exact firstExitComplementProjection_interior (A z)
  have hsolveU := congrArg PU hsolve
  have hsolveW := congrArg PW hsolve
  have hUU : PU (A (PU z)) = PU (L (PU z)) := by
    exact firstExitCompression_primeCover_eq_largePrime hS hcut hc z
  have hsolveU' : mu • PU z - PU (A z) = b := by
    calc
      mu • PU z - PU (A z) =
          PU (mu • z - primeStarInteriorPrimeCoverOperator S X Y c z) := by
        rw [map_sub, map_smul, hCU]
      _ = PU b := congrArg PU hsolve
      _ = b := hbU
  have hbW : PW b = 0 := by
    rw [← hbU]
    exact firstExitComplementProjection_compression_eq_zero b
  have hsolveW' : mu • PW z - PW (A z) = 0 := by
    calc
      mu • PW z - PW (A z) =
          PW (mu • z - primeStarInteriorPrimeCoverOperator S X Y c z) := by
        rw [map_sub, map_smul, hCW]
      _ = PW b := congrArg PW hsolve
      _ = 0 := hbW
  have hAzU : PU (A z) = PU (A (PU z)) + PU (A (PW z)) := by
    calc
      PU (A z) = PU (A (PU z + PW z)) :=
        congrArg (fun t ↦ PU (A t)) hzsplit
      _ = PU (A (PU z)) + PU (A (PW z)) := by rw [map_add, map_add]
  have hAzW : PW (A z) = PW (A (PU z)) + PW (A (PW z)) := by
    calc
      PW (A z) = PW (A (PU z + PW z)) :=
        congrArg (fun t ↦ PW (A t)) hzsplit
      _ = PW (A (PU z)) + PW (A (PW z)) := by rw [map_add, map_add]
  constructor
  · change mu • PU z - PU (L (PU (PU z))) -
        PU (A (PW (PW z))) = b
    rw [firstExitCompressionProjection_idem,
      firstExitComplementProjection_idem]
    calc
      mu • PU z - PU (L (PU z)) - PU (A (PW z)) =
          mu • PU z - (PU (A (PU z)) + PU (A (PW z))) := by
        rw [← hUU]
        abel
      _ = mu • PU z - PU (A z) := by rw [hAzU]
      _ = b := hsolveU'
  · change mu • PW z - PW (A (PW (PW z))) = PW (A (PU (PU z)))
    rw [firstExitCompressionProjection_idem,
      firstExitComplementProjection_idem]
    calc
      mu • PW z - PW (A (PW z)) =
          (mu • PW z - PW (A z)) + PW (A (PU z)) := by
        rw [hAzW]
        abel
      _ = PW (A (PU z)) := by rw [hsolveW', zero_add]

theorem firstExitLargePrimeCompressionOperator_isSymmetric
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    (firstExitLargePrimeCompressionOperator S X Y c).IsSymmetric := by
  let P := firstExitCompressionProjection S X Y c
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  have hP : P.IsSymmetric :=
    euclideanCoordinateProjection_isSymmetric
      (firstExitCompressionSupport S X Y c)
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  intro x y
  change ⟪P (L (P x)), y⟫_ℝ = ⟪x, P (L (P y))⟫_ℝ
  calc
    ⟪P (L (P x)), y⟫_ℝ = ⟪L (P x), P y⟫_ℝ := hP _ _
    _ = ⟪P x, L (P y)⟫_ℝ := hL _ _
    _ = ⟪x, P (L (P y))⟫_ℝ := hP _ _

/-- Literal reduced resolvent of the first-exit star union, constructed from
a positive lower gap rather than supplied as an abstract inverse. -/
def firstExitLargePrimeResolventOfGap
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ]
      EuclideanSpace ℝ (Vertex S X) :=
  finiteResolventOfGap
    (firstExitLargePrimeCompressionOperator S X Y c)
      mu gamma hgamma hgap

@[simp]
theorem firstExitLargePrimeResolventOfGap_shift_apply
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap
        (mu • x - firstExitLargePrimeCompressionOperator S X Y c x) = x := by
  exact finiteResolventOfGap_shift_apply _ _ _ _ _ x

@[simp]
theorem firstExitLargePrimeResolventOfGap_apply_inverse
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    mu • firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap x -
        firstExitLargePrimeCompressionOperator S X Y c
          (firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap x) = x := by
  exact finiteResolventOfGap_apply_inverse _ _ _ _ _ x

theorem norm_firstExitLargePrimeResolventOfGap_apply_le
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    ‖firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap x‖ ≤
      gamma⁻¹ * ‖x‖ := by
  exact norm_finiteResolventOfGap_apply_le _ _ _ _ _ x

theorem firstExitLargePrimeResolventOfGap_isSymmetric
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖) :
    (firstExitLargePrimeResolventOfGap
      S X Y c mu gamma hgamma hgap).IsSymmetric := by
  exact finiteResolventOfGap_isSymmetric _ _ _ _ _
    (firstExitLargePrimeCompressionOperator_isSymmetric S X Y c)

/-- Fully instantiated finite Feshbach identity for the prime-cover interior.
All three inverses are the canonical operators constructed from lower gaps;
the two block equations come from the literal coordinate decomposition. -/
theorem primeStarInteriorResolvent_firstExitFeshbachIdentity
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (mu gammaI gammaU gammaW : ℝ) (hmu : mu ≠ 0)
    (hgammaI : 0 < gammaI) (hgammaU : 0 < gammaU)
    (hgammaW : 0 < gammaW)
    (hgapI : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaI * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hgapU : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaU * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖)
    (hgapW : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaW * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖)
    (b : EuclideanSpace ℝ (Vertex S X))
    (hbU : firstExitCompressionProjection S X Y c b = b) :
    let z := primeStarInteriorResolventOfGap
      S X Y c mu gammaI hgammaI hgapI b
    let xU := firstExitCompressionProjection S X Y c z
    let RU := firstExitLargePrimeResolventOfGap
      S X Y c mu gammaU hgammaU hgapU
    let RW := firstExitComplementResolventOfGap
      S X Y c mu gammaW hgammaW hgapW
    let K := firstExitFromComplementPrimeCoverOperator S X Y c
    let J := firstExitToComplementPrimeCoverOperator S X Y c
    xU = RU b + RU (feshbachEffectiveInteraction K RW J mu mu xU) := by
  dsimp only
  let z := primeStarInteriorResolventOfGap
    S X Y c mu gammaI hgammaI hgapI b
  let xU := firstExitCompressionProjection S X Y c z
  let xW := firstExitComplementProjection S X Y c z
  let RU := firstExitLargePrimeResolventOfGap
    S X Y c mu gammaU hgammaU hgapU
  let RW := firstExitComplementResolventOfGap
    S X Y c mu gammaW hgammaW hgapW
  let L := firstExitLargePrimeCompressionOperator S X Y c
  let K := firstExitFromComplementPrimeCoverOperator S X Y c
  let J := firstExitToComplementPrimeCoverOperator S X Y c
  let CW := firstExitComplementPrimeCoverOperator S X Y c
  have hbB : primeStarBoundaryProjection S X Y c b = 0 := by
    rw [← hbU]
    exact primeStarBoundaryProjection_firstExit_eq_zero hcut hc b
  have hzInterior : primeStarInteriorProjection S X Y c z = z :=
    primeStarInteriorResolventOfGap_mem_interior
      S X Y c mu gammaI hmu hgammaI hgapI b hbB
  have hsolve : mu • z -
      primeStarInteriorPrimeCoverOperator S X Y c z = b :=
    primeStarInteriorResolventOfGap_apply_inverse
      S X Y c mu gammaI hgammaI hgapI b
  have hblocks := primeStarInteriorResolvent_blockEquations
    hS hcut hc mu z b hzInterior hbU hsolve
  have hU : mu • xU - L xU - K xW = b := hblocks.1
  have hWsolve : mu • xW - CW xW = J xU := hblocks.2
  have hW : xW = RW (J xU) := by
    calc
      xW = RW (mu • xW - CW xW) := by
        exact (firstExitComplementResolventOfGap_shift_apply
          S X Y c mu gammaW hgammaW hgapW xW).symm
      _ = RW (J xU) := by rw [hWsolve]
  have hRleft : ∀ y, RU (mu • y - L y) = y := by
    intro y
    exact firstExitLargePrimeResolventOfGap_shift_apply
      S X Y c mu gammaU hgammaU hgapU y
  exact feshbachReducedVectorIdentity L K RW J RU b xU xW
    mu mu hRleft hW hU

/-- Literal graph-level quadratic-form replacement of Lemma 8.6.  Its only
premises beyond finite graph structure are lower gaps for the three shifted
compressions, the residual small-prime norm bound, and the resulting
contraction inequality. -/
theorem primeStarInteriorResolvent_quadraticFormReplacement
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
    (hsmall : gammaU⁻¹ * (eta * gammaW⁻¹ * eta) ≤ 1 / 2)
    (b : EuclideanSpace ℝ (Vertex S X))
    (hbU : firstExitCompressionProjection S X Y c b = b) :
    let z := primeStarInteriorResolventOfGap
      S X Y c mu gammaI hgammaI hgapI b
    let RU := firstExitLargePrimeResolventOfGap
      S X Y c mu gammaU hgammaU hgapU
    |⟪b, z⟫_ℝ - ⟪b, RU b⟫_ℝ| ≤
      2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2 := by
  dsimp only
  let z := primeStarInteriorResolventOfGap
    S X Y c mu gammaI hgammaI hgapI b
  let xU := firstExitCompressionProjection S X Y c z
  let RU := firstExitLargePrimeResolventOfGap
    S X Y c mu gammaU hgammaU hgapU
  let RW := firstExitComplementResolventOfGap
    S X Y c mu gammaW hgammaW hgapW
  let K := firstExitFromComplementPrimeCoverOperator S X Y c
  let J := firstExitToComplementPrimeCoverOperator S X Y c
  let T := feshbachEffectiveInteraction K RW J mu mu
  let tau := eta * gammaW⁻¹ * eta
  let alpha := gammaU⁻¹ * tau
  have hident : xU = RU b + RU (T xU) :=
    primeStarInteriorResolvent_firstExitFeshbachIdentity
      hS hcut hc mu gammaI gammaU gammaW hmu hgammaI hgammaU hgammaW
        hgapI hgapU hgapW b hbU
  have hRU : RU.IsSymmetric :=
    firstExitLargePrimeResolventOfGap_isSymmetric
      S X Y c mu gammaU hgammaU hgapU
  have hK : ∀ x, ‖K x‖ ≤ eta * ‖x‖ := by
    intro x
    exact norm_firstExitFromComplementPrimeCoverOperator_le
      hcut eta heta hH x
  have hJ : ∀ x, ‖J x‖ ≤ eta * ‖x‖ := by
    intro x
    exact norm_firstExitToComplementPrimeCoverOperator_le
      hcut eta heta hH x
  have hRW : ∀ x, ‖RW x‖ ≤ gammaW⁻¹ * ‖x‖ := by
    intro x
    exact norm_firstExitComplementResolventOfGap_apply_le
      S X Y c mu gammaW hgammaW hgapW x
  have hRUbound : ∀ x, ‖RU x‖ ≤ gammaU⁻¹ * ‖x‖ := by
    intro x
    exact norm_firstExitLargePrimeResolventOfGap_apply_le
      S X Y c mu gammaU hgammaU hgapU x
  have hgammaWinv : 0 ≤ gammaW⁻¹ := inv_nonneg.mpr hgammaW.le
  have hgammaUinv : 0 ≤ gammaU⁻¹ := inv_nonneg.mpr hgammaU.le
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  have hT : ∀ x, ‖T x‖ ≤ tau * ‖x‖ := by
    intro x
    simpa [T, tau] using
      (norm_feshbachEffectiveInteraction_apply_le K RW J mu mu
        eta gammaW⁻¹ eta heta hgammaWinv heta hK hRW hJ x)
  have hRT : ∀ x, ‖RU (T x)‖ ≤ alpha * ‖x‖ := by
    intro x
    simpa [T, tau, alpha] using
      (norm_resolvent_feshbachEffectiveInteraction_apply_le
        RU K RW J mu mu gammaU⁻¹ eta gammaW⁻¹ eta
          hgammaUinv heta hgammaWinv heta hRUbound hK hRW hJ x)
  have hreplace := abs_quadraticForm_vectorReplacement_le
    RU T b xU tau alpha hRU hident hRT hT htau hsmall
  have hinner : ⟪b, xU⟫_ℝ = ⟪b, z⟫_ℝ := by
    have hPU : (firstExitCompressionProjection S X Y c).IsSymmetric :=
      euclideanCoordinateProjection_isSymmetric
        (firstExitCompressionSupport S X Y c)
    have h := hPU b z
    rw [hbU] at h
    exact h.symm
  simpa [hinner, tau] using hreplace

end

end PrimeStar
