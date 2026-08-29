import PrimeStar.ActualStarResolvent

/-!
# Finite localization consequences

These lemmas turn the `ℓ²` comparison with a normalized star mode into
coordinate-level hub localization.  They are purely finite-dimensional and
do not use prime-counting asymptotics.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

local instance localizationLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The inverse participation ratio of a finite real Euclidean vector. -/
def inverseParticipationRatio
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, (x i) ^ 4

/-- Coordinatewise squaring, viewed again as a Euclidean vector. -/
def coordinateSquare
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ (x i) ^ 2)

@[simp]
theorem coordinateSquare_apply
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) (i : ι) :
    coordinateSquare x i = (x i) ^ 2 :=
  rfl

/-- Coordinate absolute values are one-Lipschitz with respect to Euclidean
distance. -/
theorem abs_abs_apply_sub_abs_apply_le_norm_sub
    {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) (i : ι) :
    abs (|x i| - |y i|) ≤ ‖x - y‖ := by
  calc
    abs (|x i| - |y i|) ≤ |x i - y i| :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ = ‖(x - y) i‖ := by simp
    _ ≤ ‖x - y‖ := PiLp.norm_apply_le _ _

/-- Squared coordinate mass is two-Lipschitz on the Euclidean unit ball. -/
theorem abs_sq_apply_sub_sq_apply_le_two_mul_norm_sub
    {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) (i : ι)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |(x i) ^ 2 - (y i) ^ 2| ≤ 2 * ‖x - y‖ := by
  have hxi : |x i| ≤ 1 :=
    (PiLp.norm_apply_le x i).trans hx
  have hyi : |y i| ≤ 1 :=
    (PiLp.norm_apply_le y i).trans hy
  have hdiff : |x i - y i| ≤ ‖x - y‖ := by
    simpa using PiLp.norm_apply_le (x - y) i
  calc
    |(x i) ^ 2 - (y i) ^ 2| =
        |x i - y i| * |x i + y i| := by
          rw [sq_sub_sq, abs_mul, mul_comm]
    _ ≤ ‖x - y‖ * 2 := by
      gcongr
      calc
        |x i + y i| ≤ |x i| + |y i| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add hxi hyi
        _ = 2 := by norm_num
    _ = 2 * ‖x - y‖ := by ring

/-- Coordinatewise squaring maps the Euclidean unit ball into itself. -/
theorem norm_coordinateSquare_le_one
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι)
    (hx : ‖x‖ ≤ 1) :
    ‖coordinateSquare x‖ ≤ 1 := by
  have hsq : ‖coordinateSquare x‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, ((x i) ^ 2) ^ 2) ≤ 1
    calc
      (∑ i, ((x i) ^ 2) ^ 2) ≤ (∑ i, (x i) ^ 2) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun _i _hi ↦ sq_nonneg _)
      _ = ‖x‖ ^ 4 := by
        rw [← EuclideanSpace.real_norm_sq_eq]
        ring
      _ ≤ 1 := pow_le_one₀ (norm_nonneg x) hx
  have h0 := norm_nonneg (coordinateSquare x)
  nlinarith

/-- On the Euclidean unit ball, coordinatewise squaring is two-Lipschitz. -/
theorem norm_coordinateSquare_sub_le
    {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖coordinateSquare x - coordinateSquare y‖ ≤
      2 * ‖x - y‖ := by
  have hpoint : ∀ i : ι,
      (((x i) ^ 2 - (y i) ^ 2) ^ 2) ≤
        4 * ((x i - y i) ^ 2) := by
    intro i
    have hxi : |x i| ≤ 1 :=
      (PiLp.norm_apply_le x i).trans hx
    have hyi : |y i| ≤ 1 :=
      (PiLp.norm_apply_le y i).trans hy
    have hxb := abs_le.mp hxi
    have hyb := abs_le.mp hyi
    have hsum : (x i + y i) ^ 2 ≤ 4 := by
      nlinarith
    calc
      ((x i) ^ 2 - (y i) ^ 2) ^ 2 =
          (x i - y i) ^ 2 * (x i + y i) ^ 2 := by ring
      _ ≤ (x i - y i) ^ 2 * 4 := by
        gcongr
      _ = 4 * (x i - y i) ^ 2 := by ring
  have hsq :
      ‖coordinateSquare x - coordinateSquare y‖ ^ 2 ≤
        (2 * ‖x - y‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, (((x i) ^ 2 - (y i) ^ 2) ^ 2)) ≤ _
    calc
      (∑ i, (((x i) ^ 2 - (y i) ^ 2) ^ 2)) ≤
          ∑ i, 4 * ((x i - y i) ^ 2) :=
        Finset.sum_le_sum fun i _hi ↦ hpoint i
      _ = 4 * ‖x - y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
        simp
      _ = (2 * ‖x - y‖) ^ 2 := by ring
  have hleft := norm_nonneg (coordinateSquare x - coordinateSquare y)
  have hright : 0 ≤ 2 * ‖x - y‖ := mul_nonneg (by norm_num) (norm_nonneg _)
  nlinarith

/-- The IPR is the squared Euclidean norm of the coordinate-square vector. -/
theorem inverseParticipationRatio_eq_norm_sq_coordinateSquare
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    inverseParticipationRatio x = ‖coordinateSquare x‖ ^ 2 := by
  rw [inverseParticipationRatio, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [coordinateSquare_apply]
  ring

/-- Dimension-free IPR stability on the Euclidean unit ball. -/
theorem abs_inverseParticipationRatio_sub_le
    {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inverseParticipationRatio x - inverseParticipationRatio y| ≤
      4 * ‖x - y‖ := by
  let sx := coordinateSquare x
  let sy := coordinateSquare y
  have hsx : ‖sx‖ ≤ 1 := norm_coordinateSquare_le_one x hx
  have hsy : ‖sy‖ ≤ 1 := norm_coordinateSquare_le_one y hy
  have hdiff : ‖sx - sy‖ ≤ 2 * ‖x - y‖ :=
    norm_coordinateSquare_sub_le x y hx hy
  rw [inverseParticipationRatio_eq_norm_sq_coordinateSquare,
    inverseParticipationRatio_eq_norm_sq_coordinateSquare]
  change |‖sx‖ ^ 2 - ‖sy‖ ^ 2| ≤ _
  calc
    |‖sx‖ ^ 2 - ‖sy‖ ^ 2| =
        |‖sx‖ - ‖sy‖| * |‖sx‖ + ‖sy‖| := by
          rw [sq_sub_sq, abs_mul, mul_comm]
    _ ≤ ‖sx - sy‖ * 2 := by
      gcongr
      · exact abs_norm_sub_norm_le sx sy
      · rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        linarith
    _ ≤ (2 * ‖x - y‖) * 2 := by
      gcongr
    _ = 4 * ‖x - y‖ := by ring

/-- The Euclidean signed star vector is the corresponding literal star-data
vector. -/
theorem largePrimeEuclideanStarVector_eq_starDataVector
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) (ε : ℝ) :
    largePrimeEuclideanStarVector S X Y c ε =
      largePrimeStarDataVector S X Y c
        (√(largePrimeStarDegree S X Y c : ℝ)) (fun _ ↦ ε) :=
  rfl

/-- Exact squared norm of an unnormalized signed star vector. -/
theorem norm_sq_largePrimeEuclideanStarVector
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hε : ε ^ 2 = 1) :
    ‖largePrimeEuclideanStarVector S X Y c ε‖ ^ 2 =
      2 * largePrimeStarDegree S X Y c := by
  rw [← real_inner_self_eq_norm_sq,
    largePrimeEuclideanStarVector_eq_starDataVector,
    largePrimeStarDataVector_inner]
  have hsqrt :
      (√(largePrimeStarDegree S X Y c : ℝ)) ^ 2 =
        (largePrimeStarDegree S X Y c : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hsqrtMul :
      √(largePrimeStarDegree S X Y c : ℝ) *
          √(largePrimeStarDegree S X Y c : ℝ) =
        (largePrimeStarDegree S X Y c : ℝ) := by
    rw [← pow_two]
    exact hsqrt
  rw [hsqrtMul]
  have hsum :
      (∑ _v ∈ largePrimeLeaves S X Y c, ε * ε) =
        (largePrimeStarDegree S X Y c : ℝ) := by
    calc
      (∑ _v ∈ largePrimeLeaves S X Y c, ε * ε) =
          ∑ _v ∈ largePrimeLeaves S X Y c, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro _v _hv
            simpa [pow_two] using hε
      _ = (largePrimeStarDegree S X Y c : ℝ) := by
        simp [largePrimeStarDegree]
  rw [hsum]
  ring

/-- Every normalized nonempty signed star mode places exactly half of its
squared mass at its centre. -/
theorem sq_largePrimeNormalizedStarMode_center
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hε : ε ^ 2 = 1)
    (hd : 0 < largePrimeStarDegree S X Y c) :
    (largePrimeNormalizedStarMode S X Y c ε c) ^ 2 = 1 / 2 := by
  let u := largePrimeEuclideanStarVector S X Y c ε
  have hu0 : u ≠ 0 := by
    dsimp [u]
    rw [WithLp.toLp_eq_zero]
    exact largePrimeSignedStarVector_ne_zero hd
  have hunorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hunormsq : ‖u‖ ^ 2 =
      2 * largePrimeStarDegree S X Y c :=
    norm_sq_largePrimeEuclideanStarVector hε
  have hsqrt :
      (√(largePrimeStarDegree S X Y c : ℝ)) ^ 2 =
        (largePrimeStarDegree S X Y c : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  rw [largePrimeNormalizedStarMode, NormedSpace.normalize]
  change ((‖u‖⁻¹ • u) c) ^ 2 = 1 / 2
  have huc :
      u c = √(largePrimeStarDegree S X Y c : ℝ) := by
    simp [u, largePrimeEuclideanStarVector]
  rw [PiLp.smul_apply, smul_eq_mul, huc]
  rw [mul_pow, inv_pow, hsqrt, hunormsq]
  have hd0 : (largePrimeStarDegree S X Y c : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  field_simp [hd0]

/-- Every leaf of a normalized nonempty signed star mode has squared mass
`1 / (2d)`. -/
theorem sq_largePrimeNormalizedStarMode_leaf
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X} {ε : ℝ}
    (hε : ε ^ 2 = 1)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hv : v ∈ largePrimeLeaves S X Y c) :
    (largePrimeNormalizedStarMode S X Y c ε v) ^ 2 =
      1 / (2 * largePrimeStarDegree S X Y c) := by
  let u := largePrimeEuclideanStarVector S X Y c ε
  have hu0 : u ≠ 0 := by
    dsimp [u]
    rw [WithLp.toLp_eq_zero]
    exact largePrimeSignedStarVector_ne_zero hd
  have hunormsq : ‖u‖ ^ 2 =
      2 * largePrimeStarDegree S X Y c :=
    norm_sq_largePrimeEuclideanStarVector hε
  have huv : u v = ε := by
    simp [u, largePrimeEuclideanStarVector,
      largePrimeSignedStarVector_leaf hv]
  rw [largePrimeNormalizedStarMode, NormedSpace.normalize]
  change ((‖u‖⁻¹ • u) v) ^ 2 = _
  rw [PiLp.smul_apply, smul_eq_mul, huv, mul_pow, inv_pow, hε, hunormsq]
  have hd0 : (largePrimeStarDegree S X Y c : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  field_simp [hd0]

/-- A normalized star mode vanishes outside its closed star support. -/
theorem largePrimeNormalizedStarMode_eq_zero_of_not_mem
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X} {ε : ℝ}
    (hv : v ∉ largePrimeStarSupport S X Y c) :
    largePrimeNormalizedStarMode S X Y c ε v = 0 := by
  simp [largePrimeNormalizedStarMode, NormedSpace.normalize,
    largePrimeEuclideanStarVector,
    largePrimeSignedStarVector_eq_zero_of_not_mem hv]

/-- Exact IPR of a normalized nonempty signed star mode. -/
theorem inverseParticipationRatio_largePrimeNormalizedStarMode
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hε : ε ^ 2 = 1)
    (hd : 0 < largePrimeStarDegree S X Y c) :
    inverseParticipationRatio
        (largePrimeNormalizedStarMode S X Y c ε) =
      1 / 4 + 1 / (4 * largePrimeStarDegree S X Y c) := by
  let u := largePrimeNormalizedStarMode S X Y c ε
  have hcnot : c ∉ largePrimeLeaves S X Y c :=
    (largePrimeGraph S X Y).notMem_neighborFinset_self c
  have hsupport :
      (∑ v, (u v) ^ 4) =
        ∑ v ∈ largePrimeStarSupport S X Y c, (u v) ^ 4 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _hvUniv hvNotSupport
    have huv : u v = 0 :=
      largePrimeNormalizedStarMode_eq_zero_of_not_mem hvNotSupport
    simp [huv]
  rw [inverseParticipationRatio, hsupport, largePrimeStarSupport,
    Finset.sum_insert hcnot]
  have hcSq : (u c) ^ 2 = 1 / 2 :=
    sq_largePrimeNormalizedStarMode_center hε hd
  have hleaf :
      (∑ v ∈ largePrimeLeaves S X Y c, (u v) ^ 4) =
        (largePrimeStarDegree S X Y c : ℝ) *
          (1 / (2 * largePrimeStarDegree S X Y c : ℝ)) ^ 2 := by
    calc
      (∑ v ∈ largePrimeLeaves S X Y c, (u v) ^ 4) =
          ∑ _v ∈ largePrimeLeaves S X Y c,
            (1 / (2 * largePrimeStarDegree S X Y c : ℝ)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro v hv
              have hvSq : (u v) ^ 2 =
                  1 / (2 * largePrimeStarDegree S X Y c) :=
                sq_largePrimeNormalizedStarMode_leaf hε hd hv
              calc
                (u v) ^ 4 = ((u v) ^ 2) ^ 2 := by ring
                _ = (1 / (2 * largePrimeStarDegree S X Y c : ℝ)) ^ 2 := by
                  rw [hvSq]
      _ = (largePrimeStarDegree S X Y c : ℝ) *
          (1 / (2 * largePrimeStarDegree S X Y c : ℝ)) ^ 2 := by
            simp [largePrimeStarDegree]
  rw [hleaf]
  have hcFourth : (u c) ^ 4 = (1 / 2 : ℝ) ^ 2 := by
    calc
      (u c) ^ 4 = ((u c) ^ 2) ^ 2 := by ring
      _ = (1 / 2 : ℝ) ^ 2 := by rw [hcSq]
  rw [hcFourth]
  have hd0 : (largePrimeStarDegree S X Y c : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  field_simp [hd0]
  ring

/-- Finite hub-mass localization: any unit vector close to the positive or
negative star mode has centre mass close to one half. -/
theorem hubMass_localization_of_close_starMode
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hε : ε ^ 2 = 1)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (v : EuclideanSpace ℝ (Vertex S X)) (hv : ‖v‖ = 1) :
    |(v c) ^ 2 - 1 / 2| ≤
      2 * ‖v - largePrimeNormalizedStarMode S X Y c ε‖ := by
  rw [← sq_largePrimeNormalizedStarMode_center hε hd]
  apply abs_sq_apply_sub_sq_apply_le_two_mul_norm_sub
  · exact hv.le
  · exact (norm_largePrimeNormalizedStarMode hd).le

/-- Finite IPR localization about the exact star value. -/
theorem inverseParticipationRatio_localization_of_close_starMode
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hε : ε ^ 2 = 1)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (v : EuclideanSpace ℝ (Vertex S X)) (hv : ‖v‖ = 1) :
    |inverseParticipationRatio v -
        (1 / 4 + 1 / (4 * largePrimeStarDegree S X Y c))| ≤
      4 * ‖v - largePrimeNormalizedStarMode S X Y c ε‖ := by
  rw [← inverseParticipationRatio_largePrimeNormalizedStarMode hε hd]
  apply abs_inverseParticipationRatio_sub_le
  · exact hv.le
  · exact (norm_largePrimeNormalizedStarMode hd).le

end

end PrimeStar
