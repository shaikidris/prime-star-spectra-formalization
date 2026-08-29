import PrimeStar.StarPerturbation

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

local instance actualStarDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

def largePrimeStarDataVector
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X)
    (center : ℝ) (leaf : Vertex S X → ℝ) :
    EuclideanSpace ℝ (Vertex S X) :=
  WithLp.toLp 2 (fun v ↦
    if v = c then center
    else if v ∈ largePrimeLeaves S X Y c then leaf v else 0)

@[simp] theorem largePrimeStarDataVector_center
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (center : ℝ) (leaf : Vertex S X → ℝ) :
    largePrimeStarDataVector S X Y c center leaf c = center := by
  simp [largePrimeStarDataVector]

theorem largePrimeStarDataVector_leaf
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X}
    (center : ℝ) (leaf : Vertex S X → ℝ)
    (hv : v ∈ largePrimeLeaves S X Y c) :
    largePrimeStarDataVector S X Y c center leaf v = leaf v := by
  have hvc : v ≠ c := by
    intro hvc
    subst v
    exact (largePrimeGraph S X Y).notMem_neighborFinset_self c hv
  simp [largePrimeStarDataVector, hvc, hv]

theorem largePrimeStarDataVector_outside
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X}
    (center : ℝ) (leaf : Vertex S X → ℝ)
    (hvc : v ≠ c) (hv : v ∉ largePrimeLeaves S X Y c) :
    largePrimeStarDataVector S X Y c center leaf v = 0 := by
  simp [largePrimeStarDataVector, hvc, hv]

theorem largePrimeStarDataVector_inner
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (x x' : ℝ) (y y' : Vertex S X → ℝ) :
    ⟪largePrimeStarDataVector S X Y c x y,
      largePrimeStarDataVector S X Y c x' y'⟫_ℝ =
      x * x' + ∑ v ∈ largePrimeLeaves S X Y c, y v * y' v := by
  classical
  simp only [largePrimeStarDataVector, PiLp.inner_apply]
  change (∑ v, (if v = c then x' else
      if v ∈ largePrimeLeaves S X Y c then y' v else 0) *
    (if v = c then x else
      if v ∈ largePrimeLeaves S X Y c then y v else 0)) = _
  let f := fun v : Vertex S X ↦
    (if v = c then x' else if v ∈ largePrimeLeaves S X Y c then y' v else 0) *
      (if v = c then x else if v ∈ largePrimeLeaves S X Y c then y v else 0)
  have herase : (∑ v ∈ Finset.univ.erase c, f v) =
      ∑ v ∈ largePrimeLeaves S X Y c, y' v * y v := by
    calc
      (∑ v ∈ Finset.univ.erase c, f v) =
          ∑ v ∈ Finset.univ.erase c,
            if v ∈ largePrimeLeaves S X Y c then y' v * y v else 0 := by
              apply Finset.sum_congr rfl
              intro v hv
              have hvc : v ≠ c := by simpa using hv
              by_cases hvleaf : v ∈ largePrimeLeaves S X Y c
              · have hvadj : LargePrimeAdj S Y c v := by simpa using hvleaf
                simp [f, hvc, hvadj]
              · have hvnadj : ¬LargePrimeAdj S Y c v := by simpa using hvleaf
                simp [f, hvc, hvnadj]
      _ = ∑ v ∈ largePrimeLeaves S X Y c, y' v * y v := by
        have hfilter : (Finset.univ.erase c).filter
            (fun v ↦ v ∈ largePrimeLeaves S X Y c) =
            largePrimeLeaves S X Y c := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
          constructor
          · exact fun h ↦ h.2
          · intro hv
            refine ⟨?_, hv⟩
            intro hvc
            subst v
            exact (largePrimeGraph S X Y).notMem_neighborFinset_self c hv
        rw [Finset.sum_ite]
        rw [hfilter]
        simp
  calc
    (∑ v, (if v = c then x' else
        if v ∈ largePrimeLeaves S X Y c then y' v else 0) *
      (if v = c then x else
        if v ∈ largePrimeLeaves S X Y c then y v else 0)) =
        (∑ v ∈ Finset.univ.erase c, f v) + f c := by
          exact (Finset.sum_erase_add _ _ (Finset.mem_univ c)).symm
    _ = (∑ v ∈ largePrimeLeaves S X Y c, y' v * y v) + x' * x := by
      rw [herase]
      simp [f]
    _ = x * x' + ∑ v ∈ largePrimeLeaves S X Y c, y v * y' v := by
      rw [mul_comm x' x, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      ring

/-- Vectors carried by disjoint closed large-prime stars are orthogonal.
This is the graph-level fact that removes every cross term when the local
first-exit resolvents are assembled. -/
theorem inner_largePrimeStarDataVector_eq_zero_of_disjoint
    {S : Finset ℕ} {X Y : ℕ} {c k : Vertex S X}
    (hc kx : ℝ) (hl kl : Vertex S X → ℝ)
    (hdisj : Disjoint (largePrimeStarSupport S X Y c)
      (largePrimeStarSupport S X Y k)) :
    ⟪largePrimeStarDataVector S X Y c hc hl,
      largePrimeStarDataVector S X Y k kx kl⟫_ℝ = 0 := by
  classical
  simp only [largePrimeStarDataVector, PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro v _hv
  by_cases hvc : v ∈ largePrimeStarSupport S X Y c
  · have hvk : v ∉ largePrimeStarSupport S X Y k := by
      intro hvk
      exact (Finset.disjoint_left.mp hdisj) hvc hvk
    have hvkCenter : v ≠ k := by
      intro hvkCenter
      subst v
      exact hvk (by simp [largePrimeStarSupport])
    have hvkLeaf : v ∉ largePrimeLeaves S X Y k := by
      intro hvkLeaf
      exact hvk (by simp [largePrimeStarSupport, hvkLeaf])
    simp [hvkCenter, hvkLeaf]
  · have hvcCenter : v ≠ c := by
      intro hvcCenter
      subst v
      exact hvc (by simp [largePrimeStarSupport])
    have hvcLeaf : v ∉ largePrimeLeaves S X Y c := by
      intro hvcLeaf
      exact hvc (by simp [largePrimeStarSupport, hvcLeaf])
    simp [hvcCenter, hvcLeaf]


theorem largePrime_toEuclideanLin_starDataVector
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (x : ℝ) (y : Vertex S X → ℝ) :
    Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeStarDataVector S X Y c x y) =
      largePrimeStarDataVector S X Y c
        (∑ v ∈ largePrimeLeaves S X Y c, y v) (fun _ ↦ x) := by
  rw [largePrimeStarDataVector, largePrimeStarDataVector,
    Matrix.toLpLin_toLp 2 2]
  congr 1
  funext v
  rw [Matrix.toLin'_apply]
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  by_cases hvc : v = c
  · subst v
    change (∑ u ∈ largePrimeLeaves S X Y c,
      (if u = c then x else if u ∈ largePrimeLeaves S X Y c then y u else 0)) = _
    simp only [if_pos]
    apply Finset.sum_congr rfl
    intro u hu
    have huc : u ≠ c := by
      intro huc
      subst u
      exact (largePrimeGraph S X Y).notMem_neighborFinset_self c hu
    simp [huc, hu]
  · by_cases hvleaf : v ∈ largePrimeLeaves S X Y c
    · rw [largePrime_neighborFinset_leaf hcut hc hvleaf]
      simp [hvc, hvleaf]
    · have hvout : v ∉ largePrimeStarSupport S X Y c := by
        simp [largePrimeStarSupport, hvc, hvleaf]
      have hzero : ∀ u ∈ (largePrimeGraph S X Y).neighborFinset v,
          (if u = c then x else if u ∈ largePrimeLeaves S X Y c then y u else 0) = 0 := by
        intro u hu
        have huout : u ∉ largePrimeStarSupport S X Y c := by
          intro husupp
          have huv : LargePrimeAdj S Y v u := by simpa using hu
          exact hvout (largePrimeStarSupport_closed hcut hc husupp
            (largePrimeAdj_symm huv))
        have huc : u ≠ c := by
          intro huc
          apply huout
          simp [largePrimeStarSupport, huc]
        have huleaf : u ∉ largePrimeLeaves S X Y c := by
          intro huleaf
          apply huout
          simp [largePrimeStarSupport, huleaf]
        simp [huc, huleaf]
      rw [Finset.sum_eq_zero hzero]
      simp [hvc, hvleaf]

/-- The literal inverse of `mu - L_c` on an arbitrary vector supported by one
closed large-prime star.  The formula solves the centre equation first and
then every leaf equation. -/
def largePrimeStarResolventOfVector
    (S : Finset ℕ) (X Y : ℕ) (target : Vertex S X) (mu : ℝ)
    (b : EuclideanSpace ℝ (Vertex S X)) :
    EuclideanSpace ℝ (Vertex S X) :=
  let d : ℝ := largePrimeStarDegree S X Y target
  let zc : ℝ :=
    (mu * b target + ∑ v ∈ largePrimeLeaves S X Y target, b v) /
      (mu ^ 2 - d)
  largePrimeStarDataVector S X Y target zc (fun v ↦ (b v + zc) / mu)

/-- The arbitrary-block formula is an exact shifted inverse on the actual
large-prime graph. -/
theorem largePrimeStar_shift_resolventOfVector
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X} {mu : ℝ}
    (b : EuclideanSpace ℝ (Vertex S X))
    (hcut : X < (Y + 1) * (Y + 1)) (htarget : (target : ℕ) ≤ Y)
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hsupp : ∀ v, v ∉ largePrimeStarSupport S X Y target → b v = 0) :
    mu • largePrimeStarResolventOfVector S X Y target mu b -
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeStarResolventOfVector S X Y target mu b) = b := by
  let d : ℝ := largePrimeStarDegree S X Y target
  let B : ℝ := ∑ v ∈ largePrimeLeaves S X Y target, b v
  let zc : ℝ := (mu * b target + B) / (mu ^ 2 - d)
  rw [largePrimeStarResolventOfVector,
    largePrime_toEuclideanLin_starDataVector hcut htarget]
  change mu • largePrimeStarDataVector S X Y target zc
      (fun v ↦ (b v + zc) / mu) -
    largePrimeStarDataVector S X Y target
      (∑ v ∈ largePrimeLeaves S X Y target, (b v + zc) / mu)
      (fun _ ↦ zc) = b
  ext v
  by_cases hvt : v = target
  · subst v
    simp only [PiLp.smul_apply, PiLp.sub_apply,
      largePrimeStarDataVector_center]
    have hsum :
        (∑ w ∈ largePrimeLeaves S X Y target, (b w + zc) / mu) =
          (B + d * zc) / mu := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp [B, d, largePrimeStarDegree]
    rw [hsum]
    dsimp [zc]
    have hden0 : mu ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
    field_simp [hmu, hden0]
    ring
  · by_cases hvleaf : v ∈ largePrimeLeaves S X Y target
    · simp only [PiLp.smul_apply, PiLp.sub_apply]
      rw [largePrimeStarDataVector_leaf _ _ hvleaf,
        largePrimeStarDataVector_leaf _ _ hvleaf]
      change mu * ((b v + zc) / mu) - zc = b v
      field_simp [hmu]
      ring
    · have hvout : v ∉ largePrimeStarSupport S X Y target := by
        simp [largePrimeStarSupport, hvt, hvleaf]
      simp only [PiLp.smul_apply, PiLp.sub_apply]
      rw [largePrimeStarDataVector_outside _ _ hvt hvleaf,
        largePrimeStarDataVector_outside _ _ hvt hvleaf, hsupp v hvout]
      simp
/-- The literal first-exit vector occupying a full target star. -/
def actualUpStarFirstExit
    (S : Finset ℕ) (X Y : ℕ) (target : Vertex S X) (mu c0 : ℝ) :
    EuclideanSpace ℝ (Vertex S X) :=
  largePrimeStarDataVector S X Y target c0 (fun _ ↦ c0 / mu)

/-- The literal inverse image of a full up-star first-exit vector. -/
def actualUpStarResolvent
    (S : Finset ℕ) (X Y : ℕ) (target : Vertex S X) (mu c0 : ℝ) :
    EuclideanSpace ℝ (Vertex S X) :=
  let d : ℝ := largePrimeStarDegree S X Y target
  largePrimeStarDataVector S X Y target
    (c0 * (mu ^ 2 + d) / (mu * (mu ^ 2 - d)))
    (fun _ ↦ 2 * c0 / (mu ^ 2 - d))

theorem actualUpStar_shift_resolvent
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X} {mu c0 : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (htarget : (target : ℕ) ≤ Y)
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ)) :
    mu • actualUpStarResolvent S X Y target mu c0 -
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (actualUpStarResolvent S X Y target mu c0) =
      actualUpStarFirstExit S X Y target mu c0 := by
  let d : ℝ := largePrimeStarDegree S X Y target
  rw [actualUpStarResolvent, actualUpStarFirstExit,
    largePrime_toEuclideanLin_starDataVector hcut htarget]
  ext v
  by_cases hvt : v = target
  · subst v
    simp only [PiLp.smul_apply, PiLp.sub_apply, largePrimeStarDataVector_center]
    have hsum :
        (∑ w ∈ largePrimeLeaves S X Y target, 2 * c0 / (mu ^ 2 - d)) =
          d * (2 * c0 / (mu ^ 2 - d)) := by
      simp [d, largePrimeStarDegree]
    rw [hsum]
    change mu * (c0 * (mu ^ 2 + d) / (mu * (mu ^ 2 - d))) -
      d * (2 * c0 / (mu ^ 2 - d)) = c0
    have hden0 : mu ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
    field_simp [hmu, hden0]
    ring
  · by_cases hvleaf : v ∈ largePrimeLeaves S X Y target
    · simp only [PiLp.smul_apply, PiLp.sub_apply]
      rw [largePrimeStarDataVector_leaf _ _ hvleaf,
        largePrimeStarDataVector_leaf _ _ hvleaf,
        largePrimeStarDataVector_leaf _ _ hvleaf]
      change mu * (2 * c0 / (mu ^ 2 - d)) -
        c0 * (mu ^ 2 + d) / (mu * (mu ^ 2 - d)) = c0 / mu
      have hden0 : mu ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
      field_simp [hmu, hden0]
      ring
    · simp only [PiLp.smul_apply, PiLp.sub_apply]
      rw [largePrimeStarDataVector_outside _ _ hvt hvleaf,
        largePrimeStarDataVector_outside _ _ hvt hvleaf,
        largePrimeStarDataVector_outside _ _ hvt hvleaf]
      simp

theorem actualUpStar_quadraticForm
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X} {mu c0 : ℝ}
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    2 * mu * ⟪actualUpStarFirstExit S X Y target mu c0,
      actualUpStarResolvent S X Y target mu c0⟫_ℝ =
      (mu ^ 2 + 3 * (largePrimeStarDegree S X Y target : ℝ)) /
        (mu ^ 2 - (largePrimeStarDegree S X Y target : ℝ)) := by
  let d : ℝ := largePrimeStarDegree S X Y target
  rw [actualUpStarFirstExit, actualUpStarResolvent,
    largePrimeStarDataVector_inner]
  have hsum :
      (∑ _v ∈ largePrimeLeaves S X Y target,
        c0 / mu * (2 * c0 / (mu ^ 2 - d))) =
        d * (c0 / mu * (2 * c0 / (mu ^ 2 - d))) := by
    simp [d, largePrimeStarDegree]
  rw [hsum]
  change 2 * mu *
    (c0 * (c0 * (mu ^ 2 + d) / (mu * (mu ^ 2 - d))) +
      d * (c0 / mu * (2 * c0 / (mu ^ 2 - d)))) =
    (mu ^ 2 + 3 * d) / (mu ^ 2 - d)
  have hden0 : mu ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
  have hc02 : 2 * c0 ^ 2 = 1 := by linarith
  field_simp [hmu, hden0]
  rw [hc02]
  ring

/-- A down-star first-exit vector: only the selected leaf subset is occupied. -/
def actualDownStarFirstExit
    (S : Finset ℕ) (X Y : ℕ) (target : Vertex S X)
    (P : Finset (Vertex S X)) (mu c0 : ℝ) :
    EuclideanSpace ℝ (Vertex S X) :=
  largePrimeStarDataVector S X Y target c0
    (fun v ↦ if v ∈ P then c0 / mu else 0)

/-- The literal inverse image of a partial-leaf down-star first-exit vector. -/
def actualDownStarResolvent
    (S : Finset ℕ) (X Y : ℕ) (target : Vertex S X)
    (P : Finset (Vertex S X)) (mu c0 : ℝ) :
    EuclideanSpace ℝ (Vertex S X) :=
  let d : ℝ := largePrimeStarDegree S X Y target
  largePrimeStarDataVector S X Y target
    (2 * mu * c0 / (mu ^ 2 - d))
    (fun v ↦ 2 * c0 / (mu ^ 2 - d) +
      if v ∈ P then c0 / mu ^ 2 else 0)

theorem actualDownStar_shift_resolvent
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X}
    {P : Finset (Vertex S X)} {mu c0 : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (htarget : (target : ℕ) ≤ Y)
    (hP : P ⊆ largePrimeLeaves S X Y target)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ)) :
    mu • actualDownStarResolvent S X Y target P mu c0 -
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (actualDownStarResolvent S X Y target P mu c0) =
      actualDownStarFirstExit S X Y target P mu c0 := by
  let d : ℝ := largePrimeStarDegree S X Y target
  rw [actualDownStarResolvent, actualDownStarFirstExit,
    largePrime_toEuclideanLin_starDataVector hcut htarget]
  ext v
  by_cases hvt : v = target
  · subst v
    simp only [PiLp.smul_apply, PiLp.sub_apply, largePrimeStarDataVector_center]
    have hsumBase :
        (∑ w ∈ largePrimeLeaves S X Y target,
          (2 * c0 / (mu ^ 2 - d) + if w ∈ P then c0 / mu ^ 2 else 0)) =
        d * (2 * c0 / (mu ^ 2 - d)) + P.card * (c0 / mu ^ 2) := by
      rw [Finset.sum_add_distrib]
      have hPfilter : (largePrimeLeaves S X Y target).filter (fun w ↦ w ∈ P) = P := by
        ext w
        simp only [Finset.mem_filter]
        constructor
        · exact fun h ↦ h.2
        · intro hw
          exact ⟨hP hw, hw⟩
      rw [Finset.sum_ite, hPfilter]
      simp [d, largePrimeStarDegree]
    rw [hsumBase]
    rw [hcard]
    change mu * (2 * mu * c0 / (mu ^ 2 - d)) -
      (d * (2 * c0 / (mu ^ 2 - d)) + mu ^ 2 * (c0 / mu ^ 2)) = c0
    have hden0 : mu ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
    field_simp [hmu, hden0]
    ring
  · by_cases hvleaf : v ∈ largePrimeLeaves S X Y target
    · simp only [PiLp.smul_apply, PiLp.sub_apply]
      rw [largePrimeStarDataVector_leaf _ _ hvleaf,
        largePrimeStarDataVector_leaf _ _ hvleaf,
        largePrimeStarDataVector_leaf _ _ hvleaf]
      by_cases hvP : v ∈ P
      · simp only [if_pos hvP]
        change mu * (2 * c0 / (mu ^ 2 - d) + c0 / mu ^ 2) -
          2 * mu * c0 / (mu ^ 2 - d) = c0 / mu
        have hden0 : mu ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
        field_simp [hmu, hden0]
        ring
      · simp only [if_neg hvP]
        change mu * (2 * c0 / (mu ^ 2 - d) + 0) -
          2 * mu * c0 / (mu ^ 2 - d) = 0
        have hden0 : mu ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
        field_simp [hmu, hden0]
        ring
    · simp only [PiLp.smul_apply, PiLp.sub_apply]
      rw [largePrimeStarDataVector_outside _ _ hvt hvleaf,
        largePrimeStarDataVector_outside _ _ hvt hvleaf,
        largePrimeStarDataVector_outside _ _ hvt hvleaf]
      simp

theorem actualDownStar_quadraticForm
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X}
    {P : Finset (Vertex S X)} {mu c0 : ℝ}
    (hP : P ⊆ largePrimeLeaves S X Y target)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    2 * mu * ⟪actualDownStarFirstExit S X Y target P mu c0,
      actualDownStarResolvent S X Y target P mu c0⟫_ℝ =
      (5 * mu ^ 2 - (largePrimeStarDegree S X Y target : ℝ)) /
        (mu ^ 2 - (largePrimeStarDegree S X Y target : ℝ)) := by
  let d : ℝ := largePrimeStarDegree S X Y target
  rw [actualDownStarFirstExit, actualDownStarResolvent,
    largePrimeStarDataVector_inner]
  have hsum :
      (∑ v ∈ largePrimeLeaves S X Y target,
        (if v ∈ P then c0 / mu else 0) *
          (2 * c0 / (mu ^ 2 - d) + if v ∈ P then c0 / mu ^ 2 else 0)) =
        P.card * ((c0 / mu) *
          (2 * c0 / (mu ^ 2 - d) + c0 / mu ^ 2)) := by
    have hPfilter : (largePrimeLeaves S X Y target).filter (fun v ↦ v ∈ P) = P := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · exact fun h ↦ h.2
      · intro hv
        exact ⟨hP hv, hv⟩
    calc
      _ = ∑ v ∈ largePrimeLeaves S X Y target,
          if v ∈ P then (c0 / mu) *
            (2 * c0 / (mu ^ 2 - d) + c0 / mu ^ 2) else 0 := by
              apply Finset.sum_congr rfl
              intro v _
              by_cases hv : v ∈ P <;> simp [hv]
      _ = _ := by
        rw [Finset.sum_ite, hPfilter]
        simp
  rw [hsum, hcard]
  change 2 * mu *
    (c0 * (2 * mu * c0 / (mu ^ 2 - d)) +
      mu ^ 2 * (c0 / mu *
        (2 * c0 / (mu ^ 2 - d) + c0 / mu ^ 2))) =
    (5 * mu ^ 2 - d) / (mu ^ 2 - d)
  have hden0 : mu ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
  have hc02 : 2 * c0 ^ 2 = 1 := by linarith
  field_simp [hmu, hden0]
  rw [hc02]
  ring

/-- Ratio form of the actual up-star identity, matching Lemma 8.2. -/
theorem actualUpStar_quadraticForm_ratio
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X} {mu c0 : ℝ}
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    2 * mu * ⟪actualUpStarFirstExit S X Y target mu c0,
      actualUpStarResolvent S X Y target mu c0⟫_ℝ =
      (1 + 3 * ((largePrimeStarDegree S X Y target : ℝ) / mu ^ 2)) /
        (1 - (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) := by
  rw [actualUpStar_quadraticForm hmu hden hc0]
  have hmu2 : mu ^ 2 ≠ 0 := pow_ne_zero 2 hmu
  field_simp [hmu2, sub_ne_zero.mpr hden]

/-- Ratio form of the actual partial-leaf down-star identity, matching
Lemma 8.2 without introducing an abstract kernel coordinate. -/
theorem actualDownStar_quadraticForm_ratio
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X}
    {P : Finset (Vertex S X)} {mu c0 : ℝ}
    (hP : P ⊆ largePrimeLeaves S X Y target)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠ (largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    2 * mu * ⟪actualDownStarFirstExit S X Y target P mu c0,
      actualDownStarResolvent S X Y target P mu c0⟫_ℝ =
      (5 - (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) /
        (1 - (largePrimeStarDegree S X Y target : ℝ) / mu ^ 2) := by
  rw [actualDownStar_quadraticForm hP hcard hmu hden hc0]
  have hmu2 : mu ^ 2 ≠ 0 := pow_ne_zero 2 hmu
  field_simp [hmu2, sub_ne_zero.mpr hden]

/-- Cross terms between an up first-exit block and an up resolvent block on a
disjoint star vanish exactly. -/
theorem inner_actualUpFirstExit_actualUpResolvent_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c k : Vertex S X} {mu c0 : ℝ}
    (hdisj : Disjoint (largePrimeStarSupport S X Y c)
      (largePrimeStarSupport S X Y k)) :
    ⟪actualUpStarFirstExit S X Y c mu c0,
      actualUpStarResolvent S X Y k mu c0⟫_ℝ = 0 := by
  simpa [actualUpStarFirstExit, actualUpStarResolvent] using
    (inner_largePrimeStarDataVector_eq_zero_of_disjoint
      (S := S) (X := X) (Y := Y) (c := c) (k := k)
      c0
      (c0 * (mu ^ 2 + (largePrimeStarDegree S X Y k : ℝ)) /
        (mu * (mu ^ 2 - (largePrimeStarDegree S X Y k : ℝ))))
      (fun _ ↦ c0 / mu)
      (fun _ ↦ 2 * c0 /
        (mu ^ 2 - (largePrimeStarDegree S X Y k : ℝ))) hdisj)

/-- Cross terms between an up first-exit block and a down resolvent block on
a disjoint star vanish exactly. -/
theorem inner_actualUpFirstExit_actualDownResolvent_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c k : Vertex S X}
    {P : Finset (Vertex S X)} {mu c0 : ℝ}
    (hdisj : Disjoint (largePrimeStarSupport S X Y c)
      (largePrimeStarSupport S X Y k)) :
    ⟪actualUpStarFirstExit S X Y c mu c0,
      actualDownStarResolvent S X Y k P mu c0⟫_ℝ = 0 := by
  simpa [actualUpStarFirstExit, actualDownStarResolvent] using
    (inner_largePrimeStarDataVector_eq_zero_of_disjoint
      (S := S) (X := X) (Y := Y) (c := c) (k := k)
      c0 (2 * mu * c0 /
        (mu ^ 2 - (largePrimeStarDegree S X Y k : ℝ)))
      (fun _ ↦ c0 / mu)
      (fun v ↦ 2 * c0 /
        (mu ^ 2 - (largePrimeStarDegree S X Y k : ℝ)) +
          if v ∈ P then c0 / mu ^ 2 else 0) hdisj)

/-- Cross terms between a down first-exit block and an up resolvent block on
a disjoint star vanish exactly. -/
theorem inner_actualDownFirstExit_actualUpResolvent_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c k : Vertex S X}
    {P : Finset (Vertex S X)} {mu c0 : ℝ}
    (hdisj : Disjoint (largePrimeStarSupport S X Y c)
      (largePrimeStarSupport S X Y k)) :
    ⟪actualDownStarFirstExit S X Y c P mu c0,
      actualUpStarResolvent S X Y k mu c0⟫_ℝ = 0 := by
  simpa [actualDownStarFirstExit, actualUpStarResolvent] using
    (inner_largePrimeStarDataVector_eq_zero_of_disjoint
      (S := S) (X := X) (Y := Y) (c := c) (k := k)
      c0
      (c0 * (mu ^ 2 + (largePrimeStarDegree S X Y k : ℝ)) /
        (mu * (mu ^ 2 - (largePrimeStarDegree S X Y k : ℝ))))
      (fun v ↦ if v ∈ P then c0 / mu else 0)
      (fun _ ↦ 2 * c0 /
        (mu ^ 2 - (largePrimeStarDegree S X Y k : ℝ))) hdisj)

/-- Cross terms between down first-exit and down resolvent blocks on disjoint
stars vanish exactly. -/
theorem inner_actualDownFirstExit_actualDownResolvent_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c k : Vertex S X}
    {P Q : Finset (Vertex S X)} {mu c0 : ℝ}
    (hdisj : Disjoint (largePrimeStarSupport S X Y c)
      (largePrimeStarSupport S X Y k)) :
    ⟪actualDownStarFirstExit S X Y c P mu c0,
      actualDownStarResolvent S X Y k Q mu c0⟫_ℝ = 0 := by
  simpa [actualDownStarFirstExit, actualDownStarResolvent] using
    (inner_largePrimeStarDataVector_eq_zero_of_disjoint
      (S := S) (X := X) (Y := Y) (c := c) (k := k)
      c0 (2 * mu * c0 /
        (mu ^ 2 - (largePrimeStarDegree S X Y k : ℝ)))
      (fun v ↦ if v ∈ P then c0 / mu else 0)
      (fun v ↦ 2 * c0 /
        (mu ^ 2 - (largePrimeStarDegree S X Y k : ℝ)) +
          if v ∈ Q then c0 / mu ^ 2 else 0) hdisj)

end

end PrimeStar
