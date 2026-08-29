import PrimeStar.FirstExitSupport

/-!
# Full first-exit compression under prime deletion

The basic graph API permits an arbitrary finite deletion set. The manuscript
assumes every deleted label is prime. Under that hypothesis, multiplying by
an allowed prime and passing to an allowed divisor preserve the vertex set.
These constructors close the isolated-centre cases in the first-exit
compression.
-/

namespace PrimeStar

noncomputable section

local instance firstExitCompressionLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance firstExitCompressionPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

local instance firstExitCompressionSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Multiplication by an allowed prime stays in the vertex set whenever the
product stays below the finite cutoff. -/
def vertexMulAllowedPrimeOfBound
    {S : Finset ℕ} {X : ℕ}
    (hS : ∀ s ∈ S, s.Prime)
    (c : Vertex S X) (q : ℕ)
    (hq : q.Prime) (hqS : q ∉ S)
    (hcqX : (c : ℕ) * q ≤ X) : Vertex S X := by
  refine ⟨⟨(c : ℕ) * q, Nat.lt_succ_iff.mpr hcqX⟩,
    Nat.mul_pos (Vertex.coe_pos c) hq.pos, ?_⟩
  intro s hs
  have hsPrime := hS s hs
  apply hsPrime.not_dvd_mul (Vertex.not_dvd_of_mem c hs)
  intro hsq
  have hsqEq : s = q :=
    (Nat.prime_dvd_prime_iff_eq hsPrime hq).mp hsq
  exact hqS (by simpa [hsqEq] using hs)

@[simp]
theorem vertexMulAllowedPrimeOfBound_coe
    {S : Finset ℕ} {X : ℕ}
    (hS : ∀ s ∈ S, s.Prime)
    (c : Vertex S X) (q : ℕ)
    (hq : q.Prime) (hqS : q ∉ S)
    (hcqX : (c : ℕ) * q ≤ X) :
    (vertexMulAllowedPrimeOfBound hS c q hq hqS hcqX : ℕ) =
      (c : ℕ) * q :=
  rfl

/-- A positive divisor of an allowed vertex is again an allowed vertex. -/
def vertexDivisorOfDvd
    {S : Finset ℕ} {X m : ℕ}
    (c : Vertex S X) (hmPos : 0 < m) (hmDvd : m ∣ (c : ℕ)) :
    Vertex S X := by
  have hmLe : m ≤ X :=
    (Nat.le_of_dvd (Vertex.coe_pos c) hmDvd).trans (Vertex.coe_le c)
  refine ⟨⟨m, Nat.lt_succ_iff.mpr hmLe⟩, hmPos, ?_⟩
  intro s hs hsm
  exact Vertex.not_dvd_of_mem c hs (dvd_trans hsm hmDvd)

@[simp]
theorem vertexDivisorOfDvd_coe
    {S : Finset ℕ} {X m : ℕ}
    (c : Vertex S X) (hmPos : 0 < m) (hmDvd : m ∣ (c : ℕ)) :
    (vertexDivisorOfDvd c hmPos hmDvd : ℕ) = m :=
  rfl

/-- A residual neighbour of a large-prime leaf is never isolated in the
large-prime graph. -/
theorem not_isolated_of_smallPrimeAdj_largePrimeLeaf
    {S : Finset ℕ} {X Y : ℕ} {c leaf v : Vertex S X}
    (hS : ∀ s ∈ S, s.Prime)
    (hc : (c : ℕ) ≤ Y)
    (hleaf : leaf ∈ largePrimeLeaves S X Y c)
    (hlv : (smallPrimeGraph S X Y).Adj leaf v) :
    ¬(largePrimeGraph S X Y).IsIsolated v := by
  obtain ⟨p, hp, hpS, hYp, hcp⟩ :=
    (mem_largePrimeLeaves_iff_child hc).mp hleaf
  obtain ⟨q, hq, hqS, hqY, hEdge⟩ :=
    smallPrimeGraph_adj_iff_smallPrimeAdj.mp hlv
  intro hvIso
  rcases hEdge with hleafq | hvq
  · have hcqX : (c : ℕ) * q ≤ X := by
      have hle : (c : ℕ) * q ≤ ((c : ℕ) * q) * p :=
        Nat.le_mul_of_pos_right _ hp.pos
      apply hle.trans
      calc
        ((c : ℕ) * q) * p = ((c : ℕ) * p) * q := by ac_rfl
        _ = (leaf : ℕ) * q := by rw [hcp]
        _ = (v : ℕ) := hleafq
        _ ≤ X := Vertex.coe_le v
    let k : Vertex S X :=
      vertexMulAllowedPrimeOfBound hS c q hq hqS hcqX
    have hkv : IsLargePrimeChild S Y k v := by
      refine ⟨p, hp, hpS, hYp, ?_⟩
      change ((c : ℕ) * q) * p = (v : ℕ)
      calc
        ((c : ℕ) * q) * p = ((c : ℕ) * p) * q := by ac_rfl
        _ = (leaf : ℕ) * q := by rw [hcp]
        _ = (v : ℕ) := hleafq
    exact hvIso k (largePrimeAdj_symm (isLargePrimeChild_largePrimeAdj hkv))
  · have hqDvdCP : q ∣ (c : ℕ) * p := by
      refine ⟨(v : ℕ), ?_⟩
      calc
        (c : ℕ) * p = (leaf : ℕ) := hcp
        _ = (v : ℕ) * q := hvq.symm
        _ = q * (v : ℕ) := Nat.mul_comm _ _
    have hqDvdC : q ∣ (c : ℕ) := by
      rcases hq.dvd_mul.mp hqDvdCP with hqc | hqp
      · exact hqc
      · have hqpEq : q = p :=
          (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
        exact False.elim ((not_lt_of_ge hqY) (hqpEq ▸ hYp))
    obtain ⟨m, hcm⟩ := hqDvdC
    have hmPos : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      have hc0 : (c : ℕ) = 0 := by simpa [hm0] using hcm
      exact (Vertex.coe_pos c).ne' hc0
    have hmDvdC : m ∣ (c : ℕ) := by
      refine ⟨q, ?_⟩
      simpa [Nat.mul_comm] using hcm
    let k : Vertex S X := vertexDivisorOfDvd c hmPos hmDvdC
    have hmpv : m * p = (v : ℕ) := by
      apply Nat.eq_of_mul_eq_mul_left hq.pos
      calc
        q * (m * p) = (q * m) * p := by ac_rfl
        _ = (c : ℕ) * p := by rw [hcm]
        _ = (leaf : ℕ) := hcp
        _ = (v : ℕ) * q := hvq.symm
        _ = q * (v : ℕ) := Nat.mul_comm _ _
    have hkv : IsLargePrimeChild S Y k v := by
      refine ⟨p, hp, hpS, hYp, ?_⟩
      exact hmpv
    exact hvIso k (largePrimeAdj_symm (isLargePrimeChild_largePrimeAdj hkv))

/-- Every isolated first exit is itself an arithmetic up- or down-centre. -/
theorem mem_firstExitIsolatedVertices_arithmetic
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X}
    (hS : ∀ s ∈ S, s.Prime)
    (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ firstExitIsolatedVertices S X Y c) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ≤ Y ∧
      ((c : ℕ) * q = (v : ℕ) ∨ (v : ℕ) * q = (c : ℕ)) := by
  obtain ⟨hvExit, hvIso⟩ := mem_firstExitIsolatedVertices.mp hv
  obtain ⟨w, hw, hwv⟩ := mem_smallPrimeFirstExitSupport.mp hvExit
  obtain ⟨q, hq, hqS, hqY, hEdge⟩ :=
    smallPrimeGraph_adj_iff_smallPrimeAdj.mp hwv
  rw [mem_largePrimeStarSupport] at hw
  rcases hw with hwc | hcw
  · exact ⟨q, hq, hqS, hqY, by simpa [hwc] using hEdge⟩
  · have hwLeaf : w ∈ largePrimeLeaves S X Y c :=
      mem_largePrimeLeaves.mpr hcw
    exact False.elim
      (not_isolated_of_smallPrimeAdj_largePrimeLeaf hS hc hwLeaf hwv hvIso)

/-- No residual edge joins the selected non-isolated star union to an isolated
first-exit centre. -/
theorem not_smallPrimeAdj_firstExitStarUnion_isolated
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hS : ∀ s ∈ S, s.Prime)
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hv : v ∈
      largePrimeStarUnionSupport S X Y (firstExitLowerCenters S X Y c))
    (hw : w ∈ firstExitIsolatedVertices S X Y c) :
    ¬(smallPrimeGraph S X Y).Adj v w := by
  intro hvw
  obtain ⟨k, hkC, hvk⟩ := mem_largePrimeStarUnionSupport.mp hv
  have hkY := (mem_firstExitLowerCenters.mp hkC).1
  rw [mem_largePrimeStarSupport] at hvk
  rcases hvk with hvk0 | hkv
  · obtain ⟨q, hq, _hqS, _hqY, hkArithmetic⟩ :=
      mem_firstExitLowerCenters_arithmetic hcut hc hkC
    obtain ⟨r, hr, _hrS, _hrY, hwArithmetic⟩ :=
      mem_firstExitIsolatedVertices_arithmetic hS hc hw
    obtain ⟨ell, hell, _hellS, _hellY, hEdge⟩ :=
      smallPrimeGraph_adj_iff_smallPrimeAdj.mp hvw
    exact no_prime_step_between_primeStepNeighbors
      (Vertex.coe_pos c) (Vertex.coe_pos k) (Vertex.coe_pos w)
      hq hr hell hkArithmetic hwArithmetic (by simpa [hvk0] using hEdge)
  · have hvLeaf : v ∈ largePrimeLeaves S X Y k :=
      mem_largePrimeLeaves.mpr hkv
    exact not_isolated_of_smallPrimeAdj_largePrimeLeaf hS hkY hvLeaf hvw
      (mem_firstExitIsolatedVertices.mp hw).2

/-- Under the manuscript's prime-deletion hypothesis, the whole first-exit
compression contains no internal residual edge. -/
theorem not_smallPrimeAdj_on_firstExitCompressionSupport
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hS : ∀ s ∈ S, s.Prime)
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ firstExitCompressionSupport S X Y c)
    (hw : w ∈ firstExitCompressionSupport S X Y c) :
    ¬(smallPrimeGraph S X Y).Adj v w := by
  rcases Finset.mem_union.mp hv with hvStar | hvIso <;>
    rcases Finset.mem_union.mp hw with hwStar | hwIso
  · exact not_smallPrimeAdj_on_firstExitLargePrimeStarUnion hcut hc hvStar hwStar
  · exact not_smallPrimeAdj_firstExitStarUnion_isolated
      hS hcut hc hvStar hwIso
  · intro hvw
    exact not_smallPrimeAdj_firstExitStarUnion_isolated
      hS hcut hc hwStar hvIso
      ((smallPrimeGraph S X Y).adj_comm w v |>.mpr hvw)
  · intro hvw
    obtain ⟨q, hq, _hqS, _hqY, hvArithmetic⟩ :=
      mem_firstExitIsolatedVertices_arithmetic hS hc hvIso
    obtain ⟨r, hr, _hrS, _hrY, hwArithmetic⟩ :=
      mem_firstExitIsolatedVertices_arithmetic hS hc hwIso
    obtain ⟨ell, hell, _hellS, _hellY, hEdge⟩ :=
      smallPrimeGraph_adj_iff_smallPrimeAdj.mp hvw
    exact no_prime_step_between_primeStepNeighbors
      (Vertex.coe_pos c) (Vertex.coe_pos v) (Vertex.coe_pos w)
      hq hr hell hvArithmetic hwArithmetic hEdge

/-- On the first-exit compression, the full adjacency matrix is exactly the
large-prime adjacency matrix. -/
theorem primeCover_adjMatrix_eq_largePrime_on_firstExitCompressionSupport
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hS : ∀ s ∈ S, s.Prime)
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ firstExitCompressionSupport S X Y c)
    (hw : w ∈ firstExitCompressionSupport S X Y c) :
    (primeCoverGraph S X).adjMatrix ℝ v w =
      (largePrimeGraph S X Y).adjMatrix ℝ v w := by
  have hsmall :=
    not_smallPrimeAdj_on_firstExitCompressionSupport hS hcut hc hv hw
  have hiff :
      (primeCoverGraph S X).Adj v w ↔
        (largePrimeGraph S X Y).Adj v w := by
    constructor
    · intro hp
      by_contra hl
      exact hsmall (smallPrimeGraph_adj.mpr ⟨hp, hl⟩)
    · intro hl
      exact largePrimeGraph_le_primeCoverGraph S X Y hl
  by_cases hp : (primeCoverGraph S X).Adj v w
  · have hl := hiff.mp hp
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply,
      if_pos hp, if_pos hl]
  · have hl : ¬(largePrimeGraph S X Y).Adj v w := by
      intro hl
      exact hp (hiff.mpr hl)
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply,
      if_neg hp, if_neg hl]

/-- Every matrix block whose row and column indices lie in the first-exit
compression is exactly the corresponding large-prime block.  Quantifying over
arbitrary reindexing maps makes the statement usable both for subtype
compressions and for later ordered block decompositions. -/
theorem primeCover_submatrix_eq_largePrime_on_firstExitCompressionSupport
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    {ι κ : Type*} (r : ι → Vertex S X) (s : κ → Vertex S X)
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hr : ∀ i, r i ∈ firstExitCompressionSupport S X Y c)
    (hs : ∀ j, s j ∈ firstExitCompressionSupport S X Y c) :
    ((primeCoverGraph S X).adjMatrix ℝ).submatrix r s =
      ((largePrimeGraph S X Y).adjMatrix ℝ).submatrix r s := by
  ext i j
  exact primeCover_adjMatrix_eq_largePrime_on_firstExitCompressionSupport
    hS hcut hc (hr i) (hs j)

/-- Every full-graph edge leaving the first-exit compression is a residual
small-prime edge. -/
theorem smallPrimeAdj_of_primeCoverAdj_leaving_firstExitCompressionSupport
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hv : v ∈ firstExitCompressionSupport S X Y c)
    (hw : w ∉ firstExitCompressionSupport S X Y c)
    (hvw : (primeCoverGraph S X).Adj v w) :
    (smallPrimeGraph S X Y).Adj v w := by
  rw [smallPrimeGraph_adj]
  exact ⟨hvw,
    not_largePrimeAdj_of_mem_firstExitCompressionSupport_of_not_mem hcut hv hw⟩

/-- Across the boundary of the first-exit compression, the full adjacency
block is exactly the residual small-prime block. -/
theorem primeCover_boundarySubmatrix_eq_smallPrime
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    {ι κ : Type*} (r : ι → Vertex S X) (s : κ → Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1))
    (hr : ∀ i, r i ∈ firstExitCompressionSupport S X Y c)
    (hs : ∀ j, s j ∉ firstExitCompressionSupport S X Y c) :
    ((primeCoverGraph S X).adjMatrix ℝ).submatrix r s =
      ((smallPrimeGraph S X Y).adjMatrix ℝ).submatrix r s := by
  ext i j
  have hlarge :
      ¬(largePrimeGraph S X Y).Adj (r i) (s j) :=
    not_largePrimeAdj_of_mem_firstExitCompressionSupport_of_not_mem
      hcut (hr i) (hs j)
  have hsplit := congrFun
    (congrFun (primeCover_adjMatrix_eq_large_add_small S X Y) (r i)) (s j)
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
  calc
    (primeCoverGraph S X).adjMatrix ℝ (r i) (s j) =
        (largePrimeGraph S X Y).adjMatrix ℝ (r i) (s j) +
          (smallPrimeGraph S X Y).adjMatrix ℝ (r i) (s j) := hsplit
    _ = (smallPrimeGraph S X Y).adjMatrix ℝ (r i) (s j) := by
      rw [SimpleGraph.adjMatrix_apply, if_neg hlarge, zero_add]

end

end PrimeStar
