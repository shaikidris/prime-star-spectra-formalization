import PrimeStar.FirstExit

/-!
# Exact support of the first-exit vector

This file packages the graph-theoretic support statement behind Proposition
8.1. The first-exit support is the union of residual neighbours of the closed
large-prime star. It is disjoint from the original star, every point has the
arithmetic form classified in `FirstExit`, and the residual adjacency applied
to the signed star vector vanishes outside it.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

/-- Local decidability for first-exit support calculations. -/
local instance firstExitSupportDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Local decidability for the large-prime graph used in compression filters. -/
local instance firstExitSupportLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Local decidability for the large-prime isolated-vertex predicate. -/
local instance firstExitSupportDecidableIsolated
    (S : Finset ℕ) (X Y : ℕ) :
    DecidablePred fun v : Vertex S X =>
      (largePrimeGraph S X Y).IsIsolated v :=
  Classical.decPred _

/-- The union of all residual neighbours of one closed large-prime star. -/
def smallPrimeFirstExitSupport
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) : Finset (Vertex S X) :=
  (largePrimeStarSupport S X Y c).biUnion
    (fun w => (smallPrimeGraph S X Y).neighborFinset w)

@[simp]
theorem mem_smallPrimeFirstExitSupport
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X} :
    v ∈ smallPrimeFirstExitSupport S X Y c ↔
      ∃ w ∈ largePrimeStarSupport S X Y c,
        (smallPrimeGraph S X Y).Adj w v := by
  simp [smallPrimeFirstExitSupport]

/-- Membership in the first-exit support is exhausted by the centre/leaf
arithmetic forms of Proposition 8.1. -/
theorem smallPrimeFirstExitSupport_arithmeticForms
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X}
    (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ smallPrimeFirstExitSupport S X Y c) :
    ∃ w ∈ largePrimeStarSupport S X Y c, ∃ q : ℕ,
      q.Prime ∧ q ∉ S ∧ q ≤ Y ∧
        ((w = c ∧ ((v : ℕ) * q = (c : ℕ) ∨
            (c : ℕ) * q = (v : ℕ))) ∨
          ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ Y < p ∧
            (c : ℕ) * p = (w : ℕ) ∧
              ((v : ℕ) * q = (w : ℕ) ∨
                (w : ℕ) * q = (v : ℕ))) := by
  obtain ⟨w, hw, hwv⟩ := mem_smallPrimeFirstExitSupport.mp hv
  obtain ⟨q, hq, hqS, hqY, hforms⟩ :=
    smallPrime_firstExit_arithmeticForms hc hw
      ((smallPrimeGraph S X Y).adj_comm v w |>.mpr hwv)
  exact ⟨w, hw, q, hq, hqS, hqY, hforms⟩

/-- If a residual edge leaves a large-prime child, that child's unique large
prime label divides the exit vertex. -/
theorem exists_largePrimeLabel_dvd_of_smallPrimeAdj_child
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hchild : IsLargePrimeChild S Y c w)
    (hwv : (smallPrimeGraph S X Y).Adj w v) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ Y < p ∧
      (c : ℕ) * p = (w : ℕ) ∧ p ∣ (v : ℕ) := by
  obtain ⟨p, hp, hpS, hYp, hcp⟩ := hchild
  obtain ⟨q, hq, _hqS, hqY, hEdge⟩ :=
    smallPrimeGraph_adj_iff_smallPrimeAdj.mp hwv
  refine ⟨p, hp, hpS, hYp, hcp, ?_⟩
  rcases hEdge with hwq | hvq
  · refine ⟨(c : ℕ) * q, ?_⟩
    calc
      (v : ℕ) = (w : ℕ) * q := hwq.symm
      _ = ((c : ℕ) * p) * q := by rw [hcp]
      _ = p * ((c : ℕ) * q) := by ac_rfl
  · have hpDvd : p ∣ (v : ℕ) * q := by
      refine ⟨(c : ℕ), ?_⟩
      calc
        (v : ℕ) * q = (w : ℕ) := hvq
        _ = (c : ℕ) * p := hcp.symm
        _ = p * (c : ℕ) := Nat.mul_comm _ _
    rcases hp.dvd_mul.mp hpDvd with hpv | hpq
    · exact hpv
    · have hpqEq : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
      exact False.elim ((not_lt_of_ge hqY) (hpqEq ▸ hYp))

/-- A residual neighbour of the centre cannot be divisible by a prime larger
than the cutoff. -/
theorem not_dvd_of_largePrime_of_smallPrimeAdj_center
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X} {p : ℕ}
    (hc : (c : ℕ) ≤ Y) (hp : p.Prime) (hYp : Y < p)
    (hpv : p ∣ (v : ℕ))
    (hcv : (smallPrimeGraph S X Y).Adj c v) : False := by
  obtain ⟨q, hq, _hqS, hqY, hEdge⟩ :=
    smallPrimeGraph_adj_iff_smallPrimeAdj.mp hcv
  rcases hEdge with hcq | hvq
  · have hpDvdCQ : p ∣ (c : ℕ) * q := by simpa [hcq] using hpv
    rcases hp.dvd_mul.mp hpDvdCQ with hpc | hpq
    · have hple : p ≤ (c : ℕ) := Nat.le_of_dvd (Vertex.coe_pos c) hpc
      exact (not_lt_of_ge (hple.trans hc)) hYp
    · have hpqEq : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
      exact (not_lt_of_ge hqY) (hpqEq ▸ hYp)
  · have hpc : p ∣ (c : ℕ) := by
      refine dvd_trans hpv ?_
      exact ⟨q, by simpa [Nat.mul_comm] using hvq.symm⟩
    have hple : p ≤ (c : ℕ) := Nat.le_of_dvd (Vertex.coe_pos c) hpc
    exact (not_lt_of_ge (hple.trans hc)) hYp

/-- Every first-exit coordinate has a unique residual neighbour in the
original closed large-prime star. -/
theorem unique_smallPrime_neighbor_in_largePrimeStar
    {S : Finset ℕ} {X Y : ℕ} {c v w₁ w₂ : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hw₁ : w₁ ∈ largePrimeStarSupport S X Y c)
    (hw₂ : w₂ ∈ largePrimeStarSupport S X Y c)
    (h₁v : (smallPrimeGraph S X Y).Adj w₁ v)
    (h₂v : (smallPrimeGraph S X Y).Adj w₂ v) :
    w₁ = w₂ := by
  rw [mem_largePrimeStarSupport] at hw₁ hw₂
  rcases hw₁ with rfl | hchild₁ <;> rcases hw₂ with rfl | hchild₂
  · rfl
  · obtain ⟨p, hp, _hpS, hYp, _hcp, hpv⟩ :=
      exists_largePrimeLabel_dvd_of_smallPrimeAdj_child
        (isLargePrimeChild_of_largePrimeAdj_of_le hc hchild₂) h₂v
    exact False.elim
      (not_dvd_of_largePrime_of_smallPrimeAdj_center hc hp hYp hpv h₁v)
  · obtain ⟨p, hp, _hpS, hYp, _hcp, hpv⟩ :=
      exists_largePrimeLabel_dvd_of_smallPrimeAdj_child
        (isLargePrimeChild_of_largePrimeAdj_of_le hc hchild₁) h₁v
    exact False.elim
      (not_dvd_of_largePrime_of_smallPrimeAdj_center hc hp hYp hpv h₂v)
  · obtain ⟨p, hp, _hpS, hYp, hcp, hpv⟩ :=
      exists_largePrimeLabel_dvd_of_smallPrimeAdj_child
        (isLargePrimeChild_of_largePrimeAdj_of_le hc hchild₁) h₁v
    obtain ⟨q, hq, _hqS, hYq, hcq, hqv⟩ :=
      exists_largePrimeLabel_dvd_of_smallPrimeAdj_child
        (isLargePrimeChild_of_largePrimeAdj_of_le hc hchild₂) h₂v
    have hpq : p = q := largePrime_dvd_unique
      (Vertex.coe_pos v) (Vertex.coe_le v) hcut hp hq hYp hYq hpv hqv
    apply Subtype.ext
    apply Fin.ext
    calc
      (w₁ : ℕ) = (c : ℕ) * p := hcp.symm
      _ = (c : ℕ) * q := by rw [hpq]
      _ = (w₂ : ℕ) := hcq

/-- No first-exit vertex lies back inside the original closed star. -/
theorem disjoint_smallPrimeFirstExitSupport_largePrimeStarSupport
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hc : (c : ℕ) ≤ Y) :
    Disjoint
      (smallPrimeFirstExitSupport S X Y c)
      (largePrimeStarSupport S X Y c) := by
  rw [Finset.disjoint_left]
  intro v hvExit hvStar
  obtain ⟨w, hwStar, hwv⟩ := mem_smallPrimeFirstExitSupport.mp hvExit
  exact not_smallPrimeGraph_adj_on_largePrimeStarSupport
    hc hwStar hvStar hwv

/-- Applying the residual adjacency to a signed star vector produces no
coordinate outside the exact first-exit support. -/
theorem smallPrime_mulVec_signedStarVector_eq_zero_of_not_mem_firstExitSupport
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X} {ε : ℝ}
    (hv : v ∉ smallPrimeFirstExitSupport S X Y c) :
    Matrix.mulVec ((smallPrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeSignedStarVector S X Y c ε) v = 0 := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hwsupp : w ∈ largePrimeStarSupport S X Y c
  · exfalso
    apply hv
    rw [mem_smallPrimeFirstExitSupport]
    exact ⟨w, hwsupp,
      ((smallPrimeGraph S X Y).adj_comm w v).mpr (by simpa using hw)⟩
  · simp [largePrimeSignedStarVector_eq_zero_of_not_mem hwsupp]

/-- The support statement is not special to the signed mode: residual
adjacency sends every vector supported on the closed star into the same exact
first-exit set. -/
theorem smallPrime_mulVec_eq_zero_of_not_mem_firstExitSupport_of_supported
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X}
    (x : Vertex S X → ℝ)
    (hx : ∀ w, w ∉ largePrimeStarSupport S X Y c → x w = 0)
    (hv : v ∉ smallPrimeFirstExitSupport S X Y c) :
    Matrix.mulVec ((smallPrimeGraph S X Y).adjMatrix ℝ) x v = 0 := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  apply Finset.sum_eq_zero
  intro w hw
  have hwsupp : w ∉ largePrimeStarSupport S X Y c := by
    intro hwsupp
    apply hv
    rw [mem_smallPrimeFirstExitSupport]
    exact ⟨w, hwsupp,
      ((smallPrimeGraph S X Y).adj_comm w v).mpr (by simpa using hw)⟩
  simp [hx w hwsupp]

/-- The lower large-prime centres whose closed stars meet the first-exit
support. This is the canonical finite index set for the non-isolated part of
the first-exit compression. -/
def firstExitLowerCenters
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) : Finset (Vertex S X) :=
  Finset.univ.filter fun k =>
    (k : ℕ) ≤ Y ∧
      ∃ v ∈ smallPrimeFirstExitSupport S X Y c,
        ¬(largePrimeGraph S X Y).IsIsolated v ∧
          v ∈ largePrimeStarSupport S X Y k

@[simp]
theorem mem_firstExitLowerCenters
    {S : Finset ℕ} {X Y : ℕ} {c k : Vertex S X} :
    k ∈ firstExitLowerCenters S X Y c ↔
      (k : ℕ) ≤ Y ∧
        ∃ v ∈ smallPrimeFirstExitSupport S X Y c,
          ¬(largePrimeGraph S X Y).IsIsolated v ∧
            v ∈ largePrimeStarSupport S X Y k := by
  simp [firstExitLowerCenters]

/-- First-exit vertices that are isolated in the large-prime graph. -/
def firstExitIsolatedVertices
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) : Finset (Vertex S X) :=
  (smallPrimeFirstExitSupport S X Y c).filter fun v =>
    (largePrimeGraph S X Y).IsIsolated v

@[simp]
theorem mem_firstExitIsolatedVertices
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X} :
    v ∈ firstExitIsolatedVertices S X Y c ↔
      v ∈ smallPrimeFirstExitSupport S X Y c ∧
        (largePrimeGraph S X Y).IsIsolated v := by
  simp [firstExitIsolatedVertices]

/-- The exact large-prime invariant support generated by the first exits: the
union of all lower stars they meet, together with the exits that are
large-prime isolated. -/
def firstExitCompressionSupport
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) : Finset (Vertex S X) :=
  largePrimeStarUnionSupport S X Y (firstExitLowerCenters S X Y c) ∪
    firstExitIsolatedVertices S X Y c

/-- Every first-exit vertex belongs to its canonical large-prime invariant
compression. -/
theorem smallPrimeFirstExitSupport_subset_firstExitCompressionSupport
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) :
    smallPrimeFirstExitSupport S X Y c ⊆
      firstExitCompressionSupport S X Y c := by
  intro v hv
  by_cases hiso : (largePrimeGraph S X Y).IsIsolated v
  · apply Finset.mem_union_right
    exact mem_firstExitIsolatedVertices.mpr ⟨hv, hiso⟩
  · obtain ⟨k, hkY, hvk⟩ :=
      exists_largePrimeStarSupport_of_not_isolated hcut hiso
    apply Finset.mem_union_left
    rw [mem_largePrimeStarUnionSupport]
    refine ⟨k, ?_, hvk⟩
    exact mem_firstExitLowerCenters.mpr ⟨hkY, v, hv, hiso, hvk⟩

/-- The canonical first-exit compression is closed under every large-prime
edge. Hence the large-prime adjacency has no matrix entry between this
compression and its complement. -/
theorem firstExitCompressionSupport_closed_under_largePrimeAdj
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hv : v ∈ firstExitCompressionSupport S X Y c)
    (hvw : LargePrimeAdj S Y v w) :
    w ∈ firstExitCompressionSupport S X Y c := by
  rcases Finset.mem_union.mp hv with hvStars | hvIso
  · obtain ⟨k, hkC, _hvk, hkw⟩ :=
      exists_common_starSupport_of_mem_union_of_largePrimeAdj hcut
        (fun k hk => (mem_firstExitLowerCenters.mp hk).1) hvStars hvw
    apply Finset.mem_union_left
    exact mem_largePrimeStarUnionSupport.mpr ⟨k, hkC, hkw⟩
  · have hiso : (largePrimeGraph S X Y).IsIsolated v :=
      (mem_firstExitIsolatedVertices.mp hvIso).2
    exact False.elim (hiso w hvw)

/-- Equivalent matrix-entry form of large-prime invariance: no edge leaves
the first-exit compression. -/
theorem not_largePrimeAdj_of_mem_firstExitCompressionSupport_of_not_mem
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hv : v ∈ firstExitCompressionSupport S X Y c)
    (hw : w ∉ firstExitCompressionSupport S X Y c) :
    ¬LargePrimeAdj S Y v w := by
  intro hvw
  exact hw (firstExitCompressionSupport_closed_under_largePrimeAdj hcut hv hvw)

/-- A centre selected by a non-isolated first exit is itself non-isolated in
the large-prime graph. -/
theorem not_isolated_of_mem_firstExitLowerCenters
    {S : Finset ℕ} {X Y : ℕ} {c k : Vertex S X}
    (hk : k ∈ firstExitLowerCenters S X Y c) :
    ¬(largePrimeGraph S X Y).IsIsolated k := by
  obtain ⟨_hkY, v, _hvExit, hvNonisolated, hvk⟩ :=
    mem_firstExitLowerCenters.mp hk
  rw [mem_largePrimeStarSupport] at hvk
  rcases hvk with rfl | hkv
  · exact hvNonisolated
  · intro hkIso
    exact hkIso v hkv

/-- Every vertex in a selected closed star is non-isolated. -/
theorem not_isolated_of_mem_selected_largePrimeStarSupport
    {S : Finset ℕ} {X Y : ℕ} {c k v : Vertex S X}
    (hk : k ∈ firstExitLowerCenters S X Y c)
    (hv : v ∈ largePrimeStarSupport S X Y k) :
    ¬(largePrimeGraph S X Y).IsIsolated v := by
  rw [mem_largePrimeStarSupport] at hv
  rcases hv with rfl | hkv
  · exact not_isolated_of_mem_firstExitLowerCenters hk
  · intro hvIso
    exact hvIso k (largePrimeAdj_symm hkv)

/-- The union of selected non-isolated stars is disjoint from the isolated
first-exit block. -/
theorem disjoint_largePrimeStarUnionSupport_firstExitIsolatedVertices
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} :
    Disjoint
      (largePrimeStarUnionSupport S X Y (firstExitLowerCenters S X Y c))
      (firstExitIsolatedVertices S X Y c) := by
  rw [Finset.disjoint_left]
  intro v hvStars hvIso
  obtain ⟨k, hk, hvk⟩ := mem_largePrimeStarUnionSupport.mp hvStars
  exact not_isolated_of_mem_selected_largePrimeStarSupport hk hvk
    (mem_firstExitIsolatedVertices.mp hvIso).2

/-- If a residual edge joins two non-isolated lower large-prime stars, their
centres differ by exactly the residual prime label. This is the arithmetic
identification of the manuscript's up- and down-star centres. -/
theorem smallPrimeAdj_between_largePrimeStarSupports_centers
    {S : Finset ℕ} {X Y : ℕ} {c k w v : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y) (hk : (k : ℕ) ≤ Y)
    (hw : w ∈ largePrimeStarSupport S X Y c)
    (hv : v ∈ largePrimeStarSupport S X Y k)
    (hwv : (smallPrimeGraph S X Y).Adj w v) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ≤ Y ∧
      ((c : ℕ) * q = (k : ℕ) ∨ (k : ℕ) * q = (c : ℕ)) := by
  obtain ⟨q, hq, hqS, hqY, hEdge⟩ :=
    smallPrimeGraph_adj_iff_smallPrimeAdj.mp hwv
  rw [mem_largePrimeStarSupport] at hw hv
  rcases hw with hwc | hcw
  · rcases hv with hvk0 | hkv
    · exact ⟨q, hq, hqS, hqY, by simpa [hwc, hvk0] using hEdge⟩
    · obtain ⟨r, hr, _hrS, hYr, hkr⟩ :=
        isLargePrimeChild_of_largePrimeAdj_of_le hk hkv
      exfalso
      rcases hEdge with hcq | hvq
      · have hrDvd : r ∣ (c : ℕ) * q := by
          refine ⟨(k : ℕ), ?_⟩
          calc
            (c : ℕ) * q = (v : ℕ) := by simpa [hwc] using hcq
            _ = (k : ℕ) * r := hkr.symm
            _ = r * (k : ℕ) := Nat.mul_comm _ _
        rcases hr.dvd_mul.mp hrDvd with hrc | hrq
        · have hrcLe : r ≤ (c : ℕ) :=
            Nat.le_of_dvd (Vertex.coe_pos c) hrc
          exact (not_le_of_gt (hc.trans_lt hYr)) hrcLe
        · have hrqLe : r ≤ q := Nat.le_of_dvd hq.pos hrq
          exact (not_le_of_gt (hqY.trans_lt hYr)) hrqLe
      · have hvLe : (v : ℕ) ≤ (v : ℕ) * q :=
          Nat.le_mul_of_pos_right _ hq.pos
        have : (v : ℕ) ≤ (c : ℕ) := by
          have hvqc : (v : ℕ) * q = (c : ℕ) := by simpa [hwc] using hvq
          simpa [hvqc] using hvLe
        have hcv : (c : ℕ) < (v : ℕ) :=
          hc.trans_lt (isLargePrimeChild_cutoff_lt_child
            (isLargePrimeChild_of_largePrimeAdj_of_le hk hkv))
        exact (not_le_of_gt hcv) this
  · rcases hv with hvk0 | hkv
    · obtain ⟨p, hp, _hpS, hYp, hcp⟩ :=
        isLargePrimeChild_of_largePrimeAdj_of_le hc hcw
      exfalso
      rcases hEdge with hwq | hkq
      · have hwLe : (w : ℕ) ≤ (w : ℕ) * q :=
          Nat.le_mul_of_pos_right _ hq.pos
        have : (w : ℕ) ≤ (k : ℕ) := by
          have hwqk : (w : ℕ) * q = (k : ℕ) := by simpa [hvk0] using hwq
          simpa [hwqk] using hwLe
        have hkw : (k : ℕ) < (w : ℕ) :=
          hk.trans_lt (isLargePrimeChild_cutoff_lt_child
            (isLargePrimeChild_of_largePrimeAdj_of_le hc hcw))
        exact (not_le_of_gt hkw) this
      · have hpDvd : p ∣ (k : ℕ) * q := by
          refine ⟨(c : ℕ), ?_⟩
          calc
            (k : ℕ) * q = (w : ℕ) := by simpa [hvk0] using hkq
            _ = (c : ℕ) * p := hcp.symm
            _ = p * (c : ℕ) := Nat.mul_comm _ _
        rcases hp.dvd_mul.mp hpDvd with hpk | hpq
        · have hpkLe : p ≤ (k : ℕ) :=
            Nat.le_of_dvd (Vertex.coe_pos k) hpk
          exact (not_le_of_gt (hk.trans_lt hYp)) hpkLe
        · have hpqLe : p ≤ q := Nat.le_of_dvd hq.pos hpq
          exact (not_le_of_gt (hqY.trans_lt hYp)) hpqLe
    · obtain ⟨p, hp, _hpS, hYp, hcp⟩ :=
        isLargePrimeChild_of_largePrimeAdj_of_le hc hcw
      obtain ⟨r, hr, _hrS, hYr, hkr⟩ :=
        isLargePrimeChild_of_largePrimeAdj_of_le hk hkv
      rcases hEdge with hwq | hvq
      · have hpDvdV : p ∣ (v : ℕ) := by
          refine ⟨(c : ℕ) * q, ?_⟩
          calc
            (v : ℕ) = (w : ℕ) * q := hwq.symm
            _ = ((c : ℕ) * p) * q := by rw [hcp]
            _ = p * ((c : ℕ) * q) := by ac_rfl
        have hrDvdV : r ∣ (v : ℕ) := by
          refine ⟨(k : ℕ), ?_⟩
          simpa [Nat.mul_comm] using hkr.symm
        have hpr : p = r :=
          largePrime_dvd_unique (Vertex.coe_pos v) (Vertex.coe_le v) hcut
            hp hr hYp hYr hpDvdV hrDvdV
        subst r
        have hcancel : ((c : ℕ) * q) * p = (k : ℕ) * p := by
          calc
            ((c : ℕ) * q) * p = ((c : ℕ) * p) * q := by ac_rfl
            _ = (w : ℕ) * q := by rw [hcp]
            _ = (v : ℕ) := hwq
            _ = (k : ℕ) * p := hkr.symm
        exact ⟨q, hq, hqS, hqY,
          Or.inl (Nat.eq_of_mul_eq_mul_right hp.pos hcancel)⟩
      · have hrDvdW : r ∣ (w : ℕ) := by
          refine ⟨(k : ℕ) * q, ?_⟩
          calc
            (w : ℕ) = (v : ℕ) * q := hvq.symm
            _ = ((k : ℕ) * r) * q := by rw [hkr]
            _ = r * ((k : ℕ) * q) := by ac_rfl
        have hpDvdW : p ∣ (w : ℕ) := by
          refine ⟨(c : ℕ), ?_⟩
          simpa [Nat.mul_comm] using hcp.symm
        have hpr : p = r :=
          largePrime_dvd_unique (Vertex.coe_pos w) (Vertex.coe_le w) hcut
            hp hr hYp hYr hpDvdW hrDvdW
        subst r
        have hcancel : ((k : ℕ) * q) * p = (c : ℕ) * p := by
          calc
            ((k : ℕ) * q) * p = ((k : ℕ) * p) * q := by ac_rfl
            _ = (v : ℕ) * q := by rw [hkr]
            _ = (w : ℕ) := hvq
            _ = (c : ℕ) * p := hcp.symm
        exact ⟨q, hq, hqS, hqY,
          Or.inr (Nat.eq_of_mul_eq_mul_right hp.pos hcancel)⟩

/-- Every selected non-isolated first-exit star has one of the manuscript's
arithmetic centres obtained by multiplying or dividing the original centre by
one residual prime. -/
theorem mem_firstExitLowerCenters_arithmetic
    {S : Finset ℕ} {X Y : ℕ} {c k : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hkC : k ∈ firstExitLowerCenters S X Y c) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ≤ Y ∧
      ((c : ℕ) * q = (k : ℕ) ∨ (k : ℕ) * q = (c : ℕ)) := by
  obtain ⟨hkY, v, hvExit, _hvNonisolated, hvk⟩ :=
    mem_firstExitLowerCenters.mp hkC
  obtain ⟨w, hwc, hwv⟩ := mem_smallPrimeFirstExitSupport.mp hvExit
  exact smallPrimeAdj_between_largePrimeStarSupports_centers
    hcut hc hkY hwc hvk hwv

/-- A product of two primes is not prime. -/
theorem mul_primes_ne_prime {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) :
    p * q ≠ r := by
  intro h
  have hmul : (p * q).Prime := by simpa [h] using hr
  exact Nat.not_prime_mul hp.ne_one hq.ne_one hmul

/-- Two prime-step neighbours of the same positive integer cannot themselves
differ by one prime step. -/
theorem no_prime_step_between_primeStepNeighbors
    {a k l q r ell : ℕ}
    (ha : 0 < a) (hkPos : 0 < k) (hlPos : 0 < l)
    (hq : q.Prime) (hr : r.Prime) (hell : ell.Prime)
    (hk : a * q = k ∨ k * q = a)
    (hl : a * r = l ∨ l * r = a)
    (hkl : k * ell = l ∨ l * ell = k) : False := by
  rcases hk with hkUp | hkDown <;>
    rcases hl with hlUp | hlDown <;>
      rcases hkl with hklUp | hklDown
  · have hcancel : a * (q * ell) = a * r := by
      calc
        a * (q * ell) = (a * q) * ell := by ac_rfl
        _ = k * ell := by rw [hkUp]
        _ = l := hklUp
        _ = a * r := hlUp.symm
    have hqe : q * ell = r := Nat.eq_of_mul_eq_mul_left ha hcancel
    exact mul_primes_ne_prime hq hell hr hqe
  · have hcancel : a * (r * ell) = a * q := by
      calc
        a * (r * ell) = (a * r) * ell := by ac_rfl
        _ = l * ell := by rw [hlUp]
        _ = k := hklDown
        _ = a * q := hkUp.symm
    have hre : r * ell = q := Nat.eq_of_mul_eq_mul_left ha hcancel
    exact mul_primes_ne_prime hr hell hq hre
  · have hcancel : a * ((q * ell) * r) = a * 1 := by
      calc
        a * ((q * ell) * r) = ((a * q) * ell) * r := by ac_rfl
        _ = (k * ell) * r := by rw [hkUp]
        _ = l * r := by rw [hklUp]
        _ = a := hlDown
        _ = a * 1 := by simp
    have hprod : (q * ell) * r = 1 :=
      Nat.eq_of_mul_eq_mul_left ha hcancel
    have hqDvd : q ∣ 1 := by
      refine ⟨ell * r, ?_⟩
      simpa [Nat.mul_assoc] using hprod.symm
    exact hq.ne_one (Nat.eq_one_of_dvd_one hqDvd)
  · have hcancel : a * ell = a * (q * r) := by
      calc
        a * ell = (l * r) * ell := by rw [hlDown]
        _ = (l * ell) * r := by ac_rfl
        _ = k * r := by rw [hklDown]
        _ = (a * q) * r := by rw [hkUp]
        _ = a * (q * r) := by ac_rfl
    have her : ell = q * r := Nat.eq_of_mul_eq_mul_left ha hcancel
    exact mul_primes_ne_prime hq hr hell her.symm
  · have hcancel : a * ell = a * (r * q) := by
      calc
        a * ell = (k * q) * ell := by rw [hkDown]
        _ = (k * ell) * q := by ac_rfl
        _ = l * q := by rw [hklUp]
        _ = (a * r) * q := by rw [hlUp]
        _ = a * (r * q) := by ac_rfl
    have her : ell = r * q := Nat.eq_of_mul_eq_mul_left ha hcancel
    exact mul_primes_ne_prime hr hq hell her.symm
  · have hcancel : a * ((r * ell) * q) = a * 1 := by
      calc
        a * ((r * ell) * q) = ((a * r) * ell) * q := by ac_rfl
        _ = (l * ell) * q := by rw [hlUp]
        _ = k * q := by rw [hklDown]
        _ = a := hkDown
        _ = a * 1 := by simp
    have hprod : (r * ell) * q = 1 :=
      Nat.eq_of_mul_eq_mul_left ha hcancel
    have hrDvd : r ∣ 1 := by
      refine ⟨ell * q, ?_⟩
      simpa [Nat.mul_assoc] using hprod.symm
    exact hr.ne_one (Nat.eq_one_of_dvd_one hrDvd)
  · have hcancel : k * (ell * r) = k * q := by
      calc
        k * (ell * r) = (k * ell) * r := by ac_rfl
        _ = l * r := by rw [hklUp]
        _ = a := hlDown
        _ = k * q := hkDown.symm
    have her : ell * r = q := Nat.eq_of_mul_eq_mul_left hkPos hcancel
    exact mul_primes_ne_prime hell hr hq her
  · have hcancel : l * (ell * q) = l * r := by
      calc
        l * (ell * q) = (l * ell) * q := by ac_rfl
        _ = k * q := by rw [hklDown]
        _ = a := hkDown
        _ = l * r := hlDown.symm
    have heq : ell * q = r := Nat.eq_of_mul_eq_mul_left hlPos hcancel
    exact mul_primes_ne_prime hell hq hr heq

/-- No residual small-prime edge joins two vertices of the selected
non-isolated star union. -/
theorem not_smallPrimeAdj_on_firstExitLargePrimeStarUnion
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hv : v ∈
      largePrimeStarUnionSupport S X Y (firstExitLowerCenters S X Y c))
    (hw : w ∈
      largePrimeStarUnionSupport S X Y (firstExitLowerCenters S X Y c)) :
    ¬(smallPrimeGraph S X Y).Adj v w := by
  intro hvw
  obtain ⟨k, hkC, hvk⟩ := mem_largePrimeStarUnionSupport.mp hv
  obtain ⟨l, hlC, hwl⟩ := mem_largePrimeStarUnionSupport.mp hw
  obtain ⟨q, hq, _hqS, _hqY, hkArithmetic⟩ :=
    mem_firstExitLowerCenters_arithmetic hcut hc hkC
  obtain ⟨r, hr, _hrS, _hrY, hlArithmetic⟩ :=
    mem_firstExitLowerCenters_arithmetic hcut hc hlC
  obtain ⟨ell, hell, _hellS, _hellY, hklArithmetic⟩ :=
    smallPrimeAdj_between_largePrimeStarSupports_centers hcut
      (mem_firstExitLowerCenters.mp hkC).1
      (mem_firstExitLowerCenters.mp hlC).1 hvk hwl hvw
  exact no_prime_step_between_primeStepNeighbors
    (Vertex.coe_pos c) (Vertex.coe_pos k) (Vertex.coe_pos l)
    hq hr hell hkArithmetic hlArithmetic hklArithmetic

/-- The canonical first-exit compression lies entirely outside the original
closed large-prime star. -/
theorem disjoint_firstExitCompressionSupport_largePrimeStarSupport
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y) :
    Disjoint (firstExitCompressionSupport S X Y c)
      (largePrimeStarSupport S X Y c) := by
  rw [Finset.disjoint_left]
  intro v hvCompression hvStar
  rcases Finset.mem_union.mp hvCompression with hvUnion | hvIso
  · obtain ⟨k, hk, hvk⟩ := mem_largePrimeStarUnionSupport.mp hvUnion
    have hkc : k ≠ c := by
      intro hkc
      subst k
      obtain ⟨_hkY, w, hwExit, _hwNonisolated, hwStar⟩ :=
        mem_firstExitLowerCenters.mp hk
      exact (Finset.disjoint_left.mp
        (disjoint_smallPrimeFirstExitSupport_largePrimeStarSupport hc))
          hwExit hwStar
    exact (Finset.disjoint_left.mp
      (disjoint_largePrimeStarSupport hcut hc
        (mem_firstExitLowerCenters.mp hk).1 (Ne.symm hkc))) hvStar hvk
  · have hvExit := (mem_firstExitIsolatedVertices.mp hvIso).1
    exact (Finset.disjoint_left.mp
      (disjoint_smallPrimeFirstExitSupport_largePrimeStarSupport hc))
        hvExit hvStar

/-- Restriction of a vector to a finite coordinate block. -/
def restrictVectorToFinset {R : Type*} [Zero R] {S : Finset ℕ} {X : ℕ}
    (F : Finset (Vertex S X)) (b : Vertex S X → R) : Vertex S X → R :=
  fun v => if v ∈ F then b v else 0

@[simp]
theorem restrictVectorToFinset_apply {R : Type*} [Zero R]
    {S : Finset ℕ} {X : ℕ} (F : Finset (Vertex S X))
    (b : Vertex S X → R) (v : Vertex S X) :
    restrictVectorToFinset F b v = if v ∈ F then b v else 0 :=
  rfl

/-- Euclidean-space version of coordinate restriction to a finite block. -/
def restrictEuclideanToFinset {S : Finset ℕ} {X : ℕ}
    (F : Finset (Vertex S X))
    (b : EuclideanSpace ℝ (Vertex S X)) :
    EuclideanSpace ℝ (Vertex S X) :=
  WithLp.toLp 2 (restrictVectorToFinset F b)

@[simp]
theorem restrictEuclideanToFinset_apply
    {S : Finset ℕ} {X : ℕ} (F : Finset (Vertex S X))
    (b : EuclideanSpace ℝ (Vertex S X)) (v : Vertex S X) :
    restrictEuclideanToFinset F b v = if v ∈ F then b v else 0 :=
  rfl

/-- Restricting the right vector to `F` does not change an inner product whose
left vector is already supported on `F`. -/
theorem inner_restrictEuclideanToFinset_right_of_supported
    {S : Finset ℕ} {X : ℕ}
    (F : Finset (Vertex S X))
    (b x : EuclideanSpace ℝ (Vertex S X))
    (hb : ∀ v, v ∉ F → b v = 0) :
    ⟪b, restrictEuclideanToFinset F x⟫_ℝ = ⟪b, x⟫_ℝ := by
  simp only [PiLp.inner_apply, restrictEuclideanToFinset_apply]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hvF : v ∈ F
  · simp [hvF]
  · simp [hvF, hb v hvF]

/-- Large-prime adjacency annihilates every vector restricted to a set of
large-prime-isolated vertices. -/
theorem largePrime_toEuclideanLin_restrict_isolated_eq_zero
    {S : Finset ℕ} {X Y : ℕ}
    (F : Finset (Vertex S X))
    (b : EuclideanSpace ℝ (Vertex S X))
    (hF : ∀ v ∈ F, (largePrimeGraph S X Y).IsIsolated v) :
    Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (restrictEuclideanToFinset F b) = 0 := by
  rw [restrictEuclideanToFinset, Matrix.toLpLin_toLp 2 2]
  congr 1
  funext v
  rw [Matrix.toLin'_apply, SimpleGraph.adjMatrix_mulVec_apply]
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hwF : w ∈ F
  · exfalso
    exact hF w hwF v
      ((largePrimeGraph S X Y).adj_comm w v |>.mpr (by simpa using hw))
  · simp [restrictVectorToFinset, hwF]

/-- The isolated block in the canonical first-exit compression is killed by
large-prime adjacency. -/
theorem largePrime_toEuclideanLin_firstExitIsolatedBlock_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (b : EuclideanSpace ℝ (Vertex S X)) :
    Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (restrictEuclideanToFinset (firstExitIsolatedVertices S X Y c) b) = 0 := by
  apply largePrime_toEuclideanLin_restrict_isolated_eq_zero
  intro v hv
  exact (mem_firstExitIsolatedVertices.mp hv).2

/-- Any vector supported on the first-exit set is the direct sum of its
selected-star blocks and its isolated block. This is the literal finite
vector identity behind Proposition 8.1. -/
theorem vector_eq_sum_firstExitStarBlocks_add_isolatedBlock
    {R : Type*} [AddCommMonoid R]
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (b : Vertex S X → R)
    (hb : ∀ v, v ∉ smallPrimeFirstExitSupport S X Y c → b v = 0) :
    b =
      (∑ k ∈ firstExitLowerCenters S X Y c,
        restrictVectorToFinset (largePrimeStarSupport S X Y k) b) +
      restrictVectorToFinset (firstExitIsolatedVertices S X Y c) b := by
  funext v
  simp only [Pi.add_apply, Finset.sum_apply, restrictVectorToFinset_apply]
  by_cases hbv : b v = 0
  · simp [hbv]
  have hvExit : v ∈ smallPrimeFirstExitSupport S X Y c := by
    by_contra hv
    exact hbv (hb v hv)
  have hvCompression :=
    smallPrimeFirstExitSupport_subset_firstExitCompressionSupport hcut hvExit
  rcases Finset.mem_union.mp hvCompression with hvStars | hvIso
  · obtain ⟨k, hkC, hvk⟩ := mem_largePrimeStarUnionSupport.mp hvStars
    have hvNotIso : v ∉ firstExitIsolatedVertices S X Y c := by
      intro hvI
      exact not_isolated_of_mem_selected_largePrimeStarSupport hkC hvk
        (mem_firstExitIsolatedVertices.mp hvI).2
    have hsum :
        (∑ l ∈ firstExitLowerCenters S X Y c,
          if v ∈ largePrimeStarSupport S X Y l then b v else 0) = b v := by
      calc
        (∑ l ∈ firstExitLowerCenters S X Y c,
            if v ∈ largePrimeStarSupport S X Y l then b v else 0) =
            (if v ∈ largePrimeStarSupport S X Y k then b v else 0) := by
          apply Finset.sum_eq_single k
          · intro l hlC hlk
            have hvNot : v ∉ largePrimeStarSupport S X Y l := by
              intro hvl
              have hdisjoint :=
                disjoint_largePrimeStarSupport hcut
                  (mem_firstExitLowerCenters.mp hkC).1
                  (mem_firstExitLowerCenters.mp hlC).1
                  (Ne.symm hlk)
              exact (Finset.disjoint_left.mp hdisjoint) hvk hvl
            simp [hvNot]
          · intro hkNot
            exact False.elim (hkNot hkC)
        _ = b v := if_pos hvk
    rw [hsum]
    simp [hvNotIso]
  · have hsum :
        (∑ k ∈ firstExitLowerCenters S X Y c,
          if v ∈ largePrimeStarSupport S X Y k then b v else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hkC
      have hvNot : v ∉ largePrimeStarSupport S X Y k := by
        intro hvk
        exact not_isolated_of_mem_selected_largePrimeStarSupport hkC hvk
          (mem_firstExitIsolatedVertices.mp hvIso).2
      simp [hvNot]
    rw [hsum]
    simp [hvIso]

/-- Euclidean-space form of the exact first-exit block decomposition. -/
theorem euclidean_eq_sum_firstExitStarBlocks_add_isolatedBlock
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (b : EuclideanSpace ℝ (Vertex S X))
    (hb : ∀ v, v ∉ smallPrimeFirstExitSupport S X Y c → b v = 0) :
    b =
      (∑ k ∈ firstExitLowerCenters S X Y c,
        restrictEuclideanToFinset (largePrimeStarSupport S X Y k) b) +
      restrictEuclideanToFinset (firstExitIsolatedVertices S X Y c) b := by
  ext v
  have h := congrFun
    (vector_eq_sum_firstExitStarBlocks_add_isolatedBlock hcut
      (fun w ↦ b w) hb) v
  simpa [restrictEuclideanToFinset, Finset.sum_apply] using h

/-- The residual adjacency applied to the literal signed star mode is exactly
the finite direct sum of its selected-star and isolated first-exit blocks. -/
theorem smallPrime_mulVec_signedStarVector_eq_sum_firstExitBlocks
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) :
    Matrix.mulVec ((smallPrimeGraph S X Y).adjMatrix ℝ)
        (largePrimeSignedStarVector S X Y c ε) =
      (∑ k ∈ firstExitLowerCenters S X Y c,
        restrictVectorToFinset (largePrimeStarSupport S X Y k)
          (Matrix.mulVec ((smallPrimeGraph S X Y).adjMatrix ℝ)
            (largePrimeSignedStarVector S X Y c ε))) +
      restrictVectorToFinset (firstExitIsolatedVertices S X Y c)
        (Matrix.mulVec ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeSignedStarVector S X Y c ε)) := by
  apply vector_eq_sum_firstExitStarBlocks_add_isolatedBlock hcut
  intro v hv
  exact
    smallPrime_mulVec_signedStarVector_eq_zero_of_not_mem_firstExitSupport hv

end

end PrimeStar
