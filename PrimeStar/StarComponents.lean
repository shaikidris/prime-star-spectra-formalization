import PrimeStar.StarForest
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Exact large-prime star components

At a square cutoff, every non-isolated component of the large-prime graph is
a star.  This file states that fact using the graph's actual neighbour
finsets: lower vertices are centres, their neighbours are leaves, every leaf
has the centre as its unique neighbour, and distinct closed star supports are
disjoint.
-/

namespace PrimeStar

noncomputable section

/-- Local decidability for large-prime adjacency in component calculations. -/
local instance largePrimeGraphDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The leaves attached to `c` in the large-prime graph. -/
def largePrimeLeaves (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    Finset (Vertex S X) :=
  (largePrimeGraph S X Y).neighborFinset c

@[simp]
theorem mem_largePrimeLeaves {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X} :
    v ∈ largePrimeLeaves S X Y c ↔ LargePrimeAdj S Y c v := by
  simp [largePrimeLeaves]

/-- The centre together with all leaves attached to it. -/
def largePrimeStarSupport (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :
    Finset (Vertex S X) :=
  insert c (largePrimeLeaves S X Y c)

@[simp]
theorem mem_largePrimeStarSupport {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X} :
    v ∈ largePrimeStarSupport S X Y c ↔ v = c ∨ LargePrimeAdj S Y c v := by
  simp [largePrimeStarSupport]

/-- An undirected large-prime edge has one of its two possible child orientations. -/
theorem largePrimeAdj_iff_child_or_child {S : Finset ℕ} {X Y : ℕ}
    {m n : Vertex S X} :
    LargePrimeAdj S Y m n ↔
      IsLargePrimeChild S Y m n ∨ IsLargePrimeChild S Y n m := by
  constructor
  · rintro ⟨p, hp, hpS, hYp, h | h⟩
    · exact Or.inl ⟨p, hp, hpS, hYp, h⟩
    · exact Or.inr ⟨p, hp, hpS, hYp, h⟩
  · rintro (h | h)
    · exact isLargePrimeChild_largePrimeAdj h
    · exact largePrimeAdj_symm (isLargePrimeChild_largePrimeAdj h)

/-- At a square cutoff, an edge leaving a lower vertex is oriented away from it. -/
theorem isLargePrimeChild_of_largePrimeAdj_of_le {S : Finset ℕ} {X Y : ℕ}
    {c v : Vertex S X} (hc : (c : ℕ) ≤ Y)
    (hcv : LargePrimeAdj S Y c v) : IsLargePrimeChild S Y c v := by
  rcases largePrimeAdj_iff_child_or_child.mp hcv with h | h
  · exact h
  · have hYc : Y < (c : ℕ) := isLargePrimeChild_cutoff_lt_child h
    exact False.elim ((not_lt_of_ge hc) hYc)

/-- For a lower centre, graph neighbours are exactly its oriented children. -/
theorem mem_largePrimeLeaves_iff_child {S : Finset ℕ} {X Y : ℕ}
    {c v : Vertex S X} (hc : (c : ℕ) ≤ Y) :
    v ∈ largePrimeLeaves S X Y c ↔ IsLargePrimeChild S Y c v := by
  rw [mem_largePrimeLeaves]
  exact ⟨isLargePrimeChild_of_largePrimeAdj_of_le hc,
    isLargePrimeChild_largePrimeAdj⟩

/-- Every leaf of a lower centre has that centre as its unique neighbour. -/
theorem largePrime_neighborFinset_leaf {S : Finset ℕ} {X Y : ℕ}
    {c v : Vertex S X} (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ largePrimeLeaves S X Y c) :
    (largePrimeGraph S X Y).neighborFinset v = {c} := by
  have hcv : IsLargePrimeChild S Y c v :=
    (mem_largePrimeLeaves_iff_child hc).mp hv
  ext w
  simp only [SimpleGraph.mem_neighborFinset, largePrimeGraph_adj, Finset.mem_singleton]
  constructor
  · intro hvw
    rcases largePrimeAdj_iff_child_or_child.mp hvw with hvw | hwv
    · have hv_le : (v : ℕ) ≤ Y := isLargePrimeChild_parent_le hcut hvw
      have hYv : Y < (v : ℕ) := isLargePrimeChild_cutoff_lt_child hcv
      exact False.elim ((not_lt_of_ge hv_le) hYv)
    · exact (isLargePrimeChild_parent_unique hcut hwv hcv)
  · rintro rfl
    exact largePrimeAdj_symm (isLargePrimeChild_largePrimeAdj hcv)

/-- The large-prime adjacency restricted to a closed centre support is exactly
the adjacency of a star. -/
theorem largePrimeAdj_on_starSupport_iff {S : Finset ℕ} {X Y : ℕ}
    {c v w : Vertex S X} (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ largePrimeStarSupport S X Y c)
    (hw : w ∈ largePrimeStarSupport S X Y c) :
    LargePrimeAdj S Y v w ↔ v ≠ w ∧ (v = c ∨ w = c) := by
  rw [mem_largePrimeStarSupport] at hv hw
  constructor
  · intro hvw
    refine ⟨(show (largePrimeGraph S X Y).Adj v w from hvw).ne, ?_⟩
    rcases hv with rfl | hcv
    · exact Or.inl rfl
    · have hvleaf : v ∈ largePrimeLeaves S X Y c := mem_largePrimeLeaves.mpr hcv
      have hneighbors := largePrime_neighborFinset_leaf hcut hc hvleaf
      have : w ∈ (largePrimeGraph S X Y).neighborFinset v := by simpa using hvw
      rw [hneighbors] at this
      exact Or.inr (Finset.mem_singleton.mp this)
  · rintro ⟨hvw, rfl | rfl⟩
    · rcases hw with rfl | hcw
      · exact False.elim (hvw rfl)
      · exact hcw
    · rcases hv with rfl | hcv
      · exact False.elim (hvw rfl)
      · exact largePrimeAdj_symm hcv

/-- The closed support of a centre has no large-prime edge leaving it. -/
theorem largePrimeStarSupport_closed {S : Finset ℕ} {X Y : ℕ}
    {c v w : Vertex S X} (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ largePrimeStarSupport S X Y c)
    (hvw : LargePrimeAdj S Y v w) :
    w ∈ largePrimeStarSupport S X Y c := by
  rw [mem_largePrimeStarSupport] at hv ⊢
  rcases hv with rfl | hcv
  · exact Or.inr hvw
  · have hvleaf : v ∈ largePrimeLeaves S X Y c := mem_largePrimeLeaves.mpr hcv
    have hneighbors := largePrime_neighborFinset_leaf hcut hc hvleaf
    have : w ∈ (largePrimeGraph S X Y).neighborFinset v := by simpa using hvw
    rw [hneighbors] at this
    exact Or.inl (Finset.mem_singleton.mp this)

/-- Closed star supports of two distinct lower centres are disjoint. -/
theorem disjoint_largePrimeStarSupport {S : Finset ℕ} {X Y : ℕ}
    {c k : Vertex S X} (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hk : (k : ℕ) ≤ Y) (hck : c ≠ k) :
    Disjoint (largePrimeStarSupport S X Y c) (largePrimeStarSupport S X Y k) := by
  rw [Finset.disjoint_left]
  intro v hvc hvk
  rw [mem_largePrimeStarSupport] at hvc hvk
  rcases hvc with hvc | hcv
  · rcases hvk with hvk | hkc
    · exact hck (hvc.symm.trans hvk)
    · have hYv : Y < (v : ℕ) :=
        isLargePrimeChild_cutoff_lt_child
          ((mem_largePrimeLeaves_iff_child hk).mp (mem_largePrimeLeaves.mpr hkc))
      exact (not_lt_of_ge (by simpa [hvc] using hc)) hYv
  · rcases hvk with hvk | hkv
    · have hYv : Y < (v : ℕ) :=
        isLargePrimeChild_cutoff_lt_child
          ((mem_largePrimeLeaves_iff_child hc).mp (mem_largePrimeLeaves.mpr hcv))
      exact (not_lt_of_ge (by simpa [hvk] using hk)) hYv
    · have hcv' : IsLargePrimeChild S Y c v :=
        (mem_largePrimeLeaves_iff_child hc).mp (mem_largePrimeLeaves.mpr hcv)
      have hkv' : IsLargePrimeChild S Y k v :=
        (mem_largePrimeLeaves_iff_child hk).mp (mem_largePrimeLeaves.mpr hkv)
      exact hck (isLargePrimeChild_parent_unique hcut hcv' hkv')

/-- No large-prime edge joins two distinct closed lower-star supports. -/
theorem not_largePrimeAdj_between_distinct_starSupports
    {S : Finset ℕ} {X Y : ℕ} {c k v w : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y) (hk : (k : ℕ) ≤ Y) (hck : c ≠ k)
    (hv : v ∈ largePrimeStarSupport S X Y c)
    (hw : w ∈ largePrimeStarSupport S X Y k) :
    ¬LargePrimeAdj S Y v w := by
  intro hvw
  have hwc : w ∈ largePrimeStarSupport S X Y c :=
    largePrimeStarSupport_closed hcut hc hv hvw
  have hdisjoint :=
    disjoint_largePrimeStarSupport hcut hc hk hck
  exact (Finset.disjoint_left.mp hdisjoint) hwc hw

/-- The union of the closed large-prime stars indexed by a finite centre set. -/
def largePrimeStarUnionSupport
    (S : Finset ℕ) (X Y : ℕ) (C : Finset (Vertex S X)) :
    Finset (Vertex S X) :=
  C.biUnion (largePrimeStarSupport S X Y)

@[simp]
theorem mem_largePrimeStarUnionSupport
    {S : Finset ℕ} {X Y : ℕ} {C : Finset (Vertex S X)}
    {v : Vertex S X} :
    v ∈ largePrimeStarUnionSupport S X Y C ↔
      ∃ c ∈ C, v ∈ largePrimeStarSupport S X Y c := by
  simp [largePrimeStarUnionSupport]

/-- Every large-prime edge whose first endpoint lies in a finite union of
lower-star supports remains inside the same constituent star. -/
theorem exists_common_starSupport_of_mem_union_of_largePrimeAdj
    {S : Finset ℕ} {X Y : ℕ} {C : Finset (Vertex S X)}
    {v w : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hcentres : ∀ c ∈ C, (c : ℕ) ≤ Y)
    (hv : v ∈ largePrimeStarUnionSupport S X Y C)
    (hvw : LargePrimeAdj S Y v w) :
    ∃ c ∈ C,
      v ∈ largePrimeStarSupport S X Y c ∧
      w ∈ largePrimeStarSupport S X Y c := by
  obtain ⟨c, hcC, hvc⟩ := mem_largePrimeStarUnionSupport.mp hv
  exact ⟨c, hcC, hvc,
    largePrimeStarSupport_closed hcut (hcentres c hcC) hvc hvw⟩

/-- Every non-isolated vertex lies in the closed support of a lower centre. -/
theorem exists_largePrimeStarSupport_of_not_isolated {S : Finset ℕ} {X Y : ℕ}
    (hcut : X < (Y + 1) * (Y + 1)) {v : Vertex S X}
    (hv : ¬(largePrimeGraph S X Y).IsIsolated v) :
    ∃ c : Vertex S X, (c : ℕ) ≤ Y ∧
      v ∈ largePrimeStarSupport S X Y c := by
  rw [← SimpleGraph.neighborFinset_nonempty] at hv
  obtain ⟨w, hw⟩ := hv
  have hvw : LargePrimeAdj S Y v w := by simpa using hw
  rcases largePrimeAdj_iff_child_or_child.mp hvw with hvw | hwv
  · refine ⟨v, isLargePrimeChild_parent_le hcut hvw, ?_⟩
    simp [largePrimeStarSupport]
  · refine ⟨w, isLargePrimeChild_parent_le hcut hwv, ?_⟩
    rw [mem_largePrimeStarSupport]
    exact Or.inr (isLargePrimeChild_largePrimeAdj hwv)

end

end PrimeStar
