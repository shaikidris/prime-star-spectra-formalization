import PrimeStar.SmallPrimeNorm
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The induced-root-star lower bound

The Euclidean adjacency norm of a finite simple graph dominates the square
root of every vertex degree. At the root of the residual prime-cover graph,
the degree is exactly the number of allowed primes up to the cutoff. This is
the finite lower-bound half of the manuscript's sharp residual-norm theorem;
its asymptotic evaluation is a separate prime-counting input.
-/

namespace PrimeStar

open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

/-- Local decidability for the residual graph's root-degree calculation. -/
local instance smallPrimeLowerBoundDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj := Classical.decRel _

/-- The adjacency norm of a finite simple graph dominates the square root of
each vertex degree. -/
theorem sqrt_degree_le_adjMatrix_norm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Real.sqrt (G.degree v : ℝ) ≤ ‖G.adjMatrix ℝ‖ := by
  let e : EuclideanSpace ℝ V := EuclideanSpace.single v 1
  have he : ‖e‖ = 1 := by simp [e]
  have hmul := (G.adjMatrix ℝ).l2_opNorm_mulVec e
  rw [he, mul_one] at hmul
  have hcoord (x : V) :
      Matrix.mulVec (G.adjMatrix ℝ) (e : V → ℝ) x =
        if G.Adj x v then 1 else 0 := by
    simp [Matrix.mulVec, e, SimpleGraph.adjMatrix_apply]
  have hfilter : Finset.univ.filter (fun x ↦ G.Adj x v) = G.neighborFinset v := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    exact G.adj_comm x v
  have hnormsq : ‖(EuclideanSpace.equiv V ℝ).symm
      (Matrix.mulVec (G.adjMatrix ℝ) (e : V → ℝ))‖ ^ 2 = (G.degree v : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ x, ‖Matrix.mulVec (G.adjMatrix ℝ) (e : V → ℝ) x‖ ^ 2) = _
    simp_rw [hcoord]
    simp [Real.norm_eq_abs, hfilter, ← SimpleGraph.card_neighborFinset_eq_degree]
  have hsqrt : Real.sqrt (G.degree v : ℝ) =
      ‖(EuclideanSpace.equiv V ℝ).symm
        (Matrix.mulVec (G.adjMatrix ℝ) (e : V → ℝ))‖ := by
    have hsqrtSq : (Real.sqrt (G.degree v : ℝ)) ^ 2 = (G.degree v : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (G.degree v : ℝ),
      norm_nonneg ((EuclideanSpace.equiv V ℝ).symm
        (Matrix.mulVec (G.adjMatrix ℝ) (e : V → ℝ)))]
  rw [hsqrt]
  exact hmul

/-- The vertex labelled `1`, under the manuscript hypothesis that every
deleted label is prime. -/
def primeCoverRoot {S : Finset ℕ} {X : ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hX : 1 ≤ X) : Vertex S X := by
  refine ⟨⟨1, Nat.lt_succ_iff.mpr hX⟩, by norm_num, ?_⟩
  intro q hqS
  exact (hS q hqS).not_dvd_one

@[simp]
theorem primeCoverRoot_coe {S : Finset ℕ} {X : ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hX : 1 ≤ X) :
    (primeCoverRoot hS hX : ℕ) = 1 := rfl

private def vertexOfAllowedPrime {S : Finset ℕ} {X p : ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hp : p.Prime) (hpS : p ∉ S)
    (hpX : p ≤ X) : Vertex S X := by
  refine ⟨⟨p, Nat.lt_succ_iff.mpr hpX⟩, hp.pos, ?_⟩
  intro q hqS hqdiv
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq (hS q hqS) hp).mp hqdiv
  exact hpS (hqp ▸ hqS)

@[simp]
private theorem vertexOfAllowedPrime_coe {S : Finset ℕ} {X p : ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hp : p.Prime) (hpS : p ∉ S)
    (hpX : p ≤ X) :
    (vertexOfAllowedPrime hS hp hpS hpX : ℕ) = p := rfl

/-- The residual degree at the root is exactly the allowed-prime count at the
cutoff. -/
theorem smallPrimeGraph_degree_primeCoverRoot
    {S : Finset ℕ} {X Y : ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    (smallPrimeGraph S X Y).degree (primeCoverRoot hS (hY.trans hYX)) =
      allowedPrimeCount S Y := by
  classical
  let root : Vertex S X := primeCoverRoot hS (hY.trans hYX)
  let toVertex : (Nat.primesLE Y).filter (fun p ↦ p ∉ S) → Vertex S X :=
    fun p ↦ vertexOfAllowedPrime hS
      (Nat.mem_primesLE.mp (Finset.mem_filter.mp p.2).1).2
      (Finset.mem_filter.mp p.2).2
      ((Nat.mem_primesLE.mp (Finset.mem_filter.mp p.2).1).1.trans hYX)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [allowedPrimeCount]
  symm
  apply Finset.card_bij (fun p hp ↦ toVertex ⟨p, hp⟩)
  · intro p hp
    rw [SimpleGraph.mem_neighborFinset]
    rw [smallPrimeGraph_adj_iff_smallPrimeAdj]
    have hpdata := Finset.mem_filter.mp hp
    exact ⟨p, (Nat.mem_primesLE.mp hpdata.1).2, hpdata.2,
      (Nat.mem_primesLE.mp hpdata.1).1, Or.inl (by simp [toVertex])⟩
  · intro p hp q hq heq
    have hcoe := congrArg (fun v : Vertex S X ↦ (v : ℕ)) heq
    simpa [toVertex, root] using hcoe
  · intro v hv
    have hadj : (smallPrimeGraph S X Y).Adj root v := by simpa using hv
    obtain ⟨p, hp, hpS, hpY, hpEdge⟩ :=
      smallPrimeGraph_adj_iff_smallPrimeAdj.mp hadj
    have hmul : (root : ℕ) * p = (v : ℕ) := by
      rcases hpEdge with h | h
      · exact h
      · have hvp : (v : ℕ) < (v : ℕ) * p := by
          simpa using (Nat.mul_lt_mul_left (Vertex.coe_pos v)).mpr hp.one_lt
        have hone : 1 < (v : ℕ) * p := lt_of_le_of_lt (Vertex.coe_pos v) hvp
        rw [h, primeCoverRoot_coe] at hone
        exact (Nat.lt_irrefl 1 hone).elim
    have hpMem : p ∈ (Nat.primesLE Y).filter (fun p ↦ p ∉ S) := by
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpY, hp⟩, hpS⟩
    refine ⟨p, hpMem, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    simpa [toVertex, root] using hmul

/-- Finite induced-root-star lower bound for the residual graph. -/
theorem sqrt_allowedPrimeCount_le_smallPrimeGraph_norm
    {S : Finset ℕ} {X Y : ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    Real.sqrt (allowedPrimeCount S Y : ℝ) ≤
      ‖(smallPrimeGraph S X Y).adjMatrix ℝ‖ := by
  rw [← smallPrimeGraph_degree_primeCoverRoot hS hY hYX]
  exact sqrt_degree_le_adjMatrix_norm
    (smallPrimeGraph S X Y) (primeCoverRoot hS (hY.trans hYX))

end

end PrimeStar
