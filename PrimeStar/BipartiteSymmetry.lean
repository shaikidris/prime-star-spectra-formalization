import PrimeStar.AdjacencyEvolution
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Bipartite symmetry of prime-cover adjacency

Every prime-cover edge changes the total number of prime factors by one.
The resulting coordinate sign is an isometric involution which anticommutes
with adjacency, pairs `lambda` with `-lambda`, and exchanges the positive and
negative normalized modes of every large-prime star.
-/

namespace PrimeStar

open scoped ArithmeticFunction.Omega

noncomputable section

def primeCoverParitySign {S : Finset ℕ} {X : ℕ} (n : Vertex S X) : ℝ :=
  (-1 : ℝ) ^ ArithmeticFunction.cardFactors (n : ℕ)

@[simp] theorem primeCoverParitySign_sq
    {S : Finset ℕ} {X : ℕ} (n : Vertex S X) :
    primeCoverParitySign n ^ 2 = 1 := by
  rw [sq_eq_one_iff]
  let k := ArithmeticFunction.cardFactors (n : ℕ)
  change (-1 : ℝ) ^ k = 1 ∨ (-1 : ℝ) ^ k = -1
  induction k with
  | zero => simp
  | succ k ih =>
      rcases ih with h | h
      · right
        simp [pow_succ, h]
      · left
        simp [pow_succ, h]

theorem primeCoverParitySign_eq_neg_of_adj
    {S : Finset ℕ} {X : ℕ} {m n : Vertex S X}
    (h : (primeCoverGraph S X).Adj m n) :
    primeCoverParitySign n = -primeCoverParitySign m := by
  rcases h with ⟨p, hp, _hpS, hmul | hmul⟩
  · have hm0 : (m : ℕ) ≠ 0 := Nat.ne_of_gt (Vertex.coe_pos m)
    have hp0 : p ≠ 0 := hp.ne_zero
    have hOmega : ArithmeticFunction.cardFactors (n : ℕ) =
        ArithmeticFunction.cardFactors (m : ℕ) + 1 := by
      rw [← hmul, ArithmeticFunction.cardFactors_mul hm0 hp0,
        ArithmeticFunction.cardFactors_apply_prime hp]
    simp [primeCoverParitySign, hOmega, pow_succ]
  · have hn0 : (n : ℕ) ≠ 0 := Nat.ne_of_gt (Vertex.coe_pos n)
    have hp0 : p ≠ 0 := hp.ne_zero
    have hOmega : ArithmeticFunction.cardFactors (m : ℕ) =
        ArithmeticFunction.cardFactors (n : ℕ) + 1 := by
      rw [← hmul, ArithmeticFunction.cardFactors_mul hn0 hp0,
        ArithmeticFunction.cardFactors_apply_prime hp]
    have hsign : primeCoverParitySign m = -primeCoverParitySign n := by
      simp [primeCoverParitySign, hOmega, pow_succ]
    linarith

def primeCoverSignFlip {S : Finset ℕ} {X : ℕ}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    EuclideanSpace ℝ (Vertex S X) :=
  WithLp.toLp 2 (fun n ↦ primeCoverParitySign n * x n)

@[simp] theorem primeCoverSignFlip_apply
    {S : Finset ℕ} {X : ℕ}
    (x : EuclideanSpace ℝ (Vertex S X)) (n : Vertex S X) :
    primeCoverSignFlip x n = primeCoverParitySign n * x n := rfl

theorem norm_primeCoverSignFlip
    {S : Finset ℕ} {X : ℕ}
    (x : EuclideanSpace ℝ (Vertex S X)) :
    ‖primeCoverSignFlip x‖ = ‖x‖ := by
  have hsquares : ‖primeCoverSignFlip x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro n _hn
    simp [primeCoverSignFlip, mul_pow, primeCoverParitySign_sq]
  nlinarith [norm_nonneg (primeCoverSignFlip x), norm_nonneg x]

theorem primeCoverSignFlip_sub
    {S : Finset ℕ} {X : ℕ}
    (x y : EuclideanSpace ℝ (Vertex S X)) :
    primeCoverSignFlip (x - y) =
      primeCoverSignFlip x - primeCoverSignFlip y := by
  apply PiLp.ext
  intro n
  simp [primeCoverSignFlip]
  ring

theorem primeCoverSignFlip_smul
    {S : Finset ℕ} {X : ℕ} (r : ℝ)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    primeCoverSignFlip (r • x) = r • primeCoverSignFlip x := by
  apply PiLp.ext
  intro n
  simp [primeCoverSignFlip]
  ring

local instance bipartiteSymmetryPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

local instance bipartiteSymmetryLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

theorem primeCoverAdjacency_signFlip
    (S : Finset ℕ) (X : ℕ)
    (x : EuclideanSpace ℝ (Vertex S X)) :
    Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
        (primeCoverSignFlip x) =
      -primeCoverSignFlip
        (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x) := by
  apply PiLp.ext
  intro n
  change (Matrix.mulVec ((primeCoverGraph S X).adjMatrix ℝ)
      (fun m ↦ primeCoverParitySign m * x m)) n = _
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  change (∑ m ∈ (primeCoverGraph S X).neighborFinset n,
      primeCoverParitySign m * x m) =
    -(primeCoverParitySign n *
      (Matrix.mulVec ((primeCoverGraph S X).adjMatrix ℝ) (fun m ↦ x m) n))
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hadj : (primeCoverGraph S X).Adj n m :=
    ((primeCoverGraph S X).mem_neighborFinset n m).mp hm
  rw [primeCoverParitySign_eq_neg_of_adj hadj]
  ring

theorem primeCoverSignFlip_eigenvector
    {S : Finset ℕ} {X : ℕ}
    (x : EuclideanSpace ℝ (Vertex S X)) (lam : ℝ)
    (hx : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x =
      lam • x) :
    Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)
        (primeCoverSignFlip x) =
      (-lam) • primeCoverSignFlip x := by
  rw [primeCoverAdjacency_signFlip, hx]
  apply PiLp.ext
  intro n
  simp [primeCoverSignFlip]
  ring

theorem primeCoverSignFlip_largePrimeEuclideanStarVector_pos
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} :
    primeCoverSignFlip (largePrimeEuclideanStarVector S X Y c 1) =
      primeCoverParitySign c •
        largePrimeEuclideanStarVector S X Y c (-1) := by
  apply PiLp.ext
  intro v
  by_cases hvc : v = c
  · subst v
    simp [primeCoverSignFlip, largePrimeEuclideanStarVector]
  by_cases hvleaf : v ∈ largePrimeLeaves S X Y c
  · have hadjLarge : (largePrimeGraph S X Y).Adj c v :=
      ((largePrimeGraph S X Y).mem_neighborFinset c v).mp hvleaf
    have hadj : (primeCoverGraph S X).Adj c v :=
      largePrimeGraph_le_primeCoverGraph S X Y hadjLarge
    have hsign := primeCoverParitySign_eq_neg_of_adj hadj
    simp [primeCoverSignFlip, largePrimeEuclideanStarVector,
      largePrimeSignedStarVector_leaf hvleaf, hsign]
  · have hvnot : v ∉ largePrimeStarSupport S X Y c := by
      simp [largePrimeStarSupport, hvc, hvleaf]
    simp [primeCoverSignFlip, largePrimeEuclideanStarVector,
      largePrimeSignedStarVector_eq_zero_of_not_mem hvnot]

theorem norm_largePrimeEuclideanStarVector_pos_eq_neg
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} :
    ‖largePrimeEuclideanStarVector S X Y c 1‖ =
      ‖largePrimeEuclideanStarVector S X Y c (-1)‖ := by
  have hp := norm_sq_largePrimeEuclideanStarVector
    (S := S) (X := X) (Y := Y) (c := c) (by norm_num : (1 : ℝ) ^ 2 = 1)
  have hm := norm_sq_largePrimeEuclideanStarVector
    (S := S) (X := X) (Y := Y) (c := c) (by norm_num : (-1 : ℝ) ^ 2 = 1)
  nlinarith [norm_nonneg (largePrimeEuclideanStarVector S X Y c 1),
    norm_nonneg (largePrimeEuclideanStarVector S X Y c (-1))]

theorem primeCoverSignFlip_largePrimeNormalizedStarMode_pos
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} :
    primeCoverSignFlip (largePrimeNormalizedStarMode S X Y c 1) =
      primeCoverParitySign c •
        largePrimeNormalizedStarMode S X Y c (-1) := by
  rw [largePrimeNormalizedStarMode, largePrimeNormalizedStarMode,
    NormedSpace.normalize, NormedSpace.normalize,
    primeCoverSignFlip_smul,
    primeCoverSignFlip_largePrimeEuclideanStarVector_pos,
    norm_largePrimeEuclideanStarVector_pos_eq_neg]
  module

end

end PrimeStar
