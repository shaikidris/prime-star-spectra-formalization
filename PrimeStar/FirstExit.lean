import PrimeStar.StarPerturbation
import PrimeStar.StarResolvent

/-!
# Arithmetic first exits from a prime star

The residual graph consists exactly of prime-cover edges whose label is at
most the cutoff.  This gives the finite arithmetic classification consumed by
the local resolvent blocks.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

/-- Local decidability for prime-cover adjacency in first-exit arguments. -/
local instance firstExitPrimeCoverDecidableAdj (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- Local decidability for residual adjacency in first-exit arguments. -/
local instance firstExitSmallPrimeDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- A prime-cover step carrying an allowed prime label at most `Y`. -/
def SmallPrimeAdj (S : Finset ℕ) (Y : ℕ) {X : ℕ}
    (m n : Vertex S X) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ≤ Y ∧
    ((m : ℕ) * q = (n : ℕ) ∨ (n : ℕ) * q = (m : ℕ))

theorem smallPrimeAdj_symm {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X} :
    SmallPrimeAdj S Y m n → SmallPrimeAdj S Y n m := by
  rintro ⟨q, hq, hqS, hqY, h | h⟩
  · exact ⟨q, hq, hqS, hqY, Or.inr h⟩
  · exact ⟨q, hq, hqS, hqY, Or.inl h⟩

/-- A prime multiplier on an undirected prime-cover edge is unique. -/
theorem primeCover_multiplier_unique
    {m n p q : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hp : p.Prime) (hq : q.Prime)
    (hpEdge : m * p = n ∨ n * p = m)
    (hqEdge : m * q = n ∨ n * q = m) :
    p = q := by
  rcases hpEdge with hmp | hnp <;> rcases hqEdge with hmq | hnq
  · exact Nat.eq_of_mul_eq_mul_left hm (hmp.trans hmq.symm)
  · have hpq : p * q = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hm
      calc
        m * (p * q) = (m * p) * q := by simp [Nat.mul_assoc]
        _ = n * q := by rw [hmp]
        _ = m := hnq
        _ = m * 1 := by simp
    have hp1 : p = 1 := Nat.eq_one_of_dvd_one ⟨q, hpq.symm⟩
    exact False.elim (hp.ne_one hp1)
  · have hqp : q * p = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hm
      calc
        m * (q * p) = (m * q) * p := by simp [Nat.mul_assoc]
        _ = n * p := by rw [hmq]
        _ = m := hnp
        _ = m * 1 := by simp
    have hq1 : q = 1 := Nat.eq_one_of_dvd_one ⟨p, hqp.symm⟩
    exact False.elim (hq.ne_one hq1)
  · exact Nat.eq_of_mul_eq_mul_left hn (hnp.trans hnq.symm)

/-- The graph-theoretic residual edge is exactly an edge carrying a prime
label at most the cutoff. -/
theorem smallPrimeGraph_adj_iff_smallPrimeAdj
    {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X} :
    (smallPrimeGraph S X Y).Adj m n ↔ SmallPrimeAdj S Y m n := by
  constructor
  · intro h
    obtain ⟨hprime, hnlarge⟩ := smallPrimeGraph_adj.mp h
    obtain ⟨q, hq, hqS, hqEdge⟩ := hprime
    have hqY : q ≤ Y := by
      by_contra hnot
      exact hnlarge ⟨q, hq, hqS, Nat.lt_of_not_ge hnot, hqEdge⟩
    exact ⟨q, hq, hqS, hqY, hqEdge⟩
  · rintro ⟨q, hq, hqS, hqY, hqEdge⟩
    rw [smallPrimeGraph_adj]
    refine ⟨⟨q, hq, hqS, hqEdge⟩, ?_⟩
    rintro ⟨p, hp, hpS, hYp, hpEdge⟩
    have hpq : p = q := primeCover_multiplier_unique
      (Vertex.coe_pos m) (Vertex.coe_pos n) hp hq hpEdge hqEdge
    subst p
    exact (not_lt_of_ge hqY) hYp

/-- Every residual first exit from the closed star at `c` is a small-prime
step from either its centre or one of its large-prime children. -/
theorem smallPrime_firstExit_classification
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hc : (c : ℕ) ≤ Y)
    (hw : w ∈ largePrimeStarSupport S X Y c)
    (hvw : (smallPrimeGraph S X Y).Adj v w) :
    (w = c ∨ IsLargePrimeChild S Y c w) ∧ SmallPrimeAdj S Y v w := by
  have hsmall : SmallPrimeAdj S Y v w :=
    smallPrimeGraph_adj_iff_smallPrimeAdj.mp hvw
  rw [mem_largePrimeStarSupport] at hw
  refine ⟨?_, hsmall⟩
  rcases hw with rfl | hcw
  · exact Or.inl rfl
  · exact Or.inr (isLargePrimeChild_of_largePrimeAdj_of_le hc hcw)

/-- Literal arithmetic forms of the first exits in Proposition 8.1.  If the
source is the centre, the endpoint is obtained by multiplying or dividing by
one small prime.  If the source is a large-prime child `c*p`, the endpoint is
obtained by one additional small-prime multiplication or division. -/
theorem smallPrime_firstExit_arithmeticForms
    {S : Finset ℕ} {X Y : ℕ} {c v w : Vertex S X}
    (hc : (c : ℕ) ≤ Y)
    (hw : w ∈ largePrimeStarSupport S X Y c)
    (hvw : (smallPrimeGraph S X Y).Adj v w) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ≤ Y ∧
      ((w = c ∧ ((v : ℕ) * q = (c : ℕ) ∨ (c : ℕ) * q = (v : ℕ))) ∨
       ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ Y < p ∧ (c : ℕ) * p = (w : ℕ) ∧
         ((v : ℕ) * q = (w : ℕ) ∨ (w : ℕ) * q = (v : ℕ))) := by
  obtain ⟨hsource, hsmall⟩ := smallPrime_firstExit_classification hc hw hvw
  obtain ⟨q, hq, hqS, hqY, hqEdge⟩ := hsmall
  refine ⟨q, hq, hqS, hqY, ?_⟩
  rcases hsource with rfl | hchild
  · exact Or.inl ⟨rfl, hqEdge⟩
  · obtain ⟨p, hp, hpS, hYp, hcp⟩ := hchild
    exact Or.inr ⟨p, hp, hpS, hYp, hcp, hqEdge⟩

/-- The Stage 3 normalized arithmetic mode satisfies the exact Schur equation
as soon as a reduced inverse action for its orthogonal component is supplied. -/
theorem primeCover_schurEquation_at_normalizedStarMode
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {ε μ lam : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hε : ε ^ 2 = 1)
    (hμ : μ = ε * √(largePrimeStarDegree S X Y c : ℝ))
    (R : (EuclideanSpace ℝ (Vertex S X)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Vertex S X)))
    (v : EuclideanSpace ℝ (Vertex S X))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (hα : ⟪largePrimeNormalizedStarMode S X Y c ε, v⟫_ℝ ≠ 0)
    (hinv : orthogonalRemainder (largePrimeNormalizedStarMode S X Y c ε) v =
      ⟪largePrimeNormalizedStarMode S X Y c ε, v⟫_ℝ •
        R (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c ε))) :
    lam - μ =
      ⟪Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c ε),
        R (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c ε))⟫_ℝ := by
  apply schurScalarEquation_of_inverseAction R
    (largePrimeNormalizedStarMode S X Y c ε) v
    (Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
      (largePrimeNormalizedStarMode S X Y c ε)) μ lam hα
  · exact primeCover_scalarEquation_at_normalizedStarMode hcut hc hε hμ v hAv
  · exact hinv

end

end PrimeStar
