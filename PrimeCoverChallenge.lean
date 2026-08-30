import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Instances.Nat
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Uniform finite-prime-sum spectrum of finite prime-cover graphs

For a finite set `S` of deleted primes and a cutoff `X`, let `G(S,X)` be the
graph on the positive integers at most `X` that avoid `S`, with an edge between
`m` and `n` exactly when one is the other multiplied by an allowed prime.

The theorem below states the manuscript's finite-prime-sum asymptotic for the
ordered adjacency eigenvalue indexed by an arithmetic centre `a`, uniformly
for `a <= (log X)^(1/2-epsilon)`.
-/

namespace PrimeStar

open Filter Topology
open scoped BigOperators Classical InnerProductSpace

/-- Positive integers at most `X` avoiding every prime in `S`. -/
def Vertex (S : Finset ℕ) (X : ℕ) :=
  {n : Fin (X + 1) // 0 < n.1 ∧ ∀ p ∈ S, ¬p ∣ n.1}
  deriving DecidableEq, Fintype

namespace Vertex

instance (S : Finset ℕ) (X : ℕ) : CoeOut (Vertex S X) ℕ :=
  ⟨fun n ↦ n.1.1⟩

theorem coe_pos {S : Finset ℕ} {X : ℕ} (n : Vertex S X) : 0 < (n : ℕ) :=
  n.2.1

end Vertex

/-- Two allowed vertices differ by multiplication by one allowed prime. -/
def PrimeCoverAdj {S : Finset ℕ} {X : ℕ} (m n : Vertex S X) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∉ S ∧
    (((m : ℕ) * p = (n : ℕ)) ∨ ((n : ℕ) * p = (m : ℕ)))

theorem primeCoverAdj_symm {S : Finset ℕ} {X : ℕ} {m n : Vertex S X} :
    PrimeCoverAdj m n → PrimeCoverAdj n m := by
  rintro ⟨p, hp, hpS, h | h⟩
  · exact ⟨p, hp, hpS, Or.inr h⟩
  · exact ⟨p, hp, hpS, Or.inl h⟩

theorem not_primeCoverAdj_self {S : Finset ℕ} {X : ℕ} (m : Vertex S X) :
    ¬PrimeCoverAdj m m := by
  rintro ⟨p, hp, _hpS, h | h⟩
  all_goals
    have hmul : (m : ℕ) * p = (m : ℕ) * 1 := by simpa using h
    have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos m) hmul
    exact hp.ne_one hp1

/-- The finite prime-cover graph. -/
def primeCoverGraph (S : Finset ℕ) (X : ℕ) : SimpleGraph (Vertex S X) where
  Adj := PrimeCoverAdj
  symm := ⟨fun _ _ h ↦ primeCoverAdj_symm (S := S) (X := X) h⟩
  loopless := ⟨fun m ↦ not_primeCoverAdj_self (S := S) (X := X) m⟩

noncomputable instance palomarPrimeCoverDecidableRel (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

/-- `pi_S(N)`, the number of primes at most `N` not deleted by `S`. -/
def allowedPrimeCount (S : Finset ℕ) (N : ℕ) : ℕ :=
  ((Nat.primesLE N).filter fun p ↦ p ∉ S).card

/-- One-based rank `j(a)` of `a` among the allowed vertices. -/
def arithmeticCenterRank {S : Finset ℕ} {X : ℕ} (a : Vertex S X) : ℕ :=
  (Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (a : ℕ)).card + 1

/-- The logarithmic centre window `0 < a <= (log X)^(1/2-epsilon)`. -/
def InLogarithmicCenterWindow (ε : ℝ) (X a : ℕ) : Prop :=
  0 < a ∧ (a : ℝ) ≤ Real.log (X : ℝ) ^ (1 / 2 - ε)

/-- The finite allowed-prime sum `∑_{p ≤ N, p ∉ S} 1/(p-1)`. -/
noncomputable def palomarAllowedPrimeInvSubOneSum
    (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S), ((p : ℝ) - 1)⁻¹

/-- The centre correction `c(a) = sum_{q|a, q prime} (q-5)/(q-1)`. -/
noncomputable def centerPrimeCorrection (a : ℕ) : ℝ :=
  ∑ q ∈ a.primeFactors, ((q : ℝ) - 5) / ((q : ℝ) - 1)

/-- Zero-based spectral index corresponding to the one-based rank `j(a)`. -/
def palomarArithmeticRankIndex {S : Finset ℕ} {X : ℕ} (a : Vertex S X) :
    Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))) := by
  let T := Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (a : ℕ)
  refine ⟨T.card, ?_⟩
  have hproper : T ⊂ (Finset.univ : Finset (Vertex S X)) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, ?_⟩
    intro hEq
    have ha : a ∈ T := by simp [hEq]
    simp [T] at ha
  simpa using Finset.card_lt_card hproper

/-- Adjacency operator of the finite prime-cover graph. -/
noncomputable def palomarAdjacency (S : Finset ℕ) (X : ℕ) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ] EuclideanSpace ℝ (Vertex S X) :=
  Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)

/-- The adjacency operator is symmetric. -/
theorem palomarAdjacency_isSymmetric (S : Finset ℕ) (X : ℕ) :
    (palomarAdjacency S X).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))

/-- The ordered adjacency eigenvalue at the arithmetic rank `j(a)`. -/
noncomputable def palomarLambdaAtArithmeticRank
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X) : ℝ :=
  (palomarAdjacency_isSymmetric S X).eigenvalues rfl
    (palomarArithmeticRankIndex a)

/-- The root vertex `1` of the undeleted prime-cover graph. -/
def palomarRootVertex (X : ℕ) (hX : 1 ≤ X) : Vertex ∅ X :=
  ⟨⟨1, Nat.lt_succ_iff.mpr hX⟩, by simp⟩

@[simp]
theorem palomarRootVertex_coe (X : ℕ) (hX : 1 ≤ X) :
    (palomarRootVertex X hX : ℕ) = 1 := rfl

/-- The largest ordered adjacency eigenvalue of the undeleted graph.

The positive root vertex has arithmetic rank one, hence zero-based ordered
spectral index zero.
-/
noncomputable def palomarLargestEigenvalue (X : ℕ) (hX : 1 ≤ X) : ℝ :=
  palomarLambdaAtArithmeticRank (palomarRootVertex X hX)

/-- Uniform finite-prime-sum spectrum of finite prime-cover graphs.

For fixed finite `S` and `epsilon > 0`, uniformly over allowed centres
`a <= (log X)^(1/2-epsilon)`, the square of the `j(a)`-th largest adjacency
eigenvalue equals
`pi_S(X/a) + 4 * sum_{p <= X, p notin S} 1/(p-1) + c(a) + o(1)`.
-/
theorem palomar_uniform_finite_prime_sum
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        |(palomarLambdaAtArithmeticRank a) ^ 2
          - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)
          - 4 * palomarAllowedPrimeInvSubOneSum S X
          - centerPrimeCorrection (a : ℕ)| < δ := by
  sorry

/-- Root-centred specialization of `palomar_uniform_finite_prime_sum`.

For the undeleted graph, the square of the largest ordered adjacency
eigenvalue equals `π(X) + 4 * ∑_{p ≤ X} 1/(p-1) + o(1)`.
-/
theorem palomar_top_finite_prime_sum :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ hX : 1 ≤ X,
      |(palomarLargestEigenvalue X hX) ^ 2
        - (Nat.primeCounting X : ℝ)
        - 4 * palomarAllowedPrimeInvSubOneSum ∅ X| < δ := by
  sorry

end PrimeStar
