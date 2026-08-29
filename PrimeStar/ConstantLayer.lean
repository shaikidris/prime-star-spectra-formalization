import PrimeStar.TunedPrimeSumBounds
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Constant-layer arithmetic

This file formalizes the unconditional arithmetic surrounding the constant in
Corollary 8.9 of the manuscript. It proves exact finite-deletion identities,
transfers an explicitly supplied prime-Mertens limit through finite deletion,
and proves absolute convergence of the nonlinear local prime correction.

The base prime-Mertens theorem is intentionally represented here by the named
proposition `PrimeMertensAsymptotic`, so this arithmetic layer remains
independent of the external analytic dependency. `PrimeStar.AnalyticInputs`
supplies that proposition at the Meissel--Mertens constant and instantiates the
finite-deletion transfer. No project axiom or unconditional constant-order
spectral claim is introduced.
-/

namespace PrimeStar

open Filter Topology
open scoped BigOperators

noncomputable section

/-- The reciprocal sum over all primes at most `N`. -/
def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹

/-- The reciprocal sum over primes at most `N` not deleted by `S`. -/
def allowedPrimeReciprocalSum (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S), (p : ℝ)⁻¹

/-- The reciprocal mass of deleted primes at most `N`. -/
def deletedPrimeReciprocalSum (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∈ S), (p : ℝ)⁻¹

/-- The total reciprocal mass of the prime members of a finite deletion set. -/
def deletedPrimeReciprocalMass (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S.filter Nat.Prime, (p : ℝ)⁻¹

@[simp]
theorem allowedPrimeReciprocalSum_empty (N : ℕ) :
    allowedPrimeReciprocalSum ∅ N = primeReciprocalSum N := by
  simp [allowedPrimeReciprocalSum, primeReciprocalSum]

theorem allowedPrimeReciprocalSum_add_deleted
    (S : Finset ℕ) (N : ℕ) :
    allowedPrimeReciprocalSum S N + deletedPrimeReciprocalSum S N =
      primeReciprocalSum N := by
  rw [allowedPrimeReciprocalSum, deletedPrimeReciprocalSum, primeReciprocalSum]
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not
      (s := Nat.primesLE N) (p := fun p ↦ p ∉ S) (f := fun p ↦ (p : ℝ)⁻¹))

theorem deletedPrimeReciprocalSum_eq_mass_of_le
    (S : Finset ℕ) (N : ℕ) (hN : ∀ p ∈ S, p ≤ N) :
    deletedPrimeReciprocalSum S N = deletedPrimeReciprocalMass S := by
  rw [deletedPrimeReciprocalSum, deletedPrimeReciprocalMass]
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_hpN, hpPrime⟩, hpS⟩
    exact ⟨hpS, hpPrime⟩
  · rintro ⟨hpS, hpPrime⟩
    exact ⟨⟨hN p hpS, hpPrime⟩, hpS⟩

theorem eventually_deletedPrimeReciprocalSum_eq_mass (S : Finset ℕ) :
    ∀ᶠ N : ℕ in atTop,
      deletedPrimeReciprocalSum S N = deletedPrimeReciprocalMass S := by
  filter_upwards [eventually_ge_atTop (∑ p ∈ S, p)] with N hN
  apply deletedPrimeReciprocalSum_eq_mass_of_le
  intro p hp
  exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hp).trans hN

/-- The exact asymptotic socket needed from the prime reciprocal theorem. -/
def PrimeMertensAsymptotic (B : ℝ) : Prop :=
  Tendsto
    (fun N : ℕ ↦ primeReciprocalSum N - Real.log (Real.log (N : ℝ)))
    atTop (𝓝 B)

/-- Finite Euler deletion transfers the prime-Mertens asymptotic with exactly
the reciprocal mass of the deleted primes removed. -/
theorem PrimeMertensAsymptotic.allowed
    {B : ℝ} (hB : PrimeMertensAsymptotic B) (S : Finset ℕ) :
    Tendsto
      (fun N : ℕ ↦
        allowedPrimeReciprocalSum S N - Real.log (Real.log (N : ℝ)))
      atTop (𝓝 (B - deletedPrimeReciprocalMass S)) := by
  apply (hB.sub_const (deletedPrimeReciprocalMass S)).congr'
  filter_upwards [eventually_deletedPrimeReciprocalSum_eq_mass S] with N hdeleted
  have hsplit := allowedPrimeReciprocalSum_add_deleted S N
  calc
    primeReciprocalSum N - Real.log (Real.log (N : ℝ)) -
        deletedPrimeReciprocalMass S =
        (allowedPrimeReciprocalSum S N + deletedPrimeReciprocalSum S N) -
          Real.log (Real.log (N : ℝ)) - deletedPrimeReciprocalMass S := by rw [hsplit]
    _ = allowedPrimeReciprocalSum S N - Real.log (Real.log (N : ℝ)) := by
      rw [hdeleted]
      ring

/-- A finite deletion changes any real comparison target by at most the
number of deleted primes. -/
theorem abs_allowedPrimeCount_sub_le
    (S : Finset ℕ) (N : ℕ) (target : ℝ) :
    |(allowedPrimeCount S N : ℝ) - target| ≤
      |(Nat.primeCounting N : ℝ) - target| + S.card := by
  have hle := allowedPrimeCount_le_primeCounting S N
  have hdiff :
      ((Nat.primeCounting N : ℝ) - (allowedPrimeCount S N : ℝ)) =
        ((Nat.primeCounting N - allowedPrimeCount S N : ℕ) : ℝ) := by
    exact (Nat.cast_sub hle).symm
  have hcard :
      ((Nat.primeCounting N : ℝ) - (allowedPrimeCount S N : ℝ)) ≤ S.card := by
    rw [hdiff]
    exact_mod_cast primeCounting_sub_allowedPrimeCount_le_card S N
  have hnonneg :
      0 ≤ (Nat.primeCounting N : ℝ) - (allowedPrimeCount S N : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hle)
  calc
    |(allowedPrimeCount S N : ℝ) - target| =
        |((Nat.primeCounting N : ℝ) - target) -
          ((Nat.primeCounting N : ℝ) - (allowedPrimeCount S N : ℝ))| := by
            congr 1
            ring
    _ ≤ |(Nat.primeCounting N : ℝ) - target| +
        |(Nat.primeCounting N : ℝ) - (allowedPrimeCount S N : ℝ)| := abs_sub _ _
    _ ≤ |(Nat.primeCounting N : ℝ) - target| + S.card := by
      rw [abs_of_nonneg hnonneg]
      simpa [add_comm] using add_le_add_left hcard |(Nat.primeCounting N : ℝ) - target|

/-- Pointwise quantitative PNT estimates transfer through a finite deletion;
the only price is the finite cardinality absorbed by the comparison scale. -/
theorem abs_allowedPrimeCount_sub_le_scale
    (S : Finset ℕ) (N : ℕ) (target scale C : ℝ)
    (hscale : 1 ≤ scale)
    (hbase : |(Nat.primeCounting N : ℝ) - target| ≤ C * scale) :
    |(allowedPrimeCount S N : ℝ) - target| ≤
      (C + S.card) * scale := by
  calc
    |(allowedPrimeCount S N : ℝ) - target| ≤
        |(Nat.primeCounting N : ℝ) - target| + S.card :=
      abs_allowedPrimeCount_sub_le S N target
    _ ≤ C * scale + S.card := by
      simpa [add_comm] using add_le_add_right hbase (S.card : ℝ)
    _ ≤ (C + S.card) * scale := by
      have hcard0 : (0 : ℝ) ≤ S.card := by positivity
      nlinarith

/-- The absolutely convergent local correction left after subtracting `1/p`
from `1/(p-1)`, extended by zero off the allowed primes. -/
def nonlinearPrimeTerm (S : Finset ℕ) (n : ℕ) : ℝ :=
  if n.Prime ∧ n ∉ S then 1 / ((n : ℝ) * ((n : ℝ) - 1)) else 0

theorem nonlinearPrimeTerm_nonneg (S : Finset ℕ) (n : ℕ) :
    0 ≤ nonlinearPrimeTerm S n := by
  rw [nonlinearPrimeTerm]
  split_ifs with h
  · have hn : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h.1.one_lt
    positivity
  · exact le_rfl

theorem nonlinearPrimeTerm_le_two_div_sq (S : Finset ℕ) (n : ℕ) :
    nonlinearPrimeTerm S n ≤ 2 / (n : ℝ) ^ 2 := by
  rw [nonlinearPrimeTerm]
  split_ifs with h
  · have hn : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.1.two_le
    have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn
    have hnm1 : 0 < (n : ℝ) - 1 := by linarith
    rw [div_le_div_iff₀ (mul_pos hn0 hnm1) (sq_pos_of_pos hn0)]
    nlinarith
  · positivity

theorem summable_nonlinearPrimeTerm (S : Finset ℕ) :
    Summable (nonlinearPrimeTerm S) := by
  have hs : Summable (fun n : ℕ ↦ 2 / (n : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 2
  exact hs.of_nonneg_of_le (nonlinearPrimeTerm_nonneg S)
    (nonlinearPrimeTerm_le_two_div_sq S)

/-- The convergent nonlinear prime correction after deleting `S`. -/
def nonlinearPrimeConstant (S : Finset ℕ) : ℝ :=
  ∑' n : ℕ, nonlinearPrimeTerm S n

/-- The corresponding finite nonlinear correction. -/
def finiteNonlinearPrimeCorrection (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S),
    1 / ((p : ℝ) * ((p : ℝ) - 1))

theorem finiteNonlinearPrimeCorrection_eq_sum_range
    (S : Finset ℕ) (N : ℕ) :
    finiteNonlinearPrimeCorrection S N =
      ∑ n ∈ Finset.range (N + 1), nonlinearPrimeTerm S n := by
  rw [finiteNonlinearPrimeCorrection, Nat.primesLE_eq_filter_range,
    Finset.filter_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hp : n.Prime <;> by_cases hS : n ∈ S <;>
    simp [nonlinearPrimeTerm, hp, hS, mul_comm]

theorem tendsto_finiteNonlinearPrimeCorrection (S : Finset ℕ) :
    Tendsto (finiteNonlinearPrimeCorrection S) atTop
      (𝓝 (nonlinearPrimeConstant S)) := by
  have hsum := (summable_nonlinearPrimeTerm S).hasSum.tendsto_sum_nat
  have heq : finiteNonlinearPrimeCorrection S =
      fun N ↦ ∑ n ∈ Finset.range (N + 1), nonlinearPrimeTerm S n := by
    funext N
    exact finiteNonlinearPrimeCorrection_eq_sum_range S N
  rw [heq]
  have h := hsum.comp (tendsto_add_atTop_nat 1)
  change Tendsto
    (fun N ↦ ∑ n ∈ Finset.range (N + 1), nonlinearPrimeTerm S n)
    atTop (𝓝 (∑' n : ℕ, nonlinearPrimeTerm S n)) at h
  simpa only [nonlinearPrimeConstant] using h

/-- The limiting up-star local correction splits into its divergent reciprocal
part and the absolutely convergent nonlinear part. -/
theorem upStarCorrection_one_div
    (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    upStarCorrection (1 / x) =
      4 / x + 4 / (x * (x - 1)) := by
  rw [upStarCorrection]
  field_simp [hx0, sub_ne_zero.mpr hx1]
  ring

/-- The limiting down-star local correction is the centre term appearing in
the manuscript. -/
theorem downStarCorrection_eq_centerTerm (x : ℝ) (hx1 : x ≠ 1) :
    downStarCorrection x = (x - 5) / (x - 1) := by
  rw [downStarCorrection]
  field_simp [sub_ne_zero.mpr hx1]
  ring

/-- The finite sum of limiting up-star corrections. -/
def finiteLimitingUpStarCorrection (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S),
    upStarCorrection (1 / (p : ℝ))

/-- Exact finite decomposition of the limiting up-star correction into the
prime-reciprocal term and the convergent nonlinear term. -/
theorem finiteLimitingUpStarCorrection_eq
    (S : Finset ℕ) (N : ℕ) :
    finiteLimitingUpStarCorrection S N =
      4 * allowedPrimeReciprocalSum S N +
        4 * finiteNonlinearPrimeCorrection S N := by
  rw [finiteLimitingUpStarCorrection, allowedPrimeReciprocalSum,
    finiteNonlinearPrimeCorrection]
  calc
    (∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S),
        upStarCorrection (1 / (p : ℝ))) =
        ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S),
          (4 / (p : ℝ) + 4 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime : p.Prime :=
        (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      exact upStarCorrection_one_div (p : ℝ)
        (by exact_mod_cast hpPrime.ne_zero)
        (by exact_mod_cast hpPrime.ne_one)
    _ = 4 * (∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S), (p : ℝ)⁻¹) +
        4 * (∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S),
          1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      rw [Finset.sum_add_distrib]
      simp only [div_eq_mul_inv, Finset.mul_sum, one_mul]

/-- The constant `kappa_S` assembled from a prime-Mertens constant `B` and
the convergent nonlinear local correction. -/
def primeStarKappa (B : ℝ) (S : Finset ℕ) : ℝ :=
  B - deletedPrimeReciprocalMass S + nonlinearPrimeConstant S

@[simp]
theorem primeStarKappa_empty (B : ℝ) :
    primeStarKappa B ∅ = B + nonlinearPrimeConstant ∅ := by
  simp [primeStarKappa, deletedPrimeReciprocalMass]

/-- The finite centre-dependent correction from the distinct prime divisors
of `a`. -/
def centerPrimeCorrection (a : ℕ) : ℝ :=
  ∑ q ∈ a.primeFactors, ((q : ℝ) - 5) / ((q : ℝ) - 1)

@[simp]
theorem centerPrimeCorrection_one : centerPrimeCorrection 1 = 0 := by
  simp [centerPrimeCorrection]

end

end PrimeStar
