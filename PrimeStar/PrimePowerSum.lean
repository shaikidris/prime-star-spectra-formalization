import PrimeStar.SmallPrimeRow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Abel summation for outgoing prime powers

This module isolates the only scalar prime sum left after the exact graph-row
decomposition. No prime number theorem is used.
-/

namespace PrimeStar

open Finset MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Local decidability for residual adjacency in the Abel-summation layer. -/
local instance primePowerSumDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

private def primeIndicator (n : ℕ) : ℝ :=
  if n.Prime then 1 else 0

private theorem primeIndicator_zero : primeIndicator 0 = 0 := by
  unfold primeIndicator
  rw [if_neg Nat.not_prime_zero]

private theorem primeIndicator_one : primeIndicator 1 = 0 := by
  unfold primeIndicator
  rw [if_neg Nat.not_prime_one]

private theorem sum_primeIndicator_Icc (m : ℕ) :
    ∑ k ∈ Icc 0 m, primeIndicator k = Nat.primeCounting m := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero,
    Finset.card_eq_sum_ones]
  simp [primeIndicator]

/-- Exact Abel-summation identity for the outgoing prime-power sum. -/
theorem outgoingPrimePowerSum_eq_abel {Y : ℕ} (_hY : 2 ≤ Y) (θ : ℝ) :
    outgoingPrimePowerSum Y θ =
      (Y : ℝ) ^ (-θ) * Nat.primeCounting Y +
        θ * ∫ t in Set.Ioc (2 : ℝ) Y,
          t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊ := by
  let f : ℝ → ℝ := fun t ↦ t ^ (-θ)
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) Y, DifferentiableAt ℝ f t := by
    intro t ht
    exact Real.differentiableAt_rpow_const_of_ne (-θ) (by linarith [ht.1])
  have hint : IntegrableOn (deriv f) (Set.Icc (2 : ℝ) Y) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ?_
    rw [show deriv f = fun t ↦ (-θ) * t ^ (-θ - 1) by
      funext u
      simpa [f] using Real.deriv_rpow_const u (-θ)]
    exact ContinuousAt.continuousWithinAt <|
      continuousAt_const.mul <| Real.continuousAt_rpow_const t (-θ - 1) <|
        Or.inl (by linarith [ht.1])
  have habel := sum_mul_eq_sub_integral_mul₁ primeIndicator
    primeIndicator_zero primeIndicator_one (Y : ℝ) hdiff hint
  rw [Nat.floor_natCast, sum_primeIndicator_Icc] at habel
  have hsum :
      outgoingPrimePowerSum Y θ =
        ∑ k ∈ Icc 0 Y, f k * primeIndicator k := by
    rw [outgoingPrimePowerSum, Nat.primesLE_eq_filter_Icc_zero]
    simp only [Finset.sum_filter, primeIndicator, f]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hp : k.Prime <;> simp [hp]
  rw [hsum, habel]
  have hderiv : ∀ t ∈ Set.Ioc (2 : ℝ) Y,
      deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, primeIndicator k =
        -θ * (t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊) := by
    intro t ht
    rw [sum_primeIndicator_Icc]
    rw [show deriv f t = (-θ) * t ^ (-θ - 1) by
      simpa [f] using Real.deriv_rpow_const t (-θ)]
    ring
  have hint_deriv :
      (∫ t in Set.Ioc (2 : ℝ) Y,
          deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, primeIndicator k) =
        ∫ t in Set.Ioc (2 : ℝ) Y,
          -θ * (t ^ (-θ - 1) * Nat.primeCounting ⌊t⌋₊) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hderiv t ht
  rw [hint_deriv, MeasureTheory.integral_const_mul]
  simp only [f]
  ring

/-- The explicit finite row majorant left after the graph decomposition and
the elementary incoming-divisor split. -/
def elementarySmallPrimeRowBound (Y : ℕ) : ℝ :=
  outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) +
    (Nat.log 2 (Y ^ 2) : ℝ) *
      (√(Y : ℝ)) ^ tunedSchurExponent (Y : ℝ) +
    3 * (Y : ℝ) ^ tunedSchurExponent (Y : ℝ)

theorem elementarySmallPrimeRowBound_nonneg (Y : ℕ) :
    0 ≤ elementarySmallPrimeRowBound Y := by
  unfold elementarySmallPrimeRowBound outgoingPrimePowerSum
  positivity

/-- The incoming divisor contribution is uniformly bounded by the explicit
part of `elementarySmallPrimeRowBound` whenever the ambient graph lies below
the square cutoff. -/
theorem incomingPrimeDivisorPowerSum_le_uniform
    {S : Finset ℕ} {X Y : ℕ} (hXY : X ≤ Y ^ 2)
    (hlogY : 0 < Real.log (Y : ℝ)) (n : Vertex S X) :
    incomingPrimeDivisorPowerSum n Y (tunedSchurExponent (Y : ℝ)) ≤
      (Nat.log 2 (Y ^ 2) : ℝ) *
          (√(Y : ℝ)) ^ tunedSchurExponent (Y : ℝ) +
        3 * (Y : ℝ) ^ tunedSchurExponent (Y : ℝ) := by
  have hnY : (n : ℕ) ≤ Y ^ 2 := (Vertex.coe_le n).trans hXY
  have hθ : 0 ≤ tunedSchurExponent (Y : ℝ) :=
    tunedSchurExponent_nonneg hlogY
  refine (incomingPrimeDivisorPowerSum_le n hθ hnY).trans ?_
  gcongr

/-- Unconditional finite weighted-row bound after the only remaining scalar
outgoing prime sum has been isolated. -/
theorem smallPrimePowerWeight_row_le_elementaryBound
    {S : Finset ℕ} {X Y : ℕ} (hXY : X ≤ Y ^ 2)
    (hlogY : 0 < Real.log (Y : ℝ)) (n : Vertex S X) :
    ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n,
        smallPrimePowerWeight (Y : ℝ) v ≤
      elementarySmallPrimeRowBound Y * smallPrimePowerWeight (Y : ℝ) n := by
  calc
    ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n,
        smallPrimePowerWeight (Y : ℝ) v ≤
      smallPrimePowerWeight (Y : ℝ) n *
        (outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) +
          incomingPrimeDivisorPowerSum n Y
            (tunedSchurExponent (Y : ℝ))) :=
      smallPrimePowerWeight_row_le_primeSums n
    _ ≤ smallPrimePowerWeight (Y : ℝ) n * elementarySmallPrimeRowBound Y := by
      rw [elementarySmallPrimeRowBound]
      apply mul_le_mul_of_nonneg_left
      · have hin := incomingPrimeDivisorPowerSum_le_uniform hXY hlogY n
        linarith
      · exact (smallPrimePowerWeight_pos (Y : ℝ) n).le
    _ = elementarySmallPrimeRowBound Y * smallPrimePowerWeight (Y : ℝ) n :=
      mul_comm _ _

/-- The residual adjacency norm is bounded by the exact outgoing Abel term
plus the fully elementary incoming-divisor majorant. -/
theorem smallPrimeGraph_l2_opNorm_le_elementaryBound
    {S : Finset ℕ} {X Y : ℕ} (hXY : X ≤ Y ^ 2)
    (hlogY : 0 < Real.log (Y : ℝ)) :
    ‖(smallPrimeGraph S X Y).adjMatrix ℝ‖ ≤ elementarySmallPrimeRowBound Y := by
  exact smallPrimeGraph_l2_opNorm_le_of_weightedRow
    (smallPrimePowerWeight (Y : ℝ)) (elementarySmallPrimeRowBound Y)
    (elementarySmallPrimeRowBound_nonneg Y)
    (smallPrimePowerWeight_pos (Y : ℝ))
    (smallPrimePowerWeight_row_le_elementaryBound hXY hlogY)

end

end PrimeStar
