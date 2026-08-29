import PrimeStar.StarSpectrum
import Mathlib.NumberTheory.Chebyshev

/-!
# Allowed-prime counts and star degrees

This file begins the quantitative layer of the prime-star formalization.  It
defines the finite counting functions used by the graph, proves their exact
relation to `Nat.primeCounting`, and records the Chebyshev upper bounds that
are available in the pinned mathlib release.

The prime number theorem and prime-Mertens asymptotics are deliberately not
assumed here.
-/

namespace PrimeStar

open Filter
open scoped Nat.Prime

noncomputable section

/-- The number of primes at most `N` that do not belong to the deletion set
`S`.  Only membership in `S` matters for this counting function. -/
def allowedPrimeCount (S : Finset ℕ) (N : ℕ) : ℕ :=
  ((Nat.primesLE N).filter fun p ↦ p ∉ S).card

@[simp]
theorem allowedPrimeCount_empty (N : ℕ) : allowedPrimeCount ∅ N = Nat.primeCounting N := by
  simp [allowedPrimeCount]

theorem allowedPrimeCount_le_primeCounting (S : Finset ℕ) (N : ℕ) :
    allowedPrimeCount S N ≤ Nat.primeCounting N := by
  simpa [allowedPrimeCount] using
    Finset.card_filter_le (Nat.primesLE N) (fun p ↦ p ∉ S)

/-- Deleting a finite set removes exactly those members of `S` that are
prime and at most `N`. -/
theorem allowedPrimeCount_add_deleted (S : Finset ℕ) (N : ℕ) :
    allowedPrimeCount S N + ((Nat.primesLE N).filter fun p ↦ p ∈ S).card =
      Nat.primeCounting N := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  simpa [allowedPrimeCount] using
    (Finset.card_filter_add_card_filter_not
      (s := Nat.primesLE N) (p := fun p ↦ p ∉ S))

theorem primeCounting_sub_allowedPrimeCount_le_card (S : Finset ℕ) (N : ℕ) :
    Nat.primeCounting N - allowedPrimeCount S N ≤ S.card := by
  rw [← allowedPrimeCount_add_deleted S N]
  simp only [Nat.add_sub_cancel_left]
  exact Finset.card_le_card (by
    intro p hp
    exact (Finset.mem_filter.mp hp).2)

/-- The explicit Chebyshev estimate inherited from mathlib, with finite prime
deletions allowed. -/
theorem allowedPrimeCount_le_log4_mul_div {S : Finset ℕ} {x : ℝ} (hx : 1 < x) :
    (allowedPrimeCount S ⌊x⌋₊ : ℝ) ≤
      Real.log 4 * x / Real.log √x + √x := by
  calc
    (allowedPrimeCount S ⌊x⌋₊ : ℝ) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
      exact_mod_cast allowedPrimeCount_le_primeCounting S ⌊x⌋₊
    _ ≤ Real.log 4 * x / Real.log √x + √x := Chebyshev.pi_le_log4_mul_div hx

/-- An eventual `x / log x` upper bound for the allowed-prime count. -/
theorem eventually_allowedPrimeCount_le {S : Finset ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (allowedPrimeCount S ⌊x⌋₊ : ℝ) ≤
        (Real.log 4 + ε) * x / Real.log x := by
  filter_upwards [Chebyshev.eventually_primeCounting_le hε] with x hx
  exact (by
    calc
      (allowedPrimeCount S ⌊x⌋₊ : ℝ) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
        exact_mod_cast allowedPrimeCount_le_primeCounting S ⌊x⌋₊
      _ ≤ (Real.log 4 + ε) * x / Real.log x := hx)

/-- Allowed primes in the half-open interval `(Y,Z]`. -/
def allowedPrimeInterval (S : Finset ℕ) (Y Z : ℕ) : Finset ℕ :=
  (Nat.primesLE Z).filter fun p ↦ p ∉ S ∧ Y < p

theorem card_allowedPrimeInterval (S : Finset ℕ) {Y Z : ℕ} (hYZ : Y ≤ Z) :
    (allowedPrimeInterval S Y Z).card =
      allowedPrimeCount S Z - allowedPrimeCount S Y := by
  classical
  let A := (Nat.primesLE Z).filter fun p ↦ p ∉ S
  let B := (Nat.primesLE Y).filter fun p ↦ p ∉ S
  have hBA : B ⊆ A := by
    intro p hp
    simp only [B, A, Finset.mem_filter, Nat.mem_primesLE] at hp ⊢
    exact ⟨⟨hp.1.1.trans hYZ, hp.1.2⟩, hp.2⟩
  have hdiff : A \ B = allowedPrimeInterval S Y Z := by
    ext p
    simp only [A, B, allowedPrimeInterval, Finset.mem_sdiff, Finset.mem_filter,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hpZ, hpprime⟩, hpS⟩, hpnotB⟩
      refine ⟨⟨hpZ, hpprime⟩, hpS, ?_⟩
      by_contra hpnot
      exact hpnotB ⟨⟨Nat.le_of_not_gt hpnot, hpprime⟩, hpS⟩
    · rintro ⟨⟨hpZ, hpprime⟩, hpS, hpY⟩
      exact ⟨⟨⟨hpZ, hpprime⟩, hpS⟩, fun hpB ↦ (not_lt_of_ge hpB.1.1) hpY⟩
  rw [← hdiff, Finset.card_sdiff_of_subset hBA]
  rfl

/-- The large-prime labels that can occur above a centre `c`. -/
def largePrimeLabels (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) : Finset ℕ :=
  allowedPrimeInterval S Y (X / (c : ℕ))

/-- When the deletion set consists of primes, multiplication by an allowed
prime label preserves the allowed-vertex condition. -/
def vertexMulPrimeOfMemLargePrimeLabels
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ q ∈ S, q.Prime)
    (c : Vertex S X) (p : ℕ) (hp : p ∈ largePrimeLabels S X Y c) :
    Vertex S X := by
  have hpdata := Finset.mem_filter.mp hp
  have hpLE : p ≤ X / (c : ℕ) := (Nat.mem_primesLE.mp hpdata.1).1
  have hpprime : p.Prime := (Nat.mem_primesLE.mp hpdata.1).2
  have hpS : p ∉ S := hpdata.2.1
  have hcpX : (c : ℕ) * p ≤ X := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (Vertex.coe_pos c)).mp hpLE
  refine ⟨⟨(c : ℕ) * p, Nat.lt_succ_iff.mpr hcpX⟩,
    Nat.mul_pos (Vertex.coe_pos c) hpprime.pos, ?_⟩
  intro q hqS
  have hqprime : q.Prime := hS q hqS
  apply hqprime.not_dvd_mul (Vertex.not_dvd_of_mem c hqS)
  intro hqp
  have hqpEq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hpprime).mp hqp
  exact hpS (by simpa [hqpEq] using hqS)

/-- Exact finite degree identity: the leaves of a lower centre are in
bijection with the allowed primes in `(Y, X / c]`. -/
theorem largePrimeStarDegree_eq_card_largePrimeLabels
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ q ∈ S, q.Prime)
    (c : Vertex S X) (hc : (c : ℕ) ≤ Y) :
    largePrimeStarDegree S X Y c = (largePrimeLabels S X Y c).card := by
  classical
  unfold largePrimeStarDegree
  symm
  apply Finset.card_bij
      (fun p hp ↦ vertexMulPrimeOfMemLargePrimeLabels hS c p hp)
  · intro p hp
    rw [mem_largePrimeLeaves_iff_child hc]
    have hpdata := Finset.mem_filter.mp hp
    have hpprime : p.Prime := (Nat.mem_primesLE.mp hpdata.1).2
    exact ⟨p, hpprime, hpdata.2.1, hpdata.2.2, rfl⟩
  · intro p hp q hq hpq
    have hpEq : (c : ℕ) * p = (c : ℕ) * q := by
      exact congrArg (fun v : Vertex S X ↦ (v : ℕ)) hpq
    exact Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos c) hpEq
  · intro v hv
    have hchild : IsLargePrimeChild S Y c v :=
      (mem_largePrimeLeaves_iff_child hc).mp hv
    obtain ⟨p, hpprime, hpS, hpY, hcpv⟩ := hchild
    have hpLE : p ≤ X / (c : ℕ) := by
      apply (Nat.le_div_iff_mul_le (Vertex.coe_pos c)).2
      calc
        p * (c : ℕ) = (c : ℕ) * p := Nat.mul_comm _ _
        _ = (v : ℕ) := hcpv
        _ ≤ X := Vertex.coe_le v
    have hpLabels : p ∈ largePrimeLabels S X Y c := by
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨hpLE, hpprime⟩, hpS, hpY⟩
    refine ⟨p, hpLabels, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    exact hcpv

/-- The manuscript's exact star-degree formula in counting-function form. -/
theorem largePrimeStarDegree_eq_allowedPrimeCount_sub
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ q ∈ S, q.Prime)
    (c : Vertex S X) (hc : (c : ℕ) ≤ Y)
    (hYXc : Y ≤ X / (c : ℕ)) :
    largePrimeStarDegree S X Y c =
      allowedPrimeCount S (X / (c : ℕ)) - allowedPrimeCount S Y := by
  rw [largePrimeStarDegree_eq_card_largePrimeLabels hS c hc]
  exact card_allowedPrimeInterval S hYXc

end

end PrimeStar
