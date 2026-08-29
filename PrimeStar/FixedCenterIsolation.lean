import PrimeStar.AnalyticInputs
import PrimeStar.FeshbachDegreeGap

/-!
# Fixed-centre degree isolation

This module turns the quantitative prime-number theorem into the eventual
degree gaps consumed by the finite Feshbach comparison.  The centre and the
finite deleted-prime set are fixed throughout; no growing-centre assertion is
made here.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

/-- Dividing the argument of the logarithm by a fixed positive constant does
not change its asymptotic scale. -/
theorem log_div_const_isEquivalent_log (c : ℝ) (hc : 0 < c) :
    @Asymptotics.IsEquivalent ℝ ℝ
      NormedAddCommGroup.toSeminormedAddCommGroup atTop
      (fun x : ℝ ↦ Real.log (x / c)) Real.log := by
  apply Asymptotics.IsLittleO.isEquivalent
  have hconst : (fun _x : ℝ ↦ -Real.log c) =o[atTop] Real.log :=
    Real.isLittleO_const_log_atTop
  refine hconst.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  change -Real.log c = Real.log (x / c) - Real.log x
  rw [Real.log_div hx.ne' hc.ne']
  ring

/-- The usual PNT main term at a fixed dilated argument. -/
theorem div_const_div_log_isEquivalent (c : ℝ) (hc : 0 < c) :
    @Asymptotics.IsEquivalent ℝ ℝ
      NormedAddCommGroup.toSeminormedAddCommGroup atTop
      (fun x : ℝ ↦ (x / c) / Real.log (x / c))
      (fun x : ℝ ↦ c⁻¹ * (x / Real.log x)) := by
  have hnum :
      @Asymptotics.IsEquivalent ℝ ℝ
        NormedAddCommGroup.toSeminormedAddCommGroup atTop
        (fun x : ℝ ↦ x / c) (fun x : ℝ ↦ c⁻¹ * x) :=
    (show (fun x : ℝ ↦ x / c) =ᶠ[atTop] (fun x : ℝ ↦ c⁻¹ * x) by
      filter_upwards with x
      simp only [div_eq_mul_inv, mul_comm]).isEquivalent
  have h := hnum.div (log_div_const_isEquivalent_log c hc)
  apply h.congr_right
  filter_upwards with x
  simp only [Pi.div_apply, div_eq_mul_inv, mul_assoc]

/-- Prime counting at a fixed real dilation is asymptotic to the corresponding
constant multiple of `x / log x`. -/
theorem primeCounting_floor_div_const_isEquivalent
    (c : ℝ) (hc : 0 < c) :
    @Asymptotics.IsEquivalent ℝ ℝ
      NormedAddCommGroup.toSeminormedAddCommGroup atTop
      (fun x : ℝ ↦ (Nat.primeCounting ⌊x / c⌋₊ : ℝ))
      (fun x : ℝ ↦ c⁻¹ * (x / Real.log x)) := by
  have h := primeCounting_floor_isEquivalent_main_real.comp_tendsto
    (tendsto_id.atTop_div_const hc)
  have hmain :
      @Asymptotics.IsEquivalent ℝ ℝ
        NormedAddCommGroup.toSeminormedAddCommGroup atTop
        (fun x : ℝ ↦ (Nat.primeCounting ⌊x / c⌋₊ : ℝ))
        (fun x : ℝ ↦ (x / c) / Real.log (x / c)) := by
    convert h using 1 <;> ext x <;> rfl
  exact hmain.trans (div_const_div_log_isEquivalent c hc)

/-- Natural-number specialization of prime counting at a fixed denominator. -/
theorem primeCounting_div_const_isEquivalent
    (c : ℕ) (hc : 0 < c) :
    @Asymptotics.IsEquivalent ℕ ℝ
      NormedAddCommGroup.toSeminormedAddCommGroup atTop
      (fun X : ℕ ↦ (Nat.primeCounting (X / c) : ℝ))
      (fun X : ℕ ↦ ((c : ℝ)⁻¹) *
        ((X : ℝ) / Real.log (X : ℝ))) := by
  have h := (primeCounting_floor_div_const_isEquivalent (c : ℝ)
    (by exact_mod_cast hc)).comp_tendsto tendsto_natCast_atTop_atTop
  change @Asymptotics.IsEquivalent ℕ ℝ
    NormedAddCommGroup.toSeminormedAddCommGroup atTop
    (fun X : ℕ ↦ (Nat.primeCounting ⌊(X : ℝ) / (c : ℝ)⌋₊ : ℝ))
    (fun X : ℕ ↦ ((c : ℝ)⁻¹) *
      ((X : ℝ) / Real.log (X : ℝ))) at h
  simpa only [Nat.floor_div_eq_div] using h

/-- The prime count in a fixed multiplicative interval has its expected PNT
main term. -/
theorem primeCounting_fixedDenominator_gap_isEquivalent
    {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    @Asymptotics.IsEquivalent ℕ ℝ
      NormedAddCommGroup.toSeminormedAddCommGroup atTop
      (fun X : ℕ ↦
        (Nat.primeCounting (X / a) : ℝ) -
          (Nat.primeCounting (X / b) : ℝ))
      (fun X : ℕ ↦
        ((a : ℝ)⁻¹ - (b : ℝ)⁻¹) *
          ((X : ℝ) / Real.log (X : ℝ))) := by
  let main : ℕ → ℝ := fun X ↦ (X : ℝ) / Real.log (X : ℝ)
  have hk : (a : ℝ)⁻¹ - (b : ℝ)⁻¹ ≠ 0 := by
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    exact (sub_pos.mpr (inv_strictAnti₀ haR habR)).ne'
  have haerr :
      (fun X : ℕ ↦
        (Nat.primeCounting (X / a) : ℝ) - (a : ℝ)⁻¹ * main X) =o[atTop]
        main := by
    have h := (primeCounting_div_const_isEquivalent a ha).isLittleO
    exact h.of_const_mul_right
  have hberr :
      (fun X : ℕ ↦
        (Nat.primeCounting (X / b) : ℝ) - (b : ℝ)⁻¹ * main X) =o[atTop]
        main := by
    have h := (primeCounting_div_const_isEquivalent b (ha.trans hab)).isLittleO
    exact h.of_const_mul_right
  apply Asymptotics.IsLittleO.isEquivalent
  have herr := (haerr.sub hberr).trans_isBigO
    (Asymptotics.isBigO_self_const_mul hk main atTop)
  refine herr.congr' ?_ EventuallyEq.rfl
  filter_upwards with X
  dsimp [main]
  ring

/-- Eventual positive lower bound for a fixed multiplicative prime-counting
interval. -/
theorem eventually_primeCounting_fixedDenominator_gap_ge
    {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ X : ℕ in atTop,
      (((a : ℝ)⁻¹ - (b : ℝ)⁻¹) / 2) *
          ((X : ℝ) / Real.log (X : ℝ)) ≤
        (Nat.primeCounting (X / a) : ℝ) -
          (Nat.primeCounting (X / b) : ℝ) := by
  let k : ℝ := (a : ℝ)⁻¹ - (b : ℝ)⁻¹
  let main : ℕ → ℝ := fun X ↦ (X : ℝ) / Real.log (X : ℝ)
  have hk : 0 < k := by
    dsimp [k]
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    exact sub_pos.mpr (inv_strictAnti₀ haR habR)
  have hequiv := primeCounting_fixedDenominator_gap_isEquivalent ha hab
  have hbound := (Asymptotics.isLittleO_iff.mp hequiv.isLittleO)
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, eventually_ge_atTop 2] with X herror hX
  have hmain : 0 ≤ main X := by
    dsimp [main]
    exact div_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X from (by omega))))
  have hkm : 0 ≤ k * main X := mul_nonneg hk.le hmain
  change k / 2 * main X ≤
    (Nat.primeCounting (X / a) : ℝ) -
      (Nat.primeCounting (X / b) : ℝ)
  change
    ‖((Nat.primeCounting (X / a) : ℝ) -
        (Nat.primeCounting (X / b) : ℝ)) - k * main X‖ ≤
      (1 / 2 : ℝ) * ‖k * main X‖ at herror
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hkm] at herror
  have hlower :
      -(1 / 2 * (k * main X)) ≤
        ((Nat.primeCounting (X / a) : ℝ) -
          (Nat.primeCounting (X / b) : ℝ)) - k * main X :=
    neg_le_of_abs_le herror
  calc
    k / 2 * main X = k * main X - 1 / 2 * (k * main X) := by ring
    _ ≤ (Nat.primeCounting (X / a) : ℝ) -
        (Nat.primeCounting (X / b) : ℝ) := by linarith

/-- Once the cutoff contains every deleted prime, finite deletion subtracts
exactly `S.card` from prime counting. -/
theorem allowedPrimeCount_add_card_eq_primeCounting
    {S : Finset ℕ} {N : ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hSN : ∀ p ∈ S, p ≤ N) :
    allowedPrimeCount S N + S.card = Nat.primeCounting N := by
  have hfilter :
      ((Nat.primesLE N).filter fun p ↦ p ∈ S) = S := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · exact fun hp ↦ hp.2
    · intro hp
      exact ⟨⟨hSN p hp, hS p hp⟩, hp⟩
  rw [← allowedPrimeCount_add_deleted S N, hfilter]

/-- Finite deletion cancels from a fixed multiplicative interval after all
deleted primes lie below its lower endpoint. -/
theorem allowedPrimeCount_fixedDenominator_gap_eq
    {S : Finset ℕ} {X a b : ℕ}
    (hS : ∀ p ∈ S, p.Prime) (ha : 0 < a) (hab : a < b)
    (hSN : ∀ p ∈ S, p ≤ X / b) :
    (allowedPrimeCount S (X / a) : ℝ) -
        (allowedPrimeCount S (X / b) : ℝ) =
      (Nat.primeCounting (X / a) : ℝ) -
        (Nat.primeCounting (X / b) : ℝ) := by
  have hdiv : X / b ≤ X / a := by
    exact Nat.div_le_div_left (Nat.le_of_lt hab) ha
  have haeq := allowedPrimeCount_add_card_eq_primeCounting hS
    (fun p hp ↦ (hSN p hp).trans hdiv)
  have hbeq := allowedPrimeCount_add_card_eq_primeCounting hS hSN
  have haeqR :
      (allowedPrimeCount S (X / a) : ℝ) + (S.card : ℝ) =
        (Nat.primeCounting (X / a) : ℝ) := by exact_mod_cast haeq
  have hbeqR :
      (allowedPrimeCount S (X / b) : ℝ) + (S.card : ℝ) =
        (Nat.primeCounting (X / b) : ℝ) := by exact_mod_cast hbeq
  linarith

/-- Every member of a fixed finite set eventually lies below `X / b`. -/
theorem eventually_finset_le_nat_div (S : Finset ℕ) {b : ℕ} (hb : 0 < b) :
    ∀ᶠ X : ℕ in atTop, ∀ p ∈ S, p ≤ X / b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
      have hp := (Nat.tendsto_div_const_atTop hb.ne').eventually
        (Ici_mem_atTop p)
      filter_upwards [ih, hp] with X hSX hpX
      intro q hq
      simp only [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact hpX
      · exact hSX q hq

/-- PNT lower bound for allowed primes in a fixed multiplicative interval. -/
theorem eventually_allowedPrimeCount_fixedDenominator_gap_ge
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ X : ℕ in atTop,
      (((a : ℝ)⁻¹ - (b : ℝ)⁻¹) / 2) *
          ((X : ℝ) / Real.log (X : ℝ)) ≤
        (allowedPrimeCount S (X / a) : ℝ) -
          (allowedPrimeCount S (X / b) : ℝ) := by
  filter_upwards [eventually_primeCounting_fixedDenominator_gap_ge ha hab,
    eventually_finset_le_nat_div S (ha.trans hab)] with X hprime hSN
  rw [allowedPrimeCount_fixedDenominator_gap_eq hS ha hab hSN]
  exact hprime

/-- A linear gap between two nonnegative quantities of size at most `4 M`
becomes a square-root gap of size `sqrt M`. -/
theorem quarter_mul_sqrt_le_abs_sqrt_sub
    {x y M k : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hM : 0 ≤ M) (hk : 0 ≤ k)
    (hxM : x ≤ 4 * M) (hyM : y ≤ 4 * M)
    (hgap : k * M ≤ |x - y|) :
    k / 4 * Real.sqrt M ≤ |Real.sqrt x - Real.sqrt y| := by
  have hsx : Real.sqrt x ≤ 2 * Real.sqrt M := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hM]
  have hsy : Real.sqrt y ≤ 2 * Real.sqrt M := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hM]
  have hsum : Real.sqrt x + Real.sqrt y ≤ 4 * Real.sqrt M := by
    linarith
  have hidentity :
      |x - y| =
        |Real.sqrt x - Real.sqrt y| *
          (Real.sqrt x + Real.sqrt y) := by
    calc
      |x - y| = |(Real.sqrt x) ^ 2 - (Real.sqrt y) ^ 2| := by
        rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
      _ = |Real.sqrt x - Real.sqrt y| *
          (Real.sqrt x + Real.sqrt y) := by
        rw [sq_sub_sq, abs_mul,
          abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
        ring
  have hprod :
      k * M ≤ |Real.sqrt x - Real.sqrt y| * (4 * Real.sqrt M) := by
    calc
      k * M ≤ |x - y| := hgap
      _ = |Real.sqrt x - Real.sqrt y| *
          (Real.sqrt x + Real.sqrt y) := hidentity
      _ ≤ |Real.sqrt x - Real.sqrt y| * (4 * Real.sqrt M) := by
        exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  by_cases hs0 : Real.sqrt M = 0
  · simp [hs0]
  · have hspos : 0 < Real.sqrt M :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs0)
    have hcancel : k * Real.sqrt M ≤
        4 * |Real.sqrt x - Real.sqrt y| := by
      nlinarith [Real.sq_sqrt hM]
    nlinarith

/-- A convenient uniform upper bound for allowed-prime counts.  The constant
`4` is deliberately coarse; only the `X / log X` scale is used later. -/
theorem eventually_allowedPrimeCount_nat_le_four_main (S : Finset ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (allowedPrimeCount S X : ℝ) ≤
        4 * ((X : ℝ) / Real.log (X : ℝ)) := by
  have hcount := tendsto_natCast_atTop_atTop.eventually
    (eventually_allowedPrimeCount_le (S := S) (ε := 1) zero_lt_one)
  filter_upwards [hcount, eventually_ge_atTop 2] with X hcountX hX
  simp only [Nat.floor_natCast] at hcountX
  have hmain : 0 ≤ (X : ℝ) / Real.log (X : ℝ) :=
    div_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X from (by omega))))
  have hcoeff : Real.log 4 + 1 ≤ 4 := by
    have hlog : Real.log 4 < (4 : ℝ) - 1 :=
      Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
    linarith
  calc
    (allowedPrimeCount S X : ℝ) ≤
        (Real.log 4 + 1) * (X : ℝ) / Real.log (X : ℝ) := hcountX
    _ = (Real.log 4 + 1) *
        ((X : ℝ) / Real.log (X : ℝ)) := by ring
    _ ≤ 4 * ((X : ℝ) / Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff hmain

/-- Every square-root-cutoff star degree is bounded by the full allowed-prime
count. -/
theorem sqrtCutoff_largePrimeStarDegree_le_allowedPrimeCount
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (b : Vertex S X) (hb : (b : ℕ) ≤ Nat.sqrt X) :
    largePrimeStarDegree S X (Nat.sqrt X) b ≤ allowedPrimeCount S X := by
  have hYXb : Nat.sqrt X ≤ X / (b : ℕ) := by
    apply (Nat.le_div_iff_mul_le (Vertex.coe_pos b)).2
    calc
      Nat.sqrt X * (b : ℕ) ≤ Nat.sqrt X * Nat.sqrt X :=
        Nat.mul_le_mul_left (Nat.sqrt X) hb
      _ ≤ X := Nat.sqrt_le X
  rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS b hb hYXb]
  exact (Nat.sub_le _ _).trans
    (allowedPrimeCount_mono (Nat.div_le_self X (b : ℕ)))

/-- Uniform `4 X / log X` upper bound for all stars at the square-root cutoff. -/
theorem eventually_sqrtCutoff_largePrimeStarDegree_le_four_main
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ᶠ X : ℕ in atTop, ∀ (b : Vertex S X),
      (b : ℕ) ≤ Nat.sqrt X →
      (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ) ≤
        4 * ((X : ℝ) / Real.log (X : ℝ)) := by
  filter_upwards [eventually_allowedPrimeCount_nat_le_four_main S]
    with X hcount
  intro b hb
  have hdeg :
      (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ) ≤
        (allowedPrimeCount S X : ℝ) := by
    exact_mod_cast sqrtCutoff_largePrimeStarDegree_le_allowedPrimeCount hS b hb
  exact hdeg.trans hcount

/-- Explicit fixed-centre square-root gap constant. -/
def fixedCenterDegreeGapConstant (c : ℕ) : ℝ :=
  (16 * ((c + 1 : ℕ) : ℝ) ^ 2)⁻¹

theorem fixedCenterDegreeGapConstant_pos (c : ℕ) :
    0 < fixedCenterDegreeGapConstant c := by
  dsimp [fixedCenterDegreeGapConstant]
  positivity

/-- The chosen constant lies below one quarter of the upper adjacent-interval
PNT coefficient. -/
theorem four_mul_fixedCenterDegreeGapConstant_le_upper
    {c : ℕ} (hc : 0 < c) :
    4 * fixedCenterDegreeGapConstant c ≤
      ((c : ℝ)⁻¹ - ((c + 1 : ℕ) : ℝ)⁻¹) / 2 := by
  dsimp [fixedCenterDegreeGapConstant]
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hc1R : (0 : ℝ) < (c + 1 : ℕ) := by positivity
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp
  nlinarith

/-- The same constant also lies below one quarter of the lower adjacent-
interval coefficient when that interval exists. -/
theorem four_mul_fixedCenterDegreeGapConstant_le_lower
    {c : ℕ} (hc : 1 < c) :
    4 * fixedCenterDegreeGapConstant c ≤
      (((c - 1 : ℕ) : ℝ)⁻¹ - (c : ℝ)⁻¹) / 2 := by
  dsimp [fixedCenterDegreeGapConstant]
  have hcm1 : 0 < c - 1 := Nat.sub_pos_of_lt hc
  have hcm1R : (0 : ℝ) < ((c - 1 : ℕ) : ℝ) := by exact_mod_cast hcm1
  have hcR : (0 : ℝ) < c := by exact_mod_cast (Nat.zero_lt_of_lt hc)
  rw [Nat.cast_sub (show 1 ≤ c from Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.zero_lt_of_lt hc)))]
  norm_num [Nat.cast_add, Nat.cast_one]
  have hcR1 : (1 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hsub : (0 : ℝ) < (c : ℝ) - 1 := by linarith
  change
    4 * ((((c : ℝ) + 1) ^ 2)⁻¹ * (1 / 16)) ≤
      (((c : ℝ) - 1)⁻¹ - (c : ℝ)⁻¹) / 2
  have hlhs :
      4 * ((((c : ℝ) + 1) ^ 2)⁻¹ * (1 / 16)) =
        1 / (4 * ((c : ℝ) + 1) ^ 2) := by
    field_simp
    ring
  have hrhs :
      (((c : ℝ) - 1)⁻¹ - (c : ℝ)⁻¹) / 2 =
        1 / (2 * ((c : ℝ) - 1) * (c : ℝ)) := by
    field_simp [hsub.ne', hcR.ne']
    ring
  rw [hlhs, hrhs]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg ((c : ℝ) + 1)]

/-- At a common cutoff, subtracting two star degrees cancels the boundary
prime count exactly. -/
theorem largePrimeStarDegree_sub_eq_allowedPrimeCount_gap
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a b : Vertex S X) (haY : (a : ℕ) ≤ Y) (hbY : (b : ℕ) ≤ Y)
    (hYXa : Y ≤ X / (a : ℕ)) (hYXb : Y ≤ X / (b : ℕ)) :
    (largePrimeStarDegree S X Y a : ℝ) -
        (largePrimeStarDegree S X Y b : ℝ) =
      (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
        (allowedPrimeCount S (X / (b : ℕ)) : ℝ) := by
  have haCount := allowedPrimeCount_mono (S := S) hYXa
  have hbCount := allowedPrimeCount_mono (S := S) hYXb
  rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS a haY hYXa,
    largePrimeStarDegree_eq_allowedPrimeCount_sub hS b hbY hYXb,
    Nat.cast_sub haCount, Nat.cast_sub hbCount]
  ring

/-- Quantitative PNT isolates every fixed centre from all other nonempty
large-prime stars at the square-root cutoff. -/
theorem eventually_fixedCenter_sqrtCutoff_otherStarDegreeGap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      ∀ b : Vertex S X, (b : ℕ) ≤ Nat.sqrt X → b ≠ a →
        0 < largePrimeStarDegree S X (Nat.sqrt X) b →
        fixedCenterDegreeGapConstant c *
            Real.sqrt ((X : ℝ) / Real.log (X : ℝ)) ≤
          |Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) -
            Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ)| := by
  have hplus := eventually_allowedPrimeCount_fixedDenominator_gap_ge
    S hS hc (Nat.lt_succ_self c)
  have hcut : ∀ᶠ X : ℕ in atTop, c + 1 ≤ Nat.sqrt X := by
    filter_upwards [eventually_ge_atTop ((c + 1) ^ 2)] with X hX
    exact Nat.le_sqrt'.2 hX
  have hupper := eventually_sqrtCutoff_largePrimeStarDegree_le_four_main S hS
  by_cases hc1 : c = 1
  · filter_upwards [hplus, hcut, hupper, eventually_ge_atTop 2]
      with X hplusX hcutX hupperX hX
    intro a haVal b hbY hba _hbd
    let M : ℝ := (X : ℝ) / Real.log (X : ℝ)
    have hM : 0 ≤ M := by
      dsimp [M]
      exact div_nonneg (by positivity)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X from (by omega))))
    have haY : (a : ℕ) ≤ Nat.sqrt X := by omega
    have hYX (v : Vertex S X) (hv : (v : ℕ) ≤ Nat.sqrt X) :
        Nat.sqrt X ≤ X / (v : ℕ) := by
      apply (Nat.le_div_iff_mul_le (Vertex.coe_pos v)).2
      exact (Nat.mul_le_mul_left (Nat.sqrt X) hv).trans (Nat.sqrt_le X)
    have hbc : c < (b : ℕ) := by
      rw [hc1] at haVal
      have hbpos := Vertex.coe_pos b
      have hbne : (b : ℕ) ≠ 1 := by
        intro hbeq
        apply hba
        apply Subtype.ext
        apply Fin.ext
        exact hbeq.trans haVal.symm
      omega
    have hsucc : c + 1 ≤ (b : ℕ) := by omega
    have hquot : X / (b : ℕ) ≤ X / (c + 1) :=
      Nat.div_le_div_left hsucc (Nat.succ_pos c)
    have hallowed := allowedPrimeCount_mono (S := S) hquot
    have hdiff := largePrimeStarDegree_sub_eq_allowedPrimeCount_gap
      hS a b haY hbY (hYX a haY) (hYX b hbY)
    rw [haVal] at hdiff
    have hkcoeff := four_mul_fixedCenterDegreeGapConstant_le_upper hc
    have hgapNat :
        4 * fixedCenterDegreeGapConstant c * M ≤
          (allowedPrimeCount S (X / c) : ℝ) -
            (allowedPrimeCount S (X / (b : ℕ)) : ℝ) := by
      calc
        4 * fixedCenterDegreeGapConstant c * M ≤
            (((c : ℝ)⁻¹ - ((c + 1 : ℕ) : ℝ)⁻¹) / 2) * M :=
          mul_le_mul_of_nonneg_right hkcoeff hM
        _ ≤ (allowedPrimeCount S (X / c) : ℝ) -
            (allowedPrimeCount S (X / (c + 1)) : ℝ) := by
          simpa [M] using hplusX
        _ ≤ (allowedPrimeCount S (X / c) : ℝ) -
            (allowedPrimeCount S (X / (b : ℕ)) : ℝ) := by
          exact sub_le_sub_left (by exact_mod_cast hallowed) _
    have hstarGap :
        4 * fixedCenterDegreeGapConstant c * M ≤
          |(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) -
            (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ)| := by
      rw [hdiff]
      exact hgapNat.trans (le_abs_self _)
    simpa [M] using (quarter_mul_sqrt_le_abs_sqrt_sub
      (by positivity) (by positivity) hM
      (mul_nonneg (by norm_num) (fixedCenterDegreeGapConstant_pos c).le)
      (hupperX a haY) (hupperX b hbY) hstarGap)
  · have hcgt : 1 < c := by omega
    have hminus := eventually_allowedPrimeCount_fixedDenominator_gap_ge
      S hS (Nat.sub_pos_of_lt hcgt) (Nat.sub_lt (Nat.zero_lt_of_lt hcgt) zero_lt_one)
    filter_upwards [hplus, hminus, hcut, hupper, eventually_ge_atTop 2]
      with X hplusX hminusX hcutX hupperX hX
    intro a haVal b hbY hba _hbd
    let M : ℝ := (X : ℝ) / Real.log (X : ℝ)
    have hM : 0 ≤ M := by
      dsimp [M]
      exact div_nonneg (by positivity)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X from (by omega))))
    have haY : (a : ℕ) ≤ Nat.sqrt X := by omega
    have hYX (v : Vertex S X) (hv : (v : ℕ) ≤ Nat.sqrt X) :
        Nat.sqrt X ≤ X / (v : ℕ) := by
      apply (Nat.le_div_iff_mul_le (Vertex.coe_pos v)).2
      exact (Nat.mul_le_mul_left (Nat.sqrt X) hv).trans (Nat.sqrt_le X)
    have hbcne : (b : ℕ) ≠ c := by
      intro hbeq
      apply hba
      apply Subtype.ext
      apply Fin.ext
      exact hbeq.trans haVal.symm
    rcases lt_or_gt_of_ne hbcne with hbc | hbc
    · have hbcm1 : (b : ℕ) ≤ c - 1 := by omega
      have hquot : X / (c - 1) ≤ X / (b : ℕ) :=
        Nat.div_le_div_left hbcm1 (Vertex.coe_pos b)
      have hallowed := allowedPrimeCount_mono (S := S) hquot
      have hdiff := largePrimeStarDegree_sub_eq_allowedPrimeCount_gap
        hS b a hbY haY (hYX b hbY) (hYX a haY)
      rw [haVal] at hdiff
      have hkcoeff := four_mul_fixedCenterDegreeGapConstant_le_lower hcgt
      have hgapNat :
          4 * fixedCenterDegreeGapConstant c * M ≤
            (allowedPrimeCount S (X / (b : ℕ)) : ℝ) -
              (allowedPrimeCount S (X / c) : ℝ) := by
        calc
          4 * fixedCenterDegreeGapConstant c * M ≤
              ((((c - 1 : ℕ) : ℝ)⁻¹ - (c : ℝ)⁻¹) / 2) * M :=
            mul_le_mul_of_nonneg_right hkcoeff hM
          _ ≤ (allowedPrimeCount S (X / (c - 1)) : ℝ) -
              (allowedPrimeCount S (X / c) : ℝ) := by
            simpa [M] using hminusX
          _ ≤ (allowedPrimeCount S (X / (b : ℕ)) : ℝ) -
              (allowedPrimeCount S (X / c) : ℝ) := by
            exact sub_le_sub_right (by exact_mod_cast hallowed) _
      have hstarGap :
          4 * fixedCenterDegreeGapConstant c * M ≤
            |(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) -
              (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ)| := by
        rw [abs_sub_comm, hdiff]
        exact hgapNat.trans (le_abs_self _)
      simpa [M] using (quarter_mul_sqrt_le_abs_sqrt_sub
        (by positivity) (by positivity) hM
        (mul_nonneg (by norm_num) (fixedCenterDegreeGapConstant_pos c).le)
        (hupperX a haY) (hupperX b hbY) hstarGap)
    · have hsucc : c + 1 ≤ (b : ℕ) := by omega
      have hquot : X / (b : ℕ) ≤ X / (c + 1) :=
        Nat.div_le_div_left hsucc (Nat.succ_pos c)
      have hallowed := allowedPrimeCount_mono (S := S) hquot
      have hdiff := largePrimeStarDegree_sub_eq_allowedPrimeCount_gap
        hS a b haY hbY (hYX a haY) (hYX b hbY)
      rw [haVal] at hdiff
      have hkcoeff := four_mul_fixedCenterDegreeGapConstant_le_upper hc
      have hgapNat :
          4 * fixedCenterDegreeGapConstant c * M ≤
            (allowedPrimeCount S (X / c) : ℝ) -
              (allowedPrimeCount S (X / (b : ℕ)) : ℝ) := by
        calc
          4 * fixedCenterDegreeGapConstant c * M ≤
              (((c : ℝ)⁻¹ - ((c + 1 : ℕ) : ℝ)⁻¹) / 2) * M :=
            mul_le_mul_of_nonneg_right hkcoeff hM
          _ ≤ (allowedPrimeCount S (X / c) : ℝ) -
              (allowedPrimeCount S (X / (c + 1)) : ℝ) := by
            simpa [M] using hplusX
          _ ≤ (allowedPrimeCount S (X / c) : ℝ) -
              (allowedPrimeCount S (X / (b : ℕ)) : ℝ) := by
            exact sub_le_sub_left (by exact_mod_cast hallowed) _
      have hstarGap :
          4 * fixedCenterDegreeGapConstant c * M ≤
            |(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) -
              (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ)| := by
        rw [hdiff]
        exact hgapNat.trans (le_abs_self _)
      simpa [M] using (quarter_mul_sqrt_le_abs_sqrt_sub
        (by positivity) (by positivity) hM
        (mul_nonneg (by norm_num) (fixedCenterDegreeGapConstant_pos c).le)
        (hupperX a haY) (hupperX b hbY) hstarGap)

/-- The same fixed-centre constant also separates the target frequency from
zero. -/
theorem eventually_fixedCenter_sqrtCutoff_zeroDegreeGap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      fixedCenterDegreeGapConstant c *
          Real.sqrt ((X : ℝ) / Real.log (X : ℝ)) ≤
        Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
  have hplus := eventually_allowedPrimeCount_fixedDenominator_gap_ge
    S hS hc (Nat.lt_succ_self c)
  have hcut : ∀ᶠ X : ℕ in atTop, c + 1 ≤ Nat.sqrt X := by
    filter_upwards [eventually_ge_atTop ((c + 1) ^ 2)] with X hX
    exact Nat.le_sqrt'.2 hX
  have hupper := eventually_sqrtCutoff_largePrimeStarDegree_le_four_main S hS
  filter_upwards [hplus, hcut, hupper, eventually_ge_atTop 2]
    with X hplusX hcutX hupperX hX
  intro a haVal
  let M : ℝ := (X : ℝ) / Real.log (X : ℝ)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X from (by omega))))
  have haY : (a : ℕ) ≤ Nat.sqrt X := by omega
  have hYXa : Nat.sqrt X ≤ X / (a : ℕ) := by
    apply (Nat.le_div_iff_mul_le (Vertex.coe_pos a)).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hYXsucc : Nat.sqrt X ≤ X / (c + 1) := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos c)).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) hcutX).trans (Nat.sqrt_le X)
  have hboundary := allowedPrimeCount_mono (S := S) hYXsucc
  have hcount := allowedPrimeCount_mono (S := S) hYXa
  have hdegree :
      (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) =
        (allowedPrimeCount S (X / c) : ℝ) -
          (allowedPrimeCount S (Nat.sqrt X) : ℝ) := by
    rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS a haY hYXa,
      Nat.cast_sub hcount, haVal]
  have hkcoeff := four_mul_fixedCenterDegreeGapConstant_le_upper hc
  have hgapDegree :
      4 * fixedCenterDegreeGapConstant c * M ≤
        (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
    calc
      4 * fixedCenterDegreeGapConstant c * M ≤
          (((c : ℝ)⁻¹ - ((c + 1 : ℕ) : ℝ)⁻¹) / 2) * M :=
        mul_le_mul_of_nonneg_right hkcoeff hM
      _ ≤ (allowedPrimeCount S (X / c) : ℝ) -
          (allowedPrimeCount S (X / (c + 1)) : ℝ) := by
        simpa [M] using hplusX
      _ ≤ (allowedPrimeCount S (X / c) : ℝ) -
          (allowedPrimeCount S (Nat.sqrt X) : ℝ) := by
        exact sub_le_sub_left (by exact_mod_cast hboundary) _
      _ = (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := hdegree.symm
  have hstarGap :
      4 * fixedCenterDegreeGapConstant c * M ≤
        |(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) - (0 : ℝ)| := by
    rw [sub_zero, abs_of_nonneg (by positivity)]
    exact hgapDegree
  simpa [M, abs_of_nonneg (Real.sqrt_nonneg _)] using
    (quarter_mul_sqrt_le_abs_sqrt_sub
    (by positivity) (by norm_num) hM
    (mul_nonneg (by norm_num) (fixedCenterDegreeGapConstant_pos c).le)
    (hupperX a haY) (by positivity) hstarGap)

/-- Combined arithmetic input for the fixed-centre Feshbach wrapper: the
target star is nonempty, separated from zero, and separated from every other
nonempty star. -/
theorem eventually_fixedCenter_sqrtCutoff_degreeGap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      0 < largePrimeStarDegree S X (Nat.sqrt X) a ∧
      fixedCenterDegreeGapConstant c *
          Real.sqrt ((X : ℝ) / Real.log (X : ℝ)) ≤
        Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) ∧
      ∀ b : Vertex S X, (b : ℕ) ≤ Nat.sqrt X → b ≠ a →
        0 < largePrimeStarDegree S X (Nat.sqrt X) b →
        fixedCenterDegreeGapConstant c *
            Real.sqrt ((X : ℝ) / Real.log (X : ℝ)) ≤
          |Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) -
            Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ)| := by
  filter_upwards [eventually_fixedCenter_sqrtCutoff_zeroDegreeGap S hS hc,
    eventually_fixedCenter_sqrtCutoff_otherStarDegreeGap S hS hc,
    eventually_ge_atTop 2] with X hzero hother hX
  intro a haVal
  have hzeroA := hzero a haVal
  have hotherA := hother a haVal
  have hmainPos : 0 < (X : ℝ) / Real.log (X : ℝ) := by
    exact div_pos (by positivity)
      (Real.log_pos (by exact_mod_cast (show 1 < X from (by omega))))
  have hgammaPos :
      0 < fixedCenterDegreeGapConstant c *
        Real.sqrt ((X : ℝ) / Real.log (X : ℝ)) :=
    mul_pos (fixedCenterDegreeGapConstant_pos c) (Real.sqrt_pos.2 hmainPos)
  have hsqrtPos :
      0 < Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) :=
    hgammaPos.trans_le hzeroA
  have hdR : (0 : ℝ) < largePrimeStarDegree S X (Nat.sqrt X) a :=
    (Real.sqrt_pos).mp hsqrtPos
  have hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a := by
    exact_mod_cast hdR
  exact ⟨hd, hzeroA, hotherA⟩

end

end PrimeStar
