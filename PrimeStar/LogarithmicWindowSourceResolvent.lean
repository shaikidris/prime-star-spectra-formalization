import PrimeStar.LogarithmicWindowSourceArithmetic

/-!
# Uniform source-weighted first-exit resolvent

The canonical first-exit resolvent is an orthogonal direct sum of explicit
star blocks.  Uniform degree-ratio barriers bound every local block, while
the PNT endpoint count and the moving centre-degree lower bound give the
global scale `a / sqrt X` without a global resolvent-norm loss.
-/

namespace PrimeStar

open Filter Topology
open scoped InnerProductSpace

noncomputable section

/-- Uniform direct-sum estimate for the explicit canonical first-exit
resolvent on the logarithmic centre window. -/
theorem eventually_logarithmicWindow_sum_canonicalExitResolvent_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        let Y := Nat.sqrt X
        let mu := √(largePrimeStarDegree S X Y a : ℝ)
        let c0 := largePrimeNormalizedStarMode S X Y a 1 a
        ‖∑ i : CanonicalExitIndex S X Y a,
            canonicalExitResolvent hS a mu c0 i‖ ^ 2 ≤
          80000000 * ((a : ℝ) / (Y : ℝ)) := by
  filter_upwards [
      eventually_allowedPrimeCount_natSqrt_le_twelve_sqrt_div_log S,
      eventually_logarithmicWindow_largePrimeStarDegree_ge S hS hε,
      eventually_logarithmicWindow_canonicalUpDegreeRatio_le S hS hε,
      eventually_logarithmicWindow_canonicalDownDegreeRatio_ge S hS hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε,
      eventually_ge_atTop 4]
      with X hcount hdegree hupRatio hdownRatio hcenter hX
  intro a ha
  dsimp only
  let Y := Nat.sqrt X
  let d : ℝ := largePrimeStarDegree S X Y a
  let mu : ℝ := √d
  let c0 : ℝ := largePrimeNormalizedStarMode S X Y a 1 a
  have hYtwo : 2 ≤ Y := by dsimp [Y]; exact Nat.le_sqrt'.2 (by omega)
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hLpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have haY : (a : ℕ) ≤ Y := hcenter (a : ℕ) ha
  have haPos : (0 : ℝ) < (a : ℕ) := by exact_mod_cast Vertex.coe_pos a
  have hdLower :
      (X : ℝ) / ((16 * (a : ℝ)) * Real.log (X : ℝ)) ≤ d := by
    simpa [d, Y, mul_assoc] using hdegree a ha
  have hdPos : 0 < d := by
    have : 0 < (X : ℝ) /
        ((16 * (a : ℝ)) * Real.log (X : ℝ)) := by positivity
    exact this.trans_le hdLower
  have hdNat : 0 < largePrimeStarDegree S X Y a := by
    change 0 < (largePrimeStarDegree S X Y a : ℝ) at hdPos
    exact_mod_cast hdPos
  have hmu : mu ≠ 0 := Real.sqrt_ne_zero'.mpr hdPos
  have hmuSq : mu ^ 2 = d := by
    dsimp [mu]
    exact Real.sq_sqrt hdPos.le
  have hc0 : c0 ^ 2 = 1 / 2 := by
    dsimp [c0]
    exact sq_largePrimeNormalizedStarMode_center (by norm_num) hdNat
  have hcut : X < (Y + 1) * (Y + 1) := by
    simpa [Y] using sqrtCutoff_condition X
  have hcY : (a : ℕ) * Y ≤ X :=
    (Nat.mul_le_mul_right Y haY).trans (Nat.sqrt_le X)
  have hupCardNat :
      Fintype.card (CanonicalUpIndex S X Y a) = allowedPrimeCount S Y := by
    simpa using card_univ_canonicalUpIndex_eq_allowedPrimeCount hcY
  have hdownCardNat :
      Fintype.card (CanonicalDownIndex a) ≤ allowedPrimeCount S Y := by
    simpa using card_univ_canonicalDownIndex_le_allowedPrimeCount a haY
  have hlocal : ∀ i : CanonicalExitIndex S X Y a,
      ‖canonicalExitResolvent hS a mu c0 i‖ ^ 2 ≤ 200000 / mu ^ 2 := by
    intro i
    rcases i with q | q
    · have hr := hupRatio a ha q
      have hr' :
          (largePrimeStarDegree S X Y (canonicalUpTarget hS a q) : ℝ) /
              mu ^ 2 ≤ 199 / 200 := by
        simpa [Y, hmuSq, d] using hr
      have hr0 : 0 ≤
          (largePrimeStarDegree S X Y (canonicalUpTarget hS a q) : ℝ) /
            mu ^ 2 := by positivity
      have hden : mu ^ 2 ≠
          (largePrimeStarDegree S X Y (canonicalUpTarget hS a q) : ℝ) := by
        intro heq
        have hone :
            (largePrimeStarDegree S X Y (canonicalUpTarget hS a q) : ℝ) /
                mu ^ 2 = 1 := (div_eq_one_iff_eq (pow_ne_zero 2 hmu)).2 heq.symm
        rw [hone] at hr'
        norm_num at hr'
      exact norm_actualUpStarResolvent_sq_le_of_ratio hmu hden hc0 hr0 hr'
    · have hr := hdownRatio a ha q
      have hr' : 201 / 200 ≤
          (largePrimeStarDegree S X Y (canonicalDownTarget a q) : ℝ) /
            mu ^ 2 := by
        simpa [Y, hmuSq, d] using hr
      have hden : mu ^ 2 ≠
          (largePrimeStarDegree S X Y (canonicalDownTarget a q) : ℝ) := by
        intro heq
        have hone :
            (largePrimeStarDegree S X Y (canonicalDownTarget a q) : ℝ) /
                mu ^ 2 = 1 := (div_eq_one_iff_eq (pow_ne_zero 2 hmu)).2 heq.symm
        rw [hone] at hr'
        norm_num at hr'
      have hP := canonicalDownLeaves_subset_largePrimeLeaves
        (S := S) (X := X) (Y := Y) (q := (q : ℕ)) (canonicalDownTarget a q)
      have hcardNat := card_canonicalDownLeaves_eq_boundaryDegree hS haY q
      have hcard :
          ((canonicalDownLeaves S X Y (canonicalDownTarget a q) q).card : ℝ) =
            mu ^ 2 := by
        rw [hcardNat, hmuSq]
      exact norm_actualDownStarResolvent_sq_le_of_ratio
        hP hcard hmu hden hc0 hr'
  rw [norm_sum_canonicalExitResolvent_sq hS hcut haY,
    Fintype.sum_sum_type]
  have hupSum :
      (∑ q : CanonicalUpIndex S X Y a,
          ‖canonicalExitResolvent hS a mu c0 (Sum.inl q)‖ ^ 2) ≤
        (Fintype.card (CanonicalUpIndex S X Y a) : ℝ) *
          (200000 / mu ^ 2) := by
    calc
      _ ≤ ∑ _q : CanonicalUpIndex S X Y a, (200000 / mu ^ 2) := by
        exact Finset.sum_le_sum fun q _hq ↦ hlocal (Sum.inl q)
      _ = _ := by simp
  have hdownSum :
      (∑ q : CanonicalDownIndex a,
          ‖canonicalExitResolvent hS a mu c0
            (Sum.inr q : CanonicalExitIndex S X Y a)‖ ^ 2) ≤
        (Fintype.card (CanonicalDownIndex a) : ℝ) *
          (200000 / mu ^ 2) := by
    calc
      _ ≤ ∑ _q : CanonicalDownIndex a, (200000 / mu ^ 2) := by
        exact Finset.sum_le_sum fun q _hq ↦
          hlocal (Sum.inr q : CanonicalExitIndex S X Y a)
      _ = _ := by simp
  have hcards :
      (Fintype.card (CanonicalUpIndex S X Y a) : ℝ) +
          (Fintype.card (CanonicalDownIndex a) : ℝ) ≤
        2 * (allowedPrimeCount S Y : ℝ) := by
    exact_mod_cast (by omega :
      Fintype.card (CanonicalUpIndex S X Y a) +
          Fintype.card (CanonicalDownIndex a) ≤
        2 * allowedPrimeCount S Y)
  have hmuInv : 1 / mu ^ 2 ≤
      (16 * (a : ℝ) * Real.log (X : ℝ)) / (X : ℝ) := by
    rw [hmuSq]
    have hXpos : (0 : ℝ) < X := by positivity
    have hdenPos : 0 < 16 * (a : ℝ) * Real.log (X : ℝ) := by positivity
    have hbasePos : 0 < (X : ℝ) /
        (16 * (a : ℝ) * Real.log (X : ℝ)) := div_pos hXpos hdenPos
    calc
      1 / d ≤ 1 / ((X : ℝ) /
          (16 * (a : ℝ) * Real.log (X : ℝ))) :=
        one_div_le_one_div_of_le hbasePos hdLower
      _ = (16 * (a : ℝ) * Real.log (X : ℝ)) / (X : ℝ) := by
        field_simp [hdenPos.ne', hXpos.ne']
  have hcount' : (allowedPrimeCount S Y : ℝ) ≤
      12 * ((Y : ℝ) / Real.log (X : ℝ)) := by simpa [Y] using hcount
  have hYsq : (Y : ℝ) ^ 2 ≤ (X : ℝ) := by
    exact_mod_cast (show Y ^ 2 ≤ X by simpa [Y, pow_two] using Nat.sqrt_le X)
  calc
    (∑ q : CanonicalUpIndex S X Y a,
        ‖canonicalExitResolvent hS a mu c0 (Sum.inl q)‖ ^ 2) +
      ∑ q : CanonicalDownIndex a,
        ‖canonicalExitResolvent hS a mu c0
          (Sum.inr q : CanonicalExitIndex S X Y a)‖ ^ 2 ≤
        ((Fintype.card (CanonicalUpIndex S X Y a) : ℝ) +
          (Fintype.card (CanonicalDownIndex a) : ℝ)) *
            (200000 / mu ^ 2) := by nlinarith
    _ ≤ (2 * (allowedPrimeCount S Y : ℝ)) *
          (200000 / mu ^ 2) := by gcongr <;> positivity
    _ ≤ (2 * (12 * ((Y : ℝ) / Real.log (X : ℝ)))) *
          (200000 * ((16 * (a : ℝ) * Real.log (X : ℝ)) / (X : ℝ))) := by
      have hK : 0 ≤ (200000 : ℝ) := by norm_num
      have hmuInv0 : 0 ≤ 1 / mu ^ 2 := by positivity
      have hright0 : 0 ≤
          (16 * (a : ℝ) * Real.log (X : ℝ)) / (X : ℝ) := by positivity
      calc
        (2 * (allowedPrimeCount S Y : ℝ)) * (200000 / mu ^ 2) =
            (2 * (allowedPrimeCount S Y : ℝ)) * (200000 * (1 / mu ^ 2)) := by ring
        _ ≤ (2 * (12 * ((Y : ℝ) / Real.log (X : ℝ)))) *
            (200000 * ((16 * (a : ℝ) * Real.log (X : ℝ)) / (X : ℝ))) := by
              gcongr
    _ ≤ 80000000 * ((a : ℝ) / (Y : ℝ)) := by
      field_simp [hLpos.ne', hYpos.ne']
      nlinarith

/-- The actual first-exit compression resolvent inherits the same uniform
source-weighted bound from its exact canonical block decomposition. -/
theorem eventually_logarithmicWindow_firstExitResolvent_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ (gamma : ℝ) (hgamma : 0 < gamma)
          (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
            gamma * ‖x‖ ≤
              ‖√(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) • x -
                firstExitLargePrimeCompressionOperator S X (Nat.sqrt X) a x‖),
        ‖firstExitLargePrimeResolventOfGap S X (Nat.sqrt X) a
            (√(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)) gamma hgamma hgap
            (normalizedPrimeStarFirstExit S X (Nat.sqrt X) a)‖ ^ 2 ≤
          80000000 * ((a : ℝ) / (Nat.sqrt X : ℝ)) := by
  filter_upwards [
      eventually_logarithmicWindow_sum_canonicalExitResolvent_sq_le S hS hε,
      eventually_logarithmicWindow_largePrimeStarDegree_ge S hS hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε,
      eventually_ge_atTop 4]
      with X hsum hdegree hcenter hX
  intro a ha gamma hgamma hgap
  have haY := hcenter (a : ℕ) ha
  have hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a := by
    have hL := hdegree a ha
    have haPos : (0 : ℝ) < (a : ℕ) := by
      exact_mod_cast Vertex.coe_pos a
    have hXpos : (0 : ℝ) < X := by positivity
    have hdenPos : 0 < (16 * (a : ℝ)) * Real.log (X : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) haPos)
        (Real.log_pos (by exact_mod_cast (show 1 < X by omega)))
    have hpos : 0 < (X : ℝ) /
        ((16 * (a : ℝ)) * Real.log (X : ℝ)) := div_pos hXpos hdenPos
    have hdReal : 0 < (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) :=
      hpos.trans_le hL
    exact_mod_cast hdReal
  rw [firstExitLargePrimeResolventOfGap_eq_sum_canonicalResolvents
    hS (sqrtCutoff_condition X) haY hd rfl hgamma hgap]
  simpa [Fintype.sum_sum_type, canonicalExitResolvent] using hsum a ha

end

end PrimeStar
