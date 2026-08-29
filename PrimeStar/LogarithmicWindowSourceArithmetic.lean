import PrimeStar.LogarithmicWindowSourceNorm

/-!
# Arithmetic input for the logarithmic-window source norm

This module supplies the moving lower bound for the boundary-star degree.
The proof sums the already formalized adjacent PNT gaps from `a` through
`2a`; it therefore remains uniform when `a` grows in the logarithmic window.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

/-- The square-root endpoint contains at most a constant multiple of
`sqrt X / log X` allowed primes. -/
theorem eventually_allowedPrimeCount_natSqrt_le_twelve_sqrt_div_log
    (S : Finset ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (allowedPrimeCount S (Nat.sqrt X) : ℝ) ≤
        12 * ((Nat.sqrt X : ℝ) / Real.log (X : ℝ)) := by
  obtain ⟨N₀, hcount⟩ := eventually_atTop.1
    (eventually_allowedPrimeCount_nat_le_four_main S)
  have hratio : ∀ᶠ X : ℕ in atTop,
      (1 / 3 : ℝ) <
        Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) :=
    (log_natSqrt_div_log_tendsto_half.eventually
      (isOpen_Ioi.mem_nhds (by norm_num : (1 / 3 : ℝ) < 1 / 2)))
  filter_upwards [tendsto_natSqrt_atTop.eventually_ge_atTop N₀, hratio,
      eventually_ge_atTop 4] with X hYlarge hratioX hX
  have hcountY := hcount (Nat.sqrt X) hYlarge
  have hsqrtTwo : 2 ≤ Nat.sqrt X := Nat.le_sqrt'.2 (by omega)
  have hYpos : (0 : ℝ) < Nat.sqrt X := by
    exact_mod_cast (show 0 < Nat.sqrt X by omega)
  have hLpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogYpos : 0 < Real.log (Nat.sqrt X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Nat.sqrt X by omega))
  have hcross : Real.log (X : ℝ) <
      3 * Real.log (Nat.sqrt X : ℝ) := by
    have := (lt_div_iff₀ hLpos).mp hratioX
    nlinarith
  calc
    (allowedPrimeCount S (Nat.sqrt X) : ℝ) ≤
        4 * ((Nat.sqrt X : ℝ) /
          Real.log (Nat.sqrt X : ℝ)) := hcountY
    _ = (4 / Real.log (Nat.sqrt X : ℝ)) * (Nat.sqrt X : ℝ) := by ring
    _ ≤ (12 / Real.log (X : ℝ)) * (Nat.sqrt X : ℝ) := by
      have hrecip : 4 / Real.log (Nat.sqrt X : ℝ) ≤
          12 / Real.log (X : ℝ) := by
        rw [div_le_div_iff₀ hlogYpos hLpos]
        nlinarith
      exact mul_le_mul_of_nonneg_right hrecip hYpos.le
    _ = 12 * ((Nat.sqrt X : ℝ) / Real.log (X : ℝ)) := by ring

/-- The distinct prime divisors indexing down-stars inject into the allowed
prime labels through the cutoff whenever the centre lies below it. -/
theorem card_univ_canonicalDownIndex_le_allowedPrimeCount
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X) {Y : ℕ}
    (haY : (a : ℕ) ≤ Y) :
    (Finset.univ : Finset (CanonicalDownIndex a)).card ≤
      allowedPrimeCount S Y := by
  rw [Finset.card_univ, Fintype.card_coe]
  apply Finset.card_le_card
  intro q hq
  apply Finset.mem_filter.mpr
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqLe : q ≤ Y := (Nat.le_of_mem_primeFactors hq).trans haY
  refine ⟨Nat.mem_primesLE.mpr ⟨hqLe, hqPrime⟩, ?_⟩
  intro hqS
  exact Vertex.not_dvd_of_mem a hqS (Nat.dvd_of_mem_primeFactors hq)

/-- Doubling a centre in the `ε` window places it in the slightly larger
`ε/2` window, uniformly for large `X`. -/
theorem eventually_two_mul_center_mem_halfLogarithmicWindow
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        InLogarithmicCenterWindow (ε / 2) X (2 * a) := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowTop : Tendsto
      (fun X : ℕ ↦ Real.log (X : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp hlogTop
  filter_upwards [hpowTop.eventually_ge_atTop 2,
      hlogTop.eventually_gt_atTop 0] with X hpow hlog
  intro a ha
  refine ⟨Nat.mul_pos (by norm_num) ha.1, ?_⟩
  let L : ℝ := Real.log (X : ℝ)
  have hL : 0 < L := hlog
  have hbase : 0 ≤ L ^ (1 / 2 - ε) := Real.rpow_nonneg hL.le _
  have hmul : 2 * (a : ℝ) ≤
      L ^ (1 / 2 - ε) * L ^ (ε / 2) := by
    calc
      2 * (a : ℝ) ≤ 2 * L ^ (1 / 2 - ε) := by gcongr; exact ha.2
      _ ≤ L ^ (1 / 2 - ε) * L ^ (ε / 2) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow hbase
  push_cast
  calc
    (2 : ℝ) * a ≤ L ^ (1 / 2 - ε) * L ^ (ε / 2) := hmul
    _ = L ^ (1 / 2 - ε / 2) := by
      rw [← Real.rpow_add hL]
      congr 1
      ring

/-- Summed adjacent PNT gaps on any integer interval ending at a centre in
the logarithmic window. -/
theorem eventually_logarithmicWindow_allowedPrimeCount_interval_gap_ge
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        ∀ b : ℕ, 0 < b → b ≤ a →
          (((a - b : ℕ) : ℝ) * (X : ℝ)) /
                (4 * (a : ℝ) ^ 2 * Real.log (X : ℝ)) ≤
            (allowedPrimeCount S (X / b) : ℝ) -
              (allowedPrimeCount S (X / a) : ℝ) := by
  filter_upwards [
      eventually_logarithmicWindow_allowedPrimeCount_adjacent_gap_ge S hS hε,
      eventually_ge_atTop 4]
      with X hadj hX
  intro a ha b hb hba
  let L : ℝ := Real.log (X : ℝ)
  let F : ℕ → ℝ := fun k ↦ (allowedPrimeCount S (X / (b + k)) : ℝ)
  let m : ℝ := (X : ℝ) / (4 * (a : ℝ) ^ 2 * L)
  have haPos : 0 < a := hb.trans_le hba
  have haR : (0 : ℝ) < a := by exact_mod_cast haPos
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hterm : ∀ k ∈ Finset.range (a - b), m ≤ F k - F (k + 1) := by
    intro k hk
    have hklt : k < a - b := Finset.mem_range.mp hk
    let n : ℕ := b + k
    have hnPos : 0 < n := by dsimp [n]; omega
    have hn1Le : n + 1 ≤ a := by dsimp [n]; omega
    have hnWindow : InLogarithmicCenterWindow ε X n := by
      refine ⟨hnPos, ?_⟩
      exact (by exact_mod_cast (show n ≤ a by omega) : (n : ℝ) ≤ a).trans ha.2
    have hgap := hadj n hnWindow
    have hnLeR : (n : ℝ) ≤ a := by exact_mod_cast (show n ≤ a by omega)
    have hn1LeR : ((n + 1 : ℕ) : ℝ) ≤ a := by exact_mod_cast hn1Le
    have hprod : (n : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ (a : ℝ) ^ 2 := by
      simpa [pow_two] using
        (mul_le_mul hnLeR hn1LeR (by positivity) (by positivity))
    have hden : 4 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) * L ≤
        4 * (a : ℝ) ^ 2 * L := by
      have hfour : 4 * ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) ≤
          4 * (a : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 4)
      have hfourL := mul_le_mul_of_nonneg_right hfour hL.le
      ring_nf at hfourL ⊢
      exact hfourL
    have hmGap : m ≤
        (X : ℝ) /
          (4 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) * L) := by
      dsimp [m]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    exact hmGap.trans (by simpa [F, n, Nat.add_assoc] using hgap)
  have hsumTerms := Finset.sum_le_sum hterm
  have htel :
      (∑ k ∈ Finset.range (a - b), (F k - F (k + 1))) =
        F 0 - F (a - b) := by
    have h := Finset.sum_range_sub (fun k ↦ -F k) (a - b)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hendpoint : F (a - b) = (allowedPrimeCount S (X / a) : ℝ) := by
    simp [F, Nat.add_sub_of_le hba]
  have hstart : F 0 = (allowedPrimeCount S (X / b) : ℝ) := by simp [F]
  have hsum : ((a - b : ℕ) : ℝ) * m ≤ F 0 - F (a - b) := by
    simpa [htel] using hsumTerms
  rw [hstart, hendpoint] at hsum
  simpa [m, L, mul_div_assoc] using hsum

/-- Uniform main-scale lower bound for a square-cutoff star degree. -/
theorem eventually_logarithmicWindow_largePrimeStarDegree_ge
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        (X : ℝ) /
              (16 * (a : ℝ) * Real.log (X : ℝ)) ≤
          (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [
      eventually_two_mul_center_mem_halfLogarithmicWindow hε,
      eventually_logarithmicWindow_allowedPrimeCount_adjacent_gap_ge S hS hhalf,
      eventually_center_le_natSqrt_on_logarithmicWindow hhalf,
      eventually_ge_atTop 4]
      with X hdouble hadj hcenter hX
  intro a ha
  let A : ℕ := (a : ℕ)
  let L : ℝ := Real.log (X : ℝ)
  let F : ℕ → ℝ := fun k ↦ (allowedPrimeCount S (X / (A + k)) : ℝ)
  let m : ℝ := (X : ℝ) / (16 * (A : ℝ) ^ 2 * L)
  have hAPos : 0 < A := Vertex.coe_pos a
  have hAR : (0 : ℝ) < A := by exact_mod_cast hAPos
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hdoubleWindow := hdouble A ha
  have htwoAY : 2 * A ≤ Nat.sqrt X := hcenter (2 * A) hdoubleWindow
  have haY : A ≤ Nat.sqrt X := by omega
  have hYXa : Nat.sqrt X ≤ X / A := by
    apply (Nat.le_div_iff_mul_le hAPos).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hYXtwo : Nat.sqrt X ≤ X / (2 * A) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * A)).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) htwoAY).trans (Nat.sqrt_le X)
  have hboundary := allowedPrimeCount_mono (S := S) hYXtwo
  have hcountXa := allowedPrimeCount_mono (S := S) hYXa
  have hterm : ∀ k ∈ Finset.range A, m ≤ F k - F (k + 1) := by
    intro k hk
    have hkA : k < A := Finset.mem_range.mp hk
    let n : ℕ := A + k
    have hnPos : 0 < n := by dsimp [n]; omega
    have hnLe : n + 1 ≤ 2 * A := by dsimp [n]; omega
    have hnWindow : InLogarithmicCenterWindow (ε / 2) X n := by
      refine ⟨hnPos, ?_⟩
      exact (by exact_mod_cast (show n ≤ 2 * A by omega) :
        (n : ℝ) ≤ (2 * A : ℕ)).trans
        hdoubleWindow.2
    have hgap := hadj n hnWindow
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hn1R : (0 : ℝ) < n + 1 := by positivity
    have hden :
        4 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) * L ≤
          16 * (A : ℝ) ^ 2 * L := by
      have hnLeR : (n : ℝ) ≤ 2 * A := by exact_mod_cast (show n ≤ 2 * A by omega)
      have hn1LeR : ((n + 1 : ℕ) : ℝ) ≤ 2 * A := by exact_mod_cast hnLe
      have hprod : (n : ℝ) * ((n + 1 : ℕ) : ℝ) ≤
          (2 * (A : ℝ)) * (2 * (A : ℝ)) :=
        mul_le_mul hnLeR hn1LeR (by positivity) (by positivity)
      have hprodL := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 4)) hL.le
      nlinarith
    have hmGap : m ≤
        (X : ℝ) /
          (4 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) * L) := by
      dsimp [m]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    exact hmGap.trans (by simpa [F, n, Nat.add_assoc] using hgap)
  have hsum : (A : ℝ) * m ≤ F 0 - F A := by
    have hsumTerms := Finset.sum_le_sum hterm
    have htel :
        (∑ k ∈ Finset.range A, (F k - F (k + 1))) = F 0 - F A := by
      have h := Finset.sum_range_sub (fun k ↦ -F k) A
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    simpa [htel] using hsumTerms
  have hscale : (A : ℝ) * m =
      (X : ℝ) / (16 * (A : ℝ) * L) := by
    dsimp [m]
    field_simp [hAR.ne', hL.ne']
  have hdegree :
      (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) =
        F 0 - (allowedPrimeCount S (Nat.sqrt X) : ℝ) := by
    rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS a haY hYXa,
      Nat.cast_sub hcountXa]
    simp [F, A]
  rw [hscale] at hsum
  calc
    (X : ℝ) / (16 * (a : ℝ) * Real.log (X : ℝ)) =
        (X : ℝ) / (16 * (A : ℝ) * L) := rfl
    _ ≤ F 0 - F A := hsum
    _ ≤ F 0 - (allowedPrimeCount S (Nat.sqrt X) : ℝ) := by
      have hFA : F A = (allowedPrimeCount S (X / (2 * A)) : ℝ) := by
        simp [F, two_mul]
      rw [hFA]
      exact sub_le_sub_left (by exact_mod_cast hboundary) _
    _ = (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := hdegree.symm

/-- Every canonical up-star degree ratio stays a fixed distance below one on
the logarithmic window. -/
theorem eventually_logarithmicWindow_canonicalUpDegreeRatio_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ q : CanonicalUpIndex S X (Nat.sqrt X) a,
          (largePrimeStarDegree S X (Nat.sqrt X)
              (canonicalUpTarget hS a q) : ℝ) /
              (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) ≤
            (199 / 200 : ℝ) := by
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [
      eventually_two_mul_center_mem_halfLogarithmicWindow hε,
      eventually_logarithmicWindow_allowedPrimeCount_interval_gap_ge S hS hhalf,
      eventually_logarithmicWindow_allowedPrimeCount_div_le_twelve_main S hε,
      eventually_logarithmicWindow_largePrimeStarDegree_ge S hS hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hhalf,
      eventually_ge_atTop 4]
      with X hdouble hinterval hupper hlower hcenter hX
  intro a ha q
  let A : ℕ := (a : ℕ)
  let Y : ℕ := Nat.sqrt X
  let M : ℝ := (X : ℝ) / ((A : ℝ) * Real.log (X : ℝ))
  let da : ℝ := largePrimeStarDegree S X Y a
  let t := canonicalUpTarget hS a q
  let dt : ℝ := largePrimeStarDegree S X Y t
  have hAPos : 0 < A := Vertex.coe_pos a
  have hAR : (0 : ℝ) < A := by exact_mod_cast hAPos
  have hL : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hM : 0 < M := by dsimp [M]; positivity
  have hdoubleWindow := hdouble A ha
  have htwoAY : 2 * A ≤ Y := hcenter (2 * A) hdoubleWindow
  have haY : A ≤ Y := by omega
  have hdaLower : M / 16 ≤ da := by
    convert hlower a ha using 1 <;> simp [M, da, Y, A] <;> ring
  have hdaPos : 0 < da := by
    have : 0 < M / 16 := by positivity
    exact this.trans_le hdaLower
  have hdaUpper : da ≤ 12 * M := by
    have hdegCount : da ≤ (allowedPrimeCount S (X / A) : ℝ) := by
      have hYXa : Y ≤ X / A := by
        apply (Nat.le_div_iff_mul_le hAPos).2
        exact (Nat.mul_le_mul_left Y haY).trans (Nat.sqrt_le X)
      change (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) ≤ _
      rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS a haY hYXa]
      exact_mod_cast Nat.sub_le _ _
    exact hdegCount.trans (by simpa [M] using hupper A ha)
  by_cases htY : (t : ℕ) ≤ Y
  · have hqdata := Finset.mem_filter.mp q.property
    have hqPrime : (q : ℕ).Prime := (Nat.mem_primesLE.mp hqdata.1).2
    have hqTwo : 2 ≤ (q : ℕ) := hqPrime.two_le
    have htCoe : (t : ℕ) = A * (q : ℕ) := canonicalUpTarget_coe hS a q
    have htwoAt : 2 * A ≤ (t : ℕ) := by rw [htCoe]; nlinarith
    have hYXa : Y ≤ X / A := by
      apply (Nat.le_div_iff_mul_le hAPos).2
      exact (Nat.mul_le_mul_left Y haY).trans (Nat.sqrt_le X)
    have hYXt : Y ≤ X / (t : ℕ) := by
      apply (Nat.le_div_iff_mul_le (Vertex.coe_pos t)).2
      exact (Nat.mul_le_mul_left Y htY).trans (Nat.sqrt_le X)
    have hgapCount := hinterval (2 * A) hdoubleWindow A hAPos (by omega)
    have hgapScale : M / 16 ≤
        (allowedPrimeCount S (X / A) : ℝ) -
          (allowedPrimeCount S (X / (2 * A)) : ℝ) := by
      have hscale :
          (((2 * A - A : ℕ) : ℝ) * (X : ℝ)) /
              (4 * ((2 * A : ℕ) : ℝ) ^ 2 * Real.log (X : ℝ)) = M / 16 := by
        rw [show 2 * A - A = A by omega]
        dsimp [M]
        push_cast
        field_simp [hAR.ne', hL.ne']
        norm_num
      rw [hscale] at hgapCount
      exact hgapCount
    have hquot : X / (t : ℕ) ≤ X / (2 * A) :=
      Nat.div_le_div_left htwoAt (by omega)
    have hmono := allowedPrimeCount_mono (S := S) hquot
    have hdiff : da - dt =
        (allowedPrimeCount S (X / A) : ℝ) -
          (allowedPrimeCount S (X / (t : ℕ)) : ℝ) := by
      simpa [da, dt, Y, A, t] using
        largePrimeStarDegree_sub_eq_allowedPrimeCount_gap
          hS a t haY htY hYXa hYXt
    have hgapStar : M / 16 ≤ da - dt := by
      rw [hdiff]
      exact hgapScale.trans
        (sub_le_sub_left (by exact_mod_cast hmono) _)
    have hratio : dt ≤ (199 / 200 : ℝ) * da := by
      have hsmall : da / 200 ≤ da - dt := by
        calc
          da / 200 ≤ (12 * M) / 200 := by gcongr
          _ ≤ M / 16 := by nlinarith [hM]
          _ ≤ da - dt := hgapStar
      linarith
    exact (div_le_iff₀ hdaPos).2 (by simpa [da, dt] using hratio)
  · have hiso := canonicalUpTarget_isIsolated_of_cutoff_lt haY
      (sqrtCutoff_condition X)
      (Nat.mem_primesLE.mp (Finset.mem_filter.mp q.property).1).2
      (Nat.mem_primesLE.mp (Finset.mem_filter.mp q.property).1).1
      (canonicalUpTarget_coe hS a q).symm (Nat.lt_of_not_ge htY)
    have hdt : largePrimeStarDegree S X Y t = 0 :=
      largePrimeStarDegree_eq_zero_iff.mpr hiso
    change (largePrimeStarDegree S X Y t : ℝ) / da ≤ (199 / 200 : ℝ)
    rw [hdt]
    norm_num

/-- Every canonical down-star degree ratio stays a fixed distance above one
on the logarithmic window. -/
theorem eventually_logarithmicWindow_canonicalDownDegreeRatio_ge
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ q : CanonicalDownIndex a,
          (201 / 200 : ℝ) ≤
            (largePrimeStarDegree S X (Nat.sqrt X)
                (canonicalDownTarget a q) : ℝ) /
              (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
  filter_upwards [
      eventually_logarithmicWindow_allowedPrimeCount_interval_gap_ge S hS hε,
      eventually_logarithmicWindow_allowedPrimeCount_div_le_twelve_main S hε,
      eventually_logarithmicWindow_largePrimeStarDegree_ge S hS hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε,
      eventually_ge_atTop 4]
      with X hinterval hupper hlower hcenter hX
  intro a ha q
  let A : ℕ := (a : ℕ)
  let Y : ℕ := Nat.sqrt X
  let M : ℝ := (X : ℝ) / ((A : ℝ) * Real.log (X : ℝ))
  let da : ℝ := largePrimeStarDegree S X Y a
  let t := canonicalDownTarget a q
  let dt : ℝ := largePrimeStarDegree S X Y t
  have hAPos : 0 < A := Vertex.coe_pos a
  have hAR : (0 : ℝ) < A := by exact_mod_cast hAPos
  have hL : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hM : 0 < M := by dsimp [M]; positivity
  have haY : A ≤ Y := hcenter A ha
  have htY : (t : ℕ) ≤ Y :=
    (Nat.div_le_self A (q : ℕ)).trans haY
  have hdaLower : M / 16 ≤ da := by
    convert hlower a ha using 1 <;> simp [M, da, Y, A] <;> ring
  have hdaPos : 0 < da := by
    have : 0 < M / 16 := by positivity
    exact this.trans_le hdaLower
  have hdaUpper : da ≤ 12 * M := by
    have hYXa : Y ≤ X / A := by
      apply (Nat.le_div_iff_mul_le hAPos).2
      exact (Nat.mul_le_mul_left Y haY).trans (Nat.sqrt_le X)
    have hdegCount : da ≤ (allowedPrimeCount S (X / A) : ℝ) := by
      change (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) ≤ _
      rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS a haY hYXa]
      exact_mod_cast Nat.sub_le _ _
    exact hdegCount.trans (by simpa [M] using hupper A ha)
  have hqPrime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.property
  have hqTwo : 2 ≤ (q : ℕ) := hqPrime.two_le
  have htMul : (t : ℕ) * (q : ℕ) = A := canonicalDownTarget_mul_coe a q
  have htwoT : 2 * (t : ℕ) ≤ A := by nlinarith
  have htPos : 0 < (t : ℕ) := Vertex.coe_pos t
  have hYXa : Y ≤ X / A := by
    apply (Nat.le_div_iff_mul_le hAPos).2
    exact (Nat.mul_le_mul_left Y haY).trans (Nat.sqrt_le X)
  have hYXt : Y ≤ X / (t : ℕ) := by
    apply (Nat.le_div_iff_mul_le htPos).2
    exact (Nat.mul_le_mul_left Y htY).trans (Nat.sqrt_le X)
  have hgapCount := hinterval A ha (t : ℕ) htPos (Nat.div_le_self _ _)
  have hgapScale : M / 8 ≤
      (allowedPrimeCount S (X / (t : ℕ)) : ℝ) -
        (allowedPrimeCount S (X / A) : ℝ) := by
    have hsub : (A : ℝ) / 2 ≤ ((A - (t : ℕ) : ℕ) : ℝ) := by
      have htLe : (t : ℕ) ≤ A := by omega
      have htwoTR : 2 * ((t : ℕ) : ℝ) ≤ (A : ℝ) := by
        exact_mod_cast htwoT
      rw [Nat.cast_sub htLe]
      push_cast
      nlinarith
    let K : ℝ := (X : ℝ) /
      (4 * (A : ℝ) ^ 2 * Real.log (X : ℝ))
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hmul := mul_le_mul_of_nonneg_right hsub hK
    have hscale : M / 8 = (A : ℝ) / 2 * K := by
      dsimp [M, K]
      field_simp [hAR.ne', hL.ne']
      ring
    have hmiddle : M / 8 ≤
        (((A - (t : ℕ) : ℕ) : ℝ) * (X : ℝ)) /
          (4 * (A : ℝ) ^ 2 * Real.log (X : ℝ)) := by
      rw [hscale]
      calc
        (A : ℝ) / 2 * K ≤ ((A - (t : ℕ) : ℕ) : ℝ) * K := hmul
        _ = (((A - (t : ℕ) : ℕ) : ℝ) * (X : ℝ)) /
            (4 * (A : ℝ) ^ 2 * Real.log (X : ℝ)) := by
              dsimp [K]
              ring
    exact hmiddle.trans hgapCount
  have hdiff : dt - da =
      (allowedPrimeCount S (X / (t : ℕ)) : ℝ) -
        (allowedPrimeCount S (X / A) : ℝ) := by
    simpa [da, dt, Y, A, t] using
      (largePrimeStarDegree_sub_eq_allowedPrimeCount_gap
        hS t a htY haY hYXt hYXa)
  have hgapStar : M / 8 ≤ dt - da := by simpa [hdiff] using hgapScale
  have hratio : (201 / 200 : ℝ) * da ≤ dt := by
    have hsmall : da / 200 ≤ dt - da := by
      calc
        da / 200 ≤ (12 * M) / 200 := by gcongr
        _ ≤ M / 8 := by nlinarith [hM]
        _ ≤ dt - da := hgapStar
    linarith
  exact (le_div_iff₀ hdaPos).2 (by simpa [da, dt] using hratio)

end

end PrimeStar
