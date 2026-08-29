import PrimeStar.LogarithmicWindowDegreeIsolation
import PrimeStar.StarInertia

/-!
# Quantitative star-frequency gaps on the logarithmic window

The adjacent PNT count gap is combined with a local degree upper bound.
This produces the `mu / a`-scale square-root gap used by the uniform
Feshbach argument in Section 9.
-/

namespace PrimeStar

open Filter Topology

noncomputable section

local instance logarithmicWindowLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

/-- A concrete square-root gap scale on the logarithmic centre window. -/
def logarithmicWindowDegreeGapScale (a X : ℕ) : ℝ :=
  (96 * ((a + 1 : ℕ) : ℝ))⁻¹ *
    Real.sqrt ((X : ℝ) / ((a : ℝ) * Real.log (X : ℝ)))

theorem logarithmicWindowDegreeGapScale_nonneg (a X : ℕ) :
    0 ≤ logarithmicWindowDegreeGapScale a X := by
  dsimp [logarithmicWindowDegreeGapScale]
  positivity

/-- Uniform separation of the moving positive star frequency from every
other nonempty star frequency.  The proof pays only the nearer adjacent
denominator interval, so it retains the manuscript's `mu / a` scale. -/
theorem eventually_logarithmicWindow_otherStarDegreeGap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ b : Vertex S X, (b : ℕ) ≤ Nat.sqrt X → b ≠ a →
          0 < largePrimeStarDegree S X (Nat.sqrt X) b →
          logarithmicWindowDegreeGapScale (a : ℕ) X ≤
            |Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) -
              Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ)| := by
  filter_upwards [
      eventually_logarithmicWindow_allowedPrimeCount_adjacent_gap_ge S hS hε,
      eventually_logarithmicWindow_allowedPrimeCount_div_le_twelve_main S hε,
      eventually_center_succ_le_natSqrt_on_logarithmicWindow hε,
      eventually_ge_atTop 4]
      with X hadj hupper hsucc hX
  intro a ha b hbY hba _hbd
  let m : ℕ := min (a : ℕ) (b : ℕ)
  let L : ℝ := Real.log (X : ℝ)
  let M₀ : ℝ := (X : ℝ) / ((m : ℝ) * L)
  let M : ℝ := 3 * M₀
  let k : ℝ := (12 * ((m + 1 : ℕ) : ℝ))⁻¹
  have haPos : 0 < (a : ℕ) := Vertex.coe_pos a
  have hbPos : 0 < (b : ℕ) := Vertex.coe_pos b
  have hmPos : 0 < m := by simp [m, haPos, hbPos]
  have hmLeA : m ≤ (a : ℕ) := Nat.min_le_left _ _
  have hmLeB : m ≤ (b : ℕ) := Nat.min_le_right _ _
  have hmWindow : InLogarithmicCenterWindow ε X m := by
    refine ⟨hmPos, ?_⟩
    exact (by exact_mod_cast hmLeA : (m : ℝ) ≤ (a : ℕ)).trans ha.2
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hXpos : (0 : ℝ) < X := by positivity
  have hM₀ : 0 ≤ M₀ := by
    dsimp [M₀]
    positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have haY : (a : ℕ) ≤ Nat.sqrt X :=
    (Nat.le_succ _).trans (hsucc (a : ℕ) ha)
  have hmY : m ≤ Nat.sqrt X := hmLeA.trans haY
  have hYX (v : Vertex S X) (hv : (v : ℕ) ≤ Nat.sqrt X) :
      Nat.sqrt X ≤ X / (v : ℕ) := by
    apply (Nat.le_div_iff_mul_le (Vertex.coe_pos v)).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) hv).trans (Nat.sqrt_le X)
  have hdegreeUpper (v : Vertex S X) (hvY : (v : ℕ) ≤ Nat.sqrt X)
      (hmv : m ≤ (v : ℕ)) :
      (largePrimeStarDegree S X (Nat.sqrt X) v : ℝ) ≤ 4 * M := by
    have hdegreeCount :
        (largePrimeStarDegree S X (Nat.sqrt X) v : ℝ) ≤
          (allowedPrimeCount S (X / (v : ℕ)) : ℝ) := by
      rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS v hvY (hYX v hvY)]
      exact_mod_cast Nat.sub_le _ _
    have hdiv : X / (v : ℕ) ≤ X / m :=
      Nat.div_le_div_left hmv hmPos
    have hmono : allowedPrimeCount S (X / (v : ℕ)) ≤
        allowedPrimeCount S (X / m) := allowedPrimeCount_mono hdiv
    have hmUpper := hupper m hmWindow
    calc
      (largePrimeStarDegree S X (Nat.sqrt X) v : ℝ) ≤
          (allowedPrimeCount S (X / (v : ℕ)) : ℝ) := hdegreeCount
      _ ≤ (allowedPrimeCount S (X / m) : ℝ) := by exact_mod_cast hmono
      _ ≤ 12 * ((X : ℝ) / ((m : ℝ) * L)) := by simpa [L] using hmUpper
      _ = 4 * M := by simp [M, M₀]; ring
  have hcountGap :
      (X : ℝ) /
            (4 * (m : ℝ) * ((m + 1 : ℕ) : ℝ) * L) ≤
        |(allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
          (allowedPrimeCount S (X / (b : ℕ)) : ℝ)| := by
    rcases lt_or_gt_of_ne (fun h ↦ hba (Subtype.ext (Fin.ext h.symm))) with hab | hbaNat
    · have hmEq : m = (a : ℕ) := Nat.min_eq_left (Nat.le_of_lt hab)
      have hsuccLe : (a : ℕ) + 1 ≤ (b : ℕ) := by omega
      have hdiv : X / (b : ℕ) ≤ X / ((a : ℕ) + 1) :=
        Nat.div_le_div_left hsuccLe (Nat.succ_pos (a : ℕ))
      have hmono := allowedPrimeCount_mono (S := S) hdiv
      rw [hmEq]
      calc
        (X : ℝ) /
              (4 * ((a : ℕ) : ℝ) * (((a : ℕ) + 1 : ℕ) : ℝ) * L) ≤
            (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
              (allowedPrimeCount S (X / ((a : ℕ) + 1)) : ℝ) := by
                simpa [L] using hadj (a : ℕ) ha
        _ ≤ (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
              (allowedPrimeCount S (X / (b : ℕ)) : ℝ) := by
                exact sub_le_sub_left (by exact_mod_cast hmono) _
        _ ≤ |_ - _| := le_abs_self _
    · have hmEq : m = (b : ℕ) := Nat.min_eq_right (Nat.le_of_lt hbaNat)
      have hbWindow : InLogarithmicCenterWindow ε X (b : ℕ) := by
        refine ⟨hbPos, ?_⟩
        exact (by exact_mod_cast hbaNat.le : ((b : ℕ) : ℝ) ≤ (a : ℕ)).trans ha.2
      have hsuccLe : (b : ℕ) + 1 ≤ (a : ℕ) := by omega
      have hdiv : X / (a : ℕ) ≤ X / ((b : ℕ) + 1) :=
        Nat.div_le_div_left hsuccLe (Nat.succ_pos (b : ℕ))
      have hmono := allowedPrimeCount_mono (S := S) hdiv
      rw [hmEq]
      calc
        (X : ℝ) /
              (4 * ((b : ℕ) : ℝ) * (((b : ℕ) + 1 : ℕ) : ℝ) * L) ≤
            (allowedPrimeCount S (X / (b : ℕ)) : ℝ) -
              (allowedPrimeCount S (X / ((b : ℕ) + 1)) : ℝ) := by
                simpa [L] using hadj (b : ℕ) hbWindow
        _ ≤ (allowedPrimeCount S (X / (b : ℕ)) : ℝ) -
              (allowedPrimeCount S (X / (a : ℕ)) : ℝ) := by
                exact sub_le_sub_left (by exact_mod_cast hmono) _
        _ ≤ |(allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
              (allowedPrimeCount S (X / (b : ℕ)) : ℝ)| := by
                rw [abs_sub_comm]
                exact le_abs_self _
  have hstarGap : k * M ≤
      |(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) -
        (largePrimeStarDegree S X (Nat.sqrt X) b : ℝ)| := by
    have hdiff := largePrimeStarDegree_sub_eq_allowedPrimeCount_gap
      hS a b haY hbY (hYX a haY) (hYX b hbY)
    rw [hdiff]
    have hscale : k * M =
        (X : ℝ) /
          (4 * (m : ℝ) * ((m + 1 : ℕ) : ℝ) * L) := by
      dsimp [k, M, M₀]
      have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
      have hm1R : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      field_simp [hmR.ne', hm1R.ne', hLpos.ne']
      ring
    rw [hscale]
    exact hcountGap
  have hroot := quarter_mul_sqrt_le_abs_sqrt_sub
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hk
    (hdegreeUpper a haY hmLeA) (hdegreeUpper b hbY hmLeB) hstarGap
  have hM₀a : 0 ≤ (X : ℝ) /
      ((a : ℝ) * Real.log (X : ℝ)) := by positivity
  have hM₀order : (X : ℝ) /
        ((a : ℝ) * Real.log (X : ℝ)) ≤ M₀ := by
    dsimp [M₀, L]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
    have hmaR : (m : ℝ) ≤ (a : ℕ) := by exact_mod_cast hmLeA
    exact div_le_div_of_nonneg_left hXpos.le (mul_pos hmR hLpos)
      (mul_le_mul_of_nonneg_right hmaR hLpos.le)
  have hsqrtOrder : Real.sqrt ((X : ℝ) /
        ((a : ℝ) * Real.log (X : ℝ))) ≤ Real.sqrt M := by
    apply Real.sqrt_le_sqrt
    exact hM₀order.trans (by dsimp [M]; nlinarith [hM₀])
  have hcoef : (96 * (((a : ℕ) + 1 : ℕ) : ℝ))⁻¹ ≤ k / 4 := by
    dsimp [k]
    have hm1R : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have ha1R : (0 : ℝ) < ((a : ℕ) + 1 : ℕ) := by positivity
    have hma1 : ((m + 1 : ℕ) : ℝ) ≤ (((a : ℕ) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hmLeA 1
    have hden : 48 * ((m + 1 : ℕ) : ℝ) ≤
        96 * (((a : ℕ) + 1 : ℕ) : ℝ) := by nlinarith
    calc
      (96 * (((a : ℕ) + 1 : ℕ) : ℝ))⁻¹ =
          1 / (96 * (((a : ℕ) + 1 : ℕ) : ℝ)) := by simp [one_div]
      _ ≤ 1 / (48 * ((m + 1 : ℕ) : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) hden
      _ = (12 * ((m + 1 : ℕ) : ℝ))⁻¹ / 4 := by
        field_simp [hm1R.ne']
        norm_num
  calc
    logarithmicWindowDegreeGapScale (a : ℕ) X =
        (96 * (((a : ℕ) + 1 : ℕ) : ℝ))⁻¹ *
          Real.sqrt ((X : ℝ) /
            ((a : ℝ) * Real.log (X : ℝ))) := rfl
    _ ≤ (k / 4) * Real.sqrt M :=
      mul_le_mul hcoef hsqrtOrder (Real.sqrt_nonneg _) (by positivity)
    _ ≤ _ := hroot

/-- The same moving scale separates the positive star frequency from zero. -/
theorem eventually_logarithmicWindow_zeroDegreeGap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        logarithmicWindowDegreeGapScale (a : ℕ) X ≤
          Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
  filter_upwards [
      eventually_logarithmicWindow_allowedPrimeCount_adjacent_gap_ge S hS hε,
      eventually_center_succ_le_natSqrt_on_logarithmicWindow hε,
      eventually_ge_atTop 4]
      with X hadj hsucc hX
  intro a ha
  let L : ℝ := Real.log (X : ℝ)
  let A : ℝ := (X : ℝ) / ((a : ℝ) * L)
  have haPos : 0 < (a : ℕ) := Vertex.coe_pos a
  have haR : (0 : ℝ) < (a : ℕ) := by exact_mod_cast haPos
  have ha1R : (0 : ℝ) < ((a : ℕ) + 1 : ℕ) := by positivity
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have haY : (a : ℕ) ≤ Nat.sqrt X :=
    (Nat.le_succ _).trans (hsucc (a : ℕ) ha)
  have hYXa : Nat.sqrt X ≤ X / (a : ℕ) := by
    apply (Nat.le_div_iff_mul_le haPos).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hYXsucc : Nat.sqrt X ≤ X / ((a : ℕ) + 1) := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos (a : ℕ))).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) (hsucc (a : ℕ) ha)).trans
      (Nat.sqrt_le X)
  have hboundaryMono := allowedPrimeCount_mono (S := S) hYXsucc
  have hdegreeLower : A / (4 * (((a : ℕ) + 1 : ℕ) : ℝ)) ≤
      (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
    have hadjX := hadj (a : ℕ) ha
    rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS a haY hYXa]
    rw [Nat.cast_sub (allowedPrimeCount_mono hYXa)]
    have hscale : A / (4 * (((a : ℕ) + 1 : ℕ) : ℝ)) =
        (X : ℝ) /
          (4 * ((a : ℕ) : ℝ) * (((a : ℕ) + 1 : ℕ) : ℝ) *
            Real.log (X : ℝ)) := by
      dsimp [A, L]
      field_simp [haR.ne', ha1R.ne', hLpos.ne']
    rw [hscale]
    calc
      _ ≤ (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
          (allowedPrimeCount S (X / ((a : ℕ) + 1)) : ℝ) := hadjX
      _ ≤ (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
          (allowedPrimeCount S (Nat.sqrt X) : ℝ) := by
            exact sub_le_sub_left (by exact_mod_cast hboundaryMono) _
  have hgammaSq : logarithmicWindowDegreeGapScale (a : ℕ) X ^ 2 ≤
      A / (4 * (((a : ℕ) + 1 : ℕ) : ℝ)) := by
    dsimp [logarithmicWindowDegreeGapScale]
    rw [mul_pow, Real.sq_sqrt]
    · dsimp [A, L]
      have ha1 : (1 : ℝ) ≤ (((a : ℕ) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le (a : ℕ)))
      have hcoef : (96 * (((a : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2 ≤
          (4 * (((a : ℕ) + 1 : ℕ) : ℝ))⁻¹ := by
        field_simp [ha1R.ne']
        nlinarith [ha1]
      calc
        (96 * (((a : ℕ) + 1 : ℕ) : ℝ))⁻¹ ^ 2 *
            ((X : ℝ) / (((a : ℕ) : ℝ) * Real.log (X : ℝ))) ≤
          (4 * (((a : ℕ) + 1 : ℕ) : ℝ))⁻¹ *
            ((X : ℝ) / (((a : ℕ) : ℝ) * Real.log (X : ℝ))) :=
              mul_le_mul_of_nonneg_right hcoef hA
        _ = (X : ℝ) / (((a : ℕ) : ℝ) * Real.log (X : ℝ)) /
            (4 * (((a : ℕ) + 1 : ℕ) : ℝ)) := by field_simp
    · exact hA
  have hsqrtSq :
      Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) ^ 2 =
        (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hgammaNonneg := logarithmicWindowDegreeGapScale_nonneg (a : ℕ) X
  have hsqrtNonneg := Real.sqrt_nonneg
    (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)
  nlinarith [hgammaSq, hdegreeLower, hsqrtSq]

/-- Ordered-spectrum form of the uniform large-prime isolation theorem. -/
theorem eventually_logarithmicWindow_orderedEigenvalue_separated
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∀ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
          (j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X)))),
          j ≠ largePrimePositiveStarOrderedIndex a
              (sqrtCutoff_condition X) haY hd →
          logarithmicWindowDegreeGapScale (a : ℕ) X ≤
            |(Matrix.isSymmetric_toEuclideanLin_iff.mpr
                ((largePrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix
                  (R := ℝ))).eigenvalues rfl j -
              Real.sqrt (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)| := by
  filter_upwards [eventually_logarithmicWindow_zeroDegreeGap S hS hε,
      eventually_logarithmicWindow_otherStarDegreeGap S hS hε]
      with X hzero hother
  intro a ha haY hd
  exact largePrime_orderedEigenvalue_separated_of_degreeGap
    a (sqrtCutoff_condition X) haY hd
      (logarithmicWindowDegreeGapScale (a : ℕ) X)
      (logarithmicWindowDegreeGapScale_nonneg (a : ℕ) X)
      (hzero a ha) (fun b hbY hba hbd ↦ hother a ha b hbY hba hbd)

end

end PrimeStar
