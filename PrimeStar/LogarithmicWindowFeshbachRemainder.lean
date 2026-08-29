import PrimeStar.LogarithmicWindowSourceResolvent
import PrimeStar.LogarithmicWindowSpectral

/-!
# Source-weighted Feshbach remainder on the logarithmic window

This module transfers the explicit first-exit source bound through the two
resolvent replacements.  The key estimates retain the norm of the solved
source vector instead of replacing it by a global inverse norm.
-/

namespace PrimeStar

open Filter Topology
open scoped InnerProductSpace

noncomputable section

local instance logarithmicWindowRemainderSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj := Classical.decRel _

local instance logarithmicWindowRemainderPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

local instance logarithmicWindowRemainderLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

/-- Every fixed multiple of a fixed power of `log X` is eventually below
`sqrt X`.  This elementary comparison is used only to close the scalar
smallness conditions uniformly in the logarithmic centre window. -/
theorem eventually_const_mul_log_pow_le_sqrt
    (K : ℝ) (n : ℕ) (hK : 0 ≤ K) :
    ∀ᶠ X : ℕ in atTop,
      K * Real.log (X : ℝ) ^ n ≤ Real.sqrt (X : ℝ) := by
  have hlittle := (Real.isLittleO_pow_log_id_atTop (n := 2 * n)).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hcomp := hlittle.bound (show 0 < 1 / (K ^ 2 + 1) by positivity)
  filter_upwards [hcomp, eventually_ge_atTop 2] with X hX hXtwo
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs] at hX
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hx : 0 ≤ (X : ℝ) := by positivity
  rw [abs_of_nonneg (pow_nonneg hlog _), abs_of_nonneg hx] at hX
  have hpow : Real.log (X : ℝ) ^ (2 * n) =
      (Real.log (X : ℝ) ^ n) ^ 2 := by ring
  have hmain : (K * Real.log (X : ℝ) ^ n) ^ 2 ≤ (X : ℝ) := by
    rw [mul_pow, ← hpow]
    have hcoef : K ^ 2 ≤ K ^ 2 + 1 := by linarith
    have hmul : K ^ 2 * Real.log (X : ℝ) ^ (2 * n) ≤
        (K ^ 2 + 1) * Real.log (X : ℝ) ^ (2 * n) :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg hlog (2 * n))
    have hscaled : (K ^ 2 + 1) * Real.log (X : ℝ) ^ (2 * n) ≤ (X : ℝ) := by
      have hpos : 0 < K ^ 2 + 1 := by positivity
      calc
        (K ^ 2 + 1) * Real.log (X : ℝ) ^ (2 * n) ≤
            (K ^ 2 + 1) * ((1 / (K ^ 2 + 1)) * (X : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hX hpos.le
        _ = (X : ℝ) := by field_simp
    exact hmul.trans hscaled
  have hleft : 0 ≤ K * Real.log (X : ℝ) ^ n :=
    mul_nonneg hK (pow_nonneg hlog _)
  have hsqrt : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  apply (sq_le_sq₀ hleft hsqrt).mp
  simpa [Real.sq_sqrt hx] using hmain

/-- Squared residual scale at the literal square-root cutoff. -/
theorem eventually_sqrtCutoffResidualScale_sq_le :
    ∀ᶠ X : ℕ in atTop,
      sqrtCutoffResidualScale X ^ 2 ≤
        4 * sqrtCutoffResidualConstant ^ 2 *
          (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) := by
  have hratio : ∀ᶠ X : ℕ in atTop,
      (1 / 3 : ℝ) <
        Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) :=
    (log_natSqrt_div_log_tendsto_half.eventually
      (isOpen_Ioi.mem_nhds (by norm_num : (1 / 3 : ℝ) < 1 / 2)))
  filter_upwards [hratio, eventually_ge_atTop 4] with X hratioX hX
  let x : ℝ := X
  let y : ℝ := (Nat.sqrt X + 1 : ℕ)
  have hx : 1 < x := by dsimp [x]; exact_mod_cast (show 1 < X by omega)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hsqrtOne : (1 : ℝ) ≤ √x := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by dsimp [x]; exact_mod_cast (show 1 ≤ X by omega))
  have hy : 0 < y := by dsimp [y]; positivity
  have hyupper : y ≤ 2 * √x := by
    dsimp [x, y]
    push_cast
    have hsqrtNat := Real.nat_sqrt_le_real_sqrt (a := X)
    linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlog : Real.log x / 2 ≤ Real.log y := by
    have hsqrtPos : 0 < √x := Real.sqrt_pos.2 (by positivity)
    have hlt : √x < y := by
      dsimp [x, y]
      simpa [Nat.cast_add, Nat.cast_one] using
        (Real.real_sqrt_lt_nat_sqrt_succ (a := X))
    have hmono := Real.strictMonoOn_log.monotoneOn hsqrtPos hy hlt.le
    rw [Real.log_sqrt hx0] at hmono
    exact hmono
  have htuned := tunedSchurScale_sq_le_four_sqrt_div_log hx hy hyupper hlog
  calc
    sqrtCutoffResidualScale X ^ 2 =
        sqrtCutoffResidualConstant ^ 2 * tunedSchurScale y ^ 2 := by
      simp [sqrtCutoffResidualScale, y]
      ring
    _ ≤ sqrtCutoffResidualConstant ^ 2 *
        (4 * √x / Real.log x) := by gcongr
    _ = 4 * sqrtCutoffResidualConstant ^ 2 *
        (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) := by
      simp [x]
      ring

/-- The scalar smallness conditions needed by the source-weighted finite
Feshbach theorem hold uniformly throughout the logarithmic centre window. -/
theorem eventually_logarithmicWindow_feshbachScaleBundle
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InLogarithmicCenterWindow ε X a →
        let eta := sqrtCutoffResidualScale X
        let gamma := logarithmicWindowDegreeGapScale a X
        let R2 := 80000000 * ((a : ℝ) / (Nat.sqrt X : ℝ))
        0 < eta ∧
        16 * eta ≤ gamma ∧
        0 ≤ R2 ∧
        32 * R2 ≤ 1 / 2 ∧
        256 * (eta ^ 2 / gamma) * R2 ≤ 4 * eta * √R2 ∧
        eta ^ 2 * R2 ≤
          (640000000 * sqrtCutoffResidualConstant ^ 2) *
            ((a : ℝ) / Real.log (X : ℝ)) := by
  let K : ℝ := sqrtCutoffResidualConstant
  let Cgap : ℝ := 1024 * K ^ 2 * 96 ^ 2
  have hK : 0 < K := sqrtCutoffResidualConstant_pos
  have hCgap : 0 ≤ Cgap := by dsimp [Cgap]; positivity
  have hgapGrowth := eventually_const_mul_log_pow_le_sqrt Cgap 3 hCgap
  have hR2Growth := eventually_const_mul_log_pow_le_sqrt 10240000000 1 (by norm_num)
  have hcenterLog := eventually_mul_center_succ_lt_log_on_logarithmicWindow
    hε (by norm_num : (0 : ℝ) ≤ 1)
  filter_upwards [eventually_sqrtCutoffResidualScale_sq_le, hgapGrowth,
      hR2Growth, hcenterLog, eventually_ge_atTop 4]
      with X hetaSq hgapX hR2X hcenterLogX hX
  intro a ha
  dsimp only
  let L : ℝ := Real.log (X : ℝ)
  let Y : ℝ := Nat.sqrt X
  let eta : ℝ := sqrtCutoffResidualScale X
  let gamma : ℝ := logarithmicWindowDegreeGapScale a X
  let R2 : ℝ := 80000000 * ((a : ℝ) / Y)
  have haNat : 0 < a := ha.1
  have haR : (0 : ℝ) < a := by exact_mod_cast haNat
  have haOne : (1 : ℝ) ≤ a := by exact_mod_cast haNat
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hYnat : 1 ≤ Nat.sqrt X := Nat.le_sqrt'.2 (by omega)
  have hY : 0 < Y := by dsimp [Y]; exact_mod_cast (show 0 < Nat.sqrt X by omega)
  have hcenterLog' : (a : ℝ) + 1 < L := by
    simpa using hcenterLogX a ha
  have haL : (a : ℝ) ≤ L := by linarith
  have ha1L : ((a + 1 : ℕ) : ℝ) ≤ L := by
    push_cast
    exact hcenterLog'.le
  have hsqrtXY : Real.sqrt (X : ℝ) ≤ 2 * Y := by
    have hlt := Real.real_sqrt_lt_nat_sqrt_succ (a := X)
    have htwo : ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ 2 * Y := by
      dsimp [Y]
      push_cast
      exact_mod_cast (show Nat.sqrt X + 1 ≤ 2 * Nat.sqrt X by omega)
    have hlt' : Real.sqrt (X : ℝ) ≤ ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hlt.le
    exact hlt'.trans htwo
  have heta : 0 < eta := by
    dsimp [eta, sqrtCutoffResidualScale, tunedSchurScale]
    have hy : (1 : ℝ) < ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < Nat.sqrt X + 1 by omega)
    exact mul_pos sqrtCutoffResidualConstant_pos
      (div_pos (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_pos.2 (Real.log_pos hy)))
  have hM : 0 < (X : ℝ) / ((a : ℝ) * L) := by positivity
  have hgamma : 0 < gamma := by
    dsimp [gamma, logarithmicWindowDegreeGapScale]
    positivity
  have hetaSq' : eta ^ 2 ≤
      4 * K ^ 2 * (Real.sqrt (X : ℝ) / L) := by
    simpa [eta, K, L, mul_assoc] using hetaSq
  have hcenterCube : (a : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 ≤ L ^ 3 := by
    calc
      (a : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 ≤ L * L ^ 2 := by gcongr
      _ = L ^ 3 := by ring
  have hgapGrowth' :
      Cgap * ((a : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2) ≤
        Real.sqrt (X : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hcenterCube hCgap).trans (by
      simpa [Cgap, L] using hgapX)
  have hgammaSq : gamma ^ 2 =
      (X : ℝ) /
        (96 ^ 2 * ((a + 1 : ℕ) : ℝ) ^ 2 * (a : ℝ) * L) := by
    dsimp [gamma, logarithmicWindowDegreeGapScale]
    rw [mul_pow, Real.sq_sqrt hM.le]
    field_simp [haR.ne', hL.ne']
  have hlargeSq : (16 * eta) ^ 2 ≤ gamma ^ 2 := by
    rw [hgammaSq]
    have hden : 0 < 96 ^ 2 * ((a + 1 : ℕ) : ℝ) ^ 2 * (a : ℝ) * L := by
      positivity
    rw [le_div_iff₀ hden]
    calc
      (16 * eta) ^ 2 *
          (96 ^ 2 * ((a + 1 : ℕ) : ℝ) ^ 2 * (a : ℝ) * L) ≤
          (1024 * K ^ 2 * (Real.sqrt (X : ℝ) / L)) *
            (96 ^ 2 * ((a + 1 : ℕ) : ℝ) ^ 2 * (a : ℝ) * L) := by
              gcongr
              nlinarith
      _ = Cgap * ((a : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2) *
          Real.sqrt (X : ℝ) := by
            dsimp [Cgap]
            field_simp [hL.ne']
      _ ≤ Real.sqrt (X : ℝ) ^ 2 := by
        simpa [pow_two] using
          (mul_le_mul_of_nonneg_right hgapGrowth'
            (Real.sqrt_nonneg (X : ℝ)))
      _ = (X : ℝ) := Real.sq_sqrt (by positivity)
  have hlarge : 16 * eta ≤ gamma :=
    (sq_le_sq₀ (by positivity) hgamma.le).mp hlargeSq
  have hR2 : 0 ≤ R2 := by dsimp [R2]; positivity
  have hR2small : 32 * R2 ≤ 1 / 2 := by
    have hscaled : (10240000000 : ℝ) * (a : ℝ) ≤
        Real.sqrt (X : ℝ) := by
      exact (mul_le_mul_of_nonneg_left haL (by norm_num : (0 : ℝ) ≤ 10240000000)).trans
        (by simpa [L] using hR2X)
    have hscaledY : (5120000000 : ℝ) * (a : ℝ) ≤ Y := by
      nlinarith [hsqrtXY]
    calc
      32 * R2 = (2560000000 * (a : ℝ)) / Y := by dsimp [R2]; ring
      _ ≤ 1 / 2 := (div_le_iff₀ hY).2 (by nlinarith [hscaledY])
  have hR2quarter : 4 * R2 ≤ √R2 := by
    have hsqrtSq : (√R2) ^ 2 = R2 := Real.sq_sqrt hR2
    have hsqrtLe : √R2 ≤ 1 / 8 := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      rw [hsqrtSq]
      nlinarith
    nlinarith [Real.sqrt_nonneg R2, hsqrtSq]
  have hetaDiv : eta / gamma ≤ 1 / 16 := by
    rw [div_le_iff₀ hgamma]
    nlinarith
  have hAsmall : 256 * (eta ^ 2 / gamma) * R2 ≤ 4 * eta * √R2 := by
    calc
      256 * (eta ^ 2 / gamma) * R2 =
          256 * eta * (eta / gamma) * R2 := by ring
      _ ≤ 256 * eta * (1 / 16) * R2 := by gcongr
      _ = 4 * eta * (4 * R2) := by ring
      _ ≤ 4 * eta * √R2 := by gcongr
  have hetaR2 : eta ^ 2 * R2 ≤
      (640000000 * K ^ 2) * ((a : ℝ) / L) := by
    calc
      eta ^ 2 * R2 ≤
          (4 * K ^ 2 * (Real.sqrt (X : ℝ) / L)) *
            (80000000 * ((a : ℝ) / Y)) := by gcongr
      _ ≤ (4 * K ^ 2 * ((2 * Y) / L)) *
            (80000000 * ((a : ℝ) / Y)) := by gcongr
      _ = (640000000 * K ^ 2) * ((a : ℝ) / L) := by
        field_simp [hY.ne', hL.ne']
        norm_num
  exact ⟨heta, hlarge, hR2, hR2small, hAsmall, by simpa [eta, R2, K, L] using hetaR2⟩

/-- Degree upper bounds convert the moving star frequency and the explicit
source scale into the two scalar estimates used by the final majorant. -/
theorem eventually_logarithmicWindow_frequencySourceBounds
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        let mu := √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)
        let gamma := logarithmicWindowDegreeGapScale (a : ℕ) X
        let R2 := 80000000 * ((a : ℝ) / (Nat.sqrt X : ℝ))
        mu / gamma ≤ 768 * (a : ℝ) ∧
        mu ^ 2 * R2 ^ 2 ≤
          (48 * (80000000 : ℝ) ^ 2) *
            ((a : ℝ) / Real.log (X : ℝ)) := by
  filter_upwards [
      eventually_logarithmicWindow_allowedPrimeCount_div_le_twelve_main S hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε,
      eventually_ge_atTop 4]
      with X hcount hcenter hX
  intro a ha
  dsimp only
  let L : ℝ := Real.log (X : ℝ)
  let Y : ℝ := Nat.sqrt X
  let A : ℝ := (X : ℝ) / ((a : ℝ) * L)
  let mu : ℝ := √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)
  let gamma : ℝ := logarithmicWindowDegreeGapScale (a : ℕ) X
  let R2 : ℝ := 80000000 * ((a : ℝ) / Y)
  have haNat : 0 < (a : ℕ) := Vertex.coe_pos a
  have haR : (0 : ℝ) < (a : ℕ) := by exact_mod_cast haNat
  have haOne : (1 : ℝ) ≤ (a : ℕ) := by exact_mod_cast haNat
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hYnat : 1 ≤ Nat.sqrt X := Nat.le_sqrt'.2 (by omega)
  have hY : 0 < Y := by dsimp [Y]; exact_mod_cast (show 0 < Nat.sqrt X by omega)
  have hA : 0 < A := by dsimp [A]; positivity
  have haY : (a : ℕ) ≤ Nat.sqrt X := hcenter (a : ℕ) ha
  have hYX : Nat.sqrt X ≤ X / (a : ℕ) := by
    apply (Nat.le_div_iff_mul_le haNat).2
    exact (Nat.mul_le_mul_left (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hdegreeCount :
      (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) ≤
        (allowedPrimeCount S (X / (a : ℕ)) : ℝ) := by
    rw [largePrimeStarDegree_eq_allowedPrimeCount_sub hS a haY hYX]
    exact_mod_cast Nat.sub_le _ _
  have hdegreeUpper :
      (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) ≤ 12 * A := by
    exact hdegreeCount.trans (by simpa [A, L] using hcount (a : ℕ) ha)
  have hmuSq : mu ^ 2 =
      (largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) := by
    dsimp [mu]
    rw [Real.sq_sqrt]
    positivity
  have hmuUpper : mu ≤ 4 * √A := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [hmuSq, mul_pow, Real.sq_sqrt hA.le]
    nlinarith
  have hgamma : 0 < gamma := by
    dsimp [gamma, logarithmicWindowDegreeGapScale]
    positivity
  have hcompare : 4 * √A ≤ 768 * (a : ℝ) * gamma := by
    dsimp [gamma, logarithmicWindowDegreeGapScale]
    have ha1 : (0 : ℝ) < ((a : ℕ) + 1 : ℕ) := by positivity
    have hcoef : 4 ≤ 8 * (a : ℝ) / ((a : ℝ) + 1) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    rw [show √((X : ℝ) / ((a : ℝ) * Real.log (X : ℝ))) = √A by rfl]
    calc
      4 * √A ≤ (8 * (a : ℝ) / ((a : ℝ) + 1)) * √A := by gcongr
      _ = 768 * (a : ℝ) *
          ((96 * (((a : ℕ) + 1 : ℕ) : ℝ))⁻¹ * √A) := by
            push_cast
            field_simp [ha1.ne']
            ring
  have hmuGamma : mu / gamma ≤ 768 * (a : ℝ) := by
    rw [div_le_iff₀ hgamma]
    exact hmuUpper.trans hcompare
  have hXY : (X : ℝ) / Y ^ 2 ≤ 4 := by
    have hcut : X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := sqrtCutoff_condition X
    have hcutR : (X : ℝ) ≤ (2 * Y) ^ 2 := by
      have hYsucc : ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ 2 * Y := by
        dsimp [Y]
        push_cast
        exact_mod_cast (show Nat.sqrt X + 1 ≤ 2 * Nat.sqrt X by omega)
      have hcutCast : (X : ℝ) ≤ ((Nat.sqrt X + 1 : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast (show X ≤ (Nat.sqrt X + 1) ^ 2 by
          simpa [pow_two] using hcut.le)
      exact hcutCast.trans (by gcongr)
    rw [div_le_iff₀ (sq_pos_of_pos hY)]
    nlinarith
  have hmuR2 : mu ^ 2 * R2 ^ 2 ≤
      (48 * (80000000 : ℝ) ^ 2) * ((a : ℝ) / L) := by
    calc
      mu ^ 2 * R2 ^ 2 ≤
          (12 * A) * (80000000 * ((a : ℝ) / Y)) ^ 2 := by
            gcongr
            simpa [hmuSq] using hdegreeUpper
      _ = 12 * (80000000 : ℝ) ^ 2 * ((a : ℝ) / L) *
          ((X : ℝ) / Y ^ 2) := by
            dsimp [A]
            field_simp [haR.ne', hL.ne', hY.ne']
      _ ≤ 12 * (80000000 : ℝ) ^ 2 * ((a : ℝ) / L) * 4 := by
        exact mul_le_mul_of_nonneg_left hXY (by positivity)
      _ = (48 * (80000000 : ℝ) ^ 2) * ((a : ℝ) / L) := by ring
  exact ⟨by simpa [mu, gamma] using hmuGamma,
    by simpa [mu, R2, L] using hmuR2⟩

/-- The full interior resolvent at the reference energy is controlled by the
explicit first-exit resolvent on its source.  This is the vector form of the
`U/W` Feshbach contraction. -/
theorem norm_primeStarInteriorResolventOfGap_apply_le_four_firstExit
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (mu gammaI gammaU gammaW eta : ℝ) (hmu : mu ≠ 0)
    (hgammaI : 0 < gammaI) (hgammaU : 0 < gammaU)
    (hgammaW : 0 < gammaW) (heta : 0 ≤ eta)
    (hgapI : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaI * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hgapU : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaU * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖)
    (hgapW : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaW * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmall : gammaU⁻¹ * (eta * gammaW⁻¹ * eta) ≤ 1 / 2)
    (hWsmall : gammaW⁻¹ * eta ≤ 1)
    (b : EuclideanSpace ℝ (Vertex S X))
    (hbU : firstExitCompressionProjection S X Y c b = b) :
    ‖primeStarInteriorResolventOfGap S X Y c mu gammaI hgammaI hgapI b‖ ≤
      4 * ‖firstExitLargePrimeResolventOfGap
        S X Y c mu gammaU hgammaU hgapU b‖ := by
  let z := primeStarInteriorResolventOfGap
    S X Y c mu gammaI hgammaI hgapI b
  let xU := firstExitCompressionProjection S X Y c z
  let xW := firstExitComplementProjection S X Y c z
  let RU := firstExitLargePrimeResolventOfGap
    S X Y c mu gammaU hgammaU hgapU
  let RW := firstExitComplementResolventOfGap
    S X Y c mu gammaW hgammaW hgapW
  let K := firstExitFromComplementPrimeCoverOperator S X Y c
  let J := firstExitToComplementPrimeCoverOperator S X Y c
  let CW := firstExitComplementPrimeCoverOperator S X Y c
  have hident : xU = RU b + RU
      (feshbachEffectiveInteraction K RW J mu mu xU) :=
    primeStarInteriorResolvent_firstExitFeshbachIdentity
      hS hcut hc mu gammaI gammaU gammaW hmu hgammaI hgammaU hgammaW
        hgapI hgapU hgapW b hbU
  have hK : ∀ x, ‖K x‖ ≤ eta * ‖x‖ := by
    intro x
    exact norm_firstExitFromComplementPrimeCoverOperator_le
      hcut eta heta hH x
  have hJ : ∀ x, ‖J x‖ ≤ eta * ‖x‖ := by
    intro x
    exact norm_firstExitToComplementPrimeCoverOperator_le
      hcut eta heta hH x
  have hRW : ∀ x, ‖RW x‖ ≤ gammaW⁻¹ * ‖x‖ := by
    intro x
    exact norm_firstExitComplementResolventOfGap_apply_le
      S X Y c mu gammaW hgammaW hgapW x
  have hRU : ∀ x, ‖RU x‖ ≤ gammaU⁻¹ * ‖x‖ := by
    intro x
    exact norm_firstExitLargePrimeResolventOfGap_apply_le
      S X Y c mu gammaU hgammaU hgapU x
  have hT : ∀ x,
      ‖RU (feshbachEffectiveInteraction K RW J mu mu x)‖ ≤
        (gammaU⁻¹ * (eta * gammaW⁻¹ * eta)) * ‖x‖ := by
    intro x
    exact norm_resolvent_feshbachEffectiveInteraction_apply_le
      RU K RW J mu mu gammaU⁻¹ eta gammaW⁻¹ eta
        (inv_nonneg.mpr hgammaU.le) heta (inv_nonneg.mpr hgammaW.le) heta
        hRU hK hRW hJ x |>.trans_eq (by simp)
  have hxU : ‖xU‖ ≤ 2 * ‖RU b‖ := by
    have hmain : ‖xU‖ ≤ ‖RU b‖ +
        (gammaU⁻¹ * (eta * gammaW⁻¹ * eta)) * ‖xU‖ := by
      calc
        ‖xU‖ = ‖RU b + RU
            (feshbachEffectiveInteraction K RW J mu mu xU)‖ :=
          congrArg norm hident
        _ ≤ ‖RU b‖ + ‖RU
            (feshbachEffectiveInteraction K RW J mu mu xU)‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (le_refl _) (hT xU)
    nlinarith [norm_nonneg xU, norm_nonneg (RU b)]
  have hbB : primeStarBoundaryProjection S X Y c b = 0 := by
    rw [← hbU]
    exact primeStarBoundaryProjection_firstExit_eq_zero hcut hc b
  have hzInterior : primeStarInteriorProjection S X Y c z = z :=
    primeStarInteriorResolventOfGap_mem_interior
      S X Y c mu gammaI hmu hgammaI hgapI b hbB
  have hsolve : mu • z - primeStarInteriorPrimeCoverOperator S X Y c z = b :=
    primeStarInteriorResolventOfGap_apply_inverse
      S X Y c mu gammaI hgammaI hgapI b
  have hblocks := primeStarInteriorResolvent_blockEquations
    hS hcut hc mu z b hzInterior hbU hsolve
  have hWsolve : mu • xW - CW xW = J xU := hblocks.2
  have hxWEq : xW = RW (J xU) := by
    calc
      xW = RW (mu • xW - CW xW) := by
        exact (firstExitComplementResolventOfGap_shift_apply
          S X Y c mu gammaW hgammaW hgapW xW).symm
      _ = RW (J xU) := by rw [hWsolve]
  have hxW : ‖xW‖ ≤ ‖xU‖ := by
    calc
      ‖xW‖ = ‖RW (J xU)‖ := congrArg norm hxWEq
      _ ≤ gammaW⁻¹ * ‖J xU‖ := hRW _
      _ ≤ gammaW⁻¹ * (eta * ‖xU‖) := by gcongr; exact hJ _
      _ = (gammaW⁻¹ * eta) * ‖xU‖ := by ring
      _ ≤ ‖xU‖ := by
        nlinarith [norm_nonneg xU]
  have hzDecomp : z = xU + xW := by
    rw [← hzInterior]
    exact primeStarInteriorProjection_eq_firstExit_add_complement hcut hc z
  calc
    ‖primeStarInteriorResolventOfGap S X Y c mu gammaI hgammaI hgapI b‖ =
        ‖z‖ := rfl
    _ = ‖xU + xW‖ := congrArg norm hzDecomp
    _ ≤ ‖xU‖ + ‖xW‖ := norm_add_le _ _
    _ ≤ 2 * ‖xU‖ := by linarith
    _ ≤ 4 * ‖RU b‖ := by linarith

/-- The first resolvent identity transfers the source-weighted bound from the
reference energy to a nearby energy. -/
theorem norm_primeStarInteriorResolventOfGap_lam_le_two_mu
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (lam mu gammaLam gammaMu : ℝ)
    (hgammaLam : 0 < gammaLam) (hgammaMu : 0 < gammaMu)
    (hgapLam : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaLam * ‖x‖ ≤
        ‖lam • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hgapMu : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaMu * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hnear : |lam - mu| * gammaLam⁻¹ ≤ 1)
    (b : EuclideanSpace ℝ (Vertex S X)) :
    ‖primeStarInteriorResolventOfGap
        S X Y c lam gammaLam hgammaLam hgapLam b‖ ≤
      2 * ‖primeStarInteriorResolventOfGap
        S X Y c mu gammaMu hgammaMu hgapMu b‖ := by
  let C := primeStarInteriorPrimeCoverOperator S X Y c
  let Rlam := finiteResolventOfGap C lam gammaLam hgammaLam hgapLam
  let Rmu := finiteResolventOfGap C mu gammaMu hgammaMu hgapMu
  have hid := finiteResolventOfGap_sub_apply C lam mu gammaLam gammaMu
    hgammaLam hgammaMu hgapLam hgapMu b
  have hbound : ‖Rlam (Rmu b)‖ ≤ gammaLam⁻¹ * ‖Rmu b‖ :=
    norm_finiteResolventOfGap_apply_le C lam gammaLam hgammaLam hgapLam _
  have hmain : ‖Rlam b‖ ≤ ‖Rmu b‖ +
      (|lam - mu| * gammaLam⁻¹) * ‖Rmu b‖ := by
    calc
      ‖Rlam b‖ ≤ ‖Rmu b‖ + ‖Rlam b - Rmu b‖ := by
        have := norm_add_le (Rmu b) (Rlam b - Rmu b)
        simpa [add_sub_cancel] using this
      _ = ‖Rmu b‖ + ‖(mu - lam) • Rlam (Rmu b)‖ := by rw [hid]
      _ = ‖Rmu b‖ + |lam - mu| * ‖Rlam (Rmu b)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
      _ ≤ ‖Rmu b‖ + |lam - mu| *
          (gammaLam⁻¹ * ‖Rmu b‖) := by gcongr
      _ = ‖Rmu b‖ + (|lam - mu| * gammaLam⁻¹) * ‖Rmu b‖ := by ring
  change ‖Rlam b‖ ≤ 2 * ‖Rmu b‖
  nlinarith [norm_nonneg (Rmu b)]

set_option maxHeartbeats 1000000 in
/-- Finite source-weighted remainder estimate.  In contrast with the global
gap majorant, every occurrence of an interior resolvent is transferred back
to the explicit first-exit source vector. -/
theorem primeCover_finiteRemainder_bound_of_sourceWeightedFirstExit
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {lam gamma eta R2 : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hlower : Y * Y ≤ X) (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (heta : 0 < eta) (hlarge : 16 * eta ≤ gamma)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (v : EuclideanSpace ℝ (Vertex S X))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halpha : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤ eta * ‖x‖)
    (hnear : |lam - √(largePrimeStarDegree S X Y c : ℝ)| ≤ eta)
    (hR2 : 0 ≤ R2)
    (hsource : ∀ (gammaU : ℝ) (hgammaU : 0 < gammaU)
        (hgapU : ∀ x : EuclideanSpace ℝ (Vertex S X),
          gammaU * ‖x‖ ≤
            ‖√(largePrimeStarDegree S X Y c : ℝ) • x -
              firstExitLargePrimeCompressionOperator S X Y c x‖),
      ‖firstExitLargePrimeResolventOfGap S X Y c
          (√(largePrimeStarDegree S X Y c : ℝ)) gammaU hgammaU hgapU
          (normalizedPrimeStarFirstExit S X Y c)‖ ^ 2 ≤ R2)
    (hR2small : 32 * R2 ≤ 1 / 2)
    (hAsmall : 256 * (eta ^ 2 / gamma) * R2 ≤
      4 * eta * √R2) :
    let mu := √(largePrimeStarDegree S X Y c : ℝ)
    |(lam ^ 2 - (allowedPrimeCount S (X / (c : ℕ)) : ℝ)) -
      finiteStarCorrection
        (Finset.univ : Finset (CanonicalUpIndex S X Y c))
        (Finset.univ : Finset (CanonicalDownIndex c))
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ) /
          mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ) /
          mu ^ 2)| ≤
      2 * |mu| *
          (264 * (eta ^ 2 / gamma) * R2 +
            1280 * eta * √R2 * R2) +
        1600 * eta ^ 2 * R2 := by
  dsimp only
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let delta := lam - mu
  have hgamma : 0 < gamma := lt_of_lt_of_le (by positivity : 0 < 16 * eta) hlarge
  have hmu0 : 0 < mu := hgamma.trans_le hzeroGap
  have hnear' : |delta| ≤ eta := by simpa [delta, mu] using hnear
  obtain ⟨hgammaEta, hgapPos, hsmallBoundary, hsmallUW⟩ :=
    fixedCenter_scalar_contractions heta hlarge hzeroGap hnear'
  let gammaU := min (gamma - 2 * eta) |mu| / 2
  let gammaMu := gammaU - eta
  let gammaLam := gammaMu - |delta|
  let gammaW := gammaMu
  let gammaB := gamma - 2 * eta - |delta|
  have hgammaLam : 0 < gammaLam := by
    simpa [gammaLam, gammaMu, gammaU, delta, mu] using hgapPos
  have hgammaMu : 0 < gammaMu := lt_of_lt_of_le hgammaLam (by
    dsimp [gammaLam]
    linarith [abs_nonneg delta])
  have hgammaU : 0 < gammaU := lt_of_lt_of_le hgammaMu (by
    dsimp [gammaMu]
    linarith)
  have hgammaW : 0 < gammaW := by simpa [gammaW] using hgammaMu
  have hgammaB : 0 < gammaB := by
    dsimp [gammaB]
    nlinarith [abs_nonneg delta]
  have hgapMu : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaMu * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖ := by
    intro x
    simpa [gammaMu, gammaU, mu] using
      (primeStarInterior_gap_of_degreeGap c hcut hc hd gamma eta hgamma.le
        hgammaEta heta.le hzeroGap hdegree hH x)
  have hgapLam : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaLam * ‖x‖ ≤
        ‖lam • x - primeStarInteriorPrimeCoverOperator S X Y c x‖ := by
    intro x
    simpa [gammaLam, delta] using shifted_gap_of_gap
      (primeStarInteriorPrimeCoverOperator S X Y c) mu lam gammaMu hgapMu x
  have hgapU : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaU * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖ := by
    intro x
    simpa [gammaU, mu] using
      (firstExitLargePrimeCompression_gap_of_degreeGap c hcut hc hd gamma eta
        hgamma.le hgammaEta hzeroGap hdegree hH x)
  have hgapW : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaW * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖ := by
    intro x
    simpa [gammaW, gammaMu, gammaU, mu] using
      (firstExitComplement_gap_of_degreeGap c hcut hc hd gamma eta
        hgamma.le hgammaEta heta.le hzeroGap hdegree hH x)
  have hboundaryGap : gammaB *
        ‖normalizedPrimeStarBoundaryRemainder S X Y c v‖ ≤
      ‖lam • normalizedPrimeStarBoundaryRemainder S X Y c v -
        primeStarBoundaryPrimeCoverOperator S X Y c
          (normalizedPrimeStarBoundaryRemainder S X Y c v)‖ := by
    simpa [gammaB, delta, mu] using
      (primeStarBoundary_gap_of_degreeGap c hcut hc hd gamma eta lam hgamma.le
        hzeroGap hdegree hH v halpha)
  let b := normalizedPrimeStarFirstExit S X Y c
  let Rlam := primeStarInteriorResolventOfGap
    S X Y c lam gammaLam hgammaLam hgapLam
  let Rmu := primeStarInteriorResolventOfGap
    S X Y c mu gammaMu hgammaMu hgapMu
  let RU := firstExitLargePrimeResolventOfGap
    S X Y c mu gammaU hgammaU hgapU
  have hmin : min (gamma - 2 * eta) |mu| = gamma - 2 * eta := by
    rw [abs_of_pos hmu0, min_eq_left]
    linarith
  have hBLower : gamma / 2 ≤ gammaB := by
    dsimp [gammaB]
    nlinarith [abs_nonneg delta]
  have hMuLower : gamma / 4 ≤ gammaMu := by
    dsimp [gammaMu, gammaU]
    rw [hmin]
    nlinarith
  have hLamLower : gamma / 4 ≤ gammaLam := by
    dsimp [gammaLam, gammaMu, gammaU]
    rw [hmin]
    nlinarith [abs_nonneg delta]
  have hInvB : gammaB⁻¹ ≤ 2 / gamma := by
    have heq : (gamma / 2)⁻¹ = 2 / gamma := by field_simp
    rw [← heq]
    exact (inv_le_inv₀ hgammaB (half_pos hgamma)).2 hBLower
  have hInvMu : gammaMu⁻¹ ≤ 4 / gamma := by
    have heq : (gamma / 4)⁻¹ = 4 / gamma := by field_simp
    rw [← heq]
    exact (inv_le_inv₀ hgammaMu (by positivity)).2 hMuLower
  have hInvLam : gammaLam⁻¹ ≤ 4 / gamma := by
    have heq : (gamma / 4)⁻¹ = 4 / gamma := by field_simp
    rw [← heq]
    exact (inv_le_inv₀ hgammaLam (by positivity)).2 hLamLower
  have hInvW : gammaW⁻¹ ≤ 4 / gamma := by simpa [gammaW] using hInvMu
  have hWsmall : gammaW⁻¹ * eta ≤ 1 := by
    calc
      gammaW⁻¹ * eta ≤ (4 / gamma) * eta := by gcongr
      _ ≤ 1 := by
        have hfour : (4 * eta) / gamma ≤ 1 :=
          (div_le_iff₀ hgamma).2 (by nlinarith)
        calc
          (4 / gamma) * eta = (4 * eta) / gamma := by ring
          _ ≤ 1 := hfour
  have hLamNear : |lam - mu| * gammaLam⁻¹ ≤ 1 := by
    calc
      |lam - mu| * gammaLam⁻¹ ≤ eta * (4 / gamma) := by gcongr
      _ ≤ 1 := by
        have hfour : (4 * eta) / gamma ≤ 1 :=
          (div_le_iff₀ hgamma).2 (by nlinarith)
        calc
          eta * (4 / gamma) = (4 * eta) / gamma := by ring
          _ ≤ 1 := hfour
  have hRU2 : ‖RU b‖ ^ 2 ≤ R2 := by
    exact hsource gammaU hgammaU hgapU
  have hRUsqrt : ‖RU b‖ ≤ √R2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hR2]
    exact hRU2
  have hbU : firstExitCompressionProjection S X Y c b = b :=
    firstExitCompressionProjection_normalizedPrimeStarFirstExit hcut
  have hRmu : ‖Rmu b‖ ≤ 4 * √R2 := by
    calc
      ‖Rmu b‖ ≤ 4 * ‖RU b‖ := by
        exact norm_primeStarInteriorResolventOfGap_apply_le_four_firstExit
          hS hcut hc mu gammaMu gammaU gammaW eta hmu0.ne' hgammaMu
            hgammaU hgammaW heta.le hgapMu hgapU hgapW hH
            (by simpa [gammaU, gammaW, gammaMu, mu] using hsmallUW)
            hWsmall b hbU
      _ ≤ 4 * √R2 := by gcongr
  have hRlam : ‖Rlam b‖ ≤ 8 * √R2 := by
    calc
      ‖Rlam b‖ ≤ 2 * ‖Rmu b‖ := by
        exact norm_primeStarInteriorResolventOfGap_lam_le_two_mu
          lam mu gammaLam gammaMu hgammaLam hgammaMu hgapLam hgapMu hLamNear b
      _ ≤ 8 * √R2 := by nlinarith
  have hnormb : ‖b‖ ≤ eta := by
    dsimp [b, normalizedPrimeStarFirstExit]
    calc
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c 1)‖ ≤
          eta * ‖largePrimeNormalizedStarMode S X Y c 1‖ := hH _
      _ = eta := by rw [norm_largePrimeNormalizedStarMode hd, mul_one]
  have hreplace := primeCover_eigenvalue_interiorResolventReplacement
    hcut hc hd rfl v hAv halpha gammaB gammaLam gammaMu eta
      hgammaB hgammaLam hgammaMu heta.le hgapLam hgapMu hboundaryGap hH
      (by simpa [gammaB, gammaLam, gammaMu, gammaU, delta, mu] using hsmallBoundary)
  let q : ℝ := ⟪b, Rmu b⟫_ℝ
  change |delta - q| ≤
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
        |delta| * ‖Rlam b‖ * ‖Rmu b‖ at hreplace
  have hA : 2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 ≤
      256 * (eta ^ 2 / gamma) * R2 := by
    have hsqrtSq : (√R2) ^ 2 = R2 := Real.sq_sqrt hR2
    have hcoef : gammaB⁻¹ * eta * eta ≤ (2 / gamma) * eta * eta := by
      calc
        gammaB⁻¹ * eta * eta = gammaB⁻¹ * (eta * eta) := by ring
        _ ≤ (2 / gamma) * (eta * eta) :=
          mul_le_mul_of_nonneg_right hInvB (mul_nonneg heta.le heta.le)
        _ = (2 / gamma) * eta * eta := by ring
    have hnormSq : ‖Rlam b‖ ^ 2 ≤ (8 * √R2) ^ 2 := by
      exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hRlam
    calc
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 ≤
          2 * ((2 / gamma) * eta * eta) * ‖Rlam b‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcoef (by norm_num)) (sq_nonneg _)
      _ ≤ 2 * ((2 / gamma) * eta * eta) * (8 * √R2) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hnormSq (by positivity)
      _ = 256 * (eta ^ 2 / gamma) * R2 := by
        rw [mul_pow, hsqrtSq]
        field_simp
        ring
  have hB : ‖Rlam b‖ * ‖Rmu b‖ ≤ 32 * R2 := by
    have hsqrtSq : (√R2) ^ 2 = R2 := Real.sq_sqrt hR2
    calc
      ‖Rlam b‖ * ‖Rmu b‖ ≤ (8 * √R2) * (4 * √R2) := by
        exact mul_le_mul hRlam hRmu (norm_nonneg _) (by positivity)
      _ = 32 * (√R2) ^ 2 := by ring
      _ = 32 * R2 := by rw [hsqrtSq]
  have hq : |q| ≤ 4 * eta * √R2 := by
    dsimp [q]
    calc
      |⟪b, Rmu b⟫_ℝ| ≤ ‖b‖ * ‖Rmu b‖ := abs_real_inner_le_norm _ _
      _ ≤ eta * (4 * √R2) := by
        exact mul_le_mul hnormb hRmu (norm_nonneg _) heta.le
      _ = 4 * eta * √R2 := by ring
  have hshift : |delta| ≤ 40 * eta * √R2 := by
    let scale : ℝ := 4 * eta * √R2
    have hscale : 0 ≤ scale := by dsimp [scale]; positivity
    have hq' : |q| ≤ scale := by
      change |q| ≤ 4 * eta * √R2
      exact hq
    have hscale4 : scale ≤ 4 * scale := by
      calc
        scale = 1 * scale := by ring
        _ ≤ 4 * scale :=
          mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 4) hscale
    have hq4 : |q| ≤ 4 * scale :=
      hq'.trans hscale4
    have hreplace' : |delta - q| ≤
        2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
          |delta| * (‖Rlam b‖ * ‖Rmu b‖) := by
      simpa only [mul_assoc] using hreplace
    have hshift' := abs_le_ten_mul_scale_of_replacement
      (delta := delta) (q := q)
      (A := 2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2)
      (B := ‖Rlam b‖ * ‖Rmu b‖)
      (scale := scale)
      (hB.trans hR2small) (hA.trans hAsmall) hq4 hreplace'
    calc
      |delta| ≤ 10 * scale := hshift'
      _ = 40 * eta * √R2 := by dsimp [scale]; ring
  let shiftBound := 40 * eta * √R2
  have hshift0 : 0 ≤ shiftBound := by dsimp [shiftBound]; positivity
  have hfinite := actualFinitePrimeStarRemainder_canonical_of_degreeGap
    v lam shiftBound gamma eta hS hlower hcut hc hd hgamma.le heta.le
    hgammaEta hzeroGap hdegree hAv halpha hH
    (by simpa [delta, mu] using hgapPos)
    (by simpa [delta, mu] using hsmallBoundary)
    hsmallUW (by simpa [shiftBound, delta, mu] using hshift) hshift0
  change |(lam ^ 2 - (allowedPrimeCount S (X / (c : ℕ)) : ℝ)) -
      finiteStarCorrection
        (Finset.univ : Finset (CanonicalUpIndex S X Y c))
        (Finset.univ : Finset (CanonicalDownIndex c))
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ) /
          mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ) /
          mu ^ 2)| ≤
      2 * |mu| *
        (2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
          |delta| * ‖Rlam b‖ * ‖Rmu b‖ +
          2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2) + shiftBound ^ 2 at hfinite
  have hterm2 : |delta| * ‖Rlam b‖ * ‖Rmu b‖ ≤
      1280 * eta * √R2 * R2 := by
    calc
      |delta| * ‖Rlam b‖ * ‖Rmu b‖ =
          |delta| * (‖Rlam b‖ * ‖Rmu b‖) := by ring
      _ ≤ (40 * eta * √R2) * (32 * R2) := by gcongr
      _ = 1280 * eta * √R2 * R2 := by ring
  have hterm3 : 2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2 ≤
      8 * (eta ^ 2 / gamma) * R2 := by
    calc
      2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2 ≤
          2 * (eta * (4 / gamma) * eta) * R2 := by gcongr
      _ = 8 * (eta ^ 2 / gamma) * R2 := by field_simp; ring
  have herr :
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
          |delta| * ‖Rlam b‖ * ‖Rmu b‖ +
          2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2 ≤
        264 * (eta ^ 2 / gamma) * R2 +
          1280 * eta * √R2 * R2 := by linarith
  calc
    |(lam ^ 2 - (allowedPrimeCount S (X / (c : ℕ)) : ℝ)) -
        finiteStarCorrection
          (Finset.univ : Finset (CanonicalUpIndex S X Y c))
          (Finset.univ : Finset (CanonicalDownIndex c))
          (fun q ↦ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ) /
            mu ^ 2)
          (fun q ↦ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ) /
            mu ^ 2)| ≤
        2 * |mu| *
          (2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
            |delta| * ‖Rlam b‖ * ‖Rmu b‖ +
            2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2) + shiftBound ^ 2 := hfinite
    _ ≤ 2 * |mu| *
          (264 * (eta ^ 2 / gamma) * R2 +
            1280 * eta * √R2 * R2) +
        (40 * eta * √R2) ^ 2 := by
      dsimp [shiftBound]
      gcongr
    _ = 2 * |mu| *
          (264 * (eta ^ 2 / gamma) * R2 +
            1280 * eta * √R2 * R2) +
        1600 * eta ^ 2 * R2 := by
      have hsqrtSq : (√R2) ^ 2 = R2 := Real.sq_sqrt hR2
      nlinarith

/-- The explicit constant used when the source-weighted finite estimate is
specialized to the logarithmic centre window.  Its size is immaterial; what
matters is that it is independent of `X` and of the moving centre. -/
def logarithmicWindowFeshbachRemainderConstant : ℝ :=
  let K := sqrtCutoffResidualConstant
  let E := 640000000 * K ^ 2
  let D := 48 * (80000000 : ℝ) ^ 2
  528 * 768 * E + 1280 * (D + E) + 1600 * E

theorem logarithmicWindowFeshbachRemainderConstant_nonneg :
    0 ≤ logarithmicWindowFeshbachRemainderConstant := by
  dsimp [logarithmicWindowFeshbachRemainderConstant]
  positivity

/-- Pure scalar closeout of the source-weighted Feshbach estimate. -/
theorem sourceWeightedFeshbachMajorant_le_logarithmicWindow
    {mu eta gamma R2 a L : ℝ}
    (hmu : 0 ≤ mu) (_heta : 0 ≤ eta) (_hgamma : 0 < gamma)
    (hR2 : 0 ≤ R2) (ha : 1 ≤ a) (hL : 0 < L)
    (hmuGamma : mu / gamma ≤ 768 * a)
    (hetaR2 : eta ^ 2 * R2 ≤
      (640000000 * sqrtCutoffResidualConstant ^ 2) * (a / L))
    (hmuR2 : mu ^ 2 * R2 ^ 2 ≤
      (48 * (80000000 : ℝ) ^ 2) * (a / L)) :
    2 * |mu| *
          (264 * (eta ^ 2 / gamma) * R2 +
            1280 * eta * √R2 * R2) +
        1600 * eta ^ 2 * R2 ≤
      logarithmicWindowFeshbachRemainderConstant * (a ^ 2 / L) := by
  let E : ℝ := 640000000 * sqrtCutoffResidualConstant ^ 2
  let D : ℝ := 48 * (80000000 : ℝ) ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have haL : 0 ≤ a / L := by positivity
  have haSq : a / L ≤ a ^ 2 / L := by
    exact div_le_div_of_nonneg_right (by nlinarith) hL.le
  have htermOne :
      528 * mu * ((eta ^ 2 / gamma) * R2) ≤
        (528 * 768 * E) * (a ^ 2 / L) := by
    calc
      528 * mu * ((eta ^ 2 / gamma) * R2) =
          528 * (mu / gamma) * (eta ^ 2 * R2) := by ring
      _ ≤ 528 * (768 * a) * (E * (a / L)) := by gcongr
      _ = (528 * 768 * E) * (a ^ 2 / L) := by ring
  have hsqrtSq : (√R2) ^ 2 = R2 := Real.sq_sqrt hR2
  have hyoung :
      2 * (mu * R2) * (eta * √R2) ≤
        mu ^ 2 * R2 ^ 2 + eta ^ 2 * R2 := by
    nlinarith [sq_nonneg (mu * R2 - eta * √R2), hsqrtSq]
  have htermTwo :
      2560 * mu * eta * √R2 * R2 ≤
        1280 * (D + E) * (a ^ 2 / L) := by
    calc
      2560 * mu * eta * √R2 * R2 =
          1280 * (2 * (mu * R2) * (eta * √R2)) := by ring
      _ ≤ 1280 * (mu ^ 2 * R2 ^ 2 + eta ^ 2 * R2) := by gcongr
      _ ≤ 1280 * (D * (a / L) + E * (a / L)) := by gcongr
      _ = 1280 * (D + E) * (a / L) := by ring
      _ ≤ 1280 * (D + E) * (a ^ 2 / L) := by gcongr
  have htermThree :
      1600 * eta ^ 2 * R2 ≤ 1600 * E * (a ^ 2 / L) := by
    have hetaR2' : eta ^ 2 * R2 ≤ E * (a / L) := by
      simpa [E] using hetaR2
    calc
      1600 * eta ^ 2 * R2 ≤ 1600 * (E * (a / L)) := by nlinarith
      _ = (1600 * E) * (a / L) := by ring
      _ ≤ (1600 * E) * (a ^ 2 / L) :=
        mul_le_mul_of_nonneg_left haSq (mul_nonneg (by norm_num) hE)
      _ = 1600 * E * (a ^ 2 / L) := by ring
  rw [abs_of_nonneg hmu]
  dsimp [logarithmicWindowFeshbachRemainderConstant, E, D]
  nlinarith

/-- Uniform ordered Feshbach remainder on the full logarithmic centre
window.  This discharges the spectral input of Theorem 9.5 with one constant
independent of both `X` and the moving centre. -/
theorem logarithmicWindowOrderedRemainderBound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    LogarithmicWindowOrderedRemainderBound S ε
      logarithmicWindowFeshbachRemainderConstant := by
  filter_upwards [
      eventually_logarithmicWindow_feshbachScaleBundle hε,
      eventually_logarithmicWindow_frequencySourceBounds S hS hε,
      eventually_logarithmicWindow_firstExitResolvent_sq_le S hS hε,
      eventually_logarithmicWindow_zeroDegreeGap S hS hε,
      eventually_logarithmicWindow_otherStarDegreeGap S hS hε,
      eventually_logarithmicWindow_largePrimeStarDegree_ge S hS hε,
      eventually_center_le_natSqrt_on_logarithmicWindow hε,
      eventually_sqrtCutoff_smallPrime_apply_le_tuned,
      eventually_ge_atTop 4]
      with X hscales hfreq hsourceX hzeroX hdegreeX hdegreeLower
        hcenter hresidual hX
  intro a ha
  let Y : ℕ := Nat.sqrt X
  let mu : ℝ := √(largePrimeStarDegree S X Y a : ℝ)
  let gamma : ℝ := logarithmicWindowDegreeGapScale (a : ℕ) X
  let eta : ℝ := sqrtCutoffResidualScale X
  let R2 : ℝ := 80000000 * ((a : ℝ) / (Y : ℝ))
  have haY : (a : ℕ) ≤ Y := by
    simpa [Y] using hcenter (a : ℕ) ha
  have haPos : (0 : ℝ) < (a : ℕ) := by exact_mod_cast Vertex.coe_pos a
  have hL : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hd : 0 < largePrimeStarDegree S X Y a := by
    have hlower := hdegreeLower a ha
    have hpos : 0 < (X : ℝ) /
        ((16 * (a : ℝ)) * Real.log (X : ℝ)) := by positivity
    have : 0 < (largePrimeStarDegree S X Y a : ℝ) := by
      simpa [Y] using hpos.trans_le hlower
    exact_mod_cast this
  have hzero : gamma ≤ mu := by
    simpa [gamma, mu, Y] using hzeroX a ha
  have hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ a →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |mu - √(largePrimeStarDegree S X Y b : ℝ)| := by
    intro b hbY hba hbd
    simpa [gamma, mu, Y] using hdegreeX a ha b (by simpa [Y] using hbY) hba hbd
  have hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖ := by
    intro x
    simpa [Y, eta, sqrtCutoffResidualScale,
      sqrtCutoffResidualConstant] using hresidual S x
  obtain ⟨heta, hlarge, hR2, hR2small, hAsmall, hetaR2⟩ :=
    hscales (a : ℕ) ha
  have hgamma : 0 < gamma := lt_of_lt_of_le (by positivity : 0 < 16 * eta) hlarge
  have hsmall : 2 * eta < gamma := by nlinarith
  let L := Matrix.toEuclideanLin
    ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin
    ((smallPrimeGraph S X Y).adjMatrix ℝ)
  let hLs : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let i := largePrimePositiveStarOrderedIndex a
    (sqrtCutoff_condition X) haY hd
  let lam := (hLs.add hHs).eigenvalues rfl i
  let v := (hLs.add hHs).eigenvectorBasis rfl i
  obtain ⟨_hv, hAv, halpha, hnear, _hsimple⟩ :=
    primeCover_ordered_arithmeticStarEigenpair_withOverlap_of_degreeGap
      a (sqrtCutoff_condition X) haY hd gamma eta hgamma.le hzero hdegree hH hsmall
  have hsource : ∀ (gammaU : ℝ) (hgammaU : 0 < gammaU)
      (hgapU : ∀ x : EuclideanSpace ℝ (Vertex S X),
        gammaU * ‖x‖ ≤
          ‖mu • x - firstExitLargePrimeCompressionOperator S X Y a x‖),
      ‖firstExitLargePrimeResolventOfGap S X Y a mu gammaU hgammaU hgapU
          (normalizedPrimeStarFirstExit S X Y a)‖ ^ 2 ≤ R2 := by
    intro gammaU hgammaU hgapU
    simpa [mu, Y, R2] using hsourceX a ha gammaU hgammaU (by
      simpa [mu, Y] using hgapU)
  have hfinite := primeCover_finiteRemainder_bound_of_sourceWeightedFirstExit
    hS (Nat.sqrt_le X) (sqrtCutoff_condition X) haY hd heta hlarge hzero hdegree
      v hAv halpha hH hnear hR2 hsource hR2small hAsmall
  have hfreqBounds := hfreq a ha
  have hmuNonneg : 0 ≤ mu := by dsimp [mu]; positivity
  have hmajorant := sourceWeightedFeshbachMajorant_le_logarithmicWindow
    hmuNonneg heta.le hgamma hR2 (by exact_mod_cast (show 1 ≤ (a : ℕ) from
      Vertex.coe_pos a)) hL hfreqBounds.1 hetaR2 hfreqBounds.2
  refine ⟨haY, hd, ?_⟩
  have hcorrection := canonicalFiniteStarCorrection_eq_fixedCenterActualCorrection
    hS a haY
  dsimp only at hfinite
  change |(lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
      fixedCenterActualCorrection S (a : ℕ) X| ≤
        logarithmicWindowFeshbachRemainderConstant *
          ((a : ℝ) ^ 2 / Real.log (X : ℝ))
  rw [← hcorrection]
  exact hfinite.trans hmajorant

/-- Theorem 9.5 in its ordered, uniform `o(1)` form, with all spectral and
Feshbach hypotheses discharged. -/
theorem eventually_logarithmicWindow_ranked_actualCorrection_proved
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        ∃ (haY : (a : ℕ) ≤ Nat.sqrt X)
          (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a),
        (largePrimePositiveStarOrderedIndex a
            (sqrtCutoff_condition X) haY hd).1 + 1 =
            arithmeticCenterRank a ∧
          |(arithmeticStarFullEigenvalue a haY hd ^ 2 -
              (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            fixedCenterActualCorrection S (a : ℕ) X| < δ :=
  eventually_logarithmicWindow_ranked_actualCorrection_of_remainder
    S hS hε logarithmicWindowFeshbachRemainderConstant_nonneg
      (logarithmicWindowOrderedRemainderBound S hS hε)

end

end PrimeStar
