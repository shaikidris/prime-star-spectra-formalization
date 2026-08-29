import PrimeStar.FixedCenterIsolation

/-!
# Fixed-centre remainder assembly

This module packages the scalar smallness conditions used by the canonical
finite Feshbach remainder theorem.  It does not evaluate the finite correction
or state an asymptotic remainder.
-/

namespace PrimeStar

open Filter Real Topology
open scoped InnerProductSpace

noncomputable section

local instance fixedCenterRemainderSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance fixedCenterRemainderPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- A finite comparison between the tuned Schur scale at `y` and the main
square-root scale at `x`.  The final hypothesis is the only growth condition;
the remaining assumptions record the elementary square-root and logarithm
comparison used at the literal integer cutoff. -/
theorem sixteen_mul_tunedSchurScale_le_main_of_growth
    {K k x y : ℝ}
    (hK : 0 ≤ K) (hk : 0 < k) (hx : 1 < x) (hy : 0 < y)
    (hyupper : y ≤ 2 * √x)
    (hlog : Real.log x / 2 ≤ Real.log y)
    (hgrowth : 1024 * K ^ 2 ≤ k ^ 2 * √x) :
    16 * (K * tunedSchurScale y) ≤
      k * √(x / Real.log x) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogy : 0 < Real.log y := lt_of_lt_of_le (half_pos hlogx) hlog
  have hx0 : 0 ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  have hleft0 : 0 ≤ 16 * K * (√y / √(Real.log y)) := by positivity
  have hright0 : 0 ≤ k * √(x / Real.log x) := by positivity
  dsimp [tunedSchurScale]
  rw [← mul_assoc]
  apply (sq_le_sq₀ hleft0 hright0).mp
  have hsqrty : (√y) ^ 2 = y := Real.sq_sqrt hy.le
  have hsqrtlogy : (√(Real.log y)) ^ 2 = Real.log y := Real.sq_sqrt hlogy.le
  have hsqrtmain : (√(x / Real.log x)) ^ 2 = x / Real.log x :=
    Real.sq_sqrt (div_nonneg hx0 hlogx.le)
  have hratio : y / Real.log y ≤ 4 * √x / Real.log x := by
    rw [div_le_iff₀ hlogy]
    have hcoef : 0 ≤ 4 * √x / Real.log x := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog hcoef
    have heq : (4 * √x / Real.log x) * (Real.log x / 2) = 2 * √x := by
      field_simp
      ring
    rw [heq] at hmul
    exact hyupper.trans hmul
  calc
    (16 * K * (√y / √(Real.log y))) ^ 2 =
        256 * K ^ 2 * (y / Real.log y) := by
          rw [mul_pow, mul_pow, div_pow, hsqrty, hsqrtlogy]
          ring
    _ ≤ 256 * K ^ 2 * (4 * √x / Real.log x) := by gcongr
    _ = (1024 * K ^ 2) * √x / Real.log x := by ring
    _ ≤ (k ^ 2 * √x) * √x / Real.log x := by gcongr
    _ = k ^ 2 * ((√x) ^ 2 / Real.log x) := by ring
    _ = k ^ 2 * (x / Real.log x) := by rw [Real.sq_sqrt hx0]
    _ = (k * √(x / Real.log x)) ^ 2 := by rw [mul_pow, hsqrtmain]

/-- Squared form of the literal-cutoff tuned-scale comparison. -/
theorem tunedSchurScale_sq_le_four_sqrt_div_log
    {x y : ℝ} (hx : 1 < x) (hy : 0 < y)
    (hyupper : y ≤ 2 * √x)
    (hlog : Real.log x / 2 ≤ Real.log y) :
    tunedSchurScale y ^ 2 ≤ 4 * √x / Real.log x := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogy : 0 < Real.log y := lt_of_lt_of_le (half_pos hlogx) hlog
  have hcoef : 0 ≤ 4 * √x / Real.log x := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hcoef
  have heq : (4 * √x / Real.log x) * (Real.log x / 2) = 2 * √x := by
    field_simp
    ring
  rw [heq] at hmul
  have hratio : y / Real.log y ≤ 4 * √x / Real.log x := by
    rw [div_le_iff₀ hlogy]
    exact hyupper.trans hmul
  dsimp [tunedSchurScale]
  rw [div_pow, Real.sq_sqrt hy.le, Real.sq_sqrt hlogy.le]
  exact hratio

/-- The explicit constant in the literal square-root-cutoff residual bound. -/
def sqrtCutoffResidualConstant : ℝ :=
  12 * Real.log 4 + 2 / Real.log 2 + 16

theorem sqrtCutoffResidualConstant_pos : 0 < sqrtCutoffResidualConstant := by
  dsimp [sqrtCutoffResidualConstant]
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- The fixed-centre square-root degree-gap scale. -/
def fixedCenterGapScale (c X : ℕ) : ℝ :=
  fixedCenterDegreeGapConstant c *
    √((X : ℝ) / Real.log (X : ℝ))

/-- The literal-cutoff residual majorant used in the Feshbach assembly. -/
def sqrtCutoffResidualScale (X : ℕ) : ℝ :=
  sqrtCutoffResidualConstant *
    tunedSchurScale ((Nat.sqrt X + 1 : ℕ) : ℝ)

/-- At the literal square-root cutoff, sixteen times the available residual
majorant is eventually smaller than the fixed-centre arithmetic degree gap.
This is the scalar separation needed by matching and the finite Feshbach
contractions. -/
theorem eventually_sixteen_residual_le_fixedCenterDegreeGap
    (c : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      16 * (sqrtCutoffResidualConstant *
          tunedSchurScale ((Nat.sqrt X + 1 : ℕ) : ℝ)) ≤
        fixedCenterDegreeGapConstant c *
          √((X : ℝ) / Real.log (X : ℝ)) := by
  let K := sqrtCutoffResidualConstant
  let k := fixedCenterDegreeGapConstant c
  have hK : 0 ≤ K := sqrtCutoffResidualConstant_pos.le
  have hk : 0 < k := fixedCenterDegreeGapConstant_pos c
  have hsqrtTop : Tendsto (fun X : ℕ ↦ √(X : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowthEv :
      ∀ᶠ X : ℕ in atTop, 1024 * K ^ 2 ≤ k ^ 2 * √(X : ℝ) := by
    have hthreshold : ∀ᶠ X : ℕ in atTop,
        1024 * K ^ 2 / k ^ 2 ≤ √(X : ℝ) :=
      hsqrtTop.eventually (eventually_ge_atTop (1024 * K ^ 2 / k ^ 2))
    filter_upwards [hthreshold] with X hX
    calc
      1024 * K ^ 2 = k ^ 2 * (1024 * K ^ 2 / k ^ 2) := by
        field_simp
      _ ≤ k ^ 2 * √(X : ℝ) := by gcongr
  filter_upwards [eventually_ge_atTop 2, hgrowthEv] with X hX hgrowth
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hx0 : (0 : ℝ) ≤ X := by positivity
  have hsqrtOne : (1 : ℝ) ≤ √(X : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ X from (by omega)))
  have hy : (0 : ℝ) < ((Nat.sqrt X + 1 : ℕ) : ℝ) := by positivity
  have hyupper : ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ 2 * √(X : ℝ) := by
    push_cast
    have hsqrtNat := Real.nat_sqrt_le_real_sqrt (a := X)
    linarith
  have hlog : Real.log (X : ℝ) / 2 ≤
      Real.log ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
    have hsqrtPos : 0 < √(X : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hyPos : 0 < ((Nat.sqrt X + 1 : ℕ) : ℝ) := hy
    have hlt : √(X : ℝ) < ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (Real.real_sqrt_lt_nat_sqrt_succ (a := X))
    have hmono := Real.strictMonoOn_log.monotoneOn hsqrtPos hyPos hlt.le
    rw [Real.log_sqrt hx0] at hmono
    exact hmono
  simpa [K, k] using
    sixteen_mul_tunedSchurScale_le_main_of_growth hK hk hx hy hyupper hlog hgrowth

/-- Project-level fixed-centre input bundle at the literal square-root cutoff.
The quantitative PNT supplies the degree gaps, while the tuned weighted Schur
estimate supplies the residual norm.  Their scale comparison is included, so
downstream matching needs no separate asymptotic smallness premise. -/
theorem eventually_fixedCenter_gap_residual_bundle
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      (a : ℕ) ≤ Nat.sqrt X ∧
      0 < largePrimeStarDegree S X (Nat.sqrt X) a ∧
      fixedCenterGapScale c X ≤
        √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) ∧
      (∀ b : Vertex S X, (b : ℕ) ≤ Nat.sqrt X → b ≠ a →
        0 < largePrimeStarDegree S X (Nat.sqrt X) b →
        fixedCenterGapScale c X ≤
          |√(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ) -
            √(largePrimeStarDegree S X (Nat.sqrt X) b : ℝ)|) ∧
      (∀ x : EuclideanSpace ℝ (Vertex S X),
        ‖Matrix.toEuclideanLin
            ((smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ) x‖ ≤
          sqrtCutoffResidualScale X * ‖x‖) ∧
      0 < sqrtCutoffResidualScale X ∧
      16 * sqrtCutoffResidualScale X ≤ fixedCenterGapScale c X := by
  filter_upwards [eventually_fixedCenter_sqrtCutoff_degreeGap S hS hc,
    eventually_sqrtCutoff_smallPrime_apply_le_tuned,
    eventually_sixteen_residual_le_fixedCenterDegreeGap c,
    eventually_ge_atTop (max 2 (c ^ 2))] with X hdegree hresidual hsmall hX
  intro a ha
  have hcSq : c ^ 2 ≤ X := (le_max_right 2 (c ^ 2)).trans hX
  have hcY : c ≤ Nat.sqrt X := Nat.le_sqrt'.2 hcSq
  have haY : (a : ℕ) ≤ Nat.sqrt X := by simpa [ha] using hcY
  obtain ⟨hd, hzero, hother⟩ := hdegree a ha
  have heta : 0 < sqrtCutoffResidualScale X := by
    have htwo : 2 ≤ X := (le_max_left 2 (c ^ 2)).trans hX
    have hsqrtOne : 1 ≤ Nat.sqrt X := Nat.le_sqrt'.2 (by omega)
    have hy : (1 : ℝ) < ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < Nat.sqrt X + 1 by omega)
    dsimp [sqrtCutoffResidualScale, tunedSchurScale]
    exact mul_pos sqrtCutoffResidualConstant_pos
      (div_pos (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_pos.2 (Real.log_pos hy)))
  refine ⟨haY, hd, ?_, ?_, ?_, heta, ?_⟩
  · simpa [fixedCenterGapScale] using hzero
  · intro b hb hba hdb
    simpa [fixedCenterGapScale] using hother b hb hba hdb
  · intro x
    simpa [sqrtCutoffResidualScale, sqrtCutoffResidualConstant] using
      hresidual S x
  · simpa [fixedCenterGapScale, sqrtCutoffResidualScale] using hsmall

/-- The fixed-centre degree and residual bundle produces an actual simple
prime-cover eigenpair with nonzero overlap against the target star mode.  The
displacement recorded here is the crude matching bound; it is sharpened by
the subsequent Schur step. -/
theorem eventually_fixedCenter_exists_matched_eigenpair
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      ∃ (lam : ℝ) (v : EuclideanSpace ℝ (Vertex S X)),
        ‖v‖ = 1 ∧
        Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v ∧
        (⟪largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1, v⟫_ℝ ≠ 0) ∧
        |lam - √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)| ≤
          sqrtCutoffResidualScale X ∧
        Module.finrank ℝ
          (Module.End.eigenspace
            (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)) lam) = 1 := by
  filter_upwards [eventually_fixedCenter_gap_residual_bundle S hS hc] with X hbundle
  intro a ha
  obtain ⟨haY, hd, hzero, hdegree, hH, heta, hlarge⟩ := hbundle a ha
  have hgamma : 0 ≤ fixedCenterGapScale c X := by linarith
  have hsmall : 2 * sqrtCutoffResidualScale X < fixedCenterGapScale c X := by
    linarith
  exact primeCover_exists_simple_arithmeticStarEigenpair_withOverlap_of_degreeGap
    a (sqrtCutoff_condition X) haY hd
    (fixedCenterGapScale c X) (sqrtCutoffResidualScale X)
    hgamma hzero hdegree hH hsmall

/-- If the arithmetic star gap is at least sixteen times the residual norm,
then a matched eigenvalue lying within the residual norm automatically
satisfies the positivity and contraction hypotheses of the finite Feshbach
wrapper. -/
theorem fixedCenter_scalar_contractions
    {gamma eta mu delta : ℝ}
    (heta : 0 < eta)
    (hlarge : 16 * eta ≤ gamma)
    (hmu : gamma ≤ mu)
    (hdelta : |delta| ≤ eta) :
    0 ≤ gamma - 2 * eta ∧
    0 < min (gamma - 2 * eta) |mu| / 2 - eta - |delta| ∧
    (gamma - 2 * eta - |delta|)⁻¹ * eta *
        (min (gamma - 2 * eta) |mu| / 2 - eta - |delta|)⁻¹ * eta ≤ 1 / 2 ∧
    (min (gamma - 2 * eta) |mu| / 2)⁻¹ *
        (eta * (min (gamma - 2 * eta) |mu| / 2 - eta)⁻¹ * eta) ≤ 1 / 2 := by
  have hgamma : 0 < gamma := lt_of_lt_of_le (by positivity : 0 < 16 * eta) hlarge
  have hmu0 : 0 < mu := hgamma.trans_le hmu
  have habsmu : |mu| = mu := abs_of_pos hmu0
  have hleftmu : gamma - 2 * eta ≤ mu := by linarith
  have hmin : min (gamma - 2 * eta) |mu| = gamma - 2 * eta := by
    rw [habsmu, min_eq_left hleftmu]
  rw [hmin]
  have hge0 : 0 ≤ gamma - 2 * eta := by linarith
  have hgap : 0 < (gamma - 2 * eta) / 2 - eta - |delta| := by
    nlinarith [abs_nonneg delta]
  refine ⟨hge0, hgap, ?_, ?_⟩
  · have hden1 : 0 < gamma - 2 * eta - |delta| := by
      nlinarith [abs_nonneg delta]
    have hden2 : 0 < (gamma - 2 * eta) / 2 - eta - |delta| := hgap
    have hden1Lower : 13 * eta ≤ gamma - 2 * eta - |delta| := by
      nlinarith [abs_nonneg delta]
    have hden2Lower : 5 * eta ≤ (gamma - 2 * eta) / 2 - eta - |delta| := by
      nlinarith [abs_nonneg delta]
    have hinv1 : (gamma - 2 * eta - |delta|)⁻¹ ≤ (13 * eta)⁻¹ :=
      (inv_le_inv₀ hden1 (by positivity)).2 hden1Lower
    have hinv2 : ((gamma - 2 * eta) / 2 - eta - |delta|)⁻¹ ≤ (5 * eta)⁻¹ :=
      (inv_le_inv₀ hden2 (by positivity)).2 hden2Lower
    calc
      (gamma - 2 * eta - |delta|)⁻¹ * eta *
          ((gamma - 2 * eta) / 2 - eta - |delta|)⁻¹ * eta ≤
          (13 * eta)⁻¹ * eta * (5 * eta)⁻¹ * eta := by
            gcongr
      _ = 1 / 65 := by field_simp; ring
      _ ≤ 1 / 2 := by norm_num
  · have hden1 : 0 < (gamma - 2 * eta) / 2 := by linarith
    have hden2 : 0 < (gamma - 2 * eta) / 2 - eta := by linarith
    have hden1Lower : 7 * eta ≤ (gamma - 2 * eta) / 2 := by linarith
    have hden2Lower : 6 * eta ≤ (gamma - 2 * eta) / 2 - eta := by linarith
    have hinv1 : ((gamma - 2 * eta) / 2)⁻¹ ≤ (7 * eta)⁻¹ :=
      (inv_le_inv₀ hden1 (by positivity)).2 hden1Lower
    have hinv2 : ((gamma - 2 * eta) / 2 - eta)⁻¹ ≤ (6 * eta)⁻¹ :=
      (inv_le_inv₀ hden2 (by positivity)).2 hden2Lower
    calc
      ((gamma - 2 * eta) / 2)⁻¹ *
          (eta * ((gamma - 2 * eta) / 2 - eta)⁻¹ * eta) ≤
          (7 * eta)⁻¹ * (eta * (6 * eta)⁻¹ * eta) := by
            gcongr
      _ = 1 / 42 := by field_simp; ring
      _ ≤ 1 / 2 := by norm_num

/-- Scalar absorption used after the interior-resolvent replacement. -/
theorem abs_le_ten_mul_scale_of_replacement
    {delta q A B scale : ℝ}
    (hB : B ≤ 1 / 2)
    (hA : A ≤ scale) (hq : |q| ≤ 4 * scale)
    (hreplace : |delta - q| ≤ A + |delta| * B) :
    |delta| ≤ 10 * scale := by
  have htri : |delta| ≤ |delta - q| + |q| := by
    have hid : delta = (delta - q) + q := by ring
    calc
      |delta| = |(delta - q) + q| := congrArg abs hid
      _ ≤ |delta - q| + |q| := abs_add_le _ _
  have hmul : |delta| * B ≤ |delta| / 2 := by
    have habs : 0 ≤ |delta| := abs_nonneg _
    calc
      |delta| * B ≤ |delta| * (1 / 2) := mul_le_mul_of_nonneg_left hB habs
      _ = |delta| / 2 := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- Second-order displacement bound for an actual prime-cover eigenpair.  The
crude Weyl displacement is absorbed through the interior-resolvent identity,
giving the natural source-squared-over-gap scale. -/
theorem primeCover_fixedCenter_shift_le_ten
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {lam gamma eta : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
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
    (hnear : |lam - √(largePrimeStarDegree S X Y c : ℝ)| ≤ eta) :
    |lam - √(largePrimeStarDegree S X Y c : ℝ)| ≤
      10 * (eta ^ 2 / gamma) := by
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let delta := lam - mu
  have hgamma : 0 < gamma := lt_of_lt_of_le (by positivity : 0 < 16 * eta) hlarge
  have hmu0 : 0 < mu := hgamma.trans_le hzeroGap
  have hnear' : |delta| ≤ eta := by simpa [delta, mu] using hnear
  have hscalar := fixedCenter_scalar_contractions heta hlarge hzeroGap hnear'
  obtain ⟨hgammaEta, hgapPos, hsmallBoundary, _hsmallUW⟩ := hscalar
  let gammaU := min (gamma - 2 * eta) |mu| / 2
  let gammaMu := gammaU - eta
  let gammaLam := gammaMu - |delta|
  let gammaB := gamma - 2 * eta - |delta|
  have hgammaLam : 0 < gammaLam := by
    simpa [gammaLam, gammaMu, gammaU, delta, mu] using hgapPos
  have hgammaMu : 0 < gammaMu := lt_of_lt_of_le hgammaLam (by
    dsimp [gammaLam]
    linarith [abs_nonneg delta])
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
  have hreplace := primeCover_eigenvalue_interiorResolventReplacement
    hcut hc hd rfl v hAv halpha
    gammaB gammaLam gammaMu eta hgammaB hgammaLam hgammaMu heta.le
    hgapLam hgapMu hboundaryGap hH
    (by simpa [gammaB, gammaLam, gammaMu, gammaU, delta, mu] using hsmallBoundary)
  change |delta| ≤ 10 * (eta ^ 2 / gamma)
  change |delta - ⟪b, Rmu b⟫_ℝ| ≤
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
        |delta| * ‖Rlam b‖ * ‖Rmu b‖ at hreplace
  have hnormb : ‖b‖ ≤ eta := by
    dsimp [b, normalizedPrimeStarFirstExit]
    calc
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
          (largePrimeNormalizedStarMode S X Y c 1)‖ ≤
          eta * ‖largePrimeNormalizedStarMode S X Y c 1‖ := hH _
      _ = eta := by rw [norm_largePrimeNormalizedStarMode hd, mul_one]
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
  have hRlamRaw : ‖Rlam b‖ ≤ gammaLam⁻¹ * ‖b‖ := by
    simpa [Rlam, primeStarInteriorResolventOfGap] using
      norm_finiteResolventOfGap_apply_le
        (primeStarInteriorPrimeCoverOperator S X Y c) lam gammaLam
        hgammaLam hgapLam b
  have hRmuRaw : ‖Rmu b‖ ≤ gammaMu⁻¹ * ‖b‖ := by
    simpa [Rmu, primeStarInteriorResolventOfGap] using
      norm_finiteResolventOfGap_apply_le
        (primeStarInteriorPrimeCoverOperator S X Y c) mu gammaMu
        hgammaMu hgapMu b
  have hRlam : ‖Rlam b‖ ≤ 4 * eta / gamma := by
    calc
      ‖Rlam b‖ ≤ gammaLam⁻¹ * ‖b‖ := hRlamRaw
      _ ≤ (4 / gamma) * eta := by gcongr
      _ = 4 * eta / gamma := by ring
  have hRmu : ‖Rmu b‖ ≤ 4 * eta / gamma := by
    calc
      ‖Rmu b‖ ≤ gammaMu⁻¹ * ‖b‖ := hRmuRaw
      _ ≤ (4 / gamma) * eta := by gcongr
      _ = 4 * eta / gamma := by ring
  let scale := eta ^ 2 / gamma
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have ht : 0 ≤ eta / gamma := by positivity
  have htUpper : eta / gamma ≤ 1 / 16 := by
    rw [div_le_iff₀ hgamma]
    nlinarith
  let q := ⟪b, Rmu b⟫_ℝ
  let A := 2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2
  let B := ‖Rlam b‖ * ‖Rmu b‖
  have hB : B ≤ 1 / 2 := by
    dsimp [B]
    calc
      ‖Rlam b‖ * ‖Rmu b‖ ≤ (4 * eta / gamma) * (4 * eta / gamma) := by
        gcongr
      _ = 16 * (eta / gamma) ^ 2 := by ring
      _ ≤ 1 / 2 := by nlinarith [sq_nonneg (eta / gamma - 1 / 16)]
  have hq : |q| ≤ 4 * scale := by
    dsimp [q, scale]
    calc
      |⟪b, Rmu b⟫_ℝ| ≤ ‖b‖ * ‖Rmu b‖ := abs_real_inner_le_norm _ _
      _ ≤ eta * (4 * eta / gamma) := by gcongr
      _ = 4 * (eta ^ 2 / gamma) := by ring
  have hA : A ≤ scale := by
    dsimp [A, scale]
    calc
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 ≤
          2 * ((2 / gamma) * eta * eta) * (4 * eta / gamma) ^ 2 := by
            gcongr
      _ = 64 * (eta / gamma) ^ 2 * (eta ^ 2 / gamma) := by field_simp; ring
      _ ≤ eta ^ 2 / gamma := by
        have hfactor : 64 * (eta / gamma) ^ 2 ≤ 1 := by
          nlinarith [sq_nonneg (eta / gamma - 1 / 16)]
        exact mul_le_of_le_one_left hscale hfactor
  apply abs_le_ten_mul_scale_of_replacement hB hA hq
  simpa [q, A, B, mul_assoc] using hreplace

/-- Eventual fixed-centre eigenpair with the second-order displacement scale
already substituted. -/
theorem eventually_fixedCenter_exists_matched_eigenpair_sharp
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      ∃ (lam : ℝ) (v : EuclideanSpace ℝ (Vertex S X)),
        ‖v‖ = 1 ∧
        Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v ∧
        (⟪largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1, v⟫_ℝ ≠ 0) ∧
        |lam - √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)| ≤
          10 * (sqrtCutoffResidualScale X ^ 2 / fixedCenterGapScale c X) ∧
        Module.finrank ℝ
          (Module.End.eigenspace
            (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)) lam) = 1 := by
  filter_upwards [eventually_fixedCenter_gap_residual_bundle S hS hc,
    eventually_fixedCenter_exists_matched_eigenpair S hS hc] with X hbundle hmatch
  intro a ha
  obtain ⟨haY, hd, hzero, hdegree, hH, heta, hlarge⟩ := hbundle a ha
  obtain ⟨lam, v, hv, hAv, halpha, hnear, hsimple⟩ := hmatch a ha
  have hsharp := primeCover_fixedCenter_shift_le_ten
    (sqrtCutoff_condition X) haY hd heta hlarge hzero hdegree
    v hAv halpha hH hnear
  exact ⟨lam, v, hv, hAv, halpha, hsharp, hsimple⟩

end

end PrimeStar
