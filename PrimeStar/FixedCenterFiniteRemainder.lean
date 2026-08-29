import PrimeStar.FixedCenterRemainderAssembly

set_option maxHeartbeats 1000000

/-!
# Explicit fixed-centre finite remainder bound

This module substitutes the degree-gap, contraction, resolvent-norm, and
second-order displacement estimates into the canonical finite first-exit
remainder theorem.  Its conclusion is finite; the asymptotic evaluation of
the displayed scalar majorant is kept separate.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

local instance remainderScratchSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj := Classical.decRel _

local instance remainderScratchPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

/-- The actual finite correction differs from the squared prime-cover
eigenvalue by an explicit source-squared-over-gap majorant. -/
theorem primeCover_fixedCenter_finiteRemainder_bound
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {lam gamma eta : ℝ}
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
    (hnear : |lam - √(largePrimeStarDegree S X Y c : ℝ)| ≤ eta) :
    let mu := √(largePrimeStarDegree S X Y c : ℝ)
    |(lam ^ 2 - (allowedPrimeCount S (X / (c : ℕ)) : ℝ)) -
      finiteStarCorrection
        (Finset.univ : Finset (CanonicalUpIndex S X Y c))
        (Finset.univ : Finset (CanonicalDownIndex c))
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ) /
          mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ) /
          mu ^ 2)| ≤
      704 * |mu| * (eta ^ 4 / gamma ^ 3) +
        100 * (eta ^ 4 / gamma ^ 2) := by
  dsimp only
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let delta := lam - mu
  have hgamma : 0 < gamma := lt_of_lt_of_le (by positivity : 0 < 16 * eta) hlarge
  have hmu0 : 0 < mu := hgamma.trans_le hzeroGap
  have hnear' : |delta| ≤ eta := by simpa [delta, mu] using hnear
  obtain ⟨hgammaEta, hgapPos, hsmallBoundary, hsmallUW⟩ :=
    fixedCenter_scalar_contractions heta hlarge hzeroGap hnear'
  have hsharp := primeCover_fixedCenter_shift_le_ten
    hcut hc hd heta hlarge hzeroGap hdegree v hAv halpha hH hnear
  let shiftBound := 10 * (eta ^ 2 / gamma)
  have hshift0 : 0 ≤ shiftBound := by dsimp [shiftBound]; positivity
  have hshift : |lam - mu| ≤ shiftBound := by
    simpa [shiftBound, mu] using hsharp
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
  let b := normalizedPrimeStarFirstExit S X Y c
  let Rlam := primeStarInteriorResolventOfGap
    S X Y c lam gammaLam hgammaLam hgapLam
  let Rmu := primeStarInteriorResolventOfGap
    S X Y c mu gammaMu hgammaMu hgapMu
  let RU := firstExitLargePrimeResolventOfGap
    S X Y c mu gammaU hgammaU hgapU
  have hfinite := actualFinitePrimeStarRemainder_canonical_of_degreeGap
    v lam shiftBound gamma eta hS hlower hcut hc hd hgamma.le heta.le
    hgammaEta hzeroGap hdegree hAv halpha hH
    (by simpa [delta, mu] using hgapPos)
    (by simpa [delta, mu] using hsmallBoundary)
    hsmallUW hshift hshift0
  change |(lam ^ 2 - (allowedPrimeCount S (X / (c : ℕ)) : ℝ)) -
      finiteStarCorrection
        (Finset.univ : Finset (CanonicalUpIndex S X Y c))
        (Finset.univ : Finset (CanonicalDownIndex c))
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ) /
          mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ) /
          mu ^ 2)| ≤ _
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
  have hULower : gamma / 4 ≤ gammaU := by
    dsimp [gammaU]
    rw [hmin]
    nlinarith
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
  have hInvU : gammaU⁻¹ ≤ 4 / gamma := by
    have heq : (gamma / 4)⁻¹ = 4 / gamma := by field_simp
    rw [← heq]
    exact (inv_le_inv₀ hgammaU (by positivity)).2 hULower
  have hInvW : gammaW⁻¹ ≤ 4 / gamma := by simpa [gammaW] using hInvMu
  have hRlam : ‖Rlam b‖ ≤ 4 * eta / gamma := by
    calc
      ‖Rlam b‖ ≤ gammaLam⁻¹ * ‖b‖ := by
        simpa [Rlam, primeStarInteriorResolventOfGap] using
          norm_finiteResolventOfGap_apply_le
            (primeStarInteriorPrimeCoverOperator S X Y c) lam gammaLam
            hgammaLam hgapLam b
      _ ≤ (4 / gamma) * eta := by gcongr
      _ = 4 * eta / gamma := by ring
  have hRmu : ‖Rmu b‖ ≤ 4 * eta / gamma := by
    calc
      ‖Rmu b‖ ≤ gammaMu⁻¹ * ‖b‖ := by
        simpa [Rmu, primeStarInteriorResolventOfGap] using
          norm_finiteResolventOfGap_apply_le
            (primeStarInteriorPrimeCoverOperator S X Y c) mu gammaMu
            hgammaMu hgapMu b
      _ ≤ (4 / gamma) * eta := by gcongr
      _ = 4 * eta / gamma := by ring
  have hRU : ‖RU b‖ ≤ 4 * eta / gamma := by
    calc
      ‖RU b‖ ≤ gammaU⁻¹ * ‖b‖ := by
        simpa [RU] using norm_firstExitLargePrimeResolventOfGap_apply_le
          S X Y c mu gammaU hgammaU hgapU b
      _ ≤ (4 / gamma) * eta := by gcongr
      _ = 4 * eta / gamma := by ring
  have hterm1 :
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 ≤
        64 * (eta ^ 4 / gamma ^ 3) := by
    calc
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 ≤
          2 * ((2 / gamma) * eta * eta) * (4 * eta / gamma) ^ 2 := by gcongr
      _ = 64 * (eta ^ 4 / gamma ^ 3) := by field_simp; ring
  have hterm2 : |delta| * ‖Rlam b‖ * ‖Rmu b‖ ≤
      160 * (eta ^ 4 / gamma ^ 3) := by
    calc
      |delta| * ‖Rlam b‖ * ‖Rmu b‖ ≤
          (10 * (eta ^ 2 / gamma)) * (4 * eta / gamma) *
            (4 * eta / gamma) := by gcongr
      _ = 160 * (eta ^ 4 / gamma ^ 3) := by field_simp; ring
  have hterm3 : 2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2 ≤
      128 * (eta ^ 4 / gamma ^ 3) := by
    calc
      2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2 ≤
          2 * (eta * (4 / gamma) * eta) * (4 * eta / gamma) ^ 2 := by gcongr
      _ = 128 * (eta ^ 4 / gamma ^ 3) := by field_simp; ring
  have herr :
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
          |delta| * ‖Rlam b‖ * ‖Rmu b‖ +
          2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2 ≤
        352 * (eta ^ 4 / gamma ^ 3) := by linarith
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
    _ ≤ 2 * |mu| * (352 * (eta ^ 4 / gamma ^ 3)) +
          (10 * (eta ^ 2 / gamma)) ^ 2 := by
      dsimp [shiftBound]
      gcongr
    _ = 704 * |mu| * (eta ^ 4 / gamma ^ 3) +
          100 * (eta ^ 4 / gamma ^ 2) := by field_simp; ring

/-- Eventual fixed-centre assembly of the matched eigenpair and the explicit
finite remainder majorant at the literal square-root cutoff. -/
theorem eventually_fixedCenter_exists_finiteRemainder_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c : ℕ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ (a : Vertex S X), (a : ℕ) = c →
      ∃ (lam : ℝ) (v : EuclideanSpace ℝ (Vertex S X)),
        ‖v‖ = 1 ∧
        Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v ∧
        (⟪largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1, v⟫_ℝ ≠ 0) ∧
        |lam - √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)| ≤
          10 * (sqrtCutoffResidualScale X ^ 2 / fixedCenterGapScale c X) ∧
        Module.finrank ℝ
          (Module.End.eigenspace
            (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)) lam) = 1 ∧
        (let mu := √(largePrimeStarDegree S X (Nat.sqrt X) a : ℝ)
         |(lam ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)) -
            finiteStarCorrection
              (Finset.univ : Finset (CanonicalUpIndex S X (Nat.sqrt X) a))
              (Finset.univ : Finset (CanonicalDownIndex a))
              (fun q ↦
                (largePrimeStarDegree S X (Nat.sqrt X)
                    (canonicalUpTarget hS a q) : ℝ) / mu ^ 2)
              (fun q ↦
                (largePrimeStarDegree S X (Nat.sqrt X)
                    (canonicalDownTarget a q) : ℝ) / mu ^ 2)| ≤
            704 * |mu| *
                (sqrtCutoffResidualScale X ^ 4 /
                  fixedCenterGapScale c X ^ 3) +
              100 * (sqrtCutoffResidualScale X ^ 4 /
                fixedCenterGapScale c X ^ 2)) := by
  filter_upwards [eventually_fixedCenter_gap_residual_bundle S hS hc,
    eventually_fixedCenter_exists_matched_eigenpair_sharp S hS hc] with
      X hbundle hmatch
  intro a ha
  obtain ⟨haY, hd, hzero, hdegree, hH, heta, hlarge⟩ := hbundle a ha
  obtain ⟨lam, v, hv, hAv, halpha, hsharp, hsimple⟩ := hmatch a ha
  have hfinite := primeCover_fixedCenter_finiteRemainder_bound
    hS (Nat.sqrt_le X) (sqrtCutoff_condition X) haY hd heta hlarge
    hzero hdegree v hAv halpha hH
    (by
      exact (hsharp.trans (by
        have hgamma : 0 < fixedCenterGapScale c X := by linarith
        have hratio : 10 * (sqrtCutoffResidualScale X ^ 2 /
            fixedCenterGapScale c X) ≤ sqrtCutoffResidualScale X := by
          calc
            10 * (sqrtCutoffResidualScale X ^ 2 /
                fixedCenterGapScale c X) =
                (10 * sqrtCutoffResidualScale X ^ 2) /
                  fixedCenterGapScale c X := by ring
            _ ≤ sqrtCutoffResidualScale X :=
              (div_le_iff₀ hgamma).2 (by nlinarith)
        exact hratio)))
  refine ⟨lam, v, hv, hAv, halpha, hsharp, hsimple, ?_⟩
  simpa [ha] using hfinite

end

end PrimeStar
