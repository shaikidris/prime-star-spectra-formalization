import PrimeStar.Main

namespace PrimeStar

open Filter Topology
open scoped BigOperators Classical InnerProductSpace

noncomputable def palomarAllowedPrimeInvSubOneSum
    (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ p ∉ S), ((p : ℝ) - 1)⁻¹

def palomarArithmeticRankIndex {S : Finset ℕ} {X : ℕ} (a : Vertex S X) :
    Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))) := by
  let T := Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (a : ℕ)
  refine ⟨T.card, ?_⟩
  have hproper : T ⊂ (Finset.univ : Finset (Vertex S X)) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, ?_⟩
    intro hEq
    have ha : a ∈ T := by simp [hEq]
    simp [T] at ha
  simpa using Finset.card_lt_card hproper

noncomputable instance palomarPrimeCoverDecidableRel (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

noncomputable def palomarAdjacency (S : Finset ℕ) (X : ℕ) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ] EuclideanSpace ℝ (Vertex S X) :=
  Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)

theorem palomarAdjacency_isSymmetric (S : Finset ℕ) (X : ℕ) :
    (palomarAdjacency S X).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))

noncomputable def palomarLambdaAtArithmeticRank
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X) : ℝ :=
  (palomarAdjacency_isSymmetric S X).eigenvalues rfl
    (palomarArithmeticRankIndex a)

def palomarRootVertex (X : ℕ) (hX : 1 ≤ X) : Vertex ∅ X :=
  ⟨⟨1, Nat.lt_succ_iff.mpr hX⟩, by simp⟩

@[simp]
theorem palomarRootVertex_coe (X : ℕ) (hX : 1 ≤ X) :
    (palomarRootVertex X hX : ℕ) = 1 := rfl

noncomputable def palomarLargestEigenvalue (X : ℕ) (hX : 1 ≤ X) : ℝ :=
  palomarLambdaAtArithmeticRank (palomarRootVertex X hX)

noncomputable def palomarFirstExitCorrection
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) : ℝ :=
  fixedCenterActualCorrection S (a : ℕ) X

noncomputable def palomarApproximateFrequency
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) : ℝ :=
  logarithmicWindowApproximateFrequency S X a

noncomputable def palomarPrimeStarCentre
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) :
    EuclideanSpace ℂ (Vertex S X) :=
  normalizedPairCentre
    (complexifyEuclidean
      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
    (complexifyEuclidean
      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1)))

noncomputable def palomarPrimeStarShell
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) :
    EuclideanSpace ℂ (Vertex S X) :=
  normalizedPairShell
    (complexifyEuclidean
      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a 1))
    (complexifyEuclidean
      (largePrimeNormalizedStarMode S X (Nat.sqrt X) a (-1)))

noncomputable def palomarPrimeCoverEvolution
    (S : Finset ℕ) (X : ℕ) (t : ℝ) :
    EuclideanSpace ℂ (Vertex S X) →L[ℂ]
      EuclideanSpace ℂ (Vertex S X) :=
  primeCoverAdjacencyEvolution S X t

noncomputable def palomarLocalizationBound (a X : ℕ) : ℝ :=
  logarithmicWindowLocalizationBound a X

noncomputable def palomarFeshbachRemainderConstant : ℝ :=
  logarithmicWindowFeshbachRemainderConstant

private theorem palomarArithmeticRankIndex_eq_largePrimeIndex
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (haY : (a : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
    (hrank :
      (largePrimePositiveStarOrderedIndex a
          (sqrtCutoff_condition X) haY hd).1 + 1 = arithmeticCenterRank a) :
    palomarArithmeticRankIndex a =
      largePrimePositiveStarOrderedIndex a
        (sqrtCutoff_condition X) haY hd := by
  apply Fin.ext
  change (Finset.univ.filter fun b : Vertex S X ↦
      (b : ℕ) < (a : ℕ)).card = _
  change _ + 1 =
    (Finset.univ.filter fun b : Vertex S X ↦
      (b : ℕ) < (a : ℕ)).card + 1 at hrank
  omega

private theorem palomarLambdaAtArithmeticRank_eq
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (haY : (a : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a)
    (hrank :
      (largePrimePositiveStarOrderedIndex a
          (sqrtCutoff_condition X) haY hd).1 + 1 = arithmeticCenterRank a) :
    palomarLambdaAtArithmeticRank a = arithmeticStarFullEigenvalue a haY hd := by
  rw [palomarLambdaAtArithmeticRank,
    palomarArithmeticRankIndex_eq_largePrimeIndex a haY hd hrank]
  let L := Matrix.toEuclideanLin
    ((largePrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin
    ((smallPrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
  let hH : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((smallPrimeGraph S X (Nat.sqrt X)).isHermitian_adjMatrix (R := ℝ))
  let hA : (palomarAdjacency S X).IsSymmetric := palomarAdjacency_isSymmetric S X
  have hsplit : palomarAdjacency S X = L + H := by
    simpa [palomarAdjacency, L, H] using
      primeCover_toEuclideanLin_eq_large_add_small S X (Nat.sqrt X)
  have heig : hA.eigenvalues rfl = (hL.add hH).eigenvalues rfl := by
    rw [LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff hA rfl (hL.add hH) rfl]
    rw [hsplit]
  change hA.eigenvalues rfl _ = _
  rw [heig]
  rfl

theorem palomar_uniform_finite_prime_sum
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        |(palomarLambdaAtArithmeticRank a) ^ 2
          - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)
          - 4 * palomarAllowedPrimeInvSubOneSum S X
          - centerPrimeCorrection (a : ℕ)| < δ := by
  intro δ hδ
  have hmain := eventually_logarithmicWindow_ranked_finitePrimeSum_proved
    S hS hε δ hδ
  filter_upwards [hmain] with X hX
  intro a ha
  obtain ⟨haY, hd, hrank, hbound⟩ := hX a ha
  rw [palomarLambdaAtArithmeticRank_eq a haY hd hrank]
  change |(arithmeticStarFullEigenvalue a haY hd) ^ 2 -
    (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
    4 * finiteAllowedPrimeInvSubOneSum S X -
    centerPrimeCorrection (a : ℕ)| < δ
  exact hbound

private theorem eventually_root_in_logarithmicWindow :
    ∀ᶠ X : ℕ in atTop,
      InLogarithmicCenterWindow (1 / 4 : ℝ) X 1 := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) :=
    hlogTop.eventually (Ici_mem_atTop 1)
  filter_upwards [hlogOne] with X hX
  refine ⟨by norm_num, ?_⟩
  simpa using Real.one_le_rpow hX (by norm_num : (0 : ℝ) ≤ 1 / 2 - 1 / 4)

theorem palomar_top_finite_prime_sum :
    ∀ δ > 0, ∀ᶠ X : ℕ in atTop, ∀ hX : 1 ≤ X,
      |(palomarLargestEigenvalue X hX) ^ 2
        - (Nat.primeCounting X : ℝ)
        - 4 * palomarAllowedPrimeInvSubOneSum ∅ X| < δ := by
  intro δ hδ
  have hmain := palomar_uniform_finite_prime_sum
    ∅ (by simp) (ε := (1 / 4 : ℝ)) (by norm_num) δ hδ
  filter_upwards [hmain, eventually_root_in_logarithmicWindow] with X hX hwindow
  intro hXpos
  have hroot := hX (palomarRootVertex X hXpos) (by simpa using hwindow)
  simpa [palomarLargestEigenvalue, allowedPrimeCount_empty,
    centerPrimeCorrection_one] using hroot

private theorem largePrimeNormalizedStarMode_apply_center_exact
    {S : Finset ℕ} {X Y : ℕ} (a : Vertex S X) (sign : ℝ)
    (hsign : sign ^ 2 = 1)
    (hd : 0 < largePrimeStarDegree S X Y a) :
    largePrimeNormalizedStarMode S X Y a sign a = (Real.sqrt 2)⁻¹ := by
  let u := largePrimeEuclideanStarVector S X Y a sign
  let d : ℝ := largePrimeStarDegree S X Y a
  have huSq : ‖u‖ ^ 2 = 2 * d := by
    simpa [u, d] using
      (norm_sq_largePrimeEuclideanStarVector (S := S) (X := X)
        (Y := Y) (c := a) hsign)
  have huNorm : ‖u‖ = Real.sqrt (2 * d) := by
    rw [← Real.sqrt_sq (norm_nonneg u), huSq]
  have hua : u a = Real.sqrt d := by
    simp [u, d, largePrimeEuclideanStarVector,
      largePrimeSignedStarVector]
  have hdPos : 0 < d := by
    dsimp [d]
    exact_mod_cast hd
  have hsqrtD : Real.sqrt d ≠ 0 := (Real.sqrt_pos.2 hdPos).ne'
  have hsqrtTwo : Real.sqrt 2 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num)).ne'
  rw [largePrimeNormalizedStarMode, NormedSpace.normalize]
  change ‖u‖⁻¹ * u a = _
  rw [huNorm, hua, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

private theorem palomarPrimeStarCentre_apply_center
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a) :
    palomarPrimeStarCentre S X a a = 1 := by
  have hplus := largePrimeNormalizedStarMode_apply_center_exact
    a (1 : ℝ) (by norm_num) hd
  have hminus := largePrimeNormalizedStarMode_apply_center_exact
    a (-1 : ℝ) (by norm_num) hd
  rw [palomarPrimeStarCentre, normalizedPairCentre]
  simp only [PiLp.smul_apply, PiLp.add_apply, complexifyEuclidean_apply,
    hplus, hminus]
  have hsqrtTwo : Real.sqrt 2 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsqrtTwoSq : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  rw [smul_eq_mul]
  push_cast
  field_simp
  simpa only [one_add_one_eq_two] using hsqrtTwoSq.symm

private theorem palomarPrimeStarShell_apply_center
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) a) :
    palomarPrimeStarShell S X a a = 0 := by
  have hplus := largePrimeNormalizedStarMode_apply_center_exact
    a (1 : ℝ) (by norm_num) hd
  have hminus := largePrimeNormalizedStarMode_apply_center_exact
    a (-1 : ℝ) (by norm_num) hd
  rw [palomarPrimeStarShell, normalizedPairShell]
  simp [hplus, hminus]

theorem palomar_uniform_explicit_frequency_dynamics
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InLogarithmicCenterWindow ε X (a : ℕ) →
        palomarFirstExitCorrection S X a =
            (let c := (a : ℕ)
             let d := (allowedPrimeCount S (X / c) : ℝ) -
               (allowedPrimeCount S (Nat.sqrt X) : ℝ)
             (∑ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
                 let r := if c * q ≤ Nat.sqrt X then
                   ((allowedPrimeCount S (X / (c * q)) : ℝ) -
                       (allowedPrimeCount S (Nat.sqrt X) : ℝ)) / d
                 else 0
                 4 * r / (1 - r)) +
               ∑ q ∈ c.primeFactors,
                 let s := ((allowedPrimeCount S (X / (c / q)) : ℝ) -
                     (allowedPrimeCount S (Nat.sqrt X) : ℝ)) / d
                 (5 - s) / (1 - s)) ∧
          palomarPrimeCoverEvolution S X =
            (fun t : ℝ ↦ NormedSpace.exp ((-((t : ℂ) * Complex.I)) •
              LinearMap.toContinuousLinearMap
                (Matrix.toEuclideanLin
                  ((primeCoverGraph S X).adjMatrix ℂ)))) ∧
          palomarLocalizationBound (a : ℕ) X =
            (let K := 12 * Real.log 4 + 2 / Real.log 2 + 16
             let eta := K *
               (Real.sqrt ((Nat.sqrt X + 1 : ℕ) : ℝ) /
                 Real.sqrt (Real.log ((Nat.sqrt X + 1 : ℕ) : ℝ)))
             let gamma := (96 * (((a : ℕ) + 1 : ℕ) : ℝ))⁻¹ *
               Real.sqrt ((X : ℝ) /
                 (((a : ℕ) : ℝ) * Real.log (X : ℝ)))
             4 * eta / (gamma - 2 * eta)) ∧
          palomarFeshbachRemainderConstant =
            (let K := 12 * Real.log 4 + 2 / Real.log 2 + 16
             let E := 640000000 * K ^ 2
             let D := 48 * (80000000 : ℝ) ^ 2
             528 * 768 * E + 1280 * (D + E) + 1600 * E) ∧
          ‖palomarPrimeStarCentre S X a‖ = 1 ∧
          ‖palomarPrimeStarShell S X a‖ = 1 ∧
          palomarPrimeStarCentre S X a a = 1 ∧
          palomarPrimeStarShell S X a a = 0 ∧
          0 < palomarLambdaAtArithmeticRank a ∧
          0 < palomarApproximateFrequency S X a ∧
          0 < palomarLambdaAtArithmeticRank a +
            palomarApproximateFrequency S X a ∧
          ∀ t : ℝ,
            ‖palomarPrimeCoverEvolution S X t
                  (palomarPrimeStarCentre S X a) -
                ((Real.cos (palomarApproximateFrequency S X a * t) : ℂ) •
                    palomarPrimeStarCentre S X a -
                  (Complex.I *
                      Real.sin (palomarApproximateFrequency S X a * t)) •
                    palomarPrimeStarShell S X a)‖ ≤
              4 * palomarLocalizationBound (a : ℕ) X +
                2 * |t| *
                  ((palomarFeshbachRemainderConstant *
                      ((a : ℝ) ^ 2 / Real.log (X : ℝ))) /
                    (palomarLambdaAtArithmeticRank a +
                      palomarApproximateFrequency S X a)) := by
  have hdynamics :=
    eventually_logarithmicWindow_starPair_dynamics_with_actualCorrection
      S hS hε
  have hranked := eventually_logarithmicWindow_ranked_actualCorrection_proved
    S hS hε 1 zero_lt_one
  have hfrequency :=
    eventually_logarithmicWindow_actualCorrection_frequency_bound S hS hε
  filter_upwards [hdynamics, hranked, hfrequency] with
      X hdynamicsX hrankedX hfrequencyX
  intro a ha
  obtain ⟨haY, hd, _sigma, _hsigma, _hF, hbound⟩ := hdynamicsX a ha
  obtain ⟨haY', hd', hrank, _hrem⟩ := hrankedX a ha
  have hhaY : haY' = haY := Subsingleton.elim _ _
  subst haY'
  have hhd : hd' = hd := Subsingleton.elim _ _
  subst hd'
  have hlam := palomarLambdaAtArithmeticRank_eq a haY hd hrank
  obtain ⟨hlamPos, hFPos, _hfrequencyBound⟩ := hfrequencyX a ha haY hd
  have hhatPos : 0 < palomarApproximateFrequency S X a := by
    rw [palomarApproximateFrequency, logarithmicWindowApproximateFrequency]
    exact Real.sqrt_pos.2 hFPos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hhatPos, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa [palomarPrimeStarCentre] using
      norm_normalizedPairCentre_largePrimeStarModes hd
  · simpa [palomarPrimeStarShell] using
      norm_normalizedPairShell_largePrimeStarModes hd
  · exact palomarPrimeStarCentre_apply_center a hd
  · exact palomarPrimeStarShell_apply_center a hd
  · simpa [hlam] using hlamPos
  · have : 0 < palomarLambdaAtArithmeticRank a := by
      simpa [hlam] using hlamPos
    linarith
  · intro t
    simpa [palomarFirstExitCorrection, palomarApproximateFrequency,
      logarithmicWindowApproximateFrequency, palomarPrimeStarCentre,
      palomarPrimeStarShell, palomarPrimeCoverEvolution,
      palomarLocalizationBound, palomarFeshbachRemainderConstant,
      hlam] using hbound t

end PrimeStar
