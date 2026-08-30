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

end PrimeStar
