import PrimeStar.ArithmeticIndex

/-!
# Degree isolation for the large-prime star forest

At a square cutoff, every non-isolated component of the large-prime graph is
a star.  This file turns that component description into a spectral
classification and then translates separation of the star degrees into the
ordered-eigenvalue separation required by the perturbation interface.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

local instance degreeIsolationLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance degreeIsolationSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance degreeIsolationPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- Coordinate form of a large-prime adjacency eigenvector equation. -/
private theorem largePrime_eigenvector_coordinate
    {S : Finset ℕ} {X Y : ℕ}
    {x : EuclideanSpace ℝ (Vertex S X)} {lambda : ℝ}
    (hx : Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x =
      lambda • x) (v : Vertex S X) :
    ∑ w ∈ (largePrimeGraph S X Y).neighborFinset v, x w = lambda * x v := by
  have hv := congrArg (fun z : EuclideanSpace ℝ (Vertex S X) ↦ z v) hx
  rw [Matrix.toLpLin_toLp 2 2] at hv
  simp only [Matrix.toLin'_apply] at hv
  change Matrix.mulVec ((largePrimeGraph S X Y).adjMatrix ℝ)
      (fun w ↦ x w) v = lambda * x v at hv
  simpa only [SimpleGraph.adjMatrix_mulVec_apply] using hv

/-- A nonzero coordinate of a nonzero-eigenvalue vector belongs to a
nonempty lower star whose degree is the square of that eigenvalue. -/
theorem exists_signedStarDegree_of_eigenvector_coordinate_ne_zero
    {S : Finset ℕ} {X Y : ℕ}
    (hcut : X < (Y + 1) * (Y + 1))
    {x : EuclideanSpace ℝ (Vertex S X)} {lambda : ℝ}
    (hx : Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x =
      lambda • x) (hlambda : lambda ≠ 0)
    {v : Vertex S X} (hv : x v ≠ 0) :
    ∃ b : Vertex S X, (b : ℕ) ≤ Y ∧
      v ∈ largePrimeStarSupport S X Y b ∧
      0 < largePrimeStarDegree S X Y b ∧
      (lambda = √(largePrimeStarDegree S X Y b : ℝ) ∨
        lambda = -√(largePrimeStarDegree S X Y b : ℝ)) := by
  have hviso : ¬(largePrimeGraph S X Y).IsIsolated v := by
    intro hviso
    have hvEq := largePrime_eigenvector_coordinate hx v
    rw [hviso.neighborFinset_eq_empty] at hvEq
    simp only [Finset.sum_empty] at hvEq
    have hmul : lambda * x v = 0 := hvEq.symm
    exact hv ((mul_eq_zero.mp hmul).resolve_left hlambda)
  obtain ⟨b, hbY, hvb⟩ :=
    exists_largePrimeStarSupport_of_not_isolated hcut hviso
  have hbd : 0 < largePrimeStarDegree S X Y b := by
    rw [largePrimeStarDegree_eq_degree, SimpleGraph.degree_pos]
    intro hbiso
    rw [mem_largePrimeStarSupport] at hvb
    rcases hvb with rfl | hbv
    · exact hviso hbiso
    · exact hbiso v hbv
  have hxb : x b ≠ 0 := by
    rw [mem_largePrimeStarSupport] at hvb
    rcases hvb with rfl | hbv
    · exact hv
    · intro hxb0
      have hvleaf : v ∈ largePrimeLeaves S X Y b :=
        mem_largePrimeLeaves.mpr hbv
      have hvEq := largePrime_eigenvector_coordinate hx v
      rw [largePrime_neighborFinset_leaf hcut hbY hvleaf] at hvEq
      simp only [Finset.sum_singleton] at hvEq
      rw [hxb0] at hvEq
      exact hv (eq_zero_of_ne_zero_of_mul_left_eq_zero hlambda hvEq.symm)
  have hcenter := largePrime_eigenvector_coordinate hx b
  change (∑ w ∈ largePrimeLeaves S X Y b, x w) = lambda * x b at hcenter
  have hsum :
      lambda * (∑ w ∈ largePrimeLeaves S X Y b, x w) =
        (largePrimeStarDegree S X Y b : ℝ) * x b := by
    calc
      lambda * (∑ w ∈ largePrimeLeaves S X Y b, x w) =
          ∑ w ∈ largePrimeLeaves S X Y b, lambda * x w := by
            rw [Finset.mul_sum]
      _ = ∑ _w ∈ largePrimeLeaves S X Y b, x b := by
            apply Finset.sum_congr rfl
            intro w hw
            have hwEq := largePrime_eigenvector_coordinate hx w
            rw [largePrime_neighborFinset_leaf hcut hbY hw] at hwEq
            simpa only [Finset.sum_singleton] using hwEq.symm
      _ = (largePrimeStarDegree S X Y b : ℝ) * x b := by
            simp [largePrimeStarDegree]
  have hlambdaSq : lambda ^ 2 = (largePrimeStarDegree S X Y b : ℝ) := by
    apply mul_right_cancel₀ hxb
    calc
      lambda ^ 2 * x b = lambda * (lambda * x b) := by ring
      _ = lambda * (∑ w ∈ largePrimeLeaves S X Y b, x w) := by rw [hcenter]
      _ = (largePrimeStarDegree S X Y b : ℝ) * x b := hsum
  have hsqrtSq :
      (√(largePrimeStarDegree S X Y b : ℝ)) ^ 2 =
        (largePrimeStarDegree S X Y b : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  refine ⟨b, hbY, hvb, hbd, ?_⟩
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (hlambdaSq.trans hsqrtSq.symm)

/-- Every nonzero eigenvalue of the square-cutoff large-prime graph is one of
the two signed square roots of a nonempty lower-star degree. -/
theorem largePrime_eigenvalue_eq_zero_or_signedStarDegree
    {S : Finset ℕ} {X Y : ℕ}
    (hcut : X < (Y + 1) * (Y + 1))
    {x : EuclideanSpace ℝ (Vertex S X)} {lambda : ℝ}
    (hx : Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x =
      lambda • x) (hx0 : x ≠ 0) :
    lambda = 0 ∨
      ∃ b : Vertex S X, (b : ℕ) ≤ Y ∧
        0 < largePrimeStarDegree S X Y b ∧
        (lambda = √(largePrimeStarDegree S X Y b : ℝ) ∨
          lambda = -√(largePrimeStarDegree S X Y b : ℝ)) := by
  by_cases hlambda : lambda = 0
  · exact Or.inl hlambda
  right
  have hxcoord : ∃ v : Vertex S X, x v ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    ext v
    exact h v
  obtain ⟨v, hv⟩ := hxcoord
  obtain ⟨b, hbY, _hvb, hbd, hb⟩ :=
    exists_signedStarDegree_of_eigenvector_coordinate_ne_zero hcut hx hlambda hv
  exact ⟨b, hbY, hbd, hb⟩

/-- If the degree of `c` is unique among nonempty lower stars, then its
positive adjacency eigenspace is spanned by the positive signed star vector. -/
theorem largePrime_positiveStar_eigenvector_eq_smul
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (huniq : ∀ b : Vertex S X, (b : ℕ) ≤ Y →
      0 < largePrimeStarDegree S X Y b →
      largePrimeStarDegree S X Y b = largePrimeStarDegree S X Y c → b = c)
    {x : EuclideanSpace ℝ (Vertex S X)}
    (hx : Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x =
      √(largePrimeStarDegree S X Y c : ℝ) • x) :
    ∃ r : ℝ, x = r • largePrimeEuclideanStarVector S X Y c 1 := by
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  have hmu : 0 < mu := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hmu0 : mu ≠ 0 := hmu.ne'
  refine ⟨x c / mu, ?_⟩
  ext v
  by_cases hvc : v = c
  · subst v
    change x c = (x c / mu) *
      largePrimeSignedStarVector S X Y c 1 c
    rw [largePrimeSignedStarVector_center]
    change x c = x c / mu * mu
    field_simp
  by_cases hvleaf : v ∈ largePrimeLeaves S X Y c
  · have hvEq := largePrime_eigenvector_coordinate hx v
    rw [largePrime_neighborFinset_leaf hcut hc hvleaf] at hvEq
    simp only [Finset.sum_singleton] at hvEq
    change x c = mu * x v at hvEq
    change x v = (x c / mu) *
      largePrimeSignedStarVector S X Y c 1 v
    rw [largePrimeSignedStarVector_leaf hvleaf]
    norm_num
    exact (eq_div_iff hmu0).2 (by simpa [mul_comm] using hvEq.symm)
  · have hvout : v ∉ largePrimeStarSupport S X Y c := by
      simp [largePrimeStarSupport, hvc, hvleaf]
    have hxv : x v = 0 := by
      by_contra hxv0
      obtain ⟨b, hbY, hvb, hbd, hbSign⟩ :=
        exists_signedStarDegree_of_eigenvector_coordinate_ne_zero hcut hx hmu0 hxv0
      have hsqrt :
          √(largePrimeStarDegree S X Y b : ℝ) = mu := by
        rcases hbSign with hb | hb
        · exact hb.symm
        · have hbnonneg : 0 ≤ √(largePrimeStarDegree S X Y b : ℝ) :=
            Real.sqrt_nonneg _
          change mu = -√(largePrimeStarDegree S X Y b : ℝ) at hb
          exfalso
          nlinarith
      have hdegree :
          largePrimeStarDegree S X Y b = largePrimeStarDegree S X Y c := by
        have hsquares := congrArg (fun z : ℝ ↦ z ^ 2) hsqrt
        rw [Real.sq_sqrt (Nat.cast_nonneg _),
          Real.sq_sqrt (Nat.cast_nonneg _)] at hsquares
        exact_mod_cast hsquares
      have hbc : b = c := huniq b hbY hbd hdegree
      exact hvout (by simpa [hbc] using hvb)
    change x v = (x c / mu) *
      largePrimeSignedStarVector S X Y c 1 v
    rw [largePrimeSignedStarVector_eq_zero_of_not_mem hvout, hxv]
    ring

/-- A degree that is unique among nonempty lower stars gives a simple
positive eigenvalue of the large-prime forest. -/
theorem largePrime_positiveStar_eigenspace_finrank_eq_one
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (huniq : ∀ b : Vertex S X, (b : ℕ) ≤ Y →
      0 < largePrimeStarDegree S X Y b →
      largePrimeStarDegree S X Y b = largePrimeStarDegree S X Y c → b = c) :
    Module.finrank ℝ
      (Module.End.eigenspace
        (Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ))
        (√(largePrimeStarDegree S X Y c : ℝ))) = 1 := by
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let u := largePrimeEuclideanStarVector S X Y c 1
  have hu0 : u ≠ 0 := by
    dsimp [u, largePrimeEuclideanStarVector]
    rw [WithLp.toLp_eq_zero]
    exact largePrimeSignedStarVector_ne_zero hd
  have hsub : Module.End.eigenspace L mu ≤ ℝ ∙ u := by
    intro x hxmem
    obtain ⟨r, hr⟩ := largePrime_positiveStar_eigenvector_eq_smul
      c hcut hc hd huniq (Module.End.mem_eigenspace_iff.mp hxmem)
    rw [hr]
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self u)
  have hle : Module.finrank ℝ (Module.End.eigenspace L mu) ≤ 1 := by
    calc
      Module.finrank ℝ (Module.End.eigenspace L mu) ≤
          Module.finrank ℝ (ℝ ∙ u) := Submodule.finrank_mono hsub
      _ = 1 := finrank_span_singleton hu0
  have hge : 1 ≤ Module.finrank ℝ (Module.End.eigenspace L mu) := by
    rw [Submodule.one_le_finrank_iff]
    refine Module.End.hasEigenvalue_iff.mp ?_
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨
      Module.End.mem_eigenspace_iff.mpr (by
        simpa [L, mu, u] using
          largePrime_toEuclideanLin_signedStarVector hcut hc
            (by norm_num : (1 : ℝ) ^ 2 = 1)), hu0⟩
  exact Nat.le_antisymm hle hge

/-- The selected star index is exactly the number of ordered reference
eigenvalues strictly above its positive star frequency.  The remaining
arithmetic indexing problem is therefore a finite inertia count: one must
identify that cardinality with the number of allowed centres below `c`. -/
theorem largePrimePositiveStarOrderedIndex_val_eq_card_eigenvalues_gt
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (huniq : ∀ b : Vertex S X, (b : ℕ) ≤ Y →
      0 < largePrimeStarDegree S X Y b →
      largePrimeStarDegree S X Y b = largePrimeStarDegree S X Y c → b = c) :
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    let i := largePrimePositiveStarOrderedIndex c hcut hc hd
    i.1 = (Finset.univ.filter fun j ↦
      √(largePrimeStarDegree S X Y c : ℝ) < hL.eigenvalues rfl j).card := by
  dsimp only
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let i := largePrimePositiveStarOrderedIndex c hcut hc hd
  have hi : hL.eigenvalues rfl i = mu := by
    simpa [hL, i, mu] using
      largePrimePositiveStarOrderedIndex_eigenvalue c hcut hc hd
  have hspan : Module.finrank ℝ (Module.End.eigenspace L mu) = 1 := by
    simpa [L, mu] using
      largePrime_positiveStar_eigenspace_finrank_eq_one c hcut hc hd huniq
  have hcard := hL.card_filter_eigenvalues_eq rfl mu
  rw [hspan] at hcard
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
  have hik : i = k := by
    have hm := congrArg (fun F : Finset (Fin (Module.finrank ℝ
        (EuclideanSpace ℝ (Vertex S X)))) ↦ i ∈ F) hk
    simpa [hi] using hm
  have hunique : ∀ j, hL.eigenvalues rfl j = hL.eigenvalues rfl i → j = i := by
    intro j hj
    have hjmu : hL.eigenvalues rfl j = mu := hj.trans hi
    have hjk : j = k := by
      have hm := congrArg (fun F : Finset (Fin (Module.finrank ℝ
          (EuclideanSpace ℝ (Vertex S X)))) ↦ j ∈ F) hk
      simpa [hjmu] using hm
    exact hjk.trans hik.symm
  have hcount := orderedIndex_val_eq_card_filter_gt
    (hL.eigenvalues rfl) (hL.eigenvalues_antitone rfl) i hunique
  simpa [hi, hL, i, mu] using hcount

/-- Separation of the square roots of the nonempty lower-star degrees is
exactly the ordered spectral separation consumed by the perturbation layer. -/
theorem largePrime_orderedEigenvalue_separated_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|) :
    ∀ j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))),
      j ≠ largePrimePositiveStarOrderedIndex c hcut hc hd →
      gamma ≤
        |(Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl j -
          √(largePrimeStarDegree S X Y c : ℝ)| := by
  intro j hji
  by_cases hgamma0 : gamma = 0
  · simp [hgamma0]
  have hgammaPos : 0 < gamma := lt_of_le_of_ne hgamma (Ne.symm hgamma0)
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let i := largePrimePositiveStarOrderedIndex c hcut hc hd
  have hi : hL.eigenvalues rfl i = mu := by
    simpa [hL, i, mu] using
      largePrimePositiveStarOrderedIndex_eigenvalue c hcut hc hd
  have huniq : ∀ b : Vertex S X, (b : ℕ) ≤ Y →
      0 < largePrimeStarDegree S X Y b →
      largePrimeStarDegree S X Y b = largePrimeStarDegree S X Y c → b = c := by
    intro b hbY hbd hbcDegree
    by_contra hbc
    have hgap := hdegree b hbY hbc hbd
    rw [hbcDegree, sub_self, abs_zero] at hgap
    exact (not_lt_of_ge hgap) hgammaPos
  have hspan : Module.finrank ℝ (Module.End.eigenspace L mu) = 1 := by
    simpa [L, mu] using
      largePrime_positiveStar_eigenspace_finrank_eq_one c hcut hc hd huniq
  let x := hL.eigenvectorBasis rfl j
  have hx0 : x ≠ 0 := (hL.eigenvectorBasis rfl).orthonormal.ne_zero j
  have hxEig : L x = hL.eigenvalues rfl j • x :=
    hL.apply_eigenvectorBasis rfl j
  obtain hjzero | ⟨b, hbY, hbd, hjpos | hjneg⟩ :=
    largePrime_eigenvalue_eq_zero_or_signedStarDegree hcut hxEig hx0
  · simpa [hL, mu, hjzero, abs_of_nonneg (Real.sqrt_nonneg _)] using hzeroGap
  · by_cases hbc : b = c
    · have hjmu : hL.eigenvalues rfl j = mu := by simpa [hbc, mu] using hjpos
      have hcard := hL.card_filter_eigenvalues_eq rfl mu
      rw [hspan] at hcard
      obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
      have hik : i = k := by
        have hm := congrArg (fun F : Finset (Fin (Module.finrank ℝ
            (EuclideanSpace ℝ (Vertex S X)))) ↦ i ∈ F) hk
        simpa [hi] using hm
      have hjk : j = k := by
        have hm := congrArg (fun F : Finset (Fin (Module.finrank ℝ
            (EuclideanSpace ℝ (Vertex S X)))) ↦ j ∈ F) hk
        simpa [hjmu] using hm
      exact False.elim (hji (hjk.trans hik.symm))
    · simpa [hL, mu, hjpos, abs_sub_comm] using hdegree b hbY hbc hbd
  · have hbnonneg : 0 ≤ √(largePrimeStarDegree S X Y b : ℝ) :=
      Real.sqrt_nonneg _
    have hmunonneg : 0 ≤ mu := Real.sqrt_nonneg _
    rw [hjneg]
    rw [abs_of_nonpos (by nlinarith :
      -√(largePrimeStarDegree S X Y b : ℝ) - mu ≤ 0)]
    nlinarith

/-- Arithmetic matching with degree gaps as the only large-prime spectral
input.  This discharges the ordered-spectrum premise of
`primeCover_exists_simple_arithmeticStarEigenpair`. -/
theorem primeCover_exists_simple_arithmeticStarEigenpair_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
    let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    ∃ k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))),
      |(hL.add hHs).eigenvalues rfl k -
          √(largePrimeStarDegree S X Y c : ℝ)| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace (L + H)
          ((hL.add hHs).eigenvalues rfl k)) = 1 := by
  apply primeCover_exists_simple_arithmeticStarEigenpair
      c hcut hc hd gamma eta hgamma
  · exact largePrime_orderedEigenvalue_separated_of_degreeGap
      c hcut hc hd gamma hgamma hzeroGap hdegree
  · exact hH
  · exact hsmall

/-- Same-index arithmetic matching with the degree-gap family as its only
large-prime spectral input. -/
theorem primeCover_simple_arithmeticStarEigenpair_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmall : 2 * eta < gamma) :
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
    let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    let hHs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((smallPrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    let i := largePrimePositiveStarOrderedIndex c hcut hc hd
    |(hL.add hHs).eigenvalues rfl i -
        √(largePrimeStarDegree S X Y c : ℝ)| ≤ eta ∧
      Module.finrank ℝ
        (Module.End.eigenspace (L + H)
          ((hL.add hHs).eigenvalues rfl i)) = 1 := by
  apply primeCover_simple_arithmeticStarEigenpair
      c hcut hc hd gamma eta hgamma
  · exact largePrime_orderedEigenvalue_separated_of_degreeGap
      c hcut hc hd gamma hgamma hzeroGap hdegree
  · exact hH
  · exact hsmall

/-- The shifted complement gap with square-root degree separation in place
of an abstract ordered-spectrum hypothesis. -/
theorem primeCover_shiftedComplementGap_arithmeticStar_of_degreeGap
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta lam : ℝ) (hgamma : 0 ≤ gamma)
    (hzeroGap : gamma ≤ √(largePrimeStarDegree S X Y c : ℝ))
    (hdegree : ∀ b : Vertex S X, (b : ℕ) ≤ Y → b ≠ c →
      0 < largePrimeStarDegree S X Y b →
      gamma ≤ |√(largePrimeStarDegree S X Y c : ℝ) -
        √(largePrimeStarDegree S X Y b : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X))
    (hx : ⟪largePrimeNormalizedStarMode S X Y c 1, x⟫_ℝ = 0) :
    (gamma - eta - |lam - √(largePrimeStarDegree S X Y c : ℝ)|) * ‖x‖ ≤
      ‖Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x - lam • x‖ := by
  apply primeCover_shiftedComplementGap_arithmeticStar
      c hcut hc hd gamma eta lam hgamma
  · exact largePrime_orderedEigenvalue_separated_of_degreeGap
      c hcut hc hd gamma hgamma hzeroGap hdegree
  · exact hH
  · exact hx

end

end PrimeStar
