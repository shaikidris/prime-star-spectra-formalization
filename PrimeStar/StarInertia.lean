import PrimeStar.DegreeIsolation
import PrimeStar.PrimeCountingDegree
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Positive inertia of the large-prime star forest

Each nonempty large-prime star contributes one positive eigenvalue, counted
with multiplicity.  This module proves the fibrewise statement needed to
turn a spectrally selected ordered slot into the manuscript's arithmetic
centre rank.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

local instance starInertiaLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj := Classical.decRel _

private theorem largePrimeEigenvectorCoordinate
    {S : Finset ℕ} {X Y : ℕ}
    {x : EuclideanSpace ℝ (Vertex S X)} {lambda : ℝ}
    (hx : Matrix.toEuclideanLin
        ((largePrimeGraph S X Y).adjMatrix ℝ) x = lambda • x)
    (v : Vertex S X) :
    ∑ w ∈ (largePrimeGraph S X Y).neighborFinset v, x w = lambda * x v := by
  have hv := congrArg (fun z : EuclideanSpace ℝ (Vertex S X) ↦ z v) hx
  rw [Matrix.toLpLin_toLp 2 2] at hv
  simp only [Matrix.toLin'_apply] at hv
  change Matrix.mulVec ((largePrimeGraph S X Y).adjMatrix ℝ)
      (fun w ↦ x w) v = lambda * x v at hv
  simpa only [SimpleGraph.adjMatrix_mulVec_apply] using hv

/-- Lower nonempty stars carrying the positive frequency `mu`. -/
def largePrimePositiveDegreeFiber
    (S : Finset ℕ) (X Y : ℕ) (mu : ℝ) : Finset (Vertex S X) :=
  Finset.univ.filter fun b ↦
    (b : ℕ) ≤ Y ∧ 0 < largePrimeStarDegree S X Y b ∧
      √(largePrimeStarDegree S X Y b : ℝ) = mu

@[simp]
theorem mem_largePrimePositiveDegreeFiber
    {S : Finset ℕ} {X Y : ℕ} {mu : ℝ} {b : Vertex S X} :
    b ∈ largePrimePositiveDegreeFiber S X Y mu ↔
      (b : ℕ) ≤ Y ∧ 0 < largePrimeStarDegree S X Y b ∧
        √(largePrimeStarDegree S X Y b : ℝ) = mu := by
  simp [largePrimePositiveDegreeFiber]

/-- Positive star modes with a common frequency are linearly independent,
because their closed supports are disjoint and each has a nonzero centre
coordinate. -/
theorem linearIndependent_largePrimePositiveDegreeFiber
    {S : Finset ℕ} {X Y : ℕ} {mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) :
    LinearIndependent ℝ (fun b : ↥(largePrimePositiveDegreeFiber S X Y mu) ↦
      largePrimeEuclideanStarVector S X Y b.1 1) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum b
  have hb := mem_largePrimePositiveDegreeFiber.mp b.property
  have hcoord := congrArg
    (fun z : EuclideanSpace ℝ (Vertex S X) ↦ z b.1) hsum
  have hoff : ∀ i : ↥(largePrimePositiveDegreeFiber S X Y mu), i ≠ b →
      largePrimeSignedStarVector S X Y i.1 1 b.1 = 0 := by
    intro i hib
    have hi := mem_largePrimePositiveDegreeFiber.mp i.property
    have hibv : i.1 ≠ b.1 := fun h ↦ hib (Subtype.ext h)
    have hdisj := disjoint_largePrimeStarSupport hcut hi.1 hb.1 hibv
    have hbmem : b.1 ∈ largePrimeStarSupport S X Y b.1 := by
      simp [largePrimeStarSupport]
    have hbnot : b.1 ∉ largePrimeStarSupport S X Y i.1 := by
      intro hmem
      exact (Finset.disjoint_left.mp hdisj) hmem hbmem
    exact largePrimeSignedStarVector_eq_zero_of_not_mem hbnot
  have hsingle :
      (∑ i : ↥(largePrimePositiveDegreeFiber S X Y mu),
        g i * largePrimeSignedStarVector S X Y i.1 1 b.1) =
        g b * √(largePrimeStarDegree S X Y b.1 : ℝ) := by
    rw [Finset.sum_eq_single b]
    · rw [largePrimeSignedStarVector_center]
    · intro i _hi hib
      rw [hoff i hib, mul_zero]
    · simp
  have hcoord' : (∑ i : ↥(largePrimePositiveDegreeFiber S X Y mu),
      g i * largePrimeSignedStarVector S X Y i.1 1 b.1) = 0 := by
    simpa [largePrimeEuclideanStarVector] using hcoord
  rw [hsingle] at hcoord'
  have hsqrt : 0 < √(largePrimeStarDegree S X Y b.1 : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hb.2.1)
  exact (mul_eq_zero.mp hcoord').resolve_right hsqrt.ne'

/-- Restriction of a common-frequency eigenvector to the corresponding star
centres. -/
def largePrimeEigenspaceCenterRestriction
    {S : Finset ℕ} {X Y : ℕ} (mu : ℝ) :
    Module.End.eigenspace
        (Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)) mu →ₗ[ℝ]
      (↥(largePrimePositiveDegreeFiber S X Y mu) → ℝ) where
  toFun x b := (x.1 : EuclideanSpace ℝ (Vertex S X)) b.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- At positive frequency, centre coordinates determine the whole
large-prime eigenvector. -/
theorem injective_largePrimeEigenspaceCenterRestriction
    {S : Finset ℕ} {X Y : ℕ} {mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hmu : 0 < mu) :
    Function.Injective (largePrimeEigenspaceCenterRestriction
      (S := S) (X := X) (Y := Y) mu) := by
  intro x y hxy
  let z := x - y
  have hzmap : largePrimeEigenspaceCenterRestriction
      (S := S) (X := X) (Y := Y) mu z = 0 := by
    dsimp [z]
    rw [map_sub, hxy, sub_self]
  have hz : z = 0 := by
    apply Subtype.ext
    ext v
    by_contra hxv
    have hxEig : Matrix.toEuclideanLin
        ((largePrimeGraph S X Y).adjMatrix ℝ) (z.1) = mu • z.1 :=
      Module.End.mem_eigenspace_iff.mp z.2
    obtain ⟨b, hbY, hvb, hbd, hbpos | hbneg⟩ :=
      exists_signedStarDegree_of_eigenvector_coordinate_ne_zero
        hcut hxEig hmu.ne' hxv
    · have hbmem : b ∈ largePrimePositiveDegreeFiber S X Y mu := by
        exact mem_largePrimePositiveDegreeFiber.mpr ⟨hbY, hbd, hbpos.symm⟩
      let bs : ↥(largePrimePositiveDegreeFiber S X Y mu) := ⟨b, hbmem⟩
      have hxb : z.1 b = 0 := by
        have hzero := congrFun hzmap bs
        simpa [largePrimeEigenspaceCenterRestriction, bs] using hzero
      rw [mem_largePrimeStarSupport] at hvb
      rcases hvb with rfl | hbv
      · exact hxv hxb
      · have hvleaf : v ∈ largePrimeLeaves S X Y b :=
          mem_largePrimeLeaves.mpr hbv
        have hvEq := largePrimeEigenvectorCoordinate hxEig v
        rw [largePrime_neighborFinset_leaf hcut hbY hvleaf] at hvEq
        simp only [Finset.sum_singleton] at hvEq
        rw [hxb] at hvEq
        exact hxv (eq_zero_of_ne_zero_of_mul_left_eq_zero hmu.ne' hvEq.symm)
    · have hsqrt0 : 0 ≤ √(largePrimeStarDegree S X Y b : ℝ) :=
        Real.sqrt_nonneg _
      exfalso
      nlinarith
  exact sub_eq_zero.mp (by simpa [z] using hz)

/-- The multiplicity of a positive frequency equals the number of nonempty
stars carrying that frequency. -/
theorem largePrime_positive_eigenspace_finrank_eq_card_degreeFiber
    {S : Finset ℕ} {X Y : ℕ} {mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hmu : 0 < mu) :
    Module.finrank ℝ
        (Module.End.eigenspace
          (Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)) mu) =
      (largePrimePositiveDegreeFiber S X Y mu).card := by
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let F := largePrimePositiveDegreeFiber S X Y mu
  let w : ↥F → Module.End.eigenspace L mu := fun b ↦ ⟨
    largePrimeEuclideanStarVector S X Y b.1 1, by
      apply Module.End.mem_eigenspace_iff.mpr
      have hb := mem_largePrimePositiveDegreeFiber.mp b.property
      have heq := largePrime_toEuclideanLin_signedStarVector
        hcut hb.1 (by norm_num : (1 : ℝ) ^ 2 = 1)
      rw [hb.2.2] at heq
      simpa [L] using heq⟩
  have hliAmbient : LinearIndependent ℝ (fun b : ↥F ↦
      largePrimeEuclideanStarVector S X Y b.1 1) := by
    simpa [F] using
      (linearIndependent_largePrimePositiveDegreeFiber
        (S := S) (X := X) (Y := Y) (mu := mu) hcut)
  have hli : LinearIndependent ℝ w := by
    apply LinearIndependent.of_comp (Module.End.eigenspace L mu).subtype
    change LinearIndependent ℝ (fun b : ↥F ↦
      largePrimeEuclideanStarVector S X Y b.1 1)
    exact hliAmbient
  have hlower : Fintype.card ↥F ≤
      Module.finrank ℝ (Module.End.eigenspace L mu) :=
    hli.fintype_card_le_finrank
  let R := largePrimeEigenspaceCenterRestriction
    (S := S) (X := X) (Y := Y) mu
  have hRinj : Function.Injective R := by
    simpa [R, L] using
      (injective_largePrimeEigenspaceCenterRestriction
        (S := S) (X := X) (Y := Y) hcut hmu)
  have hupper : Module.finrank ℝ (Module.End.eigenspace L mu) ≤
      Module.finrank ℝ (↥F → ℝ) :=
    R.finrank_le_finrank_of_injective hRinj
  have hfun : Module.finrank ℝ (↥F → ℝ) = Fintype.card ↥F :=
    Module.finrank_fintype_fun_eq_card ℝ
  rw [hfun] at hupper
  have hEq := Nat.le_antisymm hupper hlower
  rw [Fintype.card_coe] at hEq
  simpa [F, L] using hEq

/-- Lower nonempty stars whose positive frequency is strictly above `mu`. -/
def largePrimePositiveAbove
    (S : Finset ℕ) (X Y : ℕ) (mu : ℝ) : Finset (Vertex S X) :=
  Finset.univ.filter fun b ↦
    (b : ℕ) ≤ Y ∧ 0 < largePrimeStarDegree S X Y b ∧
      mu < √(largePrimeStarDegree S X Y b : ℝ)

@[simp]
theorem mem_largePrimePositiveAbove
    {S : Finset ℕ} {X Y : ℕ} {mu : ℝ} {b : Vertex S X} :
    b ∈ largePrimePositiveAbove S X Y mu ↔
      (b : ℕ) ≤ Y ∧ 0 < largePrimeStarDegree S X Y b ∧
        mu < √(largePrimeStarDegree S X Y b : ℝ) := by
  simp [largePrimePositiveAbove]

/-- Positive inertia above a threshold is exactly the number of nonempty
large-prime stars whose positive frequency lies above that threshold.  This
counts repeated star degrees with their correct multiplicity. -/
theorem card_orderedEigenvalues_gt_eq_card_largePrimePositiveAbove
    {S : Finset ℕ} {X Y : ℕ} (mu : ℝ)
    (hcut : X < (Y + 1) * (Y + 1)) (hmu : 0 ≤ mu) :
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    (Finset.univ.filter fun j ↦ mu < hL.eigenvalues rfl j).card =
      (largePrimePositiveAbove S X Y mu).card := by
  dsimp only
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let eig := hL.eigenvalues rfl
  let deg : Vertex S X → ℝ := fun b ↦
    √(largePrimeStarDegree S X Y b : ℝ)
  let I := Finset.univ.filter fun j ↦ mu < eig j
  let F := largePrimePositiveAbove S X Y mu
  have himage : I.image eig = F.image deg := by
    ext nu
    constructor
    · intro hnu
      obtain ⟨j, hjI, hjnu⟩ := Finset.mem_image.mp hnu
      have hjgt : mu < eig j := (Finset.mem_filter.mp hjI).2
      let x := hL.eigenvectorBasis rfl j
      have hx0 : x ≠ 0 := (hL.eigenvectorBasis rfl).orthonormal.ne_zero j
      have hxEig : L x = eig j • x := by
        simpa [L, eig, x] using hL.apply_eigenvectorBasis rfl j
      obtain hjzero | ⟨b, hbY, hbd, hjpos | hjneg⟩ :=
        largePrime_eigenvalue_eq_zero_or_signedStarDegree hcut hxEig hx0
      · have : mu < 0 := by simpa [hjzero] using hjgt
        exact False.elim ((not_lt_of_ge hmu) this)
      · refine Finset.mem_image.mpr ⟨b, ?_, ?_⟩
        · exact mem_largePrimePositiveAbove.mpr ⟨hbY, hbd, by
            simpa [deg, hjpos] using hjgt⟩
        · simpa [deg, hjpos] using hjnu
      · have hnonneg : 0 ≤ √(largePrimeStarDegree S X Y b : ℝ) :=
          Real.sqrt_nonneg _
        have : mu < 0 := by
          calc
            mu < eig j := hjgt
            _ = -√(largePrimeStarDegree S X Y b : ℝ) := hjneg
            _ ≤ 0 := neg_nonpos.mpr hnonneg
        exact False.elim ((not_lt_of_ge hmu) this)
    · intro hnu
      obtain ⟨b, hbF, hbnu⟩ := Finset.mem_image.mp hnu
      have hb := mem_largePrimePositiveAbove.mp hbF
      have hvec : Module.End.HasEigenvector L (deg b)
          (largePrimeNormalizedStarMode S X Y b 1) := by
        rw [Module.End.hasEigenvector_iff]
        refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
        · simpa [L, deg] using
            (largePrime_toEuclideanLin_normalizedStarMode
              hcut hb.1 (by norm_num : (1 : ℝ) ^ 2 = 1))
        · intro hz
          have hn := norm_largePrimeNormalizedStarMode
            (S := S) (X := X) (Y := Y) (c := b) (ε := (1 : ℝ)) hb.2.1
          rw [hz, norm_zero] at hn
          norm_num at hn
      obtain ⟨j, hj⟩ := hL.exists_eigenvalues_eq rfl
        (Module.End.hasEigenvalue_of_hasEigenvector hvec)
      have hj' : eig j = deg b := by simpa [eig] using hj
      refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [hj']
          exact hb.2.2⟩
      · exact hj'.trans hbnu
  calc
    I.card = ∑ nu ∈ I.image eig, (I.filter fun j ↦ eig j = nu).card :=
      Finset.card_eq_sum_card_image eig I
    _ = ∑ nu ∈ F.image deg,
        (largePrimePositiveDegreeFiber S X Y nu).card := by
      rw [himage]
      apply Finset.sum_congr rfl
      intro nu hnu
      obtain ⟨b, hbF, hbnu⟩ := Finset.mem_image.mp hnu
      have hb := mem_largePrimePositiveAbove.mp hbF
      have hnugt : mu < nu := by
        rw [← hbnu]
        exact hb.2.2
      have hnupos : 0 < nu := hmu.trans_lt hnugt
      have hIfiber : (I.filter fun j ↦ eig j = nu) =
          (Finset.univ.filter fun j ↦ eig j = nu) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h ↦ h.2
        · intro hj
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            rw [hj]
            exact hnugt⟩, hj⟩
      rw [hIfiber]
      change (Finset.univ.filter fun j ↦ hL.eigenvalues rfl j = nu).card = _
      have hcard :
          (Finset.univ.filter fun j ↦ hL.eigenvalues rfl j = nu).card =
            Module.finrank ℝ (Module.End.eigenspace L nu) :=
        hL.card_filter_eigenvalues_eq rfl nu
      rw [hcard]
      simpa [L] using
        (largePrime_positive_eigenspace_finrank_eq_card_degreeFiber
          (S := S) (X := X) (Y := Y) hcut hnupos)
    _ = ∑ nu ∈ F.image deg, (F.filter fun b ↦ deg b = nu).card := by
      apply Finset.sum_congr rfl
      intro nu hnu
      obtain ⟨b, hbF, hbnu⟩ := Finset.mem_image.mp hnu
      have hb := mem_largePrimePositiveAbove.mp hbF
      have hnugt : mu < nu := by
        rw [← hbnu]
        exact hb.2.2
      have hfiber : largePrimePositiveDegreeFiber S X Y nu =
          F.filter fun z ↦ deg z = nu := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · intro hz
          have hzf := mem_largePrimePositiveDegreeFiber.mp hz
          exact ⟨mem_largePrimePositiveAbove.mpr
            ⟨hzf.1, hzf.2.1, by rw [hzf.2.2]; exact hnugt⟩,
            by simpa [deg] using hzf.2.2⟩
        · intro hz
          have hzf := mem_largePrimePositiveAbove.mp hz.1
          exact mem_largePrimePositiveDegreeFiber.mpr
            ⟨hzf.1, hzf.2.1, by simpa [deg] using hz.2⟩
      rw [hfiber]
    _ = F.card := (Finset.card_eq_sum_card_image deg F).symm

/-- Star degrees are antitone in the arithmetic centre. -/
theorem largePrimeStarDegree_antitone_of_center_le
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {b c : Vertex S X} (hbY : (b : ℕ) ≤ Y) (hcY : (c : ℕ) ≤ Y)
    (hbc : (b : ℕ) ≤ (c : ℕ)) :
    largePrimeStarDegree S X Y c ≤ largePrimeStarDegree S X Y b := by
  rw [largePrimeStarDegree_eq_card_largePrimeLabels hS c hcY,
    largePrimeStarDegree_eq_card_largePrimeLabels hS b hbY]
  apply Finset.card_le_card
  intro p hp
  have hquot : X / (c : ℕ) ≤ X / (b : ℕ) :=
    Nat.div_le_div_left hbc (Vertex.coe_pos b)
  simp only [largePrimeLabels, allowedPrimeInterval, Finset.mem_filter,
    Nat.mem_primesLE] at hp ⊢
  exact ⟨⟨hp.1.1.trans hquot, hp.1.2⟩, hp.2⟩

/-- If the target degree is unique, the stars above its frequency are
exactly the admissible arithmetic centres smaller than the target. -/
theorem largePrimePositiveAbove_eq_arithmeticLowerCenters
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (huniq : ∀ b : Vertex S X, (b : ℕ) ≤ Y →
      0 < largePrimeStarDegree S X Y b →
      largePrimeStarDegree S X Y b = largePrimeStarDegree S X Y c → b = c) :
    largePrimePositiveAbove S X Y
        (√(largePrimeStarDegree S X Y c : ℝ)) =
      Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (c : ℕ) := by
  ext b
  constructor
  · intro hb
    have hbA := mem_largePrimePositiveAbove.mp hb
    have hnot : ¬(c : ℕ) ≤ (b : ℕ) := by
      intro hcb
      have hdeg := largePrimeStarDegree_antitone_of_center_le hS hc hbA.1 hcb
      have hdegR : (largePrimeStarDegree S X Y b : ℝ) ≤
          (largePrimeStarDegree S X Y c : ℝ) := by exact_mod_cast hdeg
      have hsqrt := Real.sqrt_le_sqrt hdegR
      exact (not_lt_of_ge hsqrt) hbA.2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_of_not_ge hnot⟩
  · intro hb
    have hbval : (b : ℕ) < (c : ℕ) := (Finset.mem_filter.mp hb).2
    have hbY : (b : ℕ) ≤ Y := (Nat.le_of_lt hbval).trans hc
    have hdeg := largePrimeStarDegree_antitone_of_center_le hS hbY hc
      (Nat.le_of_lt hbval)
    have hbd : 0 < largePrimeStarDegree S X Y b := hd.trans_le hdeg
    have hne : largePrimeStarDegree S X Y b ≠
        largePrimeStarDegree S X Y c := by
      intro heq
      have hbc := huniq b hbY hbd heq
      exact (ne_of_lt hbval) (congrArg (fun z : Vertex S X ↦ (z : ℕ)) hbc)
    have hstrict : largePrimeStarDegree S X Y c <
        largePrimeStarDegree S X Y b := lt_of_le_of_ne hdeg (Ne.symm hne)
    exact mem_largePrimePositiveAbove.mpr ⟨hbY, hbd,
      Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hstrict)⟩

/-- The canonical positive-star spectral slot is the zero-based arithmetic
rank of its centre.  Equivalently, its value is the number of admissible
vertices strictly below the centre. -/
theorem largePrimePositiveStarOrderedIndex_val_eq_arithmeticRank
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (huniq : ∀ b : Vertex S X, (b : ℕ) ≤ Y →
      0 < largePrimeStarDegree S X Y b →
      largePrimeStarDegree S X Y b = largePrimeStarDegree S X Y c → b = c) :
    (largePrimePositiveStarOrderedIndex c hcut hc hd).1 =
      (Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (c : ℕ)).card := by
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  calc
    (largePrimePositiveStarOrderedIndex c hcut hc hd).1 =
        (Finset.univ.filter fun j ↦ mu < hL.eigenvalues rfl j).card := by
      simpa [L, hL, mu] using
        largePrimePositiveStarOrderedIndex_val_eq_card_eigenvalues_gt
          c hcut hc hd huniq
    _ = (largePrimePositiveAbove S X Y mu).card := by
      simpa [L, hL, mu] using
        card_orderedEigenvalues_gt_eq_card_largePrimePositiveAbove
          (S := S) (X := X) (Y := Y) mu hcut (Real.sqrt_nonneg _)
    _ = (Finset.univ.filter fun b : Vertex S X ↦
        (b : ℕ) < (c : ℕ)).card := by
      rw [largePrimePositiveAbove_eq_arithmeticLowerCenters hS c hc hd huniq]

/-- A noncanonical but exact matching between the ordered occurrences of one
positive eigenvalue and the stars carrying that frequency. -/
def largePrimePositiveEigenIndexDegreeFiberEquiv
    {S : Finset ℕ} {X Y : ℕ} (mu : ℝ)
    (hcut : X < (Y + 1) * (Y + 1)) (hmu : 0 < mu) :
    let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
    let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
    ↥(Finset.univ.filter fun j ↦ hL.eigenvalues rfl j = mu) ≃
      ↥(largePrimePositiveDegreeFiber S X Y mu) := by
  dsimp only
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  apply Fintype.equivOfCardEq
  rw [Fintype.card_coe, Fintype.card_coe]
  have hcard : (Finset.univ.filter fun j ↦ hL.eigenvalues rfl j = mu).card =
      Module.finrank ℝ (Module.End.eigenspace L mu) :=
    hL.card_filter_eigenvalues_eq rfl mu
  rw [hcard]
  simpa [L] using largePrime_positive_eigenspace_finrank_eq_card_degreeFiber
    (S := S) (X := X) (Y := Y) hcut hmu

end

end PrimeStar
