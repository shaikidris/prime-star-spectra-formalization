import PrimeStar.FiniteRemainderAssembly
import PrimeStar.PrimeCountingDegree
import PrimeStar.Localization

/-!
# Canonical arithmetic first-exit blocks

This file identifies the coordinate blocks in the canonical first-exit
compression with the literal up-star and down-star vectors used in the finite
remainder formula.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

local instance canonicalFirstExitSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance canonicalFirstExitLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance canonicalFirstExitPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- Allowed small-prime labels whose upward neighbour of `c` remains in the
finite graph. -/
def canonicalUpPrimeLabels
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) : Finset ℕ :=
  (Nat.primesLE Y).filter fun q ↦ q ∉ S ∧ (c : ℕ) * q ≤ X

/-- Canonical indices for all arithmetic up-stars. -/
abbrev CanonicalUpIndex
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :=
  {q : ℕ // q ∈ canonicalUpPrimeLabels S X Y c}

/-- Canonical indices for the down-stars, one per distinct prime divisor. -/
abbrev CanonicalDownIndex {S : Finset ℕ} {X : ℕ} (c : Vertex S X) :=
  {q : ℕ // q ∈ (c : ℕ).primeFactors}

/-- The upward arithmetic centre `c*q`. -/
def canonicalUpTarget
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X) (q : CanonicalUpIndex S X Y c) : Vertex S X := by
  have hqdata := Finset.mem_filter.mp q.property
  exact vertexMulAllowedPrimeOfBound hS c q
    (Nat.mem_primesLE.mp hqdata.1).2 hqdata.2.1 hqdata.2.2

@[simp]
theorem canonicalUpTarget_coe
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X) (q : CanonicalUpIndex S X Y c) :
    (canonicalUpTarget hS c q : ℕ) = (c : ℕ) * q :=
  rfl

/-- The downward arithmetic centre `c/q`. -/
def canonicalDownTarget
    {S : Finset ℕ} {X : ℕ} (c : Vertex S X)
    (q : CanonicalDownIndex c) : Vertex S X := by
  have hqDvd : (q : ℕ) ∣ (c : ℕ) := Nat.dvd_of_mem_primeFactors q.property
  have hqLe : (q : ℕ) ≤ (c : ℕ) := Nat.le_of_mem_primeFactors q.property
  have hqPos : 0 < (q : ℕ) := Nat.pos_of_mem_primeFactors q.property
  have hdivPos : 0 < (c : ℕ) / q := Nat.div_pos hqLe hqPos
  exact vertexDivisorOfDvd c hdivPos (Nat.div_dvd_of_dvd hqDvd)

@[simp]
theorem canonicalDownTarget_mul_coe
    {S : Finset ℕ} {X : ℕ} (c : Vertex S X)
    (q : CanonicalDownIndex c) :
    (canonicalDownTarget c q : ℕ) * q = (c : ℕ) := by
  exact Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors q.property)

/-- An upward small-prime neighbour above the cutoff has no incident
large-prime edge. -/
theorem canonicalUpTarget_isIsolated_of_cutoff_lt
    {S : Finset ℕ} {X Y q : ℕ} {c target : Vertex S X}
    (hc : (c : ℕ) ≤ Y)
    (hcut : X < (Y + 1) * (Y + 1))
    (hq : q.Prime) (hqY : q ≤ Y)
    (hup : (c : ℕ) * q = (target : ℕ))
    (hYtarget : Y < (target : ℕ)) :
    (largePrimeGraph S X Y).IsIsolated target := by
  intro w htw
  obtain ⟨p, hp, _hpS, hYp, hEdge⟩ := htw
  rcases hEdge with htp | hpt
  · have hprod : (Y + 1) * (Y + 1) ≤ (target : ℕ) * p :=
      Nat.mul_le_mul (Nat.succ_le_iff.mpr hYtarget)
        (Nat.succ_le_iff.mpr hYp)
    have hbad : (Y + 1) * (Y + 1) ≤ X :=
      hprod.trans (by rw [htp]; exact Vertex.coe_le w)
    exact (not_le_of_gt hcut) hbad
  · have hpDvd : p ∣ (c : ℕ) * q := by
      refine ⟨(w : ℕ), ?_⟩
      calc
        (c : ℕ) * q = (target : ℕ) := hup
        _ = (w : ℕ) * p := hpt.symm
        _ = p * (w : ℕ) := Nat.mul_comm _ _
    rcases hp.dvd_mul.mp hpDvd with hpc | hpq
    · have hpLe : p ≤ (c : ℕ) := Nat.le_of_dvd (Vertex.coe_pos c) hpc
      exact (not_lt_of_ge (hpLe.trans hc)) hYp
    · have hpqEq : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
      exact (not_lt_of_ge hqY) (hpqEq ▸ hYp)

/-- The selected leaf set in a down-star: precisely those leaves whose
small-prime multiplication by `q` remains below the ambient cutoff. -/
def canonicalDownLeaves
    (S : Finset ℕ) (X Y : ℕ) (target : Vertex S X) (q : ℕ) :
    Finset (Vertex S X) :=
  (largePrimeLeaves S X Y target).filter fun v ↦ (v : ℕ) * q ≤ X

theorem canonicalDownLeaves_subset_largePrimeLeaves
    {S : Finset ℕ} {X Y q : ℕ} (target : Vertex S X) :
    canonicalDownLeaves S X Y target q ⊆
      largePrimeLeaves S X Y target := by
  intro v hv
  exact (Finset.mem_filter.mp hv).1

/-- The selected leaf set of a down-star has exactly the degree of the
original boundary star. -/
theorem card_canonicalDownLeaves_eq_largePrimeStarDegree
    {S : Finset ℕ} {X Y q : ℕ} {c target : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hc : (c : ℕ) ≤ Y) (htargetY : (target : ℕ) ≤ Y)
    (hq : q.Prime)
    (hdown : (target : ℕ) * q = (c : ℕ)) :
    (canonicalDownLeaves S X Y target q).card =
      largePrimeStarDegree S X Y c := by
  classical
  rw [largePrimeStarDegree_eq_card_largePrimeLabels hS c hc]
  symm
  apply Finset.card_bij
      (fun p hp ↦
        vertexMulAllowedPrimeOfBound hS target p
          ((Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2)
          (Finset.mem_filter.mp hp).2.1 (by
            have hpLE := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1
            have hcpX : (c : ℕ) * p ≤ X := by
              simpa [Nat.mul_comm] using
                (Nat.le_div_iff_mul_le (Vertex.coe_pos c)).mp hpLE
            calc
              (target : ℕ) * p ≤ ((target : ℕ) * p) * q :=
                Nat.le_mul_of_pos_right _ hq.pos
              _ = (c : ℕ) * p := by rw [← hdown]; ac_rfl
              _ ≤ X := hcpX))
  · intro p hp
    have hpdata := Finset.mem_filter.mp hp
    have hpprime : p.Prime := (Nat.mem_primesLE.mp hpdata.1).2
    have hpS : p ∉ S := hpdata.2.1
    have hYp : Y < p := hpdata.2.2
    apply Finset.mem_filter.mpr
    constructor
    · rw [mem_largePrimeLeaves_iff_child htargetY]
      exact ⟨p, hpprime, hpS, hYp, rfl⟩
    · change ((target : ℕ) * p) * q ≤ X
      have hpLE := (Nat.mem_primesLE.mp hpdata.1).1
      have hcpX : (c : ℕ) * p ≤ X := by
        simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le (Vertex.coe_pos c)).mp hpLE
      calc
        ((target : ℕ) * p) * q = (c : ℕ) * p := by
          rw [← hdown]
          ac_rfl
        _ ≤ X := hcpX
  · intro p hp r hr hpr
    have hcoe : (target : ℕ) * p = (target : ℕ) * r :=
      congrArg (fun v : Vertex S X ↦ (v : ℕ)) hpr
    exact Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos target) hcoe
  · intro v hv
    have hvdata := Finset.mem_filter.mp hv
    obtain ⟨p, hp, hpS, hYp, htp⟩ :=
      (mem_largePrimeLeaves_iff_child htargetY).mp hvdata.1
    have hcpX : (c : ℕ) * p ≤ X := by
      calc
        (c : ℕ) * p = ((target : ℕ) * q) * p := by rw [hdown]
        _ = ((target : ℕ) * p) * q := by ac_rfl
        _ = (v : ℕ) * q := by rw [htp]
        _ ≤ X := hvdata.2
    have hpLE : p ≤ X / (c : ℕ) := by
      apply (Nat.le_div_iff_mul_le (Vertex.coe_pos c)).2
      simpa [Nat.mul_comm] using hcpX
    have hpLabels : p ∈ largePrimeLabels S X Y c := by
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨hpLE, hp⟩, hpS, hYp⟩
    refine ⟨p, hpLabels, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    exact htp

/-- A non-isolated arithmetic up-centre carries exactly the full up-star
first-exit vector. -/
theorem restrict_normalizedPrimeStarFirstExit_eq_actualUpStar
    {S : Finset ℕ} {X Y q : ℕ} {c target : Vertex S X} {mu : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y) (htargetY : (target : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmu : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ Y)
    (hup : (c : ℕ) * q = (target : ℕ)) :
    restrictEuclideanToFinset (largePrimeStarSupport S X Y target)
        (normalizedPrimeStarFirstExit S X Y c) =
      actualUpStarFirstExit S X Y target mu
        (largePrimeNormalizedStarMode S X Y c 1 c) := by
  ext v
  by_cases hvt : v = target
  · subst v
    have hAdj : (smallPrimeGraph S X Y).Adj c target :=
      smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
        ⟨q, hq, hqS, hqY, Or.inl hup⟩
    have hb := normalizedPrimeStarFirstExit_apply_eq_starMode_neighbor
      hcut hc (by simp [largePrimeStarSupport]) hAdj
    rw [restrictEuclideanToFinset_apply,
      if_pos (by simp [largePrimeStarSupport]), hb]
    simp [actualUpStarFirstExit]
  · by_cases hvleaf : v ∈ largePrimeLeaves S X Y target
    · obtain ⟨p, hp, hpS, hYp, htp⟩ :=
        (mem_largePrimeLeaves_iff_child htargetY).mp hvleaf
      have hcpX : (c : ℕ) * p ≤ X := by
        have hle : (c : ℕ) * p ≤ ((c : ℕ) * p) * q :=
          Nat.le_mul_of_pos_right _ hq.pos
        apply hle.trans
        calc
          ((c : ℕ) * p) * q = ((c : ℕ) * q) * p := by ac_rfl
          _ = (target : ℕ) * p := by rw [hup]
          _ = (v : ℕ) := htp
          _ ≤ X := Vertex.coe_le v
      let w : Vertex S X :=
        vertexMulAllowedPrimeOfBound hS c p hp hpS hcpX
      have hwleaf : w ∈ largePrimeLeaves S X Y c := by
        rw [mem_largePrimeLeaves_iff_child hc]
        exact ⟨p, hp, hpS, hYp, rfl⟩
      have hwv : (smallPrimeGraph S X Y).Adj w v := by
        apply smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
        refine ⟨q, hq, hqS, hqY, Or.inl ?_⟩
        change ((c : ℕ) * p) * q = (v : ℕ)
        calc
          ((c : ℕ) * p) * q = ((c : ℕ) * q) * p := by ac_rfl
          _ = (target : ℕ) * p := by rw [hup]
          _ = (v : ℕ) := htp
      have hb := normalizedPrimeStarFirstExit_apply_eq_starMode_neighbor
        hcut hc (by simp [largePrimeStarSupport, hwleaf]) hwv
      have hwcoord :=
        largePrimeNormalizedStarMode_leaf_eq_center_div_sqrt hd hwleaf
      rw [restrictEuclideanToFinset_apply,
        if_pos (by simp [largePrimeStarSupport, hvleaf]), hb, hwcoord, hmu]
      rw [actualUpStarFirstExit,
        largePrimeStarDataVector_leaf _ _ hvleaf]
    · have hvout : v ∉ largePrimeStarSupport S X Y target := by
        simp [largePrimeStarSupport, hvt, hvleaf]
      rw [restrictEuclideanToFinset_apply, if_neg hvout]
      exact (largePrimeStarDataVector_outside _ _ hvt hvleaf).symm

/-- The same up-star identity holds above the cutoff; there the target star
is an isolated singleton. -/
theorem restrict_normalizedPrimeStarFirstExit_eq_actualUpStar_isolated
    {S : Finset ℕ} {X Y q : ℕ} {c target : Vertex S X} {mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y) (hYtarget : Y < (target : ℕ))
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ Y)
    (hup : (c : ℕ) * q = (target : ℕ)) :
    restrictEuclideanToFinset (largePrimeStarSupport S X Y target)
        (normalizedPrimeStarFirstExit S X Y c) =
      actualUpStarFirstExit S X Y target mu
        (largePrimeNormalizedStarMode S X Y c 1 c) := by
  have hIso := canonicalUpTarget_isIsolated_of_cutoff_lt
    hc hcut hq hqY hup hYtarget
  ext v
  by_cases hvt : v = target
  · subst v
    have hAdj : (smallPrimeGraph S X Y).Adj c target :=
      smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
        ⟨q, hq, hqS, hqY, Or.inl hup⟩
    have hb := normalizedPrimeStarFirstExit_apply_eq_starMode_neighbor
      hcut hc (by simp [largePrimeStarSupport]) hAdj
    rw [restrictEuclideanToFinset_apply,
      if_pos (by simp [largePrimeStarSupport]), hb]
    simp [actualUpStarFirstExit]
  · have hvleaf : v ∉ largePrimeLeaves S X Y target := by
      intro hvleaf
      exact hIso v (mem_largePrimeLeaves.mp hvleaf)
    have hvout : v ∉ largePrimeStarSupport S X Y target := by
      simp [largePrimeStarSupport, hvt, hvleaf]
    rw [restrictEuclideanToFinset_apply, if_neg hvout]
    exact (largePrimeStarDataVector_outside _ _ hvt hvleaf).symm

/-- Uniform canonical up-block identity, including the isolated centres above
the cutoff. -/
theorem restrict_normalizedPrimeStarFirstExit_eq_canonicalUpStar
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmu : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (q : CanonicalUpIndex S X Y c) :
    restrictEuclideanToFinset
        (largePrimeStarSupport S X Y (canonicalUpTarget hS c q))
        (normalizedPrimeStarFirstExit S X Y c) =
      actualUpStarFirstExit S X Y (canonicalUpTarget hS c q) mu
        (largePrimeNormalizedStarMode S X Y c 1 c) := by
  have hqdata := Finset.mem_filter.mp q.property
  have hq : (q : ℕ).Prime := (Nat.mem_primesLE.mp hqdata.1).2
  have hqY : (q : ℕ) ≤ Y := (Nat.mem_primesLE.mp hqdata.1).1
  have hqS : (q : ℕ) ∉ S := hqdata.2.1
  by_cases htargetY : (canonicalUpTarget hS c q : ℕ) ≤ Y
  · exact restrict_normalizedPrimeStarFirstExit_eq_actualUpStar
      hS hcut hc htargetY hd hmu hq hqS hqY (canonicalUpTarget_coe hS c q)
  · exact restrict_normalizedPrimeStarFirstExit_eq_actualUpStar_isolated
      hcut hc (Nat.lt_of_not_ge htargetY) hq hqS hqY
        (canonicalUpTarget_coe hS c q)

/-- An arithmetic down-centre carries the partial-leaf down-star first-exit
vector, with the selected leaf set given by `canonicalDownLeaves`. -/
theorem restrict_normalizedPrimeStarFirstExit_eq_actualDownStar
    {S : Finset ℕ} {X Y q : ℕ} {c target : Vertex S X} {mu : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y) (htargetY : (target : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmu : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ Y)
    (hdown : (target : ℕ) * q = (c : ℕ)) :
    restrictEuclideanToFinset (largePrimeStarSupport S X Y target)
        (normalizedPrimeStarFirstExit S X Y c) =
      actualDownStarFirstExit S X Y target
        (canonicalDownLeaves S X Y target q) mu
        (largePrimeNormalizedStarMode S X Y c 1 c) := by
  ext v
  by_cases hvt : v = target
  · subst v
    have hAdj : (smallPrimeGraph S X Y).Adj c target :=
      smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
        ⟨q, hq, hqS, hqY, Or.inr hdown⟩
    have hb := normalizedPrimeStarFirstExit_apply_eq_starMode_neighbor
      hcut hc (by simp [largePrimeStarSupport]) hAdj
    rw [restrictEuclideanToFinset_apply,
      if_pos (by simp [largePrimeStarSupport]), hb]
    simp [actualDownStarFirstExit]
  · by_cases hvleaf : v ∈ largePrimeLeaves S X Y target
    · obtain ⟨p, hp, hpS, hYp, htp⟩ :=
        (mem_largePrimeLeaves_iff_child htargetY).mp hvleaf
      by_cases hvP : v ∈ canonicalDownLeaves S X Y target q
      · have hvqX : (v : ℕ) * q ≤ X :=
          (Finset.mem_filter.mp hvP).2
        let w : Vertex S X :=
          vertexMulAllowedPrimeOfBound hS v q hq hqS hvqX
        have hwleaf : w ∈ largePrimeLeaves S X Y c := by
          rw [mem_largePrimeLeaves_iff_child hc]
          refine ⟨p, hp, hpS, hYp, ?_⟩
          change (c : ℕ) * p = (v : ℕ) * q
          calc
            (c : ℕ) * p = ((target : ℕ) * q) * p := by rw [hdown]
            _ = ((target : ℕ) * p) * q := by ac_rfl
            _ = (v : ℕ) * q := by rw [htp]
        have hwv : (smallPrimeGraph S X Y).Adj w v := by
          apply smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
          exact ⟨q, hq, hqS, hqY, Or.inr rfl⟩
        have hb := normalizedPrimeStarFirstExit_apply_eq_starMode_neighbor
          hcut hc (by simp [largePrimeStarSupport, hwleaf]) hwv
        have hwcoord :=
          largePrimeNormalizedStarMode_leaf_eq_center_div_sqrt hd hwleaf
        rw [restrictEuclideanToFinset_apply,
          if_pos (by simp [largePrimeStarSupport, hvleaf]), hb, hwcoord, hmu]
        rw [actualDownStarFirstExit,
          largePrimeStarDataVector_leaf _ _ hvleaf, if_pos hvP]
      · have hvNotExit : v ∉ smallPrimeFirstExitSupport S X Y c := by
          intro hvExit
          obtain ⟨w, hwStar, hwv⟩ := mem_smallPrimeFirstExitSupport.mp hvExit
          rw [mem_largePrimeStarSupport] at hwStar
          rcases hwStar with hwc | hcw
          · obtain ⟨ell, hell, _hellS, _hellY, hEdge⟩ :=
              smallPrimeGraph_adj_iff_smallPrimeAdj.mp hwv
            exact no_prime_step_between_primeStepNeighbors
              (Vertex.coe_pos target) (Vertex.coe_pos c) (Vertex.coe_pos v)
              hq hp hell (Or.inl hdown) (Or.inl htp)
                (by simpa [hwc] using hEdge)
          · obtain ⟨r, hr, _hrS, hYr, hcr, hrv⟩ :=
              exists_largePrimeLabel_dvd_of_smallPrimeAdj_child
                (isLargePrimeChild_of_largePrimeAdj_of_le hc hcw) hwv
            have hpv : p ∣ (v : ℕ) := ⟨(target : ℕ), by
              simpa [Nat.mul_comm] using htp.symm⟩
            have hrp : r = p := largePrime_dvd_unique
              (Vertex.coe_pos v) (Vertex.coe_le v) hcut hr hp hYr hYp hrv hpv
            have hvqX : (v : ℕ) * q ≤ X := by
              calc
                (v : ℕ) * q = ((target : ℕ) * p) * q := by rw [htp]
                _ = ((target : ℕ) * q) * p := by ac_rfl
                _ = (c : ℕ) * p := by rw [hdown]
                _ = (c : ℕ) * r := by rw [hrp]
                _ = (w : ℕ) := hcr
                _ ≤ X := Vertex.coe_le w
            exact hvP (Finset.mem_filter.mpr ⟨hvleaf, hvqX⟩)
        have hb0 := normalizedPrimeStarFirstExit_eq_zero_of_not_mem hvNotExit
        rw [restrictEuclideanToFinset_apply,
          if_pos (by simp [largePrimeStarSupport, hvleaf]), hb0]
        rw [actualDownStarFirstExit,
          largePrimeStarDataVector_leaf _ _ hvleaf, if_neg hvP]
    · have hvout : v ∉ largePrimeStarSupport S X Y target := by
        simp [largePrimeStarSupport, hvt, hvleaf]
      rw [restrictEuclideanToFinset_apply, if_neg hvout]
      exact (largePrimeStarDataVector_outside _ _ hvt hvleaf).symm

/-- Uniform canonical down-block identity, indexed by the distinct prime
divisors of the original centre. -/
theorem restrict_normalizedPrimeStarFirstExit_eq_canonicalDownStar
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmu : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (q : CanonicalDownIndex c) :
    restrictEuclideanToFinset
        (largePrimeStarSupport S X Y (canonicalDownTarget c q))
        (normalizedPrimeStarFirstExit S X Y c) =
      actualDownStarFirstExit S X Y (canonicalDownTarget c q)
        (canonicalDownLeaves S X Y (canonicalDownTarget c q) q) mu
        (largePrimeNormalizedStarMode S X Y c 1 c) := by
  have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.property
  have hqDvd : (q : ℕ) ∣ (c : ℕ) := Nat.dvd_of_mem_primeFactors q.property
  have hqS : (q : ℕ) ∉ S := by
    intro hqMem
    exact Vertex.not_dvd_of_mem c hqMem hqDvd
  have hqY : (q : ℕ) ≤ Y :=
    (Nat.le_of_mem_primeFactors q.property).trans hc
  have htargetY : (canonicalDownTarget c q : ℕ) ≤ Y := by
    change (c : ℕ) / q ≤ Y
    exact (Nat.div_le_self _ _).trans hc
  exact restrict_normalizedPrimeStarFirstExit_eq_actualDownStar
    hS hcut hc htargetY hd hmu hq hqS hqY
      (canonicalDownTarget_mul_coe c q)

theorem card_canonicalDownLeaves_eq_boundaryDegree
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (hc : (c : ℕ) ≤ Y)
    (q : CanonicalDownIndex c) :
    (canonicalDownLeaves S X Y (canonicalDownTarget c q) q).card =
      largePrimeStarDegree S X Y c := by
  have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.property
  have htargetY : (canonicalDownTarget c q : ℕ) ≤ Y := by
    change (c : ℕ) / q ≤ Y
    exact (Nat.div_le_self _ _).trans hc
  exact card_canonicalDownLeaves_eq_largePrimeStarDegree
    hS hc htargetY hq (canonicalDownTarget_mul_coe c q)

/-- A single finite type indexing every arithmetic first-exit block.  The left
summand records multiplication by an allowed residual prime; the right
summand records division by a prime factor of the boundary centre. -/
abbrev CanonicalExitIndex
    (S : Finset ℕ) (X Y : ℕ) (c : Vertex S X) :=
  CanonicalUpIndex S X Y c ⊕ CanonicalDownIndex c

/-- The arithmetic centre attached to a tagged first-exit index. -/
def canonicalExitTarget
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X) : CanonicalExitIndex S X Y c → Vertex S X
  | Sum.inl q => canonicalUpTarget hS c q
  | Sum.inr q => canonicalDownTarget c q

@[simp]
theorem canonicalExitTarget_inl
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X) (q : CanonicalUpIndex S X Y c) :
    canonicalExitTarget hS c (Sum.inl q) = canonicalUpTarget hS c q :=
  rfl

@[simp]
theorem canonicalExitTarget_inr
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X) (q : CanonicalDownIndex c) :
    canonicalExitTarget (Y := Y) hS c (Sum.inr q) = canonicalDownTarget c q :=
  rfl

/-- Distinct arithmetic labels give distinct first-exit centres, including
across the up/down split. -/
theorem canonicalExitTarget_injective
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X) : Function.Injective (canonicalExitTarget (Y := Y) hS c) := by
  intro i j hij
  rcases i with q | q <;> rcases j with r | r
  · apply congrArg Sum.inl
    apply Subtype.ext
    have hcoe := congrArg (fun v : Vertex S X ↦ (v : ℕ)) hij
    exact Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos c) (by simpa using hcoe)
  · exfalso
    have hqdata := Finset.mem_filter.mp q.property
    have hqprime : (q : ℕ).Prime := (Nat.mem_primesLE.mp hqdata.1).2
    have hrprime : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.property
    have htarget : canonicalUpTarget hS c q = canonicalDownTarget c r := hij
    have hcoe := congrArg (fun v : Vertex S X ↦ (v : ℕ)) htarget
    have hcancel : (c : ℕ) * ((q : ℕ) * r) = (c : ℕ) * 1 := by
      calc
        (c : ℕ) * ((q : ℕ) * r) = ((c : ℕ) * q) * r := by ac_rfl
        _ = (canonicalUpTarget hS c q : ℕ) * r := by simp
        _ = (canonicalDownTarget c r : ℕ) * r := by rw [hcoe]
        _ = (c : ℕ) := canonicalDownTarget_mul_coe c r
        _ = (c : ℕ) * 1 := by simp
    have hprod : (q : ℕ) * r = 1 :=
      Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos c) hcancel
    exact hqprime.ne_one (Nat.eq_one_of_dvd_one ⟨(r : ℕ), hprod.symm⟩)
  · exfalso
    have htarget : canonicalUpTarget hS c r = canonicalDownTarget c q := hij.symm
    have hrdata := Finset.mem_filter.mp r.property
    have hrprime : (r : ℕ).Prime := (Nat.mem_primesLE.mp hrdata.1).2
    have hqprime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.property
    have hcancel : (c : ℕ) * ((r : ℕ) * q) = (c : ℕ) * 1 := by
      calc
        (c : ℕ) * ((r : ℕ) * q) = ((c : ℕ) * r) * q := by ac_rfl
        _ = (canonicalUpTarget hS c r : ℕ) * q := by simp
        _ = (canonicalDownTarget c q : ℕ) * q := by
          rw [congrArg (fun v : Vertex S X ↦ (v : ℕ)) htarget]
        _ = (c : ℕ) := canonicalDownTarget_mul_coe c q
        _ = (c : ℕ) * 1 := by simp
    have hprod : (r : ℕ) * q = 1 :=
      Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos c) hcancel
    exact hrprime.ne_one (Nat.eq_one_of_dvd_one ⟨(q : ℕ), hprod.symm⟩)
  · apply congrArg Sum.inr
    apply Subtype.ext
    have htarget : canonicalDownTarget c q = canonicalDownTarget c r := hij
    have hcoe := congrArg (fun v : Vertex S X ↦ (v : ℕ)) htarget
    have hcancel : (canonicalDownTarget c q : ℕ) * (q : ℕ) =
        (canonicalDownTarget c q : ℕ) * (r : ℕ) := by
      calc
        (canonicalDownTarget c q : ℕ) * (q : ℕ) = (c : ℕ) :=
          canonicalDownTarget_mul_coe c q
        _ = (canonicalDownTarget c r : ℕ) * (r : ℕ) :=
          (canonicalDownTarget_mul_coe c r).symm
        _ = (canonicalDownTarget c q : ℕ) * (r : ℕ) :=
          congrArg (fun n : ℕ ↦ n * (r : ℕ)) hcoe.symm
    exact Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos (canonicalDownTarget c q)) hcancel

/-- Every down-centre is non-isolated whenever the original boundary star has
positive degree. -/
theorem canonicalDownTarget_not_isolated
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (q : CanonicalDownIndex c) :
    ¬(largePrimeGraph S X Y).IsIsolated (canonicalDownTarget c q) := by
  have hcard : 0 <
      (canonicalDownLeaves S X Y (canonicalDownTarget c q) q).card := by
    rw [card_canonicalDownLeaves_eq_boundaryDegree hS hc q]
    exact hd
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
  have hvleaf : v ∈ largePrimeLeaves S X Y (canonicalDownTarget c q) :=
    canonicalDownLeaves_subset_largePrimeLeaves _ hv
  intro hiso
  exact hiso v (mem_largePrimeLeaves.mp hvleaf)

/-- Every canonical arithmetic centre is either a lower star centre or an
isolated large-prime vertex. -/
theorem canonicalExitTarget_le_or_isolated
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (i : CanonicalExitIndex S X Y c) :
    (canonicalExitTarget hS c i : ℕ) ≤ Y ∨
      (largePrimeGraph S X Y).IsIsolated (canonicalExitTarget hS c i) := by
  rcases i with q | q
  · by_cases hqY : (canonicalUpTarget hS c q : ℕ) ≤ Y
    · exact Or.inl hqY
    · have hqdata := Finset.mem_filter.mp q.property
      exact Or.inr (canonicalUpTarget_isIsolated_of_cutoff_lt hc hcut
        (Nat.mem_primesLE.mp hqdata.1).2 (Nat.mem_primesLE.mp hqdata.1).1
        (canonicalUpTarget_coe hS c q) (Nat.lt_of_not_ge hqY))
  · exact Or.inl (by
      change (c : ℕ) / q ≤ Y
      exact (Nat.div_le_self _ _).trans hc)

/-- Closed stars attached to distinct canonical arithmetic labels are
pairwise disjoint, including the isolated up-centres above the cutoff. -/
theorem disjoint_canonicalExitTarget_starSupport
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    {i j : CanonicalExitIndex S X Y c} (hij : i ≠ j) :
    Disjoint
      (largePrimeStarSupport S X Y (canonicalExitTarget hS c i))
      (largePrimeStarSupport S X Y (canonicalExitTarget hS c j)) := by
  have htij : canonicalExitTarget hS c i ≠ canonicalExitTarget hS c j :=
    fun h ↦ hij (canonicalExitTarget_injective hS c h)
  rcases canonicalExitTarget_le_or_isolated hS hcut hc i with hiY | hiIso
  · rcases canonicalExitTarget_le_or_isolated hS hcut hc j with hjY | hjIso
    · exact disjoint_largePrimeStarSupport hcut hiY hjY htij
    · rw [Finset.disjoint_left]
      intro v hvi hvj
      rw [mem_largePrimeStarSupport] at hvj
      rcases hvj with rfl | hjv
      · rw [mem_largePrimeStarSupport] at hvi
        rcases hvi with hEq | hijAdj
        · exact htij hEq.symm
        · exact hjIso _ (largePrimeAdj_symm hijAdj)
      · exact hjIso _ hjv
  · rw [Finset.disjoint_left]
    intro v hvi hvj
    rw [mem_largePrimeStarSupport] at hvi
    rcases hvi with rfl | hiv
    · rw [mem_largePrimeStarSupport] at hvj
      rcases hvj with hEq | hjiAdj
      · exact htij hEq
      · exact hiIso _ (largePrimeAdj_symm hjiAdj)
    · exact hiIso _ hiv

/-- Every literal first-exit coordinate lies in one of the canonical
arithmetic up/down star supports. -/
theorem exists_canonicalExitIndex_of_mem_smallPrimeFirstExitSupport
    {S : Finset ℕ} {X Y : ℕ} {c v : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hv : v ∈ smallPrimeFirstExitSupport S X Y c) :
    ∃ i : CanonicalExitIndex S X Y c,
      v ∈ largePrimeStarSupport S X Y (canonicalExitTarget hS c i) := by
  have hvCompression :=
    smallPrimeFirstExitSupport_subset_firstExitCompressionSupport hcut hv
  rcases Finset.mem_union.mp hvCompression with hvStars | hvIso
  · obtain ⟨k, hkC, hvk⟩ := mem_largePrimeStarUnionSupport.mp hvStars
    obtain ⟨q, hq, hqS, hqY, hup | hdown⟩ :=
      mem_firstExitLowerCenters_arithmetic hcut hc hkC
    · have hqMem : q ∈ canonicalUpPrimeLabels S X Y c := by
        apply Finset.mem_filter.mpr
        refine ⟨Nat.mem_primesLE.mpr ⟨hqY, hq⟩, hqS, ?_⟩
        rw [hup]
        exact Vertex.coe_le k
      let qi : CanonicalUpIndex S X Y c := ⟨q, hqMem⟩
      have htarget : canonicalUpTarget hS c qi = k := by
        apply Subtype.ext
        apply Fin.ext
        exact hup
      refine ⟨Sum.inl qi, ?_⟩
      simpa [htarget] using hvk
    · have hqDvd : q ∣ (c : ℕ) := ⟨(k : ℕ), by
          simpa [Nat.mul_comm] using hdown.symm⟩
      have hqMem : q ∈ (c : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, hqDvd, (Vertex.coe_pos c).ne'⟩
      let qi : CanonicalDownIndex c := ⟨q, hqMem⟩
      have htarget : canonicalDownTarget c qi = k := by
        apply Subtype.ext
        apply Fin.ext
        apply Nat.eq_of_mul_eq_mul_right hq.pos
        calc
          (canonicalDownTarget c qi : ℕ) * q = (c : ℕ) :=
            canonicalDownTarget_mul_coe c qi
          _ = (k : ℕ) * q := hdown.symm
      refine ⟨Sum.inr qi, ?_⟩
      simpa [htarget] using hvk
  · obtain ⟨q, hq, hqS, hqY, hup | hdown⟩ :=
      mem_firstExitIsolatedVertices_arithmetic hS hc hvIso
    · have hqMem : q ∈ canonicalUpPrimeLabels S X Y c := by
        apply Finset.mem_filter.mpr
        exact ⟨Nat.mem_primesLE.mpr ⟨hqY, hq⟩, hqS,
          hup.trans_le (Vertex.coe_le v)⟩
      let qi : CanonicalUpIndex S X Y c := ⟨q, hqMem⟩
      have htarget : canonicalUpTarget hS c qi = v := by
        apply Subtype.ext
        apply Fin.ext
        exact hup
      refine ⟨Sum.inl qi, ?_⟩
      simp [htarget, largePrimeStarSupport]
    · have hqDvd : q ∣ (c : ℕ) := ⟨(v : ℕ), by
          simpa [Nat.mul_comm] using hdown.symm⟩
      have hqMem : q ∈ (c : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, hqDvd, (Vertex.coe_pos c).ne'⟩
      let qi : CanonicalDownIndex c := ⟨q, hqMem⟩
      have htarget : canonicalDownTarget c qi = v := by
        apply Subtype.ext
        apply Fin.ext
        apply Nat.eq_of_mul_eq_mul_right hq.pos
        calc
          (canonicalDownTarget c qi : ℕ) * q = (c : ℕ) :=
            canonicalDownTarget_mul_coe c qi
          _ = (v : ℕ) * q := hdown.symm
      exfalso
      exact canonicalDownTarget_not_isolated hS hc hd qi
        (htarget ▸ (mem_firstExitIsolatedVertices.mp hvIso).2)

/-- Any vector supported on the literal first-exit set is the direct sum of
its canonical arithmetic up/down star restrictions. -/
theorem euclidean_eq_sum_canonicalExitStarBlocks
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (b : EuclideanSpace ℝ (Vertex S X))
    (hb : ∀ v, v ∉ smallPrimeFirstExitSupport S X Y c → b v = 0) :
    b = ∑ i : CanonicalExitIndex S X Y c,
      restrictEuclideanToFinset
        (largePrimeStarSupport S X Y (canonicalExitTarget hS c i)) b := by
  classical
  ext v
  change b v = EuclideanSpace.projₗ v
    (∑ i : CanonicalExitIndex S X Y c,
      restrictEuclideanToFinset
        (largePrimeStarSupport S X Y (canonicalExitTarget hS c i)) b)
  rw [map_sum]
  change b v = ∑ i : CanonicalExitIndex S X Y c,
    if v ∈ largePrimeStarSupport S X Y (canonicalExitTarget hS c i) then b v else 0
  by_cases hbv : b v = 0
  · simp [hbv]
  · have hvExit : v ∈ smallPrimeFirstExitSupport S X Y c := by
      by_contra hv
      exact hbv (hb v hv)
    obtain ⟨i, hvi⟩ :=
      exists_canonicalExitIndex_of_mem_smallPrimeFirstExitSupport
        hS hcut hc hd hvExit
    symm
    let f := fun j : CanonicalExitIndex S X Y c ↦
      if v ∈ largePrimeStarSupport S X Y (canonicalExitTarget hS c j) then b v else 0
    change (∑ j, f j) = b v
    have hfi : f i = b v := by
      dsimp [f]
      rw [if_pos hvi]
    rw [← hfi]
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _hj hji
      have hvj : v ∉
          largePrimeStarSupport S X Y (canonicalExitTarget hS c j) := by
        intro hvj
        exact (Finset.disjoint_left.mp
          (disjoint_canonicalExitTarget_starSupport hS hcut hc hji)) hvj hvi
      dsimp [f]
      rw [if_neg hvj]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))

/-- The normalized first-exit source is exactly the sum of the manuscript's
canonical up-star and down-star vectors. -/
theorem normalizedPrimeStarFirstExit_eq_sum_canonicalBlocks
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmu : mu = √(largePrimeStarDegree S X Y c : ℝ)) :
    normalizedPrimeStarFirstExit S X Y c =
      (∑ q : CanonicalUpIndex S X Y c,
        actualUpStarFirstExit S X Y (canonicalUpTarget hS c q) mu
          (largePrimeNormalizedStarMode S X Y c 1 c)) +
      (∑ q : CanonicalDownIndex c,
        actualDownStarFirstExit S X Y (canonicalDownTarget c q)
          (canonicalDownLeaves S X Y (canonicalDownTarget c q) q) mu
          (largePrimeNormalizedStarMode S X Y c 1 c)) := by
  calc
    normalizedPrimeStarFirstExit S X Y c =
        ∑ i : CanonicalExitIndex S X Y c,
          restrictEuclideanToFinset
            (largePrimeStarSupport S X Y (canonicalExitTarget hS c i))
            (normalizedPrimeStarFirstExit S X Y c) :=
      euclidean_eq_sum_canonicalExitStarBlocks hS hcut hc hd _
        (fun v hv ↦ normalizedPrimeStarFirstExit_eq_zero_of_not_mem hv)
    _ =
        (∑ q : CanonicalUpIndex S X Y c,
          restrictEuclideanToFinset
            (largePrimeStarSupport S X Y (canonicalUpTarget hS c q))
            (normalizedPrimeStarFirstExit S X Y c)) +
        (∑ q : CanonicalDownIndex c,
          restrictEuclideanToFinset
            (largePrimeStarSupport S X Y (canonicalDownTarget c q))
            (normalizedPrimeStarFirstExit S X Y c)) := by
      exact Fintype.sum_sum_type _
    _ = _ := by
      congr 1
      · apply Finset.sum_congr rfl
        intro q _hq
        exact restrict_normalizedPrimeStarFirstExit_eq_canonicalUpStar
          hS hcut hc hd hmu q
      · apply Finset.sum_congr rfl
        intro q _hq
        exact restrict_normalizedPrimeStarFirstExit_eq_canonicalDownStar
          hS hcut hc hd hmu q

/-- Every canonical arithmetic centre is itself a literal first exit. -/
theorem canonicalExitTarget_mem_smallPrimeFirstExitSupport
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hc : (c : ℕ) ≤ Y)
    (i : CanonicalExitIndex S X Y c) :
    canonicalExitTarget hS c i ∈ smallPrimeFirstExitSupport S X Y c := by
  rw [mem_smallPrimeFirstExitSupport]
  refine ⟨c, by simp [largePrimeStarSupport], ?_⟩
  rcases i with q | q
  · have hqdata := Finset.mem_filter.mp q.property
    apply smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
    exact ⟨q, (Nat.mem_primesLE.mp hqdata.1).2, hqdata.2.1,
      (Nat.mem_primesLE.mp hqdata.1).1,
      Or.inl (canonicalUpTarget_coe hS c q)⟩
  · have hqprime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.property
    have hqDvd : (q : ℕ) ∣ (c : ℕ) := Nat.dvd_of_mem_primeFactors q.property
    have hqS : (q : ℕ) ∉ S := by
      intro hqMem
      exact Vertex.not_dvd_of_mem c hqMem hqDvd
    apply smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
    exact ⟨q, hqprime, hqS,
      (Nat.le_of_mem_primeFactors q.property).trans hc,
      Or.inr (canonicalDownTarget_mul_coe c q)⟩

/-- Every canonical target contributes either one selected non-isolated lower
star or one isolated coordinate in the canonical first-exit compression. -/
theorem canonicalExitTarget_mem_lower_or_isolated
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (i : CanonicalExitIndex S X Y c) :
    canonicalExitTarget hS c i ∈ firstExitLowerCenters S X Y c ∨
      canonicalExitTarget hS c i ∈ firstExitIsolatedVertices S X Y c := by
  let target := canonicalExitTarget hS c i
  have htargetExit : target ∈ smallPrimeFirstExitSupport S X Y c :=
    canonicalExitTarget_mem_smallPrimeFirstExitSupport hS hc i
  by_cases hiso : (largePrimeGraph S X Y).IsIsolated target
  · exact Or.inr (mem_firstExitIsolatedVertices.mpr ⟨htargetExit, hiso⟩)
  · have htargetY : (target : ℕ) ≤ Y := by
      rcases canonicalExitTarget_le_or_isolated hS hcut hc i with h | h
      · exact h
      · exact False.elim (hiso h)
    have hself : target ∈ largePrimeStarSupport S X Y target := by
      simp [largePrimeStarSupport]
    exact Or.inl (mem_firstExitLowerCenters.mpr
      ⟨htargetY, target, htargetExit, hiso, hself⟩)

/-- Every canonical closed star is contained in the canonical first-exit
compression.  In the isolated case the closed star is just its centre. -/
theorem canonicalExitTarget_starSupport_subset_firstExitCompression
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (i : CanonicalExitIndex S X Y c) :
    largePrimeStarSupport S X Y (canonicalExitTarget hS c i) ⊆
      firstExitCompressionSupport S X Y c := by
  intro v hv
  rcases canonicalExitTarget_mem_lower_or_isolated hS hcut hc i with hLower | hIso
  · apply Finset.mem_union_left
    exact mem_largePrimeStarUnionSupport.mpr
      ⟨canonicalExitTarget hS c i, hLower, hv⟩
  · have hiso := (mem_firstExitIsolatedVertices.mp hIso).2
    rw [mem_largePrimeStarSupport] at hv
    rcases hv with rfl | hvAdj
    · exact Finset.mem_union_right _ hIso
    · exact False.elim (hiso v hvAdj)

/-- On an isolated target, the displayed up-star resolver is simply division
of its source by the spectral parameter. -/
theorem actualUpStarResolvent_eq_inv_smul_of_isolated
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X} {mu c0 : ℝ}
    (hiso : (largePrimeGraph S X Y).IsIsolated target) (hmu : mu ≠ 0) :
    actualUpStarResolvent S X Y target mu c0 =
      mu⁻¹ • actualUpStarFirstExit S X Y target mu c0 := by
  have hd0 : largePrimeStarDegree S X Y target = 0 :=
    largePrimeStarDegree_eq_zero_iff.mpr hiso
  ext v
  by_cases hvt : v = target
  · subst v
    rw [actualUpStarResolvent, actualUpStarFirstExit, hd0]
    simp only [Nat.cast_zero, add_zero, sub_zero, PiLp.smul_apply,
      largePrimeStarDataVector_center]
    simp only [smul_eq_mul]
    field_simp [hmu]
  · have hvleaf : v ∉ largePrimeLeaves S X Y target := by
      intro hvleaf
      exact hiso v (mem_largePrimeLeaves.mp hvleaf)
    rw [actualUpStarResolvent, actualUpStarFirstExit, hd0]
    simp only [PiLp.smul_apply]
    rw [largePrimeStarDataVector_outside _ _ hvt hvleaf,
      largePrimeStarDataVector_outside _ _ hvt hvleaf]
    simp

/-- The isolated up-star resolver satisfies the same shifted equation as the
non-isolated local formulas. -/
theorem actualUpStar_shift_resolvent_of_isolated
    {S : Finset ℕ} {X Y : ℕ} {target : Vertex S X} {mu c0 : ℝ}
    (hiso : (largePrimeGraph S X Y).IsIsolated target) (hmu : mu ≠ 0) :
    mu • actualUpStarResolvent S X Y target mu c0 -
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (actualUpStarResolvent S X Y target mu c0) =
      actualUpStarFirstExit S X Y target mu c0 := by
  have hEq : actualUpStarResolvent S X Y target mu c0 =
      mu⁻¹ • actualUpStarFirstExit S X Y target mu c0 :=
    actualUpStarResolvent_eq_inv_smul_of_isolated hiso hmu
  have hsupp : actualUpStarFirstExit S X Y target mu c0 =
      restrictEuclideanToFinset {target}
        (actualUpStarFirstExit S X Y target mu c0) := by
    ext v
    by_cases hvt : v = target
    · subst v
      simp
    · have hvleaf : v ∉ largePrimeLeaves S X Y target := by
        intro hvleaf
        exact hiso v (mem_largePrimeLeaves.mp hvleaf)
      rw [restrictEuclideanToFinset_apply]
      have hvnot : v ∉ ({target} : Finset (Vertex S X)) := by simpa using hvt
      rw [if_neg hvnot]
      exact largePrimeStarDataVector_outside _ _ hvt hvleaf
  have hLsource :
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (actualUpStarFirstExit S X Y target mu c0) = 0 := by
    rw [hsupp]
    apply largePrime_toEuclideanLin_restrict_isolated_eq_zero
    intro v hv
    have hvt : v = target := Finset.mem_singleton.mp hv
    simpa [hvt] using hiso
  rw [hEq, map_smul, hLsource, smul_zero, sub_zero, smul_smul]
  field_simp [hmu]
  simp

/-- Tagged form of the canonical first-exit source. -/
def canonicalExitFirstExit
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X) (mu c0 : ℝ) :
    CanonicalExitIndex S X Y c → EuclideanSpace ℝ (Vertex S X)
  | Sum.inl q => actualUpStarFirstExit S X Y (canonicalUpTarget hS c q) mu c0
  | Sum.inr q => actualDownStarFirstExit S X Y (canonicalDownTarget c q)
      (canonicalDownLeaves S X Y (canonicalDownTarget c q) q) mu c0

/-- Tagged form of the canonical local resolvents. -/
def canonicalExitResolvent
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (c : Vertex S X) (mu c0 : ℝ) :
    CanonicalExitIndex S X Y c → EuclideanSpace ℝ (Vertex S X)
  | Sum.inl q => actualUpStarResolvent S X Y (canonicalUpTarget hS c q) mu c0
  | Sum.inr q => actualDownStarResolvent S X Y (canonicalDownTarget c q)
      (canonicalDownLeaves S X Y (canonicalDownTarget c q) q) mu c0

/-- Each canonical local resolver satisfies its exact shifted large-prime
equation. -/
theorem canonicalExit_shift_resolvent
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu c0 : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hmu : mu ≠ 0)
    (hupden : ∀ q : CanonicalUpIndex S X Y c,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ))
    (hdownden : ∀ q : CanonicalDownIndex c,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ))
    (i : CanonicalExitIndex S X Y c) :
    mu • canonicalExitResolvent hS c mu c0 i -
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
        (canonicalExitResolvent hS c mu c0 i) =
      canonicalExitFirstExit hS c mu c0 i := by
  rcases i with q | q
  · by_cases htargetY : (canonicalUpTarget hS c q : ℕ) ≤ Y
    · exact actualUpStar_shift_resolvent hcut htargetY hmu (hupden q)
    · have hqdata := Finset.mem_filter.mp q.property
      have hiso := canonicalUpTarget_isIsolated_of_cutoff_lt hc hcut
        (Nat.mem_primesLE.mp hqdata.1).2 (Nat.mem_primesLE.mp hqdata.1).1
        (canonicalUpTarget_coe hS c q).symm (Nat.lt_of_not_ge htargetY)
      exact actualUpStar_shift_resolvent_of_isolated hiso hmu
  · have htargetY : (canonicalDownTarget c q : ℕ) ≤ Y := by
      change (c : ℕ) / q ≤ Y
      exact (Nat.div_le_self _ _).trans hc
    have hP := canonicalDownLeaves_subset_largePrimeLeaves
      (S := S) (X := X) (Y := Y) (q := (q : ℕ)) (canonicalDownTarget c q)
    have hcardNat := card_canonicalDownLeaves_eq_boundaryDegree hS hc q
    have hmuSq : mu ^ 2 = (largePrimeStarDegree S X Y c : ℝ) := by
      rw [hmuval, Real.sq_sqrt]
      positivity
    have hcard :
        ((canonicalDownLeaves S X Y (canonicalDownTarget c q) q).card : ℝ) =
          mu ^ 2 := by
      rw [hcardNat, hmuSq]
    exact actualDownStar_shift_resolvent hcut htargetY hP hcard hmu (hdownden q)

/-- Every canonical local resolver is supported on its own closed star. -/
theorem canonicalExitResolvent_eq_zero_of_not_mem_starSupport
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu c0 : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (i : CanonicalExitIndex S X Y c) {v : Vertex S X}
    (hv : v ∉ largePrimeStarSupport S X Y (canonicalExitTarget hS c i)) :
    canonicalExitResolvent hS c mu c0 i v = 0 := by
  have hvt : v ≠ canonicalExitTarget hS c i := by
    intro h
    apply hv
    simp [h, largePrimeStarSupport]
  have hvleaf : v ∉ largePrimeLeaves S X Y (canonicalExitTarget hS c i) := by
    intro h
    apply hv
    simp [largePrimeStarSupport, h]
  rcases i with q | q
  · exact largePrimeStarDataVector_outside _ _ hvt hvleaf
  · exact largePrimeStarDataVector_outside _ _ hvt hvleaf

/-- The sum of the canonical local resolvents is supported on the exact
first-exit compression. -/
theorem sum_canonicalExitResolvent_eq_zero_of_not_mem_compression
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu c0 : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    {v : Vertex S X} (hv : v ∉ firstExitCompressionSupport S X Y c) :
    (∑ i : CanonicalExitIndex S X Y c,
      canonicalExitResolvent hS c mu c0 i) v = 0 := by
  classical
  change EuclideanSpace.projₗ v
    (∑ i : CanonicalExitIndex S X Y c,
      canonicalExitResolvent hS c mu c0 i) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  apply canonicalExitResolvent_eq_zero_of_not_mem_starSupport hS i
  intro hvi
  exact hv (canonicalExitTarget_starSupport_subset_firstExitCompression
    hS hcut hc i hvi)

/-- A positive compression gap rules out resonance with every canonical star
degree.  Thus the local denominator conditions are consequences of the actual
graph gap, not additional arithmetic assumptions. -/
theorem canonicalExitTarget_degree_ne_of_compressionGap
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu gamma : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖)
    (i : CanonicalExitIndex S X Y c) :
    mu ^ 2 ≠
      (largePrimeStarDegree S X Y (canonicalExitTarget hS c i) : ℝ) := by
  intro heq
  have hmuPos : 0 < mu := by
    rw [hmuval]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  rcases canonicalExitTarget_le_or_isolated hS hcut hc i with htargetY | hiso
  · have htargetDeg : 0 <
        largePrimeStarDegree S X Y (canonicalExitTarget hS c i) := by
      have hcast : 0 <
          (largePrimeStarDegree S X Y (canonicalExitTarget hS c i) : ℝ) := by
        rw [← heq]
        positivity
      exact_mod_cast hcast
    let u := largePrimeNormalizedStarMode S X Y
      (canonicalExitTarget hS c i) 1
    have hsqrtEq :
        √(largePrimeStarDegree S X Y (canonicalExitTarget hS c i) : ℝ) = mu := by
      have hsqrtNonneg : 0 ≤
          √(largePrimeStarDegree S X Y (canonicalExitTarget hS c i) : ℝ) :=
        Real.sqrt_nonneg _
      have hsqrtSq :
          (√(largePrimeStarDegree S X Y (canonicalExitTarget hS c i) : ℝ)) ^ 2 =
            (largePrimeStarDegree S X Y (canonicalExitTarget hS c i) : ℝ) :=
        Real.sq_sqrt (by positivity)
      nlinarith
    have hLu :
        Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) u = mu • u := by
      dsimp [u]
      rw [largePrime_toEuclideanLin_normalizedStarMode hcut htargetY (by norm_num),
        hsqrtEq]
      simp
    have huSupport : ∀ v,
        v ∉ firstExitCompressionSupport S X Y c → u v = 0 := by
      intro v hv
      apply largePrimeNormalizedStarMode_eq_zero_of_not_mem
      intro hvStar
      exact hv (canonicalExitTarget_starSupport_subset_firstExitCompression
        hS hcut hc i hvStar)
    have hcompression : firstExitLargePrimeCompressionOperator S X Y c u =
        Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) u :=
      firstExitLargePrimeCompressionOperator_eq_of_supported hcut u huSupport
    have hgapU := hgap u
    rw [hcompression, hLu, sub_self, norm_zero,
      norm_largePrimeNormalizedStarMode htargetDeg] at hgapU
    linarith
  · have hd0 : largePrimeStarDegree S X Y
        (canonicalExitTarget hS c i) = 0 :=
      largePrimeStarDegree_eq_zero_iff.mpr hiso
    rw [hd0, Nat.cast_zero] at heq
    nlinarith

/-- The compression inverse supplied by a spectral gap equals the explicit
sum of all canonical up/down local resolvents. -/
theorem firstExitLargePrimeResolventOfGap_eq_sum_canonicalResolvents
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X} {mu gamma : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hgamma : 0 < gamma)
    (hgap : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gamma * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖) :
    firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap
        (normalizedPrimeStarFirstExit S X Y c) =
      (∑ q : CanonicalUpIndex S X Y c,
        actualUpStarResolvent S X Y (canonicalUpTarget hS c q) mu
          (largePrimeNormalizedStarMode S X Y c 1 c)) +
      (∑ q : CanonicalDownIndex c,
        actualDownStarResolvent S X Y (canonicalDownTarget c q)
          (canonicalDownLeaves S X Y (canonicalDownTarget c q) q) mu
          (largePrimeNormalizedStarMode S X Y c 1 c)) := by
  classical
  let c0 := largePrimeNormalizedStarMode S X Y c 1 c
  let x := ∑ i : CanonicalExitIndex S X Y c,
    canonicalExitResolvent hS c mu c0 i
  have hmu : mu ≠ 0 := by
    rw [hmuval]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hupden : ∀ q : CanonicalUpIndex S X Y c,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ) := by
    intro q
    exact canonicalExitTarget_degree_ne_of_compressionGap
      hS hcut hc hd hmuval hgamma hgap (Sum.inl q)
  have hdownden : ∀ q : CanonicalDownIndex c,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ) := by
    intro q
    exact canonicalExitTarget_degree_ne_of_compressionGap
      hS hcut hc hd hmuval hgamma hgap (Sum.inr q)
  have hsolveFull :
      mu • x - Matrix.toEuclideanLin
          ((largePrimeGraph S X Y).adjMatrix ℝ) x =
        normalizedPrimeStarFirstExit S X Y c := by
    have hsum :
        mu • x - Matrix.toEuclideanLin
            ((largePrimeGraph S X Y).adjMatrix ℝ) x =
          ∑ i : CanonicalExitIndex S X Y c,
            canonicalExitFirstExit hS c mu c0 i := by
      dsimp [x]
      rw [Finset.smul_sum, map_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      exact canonicalExit_shift_resolvent hS hcut hc hd hmuval hmu
        hupden hdownden i
    rw [hsum]
    rw [normalizedPrimeStarFirstExit_eq_sum_canonicalBlocks
      hS hcut hc hd hmuval]
    simp only [Fintype.sum_sum_type, canonicalExitFirstExit, c0]
  have hxSupport : ∀ v,
      v ∉ firstExitCompressionSupport S X Y c → x v = 0 := by
    intro v hv
    exact sum_canonicalExitResolvent_eq_zero_of_not_mem_compression
      hS hcut hc hv
  have hcompression : firstExitLargePrimeCompressionOperator S X Y c x =
      Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ) x :=
    firstExitLargePrimeCompressionOperator_eq_of_supported hcut x hxSupport
  have hsolve :
      mu • x - firstExitLargePrimeCompressionOperator S X Y c x =
        normalizedPrimeStarFirstExit S X Y c := by
    rw [hcompression]
    exact hsolveFull
  calc
    firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap
        (normalizedPrimeStarFirstExit S X Y c) =
        firstExitLargePrimeResolventOfGap S X Y c mu gamma hgamma hgap
          (mu • x - firstExitLargePrimeCompressionOperator S X Y c x) := by
            rw [hsolve]
    _ = x := firstExitLargePrimeResolventOfGap_shift_apply
      S X Y c mu gamma hgamma hgap x
    _ = _ := Fintype.sum_sum_type _

/-- If the entire residual-prime range can multiply the centre without
leaving the finite graph, the canonical up-label set is exactly the set of
allowed primes at most the cutoff. -/
theorem canonicalUpPrimeLabels_eq_allowedPrimeSet
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcY : (c : ℕ) * Y ≤ X) :
    canonicalUpPrimeLabels S X Y c =
      (Nat.primesLE Y).filter fun q ↦ q ∉ S := by
  ext q
  constructor
  · intro hq
    have h := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨h.1, h.2.1⟩
  · intro hq
    have h := Finset.mem_filter.mp hq
    have hqY := (Nat.mem_primesLE.mp h.1).1
    apply Finset.mem_filter.mpr
    exact ⟨h.1, h.2, (Nat.mul_le_mul_left (c : ℕ) hqY).trans hcY⟩

theorem card_canonicalUpPrimeLabels_eq_allowedPrimeCount
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcY : (c : ℕ) * Y ≤ X) :
    (canonicalUpPrimeLabels S X Y c).card = allowedPrimeCount S Y := by
  rw [canonicalUpPrimeLabels_eq_allowedPrimeSet hcY]
  rfl

theorem card_univ_canonicalUpIndex_eq_allowedPrimeCount
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hcY : (c : ℕ) * Y ≤ X) :
    (Finset.univ : Finset (CanonicalUpIndex S X Y c)).card =
      allowedPrimeCount S Y := by
  rw [Finset.card_univ, Fintype.card_coe,
    card_canonicalUpPrimeLabels_eq_allowedPrimeCount hcY]

/-- Monotonicity of the allowed-prime counting function. -/
theorem allowedPrimeCount_mono {S : Finset ℕ} {M N : ℕ} (hMN : M ≤ N) :
    allowedPrimeCount S M ≤ allowedPrimeCount S N := by
  apply Finset.card_le_card
  intro p hp
  have h := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_primesLE.mpr
    ⟨(Nat.mem_primesLE.mp h.1).1.trans hMN, (Nat.mem_primesLE.mp h.1).2⟩, h.2⟩

/-- The real-valued boundary-star degree identity used by the final finite
remainder theorem. -/
theorem sq_sqrt_largePrimeStarDegree_eq_allowedPrimeDifference
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (hc : (c : ℕ) ≤ Y)
    (hYXc : Y ≤ X / (c : ℕ)) :
    (√(largePrimeStarDegree S X Y c : ℝ)) ^ 2 =
      (allowedPrimeCount S (X / (c : ℕ)) : ℝ) -
        (allowedPrimeCount S Y : ℝ) := by
  have hcount := allowedPrimeCount_mono (S := S) hYXc
  rw [Real.sq_sqrt (by positivity),
    largePrimeStarDegree_eq_allowedPrimeCount_sub hS c hc hYXc]
  rw [Nat.cast_sub hcount]

/-- Canonical finite remainder comparison consumed by Theorem 8.7. All
arithmetic block sets, their source decomposition, their local resolvents,
disjointness, leaf counts, and the boundary-degree identity are constructed
internally from the actual prime-cover graph. The theorem remains conditional
on a matched actual eigenpair and explicit spectral-gap, residual-norm,
contraction, and displacement estimates; it does not prove the manuscript's
`O(1 / log X)` evaluation of the displayed error. -/
theorem actualFinitePrimeStarRemainder_canonical
    {S : Finset ℕ} {X Y : ℕ} {c : Vertex S X}
    (v : EuclideanSpace ℝ (Vertex S X))
    (lam mu shiftBound gammaB gammaLam gammaMu gammaU gammaW eta : ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (hlower : Y * Y ≤ X) (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (hmuval : mu = √(largePrimeStarDegree S X Y c : ℝ))
    (hAv : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) v = lam • v)
    (halphaMode : ⟪largePrimeNormalizedStarMode S X Y c 1, v⟫_ℝ ≠ 0)
    (hgammaB : 0 < gammaB) (hgammaLam : 0 < gammaLam)
    (hgammaMu : 0 < gammaMu) (hgammaU : 0 < gammaU)
    (hgammaW : 0 < gammaW) (heta : 0 ≤ eta)
    (hgapLam : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaLam * ‖x‖ ≤
        ‖lam • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hgapMu : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaMu * ‖x‖ ≤
        ‖mu • x - primeStarInteriorPrimeCoverOperator S X Y c x‖)
    (hgapU : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaU * ‖x‖ ≤
        ‖mu • x - firstExitLargePrimeCompressionOperator S X Y c x‖)
    (hgapW : ∀ x : EuclideanSpace ℝ (Vertex S X),
      gammaW * ‖x‖ ≤
        ‖mu • x - firstExitComplementPrimeCoverOperator S X Y c x‖)
    (hboundaryGap : gammaB *
        ‖normalizedPrimeStarBoundaryRemainder S X Y c v‖ ≤
      ‖lam • normalizedPrimeStarBoundaryRemainder S X Y c v -
        primeStarBoundaryPrimeCoverOperator S X Y c
          (normalizedPrimeStarBoundaryRemainder S X Y c v)‖)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (hsmallBoundary : gammaB⁻¹ * eta * gammaLam⁻¹ * eta ≤ 1 / 2)
    (hsmallUW : gammaU⁻¹ * (eta * gammaW⁻¹ * eta) ≤ 1 / 2)
    (hshift : |lam - mu| ≤ shiftBound) (hshift0 : 0 ≤ shiftBound) :
    let b := normalizedPrimeStarFirstExit S X Y c
    let Rlam := primeStarInteriorResolventOfGap
      S X Y c lam gammaLam hgammaLam hgapLam
    let Rmu := primeStarInteriorResolventOfGap
      S X Y c mu gammaMu hgammaMu hgapMu
    let RU := firstExitLargePrimeResolventOfGap
      S X Y c mu gammaU hgammaU hgapU
    let errBound :=
      2 * (gammaB⁻¹ * eta * eta) * ‖Rlam b‖ ^ 2 +
        |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖ +
      2 * (eta * gammaW⁻¹ * eta) * ‖RU b‖ ^ 2
    |(lam ^ 2 - (allowedPrimeCount S (X / (c : ℕ)) : ℝ)) -
      finiteStarCorrection
        (Finset.univ : Finset (CanonicalUpIndex S X Y c))
        (Finset.univ : Finset (CanonicalDownIndex c))
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ) /
          mu ^ 2)
        (fun q ↦ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ) /
          mu ^ 2)| ≤
      2 * |mu| * errBound + shiftBound ^ 2 := by
  dsimp only
  let U : Finset (CanonicalUpIndex S X Y c) := Finset.univ
  let Dset : Finset (CanonicalDownIndex c) := Finset.univ
  let upTarget := fun q : CanonicalUpIndex S X Y c ↦ canonicalUpTarget hS c q
  let downTarget := fun q : CanonicalDownIndex c ↦ canonicalDownTarget c q
  let downLeaves := fun q : CanonicalDownIndex c ↦
    canonicalDownLeaves S X Y (canonicalDownTarget c q) q
  let c0 := largePrimeNormalizedStarMode S X Y c 1 c
  have hcY : (c : ℕ) * Y ≤ X := by
    exact (Nat.mul_le_mul_right Y hc).trans hlower
  have hYXc : Y ≤ X / (c : ℕ) := by
    apply (Nat.le_div_iff_mul_le (Vertex.coe_pos c)).2
    simpa [Nat.mul_comm] using hcY
  have hc0 : c0 ^ 2 = 1 / 2 := by
    exact sq_largePrimeNormalizedStarMode_center (by norm_num) hd
  have hupden : ∀ q : CanonicalUpIndex S X Y c,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (canonicalUpTarget hS c q) : ℝ) := by
    intro q
    exact canonicalExitTarget_degree_ne_of_compressionGap
      hS hcut hc hd hmuval hgammaU hgapU (Sum.inl q)
  have hdownden : ∀ q : CanonicalDownIndex c,
      mu ^ 2 ≠ (largePrimeStarDegree S X Y (canonicalDownTarget c q) : ℝ) := by
    intro q
    exact canonicalExitTarget_degree_ne_of_compressionGap
      hS hcut hc hd hmuval hgammaU hgapU (Sum.inr q)
  have hdownLeaves : ∀ q ∈ Dset,
      downLeaves q ⊆ largePrimeLeaves S X Y (downTarget q) := by
    intro q _hq
    exact canonicalDownLeaves_subset_largePrimeLeaves _
  have hdownCard : ∀ q ∈ Dset, ((downLeaves q).card : ℝ) = mu ^ 2 := by
    intro q _hq
    dsimp [downLeaves]
    rw [card_canonicalDownLeaves_eq_boundaryDegree hS hc q, hmuval,
      Real.sq_sqrt]
    positivity
  have hboundary : (allowedPrimeCount S Y : ℝ) = U.card := by
    exact_mod_cast (card_univ_canonicalUpIndex_eq_allowedPrimeCount hcY).symm
  have hdegree : mu ^ 2 =
      (allowedPrimeCount S (X / (c : ℕ)) : ℝ) -
        (allowedPrimeCount S Y : ℝ) := by
    rw [hmuval]
    exact sq_sqrt_largePrimeStarDegree_eq_allowedPrimeDifference hS hc hYXc
  have hsource : normalizedPrimeStarFirstExit S X Y c =
      (∑ q ∈ U, actualUpStarFirstExit S X Y (upTarget q) mu c0) +
      (∑ q ∈ Dset,
        actualDownStarFirstExit S X Y (downTarget q) (downLeaves q) mu c0) := by
    simpa [U, Dset, upTarget, downTarget, downLeaves, c0] using
      (normalizedPrimeStarFirstExit_eq_sum_canonicalBlocks
        hS hcut hc hd hmuval)
  have hresolvent :
      firstExitLargePrimeResolventOfGap S X Y c mu gammaU hgammaU hgapU
          (normalizedPrimeStarFirstExit S X Y c) =
        (∑ q ∈ U, actualUpStarResolvent S X Y (upTarget q) mu c0) +
        (∑ q ∈ Dset,
          actualDownStarResolvent S X Y (downTarget q) (downLeaves q) mu c0) := by
    simpa [U, Dset, upTarget, downTarget, downLeaves, c0] using
      (firstExitLargePrimeResolventOfGap_eq_sum_canonicalResolvents
        hS hcut hc hd hmuval hgammaU hgapU)
  have hUU : ∀ q ∈ U, ∀ r ∈ U, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (upTarget r)) := by
    intro q _hq r _hr hqr
    dsimp [upTarget]
    apply disjoint_canonicalExitTarget_starSupport hS hcut hc
      (i := Sum.inl q) (j := Sum.inl r)
    intro h
    exact hqr (Sum.inl.inj h)
  have hUD : ∀ q ∈ U, ∀ r ∈ Dset,
      Disjoint (largePrimeStarSupport S X Y (upTarget q))
        (largePrimeStarSupport S X Y (downTarget r)) := by
    intro q _hq r _hr
    dsimp [upTarget, downTarget]
    apply disjoint_canonicalExitTarget_starSupport hS hcut hc
      (i := Sum.inl q) (j := Sum.inr r)
    exact Sum.inl_ne_inr
  have hDD : ∀ q ∈ Dset, ∀ r ∈ Dset, q ≠ r →
      Disjoint (largePrimeStarSupport S X Y (downTarget q))
        (largePrimeStarSupport S X Y (downTarget r)) := by
    intro q _hq r _hr hqr
    dsimp [downTarget]
    apply disjoint_canonicalExitTarget_starSupport hS hcut hc
      (i := Sum.inr q) (j := Sum.inr r)
    intro h
    exact hqr (Sum.inr.inj h)
  have hresult := actualFinitePrimeStarRemainder_of_graphGaps_blocks
    U Dset upTarget downTarget downLeaves c v
      lam mu (allowedPrimeCount S (X / (c : ℕ)) : ℝ)
      (allowedPrimeCount S Y : ℝ) shiftBound c0
      gammaB gammaLam gammaMu gammaU gammaW eta
      hS hcut hc hd hmuval hAv halphaMode
      hgammaB hgammaLam hgammaMu hgammaU hgammaW heta
      hgapLam hgapMu hgapU hgapW hboundaryGap hH hsmallBoundary hsmallUW
      hc0 (fun q _hq ↦ hupden q) hdownLeaves hdownCard
      (fun q _hq ↦ hdownden q) hboundary hdegree
      hsource hresolvent hUU hUD hDD hshift hshift0
  simpa [U, Dset, upTarget, downTarget, downLeaves, c0] using hresult

end

end PrimeStar
