import PrimeStar.TunedSchurAlgebra
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Arithmetic decomposition of a residual weighted row

Residual neighbours larger than a vertex are injectively labelled by an
outgoing prime multiplier. Neighbours smaller than it are injectively labelled
by an incoming prime divisor. This is the exact finite decomposition used by
the analytic Schur estimate.
-/

namespace PrimeStar

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Local decidability for residual adjacency in weighted-row decompositions. -/
local instance smallPrimeRowDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Residual neighbours obtained by multiplying the source by a prime. -/
def outgoingSmallPrimeNeighbors {S : Finset ℕ} {X Y : ℕ}
    (n : Vertex S X) : Finset (Vertex S X) :=
  (smallPrimeGraph S X Y).neighborFinset n |>.filter
    (fun v ↦ (n : ℕ) < (v : ℕ))

/-- Residual neighbours obtained by dividing the source by a prime. -/
def incomingSmallPrimeNeighbors {S : Finset ℕ} {X Y : ℕ}
    (n : Vertex S X) : Finset (Vertex S X) :=
  (smallPrimeGraph S X Y).neighborFinset n |>.filter
    (fun v ↦ (v : ℕ) < (n : ℕ))

/-- Every residual neighbour is uniquely on the outgoing or incoming side of
the source. -/
theorem sum_neighborFinset_eq_outgoing_add_incoming
    {S : Finset ℕ} {X Y : ℕ} (w : Vertex S X → ℝ) (n : Vertex S X) :
    ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n, w v =
      (∑ v ∈ outgoingSmallPrimeNeighbors (Y := Y) n, w v) +
      ∑ v ∈ incomingSmallPrimeNeighbors (Y := Y) n, w v := by
  let N := (smallPrimeGraph S X Y).neighborFinset n
  have hfilter :
      N.filter (fun v : Vertex S X ↦ ¬(n : ℕ) < (v : ℕ)) =
        N.filter (fun v : Vertex S X ↦ (v : ℕ) < (n : ℕ)) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hvN, hnot⟩
      have hvAdj : (smallPrimeGraph S X Y).Adj n v := by
        simpa [N] using hvN
      have hne : (n : ℕ) ≠ (v : ℕ) := by
        intro hcoe
        apply hvAdj.ne
        exact Subtype.ext (Fin.ext hcoe)
      exact ⟨hvN, lt_of_le_of_ne (Nat.le_of_not_gt hnot) hne.symm⟩
    · rintro ⟨hvN, hvn⟩
      exact ⟨hvN, Nat.not_lt_of_ge hvn.le⟩
  rw [← Finset.sum_filter_add_sum_filter_not N
    (fun v : Vertex S X ↦ (n : ℕ) < (v : ℕ)) w, hfilter]
  rfl

/-- An upward residual edge has the indicated orientation. -/
theorem smallPrimeAdj_of_lt
    {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X}
    (hmn : (m : ℕ) < (n : ℕ)) (h : SmallPrimeAdj S Y m n) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ p ≤ Y ∧ (m : ℕ) * p = (n : ℕ) := by
  obtain ⟨p, hp, hpS, hpY, hmp | hnp⟩ := h
  · exact ⟨p, hp, hpS, hpY, hmp⟩
  · have hlt : (n : ℕ) < (n : ℕ) * p :=
      by simpa using (Nat.mul_lt_mul_left (Vertex.coe_pos n)).mpr hp.one_lt
    rw [hnp] at hlt
    exact (Nat.lt_asymm hmn hlt).elim

/-- A downward residual edge has the indicated orientation. -/
theorem smallPrimeAdj_of_gt
    {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X}
    (hnm : (n : ℕ) < (m : ℕ)) (h : SmallPrimeAdj S Y m n) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ p ≤ Y ∧ (n : ℕ) * p = (m : ℕ) := by
  obtain ⟨p, hp, hpS, hpY, hmp | hnp⟩ := h
  · have hlt : (m : ℕ) < (m : ℕ) * p :=
      by simpa using (Nat.mul_lt_mul_left (Vertex.coe_pos m)).mpr hp.one_lt
    rw [hmp] at hlt
    exact (Nat.lt_asymm hnm hlt).elim
  · exact ⟨p, hp, hpS, hpY, hnp⟩

/-- The quotient of an upward neighbour by its source is its prime label. -/
theorem div_eq_smallPrimeLabel_of_lt
    {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X}
    (hmn : (m : ℕ) < (n : ℕ))
    (h : (smallPrimeGraph S X Y).Adj m n) :
    ((n : ℕ) / (m : ℕ)).Prime ∧ (n : ℕ) / (m : ℕ) ≤ Y ∧
      (m : ℕ) * ((n : ℕ) / (m : ℕ)) = (n : ℕ) := by
  obtain ⟨p, hp, _hpS, hpY, hmp⟩ :=
    smallPrimeAdj_of_lt hmn (smallPrimeGraph_adj_iff_smallPrimeAdj.mp h)
  have hq : (n : ℕ) / (m : ℕ) = p := by
    rw [← hmp, Nat.mul_div_cancel_left _ (Vertex.coe_pos m)]
  simpa [hq] using And.intro hp (And.intro hpY hmp)

/-- The quotient of a vertex by a downward neighbour is its prime label. -/
theorem div_eq_smallPrimeLabel_of_gt
    {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X}
    (hnm : (n : ℕ) < (m : ℕ))
    (h : (smallPrimeGraph S X Y).Adj m n) :
    ((m : ℕ) / (n : ℕ)).Prime ∧ (m : ℕ) / (n : ℕ) ≤ Y ∧
      (n : ℕ) * ((m : ℕ) / (n : ℕ)) = (m : ℕ) := by
  obtain ⟨p, hp, _hpS, hpY, hnp⟩ :=
    smallPrimeAdj_of_gt hnm (smallPrimeGraph_adj_iff_smallPrimeAdj.mp h)
  have hq : (m : ℕ) / (n : ℕ) = p := by
    rw [← hnp, Nat.mul_div_cancel_left _ (Vertex.coe_pos n)]
  simpa [hq] using And.intro hp (And.intro hpY hnp)

/-- Prime labels of outgoing residual neighbours. -/
def outgoingSmallPrimeLabels {S : Finset ℕ} {X Y : ℕ}
  (n : Vertex S X) : Finset ℕ :=
  (outgoingSmallPrimeNeighbors (Y := Y) n).image
    (fun v : Vertex S X ↦ (v : ℕ) / (n : ℕ))

/-- Prime labels of incoming residual neighbours. -/
def incomingSmallPrimeLabels {S : Finset ℕ} {X Y : ℕ}
  (n : Vertex S X) : Finset ℕ :=
  (incomingSmallPrimeNeighbors (Y := Y) n).image
    (fun v : Vertex S X ↦ (n : ℕ) / (v : ℕ))

theorem outgoingSmallPrimeLabels_subset_primesLE
    {S : Finset ℕ} {X Y : ℕ} (n : Vertex S X) :
    outgoingSmallPrimeLabels (Y := Y) n ⊆ Nat.primesLE Y := by
  intro p hp
  rw [outgoingSmallPrimeLabels, Finset.mem_image] at hp
  obtain ⟨v, hv, rfl⟩ := hp
  rw [outgoingSmallPrimeNeighbors, Finset.mem_filter] at hv
  have hadj : (smallPrimeGraph S X Y).Adj n v := by
    simpa using hv.1
  obtain ⟨hpPrime, hpY, _hmul⟩ := div_eq_smallPrimeLabel_of_lt hv.2 hadj
  exact Nat.mem_primesLE.mpr ⟨hpY, hpPrime⟩

theorem incomingSmallPrimeLabels_subset_primeFactors
    {S : Finset ℕ} {X Y : ℕ} (n : Vertex S X) :
    incomingSmallPrimeLabels (Y := Y) n ⊆ n.val.val.primeFactors := by
  intro p hp
  rw [incomingSmallPrimeLabels, Finset.mem_image] at hp
  obtain ⟨v, hv, rfl⟩ := hp
  rw [incomingSmallPrimeNeighbors, Finset.mem_filter] at hv
  have hadj : (smallPrimeGraph S X Y).Adj n v := by
    simpa using hv.1
  obtain ⟨hpPrime, _hpY, hmul⟩ := div_eq_smallPrimeLabel_of_gt hv.2 hadj
  exact hpPrime.mem_primeFactors ⟨(v : ℕ), by simpa [Nat.mul_comm] using hmul.symm⟩
    (Nat.ne_of_gt (Vertex.coe_pos n))

theorem incomingSmallPrimeLabels_subset_primesLE
    {S : Finset ℕ} {X Y : ℕ} (n : Vertex S X) :
    incomingSmallPrimeLabels (Y := Y) n ⊆ Nat.primesLE Y := by
  intro p hp
  rw [incomingSmallPrimeLabels, Finset.mem_image] at hp
  obtain ⟨v, hv, rfl⟩ := hp
  rw [incomingSmallPrimeNeighbors, Finset.mem_filter] at hv
  have hadj : (smallPrimeGraph S X Y).Adj n v := by
    simpa using hv.1
  obtain ⟨hpPrime, hpY, _hmul⟩ := div_eq_smallPrimeLabel_of_gt hv.2 hadj
  exact Nat.mem_primesLE.mpr ⟨hpY, hpPrime⟩

theorem outgoingSmallPrimeLabel_injOn
    {S : Finset ℕ} {X Y : ℕ} (n : Vertex S X) :
    Set.InjOn (fun v : Vertex S X ↦ (v : ℕ) / (n : ℕ))
      (outgoingSmallPrimeNeighbors (Y := Y) n) := by
  intro v₁ hv₁ v₂ hv₂ heq
  change v₁ ∈ outgoingSmallPrimeNeighbors (Y := Y) n at hv₁
  change v₂ ∈ outgoingSmallPrimeNeighbors (Y := Y) n at hv₂
  simp only [outgoingSmallPrimeNeighbors, Finset.mem_filter] at hv₁ hv₂
  have hadj₁ : (smallPrimeGraph S X Y).Adj n v₁ := by simpa using hv₁.1
  have hadj₂ : (smallPrimeGraph S X Y).Adj n v₂ := by simpa using hv₂.1
  obtain ⟨_hp₁, _hY₁, hmul₁⟩ := div_eq_smallPrimeLabel_of_lt hv₁.2 hadj₁
  obtain ⟨_hp₂, _hY₂, hmul₂⟩ := div_eq_smallPrimeLabel_of_lt hv₂.2 hadj₂
  apply Subtype.ext
  apply Fin.ext
  exact hmul₁.symm.trans ((congrArg ((n : ℕ) * ·) heq).trans hmul₂)

theorem incomingSmallPrimeLabel_injOn
    {S : Finset ℕ} {X Y : ℕ} (n : Vertex S X) :
    Set.InjOn (fun v : Vertex S X ↦ (n : ℕ) / (v : ℕ))
      (incomingSmallPrimeNeighbors (Y := Y) n) := by
  intro v₁ hv₁ v₂ hv₂ heq
  change v₁ ∈ incomingSmallPrimeNeighbors (Y := Y) n at hv₁
  change v₂ ∈ incomingSmallPrimeNeighbors (Y := Y) n at hv₂
  simp only [incomingSmallPrimeNeighbors, Finset.mem_filter] at hv₁ hv₂
  have hadj₁ : (smallPrimeGraph S X Y).Adj n v₁ := by simpa using hv₁.1
  have hadj₂ : (smallPrimeGraph S X Y).Adj n v₂ := by simpa using hv₂.1
  obtain ⟨_hp₁, _hY₁, hmul₁⟩ := div_eq_smallPrimeLabel_of_gt hv₁.2 hadj₁
  obtain ⟨_hp₂, _hY₂, hmul₂⟩ := div_eq_smallPrimeLabel_of_gt hv₂.2 hadj₂
  change (n : ℕ) / (v₁ : ℕ) = (n : ℕ) / (v₂ : ℕ) at heq
  have hprod :
      (v₁ : ℕ) * ((n : ℕ) / (v₁ : ℕ)) =
        (v₂ : ℕ) * ((n : ℕ) / (v₁ : ℕ)) := by
    calc
      (v₁ : ℕ) * ((n : ℕ) / (v₁ : ℕ)) = (n : ℕ) := hmul₁
      _ = (v₂ : ℕ) * ((n : ℕ) / (v₂ : ℕ)) := hmul₂.symm
      _ = (v₂ : ℕ) * ((n : ℕ) / (v₁ : ℕ)) := by rw [heq]
  have hcoe : (v₁ : ℕ) = (v₂ : ℕ) :=
    Nat.eq_of_mul_eq_mul_right _hp₁.pos hprod
  apply Subtype.ext
  apply Fin.ext
  exact hcoe

/-- Exact multiplicative weight of an outgoing neighbour. -/
theorem smallPrimePowerWeight_outgoing
    {S : Finset ℕ} {X Y : ℕ} {n v : Vertex S X}
    (hv : v ∈ outgoingSmallPrimeNeighbors (Y := Y) n) :
    smallPrimePowerWeight (Y : ℝ) v =
      smallPrimePowerWeight (Y : ℝ) n *
        (((v : ℕ) / (n : ℕ) : ℕ) : ℝ) ^
          (-tunedSchurExponent (Y : ℝ)) := by
  simp only [outgoingSmallPrimeNeighbors, Finset.mem_filter] at hv
  have hadj : (smallPrimeGraph S X Y).Adj n v := by simpa using hv.1
  obtain ⟨_hp, _hpY, hmul⟩ := div_eq_smallPrimeLabel_of_lt hv.2 hadj
  rw [smallPrimePowerWeight, smallPrimePowerWeight]
  have hcast : ((v : ℕ) : ℝ) =
      ((n : ℕ) : ℝ) * (((v : ℕ) / (n : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hmul.symm
  rw [hcast, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-- Exact multiplicative weight of an incoming neighbour. -/
theorem smallPrimePowerWeight_incoming
    {S : Finset ℕ} {X Y : ℕ} {n v : Vertex S X}
    (hv : v ∈ incomingSmallPrimeNeighbors (Y := Y) n) :
    smallPrimePowerWeight (Y : ℝ) v =
      smallPrimePowerWeight (Y : ℝ) n *
        (((n : ℕ) / (v : ℕ) : ℕ) : ℝ) ^
          tunedSchurExponent (Y : ℝ) := by
  simp only [incomingSmallPrimeNeighbors, Finset.mem_filter] at hv
  have hadj : (smallPrimeGraph S X Y).Adj n v := by simpa using hv.1
  obtain ⟨hp, _hpY, hmul⟩ := div_eq_smallPrimeLabel_of_gt hv.2 hadj
  let q : ℕ := (n : ℕ) / (v : ℕ)
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hp.pos
  have hcast : ((n : ℕ) : ℝ) = ((v : ℕ) : ℝ) * (q : ℝ) := by
    exact_mod_cast hmul.symm
  rw [smallPrimePowerWeight, smallPrimePowerWeight, hcast,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have hqcast : (((n : ℕ) / (v : ℕ) : ℕ) : ℝ) = (q : ℝ) := rfl
  rw [hqcast, mul_assoc]
  rw [← Real.rpow_add hqpos]
  simp [q]

/-- The full outgoing prime-power majorant. -/
def outgoingPrimePowerSum (Y : ℕ) (θ : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE Y, (p : ℝ) ^ (-θ)

/-- The incoming prime-divisor power sum at a vertex. -/
def incomingPrimeDivisorPowerSum {S : Finset ℕ} {X : ℕ}
    (n : Vertex S X) (Y : ℕ) (θ : ℝ) : ℝ :=
  ∑ p ∈ n.val.val.primeFactors.filter (fun p ↦ p ≤ Y), (p : ℝ) ^ θ

/-- Four distinct prime divisors whose squares exceed `Y` cannot divide an
integer at most `Y^2`. -/
theorem card_largePrimeFactors_le_three {n Y : ℕ} (hn : n ≠ 0)
    (hnY : n ≤ Y ^ 2) :
    (n.primeFactors.filter (fun p ↦ Y < p ^ 2)).card ≤ 3 := by
  have hYpos : 0 < Y := by
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_contra hnot
    have hYzero : Y = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hYzero] at hnY
    exact hn hnY
  by_contra hcard
  have hfour : 4 ≤ (n.primeFactors.filter (fun p ↦ Y < p ^ 2)).card := by omega
  obtain ⟨t, htSub, htCard⟩ := Finset.exists_subset_card_eq hfour
  have htNonempty : t.Nonempty := Finset.card_pos.mp (by omega)
  have hprodSq : Y ^ 4 < (∏ p ∈ t, p) ^ 2 := by
    have hlt := Finset.prod_lt_prod_of_nonempty
      (s := t) (f := fun _p : ℕ ↦ Y) (g := fun p : ℕ ↦ p ^ 2)
      (fun _p _hp ↦ hYpos)
      (fun p hp ↦ by
        have hmem := htSub hp
        simpa using (Finset.mem_filter.mp hmem).2)
      htNonempty
    simpa [Finset.prod_const, htCard, Finset.prod_pow] using hlt
  have hYYprod : Y ^ 2 < ∏ p ∈ t, p := by
    rw [← Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)]
    have hpow : (Y ^ 2) ^ 2 = Y ^ 4 := by ring
    rw [hpow]
    exact hprodSq
  have hprodDvd : (∏ p ∈ t, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset t n.primeFactors id
      (fun p hp ↦ (Finset.mem_filter.mp (htSub hp)).1)).trans
      (Nat.prod_primeFactors_dvd n)
  have hprodLe : (∏ p ∈ t, p) ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprodDvd
  exact (not_lt_of_ge hnY) (hYYprod.trans_le hprodLe)

/-- The number of distinct prime factors is at most the binary logarithm. -/
theorem card_primeFactors_le_log_two {n : ℕ} (hn : n ≠ 0) :
    n.primeFactors.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  calc
    2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by
      rw [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, p := by
      exact Finset.prod_le_prod' fun p hp ↦
        (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      (Nat.prod_primeFactors_dvd n)

/-- Elementary incoming divisor split: small prime divisors are controlled by
their count, while at most three prime divisors can have square exceeding the
cutoff under `n ≤ Y²`. -/
theorem incomingPrimeDivisorPowerSum_le
    {S : Finset ℕ} {X Y : ℕ} (n : Vertex S X) {θ : ℝ}
    (hθ : 0 ≤ θ) (hnY : (n : ℕ) ≤ Y ^ 2) :
    incomingPrimeDivisorPowerSum n Y θ ≤
      (Nat.log 2 (n : ℕ) : ℝ) * (√(Y : ℝ)) ^ θ +
        3 * (Y : ℝ) ^ θ := by
  let F := n.val.val.primeFactors.filter (fun p ↦ p ≤ Y)
  let Fsmall := F.filter (fun p ↦ p ^ 2 ≤ Y)
  let Flarge := F.filter (fun p ↦ ¬p ^ 2 ≤ Y)
  have hsplit :
      (∑ p ∈ F, (p : ℝ) ^ θ) =
        (∑ p ∈ Fsmall, (p : ℝ) ^ θ) +
          ∑ p ∈ Flarge, (p : ℝ) ^ θ := by
    rw [← Finset.sum_filter_add_sum_filter_not F
      (fun p : ℕ ↦ p ^ 2 ≤ Y) (fun p ↦ (p : ℝ) ^ θ)]
  rw [incomingPrimeDivisorPowerSum, show
    n.val.val.primeFactors.filter (fun p ↦ p ≤ Y) = F from rfl, hsplit]
  have hsmallTerms :
      (∑ p ∈ Fsmall, (p : ℝ) ^ θ) ≤
        Fsmall.card • ((√(Y : ℝ)) ^ θ) := by
    apply Finset.sum_le_card_nsmul
    intro p hp
    have hpSq : p ^ 2 ≤ Y := by
      exact (Finset.mem_filter.mp hp).2
    have hpSqrt : (p : ℝ) ≤ √(Y : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg p) (Nat.cast_nonneg Y)]
      exact_mod_cast hpSq
    exact Real.rpow_le_rpow (Nat.cast_nonneg p) hpSqrt hθ
  have hlargeTerms :
      (∑ p ∈ Flarge, (p : ℝ) ^ θ) ≤
        Flarge.card • ((Y : ℝ) ^ θ) := by
    apply Finset.sum_le_card_nsmul
    intro p hp
    have hpF : p ∈ F := (Finset.mem_filter.mp hp).1
    have hpY : p ≤ Y := (Finset.mem_filter.mp hpF).2
    exact Real.rpow_le_rpow (Nat.cast_nonneg p) (by exact_mod_cast hpY) hθ
  have hsmallCard : Fsmall.card ≤ Nat.log 2 (n : ℕ) := by
    exact (Finset.card_le_card fun p hp ↦
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).trans
      (card_primeFactors_le_log_two (Nat.ne_of_gt (Vertex.coe_pos n)))
  have hlargeCard : Flarge.card ≤ 3 := by
    apply (Finset.card_le_card ?_).trans
      (card_largePrimeFactors_le_three
        (Nat.ne_of_gt (Vertex.coe_pos n)) hnY)
    intro p hp
    rw [Finset.mem_filter]
    constructor
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    · exact Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
  calc
    (∑ p ∈ Fsmall, (p : ℝ) ^ θ) +
        ∑ p ∈ Flarge, (p : ℝ) ^ θ ≤
      Fsmall.card • ((√(Y : ℝ)) ^ θ) +
        Flarge.card • ((Y : ℝ) ^ θ) := add_le_add hsmallTerms hlargeTerms
    _ ≤ (Nat.log 2 (n : ℕ)) • ((√(Y : ℝ)) ^ θ) +
        3 • ((Y : ℝ) ^ θ) := by
      gcongr
    _ = _ := by simp [nsmul_eq_mul]

/-- Outgoing neighbour weights are bounded by the full outgoing prime-power
sum. -/
theorem sum_outgoingSmallPrimeNeighbors_le
    {S : Finset ℕ} {X Y : ℕ} (n : Vertex S X) :
    ∑ v ∈ outgoingSmallPrimeNeighbors (Y := Y) n,
        smallPrimePowerWeight (Y : ℝ) v ≤
      smallPrimePowerWeight (Y : ℝ) n *
        outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) := by
  let O := outgoingSmallPrimeNeighbors (Y := Y) n
  let label : Vertex S X → ℕ := fun v ↦ (v : ℕ) / (n : ℕ)
  have hinj : Set.InjOn label O := outgoingSmallPrimeLabel_injOn n
  have hweights :
      ∑ v ∈ O, smallPrimePowerWeight (Y : ℝ) v =
        smallPrimePowerWeight (Y : ℝ) n *
          ∑ p ∈ O.image label,
            (p : ℝ) ^ (-tunedSchurExponent (Y : ℝ)) := by
    calc
      ∑ v ∈ O, smallPrimePowerWeight (Y : ℝ) v =
          ∑ v ∈ O, smallPrimePowerWeight (Y : ℝ) n *
            ((label v : ℕ) : ℝ) ^ (-tunedSchurExponent (Y : ℝ)) := by
              apply Finset.sum_congr rfl
              intro v hv
              exact smallPrimePowerWeight_outgoing hv
      _ = smallPrimePowerWeight (Y : ℝ) n *
          ∑ v ∈ O, ((label v : ℕ) : ℝ) ^
            (-tunedSchurExponent (Y : ℝ)) := by rw [Finset.mul_sum]
      _ = smallPrimePowerWeight (Y : ℝ) n *
          ∑ p ∈ O.image label, (p : ℝ) ^
            (-tunedSchurExponent (Y : ℝ)) := by
              rw [Finset.sum_image hinj]
  rw [hweights]
  apply mul_le_mul_of_nonneg_left _ (smallPrimePowerWeight_pos _ _).le
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · simpa [O, label, outgoingSmallPrimeLabels] using
      outgoingSmallPrimeLabels_subset_primesLE (Y := Y) n
  · intro p _hp _hnot
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _

/-- Incoming neighbour weights are bounded by the filtered prime-divisor
power sum. -/
theorem sum_incomingSmallPrimeNeighbors_le
    {S : Finset ℕ} {X Y : ℕ} (n : Vertex S X) :
    ∑ v ∈ incomingSmallPrimeNeighbors (Y := Y) n,
        smallPrimePowerWeight (Y : ℝ) v ≤
      smallPrimePowerWeight (Y : ℝ) n *
        incomingPrimeDivisorPowerSum n Y (tunedSchurExponent (Y : ℝ)) := by
  let I := incomingSmallPrimeNeighbors (Y := Y) n
  let label : Vertex S X → ℕ := fun v ↦ (n : ℕ) / (v : ℕ)
  have hinj : Set.InjOn label I := incomingSmallPrimeLabel_injOn n
  have hweights :
      ∑ v ∈ I, smallPrimePowerWeight (Y : ℝ) v =
        smallPrimePowerWeight (Y : ℝ) n *
          ∑ p ∈ I.image label,
            (p : ℝ) ^ tunedSchurExponent (Y : ℝ) := by
    calc
      ∑ v ∈ I, smallPrimePowerWeight (Y : ℝ) v =
          ∑ v ∈ I, smallPrimePowerWeight (Y : ℝ) n *
            ((label v : ℕ) : ℝ) ^ tunedSchurExponent (Y : ℝ) := by
              apply Finset.sum_congr rfl
              intro v hv
              exact smallPrimePowerWeight_incoming hv
      _ = smallPrimePowerWeight (Y : ℝ) n *
          ∑ v ∈ I, ((label v : ℕ) : ℝ) ^
            tunedSchurExponent (Y : ℝ) := by rw [Finset.mul_sum]
      _ = smallPrimePowerWeight (Y : ℝ) n *
          ∑ p ∈ I.image label, (p : ℝ) ^
            tunedSchurExponent (Y : ℝ) := by
              rw [Finset.sum_image hinj]
  rw [hweights]
  apply mul_le_mul_of_nonneg_left _ (smallPrimePowerWeight_pos _ _).le
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Finset.mem_filter]
    constructor
    · exact incomingSmallPrimeLabels_subset_primeFactors (Y := Y) n
        (by simpa [I, label, incomingSmallPrimeLabels] using hp)
    · exact Nat.le_of_mem_primesLE <|
        incomingSmallPrimeLabels_subset_primesLE (Y := Y) n
          (by simpa [I, label, incomingSmallPrimeLabels] using hp)
  · intro p _hp _hnot
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _

/-- Exact graph reduction: the tuned weighted row is controlled by one
outgoing prime-power sum and one incoming divisor sum. -/
theorem smallPrimePowerWeight_row_le_primeSums
    {S : Finset ℕ} {X Y : ℕ} (n : Vertex S X) :
    ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n,
        smallPrimePowerWeight (Y : ℝ) v ≤
      smallPrimePowerWeight (Y : ℝ) n *
        (outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) +
          incomingPrimeDivisorPowerSum n Y
            (tunedSchurExponent (Y : ℝ))) := by
  rw [sum_neighborFinset_eq_outgoing_add_incoming]
  calc
    (∑ v ∈ outgoingSmallPrimeNeighbors (Y := Y) n,
        smallPrimePowerWeight (Y : ℝ) v) +
        ∑ v ∈ incomingSmallPrimeNeighbors (Y := Y) n,
          smallPrimePowerWeight (Y : ℝ) v ≤
      smallPrimePowerWeight (Y : ℝ) n *
          outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) +
        smallPrimePowerWeight (Y : ℝ) n *
          incomingPrimeDivisorPowerSum n Y
            (tunedSchurExponent (Y : ℝ)) :=
      add_le_add (sum_outgoingSmallPrimeNeighbors_le n)
        (sum_incomingSmallPrimeNeighbors_le n)
    _ = _ := by ring

/-- Scalar prime-sum estimates discharge the graph's tuned weighted-row
hypothesis. -/
theorem smallPrimeGraph_l2_opNorm_le_tuned_of_primeSums
    {S : Finset ℕ} {X Y : ℕ} {Kout Kin : ℝ}
    (hY : 1 < (Y : ℝ)) (hKout : 0 ≤ Kout) (hKin : 0 ≤ Kin)
    (hout : outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) ≤
      Kout * tunedSchurScale (Y : ℝ))
    (hin : ∀ n : Vertex S X,
      incomingPrimeDivisorPowerSum n Y (tunedSchurExponent (Y : ℝ)) ≤
        Kin * tunedSchurScale (Y : ℝ)) :
    ‖(smallPrimeGraph S X Y).adjMatrix ℝ‖ ≤
      (Kout + Kin) * tunedSchurScale (Y : ℝ) := by
  apply smallPrimeGraph_l2_opNorm_le_tuned hY (add_nonneg hKout hKin)
  intro n
  calc
    ∑ v ∈ (smallPrimeGraph S X Y).neighborFinset n,
        smallPrimePowerWeight (Y : ℝ) v ≤
      smallPrimePowerWeight (Y : ℝ) n *
        (outgoingPrimePowerSum Y (tunedSchurExponent (Y : ℝ)) +
          incomingPrimeDivisorPowerSum n Y
            (tunedSchurExponent (Y : ℝ))) :=
      smallPrimePowerWeight_row_le_primeSums n
    _ ≤ smallPrimePowerWeight (Y : ℝ) n *
        (Kout * tunedSchurScale (Y : ℝ) +
          Kin * tunedSchurScale (Y : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hout (hin n))
        (smallPrimePowerWeight_pos (Y : ℝ) n).le
    _ = ((Kout + Kin) * tunedSchurScale (Y : ℝ)) *
        smallPrimePowerWeight (Y : ℝ) n := by ring

end

end PrimeStar
