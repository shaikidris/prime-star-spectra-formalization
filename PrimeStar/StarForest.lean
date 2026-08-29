import PrimeStar.Basic

/-!
# The large-prime star structure

This file proves the exact arithmetic facts behind the large-prime star
forest: edges cross the square-root cutoff and every upper endpoint has a
unique lower parent.
-/

namespace PrimeStar

/-- A positive integer below `X` has at most one prime divisor strictly above
a cutoff `Y` when `X < (Y + 1)^2`. This is the exact natural-number form of
the square-root cutoff. -/
theorem largePrime_dvd_unique {n X Y p q : ℕ} (hn0 : 0 < n) (hnX : n ≤ X)
    (hcut : X < (Y + 1) * (Y + 1))
    (hp : p.Prime) (hq : q.Prime) (hYp : Y < p) (hYq : Y < q)
    (hpn : p ∣ n) (hqn : q ∣ n) : p = q := by
  by_contra hpq
  have hpq_dvd : p * q ∣ n := hp.dvd_mul_of_dvd_ne hpq hq hpn hqn
  have hpq_le_n : p * q ≤ n := Nat.le_of_dvd hn0 hpq_dvd
  have hsq_le : (Y + 1) * (Y + 1) ≤ p * q :=
    Nat.mul_le_mul (Nat.succ_le_iff.mpr hYp) (Nat.succ_le_iff.mpr hYq)
  exact (not_lt_of_ge (hsq_le.trans (hpq_le_n.trans hnX))) hcut

/-- The lower endpoint of a large-prime edge lies at or below the cutoff. -/
theorem isLargePrimeChild_parent_le {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (h : IsLargePrimeChild S Y m n) : (m : ℕ) ≤ Y := by
  obtain ⟨p, _hp, _hpS, hYp, hmn⟩ := h
  by_contra hmY
  have hYm : Y < (m : ℕ) := Nat.lt_of_not_ge hmY
  have hsq_le : (Y + 1) * (Y + 1) ≤ (m : ℕ) * p :=
    Nat.mul_le_mul (Nat.succ_le_iff.mpr hYm) (Nat.succ_le_iff.mpr hYp)
  rw [hmn] at hsq_le
  exact (not_lt_of_ge (hsq_le.trans (Vertex.coe_le n))) hcut

/-- The upper endpoint of a large-prime edge lies above the cutoff. -/
theorem isLargePrimeChild_cutoff_lt_child {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X}
    (h : IsLargePrimeChild S Y m n) : Y < (n : ℕ) := by
  obtain ⟨p, _hp, _hpS, hYp, hmn⟩ := h
  have hm1 : 1 ≤ (m : ℕ) := Vertex.coe_pos m
  have hp_le : p ≤ (m : ℕ) * p := by
    simpa only [one_mul] using Nat.mul_le_mul_right p hm1
  rw [hmn] at hp_le
  exact hYp.trans_le hp_le

/-- Above the square-root cutoff, a child has a unique parent. -/
theorem isLargePrimeChild_parent_unique {S : Finset ℕ} {X Y : ℕ} {m k n : Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hmn : IsLargePrimeChild S Y m n)
    (hkn : IsLargePrimeChild S Y k n) : m = k := by
  obtain ⟨p, hp, _hpS, hYp, hmp⟩ := hmn
  obtain ⟨q, hq, _hqS, hYq, hkq⟩ := hkn
  have hp_dvd : p ∣ (n : ℕ) := ⟨(m : ℕ), by simpa [Nat.mul_comm] using hmp.symm⟩
  have hq_dvd : q ∣ (n : ℕ) := ⟨(k : ℕ), by simpa [Nat.mul_comm] using hkq.symm⟩
  have hpq : p = q := largePrime_dvd_unique (Vertex.coe_pos n) (Vertex.coe_le n) hcut
    hp hq hYp hYq hp_dvd hq_dvd
  subst q
  have hmk : (m : ℕ) = (k : ℕ) := Nat.eq_of_mul_eq_mul_right hp.pos (hmp.trans hkq.symm)
  exact Subtype.ext (Fin.ext hmk)

end PrimeStar
