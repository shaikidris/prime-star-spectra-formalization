import PrimeStar.StarSpectrum
import Mathlib.Data.Nat.Sqrt

/-!
# The literal integer square-root cutoff

The manuscript splits prime labels at the real boundary `sqrt X`. For natural
prime labels this is exactly the cutoff `Y = Nat.sqrt X`, because
`X < (Y + 1)^2`. This file exposes manuscript-shaped wrappers for the star
forest and its two nonzero modes.
-/

namespace PrimeStar

noncomputable section

/-- Local decidability for graph and neighbor-finset wrappers at the literal
square-root cutoff. -/
local instance sqrtCutoffLargePrimeDecidableAdj (S : Finset ℕ) (X : ℕ) :
    DecidableRel (largePrimeGraph S X (Nat.sqrt X)).Adj :=
  Classical.decRel _

/-- The defining strict-square inequality for the natural square root. -/
theorem sqrtCutoff_condition (X : ℕ) :
    X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) :=
  Nat.lt_succ_sqrt X

/-- A vertex has at most one prime divisor exceeding its literal square-root
cutoff. -/
theorem sqrtCutoff_largePrime_dvd_unique
    {n X p q : ℕ} (hn0 : 0 < n) (hnX : n ≤ X)
    (hp : p.Prime) (hq : q.Prime)
    (hXp : Nat.sqrt X < p) (hXq : Nat.sqrt X < q)
    (hpn : p ∣ n) (hqn : q ∣ n) :
    p = q :=
  largePrime_dvd_unique hn0 hnX (sqrtCutoff_condition X)
    hp hq hXp hXq hpn hqn

/-- The lower endpoint of an edge labelled above `Nat.sqrt X` lies at or
below the cutoff. -/
theorem sqrtCutoff_isLargePrimeChild_parent_le
    {S : Finset ℕ} {X : ℕ} {m n : Vertex S X}
    (h : IsLargePrimeChild S (Nat.sqrt X) m n) :
    (m : ℕ) ≤ Nat.sqrt X :=
  isLargePrimeChild_parent_le (sqrtCutoff_condition X) h

/-- A child above the literal square-root cutoff has a unique parent. -/
theorem sqrtCutoff_isLargePrimeChild_parent_unique
    {S : Finset ℕ} {X : ℕ} {m k n : Vertex S X}
    (hmn : IsLargePrimeChild S (Nat.sqrt X) m n)
    (hkn : IsLargePrimeChild S (Nat.sqrt X) k n) :
    m = k :=
  isLargePrimeChild_parent_unique (sqrtCutoff_condition X) hmn hkn

/-- Every leaf at the literal square-root cutoff has its centre as its unique
large-prime neighbour. -/
theorem sqrtCutoff_largePrime_neighborFinset_leaf
    {S : Finset ℕ} {X : ℕ} {c v : Vertex S X}
    (hc : (c : ℕ) ≤ Nat.sqrt X)
    (hv : v ∈ largePrimeLeaves S X (Nat.sqrt X) c) :
    (largePrimeGraph S X (Nat.sqrt X)).neighborFinset v = {c} :=
  largePrime_neighborFinset_leaf (sqrtCutoff_condition X) hc hv

/-- Distinct lower centres have disjoint closed star supports at the literal
square-root cutoff. -/
theorem sqrtCutoff_disjoint_largePrimeStarSupport
    {S : Finset ℕ} {X : ℕ} {c k : Vertex S X}
    (hc : (c : ℕ) ≤ Nat.sqrt X) (hk : (k : ℕ) ≤ Nat.sqrt X)
    (hck : c ≠ k) :
    Disjoint
      (largePrimeStarSupport S X (Nat.sqrt X) c)
      (largePrimeStarSupport S X (Nat.sqrt X) k) :=
  disjoint_largePrimeStarSupport (sqrtCutoff_condition X) hc hk hck

/-- Every non-isolated large-prime vertex belongs to a lower star at the
literal square-root cutoff. -/
theorem sqrtCutoff_exists_largePrimeStarSupport_of_not_isolated
    {S : Finset ℕ} {X : ℕ} {v : Vertex S X}
    (hv : ¬(largePrimeGraph S X (Nat.sqrt X)).IsIsolated v) :
    ∃ c : Vertex S X, (c : ℕ) ≤ Nat.sqrt X ∧
      v ∈ largePrimeStarSupport S X (Nat.sqrt X) c :=
  exists_largePrimeStarSupport_of_not_isolated (sqrtCutoff_condition X) hv

/-- The positive mode on a nonempty literal square-root star has eigenvalue
`sqrt d`. -/
theorem sqrtCutoff_largePrime_hasEigenvector_star_pos
    {S : Finset ℕ} {X : ℕ} {c : Vertex S X}
    (hc : (c : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) c) :
    Module.End.HasEigenvector
      (((largePrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ).mulVecLin :
        Module.End ℝ (Vertex S X → ℝ))
      (√(largePrimeStarDegree S X (Nat.sqrt X) c : ℝ))
      (largePrimeSignedStarVector S X (Nat.sqrt X) c 1) :=
  largePrime_hasEigenvector_star_pos (sqrtCutoff_condition X) hc hd

/-- The negative mode on a nonempty literal square-root star has eigenvalue
`-sqrt d`. -/
theorem sqrtCutoff_largePrime_hasEigenvector_star_neg
    {S : Finset ℕ} {X : ℕ} {c : Vertex S X}
    (hc : (c : ℕ) ≤ Nat.sqrt X)
    (hd : 0 < largePrimeStarDegree S X (Nat.sqrt X) c) :
    Module.End.HasEigenvector
      (((largePrimeGraph S X (Nat.sqrt X)).adjMatrix ℝ).mulVecLin :
        Module.End ℝ (Vertex S X → ℝ))
      (-√(largePrimeStarDegree S X (Nat.sqrt X) c : ℝ))
      (largePrimeSignedStarVector S X (Nat.sqrt X) c (-1)) :=
  largePrime_hasEigenvector_star_neg (sqrtCutoff_condition X) hc hd

end

end PrimeStar
