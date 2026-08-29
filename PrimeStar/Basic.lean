import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Nat.Prime.Basic

/-!
# Finite prime-cover graphs

This file defines the finite allowed-vertex type, the prime-cover graph, and
its large-prime subgraph. It contains only exact finite definitions.
-/

namespace PrimeStar

/-- Positive integers at most `X` whose prime divisors avoid `S`. -/
def Vertex (S : Finset ℕ) (X : ℕ) :=
  {n : Fin (X + 1) // 0 < n.1 ∧ ∀ p ∈ S, ¬p ∣ n.1}
  deriving DecidableEq, Fintype

namespace Vertex

instance (S : Finset ℕ) (X : ℕ) : CoeOut (Vertex S X) ℕ :=
  ⟨fun n ↦ n.1.1⟩

theorem coe_pos {S : Finset ℕ} {X : ℕ} (n : Vertex S X) : 0 < (n : ℕ) :=
  n.2.1

@[simp]
theorem coe_le {S : Finset ℕ} {X : ℕ} (n : Vertex S X) : (n : ℕ) ≤ X := by
  exact Nat.lt_succ_iff.mp n.1.2

@[simp]
theorem not_dvd_of_mem {S : Finset ℕ} {X p : ℕ} (n : Vertex S X) (hp : p ∈ S) :
    ¬p ∣ (n : ℕ) :=
  n.2.2 p hp

end Vertex

/-- Two allowed vertices differ by multiplication by one allowed prime. -/
def PrimeCoverAdj {S : Finset ℕ} {X : ℕ} (m n : Vertex S X) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ((m : ℕ) * p = (n : ℕ) ∨ (n : ℕ) * p = (m : ℕ))

theorem primeCoverAdj_symm {S : Finset ℕ} {X : ℕ} {m n : Vertex S X} :
    PrimeCoverAdj m n → PrimeCoverAdj n m := by
  rintro ⟨p, hp, hpS, h | h⟩
  · exact ⟨p, hp, hpS, Or.inr h⟩
  · exact ⟨p, hp, hpS, Or.inl h⟩

theorem not_primeCoverAdj_self {S : Finset ℕ} {X : ℕ} (m : Vertex S X) :
    ¬PrimeCoverAdj m m := by
  rintro ⟨p, hp, _hpS, h | h⟩
  all_goals
    have hmul : (m : ℕ) * p = (m : ℕ) * 1 := by simpa using h
    have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos m) hmul
    exact hp.ne_one hp1

/-- The finite prime-cover graph on allowed positive integers at most `X`. -/
def primeCoverGraph (S : Finset ℕ) (X : ℕ) : SimpleGraph (Vertex S X) where
  Adj := PrimeCoverAdj
  symm := ⟨fun _ _ h ↦ primeCoverAdj_symm (S := S) (X := X) h⟩
  loopless := ⟨fun m ↦ not_primeCoverAdj_self (S := S) (X := X) m⟩

@[simp]
theorem primeCoverGraph_adj {S : Finset ℕ} {X : ℕ} {m n : Vertex S X} :
    (primeCoverGraph S X).Adj m n ↔ PrimeCoverAdj m n :=
  Iff.rfl

/-- The part of the prime-cover graph whose edge labels exceed `Y`. -/
def LargePrimeAdj (S : Finset ℕ) (Y : ℕ) {X : ℕ} (m n : Vertex S X) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ Y < p ∧
    ((m : ℕ) * p = (n : ℕ) ∨ (n : ℕ) * p = (m : ℕ))

theorem largePrimeAdj_symm {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X} :
    LargePrimeAdj S Y m n → LargePrimeAdj S Y n m := by
  rintro ⟨p, hp, hpS, hY, h | h⟩
  · exact ⟨p, hp, hpS, hY, Or.inr h⟩
  · exact ⟨p, hp, hpS, hY, Or.inl h⟩

theorem not_largePrimeAdj_self {S : Finset ℕ} {X Y : ℕ} (m : Vertex S X) :
    ¬LargePrimeAdj S Y m m := by
  rintro ⟨p, hp, _hpS, _hY, h | h⟩
  all_goals
    have hmul : (m : ℕ) * p = (m : ℕ) * 1 := by simpa using h
    have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos m) hmul
    exact hp.ne_one hp1

/-- The large-prime subgraph at cutoff `Y`. -/
def largePrimeGraph (S : Finset ℕ) (X Y : ℕ) : SimpleGraph (Vertex S X) where
  Adj := LargePrimeAdj S Y
  symm := ⟨fun _ _ h ↦ largePrimeAdj_symm (S := S) (X := X) (Y := Y) h⟩
  loopless := ⟨fun m ↦ not_largePrimeAdj_self (S := S) (X := X) (Y := Y) m⟩

@[simp]
theorem largePrimeGraph_adj {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X} :
    (largePrimeGraph S X Y).Adj m n ↔ LargePrimeAdj S Y m n :=
  Iff.rfl

theorem largePrimeGraph_le_primeCoverGraph (S : Finset ℕ) (X Y : ℕ) :
    largePrimeGraph S X Y ≤ primeCoverGraph S X := by
  rintro m n ⟨p, hp, hpS, _hY, h⟩
  exact ⟨p, hp, hpS, h⟩

/-- `n` is obtained from `m` by one allowed prime multiplication above the cutoff. -/
def IsLargePrimeChild (S : Finset ℕ) (Y : ℕ) {X : ℕ} (m n : Vertex S X) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ Y < p ∧ (m : ℕ) * p = (n : ℕ)

theorem isLargePrimeChild_largePrimeAdj {S : Finset ℕ} {X Y : ℕ} {m n : Vertex S X}
    (h : IsLargePrimeChild S Y m n) : LargePrimeAdj S Y m n := by
  obtain ⟨p, hp, hpS, hYp, hmn⟩ := h
  exact ⟨p, hp, hpS, hYp, Or.inl hmn⟩

end PrimeStar
