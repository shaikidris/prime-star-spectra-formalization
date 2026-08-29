import PrimeStar.StarPerturbation

/-!
# Arithmetic star centres in the ordered spectrum

This file removes the opaque ordered-index choice from the prime-cover
perturbation interface.  A nonempty lower star has the exact positive
eigenvalue `sqrt d`; the ordered spectral theorem therefore supplies a
canonical (noncomputable) index carrying that value.

The separation of this entry from the remaining ordered eigenvalues is a
separate quantitative input.  In the manuscript it is obtained from degree
comparisons and the prime number theorem.
-/

namespace PrimeStar

open scoped InnerProductSpace

noncomputable section

local instance arithmeticIndexLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance arithmeticIndexSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance arithmeticIndexPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- The ordered spectral index selected by the exact positive mode of the
large-prime star at `c`. -/
def largePrimePositiveStarOrderedIndex
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c) :
    Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))) := by
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hvec : Module.End.HasEigenvector L
      (√(largePrimeStarDegree S X Y c : ℝ))
      (largePrimeNormalizedStarMode S X Y c 1) := by
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · simpa [L] using
        (largePrime_toEuclideanLin_normalizedStarMode hcut hc (by norm_num : (1 : ℝ) ^ 2 = 1))
    · exact fun hzero ↦ by
        have hnorm := norm_largePrimeNormalizedStarMode
          (S := S) (X := X) (Y := Y) (c := c) (ε := (1 : ℝ)) hd
        rw [hzero, norm_zero] at hnorm
        norm_num at hnorm
  exact Classical.choose
    (hL.exists_eigenvalues_eq rfl
      (Module.End.hasEigenvalue_of_hasEigenvector hvec))

/-- The selected ordered entry is exactly the positive arithmetic star
eigenvalue `sqrt d`. -/
theorem largePrimePositiveStarOrderedIndex_eigenvalue
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c) :
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))).eigenvalues rfl
        (largePrimePositiveStarOrderedIndex c hcut hc hd) =
      √(largePrimeStarDegree S X Y c : ℝ) := by
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hvec : Module.End.HasEigenvector L
      (√(largePrimeStarDegree S X Y c : ℝ))
      (largePrimeNormalizedStarMode S X Y c 1) := by
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · simpa [L] using
        (largePrime_toEuclideanLin_normalizedStarMode hcut hc (by norm_num : (1 : ℝ) ^ 2 = 1))
    · exact fun hzero ↦ by
        have hnorm := norm_largePrimeNormalizedStarMode
          (S := S) (X := X) (Y := Y) (c := c) (ε := (1 : ℝ)) hd
        rw [hzero, norm_zero] at hnorm
        norm_num at hnorm
  exact Classical.choose_spec
    (hL.exists_eigenvalues_eq rfl
      (Module.End.hasEigenvalue_of_hasEigenvector hvec))

/-- Prime-cover perturbation theorem indexed directly by an arithmetic
centre.  The scalar-separation premise now refers to the canonical ordered
entry selected by that centre, rather than an unrelated externally supplied
index. -/
theorem primeCover_exists_simple_arithmeticStarEigenpair
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma)
    (hsep : ∀ j :
        Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))),
      j ≠ largePrimePositiveStarOrderedIndex c hcut hc hd →
      gamma ≤
        |(Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl j -
          √(largePrimeStarDegree S X Y c : ℝ)|)
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
  dsimp only
  let i := largePrimePositiveStarOrderedIndex c hcut hc hd
  have hi := largePrimePositiveStarOrderedIndex_eigenvalue c hcut hc hd
  have hsep' : ∀ j :
      Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))), j ≠ i →
      gamma ≤
        |(Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl j -
          (Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl i| := by
    intro j hji
    simpa [i, hi] using hsep j hji
  obtain ⟨k, hk, hsimple⟩ :=
    primeCover_exists_simple_orderedEigenpair
      (S := S) (X := X) (Y := Y) i gamma eta hgamma hsep' hH hsmall
  exact ⟨k, by simpa [i, hi] using hk, hsimple⟩

/-- Same-index arithmetic matching.  The full prime-cover eigenvalue at the
large-prime star's prescribed ordered index is close to the exact star
frequency and is simple. -/
theorem primeCover_simple_arithmeticStarEigenpair
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma)
    (hsep : ∀ j :
        Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))),
      j ≠ largePrimePositiveStarOrderedIndex c hcut hc hd →
      gamma ≤
        |(Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl j -
          √(largePrimeStarDegree S X Y c : ℝ)|)
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
  dsimp only
  let i := largePrimePositiveStarOrderedIndex c hcut hc hd
  have hi := largePrimePositiveStarOrderedIndex_eigenvalue c hcut hc hd
  have hsep' : ∀ j :
      Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))), j ≠ i →
      gamma ≤
        |(Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl j -
          (Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl i| := by
    intro j hji
    simpa [i, hi] using hsep j hji
  obtain ⟨hnear, hsimple⟩ := primeCover_simple_orderedEigenpair
    (S := S) (X := X) (Y := Y) i gamma eta hgamma hsep' hH hsmall
  exact ⟨by simpa [i, hi] using hnear, hsimple⟩

/-- Actual two-sided complement estimate for the shifted prime-cover
operator.  Ordered separation of the arithmetic star entry gives the
large-prime gap; the residual norm and the eigenvalue shift are then paid by
the triangle inequality.  This is the finite operator form of Lemma 8.3.
-/
theorem primeCover_shiftedComplementGap_arithmeticStar
    {S : Finset ℕ} {X Y : ℕ} (c : Vertex S X)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < largePrimeStarDegree S X Y c)
    (gamma eta lam : ℝ) (hgamma : 0 ≤ gamma)
    (hsep : ∀ j :
        Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))),
      j ≠ largePrimePositiveStarOrderedIndex c hcut hc hd →
      gamma ≤
        |(Matrix.isSymmetric_toEuclideanLin_iff.mpr
            ((largePrimeGraph S X Y).isHermitian_adjMatrix
              (R := ℝ))).eigenvalues rfl j -
          √(largePrimeStarDegree S X Y c : ℝ)|)
    (hH : ∀ x : EuclideanSpace ℝ (Vertex S X),
      ‖Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ) x‖ ≤
        eta * ‖x‖)
    (x : EuclideanSpace ℝ (Vertex S X))
    (hx : ⟪largePrimeNormalizedStarMode S X Y c 1, x⟫_ℝ = 0) :
    (gamma - eta - |lam - √(largePrimeStarDegree S X Y c : ℝ)|) * ‖x‖ ≤
      ‖Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x - lam • x‖ := by
  let L := Matrix.toEuclideanLin ((largePrimeGraph S X Y).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin ((smallPrimeGraph S X Y).adjMatrix ℝ)
  let mu := √(largePrimeStarDegree S X Y c : ℝ)
  let i := largePrimePositiveStarOrderedIndex c hcut hc hd
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((largePrimeGraph S X Y).isHermitian_adjMatrix (R := ℝ))
  have hi : hL.eigenvalues rfl i = mu := by
    simpa [hL, i, mu] using
      largePrimePositiveStarOrderedIndex_eigenvalue c hcut hc hd
  have hsep' : ∀ j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))),
      j ≠ i → gamma ≤ |hL.eigenvalues rfl j - hL.eigenvalues rfl i| := by
    intro j hji
    simpa [hL, i, hi, mu] using hsep j hji
  have huEig : L (largePrimeNormalizedStarMode S X Y c 1) =
      mu • largePrimeNormalizedStarMode S X Y c 1 := by
    simpa [L, mu] using
      (largePrime_toEuclideanLin_normalizedStarMode hcut hc
        (by norm_num : (1 : ℝ) ^ 2 = 1))
  have hLgap : gamma * ‖x‖ ≤ ‖L x - mu • x‖ := by
    by_cases hg0 : gamma = 0
    · simp [hg0]
    · have hgpos : 0 < gamma := lt_of_le_of_ne hgamma (Ne.symm hg0)
      have hsimpleGap : ∀ y : EuclideanSpace ℝ (Vertex S X),
          ⟪hL.eigenvectorBasis rfl i, y⟫_ℝ = 0 →
          gamma * ‖y‖ ≤ ‖L y - hL.eigenvalues rfl i • y‖ :=
        fun y hy ↦ isolatedModeGap_of_eigenvalueSeparation
          L hL i gamma hgamma hsep' y hy
      have hspan : Module.finrank ℝ (Module.End.eigenspace L mu) = 1 := by
        have hle : Module.finrank ℝ (Module.End.eigenspace L mu) ≤ 1 :=
          eigenspace_finrank_le_one_of_inner_kernel L
            (hL.eigenvectorBasis rfl i) mu (by
              intro y hy hyorth
              have hgap := hsimpleGap y hyorth
              have hyEig : L y = mu • y := Module.End.mem_eigenspace_iff.mp hy
              rw [hi] at hgap
              rw [hyEig, sub_self, norm_zero] at hgap
              have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
              exact norm_eq_zero.mp this)
        have hge : 1 ≤ Module.finrank ℝ (Module.End.eigenspace L mu) := by
          rw [Submodule.one_le_finrank_iff]
          exact Module.End.hasEigenvalue_iff.mp
            (Module.End.hasEigenvalue_of_hasEigenvector
              ⟨Module.End.mem_eigenspace_iff.mpr huEig,
                fun hz ↦ by
                  have hn := norm_largePrimeNormalizedStarMode
                    (S := S) (X := X) (Y := Y) (c := c) (ε := (1 : ℝ)) hd
                  rw [hz, norm_zero] at hn
                  norm_num at hn⟩)
        exact Nat.le_antisymm hle hge
      let uSub : Module.End.eigenspace L mu :=
        ⟨largePrimeNormalizedStarMode S X Y c 1,
          Module.End.mem_eigenspace_iff.mpr huEig⟩
      let bSub : Module.End.eigenspace L mu :=
        ⟨hL.eigenvectorBasis rfl i,
          Module.End.mem_eigenspace_iff.mpr
            (by simp [hi])⟩
      have huSub0 : uSub ≠ 0 := by
        intro hz
        have hz' : largePrimeNormalizedStarMode S X Y c 1 = 0 :=
          congrArg Subtype.val hz
        have hn := norm_largePrimeNormalizedStarMode
          (S := S) (X := X) (Y := Y) (c := c) (ε := (1 : ℝ)) hd
        rw [hz', norm_zero] at hn
        norm_num at hn
      obtain ⟨r, hrSub⟩ :=
        exists_smul_eq_of_finrank_eq_one hspan huSub0 bSub
      have hr : r • largePrimeNormalizedStarMode S X Y c 1 =
          hL.eigenvectorBasis rfl i := congrArg Subtype.val hrSub
      have hnormr : |r| = 1 := by
        have hb := (hL.eigenvectorBasis rfl).orthonormal.norm_eq_one i
        have hu := norm_largePrimeNormalizedStarMode
          (S := S) (X := X) (Y := Y) (c := c) (ε := (1 : ℝ)) hd
        rw [← hr, norm_smul, Real.norm_eq_abs, hu, mul_one] at hb
        exact hb
      have huBasis : hL.eigenvectorBasis rfl i =
          largePrimeNormalizedStarMode S X Y c 1 ∨
          hL.eigenvectorBasis rfl i =
            -largePrimeNormalizedStarMode S X Y c 1 := by
        have hrsq : r ^ 2 = 1 := by
          calc
            r ^ 2 = |r| ^ 2 := (sq_abs r).symm
            _ = 1 := by rw [hnormr]; norm_num
        rcases sq_eq_one_iff.mp hrsq with hr1 | hr1
        · left
          simpa [hr1] using hr.symm
        · right
          simpa [hr1] using hr.symm
      rcases huBasis with hb | hb
      · have hx' : ⟪hL.eigenvectorBasis rfl i, x⟫_ℝ = 0 := by simpa [hb] using hx
        simpa [hi] using
          isolatedModeGap_of_eigenvalueSeparation L hL i gamma hgamma hsep' x hx'
      · have hx' : ⟪hL.eigenvectorBasis rfl i, x⟫_ℝ = 0 := by
          rw [hb, inner_neg_left]
          simp [hx]
        simpa [hi] using
          isolatedModeGap_of_eigenvalueSeparation L hL i gamma hgamma hsep' x hx'
  have hsplit : Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) = L + H := by
    simpa [L, H] using primeCover_toEuclideanLin_eq_large_add_small S X Y
  have hid : L x - mu • x =
      (Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x - lam • x) -
        H x + (lam - mu) • x := by
    rw [hsplit, LinearMap.add_apply]
    rw [sub_smul]
    abel
  have hupper : ‖L x - mu • x‖ ≤
      ‖Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x - lam • x‖ +
        (eta + |lam - mu|) * ‖x‖ := by
    rw [hid]
    calc
      ‖(Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x - lam • x) -
          H x + (lam - mu) • x‖ ≤
          ‖Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x - lam • x‖ +
            ‖H x‖ + ‖(lam - mu) • x‖ := by
              exact (norm_add_le _ _).trans
                (add_le_add
                  (norm_sub_le
                    (Matrix.toEuclideanLin
                      ((primeCoverGraph S X).adjMatrix ℝ) x - lam • x)
                    (H x))
                  (le_refl ‖(lam - mu) • x‖))
      _ ≤ ‖Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x - lam • x‖ +
          eta * ‖x‖ + |lam - mu| * ‖x‖ := by
            gcongr
            · exact hH x
            · simp [norm_smul, Real.norm_eq_abs]
      _ = ‖Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ) x - lam • x‖ +
          (eta + |lam - mu|) * ‖x‖ := by ring
  dsimp [mu] at hLgap hupper ⊢
  linarith

end

end PrimeStar
