/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulGenericContraction
public import LeanCanny.Algebra.MacaulayCanonicalMatrix
public import LeanCanny.Algebra.MacaulayKoszulExteriorBridge
public import LeanCanny.Algebra.MacaulayRelationExtraneous

/-! # The canonical homotopy and the concrete Macaulay operators

In degree zero the polynomial homotopy selects exactly the existing
Macaulay multiplier row. In degree one its differential gives exactly the
existing division relation. These identities connect the finite weighted
complex with the concrete determinant factors.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem wordExponent_one (d : Fin n → ℕ) (i : Fin n) :
    wordExponent d (fun _ : Fin 1 => i) = Finsupp.single i (d i) := by
  simp only [wordExponent, Fin.sum_univ_one]

theorem divisionRow_fst (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (a : Macaulay.MultiplierIndex d W) :
    (Macaulay.divisionRow d W hW a).1 =
      Macaulay.pivot d (Macaulay.productExponent d W a) (Macaulay.productExponent_degree d W a) := by
  change Macaulay.pivot d (FixedWidthPolynomial.vector n W (Macaulay.productIndex d W hW a).val)
    ((Macaulay.mem_activeIndices d W _).mp (Macaulay.productIndex d W hW a).property) = _
  simp only [Macaulay.vector_productIndex]

theorem levelHomotopy_macaulayTarget (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W) :
    levelHomotopy (R := R) d
        (canonicalGenerator (R := R) d (Macaulay.level d) W 0 (macaulayCanonicalTarget d W r)) =
      canonicalGenerator (R := R) d (Macaulay.level d) W 1
        (macaulayCanonicalSource d W (Macaulay.selectedMultiplier d W r)) := by
  let v : Fin 0 → Fin n := Fin.elim0
  have hv : wordExponent d v = 0 := by simp only [wordExponent, Fin.sum_univ_zero]
  have hr := (Macaulay.mem_activeIndices d W r.val).mp r.property
  have ht : (FixedWidthPolynomial.vector n W r.val + wordExponent d v).degree = Macaulay.level d := by
    rw [hv, add_zero]
    exact hr
  have hi : Macaulay.pivot d (FixedWidthPolynomial.vector n W r.val + wordExponent d v) ht =
      (Macaulay.selectedMultiplier d W r).1 := by
    simp only [hv, add_zero]
    rfl
  have hb : Finsupp.single (Macaulay.selectedMultiplier d W r).1 (d (Macaulay.selectedMultiplier d W r).1) ≤
      FixedWidthPolynomial.vector n W r.val := by
    rw [← Macaulay.selectedMultiplier_add d W r]
    exact le_add_self
  have hm : FixedWidthPolynomial.vector n W (Macaulay.selectedMultiplier d W r).2.val =
      FixedWidthPolynomial.vector n W r.val -
        Finsupp.single (Macaulay.selectedMultiplier d W r).1 (d (Macaulay.selectedMultiplier d W r).1) := by
    have h := congrArg (fun m => m -
      Finsupp.single (Macaulay.selectedMultiplier d W r).1 (d (Macaulay.selectedMultiplier d W r).1))
        (Macaulay.selectedMultiplier_add d W r)
    simpa only [add_tsub_cancel_right] using h
  rw [canonicalGenerator_apply]
  change levelHomotopy (R := R) d (MvPolynomial.monomial (FixedWidthPolynomial.vector n W r.val) (1 : R) •
    exteriorBasis (R := R) ∅) = _
  rw [exteriorBasis_empty, ← blade_zero v]
  change levelHomotopy (R := R) d (monomialBlade (R := R) v (FixedWidthPolynomial.vector n W r.val)) = _
  rw [levelHomotopy_word d v _ ht, hi, powerHomotopy_apply, divide_monomialBlade, ite_eq_left hb,
    wedge_monomialBlade, monomialBlade, blade_cons, blade_zero, mul_one, ← hm, canonicalGenerator_apply]
  change _ = MvPolynomial.monomial (FixedWidthPolynomial.vector n W (Macaulay.selectedMultiplier d W r).2.val) (1 : R) •
    exteriorBasis (R := R) {(Macaulay.selectedMultiplier d W r).1}
  rw [exteriorBasis_singleton]

theorem levelHomotopy_macaulaySource (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (a : Macaulay.MultiplierIndex d W) :
    levelHomotopy (R := R) d
        (canonicalGenerator (R := R) d (Macaulay.level d) W 1 (macaulayCanonicalSource d W a)) =
      if a.1 = (Macaulay.divisionRow d W hW a).1 then 0 else
        MvPolynomial.monomial (Macaulay.divisionExponent d W hW a) (1 : R) •
          (ExteriorAlgebra.ι (Poly n R) (Pi.single (Macaulay.divisionRow d W hW a).1 1 : Fin n → Poly n R) *
            ExteriorAlgebra.ι (Poly n R) (Pi.single a.1 1 : Fin n → Poly n R)) := by
  let v := fun _ : Fin 1 => a.1
  have ht : (FixedWidthPolynomial.vector n W a.2.val + wordExponent d v).degree = Macaulay.level d := by
    rw [wordExponent_one]
    exact Macaulay.productExponent_degree d W a
  have hi : Macaulay.pivot d (FixedWidthPolynomial.vector n W a.2.val + wordExponent d v) ht =
      (Macaulay.divisionRow d W hW a).1 := by
    simpa only [v, wordExponent_one, Macaulay.productExponent] using (divisionRow_fst d W hW a).symm
  rw [canonicalGenerator_macaulaySource]
  change levelHomotopy (R := R) d (monomialBlade (R := R) v (FixedWidthPolynomial.vector n W a.2.val)) = _
  rw [levelHomotopy_word d v _ ht, hi, powerHomotopy_apply]
  split_ifs with ha
  · rw [← divide_wedge, wedge_word_eq_zero_of_mem _ v _ (by exact ⟨0, ha⟩), map_zero]
  · have hb : Finsupp.single (Macaulay.divisionRow d W hW a).1 (d (Macaulay.divisionRow d W hW a).1) ≤
        FixedWidthPolynomial.vector n W a.2.val := by
      rw [← Macaulay.divisionExponent_add d W hW a ha]
      exact le_add_self
    rw [divide_monomialBlade, ite_eq_left hb, wedge_monomialBlade, monomialBlade, blade_cons, blade_one]
    rfl

theorem differential_levelHomotopy_macaulaySource (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (a : Macaulay.MultiplierIndex d W) :
    KoszulExterior.differential p (levelHomotopy (R := R) d
      (canonicalGenerator (R := R) d (Macaulay.level d) W 1 (macaulayCanonicalSource d W a))) =
      if a.1 = (Macaulay.divisionRow d W hW a).1 then 0 else
        ExteriorAlgebra.ι (Poly n R)
          (Macaulay.koszulMultipliers p a.1 (Macaulay.divisionRow d W hW a).1 (Macaulay.divisionExponent d W hW a)) := by
  rw [levelHomotopy_macaulaySource]
  split_ifs
  · exact map_zero _
  · exact Macaulay.koszulMultipliers_exterior_boundary _ _ _ _

theorem exteriorBasis_repr_ι (q : Fin n → Poly n R) (i : Fin n) :
    (exteriorBasis (R := R)).repr (ExteriorAlgebra.ι (Poly n R) q) {i} = q i := by
  have h : (Finsupp.lapply {i}).comp
      ((exteriorBasis (R := R)).repr.toLinearMap.comp (ExteriorAlgebra.ι (Poly n R))) = LinearMap.proj i := by
    apply (Pi.basisFun (Poly n R) (Fin n)).ext
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply]
    change (exteriorBasis (R := R)).repr (ExteriorAlgebra.ι (Poly n R) (Pi.single j 1 : Fin n → Poly n R)) {i} =
      (Pi.single j 1 : Fin n → Poly n R) i
    rw [← exteriorBasis_singleton, Module.Basis.repr_self_apply]
    simp only [Finset.singleton_inj, Pi.single_apply, eq_comm]
  exact LinearMap.congr_fun h q

theorem homotopyMatrix_zero_macaulay (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) :
    (homotopyMatrix (R := R) d W hW 0).submatrix (macaulayTargetEquiv d W) (macaulaySourceEquiv d W) =
      MatrixMinorSection.rowSelection (Macaulay.selectedMultiplier d W) := by
  ext r a
  have hh : weightedHomotopy (R := R) d W hW 0
      (canonicalBasis (R := R) d (Macaulay.level d) W 0 (macaulayCanonicalTarget d W r)) =
      canonicalBasis (R := R) d (Macaulay.level d) W 1
        (macaulayCanonicalSource d W (Macaulay.selectedMultiplier d W r)) := by
    apply Subtype.ext
    change levelHomotopy (R := R) d (canonicalBasis (R := R) d (Macaulay.level d) W 0 (macaulayCanonicalTarget d W r) : Total n R) = _
    rw [canonicalBasis_apply, levelHomotopy_macaulayTarget, canonicalBasis_apply]
  change homotopyMatrix (R := R) d W hW 0 (macaulayCanonicalTarget d W r) (macaulayCanonicalSource d W a) = _
  rw [homotopyMatrix, Matrix.transpose_apply, LinearMap.toMatrix_apply, hh, Module.Basis.repr_self_apply]
  change (if macaulayCanonicalSource d W (Macaulay.selectedMultiplier d W r) = macaulayCanonicalSource d W a then 1 else 0) =
    if Macaulay.selectedMultiplier d W r = a then 1 else 0
  simp only [(macaulayCanonicalSource_bijective d W).injective.eq_iff]

theorem homotopyMatrix_one_differential_macaulay (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (homotopyMatrix (R := R) d W hW 1 * canonicalMatrix p d (Macaulay.level d) W hp hW 1).submatrix
      (macaulaySourceEquiv d W) (macaulaySourceEquiv d W) = Macaulay.divisionRelations p d W hW := by
  ext a b
  unfold homotopyMatrix canonicalMatrix
  rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp]
  change (LinearMap.toMatrix _ _
    ((differential p d (Macaulay.level d) W hp hW 1).comp (weightedHomotopy d W hW 1)))ᵀ
      (macaulayCanonicalSource d W a) (macaulayCanonicalSource d W b) = _
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, canonicalBasis_repr_coeff]
  change ((exteriorBasis (R := R)).repr (KoszulExterior.differential p
    (levelHomotopy (R := R) d (canonicalBasis (R := R) d (Macaulay.level d) W 1 (macaulayCanonicalSource d W a) : Total n R)))
      {b.1}).coeff (FixedWidthPolynomial.vector n W b.2.val) = Macaulay.divisionRelations p d W hW a b
  rw [canonicalBasis_apply, differential_levelHomotopy_macaulaySource p d W hW a]
  by_cases ha : a.1 = (Macaulay.divisionRow d W hW a).1
  · simp only [ha, ite_true, map_zero, Finsupp.zero_apply, AddMonoidAlgebra.coeff_zero,
      Macaulay.divisionRelations, Pi.zero_apply]
  · rw [ite_eq_right ha, exteriorBasis_repr_ι]
    rw [Macaulay.divisionRelations, ite_eq_right ha]
    rfl

end LeanCanny.Algebra.KoszulWeighted
