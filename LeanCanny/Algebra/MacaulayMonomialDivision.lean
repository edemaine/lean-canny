/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayKoszulRelations
public import LeanCanny.Algebra.MatrixMinorSection

/-! # Monomial division for the full coordinate-power multiplication matrix

Each multiplier row maps to one degree-level monomial. Its selected row has
the same image. The difference is a Koszul relation between the original
input coordinate and the selected pivot coordinate.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def productExponent (d : Fin n → ℕ) (W : ℕ) (a : MultiplierIndex d W) : Fin n →₀ ℕ :=
  FixedWidthPolynomial.vector n W a.2.val + Finsupp.single a.1 (d a.1)

theorem productExponent_degree (d : Fin n → ℕ) (W : ℕ) (a : MultiplierIndex d W) :
    (productExponent d W a).degree = level d := by
  simpa only [productExponent, map_add, Finsupp.degree_single] using
    (mem_multiplierIndices d W a.1 a.2.val).mp a.2.property

noncomputable def productIndex (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : MultiplierIndex d W) : activeIndices d W := by
  have hb (i : Fin n) : productExponent d W a i < 2 ^ W := by
    have hi : productExponent d W a i ≤ (productExponent d W a).degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact (hi.trans_eq (productExponent_degree d W a)).trans_lt hW
  refine ⟨FixedWidthPolynomial.index n W (productExponent d W a) hb, ?_⟩
  rw [mem_activeIndices, FixedWidthPolynomial.vector_index, productExponent_degree]

theorem vector_productIndex (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : MultiplierIndex d W) :
    FixedWidthPolynomial.vector n W (productIndex d W hW a).val = productExponent d W a :=
  FixedWidthPolynomial.vector_index n W _ _

theorem productIndex_selected (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (r : activeIndices d W) : productIndex d W hW (selectedMultiplier d W r) = r := by
  apply Subtype.ext
  apply FixedWidthPolynomial.vector_injective n W
  rw [vector_productIndex]
  exact selectedMultiplier_add d W r

theorem sourceRow_powers (d : Fin n → ℕ) (W : ℕ) (a : MultiplierIndex d W) :
    sourceRow (powers (R := R) d) d W a = MvPolynomial.monomial (productExponent d W a) 1 := by
  simp only [sourceRow, powers, MvPolynomial.monomial_mul_monomial, one_mul, productExponent]

theorem fullMatrix_powers_apply (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : MultiplierIndex d W) (r : activeIndices d W) :
    fullMatrix (powers (R := R) d) d W a r = if productIndex d W hW a = r then 1 else 0 := by
  change (sourceRow (powers (R := R) d) d W a).coeff (FixedWidthPolynomial.vector n W r.val) = _
  rw [sourceRow_powers, MvPolynomial.coeff_monomial]
  have he : productExponent d W a = FixedWidthPolynomial.vector n W r.val ↔ productIndex d W hW a = r := by
    rw [← vector_productIndex d W hW a]
    exact (FixedWidthPolynomial.vector_injective n W).eq_iff.trans Subtype.val_injective.eq_iff
  simp only [he]

noncomputable def divisionRow (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : MultiplierIndex d W) : MultiplierIndex d W :=
  selectedMultiplier d W (productIndex d W hW a)

noncomputable def divisionExponent (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : MultiplierIndex d W) : Fin n →₀ ℕ :=
  FixedWidthPolynomial.vector n W a.2.val -
    Finsupp.single (divisionRow d W hW a).1 (d (divisionRow d W hW a).1)

theorem divisionExponent_add (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : MultiplierIndex d W) (ha : a.1 ≠ (divisionRow d W hW a).1) :
    divisionExponent d W hW a + Finsupp.single (divisionRow d W hW a).1 (d (divisionRow d W hW a).1) =
      FixedWidthPolynomial.vector n W a.2.val := by
  have hj := pivot_le d _ ((mem_activeIndices d W (productIndex d W hW a).val).mp
    (productIndex d W hW a).property)
  change d (divisionRow d W hW a).1 ≤
    FixedWidthPolynomial.vector n W (productIndex d W hW a).val (divisionRow d W hW a).1 at hj
  rw [vector_productIndex] at hj
  have hb : Finsupp.single (divisionRow d W hW a).1 (d (divisionRow d W hW a).1) ≤
      FixedWidthPolynomial.vector n W a.2.val := by
    apply Finsupp.single_le_iff.mpr
    simpa only [productExponent, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm ha), add_zero] using hj
  exact tsub_add_cancel_of_le hb

theorem divisionExponent_add_original (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : MultiplierIndex d W) (ha : a.1 ≠ (divisionRow d W hW a).1) :
    divisionExponent d W hW a + Finsupp.single a.1 (d a.1) =
      FixedWidthPolynomial.vector n W (divisionRow d W hW a).2.val := by
  apply add_right_cancel (b := Finsupp.single (divisionRow d W hW a).1 (d (divisionRow d W hW a).1))
  calc
    _ = (divisionExponent d W hW a +
        Finsupp.single (divisionRow d W hW a).1 (d (divisionRow d W hW a).1)) +
          Finsupp.single a.1 (d a.1) := by ac_rfl
    _ = productExponent d W a := by rw [divisionExponent_add d W hW a ha]; rfl
    _ = _ := by
      rw [← vector_productIndex d W hW a]
      exact (selectedMultiplier_add d W (productIndex d W hW a)).symm

theorem divisionExponent_grade (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : MultiplierIndex d W) (ha : a.1 ≠ (divisionRow d W hW a).1) :
    (divisionExponent d W hW a).degree + d a.1 + d (divisionRow d W hW a).1 = level d := by
  have he := congrArg Finsupp.degree (divisionExponent_add d W hW a ha)
  simp only [map_add, Finsupp.degree_single] at he
  have hg := (mem_multiplierIndices d W a.1 a.2.val).mp a.2.property
  omega

theorem sourceCoefficients_single (d : Fin n → ℕ) (W : ℕ) (a : MultiplierIndex d W) :
    sourceCoefficients (Pi.single a.1 (MvPolynomial.monomial (FixedWidthPolynomial.vector n W a.2.val) (1 : R))) d W =
      Pi.single a 1 := by
  rcases a with ⟨i, a⟩
  funext b
  rcases b with ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simp only [sourceCoefficients, Pi.single_eq_same, MvPolynomial.coeff_monomial, Pi.single_apply,
      Sigma.mk.inj_iff, heq_eq_eq, (FixedWidthPolynomial.vector_injective n W).eq_iff,
      Subtype.val_injective.eq_iff, true_and]
    simp only [eq_comm]
  · simp [sourceCoefficients, Ne.symm hij]

theorem multiplierIndex_ext (d : Fin n → ℕ) (W : ℕ) (a b : MultiplierIndex d W)
    (hi : a.1 = b.1) (he : productExponent d W a = productExponent d W b) : a = b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  change i = j at hi
  subst j
  apply congrArg (Sigma.mk i)
  apply Subtype.ext
  apply FixedWidthPolynomial.vector_injective n W
  exact add_right_cancel he

noncomputable def divisionRelations (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    Matrix (MultiplierIndex d W) (MultiplierIndex d W) R := fun a =>
  if a.1 = (divisionRow d W hW a).1 then 0 else
    sourceCoefficients (koszulMultipliers p a.1 (divisionRow d W hW a).1 (divisionExponent d W hW a)) d W

theorem divisionRelations_powers (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : MultiplierIndex d W) :
    divisionRelations (powers (R := R) d) d W hW a = Pi.single a 1 - Pi.single (divisionRow d W hW a) 1 := by
  by_cases ha : a.1 = (divisionRow d W hW a).1
  · have he : a = divisionRow d W hW a := by
      have ht := selectedMultiplier_add d W (productIndex d W hW a)
      rw [vector_productIndex] at ht
      exact multiplierIndex_ext d W a _ ha ht.symm
    rw [divisionRelations, ite_eq_left ha, ← he, sub_self]
  · rw [divisionRelations, ite_eq_right ha]
    have hq : koszulMultipliers (powers (R := R) d) a.1 (divisionRow d W hW a).1 (divisionExponent d W hW a) =
        Pi.single a.1 (MvPolynomial.monomial (FixedWidthPolynomial.vector n W a.2.val) 1) -
          Pi.single (divisionRow d W hW a).1
            (MvPolynomial.monomial (FixedWidthPolynomial.vector n W (divisionRow d W hW a).2.val) 1) := by
      simp only [koszulMultipliers, powers, MvPolynomial.monomial_mul_monomial, one_mul,
        divisionExponent_add d W hW a ha, divisionExponent_add_original d W hW a ha]
    rw [hq]
    have hs (q r : Fin n → MvPolynomial (Fin n) R) :
        sourceCoefficients (q - r) d W = sourceCoefficients q d W - sourceCoefficients r d W := by
      funext b
      simp only [sourceCoefficients, Pi.sub_apply, MvPolynomial.coeff_sub]
    rw [hs, sourceCoefficients_single, sourceCoefficients_single]

theorem fullMatrix_powers_rowSelection_apply (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a b : MultiplierIndex d W) :
    (fullMatrix (powers (R := R) d) d W * MatrixMinorSection.rowSelection (R := R) (selectedMultiplier d W)) a b =
      (Pi.single (divisionRow d W hW a) 1 : MultiplierIndex d W → R) b := by
  rw [Matrix.mul_apply]
  simp only [fullMatrix_powers_apply d W hW, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  change (1 : Matrix (MultiplierIndex d W) (MultiplierIndex d W) R) (divisionRow d W hW a) b = _
  simp only [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem powers_division_contraction (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    fullMatrix (powers (R := R) d) d W * MatrixMinorSection.rowSelection (R := R) (selectedMultiplier d W) +
      divisionRelations (powers (R := R) d) d W hW = 1 := by
  ext a b
  change (fullMatrix (powers (R := R) d) d W *
    MatrixMinorSection.rowSelection (R := R) (selectedMultiplier d W)) a b +
      divisionRelations (powers (R := R) d) d W hW a b = _
  rw [fullMatrix_powers_rowSelection_apply, divisionRelations_powers]
  have hone : (Pi.single a 1 : MultiplierIndex d W → R) b =
      (1 : Matrix (MultiplierIndex d W) (MultiplierIndex d W) R) a b := by
    simp only [Pi.single_apply, Matrix.one_apply, eq_comm]
  change (Pi.single (divisionRow d W hW a) 1 : MultiplierIndex d W → R) b +
    ((Pi.single a 1 : MultiplierIndex d W → R) b -
      (Pi.single (divisionRow d W hW a) 1 : MultiplierIndex d W → R) b) = _
  rw [← hone]
  ring

theorem divisionRelations_mul_fullMatrix (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (hp : ∀ i, (p i).IsHomogeneous (d i)) :
    divisionRelations p d W hW * fullMatrix p d W = 0 := by
  ext a r
  change Matrix.vecMul (divisionRelations p d W hW a) (fullMatrix p d W) r = 0
  by_cases ha : a.1 = (divisionRow d W hW a).1
  · rw [divisionRelations, ite_eq_left ha, Matrix.zero_vecMul]
    rfl
  · rw [divisionRelations, ite_eq_right ha, koszul_vecMul_eq_zero p d W hp hW _ _ ha _
      (divisionExponent_grade d W hW a ha)]
    rfl

theorem powers_kernel_iff (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (v : MultiplierIndex d W → R) :
    Matrix.vecMul v (fullMatrix (powers (R := R) d) d W) = 0 ↔
      Matrix.vecMul v (divisionRelations (powers (R := R) d) d W hW) = v := by
  constructor
  · intro hv
    have he := congrArg (Matrix.vecMul v) (powers_division_contraction (R := R) d W hW)
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul, zero_add, Matrix.vecMul_one] at he
    exact he
  · intro hv
    rw [← hv, Matrix.vecMul_vecMul, divisionRelations_mul_fullMatrix (powers (R := R) d) d W hW
      (fun i => MvPolynomial.isHomogeneous_monomial 1 (Finsupp.degree_single i (d i))), Matrix.vecMul_zero]
end LeanCanny.Algebra.Macaulay
