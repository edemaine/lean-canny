/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayShiftedKoszul
public import LeanCanny.Algebra.MacaulayExtraneousLast
public import LeanCanny.Algebra.CharacteristicQuotientDegree
public import LeanCanny.Algebra.MatrixMinorSection
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Surjectivity of the generic shifted graded multiplication map

Over the rational-function field in the characteristic parameter, the selected
square minor is invertible. Its inverse gives a section of the full row map.
For homogeneous inputs, every polynomial at the Macaulay level is therefore
an explicit linear combination of the shifted inputs and belongs to their ideal.
The ideal contains the level power of the variable ideal, so any common zero
over an integral-domain coefficient extension is the origin.
Higher Koszul exactness and resultant cancellation are not asserted here.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem assemble_homogeneous (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (v : MultiplierIndex d W → R) :
    (assemble p d W v).IsHomogeneous (level d) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro a _
  exact (sourceRow_homogeneous p d W hp a).C_mul (v a)

theorem homogeneous_eq_of_active_coefficients (f g : MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hW : level d < 2 ^ W) (hf : f.IsHomogeneous (level d)) (hg : g.IsHomogeneous (level d))
    (h : ∀ r : activeIndices d W, f.coeff (FixedWidthPolynomial.vector n W r.val) =
      g.coeff (FixedWidthPolynomial.vector n W r.val)) : f = g := by
  apply MvPolynomial.ext
  intro m
  by_cases hm : m.degree = level d
  · have hb (i : Fin n) : m i < 2 ^ W := by
      have hi : m i ≤ m.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact (hi.trans_eq hm).trans_lt hW
    let r := FixedWidthPolynomial.index n W m hb
    have hr : r ∈ activeIndices d W := by
      rw [mem_activeIndices, FixedWidthPolynomial.vector_index]
      exact hm
    have he := h ⟨r, hr⟩
    simpa only [r, FixedWidthPolynomial.vector_index] using he
  · rw [hf.coeff_eq_zero hm, hg.coeff_eq_zero hm]

theorem assemble_mem_span (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (v : MultiplierIndex d W → R) : assemble p d W v ∈ Ideal.span (Set.range p) := by
  apply (Ideal.span (Set.range p)).sum_mem
  intro a _
  unfold sourceRow
  rw [← mul_assoc]
  exact (Ideal.span (Set.range p)).mul_mem_left _ (Ideal.subset_span (Set.mem_range_self a.1))

variable [IsDomain R]

noncomputable def genericShift (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) :
    Fin n → MvPolynomial (Fin n) (RatFunc R) :=
  fun i => (subtractiveSystem p d i).map (algebraMap (Polynomial R) (RatFunc R))

theorem genericShift_homogeneous (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (i : Fin n) :
    (genericShift p d i).IsHomogeneous (d i) :=
  (subtractiveSystem_homogeneous p d hp i).map (algebraMap (Polynomial R) (RatFunc R))

theorem genericShift_selected_det_ne_zero (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    ((fullMatrix (genericShift p d) d W).submatrix (selectedMultiplier d W) id).det ≠ 0 := by
  rw [fullMatrix_selected]
  have h := det_activeMinor_map (algebraMap (Polynomial R) (RatFunc R)) (subtractiveSystem p d) d W
  rw [activeMinor_subtractiveSystem] at h
  change (algebraMap (Polynomial R) (RatFunc R))
    (AffineCharacteristic.subtractiveMatrix (activeMinor p d W)).det =
    (activeMinor (genericShift p d) d W).det at h
  rw [← h]
  exact RatFunc.algebraMap_ne_zero (AffineCharacteristic.subtractive_det_ne_zero (activeMinor p d W))

noncomputable def genericShiftSection (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    Matrix (activeIndices d W) (MultiplierIndex d W) (RatFunc R) :=
  MatrixMinorSection.sectionMatrix (fullMatrix (genericShift p d) d W) (selectedMultiplier d W)

theorem genericShiftSection_mul (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    genericShiftSection p d W * fullMatrix (genericShift p d) d W = 1 :=
  MatrixMinorSection.sectionMatrix_mul _ _ (isUnit_iff_ne_zero.mpr (genericShift_selected_det_ne_zero p d W))

theorem genericShift_vecMul_surjective (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    Function.Surjective (Matrix.vecMul · (fullMatrix (genericShift p d) d W)) :=
  MatrixMinorSection.vecMul_surjective _ _ (isUnit_iff_ne_zero.mpr (genericShift_selected_det_ne_zero p d W))

theorem genericShift_assemble_surjective (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (f : MvPolynomial (Fin n) (RatFunc R)) (hf : f.IsHomogeneous (level d)) :
    ∃ v : MultiplierIndex d W → RatFunc R, assemble (genericShift p d) d W v = f := by
  obtain ⟨v, hv⟩ := genericShift_vecMul_surjective p d W
    (fun r => f.coeff (FixedWidthPolynomial.vector n W r.val))
  refine ⟨v, homogeneous_eq_of_active_coefficients _ f d W hW
    (assemble_homogeneous _ d W (genericShift_homogeneous p d hp) v) hf ?_⟩
  intro r
  have he := congrFun hv r
  change Matrix.vecMul v (fullMatrix (genericShift p d) d W) r =
    f.coeff (FixedWidthPolynomial.vector n W r.val) at he
  rw [vecMul_fullMatrix] at he
  exact he

theorem genericShift_homogeneous_mem_span (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (f : MvPolynomial (Fin n) (RatFunc R)) (hf : f.IsHomogeneous (level d)) :
    f ∈ Ideal.span (Set.range (genericShift p d)) := by
  obtain ⟨v, hv⟩ := genericShift_assemble_surjective p d W hp hW f hf
  rw [← hv]
  exact assemble_mem_span _ d W v

theorem genericShift_monomial_mem_span (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (m : Fin n →₀ ℕ) (hm : m.degree = level d) :
    MvPolynomial.monomial m (1 : RatFunc R) ∈ Ideal.span (Set.range (genericShift p d)) :=
  genericShift_homogeneous_mem_span p d W hp hW _ (MvPolynomial.isHomogeneous_monomial 1 hm)

theorem genericShift_power_idealOfVars_le (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W) :
    MvPolynomial.idealOfVars (Fin n) (RatFunc R) ^ level d ≤
      Ideal.span (Set.range (genericShift p d)) := by
  rw [MvPolynomial.pow_idealOfVars_eq_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨m, hm, rfl⟩
  exact genericShift_monomial_mem_span p d W hp hW m hm

theorem genericShift_common_zero {S : Type*} [CommRing S] [IsDomain S]
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (φ : RatFunc R →+* S) (x : Fin n → S)
    (hx : ∀ i, MvPolynomial.eval₂Hom φ x (genericShift p d i) = 0) : x = 0 := by
  have hker : Ideal.span (Set.range (genericShift p d)) ≤ RingHom.ker (MvPolynomial.eval₂Hom φ x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (hx i)
  funext i
  apply eq_zero_of_pow_eq_zero (n := level d)
  have hi := hker (genericShift_monomial_mem_span p d W hp hW
    (Finsupp.single i (level d)) (Finsupp.degree_single _ _))
  simpa [RingHom.mem_ker, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_single_index] using hi

end LeanCanny.Algebra.Macaulay
