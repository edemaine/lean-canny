/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixSelectedBlock
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Arbitrary selectors and a selected relation block

Replacing the selected rows factors any contraction determinant by the
selected multiplication determinant. When both selected diagonal blocks
are units, the matrix determinant lemma also expresses that determinant
using an arbitrary target selector and the complementary relation block.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixSelectedMinorCross
open scoped Classical Matrix
variable {R S T : Type*} [CommRing R] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in
theorem rowSelection_mul_rectangular {U : Type*} (M : Matrix S U R) (f : T → S) :
    MatrixMinorSection.rowSelection f * M = M.submatrix f id :=
  Matrix.one_submatrix_mul f (Equiv.refl S) M

noncomputable def leftFactor (D : Matrix S T R) (f : T → S) : Matrix S S R :=
  Function.extend f ((D * MatrixMinorSection.rowSelection f).submatrix f id) (1 : Matrix S S R)

theorem leftFactor_det (D : Matrix S T R) (f : T → S) (hf : Function.Injective f) :
    (leftFactor D f).det = (D.submatrix f id).det := by
  let : Fintype (Set.range f) := Subtype.fintype (fun a : S => a ∈ Set.range f)
  have hu (a : S) (ha : a ∈ Set.range f) (b : S) (hb : b ∉ Set.range f) : leftFactor D f a b = 0 := by
    obtain ⟨t, rfl⟩ := ha
    change Function.extend f ((D * MatrixMinorSection.rowSelection f).submatrix f id) (1 : Matrix S S R) (f t) b = 0
    exact (congrFun (hf.extend_apply ((D * MatrixMinorSection.rowSelection f).submatrix f id) (1 : Matrix S S R) t) b).trans
      (MatrixSelectedBlock.mul_rowSelection_not_mem D f _ _ hb)
  rw [Matrix.twoBlockTriangular_det' _ (fun a => a ∈ Set.range f) hu]
  have hfirst : (Matrix.toSquareBlockProp (leftFactor D f) (fun a => a ∈ Set.range f)).det = (D.submatrix f id).det := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.ofInjective f hf)]
    apply congrArg Matrix.det
    funext a b
    change Function.extend f ((D * MatrixMinorSection.rowSelection f).submatrix f id) (1 : Matrix S S R) (f a) (f b) = D (f a) b
    exact (congrFun (hf.extend_apply ((D * MatrixMinorSection.rowSelection f).submatrix f id) (1 : Matrix S S R) a) (f b)).trans
      (congrFun (congrFun (MatrixSelectedBlock.mul_rowSelection_submatrix D f hf) a) b)
  have hsecond : Matrix.toSquareBlockProp (leftFactor D f) (fun a => a ∉ Set.range f) = 1 := by
    funext a b
    change Function.extend f ((D * MatrixMinorSection.rowSelection f).submatrix f id) (1 : Matrix S S R) a.val b.val =
      (1 : Matrix {a : S // a ∉ Set.range f} {a : S // a ∉ Set.range f} R) a b
    calc
      _ = (1 : Matrix S S R) a.val b.val := congrFun (Function.extend_apply'
        ((D * MatrixMinorSection.rowSelection f).submatrix f id) (1 : Matrix S S R) a.val a.property) b.val
      _ = (1 : Matrix {a : S // a ∉ Set.range f} {a : S // a ∉ Set.range f} R) a b := by
        simp only [Matrix.one_apply, Subtype.val_injective.eq_iff]
  rw [hfirst, hsecond, Matrix.det_one, mul_one]

theorem contraction_factorization (D : Matrix S T R) (E : Matrix S S R) (f : T → S) (hf : Function.Injective f)
    (hE : ∀ t, E (f t) = 0) (B : Matrix T S R) :
    (D * B + E).det = (D.submatrix f id).det * Matrix.det (Function.extend f B (D * B + E) : Matrix S S R) := by
  let M : Matrix S S R := Function.extend f B (D * B + E)
  let H : Matrix T S R := MatrixMinorSection.rowSelection f
  have hM : M.submatrix f id = B := by funext t b; exact congrFun (hf.extend_apply B (D * B + E) t) b
  have hHM : H * M = B := (rowSelection_mul_rectangular M f).trans hM
  have hprod : leftFactor D f * M = D * B + E := by
    funext a b
    by_cases ha : a ∈ Set.range f
    · obtain ⟨t, rfl⟩ := ha
      have hL : leftFactor D f (f t) = (D * H : Matrix S S R) (f t) :=
        hf.extend_apply _ _ t
      calc
        _ = ((D * H) * M : Matrix S S R) (f t) b := by simp only [Matrix.mul_apply, hL]
        _ = (D * B) (f t) b := by rw [Matrix.mul_assoc, hHM]
        _ = _ := by simp only [Matrix.add_apply, hE t, Pi.zero_apply, add_zero]
    · have hL : leftFactor D f a = (1 : Matrix S S R) a := Function.extend_apply' _ _ a ha
      calc
        _ = ((1 : Matrix S S R) * M) a b := by simp only [Matrix.mul_apply, hL]
        _ = M a b := by rw [Matrix.one_mul]
        _ = _ := congrFun (Function.extend_apply' B (D * B + E) a ha) b
  calc
    _ = (leftFactor D f * M).det := congrArg Matrix.det hprod.symm
    _ = _ := by rw [Matrix.det_mul, leftFactor_det D f hf]

theorem contraction_det_of_units (D : Matrix S T R) (E : Matrix S S R) (f : T → S) (hf : Function.Injective f)
    (hE : ∀ t, E (f t) = 0) (hED : E * D = 0)
    (hD : IsUnit (D.submatrix f id).det)
    (hR : IsUnit (E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det)
    (B : Matrix T S R) :
    (D * B + E).det = (B * D).det *
      (E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det := by
  let H : Matrix T S R := MatrixMinorSection.rowSelection f
  let A : Matrix S S R := D * H + E
  have hH : H * D = D.submatrix f id := MatrixMinorSection.rowSelection_mul D f
  have hA : A.det = (D.submatrix f id).det *
      (E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det :=
    MatrixSelectedBlock.determinant D E f hf hE
  have hAu : IsUnit A.det := hA ▸ hD.mul hR
  have hHu : IsUnit (H * D).det := hH ▸ hD
  have hAD : A * D = D * (H * D) := by
    change (D * H + E) * D = _
    rw [Matrix.add_mul, hED, add_zero, Matrix.mul_assoc]
  have hinv : A⁻¹ * D = D * (H * D)⁻¹ := by
    calc
      _ = (A⁻¹ * D * (H * D)) * (H * D)⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hHu, Matrix.mul_one]
      _ = D * (H * D)⁻¹ := by rw [Matrix.mul_assoc A⁻¹ D, ← hAD, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hAu, Matrix.one_mul]
  have hinside : 1 + (B - H) * A⁻¹ * D = (B * D) * (H * D)⁻¹ := by
    rw [Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_nonsing_inv _ hHu]
    abel
  have hadd : A + D * (B - H) = D * B + E := by
    dsimp only [A]
    rw [Matrix.mul_sub]
    abel
  rw [← hadd, Matrix.det_add_mul D (B - H) hAu, hinside, Matrix.det_mul, hA]
  calc
    _ = (B * D).det * (E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det *
        ((H * D).det * ((H * D)⁻¹).det) := by rw [hH]; ring
    _ = _ := by rw [← Matrix.det_mul, Matrix.mul_nonsing_inv _ hHu, Matrix.det_one, mul_one]

theorem contraction_det_of_ne_zero [IsDomain R]
    (D : Matrix S T R) (E : Matrix S S R) (f : T → S) (hf : Function.Injective f)
    (hE : ∀ t, E (f t) = 0) (hED : E * D = 0) (hD : (D.submatrix f id).det ≠ 0)
    (hR : (E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det ≠ 0)
    (B : Matrix T S R) :
    (D * B + E).det = (B * D).det *
      (E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det := by
  let φ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hinj : Function.Injective φ := FaithfulSMul.algebraMap_injective R (FractionRing R)
  have hDm : ((D.map φ).submatrix f id).det = φ (D.submatrix f id).det := (φ.map_det _).symm
  have hRm : ((E.map φ).submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det =
      φ (E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det := (φ.map_det _).symm
  have hDu : IsUnit ((D.map φ).submatrix f id).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hDm]
    exact fun hz => hD (hinj (hz.trans (map_zero φ).symm))
  have hRu : IsUnit ((E.map φ).submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hRm]
    exact fun hz => hR (hinj (hz.trans (map_zero φ).symm))
  have hEm : ∀ t, (E.map φ) (f t) = 0 := by
    intro t
    funext b
    change φ (E (f t) b) = 0
    rw [congrFun (hE t) b, Pi.zero_apply, map_zero]
  have hEDm : E.map φ * D.map φ = 0 := by
    rw [← Matrix.map_mul, hED]
    funext a b
    exact map_zero φ
  have hAm : (D * B + E).map φ = D.map φ * B.map φ + E.map φ := by
    rw [← Matrix.map_mul]
    funext a b
    exact φ.map_add _ _
  have hBDm : (B.map φ * D.map φ).det = φ (B * D).det := by
    rw [← Matrix.map_mul]
    exact (φ.map_det _).symm
  apply hinj
  calc
    _ = ((D * B + E).map φ).det := φ.map_det _
    _ = (B.map φ * D.map φ).det *
        ((E.map φ).submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det := by
      rw [hAm]
      exact contraction_det_of_units (D.map φ) (E.map φ) f hf hEm hEDm hDu hRu (B.map φ)
    _ = φ ((B * D).det * (E.submatrix (fun a : {a : S // a ∉ Set.range f} => a.val) (fun a => a.val)).det) := by
      rw [hBDm, hRm, map_mul]

end LeanCanny.Algebra.MatrixSelectedMinorCross
