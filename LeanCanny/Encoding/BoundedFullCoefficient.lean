/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedRegularCoefficient
public import LeanCanny.Encoding.BoundedFullGeometry
public import LeanCanny.Encoding.FixedWidthRotate

/-! # Native modular coefficients in the full source's coordinate order -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullCoefficient
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MatrixPower RationalSubstitution.Indexed MvPolynomial
open scoped Classical

noncomputable def value (P : Readers) (W : List Bool → ℕ) (target modulus : List Bool → List Bool)
    (c : List Bool) : List Bool :=
  residueBits (((BoundedFullGeometry.polynomial (original P c) (size P c) (size P c) (P.radius c)).coeff
    (exponentVector (P.dim c + 4) (FixedWidthQuery.coordinate W target c)) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))

/-- Scalar packet semantics avoid dependent finite-tuple transport when
coefficient calls are made from a larger native query. -/
noncomputable def valueData (source : List Bool) (dim radius W : ℕ) (target modulus : List Bool) : List Bool :=
  value ⟨fun _ => source, fun _ => dim, fun _ => radius⟩ (fun _ => W) (fun _ => target) (fun _ => modulus) []

theorem value_data (P : Readers) (W : List Bool → ℕ) (target modulus : List Bool → List Bool) (c : List Bool) :
    value P W target modulus c = valueData (P.source c) (P.dim c) (P.radius c) (W c) (target c) (modulus c) := rfl

private theorem index_eq (n : ℕ) (i : Fin (n + 4)) :
    FixedWidthRotate.index (n + 4) i.val = (BoundedFullGeometry.inputIndex (n + 3) i).val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [FixedWidthRotate.index, BoundedFullGeometry.inputIndex]
  · simp [FixedWidthRotate.index, BoundedFullGeometry.inputIndex]

theorem coefficient_rotate (P : Readers) (W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) :
    (BoundedFullGeometry.polynomial (original P c) (size P c) (size P c) (P.radius c)).coeff
        (exponentVector (P.dim c + 4) (FixedWidthQuery.coordinate W target c)) =
      (BoundedRegularSource.polynomial (original P c) (size P c) (size P c) (P.radius c)).coeff
        (exponentVector (P.dim c + 4)
          (FixedWidthQuery.coordinate W (FixedWidthRotate.word (fun c => P.dim c + 4) W target) c)) := by
  let f := BoundedFullGeometry.inputEquiv (P.dim c + 3)
  let e := exponentVector (P.dim c + 4) (FixedWidthQuery.coordinate W target c)
  have hr : exponentVector (P.dim c + 4)
      (FixedWidthQuery.coordinate W (FixedWidthRotate.word (fun c => P.dim c + 4) W target) c) = e.mapDomain f.symm := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, exponentVector,
      Finsupp.coe_equivFunOnFinite_symm, e]
    rw [FixedWidthRotate.coordinate _ _ _ _ i.val i.isLt]
    rw [FixedWidthQuery.entry, index_eq]
    exact ite_eq_left (f i).isLt
  have he : e = (e.mapDomain f.symm).mapDomain f := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply]
  change (rename f (BoundedRegularSource.polynomial (original P c) (size P c) (size P c) (P.radius c))).coeff e = _
  rw [he, MvPolynomial.coeff_rename_mapDomain f f.injective, ← hr]

theorem evaluator {P : Readers} {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (h : P.PolyTime) (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (value P W target modulus) := by
  have he := BoundedRegularCoefficient.evaluator h hW
    (FixedWidthRotate.word_mem_FP (h.dim.add (UnaryFn.const 4)) hW ht) hm ha
  apply he.congr
  funext c
  unfold BoundedRegularCoefficient.value value
  rw [coefficient_rotate P W target c]

end LeanCanny.Encoding.BoundedFullCoefficient
