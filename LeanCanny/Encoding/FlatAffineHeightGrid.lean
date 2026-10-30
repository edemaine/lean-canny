/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightGram
public import LeanCanny.Algebra.BivariateReaderCanonical
public import LeanCanny.Algebra.DiagonalPolynomialParameterSpace
public import LeanCanny.Algebra.ModularResidueReaders

/-! # Native access to the entire varying-height coordinate grid

An indexed query selects any coordinate of the actual affine power tower.
Invalid coordinate indices return zero. Reindexing retains the original
signed-record source, and canonical coefficient access accepts all raw words.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightGrid
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def coordinate (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) (i : Fin (count F u)) : Polynomial (Polynomial ℤ) :=
  Geometry.AffineShiftCoordinates.coordinate (FlatAffinePowerPositive.system F u)
    (fun j => if j = height u then Polynomial.X else 0) (FlatAffinePowerPositive.degree F u) i

lemma coordinate_comp (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (f : List Bool → List Bool) (u : List Bool) (i : Fin (count F (f u))) :
    coordinate (FlatAffineFullSourceContext.comp F f) (fun z => height (f z)) u i =
      coordinate F height (f u) i := by
  have hs := funext (FlatAffinePowerPositive.system_comp F f u)
  have hd := funext (FlatAffinePowerPositive.degree_comp F f u)
  exact congrArg₂ (fun p d => Geometry.AffineShiftCoordinates.coordinate p
    (fun j => if j = height (f u) then Polynomial.X else 0) d i) hs hd

noncomputable def indexed (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    Polynomial (Polynomial ℤ) :=
  coordinate (FlatAffineFullSourceContext.comp F pairFst) (fun q => height (pairFst q)) z
    (FlatAffineHeightGram.rawRow F (pairFst z) (Nat.fromBitsLE (pairSnd z)))

def Valid (F : Inputs) (z : List Bool) : Prop := Nat.fromBitsLE (pairSnd z) < count F (pairFst z)
instance (F : Inputs) : DecidablePred (Valid F) := fun _ => inferInstanceAs (Decidable (_ < _))

theorem valid_FP {F : Inputs} (h : F.Access) : FPPred (Valid F) :=
  (BinaryFn.fromBits pairSnd_mem_FP).lt (BinaryFn.ofUnary ((FlatAffineFullSourcePositive.count_unary h).comp pairFst_mem_FP))

lemma selected_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    DiagonalParameterBits.selected (count F) (coordinate F height) z =
      if Valid F z then indexed F height z else 0 := by
  rw [DiagonalParameterBits.selected, DiagonalParameterBits.selectedAt]
  unfold Valid
  by_cases hz : Nat.fromBitsLE (pairSnd z) < count F (pairFst z)
  · rw [dite_eq_left hz, ite_eq_left hz, indexed, coordinate_comp]
    exact congrArg (coordinate F height (pairFst z))
      (FlatAffineHeightGram.rawRow_val F (pairFst z) ⟨Nat.fromBitsLE (pairSnd z), hz⟩).symm
  · rw [dite_eq_right hz, ite_eq_right hz]

noncomputable def indexedReader {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : CertifiedPolynomial.BivariateReader (indexed F height) := by
  have hc : UnaryFn (fun z => (FlatAffineHeightGram.rawRow F (pairFst z) (Nat.fromBitsLE (pairSnd z))).val) :=
    UnaryFn.fromBitsLE_min pairSnd_mem_FP (((FlatAffineFullSourcePositive.count_unary h).comp pairFst_mem_FP).sub (UnaryFn.const 1))
  exact FlatAffineHeightGram.reader (FlatAffineFullSourceContext.access h pairFst_mem_FP)
    (fun q => height (pairFst q)) (fun q => FlatAffineHeightGram.rawRow F (pairFst q) (Nat.fromBitsLE (pairSnd q)))
    (hh.comp pairFst_mem_FP) hc

/-- All original coordinate polynomials have a native bivariate reader under
exactly the indexed convention required by the diagonal-grid value backend. -/
theorem coefficientEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (DiagonalParameterBits.selected (count F) (coordinate F height))) := by
  have hp := (valid_FP h).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have ER := BivariateReaderCanonical.evaluator (indexedReader h height hh)
  have E := ModularResidueReaders.maskEvaluator hp ER
  refine E.congr (funext fun q => ?_)
  simp only [ModularResidueReaders.maskValue, SymbolicFixedTableEntryBits.coefficient, selected_eq, Function.comp_apply]
  by_cases hv : Valid F (pairFst (pairFst q))
  · simp only [hv, ite_true]
  · simp [hv, SymbolicFixedTableEntryBits.integerResidue, residueBits, BinaryNatCode.encode]

end LeanCanny.Encoding.FlatAffineHeightGrid
