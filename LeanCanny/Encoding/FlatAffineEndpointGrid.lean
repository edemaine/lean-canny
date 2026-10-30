/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointGram
public import LeanCanny.Algebra.SingleParameterShiftSpace

/-! # Native access to the full frozen-endpoint coordinate grid

An extra query field selects any coordinate without changing the prepared
source record. The original extended-row reader is charged at its retained
context, and invalid diagonal-grid coordinate indices return zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointGrid
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open MacaulayFullBoxBits (ctx shift uv ctx_FP shift_FP uv_FP)
open AffineValueGramBits (base base_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def coordinate (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (r : List Bool) (i : Fin (FlatAffineEndpointRows.arity F r)) : Polynomial (Polynomial ℤ) :=
  Geometry.AffineShiftCoordinates.coordinate (FlatAffineEndpointPreparation.system F height r)
    (fun j => if j = FlatAffineEndpointGram.active F height r then Polynomial.X else 0)
    (FlatAffineEndpointPreparation.degrees F r) i

noncomputable def family (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : AffineShiftCoordinateBits.Family where
  arity z := FlatAffineEndpointRows.arity F (pairFst z)
  width z := AffineRingCoordinates.width (FlatAffineEndpointPreparation.degrees F (pairFst z))
  degree z := FlatAffineEndpointGram.degree F (pairFst z)
  rows z := FlatAffineEndpointPreparation.system F height (pairFst z)
  shifts z i := if i = FlatAffineEndpointGram.active F height (pairFst z) then Polynomial.X else 0
  coordinate := FlatAffineEndpointGram.indexRow F

def degreeQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
theorem degreeQuery_FP : degreeQuery ∈ FP := by polytime [degreeQuery]

theorem degree_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) :
    BinaryFn (fun q => (family F height).degree (pairFst q) (Nat.fromBitsLE (pairSnd q))) := by
  apply BinaryFn.of_eq ((FlatAffineEndpointGram.degree_binary h).comp degreeQuery_FP)
  intro q
  simp only [Function.comp_apply, degreeQuery, pairFst_pair, pairSnd_pair]
  rfl

theorem width_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (family F height).width z = AffineRingCoordinates.width
      (fun i : Fin ((family F height).arity z) => (family F height).degree z i.val) := by
  change AffineRingCoordinates.width (FlatAffineEndpointPreparation.degrees F (pairFst z)) =
    AffineRingCoordinates.width (fun i => FlatAffineEndpointPreparation.degrees F (pairFst z)
      (FlatAffineEndpointCoefficient.rowAt F (pairFst z) i.val))
  exact congrArg AffineRingCoordinates.width (funext (fun i => congrArg
    (FlatAffineEndpointPreparation.degrees F (pairFst z)) (FlatAffineEndpointCoefficient.rowAt_val F (pairFst z) i).symm))

theorem controls {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) :
    (family F height).parameter.affine.homogeneous.layout.Controls :=
  (family F height).controls ((FlatAffineEndpointRows.arity_unary h).comp pairFst_mem_FP)
    (degree_binary h height) (width_eq F height)

theorem originalEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (family F height).integerCoefficient := by
  let G := family F height
  have hG := controls h height
  exact FlatAffineEndpointCoefficient.rowEvaluator h height hh (pairFst ∘ base) (mem_FP_comp base_FP pairFst_mem_FP)
    G.row (G.row_unary hG) (hG.width.comp base_FP) shift_FP (mem_FP_comp ctx_FP pairSnd_mem_FP)

theorem shiftEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (family F height).shiftCoefficient := by
  let G := family F height
  have hG := controls h height
  have hp := mem_FP_comp base_FP pairFst_mem_FP
  have H := PolynomialParameterShiftBits.singleScalarEvaluator (fun q => (G.row q).val)
    (fun q => (FlatAffineEndpointGram.active F height (pairFst (base q))).val)
    (G.row_unary hG) ((FlatAffineEndpointGram.active_unary height hh).comp hp)
    (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q)) (mem_FP_comp uv_FP pairFst_mem_FP)
    (mem_FP_comp ctx_FP pairSnd_mem_FP)
  refine H.congr (funext fun q => ?_)
  simp only [PolynomialParameterShiftBits.scalar, AffineShiftCoordinateBits.Family.shiftCoefficient,
    AffineShiftCoordinateBits.Family.selectedShift, family, Fin.ext_iff]
  rfl

noncomputable def indexed (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : Polynomial (Polynomial ℤ) :=
  coordinate F height (pairFst z) (FlatAffineEndpointGram.indexRow F z)

noncomputable def indexedReader {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : CertifiedPolynomial.BivariateReader (indexed F height) := by
  let G := family F height
  have E := G.canonicalReader ((FlatAffineEndpointRows.arity_unary h).comp pairFst_mem_FP) (degree_binary h height)
    (FlatAffineEndpointGram.indexRow_unary h) (fun _ => 1) (BinaryFn.const 1) (fun z i => by
      change (if i = FlatAffineEndpointGram.active F height (pairFst z) then (Polynomial.X : Polynomial ℤ) else 0).natDegree ≤ 1
      split_ifs <;> simp) (width_eq F height) (originalEvaluator h height hh) (shiftEvaluator h height hh)
  have he : (fun z => Geometry.AffineShiftCoordinates.coordinate (G.rows z) (G.shifts z)
      (fun i => G.degree z i.val) (G.coordinate z)) = indexed F height := by
    funext z
    have hd : (fun i : Fin (FlatAffineEndpointRows.arity F (pairFst z)) => G.degree z i.val) =
        FlatAffineEndpointPreparation.degrees F (pairFst z) := by
      funext i
      exact congrArg (FlatAffineEndpointPreparation.degrees F (pairFst z))
        (FlatAffineEndpointCoefficient.rowAt_val F (pairFst z) i)
    exact congrArg (fun d : Fin (FlatAffineEndpointRows.arity F (pairFst z)) → ℕ =>
      Geometry.AffineShiftCoordinates.coordinate (FlatAffineEndpointPreparation.system F height (pairFst z))
        (fun i : Fin (FlatAffineEndpointRows.arity F (pairFst z)) =>
          if i = FlatAffineEndpointGram.active F height (pairFst z) then Polynomial.X else 0)
        d (FlatAffineEndpointGram.indexRow F z)) hd
  exact he ▸ E

def Valid (F : Inputs) (z : List Bool) : Prop := Nat.fromBitsLE (pairSnd z) < FlatAffineEndpointRows.arity F (pairFst z)
instance (F : Inputs) : DecidablePred (Valid F) := fun _ => inferInstanceAs (Decidable (_ < _))

theorem valid_fppred {F : Inputs} (h : F.Access) : FPPred (Valid F) :=
  (BinaryFn.fromBits pairSnd_mem_FP).lt (BinaryFn.ofUnary ((FlatAffineEndpointRows.arity_unary h).comp pairFst_mem_FP))

lemma selected_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    DiagonalParameterBits.selected (FlatAffineEndpointRows.arity F) (coordinate F height) z =
      if Valid F z then indexed F height z else 0 := by
  rw [DiagonalParameterBits.selected, DiagonalParameterBits.selectedAt]
  unfold Valid
  by_cases hv : Nat.fromBitsLE (pairSnd z) < FlatAffineEndpointRows.arity F (pairFst z)
  · rw [dite_eq_left hv, ite_eq_left hv]
    exact congrArg (coordinate F height (pairFst z))
      (FlatAffineEndpointCoefficient.rowAt_val F (pairFst z) ⟨Nat.fromBitsLE (pairSnd z), hv⟩).symm
  · rw [dite_eq_right hv, ite_eq_right hv]

theorem coefficientEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (DiagonalParameterBits.selected (FlatAffineEndpointRows.arity F) (coordinate F height))) := by
  have hp := (valid_fppred h).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have ER := BivariateReaderCanonical.evaluator (indexedReader h height hh)
  have E := ModularResidueReaders.maskEvaluator hp ER
  refine E.congr (funext fun q => ?_)
  simp only [ModularResidueReaders.maskValue, SymbolicFixedTableEntryBits.coefficient, selected_eq, Function.comp_apply]
  by_cases hv : Valid F (pairFst (pairFst q))
  · simp only [hv, ite_true]
  · simp [hv, SymbolicFixedTableEntryBits.integerResidue, residueBits, BinaryNatCode.encode]

end LeanCanny.Encoding.FlatAffineEndpointGrid
