/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.ParameterizedBoundaryRadiusHead
public import LeanCanny.Computation.PolyTimeBinaryNat
/-! # Binary original-source controls for the boundary-radius exponent -/
@[expose] public section
namespace LeanCanny.Geometry.ParameterizedBoundaryRadiusBudget
open LeanCanny LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem size_unary {f : List Bool → ℕ} (hf : BinaryFn f) : UnaryFn (fun u => (f u).size) :=
  (UnaryFn.length hf.bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (f u))

private theorem width_unary {N D : List Bool → ℕ} (hN : UnaryFn N) (hD : BinaryFn D) :
    UnaryFn (fun u => CoerciveCoordinateEliminant.width (N u) (D u)) := by
  have HL : BinaryFn (fun u => Macaulay.level (CoerciveCriticalHomogenization.finDegree (n := N u) (D u))) := by
    have H := ((BinaryFn.ofUnary hN).mul ((BinaryFn.const 2).mul hD)).add (BinaryFn.const 1)
    apply H.of_eq
    intro u
    unfold Macaulay.level CoerciveCriticalHomogenization.finDegree CoerciveCriticalHomogenization.nativeDegree
    rw [←Equiv.sum_comp CoerciveCriticalHomogenization.layout]
    simp only [Equiv.symm_apply_apply,Fintype.sum_option,Nat.sub_self,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.add_sub_cancel,zero_add]
  have HD := ((BinaryFn.const 2).mul hD).add (BinaryFn.const 1)
  exact size_unary ((BinaryFn.ite (HL.le HD) HD HL).of_eq (fun _ => (max_def _ _).symm))

theorem dimension_binary {N D : List Bool → ℕ} (hN : UnaryFn N) (hD : BinaryFn D) :
    BinaryFn (fun u => ParameterizedBoundaryGramMass.dimension (N u) (D u)) := by
  have HE : BinaryFn (fun u => ParameterizedBoundaryGramValues.degreeBound (D u)) :=
    ((BinaryFn.const 4).mul hD).add (BinaryFn.const 6)
  have HN := hN.add (UnaryFn.const 2)
  have HW := width_unary HN HE
  have HC : BinaryFn (fun u => CoerciveBoxGramEliminant.columnCount (N u+2)
      (ParameterizedBoundaryGramValues.degreeBound (D u))) :=
    ((BinaryFn.const 2).powUnary ((HN.add (UnaryFn.const 1)).mul HW)).of_eq (fun u => by
      simp only [CoerciveBoxGramEliminant.columnCount,FixedWidthPolynomial.count,←pow_mul,Nat.mul_comm])
  exact ((BinaryFn.ofUnary (HN.add (UnaryFn.const 3))).mul HC)

theorem slope_binary {N D : List Bool → ℕ} (hN : UnaryFn N) (hD : BinaryFn D) :
    BinaryFn (fun u => ParameterizedBoundaryGramMass.slope (N u) (D u)) :=
  (BinaryFn.const 8).mul (dimension_binary hN hD)

theorem offset_binary {N D B : List Bool → ℕ} (hN : UnaryFn N) (hD : BinaryFn D) (hB : BinaryFn B) :
    BinaryFn (fun u => ParameterizedBoundaryGramMass.offset (N u) (D u) (B u)) := by
  have HR := dimension_binary hN hD
  have HE : BinaryFn (fun u => ParameterizedBoundaryGramValues.degreeBound (D u)) :=
    ((BinaryFn.const 4).mul hD).add (BinaryFn.const 6)
  have HB := ParameterizedBoundaryEnergyMass.energyOffset_binary (BinaryFn.ofUnary hN) hD hB
  exact (HR.mul (((BinaryFn.const 2).mul HR.size).add
    ((BinaryFn.const 2).mul ((HE.size.add ((BinaryFn.const 2).mul HB)).add (BinaryFn.const 3))))).add
      (BinaryFn.const 1)

theorem coefficientBits_binary {N D B : List Bool → ℕ} (hN : UnaryFn N) (hD : BinaryFn D) (hB : BinaryFn B) :
    BinaryFn (fun u => ParameterizedBoundaryGramMass.coefficientBits (N u) (D u) (B u)) :=
  IntegerPolynomialDyadic.massBudget_binary (BinaryFn.const 0) (slope_binary hN hD) (offset_binary hN hD hB)

theorem headBits_binary {N D B : List Bool → ℕ} (hN : UnaryFn N) (hD : BinaryFn D) (hB : BinaryFn B) :
    BinaryFn (fun u => ParameterizedBoundaryGramMass.headBits (N u) (D u) (B u)) :=
  (coefficientBits_binary hN hD hB).add ((dimension_binary hN hD).add (BinaryFn.const 1)).size

theorem radiusExponent_binary {N D B : List Bool → ℕ} (hN : UnaryFn N) (hD : BinaryFn D) (hB : BinaryFn B) :
    BinaryFn (fun u => ParameterizedBoundaryRadiusHead.radiusExponent (N u) (D u) (B u)) :=
  (headBits_binary hN hD hB).add (BinaryFn.const 1)

end LeanCanny.Geometry.ParameterizedBoundaryRadiusBudget
