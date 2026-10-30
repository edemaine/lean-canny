/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointGrid
public import LeanCanny.Algebra.FrozenAffineMidpointSpace

/-! # Native midpoint-value annihilators on the frozen endpoint grid

The extended coordinate grid and linear midpoint test both come from their
native source readers. Homogenization and the reciprocal Gram determinant
retain the external height parameter throughout.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointValues
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open MacaulayFullBoxBits (ctx shift uv ctx_FP shift_FP uv_FP)
open AffineValueGramBits (base base_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def coordinateDegree (F : Inputs) (r : List Bool) : ℕ :=
  ProjectiveValueGram.dimension (FlatAffineEndpointRows.arity F r)
    (AffineRingCoordinates.width (FlatAffineEndpointPreparation.degrees F r)) + 1

theorem coordinateDegree_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) :
    BinaryFn (coordinateDegree F) :=
  (FlatAffineEndpointGram.family F height (FlatAffineEndpointRows.zero F)).coordinateDegree_binary
    (FlatAffineEndpointRows.arity_unary h) (FlatAffineEndpointGram.degree_binary h)
    (FlatAffineEndpointGram.width_eq F height (FlatAffineEndpointRows.zero F))

noncomputable def width (F : Inputs) (r : List Bool) : ℕ :=
  (Macaulay.level (ProjectiveValueGram.degrees (fun _ : Fin (FlatAffineEndpointRows.arity F r) => coordinateDegree F r) 1)).size

noncomputable def family (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) : IntegerGridValueGramBits.Family where
  arity := FlatAffineEndpointRows.arity F
  width := width F
  degree r _ := coordinateDegree F r
  testDegree _ := 1
  coordinate := FlatAffineEndpointGrid.coordinate F height
  test r := (FrozenAffineCopies.midpoint (index r)).map Polynomial.C

theorem controls {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) : (family F height index).affine.homogeneous.layout.Controls :=
  (family F height index).affine.homogeneous.uniform_controls (coordinateDegree F)
    (FlatAffineEndpointRows.arity_unary h) (coordinateDegree_binary h height) (BinaryFn.const 1)
    (fun _ _ => rfl) (fun _ => rfl)

theorem coordinate_inner_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (r : List Bool) (i : Fin (FlatAffineEndpointRows.arity F r)) (k : ℕ) :
    ((FlatAffineEndpointGrid.coordinate F height r i).coeff k).natDegree ≤ coordinateDegree F r := by
  have H := Geometry.AffineShiftCoordinates.coordinate_parameter_degree_le
    (FlatAffineEndpointPreparation.system F height r)
    (fun j => if j = FlatAffineEndpointGram.active F height r then Polynomial.X else 0)
    (FlatAffineEndpointPreparation.degrees F r) 1 (fun _ => by split_ifs <;> simp) i k
  simp only [Nat.mul_one] at H
  exact H.trans (Nat.le_succ _)

theorem test_inner_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool)
    (e : Fin (FlatAffineEndpointRows.arity F r) →₀ ℕ) :
    (((family F height index).test r).coeff e).natDegree ≤ coordinateDegree F r := by
  change (Polynomial.C ((FrozenAffineCopies.midpoint (index r)).coeff e)).natDegree ≤ _
  simp only [Polynomial.natDegree_C]
  exact Nat.zero_le _

theorem testEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r)))
    (hi : UnaryFn (fun r => (index r).val)) : SpaceFunction (family F height index).testCoefficient := by
  let G := family F height index
  have hG := controls h height index
  have hn := (FlatAffineEndpointRows.originalCount_unary h).comp base_FP
  have EP := FrozenAffineMidpointBits.evaluator hn (hG.width.comp base_FP)
    (fun q => index (base q)) (hi.comp base_FP) shift_FP (mem_FP_comp ctx_FP pairSnd_mem_FP)
  have hz := (BinaryFn.fromBits (mem_FP_comp uv_FP pairFst_mem_FP)).eq (BinaryFn.const 0)
  have H := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (pairFst (uv q)) = 0)) hz.flag_mem_FP
    EP (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun q => ?_)
  let a : ℤ := (FrozenAffineCopies.midpoint (index (base q))).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FlatAffineEndpointRows.arity F (base q))))
      (width F (base q)) (Nat.fromBitsLE (shift q)))
  change (if decide (Nat.fromBitsLE (pairFst (uv q)) = 0) then
    residueBits (a : ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1)) else []) =
      residueBits (((Polynomial.C a).coeff (Nat.fromBitsLE (pairFst (uv q))) :
        ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1)))
  by_cases hk : Nat.fromBitsLE (pairFst (uv q)) = 0
  · simp only [decide_eq_true_eq, Polynomial.coeff_C, hk, ite_true]
  · simp only [decide_eq_true_eq, Polynomial.coeff_C, hk, ite_false, Int.cast_zero, residueBits, ZMod.val_zero]
    rfl

noncomputable def reader {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (index : (r : List Bool) → Fin (count F (pairFst r)))
    (hi : UnaryFn (fun r => (index r).val)) :
    CertifiedPolynomial.BivariateReader (family F height index).affine.homogeneous.annihilator :=
  (family F height index).reader (controls h height index) (coordinateDegree F) (coordinateDegree_binary h height)
    (coordinate_inner_bound F height) (test_inner_bound F height index)
    (FlatAffineEndpointGrid.coefficientEvaluator h height hh) (testEvaluator h height index hi)

theorem degrees_pos_record (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height u) = 0)
    (i : Fin (FlatAffineEndpointRows.arity F (FlatAffineEndpointPreparation.record F height u))) :
    0 < FlatAffineEndpointPreparation.degrees F (FlatAffineEndpointPreparation.record F height u) i :=
  FrozenAffineCopies.degrees_pos _ _ (FlatAffinePowerPositive.degree_pos F _)
    (FlatAffineEndpointPreparation.degree_pos_of_root F hcone height u a ha) i

theorem coordinate_degree_eq (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height u) = 0)
    (i : Fin (FlatAffineEndpointRows.arity F (FlatAffineEndpointPreparation.record F height u))) :
    (FlatAffineEndpointGrid.coordinate F height (FlatAffineEndpointPreparation.record F height u) i).natDegree =
      coordinateDegree F (FlatAffineEndpointPreparation.record F height u) := by
  let r := FlatAffineEndpointPreparation.record F height u
  let p := FlatAffineEndpointPreparation.system F height r
  let d := FlatAffineEndpointPreparation.degrees F r
  let c := fun j => if j = FlatAffineEndpointGram.active F height r then (Polynomial.X : Polynomial ℤ) else 0
  have hd := degrees_pos_record F hcone height u a ha
  have hp := FlatAffineEndpointPreparation.noInfinity_record F hcone height u a ha
  have H := (AffineRingCoordinates.exact_degree_and_positive_leading
    (SymbolicScaledSquarefree.scalarEvaluation 0) (AffineConstantParameterShift.system p c) d hd
    (AffineConstantParameterShift.noInfinity p c d hd hp _) i).1
  exact H

theorem ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (index : (r : List Bool) → Fin (count F (pairFst r)))
    (u : List Bool) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height u) = 0) :
    (family F height index).affine.homogeneous.annihilator (FlatAffineEndpointPreparation.record F height u) ≠ 0 := by
  apply (family F height index).ne_zero (FlatAffineEndpointPreparation.record F height u)
  · intro i
    exact (coordinate_degree_eq F hcone height u a ha i).symm
  · intro i
    change 0 < (FlatAffineEndpointGrid.coordinate F height (FlatAffineEndpointPreparation.record F height u) i).natDegree
    rw [coordinate_degree_eq F hcone height u a ha i]
    exact Nat.zero_lt_succ _
  · exact Nat.zero_lt_one
  · exact Nat.lt_size_self _

theorem eval_eq_zero (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool)
    {K : Type*} [Field K] (rho : Polynomial ℤ →+* K) (x : Fin (FlatAffineEndpointRows.arity F r) → K)
    (hx : ∀ i, (FlatAffineEndpointGrid.coordinate F height r i).eval₂ rho (x i) = 0) :
    ((family F height index).affine.homogeneous.annihilator r).eval₂ rho
      (2 * x (FrozenAffineCopies.block (0 : Fin 3) (index r)) -
        x (FrozenAffineCopies.block (1 : Fin 3) (index r)) - x (FrozenAffineCopies.block (2 : Fin 3) (index r))) = 0 := by
  have hp (i : Fin (FlatAffineEndpointRows.arity F r)) :
      (FlatAffineEndpointGrid.coordinate F height r i).natDegree ≤ coordinateDegree F r :=
    Geometry.AffineShiftCoordinates.coordinate_degree_le _ _ _ i
  have hq : ((family F height index).test r).totalDegree ≤ 1 :=
    (PolynomialMapDegree.degree_le Polynomial.C (FrozenAffineCopies.midpoint (index r))).trans
      (FrozenAffineCopies.midpoint_degree (index r))
  have H := (family F height index).eval_eq_zero r rho x hp hq (Nat.lt_size_self _) hx
  change ((family F height index).affine.homogeneous.annihilator r).eval₂ rho
    (((FrozenAffineCopies.midpoint (index r)).map Polynomial.C).eval₂ rho x) = 0 at H
  have hv := (MvPolynomial.eval₂_map Polynomial.C x rho (FrozenAffineCopies.midpoint (index r))).trans
    (FrozenAffineCopies.midpoint_eval (rho.comp Polynomial.C) (index r) x)
  exact (congrArg (fun y : K => ((family F height index).affine.homogeneous.annihilator r).eval₂ rho y) hv).symm.trans H

noncomputable def valueDimension (F : Inputs) (r : List Bool) : ℕ :=
  ProjectiveValueGram.dimension (FlatAffineEndpointRows.arity F r) (width F r)

theorem valueDimension_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) : BinaryFn (valueDimension F) :=
  (family F height index).affine.homogeneous.dimension_binary (controls h height index)

theorem degree_le (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool) :
    ((family F height index).affine.homogeneous.annihilator r).natDegree ≤ valueDimension F r + 1 :=
  ProjectiveValueGram.annihilator_degree_le _ _ _ _ _

theorem parameter_degree_le (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool) (k : ℕ) :
    (((family F height index).affine.homogeneous.annihilator r).coeff k).natDegree ≤ valueDimension F r * coordinateDegree F r := by
  let G := family F height index
  exact G.affine.parameter_degree_le (coordinateDegree F)
    (G.original_inner_bound (coordinateDegree F) (coordinate_inner_bound F height) (test_inner_bound F height index)) r k

end LeanCanny.Encoding.FlatAffineEndpointValues
