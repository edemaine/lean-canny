/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.AffineShiftCoordinateSpace
public import LeanCanny.Encoding.FlatAffinePowerGramLayout

/-! # Native varying-height coordinates of the actual affine power tower

One selected row varies by the external parameter. The original signed
records supply the integer power-tower rows. The parameter shift is read
internally, and the existing tower metadata supplies every Gram control.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightGram
open LeanCanny.Algebra LeanCanny.Computation MatrixPower MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open MacaulayFullBoxBits (ctx idx shift uv ctx_FP idx_FP shift_FP uv_FP)
open AffineValueGramBits (base base_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def rawRow (F : Inputs) (u : List Bool) (i : ℕ) : Fin (count F u) :=
  ⟨min i (count F u - 1), by have := FlatAffineFullSourcePositive.count_pos F u; omega⟩

lemma rawRow_val (F : Inputs) (u : List Bool) (i : Fin (count F u)) : rawRow F u i.val = i := by
  apply Fin.ext
  change min i.val (count F u - 1) = i.val
  apply Nat.min_eq_left
  have := i.isLt
  omega

noncomputable def family (F : Inputs) (height coordinate : (u : List Bool) → Fin (count F u)) :
    AffineShiftCoordinateBits.Family where
  arity := count F
  width := FlatAffinePowerControls.width F
  degree u i := FlatAffinePowerPositive.degree F u (rawRow F u i)
  rows := FlatAffinePowerPositive.system F
  shifts u i := if i = height u then Polynomial.X else 0
  coordinate := coordinate

lemma width_eq (F : Inputs) (height coordinate : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    (family F height coordinate).width u = AffineRingCoordinates.width
      (fun i : Fin ((family F height coordinate).arity u) => (family F height coordinate).degree u i.val) := by
  change FlatAffinePowerControls.width F u = AffineFiniteCoordinates.width
    (fun i : Fin (count F u) => FlatAffinePowerPositive.degree F u (rawRow F u i.val))
  rw [FlatAffinePowerGramLayout.width_eq]
  exact congrArg AffineFiniteCoordinates.width (funext (fun i => congrArg (FlatAffinePowerPositive.degree F u) (rawRow_val F u i).symm))

theorem degree_binary {F : Inputs} (h : F.Access) (height coordinate : (u : List Bool) → Fin (count F u)) :
    BinaryFn (fun q => (family F height coordinate).degree (pairFst q) (Nat.fromBitsLE (pairSnd q))) := by
  have hr : UnaryFn (fun q => (rawRow F (pairFst q) (Nat.fromBitsLE (pairSnd q))).val) :=
    UnaryFn.fromBitsLE_min pairSnd_mem_FP (((FlatAffineFullSourcePositive.count_unary h).comp pairFst_mem_FP).sub (UnaryFn.const 1))
  have hd := FlatAffinePowerPositive.degree_unary (FlatAffineFullSourceContext.access h pairFst_mem_FP)
    (fun q => rawRow F (pairFst q) (Nat.fromBitsLE (pairSnd q))) hr
  exact BinaryFn.ofUnary hd

theorem controls {F : Inputs} (h : F.Access) (height coordinate : (u : List Bool) → Fin (count F u)) :
    (family F height coordinate).parameter.affine.homogeneous.layout.Controls :=
  (family F height coordinate).controls (FlatAffineFullSourcePositive.count_unary h)
    (degree_binary h height coordinate) (width_eq F height coordinate)

theorem originalEvaluator {F : Inputs} (h : F.Access) (height coordinate : (u : List Bool) → Fin (count F u)) :
    SpaceFunction (family F height coordinate).integerCoefficient := by
  let G := family F height coordinate
  have hG := controls h height coordinate
  have E := FlatAffinePowerPositive.evaluator (FlatAffineFullSourceContext.access h base_FP)
    G.row (G.row_unary hG) ((FlatAffinePowerControls.width_unary h).comp base_FP)
    shift_FP (mem_FP_comp ctx_FP pairSnd_mem_FP)
  refine E.congr (funext fun q => ?_)
  change residueBits (((FlatAffinePowerPositive.system (FlatAffineFullSourceContext.comp F base) q (G.row q)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (FlatAffinePowerControls.width F (base q))
      (Nat.fromBitsLE (shift q)))) : ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1)) = _
  rw [FlatAffinePowerPositive.system_comp]
  rfl

theorem shiftEvaluator {F : Inputs} (h : F.Access) (height coordinate : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (family F height coordinate).shiftCoefficient := by
  let G := family F height coordinate
  have hrow := BinaryFn.ofUnary (G.row_unary (controls h height coordinate))
  have hh' := BinaryFn.ofUnary (hh.comp base_FP)
  have hk : (fun q => pairFst (uv q)) ∈ FP := mem_FP_comp uv_FP pairFst_mem_FP
  have hm : (fun q => pairSnd (ctx q)) ∈ FP := mem_FP_comp ctx_FP pairSnd_mem_FP
  have hsel := (hrow.eq hh').and ((BinaryFn.fromBits hk).eq (BinaryFn.const 1))
  have E1 := SpaceFunction.ofFP _ (mem_FP_comp (mem_FP_comp hm BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP)
  have E := SpaceFunction.branch (fun q => decide ((G.row q).val = (height (base q)).val ∧
    Nat.fromBitsLE (pairFst (uv q)) = 1)) hsel.flag_mem_FP E1 (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine E.congr (funext fun q => ?_)
  change (if decide ((G.row q).val = (height (base q)).val ∧ Nat.fromBitsLE (pairFst (uv q)) = 1) then
    ArithmeticBits.one (BinaryNat.succ (pairSnd (ctx q))) else []) =
      residueBits (((if G.row q = height (base q) then (Polynomial.X : Polynomial ℤ) else 0).coeff
        (Nat.fromBitsLE (pairFst (uv q)))) : ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1))
  simp only [decide_eq_true_eq]
  by_cases hr : G.row q = height (base q)
  · simp only [hr, ite_true, true_and, Polynomial.coeff_X, eq_comm (a := (1 : ℕ))]
    split_ifs
    · rw [BinaryNat.succ_eq_bits]
      exact ArithmeticBits.one_residueBits _
    · simp [residueBits, BinaryNatCode.encode]
  · have hv : (G.row q).val ≠ (height (base q)).val := fun he => hr (Fin.ext he)
    simp [hr, hv, residueBits, BinaryNatCode.encode]

/-- The actual height-varying tower coordinate reader needs no additional
coefficient oracle beyond the original affine source and signed records. -/
noncomputable def reader {F : Inputs} (h : F.Access)
    (height coordinate : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (hc : UnaryFn (fun u => (coordinate u).val)) :
    CertifiedPolynomial.BivariateReader (fun u => Geometry.AffineShiftCoordinates.coordinate
      (FlatAffinePowerPositive.system F u)
      (fun i => if i = height u then Polynomial.X else 0)
      (fun i => FlatAffinePowerPositive.degree F u i) (coordinate u)) := by
  let G := family F height coordinate
  have E := G.canonicalReader (FlatAffineFullSourcePositive.count_unary h) (degree_binary h height coordinate)
    hc (fun _ => 1) (BinaryFn.const 1) (fun u i => by
      change (if i = height u then (Polynomial.X : Polynomial ℤ) else 0).natDegree ≤ 1
      split_ifs <;> simp) (width_eq F height coordinate) (originalEvaluator h height coordinate)
    (shiftEvaluator h height coordinate hh)
  have he : (fun u => Geometry.AffineShiftCoordinates.coordinate (G.rows u) (G.shifts u)
      (fun i => G.degree u i.val) (G.coordinate u)) =
      (fun u => Geometry.AffineShiftCoordinates.coordinate (FlatAffinePowerPositive.system F u)
        (fun i => if i = height u then Polynomial.X else 0)
        (fun i => FlatAffinePowerPositive.degree F u i) (coordinate u)) := by
    funext u
    apply congrArg (fun d => Geometry.AffineShiftCoordinates.coordinate (FlatAffinePowerPositive.system F u)
      (fun i => if i = height u then Polynomial.X else 0) d (coordinate u))
    funext i
    exact congrArg (FlatAffinePowerPositive.degree F u) (rawRow_val F u i)
  exact he ▸ E

end LeanCanny.Encoding.FlatAffineHeightGram
