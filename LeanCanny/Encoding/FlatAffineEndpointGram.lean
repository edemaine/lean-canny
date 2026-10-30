/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointCoefficient

/-! # Canonical native Gram controls for the frozen endpoint system

The retained degree is read from the charged preparation record. All other
row degrees come from the original source. Canonical levels and widths are
derived from those binary degrees.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointGram
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def indexRow (F : Inputs) (q : List Bool) : Fin (FlatAffineEndpointRows.arity F (pairFst q)) :=
  FlatAffineEndpointCoefficient.rowAt F (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem indexRow_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => (indexRow F q).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP
    (((FlatAffineEndpointRows.arity_unary h).comp pairFst_mem_FP).sub (UnaryFn.const 1))

noncomputable def degree (F : Inputs) (r : List Bool) (i : ℕ) : ℕ :=
  FlatAffineEndpointPreparation.degrees F r (FlatAffineEndpointCoefficient.rowAt F r i)

theorem degree_binary {F : Inputs} (h : F.Access) :
    BinaryFn (fun q => degree F (pairFst q) (Nat.fromBitsLE (pairSnd q))) := by
  let G := FlatAffineFullSourceContext.comp F pairFst
  have hG := FlatAffineFullSourceContext.access h pairFst_mem_FP
  have hi := FlatAffineEndpointRows.localRow_unary hG (indexRow F) (indexRow_unary h)
  have hb := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hd := FlatAffinePowerPositive.degree_unary (FlatAffineFullSourceContext.access h hb)
    (FlatAffineEndpointRows.localRow G (indexRow F)) hi
  have he := FlatAffineEndpointPreparation.degree_binary.comp pairFst_mem_FP
  have hz := (BinaryFn.ofUnary (indexRow_unary h)).eq (BinaryFn.const 0)
  apply (BinaryFn.ite hz he (BinaryFn.ofUnary hd)).of_eq
  intro q
  exact (FlatAffineEndpointRows.selected_degree G (indexRow F) q
    (FlatAffineEndpointPreparation.degree (pairFst q))).symm

noncomputable def family (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (coordinate : (r : List Bool) → Fin (FlatAffineEndpointRows.arity F r)) : AffineShiftCoordinateBits.Family where
  arity := FlatAffineEndpointRows.arity F
  width r := AffineRingCoordinates.width (FlatAffineEndpointPreparation.degrees F r)
  degree := degree F
  rows := FlatAffineEndpointPreparation.system F height
  shifts r i := if i = FrozenAffineCopies.block (0 : Fin 3) (height (pairFst r)) then Polynomial.X else 0
  coordinate := coordinate

theorem width_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (coordinate : (r : List Bool) → Fin (FlatAffineEndpointRows.arity F r)) (r : List Bool) :
    (family F height coordinate).width r = AffineRingCoordinates.width
      (fun i : Fin (FlatAffineEndpointRows.arity F r) => (family F height coordinate).degree r i.val) := by
  change AffineRingCoordinates.width (FlatAffineEndpointPreparation.degrees F r) =
    AffineRingCoordinates.width (fun i => FlatAffineEndpointPreparation.degrees F r
      (FlatAffineEndpointCoefficient.rowAt F r i.val))
  exact congrArg AffineRingCoordinates.width (funext (fun i =>
    congrArg (FlatAffineEndpointPreparation.degrees F r) (FlatAffineEndpointCoefficient.rowAt_val F r i).symm))

theorem controls {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (coordinate : (r : List Bool) → Fin (FlatAffineEndpointRows.arity F r)) :
    (family F height coordinate).parameter.affine.homogeneous.layout.Controls :=
  (family F height coordinate).controls (FlatAffineEndpointRows.arity_unary h) (degree_binary h) (width_eq F height coordinate)

theorem originalEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (coordinate : (r : List Bool) → Fin (FlatAffineEndpointRows.arity F r))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (family F height coordinate).integerCoefficient := by
  let G := family F height coordinate
  have hG := controls h height coordinate
  exact FlatAffineEndpointCoefficient.rowEvaluator h height hh AffineValueGramBits.base AffineValueGramBits.base_FP
    G.row (G.row_unary hG) (hG.width.comp AffineValueGramBits.base_FP)
    MacaulayFullBoxBits.shift_FP (mem_FP_comp MacaulayFullBoxBits.ctx_FP pairSnd_mem_FP)

noncomputable def active (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) :
    Fin (FlatAffineEndpointRows.arity F r) := FrozenAffineCopies.block (0 : Fin 3) (height (pairFst r))

theorem active_unary {F : Inputs} (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : UnaryFn (fun r => (active F height r).val) := by
  apply ((hh.comp pairFst_mem_FP).add (UnaryFn.const 1)).of_eq
  intro r
  change (height (pairFst r)).val + 1 = (height (pairFst r)).val + count F (pairFst r) * 0 + 1
  simp only [Nat.mul_zero, Nat.add_zero]

theorem shiftEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (coordinate : (r : List Bool) → Fin (FlatAffineEndpointRows.arity F r))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (family F height coordinate).shiftCoefficient := by
  let G := family F height coordinate
  have hrow := BinaryFn.ofUnary (G.row_unary (controls h height coordinate))
  have ha := BinaryFn.ofUnary ((active_unary height hh).comp AffineValueGramBits.base_FP)
  have hk : (fun q => pairFst (MacaulayFullBoxBits.uv q)) ∈ FP := mem_FP_comp MacaulayFullBoxBits.uv_FP pairFst_mem_FP
  have hm : (fun q => pairSnd (MacaulayFullBoxBits.ctx q)) ∈ FP := mem_FP_comp MacaulayFullBoxBits.ctx_FP pairSnd_mem_FP
  have hsel := (hrow.eq ha).and ((BinaryFn.fromBits hk).eq (BinaryFn.const 1))
  have E1 := SpaceFunction.ofFP _ (mem_FP_comp (mem_FP_comp hm BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP)
  have E := SpaceFunction.branch (fun q => decide ((G.row q).val = (active F height (AffineValueGramBits.base q)).val ∧
    Nat.fromBitsLE (pairFst (MacaulayFullBoxBits.uv q)) = 1)) hsel.flag_mem_FP E1 (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine E.congr (funext fun q => ?_)
  change (if decide ((G.row q).val = (active F height (AffineValueGramBits.base q)).val ∧
    Nat.fromBitsLE (pairFst (MacaulayFullBoxBits.uv q)) = 1) then
    ArithmeticBits.one (BinaryNat.succ (pairSnd (MacaulayFullBoxBits.ctx q))) else []) =
      residueBits (((if G.row q = active F height (AffineValueGramBits.base q) then (Polynomial.X : Polynomial ℤ) else 0).coeff
        (Nat.fromBitsLE (pairFst (MacaulayFullBoxBits.uv q)))) : ZMod (Nat.fromBitsLE (pairSnd (MacaulayFullBoxBits.ctx q)) + 1))
  simp only [decide_eq_true_eq]
  by_cases hr : G.row q = active F height (AffineValueGramBits.base q)
  · simp only [hr, ite_true, true_and, Polynomial.coeff_X, eq_comm (a := (1 : ℕ))]
    split_ifs
    · rw [BinaryNat.succ_eq_bits]
      exact ArithmeticBits.one_residueBits _
    · simp [residueBits, BinaryNatCode.encode]
  · have hv : (G.row q).val ≠ (active F height (AffineValueGramBits.base q)).val := fun he => hr (Fin.ext he)
    simp [hr, hv, residueBits, BinaryNatCode.encode]

noncomputable def reader {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (coordinate : (r : List Bool) → Fin (FlatAffineEndpointRows.arity F r))
    (hh : UnaryFn (fun u => (height u).val)) (hc : UnaryFn (fun r => (coordinate r).val)) :
    CertifiedPolynomial.BivariateReader (fun r => Geometry.AffineShiftCoordinates.coordinate
      (FlatAffineEndpointPreparation.system F height r)
      (fun i => if i = active F height r then Polynomial.X else 0)
      (FlatAffineEndpointPreparation.degrees F r) (coordinate r)) := by
  let G := family F height coordinate
  have E := G.canonicalReader (FlatAffineEndpointRows.arity_unary h) (degree_binary h) hc
    (fun _ => 1) (BinaryFn.const 1) (fun r i => by
      change (if i = active F height r then (Polynomial.X : Polynomial ℤ) else 0).natDegree ≤ 1
      split_ifs <;> simp) (width_eq F height coordinate)
    (originalEvaluator h height coordinate hh) (shiftEvaluator h height coordinate hh)
  have hd (r : List Bool) : (fun i : Fin (FlatAffineEndpointRows.arity F r) => G.degree r i.val) =
      FlatAffineEndpointPreparation.degrees F r := by
    funext i
    exact congrArg (FlatAffineEndpointPreparation.degrees F r) (FlatAffineEndpointCoefficient.rowAt_val F r i)
  have he : (fun r => Geometry.AffineShiftCoordinates.coordinate (G.rows r) (G.shifts r)
      (fun i => G.degree r i.val) (G.coordinate r)) =
      (fun r => Geometry.AffineShiftCoordinates.coordinate (FlatAffineEndpointPreparation.system F height r)
        (fun i => if i = active F height r then Polynomial.X else 0)
        (FlatAffineEndpointPreparation.degrees F r) (coordinate r)) := by
    funext r
    exact congrArg (fun d : Fin (FlatAffineEndpointRows.arity F r) → ℕ =>
      Geometry.AffineShiftCoordinates.coordinate (FlatAffineEndpointPreparation.system F height r)
        (fun i : Fin (FlatAffineEndpointRows.arity F r) => if i = active F height r then Polynomial.X else 0)
        d (coordinate r)) (hd r)
  exact he ▸ E

end LeanCanny.Encoding.FlatAffineEndpointGram
