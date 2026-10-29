/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerGramLayout
public import LeanCanny.Algebra.AffineBoxGramEncoding

/-! # Native nested Gram source coefficients from affine records -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerGramSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open MacaulayFullBoxBits (ctx idx shift uv)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
attribute [local irreducible] FlatAffinePowerCoordinateRows.system FlatAffinePowerPositive.system FlatAffinePowerPositive.degree

noncomputable def row (F : Inputs) (q : List Bool) : Fin (count F (ctx q) + 1) :=
  ⟨min (Nat.fromBitsLE (idx q)) (count F (ctx q)), by omega⟩

theorem row_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => (row F q).val) := by
  exact (UnaryFn.fromBitsLE_min MacaulayFullBoxBits.idx_FP
    ((FlatAffineFullSourcePositive.count_unary h).comp MacaulayFullBoxBits.ctx_FP)).of_eq (fun _ => rfl)

noncomputable def entry (F : Inputs) (coordinate : (c : List Bool) → Fin (count F c))
    (modulus : List Bool → List Bool) (c : List Bool) (i r u v : ℕ) : List Bool :=
  if u = 0 then
    residueBits (((FlatAffinePowerCoordinateRows.system F coordinate c
      ⟨min i (count F c), by omega⟩).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (FlatAffinePowerControls.width F c) r)).coeff v :
          ZMod (Nat.fromBitsLE (modulus c) + 1))
  else []

noncomputable def value (F : Inputs) (coordinate : (c : List Bool) → Fin (count F c))
    (modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  entry F coordinate modulus (ctx q) (Nat.fromBitsLE (idx q)) (Nat.fromBitsLE (shift q))
    (Nat.fromBitsLE (pairFst (uv q))) (Nat.fromBitsLE (pairSnd (uv q)))

theorem evaluator {F : Inputs} (h : F.Access)
    (coordinate : (u : List Bool) → Fin (count F u)) (hc : UnaryFn (fun u => (coordinate u).val))
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (value F coordinate modulus) := by
  have hf := FlatAffineFullSourceContext.access h MacaulayFullBoxBits.ctx_FP
  have E := FlatAffinePowerCoordinateRows.evaluator hf
    ((FlatAffinePowerControls.width_unary h).comp MacaulayFullBoxBits.ctx_FP)
    (fun q => coordinate (ctx q)) (hc.comp MacaulayFullBoxBits.ctx_FP)
    (row F) (row_unary h) (mem_FP_comp MacaulayFullBoxBits.uv_FP pairSnd_mem_FP)
    (mem_FP_comp MacaulayFullBoxBits.ctx_FP hm)
  have ER := E.precompose (fun q => pair q (shift q))
    (mem_FP_pair id_mem_FP MacaulayFullBoxBits.shift_FP)
  have hz := BinaryNat.eq_const_fppred (mem_FP_comp MacaulayFullBoxBits.uv_FP pairFst_mem_FP) 0
  refine (SpaceFunction.branch _ hz.flag_mem_FP ER
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, value, entry, Function.comp_apply, FlatAffinePowerCoordinateRows.value_pair]
  congr 1
  exact congrArg (fun p => residueBits (((p (row F q)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (FlatAffinePowerControls.width F (ctx q))
      (Nat.fromBitsLE (shift q)))).coeff (Nat.fromBitsLE (pairSnd (uv q))) :
        ZMod (Nat.fromBitsLE (modulus (ctx q)) + 1)))
    (FlatAffinePowerCoordinateRows.system_comp F ctx coordinate q)

lemma row_packet (F : Inputs) (c : List Bool) (i : Fin (count F c + 1)) (r u v : ℕ) :
    (row F (MacaulayFullBoxBits.entryPacket c i.val r u v)).val = i.val := by
  simp only [row, MacaulayFullBoxBits.idx_entryPacket, MacaulayFullBoxBits.ctx_entryPacket,
    MacaulayBits.fromBits_encode]
  exact Nat.min_eq_left (by have := i.isLt; omega)

lemma value_packet (F : Inputs) (coordinate : (c : List Bool) → Fin (count F c))
    (modulus : List Bool → List Bool) (c : List Bool) (i : Fin (count F c + 1)) (r u v : ℕ) :
    value F coordinate modulus (MacaulayFullBoxBits.entryPacket c i.val r u v) =
      MacaulayFullBoxBits.scalar modulus c u v
        ((AffineBoxGramEliminant.liftedSystem
          (AffineFiniteCoordinates.homogeneousRows (FlatAffinePowerPositive.system F c)
            (FlatAffinePowerPositive.degree F c)) (coordinate c).succ i).coeff
              (RationalSubstitution.Indexed.exponentVector (count F c + 1)
                (FixedWidthPolynomial.entry (FlatAffinePowerControls.width F c) r))) := by
  simp only [value, MacaulayFullBoxBits.ctx_entryPacket, MacaulayFullBoxBits.idx_entryPacket, MacaulayFullBoxBits.shift_entryPacket,
    MacaulayFullBoxBits.uv_entryPacket, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode,
    MacaulayFullBoxBits.scalar,
    AffineBoxGramEliminant.liftedSystem, MvPolynomial.coeff_map, AffineBoxGramEliminant.lift_coefficient]
  unfold entry
  have hi : min i.val (count F c) = i.val := Nat.min_eq_left (by have := i.isLt; omega)
  simp only [hi, FixedWidthPolynomial.nativeExponent_refl]
  change (if u = 0 then _ else []) = _
  unfold FlatAffinePowerCoordinateRows.system
  split_ifs <;> simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode]
  rfl

end LeanCanny.Encoding.FlatAffinePowerGramSource
