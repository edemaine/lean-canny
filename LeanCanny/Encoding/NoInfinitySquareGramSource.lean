/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.NoInfinitySquareRows
public import LeanCanny.Algebra.AffineBoxGramEncoding

/-! # Native nested Gram source coefficients from affine records -/

@[expose] public section
namespace LeanCanny.Encoding.NoInfinitySquareGramSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open NoInfinitySquareSample (Family)
open MacaulayFullBoxBits (ctx idx shift uv)
open scoped Classical

noncomputable def row (F : Family) (q : List Bool) : Fin (F.count (ctx q) + 1) :=
  ⟨min (Nat.fromBitsLE (idx q)) (F.count (ctx q)), by omega⟩

theorem row_unary {F : Family} (h : NoInfinitySquareSample.Access F) : UnaryFn (fun q => (row F q).val) := by
  exact (UnaryFn.fromBitsLE_min MacaulayFullBoxBits.idx_FP
    ((h.count).comp MacaulayFullBoxBits.ctx_FP)).of_eq (fun _ => rfl)

noncomputable def entry (F : Family) (coordinate : (c : List Bool) → Fin (F.count c))
    (modulus : List Bool → List Bool) (c : List Bool) (i r u v : ℕ) : List Bool :=
  if u = 0 then
    residueBits (((NoInfinitySquareSample.coordinateSystem F coordinate c
      ⟨min i (F.count c), by omega⟩).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (NoInfinitySquareSample.width F c) r)).coeff v :
          ZMod (Nat.fromBitsLE (modulus c) + 1))
  else []

noncomputable def value (F : Family) (coordinate : (c : List Bool) → Fin (F.count c))
    (modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  entry F coordinate modulus (ctx q) (Nat.fromBitsLE (idx q)) (Nat.fromBitsLE (shift q))
    (Nat.fromBitsLE (pairFst (uv q))) (Nat.fromBitsLE (pairSnd (uv q)))

theorem evaluator {F : Family} (h : NoInfinitySquareSample.Access F)
    (coordinate : (u : List Bool) → Fin (F.count u)) (hc : UnaryFn (fun u => (coordinate u).val))
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (value F coordinate modulus) := by
  have hf := NoInfinitySquareSample.access_comp h MacaulayFullBoxBits.ctx_FP
  have E := NoInfinitySquareSample.coordinate_evaluator hf
    ((NoInfinitySquareSample.width_unary h).comp MacaulayFullBoxBits.ctx_FP)
    (fun q => coordinate (ctx q)) (hc.comp MacaulayFullBoxBits.ctx_FP)
    (row F) (row_unary h) (mem_FP_comp MacaulayFullBoxBits.uv_FP pairSnd_mem_FP)
    (mem_FP_comp MacaulayFullBoxBits.ctx_FP hm)
  have ER := E.precompose (fun q => pair q (shift q))
    (mem_FP_pair id_mem_FP MacaulayFullBoxBits.shift_FP)
  have hz := BinaryNat.eq_const_fppred (mem_FP_comp MacaulayFullBoxBits.uv_FP pairFst_mem_FP) 0
  refine (SpaceFunction.branch _ hz.flag_mem_FP ER
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (funext fun q => ?_)
  simp only [decide_eq_true_eq,value,entry,Function.comp_apply]
  split_ifs
  · exact NoInfinitySquareSample.coordinateValue_pair (NoInfinitySquareSample.comp F ctx)
      (fun z=>NoInfinitySquareSample.width F (ctx z)) (fun q=>coordinate (ctx q)) (row F)
      (pairSnd ∘ uv) (modulus ∘ ctx) q (shift q)
  · rfl

lemma row_packet (F : Family) (c : List Bool) (i : Fin (F.count c + 1)) (r u v : ℕ) :
    (row F (MacaulayFullBoxBits.entryPacket c i.val r u v)).val = i.val := by
  simp only [row, MacaulayFullBoxBits.idx_entryPacket, MacaulayFullBoxBits.ctx_entryPacket,
    MacaulayBits.fromBits_encode]
  exact Nat.min_eq_left (by have := i.isLt; omega)

lemma value_packet (F : Family) (coordinate : (c : List Bool) → Fin (F.count c))
    (modulus : List Bool → List Bool) (c : List Bool) (i : Fin (F.count c + 1)) (r u v : ℕ) :
    value F coordinate modulus (MacaulayFullBoxBits.entryPacket c i.val r u v) =
      MacaulayFullBoxBits.scalar modulus c u v
        ((AffineBoxGramEliminant.liftedSystem
          (AffineFiniteCoordinates.homogeneousRows (F.rows c)
            ((fun i=>F.rowDegree c i.val))) (coordinate c).succ i).coeff
              (RationalSubstitution.Indexed.exponentVector (F.count c + 1)
                (FixedWidthPolynomial.entry (NoInfinitySquareSample.width F c) r))) := by
  simp only [value, MacaulayFullBoxBits.ctx_entryPacket, MacaulayFullBoxBits.idx_entryPacket, MacaulayFullBoxBits.shift_entryPacket,
    MacaulayFullBoxBits.uv_entryPacket, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode,
    MacaulayFullBoxBits.scalar,
    AffineBoxGramEliminant.liftedSystem, MvPolynomial.coeff_map, AffineBoxGramEliminant.lift_coefficient]
  unfold entry
  have hi : min i.val (F.count c) = i.val := Nat.min_eq_left (by have := i.isLt; omega)
  simp only [hi, FixedWidthPolynomial.nativeExponent_refl]
  change (if u = 0 then _ else []) = _
  unfold NoInfinitySquareSample.coordinateSystem
  split_ifs <;> simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode]
  rfl

end LeanCanny.Encoding.NoInfinitySquareGramSource
