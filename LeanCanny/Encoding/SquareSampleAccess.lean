/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleInput

/-! # Native canonical coefficient queries and source-context changes -/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleInput
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem indexWord_FP : indexWord ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem widthWord_FP : widthWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rankWord_FP : rankWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem modulusWord_FP : modulusWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

theorem query_FP {u i w r m : List Bool → List Bool} (hu : u ∈ FP) (hi : i ∈ FP) (hw : w ∈ FP)
    (hr : r ∈ FP) (hm : m ∈ FP) : (fun c => query (u c) (i c) (w c) (r c) (m c)) ∈ FP :=
  mem_FP_pair (mem_FP_pair hu hi) (mem_FP_pair hw (mem_FP_pair hr hm))

theorem selected_encode (F : Inputs) (u : List Bool) (i : Fin (F.count u)) :
    selected F u (BinaryNatCode.encode i.val) = i := by
  apply Fin.ext
  change min (Nat.fromBitsLE (BinaryNatCode.encode i.val)) (F.count u - 1) = i.val
  rw [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.min_eq_left (by have := i.isLt; omega)]

theorem row_packet (F : Inputs) (u : List Bool) (i : Fin (F.count u)) (w r m : List Bool) :
    rowCoefficient F (query u (BinaryNatCode.encode i.val) w r m) = MatrixPower.residueBits
      (((F.system u i).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (F.count u)))
        w.length (Nat.fromBitsLE r)) : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  simp only [rowCoefficient, source, indexWord, widthWord, rankWord, modulusWord, query, pairFst_pair, pairSnd_pair]
  unfold rowValue
  rw [selected_encode]

theorem ann_packet (F : Inputs) (u : List Bool) (i : Fin (F.count u)) (w r m : List Bool) :
    annCoefficient F (query u (BinaryNatCode.encode i.val) w r m) = MatrixPower.residueBits
      (((F.annihilator u i).coeff (Nat.fromBitsLE r) : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  simp only [annCoefficient, source, indexWord, rankWord, modulusWord, query, pairFst_pair, pairSnd_pair]
  unfold annValue
  rw [selected_encode]

def mapSource (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  query (f (source q)) (indexWord q) (widthWord q) (rankWord q) (modulusWord q)

theorem mapSource_FP {f : List Bool → List Bool} (hf : f ∈ FP) : mapSource f ∈ FP :=
  query_FP (mem_FP_comp source_FP hf) indexWord_FP widthWord_FP rankWord_FP modulusWord_FP

theorem row_comp (F : Inputs) (f : List Bool → List Bool) (q : List Bool) :
    rowCoefficient (comp F f) q = rowCoefficient F (mapSource f q) := by
  simp only [rowCoefficient, mapSource, source, indexWord, widthWord, rankWord, modulusWord, query,
    pairFst_pair, pairSnd_pair]
  rfl

theorem ann_comp (F : Inputs) (f : List Bool → List Bool) (q : List Bool) :
    annCoefficient (comp F f) q = annCoefficient F (mapSource f q) := by
  simp only [annCoefficient, mapSource, source, indexWord, rankWord, modulusWord, query, pairFst_pair, pairSnd_pair]
  rfl

theorem access_comp {F : Inputs} (h : F.Access) {f : List Bool → List Bool} (hf : f ∈ FP) : (comp F f).Access :=
  ⟨h.count.comp hf, h.degree.comp hf, h.mass.comp hf, h.annDegree.comp hf, h.annHeight.comp hf,
    (h.row.precompose _ (mapSource_FP hf)).congr (funext fun q => (row_comp F f q).symm),
    (h.annihilator.precompose _ (mapSource_FP hf)).congr (funext fun q => (ann_comp F f q).symm)⟩

theorem row_evaluator {F : Inputs} (h : F.Access) {f : List Bool → List Bool} (hf : f ∈ FP)
    {W : List Bool → ℕ} (hW : UnaryFn W) (row : (c : List Bool) → Fin (F.count (f c)))
    (hr : UnaryFn (fun c => (row c).val)) {target modulus : List Bool → List Bool}
    (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (fun c => MatrixPower.residueBits (((F.system (f c) (row c)).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (F.count (f c)))) (W c) (Nat.fromBitsLE (target c))) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1))) := by
  have H := h.row.precompose (fun c => query (f c) (BinaryNatCode.encode (row c).val)
    (List.replicate (W c) false) (target c) (modulus c))
      (query_FP hf (BinaryFn.ofUnary hr).bits_mem_FP (hW.replicate_mem_FP false) ht hm)
  exact H.congr (funext fun c => by
    rw [Function.comp_apply, row_packet, List.length_replicate])

theorem ann_evaluator {F : Inputs} (h : F.Access) {f : List Bool → List Bool} (hf : f ∈ FP)
    (coordinate : (c : List Bool) → Fin (F.count (f c))) (hc : UnaryFn (fun c => (coordinate c).val))
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (fun c => MatrixPower.residueBits (((F.annihilator (f c) (coordinate c)).coeff
      (Nat.fromBitsLE (target c)) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))) := by
  have H := h.annihilator.precompose (fun c => query (f c) (BinaryNatCode.encode (coordinate c).val) []
    (target c) (modulus c)) (query_FP hf (BinaryFn.ofUnary hc).bits_mem_FP (constFn_mem_FP []) ht hm)
  exact H.congr (funext fun c => by rw [Function.comp_apply, ann_packet])

end LeanCanny.Encoding.SquareSampleInput
