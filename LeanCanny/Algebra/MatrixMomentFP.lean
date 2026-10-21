/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixMomentPower
public import LeanCanny.Algebra.MatrixPowerHalting
public import LeanCanny.Algebra.ModularNegFP

/-!
# Certified binary entry access for the scalar-moment child

Augmented matrix access selects a row value, column value, original matrix
entry, or zero. Binary predecessor converts interior indices back to the
original coordinates. The dimension and sink index use binary successor.
FP input access therefore gives an FP controller for the complete moment
child; the whole moment computation is not assumed to be FP.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixMoment.EntryBits

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open MatrixPower
open Matrix

structure Access where
  dimension : List Bool → List Bool
  row : List Bool → List Bool
  column : List Bool → List Bool
  entry : List Bool → List Bool

structure Access.PolyTime (a : Access) : Prop where
  dimension : a.dimension ∈ FP
  row : a.row ∈ FP
  column : a.column ∈ FP
  entry : a.entry ∈ FP

def rowIndex (p : List Bool) : List Bool := pairFst (pairSnd p)
def colIndex (p : List Bool) : List Bool := pairSnd (pairSnd p)
def sinkIndex (a : Access) (c : List Bool) : List Bool := BinaryNat.succ (a.dimension c)
def dimension (a : Access) (c : List Bool) : List Bool := BinaryNat.succ (sinkIndex a c)

def entry (a : Access) (p : List Bool) : List Bool :=
  let c := pairFst p
  let i := rowIndex p
  let j := colIndex p
  let last := sinkIndex a c
  if i = [] then
    if j = [] then [] else if j = last then [] else a.row (pair c (BinaryNat.pred j))
  else if i = last then []
  else if j = [] then []
  else if j = last then a.column (pair c (BinaryNat.pred i))
  else a.entry (pair c (pair (BinaryNat.pred i) (BinaryNat.pred j)))

theorem rowIndex_mem_FP : rowIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem colIndex_mem_FP : colIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

theorem sinkIndex_mem_FP (a : Access) (ha : a.PolyTime) : sinkIndex a ∈ FP :=
  mem_FP_comp ha.dimension BinaryNat.succ_mem_FP

theorem dimension_mem_FP (a : Access) (ha : a.PolyTime) : dimension a ∈ FP :=
  mem_FP_comp (sinkIndex_mem_FP a ha) BinaryNat.succ_mem_FP

theorem entry_mem_FP (a : Access) (ha : a.PolyTime) : entry a ∈ FP := by
  have hi := rowIndex_mem_FP
  have hj := colIndex_mem_FP
  have hl := mem_FP_comp pairFst_mem_FP (sinkIndex_mem_FP a ha)
  have hip := mem_FP_comp hi BinaryNat.pred_mem_FP
  have hjp := mem_FP_comp hj BinaryNat.pred_mem_FP
  have hr := mem_FP_comp (mem_FP_pair pairFst_mem_FP hjp) ha.row
  have hc := mem_FP_comp (mem_FP_pair pairFst_mem_FP hip) ha.column
  have he := mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_pair hip hjp)) ha.entry
  have hz := constFn_mem_FP ([] : List Bool)
  have hrow := (stringEq_fppred hj hz).ite_mem_FP hz ((stringEq_fppred hj hl).ite_mem_FP hz hr)
  have hbody := (stringEq_fppred hi hl).ite_mem_FP hz
    ((stringEq_fppred hj hz).ite_mem_FP hz ((stringEq_fppred hj hl).ite_mem_FP hc he))
  have h := (stringEq_fppred hi hz).ite_mem_FP hrow hbody
  exact mem_FP_of_eq h (fun _ => rfl)

@[simp] theorem succ_code (b : ℕ) : BinaryNat.succ (BinaryNatCode.encode b) =
    BinaryNatCode.encode (b + 1) := by
  simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem entry_vertex (a : Access) (c : List Bool) (m n : ℕ) [NeZero m]
    (r v : Fin n → ZMod m) (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hd : a.dimension c = BinaryNatCode.encode n)
    (hr : ∀ j, a.row (pair c (BinaryNatCode.encode j.val)) = residueBits (r j))
    (hv : ∀ i, a.column (pair c (BinaryNatCode.encode i.val)) = residueBits (v i))
    (he : ∀ i j, a.entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (A i j)) (p q : Unit ⊕ (Fin n ⊕ Unit)) :
    entry a (pair c (pair (BinaryNatCode.encode (vertexEquiv n p).val)
      (BinaryNatCode.encode (vertexEquiv n q).val))) = residueBits (matrix r v A p q) := by
  have hunit (x : Unit) : x = () := Subsingleton.elim _ _
  have hlast (i : Fin n) : BinaryNatCode.encode (i.val + 1) ≠ BinaryNatCode.encode (n + 1) := by
    intro h
    have hval := BinaryNatCode.encode_injective h
    have := i.isLt
    omega
  rcases p with ⟨⟩ | (i | ⟨⟩) <;> rcases q with ⟨⟩ | (j | ⟨⟩) <;>
    simp [entry, rowIndex, colIndex, sinkIndex, hd, hunit, hlast, Controller.pred_code, hr, hv, he,
      matrix, sourceRow, withSink] <;> simp [residueBits, BinaryNatCode.encode]

theorem entry_correct (a : Access) (c : List Bool) (m n : ℕ) [NeZero m]
    (r v : Fin n → ZMod m) (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hd : a.dimension c = BinaryNatCode.encode n)
    (hr : ∀ j, a.row (pair c (BinaryNatCode.encode j.val)) = residueBits (r j))
    (hv : ∀ i, a.column (pair c (BinaryNatCode.encode i.val)) = residueBits (v i))
    (he : ∀ i j, a.entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (A i j)) (i j : Fin (n + 2)) :
    entry a (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (matrixFin r v A i j) := by
  obtain ⟨p, rfl⟩ := (vertexEquiv n).surjective i
  obtain ⟨q, rfl⟩ := (vertexEquiv n).surjective j
  rw [matrixFin_apply_vertex]
  exact entry_vertex a c m n r v A hd hr hv he p q

def callbacks (a : Access) (modulus : List Bool → List Bool) : Controller.Callbacks :=
  Controller.modularCallbacks (dimension a) modulus (entry a)

theorem callbacks_polyTime (a : Access) (ha : a.PolyTime)
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    (callbacks a modulus).PolyTime :=
  Controller.modularCallbacks_polyTime (dimension_mem_FP a ha) hm (entry_mem_FP a ha)

theorem callbacks_correctAt (a : Access) (modulus : List Bool → List Bool)
    (c : List Bool) (m n : ℕ) [NeZero m] (r v : Fin n → ZMod m)
    (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hd : a.dimension c = BinaryNatCode.encode n) (hm : modulus c = BinaryNatCode.encode m)
    (hr : ∀ j, a.row (pair c (BinaryNatCode.encode j.val)) = residueBits (r j))
    (hv : ∀ i, a.column (pair c (BinaryNatCode.encode i.val)) = residueBits (v i))
    (he : ∀ i j, a.entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (A i j)) :
    Controller.CorrectAt (callbacks a modulus) c (matrixFin r v A) residueBits := by
  apply Controller.modularCallbacks_correctAt
  · simp [dimension, sinkIndex, hd, Nat.add_assoc]
  · exact hm
  · exact entry_correct a c m n r v A hd hr hv he

def start (a : Access) (exponent : List Bool → List Bool) : List Bool → List Bool :=
  Controller.initialPacket (fun c => BinaryNat.succ (BinaryNat.succ (exponent c)))
    (fun _ => []) (sinkIndex a)

theorem start_mem_FP (a : Access) (ha : a.PolyTime)
    {exponent : List Bool → List Bool} (he : exponent ∈ FP) : start a exponent ∈ FP := by
  have hk := mem_FP_comp (mem_FP_comp he BinaryNat.succ_mem_FP) BinaryNat.succ_mem_FP
  exact Controller.initialPacket_mem_FP hk (constFn_mem_FP []) (sinkIndex_mem_FP a ha)

theorem start_encode (a : Access) (exponent : List Bool → List Bool)
    (c : List Bool) (m n k : ℕ)
    (hd : a.dimension c = BinaryNatCode.encode n) (hk : exponent c = BinaryNatCode.encode k) :
    start a exponent c = pair c (stateBits (residueBits (m := m))
      (.eval ⟨(k + 2).size, k + 2, 0, Fin.last (n + 1)⟩ [])) := by
  apply Controller.initialPacket_encode
  · simp [hk, Nat.add_assoc]
  · rfl
  · simp [sinkIndex, hd]

def result (packet : List Bool) : List Bool := (pairSnd packet).drop 1

theorem result_mem_FP : result ∈ FP := drop_mem_FP pairSnd_mem_FP (UnaryFn.const 1)

def negativeResult (modulus : List Bool → List Bool) (packet : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (modulus (pairFst packet)) (result packet))

theorem negativeResult_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    negativeResult modulus ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hm) result_mem_FP)
    ArithmeticBits.negate_mem_FP
  refine mem_FP_of_eq (g := negativeResult modulus) h ?_
  intro packet
  simp only [Function.comp_apply, negativeResult]

theorem negativeResult_done (modulus : List Bool → List Bool) (c : List Bool) (m n : ℕ)
    [NeZero m] (x : ZMod m) (hm : modulus c = BinaryNatCode.encode m) :
    negativeResult modulus (pair c (stateBits (n := n + 2) residueBits (.done x))) =
      residueBits (-x) := by
  simp only [negativeResult, result, pairFst_pair, pairSnd_pair, stateBits,
    List.drop_succ_cons, List.drop_zero, hm]
  exact ArithmeticBits.negate_residueBits m x

theorem run (a : Access) (modulus exponent : List Bool → List Bool)
    (c : List Bool) (m n k : ℕ) [NeZero m] (r v : Fin n → ZMod m)
    (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hc : Controller.CorrectAt (callbacks a modulus) c (matrixFin r v A) residueBits)
    (hd : a.dimension c = BinaryNatCode.encode n) (hk : exponent c = BinaryNatCode.encode k) :
    (Controller.step (callbacks a modulus))^[MatrixPower.work (n + 2) (k + 2).size (k + 2) + 1]
      (start a exponent c) = pair c (stateBits (n := n + 2) residueBits (.done (r ⬝ᵥ (A ^ k *ᵥ v)))) := by
  rw [start_encode a exponent c m n k hd hk, Controller.run_pow _ c _ residueBits hc,
    matrixFin_pow_moment]

theorem run_result (a : Access) (modulus exponent : List Bool → List Bool)
    (c : List Bool) (m n k : ℕ) [NeZero m] (r v : Fin n → ZMod m)
    (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hc : Controller.CorrectAt (callbacks a modulus) c (matrixFin r v A) residueBits)
    (hd : a.dimension c = BinaryNatCode.encode n) (hk : exponent c = BinaryNatCode.encode k) :
    result ((Controller.step (callbacks a modulus))^[
      MatrixPower.work (n + 2) (k + 2).size (k + 2) + 1] (start a exponent c)) =
        residueBits (r ⬝ᵥ (A ^ k *ᵥ v)) := by
  rw [run a modulus exponent c m n k r v A hc hd hk]
  simp [result, stateBits]

theorem halted_before (a : Access) (modulus exponent : List Bool → List Bool)
    (c : List Bool) (m n k : ℕ) [NeZero m] (r v : Fin n → ZMod m)
    (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hc : Controller.CorrectAt (callbacks a modulus) c (matrixFin r v A) residueBits)
    (hd : a.dimension c = BinaryNatCode.encode n) (hk : exponent c = BinaryNatCode.encode k)
    (t : ℕ) (ht : t < MatrixPower.work (n + 2) (k + 2).size (k + 2) + 1) :
    Controller.halted ((Controller.step (callbacks a modulus))^[t] (start a exponent c)) = false := by
  rw [start_encode a exponent c m n k hd hk]
  exact Controller.halted_before _ c (matrixFin r v A) residueBits hc (k + 2) t _ _ ht

theorem halted_after (a : Access) (modulus exponent : List Bool → List Bool)
    (c : List Bool) (m n k : ℕ) [NeZero m] (r v : Fin n → ZMod m)
    (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hc : Controller.CorrectAt (callbacks a modulus) c (matrixFin r v A) residueBits)
    (hd : a.dimension c = BinaryNatCode.encode n) (hk : exponent c = BinaryNatCode.encode k) :
    Controller.halted ((Controller.step (callbacks a modulus))^[
      MatrixPower.work (n + 2) (k + 2).size (k + 2) + 1] (start a exponent c)) = true := by
  rw [run a modulus exponent c m n k r v A hc hd hk]
  simp [Controller.halted, stateBits]

theorem run_length (a : Access) (modulus exponent : List Bool → List Bool)
    (c : List Bool) (m n k : ℕ) [NeZero m] (r v : Fin n → ZMod m)
    (A : Matrix (Fin n) (Fin n) (ZMod m))
    (hc : Controller.CorrectAt (callbacks a modulus) c (matrixFin r v A) residueBits)
    (hd : a.dimension c = BinaryNatCode.encode n) (hk : exponent c = BinaryNatCode.encode k) (t : ℕ) :
    ((Controller.step (callbacks a modulus))^[t] (start a exponent c)).length ≤
      2 * c.length + 2 + 64 * ((n + 2).size + (k + 2).size + m.size + 1) ^ 2 := by
  rw [start_encode a exponent c m n k hd hk]
  exact Controller.modular_run_length_le (dimension a) modulus (entry a) c m
    (matrixFin r v A) hc (k + 2) t _ _

end LeanCanny.Algebra.MatrixMoment.EntryBits
