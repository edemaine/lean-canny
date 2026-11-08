/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.MonotoneGateValues
/-! # The native arithmetic root is zero exactly for the monotone Boolean circuit -/
@[expose] public section
namespace LeanCanny.Connectivity.MonotoneGateRoot
open ETR Set LeanCanny.Encoding LeanCanny.Computation
open MonotoneGateSource MonotoneGateGraph MonotoneGateArithmetic MonotoneGateValues
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def boolWire (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ) (i : ℕ) : Bool :=
  BooleanCircuitSpace.wireValue (circuit F) (MonotoneBooleanCircuit.atom (circuit F) c (status F c x)) c i

theorem bool_step (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ) (i : ℕ)
    (hi : i < F.count c) :
    boolWire F c x i = BooleanCircuitSpace.operation (F.kind (pair c (List.replicate i true)))
      (MonotoneBooleanCircuit.atom (circuit F) c (status F c x) (pair c (BinaryNatCode.encode i)))
      ((BooleanCircuitSpace.values (circuit F) (MonotoneBooleanCircuit.atom (circuit F) c (status F c x)) c i)[F.left (pair c (List.replicate i true))]?.getD false)
      ((BooleanCircuitSpace.values (circuit F) (MonotoneBooleanCircuit.atom (circuit F) c (status F c x)) c i)[F.right (pair c (List.replicate i true))]?.getD false) := by
  unfold boolWire
  rw [BooleanCircuitSpace.wireValue_step]
  simp only [circuit,call_pair F c i hi.le]

theorem atom_zero (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (i : ℕ) (hi : i < F.count c) :
    (atomBody F (pair c (List.replicate i true))).eval (Formula.extend (full F c x))=0 ↔
      MonotoneBooleanCircuit.atom (circuit F) c (status F c x) (pair c (BinaryNatCode.encode i))=true := by
  have HS := atomBody_arity F (pair c (List.replicate i true))
    (by simpa only [index,count,pairFst_pair,pairSnd_pair,List.length_replicate] using hi)
    (by simpa only [dimension,pairFst_pair] using ha i hi)
  have HScope : (atomBody F (pair c (List.replicate i true))).arity≤base F c := by
    simpa only [dimension,count,pairFst_pair,base] using HS
  rw [eval_prefix F c x _ HScope]
  simp only [MonotoneBooleanCircuit.atom,circuit,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    dite_eq_left hi,decide_eq_true_eq,status]

theorem child_zero (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (i : Fin (F.count c)) (j : ℕ)
    (IH : ∀ k (hk : k < i.val), value F c x ⟨k,hk.trans i.isLt⟩=0 ↔ boolWire F c x k=true) :
    childValue F c x i j=0 ↔
      ((BooleanCircuitSpace.values (circuit F) (MonotoneBooleanCircuit.atom (circuit F) c (status F c x)) c i.val)[j]?.getD false)=true := by
  rw [read_guarded]
  unfold childValue
  by_cases H : j < i.val
  · rw [dite_eq_left H,ite_eq_left H]
    exact IH j H
  · rw [dite_eq_right H,ite_eq_right H]
    norm_num

theorem wire_zero (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) :
    ∀ i (hi : i < F.count c), value F c x ⟨i,hi⟩=0 ↔ boolWire F c x i=true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i IH =>
    intro hi
    rw [gate_value F c x ha ⟨i,hi⟩,body_eval,bool_step F c x i hi]
    apply operation_zero_iff (hk _) (atom_zero F c x ha i hi)
    · rw [child_eval F c x ⟨i,hi⟩ false]
      simp only [Bool.coe_false,ite_false]
      exact child_zero F c x ⟨i,hi⟩ _ (fun k hk => IH k hk (hk.trans hi))
    · rw [child_eval F c x ⟨i,hi⟩ true]
      simp only [ite_true]
      exact child_zero F c x ⟨i,hi⟩ _ (fun k hk => IH k hk (hk.trans hi))

theorem root_zero (F : MonotoneGateSource.Family) (c : List Bool) (x : Fin (base F c) → ℝ)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) :
    rootValue F c x=0 ↔ MonotoneBooleanCircuit.predicate (circuit F) c (status F c x) := by
  by_cases H : F.count c=0
  · have HR : rootValue F c x=1 := by
      unfold rootValue root
      rw [ite_eq_left H]
      simp only [Term.eval,Int.cast_one]
    rw [HR]
    simp only [MonotoneBooleanCircuit.predicate,BooleanCircuitSpace.value,circuit,H,
      BooleanCircuitSpace.values,List.getElem?_nil,Option.getD_none,Bool.false_eq_true]
    norm_num
  · have HP : 0 < F.count c := Nat.pos_of_ne_zero H
    rw [root_value F c x HP]
    unfold MonotoneBooleanCircuit.predicate BooleanCircuitSpace.value
    change value F c x ⟨F.count c-1,by omega⟩=0 ↔
      (BooleanCircuitSpace.values (circuit F) (MonotoneBooleanCircuit.atom (circuit F) c (status F c x)) c
        (F.count c))[F.count c-1]?.getD false=true
    rw [BooleanCircuitSpace.read_wire _ _ c _ _ (by omega)]
    exact wire_zero F c x ha hk _ _

end LeanCanny.Connectivity.MonotoneGateRoot
