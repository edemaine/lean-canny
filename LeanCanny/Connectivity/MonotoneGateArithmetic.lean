/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.MonotoneGateGraph
public import LeanCanny.Computation.MonotoneBooleanCircuit
/-! # Native monotone circuit controls and exact zero arithmetic for gate values -/
@[expose] public section
namespace LeanCanny.Connectivity.MonotoneGateArithmetic
open LeanCanny.Encoding LeanCanny.Computation ETR Set
open MonotoneGateSource BooleanCircuitSpace
open scoped Classical

def call (F : MonotoneGateSource.Family) (q : List Bool) : List Bool :=
  pair (pairFst q) (List.replicate (min (Nat.fromBitsLE (pairSnd q)) (F.count (pairFst q))) true)

theorem call_FP (F : MonotoneGateSource.Family) (hF : MonotoneGateSource.Access F) : call F ∈ FP :=
  mem_FP_pair pairFst_mem_FP (UnaryFn.fromBitsLE_min pairSnd_mem_FP (hF.count.comp pairFst_mem_FP)).mem_FP

theorem call_pair (F : MonotoneGateSource.Family) (c : List Bool) (i : ℕ) (hi : i≤F.count c) :
    call F (pair c (BinaryNatCode.encode i)) = pair c (List.replicate i true) := by
  simp only [call,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,min_eq_left hi]

def circuit (F : MonotoneGateSource.Family) : BooleanCircuitSpace.Family where
  count := F.count
  tag q := F.kind (call F q)
  left q := F.left (call F q)
  right q := F.right (call F q)

theorem circuit_access (F : MonotoneGateSource.Family) (hF : MonotoneGateSource.Access F) :
    BooleanCircuitSpace.Access (circuit F) :=
  ⟨hF.count,hF.kind.comp (call_FP F hF),BinaryFn.ofUnary (hF.left.comp (call_FP F hF)),
    BinaryFn.ofUnary (hF.right.comp (call_FP F hF))⟩

theorem predicate_mono (F : MonotoneGateSource.Family) (c : List Bool) (hk : ∀ q, F.kind q≠3) :
    ∀ a b : Fin (F.count c) → Prop, (∀ i, a i → b i) →
      MonotoneBooleanCircuit.predicate (circuit F) c a → MonotoneBooleanCircuit.predicate (circuit F) c b :=
  MonotoneBooleanCircuit.predicate_mono (circuit F) c (fun _ => hk _)

noncomputable def realOperation (k : ℕ) (a l r : ℝ) : ℝ :=
  if k=1 then 0 else if k=2 then a else if k=4 then l^2+r^2 else if k=5 then l*r else 1

theorem operation_zero_iff {k : ℕ} (hk : k≠3) {a l r : ℝ} {A L R : Bool}
    (ha : a=0 ↔ A=true) (hl : l=0 ↔ L=true) (hr : r=0 ↔ R=true) :
    realOperation k a l r=0 ↔ BooleanCircuitSpace.operation k A L R=true := by
  by_cases H1 : k=1
  · simp [realOperation,BooleanCircuitSpace.operation,H1]
  by_cases H2 : k=2
  · simpa only [H2,realOperation,BooleanCircuitSpace.operation,decide_eq_true_eq,
      show (2 : ℕ)≠1 by decide,show (2 : ℕ)≠3 by decide,show (2 : ℕ)≠4 by decide,
      show (2 : ℕ)≠5 by decide,ite_false,ite_true,false_or,true_and,false_and,or_false] using ha
  by_cases H4 : k=4
  · have HS : l^2+r^2=0 ↔ l=0 ∧ r=0 := by
      constructor
      · intro H
        constructor <;> nlinarith [sq_nonneg l,sq_nonneg r]
      · rintro ⟨rfl,rfl⟩
        norm_num
    simpa [realOperation,BooleanCircuitSpace.operation,H4] using HS.trans (and_congr hl hr)
  by_cases H5 : k=5
  · simpa [realOperation,BooleanCircuitSpace.operation,H5] using (mul_eq_zero.trans (or_congr hl hr))
  simp [realOperation,BooleanCircuitSpace.operation,H1,H2,hk,H4,H5]

theorem read_guarded (F : BooleanCircuitSpace.Family) (a : List Bool → Bool) (c : List Bool) (i j : ℕ) :
    (values F a c i)[j]?.getD false = if j < i then wireValue F a c j else false := by
  by_cases H : j < i
  · rw [ite_eq_left H]
    exact read_wire F a c i j H
  · rw [ite_eq_right H]
    have HE : (values F a c i)[j]? = none := List.getElem?_eq_none (by rw [values_length]; omega)
    rw [HE]
    rfl

end LeanCanny.Connectivity.MonotoneGateArithmetic
