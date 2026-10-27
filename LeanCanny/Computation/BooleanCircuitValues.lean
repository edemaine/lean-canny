/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BooleanCircuitSpace

/-! # Stable wire values in the native Boolean-circuit evaluator -/

@[expose] public section
namespace LeanCanny.Computation.BooleanCircuitSpace

theorem values_congr (F : Family) (a b : List Bool → Bool) (c : List Bool) (n : ℕ)
    (h : ∀ i < n, a (pair c (BinaryNatCode.encode i)) = b (pair c (BinaryNatCode.encode i))) :
    values F a c n = values F b c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [values]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem values_prefix (F : Family) (atom : List Bool → Bool) (c : List Bool) (m n : ℕ) (hmn : m ≤ n)
    (k : ℕ) (hk : k < m) : (values F atom c n)[k]? = (values F atom c m)[k]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hm : m ≤ n
    · rw [values, List.getElem?_append_left (by rw [values_length]; omega)]
      exact ih hm
    · have he : m = n + 1 := by omega
      rw [he]

def wireValue (F : Family) (atom : List Bool → Bool) (c : List Bool) (i : ℕ) : Bool :=
  (values F atom c (i + 1))[i]?.getD false

theorem read_wire (F : Family) (atom : List Bool → Bool) (c : List Bool) (n i : ℕ) (hi : i < n) :
    (values F atom c n)[i]?.getD false = wireValue F atom c i := by
  rw [values_prefix F atom c (i + 1) n (by omega) i (by omega)]
  rfl

theorem wireValue_step (F : Family) (atom : List Bool → Bool) (c : List Bool) (i : ℕ) :
    wireValue F atom c i = operation (F.tag (pair c (BinaryNatCode.encode i))) (atom (pair c (BinaryNatCode.encode i)))
      ((values F atom c i)[F.left (pair c (BinaryNatCode.encode i))]?.getD false)
      ((values F atom c i)[F.right (pair c (BinaryNatCode.encode i))]?.getD false) := by
  simp only [wireValue, values, List.getElem?_append, values_length, lt_self_iff_false, ite_false,
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem wireValue_refs (F : Family) (atom : List Bool → Bool) (c : List Bool) (i : ℕ)
    (hl : F.left (pair c (BinaryNatCode.encode i)) < i) (hr : F.right (pair c (BinaryNatCode.encode i)) < i) :
    wireValue F atom c i = operation (F.tag (pair c (BinaryNatCode.encode i))) (atom (pair c (BinaryNatCode.encode i)))
      (wireValue F atom c (F.left (pair c (BinaryNatCode.encode i))))
      (wireValue F atom c (F.right (pair c (BinaryNatCode.encode i)))) := by
  rw [wireValue_step, read_wire F atom c i _ hl, read_wire F atom c i _ hr]

theorem value_eq_wireValue (F : Family) (atom : List Bool → Bool) (c : List Bool) (hc : 0 < F.count c) :
    value F atom c = wireValue F atom c (F.count c - 1) := by
  unfold value wireValue
  rw [Nat.sub_add_cancel hc]

end LeanCanny.Computation.BooleanCircuitSpace
