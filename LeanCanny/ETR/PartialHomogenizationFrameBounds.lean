/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenizationData
/-! # Local additive growth for bounded homogenization frames -/
@[expose] public section
namespace LeanCanny.ETR.PartialHomogenizationData
open LeanCanny.Encoding PartialHomogenization

theorem bounded_node_size (k D L : ℕ) (xs : List Data) :
    (bounded k D L (.l xs)).size ≤
      (Data.l (xs.map (bounded k D L))).size +36*D+L+70 := by
  by_cases HL : (Data.l xs).size ≤ L
  · have HC : ∀ a ∈ xs, a.size ≤ L := fun a ha => (Data.size_lt_of_mem ha).le.trans HL
    rcases xs with _ | ⟨tag,_ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩⟩
    · simp [bounded,raw]
    · simp [bounded,raw]
    · have HA := HC a (by simp)
      have HT := HC tag (by simp)
      simp only [bounded,HL,ite_true,raw]
      split_ifs
      · simp only [Data.cons_size,Data.size_empty] at HL ⊢
        omega
      · simp only [Term.dataSize_var]
        omega
      · simp only [Term.dataSize_const_zero]
        omega
    · have HA := HC a (by simp)
      have HB := HC b (by simp)
      have HDA := degree_le k D a
      have HDB := degree_le k D b
      have HDa : max (degree k D a) (degree k D b)-degree k D a ≤ D := by omega
      have HDb : max (degree k D a) (degree k D b)-degree k D b ≤ D := by omega
      simp only [bounded,HL,ite_true,raw]
      split_ifs
      · simp only [List.map_cons,List.map_nil,Data.cons_size,Data.size_empty,
          Codec.unary_size,size_power,Term.dataSize_var,bounded,HA,HB,ite_true]
        omega
      · simp only [List.map_cons,List.map_nil,Data.cons_size,Data.size_empty,
          Codec.unary_size,bounded,HA,HB,ite_true]
        omega
      · simp only [Term.dataSize_const_zero]
        omega
    · simp [bounded,raw]
  · simp only [bounded,HL,ite_false,Term.dataSize_const_zero]
    omega

end LeanCanny.ETR.PartialHomogenizationData
