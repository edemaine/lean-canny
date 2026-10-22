/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedTableCoefficientSource
public import LeanCanny.Algebra.CannyBalancedTaskAddresses
public import LeanCanny.Algebra.CannyResultantTaskDegrees
public import LeanCanny.Algebra.BerkowitzTaskDegrees

/-! # A common degree bound for the supplied-table tree

Orders read from the original table have at most the original input's length
in bits. Internal requests never increase degree; each source descent adds at
most one order and decreases height. The weighted degree/height potential
therefore gives a quadratic bound on every selected degree's bit length.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open LeanCanny.Encoding LeanCanny.Computation
open BerkowitzPolynomial.TaskDispatch CannyBalancedTaskRouting
open BalancedParameterContext (original)

attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul
  BinaryNat.div BinaryNat.mod tree node BalancedMetadataTable.read
  CannyResultantBits.RecursiveStage.selectRight CannyResultantBits.RecursiveStage.leftQuery
  CannyResultantBits.RecursiveStage.rightQuery

theorem matrixFamily_degree (B : SeparableBits.Family) (c : List Bool) :
    (matrixFamily B).degree c = Nat.fromBitsLE (pairSnd (pairFst c)) := by
  change (if isLeaf c then Nat.fromBitsLE (pairSnd (pairFst c))
    else Nat.fromBitsLE (pairSnd (pairFst c))) = _
  split_ifs <;> rfl

theorem selectedDegree_coefficientTask (B : SeparableBits.Family) (right : Bool) (p : List Bool) :
    selectedDegree (matrixFamily B) (coefficientTask right p) = Nat.fromBitsLE (pairSnd p) := by
  change (matrixFamily B).degree (childInput right p) = _
  rw [matrixFamily_degree]
  simp only [childInput, matrixPacket, pairFst_pair, pairSnd_pair]

private theorem decoded_size_le (w : List Bool) : (Nat.fromBitsLE w).size ≤ w.length :=
  Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length w)

theorem selectedDegree_size_le_length (B : SeparableBits.Family) (q : List Bool) :
    (selectedDegree (matrixFamily B) q).size ≤ q.length := by
  have hp : (payload q).length ≤ q.length := by simp only [payload, List.length_drop]; omega
  have hs := (pairSnd_length_le (payload q)).trans hp
  have hsf := (pairSnd_length_le (pairFst (payload q))).trans ((pairFst_length_le _).trans hp)
  have hsss := (pairSnd_length_le (pairSnd (pairSnd (payload q)))).trans
    ((pairSnd_length_le _).trans ((pairSnd_length_le _).trans hp))
  unfold selectedDegree
  split_ifs
  · exact Nat.zero_le _
  · rw [matrixFamily_degree]
    exact (decoded_size_le _).trans hsf
  · exact (decoded_size_le _).trans hs
  · exact (decoded_size_le _).trans hs
  · exact (decoded_size_le _).trans hsss

theorem order_size_le (p : List Bool) :
    (BalancedMetadataTable.order p).size ≤ BalancedMetadataTable.width (original p) :=
  (decoded_size_le _).trans (BalancedMetadataTable.read_length_le false p)

theorem reachable_order_sizes (B : SeparableBits.Family) (root q : List Bool) (hq : reachableTasks B root q) :
    (leftOrder (pairFst (origin q))).size ≤ root.length ∧ (rightOrder (pairFst (origin q))).size ≤ root.length := by
  have ho := CannyBalancedTaskRouting.reachable_original_length_le (leafFamily B) (sourceAccess B) root q hq
  have hl := order_size_le (BalancedParameterContext.child false (nodeContext (origin q)))
  have hr := order_size_le (BalancedParameterContext.child true (nodeContext (origin q)))
  rw [BalancedParameterContext.original_child] at hl hr
  have hw := (BalancedMetadataTable.width_le_length _).trans ho
  exact ⟨hl.trans hw, hr.trans hw⟩

private theorem weighted_step (x y n h : ℕ) (hh : 0 < h) (hx : x ≤ y + n) :
    x + n * (h - 1) ≤ y + n * h := by
  have he : n * (h - 1) + n = n * h := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  omega

theorem request_degree_potential_le (B : SeparableBits.Family) (root q child : List Bool)
    (hq : reachableTasks B root q)
    (h : Requests (matrixAccess B)
      (CannyResultantBits.WithSquarefreeLeaves.program (leafFamily B) (sourceAccess B) isLeaf
        (coefficientTask false) (coefficientTask true)).controller (fun _ => 1) q child) :
    (selectedDegree (matrixFamily B) child).size + (root.length + 1) * level (origin child) ≤
      (selectedDegree (matrixFamily B) q).size + (root.length + 1) * level (origin q) := by
  by_cases hs : SelectedSource q
  · obtain ⟨hl, hr, he⟩ := request_source (leafFamily B) (sourceAccess B) q child h hs
    have hh := (isLeaf_false_iff _).mp hl
    have ha := CannyResultantBits.RecursiveStage.request_active (sourceAccess B) _ hr
    have hb := reachable_order_sizes B root q hq
    obtain ⟨hz, hd, hf, hm⟩ := hs
    have ho : origin q = pairFst (payload q) := by
      simp only [origin, hz, hd, hf, hm, Bool.false_eq_true, ite_false]
    have hg : selectedDegree (matrixFamily B) q = SylvesterPolynomialBits.RecursiveStage.coefficientDegree (payload q) := by
      simp only [selectedDegree, hz, hd, hf, hm, Bool.false_eq_true, ite_false,
        SylvesterPolynomialBits.RecursiveStage.coefficientDegree]
    rw [ho] at hb ⊢
    rw [he]
    split_ifs with hright
    · have hdg := CannyResultantBits.RecursiveStage.rightQuery_degree_length_le (sourceAccess B) _ ha hright
      rw [selectedDegree_coefficientTask, coefficientTask_level, CannyResultantBits.RecursiveStage.rightQuery_context]
      apply weighted_step _ _ _ _ hh
      exact ((decoded_size_le _).trans hdg).trans (by omega)
    · have hleft := Bool.eq_false_iff.mpr hright
      have hdg := CannyResultantBits.RecursiveStage.leftQuery_degree_length_le (sourceAccess B) _ ha hleft
      rw [selectedDegree_coefficientTask, coefficientTask_level, CannyResultantBits.RecursiveStage.leftQuery_context]
      apply weighted_step _ _ _ _ hh
      rw [hg]
      exact ((decoded_size_le _).trans hdg).trans (by omega)
  · obtain ⟨t, _, _, hn, he⟩ := h
    have hg := internal_query_degree_le (matrixAccess B) _ _ q t hn hs
    rcases internal_query_origin (matrixAccess B) _ _ q t hn hs with he0 | heo
    · rw [he, he0, selectedDegree_zero, origin_zero, level_zero]
      exact Nat.zero_le _
    · rw [he, heo]
      exact Nat.add_le_add_right (Nat.size_le_size hg) _

theorem reachable_degree_potential_le (B : SeparableBits.Family) (root q : List Bool) (hq : reachableTasks B root q) :
    (selectedDegree (matrixFamily B) q).size + (root.length + 1) * level (origin q) ≤
      (selectedDegree (matrixFamily B) root).size + (root.length + 1) * level (origin root) := by
  change Relation.ReflTransGen _ root q at hq
  induction hq with
  | refl => exact le_refl _
  | @tail q child hq hstep ih => exact (request_degree_potential_le B root q child hq hstep).trans ih

theorem reachable_degree_size_le (B : SeparableBits.Family) (root q : List Bool) (hq : reachableTasks B root q) :
    (selectedDegree (matrixFamily B) q).size ≤ root.length + (root.length + 1) * root.length := by
  have hp := reachable_degree_potential_le B root q hq
  have hg := selectedDegree_size_le_length B root
  have hh := origin_level_le_length root
  have hm := Nat.mul_le_mul_left (root.length + 1) hh
  omega

end LeanCanny.Algebra.BalancedTablePolynomials
