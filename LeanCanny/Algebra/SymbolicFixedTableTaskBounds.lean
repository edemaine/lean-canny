/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SymbolicFixedTableTaskDegrees
public import LeanCanny.Algebra.SymbolicFixedTableTaskResidues

/-! # A polynomial bound on every selected degree in the symbolic graph -/
@[expose] public section
set_option maxRecDepth 256
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra.SymbolicFixedTableTreeSource
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial SymbolicScaledSquarefree SymbolicFixedTableEntryBits
open SymbolicFixedTableTaskRouting BerkowitzPolynomial.TaskDispatch
attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul
  BinaryNat.div BinaryNat.mod CannyResultantBits.RecursiveStage.selectRight
  CannyResultantBits.RecursiveStage.active CannyResultantBits.RecursiveStage.leftQuery
  CannyResultantBits.RecursiveStage.rightQuery selectedDegree family leftOrder rightOrder
  BalancedMetadataTable.read BalancedMetadataTable.order BalancedParameterContext.child origin nodeContext radix

variable (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
  (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)

def sourceIncrement (R : List Bool → ℕ) (root : List Bool) : ℕ := 2 * R root + (5 * root.length + 4) + 2
def selectedDegreeBound (R : List Bool → ℕ) (root : List Bool) : ℕ :=
  initialDegreeSizeBound E root + sourceIncrement R root * root.length

theorem sourceIncrement_unary (R : List Bool → ℕ) (hR : UnaryFn R) : UnaryFn (sourceIncrement R) :=
  (((UnaryFn.const 2).mul hR).add (((UnaryFn.const 5).mul (UnaryFn.length id_mem_FP)).add
    (UnaryFn.const 4))).add (UnaryFn.const 2)

theorem selectedDegreeBound_unary (hE : BinaryFn E) (R : List Bool → ℕ) (hR : UnaryFn R) :
    UnaryFn (selectedDegreeBound E R) :=
  (initialDegreeSizeBound_unary E hE).add ((sourceIncrement_unary R hR).mul (UnaryFn.length id_mem_FP))

private theorem weighted_step (x y n h : ℕ) (hh : 0 < h) (hx : x ≤ y + n) :
    x + n * (h - 1) ≤ y + n * h := by
  have he : n * (h - 1) + n = n * h := by rw [← Nat.mul_succ]; congr 1; omega
  omega

theorem request_degree_potential_le (R : List Bool → ℕ)
    (hR : ∀ root q, tasks L E hL root q → (radix E (origin q)).size ≤ R root)
    (root q child : List Bool) (hq : tasks L E hL root q)
    (h : Requests (access L E hL) (program L E hL).controller (fun _ => 1) q child) :
    (selectedDegree (family L E) child).size + sourceIncrement R root * level (origin child) ≤
      (selectedDegree (family L E) q).size + sourceIncrement R root * level (origin q) := by
  by_cases hs : SelectedSource q
  · obtain ⟨hl, hn, he⟩ := request_source L E hL q child h hs
    have ha := CannyResultantBits.RecursiveStage.request_active (source L).access _ hn
    have hc : tasks L E hL root child := hq.tail h
    have hp := hR root q hq
    have hb := hR root child hc
    have ho : origin q = pairFst (payload q) := by
      obtain ⟨hz, hd, hf, hm⟩ := hs
      simp only [origin, hz, hd, hf, hm, Bool.false_eq_true, ite_false]
    have hd : selectedDegree (family L E) q = Nat.fromBitsLE (entryDegree (payload q)) := by
      obtain ⟨hz, hd, hf, hm⟩ := hs
      simp only [selectedDegree, entryDegree, hz, hd, hf, hm, Bool.false_eq_true, ite_false]
    have hh : 0 < level (origin q) := by rw [ho]; exact (isLeaf_false_iff _).mp hl
    have hnode := reachable_node_length_le L E hL root q hq
    rw [ho] at hp hnode
    have hdeg : (selectedDegree (family L E) child).size ≤
        (selectedDegree (family L E) q).size + sourceIncrement R root := by
      rw [he] at hb ⊢
      cases hright : CannyResultantBits.RecursiveStage.selectRight (source L).access
        (sourceInput (fun q => BinaryNatCode.encode (radix E q)) (payload q)) with
      | true =>
        simp only [hright, ite_true] at hb ⊢
        rw [coefficientTask, Function.comp_apply, origin_determinant] at hb
        have ho' := (rightOrder_size_le (pairFst (payload q))).trans hnode
        have ht := rightQuery_degree_size_le L E (payload q) (R root) (5 * root.length + 4) ha hright hp hb ho'
        simpa only [hd, sourceIncrement, Nat.add_assoc] using ht
      | false =>
        simp only [hright, Bool.false_eq_true, ite_false] at hb ⊢
        rw [coefficientTask, Function.comp_apply, origin_determinant] at hb
        have ho' := (leftOrder_size_le (pairFst (payload q))).trans hnode
        have ht := leftQuery_degree_size_le L E (payload q) (R root) (5 * root.length + 4) ha
          hright hp hb ho'
        simpa only [hd, sourceIncrement, Nat.add_assoc] using ht
    have hlev : level (origin child) = level (origin q) - 1 := by
      rw [he, ho]
      split_ifs
      · rw [coefficientTask_level, sourceNode_rightQuery]
        rfl
      · rw [coefficientTask_level, sourceNode_leftQuery]
        rfl
    rw [hlev]
    exact weighted_step _ _ _ _ hh hdeg
  · obtain ⟨t, _, _, hn, he⟩ := h
    have hg := internal_query_degree_le (access L E hL) _ _ q t hn hs
    rcases internal_query_origin (access L E hL) _ _ q t hn hs with he0 | heo
    · rw [he, he0, selectedDegree_zero, origin_zero, level_zero]
      exact Nat.zero_le _
    · rw [he, heo]
      exact Nat.add_le_add_right (Nat.size_le_size hg) _

theorem reachable_degree_potential_le (R : List Bool → ℕ)
    (hR : ∀ root q, tasks L E hL root q → (radix E (origin q)).size ≤ R root)
    (root q : List Bool) (hq : tasks L E hL root q) :
    (selectedDegree (family L E) q).size + sourceIncrement R root * level (origin q) ≤
      (selectedDegree (family L E) root).size + sourceIncrement R root * level (origin root) := by
  change Relation.ReflTransGen _ root q at hq
  induction hq with
  | refl => exact le_refl _
  | @tail q child hq hstep ih => exact (request_degree_potential_le L E hL R hR root q child hq hstep).trans ih

theorem reachable_selectedDegree_size_le (R : List Bool → ℕ)
    (hR : ∀ root q, tasks L E hL root q → (radix E (origin q)).size ≤ R root)
    (root q : List Bool) (hq : tasks L E hL root q) :
    (selectedDegree (family L E) q).size ≤ selectedDegreeBound E R root := by
  have hp := reachable_degree_potential_le L E hL R hR root q hq
  have hg := selectedDegree_root_size_le L E root
  have hh := origin_level_le_length root
  have hm := Nat.mul_le_mul_left (sourceIncrement R root) hh
  unfold selectedDegreeBound
  omega

end LeanCanny.Algebra.SymbolicFixedTableTreeSource
