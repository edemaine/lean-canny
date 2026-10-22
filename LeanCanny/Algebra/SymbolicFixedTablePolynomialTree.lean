/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableTaskRouting
public import LeanCanny.Algebra.BalancedMetadataTable

/-! # Total supplied-table symbolic polynomials and native alpha bounds

All metadata words, including inconsistent tables, define a polynomial tree.
Every table order is bounded by the encoded table width. A uniform leaf alpha
bound therefore yields a binary-FP bound for every node without traversing its
subtree or assuming metadata correctness.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTablePolynomialTree
open Polynomial SymbolicScaledSquarefree SymbolicFixedTable
open LeanCanny.Encoding LeanCanny.Computation
open BalancedParameterContext (packet child original height index)
open scoped Classical BigOperators
attribute [local irreducible] Matrix.det shiftFamily

noncomputable def tree (L : List Bool → Polynomial Coefficient) (c : List Bool) : ℕ → ℕ → Polynomial Coefficient
  | 0, i => L (pair c (BinaryNatCode.encode i))
  | h + 1, i => cannyResultantWithDegrees (tree L c h (2 * i)) (tree L c h (2 * i + 1))
      (BalancedMetadataTable.direction (packet c (h + 1) i))
      (BalancedMetadataTable.order (packet c h (2 * i))) (BalancedMetadataTable.order (packet c h (2 * i + 1)))

noncomputable def node (L : List Bool → Polynomial Coefficient) (p : List Bool) : Polynomial Coefficient :=
  tree L (original p) (height p) (index p)

theorem node_packet (L : List Bool → Polynomial Coefficient) (c : List Bool) (h i : ℕ) :
    node L (packet c h i) = tree L c h i := by
  simp only [node, BalancedParameterContext.original_packet, BalancedParameterContext.height_packet,
    BalancedParameterContext.index_packet]

theorem node_zero (L : List Bool → Polynomial Coefficient) (p : List Bool) (hh : height p = 0) :
    node L p = L (pair (original p) (BinaryNatCode.encode (index p))) := by rw [node, hh, tree]

theorem node_children (L : List Bool → Polynomial Coefficient) (p : List Bool) (hh : 0 < height p) :
    node L p = cannyResultantWithDegrees (node L (child false p)) (node L (child true p))
      (BalancedMetadataTable.direction p) (BalancedMetadataTable.order (child false p)) (BalancedMetadataTable.order (child true p)) := by
  obtain ⟨h, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  have hd := BalancedMetadataTable.read_eq_packet true p
  have hl := BalancedMetadataTable.read_eq_packet false (child false p)
  have hr := BalancedMetadataTable.read_eq_packet false (child true p)
  unfold BalancedMetadataTable.direction BalancedMetadataTable.order
  rw [hd, hl, hr]
  simp only [node, BalancedParameterContext.original_child, BalancedParameterContext.height_child,
    BalancedParameterContext.index_child, he, Nat.succ_sub_one, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
  rfl

def orderCap (c : List Bool) : ℕ := 2 ^ BalancedMetadataTable.width c

theorem order_le_cap (p : List Bool) : BalancedMetadataTable.order p ≤ orderCap (original p) :=
  ((Nat.fromBitsLE_lt_pow_length _).trans_le
    (Nat.pow_le_pow_right (by decide) (BalancedMetadataTable.read_length_le false p))).le

theorem orderCap_binary : BinaryFn orderCap := (BinaryFn.const 2).powUnary BalancedMetadataTable.width_unary

def innerBound (E : List Bool → ℕ) (c : List Bool) (h : ℕ) : ℕ := E c * (2 * orderCap c + 1) ^ h

theorem specified_inner_degree (p q : Polynomial Coefficient) (c m n E : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ E) (hq : ∀ k, (q.coeff k).natDegree ≤ E) (k : ℕ) :
    ((cannyResultantWithDegrees p q c m n).coeff k).natDegree ≤ (m + n) * E := by
  have h := PolynomialKronecker.determinant_inner_degree
    (Polynomial.sylvester (shiftFamily p c) (q.map C) m n) (fun _ => E)
    (sylvester_inner_degree p q c m n E hp hq) k
  simpa only [cannyResultantWithDegrees, Polynomial.resultant, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

theorem tree_inner_degree (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
    (hE : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (c : List Bool) (h i k : ℕ) : ((tree L c h i).coeff k).natDegree ≤ innerBound E c h := by
  induction h generalizing i k with
  | zero => simpa only [tree, innerBound, pow_zero, mul_one] using hE c i k
  | succ h ih =>
    have hl := order_le_cap (packet c h (2 * i))
    have hr := order_le_cap (packet c h (2 * i + 1))
    rw [BalancedParameterContext.original_packet] at hl hr
    apply (specified_inner_degree _ _ _ _ _ _ (fun k => ih (2 * i) k) (fun k => ih (2 * i + 1) k) k).trans
    calc
      _ ≤ (2 * orderCap c + 1) * innerBound E c h := Nat.mul_le_mul_right _ (by omega)
      _ = innerBound E c (h + 1) := by unfold innerBound; rw [pow_succ]; ring

def nodeBound (E : List Bool → ℕ) (p : List Bool) : ℕ := innerBound E (original p) (height p)

theorem node_inner_degree (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
    (hE : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (p : List Bool) (k : ℕ) : ((node L p).coeff k).natDegree ≤ nodeBound E p :=
  tree_inner_degree L E hE _ _ _ k

theorem nodeBound_binary (E : List Bool → ℕ) (hE : BinaryFn E) : BinaryFn (nodeBound E) := by
  have he : BinaryFn (fun p => E (original p)) := hE.comp BalancedParameterContext.original_FP
  have ho : BinaryFn (fun p => orderCap (original p)) :=
    orderCap_binary.comp BalancedParameterContext.original_FP
  exact he.mul ((((BinaryFn.const 2).mul ho).add
    (BinaryFn.const 1)).powUnary BalancedParameterContext.height_unary)

end LeanCanny.Algebra.SymbolicFixedTablePolynomialTree
