/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedDirectionCorrect
public import LeanCanny.Algebra.PaddedAnnihilatorMetadata
public import LeanCanny.Algebra.FiniteAnnihilatorHeight

/-! # Source-derived bounds for a finite-annihilator direction step

The existing finite-tree envelope supplies one binary height control for
every prepared child. Exact degrees and consistency below the parent suffice
for a correct scan/write; child heights and fitting directions are derived
from the original finite source bounds and prepared table width.
-/

@[expose] public section

namespace LeanCanny.Algebra.PaddedAnnihilatorBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (packet)

def directionHeight (count D b : List Bool → ℕ) (p : List Bool) : ℕ :=
  let c := BalancedMetadataTable.source (BalancedParameterContext.original p)
  FiniteAnnihilatorTree.sourceHeight (D c) (b c) (count c)

theorem directionHeight_binary {count D b : List Bool → ℕ}
    (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) : BinaryFn (directionHeight count D b) := by
  have hc := mem_FP_comp BalancedParameterContext.original_FP BalancedMetadataTable.source_FP
  exact (FiniteAnnihilatorTree.sourceHeight_binary hD hb hn).comp hc

noncomputable def updateDirection (B : Family) (count D b : List Bool → ℕ) : List Bool → List Bool :=
  BalancedTablePolynomials.Candidate.update (family B count) (directionHeight count D b)

theorem updateDirectionEvaluator (B : Family) (A : Readers B) (count D b : List Bool → ℕ)
    (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) : SpaceFunction (updateDirection B count D b) :=
  BalancedTablePolynomials.Candidate.updateEvaluator (family B count) (readers B A count hn)
    (directionHeight count D b) (directionHeight_binary hn hD hb)

theorem consistent_coefficient_bound (B : Family) (count D b : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)
    (f c : List Bool) (h i : ℕ) (hh : h ≤ (count c).size)
    (hc : BalancedTablePolynomials.Consistent (family B count) f
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) h i) (k : ℕ) :
    ((BalancedTablePolynomials.tree (family B count) f h i).coeff k).natAbs ≤
      2 ^ FiniteAnnihilatorTree.sourceHeight (D c) (b c) (count c) := by
  rw [BalancedTablePolynomials.tree_eq_node _ _ _ _ _ hc]
  have hm := (FiniteAnnihilatorTree.source_tree_bounds
    (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) (D c) (b c)
    (hdegree c) (fun j hj l => (B.coefficient_bound _ l).trans
      (Nat.pow_le_pow_right (by decide) (hheight c j hj))) h i hh).parameterMass
  exact (coeff_natAbs_le_coefficientMass _ k).trans hm

theorem updateDirection_consistent (B : Family) (count D b : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)
    (f c : List Bool) (h i : ℕ) (hs : BalancedMetadataTable.source f = c)
    (hw : BalancedMetadataTable.width f = BalancedDegreeTable.width count D c)
    (hcap : BalancedMetadataTable.capacity (count c) ≤ BalancedMetadataTable.cells f)
    (hh : h + 1 ≤ (count c).size) (hi : i < 2 ^ ((count c).size - (h + 1)))
    (hcl : BalancedTablePolynomials.Consistent (family B count) f
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) h (2 * i))
    (hcr : BalancedTablePolynomials.Consistent (family B count) f
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) h (2 * i + 1))
    (hdl : BalancedMetadataTable.order (packet f h (2 * i)) =
      (BalancedPrimitiveTree.node
        (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) h (2 * i)).polynomial.natDegree)
    (hdr : BalancedMetadataTable.order (packet f h (2 * i + 1)) =
      (BalancedPrimitiveTree.node
        (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) h (2 * i + 1)).polynomial.natDegree) :
    BalancedTablePolynomials.Consistent (family B count) (updateDirection B count D b (packet f (h + 1) i))
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) (h + 1) i := by
  have hW : 0 < BalancedMetadataTable.width f := by rw [hw]; exact BalancedDegreeTable.width_pos count D c
  have hbound (j : ℕ) (hc : BalancedTablePolynomials.Consistent (family B count) f
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) h j) :=
    consistent_coefficient_bound B count D b hne hdegree hheight f c h j (by omega) hc
  have hb (right : Bool) (hc : BalancedTablePolynomials.Consistent (family B count) f
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c))
        h (2 * i + if right then 1 else 0)) (k : ℕ) :
      ((BalancedTablePolynomials.node (family B count) (BalancedParameterContext.child right (packet f (h + 1) i))).coeff k).natAbs ≤
        2 ^ directionHeight count D b (packet f (h + 1) i) := by
    rw [BalancedParameterContext.child_packet, BalancedTablePolynomials.node_packet]
    simpa only [directionHeight, BalancedParameterContext.original_packet, hs] using hbound _ hc k
  apply BalancedTablePolynomials.Candidate.update_consistent (family B count) (directionHeight count D b) f _ (count c) h i
    hW hcap hh hi hcl hcr hdl hdr
  · exact hb false (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hcl)
  · exact hb true (by simpa only [ite_true] using hcr)
  · rw [hw]
    have hf := BalancedDegreeTable.direction_fits (family B count) count D (nonzero B count hne)
      (degree_bound B count D hdegree) c h i hh
    rw [leaves_eq B count hne c] at hf
    exact hf

end LeanCanny.Algebra.PaddedAnnihilatorBits
