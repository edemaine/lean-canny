/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedAnnihilatorReaders
public import LeanCanny.Algebra.BalancedDegreeTable

/-! # Prepared degrees and exact leaves for the original finite family

The padded reader needs nonzero inputs only below the finite count. Its
canonical leaves are the existing finite-annihilator leaves, and the native
degree preparer writes their exact subtree degrees into the shared frame.
Leaf consistency holds for every table retaining the original source.
-/

@[expose] public section

namespace LeanCanny.Algebra.PaddedAnnihilatorBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (packet)

private theorem polynomial_injective : Function.Injective SeparableIntegerPolynomial.polynomial := by
  intro a b h
  cases a with
  | mk ap ah =>
    cases b with
    | mk bp bh =>
      change ap = bp at h
      subst bp
      rfl

theorem leaves_eq (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (c : List Bool) :
    BalancedCanonicalDegrees.leaves (family B count) count (nonzero B count hne) c =
      FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) := by
  funext i
  apply polynomial_injective
  by_cases hi : i < count c
  · simp only [BalancedCanonicalDegrees.leaves, FiniteAnnihilatorTree.leaf, hi, dite_true,
      SeparableIntegerPolynomial.squarefree]
    rw [polynomial_packet, ite_eq_left hi]
  · simp only [BalancedCanonicalDegrees.leaves, FiniteAnnihilatorTree.leaf, hi, dite_false]

theorem degree_bound (B : Family) (count D : List Bool → ℕ)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (c : List Bool) (i : ℕ) (hi : i < count c) :
    ((family B count).polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c := by
  rw [polynomial_packet, ite_eq_left hi]
  exact hdegree c i hi

noncomputable def prepareDegrees (B : Family) (count D : List Bool → ℕ) : List Bool → List Bool :=
  BalancedDegreeTable.prepare (family B count) count D

theorem prepareDegreesEvaluator (B : Family) (A : Readers B) (count D : List Bool → ℕ)
    (hn : UnaryFn count) (hD : BinaryFn D)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c) :
    SpaceFunction (prepareDegrees B count D) :=
  BalancedDegreeTable.prepareEvaluator (family B count) (readers B A count hn) (nonzero B count hne)
    count D hn hD (degree_bound B count D hdegree)

theorem prepared_order (B : Family) (count D : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (c : List Bool) (h i : ℕ) (hh : h ≤ (count c).size) (hi : i < 2 ^ ((count c).size - h)) :
    BalancedMetadataTable.order (packet (prepareDegrees B count D c) h i) =
      (BalancedPrimitiveTree.node
        (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) h i).polynomial.natDegree := by
  have he := BalancedDegreeTable.prepared_order (family B count) count D (nonzero B count hne)
    (degree_bound B count D hdegree) c h i hh hi
  rw [leaves_eq B count hne c] at he
  exact he

theorem leaf_consistent (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (frame c : List Bool) (hs : BalancedMetadataTable.source frame = c) (i : ℕ) :
    BalancedTablePolynomials.Consistent (family B count) frame
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) 0 i := by
  change ScaledSquarefree.polynomial ((family B count).polynomial (pair (BalancedMetadataTable.source frame) (BinaryNatCode.encode i))) = _
  rw [hs]
  exact squarefree_leaf B count hne c i

theorem prepared_leaf_consistent (B : Family) (count D : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (c : List Bool) (i : ℕ) :
    BalancedTablePolynomials.Consistent (family B count) (prepareDegrees B count D c)
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) 0 i :=
  leaf_consistent B count hne _ c (BalancedDegreeTable.prepared_source _ _ _ c) i

theorem tree_parameter (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (frame c : List Bool)
    (hc : BalancedTablePolynomials.Consistent (family B count) frame
      (FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)) (count c).size 0) :
    BalancedTablePolynomials.tree (family B count) frame (count c).size 0 =
      (FiniteAnnihilatorTree.parameter (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)).polynomial :=
  BalancedTablePolynomials.tree_eq_node _ _ _ _ _ hc

end LeanCanny.Algebra.PaddedAnnihilatorBits
