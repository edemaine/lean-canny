/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedAnnihilatorPreparation

/-! # Uniform native coefficients of the canonical finite annihilator

The evaluator prepares all degree and direction metadata itself, then runs
the uniform coefficient reader at the root. Bounds concern only the original
finite source. No supplied table, consistency, intermediate coefficient, or
execution-clock assumption remains.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteAnnihilatorBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)

noncomputable def finiteParameter (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (c : List Bool) : ℤ[X] :=
  (FiniteAnnihilatorTree.parameter (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)).polynomial

noncomputable def coefficient (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (q : List Bool) : List Bool :=
  PrincipalCoefficientBits.integerResidue
    ((finiteParameter B count hne (pairFst (pairFst q))).coeff (Nat.fromBitsLE (pairSnd (pairFst q))))
    (Nat.fromBitsLE (pairSnd q) + 1)

def rootQuery (count : List Bool → ℕ) (p : List Bool) : List Bool :=
  pair (pair (BalancedParameterContext.packet (pairSnd p) (count (pairFst (pairFst (pairFst p)))).size 0)
    (pairSnd (pairFst (pairFst p)))) (pairSnd (pairFst p))

theorem rootQuery_FP {count : List Bool → ℕ} (hn : UnaryFn count) : rootQuery count ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hh : UnaryFn (fun p => (count (pairFst (pairFst (pairFst p)))).size) := (hn.comp hc).size
  have hp := BalancedParameterContext.packet_FP pairSnd_mem_FP hh (BinaryFn.const 0)
  have hk := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
  have hm := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair hp hk) hm

attribute [local irreducible] BalancedTablePolynomials.tree BalancedTablePolynomials.node

theorem prepared_root (B : Family) (count D b : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c) (c : List Bool) :
    BalancedTablePolynomials.node (PaddedAnnihilatorBits.family B count)
      (BalancedParameterContext.packet (PaddedAnnihilatorPreparation.prepare B count D b c) (count c).size 0) =
        finiteParameter B count hne c := by
  rw [BalancedTablePolynomials.node_packet]
  exact PaddedAnnihilatorBits.tree_parameter B count hne _ c
    (PaddedAnnihilatorPreparation.prepare_consistent B count D b hne hdegree hheight c)

theorem coefficientEvaluator (B : Family) (A : Readers B) (count D b : List Bool → ℕ)
    (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c) :
    SpaceFunction (coefficient B count hne) := by
  have E := (PaddedAnnihilatorPreparation.prepareEvaluator B count D b hne hdegree A hn hD hb).precompose
    (pairFst ∘ pairFst) (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have R := (E.withInput.postcompose (rootQuery count) (rootQuery_FP hn)).chain
    (BalancedTablePolynomials.evaluator (PaddedAnnihilatorBits.family B count) (PaddedAnnihilatorBits.readers B A count hn))
  exact R.congr (funext fun q => by
    simp only [Function.comp_apply, rootQuery, pairFst_pair, pairSnd_pair, BalancedTablePolynomials.nodeValue,
      CannyBalancedTaskRouting.nodeContext, CannyResultantBits.mValue]
    rw [prepared_root B count D b hne hdegree hheight]
    rfl)

end LeanCanny.Algebra.FiniteAnnihilatorBits
