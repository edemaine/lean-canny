/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralDenominatorPrefixFP

/-! # Saved-context access to denominator passes

Coordinate packets can select a common saved input while retaining the
pass cursor, accumulator, and scalar-selector index. All metadata access
remains native FP, without any denominator or algebraic-value oracle.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralDenominatorPass
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

def requery (F : Family) (original : List Bool → List Bool) : Family where
  count c := F.count (original c)
  modulus c := F.modulus (original c)
  modulus_ne_zero c := F.modulus_ne_zero (original c)
  arity c := F.arity (original c)
  leading c := F.leading (original c)
  degree c := F.degree (original c)
  exponent c := F.exponent (original c)
  index c := F.index (original c)

def contextQuery (original : List Bool → List Bool) (p : List Bool) : List Bool := pair (original (pairFst p)) (pairSnd p)

theorem contextQuery_FP (original : List Bool → List Bool) (ho : original ∈ FP) : contextQuery original ∈ FP :=
  mem_FP_pair (mem_FP_comp (f := pairFst) (g := original) pairFst_mem_FP ho) pairSnd_mem_FP

theorem contextQuery_cursor (original : List Bool → List Bool) (p : List Bool) : cursor (contextQuery original p) = cursor p := by
  simp only [cursor, contextQuery, BoundedFold.counter, pairSnd_pair]

def indexQuery (original : List Bool → List Bool) (z : List Bool) : List Bool := pair (contextQuery original (pairFst z)) (pairSnd z)

theorem indexQuery_FP (original : List Bool → List Bool) (ho : original ∈ FP) : indexQuery original ∈ FP :=
  mem_FP_pair (mem_FP_comp (f := pairFst) (g := contextQuery original) pairFst_mem_FP (contextQuery_FP original ho)) pairSnd_mem_FP

def leadingWord (F : Family) (c : List Bool) (i : ℕ) : List Bool :=
  residueBits (F.leading c i : ZMod (F.modulus c))

attribute [local irreducible] leadingWord

theorem Access.requery (F : Family) (a : Access F) (original : List Bool → List Bool) (ho : original ∈ FP) : Access (requery F original) where
  count := a.count.comp ho
  modulus := a.modulus.comp ho
  arity := by
    apply UnaryFn.of_eq (a.arity.comp (contextQuery_FP original ho))
    intro p
    rw [contextQuery_cursor]
    simp only [contextQuery, pairFst_pair]
    rfl
  leading := by
    have HL : (fun p => leadingWord F (pairFst p) (cursor p)) ∈ FP := by
      simpa only [leadingWord] using a.leading
    have H := mem_FP_comp (contextQuery_FP original ho) HL
    refine mem_FP_of_eq H (fun p => ?_)
    change leadingWord F (pairFst (contextQuery original p)) (cursor (contextQuery original p)) = _
    rw [contextQuery_cursor]
    simp only [contextQuery, pairFst_pair]
    unfold leadingWord
    rfl
  degree := by
    apply BinaryFn.of_eq (a.degree.comp (contextQuery_FP original ho))
    intro p
    change F.degree (pairFst (contextQuery original p)) (cursor (contextQuery original p)) = _
    rw [contextQuery_cursor]
    simp only [contextQuery, pairFst_pair]
    rfl
  exponent := by
    apply BinaryFn.of_eq (a.exponent.comp (contextQuery_FP original ho))
    intro p
    change F.exponent (pairFst (contextQuery original p)) (cursor (contextQuery original p)) = _
    rw [contextQuery_cursor]
    simp only [contextQuery, pairFst_pair]
    rfl
  index := by
    apply BinaryFn.of_eq (a.index.comp (indexQuery_FP original ho))
    intro z
    change F.index (pairFst (pairFst (indexQuery original z))) (cursor (pairFst (indexQuery original z))) (Nat.fromBitsLE (pairSnd (indexQuery original z))) = _
    simp only [indexQuery, pairFst_pair, pairSnd_pair, contextQuery_cursor]
    simp only [contextQuery, pairFst_pair]
    rfl

end LeanCanny.Algebra.IntegralDenominatorPass
