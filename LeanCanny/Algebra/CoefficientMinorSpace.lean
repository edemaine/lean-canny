/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalMinorSpace

/-! # Scalar subresultant coefficient minors, including terminal orders

Only the first retained row differs from a principal minor. Reusing its binary
column map, determinant budget, and native coefficient children gives a unified
evaluator for interior and terminal coefficient forms.
-/

@[expose] public section

namespace LeanCanny.Algebra.CoefficientMinor
open Polynomial

def row (m n k r : ℕ) (hm : k ≤ m) (hn : k ≤ n) (hr : r ≤ k)
    (i : Fin ((m - k) + (n - k))) : Fin (m + n) :=
  ⟨Subresultant.rowIndex k r i.val, by unfold Subresultant.rowIndex; split_ifs <;> omega⟩

theorem minor_eq_submatrix {R : Type*} [Semiring R] (p q : R[X]) (m n k r : ℕ)
    (hm : k ≤ m) (hn : k ≤ n) (hr : r ≤ k) :
    Subresultant.minor p q m n k r = (Polynomial.sylvester p q m n).submatrix
      (row m n k r hm hn hr) (PrincipalMinor.col m n k hm hn) := by
  funext i j
  rw [Subresultant.minor_apply, Matrix.submatrix_apply, SylvesterBits.sylvester_apply]
  simp only [row, PrincipalMinor.col]
  by_cases hj : j.val < m - k
  · have hjm : j.val < m := by omega
    simp only [Subresultant.colIndex, ite_eq_left hj, hjm, ↓reduceIte, Subresultant.band]
  · have hjm : ¬j.val + k < m := by omega
    have hs : j.val + k - m = j.val - (m - k) := by omega
    simp only [Subresultant.colIndex, ite_eq_right hj, hjm, ↓reduceIte, hs, Subresultant.band]

theorem minor_apply {R : Type*} [Semiring R] (p q : R[X]) (m n k r : ℕ)
    (hm : k ≤ m) (hn : k ≤ n) (hr : r ≤ k) (i j : Fin ((m - k) + (n - k))) :
    Subresultant.minor p q m n k r i j = Polynomial.sylvester p q m n
      (row m n k r hm hn hr i) (PrincipalMinor.col m n k hm hn j) :=
  congrArg (fun M : Matrix (Fin ((m - k) + (n - k))) (Fin ((m - k) + (n - k))) R => M i j)
    (minor_eq_submatrix p q m n k r hm hn hr)

end LeanCanny.Algebra.CoefficientMinor

namespace LeanCanny.Algebra.CoefficientMinorBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
attribute [local irreducible] BinaryNat.add

structure Family where
  source : PrincipalMinorBits.Family
  coefficient : List Bool → ℕ
  coefficient_le : ∀ c, coefficient c ≤ source.order c

def Family.integer (F : Family) : Berkowitz.IntegerFamily where
  dimension := F.source.integer.dimension
  matrix c := Subresultant.minor (F.source.left c) (F.source.right c) (F.source.leftDegree c)
    (F.source.rightDegree c) (F.source.order c) (F.coefficient c)
  budget := F.source.integer.budget
  determinant_bits c := by
    dsimp +instances only [PrincipalMinorBits.Family.integer]
    have h := (Subresultant.minor_det_size_le (F.source.left c) (F.source.right c)
      (F.source.leftDegree c) (F.source.rightDegree c) (F.source.order c) (F.coefficient c) _ _
      (F.source.left_bound c) (F.source.right_bound c)).trans (Subresultant.budget_le_full _ _ _ _ _)
    simpa only [Nat.add_mul, Nat.add_assoc] using h

structure Access (F : Family) where
  source : PrincipalMinorBits.Access F.source
  coefficient : List Bool → List Bool
  coefficient_eq : ∀ c, coefficient c = BinaryNatCode.encode (F.coefficient c)

namespace Access

structure ControlsPolyTime {F : Family} (a : Access F) : Prop where
  source : a.source.bits.ControlsPolyTime
  coefficient : a.coefficient ∈ FP

def row {F : Family} (a : Access F) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (SylvesterBits.row p) = 0 then a.coefficient (SylvesterBits.context p)
  else a.source.bits.row p

def query {F : Family} (a : Access F) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (row a p) (a.source.bits.col p))

def entry {F : Family} (a : Access F) : List Bool → List Bool := SylvesterBits.entry a.source.bits.base ∘ query a

theorem row_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : row a ∈ FP := by
  have hz : FPPred (fun p => Nat.fromBitsLE (SylvesterBits.row p) = 0) :=
    (BinaryNat.lt_fppred SylvesterBits.row_mem_FP (constFn_mem_FP (BinaryNatCode.encode 1))).of_iff
      (fun p => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  have h := hz.ite_mem_FP (mem_FP_comp SylvesterBits.context_mem_FP ha.coefficient)
    (a.source.bits.row_mem_FP ha.source)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem query_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : query a ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (row_FP a ha) (a.source.bits.col_mem_FP ha.source))

theorem entryEvaluator {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (P : SpaceFunction a.source.bits.base.leftCoefficient) (Q : SpaceFunction a.source.bits.base.rightCoefficient) :
    SpaceFunction (entry a) :=
  (SylvesterBits.entryEvaluator a.source.bits.base ha.source.base P Q).precompose (query a) (query_FP a ha)

def integer {F : Family} (a : Access F) : Berkowitz.IntegerAccess F.integer where
  dimension := a.source.integer.dimension
  budget := a.source.integer.budget
  entry := entry a
  dimension_eq := a.source.integer.dimension_eq
  budget_eq := a.source.integer.budget_eq
  entry_eq := by
    intro q i j
    have h := SylvesterBits.entry_correct a.source.bits.base q
      (F.source.left (pairFst q)) (F.source.right (pairFst q))
      (F.source.leftDegree (pairFst q)) (F.source.rightDegree (pairFst q))
      (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
      ⟨a.source.leftDegree_eq _, a.source.rightDegree_eq _, a.source.left_eq q, a.source.right_eq q,
        by simp [residueBits, BinaryNatCode.encode]⟩
      (CoefficientMinor.row _ _ _ _ (F.source.order_left _) (F.source.order_right _) (F.coefficient_le _) i)
      (PrincipalMinor.col _ _ _ (F.source.order_left _) (F.source.order_right _) j)
    have he := congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
      (CoefficientMinor.minor_apply (F.source.left (pairFst q)) (F.source.right (pairFst q)) _ _ _ _
        (F.source.order_left _) (F.source.order_right _) (F.coefficient_le _) i j)
    refine Eq.trans ?_ he.symm
    refine Eq.trans ?_ h
    apply congrArg (SylvesterBits.entry a.source.bits.base)
    simp only [query, row, PrincipalMinorBits.Bits.row,
      PrincipalMinorBits.Bits.col, PrincipalMinorBits.Bits.leftWidth, SylvesterBits.context,
      SylvesterBits.row, SylvesterBits.col, pairFst_pair, pairSnd_pair, a.coefficient_eq,
      a.source.order_eq, a.source.leftDegree_eq, BinaryNat.add_pair, BinaryNat.sub_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, CoefficientMinor.row, PrincipalMinor.col,
      Subresultant.rowIndex, Subresultant.colIndex]
    split_ifs <;> rfl

theorem integer_controls {F : Family} (a : Access F) (ha : a.ControlsPolyTime) :
    a.integer.ControlsPolyTime := by
  have h := a.source.integer_controls ha.source
  exact ⟨h.dimension, h.budget⟩

theorem residueEvaluator {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (P : SpaceFunction a.source.bits.base.leftCoefficient) (Q : SpaceFunction a.source.bits.base.rightCoefficient) :
    SpaceFunction F.integer.modular.value := by
  have E : SpaceFunction a.integer.entry := by simpa only [integer] using entryEvaluator a ha P Q
  exact Berkowitz.ModularAccess.evaluator a.integer.modular (a.integer.modular_controls (integer_controls a ha))
    (a.integer.modularEntry E)

end Access
end LeanCanny.Algebra.CoefficientMinorBits
