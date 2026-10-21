/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalMinor
public import LeanCanny.Algebra.BerkowitzResidueSpace
public import LeanCanny.Algebra.IntegerDeterminantSpaceEntries
public import LeanCanny.Algebra.SylvesterSpaceAccess
public import LeanCanny.Algebra.IntegerSignumSpace

/-! # Uniform residues and signs of integer principal minors

The order may equal either degree bound. FP index arithmetic embeds the minor
in the original Sylvester matrix; both original coefficient readers may use
polynomial space. The determinant and CRT sign routines retain their costs.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalMinorBits
open Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower

structure Bits where
  base : SylvesterBits.Access
  order : List Bool → List Bool

structure Bits.ControlsPolyTime (a : Bits) : Prop where
  base : a.base.ControlsPolyTime
  order : a.order ∈ FP

namespace Bits

def leftWidth (a : Bits) (c : List Bool) : List Bool :=
  BinaryNat.sub (pair (a.base.leftDegree c) (a.order c))
def rightWidth (a : Bits) (c : List Bool) : List Bool :=
  BinaryNat.sub (pair (a.base.rightDegree c) (a.order c))
def dimension (a : Bits) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (a.leftWidth c) (a.rightWidth c))
def row (a : Bits) (p : List Bool) : List Bool :=
  BinaryNat.add (pair (a.order (SylvesterBits.context p)) (SylvesterBits.row p))
def col (a : Bits) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (SylvesterBits.col p) < Nat.fromBitsLE (a.leftWidth (SylvesterBits.context p))
  then SylvesterBits.col p
  else BinaryNat.add (pair (SylvesterBits.col p) (a.order (SylvesterBits.context p)))
def query (a : Bits) (p : List Bool) : List Bool := pair (pairFst p) (pair (a.row p) (a.col p))
def entry (a : Bits) : List Bool → List Bool := SylvesterBits.entry a.base ∘ a.query

theorem leftWidth_mem_FP (a : Bits) (ha : a.ControlsPolyTime) : a.leftWidth ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.base.leftDegree ha.order) BinaryNat.sub_mem_FP
  refine mem_FP_of_eq (g := a.leftWidth) h ?_
  intro c
  simp only [leftWidth, Function.comp_apply]
theorem rightWidth_mem_FP (a : Bits) (ha : a.ControlsPolyTime) : a.rightWidth ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.base.rightDegree ha.order) BinaryNat.sub_mem_FP
  refine mem_FP_of_eq (g := a.rightWidth) h ?_
  intro c
  simp only [rightWidth, Function.comp_apply]
theorem dimension_mem_FP (a : Bits) (ha : a.ControlsPolyTime) : a.dimension ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (a.leftWidth_mem_FP ha) (a.rightWidth_mem_FP ha)) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := a.dimension) h ?_
  intro c
  simp only [dimension, Function.comp_apply]
theorem row_mem_FP (a : Bits) (ha : a.ControlsPolyTime) : a.row ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp SylvesterBits.context_mem_FP ha.order)
    SylvesterBits.row_mem_FP) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := a.row) h ?_
  intro p
  simp only [row, Function.comp_apply]
theorem col_mem_FP (a : Bits) (ha : a.ControlsPolyTime) : a.col ∈ FP := by
  have hw := mem_FP_comp SylvesterBits.context_mem_FP (a.leftWidth_mem_FP ha)
  have hk := mem_FP_comp SylvesterBits.context_mem_FP ha.order
  have hs := mem_FP_comp (mem_FP_pair SylvesterBits.col_mem_FP hk) BinaryNat.add_mem_FP
  have h := (BinaryNat.lt_fppred SylvesterBits.col_mem_FP hw).ite_mem_FP SylvesterBits.col_mem_FP hs
  refine mem_FP_of_eq (g := a.col) h ?_
  intro p
  simp only [col, Function.comp_apply]
theorem query_mem_FP (a : Bits) (ha : a.ControlsPolyTime) : a.query ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (a.row_mem_FP ha) (a.col_mem_FP ha))

theorem entryEvaluator (a : Bits) (ha : a.ControlsPolyTime)
    (P : SpaceFunction a.base.leftCoefficient) (Q : SpaceFunction a.base.rightCoefficient) :
    SpaceFunction a.entry :=
  (SylvesterBits.entryEvaluator a.base ha.base P Q).precompose a.query (a.query_mem_FP ha)

theorem entry_correct {R : Type*} [Semiring R] (a : Bits) (q : List Bool)
    (p f : R[X]) (m n k : ℕ) (hm : k ≤ m) (hn : k ≤ n) (enc : R → List Bool)
    (hc : SylvesterBits.CorrectAt a.base q p f m n enc)
    (hk : a.order (pairFst q) = BinaryNatCode.encode k)
    (i j : Fin ((m - k) + (n - k))) :
    a.entry (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      enc (Subresultant.minor p f m n k k i j) := by
  have h := SylvesterBits.entry_correct a.base q p f m n enc hc
    (PrincipalMinor.row m n k hm hn i) (PrincipalMinor.col m n k hm hn j)
  rw [PrincipalMinor.minor_eq_submatrix p f m n k hm hn, Matrix.submatrix_apply]
  convert h using 1
  simp only [entry, Function.comp_apply, query, row, col, leftWidth, SylvesterBits.context,
    SylvesterBits.row, SylvesterBits.col, pairFst_pair, pairSnd_pair, hk, hc.leftDegree,
    BinaryNat.add_pair, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    PrincipalMinor.row, PrincipalMinor.col, Subresultant.colIndex]
  split_ifs <;> rfl

end Bits

structure Family where
  left : List Bool → ℤ[X]
  right : List Bool → ℤ[X]
  leftDegree : List Bool → ℕ
  rightDegree : List Bool → ℕ
  order : List Bool → ℕ
  coefficientBits : List Bool → ℕ
  order_left : ∀ c, order c ≤ leftDegree c
  order_right : ∀ c, order c ≤ rightDegree c
  left_bound : ∀ c i, ((left c).coeff i).natAbs ≤ 2 ^ coefficientBits c
  right_bound : ∀ c i, ((right c).coeff i).natAbs ≤ 2 ^ coefficientBits c

def Family.integer (F : Family) : Berkowitz.IntegerFamily where
  dimension c := (F.leftDegree c - F.order c) + (F.rightDegree c - F.order c)
  matrix c := Subresultant.minor (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c) (F.order c) (F.order c)
  budget c := (F.leftDegree c + F.rightDegree c).size * (F.leftDegree c + F.rightDegree c) +
    (F.leftDegree c + F.rightDegree c) * F.coefficientBits c + 1
  determinant_bits c := by
    have h := (Subresultant.minor_det_size_le (F.left c) (F.right c)
      (F.leftDegree c) (F.rightDegree c) (F.order c) (F.order c) _ _
      (F.left_bound c) (F.right_bound c)).trans (Subresultant.budget_le_full _ _ _ _ _)
    simpa only [Nat.add_mul, Nat.add_assoc] using h

structure Access (F : Family) where
  bits : Bits
  leftDegree_eq : ∀ c, bits.base.leftDegree c = BinaryNatCode.encode (F.leftDegree c)
  rightDegree_eq : ∀ c, bits.base.rightDegree c = BinaryNatCode.encode (F.rightDegree c)
  order_eq : ∀ c, bits.order c = BinaryNatCode.encode (F.order c)
  coefficientBits_eq : ∀ c, bits.base.coefficientBits c = BinaryNatCode.encode (F.coefficientBits c)
  left_eq : ∀ q i, bits.base.leftCoefficient (pair q (BinaryNatCode.encode i)) =
    residueBits (((F.left (pairFst q)).coeff i : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))
  right_eq : ∀ q i, bits.base.rightCoefficient (pair q (BinaryNatCode.encode i)) =
    residueBits (((F.right (pairFst q)).coeff i : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))

namespace Access

def integer {F : Family} (a : Access F) : Berkowitz.IntegerAccess F.integer where
  dimension := a.bits.dimension
  budget := SylvesterBits.budget a.bits.base
  entry := a.bits.entry
  dimension_eq c := by
    simp only [Bits.dimension, Bits.leftWidth, Bits.rightWidth, a.leftDegree_eq, a.rightDegree_eq,
      a.order_eq, BinaryNat.sub_pair, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Family.integer]
  budget_eq c := SylvesterBits.budget_code _ c _ _ _
    (a.leftDegree_eq c) (a.rightDegree_eq c) (a.coefficientBits_eq c)
  entry_eq := by
    intro q i j
    change a.bits.entry _ = residueBits
      ((Subresultant.minor (F.left (pairFst q)) (F.right (pairFst q)) (F.leftDegree (pairFst q))
        (F.rightDegree (pairFst q)) (F.order (pairFst q)) (F.order (pairFst q)) i j : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q) + 1))
    exact a.bits.entry_correct q (F.left (pairFst q)) (F.right (pairFst q)) _ _ _
      (F.order_left _) (F.order_right _)
      (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
      ⟨a.leftDegree_eq _, a.rightDegree_eq _, a.left_eq q, a.right_eq q,
        by simp [residueBits, BinaryNatCode.encode]⟩ (a.order_eq _) i j

theorem integer_controls {F : Family} (a : Access F) (ha : a.bits.ControlsPolyTime) :
    a.integer.ControlsPolyTime := by
  constructor
  · simpa only [integer] using a.bits.dimension_mem_FP ha
  · simpa only [integer] using SylvesterBits.budget_mem_FP_of_controls a.bits.base ha.base

theorem residueEvaluator {F : Family} (a : Access F) (ha : a.bits.ControlsPolyTime)
    (P : SpaceFunction a.bits.base.leftCoefficient) (Q : SpaceFunction a.bits.base.rightCoefficient) :
    SpaceFunction F.integer.modular.value := by
  have E : SpaceFunction a.integer.entry := by
    simpa only [integer] using a.bits.entryEvaluator ha P Q
  exact Berkowitz.ModularAccess.evaluator a.integer.modular (a.integer.modular_controls (a.integer_controls ha))
    (a.integer.modularEntry E)

end Access
end LeanCanny.Algebra.PrincipalMinorBits
