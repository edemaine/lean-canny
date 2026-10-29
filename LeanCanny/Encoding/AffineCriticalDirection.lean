/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCriticalCommonDirection
public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Encoding.PositiveAffineRecord
public import LeanCanny.Encoding.FlatAffineFullSourceTower
public import LeanCanny.Geometry.RegularAffineSubsetCount
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Short native records for affine critical directions

Unary dimension, binary source degree, and a unary family-count bit bound
supply a unary record length. The same total polynomial-time coordinate
reader decodes the integer objective used in the geometric specification.
Actual regular affine parent roots have a count bound derived from source
dimension, degree, and depth, independent of old direction magnitudes.
Selecting a good record remains separate.
-/

@[expose] public section
namespace LeanCanny.Encoding.AffineCriticalDirection
open LeanCanny.Algebra MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u

theorem singleWidth_unary {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hD : BinaryFn degree) :
    UnaryFn (fun c => Algebra.AffineCriticalBoundedDirection.binaryWidth (dim c) (degree c)) := by
  have hsD : UnaryFn (fun c => (degree c).size) :=
    (UnaryFn.length hD.bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode (degree c))
  have hE := ((UnaryFn.const 2).mul hd).add (UnaryFn.const 1)
  have hsE : UnaryFn (fun c => (2 * dim c + 1).size) :=
    (UnaryFn.length (BinaryFn.ofUnary hE).bits_mem_FP).of_eq
      (fun c => BinaryNatCode.length_encode (2 * dim c + 1))
  have hW := (((UnaryFn.const 4).mul hd).add hsD).add (UnaryFn.const 5)
  exact ((((UnaryFn.const 2).mul hd).add (UnaryFn.const 2)).mul hW |>.add hsE).of_eq (fun _ => rfl)

theorem binaryWidth_unary {dim degree countBits : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : UnaryFn countBits) :
    UnaryFn (fun c => Algebra.AffineCriticalCommonDirection.binaryWidth (dim c) (degree c) (countBits c)) :=
  hb.add (singleWidth_unary hd hD)

theorem recordLength_unary {dim degree countBits : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : UnaryFn countBits) :
    UnaryFn (fun c => dim c * Algebra.AffineCriticalCommonDirection.binaryWidth (dim c) (degree c) (countBits c)) :=
  hd.mul (binaryWidth_unary hd hD hb)

def read (dim degree countBits : List Bool → ℕ) : List Bool → List Bool :=
  FixedWidthQuery.read (dim ∘ pairFst)
    ((fun c => Algebra.AffineCriticalCommonDirection.binaryWidth (dim c) (degree c) (countBits c)) ∘ pairFst) pairSnd

theorem read_FP {dim degree countBits : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : UnaryFn countBits) : read dim degree countBits ∈ FP :=
  FixedWidthQuery.read_mem_FP (hd.comp pairFst_mem_FP)
    ((binaryWidth_unary hd hD hb).comp pairFst_mem_FP) pairSnd_mem_FP

def assignment (n D countBits : ℕ) (record : List Bool) (i : Fin n) : ℕ :=
  FixedWidthQuery.coordinate (fun _ => Algebra.AffineCriticalCommonDirection.binaryWidth n D countBits) id record i.val

theorem assignment_lt (n D countBits : ℕ) (record : List Bool) (i : Fin n) :
    assignment n D countBits record i < 2 ^ Algebra.AffineCriticalCommonDirection.binaryWidth n D countBits := by
  exact (Nat.fromBitsLE_lt_pow_length _).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

theorem read_packet (dim degree countBits : List Bool → ℕ) (c record : List Bool)
    (i : ℕ) (hi : i < dim c) :
    read dim degree countBits (pair (pair c record) (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (assignment (dim c) (degree c) (countBits c) record ⟨i, hi⟩) := by
  simp only [read, FixedWidthQuery.read_packet, Function.comp_apply, pairFst_pair,
    FixedWidthQuery.entry, hi, ite_true]
  simp only [assignment, FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, pairSnd_pair, id_eq]


def signedRecord (n D countBits : ℕ) (record : List Bool) : List Bool :=
  PositiveAffineRecord.encode n (Algebra.AffineCriticalCommonDirection.binaryWidth n D countBits) record

theorem signedRecord_length (n D countBits : ℕ) (record : List Bool) :
    (signedRecord n D countBits record).length =
      n * (2 * Algebra.AffineCriticalCommonDirection.binaryWidth n D countBits) :=
  PositiveAffineRecord.length_encode _ _ _

/-- The actual signed tower decoder returns the bounded objective unchanged. -/
theorem signed_assignment (n D countBits : ℕ) (record : List Bool) (i : Fin n) :
    FlatAffineFullSourceTower.integer (Algebra.AffineCriticalCommonDirection.binaryWidth n D countBits)
      (signedRecord n D countBits record) i.val = (assignment n D countBits record i : ℤ) :=
  PositiveAffineRecord.integer_encode _ _ _ i.val i.isLt

theorem signed_assignment_cast {R : Type*} [Ring R] (n D countBits : ℕ) (record : List Bool) (i : Fin n) :
    (FlatAffineFullSourceTower.integer (Algebra.AffineCriticalCommonDirection.binaryWidth n D countBits)
      (signedRecord n D countBits record) i.val : R) = (assignment n D countBits record i : R) := by
  rw [signed_assignment, Int.cast_natCast]

theorem signedRecord_FP {dim degree countBits : List Bool → ℕ}
    (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : UnaryFn countBits) :
    (fun q => signedRecord (dim (pairFst q)) (degree (pairFst q)) (countBits (pairFst q)) (pairSnd q)) ∈ FP :=
  PositiveAffineRecord.encode_FP (hd.comp pairFst_mem_FP)
    ((binaryWidth_unary hd hD hb).comp pairFst_mem_FP) pairSnd_mem_FP


theorem exists_record {K : Type u} [Field K] [CharZero K] {n : ℕ} {σ : Type*} [Fintype σ]
    (low H : σ → MvPolynomial (Fin n) K) (D : ℕ) (hlow : ∀ t, (low t).totalDegree < D)
    (hH : ∀ t, (H t).IsHomogeneous D) (hD : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : σ → Fin n → Fin n → K) (β : σ → Fin n → K)
    (hcone : ∀ t, ∀ (L : Type u) [Field L] [Algebra K L], AffineConeFlag.Transverse (L := L) (H t) s (A t))
    (hslice : ∀ t, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin n → L), aeval x (low t + H t) = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A t r i) * x i = algebraMap K L (β t r)) →
      GenericAffineCriticalJacobian.ConstraintIndependent (low t + H t) s (A t) x)
    (countBits : ℕ) (hcount : Fintype.card σ ≤ 2 ^ countBits) :
    ∃ record : List Bool,
      record.length = n * Algebra.AffineCriticalCommonDirection.binaryWidth n D countBits ∧
      ∀ t, ∀ (L : Type u) [Field L] [Algebra K L],
        AffineCriticalDirectionGeometry.CriticalRegular (low t + H t) s (A t) (β t)
          (fun i => (assignment n D countBits record i : L)) ∧
        AffineConeDirectionGeometry.CriticalRootFree (H t) s (A t)
          (fun i => (assignment n D countBits record i : L)) := by
  obtain ⟨v, hv, hg⟩ := Algebra.AffineCriticalCommonDirection.exists_common low H D hlow hH hD s hs A β hcone hslice countBits hcount
  let W := Algebra.AffineCriticalCommonDirection.binaryWidth n D countBits
  let record := FixedWidthNatVector.encode n W (fun i => if hi : i < n then v ⟨i, hi⟩ else 0)
  have he : assignment n D countBits record = v := by
    funext i
    change Nat.fromBitsLE ((record.drop (i.val * W)).take W) = v i
    simpa only [dite_eq_left i.isLt] using FixedWidthNatVector.decode_block n W
      (fun j => if hj : j < n then v ⟨j, hj⟩ else 0) i.val i.isLt
      (by simpa only [dite_eq_left i.isLt] using hv i)
  refine ⟨record, FixedWidthNatVector.length_encode _ _ _, ?_⟩
  rw [he]
  exact hg

abbrev Parents (F : FlatAffineFullSourceTower.Inputs) (c : List Bool) :=
  Geometry.RegularAffineRootCount.RegularRoots (FlatAffineFullSourceTower.system F c)

noncomputable def parentCountBits (F : FlatAffineFullSourceTower.Inputs) (c : List Bool) : ℕ :=
  Geometry.RegularAffineRootCount.labelWidth (FlatAffineFullSourceTower.count F c) (FlatAffineFullSourceTower.degree F c)

theorem parentCountBits_congr (F G : FlatAffineFullSourceTower.Inputs)
    (hS : F.source = G.source) (hk : F.depth = G.depth) : parentCountBits F = parentCountBits G := by
  funext c
  simp only [parentCountBits, FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth,
    FlatAffineFullSourceTower.arity, FlatAffineFullSourceTower.degree, hS, hk]

theorem finite_parents (F : FlatAffineFullSourceTower.Inputs) (c : List Bool) :
    Finite (Parents F c) ∧ Nat.card (Parents F c) ≤ 2 ^ parentCountBits F c :=
  Geometry.RegularAffineRootCount.finite_regular_card_le_uniform (FlatAffineFullSourceTower.system F c)
    (FlatAffineFullSourceTower.degree F c) (FlatAffineFullSourceTower.polynomial_degree F c)
    (FlatAffineFullSourceTower.degree_pos F c)

/-- The count budget uses only original-source controls and recursion depth. -/
theorem parentCountBits_unary {F : FlatAffineFullSourceTower.Inputs}
    (hS : F.source.PolyTime) (hk : UnaryFn F.depth) : UnaryFn (parentCountBits F) := by
  have ha := hS.dim.add (UnaryFn.const 4)
  have hm : UnaryFn (FlatAffineFullSourceTower.count F) :=
    (hk.mul (ha.add (ha.add (UnaryFn.const 1)))).of_eq (fun _ => rfl)
  have hD : BinaryFn (FlatAffineFullSourceTower.degree F) :=
    ((BoundedFullWriter.degree_binary hS).add (BinaryFn.const 1)).of_eq (fun _ => rfl)
  have hi := ((BinaryFn.ofUnary hm).mul (hD.sub (BinaryFn.const 1))).add (BinaryFn.const 1)
  have hsz : UnaryFn (fun c => (FlatAffineFullSourceTower.count F c *
      (FlatAffineFullSourceTower.degree F c - 1) + 1).size) :=
    (UnaryFn.length hi.bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode _)
  exact ((hm.mul (hm.add (UnaryFn.const 1))).mul hsz).of_eq (fun _ => rfl)

/-- The family-count charge comes from the actual regular parent tower,
without a supplied parent enumeration or an independent count allowance. -/
theorem exists_parent_record {K : Type u} [Field K] [CharZero K]
    (F : FlatAffineFullSourceTower.Inputs) (c : List Bool)
    (low H : Parents F c →
      MvPolynomial (Fin (FlatAffineFullSourceTower.arity F c)) K)
    (D : ℕ) (hlow : ∀ t, (low t).totalDegree < D) (hH : ∀ t, (H t).IsHomogeneous D) (hD : 1 < D)
    (s : Finset (Fin (FlatAffineFullSourceTower.arity F c))) (hs : s.card < FlatAffineFullSourceTower.arity F c)
    (A : Parents F c → Fin (FlatAffineFullSourceTower.arity F c) →
      Fin (FlatAffineFullSourceTower.arity F c) → K)
    (β : Parents F c → Fin (FlatAffineFullSourceTower.arity F c) → K)
    (hcone : ∀ t, ∀ (L : Type u) [Field L] [Algebra K L], AffineConeFlag.Transverse (L := L) (H t) s (A t))
    (hslice : ∀ t, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (FlatAffineFullSourceTower.arity F c) → L),
      aeval x (low t + H t) = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A t r i) * x i = algebraMap K L (β t r)) →
      GenericAffineCriticalJacobian.ConstraintIndependent (low t + H t) s (A t) x) :
    ∃ record : List Bool,
      record.length = FlatAffineFullSourceTower.arity F c * Algebra.AffineCriticalCommonDirection.binaryWidth
        (FlatAffineFullSourceTower.arity F c) D (parentCountBits F c) ∧
      ∀ t, ∀ (L : Type u) [Field L] [Algebra K L],
        AffineCriticalDirectionGeometry.CriticalRegular (low t + H t) s (A t) (β t)
          (fun i => (assignment (FlatAffineFullSourceTower.arity F c) D (parentCountBits F c) record i : L)) ∧
        AffineConeDirectionGeometry.CriticalRootFree (H t) s (A t)
          (fun i => (assignment (FlatAffineFullSourceTower.arity F c) D (parentCountBits F c) record i : L)) := by
  let _ : Finite (Parents F c) := (finite_parents F c).1
  let _ := Fintype.ofFinite (Parents F c)
  have hc : Fintype.card (Parents F c) ≤ 2 ^ parentCountBits F c := by
    simpa only [Nat.card_eq_fintype_card] using (finite_parents F c).2
  exact exists_record low H D hlow hH hD s hs A β hcone hslice (parentCountBits F c) hc

theorem parent_recordLength_unary {F : FlatAffineFullSourceTower.Inputs}
    (hS : F.source.PolyTime) (hk : UnaryFn F.depth) {degree : List Bool → ℕ} (hD : BinaryFn degree) :
    UnaryFn (fun c => FlatAffineFullSourceTower.arity F c * Algebra.AffineCriticalCommonDirection.binaryWidth
      (FlatAffineFullSourceTower.arity F c) (degree c) (parentCountBits F c)) :=
  recordLength_unary ((hS.dim.add (UnaryFn.const 4)).of_eq (fun _ => rfl)) hD (parentCountBits_unary hS hk)

end LeanCanny.Encoding.AffineCriticalDirection
