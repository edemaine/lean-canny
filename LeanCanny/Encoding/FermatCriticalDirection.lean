/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatBoundedCriticalDirection
public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Algebra.FixedWidthPolynomialFP
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Bounded records for integer critical directions

The direction block width is polynomial in dimension and source degree bit
length. A source degree supplied in binary gives a unary width certificate.
The native field reader is total, with a zero result outside the dimension.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatCriticalDirection
open LeanCanny.Algebra FermatBoundedCriticalDirection MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

theorem binaryWidth_unary {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hN : BinaryFn degree) :
    UnaryFn (fun c => binaryWidth (dim c) (degree c)) := by
  have hs : UnaryFn (fun c => (degree c).size) :=
    (UnaryFn.length hN.bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode (degree c))
  have h := (((hd.add (UnaryFn.const 2)).mul
    ((((UnaryFn.const 2).mul hd).add hs).add (UnaryFn.const 4))).add hd).add (UnaryFn.const 1)
  exact h.of_eq (fun _ => rfl)

theorem recordLength_unary {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hN : BinaryFn degree) :
    UnaryFn (fun c => dim c * binaryWidth (dim c) (degree c)) :=
  hd.mul (binaryWidth_unary hd hN)

def read (dim degree : List Bool → ℕ) : List Bool → List Bool :=
  FixedWidthQuery.read (dim ∘ pairFst)
    ((fun c => binaryWidth (dim c) (degree c)) ∘ pairFst) pairSnd

theorem read_mem_FP {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hN : BinaryFn degree) :
    read dim degree ∈ FP :=
  FixedWidthQuery.read_mem_FP (hd.comp pairFst_mem_FP)
    ((binaryWidth_unary hd hN).comp pairFst_mem_FP) pairSnd_mem_FP

def assignment (n N : ℕ) (record : List Bool) (i : Fin n) : ℕ :=
  FixedWidthQuery.coordinate (fun _ => binaryWidth n N) id record i.val

theorem read_packet (dim degree : List Bool → ℕ) (c record : List Bool) (i : ℕ) (hi : i < dim c) :
    read dim degree (pair (pair c record) (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (assignment (dim c) (degree c) record ⟨i, hi⟩) := by
  simp only [read, FixedWidthQuery.read_packet, Function.comp_apply, pairFst_pair,
    FixedWidthQuery.entry, hi, ite_true]
  simp only [assignment, FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, pairSnd_pair, id_eq]

/-- A suitable direction has an actual fixed-length binary record. The
geometric specification uses the values returned by the same native reader. -/
theorem exists_record {n : ℕ} {K : Type u} [Field K] [CharZero K]
    (low : MvPolynomial (Fin (n + 1)) K) (a : K) (ha : a ≠ 0) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N)
    (hregular : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
      aeval x (FermatCriticalHomogenization.polynomial low a N) = 0 →
        ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial low a N)) ≠ 0) :
    ∃ record : List Bool, record.length = n * binaryWidth n N ∧
      ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
        (∀ j, (FermatCriticalBadSystem.equations low a N j).eval₂
          (eval₂Hom (algebraMap K L) (fun i => (assignment n N record i : L))) x = 0) →
        (FermatCriticalBadSystem.jacobian low a N).eval₂
          (eval₂Hom (algebraMap K L) (fun i => (assignment n N record i : L))) x ≠ 0 := by
  obtain ⟨v, hv, hgood⟩ := FermatBoundedCriticalDirection.exists_bounded low a ha N hlow hN hregular
  let record := FixedWidthNatVector.encode n (binaryWidth n N) (fun i => if hi : i < n then v ⟨i, hi⟩ else 0)
  have he : assignment n N record = v := by
    funext i
    change Nat.fromBitsLE ((record.drop (i.val * binaryWidth n N)).take (binaryWidth n N)) = v i
    have hfit : v i < 2 ^ binaryWidth n N := (hv i).trans_lt (allowance_lt_two_pow n N)
    simpa only [dite_eq_left i.isLt] using FixedWidthNatVector.decode_block n (binaryWidth n N)
      (fun j => if hj : j < n then v ⟨j, hj⟩ else 0) i.val i.isLt
      (by simpa only [dite_eq_left i.isLt] using hfit)
  refine ⟨record, FixedWidthNatVector.length_encode _ _ _, ?_⟩
  rw [he]
  exact hgood

end LeanCanny.Encoding.FermatCriticalDirection
