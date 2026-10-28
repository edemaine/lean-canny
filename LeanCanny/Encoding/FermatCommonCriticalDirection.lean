/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCommonCriticalDirection
public import LeanCanny.Encoding.FermatCriticalDirection
public import LeanCanny.Encoding.BoundedFullCriticalSamples

/-! # Short common-direction records for actual-parent families

The existing parent sample-count allowance bounds the number of conditions.
Its bit width is added to the single-source direction width. Native readers
decode the resulting record, whose existence makes all eligible parent
systems regular at once. Pure-power shape and regularity over coefficient
field extensions remain explicit geometric premises.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatCommonCriticalDirection
open LeanCanny.Algebra MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

theorem binaryWidth_unary {dim degree countBits : List Bool → ℕ}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hb : UnaryFn countBits) :
    UnaryFn (fun c => Algebra.FermatCommonCriticalDirection.binaryWidth (dim c) (degree c) (countBits c)) :=
  hb.add (FermatCriticalDirection.binaryWidth_unary hd hN)

theorem recordLength_unary {dim degree countBits : List Bool → ℕ}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hb : UnaryFn countBits) :
    UnaryFn (fun c => dim c * Algebra.FermatCommonCriticalDirection.binaryWidth (dim c) (degree c) (countBits c)) :=
  hd.mul (binaryWidth_unary hd hN hb)

def read (dim degree countBits : List Bool → ℕ) : List Bool → List Bool :=
  FixedWidthQuery.read (dim ∘ pairFst)
    ((fun c => Algebra.FermatCommonCriticalDirection.binaryWidth (dim c) (degree c) (countBits c)) ∘ pairFst) pairSnd

theorem read_FP {dim degree countBits : List Bool → ℕ}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hb : UnaryFn countBits) : read dim degree countBits ∈ FP :=
  FixedWidthQuery.read_mem_FP (hd.comp pairFst_mem_FP)
    ((binaryWidth_unary hd hN hb).comp pairFst_mem_FP) pairSnd_mem_FP

def assignment (n N countBits : ℕ) (record : List Bool) (i : Fin n) : ℕ :=
  FixedWidthQuery.coordinate (fun _ => Algebra.FermatCommonCriticalDirection.binaryWidth n N countBits) id record i.val

theorem read_packet (dim degree countBits : List Bool → ℕ) (c record : List Bool)
    (i : ℕ) (hi : i < dim c) :
    read dim degree countBits (pair (pair c record) (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (assignment (dim c) (degree c) (countBits c) record ⟨i, hi⟩) := by
  simp only [read, FixedWidthQuery.read_packet, Function.comp_apply, pairFst_pair,
    FixedWidthQuery.entry, hi, ite_true]
  simp only [assignment, FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, pairSnd_pair, id_eq]

theorem exists_record {n : ℕ} {K : Type u} [Field K] [CharZero K] {σ : Type*} [Fintype σ]
    (low : σ → MvPolynomial (Fin (n + 1)) K) (a : σ → K) (ha : ∀ s, a s ≠ 0)
    (N countBits : ℕ) (hc : Fintype.card σ ≤ 2 ^ countBits)
    (hlow : ∀ s, (low s).totalDegree < N) (hN : 1 < N)
    (hregular : ∀ s, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
      aeval x (FermatCriticalHomogenization.polynomial (low s) (a s) N) = 0 →
        ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial (low s) (a s) N)) ≠ 0) :
    ∃ record : List Bool,
      record.length = n * Algebra.FermatCommonCriticalDirection.binaryWidth n N countBits ∧
      ∀ s, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
        (∀ j, (FermatCriticalBadSystem.equations (low s) (a s) N j).eval₂
          (eval₂Hom (algebraMap K L) (fun i => (assignment n N countBits record i : L))) x = 0) →
          (FermatCriticalBadSystem.jacobian (low s) (a s) N).eval₂
            (eval₂Hom (algebraMap K L) (fun i => (assignment n N countBits record i : L))) x ≠ 0 := by
  obtain ⟨v, hv, hgood⟩ := Algebra.FermatCommonCriticalDirection.exists_common low a ha N hlow hN hregular
  let W := Algebra.FermatCommonCriticalDirection.binaryWidth n N countBits
  let record := FixedWidthNatVector.encode n W (fun i => if hi : i < n then v ⟨i, hi⟩ else 0)
  have he : assignment n N countBits record = v := by
    funext i
    change Nat.fromBitsLE ((record.drop (i.val * W)).take W) = v i
    have hfit : v i < 2 ^ W := (hv i).trans_lt
      (Algebra.FermatCommonCriticalDirection.allowance_lt_two_pow n N (Fintype.card σ) countBits hc)
    simpa only [dite_eq_left i.isLt] using FixedWidthNatVector.decode_block n W
      (fun j => if hj : j < n then v ⟨j, hj⟩ else 0) i.val i.isLt
      (by simpa only [dite_eq_left i.isLt] using hfit)
  refine ⟨record, FixedWidthNatVector.length_encode _ _ _, ?_⟩
  rw [he]
  exact hgood

theorem exists_parent_record {n : ℕ} {K : Type u} [Field K] [CharZero K]
    (P : BoundedFullWriter.Readers) (c : List Bool)
    (low : BoundedFullCriticalSamples.Samples P c → MvPolynomial (Fin (n + 1)) K)
    (a : BoundedFullCriticalSamples.Samples P c → K) (ha : ∀ p, a p ≠ 0)
    (N : ℕ) (hlow : ∀ p, (low p).totalDegree < N) (hN : 1 < N)
    (hregular : ∀ p, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
      aeval x (FermatCriticalHomogenization.polynomial (low p) (a p) N) = 0 →
        ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial (low p) (a p) N)) ≠ 0) :
    ∃ record : List Bool,
      record.length = n * Algebra.FermatCommonCriticalDirection.binaryWidth n N
        (BoundedFullCriticalSamples.labelWidth P c) ∧
      ∀ p, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
        (∀ j, (FermatCriticalBadSystem.equations (low p) (a p) N j).eval₂
          (eval₂Hom (algebraMap K L) (fun i =>
            (assignment n N (BoundedFullCriticalSamples.labelWidth P c) record i : L))) x = 0) →
          (FermatCriticalBadSystem.jacobian (low p) (a p) N).eval₂
            (eval₂Hom (algebraMap K L) (fun i =>
              (assignment n N (BoundedFullCriticalSamples.labelWidth P c) record i : L))) x ≠ 0 := by
  let : Finite (BoundedFullCriticalSamples.Samples P c) := (BoundedFullCriticalSamples.finite_samples P c).1
  let := Fintype.ofFinite (BoundedFullCriticalSamples.Samples P c)
  have hc : Fintype.card (BoundedFullCriticalSamples.Samples P c) ≤
      2 ^ BoundedFullCriticalSamples.labelWidth P c := by
    simpa only [Nat.card_eq_fintype_card] using (BoundedFullCriticalSamples.finite_samples P c).2
  exact exists_record low a ha N (BoundedFullCriticalSamples.labelWidth P c) hc hlow hN hregular

end LeanCanny.Encoding.FermatCommonCriticalDirection
