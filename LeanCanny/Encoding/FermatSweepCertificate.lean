/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatBoundedSweepSample
public import LeanCanny.Encoding.FermatCriticalDirection
public import LeanCanny.Algebra.ProjectiveRootCharts
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Fixed-length direction and sweep-sample certificates

One block per direction coordinate and one final sweep-value block suffice.
The block width is polynomial in dimension and the binary degree length.
Native field access uses the same coordinates as the geometric certificate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatSweepCertificate
open LeanCanny.Algebra MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def width (n N : ℕ) : ℕ := FermatBoundedCriticalDirection.binaryWidth n N + N.size

theorem sample_lt_two_pow (n N : ℕ) : FermatBoundedSweepSample.sampleAllowance n N < 2 ^ width n N := by
  have he : FermatBoundedSweepSample.sampleAllowance n N = FermatBoundedCriticalDirection.allowance n N * N := by
    simp only [FermatBoundedSweepSample.sampleAllowance, FermatBoundedCriticalDirection.allowance, Nat.mul_assoc]
  rw [he, width, pow_add]
  exact (Nat.mul_le_mul_left _ (Nat.lt_size_self N).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (FermatBoundedCriticalDirection.allowance_lt_two_pow n N) (by positivity))

theorem width_unary {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hN : BinaryFn degree) :
    UnaryFn (fun c => width (dim c) (degree c)) :=
  (FermatCriticalDirection.binaryWidth_unary hd hN).add
    ((UnaryFn.length hN.bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode (degree c)))

theorem recordLength_unary {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hN : BinaryFn degree) :
    UnaryFn (fun c => (dim c + 1) * width (dim c) (degree c)) :=
  (hd.add (UnaryFn.const 1)).mul (width_unary hd hN)

def read (dim degree : List Bool → ℕ) : List Bool → List Bool :=
  FixedWidthQuery.read ((fun c => dim c + 1) ∘ pairFst)
    ((fun c => width (dim c) (degree c)) ∘ pairFst) pairSnd

theorem read_mem_FP {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hN : BinaryFn degree) :
    read dim degree ∈ FP := FixedWidthQuery.read_mem_FP
  ((hd.add (UnaryFn.const 1)).comp pairFst_mem_FP) ((width_unary hd hN).comp pairFst_mem_FP) pairSnd_mem_FP

def assignment (n N : ℕ) (record : List Bool) (i : Fin (n + 1)) : ℕ :=
  FixedWidthQuery.coordinate (fun _ => width n N) id record i.val

def direction (n N : ℕ) (record : List Bool) (i : Fin n) : ℕ := assignment n N record i.castSucc
def sample (n N : ℕ) (record : List Bool) : ℕ := assignment n N record (Fin.last n)

theorem read_packet (dim degree : List Bool → ℕ) (c record : List Bool) (i : ℕ) (hi : i < dim c + 1) :
    read dim degree (pair (pair c record) (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (assignment (dim c) (degree c) record ⟨i, hi⟩) := by
  simp only [read, FixedWidthQuery.read_packet, Function.comp_apply, pairFst_pair,
    FixedWidthQuery.entry, hi, ite_true]
  simp only [assignment, FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, pairSnd_pair, id_eq]

universe u

theorem exists_record {n : ℕ} {K : Type u} [Field K] [CharZero K]
    (low : MvPolynomial (Fin (n + 2)) K) (a : K) (ha : a ≠ 0) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N)
    (hregular : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 2) → L),
      aeval x (FermatCriticalHomogenization.polynomial low a N) = 0 →
        ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial low a N)) ≠ 0) :
    ∃ record : List Bool, record.length = (n + 1) * width n N ∧
      ∀ (L : Type*) [Field L] [Algebra K L] (y : Fin (n + 2) → L),
        (∀ j, (FermatBoundedSweepSample.rows low a N (direction n N record) j).eval₂
          (Polynomial.eval₂RingHom (algebraMap K L) (sample n N record : L)) y = 0) → y = 0 := by
  obtain ⟨v, hv, t, ht, hgood⟩ := FermatBoundedSweepSample.exists_bounded low a ha N hlow hN hregular
  let f : Fin (n + 1) → ℕ := Fin.lastCases t v
  have hfit (i : Fin (n + 1)) : f i < 2 ^ width n N := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [f, Fin.lastCases_last] using ht.trans_lt (sample_lt_two_pow n N)
    · have hw : FermatBoundedCriticalDirection.binaryWidth n N ≤ width n N := Nat.le_add_right _ _
      simpa only [f, Fin.lastCases_castSucc] using
        ((hv i).trans_lt (FermatBoundedCriticalDirection.allowance_lt_two_pow n N)).trans_le
          (Nat.pow_le_pow_right (by decide) hw)
  let record := FixedWidthNatVector.encode (n + 1) (width n N)
    (fun i => if hi : i < n + 1 then f ⟨i, hi⟩ else 0)
  have he : assignment n N record = f := by
    funext i
    change Nat.fromBitsLE ((record.drop (i.val * width n N)).take (width n N)) = f i
    simpa only [dite_eq_left i.isLt] using FixedWidthNatVector.decode_block (n + 1) (width n N)
      (fun j => if hj : j < n + 1 then f ⟨j, hj⟩ else 0) i.val i.isLt
      (by simpa only [dite_eq_left i.isLt] using hfit i)
  refine ⟨record, FixedWidthNatVector.length_encode _ _ _, ?_⟩
  have hdir : direction n N record = v := by
    funext i
    simp only [direction, he, f, Fin.lastCases_castSucc]
  have ht' : sample n N record = t := by simp only [sample, he, f, Fin.lastCases_last]
  rw [hdir, ht']
  exact hgood

/-- The certificate check only asks about the one sampled complex fiber. -/
def Valid {n : ℕ} (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ) (N : ℕ) (record : List Bool) : Prop :=
  ∀ y : Fin (n + 2) → ℂ,
    (∀ j, (FermatBoundedSweepSample.rows low a N (direction n N record) j).eval₂
      (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) (sample n N record : ℂ)) y = 0) → y = 0

theorem exists_valid_record {n : ℕ} (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ) (ha : a ≠ 0) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N)
    (hregular : ∀ (L : Type) [Field L] [Algebra ℚ L] (x : Fin (n + 2) → L),
      aeval x (FermatCriticalHomogenization.polynomial low a N) = 0 →
        ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial low a N)) ≠ 0) :
    ∃ record : List Bool, record.length = (n + 1) * width n N ∧ Valid low a N record := by
  obtain ⟨record, hr, hgood⟩ := exists_record low a ha N hlow hN hregular
  exact ⟨record, hr, hgood ℂ⟩

theorem valid_iff_charts {n : ℕ} (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ) (N : ℕ) (record : List Bool) :
    Valid low a N record ↔ ∀ i : Fin (n + 2), ¬ ∃ y : Fin (n + 2) → ℂ, y i = 1 ∧
      ∀ j, (FermatBoundedSweepSample.rows low a N (direction n N record) j).eval₂
        (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) (sample n N record : ℂ)) y = 0 :=
  ProjectiveRootCharts.root_free_iff_charts _ (FermatCriticalBadSystem.nativeDegrees n N)
    (FermatCriticalBadSpecialization.homogeneous _ _ _ _) _

theorem valid_regular {n : ℕ} {L : Type*} [Field L]
    [Algebra (FermatGenericSliceDirection.GenericField ℚ) L]
    (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ) (N : ℕ) (hlow : low.totalDegree < N)
    (hN : 1 < N) (record : List Bool) (hvalid : Valid low a N record) (x : Fin (n + 1) → L)
    (hx : ∀ j, (FermatCriticalBadSystem.equations (FermatGenericSliceDirection.lower low a N)
      (algebraMap ℚ (FermatGenericSliceDirection.GenericField ℚ) a) N j).eval₂
        (eval₂Hom (algebraMap (FermatGenericSliceDirection.GenericField ℚ) L)
          (fun i => (direction n N record i : L))) x = 0) :
    (FermatCriticalBadSystem.jacobian (FermatGenericSliceDirection.lower low a N)
      (algebraMap ℚ (FermatGenericSliceDirection.GenericField ℚ) a) N).eval₂
        (eval₂Hom (algebraMap (FermatGenericSliceDirection.GenericField ℚ) L)
          (fun i => (direction n N record i : L))) x ≠ 0 := by
  have h := FermatBoundedSweepSample.regular_of_sample low a N hlow hN (direction n N record)
    (sample n N record) hvalid x
  simp only [eq_ratCast] at h hx ⊢
  exact h hx

end LeanCanny.Encoding.FermatSweepCertificate
