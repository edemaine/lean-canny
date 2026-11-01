/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalSubresultant.Basic
public import LeanCanny.Algebra.IntegralBerkowitzBlockSource
public import LeanCanny.Algebra.ModularNatMulFP
public import LeanCanny.Algebra.IntegralActionHeightBounds
public import LeanCanny.Computation.SingleCallController
public import LeanCanny.Computation.ControllerRequests

/-! # Native PSC entries request one actual coordinate coefficient

The derivative block reads coefficient `k+1` and multiplies its residue by
`k+1`. The polynomial block reads coefficient `k`. Formal row/column and
truncation guards return zero on invalid labels. The child preserves the
original source and old basis coordinates, and its requested degree is
at most the original formal coordinate degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.PrincipalDerivativeEntryRequest
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Polynomial PrincipalSubresultant

structure Parameters where
  degree : List Bool → ℕ
  index : List Bool → ℕ
  modulus : List Bool → ℕ

structure Controls (F : Parameters) where
  degree : BinaryFn F.degree
  index : BinaryFn F.index
  modulus : BinaryFn F.modulus

def original := IntegralBerkowitzBlockBits.original
def row (p : List Bool) : ℕ := Nat.fromBitsLE (pairFst (pairSnd p))
def col (p : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairSnd p))
def firstBlock (F : Parameters) (p : List Bool) : ℕ := F.degree (original p) - F.index (original p)
def secondBlock (F : Parameters) (p : List Bool) : ℕ := F.degree (original p) - 1 - F.index (original p)
def derivative (F : Parameters) (p : List Bool) : Prop := col p < firstBlock F p
instance (F : Parameters) (p : List Bool) : Decidable (derivative F p) := inferInstanceAs (Decidable (_ < _))
def localCol (F : Parameters) (p : List Bool) : ℕ := if derivative F p then col p else col p - firstBlock F p
def coefficient (F : Parameters) (p : List Bool) : ℕ :=
  row p + F.index (original p) - localCol F p + if derivative F p then 1 else 0
def multiplier (F : Parameters) (p : List Bool) : ℕ := if derivative F p then coefficient F p else 1
def bound (F : Parameters) (p : List Bool) : ℕ := if derivative F p then F.degree (original p) - 1 else F.degree (original p)
def valid (F : Parameters) (p : List Bool) : Prop :=
  row p < firstBlock F p + secondBlock F p ∧ col p < firstBlock F p + secondBlock F p ∧
    localCol F p ≤ row p + F.index (original p) ∧ row p + F.index (original p) ≤ localCol F p + bound F p
instance (F : Parameters) (p : List Bool) : Decidable (valid F p) := inferInstanceAs (Decidable (_ ∧ _))

theorem row_binary : BinaryFn row := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem col_binary : BinaryFn col := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
theorem firstBlock_binary (F : Parameters) (a : Controls F) : BinaryFn (firstBlock F) :=
  (a.degree.sub a.index).comp IntegralBerkowitzBlockBits.original_FP
theorem secondBlock_binary (F : Parameters) (a : Controls F) : BinaryFn (secondBlock F) :=
  ((a.degree.sub (BinaryFn.const 1)).sub a.index).comp IntegralBerkowitzBlockBits.original_FP
theorem derivative_FP (F : Parameters) (a : Controls F) : FPPred (derivative F) :=
  col_binary.lt (firstBlock_binary F a)
theorem localCol_binary (F : Parameters) (a : Controls F) : BinaryFn (localCol F) :=
  BinaryFn.ite (derivative_FP F a) col_binary (col_binary.sub (firstBlock_binary F a))
theorem coefficient_binary (F : Parameters) (a : Controls F) : BinaryFn (coefficient F) :=
  ((row_binary.add (a.index.comp IntegralBerkowitzBlockBits.original_FP)).sub (localCol_binary F a)).add
    (BinaryFn.ite (derivative_FP F a) (BinaryFn.const 1) (BinaryFn.const 0))
theorem multiplier_binary (F : Parameters) (a : Controls F) : BinaryFn (multiplier F) :=
  BinaryFn.ite (derivative_FP F a) (coefficient_binary F a) (BinaryFn.const 1)
theorem bound_binary (F : Parameters) (a : Controls F) : BinaryFn (bound F) :=
  BinaryFn.ite (derivative_FP F a)
    ((a.degree.sub (BinaryFn.const 1)).comp IntegralBerkowitzBlockBits.original_FP)
    (a.degree.comp IntegralBerkowitzBlockBits.original_FP)
theorem valid_FP (F : Parameters) (a : Controls F) : FPPred (valid F) := by
  have HD := (firstBlock_binary F a).add (secondBlock_binary F a)
  have HR := row_binary.add (a.index.comp IntegralBerkowitzBlockBits.original_FP)
  exact (row_binary.lt HD).and ((col_binary.lt HD).and
    (((localCol_binary F a).le HR).and (HR.le ((localCol_binary F a).add (bound_binary F a)))))

def query (F : Parameters) (p : List Bool) : List Bool :=
  pair (original p) (pair (BinaryNatCode.encode (coefficient F p))
    (pair (IntegralBerkowitzBlockBits.basisRowCode p) (IntegralBerkowitzBlockBits.basisColCode p)))

theorem query_FP (F : Parameters) (a : Controls F) : query F ∈ FP :=
  mem_FP_pair IntegralBerkowitzBlockBits.original_FP (mem_FP_pair (coefficient_binary F a).bits_mem_FP
    (mem_FP_pair IntegralBerkowitzBlockBits.basisRowCode_FP IntegralBerkowitzBlockBits.basisColCode_FP))

theorem query_original (F : Parameters) (p : List Bool) : pairFst (query F p) = original p := pairFst_pair _ _

theorem query_packet (F : Parameters) (c : List Bool) (r t i j : ℕ) :
    let packet := pair (IntegralBlockMomentBits.context c r t)
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))
    query F packet = pair c (pair (BinaryNatCode.encode (coefficient F packet))
      (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))) := by
  simp only [query, original, IntegralBerkowitzBlockBits.original, IntegralBerkowitzBlockBits.basisRowCode,
    IntegralBerkowitzBlockBits.basisColCode, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair]

theorem requested_degree_le (F : Parameters) (p : List Bool) (hv : valid F p) :
    coefficient F p ≤ F.degree (original p) := by
  rcases hv with ⟨_, _, Hlow, Hhigh⟩
  unfold coefficient
  by_cases HD : derivative F p
  · rw [ite_eq_left HD]
    simp only [bound, HD, ite_true] at Hhigh
    unfold derivative firstBlock at HD
    omega
  · rw [ite_eq_right HD]
    simp only [bound, HD, ite_false] at Hhigh
    omega

def finish (F : Parameters) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (F.modulus (original (pairFst z))))
    (pair (pairSnd z) (BinaryNatCode.encode (multiplier F (pairFst z)))))

theorem finish_FP (F : Parameters) (a : Controls F) : finish F ∈ FP := by
  have HM : BinaryFn (fun z => F.modulus (original (pairFst z))) :=
    (a.modulus.comp IntegralBerkowitzBlockBits.original_FP).comp pairFst_mem_FP
  have HK : BinaryFn (fun z => multiplier F (pairFst z)) :=
    (multiplier_binary F a).comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP (mem_FP_pair pairSnd_mem_FP HK.bits_mem_FP)) BinaryNat.mulMod_mem_FP

def program (F : Parameters) : SingleCall.Program where
  request p := decide (valid F p)
  query := query F
  immediate _ := []
  finish := finish F

theorem controls (F : Parameters) (a : Controls F) : (program F).Controls :=
  ⟨(valid_FP F a).flag_mem_FP, query_FP F a, constFn_mem_FP [], finish_FP F a⟩

theorem finish_packet (F : Parameters) (p : List Bool) (x : ZMod (F.modulus (original p))) :
    finish F (pair p (residueBits x)) = residueBits (x * (multiplier F p : ZMod (F.modulus (original p)))) := by
  simp only [finish, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_nat_residueBits _ _ _

theorem value (F : Parameters) (answer : List Bool → List Bool) (p : List Bool) (x : ℤ)
    (ha : valid F p → answer (query F p) = residueBits (x : ZMod (F.modulus (original p)))) :
    (program F).value answer p =
      residueBits ((if valid F p then x * (multiplier F p : ℤ) else 0 : ℤ) : ZMod (F.modulus (original p))) := by
  by_cases HV : valid F p
  · simp only [SingleCall.Program.value, program, HV, decide_true, ite_true]
    rw [ha HV, finish_packet, Int.cast_mul, Int.cast_natCast]
  · simp only [SingleCall.Program.value, program, HV, decide_false, Bool.false_eq_true, ite_false,
      Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem requests_iff (F : Parameters) (answer : List Bool → List Bool) (budget : List Bool → ℕ)
    (p child : List Bool) : (program F).controller.Requests answer budget p child ↔
      valid F p ∧ child = query F p := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem matrix_entry {A : Type*} [CommRing A] {M : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (F : Parameters) (p : Polynomial A) (c : List Bool)
    (i j : Fin ((F.degree c - F.index c) + (F.degree c - 1 - F.index c))) (r t : Fin M) :
    let packet := pair (IntegralBlockMomentBits.context c r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
    Algebra.leftMulMatrix b (subresultantMatrix p p.derivative (F.degree c) (F.degree c - 1) (F.index c) i j) r t =
      if valid F packet then
        Algebra.leftMulMatrix b (p.coeff (coefficient F packet)) r t * (multiplier F packet : ℤ) else 0 := by
  dsimp only
  induction j using Fin.addCases with
  | left j =>
    rw [subresultantMatrix_castAdd]
    have Hj : j.val < (F.degree c - F.index c) + (F.degree c - 1 - F.index c) :=
      j.isLt.trans_le (Nat.le_add_right _ _)
    simp only [valid, row, col, firstBlock, secondBlock, localCol, coefficient, multiplier,
      derivative, bound, original, IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Fin.val_castAdd, j.isLt, Hj, ite_true, i.isLt, true_and]
    split_ifs with H
    · rw [Polynomial.coeff_derivative, show ((↑i + F.index c - ↑j : ℕ) : A) + 1 =
        (((↑i + F.index c - ↑j + 1 : ℕ) : ℤ) : A) from by simp,
        mul_comm, IntegralActionHeightBounds.int_multiply_entry]
      exact mul_comm _ _
    · rw [map_zero, Matrix.zero_apply]
  | right j =>
    rw [subresultantMatrix_natAdd]
    have Hnot : ¬ F.degree c - F.index c + j.val < F.degree c - F.index c := by omega
    simp only [valid, row, col, firstBlock, secondBlock, localCol, coefficient, multiplier,
      derivative, bound, original, IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Fin.val_natAdd, Hnot, ite_false, Nat.add_sub_cancel_left, i.isLt, true_and,
      Nat.add_zero, Nat.cast_one, mul_one]
    have Hj : F.degree c - F.index c + j.val <
        (F.degree c - F.index c) + (F.degree c - 1 - F.index c) := Nat.add_lt_add_left j.isLt _
    simp only [Hj, true_and]
    split_ifs <;> simp only [map_zero, Matrix.zero_apply]

theorem actual_value {A : Type*} [CommRing A] {M : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (F : Parameters) (p : Polynomial A) (c : List Bool)
    (i j : Fin ((F.degree c - F.index c) + (F.degree c - 1 - F.index c))) (r t : Fin M)
    (answer : List Bool → List Bool) :
    let packet := pair (IntegralBlockMomentBits.context c r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
    (valid F packet → answer (query F packet) =
      residueBits ((Algebra.leftMulMatrix b (p.coeff (coefficient F packet)) r t : ℤ) : ZMod (F.modulus c))) →
    (program F).value answer packet =
      residueBits ((Algebra.leftMulMatrix b
        (subresultantMatrix p p.derivative (F.degree c) (F.degree c - 1) (F.index c) i j) r t : ℤ) :
          ZMod (F.modulus c)) := by
  dsimp only
  intro ha
  rw [matrix_entry]
  let packet := pair (IntegralBlockMomentBits.context c r.val t.val)
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  let x := Algebra.leftMulMatrix b (p.coeff (coefficient F packet)) r t
  have HM : F.modulus (original packet) = F.modulus c := by
    simp only [packet, original, IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context, pairFst_pair]
  have HA : valid F packet → answer (query F packet) = residueBits (x : ZMod (F.modulus (original packet))) := by
    intro hv
    exact (ha hv).trans (congrArg (fun modulus : ℕ => residueBits (x : ZMod modulus)) HM.symm)
  have HE := value F answer packet x HA
  exact HE.trans (congrArg (fun modulus : ℕ => residueBits
    ((if valid F packet then x * (multiplier F packet : ℤ) else 0 : ℤ) : ZMod modulus)) HM)

end LeanCanny.Algebra.PrincipalDerivativeEntryRequest
