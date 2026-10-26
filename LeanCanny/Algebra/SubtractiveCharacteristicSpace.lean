/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CertifiedMatrix
public import LeanCanny.Algebra.AffineCharacteristic

/-! # Native coefficients of det(A − t I) with a retained parameter -/

@[expose] public section
namespace LeanCanny.Algebra.SubtractiveCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Brackets
open scoped Classical

def row (q : List Bool) : List Bool := pairFst (pairSnd q)
def col (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def inner (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd q)))
def outer (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd q)))
def modulus (q : List Bool) : List Bool := pairSnd (pairFst q)
def packet (c m : List Bool) (r s u v : ℕ) : List Bool :=
  pair (pair c m) (pair (BinaryNatCode.encode r) (pair (BinaryNatCode.encode s)
    (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))

theorem row_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_FP : col ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem inner_FP : inner ∈ FP := mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP
theorem outer_FP : outer ∈ FP := mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

def sourceQuery (q : List Bool) : List Bool := pair (pairFst q) (pair (row q) (pair (col q) (inner q)))

theorem sourceQuery_FP : sourceQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair row_FP (mem_FP_pair col_FP inner_FP))

def negativeOne (q : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNat.succ (modulus q)) (ArithmeticBits.one (BinaryNat.succ (modulus q))))

theorem negativeOne_FP : negativeOne ∈ FP := by
  have hm : (BinaryNat.succ ∘ modulus) ∈ FP := mem_FP_comp modulus_FP BinaryNat.succ_mem_FP
  have ho := mem_FP_comp hm ArithmeticBits.one_mem_FP
  have hn := mem_FP_comp (mem_FP_pair hm ho) ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq hn (fun _ => by simp only [negativeOne, Function.comp_apply])

def finish (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (outer (pairFst z)) = 0 then pairSnd z
  else if Nat.fromBitsLE (outer (pairFst z)) = 1 ∧ Nat.fromBitsLE (inner (pairFst z)) = 0 ∧
      Nat.fromBitsLE (row (pairFst z)) = Nat.fromBitsLE (col (pairFst z)) then negativeOne (pairFst z) else []

theorem finish_FP : finish ∈ FP := by
  have hv := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP outer_FP)
  have hu := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP inner_FP)
  have hr := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP row_FP)
  have hs := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP col_FP)
  have hn : (negativeOne ∘ pairFst) ∈ FP := mem_FP_comp pairFst_mem_FP negativeOne_FP
  have ht := (hv.eq (BinaryFn.const 0)).ite_mem_FP pairSnd_mem_FP
    (((hv.eq (BinaryFn.const 1)).and ((hu.eq (BinaryFn.const 0)).and (hr.eq hs))).ite_mem_FP
      hn (constFn_mem_FP []))
  exact mem_FP_of_eq ht (fun _ => by simp only [finish, Function.comp_apply])

def entry (source : List Bool → List Bool) (q : List Bool) : List Bool := finish (pair q (source (sourceQuery q)))

theorem entry_evaluator {source : List Bool → List Bool} (E : SpaceFunction source) : SpaceFunction (entry source) :=
  ((E.precompose sourceQuery sourceQuery_FP).withInput.postcompose finish finish_FP).congr (funext fun _ => rfl)

theorem finish_packet (c m : List Bool) (r s u v : ℕ) (a : ZMod (Nat.fromBitsLE m + 1)) :
    finish (pair (packet c m r s u v) (residueBits a)) =
      residueBits (if v = 0 then a else if v = 1 ∧ u = 0 ∧ r = s then -1 else 0) := by
  simp only [finish, packet, row, col, inner, outer, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs
  · rfl
  · simp only [negativeOne, modulus, pairFst_pair, pairSnd_pair, BinaryNat.succ_eq_bits]
    change ArithmeticBits.negate (pair (BinaryNatCode.encode (Nat.fromBitsLE m + 1))
      (ArithmeticBits.one (BinaryNatCode.encode (Nat.fromBitsLE m + 1)))) = _
    rw [ArithmeticBits.one_residueBits, ArithmeticBits.negate_residueBits]
  · simp [residueBits, BinaryNatCode.encode]

theorem coefficient {N : ℕ} (A : Matrix (Fin N) (Fin N) (Polynomial ℤ)) (i j : Fin N) (u v : ℕ) :
    (((AffineCharacteristic.subtractiveMatrix A i j).coeff v).coeff u) =
      if v = 0 then (A i j).coeff u else if v = 1 ∧ u = 0 ∧ i = j then -1 else 0 := by
  unfold AffineCharacteristic.subtractiveMatrix
  rw [Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial, Polynomial.coeff_sub,
    Polynomial.coeff_C, Polynomial.coeff_monomial]
  by_cases hv : v = 0 <;> by_cases hv' : v = 1 <;> by_cases hu : u = 0 <;> by_cases hij : i = j <;>
    simp_all [Matrix.one_apply, Polynomial.coeff_one, eq_comm]

theorem entry_packet {N : List Bool → ℕ} (A : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial ℤ))
    (source : List Bool → List Bool)
    (hc : ∀ c m (i j : Fin (N c)) u, source (pair (pair c m) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
        residueBits ((((A c i j).coeff u) : ℤ) : ZMod (Nat.fromBitsLE m + 1)))
    (c m : List Bool) (i j : Fin (N c)) (u v : ℕ) :
    entry source (packet c m i.val j.val u v) =
      residueBits (((((AffineCharacteristic.subtractiveMatrix (A c) i j).coeff v).coeff u) : ℤ) :
        ZMod (Nat.fromBitsLE m + 1)) := by
  unfold entry
  have hs : sourceQuery (packet c m i.val j.val u v) =
      pair (pair c m) (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u))) := by
    simp only [sourceQuery, packet, row, col, inner, pairFst_pair, pairSnd_pair]
  rw [hs, hc, finish_packet, coefficient]
  simp only [Fin.val_inj, Int.cast_ite, Int.cast_neg, Int.cast_one, Int.cast_zero]

theorem inner_degree {N E : ℕ} (A : Matrix (Fin N) (Fin N) (Polynomial ℤ))
    (hA : ∀ i j, (A i j).natDegree ≤ E) (i j : Fin N) (v : ℕ) :
    ((AffineCharacteristic.subtractiveMatrix A i j).coeff v).natDegree ≤ E := by
  unfold AffineCharacteristic.subtractiveMatrix
  rw [Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial, Polynomial.coeff_sub,
    Polynomial.coeff_C, Polynomial.coeff_monomial]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · split_ifs
    · exact hA i j
    · simp
  · split_ifs
    · by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · simp

noncomputable def reader (N E : List Bool → ℕ)
    (A : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial ℤ))
    (hN : ∀ c, 0 < N c) (hn : BinaryFn N) (hE : BinaryFn E) (hA : ∀ c i j, (A c i j).natDegree ≤ E c)
    (source : List Bool → List Bool) (S : SpaceFunction source)
    (hc : ∀ c m (i j : Fin (N c)) u, source (pair (pair c m) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
        residueBits ((((A c i j).coeff u) : ℤ) : ZMod (Nat.fromBitsLE m + 1))) :
    CertifiedPolynomial.BivariateReader (fun c => (AffineCharacteristic.subtractiveMatrix (A c)).det) :=
  CertifiedMatrix.determinantReader N E (fun c => AffineCharacteristic.subtractiveMatrix (A c)) hN hn hE
    (fun c => inner_degree (A c) (hA c)) (entry source) (entry_evaluator S) (entry_packet A source hc)

end LeanCanny.Algebra.SubtractiveCharacteristicBits
