/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogeneousSystemCoefficientRequest
public import LeanCanny.Algebra.HomogeneousCoefficientRequest

/-! # Exact source packets and guards of the homogeneous dispatcher -/

@[expose] public section
namespace LeanCanny.Algebra.HomogeneousSystemCoefficientSemantics
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open MacaulayFullBoxBits HomogeneousSystemCoefficientRequest

theorem valid_packet (F : Parameters) (q : List Bool) (j : Fin (F.free q + 1))
    (k : Fin (count (F.free q + 1) (F.width q))) (r t : Fin (F.rank q)) :
    valid F (entryPacket q j.val k.val r.val t.val) := by
  simp only [valid, row, HomogeneousSystemCoefficientRequest.target, basisRow, basisCol, IntegralReciprocalEntryRequest.row,
    IntegralReciprocalEntryRequest.target, IntegralReciprocalEntryRequest.basisRow,
    IntegralReciprocalEntryRequest.basisCol, idx_entryPacket, shift_entryPacket, uv_entryPacket,
    ctx_entryPacket, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact ⟨j.isLt, k.isLt, r.isLt, t.isLt⟩

theorem total_guard_packet (F : Parameters) (q : List Bool) (j k r t : ℕ) :
    total F (entryPacket q j k r t) = polynomialDegree F (entryPacket q j k r t) ↔
      HomogenizationLayout.weightedSum (F.free q) (F.free q) (F.width q) k =
        if j = 0 then F.degree q else F.coordinateDegree q := by
  have H := HomogenizationBits.total_eq_iff (F.free ∘ ctx) (F.free ∘ ctx) (F.width ∘ ctx)
    (polynomialDegree F) (homogeneousPacket (entryPacket q j k r t))
  simpa only [HomogeneousSystemCoefficientRequest.total, homogeneousPacket, polynomialDegree, row, IntegralReciprocalEntryRequest.row,
    idx_entryPacket, shift_entryPacket, ctx_entryPacket, pairFst_pair, pairSnd_pair, Function.comp_apply,
    BinaryNatCode.encode, Nat.fromBitsLE_bits] using H

theorem stripped_packet (F : Parameters) (q : List Bool) (j k r t : ℕ) :
    stripped F (entryPacket q j k r t) = BinaryNatCode.encode (Nat.fromBitsLE (k.bits.drop (F.width q))) := by
  simp only [stripped, ctx_entryPacket, shift_entryPacket, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

theorem query_zero_packet (F : Parameters) (q : List Bool) (k r t : ℕ) :
    query F (entryPacket q 0 k r t) = pair q (pair []
      (pair (BinaryNatCode.encode (Nat.fromBitsLE (k.bits.drop (F.width q))))
        (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))) := by
  simp only [query, row, IntegralReciprocalEntryRequest.row, idx_entryPacket,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true, ctx_entryPacket, stripped_packet, uv_entryPacket]

theorem query_succ_packet (F : Parameters) (q : List Bool) (j : Fin (F.free q))
    (k r t : ℕ) : query F (entryPacket q j.succ.val k r t) = pair q (pair [true]
      (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode (entry (F.width q) k (j.val + 1)))
        (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))))) := by
  have HR : row (entryPacket q j.succ.val k r t) < F.free (ctx (entryPacket q j.succ.val k r t)) + 1 := by
    simpa only [row, IntegralReciprocalEntryRequest.row, idx_entryPacket, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, ctx_entryPacket] using j.succ.isLt
  have HC := coefficient_eq F (entryPacket q j.succ.val k r t) HR
  rw [query, HC]
  simp only [row, HomogeneousSystemCoefficientRequest.target, IntegralReciprocalEntryRequest.row, IntegralReciprocalEntryRequest.target,
    idx_entryPacket, shift_entryPacket, ctx_entryPacket, uv_entryPacket, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Fin.val_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel_right]

theorem outsideZero_packet (F : Parameters) (q : List Bool) (j : Fin (F.free q)) (k r t : ℕ) :
    outsideZero F (entryPacket q j.succ.val k r t) ↔ ∀ i : Fin (F.free q), i ≠ j →
      nativeExponent (Equiv.refl (Fin (F.free q))) (F.width q) (Nat.fromBitsLE (k.bits.drop (F.width q))) i = 0 := by
  let p := entryPacket q j.succ.val k r t
  have HE (i : Fin (F.free q)) :
      nativeExponent (Equiv.refl (Fin (F.free q))) (F.width q) (Nat.fromBitsLE (k.bits.drop (F.width q))) i =
        DiagonalParameterBits.exponentAt (F.free ∘ ctx) (F.width ∘ ctx) (freePacket F p) i.val := by
    simp only [DiagonalParameterBits.exponentAt, FixedWidthQuery.entry, freePacket, p, pairFst_pair,
      pairSnd_pair, Function.comp_apply, ctx_entryPacket, i.isLt, ite_true, stripped_packet,
      FixedWidthQuery.coordinate, nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply,
      BinaryNatCode.encode, entry]
  change (∀ i < (F.free ∘ ctx) (pairFst (freePacket F p)),
    i ≠ row (pairFst (freePacket F p)) - 1 →
      DiagonalParameterBits.exponentAt (F.free ∘ ctx) (F.width ∘ ctx) (freePacket F p) i = 0) ↔ _
  simp only [freePacket, pairFst_pair, Function.comp_apply, p, ctx_entryPacket, row,
    IntegralReciprocalEntryRequest.row, idx_entryPacket, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Fin.val_succ, Nat.add_sub_cancel_right]
  constructor
  · intro h i hi
    exact (HE i).trans (h i.val i.isLt (fun hv => hi (Fin.ext hv)))
  · intro h i hi hn
    exact (HE ⟨i, hi⟩).symm.trans (h ⟨i, hi⟩ (fun he => hn (congrArg Fin.val he)))

theorem request_zero_packet (F : Parameters) (q : List Bool)
    (k : Fin (count (F.free q + 1) (F.width q))) (r t : Fin (F.rank q)) :
    request F (entryPacket q 0 k.val r.val t.val) ↔
      HomogenizationLayout.weightedSum (F.free q) (F.free q) (F.width q) k.val = F.degree q := by
  have HV := valid_packet F q 0 k r t
  simp only [Fin.val_zero] at HV
  simp only [request, HV, true_and]
  rw [total_guard_packet]
  simp only [row, IntegralReciprocalEntryRequest.row, idx_entryPacket, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, true_or, and_true, ite_true]

theorem request_succ_packet (F : Parameters) (q : List Bool) (j : Fin (F.free q))
    (k : Fin (count (F.free q + 1) (F.width q))) (r t : Fin (F.rank q)) :
    request F (entryPacket q j.succ.val k.val r.val t.val) ↔
      HomogenizationLayout.weightedSum (F.free q) (F.free q) (F.width q) k.val = F.coordinateDegree q ∧
        (∀ i : Fin (F.free q), i ≠ j → nativeExponent (Equiv.refl (Fin (F.free q))) (F.width q)
          (Nat.fromBitsLE (k.val.bits.drop (F.width q))) i = 0) := by
  have HV := valid_packet F q j.succ k r t
  simp only [request, HV, true_and]
  rw [total_guard_packet, outsideZero_packet]
  simp only [row, IntegralReciprocalEntryRequest.row, idx_entryPacket, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Fin.val_succ, Nat.add_one_ne_zero, false_or, ite_false]

theorem value_zero {A : Type*} [CommRing A] (F : Parameters) (q : List Bool)
    (k : Fin (count (F.free q + 1) (F.width q))) (r t : Fin (F.rank q))
    (p : MvPolynomial (Fin (F.free q)) A) (enc : A → List Bool) (hz : enc 0 = [])
    (reply : List Bool → List Bool)
    (ha : HomogenizationLayout.weightedSum (F.free q) (F.free q) (F.width q) k.val = F.degree q →
      reply (pair q (pair [] (pair (BinaryNatCode.encode (Nat.fromBitsLE (k.val.bits.drop (F.width q))))
        (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))) =
          enc (p.coeff (nativeExponent (Equiv.refl _) (F.width q) (Nat.fromBitsLE (k.val.bits.drop (F.width q)))))) :
    (program F).value reply (entryPacket q 0 k.val r.val t.val) =
      enc ((RelativeValueSystemMap.homogeneousTest p (F.degree q)).coeff (nativeExponent (Equiv.refl _) (F.width q) k.val)) := by
  rw [HomogeneousCoefficientRequest.coefficient_rank]
  by_cases HT : HomogenizationLayout.weightedSum (F.free q) (F.free q) (F.width q) k.val = F.degree q
  · have HR := (request_zero_packet F q k r t).mpr HT
    simp only [SingleCall.Program.value, program, HR, decide_true, ite_true, pairSnd_pair]
    rw [query_zero_packet, ha HT, ite_eq_left HT]
  · have HR : ¬request F (entryPacket q 0 k.val r.val t.val) := fun h => HT ((request_zero_packet F q k r t).mp h)
    simp only [SingleCall.Program.value, program, HR, decide_false, Bool.false_eq_true, ite_false,
      ite_eq_right HT, hz]

theorem value_succ {A : Type*} [CommRing A] (F : Parameters) (q : List Bool) (j : Fin (F.free q))
    (k : Fin (count (F.free q + 1) (F.width q))) (r t : Fin (F.rank q))
    (p : Polynomial A) (enc : A → List Bool) (hz : enc 0 = []) (reply : List Bool → List Bool)
    (ha : HomogenizationLayout.weightedSum (F.free q) (F.free q) (F.width q) k.val = F.coordinateDegree q ∧
        (∀ i : Fin (F.free q), i ≠ j → nativeExponent (Equiv.refl (Fin (F.free q))) (F.width q)
          (Nat.fromBitsLE (k.val.bits.drop (F.width q))) i = 0) →
      reply (pair q (pair [true] (pair (BinaryNatCode.encode j.val)
        (pair (BinaryNatCode.encode (entry (F.width q) k.val (j.val + 1)))
          (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))))) =
            enc (p.coeff (entry (F.width q) k.val (j.val + 1)))) :
    (program F).value reply (entryPacket q j.succ.val k.val r.val t.val) =
      enc ((RelativeValueSystemMap.homogeneousTest (p.toMvPolynomial j) (F.coordinateDegree q)).coeff
        (nativeExponent (Equiv.refl _) (F.width q) k.val)) := by
  rw [HomogeneousCoefficientRequest.diagonal_coefficient]
  by_cases HT : HomogenizationLayout.weightedSum (F.free q) (F.free q) (F.width q) k.val = F.coordinateDegree q ∧
      (∀ i : Fin (F.free q), i ≠ j → nativeExponent (Equiv.refl (Fin (F.free q))) (F.width q)
        (Nat.fromBitsLE (k.val.bits.drop (F.width q))) i = 0)
  · have HR := (request_succ_packet F q j k r t).mpr HT
    simp only [SingleCall.Program.value, program, HR, decide_true, ite_true, pairSnd_pair]
    rw [query_succ_packet, ha HT, ite_eq_left HT]
  · have HR : ¬request F (entryPacket q j.succ.val k.val r.val t.val) := fun h => HT ((request_succ_packet F q j k r t).mp h)
    simp only [SingleCall.Program.value, program, HR, decide_false, Bool.false_eq_true, ite_false,
      ite_eq_right HT, hz]

end LeanCanny.Algebra.HomogeneousSystemCoefficientSemantics
