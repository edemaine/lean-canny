/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueSystemControls
public import LeanCanny.Algebra.FixedWidthChartMonomial

/-! # Exact physical-birth packets for the reciprocal digit selector

The second virtual digit is removed by literal division and remainder.
The homogeneous target and source are retained. Chart recognition uses
the actual original spatial degree, which fits the original-derived
Macaulay width.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueSystemSemantics
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCoordinateBasis
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedVirtualSweepSource
open IntegralMixedValueSystemControls
open scoped Classical

theorem integer_value (F : IntegralReciprocalEntryRequest.Parameters) (reply : List Bool → List Bool)
    (p : List Bool) [NeZero (F.modulus (MacaulayFullBoxBits.ctx p))] (x : ℤ)
    (ha : IntegralReciprocalEntryRequest.request F p → reply (IntegralReciprocalEntryRequest.query F p) =
      residueBits (x : ZMod (F.modulus (MacaulayFullBoxBits.ctx p)))) :
    (IntegralReciprocalEntryRequest.program F).value reply p = residueBits
      ((if IntegralReciprocalEntryRequest.request F p then x else
        if IntegralReciprocalEntryRequest.chart F p then -1 else 0 : ℤ) : ZMod (F.modulus (MacaulayFullBoxBits.ctx p))) := by
  refine (IntegralReciprocalEntryRequest.value F reply p (x : ZMod _) ha).trans ?_
  congr 1
  split_ifs <;> simp only [Int.cast_neg, Int.cast_one, Int.cast_zero]

theorem zero_selection (x : ℤ) (a c k D : ℕ) (same : Prop) [Decidable same] :
    (if c ≤ a ∧ a - c = 1 then x else if a = c ∧ same ∧ k = D then -1 else 0) =
      (if c ≤ a then (if a - c = 1 then x else 0) -
        (if a - c = 0 ∧ k = D ∧ same then 1 else 0) else 0) := by
  by_cases HL : c ≤ a <;> by_cases HD : a - c = 1 <;> by_cases HE : a = c <;>
    by_cases HS : same <;> by_cases HK : k = D <;> simp_all
  all_goals omega

def packet (F : Family) (_I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1))
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) : List Bool :=
  MacaulayFullBoxBits.entryPacket q j.val k.val
    (pairIndex (F.birth q + 1) (F.width q) (u, a)).val
    (pairIndex (F.birth q + 1) (F.width q) (v, c)).val

theorem valid_packet (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1))
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) :
    IntegralReciprocalEntryRequest.valid (parameters F I) (packet F I q j k u v a c) := by
  simp only [IntegralReciprocalEntryRequest.valid, IntegralReciprocalEntryRequest.row,
    IntegralReciprocalEntryRequest.target, IntegralReciprocalEntryRequest.basisRow,
    IntegralReciprocalEntryRequest.basisCol, packet, MacaulayFullBoxBits.idx_entryPacket,
    MacaulayFullBoxBits.shift_entryPacket, MacaulayFullBoxBits.ctx_entryPacket,
    MacaulayFullBoxBits.uv_entryPacket, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  refine ⟨j.isLt, k.isLt, ?_, ?_⟩
  · rw [rank_eq]
    exact (pairIndex (F.birth q + 1) (F.width q) (u, a)).isLt
  · rw [rank_eq]
    exact (pairIndex (F.birth q + 1) (F.width q) (v, c)).isLt

theorem query_packet (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1))
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) :
    IntegralReciprocalEntryRequest.query (parameters F I) (packet F I q j k u v a c) =
      MacaulayFullBoxBits.entryPacket q j.val k.val u.val v.val := by
  rw [packet, IntegralReciprocalEntryRequest.query_packet]
  change MacaulayFullBoxBits.entryPacket q j.val k.val
    ((pairIndex (F.birth q + 1) (F.width q) (u, a)).val / 2 ^ F.width q)
    ((pairIndex (F.birth q + 1) (F.width q) (v, c)).val / 2 ^ F.width q) = _
  rw [FixedWidthChartMonomial.pair_div, FixedWidthChartMonomial.pair_div]

theorem chart_target (F : Family) (I : Indices F) (q : List Bool)
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q)))) :
    Finsupp.single (0 : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)) (F.spatial q).degree =
      nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val ↔
        k.val = (F.spatial q).degree :=
  eq_comm.trans (FixedWidthChartMonomial.native_eq_chart_iff _ _ _ (degree_lt F I q) k)

theorem request_zero (F : Family) (I : Indices F) (q : List Bool)
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) :
    IntegralReciprocalEntryRequest.request (parameters F I) (packet F I q 0 k u v a c) ↔
      c.val ≤ a.val ∧ a.val - c.val = 1 := by
  have HV := valid_packet F I q 0 k u v a c
  simp only [IntegralReciprocalEntryRequest.request, HV, true_and]
  simp only [IntegralReciprocalEntryRequest.row, IntegralReciprocalEntryRequest.rowDigit,
    IntegralReciprocalEntryRequest.colDigit, IntegralReciprocalEntryRequest.basisRow,
    IntegralReciprocalEntryRequest.basisCol, packet, MacaulayFullBoxBits.idx_entryPacket,
    MacaulayFullBoxBits.ctx_entryPacket, MacaulayFullBoxBits.uv_entryPacket, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, parameters, FixedWidthChartMonomial.pair_mod,
    Fin.val_zero, Nat.lt_irrefl, true_and, false_and, or_false]

theorem chart_zero (F : Family) (I : Indices F) (q : List Bool)
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) :
    IntegralReciprocalEntryRequest.chart (parameters F I) (packet F I q 0 k u v a c) ↔
      a.val = c.val ∧ u = v ∧ k.val = (F.spatial q).degree := by
  have HV := valid_packet F I q 0 k u v a c
  simp only [IntegralReciprocalEntryRequest.chart, HV, true_and]
  simp only [IntegralReciprocalEntryRequest.row, IntegralReciprocalEntryRequest.target,
    IntegralReciprocalEntryRequest.rowDigit, IntegralReciprocalEntryRequest.colDigit,
    IntegralReciprocalEntryRequest.oldRow, IntegralReciprocalEntryRequest.oldCol,
    IntegralReciprocalEntryRequest.basisRow, IntegralReciprocalEntryRequest.basisCol,
    packet, MacaulayFullBoxBits.idx_entryPacket, MacaulayFullBoxBits.shift_entryPacket,
    MacaulayFullBoxBits.ctx_entryPacket, MacaulayFullBoxBits.uv_entryPacket, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, parameters, FixedWidthChartMonomial.pair_mod,
    FixedWidthChartMonomial.pair_div, Fin.val_zero, Fin.ext_iff, true_and]

theorem zero_value (F : Family) (I : Indices F) (reply : List Bool → List Bool) (q : List Bool)
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) (x : ℤ)
    (ha : c.val ≤ a.val ∧ a.val - c.val = 1 →
      reply (MacaulayFullBoxBits.entryPacket q 0 k.val u.val v.val) = residueBits (x : ZMod (I.modulus q))) :
    (program F I).value reply (packet F I q 0 k u v a c) = residueBits
      ((if c.val ≤ a.val then (if a.val - c.val = 1 then x else 0) -
        (if a.val - c.val = 0 ∧ k.val = (F.spatial q).degree ∧ u = v then 1 else 0) else 0 : ℤ) : ZMod (I.modulus q)) := by
  let p := packet F I q 0 k u v a c
  have HM : (parameters F I).modulus (MacaulayFullBoxBits.ctx p) = I.modulus q := by
    simp only [p, packet, MacaulayFullBoxBits.ctx_entryPacket, parameters]
  let : NeZero ((parameters F I).modulus (MacaulayFullBoxBits.ctx p)) := ⟨by rw [HM]; exact I.modulus_ne_zero q⟩
  have HR := request_zero F I q k u v a c
  have HC := chart_zero F I q k u v a c
  have HA : IntegralReciprocalEntryRequest.request (parameters F I) p →
      reply (IntegralReciprocalEntryRequest.query (parameters F I) p) =
        residueBits (x : ZMod ((parameters F I).modulus (MacaulayFullBoxBits.ctx p))) := by
    intro h
    have HB : reply (IntegralReciprocalEntryRequest.query (parameters F I) p) = residueBits (x : ZMod (I.modulus q)) := by
      rw [query_packet]
      exact ha (HR.mp h)
    exact HB.trans
      (congrArg (fun m : ℕ => residueBits (x : ZMod m)) HM.symm)
  have H := integer_value (parameters F I) reply p x HA
  have HE : (if IntegralReciprocalEntryRequest.request (parameters F I) p then x else
      if IntegralReciprocalEntryRequest.chart (parameters F I) p then -1 else 0 : ℤ) =
      if c.val ≤ a.val then (if a.val - c.val = 1 then x else 0) -
        (if a.val - c.val = 0 ∧ k.val = (F.spatial q).degree ∧ u = v then 1 else 0) else 0 := by
    dsimp only [p]
    simp only [HR, HC]
    exact zero_selection x a.val c.val k.val (F.spatial q).degree (u = v)
  exact H.trans ((congrArg (fun z : ℤ => residueBits (z : ZMod ((parameters F I).modulus (MacaulayFullBoxBits.ctx p)))) HE).trans
    (congrArg (fun m : ℕ => residueBits
      ((if c.val ≤ a.val then (if a.val - c.val = 1 then x else 0) -
        (if a.val - c.val = 0 ∧ k.val = (F.spatial q).degree ∧ u = v then 1 else 0) else 0 : ℤ) : ZMod m)) HM))

theorem request_succ (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) :
    IntegralReciprocalEntryRequest.request (parameters F I) (packet F I q j.succ k u v a c) ↔ a.val = c.val := by
  have HV := valid_packet F I q j.succ k u v a c
  simp only [IntegralReciprocalEntryRequest.request, HV, true_and]
  simp only [IntegralReciprocalEntryRequest.row, IntegralReciprocalEntryRequest.rowDigit,
    IntegralReciprocalEntryRequest.colDigit, IntegralReciprocalEntryRequest.basisRow,
    IntegralReciprocalEntryRequest.basisCol, packet, MacaulayFullBoxBits.idx_entryPacket,
    MacaulayFullBoxBits.ctx_entryPacket, MacaulayFullBoxBits.uv_entryPacket, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, parameters, FixedWidthChartMonomial.pair_mod, Fin.val_succ]
  omega

theorem not_chart_succ (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) :
    ¬IntegralReciprocalEntryRequest.chart (parameters F I) (packet F I q j.succ k u v a c) := by
  rintro ⟨_, H, _⟩
  simp only [IntegralReciprocalEntryRequest.row, packet, MacaulayFullBoxBits.idx_entryPacket,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Fin.val_succ] at H
  omega

theorem succ_value (F : Family) (I : Indices F) (reply : List Bool → List Bool) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q)) (x : ℤ)
    (ha : a.val = c.val → reply (MacaulayFullBoxBits.entryPacket q j.succ.val k.val u.val v.val) =
      residueBits (x : ZMod (I.modulus q))) :
    (program F I).value reply (packet F I q j.succ k u v a c) =
      residueBits ((if a.val = c.val then x else 0 : ℤ) : ZMod (I.modulus q)) := by
  let p := packet F I q j.succ k u v a c
  have HM : (parameters F I).modulus (MacaulayFullBoxBits.ctx p) = I.modulus q := by
    simp only [p, packet, MacaulayFullBoxBits.ctx_entryPacket, parameters]
  let : NeZero ((parameters F I).modulus (MacaulayFullBoxBits.ctx p)) := ⟨by rw [HM]; exact I.modulus_ne_zero q⟩
  have HR := request_succ F I q j k u v a c
  have HC := not_chart_succ F I q j k u v a c
  have HA : IntegralReciprocalEntryRequest.request (parameters F I) p →
      reply (IntegralReciprocalEntryRequest.query (parameters F I) p) =
        residueBits (x : ZMod ((parameters F I).modulus (MacaulayFullBoxBits.ctx p))) := by
    intro h
    have HB : reply (IntegralReciprocalEntryRequest.query (parameters F I) p) = residueBits (x : ZMod (I.modulus q)) := by
      rw [query_packet]
      exact ha (HR.mp h)
    exact HB.trans (congrArg (fun m : ℕ => residueBits (x : ZMod m)) HM.symm)
  have H := integer_value (parameters F I) reply p x HA
  have HE : (if IntegralReciprocalEntryRequest.request (parameters F I) p then x else
      if IntegralReciprocalEntryRequest.chart (parameters F I) p then -1 else 0 : ℤ) =
        if a.val = c.val then x else 0 := by
    dsimp only [p]
    simp only [HR, HC, ite_false]
  exact H.trans ((congrArg (fun z : ℤ => residueBits (z : ZMod ((parameters F I).modulus (MacaulayFullBoxBits.ctx p)))) HE).trans
    (congrArg (fun m : ℕ => residueBits ((if a.val = c.val then x else 0 : ℤ) : ZMod m)) HM))

end LeanCanny.Algebra.IntegralMixedValueSystemSemantics
