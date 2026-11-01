/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueReciprocalRequest

/-! # Actual mapped-system coefficient matrices with the second formal digit

The source is the constructed double-nilpotent mapped system. Both basis
indices name its actual integer basis. Invalid labels are preserved as
zero before finite indices are formed.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueReciprocalMatrix
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualSweepSource
open scoped Classical

abbrev free (F : Family) (q : List Bool) := F.ambient q - (F.rule q).critical.offset.val + 1
abbrev width (F : Family) (q : List Bool) := IntegralMixedGridValue.width (F.spatial q) (F.rule q)
abbrev rank (F : Family) (q : List Bool) := count (F.birth q + 2) (F.width q)

noncomputable def entry (F : Family) (I : Indices F) (q : List Bool)
    (s : Fin (free F q + 1)) (k : Fin (count (free F q + 1) (width F q))) (r t : Fin (rank F q)) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
    ((IntegralMixedValueDoubleSystem.mappedSystem F q (I.coordinate q) s).coeff
      (nativeExponent (Equiv.refl _) (width F q) k.val)) r t

def Labels (F : Family) (q : List Bool) (s k r t : ℕ) : Prop :=
  s < free F q + 1 ∧ k < count (free F q + 1) (width F q) ∧ r < rank F q ∧ t < rank F q
noncomputable instance (F : Family) (q : List Bool) (s k r t : ℕ) : Decidable (Labels F q s k r t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem valid_packet_iff (A : IntegralReciprocalEntryRequest.Parameters) (q : List Bool) (s k r t : ℕ) :
    IntegralReciprocalEntryRequest.valid A (MacaulayFullBoxBits.entryPacket q s k r t) ↔
      s < A.free q + 1 ∧ k < count (A.free q + 1) (A.width q) ∧
        r < A.oldRank q * A.digit q ∧ t < A.oldRank q * A.digit q := by
  simp only [IntegralReciprocalEntryRequest.valid, IntegralReciprocalEntryRequest.row, IntegralReciprocalEntryRequest.target,
    IntegralReciprocalEntryRequest.basisRow, IntegralReciprocalEntryRequest.basisCol,
    MacaulayFullBoxBits.ctx_entryPacket, MacaulayFullBoxBits.idx_entryPacket, MacaulayFullBoxBits.shift_entryPacket,
    MacaulayFullBoxBits.uv_entryPacket, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem labels_iff (F : Family) (I : Indices F) (q : List Bool) (s k r t : ℕ) :
    Labels F q s k r t ↔ IntegralReciprocalEntryRequest.valid
      (IntegralMixedValueSystemControls.parameters F I) (MacaulayFullBoxBits.entryPacket q s k r t) := by
  have H := valid_packet_iff (IntegralMixedValueSystemControls.parameters F I) q s k r t
  rw [IntegralMixedValueSystemControls.rank_eq] at H
  exact H.symm

noncomputable def totalEntry (F : Family) (I : Indices F) (q : List Bool) (s k r t : ℕ) : ℤ :=
  if H : Labels F q s k r t then entry F I q ⟨s, H.1⟩ ⟨k, H.2.1⟩ ⟨r, H.2.2.1⟩ ⟨t, H.2.2.2⟩ else 0

theorem total_finite (F : Family) (I : Indices F) (q : List Bool)
    (s : Fin (free F q + 1)) (k : Fin (count (free F q + 1) (width F q))) (r t : Fin (rank F q)) :
    totalEntry F I q s.val k.val r.val t.val = entry F I q s k r t := by
  rw [totalEntry, dite_eq_left (show Labels F q s.val k.val r.val t.val from ⟨s.isLt, k.isLt, r.isLt, t.isLt⟩)]

theorem total_invalid (F : Family) (I : Indices F) (q : List Bool) (s k r t : ℕ)
    (h : ¬Labels F q s k r t) : totalEntry F I q s k r t = 0 := dite_eq_right h

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (totalEntry (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F) q
    (get P .slot8 q) (get P .target q) (get P .row q) (get P .col q) : ZMod (modulus P q))

end LeanCanny.Algebra.IntegralMixedValueReciprocalMatrix
