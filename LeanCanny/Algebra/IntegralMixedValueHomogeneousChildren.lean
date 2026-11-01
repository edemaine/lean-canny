/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueHomogeneousMatrix

/-! # Exact coefficient replies selected by a homogeneous value row -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueHomogeneousChildren
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps IntegralMixedValueHomogeneousQueries
open scoped Classical

theorem packet_eq (P : Parameters) (q : List Bool) (s k r t : ℕ)
    (hs : get P .slot8 q = s) (hk : get P .target q = k) (hr : get P .row q = r) (ht : get P .col q = t) :
    packet P q = MacaulayFullBoxBits.entryPacket q s k r t := by
  simp only [packet, hs, hk, hr, ht]

theorem original_target (P : Parameters) (F : Family) (q : List Bool) (k r t : ℕ)
    (hs : get P .slot8 q = 0) (hk : get P .target q = k) (hr : get P .row q = r) (ht : get P .col q = t) :
    originalTarget P F q = Nat.fromBitsLE (k.bits.drop ((parameters P F).width q)) := by
  unfold originalTarget
  rw [packet_eq P q 0 k r t hs hk hr ht, HomogeneousSystemCoefficientSemantics.stripped_packet,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem coefficient_packet (A : HomogeneousSystemCoefficientRequest.Parameters) (q : List Bool) (s k r t : ℕ)
    (hs : s < A.free q + 1) :
    HomogeneousSystemCoefficientRequest.coefficient A (MacaulayFullBoxBits.entryPacket q s k r t) =
      entry (A.width q) k s := by
  have HR : HomogeneousSystemCoefficientRequest.row (MacaulayFullBoxBits.entryPacket q s k r t) <
      A.free (MacaulayFullBoxBits.ctx (MacaulayFullBoxBits.entryPacket q s k r t)) + 1 := by
    simpa only [HomogeneousSystemCoefficientRequest.row, IntegralReciprocalEntryRequest.row,
      MacaulayFullBoxBits.idx_entryPacket, MacaulayFullBoxBits.ctx_entryPacket, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hs
  rw [HomogeneousSystemCoefficientRequest.coefficient_eq A _ HR]
  simp only [HomogeneousSystemCoefficientRequest.target, HomogeneousSystemCoefficientRequest.row,
    IntegralReciprocalEntryRequest.target, IntegralReciprocalEntryRequest.row,
    MacaulayFullBoxBits.ctx_entryPacket, MacaulayFullBoxBits.shift_entryPacket, MacaulayFullBoxBits.idx_entryPacket,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem restored_pull (F : Family) (base : List Bool → List Bool) (q : List Bool) (j e r t : ℕ) :
    IntegralMixedValueRestoredSource.entryAt (IntegralMixedVirtualQueryBits.pull F base) q j e r t =
      IntegralMixedValueRestoredSource.entryAt F (base q) j e r t := rfl

theorem restored_query (F : Family) (Q : IntegralMixedVirtualQueryBits.Queries) (q : List Bool) (e : ℕ)
    (r t : Fin (count (F.birth q + 1) (F.width q))) :
    IntegralMixedValueRestoredSource.entryAt F q (Q.coordinate q) e r.val t.val =
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((IntegralMixedVirtualOriginalRows.row F q ((IntegralMixedVirtualQueryBits.indices F Q).coordinate q)).coeff
          (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) e)) r t := by
  unfold IntegralMixedValueRestoredSource.entryAt
  simp only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]
  rfl

theorem original_reply (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool)
    (k : Fin (count ((parameters P F).free q + 1) ((parameters P F).width q)))
    (r t : Fin ((parameters P F).rank q))
    (hs : get P .slot8 q = 0) (hk : get P .target q = k.val)
    (hr : get P .row q = r.val) (ht : get P .col q = t.val)
    (hq : HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q)) :
    IntegralMixedValueRestoredSource.value P F (originalTask P F q) =
      residueBits ((Algebra.leftMulMatrix
        (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis
        ((IntegralMixedVirtualOriginalRows.row (IntegralMixedVirtualTaskBits.family P F) q
          ((IntegralMixedVirtualTaskBits.indices P F).coordinate q)).coeff
            (nativeExponent (Equiv.refl _) ((parameters P F).width q)
              (Nat.fromBitsLE (k.val.bits.drop ((parameters P F).width q))))) r t : ℤ) : ZMod (modulus P q)) := by
  rw [IntegralMixedValueRestoredSource.original_child P F g q hq]
  rw [original_target P F q k.val r.val t.val hs hk hr ht, hr, ht]
  rw [← restored_pull F (IntegralMixedVirtualTaskBits.saved P) q]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (restored_query (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.queries P) q _ r t)

noncomputable def coordinateEntry (F : Family) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (e : ℕ)
    (r t : Fin (count (F.birth q + 1) (F.width q))) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
    ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) j).coeff e) r t

theorem coordinate_finite (F : Family) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) (e : ℕ)
    (r t : Fin (count (F.birth q + 1) (F.width q))) :
    IntegralMixedVirtualQueryBits.matrixCoefficient F q j.val e r.val t.val = coordinateEntry F q j e r t := by
  rw [IntegralMixedValueCoordinateChild.matrixCoefficient_eq]
  simp only [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]
  rfl

theorem coordinate_reply (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool)
    (j : Fin ((parameters P F).free q))
    (k : Fin (count ((parameters P F).free q + 1) ((parameters P F).width q)))
    (r t : Fin ((parameters P F).rank q))
    (hs : get P .slot8 q = j.succ.val) (hk : get P .target q = k.val)
    (hr : get P .row q = r.val) (ht : get P .col q = t.val)
    (hq : HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q)) :
    (IntegralMixedVirtualTaskBits.source P F).value (coordinateTask P F q) =
      residueBits (coordinateEntry (IntegralMixedVirtualTaskBits.family P F) q j
        (entry ((parameters P F).width q) k.val j.succ.val) r t : ZMod (modulus P q)) := by
  have HZ : get P .slot8 q ≠ 0 := by rw [hs]; exact Nat.succ_ne_zero j.val
  have HC : IntegralMixedValueHomogeneousQueries.coordinateCoefficient P F q =
      entry ((parameters P F).width q) k.val j.succ.val := by
    unfold IntegralMixedValueHomogeneousQueries.coordinateCoefficient
    rw [packet_eq P q j.succ.val k.val r.val t.val hs hk hr ht]
    exact coefficient_packet _ q j.succ.val k.val r.val t.val j.succ.isLt
  rw [IntegralMixedValueTaskBounds.coordinateTask_value_guarded P F g q hq HZ]
  rw [← IntegralMixedVirtualQueryBits.matrix_pull F (IntegralMixedVirtualTaskBits.saved P) q,
    HC, hs, hr, ht]
  simp only [Fin.val_succ, Nat.add_sub_cancel]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (coordinate_finite (IntegralMixedVirtualTaskBits.family P F) q j _ r t)

end LeanCanny.Algebra.IntegralMixedValueHomogeneousChildren
