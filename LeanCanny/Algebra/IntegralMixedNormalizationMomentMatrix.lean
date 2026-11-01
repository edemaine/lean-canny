/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationSnapshots
public import LeanCanny.Algebra.IntegralCriticalTotalMomentSnapshot
/-! # Integer augmented moment matrices under virtual source retargeting -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationMomentMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits
open IntegralCriticalTotalMomentSnapshotBits (canonicalPacket atEntry momentEntry_at)
set_option backward.isDefEq.respectTransparency false

noncomputable def canonicalSize (F : Family) (key : List Bool) (s t : ℕ) : ℕ :=
  let S := IntegralBerkowitzBlockBits.momentFamily (sourceAt F key 1 (by decide))
  (S.dimension (canonicalPacket s t) + 2) * S.rank (canonicalPacket s t)
noncomputable def canonicalEntry (F : Family) (key : List Bool) (s _t r u : ℕ) : ℤ :=
  let S := sourceAt F key 1 (by decide)
  atEntry S [] (s / (S.dimension [] + 1)) r u
noncomputable def size (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  IntegralCriticalFlatMomentEntryBits.matrixSize P (source P F) q
noncomputable def entry (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry ((IntegralCriticalFlatMomentBits.source P (source P F)).powerMatrix q) r t

theorem size_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    size P F q = canonicalSize F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot11 q) (get P .slot12 q) := by
  simp only [size, canonicalSize, canonicalPacket, IntegralCriticalFlatMomentEntryBits.matrixSize,
    IntegralCriticalFlatMomentBits.source, IntegralBlockMomentBits.Family.requery,
    IntegralBerkowitzBlockBits.momentFamily, IntegralBerkowitzBlockBits.remaining,
    IntegralBerkowitzBlockBits.stage, IntegralBerkowitzBlockBits.original,
    IntegralCriticalFlatMomentBits.packet, IntegralBlockMomentBits.context,
    MatrixMoment.EntryBits.rowIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem atEntry_snapshot (P : Parameters) (F : Family) (q : List Bool) (s r t : ℕ) :
    atEntry (source P F) q s r t =
      atEntry (sourceAt F (IntegralMixedVirtualTaskBits.saved P q) 1 (by decide)) [] s r t := rfl

attribute [local irreducible] atEntry

theorem entry_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    entry P F q r t = canonicalEntry F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot11 q) (get P .slot12 q) r t := by
  change IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralBerkowitzBlockBits.momentFamily (source P F)).powerMatrix (IntegralCriticalFlatMomentBits.packet P q)) r t = _
  rw [momentEntry_at, IntegralCriticalFlatMomentBits.packet_parent]
  have HS : IntegralBerkowitzBlockBits.stage (source P F) (IntegralCriticalFlatMomentBits.packet P q) =
      get P .slot11 q / ((source P F).dimension q + 1) := by
    simp only [IntegralBerkowitzBlockBits.stage, IntegralCriticalFlatMomentBits.packet,
      IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [HS, atEntry_snapshot]
  rfl

attribute [local irreducible] canonicalSize canonicalEntry IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

theorem size_transport (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q)
    (hs : get P .slot11 c = get P .slot11 q) (ht : get P .slot12 c = get P .slot12 q) : size P F c = size P F q := by
  rw [size_snapshot, size_snapshot, IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hx, hs, ht]

theorem entry_transport (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q)
    (hs : get P .slot11 c = get P .slot11 q) (ht : get P .slot12 c = get P .slot12 q) (r t : ℕ) :
    entry P F c r t = entry P F q r t := by
  rw [entry_snapshot, entry_snapshot, IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hx, hs, ht]

noncomputable def modularEntry (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) : List Bool :=
  residueBits (entry P F q r t : ZMod (modulus P q))

theorem modularEntry_fin (P : Parameters) (F : Family) (q : List Bool) (r t : Fin (size P F q)) :
    modularEntry P F q r.val t.val = residueBits
      (((IntegralCriticalFlatMomentBits.source P (source P F)).powerMatrix q r t : ℤ) : ZMod (modulus P q)) :=
  congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) (IntegralCriticalTotalSnapshotBits.integerEntry_fin _ r t)

theorem modularEntry_transport (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q)
    (hs : get P .slot11 c = get P .slot11 q) (ht : get P .slot12 c = get P .slot12 q)
    (hm : modulus P c = modulus P q) (r t : ℕ) : modularEntry P F c r t = modularEntry P F q r t :=
  congrArg₂ (fun (m : ℕ) (z : ℤ) => residueBits (z : ZMod m)) hm (entry_transport P F q c hr hb hx hs ht r t)

end LeanCanny.Algebra.IntegralMixedNormalizationMomentMatrixBits
