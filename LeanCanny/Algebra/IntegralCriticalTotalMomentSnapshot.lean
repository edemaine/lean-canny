/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalMatrixSnapshot
public import LeanCanny.Algebra.IntegralCriticalFlatMomentEntry
/-! # Actual augmented moment matrices retain their creating snapshot -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalMomentSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

def canonicalPacket (s t : ℕ) : List Bool :=
  pair (IntegralBlockMomentBits.context [] 0 0) (pair (BinaryNatCode.encode s) (BinaryNatCode.encode t))

noncomputable def atMatrix (S : IntegralBerkowitzBlockBits.Source) (c : List Bool) (s : ℕ) :
    Matrix (Fin ((S.dimension c - s - 1 + 2) * S.rank c))
      (Fin ((S.dimension c - s - 1 + 2) * S.rank c)) ℤ := by
  let := S.ring c
  exact IntegralCoefficientBlocks.blockHom (S.basis c) (S.dimension c - s - 1 + 2)
    (MatrixMoment.matrixFin
      (fun j : Fin (S.dimension c - s - 1) => S.matrix c ⟨s, by have := j.isLt; omega⟩
        ⟨s + 1 + j.val, by have := j.isLt; omega⟩)
      (fun i : Fin (S.dimension c - s - 1) => S.matrix c ⟨s + 1 + i.val, by have := i.isLt; omega⟩
        ⟨s, by have := i.isLt; omega⟩)
      (fun i j : Fin (S.dimension c - s - 1) => S.matrix c
        ⟨s + 1 + i.val, by have := i.isLt; omega⟩ ⟨s + 1 + j.val, by have := j.isLt; omega⟩))

noncomputable def atEntry (S : IntegralBerkowitzBlockBits.Source) (c : List Bool) (s r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry (atMatrix S c s) r t

theorem momentEntry_at (S : IntegralBerkowitzBlockBits.Source) (p : List Bool) (r t : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry ((IntegralBerkowitzBlockBits.momentFamily S).powerMatrix p) r t =
      atEntry S (IntegralBerkowitzBlockBits.original p) (IntegralBerkowitzBlockBits.stage S p) r t := rfl

noncomputable def canonicalSize (A : IntegralHistoryCriticalBits.Family) (s t : ℕ) : ℕ :=
  let S := IntegralBerkowitzBlockBits.momentFamily (IntegralCriticalQuerySnapshotBits.canonicalAction A)
  (S.dimension (canonicalPacket s t) + 2) * S.rank (canonicalPacket s t)

noncomputable def canonicalEntry (A : IntegralHistoryCriticalBits.Family) (s _t r u : ℕ) : ℤ :=
  let S := IntegralCriticalQuerySnapshotBits.canonicalAction A
  atEntry S [] (s / (S.dimension [] + 1)) r u

noncomputable def size (F : Scripts) (q : List Bool) : ℕ :=
  IntegralCriticalFlatMomentEntryBits.matrixSize F.toParameters (IntegralCriticalFlatActualSources.characteristic F) q

noncomputable def entry (F : Scripts) (q : List Bool) (r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralCriticalFlatMomentBits.source F.toParameters (IntegralCriticalFlatActualSources.characteristic F)).powerMatrix q) r t

attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

theorem size_snapshot (F : Scripts) (q : List Bool) :
    size F q = canonicalSize (IntegralCriticalTotalCreatingBits.atFamily F q)
      (get F.toParameters .slot11 q) (get F.toParameters .slot12 q) := by
  simp only [size, canonicalSize, canonicalPacket, IntegralCriticalFlatMomentEntryBits.matrixSize,
    IntegralCriticalFlatMomentBits.source, IntegralBlockMomentBits.Family.requery,
    IntegralBerkowitzBlockBits.momentFamily, IntegralBerkowitzBlockBits.remaining,
    IntegralBerkowitzBlockBits.stage, IntegralBerkowitzBlockBits.original,
    IntegralCriticalFlatMomentBits.packet, IntegralBlockMomentBits.context,
    MatrixMoment.EntryBits.rowIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem atEntry_snapshot (F : Scripts) (q : List Bool) (s r t : ℕ) :
    atEntry (IntegralCriticalFlatActualSources.characteristic F) q s r t =
      atEntry (IntegralCriticalQuerySnapshotBits.canonicalAction (IntegralCriticalTotalCreatingBits.atFamily F q)) [] s r t := rfl

attribute [local irreducible] atEntry

theorem entry_snapshot (F : Scripts) (q : List Bool) (r t : ℕ) :
    entry F q r t = canonicalEntry (IntegralCriticalTotalCreatingBits.atFamily F q)
      (get F.toParameters .slot11 q) (get F.toParameters .slot12 q) r t := by
  change IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralBerkowitzBlockBits.momentFamily (IntegralCriticalFlatActualSources.characteristic F)).powerMatrix
      (IntegralCriticalFlatMomentBits.packet F.toParameters q)) r t = _
  rw [momentEntry_at, IntegralCriticalFlatMomentBits.packet_parent]
  have HS : IntegralBerkowitzBlockBits.stage (IntegralCriticalFlatActualSources.characteristic F)
      (IntegralCriticalFlatMomentBits.packet F.toParameters q) =
      get F.toParameters .slot11 q / ((IntegralCriticalFlatActualSources.characteristic F).dimension q + 1) := by
    simp only [IntegralBerkowitzBlockBits.stage, IntegralCriticalFlatMomentBits.packet,
      IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [HS, atEntry_snapshot]
  rfl

theorem size_invariance (F : Scripts) (q c : List Bool) (hr : root q = root c)
    (hb : birth F.toParameters q = birth F.toParameters c)
    (hs : get F.toParameters .slot11 q = get F.toParameters .slot11 c)
    (ht : get F.toParameters .slot12 q = get F.toParameters .slot12 c) : size F q = size F c := by
  rw [size_snapshot, size_snapshot, hs, ht]
  exact congrArg (fun A => canonicalSize A _ _) (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

theorem entry_invariance (F : Scripts) (q c : List Bool) (hr : root q = root c)
    (hb : birth F.toParameters q = birth F.toParameters c)
    (hs : get F.toParameters .slot11 q = get F.toParameters .slot11 c)
    (ht : get F.toParameters .slot12 q = get F.toParameters .slot12 c) (r t : ℕ) :
    entry F q r t = entry F c r t := by
  rw [entry_snapshot, entry_snapshot, hs, ht]
  exact congrArg (fun A => canonicalEntry A _ _ r t) (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

noncomputable def modularEntry (F : Scripts) (q : List Bool) (r t : ℕ) : List Bool :=
  residueBits (entry F q r t : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))

theorem modularEntry_fin (F : Scripts) (q : List Bool) (r t : Fin (size F q)) :
    modularEntry F q r.val t.val = residueBits
      (((IntegralCriticalFlatMomentBits.source F.toParameters (IntegralCriticalFlatActualSources.characteristic F)).powerMatrix q r t : ℤ) :
        ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)) :=
  congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)))
    (IntegralCriticalTotalSnapshotBits.integerEntry_fin _ r t)

theorem modularEntry_invariance (F : Scripts) (q c : List Bool) (hr : root q = root c)
    (hb : birth F.toParameters q = birth F.toParameters c)
    (hs : get F.toParameters .slot11 q = get F.toParameters .slot11 c)
    (ht : get F.toParameters .slot12 q = get F.toParameters .slot12 c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) (r t : ℕ) :
    modularEntry F q r t = modularEntry F c r t :=
  congrArg₂ (fun (m : ℕ) (z : ℤ) => residueBits (z : ZMod m)) hm (entry_invariance F q c hr hb hs ht r t)

end LeanCanny.Algebra.IntegralCriticalTotalMomentSnapshotBits
