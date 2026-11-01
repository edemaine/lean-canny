/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralBerkowitzMomentFreeze
public import LeanCanny.Algebra.IntegralCriticalTotalMomentSnapshot
/-! # Canonical scalar trailing moments with separate query fields -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalMomentValueSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

noncomputable def snapshotSource (A : IntegralHistoryCriticalBits.Family) (m : ℕ) (hm : m ≠ 0) : Source :=
  IntegralBerkowitzMomentFreezeBits.freeze
    (IntegralCriticalQuerySnapshotBits.canonicalAction (IntegralCriticalTotalSnapshotBits.queryAt A 0 0 0 0 m hm)) []

noncomputable def atValue (A : IntegralHistoryCriticalBits.Family) (r t s u m : ℕ) (hm : m ≠ 0) : List Bool :=
  IntegralBerkowitzMomentFreezeBits.atMoment (snapshotSource A m hm) r t s u

noncomputable def value (F : Scripts) (q : List Bool) : List Bool :=
  (momentFamily (characteristic F)).value (IntegralCriticalFlatMomentBits.packet F.toParameters q)

theorem freeze_snapshot (F : Scripts) (q : List Bool) :
    IntegralBerkowitzMomentFreezeBits.freeze (characteristic F) q =
      snapshotSource (IntegralCriticalTotalCreatingBits.atFamily F q)
        (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := rfl

theorem native_snapshot (F : Scripts) (p : List Bool) :
    (momentFamily (characteristic F)).value p = atValue (IntegralCriticalTotalCreatingBits.atFamily F (original p))
      (Nat.fromBitsLE (basisRowCode p)) (Nat.fromBitsLE (basisColCode p))
      (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p))
      (IntegralCriticalHistoryTask.modulus F.toParameters (original p))
      (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters (original p)) := by
  rw [IntegralBerkowitzMomentFreezeBits.value_freeze, freeze_snapshot]
  rfl

attribute [local irreducible] atValue

theorem value_snapshot (F : Scripts) (q : List Bool) :
    value F q = atValue (IntegralCriticalTotalCreatingBits.atFamily F q)
      (get F.toParameters .row q) (get F.toParameters .col q)
      (get F.toParameters .slot11 q) (get F.toParameters .slot12 q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := by
  unfold value
  simpa only [IntegralCriticalFlatMomentBits.packet, original, basisRowCode, basisColCode,
    IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    using native_snapshot F (IntegralCriticalFlatMomentBits.packet F.toParameters q)

theorem atValue_congr (A B : IntegralHistoryCriticalBits.Family) (r t s u m r' t' s' u' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hA : A = B) (hr : r = r') (ht : t = t')
    (hs : s = s') (hu : u = u') (hmod : m = m') : atValue A r t s u m hm = atValue B r' t' s' u' m' hm' := by
  subst B; subst r'; subst t'; subst s'; subst u'; subst m'
  rfl

end LeanCanny.Algebra.IntegralCriticalTotalMomentValueSnapshotBits
