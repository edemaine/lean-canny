/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscNativeMomentPower
public import LeanCanny.Algebra.IntegralBerkowitzMomentFreeze
public import LeanCanny.Algebra.IntegralCriticalFlatBerkowitzQuery
/-! # Actual virtual trailing moments retain their selected parent -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits

noncomputable def momentSourceAt (F : Family) (key : List Bool) (j c m : ℕ) (hm : m ≠ 0) : Source :=
  { IntegralMixedPscMatrixModel.core F key j c with modulus := fun _ => m, modulus_ne_zero := fun _ => hm }

noncomputable def momentAt (F : Family) (key : List Bool) (j c r t s u m : ℕ) (hm : m ≠ 0) : List Bool :=
  IntegralBerkowitzMomentFreezeBits.atMoment (momentSourceAt F key j c m hm) r t s u

theorem freeze_moment (P : Parameters) (F : Family) (q : List Bool) :
    IntegralBerkowitzMomentFreezeBits.freeze (characteristic P F) q =
      momentSourceAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q) (modulus P q) (modulus_ne_zero P q) := rfl

theorem moment_native_snapshot (P : Parameters) (F : Family) (p : List Bool) :
    (momentFamily (characteristic P F)).value p =
      momentAt F (IntegralMixedVirtualTaskBits.saved P (original p)) (get P .slot13 (original p)) (get P .slot8 (original p))
        (Nat.fromBitsLE (basisRowCode p)) (Nat.fromBitsLE (basisColCode p))
        (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p))
        (modulus P (original p)) (modulus_ne_zero P (original p)) := by
  rw [IntegralBerkowitzMomentFreezeBits.value_freeze, freeze_moment]
  rfl

attribute [local irreducible] momentAt

theorem moment_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    momentValue P F q = momentAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q)
      (get P .row q) (get P .col q) (get P .slot11 q) (get P .slot12 q) (modulus P q) (modulus_ne_zero P q) := by
  unfold momentValue
  simpa only [IntegralCriticalFlatMomentBits.packet, original, basisRowCode, basisColCode,
    IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    using moment_native_snapshot P F (IntegralCriticalFlatMomentBits.packet P q)

theorem momentAt_congr (F : Family) (key key' : List Bool) (j c r t s u m j' c' r' t' s' u' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hj : j = j') (hc : c = c') (hr : r = r') (ht : t = t')
    (hs : s = s') (hu : u = u') (hmod : m = m') :
    momentAt F key j c r t s u m hm = momentAt F key' j' c' r' t' s' u' m' hm' := by
  subst key'; subst j'; subst c'; subst r'; subst t'; subst s'; subst u'; subst m'
  rfl

theorem moment_child_bounded (P : Parameters) (F : Family) (p : List Bool)
    (hr : Nat.fromBitsLE (basisRowCode p) ≤ numericCap P (RankedHistoryTask.root (original p)))
    (ht : Nat.fromBitsLE (basisColCode p) ≤ numericCap P (RankedHistoryTask.root (original p)))
    (hs : Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p) ≤ numericCap P (RankedHistoryTask.root (original p)))
    (hu : Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p) ≤ numericCap P (RankedHistoryTask.root (original p))) :
    momentValue P F (IntegralCriticalFlatBerkowitzQuery.momentWriter P p) = (momentFamily (characteristic P F)).value p := by
  rw [moment_snapshot, moment_native_snapshot]
  apply momentAt_congr
  · apply IntegralMixedVirtualTaskBits.saved_invariance
    · exact IntegralCriticalFlatBerkowitzQuery.momentWriter_root P p
    · exact IntegralCriticalFlatBerkowitzQuery.momentWriter_birth P p
    · simp only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_false]
  · simp only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_false]
  · simp only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_false]
  · simpa only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left hr
  · simpa only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left ht
  · simpa only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left hs
  · simpa only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left hu
  · exact IntegralCriticalFlatBerkowitzQuery.momentWriter_modulus P p

end LeanCanny.Algebra.IntegralMixedPscUpperBits
