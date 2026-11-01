/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationTopQueries
public import LeanCanny.Algebra.IntegralMixedNormalizationCaps
public import LeanCanny.Algebra.IntegralBerkowitzMomentFreeze
public import LeanCanny.Algebra.IntegralCriticalFlatBerkowitzQuery
/-! # Actual virtual trailing moments retain their selected parent -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceAt (F : Family) (key : List Bool) (m : ℕ) (hm : m ≠ 0) : Source where
  dimension _ := dimension F key
  rank _ := 1
  carrier _ := ℤ
  ring _ := inferInstance
  nontrivial _ := inferInstance
  basis _ := Module.Basis.singleton (Fin 1) ℤ
  matrix _ := top F key
  modulus _ := m
  modulus_ne_zero _ := hm
  coefficient _ := 0
  basisRow _ := 0
  basisCol _ := 0

noncomputable def momentAt (F : Family) (key : List Bool) (r t s u m : ℕ) (hm : m ≠ 0) : List Bool :=
  IntegralBerkowitzMomentFreezeBits.atMoment (sourceAt F key m hm) r t s u

noncomputable def momentValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  (momentFamily (source P F)).value (IntegralCriticalFlatMomentBits.packet P q)

theorem freeze_moment (P : Parameters) (F : Family) (q : List Bool) :
    IntegralBerkowitzMomentFreezeBits.freeze (source P F) q =
      sourceAt F (IntegralMixedVirtualTaskBits.saved P q) (modulus P q) (modulus_ne_zero P q) := rfl

theorem moment_native_snapshot (P : Parameters) (F : Family) (p : List Bool) :
    (momentFamily (source P F)).value p =
      momentAt F (IntegralMixedVirtualTaskBits.saved P (original p))
        (Nat.fromBitsLE (basisRowCode p)) (Nat.fromBitsLE (basisColCode p))
        (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p))
        (modulus P (original p)) (modulus_ne_zero P (original p)) := by
  rw [IntegralBerkowitzMomentFreezeBits.value_freeze, freeze_moment]
  rfl

attribute [local irreducible] momentAt

theorem moment_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    momentValue P F q = momentAt F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .row q) (get P .col q) (get P .slot11 q) (get P .slot12 q) (modulus P q) (modulus_ne_zero P q) := by
  unfold momentValue
  simpa only [IntegralCriticalFlatMomentBits.packet, original, basisRowCode, basisColCode,
    IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    using moment_native_snapshot P F (IntegralCriticalFlatMomentBits.packet P q)

theorem momentAt_congr (F : Family) (key key' : List Bool) (r t s u m r' t' s' u' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hr : r = r') (ht : t = t')
    (hs : s = s') (hu : u = u') (hmod : m = m') :
    momentAt F key r t s u m hm = momentAt F key' r' t' s' u' m' hm' := by
  subst key'; subst r'; subst t'; subst s'; subst u'; subst m'
  rfl

theorem moment_child_bounded (P : Parameters) (F : Family) (p : List Bool)
    (hr : Nat.fromBitsLE (basisRowCode p) ≤ numericCap P (RankedHistoryTask.root (original p)))
    (ht : Nat.fromBitsLE (basisColCode p) ≤ numericCap P (RankedHistoryTask.root (original p)))
    (hs : Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p) ≤ numericCap P (RankedHistoryTask.root (original p)))
    (hu : Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p) ≤ numericCap P (RankedHistoryTask.root (original p))) :
    momentValue P F (IntegralCriticalFlatBerkowitzQuery.momentWriter P p) = (momentFamily (source P F)).value p := by
  rw [moment_snapshot, moment_native_snapshot]
  apply momentAt_congr
  · apply IntegralMixedVirtualTaskBits.saved_invariance
    · exact IntegralCriticalFlatBerkowitzQuery.momentWriter_root P p
    · exact IntegralCriticalFlatBerkowitzQuery.momentWriter_birth P p
    · simp only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_false]
  · simpa only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left hr
  · simpa only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left ht
  · simpa only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left hs
  · simpa only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left hu
  · exact IntegralCriticalFlatBerkowitzQuery.momentWriter_modulus P p

noncomputable def integerPower (F : Family) (key : List Bool) (r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry ((sourceAt F key 1 (by decide)).powerMatrix []) r t

theorem power_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    integerPower F (IntegralMixedVirtualTaskBits.saved P q) r t =
      IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).powerMatrix q) r t := rfl

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
