/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualFactorTransport
/-! # Actual retained-height replies of monomial matrix entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualMonomialHeight
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualFactorModel IntegralCriticalActualLowMatrixModel
open IntegralCriticalActualMonomialSnapshot
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

noncomputable def heightMatrix (S : IntegralMonomialTermBits.Source) (q : List Bool) (i : ℕ) :
    Matrix (Fin (S.rank q)) (Fin (S.rank q)) (ZMod (S.modulus q)) := by
  let := S.ring q
  exact (Algebra.leftMulMatrix (S.basis q) (S.height q i)).map (Int.castRingHom (ZMod (S.modulus q)))
noncomputable def heightAt (A : IntegralHistoryCriticalBits.Family) (x j k m : ℕ) (hm : m ≠ 0) (i r t : ℕ) :=
  entryBits (heightMatrix (monomialAt A x j k 0 0 m hm) [] i) r t
noncomputable def heightEntry (F : Scripts) (q : List Bool) (i r t : ℕ) :=
  entryBits (heightMatrix (IntegralCriticalFlatActualLow.source F) q i) r t

theorem heightAt_value (A : IntegralHistoryCriticalBits.Family) (x j k m : ℕ) (hm : m ≠ 0) (i r t : ℕ)
    (hr : r < rankAt A) (ht : t < rankAt A) :
    heightAt A x j k m hm i r t = IntegralHistoryCriticalBits.heightValue A i r t m := by
  unfold heightAt entryBits
  have HR : r < (monomialAt A x j k 0 0 m hm).rank [] := hr
  have HT : t < (monomialAt A x j k 0 0 m hm).rank [] := ht
  rw [dite_eq_left HR, dite_eq_left HT]
  unfold IntegralHistoryCriticalBits.heightValue UniformIntegralPrefix.Prefix.elementEntry
  have HR0 : r < FixedWidthPolynomial.count (A.birth []) (A.width []) := hr
  have HT0 : t < FixedWidthPolynomial.count (A.birth []) (A.width []) := ht
  simp only [Nat.mod_eq_of_lt HR0, Nat.mod_eq_of_lt HT0]
  rfl

theorem height_snapshot (F : Scripts) (q : List Bool) (i r t : ℕ) :
    heightEntry F q i r t = heightAt (IntegralCriticalTotalCreatingBits.atFamily F q)
      (IntegralCriticalHistoryTask.get F.toParameters .expression q) (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
      (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) i r t := by
  change entryBits (heightMatrix ((IntegralCriticalFlatActualLow.source F).snapshot q) [] i) r t = _
  rw [source_snapshot]
  rfl

theorem height_entry_fin (F : Scripts) (q : List Bool) (i : ℕ)
    (r t : Fin ((IntegralCriticalFlatActualLow.source F).rank q)) :
    heightEntry F q i r.val t.val = IntegralCriticalTotalHeightBits.entry F q i r.val t.val := by
  rw [height_snapshot]
  apply heightAt_value
  · rw [← rank_snapshot F q]; exact r.isLt
  · rw [← rank_snapshot F q]; exact t.isLt

theorem height_leaf (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool) (i : ℕ)
    (r t : Fin ((IntegralCriticalFlatActualLow.source F).rank q)) :
    (IntegralCriticalFlatActualLow.access F h).height
      (pair q (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      IntegralCriticalTotalHeightBits.entry F q i r.val t.val := by
  rw [(IntegralCriticalFlatActualLow.access F h).height_eq q i r t]
  exact (entryBits_fin (heightMatrix (IntegralCriticalFlatActualLow.source F) q i) r t).symm.trans (height_entry_fin F q i r t)

end LeanCanny.Algebra.IntegralCriticalActualMonomialHeight
