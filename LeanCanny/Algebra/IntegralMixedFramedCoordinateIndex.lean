/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateRepresentative
/-! # Native independent Y/E queries retain one actual old coefficient context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateIndexBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

def first (P : Parameters) (parent : List Bool→List Bool) (y : List Bool→ℕ) :=
  IntegralMixedValueFieldQuery.query P parent .rawFactor .companion .slot8 y
def query (P : Parameters) (parent : List Bool→List Bool) (y k : List Bool→ℕ) :=
  IntegralMixedValueFieldQuery.query P (first P parent y) .rawFactor .companion .coefficient k

theorem query_FP (P : Parameters) (a : Access P) (parent : List Bool→List Bool) (hp : parent∈FP)
    (y k : List Bool→ℕ) (hy : BinaryFn y) (hk : BinaryFn k) : query P parent y k∈FP :=
  IntegralMixedValueFieldQuery.query_FP P a _
    (IntegralMixedValueFieldQuery.query_FP P a parent hp _ _ _ y hy) _ _ _ k hk

theorem root (P : Parameters) (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool) :
    RankedHistoryTask.root (query P parent y k q)=RankedHistoryTask.root (parent q) :=
  (IntegralMixedValueFieldQuery.query_root _ _ _ _ _ _ q).trans
    (IntegralMixedValueFieldQuery.query_root _ _ _ _ _ _ q)
theorem birth (P : Parameters) (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool) :
    IntegralCriticalHistoryTask.birth P (query P parent y k q)=IntegralCriticalHistoryTask.birth P (parent q) :=
  (IntegralMixedValueFieldQuery.query_birth _ _ _ _ _ _ q).trans
    (IntegralMixedValueFieldQuery.query_birth _ _ _ _ _ _ q)
theorem saved (P : Parameters) (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P parent y k q)=IntegralMixedVirtualTaskBits.saved P (parent q) :=
  (IntegralMixedValueFieldQuery.query_saved _ _ _ _ _ _ q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_saved _ _ _ _ _ _ q (by decide))

theorem other (P : Parameters) (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool) (f : Field)
    (h14 : f≠.slot14) (hy : f≠.slot8) (hk : f≠.coefficient) :
    get P f (query P parent y k q)=get P f (parent q) := by
  rw [query,IntegralMixedValueFieldQuery.query_other _ _ _ _ _ _ q f h14 hk,
    first,IntegralMixedValueFieldQuery.query_other _ _ _ _ _ _ q f h14 hy]

theorem y_value (P : Parameters) (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool)
    (hy : y q≤numericCap P (RankedHistoryTask.root (parent q))) :
    get P .slot8 (query P parent y k q)=y q := by
  rw [query,IntegralMixedValueFieldQuery.query_other _ _ _ _ _ _ q .slot8 (by decide) (by decide)]
  exact IntegralMixedValueFieldQuery.query_field _ _ _ _ _ _ q (by decide) hy

theorem k_value (P : Parameters) (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool)
    (hk : k q≤numericCap P (RankedHistoryTask.root (parent q))) :
    get P .coefficient (query P parent y k q)=k q := by
  apply IntegralMixedValueFieldQuery.query_field _ _ _ _ _ _ q (by decide)
  rw [first,IntegralMixedValueFieldQuery.query_root]
  exact hk

theorem active (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent q))
    (hj : get P .slot13 (parent q)≤P.ambient (RankedHistoryTask.root (parent q))+1)
    (hy : y q<IntegralMixedCoordinateCoefficientTasks.choiceBound P (family P D H) (parent q))
    (hy' : y q≤2^P.width (RankedHistoryTask.root (parent q)))
    (hcap : y q≤numericCap P (RankedHistoryTask.root (parent q))) :
    IntegralMixedFramedAllCoordinateSourceBits.Active P D H (query P parent y k q) := by
  have HV : IntegralMixedVirtualCaps.valid P (query P parent y k q) := by
    unfold IntegralMixedVirtualCaps.valid
    rw [birth,root]
    exact ha.1
  have HC : IntegralMixedVirtualContextBits.context P (query P parent y k q) := by
    unfold IntegralMixedVirtualContextBits.context
    rw [other P parent y k q .slot15 (by decide) (by decide) (by decide)]
    exact ha.2
  refine ⟨⟨HV,HC⟩,?_,?_,?_⟩
  · rw [other P parent y k q .slot13 (by decide) (by decide) (by decide),root]
    exact hj
  · change get P .slot8 (query P parent y k q)<IntegralMixedCoordinateTrailing.ChoiceBound
      ((family P D H).spatial (IntegralMixedVirtualTaskBits.saved P (query P parent y k q)))
      ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P (query P parent y k q)))
    rw [saved,y_value P parent y k q hcap]
    exact hy
  · rw [y_value P parent y k q hcap,root]
    exact hy'

end LeanCanny.Algebra.IntegralMixedFramedCoordinateIndexBits
