/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCutRecordKind
public import LeanCanny.Geometry.IntegralMixedPrefixFrame
/-! # The actual atomic frozen sweep has an original virtual record

The offset/height are obtained from the existing frozen-first permutation;
the current-denominator bit is true. Prefix frames make the permutation
identity, retaining the literal original spatial source.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ} {F : Frame n}

noncomputable def AtomicRows.sweepData (H : AtomicRows F birth) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) : IntegralMixedCutRecordConstructor.Data n birth where
  critical:={H.pointData g g hg hg with coordinate:=⟨0,by
    have HC:=FrozenCoordinateOrdering.card_lt F.frozen g hg
    omega⟩}
  positive:=Finset.card_pos.mpr ⟨h,hh⟩
  height:=⟨((FrozenCoordinateOrdering.permutation F.frozen).symm h).val,
    (FrozenCoordinateOrdering.inverse_mem_iff F.frozen h).mpr hh⟩
  current:=true

private theorem coordinate_update {m : ℕ} (d : IntegralMixedCriticalRecordConstructor.Data n m)
    (j : Fin (n-d.offset.val+1)) :
    ({d with coordinate:=j} : IntegralMixedCriticalRecordConstructor.Data n m).rule={d.rule with coordinate:=j.val}:=rfl

theorem AtomicRows.sweepData_critical (H : AtomicRows F birth) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) :
    (H.sweepData h hh g hg).critical.rule=critical F g hg:=by
  change ({H.pointData g g hg hg with coordinate:=_} : IntegralMixedCriticalRecordConstructor.Data n birth).rule=_
  rw [coordinate_update,H.pointData_rule g g hg hg]
  rfl

theorem AtomicRows.sweepData_rule {S B : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B birth ι) (H : AtomicRows F birth) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) :
    (H.sweepData h hh g hg).rule (commonDenominator x) (commonDenominator_ne_zero x)=sweep x F h hh g hg:=by
  simp only [IntegralMixedCutRecordConstructor.Data.rule,H.sweepData_critical h hh g hg,
    show (H.sweepData h hh g hg).current=true from rfl,ite_true,sweep]
  rfl

end LeanCanny.Geometry.IntegralMixedFrozenFrame
