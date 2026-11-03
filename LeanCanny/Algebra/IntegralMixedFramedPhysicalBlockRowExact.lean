/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockPoweredExact
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockQuery
/-! # Whole fresh-row selection has the literal critical-row semantics -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalHeightBits (Active)
open FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] MvPolynomial.rename MvPolynomial.pderiv

theorem row_gradient_exact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected row : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) (hq : Active P (base q))
    (hi : row q=selected q) :
    rowPolynomial P D J T hr base selected row hs q=unpoweredExact P D J base q (.inl ⟨selected q,hs q⟩) := by
  have HB : row q<spatialCount P D J base q+(spatialCount P D J base q+1) := by have H:=hs q;omega
  rw [rowPolynomial,ite_eq_left ⟨hq,HB⟩,rawRowPolynomial,ite_eq_left (hi ▸ hs q),gradient,ite_eq_left hq]
  exact rawGradient_exact P D J base selected hs q hq

theorem row_equation_exact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected row : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) (hq : Active P (base q))
    (hi : row q=spatialCount P D J base q) :
    rowPolynomial P D J T hr base selected row hs q=unpoweredExact P D J base q (.inr 0) := by
  have HB : row q<spatialCount P D J base q+(spatialCount P D J base q+1) := by omega
  rw [rowPolynomial,ite_eq_left ⟨hq,HB⟩,rawRowPolynomial,ite_eq_right (by omega),ite_eq_left hi]
  exact sourcePolynomial_exact P D J base q

theorem row_height_exact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected row : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) (hq : Active P (base q))
    (hi : row q=spatialCount P D J base q+1+selected q) (hslot : get P .slot8 (base q)=selected q) :
    rowPolynomial P D J T hr base selected row hs q=
      unpoweredExact P D J base q (.inr (⟨selected q,hs q⟩ : Fin (spatialCount P D J base q)).succ) := by
  have HB : row q<spatialCount P D J base q+(spatialCount P D J base q+1) := by have H:=hs q;omega
  rw [rowPolynomial,ite_eq_left ⟨hq,HB⟩,rawRowPolynomial,ite_eq_right (by omega),ite_eq_right (by omega)]
  exact heightRow_exact P D J T hr base selected hs q hq hslot

noncomputable def prepared (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (row : List Bool→ℕ) := sourceTask P base (rowSelected P D J base row)

theorem prepared_FP (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP)
    (row : List Bool→ℕ) (hr : BinaryFn row) : prepared P D J base row∈FP :=
  sourceTask_FP P a base hb _ (BinaryFn.ofUnary (rowSelected_unary P a D J c base hb row hr))

theorem prepared_spatialCount (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (row : List Bool→ℕ) (q : List Bool) :
    spatialCount P D J (prepared P D J base row) q=spatialCount P D J base q := by
  rw [spatialCount_eq,spatialCount_eq]
  exact congrArg (fun r=>P.ambient r+1) (sourceTask_root P base _ q)

theorem prepared_selected_lt (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (row : List Bool→ℕ) (q : List Bool) :
    rowSelected P D J base row q<spatialCount P D J (prepared P D J base row) q := by
  rw [prepared_spatialCount]
  exact rowSelected_lt P D J base row q

theorem prepared_coordinate (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (row : List Bool→ℕ) (q : List Bool) :
    get P .slot8 (prepared P D J base row q)=rowSelected P D J base row q :=
  sourceTask_coordinate P D J base _ (rowSelected_lt P D J base row) q

theorem prepared_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (row : List Bool→ℕ) (hr : BinaryFn row)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J (prepared P D J base row)) V
      (poweredRowPolynomial P D J c.critical.tables c.critical.represents (prepared P D J base row)
        (rowSelected P D J base row) row (prepared_selected_lt P D J base row)) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘prepared P D J base row)) :=
  poweredRow_evaluator P a D J c hc _ (prepared_FP P a D J c base hb row hr) _ row
    (prepared_selected_lt P D J base row) (rowSelected_unary P a D J c base hb row hr) hr V hV target ht

theorem prepared_row_exact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (row : List Bool→ℕ) (q : List Bool) (hq : Active P (base q))
    (j : Variables (spatialCount P D J (prepared P D J base row) q))
    (hj : row q=(IntegralMixedFramedPhysicalIndex.criticalEquiv j).val) :
    rowPolynomial P D J T hr (prepared P D J base row) (rowSelected P D J base row) row
      (prepared_selected_lt P D J base row) q=unpoweredExact P D J (prepared P D J base row) q j := by
  have HA:=prepared_spatialCount P D J base row q
  have HP : Active P (prepared P D J base row q):=(sourceTask_active P base _ q).mpr hq
  cases j with
  | inl i =>
    change row q=i.val at hj
    have HS : rowSelected P D J base row q=i.val := by
      unfold rowSelected
      have H : row q<spatialCount P D J base q := by have HI:=i.isLt;omega
      rw [ite_eq_left H,hj]
    have HI : (⟨rowSelected P D J base row q,prepared_selected_lt P D J base row q⟩ :
        Fin (spatialCount P D J (prepared P D J base row) q))=i :=Fin.ext HS
    rw [row_gradient_exact P D J T hr (prepared P D J base row) _ row
      (prepared_selected_lt P D J base row) q HP (hj.trans HS.symm),HI]
  | inr k =>
    revert hj
    refine Fin.cases ?_ (fun i=>?_) k
    · intro hj
      change row q=spatialCount P D J (prepared P D J base row) q+0 at hj
      exact row_equation_exact P D J T hr (prepared P D J base row) _ row
        (prepared_selected_lt P D J base row) q HP (by omega)
    · intro hj
      change row q=spatialCount P D J (prepared P D J base row) q+(i.val+1) at hj
      have HS : rowSelected P D J base row q=i.val := by
        unfold rowSelected
        have H : ¬row q<spatialCount P D J base q := by omega
        rw [ite_eq_right H]
        have HE : row q-(spatialCount P D J base q+1)=i.val := by omega
        rw [HE,Nat.mod_eq_of_lt (by have HI:=i.isLt;omega)]
      have HI : (⟨rowSelected P D J base row q,prepared_selected_lt P D J base row q⟩ :
          Fin (spatialCount P D J (prepared P D J base row) q))=i :=Fin.ext HS
      rw [row_height_exact P D J T hr (prepared P D J base row) _ row
        (prepared_selected_lt P D J base row) q HP (by omega) (prepared_coordinate P D J base row q),HI]

theorem prepared_powered_exact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (row : List Bool→ℕ) (q : List Bool) (hq : Active P (base q))
    (j : Variables (spatialCount P D J (prepared P D J base row) q))
    (hj : row q=(IntegralMixedFramedPhysicalIndex.criticalEquiv j).val) :
    poweredRowPolynomial P D J T hr (prepared P D J base row) (rowSelected P D J base row) row
      (prepared_selected_lt P D J base row) q=poweredExact P D J (prepared P D J base row) q j := by
  rw [poweredRowPolynomial,prepared_row_exact P D J T hr base row q hq j hj]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
