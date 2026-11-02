/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPrefixSquareSample
public import LeanCanny.Algebra.IntegralMixedFramedPrefixSchedule
public import LeanCanny.Algebra.IntegralMixedFramedRowMassControls

/-! # Actual saved framed prefixes give complete native square inputs

Every numeric and mass control is derived from the original parameter and
instruction bounds. The remaining reader is literally the actual prefix row
coefficient function. Positive birth count is explicit; no dummy is added.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCompleteSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedStepHeight IntegralMixedFramedHistoryFamilyBits
open scoped Classical

noncomputable def family (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (h : FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀ u,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u)) :
    IntegralPrefixSquareSample.Family where
  horizon u := P.cap (pairFst (key u))+1
  width u := P.width (pairFst (key u))
  count u := (IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u)
  mass u := familyRowMass P L F C (pairFst (key u))
  prefixAt u := ((IntegralMixedFramedHistoryFamilyBits.family P D H).state (key u)).sampler.scalarPrefix
  count_pos := hpos
  scheduled u := IntegralMixedFramedHistoryScript.scheduled_run_all (initial P D (pairFst (key u)))
    (commands P D (key u)) (((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound (key u)).trans (Nat.le_succ _))
  row_mass u := family_row_mass P D H L F C h (key u)

noncomputable def input (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (h : FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀ u,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u)) : SquareSampleInput.Inputs :=
  IntegralPrefixSquareSample.input (family P D H L F C h key hpos)

theorem rows_heq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ)
    (h : FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀ u,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u)) (u : List Bool) :
    HEq ((input P D H L F C h key hpos).system u)
      (((IntegralMixedFramedHistoryFamilyBits.family P D H).state (key u)).sampler.scalarPrefix.rows) := HEq.rfl

theorem complete (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (h : FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀ u,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u)) :
    SquareSampleComplete.Complete (input P D H L F C h key hpos) :=
  IntegralPrefixSquareSample.complete _

theorem access (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (h : FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ u,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u))
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input P D H L F C h key hpos))) :
    (input P D H L F C h key hpos).Access := by
  apply IntegralPrefixSquareSample.access
  have hr := mem_FP_comp hk pairFst_mem_FP
  refine ⟨(a.cap.comp hr).add (UnaryFn.const 1),a.width.comp hr,?_,
    (familyRowMass_binary P a hL hF hC).comp hr,ER⟩
  exact UnaryFn.of_eq ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp hk)
    (fun u=>(family_birth P D H (key u)).symm)

end LeanCanny.Encoding.IntegralFramedCompleteSquare
