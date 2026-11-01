/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualCoefficientModel
public import LeanCanny.Algebra.IntegralCriticalActualFactorTransport
/-! # Actual bumped derivative replies from the original integer leaf -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualDerivativeTransport
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualCoefficientModel
open IntegralCriticalActualFactorModel IntegralCriticalActualLowMatrixModel
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap
attribute [local irreducible] IntegralCriticalFlatDerivativeQuery.writer

noncomputable def source (F : Scripts) := IntegralCriticalTotalCreatingBits.CoefficientLeaves.derivative F
noncomputable def access (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) :=
  IntegralCriticalTotalCreatingBits.CoefficientLeaves.derivativeAccess F h.task h.metadata h.objective

theorem originalAt_congr (A B : IntegralHistoryCriticalBits.Family) (k m r t k' m' r' t' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hA : A = B) (hk : k = k') (hmod : m = m') (hr : r = r') (ht : t = t') :
    originalAt A k m hm r t = originalAt B k' m' hm' r' t' := by
  subst B; subst k'; subst m'; subst r'; subst t'
  rfl

theorem original_transport (F : Scripts) (child q : List Bool) (k r t : ℕ)
    (hrank : r < rank F q) (htrank : t < rank F q)
    (hroot : root child = root q)
    (hbirth : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q)
    (hmod : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q)
    (hk : IntegralCriticalHistoryTask.get F.toParameters .sourceIndex child = k)
    (hr : IntegralCriticalHistoryTask.get F.toParameters .row child = r)
    (ht : IntegralCriticalHistoryTask.get F.toParameters .col child = t) :
    original F child = originalAt (IntegralCriticalTotalCreatingBits.atFamily F q) k
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) r t := by
  unfold original
  rw [hk, hr, ht, IntegralCriticalActualFactorModel.rank_invariance F child q hroot hbirth,
    Nat.mod_eq_of_lt hrank, Nat.mod_eq_of_lt htrank]
  exact originalAt_congr _ _ _ _ _ _ _ _ _ _ _ _
    (IntegralCriticalTotalCreatingBits.atFamily_invariance F child q hroot hbirth) rfl hmod rfl rfl

theorem bumped_child (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool) (hv : valid F q) :
    original F (IntegralCriticalFlatDerivativeQuery.writer F.toParameters
      (IntegralDerivativeBits.flatQuery (source F) (IntegralCriticalFlatDerivativeBits.input F.toParameters (source F) q))) =
      (access F h).coefficient
        (IntegralDerivativeBits.flatQuery (source F) (IntegralCriticalFlatDerivativeBits.input F.toParameters (source F) q)) := by
  let p := IntegralDerivativeBits.flatQuery (source F) (IntegralCriticalFlatDerivativeBits.input F.toParameters (source F) q)
  let child := IntegralCriticalFlatDerivativeQuery.writer F.toParameters p
  have HO : IntegralDerivativeBits.original p = q :=
    (IntegralDerivativeBits.flatQuery_original (source F) _).trans
      (IntegralCriticalFlatDerivativeBits.input_original F.toParameters (source F) q)
  have HR : root child = root q := by
    simpa only [child, root, IntegralCriticalFlatHeightBits.root, HO] using
      IntegralCriticalFlatDerivativeQuery.writer_root F.toParameters p
  have HB : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q := by
    simpa only [child, HO] using IntegralCriticalFlatDerivativeQuery.writer_birth F.toParameters p
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q := by
    simpa only [child, HO] using IntegralCriticalFlatDerivativeQuery.writer_modulus F.toParameters p
  have HC := IntegralCriticalFlatDerivativeBits.child_fields F.toParameters (source F) q
    (IntegralCriticalActualCaps.original_grid_cap F q hv) (IntegralCriticalActualFrozenTransport.rank_cap F q)
  let r := IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (source F).toSource .row q
  let t := IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (source F).toSource .col q
  have Hr : r.val < rank F q := by rw [rank_euler]; exact r.isLt
  have Ht : t.val < rank F q := by rw [rank_euler]; exact t.isLt
  change original F child = _
  rw [original_transport F child q _ r.val t.val Hr Ht HR HB HM HC.1 HC.2.1 HC.2.2, original_snapshot]
  rw [IntegralCriticalFlatDerivativeBits.coefficient_reply F.toParameters (source F) (access F h) q]
  exact entryBits_fin (coefficientMatrix (IntegralCriticalTotalCreatingBits.CoefficientLeaves.original F) q
    (IntegralCriticalFlatDerivativeBits.bumpedIndex F.toParameters (source F) q)) r t


theorem derivative_packet (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool) :
    IntegralDerivativeBits.value (source F) (access F h)
      (IntegralCriticalFlatDerivativeBits.input F.toParameters (source F) q) = derivative F q := by
  have H := IntegralDerivativeBits.packet (source F) (access F h) q
    (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
    (IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (source F).toSource .row q)
    (IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (source F).toSource .col q)
  unfold derivative
  rw [derivative_snapshot, rank_euler]
  exact H.trans (entryBits_fin
    (coefficientMatrix (IntegralDerivativeBits.clearedSource (source F)) q
      (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q))
    (IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (source F).toSource .row q)
    (IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (source F).toSource .col q)).symm

theorem derivative_value (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool) (hv : valid F q) :
    (IntegralCriticalFlatDerivativeBits.program F.toParameters (source F)).value (original F)
      (IntegralCriticalFlatDerivativeBits.input F.toParameters (source F) q) = derivative F q :=
  (IntegralDerivativeBits.program_value_at (source F) (access F h) (IntegralCriticalFlatDerivativeQuery.writer F.toParameters)
    (original F) (IntegralCriticalFlatDerivativeBits.input F.toParameters (source F) q)
    (fun _ => bumped_child F h q hv)).trans (derivative_packet F h q)

theorem derivative_output_at (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool)
    (hv : valid F q) (t : ℕ)
    (hh : (IntegralCriticalFlatDerivativeBits.controller F.toParameters (source F)).halted
      (((IntegralCriticalFlatDerivativeBits.controller F.toParameters (source F)).reference (original F))^[t]
        ((IntegralCriticalFlatDerivativeBits.controller F.toParameters (source F)).initial q)) = true) :
    (IntegralCriticalFlatDerivativeBits.controller F.toParameters (source F)).output
      (((IntegralCriticalFlatDerivativeBits.controller F.toParameters (source F)).reference (original F))^[t]
        ((IntegralCriticalFlatDerivativeBits.controller F.toParameters (source F)).initial q)) = derivative F q := by
  simp only [IntegralCriticalFlatDerivativeBits.controller, RecursiveController.Controller.prepare_halted_iterate,
    SingleCall.Program.controller] at hh
  simpa only [IntegralCriticalFlatDerivativeBits.controller, RecursiveController.Controller.prepare_output_iterate,
    SingleCall.Program.controller] using
      ((IntegralCriticalFlatDerivativeBits.program F.toParameters (source F)).output_when_halted (original F)
        (IntegralCriticalFlatDerivativeBits.input F.toParameters (source F) q) t hh).trans (derivative_value F h q hv)

end LeanCanny.Algebra.IntegralCriticalActualDerivativeTransport
