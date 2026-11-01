/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationMomentQuery
public import LeanCanny.Algebra.IntegralMixedNormalizationRelativeModel
public import LeanCanny.Algebra.IntegralBerkowitzBlockControllerLocal
public import LeanCanny.Computation.SingleCallRequery
/-! # Actual normalization factors use their selected top entry or moment -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

noncomputable def factorProgram (P : Parameters) (F : Family) :=
  (entryController (source P F) (entryTask P .clearedHeight) (momentTask P)).requery
    (IntegralCriticalFlatRelativeFactorBits.packet P)

theorem factor_controls (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (factorProgram P F).Controls :=
  SingleCall.Program.requery_controls _
    (entryController_controls (source P F) (access P a F h) _ _ (entryTask_FP P a .clearedHeight) (momentTask_FP P a))
    _ (IntegralCriticalFlatRelativeFactorBits.packet_FP P a)

theorem diagonal_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (original z)) (hd : selector (source P F) z = [false, true]) :
    value P F (entryTask P .clearedHeight (diagonalQuery (source P F) z)) = (access P a F h).entry (diagonalQuery (source P F) z) := by
  have HS : stage (source P F) z < (source P F).dimension (original z) :=
    ((Berkowitz.QueryBits.select_diagonal_iff _ _ _ _ _).mp ((selector_eq _ _).symm.trans hd)).2.1
  let i : Fin ((source P F).dimension (original z)) := ⟨_, HS⟩
  let r := basisIndex (source P F) basisRowCode z
  let t := basisIndex (source P F) basisColCode z
  exact (entryTask_value P F g .clearedHeight (original z) hv i i r t).trans
    ((access P a F h).entry_eq (original z) i i r t).symm

noncomputable def outer (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  outerPacket (source P F) (IntegralCriticalFlatRelativeFactorBits.packet P q)
noncomputable def diagonalChild (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  entryTask P .clearedHeight (diagonalQuery (source P F) (outer P F q))
noncomputable def momentChild (P : Parameters) (F : Family) (q : List Bool) : List Bool := momentTask P (outer P F q)

theorem outer_parent (P : Parameters) (F : Family) (q : List Bool) : original (outer P F q) = q :=
  IntegralCriticalFlatRelativeFactorBits.outer_original _ _ _

theorem factor_value_at (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q)
    (hd : selector (source P F) (outer P F q) = [false, true] →
      answer (diagonalChild P F q) = value P F (diagonalChild P F q))
    (hm : selector (source P F) (outer P F q) = [true, true] →
      answer (momentChild P F q) = momentValue P F (momentChild P F q))
    (i j : Fin (powerDimension (source P F) q)) (hi : get P .row q = i.val) (hj : get P .col q = j.val) :
    (factorProgram P F).value answer q = factorValue P F q := by
  have HP : IntegralMixedVirtualCaps.valid P (original (outer P F q)) := by rw [outer_parent]; exact hv
  have HE : (factorProgram P F).value answer q =
      entryProgram (source P F) (access P a F h) (IntegralCriticalFlatRelativeFactorBits.packet P q) := by
    rw [factorProgram, SingleCall.Program.requery_value]
    exact entryController_value_at (source P F) (access P a F h) _ _ answer _
      (fun hg => (hd hg).trans (diagonal_value P a F h g (outer P F q) HP hg))
      (fun hg => (hm hg).trans (relative_moment_child P F q))
  have HC : entryProgram (source P F) (access P a F h) (IntegralCriticalFlatRelativeFactorBits.packet P q) =
      residueBits (((source P F).powerMatrix q i j : ℤ) : ZMod ((source P F).modulus q)) := by
    rw [IntegralCriticalFlatRelativeFactorBits.packet, hi, hj]
    exact entry_correct _ _ q i j
  have HF : factorValue P F q = residueBits (((source P F).powerMatrix q i j : ℤ) : ZMod (modulus P q)) := by
    unfold factorValue
    rw [power_snapshot, hi, hj, IntegralCriticalTotalSnapshotBits.integerEntry_fin]
  exact HE.trans (HC.trans HF.symm)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
