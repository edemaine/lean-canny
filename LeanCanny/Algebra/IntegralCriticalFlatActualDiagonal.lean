/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualMomentRoutes
/-! # The selected relative diagonal child reads the actual action diagonal -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualDiagonalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess IntegralCriticalTotalCreatingBits.atFamily

theorem child_value (F : Scripts) (h : Controls F) (p : List Bool)
    (hv : IntegralCriticalTotalCompanionBits.valid F (original p)) (hd : selector (characteristic F) p = [false, true]) :
    IntegralCriticalFlatActualActionBits.value F
      (IntegralCriticalFlatBerkowitzQuery.entryWriter F.toParameters (characteristic F) (diagonalQuery (characteristic F) p)) =
      (characteristicAccess F h).entry (diagonalQuery (characteristic F) p) := by
  have HS : stage (characteristic F) p < (characteristic F).dimension (original p) :=
    ((Berkowitz.QueryBits.select_diagonal_iff _ _ _ _ _).mp ((selector_eq _ _).symm.trans hd)).2.1
  let i : Fin ((characteristic F).dimension (original p)) := ⟨_, HS⟩
  let r := basisIndex (characteristic F) basisRowCode p
  let t := basisIndex (characteristic F) basisColCode p
  exact (IntegralCriticalFlatActualMomentRoutes.actionChild_value F (original p) hv i i r t).trans
    ((characteristicAccess F h).entry_eq (original p) i i r t).symm

end LeanCanny.Algebra.IntegralCriticalFlatActualDiagonalBits
