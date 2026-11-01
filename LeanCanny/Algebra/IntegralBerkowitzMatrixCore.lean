/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalTotalMomentSnapshot

/-! # Freezing the matrix data used by characteristic and moment arithmetic

Output coefficients, moduli and selected output basis labels do not enter
the matrix. A frozen core records that distinction by construction.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzMatrixCore
open IntegralBerkowitzBlockBits IntegralCriticalTotalMomentSnapshotBits

noncomputable def freeze (S : Source) (q : List Bool) : Source where
  dimension _ := S.dimension q
  rank _ := S.rank q
  carrier _ := S.carrier q
  ring _ := S.ring q
  nontrivial _ := S.nontrivial q
  basis _ := S.basis q
  matrix _ := S.matrix q
  modulus _ := 1
  modulus_ne_zero _ := by decide
  coefficient _ := 0
  basisRow _ := ⟨0, S.rank_pos q⟩
  basisCol _ := ⟨0, S.rank_pos q⟩

theorem atEntry_freeze (S : Source) (q : List Bool) (s r t : ℕ) :
    atEntry S q s r t = atEntry (freeze S q) [] s r t := rfl

theorem momentEntry_requery (P : IntegralCriticalHistoryTask.Parameters) (S : Source) (q : List Bool) (r t : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry ((IntegralCriticalFlatMomentBits.source P S).powerMatrix q) r t =
      atEntry S q (stage S (IntegralCriticalFlatMomentBits.packet P q)) r t := by
  change IntegralCriticalTotalSnapshotBits.integerEntry
    ((momentFamily S).powerMatrix (IntegralCriticalFlatMomentBits.packet P q)) r t = _
  rw [momentEntry_at, IntegralCriticalFlatMomentBits.packet_parent]

end LeanCanny.Algebra.IntegralBerkowitzMatrixCore
