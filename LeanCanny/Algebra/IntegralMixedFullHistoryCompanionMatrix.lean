/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryCompanion
/-! # Fixed integer matrices compare creating polynomials without changing carriers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHistoryCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

noncomputable def matrixAt (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool)
    (p : Polynomial ((bank P D).state key).sampler.scalarPrefix.carrier) (d : ℕ) :
    Matrix (Fin (count ((bank P D).birth key + 1) ((bank P D).width key)))
      (Fin (count ((bank P D).birth key + 1) ((bank P D).width key))) ℤ := by
  let _ := ((bank P D).state key).sampler.scalarPrefix.ring
  let _ := ((bank P D).state key).sampler.scalarPrefix.nontrivial
  exact Algebra.leftMulMatrix (PaddedIntegralParameterExtension.coordinateBasis
    ((bank P D).state key).sampler.scalarPrefix.basis p d).finBasis (AdjoinRoot.root _)

theorem source_matrix (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    (source P D).matrix key = matrixAt P D key ((source P D).polynomial key) ((source P D).degree key) := rfl

theorem polynomial_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool)
    (c : Command (D.spatial (pairFst key)) (P.width (pairFst key)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D key = some c) :
    (source P D).polynomial key = IntegralMixedFullHistoryScript.polynomial ((bank P D).state key)
      ((bank P D).birth_bound key) c := by
  change IntegralMixedFullHistoryScript.polynomial ((bank P D).state key) ((bank P D).birth_bound key)
    ((IntegralMixedFullHistoryFamilyBits.creating P D key).getD defaultCommand) = _
  rw [hc]
  rfl

theorem degree_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool)
    (c : Command (D.spatial (pairFst key)) (P.width (pairFst key)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D key = some c) :
    (source P D).degree key = IntegralMixedFullHistoryScript.degree ((bank P D).state key)
      ((bank P D).birth_bound key) c := by
  change IntegralMixedFullHistoryScript.degree ((bank P D).state key) ((bank P D).birth_bound key)
    ((IntegralMixedFullHistoryFamilyBits.creating P D key).getD defaultCommand) = _
  rw [hc]
  rfl

end LeanCanny.Algebra.IntegralMixedFullHistoryCompanionBits
