/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullback
/-! # Literal creating-source transport through an augmented original root -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction prefixLength)
open scoped Classical

theorem profile_key (P : Parameters) (project : List Bool → List Bool) (extra : List Bool → ℕ) (q : List Bool) :
    profile P project extra (IntegralMixedFramedCompanionBits.profile (parameters P project extra) q)=
      IntegralMixedFramedCompanionBits.profile P (key project q) := by
  apply IntegralMixedFramedCompanionBits.PrefixKey.ext
  · exact (key_root project q).symm
  · exact (key_prefix P project extra q).symm

private theorem matrix_congr {S T : PaddedIntegralGeneratorSource.Source} (h : S=T) :
    HEq (S.matrix []) (T.matrix []) := by cases h; rfl

theorem source_matrix (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool → List Bool) (extra : List Bool → ℕ)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (parameters P project extra) (plan P D project extra)) (q : List Bool) :
    HEq ((IntegralMixedFramedCompanionBits.source (parameters P project extra) (plan P D project extra)
      Hnew).matrix q)
      ((IntegralMixedFramedCompanionBits.source P D H).matrix (key project q)) := by
  have HA := IntegralMixedFramedCompanionBits.source_matrix_atPrefix (parameters P project extra)
    (plan P D project extra) Hnew q
  have HB := IntegralMixedFramedCompanionBits.source_matrix_atPrefix P D H (key project q)
  have HS := source_atPrefix P D project extra (IntegralMixedFramedCompanionBits.profile (parameters P project extra) q)
  rw [profile_key] at HS
  exact HA.trans ((matrix_congr HS).trans HB.symm)

end LeanCanny.Algebra.IntegralMixedFramedRootPullback
