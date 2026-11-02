/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionSource
public import LeanCanny.Algebra.PaddedIntegralRowSpace
public import LeanCanny.Encoding.IntegralFramedCreatingCut
/-! # An actual creating cut supplies exactly its normalized factor row -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutSourceRow
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family instruction selection)
open IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool)
local notation "G" => family P D H
local notation "x" => IntegralMixedCutSource.Family.state G key
local notation "hm" => IntegralMixedCutSource.Family.birth_bound G key

theorem source_step :
    HEq (PaddedIntegralRowBits.polynomial (IntegralMixedFramedCompanionBits.source P D H)
      (fun key=>P.cap (pairFst key)+1) key)
      ((UniformIntegralPrefix.step (x).sampler.scalarPrefix hm (Nat.two_pow_pos ((G).width key))
        (IntegralMixedFullHistoryScript.polynomial x hm (instruction P D key).command)
        (IntegralMixedFullHistoryScript.degree x hm (instruction P D key).command)).rows 0) := HEq.rfl

theorem cut_row (hcut : IntegralFramedCreatingCut.IsCut (instruction P D key).command) :
    HEq (PaddedIntegralRowBits.polynomial (IntegralMixedFramedCompanionBits.source P D H)
      (fun key=>P.cap (pairFst key)+1) key)
      (UniformIntegralPrefixRows.rows ((G).cap key) (x).sampler.scalarPrefix.rows (x).sampler.scalarPrefix.basis
        (IntegralMixedHistory.normalizedScalarPolynomial x
          (IntegralMixedCutMatrix.raw x hm ((G).rule key) ((G).kind key) ((G).degree key)) ((G).degree key)) ((G).degree key) 0) := by
  cases hc:(instruction P D key).command with
  | integer p hp hd => simp only [hc,IntegralFramedCreatingCut.IsCut] at hcut
  | critical r => simp only [hc,IntegralFramedCreatingCut.IsCut] at hcut
  | cut r k d ha hd =>
    have HS : selection P D H key=⟨r,k,d,ha⟩ := by
      unfold selection
      rw [hc]
    apply (source_step P D H key).trans
    change HEq (UniformIntegralPrefixRows.rows ((G).cap key) (x).sampler.scalarPrefix.rows (x).sampler.scalarPrefix.basis
      (IntegralMixedFullHistoryScript.polynomial x hm (instruction P D key).command)
      (IntegralMixedFullHistoryScript.degree x hm (instruction P D key).command) 0)
      (UniformIntegralPrefixRows.rows ((G).cap key) (x).sampler.scalarPrefix.rows (x).sampler.scalarPrefix.basis
        (IntegralMixedHistory.normalizedScalarPolynomial x
          (IntegralMixedCutMatrix.raw x hm (selection P D H key).rule (selection P D H key).kind (selection P D H key).degree)
            (selection P D H key).degree) (selection P D H key).degree 0)
    rw [hc,HS]
    rfl

end LeanCanny.Encoding.IntegralFramedCutSourceRow
