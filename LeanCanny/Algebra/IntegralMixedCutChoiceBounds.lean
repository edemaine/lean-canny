/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutChoiceFamily
public import LeanCanny.Algebra.IntegralMixedFramedChoiceCoefficientTransport
public import LeanCanny.Algebra.IntegralMixedFramedRawHeight
/-! # One original height ceiling covers every finite lower-choice probe

Only Kind changes. The same actual bank/source/rule bounds apply literally,
so no new degree, annihilator norm or interpreted coefficient bound is input.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutChoiceFamilyBits
open IntegralMixedCutSource IntegralMixedCoordinateBounds

noncomputable def originalBounds (F : Family) (k : ℕ) (H : OriginalBounds F) : OriginalBounds (family F k) where
  bankHeight := H.bankHeight
  sourceHeight := H.sourceHeight
  rank := H.rank
  sourceWidth := H.sourceWidth
  spatialDegree := H.spatialDegree
  nodes := H.nodes
  bank := H.bank
  coefficient := H.coefficient
  rank_bound := H.rank_bound
  width_bound := H.width_bound
  degree_bound := H.degree_bound
  leading := H.leading
  expression_nodes := H.expression_nodes
  expression_coefficients := H.expression_coefficients
  scales := H.scales
  slope := H.slope
  source_le_bank := H.source_le_bank

end LeanCanny.Algebra.IntegralMixedCutChoiceFamilyBits

namespace LeanCanny.Algebra.IntegralMixedFramedChoiceCoefficientBits
open LeanCanny.Encoding IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

theorem coefficient_root_height (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (key : List Bool) (choice k : ℕ)
    (r s : Fin (count ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth key)
      ((IntegralMixedFramedHistoryFamilyBits.family P D H).width key))) :
    (coefficient P D H key choice k r s).natAbs≤2^IntegralMixedFramedRawHeight.rootCeiling P L F C (pairFst key) := by
  let G:=IntegralMixedCutChoiceFamilyBits.family (IntegralMixedFramedHistoryFamilyBits.family P D H) choice
  let I:=IntegralMixedCutStepHeight.indices G
  let HB:=IntegralMixedCutChoiceFamilyBits.originalBounds (IntegralMixedFramedHistoryFamilyBits.family P D H) choice
    (IntegralMixedFramedOriginalBounds.originalBounds P D H L F C hs hF hf)
  have HX:=IntegralMixedCutHeightProfile.coefficient_height G I HB key
    (IntegralMixedFramedOriginalBounds.family_rank_bound P D H key) k r s
  change (coefficient P D H key choice k r s).natAbs≤2^IntegralMixedFramedRawHeight.localHeight P L F C key at HX
  exact HX.trans (Nat.pow_le_pow_right (by decide) (IntegralMixedFramedRawHeight.local_le_root P L F C key))

end LeanCanny.Algebra.IntegralMixedFramedChoiceCoefficientBits
