/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOriginalBounds
public import LeanCanny.Algebra.IntegralMixedCutHeightControls
/-! # Uniform original-root ceilings for actual framed raw and top matrices

All four cut kinds use the actual saved prefix and selected creating source.
The root ceiling evaluates the bank schedule at its original horizon. Its
binary controls use original metadata; no raw/current/top matrix evaluator or
matrix-height oracle is a premise, and the spatial degree remains unchanged.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRawHeight
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedStepHeight
open IntegralMixedFramedOriginalBounds
open scoped Classical

def rootFactor (P : Parameters) (L : List Bool → ℕ) (root : List Bool) : ℕ :=
  IntegralMixedCutHeightProfile.factor (P.ambient root) (rootRank P root) (P.sourceWidth root)
    (P.degree root) (P.cap root+1) (L root)

def localHeight (P : Parameters) (L F C : List Bool → ℕ) (key : List Bool) : ℕ :=
  rootFactor P L (pairFst key)*bankHeight P L F C key

def rootCeiling (P : Parameters) (L F C : List Bool → ℕ) (root : List Bool) : ℕ :=
  rootFactor P L root*((F root+2)*IntegralMixedFramedStepHeight.height (P.ambient root) (P.cap root+1)
    (P.width root) (P.sourceWidth root) (P.degree root) (L root) (F root) (C root) (P.cap root+1))

theorem local_le_root (P : Parameters) (L F C : List Bool → ℕ) (key : List Bool) :
    localHeight P L F C key≤rootCeiling P L F C (pairFst key) := by
  have Hbirth : IntegralMixedFullHistoryFamilyBits.prefixLength P key≤P.cap (pairFst key)+1 := min_le_right _ _
  have HG : familyHeight P L F C key≤IntegralMixedFramedStepHeight.height (P.ambient (pairFst key))
      (P.cap (pairFst key)+1) (P.width (pairFst key)) (P.sourceWidth (pairFst key)) (P.degree (pairFst key))
      (L (pairFst key)) (F (pairFst key)) (C (pairFst key)) (P.cap (pairFst key)+1) := by
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right
      (IntegralMixedFramedStepHeight.growth_pos _ _ _ _ _ _ _) Hbirth)
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ HG)

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool → ℕ) (h : FamilyInputs P D L F C) (hF : ∀ root, 1≤F root)
  (hfallback : ∀ key, FallbackBounds P D H L C key)
include h hF hfallback

theorem allRaw_height_le (key : List Bool) :
    IntegralMixedAllRawHeightBounds.height (family P D H) (IntegralMixedCutStepHeight.indices (family P D H))
      (originalBounds P D H L F C h hF hfallback) key≤localHeight P L F C key :=
  IntegralMixedCutHeightProfile.height_le (family P D H) (IntegralMixedCutStepHeight.indices (family P D H))
    (originalBounds P D H L F C h hF hfallback) key (family_rank_bound P D H key)

theorem coefficient_height (key : List Bool) (k : ℕ)
    (r t : Fin (count ((family P D H).birth key) ((family P D H).width key))) :
    (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state key) ((family P D H).birth_bound key)
      ((family P D H).rule key) ((family P D H).kind key) k r t).natAbs≤2^localHeight P L F C key :=
  IntegralMixedCutHeightProfile.coefficient_height (family P D H) (IntegralMixedCutStepHeight.indices (family P D H))
    (originalBounds P D H L F C h hF hfallback) key (family_rank_bound P D H key) k r t

theorem coefficient_root_height (key : List Bool) (k : ℕ)
    (r t : Fin (count ((family P D H).birth key) ((family P D H).width key))) :
    (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state key) ((family P D H).birth_bound key)
      ((family P D H).rule key) ((family P D H).kind key) k r t).natAbs≤2^rootCeiling P L F C (pairFst key) :=
  (coefficient_height P D H L F C h hF hfallback key k r t).trans
    (Nat.pow_le_pow_right (by decide) (local_le_root P L F C key))

theorem top_root_height (key : List Bool) (r t : Fin (IntegralMixedNormalizationTopBits.dimension (family P D H) key)) :
    (IntegralMixedNormalizationTopBits.top (family P D H) key r t).natAbs≤2^rootCeiling P L F C (pairFst key) :=
  coefficient_root_height P D H L F C h hF hfallback key ((family P D H).degree key) r t

theorem natural_top_root_height (key : List Bool) (r t : ℕ) :
    (IntegralCriticalTotalSnapshotBits.integerEntry (IntegralMixedNormalizationTopBits.top (family P D H) key) r t).natAbs≤
      2^rootCeiling P L F C (pairFst key) := by
  unfold IntegralCriticalTotalSnapshotBits.integerEntry
  split_ifs with hr ht
  · exact top_root_height P D H L F C h hF hfallback key ⟨r,hr⟩ ⟨t,ht⟩
  all_goals exact Nat.zero_le _

noncomputable def rawBounds : IntegralMixedCutSource.RawBounds (family P D H) where
  height key := rootCeiling P L F C (pairFst key)
  bound := coefficient_root_height P D H L F C h hF hfallback

end LeanCanny.Algebra.IntegralMixedFramedRawHeight
