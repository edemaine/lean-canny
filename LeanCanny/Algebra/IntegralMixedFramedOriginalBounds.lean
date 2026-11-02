/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight
public import LeanCanny.Algebra.IntegralMixedFullHeightSyntax
/-! # Original raw-cut inputs from actual changing-source histories

Bank and current-source bounds are derived from full script syntax and the
original default instruction. Cut-rule syntax comes from its creating command.
Only noncut fallbacks require separate original affine-expression syntax bounds.
Characteristic ranks occur in coefficient heights, never as spatial degrees.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOriginalBounds
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedFramedStepHeight
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical

def sourceHeight (P : Parameters) (L F C : List Bool → ℕ) (key : List Bool) : ℕ :=
  F (pairFst key)*familyHeight P L F C key+1

def bankHeight (P : Parameters) (L F C : List Bool → ℕ) (key : List Bool) : ℕ :=
  (F (pairFst key)+2)*familyHeight P L F C key

def rootRank (P : Parameters) (root : List Bool) : ℕ := IntegralMixedFullScriptHeight.rank (P.cap root+1) (P.width root)

def FallbackBounds (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L C : List Bool → ℕ) (key : List Bool) : Prop :=
  match (instruction P D key).command with
  | .cut .. => True
  | _ => IntegralMixedFullHeightBits.RuleBounds (C (pairFst key)+1) (L (pairFst key)) (H.fallback key).rule

theorem rule_bounds_mono {n C C' L : ℕ} (hC : C≤C') (r : IntegralMixedCriticalSweep.Rule n)
    (h : IntegralMixedFullHeightBits.RuleBounds C L r) : IntegralMixedFullHeightBits.RuleBounds C' L r :=
  ⟨h.1,fun i => expression_coefficients_mono hC _ (h.2.1 i),fun i => (h.2.2.1 i).trans hC,h.2.2.2.trans hC⟩

theorem selected_rule_bounds (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (h : FamilyInputs P D L F C) (hF : ∀ root, 1≤F root)
    (hfallback : ∀ key, FallbackBounds P D H L C key) (key : List Bool) :
    IntegralMixedFullHeightBits.RuleBounds (sourceHeight P L F C key) (L (pairFst key)) (selection P D H key).rule := by
  have HI := family_instruction_bounds P D L F C h key
  have Hseed : C (pairFst key)+1≤sourceHeight P L F C key := by
    have HG := source_le_height (P.ambient (pairFst key)) (P.cap (pairFst key)+1) (P.width (pairFst key))
      (P.sourceWidth (pairFst key)) (P.degree (pairFst key)) (L (pairFst key)) (F (pairFst key)) (C (pairFst key))
      (IntegralMixedFullHistoryFamilyBits.prefixLength P key)
    have HF := hF (pairFst key)
    change C (pairFst key)+1≤F (pairFst key)*familyHeight P L F C key+1
    change C (pairFst key)+1≤familyHeight P L F C key at HG
    nlinarith
  unfold selection
  cases hc : (instruction P D key).command with
  | integer p hp hd =>
    have HB : IntegralMixedFullHeightBits.RuleBounds (C (pairFst key)+1) (L (pairFst key)) (H.fallback key).rule := by
      simpa only [FallbackBounds,hc] using hfallback key
    exact rule_bounds_mono Hseed _ HB
  | critical r =>
    have HB : IntegralMixedFullHeightBits.RuleBounds (C (pairFst key)+1) (L (pairFst key)) (H.fallback key).rule := by
      simpa only [FallbackBounds,hc] using hfallback key
    exact rule_bounds_mono Hseed _ HB
  | cut r k d ha hd =>
    have HB := HI.command
    rw [hc] at HB
    exact HB

theorem family_rank_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    count ((family P D H).birth key+2) ((family P D H).width key)≤rootRank P (pairFst key) := by
  have HB := (family P D H).birth_bound key
  change (family P D H).birth key≤P.cap (pairFst key)+1 at HB
  exact Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega : (family P D H).birth key+2≤P.cap (pairFst key)+1+2)

noncomputable def originalBounds (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (h : FamilyInputs P D L F C) (hF : ∀ root, 1≤F root)
    (hfallback : ∀ key, FallbackBounds P D H L C key) :
    IntegralMixedCoordinateBounds.OriginalBounds (family P D H) where
  bankHeight := bankHeight P L F C
  sourceHeight := sourceHeight P L F C
  rank key := rootRank P (pairFst key)
  sourceWidth key := P.sourceWidth (pairFst key)
  spatialDegree key := P.degree (pairFst key)
  nodes key := L (pairFst key)
  bank := family_charged_bank_bounds P D H L F C h
  coefficient key := (family_instruction_bounds P D L F C h key).low
  rank_bound key := (Nat.pow_le_pow_right (Nat.two_pow_pos _)
    (by omega : (family P D H).birth key+1≤(family P D H).birth key+2)).trans (family_rank_bound P D H key)
  width_bound key := (family_instruction_bounds P D L F C h key).width
  degree_bound key := (family_instruction_bounds P D L F C h key).degree
  leading key := (family_instruction_bounds P D L F C h key).leading
  expression_nodes key := (selected_rule_bounds P D H L F C h hF hfallback key).1
  expression_coefficients key := (selected_rule_bounds P D H L F C h hF hfallback key).2.1
  scales key := (selected_rule_bounds P D H L F C h hF hfallback key).2.2.1
  slope key := (selected_rule_bounds P D H L F C h hF hfallback key).2.2.2
  source_le_bank key := by
    have HG := height_positive (P.ambient (pairFst key)) (P.cap (pairFst key)+1) (P.width (pairFst key))
      (P.sourceWidth (pairFst key)) (P.degree (pairFst key)) (L (pairFst key)) (F (pairFst key)) (C (pairFst key))
      (IntegralMixedFullHistoryFamilyBits.prefixLength P key)
    change 1≤familyHeight P L F C key at HG
    change F (pairFst key)*familyHeight P L F C key+1+1≤(F (pairFst key)+2)*familyHeight P L F C key
    nlinarith

end LeanCanny.Algebra.IntegralMixedFramedOriginalBounds
