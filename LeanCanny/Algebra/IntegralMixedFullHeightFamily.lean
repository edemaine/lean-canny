/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHeightControls
public import LeanCanny.Algebra.IntegralMixedFullHistoryFamily
/-! # Original-only height bounds for every actual saved full-history bank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Inputs (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (C L : List Bool → ℕ) : Prop where
  coefficient : ∀ root e, ((D.spatial root).low.coeff e).natAbs ≤ 2 ^ C root
  leading : ∀ root, (D.spatial root).leading.natAbs.size ≤ C root
  command : ∀ root, ∀ c ∈ D.rules root, IntegralMixedFullScriptHeight.CommandBounds (C root) (L root) c
  nodes : ∀ key i, ((IntegralMixedFullHistoryFamilyBits.selection P D key).rule.critical.heights i).nodes ≤ L (pairFst key)
  expression : ∀ key i, ((IntegralMixedFullHistoryFamilyBits.selection P D key).rule.critical.heights i).CoefficientsBound (C (pairFst key))
  scale : ∀ key i, ((IntegralMixedFullHistoryFamilyBits.selection P D key).rule.critical.scales i).natAbs.size ≤ C (pairFst key)
  slope : ∀ key, (IntegralMixedFullHistoryFamilyBits.selection P D key).rule.slope.natAbs.size ≤ C (pairFst key)

def cap (P : Parameters) (root : List Bool) := P.cap root + 1
def rank (P : Parameters) (root : List Bool) := IntegralMixedFullScriptHeight.rank (cap P root) (P.width root)
def bankCeiling (P : Parameters) (C L : List Bool → ℕ) (root : List Bool) :=
  IntegralMixedFullScriptHeight.height (P.ambient root) (cap P root) (P.width root) (P.sourceWidth root) (P.degree root)
    (L root) (C root) (cap P root + 1)
def factor (P : Parameters) (L : List Bool → ℕ) (root : List Bool) :=
  IntegralMixedCutHeightProfile.factor (P.ambient root) (rank P root) (P.sourceWidth root) (P.degree root) (cap P root) (L root)
def height (P : Parameters) (C L : List Bool → ℕ) (root : List Bool) := factor P L root * bankCeiling P C L root

theorem bank_bound (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (C L : List Bool → ℕ)
    (h : Inputs P D C L) (key : List Bool) :
    ((IntegralMixedFullHistoryFamilyBits.family P D).state key).bank.Bounds (bankCeiling P C L (pairFst key)) := by
  let root := pairFst key
  let m := IntegralMixedFullHistoryFamilyBits.prefixLength P key
  have HM : m ≤ cap P root + 1 := (min_le_right _ _).trans (Nat.le_succ _)
  have HB := IntegralMixedFullScriptHeight.paddedRun_bounds (IntegralMixedFullHistoryFamilyBits.initial P D root)
    (P.sourceWidth root) (P.degree root) (L root) (C root) (h.coefficient root) (h.leading root)
    (D.sourceWidth root) (D.degree_eq root).le (D.scalar_cap root) (D.rules root) m HM (h.command root)
  exact HB.mono (IntegralMixedFullScriptHeight.height_mono _ _ _ _ _ _ _ HM)

theorem auxiliary_rank_bound (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    count ((IntegralMixedFullHistoryFamilyBits.family P D).birth key + 2) ((IntegralMixedFullHistoryFamilyBits.family P D).width key) ≤ rank P (pairFst key) := by
  rw [IntegralMixedFullHistoryFamilyBits.family_birth]
  apply Nat.pow_le_pow_right (Nat.two_pow_pos _)
  exact Nat.add_le_add_right (min_le_right _ _) 2

noncomputable def bounds (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (C L : List Bool → ℕ)
    (h : Inputs P D C L) : IntegralMixedCoordinateBounds.OriginalBounds (IntegralMixedFullHistoryFamilyBits.family P D) where
  bankHeight key := bankCeiling P C L (pairFst key)
  sourceHeight key := C (pairFst key)
  rank key := rank P (pairFst key)
  sourceWidth key := P.sourceWidth (pairFst key)
  spatialDegree key := P.degree (pairFst key)
  nodes key := L (pairFst key)
  bank := bank_bound P D C L h
  coefficient key := h.coefficient (pairFst key)
  rank_bound key := (Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega : (IntegralMixedFullHistoryFamilyBits.family P D).birth key + 1 ≤
    (IntegralMixedFullHistoryFamilyBits.family P D).birth key + 2)).trans (auxiliary_rank_bound P D key)
  width_bound key := D.sourceWidth (pairFst key)
  degree_bound key := (D.degree_eq (pairFst key)).le
  leading key := h.leading (pairFst key)
  expression_nodes := h.nodes
  expression_coefficients := h.expression
  scales := h.scale
  slope := h.slope
  source_le_bank key := IntegralMixedFullScriptHeight.source_le_height _ _ _ _ _ _ _ _

theorem top_bound (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (C L : List Bool → ℕ)
    (h : Inputs P D C L) (key : List Bool) (u v : Fin (IntegralMixedNormalizationTopBits.dimension (IntegralMixedFullHistoryFamilyBits.family P D) key)) :
    (IntegralMixedNormalizationTopBits.top (IntegralMixedFullHistoryFamilyBits.family P D) key u v).natAbs ≤ 2 ^ height P C L (pairFst key) :=
  IntegralMixedCutHeightProfile.coefficient_height (IntegralMixedFullHistoryFamilyBits.family P D) (IntegralMixedCutStepHeight.indices _)
    (bounds P D C L h) key (auxiliary_rank_bound P D key) ((IntegralMixedFullHistoryFamilyBits.family P D).degree key) u v

theorem top_height (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (C L : List Bool → ℕ)
    (h : Inputs P D C L) (q : List Bool)
    (u v : Fin (IntegralMixedNormalizationTopBits.dimension (IntegralMixedFullHistoryFamilyBits.family P D) (IntegralMixedVirtualTaskBits.saved P q))) :
    (IntegralMixedNormalizationTopBits.top (IntegralMixedFullHistoryFamilyBits.family P D) (IntegralMixedVirtualTaskBits.saved P q) u v).natAbs ≤
      2 ^ height P C L (RankedHistoryTask.root q) := by
  have HB := top_bound P D C L h (IntegralMixedVirtualTaskBits.saved P q) u v
  exact HB.trans_eq (congrArg (fun root => 2 ^ height P C L root) (IntegralMixedFullHistoryFamilyBits.saved_root P q))
end LeanCanny.Algebra.IntegralMixedFullHeightBits
