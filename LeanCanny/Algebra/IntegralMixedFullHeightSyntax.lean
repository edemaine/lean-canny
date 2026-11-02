/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOriginalHeightControls
/-! # Immutable command syntax supplies the selected-rule height hypotheses -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHeightBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

def RuleBounds {n : ℕ} (C L : ℕ) (r : IntegralMixedCriticalSweep.Rule n) : Prop :=
  (∀ i, (r.critical.heights i).nodes ≤ L) ∧
  (∀ i, (r.critical.heights i).CoefficientsBound C) ∧
  (∀ i, (r.critical.scales i).natAbs.size ≤ C) ∧ r.slope.natAbs.size ≤ C

theorem creating_mem (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool)
    (c : Command (D.spatial (pairFst key)) (P.width (pairFst key)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D key = some c) : c ∈ D.rules (pairFst key) :=
  List.mem_reverse.mp (List.mem_of_getElem? hc)

theorem selection_bounds (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (C L : List Bool → ℕ)
    (hcommand : ∀ root, ∀ c ∈ D.rules root, IntegralMixedFullScriptHeight.CommandBounds (C root) (L root) c)
    (hfallback : ∀ key, RuleBounds (C (pairFst key)) (L (pairFst key)) (D.fallback key).rule) (key : List Bool) :
    RuleBounds (C (pairFst key)) (L (pairFst key)) (IntegralMixedFullHistoryFamilyBits.selection P D key).rule := by
  unfold IntegralMixedFullHistoryFamilyBits.selection
  split
  · rename_i r k d ha hd hc
    exact hcommand (pairFst key) (.cut r k d ha hd) (creating_mem P D key _ hc)
  · exact hfallback key

theorem inputs_of_syntax (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (C L : List Bool → ℕ)
    (hc : ∀ root e, ((D.spatial root).low.coeff e).natAbs ≤ 2 ^ C root)
    (hp : ∀ root, (D.spatial root).leading.natAbs.size ≤ C root)
    (hcommand : ∀ root, ∀ c ∈ D.rules root, IntegralMixedFullScriptHeight.CommandBounds (C root) (L root) c)
    (hfallback : ∀ key, RuleBounds (C (pairFst key)) (L (pairFst key)) (D.fallback key).rule) : Inputs P D C L where
  coefficient := hc
  leading := hp
  command := hcommand
  nodes key := (selection_bounds P D C L hcommand hfallback key).1
  expression key := (selection_bounds P D C L hcommand hfallback key).2.1
  scale key := (selection_bounds P D C L hcommand hfallback key).2.2.1
  slope key := (selection_bounds P D C L hcommand hfallback key).2.2.2
end LeanCanny.Algebra.IntegralMixedFullHeightBits
