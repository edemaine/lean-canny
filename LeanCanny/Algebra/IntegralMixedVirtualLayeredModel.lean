/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualFactorModel
/-! # Natural entries of actual virtual layered-product matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualLayeredBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualMonomialBits IntegralCriticalActualLowMatrixModel
set_option backward.isDefEq.respectTransparency false

noncomputable def dimensionAt (F : Family) (key : List Bool) :=
  (F.ambient key + 4) * FixedWidthPolynomial.count (F.birth key + 1) (F.width key)
noncomputable def dimension (P : Parameters) (F : Family) (q : List Bool) :=
  (IntegralCriticalFlatGenericPowerBits.productFamily (source P F)).dimension q
noncomputable def layeredAt (F : Family) (key : List Bool) (x j k m : ℕ) (hm : m ≠ 0) (r t : ℕ) :=
  entryBits ((IntegralCriticalFlatGenericPowerBits.productFamily (monomialAt F key x j k 0 0 m hm)).matrix []) r t
noncomputable def layeredEntry (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :=
  entryBits ((IntegralCriticalFlatGenericPowerBits.productFamily (source P F)).matrix q) r t
noncomputable def productEntry (P : Parameters) (F : Family) (q : List Bool) :=
  layeredEntry P F q (get P .row q % dimension P F q) (get P .col q % dimension P F q)

theorem dimension_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    dimension P F q = dimensionAt F (IntegralMixedVirtualTaskBits.saved P q) := by
  change (IntegralCriticalFlatGenericPowerBits.productFamily ((source P F).snapshot q)).dimension [] = _
  rw [source_snapshot]
  rfl

theorem layered_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    layeredEntry P F q r t = layeredAt F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .expression q) (get P .derivative q) (get P .sourceIndex q) (modulus P q) (modulus_ne_zero P q) r t := by
  change entryBits ((IntegralCriticalFlatGenericPowerBits.productFamily ((source P F).snapshot q)).matrix []) r t = _
  rw [source_snapshot]
  rfl

theorem dimension_invariance (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q) : dimension P F c = dimension P F q := by
  rw [dimension_snapshot, dimension_snapshot, IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hx]

theorem layeredAt_congr (F : Family) (key key' : List Bool) (x j k m x' j' k' m' r t : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hx : x = x') (hj : j = j') (hk : k = k') (hmod : m = m') :
    layeredAt F key x j k m hm r t = layeredAt F key' x' j' k' m' hm' r t := by
  subst key'; subst x'; subst j'; subst k'; subst m'
  rfl

theorem layered_invariance (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hc : get P .slot15 c = get P .slot15 q) (hm : modulus P c = modulus P q)
    (hx : get P .expression c = get P .expression q) (hj : get P .derivative c = get P .derivative q)
    (hk : get P .sourceIndex c = get P .sourceIndex q) (r t : ℕ) : layeredEntry P F c r t = layeredEntry P F q r t := by
  rw [layered_snapshot, layered_snapshot]
  exact layeredAt_congr F _ _ _ _ _ _ _ _ _ _ r t _ _
    (IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hc) hx hj hk hm

theorem dimension_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) : dimension P F q ≤ numericCap P (RankedHistoryTask.root q) := by
  have HA : (source P F).arity q ≤ P.ambient (RankedHistoryTask.root q) + 1 := by
    change (IntegralMixedVirtualTaskBits.arithmetic P F).arity (pairFst (IntegralCriticalFlatGridBits.termInput P q)) ≤ _
    rw [IntegralCriticalFlatGridBits.termInput_parent]
    exact Nat.add_le_add_right (g.ambient q) 1
  have HR : (source P F).rank q ≤ rankCap P (RankedHistoryTask.root q) := by
    change (IntegralMixedVirtualTaskBits.arithmetic P F).rank (pairFst (IntegralCriticalFlatGridBits.termInput P q)) ≤ _
    rw [IntegralCriticalFlatGridBits.termInput_parent]
    exact IntegralMixedVirtualCaps.rank_le P F g q hv
  change (((source P F).arity q + 2) + 1) * (source P F).rank q ≤ _
  exact IntegralCriticalQueryBounds.product_block_le_of_le _ _ _ _ _ _ _ _ (Nat.add_le_add_right HA 2) HR
end LeanCanny.Algebra.IntegralMixedVirtualLayeredBits
