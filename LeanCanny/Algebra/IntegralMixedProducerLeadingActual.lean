/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerActual
public import LeanCanny.Algebra.IntegralMixedPhysicalCompanionActual
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionActual
/-! # Every native producer-leading branch is its literal creating-command scalar -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHistoryCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

noncomputable def leading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) : ℤ :=
  IntegralMixedFullHistoryScript.leading ((bank P D).state key) ((bank P D).birth_bound key)
    (IntegralMixedFullHistoryFamilyBits.creatingCommand P D key)

theorem leading_creating (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool)
    (c : Command (D.spatial (pairFst key)) (P.width (pairFst key)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D key = some c) :
    leading P D key = IntegralMixedFullHistoryScript.leading ((bank P D).state key) ((bank P D).birth_bound key) c := by
  unfold leading IntegralMixedFullHistoryFamilyBits.creatingCommand
  rw [hc]
  rfl

theorem integer_leading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (p : Polynomial ℤ) (hp : p ≠ 0) (hd : p.natDegree ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.integer p hp hd)) :
    IntegralMixedIntegerProducerBits.leadingValue P D q = residueBits (leading P D (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)) := by
  rw [leading_creating P D _ (.integer p hp hd) hc]
  unfold IntegralMixedIntegerProducerBits.leadingValue IntegralMixedIntegerProducerBits.leadingInteger
  rw [IntegralMixedIntegerProducerBits.polynomial_actual P D _ p hp hd hc]
  rfl

theorem physical_leading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : CriticalRule (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q))))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedPhysicalTaskBits.saved P q) = some (.critical r)) :
    IntegralMixedPhysicalProducerLeadingBits.value P (IntegralMixedPhysicalCompanionBits.fullFamily P D) q =
      residueBits (leading P D (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)) := by
  change IntegralMixedPhysicalProducerLeadingBits.value P (IntegralMixedPhysicalCompanionBits.fullFamily P D) q =
    residueBits (leading P D (IntegralMixedPhysicalTaskBits.saved P q) : ZMod (modulus P q))
  rw [IntegralMixedPhysicalProducerLeadingBits.value_actual,
    IntegralMixedPhysicalCompanionBits.rule_creating P D q r hc, leading_creating P D _ (.critical r) hc]
  rfl

theorem normalized_leading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))))
    (k : IntegralMixedRelativeCuts.Kind (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))) r) (d : ℕ)
    (ha : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)
      (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))).degree)
    (hd : d ≤ 2 ^ P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D (IntegralMixedVirtualTaskBits.saved P q) = some (.cut r k d ha hd)) :
    IntegralMixedNormalizationTopBits.leadingValue P (IntegralMixedNormalizedCompanionBits.fullFamily P D) q =
      residueBits (leading P D (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)) := by
  unfold IntegralMixedNormalizationTopBits.leadingValue
  rw [← IntegralMixedNormalizationTopBits.top_normalized_leading,
    leading_creating P D _ (.cut r k d ha hd) hc]
  change residueBits (normalizedScalarLeading ((bank P D).state (IntegralMixedVirtualTaskBits.saved P q))
    (IntegralMixedCutMatrix.raw ((bank P D).state (IntegralMixedVirtualTaskBits.saved P q))
      ((bank P D).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
      (IntegralMixedFullHistoryFamilyBits.selection P D (IntegralMixedVirtualTaskBits.saved P q)).rule
      (IntegralMixedFullHistoryFamilyBits.selection P D (IntegralMixedVirtualTaskBits.saved P q)).kind
      (IntegralMixedFullHistoryFamilyBits.selection P D (IntegralMixedVirtualTaskBits.saved P q)).degree)
    (IntegralMixedFullHistoryFamilyBits.selection P D (IntegralMixedVirtualTaskBits.saved P q)).degree : ZMod (modulus P q)) = _
  rw [IntegralMixedFullHistoryFamilyBits.selection_cut P D _ r k d ha hd hc]
  rfl

end LeanCanny.Algebra.IntegralMixedFullHistoryCompanionBits
