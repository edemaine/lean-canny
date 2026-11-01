/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalSnapshot
/-! # Actual physical original and gradient coefficients under spatial queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalSpatialBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalSnapshotBits
set_option backward.isDefEq.respectTransparency false

noncomputable def originalAt (F : Family) (key : List Bool) (e r t m : ℕ) (hm : m ≠ 0) :=
  (sourceAt F key 0 0 e r t m hm).toEuler.toGradient.toFrozen.toSource.value []

noncomputable def gradientAt (F : Family) (key : List Bool) (j e r t m : ℕ) (hm : m ≠ 0) : List Bool := by
  let S := (sourceAt F key 0 0 0 r t m hm).toEuler
  let := S.ring []
  exact residueBits ((Algebra.leftMulMatrix (S.basis [])
    ((IntegralCriticalGradientBits.polynomial S.toGradient []
      ⟨j % S.free [], Nat.mod_lt _ (S.free_pos [])⟩).coeff
        (RationalSubstitution.Indexed.exponentVector (S.free [])
          (FixedWidthPolynomial.entry (S.targetWidth []) e))) (S.row []) (S.col []) : ℤ) : ZMod m)

noncomputable def cleared (P : Parameters) (F : Family) (q : List Bool) :=
  (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedPhysicalTaskBits.arithmetic P F)).value q

theorem original_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (IntegralCriticalFlatGridSourceBits.original (IntegralMixedPhysicalTaskBits.arithmetic P F)).value q =
      originalAt F (IntegralMixedPhysicalTaskBits.saved P q) (get P .target q) (get P .row q) (get P .col q)
        (modulus P q) (modulus_ne_zero P q) := rfl

theorem derivative_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (IntegralCriticalFlatGridSourceBits.derivative P (IntegralMixedPhysicalTaskBits.arithmetic P F)).value q =
      gradientAt F (IntegralMixedPhysicalTaskBits.saved P q) (get P .derivative q) (get P .target q)
        (get P .row q) (get P .col q) (modulus P q) (modulus_ne_zero P q) := rfl

theorem gradient_snapshot (P : Parameters) (F : Family) (q : List Bool)
    (j : Fin ((IntegralMixedPhysicalTaskBits.arithmetic P F).free q)) (e : ℕ) :
    (IntegralCriticalGradientBits.family (IntegralMixedPhysicalTaskBits.arithmetic P F).toGradient).value
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) =
      gradientAt F (IntegralMixedPhysicalTaskBits.saved P q) j.val e (get P .row q) (get P .col q)
        (modulus P q) (modulus_ne_zero P q) := by
  rw [IntegralCriticalGradientBits.packet]
  unfold gradientAt
  let S := IntegralMixedPhysicalTaskBits.arithmetic P F
  let := S.ring q
  have H : j.val % S.free q = j.val := Nat.mod_eq_of_lt j.isLt
  change _ = residueBits ((Algebra.leftMulMatrix (S.basis q)
    ((IntegralCriticalGradientBits.polynomial S.toGradient q ⟨j.val % S.free q, _⟩).coeff
      (RationalSubstitution.Indexed.exponentVector (S.free q)
        (FixedWidthPolynomial.entry (S.targetWidth q) e))) (S.row q) (S.col q) : ℤ) : ZMod (S.modulus q))
  simp only [H]
  rfl

theorem cleared_original (P : Parameters) (F : Family) (q : List Bool) (hx : get P .expression q ≠ 1) :
    cleared P F q = originalAt F (IntegralMixedPhysicalTaskBits.saved P q) (get P .target q)
      (get P .row q) (get P .col q) (modulus P q) (modulus_ne_zero P q) := by
  unfold cleared IntegralCriticalFlatGenericGridBits.source
  rw [IntegralCriticalFlatGridSourceBits.value]
  change (if get P .expression q = 1 then _ else _) = _
  rw [ite_eq_right hx, original_snapshot]

theorem cleared_derivative (P : Parameters) (F : Family) (q : List Bool) (hx : get P .expression q = 1) :
    cleared P F q = gradientAt F (IntegralMixedPhysicalTaskBits.saved P q) (get P .derivative q) (get P .target q)
      (get P .row q) (get P .col q) (modulus P q) (modulus_ne_zero P q) := by
  unfold cleared IntegralCriticalFlatGenericGridBits.source
  rw [IntegralCriticalFlatGridSourceBits.value]
  change (if get P .expression q = 1 then _ else _) = _
  rw [ite_eq_left hx, derivative_snapshot]

theorem original_congr (F : Family) (key key' : List Bool) (e r t m e' r' t' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (he : e = e') (hr : r = r') (ht : t = t') (hmod : m = m') :
    originalAt F key e r t m hm = originalAt F key' e' r' t' m' hm' := by
  subst key'; subst e'; subst r'; subst t'; subst m'
  rfl

theorem gradient_congr (F : Family) (key key' : List Bool) (j e r t m j' e' r' t' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hj : j = j') (he : e = e') (hr : r = r') (ht : t = t') (hmod : m = m') :
    gradientAt F key j e r t m hm = gradientAt F key' j' e' r' t' m' hm' := by
  subst key'; subst j'; subst e'; subst r'; subst t'; subst m'
  rfl

theorem spatial_saved (P : Parameters) (p : Phase) (x : ℕ) (z : List Bool) :
    IntegralMixedPhysicalTaskBits.saved P (IntegralCriticalFlatEulerRowsBits.spatial P p x z) =
      IntegralMixedPhysicalTaskBits.saved P (pairFst z) := by
  apply IntegralMixedPhysicalTaskBits.saved_invariance
  · exact IntegralCriticalFlatEulerRowsBits.spatial_root P p x z
  · exact IntegralCriticalFlatEulerRowsBits.spatial_birth P p x z
  · exact IntegralCriticalFlatEulerRowsBits.spatial_other P p x z .slot15 (by decide) (by decide) (by decide)

theorem spatial_derivative_child (P : Parameters) (F : Family) (p : Phase) (q : List Bool)
    (j : Fin ((IntegralMixedPhysicalTaskBits.arithmetic P F).free q)) (e : ℕ)
    (hj : j.val ≤ numericCap P (RankedHistoryTask.root q)) (he : e ≤ numericCap P (RankedHistoryTask.root q)) :
    cleared P F (IntegralCriticalFlatEulerRowsBits.spatial P p 1
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)))) =
    (IntegralCriticalGradientBits.family (IntegralMixedPhysicalTaskBits.arithmetic P F).toGradient).value
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) := by
  let child := IntegralCriticalFlatEulerRowsBits.spatial P p 1 (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)))
  have HF := IntegralCriticalFlatEulerRowsBits.spatial_fields P p 1 q j.val e hj he (numericCap_pos P _)
  change cleared P F child = _
  rw [cleared_derivative P F child HF.2.2, gradient_snapshot P F q j e]
  apply gradient_congr
  · exact (spatial_saved P p 1 _).trans (congrArg (IntegralMixedPhysicalTaskBits.saved P) (pairFst_pair _ _))
  · exact HF.1
  · exact HF.2.1
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other P p 1
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) .row (by decide) (by decide) (by decide)
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other P p 1
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) .col (by decide) (by decide) (by decide)
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_modulus P p 1
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)))

theorem spatial_original_child (P : Parameters) (F : Family) (p : Phase) (q : List Bool) (j e : ℕ)
    (hj : j ≤ numericCap P (RankedHistoryTask.root q)) (he : e ≤ numericCap P (RankedHistoryTask.root q)) :
    cleared P F (IntegralCriticalFlatEulerRowsBits.spatial P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))) =
    originalAt F (IntegralMixedPhysicalTaskBits.saved P q) e (get P .row q) (get P .col q)
      (modulus P q) (modulus_ne_zero P q) := by
  let child := IntegralCriticalFlatEulerRowsBits.spatial P p 0 (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))
  have HF := IntegralCriticalFlatEulerRowsBits.spatial_fields P p 0 q j e hj he (Nat.zero_le _)
  change cleared P F child = _
  rw [cleared_original P F child (by rw [HF.2.2]; decide)]
  apply original_congr
  · exact (spatial_saved P p 0 _).trans (congrArg (IntegralMixedPhysicalTaskBits.saved P) (pairFst_pair _ _))
  · exact HF.2.1
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e))) .row (by decide) (by decide) (by decide)
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e))) .col (by decide) (by decide) (by decide)
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_modulus P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))

noncomputable def lowerEntryAt (F : Family) (key : List Bool) (j e r t m : ℕ) (hm : m ≠ 0) : List Bool :=
  let S := (sourceAt F key 0 0 e r t m hm).toEuler
  S.lowerValue (fun _ => ⟨j % S.free [], Nat.mod_lt _ (S.free_pos [])⟩) []

theorem lower_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedPhysicalSnapshotBits.lower P F q =
      lowerEntryAt F (IntegralMixedPhysicalTaskBits.saved P q) (get P .derivative q) (get P .target q)
        (get P .row q) (get P .col q) (modulus P q) (modulus_ne_zero P q) := rfl

theorem lowerEntryAt_congr (F : Family) (key key' : List Bool) (j e r t m j' e' r' t' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hj : j = j') (he : e = e') (hr : r = r') (ht : t = t') (hmod : m = m') :
    lowerEntryAt F key j e r t m hm = lowerEntryAt F key' j' e' r' t' m' hm' := by
  subst key'; subst j'; subst e'; subst r'; subst t'; subst m'
  rfl

theorem lower_transport (P : Parameters) (F : Family) (q c : List Bool) (j e r t : ℕ)
    (hr0 : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q) (hm : modulus P c = modulus P q)
    (hj : get P .derivative c = j) (he : get P .target c = e) (hr : get P .row c = r) (ht : get P .col c = t) :
    IntegralMixedPhysicalSnapshotBits.lower P F c =
      lowerEntryAt F (IntegralMixedPhysicalTaskBits.saved P q) j e r t (modulus P q) (modulus_ne_zero P q) := by
  rw [lower_snapshot]
  apply lowerEntryAt_congr
  · exact IntegralMixedPhysicalTaskBits.saved_invariance P q c hr0 hb hx
  · exact hj
  · exact he
  · exact hr
  · exact ht
  · exact hm

theorem lowerEntry_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedPhysicalSnapshotBits.lower P F q =
      ((sourceAt F (IntegralMixedPhysicalTaskBits.saved P q) 0 0 (get P .target q) (get P .row q) (get P .col q)
        (modulus P q) (modulus_ne_zero P q)).toEuler).lowerValue
        (fun _ => ⟨get P .derivative q % (F.ambient (IntegralMixedPhysicalTaskBits.saved P q) -
          (F.rule (IntegralMixedPhysicalTaskBits.saved P q)).offset.val + 1), Nat.mod_lt _ (by omega)⟩) [] := rfl
end LeanCanny.Algebra.IntegralMixedPhysicalSpatialBits
