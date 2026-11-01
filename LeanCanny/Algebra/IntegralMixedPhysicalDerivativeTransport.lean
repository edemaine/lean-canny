/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalCoefficientModel
public import LeanCanny.Algebra.IntegralMixedPhysicalCaps
/-! # Actual bumped derivative children in the physical source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits
set_option backward.isDefEq.respectTransparency false

theorem original_transport (P : Parameters) (F : Family) (q c : List Bool) (k r t : ℕ)
    (hr0 : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q) (hm : modulus P c = modulus P q)
    (hk : get P .sourceIndex c = k) (hr : get P .row c = r) (ht : get P .col c = t) :
    IntegralMixedPhysicalNativeLowerBits.original P F c =
      originalAt F (IntegralMixedPhysicalTaskBits.saved P q) k r t (modulus P q) (modulus_ne_zero P q) := by
  rw [original_snapshot]
  apply originalAt_congr
  · exact IntegralMixedPhysicalTaskBits.saved_invariance P q c hr0 hb hx
  · exact hk
  · exact hr
  · exact ht
  · exact hm

theorem originalAt_packet (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (q : List Bool) (k : ℕ) (r t : Fin ((source P F).rank q)) :
    (access P a F h).coefficient (pair (IntegralClearedCoefficientBits.context q r.val t.val) (BinaryNatCode.encode k)) =
      originalAt F (IntegralMixedPhysicalTaskBits.saved P q) k r.val t.val (modulus P q) (modulus_ne_zero P q) := by
  rw [(access P a F h).coefficient_eq]
  unfold originalAt
  let S := source P F
  let := S.ring q
  change residueBits ((Algebra.leftMulMatrix (S.basis q)
    ((S.polynomial q).coeff (RationalSubstitution.Indexed.exponentVector (S.arity q)
      (FixedWidthPolynomial.entry (S.sourceWidth q) k))) r t : ℤ) : ZMod (S.modulus q)) =
    residueBits ((Algebra.leftMulMatrix (S.basis q)
      ((S.polynomial q).coeff (RationalSubstitution.Indexed.exponentVector (S.arity q)
        (FixedWidthPolynomial.entry (S.sourceWidth q) k)))
      ⟨r.val % S.rank q, Nat.mod_lt _ (Nat.zero_le _ |>.trans_lt (S.row q).isLt)⟩
      ⟨t.val % S.rank q, Nat.mod_lt _ (Nat.zero_le _ |>.trans_lt (S.row q).isLt)⟩ : ℤ) : ZMod (S.modulus q))
  have HR : (⟨r.val % S.rank q, Nat.mod_lt _ (Nat.zero_le _ |>.trans_lt (S.row q).isLt)⟩ : Fin (S.rank q)) = r :=
    Fin.ext (Nat.mod_eq_of_lt r.isLt)
  have HT : (⟨t.val % S.rank q, Nat.mod_lt _ (Nat.zero_le _ |>.trans_lt (S.row q).isLt)⟩ : Fin (S.rank q)) = t :=
    Fin.ext (Nat.mod_eq_of_lt t.isLt)
  rw [HR, HT]

-- The fixed-width bumped index and the finite matrix selectors fit the original
-- root cap. No arbitrary out-of-domain coefficient reply is demanded.
theorem bumped_child (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) :
    IntegralMixedPhysicalNativeLowerBits.original P F
      (IntegralCriticalFlatDerivativeQuery.writer P (IntegralDerivativeBits.flatQuery (source P F)
        (IntegralCriticalFlatDerivativeBits.input P (source P F) q))) =
      (access P a F h).coefficient (IntegralDerivativeBits.flatQuery (source P F)
        (IntegralCriticalFlatDerivativeBits.input P (source P F) q)) := by
  let p := IntegralDerivativeBits.flatQuery (source P F) (IntegralCriticalFlatDerivativeBits.input P (source P F) q)
  let child := IntegralCriticalFlatDerivativeQuery.writer P p
  have HO : IntegralDerivativeBits.original p = q :=
    (IntegralDerivativeBits.flatQuery_original (source P F) _).trans (IntegralCriticalFlatDerivativeBits.input_original P (source P F) q)
  have HR : RankedHistoryTask.root child = RankedHistoryTask.root q := by
    simpa only [child, HO] using IntegralCriticalFlatDerivativeQuery.writer_root P p
  have HB : birth P child = birth P q := by simpa only [child, HO] using IntegralCriticalFlatDerivativeQuery.writer_birth P p
  have HM : modulus P child = modulus P q := by simpa only [child, HO] using IntegralCriticalFlatDerivativeQuery.writer_modulus P p
  have HX : get P .slot15 child = get P .slot15 q := by
    simpa only [child, HO] using IntegralCriticalFlatDerivativeQuery.writer_other P p .slot15 (by decide) (by decide) (by decide)
  have HC := IntegralCriticalFlatDerivativeBits.child_fields P (source P F) q
    (IntegralMixedPhysicalCaps.source_grid_cap P F g q) (IntegralMixedPhysicalCaps.rank_cap P F g q)
  let r := IntegralCriticalFlatOriginalCoefficientBits.index P (source P F).toSource .row q
  let t := IntegralCriticalFlatOriginalCoefficientBits.index P (source P F).toSource .col q
  change IntegralMixedPhysicalNativeLowerBits.original P F child = _
  rw [original_transport P F q child _ r.val t.val HR HB HX HM HC.1 HC.2.1 HC.2.2]
  rw [IntegralCriticalFlatDerivativeBits.query_packet]
  exact (originalAt_packet P a F h q (IntegralCriticalFlatDerivativeBits.bumpedIndex P (source P F) q) r t).symm
end LeanCanny.Algebra.IntegralMixedPhysicalCoefficientBits
