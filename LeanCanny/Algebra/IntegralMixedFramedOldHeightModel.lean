/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightOrigin
public import LeanCanny.Algebra.IntegralMixedOldHeightQuery
public import LeanCanny.Algebra.IntegralMixedFramedCompanionSource
/-! # Total literal old-height entries of the full mixed retained bank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedOldHeightBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev bankFamily (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedHistoryFamilyBits.family P D H
noncomputable abbrev state (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  (bankFamily P D H).state (IntegralMixedVirtualTaskBits.saved P q)
noncomputable def oldRank (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  FixedWidthPolynomial.count ((bankFamily P D H).birth (IntegralMixedVirtualTaskBits.saved P q))
    ((bankFamily P D H).width (IntegralMixedVirtualTaskBits.saved P q))

theorem bank_birth (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    (bankFamily P D H).birth (IntegralMixedVirtualTaskBits.saved P q) = birth P q :=
  (IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth q

theorem oldRank_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    oldRank P D H q = dimension P q := by
  unfold oldRank dimension
  rw [bank_birth, (IntegralMixedFramedHistoryFamilyBits.geometry P D H).width q]

noncomputable def bankIndex (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (h : get P .sourceIndex q < birth P q) : Fin ((bankFamily P D H).birth (IntegralMixedVirtualTaskBits.saved P q)) :=
  ⟨get P .sourceIndex q, h.trans_eq (bank_birth P D H q).symm⟩
noncomputable def rowIndex (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (h : get P .row q < dimension P q) : Fin (oldRank P D H q) :=
  ⟨get P .row q, h.trans_eq (oldRank_eq P D H q).symm⟩
noncomputable def colIndex (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (h : get P .col q < dimension P q) : Fin (oldRank P D H q) :=
  ⟨get P .col q, h.trans_eq (oldRank_eq P D H q).symm⟩

noncomputable def value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : List Bool :=
  if h : valid P q then
    residueBits ((Algebra.leftMulMatrix (state P D H q).sampler.scalarPrefix.basis.finBasis
      (cleared (state P D H q) (bankIndex P D H q h.1)) (rowIndex P D H q h.2.1) (colIndex P D H q h.2.2) : ℤ) : ZMod (modulus P q))
  else []

theorem value_canonical (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P D H q := by
  unfold value
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

theorem value_invalid (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (h : ¬ valid P q) : value P D H q = [] := dite_eq_right h

noncomputable def cofactor (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : ℤ :=
  (IntegralMixedOldBankCofactorBits.scalars P (bankFamily P D H) (index P)).cofactor q

theorem cofactor_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (h : get P .sourceIndex q < birth P q) : cofactor P D H q =
      CommonIntegerDenominator.denominator (Finset.univ.erase (bankIndex P D H q h)) (state P D H q).bank.denominator := by
  apply IntegralMixedBankCofactor.cofactor_eq (IntegralMixedVirtualTaskBits.family P (bankFamily P D H))
    (modulus P) (modulus_ne_zero P) (index P) q (bankIndex P D H q h)
  exact min_eq_left h.le

end LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
