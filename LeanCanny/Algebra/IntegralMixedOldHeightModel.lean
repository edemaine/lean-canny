/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldHeightOrigin
public import LeanCanny.Algebra.IntegralMixedOldHeightQuery
public import LeanCanny.Algebra.IntegralMixedFullHistoryCompanion
/-! # Total literal old-height entries of the full mixed retained bank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev bankFamily (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) :=
  IntegralMixedFullHistoryFamilyBits.family P D
noncomputable abbrev state (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :=
  (bankFamily P D).state (IntegralMixedVirtualTaskBits.saved P q)
noncomputable def oldRank (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :=
  FixedWidthPolynomial.count ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q))
    ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q))

theorem bank_birth (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    (bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q) = birth P q :=
  (IntegralMixedFullHistoryFamilyBits.geometry P D).birth q

theorem oldRank_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    oldRank P D q = dimension P q := by
  unfold oldRank dimension
  rw [bank_birth, (IntegralMixedFullHistoryFamilyBits.geometry P D).width q]

noncomputable def bankIndex (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (h : get P .sourceIndex q < birth P q) : Fin ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q)) :=
  ⟨get P .sourceIndex q, h.trans_eq (bank_birth P D q).symm⟩
noncomputable def rowIndex (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (h : get P .row q < dimension P q) : Fin (oldRank P D q) :=
  ⟨get P .row q, h.trans_eq (oldRank_eq P D q).symm⟩
noncomputable def colIndex (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (h : get P .col q < dimension P q) : Fin (oldRank P D q) :=
  ⟨get P .col q, h.trans_eq (oldRank_eq P D q).symm⟩

noncomputable def value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : List Bool :=
  if h : valid P q then
    residueBits ((Algebra.leftMulMatrix (state P D q).sampler.scalarPrefix.basis.finBasis
      (cleared (state P D q) (bankIndex P D q h.1)) (rowIndex P D q h.2.1) (colIndex P D q h.2.2) : ℤ) : ZMod (modulus P q))
  else []

theorem value_canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P D q := by
  unfold value
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

theorem value_invalid (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (h : ¬ valid P q) : value P D q = [] := dite_eq_right h

noncomputable def cofactor (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℤ :=
  (IntegralMixedOldBankCofactorBits.scalars P (bankFamily P D) (index P)).cofactor q

theorem cofactor_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (h : get P .sourceIndex q < birth P q) : cofactor P D q =
      CommonIntegerDenominator.denominator (Finset.univ.erase (bankIndex P D q h)) (state P D q).bank.denominator := by
  apply IntegralMixedBankCofactor.cofactor_eq (IntegralMixedVirtualTaskBits.family P (bankFamily P D))
    (modulus P) (modulus_ne_zero P) (index P) q (bankIndex P D q h)
  exact min_eq_left h.le

end LeanCanny.Algebra.IntegralMixedOldHeightBits
