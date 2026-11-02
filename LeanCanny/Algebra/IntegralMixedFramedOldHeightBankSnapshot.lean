/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightRootSnapshot
/-! # Literal retained-bank entries depend only on ROOT and scalar birth -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBankBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryScript IntegralMixedHistory
open IntegralMixedFramedOldHeightBits (bankFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def commandEntry {n S B : ℕ} {F : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State F S B 0 ι) (cs : List (Instruction n B)) (h : cs.length ≤ S + 1) (i r t : ℕ) : ℤ :=
  let x := run initial cs h
  if hv : i < cs.length ∧ r < FixedWidthPolynomial.count cs.length B ∧ t < FixedWidthPolynomial.count cs.length B then
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (cleared x ⟨i, hv.1⟩) ⟨r, hv.2.1⟩ ⟨t, hv.2.2⟩ else 0

theorem commandEntry_congr {n S B : ℕ} {F : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State F S B 0 ι) (cs ds : List (Instruction n B)) (h : cs.length ≤ S + 1) (hd : ds.length ≤ S + 1)
    (i r t : ℕ) (he : cs = ds) : commandEntry initial cs h i r t = commandEntry initial ds hd i r t := by
  cases he
  rfl

noncomputable def sourceEntry (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (i r t : ℕ) : ℤ :=
  if hv : i < (bankFamily P D J).birth key ∧ r < FixedWidthPolynomial.count ((bankFamily P D J).birth key) ((bankFamily P D J).width key) ∧
      t < FixedWidthPolynomial.count ((bankFamily P D J).birth key) ((bankFamily P D J).width key) then
    Algebra.leftMulMatrix ((bankFamily P D J).state key).sampler.scalarPrefix.basis.finBasis
      (cleared ((bankFamily P D J).state key) ⟨i, hv.1⟩) ⟨r, hv.2.1⟩ ⟨t, hv.2.2⟩ else 0

noncomputable def rootEntry (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (_J : IntegralMixedFramedHistoryFamilyBits.Data P D) (root : List Bool) (b i r t : ℕ) :=
  commandEntry (IntegralMixedFramedHistoryFamilyBits.initial P D root) (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) (min b (P.cap root + 1)))
    (by rw [paddedPast_length]; exact (min_le_right _ _).trans (Nat.le_succ _)) i r t

theorem sourceEntry_root (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (i r t : ℕ) :
    sourceEntry P D J key i r t = rootEntry P D J (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) i r t := by
  unfold sourceEntry
  change commandEntry (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.commands P D key) (((bankFamily P D J).birth_bound key).trans (Nat.le_succ _)) i r t = _
  unfold rootEntry
  apply commandEntry_congr
  exact congrArg (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (D.rules (pairFst key)))
    (min_eq_left (min_le_right _ _ : IntegralMixedFramedHistoryFamilyBits.prefixLength P key ≤ P.cap (pairFst key) + 1)).symm

theorem sourceEntry_invariance (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q) (i r t : ℕ) :
    sourceEntry P D J (IntegralMixedVirtualTaskBits.saved P c) i r t = sourceEntry P D J (IntegralMixedVirtualTaskBits.saved P q) i r t := by
  rw [sourceEntry_root, sourceEntry_root]
  simp only [IntegralMixedFramedHistoryFamilyBits.prefixLength]
  rw [IntegralMixedFullHistoryFamilyBits.saved_root, IntegralMixedFullHistoryFamilyBits.saved_root,
    IntegralMixedFullHistoryFamilyBits.saved_prefix, IntegralMixedFullHistoryFamilyBits.saved_prefix, hr, hb]

theorem value_source (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedOldHeightBits.value P D J q = residueBits
      (sourceEntry P D J (IntegralMixedVirtualTaskBits.saved P q) (get P .sourceIndex q) (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  have HE : (get P .sourceIndex q < (bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q) ∧
      get P .row q < FixedWidthPolynomial.count ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))
        ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) ∧
      get P .col q < FixedWidthPolynomial.count ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))
        ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q))) ↔ IntegralMixedOldHeightBits.valid P q := by
    rw [IntegralMixedFramedOldHeightBits.bank_birth, (IntegralMixedFramedHistoryFamilyBits.geometry P D J).width q]
    rfl
  by_cases HV : IntegralMixedOldHeightBits.valid P q
  · rw [IntegralMixedFramedOldHeightBits.value, dite_eq_left HV, sourceEntry, dite_eq_left (HE.mpr HV)]
    rfl
  · rw [IntegralMixedFramedOldHeightBits.value, dite_eq_right HV, sourceEntry, dite_eq_right (fun H => HV (HE.mp H)), Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _

end LeanCanny.Algebra.IntegralMixedFramedOldHeightBankBits
