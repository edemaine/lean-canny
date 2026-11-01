/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldHeightSnapshot
/-! # Literal retained-bank entries depend only on ROOT and scalar birth -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOldHeightBankBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullHistoryScript IntegralMixedHistory
open IntegralMixedOldHeightBits (bankFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def commandEntry {n S B : ℕ} {F : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State F S B 0 ι) (cs : List (Command F B)) (h : cs.length ≤ S + 1) (i r t : ℕ) : ℤ :=
  let x := run initial cs h
  if hv : i < cs.length ∧ r < FixedWidthPolynomial.count cs.length B ∧ t < FixedWidthPolynomial.count cs.length B then
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (cleared x ⟨i, hv.1⟩) ⟨r, hv.2.1⟩ ⟨t, hv.2.2⟩ else 0

theorem commandEntry_congr {n S B : ℕ} {F : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State F S B 0 ι) (cs ds : List (Command F B)) (h : cs.length ≤ S + 1) (hd : ds.length ≤ S + 1)
    (i r t : ℕ) (he : cs = ds) : commandEntry initial cs h i r t = commandEntry initial ds hd i r t := by
  cases he
  rfl

noncomputable def sourceEntry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) (i r t : ℕ) : ℤ :=
  if hv : i < (bankFamily P D).birth key ∧ r < FixedWidthPolynomial.count ((bankFamily P D).birth key) ((bankFamily P D).width key) ∧
      t < FixedWidthPolynomial.count ((bankFamily P D).birth key) ((bankFamily P D).width key) then
    Algebra.leftMulMatrix ((bankFamily P D).state key).sampler.scalarPrefix.basis.finBasis
      (cleared ((bankFamily P D).state key) ⟨i, hv.1⟩) ⟨r, hv.2.1⟩ ⟨t, hv.2.2⟩ else 0

noncomputable def rootEntry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (root : List Bool) (b i r t : ℕ) :=
  commandEntry (IntegralMixedFullHistoryFamilyBits.initial P D root) (paddedPast (D.rules root) (min b (P.cap root + 1)))
    (by rw [paddedPast_length]; exact (min_le_right _ _).trans (Nat.le_succ _)) i r t

theorem sourceEntry_root (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) (i r t : ℕ) :
    sourceEntry P D key i r t = rootEntry P D (pairFst key) (IntegralMixedFullHistoryFamilyBits.prefixLength P key) i r t := by
  change commandEntry (IntegralMixedFullHistoryFamilyBits.initial P D (pairFst key))
    (IntegralMixedFullHistoryFamilyBits.commands P D key) (((bankFamily P D).birth_bound key).trans (Nat.le_succ _)) i r t = _
  unfold rootEntry
  apply commandEntry_congr
  exact congrArg (paddedPast (D.rules (pairFst key)))
    (min_eq_left (min_le_right _ _ : IntegralMixedFullHistoryFamilyBits.prefixLength P key ≤ P.cap (pairFst key) + 1)).symm

theorem sourceEntry_invariance (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q) (i r t : ℕ) :
    sourceEntry P D (IntegralMixedVirtualTaskBits.saved P c) i r t = sourceEntry P D (IntegralMixedVirtualTaskBits.saved P q) i r t := by
  rw [sourceEntry_root, sourceEntry_root, IntegralMixedFullHistoryFamilyBits.saved_root, IntegralMixedFullHistoryFamilyBits.saved_root,
    IntegralMixedFullHistoryFamilyBits.saved_prefix, IntegralMixedFullHistoryFamilyBits.saved_prefix, hr, hb]

theorem value_source (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedOldHeightBits.value P D q = residueBits
      (sourceEntry P D (IntegralMixedVirtualTaskBits.saved P q) (get P .sourceIndex q) (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  have HE : (get P .sourceIndex q < (bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q) ∧
      get P .row q < FixedWidthPolynomial.count ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q))
        ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q)) ∧
      get P .col q < FixedWidthPolynomial.count ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q))
        ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q))) ↔ IntegralMixedOldHeightBits.valid P q := by
    rw [IntegralMixedOldHeightBits.bank_birth, (IntegralMixedFullHistoryFamilyBits.geometry P D).width q]
    rfl
  by_cases HV : IntegralMixedOldHeightBits.valid P q
  · rw [IntegralMixedOldHeightBits.value, dite_eq_left HV, sourceEntry, dite_eq_left (HE.mpr HV)]
    rfl
  · rw [IntegralMixedOldHeightBits.value, dite_eq_right HV, sourceEntry, dite_eq_right (fun H => HV (HE.mp H)), Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _

end LeanCanny.Algebra.IntegralMixedOldHeightBankBits
