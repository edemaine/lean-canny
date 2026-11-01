/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldHeightModel
public import LeanCanny.Algebra.IntegralMixedOldHeightQueryFields
public import LeanCanny.Algebra.IntegralMixedFullHistoryCompanionMatrix
/-! # Integer snapshots of actual creating companions, independent of saved selectors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullHistoryScript IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def commandEntry {n S B : ℕ} {F : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State F S B 0 ι) (cs : List (Command F B)) (h : cs.length ≤ S)
    (c : Command F B) (r t : ℕ) : ℤ :=
  let x := run initial cs (h.trans (Nat.le_succ _))
  let p := polynomial x h c
  let d := degree x h c
  Algebra.leftMulMatrix (PaddedIntegralParameterExtension.coordinateBasis x.sampler.scalarPrefix.basis p d).finBasis
    (AdjoinRoot.root _) ⟨r % FixedWidthPolynomial.count (cs.length + 1) B, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % FixedWidthPolynomial.count (cs.length + 1) B, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

theorem commandEntry_congr {n S B : ℕ} {F : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State F S B 0 ι) (cs ds : List (Command F B)) (h : cs.length ≤ S) (hd : ds.length ≤ S)
    (c e : Command F B) (r t : ℕ) (hcs : cs = ds) (hc : c = e) :
    commandEntry initial cs h c r t = commandEntry initial ds hd e r t := by
  cases hcs
  cases hc
  rfl

noncomputable def sourceEntry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (key : List Bool) (r t : ℕ) : ℤ :=
  (IntegralMixedFullHistoryCompanionBits.source P D).matrix key
    ⟨r % FixedWidthPolynomial.count ((bankFamily P D).birth key + 1) ((bankFamily P D).width key),
      Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % FixedWidthPolynomial.count ((bankFamily P D).birth key + 1) ((bankFamily P D).width key),
      Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

theorem sourceEntry_command (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (key : List Bool) (r t : ℕ) :
    sourceEntry P D key r t = commandEntry (IntegralMixedFullHistoryFamilyBits.initial P D (pairFst key))
      (IntegralMixedFullHistoryFamilyBits.commands P D key) ((bankFamily P D).birth_bound key)
      (IntegralMixedFullHistoryFamilyBits.creatingCommand P D key) r t := rfl

noncomputable def rootEntry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (root : List Bool) (b r t : ℕ) : ℤ :=
  commandEntry (IntegralMixedFullHistoryFamilyBits.initial P D root)
    (paddedPast (D.rules root) (min b (P.cap root + 1)))
    (by rw [paddedPast_length]; exact min_le_right _ _)
    ((chronological (D.rules root) (min b (P.cap root + 1))).getD defaultCommand) r t

theorem sourceEntry_root (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (key : List Bool) (r t : ℕ) : sourceEntry P D key r t =
      rootEntry P D (pairFst key) (IntegralMixedFullHistoryFamilyBits.prefixLength P key) r t := by
  rw [sourceEntry_command]
  unfold rootEntry
  apply commandEntry_congr
  · exact congrArg (paddedPast (D.rules (pairFst key)))
      (min_eq_left (min_le_right _ _ : IntegralMixedFullHistoryFamilyBits.prefixLength P key ≤ P.cap (pairFst key) + 1)).symm
  · exact congrArg (fun b => (chronological (D.rules (pairFst key)) b).getD defaultCommand)
      (min_eq_left (min_le_right _ _ : IntegralMixedFullHistoryFamilyBits.prefixLength P key ≤ P.cap (pairFst key) + 1)).symm

theorem sourceEntry_invariance (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (q c : List Bool) (hr : RankedHistoryTask.root c = RankedHistoryTask.root q)
    (hb : birth P c = birth P q) (r t : ℕ) :
    sourceEntry P D (IntegralMixedVirtualTaskBits.saved P c) r t =
      sourceEntry P D (IntegralMixedVirtualTaskBits.saved P q) r t := by
  rw [sourceEntry_root, sourceEntry_root, IntegralMixedFullHistoryFamilyBits.saved_root,
    IntegralMixedFullHistoryFamilyBits.saved_root, IntegralMixedFullHistoryFamilyBits.saved_prefix,
    IntegralMixedFullHistoryFamilyBits.saved_prefix, hr, hb]

theorem sourceEntry_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    IntegralMixedFullHistoryCompanionBits.value P D q =
      residueBits (sourceEntry P D (IntegralMixedVirtualTaskBits.saved P q) (get P .row q) (get P .col q) : ZMod (modulus P q)) := rfl

end LeanCanny.Algebra.IntegralMixedOldHeightBits
