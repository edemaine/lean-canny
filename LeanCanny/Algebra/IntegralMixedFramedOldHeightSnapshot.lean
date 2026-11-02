/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightModel
/-! # Actual creating companion blocks in a source-framed retained height -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryScript IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def commandEntry (P : Parameters) (D : Plan P) (root : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root))) (h : cs.length ≤ P.cap root + 1)
    (c : Instruction (P.ambient root) (P.width root)) (r t : ℕ) : ℤ :=
  let x := IntegralMixedFramedHistoryFamilyBits.creatorState P D root cs c (h.trans (Nat.le_succ (P.cap root + 1)))
  let p := IntegralMixedFullHistoryScript.polynomial x h c.command
  let d := IntegralMixedFullHistoryScript.degree x h c.command
  Algebra.leftMulMatrix (PaddedIntegralParameterExtension.coordinateBasis x.sampler.scalarPrefix.basis p d).finBasis
    (AdjoinRoot.root _) ⟨r % FixedWidthPolynomial.count (cs.length + 1) (P.width root), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % FixedWidthPolynomial.count (cs.length + 1) (P.width root), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

theorem commandEntry_congr (P : Parameters) (D : Plan P) (root root' : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root))) (cs' : List (Instruction (P.ambient root') (P.width root')))
    (h : cs.length ≤ P.cap root + 1) (h' : cs'.length ≤ P.cap root' + 1)
    (c : Instruction (P.ambient root) (P.width root)) (c' : Instruction (P.ambient root') (P.width root'))
    (r t : ℕ) (hr : root = root') (hs : HEq cs cs') (hc : HEq c c') :
    commandEntry P D root cs h c r t = commandEntry P D root' cs' h' c' r t := by
  cases hr
  cases hs
  cases hc
  rfl

noncomputable def sourceEntry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r t : ℕ) : ℤ :=
  (IntegralMixedFramedCompanionBits.source P D H).matrix key
    ⟨r % FixedWidthPolynomial.count ((bankFamily P D H).birth key + 1) ((bankFamily P D H).width key), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % FixedWidthPolynomial.count ((bankFamily P D H).birth key + 1) ((bankFamily P D H).width key), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

attribute [local irreducible] PaddedIntegralGeneratorSource.Source.matrix

theorem sourceEntry_command (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r t : ℕ) : sourceEntry P D H key r t =
    commandEntry P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.commands P D key)
      ((bankFamily P D H).birth_bound key) (IntegralMixedFramedHistoryFamilyBits.instruction P D key) r t := by
  unfold sourceEntry
  rw [IntegralMixedFramedCompanionBits.source_matrix]
  rfl

theorem commandEntry_of_fin (P : Parameters) (D : Plan P) (root : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root))) (h : cs.length ≤ P.cap root + 1)
    (c : Instruction (P.ambient root) (P.width root))
    (r t : Fin (FixedWidthPolynomial.count (cs.length + 1) (P.width root))) :
    commandEntry P D root cs h c r.val t.val =
      Algebra.leftMulMatrix (UniformIntegralPrefix.step
        (IntegralMixedFramedHistoryFamilyBits.creatorState P D root cs c (h.trans (Nat.le_succ (P.cap root + 1)))).sampler.scalarPrefix
        h (Nat.two_pow_pos (P.width root))
        (IntegralMixedFullHistoryScript.polynomial (IntegralMixedFramedHistoryFamilyBits.creatorState P D root cs c (h.trans (Nat.le_succ (P.cap root + 1)))) h c.command)
        (IntegralMixedFullHistoryScript.degree (IntegralMixedFramedHistoryFamilyBits.creatorState P D root cs c (h.trans (Nat.le_succ (P.cap root + 1)))) h c.command)).basis.finBasis
        (AdjoinRoot.root _) r t := by
  simp only [commandEntry, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]
  rfl

theorem origin_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : Fin ((bankFamily P D H).birth key))
    (r t : Fin (FixedWidthPolynomial.count ((bankFamily P D H).birth key) ((bankFamily P D H).width key)))
    (context : List Bool) :
    let o := IntegralMixedFramedHistoryFamilyBits.origin P D H key i
    Algebra.leftMulMatrix
      (birthPrefix (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key))
        (IntegralMixedFramedHistoryFamilyBits.commands P D key) (((bankFamily P D H).birth_bound key).trans (Nat.le_succ (P.cap (pairFst key) + 1))) i).basis.finBasis
      (AdjoinRoot.root _) (o.chain.oldIndex r) (o.chain.oldIndex t) =
    sourceEntry P D H (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key)
      (IntegralMixedFramedHistoryFamilyBits.prefixLength P key - 1 - i.val) context)
      (r.val / FixedWidthPolynomial.count i.val (P.width (pairFst key)))
      (t.val / FixedWidthPolynomial.count i.val (P.width (pairFst key))) := by
  let o := IntegralMixedFramedHistoryFamilyBits.origin P D H key i
  calc
    _ = commandEntry P D (pairFst key) (older (IntegralMixedFramedHistoryFamilyBits.commands P D key) i)
        (older_bound _ (((bankFamily P D H).birth_bound key).trans (Nat.le_succ (P.cap (pairFst key) + 1))) i)
        (chosen (IntegralMixedFramedHistoryFamilyBits.commands P D key) i)
        (o.chain.oldIndex r).val (o.chain.oldIndex t).val :=
      (commandEntry_of_fin P D _ _ _ _ (o.chain.oldIndex r) (o.chain.oldIndex t)).symm
    _ = _ := by
      rw [o.oldIndex_val r, o.oldIndex_val t, sourceEntry_command]
      apply commandEntry_congr
      · exact (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _).symm
      · exact IntegralMixedFramedHistoryFamilyBits.older_commands_key P D H key i context
      · exact IntegralMixedFramedHistoryFamilyBits.origin_instruction_key P D H key i context

theorem sourceEntry_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedCompanionBits.value P D H q =
      residueBits (sourceEntry P D H (IntegralMixedVirtualTaskBits.saved P q) (get P .row q) (get P .col q) : ZMod (modulus P q)) := rfl
end LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
