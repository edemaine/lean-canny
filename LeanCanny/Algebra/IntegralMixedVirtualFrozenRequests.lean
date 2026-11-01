/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeAccess
public import LeanCanny.Algebra.IntegralFrozenPowerConstantSpace
public import LeanCanny.Computation.TwoCallController
/-! # Guarded frozen constants with an explicit original-leading child

Only a zero target requests the original leading and frozen-power sum.
The native modular multiplication uses their two replies. No leading
coefficient evaluator is embedded in the local postprocessor.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualFrozenRequestBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralFrozenPowerBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def program (S : Source) (originalLeading frozenSum : List Bool → List Bool) : RecursiveFold.Program :=
  { TwoCall.program originalLeading frozenSum (multiplyPost S) with
    count q := if zeroTarget S q then 2 else 0 }

theorem certificates (S : Source) (a : Access S) (originalLeading frozenSum : List Bool → List Bool)
    (hl : originalLeading ∈ FP) (hs : frozenSum ∈ FP) :
    (program S originalLeading frozenSum).controller.Certificates
      (encQ := encBits) (encS := RecursiveFold.encState) :=
  RecursiveFold.Program.certificates _
    (BinaryFn.ite (zeroTarget_fppred S a) (BinaryFn.const 2) (BinaryFn.const 0))
    (constFn_mem_FP []) (TwoCall.entryTask_FP originalLeading frozenSum hl hs)
    (TwoCall.finish_FP (multiplyPost S) (multiplyPost_FP S a))

theorem value_at (S : Source) (a : Access S) (originalLeading frozenSum reply : List Bool → List Bool)
    (q : List Bool) (hl : zeroTarget S q → reply (originalLeading q) = a.leading q)
    (hs : zeroTarget S q → reply (frozenSum q) = S.sumValue q) :
    (program S originalLeading frozenSum).value reply q = S.constantValue q := by
  have HC : (program S originalLeading frozenSum).value reply q =
      if zeroTarget S q then (TwoCall.program originalLeading frozenSum (multiplyPost S)).value reply q else [] := by
    unfold RecursiveFold.Program.value
    by_cases hz : zeroTarget S q
    · simp only [program, hz, ite_true]
      rfl
    · simp only [program, hz, ite_false]
      rfl
  rw [HC]
  by_cases hz : zeroTarget S q
  · rw [ite_eq_left hz, TwoCall.value_eq, hl hz, hs hz, a.leading_eq,
      Source.sumValue, multiplyPost_packet, leading_value]
    simpa only [hz, ite_true] using constant_value S q
  · rw [ite_eq_right hz]
    simpa only [hz, ite_false] using constant_value S q

theorem requests_iff (S : Source) (originalLeading frozenSum reply : List Bool → List Bool)
    (q c : List Bool) :
    (program S originalLeading frozenSum).controller.Requests reply (program S originalLeading frozenSum).count q c ↔
      zeroTarget S q ∧ (c = originalLeading q ∨ c = frozenSum q) := by
  rw [RecursiveFold.Program.requests_iff]
  constructor
  · rintro ⟨i, hi, he⟩
    have hz : zeroTarget S q := by
      by_contra hn
      simp only [program, hn, ite_false] at hi
      omega
    refine ⟨hz, ?_⟩
    have hi2 : i < 2 := by simpa only [program, hz, ite_true] using hi
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · left
      simpa only [program, RecursiveFold.Program.child, TwoCall.program, TwoCall.entryTask, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true] using he
    · right
      simpa only [program, RecursiveFold.Program.child, TwoCall.program, TwoCall.entryTask, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.one_ne_zero, ite_false] using he
  · rintro ⟨hz, he | he⟩
    · refine ⟨0, ?_, ?_⟩
      · simp only [program, hz, ite_true]; decide
      · simpa only [program, RecursiveFold.Program.child, TwoCall.program, TwoCall.entryTask, pairFst_pair, pairSnd_pair,
          BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true] using he
    · refine ⟨1, ?_, ?_⟩
      · simp only [program, hz, ite_true]; decide
      · simpa only [program, RecursiveFold.Program.child, TwoCall.program, TwoCall.entryTask, pairFst_pair, pairSnd_pair,
          BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.one_ne_zero, ite_false] using he

theorem halted_after (S : Source) (originalLeading frozenSum reply : List Bool → List Bool) (q : List Bool) :
    (program S originalLeading frozenSum).controller.halted
      (((program S originalLeading frozenSum).controller.reference reply)^[(program S originalLeading frozenSum).count q] ((program S originalLeading frozenSum).initial q)) = true :=
  (program S originalLeading frozenSum).halted_after reply q

noncomputable def stateBound (S : Source) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (encNat 2).length + (S.modulus q).size + 2

theorem stateBound_unary (S : Source) (a : Access S) : UnaryFn (stateBound S) := by
  have HM : UnaryFn (fun q => (S.modulus q).size) :=
    (UnaryFn.length a.modulus.bits_mem_FP).of_eq (fun _ => Nat.size_eq_bits_len _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const (2 * (encNat 2).length))).add HM).add (UnaryFn.const 2)

theorem state_length_at (S : Source) (a : Access S) (originalLeading frozenSum reply : List Bool → List Bool)
    (q : List Bool) (hl : zeroTarget S q → reply (originalLeading q) = a.leading q)
    (hs : zeroTarget S q → reply (frozenSum q) = S.sumValue q) (t : ℕ) :
    (RecursiveFold.encState (((program S originalLeading frozenSum).controller.reference reply)^[t]
      ((program S originalLeading frozenSum).initial q))).length ≤ stateBound S q := by
  let : NeZero (S.modulus q) := ⟨S.modulus_ne_zero q⟩
  have H := (program S originalLeading frozenSum).orbit_length reply q t (S.modulus q).size
  have HB : ∀ i ≤ (program S originalLeading frozenSum).count q,
      ((program S originalLeading frozenSum).partialValue reply q i).length ≤ (S.modulus q).size := by
    intro i hi
    by_cases hz : zeroTarget S q
    · have hi2 : i ≤ 2 := by simpa only [program, hz, ite_true] using hi
      have HI : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases HI with rfl | rfl | rfl
      · change 0 ≤ _
        exact Nat.zero_le _
      · change ((TwoCall.program originalLeading frozenSum (multiplyPost S)).partialValue reply q 1).length ≤ _
        rw [TwoCall.partial_one, hl hz, a.leading_eq]
        exact residueBits_length_le _ _
      · have HE : (program S originalLeading frozenSum).count q = 2 := by simp only [program, hz, ite_true]
        rw [← HE]
        change ((program S originalLeading frozenSum).value reply q).length ≤ _
        rw [value_at S a originalLeading frozenSum reply q hl hs]
        exact residueBits_length_le _ _
    · have HI : i = 0 := by simp only [program, hz, ite_false] at hi; omega
      subst i
      change 0 ≤ _
      exact Nat.zero_le _
  have HC : (encNat ((program S originalLeading frozenSum).count q)).length ≤ (encNat 2).length := by
    apply ComputableTidilyInO.length_encNat_mono
    by_cases hz : zeroTarget S q <;> simp only [program, hz, ite_true, ite_false] <;> omega
  exact (H HB).trans (by dsimp only [stateBound]; omega)

noncomputable abbrev virtualProgram (F : IntegralMixedCutSource.Family)
    (I : IntegralMixedVirtualSweepSource.Indices F) (originalLeading frozenSum : List Bool → List Bool) :=
  program (IntegralMixedVirtualNativeBits.arithmetic F I).toGradient.toFrozen originalLeading frozenSum
end LeanCanny.Algebra.IntegralMixedVirtualFrozenRequestBits
