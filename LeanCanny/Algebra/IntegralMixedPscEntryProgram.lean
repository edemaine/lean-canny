/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscEntryQueries
/-! # A PSC entry performs one guarded native coordinate-coefficient request -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
attribute [local irreducible] ArithmeticBits.negate BinaryNat.mulMod PrincipalDerivativeEntryRequest.finish
attribute [local irreducible] coefficientValue IntegralMixedVirtualQueryBits.matrixCoefficient
attribute [local irreducible] packet PrincipalDerivativeEntryRequest.multiplier

noncomputable def finish (P : Parameters) (F : Family) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (modulus P (pairFst z)))
    (pair (pairSnd z) (BinaryNatCode.encode
      (PrincipalDerivativeEntryRequest.multiplier (parameters P F) (packet P (pairFst z))))))
theorem finish_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : finish P F ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have HK : BinaryFn (fun z => PrincipalDerivativeEntryRequest.multiplier (parameters P F) (packet P (pairFst z))) :=
    (PrincipalDerivativeEntryRequest.multiplier_binary _ (controls P a F h)).comp
      (mem_FP_comp pairFst_mem_FP (packet_FP P a))
  have H := mem_FP_comp (mem_FP_pair HM.bits_mem_FP (mem_FP_pair pairSnd_mem_FP HK.bits_mem_FP)) BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq H (fun _ => rfl)

theorem finish_integer (P : Parameters) (F : Family) (q : List Bool) (x : ℤ) :
    finish P F (pair q (residueBits (x : ZMod (modulus P q)))) =
      residueBits ((x * (PrincipalDerivativeEntryRequest.multiplier (parameters P F) (packet P q) : ℤ) : ℤ) :
        ZMod (modulus P q)) := by
  simp only [finish, pairFst_pair, pairSnd_pair]
  simpa only [Int.cast_mul, Int.cast_natCast] using ArithmeticBits.mulMod_nat_residueBits
    (modulus P q) (x : ZMod (modulus P q)) (PrincipalDerivativeEntryRequest.multiplier (parameters P F) (packet P q))

noncomputable def program (P : Parameters) (F : Family) : SingleCall.Program where
  request q := decide (Request P F q)
  query := query P F
  immediate _ := []
  finish := finish P F
theorem program_controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : (program P F).Controls :=
  ⟨(request_FP P a F h).flag_mem_FP, query_FP P a F h, constFn_mem_FP [], finish_FP P a F h⟩

noncomputable def selectedInteger (P : Parameters) (F : Family) (q : List Bool) : ℤ :=
  if Request P F q then coefficientValue P F q *
    (PrincipalDerivativeEntryRequest.multiplier (parameters P F) (packet P q) : ℤ) else 0
noncomputable def selectedValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (selectedInteger P F q : ZMod (modulus P q))

attribute [local irreducible] selectedInteger selectedValue

abbrev RepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  Request P F q → answer (query P F q) = (IntegralMixedVirtualTaskBits.source P F).value (query P F q)
theorem value_at (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F answer q) :
    (program P F).value answer q = selectedValue P F q := by
  by_cases hr : Request P F q
  · simp only [SingleCall.Program.value, program, hr, decide_true, ite_true]
    rw [he hr, child_value P F g q hr, finish_integer]
    simp only [selectedValue, selectedInteger, hr, ite_true]
  · simp only [SingleCall.Program.value, program, hr, decide_false, Bool.false_eq_true, ite_false,
      selectedValue, selectedInteger, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

end LeanCanny.Algebra.IntegralMixedPscEntryBits
