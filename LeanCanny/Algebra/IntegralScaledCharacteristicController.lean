/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralScaledCharacteristicSpace
public import LeanCanny.Computation.ControllerRequests

/-! # Resumable scalar rescaling of relative characteristic coefficients

One characteristic-coefficient request is followed by native modular
powering and multiplication. The scalar needs an FP residue reader, not a
bounded integer expansion or an inverse modulo the caller modulus.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralScaledCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] powerPost multiplyPost

noncomputable def finishAt (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (c v : List Bool) : List Bool :=
  multiplyPost S (pair c (pair v
    (powerPost S exponent (pair c (residueBits (scalar c : ZMod (S.modulus c)))))))

noncomputable def finish (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (z : List Bool) : List Bool := finishAt S scalar exponent (pairFst z) (pairSnd z)

theorem finish_FP (S : IntegralBerkowitzBlockBits.Source) (a : IntegralBerkowitzBlockBits.Access S)
    (scalar : List Bool → ℤ) (exponent : List Bool → ℕ) (he : BinaryFn exponent)
    (hc : (fun c => residueBits (scalar c : ZMod (S.modulus c))) ∈ FP) : finish S scalar exponent ∈ FP := by
  have HL : (fun z => residueBits (scalar (pairFst z) : ZMod (S.modulus (pairFst z)))) ∈ FP :=
    mem_FP_comp pairFst_mem_FP hc
  have HP := mem_FP_comp (mem_FP_pair pairFst_mem_FP HL) (powerPost_FP S a exponent he)
  have H := mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_pair pairSnd_mem_FP HP)) (multiplyPost_FP S a)
  exact mem_FP_of_eq H (fun _ => rfl)

noncomputable def program (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (task : List Bool → List Bool) : SingleCall.Program where
  request _ := true
  query := task
  immediate _ := []
  finish := finish S scalar exponent

theorem program_controls (S : IntegralBerkowitzBlockBits.Source) (a : IntegralBerkowitzBlockBits.Access S)
    (scalar : List Bool → ℤ) (exponent : List Bool → ℕ) (he : BinaryFn exponent)
    (hc : (fun c => residueBits (scalar c : ZMod (S.modulus c))) ∈ FP)
    (task : List Bool → List Bool) (ht : task ∈ FP) : (program S scalar exponent task).Controls :=
  ⟨constFn_mem_FP [true], ht, constFn_mem_FP [], finish_FP S a scalar exponent he hc⟩

theorem program_value (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (task answer : List Bool → List Bool)
    (he : ∀ c, answer (task c) = S.value c) (c : List Bool) :
    (program S scalar exponent task).value answer c = value S scalar exponent c := by
  simp only [SingleCall.Program.value, program, ite_true, finish, pairFst_pair, pairSnd_pair, he]
  unfold finishAt
  rw [powerPost_packet, IntegralBerkowitzBlockBits.Source.value, multiplyPost_packet]
  exact (value_eq S scalar exponent c).symm

theorem program_requests_iff (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) :
    (program S scalar exponent task).controller.Requests answer budget c child ↔ child = task c := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, true_and]

end LeanCanny.Algebra.IntegralScaledCharacteristicBits
