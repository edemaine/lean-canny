/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralScaledCharacteristicSpace
public import LeanCanny.Computation.TwoCallController
/-! # Scalar rescaling with two charged current replies

Both the characteristic coefficient and integer-leading residue are children.
The native local postprocessor only performs modular powering and multiplication.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralScaledCharacteristicBits.Charged
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

def post (S : IntegralBerkowitzBlockBits.Source) (exponent : List Bool → ℕ) (z : List Bool) : List Bool :=
  multiplyPost S (pair (pairFst z) (pair (pairFst (pairSnd z))
    (powerPost S exponent (pair (pairFst z) (pairSnd (pairSnd z))))))

theorem post_FP (S : IntegralBerkowitzBlockBits.Source) (a : IntegralBerkowitzBlockBits.Access S)
    (exponent : List Bool → ℕ) (he : BinaryFn exponent) : post S exponent ∈ FP := by
  have HP := mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
    (powerPost_FP S a exponent he)
  exact mem_FP_comp (mem_FP_pair pairFst_mem_FP
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) HP)) (multiplyPost_FP S a)

theorem post_packet (S : IntegralBerkowitzBlockBits.Source) (exponent : List Bool → ℕ)
    (q : List Bool) (x y : ZMod (S.modulus q)) :
    post S exponent (pair q (pair (residueBits x) (residueBits y))) =
      residueBits (x * y ^ (exponent q * S.coefficient q)) := by
  simp only [post, pairFst_pair, pairSnd_pair]
  rw [powerPost_packet, multiplyPost_packet]

def program (S : IntegralBerkowitzBlockBits.Source) (exponent : List Bool → ℕ)
    (coefficientTask leadingTask : List Bool → List Bool) : RecursiveFold.Program :=
  TwoCall.program coefficientTask leadingTask (post S exponent)

theorem certificates (S : IntegralBerkowitzBlockBits.Source) (a : IntegralBerkowitzBlockBits.Access S)
    (exponent : List Bool → ℕ) (he : BinaryFn exponent) (coefficientTask leadingTask : List Bool → List Bool)
    (hc : coefficientTask ∈ FP) (hl : leadingTask ∈ FP) :
    (program S exponent coefficientTask leadingTask).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  TwoCall.certificates coefficientTask leadingTask (post S exponent) hc hl (post_FP S a exponent he)

theorem value_at (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (coefficientTask leadingTask answer : List Bool → List Bool) (q : List Bool)
    (hc : answer (coefficientTask q) = S.value q)
    (hl : answer (leadingTask q) = residueBits (scalar q : ZMod (S.modulus q))) :
    (program S exponent coefficientTask leadingTask).value answer q = IntegralScaledCharacteristicBits.value S scalar exponent q := by
  rw [program, TwoCall.value_eq, hc, hl, IntegralBerkowitzBlockBits.Source.value, post_packet]
  exact (IntegralScaledCharacteristicBits.value_eq S scalar exponent q).symm

theorem requests_iff (S : IntegralBerkowitzBlockBits.Source) (exponent : List Bool → ℕ)
    (coefficientTask leadingTask answer : List Bool → List Bool) (q c : List Bool) :
    (program S exponent coefficientTask leadingTask).controller.Requests answer (fun _ => 2) q c ↔
      c = coefficientTask q ∨ c = leadingTask q :=
  TwoCall.requests_iff coefficientTask leadingTask (post S exponent) answer q c

theorem requests_cases (S : IntegralBerkowitzBlockBits.Source) (exponent : List Bool → ℕ)
    (coefficientTask leadingTask answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hc : (program S exponent coefficientTask leadingTask).controller.Requests answer budget q c) :
    c = coefficientTask q ∨ c = leadingTask q := by
  let P := program S exponent coefficientTask leadingTask
  obtain ⟨t, _, hh, _, he⟩ := hc
  have HI : min t (P.count q) < P.count q := by
    rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at hh
    have H : ¬ P.count q ≤ min t (P.count q) := of_decide_eq_false hh
    omega
  have HR : P.controller.Requests answer P.count q c := by
    apply (P.requests_iff answer q c).mpr
    refine ⟨min t (P.count q), HI, ?_⟩
    rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at he
    exact he
  exact (requests_iff S exponent coefficientTask leadingTask answer q c).mp HR

noncomputable def stateBound (S : IntegralBerkowitzBlockBits.Source) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (encNat 2).length + (S.modulus q).size + 2

theorem stateBound_unary (S : IntegralBerkowitzBlockBits.Source) (a : IntegralBerkowitzBlockBits.Access S) : UnaryFn (stateBound S) := by
  have HM : UnaryFn (fun q => (S.modulus q).size) :=
    (UnaryFn.length a.modulus.bits_mem_FP).of_eq (fun _ => Nat.size_eq_bits_len _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const (2 * (encNat 2).length))).add HM).add (UnaryFn.const 2)

theorem state_length_at (S : IntegralBerkowitzBlockBits.Source) (scalar : List Bool → ℤ)
    (exponent : List Bool → ℕ) (coefficientTask leadingTask answer : List Bool → List Bool) (q : List Bool)
    (hc : answer (coefficientTask q) = S.value q)
    (hl : answer (leadingTask q) = residueBits (scalar q : ZMod (S.modulus q))) (t : ℕ) :
    (RecursiveFold.encState (((program S exponent coefficientTask leadingTask).controller.reference answer)^[t]
      ((program S exponent coefficientTask leadingTask).initial q))).length ≤ stateBound S q := by
  let : NeZero (S.modulus q) := ⟨S.modulus_ne_zero q⟩
  have HC : (S.value q).length ≤ (S.modulus q).size := residueBits_length_le _ _
  have HV : (IntegralScaledCharacteristicBits.value S scalar exponent q).length ≤ (S.modulus q).size := residueBits_length_le _ _
  have H := TwoCall.state_length coefficientTask leadingTask (post S exponent) answer q t
  have HP : post S exponent (pair q (pair (answer (coefficientTask q)) (answer (leadingTask q)))) =
      IntegralScaledCharacteristicBits.value S scalar exponent q :=
    (TwoCall.value_eq coefficientTask leadingTask (post S exponent) answer q).symm.trans
      (value_at S scalar exponent coefficientTask leadingTask answer q hc hl)
  rw [HP, hc] at H
  exact H.trans (by dsimp only [stateBound]; omega)

end LeanCanny.Algebra.IntegralScaledCharacteristicBits.Charged
