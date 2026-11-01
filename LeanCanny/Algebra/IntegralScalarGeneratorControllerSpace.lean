/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralScalarGeneratorController
public import LeanCanny.Algebra.ModularScalarSpace
/-! # Companion controllers with charged leading-scalar postprocessing

The request flag and child writer stay native FP. Computing the integer
leading residue in the local finish may use polynomial space.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarGeneratorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ArithmeticBits.negate

def negatePost (m : List Bool → ℕ) (z : List Bool) : List Bool := ArithmeticBits.negate (pair (BinaryNatCode.encode (m (pairFst z))) (pairSnd z))

theorem negatePost_FP {m : List Bool → ℕ} (hm : BinaryFn m) : negatePost m ∈ FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hm.bits_mem_FP) pairSnd_mem_FP) ArithmeticBits.negate_mem_FP

theorem finish_evaluator (F : Family) (a : Access F) (EL : SpaceFunction a.leading) : SpaceFunction (finish F) := by
  have HM : BinaryFn (fun z => F.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  have HE : BinaryFn (fun z => power F (pairFst z)) :=
    ((a.selectedDegree.sub (BinaryFn.const 1)).sub (a.row.sub (a.scalarDegree.sub a.selectedDegree))).comp pairFst_mem_FP
  have HL : SpaceFunction (fun z => residueBits (F.leading (pairFst z))) :=
    (EL.precompose pairFst pairFst_mem_FP).congr (funext fun z => a.leading_eq (pairFst z))
  have HP := ModularScalarSpace.pow HM (fun z => F.modulus_ne_zero (pairFst z)) _ HE _ HL
  have HR := ModularScalarFP.natCast HM (fun z => Nat.fromBitsLE (pairSnd z)) (BinaryFn.fromBits pairSnd_mem_FP)
  have HX := ModularScalarSpace.mul HM _ _ (SpaceFunction.ofFP _ HR) HP
  have E := HX.withInput.postcompose (negatePost (fun z => F.modulus (pairFst z))) (negatePost_FP HM)
  refine E.congr (funext fun z => ?_)
  simp only [Function.comp_apply, negatePost, pairFst_pair, pairSnd_pair]
  let : NeZero (F.modulus (pairFst z)) := ⟨F.modulus_ne_zero _⟩
  exact ArithmeticBits.negate_residueBits _ _

theorem program_certificates_of_leading_space (F : Family) (a : Access F) (EL : SpaceFunction a.leading)
    (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program F task).controller.Certificates (encQ := encBits) (encS := SingleCall.encState) :=
  (program F task).certificates_of_space (request_FP F a).flag_mem_FP
    (mem_FP_comp (f := coefficientQuery F) (g := task) (coefficientQuery_FP F a) ht) (SpaceFunction.ofFP _ (immediate_FP F a)).computable
    (finish_evaluator F a EL).computable
end LeanCanny.Algebra.IntegralScalarGeneratorBits
