/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralScalarGeneratorView
public import LeanCanny.Computation.NativeTwoCallBranch
/-! # Scalar companion arithmetic with both coefficient and leading replies charged -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarGeneratorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem viewValue_coefficient (F : Family) (q : List Bool) :
    viewValue (F.modulus q) (F.scalarDegree q) (F.selectedDegree q)
      (F.row q).val (F.col q).val (F.oldRow q).val (F.oldCol q).val (F.leading q)
      (residueBits (F.coefficient q (index F q) (F.oldRow q) (F.oldCol q))) = F.toFamily.value q := by
  let answer := fun z => residueBits (F.coefficient (pairFst z) (index F (pairFst z))
    (F.oldRow (pairFst z)) (F.oldCol (pairFst z)))
  have HA (c : List Bool) : answer (id (coefficientQuery F c)) =
      residueBits (F.coefficient c (index F c) (F.oldRow c) (F.oldCol c)) := by
    dsimp only [answer, id_eq]
    rw [show pairFst (coefficientQuery F c) = c from pairFst_pair _ _]
  have HE := program_value F id answer (fun c _ => HA c) q
  rw [program_view, HA q] at HE
  exact HE

noncomputable def chargedPost (F : Family) (z : List Bool) : List Bool :=
  viewValue (F.modulus (pairFst z)) (F.scalarDegree (pairFst z)) (F.selectedDegree (pairFst z))
    (F.row (pairFst z)).val (F.col (pairFst z)).val (F.oldRow (pairFst z)).val (F.oldCol (pairFst z)).val
    (Nat.fromBitsLE (pairSnd (pairSnd z)) : ZMod (F.modulus (pairFst z))) (pairFst (pairSnd z))

attribute [local irreducible] ArithmeticBits.negate

theorem chargedPost_FP (F : Family) (a : Access F) : chargedPost F ∈ FP := by
  have HM : BinaryFn (fun z => F.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  have HE : BinaryFn (fun z => power F (pairFst z)) := ((a.selectedDegree.sub (BinaryFn.const 1)).sub
    (a.row.sub (a.scalarDegree.sub a.selectedDegree))).comp pairFst_mem_FP
  have HL : (fun z => residueBits (Nat.fromBitsLE (pairSnd (pairSnd z)) : ZMod (F.modulus (pairFst z)))) ∈ FP :=
    ModularScalarFP.natCast HM _ (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
  have HP := ModularScalarFP.pow HM (fun z => F.modulus_ne_zero (pairFst z)) _ HE _ HL
  have HC : (fun z => residueBits (Nat.fromBitsLE (pairFst (pairSnd z)) : ZMod (F.modulus (pairFst z)))) ∈ FP :=
    ModularScalarFP.natCast HM _ (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
  have HX := ModularScalarFP.mul HM _ _ HC HP
  have HN := mem_FP_comp (mem_FP_pair HM.bits_mem_FP HX) ArithmeticBits.negate_mem_FP
  have HN' : (fun z => residueBits (-((Nat.fromBitsLE (pairFst (pairSnd z)) : ZMod (F.modulus (pairFst z))) *
      (Nat.fromBitsLE (pairSnd (pairSnd z)) : ZMod (F.modulus (pairFst z))) ^ power F (pairFst z)))) ∈ FP :=
    mem_FP_of_eq HN (fun z => by
      let : NeZero (F.modulus (pairFst z)) := ⟨F.modulus_ne_zero _⟩
      exact ArithmeticBits.negate_residueBits _ _)
  have HI := mem_FP_comp pairFst_mem_FP (immediate_FP F a)
  exact mem_FP_of_eq (((request_FP F a).comp pairFst_mem_FP).ite_mem_FP HN' HI) (fun z => by
    simp only [chargedPost, viewValue, request, immediate, power, index, Function.comp_apply])

theorem chargedPost_residue (F : Family) (q : List Bool) (c l : ZMod (F.modulus q)) :
    chargedPost F (pair q (pair (residueBits c) (residueBits l))) =
      viewValue (F.modulus q) (F.scalarDegree q) (F.selectedDegree q)
        (F.row q).val (F.col q).val (F.oldRow q).val (F.oldCol q).val l (residueBits c) := by
  let : NeZero (F.modulus q) := ⟨F.modulus_ne_zero q⟩
  unfold chargedPost
  rw [pairFst_pair, pairSnd_pair, pairFst_pair, pairSnd_pair]
  simp only [residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.natCast_zmod_val]

theorem chargedPost_value (F : Family) (q : List Bool) :
    chargedPost F (pair q (pair
      (residueBits (F.coefficient q (index F q) (F.oldRow q) (F.oldCol q)))
      (residueBits (F.leading q)))) = F.toFamily.value q :=
  (chargedPost_residue F q _ _).trans (viewValue_coefficient F q)

end LeanCanny.Algebra.IntegralScalarGeneratorBits
